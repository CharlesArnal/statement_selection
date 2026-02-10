Lemma 1.1:
non-included
Searched in Mathlib/Analysis/InnerProductSpace/, Mathlib/Geometry/Euclidean/, and Mathlib/Analysis/Calculus/. This result about the derivative of a unit-length smooth map f: I -> R^2 expressed via the determinant and the rotation matrix J is specific to the differential geometry of plane curves and is not present in mathlib. Mathlib has no formalization of plane curve theory.

Proposition 1.3 (Frenet equation of motion):
non-included
Searched for "Frenet" across all of mathlib with no results. The Frenet equation of motion for plane curves, expressing the derivative of the unit tangent vector in terms of curvature, is not formalized in mathlib. Mathlib has no plane curve curvature theory.

Corollary 1.4:
non-included
This result (zero curvature implies the curve is part of a straight line) is a corollary of the Frenet equations. Searched Mathlib/Geometry/Euclidean/ and Mathlib/Analysis/Calculus/. No formalization of plane curve curvature exists in mathlib, so this corollary is not present.

Corollary 1.5:
non-included
This result (constant nonzero curvature implies the curve is part of a circle) depends on the Frenet framework for plane curves. Searched Mathlib/Geometry/Euclidean/ and Mathlib/Analysis/Calculus/. Not present in mathlib.

Lemma 2.1:
non-included
The curvature formula for a graph c(t) = (t, f(t)) is a specific computation in plane curve theory. Searched Mathlib/Geometry/ and Mathlib/Analysis/. No formalization of curvature of graphs exists in mathlib.

Lemma 2.2:
non-included
The curvature formula for unit speed plane curves as det(c', c'') is not formalized in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/InnerProductSpace/. No plane curve curvature theory exists in mathlib.

Proposition 2.3:
non-included
The existence and uniqueness (up to rigid motions) of a unit speed curve with prescribed curvature is a fundamental theorem in plane curve theory. Searched Mathlib/Geometry/ and Mathlib/Analysis/Calculus/. Not present in mathlib.

Proposition 2.4:
non-included
The reparametrization invariance of curvature is a basic property in differential geometry of curves. Searched Mathlib/Geometry/ and Mathlib/Analysis/. Not present in mathlib, as there is no formalization of curve curvature.

Lemma 2.5 (from calculus):
non-included
This lemma states that a smooth function with everywhere positive derivative on an interval is a diffeomorphism onto its image, with smooth inverse given by the inverse function theorem for one variable. Searched Mathlib/Analysis/Calculus/InverseFunctionTheorem/ and Mathlib/Analysis/Calculus/Deriv/. While mathlib has the inverse function theorem in the general Banach space setting, this specific one-dimensional result about smooth monotone functions on intervals with explicit inverse derivative formula is not stated in this form. The general inverse function theorem is local, whereas this statement is global on an interval.

Lemma 2.6:
non-included
The statement that a curve with d_1'(t) > 0 can be reparametrized to a graph is a simple consequence of the inverse function theorem for one variable. Not stated in mathlib. Searched Mathlib/Analysis/Calculus/ and Mathlib/Geometry/.

Lemma 2.7:
non-included
The existence of a unit speed reparametrization for any regular curve is a standard result in differential geometry. Searched Mathlib/Geometry/ and Mathlib/Analysis/. Not formalized in mathlib.

Proposition 3.1:
non-included
The existence and uniqueness of the osculating circle for a unit speed curve at a point of nonzero curvature is not formalized in mathlib. Searched Mathlib/Geometry/Euclidean/ for circle-related results and Mathlib/Analysis/. No osculating circle theory exists in mathlib.

Proposition 3.2:
non-included
The curvature formula for curves on level sets of smooth functions is a specific computation in plane curve theory. Searched Mathlib/Geometry/ and Mathlib/Analysis/. Not present in mathlib.

Lemma 5.1 (Gram-Schmidt orthogonalization):
included
Mathlib has a full formalization of the Gram-Schmidt process in Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean. The file provides gramSchmidt (orthogonalization), gramSchmidtNormed (orthonormalization), proofs of orthogonality (gramSchmidt_orthogonal), span preservation (span_gramSchmidt), linear independence preservation (gramSchmidt_linearIndependent), and the orthonormal basis construction (gramSchmidtOrthonormalBasis).

Lemma 5.2:
non-included
The statement that if E(t) is a differentiable family of orthogonal matrices and E'(t) = E(t)A(t), then A(t) is skew-symmetric, is a result about the Lie algebra of the orthogonal group. Searched Mathlib/LinearAlgebra/UnitaryGroup.lean and Mathlib/Algebra/Lie/SkewAdjoint.lean. While mathlib has the notion of skew-adjoint operators and the Lie algebra of the orthogonal group, this specific dynamic/ODE characterization is not formalized.

Lemma 5.4:
non-included
The reparametrization invariance of Frenet frames is part of Frenet curve theory. Searched for "Frenet" across mathlib with no results. Not present in mathlib.

Theorem 6.1:
non-included
The Frenet-Serret formulas for curves in R^n, expressing the derivative of the Frenet frame as a tridiagonal skew-symmetric matrix times the frame, are not formalized in mathlib. Searched for "Frenet" across all of mathlib with no results.

Proposition 6.2:
non-included
The formula expressing the determinant det(c', c'', ..., c^(n))/||c'||^{n(n+1)/2} as a product of Frenet curvatures is not in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/. No Frenet theory in mathlib.

Lemma 7.1:
non-included
The lifting lemma for unit-length periodic functions on R to R^2 (writing f(t) = (cos theta(t), sin theta(t))) is not formalized in mathlib. Searched Mathlib/Topology/Covering/ and Mathlib/Analysis/SpecialFunctions/. While mathlib has covering space theory, this specific lifting result for circle-valued maps is not present in this form.

Lemma 7.3:
non-included
The statement that a periodic map to the circle with nonzero degree is surjective. Searched for "winding number" and "degree" related to circle maps in mathlib. No formalization of degree theory for circle maps exists in mathlib.

Proposition 7.4:
non-included
The computation of the degree of a circle map via signed counting of preimages of a regular value. Searched mathlib for "brouwerDegree" and "winding number" with no relevant results. Not present in mathlib.

Theorem 8.2 (Jordan curve theorem):
non-included
Searched for "Jordan" and "curve" across all of mathlib. The Jordan curve theorem is not formalized in mathlib.

Lemma 8.4:
non-included
The preservation of total curvature under unit speed reparametrization of closed curves is part of plane curve theory not formalized in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/.

Proposition 8.5:
non-included
The identification of total curvature divided by 2pi with the degree of the unit tangent map (rotation number) is not in mathlib. Searched for degree theory and curvature across mathlib. Not present.

Corollary 8.6:
non-included
The formula for the rotation number via signed counting of horizontal tangencies is part of plane curve theory not formalized in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/.

Theorem 9.1 (Hopf Umlaufsatz):
non-included
The theorem that the total curvature of a simple closed curve is +/- 2pi is not formalized in mathlib. Searched for "Hopf" and "Umlaufsatz" across mathlib with no results. No turning number theory exists in mathlib.

Proposition 9.3:
non-included
The characterization of convex simple closed curves by non-changing sign of curvature is not in mathlib. Searched Mathlib/Geometry/Convex/ and Mathlib/Analysis/. Mathlib's convexity theory does not include differential-geometric characterizations.

Corollary 9.4:
non-included
The inequality that the total absolute curvature of a closed curve is at least 2pi (Fenchel's theorem for plane curves) is not in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/. Not present.

Theorem 9.5 (Whitney):
non-included
Whitney's formula for the rotation number of a closed curve with normal self-intersections is not formalized in mathlib. Searched for "Whitney" across mathlib with no relevant results.

Lemma 10.1 (Sturm-Hurwitz):
non-included
The Sturm-Hurwitz lemma about zeros of periodic functions with vanishing first three Fourier coefficients is not in mathlib. Searched for "Sturm" and "Hurwitz" across mathlib; Hurwitz results found are about zeta functions, not about zeros of periodic functions.

Lemma 10.2:
non-included
The result that h(t) + h''(t) has at least four critical points for smooth 2pi-periodic h is related to the Sturm-Hurwitz theory. Not present in mathlib. Searched Mathlib/Analysis/ and Mathlib/Topology/.

Lemma 10.3:
non-included
The reparametrization result for strictly convex closed curves achieving a specific unit tangent form is part of plane curve theory not formalized in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/.

Theorem 10.4 (Four Vertex theorem, strictly convex version):
non-included
The Four Vertex Theorem (a strictly convex closed curve has at least four vertices) is a classical result not formalized in mathlib. Searched for "four vertex" and "FourVertex" across mathlib with no results.

Lemma 12.6:
non-included
The formula D(nu) = -Df * L relating the derivative of the Gauss normal to the shape operator of a hypersurface patch is part of the theory of hypersurface geometry not formalized in mathlib. Searched for "hypersurface", "fundamental_form", "shape operator" in mathlib. Not present.

Proposition 13.1:
non-included
The coordinate change formulas for the Gauss normal, first and second fundamental forms, and shape operator under reparametrization are part of hypersurface geometry not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/. Mathlib's manifold library does not include these differential-geometric computations.

Proposition 13.3:
non-included
The rigidity theorem stating that two hypersurface patches with the same first and second fundamental forms differ by a rigid motion (Bonnet's theorem) is not in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/. Not present.

Lemma 14.5:
non-included
The formula for the Gauss curvature in terms of the determinant involving partial derivatives of the Gauss normal is part of hypersurface theory not formalized in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/.

Theorem 16.2:
non-included
The explicit formula for Christoffel symbols in terms of the first fundamental form (metric tensor) is not formalized in mathlib. Searched for "Christoffel" across mathlib with no results. Mathlib's Riemannian geometry (Mathlib/Geometry/Manifold/Riemannian/) does not include Christoffel symbol computations.

Theorem 16.3 (Gauss equation):
non-included
The Gauss equation relating the second fundamental form, shape operator, and Christoffel symbols is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/. Not present.

Corollary 17.1 (Theorema egregium for surfaces):
non-included
Gauss's Theorema Egregium (the Gauss curvature depends only on the first fundamental form) is not formalized in mathlib. Searched for "theorema egregium" and "TheoremaEgregium" across mathlib with no results.

Lemma 18.2:
non-included
The relation F_{kj} = X^{-1} R_{kj} X for moving bases on surfaces is part of connection theory not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/. Not present.

Lemma 18.3:
non-included
The skew-symmetry of connection matrices and curvature matrices for moving frames is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Algebra/Lie/SkewAdjoint.lean. Not present in this differential-geometric context.

Proposition 18.4:
non-included
The curl form expression for Gauss curvature in terms of connection 1-forms is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/. Not present.

Corollary 18.5 (Gauss-Bonnet for tori):
non-included
The vanishing of total Gauss curvature for doubly-periodic surface patches is not formalized in mathlib. Searched for "Gauss Bonnet" and "GaussBonnet" across mathlib with no results. No Gauss-Bonnet theory exists in mathlib.

Corollary 18.6:
non-included
The consequence that a doubly-periodic surface patch must have both positive and negative Gauss curvature is not in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/. Not present.

Lemma 19.1:
non-included
The statement that wedge products of basis vectors form a basis of the space of antisymmetric matrices (second exterior power) is related to exterior algebra theory. Searched Mathlib/LinearAlgebra/ExteriorPower/ and Mathlib/LinearAlgebra/ExteriorAlgebra/. While mathlib has exterior powers, this specific basis result for the space of skew-symmetric matrices is not stated in this matrix-theoretic form.

Lemma 19.3:
non-included
The trace and determinant formulas for the second exterior power of a linear map are not in this form in mathlib. Searched Mathlib/LinearAlgebra/ExteriorPower/ and Mathlib/LinearAlgebra/Trace.lean. The exterior power constructions in mathlib are algebraic and do not include these specific trace/determinant identities.

Lemma 19.4:
non-included
The injectivity result for the second exterior power map (Lambda^2 L = Lambda^2 L_tilde implies L = +/- L_tilde when rank >= 3) is not in mathlib. Searched Mathlib/LinearAlgebra/ExteriorPower/. Not present.

Theorem 20.1 (Generalized theorema egregium):
non-included
The generalized Theorema Egregium (the Riemann curvature operator is intrinsic) for hypersurfaces of arbitrary dimension is not formalized in mathlib. Searched for "theorema egregium" and "Riemann curvature" across mathlib with no results.

Corollary 20.2:
non-included
The intrinsicality of the unordered collection of products lambda_i * lambda_j of principal curvatures follows from the generalized Theorema Egregium. Not in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/.

Corollary 20.3:
non-included
The intrinsicality of scalar curvature and kappa_gauss^{n-1} is a consequence of the generalized Theorema Egregium. Not in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/.

Corollary 20.4:
non-included
The determination of extrinsic geometry by intrinsic geometry when the second fundamental form has rank >= 3 is not in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/. Not present.

Lemma 21.1:
non-included
The existence of local coordinates making the first fundamental form equal to the identity at a given point (normal coordinates at zeroth order) is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/. Not present.

Lemma 21.2:
non-included
This algebraic lemma about decomposing symmetric arrays S_{ijk} = T_{ijk} + T_{jik} is a linear algebra result not in mathlib. Searched Mathlib/LinearAlgebra/ for symmetric tensor decompositions. Not present.

Corollary 21.3:
non-included
The existence of normal coordinates (G = identity and dG = 0 at a point) is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/. Not present.

Lemma 22.3:
non-included
The result that the Minkowski orthogonal complement of a timelike vector is positive definite is a basic fact about Lorentzian geometry. Searched Mathlib/Geometry/ and Mathlib/Analysis/InnerProductSpace/. Mathlib does not have Minkowski/Lorentzian inner product space theory.

Corollary 23.3:
non-included
The vanishing of total Gauss curvature for doubly-periodic Riemannian metrics on R^2 is an intrinsic version of Corollary 18.5. Not formalized in mathlib. Searched Mathlib/Geometry/Manifold/Riemannian/ -- the Riemannian directory contains basic definitions and path energy/length but no curvature theory.

Proposition 24.3 (L'Hopital's rule):
non-included
This version of L'Hopital's rule (if psi is a local defining function for a hypersurface M and phi vanishes on M, then phi = q*psi for smooth q) is a smooth division lemma. Searched Mathlib/Analysis/Calculus/ and Mathlib/Topology/. While mathlib has various smooth function results, this specific division property for defining functions of submanifolds is not present.

Corollary 24.4:
non-included
The corollary that two local defining functions differ by a smooth nowhere-vanishing factor follows from the division lemma above. Not in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/.

Lemma 25.2:
non-included
The formula relating the shape operator to the Hessian of the defining function on a hypersurface is not in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/. Not present.

Proposition 25.4:
non-included
The formulas for mean and Gauss curvature of a hypersurface in terms of a defining function are not formalized in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/. No hypersurface curvature theory exists in mathlib.

Theorem 27.2 (Inverse function theorem):
included
The inverse function theorem is formalized in mathlib in Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean. The theorem HasStrictFDerivAt.toOpenPartialHomeomorph provides the local diffeomorphism, and HasStrictFDerivAt.to_localInverse gives the derivative of the inverse. This covers the statement that a smooth map with invertible derivative at a point is a local diffeomorphism.

Corollary 27.3 (Implicit function theorem, special case):
included
The implicit function theorem is formalized in mathlib in Mathlib/Analysis/Calculus/Implicit.lean. The file provides ImplicitFunctionData.implicitFunction and HasStrictFDerivAt.implicitFunctionDataOfComplemented, which give the implicit function theorem in a general Banach space setting that subsumes this finite-dimensional special case.

Theorem 28.2 (Inverse function theorem):
included
This is the same statement as Theorem 27.2, restated in Chapter 3 for convenience. It is covered by the same mathlib formalization in Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean.

Corollary 29.1 (Implicit function theorem, special case):
included
Same as Corollary 27.3, restated. Covered by Mathlib/Analysis/Calculus/Implicit.lean.

Lemma 29.2:
non-included
The smooth division lemma (a smooth function vanishing on {x_{n+1} = 0} can be written as q * x_{n+1}) is a Hadamard-type lemma. Searched Mathlib/Analysis/Calculus/ and Mathlib/Topology/. Not present in this specific form in mathlib, though Taylor's theorem with remainder provides related results.

Corollary 29.4:
non-included
The existence of partial parametrizations near every point of a hypersurface follows from the implicit function theorem. While mathlib has the implicit function theorem, this specific consequence for hypersurfaces (as zero sets) is not stated. Searched Mathlib/Geometry/Manifold/ -- the charted space formalism is more general and abstract. The specific result about hypersurfaces in R^{n+1} is not formalized.

Proposition 29.5:
non-included
The identification of the first fundamental form and shape operator of a partial parametrization with the intrinsic metric and shape operator of the hypersurface is part of hypersurface theory not in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/.

Proposition 30.1:
non-included
This is a restatement of Proposition 25.4 with additional sign information from the orientation. The formulas for mean and Gauss curvature of a hypersurface in terms of a defining function are not in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/.

Theorem 30.4 (from topology):
non-included
The orientability of connected compact hypersurfaces in R^{n+1} is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ChartedSpace.lean for "orientable" -- the file mentions orientability concepts but does not prove this specific theorem about hypersurfaces. Searched Mathlib/Topology/ as well. Not present.

Theorem 30.5 (from topology):
non-included
The result that a smooth map from a compact connected hypersurface (n >= 2) to S^n with everywhere invertible derivative is bijective is not in mathlib. Searched Mathlib/Topology/ and Mathlib/Geometry/. This is a topological degree theory result not formalized in mathlib.

Theorem 30.7 (Hadamard):
non-included
Hadamard's theorem on convexity of compact connected hypersurfaces with nonvanishing Gauss curvature is not in mathlib. Searched for "Hadamard" in mathlib -- found Mathlib/Analysis/Complex/Hadamard.lean, which is about the Hadamard three-lines theorem in complex analysis, not this differential-geometric result. The Geometry/Convex/ directory deals with convexity in linear algebra, not differential-geometric convexity of hypersurfaces.

Lemma 31.1:
non-included
The formula det(G^f) = det(partial_{x_1} f, ..., partial_{x_n} f, nu^f)^2 and its surface specialization are computations in hypersurface geometry not formalized in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/.

Lemma 32.1:
non-included
The formula expressing det(D(phi)) in terms of a local parametrization, the Gauss normal, and the first fundamental form is part of the theory of smooth maps between oriented hypersurfaces. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/. No such formalization exists in mathlib.

Proposition 32.3:
non-included
The integral formula for the degree of a map between compact hypersurfaces is not in mathlib. Searched for degree theory in mathlib. No Brouwer degree or smooth degree theory for manifolds exists in mathlib.

Lemma 32.4:
non-included
The result that a bijective smooth map with everywhere positive (or negative) Jacobian determinant has degree +1 (or -1) is not in mathlib. No smooth mapping degree theory in mathlib.

Theorem 32.5:
non-included
The integrality of the degree of a smooth map between compact hypersurfaces is not in mathlib. No smooth mapping degree theory exists in mathlib. Searched Mathlib/Topology/ and Mathlib/Geometry/.

Lemma 33.2:
non-included
The surjectivity of a smooth map from a compact hypersurface to S^n with nonzero degree is not in mathlib. No mapping degree theory for manifolds in mathlib.

Theorem 33.3:
non-included
The formula for the degree as a sum of signs of determinants at preimages of a regular value is not in mathlib. Searched Mathlib/Topology/ and Mathlib/Geometry/. No smooth degree theory in mathlib.

Corollary 33.5:
non-included
The formula kappa_{gauss}^{tot} = (-1)^n vol(S^n) deg(nu) relating total Gauss curvature to the degree of the Gauss map is not in mathlib. No Gauss map degree theory in mathlib.

Lemma 34.2:
non-included
The computation of the limit of the line integral of the connection form around a singularity of a moving frame is part of the Gauss-Bonnet theory not formalized in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/.

Theorem 34.4:
non-included
The existence of moving frames with singularities and the identification of the sum of singularity indices with the Euler characteristic is not in mathlib. Searched for "Euler characteristic" in mathlib -- found only combinatorial/algebraic results in incidence algebra, not topological Euler characteristic.

Corollary 34.5 (Gauss-Bonnet theorem):
non-included
The Gauss-Bonnet theorem (kappa_{gauss}^{tot} = 2pi chi(M) for compact surfaces) is not formalized in mathlib. Searched for "GaussBonnet" and "Gauss Bonnet" across all of mathlib with no results.

Corollary 34.6:
non-included
The relation chi(M) = 2 deg(nu) for compact surfaces in R^3 is not in mathlib. No Gauss map degree theory in mathlib.

Corollary 34.7:
non-included
The inequality integral_M ||kappa|| dvol >= 4pi for compact surfaces is not in mathlib. No surface curvature theory in mathlib.

Theorem 35.1 (Hopf):
non-included
Hopf's theorem relating the degree of the Gauss map to the Euler characteristic for even-dimensional closed hypersurfaces is not in mathlib. Searched for "Hopf" and degree theory across mathlib. Not present.

Corollary 35.2 (Generalized Gauss-Bonnet):
non-included
The generalized Gauss-Bonnet theorem for even-dimensional compact hypersurfaces is not in mathlib. No Gauss-Bonnet theory of any kind exists in mathlib.

Theorem 35.4 (combinatorial Gauss-Bonnet):
non-included
The combinatorial Gauss-Bonnet theorem for polyhedral surfaces (sum of combinatorial Gauss curvatures = 2pi chi(M)) is not in mathlib. Searched Mathlib/Combinatorics/ and Mathlib/Geometry/. Not present.

Lemma 36.1:
non-included
The inequality L(gamma) >= ||q - p|| for paths in R^n with characterization of equality (straight line segments) is a basic result. Searched Mathlib/Analysis/Calculus/ and Mathlib/Topology/MetricSpace/. While mathlib has the triangle inequality for metrics and norms, this specific integral form for path lengths with the equality characterization is not stated. Mathlib's Riemannian geometry directory (Mathlib/Geometry/Manifold/Riemannian/PathELength.lean) has path energy/length concepts but not this basic Euclidean result.

Lemma 36.3:
non-included
The constancy of speed for geodesics on hypersurfaces is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ for geodesic-related results. Mathlib does not have geodesic theory for Riemannian manifolds or hypersurfaces.

Proposition 36.4:
non-included
The geodesic equation in local coordinates involving Christoffel symbols is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/Riemannian/ -- the directory has basic metric and path energy definitions but no geodesic equation.

Corollary 36.5:
non-included
The uniqueness of geodesics with given initial conditions is not in mathlib's geometry libraries. While mathlib has ODE uniqueness results (Picard-Lindelof), the specific application to geodesics on hypersurfaces is not formalized.

Corollary 36.6:
non-included
The existence of geodesics with given initial conditions (and global existence for closed hypersurfaces) is not in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/ODE/. Not present as a geometric statement.

Theorem 38.1:
non-included
The variational characterization of geodesics (critical points of the energy functional) is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/Riemannian/ and Mathlib/Analysis/Calculus/. No calculus of variations for geodesics in mathlib.

Corollary 38.2:
non-included
The result that absolute energy minimizers are geodesics is not in mathlib. No variational characterization of geodesics in mathlib.

Theorem 38.3:
non-included
The existence of energy-minimizing geodesics on closed connected hypersurfaces is not in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Topology/. Not present.

Proposition 38.4:
non-included
The Hamiltonian formulation of the geodesic equations is not in mathlib. Searched Mathlib/Geometry/Manifold/Riemannian/ and Mathlib/Analysis/. No Hamiltonian mechanics or symplectic geometry formalized in mathlib for this purpose.

Lemma 39.1:
non-included
While mathlib has extensive metric space theory (Mathlib/Topology/MetricSpace/), the specific result that the intrinsic distance on a connected hypersurface forms a metric space is not formalized. Mathlib does not construct the induced metric on submanifolds of Euclidean space.

Proposition 39.2 (part of the Cauchy-Schwarz inequality):
included
This is the integral Cauchy-Schwarz inequality: integral f <= sqrt(b-a) * sqrt(integral f^2). Mathlib has Holder's inequality for Lebesgue integrals in Mathlib/MeasureTheory/Integral/MeanInequalities.lean (ENNReal.lintegral_mul_le_Lp_mul_Lq), which when specialized to p = q = 2 with one function being the constant 1 gives exactly this result. The inner product space Cauchy-Schwarz is also in Mathlib/Analysis/InnerProductSpace/Basic.lean as norm_inner_le_norm.

Corollary 39.3:
non-included
The inequality L(gamma) <= sqrt(2(b-a)E(gamma)) relating path length and energy is a consequence of Cauchy-Schwarz applied to curve theory. While the underlying Cauchy-Schwarz is in mathlib, this specific geometric corollary about path length vs. energy is not stated. Searched Mathlib/Geometry/Manifold/Riemannian/PathELength.lean -- it defines path energy and length but may not have this specific inequality.

Corollary 39.4:
non-included
The characterization of absolute energy minimizers as constant-speed absolute length minimizers is not formalized in mathlib. Searched Mathlib/Geometry/Manifold/Riemannian/ and Mathlib/Analysis/.

Corollary 39.5:
non-included
The existence of distance-realizing paths on closed connected hypersurfaces (Hopf-Rinow type result) is not in mathlib. Searched Mathlib/Topology/MetricSpace/ and Mathlib/Geometry/Manifold/. Not present.

Lemma 39.6:
non-included
The explicit distance formula in the Poincare disc model of hyperbolic space using arctanh is not in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/SpecialFunctions/. Mathlib does not have hyperbolic geometry distance formulas.

Theorem 39.7 (Schwarz-Pick):
non-included
The Schwarz-Pick theorem (|h'(z)| <= (1 - |h(z)|^2)/(1 - |z|^2) for holomorphic self-maps of the unit disc) is not in mathlib in this specific form. Mathlib's Schwarz lemma (Mathlib/Analysis/Complex/Schwarz.lean) provides norm_deriv_le_div_of_mapsTo_ball and dist_le_div_mul_dist_of_mapsTo_ball for maps sending a ball to a ball, but the specific Schwarz-Pick form at an arbitrary point (not just the center) involving the Poincare metric factors (1 - |z|^2) is not stated.

Corollary 39.8:
non-included
The distance-nonincreasing property of holomorphic self-maps of the unit disc for the Poincare metric (at the infinitesimal level) is not in mathlib. Related to Schwarz-Pick but the hyperbolic metric formulation is not present. Searched Mathlib/Analysis/Complex/Schwarz.lean.

Corollary 39.9:
non-included
The global distance-nonincreasing property of holomorphic self-maps for the hyperbolic metric is not in mathlib. The Schwarz lemma in mathlib (dist_le_dist_of_mapsTo_ball) gives a related result for the Euclidean metric on balls, but not the hyperbolic metric. Searched Mathlib/Analysis/Complex/Schwarz.lean.

Lemma 40.7:
non-included
The uniqueness of geodesics in Busemann spaces is not in mathlib. Searched for "Busemann" and "CAT" and "nonpositive curvature" in mathlib. No metric geometry of nonpositive curvature spaces exists in mathlib.

Lemma 41.2:
non-included
The formula for geodesic curvature in terms of connection matrices and a moving frame is part of surface theory not formalized in mathlib. Searched Mathlib/Geometry/Manifold/ and Mathlib/Analysis/.

Theorem 41.3 (Gauss-Bonnet with boundary, for discs):
non-included
The Gauss-Bonnet theorem for domains with boundary (relating total geodesic curvature, Gauss curvature integral, and 2pi) is not in mathlib. Searched for "GaussBonnet" and "Gauss Bonnet" across mathlib with no results. No Gauss-Bonnet theory of any kind in mathlib.

Corollary 41.4:
non-included
The angle sum formula for geodesic triangles (alpha_1 + alpha_2 + alpha_3 = pi + integral of Gauss curvature) is a consequence of Gauss-Bonnet not formalized in mathlib. Searched Mathlib/Geometry/ and Mathlib/Analysis/. Not present.
