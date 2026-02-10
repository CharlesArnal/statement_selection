Theorem 1.7:
non-included
The Bolyai-Gerwien theorem (scissors congruence of equal-area polygons) is not formalized in mathlib. Searched in Mathlib/Geometry/ and Mathlib/MeasureTheory/ for "scissors", "congruent", "ScissorsCongruent" -- no results found.

Corollary 1.9:
non-included
A refinement of the Bolyai-Gerwien theorem restricting to translations and half-turns. Since the base theorem (1.7) is absent, this corollary is also absent. Searched for "scissors" in all of mathlib with no results.

Theorem 1.11:
non-included
Hadwiger invariants for scissors congruence under translations only. This is a specialized result in combinatorial geometry not present in mathlib. Searched for "Hadwiger", "scissors" -- no results.

Theorem 2.1:
non-included
Pick's theorem relating the area of an integer polygon to interior and boundary lattice points. Searched for "Pick", "lattice.*point", "lattice.*polygon" in mathlib -- no results found. This classical combinatorial geometry result is not in mathlib.

Fact 2.6:
non-included
Any two minimal integer triangles are integer affine equivalent. A specialized lattice geometry fact not in mathlib. Searched for "lattice.*triangle", "integer.*affine" -- no results.

Fact 2.8:
non-included
Additivity of Pick's theorem under polygon decomposition. Since Pick's theorem itself is not in mathlib, this supporting fact is also absent.

Fact 2.9:
non-included
Pick's theorem for minimal triangles. Not in mathlib since Pick's theorem is not formalized there.

Fact 2.10:
non-included
A diffusion-based argument for Pick's theorem. This is a heuristic/physical argument specific to the textbook, not a standard mathematical result for formalization.

Fact 2.11:
non-included
Convergence of the diffusion argument to the area. Part of the textbook's heuristic proof of Pick's theorem, not in mathlib.

Fact 2.12:
non-included
Zero net flow across boundary in the diffusion argument. Part of the textbook's heuristic proof of Pick's theorem, not in mathlib.

Theorem 3.4:
non-included
The shoelace formula expressed via winding numbers: the signed area equals the sum of areas weighted by winding numbers. Searched for "shoelace", "signedArea", "signed_area", "winding" in mathlib -- no formalization of the shoelace formula or winding number in this combinatorial form was found.

Proposition 4.1:
non-included
Invariance of the winding number under continuous deformation of the point (not crossing the curve). Searched for "windingNumber", "winding_number", "WindingNumber" in mathlib -- no results. Mathlib does not have a formalization of the winding number for polygonal loops.

Corollary 4.2:
non-included
Winding number is zero for points that can be moved to infinity without crossing the loop. Same search as 4.1 -- winding number not formalized in mathlib for this context.

Proposition 4.3:
non-included
Winding number changes by 1 when crossing an edge. Winding number for polygonal loops not in mathlib.

Proposition 4.6:
non-included
A polygonal loop with N simple self-intersections divides the plane into N + 2 regions. This is a combinatorial topology result about plane curves not present in mathlib.

Fact 5.1:
non-included
Relation between winding numbers and the word associated to a loop avoiding two points. A combinatorial topology result specific to the free group on two generators; not in mathlib in this form.

Fact 5.2:
non-included
Surjectivity of the map from loops to words. Not in mathlib.

Theorem 5.3:
non-included
Independence of the word associated to a loop from the choice of rays. A result about the fundamental group of the plane minus two points, not formalized in mathlib at this level.

Proposition 5.4:
non-included
Structure of words when one point can be moved to infinity. Not in mathlib.

Proposition 5.5:
non-included
Structure of words when two points can be connected without crossing the loop. Not in mathlib.

Proposition 5.6:
non-included
Classification of words for simple polygons. Not in mathlib.

Proposition 6.1:
non-included
Direction bound for billiards in rational-angle polygons. Searched for "billiard" in mathlib -- no results. Billiards theory is not formalized in mathlib.

Theorem 7.1:
included
The Poincare recurrence theorem. Mathlib has this in Mathlib/Dynamics/Ergodic/Conservative.lean, specifically `MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds` (topological version) and `MeasureTheory.MeasurePreserving.conservative` showing that finite-measure-preserving maps are conservative, which implies recurrence.

Theorem 7.4:
non-included
Liouville's theorem stating the billiards map is area-preserving in phase space coordinates. This specific billiards result is not in mathlib. While mathlib has measure-preserving maps, the concrete billiards application is absent.

Theorem 7.5:
included
This is the core statement of the Poincare recurrence theorem: if a measure-preserving map has a set of positive measure, some point returns to that set. This is formalized in mathlib as `MeasureTheory.Conservative` and related results in Mathlib/Dynamics/Ergodic/Conservative.lean.

Proposition 8.1:
non-included
Characterization of the equal-angle law for billiard reflections via critical points of path length. Billiards theory is not in mathlib.

Fact 8.2:
non-included
Reflective property of ellipses (billiard trajectory from one focus reaches the other). Not in mathlib. Searched in Mathlib/Geometry/Euclidean/ -- no ellipse reflection property found.

Theorem 8.3:
non-included
Existence of periodic billiard trajectories in strictly convex domains. This is Birkhoff's theorem, a deep result in dynamical systems not in mathlib.

Proposition 8.5:
non-included
Constraint on angles for optical devices. A specialized optics/billiards result not in mathlib.

Proposition 8.6:
non-included
Constraint on lengths for equal-angle optical devices. Not in mathlib.

Proposition 8.7:
non-included
General constraint l/m <= sin(beta)/sin(alpha) for optical devices. Not in mathlib.

Lemma 9.1:
non-included
Invariance of resonance frequencies under Euclidean motions. This is about eigenvalues of the Laplacian on planar domains; not formalized in mathlib at this level.

Lemma 9.2:
non-included
Scaling law for resonance frequencies. Eigenvalue theory of the Laplacian on domains is not developed in mathlib.

Theorem 9.3:
non-included
Properties of the principal frequency/mode: uniqueness and sign-definiteness. While mathlib has spectral theory for self-adjoint operators, the specific Dirichlet eigenvalue theory for planar domains is not developed.

Theorem 10.1:
included
The minimum of the Rayleigh quotient is the smallest eigenvalue. Mathlib has this in Mathlib/Analysis/InnerProductSpace/Rayleigh.lean as `IsSelfAdjoint.hasEigenvector_of_isMinOn` and related results, which establish that the minimum of the Rayleigh quotient over a sphere yields an eigenvector with the corresponding eigenvalue.

Corollary 10.2:
included
The Rayleigh quotient is bounded below by the smallest eigenvalue. This follows from the Rayleigh quotient theory in Mathlib/Analysis/InnerProductSpace/Rayleigh.lean, specifically the results about `iInf` of the Rayleigh quotient.

Theorem 10.3:
non-included
Variational characterization of the principal frequency via the Rayleigh quotient for the Laplacian on a region. While mathlib has the abstract Rayleigh quotient theory, the specific application to Laplacian eigenvalues on planar domains is not present.

Corollary 10.5:
non-included
Domain monotonicity of the principal Dirichlet eigenvalue (larger domain implies smaller frequency). This PDE result is not in mathlib.

Theorem 10.7:
non-included
Generalized Rayleigh quotient minimum equals the smallest eigenvalue of B^{-1}A. While related to the Rayleigh quotient theory in mathlib, this specific generalized form is not present.

Corollary 10.8:
non-included
Upper bound on principal frequency via finite-element-type approximation. Not in mathlib.

Lemma 11.3:
non-included
Steiner symmetrization preserves area. Searched for "Steiner", "symmetrization", "Symmetrization" in mathlib. While there are some symmetrization-related files, the specific Steiner symmetrization for planar regions and its area-preserving property are not formalized.

Theorem 11.4:
non-included
Steiner symmetrization decreases (or preserves) perimeter. Not in mathlib.

Lemma 11.5:
non-included
Altitude symmetrization of non-equilateral isosceles triangles decreases perimeter. Not in mathlib.

Theorem 11.6:
non-included
Iterated altitude symmetrization converges to equilateral triangles. Not in mathlib.

Theorem 11.7:
non-included
Steiner symmetrization decreases (or preserves) the principal frequency. Not in mathlib.

Corollary 11.9:
non-included
Among all triangles of given area, the equilateral one minimizes the principal frequency. This is the Faber-Krahn inequality for triangles, not in mathlib.

Fact 12.3:
non-included
Any two smooth loops with the same period can be deformed into each other. This is a statement about the path-connectedness of the space of smooth loops. Searched in Mathlib/Topology/ -- not found in this form.

Proposition 12.5:
non-included
Deformation invariance of the winding number for smooth loops. The smooth winding number is not formalized in mathlib.

Corollary 12.6:
non-included
The man-dog-lamppost theorem (Rouche-type result for smooth loops). Not in mathlib.

Theorem 13.1:
non-included
Nonzero winding number implies existence of a solution to F(p) = q. This is a topological degree theory result. Searched for "degree", "winding" in the topology directories -- mathlib does not have topological degree theory for planar maps.

Corollary 13.3:
non-included
Existence of fixed points for bounded perturbations of the identity. A corollary of degree theory, not in mathlib.

Theorem 13.5:
non-included
The winding number computed as the sum of signs of the Jacobian at preimages. This is the degree formula from differential topology, not in mathlib.

Lemma 14.1:
included
The multiplicity of a root equals the smallest m such that the m-th derivative is nonzero. Mathlib has `rootMultiplicity` in Mathlib/Algebra/Polynomial/RingDivision.lean and the relationship to derivatives in Mathlib/Algebra/Polynomial/FieldDivision.lean (`lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors`), which establishes this characterization.

Theorem 14.3:
non-included
The winding number of f composed with a circle equals the sum of root multiplicities inside the circle (argument principle). Searched for "argument_principle", "ArgumentPrinciple", "countZeros" -- not found. The argument principle is not formalized in mathlib.

Corollary 14.7:
non-included
Nonnegativity of the winding number for polynomial maps on circles. Not in mathlib (depends on the argument principle).

Corollary 14.9:
non-included
Monotonicity of the winding number with respect to the radius. Not in mathlib.

Theorem 15.2:
non-included
Deformation invariance of the linking number integral for curves in R^3. Searched in Mathlib/Topology/ for "linking" -- not found. Linking numbers are not formalized in mathlib.

Corollary 15.3:
non-included
Curves in complementary half-spaces have linking number zero. Not in mathlib.

Proposition 16.4:
non-included
Umlaufsatz: the rotation number of an embedded loop is +/- 1. Searched for "Umlaufsatz", "umlauf", "rotationNumber", "rotation_number" -- not found in mathlib.

Theorem 16.5:
non-included
Whitney's formula relating rotation number to self-intersection signs. Not in mathlib.

Fact 16.7:
non-included
Deformation invariance of the rotation number for immersed loops. Not in mathlib.

Theorem 17.1:
non-included
Whitney-Graustein theorem: immersed loops are classified up to regular homotopy by rotation number. Searched for "Whitney.*Graustein" -- not found in mathlib. This is a differential topology result not present in mathlib.

Theorem 17.2:
non-included
Classification of immersed loops with simple self-intersections via Arnold moves. Not in mathlib.

Proposition 17.4:
non-included
Existence and properties of Arnold's J^+, J^- invariants. Not in mathlib.

Fact 17.5:
non-included
J^+ - J^- equals the number of self-intersection points. Not in mathlib.

Proposition 17.8:
non-included
Viro-Gutkin formula for the J^- invariant. Not in mathlib.

Fact 18.1:
non-included
Sign of the triple point triangle is invariant under loop reversal. Not in mathlib.

Fact 18.2:
non-included
Triple point move reverses the sign of the triangle. Not in mathlib.

Theorem 18.3:
non-included
Existence of the strange invariant St(c) for immersed loops. Not in mathlib.

Proposition 18.5:
non-included
Shumakovich formula for the strange invariant. Not in mathlib.

Fact 19.1:
non-included
Classification of conics. While mathlib has some algebraic geometry, the explicit classification of real conics in the plane is not formalized in this form.

Fact 19.2:
non-included
Union of algebraic curves is algebraic. This follows from the product of defining polynomials. While the algebra is trivially available in mathlib (product of polynomials), the specific statement about algebraic sets is not formalized for the real plane in this textbook form.

Fact 19.3:
non-included
Intersection of algebraic curves is algebraic (via sum of squares of defining polynomials). Similar to 19.2, not formalized as a statement about plane algebraic curves in mathlib.

Lemma 19.5:
non-included
Five points determine a conic. This is a classical projective geometry result. Searched in Mathlib/Geometry/ and Mathlib/AlgebraicGeometry/ -- not found in this form.

Theorem 19.6:
non-included
Interpolation: d(d+3)/2 points determine an algebraic curve of degree d. Not in mathlib.

Theorem 19.7:
non-included
Rational parametrizations trace out parts of algebraic curves. While mathlib has algebraic geometry foundations, this specific statement about rational curves in R^2 is not present.

Theorem 19.9:
non-included
Trigonometric rational parametrizations trace out parts of algebraic curves. Not in mathlib.

Theorem 20.3:
non-included
Linkage positions can be described by polynomial equalities and inequalities (Tarski-Seidenberg type result). While mathlib might have some quantifier elimination results, this specific application to linkages is not present.

Lemma 20.7:
included
The resultant of two polynomials is zero if and only if they have a common factor. Mathlib has the resultant in Mathlib/RingTheory/Polynomial/Resultant/Basic.lean, with `Polynomial.resultant_eq_zero_iff` establishing that the resultant is zero iff the polynomials are not coprime (i.e., share a common factor).

Corollary 20.8:
non-included
The resultant with respect to z yields an algebraic curve containing the projection. While mathlib has the resultant, this specific geometric application to elimination theory for algebraic curves is not formalized.

Proposition 21.1:
included
A degree d curve intersects a line in at most d points (unless the line is contained in the curve). This follows from `Polynomial.card_le_degree_of_subset_roots` in Mathlib/Algebra/Polynomial/Roots.lean, which states that a polynomial of degree d has at most d roots. The geometric statement is an immediate consequence.

Proposition 21.2:
non-included
An algebraic curve of odd degree is unbounded. This uses the intermediate value theorem and the fact that odd-degree polynomials always have a root. While both ingredients are in mathlib, the specific geometric conclusion about unbounded algebraic curves is not formalized.

Proposition 21.3:
non-included
A degree d curve intersects a conic in at most 2d points. This is a special case of Bezout's theorem, which is not in mathlib for plane curves.

Theorem 21.5:
non-included
Bezout's theorem for plane algebraic curves. Searched for "Bezout", "bezout" in mathlib. While mathlib has Bezout domains (Mathlib/RingTheory/Bezout.lean) as an algebraic concept, Bezout's theorem for intersection of plane algebraic curves is not formalized.

Theorem 22.4:
non-included
Implicit function theorem applied to nonsingular curves: they decompose into ovals and unbounded components. While mathlib has the implicit function theorem (Mathlib/Analysis/Calculus/Implicit.lean), the topological classification of components of nonsingular algebraic curves is not formalized.

Proposition 22.7:
non-included
A nonsingular cubic has at most one oval. Not in mathlib.

Proposition 22.8:
non-included
A nonsingular cubic has at most three unbounded components. Not in mathlib.

Lemma 22.9:
non-included
A conic through points inside and outside an oval must intersect the oval twice. Not in mathlib.

Proposition 22.10:
non-included
Oval count bound for degree 4 nonsingular curves. Not in mathlib.

Theorem 22.11:
non-included
Harnack's theorem on the maximal number of ovals of nonsingular algebraic curves. Searched for "Harnack", "harnack" -- not found in mathlib (Harnack in mathlib refers to Harnack's inequality in PDE, not this algebraic geometry result). The algebraic curve version is not present.

Lemma 23.3:
non-included
Node structure at intersection points of algebraic curves when gradients are independent. Not in mathlib.

Proposition 24.1:
non-included
Patchworking: for small t, the number of positive roots matches the number of sign changes (Descartes' rule variant). Searched for "Descartes", "sign.*change", "RuleOfSigns" -- not found. Descartes' rule of signs is not in mathlib.

Lemma 25.1:
non-included
Bounds on tropical addition approximation. Tropical geometry is present in mathlib (Mathlib/Order/Tropical.lean defines the tropical semiring), but this specific approximation lemma relating classical and tropical addition is not formalized.

Theorem 25.4:
non-included
Convergence of Log_s of algebraic curves to tropical curves as s -> infinity. Tropical curve theory and this Kapranov-type theorem are not in mathlib.

Fact 26.3:
non-included
Two projective points determine a unique projective line. While mathlib has projective spaces (Mathlib/LinearAlgebra/ProjectiveSpace/), this specific incidence axiom for the projective plane is not formalized as a standalone result in this textbook form.

Fact 26.4:
non-included
Two projective lines intersect in exactly one point. Similar to 26.3, not formalized as a standalone statement about the real projective plane in mathlib.

Proposition 26.9:
non-included
Projective duality transforms (c_lambda, l_gamma) configurations to (l_gamma, c_lambda) configurations. Not in mathlib.

Lemma 27.6:
non-included
Points at infinity of a projective curve with exactly d such points are nonsingular. Not in mathlib.

Theorem 27.7:
non-included
A nonsingular projective curve consists of finitely many projective ovals. Not in mathlib.

Theorem 27.10:
non-included
Harnack's bound for projective curves: at most d(d-3)/2 + 2 ovals. Not in mathlib.

Theorem 28.6:
non-included
Existence of Delaunay triangulations. Searched for "Delaunay", "Voronoi" -- not found in mathlib. Computational geometry constructions are not formalized.

Lemma 28.7:
non-included
Delaunay flips decrease the integral of x^2 + y^2 approximation. Not in mathlib.

Theorem 28.8:
non-included
Uniqueness criterion for triangles in Delaunay triangulations. Not in mathlib.

Fact 29.4:
non-included
D_1 D_2 = 0 for boundary operators of a planar complex. While mathlib has simplicial complexes (Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean) and simplicial homology (Mathlib/AlgebraicTopology/), the specific boundary operator formulation for planar complexes as presented in this textbook is not directly matched in mathlib's approach.

Theorem 29.7:
non-included
b_0 equals the number of connected components of the complex. While mathlib has connected components and simplicial homology, this specific identification for the textbook's notion of planar complex is not formalized in the same way.

Theorem 30.2:
non-included
b_2 = 0 for planar complexes. Not in mathlib in this form.

Theorem 30.4:
non-included
Euler characteristic equals components minus holes for planar complexes. Not in mathlib.

Corollary 30.5:
non-included
b_1 equals the number of holes for planar complexes. Not in mathlib.

Proposition 31.5:
non-included
For a connected combinatorial surface, b_2 = 1 if orientable, 0 otherwise. Not in mathlib in this combinatorial form.

Proposition 31.8:
non-included
The Euler characteristic of an orientable surface is even. Not in mathlib.

Corollary 31.9:
non-included
b_1 is even for an orientable surface. Not in mathlib.

Lemma 32.1:
non-included
Homotopy class of a constant loop depends only on the connected component. While mathlib has fundamental groupoid and path homotopy (Mathlib/Topology/Homotopy/), the specific combinatorial version for abstract complexes is not directly present.

Lemma 33.3:
non-included
The edge vector v_l of a combinatorial loop lies in ker(D_1). Not in mathlib for this textbook's formulation.

Theorem 33.4:
non-included
Homotopic loops have edge vectors differing by an element of im(D_2). Not in mathlib for this textbook's formulation.

Corollary 33.5:
non-included
The pairing with cocycles yields a homotopy invariant. This is essentially the de Rham-type pairing for simplicial cohomology, but the textbook's specific formulation is not in mathlib.

Lemma 33.7:
non-included
Coboundaries give trivial winding numbers. Not in mathlib for this formulation.

Theorem 34.2:
non-included
In a hyperbolic triangle, the angle sum is less than pi. While mathlib has the upper half-plane model (Mathlib/Analysis/Complex/UpperHalfPlane/) with its metric structure, the specific statement about hyperbolic triangle angle sums is not formalized.

Fact 34.5:
non-included
Hyperbolic circles are Euclidean circles with specific center and radius. While mathlib has the hyperbolic metric on the upper half-plane (Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean), this specific characterization of hyperbolic circles is not stated.

Theorem 35.1:
included
The hyperbolic distance equals the infimum of path lengths. This is essentially the definition of a length metric space. Mathlib has `dist_eq_iInf_of_length` type results and the upper half-plane metric in Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean, which defines the distance in the upper half-plane model and establishes it as a metric space.

Theorem 35.2:
non-included
Geodesics are the unique length-minimizing paths in the hyperbolic plane. While mathlib has the metric on the upper half-plane, the characterization of geodesics as length minimizers is not explicitly formalized.

Corollary 35.3:
included
The triangle inequality for hyperbolic distance: dist(z,w) <= dist(z,u) + dist(u,w). This is `dist_triangle` in mathlib, which holds for any metric space. Since the upper half-plane is a metric space in mathlib (Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean), this follows automatically.

Theorem 35.6:
non-included
The area of any hyperbolic triangle is less than pi. Not in mathlib.

Theorem 35.7:
non-included
Gauss-Bonnet for hyperbolic triangles: area = pi - alpha - beta - gamma. Searched for "gauss.*bonnet", "GaussBonnet" -- not found in mathlib. The Gauss-Bonnet theorem is not formalized.

Fact 36.2:
non-included
Transitivity of hyperbolic isometries on points. While mathlib has the action of SL(2,R) on the upper half-plane, the specific statement about transitivity is not immediately formalized as a standalone result.

Fact 36.3:
non-included
Transitivity of hyperbolic isometries on geodesics. Not in mathlib.

Fact 36.4:
non-included
Any hyperbolic triangle can be normalized by an isometry. Not in mathlib.

Fact 37.3:
non-included
Conservation of speed along geodesics in curved geometries. This is a general Riemannian geometry fact not formalized in mathlib for this specific setting.

Lemma 37.4:
non-included
First-order approximation of arclength for displaced curves. Not in mathlib.

Theorem 37.5:
non-included
Length-minimizing constant-speed curves satisfy the geodesic equation. This is a foundational result in Riemannian geometry. While mathlib has some differential geometry (Mathlib/Geometry/Manifold/), the calculus of variations and geodesic equation are not formalized.

Fact 38.1:
non-included
Tangent geodesics are identical (uniqueness of geodesics with given initial conditions). A consequence of ODE uniqueness, but not formalized for this geometric setting in mathlib.

Fact 38.2:
non-included
Vertical lines are geodesics in translationally invariant geometries. Not in mathlib.

Fact 38.3:
non-included
Horizontal lines at critical points of psi are geodesics. Not in mathlib.

Fact 38.4:
non-included
Geodesics can intersect infinitely many times. Not in mathlib.

Proposition 38.5:
non-included
Equivalence of geodesics under polar coordinate change for rotationally invariant geometries. Not in mathlib.

Fact 38.6:
non-included
Radial lines are geodesics in rotationally invariant geometries. Not in mathlib.

Fact 38.7:
non-included
Criterion for circles to be geodesics in rotationally invariant geometries. Not in mathlib.

Fact 38.8:
non-included
Geodesics can be periodic. Not in mathlib.

Fact 38.9:
non-included
Geodesic segments need not be shortest paths. Not in mathlib.

Fact 38.10:
non-included
Geodesics can self-intersect infinitely many times. Not in mathlib.

Theorem 39.5:
non-included
Integrated curvature of a region bounded by a periodic geodesic equals 2pi. A version of Gauss-Bonnet not in mathlib.

Theorem 39.6:
non-included
General Gauss-Bonnet for geodesic n-gons in curved geometries. Not in mathlib.

Proposition 40.1:
non-included
Discrete Gauss-Bonnet: sum of discrete curvatures equals 2pi times Euler characteristic. This combinatorial version of Gauss-Bonnet for polyhedral surfaces is not in mathlib.

Fact 40.7:
non-included
Formula for discrete curvature at vertices of translation surfaces. Not in mathlib.

Fact 40.9:
non-included
Billiard trajectories correspond to geodesics on translation surfaces. Not in mathlib.
