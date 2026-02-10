# All Mathematical Statements in "Geometry and Topology in the Plane"

## Chapter 1: Cutting and pasting polygons

**Theorem 1.7.** If two polygons have the same area, they are scissors congruent.

**Corollary 1.9.** Theorem 1.7 is still true if we restrict the notion of scissors congruence to using only translations and 180 degree rotations (instead of all Euclidean transformations).

**Theorem 1.11.** If two polygons P_1 and P_2 are scissors congruent in a way which uses only translations (and no other Euclidean transformations), then their Hadwiger invariants must agree: had_w(P_1) = had_w(P_2) for all w.

## Chapter 2: Integer polygons

**Theorem 2.1.** (Pick's theorem) The formula (2.5) for integer polygons is an exact equality. That is, area(P) = (number of integer points in the interior of P) + 1/2 (number of integer points on the boundary of P, including vertices) - 1.

**Fact 2.6.** Any two minimal integer triangles are integer affine equivalent.

**Fact 2.8.** Take an integer polygon P and cut it into two integer polygonal pieces P_1, P_2 (for simplicity, let's say by a straight cut going from one integer boundary point of P to another). If Pick's theorem holds for P_1 and P_2, then it also holds for P.

**Fact 2.9.** Pick's theorem holds for minimal triangles.

**Fact 2.10.** A very small time after the oil is placed, the amount of oil in P is exactly the right hand side of Pick's formula (2.5).

**Fact 2.11.** As time passes, the amount of oil in P gets closer and closer to the area of P.

**Fact 2.12.** At any time, the net flow rate of oil across the boundary of P is zero.

## Chapter 3: The shoelace formula and the winding number

**Theorem 3.4.** Take a polygonal loop p, with vertices (v_0, v_1, ..., v_n = v_0). Then (1/2)(v_0 x v_1 + v_1 x v_2 + ... + v_{n-1} x v_n) = sum_R area(R) wind(p, some point in R). Here, the sum is over all regions R into which p divides the plane, and wind(p, .) are the winding numbers of p.

## Chapter 4: The winding number (continued)

**Proposition 4.1.** If we move q around without crossing p, wind(p,q) remains constant.

**Corollary 4.2.** Suppose that q can be moved to infinity without crossing p. Then wind(p,q) = 0.

**Proposition 4.3.** Let q_0, q_1 be two points which lie on either side of one of the edges of p. We assume that all other edges lie outside the picture. Then wind(p, q_1) = wind(p, q_0) + 1.

**Proposition 4.6.** Take a polygonal loop which has N simple self-intersections, and no self-intersections of any other kind. It divides the plane into N + 2 regions.

## Chapter 5: Loops avoiding two points

**Fact 5.1.** The winding numbers of a loop can be read off from the associated word: wind(p, a) is the number of A letters minus the number of A^{-1} letters; and wind(p, b), the number of B letters minus the number of B^{-1} letters.

**Fact 5.2.** Every word in our language comes from some loop.

**Theorem 5.3.** The word associated to p is independent of the choice of rays. It also remains the same if we move a and b (as long as we don't cross p).

**Proposition 5.4.** Suppose that we can move a to infinity without crossing p. Then the word of p is one of the following: [], [B...B] (a bunch of repeated B) or [B^{-1}...B^{-1}] (a bunch of repeated B^{-1}).

**Proposition 5.5.** Suppose that we can move from a to b without crossing p. Then the word of p is one of the following: [], [BA...BA] (an even number of letters, with A and B alternating), [A^{-1}B^{-1}...A^{-1}B^{-1}] (an even number of letters, with A^{-1} and B^{-1} alternating).

**Proposition 5.6.** For an actual polygon, the word is one of these: [], [A], [A^{-1}], [B], [B^{-1}], [AB] = [BA], [A^{-1}B^{-1}] = [B^{-1}A^{-1}].

## Chapter 6: Introduction to billiards

**Proposition 6.1.** Suppose that we have a rational-angle polygon, in which all interior angles are integer multiples of 180 degrees/M for some natural number M. Then, any single billiards trajectory moves in at most 2M different directions.

## Chapter 7: Phase space

**Theorem 7.1.** (Poincare recurrence theorem) Inside any polygon, choose a point and a direction, in any way you want. Then, there is a billiards trajectory whose starting position and direction are arbitrarily close to the ones we picked, and which after some amount of bounces, returns to a position and direction arbitrarily close to the ones we picked.

**Theorem 7.4.** (Liouville's theorem) In (s,t) coordinates on the phase space, the billiards map is area-preserving.

**Theorem 7.5.** Let U be a subset of phase space with positive area. Then, there is some p in U and an M > 0 such that T^M(p) is in U.

## Chapter 8: Billiards in curved domains

**Proposition 8.1.** S'(t) = 0 if and only if the trajectory from p to c(t) to q satisfies the equal-angle law.

**Fact 8.2.** If a billiards trajectory in the ellipse starts at one focus, then after bouncing off once it will reach the other focus.

**Theorem 8.3.** Suppose that our billiards region has no corners, and is strictly convex. Then, for every n >= 2, there is (at least) one periodic billiards trajectory with n bounces.

**Proposition 8.5.** If the input and output lengths are equal, l = m, then the angles must satisfy beta > alpha; you can't squeeze the light into a smaller angle!

**Proposition 8.6.** If the input and output angles are equal, alpha = beta, then the lengths must satisfy l <= m: you can't make the output hole smaller than the input!

**Proposition 8.7.** In general, for the optical contraption to be theoretically possible, we need l/m <= sin(beta)/sin(alpha).

## Chapter 9: First computations

**Lemma 9.1.** The resonance frequencies of a region are unchanged under translations, rotations, and reflections (it is a congruence invariant).

**Lemma 9.2.** Scaling up a region (in both directions at once!) by some factor c results in a new region whose resonance frequencies are 1/c times those of the original one.

**Theorem 9.3.** (i) For the principal frequency, there is only one function f satisfying (9.2), up to multiplication by a constant (we call this function the principal mode). (ii) Among all resonance frequencies, the principal frequency is the only one for which the function f is either >= 0 on all of U, or <= 0 on all of U; any other resonance mode has both positive and negative values.

## Chapter 10: An extremal characterization

**Theorem 10.1.** The minimal value of the Rayleigh quotient w . Aw / (w . w) is the lowest eigenvalue of A, and the vectors w that achieve that value are the corresponding eigenvectors.

**Corollary 10.2.** Let mu be the smallest eigenvalue of A. Then mu <= w . Aw / (w . w) for all nonzero vectors w. Moreover, if equality holds, then w is an eigenvector for mu.

**Theorem 10.3.** Let lambda be the principal frequency of a region U. Then lambda^2 <= (integral_U ||grad f||^2) / (integral_U f^2) for any function f: U -> R which is zero on the boundary of U, but not altogether zero. Equality holds exactly when f is the resonance mode corresponding to lambda.

**Corollary 10.5.** Suppose that we have two regions with U subset V. Then the principal frequency of U is greater than or equal to the principal frequency of V; meaning, lambda_U >= lambda_V.

**Theorem 10.7.** Let A and B be symmetric matrices of size n. We also require that B is positive, in the sense that w . Bw > 0 for all nonzero w in R^n. Then, the minimum of the quantity w . Aw / (w . Bw), w in R^n nonzero, is the lowest eigenvalue of B^{-1}A.

**Corollary 10.8.** Pick functions f_1, ..., f_n on U, each of which is zero on the boundary, and compute the associated matrices A and B. Then the principal frequency lambda satisfies lambda^2 <= any root of p(t) = det(tB - A).

## Chapter 11: Symmetrization

**Lemma 11.3.** The area of S_l(U) is the same as that of U.

**Theorem 11.4.** The perimeter of S_l(U) is less or equal than the perimeter of U.

**Lemma 11.5.** Take an isosceles triangle which is not equilateral. If we apply altitude symmetrization to it, then the new triangle has smaller perimeter than the old one.

**Theorem 11.6.** Start with any isosceles triangle, and apply altitude symmetrization over and over. The result is a sequence of isosceles triangles, which either turns equilateral after finitely many steps, or else becomes closer and closer to equilateral in the limit.

**Theorem 11.7.** The principal frequency of S_l(U) is less or equal than that of U.

**Corollary 11.9.** Among all triangles with a given area, the equilateral one achieves the minimum of the principal frequency.

## Chapter 12: Smooth loops

**Fact 12.3.** Any two smooth loops (with the same T) can be deformed into each other.

**Proposition 12.5.** Take two smooth loops c_0, c_1 (with the same T) which avoid q. If they can be deformed into each other without ever passing through q, which means that all c_s avoid q, then wind(c_0, q) = wind(c_1, q).

**Corollary 12.6.** (Man-dog-lamppost theorem) Suppose that c_0, c_1 are smooth loops (with the same period T), and q a point, such that ||c_1(t) - c_0(t)|| < ||c_0(t) - q|| for all t. Then wind(c_0, q) = wind(c_1, q).

## Chapter 13: Equations in two variables

**Theorem 13.1.** Suppose that wind(d,q) != 0. Then there must be a p in R^2 with ||p|| < r, which solves F(p) = q.

**Corollary 13.3.** Suppose that k(a,b) and l(a,b) are functions (defined on R^2 and smooth) which are bounded (above and below, with bounds that hold for all a,b). Then, the system of equations a = k(a, b), b = l(a, b) always has a solution.

**Theorem 13.5.** Look at a loop (13.3). Assume that for every p as in (13.4), the partial derivatives dF/da and dF/db, taken at the point (a,b) = p, are linearly independent vectors. Then wind(d,q) = sum_p sign(dF/da x dF/db).

## Chapter 14: Complex polynomials

**Lemma 14.1.** The multiplicity of a root w is the smallest m such that the m-th derivative of f at w is nonzero.

**Theorem 14.3.** For a loop d(t) = f(re^{it}), wind(d,0) = sum_{|w|<r, f(w)=0} mult(f, w), where the sum is over all roots of f lying inside the circle of radius r.

**Corollary 14.7.** Take d(t) = p(re^{it}) as before. For every u where it is defined, the winding number wind(p, u) is nonnegative; and it is > 0 if and only if there is a solution of p(z) = u with z inside the circle of radius r.

**Corollary 14.9.** Take d_1 = p(r_1 e^{it}), d_2 = p(r_2 e^{it}), for some r_2 > r_1 > 0. Then, for every complex number u where both winding numbers are defined, we have wind(d_2, u) >= wind(d_1, u).

## Chapter 15: The linking number

**Theorem 15.2.** The integral (15.9) is unchanged if we deform c and d, as long as they don't cross each other.

**Corollary 15.3.** Suppose that c lies in {z > 0} subset R^3, and d in the region {z < 0} subset R^3. Then their linking number, as defined by (15.9), is zero.

## Chapter 16: Immersed loops and the rotation number

**Proposition 16.4.** (Umlaufsatz) For an embedded loop c, one always has rot(c) = +/- 1.

**Theorem 16.5.** (Whitney's formula) Let c be an immersed loop with simple selfintersections, and which has an outside starting point. Then, rot(c) = +/- 1 + sum_q sigma(q).

**Fact 16.7.** The rotation number is deformation invariant within the class of immersed loops. This means that if c_s(t) is a deformation of loops (0 <= s <= 1), such that for every value of the parameter s the loop t -> c_s(t) is immersed, then rot(c_0) = rot(c_1).

## Chapter 17: Arnold invariants

**Theorem 17.1.** (Whitney-Graustein) Take two immersed loops c_0(t) and c_1(t) with the same rotation number. Then, one can deform one into the other through immersed loops.

**Theorem 17.2.** Take two immersed loops with only simple selfintersections, and which have the same rotation number. Then, they can be transformed into each other by a composition of deformations preserving simple selfintersections, direct self-tangency moves, inverse self-tangency moves, and triple point moves.

**Proposition 17.4.** To each immersed loop c with simple selfintersections one can associate two integers J^-(c) and J^+(c), satisfying prescribed values for standard loops and prescribed behavior under self-tangency moves and triple point moves.

**Fact 17.5.** J^+(c) - J^-(c) is the number of selfintersection points of c.

**Proposition 17.8.** (Viro-Gutkin) One can compute the J^--invariant by the formula J^-(c) = 1 - sum_R wind(c, R)^2 + sum_q meanwind(c, q)^2.

## Chapter 18: Arnold invariants (continued)

**Fact 18.1.** The sign of the triangle does not change if we reverse the direction of the loop.

**Fact 18.2.** Suppose that we carry out a triple point move with our triangle. After that move, we get a new triangle whose sign is the opposite of the old one.

**Theorem 18.3.** To every immersed loop c with simple selfintersections, one can associate an integer St(c), satisfying prescribed behavior under triple point moves and invariance under other moves.

**Proposition 18.5.** (Shumakovich) Assuming an exterior starting point, one can compute the strange invariant by St(c) = sum_q sigma(q) meanwind(c, q).

## Chapter 19: Introduction to algebraic curves

**Fact 19.1.** The conics are of the following kinds: ellipses (including circles), parabolae, hyperbolae, unions of two lines, sets consisting of one point, and the empty set.

**Fact 19.2.** If C_1 and C_2 are algebraic curves, then so is C = C_1 union C_2.

**Fact 19.3.** If C_1 and C_2 are algebraic curves, then so is C = C_1 intersect C_2.

**Lemma 19.5.** For any 5 points in the plane, there is a conic which goes through all those points.

**Theorem 19.6.** Take some d >= 1, and choose d(d+3)/2 points in the plane. Then there is an algebraic curve of degree d which passes through all of them.

**Theorem 19.7.** Any two rational functions x(t) and y(t) parametrize part of an algebraic curve.

**Theorem 19.9.** Any two trigonometric rational functions x(theta) and y(theta) parametrize part of an algebraic curve.

## Chapter 20: Mechanical linkages and polynomial equations

**Theorem 20.3.** The set S of all possible positions of the pen can be described by polynomial equalities and inequalities. If, in that description, there is at least one equality, then S is a subset of an algebraic curve.

**Lemma 20.7.** If f and g share a root, then res_z(f,g) = 0. (More precisely, the resultant is zero exactly when f and g have a common factor.)

**Corollary 20.8.** If the polynomial h(x,y) = res_z(f,g) is nonzero, then the set S from (20.12) is a subset of the algebraic curve C = {h(x,y) = 0}.

## Chapter 21: Intersections of algebraic curves

**Proposition 21.1.** Let C be a degree d curve, and L a line. Then C intersects L in at most d points, except in the case where L is actually a subset of C.

**Proposition 21.2.** An algebraic curve of odd degree d can't be a bounded subset of the plane (it always goes out to infinity).

**Proposition 21.3.** Let C = {f(x,y) = 0} be a degree d curve, and D a conic. Then C intersects D in at most 2d points, with two exceptions.

**Theorem 21.5.** (Bezout's theorem) Let C_1 = {f_1(x,y) = 0} and C_2 = {f_2(x,y) = 0} be algebraic curves of degrees d_1 and d_2. Then, C_1 intersects C_2 in at most d_1 d_2 points, except when f_1 and f_2 have a common factor whose zero set has infinitely many points.

## Chapter 22: Nonsingular curves

**Theorem 22.4.** If f(x,y) = 0 is nonsingular, the curve C = {f(x,y) = 0} is a disjoint union of components of two kinds: bounded components (ovals), each of which can be traced out by an embedded loop; and unbounded components, which are embedded curves going off to infinity at both ends.

**Proposition 22.7.** A nonsingular algebraic curve of degree 3 has at most one oval.

**Proposition 22.8.** A nonsingular algebraic curve of degree 3 has at most three unbounded components.

**Lemma 22.9.** Suppose that C is a nonsingular algebraic curve. Take an oval O in C, a point p inside that oval, and another point q outside. If a conic goes through both p and q, it must intersect O at least twice.

**Proposition 22.10.** A nonsingular algebraic curve of degree 4 can have at most 4 ovals. Moreover, if it has 2 ovals nested inside each other, then it can't have any other ovals.

**Theorem 22.11.** (Harnack's theorem for the Euclidean plane) A nonsingular algebraic curve of degree d can have at most M ovals, where M = d(d-3)/2 + 2 if d is even, M = d(d-3)/2 + 1 if d is odd (this is for the Euclidean plane version -- the projective version gives (d-1)(d-2)/2).

## Chapter 23: Singular points

**Lemma 23.3.** Take polynomials f_1(x, y) and f_2(x, y). Let (x_0, y_0) be a solution both of f_1 = 0 and f_2 = 0. Suppose the gradient vectors are linearly independent. Then: for f = f_1 f_2, the equation f = 0 has a saddle-point node at (x_0, y_0); for g = f_1^2 + f_2^2, the equation g = 0 has a local-minimum node at (x_0, y_0).

## Chapter 24: Patchworking

**Proposition 24.1.** For small t, p_t has as many positive roots (solutions of p_t(x) = 0 with x > 0) as there are sign changes in the sequence (sigma_0, ..., sigma_d). More precisely, to each sign change sigma_i != sigma_{i+1} corresponds a root x approx t^{-i}.

## Chapter 25: Tropical geometry

**Lemma 25.1.** For a, b in R^{trop}, a + b <= log_s(s^a + s^b) <= a + b + 1/(s^{|a-b|} ln(s)).

**Theorem 25.4.** In the situation of (25.15), we have that as s -> infinity, Log_s(C_s cap (R^{>=0})^2) -> C_{trop}.

## Chapter 26: Projective geometry

**Fact 26.3.** Through any two (different) projective points, there is exactly one projective line.

**Fact 26.4.** Any two (different) projective lines intersect in exactly one projective point.

**Proposition 26.9.** If we take a (c_lambda l_gamma) configuration, and apply projective duality to all its points and lines, we get an (l_gamma c_lambda) configuration.

## Chapter 27: Algebraic curves in the projective plane

**Lemma 27.6.** Let f(x,y) be a polynomial of degree d. If the projective completion of the associated curve has exactly d points at infinity, then those points must be nonsingular.

**Theorem 27.7.** A nonsingular projective curve consists of a finite number of projective ovals (which one can think of as parametrized by embedded loops in P^2).

**Theorem 27.10.** A nonsingular projective curve of degree d consists of at most d(d-3)/2 + 2 ovals.

## Chapter 28: Delaunay triangulations

**Theorem 28.6.** For every finite set of points as in (28.2), there is a Delaunay triangulation.

**Lemma 28.7.** Suppose we have two adjacent triangles which form a convex quadrilateral and, by themselves, are not Delaunay. Apply a flip. Then, the new triangulation gives an approximate formula for integral of x^2 + y^2 which is less than that for the original triangulation.

**Theorem 28.8.** Suppose that T is a triangle whose vertices belong to our point set, and with the following property (which is stronger than what's in the definition of Delaunay triangulation): all the other points in our finite set lie outside (in the exterior of) the circumcircle of the triangle. Then, T occurs in every possible Delaunay triangulation.

## Chapter 29: Betti numbers

**Fact 29.4.** The boundary operators always satisfy D_1 D_2 = 0 (the zero matrix).

**Theorem 29.7.** b_0 is the number of components (parts not connected to each other) of the complex.

## Chapter 30: Betti numbers (continued)

**Theorem 30.2.** For a planar complex K, we always have b_2(K) = 0.

**Theorem 30.4.** For a planar complex K, the Euler characteristic is chi = (number of components of K) - (number of holes of K).

**Corollary 30.5.** For every planar complex, b_1 is the number of holes.

## Chapter 31: Surfaces

**Proposition 31.5.** Take a combinatorial surface which is connected (meaning that it's not divided into several mutually disconnected parts; equivalently, b_0 = 1). Then b_2 = 1 if the surface is orientable, and b_2 = 0 otherwise.

**Proposition 31.8.** The Euler characteristic of an orientable surface is always even.

**Corollary 31.9.** For an orientable surface, b_1 is even.

## Chapter 32: Combinatorial loops

**Lemma 32.1.** For a constant loop, the homotopy class depends only on the component of K in which it lies.

## Chapter 33: Combinatorial winding numbers and boundary operators

**Lemma 33.3.** The vector v_l always satisfies D_1 v_l = 0.

**Theorem 33.4.** Suppose that l_0 and l_1 are homotopic. Then v_{l_0} - v_{l_1} = D_2 x for some x in R^{n_2}.

**Corollary 33.5.** Fix some c in R^{n_1} such that D_2^t c = 0. Then, the number c . v_l in R is a homotopy invariant.

**Lemma 33.7.** If c = D_1^t b, then wind_c(l) = 0 for all loops l.

## Chapter 34: The hyperbolic plane

**Theorem 34.2.** In a hyperbolic triangle, the sum of the angles is always less than pi.

**Fact 34.5.** The hyperbolic circle with center (x, y) and radius r is exactly the ordinary Euclidean circle with center (x, cosh(r)y) and radius sinh(r)y.

## Chapter 35: Arclengths and areas

**Theorem 35.1.** For any two points z and w, dist(z, w) = min{length(c) for all paths c from z to w}.

**Theorem 35.2.** Given two points z and w, the paths of minimal length from z to w are precisely those that go along a geodesic (without ever turning back).

**Corollary 35.3.** For any three points z, u, w, we have dist(z, w) <= dist(z, u) + dist(u, w).

**Theorem 35.6.** The area of any hyperbolic triangle is < pi.

**Theorem 35.7.** (Gauss-Bonnet) For a hyperbolic triangle T, with angles (alpha, beta, gamma), area(T) = pi - alpha - beta - gamma.

## Chapter 36: Hyperbolic isometries

**Fact 36.2.** Given two points z and w, there is an isometry Phi such that Phi(z) = w.

**Fact 36.3.** Given two geodesics c and d, there is an isometry Phi such that Phi(c) = d.

**Fact 36.4.** Given any hyperbolic triangle, there is an isometry Phi such that after applying that isometry, one of the vertices of the triangle is i, and the other vertex is e^r i for some r > 0.

## Chapter 37: The geodesic equation

**Fact 37.3.** Along a solution c(t) of the geodesic equation, the speed (with respect to our curved geometry) e^{psi(c(t))} ||c'(t)|| is constant.

**Lemma 37.4.** Suppose that c'(t) is never zero. Then the arclength integrand for d(t) is approximately given by a formula involving the geodesic equation.

**Theorem 37.5.** Suppose that c(t), t in [a,b], is a curve that proceeds with constant speed in our geometry. Suppose also that among all curves connecting the endpoints c(a) and c(b), ours achieves the minimal possible arclength. Then c(t) is a solution of the geodesic equation.

## Chapter 38: Behaviour(s) of geodesics

**Fact 38.1.** If two geodesics become tangent at some point, then they trace out the same curve.

**Fact 38.2.** Any vertical line can be parametrized so that it becomes a geodesic.

**Fact 38.3.** If the derivative d psi/dy is zero (psi has a critical point) for some value of y, then that particular horizontal line is also a geodesic.

**Fact 38.4.** In general, it is possible for two geodesics to intersect each other more than once; in fact, they can intersect infinitely many times.

**Proposition 38.5.** (x(t), y(t)) is a geodesic for our rotationally invariant geometry if and only if (theta(t), rho(t)) is a geodesic for the geometry psi(e^rho) + rho.

**Fact 38.6.** In a rotationally invariant geometry, all radial lines (straight lines through the origin), parametrized in an appropriate way, are geodesics.

**Fact 38.7.** In a rotationally invariant geometry, the circle of radius r > 0 around the origin is a geodesic if and only if psi'(r) = -1/r.

**Fact 38.8.** In general, it is possible for a geodesic to come back to its starting point, and even to be periodic.

**Fact 38.9.** In general, it is possible for a segment of a geodesic to not be the shortest path between its endpoints.

**Fact 38.10.** It is possible for a geodesic to cross itself, even infinitely many times.

## Chapter 39: Curvature

**Theorem 39.5.** If the boundary of U is a periodic geodesic, the integrated curvature on U is integral_U (-Delta psi) dx dy = 2 pi.

**Theorem 39.6.** (General Gauss-Bonnet) In any curved geometry, let U be a geodesic n-gon. Then integral_U (-Delta psi) dx dy = alpha_1 + ... + alpha_n + (2 - n) pi.

## Chapter 40: Geometry of combinatorial surfaces

**Proposition 40.1.** The sum of the discrete curvatures at all vertices of the surface S equals 2 pi chi(S), where chi is the Euler characteristic.

**Fact 40.7.** If a vertex of the translation surface comes from a vertex of the triangle with an angle pi a/b (with a and b coprime), the discrete curvature at our vertex will be 2 pi (1-a).

**Fact 40.9.** The billiards motion in the triangle can be viewed as the motion along geodesics on the associated translation surface.
