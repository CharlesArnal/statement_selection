# Detailed Assessment: Statements in "The Polynomial Method" vs Mathlib

## Chapter: Introduction

Corollary 0.1 (Polynomial-time algorithm for vanishing polynomial):
non-included
This is an algorithmic/computational statement about finding minimum-degree polynomials vanishing on finite sets. Mathlib does not contain computational complexity results or algorithm descriptions of this type.

Corollary 0.2 (Dimension counting for vanishing polynomial):
included
This is the basic linear algebra observation that if dim V(d) > |S|, there exists a nonzero polynomial of degree <= d vanishing on S. This follows directly from the rank-nullity theorem in mathlib (Mathlib/LinearAlgebra/Dimension/Finrank.lean and related files), applied to the evaluation map. The dimension of the polynomial space is available via Mathlib/RingTheory/Polynomial/Basic.lean.

Corollary 0.3 (Degree bound for vanishing polynomial on s points):
included
This follows from Corollary 0.2 combined with the dimension formula for polynomial spaces. The dimension of the space of polynomials of degree <= d in n variables is binomial(d+n, n), which is available in mathlib. The corollary is a direct consequence of these standard facts.

Lemma 1.1 (Polynomial vanishing lemma, one variable):
included
This is the fundamental result that a polynomial of degree <= d vanishing at more than d points is zero. This is essentially `Polynomial.card_roots` in Mathlib/Algebra/Polynomial/Roots.lean, which states that the number of roots of a nonzero polynomial is at most its degree.

Corollary 1.2 (Uniqueness of polynomial from majority agreement):
included
This follows directly from Lemma 1.1 (the vanishing lemma) applied to the difference of two polynomials. Since card_roots is in mathlib, this corollary follows immediately.

Theorem 1.3 (Berlekamp-Welch, 1986):
non-included
This is an algorithmic result from coding theory. Mathlib does not contain algorithmic results of this nature. Searched in Mathlib/InformationTheory/ and Mathlib/RingTheory/Polynomial/ without finding an equivalent.

Theorem 2.1 (Nikodym sets of measure zero):
non-included
This is a construction result from geometric measure theory (1920s). Searched in Mathlib/MeasureTheory/ and Mathlib/Analysis/ but found no equivalent. Mathlib does not contain Kakeya-type or Nikodym-type set constructions.

Theorem 3.1 (Guth-Katz, 2010):
non-included
This is the celebrated distinct distance theorem. Searched in Mathlib/Combinatorics/ and Mathlib/Geometry/ but found no equivalent. This is a deep result in combinatorial geometry not present in mathlib.

Theorem 4.1 (Thue, 1908):
non-included
Thue's theorem on finiteness of integer solutions to homogeneous polynomial equations. Searched in Mathlib/NumberTheory/ but found no equivalent. Mathlib does not contain Thue's theorem or its generalizations (Siegel, Roth).

## Chapter: The Berlekamp-Welch Algorithm

Theorem 0.1 (Berlekamp-Welch, detailed version):
non-included
Same as Theorem 1.3 above; algorithmic result not in mathlib.

Lemma 0.2 (Vanishing Lemma):
included
Same as Lemma 1.1 above. Corresponds to `Polynomial.card_roots` and related results in Mathlib/Algebra/Polynomial/Roots.lean.

Claim 1.1 (R vanishes on graph of P):
non-included
This is a specific claim in the context of the Berlekamp-Welch algorithm proof. Not a general mathematical statement present in mathlib.

Claim 1.2 (R vanishes on vertical lines at errors):
non-included
Specific to the Berlekamp-Welch algorithm proof. Not in mathlib.

Claim 1.3 (Exact form of R):
non-included
Specific to the Berlekamp-Welch algorithm proof. Not in mathlib.

Lemma 2.1 (Divisibility Lemma, one variable):
included
This states that if P(x_1) = 0 then (x - x_1) divides P. This is exactly `Polynomial.dvd_iff_isRoot` in Mathlib/Algebra/Polynomial/Div.lean, which states X - C a divides p iff a is a root of p.

Lemma 2.2 (Divisibility Lemma, two variables):
non-included
This is a two-variable generalization: if R(x, P(x)) = 0 as a polynomial then (y - P(x)) divides R(x,y). Searched in Mathlib/RingTheory/Polynomial/ and Mathlib/Algebra/Polynomial/ but found no equivalent for multivariate polynomial divisibility of this specific form.

Theorem 2.3 (Bezout's Theorem, planar):
non-included
Bezout's theorem that Z(P,Q) has at most deg(P)*deg(Q) points or P,Q share a common factor. Searched in Mathlib/AlgebraicGeometry/ and Mathlib/RingTheory/Polynomial/ but found no equivalent. Mathlib has Bezout domains (Mathlib/RingTheory/Bezout.lean) but not the geometric Bezout theorem for intersection of plane curves.

Theorem 3.1 (Sudan, 1997):
non-included
List decoding algorithm from coding theory. Not in mathlib.

## Chapter: The Finite-Field Nikodym and Kakeya Problems

Theorem 0.1 (Dvir, finite field Nikodym):
non-included
Dvir's theorem that Nikodym sets in F^n have >= c_n q^n elements. Searched in Mathlib/Combinatorics/ and Mathlib/FieldTheory/ but found no equivalent. The Chevalley-Warning theorem is in Mathlib/FieldTheory/ChevalleyWarning.lean and the combinatorial Nullstellensatz is in Mathlib/Combinatorics/Nullstellensatz.lean, but Dvir's theorem itself is not present.

Theorem 0.2 (Finite field Kakeya):
non-included
Same type of result as Dvir's Nikodym theorem. Not in mathlib. Searched in Mathlib/Combinatorics/ and Mathlib/FieldTheory/.

## Chapter: The Joints Problem

Theorem 0.1 (Joints Theorem):
non-included
The joints theorem that L lines determine <= 10L^{3/2} joints. This is a combinatorial geometry result not present in mathlib. Searched in Mathlib/Combinatorics/ and Mathlib/Geometry/.

Main Lemma (Joints):
non-included
Part of the joints theorem proof. Not in mathlib.

Lemma 0.2 (Gradient vanishes at joints):
non-included
A lemma about the gradient of a function vanishing on lines at a joint point. While the underlying multivariable calculus is in mathlib, this specific geometric lemma is not.

## Chapter: Why Polynomials? Part 1

Lemma 2.1 (Axis-parallel joints):
non-included
The axis-parallel version of the joints main lemma (Loomis-Whitney flavored). Not in mathlib as a discrete combinatorial statement. Searched in Mathlib/Combinatorics/.

## Chapter: Incidence Geometry

Proposition 1.2 (Grid example for P_k):
non-included
A construction showing that grids achieve |P_k| >= cL^2 k^{-3}. Not in mathlib.

Theorem 1.3 (Szemeredi-Trotter):
non-included
The Szemeredi-Trotter theorem on incidences of points and lines. Searched in Mathlib/Combinatorics/ but found no equivalent. This is a fundamental result in combinatorial geometry not yet formalized in mathlib.

Proposition 1.4 (P_k upper bound via pairs):
non-included
A basic double-counting argument for point-line incidences. Not in mathlib.

Proposition 1.5 (P_k bound when k^2 > 4L):
non-included
Incidence geometry bound. Not in mathlib.

Proposition 1.6 (P_k bound when L < k^2/4):
non-included
Incidence geometry bound. Not in mathlib.

## Chapter: Crossing Numbers and the Szemeredi-Trotter Theorem

Proposition 1.1 (Planar graph E <= 3V):
non-included
This bound for planar graphs follows from the Euler formula. While mathlib has some graph theory (Mathlib/Combinatorics/SimpleGraph/), the Euler formula for planar graphs and the E <= 3V bound are not present.

Proposition 1.2 (Crossing number >= E - 3V):
non-included
A crossing number lower bound. Mathlib does not contain graph crossing number theory. Searched in Mathlib/Combinatorics/SimpleGraph/.

Theorem 1.3 (Crossing Number Inequality):
non-included
The crossing number inequality k(G) >= (1/64)E^3/V^2 when E >= 4V. Not in mathlib. Searched in Mathlib/Combinatorics/.

Theorem 2.1 (Szemeredi-Trotter via crossing numbers):
non-included
The Szemeredi-Trotter theorem proved via crossing numbers. Not in mathlib.

## Chapter: The Distinct Distance Problem and the Unit Distance Problem

Theorem 2 (Distinct distances, no 100 on a line):
non-included
A distinct distance result under non-collinearity assumptions. Not in mathlib.

Theorem 3 (Unit distance upper bound N^{4/3}):
non-included
The Spencer-Szemeredi-Trotter upper bound on unit distances. Not in mathlib.

Proposition 1 (Crossing numbers for multigraphs, basic):
non-included
Crossing number bound for multigraphs. Not in mathlib.

Lemma 1 (Crossing numbers for multigraphs, refined):
non-included
Refined crossing number bound for multigraphs. Not in mathlib.

Proposition 2 (Crossing numbers for multigraphs, general):
non-included
General crossing number bound for multigraphs. Not in mathlib.

## Chapter: Crossing Numbers and Distinct Distances

Theorem 1.1 (Szekely, N^{4/5} distinct distances):
non-included
Szekely's proof that N points determine >= cN^{4/5} distinct distances. Not in mathlib.

Lemma 1.2 (High-multiplicity edge count):
non-included
Technical lemma in the distinct distance proof. Not in mathlib.

Theorem 1.3 (Crossing number for multigraphs, restated):
non-included
Same as the crossing number theorem for multigraphs above. Not in mathlib.

## Chapter: Reguli and Applications, Zarankiewicz Problem

Proposition 1.1 (Three lines in degree 2 surface):
non-included
That any three lines in R^3 lie in a degree 2 algebraic surface. Not in mathlib. Searched in Mathlib/AlgebraicGeometry/ and Mathlib/Geometry/.

Proposition 1.2 (Regulus from three skew lines):
non-included
Construction of a regulus from three skew lines. Not in mathlib.

Lemma 1.3 (Lines meeting two intersecting lines):
non-included
Elementary geometry of lines in 3D. While basic, this specific statement is not in mathlib.

Lemma 1.4 (Lines meeting two parallel lines):
non-included
Elementary geometry of lines in 3D. Not formalized in mathlib.

Theorem 1.5 (Intersection points <= L^{5/3}):
non-included
Incidence geometry bound using reguli. Not in mathlib.

Lemma 1.6 (No large all-ones minor in A_t):
non-included
Combinatorial lemma about incidence matrices. Not in mathlib.

Theorem 1.7 (Kovari-Sos-Turan, 1954):
non-included
The Kovari-Sos-Turan theorem on 0-1 matrices with forbidden submatrices. Searched in Mathlib/Combinatorics/ but found no equivalent. This is a classical result in extremal graph theory not yet in mathlib.

Theorem 2.1 (Kovari-Sos-Turan, general):
non-included
The general (M x N) form of the Kovari-Sos-Turan theorem. Not in mathlib.

## Chapter: Elekes-Sharir Approach

Lemma 1 (|d(P)||Q(P)| >= N^4):
non-included
Cauchy-Schwarz based counting lemma for distinct distances. Not in mathlib.

Lemma 2 (Rigid motion characterization):
non-included
Characterization of distance-preserving quadruples via rigid motions. Not in mathlib.

## Chapter: Algebraic Structure and Degree Reduction

Proposition 0.1 (Degree bound for lines in F^3):
non-included
That L lines in F^3 lie in a polynomial of degree <= 3L^{1/2}. Not in mathlib.

Proposition 1.1 (Degree Reduction):
non-included
Degree reduction for lines with many intersections. Not in mathlib.

## Chapter: Bezout's Theorem in 3D

Theorem 4.1 (Bezout for lines in 3D):
non-included
If P, Q have no common factor, Z(P) intersect Z(Q) contains <= deg(P)*deg(Q) lines. Not in mathlib. Searched in Mathlib/AlgebraicGeometry/ and Mathlib/RingTheory/.

Lemma 4.2 (Rank of evaluation map on lines):
non-included
Technical lemma about the rank of the evaluation map restricted to a union of lines. Not in mathlib.

## Chapter: Special Points and Lines of Algebraic Surfaces

Theorem 2.1 (Implicit Function Theorem):
included
The implicit function theorem is in mathlib at Mathlib/Analysis/Calculus/Implicit.lean. The `ImplicitFunctionData.implicitFunction` and related results provide the implicit function theorem for smooth maps.

Lemma 2.3 (Square free => no common factor with partials):
included
The statement that a square-free polynomial and its partial derivatives have no common nonconstant factor is closely related to the separability theory in Mathlib/FieldTheory/Separable.lean. In particular, `Separable.squarefree` and the characterization of separable polynomials via coprimality with the derivative capture this idea. More precisely, the separable condition (coprime with derivative) is stronger, but the underlying algebraic machinery is present.

Proposition 2.4 (Critical points bound for square-free polynomials):
non-included
The bound that a square-free polynomial of degree d in 2 variables has at most 2d^2 critical points. This uses Bezout's theorem which is not in mathlib, and this specific geometric statement is not present.

Theorem 2.5 (Bezout for lines in 3D):
non-included
Same as Theorem 4.1 above. Not in mathlib.

## Chapter: Flecnodal Points and Ruled Surfaces

Theorem 0.1 (Ruled surfaces from flecnodal vanishing):
non-included
A theorem about algebraic surfaces being ruled when the flecnodal polynomial vanishes. This is specialized algebraic geometry not in mathlib. Searched in Mathlib/AlgebraicGeometry/.

Proposition 0.2 (Integral curves are lines under nondegeneracy):
non-included
A differential geometry result about integral curves of vector fields satisfying flecnodal equations being straight lines. Not in mathlib.

## Chapter: The Regulus Detection Lemma

Regulus Detection Lemma:
non-included
This is a specialized result about detecting reguli via polynomial conditions. Not in mathlib.

Lemma 0.1 (Algebraic set of dim I_{=3} <= 8):
non-included
Technical algebraic geometry lemma. Not in mathlib.

Lemma 0.2 (RP characterization under signature (1,1)):
non-included
Technical lemma about the regulus detection polynomial. Not in mathlib.

Lemma 0.3 (Two lines imply RP = 0):
non-included
Part of the regulus detection lemma proof. Not in mathlib.

Lemma 0.4 (RP = 0 implies regulus):
non-included
Part of the regulus detection lemma proof. Not in mathlib.

Proposition 0.5 (Integral curves are lines, restated):
non-included
Same as Proposition 0.2 above. Not in mathlib.

Lemma 0.6 (RP = 0 at critical points):
non-included
Technical lemma. Not in mathlib.

Lemma 0.7 (Flat point characterization):
non-included
Characterization of flat points of algebraic surfaces. Not in mathlib.

Lemma 0.8 (RP = 0 at flat points):
non-included
Technical lemma. Not in mathlib.

## Chapter: Incidence Estimates (Lines in R^3)

Theorem 1.1 (Incidence bound with regulus restriction):
non-included
Incidence bound for lines in R^3 with regulus restrictions. Not in mathlib.

Theorem 1.2 (k-rich point bound for lines in R^3):
non-included
Bound on k-rich points for lines in R^3. Not in mathlib.

## Chapter: Introduction to Diophantine Equations

Theorem 1.1 (Thue, diophantine equations):
non-included
Thue's theorem on finiteness of solutions. Not in mathlib. Searched in Mathlib/NumberTheory/.

Proposition 2.1 (Almost every beta has finitely many good approximations):
non-included
A measure-theoretic statement about Diophantine approximation. While mathlib has measure theory, this specific statement about Diophantine approximation is not present. Searched in Mathlib/NumberTheory/.

Proposition 2.2 (Liouville's approximation theorem):
included
Liouville's inequality |beta - x/y| >= c(beta)|y|^{-deg(beta)} for irrational algebraic numbers. This is essentially contained in Mathlib/NumberTheory/Transcendental/Liouville/Basic.lean as `exists_pos_real_of_irrational_root`, which provides a bound of the form (b+1)^{deg f} * |alpha - a/(b+1)| * A >= 1 for some positive A, which is equivalent to Liouville's approximation bound.

Theorem 2.3 (Thue's approximation theorem):
non-included
Thue's improvement of Liouville's bound to exponent (deg+2)/2. Not in mathlib. Searched in Mathlib/NumberTheory/.

## Chapter: Proof of Thue's Theorem - Part I

Proposition 1.1 (Gauss's Lemma for polynomial divisibility):
included
The statement that if P in Z[x] vanishes to order l at a rational r = p/q, then (qx-p)^l divides P in Z[x]. This is a consequence of Gauss's lemma, which is in Mathlib/RingTheory/Polynomial/GaussLemma.lean. The key content -- that Z[x] is integrally closed and the primitive/content machinery -- is available.

Corollary 1.2 (Coefficient lower bound |P| >= ||r||^l):
non-included
A quantitative bound on coefficients of integer polynomials vanishing at rational points. This specific quantitative statement is not in mathlib, though the underlying Gauss lemma is.

Proposition 2.1 (Integer solutions to underdetermined linear systems):
non-included
Existence of nonzero integer solutions to underdetermined integer linear systems. This is a pigeonhole/lattice argument. While mathlib has lattice theory, this specific statement (sometimes called Siegel's lemma in a weak form) is not present. Searched in Mathlib/LinearAlgebra/ and Mathlib/NumberTheory/.

Proposition 2.2 (Siegel's Lemma):
non-included
The quantitative version with bound |x|_inf <= |L|_{op}^{N/(M-N)}. This is not in mathlib. Searched in Mathlib/NumberTheory/ and Mathlib/LinearAlgebra/.

## Chapter: Proof of Thue's Theorem - Part II

Proposition 1.1 (Polynomial construction via parameter counting):
non-included
Construction of polynomials vanishing to high order at rational points with controlled coefficients. Not in mathlib.

Proposition 1.2 (Schneider):
non-included
Schneider's lower bound on polynomial coefficients given vanishing conditions. Not in mathlib.

Proposition 2.1 (Polynomial vanishing at algebraic point):
non-included
Construction of integer polynomials vanishing to high order at algebraic points. Not in mathlib.

Lemma 2.2 (Powers of algebraic number expansion):
non-included
Expansion of powers of an algebraic number in terms of lower powers. While mathlib has algebraic number theory, this specific quantitative coefficient bound is not present.

## Chapter: Proof of Thue's Theorem - Part III

Theorem 1.1 (Thue restated):
non-included
Restatement of Thue's theorem. Not in mathlib.

Theorem 4.1 (Taylor's Theorem):
included
Taylor's theorem with remainder is in Mathlib/Analysis/Calculus/Taylor.lean. The results `taylor_mean_remainder`, `taylor_mean_remainder_lagrange`, and `taylor_mean_remainder_cauchy` provide Taylor's theorem in various forms.

Corollary 4.2 (Taylor bound for vanishing polynomial):
non-included
A specific corollary bounding |Q(x+h)| when Q vanishes to order m at x. While Taylor's theorem is in mathlib, this specific polynomial corollary combining vanishing order with coefficient bounds is not explicitly stated.

## Chapter: How Combinatorics and Analysis Interact

Theorem 1.1 (Loomis-Whitney):
non-included
The Loomis-Whitney inequality that |X| <= A^{n/(n-1)} when each projection has measure <= A. This specific inequality in its combinatorial/measure-theoretic form is not in mathlib. The Gagliardo-Nirenberg-Sobolev inequality in Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean is related but is stated differently (for functions rather than sets).

Lemma 1.2 (Main Lemma for Loomis-Whitney):
non-included
The combinatorial lemma underlying the Loomis-Whitney proof. Not in mathlib.

Corollary 1.3 (Loomis-Whitney corollary):
non-included
Corollary of the main lemma. Not in mathlib.

Theorem 1.4 (Continuous Loomis-Whitney):
non-included
The continuous version of Loomis-Whitney. Not explicitly in mathlib, though the Sobolev inequality file contains related grid-lines lemma machinery.

Corollary 1.5 (Isoperimetric inequality):
non-included
The isoperimetric inequality Vol_n(U) <= Vol_{n-1}(dU)^{n/(n-1)}. While mathlib has some isoperimetric results, this specific formulation is not present. Searched in Mathlib/MeasureTheory/ and Mathlib/Analysis/.

Theorem 2.1 (Sobolev inequality):
included
The Gagliardo-Nirenberg-Sobolev inequality ||u||_{n/(n-1)} <= C ||nabla u||_1 is in Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean. Multiple versions are provided there.

Proposition 2.2 (Markov/Chebyshev for L^p):
included
The Markov/Chebyshev inequality |S(h)| <= M^p h^{-p} when ||u||_p <= M. This is a standard consequence of Markov's inequality, which is available in mathlib via measure theory results in Mathlib/MeasureTheory/Integral/ and related files.

Lemma 2.3 (Projection bound for superlevel set):
non-included
A geometric lemma bounding the projection of superlevel sets. Not in mathlib.

Lemma 2.4 (Revised projection bound):
non-included
Refined version of the projection bound. Not in mathlib.

Corollary 2.5 (Annular superlevel set bound):
non-included
Bound on annular superlevel sets via Loomis-Whitney. Not in mathlib.

## Chapter: Hardy-Littlewood-Sobolev Inequality

Proposition 0.1 (HLS necessary condition):
non-included
Necessary conditions for the HLS inequality from ball examples. Not in mathlib.

Theorem 0.2 (Hardy-Littlewood-Sobolev):
non-included
The HLS inequality ||T_alpha f||_q <= C ||f||_p. Not in mathlib. Searched in Mathlib/Analysis/ but found no equivalent. Mathlib has convolution (Mathlib/Analysis/Convolution.lean) but not the specific HLS inequality.

Lemma 1.1 (Vitali Covering Lemma):
included
The Vitali covering lemma is in Mathlib/MeasureTheory/Covering/Vitali.lean as `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall` and related results.

Lemma 1.2 (Ball doubling):
non-included
The ball doubling lemma |union 2B_i| <= 6^n |union B_i|. While Vitali covering is in mathlib, this specific ball doubling corollary is not explicitly stated.

Lemma 2.1 (HL maximal inequality, weak type):
non-included
The weak-type (1,1) bound for the Hardy-Littlewood maximal function. Not explicitly in mathlib. While mathlib has some covering theorems, the Hardy-Littlewood maximal function and its weak-type bound are not formalized.

Proposition 2.2 (HL maximal inequality, strong type):
non-included
The strong-type (p,p) bound ||Mf||_p <= C ||f||_p. Not in mathlib.

Lemma 2.3 (Refined weak-type maximal inequality):
non-included
A refinement of the weak-type inequality. Not in mathlib.

Lemma 3.1 (T_alpha via averages):
non-included
Representation of T_alpha f in terms of ball averages. Not in mathlib.

## Chapter: Oscillating Integrals and the Kakeya Problem

Proposition 1.1 (Fourier inversion):
included
The Fourier inversion formula f(x) = integral hat{f}(omega) e^{2pi i omega x} domega. Mathlib has Fourier transform theory in Mathlib/Analysis/Fourier/FourierTransform.lean and inversion results. The Fourier inversion theorem for Schwartz functions is present.

Proposition 2.1 (Necessary condition for oscillating kernel bounds):
non-included
Necessary conditions on p for ||tilde{T}_alpha f||_p <= C ||f||_p. Not in mathlib.

Proposition 3.1 (Tube focusing estimate):
non-included
Estimate for the oscillating kernel operator on tube-supported functions. Not in mathlib.

Corollary 3.2 (No L^p bounds for alpha < (n+1)/2):
non-included
Impossibility result for oscillating kernel bounds. Not in mathlib.

Theorem 4.1 (Besicovitch):
non-included
Besicovitch's construction of tubes with small union of translates. Not in mathlib. While Mathlib/MeasureTheory/Covering/Besicovitch.lean exists, it contains the Besicovitch covering theorem, not the tube arrangement construction.

Proposition 4.2 (Random signs and square function):
non-included
Khintchine-type inequality for random signs. Not in the precise form needed, though mathlib has some probability theory.

Corollary 4.3 (L^p norm of random tube sum):
non-included
Consequence of the random sign proposition. Not in mathlib.

Corollary 4.4 (T_alpha of random tube sum):
non-included
Consequence for the oscillating kernel operator. Not in mathlib.

Theorem 4.5 (Fefferman 1971):
non-included
Fefferman's theorem that the ball multiplier is unbounded on L^p for p != 2. This is a deep result in harmonic analysis not in mathlib. Searched in Mathlib/Analysis/Fourier/.

## Chapter: The Multilinear Kakeya Inequality

Theorem 2.1 (Bennett-Carbery-Tao-Guth, generalized Loomis-Whitney):
non-included
The generalized Loomis-Whitney inequality for nearly-orthogonal tubes. Not in mathlib. This is a relatively recent result using the polynomial method.

Lemma 2.2 (Directed volume via projection):
non-included
Formula for directed volume in terms of projection fibers. Not in mathlib.

Lemma 2.3 (Cylinder estimate):
non-included
Bound on directed volume of an algebraic variety in a cylinder. Not in mathlib.

Lemma 2.4 (Volume vs directed volumes):
non-included
Inequality relating total volume to sum of directed volumes. Not in mathlib.

Theorem 3.1 (Bennett-Carbery-Tao, Multilinear Kakeya):
non-included
The multilinear Kakeya inequality. Not in mathlib. This is a deep result in harmonic analysis/geometric combinatorics.

Lemma 3.2 (Multilinear Kakeya, per-mu bound):
non-included
Technical lemma in the multilinear Kakeya proof. Not in mathlib.

Lemma 3.3 (Multilinear Kakeya, unequal A_j):
non-included
Generalization to unequal tube counts. Not in mathlib.

## Chapter: Polynomial Cell Decompositions

Theorem 1.1 (Polynomial Cell Decomposition):
non-included
The polynomial cell decomposition theorem that a degree d polynomial can partition R^n so each cell has at most C(n)|S|d^{-n} points. This is a key result in the polynomial method not formalized in mathlib. Searched in Mathlib/Combinatorics/ and Mathlib/RingTheory/Polynomial/.

Theorem 2.1 (Ham Sandwich Theorem):
non-included
The ham sandwich theorem that n finite volume open sets in R^n can be bisected by a hyperplane. Not in mathlib. The Borsuk-Ulam theorem, on which it is based, is also not in mathlib (searched for BorsukUlam, found nothing).

Theorem 2.2 (General Ham Sandwich Theorem, Stone-Tukey 1942):
non-included
The generalization using arbitrary vector spaces of functions. Not in mathlib.

Lemma 2.4 (Polynomial Existence Lemma):
included
This is the same as Corollary 0.2 -- if N < dim V(d) then there is a nonzero polynomial of degree <= d vanishing at N given points. This follows from rank-nullity in Mathlib/LinearAlgebra/Dimension/Finrank.lean.

Corollary 4.1 (Polynomial Ham Sandwich for Finite Sets):
non-included
The finite-set version of the polynomial ham sandwich theorem. Not in mathlib.

Theorem 3.1 (Borsuk-Ulam):
non-included
The Borsuk-Ulam theorem. While mathlib has the sphere (Mathlib/Geometry/Manifold/Instances/Sphere.lean), the Borsuk-Ulam theorem itself is not formalized. Searched for BorsukUlam and antipodal but found no equivalent.

Continuity Lemma (Volume of superlevel depends continuously on f):
non-included
A measure-theoretic lemma about continuity of volumes of superlevel sets. Not explicitly in mathlib as a standalone result.

## Chapter: Using Polynomial Cell Decompositions

Theorem 1.1 (Szemeredi-Trotter via cell decomposition):
non-included
The Szemeredi-Trotter theorem proved via polynomial cell decomposition. Not in mathlib.

Lemma 1.2 (Counting Lemma):
non-included
Basic double-counting bounds I(S,L) <= L + S^2 and I(S,L) <= L^2 + S. Not in mathlib.

Theorem 2.1 (3D Szemeredi-Trotter):
non-included
The 3-dimensional incidence bound for points and lines. Not in mathlib.

Corollary 2.2 (k-rich points with plane restriction):
non-included
Bound on k-rich points in R^3 under a plane restriction. Not in mathlib.

## Chapter: What's Special About Polynomials? (Geometric Perspective)

Theorem 0.1 (Efficiency of complex polynomials in zeroes):
non-included
That a complex polynomial has no unnecessary zeroes compared to arbitrary smooth competitors. This is a topological/complex analysis result related to the argument principle, but this specific formulation (comparing polynomial and smooth function zeroes) is not in mathlib. Searched in Mathlib/Analysis/Complex/.

Theorem 0.2 (Efficiency of complex polynomials in surface area):
non-included
That Z(P) has minimal surface area among smooth competitors. Related to calibrated geometry and DeRham/Federer theory. Not in mathlib.

Lemma 0.3 (Line intersection bound for complex polynomials):
non-included
One-dimensional case of the surface area efficiency applied to line intersections. Not in mathlib.

Theorem 0.4 (Kronheimer-Mrowka):
non-included
That Z(P) has minimal genus among smooth competitors. This uses gauge theory and is far beyond current mathlib capabilities. Not in mathlib.

Theorem 0.5 (Efficiency of real polynomial space in zeroes):
non-included
That any (d+1)-dimensional function space has some function with at least d zeroes. A dimension-counting argument, but this specific formulation about function spaces is not in mathlib.

Theorem 0.6 (Gromov, Efficiency of real polynomial space):
non-included
Gromov's result on volumes of zero sets of function spaces. This is a deep geometric result from 2003. Not in mathlib.

Theorem 0.7 (Crofton):
non-included
The Crofton formula relating volume to line intersections via integral geometry. Not in mathlib. Searched for Crofton and integral_geometry but found nothing.

Theorem 0.8 (Stone-Tukey, restated):
non-included
Same as Theorem 2.2 above. Not in mathlib.

## Chapter: Detecting Reguli and Projection Theory

Theorem 0.1 (Incidence bound with regulus restriction, restated):
non-included
Same as Theorem 1.1 in Incidence Estimates chapter. Not in mathlib.

Theorem 0.2 (3-rich points with plane restriction):
non-included
Bound on 3-rich points for lines in R^3 under plane restrictions. Not in mathlib.

Plane Detection Lemma:
non-included
Analog of the regulus detection lemma for planes. Not in mathlib.

Theorem 1.1 (Lines in non-ruled surfaces):
non-included
That an irreducible non-ruled surface contains at most C(deg P)^2 lines. Based on Salmon-Cayley 19th century work. Not in mathlib.

Ruled Surface Detection Lemma:
non-included
The flecnode polynomial FP detects whether Z(P) is ruled. Based on 19th century work of Salmon and Cayley. Not in mathlib.

Lemma 1.2 (Algebraic set from projection):
non-included
That the set of parameters where flecnodal equations have nonzero solutions is algebraic. A special case of the fundamental theorem of projection theory. Not in mathlib.

Fundamental Theorem of Projection Theory:
non-included
That the projection of an algebraic set defined by polynomials homogeneous in y is algebraic over algebraically closed fields. While mathlib has the Nullstellensatz (Mathlib/RingTheory/Nullstellensatz.lean), this specific projection theorem (elimination theory) is not present.

Proposition 3.1 (Rank of ideal graded piece is algebraic):
non-included
That {x | dim I(x)_{=d} <= B} is algebraic. Not in mathlib.

Proposition 3.2 (Infinite dimensional quotient is algebraic condition):
non-included
That {x | F[y]/I(x) is infinite dimensional} is algebraic. Not in mathlib.

Proposition 3.3 (Nonzero point iff infinite dimensional quotient):
included
Over an algebraically closed field, a homogeneous ideal I has Z(I) containing a nonzero point iff F[y]/I is infinite dimensional. This is essentially a consequence of the Hilbert Nullstellensatz which is in Mathlib/RingTheory/Nullstellensatz.lean, combined with basic properties of graded rings.

Theorem 0.3 (Winding number formula):
non-included
The winding number equals the signed count of zeroes. While mathlib has some complex analysis, this specific topological formula for winding numbers is not present in the form stated. Searched for winding_number and WindingNumber but found nothing.
