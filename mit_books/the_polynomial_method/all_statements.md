# All Mathematical Statements in "The Polynomial Method"

## Chapter: Introduction

**Corollary 0.1.** There is a polynomial-time algorithm to find a minimal degree polynomial that vanishes on a given finite set.

**Corollary 0.2.** If dimV(d) > s, then there is a non-zero polynomial P of degree <= d that vanishes on the given finite set.

**Corollary 0.3.** For any set of s points in F^n, there is a non-zero polynomial that vanishes on the set with degree <= ns^{1/n}.

**Lemma 1.1.** If P : F -> F has degree <= d and vanishes at more than d points, then P is the zero polynomial.

**Corollary 1.2.** If q > 10^4, for any function F : F -> F, there is at most one polynomial P of degree <= q^{1/2} so that F(x) = P(x) for at least (51/100)q values of x.

**Theorem 1.3 (Berlekamp-Welch, 1986).** There is a polynomial time algorithm to recover P from F.

**Theorem 2.1 (Nikodym).** There are Nikodym sets of measure zero in each dimension n >= 2.

**Theorem 3.1 (Guth-Katz, 2010).** For any set of N points in the plane, the number of distinct distances is at least cN(log N)^{-1}.

**Theorem 4.1 (Thue, 1908).** If P(x, y) is an irreducible homogeneous polynomial of degree >= 3, and A is an integer, then the equation P(x, y) = A has only finitely many integer solutions.

## Chapter: The Berlekamp-Welch Algorithm

**Theorem 0.1 (Berlekamp-Welch, 1986).** Suppose that F has q elements, the degree of P is < q/100, and F(x) = P(x) for at least (51/100)q values of x. Under these assumptions, there is an efficient algorithm to recover P from F.

**Lemma 0.2 (Vanishing Lemma).** If P(x) is a polynomial of degree <= D, and P vanishes at D+1 distinct points, then P is the zero polynomial.

**Claim 1.1.** The polynomial R vanishes on the graph of P. In fact, R(x, P(x)) is the zero polynomial.

**Claim 1.2.** For each e in E, R(x,y) vanishes on the line x = e.

**Claim 1.3.** R(x,y) = c[y - P(x)] prod_{e in E} (x - e), for some non-zero constant c in F.

**Lemma 2.1 (Divisibility Lemma, one variable).** If P(x) is any polynomial and P(x_1) = 0 for some x_1 in F, then P(x) = (x - x_1)P_1(x) for some polynomial P_1.

**Lemma 2.2 (Divisibility Lemma, two variables).** If R(x, y) is a polynomial of two variables, and P(x) is a polynomial in one variable, and R(x, P(x)) is the zero polynomial, then R(x, y) = (y-P(x))R_1(x, y) for some polynomial R_1.

**Theorem 2.3 (Bezout's Theorem).** Suppose that P(x, y) and Q(x, y) are polynomials. Then either (1) Z(P,Q) has at most (degP)(degQ) points, or (2) P and Q have a non-trivial common factor.

**Theorem 3.1 (Sudan, 1997).** Suppose that F is a field with q elements, and that F: F -> F is any function. There is an efficient algorithm that lists all the polynomials of degree < (1/200)q^{1/2} that agree with F at least 1% of the time.

## Chapter: The Finite-Field Nikodym and Kakeya Problems

**Theorem 0.1 (Dvir).** Any (generalized) Nikodym set in F^n contains at least c_n q^n elements.

**Theorem 0.2.** A Kakeya set K in F^n has at least c_n q^n elements.

## Chapter: The Joints Problem

**Theorem 0.1 (Joints Theorem).** Any L lines in space determine <= 10L^{3/2} joints.

**Main Lemma.** If a set of lines has J joints, then one of the lines contains <= 3J^{1/3} joints.

**Lemma 0.2.** If x is a joint lying in three (non-coplanar) lines, and if a smooth function F: R^3 -> R vanishes on the lines, then nabla F vanishes at x.

## Chapter: Why Polynomials? Part 1

**Lemma 2.1 (Axis-parallel joints).** Suppose that L is a set of L lines in R^3, each parallel to one of the coordinate axes. If L determines J joints, then one of the lines contains <= J^{1/3} joints.

## Chapter: Incidence Geometry

**Proposition 1.2.** For all k in [sqrt(|L|)], there's a configuration such that |P_k| >= cL^2 K^{-3}.

**Theorem 1.3 (Szemeredi-Trotter).** For some constant c, |P_k| <= c(|L|/k + |L|^2/k^3).

**Proposition 1.4.** |P_k| <= 2L^2 k^{-2}.

**Proposition 1.5.** If k^2/4 > |L|, then |P_K| < k/2.

**Proposition 1.6.** If |L| < k^2/4, then |P_k| < 2|L|/k.

## Chapter: Crossing Numbers and the Szemeredi-Trotter Theorem

**Proposition 1.1.** If G is a planar graph with E edges and V vertices, then E - 3V <= 0.

**Proposition 1.2 (Crossing number lower bound).** The crossing number of G is at least E - 3V.

**Theorem 1.3 (Crossing Number Inequality).** If G is a graph with E edges and V vertices, and E >= 4V, then the crossing number of G is at least (1/64)E^3 V^{-2}.

**Theorem 2.1 (Szemeredi-Trotter, via crossing numbers).** Let L be a set of L lines in the plane. Let P_k be the set of points that lie on at least k lines of L. Then the number of points in P_k is at most max(2Lk^{-1}, 2^9 L^2 k^{-3}).

## Chapter: The Distinct Distance Problem and the Unit Distance Problem

**Theorem 2 (Distinct distances, no 100 on a line).** If we have N points in the plane, no 100 of which are on a common line, then the number of distinct distances is at least cN.

**Theorem 3 (Unit distance upper bound).** A set S of N points in the plane determine at most O(N^{4/3}) unit distances.

**Proposition 1 (Crossing numbers for multigraphs).** If Mult(G) <= M, and E >= 4MV, then K(G) >= (1/64)E^3 V^{-2} M^{-3}.

**Lemma 1 (Crossing numbers for multigraphs, refined).** Let G be a multigraph with multiplicity at most M. Assume E >= 4MV, and each edge has multiplicity greater than M/2. Then K(G) >= (1/256)E^3 V^{-2} M^{-1}.

**Proposition 2 (Crossing numbers for multigraphs, general).** If G is a multigraph with multiplicity at most M, and E >= 100MV, then K(G) >= cE^3 V^{-2} M^{-1} for some c.

## Chapter: Crossing Numbers and Distinct Distances

**Theorem 1.1 (Szekely).** If we have N distinct points in the plane, then they determine >= cN^{4/5} distinct distances.

**Lemma 1.2.** The number of edges of G with multiplicity >= M is at most C[N^2 M^{-2}t + N log Nt].

**Theorem 1.3 (Crossing number estimate for multigraphs).** If G is a multigraph with V vertices and E edges and with multiplicity <= M, and if E >= 100MV, then the crossing number of G is at least cE^3 V^{-2} M^{-1}.

## Chapter: Reguli and Applications, Zarankiewicz Problem

**Proposition 1.1.** For any three lines l_1, l_2, l_3 in R^3, there is a non-zero degree 2 polynomial Q that vanishes on all three lines.

**Proposition 1.2.** If l_1, l_2, and l_3 are pairwise skew, then there is an irreducible degree 2 algebraic surface R(l_1, l_2, l_3) which contains every line that intersects l_1, l_2, and l_3.

**Lemma 1.3.** Suppose that l_1 and l_2 are lines in R^3 that intersect at a point p. Suppose that P is the plane that contains l_1 and l_2. Then any line which intersects both l_1 and l_2 either contains p or lies in P.

**Lemma 1.4.** Suppose that l_1 and l_2 are parallel. Let P be the plane that contains them. Then any line which intersects both l_1 and l_2 lies in P.

**Theorem 1.5.** Suppose that L is a set of L lines in R^3 with <= 10 lines in any plane or degree 2 surface. Then the number of intersection points of L is <= L^{5/3} (up to constants).

**Lemma 1.6.** Suppose that L has <= 10 lines in any plane or degree 2 surface. Then A_t has no 3 x 20*2^t minor of all 1's.

**Theorem 1.7 (Kovari-Sos-Turan, 1954).** Suppose that A is an L x L matrix whose entries are 0 or 1. Suppose that A has no V x W minor of all 1's, for some integers V <= W. Then the number of 1's in A is at most C(V)W^{1/V}L^{(2V-1)/V}.

**Theorem 2.1 (Kovari-Sos-Turan, general form).** Suppose that A is an M x N matrix whose entries are 0 or 1. Suppose that A has no V x W minor of all 1's. Then the number of 1's in A is at most C(V)W^{1/V}MN^{(V-1)/V}.

## Chapter: Elekes-Sharir Approach to Distinct Distances

**Lemma 1.** |d(P)| |Q(P)| >= (N^2 - N)^2 >= N^4.

**Lemma 2.** |p_1 - q_1| = |p_2 - q_2| != 0 iff there exists a unique g in G with g(p_1) = p_2 and g(q_1) = q_2.

## Chapter: Algebraic Structure and Degree Reduction

**Proposition 0.1.** For any L lines in F^3, there is a polynomial of degree <= 3L^{1/2} that vanishes on each line.

**Proposition 1.1 (Degree Reduction).** Let X be a union of L lines in F^3. Suppose that each line contains > A intersection points with other lines. Then the degree of X is <= L/A.

## Chapter: Bezout's Theorem in 3D

**Theorem 4.1 (Bezout for lines in 3D).** If P, Q in F[x, y, z] have no common factor (of degree >= 1), then the number of lines in Z(P,Q) is <= (degP)(degQ).

**Lemma 4.2.** If X is a union of L lines in F^n, then the rank of E_X: V_d -> Fcn(X, F) is >= Ld - c(L).

## Chapter: Special Points and Lines of Algebraic Surfaces

**Theorem 2.1 (Implicit Function Theorem).** If a point x in Z(P) is not a critical point of P then Z(P) is a smooth manifold in some open neighborhood centered at x.

**Lemma 2.3.** If P is square free then P, partial_1 P, ..., partial_n P have no common nonconstant factors.

**Proposition 2.4.** If n = 2 and P is a square free polynomial of degree d then the number of critical points in Z(P) is at most 2d^2.

**Theorem 2.5 (Bezout for lines).** If P, Q in R[x_1, x_2, x_3] have no common factor then the set Z(P) intersect Z(Q) contains at most deg(P)deg(Q) lines.

## Chapter: Flecnodal Points and Ruled Surfaces

**Theorem 0.1.** If P is a polynomial in C[z_1, z_2, z_3], and if FP vanishes on Z(P), then Z(P) is ruled.

**Proposition 0.2.** Suppose that P in R[x_1, x_2, x_3]. Let O be an open subset of Z(P). Suppose that V is a smooth, non-zero vector field on O, obeying the flectodal equation, with nabla P(x) != 0 and nabla^2 P(x) non-degenerate on TZ x TZ. Then the integral curves of V are straight line segments.

## Chapter: The Regulus Detection Lemma

**Regulus Detection Lemma.** For any polynomial P in R[x_1, x_2, x_3], we can associate a list of polynomials RP with the following properties: (1) DegRP <= CDegP, (2) If x is contained in two lines in Z(P), then RP(x) = 0, (3) If P is irreducible and RP vanishes on Z(P), and if there is a non-special point x contained in two lines in Z(P), then Z(P) is a regulus.

**Lemma 0.1.** The set {(Q_1, Q_2, Q_3) in H_{=1} x ... x H_{=3} | dim I_{=3} <= 8} is an algebraic set equal to Z(R), where R is a finite list of polynomials in the coefficients of Q_s, each of degree <= 9.

**Lemma 0.2.** Suppose that x is a regular point of Z(P) with nabla^2 P(x): T_x Z x T_x Z -> R having signature (1,1). Then RP(x) = 0 if and only if nabla^3_{nu_1} P(x) = nabla^3_{nu_2} P(x) = 0.

**Lemma 0.3.** If x lies in two lines in Z(P), then RP(x) = 0.

**Lemma 0.4.** If P is irreducible and RP vanishes on Z(P), and if there is a non-special point x_0 contained in two lines in Z(P), then Z(P) is a regulus.

**Proposition 0.5.** Suppose P in R[x_1,x_2,x_3], V a smooth non-zero flectodal vector field on O with nabla P != 0 and nabla^2 P non-degenerate. Then the integral curves of V are straight line segments.

**Lemma 0.6.** If nabla P(x) = 0, then RP(x) = 0.

**Lemma 0.7.** Assume x is a regular point of Z(P). Then x is flat if and only if nabla^2 P(x): T_x Z x T_x Z -> R is equal to zero, if and only if Q_{2,x} is a multiple of Q_{1,x}.

**Lemma 0.8.** If x is a flat point of Z(P), then RP(x) = 0.

## Chapter: Incidence Estimates (Lines in R^3)

**Theorem 1.1.** Suppose that L is a set of L lines in R^3 with <= B lines in any plane or regulus, and suppose that B >= L^{1/2}. Then |P_2(L)| <= BL (up to constants).

**Theorem 1.2.** Suppose that L is a set of L lines in R^3 with <= B lines in any plane or regulus. Suppose that B >= L^{1/2} and 2 <= k <= L^{1/2}. Then |P_k(L)| <= BLk^{-2} (up to constants).

## Chapter: Introduction to Diophantine Equations

**Theorem 1.1 (Thue).** Suppose P in Z[x,y] is a homogeneous polynomial with degree >= 3 which is irreducible (over Z). If A is any integer, then the equation P(x) = A has only finitely many integer solutions.

**Proposition 2.1.** For any epsilon > 0, for almost every real number beta, there are only finitely many integer solutions to |beta - x/y| <= |y|^{-2-epsilon}.

**Proposition 2.2 (Liouville, 1840's).** If beta is an irrational algebraic number and x/y is a rational number, then |beta - x/y| >= c(beta)|y|^{-deg(beta)}.

**Theorem 2.3 (Thue).** If beta is an irrational algebraic number, and gamma > (deg(beta)+2)/2, then there are only finitely many integer solutions to |beta - x/y| <= |y|^{-gamma}.

## Chapter: Proof of Thue's Theorem - Part I

**Proposition 1.1 (Gauss).** If P in Z[x] satisfies partial^j P(r) = 0 for j = 0, 1, ..., l-1, then P(x) = (qx - p)^l P_1(x) for some P_1 in Z[x].

**Corollary 1.2.** |P| >= ||r||^l.

**Proposition 2.1.** If L: Z^M -> Z^N is a linear map, given by a matrix with integer coefficients, with M > N, then there exists a nonzero x in Z^M such that Lx = 0.

**Proposition 2.2 (Siegel's Lemma).** If L: Z^M -> Z^N is a linear map, given by a matrix with integer coefficients, with M > N, then there exists a nonzero x in Z^M with |x|_inf <= |L|_{op}^{N/(M-N)} such that Lx = 0.

## Chapter: Proof of Thue's Theorem - Part II

**Proposition 1.1.** For any r in Q^2, and any l >= 0, there is a polynomial P in Z[x_1, x_2] with the form P(x_1, x_2) = P_1(x_1)x_2 + P_0(x_1) obeying certain vanishing conditions with |P| <= C(epsilon)^l ||r_1||^{l/2 + epsilon}.

**Proposition 1.2 (Schneider).** If P(x_1, x_2) = P_1(x_1)x_2 + P_0(x_1) in Z[x_1, x_2], and partial_1^j P(r) = 0 for j = 0, ..., l-1, and l >= 2, then |P| >= min((2DegP)^{-1}||r_1||^{(l-1)/2}, ||r_2||).

**Proposition 2.1.** Let beta be an algebraic number. For any natural number l and any epsilon > 0, there is a polynomial P in Z[x_1, x_2] with the form P_1(x_1)x_2 + P_0(x_1) with partial_1^j P(beta, beta) = 0 for 0 <= j <= l-1, |P| <= C(beta)^{l/epsilon}, and degree < (1+epsilon)(1/2)deg(beta)l + 1.

**Lemma 2.2.** Suppose Q(beta) = 0, where Q in Z[x] with degree deg(Q) = deg(beta) and leading coefficient q_{deg(beta)}. Then for any d >= 0, q_{deg(beta)}^d beta^d = sum_{k=0}^{deg(beta)-1} A_{kd} beta^k, with A_{kd} in Z and |A_{kd}| <= [2|Q|]^d.

## Chapter: Proof of Thue's Theorem - Part III

**Theorem 1.1 (Thue, restated).** If beta is an irrational algebraic number, and gamma > (deg(beta)+2)/2, then there are only finitely many integer solutions to |beta - p/q| <= |q|^{-gamma}.

**Theorem 4.1 (Taylor's Theorem).** If f is a smooth function on an interval, then f(x + h) can be approximated by its Taylor expansion around x with error bounded by (1/m!) sup |partial_m f|.

**Corollary 4.2.** If Q is a polynomial, and Q vanishes at x to order m >= 1, and if |h| <= 1, then |Q(x+h)| <= C(x)^{degQ}|Q|h^m.

## Chapter: How Combinatorics and Analysis Interact

**Theorem 1.1 (Loomis-Whitney, 1950's).** If |Pi_i(X)| <= A, then |X| <= A^{n/(n-1)} (up to constants).

**Lemma 1.2 (Main Lemma).** If sum |Pi_j(X)| <= B, then there exists a column of cubes with between 1 and B^{1/(n-1)} cubes of X.

**Corollary 1.3.** If sum_j |Pi_j(X)| <= B, then |X| <= B^{n/(n-1)}.

**Theorem 1.4 (More general Loomis-Whitney).** If U is an open set in R^n with |Pi_i(U)| <= A, then |U| <= A^{n/(n-1)} (up to constants).

**Corollary 1.5 (Isoperimetric inequality).** If U is a bounded open set in R^n, then Vol_n(U) <= Vol_{n-1}(partial U)^{n/(n-1)} (up to constants).

**Theorem 2.1 (Sobolev inequality).** If u in C^1_{comp}(R^n), then ||u||_{L^{n/(n-1)}} <= C ||nabla u||_{L^1}.

**Proposition 2.2 (Markov/Chebyshev inequality for L^p).** If ||u||_p <= M, then |S(h)| <= M^p h^{-p}.

**Lemma 2.3.** If u in C^1_{comp}(R^n), |Pi_j(S(h))| <= h^{-1} ||nabla u||_{L^1}.

**Lemma 2.4 (Revised Lemma 2.3).** Let S_k := {x : 2^{k-1} <= |u(x)| <= 2^k}. Then |Pi_j S_k| <= 2^{-k} integral_{S_{k-1}} |nabla u|.

**Corollary 2.5.** |S_k| <= 2^{-kn/(n-1)} (integral_{S_{k-1}} |nabla u|)^{n/(n-1)} (up to constants).

## Chapter: Hardy-Littlewood-Sobolev Inequality

**Proposition 0.1.** ||T_alpha chi_{B_r}||_q <= C ||chi_{B_r}||_p if and only if alpha q > n and n - alpha + n/q = n/p.

**Theorem 0.2 (Hardy-Littlewood-Sobolev).** If p > 1 and alpha = n(1 - 1/q + 1/p), then ||T_alpha f||_q <= C ||f||_p.

**Lemma 1.1 (Vitali Covering Lemma).** If {B_i}_{i in I} is a finite collection of balls, then there exists a subcollection J such that {B_j}_{j in J} are disjoint but union_{i in I} B_i is contained in union_{j in J} 3B_j.

**Lemma 1.2 (Ball doubling).** If {B_i}_{i in I} is a finite collection of balls, then |union 2B_i| <= 6^n |union B_i|.

**Lemma 2.1 (Hardy-Littlewood maximal inequality, weak type).** |S_{Mf}(h)| <= C h^{-1} ||f||_1.

**Proposition 2.2 (Hardy-Littlewood maximal inequality, strong type).** ||Mf||_p <= C ||f||_p.

**Lemma 2.3.** |S_{Mf}(h)| <= C h^{-1} integral_{S_f(h/2)} |f|.

**Lemma 3.1.** T_alpha f(x) = integral_0^infty r^{n-alpha-1} (average on B(x,r) of f) dr.

## Chapter: Oscillating Integrals and the Kakeya Problem

**Proposition 1.1 (Fourier inversion).** If f is a smooth compactly supported function, then f(x) = integral hat{f}(omega) e^{2pi i omega x} domega.

**Proposition 2.1.** If ||tilde{T}_alpha f||_p <= C ||f||_p for all examples considered, then n/alpha < p.

**Proposition 3.1.** If f_T and T^+ are defined as above, then for every x in T^+, |tilde{T}_alpha f_T(x)| >= C L^{(n+1)/2 - alpha}.

**Corollary 3.2.** If alpha < (n+1)/2, then there are no bounds of the form ||tilde{T}_alpha f||_p <= C ||f||_p.

**Theorem 4.1 (Besicovitch, 1920's).** For any L >= 1, there is a finite set of disjoint tubes T_i (with length L and radius ~L^{1/2}/1000), with the property that |union_i T_i^+| <= C (log L)^{-1} |union_i T_i|.

**Proposition 4.2.** If g_i are any functions, then with high probability, ||sum_i +/- g_i||_p ~ ||(sum_i |g_i|^2)^{1/2}||_p.

**Corollary 4.3.** If T_i is any set of tubes, and f_{ran} := sum_i +/- f_{T_i}, then with high probability ||f_{ran}||_p ~ ||(sum_i chi_{T_i}^2)^{1/2}||_p ~ ||sum_i chi_{T_i}||_{p/2}^{1/2}.

**Corollary 4.4.** If T_i is any set of tubes of length L, and f_{ran} = sum_i +/- f_{T_i}, then with high probability ||tilde{T}_alpha f_{ran}||_p >= C L^{(n+1)/2-alpha} ||sum_i chi_{T_i^+}||_{p/2}^{1/2}.

**Theorem 4.5 (Fefferman 1971).** If p > 2, then tilde{T}_{(n+1)/2} is not bounded on L^p.

## Chapter: The Multilinear Kakeya Inequality

**Theorem 2.1 (Bennett-Carbery-Tao, Guth).** Suppose that T_{j,a} are cylinders in R^n for 1 <= j <= n and 1 <= a <= A. Each cylinder has radius 1 and infinite length. The axis makes an angle < (100n)^{-1} with the x_j-axis. Let I be the points which lie in one cylinder for each direction. Then the volume of I is <= C A^{n/(n-1)}.

**Lemma 2.2.** V_S(v) = integral_{v^perp} |S intersect pi^{-1}(y)| dvol(y).

**Lemma 2.3 (Cylinder estimate).** Let T be an infinite cylinder of radius r with direction v. Then V_{Z(P) intersect T}(v) <= C r^{n-1} deg(P).

**Lemma 2.4.** If S is a hypersurface in R^n, and v_1,...,v_n are unit vectors nearly aligned with coordinate axes, then Vol_{n-1}S <= 2 sum_j V_S(v_j).

**Theorem 3.1 (Bennett-Carbery-Tao, Multilinear Kakeya).** For any epsilon > 0, there exists a constant C_epsilon so that for any Kakeya set of tubes, integral prod_{j=1}^n |sum_{i in I(j)} chi_{T_i}|^{1/(n-1)} <= C_epsilon N^epsilon N^n.

**Lemma 3.2.** For each mu, |I(mu)| <= C N^n prod_j 2^{-mu_j/(n-1)}.

**Lemma 3.3.** Let T_{j,a}, a = 1...A_j be cylinders of radius 1 nearly parallel to the x_j axis. Then the volume of the set of points lying in at least one tube of each direction is <= C prod_{j=1}^n A_j^{1/(n-1)}.

## Chapter: Polynomial Cell Decompositions

**Theorem 1.1 (Polynomial Cell Decomposition).** If S is any finite subset of R^n and d is any degree, then there is a non-zero degree d polynomial P so that each component of R^n \ Z(P) contains <= C(n)|S|d^{-n} points of S.

**Theorem 2.1 (Ham Sandwich Theorem).** If U_1, ..., U_n are finite volume open sets in R^n, then there is a hyperplane that bisects each set U_i.

**Theorem 2.2 (General Ham Sandwich Theorem, Stone-Tukey 1942).** Let V be a vector space of continuous functions on R^n. Let U_1, ..., U_N be finite volume open sets with N < dim V. For any f in V \ {0}, suppose Z(f) has Lebesgue measure 0. Then there exists f in V \ {0} which bisects each U_i.

**Lemma 2.4 (Polynomial Existence Lemma).** If p_1, ..., p_N in R^n are points and N < binomial(d+n, n), then there is a non-zero polynomial of degree <= d that vanishes at each x_i.

**Corollary 4.1 (Polynomial Ham Sandwich for Finite Sets).** Let S_1, ..., S_N be finite sets of points in R^n with N < binomial(n+d, n). Then there is a non-zero polynomial of degree <= d that bisects each set S_i.

**Theorem 3.1 (Borsuk-Ulam).** Suppose that phi: S^N -> R^N is a continuous map that obeys the antipodal condition phi(-x) = -phi(x) for all x in S^N. Then the image of phi contains 0.

**Continuity Lemma.** Let V be a finite-dimensional vector space of continuous functions on R^n. Suppose that for each f in V \ {0}, the set Z(f) has measure 0. If U is a finite volume open set, then the measure of {x in U | f(x) > 0} depends continuously on f in V \ {0}.

## Chapter: Using Polynomial Cell Decompositions

**Theorem 1.1 (Szemeredi-Trotter, via cell decomposition).** If S is a set of S points and L is a set of L lines in R^2, then I(S, L) <= C_0[S^{2/3}L^{2/3} + S + L].

**Lemma 1.2 (Counting Lemma).** I(S, L) <= L + S^2 and I(S, L) <= L^2 + S.

**Theorem 2.1 (3D Szemeredi-Trotter).** Given S points and L lines in R^3 with at most B lines in any plane, I(S, L) <= C[S^{1/2}L^{3/4} + B^{1/3}L^{1/3}S^{2/3} + S + L].

**Corollary 2.2.** If L is a set of L lines in R^3 with <= L^{1/2} lines in any plane and k >= 3, then the number of k-rich points is <= CL^{3/2}k^{-2}.

## Chapter: What's Special About Polynomials? (Geometric Perspective)

**Theorem 0.1 (Efficiency of complex polynomials in zeroes).** Suppose P: C -> C is a complex polynomial and F: R^2 -> R^2 is any smooth function agreeing with P outside the unit disk D, with 0 a regular value. Then the number of zeroes of P in D is <= the number of zeroes of F in D.

**Theorem 0.2 (Efficiency of complex polynomials in surface area).** If P: C^n -> C is a complex polynomial and F: R^{2n} -> R^2 agrees with P outside the unit ball B^{2n}, with 0 a regular value, then Vol_{2n-2}[Z(P) cap B] <= Vol_{2n-2}[Z(F) cap B].

**Lemma 0.3.** For almost every complex line L in C^n, |L cap Z(P) cap B| <= |L cap Z(F) cap B|.

**Theorem 0.4 (Kronheimer-Mrowka).** If P: C^2 -> C is a complex polynomial and F: R^4 -> R^2 agrees with P outside B^4, with 0 a regular value, and Z(P), Z(F) connected, then genus(Z(P)) <= genus(Z(F)).

**Theorem 0.5 (Efficiency of real polynomial space in zeroes).** The space V_1(d) has dimension d+1 and every P in V_1(d)\{0} has at most d zeroes. For any other (d+1)-dimensional space W, some F in W\{0} has at least d zeroes.

**Theorem 0.6 (Gromov, Efficiency of real polynomial space in volume).** sup_{0 != P in V_n(d)} Vol_{n-1} Z(P) cap B^n ~ d. If W is any vector space of continuous functions with dim W >= dim V_n(d), then sup_{0 != F in W} Vol_{n-1} Z(F) cap B^n >= cd.

**Theorem 0.7 (Crofton).** There exists a constant alpha_n so that Vol_{n-1}(X) = alpha_n integral_{AG(1,n)} |l cap X| dmu(l) for every smooth hypersurface X in R^n.

**Theorem 0.8 (Stone-Tukey, restated).** If W is a vector space of continuous functions from B^n to R, and U_1,...,U_N are finite volume open sets with N < dim W, and each F in W\{0} has meas(Z(F)) = 0, then there is a nonzero F in W bisecting each U_i.

## Chapter: Detecting Reguli and Projection Theory

**Theorem 0.1 (Incidence bound with regulus restriction, restated).** If L is a set of L lines in R^3 with <= B lines in any plane or regulus, and B >= L^{1/2}, then |P_2(L)| <= BL.

**Theorem 0.2 (3-rich points with plane restriction).** If L is a set of L lines in R^3 with <= B lines in any plane, and B >= L^{1/2}, then |P_3(L)| <= CsBL.

**Plane Detection Lemma.** For any polynomial P in R[x_1, x_2, x_3], we can associate a list of polynomials SP with: (1) DegSP <= 3DegP, (2) If x is in three lines in Z(P) then SP(x)=0, (3) If P is irreducible and SP vanishes on Z(P) then Z(P) is a plane.

**Theorem 1.1 (Lines in non-ruled surfaces).** If P is an irreducible polynomial in C[z_1, z_2, z_3], then either Z(P) is ruled or the number of lines in Z(P) is <= C(deg P)^2.

**Ruled Surface Detection Lemma.** For any polynomial P in C[x_1, x_2, x_3], we can define polynomials FP with: (1) DegFP <= CDegP, (2) If x is contained in a line in Z(P) then FP(x) = 0, (3) If FP vanishes on Z(P) then Z(P) is ruled.

**Lemma 1.2 (Algebraic set from projection).** The set Sol of parameters a for which the flecnodal equations have a non-zero solution V is an algebraic set in C^M.

**Fundamental Theorem of Projection Theory.** If Q(x,y) is a finite list of polynomials homogeneous in y, and F is algebraically closed, then SOL := {x | Q(x,y) = 0 has a nonzero solution y} is an algebraic set.

**Proposition 3.1.** For any integers d, B >= 0, the set {x in F^m | dim I(x)_{=d} <= B} is an algebraic set.

**Proposition 3.2.** For any integers d, B >= 0, the set {x in F^m | F[y]/I(x) is infinite dimensional} is an algebraic set.

**Proposition 3.3.** If F is algebraically closed and I is a homogeneous ideal in F[y], then Z(I) contains a non-zero point iff F[y]/I is infinite dimensional.

**Theorem 0.3 (Winding number formula).** The winding number of F: dOmega -> C\{0} is sum_{x in Z(F) cap Omega} sigma_F(x) = sum_{x in Z(P) cap Omega} sigma_P(x).
