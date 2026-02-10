# All Statements from "An Algorithmist's Toolkit" (MIT 18.409)

## Statement 1: Definition 1 (Lecture 1)
Let M be an n x n matrix. Suppose that Mx = lambda x for x in R^n, x != 0, and lambda in R. Then we call x an eigenvector and lambda an eigenvalue of M.

## Statement 2: Proposition 2 (Lecture 1)
If M is a symmetric n x n matrix, then:
- If v and w are eigenvectors of M with different eigenvalues, then v and w are orthogonal (v . w = 0).
- If v and w are eigenvectors of M with the same eigenvalue, then so is q = av + bw, so eigenvectors with the same eigenvalue need not be orthogonal.
- M has a full orthonormal basis of eigenvectors v_1, ..., v_n. All eigenvalues and eigenvectors are real.
- M is diagonalizable: M = V Lambda V^T where V is orthogonal (VV^T = I_n), with columns equal to v_1, ..., v_n, and Lambda is diagonal, with the corresponding eigenvalues of M as its diagonal entries. So M = sum_{i=1}^n lambda_i v_i v_i^T.

## Statement 3: Definition 3 (Lecture 1)
We call the span of the eigenvectors with the same eigenvalue an eigenspace.

## Statement 4: Definition 4 (Lecture 1)
For a graph G, the adjacency matrix A = A_G is the n x n matrix given by A_{i,j} = 1 if (i,j) in E, 0 otherwise.

## Statement 5: Definition 5 (Lecture 1)
Given an unweighted graph G, the Laplacian matrix L = L_G is the n x n matrix given by L_{i,j} = -1 if (i,j) in E, d_i if i = j, 0 otherwise, where d_i is the degree of the i-th vertex. Equivalently, L_G = D_G - A_G.

## Statement 6: Remark (Lecture 1)
For any G, 1 = (1, ..., 1) is an eigenvector of L_G with eigenvalue 0, since for this vector X(i) always equals the average of its neighbors' values.

## Statement 7: Proposition 6 (Lecture 1)
The eigenvalues lambda_i and corresponding eigenvectors v_i of L_G satisfy: Order the eigenvalues so lambda_1 <= ... <= lambda_n. Then v_1 = 1 and lambda_1 = 0. So for all i, lambda_i >= 0.

## Statement 8: Lemma 1 (Lecture 2) - Edge Union
If G and H are two graphs on the same vertex set with disjoint edge sets, L_{G union H} = L_G + L_H (additivity).

## Statement 9: Lemma 2 (Lecture 2) - Isolated Vertices
If a vertex i in G is isolated, then the corresponding row and column of the Laplacian are zero, i.e. [L_G]_{i,j} = [L_G]_{j,i} = 0 for all j.

## Statement 10: Lemma 3 (Lecture 2) - Disjoint Union
The Laplacian of the disjoint union of G and H is direct sum of L_G and L_H: L_{G coprod H} = L_G oplus L_H.

## Statement 11: Theorem 4 (Lecture 2) - Disjoint Union Spectrum
If L_G has eigenvectors v_1, ..., v_n with eigenvalues lambda_1, ..., lambda_n, and L_H has eigenvectors w_1, ..., w_n with eigenvalues mu_1, ..., mu_n, then L_{G coprod H} has eigenvectors v_1 oplus 0, ..., v_n oplus 0, 0 oplus w_1, ..., 0 oplus w_n with corresponding eigenvalues lambda_1, ..., lambda_n, mu_1, ..., mu_n.

## Statement 12: Definition 5 (Lecture 2)
Let L_e be the Laplacian of the graph on n vertices consisting of just the edge e.

## Statement 13: Remark (Lecture 2) - Laplacian Quadratic Form
The Laplacian is a quadratic form: x^T L_G x = sum_{(i,j) in E} (x_i - x_j)^2. This implies that L is positive semidefinite.

## Statement 14: Definition 6 (Lecture 2) - Positive Semidefiniteness
A symmetric matrix M is positive semidefinite (PSD) if for all x in R^n, x^T M x >= 0. M is positive definite (PD) if the inequality is strict for all x != 0.

## Statement 15: Lemma 7 (Lecture 2)
M is PSD iff all eigenvalues lambda_i >= 0. Similarly M is PD iff all eigenvalues lambda_i > 0.

## Statement 16: Lemma 8 (Lecture 2) - PSD Matrix Decomposition
M is PSD iff there exists a matrix A such that M = A^T A.

## Statement 17: Definition 9 (Lecture 2) - Incidence Matrix
Let m be the number of edges and n be the number of vertices. Then the incidence matrix nabla = nabla_G is the m x n matrix given by nabla_{e,v} = 1 if e = (v,w) and v < w, -1 if e = (v,w) and v > w, 0 otherwise.

## Statement 18: Lemma 10 (Lecture 2)
L_G = nabla^T nabla.

## Statement 19: Corollary 11 (Lecture 2)
x^T L_G x = ||nabla x||^2 = sum_{(i,j) in E} (x_i - x_j)^2. This gives another proof that L is PSD.

## Statement 20: Theorem 12 (Lecture 2) - Null Space of Connected Graph
If G is connected, the null space of L_G is 1-dimensional and spanned by the vector 1.

## Statement 21: Corollary 13 (Lecture 2)
If G is connected, lambda_2 > 0.

## Statement 22: Corollary 14 (Lecture 2)
The dimension of the null space of L_G is exactly the number of connected components of G.

## Statement 23: Lemma 15 (Lecture 2) - Complete Graph Spectrum
The Laplacian for the complete graph K_n on n vertices has eigenvalue 0 with multiplicity 1 and eigenvalue n with multiplicity n-1 and associated eigenspace {x | x . 1 = 0}.

## Statement 24: Lemma 16 (Lecture 2) - Ring Graph Spectrum
The Laplacian for the ring graph R_n on n vertices has eigenvectors x_k(u) = sin(2 pi k u / n) and y_k(u) = cos(2 pi k u / n) for 0 <= k <= n/2. Both x_k and y_k have eigenvalue 2 - 2 cos(2 pi k / n).

## Statement 25: Lemma 17 (Lecture 2) - Path Graph Spectrum
The Laplacian for the path graph P_n on n vertices has the same eigenvalues as R_{2n} and eigenvectors v_k(u) = sin(pi k u / n + pi / 2n) for 0 <= k < n.

## Statement 26: Definition 18 (Lecture 2) - Graph Product
Let G = (V, E) and H = (W, F). The product graph G x H has vertex set V x W and edge set ((v_1, w), (v_2, w)) for all (v_1, v_2) in E, w in W, and ((v, w_1), (v, w_2)) for all (w_1, w_2) in F, v in V.

## Statement 27: Theorem 19 (Lecture 2) - Graph Products Spectrum
If L_G has eigenvectors v_1, ..., v_n with eigenvalues lambda_1, ..., lambda_n, and L_H has eigenvectors w_1, ..., w_k with eigenvalues mu_1, ..., mu_k, then L_{G x H} has, for all 1 <= i <= n, 1 <= j <= k, an eigenvector z_{ij}(v,w) = x_i(v) y_j(w) of eigenvalue lambda_i + mu_j.

## Statement 28: Lemma 21 (Lecture 2) - Sum of Eigenvalues
Given an n-vertex graph G with degrees d_i, where d_max = max_i d_i, and Laplacian L_G with eigenvalues lambda_i, sum_i lambda_i = sum_i d_i <= d_max * n.

## Statement 29: Lemma 22 (Lecture 2) - Bounds on lambda_2 and lambda_n
Given lambda_i and d_i as above, lambda_2 <= (sum_i d_i) / (n-1) and lambda_n >= (sum_i d_i) / (n-1).

## Statement 30: Theorem 23 (Lecture 2) - Courant-Fischer Formula
For any n x n symmetric matrix A, lambda_1 = min_{||x||=1} x^T A x, lambda_2 = min_{||x||=1, x perp v_1} x^T A x, lambda_max = max_{||x||=1} x^T A x. In general, lambda_k = min_{||x||=1, x in S_{k-1}^perp} x^T A x.

## Statement 31: Corollary 24 (Lecture 2) - Rayleigh Quotient for Graphs
For a graph G with Laplacian L_G, lambda_2 = min_{x perp 1, x != 0} (sum_{(i,j) in E} (x_i - x_j)^2) / (sum_{i in V} x_i^2) and lambda_max = max_{x != 0} (sum_{(i,j) in E} (x_i - x_j)^2) / (sum_{i in V} x_i^2).

## Statement 32: Theorem 1 (Lecture 3) - Courant-Fischer Formula (restated)
Let A be an n x n symmetric matrix with eigenvalues lambda_1 <= lambda_2 <= ... <= lambda_n and corresponding eigenvectors v_1, ..., v_n. Then lambda_k = min_{||x||=1, x in S_{k-1}^perp} x^T A x.

## Statement 33: Corollary 2 (Lecture 3) - Rayleigh Quotient (restated)
Let G = (V, E) be a graph and L be the Laplacian of G. lambda_2 = min_{x != 0, x perp 1} (sum_{(i,j) in E} (x_i - x_j)^2) / (sum_{i in V} x_i^2), lambda_max = max_{x != 0} (sum_{(i,j) in E} (x_i - x_j)^2) / (sum_{i in V} x_i^2).

## Statement 34: Definition 3 (Lecture 3) - Conductance
Let G = (V, E) be a connected graph. For S subset V, define the conductance of S as phi(S) = |E(S, S^c)| / min(|S|, |S^c|), and the conductance of G as phi(G) = min_{S subset V} phi(S).

## Statement 35: Theorem 4 (Lecture 3) - Cheeger's Inequality
lambda_2 / 2 <= phi(G) <= sqrt(2 lambda_2 d_max), where d_max is the maximum degree in the graph.

## Statement 36: Definition 1 (Lecture 4) - Normalized Laplacian
L_tilde = D^{-1/2} L D^{-1/2}, where D is the diagonal degree matrix and L is the Laplacian.

## Statement 37: Theorem 2 (Lecture 4) - Cheeger's Inequality (Normalized)
phi^2 / 2 <= lambda_2_tilde <= 2 phi, where phi is the (normalized) conductance and lambda_2_tilde is the second smallest eigenvalue of the normalized Laplacian.

## Statement 38: Theorem 3 (Lecture 4) - Cheeger (Lower Bound)
phi(G) >= lambda_2_tilde / 2.

## Statement 39: Theorem 4 (Lecture 4) - Cheeger (Upper Bound)
phi(G) <= sqrt(2 lambda_2_tilde).

## Statement 40: Definition 1 (Lecture 6) - Chebyshev Polynomials
The k-th Chebyshev polynomial T_k(x) is the unique polynomial satisfying T_k(cos(theta)) = cos(k theta).

## Statement 41: Lemma 2 (Lecture 6)
T_k(x) = 2x T_{k-1}(x) - T_{k-2}(x), with T_0(x) = 1, T_1(x) = x.

## Statement 42: Proposition 3 (Lecture 6)
The Chebyshev polynomial T_k(x) has leading coefficient 2^{k-1}.

## Statement 43: Proposition 4 (Lecture 6)
For |x| > 1, |T_k(x)| >= (1/2)|2x|^k. In particular, T_k(1 + epsilon) >= (1/2)(1 + 2 epsilon)^k.

## Statement 44: Corollary 5 (Lecture 6) - Chebyshev min-max property
Among all monic polynomials of degree k, T_k / 2^{k-1} has the smallest supremum on [-1, 1], and this supremum is 2^{1-k}.

## Statement 45: Theorem (Lecture 7-8) - Sparsification
For any graph G and epsilon > 0, there exists a graph H with O(n log n / epsilon^2) edges such that (1 - epsilon) L_G <= L_H <= (1 + epsilon) L_G.

## Statement 46: Definition (Lecture 9) - Random Walk Matrix
The random walk matrix W is defined as W = D^{-1} A, where D is the diagonal degree matrix and A is the adjacency matrix. For a d-regular graph, W = A/d.

## Statement 47: Theorem (Lecture 9) - Convergence of Random Walk
For a d-regular graph with eigenvalues 1 = lambda_1 >= lambda_2 >= ... >= lambda_n of W, the distribution after t steps converges to the stationary distribution. The mixing time is O(log(n) / (1 - lambda_2)).

## Statement 48: Claim (Lecture 10) - Rapid Mixing of Expanders
On an expander graph with spectral gap 1 - lambda_2 = Omega(1), the random walk mixes in O(log n) steps.

## Statement 49: Theorem 1 (Lecture 11) - Brunn-Minkowski Inequality
For two bodies A, B in R^n, Vol((A + B)/2)^{1/n} >= (Vol(A)^{1/n} + Vol(B)^{1/n}) / 2.

## Statement 50: Definition 2 (Lecture 11) - Isotropic Position
A convex body K in R^n is in isotropic position if Vol(K) = 1, the center of mass of K is at the origin, and (1/Vol(K)) integral_K x_i x_j dx = delta_{ij} sigma^2 for some sigma.

## Statement 51: Theorem (Lecture 12-14) - KLS Isoperimetric Conjecture / Localization Lemma
(Discussed but not fully stated as a single theorem; relates isoperimetric inequalities to spectral gaps for log-concave distributions.)

## Statement 52: Theorem (Lecture 14) - Convex Body Isoperimetry
Let K subset R^n be a convex body with diameter d. Decompose K into A union B union S, where dist(A, B) >= t. Then min{Vol_n(A), Vol_n(B)} <= (d/t) Vol_n(S).

## Statement 53: Theorem 1 (Lecture 15) - Chernoff Bound
Let x in {+-1}^n be independent random variables with p[x_i = 1] = 0.5, and a_1, ..., a_n satisfying sum a_i^2 = 1. Then Pr[|sum_{i=1}^n a_i x_i| > t] <= 2 e^{-t^2/2}.

## Statement 54: Claim 2 (Lecture 15)
sum a_i x_i = a . x = distance of x from hyperplane H_a = {x | a . x = 0}.

## Statement 55: Theorem 1 (Lecture 16) - Isoperimetric Inequality on the Sphere
For any A with Vol(A) = 1/2, Vol(A_epsilon) > 1 - e^{-n epsilon^2 / 2}, where A_epsilon is the set of points on S^{n-1} within distance epsilon of A.

## Statement 56: Definition 2 (Lecture 16) - 1-Lipschitz
A function f: S^{n-1} -> R is 1-Lipschitz if |f(a) - f(b)| <= |a - b| for all a, b in S^{n-1}.

## Statement 57: Theorem 3 (Lecture 16) - Concentration of Measure for Lipschitz Functions
If f is Lipschitz, M is its median, and epsilon > 0, then Vol({x : |f(x) - M| > epsilon}) <= 2 e^{-n epsilon^2 / 2}.

## Statement 58: Theorem 4 (Lecture 16) - Weak Isoperimetric Inequality
For any A subset S^{n-1} and any epsilon > 0, Vol(A_epsilon) > 1 - 2 e^{-n epsilon^2 / 16} / Vol(A).

## Statement 59: Definition 5 (Lecture 16) - Modulus of Convexity
The modulus of convexity delta for a sphere is delta(epsilon) = inf{1 - |(x+y)/2| : x, y in S^{n-1}, |x - y| >= epsilon} = 1 - sqrt(1 - epsilon^2/4) >= epsilon^2/8.

## Statement 60: Theorem 1 (Lecture 17) - Measure Concentration on the Sphere (restated)
Let S^{n-1} be the unit sphere in R^n and A in S^{n-1} be a measurable set with vol(A) >= 1/2, and let A_epsilon denote the set of points of S^{n-1} with distance at most epsilon from A. Then vol(A_epsilon) >= 1 - e^{-n epsilon^2 / 2}.

## Statement 61: Definition 2 (Lecture 17) - c-Lipschitz
A function f: A -> B is c-Lipschitz if, for any u, v in A, ||f(u) - f(v)|| <= c . ||u - v||.

## Statement 62: Lemma 3 (Lecture 17)
For a unit vector x in S^{n-1}, and f(x) = sqrt(x_1^2 + x_2^2 + ... + x_k^2). Let x be a vector randomly chosen with uniform distribution from S^{n-1} and M be the median of f(x). Then f(x) is sharply concentrated with Pr[|f(x) - M| >= t] <= 2 e^{-t^2 n / 2}.

## Statement 63: Definition 4 (Lecture 17) - D-embedding
Suppose X = {x_1, ..., x_n} is a finite set, d is a metric on X, and f: X -> R^k is 1-Lipschitz. The "distortion" of f is the minimum D for which ||f(x_i) - f(x_j)|| <= d(x_i, x_j) <= D ||f(x_i) - f(x_j)||.

## Statement 64: Theorem 5 (Lecture 17) - Johnson-Lindenstrauss
Let X = {x_1, ..., x_n} in R^m (for any m) and let k = O(epsilon^{-2} log n). Let L be a uniform random k dimensional subspace. Let y_i be projections of x_i on L. Let y_i' = c y_i for some fixed constant c = Theta(k/m). Then, with high probability L is a (1+epsilon)-embedding of X into R^k.

## Statement 65: Theorem 6 (Lecture 17) - Dvoretzky's Theorem
There is a positive constant c > 0 such that, for all epsilon and n, every n-dimensional origin-symmetric convex body has a section within distance 1 + epsilon of the unit ball of dimension k >= c epsilon^2 / log(1 + epsilon^{-1}) * log n.

## Statement 66: Definition (Lecture 18) - Lattice
Given n linearly independent vectors b_1, ..., b_n in R^m, the lattice generated by them is L(b_1, ..., b_n) = {sum x_i b_i | x_i in Z}. The rank of the lattice is n and its dimension is m. If n = m, the lattice is a full-rank lattice.

## Statement 67: Definition (Lecture 18) - Fundamental Parallelepiped
For matrix B, P(B) = {Bx | x in [0,1)^n} is the fundamental parallelepiped of B.

## Statement 68: Lemma (Lecture 18) - Basis Characterization
Let Lambda be a rank n full-rank lattice and B an invertible n x n matrix. Then B is a basis (of Lambda) if and only if P(B) intersect Lambda = {0}.

## Statement 69: Definition (Lecture 18) - Unimodular Matrix
A square matrix U is unimodular if all entries are integer and det(U) = +/- 1.

## Statement 70: Lemma (Lecture 18) - Unimodular Inverse
U is unimodular iff U^{-1} is unimodular.

## Statement 71: Lemma (Lecture 18) - Equivalent Bases
Nonsingular matrices B_1, B_2 are equivalent bases if and only if B_2 = B_1 U for some unimodular matrix U.

## Statement 72: Corollary (Lecture 18) - Column Operations for Equivalent Bases
Nonsingular matrices B_1, B_2 are equivalent if and only if one can be obtained from the other by: (1) b_i <- b_i + k b_j for k in Z, (2) b_i <-> b_j, (3) b_i <- -b_i.

## Statement 73: Definition (Lecture 18) - Determinant of Lattice
Let L = L(B) be a lattice of rank n. The determinant of L is det(L) = sqrt(det(B^T B)). For a full rank lattice, det(L) = |det(B)|.

## Statement 74: Definition (Lecture 18) - Dual Lattice
The dual Lambda^* of lattice Lambda is {x in R^n : for all v in Lambda, x . v in Z}.

## Statement 75: Definition (Lecture 18) - Dual Basis
For matrix B, its dual basis B^* is the unique basis satisfying span(B) = span(B^*) and B^T B^* = I.

## Statement 76: Fact (Lecture 18)
(L(B))^* = L(B^*).

## Statement 77: Fact (Lecture 18)
(Lambda^*)^* = Lambda.

## Statement 78: Fact (Lecture 18)
det(Lambda^*) = 1 / det(Lambda).

## Statement 79: Definition (Lecture 18) - Successive Minima
The i-th successive minimum of lattice Lambda, lambda_i(Lambda), is inf{r | dim(span(Lambda intersect B_bar(0,r))) >= i}.

## Statement 80: Theorem (Lecture 18) - Blichfeldt's Theorem
For any full-rank lattice Lambda and (measurable) set S in R^n with vol(S) > det(Lambda), there exist distinct z_1, z_2 in S such that z_1 - z_2 in Lambda.

## Statement 81: Theorem (Lecture 18) - Minkowski's Theorem
Let Lambda be a full-rank lattice of rank n. Any centrally-symmetric convex set S with vol(S) > 2^n det(Lambda) contains a nonzero lattice point.

## Statement 82: Theorem 1 (Lecture 19) - Blichfeldt's Theorem (restated)
For any full rank lattice L and measurable set S in R^n with Vol(S) > det(L), there exist distinct z_1, z_2 in S such that z_1 - z_2 in L.

## Statement 83: Theorem 2 (Lecture 19) - Minkowski's Theorem (restated)
If L is a full rank lattice, and S any centrally-symmetric convex set of volume greater than 2^n * det(L), then S contains a nonzero point of L.

## Statement 84: Corollary 3 (Lecture 19) - Bound on Shortest Vector
For any full-rank lattice L, lambda_1(L) <= sqrt(n) * (det L)^{1/n}.

## Statement 85: Lemma 4 (Lecture 19) - Gram-Schmidt Lower Bound
For any nonzero b in L(B), ||b|| >= min_i ||b_i^*||, where b_i^* are the Gram-Schmidt orthogonalized vectors.

## Statement 86: Proposition 5 (Lecture 19) - Reduced Basis in 2D
A reduced basis for a 2-dimensional lattice contains the first two successive minima of L.

## Statement 87: Definition 6 (Lecture 19) - Reduced Bases (LLL)
Let {b_1, ..., b_n} be a basis for a lattice L and let M be its Gram-Schmidt matrix. Then {b_1, ..., b_n} is a reduced basis if: (1) All non-diagonal entries of M satisfy |mu_{ik}| <= 1/2, and (2) For each i, ||pi_{S_i} b_i||^2 <= (4/3) ||pi_{S_i} b_{i+1}||^2, where S_i is the subspace orthogonal to span(b_1, ..., b_{i-1}).

## Statement 88: Definition 1 (Lecture 20) - Reduced Basis (restated)
Let {b_1, ..., b_n} be a basis for a lattice L and let M be its GS matrix. {b_1, ..., b_n} is a reduced basis if: Condition 1: all non-diagonal entries of M satisfy |mu_{ik}| <= 1/2. Condition 2: for each i, ||pi_{S_i} b_i||^2 <= (4/3) ||pi_{S_i} b_{i+1}||^2.

## Statement 89: Claim 2 (Lecture 20) - LLL Approximation Bound
If b_1, ..., b_n is a reduced basis, then ||b_1|| <= 2^{(n-1)/2} lambda_1(L).

## Statement 90: Theorem 3 (Lecture 20) - Lenstra's Theorem
If our polytope/convex body is in R^n for any constant n, then there exists a polynomial time algorithm for integer programming.

## Statement 91: Lemma 4 (Lecture 20) - Lattice Point Approximation
Let b_1, ..., b_n be any basis for L with ||b_1||^2 <= ... <= ||b_n||^2. Then for every x in R^n, there exists a lattice point y such that ||x - y||^2 <= (1/4)(||b_1||^2 + ... + ||b_n||^2) <= (1/4) n ||b_n||^2.

## Statement 92: Lemma 5 (Lecture 20) - Reduced Basis Product Bound
For a reduced basis b_1, ..., b_n ordered as above, prod_{i=1}^n ||b_i|| <= 2^{n(n-1)/4} det(L).

## Statement 93: Definition 1 (Lecture 21) - Spectral Radius
The spectral radius rho of a symmetric matrix M is the absolute value of its largest eigenvalue: rho = |lambda_max|.

## Statement 94: Theorem 2 (Lecture 21) - Iterative Method Convergence
Suppose A is a square matrix admitting a decomposition A = L + S where L is invertible and the largest singular value of L^{-1} S has absolute value rho < 1. Then the iteration x_{k+1} = x_k + L^{-1} r_k for solving Ax = b converges to the correct answer as rho^k.

## Statement 95: Claim 3 (Lecture 21) - Eigenvector Steepest Descent
If the current error vector e_i is an eigenvector of A, then the subsequent descent step moves directly to the correct answer: e_{i+1} = 0.

## Statement 96: Definition 4 (Lecture 21) - Energy Norm
The energy norm of a vector e is given by ||e||_A = e^T A e.

## Statement 97: Theorem 5 (Lecture 21) - Steepest Descent Convergence
Let e_i denote the error vector at step i of steepest descent. Let {v_j}_{j=1}^n be a normalized eigenbasis of A with corresponding eigenvalues lambda_j, and let e_i = sum_j xi_j v_j. Then ||e_{i+1}||_A^2 = ||e_i||_A^2 (1 - (sum_j xi_j^2 lambda_j^2)^2 / ((sum_j xi_j^2 lambda_j^3)(sum_j xi_j^2 lambda_j))).

## Statement 98: Theorem (Lecture 22) - Conjugate Gradient Convergence
The conjugate gradient method satisfies ||e_i||_A <= 2(1 - 2/(sqrt(kappa) + 1))^i ||e_0||_A, where kappa = lambda_max / lambda_min is the condition number.

## Statement 99: Theorem 1 (Lecture 23) - Ultra-Sparsification
Given a graph G with n vertices and m edges, it is possible to obtain a graph H with n + t log^{O(1)} n edges such that L_H <= L_G <= (n/t) L_H, independent of m.

## Statement 100: Lemma 2 (Lecture 23) - Path Embedding
Let P_{u,v} be a path from u to v of length k, and let E_{u,v} be the graph that just has one edge from u to v. Then E_{u,v} precedes k P_{u,v} (in the Loewner order).

## Statement 101: Theorem 3 (Lecture 23) - Low Average-Stretch Spanning Trees
Any graph G has a spanning tree T into which it can be embedded such that sum_{(i,j) in E(G)} stretch(i,j) <= m log^c n.

## Statement 102: Theorem (Lecture 24) - Multiplicative Weights (Deterministic)
Let m_i^t denote the number of mistakes that expert i makes in the first t games and m^t denote the number of mistakes that Mr. X makes. Then for all i and t, m^t <= 2 log(n) / epsilon + 2(1 + epsilon) m_i^t.

## Statement 103: Theorem (Lecture 24) - Multiplicative Weights (Randomized)
Let m_i^t denote the number of mistakes that expert i makes in the first t games and m^t denote the expected number of mistakes that Mr. X makes. Then for epsilon < 1/2 and for all i and t, E(m^t) <= log(n) / epsilon + (1 + epsilon) m_i^t.

## Statement 104: Theorem (Lecture 24) - Multiplicative Weights (General)
Let D^t denote the probability distribution with which we pick experts at event t. Then for epsilon <= 1/2 and for all T and i, sum_{t=1}^T M(D^t, j^t) <= (rho log(n)) / epsilon + (1+epsilon) sum_{t: M(i,j^t) >= 0} M(i,j^t) + (1-epsilon) sum_{t: M(i,j^t) < 0} M(i,j^t).

## Statement 105: Corollary (Lecture 24) - MW Average Penalty
For any delta, for epsilon <= min(1/2, delta/(4 rho)), for T = 16 rho^2 log(n) / delta^2 rounds and for all i, the average penalty per round obeys: (sum_{t=1}^T M(D^t, j^t)) / T <= delta + (sum_{t=1}^T M(i, j^t)) / T.

## Statement 106: Theorem (Lecture 25) - Von Neumann Minimax
min_D max_j M(D, j) = max_P min_i M(i, P). This quantity lambda^* is the value of the zero-sum game.
