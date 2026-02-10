Lemma 1.1:
Let I be a subset of R be an interval, and f: I -> R^2 a smooth map such that ||f(t)|| = 1 for all t. Then f'(t) = det(f(t), f'(t))Jf(t).

Proposition 1.3 (Frenet equation of motion):
For a regular curve c, d/dt(c'(t)/||c'(t)||) = ||c'(t)||kappa(t)Jc'(t)/||c'(t)|| = kappa(t)Jc'(t).

Corollary 1.4:
If kappa(t) = 0 for all t, then c(I) is a subset of R^2 is part of a straight line.

Corollary 1.5:
Suppose that kappa(t) = 1/R is a nonzero constant. Then c + RJ(c'/||c'||) is constant, and therefore c is part of a circle of radius |R|.

Lemma 2.1:
The curvature of a graph c(t) = (t, f(t)) is kappa(t) = f''(t)/(1 + f'(t)^2)^{3/2}.

Lemma 2.2:
The curvature of a unit speed curve is kappa(t) = det(c'(t), c''(t)). Moreover, c''(t) = kappa(t)Jc'(t), and in particular |kappa(t)| = ||c''(t)||.

Proposition 2.3:
For every kappa: I -> R there is a unit speed curve c: I -> R whose curvature is kappa. Moreover, c is unique up to translations and rotations.

Proposition 2.4:
If c_tilde(t) = c(psi(t)) is a partial reparametrization, their curvatures are related by kappa_{c_tilde}(t) = kappa_c(psi(t)).

Lemma 2.5 (from calculus):
Let I_tilde be a subset of R be an interval, and psi: I_tilde -> R a smooth function such that psi'(t) > 0 for all t. Then psi(I_tilde) = I is an interval, and psi is a one-to-one map from I to I_tilde. Moreover, its inverse map phi = psi^{-1} is again smooth, and by the chain rule phi'(t) = 1/psi'(phi(t)).

Lemma 2.6:
Let d = (d_1, d_2) be a curve such that d_1'(t) > 0 for all t. One can then reparametrize it to a graph.

Lemma 2.7:
Every curve d admits a reparametrization which is a unit speed curve.

Proposition 3.1:
Let c be a unit speed curve, and t_0 a point where kappa(t_0) != 0. Then there is a unique circle which osculates c at t_0 (the osculating circle).

Proposition 3.2:
Let f: U -> R be a smooth function, defined on an open subset U of R^2. Let c: I -> U be a regular curve, which is contained in its level set {f(x) = a}. Then, at every point t such that x = c(t) satisfies grad f(x) != 0, we have +/- kappa(t) = <J grad f(x), D^2 f(x) J grad f(x)> / ||grad f(x)||^3.

Lemma 5.1 (Gram-Schmidt orthogonalization):
Let (v_1, ..., v_k) be linearly independent vectors. There are unique orthonormal vectors (e_1, ..., e_k) of the form e_i = sum_{j <= i} f_{ij} v_j where f_{ii} > 0. In particular, each (e_1, ..., e_i) spans the same subspace as (v_1, ..., v_i). An explicit inductive formula is e_i = (v_i - <v_i, e_1> e_1 - ... - <v_i, e_{i-1}> e_{i-1}) / ||v_i - <v_i, e_1> e_1 - ... - <v_i, e_{i-1}> e_{i-1}||.

Lemma 5.2:
Let E(t) be a family of orthogonal matrices, depending differentiably on t. Write (d/dt)E(t) = E(t)A(t). Then the matrices A(t) are skewsymmetric, A(t)^tr = -A(t).

Lemma 5.4:
Frenet frames are reparametrization invariant. Explicitly, if c is a Frenet curve and d(t) = c(phi(t)) a reparametrization, then d is again Frenet, and its Frenet frame is related to that of c by f_i(t) = e_i(phi(t)).

Theorem 6.1:
We have (d/dt)E(t) = ||c'(t)|| E(t) times a tridiagonal skew-symmetric matrix with entries kappa_1(t), ..., kappa_{n-1}(t), where kappa_1(t), ..., kappa_{n-2}(t) > 0 and kappa_{n-1}(t) in R. Concretely, kappa_i(t) = <e_{i+1}(t), e_i'(t)> / ||c'(t)||.

Proposition 6.2:
Let c be a Frenet curve in R^n. Then det(c', c'', ..., c^{(n)}) / ||c'||^{n(n+1)/2} = prod_{i=1}^{n-1} kappa_i^{n-i}.

Lemma 7.1:
One can write f(t) = (cos theta(t), sin theta(t)), where theta: R -> R is a smooth function, unique up to adding constant integer multiples of 2pi. Specifically, all such functions are of the form theta(t) = theta_0 + integral_{t_0}^t det(f(tau), f'(tau)) dtau, where (cos theta_0, sin theta_0) = f(t_0).

Lemma 7.3:
If deg(f) != 0, f is a surjective (onto) map to the unit circle.

Proposition 7.4:
Let ||p|| = 1 be a point on the circle with the following properties: (i) There are only finitely many 0 <= t_1 < t_2 < ... < t_m < T for which f(t_k) = p; (ii) each such t_k satisfies f'(t_k) != 0. In that case, deg(f) = sum_{k=1}^m sign det(p, f'(t_k)).

Theorem 8.2 (Jordan curve theorem):
Let c be a simple closed curve. Then, the complement of the image of c is the disjoint union of two connected open subsets, one bounded (the inside) and one unbounded (the outside).

Lemma 8.4:
Let c be a closed curve of period T, and set L = integral_0^T ||c'(t)|| dt. Let d be the unit speed reparametrization of c. Then d is again a closed curve, of period L. Moreover, the total curvature of d is the same as that of c.

Proposition 8.5:
kappa^{tot}(c)/2pi is the degree of f(t) = c'(t)/||c'(t)||. In particular, it is always an integer. We call it the rotation number of the curve.

Corollary 8.6:
Let c be a closed curve of period T. Suppose that there are only finitely many points 0 <= t_1 < t_2 < ... < t_m < T where c_2'(t_k) = 0, c_1'(t_k) > 0, and that any such point satisfies kappa(t_k) != 0. Then, the rotation number is kappa^{tot}(c)/2pi = sum_{k=1}^m sign(kappa(t_k)).

Theorem 9.1 (Hopf Umlaufsatz):
Let c be a simple closed curve. Then kappa^{tot}(c) = +/- 2pi.

Proposition 9.3:
A simple closed curve is convex if and only if its curvature never changes sign.

Corollary 9.4:
Let c be a closed curve of period T. Then integral_0^T |kappa(t)| ||c'(t)|| dt >= 2pi.

Theorem 9.5 (Whitney):
Let c be a closed curve with normal self-intersections. Assume that it is parametrized in such a way that c_2(t) reaches a global minimum at t = 0. Then kappa^{tot}(c)/2pi = sign c_1'(0) - sum_{(s,t)} sign det(c'(s), c'(t)), where the sum is over all 0 <= s < t < T with c(s) = c(t).

Lemma 10.1 (Sturm-Hurwitz):
Let f: R -> R be a continuous 2pi-periodic function such that integral_0^{2pi} f(t) dt = 0, integral_0^{2pi} f(t) cos(t) dt = 0, integral_0^{2pi} f(t) sin(t) dt = 0. Then f has at least four zeros in the region [0, 2pi).

Lemma 10.2:
Let h be a smooth 2pi-periodic function. Then h(t) + h''(t) has at least four critical points (points where its derivative vanishes) in the region [0, 2pi).

Lemma 10.3:
Take a simple closed curve whose curvature is everywhere positive. By reparametrizing in a suitable way, one can achieve that the curve has period 2pi and satisfies c'(t)/||c'(t)|| = (cos(t), sin(t)). In that case, kappa(t) = 1/||c'(t)||.

Theorem 10.4 (Four Vertex theorem, strictly convex version):
Take a simple closed curve whose curvature is everywhere positive. Then there are at least four points where kappa'(t) = 0.

Lemma 12.6:
D(nu) = -Df * L (matrix multiplication). More explicitly, each partial derivative partial_{x_i} nu lies in the linear span of {partial_{x_1} f, ..., partial_{x_n} f}, and the shape operator allows us to express it as a linear combination of these vectors: partial_{x_i} nu = -sum_j L_{ji}(x) partial_{x_j} f.

Proposition 13.1:
The coordinate changes for the main associated data are: nu_tilde(x) = nu(phi(x)), G_tilde(x) = D(phi)(x)^tr * G(phi(x)) * D(phi)(x), H_tilde(x) = D(phi)(x)^tr * H(phi(x)) * D(phi)(x), L_tilde(x) = D(phi)(x)^{-1} * L(phi(x)) * D(phi)(x).

Proposition 13.3:
Let f, f_tilde: U -> R^{n+1} be two hypersurface patches, defined on the same connected set U of R^n. Suppose that their first and second fundamental forms coincide. Then f_tilde(x) = Af(x) + c, where A is an orthogonal matrix with determinant +1, and c some constant.

Lemma 14.5:
The Gauss curvature is kappa_{gauss} = (-1)^n det(partial_{x_1} nu, ..., partial_{x_n} nu, nu) / sqrt(det G).

Theorem 16.2:
Let g^{ij} be the coefficients of the inverse matrix G^{-1}. Then Gamma_{ij}^l = (1/2) sum_k g^{kl} (partial_{x_j} G_{ik} - partial_{x_k} G_{ij} + partial_{x_i} G_{jk}).

Theorem 16.3 (Gauss equation):
The Gauss equation holds: H_{ij}L_{sk} - H_{ik}L_{sj} = partial_k Gamma_{ij}^s - partial_j Gamma_{ik}^s + sum_t Gamma_{ij}^t Gamma_{kt}^s - Gamma_{ik}^t Gamma_{jt}^s.

Corollary 17.1 (Theorema egregium for surfaces):
The Gauss curvature of a surface patch is given in terms of the first fundamental form by kappa_{gauss} = sum_u G_{2u} R_{121}^u / det(G).

Lemma 18.2:
For any moving basis, F_{kj} = X^{-1} R_{kj} X.

Lemma 18.3:
If the moving basis is a frame, the A_j and F_{kj} are skew-symmetric matrices.

Proposition 18.4:
If alpha_i = (A_i)_{12}, then kappa_{gauss} sqrt(det(G)) = (F_{21})_{12} = partial_2 alpha_1 - partial_1 alpha_2.

Corollary 18.5 (Gauss-Bonnet for tori):
Let f: R^2 -> R^3 be a doubly-periodic surface patch, which means that f(x_1 + T_1, x_2) = f(x_1, x_2) = f(x_1, x_2 + T_2) for some T_1, T_2 > 0. Then kappa_{gauss}^{tot} = integral_{[0,T_1] x [0,T_2]} kappa_{gauss} sqrt(det(G)) dx_1 dx_2 = 0.

Corollary 18.6:
If f is a doubly-periodic surface patch, then the Gauss curvature must be > 0 at some point, and < 0 at some other point.

Lemma 19.1:
If (v_i)_{1 <= i <= n} is any basis of R^n, then (v_i wedge v_j)_{1 <= i < j <= n} is a basis of the space of antisymmetric matrices.

Lemma 19.3:
We have trace(Lambda^2 L) = (1/2)(trace(L)^2 - trace(L^2)), det(Lambda^2 L) = det(L)^{n-1}.

Lemma 19.4:
Suppose that L, L_tilde: R^n -> R^n are two linear maps, with rank(L) >= 3. Then, if Lambda^2 L = Lambda^2 L_tilde, it also follows that L = +/- L_tilde.

Theorem 20.1 (Generalized theorema egregium):
The Riemann curvature operator R is intrinsic.

Corollary 20.2:
The unordered collection of n(n-1)/2 numbers lambda_i lambda_j is intrinsic.

Corollary 20.3:
kappa_{scalar} and kappa_{gauss}^{n-1} are intrinsic. In particular, kappa_{gauss} is intrinsic for n even, and |kappa_{gauss}| is intrinsic for n >= 3 odd.

Corollary 20.4:
Let f: U -> R^{n+1} be a hypersurface patch, defined on a connected set. Suppose that for each point in U, the matrix H_x has rank >= 3. In that case, the intrinsic geometry of f determines the extrinsic one. This means that if f_tilde: U -> R^{n+1} is another hypersurface patch with the same first fundamental form as f, then necessarily f_tilde(x) = Af(x) + c with A an orthogonal matrix and c a constant.

Lemma 21.1:
For any point p, there is always a local reparametrization such that in the new coordinates, G_tilde_p = 1 is the identity matrix.

Lemma 21.2:
Suppose that we have numbers S_{ijk} (the indices i,j,k run from 1 to n) such that S_{ijk} = S_{jik}. Then there are numbers T_{ijk} with T_{ijk} = T_{kji} such that S_{ijk} = T_{ijk} + T_{jik}.

Corollary 21.3:
For any point p, there is always a local reparametrization such that in the new coordinates, G_tilde_p = 1 and partial_{x_k} G_tilde_p = 0 for all k.

Lemma 22.3:
If X in R^{n+1} has <X, X>_{Min} < 0, then its Minkowski orthogonal complement X^perp = {Y in R^{n+1} : <X, Y>_{Min} = 0} has the property that <., .>_{Min} restricted to X^perp is positive definite.

Corollary 23.3:
Take any Riemannian metric on R^2 which is doubly-periodic, G_{(x_1+T_1,x_2)} = G_{(x_1,x_2)} = G_{(x_1,x_2+T_2)}. Then kappa_{gauss}^{tot} = integral_{[0,T_1] x [0,T_2]} kappa_{gauss} sqrt(det(G)) dx_1 dx_2 = 0.

Proposition 24.3 (L'Hopital's rule):
Let psi: V -> R be a local defining function for M, and phi: V -> R another smooth function which vanishes along V intersect M. Then there is a unique smooth function q: V -> R such that phi = q*psi.

Corollary 24.4:
Let psi, psi_tilde: V -> R be two local defining functions for M. Then there is a unique smooth nowhere vanishing function q: V -> R such that psi_tilde = q*psi.

Lemma 25.2:
For X, Y in TM_y, <X, L_y * Y> = -(1/||grad_y psi||) <X, D^2 psi_y * Y>.

Proposition 25.4:
Let M be a subset of R^{n+1} be a hypersurface. Take a point y in M, a local defining function psi for M near y, and an orthonormal basis Y_1, ..., Y_n of TM_y. Then kappa_{mean} = +/- (1/||grad psi_y||) sum_{i=1}^n <Y_i, D^2 psi_y * Y_i>, kappa_{gauss} = +/- det(D^2 psi_y * Y_1, ..., D^2 psi_y * Y_n, grad psi_y) / ||grad psi_y||^{n+1}.

Theorem 27.2 (Inverse function theorem):
Let V_tilde be an open subset of R^{n+1}, y in V_tilde a point, and phi: V_tilde -> R^{n+1} a smooth map such that D(phi)_y is invertible. Then there is an open subset V of V_tilde, still containing y, such that: U = phi(V) is open, and phi|V: V -> U is a diffeomorphism.

Corollary 27.3 (Implicit function theorem, special case):
Let V_tilde be an open subset of R^{n+1}, psi: V_tilde -> R a smooth function, and y in V a point such that psi(y) = 0, D(psi)(y) != 0. Then there are: an open subset V of V_tilde, still containing y; an open subset U of R^{n+1} containing 0; and a diffeomorphism phi: U -> V such that phi(0) = y, and psi(phi(x)) = x_{n+1} for all x.

Theorem 28.2 (Inverse function theorem):
Let V_tilde be an open subset of R^{n+1}, y in V_tilde a point, and phi: V_tilde -> R^{n+1} a smooth map such that D(phi)_y is invertible. Then there is an open subset V of V_tilde, still containing y, such that: U = phi(V) is open, and phi|V: V -> U is a diffeomorphism.

Corollary 29.1 (Implicit function theorem, special case):
Let V_tilde be an open subset of R^{n+1}, psi: V_tilde -> R a smooth function, and y in V_tilde a point such that psi(y) = 0, D(psi)(y) != 0. Then there are: an open subset V of V_tilde, still containing y; an open subset U of R^{n+1} containing 0; and a diffeomorphism phi: U -> V such that phi(0) = y, and psi(phi(x)) = x_{n+1} for all x.

Lemma 29.2:
Let U be an open subset of R^{n+1} containing the origin, and psi: U -> R a smooth function which vanishes at all points x in U whose last coordinate x_{n+1} is zero. Then there is a unique smooth function q such that psi = q * x_{n+1}.

Corollary 29.4:
For every point y in M, there is a partial parametrization such that y in f(U) = M intersect V.

Proposition 29.5:
Let f be a partial parametrization. Denote by I^f its first fundamental form, and by S^f its shape operator. Under the identification Df: R^n -> TM_{f(x)}, I^f turns into the ordinary scalar product, and S^f into the shape operator S of M.

Proposition 30.1:
Let M be a subset of R^{n+1} be a hypersurface. Take a point y in M, a local defining function psi for M near y, and an orthonormal basis Y_1, ..., Y_n of TM_y. Then kappa_{mean} = +/- (1/||grad psi_y||) sum_{i=1}^n <Y_i, D^2 psi_y * Y_i>, kappa_{gauss} = +/- det(D^2 psi_y * Y_1, ..., D^2 psi_y * Y_n, grad psi_y) / ||grad psi_y||^{n+1}.

Theorem 30.4 (from topology):
A connected compact hypersurface is always orientable (in fact, there are precisely two choices of Gauss vectors, differing by a sign).

Theorem 30.5 (from topology):
Let M be a subset of R^{n+1} be a connected compact hypersurface, with n >= 2, and phi: M -> S^n a smooth map such that D(phi)_y: TM_y -> TS^n_{phi(y)} is an isomorphism for all y. Then phi is bijective (one-to-one and onto).

Theorem 30.7 (Hadamard):
Let M be a subset of R^{n+1}, n >= 2, be a compact connected hypersurface, whose Gauss curvature is everywhere nonzero. Then M is convex.

Lemma 31.1:
Let f be a partial parametrization, and nu^f the associated Gauss normal. Then det(G^f) = det(partial_{x_1} f, ..., partial_{x_n} f, nu^f)^2. In particular, in the case of a surface, sqrt(det(G^f)) = ||partial_{x_1} f x partial_{x_2} f||.

Lemma 32.1:
Let M, M_tilde be hypersurfaces, with Gauss maps nu, nu_tilde, and phi: M -> M_tilde be a smooth map. Suppose that we have a parametrization f: U -> M compatible with the orientation. Set phi^f = phi o f: U -> M_tilde, and let G^f be the first fundamental form. Then for y = f(x), det(D(phi))_y = det(partial_{x_1} phi^f, ..., partial_{x_n} phi^f, nu_tilde(phi^f(x))) / sqrt(det(G^f(x))).

Proposition 32.3:
Suppose that M_tilde is decomposed into f_i(P_i) as in the previous lecture, where f_i: U_i -> M are partial parametrizations, and P_i a subset of U_i polytopes. Then deg(phi) = (1/vol(M_tilde)) (sum_i integral_{P_i} det(partial_{x_1} phi^{f_i}, ..., partial_{x_n} phi^{f_i}, nu_tilde(phi(f_i(x)))) dx).

Lemma 32.4:
Suppose that phi is bijective (one-to-one and onto), and that det(D(phi)) is everywhere positive (or everywhere negative). Then deg(phi) = 1 (or -1).

Theorem 32.5:
The degree is always an integer.

Lemma 33.2:
Let M be a subset of R^{n+1} be a compact hypersurface with a Gauss map, and phi: M -> S^n a smooth map. If deg(phi) != 0, then phi is necessarily onto.

Theorem 33.3:
Let M, M_tilde be a subset of R^{n+1} be compact connected hypersurfaces with orientations, and phi: M -> M_tilde a smooth map. Suppose that p in M_tilde is a point with the following properties: (i) there are only finitely many y_1, ..., y_k in M such that phi(y_i) = p; (ii) at each y_i, we have det(D(phi)_{y_i}) != 0. Then deg(phi) = sum_{i=1}^k sign(det(D(phi)_{y_i})).

Corollary 33.5:
Let M be a compact hypersurface with an orientation. Then kappa_{gauss}^{tot} = (-1)^n vol(S^n) deg(nu). In particular, the total Gauss curvature is always an integer multiple of vol(S^n).

Lemma 34.2:
lim_{rho -> 0} oint_{|x|=rho} alpha = -2pi m.

Theorem 34.4:
Moving frames with singularities always exist. Moreover, for any choice of such frame, the sum of m(p_i) is the same. It agrees with a topological invariant of M, called the Euler characteristic chi(M).

Corollary 34.5 (Gauss-Bonnet theorem):
For any compact surface M in R^3, kappa_{gauss}^{tot} = 2pi * chi(M).

Corollary 34.6:
The Gauss map nu of a compact surface M in R^3 satisfies chi(M) = 2 deg(nu). In particular, chi(M) is always even.

Corollary 34.7:
For any compact surface M in R^3, integral_M ||kappa|| dvol_M >= 4pi.

Theorem 35.1 (Hopf):
Let M be a subset of R^{n+1} be a closed hypersurface of even dimension n, and nu: M -> S^n a Gauss map. Then deg(nu) = chi(M)/2.

Corollary 35.2 (Generalized Gauss-Bonnet):
In the same situation as above, kappa_{gauss}^{tot} = chi(M) vol(S^n)/2.

Theorem 35.4 (combinatorial Gauss-Bonnet):
sum_k kappa_{gauss}^{comb}(V_k) = 2pi chi(M).

Lemma 36.1:
Let gamma:[a,b] -> R^n be a smooth path, with gamma(a) = p and gamma(b) = q. Its length L(gamma) = integral_a^b ||gamma'(t)|| dt is >= ||q - p||, and equality holds iff gamma'(t) is always a nonnegative multiple of q - p.

Lemma 36.3:
If gamma is a geodesic, the speed ||gamma'(t)|| is constant.

Proposition 36.4:
Let f: U -> R^{n+1} be a partial parametrization of M, and c: I -> U a smooth curve on its domain. Then gamma = f(c) is a geodesic iff c itself satisfies the geodesic equation d^2c_k/dt^2 + sum_{ij} Gamma_{ij}^k (dc_i/dt)(dc_j/dt) = 0.

Corollary 36.5:
Two geodesics gamma, gamma_tilde: I -> M with gamma(0) = gamma_tilde(0) and gamma'(0) = gamma_tilde'(0) agree.

Corollary 36.6:
Given any point y in M and any tangent vector Y in TM_y, there is an interval I containing 0 and a geodesic gamma: I -> R such that gamma(0) = y, gamma'(0) = Y. If M is a closed subset of R^{n+1}, one can take I = R, which means that geodesics are defined for all times.

Theorem 38.1:
A curve gamma:[a,b] -> M is a geodesic if and only if for any smooth family of paths (gamma_s), -epsilon < s < epsilon, with the same endpoints gamma_s(a) = p, gamma_s(b) = q and with gamma_0 = gamma, we have (d/ds) E(gamma_s)|_{s=0} = 0.

Corollary 38.2:
A path which is an absolute minimizer of the energy (over all paths gamma:[a,b] -> M with fixed endpoints gamma(a) = p, gamma(b) = q), is necessarily a geodesic.

Theorem 38.3:
Suppose that M is closed and connected. Then, for any given p, q and any interval [a,b], there is a geodesic gamma:[a,b] -> M which is an absolute minimizer of the energy.

Proposition 38.4:
Write the geodesic equations in conjugate variables x_k (position) and p_k = sum_l g_{kl}(x) v_l (momentum). Then they take on the Hamiltonian form x_k' = dH/dp_k, p_k' = -dH/dx_k, where H = (1/2) sum_{ij} p_i g^{ij}(x) p_j.

Lemma 39.1:
If M is a connected hypersurface, then (M, dist) is a metric space, satisfying: dist(p,q) >= 0 with equality iff p = q; dist(p,q) = dist(q,p); dist(p,q) <= dist(p,r) + dist(r,q).

Proposition 39.2 (part of the Cauchy-Schwarz inequality):
Let f:[a,b] -> R be a function. Then integral_a^b f(t) dt <= sqrt(b - a) sqrt(integral_a^b f(t)^2 dt), with equality if and only if f is constant.

Corollary 39.3:
For any path gamma:[a,b] -> M, we have L(gamma) <= 2^{1/2} (b-a)^{1/2} E(gamma)^{1/2}, with equality if and only if gamma has constant speed.

Corollary 39.4:
If we fix the endpoints gamma(a) = p, gamma(b) = q, a path is an absolute energy-minimizer if and only if it is an absolute length-minimizer and is parametrized with constant speed.

Corollary 39.5:
Let M be a closed connected hypersurface. Then, for any two points p, q there is a path gamma connecting them, such that L(gamma) = dist(p, q). In other words, the infimum in the definition of distance is always attained.

Lemma 39.6:
For z, w in U, the distance in the hyperbolic metric is dist(z, w) = 2 arctanh(|z - w| / |w_bar z - 1|).

Theorem 39.7 (Schwarz-Pick):
Let h: U -> U be a holomorphic (complex differentiable) function. Then at every point z in U, |h'(z)| <= (1 - |h(z)|^2) / (1 - |z|^2).

Corollary 39.8:
For h as before, I_{h(z)}(Dh(z)X, Dh(z)X) <= I_z(X, X).

Corollary 39.9:
Any holomorphic function h: U -> U is distance-nonincreasing for the hyperbolic metric: dist(h(p), h(q)) <= dist(p, q).

Lemma 40.7:
Any two points in a Busemann space are joined by a unique metric geodesic.

Lemma 41.2:
Take a partial parametrization f: U -> M of a surface in R^3 compatible with orientation, and let gamma = f(c). Suppose that we have a moving frame (X_1(x), X_2(x)) which is positively oriented, and such that X_1(c(t)) = c'(t)/I_{c(t)}(c'(t), c'(t))^{1/2}. Then, in terms of the associated connection matrices, kappa_{geod}(t) = ((A_1)_{12} c_1'(t) + (A_2)_{12} c_2'(t)) / I_{c(t)}(c'(t), c'(t))^{1/2}.

Theorem 41.3 (Gauss-Bonnet with boundary, for discs):
Let M be a surface in R^3, and f: U -> M a partial parametrization, and D a subset of U a curvilinear disc. Take the simple closed curve c which parametrizes the boundary of D, and consider the total geodesic curvature of gamma = f(c). This satisfies kappa_{geod}^{tot} = integral kappa_{geod}(t) I_{c(t)}(c'(t), c'(t))^{1/2} dt = 2pi - integral_D kappa_{gauss} sqrt(det G) dx.

Corollary 41.4:
Let M be a surface in R^3, f: U -> M a partial parametrization, and T a subset of U a curvilinear triangle, whose sides map to geodesics in M. Let alpha_1, alpha_2, alpha_3 be the angles at the corners of the triangle, measured with respect to the first fundamental form. Then alpha_1 + alpha_2 + alpha_3 = pi + integral_T kappa_{gauss} sqrt(det G) dx.
