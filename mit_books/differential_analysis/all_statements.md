Proposition 1.1:
A map f: X -> Y between metric spaces is continuous if and only if one of the three following equivalent conditions holds: (1) f^{-1}(O) is open for all O open in Y; (2) f^{-1}(C) is closed for all C closed in Y; (3) lim f(x_n) = f(x) in Y if x_n -> x in X.

Proposition 1.2:
Any two norms on a finite dimensional vector space are equivalent.

Proposition 1.3:
The following are equivalent conditions on a linear functional u: V -> R on a normed space V: (1) u is continuous; (2) u is continuous at 0; (3) {u(f) : f in V, ||f|| <= 1} is bounded; (4) there exists C such that |u(f)| <= C||f|| for all f in V.

Lemma 1.4:
Each f in C_0(X) can be decomposed uniquely as the difference of its positive and negative parts: f = f_+ - f_-, with f_+, f_- in C_0(X) and f_+(x), f_-(x) <= |f(x)| for all x in X.

Lemma 1.5:
Any element u in (C_0(X))' can be decomposed u = u_+ - u_- into the difference of positive elements with ||u_+||, ||u_-|| <= ||u||.

Lemma 1.7:
If u is a positive continuous linear functional on C_0(X) then mu^*, defined by (1.11) and (1.12), is an outer measure.

Lemma 1.8:
Suppose U_i, i = 1, ..., N is a finite collection of open sets in a locally compact metric space and K is a compact subset of the union of the U_i, then there exist continuous functions f_i in C(X) with 0 <= f_i <= 1, supp(f_i) contained in U_i, and the sum of f_i equals 1 in a neighborhood of K.

Proposition 2.3:
The collection of mu^*-measurable sets for any outer measure is a sigma-algebra.

Theorem 2.4:
If mu^* is an outer measure on X then the collection of mu^*-measurable subsets of X is a sigma-algebra and mu^* restricted to M is a complete measure (Caratheodory's theorem).

Proposition 2.5:
If 0 <= u in (C_0(X))' for X a locally compact metric space, then each open subset of X is mu^*-measurable for the outer measure defined by (1.11) and (1.12) and mu in (1.11) is its measure.

Proposition 2.6:
The measure defined by (1.11), (1.12) from 0 <= u in (C_0(X))' by Caratheodory's theorem is a Borel measure.

Proposition 2.8:
The measure defined by (1.11), (1.12) from 0 <= u in (C_0(X))' using Caratheodory's theorem is a Radon measure.

Lemma 2.9:
If Q is rectangular then v^*(Q) = v(Q), where v^* is the outer measure defined by coverings by rectangles and v is the standard volume.

Proposition 2.10:
Lebesgue measure is a Borel measure.

Lemma 3.1:
If G is a subset of N that generates N (in the sense that N is the smallest sigma-algebra containing G), then f: X -> Y is measurable iff f^{-1}(A) is in M for all A in G.

Proposition 3.2:
Any continuous map f: X -> Y between metric spaces is measurable with respect to the Borel sigma-algebras on X and Y.

Proposition 3.3:
For any non-negative mu-measurable extended function f: X -> [0, infinity] there is an increasing sequence f_n of simple measurable functions such that lim f_n(x) = f(x) for each x in X and this limit is uniform on any measurable set on which f is finite.

Lemma 4.2:
If f: X -> [0, infinity] is measurable then the integral of f over E equals 0 for a measurable set E if and only if {x in E : f(x) > 0} has measure zero.

Theorem 4.3 (Monotone Convergence):
Let f_n be an increasing sequence of non-negative measurable (extended) functions, then f(x) = lim f_n(x) is measurable and the integral of f over E equals the limit of the integrals of f_n over E, for any measurable set E.

Lemma 4.5 (Fatou):
If f_k is a sequence of non-negative integrable functions then the integral of liminf f_n is at most liminf of the integrals of f_n.

Theorem 4.6 (Dominated Convergence):
If f_n is a sequence of integrable functions, f_k -> f a.e. and |f_n| <= g for some integrable g then f is integrable and the integral of f equals the limit of the integrals of f_n.

Lemma 4.7:
If a >= 0, b >= 0 and 0 < gamma < 1 then a^gamma * b^{1-gamma} <= gamma * a + (1 - gamma) * b, with equality only when a = b (Young's inequality for products).

Lemma 4.8 (Holder's inequality):
If f and g are measurable then |integral(fg)| <= ||f||_p * ||g||_q for any 1 < p < infinity, with 1/p + 1/q = 1.

Proposition 4.9 (Minkowski's inequality):
If 1 < p < infinity and f, g are in L^p(X, mu) then ||f + g||_p <= ||f||_p + ||g||_p.

Theorem 4.11:
For any measure space (X, M, mu) the spaces L^p(X, mu), 1 <= p < infinity, are Banach spaces.

Theorem 4.12 (Riesz representation):
If X is a locally compact metric space then every continuous linear functional on C_0(X) is given by a unique finite Radon measure on X through integration.

Lemma 5.2:
Let C be a closed and convex subset of a Hilbert space H (i.e., su + (1 - s)v in C if u, v in C and 0 < s < 1). Then C contains a unique element of smallest norm.

Proposition 5.3:
If L: H -> C is a continuous linear functional on a Hilbert space then there is a unique element v in H such that L(u) = <u, v> for all u in H (Riesz representation theorem for Hilbert spaces).

Corollary 5.4:
For any positive measure mu, any continuous linear functional on L^2(X, mu) can be written in the form u(f) = integral(f * g_bar d mu) for a unique g in L^2.

Lemma 6.1:
If V is a subspace of W with a stronger norm (V embeds continuously in W) and V is dense in W, then W' embeds continuously in V' (the dual of the larger space embeds in the dual of the smaller space).

Proposition 6.3:
The function ||u||_{C^1} = ||u||_infinity + sum_i ||partial u / partial x_i||_infinity is a norm on C_0^1(R^n) with respect to which it is a Banach space.

Proposition 6.7:
For u in S(R^n), set ||u||_{(k)} = ||<x>^k u||_{C^k} and define d(u,v) = sum_{k=0}^infinity 2^{-k} ||u-v||_{(k)} / (1 + ||u-v||_{(k)}), then d is a distance function on S(R^n) with respect to which it is a complete metric space.

Corollary 7.2:
For any k in N the norms ||phi||'_k = sup_{|alpha|<=k, |beta|<=k} sup |x^alpha D^beta phi| are equivalent to the standard Schwartz space seminorms.

Lemma 7.1:
The condition phi in S(R^n) can be written as: phi in C^infinity(R^n) and sup |x^alpha D^beta phi| < infinity for all multi-indices alpha, beta.

Proposition 7.3:
A linear functional u: S(R^n) -> C is continuous if and only if there exist C, k such that |u(phi)| <= C * ||phi||_k for all phi in S(R^n).

Lemma 7.5:
The set supp(u) defined by (7.19) is a closed subset of R^n and reduces to (7.18) if u is in S(R^n).

Proposition 8.1:
If v in C_0^0(R^n) and psi in S(R^n) then v * psi in C_0^0(R^n) and ||v * psi||_infinity <= ||v||_infinity * ||psi||_{L^1}.

Proposition 8.2:
If v in C_0^0(R^n) then as t -> 0, v_t = v * phi_t -> v in C_0^0(R^n), where phi_t is an approximation to the identity.

Corollary 8.3:
C_0^k(R^n) is dense in C_0^p(R^n) for any k >= p.

Proposition 8.4:
S(R^n) is dense in C_0^k(R^n) for any k >= 0.

Corollary 8.5:
The map from finite Radon measures to tempered distributions (via inclusion C_0^0 -> S') is injective.

Proposition 8.6:
Elements of L^2(R^n) are "continuous in the mean", i.e., ||tau_t f - f||_{L^2} -> 0 as t -> 0 where tau_t f(x) = f(x - t).

Proposition 8.7:
If U_a are open for a in A and K is a compact subset of their union, then there exist finitely many phi_i in C_c^infinity(R^n), with 0 <= phi_i <= 1, supp(phi_i) contained in U_{a_i}, such that the sum of phi_i equals 1 in a neighbourhood of K (smooth partition of unity).

Lemma 8.8:
The space C_c^infinity(R^n) of smooth functions of compact support is dense in S(R^n).

Proposition 8.9:
If u in S'(R^n) and supp(u) = empty set then u = 0.

Proposition 8.10:
If u in S'(R^n) satisfies x_j * u = 0 for j = 1, ..., n then u = c * delta for some constant c.

Proposition 8.11:
Fourier transformation defines a continuous linear map F: S(R^n) -> S(R^n).

Lemma 8.12:
The Fourier transform of the Gaussian exp(-|x|^2/2) is the Gaussian (2*pi)^{n/2} exp(-|xi|^2/2).

Theorem 9.1:
The Fourier transform F: S(R^n) -> S(R^n) is an isomorphism with inverse given by G(psi)(x) = (2*pi)^{-n} integral(e^{ix.xi} psi(xi) d xi).

Lemma 9.2 (Parseval's identity):
For all phi, psi in S(R^n), integral(phi * psi_bar dx) = (2*pi)^{-n} integral(hat{phi} * hat{psi}_bar d xi).

Proposition 9.3:
Fourier transform extends to an isomorphism F: L^2(R^n) -> L^2(R^n) (Plancherel theorem).

Lemma 9.4:
If m in N is an integer, then u in H^m(R^n) if and only if D^alpha u in L^2(R^n) for all |alpha| <= m.

Proposition 9.6:
The definition (9.7) gives an isomorphism F: H^m(R^n) -> H^m(R^n) for all m in R.

Proposition 9.7:
If m <= 0 is an integer then u in H^m(R^n) if and only if it can be written in the form u = sum_{|alpha|<=|m|} D^alpha u_alpha with u_alpha in L^2(R^n).

Proposition 9.8:
Each of the Sobolev spaces H^m(R^n) is a Hilbert space with the norm and inner product defined by <u, v>_m = (2*pi)^{-n} integral(<xi>^{2m} hat{u}(xi) hat{v}_bar(xi) d xi).

Theorem 10.1 (Sobolev embedding):
If u in H^m(R^n) where m > n/2 then u in C_0^0(R^n), i.e., u is a bounded continuous function vanishing at infinity, and ||u||_infinity <= C * ||u||_m.

Corollary 10.3:
If k in N_0 and m > n/2 + k then H^m(R^n) is contained in C_0^k(R^n), i.e., u and all its derivatives up to order k are bounded and continuous.

Proposition 10.2:
If u in H^m(R^n), m in R, then D^alpha u in H^{m-|alpha|}(R^n) and ||D^alpha u||_{m-|alpha|} <= ||u||_m.

Proposition 10.4:
Schwartz space can be written in terms of weighted Sobolev spaces: S(R^n) = intersection over all m, k of <x>^{-k} H^m(R^n).

Theorem 10.5 (Schwartz representation):
Any tempered distribution can be written in the form of a finite sum u = sum_{|alpha|<=N} D^alpha f_alpha where f_alpha in C_0^0(R^n) for each alpha and N is sufficiently large.

Lemma 10.6:
For any gamma in N_0^n there are polynomials p_{alpha,gamma}(x) of degrees at most |gamma - alpha| such that <x>^{2N} D^gamma phi = sum_{|alpha|<=|gamma|} D^alpha(p_{alpha,gamma} <x>^{2N} phi) for all phi in S(R^n).

Proposition 11.1:
The subspace S(R^n) is weakly dense in S'(R^n), i.e., each u in S'(R^n) is the weak limit of a sequence u_j in S(R^n).

Proposition 11.2:
If u_j -> u and u'_j -> u' weakly in S'(R^n) then cu_j -> cu, u_j + u'_j -> u + u', D^alpha u_j -> D^alpha u and <x>^m u_j -> <x>^m u weakly in S'(R^n).

Theorem 11.4:
Every non-zero constant coefficient differential operator has a tempered fundamental solution (Malgrange-Ehrenpreis theorem, stated without proof).

Lemma 11.5:
E(x, y) = -1/(2*pi) * 1/(x + iy) is locally integrable on R^2 and so defines E in S'(R^2), and satisfies d-bar E = delta.

Theorem 11.6 (Hormander):
If u in S'(R^n) and phi in S(R^n) then u * phi in S'(R^n) intersect C^infinity(R^n) and if supp(phi) is compact then supp(u * phi) is contained in supp(u) + supp(phi), and sing supp(u * phi) is contained in sing supp(u).

Lemma 11.7:
If v in S'(R^n) has compact support and phi in S(R^n) then v * phi in S(R^n).

Theorem 11.9:
If P(D) is hypoelliptic then sing supp(u) = sing supp(P(D)u) for all u in S'(R^n).

Lemma 11.10:
If u in S'(R^n) then for any polynomial p, p(x)u in S'(R^n), and if u has compact support then p(x)u also has compact support.

Theorem 11.12:
Every elliptic differential operator P(D) is hypoelliptic.

Lemma 11.13:
If P_m(xi) is homogeneous of degree m and elliptic then Q(xi) = (1 - phi(xi))/P_m(xi) is in S'(R^n) and is the Fourier transform of a parametrix for P_m(D).

Lemma 11.14:
Let P(xi) be a polynomial of degree m satisfying |P(xi)| >= C|xi|^m in |xi| > 1/C for some C > 0, then |D^alpha(1/P(xi))| <= C_alpha |xi|^{-m-|alpha|} in |xi| > 1/C.

Proposition 11.15:
If f in S'(R^n) and mu in S'(R^n) has compact support then sing supp(u * f) is contained in sing supp(u) + sing supp(f).

Proposition 11.16:
If f in S'(R^n) has compact support then there exists a unique u in S'(R^n) with supp(u) contained in {t >= -T} for some T and (d_t + Delta)u = f in R^{n+1} (existence and uniqueness for the heat equation with compactly supported source).

Theorem 11.17:
If f in S(R^n) then there exists a unique u in C_0^infinity(R^n) such that Delta u = f (solvability and uniqueness for the Laplacian on R^n, n >= 3).

Lemma 12.1:
If psi in C^infinity(R^n \ {0}) is homogeneous of degree 0 then |D^alpha psi| <= C_alpha |x|^{-|alpha|}.

Lemma 12.3:
For any u in S'(R^n), Csp(u) and Css(u) are closed subsets of B^n and if psi in C^infinity(S^n) has supp(psi) disjoint from Css(u) then for R sufficiently large psi_R u is in S(R^n).

Corollary 12.4:
If u in S'(R^n) then Css(u) = empty set if and only if u is in S(R^n).

Lemma 12.5:
If K_i, i = 1, 2, are two disjoint closed compact subsets of B^n then we can define an unambiguous pairing between {u in S'(R^n) : Css(u) contained in K_1} and {v in S'(R^n) : Css(v) contained in K_2}.

Lemma 12.6:
If Css(u) intersect S^{n-1} = empty set then u * v is defined unambiguously for any v in S'(R^n).

Lemma 12.7:
If u in S'(R^n) and Css(u) intersect Gamma = empty set where Gamma is a closed subset of S^{n-1}, then u = u_1 + u_2 where Csp(u_1) intersect Gamma = empty set and u_2 is in S(R^n).

Lemma 12.8:
For any u in S'(R^n) and phi in S(R^n), Css(phi * u) is contained in Css(u) intersect S^{n-1}.

Corollary 12.9:
Under the conditions of Lemma 12.6, Css(u * v) is contained in (sing supp(u) + sing supp(v)) union (Css(v) intersect S^{n-1}).

Lemma 12.10:
If u, v in S'(R^n) and omega in Css(u) intersect S^{n-1} implies -omega not in Css(v) then their convolution u * v is defined unambiguously.

Lemma 12.11:
For a conic cutoff psi_R, where psi in C^infinity(S^{n-1}), Css(hat{psi_R}) is contained in {0}.

Lemma 12.13:
If (p, q) is not in WF_sc(u) then if p in R^n there exists a neighbourhood U of p and a neighbourhood U' of q such that for all phi in C_c^infinity(R^n) with support in U, U' intersect Css(hat{phi u}) = empty set; similarly if p in S^{n-1}.

Proposition 12.14:
For any u in S'(R^n), WF_sc(u) is contained in the boundary of B^n x B^n and WF(u) is contained in R^n x S^{n-1}; these are closed sets. Under projection onto the first variable, pi_1(WF(u)) = sing supp(u) and pi_1(WF_sc(u)) = Css(u).

Corollary 12.15:
For u in S'(R^n), WF_sc(u) = empty set if and only if u is in S(R^n).

Proposition 12.16:
For any u in S'(R^n) and (p, q) in the boundary of B^n x B^n, (p, q) is not in WF_sc(u) if and only if u = u_1 + u_2, u_1, u_2 in S'(R^n), p not in Css(u_1), q not in Css(hat{u_2}).

Corollary 12.17:
For any u in S'(R^n), (p, q) in WF_sc(u) if and only if (q, -p) in WF_sc(hat{u}).

Theorem 12.18:
For u, v in S'(R^n), the product uv is unambiguously defined in S'(R^n) provided (p, omega) in WF_sc(u) intersect (B^n x S^{n-1}) implies (p, -omega) not in WF_sc(v); and the convolution u * v is unambiguously defined in S'(R^n) provided (theta, q) in WF_sc(u) intersect (S^{n-1} x B^n) implies (-theta, q) not in WF_sc(v).

Proposition 16.1:
For any bounded linear operator on a Hilbert space, spec(T) is a compact subset of {|z| <= ||T||}.

Proposition 16.2:
If A is a bounded self-adjoint operator then, with m = inf_{||phi||=1} <A phi, phi> and M = sup_{||phi||=1} <A phi, phi>, we have {m} union {M} is contained in spec(A) which is contained in [m, M].

Proposition 16.3:
If A is a bounded self-adjoint operator and p is a real polynomial in one variable, then ||p(A)|| <= sup_{t in [m,M]} |p(t)| (polynomial functional calculus estimate).
