# All Mathematical Statements in "Representations of Lie Groups" by Pavel Etingof

## Section 1: Continuous representations of topological groups

**Proposition 1.6.** If V is a Banach space then a representation (V, pi) of G is continuous if and only if the map pi : G -> Aut(V) is continuous in the strong topology.

## Section 2: K-finite vectors and matrix coefficients

**Lemma 2.2.** The map xi: bigoplus_{rho in Irr(K)} End(V_rho) -> L^2(K) given by xi(A_rho) = sqrt(dim rho) * Tr(A_rho * rho(g^{-1})) is an isomorphism of Hilbert spaces.

**Theorem 2.4.** (Peter-Weyl) L^2(K)^{fin} is a dense subspace of L^2(K). Hence {psi_{rho,i,j}} form an orthonormal basis of L^2(K), and the Fourier expansion converges in L^2.

## Section 3: Algebras of measures on locally compact groups

**Lemma 3.2.** (i) If a sequence {mu_n} in C(X)^* is Cauchy then there is a compact subset K of X such that mu_n in C(K)^* for all n. (ii) C(X)^* is a complete locally convex topological vector space.

**Proposition 3.3.** If X is a locally compact second countable Hausdorff space then the dual space C(X)^* = Meas_c(X), the space of compactly supported complex Borel measures on X.

**Corollary 3.5.** If X, Y are locally compact second countable Hausdorff spaces then the natural bilinear map Meas_c(X) x Meas_c(Y) -> Meas_c(X x Y) extends to an isomorphism of completed tensor products.

**Lemma 3.7.** The map C*G x V -> V given by g -> pi(g)v is continuous. Thus pi is continuous in the weak topology of C*G and strong topology of End(V).

**Corollary 3.8.** If (V, pi) is a continuous representation of G then the action G x V -> V uniquely extends to a continuous bilinear map Meas_c(G) x V -> V, which gives rise to a continuous unital algebra homomorphism pi: Meas_c(G) -> End(V).

## Section 4: Plancherel formulas, Dirac sequences, smooth vectors

**Proposition 4.1.** (Plancherel's theorem for compact groups) Let K be a compact group and f_1, f_2 in L^2(K). Then (f_1, f_2) = sum_{rho in Irr(K)} dim(rho) * Tr(hat{f}_1(rho)^* hat{f}_2(rho)).

**Proposition 4.3.** (Plancherel's formula) If K is a compact Lie group and f in C^infty(K) then f(g) = sum_{rho in Irr(K)} dim(rho) * Tr(hat{f}(rho) rho(g)), with absolute and uniform convergence.

**Lemma 4.5.** There exists a sequence phi_n in C_c(G) such that phi_n -> delta_1 in the weak topology as n -> infty. Moreover, if G is a Lie group, we can choose phi_n in C_c^infty(G).

**Corollary 4.6.** C_c(G) is sequentially dense in Meas_c(G). For Lie groups, C_c^infty(G) is sequentially dense in Meas_c(G).

**Corollary 4.7.** Let V be a continuous representation of a compact group K. Then V^{fin} is dense in V.

**Corollary 4.8.** L^2(K)^{fin} subset C(K) is a dense subspace. Moreover, if K is a Lie group then L^2(K)^{fin} subset C^k(K) is a dense subspace for 0 <= k <= infty.

**Corollary 4.9.** If V is an irreducible continuous representation of K then V is finite-dimensional.

**Proposition 4.13.** Let (V, pi) be a continuous representation of a Lie group G with g = Lie(G). Let v in V^infty. Then we have a linear map pi_{*,v} : g -> V^infty given by pi_{*,v}(a) = d/dt|_{t=0} pi(exp(ta))v, which extends to an algebra homomorphism U(g) -> End(V^infty).

**Proposition 4.15.** (i) V^infty is dense in V. (ii) V^{fin} subset V^infty.

## Section 5: Admissible representations and (g, K)-modules

**Proposition 5.4.** If V is K-admissible then V^{K-fin} subset V^infty, and it is a g-submodule.

**Proposition 5.10.** If V is a K-admissible continuous representation of G then V^{K-fin} is an admissible (g, K)-module.

**Theorem 5.13.** (E. Cartan) Every semisimple Lie group G has a maximal compact subgroup K subset G which is unique up to conjugation.

**Theorem 5.15.** (Harish-Chandra's admissibility theorem) Every irreducible unitary representation of a semisimple Lie group is admissible.

## Section 6: Weakly analytic vectors

**Theorem 6.3.** (Harish-Chandra's analyticity theorem) If V is an admissible representation of a semisimple Lie group G with maximal compact subgroup K then every v in V^{K-fin} is a weakly analytic vector.

**Theorem 6.6.** (Elliptic regularity) Suppose D is an elliptic operator with real analytic coefficients on an open set U in R^N, and f(x) is a smooth solution of the PDE Df = 0. Then f is real analytic.

**Corollary 6.7.** Let X be a real analytic manifold and D an elliptic operator on X with analytic coefficients. Then every smooth solution of the equation Df = 0 on X is actually real analytic.

**Corollary 6.11.** The action of G on V is completely determined by the corresponding (g, K)-module V^{K-fin}.

**Corollary 6.12.** Let W subset V^{K-fin} be a sub-(g, K)-module. Then the closure bar{W} subset V is G-invariant.

**Corollary 6.13.** Let V be an admissible representation of G. There is a bijection between subrepresentations of V and (g, K)-submodules of V^{K-fin}, given by alpha: U subset V -> U^{K-fin}. The inverse is given by beta: W -> bar{W}.

**Corollary 6.14.** If V is irreducible then V^{K-fin} is an irreducible (g, K)-module, and vice versa.

**Corollary 6.15.** If V is of finite length then V^{K-fin} is a Harish-Chandra module.

**Theorem 6.16.** The assignment V -> V^{K-fin} defines an exact, faithful functor Rep G -> HC_G, which maps irreducibles to irreducibles.

## Section 7: Infinitesimal equivalence and globalization

**Proposition 7.1.** Let V, W be two unitary representations in Rep G. If V^{K-fin} = W^{K-fin} as Harish-Chandra modules, then V = W as unitary representations. In other words, infinitesimally equivalent unitary representations in Rep G are isomorphic.

**Lemma 7.2.** (Dixmier) Let A be a countable-dimensional C-algebra and M a simple A-module. Then End_A(M) = C. In particular, the center Z of A acts on M by a character chi: Z -> C.

**Corollary 7.3.** (Schur's lemma for (g, K)-modules) Any endomorphism of an irreducible (g, K)-module M is a scalar. Thus the center Z(g) of U(g) acts on M by an infinitesimal character chi: Z(g) -> C.

**Theorem 7.5.** (Harish-Chandra's globalization theorem) Every unitary irreducible Harish-Chandra module M for G uniquely integrates (=globalizes) to an irreducible admissible unitary representation of G.

**Corollary 7.6.** For a semisimple Lie group G, the assignment V -> V^{K-fin} is an equivalence of categories between unitary representations of G of finite length and unitary Harish-Chandra modules of finite length.

## Section 8: Highest weight modules and Verma modules

**Proposition 8.5.** The map phi: U(n_-) -> M_lambda given by phi(x) = x v_lambda is an isomorphism of left U(n_-)-modules.

**Corollary 8.7.** M_lambda has a weight decomposition with P(M_lambda) = lambda - Q_+, dim M_lambda[lambda] = 1, and weight subspaces of M_lambda are finite-dimensional.

**Proposition 8.8.** (i) If V is a representation of g and v in V is a vector such that hv = lambda(h)v for h in h and e_i v = 0 then there is a unique homomorphism eta: M_lambda -> V such that eta(v_lambda) = v. In particular, if V is generated by such v != 0 then V is a quotient of M_lambda.

**Proposition 8.9.** For every lambda in h^*, the Verma module M_lambda has a unique irreducible quotient L_lambda. Moreover, L_lambda is a quotient of every highest weight g-module V with highest weight lambda.

**Corollary 8.10.** Irreducible highest weight g-modules are classified by their highest weight lambda in h^*, via the bijection lambda -> L_lambda.

**Proposition 8.12.** L_lambda is finite-dimensional if and only if lambda in P_+.

## Section 9: Representations of SL_2(R)

**Proposition 9.1.** The simple (g, K)-modules (or equivalently, Harish-Chandra modules) for SL_2(R) are L_m (m >= 0), M_m^- and M_{-m}^+ (m >= 1), and P_+(s) (s not in 2Z+1), P_-(s) (s not in 2Z), with the only isomorphisms P_pm(s) = P_pm(-s).

**Theorem 9.3.** (Gelfand-Naimark, Bargmann) The irreducible unitary representations of SL_2(R) are Hilbert space completions of the following unitary Harish-Chandra modules: discrete series and limit of discrete series M_m^-, M_{-m}^+ (m >= 1); unitary principal series P_pm(s) (s in iR, s != 0); complementary series P_+(s) (s in R, 0 < |s| < 1); the trivial representation C.

## Section 10: Chevalley restriction theorem and Chevalley-Shephard-Todd theorem

**Theorem 10.1.** (Chevalley restriction theorem) (i) Res(F) in C[h]^W. (ii) The map Res: C[g]^g -> C[h]^W is a graded algebra isomorphism.

**Theorem 10.6.** (Chevalley-Shephard-Todd theorem, part I) Let V be a finite-dimensional complex vector space and G subset GL(V) be a finite subgroup. Then C[V]^G is a polynomial algebra if and only if G is a complex reflection group.

## Section 11: Proof of the CST theorem, part I

**Lemma 11.1.** The algebra C[V]^G is generated by f_1, ..., f_r; in particular, it is finitely generated.

**Lemma 11.3.** Assume that G is a complex reflection group. Let I be as above, F_1, ..., F_m in C[V]^G be homogeneous, and suppose that F_1 does not belong to the ideal in C[V]^G generated by F_2, ..., F_m. Suppose g_i in C[V] for 1 <= i <= m are homogeneous and sum g_i F_i = 0. Then g_1 in I.

**Lemma 11.4.** f_1, ..., f_r are algebraically independent.

**Lemma 11.6.** Let U be an affine space over C and G a finite group acting on U by polynomial automorphisms. (i) Let u in U be a point with trivial stabilizer in G. Then there exists a local coordinate system on U near u consisting of elements of C[U]^G. (ii) Maximal ideals in C[U]^G are in bijection with G-orbits on U.

## Section 12: Chevalley-Shephard-Todd theorem, part II

**Proposition 12.1.** (Hilbert-Noether theorem) (i) A is integral over A^G. In particular, if A is finitely generated then it is module-finite over A^G. (ii) If R is Noetherian and A is finitely generated then so is A^G.

**Theorem 12.2.** (Chevalley-Shephard-Todd theorem, part II) If G is a complex reflection group then for any irreducible representation rho of G, the C[V]^G-module Hom_G(rho, C[V]) is free of rank dim rho. Thus the G-module R_0 = C[x_1,...,x_n]/(f_1,...,f_n) is the regular representation and prod d_i = |G|.

**Lemma 12.3.** (i) Any homogeneous lift {v_i^*} of a homogeneous basis {v_i} of M_0 to M is a system of generators for M; in particular, if dim M_0 < infty then M is finitely generated. (ii) If in addition M is projective, then {v_i^*} is actually a basis of M.

**Proposition 12.4.** If i > n then for any k[x_1,...,x_n]-modules M, N, one has Ext^i(M, N) = 0.

**Theorem 12.5.** (Hilbert syzygies theorem) H(M, q) = p(q) / (1-q)^n, where p is a polynomial with integer coefficients.

**Lemma 12.6.** Let f in m. Then dim_m(R/f) >= dim_m R - 1.

**Corollary 12.7.** Let f_1,...,f_m in k[x_1,...,x_n] be homogeneous polynomials of positive degrees. Let Z be an irreducible component of the zero set Z(f_1,...,f_m) subset k^n. Then dim_{m_0} k[Z] >= n - m.

**Lemma 12.8.** If f_1,...,f_n in R is a regular sequence then the complex K_R(f_1,...,f_n) is exact in negative degrees.

**Proposition 12.9.** Suppose f_1,...,f_n in R := k[x_1,...,x_n] are homogeneous polynomials of positive degree such that the zero set Z(f_1,...,f_n) consists of the origin. Then f_1,...,f_n is a regular sequence.

**Proposition 12.10.** Suppose f_1,...,f_n in R := k[x_1,...,x_n] are homogeneous polynomials of degrees d_1,...,d_n > 0 such that R is a finitely generated module over S := k[f_1,...,f_n]. Then this module is free of rank prod d_i.

## Section 13: Kostant's theorem

**Theorem 13.1.** (Kostant) Sg is a free (Sg)^g-module. Moreover, for every finite-dimensional irreducible representation V of g, the space Hom_g(V, Sg) is a free (Sg)^g module of rank dim V[0].

**Lemma 13.2.** As q -> 1 in (0,1), the function F_q(x) := prod_{alpha in R_+} (1 - e^{i alpha(x)})/(1 - q e^{i alpha(x)}) goes to 1 in L^2(h/Q^vee).

**Theorem 13.3.** (Kostant) For lambda in P_+ we have an explicit formula for H(Hom_g(L_lambda^*, (Sg)_0), q) in terms of roots and degrees.

**Corollary 13.4.** (1/|W|) CT(prod_{alpha in R} (1-e^alpha)/(1-qe^alpha)) = 1/(prod [d_i]_q).

**Theorem 13.5.** (Kostant) (i) The center Z(g) = U(g)^g of U(g) is a polynomial algebra in r generators C_i of PBW filtration degrees d_i. (ii) U(g) is a free module over Z(g), and for every irreducible finite-dimensional representation V of g, the space Hom_g(V, U(g)) is a free Z(g)-module of rank dim V[0].

## Section 14: Harish-Chandra isomorphism, maximal quotients

**Theorem 14.1.** (Harish-Chandra) (i) The restriction of HC to Z(g) is an algebra homomorphism. (ii) HC maps Z(g) into C[h^*]^{W bullet}. (iii) HC(b)(lambda) is the scalar by which b acts on a highest weight module with highest weight lambda. (iv) gr(HC) = Res. (v) HC is an algebra isomorphism.

**Corollary 14.3.** For any finite-dimensional irreducible g-module V we have dim Hom_g(V, U_chi) = dim V[0]. Thus U_chi is a Harish-Chandra g-bimodule.

**Corollary 14.4.** If V is a finite-dimensional g-bimodule then V tensor U_chi is a Harish-Chandra g-bimodule.

**Corollary 14.5.** (i) Every irreducible g-bimodule M locally finite under the adjoint g-action is a quotient of V tensor U_chi for some finite-dimensional irreducible g-module V. (ii) Every irreducible g-bimodule locally finite under the adjoint g-action is a Harish-Chandra bimodule.

## Section 15: Category O of g-modules - I

**Lemma 15.3.** If M in O then the weight subspaces of M are finite-dimensional.

**Corollary 15.4.** The action of Z(g) on every M in O factors through a finite-dimensional quotient.

**Corollary 15.7.** (i) Any M in O has a canonical decomposition M = bigoplus_chi M(chi), where M(chi) is the generalized eigenspace of Z(g) in M with eigenvalue chi. In other words, O = bigoplus O_chi. (ii) Each M in O_chi has a finite filtration with successive quotients having infinitesimal character chi.

**Lemma 15.9.** Every object of O has finite length.

**Theorem 15.11.** (D. N. Verma) Let lambda, mu in h^* and mu preceq lambda. Then dim Hom(M_{mu-rho}, M_{lambda-rho}) = 1 and M_{mu-rho} can be uniquely realized as a submodule of M_{lambda-rho}. In particular, L_{mu-rho} occurs in the composition series of M_{lambda-rho}.

**Proposition 15.12.** W_x is generated by the reflections s_alpha in W_x. Moreover, the roots alpha such that s_alpha in W_x form a root system R_x subset R, and W_x is the Weyl group of R_x.

## Section 16: Category O of g-modules - II

**Corollary 16.1.** The following conditions on a weight lambda in h^* are equivalent: (i) lambda is dominant for preceq; (ii) lambda is dominant for <=; (iii) For every root alpha in R_+, (lambda, alpha^vee) not in Z_{<0}; (iv) For every w in W_{lambda+Q}, w*lambda <= lambda; (v) For every w in W_{lambda+Q}, w*lambda preceq lambda.

**Proposition 16.2.** Let C be a Noetherian abelian category with enough projectives and finite-dimensional Hom spaces over an algebraically closed field k. Then (i) indecomposable projectives P_i are in bijection with simple objects L_i, and dim Hom(P_i, L_j) = delta_{ij}. (ii) For M of finite length, [M : L_i] = dim Hom(P_i, M).

**Proposition 16.4.** If lambda is dominant then M_{lambda-rho} is a projective object in O.

**Corollary 16.5.** (i) If P in O is projective then so is V tensor P. (ii) If lambda is dominant then V tensor M_{lambda-rho} is projective in O.

**Corollary 16.6.** (i) For every mu, there exists dominant lambda and a finite-dimensional g-module V such that Hom(V tensor M_{lambda-rho}, L_mu) != 0. Thus O has enough projectives. (ii) Every projective object P of O is a free U(n_-)-module.

## Section 17: The nilpotent cone of g

**Lemma 17.1.** The restriction of the adjoint representation of g to its principal sl_2-subalgebra is isomorphic to L_{2m_1} + ... + L_{2m_r} for appropriate m_i in Z_{>0}.

**Lemma 17.2.** The element e = sum e_i is regular.

**Corollary 17.3.** Ad(B_+)e is the set of elements sum c_alpha e_alpha with c_alpha in C and c_{alpha_i} != 0 for all i.

**Proposition 17.4.** The nilpotent cone is reduced.

**Proposition 17.6.** (i) The orbit O_e := Ad(G)e is open and dense in N. (ii) All regular nilpotent elements in g are conjugate to e. (iii) N is an irreducible affine variety. Thus (Sg)_0 is an integral domain.

**Corollary 17.7.** U_chi is an integral domain for all chi.

## Section 18: Maps of finite type, Duflo-Joseph theorem

**Proposition 18.2.** If M, N in O then Hom_{fin}(M, N) is an admissible g-bimodule.

**Proposition 18.3.** For M, N in O and a finite-dimensional g-module V we have Hom_{fin}(M, V tensor N) = V tensor Hom_{fin}(M, N).

**Proposition 18.5.** Let V be a finite-dimensional g-module. Then for any lambda in h^*, dim Hom_g(M_lambda, V tensor M_lambda) = dim V[0]. Thus the multiplicity of V in Hom_{fin}(M_lambda, M_lambda) equals dim V[0].

**Proposition 18.7.** The action homomorphism phi: U_{chi_{lambda+rho}} -> Hom_{fin}(M_lambda, M_lambda) is injective.

**Corollary 18.8.** (The Duflo-Joseph theorem) phi is an isomorphism.

**Corollary 18.9.** If V is a finite-dimensional g-module then the natural map V tensor U_{chi_{lambda+rho}} -> Hom_{fin}(M_lambda, V tensor M_lambda) is an isomorphism.

**Corollary 18.10.** Let V be a finite-dimensional g-module and lambda in h^*. (i) The left infinitesimal characters occurring in V tensor U_{chi_lambda} are chi_{lambda+nu} where nu runs over weights of V. (ii) If M has infinitesimal character chi_lambda then the infinitesimal characters occurring in V tensor M are among chi_{lambda+nu}. (iii) If M is a nonzero Harish-Chandra bimodule with infinitesimal character (chi_lambda, chi_mu) then there is w in W such that w*lambda - mu in P.

**Corollary 18.11.** The category HC(g) has a decomposition according to generalized infinitesimal characters: HC(g) = bigoplus_{gamma,lambda} HC_{chi_{lambda+gamma}, chi_lambda}(g).

## Section 19: Principal series representations

**Proposition 19.1.** The homomorphism phi: U(g) -> prod_{lambda in P_+} End(L_lambda) is injective.

**Proposition 19.3.** Let X in HC(g). Then Hom_{g-bimod}(X, M(lambda, mu)) = Hom_{(b_-, b_+)-bimod}(X tensor C_{lambda-rho}, C_{mu-rho}).

**Proposition 19.4.** The right action of g on M(lambda, mu) is given by the formula involving Casimir elements and weight components.

**Proposition 19.5.** We have an isomorphism of M(lambda, mu) with M(lambda', mu') when lambda - lambda' in P, mu - mu' in P, with the same infinitesimal characters.

**Proposition 19.7.** The functor H_lambda is exact when lambda is dominant.

## Section 20: BGG reciprocity and BGG Theorem

**Lemma 20.1.** Let X in O be a free U(n_-)-module. Then for any mu in h^* we have Ext^i_O(X, M_mu^vee) = 0 for i > 0. In other words, a standardly filtered X has a unique standard filtration.

**Corollary 20.2.** If X is standardly filtered then Ext^i_O(X, M_mu^vee) = 0 for all mu in h^* and i > 0.

**Theorem 20.3.** X is standardly filtered if and only if Ext^1_O(X, M_mu^vee) = 0 for all mu in h^*.

**Lemma 20.4.** If Ext^1_O(Z, M_mu^vee) = 0 for all mu in h^* then K = 0 and Z = E tensor M_lambda.

**Corollary 20.5.** (i) Every X in O which is a free U(n_-)-module is standardly filtered. In particular, for any lambda and finite-dimensional V, the module V tensor M_lambda is standardly filtered. (ii) Every indecomposable projective P_lambda is standardly filtered.

**Theorem 20.6.** (BGG reciprocity) d^*_{lambda,mu} = d_{mu,lambda}.

**Corollary 20.7.** We have [P_lambda : L_mu] = [M_mu : L_lambda] (in the Grothendieck group).

**Proposition 20.9.** (i) X^vee in O and has the same character and composition series as X. (ii) The duality functor is exact and contravariant.

**Corollary 20.10.** O has enough injectives, namely the injective hull of L_lambda is P_lambda^vee.

**Theorem 20.13.** (Bernstein-Gelfand-Gelfand) If L_{mu-rho} occurs in the composition series of M_{lambda-rho} (i.e., d_{lambda-rho,mu-rho} != 0) then mu preceq lambda.

**Corollary 20.14.** The following conditions on mu preceq lambda are equivalent: (1) L_{mu-rho} occurs in the composition series of M_{lambda-rho}; (2) M_{mu-rho} embeds in M_{lambda-rho}; (3) mu preceq lambda.

## Section 21: Kazhdan-Lusztig theory

**Proposition 21.1.** T_w, w in W are linearly independent, so they form a basis of H_q(W). Thus H_q(W) is a free Z[q^{1/2}, q^{-1/2}]-module of rank |W|.

**Theorem 21.5.** There exist unique polynomials P_{y,w} in Z[q] (the Kazhdan-Lusztig polynomials) such that C'_w = sum_{y <= w} P_{y,w}(q) T_y, with P_{w,w} = 1 and deg P_{y,w} <= (l(w) - l(y) - 1)/2 for y < w.

**Theorem 21.6.** (Kazhdan-Lusztig conjecture, proved by Beilinson-Bernstein and Brylinski-Kashiwara) (i) P_{y,w} has non-negative coefficients. (ii) The multiplicity [M_{y bullet lambda} : L_{w bullet lambda}] equals P_{y,w}(1).

## Section 22: Projective functors

**Theorem 22.4.** Let F_1, F_2 be projective theta-functors for theta = chi_lambda. Let i_lambda: Hom(F_1, F_2) -> Hom(F_1(M_{lambda-rho}), F_2(M_{lambda-rho})) be the evaluation map at M_{lambda-rho}. Then i_lambda is an isomorphism.

**Proposition 22.5.** (i) If F_1, F_2 are projective functors then every morphism phi: F_1(theta) -> F_2(theta) lifts to a morphism hat{phi}: F_1|_{Rep(g)_theta} -> F_2|_{Rep(g)_theta}. (ii) The lift is unique.

**Corollary 22.6.** (i) Any isomorphism F_1(M_{lambda-rho}) = F_2(M_{lambda-rho}) lifts to an isomorphism F_1 = F_2 on Rep(g)_theta. (ii) Any decomposition F(M_{lambda-rho}) = M_1 + ... + M_r lifts to a decomposition F = F_1 + ... + F_r.

**Proposition 22.7.** (i) Each projective functor F is a direct sum of indecomposable projective functors. Moreover, for F circ Pi_theta this sum is finite. (ii) The map [F] -> [F](theta) defines a bijection between isomorphism classes of indecomposable projective theta-functors and indecomposable projective objects in O_theta.

## Section 23: Classification of projective functors

**Theorem 23.1.** (i) If F_1, F_2 are projective functors with [F_1] = [F_2] then F_1 = F_2. (ii) Projective functors are in bijection with elements of (ZP)^W via [F].

**Theorem 23.2.** If F is a projective functor then [F] commutes with W on K(O).

**Lemma 23.3.** When lambda dominates chi then [F circ Pi_{chi_lambda}] on K(O_{chi_lambda}) is determined by [F](M_{lambda-rho}).

**Lemma 23.4.** Let lambda be dominant and phi, psi in lambda + P with psi <= phi. Then (lambda - phi)^2 <= (lambda - psi)^2, and if (lambda - phi)^2 = (lambda - psi)^2 then psi in W_lambda * phi.

**Theorem 23.6.** For any xi in Xi there exists an indecomposable projective functor F_xi such that F_xi(M_{nu-rho}) = 0 if chi_nu != chi_lambda and F_xi(M_{lambda-rho}) = P_{mu-rho} for any proper representation (mu, lambda) of xi. The assignment xi -> F_xi is a bijection between Xi and indecomposable projective functors.

**Lemma 23.7.** In this case S_*(F) = xi := W(mu, lambda) and (mu, lambda) is a proper representation of xi.

## Section 24: Translation functors

**Theorem 24.1.** If W_lambda = W_mu and V has extremal weight mu - lambda then F_{chi,V,theta}: Rep(g)_theta -> Rep(g)_chi is an equivalence of categories. A quasi-inverse equivalence is given by F_{theta,V^*,chi}.

**Theorem 24.4.** (i) I subset J iff nu(I) subset nu(J). In particular, nu is injective. (ii) nu is surjective. So two-sided ideals in U_theta are in bijection with W_{lambda}-invariant subsets of W/W_lambda via nu.

**Corollary 24.5.** Let theta = chi_lambda where lambda is dominant. If M_{lambda-rho} is irreducible then U_theta is a simple algebra. Conversely, if U_theta is simple then M_{mu-rho} is irreducible for all mu with chi_mu = theta.

## Section 25: Harish-Chandra bimodules

**Theorem 25.4.** (Duflo's theorem) Every prime ideal J subset U_theta is primitive and moreover is the annihilator of a simple highest weight module L_{mu-rho}, where chi_mu = theta.

**Lemma 25.5.** The abelian category HC^1_theta has enough projectives.

**Theorem 25.6.** The simples (and indecomposable projectives) in HC^1_theta are labeled by the set Xi, via xi -> L_xi, P_xi.

**Corollary 25.7.** Objects in HC^1_theta, hence in HC_theta and HC, have finite length.

**Theorem 25.8.** (J. Bernstein-S. Gelfand) (i) If lambda is a regular weight then the functor T_lambda is an equivalence of categories HC^1_theta -> O_{chi_lambda}, with quasi-inverse H_lambda. (ii) For general dominant lambda, the functors T_lambda and H_lambda are adjoint pairs.

**Proposition 25.10.** T_lambda is fully faithful on the subcategory of HC^1_theta consisting of modules whose support contains the open orbit.

**Corollary 25.11.** Every Harish-Chandra bimodule M with right infinitesimal character theta is realizable as V^{fin} where V is a (not necessarily unitary) admissible representation of the complex simply connected group G corresponding to g on a Hilbert space.

## Section 26: Representations of SL_2(C)

**Proposition 26.1.** (i) The principal series bimodule M(lambda, mu) is irreducible and isomorphic to M(-lambda, -mu) unless lambda, mu are nonzero integers of the same sign. Otherwise such bimodules are pairwise non-isomorphic. (ii)-(iv) Full classification of HC bimodules for sl_2.

**Theorem 26.3.** (Gelfand-Naimark) The irreducible unitary representations of SL_2(C) are Hilbert space completions of the following unitary Harish-Chandra modules: Finite-dimensional modules L_m (m >= 0); Unitary principal series P_+(s) tensor L_n with s in iR, n in Z_+; The trivial representation.

## Section 27: Geometry of complex semisimple Lie groups

**Theorem 27.3.** (Borel-Weil) Let lambda in P. If lambda in P_+ then H^0(F, L_lambda) = L_lambda^* as G-modules. Otherwise, H^0(F, L_lambda) = 0.

**Corollary 27.5.** Let lambda in P with (lambda, alpha_i^vee) = 0, i in S. Then H^0(G/P_S, L_{lambda,S}) = L_lambda^* if lambda in P_+ and 0 otherwise.

**Theorem 27.8.** The Springer map p is birational and projective, so it is a resolution of singularities.

**Theorem 27.11.** (Kirillov-Kostant) Let G be a connected real or complex Lie group or complex algebraic group. Then every G-orbit in g^* has a natural symplectic structure.

**Corollary 27.12.** The singular locus of the nilpotent cone N has codimension >= 2.

**Corollary 27.13.** N is normal (i.e., the algebra O(N) is integrally closed in its quotient field).

**Proposition 27.14.** Let Y be an irreducible normal algebraic variety. Then (i) O(Y) is integrally closed. (ii) A rational function regular in codimension 1 is regular.

**Proposition 27.15.** Let Y be an irreducible normal affine algebraic variety and p: X -> Y be a resolution of singularities. Then the homomorphism p^*: O(Y) -> O(X) is an isomorphism.

**Theorem 27.16.** Let p: T^*F -> N be the Springer resolution. Then the map p^*: O(N) -> O(T^*F) is an isomorphism of graded algebras.

## Section 28: D-modules

**Proposition 28.9.** A left D_X-module is the same thing as an O_X-module with a flat connection.

## Section 29: Beilinson-Bernstein localization

**Theorem 29.1.** (Beilinson-Bernstein) (i) The homomorphism a: U(g) -> D(F) factors through a_0: U_0 -> D(F). (ii) gr(a_0) = p^* where p is the Springer map. (iii) grD(F) = O(T^*F) and a_0 is an isomorphism.

**Theorem 29.2.** (Beilinson-Bernstein localization theorem) The functors Gamma and Loc are mutually inverse equivalences. Thus the category U_0-mod is canonically equivalent to the category of D-modules on the flag variety F.

**Corollary 29.4.** Partial flag varieties of semisimple algebraic groups are D-affine.

**Theorem 29.6.** (Beilinson-Bernstein) (i) The map a_lambda: U_lambda -> D_lambda(F) is an isomorphism for antidominant lambda. (ii) H^i(F, M) = 0 for i > 0 when M is a D_lambda-module and lambda is antidominant.

**Theorem 29.7.** (Beilinson-Bernstein localization theorem) If lambda is antidominant then the functors Gamma and Loc are mutually inverse equivalences. Thus U_lambda-mod is equivalent to the category of D_lambda-modules on F.

## Section 30: D-modules on algebraic varieties

**Proposition 30.2.** The support of an irreducible D-module is irreducible.

**Theorem 30.4.** (Kashiwara) The functor i^dagger is an equivalence of categories M_Z(X) -> M(Z).

**Proposition 30.18.** Assume that X is a D-affine variety and K an affine algebraic group acting on X. Let D(X) be the ring of global sections. Then the category of K-equivariant D_X-modules is equivalent to the category of D(X)-modules M endowed with a locally finite K-action whose differential coincides with the action of Lie(K) on M.

**Corollary 30.20.** If lambda is antidominant then the functors Gamma, Loc restrict to mutually inverse equivalences between the category of (g, K)-modules with infinitesimal character chi_{lambda-rho} and the category of K-equivariant D_lambda-modules on F.

## Section 31: Classification of irreducible (g, K)-modules

**Theorem 31.1.** Let X be a smooth variety and K a connected algebraic group acting on X with finitely many orbits. Then there are finitely many irreducible K-equivariant D-modules on X, parametrized by pairs (O, V) where O is an orbit of K and V is an irreducible representation of the component group of the stabilizer H := K_x for x in O.

**Proposition 31.3.** The group K acts on F with finitely many orbits.

**Theorem 31.4.** Irreducible (g, K)-modules with (pure) infinitesimal character chi are pi(O, V) where O is a K-orbit on F and V an irreducible representation of K_x, x in O such that Lie(K_x) acts via the character lambda_x. Namely, pi(O, V) corresponds to M(O, V) under the Beilinson-Bernstein equivalence.
