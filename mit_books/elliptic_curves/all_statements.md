Theorem 1.2 [Baker's Theorem]:
For an irreducible polynomial f(x,y), the genus g(F) of the corresponding function field is at most the number of interior lattice points of the Newton polygon of f.

Proposition 1.5:
For an irreducible nondegenerate polynomial f(x,y) whose homogenization has no singularities outside {(0:0:1),(0:1:0),(1:0:0)}, the genus equals the number of interior lattice points of the Newton polygon.

Theorem 3.3:
The ring F_p is a field, and every field of characteristic p contains a canonical subfield isomorphic to F_p. All fields of cardinality p are isomorphic.

Theorem 3.6:
The field F_q has cardinality q and every field of cardinality q is (non-canonically) isomorphic to F_q.

Theorem 3.8:
The finite field F_{p^m} is a subfield of F_{p^n} if and only if m divides n.

Theorem 3.9:
For any irreducible f in F_p[x] of degree n > 0, F_p[x]/(f) is isomorphic to F_{p^n}.

Corollary 3.10:
Every irreducible f in F_p[x] of degree n splits completely in F_{p^n}.

Theorem 3.12:
Every finite subgroup of the multiplicative group of a field is cyclic.

Corollary 3.13:
The multiplicative group of a finite field is cyclic.

Theorem 3.15:
For every prime p and positive integer n there exist primitive polynomials of degree n in F_p[x]. The number of such polynomials is phi(p^n - 1)/n.

Lemma 3.20:
An irreducible polynomial f in k[x] is inseparable if and only if f' = 0.

Theorem 3.22:
Finite fields are perfect (every irreducible polynomial in F_q[x] is separable).

Theorem 3.24:
The time to add or subtract two elements of F_q is O(n), where n = lg q.

Theorem 3.29:
DFT_omega(f * g) = DFT_omega(f) . DFT_omega(g) (convolution theorem for DFT).

Theorem 3.30:
The FFT algorithm correctly outputs DFT_omega(f).

Corollary 3.31:
Given a commutative ring R with a primitive nth root of unity (n = 2^k) and 2 invertible, one can multiply two polynomials of degree less than n/2 using O(n log n) operations in R.

Theorem 3.33:
The time to multiply two elements of F_p is O(M(n)), where n = lg p.

Theorem 3.35:
The time to multiply two elements of F_q is O(M(n)) = O(n log n), where n = lg q (assuming log e = O(log p)).

Theorem 3.38:
The long division algorithm uses O(mn) bit operations for Euclidean division of an m-bit integer by an n-bit integer.

Theorem 3.40:
The time to invert an element of F_p^x is O(M(n) log n), where n = lg p.

Theorem 3.41:
The time to invert an element of F_q^x is O(M(n) log n) = O(n log^2 n), where n = lg q.

Theorem 3.44 [Rabin 1980]:
For every pair of distinct alpha, beta in F_q, the number of delta in F_q such that alpha + delta and beta + delta are of different type is (q-1)/2.

Theorem 4.15:
If C_1 is a smooth projective curve then every rational map from C_1 to a projective curve C_2 is a morphism.

Theorem 4.17:
A morphism of projective curves is either surjective or constant.

Lemma 4.26:
An isogeny alpha: E_1 -> E_2 between elliptic curves y^2 = f(x) can be written in standard form alpha(x,y) = (u(x)/v(x), s(x)/t(x) * y) with u coprime to v and s coprime to t.

Lemma 4.27:
For an isogeny in standard form, v^3 divides t^2 and t^2 divides v^3 * f_1. Moreover, v(x) and t(x) have the same set of roots.

Corollary 4.28:
The affine points in the kernel of an isogeny in standard form are precisely those for which v(x_0) = 0.

Corollary 4.29:
The kernel of an isogeny of elliptic curves is a finite subgroup of E_1(k-bar).

Theorem 4.34:
Every transcendence basis for L/k has the same cardinality.

Theorem 4.45 [Hilbert Basis Theorem]:
If R is a noetherian ring, then so is R[x].

Lemma 4.48:
For any ideal I in a commutative ring R, the radical sqrt(I) is an ideal.

Theorem 4.49 [Hilbert's Nullstellensatz]:
For every ideal I in k-bar[x_1,...,x_n], we have I(Z_I) = sqrt(I).

Theorem 4.50 [Weak Nullstellensatz]:
For any proper ideal I of k-bar[x_1,...,x_n], the variety Z_I is nonempty.

Corollary 4.51:
The maximal ideals of k-bar[x_1,...,x_n] are all of the form m_P = (x_1 - P_1,...,x_n - P_n) for some point P in A^n(k-bar).

Corollary 4.52:
There is a one-to-one inclusion-reversing correspondence between radical ideals of k-bar[x_1,...,x_n] and algebraic sets in A^n(k-bar).

Theorem 4.55:
An algebraic set is irreducible if and only if its ideal is prime.

Lemma 5.1:
For relatively prime polynomials u,v in k[x], (u/v)' = 0 iff u' = v' = 0 iff u = f(x^p) and v = g(x^p) for some polynomials f,g, where p = char(k).

Corollary 5.2:
Over a field of characteristic zero, every isogeny is separable.

Lemma 5.3:
An inseparable isogeny of elliptic curves y^2 = f(x) over a field of characteristic p > 0 can be written as (a(x^p), b(x^p)y^p) for some rational functions a, b.

Corollary 5.4:
Any isogeny alpha of elliptic curves over a field of characteristic p > 0 can be decomposed as alpha = alpha_sep o pi^n for a separable isogeny alpha_sep and integer n >= 0, where pi is the p-power Frobenius. Moreover, deg alpha = p^n * deg alpha_sep.

Theorem 5.8:
The order of the kernel of an isogeny equals its separable degree.

Corollary 5.9:
Every purely inseparable isogeny has trivial kernel.

Corollary 5.10:
For any composition of isogenies alpha = beta o gamma, the degree, separable degree, and inseparable degree are each multiplicative.

Theorem 5.11:
Let E/k be an elliptic curve and G a finite subgroup of E(k-bar). There exists an elliptic curve E' and a separable isogeny phi: E -> E' with ker phi = G. The curve E' and isogeny phi are defined over a finite extension of k and unique up to isomorphism.

Corollary 5.12:
An isogeny of composite degree can always be decomposed into a sequence of isogenies of prime degree.

Theorem 5.13 [Velu]:
Explicit formulas for a separable isogeny of degree 2 from E: y^2 = x^3+Ax+B with kernel generated by a 2-torsion point (x_0,0), giving E': y^2 = x^3+A'x+B' where A' = A-5t, B' = B-7w, with t = 3x_0^2+A, w = x_0*t.

Theorem 5.15 [Velu]:
Explicit formulas for a separable isogeny of odd degree from E: y^2 = x^3+Ax+B with a finite kernel G of odd order, given by phi(x,y) = (r(x), r'(x)y), with E': y^2 = x^3+A'x+B' where A' = A-5t, B' = B-7w.

Lemma 5.20:
For every integer n, psi_n lies in Z[x,A,B] for n odd and 2y*Z[x,A,B] for n even; phi_n lies in Z[x,A,B]; omega_n lies in Z[x,A,B] for n even and y*Z[x,A,B] for n odd.

Theorem 5.21:
The multiplication-by-n map [n] on E: y^2 = x^3+Ax+B is given by [n](x,y) = (phi_n(x)/psi_n^2(x), omega_n(x,y)/psi_n^3(x,y)) using division polynomials.

Lemma 5.22:
For every positive integer n, phi_n(x) = x^{n^2} + ... and psi_n has leading term nx^{(n^2-1)/2} (n odd) or y(nx^{(n^2-4)/2}) (n even).

Corollary 5.23:
For all positive integers n, psi_n^2(x) = n^2 x^{n^2-1} + lower order terms.

Lemma 5.24:
For any elliptic curve E: y^2 = x^3+Ax+B, the polynomials phi_n(x) and psi_n^2(x) are relatively prime.

Theorem 5.25:
The multiplication-by-n map [n]: E -> E has degree n^2. It is separable if and only if n is not divisible by the characteristic of k.

Theorem 6.1:
For an elliptic curve E/k with char(k) = p and each prime l: E[l^e] is isomorphic to (Z/l^e Z)^2 if l != p, and to Z/l^e Z or {0} if l = p.

Corollary 6.4:
Every finite subgroup of E(k-bar) is the direct sum of two (possibly trivial) cyclic groups. Over F_q, E(F_q) = Z/mZ + Z/nZ with m|n and p does not divide m.

Proposition 6.5:
For all n in Z and alpha in Hom(E_1,E_2), [n] o alpha = n*alpha = alpha o [n].

Lemma 6.6:
Isogenies can be cancelled on either side of an equality of compositions: delta o alpha = delta o beta implies alpha = beta, and alpha o gamma = beta o gamma implies alpha = beta.

Theorem 6.7 [Dual Isogeny]:
For any isogeny alpha: E_1 -> E_2 of degree n, there exists a unique isogeny alpha-hat: E_2 -> E_1 such that alpha-hat o alpha = [n].

Lemma 6.10:
For an isogeny alpha of degree n, alpha o alpha-hat = [n] (so alpha-hat-hat = alpha). The multiplication-by-n map [n] is self-dual.

Lemma 6.11:
For any alpha, beta in Hom(E_1,E_2), the dual of (alpha+beta) equals alpha-hat + beta-hat.

Lemma 6.12:
For any alpha in Hom(E_2,E_3) and beta in Hom(E_1,E_2), the dual of (alpha o beta) equals beta-hat o alpha-hat.

Lemma 6.16:
For any endomorphism alpha, alpha + alpha-hat = 1 + deg(alpha) - deg(1-alpha), which is an integer.

Theorem 6.18:
Any endomorphism alpha and its dual alpha-hat satisfy the characteristic equation lambda^2 - (tr alpha)*lambda + deg alpha = 0.

Lemma 6.19:
If endomorphisms alpha and beta have maximum degree m, n >= 2*sqrt(m)+1 is prime to char(k) and to deg(alpha) and deg(beta), and alpha_n = beta_n, then alpha = beta.

Theorem 6.20:
For any endomorphism alpha and positive integer n prime to char(k): tr(alpha) = tr(alpha_n) mod n and deg(alpha) = det(alpha_n) mod n.

Lemma 7.1:
If alpha is inseparable and beta is any isogeny, then alpha + beta is inseparable if and only if beta is inseparable.

Theorem 7.3 [Hasse]:
For an elliptic curve E/F_q, #E(F_q) = q+1-t where t = tr(pi_E) is the trace of the Frobenius endomorphism and |t| <= 2*sqrt(q).

Theorem 7.6:
For a finite abelian group G with exponent lambda(G), if alpha and beta are uniformly random elements, then Pr[lcm(|alpha|,|beta|) = lambda(G)] > 6/pi^2.

Theorem 7.7 [Mestre]:
For p > 229 prime and E/F_p an elliptic curve with quadratic twist E-tilde, at least one of lambda(E(F_p)) and lambda(E-tilde(F_p)) has a unique multiple in the Hasse interval.

Lemma 8.2:
If P in E[l] is nonzero and pi_l^2(P) - c*pi_l(P) + q_l*P = 0 for some integer c, then c = t_l = tr(pi) mod l.

Theorem 9.3:
For a random function f: V -> V on a finite set V of cardinality N, the expected value of the collision parameter rho satisfies E[rho] ~ sqrt(pi*N/2) as N -> infinity.

Theorem 9.7 [Shoup]:
For a generic group algorithm making at most s - 4*ceil(lg N) calls to the black box, the probability of computing the discrete logarithm is less than s^2/(2p), where p is the largest prime factor of N.

Corollary 9.8:
Every deterministic generic algorithm for the DLP in a cyclic group of prime order N uses at least (sqrt(2)+o(1))*sqrt(N) group operations.

Corollary 9.9:
Every generic Monte Carlo algorithm for the DLP in a cyclic group of prime order N using o(sqrt(N)/log N) random group elements uses at least (1+o(1))*sqrt(N) group operations.

Corollary 9.10:
Every generic Las Vegas algorithm for the DLP in a cyclic group of prime order N using o(sqrt(N)/log N) random group elements uses at least (2*sqrt(2)/3+o(1))*sqrt(N) expected group operations.

Corollary 9.11:
Every generic Las Vegas algorithm for the DLP in a cyclic group of prime order N uses an expected Omega(sqrt(N)) group operations.

Theorem 10.6 [Canfield-Erdos-Pomerance]:
The asymptotic bound (1/x)*psi(x, x^{1/u}) = u^{-u+o(u)} holds uniformly as u, x -> infinity, provided u < (1-epsilon)*log(x)/log(log(x)).

Theorem 10.10:
If p,q are prime divisors of N and l_p, l_q are the largest prime divisors of p-1 and q-1 respectively, with l_p <= B and l_p < l_q, then the Pollard p-1 algorithm succeeds with probability at least 1 - 1/l_q.

Theorem 10.12:
Under conditions on the ECM algorithm (4a^3+27b^2 not divisible by N, |P_1| is l_1-smooth with l_1 <= B, |P_2| is not l_1-smooth), Algorithm 10.11 succeeds in finding a proper factor of N.

Theorem 10.14:
A Montgomery curve By^2 = x^3+Ax^2+x has either three rational points of order 2 or a rational point of order 4 (possibly both).

Theorem 10.15:
An elliptic curve y^2 = x^3+ax+b with a rational point of order 4 can be put in Montgomery form.

Theorem 11.2 [Fermat's Little Theorem]:
If N is prime, then a^N = a for all a in Z/NZ.

Theorem 11.4 [Alford-Granville-Pomerance]:
The set of Carmichael numbers is infinite.

Theorem 11.5:
A positive integer N is prime if and only if phi(N) = N-1.

Lemma 11.6:
For p = 2^s * t + 1 prime with t odd, and a nonzero mod p, exactly one of: (i) a^t = 1 mod p, or (ii) a^{2^i * t} = -1 mod p for some 0 <= i < s.

Theorem 11.8 [Monier-Rabin]:
For N an odd composite integer, the probability that a random a in [1,N-1] is a witness for N is at least 3/4.

Theorem 11.11 [Damgard-Landrock-Pomerance]:
For a random odd integer N in [2^{k-1}, 2^k] and random a in [1,N-1], Pr[N is prime | a is not a witness for N] >= 1 - k^2 * 4^{2-sqrt(k)}.

Theorem 11.13 [Goldwasser-Kilian]:
Let E/Q be an elliptic curve with M, N > 1 integers with M > (N^{1/4}+1)^2 and N coprime to Delta(E). If MP is zero mod N and (M/l)P is strongly nonzero mod N for every prime l|M, then N is prime.

Lemma 12.5:
Let R be an integral domain with fraction field B, and A an R-algebra. Every element of A tensor_R B can be written as a pure tensor alpha tensor beta.

Lemma 12.7:
For all alpha in End^0(E), N(alpha) >= 0 with equality iff alpha = 0. Also N(alpha-hat) = N(alpha) and N(alpha*beta) = N(alpha)*N(beta).

Corollary 12.8:
Every nonzero alpha in End^0(E) has a multiplicative inverse.

Lemma 12.9:
For all alpha in End^0(E), T(alpha-hat) = T(alpha) in Q. The trace is Q-linear.

Lemma 12.10:
alpha and alpha-hat are roots of x^2 - (T alpha)x + N alpha in Q[x].

Corollary 12.11:
For nonzero alpha in End^0(E), if T(alpha) = 0 then alpha^2 = -N(alpha) < 0. An element is fixed by the Rosati involution iff it lies in Q.

Lemma 12.13:
A quaternion algebra is a division ring iff N(gamma) = 0 implies gamma = 0.

Theorem 12.17:
End^0(E) is isomorphic to one of: (i) Q, (ii) an imaginary quadratic field, or (iii) a quaternion algebra with alpha^2, beta^2 < 0.

Lemma 12.18:
If alpha, beta in End^0(E) commute and alpha is not in Q, then beta is in Q(alpha).

Corollary 12.20:
End(E) is a free Z-module of rank r where r = 1, 2, or 4 is dim_Q(End^0(E)).

Theorem 12.25:
The set of algebraic integers O_K in a number field K form a ring that is a free Z-module of rank [K:Q].

Theorem 12.26:
The ring of integers O_K of a number field K is its unique maximal order.

Theorem 12.27:
The orders in an imaginary quadratic field K are precisely the subrings Z + f*O_K for positive integers f.

Theorem 13.2:
Being supersingular (or ordinary) is an isogeny invariant.

Theorem 13.3:
An elliptic curve E/F_q is supersingular iff tr(pi_E) = 0 mod p.

Corollary 13.4:
For E/F_p with p > 3, E is supersingular iff tr(pi_E) = 0, iff #E(F_p) = p+1.

Theorem 13.6:
If pi_E is not in Z then End^0(E) = Q(pi_E) is an imaginary quadratic field with discriminant D = (tr pi_E)^2 - 4q. This applies when q is prime or E is ordinary.

Corollary 13.7:
If n is odd or E is ordinary, End^0(E) = Q(pi_E) is an imaginary quadratic field.

Theorem 13.8:
For E/F_q with End^0(E) an imaginary quadratic field K, we have Z[pi_E] subset End(E) subset O_K, and the conductor of End(E) divides [O_K : Z[pi_E]].

Theorem 13.12:
For every j_0 in k there is an elliptic curve E/k with j(E) = j_0.

Theorem 13.13:
Elliptic curves y^2 = x^3 + Ax + B and y^2 = x^3 + A'x + B' over k are isomorphic (over k) iff A' = mu^4 A and B' = mu^6 B for some mu in k*.

Theorem 13.14:
E and E' are isomorphic over k-bar iff j(E) = j(E'). If j(E) = j(E') with char(k) != 2,3, they are isomorphic over an extension of degree at most 6, 4, or 2.

Theorem 13.16:
If E is supersingular over a field of char p > 0, then j(E) lies in F_{p^2}.

Theorem 13.18:
If E is supersingular, then End^0(E_{k-bar}) is a quaternion algebra.

Theorem 13.19:
If End^0(E_{k-bar}) is a quaternion algebra, then E is supersingular.

Corollary 13.20:
Over finite fields: E is supersingular iff tr(pi_E) = 0 mod p iff End^0(E_{F_q-bar}) is a quaternion algebra; E is ordinary iff tr(pi_E) != 0 mod p iff End^0 is an imaginary quadratic field.

Theorem 14.13:
Fundamental theorem of calculus for contour integrals: integral of f along gamma equals F(gamma(b)) - F(gamma(a)) when F' = f.

Theorem 14.14 [Cauchy's Theorem]:
If f is holomorphic on an open set containing a closed curve gamma and its interior, then the contour integral is 0.

Theorem 14.16:
The contour integral of a meromorphic function equals 2*pi*i times the sum of residues inside the curve.

Theorem 14.17:
Generalization of Cauchy's argument principle relating contour integral of g(z)f'(z)/f(z) to sums of g(w)*ord_w(f).

Theorem 14.18:
A nonzero elliptic function has the same number of zeros as poles in any fundamental parallelogram.

Lemma 14.22:
The Eisenstein series sum converges absolutely for all k > 2.

Theorem 14.24:
Uniform limit of holomorphic functions on compact subsets is holomorphic.

Theorem 14.25:
The Weierstrass p-function is holomorphic at every point not in L.

Theorem 14.26:
Properties of wp(z) and wp'(z): wp is meromorphic even with double poles at L; wp' is meromorphic odd with triple poles at L.

Corollary 14.27:
wp(z) is an elliptic function of order 2 for L, and wp'(z) is of order 3.

Theorem 14.28:
Laurent series of wp(z) at z=0 is 1/z^2 + sum of (2n+1)*G_{2n+2}(L)*z^{2n}.

Theorem 14.29:
wp'(z)^2 = 4*wp(z)^3 - g_2(L)*wp(z) - g_3(L), where g_2 = 60*G_4, g_3 = 140*G_6.

Theorem 14.30 [Liouville's Theorem]:
Bounded entire functions are constant.

Lemma 14.31:
A point z not in L is a zero of wp'(z;L) iff 2z is in L.

Lemma 14.33:
For any lattice L, the discriminant Delta(L) is nonzero.

Theorem 15.1:
The map Phi: C/L -> E_L(C) defined by z -> (wp(z), wp'(z)) is a group isomorphism from the complex torus to the elliptic curve.

Theorem 15.5:
Two lattices L and L' are homothetic iff j(L) = j(L').

Corollary 15.6:
Two lattices are homothetic iff the corresponding elliptic curves E_L and E_{L'} are isomorphic over C.

Theorem 15.8:
The j-function is holomorphic on H, satisfies j(-1/tau) = j(tau) and j(tau+1) = j(tau).

Lemma 15.9:
j(tau) = j(tau') iff tau' = gamma*tau for some gamma in SL_2(Z).

Lemma 15.10:
The standard fundamental domain F is a fundamental domain for H/SL_2(Z).

Theorem 15.11:
The j-function restricted to F defines a bijection from F to C.

Corollary 15.12 [Uniformization Theorem]:
For every elliptic curve E/C there exists a lattice L such that E is isomorphic to E_L.

Theorem 16.1:
Every holomorphic map phi: C/L1 -> C/L2 with phi(0)=0 is of the form phi_alpha for a unique alpha in C with alpha*L1 subset L2.

Corollary 16.2:
The set {alpha in C : alpha*L1 subset L2} -> {morphisms C/L1 -> C/L2 sending 0 to 0} is an isomorphism of additive groups.

Lemma 16.3:
C(L) = C(wp, wp'), C(L)^even = C(wp), and every holomorphic even elliptic function is a polynomial in wp.

Theorem 16.4:
For lattices L1, L2 and alpha in C, the following are equivalent: alpha*L1 subset L2; there exist rational functions R,S with phi_alpha(wp_1,wp'_1) = (R(wp_1),S(wp_1)*wp'_1); the commutative diagram relating tori and elliptic curves commutes.

Corollary 16.5:
There is a ring isomorphism between {alpha : alpha*L subset L} and End(E), where the dual isogeny corresponds to complex conjugation.

Corollary 16.7:
End(E) over C is commutative, isomorphic to either Z or an order in an imaginary quadratic field.

Theorem 16.12:
There is a one-to-one correspondence between cl(O) and homothety classes of lattices with End isomorphic to O.

Lemma 17.5:
N(alpha) = |N_K/Q(alpha)| for principal ideals (alpha) of an imaginary quadratic order.

Corollary 17.7:
N(alpha*a) = N(alpha)*Na for nonzero alpha and ideal a.

Lemma 17.9:
a is proper iff lambda*a is proper for nonzero lambda; a is invertible iff lambda*a is invertible.

Theorem 17.10:
An O-ideal a is proper iff it is invertible. For an invertible ideal a, a*a-bar = (Na).

Corollary 17.11:
cl(O) is the group of invertible fractional O-ideals modulo principal ideals.

Corollary 17.12:
N(ab) = Na*Nb for proper ideals a, b.

Theorem 17.14:
ker(phi_a) = E[a] and deg(phi_a) = Na for a proper O-ideal a.

Corollary 17.15:
E and aE are related by an isogeny of degree Na.

Theorem 17.18:
There is a unique imaginary quadratic order O with disc(O) = D for each D = u^2*D_K.

Lemma 17.19:
Every index-n sublattice L' of L satisfies nL subset L', and nL is an index-n sublattice of every such L'.

Lemma 18.1:
For compact A, B subset H, the set {gamma in Gamma : gamma*A intersect B != empty} is finite.

Lemma 18.2:
For tau_1, tau_2 in H*, there exist neighborhoods U_1, U_2 such that gamma*U1 intersect U2 != empty iff gamma*tau_1 = tau_2.

Theorem 18.3:
X(1) = H*/Gamma(1) is a connected compact Hausdorff space.

Lemma 18.7:
The stabilizers of points in F* under SL_2(Z) are: trivial for generic points; order 2 generated by S at i; order 3 generated by ST at rho; trivial at cusps.

Lemma 18.8:
A holomorphic function fixing a point in the unit disk D with |f(z)| <= 1 is either the identity or rotation by a root of unity.

Theorem 18.9:
X(1) admits a complex structure making it a compact Riemann surface.

Theorem 18.10:
X(1) is a compact Riemann surface of genus 0.

Lemma 19.5:
The q-expansions of g_2, g_3, and Delta are: g_2 = (4pi^4/3)(1 + 240*sum), g_3 = (8pi^6/27)(1 - 504*sum), Delta = (2pi)^12 * q * prod(1-q^n)^24.

Corollary 19.6:
j(tau) = 1/q + 744 + sum a_n*q^n where all a_n are integers.

Theorem 19.8:
The field of modular functions C(Gamma(1)) equals C(j).

Lemma 19.9:
Every meromorphic function on the Riemann sphere is a rational function.

Corollary 19.10:
A modular function for Gamma(1) that is holomorphic on H is a polynomial in j.

Theorem 19.11:
C(Gamma) is a finite extension of C(j) of degree at most [Gamma(1):Gamma].

Theorem 19.13:
j_N(tau) := j(N*tau) is a modular function for Gamma_0(N).

Theorem 19.14:
The field of modular functions for Gamma_0(N) is an extension of C(j) of degree n generated by j_N, where n is the number of right cosets.

Lemma 19.16:
Right coset representatives for Gamma_0(N) in Gamma(1), for prime N, are T^k (0 <= k < N) and S.

Theorem 19.17:
The modular polynomial Phi_N lies in Z[X,Y].

Lemma 19.18 [Hasse q-expansion principle]:
If f in C(j,j_N) has a q-expansion with integer coefficients and is a polynomial in j and j_N, then it has integer coefficients as a polynomial in j and j_N.

Lemma 20.2:
The cyclic sublattices of prime index p in a lattice [1,tau] are [1,tau+k/p] for 0 <= k < p and [1,p*tau].

Theorem 20.3:
Phi_N(j_1,j_2) = 0 iff j_1 and j_2 are j-invariants of elliptic curves related by a cyclic N-isogeny.

Theorem 20.4:
Theorem 20.3 generalizes to fields of characteristic not dividing N.

Theorem 20.7:
Phi_N(X,Y) = Phi_N(Y,X) for all N > 1 (symmetry of the modular polynomial).

Lemma 20.9:
For prime N, the leading term of Phi_N(X,X) in Z[X] is -X^{2N}.

Theorem 20.11:
Every ideal class in cl(O) contains infinitely many ideals of prime norm.

Theorem 20.12:
The coefficients of the Hilbert class polynomial H_D(X) are integers.

Corollary 20.13:
For an elliptic curve E/C with complex multiplication, j(E) is an algebraic integer.

Theorem 20.14:
The map Psi: Gal(L/K) -> cl(O) sending each sigma to the unique alpha_sigma such that j(E)^sigma = alpha_sigma*j(E) for all j(E) in Ell_O(C) is an injective group homomorphism.

Theorem 21.1 [First Main Theorem of CM]:
Psi: Gal(L/K) -> cl(O) is an isomorphism compatible with the actions of Gal(L/K) and cl(O) on Ell_O(L).

Corollary 21.2:
H_D is irreducible over K = Q(sqrt(D)), and K(j(E))/K is a finite abelian extension with Gal(K(j(E))/K) isomorphic to cl(O).

Theorem 21.5:
Let O be an imaginary quadratic order with discriminant D. For p not dividing D, the following are equivalent: (i) p is the norm of a principal O-ideal; (ii) (D/p)=1 and H_D splits in F_p[X]; (iii) p splits completely in L; (iv) 4p = t^2 - v^2*D with t not 0 mod p.

Lemma 21.6:
O_K-ideals of norm p are of the form [p, omega-r] where r is a root of the minimal polynomial of omega mod p. The number of such ideals is 1+(D/p).

Corollary 21.7:
The number of proper O-ideals of norm p is 0 when p divides the conductor, and 1+(D/p) otherwise.

Corollary 21.8:
The splitting field L of H_D over K is unramified at all primes not dividing the conductor of O.

Corollary 21.9:
CM curves with discriminant D reduce to ordinary curves with tr(pi) = +-t where 4p = t^2 - v^2*D, provided j != 0, 1728.

Theorem 21.12 [Deuring]:
H_D(X) splits into distinct linear factors in F_q[X] and its roots form Ell_O(F_q).

Theorem 21.13 [Deuring lifting theorem]:
For any E/F_q and nonzero phi in End(E), there exist E*/L over a number field with phi* in End(E*) such that E and phi are reductions of E* and phi*.

Theorem 22.3:
For an l-isogeny phi: E -> E', End^0(E') = End^0(E). If End^0(E) = K is an imaginary quadratic field, then End(E) = O and End(E') = O' are orders in K with [O:O'] = 1, l, or 1/l.

Theorem 22.5:
If l does not divide [O_K:O], then E admits 1+(D/l) horizontal, l-(D/l) descending, and 0 ascending l-isogenies. Otherwise, 0 horizontal, l descending, and 1 ascending.

Lemma 22.6:
Ell_O(F_q) is either empty or has cardinality h(D). If nonempty, Ell_{O'}(F_q) is also nonempty for every O' containing O.

Corollary 22.7:
Counts of horizontal, descending, and ascending l-isogenies for ordinary curves E/F_q with CM by O.

Corollary 22.8:
Ell_O(F_q) is a cl(O)-torsor, where the ideal class action is given by horizontal l-isogenies.

Theorem 22.11 [Kohel]:
Ordinary components of G_l(F_q) (not containing j=0 or 1728) are l-volcanoes with explicit level structure, surface degree 1+(D_0/l), and depth d determined by 4q = t^2 * l^{2d} * v^2 * D_0.

Lemma 22.13:
A vertex v in an ordinary component has degree <= 2 iff v is on the floor V_d; otherwise deg v = l+1.

Theorem 23.6:
Rational maps from smooth projective curves are morphisms.

Theorem 23.9:
For f in k(C)^x viewed as a morphism C -> P^1, deg f = sum_{f(P)=Q} v_P(u_Q o f) for every Q in P^1.

Corollary 23.10:
For every f in k(C)^x, sum_P v_P(f) = 0, with v_P(f) = 0 for all P iff f in k^x.

Theorem 23.17:
The Abel-Jacobi map E -> Pic^0(E) defined by P -> [P]-[0] is a group isomorphism.

Theorem 23.20 [Weil reciprocity]:
For f, g in k(C)^x with disjoint divisor supports, f(div g) = g(div f).

Lemma 23.21:
The Weil pairing e_n(D_1,D_2) depends only on divisor classes and is an nth root of unity.

Theorem 23.22:
The Weil pairing e_n: (Pic^0 C)[n] x (Pic^0 C)[n] -> mu_n is bilinear and alternating.

Lemma 23.24:
The Miller functions f_{n,P} satisfy: (i) div f_{n,P} = n[P]-(n-1)[0]-[nP]; (ii) f_{m+n,P} = f_{m,P}*f_{n,P}*G_{mP,nP}; (iii) f_{mn,P} = f_{m,P}^n * f_{n,mP}.

Corollary 23.25:
f_{n,P}(Q) is computable in O(log n) field operations.

Lemma 23.26:
Formula for e_n(P,Q) using Miller functions and a translation point T.

Corollary 23.27:
e_n(P,Q) = (-1)^n * f_{n,P}(Q) / f_{n,Q}(P) for distinct P,Q in E[n].

Theorem 23.29:
Properties of the Weil pairing: bilinear, alternating, non-degenerate, compatible, Galois-equivariant, endomorphism-compatible, and surjective.

Corollary 23.30:
If E[n] subset E(k) then mu_n subset k^x. Over Q, E[n] subset E(Q) only for n <= 2.

Corollary 23.31:
The order of e_n(P,Q) equals the largest m such that E[m] subset <P,Q>. e_n(P,Q) = 1 iff <P,Q> is cyclic.

Lemma 23.33:
The embedding degree of E with respect to n equals the least k > 0 with q^k = 1 mod n, when n is a prime divisor of #E(F_q).

Theorem 24.1 [Taylor-Wiles]:
Every semistable elliptic curve E/Q is modular.

Theorem 24.2 [Breuil-Conrad-Diamond-Taylor]:
Every elliptic curve E/Q is modular.

Theorem 24.8:
Dimension formulas for M_k(Gamma) and S_k(Gamma) in terms of genus, elliptic points, and cusps. For k=2, dim S_k(Gamma) = g(Gamma).

Theorem 24.11:
The Hecke operators T_n and homothety operators R_lambda satisfy: (i) T_n*R_lambda = R_lambda*T_n; (ii) T_{mn} = T_m*T_n for m coprime to n; (iii) T_{p^{r+1}} = T_{p^r}*T_p - p*T_{p^{r-1}}*R_p.

Corollary 24.12:
The Hecke operators generate a commutative subring of End(Div(L)).

Corollary 24.13:
For Gamma_0(1): T_{mn} = T_m*T_n for m coprime to n, and T_{p^{r+1}} = T_{p^r}*T_p - p^{k-1}*T_{p^{r-1}}.

Theorem 24.14:
The q-series coefficients of T_p*f satisfy a_n(T_p*f) = a_{np}(f) if p does not divide n, and a_{np}(f) + p^{k-1}*a_{n/p}(f) if p divides n.

Corollary 24.15:
a_m(T_n*f) = a_{mn}(f) for m coprime to n; in particular a_1(T_n*f) = a_n(f).

Lemma 24.19:
Spectral theorem for commuting Hermitian operators: if V is a finite-dimensional C-vector space with Hermitian form and alpha_1, alpha_2, ... are commuting Hermitian operators, then V decomposes as a direct sum of simultaneous eigenspaces.

Theorem 24.20:
S_k(Gamma_0(1)) has a unique basis of eigenforms, each spanning a one-dimensional eigenspace for every T_n.

Theorem 24.21:
S_k^new(Gamma_0(N)) has a unique basis of newforms, each spanning a one-dimensional eigenspace for the Hecke operators T_n.

Theorem 24.25 [Hecke]:
L(f,s) for f in S_k(Gamma_0(N)) extends analytically to a holomorphic function on C, and the normalized L-function satisfies a functional equation.

Theorem 24.27:
For a newform f in S_k^new(Gamma_0(N)), L(f,s) has an Euler product.

Theorem 24.33 [Modularity Theorem]:
Every elliptic curve E/Q is modular.

Corollary 24.34:
L(E,s) for E/Q has an analytic continuation to C and satisfies a functional equation with root number w_E = +-1.

Conjecture 24.35 [Weak BSD]:
L(E,s) has a zero of order r at s=1, where r is the rank of E(Q).

Conjecture 24.36 [Parity Conjecture]:
The root number satisfies w_E = (-1)^r.

Theorem 24.37 [Eichler-Shimura]:
Every newform f in S_2^new(Gamma_0(N)) with integer coefficients gives rise to an elliptic curve E/Q of conductor N with f_E = f.

Theorem 24.38 [Faltings-Tate]:
If a_p = a'_p for sufficiently many good primes p, then E and E' are isogenous.

Corollary 24.39:
E, E'/Q are isogenous iff L(E,s) = L(E',s).

Conjecture 25.1 [Serre's modularity conjecture]:
Every odd irreducible Galois representation rho-bar: G_Q -> GL_2(Z/lZ) is modular.

Theorem 25.2 [Ribet]:
If E is modular and rho-bar_{E,l} is irreducible, then rho-bar_{E,l} is modular of weight 2 and level N', where N' = N / (product of primes p with v_p(N)=1 and v_p(Delta_min) = 0 mod l).

Corollary 25.3:
The Frey curve E_{a,b,c} is not modular.

Theorem 25.4 [Taylor-Wiles modularity lifting]:
If E/Q is semistable and rho-bar_{E,l} is modular, then rho_{E,l} is modular.

Theorem 25.5 [Langlands-Tunnel]:
If rho-bar_{E,3} is irreducible, then it is modular.

Theorem 25.6:
No semistable elliptic curve E/Q admits a rational 15-isogeny.

Theorem 25.7 [Wiles 3-5 trick]:
For semistable E/Q with rho-bar_{E,5} irreducible, there exists semistable E'/Q with rho-bar_{E',3} irreducible and rho-bar_{E',5} isomorphic to rho-bar_{E,5}.

Theorem 25.8 [Wiles]:
Every semistable elliptic curve E/Q is modular.

Corollary 25.9 [Fermat's Last Theorem]:
x^n + y^n = z^n has no integer solutions with xyz != 0 for n > 2.
