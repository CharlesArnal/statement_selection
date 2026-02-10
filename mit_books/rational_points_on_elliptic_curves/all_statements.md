# All Mathematical Statements from "Rational Points on Elliptic Curves" (MIT Lecture Notes)

## Statement 1: Proposition (Bezout's Theorem for Plane Curves)
If C and D are projective plane curves of degrees m and n respectively, with no common component, then C and D intersect in exactly m*n points (counted with multiplicity) in the projective plane over an algebraically closed field.

## Statement 2: Proposition (Group Law on Cubic Curve)
Let C be a nonsingular cubic curve over a field F. The set of rational points C(F), together with the point at infinity O, forms an abelian group under the chord-and-tangent addition law, where the identity is O.

## Statement 3: Proposition (Addition Formula for Elliptic Curves)
Let C: y^2 = x^3 + ax^2 + bx + c be a nonsingular cubic. Given P1 = (x1, y1) and P2 = (x2, y2) on C with P1 != -P2, the sum P3 = P1 + P2 = (x3, y3) is given by x3 = lambda^2 - a - x1 - x2 and y3 = lambda*(x1 - x3) - y1, where lambda = (y2 - y1)/(x2 - x1) if P1 != P2, and lambda = (3x1^2 + 2ax1 + b)/(2y1) if P1 = P2 (duplication formula).

## Statement 4: Proposition (Associativity of the Group Law)
The chord-and-tangent addition law on a nonsingular cubic curve is associative.

## Statement 5: Proposition (Complex Torus and Elliptic Curves)
The set of complex points on an elliptic curve over C is isomorphic, as a complex Lie group, to a complex torus C/L, where L is a lattice in C.

## Statement 6: Theorem (Weierstrass p-function Uniformization)
The map u -> (P(u), P'(u)) gives an isomorphism from C/L to the elliptic curve y^2 = 4x^3 - g2*x - g3, where P is the Weierstrass p-function associated to the lattice L, and g2, g3 are the Eisenstein series.

## Statement 7: Proposition (Transformation to Short Weierstrass Form)
Over a field of characteristic not equal to 2 or 3, every elliptic curve can be transformed by an admissible change of variables to the short Weierstrass form y^2 = x^3 + ax + b.

## Statement 8: Proposition (Discriminant and Nonsingularity)
A Weierstrass curve y^2 = x^3 + ax^2 + bx + c is nonsingular (i.e., is an elliptic curve) if and only if its discriminant D is nonzero.

## Statement 9: Proposition (Nagell-Lutz Theorem)
Let C: y^2 = x^3 + ax^2 + bx + c with a, b, c integers and discriminant D != 0. If P = (x, y) is a rational point of finite order with x, y integers, then either y = 0 (so P has order 2) or y^2 divides D.

## Statement 10: Proposition (Height Function - Finiteness)
For any real number M, the set {P in C(Q) : h(P) <= M} is finite, where h is the naive (logarithmic) height function on rational points of the elliptic curve C.

## Statement 11: Lemma (Height and Translation)
Let P0 be a fixed rational point on C. Then there exists a constant k0 (depending on P0) such that h(P + P0) <= 2h(P) + k0 for all P in C(Q).

## Statement 12: Lemma (Height and Duplication)
There exists a constant K (depending on the curve) such that h(2P) >= 4h(P) - K for all P in C(Q).

## Statement 13: Theorem (Mordell's Theorem)
Let C be a nonsingular cubic curve given by y^2 = x^3 + ax^2 + bx with a, b integers. Then the group of rational points C(Q) is finitely generated.

## Statement 14: Lemma (Finiteness of Gamma/2Gamma)
The quotient group C(Q)/2C(Q) is finite.

## Statement 15: Proposition (2-Isogeny phi)
Let C: y^2 = x^3 + ax^2 + bx and C-bar: y^2 = x^3 + a-bar*x^2 + b-bar*x, where a-bar = -2a and b-bar = a^2 - 4b. Let T = (0,0) in C. Then phi(P) = (y^2/x^2, y(x^2 - b)/x^2) for P = (x,y) not in {O, T}, and phi(O) = phi(T) = O-bar, defines a group homomorphism phi: C(Q) -> C-bar(Q).

## Statement 16: Proposition (Dual Isogeny and Composition)
There exists a homomorphism psi: C-bar -> C such that psi composed with phi is the multiplication-by-2 map, i.e., psi(phi(P)) = 2P for all P in C(Q).

## Statement 17: Proposition (Image of phi and Kernel)
The kernel of phi is {O, T} = {O, (0,0)}, and P = (x, y) is in the image of psi(C-bar) if and only if x is a rational square.

## Statement 18: Proposition (Homomorphism lambda to Q*/Q*^2)
(a) The map lambda: C(Q) -> Q*/Q*^2 defined by lambda(O) = 1, lambda(T) = b, lambda(x,y) = x (mod Q*^2) is a homomorphism.
(b) The kernel of lambda is the image of psi(C-bar(Q)), so lambda induces an injection C(Q)/psi(C-bar(Q)) -> Q*/Q*^2.

## Statement 19: Proposition (Bound on Image of lambda)
Let p1, ..., pt be the distinct prime factors of b. Then the image of lambda is contained in the subgroup S = {+/- p1^e1 * ... * pt^et : each ei = 0 or 1} of Q*/Q*^2. In particular, the index (C(Q) : psi(C-bar(Q))) is at most 2^(t+1).

## Statement 20: Lemma (Index Bound from Two Isogenies)
Let A, B be abelian groups with homomorphisms phi: A -> B and psi: B -> A satisfying psi(phi(a)) = 2a and phi(psi(b)) = 2b. If phi(A) has finite index in B and psi(B) has finite index in A, then (A : 2A) is finite and (A : 2A) <= (B : phi(A)) * (A : psi(B)).

## Statement 21: Proposition (Structure of Gamma/2Gamma for Finitely Generated Abelian Groups)
If Gamma is a finitely generated abelian group, then (Gamma : 2*Gamma) = 2^(rank(Gamma)) * #Gamma[2], where Gamma[2] is the 2-torsion subgroup.

## Statement 22: Proposition (Descent Theorem)
Lemmas 10, 11, 12, and 14 (finiteness of {P : h(P) <= M}, height-translation bound, height-duplication bound, and finiteness of C(Q)/2C(Q)) together imply Mordell's Theorem (finite generation of C(Q)).

## Statement 23: Claim (Nonsingular Points on Singular Cubic Form a Group)
Let C: y^2 = x^3 + ax^2 + bx + c be a singular cubic (the discriminant is zero, so f(x) has a multiple root). Then the set of nonsingular points C_ns(Q) forms a group under the chord-and-tangent law.

## Statement 24: Lemma (Line Through Singular Point)
A line through a singular point P = (x0, y0) of a cubic curve C intersects C with multiplicity at least 2 at P.

## Statement 25: Claim (Node Case - Isomorphism with Multiplicative Group)
For the nodal cubic C1: y^2 = x^3 + x^2 (node at origin), the map phi(P) = (y - x)/(y + x) gives an isomorphism C1_ns(Q) -> Q* (the multiplicative group of nonzero rationals).

## Statement 26: Theorem (Hasse-Weil Bound for Elliptic Curves over Finite Fields)
If C is a nonsingular cubic curve over the finite field F_p, then #C(F_p) = p + 1 + epsilon, where |epsilon| <= 2*sqrt(p).

## Statement 27: Theorem (Gauss's Theorem on Fermat Cubic)
Let M_p be the number of projective solutions to X^3 + Y^3 + Z^3 = 0 over F_p. (a) If p is not congruent to 1 mod 3, then M_p = p + 1. (b) If p = 1 mod 3, then there exist integers A, B such that 4p = A^2 + 27B^2, with A unique up to sign (choosing A = 1 mod 3), and M_p = p + 1 + A.

## Statement 28: Fact (Multiplicative Group of Finite Field is Cyclic)
The multiplicative group F_p* of a finite field F_p is a cyclic group of order p - 1.

## Statement 29: Theorem (Reduction Modulo p is an Injective Homomorphism on Torsion)
Let C: y^2 = x^3 + ax^2 + bx + c with integer coefficients and discriminant D. Let Phi denote the torsion subgroup of C(Q). Then for any prime p not dividing D, the reduction map Phi -> C(F_p) is an injective group homomorphism.

## Statement 30: Theorem (Fermat's Little Theorem)
If p is prime and p does not divide a, then a^(p-1) = 1 mod p.

## Statement 31: Proposition (Euclidean Algorithm Complexity)
The Euclidean algorithm computes gcd(a, b) in at most 2*log_2(b) operations.

## Statement 32: Proposition (Bound on Solutions of x^3 + y^3 = m)
Let m >= 1 be an integer. Then every solution to x^3 + y^3 = m (with x, y integers) satisfies max(|x|, |y|) <= 2*sqrt(m/3).

## Statement 33: Proposition (Infinitely Many Integer Points for x^3 + y^3 = m)
For every integer N >= 1, there exists an integer m > 1 such that the cubic curve x^3 + y^3 = m has at least N points with integer coordinates.

## Statement 34: Theorem (Silverman's Bound on Integer Points)
Let m >= 1 be an integer, and let C_m be the cubic curve x^3 + y^3 = m. There exists a constant k > 1 independent of m such that #{(x,y) in C_m(Q) : x, y in Z, gcd(x,y) = 1} <= k^(1 + rank C_m(Q)).

## Statement 35: Theorem (Thue's Theorem)
Let a, b, c be nonzero integers. Then the equation ax^3 + by^3 = c has only finitely many solutions in integers x, y.

## Statement 36: Theorem (Diophantine Approximation Theorem)
Let b > 0 be an integer which is not a perfect cube, and let beta = b^(1/3). Let C be a fixed positive constant. Then there are only finitely many pairs of integers (p, q) with q > 0 satisfying |p/q - beta| <= C/q^3.

## Statement 37: Lemma (Siegel's Lemma)
Let N > M be positive integers. Given a homogeneous linear system of M equations in N unknowns with integer coefficients (matrix A), there exists a nonzero integer solution t = (t1, ..., tN) satisfying max|ti| <= 2*(4N * max|A_ij|)^(M/(N-M)).

## Statement 38: Proposition (Congruent Number Characterization)
Given n in Z, n > 0 squarefree, there exists a right triangle with rational sides X, Y, Z and area (1/2)*X*Y = n if and only if there exists x in Q such that x, x - n, and x + n are all in (Q*)^2, equivalently, if and only if the elliptic curve E_n: y^2 = x^3 - n^2*x has a rational point of infinite order (nonzero rank).

## Statement 39: Theorem (Congruent Number and Rank of E_n)
N is a congruent number if and only if E_n(Q) has nonzero rank.

## Statement 40: Theorem (Points of Finite Order on E_n)
The torsion subgroup of E_n(Q) = {O, (0,0), (n,0), (-n,0)}, i.e., the only rational points of finite order on E_n: y^2 = x^3 - n^2*x are the identity and the three 2-torsion points.

## Statement 41: Proposition (E_n over F_q for q = 3 mod 4)
Let q = p^k with p not dividing 2n, and suppose q = 3 mod 4. Then #E_n(F_q) = q + 1.

## Statement 42: Proposition (Doubling Criterion via Squares)
Let E: y^2 = (x - e1)(x - e2)(x - e3) with e_i in R, and let P = (x0, y0) in E(R). Then P is in 2E(R) (i.e., P = 2Q for some Q in E(R)) if and only if x0 - e_i is a perfect square in R* for i = 1, 2, 3.
