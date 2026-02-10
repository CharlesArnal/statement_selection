# All Mathematical Statements - Algebra I (MIT 18.701) Student Notes

## Statement 1 (Theorem, line 300)
**Theorem (Subgroups of Z).**
The subgroups of (Z, +) are {0}, Z, 2Z, 3Z, ... . That is, every subgroup of the integers under addition is of the form nZ for some non-negative integer n.

## Statement 2 (Corollary, line 324)
**Corollary.**
Given a, b in Z, consider S = {ai + bj : i, j in Z}. The subset S satisfies all the subgroup conditions, so by the theorem on subgroups of Z, there is some d such that S = dZ. In fact, d = gcd(a, b).

## Statement 3 (Theorem, line 370)
**Theorem (Structure of Cyclic Subgroups).**
Let S = {n in Z : g^n = e}. Then S is a subgroup of Z, so S = dZ or S = {0}, leading to two cases:
- If S = {0}, then <g> is infinite and all the g^k are distinct.
- If S = dZ, then <g> = {e, g, g^2, ..., g^{d-1}} subset G, which is finite.

## Statement 4 (Proposition, line 451)
**Proposition.**
If f(ab) = f(a)f(b) for a group homomorphism f: G -> G', then f(e_G) = e_{G'} and f(a)^{-1} = f(a^{-1}).

## Statement 5 (Theorem, line 504)
**Theorem.**
Let f be a homomorphism from G to G'. Then im(f) is a subgroup of G'.

## Statement 6 (Theorem, line 523)
**Theorem.**
The kernel of a homomorphism f is also a subgroup.

## Statement 7 (Proposition, line 707)
**Proposition.**
All cosets of H have the same order as H.

## Statement 8 (Proposition, line 714)
**Proposition.**
Cosets of H form a partition of the group G.

## Statement 9 (Lemma, line 720)
**Lemma.**
Given a coset C of H in G, take b in C. Then C = bH.

## Statement 10 (Theorem, line 757)
**Theorem (Counting Formula).**
We have |G| = [G:H] * |H|.

## Statement 11 (Corollary, line 779) -- Lagrange's Theorem
**Corollary (Lagrange's Theorem).**
For H a subgroup of G, |H| is a divisor of |G|.

## Statement 12 (Corollary, line 784)
**Corollary.**
If |G| is a prime p, then G is a cyclic group.

## Statement 13 (Corollary, line 814) -- Counting Formula (restated)
**Corollary (Counting Formula).**
Let [G:H] be the number of left cosets of H, which is called the index of H in G. Then |G| = |H| * [G:H].

## Statement 14 (Theorem, line 825) -- Lagrange's Theorem (restated)
**Theorem (Lagrange's Theorem).**
For H a subgroup of G, |H| is a divisor of |G|.

## Statement 15 (Corollary, line 830)
**Corollary.**
The order of x in G is |<x>|. Since the order of any subgroup divides the order of |G|, ord(x) also divides |G|.

## Statement 16 (Corollary, line 834)
**Corollary.**
Any group G with prime order p is a cyclic group.

## Statement 17 (Corollary, line 877)
**Corollary.**
The size of the group is |G| = |ker(f)| * |im(f)|.

## Statement 18 (Theorem, line 1000) -- Correspondence Theorem
**Theorem (Correspondence Theorem).**
For a surjective homomorphism f with kernel K, there is a bijective correspondence:
{subgroups of G containing K} <-> {subgroups of G'},
where a subset H of G containing K maps to its image f(H) <= G', and H' <= G' maps to its preimage f^{-1}(H') <= G.

## Statement 19 (Theorem, line 1041) -- Correspondence Theorem (restated)
**Theorem (Correspondence Theorem).**
Where f: G -> G' is a surjective homomorphism and K = ker(f), there is a correspondence
{subgroups H : K subset H subset G} <-> {subgroups H' : {e_{G'}} subset H' subset G'},
which states that subgroups of G containing the kernel are in bijection with subgroups of H' in the image of f.

## Statement 20 (Theorem, line 1124)
**Theorem.**
If C_1, C_2 are cosets of a normal subgroup N, then C_1 * C_2 is also a coset of N.

## Statement 21 (Theorem, line 1162)
**Theorem (Quotient Group Structure).**
The following two statements are true about the quotient group:
1. The composition law defines a group structure on G/N (all the group axioms hold).
2. There exists a surjective homomorphism pi: G -> G/N taking x to [xN] such that ker(pi) = N.

## Statement 22 (Lemma, line 1411)
**Lemma (Span Lemma).**
If S = {v_1, ..., v_r} spans V, and L = {w_1, ..., w_s} is linearly independent, then:
1. Removing elements of S gets a basis of V.
2. Adding elements of S to L gets another basis of V.
3. |S| >= |L|.

## Statement 23 (Corollary, line 1421)
**Corollary.**
If S and L are both bases for V, then |S| = |L|. Any two bases of V contain the same number of vectors.

## Statement 24 (Theorem, line 1588) -- Dimension Formula
**Theorem (Dimension Formula / Rank-Nullity).**
Given T: V -> W, dim(Ker T) + dim(im T) = dim(V).

## Statement 25 (Corollary, line 1628)
**Corollary.**
For any linear transformation, we can write its matrix in the standard form (identity block with zeros) for some choice of basis for V and W.

## Statement 26 (Corollary, line 1631)
**Corollary.**
If we are given a matrix M in Mat_{m x n} representing a linear transformation from F^n to F^m, then there exist change of basis matrices P in GL_n(F), Q in GL_m(F) such that Q^{-1}MP is in the standard form.

## Statement 27 (Corollary, line 1668)
**Corollary.**
Given a matrix M in Mat_{m x n}(F), we have rank(M) = rank(M^T).

## Statement 28 (Proposition, line 1714)
**Proposition.**
When working with linear operators T: V -> V, for V finite-dimensional, then T is injective <-> T is surjective <-> T is an isomorphism.

## Statement 29 (Proposition, line 1844)
**Proposition.**
Given lambda in F, lambda is an eigenvalue for A if and only if p_A(lambda) = 0; that is, if and only if lambda is a root of the characteristic polynomial p_A(t).

## Statement 30 (Proposition, line 1934)
**Proposition (Linear Independence of Eigenvectors).**
Given an n x n matrix A, eigenvectors v_1, ..., v_k, and distinct eigenvalues lambda_1, ..., lambda_k, the vectors v_i are all linearly independent.

## Statement 31 (Corollary, line 1957)
**Corollary.**
Consider a matrix A. If the characteristic polynomial is p_A(t) = (t - lambda_1) ... (t - lambda_n) where each lambda_i is distinct, A will have an eigenbasis and will thus be diagonalizable.

## Statement 32 (Theorem, line 2023) -- Jordan Decomposition Theorem
**Theorem (Jordan Decomposition Theorem).**
Given a linear operator T: V -> V, where dim V = n, there exists a basis v_1, ..., v_n and pairs (a_1, lambda_1), ..., (a_r, lambda_r) such that the matrix of T in this basis is a block diagonal matrix with Jordan blocks J_{a_i}(lambda_i).

## Statement 33 (Theorem, line 2091) -- Jordan Normal Form (restated)
**Theorem (Jordan Normal Form).**
Considering a transformation T: V -> V, there must exist a basis v_1, ..., v_n such that the matrix of T (in this basis) is a block diagonal matrix with Jordan blocks J_{a_i}(lambda_i).

## Statement 34 (Theorem, line 2250) -- Direct Sum Criterion
**Theorem (Splitting / Direct Sum Criterion).**
If dim W + dim W' = dim V, and W intersect W' = {0}, then it must be the case that V = W direct-sum W'.

## Statement 35 (Theorem, line 2380)
**Theorem (Characterizations of Orthogonal Matrices).**
The following conditions are all equivalent:
1. The matrix A is orthogonal.
2. For all vectors v in R^n, |Av| = |v|. That is, A preserves lengths.
3. For an n-dimensional matrix A, A^T A = I_n.
4. The columns of A form an orthonormal basis.

## Statement 36 (Proposition, line 2415)
**Proposition.**
The orthogonal matrices form a subgroup O_n of GL_n.

## Statement 37 (Theorem, line 2469)
**Theorem.**
The matrices of the second type (in the classification of 2x2 orthogonal matrices) are reflections across a line through the origin at an angle of theta/2.

## Statement 38 (Theorem, line 2504)
**Theorem.**
The rotation operators are exactly SO_3.

## Statement 39 (Theorem, line 2602)
**Theorem (Isometry Decomposition).**
Every isometry f is of the form t_b composed with A, for A in O_n and b in R^n. So f(x) = Ax + b.

## Statement 40 (Lemma, line 2608)
**Lemma.**
If f: R^n -> R^n is an isometry such that f(0) = 0, it must be a linear transformation.

## Statement 41 (Theorem, line 2696)
**Theorem (Classification of Isometries of R^2).**
Every isometry on R^2 is:
1. Translation
2. Rotation around a point p
3. Reflection across a line L
4. Glide reflection -- first reflect across a line L, then translate by some vector b parallel to L.

## Statement 42 (Theorem, line 2861)
**Theorem (Discrete Subgroups of R).**
If G <= (R, +) is discrete, then G = {0} or G = Z*alpha for some real number alpha > 0.

## Statement 43 (Theorem, line 2899)
**Theorem.**
If a subgroup H <= SO_2 is finite, then H is isomorphic to C_n for some n.

## Statement 44 (Theorem, line 2916)
**Theorem (Finite Subgroups of O_2).**
Any finite subgroup of O_2 is isomorphic to C_n or D_n.

## Statement 45 (Theorem, line 2976) -- Restated
**Theorem (Finite Subgroups of O_2).**
Any finite subgroup G of O_2 is either:
- G isomorphic to C_n = <rho_{2pi/n}>, the cyclic group generated by a rotation by 2pi/n; or
- G isomorphic to D_n = <rho_{2pi/n}, r> which is the group C_n with an extra reflection r.

## Statement 46 (Theorem, line 2996)
**Theorem.**
Any finite subgroup G of M_2 (the group of isometries of R^2) is also isomorphic to C_n or D_n.

## Statement 47 (Theorem, line 3067)
**Theorem (Discrete Subgroups of R^2).**
If G is a discrete subgroup of R^2, then:
1. G = {0}; or
2. there exists some alpha in R^2 such that G = Z*alpha; or
3. there exist linearly independent vectors a, b in R^2 such that G = Za + Zb. This is called a lattice inside R^2.

## Statement 48 (Proposition, line 3119)
**Proposition.**
Every A in the point group G-bar maps the lattice L to L.

## Statement 49 (Theorem, line 3249)
**Theorem (Point Group Acts on Lattice).**
For the point group G-bar <= O_2 of some discrete subgroup G of M_2, and the translation subgroup L of R^2, the group G-bar must map L to itself. For any element A in G-bar and b in L, the image of b under the action of A is b -> Ab in L.

## Statement 50 (Theorem, line 3315) -- Crystallographic Restriction
**Theorem (Crystallographic Restriction).**
Let L != {0}. Then the point group G-bar = C_n or D_n, where n = 1, 2, 3, 4, or 6.

## Statement 51 (Proposition, line 3572)
**Proposition.**
The orbits of G form a partition of S. In particular, S is the disjoint union of the orbits: S = disjoint-union O_i where O_i intersect O_j = empty set.

## Statement 52 (Corollary, line 3581)
**Corollary.**
If S is a finite set, and O_1, ..., O_k are the orbits, then |S| = sum_{i=1}^{k} |O_i|, since each of the orbits cover S exactly.

## Statement 53 (Proposition, line 3597)
**Proposition (Orbit-Stabilizer Bijection).**
Fix some s in S and let H := Stab(s). Then there exists a bijection epsilon from the quotient group G/H to the orbit of s, O_s, taking gH to gs.

## Statement 54 (Corollary, line 3614) -- Counting Formula for Orbits
**Corollary (Counting Formula for Orbits).**
|O_s| = [G : Stab(s)].

## Statement 55 (Theorem, line 3726)
**Theorem (Finite Subgroups of SO_3).**
If G <= SO_3, then:
- G is isomorphic to C_n, or
- G is isomorphic to D_n, or
- G is the group of rotational symmetries of a regular polyhedron.

## Statement 56 (Lemma, line 3759)
**Lemma.**
If p is a pole in P and some g in G, then gp is also in P. As a result, G acts on P.

## Statement 57 (Theorem, line 4031)
**Theorem.**
Every p-group has non-trivial center.

## Statement 58 (Corollary, line 4088)
**Corollary.**
If |G| = p^2, then G must be abelian.

## Statement 59 (Corollary, line 4106)
**Corollary.**
Given a group G such that |G| = p^2, G must be isomorphic to either C_{p^2}, the cyclic group of size p^2, or C_p x C_p.

## Statement 60 (Theorem, line 4234)
**Theorem.**
The icosahedral group I is simple.

## Statement 61 (Theorem, line 4257)
**Theorem.**
The icosahedral group I is isomorphic to the alternating group A_5.

## Statement 62 (Corollary, line 4293)
**Corollary.**
The alternating group A_5 is also simple.

## Statement 63 (Proposition, line 4375)
**Proposition.**
Two permutations sigma and tau are conjugate if and only if sigma and tau have the same cycle type.

## Statement 64 (Theorem, line 4548)
**Theorem.**
If G is finite, and H is a subgroup of G, then |H| divides |G|.

## Statement 65 (Theorem, line 4575) -- Sylow I
**Theorem (Sylow I).**
Given G such that |G| = n = p^e * m, where p^e is the largest power of p (gcd(p, m) = 1), then there exists a subgroup H <= G such that |H| = p^e.

## Statement 66 (Corollary, line 4603)
**Corollary (Cauchy's Theorem).**
If p divides |G|, there exists an element x in G with order p.

## Statement 67 (Theorem, line 4618) -- Sylow II
**Theorem (Sylow II).**
(a) Given H <= G, where H is a Sylow p-subgroup, any other Sylow p-subgroup H' <= G is conjugate to H; i.e. there exists g such that H' = gHg^{-1}.
(b) Given any subgroup K <= G such that |K| = p^d, for any Sylow subgroup H, there exists g such that gKg^{-1} <= H.

## Statement 68 (Theorem, line 4648) -- Sylow III
**Theorem (Sylow III).**
The number of Sylow p-subgroups of G divides m = n/p^e and is congruent to 1 modulo p.

## Statement 69 (Proposition, line 4692)
**Proposition.**
Where |H| = 5 and |K| = 3 (in a group of order 15):
(a) the two subgroups commute: for h in H and k in K, hk = kh;
(b) H x K is isomorphic to G.

## Statement 70 (Proposition, line 4772)
**Proposition.**
There are two isomorphism classes for groups of order 10: G isomorphic to C_5 x C_2, and G isomorphic to C_{10}.

## Statement 71 (Theorem, line 4833) -- Sylow Theorems (combined restatement)
**Theorem (Sylow Theorems).**
Let G be a finite group where |G| = n = p^e * m and gcd(p, m) = 1:
1. There always exists a Sylow p-subgroup (a subgroup H <= G with |H| = p^e).
2. Given any K <= G where |K| = p^f, there exists some g in G such that gKg^{-1} <= H.
3. The number of Sylow p-subgroups is a factor of m and congruent to 1 mod p.

## Statement 72 (Theorem, line 4852)
**Theorem (Structure Theorem for Finite Abelian Groups).**
Every abelian group G is isomorphic to a product of groups of prime power order.

## Statement 73 (Lemma, line 4862)
**Lemma.**
The homomorphism f (constructed in the proof of the structure theorem) is an isomorphism.

## Statement 74 (Theorem, line 4878) -- Sylow I (restated)
**Theorem (Sylow I).**
Given G such that |G| = n = p^e * m, where p^e is the largest power of p (gcd(p, m) = 1), then there exists a subgroup H <= G such that |H| = p^e.

## Statement 75 (Lemma, line 4887)
**Lemma (Combinatorial Lemma for Sylow I).**
Where n = |G| = m * p^e, we have that C(n, p^e) is not congruent to 0 mod p. Furthermore, C(n, p^e) is congruent to m mod p.

## Statement 76 (Lemma, line 4896)
**Lemma.**
Suppose we have a subset U in S (the set of subsets of G of size p^e), which is a subset of G. Also, let H be a subgroup of G that stabilizes U. Then |H| divides |U|.

## Statement 77 (Theorem, line 4914) -- Sylow II (restated)
**Theorem (Sylow II).**
(a) Given H <= G, where H is a Sylow p-subgroup, any other Sylow p-subgroup H' <= G is conjugate to H.
(b) Given any subgroup K <= G such that |K| = p^d, for any Sylow subgroup H, there exists g such that gKg^{-1} <= H.

## Statement 78 (Theorem, line 4950) -- Sylow III (restated)
**Theorem (Sylow III).**
The number of Sylow p-subgroups of G divides m = n/p^e and is congruent to 1 modulo p.

## Statement 79 (Fact, line 4971)
**Fact.**
Suppose we have another Sylow subgroup H' in Y. H' is fixed by H if and only if H = H'. In other words, under the action of H, there is only one fixed point.

## Statement 80 (Proposition, line 5055)
**Proposition.**
Given a symmetric matrix, the corresponding bilinear form is a symmetric bilinear form.

## Statement 81 (Proposition, line 5064)
**Proposition.**
Every bilinear form <.,.> on R^n arises from a matrix A. That is, there exists some A such that <x, y> = x^T A y. Moreover, the form is symmetric if and only if A is symmetric.

## Statement 82 (Claim, line 5366)
**Claim.**
A Hermitian matrix always has real eigenvalues.

## Statement 83 (Proposition, line 5479)
**Proposition.**
A form on a vector space (V, <.,.>) is non-degenerate if and only if the matrix of the form, A, is invertible, which is when det A != 0.

## Statement 84 (Theorem, line 5507)
**Theorem.**
If the restriction of the bilinear form to W is non-degenerate, then V = W direct-sum W^perp is a direct sum of W and its orthogonal space.

## Statement 85 (Theorem, line 5536) -- restated
**Theorem.**
Let W be a subspace of V. If the restriction of the bilinear form to W is non-degenerate on W, then V = W direct-sum W^perp, which means that every vector v in V is equal to w + u uniquely, where w in W, u in W^perp.

## Statement 86 (Theorem, line 5583)
**Theorem (Existence of Orthogonal Basis).**
For a symmetric or Hermitian form, the vector space V has an orthogonal basis {v_1, ..., v_n}, which is when <v_i, v_j> = 0 for i != j. The matrix for the pairing in the basis will then be diagonal.

## Statement 87 (Corollary, line 5610)
**Corollary.**
In fact, V has an orthogonal basis {v_1, ..., v_k} where <v_i, v_i> = 1, -1, or 0.

## Statement 88 (Claim, line 5625) -- Sylvester's Law
**Claim (Sylvester's Law of Inertia).**
Given V and the bilinear form, the number of 1s, the number of -1s, and the number of 0s that occur in the diagonal form are determined by V and the form, and not by the choice of orthogonal basis. This is called Sylvester's Law, and the number of 1s, -1s, and 0s is called the signature of the form.

## Statement 89 (Theorem, line 5713)
**Theorem (Existence of Orthonormal Basis for Euclidean/Hermitian spaces).**
If V is Euclidean or Hermitian, then there exists an orthonormal basis {v_1, ..., v_n} for V such that <v_i, v_j> = 0 and <v_i, v_i> = 1. In particular, the pairing looks like the dot product or the standard Hermitian product in this basis.

## Statement 90 (Claim, line 5721)
**Claim.**
For any W subset V and the restriction of the bilinear form to W, the restriction is always nondegenerate (in a Euclidean or Hermitian space).

## Statement 91 (Claim, line 5802)
**Claim (Adjoint Characterization).**
For v, w in V, <Tv, w> = <v, T*w>. This property means that T* is uniquely determined, by putting v = u_i and w = u_j.

## Statement 92 (Theorem, line 5844) -- Spectral Theorem
**Theorem (Spectral Theorem).**
For a Hermitian space V, and a normal linear operator T: V -> V, V has an orthonormal basis {u_1, ..., u_n} where each u_i is an eigenvector of T.

## Statement 93 (Theorem, line 5873) -- Spectral Theorem (extended version)
**Theorem (Spectral Theorem, extended).**
Given a Hermitian space V, for any normal linear operator T, there exists an orthonormal eigenbasis of V: {u_1, ..., u_n}. In matrix form, for any normal matrix M in GL_n(C), there exists a unitary matrix P such that P^{-1}MP is diagonal.
The real version states that for a Euclidean vector space V and a symmetric linear operator T, there exists an orthonormal eigenbasis; equivalently, for any symmetric matrix M in GL_n(R), there exists an orthogonal matrix P such that P^{-1}MP is diagonal. All eigenvalues of real symmetric matrices are real.

## Statement 94 (Lemma, line 5892) -- Lemma 1 for Spectral Theorem
**Lemma 1.**
For a linear operator T: V -> V where V is Hermitian, and a subspace W of V such that T(W) is contained in W, then T*(W^perp) is contained in W^perp.

## Statement 95 (Lemma, line 5903) -- Lemma 2 for Spectral Theorem
**Lemma 2.**
If Tv = lambda*v, then T*v = conjugate(lambda)*v. This means T and T* have the same eigenvectors, and eigenvalues related by complex conjugation.

## Statement 96 (Theorem, line 6011)
**Theorem (Classification of Conics).**
After an isometry, all curves of the form ax^2 + bxy + cy^2 + dx + ey + f = 0 look like one of the standard options.

## Statement 97 (Theorem, line 6228)
**Theorem (Conjugacy Classes of SU_2).**
The conjugacy classes of SU_2 are precisely the latitudes Lat_c for -1 <= c <= 1.

## Statement 98 (Theorem, line 6319)
**Theorem (Longitudes as Subgroups of SU_2).**
For each x in E (the equator), Long_x is a subgroup of SU_2. In fact, given theta in R/2piZ, the map theta -> cos(theta)I + sin(theta)x is an isomorphism between R/2piZ and Long_x.

## Statement 99 (Proposition, line 6564)
**Proposition (One-Parameter Subgroups).**
Every one-parameter group in GL_n(C) is of the form phi(t) = e^{tA} for a unique matrix A in Mat_{n x n}(C).

## Statement 100 (Lemma, line 6704)
**Lemma (det of matrix exponential).**
For any A in Mat_{n x n}(C), det(e^A) = e^{trace(A)}.

## Statement 101 (Proposition, line 6856)
**Proposition (Lie Algebra Properties).**
For Lie(G):
- All three definitions (of the Lie algebra) are actually equivalent.
- For a group G, Lie(G) is actually a vector subspace of Mat_{n x n}(R).

## Statement 102 (Theorem, line 6913)
**Theorem (Lie Bracket Closure).**
For any G <= GL_n, the Lie algebra Lie(G) is preserved by the Lie bracket: A, B in Lie(G) implies [A, B] in Lie(G).

## Statement 103 (Theorem, line 6973)
**Theorem (Lie's Third Theorem, partial).**
Given a Lie algebra (finite dimensional over R) V, there exists a unique Lie group G such that Lie(G) = V.

## Statement 104 (Theorem, line 7021)
**Theorem (Normal Subgroups of SU_2).**
If N is normal in SU_2, then N must be {I}, SU_2, or {+/-I}.

## Statement 105 (Corollary, line 7027)
**Corollary (SO_3 is simple).**
The quotient SU_2/{+/-I} is simple.

## Statement 106 (Theorem, line 7302)
**Theorem (PSL_2(F) is simple).**
For any field F with |F| >= 4, the quotient SL_2(F)/{+/-I} is simple.

## Statement 107 (Lemma, line 7319)
**Lemma.**
Given a in F, the equation x^2 = a has at most 2 solutions.

## Statement 108 (Lemma, line 7329)
**Lemma.**
If |F| > 5, then there exists some r in F such that r^2 is not 0, 1, or -1.

## Statement 109 (Claim, line 7339)
**Claim.**
We can find some B in N with distinct eigenvalues (in the proof of simplicity of PSL_2).

## Statement 110 (Claim, line 7355)
**Claim.**
All matrices in SL_2 with eigenvalues s and s^{-1} are contained in N (in the proof of simplicity of PSL_2).

## Statement 111 (Theorem, line 7415)
**Theorem (Bolyai-Gerwien Theorem).**
If P and Q (polygons) have the same area, then P ~ Q (they are scissors-congruent).

## Statement 112 (Proposition, line 7481)
**Proposition (Properties of Tensor Product of Abelian Groups).**
The definition has a few consequences:
- 0 tensor h = g tensor 0 = 0.
- If a in Z, then (ag) tensor h = a(g tensor h) = g tensor ah (by using linearity).
- If we take lists of generators G = <g_1, ..., g_r> and H = <h_1, ..., h_s>, then G tensor H = <g_i tensor h_j>.

## Statement 113 (Theorem, line 7559)
**Theorem (Dehn Invariant Preserved).**
The Dehn invariant is preserved by scissors-congruence: if P ~ Q, then d(P) = d(Q).

## Statement 114 (Theorem, line 7674)
**Theorem.**
If C is a cube and T is a regular tetrahedron, then d(C) != d(T) (their Dehn invariants differ).

## Statement 115 (Claim, line 7732)
**Claim.**
alpha (the dihedral angle arccos(1/3) of the regular tetrahedron) is not a rational multiple of pi.

## Statement 116 (Claim, line 7740)
**Claim.**
For any alpha not in Q*pi, and any nonzero l in R, l tensor alpha is nonzero (in R tensor_{Z} R/Q*pi).
