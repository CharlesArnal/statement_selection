# All Mathematical Statements — 18.725 Algebraic Geometry I

## Lecture 1

**Statement 1 — Theorem 1.1 (Essential Nullstellensatz).**
If K/k is a field extension, and K is a finitely generated k-algebra, then K/k is algebraic. In particular, if k = k-bar, then K = k.

**Statement 2 — Theorem 1.2.**
Zariski closed subsets in k^n are in bijection with radical ideals in R = k[x_1, ..., x_n].

**Statement 3 — Corollary 1.**
There is a Zariski topology on A^n, where the closed sets are the Zariski closed sets.

## Lecture 2

**Statement 4 — Theorem 2.1.**
Let k[U] denote functions associated with the set U. Then k[Spec A] is isomorphic to A.

**Statement 5 — Lemma 1 (Noether Normalization).**
Given A a finitely-generated k-algebra, there exists some algebraically independent elements X_1, ..., X_d over k such that A is a finitely generated k[X_1, ..., X_d]-module.

**Statement 6 — Proposition 1.**
Spec A is quasi-compact for any commutative ring A.

**Statement 7 — Theorem 2.2.**
Given a space of functions X, X is an affine variety if and only if X = Spec A for a finitely generated commutative ring A with no nilpotents.

**Statement 8 — Lemma 2.**
A closed subspace in an affine variety is also affine, and global regular functions restrict surjectively.

**Statement 9 — Corollary 2.**
A closed subspace of a variety is a variety.

**Statement 10 — Theorem 2.3 (Hilbert Basis Theorem).**
k[x_1, ..., x_n], and hence any finitely generated k-algebra is Noetherian.

**Statement 11 — Corollary 3.**
An algebraic variety is a Noetherian topological space (that is, every descending chain of closed subsets terminates; equivalently, every open subset is quasicompact).

**Statement 12 — Corollary 4.**
An open subspace of an algebraic variety is an algebraic variety.

## Lecture 3

**Statement 13 — Theorem 3.1.**
Let X be a space with functions. Then, X is affine if and only if X = Spec A for some finitely generated k-algebra A with no nilpotents.

**Statement 14 — Theorem 3.2 (Noether Normalization Lemma).**
Let A be a finitely generated k-algebra, where k is any field. Then, we can find B subset A such that B is isomorphic to k[x_1, ..., x_n] for some n and A is finitely generated as a B-module.

**Statement 15 — Lemma 3.**
Take P in k[x_1, ..., x_n] be a nonconstant polynomial and let d = deg P. There is a linear change of variables such that P has the form x_n^d + (terms of deg_{x_n} < d).

**Statement 16 — Proposition 2 (Hilbert Basis Theorem).**
k[x_1, ..., x_n] is Noetherian.

**Statement 17 — Theorem 3.3 (Essential Nullstellensatz).**
Let A be a finitely generated k-algebra. If A is a field, then A/k is algebraic.

**Statement 18 — Lemma 4 (Nakayama Lemma).**
Let M be a finitely generated module over a commutative ring A. If I is an ideal of A such that IM = M, then there exists a in A such that aM = 0 and a is congruent to 1 mod I.

**Statement 19 — Proposition 3.**
Spec A is irreducible if and only if A has no zerodivisors.

**Statement 20 — Proposition 4.**
A Noetherian topological space is the union of its components (finite in number).

**Statement 21 — Corollary 5.**
Irreducible closed subsets in Spec A correspond to prime ideals in A. Components correspond to minimal prime ideals.

**Statement 22 — Corollary 6.**
0 = intersection of all minimal prime ideals.

## Lecture 4

**Statement 23 — Proposition 5.**
A Noetherian topological space X is a finite union of its components (i.e. maximal irreducible subsets).

**Statement 24 — Lemma 5.**
A Noetherian topological space X is a finite union of closed irreducible subsets.

**Statement 25 — Corollary 7.**
A radical ideal in a finitely generated ring without nilpotents A is a finite intersection of prime ideals.

**Statement 26 — Corollary 8.**
A closed subset Z of Spec A is irreducible if and only if I_Z is prime.

**Statement 27 — Theorem 4.1.**
The Grassmannian Gr(k,n) defines a projective algebraic variety. The embedding into projective space is defined by W -> the line wedge^k W in wedge^k V.

**Statement 28 — Lemma 6.**
Take omega in wedge^2 V. If omega = v_1 wedge v_2, then omega wedge omega = 0. If dim V = 4, then the converse holds.

**Statement 29 — Lemma 7.**
A finite map satisfies the following properties: (1) It is closed. (2) It has finite fibers.

**Statement 30 — Corollary 9.**
If B subset A and A is finitely generated over B as a B-module, then Spec A -> Spec B has finite nonempty fibers.

**Statement 31 — Lemma 8.**
Let Z_1 strictly contained in Z_2 be irreducible closed subsets of an algebraic variety X. If f: X -> Y is a finite morphism, then f(Z_1) is strictly contained in f(Z_2).

## Lecture 5

**Statement 32 — Lemma 9.**
Let f: X -> Y be a finite map of varieties and Z_1 strictly contained in Z_2 irreducible subvarieties of X. Then f(Z_1) is strictly contained in f(Z_2).

**Statement 33 — Lemma 10.**
If f: X -> Y is a finite surjection of varieties, then dim(X) = dim(Y).

**Statement 34 — Theorem 5.1.**
dim(A^n) = n.

**Statement 35 — Corollary 10.**
If X is a hypersurface in A^n defined by a non-constant polynomial then dim(X) = n - 1.

**Statement 36 — Corollary 11.**
Every variety has finite dimension.

**Statement 37 — Proposition 6.**
All irreducible curves over a given field are homeomorphic.

**Statement 38 — Theorem 5.2 (Bezout).**
Let X, Y be curves in P^2 without a common component, of degree d and e, respectively. Then X intersect Y contains de points, counted with multiplicities.

**Statement 39 — Theorem 5.3 (Pascal).**
Let Q be a conic in P^2 and X a hexagon inscribed in Q. Then the three pairs of opposite sides of X intersect at three points which lie on a straight line.

**Statement 40 — Theorem 5.4.**
Let X be an irreducible variety of dimension n and let g be a non-constant function on X. Then any irreducible component of Z(g) has dimension n-1.

**Statement 41 — Lemma 11.**
dim(Z(g)) >= n - 1 (for g a non-constant function on an irreducible variety of dimension n).

**Statement 42 — Lemma 12.**
Let X be an irreducible variety and U a non-empty open subset. Then dim(U) = dim(X).

## Lecture 6

**Statement 43 — Lemma 13.**
Let X and Y be irreducible varieties with Y normal and f: X -> Y a finite dominant map. Then for any y in Y, #f^{-1}(y) <= deg(f).

**Statement 44 — Proposition 7.**
Let f: X -> Y be a finite dominant map of irreducible varieties and let R be the set of ramification points. R is a closed subset and if k(X)/f*k(Y) is separable, then R != X.

**Statement 45 — Lemma 14 (Yoneda).**
Let C be a category. The assignment x -> h^x defines a fully faithful functor h: C -> Functors(C, Set).

## Lecture 7

**Statement 46 — Lemma 15.**
If A, B are nilpotent-free k-algebras, so is A tensor_k B.

**Statement 47 — Theorem 7.1.**
dim(X x Y) = dim(X) + dim(Y).

**Statement 48 — Lemma 16.**
Suppose that for i in {1,2}, X_i is a closed subvariety of Y_i. Then X_1 x X_2 is a closed subvariety of Y_1 x Y_2.

**Statement 49 — Proposition 8.**
The product of projective varieties is projective.

**Statement 50 — Lemma 17.**
A locally closed subvariety in a separated variety is separated.

**Statement 51 — Lemma 18.**
P^n is separated.

**Statement 52 — Corollary 12.**
A quasiprojective variety is separated.

**Statement 53 — Corollary 13.**
If X is irreducible and Y is separated and f, g: X -> Y agree on a nonempty open set, then f = g.

**Statement 54 — Corollary 14.**
Suppose X is irreducible, Y is separated, U is a nonempty open subset of X, and f: U -> Y is a morphism. Then there is a maximal open subset V of X to which f extends.

## Lecture 8

**Statement 55 — Corollary 15.**
If k = C, then X is separated if and only if X_{cl} is Hausdorff.

**Statement 56 — Proposition 9.**
X is separated if and only if for any affine open U, V in X, U intersect V is affine and k[U intersect V] is generated by k[U] and k[V].

**Statement 57 — Proposition 10 (Catenary property).**
Let X be an algebraic variety, with X = Z_n strictly containing ... strictly containing Z_0 where each Z_i is closed irreducible. If this chain cannot be refined, then dim Z_i = i.

**Statement 58 — Proposition 11.**
If A = k[X] where X is affine of dimension d, then D_V(n) = Theta(n^d).

**Statement 59 — Theorem 8.1.**
Suppose X, Y are irreducible subvarieties in A^n. Then each component of X intersect Y has codimension at most codim X + codim Y.

**Statement 60 — Theorem 8.2.**
The previous theorem holds for X, Y in P^n; moreover, the intersection X intersect Y is nonempty if dim X + dim Y > n.

**Statement 61 — Lemma 19.**
(i) Z closed in X complete implies Z complete. (ii) If f: X -> Z is a morphism with Z separated and X complete, then f(X) is a closed complete subvariety. (iii) If X, Y are complete, then so is X x Y.

**Statement 62 — Proposition 12.**
P^n is complete.

## Lecture 9

**Statement 63 — Lemma 20 (Chow's Lemma).**
If X is a complete, irreducible variety, then there exists a projective variety X-tilde that is birational to X.

**Statement 64 — Proposition 13.**
Blowup is an intrinsic operation that does not depend on the embedding.

## Lecture 11

**Statement 65 — Proposition 14.**
Presheaf of abelian groups on k-vector space is an abelian category.

**Statement 66 — Proposition 15.**
(1) F -> F^# is exact; in particular it doesn't change the stalks. (2) F -> F^# is left adjoint to the embedding Presh -> Sh. (3) F -> F_x is an exact functor.

**Statement 67 — Theorem 11.1.**
If X = Spec(A), then QCoh(X) is equivalent to Mod(A), given by F -> Gamma(F) = F(X).

**Statement 68 — Corollary 16.**
M-tilde is a quasicoherent O_X module.

## Lecture 12

**Statement 69 — Theorem 12.1.**
Let X = Spec(A) be an affine variety. Then there is an equivalence of categories QCoh(X) equivalent to Mod(A).

**Statement 70 — Lemma 22.**
Let i in I be a directed system indexing sheaves F_i. If X is a Noetherian topological space, then the direct limit in PreSh of F_i is a sheaf.

**Statement 71 — Proposition 16.**
j_* j^* F = direct limit of (f^{-n} F), where j: U -> X.

**Statement 72 — Lemma 23.**
If X = Spec A, then F = M-tilde is coherent iff M is finitely generated.

**Statement 73 — Lemma 24.**
f_* sends QCoh(X) to QCoh(Y).

**Statement 74 — Corollary 17.**
f_* is exact for a map of affine varieties. It is left exact in general.

**Statement 75 — Lemma 25.**
If F is coherent, then: (1) Fiber is always finite dimensional. (2) Fiber of F at x is zero iff there exists U containing x with F|_U = 0. (3) The function d: x -> dim(fiber(x)) is upper semicontinuous. (4) d is locally constant if and only if F is locally free.

## Lecture 13

**Statement 76 — Lemma 26.**
Let L, R be adjoint functors, L fully faithful, R conservative, then the two functors are inverse pairs in a categorical equivalence.

**Statement 77 — Lemma 27.**
f: X -> Y is an affine morphism if and only if for every affine open U in Y, f^{-1}(U) is affine.

**Statement 78 — Proposition 17.**
For any fixed Y, the category of X that has an affine morphism to Y corresponds to the opposite category of quasicoherent sheaves of O_Y-algebra.

**Statement 79 — Proposition 18.**
Suppose X -> Y is affine. Let A = f_* O_X. Then QCoh(X) = {QCoh(Y) with an A action}.

**Statement 80 — Proposition 19.**
i_*: QCoh(Z) -> QCoh(X) is a full embedding and the image are the F such that I_Z F = 0.

**Statement 81 — Corollary 19.**
Isomorphism classes of invertible sheaves on X form an abelian group under tensor product (the Picard group).

## Lecture 14

**Statement 82 — Proposition 20.**
(1) M -> M-tilde_{P^n} is an exact functor. (2) Every quasicoherent sheaf on P^n is of the form M-tilde for some graded module M; every coherent such F comes from some finitely generated M.

**Statement 83 — Corollary 18.**
If F is coherent on P^n, then there exists d, k such that O(-d)^{oplus k} -> F is a surjection.

**Statement 84 — Proposition 21.**
QCoh(P^n) is equivalent to Mod_{gr}(A) mod out the locally nilpotent elements, and Coh(P^n) is equivalent to Mod_{gr,f.g.}(A) mod out the finite dimensional elements.

## Lecture 15

**Statement 85 — Proposition 22.**
Pic(X) = Div_C(X) / im(K^*).

**Statement 86 — Theorem 15.1.**
When X is locally factorial, Div_W(X) = Div_C(X).

**Statement 87 — Proposition 23.**
(1) k[[x_1, ..., x_n]] is a UFD. (2) If A is a Noetherian local ring such that its completion is a UFD, then A itself is a UFD.

**Statement 88 — Theorem 14.1.**
When X is factorial, DW(X) = DC(X). Generally, Pic(X) = DC(X)/K^*.

**Statement 89 — Proposition 24.**
The degree of a principal divisor is zero (on an irreducible complete curve).

**Statement 90 — Proposition 25.**
X irreducible curve, deg(D) = 0 if D is a principal divisor.

## Lecture 16

**Statement 91 — Theorem 16.1 (Bezout's Theorem).**
Sum_{x in X intersect Y} mult_x(X,Y) = deg(X) deg(Y) for curves X, Y in P^2 without common components.

**Statement 92 — Corollary 20.**
For X, Y curves in P^2, the intersection multiplicity is greater than 1 if either X or Y is not smooth at x.

## Lecture 17

**Statement 93 — Theorem 17.1.**
X can be reconstructed from the lattice H_1(X, Z) in Gamma(Omega^1)^*.

**Statement 94 — Proposition 26.**
Pic^0(X) is itself a complex variety as well as a compact abelian Lie group.

**Statement 95 — Theorem 17.2.**
Let g be the genus of X and assume g = 1. Fix x_0 in X. The Abel-Jacobi map X -> Pic^0(X) sending x to x - x_0 is an isomorphism.

**Statement 96 — Corollary 21.**
Every normal curve of genus 1 has a group structure (elliptic curves).

**Statement 97 — Proposition 27.**
A non-constant map between irreducible compact curves is finite.

**Statement 98 — Proposition 28.**
There exists a variety Y along with a finite map f: Y -> X such that for every affine open U in X, k[f^{-1}(U)] = integral closure of k[U] in E (normalization).

**Statement 99 — Corollary 22.**
Given f: X -> Y where X, Y are irreducible, if X is normal and f is finite and onto, then X can be reconstructed from Y and f^{-1}(U) for some open U.

**Statement 100 — Lemma 28.**
If f: X -> Y is a map of irreducible curves, suppose f is onto, birational, Y is normal, then f is an isomorphism.

**Statement 101 — Lemma 29.**
Suppose X -> Y is birational, X is complete, Y is normal, then X is isomorphic to Y.

## Lecture 18

**Statement 102 — Lemma 30.**
dim(T_x^* X) >= dim_x(X).

**Statement 103 — Proposition 29.**
X is smooth at x if and only if Omega_X is locally free on a neighborhood of x.

**Statement 104 — Proposition 30.**
For a variety X, the set of smooth points in X is open and dense in X.

## Lecture 19

**Statement 105 — Corollary 23.**
(1) If X in A^n is a hypersurface given by I_X = (P), then x in X is smooth iff dP|_x != 0. (2) If X in A^n has dimension n-m with I_X = (f_1, ..., f_m), then X is smooth at x iff df_i|_x are linearly independent.

**Statement 106 — Proposition 31.**
Suppose X in A^n, x in X is a smooth point iff there exist f_1, ..., f_m in I_X which locally generate I_X and df_i|_x are linearly independent.

**Statement 107 — Lemma 31.**
The completed local ring at a smooth point is isomorphic to k[[t_1, ..., t_{n-m}]].

**Statement 108 — Lemma 32.**
Let A be a ring, m a maximal ideal. If a-bar is not a zero divisor in the associated graded ring, then the associated graded of A/(a) equals the associated graded of A modulo (a-bar).

**Statement 109 — Proposition 32.**
X is smooth at x iff the completed local ring O_{X,x}-hat is isomorphic to k[[t_1, ..., t_d]] where d = dim_x X.

**Statement 110 — Proposition 33.**
(1) For Z closed in X, there is an exact sequence I_Z/I_Z^2 -> Omega_X|_Z -> Omega_Z -> 0. (2) If I_Z is locally generated by f_1, ..., f_m with linearly independent differentials, then the sequence is short exact.

**Statement 111 — Corollary 24 (Adjunction Formula).**
omega_D = omega_X(-D)|_D.

**Statement 112 — Proposition 34.**
The tangent cone is the cone over the exceptional locus in the blowup at x.

## Lecture 20

**Statement 113 — Proposition 35.**
(1) If Z in X closed, I_Z/I_Z^2 -> Omega_X|_Z -> Omega_Z -> 0. (2) If I_Z locally generated by functions with linearly independent differentials, the sequence is exact at left.

**Statement 114 — Corollary 25.**
X smooth, Z in X closed, then Z is smooth iff locally Z is given by equations with linearly independent differentials.

**Statement 115 — Corollary 26.**
If X, Z smooth, Z closed in X: s.e.s. 0 -> I_Z/I_Z^2 -> Omega_X|_Z -> Omega_Z -> 0, and K_X(D)|_D = K_D (adjunction formula).

**Statement 116 — Proposition 36.**
There is a s.e.s. 0 -> Omega_{P^n} -> O(-1)^{n+1} -> O -> 0. Corollary: K_{P^n} = O(-(n+1)).

**Statement 117 — Proposition 37.**
T_{Gr(k,n)} = Hom(V, W tensor O / V) and Omega_{Gr(k,n)} = Hom(W tensor O / V, V).

**Statement 118 — Proposition 38.**
Let E be the exceptional locus over x when blowing up X at x. Then the cone of E is the tangent cone Spec(oplus m_x^n/m_x^{n+1})_{red}. If x is smooth, the associated graded is Sym(T_x^* X).

## Lecture 21

**Statement 119 — Theorem 21.1 (Riemann-Hurwitz Formula).**
Let f: X -> Y be a morphism of smooth irreducible curves with k(X)/k(Y) separable. Then f^* K_Y(R) is isomorphic to K_X where R = sum_{x in X} (d_x - 1)x.

**Statement 120 — Corollary 27.**
If X, Y are complete then deg K_X = n * deg K_Y + sum_{x in X} (d_x - 1).

**Statement 121 — Proposition 39.**
Let X be a normal irreducible affine variety and Z a closed subvariety with dim Z <= dim X - 2. Then k[X] = k[X \ Z].

## Lecture 21 (cont.) / Lecture 22

**Statement 122 — Theorem 21.2 (Chevalley's Theorem).**
Let f: X -> Y be a morphism of varieties. Then im(f) is constructible. Furthermore, if X, Y are irreducible and im(f) is dense, then the fiber dimension function is upper semi-continuous.

**Statement 123 — Lemma 33.**
Let f: X -> Y be a morphism of irreducible affine varieties with im(f) dense. Then there is a nonempty open U in Y such that f^{-1}(U) -> U factors as finite onto followed by projection from U x A^n.

**Statement 124 — Theorem 22.1 (Bertini's Theorem).**
Let X in PV be a smooth subvariety. Then for a generic hyperplane H, Y = X intersect H is again smooth.

**Statement 125 — Corollary 28.**
A generic hypersurface of degree d is smooth. Moreover, if X in P^n is smooth, for a generic hypersurface S of degree d, S intersect X is smooth.

## Lecture 22 (cont.)

**Statement 126 — Proposition 40.**
delta (the degree function) is a well-defined homomorphism on K^0(Coh(X)).

**Statement 127 — Lemma 34.**
If 0 -> E -> E' -> T -> 0 with T torsion and the other two torsion free, then deg(E') = deg(E) + length(T).

## Lecture 23

**Statement 128 — Proposition 41 (Grothendieck).**
A delta-functor (F^i) for given F is universal provided that F^i for i > 0 is effaceable.

**Statement 129 — Proposition 42 (Snake Lemma).**
A short exact sequence of complexes yields a long exact sequence of cohomology.

**Statement 130 — Proposition 43.**
There is always a canonical map H^i(F(C)) -> R^i F(M); moreover, it is an isomorphism if M^i are adjusted to F.

**Statement 131 — Proposition 44.**
If f is affine and F is quasicoherent, then H^i(f_* F) = H^i(F).

## Lecture 24

**Statement 132 — Theorem 24.1 (Grothendieck-Birkhoff).**
A locally free coherent sheaf of rank n on P^1 is isomorphic to direct sum of O_{P^1}(d_i) for a unique collection d_i.

**Statement 133 — Theorem 24.2 (Riemann-Roch for Curves).**
Let X be an irreducible complete smooth curve. Then chi(F) = deg(F) - rank(F)(g_a - 1) where g_a = dim H^1(O).

**Statement 134 — Lemma 35.**
O(X) along with O_x generate K^0(Coh(X)) for a smooth curve X.

**Statement 135 — Theorem 24.3 (Serre Duality).**
If E is a locally free sheaf on a complete smooth irreducible curve, then Gamma(E)^* is canonically isomorphic to H^1(E^{vee} tensor K_X).

## Lecture 25

**Statement 136 — Lemma 36.**
Suppose X is a complete smooth curve, omega in Gamma(U, Omega), U is a nontrivial open subset. Then sum_{x in X \ U} Res_{x_i} omega = 0.

**Statement 137 — Corollary 29.**
g_a = g_m (arithmetic genus equals geometric genus for smooth curves).

**Statement 138 — Corollary 30.**
Riemann-Roch implies dim(Gamma(E)) - dim(Gamma(K tensor E^*)) = deg(E) + rank(E)(1-g). (Riemann's form)

**Statement 139 — Corollary 31.**
deg(K) = 2g - 2 for a smooth complete curve of genus g.
