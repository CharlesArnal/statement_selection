Theorem 1.2 [Baker's Theorem]:
non-included
Baker's theorem relates the genus of a function field defined by an irreducible polynomial f(x,y) to the number of interior lattice points of the Newton polygon of f. Searched mathlib for Newton polygon and genus computations in AlgebraicGeometry/ and RingTheory/. Mathlib has some Newton polygon machinery in RingTheory/NewtonPolygon but nothing connecting it to genus. The genus computation for algebraic curves is not formalized in mathlib.

Proposition 1.5:
non-included
States that for a nondegenerate irreducible polynomial whose homogenization has no singularities outside certain coordinate points, the genus equals the number of interior lattice points. This is a refinement of Baker's theorem. The same reasoning as Theorem 1.2 applies: genus computations from Newton polygons are not in mathlib.

Theorem 3.3:
included
States that F_p is a field and every field of cardinality p is isomorphic to F_p. Mathlib formalizes this via `ZMod.instField` in Mathlib/Data/ZMod/Basic.lean, which shows ZMod p is a field when p is prime. The uniqueness up to isomorphism for fields of prime cardinality follows from `FiniteField.algEquivGaloisField` in Mathlib/FieldTheory/Finite/GaloisField.lean.

Theorem 3.6:
included
States that F_q has cardinality q and every field of cardinality q is isomorphic to F_q. In mathlib, `GaloisField p n` is defined in Mathlib/FieldTheory/Finite/GaloisField.lean as the splitting field of X^(p^n) - X over ZMod p. The theorem `GaloisField.card` confirms it has p^n elements, and `GaloisField.algEquivGaloisField` provides the isomorphism for any finite field of the same cardinality.

Theorem 3.8:
included
States F_{p^m} is a subfield of F_{p^n} iff m | n. This is essentially captured in mathlib via the subfield embedding theory for finite fields. The Galois field framework in Mathlib/FieldTheory/Finite/GaloisField.lean together with the general finite field theory handles this through the degree divisibility conditions.

Theorem 3.9:
included
States that F_p[x]/(f) is isomorphic to F_{p^n} for irreducible f of degree n. This follows from the definition of `GaloisField` as a splitting field and the general theory of finite field extensions. In mathlib, this is a consequence of `AdjoinRoot.instField` combined with the uniqueness of finite fields of given cardinality from `GaloisField.algEquivGaloisField`.

Corollary 3.10:
included
Every irreducible f in F_p[x] of degree n splits completely in F_{p^n}. This follows from the fact that GaloisField p n is defined as the splitting field of X^(p^n) - X, which contains all roots of every irreducible polynomial of degree dividing n. The splitting behavior is part of the Galois field construction in Mathlib/FieldTheory/Finite/GaloisField.lean.

Theorem 3.12:
included
Every finite subgroup of the multiplicative group of a field is cyclic. This is formalized as `isCyclic_of_subgroup_isDomain` in Mathlib/RingTheory/IntegralDomain.lean, which proves that a finite subgroup of the units of an integral domain is cyclic.

Corollary 3.13:
included
The multiplicative group of a finite field is cyclic. This is an instance declaration in Mathlib/RingTheory/IntegralDomain.lean: `instance [Finite Rx] : IsCyclic Rx`.

Theorem 3.15:
non-included
States that primitive polynomials of degree n in F_p[x] exist and their count is phi(p^n - 1)/n. While mathlib has the Euler totient function and cyclotomic polynomial theory, the specific count of primitive polynomials over finite fields is not formalized. Searched Mathlib/FieldTheory/Finite/ and found no such counting result.

Lemma 3.20:
included
An irreducible polynomial f in k[x] is inseparable iff f' = 0. This is captured in mathlib's separability theory. In Mathlib/FieldTheory/Separable.lean, the definition of `Polynomial.Separable` and related lemmas connect separability to the derivative being coprime, and the characterization of inseparability via the derivative being zero for irreducible polynomials follows.

Theorem 3.22:
included
Finite fields are perfect (every irreducible polynomial is separable). The perfectness of finite fields is established through the separable degree theory and the Frobenius endomorphism. In Mathlib/FieldTheory/IsPerfectClosure.lean and Mathlib/FieldTheory/SeparableDegree.lean, the machinery for perfect fields is present, and finite fields are shown to be perfect.

Theorem 3.24:
non-included
States the time complexity of adding/subtracting elements of F_q is O(n). This is a computational complexity statement about algorithms, not a pure mathematical theorem. Mathlib does not formalize computational complexity bounds for field arithmetic.

Theorem 3.29:
non-included
The DFT convolution theorem. This is an algorithmic/signal processing result. While mathlib has some Fourier analysis in Mathlib/Analysis/Fourier/, the discrete finite-field DFT convolution theorem for polynomial multiplication is not formalized.

Theorem 3.30:
non-included
Correctness of the FFT algorithm. This is an algorithmic correctness statement. Mathlib does not formalize algorithm correctness proofs for FFT.

Corollary 3.31:
non-included
Polynomial multiplication via FFT in O(n log n). This is a computational complexity result about polynomial multiplication algorithms. Not in mathlib.

Theorem 3.33:
non-included
Time complexity of multiplying elements of F_p. Computational complexity bound, not formalized in mathlib.

Theorem 3.35:
non-included
Time complexity of multiplying elements of F_q. Computational complexity bound, not formalized in mathlib.

Theorem 3.38:
non-included
Bit operation complexity of the long division algorithm. Computational complexity bound, not formalized in mathlib.

Theorem 3.40:
non-included
Time complexity of inverting an element of F_p^x. Computational complexity bound, not formalized in mathlib.

Theorem 3.41:
non-included
Time complexity of inverting an element of F_q^x. Computational complexity bound, not formalized in mathlib.

Theorem 3.44 [Rabin 1980]:
non-included
For distinct alpha, beta in F_q, exactly (q-1)/2 values of delta make alpha+delta and beta+delta of different type (quadratic residue vs non-residue). Searched Mathlib/NumberTheory/LegendreSymbol/ and Mathlib/FieldTheory/Finite/. This specific counting result about shifting quadratic residues is not formalized.

Theorem 4.15:
non-included
Every rational map from a smooth projective curve to a projective curve is a morphism. This is a fundamental result in algebraic geometry. While mathlib has algebraic geometry machinery in Mathlib/AlgebraicGeometry/, the specific theory of curves and the regularity theorem for rational maps on smooth curves is not yet formalized.

Theorem 4.17:
non-included
A morphism of projective curves is either surjective or constant. This is a standard result in algebraic curve theory. Mathlib's algebraic geometry library does not yet have the theory of projective curves developed to this level.

Lemma 4.26:
non-included
Standard form for isogenies of elliptic curves y^2 = f(x). Searched Mathlib/AlgebraicGeometry/EllipticCurve/ and found IsogenyMap.lean but no formalization of the standard form decomposition of isogenies into rational functions of this type.

Lemma 4.27:
non-included
Divisibility relations between denominators in the standard form of an isogeny. This is a specialized result about the structure of isogenies. Not found in Mathlib/AlgebraicGeometry/EllipticCurve/.

Corollary 4.28:
non-included
Kernel points of an isogeny correspond to roots of v(x). Specialized EC isogeny result not in mathlib. Searched Mathlib/AlgebraicGeometry/EllipticCurve/; no kernel characterization of this type found.

Corollary 4.29:
non-included
The kernel of an isogeny is a finite subgroup of E_1(k-bar). Searched Mathlib/AlgebraicGeometry/EllipticCurve/ and found no formalization of isogeny kernels as finite subgroups.

Theorem 4.34:
included
Every transcendence basis for L/k has the same cardinality. This is formalized in mathlib via the theory of algebraic independence. In Mathlib/RingTheory/AlgebraicIndependent/RankAndCardinality.lean, the cardinality of transcendence bases is shown to be an invariant.

Theorem 4.45 [Hilbert Basis Theorem]:
included
If R is noetherian then so is R[x]. Formalized as `Polynomial.isNoetherianRing` in Mathlib/RingTheory/Polynomial/Basic.lean, explicitly labeled "Hilbert basis theorem" in the docstring.

Lemma 4.48:
included
The radical sqrt(I) of an ideal I is an ideal. In mathlib, the radical of an ideal is defined as `Ideal.radical` in Mathlib/RingTheory/Ideal/Operations.lean and is shown to be an ideal by construction.

Theorem 4.49 [Hilbert's Nullstellensatz]:
included
I(Z_I) = sqrt(I) for ideals in k-bar[x_1,...,x_n]. Formalized as `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` in Mathlib/RingTheory/Nullstellensatz.lean.

Theorem 4.50 [Weak Nullstellensatz]:
included
Every proper ideal of k-bar[x_1,...,x_n] has a nonempty zero locus. This follows from the Nullstellensatz formalization in Mathlib/RingTheory/Nullstellensatz.lean.

Corollary 4.51:
included
Maximal ideals of k-bar[x_1,...,x_n] are of the form (x_1-P_1,...,x_n-P_n). This is a direct consequence of the Nullstellensatz and is covered by the maximal ideal characterization in Mathlib/RingTheory/Nullstellensatz.lean.

Corollary 4.52:
included
Inclusion-reversing bijection between radical ideals and algebraic sets. The Galois connection `zeroLocus_vanishingIdeal_galoisConnection` in Mathlib/RingTheory/Nullstellensatz.lean establishes this correspondence.

Theorem 4.55:
included
An algebraic set is irreducible iff its ideal is prime. The correspondence between prime ideals and irreducible closed sets is part of the spectrum theory in Mathlib/AlgebraicGeometry/PrimeSpectrum/ and follows from the Nullstellensatz machinery.

Lemma 5.1:
non-included
For coprime u,v in k[x], (u/v)' = 0 iff u' = v' = 0 iff u,v are polynomials in x^p. This is a specific lemma about derivatives of rational functions over fields of positive characteristic. Not found in mathlib's elliptic curve or field theory libraries.

Corollary 5.2:
non-included
Over characteristic zero, every isogeny is separable. Searched Mathlib/AlgebraicGeometry/EllipticCurve/ for separability of isogenies; no such formalization found.

Lemma 5.3:
non-included
An inseparable isogeny over characteristic p > 0 can be written as (a(x^p), b(x^p)y^p). This is a specialized EC result about the structure of inseparable isogenies. Not in mathlib.

Corollary 5.4:
non-included
Decomposition of isogenies into separable part composed with Frobenius powers, with degree multiplicativity. Searched Mathlib/AlgebraicGeometry/EllipticCurve/ and Mathlib/Algebra/CharP/Frobenius.lean. The Frobenius endomorphism is in mathlib but its application to isogeny decomposition on elliptic curves is not.

Theorem 5.8:
non-included
The order of the kernel of an isogeny equals its separable degree. This is a fundamental result in isogeny theory not yet formalized in mathlib's EC library.

Corollary 5.9:
non-included
Every purely inseparable isogeny has trivial kernel. Follows from Theorem 5.8. Not in mathlib.

Corollary 5.10:
non-included
Multiplicativity of degree, separable degree, and inseparable degree under composition of isogenies. Not formalized in mathlib's EC library.

Theorem 5.11:
non-included
Existence and uniqueness (up to isomorphism) of a separable isogeny with prescribed finite kernel subgroup. This is a deep result about quotients of elliptic curves by finite subgroups. Not in mathlib.

Corollary 5.12:
non-included
Isogenies of composite degree decompose into sequences of prime-degree isogenies. Not in mathlib.

Theorem 5.13 [Velu]:
non-included
Explicit formulas for degree-2 separable isogenies via Velu's formulas. Searched Mathlib/AlgebraicGeometry/EllipticCurve/ for "Velu" or "velu"; not found. The IsogenyMap.lean file exists but does not contain Velu's formulas.

Theorem 5.15 [Velu]:
non-included
Explicit formulas for odd-degree separable isogenies via Velu's formulas. Same reasoning as Theorem 5.13; not in mathlib.

Lemma 5.20:
non-included
Ring membership of division polynomials psi_n, phi_n, omega_n. Mathlib has division polynomials in Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean but the specific ring membership characterization is not explicitly stated in the form given.

Theorem 5.21:
non-included
The multiplication-by-n map expressed via division polynomials. While mathlib has division polynomials defined, the explicit connection to the multiplication-by-n endomorphism is not yet formalized. Searched Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/ and Group.lean.

Lemma 5.22:
non-included
Leading terms of phi_n and psi_n. Mathlib has Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean which contains degree results but the specific leading term characterizations may not match exactly.

Corollary 5.23:
non-included
Leading term of psi_n^2(x). Related to the degree results in DivisionPolynomial/Degree.lean but the specific formulation is not present.

Lemma 5.24:
non-included
Coprimality of phi_n(x) and psi_n^2(x). Not found in mathlib's division polynomial files.

Theorem 5.25:
non-included
The multiplication-by-n map has degree n^2 and is separable iff char(k) does not divide n. Searched Mathlib/AlgebraicGeometry/EllipticCurve/ for degree of multiplication map; not found.

Theorem 6.1:
non-included
Structure of E[l^e] as (Z/l^e Z)^2 for l != p and Z/l^e Z or {0} for l = p. This is a fundamental structural theorem about torsion subgroups of elliptic curves. Searched Mathlib/AlgebraicGeometry/EllipticCurve/ for torsion structure; not found.

Corollary 6.4:
non-included
Every finite subgroup of E(k-bar) is isomorphic to (Z/mZ)+(Z/nZ) with m|n. Not in mathlib.

Proposition 6.5:
non-included
[n] o alpha = n*alpha = alpha o [n] for isogenies. This is about the interaction of the multiplication-by-n map with isogenies in the endomorphism ring. Not formalized in mathlib.

Lemma 6.6:
non-included
Cancellation of isogenies in compositions. Not in mathlib's EC library.

Theorem 6.7 [Dual Isogeny]:
non-included
Existence and uniqueness of the dual isogeny alpha-hat with alpha-hat o alpha = [n]. Searched for "dualIsogeny", "dual_isogeny" in mathlib; not found.

Lemma 6.10:
non-included
Properties of the dual: alpha o alpha-hat = [n], [n]-hat = [n]. Not in mathlib.

Lemma 6.11:
non-included
Dual of a sum equals sum of duals. Not in mathlib.

Lemma 6.12:
non-included
Dual of a composition reverses order: (alpha o beta)-hat = beta-hat o alpha-hat. Not in mathlib.

Lemma 6.16:
non-included
alpha + alpha-hat = 1 + deg(alpha) - deg(1-alpha) is an integer. Endomorphism ring identity, not in mathlib.

Theorem 6.18:
non-included
Characteristic equation lambda^2 - (tr alpha)*lambda + deg alpha = 0 for endomorphisms. Not in mathlib.

Lemma 6.19:
non-included
Endomorphism equality detection via action on n-torsion. Not in mathlib.

Theorem 6.20:
non-included
Trace and degree of endomorphisms detected modulo n on n-torsion. Not in mathlib.

Lemma 7.1:
non-included
If alpha is inseparable and beta is any isogeny, alpha + beta is inseparable iff beta is inseparable. Specialized EC result, not in mathlib.

Theorem 7.3 [Hasse]:
non-included
#E(F_q) = q+1-t with |t| <= 2*sqrt(q) (Hasse bound). Searched mathlib for "Hasse", "hasse_bound", "hasseWeil" in AlgebraicGeometry/EllipticCurve/ and NumberTheory/. The Hasse bound for elliptic curves is not yet formalized in mathlib.

Theorem 7.6:
non-included
Probability that two random elements of a finite abelian group generate a subgroup whose order equals the exponent. This is a group-theoretic probabilistic result. Not in mathlib.

Theorem 7.7 [Mestre]:
non-included
For p > 229, at least one of E or its quadratic twist has a unique group order candidate in the Hasse interval. Specialized algorithmic/computational number theory result. Not in mathlib.

Lemma 8.2:
non-included
If P in E[l] is nonzero and satisfies pi_l^2(P) - c*pi_l(P) + q_l*P = 0, then c = tr(pi) mod l. This is about Schoof's algorithm for point counting. Not in mathlib.

Theorem 9.3:
non-included
Expected collision time for random walks: E[rho] ~ sqrt(pi*N/2). This is a probabilistic/combinatorial result about random functions on finite sets. Not in mathlib.

Theorem 9.7 [Shoup]:
non-included
Generic lower bound for the discrete logarithm problem: probability < s^2/(2p). This is a computational complexity/cryptographic lower bound. Not in mathlib.

Corollary 9.8:
non-included
Deterministic generic DLP algorithms need at least (sqrt(2)+o(1))*sqrt(N) operations. Computational complexity lower bound. Not in mathlib.

Corollary 9.9:
non-included
Monte Carlo generic DLP lower bound. Computational complexity result. Not in mathlib.

Corollary 9.10:
non-included
Las Vegas generic DLP lower bound. Computational complexity result. Not in mathlib.

Corollary 9.11:
non-included
Every generic Las Vegas DLP algorithm uses Omega(sqrt(N)) operations. Computational complexity result. Not in mathlib.

Theorem 10.6 [Canfield-Erdos-Pomerance]:
non-included
Asymptotic density of smooth numbers: (1/x)*psi(x, x^{1/u}) = u^{-u+o(u)}. This is a deep analytic number theory result. Searched Mathlib/NumberTheory/ for smooth numbers; not found.

Theorem 10.10:
non-included
Success condition for Pollard p-1 factoring algorithm. Algorithmic/computational result. Not in mathlib.

Theorem 10.12:
non-included
Success condition for ECM factoring algorithm. Algorithmic/computational result. Not in mathlib.

Theorem 10.14:
non-included
Montgomery curve torsion: either three rational 2-torsion points or a rational 4-torsion point. Specialized EC result about Montgomery curves. Searched Mathlib/AlgebraicGeometry/EllipticCurve/ for Montgomery; not found.

Theorem 10.15:
non-included
An elliptic curve with a rational 4-torsion point can be put in Montgomery form. Specialized EC result. Not in mathlib.

Theorem 11.2 [Fermat's Little Theorem]:
included
Formalized as `FiniteField.pow_card` in Mathlib/FieldTheory/Finite/Basic.lean: `theorem pow_card (a : K) : a ^ q = a`. Also present as `ZMod.pow_card`. The version a^(N-1) = 1 for a != 0 is `FiniteField.pow_card_sub_one_eq_one`.

Theorem 11.4 [Alford-Granville-Pomerance]:
non-included
The set of Carmichael numbers is infinite. This is a deep result in analytic number theory. Searched Mathlib/NumberTheory/ for Carmichael; not found.

Theorem 11.5:
included
N is prime iff phi(N) = N-1. The Euler totient function is in Mathlib/Data/Nat/Totient.lean. The characterization that phi(N) = N-1 iff N is prime is captured by `Nat.totient_prime` and the converse follows from the totient theory in mathlib.

Lemma 11.6:
non-included
For p = 2^s * t + 1 prime with t odd and nonzero a mod p, either a^t = 1 or a^{2^i * t} = -1 for some i. This is the core lemma behind the Miller-Rabin test. The specific characterization is not formalized in mathlib.

Theorem 11.8 [Monier-Rabin]:
non-included
For odd composite N, at least 3/4 of integers in [1,N-1] are Miller-Rabin witnesses. This is a result about primality testing algorithms. Not in mathlib.

Theorem 11.11 [Damgard-Landrock-Pomerance]:
non-included
Posterior probability bound for Miller-Rabin primality testing. Not in mathlib.

Theorem 11.13 [Goldwasser-Kilian]:
non-included
Foundational theorem for elliptic curve primality proving (ECPP). Not in mathlib.

Lemma 12.5:
non-included
Every element of A tensor_R B (where B is the fraction field of R) can be written as a pure tensor. Searched Mathlib/LinearAlgebra/TensorProduct/ for pure tensor characterizations over fraction fields. Not formalized in this form in mathlib.

Lemma 12.7:
non-included
Mathlib has no formal theory of endomorphism algebras End^0(E) of elliptic curves, let alone norm/degree maps on them. The endomorphism ring of elliptic curves is not developed in mathlib beyond basic isogeny structure.

Corollary 12.8:
non-included
Follows from Lemma 12.7; depends on End^0(E) theory absent from mathlib.

Lemma 12.9:
non-included
End^0(E) trace theory not in mathlib.

Lemma 12.10:
non-included
End^0(E) theory not in mathlib.

Corollary 12.11:
non-included
Rosati involution not defined in mathlib.

Lemma 12.13:
non-included
Mathlib has `Algebra.Quaternion` with basic quaternion algebra definitions but not this norm criterion for being a division ring.

Theorem 12.17:
non-included
Classification of End^0(E) as Q, imaginary quadratic field, or quaternion algebra. This is a deep result about endomorphism algebras of elliptic curves, not in mathlib.

Lemma 12.18:
non-included
Endomorphism algebra theory not developed in mathlib.

Corollary 12.20:
non-included
Consequence of the classification theorem. Not in mathlib.

Theorem 12.25:
included
Mathlib has `NumberField.RingOfIntegers` in Mathlib/NumberTheory/NumberField/ which establishes that the ring of integers of a number field is an integral domain and a free Z-module of the appropriate rank.

Theorem 12.26:
non-included
Mathlib defines ring of integers and has some order theory, but the statement that O_K is the unique maximal order is not stated in this exact form. The definition of `ringOfIntegers` in mathlib implicitly captures maximality but the explicit uniqueness statement is not present.

Theorem 12.27:
non-included
The classification of orders O = Z + f*O_K in quadratic fields is not in mathlib. Mathlib lacks theory of orders in number fields.

Theorem 13.2:
non-included
Being supersingular is an isogeny invariant. Mathlib has no theory of supersingular/ordinary curves.

Theorem 13.3:
non-included
E/F_q is supersingular iff tr(pi_E) = 0 mod p. Mathlib has no theory of supersingular/ordinary curves.

Corollary 13.4:
non-included
For E/F_p with p > 3, E is supersingular iff #E(F_p) = p+1. Mathlib has no theory of supersingular/ordinary curves.

Theorem 13.6:
non-included
End^0(E) = Q(pi_E) is an imaginary quadratic field when pi_E is not in Z. Not in mathlib.

Corollary 13.7:
non-included
End^0(E) is imaginary quadratic when n is odd or E is ordinary. Not in mathlib.

Theorem 13.8:
non-included
Z[pi_E] subset End(E) subset O_K for ordinary elliptic curves. Not in mathlib.

Theorem 13.12:
included
Corresponds to constructions in Mathlib/AlgebraicGeometry/EllipticCurve/ModelsWithJ.lean which constructs elliptic curves with prescribed j-invariant.

Theorem 13.13:
included
Corresponds to Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean and related files which handle variable changes (u, r, s, t) between Weierstrass models.

Theorem 13.14:
included
Corresponds to `exists_variableChange_of_j_eq` in Mathlib/AlgebraicGeometry/EllipticCurve/IsomOfJ.lean: if E.j = E'.j then there exists a variable change C with C * E = E'.

Theorem 13.16:
non-included
j(E) lies in F_{p^2} for supersingular E. Not in mathlib.

Theorem 13.18:
non-included
End^0(E_{k-bar}) is a quaternion algebra for supersingular E. Not in mathlib.

Theorem 13.19:
non-included
Quaternion End^0 implies supersingular. Not in mathlib.

Corollary 13.20:
non-included
Full characterization of supersingular/ordinary in terms of Frobenius trace and endomorphism algebra. Not in mathlib.

Theorem 14.13:
included
Mathlib has `MeasureTheory.integral_eq_sub_of_hasDeriv_right` and related FTC results in Mathlib/MeasureTheory/Integral/FundThmCalculus.lean. For complex contour integrals, Mathlib/MeasureTheory/Integral/CircleIntegral.lean provides relevant results.

Theorem 14.14 [Cauchy's Theorem]:
included
Mathlib/Analysis/Complex/CauchyIntegral.lean contains `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` and related Cauchy-Goursat theorems.

Theorem 14.16:
non-included
Mathlib has Cauchy integral formulas in CauchyIntegral.lean but a general residue theorem for meromorphic functions with arbitrary poles is not fully developed.

Theorem 14.17:
non-included
The generalized argument principle with g(z)*f'(z)/f(z) is not explicitly in mathlib.

Theorem 14.18:
non-included
Theory of elliptic functions (doubly periodic meromorphic functions) is not in mathlib.

Lemma 14.22:
non-included
Mathlib has Mathlib/NumberTheory/ModularForms/EisensteinSeries/Summable.lean which proves summability of Eisenstein series, but the result is only partially related to the convergence statement here. The exact form as stated is not present.

Theorem 14.24:
included
This is a consequence of results in Mathlib/Analysis/Complex/CauchyIntegral.lean and uniform convergence results. Mathlib has results of the `DifferentiableOn.of_tendstoUniformlyOn` type.

Theorem 14.25:
non-included
Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean defines Weierstrass p-function infrastructure but the full analytic theory (holomorphy, poles, meromorphic properties) is work in progress.

Theorem 14.26:
non-included
The Weierstrass elliptic function file has basic lattice infrastructure but not the full meromorphic/parity/pole analysis.

Corollary 14.27:
non-included
Order of wp and wp' as elliptic functions not in mathlib.

Theorem 14.28:
non-included
Laurent series of wp not in mathlib.

Theorem 14.29:
non-included
Differential equation wp'^2 = 4wp^3 - g_2 wp - g_3 not in mathlib.

Theorem 14.30 [Liouville's Theorem]:
included
Mathlib/Analysis/Complex/Liouville.lean contains `Differentiable.apply_eq_apply_of_bounded` and `Differentiable.exists_const_forall_eq_of_bounded`: bounded entire functions are constant.

Lemma 14.31:
non-included
Zeros of wp' not in mathlib.

Lemma 14.33:
non-included
Discriminant Delta(L) nonvanishing not in mathlib.

Theorem 15.1:
non-included
The isomorphism C/L -> E_L(C) via (wp, wp') is not in mathlib. The complex-analytic uniformization theory is entirely absent.

Theorem 15.5:
non-included
Homothetic lattices iff same j-invariant. Complex-analytic theory not in mathlib.

Corollary 15.6:
non-included
Homothetic iff isomorphic E. Not in mathlib.

Theorem 15.8:
non-included
j-function holomorphic on H with modular properties. Not in mathlib.

Lemma 15.9:
non-included
j(tau) = j(tau') iff SL_2(Z)-equivalent. Not in mathlib.

Lemma 15.10:
non-included
Fundamental domain for H/SL_2(Z). Not in mathlib.

Theorem 15.11:
non-included
j bijection from fundamental domain F to C. Not in mathlib.

Corollary 15.12 [Uniformization Theorem]:
non-included
For every E/C there exists a lattice L with E isomorphic to E_L. Not in mathlib.

Theorem 16.1:
non-included
Holomorphic maps of tori correspond to lattice inclusions. Not in mathlib.

Corollary 16.2:
non-included
Morphisms = lattice inclusions. Not in mathlib.

Lemma 16.3:
non-included
C(L) = C(wp, wp'). Not in mathlib.

Theorem 16.4:
non-included
Equivalent conditions for alpha*L1 subset L2. Not in mathlib.

Corollary 16.5:
non-included
End(E) = {alpha : alpha*L subset L}. Not in mathlib.

Corollary 16.7:
non-included
End(E) over C commutative. Not in mathlib.

Theorem 16.12:
non-included
cl(O) <-> homothety classes with End isomorphic to O. Not in mathlib.

Lemma 17.5:
non-included
Ideal norm equals absolute field norm for principal ideals. Not in mathlib for orders in imaginary quadratic fields.

Corollary 17.7:
non-included
N(alpha*a) = N(alpha)*Na. Not in mathlib.

Lemma 17.9:
non-included
Proper iff lambda*a proper. Not in mathlib.

Theorem 17.10:
non-included
Proper iff invertible for O-ideals. Not in mathlib.

Corollary 17.11:
non-included
cl(O) = invertible mod principal. Mathlib has Mathlib/RingTheory/ClassGroup.lean which defines the class group of a Dedekind domain, but this is for the maximal order only. The theory for non-maximal orders O is not in mathlib.

Corollary 17.12:
non-included
Norm multiplicative for proper ideals. Not in mathlib.

Theorem 17.14:
non-included
ker(phi_a) = E[a] and deg(phi_a) = Na. Not in mathlib.

Corollary 17.15:
non-included
E and aE isogenous of degree Na. Not in mathlib.

Theorem 17.18:
non-included
Unique imaginary quadratic order with given discriminant. Not in mathlib.

Lemma 17.19:
non-included
Sublattice inclusions. Not in mathlib.

Lemma 18.1:
non-included
Finiteness of gamma with gamma*A intersect B nonempty. Not in mathlib.

Lemma 18.2:
non-included
Neighborhoods with unique gamma. Not in mathlib.

Theorem 18.3:
non-included
X(1) compact Hausdorff. Mathlib has the upper half-plane and SL_2(Z) action but not the quotient construction.

Lemma 18.7:
non-included
Stabilizers in the fundamental domain. Not in mathlib.

Lemma 18.8:
non-included
Mathlib has the Schwarz lemma in Mathlib/Analysis/Complex/AbsMax.lean and related files, but this specific variant about holomorphic self-maps of the disk fixing a point is not directly stated in this form.

Theorem 18.9:
non-included
Complex structure on X(1). Not in mathlib.

Theorem 18.10:
non-included
X(1) genus 0. Not in mathlib.

Lemma 19.5:
non-included
q-expansions of g_2, g_3, Delta. Not in mathlib in this explicit form.

Corollary 19.6:
non-included
j = 1/q + 744 + ... with integer coefficients. Not in mathlib.

Theorem 19.8:
non-included
C(Gamma(1)) = C(j). Not in mathlib.

Lemma 19.9:
non-included
Meromorphic on Riemann sphere = rational. Not in mathlib.

Corollary 19.10:
non-included
Modular function holomorphic on H is polynomial in j. Not in mathlib.

Theorem 19.11:
non-included
C(Gamma) finite extension of C(j). Not in mathlib.

Theorem 19.13:
non-included
j_N modular function for Gamma_0(N). Not in mathlib.

Theorem 19.14:
non-included
Modular function field for Gamma_0(N). Not in mathlib.

Lemma 19.16:
non-included
Coset representatives for Gamma_0(N). Not in mathlib.

Theorem 19.17:
non-included
Phi_N in Z[X,Y]. Not in mathlib.

Lemma 19.18 [Hasse q-expansion principle]:
non-included
Not in mathlib.

Lemma 20.2:
non-included
Cyclic sublattices of prime index. Not in mathlib.

Theorem 20.3:
non-included
Phi_N(j1,j2) = 0 iff cyclic N-isogeny. Not in mathlib.

Theorem 20.4:
non-included
Modular polynomial over general fields. Not in mathlib.

Theorem 20.7:
non-included
Phi_N symmetric. Not in mathlib.

Lemma 20.9:
non-included
Leading term of Phi_N(X,X). Not in mathlib.

Theorem 20.11:
non-included
Infinitely many ideals of prime norm. Not in mathlib.

Theorem 20.12:
non-included
H_D has integer coefficients. Not in mathlib.

Corollary 20.13:
non-included
CM j-invariant is algebraic integer. Not in mathlib.

Theorem 20.14:
non-included
Psi: Gal(L/K) -> cl(O) injective. Not in mathlib.

Theorem 21.1 [First Main Theorem of CM]:
non-included
Not in mathlib.

Corollary 21.2:
non-included
H_D irreducible, Gal = cl(O). Not in mathlib.

Theorem 21.5:
non-included
Norm equation equivalences. Not in mathlib.

Lemma 21.6:
non-included
O_K-ideals of norm p. Not in mathlib.

Corollary 21.7:
non-included
Number of proper O-ideals of norm p. Not in mathlib.

Corollary 21.8:
non-included
Ring class field unramified. Not in mathlib.

Corollary 21.9:
non-included
CM curves reduce to ordinary. Not in mathlib.

Theorem 21.12 [Deuring]:
non-included
H_D splits in F_q. Not in mathlib.

Theorem 21.13 [Deuring lifting theorem]:
non-included
Not in mathlib.

Theorem 22.3:
non-included
End rings under l-isogeny. Not in mathlib.

Theorem 22.5:
non-included
Counts of horizontal/descending/ascending isogenies. Not in mathlib.

Lemma 22.6:
non-included
Ell_O(F_q) cardinality. Not in mathlib.

Corollary 22.7:
non-included
l-isogeny counts over F_q. Not in mathlib.

Corollary 22.8:
non-included
Ell_O(F_q) is cl(O)-torsor. Not in mathlib.

Theorem 22.11 [Kohel]:
non-included
Ordinary components are l-volcanoes. Not in mathlib.

Lemma 22.13:
non-included
Floor vertices degree <= 2. Not in mathlib.

Theorem 23.6:
non-included
Rational maps from smooth projective curves are morphisms. Mathlib has algebraic geometry infrastructure for schemes and morphisms but the specific classical statement for smooth projective curves is not cleanly stated.

Theorem 23.9:
non-included
Degree formula for morphisms of curves. Not in mathlib.

Corollary 23.10:
non-included
sum v_P(f) = 0. Not in mathlib.

Theorem 23.17:
non-included
Abel-Jacobi isomorphism. Not in mathlib.

Theorem 23.20 [Weil reciprocity]:
non-included
Not in mathlib.

Lemma 23.21:
non-included
Weil pairing well-defined. Not in mathlib.

Theorem 23.22:
non-included
Weil pairing bilinear alternating. Not in mathlib.

Lemma 23.24:
non-included
Miller function properties. Not in mathlib.

Corollary 23.25:
non-included
Miller algorithm O(log n). Not in mathlib.

Lemma 23.26:
non-included
Weil pairing via Miller functions. Not in mathlib.

Corollary 23.27:
non-included
e_n formula. Not in mathlib.

Theorem 23.29:
non-included
Weil pairing full properties. Not in mathlib.

Corollary 23.30:
non-included
E[n] subset E(k) implies mu_n subset k^x. Not in mathlib.

Corollary 23.31:
non-included
Order of e_n. Not in mathlib.

Lemma 23.33:
non-included
Embedding degree = least k with q^k = 1 mod n. Not in mathlib.

Theorem 24.1 [Taylor-Wiles]:
non-included
Semistable modularity. Far beyond current mathlib.

Theorem 24.2 [Breuil-Conrad-Diamond-Taylor]:
non-included
Full modularity. Far beyond current mathlib.

Theorem 24.8:
non-included
Dimension formulas for spaces of modular forms. Mathlib has definitions of modular forms but not dimension formulas.

Theorem 24.11:
non-included
Hecke operator properties. Hecke operators are not defined in mathlib.

Corollary 24.12:
non-included
Hecke operators commutative. Not in mathlib.

Corollary 24.13:
non-included
Hecke operator recurrences. Not in mathlib.

Theorem 24.14:
non-included
q-coefficients of T_p f. Not in mathlib.

Corollary 24.15:
non-included
a_m(T_n f) = a_{mn}(f). Not in mathlib.

Lemma 24.19:
non-included
Mathlib has the spectral theorem for self-adjoint operators in various forms in Mathlib/Analysis/InnerProductSpace/, but the specific formulation about simultaneous diagonalization of commuting Hermitian operators on finite-dimensional spaces may not be stated exactly this way.

Theorem 24.20:
non-included
Unique eigenform basis for S_k(Gamma_0(1)). Not in mathlib.

Theorem 24.21:
non-included
Unique newform basis for S_k^new. Not in mathlib.

Theorem 24.25 [Hecke]:
non-included
L-function analytic continuation. Not in mathlib.

Theorem 24.27:
non-included
Newform L-function Euler product. Not in mathlib.

Theorem 24.33 [Modularity Theorem]:
non-included
Not in mathlib.

Corollary 24.34:
non-included
L(E,s) analytic continuation. Not in mathlib.

Conjecture 24.35 [Weak BSD]:
non-included
Not in mathlib.

Conjecture 24.36 [Parity Conjecture]:
non-included
Not in mathlib.

Theorem 24.37 [Eichler-Shimura]:
non-included
Not in mathlib.

Theorem 24.38 [Faltings-Tate]:
non-included
Not in mathlib.

Corollary 24.39:
non-included
Isogenous iff same L-function. Not in mathlib.

Conjecture 25.1 [Serre's modularity conjecture]:
non-included
Not in mathlib.

Theorem 25.2 [Ribet]:
non-included
Not in mathlib.

Corollary 25.3:
non-included
Frey curve not modular. Not in mathlib.

Theorem 25.4 [Taylor-Wiles modularity lifting]:
non-included
Not in mathlib.

Theorem 25.5 [Langlands-Tunnel]:
non-included
Not in mathlib.

Theorem 25.6:
non-included
No semistable rational 15-isogeny. Not in mathlib.

Theorem 25.7 [Wiles 3-5 trick]:
non-included
Not in mathlib.

Theorem 25.8 [Wiles]:
non-included
Semistable => modular. Not in mathlib.

Corollary 25.9 [Fermat's Last Theorem]:
non-included
Mathlib has `FermatLastTheorem` as a definition in Mathlib/NumberTheory/FLT/Basic.lean, and has proved the cases n=3 and n=4. The full theorem is stated but not proved in mathlib.
