# Detailed Assessment: Mathlib Coverage of "Rational Points on Elliptic Curves"

## Statement 1: Proposition (Bezout's Theorem for Plane Curves)
**Status**: not included
Bezout's theorem for projective plane curves (intersection multiplicity) is not formalized in mathlib. While Mathlib has polynomial ring machinery and some algebraic geometry, it does not have a general Bezout theorem for projective plane curves counting intersection multiplicities.

## Statement 2: Proposition (Group Law on Cubic Curve)
**Status**: included
Corresponds to the instance `WeierstrassCurve.Affine.Point.instAddCommGroup` in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`. This proves that nonsingular points W(F) on a Weierstrass curve form an abelian group under the chord-and-tangent law.

## Statement 3: Proposition (Addition Formula for Elliptic Curves)
**Status**: included
Corresponds to the definitions and lemmas in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`, specifically `WeierstrassCurve.Affine.addX`, `WeierstrassCurve.Affine.addY`, and the slope definitions in `WeierstrassCurve.Affine.slope`. The general Weierstrass form addition formulas are given there.

## Statement 4: Proposition (Associativity of the Group Law)
**Status**: included
Proved as part of the `AddCommGroup` instance in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`. The associativity is established via the ideal class group approach.

## Statement 5: Proposition (Complex Torus and Elliptic Curves)
**Status**: not included
The uniformization of elliptic curves by complex tori C/L is not formalized in mathlib. While `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` exists, it deals with the Weierstrass elliptic function as an analytic object, not the full uniformization theorem.

## Statement 6: Theorem (Weierstrass p-function Uniformization)
**Status**: not included
The statement that u -> (P(u), P'(u)) gives an isomorphism from C/L to the elliptic curve is not in mathlib. The Weierstrass p-function is partially formalized but not its connection to elliptic curves as an algebraic isomorphism.

## Statement 7: Proposition (Transformation to Short Weierstrass Form)
**Status**: included
Corresponds to `WeierstrassCurve.exists_variableChange_isShortNF` in `Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean`, which shows that when 2 and 3 are invertible, any Weierstrass curve can be transformed to y^2 = x^3 + a4*x + a6. Also `WeierstrassCurve.exists_variableChange_isCharNeTwoNF` for characteristic != 2.

## Statement 8: Proposition (Discriminant and Nonsingularity)
**Status**: included
Corresponds to `WeierstrassCurve.Affine.equation_iff_nonsingular` in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean` and the `WeierstrassCurve.IsElliptic` typeclass in `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`, which asserts that the discriminant Delta is a unit.

## Statement 9: Proposition (Nagell-Lutz Theorem)
**Status**: not included
The Nagell-Lutz theorem is not formalized in mathlib. There is no file or lemma corresponding to this classical result about torsion points having integer coordinates with y^2 | D.

## Statement 10: Proposition (Height Function - Finiteness)
**Status**: not included
Height functions on elliptic curves are not formalized in mathlib. There is no machinery for naive or canonical heights on rational points.

## Statement 11: Lemma (Height and Translation)
**Status**: not included
No height function theory exists in mathlib for elliptic curves.

## Statement 12: Lemma (Height and Duplication)
**Status**: not included
No height function theory exists in mathlib for elliptic curves.

## Statement 13: Theorem (Mordell's Theorem)
**Status**: not included
The Mordell-Weil theorem (finite generation of the group of rational points on an elliptic curve over Q) is not formalized in mathlib. This is one of the major open formalization targets in arithmetic geometry.

## Statement 14: Lemma (Finiteness of Gamma/2Gamma)
**Status**: not included
The weak Mordell-Weil theorem (finiteness of E(Q)/2E(Q)) is not formalized in mathlib.

## Statement 15: Proposition (2-Isogeny phi)
**Status**: not included
The explicit 2-isogeny for curves of the form y^2 = x^3 + ax^2 + bx with a rational 2-torsion point is not formalized in mathlib. Mathlib has general Weierstrass curve machinery but not specific isogeny constructions.

## Statement 16: Proposition (Dual Isogeny and Composition)
**Status**: not included
Dual isogenies are not formalized in mathlib. There is no general theory of isogenies between elliptic curves.

## Statement 17: Proposition (Image of phi and Kernel)
**Status**: not included
The kernel and image characterization of the 2-isogeny are not in mathlib.

## Statement 18: Proposition (Homomorphism lambda to Q*/Q*^2)
**Status**: not included
The x-coordinate map modulo squares used in 2-descent is not formalized in mathlib.

## Statement 19: Proposition (Bound on Image of lambda)
**Status**: not included
The bound on the image of the descent map in terms of prime divisors is not formalized.

## Statement 20: Lemma (Index Bound from Two Isogenies)
**Status**: not included
This abstract lemma about indices in abelian groups with paired homomorphisms is not in mathlib in this specific form, though mathlib has extensive abelian group theory.

## Statement 21: Proposition (Structure of Gamma/2Gamma for Finitely Generated Abelian Groups)
**Status**: not included
While mathlib has the structure theorem for finitely generated abelian groups in various forms, this specific formula (Gamma : 2Gamma) = 2^rank * #Gamma[2] is not stated as a standalone lemma in this form.

## Statement 22: Proposition (Descent Theorem)
**Status**: not included
The descent argument combining the height lemmas and finiteness of E(Q)/2E(Q) to prove finite generation is not formalized.

## Statement 23: Claim (Nonsingular Points on Singular Cubic Form a Group)
**Status**: not included
The group structure on nonsingular points of a singular cubic is not formalized in mathlib. Mathlib focuses on nonsingular (elliptic) curves.

## Statement 24: Lemma (Line Through Singular Point)
**Status**: not included
This intersection multiplicity result for lines through singular points is not formalized.

## Statement 25: Claim (Node Case - Isomorphism with Multiplicative Group)
**Status**: not included
The explicit isomorphism between the group of nonsingular points on a nodal cubic and the multiplicative group is not formalized.

## Statement 26: Theorem (Hasse-Weil Bound for Elliptic Curves over Finite Fields)
**Status**: not included
The Hasse-Weil bound |#E(F_q) - q - 1| <= 2*sqrt(q) (or 2g*sqrt(q) for genus g) is not formalized in mathlib. This is a major result in arithmetic geometry that remains unformalized.

## Statement 27: Theorem (Gauss's Theorem on Fermat Cubic)
**Status**: not included
Gauss's theorem on the number of projective solutions to X^3 + Y^3 + Z^3 = 0 over F_p, relating it to the representation 4p = A^2 + 27B^2, is not in mathlib. While mathlib has Gauss sums (`Mathlib/NumberTheory/GaussSum.lean`) and Jacobi sums (`Mathlib/NumberTheory/JacobiSum/Basic.lean`), this specific application is not formalized.

## Statement 28: Fact (Multiplicative Group of Finite Field is Cyclic)
**Status**: included
Corresponds to the instances for `IsCyclic (ZMod p)^*` in `Mathlib/RingTheory/ZMod/UnitsCyclic.lean`, specifically `ZMod.instIsCyclicUnitsOfPrime` which proves that (Z/pZ)* is cyclic for prime p.

## Statement 29: Theorem (Reduction Modulo p is Injective on Torsion)
**Status**: not included
While `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` contains definitions for reduction of Weierstrass curves (minimal models, good/bad reduction), the specific result that the reduction map is injective on the torsion subgroup is not proven there.

## Statement 30: Theorem (Fermat's Little Theorem)
**Status**: included
Corresponds to `ZMod.pow_card_sub_one_eq_one` and related lemmas in `Mathlib/FieldTheory/Finite/Basic.lean`, which state that for p prime and a not divisible by p, a^(p-1) = 1 mod p. Also `Int.emod_pow_succ_self` and `Nat.Coprime.pow_card_sub_one_eq_one_mod`.

## Statement 31: Proposition (Euclidean Algorithm Complexity)
**Status**: not included
The complexity bound of O(log b) for the Euclidean algorithm is not formalized in mathlib. While mathlib has the Euclidean algorithm itself (GCD computations), it does not contain complexity analysis.

## Statement 32: Proposition (Bound on Solutions of x^3 + y^3 = m)
**Status**: not included
This elementary bound on solutions of the sum-of-cubes equation is not formalized.

## Statement 33: Proposition (Infinitely Many Integer Points for x^3 + y^3 = m)
**Status**: not included
This existence result for m with many integer points on x^3 + y^3 = m is not formalized.

## Statement 34: Theorem (Silverman's Bound on Integer Points)
**Status**: not included
Silverman's result bounding the number of coprime integer points on x^3 + y^3 = m in terms of rank is not formalized.

## Statement 35: Theorem (Thue's Theorem)
**Status**: not included
Thue's theorem that ax^3 + by^3 = c has finitely many integer solutions is not in mathlib. This is a major result in Diophantine equations that remains unformalized.

## Statement 36: Theorem (Diophantine Approximation Theorem)
**Status**: not included
The Diophantine approximation result |p/q - beta| <= C/q^3 having only finitely many solutions (for beta an algebraic number of degree 3) is not in mathlib. `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` contains some Diophantine approximation results but not this specific Thue-Siegel type bound.

## Statement 37: Lemma (Siegel's Lemma)
**Status**: included
Corresponds to `exists_ne_zero_int_vec_norm_le` in `Mathlib/NumberTheory/SiegelsLemma.lean`. This provides the existence of a nonzero integer solution to a homogeneous linear system with a bound on the solution's norm.

## Statement 38: Proposition (Congruent Number Characterization)
**Status**: not included
The equivalence between n being a congruent number and the existence of x in Q with x, x-n, x+n all squares (equivalently, E_n having positive rank) is not formalized in mathlib.

## Statement 39: Theorem (Congruent Number and Rank of E_n)
**Status**: not included
The characterization of congruent numbers via the rank of E_n: y^2 = x^3 - n^2*x is not in mathlib.

## Statement 40: Theorem (Points of Finite Order on E_n)
**Status**: not included
The determination that the torsion subgroup of E_n(Q) is {O, (0,0), (n,0), (-n,0)} = Z/2Z x Z/2Z is not formalized. While this could in principle follow from Nagell-Lutz (itself not formalized), it is not in mathlib.

## Statement 41: Proposition (E_n over F_q for q = 3 mod 4)
**Status**: not included
The result that #E_n(F_q) = q + 1 when q = 3 mod 4 and p does not divide 2n is not formalized. This uses the fact that -1 is not a square in F_q when q = 3 mod 4.

## Statement 42: Proposition (Doubling Criterion via Squares)
**Status**: not included
The criterion for P to be in 2E(R) in terms of x0 - e_i being perfect squares is not formalized in mathlib.
