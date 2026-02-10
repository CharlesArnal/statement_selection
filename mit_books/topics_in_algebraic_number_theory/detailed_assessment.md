# Detailed Assessment: Topics in Algebraic Number Theory

## Statement 1: Theorem 1 (Primitive element theorem)
**Assessment: included**
This is formalized in mathlib at `Mathlib/FieldTheory/PrimitiveElement.lean`. The main theorem is `Field.exists_primitive_element`, which states: for a finite separable field extension `E/F`, there exists `alpha : E` such that `F(alpha) = top`. The textbook states it for a perfect field K and a finite extension L/K; since every extension of a perfect field is separable, this is a special case. The mathlib file also provides `Field.powerBasisOfFiniteOfSeparable`, which gives the explicit power basis `1, alpha, alpha^2, ..., alpha^n`.

## Statement 2: Lemma 1 (Coprime ideals and products)
**Assessment: included**
This is formalized in mathlib at `Mathlib/RingTheory/Coprime/Basic.lean`. The relevant theorem is `IsCoprime.mul_right` (line 114): if `IsCoprime x y` and `IsCoprime x z`, then `IsCoprime x (y * z)`. The textbook states this for ideals (if a_1 is coprime to a_2 and a_3, then a_1 is coprime to their product), which is the same algebraic statement. The Coprime/Lemmas.lean file further contains `IsCoprime.prod_right` for products over finsets.

## Statement 3: Lemma 1 (Nonarchimedean iff bounded)
**Assessment: included**
This is formalized in mathlib at `Mathlib/Analysis/Normed/Field/Ultra.lean`. The theorem `isUltrametricDist_iff_forall_norm_natCast_le_one` (line 140) states: a norm on a division ring is ultrametric (nonarchimedean) if and only if the norm of every natural number cast is at most 1. This is exactly the equivalence between nonarchimedean and the norms of n = 1 + 1 + ... + 1 being bounded (in fact bounded by 1).

## Statement 4: Theorem 1 (Ostrowski's theorem for Q)
**Assessment: included**
This is formalized in mathlib at `Mathlib/NumberTheory/Ostrowski.lean`. The main theorem is `Rat.AbsoluteValue.equiv_real_or_padic` (line 469): every nontrivial absolute value on Q (with values in R) is equivalent to either the standard archimedean absolute value or to a p-adic absolute value for some prime p. This is exactly Ostrowski's theorem as stated in the textbook.

## Statement 5: Lemma 2 (Cauchy sequence norm eventually constant)
**Assessment: non-included**
This statement says that for a Cauchy sequence {a_n} converging to a nonzero element in a nonarchimedean valued field, the norm |a_n| is eventually constant (equal to |a_m| for large m). Searched in `Mathlib/Topology/Algebra/Valued/`, `Mathlib/Analysis/Normed/`, `Mathlib/NumberTheory/Padics/`. While properties of Cauchy sequences and limits are present in mathlib, this specific result about eventual constancy of the valuation of a Cauchy sequence converging to a nonzero limit in the nonarchimedean setting was not found as a standalone lemma.

## Statement 6: Corollary 1 (Value group of completion equals that of K)
**Assessment: included**
This is formalized in mathlib at `Mathlib/Topology/Algebra/Valued/ValuedField.lean`. The lemma `Valued.exists_coe_eq_v` (line 336) states: for every element x in the completion, there exists r in K such that `extensionValuation x = v r`. This shows that the value group of the completion is the same as the value group of K.

## Statement 7: Proposition 1 (Residue field of completion isomorphic to residue field)
**Assessment: non-included**
This statement says that for a discretely valued field K with completion K_hat, the residue field of K_hat is isomorphic to the residue field of K (and more generally o_hat/p_hat^r is isomorphic to o/p^r). Searched in `Mathlib/Topology/Algebra/Valued/`, `Mathlib/RingTheory/Valuation/`, `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean`. No formalization of this isomorphism between residue fields of a valued field and its completion was found.

## Statement 8: Proposition 2 (p-adic series expansion)
**Assessment: non-included**
This statement says that every nonzero element in the completion of a discretely valued field has a unique representation as a convergent series x = pi^m (a_0 + a_1 pi + a_2 pi^2 + ...) where a_i are representatives of the residue field. Searched in `Mathlib/NumberTheory/Padics/`, `Mathlib/Topology/Algebra/Valued/`, `Mathlib/RingTheory/Valuation/`. While p-adic integers have `appr` (approximation) functions, the formal statement about unique convergent series representation with respect to a system of representatives was not found.

## Statement 9: Lemma 1 (CDVF with finite residue field: o compact, K locally compact)
**Assessment: included**
This is formalized in mathlib at `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean`. The key result is `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`, which characterizes compactness of the valuation ring in terms of completeness, DVR structure, and finiteness of the residue field. Combined with `properSpace_iff_compactSpace_integer`, this gives local compactness of K when the residue field is finite. The specific case of p-adic integers is in `Mathlib/NumberTheory/Padics/ProperSpace.lean` with `PadicInt.compactSpace`.

## Statement 10: Theorem 1 (Ostrowski: archimedean complete field is R or C)
**Assessment: included**
This is formalized in mathlib at `Mathlib/Analysis/Normed/Algebra/GelfandMazur.lean`. The theorem `NormedAlgebra.Real.nonempty_algEquiv_or` (line 407) states: if a field F is a normed R-algebra, then F is isomorphic (as an R-algebra) either to R or to C. This is essentially the same as the "second Ostrowski theorem": a field complete with respect to an archimedean valuation is isomorphic to R or C. The file notes in comments that the additional step of showing that any field complete w.r.t. an archimedean absolute value is a normed R-algebra is marked as TODO, but the core algebraic/analytic content is formalized.

## Statement 11: Theorem 2 (Hensel's lemma, factorization version)
**Assessment: non-included**
The textbook states the factorization version of Hensel's lemma: if f_bar factors as g_bar * h_bar with g_bar, h_bar coprime over the residue field, then f factors as g * h over the valuation ring with matching degrees and reductions. The file `Mathlib/RingTheory/Henselian.lean` defines HenselianRing and HenselianLocalRing, but explicitly states in its TODO section (line 49) that "factorizations into coprime polynomials can be lifted from the residue field to the Henselian ring" is not yet done. The file `Mathlib/NumberTheory/Padics/Hensel.lean` proves Hensel's lemma only for simple root lifting (the Newton's method version), not the factorization version.

## Statement 12: Corollary 1 (Hensel's lemma, simple root lifting)
**Assessment: included**
This is formalized in mathlib at `Mathlib/NumberTheory/Padics/Hensel.lean`. The theorem `hensels_lemma` (line 482) states that if f(a) has norm less than the square of the norm of f'(a), then there exists a root z of f in Z_p near a. More generally, `Mathlib/RingTheory/Henselian.lean` provides `HenselianRing` and `HenselianLocalRing` classes that encode this simple root lifting property. The instance `IsAdicComplete.henselianRing` shows that I-adically complete rings are Henselian.

## Statement 13: Corollary 2 (Irreducible polynomial norm equals max of leading and constant coefficients)
**Assessment: non-included**
This statement says that for an irreducible polynomial f = a_0 + a_1 x + ... + a_n x^n over a CDVF with a_0 a_n nonzero, |f| = max(|a_0|, |a_n|). Searched in `Mathlib/NumberTheory/Padics/`, `Mathlib/RingTheory/Valuation/`, `Mathlib/RingTheory/Polynomial/`, `Mathlib/Analysis/Normed/`. No formalization of this result about the Gauss norm of irreducible polynomials over a complete discrete valuation field was found.

## Statement 14: Theorem 3 (Unique extension of discrete valuation to finite extension)
**Assessment: included**
This is formalized across several files in mathlib. The spectral norm construction and unique norm extension theorem are in `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`, which proves that for a nonarchimedean normed field K and algebraic extension L/K, the spectral norm is the unique power-multiplicative K-algebra norm on L extending the norm on K (`spectralNorm_unique`), and that if L/K is finite, L is complete (`spectralNorm.completeSpace`). The formula involving the norm map N_{L/K} is related but the mathlib formulation uses spectral values rather than the explicit norm map formula. The extension of valuations to completions is in `Mathlib/Topology/Algebra/Valued/ValuedField.lean` via `Valued.extensionValuation`.

## Statement 15: Proposition 1 (Localization-quotient commutativity)
**Assessment: non-included**
This statement says that if S is a multiplicative set disjoint from an ideal a of A, then S^{-1}A / (a S^{-1}A) is isomorphic to S_bar^{-1}(A/a), where S_bar is the image of S in A/a. Searched in `Mathlib/RingTheory/Localization/` (Ideal.lean, Basic.lean, AtPrime/Basic.lean, Defs.lean), `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`. The closest result found is `IsLocalization.AtPrime.equivQuotMaximalIdeal` in `AtPrime/Basic.lean`, which gives R/p isomorphic to R_p / maximal ideal of R_p for a prime p. However, the general statement about the commutativity of localization and quotient for arbitrary ideals and multiplicative sets was not found.

## Statement 16: Proposition 2 (Kummer-Dedekind theorem)
**Assessment: included**
This is formalized in mathlib at `Mathlib/NumberTheory/KummerDedekind.lean`. The main theorem `normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map` (line 132) is the Kummer-Dedekind theorem, stating the bijection between prime factors of I*S and prime factors of the minimal polynomial mod I. The multiplicity-preserving property is given by `emultiplicity_factors_map_eq_emultiplicity`. The mathlib version uses a conductor condition `(conductor R x).comap (algebraMap R S) ⊔ I = top` which is satisfied when B is monogenic over A.

## Statement 17: Proposition 1 (Kummer-Dedekind theorem, repeated)
**Assessment: included**
This is the same statement as Statement 16 (the text has it repeated). It is formalized in mathlib at `Mathlib/NumberTheory/KummerDedekind.lean` as described above.

## Statement 18: Proposition 2 (Unique unramified extension of degree n)
**Assessment: non-included**
This statement says that there is a unique unramified extension of degree n of a CDVF K. Searched in `Mathlib/RingTheory/DedekindDomain/`, `Mathlib/NumberTheory/`, `Mathlib/FieldTheory/`, `Mathlib/RingTheory/Valuation/`. The file `Mathlib/RingTheory/Frobenius.lean` mentions unique unramified extensions but only in a different context. No formalization of the uniqueness of unramified extensions of a given degree for complete discretely valued fields was found.
