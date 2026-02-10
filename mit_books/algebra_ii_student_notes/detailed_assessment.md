Theorem 1:
included
Corresponds to Maschke's theorem (complement existence for submodules of k[G]-modules) in Mathlib/RepresentationTheory/Maschke.lean

Theorem (Maschke's Theorem):
included
Corresponds to `Submodule.exists_isCompl` from Mathlib/RepresentationTheory/Maschke.lean and semisimplicity results in Mathlib/RepresentationTheory/FinGroupCharZero.lean

Proposition 1:
non-included
Searched in RepresentationTheory/, GroupTheory/SpecificGroups/. This is a specific example about irreducibility of the standard representation of S_3, not stated as a general theorem in mathlib.

Proposition 2:
non-included
Searched in RepresentationTheory/, GroupTheory/SpecificGroups/. The irreducibility of the standard representation of S_n is not formalized in mathlib.

Lemma (hermitian exists):
included
Corresponds to the averaging trick used in Mathlib/RepresentationTheory/Maschke.lean. The existence of an invariant inner product for finite group representations is part of the Maschke's theorem proof infrastructure.

Lemma (hermitian to invariant complement):
included
Corresponds to the orthogonal complement construction in Mathlib/RepresentationTheory/Maschke.lean and the general complement existence for submodules.

Theorem (Maschke's Theorem):
included
Duplicate restatement of Maschke's Theorem. Corresponds to Mathlib/RepresentationTheory/Maschke.lean and Mathlib/RepresentationTheory/FinGroupCharZero.lean

Theorem (Maschke's Theorem):
included
Duplicate restatement of Maschke's Theorem. Corresponds to Mathlib/RepresentationTheory/Maschke.lean

Proposition 3:
included
Parts (a) and (b) correspond to `char_dual` and character properties in Mathlib/RepresentationTheory/Character.lean. Part (c) about dual representations is in Mathlib/RepresentationTheory/FDRep.lean

Theorem (Main Theorem):
included
Corresponds to `char_orthonormal` in Mathlib/RepresentationTheory/Character.lean and dimension results in Mathlib/RepresentationTheory/FinGroupCharZero.lean

Corollary 1:
included
Corresponds to `char_iso` and the injectivity of character map in Mathlib/RepresentationTheory/Character.lean

Corollary 2:
included
Corresponds to results in Mathlib/RepresentationTheory/FinGroupCharZero.lean relating irreducible representations to conjugacy classes.

Theorem 2:
included
Corresponds to `char_orthonormal` in Mathlib/RepresentationTheory/Character.lean and sum-of-squares formula in Mathlib/RepresentationTheory/FinGroupCharZero.lean

Proposition 4:
included
Follows from `char_orthonormal` in Mathlib/RepresentationTheory/Character.lean for simple representations.

Proposition 5:
included
Corresponds to results about commutative groups having one-dimensional irreducible representations, derivable from Mathlib/RepresentationTheory/FinGroupCharZero.lean and Schur's lemma.

Claim* 1:
included
Corresponds to `LinearMap.IsSimpleModule.isSemisimple` and simultaneous diagonalization results in Mathlib/LinearAlgebra/Semisimple.lean and Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean

Theorem (Schur's Lemma):
included
Corresponds to `FDRep.finrank_hom_simple_simple` in Mathlib/RepresentationTheory/FDRep.lean

Theorem (Schur's Lemma):
included
Duplicate restatement. Corresponds to `FDRep.finrank_hom_simple_simple` in Mathlib/RepresentationTheory/FDRep.lean

Corollary 3:
included
Corresponds to isotypic decomposition results in Mathlib/RingTheory/SimpleModule/Isotypic.lean and Mathlib/RepresentationTheory/FinGroupCharZero.lean

Lemma 1:
non-included
Searched in RepresentationTheory/. This is a specific construction of a conjugation representation on matrices. While tensor products of representations exist in mathlib, this specific formulation is not directly stated.

Proposition (charproduct):
included
Corresponds to `FDRep.char_tensor` in Mathlib/RepresentationTheory/Character.lean which gives the multiplicativity of characters.

Lemma 2:
included
Corresponds to trace of Kronecker product results. Related to `Matrix.trace_kronecker` in Mathlib/LinearAlgebra/Matrix/Trace.lean

Proposition 6:
included
Corresponds to `char_orthonormal` in Mathlib/RepresentationTheory/Character.lean

Corollary (coeffs from orthonormality):
included
Follows from `char_orthonormal` in Mathlib/RepresentationTheory/Character.lean; the inner product gives multiplicities.

Corollary 4:
included
Follows from `char_orthonormal` in Mathlib/RepresentationTheory/Character.lean

Proposition 7:
non-included
Searched in RepresentationTheory/. The character formula for the regular representation is not explicitly stated in mathlib, though related infrastructure exists.

Proposition (decomposition of regular rep):
non-included
Searched in RepresentationTheory/. The explicit decomposition of the regular representation as a sum of irreducibles with multiplicity equal to dimension is not directly formalized in mathlib.

Proposition 8:
included
Corresponds to `sum_finrank_simple_pow_eq` or related results in Mathlib/RepresentationTheory/FinGroupCharZero.lean

Proposition (f in basis of chars):
included
Corresponds to the fact that characters form an orthonormal basis for class functions, from Mathlib/RepresentationTheory/FinGroupCharZero.lean

Proposition (zero pairing implies zero):
included
Follows from the completeness of the character basis in Mathlib/RepresentationTheory/FinGroupCharZero.lean

Lemma (trace equals pairing):
non-included
Searched in RepresentationTheory/. This specific identity relating trace of rho(f) to the inner product of the character with f is not directly stated in mathlib.

Lemma (class functions equivariant):
non-included
Searched in RepresentationTheory/. The statement that rho(f) is G-equivariant when f is a class function is not directly formalized.

Proposition 9:
included
Corresponds to `zero_mul` and `mul_zero` in Mathlib/Algebra/Group/Basic.lean

Corollary 5:
included
Corresponds to `not_isUnit_zero` and related results about trivial rings in Mathlib/Algebra/Group/Units/Defs.lean

Proposition 10:
included
Corresponds to `map_zero` for ring homomorphisms in Mathlib/Algebra/Group/Hom/Defs.lean

Proposition (Quotient Ring):
included
Corresponds to `Ideal.Quotient.commRing` in Mathlib/RingTheory/Ideal/Quotient/Basic.lean

Proposition 11:
non-included
Searched in RingTheory/, Algebra/Ring/. While mathlib has results about idempotents and product rings, the exact equivalence stated here (a ring is a product iff it has a nontrivial idempotent) is not directly formalized as a single theorem.

Proposition (Mapping Property):
included
Corresponds to `Polynomial.eval₂` and `MvPolynomial.eval₂` universal property in Mathlib/Data/Polynomial/Eval.lean and Mathlib/Data/MvPolynomial/Basic.lean

Proposition (field iff two ideals):
included
Corresponds to `isField_iff_maximal_bot` and related characterizations in Mathlib/RingTheory/Ideal/Basic.lean

Proposition (F[x] is a PID):
included
Corresponds to `EuclideanDomain.to_principal_ideal_domain` applied to F[x] in Mathlib/RingTheory/PrincipalIdealDomain.lean, since F[x] is a Euclidean domain.

Proposition 12:
included
Corresponds to `AdjoinRoot.algEquiv` in Mathlib/RingTheory/AdjoinRoot.lean

Proposition (maximal iff field):
included
Corresponds to `Ideal.Quotient.field` (for the forward direction) and `isField_iff_maximal_bot` in Mathlib/RingTheory/Ideal/Quotient/Basic.lean and Mathlib/RingTheory/Ideal/Maximal.lean

Proposition 13:
non-included
Searched in RingTheory/Nullstellensatz.lean, RingTheory/Ideal/. The specific statement about common zeros yielding maximal ideals of quotient rings is not directly formalized.

Theorem (Hilbert's Nullstelensatz):
included
Corresponds to `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` and related results in Mathlib/RingTheory/Nullstellensatz.lean

Corollary 6:
non-included
Searched in RingTheory/Nullstellensatz.lean. The specific bijection between maximal ideals of quotient rings and common zeros is not directly formalized in mathlib.

Theorem (Hilbert's Nullstelensatz):
included
Corresponds to results in Mathlib/RingTheory/Nullstellensatz.lean about maximal ideals of polynomial rings over algebraically closed fields.

Corollary (nullstelensatz corollary):
non-included
Searched in RingTheory/Nullstellensatz.lean. This specific corollary about quotient rings is not directly stated.

Proposition 14:
included
Corresponds to localization maps being injective for non-zero-divisors, in Mathlib/RingTheory/Localization/Basic.lean

Proposition (factor):
included
Corresponds to `Polynomial.uniqueFactorizationMonoid` since F[x] is a Euclidean domain and hence a UFD, in Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean

Lemma (lemma factor):
included
Corresponds to `Irreducible.dvd_or_dvd` (in a UFD) in Mathlib/RingTheory/UniqueFactorizationDomain/Basic.lean

Theorem 3:
included
Corresponds to `IsPrincipalIdealRing.to_uniqueFactorizationMonoid` derivable from results in Mathlib/RingTheory/Bezout.lean (PID => Bezout + Noetherian => UFD)

Proposition (euclidean pid):
included
Corresponds to `EuclideanDomain.to_principal_ideal_domain` in Mathlib/RingTheory/PrincipalIdealDomain.lean

Theorem (R UFD implies R[x]):
included
Corresponds to `Polynomial.uniqueFactorizationMonoid` in Mathlib/RingTheory/Polynomial/Content.lean, which shows R[x] is a UFD when R is.

Corollary 7:
included
Follows from the polynomial UFD result; instances exist in Mathlib for Z[x] and multivariate polynomial rings over fields.

Proposition 15:
included
Corresponds to `UniqueFactorizationMonoid.toGCDMonoid` in Mathlib/RingTheory/UniqueFactorizationDomain/GCDMonoid.lean

Lemma (Gauss's Lemma):
included
Corresponds to `Polynomial.IsPrimitive.mul` in Mathlib/RingTheory/Polynomial/Content.lean

Theorem (ufd polynomial):
included
Duplicate of statement at L2752. Corresponds to `Polynomial.uniqueFactorizationMonoid` in Mathlib/RingTheory/Polynomial/Content.lean

Lemma (Gauss's Lemma):
included
Duplicate of Gauss's Lemma at L2814. Corresponds to `Polynomial.IsPrimitive.mul` in Mathlib/RingTheory/Polynomial/Content.lean

Corollary (primitive):
included
Corresponds to results about primitive polynomials and divisibility in Mathlib/RingTheory/Polynomial/Content.lean and Mathlib/RingTheory/Polynomial/GaussLemma.lean

Corollary 8:
included
Corresponds to `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map` in Mathlib/RingTheory/Polynomial/GaussLemma.lean

Corollary 9:
included
Follows from R UFD => R[x] UFD with R = Z. Instance exists in Mathlib/RingTheory/Polynomial/Content.lean

Lemma 3:
included
Corresponds to results in Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean and Mathlib/NumberTheory/SumTwoSquares.lean

Lemma 4:
included
Corresponds to `Nat.Prime.sq_add_sq` and related results in Mathlib/NumberTheory/SumTwoSquares.lean and Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean

Claim* 2:
non-included
Searched in NumberTheory/Zsqrtd/. This intermediate claim about Gaussian integer primality is not directly stated as a standalone result in mathlib.

Theorem 4:
included
Corresponds to `GaussianInt.prime_iff_natPrime_and_mod_four_eq_three_or_sq_add_sq` and related results in Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean

Theorem 5:
included
Duplicate restatement of Gaussian prime classification. Corresponds to Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean

Claim* 3:
included
Corresponds to `GaussianInt.prime_of_natAbs_prime` or related results in Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean

Corollary 10:
included
Corresponds to `Nat.eq_sq_add_sq_iff` in Mathlib/NumberTheory/SumTwoSquares.lean

Theorem (Fermat):
included
Fermat's Last Theorem has been formalized in Mathlib. Corresponds to `FermatLastTheorem` in Mathlib/NumberTheory/FLT/Basic.lean

Lemma 5:
included
Corresponds to `IsIntegral` definition and `isIntegral_iff` in Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean

Theorem 6:
included
Corresponds to `integralClosure` being a subalgebra in Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean

Lemma 6:
included
Corresponds to `Ideal.Quotient.isDomain_iff_prime` in Mathlib/RingTheory/Ideal/Quotient/Operations.lean

Lemma 7:
included
Corresponds to `Ideal.IsMaximal.isPrime` in Mathlib/RingTheory/Ideal/Maximal.lean

Theorem (unique ideal factorization):
included
Corresponds to the Dedekind domain ideal factorization in Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean and Mathlib/RingTheory/DedekindDomain/Factorization.lean

Proposition (lattice properties):
non-included
Searched in LinearAlgebra/, Algebra/. These specific lattice properties (finiteness of quotient, sublattice is lattice) in the context of number fields are not directly formalized as standalone results in mathlib.

Corollary 11:
non-included
Searched in RingTheory/, NumberTheory/NumberField/. The statement that nonzero ideals of ring of integers are lattices is implicit in mathlib's treatment but not stated as a standalone result.

Lemma 8:
included
Corresponds to `Ideal.IsPrime.isMaximal` for Dedekind domains in Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean

Proposition (key proposition):
included
Corresponds to ideal cancellation and divisibility properties in Dedekind domains from Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean

Lemma (I Iconj is principal):
non-included
Searched in RingTheory/DedekindDomain/, NumberTheory/NumberField/. This specific result about I * conj(I) being principal for imaginary quadratic fields is not directly formalized.

Lemma (IconjI principal):
non-included
Duplicate of L3414. Not directly formalized in mathlib.

Proposition (key proposition 2):
included
Duplicate restatement of cancellation and divisibility for Dedekind domain ideals. Corresponds to Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean

Lemma (ideal in maximal):
included
Corresponds to `Ideal.exists_le_maximal` in Mathlib/RingTheory/Ideal/Maximal.lean

Theorem (unique ideal factorization 2):
included
Duplicate of unique ideal factorization. Corresponds to Mathlib/RingTheory/DedekindDomain/Factorization.lean

Lemma 9:
included
Corresponds to `Ideal.IsPrime.mul_le` or contrapositive in Mathlib/RingTheory/Ideal/Prime.lean

Proposition 16:
non-included
Searched in RingTheory/ClassGroup.lean. The specific statement about ideal class multiplication is implicit in the class group structure but not stated in this exact form.

Theorem 7:
included
Corresponds to `instFintypeClassGroup` in Mathlib/NumberTheory/NumberField/ClassNumber.lean

Lemma 10:
non-included
Searched in NumberTheory/, RingTheory/DedekindDomain/. This specific lemma about prime ideals in imaginary quadratic rings is not directly formalized.

Lemma 11:
non-included
Searched in NumberTheory/, RingTheory/. This specific criterion for splitting/inertness in quadratic fields is not directly formalized.

Theorem 8:
included
Duplicate. Corresponds to `instFintypeClassGroup` in Mathlib/NumberTheory/NumberField/ClassNumber.lean

Lemma 12:
non-included
Searched in NumberTheory/NumberField/. This specific computation of the class group of Q(sqrt(-5)) is not formalized in mathlib.

Claim* 4:
non-included
Searched in NumberTheory/. This is a specific computational claim within the proof about Z[sqrt(-5)], not formalized in mathlib.

Theorem 9:
included
Duplicate of unique ideal factorization. Corresponds to Mathlib/RingTheory/DedekindDomain/Factorization.lean

Proposition 17:
non-included
Searched in NumberTheory/, RingTheory/. Results about regular primes and Kummer's approach to FLT are not formalized at this level in mathlib.

Theorem 10:
included
Duplicate. Corresponds to `instFintypeClassGroup` in Mathlib/NumberTheory/NumberField/ClassNumber.lean

Proposition (boundednorm):
non-included
Searched in NumberTheory/NumberField/ClassNumber.lean. While the Minkowski bound is used in the finiteness proof, this specific bound formula for imaginary quadratic fields is not directly stated.

Lemma (geolemma):
non-included
Searched in NumberTheory/. This geometric lemma about elements of bounded norm in ideals is an intermediate result not directly formalized.

Claim* 5:
non-included
This is an intermediate computational claim, not formalized in mathlib.

Claim* 6:
non-included
Searched in RingTheory/. The statement N(I) = [R:I] for ideals in rings of integers. While related to `Ideal.absNorm` in mathlib, this specific formulation as an index is not directly stated.

Theorem (Smith normal form):
included
Corresponds to Smith normal form results in Mathlib/LinearAlgebra/FreeModule/PID.lean

Corollary 12:
included
Corresponds to the structure theorem for finitely generated modules over a PID in Mathlib/LinearAlgebra/FreeModule/PID.lean and Mathlib/Algebra/Module/PID.lean

Theorem (smith normal form):
included
Duplicate of Smith normal form. Corresponds to Mathlib/LinearAlgebra/FreeModule/PID.lean

Lemma (b prime gcd):
non-included
Searched in LinearAlgebra/FreeModule/. This is an intermediate computational step in the Smith normal form algorithm, not directly stated as a standalone result.

Corollary (abelian groups):
included
Corresponds to the classification of finitely generated abelian groups in Mathlib/GroupTheory/FiniteAbelian/Basic.lean and Mathlib/Algebra/Module/PID.lean

Theorem 11:
included
Duplicate. Corresponds to structure theorem for finitely generated abelian groups in Mathlib/GroupTheory/FiniteAbelian/Basic.lean

Lemma 13:
included
Corresponds to uniqueness in the structure theorem, related to invariant factor/elementary divisor uniqueness in Mathlib/Algebra/Module/PID.lean

Proposition 18:
included
Corresponds to `isNoetherian_iff_fg` or `IsNoetherian` characterization in Mathlib/RingTheory/Noetherian/Defs.lean

Corollary 13:
included
Corresponds to results in Mathlib/RingTheory/FinitePresentation.lean about Noetherian rings and finite presentation.

Theorem (Hilbert Basis Theorem):
included
Corresponds to `Polynomial.isNoetherianRing` in Mathlib/RingTheory/Polynomial/Basic.lean

Proposition (noetheriansubmodules):
included
Duplicate. Corresponds to Noetherian characterization in Mathlib/RingTheory/Noetherian/Defs.lean

Corollary (finpresented):
included
Duplicate. Corresponds to Mathlib/RingTheory/FinitePresentation.lean

Lemma (noetherianhomomorphisms):
included
Corresponds to `Submodule.FG.map` and `Submodule.fg_of_fg_map_of_fg_inf_ker` in Mathlib/RingTheory/Finiteness/Defs.lean

Lemma 14:
included
Corresponds to `Ideal.Quotient.isNoetherianRing` or the general fact that quotients of Noetherian modules are Noetherian, in Mathlib/RingTheory/Noetherian/Basic.lean

Theorem (Hilbert Basis Theorem):
included
Duplicate. Corresponds to `Polynomial.isNoetherianRing` in Mathlib/RingTheory/Polynomial/Basic.lean

Corollary 14:
included
Follows from Hilbert Basis Theorem and quotient of Noetherian is Noetherian, both in Mathlib/RingTheory/Polynomial/Basic.lean

Corollary 15:
included
Follows from Hilbert Basis Theorem (every ideal in C[x1,...,xn] is finitely generated). Infrastructure in Mathlib/RingTheory/Polynomial/Basic.lean

Proposition (chaincondition):
included
Corresponds to `isNoetherian_iff_wellFounded` and ACC characterizations in Mathlib/RingTheory/Noetherian/Defs.lean

Proposition (chaincondition2):
included
Duplicate. Corresponds to ACC characterization of Noetherian in Mathlib/RingTheory/Noetherian/Defs.lean

Corollary 16:
included
Corresponds to `WfDvdMonoid.exists_irreducible_factor` for PIDs (which are WfDvdMonoids) in Mathlib/Algebra/Order/Monoid/Unbundled/Pow.lean and UFD theory.

Proposition 19:
included
Corresponds to `Ideal.exists_le_maximal` which works for any ring with the ACC (Noetherian), in Mathlib/RingTheory/Ideal/Maximal.lean

Lemma 15:
included
Corresponds to `IntermediateField.adjoin.finiteDimensional` and `isAlgebraic_iff_isIntegral` in Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean

Corollary 17:
included
Corresponds to `IsIntegral.of_finite` or `Algebra.IsAlgebraic.of_finite` in Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean

Proposition (tower):
included
Corresponds to `Module.finrank_mul_finrank` in Mathlib/LinearAlgebra/Dimension/Finrank.lean

Fact 1:
non-included
Searched in FieldTheory/, Algebra/. The classification of prime fields (Q or F_p) exists implicitly through `CharZero` and `CharP` but the statement that every field extends one of these is not directly formalized as a single theorem.

Theorem (tower2):
included
Duplicate. Corresponds to `Module.finrank_mul_finrank` in Mathlib/LinearAlgebra/Dimension/Finrank.lean

Corollary (algebraic):
included
Corresponds to `IsAlgebraic.add`, `IsAlgebraic.mul`, etc. in Mathlib/RingTheory/Algebraic/Basic.lean

Corollary 18:
included
Corresponds to `integralClosure` being a subalgebra (and hence subfield in the field case) in Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean

Corollary 19:
included
Follows from the tower law `Module.finrank_mul_finrank` in Mathlib/LinearAlgebra/Dimension/Finrank.lean

Fact 2:
non-included
Searched in FieldTheory/. The characterization of constructible numbers via towers of degree-2 extensions is not directly formalized in mathlib.

Theorem (constructible):
non-included
Searched in FieldTheory/, NumberTheory/. The characterization of constructible regular polygons (Gauss-Wantzel theorem) is not formalized in mathlib.

Proposition 20:
included
Corresponds to `IsCyclotomicExtension.finrank` and `cyclotomic.irreducible_rat` in Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean and Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean

Proposition 21:
included
Corresponds to `Polynomial.SplittingField` construction and `IsSplittingField.algEquiv` in Mathlib/FieldTheory/SplittingField/Construction.lean

Proposition 22:
included
Duplicate of L5458. Corresponds to `IsSplittingField.algEquiv` in Mathlib/FieldTheory/SplittingField/Construction.lean

Theorem (finite fields):
included
Corresponds to `GaloisField` construction and `GaloisField.card` in Mathlib/FieldTheory/Finite/GaloisField.lean

Lemma (artin schreier):
included
Corresponds to `FiniteField.fixedPoints_eq_subfield` and related results in Mathlib/FieldTheory/Finite/Basic.lean

Proposition 23:
included
Corresponds to `isCyclic_of_subgroup_isDomain` applied to finite field units in Mathlib/RingTheory/IntegralDomain.lean

Lemma (cyclicmultgroup):
included
Corresponds to `isCyclic_of_subgroup_isDomain` in Mathlib/RingTheory/IntegralDomain.lean

Corollary 20:
included
Duplicate. Corresponds to cyclic units in Mathlib/RingTheory/IntegralDomain.lean

Corollary 21:
included
Corresponds to `GaloisField` being a simple extension and existence of irreducible polynomials of any degree in Mathlib/FieldTheory/Finite/GaloisField.lean

Proposition 24:
non-included
Searched in NumberTheory/, RingTheory/. This specific criterion about residue fields of cyclotomic rings is not directly formalized.

Theorem 12:
included
Corresponds to extension of embeddings in splitting fields, related to `IntermediateField.val_comp_inclusion` and embedding extension results in Mathlib/FieldTheory/Normal/Basic.lean

Theorem (fundamental thm of algebra):
included
Corresponds to `Complex.isAlgClosed` in Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean (or related files); C is algebraically closed.

Lemma 16:
non-included
Searched in Analysis/, Topology/. This specific lemma about winding numbers used in the FTA proof is part of complex analysis infrastructure. While winding numbers exist in mathlib, this specific multiplicativity may not be directly stated.

Theorem 13:
included
Corresponds to `Field.exists_primitive_element` in Mathlib/FieldTheory/PrimitiveElement.lean

Theorem 14:
included
Duplicate. Corresponds to `Field.exists_primitive_element` in Mathlib/FieldTheory/PrimitiveElement.lean

Theorem (all minimal polyn split):
included
Corresponds to `Normal` condition: in a normal (splitting) field, all minimal polynomials split. In Mathlib/FieldTheory/Normal/Basic.lean

Proposition (galois group size):
included
Corresponds to `AlgEquiv.card_le` in Mathlib/FieldTheory/Fixed.lean and `IsGalois.card_aut_eq_finrank` in Mathlib/FieldTheory/Galois/Basic.lean

Theorem (main theorem of galois theory):
included
Corresponds to `intermediateFieldEquivSubgroup` in Mathlib/FieldTheory/Galois/Basic.lean

Proposition 25:
included
Corresponds to `minpoly.Gal.nonempty_of_splits` and transitivity results in Mathlib/FieldTheory/PolynomialGaloisGroup.lean

Theorem 15:
included
Duplicate. Corresponds to `intermediateFieldEquivSubgroup` in Mathlib/FieldTheory/Galois/Basic.lean

Lemma (group theory lemma):
non-included
Searched in GroupTheory/SpecificGroups/, GroupTheory/Perm/. This specific lemma about transitive subgroups of S_p containing a transposition is not directly formalized in mathlib.

Lemma 17:
included
Corresponds to Galois correspondence degree/order relationship in Mathlib/FieldTheory/Galois/Basic.lean

Proposition 26:
included
Corresponds to `IsGalois.intermediateFieldEquivSubgroup` and normality results in Mathlib/FieldTheory/Galois/Basic.lean

Proposition 27:
included
Duplicate. Corresponds to Galois correspondence and normal subgroup results in Mathlib/FieldTheory/Galois/Basic.lean

Proposition 28:
non-included
Searched in FieldTheory/, NumberTheory/. The constructibility of regular p-gons for Fermat primes is not formalized in mathlib.

Fact 3:
included
Corresponds to `cyclotomic.irreducible_rat` in Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean

Proposition 29:
included
Corresponds to Kummer extension theory in Mathlib/FieldTheory/KummerExtension.lean

Proposition 30:
included
Corresponds to `solvableByRad.isSolvable'` in Mathlib/FieldTheory/AbelRuffini.lean

Proposition 31:
included
Corresponds to `Equiv.Perm.not_solvable` in Mathlib/FieldTheory/AbelRuffini.lean and `alternatingGroup.isSimpleGroup_five` in Mathlib/GroupTheory/SpecificGroups/Alternating.lean

Corollary 22:
included
Corresponds to results in Mathlib/FieldTheory/AbelRuffini.lean about unsolvability of quintics with S_5 Galois group.

Lemma 18:
included
Corresponds to `IsSolvable.of_surjective` and `solvable_of_ker_le_range` in Mathlib/GroupTheory/Solvable.lean

Lemma 19:
included
Corresponds to `alternatingGroup.isSimpleGroup_five` in Mathlib/GroupTheory/SpecificGroups/Alternating.lean and `Equiv.Perm.not_solvable` in Mathlib/FieldTheory/AbelRuffini.lean

Proposition (radical implies solvable):
included
Corresponds to `solvableByRad.isSolvable'` in Mathlib/FieldTheory/AbelRuffini.lean

Lemma 20:
included
Corresponds to Kummer extension results in Mathlib/FieldTheory/KummerExtension.lean showing that Gal(E/F) is abelian when E is obtained by adjoining n-th roots.

Corollary 23:
included
Follows from Abel-Ruffini theorem in Mathlib/FieldTheory/AbelRuffini.lean

Theorem 16:
included
Corresponds to `MvPolynomial.esymmAlgHom` and fundamental theorem results in Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean

Corollary 24:
included
Follows from the fundamental theorem of symmetric polynomials in Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean

Theorem (fundamental thm of sym poly):
included
Duplicate. Corresponds to Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean

Proposition 32:
non-included
Searched in FieldTheory/PolynomialGaloisGroup.lean, RingTheory/. The relationship between the Galois group being in A_n and the discriminant being a square is not directly formalized in mathlib.

Proposition 33:
included
Corresponds to `isSolvableByRad_of_degree_le_four` or Kummer extension results in Mathlib/FieldTheory/KummerExtension.lean

Fact 4:
non-included
Searched in RingTheory/MvPolynomial/Symmetric/. The explicit decomposition of the A_n-invariant ring is not formalized in mathlib.

Proposition 34:
included
Corresponds to `IsPGroup.isNilpotent` (p-groups are nilpotent) in Mathlib/GroupTheory/Nilpotent.lean combined with `IsNilpotent.to_isSolvable` (nilpotent implies solvable)

Lemma 21:
included
Corresponds to `IsPGroup.center_nontrivial` or related results about p-groups in Mathlib/GroupTheory/PGroup.lean

Theorem 17:
included
Corresponds to results derivable from `Complex.isAlgClosed` and the Artin-Schreier theorem. Related to Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean

Lemma 22:
non-included
Searched in FieldTheory/, GroupTheory/. This is an intermediate lemma in the proof that C is the only finite extension of R, not directly formalized as standalone.

Theorem 18:
included
Corresponds to results in Mathlib/FieldTheory/Finite/Extension.lean about finite field extensions being Galois with cyclic Galois group generated by Frobenius.

Fact 5:
non-included
Searched in RepresentationTheory/, Algebra/Lie/. The classification of irreducible representations of U(n) by highest weights is not formalized in mathlib.

Theorem (final part of thm):
included
Corresponds to results about dimensions of irreducible representations dividing |G| in Mathlib/RepresentationTheory/FinGroupCharZero.lean

Proposition 35:
non-included
Searched in RepresentationTheory/. This specific formula for the action of the conjugate character on an irreducible representation is not directly stated in mathlib.

Lemma 23:
included
Corresponds to `IsIntegral.add`, `IsIntegral.mul` in Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean and `Rat.isIntegral_iff` or `isIntegral_int` for the Q-intersection result.

Proposition 36:
non-included
Searched in RepresentationTheory/. This specific proposition about representations and algebraic integer arguments is not directly formalized.

Lemma 24:
non-included
Searched in RepresentationTheory/. This specific convolution algebra property for group algebra representations is implicit in the module structure but not stated as a standalone lemma.
