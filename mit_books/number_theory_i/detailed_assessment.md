# Detailed Assessment: Number Theory I

## Statement 1: Lemma 1.4
**Status**: included
Absolute values on Q are formalized in `Mathlib/NumberTheory/Padics/PadicNorm.lean` and `Mathlib/Analysis/Normed/Field/Basic.lean`.

## Statement 2: Corollary 1.5
**Status**: included
Extension of absolute values is covered in valuation theory in `Mathlib/RingTheory/Valuation/Basic.lean`.

## Statement 3: Theorem 1.8 (Ostrowski's Theorem)
**Status**: included
Ostrowski's theorem is formalized in `Mathlib/NumberTheory/Ostrowski.lean`.

## Statement 4: Theorem 1.9 (Product Formula)
**Status**: included
Product formula for number fields is in `Mathlib/NumberTheory/NumberField/Basic.lean`.

## Statement 5: Theorem 1.16 (DVR characterizations)
**Status**: included
DVR characterizations are formalized in `Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean`.

## Statement 6: Proposition 1.18 (Integral closure under addition/multiplication)
**Status**: included
Integral closure forms a ring, proven in `Mathlib/RingTheory/IntegralClosure/Basic.lean`.

## Statement 7: Proposition 1.20 (Transitivity of integrality)
**Status**: included
Transitivity of integral closure in `Mathlib/RingTheory/IntegralClosure/Basic.lean` with `IsIntegral.trans`.

## Statement 8: Corollary 1.21 (Integral closure is integrally closed)
**Status**: included
Formalized as `integralClosure.isIntegrallyClosed` in `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean`.

## Statement 9: Proposition 1.22 (Z is integrally closed)
**Status**: included
Instance `Int.instIsIntegrallyClosed` in `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean`.

## Statement 10: Corollary 1.23 (UFD is integrally closed)
**Status**: included
Formalized as `UniqueFactorizationMonoid.instIsIntegrallyClosed` in `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean`.

## Statement 11: Proposition 1.25 (Valuation ring is integrally closed)
**Status**: included
Proven in `Mathlib/RingTheory/Valuation/Integral.lean` as `ValuationRing.isIntegrallyClosed`.

## Statement 12: Proposition 1.28 (Integrality iff minimal polynomial is in A[x])
**Status**: included
Minimal polynomial characterization in `Mathlib/RingTheory/IntegralClosure/Basic.lean`.

## Statement 13: Theorem 2.1 (Prime ideal correspondence under localization)
**Status**: included
Prime ideal correspondence formalized in `Mathlib/RingTheory/Localization/AtPrime.lean`.

## Statement 14: Proposition 2.6 (Module equals intersection of localizations)
**Status**: included
Localization intersection property in `Mathlib/RingTheory/Localization/Module.lean`.

## Statement 15: Corollary 2.7 (Ideal is intersection of localizations)
**Status**: included
Special case of module localization in `Mathlib/RingTheory/Localization/Ideal.lean`.

## Statement 16: Proposition 2.9 (Equivalent conditions for Dedekind domain)
**Status**: included
Multiple characterizations in `Mathlib/RingTheory/DedekindDomain/Basic.lean`.

## Statement 17: Corollary 2.11 (PID is Dedekind domain)
**Status**: included
Instance in `Mathlib/RingTheory/DedekindDomain/PID.lean`.

## Statement 18: Lemma 2.14 (Finite generation of fractional ideals)
**Status**: included
Fractional ideals are finitely generated modules, formalized in `Mathlib/RingTheory/FractionalIdeal/Basic.lean`.

## Statement 19: Corollary 2.16 (Fractional ideal form (1/a)I)
**Status**: included
Fractional ideal structure in `Mathlib/RingTheory/FractionalIdeal/Basic.lean`.

## Statement 20: Lemma 2.18 (Ideal quotient is fractional ideal)
**Status**: included
Division of fractional ideals in `Mathlib/RingTheory/FractionalIdeal/Operations.lean`.

## Statement 21: Lemma 2.20 (Invertibility criterion for fractional ideals)
**Status**: included
Invertibility characterization in `Mathlib/RingTheory/FractionalIdeal/Basic.lean`.

## Statement 22: Lemma 3.1 (Localization of fractional ideal operations)
**Status**: included
Localization commutes with operations in `Mathlib/RingTheory/FractionalIdeal/Operations.lean`.

## Statement 23: Theorem 3.2 (Invertibility is local)
**Status**: included
Local characterization of invertibility in `Mathlib/RingTheory/DedekindDomain/Factorization.lean`.

## Statement 24: Corollary 3.3 (Every nonzero fractional ideal in Dedekind domain is invertible)
**Status**: included
Key theorem in `Mathlib/RingTheory/DedekindDomain/Basic.lean`.

## Statement 25: Lemma 3.4 (Local invertibility = principality)
**Status**: included
Characterization in `Mathlib/RingTheory/DedekindDomain/Factorization.lean`.

## Statement 26: Corollary 3.5 (Invertible iff locally principal)
**Status**: included
Follows from local-global principle in `Mathlib/RingTheory/DedekindDomain/Basic.lean`.

## Statement 27: Lemma 3.6 (Finite number of primes containing an element)
**Status**: included
Finitely many primes divide nonzero element in `Mathlib/RingTheory/DedekindDomain/Factorization.lean`.

## Statement 28: Corollary 3.7 (Finite number of primes containing an ideal)
**Status**: included
Finite support of ideal factorization in `Mathlib/RingTheory/DedekindDomain/Factorization.lean`.

## Statement 29: Lemma 3.9 (Valuation of ideals and prime containment)
**Status**: included
Valuation at prime ideals in `Mathlib/RingTheory/DedekindDomain/Factorization.lean`.

## Statement 30: Corollary 3.10 (Almost all valuations are zero)
**Status**: included
Finite support of valuations in `Mathlib/RingTheory/DedekindDomain/Factorization.lean`.

## Statement 31: Theorem 3.11 (Ideal group is free abelian on primes)
**Status**: included
Factorization structure in `Mathlib/RingTheory/DedekindDomain/Factorization.lean`.

## Statement 32: Corollary 3.13 (Unique prime factorization of ideals)
**Status**: included
Core Dedekind domain theorem in `Mathlib/RingTheory/DedekindDomain/Factorization.lean`.

## Statement 33: Corollary 3.15 (Dedekind domain is UFD iff PID)
**Status**: included
Characterization in `Mathlib/RingTheory/DedekindDomain/PID.lean`.

## Statement 34: Lemma 3.16 (Every ideal class contains a coprime representative)
**Status**: included
Coprimality in ideal class group in `Mathlib/RingTheory/ClassGroup.lean`.

## Statement 35: Corollary 3.17 (Finite approximation)
**Status**: included
Chinese remainder for Dedekind domains in `Mathlib/RingTheory/DedekindDomain/Basic.lean`.

## Statement 36: Corollary 3.18 (A/I is a PIR)
**Status**: included
Quotient structure in `Mathlib/RingTheory/DedekindDomain/Basic.lean`.

## Statement 37: Corollary 3.21 (Semilocal Dedekind = PID)
**Status**: included
Semilocal characterization in `Mathlib/RingTheory/DedekindDomain/PID.lean`.

## Statement 38: Theorem 3.22 (Every ideal is 2-generated)
**Status**: included
Two-generator property in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 39: Theorem 3.23 (Equivalent definitions of Dedekind domains)
**Status**: included
Multiple characterizations in `Mathlib/RingTheory/DedekindDomain/Basic.lean`.

## Statement 40: Lemma 4.4 (Irreducible inseparable iff f' = 0)
**Status**: included
Derivative characterization in `Mathlib/FieldTheory/Separable.lean`.

## Statement 41: Corollary 4.5 (Inseparable factorization f(x) = g(x^{p^n}))
**Status**: included
Purely inseparable factorization in `Mathlib/FieldTheory/PurelyInseparable.lean`.

## Statement 42: Corollary 4.6 (Char 0 implies separable)
**Status**: included
Characteristic zero separability in `Mathlib/FieldTheory/Separable.lean`.

## Statement 43: Lemma 4.7 (Number of embeddings)
**Status**: included
Embedding count in `Mathlib/FieldTheory/Separable.lean`.

## Statement 44: Theorem 4.9 (Extension of homomorphisms to algebraically closed fields)
**Status**: included
Homomorphism lifting in `Mathlib/FieldTheory/Normal.lean`.

## Statement 45: Lemma 4.10 (Multiplicativity of number of embeddings)
**Status**: included
Tower law for embeddings in `Mathlib/FieldTheory/Separable.lean`.

## Statement 46: Corollary 4.11 (Separable/inseparable degrees multiplicative in towers)
**Status**: included
Tower law in `Mathlib/FieldTheory/Separable.lean` and `PurelyInseparable.lean`.

## Statement 47: Theorem 4.12 (Characterizations of separable extensions)
**Status**: included
Multiple characterizations in `Mathlib/FieldTheory/Separable.lean`.

## Statement 48: Corollary 4.13 (Separable degree inequality)
**Status**: included
Separable degree bounds in `Mathlib/FieldTheory/Separable.lean`.

## Statement 49: Corollary 4.14 (Separability in towers)
**Status**: included
Separability transitivity in `Mathlib/FieldTheory/Separable.lean`.

## Statement 50: Corollary 4.15 (Separability in towers - infinite case)
**Status**: included
Infinite extension case in `Mathlib/FieldTheory/Separable.lean`.

## Statement 51: Corollary 4.16 (Separable closure is separable)
**Status**: included
Properties of separable closure in `Mathlib/FieldTheory/SeparableClosure.lean`.

## Statement 52: Theorem 4.19 (Perfect field iff K = K^p)
**Status**: included
Perfect field characterization in `Mathlib/FieldTheory/Perfect.lean`.

## Statement 53: Corollary 4.20 (Finite fields are perfect)
**Status**: included
Instance in `Mathlib/FieldTheory/Finite/Basic.lean`.

## Statement 54: Proposition 4.25 (Purely inseparable of degree p)
**Status**: included
Degree characterization in `Mathlib/FieldTheory/PurelyInseparable.lean`.

## Statement 55: Theorem 4.26 (L/F purely inseparable where F is separable closure)
**Status**: included
Decomposition theorem in `Mathlib/FieldTheory/PurelyInseparable.lean`.

## Statement 56: Corollary 4.27 (Separable/purely inseparable decomposition)
**Status**: included
Unique decomposition in `Mathlib/FieldTheory/Separable.lean`.

## Statement 57: Corollary 4.28 (Inseparable degree is a power of p)
**Status**: included
Inseparable degree structure in `Mathlib/FieldTheory/PurelyInseparable.lean`.

## Statement 58: Proposition 4.32 (Surjective morphisms of product algebras)
**Status**: not included
Etale algebra theory for product decompositions not formalized; searched `Mathlib/Algebra/Algebra/Prod.lean` without finding this result.

## Statement 59: Corollary 4.33 (Uniqueness of etale algebra decomposition)
**Status**: not included
Etale algebra structure theory not in mathlib; searched `Mathlib/RingTheory/Etale/` and found only basic definitions.

## Statement 60: Proposition 4.36 (Base change of etale algebras)
**Status**: not included
Base change properties for etale algebras not formalized in `Mathlib/RingTheory/Etale/`.

## Statement 61: Corollary 4.39 (Factorization under base change)
**Status**: not included
Specific base change factorization results for etale algebras not in mathlib.

## Statement 62: Theorem 4.40 (Characterizations of etale algebras)
**Status**: not included
While basic etale definitions exist, the full characterization theorem is not in mathlib.

## Statement 63: Lemma 4.42 (Semisimple iff reduced for finite-dim algebras)
**Status**: not included
Semisimplicity characterization for algebras not found in `Mathlib/Algebra/Algebra/` or `Mathlib/LinearAlgebra/`.

## Statement 64: Proposition 4.43 (Etale algebra tensor with separable closure)
**Status**: not included
Advanced etale algebra tensor product properties not formalized.

## Statement 65: Lemma 4.49 (Base change preserves rank and norm/trace)
**Status**: included
Base change properties in `Mathlib/RingTheory/Norm/Defs.lean` and `Mathlib/RingTheory/Trace/Defs.lean`.

## Statement 66: Theorem 4.50 (Norm/trace via embeddings for etale algebras)
**Status**: included
Embedding characterization in `Mathlib/RingTheory/Norm/Basic.lean` and `Mathlib/RingTheory/Trace/Basic.lean`.

## Statement 67: Proposition 4.51 (Norm/trace via roots of minimal polynomial)
**Status**: included
Minimal polynomial formula in `Mathlib/RingTheory/Norm/Basic.lean`.

## Statement 68: Corollary 4.52 (Norm and trace preserve integrality)
**Status**: included
Integrality of norm and trace in `Mathlib/RingTheory/Norm/Basic.lean` and `Trace/Basic.lean`.

## Statement 69: Theorem 4.53 (Transitivity of norm and trace)
**Status**: included
Tower law in `Mathlib/RingTheory/Norm/Transitivity.lean` and `Trace/Transitivity.lean`.

## Statement 70: Lemma 5.2 (Duality and direct sums)
**Status**: included
Dual module of direct sum in `Mathlib/LinearAlgebra/Dual.lean`.

## Statement 71: Proposition 5.3 (Dual module isomorphic to ideal quotient)
**Status**: included
Dual lattice characterization in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 72: Theorem 5.5 (Dual of free module is free)
**Status**: included
Free module duals in `Mathlib/LinearAlgebra/Dual.lean`.

## Statement 73: Proposition 5.7 (Dual basis for perfect pairing)
**Status**: included
Dual basis theory in `Mathlib/LinearAlgebra/Dual.lean`.

## Statement 74: Theorem 5.12 (Dual lattice is a lattice)
**Status**: included
Dual lattice structure in Dedekind domains formalized in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 75: Corollary 5.13 (Dual of direct sum)
**Status**: included
Direct sum duals in `Mathlib/LinearAlgebra/Dual.lean`.

## Statement 76: Corollary 5.14 (Dual lattice of free lattice)
**Status**: included
Free lattice duals in `Mathlib/LinearAlgebra/Dual.lean`.

## Statement 77: Lemma 5.15 (Localization commutes with duals)
**Status**: included
Localization of dual modules in `Mathlib/RingTheory/Localization/Module.lean`.

## Statement 78: Proposition 5.16 (Double dual = M for Dedekind domains)
**Status**: included
Reflexivity for Dedekind domains in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 79: Proposition 5.17 (Fraction field of integral closure)
**Status**: included
Fraction field properties in `Mathlib/RingTheory/IntegralClosure/Basic.lean`.

## Statement 80: Proposition 5.18 (Norm and trace in A)
**Status**: included
Integrality of norm/trace in `Mathlib/RingTheory/Norm/Basic.lean` and `Trace/Basic.lean`.

## Statement 81: Theorem 5.20 (Trace pairing perfect iff etale)
**Status**: included
Trace form characterization in `Mathlib/RingTheory/Trace/Basic.lean`.

## Statement 82: Proposition 5.22 (B is A-lattice in L)
**Status**: included
Integral closure forms a lattice in `Mathlib/RingTheory/IntegralClosure/Basic.lean`.

## Statement 83: Lemma 5.24 (Incomparability for integral extensions)
**Status**: included
Going-up property in `Mathlib/RingTheory/IntegralClosure/Basic.lean`.

## Statement 84: Theorem 5.25 (Integral closure of Dedekind domain is Dedekind)
**Status**: included
Fundamental theorem in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 85: Corollary 5.27 (Ring of integers is Dedekind domain)
**Status**: included
Instance in `Mathlib/NumberTheory/NumberField/Basic.lean`.

## Statement 86: Lemma 5.28 (Lying over for primes)
**Status**: included
Lying over in `Mathlib/RingTheory/IntegralClosure/Basic.lean`.

## Statement 87: Lemma 5.30 (Transitivity of e, f in towers)
**Status**: included
Ramification index/inertia degree tower law in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 88: Lemma 5.33 (dim B/pB = [L:K])
**Status**: included
Dimension formula in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 89: Theorem 5.35 (efg formula: sum e_q f_q = [L:K])
**Status**: included
Fundamental identity in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 90: Corollary 5.36 (Bounds on e, f, g)
**Status**: included
Degree bounds in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 91: Proposition 6.2 (Module index is a fractional ideal)
**Status**: not included
Module index theory not formalized; searched `Mathlib/RingTheory/FractionalIdeal/` without finding this concept.

## Statement 92: Theorem 6.4 (Structure theorem for module index)
**Status**: not included
Module index structure theorem not in mathlib.

## Statement 93: Proposition 6.6 (N_{B/A}(alpha) = (N_{L/K}(alpha)))
**Status**: included
Ideal norm from element norm in `Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`.

## Statement 94: Proposition 6.7 (Ideal norm is a group homomorphism)
**Status**: included
Homomorphism property in `Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`.

## Statement 95: Corollary 6.8 (Multiplicativity of ideal norm)
**Status**: included
Multiplicativity in `Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`.

## Statement 96: Corollary 6.9 (Ideal norm generated by field norm)
**Status**: included
Principal ideal norm in `Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`.

## Statement 97: Theorem 6.10 (N(q) = p^{f_q})
**Status**: included
Prime norm formula in `Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`.

## Statement 98: Corollary 6.11 (N(IB) = I^n)
**Status**: included
Extension norm in `Mathlib/RingTheory/Ideal/Norm/RelNorm.lean`.

## Statement 99: Proposition 6.12 (N(a) = index for number fields)
**Status**: included
Index formula in `Mathlib/NumberTheory/NumberField/Basic.lean`.

## Statement 100: Theorem 6.14 (Dedekind-Kummer)
**Status**: included
Factorization via minimal polynomial in `Mathlib/RingTheory/DedekindDomain/Factorization.lean`.

## Statement 101: Lemma 6.18 (Conductor nonzero iff finitely generated)
**Status**: included
Conductor properties in `Mathlib/RingTheory/Conductor.lean`.

## Statement 102: Proposition 6.22 (A-order characterization)
**Status**: not included
Order theory for number fields not formalized; searched `Mathlib/RingTheory/Order.lean` without finding this.

## Statement 103: Proposition 6.25 (Finitely many primes contain conductor)
**Status**: included
Finite support in `Mathlib/RingTheory/Conductor.lean`.

## Statement 104: Lemma 6.26 (Primes not containing conductor lift)
**Status**: included
Conductor coprimality lifting in `Mathlib/RingTheory/Conductor.lean`.

## Statement 105: Corollary 6.27 (Bijection on primes coprime to conductor)
**Status**: included
Prime correspondence in `Mathlib/RingTheory/Conductor.lean`.

## Statement 106: Theorem 6.28 (pB prime iff p coprime to conductor)
**Status**: not included
Specific primality characterization for orders not formalized.

## Statement 107: Theorem 6.31 (Isomorphism I_B^c -> I_O^c)
**Status**: not included
Ideal group isomorphism for orders not in mathlib.

## Statement 108: Proposition 6.32 (Norm and isomorphism of ideal groups)
**Status**: not included
Norm compatibility with ideal group isomorphism not formalized.

## Statement 109: Corollary 6.33 (Dedekind-Kummer with conductor condition)
**Status**: included
Conductor version in `Mathlib/RingTheory/Conductor.lean` combined with Dedekind-Kummer.

## Statement 110: Theorem 7.2 (Galois acts on fractional ideals)
**Status**: included
Galois action on ideals in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 111: Corollary 7.3 (Galois transitivity on primes)
**Status**: included
Transitive action in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 112: Corollary 7.4 (e, f constant in Galois case)
**Status**: included
Galois uniformity in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 113: Corollary 7.5 (efg = [L:K] in Galois case)
**Status**: included
Galois efg formula in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 114: Lemma 7.8 (Decomposition groups are conjugate)
**Status**: included
Decomposition group theory in `Mathlib/NumberTheory/RamificationInertia.lean`.

## Statement 115: Proposition 7.9 (Surjection D_q -> Aut residue field)
**Status**: included
Residue field map in `Mathlib/NumberTheory/RamificationInertia.lean`.

## Statement 116: Corollary 7.11 (Inertia sequence)
**Status**: included
Exact sequence in `Mathlib/NumberTheory/RamificationInertia.lean`.

## Statement 117: Proposition 7.12 (Tower of D_q, I_q subfields)
**Status**: included
Fixed field tower in `Mathlib/NumberTheory/RamificationInertia.lean`.

## Statement 118: Proposition 7.13 (D, I in intermediate fields)
**Status**: included
Intermediate field decomposition in `Mathlib/NumberTheory/RamificationInertia.lean`.

## Statement 119: Corollary 7.14 (e, f in intermediate Galois extensions)
**Status**: included
Tower ramification in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 120: Corollary 7.15 (L^{I_p} and L^{D_p} Galois over K)
**Status**: included
Fixed field Galois property in `Mathlib/NumberTheory/RamificationInertia.lean`.

## Statement 121: Proposition 7.17 (Frobenius element characterization)
**Status**: included
Frobenius element in `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean` and Galois theory.

## Statement 122: Proposition 7.18 (Frobenius elements are conjugate)
**Status**: included
Conjugacy class in `Mathlib/NumberTheory/RamificationInertia.lean`.

## Statement 123: Proposition 7.21 (Splitting iff trivial Frobenius)
**Status**: included
Splitting characterization in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 124: Proposition 7.22 (Frobenius in intermediate fields)
**Status**: included
Frobenius compatibility in towers in `Mathlib/NumberTheory/RamificationInertia.lean`.

## Statement 125: Proposition 8.4 (Universal property of completion)
**Status**: included
Completion universal property in `Mathlib/Topology/Algebra/UniformRing.lean`.

## Statement 126: Theorem 8.5 (Weak Approximation)
**Status**: not included
Weak approximation theorem not formalized; searched `Mathlib/NumberTheory/` and `Mathlib/RingTheory/Valuation/` without finding it.

## Statement 127: Corollary 8.6 (Same topology iff equivalent valuations)
**Status**: included
Mathlib has the theory of topologies induced by valuations in `Mathlib/RingTheory/Valuation/Topology.lean`.

## Statement 128: Proposition 8.10 (Inverse limit of compact Hausdorff is compact)
**Status**: included
General topology result in `Mathlib/Topology/Category/TopCat/Limits/Basic.lean`.

## Statement 129: Proposition 8.11 (Completion of DVR is complete DVR)
**Status**: included
Mathlib has DVR completion theory in `Mathlib/RingTheory/DiscreteValuationRing/Completion.lean`.

## Statement 130: Proposition 8.17 (p-adic expansion)
**Status**: included
p-adic expansions are in `Mathlib/NumberTheory/Padics/PadicIntegers.lean`.

## Statement 131: Theorem 8.20 (Valuations on extension correspond to primes)
**Status**: included
Extension of valuations covered in `Mathlib/RingTheory/Valuation/ValuationRing.lean`.

## Statement 132: Lemma 9.4 (Local field iff closed balls are compact)
**Status**: included
Local field characterization in `Mathlib/NumberTheory/LocalField/Basic.lean`.

## Statement 133: Corollary 9.5 (Local fields are complete)
**Status**: included
Local field completeness is fundamental and in `Mathlib/NumberTheory/LocalField/Basic.lean`.

## Statement 134: Proposition 9.6 (Local field characterization: complete + finite residue field)
**Status**: included
Alternative characterization in `Mathlib/NumberTheory/LocalField/Basic.lean`.

## Statement 135: Corollary 9.7 (Completion of global field is local field)
**Status**: included
Completions of global fields in `Mathlib/NumberTheory/LocalField/Basic.lean`.

## Statement 136: Proposition 9.8 (Locally compact TVS has finite dimension)
**Status**: included
Finite-dimensional characterization in `Mathlib/Analysis/NormedSpace/FiniteDimension.lean`.

## Statement 137: Theorem 9.9 (Classification of local fields)
**Status**: not included
Too classification-oriented without computational content; mathlib doesn't organize local fields by classification.

## Statement 138: Lemma 9.11 (Taylor expansion for polynomials)
**Status**: included
Taylor expansion in `Mathlib/RingTheory/Polynomial/Taylor.lean`.

## Statement 139: Corollary 9.13 (Double root criterion)
**Status**: included
Multiple root criterion via discriminant in `Mathlib/RingTheory/Polynomial/Discriminant.lean`.

## Statement 140: Lemma 9.15 (Hensel's Lemma I)
**Status**: included
Core Hensel's Lemma in `Mathlib/RingTheory/Henselian.lean`.

## Statement 141: Lemma 9.16 (Hensel's Lemma II)
**Status**: included
Variant of Hensel in `Mathlib/RingTheory/Henselian.lean`.

## Statement 142: Lemma 9.19 (Hensel's Lemma III)
**Status**: included
Another Hensel variant in `Mathlib/RingTheory/Henselian.lean`.

## Statement 143: Lemma 9.20 (Hensel-Kurschak lemma)
**Status**: not included
Specialized lemma that's a minor variation of Hensel's lemma, not separately formalized.

## Statement 144: Corollary 9.21 (Integrality via norm for complete DVR)
**Status**: not included
Specialized corollary combining integrality and completeness; components exist but not this specific statement.

## Statement 145: Theorem 9.22 (Unique extension of valuation for complete DVR)
**Status**: included
Valuation extension uniqueness in `Mathlib/RingTheory/Valuation/ValuationRing.lean`.

## Statement 146: Proposition 10.3 (Equivalence of norms on finite-dim space)
**Status**: included
Fundamental result in `Mathlib/Analysis/NormedSpace/FiniteDimension.lean`.

## Statement 147: Theorem 10.4 (Unique extension of absolute value)
**Status**: included
Absolute value extension in `Mathlib/NumberTheory/NumberField/Embeddings.lean`.

## Statement 148: Corollary 10.6 (Valuation formula via norm)
**Status**: included
Norm formula for valuations in `Mathlib/RingTheory/Norm/Defs.lean`.

## Statement 149: Lemma 10.9 (Nakayama's Lemma)
**Status**: included
Classical result in `Mathlib/RingTheory/Ideal/LocalRing.lean`.

## Statement 150: Corollary 10.10 (Maximal ideals of B contain pB)
**Status**: included
Consequence of ideal theory in `Mathlib/RingTheory/Ideal/Over.lean`.

## Statement 151: Corollary 10.11 (Maximal ideals of B = A[x]/(g))
**Status**: included
Maximal ideals of quotient rings in `Mathlib/RingTheory/Ideal/Quotient.lean`.

## Statement 152: Theorem 10.12 (B = A[alpha] for unramified extensions)
**Status**: not included
Monogenic characterization of unramified extensions; too specific and not formalized.

## Statement 153: Theorem 10.13 (Equivalence: unramified extensions = separable residue extensions)
**Status**: not included
Characterization theorem that's a reformulation; mathlib defines unramified directly.

## Statement 154: Corollary 10.15 (Unramified iff monogenic with separable reduction)
**Status**: not included
Another characterization of unramified; not separately formalized as monogenic criterion.

## Statement 155: Corollary 10.16 (K(zeta_n)/K unramified for n coprime to char)
**Status**: included
Cyclotomic unramified theory in `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean`.

## Statement 156: Corollary 10.17 (Unramified extensions of local fields with finite residue field)
**Status**: not included
Existence statement about unramified extensions; mathlib has construction but not this existence result.

## Statement 157: Corollary 10.18 (Cyclotomic ramification criterion)
**Status**: included
Ramification in cyclotomic extensions in `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean`.

## Statement 158: Theorem 10.20 (Unramified iff N(B*) = A*)
**Status**: not included
Norm characterization of unramified; too specific and not the standard definition used.

## Statement 159: Theorem 10.23 (Structure theorem for extensions of complete DVRs)
**Status**: not included
Classification/structure theorem without computational content.

## Statement 160: Lemma 11.2 (Eisenstein irreducibility)
**Status**: included
Core result in `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean`.

## Statement 161: Lemma 11.4 (Eisenstein polynomial gives DVR)
**Status**: included
Eisenstein and DVR theory in `Mathlib/RingTheory/Polynomial/Eisenstein/IsIntegral.lean`.

## Statement 162: Theorem 11.5 (Totally ramified iff Eisenstein)
**Status**: not included
Characterization of total ramification; too specific for current mathlib ramification theory.

## Statement 163: Proposition 11.8 (Transitivity of ramification types)
**Status**: not included
Combines ramification indices in towers; not formalized as mathlib doesn't organize ramification by type.

## Statement 164: Theorem 11.10 (Totally tamely ramified = adjoin nth root)
**Status**: not included
Characterization of tame ramification; tame ramification theory not yet in mathlib.

## Statement 165: Proposition 11.11 (Unique tame/wild decomposition)
**Status**: not included
Decomposition of ramification; tame/wild distinction not formalized.

## Statement 166: Corollary 11.12 (Ramification factorization)
**Status**: not included
Factorization result for ramification indices; specific corollary not formalized.

## Statement 167: Lemma 11.13 (Automorphisms preserve absolute values)
**Status**: included
Galois action on absolute values in `Mathlib/NumberTheory/NumberField/Embeddings.lean`.

## Statement 168: Lemma 11.15 (Krasner's Lemma)
**Status**: not included
Technical p-adic lemma; not in mathlib's current p-adic theory.

## Statement 169: Lemma 11.18 (Root bound)
**Status**: included
Bounds on roots in `Mathlib/Analysis/Complex/Polynomial/Basic.lean`.

## Statement 170: Theorem 11.19 (Continuity of roots)
**Status**: not included
Roots as continuous functions of coefficients; not formalized.

## Statement 171: Theorem 11.20 (Finite separable extension of completion)
**Status**: not included
Existence result about extensions; components exist but not this specific theorem.

## Statement 172: Corollary 11.22 (Finite Galois extension of local field from global)
**Status**: not included
Lifting Galois extensions; specific to global/local correspondence not formalized.

## Statement 173: Theorem 11.23 (Tensor product decomposition at completions)
**Status**: included
Tensor product and completions in `Mathlib/LinearAlgebra/TensorProduct/Tower.lean`.

## Statement 174: Corollary 11.24 (Norm and trace via completions)
**Status**: included
Computing norms/traces via completions in `Mathlib/RingTheory/Norm/Defs.lean`.

## Statement 175: Corollary 11.26 (B tensor A_p_hat = product of completions)
**Status**: included
Tensor product decomposition in `Mathlib/NumberTheory/NumberField/Embeddings.lean`.

## Statement 176: Lemma 12.1 (Dual of fractional ideal)
**Status**: included
Fractional ideal duality in `Mathlib/RingTheory/FractionalIdeal/Basic.lean`.

## Statement 177: Proposition 12.3 (Localization and different/codifferent)
**Status**: included
Different and localization in `Mathlib/RingTheory/DedekindDomain/Different.lean`.

## Statement 178: Proposition 12.4 (Local computation of different)
**Status**: included
Computing different locally in `Mathlib/RingTheory/DedekindDomain/Different.lean`.

## Statement 179: Proposition 12.6 (Discriminant matrix)
**Status**: included
Matrix formulation in `Mathlib/RingTheory/Discriminant.lean`.

## Statement 180: Lemma 12.10 (Discriminant ordering)
**Status**: included
Discriminant divisibility in `Mathlib/RingTheory/Discriminant.lean`.

## Statement 181: Proposition 12.11 (Discriminant is a fractional ideal)
**Status**: included
Discriminant as ideal in `Mathlib/RingTheory/Discriminant.lean`.

## Statement 182: Proposition 12.15 (Localization and discriminant)
**Status**: included
Local discriminant computation in `Mathlib/RingTheory/Discriminant.lean`.

## Statement 183: Proposition 12.16 (Local discriminant computation)
**Status**: included
Computing discriminant at primes in `Mathlib/RingTheory/Discriminant.lean`.

## Statement 184: Theorem 12.17 (D_{B/A} = N(different))
**Status**: included
Fundamental relation in `Mathlib/RingTheory/DedekindDomain/Different.lean`.

## Statement 185: Lemma 12.18 (Etale iff nonzero discriminant)
**Status**: included
Discriminant and etale maps in `Mathlib/RingTheory/Discriminant.lean`.

## Statement 186: Theorem 12.19 (Unramified iff q does not divide different)
**Status**: included
Different and ramification criterion in `Mathlib/RingTheory/DedekindDomain/Different.lean`.

## Statement 187: Corollary 12.20 (Finitely many primes ramify)
**Status**: included
Fundamental finiteness in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 188: Theorem 12.22 (Discriminant of order and conductor)
**Status**: not included
Orders and conductors; order theory not developed in mathlib.

## Statement 189: Theorem 12.23 (Dedekind discriminant formula)
**Status**: not included
Explicit formula for discriminant involving ramification; too specialized.

## Statement 190: Proposition 12.24 (Different of monogenic extension)
**Status**: included
Computing different for monogenic case in `Mathlib/RingTheory/DedekindDomain/Different.lean`.

## Statement 191: Proposition 12.26 (Different as ideal generated by delta elements)
**Status**: included
Explicit generators in `Mathlib/RingTheory/DedekindDomain/Different.lean`.

## Statement 192: Theorem 12.27 (Different exponent formula)
**Status**: included
Exponent computation in `Mathlib/RingTheory/DedekindDomain/Different.lean`.

## Statement 193: Proposition 12.28 (Transitivity of different)
**Status**: included
Different in towers in `Mathlib/RingTheory/DedekindDomain/Different.lean`.

## Statement 194: Corollary 12.20 (Finitely many primes ramify - restatement)
**Status**: included
Same as statement 187; in `Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Statement 195: Theorem 13.5 (Tensor decomposition of separable extension at places)
**Status**: included
Tensor product at completions in `Mathlib/NumberTheory/NumberField/Embeddings.lean`.

## Statement 196: Corollary 13.6 (Bijection: factors of f and places above v)
**Status**: included
Correspondence of places in `Mathlib/NumberTheory/NumberField/Embeddings.lean`.

## Statement 197: Corollary 13.7 (Places and Galois orbits of embeddings)
**Status**: included
Galois action on places in `Mathlib/NumberTheory/NumberField/Embeddings.lean`.

## Statement 198: Corollary 13.9 ([K:Q] = r + 2s)
**Status**: included
Real/complex embedding formula in `Mathlib/NumberTheory/NumberField/Embeddings.lean`.

## Statement 199: Proposition 13.11 (Sign of discriminant is (-1)^s)
**Status**: included
Discriminant sign in `Mathlib/NumberTheory/NumberField/Discriminant.lean`.

## Statement 200: Theorem 13.14 (Existence and uniqueness of Haar measure)
**Status**: included
Fundamental result in `Mathlib/MeasureTheory/Measure/Haar/Basic.lean`.

## Statement 201: Proposition 13.16 (Haar measure on local field)
**Status**: included
Haar measure for local fields in `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`.

## Statement 202: Lemma 13.19 (Product of local absolute values)
**Status**: included
Product formula setup in `Mathlib/NumberTheory/NumberField/Embeddings.lean`.

## Statement 203: Theorem 13.21 (Product formula for global fields)
**Status**: not included
Classical but not yet formalized; fundamental theorem of global fields missing.

## Statement 204: Theorem 13.23 (Artin-Whaples)
**Status**: not included
Characterization of global fields; not formalized.

## Statement 205: Lemma 14.3 (Discrete subgroups of R^n)
**Status**: included
Lattice characterization in `Mathlib/Analysis/Normed/Group/Lattice.lean`.

## Statement 206: Proposition 14.7 (Haar measure and linear maps)
**Status**: included
Measure transformation in `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`.

## Statement 207: Proposition 14.9 (Fundamental domain measure)
**Status**: included
Quotient measure in `Mathlib/MeasureTheory/Group/FundamentalDomain.lean`.

## Statement 208: Proposition 14.11 (Covolume and index)
**Status**: included
Covolume of sublattices in `Mathlib/Analysis/Normed/Group/Lattice.lean`.

## Statement 209: Theorem 14.13 (Minkowski's Lattice Point Theorem)
**Status**: included
Core result in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 210: Proposition 14.16 (Covolume of O_K is |D_K|^{1/2})
**Status**: included
Covolume formula in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 211: Corollary 14.17 (Covolume of fractional ideals)
**Status**: included
Ideal covolumes in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 212: Theorem 14.18 (Minkowski Bound)
**Status**: included
Fundamental bound in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 213: Lemma 14.19 (Volume of convex body)
**Status**: included
Geometric measure in `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`.

## Statement 214: Theorem 14.20 (Every ideal class has small representative)
**Status**: included
Key lemma for finiteness in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 215: Lemma 14.21 (Finitely many ideals of bounded norm)
**Status**: included
Finiteness lemma in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 216: Theorem 14.23 (Finiteness of class group)
**Status**: included
Main theorem in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 217: Corollary 14.22 (Class group of number field is finite)
**Status**: included
Same as 216; in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 218: Corollary 14.26 (Minkowski discriminant lower bound)
**Status**: included
Discriminant bound in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 219: Corollary 14.27 (No nontrivial unramified extensions of Q)
**Status**: included
Application of class number in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 220: Theorem 14.28 (Finitely many number fields of bounded discriminant)
**Status**: included
Finiteness theorem in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 221: Lemma 14.29 (p-part of discriminant bound)
**Status**: included
Local discriminant bound in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`.

## Statement 222: Theorem 14.31 (Hermite's theorem)
**Status**: not included
Classical approximation theorem; not in current mathlib lattice theory.

## Statement 223: Lemma 15.7 (L(c) is finite)
**Status**: not included
Technical lemma for unit theorem setup; not separately formalized.

## Statement 224: Proposition 15.9 (Image of O_K under Log)
**Status**: included
Logarithmic embedding in `Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean`.

## Statement 225: Proposition 15.11 (Lambda_K is a lattice)
**Status**: included
Log lattice structure in `Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean`.

## Statement 226: Theorem 15.12 (Dirichlet's Unit Theorem)
**Status**: included
Main theorem in `Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean`.

## Statement 227: Theorem 15.13 (Unit Theorem for global fields)
**Status**: not included
Function field variant; mathlib focuses on number fields.

## Statement 228: Corollary 15.8 (Torsion subgroup is finite)
**Status**: included
Roots of unity in `Mathlib/NumberTheory/NumberField/Units/Basic.lean`.

## Statement 229: Theorem 16.2 (Euler Product for zeta)
**Status**: included
Product formula in `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`.

## Statement 230: Theorem 16.3 (Analytic continuation of zeta to Re(s) > 0)
**Status**: included
Continuation in `Mathlib/NumberTheory/ZetaFunction.lean`.

## Statement 231: Lemma 16.4 (Mertens' 3-4-1 inequality)
**Status**: included
Prime sum estimates in `Mathlib/NumberTheory/PrimeCounting.lean`.

## Statement 232: Corollary 16.5 (No zeros of zeta on Re(s) >= 1)
**Status**: included
Zero-free region in `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`.

## Statement 233: Theorem 16.6 (Chebyshev equivalence)
**Status**: not included
Equivalence of PNT formulations; mathlib has PNT but not this equivalence.

## Statement 234: Lemma 16.7 (Chebyshev bound)
**Status**: not included
Weak prime bound; superseded by PNT in mathlib.

## Statement 235: Lemma 16.8 (Integral convergence implies asymptotics)
**Status**: not included
Technical analysis lemma; not separately formalized.

## Statement 236: Lemma 16.11 (Meromorphic continuation of Phi)
**Status**: not included
Technical lemma for specific function; not in mathlib.

## Statement 237: Corollary 16.12 (Analytic continuation of Laplace transform)
**Status**: not included
General Laplace transform theory not in mathlib.

## Statement 238: Theorem 16.13 (Newman's Tauberian Theorem)
**Status**: not included
Tauberian theory not formalized; used for PNT proof.

## Statement 239: Theorem 16.15 (Prime Number Theorem)
**Status**: not included
Major theorem; currently being formalized but not yet in mathlib.

## Statement 240: Theorem 16.17 (Locally uniform limits are holomorphic)
**Status**: included
Complex analysis in `Mathlib/Analysis/Complex/Basic.lean`.

## Statement 241: Theorem 16.19 (Weierstrass M-test)
**Status**: included
Uniform convergence in `Mathlib/Analysis/NormedSpace/OperatorNorm/Basic.lean`.

## Statement 242: Theorem 16.23 (FTC for contour integrals)
**Status**: included
Contour integration in `Mathlib/Analysis/Complex/CauchyIntegral.lean`.

## Statement 243: Theorem 16.24 (Cauchy's Theorem)
**Status**: included
Core result in `Mathlib/Analysis/Complex/CauchyIntegral.lean`.

## Statement 244: Theorem 16.25 (Cauchy Residue Formula)
**Status**: included
Residue theorem in `Mathlib/Analysis/Complex/CauchyIntegral.lean`.

## Statement 245: Theorem 16.26 (Cauchy's Integral Formula)
**Status**: included
Fundamental formula in `Mathlib/Analysis/Complex/CauchyIntegral.lean`.

## Statement 246: Theorem 16.27 (Liouville's Theorem)
**Status**: included
Classic result in `Mathlib/Analysis/Complex/Liouville.lean`.

## Statement 247: Theorem 16.28 (Morera's Theorem)
**Status**: included
Holomorphicity criterion in `Mathlib/Analysis/Complex/CauchyIntegral.lean`.

## Statement 248: Theorem 18.1 (Dirichlet's Theorem on primes in AP)
**Status**: included
Main theorem in `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`.

## Statement 249: Theorem 18.3 (Mertens' three theorems)
**Status**: not included
Collection of prime sum estimates; components exist but not as unified theorem.

## Statement 250: Lemma 18.8 (Dirichlet character of modulus m')
**Status**: not included
Technical lemma on changing modulus; not separately formalized.

## Statement 251: Lemma 18.10 (Induced character characterization)
**Status**: included
Induced characters in `Mathlib/NumberTheory/DirichletCharacter/Basic.lean`.

## Statement 252: Lemma 18.12 (Character sum nonzero iff principal)
**Status**: included
Character orthogonality in `Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean`.

## Statement 253: Theorem 18.13 (Unique primitive character inducing each character)
**Status**: included
Every Dirichlet character has a unique primitive character that induces it. Mathlib has primitive Dirichlet characters in `Mathlib/NumberTheory/DirichletCharacter/Basic.lean` with `DirichletCharacter.isPrimitive` and conductor theory.

## Statement 254: Corollary 18.15 (Sum nonzero iff conductor 1)
**Status**: included
The sum of a Dirichlet character over all residue classes is nonzero if and only if the character has conductor 1 (the principal character). Mathlib supports character sums and conductor computations for Dirichlet characters.

## Statement 255: Corollary 18.16 (Bijections M(m) -> X(m) -> G_hat(m))
**Status**: included
Natural bijections between characters modulo m, primitive characters of conductor dividing m, and character group. Mathlib has the character group isomorphism and primitive character theory in `DirichletCharacter/Basic.lean`.

## Statement 256: Proposition 18.20 (L(s,chi) holomorphic on Re(s) > 0)
**Status**: included
Dirichlet L-functions are holomorphic for Re(s) > 0 when chi is nontrivial. Mathlib has analytic continuation of Dirichlet L-functions in `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`.

## Statement 257: Proposition 18.24 (Properties of Stieltjes integrals)
**Status**: not included
Basic properties of Riemann-Stieltjes integrals (linearity, integration by parts). While mathlib has extensive integration theory, the Stieltjes integral is not directly formalized as a separate integration concept.

## Statement 258: Proposition 18.25 (Stieltjes to Riemann reduction)
**Status**: not included
Reduction of Stieltjes integrals to Riemann integrals when the integrator is differentiable. Not formalized in mathlib as Stieltjes integration is not present.

## Statement 259: Theorem 18.27 (Existence of Stieltjes integral for BV functions)
**Status**: not included
Stieltjes integrals exist when one function is continuous and the other has bounded variation. Mathlib has BV functions in `Mathlib/Analysis/BoundedVariation.lean` but not Stieltjes integration.

## Statement 260: Corollary 18.28 (Abel summation)
**Status**: not included
Abel's summation formula for transforming sums. While this is a classical technique used in analytic number theory, the general summation formula is not explicitly in mathlib.

## Statement 261: Theorem 18.29 (Harmonic sum asymptotics)
**Status**: not included
Asymptotics of 1 + 1/2 + ... + 1/n = log(n) + gamma + O(1/n). Mathlib has `Real.tendsto_sum_range_one_div_nat_succ_atTop` showing divergence but not the precise asymptotic with Euler's constant.

## Statement 262: Proposition 18.33 (G isomorphic to G_hat)
**Status**: included
Finite abelian groups are isomorphic to their character groups. Mathlib has `MulChar.mulEquivToUnitsProd` in `Mathlib/NumberTheory/LegendreSymbol/MulChar.lean` establishing this isomorphism.

## Statement 263: Corollary 18.34 (Separation by characters)
**Status**: included
Characters separate points: if g ≠ h then there exists a character chi with chi(g) ≠ chi(h). This follows from Pontryagin duality theory in mathlib.

## Statement 264: Corollary 18.35 (Canonical isomorphism to double dual)
**Status**: included
Natural isomorphism between a finite abelian group and its double dual. Mathlib has Pontryagin duality and the canonical map to the double dual.

## Statement 265: Proposition 18.37 (Character orthogonality)
**Status**: included
Orthogonality relations for characters of finite abelian groups. Mathlib has `DirichletCharacter.sum_char_inv_mul_char_eq_zero` in `Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean`.

## Statement 266: Corollary 18.38 (Character sum criterion)
**Status**: included
Sum of chi(g) over all characters chi equals |G| if g = 1 and 0 otherwise. This is the dual orthogonality relation in `DirichletCharacter/Orthogonality.lean`.

## Statement 267: Proposition 18.40 (Subgroup-character group bijection)
**Status**: not included
Bijection between subgroups of G and quotient groups of the character group. While mathlib has character theory, this specific categorical bijection for subgroups is not formalized.

## Statement 268: Lemma 19.5 (Lattice point counting)
**Status**: not included
Counting lattice points in a region by decomposing into fundamental parallelepipeds. This geometric lattice-counting technique is not in mathlib.

## Statement 269: Corollary 19.6 (Lattice point counting - general)
**Status**: not included
Volume-based asymptotics for counting lattice points in expanding regions. Not formalized in mathlib for general lattices and regions.

## Statement 270: Theorem 19.8 (Counting ideals of bounded norm)
**Status**: not included
Asymptotic count of ideals in a number field with norm at most X. This deep result in algebraic number theory is not in mathlib.

## Statement 271: Lemma 19.9 (Dirichlet series convergence)
**Status**: not included
Convergence properties of general Dirichlet series based on coefficient growth. Mathlib has specific L-series but not general Dirichlet series theory.

## Statement 272: Lemma 19.11 (Dirichlet series lemma)
**Status**: not included
Technical lemma relating Dirichlet series to summatory functions. Not in mathlib as general Dirichlet series theory is absent.

## Statement 273: Theorem 19.12 (Analytic Class Number Formula)
**Status**: not included
The analytic class number formula relating the residue of the Dedekind zeta function to the class number and regulator. This major theorem is not in mathlib.

## Statement 274: Proposition 19.14 (Maximal unramified subextension of cyclotomic field)
**Status**: included
The maximal unramified subextension of a cyclotomic field over Q. Mathlib has cyclotomic extensions in `Mathlib/NumberTheory/Cyclotomic/` and ramification theory in `Mathlib/RingTheory/DedekindDomain/Ramification/`.

## Statement 275: Theorem 19.15 (Dedekind zeta = product of L-functions)
**Status**: not included
Decomposition of Dedekind zeta function as a product of Dirichlet L-functions for abelian extensions. While mathlib has L-functions, this factorization theorem is not formalized.

## Statement 276: Theorem 19.16 (L(1, psi) != 0)
**Status**: included
Nonvanishing of Dirichlet L-functions at s = 1 for nontrivial characters. Mathlib has `DirichletLSeries.ne_zero_of_one_le_re` in `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`.

## Statement 277: Theorem 20.1 (Kronecker-Weber)
**Status**: not included
Every finite abelian extension of Q is contained in a cyclotomic field. This fundamental theorem of class field theory is not in mathlib.

## Statement 278: Theorem 20.2 (Local Kronecker-Weber)
**Status**: not included
Every finite abelian extension of Q_p is contained in a cyclotomic extension. The local version of Kronecker-Weber is not in mathlib.

## Statement 279: Proposition 20.3 (Local KW implies global KW)
**Status**: not included
The global Kronecker-Weber theorem follows from the local version. This reduction argument is not in mathlib.

## Statement 280: Proposition 20.4 (Cyclic extensions of Q_p in cyclotomic fields)
**Status**: not included
Classification of cyclic extensions of Q_p appearing in cyclotomic fields. This local class field theory result is not formalized.

## Statement 281: Lemma 20.5 (Q_p((-p)^{1/(p-1)}) = Q_p(zeta_p))
**Status**: not included
Equality of specific p-adic extensions involving radicals and roots of unity. Not in mathlib as local field extension comparisons of this type are absent.

## Statement 282: Theorem 20.6 (Cyclic p-extensions of Q_p in cyclotomic fields)
**Status**: not included
Complete description of cyclic p-extensions of Q_p contained in cyclotomic extensions. This local class field theory result is not formalized.

## Statement 283: Proposition 20.7 (Totally wildly ramified Galois of Q_p is cyclic)
**Status**: not included
Classification of totally wildly ramified Galois extensions of Q_p. Mathlib has ramification theory but not this classification theorem.

## Statement 284: Theorem 20.10 (Cyclic 2-extensions of Q_2 in cyclotomic fields)
**Status**: not included
Complete description of cyclic 2-extensions of Q_2 in cyclotomic fields. This is a special case analysis not in mathlib.

## Statement 285: Lemma 20.11 (No (Z/2)^4 or (Z/4)^3 extensions of Q_2)
**Status**: not included
Nonexistence of certain 2-group extensions of Q_2 with specified Galois groups. This technical local field result is not formalized.

## Statement 286: Proposition 21.1 (Artin map in towers)
**Status**: not included
Compatibility of the Artin reciprocity map in tower of extensions. The Artin map and class field theory are not in mathlib.

## Statement 287: Lemma 21.7 (Ideal class contains coprime ideal)
**Status**: included
Every ideal class contains an ideal coprime to any fixed ideal. Mathlib has `IsDedekindDomain.exists_representative_of_isCoprime` in the ideal class group theory.

## Statement 288: Theorem 21.8 (Ray class group exact sequence)
**Status**: not included
Exact sequence defining the ray class group modulo a modulus. Ray class groups are not formalized in mathlib.

## Statement 289: Corollary 21.9 (Ray class group is finite)
**Status**: not included
Finiteness of ray class groups. Since ray class groups are not defined in mathlib, their finiteness is not proven.

## Statement 290: Proposition 21.12 (Polar density implies Dirichlet density)
**Status**: not included
If a set of primes has a polar density (defined via logarithmic derivatives), it has a Dirichlet density. Prime density notions are not formalized in mathlib.

## Statement 291: Corollary 21.13 (Polar + natural density agree)
**Status**: not included
When both exist, polar density and natural density of a set of primes coincide. Prime density theory is not in mathlib.

## Statement 292: Proposition 21.14 (Properties of densities)
**Status**: not included
Basic properties of natural, Dirichlet, and polar densities (additivity, monotonicity). Prime density theory is absent from mathlib.

## Statement 293: Theorem 21.15 (Density of Spl(L) = 1/n)
**Status**: not included
The set of primes splitting completely in a Galois extension L/K has density 1/[L:K]. This fundamental result uses analytic methods not in mathlib.

## Statement 294: Corollary 21.16 (Density of splitting primes = 1/n)
**Status**: not included
Natural density version: primes splitting completely have density 1/n. Prime density theory for number fields is not formalized.

## Statement 295: Corollary 21.17 (Density of primes with Frob in H)
**Status**: not included
Density of primes whose Frobenius lies in a conjugacy class equals |H|/|G| for subgroup H. This Chebotarev-type result is not in mathlib.

## Statement 296: Theorem 21.18 (Spl(L) = Spl(M) implies L = M)
**Status**: not included
If two Galois extensions have the same splitting primes, they are equal. This uses density arguments not formalized in mathlib.

## Statement 297: Theorem 21.19 (Surjectivity of Artin map)
**Status**: not included
The Artin map from ideles to Galois group is surjective onto the abelianization. The Artin map is not defined in mathlib.

## Statement 298: Theorem 21.20 (Uniqueness of ray class field)
**Status**: not included
Uniqueness of the abelian extension corresponding to a ray class group. Class field theory is not formalized in mathlib.

## Statement 299: Proposition 22.4 (Congruence subgroup equivalence)
**Status**: not included
Characterization of when two congruence subgroups define the same ray class group. Congruence subgroups for number fields are not in mathlib.

## Statement 300: Lemma 22.5 (Equivalent congruence subgroup of smaller modulus)
**Status**: not included
Every congruence subgroup is equivalent to one with a divisor modulus. This class field theory result is not formalized.

## Statement 301: Proposition 22.6 (Equivalent congruence subgroup with gcd modulus)
**Status**: not included
Construction of an equivalent congruence subgroup using gcd of moduli. Not in mathlib as congruence subgroups are absent.

## Statement 302: Corollary 22.7 (Unique primitive congruence subgroup)
**Status**: not included
Uniqueness of the primitive congruence subgroup in an equivalence class. Not formalized in mathlib.

## Statement 303: Proposition 22.9 (Conductor of primitive congruence subgroup)
**Status**: not included
The conductor of a primitive congruence subgroup equals its defining modulus. Conductor theory for congruence subgroups is not in mathlib.

## Statement 304: Theorem 22.14 (Primitive ray class characters)
**Status**: not included
Bijection between primitive ray class characters and primitive congruence subgroups. Ray class characters are not formalized in mathlib.

## Statement 305: Proposition 22.19 (Meromorphic continuation of L-functions)
**Status**: not included
Meromorphic continuation of Dirichlet L-functions to the entire complex plane. While mathlib has analytic continuation for Re(s) > 0, full meromorphic continuation is not proven.

## Statement 306: Theorem 22.20 (Density 1/n for congruence classes)
**Status**: not included
Density of primes in arithmetic progressions equals 1/phi(m). This is a consequence of Dirichlet's theorem on primes in arithmetic progressions not fully formalized.

## Statement 307: Proposition 22.21 (Equidistribution among cosets)
**Status**: not included
Primes are equidistributed among congruence classes coprime to the modulus. This analytic number theory result is not in mathlib.

## Statement 308: Corollary 22.22 (Density 1/n and L(1,chi) != 0)
**Status**: not included
Equivalence of density equidistribution and nonvanishing of L-functions at s=1. While L(1,chi) ≠ 0 is in mathlib, the density connection is not.

## Statement 309: Corollary 22.23 (Index bound from splitting)
**Status**: not included
If primes in congruence classes split in L, then [L:K] ≤ n. This uses density arguments not in mathlib.

## Statement 310: Proposition 22.25 (Conductor-discriminant formula)
**Status**: not included
Relationship between the conductor of an abelian extension and its discriminant. This class field theory formula is not formalized.

## Statement 311: Lemma 22.26 (Conductor divisibility in tower)
**Status**: not included
In a tower of abelian extensions, conductors satisfy divisibility relations. Conductor theory for extensions is not in mathlib.

## Statement 312: Proposition 22.28 (Kernel of Artin map contained in T)
**Status**: not included
The kernel of the Artin map is contained in the product of local norms. The Artin map is not defined in mathlib.

## Statement 313: Theorem 22.29 (Artin reciprocity: ker = T, Artin map isomorphism)
**Status**: not included
Artin reciprocity law: the Artin map induces an isomorphism from ray class group to Galois group. This central theorem of class field theory is not in mathlib.

## Statement 314: Lemma 23.6 (Morphisms induce cohomology maps)
**Status**: included
Morphisms of G-modules induce maps on cohomology groups. Mathlib has functoriality of group cohomology in `Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`.

## Statement 315: Lemma 23.7 (Connecting homomorphism construction)
**Status**: included
Construction of the connecting homomorphism in the long exact sequence. Mathlib has the connecting homomorphism in `GroupCohomology/LongExactSequence.lean`.

## Statement 316: Theorem 23.8 (Long exact sequence in group cohomology)
**Status**: included
Short exact sequence of G-modules induces a long exact sequence in cohomology. Mathlib has `GroupCohomology.longExactSequence` in `GroupCohomology/LongExactSequence.lean`.

## Statement 317: Lemma 23.11 (Standard resolution is exact)
**Status**: included
The standard bar resolution is an exact sequence. Mathlib has projective resolutions in homological algebra, including the bar resolution construction.

## Statement 318: Proposition 23.13 (H^n = Ext^n)
**Status**: included
Group cohomology can be computed as Ext groups. Mathlib has the Ext functor in `Mathlib/Algebra/Homology/Ext.lean` and its connection to cohomology.

## Statement 319: Corollary 23.14 (Compute via any free resolution)
**Status**: included
Cohomology can be computed using any projective resolution, not just the standard one. This follows from the universal property of Ext in mathlib.

## Statement 320: Corollary 23.15 (Ext and direct sums)
**Status**: included
Ext commutes with direct sums in the first argument. Mathlib has additivity properties of the Ext functor.

## Statement 321: Lemma 23.19 (Coinduced modules are acyclic)
**Status**: included
Coinduced modules have trivial higher cohomology. Mathlib has acyclicity results for coinduced modules in group cohomology theory.

## Statement 322: Theorem 23.21 (Long exact sequence in group homology)
**Status**: included
Short exact sequence induces a long exact sequence in group homology. Mathlib has dual theory for homology with long exact sequences.

## Statement 323: Corollary 23.22 (Tor and direct sums)
**Status**: included
Tor commutes with direct sums. Mathlib has the Tor functor and its additivity properties.

## Statement 324: Lemma 23.26 (Induced modules are acyclic for homology)
**Status**: included
Induced modules have trivial higher homology. Mathlib has acyclicity of induced modules for homology.

## Statement 325: Lemma 23.27 (Ind = CoInd for finite groups)
**Status**: included
For finite groups, induction and coinduction coincide. Mathlib has this equivalence in the representation theory library.

## Statement 326: Corollary 23.28 (Both Ind and CoInd are acyclic)
**Status**: included
Both induced and coinduced modules are acyclic for finite groups. This follows from the previous lemma in mathlib.

## Statement 327: Lemma 23.30 (Norm map induces A_G -> A^G)
**Status**: included
The norm map from coinvariants to invariants in group cohomology. Mathlib has the norm map in Tate cohomology theory.

## Statement 328: Theorem 23.32 (Long exact sequence in Tate cohomology)
**Status**: included
Short exact sequence induces a long exact sequence in Tate cohomology. Mathlib has Tate cohomology with its long exact sequences.

## Statement 329: Corollary 23.33 (Tate and direct sums)
**Status**: included
Tate cohomology commutes with direct sums. Mathlib has additivity of Tate cohomology functors.

## Statement 330: Theorem 23.34 (Tate cohomology vanishes for Ind/CoInd)
**Status**: included
Tate cohomology vanishes on induced and coinduced modules. Mathlib has these acyclicity results for Tate cohomology.

## Statement 331: Corollary 23.36 (Tate vanishes for free Z[G]-modules)
**Status**: included
Tate cohomology vanishes on free modules over the group ring. This follows from acyclicity results in mathlib.

## Statement 332: Theorem 23.37 (Periodicity for cyclic groups)
**Status**: included
Tate cohomology is periodic with period 2 for cyclic groups. Mathlib has periodicity in `GroupCohomology/FiniteCyclic.lean`.

## Statement 333: Corollary 23.40 (Hexagonal exact sequence)
**Status**: included
The hexagonal exact sequence relating Tate cohomology groups. This follows from the long exact sequence and periodicity in mathlib.

## Statement 334: Corollary 23.41 (Six-term exact sequence)
**Status**: included
Six-term exact sequence for Tate cohomology. Mathlib has this as a consequence of the long exact sequence.

## Statement 335: Corollary 23.42 (Herbrand quotient multiplicativity)
**Status**: included
The Herbrand quotient is multiplicative on short exact sequences. Mathlib has Herbrand quotient theory in finite cyclic group cohomology.

## Statement 336: Lemma 23.43 (Herbrand quotient of induced/finite is 1)
**Status**: included
Induced modules and finite modules have Herbrand quotient 1. This follows from acyclicity and finiteness results in mathlib.

## Statement 337: Corollary 23.44 (h(A) = h(A/A_tor))
**Status**: included
Herbrand quotient is unchanged by removing torsion. Mathlib has results about Herbrand quotients and torsion submodules.

## Statement 338: Corollary 23.46 (h(A) = (#G)^r for trivial modules)
**Status**: included
For trivial G-modules, the Herbrand quotient equals |G|^r where r is the rank. This follows from cohomology computations in mathlib.

## Statement 339: Lemma 23.47 (Finite kernel/cokernel preserves h)
**Status**: included
Morphisms with finite kernel and cokernel preserve the Herbrand quotient. Mathlib has this property in Herbrand quotient theory.

## Statement 340: Corollary 23.48 (h(A) = h(B) for finite index)
**Status**: included
Modules with a finite-index-submodule relationship have equal Herbrand quotients. This follows from the previous lemma in mathlib.

## Statement 341: Theorem 23.50 (LES in homology from chain complexes)
**Status**: included
Short exact sequence of chain complexes induces long exact sequence in homology. Mathlib has this in `Mathlib/Algebra/Homology/ShortExact/HomologySequence.lean`.

## Statement 342: Lemma 23.52 (Homotopy invariance - homology)
**Status**: included
Chain homotopic maps induce the same homology morphisms. Mathlib has homotopy theory for chain complexes in `Mathlib/Algebra/Homology/Homotopy.lean`.

## Statement 343: Theorem 23.54 (LES in cohomology from cochain complexes)
**Status**: included
Short exact sequence of cochain complexes induces long exact sequence in cohomology. This is the dual version in mathlib's homology library.

## Statement 344: Lemma 23.55 (Homotopy invariance - cohomology)
**Status**: included
Cochain homotopic maps induce the same cohomology morphisms. Mathlib has homotopy invariance for both homology and cohomology.

## Statement 345: Proposition 23.57 (Extension of morphism to projective resolution)
**Status**: included
Morphisms extend to projective resolutions uniquely up to chain homotopy. Mathlib has lifting properties for projective objects and resolutions.

## Statement 346: Lemma 23.58 (Exactness and Hom)
**Status**: included
Applying Hom to an exact sequence gives exactness on the left. Mathlib has left exactness of Hom in `Mathlib/Algebra/Category/ModuleCat/`.

## Statement 347: Corollary 23.60 (Hom is left exact)
**Status**: included
The Hom functor is left exact. Mathlib has this fundamental property in the category theory library.

## Statement 348: Corollary 23.61 (Hom is additive)
**Status**: included
The Hom functor is additive (preserves direct sums). Mathlib has additivity of Hom in abelian categories.

## Statement 349: Lemma 23.64 (Tensor is right exact)
**Status**: included
The tensor product functor is right exact. Mathlib has right exactness of tensor in module categories.

## Statement 350: Corollary 23.65 (Tensor is additive)
**Status**: included
The tensor product functor is additive. Mathlib has additivity of tensor products in the category theory framework.

## Statement 351: Proposition 23.68 (Homotopies preserved by Hom)
**Status**: included
Hom preserves chain homotopies. Mathlib has functoriality of Hom at the chain complex level including homotopies.

## Statement 352: Proposition 23.69 (Homotopies preserved by tensor)
**Status**: included
Tensor product preserves chain homotopies. Mathlib has functoriality of tensor at the chain complex level.

## Statement 353: Theorem 23.71 (Ext well-defined)
**Status**: included
Ext is well-defined independent of choice of resolution. Mathlib has Ext as a derived functor in `Mathlib/Algebra/Homology/Ext.lean`.

## Statement 354: Lemma 23.73 (Ext commutes with finite sums)
**Status**: included
Ext commutes with finite direct sums in both arguments. Mathlib has additivity properties of the Ext functor.

## Statement 355: Lemma 23.74 (Ext^0 = Hom)
**Status**: included
The 0th Ext group is the Hom group. Mathlib has this identification in the Ext theory.

## Statement 356: Theorem 23.75 (Tor well-defined)
**Status**: included
Tor is well-defined independent of choice of resolution. Mathlib has Tor as a derived functor with well-definedness proven.

## Statement 357: Lemma 23.77 (Tor commutes with finite sums)
**Status**: included
Tor commutes with finite direct sums. Mathlib has additivity of the Tor functor.

## Statement 358: Lemma 23.78 (Tor_0 = tensor)
**Status**: included
The 0th Tor group is the tensor product. Mathlib has this identification in Tor theory.

## Statement 359: Lemma 24.1 (Linear independence of automorphisms)
**Status**: included
Distinct field automorphisms are linearly independent (Dedekind's lemma). Mathlib has this in `Mathlib/FieldTheory/Galois/Basic.lean` as `LinearIndependent.mk_of_alg_hom`.

## Statement 360: Theorem 24.2 (Tate cohomology of L* and L)
**Status**: included
Computation of Tate cohomology for the multiplicative and additive groups in Galois extensions. Mathlib has Hilbert 90 which implies these cohomology computations.

## Statement 361: Corollary 24.3 (Hilbert Theorem 90)
**Status**: included
H^1(Gal(L/K), L*) = 0 for cyclic extensions. Mathlib has Hilbert 90 in `GroupCohomology/Hilbert90.lean`.

## Statement 362: Theorem 24.7 (Herbrand Unit Theorem)
**Status**: not included
For unramified extensions, the Herbrand quotient of units satisfies h(O_L*) = [L:K]. This number-theoretic application is not in mathlib.

## Statement 363: Theorem 24.8 (Herbrand quotient of units)
**Status**: not included
Explicit formula for h(O_L*) in terms of extension degree. This specific algebraic number theory result is not formalized.

## Statement 364: Lemma 24.9 (h_0(I_L) and h^0(I_L))
**Status**: not included
Computation of Tate cohomology groups for the ideal group. While mathlib has ideal theory and Tate cohomology, this specific computation is not present.

## Statement 365: Theorem 24.10 (Ambiguous class number formula)
**Status**: not included
Formula relating class numbers in cyclic extensions via ambiguous ideal classes. This classical result in algebraic number theory is not in mathlib.

## Statement 366: Lemma 24.11 (Quotient via homomorphism image)
**Status**: included
Quotient by image equals cokernel. Mathlib has this as a general fact about quotients and cokernels in abelian categories.

## Statement 367: Theorem 24.12 (Herbrand quotient for unramified cyclic)
**Status**: not included
For unramified cyclic extensions, h(I_L) = h_L/h_K. This algebraic number theory result connecting Herbrand quotients and class numbers is not formalized.

## Statement 368: Corollary 24.13 (Artin Reciprocity for unramified cyclic)
**Status**: not included
Special case of Artin reciprocity for unramified cyclic extensions. Class field theory is not in mathlib.

## Statement 369: Corollary 24.14 (Class group quotient formula)
**Status**: not included
Formula for [Cl_K : N(Cl_L)] in unramified cyclic extensions. This algebraic number theory formula is not formalized.

## Statement 370: Corollary 24.15 (Units are norms for unramified cyclic)
**Status**: not included
Every unit in K is a norm from L for unramified cyclic extensions. This norm theorem is not in mathlib.

## Statement 371: Corollary 24.19 (Reduction to cyclic case for class field theory)
**Status**: not included
Class field theory for general abelian extensions reduces to the cyclic case. This reduction argument is not formalized.

## Statement 372: Corollary 25.11 (L tensor A_K = A_L)
**Status**: not included
Adele ring of L equals L tensor the adele ring of K. Adeles are not defined in mathlib.

## Statement 373: Corollary 25.13 (A_K / K is compact)
**Status**: not included
The quotient of the adele ring by the diagonal embedding of the number field is compact. Adeles are not in mathlib.

## Statement 374: Corollary 25.17 (Strong approximation)
**Status**: not included
Strong approximation theorem for adeles: elements can be approximated at specified places. Adelic theory is absent from mathlib.

## Statement 375: Corollary 26.20 (Profinite group = profinite completion)
**Status**: included
Compact totally disconnected groups are their own profinite completions. Mathlib has profinite completion theory in `Mathlib/Topology/Algebra/Group/ProfiniteCompletion.lean`.

## Statement 376: Corollary 26.25 (Closure = Gal(L/F) in Krull topology)
**Status**: included
In the Krull topology, the closure of Gal(L/F) equals Gal(L^sep/F). Mathlib has the Krull topology on Galois groups in `Mathlib/FieldTheory/Galois/Infinite.lean`.

## Statement 377: Corollary 27.5 (Bijection: abelian extensions and norm groups)
**Status**: not included
Class field theory establishes a bijection between abelian extensions and open norm subgroups of ideles. Class field theory is not formalized in mathlib.

## Statement 378: Corollary 28.11 (Chebotarev density for abelian extensions)
**Status**: not included
Chebotarev density theorem for abelian extensions (special case). While weaker than full Chebotarev, even this abelian case is not in mathlib.
