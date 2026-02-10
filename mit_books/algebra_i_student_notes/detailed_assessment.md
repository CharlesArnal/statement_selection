# Detailed Assessment - Algebra I (MIT 18.701) Student Notes

## Theorem 1 (line 300) -- Subgroups of Z
**Verdict: included**

Every subgroup of (Z, +) is of the form nZ. This is formalized in mathlib as `Int.subgroup_cyclic` in `Mathlib/GroupTheory/Archimedean.lean`, which states "Every subgroup of Z is cyclic," i.e., every `AddSubgroup Z` equals `AddSubgroup.closure {a}` for some `a`. I searched `GroupTheory/Archimedean.lean` and confirmed the theorem at line 112.

## Corollary 2 (line 324) -- gcd as generator
**Verdict: included**

The set {ai + bj : i, j in Z} equals gcd(a,b)*Z. This is essentially Bezout's identity, which states gcd(a,b) = ar + bs for some integers r, s. Mathlib contains `Nat.gcd_eq_gcd_ab` and related results in `Data/Int/GCD.lean` and `Data/Nat/GCD/Basic.lean`. The subgroup characterization follows from combining `Int.subgroup_cyclic` with gcd properties. The Bezout identity itself is formalized.

## Theorem 3 (line 370) -- Structure of Cyclic Subgroups
**Verdict: included**

This theorem characterizes cyclic subgroups as either infinite (all powers distinct) or finite with d elements. In mathlib, this is captured by the theory of `orderOf` and `zpowers` in `GroupTheory/OrderOfElement.lean`. The key results include `orderOf_eq_card_powers` (line 862) and the general framework relating `orderOf` to the structure of cyclic subgroups. The dichotomy between finite and infinite order is built into the definition of `orderOf`.

## Proposition 4 (line 451) -- Homomorphism preserves identity and inverses
**Verdict: included**

If f(ab) = f(a)f(b), then f(e_G) = e_{G'} and f(a)^{-1} = f(a^{-1}). This is formalized in `Algebra/Group/Hom/Defs.lean` as `map_one` (line 234) and `map_inv` (line 440). These are fundamental lemmas in the `MonoidHomClass` and `OneHomClass` type classes.

## Theorem 5 (line 504) -- Image is a subgroup
**Verdict: included**

The image of a group homomorphism f is a subgroup of G'. In mathlib, `MonoidHom.range` is defined as a `Subgroup` in `Algebra/Group/Subgroup/Ker.lean` (line 65: `def range (f : G →* N) : Subgroup N`). The range/image being a subgroup is built into the definition.

## Theorem 6 (line 523) -- Kernel is a subgroup
**Verdict: included**

The kernel of a homomorphism is a subgroup. In mathlib, `MonoidHom.ker` is defined as a `Subgroup` in `Algebra/Group/Subgroup/Ker.lean` (line 218: `def ker (f : G →* M) : Subgroup G`). This is a foundational definition in the group theory library.

## Proposition 7 (line 707) -- Cosets have same order
**Verdict: included**

All cosets of H have the same cardinality as H. This follows from the fact that left multiplication by g is a bijection from H to gH. In mathlib, this is implicit in the coset theory in `GroupTheory/Coset/` and used in the proof of Lagrange's theorem. The equivalence between a subgroup and any of its cosets is captured by the quotient group framework.

## Proposition 8 (line 714) -- Cosets partition the group
**Verdict: included**

Cosets of H form a partition of G. In mathlib, this is formalized via the `Setoid` and `Quotient` framework. The left coset relation `leftRel` in `GroupTheory/Coset/Defs.lean` defines an equivalence relation whose classes are the cosets, and equivalence classes always partition the set.

## Lemma 9 (line 720) -- Coset characterization
**Verdict: included**

Given a coset C of H with b in C, then C = bH. This is part of the basic coset theory in `GroupTheory/Coset/Defs.lean`. The characterization that each coset is of the form bH for any element b in it follows from the equivalence relation properties of the left coset relation.

## Theorem 10 (line 757) -- |G| = [G:H]|H|
**Verdict: included**

This counting formula is formalized in `GroupTheory/Coset/Card.lean` as `card_eq_card_quotient_mul_card_subgroup` (line 53): `Nat.card alpha = Nat.card (alpha / s) * Nat.card s`. This is the fundamental counting result for cosets.

## Corollary 11 (line 779) -- Lagrange's Theorem
**Verdict: included**

|H| divides |G| for subgroup H of finite group G. Formalized as `Subgroup.card_subgroup_dvd_card` in `GroupTheory/Coset/Card.lean` (line 69), which is explicitly labeled as "Lagrange's Theorem" in the docstring.

## Corollary 12 (line 784) -- Prime order implies cyclic
**Verdict: included**

If |G| is prime p, then G is cyclic. Formalized as `isCyclic_of_prime_card` in `GroupTheory/SpecificGroups/Cyclic.lean` (line 190). The proof uses Lagrange's theorem to show that any non-identity element must generate the whole group.

## Corollary 13 (line 814) -- Counting Formula (restated)
**Verdict: included**

This is a restatement of Theorem 10 (|G| = |H|[G:H]) and is covered by the same `card_eq_card_quotient_mul_card_subgroup` in `GroupTheory/Coset/Card.lean`.

## Theorem 14 (line 825) -- Lagrange's Theorem (restated)
**Verdict: included**

This is a restatement of Corollary 11 and is covered by `Subgroup.card_subgroup_dvd_card` in `GroupTheory/Coset/Card.lean`.

## Corollary 15 (line 830) -- Order of element divides group order
**Verdict: included**

The order of an element x divides |G|. Formalized as `orderOf_dvd_card` in `GroupTheory/OrderOfElement.lean` (line 995) and `orderOf_dvd_natCard` (line 1001).

## Corollary 16 (line 834) -- Prime order implies cyclic (restated)
**Verdict: included**

Restatement of Corollary 12, covered by `isCyclic_of_prime_card` in `GroupTheory/SpecificGroups/Cyclic.lean`.

## Corollary 17 (line 877) -- |G| = |ker(f)| * |im(f)|
**Verdict: included**

This is the first isomorphism theorem applied to counting. In mathlib, this follows from `card_eq_card_quotient_mul_card_subgroup` applied to the kernel, combined with the first isomorphism theorem (`QuotientGroup.quotientKerEquivRange` in `GroupTheory/QuotientGroup/Basic.lean`). The result that |G| = |ker(f)| * |im(f)| is a direct consequence.

## Theorem 18 (line 1000) -- Correspondence Theorem
**Verdict: included**

The correspondence theorem (lattice theorem) states there is a bijection between subgroups of G containing ker(f) and subgroups of G'. In mathlib, this is formalized as `QuotientGroup.comapMk'OrderIso` in `GroupTheory/QuotientGroup/Basic.lean` (line 359), explicitly called "The correspondence theorem, or lattice theorem."

## Theorem 19 (line 1041) -- Correspondence Theorem (restated)
**Verdict: included**

Same as Theorem 18, covered by `QuotientGroup.comapMk'OrderIso`.

## Theorem 20 (line 1124) -- Product of cosets of normal subgroup is a coset
**Verdict: included**

If C_1, C_2 are cosets of a normal subgroup N, then C_1 * C_2 is also a coset of N. This is the key property that makes the quotient group well-defined. In mathlib, this is formalized as part of the quotient group construction in `GroupTheory/QuotientGroup/Defs.lean`, where the group operation on G/N is defined via `QuotientGroup.instGroup`.

## Theorem 21 (line 1162) -- Quotient group structure
**Verdict: included**

The quotient G/N is a group and there exists a surjective homomorphism pi: G -> G/N with ker(pi) = N. In mathlib, the group structure on G/N is `QuotientGroup.Quotient.group` in `GroupTheory/QuotientGroup/Defs.lean`. The surjectivity of mk' is `QuotientGroup.mk'_surjective` (line 100), and `ker_mk'` (line 141) shows ker(pi) = N.

## Lemma 22 (line 1411) -- Span Lemma
**Verdict: included**

If S spans V and L is linearly independent, then (1) removing elements of S gives a basis, (2) adding elements of S to L gives a basis, and (3) |S| >= |L|. These are fundamental results in linear algebra formalized across `LinearAlgebra/LinearIndependent/Basic.lean` and `LinearAlgebra/Basis/Basic.lean`. The exchange lemma and basis extension theorems are present in mathlib.

## Corollary 23 (line 1421) -- Bases have same cardinality
**Verdict: included**

Any two bases of V have the same number of vectors. This is the well-definedness of dimension, which is a fundamental result in mathlib's linear algebra library. The `finrank` function in `LinearAlgebra/Dimension/` is well-defined precisely because of this invariance, formalized via the theory of `Module.rank` and `InvariantBasisNumber`.

## Theorem 24 (line 1588) -- Dimension Formula (Rank-Nullity)
**Verdict: included**

dim(Ker T) + dim(im T) = dim(V). This is the rank-nullity theorem, formalized in `LinearAlgebra/Dimension/RankNullity.lean` (line 83, labeled "The rank-nullity theorem"). Also present in various equivalent forms throughout the dimension theory files.

## Corollary 25 (line 1628) -- Matrix in standard form
**Verdict: included**

Any linear transformation can be represented in standard form (identity block with zeros) for some choice of bases. This follows from the rank-nullity theorem and basis theory. In mathlib, the canonical form for linear maps is captured through the equivalence between linear maps and matrices, and the theory of `LinearMap.toMatrix` combined with basis changes.

## Corollary 26 (line 1631) -- Change of basis to standard form
**Verdict: included**

For a matrix M, there exist invertible change-of-basis matrices P, Q such that Q^{-1}MP is in standard form. This is the matrix version of Corollary 25 and follows from the same framework. The matrix equivalence under change of basis is part of `LinearAlgebra/Matrix/` theory.

## Corollary 27 (line 1668) -- rank(M) = rank(M^T)
**Verdict: included**

Row rank equals column rank. Formalized as `Matrix.rank_transpose` in `LinearAlgebra/Matrix/Rank.lean` (line 423): `Aᵀ.rank = A.rank`.

## Proposition 28 (line 1714) -- Injective iff surjective for endomorphisms
**Verdict: included**

For a linear operator T: V -> V with V finite-dimensional, T injective iff T surjective iff T is an isomorphism. Formalized as `LinearMap.injective_iff_surjective` in `LinearAlgebra/FiniteDimensional/Basic.lean` (line 285).

## Proposition 29 (line 1844) -- Eigenvalue iff root of characteristic polynomial
**Verdict: included**

Lambda is an eigenvalue of A iff p_A(lambda) = 0. Formalized as `Matrix.mem_spectrum_iff_isRoot_charpoly` in `LinearAlgebra/Matrix/Charpoly/Eigs.lean` (referenced in docstring line 17).

## Proposition 30 (line 1934) -- Eigenvectors for distinct eigenvalues are linearly independent
**Verdict: included**

Eigenvectors corresponding to distinct eigenvalues are linearly independent. Formalized as `Module.End.eigenvectors_linearIndependent` in `LinearAlgebra/Eigenspace/Basic.lean` (line 696) and the indexed variant `eigenvectors_linearIndependent'` (line 684).

## Corollary 31 (line 1957) -- Distinct eigenvalues implies diagonalizable
**Verdict: included**

If the characteristic polynomial has n distinct roots, A is diagonalizable. This follows from Proposition 30 (eigenvectors for distinct eigenvalues are linearly independent, hence form a basis). The diagonalizability theory is in `LinearAlgebra/Eigenspace/` and the connection to distinct eigenvalues is captured by the linear independence result.

## Theorem 32 (line 2023) -- Jordan Decomposition Theorem
**Verdict: non-included**

The Jordan normal form theorem states that any linear operator on a finite-dimensional vector space (over an algebraically closed field) has a Jordan normal form. I searched `LinearAlgebra/` for Jordan-related files and found only `LinearAlgebra/JordanChevalley.lean`, which covers the Jordan-Chevalley decomposition (semisimple + nilpotent), not the Jordan normal form. There is no formalization of Jordan blocks or the Jordan canonical form in mathlib.

## Theorem 33 (line 2091) -- Jordan Normal Form (restated)
**Verdict: non-included**

Same as Theorem 32. The Jordan normal form is not formalized in mathlib.

## Theorem 34 (line 2250) -- Direct Sum Criterion
**Verdict: included**

If dim W + dim W' = dim V and W intersect W' = {0}, then V = W direct-sum W'. Formalized as `eq_top_of_disjoint` in `LinearAlgebra/FiniteDimensional/Lemmas.lean` (line 72), which shows that if the finranks add up to the total and the submodules are disjoint, then their sup is the whole space.

## Theorem 35 (line 2380) -- Characterizations of Orthogonal Matrices
**Verdict: included**

The equivalence of: A is orthogonal, A preserves lengths, A^T A = I, columns of A form an orthonormal basis. The orthogonal group and its properties are formalized in `LinearAlgebra/UnitaryGroup.lean` (which covers the unitary group, with the orthogonal group as a special case). The characterization A^T A = I is the definition, and the equivalence with norm preservation is in `Analysis/InnerProductSpace/LinearMap.lean` and `Analysis/Normed/Operator/LinearIsometry.lean`.

## Proposition 36 (line 2415) -- Orthogonal matrices form a subgroup
**Verdict: included**

O_n is a subgroup of GL_n. In mathlib, the orthogonal/unitary group is defined as a group in `LinearAlgebra/UnitaryGroup.lean`. The group structure (closure under multiplication and inversion) is built into the definition of `Matrix.unitaryGroup`.

## Theorem 37 (line 2469) -- 2x2 orthogonal reflections
**Verdict: non-included**

The specific characterization that 2x2 orthogonal matrices with determinant -1 are reflections across lines at angle theta/2 is not formalized in mathlib. While mathlib has general reflection theory (`LinearAlgebra/Reflection.lean`), the specific 2D classification of orthogonal matrices into rotations and reflections with explicit angle parametrization is not present.

## Theorem 38 (line 2504) -- Rotation operators are SO_3
**Verdict: non-included**

The statement that rotation operators on R^3 are exactly SO_3 is not formalized in mathlib. There is no `SO_3` or `SpecialOrthogonal` specific type in mathlib, and the geometric characterization of rotations is not present. The unitary/orthogonal group theory in mathlib is algebraic rather than geometric.

## Theorem 39 (line 2602) -- Isometry decomposition
**Verdict: non-included**

Every isometry f of R^n is of the form f(x) = Ax + b for A in O_n. While mathlib has the Mazur-Ulam theorem in `Analysis/Normed/Affine/MazurUlam.lean` (showing isometric bijections of normed spaces over R are affine), the specific decomposition into orthogonal part plus translation for Euclidean spaces is not explicitly stated in this form. The affine isometry theory in `Analysis/Normed/Affine/Isometry.lean` exists but the exact equivalence as stated here is not directly present.

## Lemma 40 (line 2608) -- Isometry fixing origin is linear
**Verdict: non-included**

If f: R^n -> R^n is an isometry with f(0) = 0, then f is linear. This is essentially the Mazur-Ulam result specialized to R^n, but the specific statement for finite-dimensional Euclidean space with f(0) = 0 implying linearity is not directly formalized as a standalone lemma in mathlib in this form. The Mazur-Ulam theorem gives affinity for bijective isometries, not linearity directly.

## Theorem 41 (line 2696) -- Classification of isometries of R^2
**Verdict: non-included**

Every isometry of R^2 is a translation, rotation, reflection, or glide reflection. This geometric classification result is not formalized in mathlib. While mathlib has components (affine isometries, reflections), the complete classification of plane isometries into these four types is not present.

## Theorem 42 (line 2861) -- Discrete subgroups of R
**Verdict: non-included**

If G <= (R, +) is discrete, then G = {0} or G = Z*alpha. While the Archimedean property and related results are in `GroupTheory/Archimedean.lean`, the specific classification of discrete subgroups of (R, +) is not formalized in mathlib. The file deals with subgroups of Z, not of R.

## Theorem 43 (line 2899) -- Finite subgroups of SO_2
**Verdict: non-included**

Finite subgroups of SO_2 are cyclic groups C_n. This is not formalized in mathlib. While mathlib has `GroupTheory/SpecificGroups/Dihedral.lean` with dihedral group theory, the classification of finite subgroups of SO_2 specifically is not present.

## Theorem 44 (line 2916) -- Finite subgroups of O_2
**Verdict: non-included**

Any finite subgroup of O_2 is isomorphic to C_n or D_n. This classification result is not formalized in mathlib. While dihedral groups are defined in `GroupTheory/SpecificGroups/Dihedral.lean`, the theorem classifying finite subgroups of the orthogonal group O_2 is not present.

## Theorem 45 (line 2976) -- Finite subgroups of O_2 (restated)
**Verdict: non-included**

Same as Theorem 44. Not in mathlib.

## Theorem 46 (line 2996) -- Finite subgroups of M_2
**Verdict: non-included**

Any finite subgroup of the isometry group M_2 of R^2 is isomorphic to C_n or D_n. This is not formalized in mathlib. The classification of finite groups of isometries of the plane is a geometric group theory result not present in mathlib.

## Theorem 47 (line 3067) -- Discrete subgroups of R^2
**Verdict: non-included**

Discrete subgroups of R^2 are either {0}, Z*alpha (a line), or Za + Zb (a lattice). While mathlib has extensive lattice theory in `Algebra/Module/ZLattice/`, the classification of discrete subgroups of R^2 into these three types is not explicitly formalized.

## Proposition 48 (line 3119) -- Point group maps lattice to itself
**Verdict: non-included**

This is a specific result about wallpaper groups: the point group preserves the translation lattice. This is part of the theory of crystallographic groups, which is not formalized in mathlib.

## Theorem 49 (line 3249) -- Point group acts on lattice
**Verdict: non-included**

Same context as Proposition 48. The action of the point group on the translation lattice is not formalized in mathlib.

## Theorem 50 (line 3315) -- Crystallographic Restriction
**Verdict: non-included**

The crystallographic restriction theorem states that the point group can only have rotational symmetry of order 1, 2, 3, 4, or 6. I searched for "crystallographic" and "wallpaper" in mathlib and found no results. This theorem is not formalized.

## Proposition 51 (line 3572) -- Orbits partition S
**Verdict: included**

The orbits of a group action partition the set S. In mathlib, this is captured by `MulAction.orbitRel` in `GroupTheory/GroupAction/Defs.lean`, which defines the orbit equivalence relation. The orbit equivalence relation classes (orbits) partition S by the properties of equivalence relations. The disjointness is at `orbit_eq_iff` (line 234).

## Corollary 52 (line 3581) -- |S| = sum of orbit sizes
**Verdict: included**

If S is finite with orbits O_1, ..., O_k, then |S| = sum |O_i|. This follows directly from Proposition 51 (orbits partition S) and is implicit in the orbit counting framework in `GroupTheory/GroupAction/Defs.lean` and `GroupTheory/ClassEquation.lean`.

## Proposition 53 (line 3597) -- Orbit-Stabilizer bijection
**Verdict: included**

There is a bijection between G/Stab(s) and the orbit O_s. In mathlib, this is part of the orbit-stabilizer theorem framework in `GroupTheory/GroupAction/Quotient.lean`. The orbit-stabilizer bijection is used in proving `card_orbit_mul_card_stabilizer_eq_card_group` (line 180).

## Corollary 54 (line 3614) -- Counting Formula for Orbits
**Verdict: included**

|O_s| = [G : Stab(s)]. This is the orbit-stabilizer theorem, formalized as `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` in `GroupTheory/GroupAction/Quotient.lean` (line 180), which states |orbit| * |stabilizer| = |G|, equivalent to |orbit| = [G : Stab(s)].

## Theorem 55 (line 3726) -- Finite subgroups of SO_3
**Verdict: non-included**

Finite subgroups of SO_3 are either C_n, D_n, or the symmetry group of a regular polyhedron (tetrahedral, octahedral, icosahedral). This classification theorem is not formalized in mathlib. There is no SO_3-specific theory in mathlib, and the classification of finite rotation groups in 3D is not present.

## Lemma 56 (line 3759) -- G acts on poles
**Verdict: non-included**

If p is a pole and g is in G (a finite rotation group), then gp is also a pole. This is a specific lemma about the action of rotation groups on poles of S^2, used in classifying finite subgroups of SO_3. This geometric group theory result is not in mathlib.

## Theorem 57 (line 4031) -- p-group has non-trivial center
**Verdict: included**

Every p-group has non-trivial center. Formalized as `IsPGroup.center_nontrivial` in `GroupTheory/PGroup.lean` (line 216). Also `IsPGroup.bot_lt_center` (line 226).

## Corollary 58 (line 4088) -- Group of order p^2 is abelian
**Verdict: included**

If |G| = p^2, then G is abelian. Formalized as `IsPGroup.commutative_of_card_eq_prime_sq` in `GroupTheory/PGroup.lean` (line 375), and the CommGroup instance `IsPGroup.commGroupOfCardEqPrimeSq` (line 369).

## Corollary 59 (line 4106) -- Group of order p^2 is C_{p^2} or C_p x C_p
**Verdict: included**

A group of order p^2 is isomorphic to either C_{p^2} or C_p x C_p. This follows from Corollary 58 (the group is abelian) combined with the classification of finite abelian groups. In mathlib, the abelian group structure theorem is in `GroupTheory/FiniteAbelian/Basic.lean`, and the fact that an abelian group of order p^2 has exactly these two forms follows from the prime power decomposition. The specific classification for p^2 can be derived from the cyclic center quotient result at line 358.

## Theorem 60 (line 4234) -- Icosahedral group is simple
**Verdict: non-included**

The icosahedral rotation group I is simple. I searched for "icosahedral" in mathlib and found no results. While A_5 simplicity is proven (see Statement 62), the icosahedral group as a geometric object and its simplicity are not formalized.

## Theorem 61 (line 4257) -- Icosahedral group isomorphic to A_5
**Verdict: non-included**

The icosahedral group I is isomorphic to A_5. The icosahedral group is not defined in mathlib, so this isomorphism cannot be stated. While the alternating group A_5 is well-defined in mathlib, the geometric icosahedral group is not.

## Corollary 62 (line 4293) -- A_5 is simple
**Verdict: included**

The alternating group A_5 is simple. Formalized as `alternatingGroup.isSimpleGroup_five` in `GroupTheory/SpecificGroups/Alternating.lean` (line 347). The proof is by casework on elements of A_5.

## Proposition 63 (line 4375) -- Conjugate permutations have same cycle type
**Verdict: included**

Two permutations are conjugate iff they have the same cycle type. Formalized as `Equiv.Perm.isConj_iff_cycleType_eq` in `GroupTheory/Perm/Cycle/Type.lean` (line 297).

## Theorem 64 (line 4548) -- Lagrange's Theorem (restated again)
**Verdict: included**

|H| divides |G| for subgroup H of finite group G. Same as Corollary 11, covered by `Subgroup.card_subgroup_dvd_card`.

## Theorem 65 (line 4575) -- Sylow I
**Verdict: included**

Given |G| = p^e * m with gcd(p,m) = 1, there exists a subgroup H with |H| = p^e. Formalized via `Sylow.exists_subgroup_card_pow_prime` and `IsPGroup.exists_le_sylow` in `GroupTheory/Sylow.lean` (lines 30, 155). The existence of Sylow p-subgroups is a core result.

## Corollary 66 (line 4603) -- Cauchy's Theorem
**Verdict: included**

If p divides |G|, there exists an element of order p. Formalized as `exists_prime_orderOf_dvd_card'` in `GroupTheory/Perm/Cycle/Type.lean` (line 541). This is used in the Sylow theory proofs.

## Theorem 67 (line 4618) -- Sylow II
**Verdict: included**

(a) All Sylow p-subgroups are conjugate. (b) Any p-subgroup is contained in some Sylow p-subgroup (up to conjugation). Part (a) is formalized as `Sylow.isPretransitive_of_finite` in `GroupTheory/Sylow.lean` (line 37 in docstring), which states the conjugation action on Sylow subgroups is transitive. Part (b) follows from `IsPGroup.exists_le_sylow`.

## Theorem 68 (line 4648) -- Sylow III
**Verdict: included**

The number of Sylow p-subgroups divides m and is congruent to 1 mod p. Formalized as `card_sylow_modEq_one` in `GroupTheory/Sylow.lean` (line 312). The divisibility condition is also present in the Sylow theory.

## Proposition 69 (line 4692) -- Group of order 15 structure
**Verdict: non-included**

For a group of order 15 with subgroups H of order 5 and K of order 3: (a) H and K commute, and (b) G is isomorphic to H x K. While this can be derived from Sylow theory (both subgroups are normal, hence the group is a direct product), the specific statement for order 15 is not formalized as a standalone result in mathlib.

## Proposition 70 (line 4772) -- Groups of order 10
**Verdict: non-included**

Groups of order 10 are isomorphic to C_5 x C_2 or C_{10}. This specific classification for order 10 is not formalized in mathlib. While it can be derived from general theory, no explicit statement exists.

## Theorem 71 (line 4833) -- Sylow Theorems (combined)
**Verdict: included**

This is a combined restatement of Sylow I, II, and III. All parts are covered by the Sylow theory in `GroupTheory/Sylow.lean`.

## Theorem 72 (line 4852) -- Structure theorem for finite abelian groups
**Verdict: included**

Every finite abelian group is isomorphic to a product of groups of prime power order. Formalized as `AddCommGroup.equiv_directSum_zmod_of_finite` in `GroupTheory/FiniteAbelian/Basic.lean` (line 135), and the multiplicative version at line 177.

## Lemma 73 (line 4862) -- Homomorphism f is an isomorphism
**Verdict: non-included**

This is a context-specific lemma within a proof (the homomorphism constructed in the proof of the structure theorem is an isomorphism). It is not a standalone mathematical statement and is too proof-specific to be independently in mathlib.

## Theorem 74 (line 4878) -- Sylow I (restated)
**Verdict: included**

Same as Theorem 65, covered by `GroupTheory/Sylow.lean`.

## Lemma 75 (line 4887) -- Combinatorial lemma for Sylow I
**Verdict: non-included**

The binomial coefficient C(n, p^e) is not divisible by p, and C(n, p^e) is congruent to m mod p. While this combinatorial fact is used in the proof of Sylow I in mathlib, I could not find it stated as a separate standalone lemma. The proof in mathlib takes a different approach via group actions on subsets.

## Lemma 76 (line 4896) -- Stabilizer divides subset size
**Verdict: non-included**

If H stabilizes a subset U of G, then |H| divides |U|. This is a technical lemma used in the proof of Sylow I. While the orbit-stabilizer theorem is in mathlib, this specific statement about stabilizers of subsets is not a standalone lemma.

## Theorem 77 (line 4914) -- Sylow II (restated)
**Verdict: included**

Same as Theorem 67, covered by `GroupTheory/Sylow.lean`.

## Theorem 78 (line 4950) -- Sylow III (restated)
**Verdict: included**

Same as Theorem 68, covered by `card_sylow_modEq_one` in `GroupTheory/Sylow.lean`.

## Fact 79 (line 4971) -- Sylow subgroup fixed point
**Verdict: non-included**

Under the conjugation action of a Sylow subgroup H on the set of all Sylow subgroups, H is the unique fixed point. While this fact is used in the proof of Sylow III in mathlib, it is not stated as a separate named fact.

## Proposition 80 (line 5055) -- Symmetric matrix gives symmetric bilinear form
**Verdict: included**

A symmetric matrix gives a symmetric bilinear form. This is part of the bilinear form theory in `LinearAlgebra/Matrix/BilinearForm.lean` and `LinearAlgebra/Matrix/SesquilinearForm.lean`. The correspondence between symmetric matrices and symmetric bilinear forms is formalized through the `toBilin` and `toMatrix` equivalences.

## Proposition 81 (line 5064) -- Every bilinear form on R^n comes from a matrix
**Verdict: included**

Every bilinear form on R^n arises from a matrix A via <x,y> = x^T A y, and the form is symmetric iff A is symmetric. Formalized in `LinearAlgebra/Matrix/BilinearForm.lean` through the equivalence `Matrix.toBilin'` and `BilinForm.toMatrix'`, which establish a bijection between matrices and bilinear forms. The symmetry correspondence is also captured.

## Claim 82 (line 5366) -- Hermitian matrix has real eigenvalues
**Verdict: included**

A Hermitian matrix always has real eigenvalues. Formalized in `Analysis/InnerProductSpace/Spectrum.lean` as `LinearMap.IsSymmetric.conj_eigenvalue_eq_self` (line 85), which states the eigenvalues of a self-adjoint operator are real. Also present in `Analysis/Matrix/Spectrum.lean` for the matrix version.

## Proposition 83 (line 5479) -- Non-degenerate iff det != 0
**Verdict: included**

A bilinear form is non-degenerate iff its matrix is invertible (det A != 0). Formalized in `LinearAlgebra/Matrix/BilinearForm.lean` and `LinearAlgebra/Matrix/Nondegenerate.lean`. The connection between non-degeneracy of the form and invertibility of the matrix is established through the `Nondegenerate` predicate.

## Theorem 84 (line 5507) -- Non-degenerate restriction implies direct sum
**Verdict: included**

If the restriction of the bilinear form to W is non-degenerate, then V = W direct-sum W^perp. Formalized as `BilinForm.isCompl_orthogonal_of_restrict_nondegenerate` in `LinearAlgebra/BilinearForm/Orthogonal.lean` (line 304).

## Theorem 85 (line 5536) -- Non-degenerate restriction implies direct sum (restated)
**Verdict: included**

Same as Theorem 84, covered by `BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`.

## Theorem 86 (line 5583) -- Existence of orthogonal basis for symmetric/Hermitian form
**Verdict: included**

For a symmetric or Hermitian form, V has an orthogonal basis. The existence of orthogonal bases is formalized through `BilinForm.orthogonalBasis` in `LinearAlgebra/BilinearForm/Basic.lean` and the Gram-Schmidt process in `Analysis/InnerProductSpace/GramSchmidtOrtho.lean`. The orthogonal basis theory for quadratic/bilinear forms is in `LinearAlgebra/QuadraticForm/Basic.lean`.

## Corollary 87 (line 5610) -- Orthogonal basis with entries 1, -1, or 0
**Verdict: included**

V has an orthogonal basis where <v_i, v_i> = 1, -1, or 0. This is the canonical form for symmetric bilinear forms over R, related to the signature. In mathlib, the diagonal form is achieved through the orthogonal basis theory, and the normalization to +/-1 or 0 follows from scaling. The quadratic form theory in `LinearAlgebra/QuadraticForm/Real.lean` handles the real case.

## Claim 88 (line 5625) -- Sylvester's Law of Inertia
**Verdict: non-included**

The signature (numbers of 1s, -1s, and 0s in the diagonal form) is an invariant of the form. I searched for "Sylvester" and "inertia" and "signature" in mathlib and did not find a formalization of Sylvester's law of inertia. While the quadratic form theory exists, the specific invariance of signature under basis change is not formalized.

## Theorem 89 (line 5713) -- Existence of orthonormal basis
**Verdict: included**

If V is Euclidean or Hermitian, there exists an orthonormal basis. Formalized through `OrthonormalBasis` in `Analysis/InnerProductSpace/PiL2.lean` and the Gram-Schmidt orthonormalization in `Analysis/InnerProductSpace/GramSchmidtOrtho.lean`. The function `stdOrthonormalBasis` and `OrthonormalBasis.fromOrthogonalSpanSingleton` provide constructions.

## Claim 90 (line 5721) -- Restriction always nondegenerate in Euclidean/Hermitian
**Verdict: included**

For a Euclidean or Hermitian space (positive definite inner product), the restriction to any subspace is always nondegenerate. This follows from the positive definiteness of the inner product, which is built into the `InnerProductSpace` definition in mathlib (`Analysis/InnerProductSpace/Basic.lean`). The inner product restricted to any subspace remains positive definite, hence nondegenerate.

## Claim 91 (line 5802) -- Adjoint characterization
**Verdict: included**

<Tv, w> = <v, T*w> characterizes the adjoint T*. Formalized as `ContinuousLinearMap.adjoint_inner_left` and `adjoint_inner_right` in `Analysis/InnerProductSpace/Adjoint.lean` (lines 117, 121). The adjoint is defined precisely by this inner product relation.

## Theorem 92 (line 5844) -- Spectral Theorem
**Verdict: included**

For a normal operator T on a Hermitian space, there exists an orthonormal basis of eigenvectors. Formalized in `Analysis/InnerProductSpace/Spectrum.lean` through `LinearMap.IsSymmetric.eigenvectorBasis` (referenced in the docstring at line 31) and `LinearMap.IsSymmetric.diagonalization`. The matrix version is in `Analysis/Matrix/Spectrum.lean` via `IsHermitian.eigenvectorBasis` (line 66).

## Theorem 93 (line 5873) -- Spectral Theorem (extended)
**Verdict: included**

The extended spectral theorem including the matrix form (P^{-1}MP is diagonal for unitary/orthogonal P) and the real version for symmetric operators. Both versions are covered by the same formalization in `Analysis/InnerProductSpace/Spectrum.lean` and `Analysis/Matrix/Spectrum.lean`. The real eigenvalue property for symmetric matrices is `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`.

## Lemma 94 (line 5892) -- T-invariant subspace complement
**Verdict: included**

If T(W) is contained in W, then T*(W^perp) is contained in W^perp. This is a standard result in inner product space theory. In mathlib, this is related to the theory in `Analysis/InnerProductSpace/Spectrum.lean` and `Analysis/InnerProductSpace/Adjoint.lean`. The invariance of orthogonal complements under adjoints is used in the proof of the spectral theorem.

## Lemma 95 (line 5903) -- Eigenvalues of T and T*
**Verdict: included**

If Tv = lambda*v, then T*v = conj(lambda)*v for normal T. This is formalized as part of the spectral theory in `Analysis/InnerProductSpace/Spectrum.lean`. The relationship between eigenvalues of T and T* is used in the proof of the spectral theorem for normal operators.

## Theorem 96 (line 6011) -- Classification of conics
**Verdict: non-included**

After an isometry, all conics ax^2 + bxy + cy^2 + dx + ey + f = 0 reduce to standard forms. This is a classical result in analytic geometry that is not formalized in mathlib. While mathlib has quadratic form theory, the specific geometric classification of conics under isometries is not present.

## Theorem 97 (line 6228) -- Conjugacy classes of SU_2
**Verdict: non-included**

The conjugacy classes of SU_2 are precisely the latitudes (level sets of the trace function). This specific result about the structure of SU_2 is not formalized in mathlib. While mathlib defines the unitary group (`LinearAlgebra/UnitaryGroup.lean`), the specific topology and conjugacy class structure of SU_2 is not present.

## Theorem 98 (line 6319) -- Longitudes as subgroups of SU_2
**Verdict: non-included**

For each element x on the equator of SU_2, the longitude Long_x is a subgroup isomorphic to R/2piZ. This is a specific structural result about SU_2 that is not formalized in mathlib.

## Proposition 99 (line 6564) -- One-parameter subgroups
**Verdict: non-included**

Every one-parameter group in GL_n(C) is of the form phi(t) = e^{tA}. While mathlib has matrix exponential theory in `Analysis/Normed/Algebra/MatrixExponential.lean`, the classification of one-parameter subgroups of GL_n as matrix exponentials is not explicitly formalized as a theorem.

## Lemma 100 (line 6704) -- det(e^A) = e^{trace(A)}
**Verdict: non-included**

For any matrix A, det(e^A) = e^{trace(A)}. The file `Analysis/Normed/Algebra/MatrixExponential.lean` mentions this as a TODO (line 57: "Show that det(exp A) = exp(trace A)") but it is not yet proven in mathlib. The proof outline is present but the formal statement is not completed.

## Proposition 101 (line 6856) -- Lie algebra properties
**Verdict: non-included**

The three definitions of the Lie algebra of a matrix group are equivalent, and Lie(G) is a vector subspace. While mathlib has extensive Lie algebra theory in `Algebra/Lie/`, the specific correspondence between Lie groups and their Lie algebras (as tangent spaces at the identity) is not formalized for matrix groups. The Lie algebra in mathlib is defined algebraically, not via matrix groups.

## Theorem 102 (line 6913) -- Lie bracket closure
**Verdict: included**

For G <= GL_n, the Lie algebra Lie(G) is closed under the Lie bracket. In mathlib, Lie algebras are defined with the bracket as part of the structure (`LieRing` in `Algebra/Lie/Basic.lean`, line 61). The closure under the bracket is built into the definition of a Lie algebra and Lie subalgebra.

## Theorem 103 (line 6973) -- Lie's Third Theorem
**Verdict: non-included**

Given a finite-dimensional Lie algebra V over R, there exists a unique Lie group G with Lie(G) = V. This deep theorem connecting Lie algebras to Lie groups is not formalized in mathlib. While mathlib has Lie algebra theory, the correspondence with Lie groups (Lie's third theorem) requires differential geometry machinery that is not yet available.

## Theorem 104 (line 7021) -- Normal subgroups of SU_2
**Verdict: non-included**

The only normal subgroups of SU_2 are {I}, {+/-I}, and SU_2 itself. This specific result about SU_2 is not formalized in mathlib. While mathlib has the `IsSimpleGroup` predicate and simple group theory, SU_2 itself is not studied in sufficient detail.

## Corollary 105 (line 7027) -- SO_3 is simple
**Verdict: non-included**

SU_2/{+/-I} (which is isomorphic to SO_3) is simple. This is not formalized in mathlib. SO_3 is not defined as a specific group in mathlib, and its simplicity is not proven.

## Theorem 106 (line 7302) -- PSL_2(F) is simple
**Verdict: non-included**

For any field F with |F| >= 4, SL_2(F)/{+/-I} is simple. While `LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean` defines the PSL, the simplicity theorem for PSL_2 is not formalized in mathlib. I searched for "simple" combined with "SL" and "PSL" and found no results.

## Lemma 107 (line 7319) -- x^2 = a has at most 2 solutions
**Verdict: included**

In a field F, x^2 = a has at most 2 solutions. This is a basic consequence of the fact that a polynomial of degree n has at most n roots in a field, which is formalized in mathlib (`Polynomial.card_roots_le_degree` and related results in `Algebra/Polynomial/`). The specific case of degree 2 follows immediately.

## Lemma 108 (line 7329) -- Existence of r with r^2 not 0, 1, -1
**Verdict: non-included**

If |F| > 5, there exists r in F with r^2 not equal to 0, 1, or -1. This is a specific counting argument for finite fields that is not formalized as a standalone lemma in mathlib.

## Claim 109 (line 7339) -- Finding B with distinct eigenvalues in N
**Verdict: non-included**

This is a proof-specific intermediate claim in the proof of simplicity of PSL_2(F). It is not a standalone mathematical statement in mathlib.

## Claim 110 (line 7355) -- Matrices with given eigenvalues in N
**Verdict: non-included**

All matrices in SL_2 with eigenvalues s and s^{-1} are in the normal subgroup N. This is a proof-specific claim, not a standalone result in mathlib.

## Theorem 111 (line 7415) -- Bolyai-Gerwien Theorem
**Verdict: non-included**

If polygons P and Q have the same area, then they are scissors-congruent. I searched for "Bolyai," "Gerwien," and "scissors" in mathlib and found no results. This classical geometry theorem is not formalized.

## Proposition 112 (line 7481) -- Properties of tensor product of abelian groups
**Verdict: included**

Basic properties of the tensor product: 0 tensor h = 0, (ag) tensor h = a(g tensor h), and generators of the tensor product. These are formalized in `LinearAlgebra/TensorProduct/Basic.lean` through the properties of the tensor product construction. The zero and linearity properties are part of the bilinear map structure used to define tensor products.

## Theorem 113 (line 7559) -- Dehn invariant preserved
**Verdict: non-included**

The Dehn invariant is preserved by scissors-congruence. I searched for "Dehn" in mathlib and found no results. The Dehn invariant and scissors-congruence theory are not formalized.

## Theorem 114 (line 7674) -- Cube and tetrahedron have different Dehn invariants
**Verdict: non-included**

The cube and regular tetrahedron have different Dehn invariants (Hilbert's third problem). Not formalized in mathlib.

## Claim 115 (line 7732) -- arccos(1/3) is irrational multiple of pi
**Verdict: non-included**

The dihedral angle arccos(1/3) of the regular tetrahedron is not a rational multiple of pi. This specific transcendence/irrationality result is not in mathlib.

## Claim 116 (line 7740) -- l tensor alpha is nonzero
**Verdict: non-included**

For alpha not a rational multiple of pi and nonzero l, the element l tensor alpha is nonzero in R tensor_Z (R/Q*pi). This is a technical claim in the Dehn invariant computation and is not formalized in mathlib.
