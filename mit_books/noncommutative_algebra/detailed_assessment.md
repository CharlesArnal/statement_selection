# Detailed Assessment of Statements Against Mathlib v4.27.0

## Statement 1: Lemma 1.17
If $\varphi: R \to S$ is a ring homomorphism and S satisfies IBN, then so does R.

Assessment: included
Mathlib contains `InvariantBasisNumber` as a type class in `Mathlib/LinearAlgebra/InvariantBasisNumber.lean`. The transfer of IBN along ring homomorphisms is established there. Specifically, `invariantBasisNumber_of_rankCondition` and related lemmas show how IBN transfers. The statement that a nontrivial ring with a homomorphism to a ring satisfying IBN also satisfies IBN is a consequence of these results.

## Statement 2: Corollary 1.18
Any ring admitting a homomorphism into a skew field satisfies IBN.

Assessment: included
In `Mathlib/LinearAlgebra/InvariantBasisNumber.lean`, it is shown that division rings satisfy the strong rank condition (hence IBN), and in `Mathlib/LinearAlgebra/FreeModule/StrongRankCondition.lean`, the strong rank condition (and hence IBN) transfers along ring homomorphisms to nontrivial rings. Since division rings satisfy IBN, any ring mapping into one does too.

## Statement 3: Theorem 1.23
Suppose that every R-module is free. Then R is a skew field.

Assessment: non-included
Searched for this specific characterization of division rings in `Mathlib/Algebra/Field/`, `Mathlib/RingTheory/`, and `Mathlib/LinearAlgebra/`. While mathlib has extensive material on division rings and free modules, this specific equivalence (every module free implies the ring is a division ring) does not appear to be formalized.

## Statement 4: Lemma 1.26 (Schur's Lemma)
If M is simple, then $\operatorname{End}_R(M)$ is a division ring.

Assessment: included
This is explicitly in `Mathlib/RingTheory/SimpleModule/Basic.lean` (line 30-34 in the docstring: "Schur's Lemma: `bijective_or_eq_zero`... leading to a `DivisionRing` structure on the endomorphism ring"). Also proved in the category-theoretic setting in `Mathlib/CategoryTheory/Preadditive/Schur.lean` where a `DivisionRing` instance on `End X` is provided for simple objects X.

## Statement 5: Corollary 1.27
Any nonzero map of simple modules is an isomorphism. In particular, if M, N are non-isomorphic simple modules, Hom(M, N) = 0.

Assessment: included
In `Mathlib/CategoryTheory/Preadditive/Schur.lean`, `isIso_of_hom_simple` shows that a nonzero morphism between simple objects is an isomorphism. In `Mathlib/RingTheory/SimpleModule/Basic.lean`, `bijective_or_eq_zero` provides the module-theoretic version.

## Statement 6: Lemma 1.28
a) Every nonzero ring has a simple module.
b) Every proper left ideal in a nonzero ring is contained in a maximal ideal.
c) A proper submodule N in a module M is maximal iff M/N is simple.

Assessment: included
Part (c) is `isSimpleModule_iff_quot_maximal` in `Mathlib/RingTheory/SimpleModule/Basic.lean`. Part (b) follows from Zorn's lemma as applied in `Mathlib/RingTheory/Ideal/Basic.lean` (existence of maximal ideals). Part (a) follows from (b) and (c) and is implicit in the existence of simple modules used throughout the library.

## Statement 7: Corollary 1.30
Every finitely generated module has an irreducible quotient.

Assessment: included
This follows from Lemma 1.28 parts (b) and (c) which are in mathlib. Every finitely generated module has a maximal submodule (by Zorn's lemma, as the module is finitely generated), and the quotient by a maximal submodule is simple. This is used implicitly in several places in the library.

## Statement 8: Lemma 1.33
Let $M = \bigoplus_{i \in I} M_i$ be a semisimple module, $M_i$ are simple modules. Then any submodule $N \subset M$ has a direct complement of the form $\bigoplus_{i \in J} M_i$ for some $J \subset I$.

Assessment: included
This is a consequence of the `ComplementedLattice` instance on submodules of a semisimple module, which is part of the definition `IsSemisimpleModule` in `Mathlib/RingTheory/SimpleModule/Basic.lean`. The complemented lattice property means every submodule has a complement. The specific form of the complement as a direct sum of some of the simple summands is implicit in the proof.

## Statement 9: Theorem 1.34
Every R-module is semisimple iff $R = \prod_{i=1}^n \operatorname{Mat}_{n_i}(D_i)$ where the $D_i$ are skew fields.

Assessment: included
This is the Wedderburn-Artin theorem formalized in `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`. `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite` shows that a semisimple ring is isomorphic to a finite product of matrix rings over division rings.

## Statement 10: Corollary 2.2
Subquotients and sums of semisimple modules are semisimple.

Assessment: included
In `Mathlib/RingTheory/SimpleModule/Basic.lean`, `IsSemisimpleModule.submodule` and `IsSemisimpleModule.quotient` show that submodules and quotients of semisimple modules are semisimple. The result `isSemisimpleModule_of_isSemisimpleModule_submodule` handles sums.

## Statement 11: Proposition 2.9
M is semisimple iff any short exact sequence $0 \to M_1 \to M \to M_2 \to 0$ splits.

Assessment: included
The equivalence between semisimplicity and having a complemented lattice of submodules (which is equivalent to all short exact sequences splitting) is the definition of `IsSemisimpleModule` in `Mathlib/RingTheory/SimpleModule/Basic.lean` together with `sSup_simples_eq_top_iff_isSemisimpleModule`.

## Statement 12: Theorem 2.10
Every R-module is semisimple iff R is semisimple over itself iff $R = \prod_{i=1}^{n} \operatorname{Mat}_{n_i}(D_i)$ where the $D_i$ are skew fields.

Assessment: included
This is the core of the Wedderburn-Artin theorem. The equivalence between R being semisimple (as a module over itself) and every R-module being semisimple is `IsSemisimpleRing.isSemisimpleModule` in `Mathlib/RingTheory/SimpleModule/Basic.lean`. The structural decomposition is in `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`.

## Statement 13: Theorem 2.16 (Wedderburn)
Let R be a ring. TFAE: a) R is simple and Artinian, b) every R-module is semisimple and R has a unique simple module up to isomorphism, c) $R \cong \operatorname{Mat}_n(D)$ where D is a skew field.

Assessment: included
In `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`, `IsSimpleRing.tfae` proves that for a simple ring: semisimple iff Artinian iff has minimal left ideal. `IsSimpleRing.exists_ringEquiv_matrix_divisionRing` gives the structural result (c). `isSimpleRing_isArtinianRing_iff` provides the equivalence between simple Artinian and semisimple isotypic nontrivial.

## Statement 14: Corollary 3.2
Suppose that k is algebraically closed and |G| does not divide char k. Then $|G| = \sum (\dim \rho_i)^2$ where the $\rho_i$ are the isomorphism classes of simple k[G]-modules.

Assessment: included
Mathlib has Maschke's theorem in `Mathlib/RepresentationTheory/Maschke.lean` (semisimplicity of group algebras when the characteristic does not divide the group order) and the dimension formula follows from the Wedderburn-Artin theorem. In `Mathlib/RepresentationTheory/FinGroupCharZero.lean`, the results about semisimplicity of group algebras in characteristic zero are established.

## Statement 15: Theorem 3.3 (Density Theorem)
Let L be a simple R-module and $D = \operatorname{End}_R(L)$. Then given any finite set $x_1, \ldots, x_n, y_1, \ldots, y_n \in L$ with the $x_i$ linearly independent over D, there exists $r \in R$ such that $r(x_i) = y_i$.

Assessment: non-included
Searched for "JacobsonDensity", "DensityTheorem", "dense" in the RingTheory and LinearAlgebra directories. The Jacobson density theorem does not appear to be formalized in mathlib v4.27.0. While mathlib has the consequences (like Wedderburn-Artin), the density theorem itself is not present as a standalone result.

## Statement 16: Corollary 3.5
If L is finite-dimensional simple over $D := \operatorname{End}_R(L)$, then there is a surjection $R \to \operatorname{End}_D(L) \cong \operatorname{Mat}_n(D)$, $n = \dim_D(L)$.

Assessment: non-included
This is a direct consequence of the density theorem (Statement 15), which is not in mathlib. While the Wedderburn-Artin theorem achieves similar structural results, this specific corollary about the surjection from R to the endomorphism ring is not formalized separately.

## Statement 17: Proposition 3.10
A module is Noetherian iff every submodule is finitely generated.

Assessment: included
This is a standard characterization of Noetherian modules formalized in `Mathlib/RingTheory/Noetherian/Basic.lean` and `Mathlib/RingTheory/Noetherian/Defs.lean`. The equivalence between ACC on submodules and every submodule being finitely generated is a foundational result there.

## Statement 18: Proposition 3.11
If $0 \to M_1 \to M \to M_2 \to 0$ is a short exact sequence and $M_1, M_2$ are Noetherian (resp. Artinian), then M is also Noetherian (resp. Artinian).

Assessment: included
For the Noetherian case, this is in `Mathlib/RingTheory/Noetherian/Basic.lean` (e.g., `isNoetherian_iff_submodule_quotient`). For the Artinian case, it is in `Mathlib/RingTheory/Artinian/Module.lean` (`isArtinian_iff_submodule_quotient`).

## Statement 19: Lemma 3.13
A module M has finite length iff M is both Noetherian and Artinian.

Assessment: included
This is `isFiniteLength_iff_isNoetherian_isArtinian` in `Mathlib/RingTheory/FiniteLength.lean`, which states exactly that `IsFiniteLength R M iff IsNoetherian R M /\ IsArtinian R M`.

## Statement 20: Theorem 3.15 (Jordan-Holder)
Given two composition series of M, the associated graded modules are the same (up to permutation). The number of irreducible subquotients isomorphic to a given simple module L is independent of the choice of filtration.

Assessment: included
The Jordan-Holder theorem is formalized in `Mathlib/Order/JordanHolder.lean` as `CompositionSeries.jordan_holder`, which says that two composition series with the same endpoints are `Equivalent` (there is a bijection on their factors preserving the isomorphism type).

## Statement 21: Corollary 3.19
Let $\mathcal{M}$ be the modules of finite length over R. Then $K(\mathcal{M})$ is freely generated by [L] for irreducible modules L.

Assessment: non-included
While mathlib has the Jordan-Holder theorem and the definition of Grothendieck groups (in `Mathlib/GroupTheory/MonoidLocalization/GrothendieckGroup.lean`), the specific statement that the Grothendieck group of finite-length modules is freely generated by classes of simple modules is not formalized.

## Statement 22: Lemma 3.21
Multiple equivalent characterizations of the Jacobson radical: intersection of annihilators of simple modules, intersection of maximal left ideals, elements a such that 1-xay is invertible for all x,y, etc.

Assessment: included
The Jacobson radical is defined in `Mathlib/RingTheory/Jacobson/Radical.lean` and `Mathlib/RingTheory/Jacobson/Semiprimary.lean`. The characterization as the intersection of maximal left ideals and the relationship with annihilators of simple modules are established there. The invertibility characterization (1-xay invertible) is captured via `Ring.jacobson`.

## Statement 23: Proposition 4.15
If M is indecomposable of finite length, then $\operatorname{End}_R(M)$ is local.

Assessment: non-included
While mathlib defines local rings (`IsLocalRing` in `Mathlib/RingTheory/LocalRing/`) and has some results on endomorphism rings, the specific statement that the endomorphism ring of an indecomposable finite-length module is local (the "Fitting lemma" approach) does not appear to be formalized. No results for "FittingLemma" were found in the library.

## Statement 24: Lemma 4.16
If M is an indecomposable finite length module, every $a \in \operatorname{End}_R(M)$ is either nilpotent or invertible.

Assessment: non-included
This is the Fitting lemma, which is not present in mathlib. Searched for "FittingLemma", "Fitting" in the library with no relevant results.

## Statement 25: Theorem 4.17 (Krull-Schmidt)
a) Every finite length module can be decomposed as a direct sum of indecomposable modules.
b) For any two such decompositions, the multisets of isomorphism classes of the indecomposable summands coincide.

Assessment: non-included
Searched for "KrullSchmidt", "Krull.*Schmidt" in the library. The only hit was in `Mathlib/CategoryTheory/Preadditive/Mat.lean` which mentions Krull-Schmidt in a comment but does not formalize it. The theorem itself is not present in mathlib v4.27.0.

## Statement 26: Proposition 5.6
A (left or right) Artinian semi-primitive ring has the form $\prod_{i=1}^{n} \operatorname{Mat}_{n_i}(D_i)$.

Assessment: included
This follows from the Wedderburn-Artin theorem. An Artinian semi-primitive ring is semisimple (as shown in the Hopkins-Levitzki developments in `Mathlib/RingTheory/HopkinsLevitzki.lean`), and a semisimple ring has the desired form by `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite` in `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`.

## Statement 27: Corollary 5.7
Suppose R is Artinian. Then M is semisimple iff J(R)M = 0.

Assessment: included
In `Mathlib/RingTheory/Artinian/Module.lean`, `IsArtinian.isSemisimpleModule_iff_jacobson` states that an Artinian module is semisimple iff its Jacobson radical is zero. The Jacobson radical annihilation characterization is in `Mathlib/RingTheory/Jacobson/Semiprimary.lean`.

## Statement 28: Corollary 5.8 (Nakayama's Lemma)
Suppose M is a finitely generated R-module such that J(R)M = M. Then M = 0.

Assessment: included
Nakayama's lemma is formalized in `Mathlib/RingTheory/Nakayama.lean` and `Mathlib/RingTheory/Finiteness/Nakayama.lean`. The statement that if J(R)M = M for a finitely generated M, then M = 0, is a standard form of the lemma present there.

## Statement 29: Theorem 6.1 (Akizuki-Hopkins-Levitzki)
A left (or right) Artinian ring is Noetherian.

Assessment: included
This is the Hopkins-Levitzki theorem, formalized in `Mathlib/RingTheory/HopkinsLevitzki.lean`. The file proves `IsSemiprimaryRing.isNoetherian_iff_isArtinian` (Hopkins-Levitzki for modules over semiprimary rings), and that Artinian rings are semiprimary (`instIsSemiprimaryRingOfIsArtinianRing` in `Mathlib/RingTheory/Artinian/Module.lean`), hence Noetherian.

## Statement 30: Proposition 6.4
Let R be a ring such that every finitely generated module has a projective cover. Then R/J(R) is semisimple and idempotents lift modulo J(R).

Assessment: non-included
Searched for "projective_cover", "ProjectiveCover", "idempotent.*lift" in mathlib. No formalization of projective covers or idempotent lifting was found in the library.

## Statement 31: Proposition 6.5
The map $P \mapsto P/J(R)P$ is a bijection between indecomposable projective R-modules and simple R-modules.

Assessment: non-included
This requires projective covers which are not formalized in mathlib. No results were found for the bijection between indecomposable projectives and simples.

## Statement 32: Theorem 7.1 (Morita Equivalence)
$\operatorname{End}_R(P)$-mod is equivalent to R-mod iff P is a projective generator.

Assessment: non-included
While mathlib has the definition of Morita equivalence in `Mathlib/RingTheory/Morita/Basic.lean` (as an R-linear equivalence of module categories) and the definition `IsMoritaEquivalent`, the characterization via projective generators is listed as a TODO in that file. The file notes "Morita equivalence in terms of projective generators" as future work.

## Statement 33: Lemma 7.3 (Yoneda Lemma)
The functor $Y: C \to \operatorname{Fun}(C^{op}, \operatorname{Set})$ sending $a \mapsto \operatorname{Hom}(-, a)$ is fully faithful.

Assessment: included
The Yoneda lemma is formalized in mathlib's category theory library. `CategoryTheory.yoneda` defines the Yoneda embedding and its full faithfulness is established.

## Statement 34: Proposition 7.5
Two rings R and S are Morita equivalent iff $S \cong \operatorname{End}_R(P)$ for some projective generator P for R.

Assessment: non-included
As noted above, the characterization of Morita equivalence via projective generators is listed as a TODO in `Mathlib/RingTheory/Morita/Basic.lean`.

## Statement 35: Proposition 8.5
For Morita equivalent rings R, S via functors F, G, the functor F is naturally isomorphic to tensoring with a bimodule.

Assessment: non-included
The Eilenberg-Watts theorem (that cocontinuous additive functors between module categories are tensor products with bimodules) is not formalized in mathlib. The Morita theory in mathlib is at an early stage.

## Statement 36: Theorem 12.5 (Koszul Duality)
If A is a Koszul algebra, then A! is also Koszul and (A!)! = A.

Assessment: non-included
Searched for "Koszul", "koszul" in mathlib. The only hits are `Mathlib/Algebra/Homology/LocalCohomology.lean` and `Mathlib/RingTheory/Regular/RegularSequence.lean`, which deal with Koszul complexes in the commutative algebra sense, not Koszul duality for graded algebras. The theory of Koszul algebras and their duals is not present.

## Statement 37: Proposition 13.4
$A \otimes_F A^{op} \cong \operatorname{End}_F(A)$ for any central simple algebra A over F.

Assessment: included
This is essentially the definition of an Azumaya/CSA algebra. In `Mathlib/Algebra/Azumaya/Defs.lean` and `Mathlib/Algebra/Azumaya/Basic.lean`, the map `AlgHom.mulLeftRight R A : A tensor A^mop -> End_R A` being bijective is the defining property of `IsAzumaya`. For CSAs over fields, this is a consequence of the CSA structure defined in `Mathlib/Algebra/BrauerGroup/Defs.lean`.

## Statement 38: Theorem 14.1 (Skolem-Noether)
Let A be a central simple algebra over F. Every automorphism of A is inner.

Assessment: non-included
Searched for "SkolemNoether", "Skolem.*Noether" in the library. Found hits in `Mathlib/LinearAlgebra/Trace.lean` and `Mathlib/LinearAlgebra/Determinant.lean` but these are only comments referencing Skolem-Noether, not formalizations. The theorem itself is not proved in mathlib.

## Statement 39: Theorem 14.2 (Artin-Wedderburn for CSAs)
A finite-dimensional central simple algebra over F is isomorphic to $\operatorname{Mat}_n(D)$ for a unique division algebra D central over F.

Assessment: included
In `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`, `IsSimpleRing.exists_ringEquiv_matrix_divisionRing` shows a simple Artinian ring (which a finite-dimensional CSA over a field is) is isomorphic to a matrix ring over a division ring. For CSAs specifically, `Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean` provides additional results.

## Statement 40: Corollary 14.3
Every automorphism of $\operatorname{Mat}_n(F)$ is inner.

Assessment: non-included
This is a special case of Skolem-Noether, which is not formalized in mathlib.

## Statement 41: Proposition 14.5
Let B be a simple subalgebra of a central simple algebra A over F. Then the centralizer $C_A(B)$ is simple and $\dim_F A = \dim_F B \cdot \dim_F C_A(B)$.

Assessment: non-included
Searched for "centralizer" in the context of CSAs and simple algebras. While mathlib has centralizer theory in `Mathlib/Algebra/Central/`, the double centralizer theorem for CSAs and the dimension formula are not present.

## Statement 42: Proposition 14.6
If B is a simple subalgebra of a central simple algebra A over F, then $C_A(C_A(B)) = B$.

Assessment: non-included
The double centralizer theorem for CSAs is not formalized in mathlib. Searched for "double_centralizer", "DoubleCentralizer", "bicommutant" with no relevant results for CSAs.

## Statement 43: Corollary 14.7
Every maximal commutative subalgebra of a central simple algebra A of degree n over F has dimension n over F.

Assessment: non-included
This is a consequence of the double centralizer theorem which is not in mathlib.

## Statement 44: Corollary 14.8
Every commutative field extension $E/F$ of degree n embeds into $\operatorname{Mat}_n(F)$.

Assessment: non-included
While this is a classical result in noncommutative algebra, it does not appear to be formalized in mathlib. Searched for relevant embedding results in `Mathlib/FieldTheory/` and `Mathlib/RingTheory/` without finding this.

## Statement 45: Corollary 14.9
A CSA of degree n over F is split iff it contains $F^n$ as a subalgebra.

Assessment: non-included
The splitting criterion for CSAs via subalgebras is not formalized in mathlib. The Brauer group infrastructure in `Mathlib/Algebra/BrauerGroup/Defs.lean` defines Brauer equivalence but does not include splitting criteria.

## Statement 46: Proposition 14.10
A central simple algebra A over F is split iff it has a left ideal of dimension n = deg(A) over F.

Assessment: non-included
This splitting criterion is not in mathlib.

## Statement 47: Corollary 14.11
A CSA of degree n is split by E/F iff E embeds into A as a maximal commutative subalgebra.

Assessment: non-included
Not formalized in mathlib.

## Statement 48: Corollary 14.12
The index of [A] divides deg(A), and they are equal iff A is a division algebra.

Assessment: non-included
The notion of index of an element of the Brauer group is not defined in mathlib.

## Statement 49: Corollary 14.13
A CSA A of degree n over F is split by a field extension E/F with $[E:F] \le n$.

Assessment: non-included
Not formalized in mathlib.

## Statement 50: Corollary 14.14
If E/F is a separable field extension with $[E:F] = n$, then $A \otimes_F E \cong \operatorname{Mat}_n(E)$ iff E embeds into A.

Assessment: non-included
Not formalized in mathlib.

## Statement 51: Theorem 14.15
Every CSA A over F is split by a finite separable extension of F.

Assessment: non-included
Not formalized in mathlib. The Brauer group theory in mathlib is at a very early stage.

## Statement 52: Proposition 15.2
The Brauer group $\operatorname{Br}(E/F)$ for a cyclic Galois extension E/F is isomorphic to $F^\times / \operatorname{Nm}(E^\times)$.

Assessment: non-included
Not formalized in mathlib. The Brauer group file `Mathlib/Algebra/BrauerGroup/Defs.lean` only defines Brauer equivalence and its reflexivity, symmetry, and transitivity.

## Statement 53: Lemma 16.3
A CSA A over F is split by E/F iff E embeds into A as a maximal commutative subfield.

Assessment: non-included
Not formalized in mathlib.

## Statement 54: Theorem 16.4
$\operatorname{Br}(E/F) \cong H^2(\operatorname{Gal}(E/F), E^\times)$ for a finite Galois extension E/F.

Assessment: non-included
The cohomological description of the Brauer group is not in mathlib. While mathlib has group cohomology (`Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`), it is not connected to the Brauer group.

## Statement 55: Corollary 16.7
For a cyclic extension E/F, $\operatorname{Br}(E/F) \cong F^\times / \operatorname{Nm}_{E/F}(E^\times)$.

Assessment: non-included
Not formalized in mathlib.

## Statement 56: Theorem 16.8
The period of $[A] \in \operatorname{Br}(F)$ divides the index, and has the same prime factors.

Assessment: non-included
Not formalized in mathlib.

## Statement 57: Proposition 17.1
There exist well-defined reduced norm and reduced trace for a CSA A over F.

Assessment: non-included
Searched for "reduced_norm", "reduced_trace", "Nrd", "Trd" in mathlib. These notions are not formalized.

## Statement 58: Lemma 17.5
If F is a $C_1$ field and $E/F$ is a finite extension, then E is also $C_1$.

Assessment: non-included
Searched for "C1Field", "ChevalleyWarning" in mathlib. The notion of $C_1$ fields is not present.

## Statement 59: Theorem 17.6 (Chevalley-Warning)
Finite fields are $C_1$ fields.

Assessment: non-included
While there is a file `Mathlib/Combinatorics/Additive/ErdosGinzburgZiv.lean` that mentions Chevalley-Warning, it is in a different context (Erdos-Ginzburg-Ziv). The Chevalley-Warning theorem itself (that finite fields are $C_1$) is not formalized.

## Statement 60: Theorem 17.8 (Tsen's Theorem)
Suppose k is algebraically closed. Then the field $F = k(t)$ is $C_1$.

Assessment: non-included
Tsen's theorem is not formalized in mathlib.

## Statement 61: Theorem 17.10
Let F be a non-Archimedean local field. Then $\operatorname{Br}(F) \cong \mathbb{Q}/\mathbb{Z}$.

Assessment: non-included
The Brauer group of local fields is not computed in mathlib.

## Statement 62: Proposition 17.14
Every central simple algebra over a local field F splits over an unramified extension.

Assessment: non-included
Not formalized in mathlib.

## Statement 63: Proposition 17.15
If E/F is an unramified degree n extension of a non-Archimedean local field, then $\operatorname{Br}(E/F) = \mathbb{Z}/n\mathbb{Z}$.

Assessment: non-included
Not formalized in mathlib.

## Statement 64: Lemma 18.1
Equivalent characterizations of Azumaya algebras: $A \otimes_R A^{op} \to \operatorname{End}_R(A)$ is an isomorphism; base change to every algebraically closed residue field gives a matrix algebra; base change to every residue field gives a CSA.

Assessment: included
The definition `IsAzumaya` in `Mathlib/Algebra/Azumaya/Defs.lean` uses the condition that `AlgHom.mulLeftRight R A` (the map $A \otimes_R A^{op} \to \operatorname{End}_R(A)$) is bijective. Some equivalent characterizations are developed in `Mathlib/Algebra/Azumaya/Basic.lean` and `Mathlib/Algebra/Azumaya/Matrix.lean`.

## Statement 65: Proposition 18.11
If $R \to S$ is faithfully flat, the functor sending M to its descent data is an equivalence.

Assessment: non-included
Faithfully flat descent is not fully formalized in mathlib. While there are definitions related to flat and faithfully flat modules in `Mathlib/RingTheory/Flat/`, the descent equivalence is not present.

## Statement 66: Theorem 18.15
The universal splitting functor for an Azumaya algebra is representable, formally smooth, and faithfully flat.

Assessment: non-included
Not formalized in mathlib. The Azumaya algebra theory in mathlib is at a basic level.

## Statement 67: Theorem 19.5
For R a smooth finitely generated commutative domain over an algebraically closed field, $\operatorname{Br}(R) \hookrightarrow \operatorname{Br}(\operatorname{Frac}(R))$.

Assessment: non-included
Not formalized in mathlib. This requires the theory of Brauer-Severi varieties which is absent.

## Statement 68: Lemma 19.7
$R_S = R(t_s)_{s \in S}/(t_s s = s t_s = 1)$ (explicit presentation of the localization at a multiplicative subset).

Assessment: non-included
This is about noncommutative localization. While mathlib has commutative localization in `Mathlib/RingTheory/Localization/`, the noncommutative (Ore) localization is not present.

## Statement 69: Proposition 20.1
For a right reversible multiplicative subset S in a ring R, the localization $R_S$ can be described as equivalence classes of fractions $as^{-1}$.

Assessment: non-included
Ore localization is not formalized in mathlib. No results for "Ore" were found in the ring theory directories.

## Statement 70: Corollary 20.2
For a right denominator set $S \subset R$, the kernel of $R \to R_S$ is $\{a \in R \mid as = 0 \text{ for some } s \in S\}$.

Assessment: non-included
Ore localization is not in mathlib.

## Statement 71: Corollary 20.4
If S consists of regular elements, $R \to R_S$ is injective.

Assessment: non-included
Ore localization is not in mathlib.

## Statement 72: Proposition 20.5
If S is a right denominator set, then the diagram category D is filtered.

Assessment: non-included
Ore localization is not in mathlib.

## Statement 73: Proposition 20.9
a) (Goldie) Either R is a right Ore domain or it contains a free right ideal of infinite rank.
b) (Jategoankar) Either R is a left and right Ore domain or it contains a free ring.

Assessment: non-included
These results about Ore domains are not in mathlib.

## Statement 74: Corollary 20.12
If A is a domain of subexponential growth, then A is an Ore domain.

Assessment: non-included
Growth of algebras and Ore domains are not formalized in mathlib.

## Statement 75: Proposition 20.16
Every semi-primitive ring is semi-prime.

Assessment: non-included
The notions of semi-primitive and semi-prime rings in the noncommutative sense are not directly formalized in mathlib as used in this textbook. While mathlib has Jacobson radicals and prime ideals in commutative settings, the specific noncommutative ring-theoretic notions of "prime ring" and "semi-prime ring" (where $IJ \neq 0$ for nonzero two-sided ideals) are not present.

## Statement 76: Theorem 20.17 (Goldie)
If R is a semi-prime right Noetherian ring, then the set of regular elements satisfies the Ore condition, and $R_S$ is Artinian semisimple.

Assessment: non-included
Goldie's theorem is not formalized in mathlib. The Ore conditions, noncommutative localization, and the concepts of Goldie rank are all absent.

## Statement 77: Corollary 20.18
If R is left or right Noetherian, it admits a homomorphism to $\operatorname{Mat}_n(D)$, so it satisfies the IBN.

Assessment: included
In `Mathlib/RingTheory/Noetherian/Orzech.lean`, it is shown that Noetherian rings satisfy the Orzech property, which implies the strong rank condition, which implies IBN. The result `IsNoetherianRing.strongRankCondition` (referenced in `Mathlib/LinearAlgebra/InvariantBasisNumber.lean`) gives this. The approach is different (via Orzech property rather than Goldie's theorem), but the conclusion is the same.

## Statement 78: Lemma 20.21
If $N \subset M$ is a submodule, then there exists a submodule $N' \subset M$ such that $N \oplus N'$ is an essential submodule in M.

Assessment: non-included
The theory of essential submodules and essential complements is not formalized in mathlib.

## Statement 79: Proposition 20.22
A Noetherian module contains an essential submodule that is a sum of uniform submodules, and the number of uniform summands (Goldie rank) is independent of choices.

Assessment: non-included
Goldie rank and uniform submodules are not in mathlib.

## Statement 80: Corollary 20.23
If $s \in R$ is regular, then $sR \subset R$ is essential.

Assessment: non-included
Essential submodules are not formalized in mathlib.

## Statement 81: Lemma 20.24
The preimage of an essential submodule is essential.

Assessment: non-included
Essential submodules are not in mathlib.

## Statement 82: Proposition 20.25
An essential right ideal in a semi-prime right Noetherian ring contains a regular element.

Assessment: non-included
Not formalized in mathlib.

## Statement 83: Corollary 21.1
A module M has no proper essential submodules iff it is semisimple.

Assessment: non-included
Essential submodules are not formalized in mathlib.

## Statement 84: Lemma 21.2
Properties of essential submodules: transitivity, preimage preservation, direct sum preservation.

Assessment: non-included
Essential submodules are not in mathlib.

## Statement 85: Proposition 21.5
A finite Goldie rank module contains an essential submodule which is a finite sum of uniform submodules.

Assessment: non-included
Goldie rank theory is not in mathlib.

## Statement 86: Theorem 21.6
If M has finite Goldie rank m and $E = \bigoplus_{i=1}^m U_i$ essential with $U_i$ uniform, and $N = \bigoplus_{i=1}^n N_i$ with $N_i \neq 0$, then $n \le m$.

Assessment: non-included
Goldie rank theory is not in mathlib.

## Statement 87: Corollary 21.7
If M has finite Goldie rank n, every submodule of the same Goldie rank is essential.

Assessment: non-included
Goldie rank theory is not in mathlib.

## Statement 88: Theorem 21.11
An essential right ideal in a semi-prime, right Noetherian ring contains a regular element.

Assessment: non-included
Not in mathlib.

## Statement 89: Lemma 21.12
Let R be a right Noetherian, semi-prime ring and $I \subset R$ an essential right ideal. Then the left annihilator of I is zero.

Assessment: non-included
Not in mathlib.

## Statement 90: Proposition 21.13
Any right ideal I contains an element x with $\operatorname{rAnn}(x) \cap I = 0$.

Assessment: non-included
Not in mathlib.

## Statement 91: Proposition 22.3
Let R be a semi-prime Goldie ring and S the set of regular elements. Essential subideal localizations coincide; uniform ideal localizations are irreducible.

Assessment: non-included
Goldie theory is not in mathlib.

## Statement 92: Theorem 22.9 (Amitsur-Levitzki)
$S_{2n}$ is an identity in $\operatorname{Mat}_n(R)$ for commutative R, and no homogeneous identity of smaller degree holds.

Assessment: non-included
The Amitsur-Levitzki theorem is not formalized in mathlib. Searched for "amitsur", "levitzki", "AmitsurLevitzki" and found no relevant results (only the Hopkins-Levitzki theorem, which is different).

## Statement 93: Lemma 22.10 (Staircase Lemma)
$\operatorname{Mat}_n(R)$ does not satisfy a multilinear identity of degree $d < 2n$.

Assessment: non-included
PI ring theory is not in mathlib.

## Statement 94: Lemma 22.11
a) If a ring satisfies an identity of degree d, it satisfies a multilinear one of the same degree.
b) Over an infinite field, each homogeneous component of a PI is also an identity.

Assessment: non-included
PI ring theory is not in mathlib.

## Statement 95: Theorem 23.1 (Cayley-Hamilton)
Let $x \in \operatorname{Mat}_n(R)$ with R commutative and $P_x(t)$ its characteristic polynomial. Then $P_x(x) = 0$.

Assessment: included
This is `Matrix.aeval_self_charpoly` in `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`, which states exactly that `aeval M M.charpoly = 0` for a matrix M over a commutative ring.

## Statement 96: Corollary 23.2
If $P_x(t) = t^n$, then $x^n = 0$.

Assessment: included
This is a direct corollary of Cayley-Hamilton. In `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`, once `aeval_self_charpoly` is established, this follows immediately. The nilpotency result is used in various places in the library.

## Statement 97: Theorem 23.3 (Kaplansky)
A primitive PI algebra with identity of degree d is simple of degree $\le d/2$ over its center.

Assessment: non-included
Kaplansky's theorem for PI algebras is not in mathlib. PI ring theory is entirely absent.

## Statement 98: Theorem 23.4 (Posner)
A prime PI algebra has a domain center, and localizing at the center gives $\operatorname{Mat}_n(D)$ with D finite-dimensional over the fraction field.

Assessment: non-included
Posner's theorem is not in mathlib.

## Statement 99: Theorem 23.5 (Rowen)
In a semi-prime PI algebra, every nonzero two-sided ideal meets the center.

Assessment: non-included
Rowen's theorem is not in mathlib.

## Statement 100: Corollary 23.6
A prime PI ring whose center is a field is a central simple algebra over that field.

Assessment: non-included
Not in mathlib.

## Statement 101: Lemma 23.7
For $x \in \operatorname{Mat}_n(k)$, $\sum_i m_i x m_i^* = \operatorname{Tr}(x) I_n$.

Assessment: non-included
This specific identity about dual bases and trace in matrix algebras is not in mathlib as a standalone result.

## Statement 102: Lemma 23.9
Relationship between the Capelli polynomial and dual bases via the trace pairing.

Assessment: non-included
The Capelli polynomial and its properties are not in mathlib.

## Statement 103: Theorem 23.11
The Razmyslov polynomial takes values in scalar matrices and is not identically zero.

Assessment: non-included
The Razmyslov polynomial is not in mathlib. Central polynomials for matrix rings are not formalized.

## Statement 104: Proposition 23.12
In a semi-primitive PI algebra, every nonzero two-sided ideal meets the center.

Assessment: non-included
Not in mathlib.

## Statement 105: Theorem 23.13
If R is a semi-prime PI algebra, then R[t] is semi-primitive.

Assessment: non-included
Not in mathlib.

## Statement 106: Theorem 23.15 (Amitsur)
If R has no nonzero nil ideals, then R[t] is semi-primitive.

Assessment: non-included
Not in mathlib.

## Statement 107: Proposition 23.16
A semi-prime PI algebra contains no nil ideals.

Assessment: non-included
Not in mathlib.

## Statement 108: Lemma 23.17
If R satisfies ACC on right annihilators and is semi-prime, every nil left ideal is zero.

Assessment: non-included
Not in mathlib.

## Statement 109: Lemma 23.18
A prime PI ring satisfies ACC on right and left annihilators.

Assessment: non-included
Not in mathlib.

## Statement 110: Lemma 23.19
A semi-prime ideal is an intersection of prime ideals.

Assessment: included
For commutative rings, this is formalized in mathlib. The radical of an ideal being the intersection of prime ideals containing it is in `Mathlib/RingTheory/Ideal/Radical.lean`. A semi-prime ideal (one whose quotient ring is reduced/semi-prime) equals its own radical, hence is an intersection of primes.

## Statement 111: Lemma 24.5
a) GKdim(A) < 1 implies A is finite-dimensional.
b) GKdim(A[t]) = GKdim(A) + 1.
c) GKdim(A[a^{-1}]) = GKdim(A) if a is central and regular.

Assessment: non-included
Gelfand-Kirillov dimension is not defined in mathlib. Searched for "GelfandKirillov", "gelfand_kirillov", "GKdim" with no results.

## Statement 112: Theorem 24.6 (Warfield)
For any real $\delta \ge 2$, there exists an algebra with GK dimension $\delta$.

Assessment: non-included
GK dimension is not in mathlib.

## Statement 113: Theorem 24.8 (Bergman gap)
No finitely generated algebra has GK dimension strictly between 1 and 2.

Assessment: non-included
GK dimension is not in mathlib.

## Statement 114: Proposition 24.9
If A is graded generated in degree 1 with $\dim A_d < d$ for some d, then GKdim(A) $\le$ 1.

Assessment: non-included
GK dimension is not in mathlib.

## Statement 115: Lemma 24.10
Structure of allowed words of large length in terms of periodic subwords.

Assessment: non-included
Combinatorics on words related to GK dimension is not in mathlib.

## Statement 116: Lemma 24.11
A periodic word of minimal period p with two equal subwords of length p-1 has them p letters apart.

Assessment: non-included
Not in mathlib.

## Statement 117: Theorem 24.12 (Smoktunowicz)
The GK dimension of a graded domain cannot fall in (2, 3).

Assessment: non-included
Not in mathlib.

## Statement 118: Theorem 24.13 (Berele)
Finitely generated PI algebras have finite GK dimension.

Assessment: non-included
Neither PI algebras nor GK dimension are in mathlib.

## Statement 119: Proposition 24.17
If A has commutative associated graded, GKdim(M) is the dimension of the support of gr(M).

Assessment: non-included
GK dimension is not in mathlib.

## Statement 120: Lemma 24.18
For A with commutative associated graded, the support of gr(M) and its K-theory class are filtration-independent.

Assessment: non-included
Not in mathlib.

## Statement 121: Theorem 24.21 (Stephenson-Zhang)
A right (or left) Noetherian algebra has subexponential growth.

Assessment: non-included
Growth of algebras is not formalized in mathlib.

## Statement 122: Lemma 24.22
Characterizations of exponential growth and existence of certain subsequences.

Assessment: non-included
Growth of algebras is not in mathlib.

## Statement 123: Theorem 24.23
For a Noetherian graded algebra of finite homological dimension, the Hilbert series is the reciprocal of a polynomial whose roots are roots of unity.

Assessment: non-included
This deep result connecting Hilbert series, Noetherian property, and homological dimension is not in mathlib.

## Statement 124: Conjecture 24.24 (Polishchuk-Positselski)
The Hilbert series of a Koszul algebra is rational, with further structural properties.

Assessment: non-included
This is an open conjecture and is not in mathlib.

## Statement 125: Conjecture 24.25 (Anick)
For a right Noetherian algebra with finite GKdim and hdim, the Hilbert series equals that of a symmetric algebra.

Assessment: non-included
This is an open conjecture and is not in mathlib.

## Statement 126: Theorem 25.3 (Serre)
An algebraic variety X over k is smooth iff Coh(X) has finite homological dimension.

Assessment: non-included
While mathlib has extensive algebraic geometry infrastructure, this specific characterization of smoothness via homological dimension of the category of coherent sheaves does not appear to be formalized as a theorem. Smoothness in mathlib's algebraic geometry is approached differently.

## Statement 127: Conjecture 25.6
The degeneration of $\operatorname{HH}_* \implies \operatorname{HC}_*^{per}$ spectral sequence for dg-categories of finite type.

Assessment: non-included
This is an open conjecture (partially proved by Kaledin and Mathew) and is not in mathlib.
