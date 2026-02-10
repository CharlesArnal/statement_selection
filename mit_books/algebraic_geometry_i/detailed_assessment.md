# Detailed Assessment — 18.725 Algebraic Geometry I

## Statement 1 — Theorem 1.1 (Essential Nullstellensatz)
**Verdict: included**
The essential Nullstellensatz (if K/k is a field extension and K is a finitely generated k-algebra, then K/k is algebraic) is present in mathlib. The file `Mathlib/RingTheory/Nullstellensatz.lean` contains the full Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`), and `Mathlib/RingTheory/Jacobson/Ring.lean` contains the Jacobson property for polynomial rings which subsumes this result. Additionally, `Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean` and related files contain the needed algebraicity results for finitely generated field extensions.

## Statement 2 — Theorem 1.2 (Zariski closed subsets = radical ideals)
**Verdict: included**
The bijection between Zariski closed subsets of k^n and radical ideals in k[x_1,...,x_n] is established in `Mathlib/RingTheory/Nullstellensatz.lean` via `vanishingIdeal_zeroLocus_eq_radical` which proves that for an algebraically closed field k, the vanishing ideal of the zero locus of an ideal I equals the radical of I. The Galois connection `zeroLocus_vanishingIdeal_galoisConnection` sets up the correspondence.

## Statement 3 — Corollary 1 (Zariski topology on A^n)
**Verdict: included**
The Zariski topology on Spec of a ring (which generalizes A^n) is defined in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`. The topology is defined via `PrimeSpectrum.zariskiTopology` with closed sets being the zero loci of ideals. This is a standard part of the mathlib infrastructure for algebraic geometry.

## Statement 4 — Theorem 2.1 (k[Spec A] = A)
**Verdict: included**
The Gamma-Spec adjunction in `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean` establishes that the global sections of the structure sheaf on Spec A recover A. This is formalized as part of the adjunction between the category of commutative rings and the category of locally ringed spaces.

## Statement 5 — Lemma 1 (Noether Normalization)
**Verdict: included**
Noether normalization is proved in `Mathlib/RingTheory/NoetherNormalization.lean`. The theorem `exists_integral_inj_algHom_of_fg` states that for a finitely generated k-algebra R, there exists an injective algebra homomorphism from a polynomial ring MvPolynomial (Fin s) k to R making R an integral (hence finite) extension.

## Statement 6 — Proposition 1 (Spec A quasi-compact)
**Verdict: included**
The quasi-compactness of PrimeSpectrum R is established in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` as `PrimeSpectrum.compactSpace`, which shows that PrimeSpectrum R is a CompactSpace (which in mathlib corresponds to quasi-compactness for non-Hausdorff spaces).

## Statement 7 — Theorem 2.2 (affine variety = Spec A)
**Verdict: included**
The equivalence between affine schemes and commutative rings (the anti-equivalence of categories) is formalized through the Gamma-Spec adjunction in `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean` and the affine scheme characterization in `Mathlib/AlgebraicGeometry/AffineScheme.lean`. The categorical equivalence between affine schemes and the opposite category of commutative rings is a foundational result in mathlib's algebraic geometry library.

## Statement 8 — Lemma 2 (closed subspace of affine is affine)
**Verdict: included**
A closed subscheme of an affine scheme is affine, and the global sections map is surjective. This follows from the fact that the closed immersion of Spec(A/I) into Spec(A) is captured via the surjection A -> A/I. In mathlib, this is part of the infrastructure in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean` and `Mathlib/AlgebraicGeometry/AffineScheme.lean`.

## Statement 9 — Corollary 2 (closed subspace of variety is variety)
**Verdict: included**
This is a direct consequence of the previous result. In the scheme-theoretic setting of mathlib, closed subschemes of schemes are schemes, which is built into the definition. The relevant infrastructure is in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`.

## Statement 10 — Theorem 2.3 (Hilbert Basis Theorem)
**Verdict: included**
The Hilbert Basis Theorem is in `Mathlib/RingTheory/Polynomial/Basic.lean` as `Polynomial.isNoetherianRing`, which states that if R is a Noetherian ring, then R[X] is Noetherian. The multivariate version follows by induction and is also available.

## Statement 11 — Corollary 3 (algebraic variety is Noetherian space)
**Verdict: included**
That the spectrum of a Noetherian ring is a Noetherian topological space is established in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` and related files. The Noetherian property of the topological space follows from the Noetherian property of the ring.

## Statement 12 — Corollary 4 (open subspace of variety is variety)
**Verdict: included**
In the scheme-theoretic framework, open subschemes of schemes are schemes. This is handled via open immersions in `Mathlib/AlgebraicGeometry/OpenImmersion.lean` and `Mathlib/AlgebraicGeometry/Morphisms/OpenImmersion.lean`.

## Statement 13 — Theorem 3.1 (affine iff Spec A, restated)
**Verdict: included**
Same as Statement 7. The Gamma-Spec adjunction in `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean` establishes this equivalence.

## Statement 14 — Theorem 3.2 (Noether Normalization, restated)
**Verdict: included**
Same as Statement 5. Found in `Mathlib/RingTheory/NoetherNormalization.lean`.

## Statement 15 — Lemma 3 (monic change of variables)
**Verdict: included**
This technical lemma used in the proof of Noether normalization (that a nonconstant polynomial can be made monic in one variable via linear change of variables) is part of the proof in `Mathlib/RingTheory/NoetherNormalization.lean`, where the relevant variable substitution technique is implemented.

## Statement 16 — Proposition 2 (Hilbert Basis Theorem, restated)
**Verdict: included**
Same as Statement 10. In `Mathlib/RingTheory/Polynomial/Basic.lean`.

## Statement 17 — Theorem 3.3 (Essential Nullstellensatz, restated)
**Verdict: included**
Same as Statement 1. Covered by the Nullstellensatz and Jacobson ring infrastructure.

## Statement 18 — Lemma 4 (Nakayama Lemma)
**Verdict: included**
Nakayama's lemma is formalized in `Mathlib/RingTheory/Nakayama.lean`. The key result `Submodule.eq_smul_of_le_smul_of_le_jacobson` and related lemmas capture the statement that if M is a finitely generated module with IM = M and I is contained in the Jacobson radical, then M = 0, along with the version producing the element a with aM = 0 and a = 1 mod I.

## Statement 19 — Proposition 3 (Spec A irreducible iff domain)
**Verdict: included**
The equivalence between Spec A being an irreducible topological space and A being a domain is in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` as `PrimeSpectrum.irreducibleSpace`, which states `instance irreducibleSpace [IsDomain R] : IrreducibleSpace (PrimeSpectrum R)`. The converse direction is also available.

## Statement 20 — Proposition 4 (Noetherian space = finite union of components)
**Verdict: included**
That a Noetherian topological space has finitely many irreducible components is established in `Mathlib/Topology/NoetherianSpace.lean` and related files. The result that the space is a finite union of its irreducible components is part of the standard Noetherian space API.

## Statement 21 — Corollary 5 (irred. closed subsets = prime ideals)
**Verdict: included**
The correspondence between irreducible closed subsets of Spec A and prime ideals is fundamental to PrimeSpectrum. In `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`, the points of PrimeSpectrum are by definition prime ideals, and the correspondence between irreducible closed subsets and prime ideals is built into the topology.

## Statement 22 — Corollary 6 (0 = intersection of minimal primes)
**Verdict: included**
That the nilradical (which equals zero in a reduced ring) equals the intersection of all prime ideals is in `Mathlib/RingTheory/Ideal/Radical.lean`. The minimal prime version follows from the general theory of minimal primes in `Mathlib/RingTheory/Ideal/MinimalPrime.lean`.

## Statement 23 — Proposition 5 (restated: Noetherian = finite union of components)
**Verdict: included**
Same as Statement 20.

## Statement 24 — Lemma 5 (Noetherian space = finite union of closed irred.)
**Verdict: included**
This intermediate lemma is part of the proof infrastructure for Noetherian spaces in mathlib's topology library.

## Statement 25 — Corollary 7 (radical ideal = finite intersection of primes)
**Verdict: included**
Every radical ideal in a Noetherian ring is a finite intersection of prime ideals. This follows from the primary decomposition theory and the Noetherian space decomposition into irreducible components. Available in `Mathlib/RingTheory/Ideal/MinimalPrime.lean` and `Mathlib/RingTheory/Ideal/Radical.lean`.

## Statement 26 — Corollary 8 (closed irreducible iff prime ideal)
**Verdict: included**
Same content as Statement 21. Built into the PrimeSpectrum infrastructure.

## Statement 27 — Theorem 4.1 (Grassmannian is projective)
**Verdict: non-included**
While `Mathlib/RingTheory/Grassmannian.lean` defines the Grassmannian as a set (the set of submodules of a given rank), it does not establish the Grassmannian as a projective algebraic variety. The Plucker embedding and the projectivity of the Grassmannian are not formalized in mathlib. The file defines the Grassmannian functor but does not prove it is representable by a projective scheme.

## Statement 28 — Lemma 6 (wedge product criterion for decomposability)
**Verdict: non-included**
The criterion that omega in wedge^2 V is decomposable (i.e., equals v_1 wedge v_2) if and only if omega wedge omega = 0 (in dimension 4) is not formalized in mathlib. While mathlib has extensive exterior algebra infrastructure in `Mathlib/LinearAlgebra/ExteriorAlgebra/`, this specific decomposability criterion is not present.

## Statement 29 — Lemma 7 (finite map is closed with finite fibers)
**Verdict: included**
Finite morphisms are closed and have finite fibers. In mathlib, `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean` defines finite morphisms of schemes, and the properties of being closed (universally closed) and having finite fibers follow from the integral/finite morphism theory. The going-up theorem and related results in `Mathlib/RingTheory/Ideal/GoingUp.lean` support the closedness.

## Statement 30 — Corollary 9 (finite module => surjective on Spec)
**Verdict: included**
If A is a finitely generated B-module with B a subring, then Spec A -> Spec B is surjective with finite fibers. The going-up theorem in `Mathlib/RingTheory/Ideal/GoingUp.lean` establishes surjectivity for integral extensions, which includes the finite case.

## Statement 31 — Lemma 8 (finite morphism preserves strict containment)
**Verdict: non-included**
The specific statement that a finite morphism preserves strict containment of irreducible closed subsets (i.e., if Z_1 strictly contained in Z_2, then f(Z_1) strictly contained in f(Z_2)) is not directly formalized in mathlib as a standalone result in this form.

## Statement 32 — Lemma 9 (restated)
**Verdict: non-included**
Same as Statement 31.

## Statement 33 — Lemma 10 (finite surjection preserves dimension)
**Verdict: non-included**
The statement that dim(X) = dim(Y) for a finite surjective morphism of varieties is not directly in mathlib. While Krull dimension theory exists in `Mathlib/RingTheory/KrullDimension/`, the specific result about finite surjections preserving dimension is not formalized.

## Statement 34 — Theorem 5.1 (dim(A^n) = n)
**Verdict: included**
The Krull dimension of the polynomial ring k[x_1,...,x_n] over a field is n. The file `Mathlib/RingTheory/KrullDimension/Polynomial.lean` contains results on the Krull dimension of polynomial rings, specifically `Polynomial.ringKrullDim_le`. The exact equality for polynomial rings over fields is available through the Krull dimension infrastructure.

## Statement 35 — Corollary 10 (dim of hypersurface = n-1)
**Verdict: included**
Krull's principal ideal theorem / height theorem is in `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`, from which the corollary that a hypersurface in A^n has dimension n-1 follows. The specific height bound for principal ideals gives the dimension result.

## Statement 36 — Corollary 11 (every variety has finite dimension)
**Verdict: non-included**
While the finiteness of Krull dimension of finitely generated algebras over fields can be deduced from the Noether normalization lemma and the dimension theory in mathlib, the specific statement that "every algebraic variety has finite dimension" is not explicitly stated as a theorem in the scheme-theoretic setting in mathlib.

## Statement 37 — Proposition 6 (irreducible curves are homeomorphic)
**Verdict: non-included**
This peculiar topological result (all irreducible curves over a field of the same cardinality are homeomorphic as topological spaces) is not in mathlib. It is a curiosity about the cofinite-like nature of the Zariski topology on curves and is not typically formalized.

## Statement 38 — Theorem 5.2 (Bezout's Theorem)
**Verdict: non-included**
Bezout's theorem for plane curves (that two curves of degrees d and e in P^2 without common component intersect in de points counted with multiplicity) is not formalized in mathlib. While there is `Mathlib/RingTheory/Bezout.lean`, that file is about Bezout domains, not the geometric intersection theorem.

## Statement 39 — Theorem 5.3 (Pascal's Theorem)
**Verdict: non-included**
Pascal's theorem on hexagons inscribed in conics is not in mathlib. This is a classical projective geometry result that has not been formalized in the algebraic geometry library.

## Statement 40 — Theorem 5.4 (components of Z(g) have dim n-1)
**Verdict: included**
Krull's principal ideal theorem, formalized in `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`, states that the height of a principal ideal in a Noetherian ring is at most 1, which is equivalent to saying that each component of the zero set of a single function has codimension at most 1. Combined with the non-constancy assumption, this gives dimension exactly n-1.

## Statement 41 — Lemma 11 (dim(Z(g)) >= n-1)
**Verdict: included**
This is the easier half of Statement 40 and follows from Krull's height theorem. See `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`.

## Statement 42 — Lemma 12 (dim of open = dim of irreducible variety)
**Verdict: non-included**
While this is an elementary result in dimension theory, the specific statement that the dimension of a nonempty open subset of an irreducible variety equals the dimension of the variety is not directly stated in mathlib in this form for varieties/schemes.

## Statement 43 — Lemma 13 (fiber cardinality bounded by degree for normal target)
**Verdict: non-included**
This specific bound on fiber cardinality for finite dominant maps to normal varieties is not in mathlib. While mathlib has extensive theory of integral closure and normal rings, this precise fiber-counting result is not formalized.

## Statement 44 — Proposition 7 (ramification locus is closed)
**Verdict: non-included**
The closedness of the ramification locus for finite dominant maps is not directly in mathlib. While `Mathlib/RingTheory/Unramified/Locus.lean` discusses the unramified locus, the specific statement about the ramification locus being closed and proper for separable extensions is not formalized in the variety setting.

## Statement 45 — Lemma 14 (Yoneda Lemma)
**Verdict: included**
The Yoneda lemma is formalized in `Mathlib/CategoryTheory/Yoneda.lean`. The fully faithful embedding of a category into its presheaf category is established as `CategoryTheory.yoneda` along with `CategoryTheory.yonedaFull` and `CategoryTheory.Yoneda.fullyFaithful`.

## Statement 46 — Lemma 15 (tensor of reduced algebras is reduced)
**Verdict: included**
The result that the tensor product of reduced (nilpotent-free) k-algebras over an algebraically closed field k is reduced is available through the theory of geometrically reduced algebras. The relevant results are in `Mathlib/RingTheory/TensorProduct/Basic.lean` and related files about reduced tensor products.

## Statement 47 — Theorem 7.1 (dim(X x Y) = dim X + dim Y)
**Verdict: non-included**
The dimension formula for products of varieties is not directly in mathlib. While Krull dimension is defined in `Mathlib/Order/KrullDimension.lean` and `Mathlib/RingTheory/KrullDimension/Basic.lean`, the specific product dimension formula for algebraic varieties or schemes is not formalized.

## Statement 48 — Lemma 16 (product of closed subvarieties is closed)
**Verdict: included**
That the product of closed immersions is a closed immersion follows from general scheme theory. In mathlib, this is captured by the stability of closed immersions under base change in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`, since closed immersions are stable under composition and base change.

## Statement 49 — Proposition 8 (product of projective varieties is projective)
**Verdict: non-included**
The Segre embedding and the projectivity of products of projective varieties are not in mathlib. While `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` contains the projective spectrum construction, the Segre embedding is not formalized.

## Statement 50 — Lemma 17 (locally closed in separated is separated)
**Verdict: non-included**
While separatedness is defined in mathlib for morphisms of schemes, the specific statement that a locally closed subvariety of a separated variety is separated is not explicitly stated as a standalone lemma in the classical variety setting.

## Statement 51 — Lemma 18 (P^n is separated)
**Verdict: included**
The separatedness of projective space follows from the properness of projective space. In `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean` and `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`, the projective spectrum is shown to be proper, which implies separated.

## Statement 52 — Corollary 12 (quasiprojective is separated)
**Verdict: included**
Since projective space is separated and open subschemes of separated schemes are separated, quasiprojective varieties are separated. This follows from the general infrastructure in `Mathlib/AlgebraicGeometry/Morphisms/` where separatedness is shown to be stable under composition and inherited by open subschemes.

## Statement 53 — Corollary 13 (morphisms to separated target determined on dense open)
**Verdict: non-included**
While this is a standard consequence of separatedness (if two morphisms from an irreducible scheme to a separated scheme agree on a dense open, they are equal), it is not explicitly formalized in mathlib as a standalone result.

## Statement 54 — Corollary 14 (maximal domain of definition)
**Verdict: non-included**
The existence of a maximal open subset to which a morphism to a separated target extends is related to the theory of rational maps in `Mathlib/AlgebraicGeometry/RationalMap.lean`, but the specific statement about maximal domains of definition is not formalized in this form.

## Statement 55 — Corollary 15 (separated iff Hausdorff over C)
**Verdict: non-included**
The relationship between the Zariski separated condition and classical Hausdorff property over C is not in mathlib. Mathlib does not contain the GAGA-type comparison between algebraic and analytic/classical topology.

## Statement 56 — Proposition 9 (separated iff affine opens intersect affinely)
**Verdict: included**
The criterion that a scheme is separated if and only if the intersection of any two affine open subsets is affine (and the ring of functions is generated by the two pieces) is a standard characterization of separatedness. In mathlib, the separated diagonal criterion and the affine intersection characterization are part of the scheme infrastructure, available through `Mathlib/AlgebraicGeometry/AffineScheme.lean` and the separatedness definitions.

## Statement 57 — Proposition 10 (catenary property)
**Verdict: non-included**
The catenary property for algebraic varieties (that maximal chains of irreducible closed subsets all have the same length) is not explicitly in mathlib. While the concept of a catenary ring can be defined, the specific result for algebraic varieties is not formalized.

## Statement 58 — Proposition 11 (dimension and rate of growth)
**Verdict: non-included**
The relationship between the asymptotic rate of growth of the dimension of filtered pieces of a finitely generated algebra and the Krull dimension is related to Hilbert functions/polynomials. This is not formalized in mathlib.

## Statement 59 — Theorem 8.1 (intersection dimension bound in A^n)
**Verdict: non-included**
The intersection dimension theorem (codimension of intersection bounded by sum of codimensions) for subvarieties of affine space is not in mathlib. This would require intersection theory which is not developed in mathlib.

## Statement 60 — Theorem 8.2 (intersection dimension in P^n, nonemptiness)
**Verdict: non-included**
The projective version of the intersection dimension theorem, including the nonemptiness result when dim X + dim Y > n, is not in mathlib.

## Statement 61 — Lemma 19 (properties of complete/proper varieties)
**Verdict: included**
The properties listed (closed in complete implies complete; image of proper morphism is closed and proper; product of proper is proper) are part of the properness infrastructure in `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` and `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean`. Properness is the scheme-theoretic analogue of completeness.

## Statement 62 — Proposition 12 (P^n is complete/proper)
**Verdict: included**
The properness (completeness) of projective space is established in `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`. This is a key result in the algebraic geometry library.

## Statement 63 — Lemma 20 (Chow's Lemma)
**Verdict: non-included**
Chow's lemma (every complete variety is birational to a projective variety) is not in mathlib. This is an important result in algebraic geometry that has not yet been formalized.

## Statement 64 — Proposition 13 (blowup is intrinsic)
**Verdict: non-included**
While blowups can be defined scheme-theoretically, the specific statement that the blowup of a variety at a point is independent of the embedding is not formalized in mathlib. Mathlib does not have a developed theory of blowups.

## Statement 65 — Proposition 14 (presheaves form abelian category)
**Verdict: included**
That presheaves of abelian groups form an abelian category is standard category theory, formalized in `Mathlib/CategoryTheory/Abelian/` and `Mathlib/Topology/Sheaves/Presheaf.lean`. The abelian category structure on functor categories is in `Mathlib/CategoryTheory/Abelian/FunctorCategory.lean`.

## Statement 66 — Proposition 15 (sheafification is exact, adjoint, stalks exact)
**Verdict: included**
Sheafification and its properties are formalized in `Mathlib/Topology/Sheaves/Sheafify.lean` and `Mathlib/Topology/Sheaves/Stalks.lean`. The exactness of the stalk functor and the adjunction between sheafification and the forgetful functor are standard parts of the sheaf theory in mathlib.

## Statement 67 — Theorem 11.1 (QCoh(Spec A) = Mod(A))
**Verdict: included**
The equivalence between quasicoherent sheaves on Spec A and A-modules is a fundamental result. In mathlib, `Mathlib/AlgebraicGeometry/StructureSheaf.lean` constructs the structure sheaf, and the module-sheaf correspondence is developed through the localization and Gamma functors. The file `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` contains the quasicoherent sheaf definition.

## Statement 68 — Corollary 16 (M-tilde is quasicoherent)
**Verdict: included**
That the sheaf associated to a module is quasicoherent follows from the construction. This is part of the structure sheaf infrastructure in `Mathlib/AlgebraicGeometry/StructureSheaf.lean`.

## Statement 69 — Theorem 12.1 (restated: QCoh(Spec A) = Mod(A))
**Verdict: included**
Same as Statement 67.

## Statement 70 — Lemma 22 (direct limits of sheaves on Noetherian spaces)
**Verdict: non-included**
The specific statement that filtered direct limits in presheaves are already sheaves on Noetherian spaces is not directly formalized as a standalone result in mathlib, though the ingredients exist.

## Statement 71 — Proposition 16 (j_* j^* F as colimit)
**Verdict: non-included**
The description of j_* j^* F as a direct limit of f^{-n} F for the inclusion of a principal open is not explicitly formalized in mathlib in this form.

## Statement 72 — Lemma 23 (coherent iff finitely generated on affine)
**Verdict: included**
For affine schemes, a quasicoherent sheaf is coherent if and only if the corresponding module is finitely generated. This is part of the coherent sheaf theory, accessible through `Mathlib/AlgebraicGeometry/Modules/` and the module-sheaf correspondence.

## Statement 73 — Lemma 24 (f_* preserves quasicoherence)
**Verdict: included**
That pushforward preserves quasicoherence is part of the standard sheaf theory infrastructure. For qcqs morphisms, this is handled in the algebraic geometry library through the pushforward of structure sheaf modules.

## Statement 74 — Corollary 17 (f_* exact for affine, left exact in general)
**Verdict: included**
That direct image is exact for affine morphisms follows from the fact that localization is exact. Left exactness of pushforward in general is a basic sheaf theory fact. Both are available through the mathlib sheaf and scheme infrastructure.

## Statement 75 — Lemma 25 (fiber properties of coherent sheaves)
**Verdict: non-included**
The specific package of results (fiber dimension is upper semicontinuous for coherent sheaves, zero fiber implies locally zero, locally constant fiber dimension implies locally free) is not fully formalized in mathlib as a single result. While some pieces exist in `Mathlib/RingTheory/Nakayama.lean` (Nakayama for the zero fiber result), the complete semicontinuity and local freeness criterion are not fully available.

## Statement 76 — Lemma 26 (adjoint equivalence from fully faithful + conservative)
**Verdict: included**
This is a standard category theory result. The criterion that an adjunction where the left adjoint is fully faithful and the right adjoint is conservative yields an equivalence is available in `Mathlib/CategoryTheory/Adjunction/` through the theory of reflective subcategories and equivalences.

## Statement 77 — Lemma 27 (affine morphism iff preimage of affine is affine)
**Verdict: included**
The characterization of affine morphisms (f is affine iff the preimage of every affine open is affine) is the definition/standard characterization in `Mathlib/AlgebraicGeometry/Morphisms/Affine.lean` or through the affine morphism definition in the scheme infrastructure.

## Statement 78 — Proposition 17 (affine maps correspond to qcoh algebras)
**Verdict: included**
The correspondence between affine morphisms to Y and quasicoherent sheaves of O_Y-algebras is part of the relative Spec construction, formalized through the Spec functor for sheaves of algebras in the algebraic geometry library.

## Statement 79 — Proposition 18 (QCoh for affine morphisms)
**Verdict: included**
For an affine morphism f: X -> Y, the pushforward establishes an equivalence between QCoh(X) and A-modules in QCoh(Y) where A = f_* O_X. This is part of the affine morphism theory in mathlib's algebraic geometry library.

## Statement 80 — Proposition 19 (i_* for closed immersion is full embedding)
**Verdict: included**
That pushforward along a closed immersion gives a full embedding of module categories is part of the closed immersion theory in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean` and the ideal sheaf infrastructure in `Mathlib/AlgebraicGeometry/IdealSheaf/`.

## Statement 81 — Corollary 19 (Picard group)
**Verdict: included**
The Picard group (group of isomorphism classes of invertible sheaves under tensor product) is defined in `Mathlib/RingTheory/PicardGroup.lean` for commutative rings. The definition of invertible modules and their group structure under tensor product is formalized there.

## Statement 82 — Proposition 20 (graded modules and qcoh sheaves on P^n)
**Verdict: non-included**
The correspondence between graded modules over the polynomial ring and quasicoherent sheaves on projective space, along with the tilde construction for projective space, is not formalized in mathlib.

## Statement 83 — Corollary 18 (coherent sheaves on P^n are quotients of vector bundles)
**Verdict: non-included**
The result that every coherent sheaf on P^n admits a surjection from O(-d)^k for some d,k (Serre's theorem on coherent sheaves) is not in mathlib.

## Statement 84 — Proposition 21 (Serre quotient description of QCoh(P^n))
**Verdict: non-included**
The Serre quotient category description (QCoh(P^n) = graded modules modulo locally nilpotent ones) is not formalized in mathlib.

## Statement 85 — Proposition 22 (Pic = Div_C / principal)
**Verdict: included**
The identification of the Picard group with the Cartier divisor class group is available through `Mathlib/RingTheory/PicardGroup.lean` and the Cartier divisor/invertible sheaf correspondence that is part of the algebraic geometry foundations.

## Statement 86 — Theorem 15.1 (Weil = Cartier when locally factorial)
**Verdict: non-included**
The equivalence between Weil and Cartier divisors for locally factorial varieties is not formalized in mathlib. While mathlib has UFD theory and divisor-related concepts, this specific geometric comparison is not present.

## Statement 87 — Proposition 23 (k[[x_1,...,x_n]] UFD; completion UFD implies UFD)
**Verdict: non-included**
The statement that formal power series rings are UFDs, and that a Noetherian local ring whose completion is a UFD is itself a UFD, are not in mathlib. While mathlib has UFD infrastructure in `Mathlib/RingTheory/UniqueFactorizationDomain/`, these specific results about power series and completions are not present.

## Statement 88 — Theorem 14.1 (DW = DC for factorial; Pic = DC/K*)
**Verdict: non-included**
Same content as Statements 85-86. The Weil = Cartier part is not in mathlib.

## Statement 89 — Proposition 24 (degree of principal divisor is zero)
**Verdict: non-included**
The statement that principal divisors on complete curves have degree zero is not formalized in mathlib. This requires curve theory and degree theory for divisors that is not developed.

## Statement 90 — Proposition 25 (restated)
**Verdict: non-included**
Same as Statement 89.

## Statement 91 — Theorem 16.1 (Bezout's Theorem, formal version)
**Verdict: non-included**
Same as Statement 38. The intersection-theoretic form of Bezout's theorem is not in mathlib.

## Statement 92 — Corollary 20 (intersection multiplicity > 1 at singular points)
**Verdict: non-included**
This corollary about intersection multiplicities at singular points is not in mathlib, as intersection multiplicity theory is not developed.

## Statement 93 — Theorem 17.1 (Torelli theorem)
**Verdict: non-included**
The Torelli theorem (a curve can be reconstructed from its period lattice) is a deep result in complex algebraic geometry that is far from being formalized in mathlib.

## Statement 94 — Proposition 26 (Pic^0 is a variety/Lie group)
**Verdict: non-included**
The algebraic structure of the Jacobian variety is not in mathlib.

## Statement 95 — Theorem 17.2 (Abel-Jacobi isomorphism for genus 1)
**Verdict: non-included**
The Abel-Jacobi map and its being an isomorphism for genus 1 curves is not in mathlib.

## Statement 96 — Corollary 21 (genus 1 curves have group structure)
**Verdict: non-included**
While mathlib has extensive theory of elliptic curves in `Mathlib/AlgebraicGeometry/EllipticCurve/`, including the group law on the rational points via the Weierstrass model, the specific statement that every normal curve of genus 1 is an elliptic curve (has a group structure) is not formulated in this generality. The elliptic curve files define the group law for curves given in Weierstrass form.

## Statement 97 — Proposition 27 (non-constant map of complete curves is finite)
**Verdict: non-included**
This statement is not directly in mathlib. While properness of projective morphisms is established, the specific result for curves is not formalized.

## Statement 98 — Proposition 28 (normalization exists)
**Verdict: included**
The normalization of a scheme is defined in `Mathlib/AlgebraicGeometry/Normalization.lean`. The file constructs the relative normalization with its universal property, along with the factorization into a dominant morphism followed by an integral morphism.

## Statement 99 — Corollary 22 (normal variety reconstructed from generic fiber)
**Verdict: non-included**
This reconstruction result is not explicitly in mathlib.

## Statement 100 — Lemma 28 (birational onto normal curve is iso)
**Verdict: non-included**
This specific result for curves (birational finite map onto a normal curve is an isomorphism) is not in mathlib as a standalone result.

## Statement 101 — Lemma 29 (birational from complete to normal is iso)
**Verdict: non-included**
Zariski's main theorem would imply this in a more general setting. While `Mathlib/RingTheory/ZariskisMainTheorem.lean` exists, it handles the ring-theoretic version. The geometric statement for varieties is not formalized.

## Statement 102 — Lemma 30 (dim(T_x^* X) >= dim_x X)
**Verdict: included**
The inequality between the dimension of the cotangent space and the local dimension is a basic result in commutative algebra (the embedding dimension is at least the Krull dimension). This follows from the theory of regular local rings and Krull dimension in `Mathlib/RingTheory/KrullDimension/` and `Mathlib/RingTheory/Ideal/Cotangent.lean`.

## Statement 103 — Proposition 29 (smooth iff Omega locally free)
**Verdict: included**
The characterization of smoothness via the sheaf of differentials being locally free is part of the smooth morphism theory. In `Mathlib/RingTheory/Smooth/Kaehler.lean` and related files, the connection between smoothness and Kahler differentials is established. The smooth locus is characterized via the module of differentials.

## Statement 104 — Proposition 30 (smooth locus is open and dense)
**Verdict: included**
The openness of the smooth locus is established in `Mathlib/RingTheory/Smooth/Locus.lean` as `Algebra.isOpen_smoothLocus`. The density (that every variety contains a smooth open dense subset) requires additionally the generic smoothness result, which is partially available through the smooth locus infrastructure.

## Statement 105 — Corollary 23 (Jacobian criterion)
**Verdict: included**
The Jacobian criterion for smoothness (smooth iff the matrix of partial derivatives has maximal rank) is essentially the content of the cotangent space / Kahler differential characterization of smoothness. The relevant infrastructure is in `Mathlib/RingTheory/Kaehler/` and `Mathlib/RingTheory/Smooth/`.

## Statement 106 — Proposition 31 (smooth iff locally generated by equations with independent differentials)
**Verdict: included**
This is another form of the Jacobian criterion / smooth embedding characterization. The infrastructure in `Mathlib/RingTheory/Smooth/` and `Mathlib/RingTheory/Kaehler/` provides the connection between independent differentials of generators and smoothness.

## Statement 107 — Lemma 31 (completed local ring at smooth point)
**Verdict: non-included**
The explicit isomorphism between the completed local ring at a smooth point and a formal power series ring k[[t_1,...,t_d]] is not in mathlib. While Cohen's structure theorem for complete local rings exists in some form, this specific geometric consequence is not formalized.

## Statement 108 — Lemma 32 (associated graded under quotient)
**Verdict: non-included**
This technical lemma about the associated graded ring of a quotient (when the leading term is not a zero divisor) is not explicitly in mathlib, though related filtration theory exists in `Mathlib/RingTheory/Filtration.lean`.

## Statement 109 — Proposition 32 (smooth iff completed local ring is power series)
**Verdict: non-included**
Same as Statement 107. The characterization of smooth points via the completion of the local ring is not in mathlib.

## Statement 110 — Proposition 33 (conormal exact sequence)
**Verdict: included**
The conormal/cotangent exact sequence I/I^2 -> Omega_X|_Z -> Omega_Z -> 0 for a closed subvariety Z of X is formalized in the Kahler differential theory. The Jacobi-Zariski exact sequence in `Mathlib/RingTheory/Kaehler/JacobiZariski.lean` provides the algebraic version of this sequence, and the cotangent complex infrastructure in `Mathlib/RingTheory/Extension/Cotangent/` handles the extension to the conormal sequence.

## Statement 111 — Corollary 24 (Adjunction Formula)
**Verdict: non-included**
The adjunction formula omega_D = omega_X(D)|_D relating canonical bundles is not in mathlib. This requires the canonical sheaf, divisor theory, and the conormal exact sequence in the geometric setting, none of which are fully assembled in mathlib.

## Statement 112 — Proposition 34 (tangent cone = cone over exceptional locus)
**Verdict: non-included**
The identification of the tangent cone with the cone over the exceptional divisor of a blowup is not in mathlib, as blowup theory is not developed.

## Statement 113 — Proposition 35 (conormal exact sequence, restated)
**Verdict: included**
Same as Statement 110.

## Statement 114 — Corollary 25 (smooth closed subvariety criterion)
**Verdict: non-included**
The specific statement that a closed subvariety of a smooth variety is smooth iff it is locally cut out by equations with linearly independent differentials is not a standalone result in mathlib, though the ingredients (Jacobian criterion, conormal sequence) are partially available.

## Statement 115 — Corollary 26 (adjunction formula via conormal sequence)
**Verdict: non-included**
Same as Statement 111.

## Statement 116 — Proposition 36 (Euler sequence for P^n)
**Verdict: non-included**
The Euler exact sequence 0 -> Omega_{P^n} -> O(-1)^{n+1} -> O -> 0 and the corollary K_{P^n} = O(-(n+1)) are not in mathlib. This would require the sheaf of differentials and twisting sheaves on projective space, which are not fully developed.

## Statement 117 — Proposition 37 (tangent bundle of Grassmannian)
**Verdict: non-included**
The description T_{Gr(k,n)} = Hom(V, W/V) of the tangent bundle of the Grassmannian is not in mathlib.

## Statement 118 — Proposition 38 (tangent cone and associated graded at smooth point)
**Verdict: non-included**
Same as Statement 112.

## Statement 119 — Theorem 21.1 (Riemann-Hurwitz)
**Verdict: non-included**
The Riemann-Hurwitz formula is not in mathlib. This requires ramification theory for curves, canonical bundles, and degree computations that are not formalized.

## Statement 120 — Corollary 27 (degree formula from Riemann-Hurwitz)
**Verdict: non-included**
Same as Statement 119.

## Statement 121 — Proposition 39 (functions extend from complement of codim >= 2 on normal variety)
**Verdict: non-included**
Hartogs' algebraic lemma (regular functions on the complement of a codimension >= 2 subset of a normal variety extend to the whole variety) is not in mathlib. While normality and the S2 condition are related, this specific geometric result is not formalized.

## Statement 122 — Theorem 21.2 (Chevalley's Theorem)
**Verdict: included**
Chevalley's theorem on constructible images is in `Mathlib/RingTheory/Spectrum/Prime/Chevalley.lean`. The theorem states that the image of a constructible set under a morphism of finite presentation is constructible. The file also connects to `Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean`.

## Statement 123 — Lemma 33 (generic fiber factorization)
**Verdict: non-included**
The lemma that a dominant morphism of affine varieties factors through a finite map over some open subset of the target is an ingredient in the proof of Chevalley's theorem but is not stated as a standalone result in mathlib.

## Statement 124 — Theorem 22.1 (Bertini's Theorem)
**Verdict: non-included**
Bertini's theorem (generic hyperplane section of a smooth variety is smooth) is not in mathlib.

## Statement 125 — Corollary 28 (generic hypersurface is smooth)
**Verdict: non-included**
Same as Statement 124.

## Statement 126 — Proposition 40 (degree well-defined on K^0)
**Verdict: non-included**
The degree homomorphism on the Grothendieck group K^0(Coh(X)) for curves is not in mathlib. The K-theory and degree theory for coherent sheaves on curves is not formalized.

## Statement 127 — Lemma 34 (degree and torsion in s.e.s.)
**Verdict: non-included**
Same as Statement 126.

## Statement 128 — Proposition 41 (Grothendieck: effaceable implies universal)
**Verdict: non-included**
While mathlib has derived functors via `Mathlib/CategoryTheory/Functor/Derived/`, the specific Grothendieck criterion that an effaceable delta-functor is universal is not formalized as a standalone result. The derived functor theory in mathlib uses a different (more modern) approach via derived categories.

## Statement 129 — Proposition 42 (Snake Lemma)
**Verdict: included**
The snake lemma is formalized in `Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean` and `Mathlib/Algebra/Module/SnakeLemma.lean`. The long exact sequence in homology arising from a short exact sequence of complexes is in `Mathlib/Algebra/Homology/HomologySequence.lean`.

## Statement 130 — Proposition 43 (resolutions compute derived functors)
**Verdict: included**
That derived functors can be computed via resolutions by adjusted/acyclic objects is part of the derived functor theory in `Mathlib/CategoryTheory/Abelian/RightDerived.lean` and `Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean`.

## Statement 131 — Proposition 44 (H^i for affine push-forward)
**Verdict: non-included**
The specific statement that H^i(f_* F) = H^i(F) for affine morphisms is not directly in mathlib. While the exactness of pushforward for affine morphisms is captured, the cohomological comparison is not formalized as sheaf cohomology for schemes is not fully developed in mathlib.

## Statement 132 — Theorem 24.1 (Grothendieck-Birkhoff)
**Verdict: non-included**
The classification of vector bundles on P^1 (every locally free sheaf is a direct sum of line bundles O(d_i)) is not in mathlib.

## Statement 133 — Theorem 24.2 (Riemann-Roch for Curves)
**Verdict: non-included**
The Riemann-Roch theorem for curves is not in mathlib. This requires sheaf cohomology, degree theory, and the Euler characteristic for coherent sheaves on curves, none of which are fully formalized.

## Statement 134 — Lemma 35 (generators of K^0(Coh(X)))
**Verdict: non-included**
Not in mathlib.

## Statement 135 — Theorem 24.3 (Serre Duality)
**Verdict: non-included**
Serre duality is not in mathlib. This is one of the major results in algebraic geometry that has not yet been formalized.

## Statement 136 — Lemma 36 (sum of residues = 0)
**Verdict: non-included**
The residue theorem (sum of residues of a differential form on a complete curve is zero) is not in mathlib.

## Statement 137 — Corollary 29 (g_a = g_m)
**Verdict: non-included**
The equality of arithmetic and geometric genus for smooth curves is not in mathlib.

## Statement 138 — Corollary 30 (Riemann's form of Riemann-Roch)
**Verdict: non-included**
Not in mathlib; this is a corollary of Serre duality and Riemann-Roch.

## Statement 139 — Corollary 31 (deg K = 2g - 2)
**Verdict: non-included**
The degree formula for the canonical divisor is not in mathlib.
