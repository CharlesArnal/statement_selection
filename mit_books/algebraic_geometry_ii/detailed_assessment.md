# Detailed Assessment: 18.726 Algebraic Geometry II Statements in Mathlib

## Statement 1 (Basis Lemma) — included
The sheaf-on-basis extension result is implemented in mathlib's sheaf infrastructure. The structure sheaf on `PrimeSpectrum R` in `Mathlib/AlgebraicGeometry/StructureSheaf.lean` is constructed precisely by defining data on the basis of distinguished opens and extending. The sheaf-on-basis machinery is available in `Mathlib/Topology/Sheaves/Presheaf.lean` and `Mathlib/Topology/Sheaves/Sheaf.lean`.

## Statement 2 (Gluing Corollary) — included
Gluing sheaves from compatible data on an open cover is available in mathlib. The general gluing machinery for sheaves is in `Mathlib/Topology/Sheaves/` and for schemes specifically in `Mathlib/AlgebraicGeometry/Gluing.lean` and `Mathlib/AlgebraicGeometry/GluingOneHypercover.lean`. The cocycle-condition-based gluing is a core part of the sheaf formalism.

## Statement 3 (Stalks and Morphisms Lemma) — included
The relationship between stalk-wise properties and section-wise properties of sheaf morphisms is established in `Mathlib/Topology/Sheaves/Stalks.lean`. Key lemmas relating injectivity/surjectivity/bijectivity on stalks to the same on sections are present there.

## Statement 4 (Sheafification Proposition) — included
Sheafification as a left adjoint to the forgetful functor is implemented in `Mathlib/Topology/Sheaves/Sheafify.lean` and the general site-theoretic version in `Mathlib/CategoryTheory/Sites/Sheafification.lean`.

## Statement 5 (Inverse and Direct Image Adjunction) — included
The adjunction between inverse image and direct image for sheaves is in `Mathlib/Topology/Sheaves/Functors.lean`. This is fundamental to the sheaf theory infrastructure in mathlib.

## Statement 6 (Five Lemma) — included
The five lemma for abelian categories is proved in `Mathlib/CategoryTheory/Abelian/DiagramLemmas/` and can also be derived from the snake lemma in `Mathlib/Algebra/Module/SnakeLemma.lean`.

## Statement 7 (Snake Lemma) — included
The snake lemma is proved in `Mathlib/Algebra/Module/SnakeLemma.lean` (module version with `SnakeLemma.delta`) and `Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean` (general abelian category version). The exactness of the six-term sequence is established.

## Statement 8 (Short Five Lemma) — included
The short five lemma follows from the snake lemma and is available in the abelian category API in `Mathlib/CategoryTheory/Abelian/`.

## Statement 9 (Adjoint Functors and Exactness) — included
The fact that left adjoints are right exact and right adjoints are left exact is in `Mathlib/CategoryTheory/Adjunction/Limits.lean` via the preservation of colimits by left adjoints and limits by right adjoints.

## Statement 10 (Stalks of Kernel/Image/Cokernel) — included
The commutation of stalk formation with kernel, image, and cokernel is in `Mathlib/Topology/Sheaves/Stalks.lean`, following from the fact that stalk formation is a filtered colimit.

## Statement 11 (Global Sections Left Exact) — included
The left exactness of the global sections functor follows from the general categorical fact that right adjoints preserve limits, implicit in `Mathlib/Topology/Sheaves/Sheaf.lean` and the presheaf/sheaf infrastructure.

## Statement 12 (Quasicompactness of Distinguished Opens) — included
The quasicompactness of distinguished opens D(f) in Spec(R) is proved in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` via `isCompact_basicOpen` or equivalent.

## Statement 13 (Distinguished Open Inclusion Lemma) — included
The characterization D(f) subset D(g) iff f is in the radical of (g) is established in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` as part of the basic topology of prime spectra.

## Statement 14 (Fundamental Theorem of Affine Schemes, Part 1) — included
The structure sheaf on Spec R is constructed in `Mathlib/AlgebraicGeometry/StructureSheaf.lean`. The sheaf axiom for the presheaf on distinguished opens is the core content of that file.

## Statement 15 (Fundamental Theorem of Affine Schemes, Part 2) — included
The construction of the quasicoherent sheaf tilde{M} is in `Mathlib/AlgebraicGeometry/StructureSheaf.lean` and `Mathlib/AlgebraicGeometry/Modules/`.

## Statement 16 (Morphisms of Affine Schemes) — included
The bijection between morphisms Spec(A) -> Spec(B) and ring homomorphisms B -> A is established in `Mathlib/AlgebraicGeometry/Spec.lean` and `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`. This is the special case of Statement 17.

## Statement 17 (Gamma-Spec Adjunction) — included
The Gamma-Spec adjunction is a central result in `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`, establishing the adjunction between Spec and global sections as functors between rings and locally ringed spaces.

## Statement 18 (Fibre Product Open Subscheme Lemma) — included
The compatibility of fibre products with passage to open subschemes is part of the pullback infrastructure in `Mathlib/AlgebraicGeometry/Pullbacks.lean` and `Mathlib/AlgebraicGeometry/Limits.lean`. The categorical machinery for limits in the category of schemes handles this.

## Statement 19 (Existence of Fibre Products) — included
The existence of all fibre products in the category of schemes is proved in `Mathlib/AlgebraicGeometry/Pullbacks.lean` (for pullbacks, which is the same as fibre products). The construction via tensor products for affine schemes and gluing for the general case is implemented.

## Statement 20 (Quasicoherent Sheaves on Affine Schemes) — included
The equivalence between quasicoherent sheaves on Spec(R) and R-modules (the third fundamental theorem) is in `Mathlib/AlgebraicGeometry/Modules/` and implicitly in the structure sheaf construction. The tilde functor and its quasi-inverse via global sections are implemented.

## Statement 21 (Separatedness and Diagonal) — included
The characterization of separatedness via the diagonal being a closed immersion is the definition in `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean`. The equivalence with the image of the diagonal being closed is part of this infrastructure.

## Statement 22 (Affine Intersection Theorem) — included
The fact that the intersection of two open affine subschemes in a separated scheme is affine is established in `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` and related files. This is a key consequence of separatedness.

## Statement 23 (Separatedness Stable under Base Change) — included
The stability of separatedness under base change is in `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean`, where separatedness is shown to be a morphism property stable under composition and base change.

## Statement 24 (Composition of Closed Immersions) — included
The stability of closed immersions under composition is in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`.

## Statement 25 (Closed Immersion is Separated) — included
The fact that affine morphisms (and hence closed immersions) are separated is in `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` and `Mathlib/AlgebraicGeometry/QuasiAffine.lean`.

## Statement 26 (Varieties and Schemes Equivalence) — non-included
The equivalence of abstract algebraic varieties with reduced schemes locally of finite type over an algebraically closed field is not formalized in mathlib. Mathlib does not have a separate formalization of classical varieties to compare with.

## Statement 27 (Properness of Projective Space) — included
The properness of projective space is proved in `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`.

## Statement 28 (Closed Immersion is Proper) — included
The fact that closed immersions are proper is in `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`, since closed immersions are universally closed and of finite type.

## Statement 29 (Projective Morphism is Proper Corollary) — included
The properness of projective morphisms (compositions of closed immersions with projective space projections) follows from the composition stability of proper morphisms in `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` combined with Statement 27 and 28.

## Statement 30 (Twisting Sheaves on Proj) — non-included
While Proj is constructed in `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/`, the twisting sheaves O(n) and their tensor product properties are not fully formalized. The `ProjectiveSpectrum/Scheme.lean` file constructs the scheme but the line bundle theory is incomplete.

## Statement 31 (Quasicoherent Sheaves on Proj) — non-included
The theory of quasicoherent sheaves on Proj and the tilde construction for graded modules is not formalized in mathlib. The Proj construction exists but the sheaf-module correspondence is not developed.

## Statement 32 (Proj and Projective Space Isomorphism) — included
The identification of Proj A[x_0,...,x_n] with P^n_A is part of the projective spectrum construction in `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`.

## Statement 33 (Closed Immersions into Projective Space) — non-included
The characterization of closed subschemes of projective space via homogeneous ideals is not fully formalized. While the Proj construction handles homogeneous ideals, the correspondence between closed immersions and saturated homogeneous ideals is not established.

## Statement 34 (Equivalent Conditions for Projective Closed Subscheme) — non-included
The conditions characterizing when a closed subscheme of Proj is empty (related to the irrelevant ideal) are not formalized.

## Statement 35 (Projective iff Proper plus Very Ample) — non-included
The characterization of projective morphisms as proper morphisms with a very ample sheaf is not formalized. Ampleness and very ample sheaves are not defined in mathlib's algebraic geometry library.

## Statement 36 (Blowup and Locally Principal Ideal) — non-included
Blowups are not formalized in mathlib. While ideal sheaves are available in `Mathlib/AlgebraicGeometry/IdealSheaf/`, the blowup construction (relative Proj of the Rees algebra) is absent.

## Statement 37 (Chow's Lemma) — non-included
Chow's lemma is not formalized in mathlib. This deep result requires the blowup construction and quasiprojective schemes, neither of which is available.

## Statement 38 (Reduced Scheme Characterization) — included
The equivalence of reducedness conditions for schemes is in `Mathlib/AlgebraicGeometry/Properties.lean`, where `IsReduced` is defined and shown to be equivalent to having reduced local rings.

## Statement 39 (Connected Scheme Characterization) — included
The characterization of connected schemes via idempotent elements is available through the topological infrastructure. Connected components and the relationship with idempotents in global sections follow from general ring-theoretic facts in `Mathlib/RingTheory/` combined with the Properties file.

## Statement 40 (Irreducible Affine Scheme Characterization) — included
The characterization of irreducible affine schemes (nilradical is prime) is in `Mathlib/AlgebraicGeometry/Properties.lean`, using results about prime spectra from `Mathlib/RingTheory/Spectrum/Prime/`.

## Statement 41 (Unique Generic Point) — included
The existence of a unique generic point for irreducible schemes is in `Mathlib/AlgebraicGeometry/Properties.lean` and uses `Mathlib/Topology/IrreducibleSpace.lean` which establishes the existence of generic points for irreducible sober spaces.

## Statement 42 (Integral Scheme Characterization) — included
The characterization of integral schemes (integral domain iff connected + all local rings are domains) is in `Mathlib/AlgebraicGeometry/Properties.lean`.

## Statement 43 (Normal Affine Scheme Characterization) — included
The characterization of normal affine schemes is in `Mathlib/AlgebraicGeometry/Normalization.lean` and `Mathlib/AlgebraicGeometry/Properties.lean`, using the fact that normality of a domain is equivalent to normality of all localizations.

## Statement 44 (Existence of Normalization) — included
The existence of normalization for integral schemes is in `Mathlib/AlgebraicGeometry/Normalization.lean`.

## Statement 45 (Flat Module on Affine Scheme) — included
The equivalence between flatness of a module and flatness of the associated sheaf on an affine scheme is in `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`, using the standard commutative algebra fact that flatness is local on localizations from `Mathlib/RingTheory/Flat/`.

## Statement 46 (Flat Morphism of Affine Schemes) — included
The characterization of flat morphisms of affine schemes via flat ring maps is in `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`.

## Statement 47 (Flat Locally of Finite Presentation is Universally Open) — included
The result that flat + locally of finite presentation implies universally open is in `Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean` and `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`.

## Statement 48 (Generic Flatness) — non-included
The generic flatness theorem (EGA IV) stating that the flat locus of a module on a morphism of finite type over a locally noetherian base is open is not formalized in mathlib. While flatness is well-developed, the openness of the flat locus is a deep result that is absent.

## Statement 49 (Faithfully Flat Descent) — included
Faithfully flat descent for quasicoherent sheaves is in `Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`. The descent framework is set up using the categorical machinery.

## Statement 50 (Descent of Finite Type) — included
The descent of the finite type property along faithfully flat quasicompact morphisms is available in `Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`, which establishes descent for various morphism properties.

## Statement 51 (Formally Unramified iff Omega Zero) — included
The characterization of formally unramified morphisms via vanishing of the sheaf of differentials is in `Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean`. Kahler differentials are defined in `Mathlib/RingTheory/Kaehler/`.

## Statement 52 (Etale iff Flat and Unramified) — included
The characterization of etale morphisms as flat + unramified is in `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean`.

## Statement 53 (Smooth iff Flat and Geometrically Regular Fibres) — non-included
While smooth morphisms are defined in `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`, the full characterization via flat + geometrically regular fibers is not completely established. The definition uses a different (but equivalent for lfp morphisms) formulation.

## Statement 54 (DVR Characterization) — included
The equivalence of regular, normal, and DVR for noetherian local rings of dimension 1 is a classical result from commutative algebra available in `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` and `Mathlib/RingTheory/KrullDimension/Regular.lean`.

## Statement 55 (Cartier and Weil Divisors for Locally Factorial Schemes) — non-included
The isomorphism between Cartier and Weil divisors for locally factorial (UFD local rings) schemes is not formalized. Mathlib does not have a formal theory of Weil or Cartier divisors on schemes.

## Statement 56 (Riemann-Roch for Curves) — non-included
The Riemann-Roch theorem for algebraic curves is not formalized in mathlib. This requires sheaf cohomology on curves, the canonical divisor, and the genus, none of which are developed in the scheme-theoretic context.

## Statement 57 (Closed Immersion from High Degree Divisors) — non-included
The embedding theorem for high-degree divisors on curves requires Riemann-Roch which is not formalized.

## Statement 58 (l(D) Bounds) — non-included
The dimension bounds for sections of line bundles on curves require the divisor theory and cohomology infrastructure that is not in mathlib.

## Statement 59 (Canonical Embedding and Hyperelliptic Curves) — non-included
The characterization of when the canonical embedding is a closed immersion (iff not hyperelliptic) is not formalized. This requires Riemann-Roch and the canonical divisor theory.

## Statement 60 (Riemann-Hurwitz Formula, Divisor Form) — non-included
The Riemann-Hurwitz formula relating canonical divisors via the ramification divisor is not formalized. While Kahler differentials exist in `Mathlib/RingTheory/Kaehler/`, the application to curves and ramification theory is absent.

## Statement 61 (Riemann-Hurwitz Formula, Genus Form) — non-included
The genus formula 2g(X)-2 = deg(f)(2g(Y)-2) + deg(R) is not formalized, as it requires Statement 60 and Riemann-Roch.

## Statement 62 (Finite Generation of Canonical Ring, BCHM) — non-included
The Birkar-Cascini-Hacon-McKernan theorem on finite generation of the canonical ring is a Fields-medal-level result that is not in mathlib. This is extremely far from formalization.

## Statement 63 (Universality of Effaceable Cohomological Functors) — non-included
The universality theorem for effaceable cohomological delta-functors is not formalized. While derived functor infrastructure exists in `Mathlib/CategoryTheory/Functor/Derived/`, the specific effaceability-based universality criterion is not established as such.

## Statement 64 (Acyclic Resolution Theorem) — non-included
The theorem that acyclic resolutions compute derived functors is not formalized in the general categorical setting in mathlib.

## Statement 65 (Injectives are Acyclic for Universal Functors) — non-included
The acyclicity of injective objects for universal delta-functors is implicit in the derived functor construction but not stated separately.

## Statement 66 (Derived Functors from Enough Injectives) — included
The construction of derived functors when enough injectives exist is in `Mathlib/CategoryTheory/Functor/Derived/` and `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean`.

## Statement 67 (Flat Module Characterization) — included
The characterization of flat modules via Tor_1 vanishing and preservation of injectivity is in `Mathlib/RingTheory/Flat/Basic.lean` and `Mathlib/Algebra/Homology/Tor/`.

## Statement 68 (Short Exact Sequence with Flat Term) — included
The fact that tensoring a short exact sequence by a module preserves exactness when the third term is flat follows from the definition of flatness in `Mathlib/RingTheory/Flat/Basic.lean`.

## Statement 69 (Ab Has Enough Injectives) — included
The fact that Ab (or more generally, module categories) has enough injectives is in `Mathlib/Algebra/Category/ModuleCat/EnoughInjectives.lean`.

## Statement 70 (Sheaves of Modules Have Enough Injectives) — included
The category of sheaves of O_X-modules having enough injectives is addressed via the Grothendieck abelian category framework in `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean`.

## Statement 71 (Grothendieck's Theorem on Enough Injectives) — included
Grothendieck's theorem that abelian categories with a generator, exact filtered colimits, and arbitrary products have enough injectives is in `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean`.

## Statement 72 (Injective Iff Extension Property from Generator) — non-included
The characterization of injective objects via the extension property from monomorphisms into a generator is not explicitly formalized as a standalone theorem.

## Statement 73 (Injective Implies Flasque) — non-included
The implication that injective sheaves are flasque requires the notion of flasque sheaf which is not in mathlib. A grep for "flasque" and "flabby" returns no results.

## Statement 74 (Flasque Sheaves Acyclic) — non-included
The acyclicity of flasque sheaves requires both the flasque notion and sheaf cohomology on topological spaces, neither of which is in mathlib.

## Statement 75 (Singular and Sheaf Cohomology Agree) — non-included
The comparison between singular and sheaf cohomology for locally contractible spaces is not in mathlib. Singular cohomology is not formalized.

## Statement 76 (Homotopy Equivalence Lemma for Singular Cochains) — non-included
This algebraic topology lemma about cochains is not formalized in mathlib.

## Statement 77 (Cech Cohomology Vanishes for Flasque Sheaves) — non-included
Since neither flasque sheaves nor Cech cohomology of sheaves are formalized, this is absent.

## Statement 78 (Cech Cohomology on Paracompact Spaces) — non-included
Cech cohomology comparison on paracompact spaces is not formalized. Neither Cech cohomology nor the comparison theorem is available.

## Statement 79 (Leray's Theorem) — non-included
Leray's theorem requires both Cech and sheaf cohomology which are not formalized.

## Statement 80 (Vanishing of Quasicoherent Cohomology on Affine Schemes) — non-included
This fundamental result (H^i(Spec A, tilde{M}) = 0 for i > 0) is not in mathlib because sheaf cohomology on schemes is not formalized. While the affine scheme infrastructure is extensive, cohomological vanishing is absent.

## Statement 81 (Global Sections Exact for Quasicoherent Sheaves on Affines) — non-included
The exactness of global sections for quasicoherent sheaves on affine schemes requires the cohomological vanishing of Statement 80.

## Statement 82 (Cech Cohomology for Affine Covers) — non-included
Cech cohomology computation on affine covers requires both Cech and sheaf cohomology.

## Statement 83 (Cech Cohomology on Distinguished Open Covers) — non-included
The Cech cohomology computation for distinguished open covers is the computational heart of affine acyclicity but is not formalized.

## Statement 84 (Cartan's Theorem) — non-included
Cartan's theorem comparing Cech and sheaf cohomology using a nice basis is not in mathlib.

## Statement 85 (Cech^1 Vanishing Implies Surjectivity) — non-included
This lemma requires Cech cohomology which is not formalized.

## Statement 86 (Finitely Generated Module iff Finitely Generated Sheaf) — non-included
The equivalence between finite generation of a module and finite generation of the associated sheaf is not explicitly stated in mathlib. The concept of finitely generated sheaf in the scheme-theoretic sense is not fully developed.

## Statement 87 (Cohomology of Closed Immersion) — non-included
The isomorphism H^i(Z, F) = H^i(X, f_*F) for closed immersions requires sheaf cohomology which is not formalized.

## Statement 88 (Cohomology Commutes with Direct Limits on Noetherian Spaces) — non-included
This requires sheaf cohomology which is not in mathlib.

## Statement 89 (Serre's Computation of Cohomology of Projective Space) — non-included
Serre's explicit computation of H^i(P^r_A, O(n)) is not in mathlib. Projective space is constructed but cohomology computations are absent.

## Statement 90 (Serre's Generation by Global Sections) — non-included
The theorem that F(n) is generated by global sections for n large requires the twisting sheaf and cohomological machinery.

## Statement 91 (Serre's Surjection Corollary) — non-included
The existence of a surjection from twisting sheaves depends on Statement 90.

## Statement 92 (Serre's Finiteness Theorem) — non-included
Serre's finiteness and vanishing for cohomology on projective schemes is not formalized.

## Statement 93 (Euler Characteristic Additivity) — non-included
The Euler characteristic and its additivity require sheaf cohomology.

## Statement 94 (Existence of Hilbert Polynomial) — non-included
While `Mathlib/RingTheory/Polynomial/HilbertPoly.lean` exists for ring-theoretic Hilbert polynomials, the geometric version (chi(X, F(n)) is polynomial in n) is not formalized.

## Statement 95 (Flatness and Constancy of Hilbert Polynomials) — non-included
The numerical criterion for flatness via Hilbert polynomials is not in mathlib.

## Statement 96 (Existence of Hilbert Scheme) — non-included
The representability of the Hilbert functor is a deep result not in mathlib.

## Statement 97 (Hilbert Polynomial and Dimension/Degree) — non-included
The relationship between Hilbert polynomial, dimension, and degree is not formalized.

## Statement 98 (Spectral Sequence Convergence) — non-included
Spectral sequences are not fully formalized in mathlib. Only partial infrastructure exists in `Mathlib/CategoryTheory/Triangulated/SpectralObject.lean`.

## Statement 99 (Cartan's Theorem via Spectral Sequences) — non-included
This spectral sequence approach to Cartan's theorem is not formalized.

## Statement 100 (Coherent Sheaves on Noetherian Affine Schemes) — non-included
The equivalence between coherent sheaves, finitely generated quasicoherent sheaves, and finitely generated modules on noetherian affine schemes is not fully formalized. While noetherian schemes are defined in `Mathlib/AlgebraicGeometry/Noetherian.lean`, the coherent sheaf characterization is not established.

## Statement 101 (Cartan's Lemma on Coherence of Analytification Pullback) — non-included
Complex analytic geometry and analytification are not in mathlib. Searched for "analytification" and "GAGA" with no results.

## Statement 102 (Flatness of Analytification) — non-included
Requires complex analytic geometry which is absent from mathlib.

## Statement 103 (GAGA, Part 1) — non-included
The GAGA cohomology comparison theorem is not in mathlib. Complex analytic spaces are not formalized.

## Statement 104 (Cartan's Theorem B for Stein Manifolds) — non-included
Cartan's theorem B belongs to complex analytic geometry which is absent from mathlib.

## Statement 105 (Cech Computation on Analytic Projective Space) — non-included
Requires complex analytic geometry not present in mathlib.

## Statement 106 (GAGA, Part 2) — non-included
The GAGA morphism comparison is not in mathlib.

## Statement 107 (Hom Base Change for Flat Algebras) — non-included
The Hom-tensor base change for flat algebras over noetherian rings was not found as an explicit theorem in mathlib. While flatness and Hom-tensor adjunction exist separately, this specific result was not located in `Mathlib/RingTheory/Flat/` or `Mathlib/Algebra/Module/`.

## Statement 108 (Cartan-Serre Finiteness) — non-included
Requires complex analytic geometry not present in mathlib.

## Statement 109 (GAGA, Part 3) — non-included
The essential surjectivity part of GAGA is not in mathlib.

## Statement 110 (GAGA Lemma on Local Generation) — non-included
This technical GAGA lemma is not formalized.

## Statement 111 (GAGA Corollary on Uniform Generation) — non-included
This GAGA corollary is not formalized.

## Statement 112 (Analytification Functor Theorem) — non-included
The analytification functor requires complex analytic spaces which are not in mathlib.

## Statement 113 (GAGA for Projective Schemes) — non-included
The full GAGA theorem for projective schemes is not in mathlib.

## Statement 114 (GAGA for Hodge Cohomology) — non-included
The comparison of algebraic and analytic Hodge cohomology is not formalized. Kahler differentials exist in `Mathlib/RingTheory/Kaehler/` but the cohomological comparison is absent.

## Statement 115 (Grothendieck's Theorem on Finite Covers) — non-included
The correspondence between finite covering spaces and finite etale covers requires GAGA and the etale fundamental group, neither of which is formalized.

## Statement 116 (Profinite Completion Independence) — non-included
This result about the profinite completion of the fundamental group requires the etale fundamental group which is not in mathlib.

## Statement 117 (Separatedness and Analytification) — non-included
Requires analytification which is not in mathlib. Separatedness is in `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` but the analytic comparison is absent.

## Statement 118 (Injective Restriction to Opens) — included
The restriction of an injective sheaf to an open subset remaining injective follows from the adjunction between extension by zero and restriction, available through the categorical injective object framework in `Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean`.

## Statement 119 (Ext as Cohomological Functor) — non-included
While Ext groups exist in `Mathlib/Algebra/Homology/DerivedCategory/Ext/`, the specific statement about sheaf Ext being a cohomological functor on the opposite category is not formalized for ringed spaces.

## Statement 120 (Ext via Locally Free Resolutions) — non-included
The computation of sheaf Ext via locally free resolutions is not formalized for sheaves on ringed spaces.

## Statement 121 (Coherence of Ext on Projective Space) — non-included
Coherence of sheaf Ext requires both sheaf Ext and coherent sheaf theory not developed in mathlib.

## Statement 122 (Ext Tensor Adjunction) — non-included
The tensor-Hom adjunction for sheaf Ext with locally free sheaves is not formalized.

## Statement 123 (Serre Duality on Projective Space) — non-included
Serre duality is not in mathlib. Searched for "SerreDuality", "dualizing" in the algebraic geometry directory with no results.

## Statement 124 (Canonical Sheaf of Projective Space) — non-included
The identification omega_{P^n} = O(-n-1) requires the sheaf of differentials on projective space which is not computed in mathlib.

## Statement 125 (Existence of Dualizing Sheaf) — non-included
Dualizing sheaves for projective schemes are not formalized. No results for "dualizingSheaf" were found.

## Statement 126 (Canonical Sheaf is Dualizing for Smooth Schemes) — non-included
Requires both dualizing sheaves and Serre duality which are not formalized.

## Statement 127 (Ext Proposition for Sheaves) — non-included
Requires sheaf Ext, twisting sheaves, and Serre vanishing which are not available.

## Statement 128 (Grothendieck Vanishing) — non-included
H^i(X, F) = 0 for i > dim(X) requires sheaf cohomology which is not formalized.

## Statement 129 (Dualizing Sheaf for Local Complete Intersections) — non-included
Requires sheaf Ext and regular embeddings not available in mathlib.

## Statement 130 (Cohen-Macaulay Duality Equivalence) — non-included
The Cohen-Macaulay condition is not defined in mathlib. A search for "CohenMacaulay" returns no results.

## Statement 131 (Smooth Implies Full Duality) — non-included
Requires Serre duality which is not formalized.

## Statement 132 (Cohen-Macaulay via Cohomological Vanishing) — non-included
Requires both the Cohen-Macaulay condition and sheaf cohomology.

## Statement 133 (Cohen-Macaulay via Ext Vanishing) — non-included
Requires sheaf Ext and duality theory.

## Statement 134 (Cohen-Macaulay via Local Ext Vanishing) — non-included
Requires local Ext computations not formalized in this context.

## Statement 135 (Projective Dimension and Ext Vanishing) — non-included
Projective dimension is defined in `Mathlib/CategoryTheory/Abelian/Projective/Dimension.lean`, but the specific equivalence for modules over regular local rings is not fully formalized.

## Statement 136 (Auslander-Buchsbaum Formula) — non-included
The formula pd_A(M) + depth_A(M) = dim(A) is not in mathlib. Depth and regular sequences are partially available but the full formula is absent.

## Statement 137 (Cohen-Macaulay via Depth) — non-included
The depth characterization of the duality condition is not formalized.

## Statement 138 (Hodge Index Theorem) — non-included
Intersection theory on surfaces is not formalized. Searched for "HodgeIndex" with no results.

## Statement 139 (Nakai-Moishezon Criterion) — non-included
The ampleness criterion via intersection numbers is not in mathlib. Ampleness is not formalized in algebraic geometry.

## Statement 140 (Hirzebruch-Riemann-Roch) — non-included
Requires Chern classes, Todd classes, and intersection theory. Searched for "chernCharacter", "toddClass" with no results.

## Statement 141 (Grothendieck-Riemann-Roch) — non-included
Requires K-theory and intersection theory which are not formalized.

## Statement 142 (Etale Cohomology Computes Betti Numbers) — non-included
Etale cohomology is not formalized beyond the Grothendieck topology setup in `Mathlib/CategoryTheory/Sites/`.

## Statement 143 (Riemann-Roch for Surfaces) — non-included
Requires intersection theory and sheaf cohomology on surfaces which are not formalized.
