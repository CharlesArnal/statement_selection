Theorem 5.1:
included
Corresponds to the Inverse Function Theorem in mathlib_coverage/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean. The key result is `HasStrictFDerivAt.to_localInverse`, which shows that if f has an invertible strict derivative f' at a, then the local inverse has derivative f'.symm. The theorem constructs an `OpenPartialHomeomorph` via `HasStrictFDerivAt.toOpenPartialHomeomorph`. This covers both the local diffeomorphism statement and the derivative-of-inverse formula.

Theorem 5.2:
included
Corresponds to the Implicit Function Theorem in mathlib_coverage/mathlib/Mathlib/Analysis/Calculus/Implicit.lean. The file defines `ImplicitFunctionData` and proves `HasStrictFDerivAt.implicitFunctionDataOfComplemented`, which handles the case where the derivative is surjective and its kernel has a closed complement -- exactly the hypotheses in the textbook. There is also `HasStrictFDerivAt.implicitFunction` for finite-dimensional codomains where complementedness is automatic.

Corollary 5.4:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/ and mathlib_coverage/mathlib/Mathlib/Analysis/Calculus/ but found no direct statement that the preimage of a regular value is a submanifold in the sense of smooth manifolds. While the implicit function theorem is present (providing the local chart structure), mathlib does not currently have a formal notion of "submanifold" or a statement packaging the preimage-of-regular-value result at the manifold level. The closest results are the implicit function theorem files which give local parametrizations.

Lemma 6.1:
included
The Picard-Lindelof (Cauchy-Lipschitz) theorem is formalized in mathlib_coverage/mathlib/Mathlib/Analysis/ODE/PicardLindelof.lean. The file proves existence and uniqueness of solutions to ODEs with Lipschitz-continuous right-hand sides on Banach spaces, using the contraction mapping theorem. The Lipschitz properties of the ODE flow operator are established as part of this proof (see `IsPicardLindelof` structure and its associated theorems). This essentially covers the content of Lemma 6.1.

Theorem 10.1:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/ and mathlib_coverage/mathlib/Mathlib/RingTheory/Grassmannian.lean. While mathlib has a definition of the Grassmannian as an algebraic object, there is no theorem about classifying vector bundles of finite type via maps to Grassmannians. The Whitney embedding theorem file uses partitions of unity for embedding but does not formalize the classifying map construction for vector bundles.

Theorem 11.1:
included
Corresponds to the Whitney embedding theorem in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/WhitneyEmbedding.lean. The theorem `SmoothBumpCovering.exists_embedding_euclidean_of_compact` states that for a compact smooth manifold M, there exists n and a smooth closed embedding M -> R^n with injective derivative everywhere. This is exactly the "easiest version" (embedding into R^N for some large N).

Theorem 12.1:
included
Corresponds to Fubini-type results on null sets in mathlib_coverage/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean. The theorem `measure_prod_null` (and related `measure_prod_null_of_ae_null`) states that a measurable set in a product space has zero product measure if and only if for almost every t, the slice has zero measure. This is the measure-theoretic version of the Fubini-type measure zero result stated in the textbook.

Lemma 12.2:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/MeasureTheory/ for a result stating that the continuous image of a measurable set is measurable. This is not true in general (continuous images of Borel sets need not be Borel), and indeed mathlib does not contain such a statement. Mathlib has results about measurable images under injective measurable maps, and about analytic sets, but not the blanket statement as given in the textbook (which is stated somewhat loosely).

Theorem 12.3:
included
A version of Sard's theorem is proved in mathlib_coverage/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean. The theorem `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` states that if f is differentiable on a set s and its derivative has zero determinant everywhere on s, then f(s) has zero Lebesgue measure. This is a version of Sard's lemma in fixed dimension. The file also contains `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (image of a null set under a differentiable map is null). Together these give the essential content of Sard's theorem for finite-dimensional manifolds.

Proposition 13.2:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/LinearAlgebra/, mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/, and mathlib_coverage/mathlib/Mathlib/RingTheory/Grassmannian.lean. There is no formalization of the fact that the set of linear maps of a given rank forms a smooth submanifold of hom(R^k, R^n) with specified codimension. The Grassmannian file only defines the Grassmannian as a quotient, without manifold structure.

Lemma 13.3:
non-included
This is a concrete linear algebra lemma about block matrix kernel characterization. Searched in mathlib_coverage/mathlib/Mathlib/LinearAlgebra/ and mathlib_coverage/mathlib/Mathlib/Analysis/Matrix/. No equivalent statement was found. Mathlib has general results about block matrices but not this specific characterization used in the rank stratification proof.

Theorem 15.1:
non-included
The weak Whitney embedding theorem (compact n-manifold embeds into R^{2n+1}) is explicitly listed as a TODO in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/WhitneyEmbedding.lean: "Prove the weak Whitney embedding theorem: any sigma-compact smooth m-dimensional manifold can be embedded into R^{2m+1}." Only the easiest version (embedding into R^N for unspecified large N) is proved.

Lemma 15.2:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/WhitneyEmbedding.lean and related files. The lemma about generic hyperplane projections preserving the embedding property is not formalized. This would require Sard's theorem applied in projective space, which is not currently in mathlib.

Proposition 15.3:
non-included
The statement that a closed smooth n-manifold immerses into R^{2n} is not in mathlib. Searched in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/. The Whitney embedding file only proves embedding into R^N for large unspecified N.

Theorem 16.3:
included
Corresponds to the completion construction in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Module/Completion.lean and mathlib_coverage/mathlib/Mathlib/Topology/UniformSpace/Completion.lean. The `UniformSpace.Completion` provides the completion of any uniform space, and `NormedSpace` structure is defined on `Completion E` in the completion file, along with the canonical linear isometric embedding `toComplLi : E ->Li[K] Completion E`. The universal property is established through the abstract completion framework.

Theorem 16.5:
included
Corresponds to the Hahn-Banach theorem in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Module/HahnBanach.lean. The key results are `Real.exists_extension_norm_eq` (for real normed spaces) and `exists_extension_norm_eq` (for R or C), which prove that a continuous linear functional on a subspace can be extended to the whole space preserving the norm.

Corollary 16.6:
included
Corresponds to `Submodule.ClosedComplemented.of_finiteDimensional` in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Module/HahnBanach.lean (line 139), which states that a finite-dimensional submodule over R or C is closed-complemented. This is proved using the Hahn-Banach theorem exactly as in the textbook.

Theorem 16.7:
included
Corresponds to `ContinuousLinearMap.isOpenMap` in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean (line 228), which states: "The Banach open mapping theorem: a surjective bounded linear map between Banach spaces is open."

Theorem 16.8:
included
Corresponds to `ContinuousLinearEquiv.ofBijective` in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean (line 403), which converts a bijective continuous linear map between Banach spaces into a continuous linear equivalence (topological isomorphism). This is derived from the open mapping theorem.

Theorem 16.9:
included
Corresponds to `LinearMap.continuous_of_isClosed_graph` in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean (line 490), which states the closed graph theorem: a linear map between Banach spaces whose graph is closed is continuous. Also available as `ContinuousLinearMap.ofIsClosedGraph`.

Theorem 16.11:
included
Corresponds to the Arzela-Ascoli theorem in mathlib_coverage/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean and mathlib_coverage/mathlib/Mathlib/Topology/UniformSpace/Ascoli.lean. The first file proves `BoundedContinuousFunction.arzela_ascoli1` (compact closure iff equicontinuous and bounded range) for bounded continuous functions on compact spaces. The second file proves a general version via uniform structures, showing that on equicontinuous families, uniform convergence and pointwise convergence topologies coincide.

Corollary 16.12:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Operator/Compact.lean and related files. While mathlib has the general theory of compact operators (`IsCompactOperator`), the specific statement that the inclusion C^1(B) -> C^0(B) is compact is not formalized. This would require combining Arzela-Ascoli with Sobolev-type embedding, which is not present in this form.

Lemma 16.14:
included
This follows from the open mapping theorem / Banach isomorphism theorem as formalized in mathlib. Specifically, the result `Submodule.ClosedComplemented.of_isCompl_isClosed` in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Module/Complemented.lean (line 117) and the related machinery show that if a range has a closed complement, then the range is closed. Also `ContinuousLinearMap.closed_complemented_range_of_isCompl_of_ker_eq_bot` in the Banach file provides the closed-range conclusion.

Theorem 16.15:
included
Corresponds to `Units.isOpen` and `Units.add` in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean. The result `Units.add` constructs the invertible element x + t when ||t|| < ||x^{-1}||^{-1}, using the Neumann series (`Units.oneSub`). The openness of the set of units (`Units.isOpen`) is the global version of this perturbation result.

Lemma 16.16:
included
Corresponds to `FiniteDimensional.of_isCompact_closedBall0` in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean (line 438): "Riesz's theorem: if a closed ball with center zero of positive radius is compact in a vector space, then the space is finite-dimensional." The converse (finite-dimensional implies proper, hence compact balls) is `FiniteDimensional.proper` in the same file. Together they give exactly Riesz's lemma as stated.

Lemma 16.18:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean where a TODO comment (line 377) explicitly states: "once mathlib has Fredholm operators, generalise the next two lemmas accordingly." Mathlib does not currently have a formalization of Fredholm operators, their openness, or local constancy of the index.

Lemma 16.19:
non-included
Since mathlib lacks Fredholm operators (see note at line 377 of Banach.lean), this specific perturbation result reducing a Fredholm perturbation to a finite-dimensional problem is not formalized.

Lemma 16.20:
non-included
Same as above -- depends on Fredholm operator theory which is not in mathlib.

Lemma 16.22:
included
The statement that the adjoint (transpose) of a bounded operator has the same norm is established in the context of the double dual. In mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Module/Dual.lean, the result `inclusionInDoubleDual_norm_eq` establishes the isometric nature of the double dual embedding. For inner product spaces, mathlib_coverage/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean defines the adjoint as a conjugate-linear isometric equivalence (`ContinuousLinearMap.adjoint`), which directly implies norm preservation. The general Banach space dual pairing norm equality is implicit in the framework.

Lemma 16.23:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Module/Dual.lean and mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Operator/. The isomorphism Coker(T)* = ker(T*) for operators with closed range between Banach spaces is not explicitly formalized. For inner product spaces, mathlib has adjoint theory, but the general Banach space version relating cokernel duals to adjoint kernels is not present.

Lemma 16.24:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Operator/Compact.lean and mathlib_coverage/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean. The result that the adjoint of a compact operator is compact is not present in mathlib. The compact operator file defines `IsCompactOperator` and proves algebraic properties (addition, composition with continuous maps) but does not address the adjoint.

Lemma 16.25:
non-included
The result that I + K is Fredholm when K is compact is not in mathlib, since mathlib does not have Fredholm operators. While compact operators are defined (`IsCompactOperator` in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Operator/Compact.lean), the Fredholm theory built on top of them is absent.

Theorem 16.26:
non-included
The characterization of Fredholm operators via parametrices (quasi-inverses modulo compacts) is not in mathlib, since Fredholm operators themselves are not formalized.

Lemma 16.27:
non-included
The composition of Fredholm operators and index additivity are not in mathlib, since Fredholm operators are not formalized. The TODO comment in mathlib_coverage/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean confirms this gap.

Theorem 17.3:
non-included
The Sard-Smale theorem for Fredholm maps between Banach manifolds is not in mathlib. This requires both Fredholm operator theory and Banach manifold theory beyond what is currently available.

Lemma 17.4:
non-included
The local normal form for nonlinear Fredholm maps is not in mathlib. Requires Fredholm theory.

Lemma 17.6:
non-included
The local closedness of Fredholm maps is not in mathlib. Requires Fredholm theory.

Lemma 18.2:
non-included
Searched in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/ and mathlib_coverage/mathlib/Mathlib/Analysis/Calculus/Implicit.lean. While the implicit function theorem gives local parametrizations, the transversality preimage theorem (transverse preimage is a submanifold) is not formalized. Mathlib lacks both a formal definition of submanifold and a definition of transversality for smooth maps between manifolds.

Theorem 18.3:
non-included
The parametric transversality theorem (generic transversality) is not in mathlib. This requires transversality theory which is not currently formalized.

Lemma 18.4:
non-included
This criterion relating transversality of the preimage to transversality of the parametrized map is not in mathlib.

Theorem 18.5:
non-included
The infinite-dimensional parametric transversality theorem requires both Fredholm theory and Banach manifold transversality, neither of which is in mathlib.

Lemma 18.6:
non-included
This technical lemma about cokernels in the transversality setting is not in mathlib.

Theorem 18.8:
non-included
The Thom transversality theorem (generic maps are transverse to any submanifold) is not in mathlib.

Theorem 19.1:
non-included
The strong Whitney embedding theorem (compact n-manifold embeds into R^{2n}) is not in mathlib. Only the easiest version (into R^N) is proved. This would require Sard's theorem, transversality, and the Whitney trick.

Lemma 19.2:
non-included
This specific dimension computation for strata of pairs of n-planes in Grassmannians is not in mathlib.

Lemma 19.3:
non-included
The local chart description at double points of an immersion is not in mathlib.

Proposition 19.4:
non-included
The Whitney trick (eliminating double points of opposite sign) is not in mathlib. This is a deep geometric result involving disk constructions and normal bundle arguments.

Lemma 21.1:
included
The flow derivative formula d/dt f(F_t(x))|_{t=0} = D_x f(X(x)) is essentially the definition/basic property of integral curves in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean and the related transform file. The Lie derivative framework in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/VectorField/LieBracket.lean also relies on this fundamental formula through the pullback mechanism.

Theorem 21.3:
non-included
The flow box theorem (straightening lemma for nonzero vector fields) is not in mathlib. Searched for "flowBox", "flow_box", "straightening" in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/ with no results. While integral curves exist in mathlib, the coordinate-change result that straightens a nonzero vector field is not formalized.

Theorem 21.4:
non-included
The Frobenius integrability theorem is not in mathlib. Searched in mathlib_coverage/mathlib/Mathlib/Geometry/Manifold/ and more broadly. The search for "Frobenius" returned only results about the Frobenius endomorphism in algebra (characteristic p). The differential-geometric Frobenius theorem about involutive distributions being integrable is not present.

Proposition 22.1:
non-included
The characterization of codimension-one foliations via n . (curl n) = 0 is not in mathlib. Mathlib does not have a theory of foliations.

Theorem 24.2:
non-included
Reeb's stability theorem (S^2 leaf implies S^2 x S^1 structure) is not in mathlib. No foliation theory is present.

Lemma 24.3:
non-included
This extension lemma for foliating coordinate patches is not in mathlib. No foliation theory.

Lemma 24.4:
non-included
The product neighborhood structure around an S^2 leaf is not in mathlib. No foliation theory.

Theorem 24.5:
non-included
The existence of transverse circles to foliations is not in mathlib. No foliation theory.

Proposition 25.4:
non-included
Homotopy invariance of de Rham cohomology H*(M) = H*(R x M) is not in mathlib. Searched for "deRham", "de_rham", "homotopy_invariance" with no results. Mathlib does not have de Rham cohomology.

Lemma 27.1:
non-included
The exactness of the Cech-de Rham complex (Mayer-Vietoris sequence for differential forms) is not in mathlib. While mathlib_coverage/mathlib/Mathlib/Topology/Sheaves/MayerVietoris.lean defines Mayer-Vietoris squares in the context of sheaves on sites (category-theoretic), it does not contain the concrete Cech cohomology exactness result for differential forms used in de Rham theory.
