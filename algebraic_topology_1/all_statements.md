# All Mathematical Statements in "Lectures on Algebraic Topology" by Haynes Miller

## Chapter 1: Singular Homology

### Section 1-2: Introduction and Homology
- **Theorem 1.5**: Any boundary is a cycle; that is, d² = 0.

### Section 3-4: Categories, Functors, Natural Transformations
- **Lemma 4.7**: A map is an isomorphism if and only if it is both a split epimorphism and a split monomorphism.
- **Lemma 4.8**: Any functor sends split epis to split epis and split monos to split monos.

### Section 5: Homotopy, Star-shaped Regions
- **Theorem 5.2 [Homotopy invariance of homology]**: If f₀ ≃ f₁, then H∗(f₀) = H∗(f₁): homology cannot distinguish between homotopic maps.
- **Corollary 5.5**: Homotopy equivalences induce isomorphisms in homology.
- **Corollary 5.7**: Let X be a contractible space. The augmentation ε: H∗(X) → Z is an isomorphism.
- **Lemma 5.10**: If f₀, f₁: C∗ → D∗ are chain homotopic, then f₀∗ = f₁∗: H∗(C) → H∗(D).
- **Proposition 5.11**: Let f₀, f₁: X → Y be homotopic. Then f₀∗, f₁∗: S∗(X) → S∗(Y) are chain homotopic.
- **Proposition 5.13**: S∗(X) → Z is a chain homotopy equivalence (for X star-shaped).

### Section 6: Homotopy Invariance of Homology
- **Theorem 6.1**: A homotopy h: f₀ ≃ f₁: X → Y determines a natural chain homotopy f₀∗ ≃ f₁∗: S∗(X) → S∗(Y).
- **Theorem 6.2 [Cross product]**: There exists a map ×: Sp(X) × Sq(Y) → Sp+q(X × Y), the cross product, that is natural, bilinear, satisfies the Leibniz rule, and is normalized.

### Section 7: Homology Cross Product
- **Lemma 7.1**: The chain-level cross product determines a bilinear map ×: Hp(A) × Hq(B) → Hp+q(C).
- **Theorem 7.2**: There is a map ×: Hp(X) × Hq(Y) → Hp+q(X × Y) that is natural, bilinear, and normalized.

### Section 8: Relative Homology
- **Lemma 8.4**: Let A∗ be a subcomplex of the chain complex B∗. There is a unique structure of chain complex on the quotient graded abelian group C∗ with entries Cn = Bn/An such that B∗ → C∗ is a chain map.

### Section 9: The Homology Long Exact Sequence
- **Theorem 9.1 [The homology long exact sequence]**: Let 0 → A∗ → B∗ → C∗ → 0 be a short exact sequence of chain complexes. Then there is a natural homomorphism ∂: Hn(C) → Hn−1(A) such that the sequence ⋯ → Hn(A) → Hn(B) → Hn(C) → Hn−1(A) → ⋯ is exact.
- **Proposition 9.4 [Five lemma]**: In a map of exact sequences, if f₀ is injective and f₁, f₃ are surjective, then f₂ is surjective. If f₄ is surjective and f₃, f₁ are injective, then f₂ is injective.
- **Corollary 9.5**: Let a map of short exact sequences of chain complexes be given. If two of the three maps induced in homology are isomorphisms, then so is the third.
- **Proposition 9.6**: Let (A, X) → (B, Y) be a map of pairs, and assume that two of A → B, X → Y, and (X, A) → (Y, B) induce isomorphisms in homology. Then the third one does as well.

### Section 10: Excision and Applications
- **Theorem 10.2 [Excision]**: An excision induces an isomorphism in homology: H∗(X − U, A − U) ≅ H∗(X, A).
- **Corollary 10.3**: Assume that there is a subspace B of X such that (1) A ⊆ Int B and (2) A → B is a deformation retract. Then H∗(X, A) → H∗(X/A, ∗) is an isomorphism.
- **Proposition 10.4**: Computation of Hq(Sⁿ) and Hq(Dⁿ, Sⁿ⁻¹).
- **Corollary 10.5**: If m ≠ n, then Sᵐ and Sⁿ are not homotopy equivalent.
- **Corollary 10.6**: If m ≠ n, then Rᵐ and Rⁿ are not homeomorphic.
- **Theorem 10.7 [Brouwer fixed-point theorem]**: If f: Dⁿ → Dⁿ is continuous, then there is some point x ∈ Dⁿ such that f(x) = x.
- **Theorem 10.8**: Let n ≥ 1. The degree map provides us with a surjective monoid homomorphism deg: [Sⁿ, Sⁿ] → Z×.

### Section 11: The Eilenberg-Steenrod Axioms and the Locality Principle
- **Theorem 11.4 [The locality principle]**: The inclusion S^A_∗(X) ⊆ S∗(X) induces an isomorphism in homology, H^A_∗(X) ≅ H∗(X).
- **Theorem 11.5 [Mayer-Vietoris]**: Assume that A = {A, B} is a cover of X. There are natural maps ∂: Hn(X) → Hn−1(A ∩ B) such that the Mayer-Vietoris sequence is exact.
- **Lemma 11.6**: Exact sequence from a map of long exact sequences with every third arrow an isomorphism.

### Section 12: Subdivision
- **Proposition 12.1**: $ is a natural chain map S∗(X) → S∗(X) that is naturally chain-homotopic to the identity.

### Section 13: Proof of the Locality Principle
- **Lemma 13.1**: Let σ be an affine n-simplex, and τ a simplex in $σ. Then diam(τ) ≤ (n/(n+1))diam(σ).
- **Lemma 13.2**: For any singular chain c, some iterate of the subdivision operator sends c to an A-small chain.
- **Lemma 13.3 [Lebesgue covering lemma]**: Let M be a compact metric space, and let U be an open cover. Then there is ε > 0 such that for all x ∈ M, Bε(x) ⊆ U for some U ∈ U.
- **Lemma 13.4**: For any k ≥ 1, $ᵏ ≃ 1: S∗(X) → S∗(X).
- **Theorem 13.5 [The locality principle]**: Let A be a cover of a space X. The inclusion S^A_∗(X) ⊆ S∗(X) is a quasi-isomorphism.

## Chapter 2: Computational Methods

### Section 14-15: CW-complexes
- **Theorem 14.8**: Any CW-complex is Hausdorff, and it's compact if and only if it's finite.
- **Proposition 15.3**: Let X be a CW-complex with a chosen cell structure. Any compact subspace of X lies in some finite subcomplex.
- **Proposition 15.5**: S^∞ is contractible.

### Section 16: Homology of CW-complexes
- **Proposition 16.2**: Let k, q ≥ 0. Then Hq(Xk) = 0 for k < q and Hq(Xk) ≅ Hq(X) for k > q.
- **Theorem 16.3**: For a CW complex X, there is an isomorphism H∗(C∗(X)) ≅ H∗(X) natural with respect to filtration-preserving maps.
- **Corollary 16.4**: Suppose that the CW complex X has only even cells. Then H∗(X) ≅ C∗(X).

### Section 17: Real Projective Space
- **Proposition 17.1**: The homology of real projective space RPⁿ.

### Section 18: Euler Characteristic and Homology Approximation
- **Theorem 18.1**: Let X be a finite CW-complex with aₙ n-cells. Then χ(X) = Σ(−1)ᵏaₖ depends only on the homotopy type of X.
- **Lemma 18.2**: Let 0 → A → B → C → 0 be a short exact sequence of finitely generated abelian groups. Then rank A − rank B + rank C = 0.
- **Theorem 18.3**: Let X be a finite CW complex. Then χ(X) = Σₖ(−1)ᵏ rank Hₖ(X).
- **Theorem 18.4 [Wall]**: Let X be a simply connected CW-complex of finite type. Then there exists a CW complex Y with r(k) + t(k) + t(k−1) k-cells, for all k, and a homotopy equivalence Y → X.
- **Proposition 18.5**: For any graded abelian group A∗ with Aₖ = 0 for k ≤ 0, there exists a CW complex X with H̃∗(X) = A∗.

### Section 20: Tensor Product
- **Proposition 20.11**: For any abelian group M, (X, A) ↦ H∗(X, A; M) provides a homology theory satisfying the Eilenberg-Steenrod axioms with H₀(∗; M) = M.

### Section 21: Tensor and Tor
- **Proposition 21.1**: The functor N ↦ M ⊗_R N preserves cokernels; it is right exact.
- **Lemma 21.2**: If M'ᵢ → Mᵢ → M''ᵢ is exact for all i ∈ I, then so is ⊕M'ᵢ → ⊕Mᵢ → ⊕M''ᵢ.

### Section 22: The Fundamental Theorem of Homological Algebra
- **Theorem 22.1 [Fundamental Theorem of Homological Algebra]**: Let M and N be R-modules; let 0 ← M ← E₀ ← E₁ ← ⋯ be a sequence in which each Eₙ is free; let 0 ← N ← F₀ ← F₁ ← ⋯ be an exact sequence; and let f: M → N be a homomorphism. Then we can lift f to a chain map f∗: E∗ → F∗, uniquely up to chain homotopy.

### Section 23: Hom and Lim
- **Lemma 23.1**: The natural map Hom(L, Hom(M, N)) → Hom(L ⊗ M, N) is an isomorphism.
- **Proposition 23.10**: Let I be a directed set, and let M: I → Mod_R be an I-directed system. There is a natural isomorphism (lim Mᵢ) ⊗_R N ≅ lim(Mᵢ ⊗_R N).
- **Lemma 23.11**: A map f: X → c_L is the direct limit if and only if: (1) surjectivity condition and (2) injectivity condition hold.
- **Proposition 23.12**: The direct limit functor lim: Fun(I, Ab) → Ab is exact.
- **Corollary 23.13**: Let i ↦ C(i) be a directed system of chain complexes. Then there is a natural isomorphism lim H∗(C(i)) → H∗(lim C(i)).
- **Corollary 23.14**: H∗(X; Q) = H∗(X) ⊗ Q.

### Section 24: Universal Coefficient Theorem
- **Theorem 24.1 [Universal Coefficient Theorem]**: Let R be a PID and C∗ a chain complex of R-modules such that Cₙ is free for all n. Then there is a natural short exact sequence 0 → Hₙ(C∗) ⊗ M → Hₙ(C∗ ⊗ M) → Tor₁^R(Hₙ₋₁(C∗), M) → 0 that splits (but not naturally).

### Section 25: Künneth and Eilenberg-Zilber
- **Theorem 25.2 [Künneth theorem]**: Let R be a PID and C∗, D∗ be chain complexes of R-modules. Assume that Cₙ is a free R-module for all n. There is a short exact sequence relating H∗(C ⊗ D) to H∗(C) ⊗ H∗(D) and Tor.
- **Corollary 25.3**: Let R be a PID and assume C'ₙ and Cₙ are R-free for all n. If C'∗ → C∗ and D'∗ → D∗ are homology isomorphisms then so is C'∗ ⊗ D'∗ → C∗ ⊗ D∗.
- **Lemma 25.10**: Let F be M-free, let G' → G be an M-epimorphism, and let f: F → G be any natural transformation. Then there is a lifting.
- **Theorem 25.11 [Eilenberg-Zilber]**: The cross product × : S∗(X) ⊗ S∗(Y) → S∗(X × Y) is a natural quasi-isomorphism.
- **Corollary 25.12**: The homology cross product × : H∗(X) ⊗ H∗(Y) → H∗(X × Y) is an isomorphism under certain conditions.

## Chapter 3: Cohomology and Duality

### Section 26-27: Coproducts, Cohomology, Ext and UCT
- **Proposition 27.1 [Universal Coefficient Theorem for Cohomology]**: There is a natural short exact sequence 0 → Ext¹(Hₙ₋₁(C), M) → Hⁿ(C; M) → Hom(Hₙ(C), M) → 0.

### Section 28-29: Products in Cohomology
- **Theorem 28.1**: H∗(X; R) is a graded commutative R-algebra under cup product.
- **Proposition 29.2**: The cohomology cross product ×: H∗(X) ⊗ H∗(Y) → H∗(X × Y) is an R-algebra homomorphism.
- **Corollary 29.4**: Let p, q > 0. Any map Sᵖ⁺ᵍ → Sᵖ × Sᵍ induces the zero map in Hᵖ⁺ᵍ(−).

### Section 30: Surfaces and Nondegenerate Symmetric Bilinear Forms
- **Theorem 30.2 [Poincaré duality, F₂ coefficients]**: Let M be a compact manifold of dimension n. There exists a unique class [M] ∈ Hₙ(M) such that the cup product pairing is perfect.
- **Lemma 30.5**: The restriction of a nondegenerate bilinear form on V to a subspace W is nondegenerate exactly when W ∩ W^⊥ = 0.
- **Proposition 30.6**: Any finite dimensional nondegenerate symmetric bilinear form over F₂ splits as an orthogonal direct sum of forms with matrices [1] and the hyperbolic form.
- **Claim 30.7**: The relation I ⊕ H = 3I holds for bilinear forms over F₂.
- **Proposition 30.8**: There is an isomorphism H₁(Σ₁#Σ₂) ≅ H₁(Σ₁) ⊕ H₁(Σ₂) compatible with the intersection forms.
- **Theorem 30.9**: Formation of the intersection bilinear form gives an isomorphism of commutative monoids Surf → Bil.

### Section 31: Local Coefficients and Orientations
- **Lemma 31.4**: If π acts principally on X then the orbit projection map X → π\X is a covering space.
- **Theorem 31.5 [Unique path lifting]**: Let p: E → B be a covering space, and ω: I → B a path in the base. For any e ∈ E such that p(e) = ω(0), there is a unique path ω̃: I → E in E such that pω̃ = ω and ω̃(0) = e.
- **Theorem 31.6**: Assume that B is semi-locally simply connected. Then the functor Cov_B → Set-π₁(B, b) is an equivalence of categories.
- **Theorem 31.7**: Let B be path connected and semi-locally simply connected. Then forming the fiber over a point gives an equivalence of categories from local coefficient systems of R-modules over B to modules over the group algebra R[π₁(B, b)].
- **Theorem 31.9 [Orientation Theorem]**: If M is compact, the map j: Hₙ(M; R) → Γ(M; o_M ⊗ R) is an isomorphism.
- **Corollary 31.10**: If M is a compact connected n-manifold, then Hₙ(M; R) ≅ R if M is orientable, and Hₙ(M; R) ≅ R[2] if not.

### Section 32: Proof of the Orientation Theorem
- **Theorem 32.1**: Let M be an n-manifold and let A be a compact subset of M. Then Hq(M|A; R) = 0 for q > n, and the map j_A: Hₙ(M|A; R) → Γ(A; o_M ⊗ R) is an isomorphism.
- **Proposition 32.2**: Let A and B be closed subspaces of M, and suppose the result holds for A, B, and A ∩ B. Then it holds for A ∪ B.
- **Proposition 32.3**: Let A₁ ⊇ A₂ ⊇ ⋯ be a decreasing sequence of compact subsets of M, and assume that the theorem holds for each Aₙ. Then it holds for the intersection A = ∩Aᵢ.
- **Lemma 32.4**: Let A₁ ⊇ A₂ ⊇ ⋯ be a decreasing sequence of compact subsets of a space X, with intersection A. Then lim Hq(X, X − Aᵢ) ≅ Hq(X, X − A).
- **Lemma 32.5**: Let A₁ ⊇ A₂ ⊇ ⋯ be a decreasing sequence of compact subsets in a Hausdorff space X with intersection A. For any open neighborhood U of A there exists i such that Aᵢ ⊆ U.

### Section 33: A Plethora of Products
- **Claim 33.1**: ⟨f∗b, x⟩ = ⟨b, f∗x⟩.
- **Lemma 33.2**: Let a ∈ Hᵖ(X), b ∈ Hᵍ(Y), x ∈ Hₚ(X), y ∈ Hq(Y). Then ⟨a × b, x × y⟩ = (−1)^|x|·|b| ⟨a, x⟩⟨b, y⟩.
- **Theorem 33.3 [Cohomology Künneth theorem]**: Let R be a PID. Assume that Hₚ(X) is a finitely generated free R-module for all p. Then ×: H∗(X; R) ⊗_R H∗(Y; R) → H∗(X × Y; R) is an isomorphism.

### Section 34: Cap Product and Čech Cohomology
- **Proposition 34.1**: The cap product enjoys properties: (1) module structure, (2) projection formula, (3) augmentation property, (4) adjointness with cup.
- **Theorem 34.2 [Poincaré duality]**: Let M be a topological n-manifold that is compact and oriented with respect to a PID R. Then − ∩ [M]: Hᵖ(M; R) → Hq(M; R), p + q = n, is an isomorphism for all p.
- **Lemma 34.3**: Compatibility of cap product with Čech cohomology restrictions.
- **Lemma 34.5**: Under regular neighborhood conditions, Ȟ∗(K) → H∗(K) is an isomorphism.
- **Theorem 34.6**: Let X be a compact subset of some Euclidean space. If there is an open neighborhood of which it is a retract, then Ȟ∗(X; R) is canonically isomorphic to the cohomology defined using the Čech construction.

### Section 35: Čech Cohomology as a Cohomology Theory
- **Theorem 35.2 [Long exact sequence for Čech]**: Let (K, L) be a closed pair in X. There is a long exact sequence for Čech cohomology.
- **Theorem 35.3 [Excision for Čech]**: Suppose A and B are closed subsets of a normal space, or compact subsets of a Hausdorff space. Then Ȟᵖ(A ∪ B, A) ≅ Ȟᵖ(B, A ∩ B).
- **Lemma 35.7**: If φ: J → I is cofinal then lim_J Aφ → lim_I A is an isomorphism.
- **Lemma 35.8**: Cofinality conditions for Čech excision.
- **Corollary 35.9 [Mayer-Vietoris for Čech]**: There is a natural long exact Mayer-Vietoris sequence for Čech cohomology.

### Section 36: The Fully Relative Cap Product
- **Theorem 36.1**: There is a fully relative cap product ∩: Ȟᵖ(K, L) ⊗ Hₙ(X, X − K) → Hq(X − L, X − K).
- **Theorem 36.2**: The Čech cohomology and singular homology Mayer-Vietoris sequences are compatible.

### Section 37: Poincaré Duality
- **Theorem 37.1 [Fully relative Poincaré duality]**: Let M be an n-manifold and K ⊇ L a pair of compact subsets. Assume given an R-orientation along K. With p + q = n, the map ∩[M]_K: Ȟᵖ(K, L; R) → Hq(M − L, M − K; R) is an isomorphism.
- **Lemma 37.2**: Let A₁ ⊇ A₂ ⊇ ⋯ be a decreasing sequence of compact subspaces of M. Then Ȟᵖ(Aₖ) → Ȟᵖ(A) is an isomorphism.
- **Corollary 37.3**: Ladder of isomorphisms for compact R-oriented n-manifold with closed subset.
- **Corollary 37.4**: An R-orientation along K determines an isomorphism ∩[M]_K: Ȟᵖ(K; R) → Hq(M, M − K; R).
- **Corollary 37.5 [Poincaré duality]**: Let M be a compact R-oriented n-manifold. Then ∩[M]: Hᵖ(M; R) → Hₙ₋ₚ(M; R) is an isomorphism.

### Section 38: Applications
- **Theorem 38.1**: Let M be an n-manifold and K a compact subset. An R-orientation along K determines a fundamental class and cap product isomorphism.
- **Corollary 38.2**: Ȟᵖ(K; R) = 0 for p > n.
- **Theorem 38.4 [Alexander duality]**: For any compact subset K of Rⁿ, the composite Ȟⁿ⁻ᵍ(K; R) → Hq(Rⁿ, Rⁿ − K; R) → H̃q₋₁(Rⁿ − K; R) is an isomorphism.
- **Corollary 38.5**: If K is a compact subset of Rⁿ then Ȟⁿ(K; R) = 0.
- **Corollary 38.6**: The complement of a knot in S³ is a homology circle.
- **Theorem 38.8**: Let R be a PID and M a compact R-oriented n-manifold. Then a ⊗ b ↦ ⟨a ∪ b, [M]⟩ induces a perfect pairing.
- **Theorem 38.11 [Borsuk-Ulam]**: Think of Sⁿ as the unit vectors in Rⁿ⁺¹. For any continuous function f: Sⁿ → Rⁿ, there exists x ∈ Sⁿ such that f(x) = f(−x).
