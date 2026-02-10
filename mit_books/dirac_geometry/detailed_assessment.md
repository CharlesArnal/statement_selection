Theorem 1 (Cartan's formula):
non-included
Searched for "Cartan.*formula", "cartan.*magic", "interior_product", "interiorProduct", "lieDerivative", "LieDerivative" across all of Mathlib. No results were found. Cartan's magic formula ($i_{[X,Y]} = [[i_X,d],i_Y]$) relating the interior product, exterior derivative, and Lie derivative on differential forms is not formalized in mathlib. Mathlib has Lie derivative and interior product definitions in limited contexts but not this specific identity on smooth manifolds.

Theorem 2 (Frobenius):
non-included
Searched for "Frobenius", "frobenius.*theorem" in Mathlib/Geometry/Manifold/. No results were found. The Frobenius integrability theorem for distributions on smooth manifolds is not present in mathlib. While mathlib has the Frobenius endomorphism in algebra, the differential-geometric Frobenius theorem about involutive distributions and foliations is absent.

Theorem 3 (Darboux):
non-included
Searched for "Darboux", "darboux" across Mathlib. Found only Mathlib/Analysis/Calculus/Darboux.lean, which is about the intermediate value property of derivatives (Darboux's theorem in real analysis), not the symplectic Darboux theorem about local normal forms of symplectic manifolds. The symplectic Darboux theorem is not in mathlib.

Corollary 1:
non-included
Searched for "symplectic.*sphere", "sphere.*symplectic" across Mathlib. No results. This corollary that $S^4$ and $S^1 \times S^3$ admit no symplectic structure is not in mathlib. Mathlib does not have symplectic manifolds formalized at all.

Proposition 1:
non-included
Searched for "symplectomorphism", "Symplectomorphism", "lagrangian.*graph", "Lagrangian" across Mathlib. No results. The characterization of symplectomorphisms via Lagrangian graphs is not in mathlib. While Mathlib/LinearAlgebra/SymplecticGroup.lean exists with the symplectic group defined, it does not contain manifold-level symplectic geometry.

Proposition 2:
non-included
Searched for "Poisson.*algebra", "PoissonAlgebra", "poisson_algebra", "Poisson.*bracket", "poissonBracket" across Mathlib. Found only Mathlib/Algebra/Lie/NonUnitalNonAssocAlgebra.lean which mentions Poisson algebras in a docstring but does not formalize them. The statement that smooth functions on a Poisson manifold form a Poisson algebra is not in mathlib.

Theorem 4 (Newlander-Nirenberg):
non-included
Searched for "Newlander.Nirenberg", "newlander_nirenberg", "almost.*complex", "AlmostComplex", "almostComplex" across Mathlib. No results. The Newlander-Nirenberg theorem, asserting that an integrable almost complex structure on a smooth manifold makes it a complex manifold, is not in mathlib. Even the notion of almost complex structure on a manifold is absent.

Proposition 3:
non-included
Searched for "CliffordAlgebra", "Mukai", "mukai_pairing" across Mathlib. While Mathlib has an extensive Clifford algebra library (Mathlib/LinearAlgebra/CliffordAlgebra/), this specific proposition about the bilinear pairing on spinors $(x \cdot \rho, \phi) = (\phi, \alpha(x) \cdot \phi)$ is not present. The Mukai pairing on spinors is not formalized in mathlib.

Corollary 2:
non-included
Searched in Mathlib/LinearAlgebra/CliffordAlgebra/. This corollary about the spin-invariance of the Mukai pairing is a direct consequence of Proposition 3 and involves concepts (Mukai pairing, spin representation on exterior algebra) that are not in mathlib.

Proposition 4:
non-included
This symmetry property of the Mukai pairing $(\rho, \phi) = (-1)^{n(n-1)/2}(\phi, \rho)$ is not in mathlib. The Mukai pairing itself is not formalized.

Claim 1:
non-included
Searched across Mathlib for Lie bracket symmetries and diffeomorphism groups. The claim that symmetries of the Lie bracket on vector fields are exactly given by diffeomorphisms is a result in differential geometry not formalized in mathlib. Mathlib does not have the infrastructure for diffeomorphism groups acting on sections of the tangent bundle.

Theorem 5:
non-included
Searched for "Courant", "courant" across Mathlib. No results. This theorem about symmetries of exact Courant algebroids forming a short exact sequence $0 \to \Omega^2_{cl} \to Sym(E) \to Diff_{[H]} \to 0$ belongs to the theory of Courant algebroids, which is entirely absent from mathlib.

Theorem 6:
non-included
This theorem about involutive subbundles of Courant algebroids being either isotropic or pullbacks of integrable distributions is part of Dirac geometry, which is not in mathlib. Searched for "Dirac.*structure", "dirac_structure" with no results.

Lemma 1:
non-included
Searched for "bi.invariant.*closed", "biInvariant", "biInvariantForm" across Mathlib. No results. While mathlib has the Killing form (Mathlib/Algebra/Lie/Killing.lean), the specific lemma that bi-invariant differential forms on Lie groups are closed is not present. Mathlib's Lie group theory does not extend to differential forms on Lie groups.

Lemma 2:
non-included
This lemma computing the exterior derivative of the dual of a left-invariant vector field in terms of the Cartan 3-form is a specialized result in Lie group geometry not in mathlib.

Corollary 3:
non-included
The involutivity of the Cartan-Dirac structure $L_C$ under the H-twisted Courant bracket is part of Dirac geometry on Lie groups, entirely absent from mathlib.

Theorem 7:
non-included
This theorem that the multiplication map $(m,\tau)$ is a Dirac morphism from $L_C \times L_C \to L_C$ is a result in the Dirac geometry of Lie groups, not in mathlib.

Proposition 5:
non-included
Searched for "generalizedComplex", "GeneralizedComplex", "Dirac.*structure" across Mathlib. No results. The equivalence between generalized complex structures and complex Dirac structures of real index 0 is part of generalized complex geometry, entirely absent from mathlib.

Proposition 6:
non-included
The ellipticity of the Lie algebroid complex $(C^{\infty}(\bigwedge^* L^*), d_L)$ for a generalized complex structure is not in mathlib. Searched for "LieAlgebroid", "lie_algebroid" with no results.

Corollary 4:
non-included
The finite-dimensionality of Lie algebroid cohomology for compact generalized complex manifolds follows from Proposition 6 and is not in mathlib.

Corollary 5:
non-included
The finite-dimensionality of the generalized Dolbeault cohomology groups on compact generalized complex manifolds is not in mathlib. Searched for "Dolbeault", "dolbeault" with no results.

Lemma 3:
non-included
The statement $O(n,n)/(O(n) \times O(n))$ is contractible (expressed as $O(n,n) \simeq O(n) \times O(n)$ as a homotopy equivalence) is not in mathlib. While mathlib has orthogonal groups, it does not have split-signature orthogonal groups or their homogeneous space topology.

Lemma 4:
non-included
Similarly, the homotopy equivalence $U(n,n) \simeq U(n) \times U(n)$ for the indefinite unitary group is not in mathlib.

Theorem 8:
non-included
The theorem that a generalized complex manifold is foliated by symplectic leaves with transverse complex structure is part of generalized complex geometry, not in mathlib.

Lemma 5:
non-included
The statement that $\mathbb{J}T^*$ is Dirac for an integrable generalized complex structure is part of generalized complex geometry, not in mathlib.

Lemma 6:
non-included
The result that $e^{\theta\mathbb{J}}T^*$ yields a twisted Poisson structure is part of generalized complex geometry, not in mathlib.

Theorem 9 (Weinstein Splitting):
non-included
Searched for "Weinstein.*splitting", "weinstein" across Mathlib. Found only unrelated results (Mathlib/LinearAlgebra/Matrix/SchurComplement.lean, Mathlib/Analysis/Hofer.lean). The Weinstein splitting theorem for Poisson manifolds giving local coordinates decomposing into symplectic and transverse parts is not in mathlib.

Theorem 10:
non-included
This local normal form theorem for generalized complex structures near regular points is part of generalized complex geometry, not in mathlib.

Corollary 6:
non-included
The local equivalence of a GCS on an exact Courant algebroid to $\mathbb{R}^{2(n-k)}_{\omega_0} \times \mathbb{C}^k$ near a regular point follows from Theorem 10 and is not in mathlib.

Corollary 7:
non-included
The type inequality $type(A) + type(B) \le n$ for generalized Kahler structures is part of generalized Kahler geometry, not in mathlib. Searched for "Kahler", "kaehler" in Mathlib; found only algebraic Kaehler differentials, not Kahler geometry.

Proposition 7:
non-included
The reconstruction of a generalized Kahler pair $(\mathbb{J}_A, \mathbb{J}_B)$ from $(g, J_+, J_-)$ is part of generalized Kahler geometry, not in mathlib.

Proposition 8:
non-included
The result that involutivity of $L_{\pm}$ implies involutivity of $L_{+} \oplus L_{-}$ and $L_{+} \oplus \overline{L_{-}}$ is part of the integrability theory for generalized Kahler structures, not in mathlib.

Theorem 11:
non-included
The characterization of generalized Kahler structures via the condition $H = d_+^c \omega_+ = -d_-^c \omega_-$ is part of generalized Kahler geometry, not in mathlib.

Theorem 12:
non-included
The equivalence between generalized Kahler structures on exact Courant algebroids and bi-Hermitian structures satisfying $d_+^c \omega_+ + d_-^c \omega_- = 0$ (the Gates-Hull-Rocek theorem) is not in mathlib.

Proposition 9:
non-included
The holomorphicity of the subbundles A, B of $T_{1,0}^+$ in the generalized Kahler setting with commuting $J_+, J_-$ is not in mathlib.

Lemma 7:
non-included
Searched for "HodgeStar", "hodgeStar", "Hodge.*star" across Mathlib. No results. The adjunction property $\langle d\phi, \psi \rangle = (-1)^{\dim M} \langle \phi, \partial \psi \rangle$ for differential forms with respect to the generalized inner product is not in mathlib. Mathlib does not have the Hodge star operator.

Lemma 8:
non-included
The analogous adjunction property for $H \wedge \cdot$ is part of the generalized Hodge theory framework, not in mathlib.

Corollary 8:
non-included
The integration-by-parts identity $\int_M \langle d_H \phi, \psi \rangle = \int_M \langle \phi, d_H \psi \rangle$ on even-dimensional manifolds is not in mathlib.

Proposition 10:
non-included
The adjoint relations $\delta_+^* = -\overline{\delta}_+$ and $\delta_-^* = \overline{\delta}_-$ for the decomposed differentials in generalized Kahler geometry are not in mathlib.

Corollary 9:
non-included
The result that closed forms in $\mathcal{U}^{p,q}$ are automatically $\Delta$-closed (harmonic) in generalized Kahler geometry is not in mathlib.

Proposition 11:
non-included
The closure of maximal isotropies under composition of relations in the category $\mathcal{H}$ is a result in the linear algebra of split-signature spaces, not in mathlib.

Theorem 13:
non-included
The factorization $L = \mathcal{D}\psi_* \circ e^F \circ \mathcal{D}\phi^*$ of morphisms in the category $\mathcal{H}$ via the doubling functor is not in mathlib.

Corollary 10:
non-included
The characterization of isomorphisms in $\mathcal{H}$ via surjectivity of projections and nondegeneracy of the pairing is not in mathlib.

Theorem 14 (BHM):
non-included
Searched for "twisted.*K.theory", "twistedKTheory" across Mathlib. No results. The Bouwknegt-Hannabuss-Mathai T-duality isomorphism $K_H^*(P) \cong K_{\tilde{H}}^{*+1}(\tilde{P})$ in twisted K-theory is not in mathlib. Mathlib does not have twisted K-theory.
