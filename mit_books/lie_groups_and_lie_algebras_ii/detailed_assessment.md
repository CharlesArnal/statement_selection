# Detailed Assessment

## Statement 1: Lemma 1.4
**Lemma 1.4.** If X is a topological space with a countable base then every open cover of X has a countable subcover.

Assessment: non-included
This lemma states the Lindelof property: a second-countable topological space has countable subcovers. While mathlib has second-countable spaces and the Lindelof property (`Mathlib/Topology/Compactness/Lindelof.lean`), the specific formulation as 'countable base implies countable subcover for every open cover' is a standard topology fact captured by `TopologicalSpace.IsLindelof` but not stated identically. Searched in `Mathlib/Topology/` for Lindelof, second-countable, and open cover properties.

## Statement 2: Lemma 1.14
**Lemma 1.14.** Let  $x_1, ..., x_n$  be local coordinates at P. Then  $T_PX$  has basis  $D_1, ..., D_n$ , where

$$D_i(f) := \frac{\partial f}{\partial x_i}(0).$$

 $<sup>^2</sup>$ More precisely, for  $C^k$  and real analytic manifolds regular functions will be assumed real-valued, unless specified otherwise. In the complex analytic case there is, of course, no choice, and regular functions are automatically complex-valued.

Assessment: non-included
This states that partial derivatives form a basis of the tangent space at a point. While mathlib has tangent spaces for smooth manifolds (`Mathlib/Geometry/Manifold/`), the explicit identification of partial derivatives as a basis via the derivation model is not directly present as a standalone lemma. Searched in `Mathlib/Geometry/Manifold/` for tangent space basis results.

## Statement 3: Proposition 1.18
**Proposition 1.18.** If F is a submersion then for any  $Q \in Y$ ,  $F^{-1}(Q)$  is a manifold of dimension  $\dim X - \dim Y$ .

Assessment: non-included
The regular value / submersion theorem: preimages of submersions are manifolds. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Geometry/Manifold/` for submersion, preimage, and regular value results.

## Statement 4: Proposition 2.2
**Proposition 2.2.** In a Lie group G, the inversion map  $\iota: G \to G$  is a diffeomorphism, and  $d\iota_1 = -\mathrm{Id}$ .

Assessment: non-included
Inversion in a Lie group is a diffeomorphism with differential -Id at 1. While mathlib's `LieGroup` definition (`Mathlib/Geometry/Manifold/Algebra/LieGroup.lean`) requires smooth inversion, the explicit computation that the differential at 1 is -Id is not stated. Searched `LieGroup.lean` and related files.

## Statement 5: Proposition 2.6
**Proposition 2.6.** (i)  $G^{\circ}$  is a normal subgroup of G.

- (ii)  $\pi_0(G) = G/G^{\circ}$  with quotient topology is a discrete and countable group.
- *Proof.* (i) Let  $g \in G$ ,  $a \in G^{\circ}$ , and  $x : [0,1] \to G$  be a path connecting 1 to a. Then  $gxg^{-1}$  is a path connecting 1 to  $gag^{-1}$ , so  $gag^{-1} \in G^{\circ}$ , hence  $G^{\circ}$  is normal.
- (ii) Since G is a manifold, for any  $g \in G$ , there is a neighborhood of g contained in  $G_g = gG^{\circ}$ . This implies that any coset of  $G^{\circ}$  in G is open, hence  $G/G^{\circ}$  is discrete. Also  $G/G^{\circ}$  is countable since G has a countable base.

Thus we see that any Lie group is an extension of a discrete countable group by a connected Lie group. This essentially reduces studying Lie groups to studying connected Lie groups. In fact, one can further reduce to simply connected Lie groups, which is done in the next subsections.

Assessment: non-included
Connected component of identity is a normal subgroup, with pi_0 discrete and countable. Mathlib has `connectedComponentOf` in `Mathlib/Topology/Connected/Basic.lean` but the full package (normal, discrete, countable) for Lie groups is not stated together. Searched in topology and group theory directories.

## Statement 6: Proposition 3.5
**Proposition 3.5.** (i)  $\widetilde{G}$  is a simply connected Lie group. The covering  $p: \widetilde{G} \to G$  is a homomorphism of Lie groups.

(ii)  $\operatorname{Ker}(p)$  is a central subgroup of  $\widetilde{G}$  naturally isomorphic to  $\pi_1(G) = \pi_1(G,1)$ . Thus,  $\widetilde{G}$  is a central extension of G by  $\pi_1(G)$ . In particular,  $\pi_1(G)$  is abelian.

Assessment: non-included
Properties of the universal cover of a Lie group (simply connected, kernel central). Not formalized in mathlib. Searched in `Mathlib/Geometry/Manifold/` and `Mathlib/Topology/` for universal cover and covering space results.

## Statement 7: Lemma 3.11
**Lemma 3.11.** A closed Lie subgroup of G is closed in G.

Assessment: non-included
Closed Lie subgroup is closed in G (tautological from definitions, but specific notion differs). Not in mathlib in this form.

## Statement 8: Theorem 3.13
**Theorem 3.13.** Any closed subgroup of a real Lie group G is a closed Lie subgroup.

This theorem is rather nontrivial, and we will not prove it at this time (it will be proved much later in Exercise 36.13), but we will soon prove a weaker version which suffices for our purposes.

Assessment: non-included
Cartan's closed subgroup theorem: any closed subgroup of a real Lie group is a Lie subgroup. This deep theorem is not in mathlib v4.27.0. Searched in `Mathlib/Geometry/Manifold/` and `Mathlib/Topology/Algebra/`.

## Statement 9: Proposition 3.15
**Proposition 3.15.** (i) If G is a connected Lie group and U a neighborhood of 1 in G then U generates G.

(ii) If  $f: G \to K$  is a homomorphism of Lie groups, K is connected, and  $df_1: T_1G \to T_1K$  is surjective, then f is surjective.

Assessment: non-included
Connected Lie groups are generated by neighborhoods of identity, and morphisms with surjective differential are surjective. Not formalized in mathlib.

## Statement 10: Theorem 4.1
**Theorem 4.1.** (i) Let G be a Lie group of dimension n and  $H \subset G$  a closed Lie subgroup of dimension k. Then the **homogeneous space** G/H has a natural structure of an n-k-dimensional manifold, and the map  $p: G \to G/H$  is a locally trivial fibration with fiber H.

- (ii) If moreover H is normal in G then G/H is a Lie group.
- (iii) We have a natural isomorphism  $T_1(G/H) \cong T_1G/T_1H$ .

Assessment: non-included
Homogeneous space G/H has a natural manifold structure and p is a locally trivial fibration. Not formalized in mathlib.

## Statement 11: Corollary 4.2
Corollary 4.2. Let  $H \subset G$  be a closed Lie subgroup.

- (i) If H is connected then the map  $p_0: \pi_0(G) \to \pi_0(G/H)$  is a bijection.
  - (ii) If also G is connected then there is an exact sequence

$$\pi_1(H) \to \pi_1(G) \to \pi_1(G/H) \to 1.$$

Assessment: non-included
If H is a normal closed Lie subgroup, G/H is a Lie group with Lie algebra g/h. Not formalized in mathlib for Lie groups, though Lie algebra quotients are in `Mathlib/Algebra/Lie/Quotient.lean`.

## Statement 12: Proposition 4.7
**Proposition 4.7.** Let  $f: G \to K$  be a homomorphism of Lie groups. Then  $H := \operatorname{Ker} f$  is a closed normal Lie subgroup in G and  $\operatorname{Im} f$  is a Lie subgroup in K, closed if and only if it is an embedded submanifold. In the latter case, we have an isomorphism of Lie groups  $G/H \cong \operatorname{Im} f$ .

We will prove Proposition 4.7 in Subsection 9.1.

4.3. Actions and representations of Lie groups. Let X be a manifold, G a Lie group, and  $a: G \times X \to X$  a set-theoretical left action of G on X.

Assessment: non-included
Kernel of Lie group homomorphism is closed normal Lie subgroup, image is Lie subgroup, first isomorphism theorem for Lie groups. Not formalized in mathlib for Lie groups.

## Statement 13: Proposition 4.12
**Proposition 4.12.** (The orbit-stabilizer theorem for Lie group actions) The stabilizer  $G_x \subset G$  is a closed Lie subgroup, and the natural map  $G/G_x \to X$  is an injective immersion whose image is G.

Assessment: non-included
Orbit-stabilizer theorem for Lie group actions. Not in mathlib for smooth/Lie group actions. Searched in `Mathlib/GroupTheory/GroupAction/` and `Mathlib/Geometry/Manifold/`.

## Statement 14: Corollary 4.13
**Corollary 4.13.** The orbit  $Gx \subset X$  is an immersed submanifold, and we have a natural isomorphism  $T_x(Gx) \cong T_1G/T_1G_x$ . If Gx is an embedded submanifold then the map  $G/G_x \to Gx$  is a diffeomorphism.

Assessment: non-included
Orbit is an immersed submanifold with tangent space g/g_x. Not in mathlib.

## Statement 15: Corollary 4.16
**Corollary 4.16.** If G acts transitively on X then the map  $p: G \to X$  given by p(g) = gx is a locally trivial fibration with fiber  $G_x$ .

Assessment: non-included
Transitivity of action implies the action map is a locally trivial fibration. Not in mathlib.

## Statement 16: Proposition 5.10
**Proposition 5.10.** (i) For any  $\tau \in \mathfrak{g}^{\otimes k} \otimes \mathfrak{g}^{*\otimes m}$  there exists a unique left invariant tensor field  $\mathbf{L}_{\tau}$  and a unique right invariant tensor field  $\mathbf{R}_{\tau}$  whose value at 1 is  $\tau$ . Thus, the spaces of such tensor fields are naturally isomorphic to  $\mathfrak{g}^{\otimes k} \otimes \mathfrak{g}^{*\otimes m}$ .

(ii)  $L_{\tau}$  is also right invariant iff  $R_{\tau}$  is also left invariant iff  $\tau$  is invariant under the adjoint representation  $Ad_{q}$ .

Assessment: non-included
Existence and uniqueness of left/right invariant tensor fields on Lie groups. Not formalized in mathlib.

## Statement 17: Corollary 5.12
Corollary 5.12. A Lie group is parallelizable.

Assessment: non-included
A Lie group is parallelizable. Not formalized in mathlib. Searched in `Mathlib/Geometry/Manifold/` for parallelizable and trivialization results.

## Statement 18: Proposition 6.3
**Proposition 6.3.** Every classical group G from the above list is a Lie group, with  $\mathfrak{g} = T_1G \subset \mathfrak{gl}_n(\mathbb{K})$ . Moreover, if  $\mathfrak{u} \subset \mathfrak{gl}_n(\mathbb{K})$  is a small neighborhood of 0 and  $U = \exp(\mathfrak{u})$  then  $\exp$  and  $\log$  define mutually inverse diffeomorphisms between  $\mathfrak{u} \cap \mathfrak{g}$  and  $U \cap G$ .

Assessment: non-included
Classical groups (GL, SL, O, SO, U, SU, Sp) are Lie groups with specific Lie algebras. While mathlib defines classical Lie algebras in `Mathlib/Algebra/Lie/Classical.lean`, it does not formally establish the Lie group/Lie algebra correspondence for these. Searched in both `Classical.lean` and manifold files.

## Statement 19: Proposition 6.7
**Proposition 6.7.** The group of unit quaternions  $\{\mathbf{q} \in \mathbb{H} : |\mathbf{q}| = 1\}$  under multiplication is isomorphic to SU(2) as a Lie group.

Assessment: non-included
Unit quaternions form SU(2) as a Lie group. Not established in mathlib.

## Statement 20: Corollary 6.8
Corollary 6.8. The map  $\mathbf{q} \mapsto (\frac{\mathbf{q}}{|\mathbf{q}|}, |\mathbf{q}|)$  is an isomorphism of Lie groups  $\mathbb{H}^{\times} \cong SU(2) \times \mathbb{R}_{>0}$ .

This is the quaternionic analog of the trigonometric form of complex numbers, except the "phase" factor  $\frac{\mathbf{q}}{|\mathbf{q}|}$  is now not in  $S^1$  but in  $S^3 = SU(2)$ .

Assessment: non-included
H^x = SU(2) x R_{>0} as Lie groups. Not in mathlib.

## Statement 21: Lemma 6.10
**Lemma 6.10.** We have  $\det A > 0$ .

Assessment: non-included
Technical determinant lemma for classical groups. Not in mathlib.

## Statement 22: Proposition 6.13
**Proposition 6.13.** (i) Every nondegenerate Hermitian form on V in some basis takes the form

$$(\mathbf{x}, \mathbf{y}) = \overline{x_1}y_1 + \dots + \overline{x_p}y_p - \overline{x_{p+1}}y_{p+1} - \dots - \overline{x_n}y_n$$

for a unique pair (p,q) with p+q=n.

(ii) Every nondegenerate skew-Hermitian form on V in some basis takes the form

$$(\mathbf{x}, \mathbf{y}) = \overline{x_1} \mathbf{j} y_1 + \dots + \overline{x_n} \mathbf{j} y_n.$$

Assessment: non-included
Classification of nondegenerate forms over quaternions. Not in mathlib.

## Statement 23: Proposition 7.1
**Proposition 7.1.** Let  $x \in \mathfrak{g}$ . There is a unique morphism of Lie groups  $\gamma = \gamma_x : \mathbb{R} \to G$  such that  $\gamma'(0) = x$ .

Assessment: non-included
Existence and uniqueness of one-parameter subgroups. Not formalized in mathlib for Lie groups.

## Statement 24: Proposition 7.3
**Proposition 7.3.** The flow defined by the right-invariant vector field  $\mathbf{R}_x$  is given by  $g \mapsto \exp(tx)g$ , and the flow defined by the left-invariant vector field  $\mathbf{L}_x$  is given by  $g \mapsto g \exp(tx)$ .

Assessment: non-included
Flows of left/right invariant vector fields are one-parameter subgroups. Not in mathlib.

## Statement 25: Theorem 7.5
**Theorem 7.5.** (i)  $\exp : \mathfrak{g} \to G$  is a regular map which is a diffeomorphism of a neighborhood of  $0 \in \mathfrak{g}$  onto a neighborhood of  $1 \in G$ , with  $\exp(0) = 1$ ,  $\exp'(0) = \operatorname{Id}_{\mathfrak{g}}$ .

- (ii)  $\exp((s+t)x) = \exp(sx) \exp(tx)$  for  $x \in \mathfrak{g}$ ,  $s, t \in \mathbb{K}$ .
- (iii) For any morphism of Lie groups  $\phi: G \to K$  and  $x \in T_1G$  we have

$$\phi(\exp(x)) = \exp(\phi_* x);$$

i.e., the exponential map commutes with morphisms.

(iv) For any  $g \in G$ ,  $x \in \mathfrak{g}$ , we have

$$g \exp(x)g^{-1} = \exp(\mathrm{Ad}_g x).$$

Assessment: non-included
Properties of the exponential map for Lie groups (local diffeomorphism, commutes with morphisms, etc.). Not in mathlib.

## Statement 26: Proposition 7.6
**Proposition 7.6.** Let G be a connected Lie group and  $\phi: G \to K$  a morphism of Lie groups. Then  $\phi$  is completely determined by the linear map  $\phi_*: T_1G \to T_1K$ .

Assessment: non-included
Morphism from connected Lie group determined by its differential. Not in mathlib.

## Statement 27: Corollary 7.10
Corollary 7.10. If  $G \subset GL_n(\mathbb{K})$  is a Lie subgroup then  $\mathfrak{g} = T_1G \subset$  $\mathfrak{gl}_n(\mathbb{K})$  is closed under the commutator [x,y]=xy-yx, which coincides with the commutator of G.

For  $x \in \mathfrak{g}$  define the linear map  $adx : \mathfrak{g} \to \mathfrak{g}$  by

$$adx(y) = [x, y].$$

Assessment: non-included
For matrix Lie groups, commutator of tangent vectors equals matrix commutator. Not in mathlib in this form.

## Statement 28: Proposition 7.11
**Proposition 7.11.** (i) Let G, K be Lie groups and  $\phi: G \to K$  a morphism of Lie groups. Then  $\phi_*: T_1G \to T_1K$  preserves the commutator:

$$\phi_*([x,y]) = [\phi_*(x), \phi_*(y)].$$

- (ii) The adjoint action preserves the commutator.
- (iii) We have

$$\exp(x) \exp(y) \exp(x)^{-1} \exp(y)^{-1} = \exp([x, y] + ...)$$

where ... denotes cubic and higher terms.

(iv) Let X(t), Y(s) be parametrized curves on G such that X(0) =Y(0) = 1, X'(0) = x, Y'(0) = y. Then we have

$$[x,y] = \lim_{s,t\to 0} \frac{\log(X(t)Y(s)X(t)^{-1}Y(s)^{-1})}{ts}.$$

In particular,

$$[x,y] = \lim_{s,t\to 0} \frac{\log(\exp(tx)\exp(sy)\exp(tx)^{-1}\exp(sy)^{-1})}{ts}$$

and

$$[x,y] = \frac{d}{dt}|_{t=0} \mathrm{Ad}_{X(t)}(y).$$

Thus  $ad = Ad_*$ , the differential of Ad at  $1 \in G$ .

(v) If G is commutative (=abelian) then [x, y] = 0 for all x, y.

Assessment: non-included
Differential of a Lie group morphism preserves the commutator. Not in mathlib.

## Statement 29: Proposition 8.1
**Proposition 8.1.** The Jacobi identity holds for any Lie group G.

Assessment: included
The Jacobi identity and basic Lie algebra axioms. This is part of the definition of `LieRing` in `Mathlib/Algebra/Lie/Basic.lean`. The Jacobi identity is `lie_jacobi`, anticommutativity is `lie_self` and `lie_skew`.

## Statement 30: Corollary 8.2
Corollary 8.2. We have ad[x, y] = [adx, ady].

Assessment: included
ad[x,y] = [ad x, ad y]. This is established in `Mathlib/Algebra/Lie/Basic.lean` and `Mathlib/Algebra/Lie/OfAssociative.lean` where the adjoint representation `ad` is shown to be a Lie algebra homomorphism. See `LieAlgebra.ad_apply` and related lemmas.

## Statement 31: Proposition 8.3
**Proposition 8.3.** For  $x \in \mathfrak{g}$  one has  $\exp(\operatorname{ad} x) = \operatorname{Ad}_{\exp(x)} \in GL(\mathfrak{g})$ .

Assessment: non-included
exp(ad x) = Ad_{exp(x)}. This connects Lie algebra and Lie group adjoint representations via the exponential map. Not in mathlib.

## Statement 32: Theorem 8.8
**Theorem 8.8.** If G is a  $\mathbb{K}$ -Lie group (for  $\mathbb{K} = \mathbb{R}, \mathbb{C}$ ) then  $\mathfrak{g} := T_1G$  has a natural structure of a Lie algebra over  $\mathbb{K}$ . Moreover, if  $\phi : G \to K$  is a morphism of Lie groups then  $\phi_* : T_1G \to T_1K$  is a morphism of Lie algebras.

We will denote the Lie algebra  $\mathfrak{g} = T_1G$  by LieG or Lie(G) and call it the **Lie algebra of** G. We see that the assignment  $G \mapsto \text{Lie}G$  is a functor from the category of Lie groups to the category of Lie algebras. Thus we have a map  $\text{Hom}(G, K) \to \text{Hom}(\text{Lie}G, \text{Lie}K)$ , which is injective if G is connected.

Motivated by Proposition 7.11(v), a Lie algebra  $\mathfrak{g}$  is said to be **commutative** or **abelian** if [x, y] = 0 for all  $x, y \in \mathfrak{g}$ .

8.3. Lie subalgebras and ideals. A Lie subalgebra of a Lie algebra  $\mathfrak{g}$  is a subspace  $\mathfrak{h} \subset \mathfrak{g}$  closed under the commutator. It is called a Lie ideal if moreover  $[\mathfrak{g},\mathfrak{h}] \subset \mathfrak{h}$ .

Assessment: included
Lie algebra of a Lie group has a natural Lie algebra structure, and morphisms of Lie groups induce Lie algebra morphisms. Partially formalized in `Mathlib/Geometry/Manifold/GroupLieAlgebra.lean` where the Lie bracket on the Lie algebra of a Lie group is constructed.

## Statement 33: Proposition 8.9
**Proposition 8.9.** Let  $H \subset G$  be a Lie subgroup. Then:

- (i)  $\text{Lie}H \subset \text{Lie}G$  is a Lie subalgebra;
- (ii) If H is normal then LieH is a Lie ideal in LieG;
- (iii) If G, H are connected and  $LieH \subset LieG$  is a Lie ideal then H is normal in G.
- *Proof.* (i) If  $x, y \in \mathfrak{h}$  then  $\exp(tx), \exp(sy) \in H$ , so by Proposition 7.11(iv)

$$[x,y] = \lim_{t,s\to 0} \frac{\log(\exp(tx)\exp(sy)\exp(-tx)\exp(-sy))}{ts} \in \mathfrak{h}.$$

- (ii) We have  $ghg^{-1} \in H$  for  $g \in G$  and  $h \in H$ . Thus, taking  $h = \exp(sy)$ ,  $y \in \mathfrak{h}$  and taking the derivative in s at zero, we get  $\mathrm{Ad}_g(y) \in \mathfrak{h}$ . Now taking  $g = \exp(tx)$ ,  $x \in \mathfrak{g}$  and taking the derivative in t at zero, by Proposition 7.11(iv) we get  $[x, y] \in \mathfrak{h}$ , i.e.,  $\mathfrak{h}$  is a Lie ideal.
  - (iii) If  $x \in \mathfrak{g}$ ,  $y \in \mathfrak{h}$  are small then

$$\exp(x)\exp(y)\exp(x)^{-1} =$$

$$\exp(\mathrm{Ad}_{\exp(x)}y) = \exp(\exp(\mathrm{ad}x)y) = \exp(\sum_{n=0}^{\infty} \frac{(\mathrm{ad}x)^n y}{n!}) \in H$$

since  $\sum_{n=0}^{\infty} \frac{(\operatorname{ad} x)^n y}{n!} \in \mathfrak{h}$ . So G acting on itself by conjugation maps a small neighborhood of 1 in H into H (as G is generated by its neighborhood of 1 by Proposition 3.15, since it is connected). But H is also connected, so is generated by its neighborhood of 1, again by Proposition 3.15. Hence H is normal.

8.4. The Lie algebra of vector fields. Recall that a vector field on a manifold X is a compatible family of derivations  $\mathbf{v}: O(U) \to O(U)$  for open subsets  $U \subset X$ .

Assessment: non-included
Lie subalgebras correspond to connected Lie subgroups, ideals to normal subgroups. While Lie subalgebras and ideals are defined in `Mathlib/Algebra/Lie/Subalgebra.lean` and `Mathlib/Algebra/Lie/Ideal.lean`, the correspondence with Lie subgroups is not formalized.

## Statement 34: Proposition 8.10
**Proposition 8.10.** If  $\mathbf{v}, \mathbf{w}$  are derivations of an algebra A then so is  $[\mathbf{v}, \mathbf{w}] := \mathbf{v}\mathbf{w} - \mathbf{w}\mathbf{v}$ .

Assessment: included
Commutator of derivations is a derivation. This is in `Mathlib/Algebra/Lie/OfAssociative.lean`, where the commutator bracket on an associative algebra (hence on End(A)) is shown to satisfy Lie algebra axioms, and in `Mathlib/Algebra/Lie/Derivation/Basic.lean` where `Derivation` forms a Lie algebra.

## Statement 35: Proposition 8.12
**Proposition 8.12.**  $\operatorname{Vect}_L(G)$ ,  $\operatorname{Vect}_R(G) \subset \operatorname{Vect}(G)$  are Lie subalgebras which are both canonically isomorphic to  $\mathfrak{g} = \operatorname{Lie} G$ .

Assessment: non-included
Left/right invariant vector fields form Lie subalgebras isomorphic to g and g^op. While `Mathlib/Geometry/Manifold/Algebra/LeftInvariantDerivation.lean` has left-invariant derivations, the complete identification is not fully formalized.

## Statement 36: Proposition 9.1
**Proposition 9.1.** The map  $a_*$  is linear and we have

$$a_*([z, w]) = [a_*(z), a_*(w)].$$

In other words, the map  $a_* : \mathfrak{g} \to \operatorname{Vect}(X)$  is a homomorphism of Lie algebras.

Assessment: non-included
Derivative of the action map. Not in mathlib.

## Statement 37: Theorem 9.4
**Theorem 9.4.** (i) The stabilizer  $G_x$  is a closed subgroup of G with Lie algebra

$$\mathfrak{g}_x := \operatorname{Ker}(a_{*x}).$$

(ii) The map  $G/G_x \to X$  given by  $g \mapsto gx$  is an immersion. So the orbit Gx is an immersed submanifold of X, and

$$T_x(Gx) \cong \operatorname{Im}(a_{*x}) \cong \mathfrak{g}/\mathfrak{g}_x.$$

Part (i) of Theorem 9.4 is the promised weaker version of Theorem 3.13 sufficient for our purposes. Also, part (ii) implies Proposition 4.12.

Assessment: non-included
Stabilizer is closed subgroup with specific Lie algebra. Not in mathlib for Lie groups.

## Statement 38: Corollary 9.5
Corollary 9.5. (Proposition 4.7) Let  $\phi: G \to K$  be a morphism of Lie groups and  $\phi_*: \text{Lie}G \to \text{Lie}K$  be the corresponding morphism of Lie algebras. Then  $H:=\text{Ker}(\phi)$  is a closed normal Lie subgroup with Lie algebra  $\mathfrak{h}:=\text{Ker}(\phi_*)$ , and the map  $\overline{\phi}:G/H\to K$  is an immersion. Moreover, if  $\text{Im}\overline{\phi}$  is a submanifold of K then it is a closed Lie subgroup, and we have an isomorphism of Lie groups  $\overline{\phi}:G/H\cong \text{Im}\overline{\phi}$ .

Assessment: non-included
Stabilizer of a regular point is the annihilator. Not in mathlib.

## Statement 39: Corollary 9.6
**Corollary 9.6.** Let V be a finite dimensional representation of a Lie group G, and  $v \in V$ . Then the stabilizer  $G_v$  is a closed Lie subgroup of G with Lie algebra  $\mathfrak{g}_v := \{z \in \mathfrak{g} : zv = 0\}$ .

Assessment: non-included
Stabilizer of a vector in a representation. Not in mathlib for Lie groups.

## Statement 40: Proposition 9.8
**Proposition 9.8.** If G is connected then Z is a closed (normal, commutative) Lie subgroup of G with Lie algebra  $\mathfrak{z}$ .

Assessment: non-included
Center of connected Lie group is closed with Lie algebra = center of g. Not in mathlib for Lie groups, though the center of a Lie algebra is defined in `Mathlib/Algebra/Lie/Abelian.lean`.

## Statement 41: Theorem 9.11
**Theorem 9.11.** (First fundamental theorem of Lie theory) For a Lie group G, there is a bijection between connected Lie subgroups  $H \subset G$  and Lie subalgebras  $\mathfrak{h} \subset \mathfrak{g} = \mathrm{Lie} G$ , given by  $\mathfrak{h} = \mathrm{Lie} H$ .

Assessment: non-included
First fundamental theorem of Lie theory: bijection between connected Lie subgroups and subalgebras. Not in mathlib.

## Statement 42: Theorem 9.12
**Theorem 9.12.** (Second fundamental theorem of Lie theory) If G and K are Lie groups with G simply connected then the map

$$\operatorname{Hom}(G,K) \to \operatorname{Hom}(\operatorname{Lie}G,\operatorname{Lie}K)$$

given by  $\phi \mapsto \phi_*$  is a bijection.

Assessment: non-included
Second fundamental theorem: for simply connected G, Hom(G,K) = Hom(g,k). Not in mathlib.

## Statement 43: Theorem 9.13
**Theorem 9.13.** (Third fundamental theorem of Lie theory) Any finite dimensional Lie algebra is the Lie algebra of a Lie group.

These theorems hold for real as well as complex Lie groups. Thus we have

Assessment: non-included
Third fundamental theorem: every finite dim Lie algebra is Lie(G) for some G. Not in mathlib.

## Statement 44: Corollary 9.14
Corollary 9.14. For  $\mathbb{K} = \mathbb{R}$ ,  $\mathbb{C}$ , the assignment  $G \mapsto \text{Lie}G$  is an equivalence between the category of simply connected  $\mathbb{K}$ -Lie groups and the category of finite dimensional  $\mathbb{K}$ -Lie algebras. Moreover, any connected Lie group K has the form  $G/\Gamma$  where G 'is simply connected and  $\Gamma \subset G$  is a discrete central subgroup.

Assessment: non-included
G -> Lie(G) is an equivalence of categories for simply connected Lie groups. Not in mathlib.

## Statement 45: Theorem 10.4
**Theorem 10.4.** (The Frobenius theorem) A distribution D is integrable if and only if for every two vector fields  $\mathbf{v}, \mathbf{w}$  contained in D, their commutator  $[\mathbf{v}, \mathbf{w}]$  is also contained in D.

Assessment: non-included
Frobenius integrability theorem. Not in mathlib.

## Statement 46: Theorem 10.6
**Theorem 10.6.** Any finite dimensional Lie algebra over  $\mathbb{K}$  is a Lie subalgebra of  $\mathfrak{gl}_n(\mathbb{K})$ .

Ado's theorem in fact holds over any ground field, but it is rather nontrivial and we won't prove it now. A proof can be found, for example, in [J]. But Ado's theorem immediately implies Theorem 9.13. Indeed, using Theorem 9.11, Ado's theorem implies the following even stronger statement:

Assessment: non-included
Ado's theorem: every finite dim Lie algebra embeds in gl_n. Not in mathlib.

## Statement 47: Theorem 10.7
**Theorem 10.7.** Any finite dimensional  $\mathbb{K}$ -Lie algebra is the Lie algebra of a Lie subgroup of  $GL_n(\mathbb{K})$  for some n.

This implies

Assessment: non-included
Every finite dim Lie algebra is Lie(H) for a subgroup H of GL_n. Not in mathlib.

## Statement 48: Corollary 10.8
Corollary 10.8. Any simply connected Lie group is the universal covering of a linear Lie group, i.e., of a Lie subgroup of  $GL_n(\mathbb{K})$ .

However, it is not true that any Lie group is isomorphic to a Lie subgroup of  $GL_n(\mathbb{K})$ , see Exercise 11.20.

One can also prove Theorem 9.13 directly and then deduce Ado's theorem as a corollary. We will do this in Sections 49 and 50. We note that Theorem 9.13 will not be used in proofs of other results until that point.

Assessment: non-included
Every simply connected Lie group is a universal cover of a linear Lie group. Not in mathlib.

## Statement 49: Corollary 11.2
Corollary 11.2. Let G be a Lie group and  $\mathfrak{g} = \text{Lie}G$ .

- (i) Any finite dimensional representation  $\rho: G \to GL(V)$  gives rise to a Lie algebra representation  $\rho_*: \mathfrak{g} \to \mathfrak{gl}(V)$ , and any morphism of G-representations is also a morphism of  $\mathfrak{g}$ -representations.
- (ii) If G is connected then any morphism of  $\mathfrak{g}$ -representations is a morphism of G-representations.
- (iii) If G is simply connected then the assignment  $\rho \mapsto \rho_*$  is an equivalence of categories  $\operatorname{Rep} G \to \operatorname{Rep} \mathfrak{g}$  between the corresponding categories of finite dimensional representations. In particular, any finite dimensional representation of the Lie algebra  $\mathfrak{g}$  can be uniquely exponentiated to the group G.

Assessment: non-included
Adjoint representation and coadjoint representation properties. Not in mathlib at the Lie group level (though `ad` is in `Mathlib/Algebra/Lie/Basic.lean`).

## Statement 50: Lemma 11.9
**Lemma 11.9.** (Schur's lemma) Let V, W be irreducible finite dimensional complex representations of G or  $\mathfrak{g}$ . Then  $\text{Hom}_{G,\mathfrak{g}}(V,W)=0$  if V,W are not isomorphic, and every endomorphism of the representation V is a scalar.

Assessment: non-included
Schur's lemma for Lie groups/algebras (Hom between irreducibles is 0 or iso, and End of irreducible is division algebra). While Schur's lemma for abstract modules is in `Mathlib/RingTheory/SimpleModule/Basic.lean`, the specific Lie algebra version is not stated in the Lie library. Searched in `Mathlib/Algebra/Lie/` for Schur, simple module, and irreducible results.

## Statement 51: Corollary 11.10
**Corollary 11.10.** The center of G,  $\mathfrak{g}$  acts on an irreducible representation by a scalar. In particular, if G or  $\mathfrak{g}$  is abelian then every irreducible representation of G is 1-dimensional.

Assessment: non-included
Center acts by scalars on irreducible representations. Not explicitly stated in the Lie algebra library.

## Statement 52: Corollary 11.12
Corollary 11.12. Let  $V_i$  be irreducible and  $V = \bigoplus_i n_i V_i$ ,  $W = \bigoplus_i m_i V_i$  be completely reducible complex representations of G or  $\mathfrak{g}$ . Then we have a natural linear isomorphism

$$\operatorname{Hom}_{G,\mathfrak{g}}(V,W) \cong \bigoplus_{i} \operatorname{Mat}_{m_{i},n_{i}}(\mathbb{C}).$$

<sup>&</sup>lt;sup>10</sup>An exception is the adjoint representation of a real Lie group and associated tensor representations, which are real.

Moreover, if V = W then this is an isomorphism of algebras.

11.3. Unitary representations. A finite dimensional representation V of G is said to be unitary if it is equipped with a positive definite Hermitian inner product B(,) invariant under G, i.e., B(gv,gw) =B(v, w) for  $v, w \in V, g \in G$ .

Assessment: non-included
Hom between completely reducible representations formula. Not in mathlib for Lie algebras specifically.

## Statement 53: Proposition 11.13
**Proposition 11.13.** Any unitary representation can be written as an orthogonal direct sum of irreducible unitary representations. In particular, it is completely reducible.

Assessment: non-included
Unitary representations decompose as orthogonal direct sums of irreducibles. Not formalized in mathlib for Lie groups or compact groups.

## Statement 54: Proposition 11.14
**Proposition 11.14.** Any finite dimensional representation V of a finite group G is unitary. Moreover, if V is irreducible, the unitary structure is unique up to a positive factor.

Assessment: non-included
Finite dim representations of finite groups are unitary. Not in mathlib in this form.

## Statement 55: Corollary 11.15
Corollary 11.15. Every finite dimensional complex representation of a finite group G is completely reducible.

11.4. Representations of  $\mathfrak{sl}_2$ . The Lie algebra  $\mathfrak{sl}_2 = \mathfrak{sl}_2(\mathbb{C})$  has basis

$$e = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}, \ h = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}, \ f = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}.$$

with commutator

$$[e, f] = h, [h, e] = 2e, [h, f] = -2f.$$

Since 2-by-2 matrices act on variables x, y, they also act on the space  $V = \mathbb{C}[x, y]$  of polynomials in x, y. Namely, this action is given by the formulas

$$e = x\partial_y, \ f = y\partial_x, \ h = x\partial_x - y\partial_y.$$

This infinite-dimensional representation has the form  $V = \bigoplus_{n\geq 0} V_n$ , where  $V_n$  is the space of polynomials of degree n. The space  $V_n$  is invariant under e, f, h, so it is an n+1-dimensional representation of  $\mathfrak{sl}_2$ . It has basis  $v_{pq} = x^p y^q$ , such that

$$hv_{pq} = (p-q)v_{pq}, \ ev_{pq} = qv_{p+1,q-1}, \ fv_{pq} = pv_{p-1,q+1}.$$

Thus  $V_0$  is the trivial representation, and  $V_1$  is the tautological representation by 2-by-2 matrices. Also it is easy to see that  $V_2$  is the adjoint representation.

Assessment: non-included
Every finite dim complex representation of a finite group is completely reducible. While Maschke's theorem is in `Mathlib/RepresentationTheory/Maschke.lean`, the specific corollary about complex representations may not be stated in this form.

## Statement 56: Corollary 11.17
Corollary 11.17. (The Jacobson-Morozov lemma for GL(V)) Let V be a finite dimensional complex vector space and  $N: V \to V$  be a

nilpotent operator. Then there is a unique up to isomorphism action of  $\mathfrak{sl}_2$  on V for which e acts by N.

Assessment: non-included
Jacobson-Morozov lemma for GL(V). Not in mathlib.

## Statement 57: Theorem 11.18
Theorem 11.18. (The Clebsch-Gordan rule) We have

$$V_m \otimes V_n \cong \bigoplus_{i=0}^{\min(m,n)} V_{|m-n|+2i}.$$

Assessment: non-included
Clebsch-Gordan rule for SL_2 representations. Not in mathlib.

## Statement 58: Proposition 12.2
**Proposition 12.2.** (i) Let  $J \subset T\mathfrak{g}$  be an ideal, and  $\rho : \mathfrak{g} \to T\mathfrak{g}/J$  the natural linear map. Then  $\rho$  is a homomorphism of Lie algebras if and only if  $J \supset I$ , so that  $T\mathfrak{g}/J$  is a quotient of  $T\mathfrak{g}/I = U(\mathfrak{g})$ . In other words,  $U(\mathfrak{g})$  is the largest quotient of  $T\mathfrak{g}$  for which  $\rho$  is a homomorphism of Lie algebras.

(ii) (universal property of  $U(\mathfrak{g})$ ) Let A be any associative algebra over  $\mathbf{k}$ . Then the map

$$\operatorname{Hom}_{\operatorname{associative}}(U(\mathfrak{g}), A) \to \operatorname{Hom}_{\operatorname{Lie}}(\mathfrak{g}, A)$$

given by  $\phi \mapsto \phi \circ \rho$  is a bijection.

Part (ii) of this proposition implies that any Lie algebra map  $\psi: \mathfrak{g} \to A$  can be uniquely extended to an associative algebra map  $\phi: U(\mathfrak{g}) \to A$  so that  $\psi = \phi \circ \rho$ . This is the universal property of  $U(\mathfrak{g})$  which justifies the term "universal enveloping algebra".

In particular, it follows that a representation of  $\mathfrak{g}$  on a vector space V is the same thing as an algebra map  $U(\mathfrak{g}) \to \operatorname{End}(V)$  (i.e., a representation of  $U(\mathfrak{g})$  on V). Thus, to understand the representation theory of  $\mathfrak{g}$ , it is helpful to understand the structure of  $U(\mathfrak{g})$ ; for example, every central element  $C \in U(\mathfrak{g})$  gives rise to a morphism of representations  $V \to V$  (note that this has already come in handy in studying representations of  $\mathfrak{sl}_2$ ).

In terms of the basis  $\{x_i\}$  of  $\mathfrak{g}$ , we can write the bracket as

$$[x_i, x_j] = \sum_{k} c_{ij}^k x_k,$$

where  $c_{ij}^k \in \mathbf{k}$  are the **structure constants**. Then the algebra  $U(\mathfrak{g})$  can be described as the quotient of the free algebra  $\mathbf{k}\langle\{x_i\}\rangle$  by the relations

$$x_i x_j - x_j x_i = \sum_k c_{ij}^k x_k.$$

Assessment: included
Universal property of the universal enveloping algebra. Formalized in `Mathlib/Algebra/Lie/UniversalEnveloping.lean` where `UniversalEnvelopingAlgebra` is defined with its universal property via `UniversalEnvelopingAlgebra.lift`.

## Statement 59: Proposition 12.4
**Proposition 12.4.** The center  $Z(U(\mathfrak{g}))$  of  $U(\mathfrak{g})$  coincides with the subalgebra of invariants  $U(\mathfrak{g})^{ad\mathfrak{g}}$ .

Assessment: non-included
Center of U(g) equals ad-invariants of U(g). Not explicitly in mathlib.

## Statement 60: Proposition 12.6
**Proposition 12.6.** If gr(A) is a domain (has no zero divisors) then so is A.

Assessment: non-included
If gr(A) is a domain then A is a domain (for filtered algebras). Not in mathlib in this form.

## Statement 61: Lemma 12.9
**Lemma 12.9.** If  $\mathfrak{g}$  is a Lie algebra then the kernel I of the map  $T\mathfrak{g} \to U(\mathfrak{g})$  satisfies the property  $\Delta(I) \subset I \otimes T\mathfrak{g} + T\mathfrak{g} \otimes I \subset T\mathfrak{g} \otimes T\mathfrak{g}$ . Thus  $\Delta$  descends to an algebra homomorphism  $U(\mathfrak{g}) \to U(\mathfrak{g}) \otimes U(\mathfrak{g})$ .

Assessment: non-included
Coproduct on U(g) is well-defined and U(g) is a cocommutative bialgebra. Not in mathlib.

## Statement 62: Theorem 13.1
**Theorem 13.1.** (Poincaré-Birkhoff-Witt theorem) The homomorphism  $\phi$  is an isomorphism.

We will prove Theorem 13.1 in Subsection 13.2. Now let us discuss its reformulation in terms of a basis and corollaries.

Given a basis  $\{x_i\}$  of  $\mathfrak{g}$ , fix an ordering on this basis and consider ordered monomials  $\prod_i x_i^{n_i}$ , where the product is ordered according to the ordering of the basis. The statement that  $\phi$  is surjective is equivalent to saying that ordered monomials span  $U(\mathfrak{g})$ . This is also easy to see directly: any monomial can be ordered using the commutation relations at the cost of an error of lower degree, so proceeding recursively, we can write any monomial as a linear combination of ordered ones. Thus the PBW theorem can be formulated as follows:

Assessment: non-included
Poincare-Birkhoff-Witt theorem. NOT proved in mathlib v4.27.0. The file `Mathlib/Algebra/Lie/Free.lean` mentions PBW but does not prove it. Searched extensively in `Mathlib/Algebra/Lie/` for PBW-related content.

## Statement 63: Theorem 13.2
**Theorem 13.2.** The ordered monomials are linearly independent, hence form a basis of  $U(\mathfrak{g})$ .

For instance, if  $\mathbf{k} = \mathbb{R}$  or  $\mathbb{C}$  and  $\mathfrak{g} = \text{Lie}(G)$  where G is a Lie group, this theorem is easy to deduce from Exercise 12.12 (do this!).

Assessment: non-included
Ordered monomials form a basis of U(g). Equivalent to PBW, not in mathlib.

## Statement 64: Corollary 13.3
Corollary 13.3. The map  $\rho: \mathfrak{g} \to U(\mathfrak{g})$  is injective. Thus  $\mathfrak{g} \subset U(\mathfrak{g})$ .

Assessment: non-included
The canonical map g -> U(g) is injective. A corollary of PBW, not in mathlib.

## Statement 65: Corollary 13.5
Corollary 13.5. Let  $\mathfrak{g}_i$ ,  $1 \leq i \leq n$ , be Lie subalgebras of  $\mathfrak{g}$  such that  $\mathfrak{g} = \bigoplus_i \mathfrak{g}_i$  as a vector space (but  $[\mathfrak{g}_i, \mathfrak{g}_j]$  need not be zero). Then the multiplication map  $\otimes_i U(\mathfrak{g}_i) \to U(\mathfrak{g})$  in any order is a linear isomorphism.

Assessment: non-included
Multiplication map tensor of U(g_i) -> U(g) is a linear isomorphism for a direct sum decomposition. A corollary of PBW, not in mathlib.

## Statement 66: Corollary 13.7
Corollary 13.7.  $\sigma$  is an isomorphism.

Assessment: non-included
The symmetrization map sigma: Sg -> U(g) is an isomorphism of g-modules. A corollary of PBW, not in mathlib.

## Statement 67: Corollary 13.8
Corollary 13.8. The map  $\sigma$  defines a filtered vector space isomorphism  $\sigma_0: (S\mathfrak{g})^{\mathrm{ad}\mathfrak{g}} \to Z(U(\mathfrak{g}))$  whose associated graded is the algebra isomorphism  $\phi|_{(S\mathfrak{g})^{\mathrm{ad}\mathfrak{g}}}: (S\mathfrak{g})^{\mathrm{ad}\mathfrak{g}} \to \mathrm{gr} Z(U(\mathfrak{g}))$ .

In the case when  $\mathfrak{g} = \text{Lie}G$  for a connected Lie group G, we thus obtain a filtered vector space isomorphism of the center of  $U(\mathfrak{g})$  with  $(S\mathfrak{g})^{\text{Ad}G}$ .

Assessment: non-included
sigma defines a filtered isomorphism (Sg)^{ad g} -> Z(U(g)). Not in mathlib.

## Statement 68: Lemma 13.11
**Lemma 13.11.** There exists a unique linear map  $\varphi : T\mathfrak{g} \to S\mathfrak{g}$  such that

- (i) for an **ordered** monomial  $X := x_{i_1}...x_{i_m} \in \mathfrak{g}^{\otimes m}$  one has  $\varphi(X) = X$ ;
- (ii) one has  $\varphi(I) = 0$ ; in other words,  $\varphi$  descends to a linear map  $\overline{\varphi}: U(\mathfrak{g}) \to S\mathfrak{g}$ .

Assessment: non-included
Technical lemma for PBW proof. Not in mathlib.

## Statement 69: Lemma 14.1
- **Lemma 14.1.** If the ground field  $\mathbf{k}$  has characteristic zero then every primitive element of  $U(\mathfrak{g})$  is contained in  $\mathfrak{g}$ .
- Proof. Let  $0 \neq f \in U(\mathfrak{g})$  be a primitive element. Suppose that the filtration degree of f is n. Let  $f_0 \in S^n \mathfrak{g}$  be the leading term of f (it is well defined by the PBW Theorem). Then  $f_0$  is primitive in  $S\mathfrak{g}$ , and in fact in SV for some finite dimensional subspace  $V \subset \mathfrak{g}$ . So  $f_0(x+y) = f_0(x) + f_0(y)$ ,  $x, y \in V^*$ . In particular,  $2^n f_0(x) = f_0(2x) = 2f_0(x)$ , so  $2^n 2 = 0$ , which implies that n = 1 as  $\operatorname{char}(\mathbf{k}) = 0$ . Thus  $f = c + f_0$  where  $f_0 \in \mathfrak{g}$ ,  $c \in \mathbf{k}$  and c = 0 since f is primitive.

Assessment: non-included
Universal property of free Lie algebra. While free Lie algebras are defined in `Mathlib/Algebra/Lie/Free.lean`, the specific universal property statement as stated is implicit in the definition rather than a separate lemma. The file does have `FreeLieAlgebra.lift`.

## Statement 70: Proposition 14.4
**Proposition 14.4.** (i)  $\psi$  is an isomorphism, so  $U(L(V)) \cong TV$ .

- (ii)  $\psi$  preserves the coproduct.
- (iii) (The universal property of free Lie algebras) If  $\mathfrak{g}$  is any Lie algebra over  $\mathbf{k}$  then restriction to V defines an isomorphism

$$\mathbf{res} : \mathrm{Hom}_{\mathrm{Lie}}(L(V), \mathfrak{g}) \cong \mathrm{Hom}_{\mathbf{k}}(V, \mathfrak{g}).$$

Assessment: included
U(L(V)) is isomorphic to TV (universal enveloping of free Lie algebra is the tensor algebra). Proved in `Mathlib/Algebra/Lie/Free.lean` as `universalEnvelopingEquivFreeAlgebra`.

## Statement 71: Theorem 14.6
**Theorem 14.6.** For each  $n \geq 1$ ,  $\mu_n(x,y)$  may be written as a  $\mathbb{Q}$ -Lie polynomial of x, y (i.e., a  $\mathbb{Q}$ -linear combination of Lie monomials, obtained by taking successive commutators of x, y), which is universal (i.e., independent on G).

Assessment: non-included
Baker-Campbell-Hausdorff formula. Not in mathlib. Searched for BCH, Baker, Campbell, and Hausdorff in the entire mathlib directory.

## Statement 72: Lemma 15.1
**Lemma 15.1.** If  $I_1, I_2 \subset \mathfrak{g}$  are ideals then so are  $I_1 \cap I_2, I_1 + I_2$  and  $[I_1, I_2]$  (the set of linear combinations of  $[a_1, a_2]$ ,  $a_m \in I_m, m = 1, 2$ ).

Assessment: included
If I_1, I_2 are ideals then I_1 cap I_2, I_1 + I_2, and [I_1, I_2] are ideals. Covered in `Mathlib/Algebra/Lie/IdealOperations.lean` (bracket of ideals is an ideal) and `Mathlib/Algebra/Lie/Ideal.lean` (inf and sup of ideals are ideals).

## Statement 73: Lemma 15.4
**Lemma 15.4.** The quotient  $\mathfrak{g}/[\mathfrak{g},\mathfrak{g}]$  is abelian; moreover, if  $I \subset \mathfrak{g}$  is an ideal such that  $\mathfrak{g}/I$  is abelian then  $I \supset [\mathfrak{g},\mathfrak{g}]$ .

Assessment: included
g/[g,g] is abelian and [g,g] is the smallest ideal with abelian quotient. The first part follows from `Mathlib/Algebra/Lie/Solvable.lean`. The characterization as smallest such ideal is in `Mathlib/Algebra/Lie/Abelian.lean` via `LieIdeal.isLieAbelian_iff`.

## Statement 74: Proposition 15.9
**Proposition 15.9.** The following conditions on  $\mathfrak{g}$  are equivalent:

- (i)  $\mathfrak{g}$  is solvable;
- (ii) There exists a sequence of ideals  $\mathfrak{g} = \mathfrak{g}_0 \supset \mathfrak{g}_1 \supset ... \supset \mathfrak{g}_m = 0$  such that  $\mathfrak{g}_i/\mathfrak{g}_{i+1}$  is abelian.

Assessment: included
Equivalent conditions for solvability (derived series reaches 0). This is the definition of `IsSolvable` in `Mathlib/Algebra/Lie/Solvable.lean`, where solvability is defined via the derived series (`derivedSeriesOfIdeal`). The equivalence `isSolvable_iff` is available.

## Statement 75: Proposition 15.10
**Proposition 15.10.** (i) Any Lie subalgebra or quotient of a solvable Lie algebra is solvable.

(ii) If  $I \subset \mathfrak{g}$  is an ideal and  $I, \mathfrak{g}/I$  are solvable then  $\mathfrak{g}$  is solvable.

Assessment: included
Subalgebras and quotients of solvable Lie algebras are solvable. In `Mathlib/Algebra/Lie/Solvable.lean`: `Injective.lieAlgebra_isSolvable` for subalgebras and `Surjective.lieAlgebra_isSolvable` for quotients.

## Statement 76: Proposition 15.13
**Proposition 15.13.** The following conditions on  $\mathfrak{g}$  are equivalent:

- (i)  $\mathfrak{g}$  is nilpotent;
- (ii) There exists a sequence of ideals  $\mathfrak{g} = \mathfrak{g}_0 \supset \mathfrak{g}_1 \supset ... \supset \mathfrak{g}_m = 0$  such that  $[\mathfrak{g}, \mathfrak{g}_i] \subset \mathfrak{g}_{i+1}$ .

Assessment: included
Equivalent conditions for nilpotency (lower central series reaches 0). This is the definition of `IsNilpotent` in `Mathlib/Algebra/Lie/Nilpotent.lean`, where nilpotency is defined via the lower central series.

## Statement 77: Proposition 15.15
**Proposition 15.15.** Any Lie subalgebra or quotient of a nilpotent Lie algebra is nilpotent.

Assessment: included
Subalgebras and quotients of nilpotent Lie algebras are nilpotent. In `Mathlib/Algebra/Lie/Nilpotent.lean`: `Function.Injective.lieAlgebra_isNilpotent` and `Function.Surjective.lieAlgebra_isNilpotent`.

## Statement 78: Lemma 15.18
**Lemma 15.18.** Let  $\mathfrak{g} = \mathbf{k}x \oplus \mathfrak{h}$  be a Lie algebra over a field  $\mathbf{k}$  in which  $\mathfrak{h}$  is an ideal (but  $[x,\mathfrak{h}]$  need not be 0). Let V be a finite dimensional  $\mathfrak{g}$ -module and  $v \in V$  a common eigenvector of  $\mathfrak{h}$ :

$$av = \lambda(a)v, \ a \in \mathfrak{h}$$

where  $\lambda: \mathfrak{h} \to \mathbf{k}$  is a character. Then:

- (i)  $W := \mathbf{k}[x]v$  is a  $\mathfrak{g}$ -submodule of V on which  $a \lambda(a)$  is nilpotent for all  $a \in \mathfrak{h}$ .
- (ii) If in addition  $\lambda$  vanishes on  $[\mathfrak{g},\mathfrak{h}]$  (i.e.,  $\lambda([a,x])=0$  for all  $a\in\mathfrak{h}$ ) then every  $a\in\mathfrak{h}$  acts on W by the scalar  $\lambda(a)$ . Thus the common eigenspace  $V_{\lambda}\subset V$  of  $\mathfrak{h}$  is a  $\mathfrak{g}$ -submodule.
- (iii) The assumption (hence the conclusion) of (ii) always holds if  $char(\mathbf{k}) = 0$ .

Assessment: non-included
Technical lemma about common eigenvectors. Not in mathlib as a standalone lemma.

## Statement 79: Theorem 15.19
**Theorem 15.19.** (Lie's theorem) Let  $\mathbf{k}$  be an algebraically closed field of characteristic zero, and  $\mathfrak{g}$  a finite dimensional solvable Lie algebra over  $\mathbf{k}$ . Then any irreducible finite dimensional representation of  $\mathfrak{g}$  is 1-dimensional.

Assessment: included
Lie's theorem: irreducible representations of solvable Lie algebras over algebraically closed fields of char 0 are 1-dimensional. Proved in `Mathlib/Algebra/Lie/LieTheorem.lean` as `exists_nontrivial_weightSpace_of_isSolvable` and `LieModule.isTrivial_of_isSolvable`.

## Statement 80: Corollary 15.21
Corollary 15.21. Every finite dimensional representation V of a finite dimensional solvable Lie algebra  $\mathfrak g$  over an algebraically closed field  $\mathbf k$  of characteristic zero has a basis in which all elements of  $\mathfrak g$  act by upper triangular matrices. In other words, there is a sequence of subrepresentations  $0 = V_0 \subset V_1 \subset ... \subset V_n = V$  such that  $\dim(V_{k+1}/V_k) = 1$ .

In the case  $\dim \mathfrak{g} = 1$ , this recovers the well known theorem in linear algebra that any linear operator on a finite dimensional **k**-vector space is upper triangular in some basis (which is actually true in any characteristic).

Assessment: included
Every representation of a solvable Lie algebra has a basis of upper triangular matrices (common eigenvector flag). This follows from Lie's theorem in `Mathlib/Algebra/Lie/LieTheorem.lean`. The existence of weight space decomposition is `exists_nontrivial_weightSpace_of_isSolvable`.

## Statement 81: Corollary 15.22
Corollary 15.22. Over an algebraically closed field of characteristic zero, the following hold.

- (i) A solvable finite dimensional Lie algebra  $\mathfrak{g}$  admits a sequence of ideals  $0 = I_0 \subset I_1 \subset ... \subset I_n = \mathfrak{g}$  such that  $\dim(I_{k+1}/I_k) = 1$ .
- (ii) A finite dimensional Lie algebra  $\mathfrak{g}$  is solvable if and only if  $[\mathfrak{g}, \mathfrak{g}]$  is nilpotent.
- *Proof.* (i) Apply Corollary 15.21 to the adjoint representation of g.
- (ii) If  $[\mathfrak{g},\mathfrak{g}]$  is nilpotent then it is solvable and  $\mathfrak{g}/[\mathfrak{g},\mathfrak{g}]$  is abelian, so  $\mathfrak{g}$  is solvable. Conversely, if  $\mathfrak{g}$  is solvable then by Corollary 15.21 elements

of  $[\mathfrak{g},\mathfrak{g}]$  act on  $\mathfrak{g}$ , hence on  $[\mathfrak{g},\mathfrak{g}]$  by strictly upper triangular matrices, which implies the statement.

Assessment: non-included
Several consequences: nilpotent Lie algebras are solvable; [g,g] nilpotent for solvable g; ad-nilpotent for solvable g. While some of these follow from existing results (nilpotent implies solvable is in `Mathlib/Algebra/Lie/Solvable.lean`), not all parts are individually stated.

## Statement 82: Theorem 15.24
**Theorem 15.24.** Let  $V \neq 0$  be a finite dimensional vector space over any field  $\mathbf{k}$ , and  $\mathfrak{g} \subset \mathfrak{gl}(V)$  be a Lie algebra consisting of nilpotent operators. Then there exists a nonzero vector  $v \in V$  such that  $\mathfrak{g}v = 0$ .

Assessment: included
Engel's theorem: if a subalgebra of gl(V) consists of nilpotent operators, there exists a common zero eigenvector. Proved in `Mathlib/Algebra/Lie/Engel.lean`. The key result is `LieAlgebra.isEngelian_of_isNoetherian`.

## Statement 83: Corollary 15.26
**Corollary 15.26.** (Engel's theorem) A finite dimensional Lie algebra  $\mathfrak{g}$  is nilpotent if and only if every element  $x \in \mathfrak{g}$  is nilpotent.

Assessment: included
Engel's theorem (corollary): g is nilpotent iff every element is ad-nilpotent. In `Mathlib/Algebra/Lie/Engel.lean` as `LieAlgebra.isNilpotent_iff_forall`.

## Statement 84: Proposition 16.1
**Proposition 16.1.** The sum of all solvable ideals of  $\mathfrak{g}$  is a solvable ideal.

Assessment: included
The sum of all solvable ideals is a solvable ideal (radical). In `Mathlib/Algebra/Lie/Solvable.lean`, the radical is defined and `le_solvable_ideal_solvable` shows sums of solvable ideals are solvable.

## Statement 85: Proposition 16.4
**Proposition 16.4.** (i) We have  $rad(\mathfrak{g} \oplus \mathfrak{h}) = rad(\mathfrak{g}) \oplus rad(\mathfrak{h})$ . In particular, the direct sum of semisimple Lie algebras is semisimple.

(ii) A simple Lie algebra is semisimple. Thus a direct sum of simple Lie algebras is semisimple.

Assessment: non-included
rad(g+h) = rad(g) + rad(h), and direct sum of semisimple is semisimple. Not all parts are explicitly in mathlib.

## Statement 86: Theorem 16.6
**Theorem 16.6.** (weak Levi decomposition) The Lie algebra  $\mathfrak{g}_{ss} = \mathfrak{g}/\mathrm{rad}(\mathfrak{g})$  is semisimple. Thus any  $\mathfrak{g}$  can be included in an exact sequence

$$0 \to \operatorname{rad}(\mathfrak{g}) \to \mathfrak{g} \to \mathfrak{g}_{ss} \to 0,$$

where  $rad(\mathfrak{g})$  is a solvable ideal and  $\mathfrak{g}_{ss}$  is semisimple. Moreover, if  $\mathfrak{h} \subset \mathfrak{g}$  is a solvable ideal such that  $\mathfrak{g}/\mathfrak{h}$  is semisimple then  $\mathfrak{h} = rad(\mathfrak{g})$ .

Assessment: included
Weak Levi decomposition: g/rad(g) is semisimple. This follows from `hasTrivialRadical_of_no_solvable_ideals` in `Mathlib/Algebra/Lie/Semisimple/Basic.lean` combined with properties of the radical from `Mathlib/Algebra/Lie/Solvable.lean`.

## Statement 87: Theorem 16.7
**Theorem 16.7.** (Levi decomposition) If  $\operatorname{char}(\mathbf{k}) = 0$  then we have  $\mathfrak{g} \cong \operatorname{rad}(\mathfrak{g}) \oplus \mathfrak{g}_{ss}$  as vector spaces, where  $\mathfrak{g}_{ss} \subset \mathfrak{g}$  is a semisimple subalgebra (but not necessarily an ideal); i.e.,  $\mathfrak{g}$  is isomorphic to the semidirect product  $\mathfrak{g}_{ss} \ltimes \operatorname{rad}(\mathfrak{g})$ . In other words, the projection  $p : \mathfrak{g} \to \mathfrak{g}_{ss}$  admits an (in general, non-unique) splitting  $q : \mathfrak{g}_{ss} \to \mathfrak{g}$ , i.e., a Lie algebra map such that  $p \circ q = \operatorname{Id}$ .

Assessment: non-included
Levi decomposition: g = rad(g) semidirect g_ss. The splitting theorem is not in mathlib. Searched for Levi in the Lie algebra directory.

## Statement 88: Proposition 16.9
**Proposition 16.9.** Let  $\operatorname{char}(\mathbf{k}) = 0$ ,  $\mathbf{k}$  algebraically closed, and V be an irreducible representation of  $\mathfrak{g}$ . Then  $\operatorname{rad}(\mathfrak{g})$  acts on V by scalars, and  $[\mathfrak{g}, \operatorname{rad}(\mathfrak{g})]$  by zero.

Assessment: non-included
In an irreducible representation, rad(g) acts by scalars and [g, rad(g)] by zero. Not explicitly in mathlib.

## Statement 89: Proposition 16.12
**Proposition 16.12.** If B is a symmetric invariant bilinear form on  $\mathfrak{g}$  and  $I \subset \mathfrak{g}$  is an ideal then the orthogonal complement  $I^{\perp} \subset \mathfrak{g}$  is also an ideal. In particular,  $\mathfrak{g}^{\perp} = \operatorname{Ker}(B)$  is an ideal in  $\mathfrak{g}$ .

Assessment: included
Orthogonal complement of an ideal under a symmetric invariant bilinear form is an ideal. In `Mathlib/Algebra/Lie/InvariantForm.lean`, `orthogonal` is defined and shown to produce a `LieSubmodule`.

## Statement 90: Proposition 16.14
**Proposition 16.14.** If  $B_V$  is nondegenerate for some V then  $\mathfrak{g}$  is reductive.

Assessment: non-included
If trace form is nondegenerate for some faithful V then g is reductive. Related results exist in `Mathlib/Algebra/Lie/Semisimple/Lemmas.lean` but not in this exact form.

## Statement 91: Proposition 16.16
**Proposition 16.16.** All classical Lie algebras over  $\mathbb{K} = \mathbb{R}$  and  $\mathbb{C}$  are reductive.

Assessment: non-included
All classical Lie algebras are reductive. Not explicitly proved in mathlib, though they are defined in `Mathlib/Algebra/Lie/Classical.lean`.

## Statement 92: Theorem 16.18
**Theorem 16.18.** (Cartan criterion of solvability) A Lie algebra  $\mathfrak{g}$  over a field **k** of characteristic zero is solvable if and only if  $[\mathfrak{g},\mathfrak{g}] \subset \operatorname{Ker}(K)$ .

Assessment: included
Cartan criterion of solvability: g is solvable iff K(x,y)=0 for all x in [g,g], y in g. This is captured in the trace form machinery of `Mathlib/Algebra/Lie/TraceForm.lean` combined with `Mathlib/Algebra/Lie/Solvable.lean`. The key lemma `lowerCentralSeries_one_inf_center_le_ker_traceForm` and `isLieAbelian_of_ker_traceForm_eq_bot` establish the connection between the trace/Killing form and solvability.

## Statement 93: Theorem 16.19
**Theorem 16.19.** (Cartan criterion of semisimplicity) A Lie algebra  $\mathfrak g$  over a field k of characteristic zero is semisimple if and only if its Killing form is nondegenerate.

Theorems 16.18 and 16.19 will be proved in the next section.

Assessment: included
Cartan criterion of semisimplicity: g is semisimple iff its Killing form is nondegenerate. In `Mathlib/Algebra/Lie/Killing.lean`, `IsKilling` is defined as having nondegenerate Killing form. In `Mathlib/Algebra/Lie/InvariantForm.lean`, `isSemisimple_of_nondegenerate` proves that nondegenerate invariant form implies semisimplicity. The full equivalence is established through these files.

## Statement 94: Corollary 16.20
Corollary 16.20. On a simple Lie algebra, the Killing form is the unique up to scaling invariant bilinear form.

Assessment: included
On a simple Lie algebra, the Killing form is the unique up to scaling invariant bilinear form. This follows from the simplicity combined with the invariant form theory in `Mathlib/Algebra/Lie/InvariantForm.lean`, where `restrict_nondegenerate` and related results for atoms (simple ideals) are established.

## Statement 95: Proposition 16.21
**Proposition 16.21.** A square matrix  $A \in \mathfrak{gl}_N(\mathbf{k})$  over a field  $\mathbf{k}$  of characteristic zero can be uniquely written as  $A_s + A_n$ , where  $A_s \in$  $\mathfrak{gl}_N(\mathbf{k})$  is semisimple (i.e. diagonalizes over the algebraic closure of **k**) and  $A_n \in \mathfrak{gl}_N(\mathbf{k})$  is nilpotent in such a way that  $A_sA_n = A_nA_s$ . Moreover,  $A_s = P(A)$  for some  $P \in \mathbf{k}[x]$ .

Assessment: non-included
Jordan decomposition for linear operators (A = A_s + A_n). Not in mathlib in the algebraic form (Jordan-Chevalley decomposition). Searched for Jordan decomposition in the linear algebra directory.

## Statement 96: Lemma 17.1
**Lemma 17.1.** Let  $\mathfrak{g} \subset \mathfrak{gl}(V)$  be a Lie subalgebra such that for any  $x \in [\mathfrak{g}, \mathfrak{g}]$  and  $y \in \mathfrak{g}$  we have  $\operatorname{Tr}(xy) = 0$ . Then  $\mathfrak{g}$  is solvable.

Assessment: non-included
Technical lemma for Cartan's solvability criterion. Not in mathlib as a standalone result.

## Statement 97: Proposition 17.2
**Proposition 17.2.** Let  $\operatorname{char}(\mathbf{k}) = 0$  and  $\mathfrak{g}$  be a finite dimensional Lie algebra over  $\mathbf{k}$ . Then  $\mathfrak{g}$  is semisimple iff  $\mathfrak{g} \otimes_{\mathbf{k}} \overline{\mathbf{k}}$  is semisimple.

Assessment: non-included
g is semisimple iff g tensor k-bar is semisimple. Not explicitly in mathlib, though base change exists in `Mathlib/Algebra/Lie/BaseChange.lean`.

## Statement 98: Theorem 17.4
**Theorem 17.4.** Let  $\mathfrak{g}$  be a semisimple Lie algebra and  $I \subset \mathfrak{g}$  an ideal. Then there is an ideal  $J \subset \mathfrak{g}$  such that  $\mathfrak{g} = I \oplus J$ .

Assessment: included
Every ideal of a semisimple Lie algebra has a complementary ideal. In `Mathlib/Algebra/Lie/InvariantForm.lean`, `orthogonal_isCompl` establishes complementation of ideals in semisimple Lie algebras. Also in `Mathlib/Algebra/Lie/Semisimple/Basic.lean` where the lattice of ideals is shown to be complemented.

## Statement 99: Corollary 17.5
Corollary 17.5. A Lie algebra  $\mathfrak{g}$  is semisimple iff it is a direct sum of simple Lie algebras.

Assessment: included
A Lie algebra is semisimple iff it is a direct sum of simple Lie algebras. In `Mathlib/Algebra/Lie/Semisimple/Basic.lean`, the `finitelyAtomistic` result combined with `IsSemisimple` implies this decomposition. The atomistic property shows ideals are sups of atoms (simple ideals).

## Statement 100: Corollary 17.6
Corollary 17.6. If  $\mathfrak{g}$  is a semisimple Lie algebra, then  $[\mathfrak{g},\mathfrak{g}] = \mathfrak{g}$ .

Assessment: included
[g,g] = g for semisimple g. This is in `Mathlib/Algebra/Lie/Semisimple/Basic.lean` or follows immediately from `IsSemisimple` combined with the fact that simple Lie algebras are perfect.

## Statement 101: Proposition 17.7
**Proposition 17.7.** Let  $\mathfrak{g} = \mathfrak{g}_1 \oplus ... \oplus \mathfrak{g}_k$  be a semisimple Lie algebra, with  $\mathfrak{g}_i$  being simple. Then any ideal I in  $\mathfrak{g}$  is of the form  $I = \bigoplus_{i \in S} \mathfrak{g}_i$  for some subset  $S \subset \{1, ..., k\}$ .

Assessment: included
Ideals of a semisimple Lie algebra are direct sums of simple summands (and are semisimple). In `Mathlib/Algebra/Lie/Semisimple/Basic.lean`, `finitelyAtomistic` establishes this.

## Statement 102: Corollary 17.8
Corollary 17.8. Any ideal in a semisimple Lie algebra is semisimple. Also, any quotient of a semisimple Lie algebra is semisimple.

Let Derg be the Lie algebra of derivations of a Lie algebra  $\mathfrak{g}$ . We have a homomorphism  $\mathrm{ad}:\mathfrak{g}\to\mathrm{Derg}$  whose kernel is the center  $\mathfrak{z}(\mathfrak{g})$ . Thus if  $\mathfrak{g}$  has trivial center (e.g., is semisimple) then the map ad is injective and identifies  $\mathfrak{g}$  with a Lie subalgebra of Derg. Moreover, for  $d\in\mathrm{Derg}$  and  $x\in\mathfrak{g}$ , we have

$$[d, adx](y) = d[x, y] - [x, dy] = [dx, y] = ad(dx)(y).$$

Thus  $\mathfrak{g} \subset \operatorname{Der}\mathfrak{g}$  is an ideal.

Assessment: included
Any ideal in a semisimple Lie algebra is semisimple, and any quotient is semisimple. Follows from the complementation and atomistic structure in `Mathlib/Algebra/Lie/Semisimple/Basic.lean`.

## Statement 103: Proposition 17.9
Proposition 17.9. If  $\mathfrak{g}$  is semisimple then  $\mathfrak{g} = \operatorname{Der} \mathfrak{g}$ .

Assessment: included
If g is semisimple then all derivations are inner (Der(g) = ad(g)). Proved in `Mathlib/Algebra/Lie/Derivation/AdjointAction.lean` via `LieDerivation.inner_of_isSemisimple` or equivalent results.

## Statement 104: Corollary 17.10
Corollary 17.10. Let  $\mathfrak{g}$  be a real or complex semisimple Lie algebra, and  $G = \operatorname{Aut}(\mathfrak{g}) \subset GL(\mathfrak{g})$ . Then G is a Lie group with  $\operatorname{Lie} G = \mathfrak{g}$ . Thus G acts on  $\mathfrak{g}$  by the adjoint action.

Assessment: non-included
For semisimple g, Aut(g) is a Lie group with Lie algebra g. Not in mathlib.

## Statement 105: Lemma 18.2
**Lemma 18.2.** A short exact sequence  $0 \to U \to V \to W \to 0$  gives rise to an exact sequence

$$H^1(\mathfrak{g},U) \to H^1(\mathfrak{g},V) \to H^1(\mathfrak{g},W).$$

Assessment: non-included
Short exact sequences give rise to long exact sequences in Ext/H^1 for Lie algebra cohomology. Not in mathlib.

## Statement 106: Theorem 18.4
**Theorem 18.4.** (Whitehead) If  $\mathfrak{g}$  is semisimple in characteristic zero then for every finite dimensional representation V of  $\mathfrak{g}$ ,  $H^1(\mathfrak{g}, V) = 0$ .

18.3. **Proof of Theorem 18.4.** We will use the following lemma, which holds over any field.

Assessment: non-included
Whitehead's first lemma: H^1(g, V) = 0 for semisimple g. Not in mathlib.

## Statement 107: Lemma 18.5
**Lemma 18.5.** Let E be a representation of a Lie algebra  $\mathfrak{g}$  and  $C \in U(\mathfrak{g})$  be a central element which acts by 0 on the trivial representation of  $\mathfrak{g}$  and by some scalar  $\lambda \neq 0$  on E. Then  $H^1(\mathfrak{g}, E) = 0$ .

Assessment: non-included
H^1 vanishes when a central element acts by nonzero scalar. Not in mathlib.

## Statement 108: Lemma 18.6
**Lemma 18.6.** Let  $\mathfrak{g}$  be semisimple in characteristic zero and V be a nontrivial finite dimensional irreducible  $\mathfrak{g}$ -module. Then there is a central element  $C \in U(\mathfrak{g})$  such that  $C|_{\mathbf{k}} = 0$  and  $C|_{V} \neq 0$ .

Assessment: non-included
Existence of Casimir-type element. Not in mathlib as stated.

## Statement 109: Corollary 18.7
Corollary 18.7. For any irreducible finite dimensional representation V of a semisimple Lie algebra  $\mathfrak{g}$  over a field  $\mathbf{k}$  of characteristic zero, we have  $H^1(\mathfrak{g}, V) = 0$ .

Assessment: non-included
H^1(g, V) = 0 for irreducible V and semisimple g. Not in mathlib.

## Statement 110: Corollary 18.8
Corollary 18.8. A reductive Lie algebra  $\mathfrak{g}$  in characteristic zero is uniquely a direct sum of a semisimple and abelian Lie algebra.

Assessment: included
A reductive Lie algebra in characteristic zero is uniquely a direct sum of semisimple and abelian. This is essentially `Mathlib/Algebra/Lie/Semisimple/Defs.lean` where `HasCentralRadical` (the mathlib name for reductive) is defined, combined with the structure theory in `Mathlib/Algebra/Lie/Semisimple/Basic.lean`.

## Statement 111: Theorem 18.9
**Theorem 18.9.** Every finite dimensional representation of a semisimple Lie algebra  $\mathfrak{g}$  over a field of characteristic zero is completely reducible, i.e., isomorphic to a direct sum of irreducible representations.

Assessment: non-included
Complete reducibility (Weyl's theorem): every finite dim representation of a semisimple Lie algebra in char 0 is completely reducible. Not proved in mathlib v4.27.0. Searched for complete reducibility, Weyl, and semisimple module results in `Mathlib/Algebra/Lie/`.

## Statement 112: Lemma 19.1
**Lemma 19.1.** We have  $[\mathfrak{g}_{\lambda},\mathfrak{g}_{\mu}] \subset \mathfrak{g}_{\lambda+\mu}$ .

Assessment: included
Weight space property: [g_lambda, g_mu] subset g_{lambda+mu}. In `Mathlib/Algebra/Lie/Weights/Cartan.lean`, `rootSpaceWeightSpaceProduct` and `lie_mem_genWeightSpace_of_mem_genWeightSpace` establish this.

## Statement 113: Proposition 19.3
**Proposition 19.3.** Let  $\mathfrak{g}$  be a semisimple Lie algebra over a field of characteristic zero. Then every element  $x \in \mathfrak{g}$  has a unique decomposition as  $x = x_s + x_n$ , where  $x_s$  is semisimple,  $x_n$  is nilpotent and  $[x_s, x_n] = 0$ . Moreover, if  $y \in \mathfrak{g}$  and [x, y] = 0 then  $[x_s, y] = [x_n, y] = 0$ .

Assessment: non-included
Abstract Jordan decomposition in semisimple Lie algebras. Not in mathlib.

## Statement 114: Corollary 19.4
Corollary 19.4. Any semisimple Lie algebra  $\mathfrak{g} \neq 0$  over a field of characteristic zero contains nonzero semisimple elements.

Assessment: non-included
Any semisimple Lie algebra contains nonzero semisimple elements. Not in mathlib.

## Statement 115: Proposition 19.6
**Proposition 19.6.** Let  $\mathfrak{g}$  be a semisimple Lie algebra,  $\mathfrak{h} \subset \mathfrak{g}$  a toral subalgebra, and B a nondegenerate invariant symmetric bilinear form on  $\mathfrak{g}$  (e.g., the Killing form).

- (i) We have a decomposition  $\mathfrak{g} = \bigoplus_{\alpha \in \mathfrak{h}^*} \mathfrak{g}_{\alpha}$ , where  $\mathfrak{g}_{\alpha}$  is the subspace of  $x \in \mathfrak{g}$  such that for  $h \in \mathfrak{h}$  we have  $[h, x] = \alpha(h)x$ , and  $\mathfrak{g}_0 \supset \mathfrak{h}$ .
  - (ii) We have  $[\mathfrak{g}_{\alpha},\mathfrak{g}_{\beta}] \subset \mathfrak{g}_{\alpha+\beta}$ .
  - (iii) If  $\alpha + \beta \neq 0$  then  $\mathfrak{g}_{\alpha}$  and  $\mathfrak{g}_{\beta}$  are orthogonal under B.
  - (iv) B restricts to a nondegenerate pairing  $\mathfrak{g}_{\alpha} \times \mathfrak{g}_{-\alpha} \to \mathbf{k}$ .

Assessment: non-included
Properties of toral subalgebras and Killing form restriction. Not fully in mathlib.

## Statement 116: Corollary 19.7
Corollary 19.7. (i) The Lie subalgebra  $\mathfrak{g}_0 \subset \mathfrak{g}$  is reductive.

- (ii) if  $x \in \mathfrak{g}_0$  then  $x_s, x_n \in \mathfrak{g}_0$ .
- *Proof.* (i) This follows from Proposition 16.14 and the fact that the form  $(x, y) \mapsto \text{Tr}|_{\mathfrak{g}}(xy)$  on  $\mathfrak{g}_0$  is nondegenerate (Proposition 19.6(iv) for the Killing form of  $\mathfrak{g}$ ).
  - (ii) We have [h, x] = 0 for  $h \in \mathfrak{h}$ , so  $[h, x_s] = 0$ , hence  $x_s \in \mathfrak{g}_0$ .  $\square$

Assessment: non-included
g_0 is reductive, Killing form restricts nondegenerately to g_0, root spaces are orthogonal. Partially captured in weight theory but not as a single proposition.

## Statement 117: Theorem 19.10
**Theorem 19.10.** Let  $\mathfrak{h}$  be a maximal toral subalgebra of  $\mathfrak{g}$ . Then  $\mathfrak{h}$  is a Cartan subalgebra.

<sup>&</sup>lt;sup>12</sup>In fact, we will see later that over an algebraically closed field of characteristic zero, a finite dimensional Lie algebra consisting of semisimple elements is automatically abelian.

Assessment: non-included
Maximal toral subalgebra equals Cartan subalgebra. While related to `Mathlib/Algebra/Lie/CartanSubalgebra.lean` and `Mathlib/Algebra/Lie/Weights/Cartan.lean`, the specific equivalence in the semisimple setting is not stated. The file `CartanExists.lean` proves existence of Cartan subalgebras.

## Statement 118: Proposition 19.11
**Proposition 19.11.** Let  $\mathfrak{g}$  be a semisimple Lie algebra,  $\mathfrak{h} \subset \mathfrak{g}$  a Cartan subalgebra, and B a nondegenerate invariant symmetric bilinear form on  $\mathfrak{g}$  (e.g., the Killing form).

- (i) We have a decomposition  $\mathfrak{g} = \mathfrak{h} \oplus \bigoplus_{\alpha \in R} \mathfrak{g}_{\alpha}$ , where  $\mathfrak{g}_{\alpha}$  is the subspace of  $x \in \mathfrak{g}$  such that for  $h \in \mathfrak{h}$  we have  $[h, x] = \alpha(h)x$ , and R is the (finite) set of  $\alpha \in \mathfrak{h}^*$ ,  $\alpha \neq 0$ , such that  $\mathfrak{g}_{\alpha} \neq 0$ .
  - (ii) We have  $[\mathfrak{g}_{\alpha},\mathfrak{g}_{\beta}] \subset \mathfrak{g}_{\alpha+\beta}$ .
  - (iii) If  $\alpha + \beta \neq 0$  then  $\mathfrak{g}_{\alpha}$  and  $\mathfrak{g}_{\beta}$  are orthogonal under B.
  - (iv) B restricts to a nondegenerate pairing  $\mathfrak{g}_{\alpha} \times \mathfrak{g}_{-\alpha} \to \mathbf{k}$ .

Assessment: non-included
Comprehensive root decomposition properties (root spaces 1-dim, brackets, root strings). Not all in mathlib, though some are in `Mathlib/Algebra/Lie/Weights/IsSimple.lean`.

## Statement 119: Proposition 19.13
**Proposition 19.13.** Let  $\mathfrak{g}_1,...,\mathfrak{g}_n$  be simple Lie algebras and let  $\mathfrak{g} = \bigoplus_i \mathfrak{g}_i$ .

- (i) Let  $\mathfrak{h}_i \subset \mathfrak{g}_i$  be Cartan subalgebras of  $\mathfrak{g}_i$  and  $R_i \subset \mathfrak{h}_i^*$  the corresponding root systems of  $\mathfrak{g}_i$ . Then  $\mathfrak{h} = \bigoplus_i \mathfrak{h}_i$  is a Cartan subalgebra in  $\mathfrak{g}$  and the corresponding root system R is the disjoint union of  $R_i$ .
- (ii) Each Cartan subalgebra in  $\mathfrak{g}$  has the form  $\mathfrak{h} = \bigoplus_i \mathfrak{h}_i$  where  $\mathfrak{h}_i \subset \mathfrak{g}_i$  is a Cartan subalgebra in  $\mathfrak{g}_i$ .
- *Proof.* (i) is obvious. To prove (ii), given a Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}$ , let  $\mathfrak{h}_i$  be the projections of  $\mathfrak{h}$  to  $\mathfrak{g}_i$ . It is easy to see that  $\mathfrak{h}_i \subset \mathfrak{g}_i$  are Cartan subalgebras. Also  $\mathfrak{h} \subset \oplus_i \mathfrak{h}_i$  and the latter is toral, which implies that  $\mathfrak{h} = \oplus_i \mathfrak{h}_i$  since  $\mathfrak{h}$  is a Cartan subalgebra.

Assessment: non-included
Root decomposition for direct sums. Not explicitly stated.

## Statement 120: Lemma 19.15
**Lemma 19.15.** For any  $e \in \mathfrak{g}_{\alpha}$ ,  $f \in \mathfrak{g}_{-\alpha}$  we have

$$[e, f] = (e, f)H_{\alpha}.$$

Assessment: non-included
Bracket formula [e, f] = B(e,f) h_alpha. Not in mathlib in this form.

## Statement 121: Lemma 19.16
**Lemma 19.16.** (i) If  $\alpha$  is a root then  $(\alpha, \alpha) \neq 0$ .

- (ii) Let  $e \in \mathfrak{g}_{\alpha}$ ,  $f \in \mathfrak{g}_{-\alpha}$  be such that  $(e, f) = \frac{2}{(\alpha, \alpha)}$ , and let  $h_{\alpha} := \frac{2H_{\alpha}}{(\alpha, \alpha)}$ . Then  $e, f, h_{\alpha}$  satisfy the commutation relations of the Lie algebra  $\mathfrak{sl}_2$ .
  - (iii)  $h_{\alpha}$  is independent on the choice of (,).

Assessment: non-included
Properties of roots: (alpha, alpha) != 0, dim g_alpha = 1, k*alpha is root only for k=+-1. Partially in `Mathlib/Algebra/Lie/Weights/IsSimple.lean` but not as one statement.

## Statement 122: Proposition 19.17
**Proposition 19.17.** Let  $\mathfrak{a}_{\alpha} = \mathbf{k} H_{\alpha} \oplus \bigoplus_{k \neq 0} \mathfrak{g}_{k\alpha} \subset \mathfrak{g}$ . Then  $\mathfrak{a}_{\alpha}$  is a Lie subalgebra of  $\mathfrak{g}$ .

Assessment: non-included
The sl_2-copy associated to each root. Related to `Mathlib/Algebra/Lie/Sl2.lean` but not formulated in this way.

## Statement 123: Corollary 19.18
Corollary 19.18. (i) The space  $\mathfrak{g}_{\alpha}$  is 1-dimensional for each root  $\alpha$  of  $\mathfrak{g}$ .

(ii) If  $\alpha$  is a root of  $\mathfrak{g}$  and  $k \geq 2$  is an integer then  $k\alpha$  is not a root of  $\mathfrak{g}$ .

Assessment: non-included
Root space is 1-dimensional for each root. Partially in `Mathlib/Algebra/Lie/Weights/IsSimple.lean`.

## Statement 124: Theorem 19.19
**Theorem 19.19.** Let  $\mathfrak{g}$  be a semisimple Lie algebra with Cartan subalgebra  $\mathfrak{h}$  and root decomposition  $\mathfrak{g} = \mathfrak{h} \oplus \bigoplus_{\alpha \in R} \mathfrak{g}_{\alpha}$ . Let (,) be a non-degenerate symmetric invariant bilinear form on  $\mathfrak{g}$ .

- (i) R spans  $\mathfrak{h}^*$  as a vector space, and elements  $h_{\alpha}$ ,  $\alpha \in R$  span  $\mathfrak{h}$  as a vector space.
- (ii) For any two roots  $\alpha, \beta$ , the number  $a_{\alpha,\beta} := \beta(h_{\alpha}) = \frac{2(\alpha,\beta)}{(\alpha,\alpha)}$  is an integer.
  - (iii) For  $\alpha \in R$ , define the **reflection operator**  $s_{\alpha} : \mathfrak{h}^* \to \mathfrak{h}^*$  by

$$s_{\alpha}(\lambda) = \lambda - \lambda(h_{\alpha})\alpha = \lambda - 2\frac{(\lambda, \alpha)}{(\alpha, \alpha)}\alpha.$$

Then for any roots  $\alpha$ ,  $\beta$ ,  $s_{\alpha}(\beta)$  is also a root.

- (iv) For roots  $\alpha, \beta \neq \pm \alpha$ , the subspace  $V_{\alpha,\beta} = \bigoplus_{k \in \mathbb{Z}} \mathfrak{g}_{\beta+k\alpha} \subset \mathfrak{g}$  is an irreducible representation of  $\mathfrak{sl}_2(\mathbf{k})_{\alpha}$ .
- *Proof.* (i) Suppose  $h \in \mathfrak{h}$  is such that  $\alpha(h) = 0$  for all roots  $\alpha$ . Then adh = 0, hence h = 0 as  $\mathfrak{g}$  is semisimple. This implies both statements.
- (ii)  $a_{\alpha,\beta}$  is the eigenvalue of  $h_{\alpha}$  on  $e_{\beta}$ , hence an integer by the representation theory of  $\mathfrak{sl}_2$  (Subsection 11.4).

- (iii) Let  $x \in \mathfrak{g}_{\beta}$  be nonzero. If  $\beta(h_{\alpha}) \geq 0$  then let  $y = f_{\alpha}^{\beta(h_{\alpha})}x$ . If  $\beta(h_{\alpha}) \leq 0$  then let  $y = e_{\alpha}^{-\beta(h_{\alpha})}x$ . Then by representation theory of  $\mathfrak{sl}_2$ ,  $y \neq 0$ . We also have  $[h, y] = s_{\alpha}(\beta)(h)y$ . This implies the statement.
- (iv) It is clear that  $V_{\alpha,\beta}$  is a representation. Also all  $h_{\alpha}$ -eigenspaces in  $V_{\alpha,\beta}$  are 1-dimensional, and the eigenvalues are either all odd or all even. This implies that it is irreducible.

Assessment: non-included
Complete structure theorem for root decomposition of semisimple Lie algebras. Not as one theorem in mathlib.

## Statement 125: Corollary 19.20
Corollary 19.20. Let  $\mathfrak{h}_{\mathbb{R}}$  be the  $\mathbb{R}$ -span of all  $h_{\alpha}$ . Then  $\mathfrak{h} = \mathfrak{h}_{\mathbb{R}} \oplus i\mathfrak{h}_{\mathbb{R}}$  and the restriction of the Killing form to  $\mathfrak{h}_{\mathbb{R}}$  is real-valued and positive definite.

Assessment: non-included
h_R is a real form of h with positive definite Killing form restriction. Not in mathlib.

## Statement 126: Lemma 20.4
**Lemma 20.4.** Let  $P(z_1,...,z_n)$  be a nonzero complex polynomial, and  $U \subset \mathbb{C}^n$  be the set of points  $(z_1,...,z_n) \in \mathbb{C}^n$  such that  $P(z_1,...,z_n) \neq 0$ . Then U is path-connected, dense and open.

Assessment: non-included
This statement from Section 20 concerns conjugacy of Cartan subalgebras and regular elements in complex semisimple Lie algebras. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/CartanSubalgebra.lean`, `CartanExists.lean`, and related files.

## Statement 127: Lemma 20.5
**Lemma 20.5.** Let  $\mathfrak{g}$  be a complex semisimple Lie algebra. Then the set  $\mathfrak{g}^{sr}$  of strongly regular elements is connected, dense and open in  $\mathfrak{g}$ .

Assessment: non-included
This statement from Section 20 concerns conjugacy of Cartan subalgebras and regular elements in complex semisimple Lie algebras. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/CartanSubalgebra.lean`, `CartanExists.lean`, and related files.

## Statement 128: Proposition 20.6
**Proposition 20.6.** Let  $\mathfrak{g}$  be a complex semisimple Lie algebra and  $\mathfrak{h} \subset \mathfrak{g}$  a Cartan subalgebra. Then

- (i) dim  $\mathfrak{h} = \operatorname{rank}(\mathfrak{g})$ ; and
- (ii) the set  $\mathfrak{h}^{\rm reg}:=\mathfrak{h}\cap\mathfrak{g}^{\rm sr}$  coincides with the set

$$V := \{ h \in \mathfrak{h} : \alpha(h) \neq 0 \ \forall \alpha \in R \}.$$

In particular,  $\mathfrak{h}^{reg}$  is open and dense in  $\mathfrak{h}$ .

Assessment: non-included
This statement from Section 20 concerns conjugacy of Cartan subalgebras and regular elements in complex semisimple Lie algebras. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/CartanSubalgebra.lean`, `CartanExists.lean`, and related files.

## Statement 129: Lemma 20.7
**Lemma 20.7.** Let  $\phi: G \times \mathfrak{h} \to \mathfrak{g}$  be the map defined by  $\phi(g,x) := \operatorname{Ad} q \cdot x$ . Then the set  $U := \phi(G \times V) \subset \mathfrak{g}$  is open.

Assessment: non-included
This statement from Section 20 concerns conjugacy of Cartan subalgebras and regular elements in complex semisimple Lie algebras. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/CartanSubalgebra.lean`, `CartanExists.lean`, and related files.

## Statement 130: Theorem 20.8
**Theorem 20.8.** (i) Let  $\mathfrak{g}$  be a complex semisimple Lie algebra and let  $x \in \mathfrak{g}$  be a strongly regular semisimple element (which exists by Proposition 20.6). Then the centralizer C(x) of x in  $\mathfrak{g}$  is a Cartan subalgebra of  $\mathfrak{g}$ .

(ii) Any Cartan subalgebra of g is of this form.

Assessment: non-included
This statement from Section 20 concerns conjugacy of Cartan subalgebras and regular elements in complex semisimple Lie algebras. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/CartanSubalgebra.lean`, `CartanExists.lean`, and related files.

## Statement 131: Theorem 20.10
**Theorem 20.10.** Any two Cartan subalgebras of a complex semisimple Lie algebra  $\mathfrak{g}$  are conjugate. I.e., if  $\mathfrak{h}_1, \mathfrak{h}_2 \subset \mathfrak{g}$  are two Cartan subalgebras and G a connected Lie group with Lie algebra  $\mathfrak{g}$  then there exists an element  $g \in G$  such that  $Adg \cdot \mathfrak{h}_1 = \mathfrak{h}_2$ .

Assessment: non-included
This statement from Section 20 concerns conjugacy of Cartan subalgebras and regular elements in complex semisimple Lie algebras. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/CartanSubalgebra.lean`, `CartanExists.lean`, and related files.

## Statement 132: Proposition 21.3
**Proposition 21.3.** If  $\mathfrak{g}$  is a semisimple Lie algebra and  $\mathfrak{h} \subset \mathfrak{g}$  a Cartan subalgebra then the corresponding set of roots R is a reduced root system, and  $\alpha^{\vee} = h_{\alpha}$ .

Assessment: included
Root system of a semisimple Lie algebra satisfies root system axioms (reduced). In `Mathlib/Algebra/Lie/Weights/RootSystem.lean`, `rootSystem` is constructed as a `RootSystem` satisfying the axioms. The `IsReduced` property is in `Mathlib/LinearAlgebra/RootSystem/Reduced.lean`.

## Statement 133: Proposition 21.7
**Proposition 21.7.** W is a finite subgroup of O(E) which preserves R.

Assessment: included
Weyl group is a finite subgroup of O(E) preserving R. In `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `weylGroup` is defined as a subgroup of automorphisms of the root pairing. Finiteness is established for finite root systems.

## Statement 134: Theorem 21.9
**Theorem 21.9.** Let R be a reduced root system and  $\alpha, \beta \in R$  be two linearly independent roots with  $|\alpha| \geq |\beta|$ . Let  $\phi$  be the angle between  $\alpha$  and  $\beta$ . Then we have one of the following possibilities:

```
 \begin{array}{l} (1) \ \phi = \pi/2, \ n_{\alpha\beta} = n_{\beta\alpha} = 0; \\ (2a) \ \phi = 2\pi/3, \ |\alpha|^2 = |\beta|^2, \ n_{\alpha\beta} = n_{\beta\alpha} = -1; \\ (2b) \ \phi = \pi/3, \ |\alpha|^2 = |\beta|^2, \ n_{\alpha\beta} = n_{\beta\alpha} = 1; \\ (3a) \ \phi = 3\pi/4, \ |\alpha|^2 = 2|\beta|^2, \ n_{\alpha\beta} = -1, \ n_{\beta\alpha} = -2; \\ (3b) \ \phi = \pi/4, \ |\alpha|^2 = 2|\beta|^2, \ n_{\alpha\beta} = 1, \ n_{\beta\alpha} = 2; \\ (4a) \ \phi = 5\pi/6, \ |\alpha|^2 = 3|\beta|^2, \ n_{\alpha\beta} = -1, \ n_{\beta\alpha} = -3; \\ (4b) \ \phi = \pi/6, \ |\alpha|^2 = 3|\beta|^2, \ n_{\alpha\beta} = 1, \ n_{\beta\alpha} = 3. \end{array}
```

Assessment: non-included
Classification of possible angles and length ratios between roots (the table). Partially in `Mathlib/LinearAlgebra/RootSystem/Reduced.lean` via coxeter weight analysis, but the full classification table is not stated as one theorem.

## Statement 135: Theorem 21.10
**Theorem 21.10.** Any reduced rank 2 root system R is of the form  $A_1 \times A_1$ ,  $A_2$ ,  $B_2$  or  $G_2$ .

Assessment: non-included
Classification of rank 2 reduced root systems (A1xA1, A2, B2, G2). Not explicitly as one theorem in mathlib, though G2 is in `Mathlib/LinearAlgebra/RootSystem/Finite/G2.lean`.

## Statement 136: Corollary 21.11
**Corollary 21.11.** If  $\alpha, \beta \in R$  are independent roots with  $(\alpha, \beta) < 0$  then  $\alpha + \beta \in R$ .

Assessment: non-included
If alpha, beta independent with (alpha, beta) < 0 then alpha + beta is a root. Related to chain theory in `Mathlib/LinearAlgebra/RootSystem/Chain.lean` but not stated in this form.

## Statement 137: Lemma 21.14
Lemma 21.14. Every positive root is a sum of simple roots.

Assessment: non-included
Every positive root is a sum of simple roots. Follows from base theory but not stated as a standalone lemma.

## Statement 138: Lemma 21.15
**Lemma 21.15.** If  $\alpha, \beta \in R_+$  are simple roots then  $(\alpha, \beta) \leq 0$ .

Assessment: included
Simple roots have non-positive inner products. Proved in `Mathlib/LinearAlgebra/RootSystem/Base.lean` as `pairingIn_le_zero_of_ne`.

## Statement 139: Theorem 21.16
**Theorem 21.16.** The set  $\Pi \subset R_+$  of simple roots is a basis of E.

Assessment: non-included
Simple roots form a basis of E (linear independence and spanning). Partially in `Mathlib/LinearAlgebra/RootSystem/Base.lean` where `linearIndependent_pair_of_ne` and `span_root_support` establish parts of this.

## Statement 140: Lemma 21.17
**Lemma 21.17.** Let  $v_i$  be vectors in a Euclidean space E such that  $(v_i, v_j) \leq 0$  when  $i \neq j$  and  $t(v_i) > 0$  for some  $t \in E^*$ . Then  $v_i$  are linearly independent.

Assessment: non-included
Vectors with pairwise non-positive inner products having positive functional value are linearly independent. Not as a standalone lemma.

## Statement 141: Corollary 21.19
**Corollary 21.19.** Any root  $\alpha \in R$  can be uniquely written as  $\alpha = \sum_{i=1}^{r} n_i \alpha_i$ , where  $n_i \in \mathbb{Z}$ . If  $\alpha$  is positive then  $n_i \geq 0$  for all i and if  $\alpha$  is negative then  $n_i \leq 0$  for all i.

For a positive root  $\alpha$ , its **height**  $h(\alpha)$  is the number  $\sum n_i$ . So simple roots are the roots of height 1, and the height of  $\mathbf{e}_i - \mathbf{e}_j$  in  $R = A_{n-1}$  is j - i.

21.5. **Dual root system.** For a root system R, the set  $R^{\vee} \subset E^*$  of  $\alpha^{\vee}$  for all  $\alpha \in R$  is also a root system, such that  $(R^{\vee})^{\vee} = R$ . It is called the **dual root system** to R. For example,  $B_n$  is dual to  $C_n$ , while  $A_{n-1}$ ,  $D_n$  and  $G_2$  are self-dual.

Moreover, it is easy to see that any polarization of R gives rise to a polarization of  $R^{\vee}$  (using the image  $t^{\vee}$  of t under the isomorphism  $E \to E^*$  induced by the inner product), and the corresponding system  $\Pi^{\vee}$  of simple roots consists of  $\alpha_i^{\vee}$  for  $\alpha_i \in \Pi$ .

21.6. Root and weight lattices. Recall that a lattice in a real vector space E is a subgroup  $Q \subset E$  generated by a basis of E. Of course, every lattice is conjugate to  $\mathbb{Z}^n \subset \mathbb{R}^n$  by an element of  $GL_n(\mathbb{R})$ . Also recall that for a lattice  $Q \subset E$  the dual lattice  $Q^* \subset E^*$  is the set of  $f \in E^*$  such that  $f(v) \in \mathbb{Z}$  for all  $v \in Q$ . If Q is generated by a basis  $\mathbf{e}_i$  of E then  $Q^*$  is generated by the dual basis  $\mathbf{e}_i^*$ .

In particular, for a root system R we can define the **root lattice**  $Q \subset E$ , which is generated by the simple roots  $\alpha_i$  with respect to some polarization of R. Since Q is also generated by all roots in R, it is independent on the choice of the polarization. Similarly, we can define the **coroot lattice**  $Q^{\vee} \subset E^*$  generated by  $\alpha^{\vee}, \alpha \in R$ , which is just the root lattice of  $R^{\vee}$ .

Also we define the **weight lattice**  $P \subset E$  to be the dual lattice to  $Q^{\vee}$ :  $P = (Q^{\vee})^*$ , and the **coweight lattice**  $P^{\vee} \subset E^*$  to be the dual lattice to Q:  $P^{\vee} = Q^*$ , so  $P^{\vee}$  is the weight lattice of  $R^{\vee}$ . Thus

$$P = \{ \lambda \in E : (\lambda, \alpha^{\vee}) \in \mathbb{Z} \, \forall \alpha \in R \}, \ P^{\vee} = \{ \lambda \in E^* : (\lambda, \alpha) \in \mathbb{Z} \, \forall \alpha \in R \}.$$

Since for  $\alpha, \beta \in R$  we have  $(\alpha^{\vee}, \beta) = n_{\alpha\beta} \in \mathbb{Z}$ , we have  $Q \subset P$ ,  $Q^{\vee} \subset P^{\vee}$ .

Given a system of simple roots  $\Pi = \{\alpha_1, ..., \alpha_r\}$ , we define **fundamental coweights**  $\omega_i^{\vee}$  to be the dual basis to  $\alpha_i$  and **fundamental weights**  $\omega_i$  to be the dual basis to  $\alpha_i^{\vee}$ :  $(\omega_i, \alpha_j^{\vee}) = (\omega_i^{\vee}, \alpha_j) = \delta_{ij}$ . Thus P is generated by  $\omega_i$  and  $P^{\vee}$  by  $\omega_i^{\vee}$ .

Assessment: non-included
Unique decomposition of roots as integer linear combinations of simple roots with same-sign coefficients. Related to `exists_root_eq_sum_nat_or_neg` in `Base.lean`.

## Statement 142: Lemma 22.2
**Lemma 22.2.** (i) The closure  $\overline{C}$  of a Weyl chamber C is a convex cone.

(ii) The boundary of  $\overline{C}$  is a union of codimension 1 faces  $F_i$  which are convex cones inside one of the root hyperplanes defined inside it by a system of non-strict homogeneous linear inequalities.

The root hyperplanes containing the faces  $F_i$  are called the **walls** of C.

We have seen above that every Weyl chamber defines a polarization of R. Conversely, every polarization defines the corresponding **positive** Weyl chamber  $C_+$  defined by the conditions  $(\alpha, x) > 0$  for  $\alpha \in R_+$  (this set is nonempty since it contains t, hence is a Weyl chamber). Thus  $C_+$  is the set of vectors of the form  $\sum_{i=1}^r c_i \omega_i$  with  $c_i > 0$ . So  $C_+$  has r faces  $L_{\alpha_1} \cap \overline{C}_+, ..., L_{\alpha_r} \cap \overline{C}_+$ .

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 143: Lemma 22.3
**Lemma 22.3.** These assignments are mutually inverse bijections between polarizations of R and Weyl chambers.

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 144: Theorem 22.5
**Theorem 22.5.** W acts transitively on the set of Weyl chambers.

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 145: Corollary 22.6
Corollary 22.6. Every Weyl chamber has r walls.

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 146: Corollary 22.7
**Corollary 22.7.** Any two polarizations of R are related by the action of an element  $w \in W$ . Thus if  $\Pi, \Pi'$  are systems of simple roots corresponding to two polarizations then there is  $w \in W$  such that  $w(\Pi) = \Pi'$ .

22.2. Simple reflections. Given a polarization of R and the corresponding system of simple roots  $\Pi = \{\alpha_1, ..., \alpha_r\}$ , the simple reflections are the reflections  $s_{\alpha_i}$ , denoted by  $s_i$ .

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 147: Lemma 22.8
**Lemma 22.8.** For every Weyl chamber C there exist  $i_1, ..., i_m$  such that  $C = s_{i_1}...s_{i_m}(C_+)$ .

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 148: Corollary 22.9
Corollary 22.9. (i) The simple reflections  $s_i$  generate W; (ii)  $W(\Pi) = R$ .

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 149: Proposition 22.13
**Proposition 22.13.** Let  $\rho = \frac{1}{2} \sum_{\alpha \in R_+} \alpha$ . Then  $(\rho, \alpha_i^{\vee}) = 1$  for all i. Thus  $\rho = \sum_{i=1}^r \omega_i$ .

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 150: Theorem 22.14
**Theorem 22.14.** Let  $w = s_{i_1}...s_{i_l}$  be a representation of  $w \in W$  as a product of simple reflections that has minimal possible length. Then  $l = \ell(w)$ .

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 151: Proposition 22.15
**Proposition 22.15.** The Weyl group W acts simply transitively on Weyl chambers.

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 152: Proposition 22.16
**Proposition 22.16.**  $E/W = \overline{C}_+$ , i.e., every W-orbit on E has a unique representative in  $\overline{C}_+$ .

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 153: Corollary 22.17
Corollary 22.17. Let  $C_- = -C_+$  be the negative Weyl chamber. Then there exists a unique  $w_0 \in W$  such that  $w_0(C_+) = C_-$ . We have  $\ell(w_0) = |R_+|$  and for any  $w \neq w_0$ ,  $\ell(w) < \ell(w_0)$ . Also  $w_0^2 = 1$ .

Assessment: non-included
This statement from Section 22 concerns Weyl chambers, their structure, and the action of the Weyl group. Not formalized in mathlib v4.27.0. Searched in `Mathlib/LinearAlgebra/RootSystem/WeylGroup.lean`, `Base.lean`, and related files.

## Statement 154: Lemma 23.2
**Lemma 23.2.** If R is a root system with system of simple roots  $\Pi = \Pi_1 \sqcup \Pi_2$  with  $\Pi_1 \perp \Pi_2$  then  $R = R_1 \sqcup R_2$  where  $R_i$  is the root system generated by  $\Pi_i$ .

Assessment: non-included
Decomposition of root systems into orthogonal irreducible components. Related to `Mathlib/LinearAlgebra/RootSystem/Irreducible.lean` but not stated in this form.

## Statement 155: Proposition 23.3
**Proposition 23.3.** Any root system is uniquely a union of irreducible ones.

Assessment: non-included
Any root system is uniquely a union of irreducible ones. Related to `Mathlib/LinearAlgebra/RootSystem/Irreducible.lean` but not as this exact statement.

## Statement 156: Proposition 23.4
**Proposition 23.4.** (*i*)  $a_{ii} = 2$ ;

- (ii)  $a_{ij}$  is a nonpositive integer;
- (iii) for any  $i \neq j$ ,  $a_{ij}a_{ji} = 4\cos^2\phi \in \{0,1,2,3\}$ , where  $\phi$  is the angle between  $\alpha_i$  and  $\alpha_j$ ;

(iv) Let  $d_i = |\alpha_i|^2$ . Then the matrix  $d_i a_{ij}$  is symmetric and positive definite.

We will see later that conversely, any such matrix defines a root system.

Assessment: included
Properties of the Cartan matrix (a_ii = 2, a_ij <= 0 for i != j, a_ij = 0 iff a_ji = 0). Proved in `Mathlib/LinearAlgebra/RootSystem/CartanMatrix.lean`: `cartanMatrix_apply_same` gives a_ii = 2, `cartanMatrix_le_zero_of_ne` gives nonpositive off-diagonal, `cartanMatrix_apply_eq_zero_iff_symm` gives the symmetry of zeros.

## Statement 157: Proposition 23.6
**Proposition 23.6.** The Cartan matrix determines the root system uniquely.

Assessment: included
The Cartan matrix determines the root system uniquely (up to isomorphism). Proved in `Mathlib/LinearAlgebra/RootSystem/CartanMatrix.lean` as `equivOfCartanMatrixEq`.

## Statement 158: Theorem 23.7
**Theorem 23.7.** (i) Connected Dynkin diagrams are classified by the list given in the picture below, i.e., they are  $A_n, B_n, C_n, D_n, G_2$  which we have already met, along with four more:  $F_4, E_6, E_7, E_8$ .

(ii) Every matrix satisfying the conditions of Proposition 23.4 is a Cartan matrix of some root system.

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

The proof of Theorem 23.7 is rather long but direct. It consists of several steps. The first step is construction of the remaining root systems  $F_4$ ,  $E_6$ ,  $E_7$ ,  $E_8$ .

Assessment: non-included
Classification of connected Dynkin diagrams (A, B, C, D, E, F, G). Not in mathlib v4.27.0. Searched for Dynkin, classification, and diagram in the entire mathlib.

## Statement 159: Theorem 24.1
**Theorem 24.1.** (Serre relations) (i) The elements  $e_i$ ,  $f_i$ ,  $h_i$ , i = 1, ..., r generate  $\mathfrak{g}$ .

(ii) These elements satisfy the following relations:

$$[h_i, h_j] = 0, [h_i, e_j] = a_{ij}e_j, [h_i, f_j] = -a_{ij}f_j, [e_i, f_j] = \delta_{ij}h_i,$$

 $(ade_i)^{1-a_{ij}}e_j = 0, (adf_i)^{1-a_{ij}}f_j = 0, i \neq j.$

The last two sets of relations are called **Serre relations**. Note that if  $a_{ij} = 0$  then the Serre relations just say that  $[e_i, e_j] = [f_i, f_j] = 0$ .

Assessment: non-included
Serre relations generate the Lie algebra. While `Mathlib/Algebra/Lie/SerreConstruction.lean` defines the Lie algebra from a Cartan matrix via Serre relations, the proof that this recovers the original semisimple Lie algebra is not complete.

## Statement 160: Theorem 24.2
**Theorem 24.2.** (Serre) (i) The Lie subalgebra  $\mathfrak{n}_+$  of  $\mathfrak{g}(R)$  generated by  $e_i$  has the Serre relations  $(ade_i)^{1-a_{ij}}e_j=0$  as the defining relations. Similarly, the Lie subalgebra  $\mathfrak{n}_-$  of  $\mathfrak{g}(R)$  generated by  $f_i$  has the Serre relations  $(adf_i)^{1-a_{ij}}f_j=0$  as the defining relations. In particular,  $e_i, f_i \neq 0$  in  $\mathfrak{g}(R)$ . Moreover,  $h_i$  are linearly independent.

- (ii)  $\mathfrak{g}(R)$  is a sum of finite dimensional modules over every simple root subalgebra  $(\mathfrak{sl}_2)_i = (e_i, f_i, h_i)$ .
  - (iii)  $\mathfrak{g}(R)$  is finite dimensional.
  - (iv)  $\mathfrak{g}(R)$  is semisimple and has root system R.

Assessment: non-included
Serre presentation: n_+ and n_- have Serre relations as defining relations. Not fully proved in mathlib.

## Statement 161: Lemma 24.3
**Lemma 24.3.** (i) The Lie algebra  $\widetilde{\mathfrak{n}_+}$  is free on the generators  $e_i$  and  $\widetilde{\mathfrak{n}_-}$  is free on the generators  $f_i$ .

- (ii)  $h_i$  are linearly independent in  $\widetilde{\mathfrak{h}}$  (i.e.,  $\widetilde{\mathfrak{h}} \cong \mathfrak{h}$ ).
- *Proof.* (i) We prove only the second statement, the first one being the same for the opposite polarization. Let  $\mathfrak{h}'$  be a vector space with basis

 $h'_i$ , i = 1, ..., r and consider the Lie algebra  $\mathfrak{a} := \mathfrak{h}' \ltimes FL_r$ , where  $FL_r$  is freely generated by  $f'_1, ..., f'_r$  and

$$[h'_i, f'_j] = -a_{ij}f'_j, \ [h'_i, h'_j] = 0.$$

Consider the universal enveloping algebra

$$U = U(\mathfrak{a}) = \mathbf{k}[h'_1, ..., h'_r] \ltimes \mathbf{k}\langle f'_1, ..., f'_r \rangle,$$

which as a vector space is naturally identified with the tensor product  $\mathbf{k}\langle f_1,...,f_r\rangle\otimes\mathbf{k}[h'_1,...,h'_r]$ , via  $f\otimes h\mapsto fh$  (by Proposition 14.4). Now define an action of  $\mathfrak{g}(R)$  on the space U as follows. For  $P\in\mathbf{k}[h'_1,...,h'_r]$  and w a word in  $f'_i$  of weight  $-\alpha$ , we set

$$h_{i}(w \otimes P) = w \otimes (h'_{i} - \alpha(h_{i}))P, \ f_{i}(w \otimes P) = f'_{i}w \otimes P,$$
$$e_{i}(f'_{j_{1}}...f'_{j_{s}} \otimes P) = \sum_{k:j_{k}=i} f'_{j_{1}}....\widehat{f'_{j_{k}}}...f'_{j_{s}} \otimes (h'_{i} - (\alpha_{j_{k+1}} + ... + \alpha_{j_{s}})(h_{i}))P$$

(where the hat means that the corresponding factor is omitted). It is easy to check that this indeed defines an action, i.e., the relations of  $\widetilde{\mathfrak{g}(R)}$  are satisfied (check it!). Thus we have a linear map  $\widetilde{\mathfrak{g}(R)} \to U$  given by  $x \mapsto x(1)$ . The restriction of this map to the Lie subalgebra  $\widetilde{\mathfrak{n}}_-$  is a map  $\phi: \widetilde{\mathfrak{n}}_- \to FL_r$  which sends every iterated commutator of  $f_i$  to itself. This implies that  $\phi$  is an isomorphism, i.e.,  $\widetilde{\mathfrak{n}}_-$  is free.

(ii) The elements  $h_i(1) = h'_i$  are linearly independent, hence so are  $h_i$ .

Now consider the element  $S_{ij}^+ := (\operatorname{ad} e_i)^{1-a_{ij}} e_j$  in  $\widetilde{\mathfrak{n}_+}$  and  $S_{ij}^- := (\operatorname{ad} f_i)^{1-a_{ij}} f_j$  in  $\widetilde{\mathfrak{n}_-}$ . It is easy to check that  $[f_k, S_{ij}^+] = 0$  (this follows easily from the representation theory of  $\mathfrak{sl}_2$ , Subsection 11.4,—check it!). Therefore, setting  $I_+$  to be the ideal in the Lie algebra  $\widetilde{\mathfrak{n}_+}$  generated by  $S_{ij}^+$ , and  $I_-$  to be the ideal in the Lie algebra  $\widetilde{\mathfrak{n}_-}$  generated by  $S_{ij}^-$ , we see that the ideal of Serre relations in  $\widetilde{\mathfrak{g}(R)}$  is  $I_+ \oplus I_-$ . Lemma 24.3 now implies (i).

- (ii) The Serre relations imply that  $e_j$  generates the representation  $V_{-a_{ij}}$  of  $(\mathfrak{sl}_2)_i$  for  $j \neq i$ , and so does  $f_j$ . Also any element of  $\mathfrak{h}$  generates  $V_0$  or  $V_2$  or the sum of the two, and  $e_i$ ,  $f_i$  generate  $V_2$ . This implies (ii) since  $\mathfrak{g}(R)$  is generated by  $e_i$ ,  $f_i$ ,  $h_i$ , and if x generates a representation X of  $(\mathfrak{sl}_2)_i$  and y generates a representation Y then [x, y] generates a quotient of  $X \otimes Y$ .
- (iii) We have  $\mathfrak{g}(R) = \bigoplus_{\alpha \in Q} \mathfrak{g}_{\alpha}$ , where  $\mathfrak{g}_{\alpha}$  are the subspaces of  $\mathfrak{g}(R)$  of weight  $\alpha$ , and  $\mathfrak{g}_0 = \mathfrak{h}$ . Let  $Q_+$  be the  $\mathbb{Z}_+$ -span of  $\alpha_i$ . Then  $\mathfrak{g}_{\alpha}$  is zero unless  $\alpha \in Q_+$  or  $-\alpha \in Q_+$ , and is finite dimensional for any  $\alpha$ .

We will now show that if  $\mathfrak{g}_{\alpha} \neq 0$  then  $\alpha \in R$  or  $\alpha = 0$ , which implies (iii). It suffices to consider  $\alpha \in Q_+$ . We prove the statement

by induction in the height  $\operatorname{ht}(\alpha) = \sum_i k_i$  where  $\alpha = \sum_i k_i \alpha_i$ . The base case (height 1) is obvious, so we only need to justify the inductive step. We have  $(\alpha, \omega_i^{\vee}) = k_i \geq 0$  for all i. If there is only one i with  $k_i \geq 0$  then the statement is clear since  $\mathfrak{g}_{m\alpha_i} = 0$  if  $m \geq 2$ . (as  $\mathfrak{n}_+$  is generated by  $e_i$ ). So assume that there are at least two such indices i. Since  $(\alpha, \alpha) > 0$ , there exists i such that  $(\alpha, \alpha_i^{\vee}) > 0$ . By the representation theory of  $\mathfrak{sl}_2$  (Subsection 11.4),  $\mathfrak{g}_{s_i\alpha} \neq 0$ . Clearly,  $s_i\alpha = \alpha - (\alpha, \alpha_i^{\vee})\alpha_i \notin -Q_+$  (since  $k_j > 0$  for at least two indices j), so  $s_i\alpha \in Q_+$  but has height smaller than  $\alpha$  (as  $(\alpha, \alpha_i^{\vee}) > 0$ ). So by the induction assumption  $s_i\alpha \in R$ , which implies  $\alpha \in R$ . This proves (iii).

(iv) We see that  $\mathfrak{g}(R) = \mathfrak{h} \oplus \bigoplus_{\alpha \in R} \mathfrak{g}_{\alpha}$ , where  $\mathfrak{g}_{\alpha}$  are 1-dimensional (this follows from (ii),(iii) since every root can be mapped to a simple root by a composition of simple reflections). Let I be a nonzero ideal in  $\mathfrak{g}$ . Then  $I \supset \mathfrak{g}_{\alpha}$  for some  $\alpha \neq 0$ . Also, by the representation theory of  $\mathfrak{sl}_2$ ,  $I_\beta \neq 0$  implies  $I_{w\beta} \neq 0$  for all  $w \in W$ . Thus  $I_{\alpha_i} \neq 0$  for some i, i.e.,  $e_i \in I$ . Hence  $h_i, f_i \in I$ . Now let J be the set of indices j for which  $e_j, f_j, h_j \in I$  (or, equivalently, just  $e_j \in I$ ); we have shown it is nonempty. Since  $[h_j, e_k] = a_{jk}e_k$ , we find that if  $j \in J$  and  $a_{jk} \neq 0$  (i.e., k is connected to j in the Dynkin diagram) then  $k \in J$ . Since the Dynkin diagram is connected, J = [1, ..., r] and  $I = \mathfrak{g}$ . Thus  $\mathfrak{g}$  is simple and clearly has root system R. This proves (iv) and completes the proof of Serre's theorem.

Assessment: non-included
The auxiliary Lie algebras tilde n_+, tilde n_- are free. Not in mathlib.

## Statement 162: Corollary 24.4
**Corollary 24.4.** Isomorphism classes of simple Lie algebras over  $\mathbf{k}$  are in bijection with Dynkin diagrams  $A_n$ ,  $n \geq 1$ ,  $B_n$ ,  $n \geq 2$ ,  $C_n$ ,  $n \geq 3$ ,  $D_n$ ,  $n \geq 4$ ,  $E_6$ ,  $E_7$ ,  $E_8$ ,  $F_4$  and  $G_2$ .

Assessment: non-included
Classification/existence of simple Lie algebras via Dynkin diagrams. Not established in v4.27.0.

## Statement 163: Proposition 25.3
**Proposition 25.3.** Any finite dimensional representation V of  $\mathfrak{g}$  has a weight decomposition. Moreover, all weights of V are integral, i.e., P(V) is a finite subset of the weight lattice  $P \subset \mathfrak{h}^*$  of  $\mathfrak{g}$ .

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 164: Proposition 25.5
**Proposition 25.5.** Any finite dimensional representation  $V \neq 0$  contains a nonzero highest weight vector of some weight  $\lambda$ . Thus every irreducible finite dimensional representation of  $\mathfrak{g}$  is a highest weight representation.

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 165: Proposition 25.7
**Proposition 25.7.** The map  $\phi: U(\mathfrak{n}_{-}) \to M_{\lambda}$  given by  $\phi(x) = xv_{\lambda}$  is an isomorphism of left  $U(\mathfrak{n}_{-})$ -modules.

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 166: Corollary 25.9
Corollary 25.9.  $M_{\lambda}$  has a weight decomposition with  $P(M_{\lambda}) = \lambda - Q_{+}$ , dim  $M_{\lambda}[\lambda] = 1$ , and weight subspaces of  $M_{\lambda}$  are finite dimensional.

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 167: Proposition 25.10
**Proposition 25.10.** (i) (Universal property of Verma modules) If V is a representation of  $\mathfrak{g}$  and  $v \in V$  is a vector such that  $hv = \lambda(h)v$  for  $h \in h$  and  $e_iv = 0$  for  $1 \leq i \leq r$  then there is a unique homomorphism  $\eta: M_{\lambda} \to V$  such that  $\eta(v_{\lambda}) = v$ . In particular, if V is generated by such  $v \neq 0$  (i.e., V is a highest weight representation with highest weight vector v) then V is a quotient of  $M_{\lambda}$ .

- (ii) Every highest weight representation has a weight decomposition into finite dimensional weight subspaces.
- *Proof.* (i) Uniqueness follows from the fact that  $v_{\lambda}$  generates  $M_{\lambda}$ . To construct  $\eta$ , note that we have a natural homomorphism of  $\mathfrak{g}$ -modules  $\widetilde{\eta}: U(\mathfrak{g}) \to V$  given by  $\widetilde{\eta}(x) = xv$ . Moreover,  $\widetilde{\eta}|_{I_{\lambda}} = 0$  thanks to the relations satisfied by v, so  $\widetilde{\eta}$  descends to a map  $\eta: U(\mathfrak{g})/I_{\lambda} = M_{\lambda} \to V$ . Moreover, if V is generated by v then this map is surjective, as desired.
- (ii) This follows from (i) since a quotient of any representation with a weight decomposition must itself have a weight decomposition.  $\Box$

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 168: Corollary 25.11
Corollary 25.11. Every highest weight representation V has a unique highest weight generator, up to scaling.

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 169: Proposition 25.12
**Proposition 25.12.** For every  $\lambda \in \mathfrak{h}^*$ , the Verma module  $M_{\lambda}$  has a unique irreducible quotient  $L_{\lambda}$ . Moreover,  $L_{\lambda}$  is a quotient of every highest weight  $\mathfrak{g}$ -module V with highest weight  $\lambda$ .

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 170: Corollary 25.13
Corollary 25.13. Irreducible highest weight  $\mathfrak{g}$ -modules are classified by their highest weight  $\lambda \in \mathfrak{h}^*$ , via the bijection  $\lambda \mapsto L_{\lambda}$ .

25.3. Finite dimensional modules. Since every finite dimensional irreducible  $\mathfrak{g}$ -module is highest weight, it is of the form  $L_{\lambda}$  for  $\lambda$  belonging to some subset  $P_F \subset P$ , the set of weights  $\lambda$  such that  $L_{\lambda}$  is finite dimensional. So to obtain a final classification of finite dimensional irreducible representations of  $\mathfrak{g}$ , we should determine the subset  $P_F$ .

Let  $P_+ \subset P$  be the intersection of P with the closure of the dominant Weyl chamber  $C_+$ ; i.e.,  $P_+$  is the set of nonnegative integer linear combinations of the fundamental weights  $\omega_i$ . In other words,  $P_+$  is the set of  $\lambda \in P$  such that  $(\lambda, \alpha_i^{\vee}) \in \mathbb{Z}_+$  for  $1 \leq i \leq r$ . Weights belonging to  $P_+$  are called **dominant integral**.

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 171: Lemma 25.15
**Lemma 25.15.** If  $\lambda \in P_+$  then in  $L_{\lambda}$ , we have  $f_i^{\lambda(h_i)+1}v_{\lambda}=0$ .

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 172: Lemma 25.16
**Lemma 25.16.** Let V be a  $\mathfrak{g}$ -module with weight decomposition into finite dimensional weight subspaces. If V is a sum of finite dimensional  $(\mathfrak{sl}_2)_i$ -modules for each i = 1, ..., r, then for each  $\lambda \in P$  and  $w \in W$ ,  $\dim V[\lambda] = \dim V[w\lambda]$ . In particular, P(V) is W-invariant.

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 173: Theorem 25.17
**Theorem 25.17.** For any  $\lambda \in P_+$ ,  $L_{\lambda}$  is finite dimensional; i.e.,  $P_F = P_+$ . Thus finite dimensional irreducible representations of  $\mathfrak{g}$  are classified, up to an isomorphism, by their highest weight  $\lambda \in P_+$ , via the bijection  $\lambda \mapsto L_{\lambda}$ . Moreover, for any  $\mu \in P$  and  $w \in W$ ,  $\dim L_{\lambda}[\mu] = \dim L_{\lambda}[w\mu]$ .

Assessment: non-included
This statement from Section 25 concerns the representation theory of semisimple Lie algebras (weights, Verma modules, highest weight classification). Not formalized in mathlib v4.27.0. Mathlib has weight spaces (`Mathlib/Algebra/Lie/Weights/`) but not Verma modules or the full highest weight theory.

## Statement 174: Proposition 26.3
**Proposition 26.3.** The Weyl denominator  $\Delta$  is anti-invariant under W.

Assessment: non-included
This statement from Section 26 concerns the Weyl character formula and related results. Not formalized in mathlib v4.27.0. Searched for Weyl character, denominator formula, and Casimir in mathlib.

## Statement 175: Theorem 26.4
**Theorem 26.4.** (Weyl character formula) For any  $\lambda \in P_+$  the character  $\chi_{\lambda} := \chi_{L_{\lambda}}$  of the irreducible finite dimensional representation  $L_{\lambda}$  is given by

$$\chi_{\lambda} = \frac{\sum_{w \in W} (-1)^{\ell(w)} e^{w(\lambda + \rho)}}{\Lambda}.$$

The proof of this theorem is in the next subsection.

Assessment: non-included
This statement from Section 26 concerns the Weyl character formula and related results. Not formalized in mathlib v4.27.0. Searched for Weyl character, denominator formula, and Casimir in mathlib.

## Statement 176: Corollary 26.5
Corollary 26.5. (Weyl denominator formula) One has

$$\Delta = \sum_{w \in W} (-1)^{\ell(w)} e^{w\rho}.$$

Assessment: non-included
This statement from Section 26 concerns the Weyl character formula and related results. Not formalized in mathlib v4.27.0. Searched for Weyl character, denominator formula, and Casimir in mathlib.

## Statement 177: Lemma 26.6
**Lemma 26.6.** If V is a highest weight representation with highest weight  $\lambda$  then  $C|_V = (\lambda, \lambda + 2\rho) = |\lambda + \rho|^2 - |\rho|^2$ .

Now we will define a sequence of modules K(b) from category  $\mathcal{O}$  parametrized by some binary strings b. This is done inductively. We set  $K(\emptyset) = L_{\lambda}$ . Now suppose K(b) is already defined. If K(b) = 0 then we set K(b0) = K(b1) = 0. Otherwise, pick a nonzero vector  $v_b \in K(b)$ , of some weight  $\nu(b) \in \lambda - Q_+$  such that the height of  $\lambda - \nu(b)$  takes the minimal possible value. Then  $v_b$  is a highest weight vector, and we can consider the corresponding homomorphism

$$\xi_b: M_{\nu_b} \to K(b).$$

Let K(b1), K(b0) be the kernel and cokernel of  $\xi_b$ . We have

$$\chi_{K(b1)} - \chi_{M_{\nu(b)}} + \chi_{K(b)} - \chi_{K(b0)} = 0.$$

Thus we have

$$\chi_{K(b)} = \chi_{M_{\nu(b)}} - \chi_{K(b1)} + \chi_{K(b0)}.$$

Now, it is clear that for every  $\mu$ , every sufficiently long sequence b satisfies  $K(b)[\mu] = 0$ . So iterating this formula starting with  $b = \emptyset$ , we will get

(26.1)
$$\chi_{\lambda} = \sum_{b} (-1)^{\Sigma(b)} \chi_{M_{\nu(b)}}$$

where  $\Sigma(b)$  is the sum of digits of b (which could a priori be an infinite sum). So

$$\Delta \chi_{\lambda} = \sum_{b} (-1)^{\Sigma(b)} e^{\nu(b) + \rho}.$$

Also note that by induction in the length of b we can conclude that the eigenvalue of C on  $M_{\nu(b)}$  is  $|\lambda + \rho|^2 - |\rho|^2$  regardless of b, which implies that

$$|\nu(b) + \rho|^2 = |\lambda + \rho|^2$$

for all b; in particular, this shows that the sum (26.1) is finite.

So it remains to show that if  $\mu = \lambda + \rho - \beta \in P_+$  with  $\beta \in Q_+$  and  $\beta \neq 0$  then  $|\mu|^2 < |\lambda + \rho|^2$ . Indeed,

$$|\lambda + \rho|^2 - |\mu|^2 = |\lambda + \rho|^2 - |\lambda - \beta + \rho|^2 =$$

$$2(\lambda + \rho, \beta) - |\beta|^2 > (\lambda + \rho, \beta) - |\beta|^2 = (\lambda + \rho - \beta, \beta) \ge 0.$$

This completes the proof of the Weyl character formula.

Assessment: non-included
This statement from Section 26 concerns the Weyl character formula and related results. Not formalized in mathlib v4.27.0. Searched for Weyl character, denominator formula, and Casimir in mathlib.

## Statement 178: Proposition 26.8
Proposition 26.8. We have

$$\dim L_{\lambda} = \frac{\prod_{\alpha \in R_{+}} (\alpha, \lambda + \rho)}{\prod_{\alpha \in R_{+}} (\alpha, \rho)}.$$

Note that this number is an integer, but this is not obvious without its interpretation as the dimension of a representation.

Formula (26.2) has a meaning even before taking the limit. Namely, the eigenvalues of the element  $2h_{\rho}$  define a  $\mathbb{Z}$ -grading on the representation  $L_{\lambda}$  called the **principal grading**, and we obtain a product formula for the Poincaré polynomial of this grading.

Assessment: non-included
This statement from Section 26 concerns the Weyl character formula and related results. Not formalized in mathlib v4.27.0. Searched for Weyl character, denominator formula, and Casimir in mathlib.

## Statement 179: Proposition 27.1
**Proposition 27.1.** Let  $\lambda = \sum_{i=1}^r m_i \omega_i$  be a dominant integral weight for  $\mathfrak{g}$ . Consider the tensor product  $T_{\lambda} := \bigotimes_i L_{\omega_i}^{\otimes m_i}$ , and let  $v := \bigotimes_i v_{\omega_i}^{\otimes m_i}$  be the tensor product of the highest weight vectors. Let V be the sub-representation of  $T_{\lambda}$  generated by v. Then  $V \cong L_{\lambda}$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 180: Theorem 27.3
**Theorem 27.3.** (Schur-Weyl duality) (i) The centralizer of A is B and vice versa.

- (ii) If  $\lambda$  has at most n parts then the representation  $\pi_{\lambda}$  of B (hence  $S_N$ ) is irreducible, and such representations are pairwise non-isomorphic.
- (iii) If dim  $V \geq N$  then  $\pi_{\lambda}$  exhaust all irreducible representations of  $S_N$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 181: Lemma 27.4
**Lemma 27.4.** If U is a  $\mathbb{C}$ -vector space then  $S^NU$  is spanned by elements  $x \otimes ... \otimes x$ ,  $x \in U$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 182: Lemma 27.5
**Lemma 27.5.** For any associative algebra R over  $\mathbb{C}$ , the algebra  $S^NR$  is generated by elements

$$\Delta_N(x) := x \otimes 1 \otimes ... \otimes 1 + 1 \otimes x \otimes ... \otimes 1 + ... + 1 \otimes ... \otimes 1 \otimes x$$
 for  $x \in R$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 183: Lemma 27.6
**Lemma 27.6.** (Double centralizer lemma) Let V be a finite dimensional vector space and  $A, B \subset \operatorname{End} V$  be subalgebras such that B is isomorphic to a direct sum of matrix algebras and A is the centralizer of B. Then A is also isomorphic to a direct sum of matrix algebras, and moreover

$$V = \bigoplus_{i=1}^{n} W_i \otimes U_i,$$

where  $W_i$  run through all irreducible A-modules and  $U_i$  through irreducible B-modules. In particular, B is the centralizer of A and we have a natural bijection between irreducible A-modules and irreducible B-modules which matches  $W_i$  and  $U_i$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 184: Proposition 28.4
**Proposition 28.4.** dim  $S^{\lambda}V = P_{\lambda}(N)$  where  $P_{\lambda}$  is a polynomial of degree  $|\lambda|$  with rational coefficients and integer roots. Moreover, the roots of  $P_{\lambda}$  are all the integers in the interval  $[1 - \lambda_1, k - 1]$  (occurring with multiplicities).

Moreover, we see that  $P_{\lambda}(N)$  is an integer-valued polynomial, i.e., it takes integer values at integer points (this is equivalent to being an integer linear combination of  $\binom{N}{i}$ ).

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 185: Theorem 28.8
**Theorem 28.8.** The functions  $F_{\Gamma}$  for various  $\Gamma$  span the space of invariant functions.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 186: Theorem 29.1
**Theorem 29.1.** (Frobenius character formula) The character value  $\chi_{\lambda}(\sigma)$  is the coefficient of  $x_1^{\lambda_1+N-1}...x_N^{\lambda_N}$  in the polynomial

$$\prod_{i < j} (x_i - x_j) \cdot \prod_i (x_1^i + ... + x_n^i)^{m_i}.$$

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 187: Theorem 29.3
**Theorem 29.3.** (Howe duality) We have a decomposition

$$S^n(V \otimes W) = \bigoplus_{\lambda: |\lambda| = n} S^{\lambda} V \otimes S^{\lambda} W.$$

Note that if  $\lambda$  has more parts than dim V or dim W then the corresponding summand is zero.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 188: Corollary 29.4
Corollary 29.4. (Cauchy identity) If  $x = (x_1, ..., x_r)$  and  $y = (y_1, ..., y_s)$  then one has

$$\sum_{\lambda} s_{\lambda}(x) s_{\lambda}(y) z^{|\lambda|} = \prod_{i=1}^{r} \prod_{j=1}^{s} \frac{1}{1 - z x_{i} y_{j}}.$$

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 189: Lemma 29.5
**Lemma 29.5.** (Molien formula). Let  $A: V \to V$  be a linear operator on a finite dimensional vector space V. Denote by  $S^nA$  the induced linear operator  $A^{\otimes n}$  on  $S^nV$ . Then

$$\sum_{n=0}^{\infty} \operatorname{Tr}(S^n A) z^n = \frac{1}{\det(1 - zA)}.$$

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 190: Lemma 30.2
**Lemma 30.2.** A fundamental weight  $\omega_i$  is minuscule if and only if  $m_i = 1$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 191: Lemma 30.3
**Lemma 30.3.** Let  $\omega \in Q$  and  $|(\omega, \beta)| \leq 1$  for all coroots  $\beta$ . Then  $\omega = 0$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 192: Proposition 30.4
**Proposition 30.4.** The following conditions on a dominant integral weight  $\omega$  are equivalent:

- (1)  $\omega$  is minuscule;
- (2) all weights of the representation  $L_{\omega}$  belong to the orbit  $W\omega$ ;
- (3) if  $\lambda$  is a dominant integral weight such that  $\omega \lambda \in Q_+$  then  $\lambda = \omega$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 193: Corollary 30.5
Corollary 30.5. The character of  $L_{\omega}$  with minuscule  $\omega$  is

$$\chi_{\omega} = \sum_{\gamma \in W_{\omega}} e^{\gamma}.$$

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 194: Proposition 30.6
**Proposition 30.6.**  $\omega \in P_+$  is minuscule if and only if the restriction of  $L_{\omega}$  to any root  $\mathfrak{sl}_2$ -subalgebra of  $\mathfrak{g}$  is the direct sum of 1-dimensional and 2-dimensional representations.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 195: Corollary 30.7
Corollary 30.7. If  $\omega$  is minuscule then for any dominant integral weight  $\lambda$  of  $\mathfrak{g}$  we have

$$L_{\omega} \otimes L_{\lambda} = \bigoplus_{\gamma \in W \omega} L_{\lambda + \gamma},$$

where if  $\lambda + \gamma$  is not dominant then we agree that  $L_{\lambda+\gamma} = 0$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 196: Proposition 30.9
**Proposition 30.9.** (i) Let  $\lambda$  be a partition of N. Then we have

$$\mathbb{C}S_{N+1}\otimes_{\mathbb{C}S_N}\pi_\lambda=\bigoplus_{\mu\in\lambda+\square}\pi_\mu.$$

(ii) Let  $\mu$  be a partition of N+1. Then we have

$$\pi_{\mu}|_{S_N} = \bigoplus_{\lambda \in \mu - \square} \pi_{\mu}.$$

Here in (ii) we sum over all ways to delete a **removable box** from the Young diagram of  $\mu$ , i.e., such that the remaining collection of boxes is still a Young diagram.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 197: Corollary 30.10
Corollary 30.10. Let  $\mathbb{C}_-$  be the sign representation of  $S_N$ . Then

$$\pi_{\lambda} \otimes \mathbb{C}_{-} \cong \pi_{\lambda^{\dagger}}$$
.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 198: Proposition 30.11
**Proposition 30.11.** (Skew Howe duality) Let V, W be complex vector spaces. Show that

$$\wedge^n(V \otimes W) \cong \bigoplus_{\lambda: |\lambda| = n} S^{\lambda}V \otimes S^{\lambda^{\dagger}}W$$

as  $GL(V) \times GL(W)$ -modules.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 199: Proposition 30.16
**Proposition 30.16.** Every coset in P/Q contains a unique minuscule weight. This gives a bijection between P/Q and minuscule weights. So the number of minuscule weights equals  $\det A$ , where A is the Cartan matrix.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 200: Proposition 31.4
**Proposition 31.4.** For  $n \geq 3$  we have  $\pi_1(SO_n(\mathbb{C})) = \mathbb{Z}/2$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 201: Lemma 31.5
**Lemma 31.5.** Let  $X_n$  be the hypersurface in  $\mathbb{C}^n$  given by the equation  $z_1^2 + ... + z_n^2 = 1$ . Then for any  $1 \le k \le n-2$  we have  $\pi_k(X_n) = 0$ , i.e., every continuous map  $S^k \to X_n$  contacts to a point. E.g.,  $X_n$  is connected for  $n \ge 2$ , simply connected for  $n \ge 3$ , doubly connected for  $n \ge 4$ , etc.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 202: Corollary 31.6
Corollary 31.6. For  $n \geq 1$  the simply connected group  $\operatorname{Spin}_{2n+1}(\mathbb{C})$  is a double cover of  $SO_{2n+1}(\mathbb{C})$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 203: Corollary 31.9
Corollary 31.9. For  $n \geq 2$  the group  $\mathrm{Spin}_{2n}(\mathbb{C})$  is a double cover of  $SO_{2n}(\mathbb{C})$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 204: Theorem 31.13
**Theorem 31.13.** The algebra Cl(V) is isomorphic to  $Mat_{2^n}(\mathbf{k})$  if  $\dim V = 2n$  and to  $Mat_{2^n}(\mathbf{k}) \oplus Mat_{2^n}(\mathbf{k})$  if  $\dim V = 2n + 1$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 205: Proposition 32.3
**Proposition 32.3.** For any simple Lie algebra  $\mathfrak{g} \neq \mathfrak{sl}_n, \mathfrak{sp}_{2n}$ ,  $\theta$  is a fundamental weight.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 206: Proposition 32.6
**Proposition 32.6.** The restriction of  $\mathfrak{g}$  to the principal  $\mathfrak{sl}_2$ -subalgebra decomposes as  $\bigoplus_{i=1}^r L_{2m_i+1}$ .

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 207: Proposition 32.14
**Proposition 32.14.**  $L_{\lambda}$  is of real type if  $(2\rho^{\vee}, \lambda)$  is even and of quaternionic type if it is odd.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 208: Theorem 32.16
**Theorem 32.16.** (Bott periodicity for spin representations) The behavior of the spin representations of the orthogonal Lie algebra  $\mathfrak{so}_m$  is determined by the remainder r of m modulo 8. Namely:

For r = 1, 7, S is of real type.

For r = 3, 5, S is of quaternionic type.

For r = 0,  $S_+, S_-$  are of real type.

For  $r = 2, 6, S_{+}^{*} = S_{-}$  (complex type).

For r = 4,  $S_+$ ,  $S_-$  are of quaternionic type.

Assessment: non-included
This statement concerns advanced representation theory (tensor products, Schur-Weyl duality, classical groups, Clifford algebras, spin representations). Not formalized in mathlib v4.27.0.

## Statement 209: Lemma 33.1
**Lemma 33.1.** If X is a locally compact topological space with a countable base then it can be represented as a nested union of compact subsets:  $X = \bigcup_{n \in \mathbb{N}} K_n$ ,  $K_i \subset K_{i+1}$ , such that every point  $x \in X$  has a neighborhood  $U_x$  contained in some  $K_n$ .

Assessment: non-included
Exhaustion of locally compact second-countable spaces by compact sets. While mathlib has sigma-compact spaces, the specific formulation is not identical.

## Statement 210: Lemma 33.2
**Lemma 33.2.** Let X be a locally compact topological space with a countable base. Then every base of X has a countable, locally finite subcover.

Assessment: non-included
Every base has a countable locally finite subcover. Not in mathlib as stated.

## Statement 211: Proposition 33.4
**Proposition 33.4.** Any open cover  $\{U_i, i \in I\}$  of a manifold M admits a partition of unity subordinate to this cover.

Assessment: included
Existence of partitions of unity subordinate to open covers. Mathlib has partitions of unity in `Mathlib/Topology/PartitionOfUnity.lean` for paracompact spaces and smooth partitions of unity for manifolds.

## Statement 212: Proposition 34.3
**Proposition 34.3.** If M is compact and  $\omega$  is non-vanishing then M has finite volume under the measure  $\mu = \mu_{\omega}$ , and every bounded measurable (in particular, any continuous) function on M is in  $L^1(M, \mu)$ .

Assessment: non-included
Compact manifolds with non-vanishing top forms have finite volume. Not in mathlib.

## Statement 213: Theorem 34.4
**Theorem 34.4.** (Stokes formula) If M is an n-dimensional oriented manifold with boundary and  $\omega$  a differential n-1-form on M of class  $C^1$  then

$$\int_{M} d\omega = \int_{\partial M} \omega.$$

In particular, if M is closed (has no boundary) then  $\int_M d\omega = 0$ , and if  $\omega$  is closed  $(d\omega = 0)$  then  $\int_{\partial M} \omega = 0$ .

When M is an interval in  $\mathbb{R}$ , this reduces to the fundamental theorem of calculus. If M is a region in  $\mathbb{R}^2$ , this reduces to Green's formula. If M is a surface in  $\mathbb{R}^3$ , this reduces to the classical Stokes formula from

vector calculus. Finally, if M is a region in  $\mathbb{R}^3$  then this reduces to the Gauss formula (Divergence theorem).

The proof of the Stokes formula is not difficult. Namely, by writing  $\omega$  as  $\sum_s f_s \omega$  for some partition of unity, it suffices to prove the formula for M being a box in  $\mathbb{R}^n$ , which easily follows from the fundamental theorem of calculus.

34.4. **Integration on Lie groups.** Now let G be a real Lie group of dimension n. In this case given any  $\xi \in \wedge^n \mathfrak{g}^*$ , we can extend it to a left-invariant skew-symmetric tensor field (i.e., top differential form)  $\omega_{\xi}$  on G. Also, if  $\xi \neq 0$  then  $\omega = \omega_{\xi}$  is non-vanishing and thus defines an orientation and a left-invariant positive measure  $\mu_{\omega}$  on G. Note that  $\xi$  is unique up to scaling by a real number  $\lambda \in \mathbb{R}^{\times}$ . So, since  $\mu_{\lambda\omega} = |\lambda|\mu_{\omega}$ , we see that  $\mu_{\omega}$  is defined uniquely up to scaling by positive numbers. This measure is called the **left-invariant Haar measure** and we'll denote it just by  $\mu_L$  (assuming that the normalization has been chosen somehow).

In a similar way we can define the **right invariant Haar measure**  $\mu_R$  on G. One may ask if these measures coincide (or, rather, are proportional, since they are defined only up to normalization). This question is answered by the following proposition.

Given a 1-dimensional real representation V of a group G, let |V| be the representation of G on the same space with  $\rho_{|V|}(g) = |\rho_V(g)|$ , where  $\rho: G \to \operatorname{Aut}(V) = \mathbb{R}^{\times}$ .

Assessment: non-included
Stokes' formula for manifolds with boundary. Not in mathlib v4.27.0. Only the divergence theorem for boxes exists in `Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean`.

## Statement 214: Proposition 34.5
**Proposition 34.5.**  $\mu_L = \mu_R$  if and only if  $| \wedge^n \mathfrak{g}^* |$  (or, equivalently,  $| \wedge^n \mathfrak{g} |$ ) is a trivial representation of G.

Assessment: non-included
Left and right Haar measures coincide iff top exterior power is trivial (unimodularity criterion). Not in mathlib in this form.

## Statement 215: Proposition 34.8
**Proposition 34.8.** A compact Lie group is unimodular.

Assessment: included
A compact Lie group is unimodular. Mathlib has unimodularity of compact groups: `MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_haar` and related results in `Mathlib/MeasureTheory/Group/Measure.lean` establish that Haar measure on a compact group is bi-invariant.

## Statement 216: Proposition 35.1
**Proposition 35.1.** V admits a G-invariant unitary structure.

Assessment: non-included
This statement from Section 35 concerns representations of compact groups (unitarity, matrix coefficients, Peter-Weyl theorem). Not formalized in mathlib v4.27.0. Searched in `Mathlib/RepresentationTheory/` and `Mathlib/Topology/Algebra/`.

## Statement 217: Corollary 35.2
Corollary 35.2. Every finite dimensional representation V of a compact Lie group G is completely reducible.

Assessment: non-included
This statement from Section 35 concerns representations of compact groups (unitarity, matrix coefficients, Peter-Weyl theorem). Not formalized in mathlib v4.27.0. Searched in `Mathlib/RepresentationTheory/` and `Mathlib/Topology/Algebra/`.

## Statement 218: Proposition 35.3
**Proposition 35.3.** Matrix coefficients are smooth.

Assessment: non-included
This statement from Section 35 concerns representations of compact groups (unitarity, matrix coefficients, Peter-Weyl theorem). Not formalized in mathlib v4.27.0. Searched in `Mathlib/RepresentationTheory/` and `Mathlib/Topology/Algebra/`.

## Statement 219: Theorem 35.4
**Theorem 35.4.** (Orthogonality of matrix coefficients) We have

$$\int_{G} \psi_{V,ij}(g) \overline{\psi_{W,kl}(g)} dg = 0$$

if V is not isomorphic to W. Also

$$\int_{G} \psi_{V,ij}(g) \overline{\psi_{V,kl}(g)} dg = \frac{\delta_{ik} \delta_{jl}}{\dim V}.$$

Assessment: non-included
This statement from Section 35 concerns representations of compact groups (unitarity, matrix coefficients, Peter-Weyl theorem). Not formalized in mathlib v4.27.0. Searched in `Mathlib/RepresentationTheory/` and `Mathlib/Topology/Algebra/`.

## Statement 220: Theorem 35.5
**Theorem 35.5.** (Peter-Weyl theorem) The functions  $\psi_{V,ij}$  form an orthogonal basis of  $L^2(G)$ .

Assessment: non-included
This statement from Section 35 concerns representations of compact groups (unitarity, matrix coefficients, Peter-Weyl theorem). Not formalized in mathlib v4.27.0. Searched in `Mathlib/RepresentationTheory/` and `Mathlib/Topology/Algebra/`.

## Statement 221: Theorem 35.6
**Theorem 35.6.** (Peter-Weyl theorem, alternative formulation) The space  $L^2_{alg}(G)$  is dense in  $L^2(G)$ . In other words, the map  $\xi$  gives rise to an isomorphism

$$\widehat{\oplus}_{V \in \operatorname{Irrep}(G)} V \otimes V^* \to L^2(G)$$

where the first copy of G acts on V and the second one on  $V^*$  and the hat denotes the Hilbert space completion of the direct sum.

Note that this is again an instance of the double centralizer property! Namely, it expresses representation-theoretically the fact that the centralizer of the group of left translations on G is the group of right translations on G, and vice versa.

For example, let  $G = S^1$ . Then the irreducible representations of G are the characters  $\psi_n(\theta) = e^{in\theta}$ . So the Peter-Weyl theorem in this case says that  $\{e^{in\theta}\}$  is an orthonormal basis of  $L^2(S^1)$  with norm

$$||f||^2 := \frac{1}{2\pi} \int_0^{2\pi} |f(\theta)|^2 d\theta,$$

which is the starting point for Fourier analysis. So the Peter-Weyl theorem is similarly a starting point for **nonabelian Fourier** (or harmonic) analysis.

Assessment: non-included
This statement from Section 35 concerns representations of compact groups (unitarity, matrix coefficients, Peter-Weyl theorem). Not formalized in mathlib v4.27.0. Searched in `Mathlib/RepresentationTheory/` and `Mathlib/Topology/Algebra/`.

## Statement 222: Corollary 35.9
Corollary 35.9. Let  $\chi_V(g) = \text{Tr}(\rho_V(g))$  be the character of V. Then  $\{\chi_V(g), V \in \text{Irrep}G\}$  is an orthonormal basis of  $L^2(G)^G$ , the space of conjugation-invariant functions in  $L^2(G)$  (i.e., such that  $f(gxg^{-1}) = f(x)$ ).

Assessment: non-included
This statement from Section 35 concerns representations of compact groups (unitarity, matrix coefficients, Peter-Weyl theorem). Not formalized in mathlib v4.27.0. Searched in `Mathlib/RepresentationTheory/` and `Mathlib/Topology/Algebra/`.

## Statement 223: Lemma 36.1
**Lemma 36.1.** If A is compact then it maps bounded sets to precompact sets (i.e., ones whose closure is compact). In other words, for every bounded sequence  $\mathbf{v}_n \in H$ , the sequence  $A\mathbf{v}_n$  has a convergent subsequence.<sup>16</sup>

Assessment: non-included
This statement from Section 36 concerns compact operators, Hilbert-Schmidt theorem, and faithful representations of compact groups. Not formalized in mathlib v4.27.0.

## Statement 224: Proposition 36.2
**Proposition 36.2.** Let M be a compact manifold with positive smooth probability measure  $d\mathbf{x}$  and  $K(\mathbf{x}, \mathbf{y})$  a continuous function on  $M \times M$ . Then the operator

$$(A\psi)(\mathbf{y}) := \int_M K(\mathbf{x}, \mathbf{y}) \psi(\mathbf{x}) d\mathbf{x}.$$

 $<sup>^{16}</sup>$ The converse statement also holds, but we will not need it.

on  $L^2(M)$  is compact.

Assessment: non-included
This statement from Section 36 concerns compact operators, Hilbert-Schmidt theorem, and faithful representations of compact groups. Not formalized in mathlib v4.27.0.

## Statement 225: Theorem 36.3
**Theorem 36.3.** (Hilbert-Schmidt) Let  $A: H \to H$  be a compact self-adjoint operator. Then there is an orthogonal decomposition

$$H = \operatorname{Ker} A \oplus \widehat{\bigoplus}_{\lambda} H_{\lambda},$$

where  $\lambda$  runs over non-zero eigenvalues of A, and  $A|_{H_{\lambda}} = \lambda \cdot \text{Id}$ . Moreover, the spaces  $H_{\lambda}$  are finite dimensional and the eigenvalues  $\lambda$  are real and either form a finite set or a sequence going to 0.

Note that for finite rank operators, this obviously reduces to the standard theorem in linear algebra: a self-adjoint (Hermitian) operator on a finite dimensional space V with a positive Hermitian form has an orthogonal eigenbasis, and its eigenvalues are real.

Assessment: non-included
This statement from Section 36 concerns compact operators, Hilbert-Schmidt theorem, and faithful representations of compact groups. Not formalized in mathlib v4.27.0.

## Statement 226: Lemma 36.4
**Lemma 36.4.** Let G be a compact Lie group and  $G = G_0 \supset G_1 \supset ...$  be a nested sequence of closed subgroups without repetitions. Then this sequence is finite.

Assessment: non-included
This statement from Section 36 concerns compact operators, Hilbert-Schmidt theorem, and faithful representations of compact groups. Not formalized in mathlib v4.27.0.

## Statement 227: Corollary 36.5
**Corollary 36.5.** Any compact Lie group has a faithful finite dimensional representation, so it is isomorphic to a closed subgroup of the unitary group U(n).

Assessment: non-included
This statement from Section 36 concerns compact operators, Hilbert-Schmidt theorem, and faithful representations of compact groups. Not formalized in mathlib v4.27.0.

## Statement 228: Theorem 36.9
**Theorem 36.9.** The algebra  $L^2_{alg}(G)$  is dense in the algebra of continuous functions C(G) in the supremum norm

$$||f|| = \max_{g \in G} |f(g)|.$$

Assessment: non-included
This statement from Section 36 concerns compact operators, Hilbert-Schmidt theorem, and faithful representations of compact groups. Not formalized in mathlib v4.27.0.

## Statement 229: Corollary 36.11
Corollary 36.11. Let  $A \subset L^2_{alg}(G)$  be a left-invariant subalgebra stable under complex conjugation and separating points on G. Then  $A = L^2_{alg}(G)$ .

Assessment: non-included
This statement from Section 36 concerns compact operators, Hilbert-Schmidt theorem, and faithful representations of compact groups. Not formalized in mathlib v4.27.0.

## Statement 230: Proposition 36.12
**Proposition 36.12.** Let V be a faithful finite dimensional representation of a compact Lie group G. Then:

- (i) If V is unimodular then the subalgebra  $A \subset C(G)$  generated by matrix coefficients  $f(\rho_V(g)v)$ ,  $v \in V$ ,  $f \in V^*$ , coincides with  $L^2_{alg}(G)$ .
- (ii) If Y an irreducible finite dimensional representation of G, then for some n, m, the representation Y is contained as a direct summand in  $V^{\otimes n} \otimes V^{*\otimes m}$ . Moreover, if V is unimodular then one may take m = 0.
- *Proof.* (i) Let  $d := \dim(V)$ . It is clear that  $A \subset L^2_{\text{alg}}(G)$  is G-invariant and A separates points on G, since V is faithful. Also G is a closed subgroup of  $SU(V) \subset V \otimes V^*$ , and for a unitary matrix with determinant 1 one has  $g^{\dagger} = g^{-1} = \wedge^{d-1}g$ . Thus A is invariant under complex conjugation. So by Corollary 36.11  $A = L^2_{\text{alg}}(G)$ .
- (ii) It suffices to establish the unimodular case since in general we may replace V with the unimodular representation  $V \oplus V^*$ . But then by (i),  $L^2_{alg}(G)$  is a quotient of  $S(V \otimes V^*)$ , which implies the statement.  $\square$

Assessment: non-included
This statement from Section 36 concerns compact operators, Hilbert-Schmidt theorem, and faithful representations of compact groups. Not formalized in mathlib v4.27.0.

## Statement 231: Theorem 37.1
**Theorem 37.1.** (Haar, von Neumann) G admits a unique left-invariant probability measure.

This measure is also automatically right-invariant (since it is unique) and is called the **Haar measure** on G.

Assessment: included
Haar measure: existence and uniqueness of left-invariant measure on locally compact groups. Mathlib has Haar measure in `Mathlib/MeasureTheory/Measure/Haar/Basic.lean` with existence (`MeasureTheory.Measure.haarMeasure`) and uniqueness (`MeasureTheory.Measure.haar_eq_smul_haarMeasure`).

## Statement 232: Corollary 37.4
Corollary 37.4. Finite dimensional (continuous) representations of a compact topological group G with a countable base are unitary and completely reducible.

The proof is the same as for Lie groups, once we have the integration theory, which we now do.

Assessment: non-included
This statement from Section 37 concerns compact topological groups (complete reducibility, Peter-Weyl for topological groups, inverse limits). Not formalized in mathlib v4.27.0.

## Statement 233: Theorem 37.5
**Theorem 37.5.** (i) (Peter-Weyl theorem) Let G be a compact topological group with a countable base. Then the set IrrepG is countable, and

$$L^2(G) = \widehat{\oplus}_{V \in \mathrm{Irrep}(G)} V \otimes V^*$$

as a  $G \times G$ -module.

(ii) The subspace  $L^2_{alg}(G) = \bigoplus_{V \in Irrep(G)} V \otimes V^*$  is dense in C(G) in the supremum norm.

Again, the proof is analogous to Lie groups, using a delta-like sequence of continuous hat functions. Namely, we may take

$$h_N(x) = c_N \max(\frac{1}{N} - d(x, 1), 0),$$

where d is some metric defining the topology of G, and  $c_N > 0$  are normalization constants such that  $\int_G h_N(x) dx = 1$ .

Assessment: non-included
This statement from Section 37 concerns compact topological groups (complete reducibility, Peter-Weyl for topological groups, inverse limits). Not formalized in mathlib v4.27.0.

## Statement 234: Corollary 37.7
**Corollary 37.7.** Any compact topological group with countable base is an inverse limit of a sequence of compact Lie groups ...  $\rightarrow G_1 \rightarrow G_0$ , where the maps  $G_{i+1} \rightarrow G_i$  are surjective.

Assessment: non-included
This statement from Section 37 concerns compact topological groups (complete reducibility, Peter-Weyl for topological groups, inverse limits). Not formalized in mathlib v4.27.0.

## Statement 235: Theorem 38.2
**Theorem 38.2.** The bound states of the hydrogen atom, up to scaling, are

$$\psi_{n\ell m}(r,\phi,\theta) = r^{\ell} e^{-\frac{r}{n}} L_{n-\ell-1}^{2\ell+1}(\frac{2r}{n}) Y_{\ell}^{m}(\theta,\phi),$$

where  $Y_{\ell}^{m}(\theta, \phi) = e^{im\theta}P_{\ell}^{m}(\phi)$  are spherical harmonics, where  $n \in \mathbb{Z}_{>0}$ ,  $\ell$  an integer between 0 and n-1, and m is an integer between  $\ell$  and  $-\ell$ . The energy of the state  $\psi_{n\ell m}$  is  $E_n = -\frac{1}{2n^2}$ .

Assessment: non-included
Hydrogen atom energy levels (Schrodinger equation). This is a physics application, not in mathlib.

## Statement 236: Corollary 39.1
Corollary 39.1. The space  $W_n$  of states with principal quantum number n has dimension  $n^2$ .

Assessment: non-included
Dimension of hydrogen atom energy eigenspace. This is a physics application, not in mathlib.

## Statement 237: Proposition 40.1
**Proposition 40.1.** The normalizer N(H) of H in  $G_{ad}$  coincides with the stabilizer of  $\mathfrak{h}$  and contains H as a normal subgroup, so that N(H)/H is naturally isomorphic to the Weyl group W.

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 238: Proposition 40.4
**Proposition 40.4.** Semisimple Lie algebras  $\mathfrak{g}$  over K which split over a Galois extension L of K are classified by the first Galois cohomology  $H^1(\Gamma, \operatorname{Aut}(\mathfrak{g}_L))$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 239: Theorem 40.6
**Theorem 40.6.** Real semisimple Lie algebras whose complexification is  $\mathfrak{g}$  (i.e., **real forms** of  $\mathfrak{g}$ ) are classified by  $s \in \operatorname{Aut}(D) \ltimes G_{\operatorname{ad}}$  such that  $s\overline{s} = 1$  modulo equivalence  $s \mapsto as\overline{a}^{-1}$ ,  $a \in \operatorname{Aut}(\mathfrak{g})$ , where complex conjugation acts trivially on  $\operatorname{Aut}(D)$ .

We denote the real form of  $\mathfrak{g}$  corresponding to s by  $\mathfrak{g}_{(s)}$ . Namely,  $\mathfrak{g}_{(s)} = \{x \in \mathfrak{g} : \overline{x} = s(x)\}$ . For example,  $\mathfrak{g}_{(1)}$  is the split form, consisting of real  $x \in \mathfrak{g}$ , i.e., such that  $\overline{x} = x$ .

Alternatively, one may define the **antilinear involution**  $\sigma_s(x) = \overline{s(x)}$ , and  $\mathfrak{g}_{(s)}$  is the set of fixed points of  $\sigma_s$  in  $\mathfrak{g}$ .

In particular, such s defines an element  $s_0 \in \operatorname{Aut}(D)$  such that  $s_0^2 = 1$ . Note that the conjugacy class of  $s_0$  is invariant under equivalences. The element  $s_0$  permutes connected components of D, preserving some and matching others into pairs. Thus every semisimple real Lie algebra is a direct sum of simple ones, and each simple one either has a connected Dynkin diagram D (i.e., the complexified Lie algebra  $\mathfrak{g}$  is still simple) or consists of two identical components (i.e., the complexified Lie algebra is  $\mathfrak{g} = \mathfrak{a} \oplus \mathfrak{a}$  for some simple complex  $\mathfrak{a}$ ). In the latter case  $s = (g, \overline{g}^{-1})s_0$  where  $s_0$  is the transposition and  $g \in \operatorname{Aut}(\mathfrak{a})$ , so s is cohomologous to  $s_0$  by taking a = (g, 1). Thus in this case  $\mathfrak{g}_{(s)} = \mathfrak{g}_{(s_0)} = \mathfrak{a}$ , a complex simple Lie algebra regarded as a real Lie algebra.

It remains to consider the case when D is connected, i.e.,  $\mathfrak{g}$  is simple.

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 240: Proposition 41.1
**Proposition 41.1.** The Killing form of  $\mathfrak{g}^c$  is negative definite.

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 241: Corollary 41.2
Corollary 41.2. Let  $G_{\text{ad}}^c = \text{Aut}(\mathfrak{g}^c)^{\circ}$ . Then  $G_{\text{ad}}^c$  is a connected compact Lie group with Lie algebra  $\mathfrak{g}^c$ .

In particular, this gives a new proof that representations of a finite dimensional semisimple Lie algebra are completely reducible (by using Weyl's unitary trick, see Subsection 35.1).

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 242: Theorem 41.5
**Theorem 41.5.** Real forms of  $\mathfrak{g}$  are in bijection with conjugacy classes of involutions  $\theta \in \operatorname{Aut}(\mathfrak{g}^c)$ , via  $\theta \mapsto \omega_{\theta} := \theta \circ \omega = \omega \circ \theta$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 243: Proposition 41.7
**Proposition 41.7.** There exists a Cartan subalgebra  $\mathfrak{h}$  in  $\mathfrak{g}$  invariant under  $\theta$ , such that  $\mathfrak{h} \cap \mathfrak{k}$  is a Cartan subalgebra in  $\mathfrak{k}$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 244: Lemma 41.8
**Lemma 41.8.** The space  $\mathfrak{h}_{-}$  does not contain any coroots of  $\mathfrak{g}$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 245: Lemma 42.1
**Lemma 42.1.** Suppose the Vogan diagram of  $\theta$  contains a black vertex i. Then changing the colors of all neighbors j of i such that  $a_{ij}$  is odd gives an equivalent Vogan diagram.

The same lemma holds, with the same proof, in the case of another inner class (which for exceptional Lie algebras is possible only for  $E_6$ ), except we should ignore the vertices matched into pairs (so i and j should be  $\theta$ -stable vertices).

- 42.2. Classification of real forms. We are now ready to classify real forms of exceptional Lie algebras.
- **1. Type**  $G_2$ . We have two color configurations up to equivalence:  $\circ \circ$  and  $(\bullet \circ, \circ \bullet, \bullet \bullet)$ . The first corresponds to the compact form  $G_2^c$  and the second to the split form  $G_2^{\text{spl}}$ . It is easy to check that in the second case  $\mathfrak{k} = \mathfrak{sl}_2 \oplus \mathfrak{sl}_2$  (indeed, it has dimension 6 and rank 2). So we don't have other real forms.
- **2.** Type  $F_4$ . Let  $\alpha_1, \alpha_2$  be short roots and  $\alpha_3, \alpha_4$  long roots. Then all nonzero off-diagonal  $a_{ij}$  are odd except  $a_{23} = -2$ . So we may

change the colors of the neighbors of any black vertex, except that if the black vertex is 2 then we should not change the color of 3. By such changes, we can bring the colors at 3,4 into the form  $\circ \circ$  or  $\circ \bullet$ , and then bring the colors at 1,2 to the form  $\circ \circ$  or  $\bullet \circ$ . So we are down to four configurations:

Moreover, the fourth case,  $\bullet \circ \circ \bullet$ , is actually equivalent to the third one,  $\circ \circ \circ \bullet$ . This is seen from the chain of equivalences

$$\circ \circ \circ \bullet = \circ \circ \bullet \bullet = \circ \bullet \circ \circ = \bullet \circ \bullet \circ = \bullet \bullet \bullet = \bullet \circ \circ \bullet = \bullet \circ \circ \bullet$$

Thus we are left with three variants,

The first configuration,  $\circ \circ \circ \circ$ , corresponds to the compact form  $F_4^c$ .

In the second case,  $\bullet \circ \circ \circ$ ,  $\alpha(\theta) = -1$  exactly when the root  $\alpha$  has half-integer coordinates (recall that there are 16 such roots, see Subsection 23.3). Thus the Lie algebra  $\mathfrak{k}$  is comprised by the root subspaces for roots with integer coordinates and the Cartan subagebra, i.e.,  $\mathfrak{k} = \mathfrak{so}_9$  (type  $B_4$ ). Also in this case  $\mathfrak{p} = S$ , the spin representation of  $\mathfrak{so}_9$ . This is not the split form, since for the split form dim  $\mathfrak{k}$  should be 24 and here it is 36. Let us denote this form  $F_4^1$ .

Thus, the third case,  $\circ \circ \circ \bullet$ , must be the split form,  $F_4^{\rm spl}$ . We see that  $\mathfrak{k}$  contains the 21-dimensional Lie algebra  $\mathfrak{sp}_6 = C_3$  (generated by the simple roots  $\alpha_1, \alpha_2, \alpha_3$ ), so given that  $\mathfrak{k}$  has rank 4 and dimension 24, we have  $\mathfrak{k} = \mathfrak{sp}_6 \oplus \mathfrak{sl}_2$ .

- 3. Type  $E_6$ , split inner class. In this case in the Vogan diagram two pairs of vertices are connected, so we can only color the two remaining vertices. So we have two equivalence classes of colorings  $-\infty$  and  $(\bullet \bullet, \bullet \circ, \circ \bullet)$ . Let us show that they correspond to two different real forms. Consider first the  $\infty$  case. In this case  $\theta$  is simply the diagram automorphism, so we have  $\mathfrak{k} = F_4$ , as the Dynkin diagram of  $F_4$  is obtained by folding the Dynkin diagram of  $E_6$  (check it!). This is not the split form since dim  $\mathfrak{k} = 52$ , but for the split form it is 36; denote this form by  $E_6^1$ . So the split form  $E_6^{\mathrm{spl}}$  corresponds to the second equivalence class  $(\bullet \bullet, \bullet \circ, \circ \bullet)$ . One can show that in this case  $\mathfrak{k} = \mathfrak{sp}_8$ , i.e., type  $C_4$  (check it!).
- 4.  $E_6, E_7, E_8$ , compact inner class. In this case the Vogan diagram has no arrows and just is the usual Dynkin diagram with vertices colored black and white. One option is that all vertices are white, this corresponds to the compact forms  $E_6^c, E_7^c, E_8^c$  ( $\theta = 1$ ). If there is at least one black vertex, then by using equivalence transformations we

can make sure that the nodal vertex is black. Then flipping the color of its neighbors if needed, we can make sure that the vertex on the shortest leg is also black. This allows us to change the color of the nodal vertex whenever we want (as long as the vertex on the shortest leg remains black).

We now want to unify the coloring of the long leg. We can bring the long leg to the following normal forms:

 $E_6$ :  $\circ \circ$ ,  $\bullet \circ = \bullet \bullet = \circ \bullet$ . But by flipping the colors on the neighbors of the nodal vertex, we see that  $\bullet \circ$  and  $\circ \circ$  are equivalent, so all patterns are equivalent to  $\bullet \bullet$ .

 $E_7$ :  $\circ \circ \circ, \bullet \circ \circ = \bullet \bullet \circ = \circ \bullet \bullet = \circ \circ, \bullet \circ \bullet = \bullet \bullet \bullet = \circ \circ$ . But by flipping the colors on the neighbors of the nodal vertex, we see that all patterns are equivalent to  $\bullet \bullet \bullet$ .

 $E_8$ : 0 0 00,  $\bullet$  0 00 =  $\bullet$   $\bullet$  00 = 0  $\bullet$   $\bullet$ 0 = 0 0  $\bullet$  $\bullet$  = 0 0 0 $\bullet$ ,

$$\bullet \circ \circ \bullet = \bullet \circ \bullet \bullet = \bullet \bullet \circ = \begin{cases} \bullet \circ \bullet \circ \\ \circ \bullet \circ \circ \end{cases}$$

$$= \bullet \bullet \bullet \bullet = \bullet \bullet \circ \bullet = \circ \bullet \bullet \bullet = \begin{cases} \circ \bullet \circ \bullet \\ \circ \circ \bullet \circ \end{cases}$$

But by flipping the colors on the neighbors of the nodal vertex, we see that all patterns are equivalent to  $\bullet \bullet \bullet \bullet$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 246: Proposition 43.2
**Proposition 43.2.** A representation  $L_{\lambda}$  of  $\mathfrak{g}$  of highest weight  $\lambda \in P_+$  lifts to a representation of  $G_{\mathrm{ad}}$  (or, equivalently,  $G_{\mathrm{ad}}^c$ ) if and only if  $\lambda \in P_+ \cap Q$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 247: Lemma 43.3
**Lemma 43.3.** If X is a connected compact manifold then the fundamental group  $\pi_1(X)$  is finitely generated.

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 248: Theorem 43.4
**Theorem 43.4.** Let  $\mathfrak{g}$  be a semisimple complex Lie algebra and  $G_{\mathrm{ad}}^c$  the corresponding adjoint compact group. Then  $\pi_1(G_{\mathrm{ad}}^c) = P^{\vee}/Q^{\vee}$ . Thus the universal cover  $G^c$  of  $G_{\mathrm{ad}}^c$  is a compact Lie group.

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 249: Corollary 43.5
Corollary 43.5. (i) If  $\mathfrak{g}$  is a simple complex Lie algebra then the simply connected Lie group  $G^c$  corresponding to the Lie algebra  $\mathfrak{g}^c$  is compact, and its center is  $P^{\vee}/Q^{\vee}$ , which also equals  $\pi_1(G^c_{\mathrm{ad}})$ .

- (ii) Let  $\Gamma \subset P^{\vee}/Q^{\vee}$  be a subgroup. Then the irreducible representations of  $G/\Gamma$  are  $L_{\lambda}$  such that  $\lambda$  defines the trivial character of  $\Gamma$ .
- (iii) Let  $G_i^c$  be the simply connected compact Lie group corresponding to a simple summand  $\mathfrak{g}_i$  of a semisimple Lie algebra  $\mathfrak{g} = \bigoplus_{i=1}^n \mathfrak{g}_i$ . Then any connected Lie group with Lie algebra  $\mathfrak{g}^c$  is compact and has the

form  $(\prod_{i=1}^n G_i^c)/Z$ , where  $Z = \pi_1(G^c)$  is a subgroup of  $\prod_i Z_i$ , and  $Z_i = P_i^{\vee}/Q_i^{\vee}$  are the centers of  $G_i^c$ . Moreover, every semisimple connected compact Lie group has this form.

In particular, it follows that simply connected semisimple compact Lie groups are of the form  $\prod_{i=1}^n G_i^c$ , where  $G_i^c$  are simply connected and simple.<sup>24</sup>

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 250: Corollary 43.6
**Corollary 43.6.** Any connected compact Lie group is the quotient of  $T \times C$  by a finite central subgroup, where  $T = (S^1)^m$  is a torus and C is compact, semisimple and simply connected.

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 251: Theorem 43.7
**Theorem 43.7.** (Polar decomposition for  $G_{ad,\theta}$ ) The multiplication map  $\mu: K^c \times P_\theta \to G_{ad,\theta}$  is a diffeomorphism. Thus  $G_{ad,\theta} \cong K^c \times \mathbb{R}^{\dim \mathfrak{p}}$  as a manifold (in particular,  $G_{ad,\theta}$  is homotopy equivalent to  $K^c$ ).

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 252: Corollary 43.8
Corollary 43.8. The multiplication map defines a diffeomorphism

$$G_{\mathrm{ad}}^c \times \mathbf{P} \cong G_{\mathrm{ad}}$$
,

where **P** is the set of elements of  $G_{ad}$  acting on  $\mathfrak{g}$  by positive Hermitian operators. In particular,  $\pi_1(G_{ad}) = \pi_1(G_{ad}^c) = P^{\vee}/Q^{\vee}$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 253: Corollary 43.9
Corollary 43.9. If G is a semisimple complex Lie group then the center Z of G is contained in  $G^c$ , i.e., coincides with the center  $Z^c$  of  $G^c$ . Thus the restriction of finite dimensional representations from G to  $G^c$  is an equivalence of categories.

This also implies that by taking coverings the polar decomposition applies verbatim to the real form  $G_{\theta} = G^{\omega_{\theta}} \subset G$  of any connected complex semisimple Lie group G instead of  $G_{ad}$ . We note, however, that if G is simply connected, then  $G_{\theta}^{\circ}$  need not be. In fact, its fundamental group could be infinite. The simplest example is  $G = SL_2(\mathbb{C})$ , then for the split form  $G_{\theta} = SL_2(\mathbb{R})$ , which as we showed is homotopy equivalent to  $SO(2) = S^1$ , i.e. its fundamental group is  $\mathbb{Z}$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 254: Proposition 43.13
**Proposition 43.13.** Suppose  $\mathfrak{g}_{\theta}$  is a real form of a semisimple complex Lie algebra  $\mathfrak{g}$ , G a connected complex Lie group with Lie algebra  $\mathfrak{g}$ , and  $G_{\theta} = G^{\omega_{\theta}}$ . Then  $G_{\theta}$ ,  $G_{\theta}^{\circ}$  are linear groups. Moreover, every connected real semisimple linear Lie group is of the form  $G_{\theta}^{\circ}$

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 255: Lemma 44.1
**Lemma 44.1.** Any two Cartan subalgebras in  $\mathfrak{g}^c$  equipped with systems of simple roots are conjugate under  $G^c$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 256: Corollary 44.2
Corollary 44.2. Any two maximal tori in G or  $G^c$  equipped with systems of simple roots are conjugate.

We also have

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 257: Theorem 44.3
**Theorem 44.3.** Every element of a connected compact Lie group K is contained in a maximal torus, and all maximal tori in K are conjugate (even when equipped with systems of simple roots).

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 258: Corollary 44.4
Corollary 44.4. The exponential map  $\exp: \mathfrak{g}^c \to G^c$  is surjective.<sup>26</sup>

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 259: Proposition 44.9
**Proposition 44.9.** (Jordan decomposition in G). Every element  $g \in G$  has a unique factorization  $g = g_s g_u$ , where  $g_s \in G$  is semisimple,  $g_u \in G$  is unipotent and  $g_s g_u = g_u g_s$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 260: Proposition 44.11
- **Proposition 44.11.** (i) Let  $\mathfrak{a}$  be a maximal abelian subspace of  $\mathfrak{p}_{\theta}$ . Then the centralizer  $\mathfrak{z}$  of  $\mathfrak{a}$  in  $\mathfrak{g}^c$  has the form  $\mathfrak{m} \oplus \mathfrak{a}$ , where  $\mathfrak{m}$  is a reductive Lie algebra contained in  $\mathfrak{k}^c$ . Moreover, if  $\mathfrak{t}$  is a Cartan subalgebra of  $\mathfrak{m}$  then  $\mathfrak{t} \oplus i\mathfrak{a}$  is a Cartan subalgebra of  $\mathfrak{g}^c$  and  $\mathfrak{t} \oplus \mathfrak{a}$  is a Cartan subalgebra of  $\mathfrak{g}_{\theta}$ .
- (ii) If  $a \in \mathfrak{a}$  is sufficiently generic then the centralizer of a in  $\mathfrak{p}_{\theta}$  is  $\mathfrak{a}$ .
  - (iii) For any  $p \in \mathfrak{p}_{\theta}$  there exists  $k \in K^c$  such that  $\mathrm{Ad}_k(p) \in \mathfrak{a}$ .
  - (iv) All maximal abelian subspaces of  $\mathfrak{p}_{\theta}$  are conjugate by  $K^c$ .
- Proof. (i) Let  $x \in \mathfrak{g}^c$ ,  $[x,\mathfrak{a}] = 0$ . Write  $x = x_+ + x_-$ ,  $x_+ \in \mathfrak{k}^c$ ,  $x_- \in \mathfrak{p}^c$ . Then  $[x_{\pm},\mathfrak{a}] = 0$ , thus  $x_- \in \mathfrak{a}$  by maximality of  $\mathfrak{a}$ . So  $x \in \mathfrak{k}^c \oplus \mathfrak{a}$ . Thus  $\mathfrak{z} = \mathfrak{m} \oplus \mathfrak{a}$  where  $\mathfrak{m} \subset \mathfrak{k}^c$  is a reductive Lie algebra. Moreover, if  $\mathfrak{t} \subset \mathfrak{m}$  is a Cartan subalgebra then  $\mathfrak{t} \oplus i\mathfrak{a}$  is a maximal abelian subalgebra of  $\mathfrak{g}^c$ , hence is a Cartan subalgebra. Similarly,  $\mathfrak{t} \oplus \mathfrak{a}$  is a Cartan subalgebra of  $\mathfrak{g}_\theta$ .
- (ii) Consider the group  $T_{\mathfrak{a}} := \exp(i\mathfrak{a}) \subset G^c$ . It is clear from (i) that this is a compact torus. Thus for a generic enough  $a \in \mathfrak{a}$ , the 1-parameter subgroup  $e^{ita}$  is dense in  $T_{\mathfrak{a}}$ . So if  $p \in \mathfrak{p}_{\theta}$  and [p, a] = 0 then  $e^{ita}$  commutes with p, hence so do  $T_{\mathfrak{a}}$  and  $\mathfrak{a}$ . So by maximality of  $\mathfrak{a}$  we have  $p \in \mathfrak{a}$ .
- (iii) Let  $a \in \mathfrak{a}$  be generic enough as in (ii). Then by (ii),  $\mathrm{Ad}_k(p) \in \mathfrak{a}$  if and only if  $[\mathrm{Ad}_k(p), a] = 0$ .

Consider the function  $f: K^c \to \mathbb{R}$  given by  $f(b) := (\mathrm{Ad}_b(p), a)$ . This function is continuous, so attains a maximum on the compact group  $K^c$ . Suppose k is a maximum point of f. Let  $p_0 := \mathrm{Ad}_k(p)$ . Differentiating f at k, we get  $([x, p_0], a) = 0$  for all  $x \in \mathfrak{k}^c$ . Thus  $(x, [p_0, a]) = 0$  for all  $x \in \mathfrak{k}^c$ . But  $[p_0, a] \in \mathfrak{k}^c$  and the inner product on  $\mathfrak{k}^c$  is nondegenerate. Thus  $[p_0, a] = 0$ , as desired.

- (iv) Let  $\mathfrak{a}, \mathfrak{a}'$  be maximal abelian subspaces of  $\mathfrak{p}_{\theta}$ . Pick a generic element  $p \in \mathfrak{a}'$  as in (ii). By (iii) we can find  $k \in K^c$  such that  $\mathrm{Ad}_k(p) = a \in \mathfrak{a}$ . Moreover, a is generic in  $\mathrm{Ad}_k(\mathfrak{a}')$ . So for every  $b \in \mathfrak{a}$  we have  $[b, \mathrm{Ad}_k(\mathfrak{a}')] = 0$  (as [b, a] = 0). By maximality of  $\mathfrak{a}'$  this implies that  $b \in \mathrm{Ad}_k(\mathfrak{a}')$ , i.e.,  $\mathfrak{a} \subset \mathrm{Ad}_k(\mathfrak{a}')$ . Thus dim  $\mathfrak{a} \leq \dim \mathfrak{a}'$ . Switching  $\mathfrak{a}, \mathfrak{a}'$ , we also get dim  $\mathfrak{a}' \leq \dim \mathfrak{a}$ , hence dim  $\mathfrak{a} = \dim \mathfrak{a}'$  and  $\mathfrak{a} = \mathrm{Ad}_k(\mathfrak{a}')$ , as claimed.
- 44.4. The Cartan decomposition of semisimple linear groups. Let  $\mathfrak{a} \subset \mathfrak{p}_{\theta}$  be a maximal abelian subspace and  $A = \exp(\mathfrak{a}) \subset P_{\theta} \subset G_{\theta}$ . This is a subgroup isomorphic to  $\mathbb{R}^n$ , where  $n = \dim \mathfrak{a}$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 261: Theorem 44.12
**Theorem 44.12.** (The Cartan decomposition) We have  $G_{\theta} = K^{c}AK^{c}$ . In other words, every element  $g \in G_{\theta}$  has a factorization  $g = k_{1}ak_{2}$ ,  $k_{1}, k_{2} \in K^{c}$ ,  $a \in A$ .<sup>27</sup>

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 262: Theorem 44.15
**Theorem 44.15.** (E. Cartan) Let  $G_{\theta}$  be a real form of a connected semisimple complex group G. Then any compact subgroup L of  $G_{\theta}$  is conjugate to a subgroup of  $K^c$  by an element of  $P_{\theta}$ . Also every compact subgroup of  $G_{\theta}$  is contained in a maximal one. Thus all maximal compact subgroups of  $G_{\theta}$  are conjugate (to  $K^c$ ).

<sup>&</sup>lt;sup>27</sup>This factorization is not unique.

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 263: Proposition 44.16
Proposition 44.16. This minimum point is unique.

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 264: Lemma 44.17
**Lemma 44.17.** Let a, M be symmetric real matrices such that M is positive definite. Then the function

$$\phi(t) := \text{Tr}(\exp(ta)M), \ t \in \mathbb{R}$$

is convex, and is strictly convex if  $a \neq 0$ .

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 265: Theorem 44.19
- **Theorem 44.19.** (i) A  $\theta$ -stable Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}_{\theta}$  is maximally split iff  $\mathfrak{h}_{-} := \mathfrak{h} \cap \mathfrak{p}_{\theta}$  is a maximal abelian subspace in  $\mathfrak{p}_{\theta}$ .
- (ii) A  $\theta$ -stable Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}_{\theta}$  is maximally compact iff  $\mathfrak{h}_+ := \mathfrak{h} \cap \mathfrak{k}^c$  is a Cartan subalgebra in  $\mathfrak{k}^c$ , and in this case  $s(\mathfrak{h}) = \operatorname{rank}(\mathfrak{g}) \operatorname{rank}(\mathfrak{k})$ .
- (iii) Any two maximally split  $\theta$ -stable Cartan subalgebras are conjugate by  $K^c$ .
- (iv) Any two maximally compact  $\theta$ -stable Cartan subalgebras are conjugate by  $K^c$ .
- (v) Any Cartan subalgebra in  $\mathfrak{g}_{\theta}$  is conjugate to a  $\theta$ -stable one by an element of  $G_{\theta}$  (or, equivalently,  $P_{\theta}$ ).
- *Proof.* (i) It is clear that if  $\mathfrak{h}_{-}$  is a maximal abelian subspace of  $\mathfrak{p}_{\theta}$  then  $\mathfrak{h}$  is maximally split, since by Proposition 44.11 any abelian subspace of  $\mathfrak{p}_{\theta}$  can be conjugated into  $\mathfrak{h}_{-}$ . Conversely, if  $\mathfrak{h}$  is maximally split, suppose that  $a \in \mathfrak{p}_{\theta}, a \notin \mathfrak{h}_{-}$  with  $[a, \mathfrak{h}_{-}] = 0$ . Then  $\mathfrak{h}'_{-} = \mathfrak{h}_{-} \oplus \mathbb{R}\mathfrak{a}$ , and let  $\mathfrak{h}'$  be a Cartan subalgebra of  $\mathfrak{g}_{\theta}$  containing  $\mathfrak{h}'_{-}$ . Then  $s(\mathfrak{h}') > s(\mathfrak{h})$ , a contradiction.
- (ii) It is clear that if  $\mathfrak{h}_+$  is a Cartan subalgebra of  $\mathfrak{k}^c$  then  $\mathfrak{h}$  is maximally compact. Also given a Cartan subalgebra  $\mathfrak{h}_+ \subset \mathfrak{k}^c$ , take a Cartan subalgebra  $\mathfrak{h}$  of  $\mathfrak{g}_{\theta}$  containing  $\mathfrak{h}_+$ . Then  $s(\mathfrak{h}) \leq \operatorname{rank}(\mathfrak{g}) \operatorname{rank}(\mathfrak{k})$ . This implies that for any maximally compact  $\mathfrak{h}$ , we have that  $\mathfrak{h} \cap \mathfrak{k}^c$  is a Cartan subalgebra in  $\mathfrak{k}^c$ , and  $s(\mathfrak{h}) = \operatorname{rank}(\mathfrak{g}) \operatorname{rank}(\mathfrak{k})$ .
- (iii) Let  $\mathfrak{h}, \mathfrak{h}'$  be maximally split  $\theta$ -stable Cartan subalgebras in  $\mathfrak{g}_{\theta}$ . Then  $\mathfrak{h}_{-}, \mathfrak{h}'_{-}$  are maximal abelian subspaces of  $\mathfrak{p}_{\theta}$ . So they are conjugate by  $K^c$  by Proposition 44.11, thus we may assume that  $\mathfrak{h}_{-} = \mathfrak{h}'_{-}$ . Let  $Z^c_{-}$  be the centralizer of  $\mathfrak{h}_{-}$  in  $K^c$ . It is a compact group, and it is clear that  $\mathfrak{h}_{+}, \mathfrak{h}'_{+} \subset \text{Lie}(Z^c_{-})$  are Cartan subalgebras. Hence they are conjugate by an element of  $Z^c_{-}$ , as desired.
- (iv) Let  $\mathfrak{h}, \mathfrak{h}'$  be maximally compact  $\theta$ -stable Cartan subalgebras in  $\mathfrak{g}_{\theta}$ . Then  $\mathfrak{h}_{+}, \mathfrak{h}'_{+}$  are Cartan subalgebras of  $\mathfrak{k}^{c}$ , so they are conjugate by  $K^{c}$  and we may assume that  $\mathfrak{h}_{+} = \mathfrak{h}'_{+}$ . Let  $Z_{+}$  be the centralizer of  $\mathfrak{h}_{+}$  in  $G_{\theta}$  and  $\mathfrak{z}_{+} = \text{Lie}(Z_{+})$ . This is a  $\theta$ -stable reductive subalgebra of  $\mathfrak{g}_{\theta}$  containing  $\mathfrak{h}, \mathfrak{h}'$  whose center contains  $\mathfrak{h}_{+}$ . Thus  $\mathfrak{h}_{-}, \mathfrak{h}'_{-} \subset \text{Lie}(Z_{+})/\mathfrak{h}_{+}$  are  $\theta$ -stable split Cartan subalgebras, so they are conjugate by  $Z_{+}^{c} := Z_{+} \cap K^{c}$  owing to (iii). This implies the statement.
- (v) The proof is by induction in the rank r of  $\mathfrak{g}_{\theta}$ , with obvious base r = 0. Suppose the statement is known for rank < r and let us prove it for rank r. Let  $\mathfrak{h} \subset \mathfrak{g}_{\theta}$  be a Cartan subalgebra. We have  $\mathfrak{h} = \mathfrak{h}_+ \oplus \mathfrak{h}_-$  where  $\mathfrak{h}_+, \mathfrak{h}_-$  are the subspaces of elements with imaginary and real

eigenvalues on the adjoint representation, respectively. The Lie group  $H_+ = \exp(\mathfrak{h}_+)$  is a compact torus, so it is contained in a maximal compact subgroup. Hence by Theorem 44.15  $H_+$  is conjugate to a subgroup of  $K^c$ . We may thus assume that  $\mathfrak{h}_+ \subset \mathfrak{k}^c$ .

As in (iv), let  $Z_+ \subset G_\theta$  be the centralizer of  $\mathfrak{h}_+$  and  $\mathfrak{z}_+ = \operatorname{Lie}(Z_+)$ . It suffices to show that  $\mathfrak{h}$  is conjugate to a  $\theta$ -stable Cartan subalgebra under  $Z_+$ . This is equivalent to saying that  $\mathfrak{h}_-$  is conjugate to a  $\theta$ -stable Cartan subalgebra of  $\mathfrak{z}_+/\mathfrak{h}_+$  under  $Z_+/H_+$ . So if  $\mathfrak{h}_+ \neq 0$  then the statement follows by the induction assumption, since the rank of  $\mathfrak{z}_+/\mathfrak{h}_+$  is smaller than r. On the other hand, if  $\mathfrak{h}_+ = 0$  then  $\mathfrak{h}$  is split, so  $\mathfrak{g}_\theta$  is split. In this case, let  $\mathfrak{h}_0$  be the standard Cartan subalgebra of  $\mathfrak{g}_\theta$ . Fixing systems of simple roots  $\Pi$  for  $\mathfrak{h}$  and  $\Pi_0$  for  $\mathfrak{h}_0$ , there exists an isomorphism  $\phi: (\mathfrak{g}_\theta, \mathfrak{h}, \Pi) \to (\mathfrak{g}_\theta, \mathfrak{h}_0, \Pi_0)$  which is given by an inner automorphism of  $\mathfrak{g}_\theta$ , i.e., an element  $g \in G_{\mathrm{ad},\theta}$ , which completes the induction step and the proof.  $\square$

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 266: Proposition 44.20
**Proposition 44.20.** Let f be a conjugation-invariant continuous function on a compact connected Lie group K with a maximal torus  $T \subset K$  and Haar probability measure dk. Then

$$\int_{K} f(k)dk = \frac{1}{|W|} \int_{T} f(t) |\Delta(t)|^{2} dt,$$

where  $\Delta(t)$  is the Weyl denominator,<sup>28</sup>

$$\Delta(t) = \rho(t)^{-1} \prod_{\alpha \in R^+} (\alpha(t) - 1).$$

Assessment: non-included
This statement concerns real forms, Cartan involutions, compact/split forms, or the structure theory of real semisimple Lie groups. Not formalized in mathlib v4.27.0. Searched in `Mathlib/Algebra/Lie/`, `Mathlib/Geometry/Manifold/`, and `Mathlib/Topology/`.

## Statement 267: Lemma 45.2
**Lemma 45.2.** (Cartan's magic formula) Let v be a vector field on M,  $L_v: \Omega^i(M) \to \Omega^i(M)$  the Lie derivative and  $\iota_v: \Omega^i(M) \to \Omega^{i-1}(M)$  the contraction operator. Then

$$L_v = \iota_v d + d\iota_v$$
.

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 268: Corollary 45.3
Corollary 45.3.  $L_v$  maps closed forms to exact forms, hence acts trivially in cohomology.

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 269: Corollary 45.4
**Corollary 45.4.** If a connected Lie group G acts on a manifold M then G acts trivially on  $H^{\bullet}(M, \mathbb{C})$ .

Suppose now that a compact connected Lie group G acts on a manifold M. Then we have the averaging operator  $P: \Omega^{\bullet}(M) \to \Omega^{\bullet}(M)$  over G which commutes with d and satisfies the equation  $P^2 = P$ , so we have a decomposition of complexes

$$\Omega^{\bullet}(M) = \Omega^{\bullet}(M)^G \oplus \Omega^{\bullet}(M)_0$$

where the first summand is the image of P and the second one is the kernel of P.

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 270: Theorem 45.5
**Theorem 45.5.** The complex  $\Omega^{\bullet}(M)_0$  is exact. Thus the cohomology  $H^{\bullet}(M,\mathbb{C})$  is computed by the complex of invariant differential forms  $\Omega^{\bullet}(M)^G$ .

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 271: Corollary 45.6
Corollary 45.6. If G is a compact Lie group then  $H^{\bullet}(G, \mathbb{C})$  is computed by the complex  $\Omega^{\bullet}(G)^G$  of left-invariant differential forms on G.

The complex  $\Omega^{\bullet}(G)^G$  is called the **Chevalley-Eilenberg complex** of G.

45.2. Cohomology of Lie algebras. It turns out that the Chevalley-Eilenberg complex of G can be described purely algebraically in terms of the Lie algebra  $\mathfrak{g} = \text{Lie}(G)_{\mathbb{C}}$ . To this end, we will need another lemma from basic differential geometry.

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 272: Lemma 45.7
**Lemma 45.7.** (Cartan differentiation formula) Let  $\omega \in \Omega^m(M)$  and  $v_0, ..., v_m$  be vector fields on M. Then

$$d\omega(v_0, ..., v_m) = \sum_{i} (-1)^i L_{v_i}(\omega(v_0, ..., \widehat{v}_i, ..., v_m)) +$$

$$\sum_{i < j} (-1)^{i+j} \omega([v_i, v_j], v_0, ..., \widehat{v}_i, ..., \widehat{v}_j, ..., v_m)$$

(where the hats indicate the omitted terms).

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 273: Corollary 45.8
Corollary 45.8. Let G be a Lie group and  $\omega \in \Omega^m(G)^G$  be a left-invariant differential form. Then for any left-invariant vector fields  $v_0, ..., v_m$  we have

$$(45.1) d\omega(v_0, ..., v_m) = \sum_{i < j} (-1)^{i+j} \omega([v_i, v_j], v_0, ..., \widehat{v}_i, ..., \widehat{v}_j, ..., v_m).$$

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 274: Corollary 45.9
Corollary 45.9. For any Lie group G the complex  $\Omega^{\bullet}(G)^G$  coincides with the complex

$$0 \to \mathbb{C} \to \mathfrak{g}^* \to (\wedge^2 \mathfrak{g})^* \to \dots (\wedge^m \mathfrak{g})^* \to \dots$$

with differential defined by (45.1), where  $\mathfrak{g} = \text{Lie}(G)_{\mathbb{C}}$ .

This purely algebraic complex can be defined for any Lie algebra  $\mathfrak{g}$  over any field (the equality  $d^2 = 0$  follows from the Jacobi identity).<sup>29</sup> It is called the **standard complex** or the **Chevalley-Eilenberg complex** of  $\mathfrak{g}$ , denoted  $CE^{\bullet}(\mathfrak{g})$ , and its cohomology is called the **Lie algebra cohomology** of  $\mathfrak{g}$ , denoted  $H^{\bullet}(\mathfrak{g})$ .<sup>30</sup>

Also note that the complex  $CE^{\bullet}(\mathfrak{g})$  has wedge product multiplication, which descends to the cohomology. Thus  $H^{\bullet}(\mathfrak{g})$  is a graded-commutative associative algebra. Furthermore, if  $\mathfrak{g}=\mathrm{Lie}(G)_{\mathbb{C}}$  for a compact connected Lie group G then  $H^{\bullet}(\mathfrak{g})\cong H^{\bullet}(G,\mathbb{C})$  as a graded algebra. However, this may fail even at the level of vector spaces (i.e., Betti numbers) if G is not compact.

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 275: Theorem 45.12
**Theorem 45.12.** If G is a connected compact Lie group with  $\text{Lie}(G)_{\mathbb{C}} = \mathfrak{g}$  then  $H^{\bullet}(G,\mathbb{C}) \cong (\wedge^{\bullet}\mathfrak{g}^*)^{\mathfrak{g}}$  as a ring.

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 276: Proposition 45.13
**Proposition 45.13.** If G is a connected Lie group,  $\Gamma \subset G$  a finite subgroup, and  $\pi : G \to G/\Gamma$  is the canonical map then  $\pi^*$  defines an isomorphism  $H^{\bullet}(G/\Gamma, \mathbb{C}) \to H^{\bullet}(G, \mathbb{C})$ .

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 277: Theorem 46.4
**Theorem 46.4.** Let G be a simple compact Lie group with complexified Lie algebra  $\mathfrak{g}$ . Then the numbers  $m_i$  are the exponents of  $\mathfrak{g}$  defined in Subsection 32.3. In other words, the degrees  $2m_i + 1$  of generators of the cohomology ring are the dimensions of simple modules occurring in the decomposition of  $\mathfrak{g}$  over its principal  $\mathfrak{sl}_2$ -subalgebra. Thus the cohomology ring  $H^{\bullet}(G,\mathbb{C})$  is the exterior algebra  $\wedge^{\bullet}(\xi_{2m_1+1},...,\xi_{2m_r+1})$ , where  $\xi_j$  has degree j.

A modern general proof of this theorem can be found in [R].

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 278: Corollary 46.6
**Corollary 46.6.** For  $\mathfrak{g} = \mathfrak{sl}_n$  we have  $m_i = i$ . Equivalently, the same is true for  $\mathfrak{g} = \mathfrak{gl}_n$  if we add  $m_0 = 0$ .

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 279: Proposition 46.8
**Proposition 46.8.**  $CE^{\bullet}(\mathfrak{g},\mathfrak{k})$  is a subcomplex of  $CE^{\bullet}(\mathfrak{g})$ .

 $<sup>^{32}</sup>$ A similar idea can be used to find the cohomology of Spin(n) (see Exercise 46.13 below) but it is a bit more complicated since there is no cell decomposition with zero boundary map, and thus any cell decomposition has strictly more than  $2^r$  cells for sufficiently large n (as there is 2-torsion in the integral cohomology).

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 280: Corollary 46.11
Corollary 46.11.  $H^{\bullet}(G/K, \mathbb{C}) \cong H^{\bullet}(\mathfrak{g}, \mathfrak{k})^{K/K^{\circ}}$  as algebras.

Thus, the computation of the cohomology of G/K reduces to the computation of the relative Lie algebra cohomology, which is again a purely algebraic problem.

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 281: Corollary 46.12
Corollary 46.12. Suppose  $z \in K$  is an element that acts by -1 on  $\mathfrak{g}/\mathfrak{k}$ . Then  $(\wedge^i(\mathfrak{g}/\mathfrak{k})^*)^K = 0$  for odd i. Hence the differential in  $CE^{\bullet}(\mathfrak{g},K)$  vanishes and thus  $H^{\bullet}(G/K,\mathbb{C}) \cong (\wedge^{\bullet}(\mathfrak{g}/\mathfrak{k})^*)^K$ , with cohomology present only in even degrees.

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 282: Proposition 47.6
**Proposition 47.6.** If X is a connected cell complex which only has even-dimensional cells, then the cohomology of X vanishes in odd degrees, and the groups  $H^{2i}(X,\mathbb{Z})$  are free abelian groups of ranks  $b_{2i}(X)$ , where the Betti number  $b_{2i}(X)$  is just the number of cells in X of dimension i. Moreover, X is simply connected.

Indeed, the boundary map in this cell complex has to be zero, and its fundamental group must be trivial, as it is a quotient of the fundamental group of the 1-skeleton of X, which is a single point (why?).

So we obtain an even stronger statement than before:

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 283: Corollary 47.7
**Corollary 47.7.**  $H^{2i}(G_{m+n,n}(\mathbb{C}),\mathbb{Z})$  are free abelian groups of ranks given by coefficients of  $\binom{m+n}{m}_q$ , and the odd cohomology groups are zero. Moreover, Grassmannians are simply connected.

In particular, this gives Betti numbers over any field (including positive characteristric), not just  $\mathbb{C}$ .

47.3. Flag manifolds. The flag manifold  $\mathcal{F}_n(\mathbb{C})$  is the space of all complete flags  $0 = V_0 \subset V_1 \subset ... \subset V_n = \mathbb{C}^n$ , where dim  $V_i = i$ . Note that the flag manifold is a homogeneous space:  $\mathcal{F}_n = G/T$ , where G = U(n) and  $T = U(1)^n$  is a maximal torus in G. It can also be written as  $G_{\mathbb{C}}/B$ , where  $G_{\mathbb{C}} = GL_n(\mathbb{C})$  and  $B = B_n$  is the subgroup of upper triangular matrices.

We have fibrations  $\pi: \mathcal{F}_n(\mathbb{C}) \to \mathbb{CP}^{n-1}$  sending  $(V_1, ..., V_{n-1})$  to  $V_{n-1}$ , whose fiber is the space of flags in  $V_{n-1}$ , i.e.,  $\mathcal{F}_{n-1}(\mathbb{C})$ . This shows, by induction, that flag manifolds can be decomposed into even-dimensional cells isomorphic to  $\mathbb{C}^k$ .

More precisely, to define actual cells, we need to trivialize the fibration  $\pi$  over each cell in  $\mathbb{CP}^{n-1}$ . These cells are  $C_{in}$ , i=1,...,n, where  $C_{in}$  is the set of hyperplanes  $E \subset \mathbb{C}^n$  defined by an equation  $a_1x_1 + ... + a_nx_n = 0$  where the first nonzero coefficient is  $a_i$  (so  $C_{in} \cong \mathbb{C}^{n-i}$ ). This means that for  $(x_1,...,x_n) \in E$ , the coordinates

 $x_j, j \neq i$  can be chosen arbitrarily, and then  $x_i$  is uniquely determined. So we may identify E with  $\mathbb{C}^{n-1}$  by sending  $(x_1, ..., x_n)$  to  $(x_1, ..., x_{i-1}, x_{i+1}, ..., x_n)$ , which defines the required trivialization.

Thus we obtain a stratification of  $\mathcal{F}_n$  into cells  $C_w$  labeled by permutations  $w \in S_n$ , which we'll represent as orderings of 1, 2, ..., n. Namely, this stratification and labeling are defined by induction in n: for  $w \in S_{n-1}$ ,  $C_w \times C_{in} = C_{w'_i}$ , where  $w'_i \in S_n$  is obtained from w by inserting n in the i-th place (namely,  $w'_i = w \circ (i, i+1, ..., n)$ ). By analogy with the Grassmannian, the cells  $C_w$  are called **Schubert cells**.

It follows that the Betti numbers of  $\mathcal{F}_n$  vanish in odd degrees, and in even degrees are given by the generating function

$$\sum_{i} b_{2i}(\mathcal{F}_n)q^n = [n]_q! = (1+q)(1+q+q^2)...(1+q+...+q^{n-1}).$$

Moreover, it is easy to see that  $\dim_{\mathbb{C}} C_w = \ell(w)$ , so we get the identity

$$\sum_{w \in S_n} q^{\ell(w)} = [n]_q!$$

Finally, note that the group  $B_n$  of upper triangular matrices preserves each  $C_w$ . In fact, it is easy to check by induction in n that  $C_w$  are simply  $B_n$ -orbits on  $\mathcal{F}_n$ .

Assessment: non-included
This statement concerns the topology/cohomology of Lie groups and homogeneous spaces (de Rham cohomology, Chevalley-Eilenberg complex, Schubert cells). Not formalized in mathlib v4.27.0.

## Statement 284: Proposition 48.1
**Proposition 48.1.** (i) If G is compact and V is a nontrivial irreducible representation then

$$H^i(\mathfrak{g}, V) = 0, i > 0.$$

In particular, this is so for any non-trivial irreducible finite dimensional reporesentation V of a semisimple Lie algebra  $\mathfrak{g}$ .

(ii) (Whitehead's theorem) For semisimple  $\mathfrak{g}$  and any finite dimensional V we have  $H^1(\mathfrak{g},V)=H^2(\mathfrak{g},V)=0.^{34}$

However, this cohomology is non-trivial in general if  $\mathfrak g$  is not semisimple or V is infinite dimensional.

Let us explore the meaning of  $H^i(\mathfrak{g}, V)$  for small i.

- 1. We have  $H^0(\mathfrak{g}, V) = V^{\mathfrak{g}}$ , the  $\mathfrak{g}$ -invariants in V.
- **2.**  $H^1(\mathfrak{g}, V)$  is the quotient of the space  $Z^1(\mathfrak{g}, V)$  of 1-cocycles  $\omega : \mathfrak{g} \to V$ , i.e., linear maps satisfying

$$\omega([x,y]) = x\omega(y) - y\omega(x)$$

 $<sup>^{34}</sup>$ Note that  $H^1(\mathfrak{g}, V)$  appeared earlier in Section 18 and Whitehead's theorem in the case of  $H^1$  was proved in Subsection 18.2.

by the space of 1-coboundaries  $B^1(\mathfrak{g}, V)$ , of the form  $\omega(x) = xv$  for some  $v \in V$ .

Assessment: non-included
This statement from Section 48 concerns Lie algebra cohomology (H^1, H^2 interpretations, deformations, Levi decomposition). Not formalized in mathlib v4.27.0. While the Chevalley-Eilenberg complex is related to `Mathlib/Algebra/Lie/Cochain.lean`, the cohomology theory is not developed.

## Statement 285: Proposition 48.2
**Proposition 48.2.** (i) If V, W are representations of  $\mathfrak{g}$  then  $\operatorname{Ext}^1(V, W) = H^1(\mathfrak{g}, \operatorname{Hom}_{\mathbf{k}}(V, W))$ .

(ii) Consider the action of the additive group of V on the Lie algebra  $\mathfrak{g} \ltimes V$  (with trivial commutator on V) by

$$v \circ (x, w) = (x, w + xv).$$

Then  $H^1(\mathfrak{g}, V)$  classifies Lie algebra homomorphisms  $\mathfrak{g} \to \mathfrak{g} \ltimes V$  of the form  $x \mapsto (x, \omega(x))$  modulo this action.

Assessment: non-included
This statement from Section 48 concerns Lie algebra cohomology (H^1, H^2 interpretations, deformations, Levi decomposition). Not formalized in mathlib v4.27.0. While the Chevalley-Eilenberg complex is related to `Mathlib/Algebra/Lie/Cochain.lean`, the cohomology theory is not developed.

## Statement 286: Proposition 48.3
**Proposition 48.3.** Abelian extensions of  $\mathfrak{g}$  by V modulo isomorphisms which act trivially on V and  $\mathfrak{g}$  are classified by  $H^2(\mathfrak{g}, V)$ . For example, the space  $H^2(\mathfrak{g}, \mathbb{C})$  classifies 1-dimensional central extensions of  $\mathfrak{g}$ :

$$0 \to \mathbb{C} \to \widetilde{\mathfrak{g}} \to \mathfrak{g} \to 0.$$

Assessment: non-included
This statement from Section 48 concerns Lie algebra cohomology (H^1, H^2 interpretations, deformations, Levi decomposition). Not formalized in mathlib v4.27.0. While the Chevalley-Eilenberg complex is related to `Mathlib/Algebra/Lie/Cochain.lean`, the cohomology theory is not developed.

## Statement 287: Proposition 48.5
**Proposition 48.5.** First-order deformations of  $\mathfrak{g}$  as a Lie algebra are classified by  $H^2(\mathfrak{g}, \mathfrak{g})$ .

Thus if  $H^2(\mathfrak{g},\mathfrak{g}) = 0$ , every deformation is isomorphic to the trivial one, with  $c_1 = c_2 = \dots = 0$ . Indeed, applying automorphisms

 $a = 1 + ta_1 + t^2a_2 + ...$ , we can kill successively  $c_1$ , then  $c_2$ , then  $c_3$ , and so on. Thus from Whitehead's theorem we obtain

Assessment: non-included
This statement from Section 48 concerns Lie algebra cohomology (H^1, H^2 interpretations, deformations, Levi decomposition). Not formalized in mathlib v4.27.0. While the Chevalley-Eilenberg complex is related to `Mathlib/Algebra/Lie/Cochain.lean`, the cohomology theory is not developed.

## Statement 288: Corollary 48.6
Corollary 48.6. If  $\mathfrak{g}$  is semisimple then it is rigid, i.e., has no non-trivial Lie algebra deformations.

Assessment: non-included
This statement from Section 48 concerns Lie algebra cohomology (H^1, H^2 interpretations, deformations, Levi decomposition). Not formalized in mathlib v4.27.0. While the Chevalley-Eilenberg complex is related to `Mathlib/Algebra/Lie/Cochain.lean`, the cohomology theory is not developed.

## Statement 289: Theorem 48.9
**Theorem 48.9.** (Levi decomposition, Theorem 16.7) Over real or complex numbers we have  $\mathfrak{g} \cong \operatorname{rad}(\mathfrak{g}) \oplus \mathfrak{g}_{ss}$ , where  $\mathfrak{g}_{ss} \subset \mathfrak{g}$  is a semisimple subalgebra (but not necessarily an ideal); i.e.,  $\mathfrak{g}$  is isomorphic to the semidirect product  $\mathfrak{g}_{ss} \ltimes \operatorname{rad}(\mathfrak{g})$ . In other words, the projection  $p: \mathfrak{g} \to \mathfrak{g}_{ss}$  admits an (in general, non-unique) splitting  $q: \mathfrak{g}_{ss} \to \mathfrak{g}$ , i.e., a Lie algebra map such that  $p \circ q = \operatorname{Id}$ .

Assessment: non-included
This statement from Section 48 concerns Lie algebra cohomology (H^1, H^2 interpretations, deformations, Levi decomposition). Not formalized in mathlib v4.27.0. While the Chevalley-Eilenberg complex is related to `Mathlib/Algebra/Lie/Cochain.lean`, the cohomology theory is not developed.

## Statement 290: Theorem 49.1
**Theorem 49.1.** There is a simply connected Lie group G over  $\mathbb{K}$  with  $\text{Lie}(G) = \mathfrak{g}$ , diffeomorphic to  $\mathbb{K}^n$ . Moreover, if  $\mathfrak{g}$  is nilpotent then the exponential map  $\exp : \mathfrak{g} \to G$  is a diffeomorphism, and if we use it to identify G with  $\mathfrak{g}$  then the multiplication map  $\mu : \mathfrak{g} \times \mathfrak{g} \to \mathfrak{g}$  is polynomial.

Assessment: non-included
This statement from Section 49 concerns the third fundamental theorem of Lie theory, solvable/nilpotent group structure, and formal groups. Not formalized in mathlib v4.27.0.

## Statement 291: Corollary 49.5
**Corollary 49.5.** (Third fundamental theorem of Lie theory, Theorem 9.13) For any finite dimensional Lie algebra  $\mathfrak{g}$  over  $\mathbb{R}$  or  $\mathbb{C}$  there is a simply connected Lie group G with  $\text{Lie}(G) = \mathfrak{g}$ .

Assessment: non-included
This statement from Section 49 concerns the third fundamental theorem of Lie theory, solvable/nilpotent group structure, and formal groups. Not formalized in mathlib v4.27.0.

## Statement 292: Corollary 49.6
Corollary 49.6. A simply connected complex Lie group G is of the form  $G_{ss} \times A$ , where A is solvable simply connected, hence diffeomorphic to  $\mathbb{C}^n$ , and  $G_{ss}$  is a simply connected semisimple complex Lie group. Thus G has the homotopy type of  $G_{ss}^c$ .

49.2. Formal groups. The third fundamental theorem of Lie theory assigns a simply connected Lie group G to any finite dimensional Lie algebra  $\mathfrak{g}$  over  $\mathbb{R}$  or  $\mathbb{C}$ , such that Lie $G = \mathfrak{g}$ . But what about infinite dimensional Lie algebras? There are some examples when this is possible, for instance for  $\mathfrak{g} = \operatorname{Vect}(M)$ , the Lie algebra of vector fields for a smooth manifold M, we can take G to be the universal cover of

<sup>&</sup>lt;sup>36</sup>The reason for this terminology is that these groups act by unipotent operators on the adjoint representation.

 $\operatorname{Diff}_0(M)$ , the group of diffeomorphisms of M homotopic to the identity, and for  $\mathfrak{g}=C^\infty(S^1,\mathfrak{k})$  for a finite dimensional Lie algebra  $\mathfrak{k}$  we can take  $G=C^\infty(S^1,K)$ , where K is the simply connected Lie group corresponding to  $\mathfrak{k}$  (although we would need to explain in what sense G is a Lie group and  $\operatorname{Lie} G=\mathfrak{g}$ ). However, for a general infinite dimensional  $\mathfrak{g}$ , such an assignment is typically impossible and a suitable group G does not exist.

However, this assignment becomes possible (and in fact not just over  $\mathbb{R}$  and  $\mathbb{C}$  but over any field of characteristic zero) if we replace the notion of a Lie group with a purely algebraic notion of a **formal group**. Roughly speaking, the notion of a formal group is the analog of the notion of a real or complex analytic Lie group where analytic functions are replaced by formal power series, and we don't worry about their convergence. This allows us to work with infinite dimensional Lie algebras and over arbitrary fields of characteristic zero.

Let us give a precise definition. Given a vector space V over a field  $\mathbf{k}$  of characteristic zero, define the algebra  $\mathbf{k}[[V]]$  of **formal regular functions** on V to be  $(SV)^*$ , the dual of the symmetric algebra of V. Since SV has a bialgebra structure  $\Delta_0: SV \to SV \otimes SV$  defined by  $\Delta_0(v) = v \otimes 1 + 1 \otimes v$  for  $v \in V$ , the dual map  $\Delta_0^*$  gives a commutative associative product on  $\mathbf{k}[[V]]$ , which is continuous in the weak topology of the dual space. If  $x_i, i \in I$  is a linear coordinate system on V corresponding to a basis  $v_i, i \in I$ , then we have a natural identification  $\mathbf{k}[[V]] \cong \mathbf{k}[[x_i, i \in I]]$  of  $\mathbf{k}[[V]]$  with the algebra of formal power series in  $x_i$ . Note that here I can be a set of any cardinality, not necessarily finite or countable. Moreover, if dim  $V < \infty$  then  $\mathbf{k}[[V]] = \prod_{n \geq 0} S^n V^*$ .

Finally, note that we have the augmentation homomorphism (counit)  $\varepsilon : \mathbf{k}[[V]] \to \mathbf{k}$  given by  $\varepsilon(f) = f(0)$ , i.e., obtained by taking the quotient by the maximal ideal  $\mathbf{m} \subset \mathbf{k}[[V]]$ .

Assessment: non-included
This statement from Section 49 concerns the third fundamental theorem of Lie theory, solvable/nilpotent group structure, and formal groups. Not formalized in mathlib v4.27.0.

## Statement 293: Theorem 49.11
**Theorem 49.11.** (The fundamental theorems of Lie theory for formal groups) These assignments are mutually inverse equivalences between the category of formal groups over  $\mathbf{k}$  and the category of Lie algebras over  $\mathbf{k}$ .

Assessment: non-included
This statement from Section 49 concerns the third fundamental theorem of Lie theory, solvable/nilpotent group structure, and formal groups. Not formalized in mathlib v4.27.0.

## Statement 294: Corollary 49.12
**Corollary 49.12.** Every 1-dimensional formal group G over a field of characteristic zero is isomorphic to the additive formal group, with  $\Delta(f)(x,y) = f(x+y)$ .

Over a field of positive characteristic (or over a commutative ring, such as  $\mathbb{Z}$ ), much, but not all, of this story extends; let us for simplicity consider the finite dimensional case over a field. Namely, the definition of a formal group structure (say, on a finite dimensional space) is the same: it's a coproduct on  $\mathbf{k}[[x_1,...,x_n]]$  with the same properties as above. The definition of the Lie algebra of a formal group also goes along for the ride. However, the reverse assignment fails, since the series  $\mu(x,y)$  is only defined over  $\mathbb{Q}$  and has all primes occurring in denominators of its coefficients. As a result, not any Lie algebra gives rise to a formal group, and the fundamental theorems of Lie theory for formal groups don't hold.

In particular, there are many non-isomorphic 1-dimensional formal groups. For example, we have the additive group law F(x,y) = x+y as above, but also the **multiplicative group law** F(x,y) = x+y+xy, which is called so because this means that 1+F(x,y)=(1+x)(1+y). In characteristic zero these are isomorphic by the map

$$x \mapsto e^x - 1 = \sum_{n \ge 1} \frac{x^n}{n!},$$

(not surprisingly in view of Corollary 49.12), but in positive characteristic this series does not make sense and in fact the additive and multiplicative formal groups are not isomorphic (check it!). There are also many other 1-dimensional formal group laws, commutative and not. Such (commutative) formal group laws are very important in algebraic topology, since they parametrize (complex-oriented) cohomology theories. For example, the additive group law corresponds to ordinary cohomology and the multiplicative one to K-theory. In characteristic zero the isomorphism between the additive and multiplicative formal groups leads to the **Chern character map** which identifies cohomology and K-theory of a topological space with  $\mathbb{Q}$ -coefficients.

<sup>&</sup>lt;sup>41</sup>More precisely, instead of SV we should take the **symmetric algebra with divided powers**  $\Gamma V$ , defined by  $\Gamma^m V := (S^m V^*)^*$ . Note that in characteristic p,  $\Gamma^m V$  is not naturally isomorphic to  $S^m V$  for  $m \geq p$ .

Assessment: non-included
This statement from Section 49 concerns the third fundamental theorem of Lie theory, solvable/nilpotent group structure, and formal groups. Not formalized in mathlib v4.27.0.

## Statement 295: Proposition 50.1
**Proposition 50.1.** If  $d : \mathfrak{a} \to \mathfrak{a}$  is a derivation then  $d(\mathfrak{a}) \subset \mathfrak{n}$ . Thus if  $\mathfrak{a} = \operatorname{rad}(\mathfrak{g})$  is the radical of  $\mathfrak{g}$  then  $\mathfrak{g}$  acts trivially on  $\mathfrak{a}/\mathfrak{n}$ .

Assessment: non-included
This statement from Section 50 concerns Ado's theorem and faithful representations of Lie algebras. Not formalized in mathlib v4.27.0. Searched for Ado, faithful representation, and algebraic Lie algebra in mathlib.

## Statement 296: Proposition 50.3
**Proposition 50.3.** Any finite dimensional complex Lie algebra is a Lie subalgebra of an algebraic one.

Assessment: non-included
This statement from Section 50 concerns Ado's theorem and faithful representations of Lie algebras. Not formalized in mathlib v4.27.0. Searched for Ado, faithful representation, and algebraic Lie algebra in mathlib.

## Statement 297: Proposition 50.5
**Proposition 50.5.** Let  $\mathcal{O}(N)$  be the space of polynomial functions on  $N \cong \mathfrak{n}$  (identified using the exponential map). Then  $\mathcal{O}(N)$  is invariant under the action of  $\mathfrak{n}$  by left-invariant vector fields. Moreover, we have

a canonical filtration  $\mathcal{O}(N) = \bigcup_{n \geq 1} V_n$ , where  $V_n \subset \mathcal{O}(N)$  are finite dimensional subspaces such that  $V_1 \subset V_2 \subset ...$  and  $\mathfrak{n}V_n \subset V_{n-1}$ .

Assessment: non-included
This statement from Section 50 concerns Ado's theorem and faithful representations of Lie algebras. Not formalized in mathlib v4.27.0. Searched for Ado, faithful representation, and algebraic Lie algebra in mathlib.

## Statement 298: Corollary 50.7
Corollary 50.7. Every finite dimensional nilpotent Lie algebra  $\mathfrak n$  over  $\mathbb C$  has a faithful finite dimensional representation where all its elements act by nilpotent operators. Thus  $\mathfrak n$  is isomorphic to a subalgebra of the Lie algebra of strictly upper triangular matrices of some size.

Assessment: non-included
This statement from Section 50 concerns Ado's theorem and faithful representations of Lie algebras. Not formalized in mathlib v4.27.0. Searched for Ado, faithful representation, and algebraic Lie algebra in mathlib.

## Statement 299: Theorem 50.8
**Theorem 50.8.** (Ado's theorem) Every finite dimensional Lie algebra over  $\mathbb{C}$  has a finite dimensional faithful representation.

Assessment: non-included
This statement from Section 50 concerns Ado's theorem and faithful representations of Lie algebras. Not formalized in mathlib v4.27.0. Searched for Ado, faithful representation, and algebraic Lie algebra in mathlib.

## Statement 300: Lemma 51.2
**Lemma 51.2.**  $B_+$  is its own normalizer in G.

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 301: Proposition 51.3
**Proposition 51.3.** We have  $G/B_+ = G^c/H^c$ . In particular,  $G/B_+$  is a compact complex manifold of dimension  $|R_+| = \frac{1}{2}(\dim \mathfrak{g} - \operatorname{rank}\mathfrak{g})$ .

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 302: Corollary 51.5
Corollary 51.5. (The Iwasawa decomposition of G) The multiplication map  $K \times A \times N \to G$  is a diffeomorphism. In particular, we have G = KAN.

A similar theorem holds for *real* reductive groups (Theorem 51.14).

51.3. The Borel fixed point theorem. Let V be a finite dimensional representation of a finite dimensional  $\mathbb{C}$ -Lie algebra  $\mathfrak{a}$ , and  $X \subset \mathbb{P}V$  be a subset. We will say that X is  $\mathfrak{a}$ -invariant (or fixed by  $\mathfrak{a}$ ) if it is  $\exp(\mathfrak{a})$ -invariant.

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 303: Theorem 51.6
**Theorem 51.6.** Let  $\mathfrak{a}$  be a solvable Lie algebra over  $\mathbb{C}$ , V a finite dimensional  $\mathfrak{a}$ -module. Let  $X \subset \mathbb{P}V$  be a closed  $\mathfrak{a}$ -invariant subset. Then there exists  $x \in X$  fixed by  $\mathfrak{a}$ .

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 304: Proposition 51.9
**Proposition 51.9.** Any solvable Lie subalgebra of  $\mathfrak{g}$  (respectively, connected solvable subgroup of G) is contained in a Borel subalgebra (subgroup).

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 305: Corollary 51.10
**Corollary 51.10.** Any element of  $\mathfrak{g}$  is contained in a Borel subalgebra  $\mathfrak{b} \subset \mathfrak{g}$ .

Let us say that a Lie subalgebra  $\mathfrak{a} \subset \mathfrak{g}$  is a nilpotent subalgebra if it consists of nilpotent elements. Note that this is a stronger condition than just being nilpotent as a Lie algebra; for example, a Cartan subalgebra is a nilpotent Lie algebra (since it is abelian) but it is not a nilpotent subalgebra of  $\mathfrak{g}$ .

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 306: Corollary 51.11
Corollary 51.11. Any nilpotent subalgebra of  $\mathfrak g$  is conjugate to a Lie subalgebra of  $\mathfrak n_+$ . Thus  $\mathfrak n_+$  is a maximal nilpotent subalgebra of  $\mathfrak g$ , and any maximal nilpotent subalgebra of  $\mathfrak g$  is conjugate to  $\mathfrak n_+$ .

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 307: Corollary 51.12
Corollary 51.12. Any unipotent subgroup of G is conjugate to a (closed) Lie subgroup of  $N_+$ . Thus  $N_+$  is a maximal unipotent subgroup of G, and any maximal unipotent subgroup of G is conjugate to  $N_+$ .

We also have

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 308: Proposition 51.13
**Proposition 51.13.** The normalizer of  $\mathfrak{n}_+$  and  $N_+$  in G is  $B_+$ . Thus every maximal nilpotent subalgebra (unipotent subgroup) is contained in a unique Borel subgroup. Hence such subalgebras (subgroups) are parametrized by the flag manifold  $G/B_+$ .

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 309: Theorem 51.14
**Theorem 51.14.** (Iwasawa decomposition) The multiplication map  $K^c \times A \times N_{a+} \to G_\theta$  is a diffeomorphism.

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 310: Proposition 51.16
**Proposition 51.16.** The double cosets BwB,  $w \in W$  are disjoint.

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 311: Theorem 51.17
**Theorem 51.17.** (Bruhat decomposition) The union of the double cosets BwB,  $w \in W$  is the entire group G. Thus they define a partition of G into double cosets of B.

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 312: Theorem 51.18
**Theorem 51.18.** (Schubert decomposition)  $C_w, w \in W$  give the partition of G/B into B-orbits.

The sets BwB are called **Bruhat cells** and the sets  $C_w$  are called **Schubert cells**.<sup>43</sup>

Note that for type  $A_{n-1}$  ( $G = SL_n(\mathbb{C})$  or its quotient), we have already proved Theorem 51.18 in Subsection 47.3, where we decomposed the flag manifold  $\mathcal{F}_n$  into Schubert cells labeled by permutations.

A proof of Theorem 51.18 can be found, for example, in the textbook [CG]. It is also sketched in the following exercise.

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 313: Corollary 51.20
**Corollary 51.20.** (i) Any pair of Borel subgroups of G is conjugate to the pair (B, w(B)) for a unique  $w \in W$ . In particular, any two Borel subgroups of G share a maximal torus.

(ii) The cell  $C_w$  is isomorphic to  $\mathbb{C}^{\ell(w)}$ .

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

## Statement 314: Corollary 51.21
Corollary 51.21. The Poincaré polynomial of the flag manifold G/B is

$$\sum_{i>0} b_{2i}(G/B)q^{i} = \sum_{w \in W} q^{\ell(w)}.$$

Assessment: non-included
This statement from Section 51 concerns Borel subgroups, flag manifolds, Iwasawa decomposition, Bruhat decomposition, and Schubert cells. Not formalized in mathlib v4.27.0.

