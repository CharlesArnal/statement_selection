# GRASSMANNIANS: THE FIRST EXAMPLE OF A MODULI SPACE

## 1. What is this course about?

Many objects of algebraic geometry, such as subspaces of a linear space, smooth curves of genus g, or stable vector bundles on a curve, themselves vary in algebraically defined families. Moduli theory studies such families of algebraic objects.

Roughly speaking a *moduli problem* is the problem of understanding a given geometrically meaningful functor from the category of schemes to sets. To make this more concrete consider the following three functors.

**Example 1.1** (Example 1: The Grassmannian Functor.). Let S be a scheme, E a vector bundle on S and k a positive integer less than the rank of E. Let

$$Gr(k, S, E) : \{Schemes/S\} \rightarrow \{sets\}$$

be the contravariant functor that associates to an S-scheme X subvector bundles of rank k of  $X \times_S E$ .

**Example 1.2** (Example 2: The Hilbert Functor.). Let  $X \to S$  be a projective scheme,  $\mathcal{O}(1)$  a relatively ample line bundle and P a fixed polynomial. Let

$$Hilb_P(X/S): \{Schemes/S\} \rightarrow \{sets\}$$

be the contravariant functor that associates to an S scheme Y the subschemes of  $X \times_S Y$  which are proper and flat over Y and have the Hilbert polynomial P.

Example 1.3 (Example 3: Moduli of stable curves.). Let

$$\overline{\mathcal{M}}_g: \{\text{Schemes}\} \to \{\text{sets}\}$$

be the functor that assigns to a scheme Z the set of families (up to isomorphism)  $X \to Z$  flat over Z whose fibers are stable curves of genus g.

Each of the functors in the three examples above poses a moduli problem. The first step in the solution of such a problem is to construct a smooth, projective variety/proper scheme/ proper Deligne-Mumford stack that represents the functor finely/coarsely.

**Definition 1.4.** Given a contravariant functor F from schemes over S to sets, we say that a scheme X(F) over S and an element  $U(F) \in F(X(F))$  represents the functor finely if for every S scheme Y the map

$$\operatorname{Hom}_S(Y, X(F)) \to F(Y)$$

given by  $g \to g^*U(F)$  is an isomorphism.

The best answer one can usually hope for (such as in Examples 1 and 2) is that there is a scheme (hopefully proper) representing the functor. There may not be such a scheme. For instance for the functor in Example 3 there does not exist a fine moduli scheme representing the functor. In such cases we represent the functor either in a different category or we relax the conditions that we impose on the representing scheme. The most common alternatives are to work with stacks or to ask for the moduli space to only coarsely represent the functor.

**Definition 1.5.** Given a contravariant functor F from schemes over S to sets, we say that a scheme X(F) over S coarsely represents the functor F if there is a natural transformation of functors  $\Phi: F \to \operatorname{Hom}_S(*, X(F))$  such that

- (1)  $\Phi(spec(k)) : F(spec(k)) \to \operatorname{Hom}_S(spec(k), X(F))$  is a bijection for every algebraically closed field k,
- (2) For any S-scheme Y and any natural transformation  $\Psi: F \to \operatorname{Hom}_S(*, Y)$ , there is a unique natural transformation

$$\Pi: \operatorname{Hom}_S(*, X(F)) \to \operatorname{Hom}_S(*, Y)$$

such that  $\Psi = \Pi \circ \Phi$ .

Finding a representing scheme/stack, a moduli space, is only the first step of a moduli problem. Usually the motivation for constructing a moduli space is to understand the objects this space parameterizes. This in turn requires a good knowledge of the geometry of the moduli space. Among the questions that arise about these moduli spaces are:

- (1) Is the moduli space proper? If not, does it have a modular compactification? Is the moduli space projective?
- (2) What is the dimension of the moduli space? Is it connected? Is it irreducible? What are its singularities?
- (3) What is the cohomology/Chow ring of the moduli space?
- (4) What is the Picard group of the moduli space? Assuming the moduli space is projective, which of the divisors are ample? Which of the divisors are effective?
- (5) Can the moduli space be rationally parameterized? What is the Kodaira dimension of the moduli space?

The second step of the moduli problem is answering as many of these questions as possible. The focus of this course will be the second step of the moduli problem. In this course we will not concentrate on the constructions of the moduli spaces. We will often stop at outlining the main steps of the constructions only in so far as they help us understand the geometry. We will spend most of the time talking about the explicit geometry of these moduli spaces.

We begin our study with the Grassmannian. The Grassmannian is the scheme that represents the functor in Example 1. Grassmannians lie at the heart of moduli theory. Their existence is the first step for the proof of the existence of the Hilbert scheme. Many moduli spaces in turn can be constructed using the Hilbert scheme. On the other hand, the Grassmannians are sufficiently simple that their geometry is well-understood. Many of the constructions for understanding the geometry of other moduli spaces, such as the moduli space of stable curves, imitates the techniques used in the case of Grassmannians. This motivates us to begin our exploration with the Grassmannian.

Additional references: For a more detailed introduction to moduli problems you might want to read [HM] Chapter 1 Section A, [H] Lecture 21, [EH] Section VI and [K] Section I.1.

## 2. Preliminaries about the Grassmannian

Good references for this section (in random order) are [H] Lectures 6 and 16, [GH] I.5 and [Ful2] Chapter 14, [Kl2] and [KL].

Let G(k,n) denote the classical Grassmannian that parameterizes k-dimensional linear subspaces of a fixed n-dimensional vector space V. G(k,n) naturally carries the structure of a smooth, projective variety. It is often convenient to think of G(k,n) as the parameter space of k-1-dimensional projective linear spaces in  $\mathbb{P}^{n-1}$ . When we use this point of view, we will denote the Grassmannian by  $\mathbb{G}(k-1,n-1)$ .

It is easy to give G(k,n) the structure of an abstract variety. In case  $V=\mathbb{C}^n$ , G(k,n) becomes a complex manifold under this structure. Given a k-dimensional subspace  $\Omega$  of V, we can represent it by a  $k\times n$  matrix. Choose a basis for  $\Omega$  and write them as the row vectors of the matrix. GL(k) acts on the left by multiplication. Two  $k\times n$  matrices represent the same linear space if and only if they are related by this action of GL(k). Since the k vectors span  $\Omega$ , in the matrix representation there must exist a non-vanishing  $k\times k$  minor. Suppose we look at those matrices that have a fixed non-vanishing  $k\times k$  minor. We can normalize that this submatrix is the identity matrix. This gives a unique representation for  $\Omega$ . In this representation the remaining entries are free to vary. The space of such matrices is isomorphic to  $\mathbb{A}^{k(n-k)}$ . In case  $V=\mathbb{C}^n$  the transition functions are clearly holomorphic. We thus obtain the structure of a complex manifold of dimension k(n-k) on the Grassmannian G(k,n). The Grassmannian is compact and connected (for example, the unitary group U(n) maps continuously onto G(k,n)).

The cohomology/Chow ring of the Grassmannian can be very explicitly described. Fix a flag

$$F_{\bullet}: 0 = F_0 \subset F_1 \subset \cdots \subset F_n = V$$

in the vector space V. Recall that a flag is a nested sequence of vector subspaces of V where the difference in dimension of two consecutive vector spaces is one. Given a partition  $\lambda$  with k parts satisfying the conditions

$$n-k \ge \lambda_1 \ge \lambda_2 \ge \cdots \ge \lambda_k \ge 0$$
,

we can define a subvariety of the Grassmannian called the Schubert variety  $\Sigma_{\lambda_1,...,\lambda_k}(F_{\bullet})$  of type  $\lambda$  with respect to the flag  $F_{\bullet}$  to be the closure of

$$\Sigma^0_{\lambda_1,...,\lambda_k}(F_\bullet) := \{ [\Omega] \in G(k,n) : \dim(\Omega \cap F_{n-k+i-\lambda_i}) = i \}.$$

This closure is obtained by turning all  $= to \ge in$  the rank conditions.

The homology class of a Schubert variety does not depend on the choice of flag. For each partition satisfying the above properties, we get a homology class. A word of caution: Most Schubert varieties in a Grassmannian are singular.

Fix the standard flag for  $\mathbb{C}^n$  where  $F_i = \langle e_1, \ldots, e_i \rangle$ . Let  $\Omega$  be a k-plane in the open part of the Schubert variety  $\Sigma_{\lambda_1, \ldots, \lambda_k}(F_{\bullet})$  defined with respect to this flag. We can normalize  $\Omega \cap F_{n-k+i-\lambda_i}$  so that  $\langle v_i, e_{n-k+j-\lambda_j} \rangle = 0$  for j < i and  $\langle v_i, e_{n-k+i-\lambda_i} \rangle = 1$ . Thus we get a unique matrix representation for  $\Omega$  and

see that  $\Sigma^0_{\lambda_1,...,\lambda_k}(F_{\bullet}) \cong \mathbb{A}^{k(n-k)-\sum_i \lambda_i}$ . In other words, Schubert varieties give a cell-decomposition of G(k,n) with only even dimensional cells. It follows that the classes of Schubert varieties generates the homology of G(k,n). Applying Poincaré duality we obtain the following fundamental theorem about the cohomology of G(k,n). We will denote the cohomology class that corresponds to the Schubert variety  $\Sigma_{\lambda_1,...,\lambda_k}$  by  $\sigma_{\lambda_1,...,\lambda_k}$ . We often omit the indices that are zero.

**Theorem 2.1.** The Poincaré duals of the classes of Schubert varieties give an additive basis of the cohomology of the Grassmannian.

**Example 2.2.** Let us consider the case  $G(2,4) = \mathbb{G}(1,3)$ . This variety geometrically corresponds to the variety of lines in  $\mathbb{P}^3$ . The Schubert varieties are in this case given by  $\Sigma_1$  in codimension 1,  $\Sigma_{1,1}$  and  $\Sigma_2$  in codimension 2,  $\Sigma_{2,1}$  in codimension 3 and  $\Sigma_{2,2}$  in codimension 4. Of course, all the codimensions are complex codimensions. A flag in  $\mathbb{P}^3$  corresponds to a choice of point q contained in a line l contained in a plane P contained in  $\mathbb{P}^3$ .  $\Sigma_1$  parameterizes lines that intersect l.  $\Sigma_2$  parameterizes lines that contain q.  $\Sigma_{1,1}$  parameterizes lines that are contained in P and contain q.

Since the cohomology of Grassmannians is generated by Schubert cycles, given two Schubert cycles  $\sigma_{\lambda}$  and  $\sigma_{\mu}$ , their product in the cohomology ring can be expressed as a linear combination of Schubert cycles.

$$\sigma_{\lambda} \cdot \sigma_{\mu} = \sum_{\nu} c^{\nu}_{\lambda,\mu} \ \sigma_{\nu}$$

The structure constants  $c_{\lambda,\mu}^{\nu}$  of the cohomology ring with respect to the Schubert basis are known as Littlewood - Richardson coefficients.

**Example 2.2 continued.** Let us work out the Littlewood - Richardson coefficients of  $G(2,4)=\mathbb{G}(1,3)$ . All but one of the calculations are easy. It is simplest to work dually with the intersection of Schubert varieties. Suppose we wanted to calculate  $\Sigma_2 \cap \Sigma_2$ .  $\Sigma_2$  is the class of lines that pass through a point. If we take points, there will be a unique line containing them both. We conclude that  $\Sigma_2 \cap \Sigma_2 = \Sigma_{2,2}$ . Similarly  $\Sigma_{1,1} \cap \Sigma_{1,1} = \Sigma_{2,2}$ , because there is a unique line contained in two distinct planes in  $\mathbb{P}^3$ . On the other hand  $\Sigma_{1,1} \cap \Sigma_2 = 0$  since there will not be a line contained in a plane and passing through a point not contained in the plane.

The hardest class to compute is  $\Sigma_1 \cap \Sigma_1$ . We know that the class is expressible as a linear combination of  $\Sigma_{1,1}$  and  $\Sigma_2$ . We just saw that both these cycles are self-dual. In order to compute the coefficient we can calculate the triple intersection.  $\Sigma_1 \cap \Sigma_1 \cap \Sigma_2$  is the set of lines that meet two lines  $l_1, l_2$  and contain a point q. There is a unique such line given by  $\overline{ql_1} \cap \overline{ql_2}$ . The other coefficient can be similarly computed to see  $\sigma_1^2 = \sigma_{1,1} + \sigma_2$ .

**Exercise 2.3.** Work out the multiplicative structure of the cohomology ring of  $G(2,4) = \mathbb{G}(1,3), G(2,5) = \mathbb{G}(1,4)$  and  $G(3,6) = \mathbb{G}(2,5)$ .

**Exercise 2.4.** Show that the dual of the Schubert cycle  $\sigma_{\lambda_1,...,\lambda_k}$  is the Schubert cycle  $\sigma_{n-k-\lambda_k,...,n-k-\lambda_1}$ . Conclude that the Littlewood - Richardson coefficient  $c_{\lambda,\mu}^{\nu}$  may be computed as the triple product  $\sigma_{\lambda} \cdot \sigma_{\mu} \cdot \sigma_{\nu^*}$ .

The method of undetermined coefficients we just employed is a powerful technique for calculating the classes of subvarieties of the Grassmannian. Let us do an example to show another use of the technique.

**Example 2.5.** How many lines are contained in the intersection of two general quadric hypersurfaces in  $\mathbb{P}^4$ ? In order to work out this problem we can calculate the class of lines contained in a quadric hypersurface in  $\mathbb{P}^4$  and square the class. The dimension of the space of lines on a quadric hypersurface is 3. The classes of dimension 3 in  $\mathbb{G}(1,4)$  are given by  $\sigma_3$  and  $\sigma_{2,1}$ . We can, therefore, write this class as  $a\sigma_3 + b\sigma_{2,1}$ . The coefficient of  $\sigma_3$  is zero because  $\sigma_3$  is self-dual and corresponds to lines that pass through a point. As long as the quadric hypersurface does not contain the point, the intersection will be zero. On the other hand, b=4.  $\Sigma_{2,1}$  parameterizes lines in  $\mathbb{P}^4$  that intersect a  $\mathbb{P}^1$  and are contained in a  $\mathbb{P}^3$  containing the  $\mathbb{P}^1$ . The intersection of the quadric hypersurface with the  $\mathbb{P}^3$  is a quadric surface. The lines have to be contained in this surface and must pass through the two points of intersection of the  $\mathbb{P}^1$  with the quadric surface. There are four such lines. We conclude that there are 16 lines that are contained in the intersection of two general quadric hypersurfaces in  $\mathbb{P}^4$ .

Another way to verify this fact is to observe that such an intersection is a quartic Del Pezzo surface. Such a surface is the blow-up of  $\mathbb{P}^2$  at 5 general points embedded by its anti-canonical linear system. The lines in this embedding correspond to the (-1)-curves on the surface. It is well-known that the number of (-1)-curves on this surface is 16 (see for example [Ha] Chapter 5).

There is one issue that requires some attention. So far we have pretended that all the intersections are transverse. This is indeed the case. We can either explicitly calculate the tangent spaces to check that the intersection is transverse or we can appeal to a general theorem that guarantees the result. Since the theorem is very useful, we reproduce its statement here. However, be warned that the theorem in the form stated holds only in characteristic zero. For a proof see [Kl1] or [Ha] Theorem III.10.8.

**Theorem 2.6.** (Kleiman) Assume we are working over an algebraically closed field of characteristic zero. Let G be an integral algebraic group scheme, X an integral algebraic scheme with a transitive G action. Let  $f: Y \to X$  and  $g: Z \to X$  be two maps of integral algebraic schemes. For each rational element of  $g \in G$ , denote by gY the X-scheme given by  $gY \mapsto gf(g)$ . Then there exists a dense open subset G of such that for every rational element  $g \in G$ , the fiber product  $gY \to G$  is either empty or equidimensional of the expected dimension

$$\dim(Y) + \dim(Z) - \dim(X)$$
.

Furthermore, if Y and Z are regular, for a dense open set this fibered product is regular.

*Proof.* The theorem follows from the following lemma.

**Lemma 2.7.** Suppose all the schemes in the following diagram are integral over an algebraically closed field of characteristic zero.

If q is flat, then there exists a dense open subset of S such that  $p^{-1}(s) \times_X Z$  is empty or equidimensional of dimension

$$\dim(p^{-1}(s)) + \dim(Z) - \dim(X).$$

If in addition, Z is regular and q has regular fibers, then  $p^{-1}(s) \times_X Z$  is regular for a dense open subset of S.

The theorem follows by taking  $S=G, W=G\times Y$  and  $q:G\times Y\to X$  given by q(g,y)=gf(y). The lemma follows by flatness and generic smoothness. More precisely, since q is flat, the fibers of q are equidimensional of dimension  $\dim(W)-\dim(X)$ . By base change the induced map  $W\times_XZ\to Z$  is also flat, hence the fibers have dimension  $\dim(W\times_XZ)-\dim(Z)$ . Consequently,

$$\dim(W \times_X Z) = \dim(W) + \dim(Z) - \dim(X).$$

There is an open subset  $U_1 \subset S$  over which p is flat, so the fibers are either empty or equidimensional with dimension  $\dim(W) - \dim(S)$ . Similarly there is an open subset  $U_2 \subset S$ , where the fibers of  $p \circ pr_W : X \times_X Z \to S$  is either empty or equidimensional of dimension  $\dim(X \times_X Z) - \dim(S)$ . The first part of the lemma follows by taking  $U = U_1 \cap U_2$  and combining these dimension statements. The second statement follows by generic smoothness. This is where we use the assumption that the characteristic is zero.

The Grassmannians G(k, n) are homogeneous under the action of GL(n). Hence Kleiman's Theorem easily implies the transversality of intersections in many cases.

We now give two presentations for the cohomology ring of the Grassmannian. These presentations are useful for theoretical computations. However, we will soon develop Littlewood - Richardson rules, positive combinatorial rules for computing Littlewood - Richardson coefficients, that are much more effective in computing and understanding the structure of the cohomology ring of G(k, n).

One extremely useful way comes from considering the universal exact sequence of bundles on G(k,n). Let T denote the tautological bundle over G(k,n). Recall that the fiber of T over a point  $[\Omega]$  is the vector subspace  $\Omega$  of V. There is a natural inclusion

$$0 \to T \to V \to Q \to 0$$

with quotient bundle Q.

**Theorem 2.8.** As a ring the cohomology ring of G(k,n) is isomorphic to

$$\mathbb{R}[c_1(T),\ldots,c_k(T),c_1(Q),\ldots,c_{n-k}(Q)]/(c(T)c(Q)=1).$$

Moreover, the chern classes of the Quotient bundle generate the cohomology ring.

The chern classes of the tautological bundle and the quotient bundle are easy to see in terms of Schubert cycles. As an exercise prove the following proposition:

**Proposition 2.9.** The chern classes of the tautological bundle are given as follows:

$$c_i(T) = (-1)^i \sigma_{1,\dots,1}$$

where there are i ones. The chern classes of the quotient bundle are given by

$$c_i(Q) = \sigma_i.$$

The Schubert cycles  $\sigma_i$  where all the parts of the partition except for the first are zero are called special Schubert cycles. It is easy to calculate the product of special Schubert cycles. Pieri's rule gives an algorithm for computing these products. In fact, Pieri's rule gives an algorithm for computing the product of any Schubert cycle with a special Schubert cycle.

**Theorem 2.10** (Pieri's formula). Let  $\sigma_{\lambda}$  be a special Schubert cycle. Suppose  $\sigma_{\mu}$  is any Schubert cycle with parts  $\mu_1, \ldots, \mu_k$ . Then

$$\sigma_{\lambda} \cdot \sigma_{\mu} = \sum_{\substack{\mu_{i} \leq \nu_{i} \leq \mu_{i-1} \\ \sum \nu_{i} = \lambda + \sum \mu_{i}}} \sigma_{\nu} \tag{1}$$

The special Schubert cycles generate the cohomology ring of the Grassmannian. In order to prove this we have to express every Schubert cycle  $\sigma_{\lambda_1,...,\lambda_k}$  as a linear combination of products of special Schubert cycles.

Exercise 2.11. Using Pieri's formula prove the following identity

$$(-1)^k \sigma_{\lambda_1,\dots,\lambda_k} = \sum_{j=1}^k (-1)^j \sigma_{\lambda_1,\dots,\lambda_{j-1},\lambda_{j+1}-1,\dots,\lambda_k-1} \cdot \sigma_{\lambda_j+k-j}$$

Using this relation and induction obtain the following formula for the class of any Schubert cycle in terms of special Schubert cycles.

**Theorem 2.12** (Giambelli's formula). Any Schubert cycle may be expressed as a linear combination of products of special Schubert cycles as follows

$$\sigma_{\lambda_1,\dots,\lambda_k} = \begin{vmatrix} \sigma_{\lambda_1} & \sigma_{\lambda_1+1} & \sigma_{\lambda_1+2} & \dots & \sigma_{\lambda_1+k-1} \\ \sigma_{\lambda_2-1} & \sigma_{\lambda_2} & \sigma_{\lambda_2+1} & \dots & \sigma_{\lambda_2+k-2} \\ \vdots & \vdots & \vdots & \vdots \\ \sigma_{\lambda_k-k+1} & \sigma_{\lambda_k-k+2} & \sigma_{\lambda_k-k+3} & \dots & \sigma_{\lambda_k} \end{vmatrix}$$

**Exercise 2.13.** Use Giambelli's formula to express  $\sigma_{3,2,1}$  in G(4,8) in terms of special Schubert cycles. Using Pieri's rule find the class of its square.

Pieri's formula and Giambelli's formula together give an algorithm for computing the cup product of any two Schubert cycles. Unfortunately, in practice this algorithm is hard to implement. We will rectify this problem shortly.

So far we have treated the Grassmannian simply as a complex manifold. For the sake of completeness, we recall how to endow it with the structure of a smooth, projective variety. Using the Plücker coordinates we can embed G(k, V) into  $\mathbb{P}(\bigwedge^k V)$ . Given a k-plane  $\Omega$  we can choose a basis for it  $v_1, \ldots, v_k$ . Then we can define the map  $Pl: G(k, n) \to \mathbb{P}(\bigwedge^k V)$  by sending the k-plane  $\Omega$  to  $v_1 \wedge \cdots \wedge v_k$ . A change of basis changes the image by the determinant of the matrix giving the change of basis. Hence the map is well-defined as a point of  $\mathbb{P}(\bigwedge^k V)$ .

The map is injective since we can recover  $\Omega$  from its image  $p = [v_1 \wedge \cdots \wedge v_k] \in \mathbb{P}(\bigwedge^k V)$  as the set of all vectors  $v \in V$  such that  $v \wedge v_1 \wedge \cdots \wedge v_k = 0$ . A point of  $\mathbb{P}(\bigwedge^k V)$  is in the image of this map if and only if the representative  $\sum p_{i_1,\ldots,i_k}e_1 \wedge \cdots \wedge e_{i_k}$  is completely decomposable. It is not hard to characterize the subvariety of  $\mathbb{P}(\bigwedge^k V)$  corresponding to completely decomposable elements. An

element  $x \in \bigwedge^k V$  is completely decomposable if and only if  $\langle u, x \rangle \wedge x = 0$  for every  $u \in \bigwedge^{k-1} V^*$ . Writing this in coordinates we obtain the Plücker relations

$$\sum_{s=1}^{k+1} (-1)^s p_{i_1,\dots,i_{r-1},j_t} p_{j_1,\dots,\hat{j_t},\dots,j_{r+1}} = 0.$$

These Plücker relations generate the ideal of the Grassmannian.

Everyone's favorite example is G(2,4). In that case there is a unique Plücker relation

$$p_{12}p_{34} - p_{13}p_{24} + p_{14}p_{23} = 0.$$

Hence the Plücker map embeds G(2,4) in  $\mathbb{P}^5$  as a smooth quadric hypersurface.

**Exercise 2.14.** Show that the locus where a Plücker coordinate vanishes corresponds to a Schubert variety  $\Sigma_1$ . Observe that the class of  $\Sigma_1$  generates the second homology of the Grassmannian. In particular, the Picard group is isomorphic to  $\mathbb{Z}$ . Conclude that  $\mathcal{O}_{G(k,n)}(\Sigma_1)$  is the very ample generator of the Picard group and it gives rise to the Plücker embedding.

We can compute the degree of the Grassmannian G(k,n) under the Plücker embedding. The answer is provided by  $\sigma_1^{k(n-k)}$ . When k=2, this computation is relatively easy to carry out. By Pieri's formula  $\sigma_1$  times any cycle in G(2,n) either increases the first index of the cycle or it increases the second index provided that it is less than the first index. This means that the degree of the Grassmannian G(2,n) is the number of ways of walking from one corner of an  $(n-2)\times (n-2)$  to the opposite corner without crossing the diagonal. This is well-known to be the Catalan number

$$\frac{(2(n-2))!}{(n-2)!(n-1)!}.$$

The general formula is more involved. The degree of G(k,n) is given by

$$(k(n-k))! \prod_{i=1}^{k} \frac{(i-1)!}{(n-k+i-1)!}.$$

The local structure of the Grassmannian. The tangent bundle of the Grassmannian has a simple intrinsic description in terms of the tautological bundle T and the quotient bundle Q. There is a natural identification of the tangent bundle of the Grassmannian with homomorphisms from T to Q, in other words

$$TG(k, n) = \text{Hom}(T, Q).$$

In particular, the tangent space to the Grassmannian at a point  $[\Omega]$  is given by  $\operatorname{Hom}(\Omega,V/\Omega)$ . One way to realize this identification is to note that the Grassmannian is a homogeneous space for GL(n). The tangent space at a point may be naturally identified with quotient of the Lie algebra of GL(n) by the Lie algebra of the stabilizer. The Lie algebra of GL(n) is the endomorphisms of V. Those that stabilize  $\Omega$  are those homomorphisms  $\phi: V \to V$  such that  $\phi(\Omega) \subset \Omega$ . These homomorphisms are precisely homomorphisms  $\operatorname{Hom}(\Omega,V/\Omega)$ .

**Exercise 2.15.** Use the above description to obtain a description of the tangent space to the Schubert variety  $\Sigma_{\lambda_1,...,\lambda_k}$  at a smooth point  $[\Omega]$  of the variety.

We can use the description of the tangent space to check that the intersection of Schubert cycles in previous calculations were indeed transverse. For example, suppose we take the intersection of two Schubert varieties  $\Sigma_1$  in  $\mathbb{G}(1,3)$  defined with respect to two skew-lines. Then the intersection is a smooth variety. In vector space notation, we can assume that the conditions are imposed by two non-intersecting two-dimensional vector spaces  $V_1$  and  $V_2$ . Suppose a 2-dimensional vector space  $\Omega$  meets each in dimension 1. The tangent space to  $\Omega$  at the intersection is given by

$$\phi \in \operatorname{Hom}(\Omega, V/\Omega)$$
 such that  $\phi(\Omega \cap V_i) \subset [V_i] \in V/\Omega$ .

As long as  $V_1$  and  $V_2$  do not intersect,  $\Omega$  has exactly a one-dimensional intersection with each of  $V_i$  and these span  $\Omega$ . On the other hand, the quotient of  $V_i$  in  $V/\Omega$  is one-dimensional. We conclude that the dimension of such homomorphisms is 2. Since this is equal to the dimension of the variety, we deduce that the variety is smooth.

Exercise 2.16. Carry out a similar analysis for the other examples we did above.

**Definition 2.17.** Let S be a scheme, E a vector bundle on S and k a natural number less than or equal to the rank of E. The functor

$$Gr(k, E) : \{ schemes over S \} \rightarrow \{ sets \}$$

associates to every S scheme X the set of rank k subvector bundles of  $E \times_S X$ .

**Theorem 2.18.** The functor Gr(k, E) is represented by a scheme  $G_S(k, E)$  and a subvector bundle  $U \subset E \times_S G_S(k, E)$  of rank k.

### 3. A LITTLEWOOD-RICHARDSON RULE

Positive combinatorial rules for determining Littlewood - Richardson coefficients are known as Littlewood - Richardson rules. As an introduction to the degeneration techniques that we will employ through out this course, we give a Littlewood - Richardson rule for the Grassmannian.

There are many Littlewood - Richardson rules for the Grassmannian. You can find other Littlewood - Richardson rules in [Ful1], [V1], [KT]. The rule we will develop here is a geometric Littlewood - Richardson rule. These rules have many applications in geometry. For some examples of applications to positive characteristic, Schubert calculus over  $\mathbb{R}$  and monodromy groups see [V2].

The fundamental example. Consider calculating  $\sigma_1^2$  in G(2,4). Geometrically we would like to calculate the class of two dimensional linear spaces that meet two general two dimensional linear spaces in a four dimensional vector space. Projectivizing this question is equivalent to asking for the class of lines in  $\mathbb{P}^3$  intersecting two general lines.

The idea underlying the approach to answering this question is classical. While it is hard to see the Schubert cycles that constitute this intersection when the two lines that define the two Schubert cycles are general, the result becomes easier if the lines are in special position.

To put the lines  $l_1$  and  $l_2$  in a special position fix a plane containing  $l_1$  and rotate it about a point on it, so that it intersects  $l_2$ . As long as  $l_1$  and  $l_2$  do not intersect, they are in general position since the automorphism group of  $\mathbb{P}^3$  acts transitively

on pairs of skew lines. However, when  $l_1$  and  $l_2$  intersect, then they are no longer in general position.

We can ask the following fundamental question: What is the limiting position of the lines that intersect both  $l_1$  and  $l_2$ ? Since intersecting the lines are closed conditions, any limit line has to continue to intersect  $l_1$  and  $l_2$ . There are two ways that a line can intersect two intersecting lines in  $\mathbb{P}^3$ . Either the line passes through their intersection point, or if it does not pass through its intersection point then it must lie in the plane spanned by the two lines. Note that these are both Schubert cycles. Since their dimensions are equal to the dimension of the original variety, the class of the original variety has to be the sum of multiples of these two Schubert cycles.

We can determine that the multiplicities are one as follows. The tangent space to the Grassmannian G(k,n) at a point  $\Lambda$  is given by It suffices then to check that the two cycles intersect transversely at a general point of each of the Schubert cycles.

A Mondrian tableau associated to a Schubert class  $\sigma_{\lambda_1,\cdots,\lambda_k}$  in G(k,n) is a collection of k nested squares labeled by integers  $1,\ldots,k$  where the j-th box has size  $n-k+j-\lambda_j$  and a box of smaller index is contained in every box of larger index. Figure 1 depicts a Mondrian tableau for  $\sigma_{2,1}$  in G(3,6).

FIGURE 1. The Mondrian tableau associated to  $\sigma_{2,1}$  in G(3,6).

In Mondrian tableaux a box of side length s denotes a vector space of dimension s. If a box  $S_1$  is contained in another box  $S_2$ , then the linear space represented by  $S_1$  is a subspace of the linear space represented by  $S_2$ . The reader should think of unit squares along the anti-diagonal as giving a basis of the underlying vector space. The vector space represented by a box is the span of the basis elements it contains. In a Mondrian tableau associated to  $\sigma_{\lambda}$  the k-plane is required to meet the vector space represented by a box in dimension equal to the number of boxes contained in that box (including itself). We will denote boxes in a Mondrian tableau by capital letters in the math font (e.g.  $A_i$ ) and the vector spaces they represent by the corresponding letter in Roman font (e.g.  $A_i$ ).

We stress that any nested sequence of a boxes that have their centers along the anti-diagonal defines a Schubert cycle. The boxes need not be left or right aligned.

The game. To multiply two Schubert classes  $\sigma_{\lambda}$  and  $\sigma_{\mu}$  in G(k,n) we place the tableau associated to  $\lambda$  starting from the lower left hand corner and the tableau associated to  $\mu$  starting from the upper right hand corner of an  $n \times n$  square. The squares in the  $\lambda$  ( $\mu$ ) tableau are all left (respectively, right) aligned with respect to the  $n \times n$  square. We will denote the boxes corresponding to  $\lambda$  and  $\mu$  by  $A_i$  and  $B_j$ , respectively. The left panel in Figure 2 shows the initial tableau for the multiplication  $\sigma_{2,1,1} \cdot \sigma_{1,1,1}$  in G(3,6).

Figure 2. An application of the OB rule.

Initially the two Schubert cycles are defined with respect to two transverse flags. If the intersection of the two Schubert cycles is non-empty, then the Schubert cycles have to satisfy certain conditions. A preliminary rule (MM rule) guarantees that these conditions are satisfied. Then there are some simplifications that reduce the problem to a smaller problem. The OB and S rules give these simplifications.

• The MM rule. We check that  $A_i$  intersects  $B_{k-i+1}$  in a square of side length at least one for every i between 1 and k. If not, we stop. The Schubert cycles have empty intersection. In other words, the class of the intersection is zero.

In a k-dimensional vector space  $V^k$  every i-dimensional subspace (such as  $V^k \cap A_i$ ) Must Meet every k-i+1-dimensional subspace (such as  $V^k \cap B_{k-i+1}$ ) in at least a line. The intersection of two Schubert cycles is zero if and only if the initial tableau formed by the two cycles does not satisfy the MM rule.

• The OB rule. We call the intersection of  $A_k$  and  $B_k$  the Outer Box of the tableau. We replace every square with its intersection with the outer box.

Since the k-planes are contained in both  $A_k$  and  $B_k$ , they must be contained in their intersection. Figure 2 shows an example in G(3,6).

• The S rule. We check that  $A_i$  and  $B_{a-i}$  touch or have a common square. If not, we remove the rows and columns between these squares as shown in Figure 3.

This rule corresponds to the fact that an a-dimensional vector space lies in the Span of any two of its subspaces of complementary dimension whose only intersection is the origin. This rule removes any basis element of V that is not needed in expressing the a-planes parameterized by the intersection of the two Schubert varieties.

FIGURE 3. Adjusting the span of the linear constraints.

Once we have performed these preliminary steps, we will inductively build a new flag (the D flag) by degenerating the two flags (the A and B flags). At each stage

of the game we will have a partially built new flag (depicted by D boxes that arise as intersections of A and B boxes) and partially remaining A and B flags (depicted by boxes  $A_i, \ldots, A_a$  and  $B_k, B_{k-i}, \ldots, B_1$ ). After nesting the D boxes, we will increase the dimension of the intersection of  $A_i$  with  $B_{k-i}$  by one in order of increasing i. We will depict this move in the Mondrian tableau by sliding  $A_i$  anti-diagonally up by one unit. Assuming that there are no boxes left justified with  $A_i$ , the corresponding degeneration can be described as follows:

Let s be the side-length of  $A_i$  and suppose that initially  $A_i$  and  $B_{a-i}$  intersect in a square of side-length r. There is a family of s-dimensional linear spaces  $A_i(t)$  parameterized by an open subset  $0 \in U \subset \mathbb{P}^1$  such that over the points  $t \in U$  with  $t \neq 0$ , the dimension of intersection  $A_i(t) \cap B_{k-i}$  is equal to r and when t = 0, the dimension of intersection  $A_i(0) \cap B_{a-i}$  is r+1. Denoting the basis vectors represented by the unit squares along the diagonal by  $e_1, \ldots, e_n$ , we explicitly take the family to be

$$A_i(t) = \text{ the span of } \{(te_1 + (1-t)e_{s+1}, e_2, \dots, e_s)\}.$$

When t = 1, we have our original vector space  $A_i$  represented by the old position of the box  $A_i$ . When t = 0, we have the new vector space  $A_i(0)$  represented by the new position of the box  $A_i$ . When t = 0, the intersection of Schubert varieties defined with respect to the A and B flags either remains irreducible or breaks into two irreducible components. The LR rule records these possibilities and can be informally phrased as:

If the a-planes in the limit do not intersect  $A_i(0) \cap B_{k-i}$ , then they must be contained in their new span.

The main work in establishing the rule rests in describing which varieties (equivalently which Mondrian tableaux) occur as a result of the degenerations (equivalently moves). Very generally we can define a Mondrian tableau in G(k, n) to be a collection of k boxes contained in an  $n \times n$  box satisfying the following two properties:

- (1) None of the boxes are equal to the span of the boxes contained in them.
- (2) Let  $S_1$  and  $S_2$  be any two boxes in the tableau. If the number of boxes contained in their span but not contained in  $S_1$  is r, then the side length of  $S_1$  is at least r less than the side length of their span.

We can associate an irreducible subvariety of the Grassmannian G(k, n) to such a tableau. We first define an open subset of the variety by requiring the k-planes to meet the vector spaces represented by each box in dimension equal to the number of boxes contained in that box (including itself). We further require the vector subspaces of the k-planes contained in the vector spaces represented by any two boxes to only meet along the subspaces contained in subspaces contained in boxes common to both of the boxes and otherwise to be independent. The variety associated to the generalized Mondrian tableau is the closure in G(k,n) of the quasi-projective variety parameterizing such k-planes.

The intersection of two Schubert varieties can be turned to such a tableau by replacing the boxes  $A_i$  and  $B_j$  by the boxes consisting of the intersections  $A_i \cap B_{k-i+1}$ . Here we will not discuss the rule that expresses the classes of the varieties defined by these very general tableaux as a sum of Schubert varieties. When we resolve the intersection of Schubert varieties into a union of Schubert varieties, only very few of these varieties occur. During the game the Mondrian tableaux

that occur have more structure. The admissible tableaux characterize the ones that occur.

A Mondrian tableau is *admissible* for G(k, n) if the squares that constitute the tableau (except for the outer box) are uniquely labeled as an indexed A, B or D box such that

- (1) The boxes  $A_k = B_k$  form the outer box. They have side length  $m \leq n$  and contain the entire tableau.
- (2) The A boxes are all nested, distinct, left aligned and strictly contain all the D boxes. If the number of D boxes is i-1 < k, then the A boxes are  $A_i, A_{i+1}, \ldots, A_k$  with the smaller index corresponding to the smaller box. (In particular, the number of A boxes is k-i+1, hence the number of A and D boxes add up to k.)
- (3) The B boxes are all nested, distinct and right aligned. They are labeled  $B_k, B_{k-i}, B_{k-i-1}, \ldots, B_1$ , where a smaller box has the smaller index. (In particular, the number of B boxes equals the number of A boxes.) The A and B boxes satisfy the MM and S rules. The D boxes may intersect  $B_{k-i}$ , but none are contained in  $B_{k-i}$ . The side length of  $B_{k-i}$  is at least i units smaller than the side length of the outer box and at least h units smaller than the side length of the box spanned by the boxes  $D_s$  for  $1 \le s \le h$  and  $B_{k-i}$  for every  $1 \le h \le i-1$ .
- (4) The D boxes are labeled  $D_1, \ldots, D_{i-1}$ . They do not need to be nested; however, there can be at most one unnested D box. An unnested D box is defined to be a D box that does not contain every D box of smaller index. More precisely, if  $D_j$  does not contain all the D boxes of smaller index, then it does not contain any of the D boxes of smaller index; it is contained in every D box of larger index; and  $D_h \subset D_k$  for every h < k as long as h and k are different from j. All the D boxes of index lower than j are to the lower left of  $D_j$ .  $D_{j-1}$  and  $D_j$  share a common square or corner. If there is an unnested D box  $D_j$ , the D or A box with one larger index is at least one larger than the span of the D boxes contained in it. The side length of  $D_j$  is at least i smaller than the side length of the square spanned by  $D_i$  and  $D_j$  for every i < j.

Given an admissible Mondrian tableau there is a corresponding subvariety of G(k, n). The corresponding subvariety is defined as the closure of the locus of k-planes that satisfy certain numerical conditions with respect to the vector spaces represented by the A, B and D boxes. Precisely, the variety associated to an admissible Mondrian tableau is the closure of the locus of k-planes that intersect the vector spaces represented by the boxes  $D_s$ ,  $s = 1, \ldots, i - 1$ ,  $A_t$ ,  $t = i, \ldots, k$ , and  $B_u$ ,  $u = k - i, \ldots, 1$ , in dimension equal to the number of boxes contained in them. This defines an irreducible variety. The strategy is to specialize the flags in order to break such a variety into a union of two varieties that have the same form. The moves on the Mondrian tableaux achieve this purpose.

Let M be an admissible Mondrian tableau with an outer box of side length m. If all the D boxes are nested, we slide the smallest A box  $A_i$  anti-diagonally up by one unit. Any of the D boxes that touch the lower left hand corner of  $A_i$  move one unit up with  $A_i$ . The remaining D boxes do not move. If the side length of  $A_{i+1}$  is not one larger than the side length of  $A_i$  or the side length of  $B_{k-i}$  is not

m-i (informally, if  $A_i$  or  $B_{k-i}$  are not as large as possible given  $A_{i+1}$  and  $B_k$ ), we replace M with the two tableaux described in Possibilities 1 and 2. If the side length of  $A_{i+1}$  is one larger than the side length of  $A_i$  or the side length of  $B_{k-i}$  is m-i, we replace M only with the tableau in Possibility 1.

- Possibility 1. We delete  $A_i$  and  $B_{k-i}$  and replace them with  $D_i$  which is the new intersection of  $A_i$  and  $B_{k-i}$ . If  $D_i$  does not intersect or touch  $B_{k-i-1}$ , we slide all the D boxes anti-diagonally up until  $D_i$  touches  $B_{k-i-1}$ . All the remaining boxes stay as in M.
- Possibility 2. We shrink the outer box by one so that it passes along the new boundary of  $A_i$  and  $B_{k-i}$  and we delete the column and row that lies outside this box. The rest of the boxes stay as in M.

FIGURE 4. Admissible Mondrian tableaux and the moves.

The two tableaux obtained from M are depicted in Figure 4. Geometrically in the first possibility the k-plane intersects the new intersection  $A_i \cap B_{k-i}$ . In the second possibility, the k-plane lies in the new span of  $A_i$  and  $B_{k-i}$ .

Nesting the D boxes. Now suppose that there is an unnested D box  $D_j$ . Assume that the smallest square containing  $D_{j-1}$  and  $D_j$  has side length  $d_j$ . In this case we move  $D_{j-1}$  anti-diagonally up by one unit. Any D boxes contained in  $D_{j-1}$  and left justified with it move one unit up with  $D_{j-1}$ . The remaining boxes stay fixed. If the side length of  $D_j$  is less than  $d_j - j + 1$  or after the move  $D_{j-1}$  does not contain  $D_j$ , we replace the tableau M with the following two tableaux. If the side length of  $D_j$  is  $d_j - j + 1$  or after the move  $D_{j-1}$  contains  $D_j$ , we replace M only with the tableau in Possibility 1.

• Possibility 1. We delete  $D_j$  and  $D_{j-1}$ . We draw the old span and label it  $D_j$ . We also draw the new intersection and label it  $D_{j-1}$ . If  $D_{j-1}$  does not meet

or touch  $B_{a-i}$ , we slide all the D boxes of index at most j-1 anti-diagonally up until it does. We keep the remaining boxes as in M.

• Possibility 2. We place  $D_{j-1}$  in its new position and keep all the remaining boxes as in M.

It is not hard to check that the results of the moves transform an admissible Mondrian tableau to one or two new admissible Mondrian tableaux. Therefore, we can continue applying the moves to each of the resulting tableaux. After a cycle of moves the number of A and B boxes decrease and the number of nested D boxes increases. Eventually all the boxes will be nested again. The corresponding variety is a Schubert variety. If we apply the moves to each of the Mondrian tableaux that occur until all the boxes are nested, we end up with a collection of tableaux corresponding to Schubert varieties.

A dimension calculation shows that applying the degeneration described above to the variety represented by an admissible Mondrian tableau results in the varieties represented by the Mondrian tableaux described in the possibilities. A multiplicity calculation shows that each of the varieties occur with multiplicity one. The following theorem is a consequence of these calculations.

**Theorem 3.1.** The LR coefficient  $c_{\lambda,\mu}^{\nu}$  of G(k,n) equals the number of times  $\sigma_{\nu}$  results in a game of Mondrian tableaux starting with  $\sigma_{\lambda}$  and  $\sigma_{\mu}$  in an  $n \times n$  box.

We conclude the discussion of the geometric Littlewood - Richardson rules for the ordinary Grassmannian with an example. We compute  $\sigma_{2,1}^2$  in G(3,6) (see Figure 5). We start by moving the smallest A box. There are two possibilities. We replace the tableau by the two tableaux where we take the intersection of  $A_1$  and  $B_2$  (and slide it up) and keep everything else the same and where we restrict the tableau to the new span of  $A_1$  and  $B_2$ . We continue resolving the first tableau by moving  $A_2$ . Again there are two possibilities. In the second tableau  $B_2$  is as large as possible given the outer box, so when we move  $A_1$ , there is only one possibility. We then move  $A_2$  and now there are two possibilities. We replace the tableau with the tableau where we take the intersection of  $A_2$  and  $B_1$  and with the tableau where we restrict the tableau to the new span of  $A_2$  and  $B_1$ . Continuing we conclude that

$$\sigma_{2,1}^2 = \sigma_{3,3} + 2\sigma_{3,2,1} + \sigma_{2,2,2}.$$

**Exercise 3.2.** Show that when one takes one of the Schubert cycles to be a special Schubert cycle, one recovers Pieri's rule. Our proof of the Littlewood - Richardson rule used Pieri's rule. Carry out the multiplicity calculations explicitly for that case to reprove Pieri's rule.

**Exercise 3.3.** Formulate and prove a Littlewood - Richardson rule that decomposes the class of any variety described by a generalized Mondrian tableau into a sum of Schubert classes.

Exercise 3.4. Using the rule compute the Littlewood - Richardson coefficients of small Grassmannians.

### References

[EH] David Eisenbud and Joe Harris. The geometry of schemes, volume 197 of Graduate Texts in Mathematics. Springer-Verlag, New York, 2000.

FIGURE 5. The product  $\sigma_{2,1}^2 = \sigma_{3,3} + 2\sigma_{3,2,1} + \sigma_{2,2,2}$  in G(3,6).

- [Ful1] W. Fulton. Young tableaux, volume 35 of London Mathematical Society Student Texts. Cambridge University Press, Cambridge, 1997.
- [Ful2] W. Fulton. Intersection theory, volume 2 of Ergebnisse der Mathematik und ihrer Grenzgebiete. 3. Folge. A Series of Modern Surveys in Mathematics. Springer-Verlag, Berlin, second edition, 1998.
- [GH] P. Griffiths and J. Harris. Principles of Algebraic Geometry. Wiley Interscience, 1978.
- [H] J. Harris. Algebraic geometry, volume 133 of Graduate Texts in Mathematics. Springer-Verlag, New York, 1995.
- [HM] J. Harris and I. Morrison. Moduli of curves. Springer-Verlag, 1998.
- [Ha] R. Hartshorne. Algebraic geometry. Springer-Verlag, New York, 1977. Graduate Texts in Mathematics, No. 52.
- [Kl1] S. L. Kleiman. The transversality of a general translate. Compositio Math. 28(1974), 287–297.
- [Kl2] S. L. Kleiman. Problem 15: Rigorous foundation of Schubert's enumerative calculus. In Mathematical developments arising from Hilbert problems (Proc. Sympos. Pure Math., Northern Illinois Univ., De Kalb, Ill., 1974), pages 445–482. Proc. Sympos. Pure Math., Vol. XXVIII. Amer. Math. Soc., Providence, R. I., 1976.
- [KL] S. L. Kleiman and D. Laksov. Schubert calculus. Amer. Math. Monthly 79(1972), 1061– 1082.
- [KT] A. Knutson and T. Tao. Puzzles and (equivariant) cohomology of Grassmannians. Duke Math. J. 119(2003), 221–260.
- [K] J. Kollár. Rational curves on algebraic varieties, volume 32 of Ergebnisse der Mathematik und ihrer Grenzgebiete. 3. Folge. A Series of Modern Surveys in Mathematics. Springer-Verlag, Berlin, 1996.
- [V1] R. Vakil. A geometric Littlewood-Richardson rule. to appear Ann. of Math.
- [V2] R. Vakil. Schubert induction. to appear Ann. of Math.

---

### DIVISOR CLASSES ON THE MODULI SPACE OF CURVES

#### 1. The cohomology of the moduli space of pointed genus zero curves

In this section we discuss the Chow rings of the moduli spaces of n-pointed genus zero curve  $\overline{\mathrm{M}}_{0,n}$ . Recall that we are working over the complex numbers  $\mathbb{C}$ . The cohomology and Chow groups of  $\overline{\mathrm{M}}_{0,n}$  turn out to be isomorphic. The main statement is that the Chow/cohomology ring of  $\overline{\mathrm{M}}_{0,n}$  is generated by the classes of boundary divisors. The main reference for this section is [Kee].

The basic strategy for determining the Chow/cohomology ring of  $\overline{\mathrm{M}}_{0,n}$  is to exhibit  $\overline{\mathrm{M}}_{0,n}$  as a sequence of blow-ups of the product  $\mathbb{P}^1 \times \cdots \times \mathbb{P}^1$  of n-3 copies of  $\mathbb{P}^1$  along smooth centers. One then inductively calculates the Chow ring at each stage of the blow-up process using the following basic theorem.

**Theorem 1.1** (The Chow ring of blow-ups). Let X be a codimension d smooth subvariety of a smooth variety Y with normal bundle  $N_{X/Y}$ . Let  $i: X \to Y$  denote the inclusion of X in Y. Let  $\tilde{Y}$  be the blow-up of Y along X. Assume that

$$i^*: A(Y) \to A(X)$$

is surjective. Then

$$A^*(\tilde{Y}) \cong \frac{A^*(Y)[\zeta]}{\langle \zeta \ker(i^*), \zeta^d + \zeta^{d-1}c_1(N_{X/Y}) + \dots + \zeta c_{d-1}(N_{X/Y}) + c_d(N_{X/Y}) \rangle}$$

where  $-\zeta$  is the class of the exceptional divisor.

Now we introduce the generators of the Chow ring. Let S be a subset of  $\{1,\ldots,n\}$  with the property that both S and its complement have at least two elements. We will denote the number of elements of S by #S. Given such a set we can define the class  $\delta_S$  on  $\overline{\mathrm{M}}_{0,n}$  as the class of the divisor  $\Delta_S$  of stable curves C that have a separating node that divides C into  $C_1 \cup C_2$  where the labelings of the points on  $C_1$  are precisely the elements of S and the labelings of the points on  $C_2$  are precisely the elements of  $S^c$ . The divisor  $\Delta_S$  is a normal crossings divisor isomorphic to

$$\Delta_S \cong \overline{M}_{0,S \cup \{r\}} \times \overline{M}_{0,S^c \cup \{s\}}$$

obtained by the map that glues the marked points r and s.

The main theorem about the Chow ring of  $\overline{\mathrm{M}}_{0,n}$  is the following:

**Theorem 1.2** (Keel). The Chow/cohomology ring of  $\overline{M}_{0,n}$  is generated by the classes  $\delta_S$  where  $\#S \geq 2$  and  $\#S^c \geq 2$  subject to the following relations:

- (1)  $\delta_S = \delta_{S^c}$ .
- (2) For any four distinct elements  $i, j, k, l \in \{1, ..., n\}$

$$\sum_{i,j \in S, k, l \notin S} \Delta_S = \sum_{i,k \in S, j, l \notin S} \delta_S = \sum_{i,l \in S, j, k \notin S} \delta_S.$$

#### (3) For two subsets S and T

$$\delta_S \delta_T = 0$$

unless  $S \subset T, T \subset S, S \subset T^c$  or  $T^c \subset S$ .

**Example 1.3.** Since  $\overline{\mathrm{M}}_{0,4} \cong \mathbb{P}^1$ , the classes of the three boundary divisors  $\Delta_{\{1,2\}}$ ,  $\Delta_{\{1,3\}}$  and  $\Delta_{\{1,4\}}$  are linearly equivalent. If we specialize the statement of the theorem to n=4 we recover the cohomology of  $\mathbb{P}^1$ .

**Remark 1.4.** It is easy to see that the claimed relations are satisfied. The divisor classes  $\delta_S$  and  $\delta_{S^c}$  are equal since the divisors they represent are equal.

To prove the relation

$$\sum_{i,j \in S, k, l \notin S} \delta_S = \sum_{i,k \in S, j, l \notin S} \delta_S$$

consider the map

$$\pi_{i,j,k,l}:\overline{\mathrm{M}}_{0,n}\to\overline{\mathrm{M}}_{0,4}$$

given by forgetting all the points, but the points labeled by i, j, k, l and stabilizing the resulting curve. The pull-back of the divisor class  $\delta_{\{i,j\}}$  on  $\overline{\mathrm{M}}_{0,4}$  is given by

$$\sum_{i,j\in S,k,l\notin S} \delta_S.$$

The pull-back of the divisor class  $\delta_{\{i,k\}}$  on  $\overline{\mathrm{M}}_{0,4}$  is given by

$$\sum_{i,k\in S, j,l\notin S} \delta_S.$$

Since these divisors have to be linearly equivalent, the relation follows.

Finally to see that  $\delta_S \delta_T = 0$  unless  $S \subset T, T \subset S, S \subset T^c$  or  $T^c \subset S$  note that two divisors  $\Delta_S$  and  $\Delta_T$  contain the point represeting a curve C in their intersection if and only if there are two nodes on C that divide C into  $C_1, C_2$  and  $C_1', C_2'$  where the labeling on  $C_1$  is S and the labeling on  $C_1'$  is S. Observe that unless the conditions  $S \subset T, T \subset S, S \subset T^c$  or  $T^c \subset S$  are satisfied S and S and S are disjoint, hence the product of their classes is zero in the Chow/cohomology ring.

**Example 1.5.** We can view  $\overline{\mathrm{M}}_{0,5}$  as the blow-up of  $\mathbb{P}^1 \times \mathbb{P}^1$  at the three points (0,0),(1,1) and  $(\infty,\infty)$ . Hence  $\overline{\mathrm{M}}_{0,5}$  is isomorphic to the Del Pezzo surface  $D_5$ . The 10 boundary divisors on  $\overline{\mathrm{M}}_{0,5}$  correspond to the 10 exceptional curves on  $D_5$ . We can recover the cohomology ring of  $D_5$  from Keel's relations. Note that Keel's second set of relations in this case give us that for any distinct 4-tuple i,j,k,l:

$$\delta_{i,i} + \delta_{k,l} = \delta_{i,k} + \delta_{i,l} = \delta_{i,l} + \delta_{i,k}$$

Multiplying these relations by  $\delta_{i,j}$  and using the third set of relations easily gives that  $\delta_{i,j}^2 = \delta_{k,l}^2 = -\delta_{r,s}\delta_{t,u}$  for any i,j,k,l and distinct r,s,t,u. Finally all triple products vanish. Note that one can give a very simple presentation of the cohomology ring of  $D_5$  realizing it as the blow-up of  $\mathbb{P}^2$  in four points. Sending the divisors  $\delta_{i,5}$  to the classes of the four exceptional divisors  $E_1,\ldots,E_4$  and  $\delta_{i,j}$  to  $H-E_k-E_l$  (where  $\{k,l\}$  is disjoint from  $\{i,j,5\}$ ) for the remaining i,j gives a ring isomorphism. Here H denotes the hyperplane class on  $\mathbb{P}^2$ . Hence, Keel's presentation is not necessarily the simplest presentation.

Exercise 1.6. Verify the claims made in the discussion of the previous example.

**Exercise 1.7.** Using the description of the cohomology ring of  $\overline{\mathrm{M}}_{0,n}$  determine its Betti numbers. Find the Euler characteristic of  $\overline{\mathrm{M}}_{0,n}$ .

Now we can describe the main technical tool that allows one to compute the Chow ring of  $\overline{\mathrm{M}}_{0,n}$ . Consider the map

$$\pi_{n+1}: \overline{\mathrm{M}}_{0,n+1} \to \overline{\mathrm{M}}_{0,n}$$

given by forgetting the last marked point. This morphism factors through

$$\overline{M}_{0,n+1} \xrightarrow{\phi} \overline{M}_{0,n} \times \overline{M}_{0,4}$$

$$\downarrow^{\pi_{n+1}} \qquad \qquad \downarrow^{pr_1} \qquad \downarrow^{pr_1}$$

$$\overline{M}_{0,n} \xrightarrow{id} \overline{M}_{0,n}$$

where  $pr_2$  is the projection onto the second factor and  $\phi$  is induced by  $(\pi_{n+1}, \pi_{4,...,n})$  where  $\pi_{4,...,n}$  is the morphism that forgets all but the points marked 1,2,3,n+1. The calculation is based on the obervation that the morphism  $\phi$  is in fact a sequence of n-3 blow-ups along explicit smooth centers.

Set  $X_1 = \overline{\mathrm{M}}_{0,n} \times \overline{\mathrm{M}}_{0,4}$ . If S is a subset of  $\{1,\ldots,n\}$ , we can embed the divisors  $\Delta_S$  into  $X_1$  by first mapping  $\Delta_S$  by the universal section corresponding to the i-th point to  $\overline{\mathrm{M}}_{0,n+1}$ , then following it with the map to  $X_1$ . Let  $X_2$  be the blow-up of  $X_1$  along  $\Delta_S$  where  $\#S^c = 2$  and S contains at most one of 1,2,3. Note that these are disjoint in  $X_1$ . Let  $X_3$  be the blow-up of  $X_2$  along the proper transform of the  $\Delta_S$  with  $\#S^c = 3$  and S contains at most one of 1,2,3. Continue in this way where  $X_k$  is the blow-up of  $X_{k-1}$  along the proper transform of  $\Delta_S$  with  $\#S^c = k$  such that S contains at most one of 1,2,3. Then  $\overline{\mathrm{M}}_{0,n+1} \cong X_{n-2}$  and the map

$$\phi: \overline{\mathrm{M}}_{0,n+1} \to \overline{\mathrm{M}}_{0,n} \times \overline{\mathrm{M}}_{0,4}$$

is the blowing-up just described.

To finish the proof of Theorem 1.2 we simply have to inductively apply the theorem describing the Chow ring of the blow-up repeatedly. This is messy but straightforward (see [Kee]).

**Remark 1.8.** Note that the construction of  $\overline{M}_{0,n}$  as a blow-up of  $\mathbb{P}^1 \times \cdots \times \mathbb{P}^1$  implies that the Chow ring and the cohomology ring are isomorphic. In particular,  $\overline{M}_{0,n}$  does not have any odd cohomology.

Remark 1.9. Observe that  $M_{0,n}$  is an affine variety. Fixing three of the points at 0, 1 and  $\infty$  we can view this space as the complement of hyperplanes in  $\mathbb{C}^{n-3}$ . Hence,  $M_{0,n}$  is affine of dimension n-3. Recall that the homology of an affine manifold vanishes above half its real dimension.

**Theorem 1.10.** Let X be a smooth, complex affine variety of complex dimension n, then  $H_k(X,\mathbb{Q}) = 0$  for k > n.

Milnor's proof of this theorem using Morse theory is one of the most beautiful proofs in mathematics (see [Mi]). We conclude that the cohomology  $H_k(M_{0,n}, \mathbb{Q})$  vanishes for k > n - 3.

Note that Theorem 1.2 in particular determines second homology/the Picard group of  $\overline{\mathrm{M}}_{0,n}$ .

Corollary 1.11. The Picard group of  $\overline{M}_{0,n}$  is generated by the classes of boundary divisors  $\Delta_S$  subject to the relations  $\delta_S = \delta_{S^c}$  and for any four distinct elements  $i, j, k, l \in \{1, \ldots, n\}$ 

$$\sum_{i,j \in S, k, l \notin S} \delta_S = \sum_{i,k \in S, j, l \notin S} \delta_S = \sum_{i,l \in S, j, k \notin S} \delta_S.$$

**Exercise 1.12.** Determine the class of the canonical divisor of  $\overline{\mathrm{M}}_{0,n}$ .

In fact, we can do better than the previous corollary.

**Proposition 1.13.** Let  $n \geq 4$ . Fix three distinct indeces i, j, k. The second cohomology group of  $\overline{M}_{0,n}$  has basis  $\delta_{\{j,k\}}$ ,  $\delta_S$  where  $i \in S$  and  $\#S \leq n-3$ .

*Proof.* We can give an elementary proof of this result that does not depend on the complicated combinatorics of Keel's theorem. We already saw that the boundary divisors generate the second cohomology (e.g. the complement of the boundary is  $\mathbb{C}^{n-3}$  with some hyperplanes removed) and that the relations in Keel's theorem are satisfied. We need to show that we can express all boundary divisors in terms of these and that these are independent. The only boundary divisors not on the list are those of the form  $\delta_{u,v}$  where neither of u,v is i and the pair is not j,k. Writing the boundary relation for i, w, u, v we see that

$$\delta_{\{i,w\}} + \sum_{i,w \in S, u, v \not \in S, 3 \leq \#S \leq n-3} \delta_S + \delta_{\{u,v\}} = \delta_{\{i,v\}} + \sum_{i,v \in S, u, w \not \in S, 3 \leq \#S \leq n-3} \delta_S + \delta_{\{u,w\}}.$$

Hence  $\delta_{\{u,v\}} = \delta_{\{u,w\}}$ . Taking v = j and then applying the relation again to replace u by k, we see that the given boundary divisors generate.

We prove the fact that they are independent by induction. Suppose there was a relation among them. Look at the morphism forgetting a point other than i, j, k. It immediately follows that all the coefficients of the relation have to be zero.  $\Box$ 

**Remark 1.14.** Note that the following proposition implies that the rank of the second cohomology group is

$$2^{n-1} - \frac{n^2 - n + 2}{2}.$$

#### 2. The second homology group of the moduli space of curves

Originally Harer determined the second homology group of the moduli space of curves by computing the second homology group of the mapping class group. Some good references for Harer's work on this computation is Harer's original paper [Har1] and Harer's C.I.M.E. notes [Har2]. Here we will outline Arbarello and Cornalba's algebraic approach to the computation of the second homology group [AC2].

We begin by introducing some divisor classes on  $\overline{\mathrm{M}}_{q,n}$ . Let

$$\pi_{n+1}: \overline{\mathrm{M}}_{g,n+1} \to \overline{\mathrm{M}}_{g,n}$$

denote the morphism that forgets the last marked point. Let  $\omega_{\pi_{n+1}}$  be the relattive dualizing sheaf.  $\pi_{n+1}$  has n sections given by the marked points  $p_1, \ldots, p_n$ . Denote the images of these sections  $\sigma_i$  by  $\Sigma_i$ . The class  $\kappa$  in this notation is defined by

$$\kappa = \pi_{n+1} * (c_1(\omega_{\pi_{n+1}}(\sum_{i=1}^n \Sigma_i))^2).$$

The classes of the n cotangent lines  $\psi_i$  for  $1 \leq i \leq n$  are defined by

$$\psi_i = \sigma_i^*(\omega_{\pi_{n+1}}).$$

The sum  $\sum_{i=1}^{n} \psi_i$  is often denoted by  $\psi$ .

Finally there are the classes of the boundary divisors. Let  $\delta_{irr}$  be the class of the divisor of curves  $\Delta_{irr}$  that contain a non-separating node. Let  $0 \le h \le g$  be an integer and let S be a subset of  $\{1,\ldots,n\}$ . Let  $\delta_{h,S}$  be the class of the divisor  $\Delta_{h,S}$  of curves that contain a node which separates the curve into two components of genus h with marked points  $p_i$  for  $i \in S$  and genus g - h and marked points  $p_i$  for  $i \in S^c$ . If h (respectively, g - h) is zero, we require that  $\#S \ge 2$  ( $\#S^c \ge 2$ ). There is one exception to this definition. When we define the class  $\delta_{1,\emptyset} = \delta_{g-1,n}$ , we need to be careful because a general member of this divisor has an automorphism of order 2. When we define this class, we take it to be half the class of the locus of the class of the boundary divisor. In terms of this notation the main theorem of this section is the following:

**Theorem 2.1.** Let g and n be non-negative integers such that 2g - 2 + n > 0 and g > 0. The second cohomology group  $H^2(\overline{M}_{g,n}, \mathbb{Q})$  is generated by the classes  $\kappa$ ,  $\psi_i$  for  $1 \le i \le n$  and the classes  $\delta_{irr}$  and  $\delta_{h,S}$  such that  $0 \le h \le g$  and 2h - 2 + #S > 0 and  $2(g - h) - 2 + \#S^c > 0$ .

(1) If g > 2, the relations among these classes are generated by

$$\delta_{h,S} = \delta_{a-h,S^c}$$
.

(2) If g = 2, there is the additional relation

$$5\kappa = 5\psi + \delta_{irr} - 5\delta_0 + 7\delta_1.$$

(3) If g = 1, there are the following two additional relations

$$\kappa = \psi - \delta_0, \quad 12\psi_p = \delta_{irr} + 12 \sum_{p \in S, \#S \ge 2} \delta_{0,S}.$$

Since Theorem 1.2 already determines the genus zero case we will omit it from our discussion.

The strategy of the proof is to do induction on the genus and the number of marked points. We now explain the mechanism that allows us to do this induction. Recall that since the coarse moduli scheme  $\overline{\mathrm{M}}_{g,n}$  is an orbifold, Poincaré duality holds for it provided that we work with rational coefficients.

We need to know the vanishing of the k-th homology groups of  $M_{g,n}$  for large k. Recall Harer's theorem which states that the moduli space  $M_{g,n}$  has the homotopy type of a finite cell complex of dimension 4g-4+n for n>0. Since the homology groups of a finite cell complex vanish in dimension bigger than the dimension of the cell complex, we can deduce that

$$H_k(M_{q,n}) = 0, k > 4g - 4 + n, n > 0$$

Furthermore, a spectral sequence argument implies that

$$H_k(M_{q,0}, \mathbb{Q}) = 0, \ k > 4g - 5.$$

Combining this vanishing with Poincaré duality and the long exact sequence of cohomology

$$H_c^k(\mathcal{M}_{q,n},\mathbb{Q}) \to H^k(\overline{\mathcal{M}}_{q,n},\mathbb{Q}) \to H^k(\delta\mathcal{M}_{q,n},\mathbb{Q}) \to H_c^{k+1}(\mathcal{M}_{q,n},\mathbb{Q})$$

we conclude the following proposition.

**Proposition 2.2.** The map  $H^k(\overline{M}_{g,n}, \mathbb{Q}) \to H^k(\delta M_{g,n}, \mathbb{Q})$  is an isomorphism when k < d(g,n) and injective when k = d(g,n), where d(g,n) is defined by

$$d(g,n) = \begin{cases} n-4 & \text{if } g = 0\\ 2g-2 & \text{if } n = 0\\ 2g-3+n & \text{if } g, n > 0. \end{cases}$$

This proposition gives us hope to do induction on the genus and the number of marked points. Recall that

$$\Delta_{irr} \cong \overline{\mathbf{M}}_{g-1, P \cup \{r, s\}}$$

where the isomorphism is obtained by attaching the marked points r and s to obtain a curve of arithmetic genus q. Similarly

$$\Delta_{h,S} \cong \overline{\mathbf{M}}_{h,S \cup \{r\}} \times \overline{\mathbf{M}}_{g-h,S^c \cup \{s\}}$$

where the isomorphism is obtained by attaching the two curves along the last marked points. The problem is while we can inductively understand each irreducible component of boundary of the moduli space, these boundary components intersect. However, the next proposition guarantees that this does not effect the small cohomology groups.

**Proposition 2.3.** Let  $X_i$ ,  $i \in I$ , denote all the irreducible components of the boundary of  $\overline{M}_{q,n}$ . The map

$$H^k(\overline{M}_{g,n},\mathbb{Q}) \to \bigoplus_{i \in I} H^k(X_i,\mathbb{Q})$$

is injective if  $k \leq d(g, n)$ .

Sketch. This proposition follows from the fact that the map

$$H^k(\overline{\mathrm{M}}_{q,n},\mathbb{Q}) \to H^k(\delta\mathrm{M}_{q,n},\mathbb{Q})$$

is a morphism of Hodge structures. Since the map is an injection in the claimed range and  $H^k(\overline{\mathrm{M}}_{g,n},\mathbb{Q})$  is pure of weight k, the cohomology injects to the weight k part of the cohomology. The proposition follows from a result of Deligne which asserts that if  $f:X\to Y$  is a proper, surjective morphism from a smooth variety to a proper variety, then the weight k quotient of  $H^k(Y,\mathbb{Q})$  is the image of  $H^k(Y,\mathbb{Q})$  in  $H^k(X,\mathbb{Q})$ . Taking X to be the disjoint union of the irreducible components of the boundary and Y to be the boundary, Deligne's result (at least its modification for orbifolds) implies the proposition.

**Proposition 2.4.** Let  $\xi: \overline{M}_{g-1,n+2} \to \overline{M}_{g,n}$  be the morphism that glues the last two marked points. Then the induced map

$$\xi^*: H^2(\overline{M}_{q-1,n+2},\mathbb{Q}) \to H^2(\overline{M}_{q,n},\mathbb{Q})$$

is injective if  $g \geq 2$ .

**Exercise 2.5.** Prove the Proposition 2.4 by induction on the number of marked points and the genus. Use Künneth decomposition, Proposition 2.3 and the fact that  $H^1(\overline{\mathrm{M}}_{g,n},\mathbb{Q})=0$  for every g and n. There are many ways of proving the last statement. It follows, for example, from the fact that  $\overline{\mathrm{M}}_{g,n}$  is simply connected. We will see an elementary proof in the next section.

2.1. The relations among tautological classes. In this subsection we indicate how tautological divisor classes pull-back under special morphisms. Let

$$\pi_{n+1}: \overline{\mathrm{M}}_{g,n+1} \to \overline{\mathrm{M}}_{g,n}$$

be the morphism that forgets the n + 1st marked point.

Exercise 2.6. Prove the following formulae:

- (1)  $\pi_{n+1}^*(\kappa) = \kappa \psi_{n+1}$ .
- (2)  $\pi_{n+1}^*(\psi_i) = \psi_i \delta_{0,\{i,n+1\}}$  for  $i \le n$ .
- (3)  $\pi_{n+1}^*(\delta_{irr}) = \delta_{irr}$ .
- (4)  $\pi_{n+1}^*(\delta_{h,S}) = \delta_{h,S} + \delta_{h,S \cup \{n+1\}}.$

Let

$$\xi: \overline{\mathbf{M}}_{g-1,n\cup\{x,y\}} \to \overline{\mathbf{M}}_{g,n}$$

be the morphism that glues the two points x, y.

**Exercise 2.7.** Show that  $\xi$  pulls back the tautological classes as follows:

- (1)  $\xi^*(\kappa) = \kappa$ .
- (2)  $\xi^*(\phi_i) = \phi_i \text{ for } i < n.$
- (3)  $\xi^*(\delta_{irr}) = \delta_{irr} \psi_x \psi_y + \sum_{x \in S, y \notin S} \delta_{g,S}$

(4) 
$$\xi^*(\delta_{h,S}) = \begin{cases} \delta_{h,S} & \text{if } g = 2h, \quad n = 0\\ \delta_{h,S} + \delta_{h-1,S \cup \{x,y\}} & \text{otherwise} \end{cases}$$

Finally, we need to know the pull-backs of tautological classes by the morphism

$$at_{h,S}: \overline{\mathbf{M}}_{g-h,n-S\cup\{x\}} \to \overline{\mathbf{M}}_{g,n}$$

obtained by attaching a fixed curve of genus h and marking  $S \cup \{y\}$  to curves in  $\overline{\mathrm{M}}_{q-h,n-S\cup\{x\}}$  by identifying x and y.

Exercise 2.8. Show that the following relations hold:

- (1)  $at_{h,S}^*(\kappa) = \kappa$ .
- (2)  $at_{h,S}^*(\phi_i) = \begin{cases} \phi_i & \text{if } i \in S \\ 0 & \text{otherwise} \end{cases}$
- (3)  $at_{h,S}^*(\delta_{irr}) = \delta_{irr}$ .

(4) If 
$$S = \{1, ..., n\}$$
, then

$$at_{h,S}^*(\delta_{k,T}) = \begin{cases} \delta_{2h-g,S\cup\{x\}} - \psi_x & \text{if } k = h, \#T = n, \text{ or } k = g-h, \#T = 0\\ \delta_{k,T} + \delta_{k+h-g,T\cup\{x\}} & \text{otherwise} \end{cases}$$

(5) If 
$$S \neq \{1, ..., n\}$$
, then

$$at_{h,S}^{*}(\delta_{k,T}) = \begin{cases} -\psi_{x} & \text{if } (k,T) = (h,S) \text{ or } (k,T) = (g-h,S^{c}) \\ \delta_{k,T} & \text{if } T \subset S \text{ and } (k,T) \neq (h,S) \\ \delta_{k+h-g,(T \setminus S^{c}) \cup \{x\}} & \text{if } S^{c} \subset T \text{ and } (k,T) \neq (g-h,S^{c}) \\ 0 & \text{otherwise} \end{cases}$$

Using the previous three exercises we can obtained the claimed relations in Theorem 2.1. Recall that the Hodge class  $\lambda$  is the first chern class of the Hodge bundle.

**Lemma 2.9** (Mumford's relation). On any  $\overline{M}_{g,n}$  there is the following relation  $\kappa = 12\lambda - \delta + \psi$ .

*Proof.* It suffices to prove the formula when n=0. The general case follows by pulling-back via the relations given by the forgetful morphisms. We use the Grothendieck - Riemann - Roch (GRR) formula to see the case n=0. Set

$$\Omega = \Omega_{\overline{M}_{q,1}/\overline{M}_q}^1.$$

Recall the GRR formula reads

$$ch(\pi_{1!}F) = \pi_{1*}(ch(F) \cdot Todd(\Omega)).$$

Set  $F = \omega_{\overline{M}_{g,1}/\overline{M}_g}$ . Since  $R^1\pi_{1*}$  of the relative dualizing sheaf is trivial, solving for the degree one term of the GRR formula we obtain

$$\lambda = c_1(\pi_{1*}F) = \pi_{1*}(\frac{c_1(\Omega)^2 + c_2(\Omega)}{12} - \frac{c_1(F)c_1(\Omega)}{2} + \frac{c_1(F)}{2})$$

A local calculation shows that

$$c_1(\Omega^1_{\overline{M}_{g,1}/\overline{M}_g}) = c_1(\omega^1_{\overline{M}_{g,1}/\overline{M}_g}), \quad c_2(\Omega^1_{\overline{M}_{g,1}/\overline{M}_g}) = [Sing]$$

where Sinq denotes the singular locus. This follows from the exact sequence

$$0 \to \Omega^{\frac{1}{M_{g,1}/\overline{M}_g}} \to \omega^{\frac{1}{M_{g,1}/\overline{M}_g}} \to \omega^{\frac{1}{M_{g,1}/\overline{M}_g}} \otimes \mathcal{O}_{Sing} \to 0.$$

Mumford's formula immediately follows.

Now all the relations follow when we observe that on  $\overline{\mathrm{M}}_2$  we have the relation

$$10\lambda = \delta_0 + 2\delta_1$$
.

To prove this relation, for instance, consider the following test families.

- (1) To a fixed genus 1 curve attach a fixed point of a genus 1 curve at a variable point.
- (2) On a genus 1 curve identify a variable point with a fixed point.
- (3) Identify a fixed point of a fixed genus 1 curve with a pencil of plane cubics.

**Exercise 2.10.** By calculating the intersections of these families with  $\delta_0, \delta_1$  and  $\lambda$  prove the claimed equality.

Exercise 2.11. Deduce the relations in Theorem 2.1 from the relations in this section.

**Remark 2.12.** By intersecting with test families it is not hard to show that the relations in Theorem 2.1 are the only relations among tautological divisors.

2.2. Sketch of the proof of Theorem 2.1. In this subsection we will sketch the proof of Theorem 2.1. We would like to show that  $H^2(\overline{\mathrm{M}}_{g,n},\mathbb{Q})$  is tautological. Assume that the tautological classes generate the second cohomology of  $\overline{\mathrm{M}}_{h,m}$  whenever h < g or h = g and m < n. Suppose that the genus is at least 3 for now.

Let  $d \in H^2(\overline{\mathrm{M}}_{g,n},\mathbb{Q})$  be any class. Consider

$$\xi^* d \in H^2(\overline{\mathbf{M}}_{q-1,n \cup \{x,y\}}, \mathbb{Q})$$

where  $\xi: \overline{\mathrm{M}}_{g-1,n\cup\{x,y\}} \to \overline{\mathrm{M}}_{g,n}$  is the morphism that identifies the two points x,y. Since by induction  $H^2(\overline{\mathrm{M}}_{g-1,n\cup\{x,y\}},\mathbb{Q})$  is tautological  $\xi^*d$  may be expressed as a linear combination of tautological classes. Moreover, since the morphism is symmetric under exchanging x and y, the expressions of divisors involving x and y need to be symmetric. Hence,  $\xi^*d$  is a linear combination of  $\kappa$ ,  $\psi_i$ ,  $i \leq n$ ,  $\psi_x + \psi_y$ ,  $\delta_{irr}$ ,  $\delta_{h,S}$ ,  $\delta_{h,S\cup\{x,y\}}$  and  $\delta_{h,S\cup\{x\}} + \delta_{h,S\cup\{y\}}$ .

We can find a tautological class  $d_t$  in  $H^2(\overline{\mathbb{M}}_{g,n}, \mathbb{Q})$  such that  $\xi^*(d-d_t)$  can be expressed only in terms of  $\psi_x + \psi_y$ ,  $\delta_{h,S \cup \{x,y\}}$  and  $\delta_{h,S \cup \{x\}} + \delta_{h,S \cup \{y\}}$ . To conclude that all the coefficients vanish we further pull-back  $\xi^*(d-d_t)$  by the morphism

$$ell_{g-2}: \overline{\mathbf{M}}_{g-2,n\cup\{x,y,z\}} \to \overline{\mathbf{M}}_{g-1,n\cup\{x,y\}}$$

obtained by attaching a fixed elliptic tail at the marked point z. We could also pull-back  $d-d_t$  to  $\overline{\mathrm{M}}_{g-2,n\cup\{x,y,z\}}$  in a different order, first by the map

$$ell_{g-1}: \overline{\mathbf{M}}_{g-1,n\cup\{z\}} \to \overline{\mathbf{M}}_{g,n}$$

that attaches a fixed elliptic curve at the point z, then by the map

$$\xi_{g-2}: \overline{\mathbf{M}}_{g-2,n\cup\{x,y,z\}} \to \overline{\mathbf{M}}_{g-1,n\cup\{z\}}$$

that identifies the points x and y. The classes of these two pull-backs have to coincide. This gives a relation that shows that  $\xi^*(d-d_t)$  must be identically zero. Since by Proposition 2.4, the map  $\xi^*$  is injective, we conclude that d is tautological.

To conclude the proof then one needs to analyze the cases of genus 1 and 2 in greater detail. This is straightforward but tedious. We leave you to read the details in [AC2].

#### 3. The first, third and fifth cohomology groups of moduli space

The purpose of this section is to sketch an elementary proof of the vanishing of the first, third and fifth cohomology groups of  $\overline{\mathbf{M}}_{g,n}$  following Arbarello and Cornalba [AC2].

**Theorem 3.1.** 
$$H^{k}(\overline{M}_{q,n}, \mathbb{Q}) = 0$$
 for  $k = 1, 3, 5$ .

The proof proceeds by reducing the general case to checking the vanishing for finitely many  $\overline{M}_{g,n}$  with g and n small and carrying out these verifications explicitly. As in the previous section set

$$d(g,n) = \begin{cases} n-4 & \text{if } g=0\\ 2g-2 & \text{if } n=0\\ 2g-3+n & \text{if } g,n>0. \end{cases}$$

Recall that  $H^k(\overline{M}_{g,n},\mathbb{Q})$  injects into  $\oplus_i H^k(X_i,\mathbb{Q})$  where the  $X_i$  denote all the irreducible components of the boundary. Like in the previous section we have the following Reduction Lemma.

**Lemma 3.2** (Reduction Lemma). Let k be an odd integer. Suppose that

$$H^q(\overline{M}_{g,n},\mathbb{Q})=0$$

for all odd  $q \leq k$ , and for all g and n such that q > d(g, n), then

$$H^q(\overline{M}_{q,n},\mathbb{Q})=0$$

for all odd  $q \leq k$  and all q and n.

In other words, as long as all the odd cohomology for j < k vanishes, to conclude vanishing of the k-th cohomology it suffices to verify it for finitely many special values, namely those values for which q > d(g, n).

Proof. The proof is by induction on k. Suppose  $H^q(\overline{M}_{g,n},\mathbb{Q})$  vanishes for all odd  $q \leq k$ . We can assume  $d(g,n) \geq k$ . By the previous lemma we conclude that  $H^k(\overline{M}_{g,n},\mathbb{Q})$  injects into  $H^k(X_i,\mathbb{Q})$ . Each  $X_i$  is of the form  $\overline{M}_{g-1,n+2}$  or a product of  $\overline{M}_{a,A}$  and  $\overline{M}_{b,B}$  where either a < g or a = g and |A| < n. (Similarly for b and b). Using the Künneth formula, we conclude that  $H^k(\overline{M}_{g,n},\mathbb{Q})$  injects into a direct sum of  $H^k(\overline{M}_{g-1,n+2},\mathbb{Q})$  and  $H^l(\overline{M}_{a,A},\mathbb{Q}) \otimes H^m(\overline{M}_{b,B},\mathbb{Q})$  with l+m=k. Since either l or m must be odd, all these spaces vanish by the induction hypothesis except possibly for k=m or k=l. In this case either the genus is smaller than a or if the genus is equal to a the number of marked points is smaller than a0. A double induction concludes the proof.

Proof of vanishing of the first cohomology. By the Reduction Lemma to prove that the first cohomology groups of  $\overline{M}_{q,n}$  vanish we need to check the cases

$$\overline{M}_{0,3}, \overline{M}_{0,4}, \overline{M}_{1,0}.$$

 $\overline{M}_{0,3}$  consists of a single point.  $\overline{M}_{0,4}$  and  $\overline{M}_{1,1}$  are isomorphic to the projective line. The first cohomology of all these spaces vanish. This concludes the proof that  $H^1(\overline{M}_{q,n},\mathbb{Q})=0$  for all g and n.

Remark 3.3.  $H^1(\overline{M}_{g,n},\mathbb{Q})=0$  also follows from the fact that  $\overline{M}_{g,n}$  is simply connected. However, note that  $M_{g,n}$  is not simply connected. This is one reason why computing the cohomology of the compactified moduli space is simpler. For example, we can identify  $M_{0,4}$  with  $\mathbb{P}^1$  with three points removed. Fix the three marked points at  $0,1,\infty$ . The fourth fixed point is free to vary on the sphere except it cannot be one of the other three marked points. The fundamental group of  $\mathbb{P}^1 - \{0,1,\infty\}$  is the free group on two letters. In particular, the first cohomology group of  $\mathbb{P}^1 - \{0,1,\infty\}$  has rank 2. In contrast we saw above that all odd cohomology groups of  $\overline{M}_{0,n}$  vanish.

To emphasize the point, observe that the Euler characteristic of  $M_{0,n}$  is given by the formula

$$\chi(M_{0,n}) = (-1)^{(n-3)}(n-3)!.$$

To prove this formula consider the map  $M_{0,n} \to M_{0,n-1}$  given by forgetting one of the marked points. This is a fibration with each fiber given by a sphere with n-1 points removed. We conclude that the Euler characteristic of  $M_{0,n}$  is  $(3-n)\chi(M_{0,n-1})$ . The result follows by induction. The Euler characteristic of  $M_{0,n}$  is negative for even n. At least for those n, the odd cohomology groups cannot vanish.

<u>Proof of the vanishing of third cohomology</u>. To conclude that  $H^3$  vanishes for all  $\overline{M}_{q,n}$  we need to check the cases

- (1) g = 0 and  $3 \le n \le 6$ ,
- (2) g = 1 and  $1 \le n \le 3$ , and
- (3) g = 2 and n = 0 or 1.

We already observed that the odd cohomology of  $\overline{M}_{0,n}$  vanishes. In this range, this is easy to check directly.)  $\overline{M}_{0,3}$  is a point so  $H^3$  clearly vanishes. Both  $\overline{M}_{0,4}$  and  $\overline{M}_{1,1}$  are isomorphic to  $\mathbb{P}^1$ , hence their third cohomology clearly vanishes.

The moduli spaces  $\overline{\mathrm{M}}_{0,5}$  and  $\overline{\mathrm{M}}_{1,2}$  both have complex dimension 2 or real dimension 4. By Poincaré duality we conclude that the dimension of  $H^3$  is equal to the dimension of  $H^1$ . Since  $H^1$  vanishes we conclude that  $H^3$  vanishes.

To show the vanishing of the third cohomology groups of  $\overline{M}_{2,0}$  and  $\overline{M}_{2,1}$ , we observe that they admit surjective morphisms from  $\overline{M}_{0,6}$  and  $\overline{M}_{0,7}$ , respectively. This suffices to show the vanishing of the third cohomology. Recall that genus 2 curves are all hyperelliptic. They are a double cover of  $\mathbb{P}^1$  ramified at six points. Given a Riemann sphere with six marked points take the hyperelliptic curve ramified over these six points. Similarly given a Riemann sphere with seven marked points take the hyperelliptic curve of genus 2 ramified at the first six with one of the points above the seventh point as marked. (Note that since the hyperelliptic involution takes one sheet of the covering to the other, the choice is immaterial.) We conclude that the third cohomology groups of these two spaces vanish.

We are left to consider the case g=1 and n=3. One way to check the vanishing of cohomology groups is to use Euler characteristic considerations. If Y is a quasi-projective variety which has a filtration by closed subvarieties  $\overline{Y}_i$ 

$$Y = \overline{Y}_d \subset \overline{Y}_{d-1} \subset \dots \subset \overline{Y}_1 \subset \overline{Y}_0$$

so that  $Y_i = \overline{Y}_i \backslash \overline{Y}_{i-1}$  is empty or of pure dimension i for every i, then by the exact sequence of cohomology with compact supports the Euler characteristic of Y with cohomology with compact supports is the sum of those of  $Y_d$  and  $\overline{Y}_{d-1}$ . Repeating the process and using Poincaré duality we conclude that the Euler characteristic of  $\overline{M}_{g,n}$  is the sum of the Euler characteristics of open strata where we stratify  $\overline{M}_{g,n}$  according to graph type.

 $\overline{M}_{1,3}$  has complex dimension 3 or real dimension 6. We already know that its first and by Poincaré duality its fifth cohomology groups vanish. The second cohomology group is generated by

$$\kappa, \psi_1, \psi_2, \psi_3, \delta_{irr}, \delta_{0,\{1,2\}}, \delta_{0,\{1,3\}}, \delta_{0,\{2,3\}}, \delta_{0,\{1,2,3\}}.$$

There are 4 independent linear relations among these. Hence the rank of the second (and by Poincaré duality fourth) cohomology groups are 5. If we can show that the Euler characteristic of  $\overline{M}_{1,3}$  is twelve, it follows that the third cohomology group has to vanish.

Let us compute that the Euler characteristic of  $\overline{M}_{1,3}$  is 12. This is done by splitting  $\overline{M}_{1,3}$  to its strata according to topological type. In this computation we need the Euler characteristics of  $M_{1,2}$ ,  $M_{1,3}$ ,  $M'_{0,4}$ ,  $M'_{0,5}$ , where  $M'_{0,4}$  and  $M'_{0,5}$  denote the space obtained by taking the quotients of  $M_{0,4}$  and  $M_{0,5}$  under the operation of interchanging the labeling of two marked points. To calculate the Euler characteristics of the latter two we note that we have morphisms from  $M_{0,4}$  and  $M_{0,5}$  to these spaces. Both morphisms have degree 2 since the fiber over a point has two points corresponding to the two different ways of ordering the identified marked points. The morphism from  $M_{0,4}$  to  $M'_{0,4}$  is ramified at one point. If there is only one point over  $(0, \infty, 1 \ x)$ , then there must be an automorphism of the sphere permuting 1 and x and keeping 0 and  $\infty$  fixed. This can only happen if x = -1 and the automorphism is multiplication by -1. By the Riemann-Hurwitz formula we conclude that  $\chi(M'_{0,4}) = 0$ . The map in the case of  $M'_{0,5}$  is unramified and therefore  $\chi(M'_{0,5}) = 1$ .

The Euler characteristics of  $M_{1,n}$  can be computed inductively. First,  $M_{1,1}$  is the affine line, so its Euler characteristic is 1. It is a fundamental theorem in the theory of elliptic curves that the group of automorphisms fixing a point is a group of order 2 except in two cases. In one case the elliptic curve can be realized as ramified over the points  $0, 1, -1, \infty$  of the sphere and it has the extra automorphism coming from rotating the sphere by  $\pi$  along the  $0 - \infty$  axis (multiplication by -1). In the other case the elliptic curve can be realized as ramified over the cube roots of unity and  $\infty$ . Its automorphism group has order 6 and it can be generated by the usual involution and by multiplication by a cube root of unity (rotation of the underlying sphere around the  $0 - \infty$  axis by an angle of  $2\pi/3$ ).

Consider the morphism from  $M_{1,2}$  to  $M_{1,1}$  given by forgetting the second marked point. The fiber over each point of  $M_{1,1}$  is an affine line. Hence, the Euler characteristic of  $M_{1,2}$  is 1. Next, consider the morphism from  $M_{1,3}$  to  $M_{1,2}$ . Here we need to break  $M_{1,2}$  up to pieces over which the fibers have nice descriptions. First, consider the case where  $p_2$ , the second marked point, is a 2-torsion point with respect to  $p_1$ . Observe that this space is  $M'_{0,4}$  and the fiber of the map over such a point is the sphere with two points removed. Next, there is the case when C is the special curve whose automorphism group has order 6 and  $p_2$  lies above 0. In

this case the fiber is also a sphere with two points removed. Finally, there is the case when  $p_2$  is not a 2-torsion point and not the special point considered in the previous case. In this case the fiber is an elliptic curve with two points removed. Adding up the various Euler characteristics we conclude that  $\chi(M_{1,3})=0$ . This information together with an enumeration of the strata of  $\overline{M}_{1,3}$  suffices to calculate that the Euler characteristic is 12. Since the Euler characteristic is 12, the third cohomology group must vanish. By the reduction lemma this completes the proof that all the third cohomology groups of  $\overline{M}_{g,n}$  vanish.

The technique for showing that the fifth cohomology groups of  $\overline{M}_{g,n}$  vanish is similar. The cases that need to be checked in this case are

- (1) g = 0 and  $n \le 8$
- (2) g = 1 and  $n \leq 5$
- (3) g = 2 and  $n \leq 3$
- (4) g = 3 and  $n \le 1$ .

We already know the case g = 0. The case g = 1 and  $n \le 4$  are easy. The remaining cases are more challenging.

**Remark 3.4.** Arbarello and Cornalba's approach outlined here cannot be applied directly to the odd cohomology groups for  $k \geq 11$  since these groups do not always vanish. For example,  $H^{11}(\overline{M}_{1,11},\mathbb{Q})$  does not vanish. Their inductive argument breaks down.

**Problem 3.5.** Determine  $H^7(\overline{\mathrm{M}}_{g,n},\mathbb{Q})$  and  $H^9(\overline{\mathrm{M}}_{g,n},\mathbb{Q})$ .

# 4. The Picard group of the moduli functor

In this section we will determine the Picard group of the moduli functor following [AC1]. A very good introduction to Picard groups of moduli functors is contained in [Mum].

Let  $\overline{\mathcal{M}}_{g,n}$  denote the moduli functor of genus g stable curves with n marked points. Let  $(C \to S, \sigma_1, \ldots, \sigma_n)$  denote a family of stable curves of genus g and n marked points parameterized by S. A line bundle on the moduli functor  $\overline{\mathcal{M}}_{g,n}$  is an assignment of a line bundle  $L_C$  to the base of the family S for every family  $C \to S$  and isomorphisms between  $L_D \cong \alpha^*(L_C)$  for every fiber diagram

$$D \xrightarrow{C} C$$

$$\downarrow \qquad \qquad \downarrow$$

$$T \xrightarrow{\alpha} S$$

satisfying the cocycle condition.

Similarly let  $\mathcal{M}_{g,n}$  denote the moduli functor of genus g smooth curves with n marked points. The Picard group of the functor  $\mathcal{M}_{g,n}$  is defined the same way.

The Hodge class  $\lambda$  and the classes of the boundary divisors  $\delta_{irr}, \delta_1, \ldots, \delta_{\lfloor g/2 \rfloor}$  are elemements of  $Pic(\overline{\mathcal{M}}_g)$ . Recall that the Hodge class  $\lambda$  is defined as the class of the determinant of the Hodge bundle which is the push-forward of the relative dualizing sheaf on any family. The class  $\delta_{irr}$  is the class of the divisor of curves

with a non-separating node. The class  $\delta_i$  is the class of the divisor of curves that contain a node that separates the curve to a subcurve of genus i and genus g - i.

Similarly  $\lambda, \psi_1, \ldots, \psi_n, \delta_{irr}, \delta_{h,S}$  are elements of  $Pic(\overline{\mathcal{M}}_{g,n})$ . Recall that  $\lambda$  is the Hodge class. The class  $\psi_i$  is the class of the cotangent line at the *i*-th marked point and is formally defined by the pull-back of the relative dualizing sheaf by the section giving the *i*-th marked point. The classes  $\delta_{h,S}$  are the classes of boundary divisors of curves containing a node that separates the curve to a subcurve of genus  $1 \leq h \leq \lfloor g/2 \rfloor$  with the marked points  $p_i$  for  $i \in S \subset \{1,\ldots,n\}$  and a residual curve of genus g-h with the remaining marked points. Of course, for the curve to be stable  $\#S \geq 2$  if h=0.

**Theorem 4.1.** Let  $g \geq 3$ . The Picard group  $Pic(\overline{\mathcal{M}}_g)$  is freely generated by the classes  $\lambda, \delta_{irr}, \delta_1, \ldots, \delta_{\lfloor g/2 \rfloor}$ . The Picard group  $Pic(\mathcal{M}_g)$  is freely generated by  $\lambda$ .

In the rest of the course we will only use Theorem 4.1. However, similar techniques also prove the following more general theorem.

**Theorem 4.2.** Let  $g \geq 3$ . The Picard group  $Pic(\overline{\mathcal{M}}_{g,n})$  is freely generated by the classes  $\lambda$ ,  $\psi_1, \ldots, \psi_n$  and the classes of boundary divisors. The Picard group  $Pic(\mathcal{M}_{g,n})$  is freely generated by  $\lambda$  and  $\psi_1, \ldots, \psi_n$ .

Sketch of the proof of Theorem 4.1. We first remark that  $Pic(\overline{\mathcal{M}}_g)$  is torsion free and contains  $Pic(\overline{\mathcal{M}}_g)$  as a finite index subgroup. To see that  $Pic(\overline{\mathcal{M}}_g)$  is torsion free one uses Teichmüller theory. Suppose  $Pic(\mathcal{M}_g)$  had a torsion element L of prime order p. Since the p-th power of L is trivial, we can take the p-th root of a nowhere vanishing section to get an unramified  $\mathbb{Z}/p\mathbb{Z}$  covering of any family. In particular, we get an unramified covering of Teichmüller space which must split completely. It follows that L has a section over the automorphism free locus. This extends to a holomorphic, nowehere vanishing section of L since the p-th power does. Hence L is trivial. Any class in  $Pic(\overline{\mathcal{M}}_g)$  whose restriction to  $\mathcal{M}_g$  is trivial is an integral linear combination of the boundary classes. The boundary classes are independent, hence  $Pic(\overline{\mathcal{M}}_g)$  is torsion free.

By the calculation of the second homology group of  $Pic(\overline{\mathcal{M}}_g)$ , we can express any divisor class as a linear combination of

$$\lambda, \delta_{irr}, \delta_1, \ldots, \delta_{\lfloor q/2 \rfloor}$$
.

The point is to show that it may be expressed as an integral linear combination. The strategy is to construct two different sets of one-parameter families of curves  $F_1, \ldots, F_{\lfloor g/2 \rfloor + 2}$  and  $G_1, \ldots, G_{\lfloor g/2 \rfloor + 2}$  such that their intersection matrices with respect to

$$\lambda, \delta_{irr}, \delta_1, \dots, \delta_{\lfloor g/2 \rfloor}$$

are non-singular and have relatively prime determinant. Since the determinant of these matrices times the coefficients of the expressions of any divisor class in terms of

$$\lambda, \delta_{irr}, \delta_1, \dots, \delta_{\lfloor g/2 \rfloor}$$

have to be integral, the theorem follows.

The required families are obtained as follows:

Let  $K_h$  be the family consisting of a pencil of hyperplane sections of a K3 surface of degree 2h-2 to which a fixed curve of genus g-h is attached at a base point of the pencil. It is easy to see that

$$K_h \cdot \delta_{irr} = 18 + 6h$$
,  $K_h \cdot \delta_h = -1$ ,  $K_h \cdot \delta_i = 0$  if  $i \neq h$ .

The degree of  $\lambda$  on  $K_h$  is h+1.

Let  $F_h$  be the family consisting of three curves  $C_1, C_2, E$  of genus h, g - h - 1and 1, respectively. Attach  $C_2$  to E at a fixed point, then attach  $C_1$  to E at a fixed point of  $E_1$ , but a variable point of E. The degree of  $\lambda$  on this familiy is zero. All the intersections with the boundary divisors vanish unless i = 1, h or h + 1. The degree of  $\delta_1$  on  $F_h$  is 1 if h > 1, 0 if g - h - 1 > h = 1 and -1 if g = 3and g-h-1=h=1. The degree of  $\delta_h$  on  $F_h$  is -1 if g-h-1>h=1 or if g-h-1=h=1, 0 if g-h-1>h=1 and -2 if g-h-1=h>1.

Let C be the family obtained by attaching a fixed genus q-3 curve at fixed 4 points to the base points of a pencil of conics. The degree of  $\lambda$  and  $\delta_i$  on this family is zero. The degree of  $\delta_{irr}$  is -1.

Finally let CE be the family obtained by attaching a genus g-3 curve at three of the base points of a pencil of conics and a genus one curve at the fourth base point. All the degrees except for the degree of  $\delta_1$  vanish on this family. The latter degree is -1.

The theorem follows from these computations. If the genus is 2m+1, the intersection matrix for the families

$$K_h, C, F_1, \ldots, F_m$$

has determinant  $(-1)^{m+1}(h+1)$  if  $m \ge h \ge 2$ . Taking h=2 and h=3 gives two relatively prime determinants. If the genus is 2m+2, the intersection matrix for the families

$$K_h, C, CE, F_1, \ldots, F_m$$

has determinant  $(-1)^{m+1}(h+1)$  if m > h > 2. Again taking h = 2 and h = 3 gives two relatively prime determinants.

# 5. The Tautological ring of ${\cal M}_g$

In this course we will not have time to discuss the tautological ring. In this section I will give a few references to where you may learn more about it. Many people have worked on it, including Faber, Looijenga, Pandharipande, Graber, Vakil, Getzler, Ionel to mame very few (see, for example, [Fab], [Lo], [FaP1], [FaP2], [GV1], [V], [GV2]). .

Usually when a moduli space is defined with respect to a universal property, it contains certain tautologically defined Chow classes. The prime example of such Chow classes are the chern classes of the universal tautological and quotient bundles on Grassmannians. The Chow ring of the Grassmannian is generated by these tautological classes.

For the moduli space of curves  $M_q$ , it is also possible to define tautological classes. Consider the universal curve

$$\pi_1: M_{g,1} \to M_g.$$

The first chern class of the relative dualizing sheaf leads to a sequence of classes on  $M_g$ . More precisely, let  $K = c_1(\omega_{M_g,1/M_g})$ . Define  $\kappa_l = \pi_{1*}K^{l+1}$ . These are classes in  $A^l(M_g)$ . Also on  $M_g$  there is a rank g locally free sheaf called the Hodge bundle  $\mathbb{E}$ . The Hodge bundle is defined by  $\mathbb{E} = \pi_{1*}\omega_{M_g,1/M_g}$ . The chern classes  $\lambda_l = c_l(\mathbb{E})$  also define classes in  $A^l(M_g)$ . The subring of the Chow ring generated by these classes is called the tautological ring.

One of the first things to observe is that the cohomology of  $M_g$  is not in general tautological. There are many ways to see this. The simplest is to observe that tautological classes are even cohomology classes. Since we have computed the Euler characteristic of the moduli spaces, we can see that the moduli space of curves has odd cohomology classes. There are also explicit constructions of non-tautological classes.

Faber has very detailed conjectures about the structure of the tautological ring. Roughly these conjectures say that the tautological ring of  $M_g$  exhibits properties that one would expect the algebraic cohomology ring of a smooth projective variety of dimension g-2 to exhibit. For instance that it is Gorenstein with socle in degree g-2, satisfies Hard Lefschetz and Hodge Positivity with respect to the class  $\kappa_1$ . Furthermore, Faber conjectures that

$$\kappa_1, \ldots \kappa_{\lfloor g/3 \rfloor}$$

generate the ring and gives some explicit relations among these generators. I refer you to the papers cited above for detailed statements and what is known.

## References

- [AC1] E. Arbarello and M. Cornalba. The Picard groups of the moduli spaces of curves. Topology 26(1987), 153–171.
- [AC2] E. Arbarello and M. Cornalba. Calculating cohomology groups of moduli spaces of curves via algebraic geometry. Inst. Hautes Études Sci. Publ. Math. (1998), 97–127 (1999).
- [Fab] C. Faber. A conjectural description of the tautological ring of the moduli space of curves. In Moduli of curves and abelian varieties, Aspects Math., E33, pages 109–129. Vieweg, Braunschweig, 1999.
- [FaP1] C. Faber and R. Pandharipande. Logarithmic series and Hodge integrals in the tautological ring. Michigan Math. J. 48(2000), 215–252. With an appendix by Don Zagier, Dedicated to William Fulton on the occasion of his 60th birthday.
- [FaP2] C. Faber and R. Pandharipande. Hodge integrals, partition matrices, and the  $\lambda_g$  conjecture. Ann. of Math. (2) **157**(2003), 97–124.
- [GP] T. Graber and R. Pandharipande. Constructions of nontautological classes on moduli spaces of curves. Michigan Math. J. 51(2003), 93–109.
- [GV1] T. Graber and R. Vakil. On the tautological ring of  $\overline{M}_{g,n}$ . Turkish J. Math. **25**(2001), 237–243.
- [GV2] T. Graber and R. Vakil. Relative virtual localization and vanishing of tautological classes on moduli spaces of curves. Duke Math. J. 130(2005), 1–37.
- [Har1] J. Harer. The second homology group of the mapping class group of an orientable surface. Invent. Math. 72(1983), 221–239.
- [Har2] J. L. Harer. The cohomology of the moduli space of curves. In Theory of moduli (Montecatini Terme, 1985), volume 1337 of Lecture Notes in Math., pages 138–221. Springer, Berlin, 1988.
- [Kee] S. Keel. Intersection theory of moduli space of stable n-pointed curves of genus zero. Trans. Amer. Math. Soc. **330**(1992), 545–574.
- [Lo] Eduard Looijenga. On the tautological ring of  $M_g$ . Invent. Math. 121(1995), 411–419.
- [Mi] J. Milnor. Morse theory. Based on lecture notes by M. Spivak and R. Wells. Annals of Mathematics Studies, No. 51. Princeton University Press, Princeton, N.J., 1963.

- [Mum] D. Mumford. Picard groups of moduli problems. In Arithmetical Algebraic Geometry (Proc. Conf. Purdue Univ., 1963), pages 33–81. Harper & Row, New York, 1965.
- [V] R. Vakil. The moduli space of curves and its tautological ring. *Notices Amer. Math. Soc.* **50**(2003), 647–658.

---

#### THE MODULI SPACE OF CURVES

# 1. The moduli space of curves and a few remarks about its construction

The theory of smooth algebraic curves lies at the intersection of many branches of mathematics. A smooth complex curve may be considered as a Riemann surface. When the genus of the curve is at least 2, then it may also be considered as a hyperbolic two manifold, that is a surface with a metric of constant negative curvature. Each of these points of view enhance our understanding of the classification of smooth complex curves. While we will begin with an algebraic treatment of the problem, we will later use insights offered by these other perspectives.

As a first approximation we would like to understand the functor

$$\mathcal{M}_q: \{\text{Schemes}\} \to \{\text{sets}\}$$

that assigns to a scheme Z the set of families (up to isomorphism)  $X \to Z$  flat over Z whose geometric fibers are smooth curves of genus g.

There are two problems with this functor. First, there does not exist a scheme that represents this functor. Recall that given a contravariant functor F from schemes over S to sets, we say that a scheme X(F) over S and an element  $U(F) \in F(X(F))$  represents the functor finely if for every S scheme Y the map

$$\operatorname{Hom}_S(Y, X(F)) \to F(Y)$$

given by  $g \to g^*U(F)$  is an isomorphism.

**Example 1.1.** The main obstruction to the representability (in particular, to the existence of a universal family) of  $\mathcal{M}_q$  is curves with automorphisms. For instance, fix a hyperelliptic curve C of genus g. Let  $\tau$  denote the hyperelliptic involution of C. Let S be a K3-surface with a fixed point free involution i such that S/i is an Enriques surface E. To be very concrete let C be the normalization of the plane curve defined by the equation  $y^2 = p(x)$  where p(x) is a polynomial of degree 2g + 2with no repeated roots. The hyperelliptic involution is given by  $(x,y) \mapsto (x,-y)$ . Let  $Q_1, Q_2, Q_3$  be three general ternary quadratic forms. Let the K3-surface S be defined by the vanishing of the three polynomials  $Q_i(x_0, x_1, x_2) + Q_i(x_3, x_4, x_5) = 0$ with the involution that exchanges the triple  $(x_0, x_1, x_2)$  with  $(x_3, x_4, x_5)$ . Consider the quotient of  $C \times S$  by the fixed-point free involution  $\tau \times i$ . The quotient is a non-trivial family over the Enriques surface E; however, every fiber is isomorphic to C. If  $\mathcal{M}_q$  were finely represented by a scheme, then this family would correspond to a morphism from E to it. However, this morphism would have to be constant since the moduli of the fibers is constant. The trivial family would also give rise to the constant family. Hence,  $\mathcal{M}_q$  cannot be finely represented.

There are two ways to remedy this problem. The first way is to ask a scheme to only coarsely represent the functor. Recall the following definition:


**Definition 1.2.** Given a contravariant functor F from schemes over S to sets, we say that a scheme X(F) over S coarsely represents the functor F if there is a natural transformation of functors  $\Phi: F \to \operatorname{Hom}_S(*, X(F))$  such that

- (1)  $\Phi(spec(k)) : F(spec(k)) \to \operatorname{Hom}_S(spec(k), X(F))$  is a bijection for every algebraically closed field k,
- (2) For any S-scheme Y and any natural transformation  $\Psi: F \to \operatorname{Hom}_S(*,Y)$ , there is a unique natural transformation

$$\Pi: \operatorname{Hom}_S(*, X(F)) \to \operatorname{Hom}_S(*, Y)$$

such that  $\Psi = \Pi \circ \Phi$ .

The main theorem of moduli theory asserts that there exists a quasi-projective moduli scheme coarsely representing the functor  $\mathcal{M}_q$ .

Alternatively, we can ask for a Deligne-Mumford stack that parameterizes smooth curves. Below we will give a few details explaining how both constructions work.

There is another serious problem with the functor  $\mathcal{M}_g$ . Most families of curves in projective space specialize to singular curves. This makes it seem unlikely that any moduli space of smooth curves will be proper. This, of course, is in no way conclusive. It is useful to keep the following cautionary tale in mind.

**Example 1.3.** Consider a general pencil of smooth quartic plane curves specializing to a double conic. To be explicit fix a general, smooth quartic F in  $\mathbb{P}^2$ . Let Q be a general conic. Consider the family of curves in  $\mathbb{P}^2$  given by

$$C_t: Q^2 + tF.$$

I claim that after a base change of order 2, the central fiber of this family may be replaced by a smooth, hyperelliptic curve of genus 3. The total space of this family is singular at the 8 points of intersection of Q and F. These are ordinary double points of the surface. We can resolve these singularities by blowing up these points.

FIGURE 1. Quartics specializing to a double conic.

We now make a base change of order 2. This is obtained by taking a double cover branched at the exceptional curves  $E_1, \ldots, E_8$ . The inverse image of the proper transform of  $C_0$  is a double cover of  $\mathbb{P}^1$  branched at the 8 points. In particular,

it is a hyperelliptic curve of genus 3. The inverse image of each exceptional curve is rational curve with self-intersection -1. These can be blown-down. Thus, after base change, we obtain a family of genus 3 curves where every fiber is smooth.

Exercise 1.4. Consider a general pencil of quartic curves in the plane specializing to a quartic with a single node. Show that it is not possible to find a flat family of curves (even after base change) that replaces the central fiber with a smooth curve. (Hint: After blowing up the base points of the pencil, we can assume that the total space of the family is smooth and the surface is relatively minimal. First, assume we can replace the central fiber by a smooth curve without a base change. Use Zariski's main theorem to show that this is impossible. Then analyze what happens when we perform a base change.)

The previous exercise shows that the coarse moduli scheme of smooth curves (assuming it exists) cannot be proper. Given that curves in projective space can become arbitrarily singular, it is an amazing fact that the moduli space of curves can be compactified by allowing curves that have only nodes as singularities.

**Definition 1.5.** Consider the tuples  $(C, p_1, \ldots, p_n)$  where C is a connected at worst nodal curve of arithmetic genus g and  $p_1, \ldots, p_n$  are distinct smooth points of C. We call the tuple  $(C, p_1, \ldots, p_n)$  stable if in the normalization of the curve any rational component has at least three distinguished points—inverse images of nodes or of  $p_i$ —and any component of genus one has at least one distinguished point.

Note that for there to be any stable curves the inequality 2g - 2 + n > 0 needs to be satisfied.

**Definition 1.6.** Let S be a scheme. A stable curve over S is a proper, flat family  $C \to S$  whose geometric fibers are stable curves.

**Theorem 1.7** (Deligne-Mumford-Knudsen). There exists a coarse moduli space  $\overline{\mathcal{M}}_{g,n}$  of stable n-pointed, genus g curves.  $\overline{\mathcal{M}}_{g,n}$  is a projective variety and contains the coarse moduli space  $\mathcal{M}_{g,n}$  of smooth n-pointed genus g curves as a Zariski open subset.

One way to construct the coarse moduli scheme of stable curves is to consider pluri-canonically embedded curves, that is curves embedded in projective space  $\mathbb{P}^{(2n-1)(g-1)-1}$  by their complete linear system  $|nK_C|$  for  $n\geq 3$ . A locally closed subscheme K of the Hilbert scheme parameterizes the locus of n-canonical curves of genus g. The group PGL((2n-1)(g-1)) acts on K. The coarse moduli scheme may be constructed as the G.I.T. quotient of K under this action. The proof that this construction works is lengthy. Below we will briefly explain some of the main ingredients. We begin by recalling the key features of the construction of the Hilbert scheme. We then recall the basics of G.I.T..

#### 2. A FEW REMARKS ABOUT THE CONSTRUCTION OF THE HILBERT SCHEME

Assume in this section that all schemes are Noetherian. Recall that the Hilbert functor is a contravariant functor from schemes to sets defined as follows:

**Definition 2.1.** Let  $X \to S$  be a projective scheme,  $\mathcal{O}(1)$  a relatively ample line bundle and P a fixed polynomial. Let

$$Hilb_P(X/S): \{Schemes/S\} \rightarrow \{sets\}$$

be the contravariant functor that associates to an S scheme Y the subschemes of  $X \times_S Y$  which are proper and flat over Y and have the Hilbert polynomial P.

A major theorem of Grothendieck asserts that the Hilbert functor is representable by a projective scheme.

**Theorem 2.2.** Let X/S be a projective scheme,  $\mathcal{O}(1)$  a relatively ample line bundle and P a fixed polynomial. The functor  $Hilb_P(X/S)$  is represented by a morphism

$$u: U_P(X/S) \to Hilb_P(X/S).$$

 $Hilb_P(X/S)$  is projective over S.

I will explain some of the ingredients that go into the proof of this theorem, leaving you to read [Gr], [Mum2], [K], [Se] and the references contained in those accounts for complete details.

Let us first concentrate on the case  $X = \mathbb{P}^n$  and S = Spec(k), the spectrum of a field k. A subscheme of projective space is determined by its equations. The polynomials in  $k[x_0,\ldots,x_n]$  that vanish on a subscheme form an infinite-dimensional subvector space of  $k[x_0,\ldots,x_n]$ . Suppose we knew that a finite-dimensional subspace actually determined the schemes with a fixed Hilbert polynomial. Then we would get an injection of the schemes with a fixed Hilbert polynomial into a Grassmannian. We have already seen that the Grassmannian (together with its tautological bundle) represents the functor classifying subspaces of a vector space. Assuming the image in the Grassmannian is an algebraic subscheme, we can use this subscheme to represent the Hilbert functor.

Given a proper subscheme Y of  $\mathbb{P}^n$  and a coherent sheaf F on Y, the higher cohomology  $H^i(Y, F(m))$ , i > 0, vanishes for m sufficiently large. The finiteness that we are looking for comes from the fact that if we restrict ourselves to ideal sheaves of subschemes with a fixed Hilbert polynomial, one can find an integer m depending only on the Hilbert polynomial (and not on the subscheme) that works simultaneously for the ideal sheaf of every subscheme with a fixed Hilbert polynomial.

**Theorem 2.3.** For every polynomial P, there exists an integer  $m_P$  depending only on P such that for every subsheaf  $I \subset \mathcal{O}_{\mathbb{P}^n}$  with Hilbert polynomial P and every integer  $k > m_P$ 

- (1)  $h^i(\mathbb{P}^n, I(k)) = 0 \text{ for } i > 0;$
- (2) I(k) is generated by global sections;
- (3)  $H^0(\mathbb{P}^n, I(k)) \otimes H^0(\mathbb{P}^n, \mathcal{O}(1)) \to H^0(\mathbb{P}^n, I(k+1))$  is surjective.

How does this theorem help? Let  $Y \subset \mathbb{P}^n$  be a closed subscheme with Hilbert polynomial P. Choose  $k > m_P$ . By item (2) of the theorem,  $I_Y(k)$  is generated by global sections. Consider the exact sequence

$$0 \to I_Y(k) \to \mathcal{O}_{\mathbb{P}^n}(k) \to \mathcal{O}_Y(k) \to 0.$$

This realizes  $H^0(\mathbb{P}^n, I_Y(k))$  as a subspace of  $H^0(\mathbb{P}^n, \mathcal{O}_{\mathbb{P}^n}(k))$ . This subspace determines  $I_Y(k)$  and hence the subscheme Y. Since k depends only on the Hilbert polynomial, we get an injection to  $G(P(k), H^0(\mathbb{P}^n, \mathcal{O}_{\mathbb{P}^n}(k))$ . The image has a natural scheme structure. This scheme together with the restriction of the tautological bundle to it, represents the Hilbert functor. I will now fill in some of the details,

leaving most of them to you. Let us begin with a sketch of the proof of the theorem.

**Definition 2.4.** A coherent sheaf F on  $\mathbb{P}^n$  is called (Castelnuovo-Mumford) mregular if  $H^i(\mathbb{P}^n, F(m-i)) = 0$  for all i > 0.

**Proposition 2.5.** If F is an m-regular coherent sheaf on  $\mathbb{P}^n$ , then

- (1)  $h^i(\mathbb{P}^n, F(k)) = 0$  for i > 0 and k + i > m.
- (2) F(k) is generated by global sections if  $k \ge m$ . (3)  $H^0(\mathbb{P}^n, F(k)) \otimes H^0(\mathbb{P}^n, \mathcal{O}(1)) \to H^0(\mathbb{P}^n, F(k+1))$  is surjective if  $k \ge m$ .

*Proof.* The proposition is proved by induction on the dimension n. When n=0. the result is clear. Take a general hyperplane H and consider the following exact sequence

$$0 \to F(k-1) \to F(k) \to F_H(k) \to 0.$$

When k = m - i, the associated long exact sequence of cohomology gives that

$$H^{i}(F(m-i)) \to H^{i}(F_{H}(m-i)) \to H^{i+1}(F(m-i-1)).$$

In particular, if F is m-regular on  $\mathbb{P}^n$ , then so is  $F_H$  on  $\mathbb{P}^{n-1}$ . Now we can prove the first item by induction on k. Now consider the similar long exact sequence

$$H^{i+1}(F(m-i-1) \to H^{i+1}(F(m-i)) \to H^{i+1}(F_H(m-i-1)).$$

The first group vanishes by induction on dimension and the third one vanishes by the assumption that F is m regular for  $i \geq 0$ . We conclude that F is m+1 regular. Hence by induction k regular for all k > m. This proves item (1).

Consider the commutative diagram

$$H^{0}(F(k-1)) \otimes H^{0}(\mathcal{O}_{\mathbb{P}^{n}}(1)) \xrightarrow{u} H^{0}(F_{H}(k-1)) \otimes H^{0}(\mathcal{O}_{H}(1))$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \downarrow \qquad \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad$$

The map u is surjective by the regularity assumption. The map f is surjective by induction on the dimension. It follows that  $v \circ g$  is also surjective. Since the image of  $H^0(F(k-1))$  is contained in the image of g, claim (3) follows.

It is easy to deduce 
$$(2)$$
 from  $(3)$ .

The proof of the theorem is concluded if we can show that the ideal sheaves of proper subchemes of  $\mathbb{P}^n$  with a fixed Hilbert polynomial are  $m_P$ -regular for an integer depending only on P. This claim also follows by induction on the dimension n. Choose a general hyperplane H and consider the exact sequence

$$0 \to I(m) \to I(m+1) \to I_H(m+1) \to 0.$$

 $I_H$  is a sheaf of ideals so we may use induction on the dimension.

Assume the Hilbert polynomial is given by

$$P(m) = \sum_{i=0}^{n} a_i \binom{m}{i}.$$

We then have

$$\chi(I_H(m+1)) = \chi(I(m+1)) - \chi(I(m))$$

$$= \sum_{i=0}^{n} a_i \left( \binom{m+1}{i} - \binom{m}{i} \right) = \sum_{i=0}^{n-1} a_{i+1} \binom{m}{i}$$

Assuming the result by induction, we get an integer  $m_1$  depending only on the coefficients  $a_1, \ldots, a_n$  such that  $I_H$  has that regularity. Considering the long exact sequence associated to our short exact sequence, we see that  $H^{i}(I(m))$  is isomorphic to  $H^{i}(I(m+1))$  as long as i>1 and  $m>m_1-i$ . Since by Serre's theorem these cohomologies vanish when m is large enough, we get the vanishing of the higher cohomology groups. For i=1 we only get that  $h^1(I(m))$  is strictly decreasing for  $m \ge m_1 - 1$ . We conclude that I is  $m_1 + h^1(I(m_1 - 1))$ -regular. However, since I is an ideal sheaf we can bound the latter term as follows

$$h^1(I(m_1-1)) = h^0(I(m_1-1)) - \chi(I(m_1-1)) \le h^0(\mathcal{O}_{\mathbb{P}^n}(m_1-1)) - \chi(I(m_1-1)).$$
 This clearly depends only on the Hilbert polynomial; hence concludes the proof of Theorem 2.3.

Now we indicate how one proceeds to deduce Theorem 2.2. So far we have given an injection from the set of subshemes of  $\mathbb{P}^n$  with a fixed Hilbert polynomial Pto the Grassmannian  $G(P(m), H^0(\mathbb{P}^n, \mathcal{O}_{\mathbb{P}^n}(m)))$  for any  $m > m_P$  by sending the subscheme to the P(m)-dimensional subspace  $H^0(\mathbb{P}^n, I(m))$  of  $H^0(\mathbb{P}^n, \mathcal{O}_{\mathbb{P}^n}(m))$ . Of course, this subspace uniquely determines the subscheme. We still have to show that the image has a natural scheme structure and that this subscheme represents the Hilbert functor. For this purpose we will use flattening stratifications.

Recall that a stratification of a scheme S is a finite collection  $S_1, \ldots, S_j$  of locally closed subschemes of S such that

$$S = S_1 \sqcup \cdots \sqcup S_i$$

is a disjoint union of these subschemes.

**Proposition 2.6.** Let F be a coherent sheaf on  $\mathbb{P}^n \times S$ . Let S and T be Noetherian schemes. There exists a stratification of S such that for all morphisms  $f: T \to S$ ,  $(1 \times f)^*F$  to  $\mathbb{P}^n \times T$  is flat over T if and only if the morphism factors through the stratification.

This stratification is called the flattening stratification (see Lecture 8 in [Mum2] for the details). To prove it one uses the fact that if  $f: X \to S$  is a morphism of finite type, S is integral and F is any coherent sheaf on X, then there is a dense open subset U of S such that the restriction of F to  $f^{-1}(U)$  is flat over U. A corollary is that S can be partitioned into finitely many locally closed subsets  $S_i$ such that giving each the reduced induced structure, the restriction of F to  $X \times_S S_i$ is flat over  $S_i$ .

We can partition S to locally closed subschemes as in the previous paragraph. Only finitely many Hilbert polynomials  $P_i$  occur. We can conclude that there is an integer m such that if  $l \geq m$ , then

$$H^i(\mathbb{P}^n(s), F(s)(l)) = 0$$

and

$$\pi_{S*}F(l)\otimes k(s)\to H^0(\mathbb{P}^n(s),F(s)(l))$$

is an isomorphism, where  $\pi_S$  denotes the natural projection to S.

Next one observes that  $(1 \times f)^*F$  is flat over T if and only if  $f^*\pi_{S*}F(l)$  is locally free for all  $l \geq m$ . For each l we find the stratification of S such that  $S_{l,j}$  the sheaf  $f^*\pi_{S*}F(l)$  is locally free of rank j. Note that there is the following equality between subsets of S

$$\bigcap_{l\geq m} \operatorname{Supp}[S_{l,j}] = \bigcap_{m+n\geq l\geq m} \operatorname{Supp}[S_{l,j}].$$

This is because the Hilbert polynomials have degree at most n.

For each integer  $h \geq 0$ , there is a well-defined locally closed subscheme of S defined by

$$\cap_{0 \leq r \leq h} S_{r,P_i(m+r)}$$
.

When  $h \ge n$ , these form a decreasing sequence of subschemes with the same support. Therefore, they stabilize. These give us the required stratification.

The flattening stratification allows us to put a scheme structure on the image of our map to the Grassmannian. More precisely, consider the incidence correspondence

$$I \subset \mathbb{P}^n \times G(P(m_P), H^0(\mathbb{P}^n, \mathcal{O}_{\mathbb{P}^n}(m_P))).$$

The incidence correspondence has two projections

$$\pi_1:I\to\mathbb{P}^n$$

and

$$\pi_2: I \to G(P(m_P), H^0(\mathbb{P}^n, \mathcal{O}_{\mathbb{P}^n}(m_P))).$$

For the rest of this section we will abbreviate  $G(P(m_P), H^0(\mathbb{P}^n, \mathcal{O}_{\mathbb{P}^n}(m_P)))$  simply by G.  $\pi_2^*T(-m_P)$  where T is the tautological bundle on G is an idea sheaf of  $\mathcal{O}_{\mathbb{P}^n\times G}$ . Let us denote the corresponding subscheme by Y. The flattening stratification of  $\mathcal{O}_Y$  over G gives a subscheme  $H_P$  of G corresponding to the Hilbert polynomial P. (Note that this is the scheme structure that we put on the set we earlier obtained.) The claim is that  $H_P$  represents the Hilbert functor and the universal family is the restriction W of Y to the inverse image of  $H_P$ .

Suppose we have a subscheme  $X \subset \mathbb{P}^n \times S$  mapping to S via f and flat over S (and suppose the Hilbert polynomial is P). We obtain an exact sequence

$$0 \to f_*I_X(m_P) \to f_*\mathcal{O}_{\mathbb{P}^n \times S}(m_P) \to f_*\mathcal{O}_X(m_P) \to 0.$$

By the universal property of the Grassmannian G, this induces a map  $g: S \to G$ . Since

$$f_*I_X(m) = g^*\pi_{2*}I_Y(m)$$

for m sufficiently large, we see that  $(1 \times g)^* \mathcal{O}_Y$  is flat with Hilbert polynomial P, hence g factors through  $H_P$  by the definition of the flattening stratification. Moreover, X is simply  $S \times_{H_P} W$ . This concludes the construction of  $Hilb_P(\mathbb{P}^n/S)$ .

Exercise 2.7. Verify the details of the above construction.

So far we have constructed the Hilbert scheme as a quasi-projective subscheme of the Grassmannian. To prove that it is projective it suffices to check that it is proper. This is done by checking the valuative criterion of properness. This follows from the following proposition [Ha] III.9.8.

**Proposition 2.8.** Let X be a regular, integral scheme of dimension one. Let  $p \in X$  be a closed point. Let  $Z \subset \mathbb{P}^n_{X-p}$  be a closed subscheme flat over X-p. Then there exists a unique closed subscheme  $\overline{Z} \in \mathbb{P}^n_X$  flat over X, whose restriction to  $\mathbb{P}^n_{X-p}$  is Z.

**Exercise 2.9.** Deduce from the proposition that the Hilbert scheme we constructed is projective.

**Exercise 2.10.** For a projective scheme X/S construct  $Hilb_P(X/S)$  as a locally closed subscheme of  $Hilb_P(\mathbb{P}^n/S)$ .

**Exercise 2.11.** Suppose X and Y are projective schemes over S. Assume X is flat over S. Let Hom(X,Y) be the functor that associates to any S scheme T the set of morphisms

$$X \times_S T \to Y \times_S T$$
.

Using our construction of the Hilbert scheme and noting that a morphism may be identified with its graph construct a scheme that represents the functor Hom(X,Y).

2.1. Examples of Hilbert schemes. In this subsection we would like to give some explicit examples of Hilbert schemes.

**Example 2.12.** Consider the Hilbert scheme associated to a projective variety X and the Hilbert polynomial 1. Then the Hilbert scheme is simply X.

**Exercise 2.13.** Show that if C is a smooth curve, then  $Hilb_n(C)$  is simply the symmetric n-th power of C. In particular,  $Hilb_n(\mathbb{P}^1) = \mathbb{P}^n$ 

**Exercise 2.14.** Show that the Hilbert scheme of hypersurfaces of degree d in  $\mathbb{P}^n$  is isomorphic to  $\mathbb{P}^{\binom{n+d}{d}-1}$ .

**Example 2.15** (The Hilbert scheme of conics in  $\mathbb{P}^3$ ). Any degree 2 curve is necessarily the complete intersection of a linear and quadratic polynomial. Moreover, the linear polynomial is uniquely determined. We thus obtain a map

$$Hilb_{2n-1}(\mathbb{P}^3) \to \mathbb{P}^{3*}.$$

The fibers of this map are  $Hilb_{2n-1}(\mathbb{P}^2)$  which is isomorphic to  $\mathbb{P}^5$ . We conclude by Zariski's main theorem that that  $Hilb_{2n-1}(\mathbb{P}^3)$  is the  $\mathbb{P}^5$  bundle  $\mathbb{P}(Sym^2T^*) \to \mathbb{P}^{3*}$ . Of course, in all this discussion we needed the fact that  $Hilb_{2n-1}(\mathbb{P}^3)$  is reduced.

**Theorem 2.16.** Let X be a projective scheme over a field k and  $Y \subset X$  be a closed subscheme, then the Zariski tangent space to Hilb(X) at [Y] is naturally isomorphic to  $Hom_Y(I_Y/I_Y^2, \mathcal{O}_Y)$ .

In particular, in our case the dimension of  $THilb_{2n-1}(\mathbb{P}^3)=h^0(N_{C/\mathbb{P}^3})=8$ . Hence  $Hilb_{2n-1}(\mathbb{P}^3)$  is reduced (in fact smooth).  $Hilb_{2n-1}(\mathbb{P}^3)$  is one of the few examples where we can answer many of the geometric questions we can ask about a Hilbert scheme.

We can use the Hilbert scheme of conics to solve the following question:

Question 2.17. How many conics in  $\mathbb{P}^3$  intersect 8 general lines in  $\mathbb{P}^3$ ?

As in the case of Schubert calculus, we can try to calculate this number as an intersection in the cohomology ring. The cohomology ring of a projective bundle over a smooth variety is easy to describe in terms of the chern classes of the bundle and the cohomology ring of the variety.

**Theorem 2.18.** Let E be a rank n vector bundle over a smooth, projective variety X. Suppose that the chern polynomial of E is given by  $\sum c_i(E)t^i$ . Let  $\zeta$  denote the first chern class of the dual of the tautological bundle over  $\mathbb{P}E$ . The cohomology of  $\mathbb{P}E$  is isomorphic to

$$H^*(\mathbb{P}E) \cong \frac{H^*(X) [\zeta]}{< \zeta^n + \zeta^{n-1}c_1(E) + \dots + c_n(E) = 0 >}$$

If you are not familiar with chern classes, see the handout about chern classes. Using Theorem 2.18 we can compute the cohomology ring of  $Hilb_{2n-1}(\mathbb{P}^3)$ . Recall that  $T^*$  on  $\mathbb{P}^{3*}$  is a rank 3 vector bundle with chern polynomial

$$c(T^*) = 1 + h + h^2 + h^3.$$

Using the splitting principle we assume that the polynomial splits into three linear factors

$$(1+x)(1+y)(1+z)$$
.

Then the chern polynomial of  $Sym^2(T^*)$  is given by

$$(1+2x)(1+2y)(1+2z)(1+x+y)(1+x+z)(1+y+z).$$

Multiplying this out and expressing it in terms of the elementary symmetric polynomials in x, y, z, we see that

$$c(Sym^2(T^*)) = 1 + 4h + 10h^2 + 20h^3.$$

It follows that the cohomology ring of  $Hilb_{2n-1}(\mathbb{P}^3)$  is given as follows:

$$H^*(Hilb_{2n-1}(\mathbb{P}^3)) \cong \frac{\mathbb{Z}[h,\zeta]}{\langle h^4, \zeta^3 + 4h\zeta^2 + 10h^2\zeta + 20h^3 \rangle}$$

The class of the locus of conics interseting a line is given by  $2h + \zeta$ . This can be checked by a calculation away from codimension at least 2. Consider the locus of planes in  $\mathbb{P}^{3*}$  that do not contain the line l. Over this locus there is a line bundle that associates to each point (H,Q) on  $Hilb_{2n-1}(\mathbb{P}^3)$  the homogeneous quadratic polynomials modulo those that vanish at  $H \cap l$ . This line bundle is none other than the pull-back of  $\mathcal{O}_{\mathbb{P}^{3*}}$ . The tautological bundle over  $Hilb_{2n-1}(\mathbb{P}^3)$  maps by evaluation. The locus where the evaluation vanishes is the locus of conics that intersect l. Hence the class is the difference of the first chern classes. Finally, we compute  $(2h + \zeta)^8$  using the presentation of the ring to obtain 92.

Over the complex numbers we can invoke Kleiman's theorem to deduce that there are 92 smooth conics intersecting 8 general lines in  $\mathbb{P}^3$ .

**Exercise 2.19.** Calculate the number of conics that intersect 8-2i lines and contain i points for  $0 \le i \le 3$ .

**Exercise 2.20.** Calculate the class of conics that are tangent to a plane in  $\mathbb{P}^3$ . Find how many conics are tangent to a general plane and intersect 7 general lines.

**Exercise 2.21.** Generalize the previous discussion to conics in  $\mathbb{P}^4$ . Calculate the numbers of conics that intersect general 11 - 2i - 3j planes, i lines and j points.

**Example 2.22** (The Hilbert scheme of twisted cubics in  $\mathbb{P}^3$ ). The Hilbert polynomial of a twisted cubic is 3t+1. This Hilbert scheme has two components. A general point of the first component parameterizes a smooth rational curve of degree 3 in  $\mathbb{P}^3$ . A general point of the second component parameterizes a degree

3 plane curve together with a point in  $\mathbb{P}^3$ . Note that the dimension of the first component is 12, whereas the dimension of the second component is 15. Hence the Hilbert scheme is not pure dimensional. The component of the Hilbert scheme parameterizing the smooth rational curves has been studies in detail. In fact, that component is smooth.

**Exercise 2.23.** Describe the subschemes of  $\mathbb{P}^3$  that are parameterized by the component of the Hilbert scheme that parameterizes smooth rational curves of degree 3 in  $\mathbb{P}^3$ .

Piene and Schlessinger proved that the component of the Hilbert scheme parameterizing twisted cubics is smooth. In analogy with our analysis of the Hilbert scheme of conics we can try to compute invariants of cubics using the Hilbert scheme. Unfortunately, this turns out to be very difficult.

**Problem 2.24.** Calculate the number of twisted cubics intersecting 12 general lines in  $\mathbb{P}^3$ .

**Problem 2.25.** Calculate the number of twisted cubics that are tangent to 12 general quadric hypersurfaces in  $\mathbb{P}^3$ . (Hint: There are 5,819,539,783,680 of them.)

Towards the end of the course we will see how to use the Kontsevich moduli space to answer these questions.

Unfortunately, Hilbert schemes are often unwieldy schemes to work with. They often have many irreducible components. It is hard to compute the dimensions of these components. Even components of the Hilbert scheme whose generic point parameterizes smooth curves in  $\mathbb{P}^3$  may be everywhere non-reduced.

**Example 2.26** (Mumford's example). Mumford showed that there exists a component of the Hilbert scheme parameterizing smooth curves of degree 14 and genus 24 in  $\mathbb{P}^3$  that is non-reduced at the generic point of that component. See [Mum1] or [HM] Chapter 1 Section D.

The pathological behavior of most Hilbert schemes make them hard to use for studying the explicit geometry of algebraic varieties. In fact, the Hilbert schemes often exhibit behavior that is arbitrarily bad. For instance, R. Vakil recently proved that all possible singularities occur in some component of the Hilbert scheme of curves in projective space.

**Theorem 2.27** (Murphy's Law). Every singularity class of finite type over  $Spec\mathbb{Z}$  occurs in a Hilbert scheme of curves in some projective space.

# 3. Basics about curves

Here we collect some basic facts about stable curves.

If  $\pi: C \to S$  is a stable curve of genus g over a scheme S, then C has a relative dualizing sheaf  $\omega_{C/S}$  with the following properties

- (1) The formation of  $\omega_{C/S}$  commutes with base change.
- (2) If  $S = Spec \ k$  where k is an algebraically closed field and  $\tilde{C}$  is the normalization of C, then  $\omega_{C/S}$  may be identified with the sheaf of meromorphic differentials on  $\tilde{C}$  that are allowed to have simple poles only at the inverse image of the nodes subject to the condition that if the points x and y lie over the same node then the residues at these two points must sum to zero.

(3) In particular, if C is a stable curve over a field k, then  $H^1(C, \omega_{C/k}^{\otimes n}) = 0$  if  $n \geq 2$  and  $\omega_{C/k}^{\otimes n}$  is very ample for  $n \geq 3$ . When n = 3 we obtain a tri-canonical embedding of stable curves to  $\mathbb{P}^{5g-6}$  with Hilbert polynomial P(m) = (6m-1)(g-1).

To see the third property observe that every irreducible component E of a stable curve C either has arithmetic genus 2 or more, or has arithmetic genus one but meets the other components in at least one point, or has arithmetic genus 0 and meets the other components in at least three points. Since  $\omega_{C/k} \otimes \mathcal{O}_E$  is isomorphic to  $\omega_{E/k}(\sum_i Q_i)$  where  $Q_i$  are the points where E meets the rest of the curve. Since this sheaf has positive degree it is ample on each component E of C, hence it is ample.  $\omega_{E/k}(\sum_i Q_i)$  has positive degree on each component, hence  $\omega_{C/k}^{1-n} \otimes \mathcal{O}_E$  has no sections for any  $n \geq 2$ . By Serre duality, it follows that  $H^1(C, \omega_{C/k}^{\otimes n}) = 0$ . To show that when  $n \geq 3$ ,  $\omega_{C/k}^{\otimes n}$  is very ample, it suffices to check that  $\omega_{C/k}^{\otimes n}$  separates points and tangents.

**Exercise 3.1.** Check that when  $n \geq 3$ ,  $\omega_{C/k}^{\otimes n}$  separates points and tangents.

#### 4. Stable reduction

Stable reduction was originally proved by Deligne and Mumford using the existence of stable reduction for abelian varieties [DM]. [HM] Chapter 3 Section C contains a beautiful account which we will summarize below.

The main theorem is the following:

**Theorem 4.1** (Stable reduction). Let B be the spectrum of a DVR with function field K. Let  $X \to B$  be a family of curves with n sections  $\sigma_1, \ldots, \sigma_n$  such that the restriction  $X_K \to Spec\ K$  is an n-pointed stable curve. Then there exists a finite field extension L/K and a unique stable family  $\tilde{X} \to B \times_K L$  with sections  $\tilde{\sigma}_1, \ldots, \tilde{\sigma}_n$  such that the restriction to  $Spec\ L$  is isomorphic to  $X_K \times_K L$ .

One can algorithmically carry out stable reduction (at least in characteristic zero). Since stable reduction is an essential tool in algebraic geometry we begin by giving some examples. We will then sketch the proof.

**Example 4.2.** Fix a smooth curve C of genus  $g \geq 2$ . Let  $p \in C$  be a fixed point and let q be a varying point. More precisely, we have the family  $C \times C \to C$  with two sections  $\sigma_p : C \to C \times C$  mapping a point q to (q,p) and  $\sigma_q : C \to C \times C$  mapping q to (q,q). All the fibers are stable except when p=q. To obtain a stable family, we blow up  $C \times C$  at (p,p). The resulting picture looks as follows (see Figure 2):

There is an algorithm that produces the stable reduction in characteristic zero. This algorithm is worth knowing because the explicit calculation of the stable limit often has applications to geometric problems.

**Step 1.** Resolve the singularities of the total space of the family. The result of this step is a smooth surface X mapping to our initial surface. Moreover, we can assume that the support of the central fiber is a normal-crossings divisor.

**Step 2.** After Step 1 at every point of the central fiber the pull-back of the uniformizer may be expressed as  $x^a$  for some a > 0 at a smooth point or  $x^a y^b$  for

FIGURE 2. Stable reduction when two marked points collide.

a pair a, b > 0 at a node. Make a base change of order p for some prime dividing the multiplicity of a multiple component of the fiber.

# **Step 3.** Normalize the resulting surface.

Suppose the central fiber was of the form  $\sum_i n_i C_i$  The effect of doing steps 2 and 3 is to take a branched cover of the surface X branched along the reduction of the divisor forming the central fiber modulo p. Repeat steps 2 and 3 until all the components occurring in the central fiber appear with multiplicity 1.

Step 4. Contract the rational components of the central fiber that are not stable.

Sketch of proof of Theorem 4.1. We will assume that n=0 and then make some remarks about how to modify the statements here to obtain the general case. Let R be a DVR with uniformizer z. Let  $\eta \in B = Spec\ R$  be the generic point. We are assuming that our family  $X_{\eta}$  is a stable curve of genus g.

Consider regular, proper B-schemes that extend  $X_{\eta}$ . By results of Abhyankar [Ab] about resolutions of surface singularities there exists a unique relatively minimal model of  $X_{\eta}$ . Consider the completion of the local ring at a node of the special fiber. This ring is isomorphic to  $R[[x,t]]/(xy-z^n)$  for some integer  $n \geq 1$ . This ring is not regular for n > 1. We can desingularize it in a sequence of  $\lfloor n/2 \rfloor$  blow-ups. Over the node we get a sequence of -2-curves.

Let X be a proper, flat regular surface extending  $X_{\eta}$ . Let  $C_i$ , i = 1, ..., n, be the components of the special fiber. Suppose they occur with multiplicity  $r_i$ . Recall the following basic facts about the components of the special fiber

- (1) The special fiber C is connected and the multiplicities  $r_i > 0$  for all i.
- (2)  $C_i \cdot C_j \geq 0$  for all  $i \neq j$  and  $C_i \cdot C = 0$  for all i.
- (3) If K is the canonical class, then the arithmetic genus of  $C_i$  is given by the genus formula as

$$1 + \frac{C_i^2 + C_i \cdot K}{2}.$$

(4) The intersection matrix  $C_i \cdot C_j$  is a negative definite symmetric matrix. The only linear combinations  $Z = \sum a_i C_i$  with the property that  $Z^2 = 0$  are rational multiples of C.

One can divide the components  $C_i$  of the special fiber into the following categories


**Example 4.3.** Suppose we have a general pencil of smooth curves of genus g in  $\mathbb{P}^2$  specializing to a curve with an ordinary m-fold point. We may write down the equation of such a family as F + tG where G is the equation defining a general curve of genus g and F locally has the form

$$\prod_{i=1}^{m} (y - a_i x) + \text{h. o. t.}$$

with distinct  $a_i$ . To perform stable reduction we blow-up the m-fold point. In the resulting surface the proper transform C of the central fiber is smooth of genus g - m(m-1)/2, but the exceptional divisor is a  $\mathbb{P}^1$  that meets C in m points and occurs with multiplicity m. We make a base change of order m. We get an m-fold cover of this  $\mathbb{P}^1$  totally ramified at the m points of intersection with C. By the Riemann-Hurwitz formula this is a genus m(m-3)/2+1. The stable limit then is as shown in the figure.

**Exercise 4.4.** Suppose  $C_t$  is a general pencil of smooth genus g plane curves acquiring an ordinary cusp (a singularity whose local equation is given by  $y^2 = x^3$ ). Describe the stable limit of this family of curves.

Exercise 4.5. Read and do the exercises in Chapter 3 Section C of [HM].

#### 5. Deligne-Mumford Stacks

In this section for completeness I will give you the definition of Deligne-Mumford stacks. I will summarize a few basic results and definitions. Much better accounts exist in [DM], [Ed] and [LM-B]. See also [Fan].

Let S be the category of schemes over a scheme S. A category T over S is a category together with a functor  $p: T \to S$ .

**Definition 5.1** (Groupoid). A category ((T, p) over S is a groupoid if the following two conditions hold

- (1) If  $f: B' \to B$  is a morphism in  $\mathcal{S}$  and C is an object in T lying over B, then there exists an object C' over B' and a morphism  $\phi: C' \to C$  such that  $p(\phi) = f$ .
- (2) Let C, C', C'' be objects in T lying over the objects B, B', B'' in S, respectively. If  $\phi: C' \to C$  and  $\psi: C'' \to C$  are morphisms in T and  $f: B' \to B''$  is a morphism in S satisfying  $p(\psi) \circ f = p(\phi)$ , then there is a unique morphism  $\tau: C' \to C''$  such that  $\psi \circ \tau = \phi$  and  $p(\tau) = f$ .

**Example 5.2.** Recall that a Deligne-Mumford stable curve (or simply a stable curve) of genus  $g \geq 2$  over a scheme S is a proper, flat family  $\pi: C \to S$  whose geometric fibers are reduced, connected, one dimensional schemes  $C_s$  satisfying the following properties:

- (1) The only singularities of  $C_s$  are ordinary double points.
- (2) A non-singular rational component of  $C_s$  meets the other components in at least three points.
- (3)  $C_s$  has arithmetic genus g—equivalently  $h^1(\mathcal{O}_{C_s}) = g$ .

We can define a groupoid  $\overline{\mathcal{M}}_g$  of Deligne-Mumford stable curves of genus g over schemes over  $Spec \mathbb{Z}$  as follows: The sections of  $\overline{\mathcal{M}}_g$  over a scheme X are families

of stable curves  $C \to X$ . A morphism between  $C' \to X'$  and  $C \to X$  is a fiber diagram

$$C' \longrightarrow C$$

$$\downarrow \qquad \qquad \downarrow$$

$$X' \longrightarrow X$$

which induces an isomorphism  $C' \cong X' \times_X C$ .

 $\overline{\mathcal{M}}_g$  is a groupoid and it is the main example that we are interested in.

For the sake of future constructions and definitions it is important to keep in mind the examples of two more groupoids.

**Example 5.3.** Any contravariant functor  $F: \mathcal{S} \to \{\text{sets}\}$  from schemes to sets gives rise to a groupoid (usually also called F by abuse of notation). The objects of the groupoid F are pairs  $(X,\alpha)$  where X is a scheme and  $\alpha$  is an element of the set F(X). A morphism between  $(X,\alpha)$  and  $(Y,\beta)$  is a morphism  $f: X \to Y$  such that  $F(f)(\beta) = \alpha$ . In particular, this construction allows us to view schemes as groupoids. To a scheme X we can associate its functor of points  $\operatorname{Hom}(*,X)$ . Since this is a contravariant functor from schemes to sets, to a scheme X we can also associate a groupoid X. The distinction between a scheme X and the associated groupoid is often blurred.

**Example 5.4.** Since the construction of many moduli spaces involves taking the quotient of a parameter space (such as a component of a Hilbert scheme) by a group action, the groupoid [X/G] is important. Let X be a scheme and G a group scheme acting on X. The sections of [X/G] over a scheme Y are principal G-bundles  $E \to Y$  together with a G-equivariant map  $E \to X$ . A morphism between two such principal G-bundles is a pull-back diagram.

**Exercise 5.5.** There is a relation between the previous two examples. Show that if the action of G on X is free and a quotient scheme X/G exists, then then there is an equivalence of categories between [X/G] and the groupoid associated to the scheme X/G.

Let (T,p) be a groupoid. For any two objects X and Y in the fiber of T over a scheme B, we can associate a functor  $Isom_B(X,Y)$ . This functor associates to any morphism  $f: B' \to B$ , the set of isomorphisms in T(B') between  $f^*(X)$  and  $f^*(Y)$ .

In the case of Deligne-Mumford stable curves, given any two stable curves C and C',  $Isom_X(C,C')$  associates to any morphism  $f:Y\to X$  the set of isomorphisms between  $f^*(C)$  and  $f^*(C')$ . Recall that C and C' are both canonically polarized by  $\omega_{C/X}$  and  $\omega_{C'/X}$ , respectively. Moreover, the formation of the relative dualizing sheaf commutes with base change. Consequently, any isomorphism satisfies  $f^*(\omega_{C'/X}) = \omega_{C/X}$ . Hence, all isomorphisms are isomorphisms between polarized schemes. It follows by the existence of the Hilbert scheme, that  $Isom_X(C,C')$  is represented by a scheme quasi-projective over X.

**Definition 5.6** (Stack). A groupoid (T, p) over S is a stack if

(1)  $Isom_B(X,Y)$  is a sheaf in the étale topology for all B,X and Y;

(2) If  $\{B_i \to B\}$  is a covering of B in the étale topology, and  $X_i$  are a collection of objects in  $T(B_i)$  with isomorphisms

$$\phi_{i,j}: X_{j|B_i \times_B B_i} \to X_{i|B_i \times_B B_i}$$

in  $T(B_i \times_B B_j)$  satisfying the cocycle condition, then there exists an object  $X \in T(B)$  with isomorphisms  $X_{|B_i} \to X_i$  inducing the isomorphisms  $\phi_{i,j}$ .

**Example 5.7.** The groupoid [X/G] defined in Example 5.4 is a stack. Let e, e' be two objects in [X/G](Y) corresponding to two principal G-bundles  $E, E' \to Y$  with G-equivariant maps f, f' to X, respectively.  $Isom_Y(e, e')$  is empty unless E = E' and f = f'. In the latter case the isomorphisms correspond to the subgroup of G that stabilizes the map f. Since the functor that associates to a G-equivariant map its stabilizer is representable, condition (1) follows. Condition (2) also holds for principal G-bundles.

Let  $P_{g,n}(m)$  be the Hilbert polynomial (2nm-1)(g-1), the Hilbert polynomial of an n-canonically embedded stable curve. Set N=n(2g-2)-g. Let  $\overline{H}_{g,n}$  the subscheme of the Hilbert scheme  $Hilb_{(2nm-1)(g-1)}(\mathbb{P}^N)$  parameterizing n-canonically embedded stable curves. Below we will show that there is an equivalence of categories between  $\overline{\mathcal{M}}_g$  and  $[\overline{H}_{g,n}/\mathbb{P}GL(N+1)]$  where the action of  $\mathbb{P}GL(N+1)$  on the Hilbert scheme is the one induced by its usual action on  $\mathbb{P}^N$ . In particular, it follows from the previous example that  $\overline{\mathcal{M}}_g$  is a stack.

Recall in example 5.3 we associated to a scheme a groupoid. Observe that this groupoid is a stack. The second condition is satisfied because the functor of points of a scheme is represented by the scheme itself. In particular, we can view each scheme as a stack. In the litterature stacks that arise this way are usually referred to as schemes meaning that the stack associated to the scheme. We will also indulge in this habit.

A morphism of stacks  $f: T \to T'$  is representable if for any map of a scheme  $X \to T'$  the fiber product  $T \times_{T'} X$  is represented by a scheme. We can transport the notions of morphisms of schemes to representable morphisms of stacks in the following way: We say that a representable morphism  $f: T \to T'$  has a property P (such as quasi-compact, separated, proper, etc.) if for all maps of a scheme  $X \to T'$ , the corresponding morphism of schemes  $T \times_{T'} X \to X$  has the property P.

**Definition 5.8** (Deligne-Mumford stack). A stack is called a Deligne-Mumford stack if

- (1) The diagonal  $\Delta_X: T \to T \times_{\mathcal{S}} T$  is representable, quasi-compact and separated:
- (2) There exists a scheme U and an étale, surjective morphism  $U \to T$ .

Morphisms as in condition (2) are called étale atlases.

The following is a useful theorem for verifying that a stack is a Deligne-Mumford stack (see [DM] Theorem 4.21, or [Ed] Theorem 2.1).

**Theorem 5.9.** Let T be a quasi-separated stack over a Noetherian scheme S. Suppose that

- (1) The diagonal is representable and unramified,
- (2) There exists a scheme U of finite type over S and a smooth, surjective S-morphism  $U \to F$ .

The F is a Deligne-Mumford stack.

A consequence of this theorem is that if X/S is a Noetherian scheme of finite type and G/S is a smooth group scheme acting on X with with finite and reduced stabilizers, then [X/G] is a Deligne-Mumford stack. The conditions on the stabilizers (that they are finite and reduced) guarantee that  $Isom_B(E, E)$  are unramified. It follows that the diagonal is unramified. The second condition in the theorem is satisfied by the map  $X \to [X/G]$ .

Given the equivalence of categories between  $\overline{\mathcal{M}}_g$  and  $[\overline{H}_{g,n}/\mathbb{P}GL(N+1)]$  it follows that  $\overline{\mathcal{M}}_g$  is a Deligne-Mumford stack because the action of  $\mathbb{P}GL(N+1)$  on  $\overline{H}_{g,n}$  has finite and reduced stabilizers.

Just like in the case of schemes there are valuative criteria for separatedness and properness. We now state these and observe that  $\overline{\mathcal{M}}_g$  is a proper Deligne-Mumford stack. For the following two theorems let  $f:T\to S$  be a morphism of finite type from a Deligne-Mumford stack to a noetherian scheme S

**Theorem 5.10** (The valuative criterion for separatedness). The morphism f is separated if and only if for any complete discrete valuation ring with algebraically closed residue field and any commutative diagram

any isomorphism between the restrictions of  $g_1$  and  $g_2$  to the generic point of Spec R can be extended to an isomorphism of  $g_1$  and  $g_2$ .

**Theorem 5.11** (The valuative criterion of properness). If f is separated, then f is proper if and only if, for any discrete valuation ring R with field of fractions K and any map  $Spec\ R \to T$  which lifts over  $Spec\ K$  to a map to T, there is a finite extension K' of K such that the lift extends to all of  $Spec\ R'$  where R' is the integral closure of R in K'.

The stable reduction theorem together with the valuative criterion of properness implies that  $\overline{\mathcal{M}}_q$  is a proper Deligne-Mumford stack.

One approach for constructing the coarse moduli scheme (which we cannot complete at present because we have not yet developed the theory of divisors on the moduli stack) is to first construct the moduli space as an algebraic space, then exhibit an ample divisor on the coarse moduli algebraic space. This approach has been applied successfully to represent many moduli functors. The first step is achieved by a corollary of a general theorem of Keel and Mori [KM] (see also [Li] for a nice treatment).

**Theorem 5.12.** Any separated Deligne-Mumford stack of finite type has a coarse moduli space in the category of algebraic spaces.

Once we study the ample cone in the Picard group of the moduli stack, we will be able to deduce the existence of a coarse moduli scheme from the previous theorem. The second approach to the construction of the coarse moduli scheme is to directly take the G.I.T. quotient of the Hilbert scheme parameterizing n-canonically embedded stable curves. The advantage of the first approach is that it does away

with delicate calculations describing the stable and semi-stable loci of this action. The first approach may also be used to construct moduli spaces in other situations. The advantage of the second approach is that it produces a projective coarse moduli scheme at once.

#### 6. The GIT construction of the moduli space

Good references for this section are [HM] Chapter 4, [Mum3], [FKM] and [Ne]. Explaining the GIT construction in detail would take us too far afield. Instead we will briefly sketch the main ideas and refer you to the literature.

6.1. **Basics about G.I.T..** An algebraic group G is a group together with the structure of an algebraic variety such that the multiplication and inverse maps are morphisms of varieties. An action of an algebraic group G on a variety X is a morphism  $f: G \times X \to X$  such that f(gg', x) = f(g, f(g', x)) and f(e, x) = x, where e is the identity of the group. The stabilizer of a point  $x \in X$  is the closed subgroup of G fixing x. The orbit of a point x under G is the image of f restricted to  $G \times \{x\}$ .

For our purposes we can always restrict attention to SL(n), GL(n) or  $\mathbb{P}GL(n)$ . An algebraic group which is isomorphic to a closed subgroup of GL(n) is called a linear algebraic group. A group is called geometrically reductive if for every linear action of G on  $k^n$  and every non-zero invariant point  $v \in k^n$ , there exists an invariant homogeneous polynomial that does not vanish on v. The group is called linearly reductive if the homogeneous polynomial may be taken to have degree one. Finally a group is called reductive if the maximal connected normal solvable subgroup is isomorphic to a direct product of copies of  $k^*$ . In characteristic zero these concepts coincide. In characteristic p > 0 a threorem of Haboush guarantees that every reductive group is geometrically reductive.

The question is to obtain a quotient of a variety under the action of a reductive group.

**Lemma 6.1.** Let G be a geometrically reductive group acting on an affine variety X. Let  $W_1$  and  $W_2$  be two disjoint invariant closed orbits. Then there exists an invariant polynomial  $f \in A(X)^G$  such that  $f(W_1) = 0$  and  $f(W_2) = 1$ .

Proof. Pick any  $h \in A(X)$  such that  $h(W_1) = 0$  and  $h(W_2) = 1$ . Consider the subspace spanned by  $h^g$  for  $g \in G$ . This is a finite dimensional subspace. To see this consider the function H(g,x) = h(gx) in  $A(G \times X) \cong A(G) \otimes A(X)$ . We can write H(g,x) as a finite sum  $\sum_i F_i \otimes H_i$  in  $A(G) \otimes A(X)$  of the generators of A(G) and A(X). Hence the subspace spanned by  $h^g$  for  $g \in G$  is contained in the subspace spanned by the  $H_i$ . Pick a basis for this subspace  $h_1, \ldots, h_n$ . We obtain a rational representation of G on this subspace, hence a linear action on  $k^n$  making the morphism  $\pi: X \to k^n$  given by  $\pi(x) = (h_1(x), \ldots, h_n(x))$  into a G-morphism. Since G is geometrically reductive there is an invariant polynomial f that has the value zero on  $\pi(W_1)$  and the value 1 on  $\pi(W_2)$ .  $f \circ \pi$  is the desired polynomial.  $\square$ 

The main theorem for quotients of reductive group actions on affine varieties is the following:

**Theorem 6.2.** Let G be a reductive group acting on an affine variety X. Then there exists a quotient affine variety Y and a G-invariant, surjective morphism  $\phi: X \to Y$  such that

(1) For any open set  $U \subset Y$ , the ring homomorphism

$$\phi^* : A(U) \to A(\phi^{-1}(U))$$

is an isomorphism of A(U) with  $A(\phi^{-1}(U))^G$ .

- (2) If  $W \subset X$  is a closed invariant subset, then  $\phi(W)$  is closed in Y.
- (3) If  $W_1$  and  $W_2$  are disjoint closed invariant sets, then their images under  $\phi$  are disjoint.

*Proof.* The main technical results are provided by a theorem of Haboush and a theorem of Nagata.

**Theorem 6.3** (Haboush). Any reductive group G is geometrically reductive.

**Theorem 6.4** (Nagata). Let G be a geometrically reductive group acting rationally on a finitely generated k-algebra R. Then the ring of invariants  $R^G$  is finitely generated.

In view of these theorems  $A(X)^G$  is finitely generated. Hence we can let  $Y = Spec\ A(X)^G$ . The inclusion of  $A(X)^G \to A(X)$  induces a morphism  $\phi: X \to Y$ . The claimed properties are easy to check for  $\phi$ .

**Remark 6.5.** The following are straightforward observations:

- (1) For any open subset  $U \subset Y$ ,  $(U, \phi)$  is a categorical quotient of  $\phi^{-1}(U)$  by G.
- (2) The images of two points in X coincide if and only if the orbit closures of these two points intersect. Consequently, Y will be an orbit space if and only if the orbits of the G action on X are closed.

Remark 6.6. We will not prove Haboush's theorem here. The interested reader may consult the original paper [Hab]. Over the complex numbers reductive, geometrically reductive and linearly reductive coincide. This follows from the fact that any finite dimensional representation is decomposible to irreducible representations. Projection to the one-dimensional invariant subspace produces the desired invariant linear functional.

We now sketch the proof of Nagata's theorem. Since R is a finitely generated k-algebra, we can pick generators  $f_1, dots, f_n$  that generate R. We can also assume that the subspace spanned by the  $f_i$  is G-invariant. (If not, we can replace it by a minimal G-invariant subspace, which is finite-dimensional by the argument in Lemma 6.1.) We thus obtain a linear G action on the subspace spanned by  $f_i$  by setting

$$f_i^g = \sum_j \alpha_{i,j}(g) f_j.$$

Let  $S = k[X_1, ..., X_n]$ . There is an action of G on S by setting

$$X_i^g = \sum_j \alpha_{i,j}(g) X_j.$$

There is a k-algebra homomorphism from S to R sending  $X_i$  to  $f_i$  that is compatible with the G actions. We are thus reduced to proving Nagata's theorem in the case

when G acts on S preserving degree,  $Q \subset S$  is a G-invariant ideal with the induced action on R = S/Q. Under these assumptions we would like to see  $R^G$  is finitely generated.

Suppose not. Since S is Noetherian, there exists an ideal Q maximal among those that are G-invariant such that  $R^G$  where R = S/Q is not finitely generated. Then if  $J \neq 0$  is a G-invariant homogeneous ideal in R, then  $(R/J)^G$  is finitely generated. Suppose first there is a homogeneous ideal Q with the desired properties.

I claim that  $(R/J)^G$  is integral over  $R^G/(J\cap R^G)$ . Suppose  $f\in (R/J)^G$ . Pick  $h\in R$  such that the image of h in R/J is f. We would like to find  $h_0\in R^G$  such that  $(h)^t-h_0$  for some positive integer t is in  $R^G$ . Look at the finite-dimensional, G-invariant subsapce M generated by  $h^g$ . [Unfortunately, there is potential for confusion between  $h^g$  and  $(h)^t$ . The first denotes the g-translate of h, the second denotes the t-th power of h. To distinguish between these two, we will put parentheses around h in the latter case.] Since J is invariant,  $h^g-h$  is in J for every g. We conclude that  $M\cap J$  has codimension 1 in M. We can write every element in M uniquely as ah+h' where  $a\in k$  and  $h'\in M\cap J$ . Sending ah+h' to a defines a G-invariant linear functional l on M.

There is an action of G also on  $M^*$ . If we let  $h, j_2, \ldots, j_n$  be a basis of M where  $j_i \in M \cap J$ , we can identify  $M^*$  with  $k^r$  in terms of the dual basis. The linear functional l corresponds to the vector  $(1,0,\ldots,0)$ . Since G is geometrically reductive, there exists an invariant homogeneous polynomial  $F \in k[X_1,\ldots,X_n]$  of degree  $t \geq 1$  such that the coefficient of  $X_1^t$  does not vanish. Consider the morphism  $k[X_1,\ldots,X_n]$  sending  $X_1$  to h and  $X_i$  to  $j_i$  for i>1. If  $h_0$  is the image of F,  $h^t-h_0$  belongs to J. We conclude that  $(R/J)^G$  is integral over  $R^G/(J \cap R^G)$ .

If A is a finitely generated k-algebra which is integral over a subalgebra B, then B is finitely generated. Hence in our case,  $R^G/(J\cap R^G)$  is finitely generated. In fact,  $(R/J)^G$  is a finite  $R^G/(J\cap R^G)$ -module.

Choose a non-zero homogeneous element f of  $R^G$  of degree at least one. If f is not a zero-divisor,  $fR \cap R^G = fR^G$ . Since  $R^G/fR^G$  is finitely generated,  $(R^G/fR^G)_+$  is finitely generated as an ideal. Hence  $R_+^G$  is finitely generated as an ideal in  $R^G$ . Hence  $R^G$  is a finitely generated k-algebra.

**Exercise 6.7.** Modify the last paragraph of the proof in case f is a zero-divisor. Hint: Consider the homogeneous ideal I of elements of R that annihilate f. Since  $R^G/(fR \cap R^G)$  and  $R^G/I \cap R^G$  are both finitely generated, there is a finitely generated subalgebra of  $R^G$  that surjects onto both these algebras

In order to handle the non-homogeneous case, we may assume that  $R^G$  is a domain. By the homogeneous case  $S^G$  is finitely generated.  $R^G$  is integral over  $S^G/Q\cap S^G$ . It suffices to show that the field of fractions of  $R^G$  is a finitely generated extension of R. Let T be the set of non-zero divisors of R. Form the ring of fractions of R with respect to T. Let m be the maximal ideal. The field of fractions of  $R^G$  may be identified with a subfield of  $T^{-1}R/m$ . Since  $T^{-1}R/m$  is the field of fractions of the finitely generated R-algebra  $R/m \cap R$ , this follows.

**Example 6.8.** Everyone's favorite example is the action of GL(n) on the space of  $n \times n$  matrices  $M_n$  by conjugation. The space of matrices is isomorphic to affine space  $\mathbb{A}^{n^2}$ . Hence, the coordinate ring is  $k[a_{i,j}]$ ,  $1 \le i, j \le n$ . Any conjugacy class

has a representative in Jordan canonical form which is unique upto a permutation of the Jordan blocks. Since the set of eigenvalues of a matrix is invariant under conjugation, we see that the elementary symmetric polynomials of the eigenvalues, i.e. the coefficients of the characteristic polynomial, are invariant under the action. Conversely, suppose that a polynomial is invariant under conjugation. If the eigenvalues are distinct, we can diagonalize the matrix by connjugation. Hence the polynomial must be a symmetric function of the eigenvalues. If the eigenvalues are repeated, the diagonal matrix is in the closure of the orbits with non-trivial Jordan blocks. We conclude that any invariant polynomial is a symmetric polynomial of the eigenvalues. Since the elementary symmetric polynomials generate the ring of symmetric polynomials, we conclude that the ring of invariant functions is generated by the coefficients of the characteristic polynomial.

Now we would like to extend the discussion from actions of reductive groups on affine varieties to actions on projective varieties. Suppose we have a group acting on a projective variety  $X \subset \mathbb{P}^n$ . A linearization of the action of G is a linear action on  $k^{n+1}$  which induces the given action on X. More generally, let X be a variety, G a group acting on it and L a line bundle on X. A linearization of the action of G with respect to L is a linear action on L that induces the action of G on X.

**Definition 6.9.** A point  $x \in X$  is called semi-stable if there exists an invariant homogeneous polynomial that does not vanish on x. A point  $x \in X$  is called stable if there exists an invariant polynomial f that does not vanish on x, the action of G on  $X_f$  is closed and the dimension of the orbit of x is equal to the dimension of G. These depend not only on the action, but the chosen linearization. Denote the locus of semi-stable points by  $X^{ss}$  and the locus of stable points by  $X^{s}$ .

**Remark 6.10.** Note that the semi-stable points are precisely those that do not contain 0 in the closure of their orbits. Both  $X^{ss}$  and  $X^s$  are clearly open (possibly empty) in X.

The main theorem of G.I.T. is the existence of a good quotient of the semi-stable locus whose restriction to the stable locus is a geometric quotient. We will call a quotient a good quotient if it satisfies the conditions of Theorem 6.2. We will call a good quotient that is also an orbit space a geometric quotient.

**Theorem 6.11.** Let X be a projective variety in  $\mathbb{P}^n$ . Then for every linear action of a reductive group G on X

- (1) There exists a good quotient  $(Y, \phi)$  of  $X^{ss}$  by G and Y is projective.
- (2) There exists an open subset  $Y^s$  of Y such that  $\phi^{-1}(Y^s) = X^s$  and  $(Y^s, \phi)$  is a geometric quotient of  $X^s$ .

In view of this theorem it is important to determine the stable and semi-stable loci for reductive group actions on projective varieties. Unfortunately, this in general is a very difficult problem. There is one instance where stability and semi-stability is easy to determine.

**Definition 6.12.** A one-parameter subgroup is a homomorphism  $\lambda : \mathbb{G}_m \to G$ .

Any action of  $k^*$  on  $k^{n+1}$  can be diagonalized. Hence, there exists a basis  $e_0, \ldots, e_n$  such that the action of the one-parameter subgroup  $\lambda$  is given by  $\lambda(t)e_i =$ 

 $t^{r_i}e_i$  for some integers  $r_i$ . If  $\hat{x} = \sum x_ie_i$ , then

$$\lambda(t)\hat{x} = \sum_{i} t^{r_i} x_i e_i.$$

Define

$$\mu(x,\lambda) = \max\{-r_i \mid x_i \neq 0 \}.$$

**Theorem 6.13** (The Hilbert-Mumford criterion of stability). Let G be a reductive group acting linearly on a projective variety  $X \subset \mathbb{P}^n$ . Then:

- (1) x is semi-stable if and only if for every one-parameter subgroup  $\lambda$  of G  $\mu(x,\lambda) \geq 0$ .
- (2) x is stable if and only if for every one-parameter subgroup  $\lambda$  of G  $\mu(x,\lambda) > 0$ .

*Proof.* The challenging part of the theorem is to produce a one-parameter subgroup that has the wrong  $\mu$  invariant if x is not semi-stable. We will sketch Hilbert's proof for the case G = SL(m). The general case follows the same general line of argument (see §2.1 [FKM]).

Let K be the field of fractions of R = k[[T]]. If x is not stable, then the morphism  $G \to k^{n+1}$  given by sending g to  $g\hat{x}$  where  $\hat{x}$  is a lift of x is not proper. By the valuative criterion of properness, there exists  $\bar{g} \in SL(m,K)$  such that  $\bar{g}\hat{x} \in R^{n+1}$ , but  $\bar{g} \notin SL(m,R)$ . We can, however, clear denominators so that  $T^r\bar{g} \in SL(m,R)$  for some r. The ring R is a P.I.D., hence we can decompose  $\bar{g} = \bar{g_1}d\bar{g_2}$  where  $g_1$  and  $g_2$  are in SL(m,R) and d is a diagonal matrix consisting of entries  $T^{w_1},\ldots,T^{w_m}$  for some integers  $w_i$  whose sum is zero (since the resulting matrix has to be in SL(m,K). This is the point in the proof where we are using that G = SL(m). To prove the theorem for general groups one needs to use a theorem of Iwahori which asserts that the double coset in  $G(R)\backslash G(K)/G(R)$  for a reductive group can be represented by a one-parameter subgroup.

Let  $g_2$  be the matrix obtained by setting T=0 in  $\bar{g}_2$ . The de-stabilizing one-parameter subgroup is defined by

$$\lambda(t) = g_2^{-1} \operatorname{diag}(t^{w_1}, \dots, t^{w_m}) g_2.$$

Diagonalize the action of  $\lambda$  on  $k^{n+1}$  with respect to a basis  $e_0, \ldots, e_n$  as above. We would like to show that if  $\hat{x}_i \neq 0$ , then the weight  $r_i$  of the action on  $e_i$  is non-negative. We can also consider the basis  $e_0, \ldots, e_n$  as a basis of  $K^{n+1}$ . Then  $g_2^{-1}dg_2e_i = T^{r_i}e_i$ . In particular,

$$g_2^{-1}\bar{g_1}^{-1}\bar{g} = g_2^{-1}\bar{g_1}^{-1}\bar{g_1}d\bar{g_2} = (g_2^{-1}dg_2)g_2^{-1}\bar{g_2}.$$

Therefore, the *i*-th component of  $g_2^{-1}\bar{g_1}^{-1}\bar{g}\hat{x}$  is  $T^{r_i}$  times the *i*-th component of  $g_2^{-1}\bar{g_2}\hat{x}$ . Consequently, the *i*-th component of  $g_2^{-1}\bar{g_2}\hat{x}$  is in  $T^{-r_i}R$ . Since it is also in R, we conclude that  $r_i \geq 0$ .

Exercise 6.14. Modify the previous argument to obtain the theorem for the semi-stable case.

**Example 6.15** (Points on  $\mathbb{P}^1$ ). Consider the action of SL(2) on the homogeneous polynomials of degree d in two variables. Let  $\lambda$  be a one-parameter subgroup of SL(2). If we diagonalize the action of  $\lambda$  on  $k^2$  by  $diag(t^a, t^{-a})$  in coordinates (x, y), then the monomials  $x^iy^{d-i}$  diagonalizes the action of  $\lambda$  on homogeneous

polynomials of degree d. The weight of the action on  $x^iy^{d-i}$  is a(2i-d). If we want the weight to be negative, then the coefficient of one monomial  $x^iy^{d-i}$  with 2i-d<0 has to be non-zero. This means that a homogeneous polynomial is stable if and only if it does not have any zeros with multiplicity  $\geq d/2$ . Similarly, a homogeneous polynomial is semi-stable if and only if it does not have any zeros with multiplicity > d/2.

Example 6.16 (Cubic plane curves). Consider the action of SL(3) on the homogeneous polynomials of degree 3 in three variables. If we diagonalize the action of a one-parameter subgroup  $\lambda$  in terms of the coordinates  $x_1, x_2, x_3$  such that  $\lambda(t)x_i = t^{w_i}x_i$ , then the basis given by monomials  $x_1^ix_2^jx_3^{3-i-j}$  diagonalizes the action of  $\lambda$  on degree 3 homogeneous polynomials. The weight of the action on  $x_1^ix_2^jx_3^{3-i-j}$  is given by  $iw_1 + jw_2 + (3-i-j)w_3$ . We can visualize the one parameter subgroup in terms of barycentric coordinates. The one-parameter subgroups correspond in this picture to lines pivoted around the point (i,j,3-i-j)=(1,1,1). If we move the line without crossing any integral points on the triangle, we do not change the conditions for stability. Also the picture is invariant under the symmetries of the triangle. Analyzing the coefficients we see that a cubic is stable if and only if it is smooth. Similarly a cubic is semi-stable if and only if it has ordinary double points. Note that the G.I.T. quotient of the stable locus in this case constructs the j-line.

**Exercise 6.17.** Try to generalize the previous example to the action of SL(3) on homogeneous polynomials of degree 4, 5, 6, ... In particular, describe what kinds of singularities are allowed on stable curves of degree 4, 5, 6...

6.2. The construction of  $\overline{M}_g$ . In view of Theorem 6.11 in order to construct  $\overline{M}_g$  we need to show that the N-canonically embedded Deligne-Mumford stable curves are stable points for the SL(n+1)-action on the Hilbert scheme and that they form a closed subset. The details of this verification are involved. You may find good accounts in [HM] and [Mum3].

We would like to apply the Hilbert-Mumford criterion to the action of SL(n+1) on  $Hilb_{P(m)}(\mathbb{P}^n)$ . Fix a one-parameter subgroup  $\lambda$  of SL(n+1). Suppose in terms of homogeneous coordinates  $x_i$  that diagonalize the action, the weights are  $w_0,\ldots,w_n$ . Of course, as usual we have that  $\sum_i w_i=0$ . Recall that we exhibited the Hilbert scheme as a subscheme of the Grassmannian  $G(P(m),H^0(\mathbb{P}^n,\mathcal{O}_{\mathbb{P}^n}(m)))$  for m greater than or equal to the regularity of all the ideal sheaves with Hilbert polynomial P. The Grassmannian has natural Plücker coordinates consisting of P(m)-element subsets of monomials in the  $x_i$  of degree m. This basis also diagonalizes the action of SL(n+1) on  $\bigwedge^{P(m)} H^0(\mathbb{P}^n, \mathcal{O}_{\mathbb{P}^n}(m))$ . The weight on the Plücker coordinate  $\{Y_{j_1},\ldots,Y_{j_{P(m)}}\}$  where  $Y_{j_i}=\prod_r x_r^{m_{j_i,r}}$  is given by

$$\sum_{i,r} w_r m_{j_i,r}.$$

The Hilbert-Mumford criterion for semi-stability then translates to the condition that for each one parameter subgroup, there should be a non-vanishing Plücker coordinate whose weight is non-positive.

We begin by showing that the m-th Hilbert points of smooth, non-degenerate curves embedded by a complete linear series of degree  $d \geq 2g$  are stable for the SL(n+1) action.

**Theorem 6.18** (Stability for smooth curves). Let C be a smooth curve of genus  $g \geq 2$  embedded in projective space  $\mathbb{P}^{d-g}$  by a complete linear system of degree d at least 2g. Then C is Hilbert stable. Moreover, there exists M such that for all  $m \geq M$ , the m-th Hilbert point of non-degenerate, smooth curves of degree d and genus g in  $\mathbb{P}^{d-g}$  is stable.

Sketch. The proof is an application of the Hilbert-Mumford criterion.

**Definition 6.19** (Potential stability). A connected curve C of degree d and genus q in  $\mathbb{P}^{d-g+1}$  is called potentially stable if

- (1) The embedded curve C is non-degenerate.
- (2) The abstract curve C is moduli semi-stable.
- (3) The linear series embedding C is complete and non-special (i.e. has  $h^1 = 0$ ).
- (4) If C' is a complete subcurve of C of arithmetic genus g' meeting the rest of the curve C in k points, then the following estimate holds

$$\left| \deg_{C'}(\mathcal{O}_C(1)) - \frac{d}{g-1}(g_{C'} - 1 + \frac{k}{2}) \right| \le \frac{k}{2}.$$

**Remark 6.20.** Observe that if C' is a smooth rational curve meeting the rest of the curve in exactly two points (k=2), then the term  $g_{C'}-1+k/2=0$ , hence the degree of C' has to be 1. In other words, C' is a line. By the same argument, if C' is a nodal tree of smooth rational curves meeting the rest of C in exactly two points, then C' is a smooth rational curve since the degree is at most one. Furthermore, C' cannot meet the rest of the curve in only one point.

Recall that  $\omega_{C|C'}$  is the dualizing sheaf  $\omega_{C'}$  twisted by the nodes connecting C' to C. Hence,  $\deg(\omega_{C|C'}) = 2g_{C'} - 2 + k$ . Condition (4) has the following alternative useful expression

$$\left| \deg C' - d \frac{\deg(\omega_{C|C'})}{\deg(\omega_C)} \right| \le \frac{k}{2}.$$

**Theorem 6.21** (Potential stability). Let  $g \geq 2$  and d > 9(g-1). Then there is an integer M depending only on d and g such that if  $m \geq M$  and  $C \in \mathbb{P}^{d-g}$  is a connected curve with semi-stable m-th Hilbert point, then C is potentially stable.

The proof of this theorem is quite lengthy even though the strategy is straightforward. We suppose C has a geometric property that violates potential stability. Under this assumption we construct a one-parameter subgroup that destabilizes the Hilbert point of C contradicting the assumption that the m-th Hilbert point of C was semi-stable.

We first assume Theorem 6.21 and deduce from it the existence of the coarse moduli space  $\overline{M}_g$ . Fix an integer  $r \geq 5$ . Consider r-canonically embedded stable curves. Since  $\omega_C^{\otimes r}$  is very ample for  $r \geq 3$ , every Deligne-Mumford stable curve has a representative in the Hilbert scheme  $\hat{H} = Hilb_{r(2g-2)+1-g}(\mathbb{P}^{r(2g-2)-g})$ . Now consider the subscheme H of  $\hat{H}$  subscheme of the Hilbert scheme parameterizing r-canonically embedded Deligne-Mumford stable curves. Let  $H^{ss}$  denote the intersection of H with the semi-stable locus of  $\hat{H}$ . Since  $r \geq 5$ , we have that the degree of the curves are at least 10(g-1) > 9(g-1). Therefore, the assumption of the Potential Stability Theorem is satisfied. We conclude that every semi-stable point of  $\hat{H}$  is potentially stable.

**Lemma 6.22.** The locus  $H^{ss}$  is closed in semi-stable locus of the Hilbert scheme  $\hat{H}^{ss}$ .

Proof. To show that  $H^{ss}$  is closed we need to show that the inclusion  $H^{ss} \to \hat{H}^{ss}$  is proper. By the valuative criterion of properness it suffices to check that given a map from the spectrum of a DVR to  $\hat{H}^{ss}$  whose generic point lies in  $H^{ss}$ , the closed point also lies in  $H^{ss}$ . Given such a map consider the universal curve  $C_R$  over Spec(R). There are two line bundles on  $C_R$ , the relative dualizing sheaf  $\omega_{C_R/R}$  and  $\mathcal{O}_{C_R}(1)$ . These two are isomorphic except possibly at the central fiber. To conclude the lemma we need to show that they also agree on the central fiber. Hence the two differ by  $\mathcal{O}_{C_R}(-\sum_i a_i C_i)$  where  $\sum_i a_i C_i$  is a linear combination of the central fiber. We need that  $a_i = 0$  for all i. We can assume that  $a_i \geq 0$  for all i with at least one  $a_i = 0$ . Let  $C_1'$  be the subcurve of the central fiber D where  $a_i > 0$  and  $C_2'$  be the subcurve of the central fiber D where  $a_i = 0$ . We see that all  $a_i = 0$  as follows. A local equation of  $\mathcal{O}_{C_R}(-\sum_i a_i C_i)$  is identically zero on every component of  $C_2'$  and on no component of  $C_1'$ . In particular, the local equation vanishes at the k points of intersection between  $C_1'$  and  $C_2'$ . We then have that

$$k \leq \deg_D(\mathcal{O}_{C_R}(-\sum_i a_i C_i) \leq \deg_D(\mathcal{O}_{C_R}(1)) - \frac{\deg_{C_2'}(\mathcal{O}_{C_R}(1)_{|C_2'})}{\deg_{C_2'}(\omega_{|C_2'})} \deg_D(\omega_{|C_2'}) \leq \frac{k}{2}.$$

**Lemma 6.23.** Every curve C whose Hilbert point lies in  $H^{ss}$  is Deligne-Mumford stable.

*Proof.* By the potential stability theorem C is semi-stable. In order to show that it is stable we need to check that there are no rational curves that intersect the rest of the curve in only two points. On a rational curve meeting the rest of C in two points, the degree of the dualizing sheaf of C is zero whereas  $\mathcal{O}_C(1)$  is very ample. Since these two coincide for points in  $H^{ss}$ , we conclude that C must be Deligne-Mumford stable.

**Lemma 6.24.** Every Deligne-Mumford stable curve of genus g has a model in  $H^{ss}$ .

Proof. Every moduli stable curve C is embedded in  $\mathbb{P}^{r(2g-2)-g}$  by its  $\omega_C^{\otimes r}$ . We need to show that the Hilbert point of C lies in  $H^{ss}$ . If C is smooth, we already know this by Theorem 6.18. To deduce it for singular Deligne-Mumford stable curves, we take a one-parameter deformation of C to a smooth curve of genus g over the spectrum of a DVR R. If we embed this curve r-canonically, we get a map from  $Spec\ R$  to the Hilbert scheme. The generic point lies in  $H^{ss}$ . Since the G.I.T. quotient of the Hilbert scheme  $\hat{H}^{ss}$  by the action of the special linear group is projective, after a base change we can extend the map to  $\hat{H}^{ss}$ . Since  $H^{ss}$  is closed, the image of the map lies in  $H^{ss}$ . Pulling back the universal curve we obtain a semi-stable reduction of a family of stable curves. By the uniqueness of semi-stable reduction this family has to agree with our original family. Since the curves  $H^{ss}$  are actually stable, the central fiber of both families have to be projectively equivalent. The lemma follows.

**Lemma 6.25.** Every curve whose Hilbert point lies in  $H^{ss}$  is Hilbert stable.

*Proof.* We need to show that every point in  $H^{ss}$  has closed orbit and the stabilizer of a point in  $H^{ss}$  is finite. Suppose the stabilizer is not finite, then the curve

C would have infinitely many automorphisms contradicting that Deligne-Mumford stable curves have only finitely many automorphisms. If the orbit is not closed, then the closure would contain a semi-stable orbit with positive dimensional stabilizer. Again we would obtain a contradiction.

# **Lemma 6.26.** The locus $H^{ss}$ is non-singular.

*Proof.* Recall that given a Deligne-Mumford stable curve C, there exists a formal scheme  $\tilde{C}$  proper and flat over  $Spec\ k[[t_1,\ldots,t_r]]$  where  $r=\dim\operatorname{Ext}^1(\Omega^1_C,\mathcal{O}_C)$  such that the special fiber is isomorphic to C. Moreover, for a stable curve the versal deformation is universal and algebrizable and the generic fiber is smooth.

Let  $[C] \in H^{ss}$  be a point. Let  $\tilde{C}$  be the universal formal deformation of C over  $B = Spec \ k[[t_1, \ldots, t_r]]$ . Set S be the formal completion of  $H^{ss}$  at [C]. By the universal property of the Hilbert scheme we get a map  $S \to H^{ss}$ . By the universal property there exists a unique morphism  $f: S \to B$  such that the pull-back of the universal curve is  $S \times_B \tilde{C}$ . The Lemma follows from the claim that  $f: S \to B$  is formally smooth.

One important aspect of the G.I.T. construction is that the projectivity of  $\overline{M}_g$  is immediate. Another important consequence is the irreducibility of the moduli space of curves over an algebraically closed field of any characteristic. Originally Deligne and Mumford developed the theory of Deligne-Mumford stacks to prove the irreducibility in all characteristics and for all genus in [DM].

**Theorem 6.27.** The moduli space  $\overline{M}_q$  is projective.

**Theorem 6.28.** The moduli space  $\overline{M}_g$  is irreducible (and reduced) over any algebraically closed field.

Proof. Soon we will see that the moduli space of curves in characteristic zero is irreducible. There are many ways of seeing this. We will use Teichmüller theory to construct  $M_g$  as the quotient of a bounded, contractible domain in  $\mathbb{C}^{3g-3}$ . Alternatively, one can exhibit every smooth curves as a branched cover of  $\mathbb{P}^1$ . When the number of branch points is large relative to the degree of the map, using the combinatorics of the symmetric group one may show that the space of branched covers of  $\mathbb{P}^1$  is irreducible. Suppose now that the characteristic of the field k is positive. Let R be a discrete valuation ring whose quotient field has characteristic zero and whose residue field is k. The construction outlined so far works over  $Spec\ R$ . Since the generic fiber of  $H_R^{ss}/\mathbb{P}GL \to Spec\ R$  is connected, by Zariski's connectedness theorem  $H_R^{ss}/\mathbb{P}GL \otimes k$  is connected. Since this is an orbit space  $H_k^{ss}$  is connected. Since it is smooth, it is reduced and irreducible. Consequently  $\overline{M}_g$  is also irreducible.  $\overline{M}_g$  is also reduced because the structure sheaf of the quotient is the sheaf of invariants of the structure sheaf of  $H^{ss}$ .

Finally we enumerate the steps that one carries out in order to prove the Potential Stability Theorem. We assume that a geometric condition violating potential stability occurs on a curve. We then produce a one-parameter subgroup destabilizing that point, hence showing that it is not a Hilbert stable point. Unfortunately the number of cases and calculations needed to give a complete proof is rather large. Since we will not use these techniques later in the course, we will just sketch a few sample cases. A complete proof can be found on pages 35-87 of [G].

**Claim 6.29.** The first claim is that if a curve C is Hilbert stable, then  $C_{red}$  is not contained in a hyperplane.

If the curve is degenerate, then the map  $H^0(\mathcal{O}_{\mathbb{P}^n}(1)) \to H^0(C_{red},$ 

 $O_{C_{red}}(1))$  has non-trivial kernel. Use the filtration that assigns weight -1 to sections vanishing on  $C_{red}$  and weight w>0 to the others so that the average weight is 0. There exists an integer q such that the q-th power of the ideal sheaf of nilpotents in  $\mathcal{O}_C$  is zero. Hence no monomial that contains more than q factors of weight -1 can be zero. Provided we choose m such that (m-q)w>q, every element of a monomial basis of  $H^0(C,\mathcal{O}_C(m))$  has positive weight. Hence, C is not Hilbert semi-stable. From now on we may assume that the linear span of our curves in  $\mathbb{P}^n$ . This argument is the blueprint for the other arguments. We will give very few details for the other ones.

Claim 6.30. The second claim is that every component of C is generically reduced.

Claim 6.31. The third claim is that every singularity of  $C_{red}$  is a double point.

If p is a point of multiplicity 3 or more, the two-step filtration assigning weight 0 to the sections vanishing at p and weight one to the others is destabilizing.

Claim 6.32. Every double point of  $C_{red}$  is a node.

Claim 6.33.  $H^1(C_{red}, \mathcal{O}_C(1)) = 0$ 

Claim 6.34. C is reduced.

From these claims it follows that the first three conditions of the definition of potential stability hold. The final step is to show that the estimate in (4) holds. This is done by showing that if not the filtration  $F_{C'}$  is destabilizing.

## References

- [Ab] S. S. Abhyankar. Resolution of singularities of arithmetical surfaces. In Arithmetical Algebraic Geometry (Proc. Conf. Purdue Univ., 1963), pages 111–152. Harper & Row, New York, 1965.
- [DM] P. Deligne and D. Mumford. The irreducibility of the space of curves of given genus. IHES Publ. Math. 36(1969), 75–110.
- [Ed] D. Edidin. Notes on the construction of the moduli space of curves. In Recent progress in intersection theory (Bologna, 1997), Trends Math., pages 85–113. Birkhäuser Boston, Boston, MA, 2000.
- [Fan] B. Fantechi. Stacks for everybody. In European Congress of Mathematics, Vol. I (Barcelona, 2000), volume 201 of Progr. Math., pages 349–359. Birkhäuser, Basel, 2001.
- [G] D. Gieseker. Lectures on moduli of curves, volume 69 of Tata Institute of Fundamental Research Lectures on Mathematics and Physics. Published for the Tata Institute of Fundamental Research, Bombay, 1982.
- [Gr] A. Grothendieck. Techniques de construction et théorèmes d'existence en géométrie algébrique. IV. Les schémas de Hilbert. In Séminaire Bourbaki, Vol. 6, pages Exp. No. 221, 249–276. Soc. Math. France, Paris, 1995.
- [Hab] W. J. Haboush. Reductive groups are geometrically reductive. Ann. of Math. (2) 102(1975), 67–83.
- [HM] J. Harris and I. Morrison. Moduli of curves. Springer-Verlag, 1998.
- [Ha] R. Hartshorne. Algebraic geometry. Springer-Verlag, New York, 1977. Graduate Texts in Mathematics, No. 52.
- [KM] S. Keel and S. Mori. Quotients by groupoids. Ann. of Math. (2) 145(1997), 193–213.
- [K] J. Kollár. Rational curves on algebraic varieties, volume 32 of Ergebnisse der Mathematik und ihrer Grenzgebiete. 3. Folge. A Series of Modern Surveys in Mathematics. Springer-Verlag, Berlin, 1996.

- [LM-B] G. Laumon and L. Moret-Bailly. Champs algébriques, volume 39 of Ergebnisse der Mathematik und ihrer Grenzgebiete. 3. Folge. A Series of Modern Surveys in Mathematics [Results in Mathematics and Related Areas. 3rd Series. A Series of Modern Surveys in Mathematics]. Springer-Verlag, Berlin, 2000.
- [Li] M. Lieblich. Groupoids and quotients in algebraic geometry. In Snowbird lectures in algebraic geometry, volume 388 of Contemp. Math., pages 119–136. Amer. Math. Soc., Providence, RI, 2005.
- [Mum1] D. Mumford. Further pathologies in algebraic geometry. Amer. J. Math. 84(1962), 642–648.
- [Mum2] D. Mumford. Lectures on curves on an algebraic surface. With a section by G. M. Bergman. Annals of Mathematics Studies, No. 59. Princeton University Press, Princeton, N.J., 1966.
- [Mum3] D. Mumford. Stability of projective varieties. Enseignement Math. (2) 23(1977), 39-110.
- [FKM] D. Mumford, J. Fogarty, and F. Kirwan. Geometric invariant theory, volume 34. Springer-Verlag, Berlin, third edition, 1994.
- [Ne] P. E. Newstead. Introduction to moduli problems and orbit spaces, volume 51 of Tata Institute of Fundamental Research Lectures on Mathematics and Physics. Tata Institute of Fundamental Research, Bombay, 1978.
- [Se] E. Sernesi. Topics on families of projective schemes, volume 73 of Queen's Papers in Pure and Applied Mathematics. Queen's University, Kingston, ON, 1986.

---

### THE COHOMOLOGY OF THE MODULI SPACE OF CURVES

The purpose of this unit is to give a brief survey about the cohomology and the tautological rings of the moduli space of curves. Unfortunately, for the most part the cohomology of  $M_g$  remains mysterious. Some of the outstanding problems include:

**Problem 0.1.** What is the cohomological dimension of  $M_q$ ?

**Problem 0.2.** Which classes generate the cohomology of  $M_q$ ?

**Problem 0.3.** What are the largest dimensional subvarieties of  $M_g$ ? What are the largest dimensional subvarieties of  $M_g$  that pass through a general point?

These are a few problems from an endless list of unknowns about the cohomology of  $M_g$ . Despite our ignorance there has been a tremendous effort to study the cohomology of  $M_g$  in the last three decades. Especially Harer and his students using cohomological methods applied to the mapping class group have obtained major results about the cohomology of  $M_g$ . In this unit we will survey some of these results.

#### 1. Teichmüller theory

There are many good references for Teichmüller theory. Two books that are friendly to algebraic geometers are [IT] and [Ab]. A more analytic introduction can be found in [Le]. Curt McMullen regularly teaches courses on the subject and he has really nice course notes on the subject.

From now on we will be working over the complex numbers  $\mathbb{C}$ . Accordingly we will use the Let S be a closed, oriented surface of genus g.

**Definition 1.1.** A marked Riemann surface is a pair (R, [f]) consisting of a Riemann surface and the homotopy class of an orientation preserving homeomorphism  $f: R \to S$ . Two marked Riemann surfaces  $(R_1, [f_1]), (R_2, f_2)$  are equivalent if there exists a holomorphic map  $h: R_1 \to R_2$  such that  $[f_2 \circ h] = [f_1]$ .

**Definition 1.2.** The set of equivalence classes of marked Riemann surfaces is called the Teichmüller space  $T_q$  of genus g.

We will shortly describe the Fenchel-Nielsen coordinates on Teichmüller space. Under the topology induced by these coordinates  $T_g$  becomes homeomorphic to  $\mathbb{R}^{6g-g}$ ; hence it is a contractible space. On the other hand,  $T_g$  is very closely related to  $M_g$ . Certainly if  $(R_1, f_1)$  is equivalent to  $(R_2, f_2)$ , then  $R_1$  and  $R_2$  have to be isomorphic as Riemann surfaces. This suggests that the moduli space  $M_g$  should be a quotient of  $T_g$ .

**Definition 1.3.** Define the mapping class group  $\Gamma_g$  of genus g to be the isotopy classes of orientation preserving homeomorphisms of F.


 $\Gamma_g$  acts on  $T_g$  by

$$[w]_*(R,[f]) = (R,[w \circ f])$$
 for  $[w] \in \Gamma_g$ .

This action of  $\Gamma_g$  on  $T_g$  is properly discontinuous: for any two compact subsets  $K_1$  and  $K_2$  of  $T_g$  there exists only finitely many  $[w] \in \Gamma_g$  for which  $K_1 \cap [w]_*K_2 \neq \emptyset$ . If  $(R_1, [f_1])$  and  $(R_2, [f_2])$  become identified under the action of  $\Gamma_g$ , then  $R_1$  and  $R_2$  are isomorphic as Riemann surfaces. Conversely, if there is an isomorphism  $h: R_1 \to R_2$  between  $R_1$  and  $R_2$ , we get an element of  $\Gamma_g$  by taking  $[f_2 \circ h \circ f_1^{-1}]$ . In fact  $T_g$  may be embedded in  $\mathbb{C}^{3g-3}$  as a bounded, contractible domain by the Bers embedding. Once we know this fact, we obtain a new construction of  $M_g$  as a complex orbifold.

In the sequel we will frequently invoke the Uniformization Theorem from elementary complex analysis, so we recall its statement.

**Theorem 1.4** (Uniformization). Any simply connected Riemann surface is biholomorphic to the Riemann sphere  $\hat{\mathbb{C}}$ , the complex plane  $\mathbb{C}$  or the upper half-plane  $\mathbb{H}$ . Furthermore, among  $\hat{\mathbb{C}}$ ,  $\mathbb{C}$  and  $\mathbb{H}$  no two are mutually biholomorphic.

**Example 1.5.** The uniformization theorem together with the following theorem from elementary topology

**Theorem 1.6.** Any orientation preserving homeomorphism of the two-dimensional sphere to itself is isotopic to the identity.

we conclude that  $T_0$  consists of a single point.

**Example 1.7.** The universal cover of a Riemann surface naturally has the structure of a Riemann surface. The uniformization theorem implies that the universal cover of a genus one Riemann surface is the complex plane. Every genus one Riemann surface is the quotient of the complex plane by a rank 2 lattice. We can normalize the lattice so that it is generated by  $(1,\tau)$  where  $\tau \in \mathbb{H}$ . It is well known that two complex tori represented by  $\tau$  and  $\tau'$  are biholomorphic if and only if there exists  $M \in \mathbb{P}SL_2(\mathbb{Z})$  such that  $\tau = M\tau'$ . If in addition, we want the map to be isotopic to the identity, we can assume that in the lift of the map 1 maps to 1. It follows that then two tori represent the same point in  $T_1$  if and only if  $\tau = \tau'$ . Thus we identify  $T_1$  with  $\mathbb{H}$ .

Now that we have described the spaces  $T_0$  and  $T_1$ , we will assume that  $g \geq 2$ . Every subgroup of  $Aut(\mathbb{C})$  that acts properly discontinuously and fixed point free on  $\mathbb{C}$  is abelian. It follows that any Riemann surface of genus at least two is uniformized by the upper half plane. The upper half plane with the Poincaré metric is also a model for hyperbolic two space. Since the Poincaré metric on  $\mathbb{H}$  is invariant under  $\mathbb{P}SL_2(\mathbb{R})$ , hence Riemann surfaces of genus g > 1 inherit a hyperbolic metric. Furthermore, two Riemann surfaces of genus g > 1 are conformally equivalent if and only if they are isometric with respect to the hyperbolic metric they inherit from  $\mathbb{H}$  since  $\mathbb{P}SL_2(\mathbb{R})$  is both the group of conformal self maps of  $\mathbb{H}$  and the isometries of the Poincaré metric on  $\mathbb{H}$ . We thus obtain a different description of the Teichmüller space for hyperbolic surfaces. Consider marked hyperbolic surfaces (X, [f]), where X is a smooth, oriented surface equipped with a complete Riemannian metric of constant curvature -1 and [f] is the homotopy class of an orientation preserving homeomorphism  $f: X \to F$  to a fixed compact, oriented genus g surface F. Two marked hyperbolic surfaces  $(X_1, [f_1])$  and  $(X_2, [f_2])$  are equivalent if there exists an

isometry  $h: X_1 \to X_2$  such that  $[f_2 \circ h] = [f_1]$ . The resulting space is again the Teichmüller space  $T_q$  of genus g.

We next introduce the Fenchel-Nielsen coordinates on Teichmüller space. Given a hyperbolic surface of genus g>1, we can cut the surface along 3g-3 simple, closed curves to obtain 2g-2 pieces called **pants** that are homeomorphic to a disc with two smaller inner discs removed. In a hyperbolic surface each free-homotopy (equivalently isotopy) class contains a unique geodesic loop. Moreover, if  $\alpha_1, \dots, \alpha_n$  are pair wise non-isotopic, non-intersecting simple loops, then we can find non-intersecting simple closed geodesics  $\gamma_1, \dots, \gamma_n$  with  $\gamma_i$  isotopic to  $\alpha_i$ . The  $\gamma_i$  are uniquely determined. Therefore, we can assume that we are cutting the surface along geodesics. Note that the conformal structure of the pants is determined by the lengths of the ordered (geodesic) boundary components of the pants. Consider a Fuchsian model for the surface. Then the stabilizer of a connected component of the inverse image of the pants is a free subgroup  $G_P$  of  $Aut(\mathbb{H})$  generated by two hyperbolic elements. We can realize the pants as the quotient of the upper half plane by  $G_P$ . We can conjugate  $G_P$  so that its generators are of the form

$$g_1 = (\lambda)^2 z$$
,  $0 < \lambda < 1$ ,  $g_2 = \frac{az+b}{cz+d}$ ,  $ad-bc = 1$ ,  $a+d=b+c$ ,  $c > 0$ 

and we can assume that  $g_1, g_2$  and  $(g_2 \circ g_1)^{-1}$  cover the boundary geodesics  $\gamma_1, \gamma_2, \gamma_3$ , respectively. There is a useful relation between the length of  $\gamma_i$  and the square of the trace of  $g_i$ .

**Lemma 1.8.** Let R be a Riemann surface uniformized by  $\mathbb{H}$ . Let g

$$g(z) = \frac{az+b}{cz+d}$$
,  $ad-bc = 1$ 

be a hyperbolic element in the Fuchsian group of R and let  $\gamma$  be the closed geodesic on R corresponding to g. Then

$$tr^{2}(g) = 4\cosh^{2}\left(\frac{l(\gamma)}{2}\right) \tag{1}$$

*Proof.* Since both sides of the equation are invariant under conjugation, we can assume that  $g = \lambda z$  with  $\lambda > 1$ . The length of the geodesic covered by g is given by

$$\int_{1}^{\lambda} \frac{dy}{y} = \log \lambda.$$

The lemma follows from the equality

$$(\sqrt{\lambda} + 1/\sqrt{\lambda})^2 = 4\cosh^2\left(\frac{\log \lambda}{2}\right).$$

By equation (1) the lengths of the boundary components of the pants determine the generators of  $G_P$  and consequently the conformal structure of the pants.

Next, observe that given any two boundary components of the pants, there is a unique geodesic that intersects both perpendicularly. Join the two boundary components by an arc. Double the pants to obtain a hyperbolic genus 2 surface. The arcs form a simple closed loop, hence there is a unique simple closed geodesic in the isotopy class of the loop. By symmetry this geodesic must intersect the boundary of the pants perpendicularly. The intersection point of this geodesic with a boundary

component serves as a reference point to measure any twisting in the boundary when gluing two pants. The ordered pair of lengths of the 3g-3 geodesics and the 3g-3 twist parameters give a map from  $T_g$  into  $(\mathbb{R}^+)^{3g-3} \times (\mathbb{R})^{3g-3}$ . This is in fact a bijection. We thus obtain a topology on  $T_g$  under which  $T_g$  is homeomorphic to a contractible open subset of  $\mathbb{R}^{6g-6}$ . Let us briefly recall some of the ingredients of the proof.

**Lemma 1.9.** Given an arbitrary ordered triple of positive real numbers  $(l_1, l_2, l_3)$  there exists a right hexagon in the hyperbolic plane such that the length of every other side is equal to  $l_i$ .

*Proof.* Consider the unit circle model of the hyperbolic plane. Fix a portion  $C_1$  of the imaginary axis. Find another geodesic  $C_2$  such that the distance from  $C_1$  to this geodesic is  $l_1$ . There is a one parameter family of geodesics a distance  $l_2$  away from  $C_1$ , hence one that is a distance  $l_3$  away from  $C_2$ . This gives the desired right hexagon. Observe that by letting one or two of the lengths go to zero, we obtain an ideal pentagon and an ideal quadrilateral, respectively. This will be important later when we generalize the discussion to Riemann surfaces with marked points.

The right hexagons are closely related to the pants decomposition of surfaces. If we take a pair of pants with geodesic boundaries and cut them along the perpendicular geodesics that join the boundaries pair wise, we obtain a pair of equivalent right hexagons. (Observe that two perpendicular geodesics that join different boundary components are disjoint.) Conversely, to obtain a pair of pants identify every other side of two equivalent right hexagons. When identifying the hexagons, give them opposite orientations and glue them along their boundaries respecting the orientation. The correspondence between pants and hexagons together with Lemma 1.9 allows us to conclude that there is a pair of pants with any ordered triple of positive numbers as the lengths of its boundary components. Moreover, the conformal structure of the pants is uniquely determined by these lengths. We obtain a surjective map from Teichmüller space to  $(\mathbb{R}^+)^{3(g-1)}$ . Fix 3(g-1) simple closed curves  $\alpha_i$  (see Figure 1) that cut the surface into pants. As we vary the hyperbolic metric on the surface the lengths of the geodesics in the isotopy classes of these simple closed curves assume all values in  $(\mathbb{R}^+)^{3(g-1)}$ . Observe that we can glue two pants (metrically) along two geodesic boundary components if and only if the boundary components have the same length. We identify two points on the boundary and then glue according to arc length. But we can also twist the boundary components by an angle before we glue. There remains to show that any twisting in any of the curves leads to different points of Teichmüller space. For the proof one fixes a non-trivial loop  $\beta_i$  that intersects  $\alpha_i$  at two points. Then there is a function from  $\mathbb{R}^{3(g-1)}$  to  $\mathbb{R}$  given by the length of the geodesic loop in the homotopy class of  $\beta_i$  as one varies the metric by twisting the 3(q-1) curves. One proves that the functions so obtained are strictly convex and have minima. This implies then that there is a bijection between Teichmüller space and  $(\mathbb{R}^+ \times \mathbb{R})^{3(g-1)}$ .

**Remark 1.10.** It is possible to give a third definition of Teichmüller space in terms of quasiconformal mappings. Using this point of view one can introduce a complex structure on Teichmüller space so that  $T_g$  becomes a bounded domain in  $\mathbb{C}^{3g-3}$ . Let  $\{z_i\}$  be local parameters on an open cover  $S = \bigcup U_i$  of the Riemann surface S.

FIGURE 1. Cutting a genus 2 surface into pairs of pants.

A collection of complex valued functions  $\phi_i$  on  $U_i$  is a differential of type (m, n) if the functions transform according to the rule

$$\phi_i \left(\frac{dz_i}{dz_j}\right)^m \left(\overline{\frac{dz_i}{dz_j}}\right)^n = \phi_j$$

whenever  $U_i \cap U_i \neq \emptyset$ . A differential of type (2,0) is called a quadratic differential. A differential of type (-1,1) where  $\phi$  is measurable and  $||\phi||_{\infty} < 1$  is called a Beltrami differential. A homeomorphism f from one Riemann surface to another is called quasiconformal if f is an  $L^2$  solution of the differential equation  $\overline{\partial} f = \mu \partial f$  for some Beltrami differential  $\mu$ . Given a Beltrami differential  $\mu$  on a Riemann surface S, there exists a quasiconformal map of S onto another Riemann surface with complex dilation  $\mu$ . This map is uniquely determined up to a conformal map. Hence, a Beltrami differential on a Riemann surface S determines a complex structure on S. To define Teichmüller space consider all quasiconformal mappings of a Riemann surface F onto other Riemann surfaces. Let two maps  $f_1$  and  $f_2$  be equivalent when  $f_2 \circ f_1^{-1}$  is homotopic to a conformal map. The set of equivalence classes is Teichmüller space. In case the Riemann surface is compact each homotopy class of an orientation preserving homeomorphism contains a quasiconformal map, so this definition agrees with the previous ones. Suppose a Riemann surface R is uniformized by the upper half plane. Let  $G_R$  be the Fuchsian model of R. Given a Beltrami differential  $\mu$  on R, it is possible to lift  $\mu$  to H in a  $G_R$  invariant way. Extend this differential to the complex plane by setting it to zero in the complement of the upper half plane. There is a quasiconformal map  $f_{\mu}$  corresponding to this extended Beltrami differential. If we require  $f_{\mu}$  to fix  $0, 1, \infty$ , then  $f_{\mu}$  is unique. Note that  $f_{\mu}$  is conformal in the lower half plane. The Schwarzian derivative of  $f_{\mu}$  gives a holomorphic automorphic form of weight -4 with respect to  $G_R$  on the lower half plane. Let  $A_2(H^*, G_R)$  be the complex vector space of holomorphic automorphic forms of weight -4 on the lower half plane. We can define the **Bers' embedding** by sending  $\mu$  to the Schwarzian derivative  $S(f_{\mu_{\mid H^*}})$ . A fundamental theorem states that the Bers' embedding realizes Teichmüller space as a bounded domain in  $A_2(H^*, G_R)$ . We thus obtain a complex structure on Teichmüller space via the Bers' embedding. The mapping class group acts as a group of biholomorphic automorphisms of Teichmüller space. Since we can realize Teichmüller space as a bounded domain in a complex vector space we can apply normality arguments to the mapping class group. For example, we can prove that the mapping class group acts properly discontinuously on Teichmüller space.

**Proposition 1.11.** The Teichmüller modular group acts properly discontinuously on Teichmüller space.

The proof is by contradiction. The strategy is to find a sequence  $f_n \in \Gamma_g$  converging to f uniformly on compact subsets of  $T_g$ . Consider the elements  $h_n = f_{n+1}^{-1} \circ f_n$  converging to an element  $h \in \Gamma_g$ . Using the fact that the square of the traces of the elements of a Fuchsian group is discrete in  $\mathbb{R}$ , we conclude that  $h_n$  must be in the isotropy group of some point in  $T_g$  after some large n. We thus obtain an infinite sequence of elements in the isotropy group of a point in  $T_g$ . But the isotropy group of a point is isomorphic to the biholomorphic automorphisms of the Riemann surface, which is a finite group. This contradicts the fact that we had an infinite sequence. Now let us flesh out the details.

**Lemma 1.12.** The set of hyperbolic lengths of all closed geodesics on a closed Riemann surface R of genus  $g \geq 2$  is a discrete set of real numbers. Moreover, for any positive number there are at most finitely many closed geodesics with that hyperbolic length.

Proof. Suppose there exists a sequence  $\{C_n\}_{n=1}^{\infty}$  of simple closed geodesics on R with  $l(C_n) \leq M$  for some finite positive number M. We derive a contradiction by showing that the Fuchsian group of covering transformations of R cannot be discrete in  $Aut(\mathbb{H})$ . Choose a relatively compact fundamental domain for the Fuchsian group and choose elements of the group representing the closed geodesics. We thus obtain a sequence of mutually distinct elements  $\gamma_n$  of the Fuchsian group for which  $\min_{z\in\overline{F}}\rho(z,\gamma_n(z))\leq M$ , where  $\overline{F}$  is the closure (compact by choice) of the fundamental domain. Now  $\gamma_n$  is a normal family, hence, by choosing a subsequence if necessary, we see that they converge to an automorphism of H. Hence the Fuchsian group is not discrete. This is a contradiction.

We may conclude from this lemma that  $\{tr^2(\gamma): \gamma \in \Gamma\}$  is a discrete set of real numbers. In lemma 1.8 we proved that

$$tr(\gamma)^2 = 4\cosh^2(\frac{l(L_\gamma)}{2}).$$

Since the lengths of the geodesics are discrete, so must the square of the traces of the group elements.

A final observation is that given a system of generators  $\{g_i\}$  for a Fuchsian model of a closed Riemann surface such that  $g_1$  has a repelling fixed point at 0 and an attractive fixed point at  $\infty$  and  $g_2$  has an attractive fixed point at 1 and a repelling fixed point at r < 0, the generators are determined by the absolute values of the traces in

$$\{g_i, g_1 \circ g_i, g_1^{-1} \circ g_i, g_2 \circ g_i, g_2^{-1} \circ g_i, g_1 \circ g_2 \circ g_i, (g_1 \circ g_2)^{-1} \circ g_i\}$$

Let us return to the proof that the mapping class group acts properly discontinuously on Teichmüller space. Suppose not. Then we can find a sequence of distinct elements in the mapping class group and a sequence of points  $p_n$  in Teichmüller space converging to a point p such that

$$f_n(p_n) \to p \in T_q$$
.

By the normality of the family, selecting a subsequence if necessary, we can assume that  $f_n$  converges to f uniformly on compact subsets of the Teichmüller space. Set  $h_n = f_{n+1}^{-1} \circ f_n$ . Observe that  $h_n$  converges to some h uniformly on compact subsets of Teichmüller space and h fixes the point p. By translating p to the identity we can assume that h fixes the identity. We want to deduce that after some p each p and p are the point p and p are the identity we can assume that p fixes the identity.

fixes the identity. If we let  $w_n$  represent  $h_n$ , then for any g in the Fuchsian group we have

$$\lim_{n \to \infty} tr^2(w_n^{-1}gw_n) = tr^2(g).$$

Since the traces are discrete, after some n equality must hold without the limit. Since the group is determined by the traces of finitely many elements, after some n each  $h_n$  must be in the normalizer of the group. Hence  $h_n$  is in the isotropy group of the identity for all sufficiently large n. This is a contradiction. We conclude that the mapping class group acts properly discontinuously on Teichmüller space.

The action of the mapping class group, however, is not fixed point free. Riemann surfaces with non-trivial biholomorphic automorphisms are fixed by suitable elements of the group. In general, the moduli space is not a manifold. However, as we observed in the beginning of this section, Proposition 1.11 implies that  $M_g$  has an orbifold structure.

**Remark 1.13.** In this section to make the exposition more manageable I described the Teichmüller space of compact genus q surfaces. In the sequel we will need to consider the case when the surface has marked points and boundary components. Let  $F_{g,n}$  be a surface of genus g with n marked points  $p_1, \dots, p_n$ . Consider triples  $(R, q_i, [f])$  consisting of a Riemann surface R with n parked points  $q_1, \dots, q_n$  and the homotopy class (relative to the  $q_i$ ) of an orientation preserving homeomorphisms f:  $R \to F$  such that  $f(q_i) = p_i$ . Call two triples  $(R_1, q_i^1, [f_1]) \cong (R_2, q_i^2, [f_2])$  equivalent iff there exists a conformal homeomorphism  $h: R_1 \to R_2$  such that  $h(q_i^1) = q_i^2$  and  $[f_2 \circ h] = [f_1]$ . The Teichmüller space  $T_{g,n}$  is the set of equivalence classes of triples. More generally, we can allow F to have boundary components. In this case we require the homotopies to fix the boundary. We obtain the Teichmüller space  $T_{g,n}^r$ . There is a corresponding mapping class group  $\Gamma_{g,n}^r$  consisting of orientation preserving homeomorphisms of  $F_{g,n}^r$  that fix the marked points and the boundary components. We can interpret  $T_{g,n}$  from the point of view of hyperbolic geometry by considering complete hyperbolic surfaces of finite area. Here the marked points can be thought of as cusps. There is a pants decomposition provided that we allow ideal pants with one or two boundary components of length zero. The analysis in the Fenchel-Nielsen coordinates goes through to show that the Teichmüller space is homeomorphic to  $(\mathbb{R}^+ \times \mathbb{R})^{3(g-1)+n}$  provided that 2g-2+n>0.

# 2. The Harer-Zagier Formula for the orbifold Euler characteristic of the mapping class group

The main references for this section are [HZ] and [Har4].

Here we will discuss remarkable formula due to Harer and Zagier, which relates the orbifold Euler characteristic of the mapping class group  $\Gamma_{1,g}$  to the values of the zeta function at the negative odd integers.

$$\chi_{orb}(\Gamma g, 1) = \zeta(1 - 2g) = -\frac{B_{2g}}{2g}$$
(2)

Pick a torsion free subgroup  $\Gamma'$  of finite index in  $\Gamma_{g,1}$ . Note that  $\Gamma'$  acts on Teichmüller space freely and properly discontinuously, so the quotient of Teichmüller space by  $\Gamma'$  is a manifold. Define the orbifold Euler characteristic of  $\Gamma_{1,g}$  as the Euler characteristic of this manifold divided by the index of  $\Gamma'$  in  $\Gamma_{1,g}$ . Note that

the orbifold Euler characteristic does not depend on the choice of  $\Gamma'$ . Given a different subgroup  $\Gamma''$  we can find a common subgroup H of  $\Gamma'$  and  $\Gamma''$  so that H has finite index in  $\Gamma_{1,g}$ . By the multiplicativity of indexes and of the Euler characteristics of covering spaces we conclude that the orbifold Euler characteristic of  $\Gamma_{1,g}$  is independent of the choice of finite index subgroup.

Suppose a group acts on a contractible cell complex respecting the cell structure of the complex. Under some finiteness conditions a theorem of Quillen gives a method for calculating the orbifold Euler characteristic of a group. Splitting the cell complex to orbits leads to a spectral sequence. Denoting the stabilizers of a representative of each orbit by  $G_p^i$ , we can write Quillen's formula as

$$\chi_{orb}(\Gamma_{1,g}) = \sum_p (-1)^p \sum_i \chi(G_p^i).$$

We will now describe a contractible cell complex on which  $\Gamma_{1,g}$  acts preserving the cell structure. Let F be a Riemann surface of genus g with a base point q. An  $\operatorname{arc}$ system of rank k is a collection of k+1 isotopy classes of curves  $<\alpha_0,\cdots\alpha_k>$ that intersect only at the base point q and satisfy the non-triviality condition that none of the curves are null-homotopic and no two of the curves are homotopic to each other. Here and in what follows homotopy and isotopy should be interpreted to be relative to the base point q. An arc system fills the surface F if all the components of the complement of the curves  $F - \{\alpha_i\}$  are simply connected. Build a cell complex Y which has a k-cell for each rank 6g-4-k arc system that fills the surface. An l-cell  $\langle \beta_0, \dots, \beta_l \rangle$  is a face of a k-cell  $\langle \alpha_0, \dots, \alpha_k \rangle$  exactly when  $\{\beta_i\}\subset\{\alpha_j\}$ . Observe that by the non-triviality conditions the largest possible rank for an arc system is 6g - 4 since 6g - 3 curves separate the surface into disjoint triangles. Also observe that an arc system of rank less than or equal to 2g-2cannot fill the surface. The cell complex Y that we obtain is contractible. (We will assume this result without proof.) The group  $\Gamma_{1,g}$  acts on Y. We will compute the orbifold Euler characteristic using this action. Take a rank n = 6g - 3 - p arc system  $\langle \alpha_0, \dots, \alpha_n \rangle$  which fills F. We will construct a dual graph  $\Omega$  to this arc system.  $\Omega$  has a vertex for each connected component of  $F - \{\alpha_i\}$  and one edge that meets  $\alpha_i$  transversely for each  $\alpha_i$ . Cutting the surface along this graph gives a 2n-gon  $P_n$  with a pairing  $\tau$  of the edges so that  $F \cong P_n/\tau$ . We take the marked point to be the center of the 2n-gon. Observe that every vertex of the dual graph has valence at least 3. If a vertex had valence 1, then the boundary of the connected component corresponding to that vertex would have to consist of one curve. However, that curve would be contractible (recall the pieces are simply connected) contradicting the assumption that none of the curves in the arc system were null homotopic. If a vertex had valence 2, then the boundary of the connected component corresponding to that vertex would have only two curves. Those curves would have to be homotopic. This violates the other non-triviality condition. These conditions imply two conditions A and B on the way the sides of  $P_n$  can be identified. First, no two adjacent sides of  $P_n$  are identified (A). Otherwise, the vertex common to both would have valence 1. Second, no two adjacent sides are identified to two other adjacent sides in the reverse order (B). Otherwise, the vertex common to the pair of adjacent sides would be a vertex of valence 2. These are the only requirements on the identification. Denote by  $\lambda_g(n)$  the number of possible pairings of the sides of  $P_n$  satisfying both these conditions and giving an orientable genus g surface. Denote by  $\mu_q(n)$  the number of possible pairings that satisfy only the first condition but not necessarily the second. Finally denote by  $\epsilon_g(n)$  the number of possible pairings of the sides of  $P_n$  that gives an orientable genus g surface (no conditions imposed). Note that these three numbers satisfy the following two equations:

$$\epsilon_g(n) = \sum_i \binom{2n}{i} \mu_g(n-i) \tag{3}$$

$$\mu_g(n) = \sum_i \binom{n}{i} \lambda_g(n-i) \tag{4}$$

To prove equation (4) start with an arbitrary pairing on the 2n-gon that gives a genus g surface. If two adjacent sides are identified, we can eliminate them by making their common vertex an interior point of a 2n-2-gon. The 2n-2-gon has an identification of its sides that gives a genus g surface. There might still be adjacent sides which are identified. (In fact, two sides that are identified can become adjacent as a result of this process.) If we continue to eliminate the adjacent sides that are identified, we eventually obtain a 2n-2i-gon with no adjacent sides identified. Observe that this process does not change the genus of the surface. All the  $\mu_g(n-i)$  possibilities can occur for each i. Moreover, a particular identification of  $P_{n-i}$  occurs  $\binom{2n}{i}$  times since we are free to choose any of the i vertices of  $P_n$  as the vertices that become the interior points of  $P_{n-i}$ .

The proof of equation (5) is similar in flavor. Suppose we start with an arbitrary identification satisfying condition (A) but not necessarily condition (B). We can make a pair of edges into one edge if this pair is identified to another pair in the reverse order. We get  $P_{2n-2}$  with an identification of its sides, which still gives a genus g surface. Continuing we eventually obtain  $P_{2n-2i}$  with an identification that satisfies both conditions. Given an admissible identification of the sides of  $P_{2n-2i}$  there are  $\binom{n}{i}$  ways that it can occur under this reduction. Orient the boundary of  $P_{2n-2i}$  and number its edges consecutively starting from some vertex. For each pair of identified edges take the smaller of the numbers. This leads to a sequence of numbers  $1 < j_1 < \cdots < j_{n-i}$ . Given any n-i non negative integers that sum to i, we can split the side corresponding to  $j_k$  to  $m_k + 1$  pieces. The only ambiguity is in choosing which of the  $m_1 + 1$  edges becomes edge 1 in  $P_n$ . Summing the possibilities leads to equation (5).

The stabilizer of a p-cell in Y corresponds to the rotational symmetries of an identification of  $P_n$  where n=6g-3-p. The stabilizer of this cell is of finite order, say 2n/m, with Euler characteristic m/2n. Consider pairings of the edges of  $P_n$  that satisfy both (A) and (B). Let two pairings be equivalent if they differ by a rotation of  $P_n$ . Choose a representative of each equivalence class. If an equivalence class has order m, then the cells have cyclic symmetry of order 2n/m. Hence we can count over each possible pairing giving each pairing the weight 1/2n. Using Quillen's formula we conclude that

$$\chi_{orb}(\Gamma_{1,g}) = \sum_{p} (-1)^p \sum_{i} \chi(G_p^i) = \sum_{n=2q}^{6g-3} (-1)^{n-1} \lambda_g(n).$$
 (5)

Note that the non-triviality condition on the arc systems means that there cannot be any arc systems of rank bigger than 6g - 4. The fact that they fill the surface

implies that the rank is at least 2g - 1. This justifies letting the sum run from 2g to 6g - 3.

Now that we have obtained an expression for the orbifold Euler characteristic of  $\Gamma_{1,g}$ , there remains to relate this expression to the zeta function. The main task will be to prove the equation

$$\epsilon_g(n) = \frac{(2n)!}{(n+1)!(n-2g)!} \ Co\left(x^{2g}, \left(\frac{x/2}{\tanh(x/2)}\right)^{n+1}\right)$$
 (6)

where  $Co(x^k, f(x))$  denotes the coefficient of  $x^k$  in the power series expansion of f. It is convenient to define an auxiliary polynomial whose value at 0 is the orbifold Euler characteristic. Let

$$\epsilon_g(n) = \binom{2n}{n+1} F_g(n)$$

If we assume the previous claim about  $\epsilon_g(n)$ , then we observe that  $F_g(n)$  is a polynomial of degree 3g-1. It vanishes at -1, hence n+1 divides it. Taking  $(n-1), (n-1)(n-2), \cdots$  as our basis for polynomials we can express F as

$$F_g(n) = (n+1) \sum_{r=1}^d \frac{r!}{(2r)!} \kappa_g(r) (n-1) (n-2) \cdots (n-r+1).$$

The factor r!/(2r)! will simplify some of the equations that will occur later. Observe that we can express  $\epsilon_q(n)$  as

$$\epsilon_g(n) = \frac{(2n)!}{n!} \sum_{r=1}^d \frac{r! \kappa_g(r)}{(2r)! (n-r)!}.$$

To complete the proof of the theorem we have to justify two assertions. First,  $F_g(0)$  is the orbifold Euler characteristic of  $\Gamma_{g,1}$ . Second,  $\epsilon_g(n)$  is given by equation (7). Observe that the Taylor expansion of  $(t/2)/\tanh(t/2)$  leads to the Harer-Zagier formula. We begin by verifying the first claim. Form the generating functions

$$L_g(x) = \sum_{n>0} \lambda_g(n)x^n \qquad M_g(x) = \sum_{n>0} \mu_g(n)x^n$$

$$E_g(x) = \sum_{n \ge 0} \epsilon_g(n) x^n$$
  $K_g(x) = \sum_n \kappa_g(n) x^n$ 

It is possible to relate these functions to each other by using the relations between the coefficients. The following formula will be useful.

$$\sum_{i} {2i+k \choose i} x^{i} = \frac{1}{\sqrt{1-4x}} \left( \frac{1-\sqrt{1-4x}}{2x} \right)^{k}.$$

To prove this formula observe that when k = 0 we have the well known case  $(1-4x)^{-1/2}$ . Let the sum on the left be  $f_k$ . Writing

$$\binom{2i+k}{i} = \binom{2i+k-1}{i} + \binom{2(i-1)+k+1}{i-1}$$

we obtain the recursion relation  $f_{k-2} = f_{k-1} + xf_k$  valid for  $k \ge 2$ . For k = 1 one has to fix the first few terms to obtain  $f_0 = 2xf_1 + 1$ . The rest follows by induction.

We can now obtain the relations among the generating functions we defined. To relate E and M write

$$E_g(x) = \sum_{n} \epsilon_g(n) x^n = \sum_{n} \left( \sum_{i} {2n \choose i} \mu_g(n-i) \right) x^n$$

$$= \sum_{j \ge 0} \sum_{i} {2i+2j \choose i} \mu_g(j) x^{i+j} = \sum_{j} \mu_g(j) x^j \sum_{i} {2i+2j \choose i} x^i$$

$$= \frac{1}{\sqrt{1-4x}} M_g(\frac{1-2x-\sqrt{1-4x}}{2x})$$

To relate E and K we write

$$E_g(x) = \sum_n \frac{(2n)!}{n!} \sum_{r=1}^d \frac{r! \kappa_g(r) x^n}{(2r)! (n-r)!} = \sum_{r=1}^d \frac{r! \kappa_g(r)}{(2r)!} \sum_n \frac{(2n)! x^n}{n! (n-r)!}$$

$$= \sum_{r=1}^d \frac{r! \kappa_g(r)}{(2r)!} x^r \frac{d^r}{dx^r} \sum_n \frac{(2n)! x^n}{n! (n)!} = \sum_{r=1}^d \frac{r! \kappa_g(r)}{(2r)!} x^r \frac{d^r (1-4x)^{-1/2}}{dx^r}$$

$$= \frac{1}{\sqrt{1-4x}} \sum_r \kappa_g(r) \left(\frac{x}{1-4x}\right)^r = \frac{1}{\sqrt{1-4x}} K_g\left(\frac{x}{1-4x}\right)$$

Finally to relate L to the rest

$$M_g(x) = \sum_{n} \sum_{i} \binom{n}{i} \lambda_g(n-i) x^n = \sum_{j} \lambda_g(j) x^j \sum_{i} \binom{i+j}{i} x^i$$
$$= \sum_{i} \lambda_g(j) x^j \frac{1}{(1-x)^{j+1}} = \frac{1}{1-x} L_g\left(\frac{x}{1-x}\right)$$

Combining these relations we obtain

$$L_g(x) = \frac{1}{1+x} K_g(x(1+x)). \tag{7}$$

This formula allows us to relate the orbifold Euler characteristic of  $\Gamma_{g,1}$  to the value  $F_g(0)$ . We have an expression for the Euler characteristic in terms of  $\lambda_g$ . Using the previous equation we can turn this expression into a beta integral.

$$\chi_{orb}(g) = \sum_{i} \frac{(-1)^{n-1} \lambda_g(n)}{2n} = -\frac{1}{2} \int_0^1 \frac{\sum_{n} \lambda_g(n)(-x)^n dx}{x}$$

$$= -\frac{1}{2} \int_0^1 \frac{L_g(-x) dx}{x} = -\frac{1}{2} \int_0^1 \frac{K_g(-x(1-x)) dx}{x(1-x)}$$

$$= \frac{1}{2} \sum_{r} (-1)^{r-1} \kappa_g(r) \int_0^1 x^{r-1} (1-x)^{r-1} dx$$

$$= \sum_{r} (-1)^{r-1} \frac{r!(r-1)! \kappa_g(r)}{(2r)!} = F_g(0)$$

There remains to prove equation (7). We will first relate  $\epsilon_g(n)$  to the number of pairs consisting of a coloring of the vertices of  $P_n$  and an identification of the edges compatible with the coloring that gives an orientable surface. Counting the number of pairs a different way will yield an integral formula for  $\epsilon_g(n)$ . More precisely let C(n,k) denote the number of pairs  $(\phi,\tau)$  where  $\phi$  is a k-coloring of the vertices

of  $P_n$  and  $\tau$  is a compatible identification of the edges. Suppose we are given an identification that yields a genus g surface. In  $P_n$  there are n+1-2g inequivalent vertices. These can be colored arbitrarily. So given an identification that yields a genus g surface there are  $k^{n+1-2g}$  possible ways to color the vertices. On the other hand, the sides can be paired to give any surface of genus between 0 and n/2. We conclude

$$C(n,k) = \sum_{0}^{n/2} \epsilon_g(n) k^{n+1-2g}.$$

It is convenient to introduce another auxiliary function D(n, k), which will be related to C(n, k) by the equation

$$C(n,k) = (2n-1)!!D(n,k).$$

However, to make D(n, k)'s connection to the zeta function more apparent it is more convenient to define it by the equality

$$1 + 2\sum_{n=0}^{\infty} D(n,k)x^{n+1} = \left(\frac{1+x}{1-x}\right)^k.$$

Showing the relation between C(n,k) and D(n,k) will be the hard work. Once we assume this relation the main theorem follows. Differentiate both sides of the defining equation of D(n,k). To extract D(n,k) we can divide both sides of the resulting equation by  $x^{n+1}$ . The residue at 0 will be (n+1)D(n,k). Substituting  $x = \tanh(t/2)$  we obtain

$$(n+1)D(n,k) = res_{t=0} \frac{k}{2} \left(\frac{1}{\tanh(t/2)}\right)^{n+1} e^{kt} dt$$

Consider the function  $e^{kt}((t/2)/\tanh(t/2))^{n+1}$ . The above residue will be  $2^nk$  times the coefficient of  $t^n$  of this function.  $((t/2)/\tanh(t/2))^{n+1}$  is an even function and we know the power series expansion of  $e^{kt}$ . Multiplying these out and using the equation that relates C(n,k) and D(n,k) we obtain

$$C(n,k) = \sum_{g=0}^{n/2} \frac{(2n)!k^{n+1-2g}}{(n+1)!(n-2g)!} Co\left(t^{2g}, \left(\frac{t/2}{\tanh(t/2)}\right)^{n+1}\right).$$

Comparing the coefficients of k in this expression and in the expression defining C(n,k), we obtain equation (7). This completes the proof of the theorem that

$$\chi_{orb}(\Gamma_{1,q}) = \zeta(1-2q)$$

modulo the equality C(n,k) = (2n-1)!!D(n,k). We now sketch a proof of this equality.

Observe that D(n,k) is a polynomial of degree k-1 in n. To be precise expanding  $((1+x)/(1-x))^k$  using the binomial coefficients theorem we see that

$$D(n,k) = \sum_{l=1}^{k} 2^{l-1} \binom{k}{l} \binom{n}{l-1}.$$

Suppose C(n, k) could be expressed as (2n - 1)!!Q(n, k), where Q(n, k) is a polynomial of degree k - 1 in n. Then we can identify Q(n, k) and C(n, k). Note that this statement should be the content of lemma 8.7 in Harer's C.I.M.E. notes. Recall that C(n, k) was the number of pairs consisting of a coloring of the vertices of

 $P_n$  and a compatible identification of the edges. The number of compatible pairs where the coloring uses all k available colors at least once generates a new function S(n,k). Since any pair counted in C(n,k) uses l different colors and since there are  $\binom{k}{l}$  choices for the colors, we obtain

$$C(n,k) = \sum_{l=0}^{k} {k \choose l} S(n,l).$$

or equivalently

$$S(n,k) = \sum_{l=0}^{k} (-1)^{k-l} {k \choose l} C(n,l) = (2n-1)!! \sum_{l=0}^{k} (-1)^{k-l} {k \choose l} Q(n,k)$$
  

$$\equiv (2n-1)!! Q'(n,k).$$

Observe that our assumptions about Q(n,k) imply that Q'(n,k) is a polynomial of degree k-1 in n. Since there cannot be any surjective coloring of  $P_n$  by k colors if n < k-1 this polynomial vanishes at  $0, 1, \dots k-2$ , so

$$Q'(n,k) = \delta_k \binom{n}{k-1}$$

where  $\delta_k$  does not depend on n. We have to identify  $\delta_k$ . Since  $\delta_k$  does not depend on n but only on k we can determine it in the case when n = k - 1. S(k - 1, k) is  $k!\epsilon_0(k-1)$  since the only genus that one can obtain from  $P_{k-1}$  by using k colors is a genus 0 surface and there are k! choices of colors for each surface.  $\epsilon_0(k)$  is the k-th Catalan number. Putting these facts together gives  $\delta_k = 2^{k-1}$ . We proved

$$C(n,k) = \sum_{l=0}^{k} {k \choose l} S(n,l) = (2n-1)!! \sum_{l=1}^{k-1} 2^{l-1} {k \choose l} {n \choose k-1}$$
$$= (2n-1)!! D(n,k)$$

except for the assertion that C(n,k) can be expressed as a polynomial of degree k-1 in n times (2n-1)!!. To conclude the proof we exhibit C(n,k) as such a polynomial.

We are going to obtain a different formula for C(n,k) by first fixing a coloring, then counting all the possible ways to identify the sides compatible with that coloring. Fix an orientation of the boundary of  $P_n$ . Denote by  $n_{ij}$  the number of edges that have the coloring i-j. First, observe that for there to be a compatible identification  $n_{ij} = n_{ji}$  and  $2|n_{ii}$ . Note that the matrix  $N = (n_{ij})$  is symmetric and the entries along the diagonal are even. Call such matrices even symmetric matrices. Once these conditions on  $n_{ij}$  are satisfied for every i, j the number of ways to identify the sides in a compatible way is  $\prod_{i < j} n_{ij}! \prod_i (n_{ii} - 1)!!$ . We can express C(n, k) as a sum over matrices with non-negative integer coefficients such that  $\sum_{i,j} n_{ij} = 2n$ . We sum the product of the number of ways C(N) of coloring  $P_n$  with  $n_{ij}$  edges having color i-j and the number of ways E(N) of identifying the edges compatible with that coloring to obtain an orientable surface:

$$C(n,k) = \sum_{N} C(N)E(N).$$

Using the integral representations of the delta function and the gamma function, we can express C(n,k) as

$$C(n,k) = 2^{-k/2} \pi^{-k^2/2} \int_{H_k} tr(Z^{2n}) e^{-\frac{1}{2}tr(Z^2)} d\nu_H,$$

where the integral is over  $k \times k$  Hermitian matrices. Every Hermitian matrix can be diagonalized by conjugation. The diagonal matrix is unique up to a permutation. This allows to rewrite the integral as an integral over diagonal matrices. (Observe that the function we are integrating is invariant under conjugation.) Our function is easy to evaluate on diagonal matrices. One obtains the formula

$$C(n,k) = c_k \int_{\mathbf{R}^k} \left( \sum_{i=1}^k t_i^{2n} \right) e^{-\frac{1}{2} \left( \sum_{i=1}^k t_i^2 \right)} \prod_{1 \le i,j \le k} (t_i - t_j)^2 dt_1 \cdots dt_k.$$

Using the symmetry of the integral one can integrate over  $t_1$  to express C(n, k) as a polynomial of degree k-1 times (2n-1)!!. This completes the proof of the theorem.

Remark: There are ways of obtaining the actual Euler characteristic of the Moduli space using the orbifold Euler characteristic. Harer and Zagier have given a generating function for the Euler characteristic of  $\Gamma_g$ . In view of the techniques Arbarello and Cornalba use, knowing the Euler characteristics of various Moduli spaces becomes important. Hence, as our knowledge about the homology groups of various moduli spaces increases, the Harer Zagier formula might have many applications. Also note that in the process of the proof we have counted the ways of identifying the sides of a polygon to obtain a genus g surface. This seems to be an interesting geometric fact that is not immediately apparent.

## 3. The stable cohomology of $M_q$ , Mumford's conjecture

The basic strategy in calculating the orbifold Euler characteristic of moduli space was to relate the Euler characteristic to an invariant of the mapping class group. Then using the action of the mapping class group on another suitable space one was able to calculate the Euler characteristic. In fact, Harer has used this basic strategy in many other circumstances to obtain information about the cohomology of the moduli space of curves. In this section we briefly summarize some of his results without giving any proofs. For the proofs the reader may consult [Har2], [Har3], [Har1] and [Har4].

An important corollary of the construction of the moduli space of curves as the quotient of Teichmüller space by the action of the mapping class group is that the homology with  $\mathbb{Q}$ -coefficients of  $M_g$  is isomorphic to the homology of the mapping class group. This allows Harer to compute the homology of  $M_g$  via the homology of the mapping class group.

An initial result about the homology or more precisely the homotopy type of  $M_{g,n}$  is that it has the homotopy type of a finite cell complex of dimension 4g - 4 + n when n > 0. This allows us to conclude that the k-th homology groups of  $M_{g,n}$  vanish for sufficiently large values of k. The precise statements and proofs may be found in [Har3].

**Theorem 3.1.** The moduli space  $M_{g,n}$  has the homotopy type of a finite cell-complex of dimension 4g - 4 + n, n > 0. Using this one may deduce that

$$H_k(M_{q,n},\mathbb{Z})=0$$

if n>0 and k>4g-4+n and

$$H_k(M_a,\mathbb{Q})=0$$

if k > 4g - 5.

**Problem 3.2.** Determine the precise homological dimension of the moduli space of curves.

Harer's next result is that the k-th homology group of  $M_{g,n}$  does not depend on g provided k is small compared to g. Again the details and precise statements may be found in [Har2]. One advantage of working with the mapping class group is that we can allow the Riemann surfaces to have boundaries. Let  $\Sigma_{g,n}^r$  denote a Riemann surface of genus g with n marked points and r boundary components. Define the mapping class group  $Map_{g,n}^r$  to be the homotopy classes of orientation preserving diffeomorphisms of  $\Sigma_{g,n}^r$  that restrict to the identity on the boundary and the marked points.

There are the following inclusions between these mapping class group given by the geometric operations depicted in Figure 2.

The map  $\Psi: Map_{q,n}^r \to Map_{q+1,n}^{r-1}$ 

The map  $\eta: Map_{g,n}^r \to Map_{g+1,n}^{r-2}$ 

FIGURE 2. The maps that occur in Harer's Stability Theorem

(1) There is a map  $\Phi: Map_{g,n}^r \to Map_{g,n}^{r+1}$  induced by attaching a pair of pants along one of the boundary components of  $\Sigma_{g,n}^r$ . In particular, we need to assume that  $r \geq 1$  for this map to make sense.

- (2) There is a map  $\Psi: Map_{g,n}^r \to Map_{g+1,n}^{r-1}$  induced by attaching a pair of pants to  $\Sigma_{g,n}^r$  along two boundary components. Here we need to assume that r > 2.
- (3) Finally there is a map  $\eta: Map_{g,n}^r \to Map_{g+1,n}^{r-2}$  induced by gluing two boundary components of  $\Sigma_{g,n}^r$ . We again need to assume that  $r \geq 2$ .

Harer's stability theorem asserts that the maps  $\Phi$ ,  $\Psi$  and  $\eta$  induce isomorphisms on homology in a certain range.

**Theorem 3.3.** (1)  $\Phi_*: H_k(Map_{g,n}^r) \to H_k(Map_{g,n}^{r+1})$  is an isomorphism if  $g \geq 3k-2$  and  $r \geq 1$ .

- (2)  $\Psi_*: H_k(Map_{g,n}^r) \to H_k(Map_{g+1,n}^{r-1})$  is an isomorphism if  $g \geq 3k-1$  and r > 2.
- (3)  $\eta_*: H_k(Map_{q,n}^r) \to H_k(Map_{q+1,n}^{r-2})$  is an isomorphism if  $g \geq 3k$  and  $r \geq 2$ .

In particular, combining these isomorphisms we see that  $H_k(M_{g,n},\mathbb{Q})$  does not depend on g provided  $g \geq 3k+1$ . Using the universal coefficients theorem similarly we can say that  $H^k(M_{g,n},\mathbb{Q})$  does not depend on g provided  $g \geq 3k+1$ . Moreover, the isomorphisms are compatible with cup products. This allows one to define a stable cohomology ring  $H^*_{stab}(M,\mathbb{Q})$  of moduli spaces of curves by setting the k-th cohomology group to be  $H^k(M_g,\mathbb{Q})$  for g > 3k+1.

The first question that presents itself is to describe  $H^*_{stab}(M,\mathbb{Q})$ . Consider the tautological map

$$\pi:M_{a,1}\to M_a$$

given by forgetting the marked point. Let  $\zeta = c_1(\omega_{M_g,1/M_g})$ . We obtain a collection of natural even cohomology classes on  $M_g$  by considering  $\kappa_i = \pi_*(\zeta^{i+1})$ . The celebrated Mumford conjecture states that these classes generate the stable cohomology of curves.

**Theorem 3.4** (Mumford's Conjecture). The stable cohomology ring of curves is isomorphic to the polynomial algebra generated by the classes  $\kappa_i$ 

$$H^*_{stab}(M,\mathbb{Q}) \cong \mathbb{Q}[\kappa_1,\kappa_2,\ldots].$$

One of the major achievements of the last few years has been the proof of Mumford's conjecture by the efforts of Madsen, Weiss, Ullrike, Tillman, Galatius among many others. For proofs, references and discussion consult Madsen and Weiss' paper math.AT/0212321, [MW], [MT] and [Gal]. The proof is well-beyond the techniques developed in this class.

**Problem 3.5.** Harer's vanishing results and Mumford's conjecture allows us to understand the cohomology of  $M_g$  in a certain range. Note however that the computation of the Euler characteristic suggests that the dimension of the cohomology groups grow more than exponentially. The fact that the Euler characteristic is often negative means that  $M_g$  has a lot of odd cohomology. Construct odd cohomology classes on  $M_g$ . Construct cohomology classes on  $M_g$  in general. In particular, are there constructions that would explain the more than exponential growth of the Euler characteristic? Despite the incredible efforts of many mathematicians our knowledge of the cohomology of  $M_g$  remains fairly limited.

4. Some small homology groups of the moduli space of curves

In this section we will give a rough sketch of Harer's celebrated theorem

Theorem 4.1. 
$$H_2(Map_{q,n}^r; \mathbb{Z}) = \mathbb{Z}^{n+1}; g \geq 5.$$

We will later give an algebraic proof of this result due to Arbarello and Cornalba. By a theorem of Mumford  $Pic(M_{g,n}) \cong H^2(Map_{g,n})$ , where  $Pic(M_{g,n})$  denotes the Picard group of  $M_{g,n}$ . Hence, Harer's theorem determines the rank of the Picard group of the moduli space. In particular, when n=0 and  $g\geq 5$  the rank of the Picard group of  $M_g$  is one.

4.1. **Preliminaries about the mapping class group.** In this section, following Birman [Bir], we will outline a proof of the fact that the mapping class group of a genus g surface is generated by Dehn twists. In fact, Dehn twists on finitely many simple closed curves suffice to generate the group. Recall that a Dehn twist is the homeomorphism of the surface obtained by cutting the surface along a simple closed curve and re-gluing after a twist of  $2\pi$ .

The proof is by induction on the genus of the surface. We have already encountered the base case in our discussion of the Teichmüller space of the sphere: Every orientation preserving homeomorphism of the sphere is isotopic to the identity. To carry out the induction step we establish that given any orientation preserving homeomorphism h of the surface, there exists a sequence of Dehn twists and a meridian m such that if h is followed by a suitable sequence of Dehn twists, then mstays fixed. By cutting the surface along m we obtain a surface of genus g-1 with two disks  $D_1$ ,  $D_2$  removed. h composed with the sequence of Dehn twists gives rise to a homeomorphism of the genus g-1 surface with the disks removed. This homeomorphism extends to a homeomorphism  $\hat{h}$  of the genus g-1 surface that fixes an interior point in each disc. We patch discs to the holes. h is the identity on the boundary of the discs, so we can extend it to the disc. There is a natural surjective homomorphism from the mapping class group of a surface of genus q-1with two marked points to the mapping class group of a surface of genus g-1. The kernel is a braid group that can be shown to be generated by Dehn twists. The result follows by induction. There remains to exhibit a meridian that is fixed when h is followed by a suitable sequence of Dehn twists.

First, observe that if two simple closed curves are isotopic, then the Dehn twists generated by the two curves are isotopic. Next observe that if two simple closed curves  $C_1$  and  $C_2$  intersect at exactly one point, then there exists (up to a homeomorphism isotopic to the identity) a Dehn twist that takes one to the other. Act on  $C_1$  by the Dehn twist generated by  $C_2$ . This adds a copy of  $C_2$  to  $C_1$ , now follow this with a Dehn twist on  $C_1$  with the appropriate orientation. To state the main lemma we need a definition. Two paths p and q have **algebraically zero** intersection if they intersect at exactly two points and if it is possible to orient p so that p has different directions with respect to a given orientation of q at the points of intersections. The key lemma is:

**Lemma 4.2.** Let p be a simple closed path and let m be a simple path on a surface of genus g. Let N be a regular neighborhood of m. Then there exists a path u on the surface that lies in  $p \cup N$ , is related to p by a sequence of Dehn twists and has either zero or algebraically zero intersection with m.

*Proof.* The proof is by induction on the cardinality of intersection between p and m. If p and m do not intersect, then we can take u to be p. If p and m intersect at exactly one point and m is closed, then p and m are related by Dehn twists. Hence we can take u to be m, but we isotope it slightly in the neighborhood so that it actually becomes disjoint from m. If m is not closed, we can isotope it off p by an isotopy that is the identity outside  $N \cup p$ . To complete the induction we assume that the lemma holds whenever the cardinality of intersection between p and m is less than k. We have to consider two cases. The first is, if we orient p and m, then there are two adjacent points of intersection on m with the same orientation. In this case we take two points slightly off m in the neighborhood N (see Figure 3) and consider a curve that goes close to p and intersects m once in a neighborhood. Doing a Dehn twist in this curve allows one to reduce the number of intersections. The induction hypothesis applies.

The second case we have to consider is the case when there are no two adjacent points with the same orientation. In this case choose three adjacent points of intersection on m such that the middle one has different orientation then the outer ones. Choose a curve that intersects m at one point in the neighborhood and is very close to p elsewhere. A Dehn twist in this curve allows us to reduce the number of intersection. We are done by the induction hypothesis.

The lemma has an immediate strengthening from the case of a single m to finitely many disjoint  $m_i$ . We are interested in this lemma since meridians satisfy the hypotheses.

**Lemma 4.3.** Let p be a simple closed path and let  $m_1, \dots, m_r$  be disjoint, simple paths, then there exists a path u which is related to p by a sequence of Dehn twists and has zero or algebraically zero intersection with each of the  $m_i$ .

Choose mutually distinct neighborhoods of the paths  $m_i$  and apply the previous lemma multiple times. Note that if at some step we have  $p_i$  which has algebraically zero intersection with  $m_j$  for  $j \leq i$  repeating the process of the previous lemma may result in changing an algebraically zero intersection to one intersection. We can always eliminate that case using the technique described in the beginning of the proof of the previous lemma.

**Lemma 4.4.** Let h be an orientation preserving homeomorphism of the genus g surface, let p be the image of the meridian  $m_1$ . Then there exists a simple closed curve v related to p by a sequence of Dehn twists such that v does not intersect any of the other meridians,  $v \cap m_i = \emptyset$  and the intersection of v with curves  $d_i$  that cut the genus g surface into tori is either zero or algebraically zero. (see figure 2) Moreover, v is related to  $m_1$  by a sequence of Dehn twists. Consequently, p is related to  $m_1$  by a sequence of Dehn twists.

*Proof.* By the previous lemma we can choose u so that the intersection of u with  $m_i$  and  $d_i$  is either zero or algebraically zero. If u intersects  $m_j$ , then it must also intersect  $d_j$ .  $d_j$  bounds a torus. If u did not intersect  $d_j$ , in this torus u would either have to intersect itself or it would bound a disc. Neither can happen since the original meridian did not have these properties and these are properties invariant under a homeomorphism. Now it is not hard to push u off  $m_j$  by finding a disc that u and  $m_j$  bound. Repeating for every j we obtain the desired curve v. To see that v is related to  $m_1$  by Dehn twists, remove the g meridians to obtain a

sphere with 2g holes. v must separate the sphere, but since v is non-separating in the surface it must bound a boundary component. v intersects a simple closed curve  $a_k$  going once around a hole in the original surface. We can assume that the cardinality of intersection is one (or we can reduce it to that case by a sequence of Dehn twists and isotopies.) We conclude that v is related to  $a_k$  by a Dehn twist. Finally choosing a curve that intersects  $a_k$  and  $m_1$  once we see that v is related to  $m_1$  by Dehn twists. This completes the proof that the mapping class group is generated by Dehn twists.

4.2. Computation of  $H_1(Map)$ . In this subsection using the fact that the mapping class group is generated by Dehn twists we will prove that the first homology group of the mapping class group with  $\mathbb{Z}$  coefficients vanishes when the genus is bigger than 2. First, recall the basic definitions of group homology. Let  $\mathbb{Z}G$  denote the group ring and let B be a right  $\mathbb{Z}G$  module. The n-th homology group with coefficients in A is defined to be

$$H_n(G, A) = Tor_n^{\mathbb{Z}G}(A, \mathbb{Z}),$$

where  $\mathbb{Z}$  is regarded as a trivial  $\mathbb{Z}G$  module. More explicitly, take a  $\mathbb{Z}G$ -projective resolution of the trivial  $\mathbb{Z}G$  module  $\mathbb{Z}$ .

$$\cdots P_2 \to P_1 \to P_0 \to 0, \ H_0(P) \cong \mathbb{Z}$$

Tensor this complex over  $\mathbb{Z}G$  by A to obtain the complex

$$\cdots \to P_1 \otimes_{\mathbb{Z}G} A \to P_0 \otimes_{\mathbb{Z}G} A \to 0$$

The n-th homology group of G with A coefficients is the n-th homology group of this complex. It is a fact that this group is independent (up to canonical isomorphism) of the chosen projective resolution. It is useful to have explicit descriptions of the groups  $H_0$  and  $H_1$ . First, observe that by the right exactness of the tensor product, we conclude that

$$H_0(G,A) \cong A \otimes_{\mathbb{Z}G} \mathbb{Z}.$$

The kernel of the map  $\mathbb{Z}G \to \mathbb{Z}$  sending an element of G to 1 is called the augmentation ideal IG and as a free group it is generated on the set

$$S = \{x - e | x \neq e \in G\}.$$

Since the G action on  $\mathbb Z$  is trivial, we can write

$$A \otimes_{\mathbb{Z}G} \mathbb{Z} = A/(A \circ IG).$$

To compute  $H_1(G,\mathbb{Z})$ , we take the free resolution of  $\mathbb{Z}$  given by

$$0 \to IG \to \mathbb{Z}G \to \mathbb{Z} \to 0$$

The long exact sequence of homology

$$0 \to H_1(G, \mathbb{Z}) \to A \otimes_{\mathbb{Z}G} IG \xrightarrow{i} A \to H_0(G, \mathbb{Z}) \to 0$$

implies that  $H_1(G,\mathbb{Z}) \cong A \otimes_{\mathbb{Z}G} IG$ . Here we used the facts that the higher homology groups of free modules vanish and that i is trivial. Recalling that G acts trivially on  $\mathbb{Z}$  we obtain

$$H_1(G,\mathbb{Z}) = \mathbb{Z} \otimes_{\mathbb{Z}G} IG = IG/(IG)^2.$$

The latter group is isomorphic to the quotient of G by its commutator subgroup. We conclude from this discussion that the first homology group of G with integer coefficients is isomorphic to the abelianization of the group. In this section whenever

I omit the coefficients I mean homology with integer coefficients. Having mentioned the facts we will use from group homology, we can compute the first homology of the mapping class group.

**Proposition 4.5.**  $H_1(Map_{a,n}^r) = 0$  for  $g \geq 3$  and r, n arbitrary.

*Proof.* We will show that the abelianization of  $Map_{g,n}^r$  is trivial for  $g \geq 3$  by exhibiting relations among the Dehn twists that generate it. We will show these relations by explicit calculation on a sphere  $S_4$  with four discs removed. We will conclude that they also hold on  $\Sigma_{g,n}^r$  by embedding  $S_4$  into  $\Sigma_{g,n}^r$ , which we can do when  $g \geq 3$ .

Take a sphere and remove four discs. Label the boundary components as  $C_0, \dots, C_3$ . Let  $\tau_i$  denote the Dehn twist generated by a curve parallel to the boundary  $C_i$ . Let  $C_{ij}$  denote a curve circling  $C_i$  and  $C_j$ , and let  $\tau_{ij}$  be the Dehn twist on  $C_{ij}$ . In the mapping class group the following relation holds between these Dehn twists:

$$\tau_0 \tau_1 \tau_2 \tau_3 = \tau_{12} \tau_{13} \tau_{23} \tag{8}$$

To prove this relation observe that we can cut  $S_4$  along three arcs to obtain a disc. If we can show that the action of the Dehn twists on the right and left hand sides of equation (2) agree on these arcs, we can conclude that equality holds. This follows from the fact that any orientation preserving homeomorphism of the closed disc fixing the boundary is isotopic to the identity. For the calculation that the action on the arcs agree see Figure 4.

This relation allows us to conclude that the mapping class group is generated by non-separating curves for g > 2. Embed  $S_4$  into the surface of interest such that boundary of one of the discs is the separating curve and the others are not. Then using the relation we can eliminate the disc that is separating. Any non-separating curve can be mapped onto another non-separating curve by an orientation preserving homeomorphism of the surface. Find two canonical systems of generators one system containing one of the curves, the other system containing the other curve. If we cut the surface along these systems, we get a polygonal region. We can find a homeomorphism of the boundary taking one curve to the other. This induces a homeomorphism of the surface. We thus obtain a relation between the Dehn twists of two non-separating curves differing by a homeomorphism h

$$\tau_A = h \tau_B h^{-1}$$
.

It follows that the first homology group is cyclic since we can write all the generators as  $\alpha_i\tau\alpha_i^{-1}$  for a fixed Dehn twist  $\tau$  and some element  $\alpha_i\in\Gamma_{g,n}^r$ . When we abelianize, all the generators become equal. Hence,  $H_1(\Gamma_{g,n}^r)$  is cyclic for  $g\geq 3$ . To show that  $H_1$  is actually zero when  $g\geq 3$ , we use the fact that we can embed  $S_4$  into our surface such that all the seven curves that we considered are non-separating. We then obtain the relation (2) among the seven Dehn twists  $\alpha_i\tau\alpha_i^{-1}$ . Abelianizing we see that  $\tau^4=\tau^3$ . In other words, the abelianization of the mapping class group is trivial. This proves the proposition.

4.3. Construction of the cut system complex. A cut system  $\langle C_i \rangle_{i=1}^g$  on the genus g surface F is the isotopy classes of a collection of g disjoint, simple closed curves such that the complement of these curves  $F - (C_1 \cup \cdots \cup C_g)$  remains connected. There is no ordering or orientation on the curves. Observe that in general there will be infinitely many cut systems on a given surface. Given two

isotopy classes of curves define I(C, C') as the minimum number of intersections among representatives intersecting transversely.

We start building a cell complex X. X has one vertex for each cut system on F. We attach a one cell between vertices that represent cut systems that differ by a simple move. A cut system differs from another cut system by a **simple move** if the two cut systems differ in only one isotopy class and for these  $I(C_i, C_i') = 1$ . For example, on the torus a loop going around the hole once represents a cut system and a loop going around the handle represents another cut system. These cut systems differ by a simple move. There are three basic cycles of simple moves. (See Figure 5) We adjoin a 2-cell each time one of these basic cycles of simple moves occurs. Usually when writing cycles, we omit any isotopy class that remains unchanged. Hatcher and Thurston [HT] proved that the resulting cell complex is connected and simply connected.

The main idea of the proof is to realize cut systems as maximal trees in a graph, where the vertices of the graph correspond to the critical points of a  $C^{\infty}$  function and the edges correspond to the connected components of the function's level sets. Then drawing paths in the space of  $C^{\infty}$  functions they are able to show that X is connected. Using a careful analysis of how non-degenerate critical points can change if a family of functions has a specified type of degenerate critical point, they show that one can contract any loop. Since the details are involved we will omit them here.

The mapping class group  $\Gamma$  acts on the complex X by

$$[w] < C_i > = < w(C_i) > .$$

Observe that since the cells are determined solely by configurations of simple closed curves on F, this action extends to the whole complex. Unfortunately the cell complex X is too large to work with. The next step is to select a Map invariant simply connected subcomplex of X whose combinatorics we can control.

The definition is complicated. First, among the two cells corresponding to the  $R_1$  cycles we pick a subset corresponding to the Map orbit of the cycles where the changing isotopy classes correspond to  $\alpha_1, \beta_1, \gamma_i$  and the fixed ones correspond to  $\alpha_i, 2 \leq i \leq g$ . (See Figures 6 and 7.) We take all the two cells corresponding to  $R_2$  cycles. Finally, we take the Map orbit of the  $R_3$  cycle shown in the figure. By definition this subcomplex  $Y_2$  is invariant under the action of the mapping class group. The main theorem is that  $Y_2$  like X is simply connected. The proof proceeds by showing that  $Y_2$  has enough cells of each type so that when contracting any loop contained in  $Y_2$  one can stay within  $Y_2$  and does not have to use any other cells in X. Finally, by adding two types of three cells Harer constructs a 3-complex  $Y_3$ . See figures for a description of these three cells. We thus obtain a simply connected 3complex on which the mapping class group acts. The construction has been carried out in such a way that the action of the mapping class group decomposes into orbits since an orientation preserving homeomorphism cannot take a specific type of curve configuration to another. Moreover, we have a precise description of an element in each orbit. This allows us to compute stabilizers and compute homology groups.

4.4. The calculation of  $H_2(Map)$ . Until we explicitly remove the assumptions, we will assume that  $g \geq 5$ , n = 0 and  $r \geq 1$ . We will often write Map instead of  $Map_{g,n}^r$ . Let B be a CW complex and a K(Map,1). In other words, B has trivial higher homotopy groups and  $\pi_1(B) = Map$ . Let E be the universal cover of B. Consider the fiber product  $\Delta = E \times_{Map} Y_3$ . Recall that the fiber product is the quotient of the Cartesian product under the equivalence relation  $(eg, y) \sim (e, gy)$ . There is a natural projection from E to E is given by  $\tilde{p}(e, y) = p(e)$ , where E is the projection map from E to E. The fiber of this projection is E is simply connected and E is a E is a E in E in E is a fibration allows us to conclude that E is a E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in E in

$$H_3(Map) \to H_2(\tilde{\Delta}) \to H_2(\Delta) \xrightarrow{\phi} H_2(Map) \to 0.$$

Here  $\tilde{\Delta}$  denotes the universal cover of  $\Delta$  and all the homology groups are with integer coefficients. Harer computes the image of  $\phi$  in the above sequence as  $\mathbb{Z}$ . Since the map is surjective this shows that  $H_2(Map)$  is  $\mathbb{Z}$ .

Using the cellular chain complexes we have for  $Y_3$  and E we can obtain a cellular complex for  $\Delta$ . Let  $(C_*, \partial_*^C)$  be the cellular chain complex of  $Y_3$  and  $(K^*, \partial_*^K)$  be the cellular chain complex of E. Form the tensor product of these chain complexes over the group ring of Map. Denote the resulting chain complex by  $(M_*, \partial_*^M)$ . Explicitly, M is given by

$$M_k = \bigoplus_{i+j=k} C_i \otimes_{\mathbb{Z}Map} K_j.$$

As usual the differential is

$$\partial_k^M = (\oplus(\partial_i^C \otimes_{\mathbb{Z}Map} 1_{K_{k-i}})) + (\oplus(1_{C_i} \otimes_{\mathbb{Z}Map} (-1)^i \partial_{k-i}^K))$$

There is a natural filtration on the chain complex  $(M_*, \partial_*^M)$  given by

$$F_p(M_k) = \bigoplus_{i+j=k,i < p} C_i \otimes_{\mathbb{Z}Map} K_j.$$

This gives rise to a spectral sequence which abuts to

$$E_{p,q}^{\infty} = \frac{F_p H_{p+q}(\Delta)}{F_{p-1} H_{p+q}(\Delta)},$$

where  $F_p$  is the filtration of  $H_*(\Delta)$  obtained by taking the images of  $H_{p+q}(E \times_{\Gamma} Y_p)$  in  $H_{p+q}(\Delta)$  arising from the inclusion of  $E \times_{Map} Y_p$  in  $\Delta$ .

The main observation is that Map cannot take a given cell of  $Y_3$  to any arbitrary cell of  $Y_3$ . Map acts transitively on the zero cells. This follows from the fact that  $Y_2$  is connected. We can choose a path along the one skeleton going from one cut system to another. As we discussed above, there is a sequence of Dehn twists that takes a curve  $\alpha$  to a curve  $\beta$  when  $\alpha$  intersects  $\beta$  exactly once. This sequence does not affect any of the other curves in the cut system. Finally, any  $R_2$  type cell can be taken to any other one by Map. Using this information we can obtain a description of the decomposition of  $C_p$ , the p-th graded piece in the cell complex of Y into orbits of Map. For zero-cells we only need to take the zero-cell  $\sigma_0$  corresponding to  $\alpha_1, \alpha_2, \cdots, \alpha_g > 0$ . To make the notation less cumbersome we omit the  $\alpha_i$  that do not change from the notation. For one cells we only need to take the 1-cell  $\sigma_1$  given by  $\alpha_1 > 0$ . For the two cells of type  $\alpha_1 > 0$ .

need the  $\sigma_2^i$  corresponding to  $<\alpha_1>-<\beta_1>-<\gamma_i>-<\alpha_1>$  for each  $\gamma_i$ ,  $1\leq i\leq N$ . For the two cell of type  $R_2$  we need to include  $\sigma_2^{N+1}$  corresponding to  $<\alpha_1,\alpha_2>-<\beta_1,\alpha_2>-<\beta_1,\beta_2>-<\alpha_1,\beta_2>$ . Finally, for the 2-cell of type  $R_3$  take  $\sigma_2^{N+2}$ . (See figure 7) For our two types of 3-cells take  $\sigma_3^1$  and  $\sigma_3^2$  as pictured.

The action of Map on  $C_p$  splits as

$$C_p = C(\sigma_p^1) \oplus \cdots \oplus C(\sigma_p^{n_p})$$

where  $C(n_p^i)$  denotes the Map orbit of the p-cell  $\sigma_p^i$ . Let  $\Gamma_p^i$  denote the stabilizer of  $\sigma_p^i$ . Then we can view  $C_p^i$  as

$$C_p^i = \mathbb{Z}Map \otimes_{\mathbb{Z}\Gamma_p^i} \mathbb{Z}.$$

This allows us to describe the  $E^1$  term of the spectral sequence as

$$E_{n,q}^1 = \bigoplus_i H_q(\Gamma_n^i, \langle \sigma_n^i \rangle).$$

Recall that  $H_0$  was given as  $\mathbb{Z}\otimes_{\mathbb{Z}\Gamma_p^i}<\sigma_p^i>$ . To compute the various  $H_0$  we need to know how  $\Gamma_p^i$  acts on  $<\sigma_p^i>$ . It is clear that  $\Gamma_0$  acts trivially on the single point  $<\sigma_0>$ . We conclude that  $H_0(\Gamma_0,<\sigma_0>)\cong\mathbb{Z}$ .  $\Gamma_1$  can interchange  $\alpha_1$  and  $\beta_1$ , so it contains an element that reverses the orientation of the 1-cell  $<\sigma_1>$ . From this we can conclude that  $H_0(\Gamma_1,<\sigma_1>)\cong\mathbb{Z}/2\mathbb{Z}$  since  $1\otimes_{\mathbf{Z}\Gamma_0}m=1\otimes_{\mathbb{Z}\Gamma_0}-m$  because of the flip. Harer observes (?) that  $\Gamma_2^i$  for  $1\leq i\leq N$  acts trivially on  $<\sigma_2^i>$ . It follows that  $H_0(\Gamma_2^i,<\sigma_2^i>)=\mathbb{Z}$ .  $\Gamma_2^{N+1}$  contains an orientation reversing element given by switching  $\alpha_1$  and  $\beta_1$ . We conclude that  $H_0(\Gamma_2^{N+1},<\sigma_2^{N+1}>)\cong\mathbb{Z}/2\mathbb{Z}$ .  $\Gamma_2^{N+2}$  and  $\Gamma_3^1$  act trivially on  $<\sigma_2^{N+2}>$  and  $<\sigma_3^1>$ , respectively. Hence their homology groups are isomorphic to  $\mathbb{Z}$ .  $\Gamma_3^2$  on the other hand has an orientation reversing element, hence its homology group is  $\mathbb{Z}/2\mathbb{Z}$ . This allows us to determine  $E_{p,0}^2$  as

$$E_{0,0}^2 \cong \mathbb{Z}, \ E_{1,0}^2 = E_{3,0}^2 = 0, \ E_{2,0}^2 \cong \mathbb{Z}^N \oplus \mathbb{Z}/2\mathbb{Z}$$

The next step is to describe the subgroup  $\hat{\Gamma}_0$  of  $\Gamma_0$  that fixes the curves which determine  $\sigma_0$  pointwise. There is an explicit description of  $\hat{\Gamma}_0$ .  $\hat{\Gamma}_0 \cong P_{2g+r-1} \times \mathbb{Z}^{g+r-1}$ .  $\hat{\Gamma}_0$  is isomorphic to the direct product of the pure braid group on 2g+r-1 strings and the free abelian group generated by Dehn twists on the  $\alpha_i$  and on r-1 curves parallel to the r-1 boundary components  $\Delta_{r-1}$ . On the other hand, the group of symmetries of  $\sigma_0$  is the group of signed permutations  $\pm \Sigma_g$  on g elements since the  $\alpha_i$  can be permuted among each other and their orientations might be reversed. In other words, there is a short exact sequence

$$1 \to \hat{\Gamma}_0 \to \Gamma_0 \to \pm \Sigma_g \to 1$$

Given a short exact sequence of groups there is a spectral sequence, the Lyndon-Hochschild-Serre spectral sequence, which relates the homology of the groups.

Theorem 4.6 (Lyndon-Hochschild-Serre). Given a short exact sequence of groups

$$1 \to K \to G \to Q \to 1$$

and a  $\mathbb{Z}G$  module M, there exists a first quadrant spectral sequence with

$$E_{p,q}^2 = H_p(Q, H_q(K, M))$$

and converging strongly to  $H_*(G, M)$ .

A corollary of the spectral sequence is the existence of an exact sequence

$$H_2(G) \to H_2(Q) \to K/[G,K] \to H_1(G) \to H_1(Q) \to 0$$

Applying this exact sequence to our short exact sequence allows us to conclude that  $H_1(\Gamma_0) \cong \mathbb{Z}^{N-1} \oplus \mathbb{Z}/2\mathbb{Z}$ . Here one uses an explicit presentation of the pure braid group to compute  $H_1(\hat{\Gamma}_0)$ .  $H_1(G_0)$  is the Klein 4 group. One can see this by abelianizing  $\pm \Sigma_g$ . This computation also identifies  $E_{2,0}^3$  of our original spectral sequence as  $\mathbb{Z}$ . To complete the computation Harer identifies  $\phi(F_0(H_2(\Delta)))$  and  $\phi(F_1(H_2(\Delta)))$  as 0, where  $\phi$  is the map whose image we are trying to identify and  $F_p(H_2(\Delta))$  is the filtration described in the beginning of this section. This proves that  $\phi: H_2(\Delta) \to H_2(Map)$  is surjective.

There remains to remove the restrictions on the number of marked points and the number of boundary components. From now on we remove the global assumptions we made in the beginning of the section. There is an exact sequence that relates  $Map_{g,n}^{r-1}$  to  $Map_{g,n+1}^{r-1}$  when  $r\geq 1$ . Attach a disc to the r-th boundary component and make its center a marked point. Then  $Map_{g,n}^{r}$  surjects onto  $Map_{g,n+1}^{r-1}$  since any orientation preserving homeomorphism restricted to the added disc is isotopic to the identity with an isotopy that fixes the center. The kernel of the map is generated by a Dehn twist parallel to the boundary of the r-th component. We obtain the exact sequence

$$1 \to \mathbb{Z} \to Map^r_{q,n} \to Map^{r-1}_{q,n+1} \to 1$$

The Lyndon-Hochschild-Serre spectral sequence allows Harer to conclude inductively that  $H_2(Map_{g,n}^r) \cong \mathbb{Z}^{n+1}$ . This settles the theorem except when the surface has no boundary components and no marked points. In this case we have to use a different exact sequence instead. There is a surjection from  $Map_{g,1}$  to  $Map_g$  obtained by forgetting the marked point. (We omit the indices that are equal to 0.) This is a surjection since any orientation preserving homeomorphism is isotopic to one that fixes the marked point. The kernel of the map is isomorphic to the fundamental group of the surface. We obtain an exact sequence

$$1 \to \pi_1(F_g) \to Map_{g,1} \to Map_g \to 1$$

and the Lyndon-Hochschild-Serre spectral sequence becomes available as a tool.

### References

- [Ab] W. Abikoff. The real analytic theory of Teichmüller space, volume 820 of Lecture Notes in Mathematics. Springer, Berlin, 1980.
- [Bir] J. S. Birman. Braids, links, and mapping class groups. Princeton University Press, Princeton, N.J., 1974. Annals of Mathematics Studies, No. 82.
- [Gal] S. Galatius. Mod p homology of the stable mapping class group. Topology 43(2004), 1105– 1132.
- [Har1] J. Harer. The second homology group of the mapping class group of an orientable surface. Invent. Math. 72(1983), 221–239.
- [Har2] J. L. Harer. Stability of the homology of the mapping class groups of orientable surfaces. Ann. of Math. (2) 121(1985), 215–249.
- [Har3] J. L. Harer. The virtual cohomological dimension of the mapping class group of an orientable surface. *Invent. Math.* 84(1986), 157–176.
- [Har4] J. L. Harer. The cohomology of the moduli space of curves. In Theory of moduli (Montecatini Terme, 1985), volume 1337 of Lecture Notes in Math., pages 138–221. Springer, Berlin, 1988.

- [HZ] J. L. Harer and D. Zagier. The Euler characteristic of the moduli space of curves. Invent. math.~85(1986),~457-485.
- [HT] A. Hatcher and W. Thurston. A presentation for the mapping class group of a closed orientable surface. Topology 19(1980), 221–237.
- [IT] Y. Imayoshi and M. Taniguchi. An Introduction to Teichmüller Spaces. Springer-Verlag, 1992.
- $[\mathrm{Le}] \hspace{0.5cm} \text{O. Lehto.} \hspace{0.1cm} \textit{Univalent functions and Teichm\"{u}ller spaces.} \hspace{0.1cm} \text{Springer-Verlag, 1987.}$
- [MT] I. Madsen and U. Tillmann. The stable mapping class group and  $Q(\mathbb{C}_+^{\infty})$ . Invent. Math. **145**(2001), 509–544.
- [MW] I. Madsen and M. Weiss. The stable mapping class group and stable homotopy theory. In *European Congress of Mathematics*, pages 283–307. Eur. Math. Soc., Zürich, 2005.

---

### THE KONTSEVICH MODULI SPACES OF STABLE MAPS

- 1. The Kontsevich moduli space of stable maps.
- 1.1. **Preliminaries.** We will begin with a detailed study of the Kontsevich moduli spaces of stable maps to  $\mathbb{P}^r$ . These spaces can be defined much more generally. However, we will have very little to say about the general situation. We will mostly concentrate on the case of genus zero maps to  $\mathbb{P}^r$ . The best introduction to Kontsevich moduli spaces is [FP] where you can find details about the construction of the space.

**Definition 1.1.** Let X be a smooth projective variety. Let  $\beta \in H_2(X,\mathbb{Z})$  denote the class of a curve. The Kontsevich moduli space  $\overline{M}_{g,n}(X,\beta)$  of n-pointed, genus g stable maps to X in the class parameterizes isomorphism classes of the following data

- (1)  $(C, p_1, \ldots, p_n, f)$  an at worst nodal curve C of arithmetic genus g with n distinct, smooth points  $p_1, \ldots, p_n$  of C and a morphism  $f: C \to X$  such that  $f_*[C] = \beta$ ,
- (2) The map is required to be stable; that is if f is constant on any component of C, then that component is required to have at least 3 distinguished points. The distinguished points are either marked points, or points lying over nodes in the normalization of the curve.

We have already encountered some examples of Kontsevich moduli spaces.

**Example 1.2.** The moduli space of stable maps to a point coincides with the moduli space of curves:

$$\overline{\mathrm{M}}_{g,n}(\mathbb{P}^0,0) \cong \overline{\mathrm{M}}_{g,n}.$$

**Example 1.3.** The moduli space of degree zero stable maps, similarly, is easy to describe.

$$\overline{M}_{g,n}(X,0) = \overline{M}_{g,n} \times X.$$

Since a degree 0 map from a connected curve is determined by specifying a point on X, this identification is immediate.

**Example 1.4.** The moduli space of degree one maps to  $\mathbb{P}^r$  is isomorphic to the Grassmannian:

$$\overline{M}_{0,0}(\mathbb{P}^n,1) = G(2,n+1) = \mathbb{G}(1,n).$$

A generalization of this example is the moduli space of degree one maps to a smooth quadric hypersurface Q in  $\mathbb{P}^n$  for n > 3. In that case the Kontsevich moduli space is isomorphic to the orthogonal Grassmannian.

**Example 1.5.** The Kontsevich moduli space  $\overline{M}_{0,0}(\mathbb{P}^2,2)$  is isomorphic to the space of complete conics or alternatively it is isomorphic to the blow up of the Hilbert scheme of conics in  $\mathbb{P}^2$  along the Veronese surface of double lines.

**Exercise 1.6.** Prove the previous assertion by exhibiting a map (using the universal property of complete conics) from  $\overline{M}_{0,0}(\mathbb{P}^2,2)$  to the space of complete conics. Check that this is a bijection on points. The claim then follows from Zariski's Main Theorem once we know that  $\overline{M}_{0,0}(\mathbb{P}^2,2)$  is smooth.

The main existence theorems for Kontsevich moduli spaces are the following. We refer you to [FP] for their proof.

**Theorem 1.7.** If X is a complex, projective variety, then there exists a projective coarse moduli scheme  $\overline{M}_{q,n}(X,\beta)$ .

Note that even when X is a nice, simple variety (such as  $\mathbb{P}^2$ ),  $\overline{\mathrm{M}}_{g,n}(X,\beta)$  may have many components of different dimensions.

Example 1.8. Consider the Kontsevich moduli space  $\overline{\mathrm{M}}_{1,0}(\mathbb{P}^2,3)$  of genus one degree three stable maps to  $\mathbb{P}^2$ . This space has three components: two of dimension 9 and one of dimension 10. Naively, we might expect an open subset of  $\overline{\mathrm{M}}_{1,0}(\mathbb{P}^2,3)$  to parameterize smooth cubic curves in  $\mathbb{P}^2$ . Indeed an open subset of one of the components does so. However, there is a second component whose general member is a map from a reducible curve with a genus zero component and a genus one component to  $\mathbb{P}^2$  that contracts the genus one component and gives a degree three map on the genus zero component. Note that this component of  $\overline{\mathrm{M}}_{1,0}(\mathbb{P}^2,3)$  has dimension 10. The dimension of rational cubics in  $\mathbb{P}^2$  is 8, but the moduli of the contracted elliptic curve and the point of attachment add two more moduli. Similarly, one obtains a third component of dimension 9 by considering maps from elliptic curves with two rational tails which contract the elliptic curve and map the rational tails as a line and a conic.

**Example 1.9.** Even if we restrict ourselves to genus zero stable maps the Kontsevich moduli spaces may have many components of different dimensions. Consider degree two genus zero stable maps to a smooth degree seven hypersurface X in  $\mathbb{P}^7$ . Assume that X contains a  $\mathbb{P}^3$ .  $\overline{\mathrm{M}}_{0,0}(X,2)$  contains at least two components. One component covers X and has dimension 5. The conics in the  $\mathbb{P}^3$  give a different component of dimension 8.

In order to obtain an irreducible moduli space with mild singularities one needs to impose some conditions on X. One possibility is to require that X is convex. Recall that a variety X is convex if for every map

$$f: \mathbb{P}^1 \to X$$
,

 $f^*T_X$  is generated by global sections. Since every vector bundle on  $\mathbb{P}^1$  decomposes as a direct sum of line bundles, a variety is convex if for every map

$$f: \mathbb{P}^1 \to X$$

the summands appearing in  $f^*T_X$  are non-negative. If we consider genus zero stable maps to convex varieties, the Kontsevich moduli space has very nice properties.

**Theorem 1.10.** Let X be a smooth, projective, convex variety.

(1)  $\overline{M}_{0,n}(X,\beta)$  is a normal, projective variety of pure dimension

$$\dim(X) + c_1(X) \cdot \beta + n - 3.$$

- (2)  $\overline{M}_{0,n}(X,\beta)$  is locally the quotient of a non-singular variety by a finite group. The locus of automorphism free maps is a fine moduli space with a universal family and it is smooth.
- (3) The boundary is a normal crossings divisor.

Observe that the previous theorem in particular applies to homogeneous varieties since homogeneous varieties are convex. In fact, if X is a homogeneous variety, then  $\overline{\mathrm{M}}_{0,n}(X,\beta)$  is irreducible (see [KP]).

**Remark 1.11.** Although when we do not restrict ourselves to the case of genus zero maps to homogeneous varieties Kontsevich moduli spaces may be reducible with components of different dimensions,  $\overline{\mathrm{M}}_{g,n}(X,\beta)$  possesses a virtual fundamental class of the expected dimension. The existence of the virtual fundamental class is the key to Gromov-Witten Theory.

Requiring a variety to be convex is a strong requirement on uniruled varieties. For instance, the blow-up of a convex variety ceases to be convex. In fact, I do not know any examples of rationally connected, projective convex varieties that are not homogeneous.

**Problem 1.12.** Is every rationally connected, convex projective variety a homogeneous space? Either prove that it is or give counterexamples.

1.2. Kontsevich's count of rational curves. The Kontsevich moduli space is endowed with n evaluation morphisms

$$ev_i: \overline{M}_{q,n}(X,\beta) \to X,$$

where  $ev_i$  sends the point  $(C, p_1, \ldots, p_n, f)$  to  $f(p_i) \in X$ .

From now on we will assume that X is a homogeneous variety and we will always restrict ourselves to the case of genus zero curves. Given the classes  $\gamma_1, \ldots, \gamma_n$  of algebraic subvarieties of X, we can construct a class on  $\overline{M}_{0,n}(X,\beta)$  by pulling them back via the evaluation morphisms and cupping:

$$ev_1^*(\gamma_1) \cup \cdots \cup ev_n^*(\gamma_n).$$

If the codimension of the classes add up to

$$\dim(X) + c_1(X) \cdot \beta + n - 3,$$

then we can define  $I_{\beta}(\gamma_1, \dots, \gamma_n)$ , the Gromov-Witten invariant of X associated to the curve class  $\beta$  and cohomology classes  $\gamma_1, \dots, \gamma_n$  as follows:

$$I_{\beta}(\gamma_1, \dots, \gamma_n) = \int_{\overline{\mathrm{M}}_{0,n}(X,\beta)} ev_1^*(\gamma_1) \cup \dots \cup ev_n^*(\gamma_n).$$

**Remark 1.13.** We can still define Gromov-Witten invariants for arbitrary, smooth projective varieties and higher genus curves. In that case we have to evaluate the product over the virtual fundamental class  $[\overline{\mathrm{M}}_{g,n}(X,\beta)]^{\mathrm{virt}}$  instead of  $\overline{\mathrm{M}}_{0,n}(X,\beta)$ .

The relation between Gromov-Witten invariants and enumerative geometry is established via the following variant of Kleiman's Transversality Theorem.

**Lemma 1.14.** Let X be a homogeneous variety G/P. Let  $\Gamma_1, \ldots, \Gamma_n$  be irreducible subvarieties of X with classes  $\gamma_1, \ldots, \gamma_n$ . Let  $g_1 \cdots, g_n \in G$  be general elements, then the scheme theoretic intersection

$$\rho_1^{-1}(g_1\Gamma_1)\cap\cdots\cap\rho_n^{-1}(g_n\Gamma_n)$$

is a finite number of reduced points supported in  $M_{0,n}(X,\beta)$  and the Gromov-Witten invariant equals the cardinality of this set

$$I_{\beta}(\gamma_1, \dots, \gamma_n) = \# \rho_1^{-1}(g_1 \Gamma_1) \cap \dots \cap \rho_n^{-1}(g_n \Gamma_n).$$

**Example 1.15.** In this example we derive Kontsevich's recursive formula for the number of rational plane curves of degree d that contain 3d-1 general points. We begin by giving a geometric argument. We will then see how quantum cohomology gives the same answer formally. Define  $N_e$  to be the number of rational plane curves of degree e that contain 3e-1 general points. Consider 3d pointed stable maps of degree d to  $\mathbb{P}^2$  that map the points marked by  $p_1, \ldots, p_{3d-2}$  to fixed general points of  $\mathbb{P}^2$ . Fix also two general lines  $l_1, l_2$  and require  $p_{3d-1}$  to map to  $l_1$  and  $p_{3d}$  to map to  $l_2$ . Such stable maps give us a curve C in  $\overline{M}_{0,3d}(\mathbb{P}^2, d)$ .

We will now analyze how C intersects the boundary divisors of  $\overline{\mathrm{M}}_{0,3d}(\mathbb{P}^2,d)$ . The main point is that there is a map

$$\pi: \overline{\mathrm{M}}_{0,n}(X,\beta) \to \overline{\mathrm{M}}_{0,4}$$

given by forgetting the map and the marked points but any specified four of the marked points (assuming of course that  $n \geq 4$ ) and then stabilizing. Since the boundary divisors on  $\overline{\mathrm{M}}_{0,4}$  are linearly equivalent, their pull-backs are also linearly equivalent.

Let us apply this discussion to our situation. Consider the map

$$\pi: \overline{\mathrm{M}}_{0.3d}(\mathbb{P}^2,d) \to \overline{\mathrm{M}}_{0.4}$$

as above that forgets all the points but  $p_1, p_2, p_{3d-1}$  and  $p_{3d}$ . The pull-back of the two divisors  $\Delta_{\{p_1, p_{3d-1}\}, \{p_2, p_{3d}\}}$  and  $\Delta_{\{p_1, p_2\}, \{p_{3d-1}, p_{3d}\}}$  are linearly equivalent, hence must intersect our curve C in the same number of points. Let us calculate these two numbers. First,

$$\pi^*\Delta_{\{p_1,p_{3d-1}\},\{p_2,p_{3d}\}} = \sum_{\{i,A \ | \ \{p_1,p_{3d-1}\}\subset A,\{p_2,p_{3d}\}\subset A^c} \Delta_{i,A}$$

where the sum runs over boundary divisors in  $\overline{\mathrm{M}}_{0,3d}(\mathbb{P}^2,d)$  consisting of maps with reducible domain curves such that the marking on one component contains  $p_1, p_{3d-1}$ , but does not contain  $p_2, p_{3d}$  and the map has degree  $d-1 \geq i \geq 1$  on that component. The intersection of this divisor with our curve C is counted by the number of maps from reducible rational curves that have these properties.

Suppose the number of marked point on the component of degree i is larger than 3i, then since more than 3i-1 of these points are required to map to general fixed points of  $\mathbb{P}^2$  by the above dimension count there will not be such maps. On the other hand, if there were fewer than 3i marked points, then the same argument when applied to the other component shows that there are no such maps. We conclude that #A = 3i and  $\#A^c = 3(d-i)$ . Since  $\{p_1, p_{3d-1}\} \subset A, \{p_2, p_{3d}\} \subset A^c$  in order to determine the marking on the degree i component we need to choose 3i-2 points among the 3d-4 points  $p_3, \ldots, p_{3d-2}$ . Once we choose those points,

the number of rational plane curves passing through the 3i-1 points is  $N_i$ . Each curve intersects  $l_1$  in i points, hence the choice of point  $p_{3d-1}$  is i. Similarly the degree d-i component contributes a factor of  $N_{d-i}(d-i)$ . Finally, in order to specify the map we have to specify among the i(d-i) points of intersection between the two components which is the image of the node. We thus get that the total number of points of intersection of our curve C with this divisor is

$$\sum_{1 \le i \le d-1} {3d-4 \choose 3i-2} i^2 (d-i)^2 N_i N_{d-i}.$$

We now calculate the  $C \cdot \pi^* \Delta_{\{p_1, p_2\}, \{p_{3d-1}, p_{3d}\}}$ . We first observe that

$$\pi^* \Delta_{\{p_1, p_2\}, \{p_{3d-1}, p_{3d}\}} = \sum_{\{i, A \mid \{p_1, p_2\} \subset A^c, \{p_{3d-1}, p_{3d}\} \subset A} \Delta_{i, A}$$

where the sum runs over  $0 \le i \le d-1$  and partitions of the marked points so that  $p_{3d-1}, p_{3d}$  are marked points in the domain on which the map has degree i and  $p_1, p_2$  are not on that component. Note that since the images of  $p_1$  and  $p_2$  are distinct, d-i cannot be zero. However, if the curve passes through the intersection point of  $l_1$  and  $l_2$ , then the map may have a contracted component, where  $p_{3d-1}$  and  $p_{3d}$  lie on the component contracted to the point of intersection of  $l_1$  and  $l_2$ . Hence, i may be zero. Keeping this in mind we see that the intersection of C with this divisor is

$$N_d + \sum_{1 \le i \le d-1} {3d-4 \choose 3i-1} i^3 (d-i) N_i N_{d-i}.$$

This is calculated in exactly the same way as above. Since these two divisors are linearly equivalent, the two numbers we calculated have to be equal. We conclude that the number of rational plane curves of degree d containing 3d-1 general points may be recursively determined as follows:

$$N_d = \sum_{1 \le i \le d-1} \left( \binom{3d-4}{3i-2} i^2 (d-i)^2 - \binom{3d-4}{3i-1} i^3 (d-i) \right) N_i N_{d-i}.$$

Of course, we know the first few of these numbers classically

$$N_1 = 1$$
,  $N_2 = 1$ ,  $N_3 = 12$ .

**Exercise 1.16.** Check that  $N_2$  and  $N_3$  follow from the recursion and  $N_1$ . Calculate the next few  $N_d$ .

Exercise 1.17. Verify the details of the calculation above. In particular, carry out the necessary dimension counts that justify the claims made.

**Exercise 1.18.** Find the number of rational curves  $N_{d_1,d_2}$  in the class

$$\mathcal{O}_{\mathbb{P}^1 \times \mathbb{P}^1}(d_1, d_2)$$

on  $\mathbb{P}^1 \times \mathbb{P}^1$  passing through  $2d_1 + 2d_2 - 1$  general points using the same method.

**Problem 1.19.** Is it possible to generalize the previous discussion to other simple rational surfaces such as Hirzebruch surfaces or Del Pezzo surfaces? What kind of new problems arise? Are these surfaces convex?

1.3. The quantum cohomology ring. There is a way of formalizing the calculations we performed in the previous section. One forms a ring called the quantum cohomology ring whose structure constants encode the Gromov-Witten invariants. This ring turns out to be a commutative, associative ring with unit. The type of recursions we determined in the previous section then follows from the associativity relations in the ring.

We first choose a basis for the cohomology ring of the homogeneous variety X. We let  $T_0 = 1, T_1, \ldots, T_m$  denote the divisor classes and  $T_{m+1}, \ldots, T_r$  be an additive basis for the rest of the cohomology ring. There is a natural intersection matrix defined by

$$g_{ij} = \int_X T_i \cup T_j.$$

Let  $g^{ij}$  be the inverse of the intersection matrix. Then the products in the ordinary cohomology ring may be expressed as follows

$$T_i \cup T_j = \sum_{k,l} \left( \int_X T_i \cup T_j \cup T_k \right) g^{kl} T_l = \sum_{k,l} I_0(T_i, T_j, T_k) g^{kl} T_l.$$

The idea is to define a different multiplication structure on the cohomology ring by allowing Gromov-Witten invariants associated to non-zero curve classes as structure constants. Given a class  $\gamma$  in the cohomology ring define the generating function  $\Phi$  by

$$\Phi(\gamma) = \sum_{n \ge 3} \sum_{\beta} \frac{1}{n!} I_{\beta}(\underbrace{\gamma, \dots, \gamma}_{n \text{ times}}).$$

For convenience of notation  $I_{\beta}(\underline{\gamma, \dots, \gamma})$  is abbreviated by  $I_{\beta}(\gamma^n)$ , Setting

$$_{n}$$
 times

$$\gamma = \sum y_i T_i$$

and expanding, the function  $\Phi$  becomes a formal power series in  $\mathbb{Q}[[y_0,\ldots,y_r]]$ 

$$\Phi(y_0, \dots, y_r) = \sum_{n_0 + \dots + n_r \ge 3} \sum_{\beta} I_{\beta}(T_0^{n_0}, \dots, T_r^{n_r}) \frac{y_0^{n_0} \cdots y_r^{n_r}}{n_0! \cdots n_r!}.$$

The third partial derivative of  $\Phi$  with respect to  $y_i, y_j$  and  $y_k$  is

$$\Phi_{ijk} = \frac{\partial^3 \Phi}{\partial y_i \partial y_j \partial y_k} = \sum_{n>0} \sum_{\beta} \frac{1}{n!} I_{\beta}(\gamma^n, T_i, T_j, T_k).$$

**Definition 1.20** (Quantum product). Define a multiplication, called quantum multiplication, on  $A^*(X,\mathbb{Z}) \otimes_{\mathbb{Z}} \mathbb{Q}[[y_0,\ldots,y_r]]$  by setting

$$T_i * T_j = \sum_{k,l} \Phi_{ijk} g^{kl} T_l$$

and extending the multiplication to  $\mathbb{Q}[[y_0,\ldots,y_r]]$ -linearly.

**Theorem 1.21.** Under the quantum multiplication  $A^*(X,\mathbb{Z}) \otimes_{\mathbb{Z}} \mathbb{Q}[[y_0,\ldots,y_r]]$  is a commutative, associative  $\mathbb{Q}[[y_0,\ldots,y_r]]$ -algebra with unit  $T_0$ .

Remark 1.22. The ring we have just defined is sometimes referred to as the big quantum cohomology ring. There is also a small quantum cohomology ring. The structure constants of the small quantum cohomology ring depend only on the three-pointed Gromov-Witten invariants. The definition of the small quantum multiplication differs from that of the big quantum multiplication only in the fact that in the definition of the small quantum cohomology we set the variables corresponding to classes of codimension two or more to zero. More precisely, set

$$\tilde{\Phi}_{ijk} = \Phi_{ijk}(y_0, y_1, \dots, y_m, 0, \dots, 0).$$

Define the small quantum product by

$$T_i * T_j = \sum_{k \ l} \tilde{\Phi}_{ijk} g^{kl} T_l$$

**Example 1.23** (Kontsevich's count revisited). The quantum cohomology ring provides a formalism for deriving enumerative information about varieties. We demonstrate how this works in the case of  $\mathbb{P}^2$ . As a basis of the cohomology of  $\mathbb{P}^2$  we can take  $T_0 = 1$ ,  $T_1 = [\text{line}]$ ,  $T_2 = [\text{point}]$ .

Note that if  $\beta=0$ , the only way a Gromov-Witten invariant can be non-zero is if n=3 and the codimension of the three cycles  $\gamma_1,\gamma_2$  and  $\gamma_3$  sum to the dimension of X. In this case, the Gromov-Witten invariant is the classical intersection

$$I_0(\gamma_1, \gamma_2, \gamma_3) = \int_X \gamma_1 \cup \gamma_2 \cup \gamma_3.$$

Similarly, if one of the cohomology classes is the identity, the Gromov-Witten invariant vanishes unless  $\beta = 0$ , n = 3.

On the other hand, for  $\mathbb{P}^2$  we have that  $I_d(T_1^r, T_2^s) = 0$  unless s = 2d - 1. If s = 3d - 1, then

$$I_d(T_1^r, T_2^{3d-1}) = (rd)N_d.$$

Therefore, we obtain the following expression for the function  $\Phi$ :

$$\Phi(y_0, y_1, y_2) = \frac{y_0^2 y_2}{2} + \frac{y_0 y_1^2}{2} + \sum_{d \ge 1} \sum_{r \ge 0} I_d(T_1^r, T_2^{3d-1}) \frac{y_1^r}{r!} \frac{y_2^{3d-1}}{(3d-1)!}$$

$$= \frac{y_0^2 y_2}{2} + \frac{y_0 y_1^2}{2} + \sum_{d \ge 1} N_d e^{dy_1} \frac{y_2^{3d-1}}{(3d-1)!}.$$

We now express the quantum product of the generators.

$$T_i * T_i = \Phi_{ii0}T_2 + \Phi_{ii1}T_1 + \Phi_{ii2}T_0.$$

Therefore, we have

$$\begin{array}{lcl} (T_1*T_1)*T_2 & = & (T_2+\Phi_{111}T_1+\Phi_{112}T_0)*T_2 \\ & = & \Phi_{221}T_1+\Phi_{222}T_0+\Phi_{111}(\Phi_{121}T_1+\Phi_{122}T_0)+\Phi_{112}T_2 \end{array}$$

On the other hand,

$$T_1 * (T_1 * T_2) = T_1 * (\Phi_{121}T_1 + \Phi_{122}T_0)$$
  
=  $\Phi_{121}(T_2 + \Phi_{111}T_1 + \Phi_{112}T_0) + \Phi_{122}T_1$ 

By the associativity of the quantum cohomology ring the coefficients of  $T_i$  in the two expressions of  $T_1 * T_1 * T_2$  have to be equal. Comparing the coefficients of  $T_0$  (and remembering that taking the partial derivatives of  $\Phi$  is independent of order), we obtain the relation

$$\Phi_{222} = (\Phi_{112})^2 - \Phi_{111}\Phi_{122}.$$

Working out these partial derivatives of  $\Phi$  we obtain the equation

$$\sum_{d\geq 1} N_d e^{dy_1} \frac{y_2^{3d-4}}{(3d-4)!} = \left(\sum_{i\geq 1} N_i i^2 e^{iy_1} \frac{y_2^{3i-2}}{(3i-2)!}\right)^2 - \left(\sum_{i\geq 1} N_i i^3 e^{iy_1} \frac{y_2^{3i-1}}{(3i-1)!}\right) \left(\sum_{i\geq 1} N_i i e^{iy_1} \frac{y_2^{3i-3}}{(3i-3)!}\right)$$

Equating the coefficients it is easy to obtain Kontsevich's recursion

$$N_d = \sum_{1 \le i \le d-1} \left( \binom{3d-4}{3i-2} i^2 (d-i)^2 - \binom{3d-4}{3i-1} i^3 (d-i) \right) N_i N_{d-i}.$$

**Exercise 1.24.** Work out recursion relations for the number of rational curves in the class  $\mathcal{O}_{\mathbb{P}^1 \times \mathbb{P}^1}(d_1, d_2)$  passing through  $2d_1 + 2d_2 - 1$  general points in  $\mathbb{P}^1 \times \mathbb{P}^1$  using the quantum cohomology formalism.

**Exercise 1.25.** Work out recursion relations for the number of rational curves of degree d in  $\mathbb{P}^3$  that contain i general points and intersect 4d-2i general lines using the quantum cohomology formalism.

**Exercise 1.26.** Repeat the following two exercises for other simple varieties such as a smooth quadric threefold, the Grassmannian G(2,4), ...

# 2. Divisor classes on the Kontsevich moduli space and enumerative geometry

In this section following Rahul Pandharipande [Pa] we determine the Picard group of the Kontsevich moduli space. We will then use this knowledge to study the enumerative geometry of rational curves in  $\mathbb{P}^n$ . In particular, we will solve some of the enumerative questions we asked earlier in the course about twisted cubics.

We start by giving the definitions of standard divisor classes.

- (1)  $\mathcal{H}$  is class of the divisor of maps whose images intersect a fixed codimension two linear space in  $\mathbb{P}^r$ . This divisor is defined provided r > 1 and d > 0. Whenever we refer to  $\mathcal{H}$  we assume these conditions hold.
- (2)  $\mathcal{L}_i = ev_i^*(\mathcal{O}_{\mathbb{P}^r}(1))$ , for  $1 \leq i \leq n$ , are the *n* divisor classes obtained by pulling back  $\mathcal{O}_{\mathbb{P}^r}(1)$  by the *n* evaluation morphisms.

(3)  $\Delta_{(A,d_A),(B,d_B)}$  are the classes of boundary divisors consisting of maps with reducible domains. Here  $A \sqcup B$  is any ordered partition of the marked points.  $d_A$  and  $d_B$  are non-negative integers satisfying  $d = d_A + d_B$ . If  $d_A = 0$  (or  $d_B = 0$ ), we require that  $\#A \geq 2$  ( $\#B \geq 2$ , respectively).

**Theorem 2.1** (Pandharipande). Let  $r \geq 2$  and d > 0. The divisor class  $\mathcal{H}$ , the divisor classes  $\mathcal{L}_i$  and the classes of boundary divisors  $\Delta_{(A,d_A),(B,d_B)}$  generate the group of  $\mathbb{Q}$ -Cartier divisors of  $\overline{M}_{0,n}(\mathbb{P}^r,d)$ .

*Proof.* We will prove a more precise version of the theorem and determine the relations between the divisors in the process. For simplicity let

$$P = \operatorname{Pic}(\overline{\mathbf{M}}_{0,n}(\mathbb{P}^r, d)) \otimes \mathbb{Q}.$$

**Claim 2.2.** If the number of marked points  $n \geq 3$ , then  $\mathcal{H}$  and the boundary divisors generate P.

Consider the product of n-3 copies of  $\mathbb{P}^1$ . Let W be the complement of diagonals and the locus where one of the factors is 0, 1 or  $\infty$ . Let U be the open subset

$$U \subset \mathbb{P} \oplus_0^r H^0(\mathbb{P}^1, \mathcal{O}_{\mathbb{P}^1}(d))$$

parameterizing base-point free degree d maps from  $\mathbb{P}^1$  to  $\mathbb{P}^r$ . The complement of U has codimension at least 2. The product  $W \times U$  embeds as an open subset of  $\overline{\mathrm{M}}_{0,n}(\mathbb{P}^r,d)$  whose complement is the boundary. Since the group of codimension one cycles of  $W \times U$  is generated by a multiple of  $\mathcal{H}$ , the claim follows.

**Claim 2.3.** If the number of marked points n = 2, then the boundary,  $\mathcal{L}_1$  and  $\mathcal{L}_2$  generate P.

Fix a hyperplane  $\Lambda$ . Consider the inverse image U of  $\Lambda$  under the third evaluation morphism from  $\overline{\mathrm{M}}_{0,3}(\mathbb{P}^r,d)$ . Away from the inverse image of the locus where the domain of the map is reducible and the images of the marked points lie in  $\Lambda$ , the forgetful map that forgets the third point is finite and projective. Hence it suffices to show that the divisor class group of this latter space is zero. This is clear.

**Claim 2.4.** If the number of marked points n = 1, then the boundary,  $\mathcal{L}_1$  and  $\mathcal{H}$  generate P.

In order to see this claim fix two general hyperplanes  $\Lambda_1, \Lambda_2$  and carry out an argument similar to the previous two arguments.

**Claim 2.5.** If the number of marked points n = 0, then  $\mathcal{H}$  and the boundary divisors generate P.

Fix three hyperplanes  $H_1$ ,  $H_2$ ,  $H_3$ . Consider the complement Z in  $\overline{\mathrm{M}}_{0,0}(\mathbb{P}^r,d)$  of the boundary and the three hypersurfaces of maps intersecting  $H_i \cap H_j$ ,  $i \neq j$ . It suffices to prove that the divisor classes of Z is trivial. This is easy to see.

Note that the previous four claims suffice to complete the proof of the theorem.

These divisors satisfy certain relations. Already this is clear from the proof of the theorem. These relations may be determined as follows.

Relations among the boundary divisors. The Kontsevich moduli space admits a morphism to the Deligne-Mumford moduli space of stable curves  $\overline{\mathrm{M}}_{0,n}$  by forgetting the map and stabilizing. We already know relations among the boundary components of  $\overline{\mathrm{M}}_{0,n}$ . Pulling back these relations among the boundary components yields the relations among the boundary components.

**Exercise 2.6.** By exhibiting one parameter families that have different intersection numbers show that

- (1)  $\mathcal{H}$  is not in the span of boundary divisors. (Hint: Consider the Veronese image of a pencil of lines in  $\mathbb{P}^2$ )
- (2) If the number of marked points is one, then  $\mathcal{H}$  and  $\mathcal{L}_1$  are independent modulo the boundary.
- (3) If the number of marked points is two, then  $\mathcal{L}_1$  and  $\mathcal{L}_2$  are independent modulo the boundary.

**Exercise 2.7.** Fix a hyperplane  $\Lambda$  in  $\mathbb{P}^r$ . Show that the locus of stable maps in  $\overline{\mathrm{M}}_{0,0}(\mathbb{P}^r,d)$  where  $f^{-1}(\Lambda)$  is not d distinct, smooth points is a divisor  $\mathcal{T}$  in  $\overline{\mathrm{M}}_{0,0}(\mathbb{P}^r,d)$ . Calculate the class of this divisor in terms of  $\mathcal{H}$  and the boundary divisors. (Hint:

$$\mathcal{T} = \frac{d-1}{d}\mathcal{H} + \sum_{i=1}^{\lfloor d/2 \rfloor} \frac{i(d-i)}{d} \Delta_i.)$$

2.1. An algorithm for computing the genus zero characteristic numbers in projective space. There is an algorithm for computing the number of rational curves in  $\mathbb{P}^r$  that intersect i general codimension two linear spaces and are tangent to (r+1)(d+1)-4-i general hyperplanes. In general this algorithm gets out of hand very quickly and it is hard to implement. However, for small degree curves it solves the characteristic number problem rather easily.

**Proposition 2.8.** The number of rational curves of degree d in  $\mathbb{P}^r$  that intersect i general codimension two linear spaces and are tangent to (r+1)(d+1)-4-i general hyperplanes may be computed as  $\mathcal{H}^i \cdot \mathcal{T}^{(r+1)(d+1)-4-i}$  on  $\overline{M}_{0,0}(\mathbb{P}^r,d)$ .

Assuming the proposition for the moment, we can describe the algorithm. We can compute the intersections of top monomials consisting of  $\mathcal{H}$  and  $\mathcal{L}_i$ . (For instance we can use the associativity relations in the cohomology ring and Kontsevich-Manin's First Reconstruction Theorem in order to determine these top degree monomials.)

In order to determine the top monomials involving the boundary, we can pull-back to the boundary divisors. The boundary itself is a product of Kontsevich moduli spaces. We can express the pull-back of the standard divisors as standard divisors on the product and proceed inductively.

**Exercise 2.9.** Determine the characteristic numbers of conics in  $\mathbb{P}^2$  using this algorithm. In particular, show that

$$\mathcal{H}^5 = \mathcal{T}^5 = 1, \quad \mathcal{H}^4 \mathcal{T} = \mathcal{H} \mathcal{T}^4 = 2, \quad \mathcal{H}^3 \mathcal{T}^2 = \mathcal{H}^2 \mathcal{T}^3 = 4.$$

Exercise 2.10. Show that the class of degree two maps whose image is tangent to a conic has class

$$2(\mathcal{H} + \mathcal{T})$$

in  $\overline{\mathrm{M}}_{0,0}(\mathbb{P}^2,2)$ . Using this fact and the previous exercise, show that there are 3264 conics tangent to 5 general conics in  $\mathbb{P}^2$ .

**Exercise 2.11.** Determine the number of twisted cubics in  $\mathbb{P}^3$ . intersecting i general lines and tangent to 12-i general planes by applying the algorithm described in this section. (Hint: The numbers are determined by  $\mathcal{H}^i\mathcal{T}^{12-i}$ . In order of decreasing i they are 80160, 134400, 209760, 297280, 375296, 415360, 401920, 343360, 264320, 188256, 128160, 85440 and 56960.)

**Exercise 2.12.** Show that the closure of the locus of twisted cubics tangent to a smooth quadric hypersurface is a divisor with class  $2\mathcal{H} + 2\mathcal{T}$ . Using the previous exercise determine the number of twisted cubics tangent to 12 general quadric hypersurfaces. (Hint: The number is equal to  $(2\mathcal{H} + 2\mathcal{T})^{12}$ . You should get 5,819,539,783,680.)

Exercise 2.13. Finally, establish the proposition that guarantees that the characteristic numbers are indeed given by the claimed intersection numbers. First, show that the divisors  $\mathcal{H}, \mathcal{T}$  and  $\mathcal{L}_i$  are base-point-free divisors. Conclude from this that if representatives defined with respect to general linear spaces are chosen, then the intersections are zero dimensional. Furthermore, check that the points of intersection correspond to maps that in addition have irreducible domain, are simply tangent to those hyperplanes defining  $\mathcal{T}$  and intersect the linear spaces defining  $\mathcal{H}$  transversely. Finally apply Kleiman's Bertini Theorem to the universal map in order to deduce that the points occurring in the intersection are reduced.

### 3. Counting genus zero curves in $\mathbb{P}^n$ : Vakil's algorithm

Ravi Vakil in his thesis developed a different approach for calculating genus zero Gromov-Witten invariants using degenerations. Following [V] we describe his method. For proofs and further discussions we refer you to Ravi's paper.

Before we describe his theorem that allows us to do the following computations, we will give a few sample calculations to indicate how his method works.

**Example 3.1.** Let us find out the number of conics in  $\mathbb{P}^3$  that contain 2 general points  $p_1, p_2$  and intersect 4 general lines  $l_1, \ldots, l_4$ . The idea is to specialize the conditions that the curves satisfy one at a time to general linear spaces of a hyperplane. Fix a general hyperplane H, that is a general  $\mathbb{P}^2$ . We can assume that H contains the two points  $p_1, p_2$ . We specialize one of the lines  $l_1$  to H. Any connected degree two curve containing  $p_1, p_2$  and intersecting  $l_1$  either has to be contained in H or it has to have a component in H. In the first case the conic is uniquely determined.

FIGURE 1. Calculating the number of conics that contain 2 general points and intersect 4 general lines.

It has to contain the two points in H and the three points of intersection of  $l_2, l_3, l_4$  with H. We count this conic twice for the choice of intersection of the conic with  $l_1$ . In the latter case the component in H has to be a line. In fact, it has to be the line passing through  $p_1$  and  $p_2$ . The remaining component has to intersect this line and  $l_2, l_3, l_4$ . There are two lines in  $\mathbb{P}^3$  that intersect 4 lines. We conclude that there are a total of 4 conics that contain 2 general points and intersect 4 general lines. See Figure 1 for a schematic representation of this calculation.

**Example 3.2.** Let us calculate that there are 5 twisted cubics in  $\mathbb{P}^3$  containing 5 general points and intersecting 2 general lines. We will carry out this calculation in two different ways in order to show the degenerations that can occur. Figure 2 shows a schematic diagram of both of these degenerations.

FIGURE 2. Calculating the number of twisted cubics that contain 5 general points and intersect 2 general lines.

The left hand panel shows the degeneration when we first specialize the line  $l_1$  to a plane P that is spanned by the three points  $p_1, p_2, p_3$ . Once we make this degeneration, the limit twisted cubics necessarily become reducible. P contains either a conic or a line. If P contains a conic, then the residual line has to be the span of the remaining two points  $p_4, p_5$  not contained in P. The conic then is uniquely determined by the facts that it has to intersect this line,  $l_2$  and contain  $p_1, p_2, p_3$ . This solution contributes 2 for the choice of intersection of the conic with  $l_1$ . If P contains a line, the line has to be the span of two of the points  $p_1, p_2, p_3$ , hence there are 3 choices for the line. The conic is then uniquely determined by the requirements that it intersect the line in P,  $l_2$  and contain the remaining three points. We see that there are 5 twisted cubics that contain 5 general points and intersect 2 general lines.

The right hand panel shows a different order of degeneration for the same problem. We first specialize a point and the two lines to a general plane P. The limiting twisted cubics may meet  $l_1$  and  $l_2$  along their points of intersection. This problem reduces to counting twisted cubics passing through 6 general points. The answer is 1. Otherwise, we specialize another point to P. At this stage the limiting twisted cubics have to become reducible. There could be a line in P (necessarily the span of the two points contained in P) and a conic in the plane spanned by the three points not contained in P. A priori there seems to be a one parameter family of possible conics.

This forces us to answer the question of which among these conics are limits of our original solutions. The key to the answer lies in tracing the limit of the Cartier divisor cut out on the family of twisted cubics by the plane P. The limit is a degree three divisor on the limiting curve. However, the restriction of the limiting divisor to the reducible curve may have degree 2 or 3 on the line component. If it has degree 2, then the conic has to intersect one of  $l_1$  or  $l_2$  giving two solutions. If it has degree 3, the conic has to be tangent to the plane P. There is one such conic. However, in this case there is a new twist. Two distinct solutions approach this solution. Hence, this solution counts with multiplicity 2.

For more examples see [V]. We now describe how the algorithm in the previous examples works in general. The aim is to calculate the characteristic numbers of rational curves in projective space. Recall that the characteristic numbers of rational curves of degree e are the numbers of rational curves of degree e that intersect general linear subspaces  $\Lambda_i$  of  $\mathbb{P}^n$  of codimension  $c_i$  such that

$$\sum_{i} (c_i - 1) = (e+1)(n+1) - 4.$$

In fact, the algorithm will calculate slightly more general numbers by allowing the curves to have higher order contact with a fixed hyperplane.

The idea is to specialize the linear spaces that impose conditions on the curves one at a time to general linear spaces of a fixed hyperplane H. We then trace the limits of the stable maps.

More precisely, fix positive integers d and r. Let  $\{\Delta_i\}_{i\in I}$  be a general collection of linear subspaces of  $\mathbb{P}^r$  and let  $\{\Gamma_j^m\}_{j\in J}$  be a general collection of linear subspaces of a hyperplane H in  $\mathbb{P}^r$ . Let  $X_r(d,\Gamma,\Delta)$  be the locus of stable maps of degree d to  $\mathbb{P}^r$  with #I + #J marked points such that the point  $p_i$  maps to  $\Delta_i$  and the point  $q_i^m$ 

maps to  $\Gamma_j^m$ . Furthermore, assume that the pull-back of the hyperplane H under the stable map is  $\sum_j mq_j^m$ . You should think of  $X_r(d,\Gamma,\Delta)$  as parameterizing rational curves of degree d with specified contact orders with a hyperplane H along general linear subspaces  $\Gamma_j^m$  of H and intersting other linear subspaces  $\Delta_i$  of  $\mathbb{P}^r$ . There is a Cartier divisor  $D_H$  of  $X_r(d,\Gamma,\Delta)$  obtained by requiring one of the points not mapping to H to map to H.

The task at hand is to enumerate the Weil divisors (together with their multiplicities) that form the components of  $D_H$ . The following loci turn out to be crucial. Let

$$Y_r(d(0), \Gamma(0), \Delta(0); \ldots; d(l), \Gamma(l), \Delta(l))$$

be the locus of stable maps to  $\mathbb{P}^r$  such that

- (1) The domain has l+1 components. The central component is C(0) and all other components meet this component.
- (2) The map has degree d(i) on the *i*th component.
- (3) There is a partition of the conditions  $\Delta$  and  $\Gamma$  to the various components and the images of the marked points on the component C(i) lie in the corresponding linear constraints  $\Delta(i)$  and  $\Gamma(i)$ .
- (4) The only component that is mapped to H is C(0). All the other components intersect H along the marked points and the point of attachment of C(i) with C(0).
- (5) The pull-back of H to the *i*th component by the stable map has the form

$$\sum m p_j^m(i) + m_i(C(0) \cap C(i))$$

where the positive integer  $m_i$  is defined by

$$m_i = d(i) - \sum_m m \# \Gamma_i^m.$$

The following theorem of Vakil identifies the components of  $D_H$ .

**Theorem 3.3** (Vakil). Every component of  $D_H$  has the form

$$Y_r(d(0), \Gamma(0), \Delta(0); \ldots; d(l), \Gamma(l), \Delta(l))$$

for some partition of d into non-negative integers and partitions of  $\Delta$  and  $\Gamma$ . The component

$$Y_r(d(0), \Gamma(0), \Delta(0); \ldots; d(l), \Gamma(l), \Delta(l))$$

occurs with multiplicity  $\prod m_i$ .

We can depict Vakil's theorem rather informally by the diagram in Figure 3:

Every limiting curve that occurs has the form that there is one central component contained in the hyperplane and some number (r) in the picture of irreducible components that are not contained in the hyperplane and intersect the central component. In addition each of these latter components have contact of order  $m_i$  with the hyperplane. Vakil's theorem says that such a limit occurs with multiplicity  $\prod m_i$ .

The proof is non-trivial. The task is to express the Cartier divisor  $D_H$  as a There is an easy component of the proof. One identifies the potential limits by a dimension count. The limit has to be a stable map from a tree of  $\mathbb{P}^1$ s. Once we fix

FIGURE 3. The limits that occur.

the combinatorics of the tree the dimension of such maps is easy to calculate. The problem is that contracted components may add moduli. However, these loci of maps are not enumeratively relevant because their image in the Hilbert scheme or the Chow variety have smaller dimension. Keeping this in mind it is easy to see that the loci described in the theorem are the only enumeratively relevant codimension one loci that can occur in the expression of  $D_H$ .

The technically harder part of the proof is to calculate the multiplicity of each of the enumeratively relevant Weil divisors. One first reduces the problem when the target is  $\mathbb{P}^1$  instead of  $\mathbb{P}^r$ . This is done by projecting via a general codimension two linear space contained in the hyperplane H. This is only a rational map, but the locus where it is defined intersects all the enumeratively relevant divisors and is smooth at a general point of the intersection. The problem thus reduces to analyzing coverings of  $\mathbb{P}^1$ . In this setting the calculation of the deformation spaces is easier and yields the desired multiplicity.

**Exercise 3.4.** Determine the number of conics in  $\mathbb{P}^3$  intersecting i general points and 8-2i general lines for  $0 \ge i \ge 3$  using Vakil's method. Try this with different orders of degeneration. Which ones tend to be easier to carry out? Compare your results with those obtained by calculating in the cohomology ring of the Hilbert scheme of conics in  $\mathbb{P}^3$ .

**Exercise 3.5.** Using Vakil's method show that there is a unique twisted cubic containing 6 general points in  $\mathbb{P}^3$ . By induction show that there is a unique rational normal curve of degree d in  $\mathbb{P}^d$  containing d+3 points. Give a direct argument that does not use degenerations.

**Exercise 3.6.** Show that there are 5 twisted cubics that contain 5 points and meet two lines; and 30 twisted cubics that contain 4 points and meet 4 lines. Try doing these calculations with different orders of degeneration. Using induction deduce that the number of rational normal curves of degree d in  $\mathbb{P}^d$  that contain d+2 general points, meet a line and a  $\mathbb{P}^{d-2}$  is  $(d^2+d-2)/2$ .

**Exercise 3.7.** Degeneration techniques may be used to calculate tangency to higher degree hypersurfaces as well. Show that there are 3264 conics in  $\mathbb{P}^2$  tangent to five general conics. Do this by degenerating the conics into a pair of lines.

(Hint: In the limit the conics maybe tangent to either of the two lines or pass through the singular point. The latter count with multiplicity 2.) Do this calculation directly in the cohomology ring of  $\overline{\mathrm{M}}_{0,0}(\mathbb{P}^2,2)$ , recalling that the Kontsevich space in this case is isomorphic to the blow up of  $\mathbb{P}^5$  (the Hilbert scheme) along the Veronese surface of double lines.

**Remark 3.8.** R. Vakil using the same technique can also calculate the characteristic numbers of elliptic curves. The details are very similar. A few new phenomena (such as the need to record some information about the Picard group of the elliptic curve) complicate matters slightly. We leave it to you to develop or read the necessary modifications.

**Exercise 3.9.** Try finding the number of elliptic cubic curves in  $\mathbb{P}^3$  that contain 2 general points and intersect 8 general lines. (Hint: Specialize the lines one at a time to a plane P containing the two points. If after specializing  $l_1$  to P the elliptic cubics do not have a component in P where do they have to intersect  $l_1$ ?)

**Problem 3.10.** Extend Vakil's method to higher genus curves. It would be especially interesting to be able to determine the characteristic numbers of canonical curves or curves embedded by special  $g_d^r$ 's using degenerations. At present this problem seems difficult.

**Remark 3.11.** Caporaso and Harris in [CH1] (see also [CH2]) using essentially the same technique (but working in a partial compactification of the Severi variety rather than the Kontsevich moduli space) calculated the degrees of Severi varieties in  $\mathbb{P}^2$  for all genera. I believe this work inspired Vakil to develop his algorithm.

**Exercise 3.12.** Using degenerations show that there are  $2^6$  canonical curves of genus 4 in  $\mathbb{P}^3$  containing 9 general points and meeting 6 lines. Determine the number of canonical curves of genus 4 in  $\mathbb{P}^3$  contining 8 general points and intersecting 8 general lines. (Hint: Use the fact that a genus 4 curve is the complete intersection of a quadric and a cubic surface and trace the limit of the quadric surface.)

Remark 3.13. Degeneration techniques may be used much more generally to determine the characteristic numbers of varieties. We already used this technique to obtain Littlewood - Richardson rules for Grassmannians. It is possible to calculate certain characteristic numbers of scrolls and other simple surfaces such as Del Pezzo surfaces.

# 4. The cones of ample and effective divisors on the Kontsevich moduli space

In this section we will discuss the ample cone and the effective cone of divisors on the Kontsevich moduli space of genus zero stable maps to  $\mathbb{P}^r$ . For more details you can consult [CHS1] and [CHS2].

4.1. The ample cone of the Kontsevich moduli space. We begin by describing the ample cone of  $\overline{\mathrm{M}}_{0,n}(\mathbb{P}^r,d)$ .

**Theorem 4.1.** Let r and d be positive integers, n a nonnegative integer such that  $n+d \geq 3$ . There is an injective linear map,

$$v: Pic(\overline{\mathcal{M}}_{0,n+d})^{\mathfrak{S}_d}_{\mathbb{Q}} \to Pic(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d))_{\mathbb{Q}}.$$

The NEF cone of  $\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$  is the product of the cone generated by

$$\mathcal{H}, \mathcal{T}, \mathcal{L}_1, \ldots, \mathcal{L}_n$$

and the image under v of the NEF cone of  $\overline{\mathcal{M}}_{0,n+d}//\mathfrak{S}_d$ .

We recall that  $\mathcal{H}$  is the class of the divisor of maps whose images intersect a fixed codimension two linear space in  $\mathbb{P}^r$  (provided r > 1 and d > 0). The class  $\mathcal{L}_i$  is the pullback of  $\mathcal{O}_{\mathbb{P}^r}(1)$  by the  $i^{\text{th}}$  evaluation morphism. Fixing a hyperplane  $\Pi \subset \mathbb{P}^r$ ,  $\mathcal{T}$  is the class of the divisor parametrizing stable maps  $(C, p_1, \ldots, p_i, f)$  for which  $f^{-1}(\Pi)$  is not simply d reduced, smooth points of C. In terms of Pandharipande's generators, the class of  $\mathcal{T}$  equals,

$$\mathcal{T} = \frac{d-1}{d}\mathcal{H} + \sum_{k=0}^{\lfloor d/2 \rfloor} \frac{k(d-k)}{d} (\sum_{A,B} \Delta_{(A,k),(B,d-k)}).$$

We now describe the map v that occurs in Theorem 4.1.

FIGURE 4. The morphism  $\alpha$ .

The morphism  $\alpha$ . There is a 1-morphism  $\alpha: \overline{M}_{0,n+d} \times \mathbb{P}^{r-1} \to \overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$  defined as follows. Fix a point  $p \in \mathbb{P}^r$  and a line  $L \subset \mathbb{P}^r$  containing p. To every curve C in  $\overline{M}_{0,n+d}$  attach a copy of L at each of the last d marked points and denote the resulting curve by C'. Consider the morphism  $f: C' \to \mathbb{P}^r$  that contracts C to p and maps the d rational tails isomorphically to L (see Figure 4). Since the space of lines in  $\mathbb{P}^r$  passing through the point p is parameterized by  $\mathbb{P}^{r-1}$ , there is an induced 1-morphism  $\alpha:\overline{M}_{0,n+d}\times\mathbb{P}^{r-1}\to\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$ .

Since  $\alpha$  is invariant for the action of  $\mathfrak{S}_d$  permuting the last d marked points, the pull-back map determines a homomorphism

$$\alpha^* = (\alpha_1^*, \alpha_2^*) : \operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r, d)) \to \operatorname{Pic}(\overline{\mathcal{M}}_{0,n+d})^{\mathfrak{S}_d} \times \operatorname{Pic}(\mathbb{P}^{r-1}).$$

We will denote the two projections of  $\alpha^*$  by  $\alpha_1^*$  and  $\alpha_2^*$ .

The morphisms  $\beta_i$ . For each  $1 \leq i \leq n$ , there is a 1-morphism  $\beta_i : \mathbb{P}^1 \to \overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$  defined as follows. Fix a degree-(d-1), (n-1)-pointed curve C containing all except the  $i^{\text{th}}$  marked point. At a general point of C, attach a line L. Attach a line L to C at a general point of C. The resulting degree-d, reducible

FIGURE 5. The morphism  $\beta_i$ .

curve will be the domain of our map. The final,  $i^{th}$  marked point is in L. Varying  $p_i$ in L gives a 1-morphism  $\beta_i: \mathbb{P}^1 \to \overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$  (see Figure 5). This definition has to be slightly modified in the cases (n,d)=(1,1) or (2,1). When (n,d)=(1,1), we assume that the line L with the varying marked point  $p_i$  constitutes the entire stable map. When (n,d)=(2,1), we assume that the map has L as the only component. One marked point is allowed to vary on L and the remaining marked point is held fixed at a point  $p \in L$ .

FIGURE 6. The morphism  $\gamma$ .

**The morphism**  $\gamma$ . If  $d \geq 2$ , there is a 1-morphism  $\gamma : \mathbb{P}^1 \to \overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$  defined as follows. Take two copies of a fixed line L attached to each other at a variable point. Fix a point p in the second copy of L. Let C be a smooth, degree-(d-2), genus 0, (n+1)-pointed stable map to  $\mathbb{P}^r$  whose (n+1)-st point maps to p. Attach this to the second copy of L at p. Altogether, this gives a degree-d, n-pointed, genus 0 stable maps with three irreducible components. The n marked points are the first n marked points of C. The only varying aspect of this family of stable maps is the attachment point of the two copies of L. Varying the attachment point in  $L \cong \mathbb{P}^1$  gives a stable maps is parameterized by  $\mathbb{P}^1$ , hence there is an induced 1-morphism  $\gamma: \mathbb{P}^1 \to \overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$  (see Figure 6). When (n,d)=(1,2), we modify the definition by assuming that the map consists only of the two copies of the line L and the marked point is held fixed at the point p on the second copy of L.

If  $d \geq 2$ , denote by  $P_{r,n,d}$  the Abelian group

$$P_{r,n,d} := \operatorname{Pic}(\overline{\mathbf{M}}_{0,n+d})^{\mathfrak{S}_d} \times \operatorname{Pic}(\mathbb{P}^{r-1}) \times \operatorname{Pic}(\mathbb{P}^1)^n \times \operatorname{Pic}(\mathbb{P}^1).$$

Denote by  $u = u_{r,n,d} : \operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)) \to P_{r,n,d}$  the pull-back map

$$u_{r,n,d} = (\alpha^*, (\beta_1^*, \dots, \beta_n^*), \gamma^*).$$

If d = 1, denote by  $P_{r,n,1}$  the Abelian group

$$P_{r,n,1} := \operatorname{Pic}(\overline{\mathbf{M}}_{0,n+d})^{\mathfrak{S}_d} \times \operatorname{Pic}(\mathbb{P}^{r-1}) \times \operatorname{Pic}(\mathbb{P}^1)^n$$

| Divisors in $\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$ | $\alpha_1^*$                                         | $\alpha_2^*$                         | $\beta_i^*$                      | $\gamma^*$                       |
|------------------------------------------------------------|------------------------------------------------------|--------------------------------------|----------------------------------|----------------------------------|
| $\mathcal{T}$                                              | 0                                                    | 0                                    | 0                                | $\mathcal{O}_{\mathbb{P}^1}(2)$  |
| $\mathcal{H}$                                              | 0                                                    | $\mathcal{O}_{\mathbb{P}^{r-1}}(d)$  | 0                                | 0                                |
| $\mathcal{L}_i$                                            | 0                                                    | 0                                    | $\mathcal{O}_{\mathbb{P}^1}(1)$  | 0                                |
| $\mathcal{L}_{j \neq i}$                                   | 0                                                    | 0                                    | 0                                | 0                                |
| $\Delta_{(\emptyset,1),(\underline{n},d-1)}$               | c                                                    | $\mathcal{O}_{\mathbb{P}^{r-1}}(-d)$ | $\mathcal{O}_{\mathbb{P}^1}(-1)$ | $\mathcal{O}_{\mathbb{P}^1}(4)$  |
| $\Delta_{(\emptyset,2),(\underline{n},d-2)}$               | $\tilde{\Delta}_{(\emptyset,2),(\underline{n},d-2)}$ | 0                                    | 0                                | $\mathcal{O}_{\mathbb{P}^1}(-1)$ |
| $\Delta_{(\{i\},1),(\{i\}^c,d-1)}$                         | $\tilde{\Delta}_{(\{i\},1),(\{i\}^c,d-1)}$           | 0                                    | $\mathcal{O}_{\mathbb{P}^1}(-1)$ | 0                                |
| $\Delta_{(A,d_A),(B,d_B)}$ all others                      | $\tilde{\Delta}_{(A,d_A),(B,d_B)}$                   | 0                                    | 0                                | 0                                |

FIGURE 7. The pull-backs of the standard generators

and denote by  $u = u_{r,n,1} : \operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r, 1)) \to P_{r,n,1}$  the pull-back map  $u_{r,n,1} = (\alpha^*, (\beta_1, {}^*, \dots, \beta_n^*))$ 

Theorem 4.1 is equivalent to the following.

**Theorem 4.2.** The map  $u_{r,n,d} \otimes \mathbb{Q} : Pic(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d))_{\mathbb{Q}} \to P_{r,n,d} \otimes \mathbb{Q}$  is an isomorphism. The image under  $u_{r,n,d} \otimes \mathbb{Q}$  of the ample cone, resp. NEF, eventually free cone of  $\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$  equals the product of the ample cones, resp. NEF, eventually free cones of  $Pic(\overline{\mathcal{M}}_{0,n+d})^{\mathfrak{S}_d}$ ,  $Pic(\mathbb{P}^{r-1})$ , and the factors  $Pic(\mathbb{P}^1)$ .

To apply Theorem 4.2, we need to express the images of the standard generators of  $\operatorname{Pic}(\overline{\mathbb{M}}_{0,n}(\mathbb{P}^r,d))$  in terms of the standard generators for  $\operatorname{Pic}(\overline{\mathbb{M}}_{0,n+d})^{\mathfrak{S}_d}$ ,  $\operatorname{Pic}(\mathbb{P}^{r-1})$  and  $\operatorname{Pic}(\mathbb{P}^1)$  factors. This is summarized in Table 7.

Let  $\Pi \subset \mathbb{P}^r$  be a hyperplane not containing the point p used to define the morphisms  $\alpha$  and  $\gamma$ . Assume that the degree d-1 curve used to define the morphisms  $\beta_i$  is not tangent to  $\Pi$ , and none of the marked points on this curve are contained in  $\Pi$ . Finally, assume that the degree d-2 curve used to define the morphism  $\gamma$  is not tangent to  $\Pi$  and none of the marked points are contained in  $\Pi$ .

Denote by  $\mathcal{M}_{0,n+d}(\mathbb{P}^r,d)$  the open substack of  $\overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d)$  parameterizing stable maps with irreducible domain. Let

$$\operatorname{ev}_{n+1,\dots,n+d}:\mathcal{M}_{0,n+d}(\mathbb{P}^r,d)\to(\mathbb{P}^r)^d$$

be the evaluation morphism associated to the last d marked point. Denote by  $\mathcal{M}_{0,n+d}(\mathbb{P}^r,d)_{\Pi}$  the inverse image of  $\Pi^d$  and by  $\overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d)_{\Pi}$  the closure of  $\mathcal{M}_{0,n+d}(\mathbb{P}^r,d)_{\Pi}$  in  $\overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d)$ .

 $\overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d)_{\Pi}$  is  $\mathfrak{S}_d$ -invariant under the action of  $\mathfrak{S}_d$  on  $\overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d)$  permuting the last d marked points. Denote by

$$\pi: \overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d) \to \overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$$

the forgetful 1-morphism that forgets the last d marked points and stabilizes the resulting family of prestable maps. This is  $\mathfrak{S}_d$ -invariant. Denote by

$$\rho: \overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d) \to \overline{\mathrm{M}}_{0,n+d}$$

the 1-morphism that stabilizes the universal family of marked prestable curves over  $\overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d)$ . This is  $\mathfrak{S}_d$ -equivariant.

Denote by  $q: \overline{\mathrm{M}}_{0,n+d} \to \overline{\mathrm{M}}_{0,n+d}/\mathfrak{S}_d$  the geometric quotient. The composition  $q \circ \rho: \overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d)_{\Pi} \to \overline{\mathrm{M}}_{0,n+d}/\mathfrak{S}_d$  is  $\mathfrak{S}_d$ -equivariant. Because  $\mathcal{M}_{0,n+d}(\mathbb{P}^r,d)_{\Pi}$  is an  $\mathfrak{S}_d$ -torsor over  $O_{\Pi}$ , there is a unique 1-morphism  $\phi'_{\Pi}: O_{\Pi} \to \overline{\mathrm{M}}_{0,n+d}/\mathfrak{S}_d$  such that  $\phi' \circ \pi = q \circ \rho$ .

**Definition 4.3.** Define  $U_{\Pi}$  to be the maximal open substack of  $\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)$  over which  $\phi'_{\Pi}$  extends to a 1-morphism, denoted

$$\phi_{\Pi}: U_{\Pi} \to \overline{\mathrm{M}}_{0,n+d}/\mathfrak{S}_d.$$

Define  $I_{\Pi}$  to be the normalization of the closure in  $\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d) \times \overline{\mathrm{M}}_{0,n+d}/\mathfrak{S}_d$  of the image of the graph of  $\phi'_{\Pi}$ , i.e.,  $I_{\Pi}$  is the normalization of the image of  $(\pi,q\circ\rho)$ . Define  $\widetilde{I}_{\Pi}$  to be the normalization of the image of  $(\pi,\rho)$  in  $\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d) \times \overline{\mathrm{M}}_{0,n+d}$ . Finally, define  $\widetilde{U}_{\Pi}$  to be the inverse image of  $U_{\Pi}$  in  $\widetilde{I}_{\Pi}$ .

There is a pull-back map of  $\mathfrak{S}_d$ -invariant invertible sheaves,

$$\rho^* : \operatorname{Pic}(\overline{\mathbf{M}}_{0,n+d})^{\mathfrak{S}_d} \to \operatorname{Pic}(\widetilde{I}_{\Pi})^{\mathfrak{S}_d},$$

which further restricts to  $\operatorname{Pic}(\widetilde{U}_{\Pi})^{\mathfrak{S}_d}$ . After étale base-change from  $U_{\Pi}$  to a scheme, the morphism  $\widetilde{U}_{\Pi} \to U_{\Pi}$  is the geometric quotient of  $\widetilde{U}_{\Pi}$  by the action of  $\mathfrak{S}_d$ . Therefore the pull-back map  $\operatorname{Pic}(U_{\Pi}) \to \operatorname{Pic}(\widetilde{U}_{\Pi})^{\mathfrak{S}_d}$  is an isomorphism after tensoring with  $\mathbb{Q}$ ; in fact, both the kernel and cokernel are annihilated by d!. Because  $\overline{M}_{0,n+d}/\mathfrak{S}_d$  is a proper scheme and because  $\overline{M}_{0,n}(\mathbb{P}^r,d)$  is separated and normal, by the valuative criterion of properness the complement of  $U_{\Pi}$  has codimension  $\geq 2$ . The smoothness of  $\overline{M}_{0,n}(\mathbb{P}^r,d)$  and [Ha, Prop. 6.5(c)] imply that the restriction map  $\operatorname{Pic}(\overline{M}_{0,n}(\mathbb{P}^r,d)) \to \operatorname{Pic}(U_{\Pi})$  is an isomorphism.

**Definition 4.4.** Define  $v : \operatorname{Pic}(\overline{\mathbb{M}}_{0,n+d})^{\mathfrak{S}_d} \to \operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)) \otimes \mathbb{Q}$  to be the unique homomorphism commuting with  $\rho^*$  via the isomorphisms above.

The map v is independent of the choice of  $\Pi$ , hence it sends NEF divisors to NEF divisors.

**Lemma 4.5.** For every base-point-free invertible sheaf  $\mathcal{L}$  in  $Pic(\overline{M}_{0,n+d})^{\mathfrak{S}_d}$ ,  $v(\mathcal{L})$  is base-point-free. In particular, for every ample invertible sheaf  $\mathcal{L}$ ,  $v(\mathcal{L})$  is NEF. Thus, by Kleiman's criterion, for every NEF invertible sheaf  $\mathcal{L}$ ,  $v(\mathcal{L})$  is NEF.

Proof. For every  $[(C, (p_1, \ldots, p_n), f)]$  in  $\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r, d)$ , there exists a hyperplane  $\Pi$  satisfying the conditions above and such that  $f^{-1}(\Pi)$  is a reduced Cartier divisor containing none of  $p_1, \ldots, p_n$ .  $(C, (p_1, \ldots, p_n), f)$  is contained in  $U_{\Pi}$ . Since  $\mathcal{L}$  is base-point-free, there exists a divisor D in the linear system  $|\mathcal{L}|$  not containing  $\phi_{\Pi}[(C, (p_1, \ldots, p_n), f)]$ . By the proof of [Ha, Prop. 6.5(c)], the closure of  $\phi_{\Pi}^{-1}(D)$  is in the linear system  $|v(\mathcal{L})|$ ; and it does not contain  $[(C, (p_1, \ldots, p_n), f)]$ .

**Lemma 4.6.** (i) The images of  $\alpha$ ,  $\beta_i$  and  $\gamma$  are contained in  $U_{\Pi}$ .

- (ii) The morphisms  $\phi_{\Pi} \circ \beta_i$  and  $\phi_{\Pi} \circ \gamma$  are constant morphisms. Therefore  $\beta_i^* \circ v$  and  $\gamma^* \circ v$  are the zero homomorphism.
- (iii) The composition of  $\alpha$  with  $\phi_{\Pi}$  equals  $q \circ pr_{\overline{M}_{0,n+d}}$ . Therefore

$$\alpha^* \circ v : Pic(\overline{M}_{0,n+d})^{\mathfrak{S}_d} \to Pic(\overline{M}_{0,n+d})^{\mathfrak{S}_d} \times Pic(\mathbb{P}^{r-1})$$

is the homomorphism whose projection on the first factor is the identity, and whose projection on the second factor is 0.

*Proof.* (i): The image of  $\alpha$  is contained in  $O_{\Pi}$ . Denote by q the intersection point of L and  $\Pi$ .

The image  $\beta_i(L-\{q\})$  is contained in  $O_{\Pi}$ . The stable map  $\beta_i(q)$  sends the  $i^{\text{th}}$  marked point into  $\Pi$ . Up to labeling the d points of the inverse image of  $\Pi$ , there is only one (n+d)-pointed stable map in  $\overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d)_{\Pi}$  that stabilizes to this stable map. It is obtained from  $\beta_i(q)$  by removing the  $i^{\text{th}}$  marked point from L, attaching a contracted component C' to L at q, containing the  $i^{\text{th}}$  marked point and exactly one of the last d marked points, and labeling the d-1 points in  $C \cap \Pi$  with the remaining d-1 marked points.

Similarly,  $\gamma(L - \{q\})$  is contained in  $O_{\Pi}$ . The stable map  $\gamma(q)$  has two copies of L attached to each other at q. This appears to be a problem, because the inverse image of  $\gamma(q)$  in  $\overline{\mathcal{M}}_{0,n+d}(\mathbb{P}^r,d)_{\Pi}$  is 1-dimensional, isomorphic to  $\overline{\mathcal{M}}_{0,4}$ . The stable maps have a contracted component C' such that both copies of L are attached to C' and 2 of the d new marked points are attached to C'. The remaining d-2 marked points are the points of  $C \cap \Pi$ . However, the map  $\rho$  that stabilizes the resulting prestable (n+d)-marked curve is constant on this  $\overline{\mathcal{M}}_{0,4}$ . Indeed, the first copy of L has no marked points and is attached to C' at one point. So the first step in stabilization will prune L reducing the number of special points on C' from 4 to 3.

(ii): In the family defining  $\beta_i$ , only the  $i^{\text{th}}$  marked point on L varies. After adding the d new marked points, L is a 3-pointed prestable curve; marked by the node p, the  $i^{\text{th}}$  marked point, and the point q. For every base the only family of genus 0, 3-pointed, stable curves is the constant family. So upon stabilization, this family of genus 0, 3-pointed, stable curves becomes the constant family.

In the family defining  $\gamma$ , only the attachment point of the two copies of L varies. The first copy of L gives a family of 2-pointed, prestable curves; marked by q and the attachment point of the two copies of L. This is unstable. Upon stabilization, the first copy of L is pruned and the marked point q on the first copy is replaced by a marked point on the second copy at the original attachment point. Now the second copy of L gives a family of 3-pointed, prestable curves; marked by the attachment point p of the second and third irreducible components, the attachment point of the first and second components, and q. For the same reason as in the last paragraph, this becomes a constant family.

(iii): Each stable map in  $\alpha(\overline{\mathbf{M}}_{0,n+d} \times \mathbb{P}^{r-1})$  is obtained from a genus 0, (n+d)-pointed, stable curve  $(C_0, (p_1, \dots, p_n, q_1, \dots, q_d))$  and a line L in  $\mathbb{P}^r$  containing p by attaching for each  $1 \leq i \leq n$ , a copy  $C_i$  of L to  $C_0$  where p in  $C_i$  is identified with  $q_i$  in  $C_0$ . The map to  $\mathbb{P}^r$  contracts  $C_0$  to p, and sends each curve C to L via the identity morphism. Denoting by r the intersection point of L and  $\Pi$ , the inverse image of  $\Pi$  consists of the d points  $r_1, \dots, r_d$ , where  $r_i$  is the copy of r in  $C_i$ .

The component  $C_i$  is a 2-pointed, prestable curve: marked by the attachment point p of  $C_i$  and by  $r_i$ . This is unstable. So, upon stabilization,  $C_i$  is pruned and the marked point  $r_i$  is replaced by a marking on  $C_0$  at the point of attachment of  $C_0$  and  $C_i$ , namely  $q_i$ . Therefore, up to relabeling of the last d marked points, the result is the genus 0, (n+d)-pointed, stable curve we started with,  $(C_0, (p_1, \ldots, p_n, q_1, \ldots, q_d))$ .

In the previous section we constructed a map (see Definition 4.4)

$$v: \operatorname{Pic}(\overline{\mathrm{M}}_{0,n+d})^{\mathfrak{S}_d} \to \operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)) \otimes \mathbb{Q}.$$

In this section we prove that the image of v, the divisor classes  $\mathcal{H}$ ,  $\mathcal{T}$  and the tautological divisors  $\mathcal{L}_i$ , generate  $\operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d))\otimes \mathbb{Q}$ .

The divisor class  $\mathcal{H}_{\Lambda}$ , [Pa, Prop. 1] is the class of stable maps whose image intersects a fixed codimension 2 linear space  $\Lambda$  of  $\mathbb{P}^r$ . This is defined to be the empty divisor if r=1. For convenience, assume  $\Lambda$  is contained in  $\Pi$  and does not intersect L or the curves C used to define  $\beta_i$  and  $\gamma$ . If  $n \geq 1$ , the divisors  $\mathcal{L}_{i,\Pi}$ ,  $i=1,\ldots,n$ , [Pa, Prop. 1] are the pull-back by  $\operatorname{ev}_i$  of the Cartier divisor  $\Pi$ . If  $d \geq 1$ , the last divisor is  $\mathcal{T}_{\Pi}$ , [Pa, §2.3]; the divisor of stable maps  $(C, (p_1, \ldots, p_n), f)$  such that  $f^{-1}(\Pi)$  is not a reduced, finite set of degree d. This is defined to be the empty divisor if d=1. In [Pa] Pandharipande proves that  $\mathcal{H}_{\Lambda}$ ,  $\mathcal{L}_{i,\Pi}$  and  $\mathcal{T}_{\Pi}$  are irreducible Cartier divisors (when they are nonempty).

**Lemma 4.7.** (i) The Cartier divisors  $\mathcal{T}_{\Pi}$ ,  $\mathcal{L}_{i,\Pi}$  and  $\mathcal{H}_{\Lambda}$  are NEF.

- (ii) The pull-backs  $\alpha^*(\mathcal{T}_{\Pi})$  and  $\alpha^*(\mathcal{L}_{i,\Pi})$  are zero. The pull-back  $\alpha^*(\mathcal{H}_{\Lambda})$  equals  $(0, \mathcal{O}_{\mathbb{P}^{r-1}}(d))$  in  $Pic(\overline{M}_{0,n+d})^{\mathfrak{S}_d} \times Pic(\mathbb{P}^{r-1})$ ; if r = 1, then  $\mathcal{O}_{\mathbb{P}^{r-1}}(1)$  is the trivial invertible sheaf.
- (iii) Assume  $n \geq 1$  so that  $\beta_i$  is defined for  $1 \leq i \leq n$ . The pull-backs  $\beta_i^*(\mathcal{T}_{\Pi})$  and  $\beta_i^*(\mathcal{H}_{\Pi})$  are zero. For  $1 \leq j \leq n$  different from i,  $\beta_i^*(\mathcal{L}_{j,\Pi})$  is zero. Finally,  $\beta_i^*(\mathcal{L}_{i,\Pi})$  is  $\mathcal{O}_{\mathbb{P}^1}(1)$ .
- (iv) Assume  $d \geq 2$  so that  $\gamma$  is defined. The pull-backs  $\gamma^*(\mathcal{H}_{\Lambda})$  and  $\gamma^*(\mathcal{L}_{i,\Pi})$  are zero, and  $\gamma^*(\mathcal{T}_{\Pi})$  is  $\mathcal{O}_{\mathbb{P}^1}(2)$  in  $Pic(\mathbb{P}^1)$ .
- *Proof.* (i): By an argument similar to the one in Lemma 4.5, these divisors are base-point-free (whenever they are non-empty). The divisor  $\mathcal{H}_{\Lambda}$  is big if  $r \geq 2$ , and  $\mathcal{T}_{\Pi}$  is big if  $d \geq 2$ . The divisors  $\mathcal{L}_i$  are not big.
- (ii): By the proof of Lemma 4.6, the image of  $\alpha$  is in  $O_{\Pi}$ , which is disjoint from  $\mathcal{T}_{\Pi}$ . Also,  $\operatorname{ev}_i \circ \alpha$  is the constant morphism with image p, so the inverse image of  $\mathcal{L}_i$  is empty. Finally, the pull-back of  $\mathcal{H}_{\Pi}$  equals the pull-back under the diagonal  $\Delta$  of the Cartier divisor  $\sum_{j=1}^d \operatorname{pr}_j^{-1}(\Lambda)$  in  $(\mathbb{P}^{r-1})$ , where  $\Lambda$  is considered as a divisor in  $\mathbb{P}^{r-1}$  via projection from p.
- (iii): Since the image of  $\beta_i$  is disjoint from  $\mathcal{H}_{\Pi}$ ,  $\mathcal{T}_{\Pi}$  and  $\mathcal{L}_{j,\Pi}$  for  $j \neq i$ , the corresponding pull-backs are zero. The map  $ev_i \circ \beta_i : \mathbb{P}^1 \to \mathbb{P}^r$  embeds  $\mathbb{P}^1$  as the line L in  $\mathbb{P}^r$ , hence  $\beta_i^*(\mathcal{L}_{i,\Pi}) = \mathcal{O}_{\mathbb{P}^1}(1)$ .
- (iv): Since neither the image curve nor the marked points vary under  $\gamma$ , clearly  $\gamma^* \mathcal{H}_{\Lambda}$  and  $\gamma^* \mathcal{L}_{i,\Pi}$  are zero. To compute  $\gamma^* \mathcal{T}_{\Pi}$ , use [Pa, Lem 2.3.1].

The main observation of this section is the following.

**Proposition 4.8.** The  $\mathbb{Q}$ -vector space  $Pic(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)) \otimes \mathbb{Q}$  is generated by  $\mathcal{T}_{\Pi}$ ,  $\mathcal{H}_{\Lambda}$ ,  $\mathcal{L}_{i,\Pi}$  for  $1 \leq i \leq n$ , and the image of v.

Proof. When  $r \geq 2$ , Pandharipande proves that the classes of the divisors  $\mathcal{H}_{\Lambda}$ ,  $\mathcal{L}_{i,\Pi}$  for  $1 \leq i \leq n$ , and the boundary divisors  $\Delta_{(A,d_A),(B,d_B)}$  for  $((A,d_A),(B,d_B)) \in \Delta$  generate the  $\mathbb{Q}$ -vector space  $\operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)) \otimes \mathbb{Q}$ , cf. [Pa, Prop. 1]. The tangency divisor  $\mathcal{T}$  can be expressed in terms of  $\mathcal{H}$  and the boundary divisors as follows [Pa, Lem 2.3.1]:

$$\mathcal{T} = \frac{d-1}{d}\mathcal{H} + \sum_{j=0}^{\lfloor \frac{d}{2} \rfloor} \frac{j(d-j)}{d} \sum_{((A,d_A),(B,d_B)),d_A=j} \Delta_{(A,d_A),(B,d_B)}.$$

From Lemmas 4.7 and 4.6 and by pairing with one-parameter families, we see that

$$v(\tilde{\Delta}_{(A,d_A),(B,d_B)}) = \Delta_{(A,d_A),(B,d_B)}$$

unless  $(\#A, d_A)$  or  $(\#B, d_B)$  equals one of (0, 2) or (1, 1).

$$v(\tilde{\Delta}_{(A,d_A),(B,d_B)}) = \frac{1}{2} \mathcal{T} + \Delta_{(A,d_A),(B,d_B)}$$

if  $(\#A, d_A)$  or  $(\#B, d_B)$  equals (0, 2). Finally,

$$v(\tilde{\Delta}_{(\{i\},1),(\{i\}^c,d-1)}) = \Delta_{(\{i\},1),(\{i\}^c,d-1)} + \mathcal{L}_{i,\Pi}.$$

Consequently, it follows that the classes of the divisors  $\mathcal{H}, \mathcal{T}, \mathcal{L}_{i,\Pi}$  and the image of v generate the classes of all the boundary divisors in the Kontsevich moduli space. Hence, they generate  $\operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)) \otimes \mathbb{Q}$ .

We can reduce the case r=1 to the case  $r\geq 2$ . Because L is disjoint from  $\Lambda$ , there is a unique linear projection

$$\operatorname{pr}_{\Lambda}: (\mathbb{P}^r - \Lambda) \to L$$

whose restriction to L is the identity. This is a vector bundle over L whose associated sheaf of sections is  $\mathcal{O}_L(1)^{\oplus (r-1)}$ . Composing a stable map to  $(\mathbb{P}^r - \Lambda)$  with  $\operatorname{pr}_{\Lambda}$  gives a stable map to L. This defines a 1-morphism,

$$\overline{\mathcal{M}}_{0,n}(\mathrm{pr}_{\Lambda},d): (\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)-\mathcal{H}_{\Lambda}) \to \overline{\mathcal{M}}_{0,n}(L,d).$$

This is a vector bundle over  $\overline{\mathcal{M}}_{0,n}(L,d)$  whose associated sheaf of sections is the sheaf whose fiber at  $(C,(p_1,\ldots,p_n),f)$  equals  $H^0(C,f^*\mathcal{O}_L(1)^{\oplus (r-1)})$ . Thus the pull-back homomorphism,

$$\overline{\mathcal{M}}_{0,n}(\mathrm{pr}_{\Lambda},d)^*:\mathrm{Pic}(\overline{\mathcal{M}}_{0,n}(L,d))\to\mathrm{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)-\mathcal{H}_{\Lambda}),$$

is an isomorphism, cf. [Ful, Thm. 3.3(a)].

The hyperplane  $\Pi$  is the closure of  $\operatorname{pr}_{\Lambda}^{-1}(L \cap \Pi)$ . Thus  $U_{\Pi} - \mathcal{H}_{\Lambda} \cap U_{\Pi}$  (see Definition 4.3) is the inverse image of the corresponding open substack of  $\overline{\mathcal{M}}_{0,n}(L,d)$  for  $L \cap \Pi$  inside L. The inverse image of  $\mathcal{T}_{L \cap \Pi}$ , resp.  $\mathcal{L}_{i,L \cap \Pi}$ , equals the restriction of  $\mathcal{T}_{\Pi}$ , resp.  $\mathcal{L}_{i,\Pi}$ . And  $\phi_{L \cap \Pi} \circ \overline{\mathcal{M}}_{0,n}(\operatorname{pr}_{\Lambda},d)$  equals the restriction of  $\phi_{\Pi}$ . Thus  $\operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)-\mathcal{H}_{\Lambda}) \otimes \mathbb{Q}$  is generated by  $\mathcal{T}_{\Pi}$ ,  $\mathcal{L}_{i,\Pi}$  for  $1 \leq i \leq n$ , and the image of v if and only if the same is true for  $\operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^1,d)) \otimes \mathbb{Q}$ .

*Proof of Theorem 4.1.* Now we can complete the proof of Theorem 4.1. Denote by

$$\widetilde{v}: P_{r,n,d} \otimes \mathbb{Q} \to \operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d)) \otimes \mathbb{Q}$$

the unique homomorphism whose restriction to  $\operatorname{Pic}(\overline{\mathbb{M}}_{0,n+d})^{\mathfrak{S}_d}$  is v (see Definition 4.4), whose restriction to  $\operatorname{Pic}(\mathbb{P}^{r-1})$  sends  $\mathcal{O}_{\mathbb{P}^{r-1}}(1)$  to  $[\mathcal{H}_{\Lambda}]$ , whose restriction to the  $i^{\operatorname{th}}$  factor of  $\operatorname{Pic}(\mathbb{P}^1)^n$  sends  $\mathcal{O}_{\mathbb{P}^1}(1)$  to  $[\mathcal{L}_i]$  if  $n \geq 1$ , and whose restriction to the

last factor  $\operatorname{Pic}(\mathbb{P}^1)$  (assuming  $d \geq 2$ ) sends  $\mathcal{O}_{\mathbb{P}^1}(1)$  to 1/2  $[\mathcal{T}_{\Pi}]$ . By Lemma 4.6 (ii), (iii) and by Lemma 4.7,  $u \otimes \mathbb{Q} \circ \widetilde{v}$  is the identity map. In particular,  $\widetilde{v}$  is injective. By Proposition 4.8,  $\widetilde{v}$  is surjective. Thus  $\widetilde{v}$  and  $u \otimes \mathbb{Q}$  are isomorphisms.

Because  $\alpha$ ,  $\beta_i$  and  $\gamma$  are morphisms, for every NEF, resp. eventually free, divisor D in  $\operatorname{Pic}(\overline{\mathcal{M}}_{0,n}(\mathbb{P}^r,d))\otimes\mathbb{Q}, \ \alpha^*(D), \ \beta_i^*(D), \ \operatorname{and} \ \gamma^*(D)$  are NEF, resp. eventually free. Denote,

$$D_1 = \alpha_1^*(D), \quad a \ [\mathcal{O}_{\mathbb{P}^{r-1}}(1)] = \alpha_2^*(D), \quad b_i \ [\mathcal{O}_{\mathbb{P}^1}(1)] = \beta_i^*(D), \quad c \ [\mathcal{O}_{\mathbb{P}^1}(1)] = \gamma^*(D),$$

where by convention a is defined to be 0 if r=1 and c is defined to be 0 if d=1. If D is NEF, resp. eventually free,  $D_1$  is NEF, resp. eventually free, in  $Pic(\overline{M}_{0,n+d})^{\mathfrak{S}_d}$ , and  $a, b_i, c \geq 0$ .

Conversely, by Lemma 4.5, for every NEF, resp. eventually free, divisor  $D_1$  in  $\operatorname{Pic}(\overline{\mathbb{M}}_{0,n+d})^{\mathfrak{S}_d}$ ,  $v(D_1)$  is NEF, resp. eventually free. By Lemma 4.7(i), for  $a,b_i,c\geq 0$ ,  $a[\mathcal{H}_{\Lambda}]$ ,  $b_i[\mathcal{L}_{i,\Pi}]$  and c/2  $[\mathcal{T}_{\Pi}]$  are NEF and eventually free. Since a sum of NEF, resp. eventually free, divisors is NEF, resp. eventually free,  $D=v(D_1)+a$   $[\mathcal{H}_{\Lambda}]+b_i$   $[\mathcal{L}_i]+c/2$   $[\mathcal{T}_{\Pi}]$  is NEF, resp. eventually free. Therefore D is NEF if and only if  $u\otimes \mathbb{Q}(D)$  is in the product of the NEF cones of the factors. This argument needs to be modified in the obvious way when (n,d)=(0,3) and (1,2) to account for the slight variations in the formulae.

Because the interior of a product of cones equals the product of the interiors of the cones, by Kleiman's criterion, D is ample iff  $u \otimes \mathbb{Q}(D)$  is contained in the product of the ample cones of the factors.

Theorem 4.1 has the following important corollary.

**Theorem 4.9.** For every integer  $r \geq 1$  and  $d \geq 2$ , there is a contraction,

$$cont: \overline{M}_{0,0}(\mathbb{P}^r,d) \to Y,$$

restricting to an open immersion on the interior  $M_{0,0}(\mathbb{P}^r,d)$  and whose restriction to the boundary divisor  $\Delta_{k,d-k} \cong M_{0,1}(\mathbb{P}^r,k) \times_{\mathbb{P}^r} M_{0,1}(\mathbb{P}^r,d-k)$  factors through the projection to  $\overline{M}_{0,1}(\mathbb{P}^r,d-k)$  for each  $1 \leq k \leq \lfloor d/2 \rfloor$ . The following divisor is the pullback of an ample divisor on Y,

$$D_{r,d} = \mathcal{T} + \sum_{k=2}^{\lfloor d/2 \rfloor} k(k-1) \Delta_{k,d-k}.$$

Theorem 4.9 has implications for the study of rational curves on Fano manifolds. For instance J. Starr has proved the following nice consequence.

4.2. The effective cone of the Kontsevich moduli space. The main problem we would like to address is the following:

**Problem 4.10.** Describe the cone of effective divisor classes on  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^r,d)$  in terms of the standard generators of the Picard group.

Denote by  $P_d$  the  $\mathbb{Q}$ -vector space of dimension  $\lfloor d/2 \rfloor + 1$  with basis labeled  $\mathcal{H}$  and  $\Delta_{k,d-k}$  for  $k = 1, \ldots, \lfloor d/2 \rfloor$ . For each  $r \geq 2$ , there is a  $\mathbb{Q}$ -linear map

$$u_{d,r}: P_d \to \operatorname{Pic}(\overline{\mathcal{M}}_{0,0}(\mathbb{P}^r, d)) \otimes \mathbb{Q}$$

that is an isomorphism of  $\mathbb{Q}$ -vector spaces.

**Definition 4.11.** For every integer  $r \geq 2$ , denote by  $\mathrm{Eff}_{d,r} \subset P_d$  the inverse image under  $u_{d,r}$  of the effective cone of  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^r,d)$ .

**Proposition 4.12.** For every integer  $r \geq 2$ ,  $Eff_{d,r}$  is contained in  $Eff_{d,r+1}$ . For every integer  $r \geq d$ ,  $Eff_{d,r}$  equals  $Eff_{d,d}$ .

Proof of Proposition 4.12. Let  $p \in \mathbb{P}^{r+1}$  be a point, denote  $U = \mathbb{P}^{r+1} - \{p\}$ , and let  $\pi : U \to \mathbb{P}^r$  be a linear projection from p. This induces a smooth 1-morphism

$$\overline{\mathcal{M}}_{0,0}(\pi,d):\overline{\mathcal{M}}_{0,0}(U,d)\to\overline{\mathcal{M}}_{0,0}(\mathbb{P}^r,d).$$

Let  $i: U \to \mathbb{P}^{r+1}$  be the open immersion. This induces a 1-morphism

$$\overline{\mathcal{M}}_{0,0}(i,d):\overline{\mathcal{M}}_{0,0}(U,d)\to\overline{\mathcal{M}}_{0,0}(\mathbb{P}^{r+1},d)$$

relatively representable by open immersions. The complement of the image of  $\overline{\mathcal{M}}_{0,0}(i,d)$  has codimension r, which is greater than 2. Therefore, the pull-back morphism

$$\overline{\mathcal{M}}_{0,0}(i,d)^* : \operatorname{Pic}(\overline{\mathcal{M}}_{0,0}(\mathbb{P}^{r+1},d)) \to \operatorname{Pic}(\overline{\mathcal{M}}_{0,0}(U,d))$$

is an isomorphism. So there is a unique homomorphism

$$h: \operatorname{Pic}(\overline{\mathcal{M}}_{0,0}(\mathbb{P}^r, d)) \to \operatorname{Pic}(\overline{\mathcal{M}}_{0,0}(\mathbb{P}^{r+1}, d))$$

such that

$$\overline{\mathcal{M}}_{0,0}(\pi,d)^* = \overline{\mathcal{M}}_{0,0}(i,d)^* \circ h.$$

Recalling from the introduction that u(r,d) is the map that identifies the Picard group of  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^r,d)$ ) with the vector space spanned by  $\mathcal{H}$  and the boundary divisors  $\Delta_{k,d-k}$ , we see that  $h \circ u_{d,r}$  equals  $u_{d,r+1}$ . So to prove  $\mathrm{Eff}_{d,r}$  is contained in  $\mathrm{Eff}_{d,r+1}$ , it suffices to prove that  $\overline{\mathcal{M}}_{0,0}(\pi,d)$  pulls back effective divisors to effective divisors classes, which follows since  $\overline{\mathcal{M}}_{0,0}(\pi,d)$  is smooth.

Next assume  $r \geq d$ . Let D be any effective divisor in  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^r,d)$ . A general point in the complement of D parameterizes a stable map  $f: C \to \mathbb{P}^r$  such that f(C) spans a d-plane. Denote by  $j: \mathbb{P}^d \to \mathbb{P}^r$  a linear embedding whose image is this d-plane. There is an induced 1-morphism

$$\overline{\mathcal{M}}_{0,0}(j,d):\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)\to\overline{\mathcal{M}}_{0,0}(\mathbb{P}^r,d).$$

The map  $\overline{\mathcal{M}}_{0,0}(j,d)^* \circ u_{d,r}$  equals  $u_{d,d}$ . By construction,  $\overline{\mathcal{M}}_{0,0}(j,d)^*([D])$  is the class of the effective divisor  $\overline{\mathcal{M}}_{0,0}(j,d)^{-1}(D)$ , i.e., [D] is in  $\mathrm{Eff}_{d,d}$ . Thus  $\mathrm{Eff}_{d,d}$  contains  $\mathrm{Eff}_{d,r}$ , which in turn contains  $\mathrm{Eff}_{d,d}$  by the last paragraph. Therefore  $\mathrm{Eff}_{d,r}$  equals  $\mathrm{Eff}_{d,d}$ .

In view of Proposition 4.12 it is especially interesting to understand  $\mathrm{Eff}_{d,d}$ . We will concentrate on this case.

When r = d, the locus parameterizing stable maps  $f: C \to \mathbb{P}^d$  of degree d whose set theoretic image does not span  $\mathbb{P}^d$ . We will denote its class by  $D_{\text{deg}}$ . The class is easily calculated in terms of the standard divisors.

**Lemma 4.13.** The class  $D_{deq}$  equals

$$D_{deg} = \frac{1}{2d} \left[ (d+1)\mathcal{H} - \sum_{k=1}^{\lfloor d/2 \rfloor} k(d-k)\Delta_{k,d-k} \right]. \tag{2}$$

*Proof.* We will prove the equality (2) by intersecting  $D_{\text{deg}}$  by test curves. Fix a general rational normal scroll of degree i and a general rational normal curve of degree d-i-1 intersecting the scroll in one point p. Consider the one-parameter family  $C_i$  of degree d curves consisting of the fixed degree d-i-1 rational normal curve union curves in a general pencil (that has p as a base-point) of degree i+1 rational normal curves on the scroll. When  $2 \le i \le \lfloor d/2 \rfloor$ ,  $C_i$  has the following intersection numbers with  $\mathcal{H}$  and  $D_{\text{deg}}$ .

$$C_i \cdot \mathcal{H} = i, \quad C_i \cdot D_{\text{deg}} = 0.$$

The curve  $C_i$  is contained in the boundary divisor  $\Delta_{i+1,d-i-1}$  and has intersection number

$$C_i \cdot \Delta_{i+1} d_{-i-1} = -1$$

with it. The intersection number of  $C_i$  with the boundary divisors  $\Delta_{i,d-i}$  and  $\Delta_{1,d-1}$  is non-zero and given as follows:

$$C_i \cdot \Delta_{i,d-i} = 1, \quad C_i \cdot \Delta_{1,d-1} = i + 1.$$

Finally, the intersection number of  $C_i$  with all the other boundary divisors is zero. When i=1, we have to modify the intersection number of  $C_1$  with  $\Delta_{1,d-1}$  to read  $C_1 \cdot \Delta_{1,d-1} = 3$ . Next consider the one-parameter family  $B_1$  of rational curves of degree d that contain d+2 general points and intersect a general line. The intersection number of  $B_1$  with all the boundary divisors but  $\Delta_{1,d-1}$  is zero. Clearly  $B_1 \cdot D_{\text{deg}} = 0$ . By the algorithm for counting rational curves in projective space given in [V] it follows that

$$B_1 \cdot \mathcal{H} = \frac{d^2 + d - 2}{2}, \quad B_1 \cdot \Delta_{1,d-1} = \frac{(d+2)(d+1)}{2}.$$

This determines the class of  $D_{\text{deg}}$  up to a constant multiple. In order to determine the multiple, consider the curve C that consists of a fixed degree d-1 curve and a pencil of lines in a general plane intersecting the curve in one point. The curve C has intersection number zero with all the boundary divisors but  $\Delta_{1,d-1}$  and has the following intersection numbers:

$$C \cdot \mathcal{H} = 1$$
,  $C \cdot D_{\text{deg}} = 1$ ,  $C \cdot \Delta_{1,d-1} = -1$ .

The lemma follows from these intersection numbers.

 $D_{\text{deg}}$  plays a crucial role in describing the effective cone of  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$ . The following theorem completely describes the effective cone of  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$ .

**Theorem 4.14.** The class of a divisor lies in the effective cone of  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$  if and only if it is a non-negative linear combination of the class of  $D_{deg}$  and the classes of the boundary divisors  $\Delta_{k,d-k}$  for  $1 \le k \le \lfloor d/2 \rfloor$ .

Following Keel one may reduce the proof of this theorem to determining the effective cone of  $\overline{M}_{0,d}/\mathfrak{S}_d$ . However, this proof is not significantly simpler and has the disadvantage that it does not generalize to other contexts. We will therefore give a better proof.

*Proof.* Since  $D_{\text{deg}}$  and the boundary divisors are effective, any non-negative rational linear combination of these divisors lies in the effective cone. The main content of the theorem is to show that there are no other effective divisor classes.

**Definition 4.15.** A reduced, irreducible curve C on a scheme X is a moving curve if the deformations of C cover a Zariski open subset of X. More precisely, a curve C is a moving curve if there exists a flat family of curves  $\pi : C \to T$  on X such that  $\pi^{-1}(t_0) = C$  for  $t_0 \in T$  and for a Zariski open subset  $U \subset X$  every point  $x \in U$  is contained in  $\pi^{-1}(t)$  for some  $t \in T$ . We call the class of a moving curve a moving curve class.

An obvious observation is that the intersection pairing between the class of an effective divisor and a moving curve class is always non-negative. Intersecting divisors with a moving curve class gives an inequality for the coefficients of an effective divisor class. The strategy for the proof of Theorem 4.14 is to produce enough moving curves to force the effective divisor classes to be a non-negative linear combination of  $D_{\rm deg}$  and the boundary classes.

**Lemma 4.16.** If  $C \subset \overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$  is a reduced, irreducible curve that intersects the complement in  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$  of the boundary divisors and the divisor of maps whose image is degenerate, then C is a moving curve.

*Proof.* The automorphism group of  $\mathbb{P}^d$  acts transitively on rational normal curves. An irreducible curve of degree d that spans  $\mathbb{P}^d$  is a rational normal curve. Hence, a curve  $C \subset \overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$  that intersects the complement in  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$  of the boundary divisors and the divisor of maps whose image is degenerate, contains a point that represents a map that is an embedding of  $\mathbb{P}^1$  as a rational normal curve. The translations of C by  $\mathbb{P}GL(d+1)$  cover a Zariski open set of  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$ .  $\square$ 

First, observe that if D is an effective divisor on  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$  and D has the class

$$a\mathcal{H} + \sum_{k=1}^{\lfloor d/2 \rfloor} b_{k,d-k} \Delta_{k,d-k},$$

then  $a \geq 0$ . Furthermore, if a = 0, then  $b_{k,d-k} \geq 0$ . Consider a general projection of the d-th Veronese embedding of  $\mathbb{P}^2$  to  $\mathbb{P}^d$ . Consider the image of a pencil of lines in  $\mathbb{P}^2$ . By Lemma 4.16 this is a moving one-parameter family C of degree d rational curves that has intersection number zero with the boundary divisors. It follows from the inequality  $C \cdot D \geq 0$  that  $a \geq 0$ .

Furthermore, suppose that a=0. Consider a general pencil of (1,1) curves on  $\mathbb{P}^1 \times \mathbb{P}^1$ . Take a general projection to  $\mathbb{P}^d$  of the embedding of  $\mathbb{P}^1 \times \mathbb{P}^1$  by the linear system  $\mathcal{O}_{\mathbb{P}^1 \times \mathbb{P}^1}(i,d-i)$ . By Lemma 4.16 the image of the pencil gives a moving one-parameter family C of degree d curves whose intersection with  $\Delta_{k,d-k}$  is zero unless k=i. The relation  $C \cdot D \geq 0$  implies that if a=0, then  $b_{i,d-i} \geq 0$ . We conclude that Theorem 4.14 is true if a=0. We can, therefore, assume that a>0.

Suppose that for every  $1 \leq i \leq \lfloor d/2 \rfloor$ , we could construct a moving curve  $C_i$  in  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$  with the property that  $C_i \cdot \Delta_{k,d-k} = 0$  for  $k \neq i$  and that the ratio of  $C_i \cdot \Delta_{i,d-i}$  to  $C_i \cdot \mathcal{H}$  is given by

$$\frac{C_i \cdot \Delta_{i,d-i}}{C_i \cdot \mathcal{H}} = \frac{d+1}{i(d-i)}.$$
 (3)

Observe that given these intersection numbers, Lemma 4.13 implies that  $C_i \cdot D_{\text{deg}} = 0$ . Theorem 4.14 follows from the inequalities  $C_i \cdot D \geq 0$ .

We now construct approximations to these curves.

**Proposition 4.17.** Let k, j and d be positive integers subject to the condition that  $2k \leq d$ . There exists an integer n(k, d) depending only on k and d such that the linear system

$$L'(j) = d F_1 + \left(\frac{jk(k+1)}{2} - 1\right) F_2 - \sum_{i=1}^{j(d+1) - n(k,d)} k E_i - \sum_{i=j(d+1) - n(k,d) + 1}^{j(d+1) + n(k,d) \frac{(k-1)(k+2)}{2}} E_i$$

on the blow-up of  $\mathbb{P}^1 \times \mathbb{P}^1$  at  $j(d+1) + n(k,d) \frac{(k-1)(k+2)}{2}$  general points is non-special for every j >> 0. The integer n(k,d) may be taken to be

$$n(k,d) = \lceil 2(d+1)/k \rceil.$$

Proposition 4.17 implies Theorem 4.14. As in the previous subsection we consider the blow-up of  $\mathbb{P}^1 \times \mathbb{P}^1$  in

$$j(d+1) + \frac{n(k,d)(k-1)(k+2)}{2}$$

general points. The proper transform of the fibers  $F_2$  under the linear system

$$d\ F_1 + \frac{jk(k+1)}{2}\ F_2 - \sum_{i=1}^{j(d+1)-n(k,d)} k\ E_i - \sum_{i=j(d+1)-n(k,d)+1}^{j(d+1)+n(k,d)\frac{(k-1)(k+2)}{2}} E_i$$

gives a one-parameter family  $C_k(j)$  of rational curves of degree d that has intersection number zero with  $D_{\text{deg}}$ . Letting j tend to infinity we obtain a sequence of moving curves  $C_k(j)$  in  $\overline{\mathcal{M}}_{0,0}(\mathbb{P}^d,d)$  that has intersection zero with all the boundary divisors but  $\Delta_{1,d-1}$  and  $\Delta_{k,d-k}$ . Unfortunately, the intersection of  $C_k(j)$  with  $\Delta_{1,d-1}$  is not zero and the ratio of  $C_k(j) \cdot \mathcal{H}$  to  $C_k(j) \cdot \Delta_{k,d-k}$  is not the one required by Equation (3). However, as j tends to infinity, the ratio of the intersection numbers  $C_k(j) \cdot \Delta_{1,d-1}$  to  $C_k(j) \cdot \mathcal{H}$  tends to zero and the ratio of  $C_k(j) \cdot \Delta_{k,d-k}$  to  $C_k(j) \cdot \mathcal{H}$  tends to the desired ratio  $\frac{d+1}{k(d-k)}$ . Theorem 4.14 follows.

Proof of Proposition 4.17. The specialization technique in §2 of [Ya] yields the proof of the proposition. We will specialize the points of multiplicity k one by one onto a point q. At each stage the k-fold point that we specialize will be in general position. We will first slide the point along a fiber  $f_1$  in the class  $F_1$  onto the fiber  $f_2$  in the fiber class  $F_2$  containing the point q. We then slide the point onto q along  $f_2$ . We will record the flat limit of this degeneration.

There is a simple checker game that describes the limits of these degenerations. This checker game for  $\mathbb{P}^2$  is described in §2 of [Ya]. The details for  $\mathbb{P}^1 \times \mathbb{P}^1$  are identical. The global sections of the linear system  $\mathcal{O}_{\mathbb{P}^1 \times \mathbb{P}^1}(a,b)$  are bi-homogeneous polynomials of bi-degree a and b in the variables x,y and z,w, respectively. A basis for the space of global sections is given by  $x^iy^{a-i}z^jw^{b-j}$ , where  $0 \le i \le a$  and  $0 \le j \le b$ . We can record these monomials in a rectangular  $(a+1) \times (b+1)$  grid. In this grid the box in the i-th row and the j-th column corresponds to the monomial  $x^iy^{a-i}z^jw^{b-j}$ .

If we impose an ordinary k-fold point on the linear system at ([x:y], [z:w]) = ([0:1], [0:1]), then the coefficients of the monomials

$$y^a w^b, xy^{a-1} w^b, \dots, x^{k-1} y^{a-k+1} z^{k-1} w^{b-k+1}$$

FIGURE 8. Imposing a triple point on  $\mathcal{O}_{\mathbb{P}^1 \times \mathbb{P}^1}(4,6)$ .

must vanish. We depict this by filling in a  $k \times k$  triangle of checkers into the boxes at the upper left hand corner as in Figure 8. The coefficients of the monomials represented by boxes that have checkers in them must vanish.

We first slide the k-fold point along the fiber  $f_1$  onto the point ([x:y], [z:w]) = ([1:0], [0:1]). This correspond to the degeneration

$$([x:y],[z:w]) \mapsto ([x:ty],[z:w]).$$

The flat limit of this degeneration is described by the vanishing of the coefficients of certain monomials (assuming none of the checkers fall out of the rectangle). The monomials whose coefficients must vanish are those that correspond to boxes with checkers in them when we let the checkers fall according to the force of gravity. The first two panels in Figure 9 depict the result of applying this procedure to a 4-fold point when there is an aligned ideal condition at the point ([x:y], [z:w]) = ([1:0], [1:0]).

We then follow this degeneration with a degeneration that specializes the k-fold point to q by sliding along the fiber  $f_2$ . This degeneration is explicitly given by

$$([x:y],[z:w]) \mapsto ([x:y],[z:tw]).$$

The flat limit is described by the vanishing of the coefficients of the monomials that have checkers in them when we slide all the checkers as far right as possible. The last two panels of Figure 9 depict this degeneration.

FIGURE 9. Depicting the degenerations by checkers.

S. Yang proves that, provided none of the checkers fall out of the ambient rectangle during these moves, these checker movements do correspond to the flat limits of the linear systems under the given degenerations. If one can play this checker game with all the multiple points that one imposes on a linear system so that during the game none of the checkers fall out of the rectangle, one can conclude that the multiple points impose independent conditions on the linear system. The limit linear

system has the expected dimension. In particular, it is non-special. By upper semicontinuity the original linear system must also have the expected dimension and be non-special. Unfortunately, when one plays this game, occasionally checkers may fall out of the rectangle. In that case we lose information on what the limits are. This may happen even if the original linear system has the expected dimension.

In order to conclude the proposition we need to show that if we impose at most j(d+1)-n(k,d) points of multiplicity k on the linear system  $\mathcal{O}_{\mathbb{P}^1\times\mathbb{P}^1}(d,jk(k+1)/2)$  where  $2k \leq d$ , we do not lose any checkers when we specialize all the k-fold points by the degeneration just described. This suffices to conclude the proposition because general simple points always impose independent conditions.

The main observation is that if there is a safety net of empty boxes at the top of the rectangle, then the checkers will not fall out of the box. The proof of the proposition is completed by noting the following simple facts.

- (1) At any stage of the degeneration the height of the checkers in the rectangle is at most k larger than the highest row full of checkers.
- (2) The left most checker of a row is to the lower left of the left most checker of any row above it.

If there are at least (k+1)(d+1) empty boxes in our rectangle, then by the above two observations when we specialize a k-fold point we do not lose any of the checkers. As long as  $n(k,d) \geq \lceil 2(d+1)/k \rceil$ , there is always at least (k+1)(d+1) boxes empty. Hence until the stage where we specialize the last k-fold point we cannot lose any checkers. This concludes the proof.

This also concludes the proof of the theorem.

**Remark 4.18.** We observe that both Theorem 4.1 and Theorem 4.14 admit generalizations to other homogeneous targets. These may be proved using the methods developed here.

Exercise 4.19. Determine the ample and stable effective cones of the Kontsevich moduli space of stable maps into Grassmannians.

#### References

- [CH1] L. Caporaso and J. Harris. Counting plane curves of any genus. Invent. Math. 131 no.2(1998), 345–392.
- [CH2] L. Caporaso and J. Harris. Enumerating rational curves: the rational fibration method. Compositio Math. 113 no.2(1998), 209–236.
- [CHS1] I. Coskun, J. Harris, and J. Starr. The ample cone of the Kontsevich moduli space. submitted.
- [CHS2] I. Coskun, J. Harris, and J. Starr. The effective cone of the Kontsevich moduli space.
- [Ful] W. Fulton. Intersection theory, volume 2 of Ergebnisse der Mathematik und ihrer Grenzgebiete. 3. Folge. A Series of Modern Surveys in Mathematics. Springer-Verlag, Berlin, second edition, 1998.
- [FP] W. Fulton and R. Pandharipande. Notes on stable maps and quantum cohomology. In Algebraic geometry—Santa Cruz 1995, volume 62 Part 2 of Proc. Sympos. Pure Math., pages 45–96. Amer. Math. Soc., 1997.
- [Ha] R. Hartshorne. Algebraic geometry. Springer-Verlag, New York, 1977. Graduate Texts in Mathematics, No. 52.
- [KP] B. Kim and R. Pandharipande. The connectedness of the moduli space of maps to homogeneous spaces. In Symplectic geometry and mirror symmetry (Seoul, 2000), pages 187–201. World Sci. Publishing, River Edge, NJ, 2001.

- R. Pandharipande. Intersections of **Q**-divisors on Kontsevich's moduli space  $\overline{M}_{0,n}(\mathbf{P}^r,d)$ [Pa] and enumerative geometry. Trans. Amer. Math. Soc. 351(1999), 1481–1505.
- R. Vakil. The enumerative geometry of rational and elliptic curves in projective space. J. [V] Reine Angew. Math.  $\bf 529 (2000), 101-153.$ S. Yang. Linear systems in  $P^2$  with base points of bounded multiplicity. preprint.
- [Ya]

---

# THE KODAIRA DIMENSION OF THE MODULI SPACE OF CURVES

## 1. Preliminaries

A great reference for background about linear systems, big and ample line bundles and Kodaira dimensions is [L]. Here we will only develop a few basics that will be necessary for our discussion of the Kodaira dimension of the moduli space of curves.

Let L be a line bundle on a normal, irreducible, projective variety X. The semi-group N(X,L) of L is defined to be the non-negative powers of L that have a non-zero section:

$$N(X,L) := \{ m \ge 0 : H^0(X,L^{\otimes m}) > 0 \}.$$

Given  $m \in N(X, L)$  we can consider the rational map  $\phi_m$  associated to  $L^{\otimes m}$ .

**Definition 1.1.** Let L be a line bundle on a normal, irreducible, projective variety. Then the Iitaka dimension of L is defined to be the maximum dimension of the image of  $\phi_m$  for  $m \in N(X, L)$  provided  $N(X, L) \neq 0$ . If N(X, L) = 0, then the Iitaka dimension of L is defined to be  $-\infty$ . When X is smooth, the Kodaira dimension of X is defined to be the Iitaka dimension of its canonical bundle  $K_X$ . If X is singular, the Kodaira dimension of X is defined to be the Kodaira dimension of any desingularization of X.

**Remark 1.2.** Note that by definition the Iitaka dimension of a line bundle L on X is an integer between 0 and  $\dim(X)$  or it is  $-\infty$ .

**Definition 1.3.** A line bundle L on a normal, projective variety is called big if its litaka dimension is equal to the dimension of X. A smooth, projective variety is called of general type if its canonical bundle is big. A singular variety is called of general type if a desingularization is of general type.

**Remark 1.4.** Of course, the same definitions can be made for Cartier (or even Q-Cartier) divisors instead of line bundles. Below we will use the language of Cartier divisors and line bundles interchangably.

An alternative definition of big line bundles in terms of cohomology is given by the following well-known lemma.

**Lemma 1.5.** A line bundle L on a normal, projective variety X of dimension n is big if and only if there exists a positive constant C such that

$$h^0(X, L^{\otimes m}) \ge Cm^n$$

for all sufficiently large  $m \in N(X, L)$ .

Kodaira's Lemma allows us to obtain other useful characterizations of big line bundles.


**Lemma 1.6** (Kodaira's Lemma). Let D be a big Cartier divisor and E be an arbitrary effective Cartier divisor on a normal, projective variety X. Then

$$H^0(X, \mathcal{O}_X(mD-E)) \neq 0$$

for all sufficiently large  $m \in N(X, D)$ .

*Proof.* Consider the exact sequence

$$0 \to \mathcal{O}_X(mD - E) \to \mathcal{O}_X(mD) \to \mathcal{O}_E(mD) \to 0.$$

Since D is big by assumption, the dimension of global sections of  $\mathcal{O}_X(mD)$  grows like  $m^{\dim(X)}$ . On the other hand,  $\dim(E) < \dim(X)$ , hence the dimension of global sections of  $\mathcal{O}_E(mD)$  grows at most like  $m^{\dim(X)-1}$ . It follows that

$$h^0(X, \mathcal{O}_X(mD)) > h^0(E, \mathcal{O}_E(mD))$$

for large enough  $m \in N(X, D)$ . The lemma follows by the long exact sequence of cohomology associated to the exact sequence of sheaves.

A corollary of Kodaira's Lemma is the characterization of big divisors as those divisors that are numerically equivalent to the sum of an ample and an effective divisor. We will use this characterization in determining the Kodaira dimension of the moduli space of curves.

**Proposition 1.7.** Let D be a divisor on a normal, irreducible projective variety X. Then the following are equivalent:

- (1) D is big.
- (2) For any ample divisor A, there exists an integer m > 0 and an effective divisor E such that mD is linearly equivalent to A + E.
- (3) There exists an ample divisor A, an integer m > 0 and an effective divisor E such that mD is linearly equivalent to A + E.
- (4) There exists an ample divisor A, an integer m > 0 and an effective divisor E such that mD is numerically equivalent to A + E.

*Proof.* To prove that (1) implies (2) given any ample divisor A, take a large enough positive number r such that both rA and (r+1)A are effective. By Kodaira's Lemma there is a positive integer m such that mD - (r+1)A is effective, say linearly equivalent to an effective divisor E. We thus get that mD is linearly equivalent to A + (rA + E) proving (2). Clearly (2) implies (3) and (3) implies (4). To see that (4) implies (1), since mD is numerically equivalent to A + E, mD - E is numerically equivalent to an ample divisor. Since ampleness is numerical, mD - E is ample. Since ample divisors are big and

$$h^0(X, mD) \ge h^0(X, mD - E),$$

D is big.

# 2. The canonical bundle of the moduli space of curves

We can calculate the canonical class of the moduli space of curves using the Grothendieck - Riemann - Roch formula.

**Theorem 2.1.** The canonical class of the coarse moduli scheme  $\overline{M}_g$  is given by

$$K_{\overline{M}_g} = 13\lambda - 2\delta - \delta_1.$$

*Proof.* The cotangent bundle of  $\overline{\mathrm{M}}_g$  at a smooth, automorphism-free curve is given by the space of quadratic differentials. More generally, over the automorphism-free locus the canonical bundle will be the first chern class of

$$\pi_*(\Omega_{\overline{\mathrm{M}}_{q,1}/\overline{\mathrm{M}}_q} \otimes \omega_{\overline{\mathrm{M}}_{q,1}/\overline{\mathrm{M}}_q}).$$

We can easily calculate this class in the Picard group of the moduli functor:

$$\pi_* \left( (1 + c_1(\Omega \otimes \omega) + \frac{c_1^2(\Omega \otimes \omega)}{2} - c_2(\Omega \otimes \omega))(1 - \frac{c_1(\Omega)}{2} + \frac{c_1^2(\Omega) + c_2(\Omega)}{12}) \right)$$

Expanding (and using the relations we proved in the last unit) we see that this expression equals

$$\pi_* \left( 2c_1^2(\omega) - [Sing] - c_1^2(\omega) + \frac{c_1^2(\omega) + [Sing]}{12} \right) = 13\lambda - 2\delta.$$

We need to adjust this formula to take into account that every element of the locus of curves with an elliptic tail have an automorphism given by the hyperelliptic involution on the elliptic tail. The effect of this can be calculated in local coordinates to see that it introduces a simple zero along that locus.  $\Box$ 

Remark 2.2. One word of caution is in order. Recall that  $\delta_1$  does not descend to the coarse moduli scheme because every curve in the boundary locus has an automorphism of order 2. However,  $\delta_1^2$  descends to the coarse moduli scheme. Accordingly we defined the class  $\delta_1$  as half of the class of the boundary locus  $\Delta_1$ . In terms of the class of the loci of reducible curves the canonical class is

$$13\lambda - 2[\Delta] + \frac{1}{2}[\Delta_1].$$

# 3. Ample divisors on the moduli space of curves

In order to show that the moduli space is of general type we need to show that the canonical bundle is big (on a desingularization). In view of the discussion in the first section we can try to express the canonical bundle as a sum of an ample and an effective divisor. The G.I.T. construction gives us a large collection of ample divisors.

For our purposes we need only the following fact:

# **Lemma 3.1.** The divisor class $\lambda$ is big and NEF.

Proof. The shortest proof of this result is based on some facts about the Torelli map and the moduli spaces of abelian varieties. We can map the moduli space of curves  $\overline{\mathrm{M}}_g$  to the moduli space  $A_g$  of principally polarized abelian varieties of dimension g by sending C to the pair  $(Jac(C), \Theta)$  consisting of the Jacobian of C and the theta divisor. In characteristic zero this map extends from  $\overline{\mathrm{M}}_g$  to the Satake compactification. The class  $\lambda$  is a multiple of the pull-back of  $\mathcal{O}_{\mathbb{P}^n}(1)$  from the embedding of  $A_g$  by theta constants. The lemma follows.

A much more precise theorem due Cornalba and Harris [CH] determines the restriction of the ample cone of  $\overline{\mathrm{M}}_g$  to the plane spanned by  $\lambda$  and  $\delta$ .

**Theorem 3.2.** Let a and b be any positive integers. Then the divisor class  $a\lambda - b\delta$  is ample on  $\overline{M}_q$  if and only if a > 11b.

For a nice exposition of the proof see [HM1] §6.D.

**Remark 3.3.** Note that  $\lambda$  itself is not ample, but since it is big it is a sum of an ample and an effective divisor. Consequently, it suffices to express the canonical bundle of  $\overline{\mathrm{M}}_q$  as a sum of  $\lambda$  and an effective divisor.

#### 4. The moduli space is of general type

In this section we would like to sketch the main steps of the proof of the following fundamental theorem due to Harris, Mumford and Eisenbud. You can read more about the details in [HM1] §6.F. The papers [HM2], [H] and [EH5] contain the proofs.

**Theorem 4.1.** The moduli space of curves  $\overline{M}_g$  is of general type if  $g \geq 24$ .

The strategy of the proof is to show that the canonical class of the moduli space of curves is numerically equivalent to the sum of an ample and an effective divisor. We already know that the class of any divisor on the moduli space may be expressed as a linear combination of the classes  $\lambda$  and the boundary divisors  $\delta_i$ .

We know that the canonical class of  $\overline{\mathrm{M}}_q$  is given by the formula

$$K_{\overline{M}_a} = 13\lambda - 2\delta - \delta_1.$$

We also know that since  $(11 + \epsilon)\lambda - \delta$  is ample,  $\lambda$  is big. Hence if we could find an effective divisor

$$a\lambda - b_0\delta_{irr} - b_1\delta_1 - \dots - b_{\lfloor g/2\rfloor}\delta_{\lfloor g/2\rfloor}$$

satisfying the inequalities

$$\frac{a}{b_i} < \frac{13}{2}, \quad \frac{a}{b_1} < \frac{13}{3}$$

then this will show that the canonical bundle is big because it may be expressed as the sum of a big and effective class.

There are two main difficulties with the approach we have outlined so far. First the construction of effective divisors with small slope is a difficult problem. We will see that the Brill-Noether and Petri divisors will do the job for Theorem 4.1. However, the calculation of these divisor classes are not easy.

The second problem is that even if we show that there are many canonical forms on  $\overline{M}_g$ , this does not necessarily prove that the moduli space is of general type. The problem is that  $\overline{M}_g$  is singular. It is possible that canonical forms defined on the smooth locus do not extend to a desingularization. In fact, this is not the case. All the singularities of  $\overline{M}_g$  are canonical, hence the canonical forms defined on the smooth locus extend to any desingularization. More precisely:

**Theorem 4.2.** Let  $g \ge 4$ . Then for every n, the n-canonical forms defined on the locus of curves without automorphisms extend to n-canonical forms on a desingularization of  $\overline{M}_q$ .

A sketch of some ideas. We will briefly outline some of the main ideas that go into the proof. For a complete argument see [HM2].

The proof relies on Reid-Tai Criterion. Let G be a finite group acting on a finite dimensional vector space V linearly. Let  $V^0$  be the locus where the action is free. The Reid-Tai criterion answers the question of when pluri-canonical forms extend from  $V^0/G$  to a desingularization of V/G. For all  $g \in G$ , let g be conjugate to a matrix  $Diag(\zeta^{a_1}, \ldots, \zeta^{a_d})$  where  $\zeta$  is a primitive mth root of unity and  $0 \le a_i < m$ . If for all  $g \in G$  and  $\zeta$ 

$$\sum_{i=1}^{d} \frac{a_i}{m} \ge 1$$

then any pluri-canonical form on  $V^0/G$  extends holomorphically to a desingularization of V/G.

In view of the Reid-Tai Criterion one has to check whether  $\sum_{i=1}^d \frac{a_i}{m} \geq 1$  holds and in cases it does not hold verify by hand that the pluri-canonical sections extend holomorphically to a desingularization. The following theorem characterizes the stable curves that fail to satisfy the Reid-Tai criterion.

**Theorem 4.3.** Let C be a stable curve of arithmetic genus  $g \geq 4$ . Let  $\phi$  be an automorphism of C of order n. Let  $\zeta$  be a primitive n-th root of unity and suppose that the action of  $\phi$  on  $H^0(\Omega_C \otimes \omega_C)$  is given by  $Diag(\zeta^{a_1}, \ldots, \zeta^{a_{3g-3}})$ . Then one of the following possibilities hold:

- (1)  $\sum_{i=1}^{3g-3} \frac{a_i}{m} \ge 1$ .
- (2) C is the union of an elliptic or one-nodal rational curve  $C_1$  meeting a curve  $C_2$  of genus g-1 at one point.  $\phi$  is the hyperelliptic involution on  $C_1$  and the identity on  $C_2$ .
- (3) C is the union of the elliptic curve  $C_1$  with j invariant 0 meeting a curve  $C_2$  of genus g-1 at one point.  $\phi$  is an order 6 automorphism of  $C_1$  and is the identity on  $C_2$ .
- (4) C is the union of the elliptic curve  $C_1$  with j invariant  $12^3$  meeting a curve  $C_2$  of genus g-1 at one point.  $\phi$  is an order 4 automorphism of  $C_1$  and is the identity on  $C_2$ .

The proof of this result rests on a case by case analysis of the possibilities based on a lemma that solves the problem for smooth curves.

**Lemma 4.4.** Let C be a smooth curve. Let  $\phi$  be an automorphism of C of order n. Let  $\zeta$  be a primitive n-th root of unity and suppose that the action of  $\phi$  on  $H^0(\Omega_C \otimes \omega_C)$  is given by  $Diag(\zeta^{a_1}, \ldots, \zeta^{a_{3g-3}})$ . Then one of the following possibilities hold:

- (1)  $\sum_{i=1}^{3g-3} \frac{a_i}{m} \ge 1$ .
- (2) C is a genus zero or one curve.
- (3) C is a hyperelliptic curve of genus 2 or 3 and  $\phi$  is the hyperelliptic involution.
- (4) C is a genus 2 curve which is the double cover of an elliptic curve and  $\phi$  is the involution exchanging the branches.

The proof of the lemma is based on an analysis of the possibilities using the Riemann-Hurwitz formula.

The final step of the proof is to check by explicit computation that pluri-canonical forms extend to the resolution of the singularities over the loci that do not satisfy the Reid-Tai Criterion.

The fact that  $\overline{\mathrm{M}}_g$  has canonical singularities allows us to carry out the naive program outlined above. We need effective divisors of small slope. The locus of curves that admit a degree d map to  $\mathbb{P}^r$  where g, r, d satisfy the equality

$$g - (r+1)(g - d + r) = -1$$

form a divisor on  $\overline{\mathcal{M}}_g$  called the Brill-Noether divisor. Its class is given by the following theorem:

**Theorem 4.5.** If g + 1 = (r + 1)(g - d + r), then the class of the Brill-Noether divisor on  $\overline{M}_g$  is given by

$$c\left((g+3)\lambda - \frac{g+1}{6}\delta_{irr} - \sum_{i=1}^{\lfloor g/2\rfloor} i(g-i)\delta_i\right)$$

where c is a positive rational constant.

Unfortunately this divisor exists only when g+1 is composite. When g is composite and g+1 is not, every curve admits finitely many degree d maps to  $\mathbb{P}^r$  where

$$q - (r+1)(q-d+r) = 0.$$

The number of such maps may be determined by Schubert calculus. We can then try to define a divisor by asking that some of these maps not be distinct. This will essentially be the Petri divisor (we will give a more precise definition below).

**Example 4.6.** The Petri divisors in g=4 and 6 are fun to describe. Consider a smooth, non-hyperelliptic curve C of genus 4. The canonical model of such a curve is the complete intersection in  $\mathbb{P}^3$  of a quadric and a cubic surface. Such a curve lies on a unique quadric surface. If the quadric is a smooth quadric surface, then C possesses two (distinct)  $g_3^1$ s. They are given by projection to either of the factors of  $\mathbb{P}^1 \times \mathbb{P}^1$ . In codimension one C lies on a quadric cone. For such curves the two  $g_3^1$ s come together. The Petri divisor is simply the closure of such curves.

**Exercise 4.7.** Calculate the class of the divisor given by the closure of curves whose canonical model lies in a singular quadric.

Let C be a smooth, non-hyperelliptic curve of genus 6. A general such curve C lies on a Del Pezzo surface of degree 5 and contains 5 distinct  $g_6^2$ s corresponding to the ways of blowing down  $D_5$  to  $\mathbb{P}^2$ . If C lies on a Del Pezzo surface with double points, then these  $g_6^2$ s are no longer distinct. Again the Petri divisor is the closure of the locus of such curves.

The Petri divisor is defined as the closure of the union of codimension one loci in  $\overline{\mathrm{M}}_g$  of curves which possess a linear series  $V \subset H^0(C,L)$  of degree d and dimension 1 such that the multiplication map

$$V \otimes H^0(C, K \otimes L^{-1}) \to H^0(C, K)$$

is not injective.

**Theorem 4.8.** Let g = 2(d-1). Then the class of the Petri divisor is given by

$$\frac{2(2d-4)!}{d!(d-2)!} \left( (6d^2+d-6)\lambda - d(d-1)\delta_{irr} - (2d-3)(3d-2)\delta_1 - \cdots \right)$$

where the coefficients of the remaining boundary divisors are negative and larger in absolute value than that of  $\delta_1$  (at least when d > 4).

The Brill-Noether and Petri divisors give us the necessary divisors to conclude the proof of Theorem 4.1. When  $g \geq 24$  and odd, we can use the Brill-Noether divisor with r = 1. The relevant ratio is that of  $\lambda$  and  $\delta_0$  and is equal to

$$6 + \frac{12}{q+1}$$
.

When  $g \ge 24$  this is less than 6.5, hence the canonical class of  $\overline{\mathrm{M}}_g$  is big provided g+1 is not prime. The Brill-Noether divisors also take care of the cases g=24,26. When g is even and greater than or equal to 28, the Petri divisor works to give the conclusion.

We will spend the next section calculating the class of the Brill-Noether divisor. The class of the Petri divisor is harder to compute. You can find the computation in [EH5].

**Remark 4.9.** Recently G. Farkas has announced that  $\overline{\mathrm{M}}_{22}$  and  $\overline{\mathrm{M}}_{23}$  are also of general type. The strategy of his proof is the same. He constructs more elaborate effective divisors.

- 5. The computation of the classes of Brill-Noether Divisors
- 5.1. The Brill-Noether Theorem. In this subsection we will discuss some of the basics of Brill-Noether theory and the theory of limit linear series. Eisenbud and Harris have developed this theory in order to prove theorems like the Brill-Noether or Gieseker-Petri theorems. We will describe their approach to some of these problems. The best places to start learning about the subject are Chapter 5 of [HM1] and [ACGH]. Other good references [GH], [EH2], [EH1], [EH3], [EH4], [KL2], [KL1] among others.

Brill-Noether theory asks the following fundamental question:

**Question 5.1.** When can a curve of genus g be represented in  $\mathbb{P}^r$  as a non-degenerate curve of degree d?

There is an expected answer to this question. We are asking when does there exist a degree d line bundle on a curve C of genus g with at least an r+1-dimensional space of global sections? We can calculate the expected dimension of this locus in  $Pic^d(C)$  as follows. Let us twist all the line bundles in  $Pic^d(C)$  by  $\mathcal{O}_C(np)$  for a sufficiently large n (large enough to kill  $h^1$ ). Over  $Pic^d(C)$  there is a map between

the push-forward of the Poincare bundle and the trivial bundle of rank n given by evaluation at the point p. We are interested in the dimension of the locus where the evaluation map has kernel of dimension at least r+1. The expected codimension of the locus is given by (r+1)(g-d+r).

The Brill-Noether number is defined as follows

$$\rho(g, r, d) = g - (r+1)(g - d + r).$$

By the discussion in the previous paragraph on a general curve of genus g, we expect there to be a  $g_d^r$  if and only if this number is non-negative.

**Example 5.2.** One learns very early in one's algebraic geometry career that every Riemann surface admits a non-constant meromorphic function. One then ask given a genus g Riemann surface S what is the smallest degree meromorphic function on S?

- (1) If S has genus zero, then there are non-constant meromorphic functions of degree one, namely the Möbius transformations.
- (2) If S has genus one or two, then the smallest degree non-constant meromorphic function has degree 2. For instance, in the case of genus 1, the Weiestrass p function is such a function.
- (3) If S has genus 3, already the story becomes more complicated. If S is hyperelliptic, then it does admit a meromorphic function of degree 2. However, not all genus 3 curves are hyperelliptic. They do not admit meromorphic functions of degree 2. However, non-hyperelliptic curves of genus 3 can be realized as plane quartics in  $\mathbb{P}^2$ . Projecting the quartic from a point on the curve gives a meromorphic function of degree 3.
- (4) If S is a non-hyperelliptic curve of genus 4, then its canonical image is the complete intersection of a quadric and a cubic in  $\mathbb{P}^3$ . By projecting to one of the factors of  $\mathbb{P}^1 \times \mathbb{P}^1$  or the base of the Hirzebruch surface  $F_2$  (in case the quadric is singular), we obtain a map of degree 3 to  $\mathbb{P}^1$ .
- (5) If S is a non-hyperelliptic and non-trigonal curve of genus 5, then it is the complete intersection of three quadric hypersurfaces in  $\mathbb{P}^4$ . Hence such a curve does not admit a map of degree 3 to  $\mathbb{P}^1$  (Exercise: why?). Show that a such a curve does admit a map of degree 4 to  $\mathbb{P}^1$ . (Hint: The intersection of two quadrics is a Del Pezzo surface of degree 4. The map to  $\mathbb{P}^2$  blowing down 5 disjoint exceptional curves presents the curve as a five-nodal sextic. Project from a node.)
- (6) Show that a general curve of genus 6 does not admit a curve of degree 2 or 3 to  $\mathbb{P}^1$ , but does admit a map of degree 4. (Hint: The canonical image of a general curve of genus 6 lies on a degree 5 Del Pezzo surface in  $\mathbb{P}^5$ .)
- (7) One can carry the analysis a little further. In fact the following is known.

**Proposition 5.3.** Every Riemann surface of genus g admits a non-constant meromorphic function of degree  $\lfloor \frac{g+3}{2} \rfloor$ . Moreover, a general Riemann surface of genus g does not admit a non-constant meromorphic function of smaller degree.

We say that a curve C of genus g has a  $g_d^r$  if there exists a line bundle L of degree d on C with  $h^0(C, L) \geq r$ . The Brill-Noether theorem asserts that a general curve has a  $g_d^r$  if and only if the Brill-Noether number  $\rho(g, r, d)$  is non-negative. In fact, more is true. Let  $W(C)_d^r$  be the locus of line bundles in  $Pic_d(C)$  that have at least r+1-dimensional space of global sections. Then for a general C, the dimension of this locus is given by the Brill-Noether number.

**Theorem 5.4** (Brill-Noether, Kempf, Kleiman-Laksov, Griffiths-Harris, Eisenbud-Harris). Let C be a general curve of genus g. Then the dimension of  $W(C)_d^r$  is equal to the Brill-Noether number. In particular, there exists a  $g_d^r$  on C if and only if the Brill-Noether number is non-negative. Moreover, in case  $\rho(g, r, \underline{d}) = -1$ , the closure of the locus of smooth curves that possess a  $g_d^r$  is a divisor in  $\overline{M}_g$ .

**Remark 5.5.** Note that the previous proposition is a special case of the Brill-Noether theorem. If we take r=1, then we see that the Brill-Noether number is non-negative if and only if  $d \geq \lfloor \frac{g+3}{2} \rfloor$ .

A sketch of the proof. The idea of the proof goes back to Castelnuovo. Let us consider a g-nodal rational curve and try to calculate the dimension of the space of  $g_d^r$ s on such a curve. If the dimension is correct, then we have a chance of deducing the theorem for general curves by specializing them to a g-nodal rational curve. A map of degree d to  $\mathbb{P}^r$  (where r < d) on a g-nodal rational curve amounts to the same thing as the projection of a rational normal curve of degree d from a  $\mathbb{P}^{d-r-1}$  that meets g specified secant lines. In other words we are asking for the dimension of the intersection of g Schubert cycles  $\Sigma_r$  in  $\mathbb{G}(d-r-1,d)$ . Had these cycles been general we could conclude that the dimension of the space of  $g_d^r$  on a g-nodal rational curve is

$$(d-r)(r+1) - qr.$$

I leave it to you to verify that this is equal to the Brill-Noether number.

There are a few problems with the previous idea. First, the Jacobian of a g-nodal curve is not compact, so the limits of  $g_d^r$ s on a general curve need not be  $g_d^r$ s. Second, more serious problem, is that the Schubert cycles  $\Sigma_r$  are not general Schubert cycles, hence their intersection need not be dimension theoretically transverse. We will completely circumvent the first problem and deal with the second in the meantime by specializing to g-cuspidal curves. In other words, we will make the Schubert cycles  $\Sigma_r$  be defined with respect to tangent lines to the rational normal curve. Note that the semi-stable reduction of such a curve is the normalization of the curve with g elliptic tails attached at the points that map to the cusps. In particular, the non-compactness issue disappears.

**Theorem 5.6** (Eisenbud-Harris). Let  $p_1, \ldots, p_m$  be distinct points on a rational normal curve of degree d in  $\mathbb{P}^d$ . Let  $F_1, \ldots, F_m$  be the osculating flags to the rational normal curve defined at these points, respectively. Then Schubert varieties defined with respect to the flags  $F_i$  in the Grassmannian, if non-empty, intersect in the expected dimension.

The proof of this theorem is based on a Plücker formula. Let  $V \subset H^0(C, L)$  be a linear series of vector-space dimension r+1 on a genus g curve C. Let

$$0 \le \alpha_0(p) \le \alpha_1(p) \le \dots \le \alpha_r(p)$$

be the ramification sequence of V at a point p of C. Let  $R_i(p)$  be the orders of vanishing of sections in V at p. Recall that the ramification sequence index  $\alpha_i(p)$  is defined to be  $\alpha_i(p) = R_i(p) - i$ . The sum of all the ramification indeces over all points of the curve C may be expressed only in terms of the dimension of V, degree of L and the genus of C as the following proposition indicates.

**Proposition 5.7.** Let V be a linear series of degree d and vector-space dimension r+1 on a genus g curve. Then the sum of the ramification indices satisfy the following equality

$$\sum_{j,p} \alpha_j(p) = (r+1)d + \frac{r(r+1)}{2}(2g-2).$$

*Proof of Proposition.* The Taylor expansions of order r of the sections in V gives a map to the bundle of r-jets of sections of L

$$\alpha: V \otimes \mathcal{O}_C \to P^r(L).$$

Taking the r + 1st exterior power we get a map

$$\mathcal{O}_C \to \bigwedge^{r+1} P^r(L).$$

The formula claimed in the proposition arises from calculating the number of zeroes of this map in two different ways. First of all using the exact sequence that relates principal parts bundles

$$0 \to L \times K_C^m \to P^m(L) \to P^{m-1}(L) \to 0$$

we see inductively that

$$\bigwedge^{r+1} P^r(L) \cong L^{r+1} \otimes K_C^{\frac{r(r+1)}{2}}.$$

Therefore, the number of zeros is equal to

$$(r+1)d + \frac{r(r+1)}{2}(2g-2),$$

which is the right hand side of the claimed formula.

On the other hand, we can calculate the number of zeros in local coordinates. At each point  $p \in C$  we choose the sections of V that vanish to order  $i + \alpha_i(p)$  in terms of a local coordinate t. The order of zeros of the map is the smalles order of vanishing of any linear combination of the  $(r + 1) \times (r + 1)$  minors of the matrix

$$\begin{pmatrix} t^{\alpha_0(p)} & t^{1+\alpha_1(p)} & t^{2+\alpha_2(p)} & \dots \\ \alpha_0(p)t^{\alpha_0(p)-1} & (1+\alpha_1(p))t^{\alpha_1(p)} & \dots & \dots \\ \dots & \dots & \dots & \dots \end{pmatrix}.$$

This order is precisely the left hand side of the formula in the proposition.  $\Box$ 

In particular, when the genus is equal to zero we see that the total ramification is equal to (r+1)(d-r). Since the total ramification may not exceed this number it is now easy to conclude the Eisenbud-Harris Theorem.

**Exercise 5.8.** Check that for a map of a rational curve to have a ramification sequence  $\alpha_0, \ldots, \alpha_{r+1}$  at p is equivalent to asking the center of the projection to satisfy the Schubert condition of codimension equal to the sum of the ramification indeces with respect to the osculating flag to C at p. Express the class of the Schubert variety in terms of the ramification sequence.

Another central theorem of curve theory that is amenable to similar (but more difficult) techniques is the Gieseker-Petri Theorem.

**Theorem 5.9** (Gieseker-Petri, Eisenbud-Harris, Lazarsfeld). Let C be a general curve. Let L be any line bundle on C. Then the multiplication map

$$H^0(C,L) \otimes H^0(C,K \otimes L^{-1}) \to H^0(C,K)$$

is injective.

Suppose that there exists a  $g_d^r$  with negative Brill-Noether number. Using Riemann-Roch for curves, we see that

$$h^{0}(K - g_{d}^{r}) = h^{0}(g_{d}^{r}) - d + g - 1 = r + 1 - d + g - 1 = r - d + g.$$

Since the Brill-Noether number is negative, we must have  $(r+1)(r-d+g) \geq g+1$ . Hence the domain of the map  $H^0(C,L) \otimes H^0(C,K \otimes L^{-1})$ , where L is the line bundle giving the  $g^r_d$  has dimension at least g+1. Consequently, the Petri map cannot be injective. We conclude that for a Gieseker-Petri general curve there does not exist a  $g^r_d$  if the Brill-Noether number is negative.

**Remark 5.10.** In general, the failure of the injectivity cannot be explained by dimension theoretic reasons alone. Consider a genus 4 curve with a canonical form with a single zero (necessarily of multiplicity 6). The Weierstrass sequence for such a point is given as follows:

$$h^0(3p) = 2$$
,  $h^0(5p) = 3$ ,  $h^0(6p) = 4$ .

Although the target and the domain vector spaces in  $h^0(3p) \otimes h^0(3p) \to h^0(6p)$  have the same dimension, the multiplication map is not an isomorphism since it is not possible to get a section vanishing to order 5 by multiplying sections vanishing to order 3.

Unfortunately, most easy to manipulate curves are not general in the sense of Gieseker-Petri. For example, a k-gonal curve, that is a curve admitting a non-constant holomorphic map of degree k to  $\mathbb{P}^1$ , if k is small (k < (g+3)/2 compared to g) will not satisfy the Gieseker-Petri Theorem as observed by the above calculation.

5.2. Limit linear series. In this subsection we will briefly sketch the theory of limit linear series for curves of compact type developed by Eisenbud and Harris in order to study Brill-Noether theory. Since Joe has written very good accounts of the theory our treatment will be brief. One of the main uses of the theory is to describe the closure of Brill-Noether conditions on singular curves. For more details see [HM1] Chapter 5, [EH1], [EH3], [EH4], [EH2].

**Definition 5.11.** A curve is of *compact type* if its dual graph is a tree.

**Proposition 5.12.** The following conditions on an at worst nodal curve C of genus are equivalent

- (1) C is of compact type.
- (2) The sum of the geometric genera of the components of C equals g.
- (3) The Jacobian of C is compact.

*Proof.* If C is of compact type, then its dual graph is a tree. In particular, every irreducible component of C is smooth and any two components meet at most in one point. We can prove the equivalence of 1 and 2 by induction. If the dual graph of C has only one vertex, then the equivalence is obvious. Suppose the result is true for C whose dual graphs have at most k vertices. Take a leaf of the dual graph of C with k+1 vertices. If we remove the leaf, the remaining curve is a curve of compact type whose dual graph has k vertices. Hence the sum of the geometric genera of its components equals its genus. Since the component we removed is attached at one point using the exact sequence

$$0 \to \mathcal{O}_C \to \mathcal{O}_{C_1} \oplus \mathcal{O}_{C_2} \to \mathcal{O}_{C_1 \cap C_2} \to 0$$

we see that

$$h^1(C, \mathcal{O}_C) = h^1(C_1, \mathcal{O}_{C_1}) + h^1(C_2, \mathcal{O}_{C_2}).$$

This completes the proof that 1 implies 2.

To see that 2 implies 1, we observe that by the same exact sequence that the genus of a curves is at least the sum of the genus of its components. If there is a loop, then by the exact sequence the genus of the curve formed by a loop is one more than the sum of its components.

To see the equivalence of these conditions with the condition that the Jacobian is compact, we need to study the group line bundles on a singular curve. Let  $\nu: \tilde{C} \to C$  be the normalization of the curve C.

We have an exact sequence

$$0 \to \mathbb{C}^* \to (\mathbb{C}^*)^r \to \Gamma(C) \to \operatorname{Pic}(C) \to \operatorname{Pic}(\tilde{C}) \to 0$$

where r is the number of irreducible components of C. Consequently, J(C) is compact if and only if the number of points lying over the singular points of the curve is two less than twice the number of irreducible components. But the latter can only happen if and only if the dual graph of the curve is a tree. This proves the equivalence of the conditions.

The importance of curves of compact type arises from the fact that one can develop a theory of limits of line bundles on such curves. In fact, one can develop such a theory on tree-like curves. A Deligne-Mumford stable curve is tree-like if after normalizing the curve at its non-separating nodes one obtains a curve of compact type. In other words, a tree-like curve differs from curves of compact type so that the irreducible components may have internal nodes.

The main difficulty. Suppose you have a one-parameter family of curves  $\mathcal{X} \to B$  such that the total space of the family is smooth, all the fibers but the central fiber are smooth curves and the central fiber is a reducible nodal curve with smooth components. Given line bundle L on  $\mathcal{X} - X_0$ , we can always extend it to the total space. Since  $\mathcal{X} - X_0$  is smooth, the line bundle L corresponds to a Cartier divisor on

 $\mathcal{X} - X_0$ . We can take the closure of this divisor in  $\mathcal{X}$  to obtain a Cartier divisor on  $\mathcal{X}$  (Note that here we use the smoothness of the total space). Since Cartier divisors correspond to line bundles, there is a corresponding line bundle  $\tilde{L}$  extending L.

Unfortunately, the extension is not unique. This is the main technical difficulty of the subject. Suppose the central fiber  $X_0 = Y \cup Z$ . If we twist  $\tilde{L}$  by  $\mathcal{O}_{\mathcal{X}}(mY)$  or  $\mathcal{O}_{\mathcal{X}}(mZ)$ , we do not change the line bundle L on  $\mathcal{X} - X_0$ ; however, we obtain a different line bundle on the total space.

**Definition 5.13** (Limit linear series). Let C be a curve of compact type. A *limit linear series* D of degree d and dimension r on C is a linear series  $|V_Y|$  of degree d and dimension r on every irreducible component of C called the *aspect* of D on Y, such that for any two components Y and Z of C meeting at a node p the aspects  $V_Y$  and  $V_Z$  satisfy

$$a_i(V_Y, p) + a_{r-i}(V_Z, p) \ge d.$$

The limit linear series is *refined* if the following inequalities are equalities for every *i*. The limit linear series is *crude* if one inequality is strict.

Using the Plücker formulae one may generalize the Brill-Noether theorem to curves of compact type. In fact, to tree-like curves as follows:

**Theorem 5.14.** Let C be a tree-like curve. Suppose the following about the irreducible components of Y:

- (1) If the genus of Y is 1, then Y meets the rest of the curve in one point.
- (2) If the genus of Y is 2, then Y meets the rest of the curve in one point which is not a Weierstrass point.
- (3) If the genus of Y is three or more, then Y meets the rest of the curve at general points

If  $p_1, \ldots, p_r$  are general points of C or arbitrary smooth points on rational components of C, then for any ramification sequence at the points  $p_i$ , the dimension of the special linear series with the given ramification sequences at the points has the expected dimension.

**Remark 5.15.** For our purposes, the important corollary of the theorem is that if we consider the pull-back of the Brill-Noether divisor to  $\overline{\mathrm{M}}_{0,n}$  and  $\overline{\mathrm{M}}_{2,1}$  via the map that attaches g fixed elliptic curves at the marked points and the map that attaches a fixed genus g-2 curve, respectively, the pull-back to  $\overline{\mathrm{M}}_{0,n}$  is zero while the pull-back to  $\overline{\mathrm{M}}_{2,1}$  is supported on the Weierstrass divisor.

5.3. Calculating the classes of the Brill-Noether divisors. In this subsection we complete our discussion of the proof of Theorem 4.1 by calculating the class of the Brill-Noether divisors. For the rest of this section assume that the Brill-Noether divisor is expressed as follows in terms of the standard generators

$$a\lambda - b_0\delta_{irr} - \sum_{i=1}^{\lfloor g/2 \rfloor} b_i\delta_i.$$

We calculate the class by pulling-back the Brill-Noether divisor to  $\overline{\mathrm{M}}_{2,1}$  and  $\overline{\mathrm{M}}_{0,g}$ . Using the first pull-back we obtain the relations

$$a = 5b_1 - 2b_2$$
 and  $b_{irr} = \frac{b_1}{2} - \frac{b_2}{6}$ .

Using the second pull-back, we obtain for i > 1 the relations

$$b_i = \frac{i(g-i)}{g-1}b_1.$$

Solving for all the coefficients in terms of  $b_1$ , we obtain the class of the Brill-Noether divisors upto a positive constant. (One can determine the constant, but we do not need this for proving Theorem 4.1.)

**Theorem 5.16.** If g + 1 = (r + 1)(g - d + r), then the class of the Brill-Noether divisor on  $\overline{M}_g$  is given by

$$c\left((g+3)\lambda - \frac{g+1}{6}\delta_{irr} - \sum_{i=1}^{\lfloor g/2\rfloor} i(g-i)\delta_i\right)$$

where c is a positive rational constant.

To conclude the proof we need to obtain the claimed relations between the coefficients. First, consider the map

$$at_{g-2}: \overline{\mathrm{M}}_{2,1} \to \overline{\mathrm{M}}_{g}$$

obtained by attaching a fixed genus g-2 curve with a marked point to curves of genus 2 with a marked point along their marked points. The theory of limit linear series shows that the pull-back of the Brill-Noether divisor is a multiple of the divisor W on  $\overline{\mathrm{M}}_{2,1}$  obtained by taking the closure of the locus in  $\mathrm{M}_{2,1}$  where the marked point is a Weierstrass point. The first set of relations are obtained by comparing the class of W and the pull-backs of the standard generators by  $at_{q-2}$ 

Claim 5.17. The class of the Weierstrass divisor W is given by

$$W = 3\omega - \lambda - \delta_1$$
.

where  $\omega$  is the class of the relative dualizing sheaf on  $M_{2,1}$ .

The pull-back of  $\lambda$  by  $at_{g-2}$  is  $\lambda$  on  $\overline{\mathrm{M}}_{2,1}$ . Similarly the pull-backs of  $\delta_{irr}$  and  $\delta_1$  by  $at_{g-2}$  are  $\delta_{irr}$  and  $\delta_1$  on  $\overline{\mathrm{M}}_{2,1}$ , respectively. By adjunction the pull-back of  $\delta_2$  is  $-\omega$ . It follows that by pulling back the Brill-Noether divisor and using the claim we obtain the relation

$$a\lambda - b_{irr}\delta_{irr} - b_1\delta_1 - b_2\omega = c(3\omega - \lambda - \delta_1).$$

We thus see that  $b_2 = 3c$ . Next we use the relation

$$10\lambda = \delta_{irr} + 2\delta_1$$

to solve for the other coefficients to obtain the first set of relations.

To calculate the class of the Weierstrass divisor W, we note that a Weierstrass point is a ramification point of the canonical linear series. Using this one can exhibit W as the degenracy locus of a map between vector bundles.

**Exercise 5.18.** Carry this out and complete the calculation of the class of W. (Hint: See page 338-339 in [HM1]).

Next, consider the map

$$att: \overline{\mathrm{M}}_{0,q} \to \overline{\mathrm{M}}_{q}$$

obtained by attaching a fixed one pointed elliptic curve to the marked points. To obtain the required relations among the coefficients of the boundary we consider the pull-back of the Brill-Noether divisors by  $\pi$ . Since the Brill-Noether divisor is disjoint from the imape of att, the pull-back of the divisor to  $\overline{\mathrm{M}}_{0,q}$  is zero.

We thus obtain the following relation among the coefficients:

$$a \ att^*\lambda - b_0 \ att^*\delta_0 - \sum_{i=1}^{\lfloor g/2\rfloor} b_i \ att^*\delta_i = 0.$$

We have to calculate the pull-backs of the standard divisors by att. Clearly,  $\lambda$  and  $\delta_{irr}$  pull-back to zero. The pull-backs of the divisors  $\delta_i$  are the classes  $\delta_i^0$  on  $\overline{\mathrm{M}}_{0,g}$  (where we place a 0 to remind ourselves that these are the divisors on  $\overline{\mathrm{M}}_{0,g}$ ) provided i > 1. The image of att is contained in  $\Delta_1 \subset \overline{\mathrm{M}}_g$ , so the pull-back of  $\delta_1$  is the trickiest. To calculate its class, we take a one-parameter family of curves

$$\pi:C\to B$$

in  $\overline{\mathrm{M}}_{0,g}$ . We may assume that every member of the family has at most two components and that the total space of the family is smooth. Contracting the components with fewer sections (or either of the components when equal numbers of sections pass through both components), we obtain a  $\mathbb{P}^1$  bundle with g sections

$$\tilde{\pi}: \tilde{C} \to B.$$

Since the classes of any two sections differ by a multiple of the fiber class, the difference of two section classes has self-intersection zero.

The pull-back of  $\delta_1$  by att is the push-forward to the sum of the squares of the sections  $\sigma_i$  in the original family to the base. The sections  $\gamma_i$  in the projective bundle and in the original family are related by

$$\tilde{\pi}_*(\sum \gamma_i^2) = \pi_*(\sum \sigma_i^2) + \sum_{i=2}^{\lfloor g/2 \rfloor} i \ \delta_i^0.$$

Using that

$$\gamma_i^2 + \gamma_j^2 = 2\gamma_i \cdot \gamma_j$$

we obtain the relation

$$\tilde{\pi}_*(\sum \gamma_i^2) = \sum_{i=2}^{\lfloor g/2 \rfloor} \frac{i(i-1)}{g-1} \delta_i^0.$$

Combining these relations we obtain that

$$att^*\delta_1 = \sum_{i=2}^{\lfloor g/2\rfloor} -\frac{i(g-i)}{g-1}\delta_i^0.$$

The class of the Brill-Noether divisors (up to a constant multiple) follow from these calculations.

### 6. The ample and effective cones of the moduli space of curves

The proof that  $\overline{\mathrm{M}}_g$  is of general type when g > 24 required us to know a two-dimensional slice of the ample cone of  $\overline{\mathrm{M}}_g$ . Combining this with our knowledge of some special effective divisors we could conclude the proof. One may ask the more detailed questions:

**Question 6.1.** In terms of the generators of the picard group  $\lambda, \delta_1, \ldots, \delta_{\lfloor g/2 \rfloor}$  what is the ample cone of  $\overline{\mathrm{M}}_g$ ? What is the effective cone of  $\overline{\mathrm{M}}_g$ ?

Almost nothing is known about the effective cone of  $\overline{\mathrm{M}}_g$ . Of course, everytime one writes down an effective divisor, one generates part of the effective cone. In recent years G. Farkas has spent a tremendous amount of effort to construct effective divisors on  $\overline{\mathrm{M}}_g$ . Despite these efforts our understanding of the effective cone of the effective cone of  $\overline{\mathrm{M}}_g$  has progressed little beyond examples of effective divisors. On the other hand, there is a beautiful conjecture giving a complete description of the ample cone of  $\overline{\mathrm{M}}_{g,n}$ .

**Remark 6.2.** There is however one exception to our ignorance about the effective cone. The effective cone of  $\overline{\mathrm{M}}_{0,n}$  is difficult to describe. However, if we quotient  $\overline{\mathrm{M}}_{0,n}$  by the action of the symmetric group on n letters it becomes very easy to see that the effective cone is equal to the cone spanned by the boundary divisors.

Exercise 6.3. Show that the effective cone of  $\overline{\mathrm{M}}_{0,n}/\mathfrak{S}_n$  is the span of the boundary divisors as follows: Show that if D is effective, then the coefficient of  $\Delta_2$  has to be non-negative (Hint: Consider a fixed  $\mathbb{P}^1$  with n-marked points. Let the last marked point vary keeping the rest fixed. Show that such curves cover an open subset of  $\overline{\mathrm{M}}_{0,n}/\mathfrak{S}_n$  and only intersect  $\Delta_2$  among the boundary divisors.) Show that the coefficient of  $\Delta_t$  has to be non-negative by induction on t. (Hint: Assume that the effective divisor does not contain any of the boundary divisors as a fixed component. Fix a reducible curve with t-1 points on one component and n-t+1 points on the other component. Attach the first component at a fixed point of the first curve to a variable point on the second curve. Considering this curve complete the induction.)

 $\overline{M}_{g,n}$  has a stratification according to topological type. Given a curve C we can associate the dual graph to C. For every irreducible component we associate a vertex. For every node connecting two irreducible components we associate an edge between the two vertices. For every self node we associate a loop based at the vertex corresponding to the irreducible component. Finally, we associate a tail emanating from the appropriate vertex for each marked point. We label the vertices by the geometric genus of the corresponding curve.

We obtain a stratification of  $\overline{M}_{g,n}$  by considering the loci of curves with a fixed dual graph. The codimension of a stratum is equal to the number of nodes that the curve represented by that graph has. The zero dimensional strata consist of curves with 3g-3+n nodes. We proved that every component of such a curve is a  $\mathbb{P}^1$  whose normalization contains exactly three distinguished points. The one dimensional strata consist of curves with 3g-4+n nodes. Every component but one of a curve with 3g-4+n nodes is a  $\mathbb{P}^1$  whose normalization has three distinguished points. The remaining component is either a  $\mathbb{P}^1$  whose normalization

has four distinguished points or a genus one curve whose normalization has one distinguished point. We can view the one-dimensional loci as the images of  $\overline{\mathrm{M}}_{0,4}$  and  $\overline{\mathrm{M}}_{1,1}$ . These curves are often referred to as F-curves.

The F-conjecture describes the ample cone of  $\overline{M}_{q,n}$  in terms of the F-curves.

**Conjecture 6.4** (The F-conjecture). A divisor on  $\overline{M}_{g,n}$  is ample if and only if it intersects positively with every F-curve.

Of course, by Kleiman's criterion every ample divisor intersects every curve positively. The content of the F-conjecture is to say that checking for the F-curves suffices. Alternatively the conjecture may be formulated as saying that the Mori cone of curves on  $\overline{M}_{q,n}$  is generated by the F-curves.

Observe that from this statement one can obtain very explicit inequalities describing the ample cone of  $\overline{M}_{g,n}$ . For simplicity we will give the description when n=0.

**Exercise 6.5.** Determine inequalities describing the ample cone of  $\overline{M}_{g,n}$  in terms of the generators of the Picard group when  $n \geq 1$ .

We begin by enumerating the F-curves. As already observed every component but one of a curve parameterized by a general point on an F-curve corresponds to a  $\mathbb{P}^1$  with 3 distinguished points. If the remaining component is a genus 1 curve with one marked point, then when we separate the curve at this marked point we obtain a curve of genus g-1 consisting of  $\mathbb{P}^1$ s with three distinguised points each and the genus one curve with one marked point. This curve is obtained by attaching a fixed curve with one marked point to  $\overline{M}_{1,1}$ . From this it follows that  $C \cdot \delta_i = 0$  for  $i \geq 1$ . To calculate  $C \cdot \delta_0 = 1/2$ , we observe that Finally,  $C \cdot \lambda = 1$ .

If the remaining component is a genus 0 curve with 4 marked points, then the normalization restricted to that component might be injective. In this case if we split the curve at the distinguished points, we obtain four pieces of genus  $g_1, g_2, g_3$  and  $g - g_1 - g_2 - g_3$ .

**Exercise 6.6.** Work out the intersections of the F-curves with the boundary components. Use these intersections to give inequalities that describe an upper bound on the ample cone.

**Problem 6.7.** Show that every divisor in the cone dual to the F-curves is ample (or give a counterexample).

Currently the F-conjecture is open. A. Gibney has verified the conjecture for  $\overline{\mathrm{M}}_g$  for many small genera. There is also a general result due to Gibney, Keel and Morrison [GKM] that reduces the general conjecture to the case of genus zero:

**Theorem 6.8.** The F conjecture holds for  $\overline{M}_{g,n}$  if it holds for  $\overline{M}_{0,m}$  for  $m \leq g+n$ .

## References

- [ACGH] E. Arbarello, M. Cornalba, P. A. Griffiths, and J. Harris. Geometry of algebraic curves. Vol. I, volume 267 of Grundlehren der Mathematischen Wissenschaften [Fundamental Principles of Mathematical Sciences]. Springer-Verlag, New York, 1985.
- [CH] M. Cornalba and J. Harris. Divisor classes associated to families of stable varieties, with applications to the moduli space of curves. Ann. Sci. École Norm. Sup. (4) 21(1988), 455–475.

- [EH1] D. Eisenbud and J. Harris. Divisors on general curves and cuspidal rational curves. Invent. Math. 74(1983), 371–418.
- [EH2] D. Eisenbud and J. Harris. On the Brill-Noether theorem. In Algebraic geometry open problems (Ravello, 1982), volume 997 of Lecture Notes in Math., pages 131–137. Springer, Berlin, 1983.
- [EH3] D. Eisenbud and J. Harris. A simpler proof of the Gieseker-Petri theorem on special divisors. *Invent. Math.* 74(1983), 269–280.
- [EH4] D. Eisenbud and J. Harris. Limit linear series: basic theory. Invent. Math. 85(1986), 337–371.
- [EH5] D. Eisenbud and J. Harris. The Kodaira dimension of the moduli space of curves of genus  $\geq 23$ . Invent. Math. **90**(1987), 359–387.
- [GKM] A. Gibney, S. Keel, and I. Morrison. Towards the ample cone of  $\overline{M}_{g,n}$ . J. Amer. Math. Soc. 15(2002), 273–294.
- [GH] P. Griffiths and J. Harris. On the variety of special linear systems on a general algebraic curve. Duke Math. J. 47(1980), 233–272.
- [H] J. Harris. On the Kodaira dimension of the moduli space of curves. II. The even-genus case. *Invent. Math.* 75(1984), 437–466.
- [HM1] J. Harris and I. Morrison. Moduli of curves. Springer-Verlag, 1998.
- [HM2] J. Harris and D. Mumford. On the Kodaira dimension of the moduli space of curves. Invent. Math. 67(1982), 23–88. With an appendix by William Fulton.
- [KL1] S. L. Kleiman and D. Laksov. Another proof of the existence of special divisors. Acta Math. 132(1974), 163–176.
- [KL2] S. L. Kleiman and Dan. Laksov. On the existence of special divisors. Amer. J. Math. 94(1972), 431–436.
- [L] R. Lazarsfeld. Positivity in algebraic geometry. I, volume 48 of Ergebnisse der Mathematik und ihrer Grenzgebiete. 3. Folge. A Series of Modern Surveys in Mathematics. Springer-Verlag, Berlin, 2004. Classical setting: line bundles and linear series.

---

## FORMULARIUM FOR DIVISOR CLASSES

## Exercise 0.1. Let

$$\pi_{n+1}:\overline{\mathrm{M}}_{g,n+1}\to\overline{\mathrm{M}}_{g,n}$$

be the morphism that forgets the n+1st marked point. Prove the following formulae:

- (1)  $\pi_{n+1}^*(\kappa) = \kappa \psi_{n+1}$ .
- (2)  $\pi_{n+1}^*(\psi_i) = \psi_i \delta_{0,\{i,n+1\}}$  for  $i \le n$ .
- (3)  $\pi_{n+1}^*(\delta_{irr}) = \delta_{irr}$ .
- (4)  $\pi_{n+1}^*(\delta_{h,S}) = \delta_{h,S} + \delta_{h,S \cup \{n+1\}}.$

## Exercise 0.2. Let

$$\xi: \overline{\mathbf{M}}_{g-1,n\cup\{x,y\}} \to \overline{\mathbf{M}}_{g,n}$$

be the morphism that glues the two points x, y. Show that  $\xi$  pulls back the tautological classes as follows:

- (1)  $\xi^*(\kappa) = \kappa$ .
- (2)  $\xi^*(\phi_i) = \phi_i$  for  $i \leq n$ .

(3) 
$$\xi^*(\delta_{irr}) = \delta_{irr} - \psi_x - \psi_y + \sum_{x \in S, y \notin S} \delta_{g,S}$$

(4) 
$$\xi^*(\delta_{h,S}) = \begin{cases} \delta_{h,S} & \text{if } g = 2h, \quad n = 0\\ \delta_{h,S} + \delta_{h-1,S \cup \{x,y\}} & \text{otherwise} \end{cases}$$

## Exercise 0.3. Let

$$at_{h,S}: \overline{\mathbf{M}}_{g-h,n-S\cup\{x\}} \to \overline{\mathbf{M}}_{g,n}$$

be the morphism obtained by attaching a fixed curve of genus h and marking  $S \cup \{y\}$  to curves in  $\overline{\mathrm{M}}_{g-h,n-S \cup \{x\}}$  by identifying x and y. Show that the following relations hold:

- (1)  $at_{h.S}^*(\kappa) = \kappa$ .
- (2)  $at_{h,S}^*(\phi_i) = \begin{cases} \phi_i & \text{if } i \in S \\ 0 & \text{otherwise} \end{cases}$
- (3)  $at_{h,S}^*(\delta_{irr}) = \delta_{irr}$ .
- (4) If  $S = \{1, ..., n\}$ , then

$$at_{h,S}^{*}(\delta_{k,T}) = \begin{cases} \delta_{2h-g,S\cup\{x\}} - \psi_{x} & \text{if } k = h, \#T = n, \text{ or } k = g-h, \#T = 0\\ \delta_{k,T} + \delta_{k+h-g,T\cup\{x\}} & \text{otherwise} \end{cases}$$

(5) If 
$$S \neq \{1, ..., n\}$$
, then

$$at_{h,S}^*(\delta_{k,T}) = \begin{cases} -\psi_x & \text{if } (k,T) = (h,S) \text{ or } (k,T) = (g-h,S^c) \\ \delta_{k,T} & \text{if } T \subset S \text{ and } (k,T) \neq (h,S) \\ \delta_{k+h-g,(T \setminus S^c) \cup \{x\}} & \text{if } S^c \subset T \text{ and } (k,T) \neq (g-h,S^c) \\ 0 & \text{otherwise} \end{cases}$$

**Exercise 0.4.** Using the previous exercises and our calculations in class determine the divisor class relations between  $\kappa$ ,  $\psi$  and  $\delta$  classes in  $\overline{\mathrm{M}}_{1,n}$  and  $\overline{\mathrm{M}}_{2,n}$ .
