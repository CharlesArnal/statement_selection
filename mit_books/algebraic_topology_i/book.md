# Lectures on Algebraic Topology

Fall 2016

#### **Preface**

Over the 2016–2017 academic year, I ran the graduate algebraic topology sequence at MIT. The first semester traditionally deals with singular homology and cohomology and Poicaré duality; the second builds up basic homotopy theory, spectral sequences, and characteristic classes.

My goal was to give a pretty standard classical approach to these subjects. In the first semester, I had various more specific objectives as well. I wanted to introduce students to the basic language of category theory and simplicial sets, so useful throughout mathematics and finding their first real manifestations in algebraic topology. I wanted to stress the methods of homological algebra, for similar reasons. And I especially wanted to give an honest account of the machinery – relative cap product and Čech cohomology – needed in the proof of Poincaré duality. The present document contains a bit more detail on these last matters than was presented in the course itself.

On the other hand I barely touched on some important subjects. I did not talk about simplicial complexes at all, nor about the Lefschetz fixed point theorem. I gave only a brief summary of the theory of covering spaces and the fundamental group, in preparation for a proper understanding of orientations. I avoided some point set topology by working with only compact subspaces rather than general closed subspaces in the development of Poincaré duality.

I was lucky enough to have in the audience a student, Sanath Devalapurkar, who spontaneously decided to live TeX the entire course. This resulted in a remarkably accurate record of what happened in the classroom – right down to random alarms ringing and embarassing jokes and mistakes on the blackboard. Sanath's TeX forms the basis of these notes, and I am grateful to him for making them available. The attractive drawings were provided by another student, Xianglong Ni, who also carefully proofread the manuscript.

In the course of editing these notes, beyond correcting various errors (while hopefully not introducting too many new ones), I completed a few arguments not done in detail in the actual lectures and rearranged some of the material to take full advantage of hindsight. I tried not to do too much damage to the light and spontaneous character of Sanath's original notes. I hope you find these notes useful, and I welcome comments or corrections!

# Contents

| $\mathbf{C}_{\mathbf{C}}$ | onter | nts                                                      | iv             |  |  |  |  |  |  |  |
|---------------------------|-------|----------------------------------------------------------|----------------|--|--|--|--|--|--|--|
| 1                         | Sing  | Singular homology                                        |                |  |  |  |  |  |  |  |
| _                         | 1     | Introduction: singular simplices and chains              | 1<br>1         |  |  |  |  |  |  |  |
|                           | 2     | Homology                                                 | $\overline{4}$ |  |  |  |  |  |  |  |
|                           | 3     | Categories, functors, natural transformations            | 6              |  |  |  |  |  |  |  |
|                           | 4     | Categorical language                                     | 8              |  |  |  |  |  |  |  |
|                           | 5     | Homotopy, star-shaped regions                            | 10             |  |  |  |  |  |  |  |
|                           | 6     | Homotopy invariance of homology                          | 13             |  |  |  |  |  |  |  |
|                           | 7     | Homology cross product                                   | 15             |  |  |  |  |  |  |  |
|                           | 8     | Relative homology                                        | 17             |  |  |  |  |  |  |  |
|                           | 9     | The homology long exact sequence                         | 19             |  |  |  |  |  |  |  |
|                           | 10    | Excision and applications                                | 22             |  |  |  |  |  |  |  |
|                           | 11    | The Eilenberg Steenrod axioms and the locality principle | 25             |  |  |  |  |  |  |  |
|                           | 12    | Subdivision                                              | 28             |  |  |  |  |  |  |  |
|                           | 13    | Proof of the Locality Principle                          | 30             |  |  |  |  |  |  |  |
| 2                         | Con   | Computational methods                                    |                |  |  |  |  |  |  |  |
|                           | 14    | CW-complexes                                             | 35             |  |  |  |  |  |  |  |
|                           | 15    | CW-complexes II                                          | 38             |  |  |  |  |  |  |  |
|                           | 16    | Homology of CW-complexes                                 | 40             |  |  |  |  |  |  |  |
|                           | 17    | Real projective space                                    | 42             |  |  |  |  |  |  |  |
|                           | 18    | Euler characteristic and homology approximation          | 44             |  |  |  |  |  |  |  |
|                           | 19    | Coefficients                                             | 47             |  |  |  |  |  |  |  |
|                           | 20    | Tensor product                                           | 48             |  |  |  |  |  |  |  |
|                           | 21    | Tensor and Tor                                           | 53             |  |  |  |  |  |  |  |
|                           | 22    | The fundamental theorem of homological algebra           | 55             |  |  |  |  |  |  |  |
|                           | 23    | Hom and Lim                                              | 58             |  |  |  |  |  |  |  |
|                           | 24    | Universal coefficient theorem                            | 61             |  |  |  |  |  |  |  |
|                           | 25    | Künneth and Eilenberg-Zilber                             | 63             |  |  |  |  |  |  |  |
|                           |       |                                                          |                |  |  |  |  |  |  |  |
| 3                         | Coh   | Cohomology and duality 69                                |                |  |  |  |  |  |  |  |
|                           | 26    | Coproducts, cohomology                                   | 69             |  |  |  |  |  |  |  |
|                           | 27    | Ext and UCT                                              | 73             |  |  |  |  |  |  |  |
|                           | 28    | Products in cohomology                                   | 76             |  |  |  |  |  |  |  |
|                           | 29    | Cup product, continued                                   | 77             |  |  |  |  |  |  |  |
|                           | 30    | Surfaces and nondegenerate symmetric bilinear forms      | 80             |  |  |  |  |  |  |  |
|                           | 31    | Local coefficients and orientations                      | 83             |  |  |  |  |  |  |  |

| 32           | Proof of the orientation theorem       | 88  |  |  |  |  |
|--------------|----------------------------------------|-----|--|--|--|--|
| 33           | A plethora of products                 | 91  |  |  |  |  |
| 34           | Cap product and "Cech" cohomology      | 93  |  |  |  |  |
| 35           | Cech cohomology as a cohomology theory | 97  |  |  |  |  |
| 36           | The fully relative cap product         | 100 |  |  |  |  |
| 37           | Poincaré duality                       | 102 |  |  |  |  |
| 38           | Applications                           | 105 |  |  |  |  |
|              |                                        |     |  |  |  |  |
| Bibliography |                                        |     |  |  |  |  |

# Chapter 1

# Singular homology

#### 1 Introduction: singular simplices and chains

This is a course on algebraic topology. We'll discuss the following topics.

- 1. Singular homology
- 2. CW-complexes
- 3. Basics of category theory
- 4. Homological algebra
- 5. The Künneth theorem
- 6. Cohomology
- 7. Universal coefficient theorems
- 8. Cup and cap products
- 9. Poincaré duality.

The objects of study are of course topological spaces, and the machinery we develop in this course is designed to be applicable to a general space. But we are really mainly interested in geometrically important spaces. Here are some examples.

- The most basic example is n-dimensional Euclidean space,  $\mathbb{R}^n$ .
- The *n*-sphere  $S^n = \{x \in \mathbf{R}^{n+1} : |x| = 1\}$ , topologized as a subspace of  $\mathbf{R}^{n+1}$ .
- Identifying antipodal points in  $S^n$  gives real projective space  $\mathbf{RP}^n = S^n/(x \sim -x)$ , i.e. the space of lines through the origin in  $\mathbf{R}^{n+1}$ .
- Call an ordered collection of k orthonormal vectors an orthonormal k-frame. The space of orthonormal k-frames in  $\mathbf{R}^n$  forms the Stiefel manifold  $V_k(\mathbf{R}^n)$ , topologized as a subspace of  $(S^{n-1})^k$ .
- The Grassmannian  $\operatorname{Gr}_k(\mathbf{R}^n)$  is the space of k-dimensional linear subspaces of  $\mathbf{R}^n$ . Forming the span gives us a surjection  $V_k(\mathbf{R}^n) \to \operatorname{Gr}_k(\mathbf{R}^n)$ , and the Grassmannian is given the quotient topology. For example,  $\operatorname{Gr}_1(\mathbf{R}^n) = \mathbf{R}\mathbf{P}^{n-1}$ .

All these examples are manifolds; that is, they are Hausdorff spaces locally homeomorphic to Euclidean space. Aside from  $\mathbb{R}^n$  itself, the preceding examples are also compact. Such spaces exhibit a hidden symmetry, which is the culmination of 18.905: Poincaré duality.

As the name suggests, the central aim of algebraic topology is the usage of algebraic tools to study topological spaces. A common technique is to probe topological spaces via maps to them from simpler spaces. In different ways, this approach gives rise to singular homology and homotopy groups. We now detail the former; the latter takes the stage in 18.906.

**Definition 1.1.** For  $n \geq 0$ , the standard n-simplex  $\Delta^n$  is the convex hull of the standard basis  $\{e_0, \ldots, e_n\}$  in  $\mathbf{R}^{n+1}$ :

$$\Delta^n = \left\{ \sum t_i e_i : \sum t_i = 1, t_i \ge 0 \right\} \subseteq \mathbf{R}^{n+1}.$$

The  $t_i$  are called barycentric coordinates.

The standard simplices are related by face inclusions  $d^i : \Delta^{n-1} \to \Delta^n$  for  $0 \le i \le n$ , where  $d^i$  is the affine map that sends vertices to vertices, in order, and omits the vertex  $e_i$ .

**Definition 1.2.** Let X be any topological space. A singular n-simplex in X is a continuous map  $\sigma: \Delta^n \to X$ . Denote by  $\operatorname{Sin}_n(X)$  the set of all n-simplices in X.

This seems like a rather bold construction to make, as  $Sin_n(X)$  is huge. But be patient!

For  $0 \le i \le n$ , precomposition by the face inclusion  $d^i$  produces a map  $d_i : \operatorname{Sin}_n(X) \to \operatorname{Sin}_{n-1}(X)$  sending  $\sigma \mapsto \sigma \circ d^i$ . This is the "ith face" of  $\sigma$ . This allows us to make sense of the "boundary" of a simplex, and we are particularly interested in simplices for which that boundary vanishes.

For example, if  $\sigma$  is a 1-simplex that forms a closed loop, then  $d_1\sigma = d_0\sigma$ . To express the condition that the boundary vanishes, we would like to write  $d_0\sigma - d_1\sigma = 0$  – but this difference is no longer a simplex. To accommodate such formal sums, we will enlarge  $\operatorname{Sin}_n(X)$  further by forming the free abelian group it generates.

**Definition 1.3.** The abelian group  $S_n(X)$  of singular n-chains in X is the free abelian group generated by n-simplices

$$S_n(X) = \mathbf{Z}\mathrm{Sin}_n(X).$$

So an *n*-chain is a finite linear combination of simplices,

$$\sum_{i=1}^{k} a_i \sigma_i \,, \quad a_i \in \mathbf{Z} \,, \quad \sigma_i \in \operatorname{Sin}_n(X) \,.$$

If n < 0,  $Sin_n(X)$  is declared to be empty, so  $S_n(X) = 0$ .

We can now define the boundary operator

$$d: \operatorname{Sin}_n(X) \to S_{n-1}(X),$$

by

$$d\sigma = \sum_{i=0}^{n} (-1)^{i} d_{i}\sigma.$$

This extends to a homomorphism  $d: S_n(X) \to S_{n-1}(X)$  by additivity.

We use this homomorphism to obtain something more tractable than the entirety of  $S_n(X)$ . First we restrict our attention to chains with vanishing boundary.

**Definition 1.4.** An *n*-cycle in X is an *n*-chain c with dc = 0. Notation:

$$Z_n(X) = \ker(d: S_n(X) \to S_{n-1}(X))$$
.

For example, if  $\sigma$  is a 1-simplex forming a closed loop, then  $\sigma \in Z_1(X)$  since  $d\sigma = d_0\sigma - d_1\sigma = 0$ . It turns out that there's a cheap way to produce a cycle:

**Theorem 1.5.** Any boundary is a cycle; that is,  $d^2 = 0$ .

We'll leave the verification of this important result as a homework problem. What we have found, then, is that the singular chains form a "chain complex," as in the following definition.

**Definition 1.6.** A graded abelian group is a sequence of abelian groups, indexed by the integers. A chain complex is a graded abelian group  $\{A_n\}$  together with homomorphisms  $d: A_n \to A_{n-1}$  with the property that  $d^2 = 0$ .

The group of n-dimensional boundaries is

$$B_n(X) = \operatorname{im}(d: S_{n+1}(X) \to S_n(X)),$$

and the theorem tells us that this is a subgroup of the group of cycles: the "cheap" ones. If we quotient by them, what's left is the "interesting cycles," captured in the following definition.

**Definition 1.7.** The *nth singular homology group* of X is:

$$H_n(X) = \frac{Z_n(X)}{B_n(X)} = \frac{\ker(d: S_n(X) \to S_{n-1}(X))}{\operatorname{im}(d: S_{n+1}(X) \to S_n(X))}.$$

We use the same language for any chain complex: it has cycles, boundaries, and homology groups. The homology forms a graded abelian group.

Both  $Z_n(X)$  and  $B_n(X)$  are free abelian groups because they are subgroups of the free abelian group  $S_n(X)$ , but the quotient  $H_n(X)$  isn't necessarily free. While  $Z_n(X)$  and  $B_n(X)$  are uncountably generated,  $H_n(X)$  turns out to be finitely generated for the spaces we are interested in. If T is the torus, for example, then we will see that  $H_1(T) \cong \mathbf{Z} \oplus \mathbf{Z}$ , with generators given by the 1-cycles illustrated below.

We will learn to compute the homology groups of a wide variety of spaces. The n-sphere for example has the following homology groups:

$$H_q(S^n) = \begin{cases} \mathbf{Z} & \text{if} \quad q = n > 0 \\ \mathbf{Z} & \text{if} \quad q = 0, n > 0 \\ \mathbf{Z} \oplus \mathbf{Z} & \text{if} \quad q = n = 0 \\ 0 & \text{otherwise} \,. \end{cases}$$

#### 2 Homology

In the last lecture we introduced the standard n-simplex  $\Delta^n \subseteq \mathbf{R}^{n+1}$ . Singular simplices in a space X are maps  $\sigma \colon \Delta^n \to X$  and constitute the set  $\operatorname{Sin}_n(X)$ . For example,  $\operatorname{Sin}_0(X)$  consists of points of X. We also described the face inclusions  $d^i : \Delta^{n-1} \to \Delta^n$ , and the induced "face maps"

$$d_i: \operatorname{Sin}_n(X) \to \operatorname{Sin}_{n-1}(X), 0 \le i \le n$$

given by precomposing with face inclusions:  $d_i\sigma = \sigma \circ d^i$ . For homework you established some quadratic relations satisfied by these maps. A collection of sets  $K_n, n \geq 0$ , together with maps  $d_i: K_n \to K_{n-1}$  related to each other in this way, is a *semi-simplicial set*. So we have assigned to any space X a semi-simplicial set  $S_*(X)$ .

To the semi-simplicial set  $\{\operatorname{Sin}_n(X), d_i\}$  we then applied the free abelian group functor, obtaining a semi-simplicial abelian group. Using the  $d_i$ s, we constructed a boundary map d which makes  $S_*(X)$  a *chain complex* – that is,  $d^2 = 0$ . We capture this process in a diagram:

**Example 2.1.** Suppose we have  $\sigma \colon \Delta^1 \to X$ . Define  $\phi \colon \Delta^1 \to \Delta^1$  by sending (t, 1-t) to (1-t, t). Precomposing  $\sigma$  with  $\phi$  gives another singular simplex  $\overline{\sigma}$  which reverses the orientation of  $\sigma$ . It is not true that  $\overline{\sigma} = -\sigma$  in  $S_1(X)$ .

However, we claim that  $\overline{\sigma} \equiv -\sigma \mod B_1(X)$ . This means that there is a 2-chain in X whose boundary is  $\overline{\sigma} + \sigma$ . If  $d_0\sigma = d_1\sigma$ , so that  $\sigma \in Z_1(X)$ , then  $\overline{\sigma}$  and  $-\sigma$  are homologous:  $[\overline{\sigma}] = -[\sigma]$  in  $H_1(X)$ .

To construct an appropriate boundary, consider the projection map  $\pi: \Delta^2 \to \Delta^1$  that is the affine extension of the map sending  $e_0$  and  $e_2$  to  $e_0$  and  $e_1$  to  $e_1$ .

2. HOMOLOGY 5

We'll compute  $d(\sigma \circ \pi)$ . Some of the terms will be constant singular simplices. Let's write  $c_x^n : \Delta^n \to X$  for the constant map with value  $x \in X$ . Then

$$d(\sigma \circ \pi) = \sigma \pi d^0 - \sigma \pi d^1 + \sigma \pi d^2 = \overline{\sigma} - c_{\sigma(0)}^1 + \sigma.$$

The constant simplex  $c_{\sigma(0)}^1$  is an "error term," and we wish to eliminate it. To achieve this we can use the constant 2-simplex  $c_{\sigma(0)}^2$  at  $\sigma(0)$ ; its boundary is

$$c_{\sigma(0)}^1 - c_{\sigma(0)}^1 + c_{\sigma(0)}^1 = c_{\sigma(0)}^1$$
.

So

$$\overline{\sigma} + \sigma = d(\sigma \circ \pi + c_{\sigma(0)}^2),$$

and  $\overline{\sigma} \equiv -\sigma \mod B_1(X)$  as claimed.

Some more language: two cycles that differ by a boundary dc are said to be *homologous*, and the chain c is a *homology* between them.

Let's compute the homology of the very simplest spaces,  $\varnothing$  and \*. For the first,  $\operatorname{Sin}_n(\varnothing) = \varnothing$ , so  $S_*(\varnothing) = 0$ . Hence  $\cdots \to S_2 \to S_1 \to S_0$  is the zero chain complex. This means that  $Z_*(\varnothing) = B_*(\varnothing) = 0$ . The homology in all dimensions is therefore 0.

For \*, we have  $\operatorname{Sin}_n(*) = \{c_*^n\}$  for all  $n \geq 0$ . Consequently  $S_n(*) = \mathbf{Z}$  for  $n \geq 0$  and 0 for n < 0. For each i,  $d_i c_*^n = c_*^{n-1}$ , so the boundary maps  $d: S_n(*) \to S_{n-1}(*)$  in the chain complex depend on the parity of n as follows:

$$d(c_*^n) = \sum_{i=0}^n (-1)^i c_*^{n-1} = \begin{cases} c_*^{n-1} & \text{for } n \text{ even, and} \\ 0 & \text{for } n \text{ odd.} \end{cases}$$

This means that our chain complex is:

$$0 \leftarrow \mathbf{Z} \stackrel{0}{\leftarrow} \mathbf{Z} \stackrel{1}{\leftarrow} \mathbf{Z} \stackrel{0}{\leftarrow} \mathbf{Z} \stackrel{1}{\leftarrow} \cdots$$

The boundaries coincide with the cycles except in dimension zero, where  $B_0(*) = 0$  while  $Z_0(*) = \mathbf{Z}$ . Therefore  $H_0(*) = \mathbf{Z}$  and  $H_i(*) = 0$  for  $i \neq 0$ .

We've defined homology groups for each space, but haven't yet considered what happens to maps between spaces. A continuous map  $f: X \to Y$  induces a map  $f_*: \operatorname{Sin}_n(X) \to \operatorname{Sin}_n(Y)$  by composition:

$$f_*: \sigma \mapsto f \circ \sigma$$
.

For  $f_*$  to be a map of semi-simplicial sets, it needs to commute with face maps: We need  $f_* \circ d_i = d_i \circ f_*$ . A diagram is said to be *commutative* if all composites with the same source and target are equal, so this equation is equivalent to commutativity of the diagram

$$\operatorname{Sin}_{n}(X) \xrightarrow{f_{*}} \operatorname{Sin}_{n}(Y) 
\downarrow^{d_{i}} \qquad \downarrow^{d_{i}} 
\operatorname{Sin}_{n-1}(X) \xrightarrow{f_{*}} \operatorname{Sin}_{n-1}(Y).$$

Well,  $d_i f_* \sigma = (f_* \sigma) \circ d^i = f \circ \sigma \circ d^i$ , and  $f_*(d_i \sigma) = f_*(\sigma \circ d^i) = f \circ \sigma \circ d^i$  as well. The diagram remains commutative when we pass to the free abelian groups of chains.

If  $C_*$  and  $D_*$  are chain complexes, a *chain map*  $f: C_* \to D_*$  is a collection of maps  $f_n: C_n \to D_n$  such that the following diagram commutes for every n:

$$C_{n} \xrightarrow{f_{n}} D_{n}$$

$$\downarrow^{d_{C}} \qquad \downarrow^{d_{D}}$$

$$C_{n-1} \xrightarrow{f_{n-1}} D_{n-1}$$

For example, if  $f: X \to Y$  is a continuous map, then  $f_*: S_*(X) \to S_*(Y)$  is a chain map as discussed above.

A chain map induces a map in homology  $f_*: H_n(C) \to H_n(D)$ . The method of proof is a socalled "diagram chase" and it will be the first of many. We check that we get a map  $Z_n(C) \to Z_n(D)$ . Let  $c \in Z_n(C)$ , so that  $d_C c = 0$ . Then  $d_D f_n(c) = f_{n-1} d_C c = f_{n-1}(0) = 0$ , because f is a chain map. This means that  $f_n(c)$  is also an n-cycle, i.e., f gives a map  $Z_n(C) \to Z_n(D)$ .

Similarly, we get a map  $B_n(C) \to B_n(D)$ . Let  $c \in B_n(C)$ , so that there exists  $c' \in C_{n+1}$  such that  $d_C c' = c$ . Then  $f_n(c) = f_n d_C c' = d_D f_{n+1}(c')$ . Thus  $f_n(c)$  is the boundary of  $f_{n+1}(c')$ , and f gives a map  $B_n(C) \to B_n(D)$ .

The two maps  $Z_n(C) \to Z_n(D)$  and  $B_n(C) \to B_n(D)$  quotient to give a map on homology  $f_*: H_n(X) \to H_n(Y)$ .

#### 3 Categories, functors, natural transformations

From spaces and continuous maps, we constructed graded abelian groups and homomorphisms. We now cast this construction in the more general language of category theory.

Our discussion of category theory will be interspersed throughout the text, introducing new concepts as they are needed. Here we begin by introducing the basic definitions.

**Definition 3.1.** A category  $\mathcal{C}$  consists of the following data.

- a class  $ob(\mathcal{C})$  of *objects*;
- for every pair of objects X and Y, a set of morphisms  $\mathcal{C}(X,Y)$ ;
- for every object X an identity morphism  $1_X \in \mathcal{C}(X,X)$ ; and
- for every triple of objects X, Y, Z, a composition map  $\mathcal{C}(X, Y) \times \mathcal{C}(Y, Z) \to \mathcal{C}(X, Z)$ , written  $(f, g) \mapsto g \circ f$ .

These data are required to satisfy the following:

- $1_Y \circ f = f$ , and  $f \circ 1_X = f$ .
- Composition is associative:  $(h \circ g) \circ f = h \circ (g \circ f)$ .

Note that we allow the collection of objects to be a class. This enables us to talk about a "category of all sets" for example. But we require each C(X,Y) to be set, and not merely a class. Some interesting categories have a *set* of objects; they are called *small categories*.

We will often write  $X \in \mathcal{C}$  to mean  $X \in \text{ob}(\mathcal{C})$ , and  $f: X \to Y$  to mean  $f \in \mathcal{C}(X,Y)$ .

**Definition 3.2.** If  $X, Y \in \mathcal{C}$ , then  $f: X \to Y$  is an *isomorphism* if there exists  $g: Y \to X$  with  $f \circ g = 1_Y$  and  $g \circ f = 1_X$ . We may write

$$f: X \xrightarrow{\cong} Y$$

to indicate that f is an isomorphism.

**Example 3.3.** Many common mathematical structures can be arranged in categories.

- Sets and functions between them form a category **Set**.
- Abelian groups and homomorphisms form a category **Ab**.
- Topological spaces and continuous maps form a category **Top**.
- Chain complexes and chain maps form a category chAb.
- A monoid is the same as a category with one object, where the elements of the monoid are the morphisms in the category. It's a small category.
- The sets  $[n] = \{0, ..., n\}$  for  $n \geq 0$  together with weakly order-preserving maps between them form the *simplex category*  $\Delta$ , another small category. It contains as a subcategory the *semi-simplex category*  $\Delta_{inj}$  with the same objects but only injective weakly order-preserving maps.
- A partially ordered set or "poset" forms a category in which there is a morphism from x to y iff  $x \leq y$ . A small category is a poset exactly when (1) there is at most one morphism between any two objects, and (2) the only isomorphisms are identities. This is to be distinguished from the category of posets and order-preserving maps between them, which is "large."

Categories may be related to each other by rules describing effect on both objects and morphisms.

**Definition 3.4.** Let  $\mathcal{C}, \mathcal{D}$  be categories. A functor  $F: \mathcal{C} \to \mathcal{D}$  consists of the data of

- an assignment  $F : ob(\mathcal{C}) \to ob(\mathcal{D})$ , and
- for all  $X, Y \in ob(\mathcal{C})$ , a function  $F : \mathcal{C}(X, Y) \to \mathcal{D}(F(X), F(Y))$ .

These data are required to satisfy the following two properties:

- For all  $X \in ob(\mathcal{C})$ ,  $F(1_X) = 1_{F(X)} \in \mathcal{D}(F(X), F(X))$ , and
- For all composable pairs of morphisms f, g in C,  $F(g \circ f) = F(g) \circ F(f)$ .

We have defined quite a few functors already:

$$\operatorname{Sin}_n : \operatorname{\mathbf{Top}} \to \operatorname{\mathbf{Set}}, \quad S_n : \operatorname{\mathbf{Top}} \to \operatorname{\mathbf{Ab}}, \quad H_n : \operatorname{\mathbf{Top}} \to \operatorname{\mathbf{Ab}}.$$

for example. We also have defined, for each X, a morphism  $d: S_n(X) \to S_{n-1}(X)$ . This is a "morphism between functors." This property is captured by another definition.

**Definition 3.5.** Let  $F, G: \mathcal{C} \to \mathcal{D}$  be two functors. A natural transformation or natural map  $\theta: F \to G$  consists of maps  $\theta_X: F(X) \to G(X)$  for all  $X \in ob(\mathcal{C})$  such that for all  $f: X \to Y$  the following diagram commutes.

$$F(X) \xrightarrow{\theta_X} G(X)$$

$$\downarrow^{F(f)} \qquad \downarrow^{G(f)}$$

$$F(Y) \xrightarrow{\theta_Y} G(Y)$$

So for example the boundary map  $d: S_n \to S_{n-1}$  is a natural transformation.

**Example 3.6.** Suppose that  $\mathcal{C}$  and  $\mathcal{D}$  are two categories, and assume that  $\mathcal{C}$  is small. We may then form the *category of functors* Fun( $\mathcal{C}, \mathcal{D}$ ). Its objects are the functors from  $\mathcal{C}$  to  $\mathcal{D}$ , and given two functors F, G, Fun( $\mathcal{C}, \mathcal{D}$ )(F, G) is the set of natural transformations from F to G. We let the reader define the rest of the structure of this category, and check the axioms. We needed to assume that  $\mathcal{C}$  is small in order to guarantee that there is no more than a set of natural transformations between functors.

For example, let G be a group (or a monoid) viewed as a one-object category. An object  $F \in \text{Fun}(G, \mathbf{Ab})$  is simply a group action of G on F(\*) = A, i.e., a representation of G in abelian groups. Given another  $F' \in \text{Fun}(G, \mathbf{Ab})$  with F'(\*) = A', a natural transformation from  $F \to F'$  is precisely a G-equivariant homomorphism  $A \to A'$ .

#### 4 Categorical language

Let  $\operatorname{Vect}_k$  be the category of vector spaces over a field k, and linear transformations between them. Given a vector space V, you can consider the dual  $V^* = \operatorname{Hom}(V, k)$ . Does this give us a functor? If you have a linear transformation  $f: V \to W$ , you get a map  $f^*: W^* \to V^*$ , so this is like a functor, but the induced map goes the wrong way. This operation does preserve composition and identities, in an appropriate sense. This is an example of a *contravariant functor*.

I'll leave it to you to spell out the definition, but notice that there is a univeral example of a contravariant functor out of a category  $\mathcal{C}: \mathcal{C} \to \mathcal{C}^{op}$ , where  $\mathcal{C}^{op}$  has the same objects as  $\mathcal{C}$ , but  $\mathcal{C}^{op}(X,Y)$  is declared to be the set  $\mathcal{C}(Y,X)$ . The identity morphisms remain the same. To describe the composition in  $\mathcal{C}^{op}$ , I'll write  $f^{op}$  for  $f \in \mathcal{C}(Y,X)$  regarded as an element of  $\mathcal{C}^{op}(X,Y)$ ; then  $f^{op} \circ g^{op} = (g \circ f)^{op}$ .

Then a contravariant functor from  $\mathcal{C}$  to  $\mathcal{D}$  is the same thing as a ("covariant") functor from  $\mathcal{C}^{op}$  to  $\mathcal{D}$ .

Let  $\mathcal{C}$  be a category, and let  $Y \in \text{ob}(\mathcal{C})$ . We get a map  $\mathcal{C}^{op} \to \mathbf{Set}$  that takes  $X \mapsto \mathcal{C}(X,Y)$ , and takes a map  $X \to W$  to the map defined by composition  $\mathcal{C}(W,Y) \to \mathcal{C}(X,Y)$ . This is called the functor represented by Y. It is very important to note that  $\mathcal{C}(-,Y)$  is contravariant, while, on the other hand, for any fixed X,  $\mathcal{C}(X,-)$  is a covariant functor (and is said to be "corepresentable" by X).

**Example 4.1.** Recall that the simplex category  $\Delta$  has objects the totally ordered sets  $[n] = \{0, 1, \ldots, n\}$ , with order preserving maps as morphisms. The "standard simplex" gives us a functor  $\Delta \colon \Delta \to \mathbf{Top}$ . Now fix a space X, and consider

$$[n] \mapsto \mathbf{Top}(\Delta^n, X)$$
.

This gives us a contravariant functor  $\Delta \to \mathbf{Set}$ , or a covariant functor  $\Delta^{op} \to \mathbf{Set}$ . This functor carries in it all the face and degeneracy maps we discussed earlier, and their compositions. Let us make a definition.

**Definition 4.2.** Let  $\mathcal{C}$  be any category. A *simplicial object* in  $\mathcal{C}$  is a functor  $K: \Delta^{op} \to \mathcal{C}$ . Simplicial objects in  $\mathcal{C}$  form a category with natural transformations as morphisms. Similarly, *semi-simplicial object* in  $\mathcal{C}$  is a functor  $\Delta^{op}_{inj} \to \mathcal{C}$ ,

So the singular functor Sin<sub>\*</sub> gives a functor from spaces to simplicial sets (and so, by restriction, to semi-simplicial sets).

I want to interject one more bit of categorical language that will often be useful to us.

**Definition 4.3.** A morphism  $f: X \to Y$  in a category  $\mathcal{C}$  is a *split epimorphism* ("split epi" for short) if there exists  $g: Y \to X$  (called a section or a splitting) such that the composite  $Y \xrightarrow{g} X \xrightarrow{f} Y$  is the identity.

**Example 4.4.** In the category of sets, a map  $f: X \to Y$  is a split epimorphism exactly when, for every element of Y there exists some element of X whose image in Y is the original element. So f is surjective. Is every surjective map a split epimorphism? This is equivalent to the axiom of choice! because a section of f is precisely a choice of  $x \in f^{-1}(y)$  for every  $y \in Y$ .

Every categorical definition is accompanied by a "dual" definition.

**Definition 4.5.** A map  $g: Y \to X$  is a *split monomorphism* ("split mono" for short) if there is  $f: X \to Y$  such that  $f \circ g = 1_Y$ .

**Example 4.6.** Again let  $C = \mathbf{Set}$ . Any split monomorphism is an injection: If  $y, y' \in Y$ , and g(y) = g(y'), we want to show that y = y'. Apply f, to get y = f(g(y)) = f(g(y')) = y'. But the injection  $\emptyset \to Y$  is a split monomorphism only if  $Y = \emptyset$ . So there's an asymmetry in the category of sets.

**Lemma 4.7.** A map is an isomorphism if and only if it is both a split epimorphism and a split monomorphism.

Proof. Easy!  $\Box$ 

The importance of these definitions is this: Functors will not in general respect "monomorphisms" or "epimorphisms," but:

**Lemma 4.8.** Any functor sends split epis to split epis and split monos to split monos.

*Proof.* Apply F to the diagram establishing f as a split epi or mono.  $\Box$ 

**Example 4.9.** Suppose C = Ab, and you have a split epi  $f : A \to B$ . Let  $g : B \to A$  be a section. We also have the inclusion  $i : \ker f \to A$ , and hence a map

$$[g \quad i]: B \oplus \ker f \to A.$$

I leave it to you to check that this map is an isomorphism, and to formulate a dual statement.

#### 5 Homotopy, star-shaped regions

We've computed the homology of a point. Let's now compare the homology of a general space X to this example. There's always a unique map  $X \to *$ : \* is a "terminal object" in **Top**. We have an induced map

$$H_n(X) \to H_n(*) = \begin{cases} \mathbf{Z} & n = 0\\ 0 & \text{otherwise} \end{cases}$$

Any formal linear combination  $c = \sum a_i x_i$  of points of X is a 0-cycle. The map to \* sends c to  $\sum a_i \in \mathbf{Z}$ . This defines the augmentation  $\epsilon : H_*(X) \to H_*(*)$ . If X is nonempty, the map  $X \to *$  is split by any choice of point in X, so the augmentation is also split epi. The kernel of  $\epsilon$  is the reduced homology  $\widetilde{H}_*(X)$  of X, and we get a canonical splitting

$$H_*(X) \cong \widetilde{H}_*(X) \oplus \mathbf{Z}$$
.

Actually, it's useful to extend the definition to the empty space by the following device. Extend the singular chain complex for any space to include  $\mathbf{Z}$  in dimension -1, with  $d: S_0(X) \to S_{-1}(X)$  given by the augmentation  $\epsilon$  sending each 0-simplex to  $1 \in \mathbf{Z}$ . Let's write  $\widetilde{S}_*(X)$  for this chain complex, and  $\widetilde{H}_*(X)$  for its homology. When  $X \neq \emptyset$ ,  $\epsilon$  is surjective and you get the same answer as above. But

$$\widetilde{H}_q(\varnothing) = \begin{cases} \mathbf{Z} & \text{for } q = -1 \\ 0 & \text{for } q \neq -1 \end{cases}.$$

This convention is not universally accepted, but I find it useful.  $\widetilde{H}_*(X)$  is the reduced homology of X.

What other spaces have trivial homology? A slightly non-obvious way to reframe the question is this:

When do two maps  $X \to Y$  induce the same map in homology?

For example, when do  $1_X: X \to X$  and  $X \to * \to X$  induce the same map in homology? If they do, then  $\epsilon: H_*(X) \to \mathbf{Z}$  is an isomorphism.

The key idea is that homology is a discrete invariant, so it should be unchanged by deformation. Here's the definition that makes "deformation" precise.

**Definition 5.1.** Let  $f_0, f_1: X \to Y$  be two maps. A homotopy from  $f_0$  to  $f_1$  is a map  $h: X \times I \to Y$  (continuous, of course) such that  $h(x,0) = f_0(x)$  and  $f(x,1) = f_1(x)$ . We say that  $f_0$  and  $f_1$  are homotopic, and that h is a homotopy between them. This relation is denoted by  $f_0 \simeq f_1$ .

Homotopy is an equivalence relation on maps from X to Y. Transitivity follows from the gluing lemma of point set topology. We denote by [X,Y] the set of homotopy classes of maps from X to Y. A key result about homology is this:

**Theorem 5.2** (Homotopy invariance of homology). If  $f_0 \simeq f_1$ , then  $H_*(f_0) = H_*(f_1)$ : homology cannot distinguish between homotopic maps.

Suppose I have two maps  $f_0, f_1: X \to Y$  with a homotopy  $h: f_0 \simeq f_1$ , and a map  $g: Y \to Z$ . Composing h with g gives a homotopy between  $g \circ f_0$  and  $g \circ f_1$ . Precomposing also works: If

 $g: W \to X$  is a map and  $f_0, f_1: X \to Y$  are homotopic, then  $f_0 \circ g \simeq f_1 \circ g$ . This lets us compose homotopy classes: we can complete the diagram:

$$\mathbf{Top}(Y,Z)\times\mathbf{Top}(X,Y)\longrightarrow\mathbf{Top}(X,Z)$$
 
$$\downarrow \qquad \qquad \downarrow$$
 
$$[Y,Z]\times[X,Y]---->[X,Z]$$

**Definition 5.3.** The homotopy category (of topological spaces)  $\text{Ho}(\mathbf{Top})$  has the same objects as  $\mathbf{Top}$ , but  $\text{Ho}(\mathbf{Top})(X,Y) = [X,Y] = \mathbf{Top}(X,Y)/\simeq$ .

We may restate Theorem 5.2 as follows:

For each n, the homology functor  $H_n : \mathbf{Top} \to \mathbf{Ab}$  factors as  $\mathbf{Top} \to \mathbf{Ho}(\mathbf{Top}) \to \mathbf{Ab}$ ; it is a "homotopy functor."

We will prove this in the next lecture, but let's stop now and think about some consequences.

**Definition 5.4.** A map  $f: X \to Y$  is a homotopy equivalence if  $[f] \in [X, Y]$  is an isomorphism in Ho(**Top**). In other words, there is a map  $g: Y \to X$  such that  $fg \simeq 1_Y$  and  $gf \simeq 1_X$ .

Such a map g is a homotopy inverse for f; it is well-defined only up to homotopy.

Most topological properties are not preserved by homotopy equivalences. For example, compactness is not a homotopy-invariant property: Consider the inclusion  $i: S^{n-1} \subseteq \mathbf{R}^n - \{0\}$ . A homotopy inverse  $p: \mathbf{R}^n - \{0\} \to S^{n-1}$  can be obtained by dividing a (always nonzero!) vector by its length. Clearly  $p \circ i = 1_{S^{n-1}}$ . We have to find a homotopy  $i \circ p \simeq 1_{\mathbf{R}^n - \{0\}}$ . This is a map  $(\mathbf{R}^n - \{0\}) \times I \to \mathbf{R}^n - \{0\}$ , and we can use  $(v, t) \mapsto tv + (1 - t) \frac{v}{||v||}$ .

On the other hand:

Corollary 5.5. Homotopy equivalences induce isomorphisms in homology.

*Proof.* If f has homotopy inverse g, then  $f_*$  has inverse  $g_*$ .

**Definition 5.6.** A space X is *contractible* if the map  $X \to *$  is a homotopy equivalence.

Corollary 5.7. Let X be a contractible space. The augmentation  $\epsilon: H_*(X) \to \mathbf{Z}$  is an isomorphism.

Homotopy equivalences in general may be somewhat hard to visualize. A particularly simple and important class of homotopy equivalences is given by the following definition.

**Definition 5.8.** An inclusion  $A \hookrightarrow X$  is a deformation retract provided that there is a map  $h: X \times I \to X$  such that h(x,0) = x and  $h(x,1) \in A$  for all  $x \in X$  and h(a,t) = a for all  $a \in A$  and  $t \in I$ .

For example,  $S^{n-1}$  is a deformation retract of  $\mathbf{R}^n - \{0\}$ .

We now set about constructing a proof of homotopy invariance of homology. The first step is to understand the analogue of homotopy on the level of chain complexes.

**Definition 5.9.** Let  $C_*, D_*$  be chain complexes, and  $f_0, f_1 : C_* \to D_*$  be chain maps. A *chain homotopy*  $h : f_0 \simeq f_1$  is a collection of homomorphisms  $h : C_n \to D_{n+1}$  such that  $dh + hd = f_1 - f_0$ .

This relation takes some getting used to. It is an equivalence relation. Here's a picture (not a commutive diagram).

$$\cdots \longrightarrow C_{n+1} \xrightarrow{d} C_n \xrightarrow{d} C_{n-1} \longrightarrow \cdots$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \downarrow \qquad \downarrow$$

**Lemma 5.10.** If  $f_0, f_1 : C_* \to D_*$  are chain homotopic, then  $f_{0*} = f_{1*} : H_*(C) \to H_*(D)$ .

*Proof.* We want to show that for every  $c \in Z_n(C_*)$ , the difference  $f_1c - f_0c$  is a boundary. Well,

$$f_1c - f_0c = (dh + hd)c = dhc + hdc = dhc$$
.

So homotopy invariance of homology will follow from

**Proposition 5.11.** Let  $f_0, f_1 : X \to Y$  be homotopic. Then  $f_{0*}, f_{1*} : S_*(X) \to S_*(Y)$  are chain homotopic.

To prove this we will begin with a special case.

**Definition 5.12.** A subset  $X \subseteq \mathbf{R}^n$  is *star-shaped* with respect to  $b \in X$  if for every  $x \in X$  the interval

$$\{tb + (1-t)x : t \in [0,1]\}$$

lies in X.

Any nonempty convex region is star shaped. Any star-shaped region X is contractible: A homotopy inverse to  $X \to *$  is given by sending  $* \mapsto b$ . One composite is perforce the identity. A homotopy from the other composite to the identity  $1_X$  is given by  $(x,t) \mapsto tb + (1-t)x$ .

So we should expect that  $\epsilon: H_*(X) \to \mathbf{Z}$  is an isomorphism if X is star-shaped. In fact, using a piece of language that the reader can interpret:

**Proposition 5.13.**  $S_*(X) \to \mathbf{Z}$  is a chain homotopy equivalence.

Proof. We have maps  $S_*(X) \xrightarrow{\epsilon} \mathbf{Z} \xrightarrow{\eta} S_*(X)$  where  $\eta(1) = c_b^0$ . Clearly  $\epsilon \eta = 1$ , and the claim is that  $\eta \epsilon \simeq 1 : S_*(X) \to S_*(X)$ . The chain map  $\eta \epsilon$  concentrates everything at the point  $b : \eta \epsilon \sigma = c_b^n$  for all  $\sigma \in \operatorname{Sin}_n(X)$ . Our chain homotopy  $h : S_q(X) \to S_{q+1}(X)$  will actually send simplices to

simplices. For  $\sigma \in \operatorname{Sin}_q(X)$ , define the chain homotopy evaluated on  $\sigma$  by means of the following "cone construction":  $h(\sigma) = b * \sigma$ , where

$$(b*\sigma)(t_0,\ldots,t_{q+1}) = t_0b + (1-t_0)\sigma\left(\frac{(t_1,\ldots,t_{q+1})}{1-t_0}\right).$$

Explanation: The denominator  $1 - t_0$  makes the entries sum to 1, as they must if we are to apply  $\sigma$  to this vector. When  $t_0 = 1$ , this isn't defined, but it doesn't matter since we are multiplying by  $1 - t_0$ . So  $(b * \sigma)(1, 0, ..., 0) = b$ ; this is the vertex of the cone.

Setting  $t_0 = 0$ , we find

$$d_0b*\sigma=\sigma$$
.

Setting  $t_i = 0$  for i > 0, we find

$$d_i b * \sigma = h d_{i-1} \sigma.$$

Using the formula for the boundary operator, we find

$$db * \sigma = \sigma - b * d\sigma$$

 $\dots unless q = 0$ , when

$$db * \sigma = \sigma - c_b^0.$$

This can be assembled into the equation

$$db*+b*d=1-\eta\epsilon$$

which is what we wanted.

## 6 Homotopy invariance of homology

We now know that the homology of a star-shaped region is trivial: in such a space, every cycle with augmentation 0 is a boundary. We will use that fact, which is a special case of homotopy invariance of homology, to prove the general result, which we state in somewhat stronger form:

**Theorem 6.1.** A homotopy  $h: f_0 \simeq f_1: X \to Y$  determines a natural chain homotopy  $f_{0*} \simeq f_{1*}: S_*(X) \to S_*(Y)$ .

The proof uses naturality (a lot). For a start, notice that if  $k: g_0 \simeq g_1: C_* \to D_*$  is a chain homotopy, and  $j: D_* \to E_*$  is another chain map, then the composites  $j \circ k_n: C_n \to E_{n+1}$  give a chain homotopy  $j \circ g_0 \simeq j \circ g_1$ . So if we can produce a chain homotopy between the chain maps induced by the two inclusions  $i_0, i_1: X \to X \times I$ , we can get a chain homotopy k between  $f_{0*} = h_* \circ i_{0*}$  and  $f_{1*} = h_* \circ i_{1*}$  in the form  $h_* \circ k$ .

So now we want to produce a natural chain homotopy, with components  $k_n: S_n(X) \to S_{n+1}(X \times I)$ . The unit interval hosts a natural 1-simplex given by an identification  $\Delta^1 \to I$ , and we should imagine k as being given by "multiplying" by that 1-chain. This "multiplication" is a special case of a chain map

$$\times: S_*(X) \times S_*(Y) \to S_*(X \times Y)$$
,

defined for any two spaces X and Y, with lots of good properties. It will ultimately be used to compute the homology of a product of two spaces in terms of the homology groups of the factors. Here's the general result.

**Theorem 6.2.** There exists a map  $\times : S_p(X) \times S_q(Y) \to S_{p+q}(X \times Y)$ , the cross product, that is:

- Natural, in the sense that if  $f: X \to X'$  and  $g: Y \to Y'$ , and  $a \in S_p(X)$  and  $b \in S_p(Y)$  so that  $a \times b \in S_{p+q}(X \times Y)$ , then  $f_*(a) \times g_*(b) = (f \times g)_*(a \times b)$ .
- Bilinear, in the sense that  $(a + a') \times b = (a \times b) + (a' \times b)$ , and  $a \times (b + b') = a \times b + a \times b'$ .
- The Leibniz rule is satisfied, i.e.,  $d(a \times b) = (da) \times b + (-1)^p a \times db$ .
- Normalized, in the following sense. Let  $x \in X$  and  $y \in Y$ . Write  $j_x : Y \to X \times Y$  for  $y \mapsto (x,y)$ , and write  $i_y : X \to X \times Y$  for  $x \mapsto (x,y)$ . If  $b \in S_q(Y)$ , then  $c_x^0 \times b = (j_x)_*b \in S_q(X \times Y)$ , and if  $a \in S_p(X)$ , then  $a \times c_y^0 = (i_y)_*a \in S_p(X \times Y)$ .

The Leibniz rule contains the first occurrence of the "topologist's sign rule"; we'll see these signs appearing often. Watch for when it appears in our proof.

*Proof.* We're going to use induction on p+q; the normalization axiom gives us the cases p+q=0,1. Let's assume that we've constructed the cross-product in total dimension p+q-1. We want to define  $\sigma \times \tau$  for  $\sigma \in S_p(X)$  and  $\tau \in S_q(Y)$ .

Note that there's a universal example of a p-simplex, namely the identity map  $\iota_p: \Delta^p \to \Delta^p$ . It's universal in the sense any p-simplex  $\sigma: \Delta^p \to X$  can be written as  $\sigma_*(\iota_p)$  where  $\sigma_*: \operatorname{Sin}_p(\Delta^p) \to \operatorname{Sin}_p(X)$  is the map induced by  $\sigma$ . To define  $\sigma \times \tau$  in general, then, it suffices to define  $\iota_p \times \iota_q \in S_{p+q}(\Delta^p \times \Delta^q)$ ; we can (and must) then take  $\sigma \times \tau = (\sigma \times \tau)_*(\iota_p \times \iota_q)$ .

Our long list of axioms is useful in the induction. For one thing, if p = 0 or q = 0, normalization provides us with a choice. So now assume that both p and q are positive. We want the cross-product to satisfy the Leibnitz rule:

$$d(\iota_p \times \iota_q) = (d\iota_p) \times \iota_q + (-1)^p \iota_p \times d\iota_q \in S_{p+q-1}(\Delta^p \times \Delta^q)$$

Since  $d^2 = 0$ , a necessary condition for  $\iota_p \times \iota_q$  to exist is that  $d((d\iota_p) \times \iota_q + (-1)^p \iota_p \times d\iota_q) = 0$ . Let's compute what this is, using the Leibnitz rule in dimension p + q - 1 where we have it by the inductive assumption:

$$d((d\iota_p) \times \iota_q + (-1)^p \iota_p \times (d\iota_q)) = (d^2\iota_p) \times \iota_q + (-1)^{p-1} (d\iota_p) \times (d\iota_q) + (-1)^p (d\iota_p) \times (d\iota_q) + (-1)^q \iota_p \times (d^2\iota_q) = 0$$

because  $d^2 = 0$ . Note that this calculation would not have worked without the sign!

The subspace  $\Delta^p \times \Delta^q \subseteq \mathbf{R}^{p+1} \times \mathbf{R}^{q+1}$  is convex and nonempty, and hence star-shaped. Therefore we know that  $H_{p+q-1}(\Delta^p \times \Delta^q) = 0$  (remember, p+q>1), which means that every cycle is a boundary. In other words, our necessary condition is also sufficient! So, choose any element with the right boundary and declare it to be  $\iota_p \times \iota_q$ .

The induction is now complete provided we can check that this choice satisfies naturality, bilinearity, and the Leibniz rule. I leave this as a relaxing exercise for the listener.  $\Box$ 

The essential point here is that the space supporting the universal pair of simplices  $-\Delta^p \times \Delta^q$  – has trivial homology. Naturality transports the result of that fact to the general situation.

The cross-product that this procedure constructs is not unique; it depends on a choice a choice of the chain  $\iota_p \times \iota_q$  for each pair p,q with p+q>1. The cone construction in the proof that star-shaped regions have vanishing homology provids us with a specific choice; but it turns out that any two choices are equivalent up to natural chain homotopy.

We return to homotopy invariance. To define our chain homotopy  $h_X: S_n(X) \to S_{n+1}(X \times I)$ , pick any 1-simplex  $\iota: \Delta^1 \to I$  such that  $d_0\iota = c_1^0$  and  $d_1\iota = c_0^0$ , and define

$$h_X \sigma = (-1)^n \sigma \times \iota.$$

Let's compute:

$$dh_X \sigma = (-1)^n d(\sigma \times \iota) = (-1)^n (d\sigma) \times \iota + \sigma \times (d\iota)$$

But  $d\iota = c_1^0 - c_0^0 \in S_0(I)$ , which means that we can continue (remembering that  $|\partial \sigma| = n - 1$ ):

$$= -h_X d\sigma + (\sigma \times c_1^0 - \sigma \times c_0^0) = -h_X d\sigma + (\iota_{1*}\sigma - \iota_{0*}\sigma),$$

using the normalization axiom of the cross-product. This is the result.

## 7 Homology cross product

In the last lecture we proved homotopy invariance of homology using the construction of a chain level bilinear cross-product

$$\times: S_p(X) \times S_q(Y) \to S_{p+q}(X \times Y)$$

that satisfied the Leibniz formula

$$d(a \times b) = (da) \times b + (-1)^p a \times (db)$$

What else does this map give us?

Let's abstract a little bit. Suppose we have three chain complexes  $A_*$ ,  $B_*$ , and  $C_*$ , and suppose we have maps  $\times : A_p \times B_q \to C_{p+q}$  that satisfy bilinearity and the Leibniz formula. What does this induce in homology?

**Lemma 7.1.** These data determine a bilinear map  $\times : H_p(A) \times H_q(B) \to H_{p+q}(C)$ .

*Proof.* Let  $a \in Z_p(A)$  and  $b \in Z_q(B)$ . We want to define  $[a] \times [b] \in H_{p+q}(C)$ . We hope that  $[a] \times [b] = [a \times b]$ . We need to check that  $a \times b$  is a cycle. By Leibniz,  $d(a \times b) = da \times b + (-1)^p a \times db$ , which vanishes because a, b are cycles.

Now we need to check that homology class depends only on the homology classes we started with. So pick other cycles a' and b' in the same homology classes. We want  $[a \times b] = [a' \times b']$ . In

other words, we need to show that  $a \times b$  differs from  $a' \times b'$  by a boundary. We can write  $a' = a + d\overline{a}$  and  $b' = b + d\overline{b}$ , and compute, using bilinearity:

$$a' \times b' = (a + d\overline{a}) + (b + d\overline{b}) = a \times b + a \times d\overline{b} + (d\overline{a}) \times b + (d\overline{a}) \times (d\overline{b})$$

We need to deal with the last three terms here. But since da = 0,

$$d(a \times \overline{b}) = (-1)^p a \times (d\overline{b})$$
.

Since  $d\bar{b} = 0$ ,

$$d((\overline{a}) \times b) = (d\overline{a}) \times b$$
.

And since  $d^2\bar{b} = 0$ ,

$$d(a \times \overline{b}) = (d\overline{a}) \times (d\overline{b}).$$

This means that  $a' \times b'$  and  $a \times b$  differ by

$$d\left((-1)^p(a\times\overline{b})+\overline{a}\times b+\overline{a}\times d\overline{b}\right)$$
,

and so are homologous.

The last step is to check bilinearity, which is left to the listener.

This gives the following result.

#### Theorem 7.2. There is a map

$$\times: H_p(X) \times H_q(Y) \to H_{p+q}(X \times Y)$$

that is natural, bilinear, and normalized.

We will see that this map is also *uniquely defined* by these conditions, unlike the chain-level cross product.

I just want to mention an explicit choice of  $\iota_p \times \iota_q$ . This is called the Eilenberg-Zilber chain. You're highly encouraged to think about this yourself. It comes from a triangulation of the prism.

The simplices in this triangulation are indexed by order preserving injections

$$\omega: [p+q] \to [p] \times [q]$$

Injectivity forces  $\omega(0) = (0,0)$  and  $\omega(p+q) = (p,q)$ . Each such map determines an affine map  $\Delta^{p+q} \to \Delta^p \times \Delta^q$  of the same name. These will be the singular simplices making up  $\iota_p \times \iota_q$ . To specify the coefficients, think of  $\omega$  as a staircase in the rectangle  $[0,p] \times [0,q]$ . Let  $A(\omega)$  denote the area under that staircase. Then the Eilenberg-Zilber chain is given by

$$\iota_p \times \iota_q = \sum (-1)^{A(\omega)} \omega$$

This chain is due to Eilenberg and Mac Lane; the description appears in a paper [4] by Eilenberg and Moore. It's very pretty, but it's combinatorially annoying to check that this satisfies the conditions of the theorem. It provides an explicit chain map

$$\beta_{X,Y}: S_*(X) \times S_*(Y) \to S_*(X \times Y)$$

that satisfies many good properties on the nose and not just up to chain homotopy. For example, it's associative –

$$S_{*}(X) \times S_{*}(Y) \times S_{*}(Z) \xrightarrow{\beta_{X,Y} \times 1} S_{*}(X \times Y) \times S_{*}(Z)$$

$$\downarrow^{1 \times \beta Y, Z} \qquad \qquad \downarrow^{\beta_{X \times Y, Z}}$$

$$S_{*}(X) \times S_{*}(Y \times Z) \xrightarrow{\beta_{X,Y \times Z}} S_{*}(X \times Y \times Z)$$

commutes - and commutative -

$$S_{*}(X) \times S_{*}(Y) \xrightarrow{\beta_{X,Y}} S_{*}(X \times Y)$$

$$\downarrow^{T} \qquad \downarrow^{S_{*}(T)}$$

$$S_{*}(Y) \times S_{*}(X) \xrightarrow{\beta_{Y,X}} S_{*}(X \times Y)$$

commutes, where on spaces T(x,y) = (y,x), and on chain complexes  $T(a,b) = (-1)^{pq}(b,a)$  when a has degree p and b has degree q.

We will see that these properties hold up to chain homotopy for any choice of chain-level cross product.

## 8 Relative homology

An ultimate goal of algebraic topology is to find means to compute the set of homotopy classes of maps from one space to another. This is important because many geometrical problems can be rephrased as such a computation. It's a lot more modest than wanting to characterize, somehow, all continuous maps from X to Y; but the very fact that it still contains a great deal of interesting information means that it is still a very challenging problem.

Homology is in a certain sense the best "additive" approximation to this problem; and its additivity makes it much more computable. To justify this, we want to describe the sense in which homology is "additive." Here are two related aspects of this claim.

- 1. If  $A \subseteq X$  is a subspace, then  $H_*(X)$  a combination of  $H_*(A)$  and  $H_*(X-A)$ .
- 2. The homology  $H_*(A \cup B)$  is like  $H_*(A) + H_*(B) H_*(A \cap B)$ .

The first hope is captured by the long exact sequence of a pair, the second by the Mayer-Vietoris Theorem. Both facts show that homology behaves like a measure. The precise statement of both facts uses the machinery of exact sequences. I'll use the following language.

**Definition 8.1.** A sequence of abelian groups is a diagram of abelian groups of the form

$$\cdots \to C_{n+1} \xrightarrow{f_n} C_n \xrightarrow{f_{n-1}} C_{n-1} \to \cdots$$

in which all composites are zero; that is, im  $f_n \subseteq \ker f_{n-1}$  for all n. It is exact at  $C_n$  provided that this inequality is an equality.

A sequence is just another name for a chain complex; it is exact at  $C_n$  if and only if  $H_n(C_*) = 0$ . So homology measures the failure of exactness.

**Example 8.2.** Sequences may be zero for n large or for n small. We may just not write them down if all the groups from some point on are zero. For example,  $0 \to A \xrightarrow{i} B$  is exact iff i is injective, and  $B \xrightarrow{p} C \to 0$  is exact iff p is surjective.

Exactness was a key concept in the development of algebraic topology, and "exact" is a great word for the concept. A foundational treatment [5] of algebraic topology was published by Sammy Eilenberg and Norman Steenrod in 1952. The story goes that in the galleys for the book they left a blank space whenever the word representing this concept was used, and filled it in at the last minute.

**Definition 8.3.** A short exact sequence is an exact sequence of the form

$$0 \to A \xrightarrow{i} B \xrightarrow{p} C \to 0$$
.

Any sequence of the form  $A \to B \to C$  expands to a diagram

It is exact at B if and only if  $A \xrightarrow{\cong} \ker p$  or, equivalently,  $\operatorname{coker}(i) \xrightarrow{\cong} C$ . It is short exact if furthermore i is injective and p is surjective.

We will study the homology of a space X by comparing it to the homology of a subspace A and a complement or quotient modulo the subspace. Note that  $S_*(A)$  injects into  $S_*(X)$ . This suggests considering the quotient group

$$\frac{S_n(X)}{S_n(A)}$$
.

This is the group of *relative n-chains* of the pair (X, A).

Let's formalize this a bit. Along with the category **Top** of spaces, we have the category **Top<sub>2</sub>** of pairs of spaces. An object of **Top<sub>2</sub>** is a space X together with a subspace A. A map  $(X, A) \to (Y, B)$  is a continuous map  $X \to Y$  that sends A into B.

There are four obvious functors relating **Top** and **Top<sub>2</sub>**:

$$X \mapsto (X, \varnothing), \quad X \mapsto (X, X),$$

$$(X, A) \mapsto X$$
,  $(X, A) \mapsto A$ .

Do the relative chains form themselves into a chain complex?

**Lemma 8.4.** Let  $A_*$  be a subcomplex of the chain complex  $B_*$ . There is a unique structure of chain complex on the quotient graded abelian group  $C_*$  with entries  $C_n = B_n/A_n$  such that  $B_* \to C_*$  is a chain map.

*Proof.* To define  $d: C_n \to C_{n-1}$ , represent  $c \in C_n$  by  $b \in B_n$ , and hope that  $[db] \in B_{n-1}/A_{n-1}$  is well defined. If we replace b by b+a for  $a \in A_n$ , we find

$$d(b+a) = db + da \equiv db \mod A_{n-1}$$

so our hope is justified. Then  $d^2[b] = [d^2b] = 0$ .

**Definition 8.5.** The relative singular chain complex of the pair (X, A) is

$$S_*(X,A) = \frac{S_*(X)}{S_*(A)}.$$

This is a functor from pairs of spaces to chain complexes. Of course

$$S_*(X,\varnothing) = S_*(X), \quad S_*(X,X) = 0.$$

**Definition 8.6.** The relative singular homology of the pair (X, A) is the homology of the relative singular chain complex:

$$H_n(X,A) = H_n(S_*(X,A)).$$

One of the nice features of the absolute chain group  $S_n(X)$  is that it is free as an abelian group. This is also the case for its quotent  $S_n(X,A)$ , since the map  $S_n(A) \to S_n(X)$  takes basis elements to basis elements.  $S_n(X,A)$  is freely generated by the *n*-simplices in X that do not lie entirely in A.

**Example 8.7.** Consider  $\Delta^n$ , relative to its boundary

$$\partial \Delta^n := \bigcup \operatorname{im} d_i \cong S^{n-1}.$$

We have the identity map  $\iota_n : \Delta^n \to \Delta^n$ , the universal n-simplex, in  $\operatorname{Sin}_n(\Delta^n) \subseteq S_n(\Delta^n)$ . It is not a cycle; its boundary  $d\iota_n \in S_{n-1}(\Delta^n)$  is the alternating sum of the faces of the n-simplex. Each of these singular simplices lies in  $\partial \Delta^n$ , so  $d\iota_n \in S_{n-1}(\partial \Delta^n)$ , and  $[\iota_n] \in S_n(\Delta_n, \partial \Delta_n)$  is a relative cycle. We will see that the relative homology  $H_n(\Delta^n, \partial \Delta^n)$  is infinite cyclic, with generator  $[\iota_n]$ .

## 9 The homology long exact sequence

A pair of spaces (X, A) gives rise to a short exact sequence of chain complexes:

$$0 \to S_*(A) \to S_*(X) \to S_*(X,A) \to 0$$
.

In homology, this will relate  $H_*(A)$ ,  $H_*(X)$ , and  $H_*(X,A)$ .

To investigate what happens, let's suppse we have a general short exact sequence of chain complexes,

$$0 \to A_* \to B_* \to C_* \to 0$$

and study what happens in homology. Clearly the composite  $H_*(A) \to H_*(B) \to H_*(C)$  is trivial. Is this sequence exact? Let  $[b] \in H_n(B)$  such that g([b]) = 0. It's determined by some  $b \in B_n$  such that d(b) = 0. If g([b]) = 0, then there is some  $\overline{c} \in C_{n+1}$  such that  $d\overline{c} = gb$ . Now, g is surjective, so there is some  $\overline{b} \in B_{n+1}$  such that  $g(\overline{b}) = \overline{c}$ . Then we can consider  $d\overline{b} \in B_n$ , and  $g(d(\overline{b})) = d(\overline{c}) \in C_n$ . What is  $b - d\overline{b}$ ? This maps to zero in  $C_n$ , so by exactness there is some  $a \in A_n$  such that  $f(a) = b - d\overline{b}$ . Is a a cycle? Well,  $f(da) = d(fa) = d(b - d\overline{b}) = db - d^2\overline{b} = db$ , but we assumed that db = 0, so f(da) = 0. This means that da is zero because f is an injection by

exactness. Therefore a is a cycle. What is  $[a] \in H_n(A)$ ? Well,  $f([a]) = [b - d\bar{b}] = [b]$ . This proves exactness of  $H_n(A) \to H_n(B) \to H_n(C)$ .

On the other hand,  $H_*(A) \to H_*(B)$  may fail to be injective, and  $H_*(B) \to H_*(C)$  may fail to be surjective. Instead:

**Theorem 9.1** (The homology long exact sequence). Let  $0 \to A_* \to B_* \to C_* \to 0$  be a short exact sequence of chain complexes. Then there is a natural homomorphism  $\partial: H_n(C) \to H_{n-1}(A)$  such that the sequence

$$H_n(A) \xrightarrow{\partial} H_{n+1}(C)$$

$$H_n(A) \xrightarrow{\partial} H_n(C)$$

$$H_{n-1}(A) \xrightarrow{\partial} \cdots$$

is exact.

*Proof.* We'll construct  $\partial$ , and leave the rest as an exercise. Here's an expanded part of this short exact sequence:

$$0 \longrightarrow A_{n+1} \xrightarrow{f} B_{n+1} \xrightarrow{g} C_{n+1} \longrightarrow 0$$

$$\downarrow^{d} \qquad \downarrow^{d} \qquad \downarrow^{d}$$

$$0 \longrightarrow A_{n} \xrightarrow{f} B_{n} \xrightarrow{g} C_{n} \longrightarrow 0$$

$$\downarrow^{d} \qquad \downarrow^{d} \qquad \downarrow^{d}$$

$$0 \longrightarrow A_{n-1} \xrightarrow{f} B_{n-1} \xrightarrow{g} C_{n-1} \longrightarrow 0$$

Let  $c \in C_n$  be a cycle: dc = 0. The map g is surjective, so pick a  $b \in B_n$  such that g(b) = c, and consider  $db \in B_{n-1}$ . Well, g(d(b)) = d(g(b)) = dc = 0. So by exactness, there is some  $a \in A_{n-1}$  such that f(a) = db. How many choices are there of picking a? Only one, because f is injective. We need to check that a is a cycle. What is d(a)? Well,  $d^2b = 0$ , so da maps to 0 under f. But because f is injective, da = 0, i.e., a is a cycle. This means we can define  $\partial[c] = [a]$ .

To make sure that this is well-defined, let's make sure that this choice of homology class a didn't depend on the b that we chose. Pick some other b' such that g(b') = c. Then there is  $a' \in A_{n-1}$  such that f(a') = db'. We want a - a' to be a boundary, so that [a] = [a']. We want  $\overline{a} \in A_n$  such that  $d\overline{a} = a - a'$ . Well, g(b - b') = 0, so by exactness, there is  $\overline{a} \in A_n$  such that  $f(\overline{a}) = b - b'$ . What is  $d\overline{a}$ ? Well,  $d\overline{a} = d(b - b') = db - db'$ . But f(a - a') = b - b', so because f is injective,  $d\overline{a} = a - a'$ , i.e., [a] = [a']. I leave the rest of what needs checking to the listener.

**Example 9.2.** A pair of spaces (X, A) gives rise to a natural long exact sequence in homology:

**Example 9.3.** Let's think again about the pair  $(D^n, S^{n-1})$ . By homotopy invariance we know that  $H_q(D^n) = 0$  for q > 0, since  $D^n$  is contractible. So

$$\partial: H_q(D^n, S^{n-1}) \to H_{q-1}(S^{n-1})$$

is an isomorphism for q > 1. The bottom of the long exact sequence looks like this:

$$0 \longrightarrow H_1(D^n, S^{n-1})$$

$$H_0(S^{n-1}) \longrightarrow H_0(D^n) \longrightarrow H_0(D^n, S^{n-1}) \longrightarrow 0$$

When n > 1, both  $S^{n-1}$  and  $D^n$  are path-connected, so the map  $H_0(S^{n-1}) \to H_0(D^n)$  is an isomorphism, and

$$H_1(D^n, S^{n-1}) = H_0(D^n, S^{n-1}) = 0.$$

When n = 1, we discover that

$$H_1(D^1, S^0) = \mathbf{Z}$$
 and  $H_0(D^1, S^0) = 0$ .

The generator of  $H_1(D^1, S^0)$  is represented by any 1-simplex  $\iota_1 : \Delta^1 \to D^1$  such that  $d_0\iota = c_1^0$  and  $d_1\iota = c_0^0$  (or vice versa). To go any further in this analysis, we'll need another tool, known as "excision."

We can set this up for reduced homology (as in Lecture 5) as well. Note that any map induces an isomorphism in  $\widetilde{S}_{-1}$ , so to a pair (X, A) we can associate a short exact sequence

$$0 \to \widetilde{S}_*(A) \to \widetilde{S}_*(X) \to S_*(X,A) \to 0$$

and hence a long exact sequence

$$H_{n+1}(X,A) .$$

$$\widetilde{H}_n(A) \xrightarrow{\partial} H_n(X,A)$$

$$\widetilde{H}_{n-1}(A) \xrightarrow{\partial} \cdots$$

In the example  $(D^n, S^{n-1})$ ,  $\widetilde{H}_*(D^n) = 0$  and so

$$\partial: H_q(D^n, S^{n-1}) \xrightarrow{\cong} \widetilde{H}_{q-1}(S^{n-1})$$

for all n and q. This even works when n=0; remember that  $S^{-1}=\varnothing$  and  $\widetilde{H}_{-1}(\varnothing)=\mathbf{Z}$ . This is why I like this convention.

The homology long exact sequence is often used in conjunction with an elementary fact about a map between exact sequences known as the *five lemma*. Suppose you have two exact sequences of abelian groups and a map between them - a "ladder":

$$A_{4} \xrightarrow{d} A_{3} \xrightarrow{d} A_{2} \xrightarrow{d} A_{1} \xrightarrow{d} A_{0}$$

$$\downarrow f_{4} \qquad \downarrow f_{3} \qquad \downarrow f_{2} \qquad \downarrow f_{1} \qquad \downarrow f_{0}$$

$$B_{4} \xrightarrow{d} B_{3} \xrightarrow{d} B_{2} \xrightarrow{d} B_{1} \xrightarrow{d} B_{0}$$

When can we guarantee that the middle map  $f_2$  is an isomorphism? We're going to "diagram chase." Just follow your nose, making assumptions as necessary.

Surjectivity: Let  $b_2 \in B_2$ . We want to show that there is something in  $A_2$  mapping to  $b_2$ . We can consider  $db_2 \in B_1$ . Let's assume that  $f_1$  is surjective. Then there's  $a_1 \in A_1$  such that  $f_1(a_1) = db_2$ . What is  $da_1$ ? Well,  $f_0(da_1) = d(f_1(a_1)) = d(db) = 0$ . So we want  $f_0$  to be injective. Then  $da_1$  is zero, so by exactness of the top sequence, there is some  $a_2 \in A_2$  such that  $da_2 = a_1$ . What is  $f_2(a_2)$ ? To answer this, begin by asking: What is  $d(f_2(a_2))$ ? By commutativity,  $d(f_2(a_2)) = f_1(d(a_2)) = f_1(a_1) = db_2$ . Let's consider  $b_2 - f_2(a_2)$ . This maps to zero under d. So by exactness, there is  $b_3 \in B_3$  such that  $d(b_3) = b_2 - f_2(a_2)$ . If we assume that  $f_3$  is surjective, then there is  $a_3 \in A_3$  such that  $f_3(a_3) = b_3$ . But now  $d(a_3) \in A_2$ , and  $f_2(d(a_3)) = d(f_3(a_3)) = b_2 - f_2(a_2)$ . This means that  $b_2 = f(a_2 + d(a_3))$ , verifying surjectivity of  $f_2$ .

This proves the first half of the following important fact. The second half is "dual" to the first.

**Proposition 9.4** (Five lemma). In the map of exact sequences above,

- If  $f_0$  is injective and  $f_1$  and  $f_3$  are surjective, then  $f_2$  is surjective.
- If  $f_4$  is surjective and  $f_3$  and  $f_1$  are injective, then  $f_2$  is injective.

Very commonly one knows that  $f_0$ ,  $f_1$ ,  $f_3$ , and  $f_4$  are all isomorphisms, and concludes that  $f_2$  is also an isomorphism. For example:

#### Corollary 9.5. Let

$$0 \longrightarrow A'_* \longrightarrow B'_* \longrightarrow C'_* \longrightarrow 0$$

$$\downarrow^f \qquad \downarrow^g \qquad \downarrow^h$$

$$0 \longrightarrow A_* \longrightarrow B_* \longrightarrow C_* \longrightarrow 0$$

be a map of short exact sequences of chain complexes. If two of the three maps induced in homology by f, g, and h are isomorphisms, then so is the third.

Here's an application.

**Proposition 9.6.** Let  $(A, X) \to (B, Y)$  be a map of pairs, and assume that two of  $A \to B$ ,  $X \to Y$ , and  $(X, A) \to (Y, B)$  induce isomorphims in homology. Then the third one does as well.

*Proof.* Just apply the five lemma to the map between the two homology long exact sequences.  $\Box$ 

## 10 Excision and applications

We have found two general properties of singular homology: homotopy invariance and the long exact sequence of a pair. We also claimed that  $H_*(X,A)$  "depends only on X-A." You have to be careful about this. The following definition gives conditions that will capture the sense in which the relative homology of a pair (X,A) depends only on the complement of A in X.

**Definition 10.1.** A triple (X, A, U) where  $U \subseteq A \subseteq X$ , is *excisive* if  $\overline{U} \subseteq \text{Int}(A)$ . The inclusion  $(X - U, A - U) \subseteq (X, A)$  is then called an *excision*.

**Theorem 10.2.** An excision induces an isomorphism in homology.

$$H_*(X-U,A-U) \xrightarrow{\cong} H_*(X,A)$$
.

So you can cut out closed bits of the interior of A without changing the relative homology. The proof will take us a couple of days. Before we give applications, let me pose a different way to interpret the motto " $H_*(X, A)$  depends only on X - A." Collapsing the subspace A to a point gives us a map of pairs

$$(X,A) \rightarrow (X/A,*)$$
.

When does this map induce an isomorphism in homology? Excision has the following consequence.

**Corollary 10.3.** Assume that there is a subspace B of X such that (1)  $\overline{A} \subseteq \text{Int}B$  and (2)  $A \to B$  is a deformation retract. Then

$$H_*(X,A) \to H_*(X/A,*)$$

is an isomorphism.

*Proof.* The diagram of pairs

$$(X,A) \xrightarrow{i} (X,B) \xleftarrow{j} (X-A,B-A)$$

$$\downarrow \qquad \qquad \downarrow k$$

$$(X/A,*) \xrightarrow{\bar{\imath}} (X/A,B/A) \xleftarrow{\bar{\jmath}} (X/A-*,B/A-*)$$

commutes. We want the left vertical to be a homology isomorphism, and will show that the rest of the perimeter consists of homology isomorphisms. The map k is a homeomorphism of pairs while j is an excision by assumption (1). The map i induces an isomorphism in homology by assumption (2), the long exact sequences, and the five-lemma. Since I is a compact Hausdorff space, the map  $B \times I \to B/A \times I$  is again a quotient map, so the deformation  $B \times I \to B$ , which restricts to the constant deformation on A, descends to show that  $* \to B/A$  is a deformation retract. So the map  $\bar{\imath}$  is also a homology isomorphism. Finally,  $\bar{\ast} \subseteq \operatorname{Int}(B/A)$  in X/A, by definition of the quotient topology, so  $\bar{\jmath}$  induces an isomorphism by excision.

Now what are some consequences? For a start, we'll finally get around to computing the homology of the sphere. It happens simultaneously with a computation of  $H_*(D^n, S^{n-1})$ . (Note that  $S^{-1} = \emptyset$ .) To describe generators, for each  $n \ge 0$  pick a homeomorphism

$$(\Delta^n, \partial \Delta^n) \to (D^n, S^{n-1}),$$

and write

$$\iota_n \in S_n(D^n, S^{n-1})$$

for the corresponding relative n-chain.

**Proposition 10.4.** Let n > 0 and let  $* \in S^{n-1}$  be any point. Then:

$$H_q(S^n) = \begin{cases} \mathbf{Z} = \langle [\partial \iota_{n+1}] \rangle & \text{if} \quad q = n > 0 \\ \mathbf{Z} = \langle [c_*^0] \rangle & \text{if} \quad q = 0, n > 0 \\ \mathbf{Z} \oplus \mathbf{Z} = \langle [c_*^0], [\partial \iota_1] \rangle & \text{if} \quad q = n = 0 \\ 0 & \text{otherwise} \end{cases}$$

and

$$H_q(D^n, S^{n-1}) = \begin{cases} \mathbf{Z} = \langle [\iota_n] \rangle & if \quad q = n \\ 0 & otherwise. \end{cases}$$

*Proof.* The division into cases for  $H_q(S^n)$  can be eased by employing reduced homology. Then the claim is merely that for  $n \geq 0$ 

$$\widetilde{H}_q(S^{n-1}) = \begin{cases} \mathbf{Z} & \text{if} \quad q = n-1\\ 0 & \text{if} \quad q \neq n-1 \end{cases}$$

and the map

$$\partial: H_q(D^n, S^{n-1}) \to \widetilde{H}_{q-1}(S^{n-1})$$

is an isomorphism. The second statement follows from the long exact sequence in reduced homology together with the fact that  $\widetilde{H}_*(D^n) = 0$  since  $D^n$  is contractible. The first uses induction and the pair of isomorphisms

$$\widetilde{H}_{q-1}(S^{n-1}) \stackrel{\cong}{\longleftarrow} H_q(D^n, S^{n-1}) \stackrel{\cong}{\longrightarrow} H_q(D^n/S^{n-1}, *)$$

since  $D^n/S^{n-1} \cong S^n$ . The right hand arrow is an isomorphism since  $S^{n-1}$  is a deformation retract of a neighborhood in  $D^n$ .

Why should you care about this complicated homology calculation?

Corollary 10.5. If  $m \neq n$ , then  $S^m$  and  $S^n$  are not homotopy equivalent.

*Proof.* Their homology groups are not isomorphic.

Corollary 10.6. If  $m \neq n$ , then  $\mathbb{R}^m$  and  $\mathbb{R}^n$  are not homeomorphic.

*Proof.* If m or n is zero, this is clear, so let m, n > 0. Assume we have a homeomorphism  $f: \mathbf{R}^m \to \mathbf{R}^n$ . This restricts to a homeomorphism  $\mathbf{R}^m - \{0\} \to \mathbf{R}^n - \{f(0)\}$ . But these spaces are homotopy equivalent to spheres of different dimension.

**Theorem 10.7** (Brouwer fixed-point theorem). If  $f: D^n \to D^n$  is continuous, then there is some point  $x \in D^n$  such that f(x) = x.

Proof. Suppose not. Then you can draw a ray from f(x) through x. It meets the boundary of  $D^n$  at a point  $g(x) \in S^{n-1}$ . Check that  $g: D^n \to S^{n-1}$  is continuous. If x is on the boundary, then x = g(x), so g provides a factorization of the identity map on  $S^{n-1}$  through  $D^n$ . This is inconsistent with our computation because the identity map induces the identity map on  $\widetilde{H}_{n-1}(S^{n-1}) \cong \mathbb{Z}$ , while  $\widetilde{H}_{n-1}(D^n) = 0$ .

Our computation of the homology of a sphere also implies that there are many non-homotopic self-maps of  $S^n$ , for any  $n \geq 1$ . We will distinguish them by means of the "degree": A map  $f: S^n \to S^n$  induces an endomorphism of the infinite cyclic group  $H_n(S^n)$ . Any endomorphism of an infinite cyclic group is given by multiplication by an integer. This integer is well defined (independent of a choice of basis), and any integer occurs. Thus  $\operatorname{End}(\mathbf{Z}) = \mathbf{Z}_{\times}$ , the monoid of integers under multiplication. The homotopy classes of self-maps of  $S^n$  also form a monoid, under composition, and:

**Theorem 10.8.** Let  $n \geq 1$ . The degree map provides us with a surjective monoid homomorphism

$$\deg: [S^n, S^n] \to \mathbf{Z}_{\times}$$
.

*Proof.* Degree is multiplicative by functoriality of homology.

We construct a map of degree k on  $S^n$  by induction on n. If n = 1, this is just the winding number; an example is given by regarding  $S^1$  as unit complex numbers and sending z to  $z^k$ . The proof that this has degree k is an exercise.

Suppose we've constructed a map  $f_k: S^{n-1} \to S^{n-1}$  of degree k. Extend it to a map  $\overline{f}_k: D^n \to D^n$  by defining  $\overline{f}_k(tx) = tf_k(x)$  for  $t \in [0,1]$ . We may then collapse the sphere to a point and identify the quotient with  $S^n$ . This gives us a new map  $g_k: S^n \to S^n$  making the diagram below commute.

$$H_{n-1}(S^{n-1}) \stackrel{\cong}{\longleftarrow} H_n(D^n, S^{n-1}) \stackrel{\cong}{\longrightarrow} H_n(S^n)$$

$$\downarrow^{f_{k*}} \qquad \qquad \downarrow^{g_{k*}}$$

$$H_{n-1}(S^{n-1}) \stackrel{\cong}{\longleftarrow} H_n(D^n, S^{n-1}) \stackrel{\cong}{\longrightarrow} H_n(S^n)$$

The horizontal maps are isomorphisms, so deg  $g_k = k$  as well.

We will see (in 18.906) that this map is in fact an isomorphism.

## 11 The Eilenberg Steenrod axioms and the locality principle

Before we proceed to prove the excision theorem, let's review the properties of singular homology as we have developed them. They are captured by a set of axioms, due to Sammy Eilenberg and Norman Steenrod [5].

**Definition 11.1.** A homology theory (on **Top**) is:

- a sequence of functors  $h_n : \mathbf{Top}_2 \to \mathbf{Ab}$  for all  $n \in \mathbf{Z}$  and
- a sequence of natural transformations  $\partial: h_n(X,A) \to h_{n-1}(A,\varnothing)$

such that:

- If  $f_0, f_1: (X, A) \to (Y, B)$  are homotopic, then  $f_{0*} = f_{1*}: h_n(X, A) \to h_n(Y, B)$ .
- Excisions induce isomorphisms.
- For any pair (X, A), the sequence

$$\cdots \to h_{q+1}(X,A) \xrightarrow{\partial} h_q(A) \to h_q(X) \to h_q(X,A) \xrightarrow{\partial} \cdots$$

is exact, where we have written  $h_q(X)$  for  $h_q(X,\varnothing)$ .

• (The dimension axiom): The group  $h_n(*)$  is nonzero only for n=0.

We add the following "Milnor axiom" [8] to our definition. To state it, let I be a set and suppose that for each  $i \in I$  we have a space  $X_i$ . We can form their disjoint union or *coproduct*  $\coprod X_i$ . The inclusion maps  $X_i \to \coprod X_i$  induce maps  $h_n(X_i) \to h_n(\coprod X_i)$ , and these in turn induce a map from the direct sum, or coproduct in  $\mathbf{Ab}$ :

$$\alpha: \bigoplus_{i \in I} h_n(X_i) \to h_n \left( \coprod_{i \in I} X_i \right) .$$

Then:

• The map  $\alpha$  is an isomorphism for all n.

Ordinary singular homology satisfies these, with  $h_0(*) = \mathbf{Z}$ . We will soon add "coefficients" to homology, producing a homology theory whose value on a point is any prescribed abelian group. In later developments, it emerges that the dimension axiom is rather like the parallel postulate in Euclidean geometry: it's "obvious," but, as it turns out, the remaining axioms accommodate extremely interesting alternatives, in which  $h_n(*)$  is nonzero for infinitely many values of n (both positive and negative).

Excision is a statement that homology is "localizable." To make this precise, we need some definitions.

**Definition 11.2.** Let X be a topological space. A family  $\mathcal{A}$  of subsets of X is a *cover* if X is the union of the interiors of elements of  $\mathcal{A}$ .

**Definition 11.3.** Let  $\mathcal{A}$  be a cover of X. An n-simplex  $\sigma$  is  $\mathcal{A}$ -small if there is  $A \in \mathcal{A}$  such that the image of  $\sigma$  is entirely in A.

Notice that if  $\sigma: \Delta^n \to X$  is  $\mathcal{A}$ -small, then so is  $d_i\sigma$ ; in fact, for any simplicial operator  $\phi$ ,  $\phi^*\sigma$  is again  $\mathcal{A}$ -small. Let's denote by  $\operatorname{Sin}_*^{\mathcal{A}}(X)$  the graded set of  $\mathcal{A}$ -small simplices. This us a sub-simplicial set of  $\operatorname{Sin}_*(X)$ . Applying the free abelian group functor, we get the subcomplex

$$S_*^{\mathcal{A}}(X)$$

of A-small singular chains. Write  $H_*^{\mathcal{A}}(X)$  for its homology.

**Theorem 11.4** (The locality principle). The inclusion  $S_*^{\mathcal{A}}(X) \subseteq S_*(X)$  induces an isomorphism in homology,  $H_*^{\mathcal{A}}(X) \stackrel{\cong}{\to} H_*(X)$ .

This will take a little time to prove. Let's see right now how it implies excision.

Suppose  $X \supset A \supset U$  is excisive, so that  $\overline{U} \subseteq \text{Int}A$ , or  $\text{Int}(X - U) \cup \text{Int}A = X$ . This if we let B = X - U, then  $A = \{A, B\}$  is a cover of X. Rewriting in terms of B,

$$(X-U,A-U)=(B,A\cap B),$$

so we aim to show that

$$S_*(B, A \cap B) \to S_*(X, A)$$

induces an isomorphism in homology. We have the following diagram of chain complexes with exact rows:

$$0 \longrightarrow S_*(A) \longrightarrow S_*^{\mathcal{A}}(X) \longrightarrow S_*^{\mathcal{A}}(X)/S_*(A) \longrightarrow 0$$

$$\downarrow = \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$0 \longrightarrow S_*(A) \longrightarrow S_*(X) \longrightarrow S_*(X,A) \longrightarrow 0$$

The middle vertical induces an isomorphism in homology by the locality principle, so the homology long exact sequences combine with the five-lemma to show that the right hand vertical is also a homology isomorphism. But

$$S_n^{\mathcal{A}}(X) = S_n(A) + S_n(B) \subseteq S_n(X)$$

and a simple result about abelian groups provides an isomorphism

$$\frac{S_n(B)}{S_n(A \cap B)} = \frac{S_n(B)}{S_n(A) \cap S_n(B)} \xrightarrow{\cong} \frac{S_n(A) + S_n(B)}{S_n(A)} = \frac{S_n^{\mathcal{A}}(X)}{S_n(A)},$$

so excision follows.

This case of a cover with two elements leads to another expression of excision, known as the "Mayer-Vietoris sequence." In describing it we will use the following notation for the various inclusion.

$$\begin{array}{ccc}
A \cap B \xrightarrow{j_1} & A \\
\downarrow j_2 & & \downarrow i_1 \\
B \xrightarrow{j_2} & X
\end{array}$$

**Theorem 11.5** (Mayer-Vietoris). Assume that  $\mathcal{A} = \{A, B\}$  is a cover of X. There are natural maps  $\partial: H_n(X) \to H_{n-1}(A \cap B)$  such that the sequence

$$H_n(A \cap B) \xrightarrow{\alpha} H_n(A) \oplus H_n(B) \xrightarrow{\beta} H_n(X)$$

$$H_{n-1}(A \cap B) \xrightarrow{\alpha} H_n(A) \oplus H_n(B) \xrightarrow{\beta} H_n(X)$$

is exact, where

$$\alpha = \begin{bmatrix} j_{1*} \\ -j_{2*} \end{bmatrix}, \quad \beta = \begin{bmatrix} i_{1*} & i_{2*} \end{bmatrix}.$$

*Proof.* This is the homology long exact sequence associated to the short exact sequence of chain complexes

$$0 \to S_*(A \cap B) \xrightarrow{\alpha} S_*(A) \oplus S_*(B) \xrightarrow{\beta} S_*^{\mathcal{A}}(X) \to 0$$

combined with the locality principle.

The Mayer-Vietoris theorem follows from excision as well, via the following simple observation. Suppose we have a map of long exact sequences

$$\cdots \longrightarrow C'_{n+1} \xrightarrow{k} A'_n \longrightarrow B'_n \longrightarrow C'_n \longrightarrow \cdots$$

$$\downarrow h \qquad \qquad \downarrow f \qquad \qquad \downarrow h$$

$$\cdots \longrightarrow C_{n+1} \xrightarrow{k} A_n \longrightarrow B_n \longrightarrow C_n \longrightarrow \cdots$$

in which every third arrow is an isomorphism as indicated. Define a map

$$\partial: A_n \to B_n \stackrel{\cong}{\leftarrow} B'_n \to C'_n$$
.

An easy diagram chase shows:

Lemma 11.6. The sequence

$$\cdots \longrightarrow C'_{n+1} \xrightarrow{\begin{bmatrix} h \\ -k \end{bmatrix}} C_{n+1} \oplus A'_n \xrightarrow{\begin{bmatrix} k & f \end{bmatrix}} A_n \xrightarrow{\partial} C'_n \longrightarrow \cdots$$

is exact.

To get the Mayer-Vietoris sequence, let  $\{A, B\}$  be a cover of X and apply the lemma to

$$\cdots \longrightarrow H_n(A \cap B) \longrightarrow H_n(B) \longrightarrow H_n(B, A \cap B) \longrightarrow H_{n-1}(A \cap B) \longrightarrow H_{n-1}(B) \longrightarrow \cdots$$

$$\downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$\cdots \longrightarrow H_n(A) \longrightarrow H_n(X) \longrightarrow H_n(X, A) \longrightarrow H_{n-1}(A) \longrightarrow H_{n-1}(X) \longrightarrow \cdots$$

#### 12 Subdivision

We will begin the proof of the locality principle today, and finish it in the next lecture. The key is a process of subdivision of singular simplices. It will use the "cone construction" b\* from Lecture 5. The cone construction dealt with a region X in Euclidean space, star-shaped with respect to  $b \in X$ , and gave a chain-homotopy between the identity and the "constant map" on  $S_*(X)$ :

$$db*+b*d=1-n\epsilon$$

where  $\epsilon: S_*(X) \to \mathbf{Z}$  is the augmentation and  $\eta: \mathbf{Z} \to S_*(X)$  sends 1 to the constant 0-chain  $c_b^0$ . Let's see how the cone construction can be used to "subdivide" an "affine simplex." An affine simplex is the convex hull of a finite set of points in Euclidean space. To make this non-degenerate, assume that the points  $v_0, v_1, \ldots, v_n$ , have the property that  $\{v_1 - v_0, \ldots, v_n - b_0\}$  is linearly independent. The barycenter of this simplex is the center of mass of the vertices,

$$b = \frac{1}{n+1} \sum v_i.$$

Start with n = 1. To subdivide a 1-simplex, just cut it in half. For the 2-simplex, look at the subdivision of each face, and form the cone of them with the barycenter of the 2-simplex. This gives us a decomposition of the 2-simplex into six sub-simplices.

12. SUBDIVISION 29

We want to formalize this process, and extend it to singular simplices (using naturality, of course). Define a natural transformation

$$\$: S_n(X) \to S_n(X)$$

by defining it on standard *n*-simplex, namely by specifying what  $\$(\iota_n)$  is where  $\iota_n : \Delta^n \to \Delta^n$  is the universal *n*-simplex, and then extending by naturality:

$$\$(\sigma) = \sigma_* \$(\iota_n) .$$

Here's the definition. When n=0, define \$ to be the identity; i.e.,  $\mathfrak{s}\iota_0=\iota_0$ . For n>0, define

$$\$\iota_n := b_n * \$d\iota_n$$

where  $b_n$  is the barycenter of  $\Delta^n$ . This makes a lot of sense if you draw out a picture, and it's a very clever definition that captures the geometry we described.

The dollar sign symbol is a little odd, but consider: it derives from the symbol for the Spanish piece of eight, which was meant to be subdivided (so for example two bits is a quarter).

Here's what we'll prove.

**Proposition 12.1.** \$\\$ is a natural chain map  $S_*(X) \to S_*(X)$  that is naturally chain-homotopic to the identity.

*Proof.* Let's begin by proving that it's a chain map. We'll use induction on n. It's enough to show that  $d \mathfrak{s} \iota_n = \mathfrak{s} d \iota_n$ , because then, for any n-simplex  $\sigma$ ,

$$d\$\sigma = d\$\sigma_*\iota_n = \sigma_*d\$\iota_n = \sigma_*\$d\iota_n = \$d\sigma_*\iota_n = \$d\sigma.$$

Dimension zero is easy: since  $S_{-1} = 0$ ,  $d$\iota_0$  and  $$d\iota_0$  are both zero and hence equal. For  $n \ge 1$ , we want to compute  $d$\iota_n$ . This is:

$$d\$\iota_n = d(b_n * \$d\iota_n)$$
  
=  $(1 - \eta_b \epsilon - b_n * d)(\$d\iota_n)$ 

What happens when n = 1? Well,

$$\eta_b \epsilon \$ d\iota_1 = \eta_b \epsilon \$ (c_1^0 - c_0^0) = \eta_b \epsilon (c_1^0 - c_0^0) = 0,$$

since  $\epsilon$  takes sums of coefficients. So the  $\eta_b \epsilon$  term drops out for any  $n \geq 1$ . Let's continue, using the inductive hypothesis:

$$d\$\iota_n = (1 - b_n * d)(\$d\iota_n)$$

$$= \$d\iota_n - b_n * d\$d\iota_n$$

$$= \$d\iota_n - b_n\$d^2\iota_n$$

$$= \$d\iota_n$$

because  $d^2 = 0$ .

To define the chain homotopy T, we'll just write down a formula and not try to justify it. Making use of naturality, we just need to define  $T\iota_n$ . Here it is:

$$T\iota_n = b_n * (\$\iota_n - \iota_n - Td\iota_n) \in S_{n+1}(\Delta^n).$$

Once again, we're going to check that T is a chain homotopy by induction, and, again, we need to check only on the universal case.

When n = 0, the formula gives  $T\iota_0 = 0$  (which starts the inductive definition!) so it's true that  $dT\iota_0 - Td\iota_0 = \$\iota_0 - \iota_0$ . Now let's assume that dTc - Tdc = \$c - c for every (n - 1)-chain c. Let's start by computing  $dT\iota_n$ :

$$dT\iota_n = d_n(b_n * (\$\iota_n - \iota_n - Td\iota_n))$$

$$= (1 - b_n * d)(\$\iota_n - \iota_n - Td\iota_n)$$

$$= \$\iota_n - \iota_n - Td\iota_n - b_n * (d\$\iota_n - d\iota_n - dTd\iota_n)$$

All we want now is that  $b_n * (d \mathfrak{s} \iota_n - d \iota_n - d T d \iota_n) = 0$ . We can do this using the inductive hypothesis, because  $d \iota_n$  is in dimension n-1.

$$dTd\iota_n = -Td(d\iota_n) + \$d\iota_n - d\iota_n$$
$$= \$d\iota_n - d\iota_n$$
$$= d\$\iota_n - d\iota_n.$$

This means that  $d \iota_n - d \iota_n - d T d \iota_n = 0$ , so T is indeed a chain homotopy.

## 13 Proof of the Locality Principle

We have constructed the subdivision operator  $S: S_*(X) \to S_*(X)$ , with the idea that it will shrink chains and by iteration eventually render any chain A-small. Does S succeed in making simplices smaller? Let's look first at the affine case. Recall that the "diameter" of a subset S of a metric space is given by

$$diam(X) = \sup\{d(x, y) : x, y \in X\}.$$

**Lemma 13.1.** Let  $\sigma$  be an affine n-simplex, and  $\tau$  a simplex in  $\$\sigma$ . Then  $\operatorname{diam}(\tau) \leq \frac{n}{n+1}\operatorname{diam}(\sigma)$ .

*Proof.* Suppose that the vertices of  $\sigma$  are  $v_0, v_1, \ldots, v_n$ . Let b be the barycenter of  $\sigma$ , and write the vertices of  $\tau$  as  $w_0 = b, w_1, \ldots, w_n$ . We want to estimate  $|w_i - w_j|$ . First, compute

$$|b - v_i| = \left| \frac{v_0 + \dots + v_n - (n+1)v_i}{n+1} \right| = \left| \frac{(v_0 - v_i) + (v_1 - v_i) + \dots + (v_n - v_i)}{n+1} \right|.$$

One of the terms in the numerator is zero, so we can continue:

$$|b - v_i| \le \frac{n}{n+1} \max_{i,j} |v_i - v_j| = \frac{n}{n+1} \operatorname{diam}(\sigma)$$

Since  $w_i \in \sigma$ ,

$$|b - w_i| \le \max_i |b - v_i| \le \frac{n}{n+1} \operatorname{diam}(\sigma)$$
.

For the other cases, we use induction:

$$|w_i - w_j| \le \operatorname{diam}(\operatorname{simplex in } d\sigma) \le \frac{n-1}{n} \operatorname{diam}(d\sigma) \le \frac{n}{n+1} \operatorname{diam}(\sigma).$$

Now let's transfer this calculation to singular simplices in a space X equipped with a cover A.

**Lemma 13.2.** For any singular chain c, some iterate of the subdivision operator sends c to an A-small chain.

*Proof.* We may assume that c is a single simplex  $\sigma: \Delta^n \to X$ , because in general you just take the largest of the iterates of \$ needed to send the simplices in c to a A-small chains. We now encounter another of the great virtues of singular homology: we pull A back to a cover of the standard simplex. Define an open cover of  $\Delta^n$  by

$$\mathcal{U} := \{ \sigma^{-1}(\operatorname{Int}(A)) : A \in \mathcal{A} \}.$$

The space  $\Delta^n$  is a compact metric space, and so is subject to the Lebesgue covering lemma, which we apply to the open cover  $\mathcal{U}$ .

**Lemma 13.3** (Lebesgue covering lemma). Let M be a compact metric space, and let  $\mathcal{U}$  be an open cover. Then there is  $\epsilon > 0$  such that for all  $x \in M$ ,  $B_{\epsilon}(x) \subseteq U$  for some  $U \in \mathcal{U}$ .

To apply this, we will have to understand iterates of the subdivision operator.

**Lemma 13.4.** For any  $k \ge 1$ ,  $\$^k \simeq 1 : S_*(X) \to S_*(X)$ .

*Proof.* We construct  $T_k$  such that  $dT_k + T_k d = \$^k - 1$ . To begin, we take  $T_1 = T$ , since dT + Td = \$ - 1. Let's apply \$ to this equation. We get  $\$dT + \$Td = \$^2 - \$$ . Sum up these two equations to get

$$dT + Td + \$dT + \$Td = \$^2 - 1$$
,

which simplifies to

$$d(\$+1)T + (\$+1)Td = \$^2 - 1$$

since d = d.

So define  $T_2 = (\$ + 1)T$ . Continuing, you see that we can define

$$T_k = (\$^{k-1} + \$^{k-2} + \dots + 1)T.$$

We are now in position to prove the Locality Principle, which we recall:

**Theorem 13.5** (The locality principle). Let  $\mathcal{A}$  be a cover of a space X. The inclusion  $S_*^{\mathcal{A}}(X) \subseteq S_*(X)$  is a quasi-isomorphism; that is,  $H_*^{\mathcal{A}}(X) \to H_*(X)$  is an isomorphism.

*Proof.* To prove surjectivity let c be an n-cycle in X. We want to find an A-small n-cycle that is homologous to c. There's only one thing to do. Pick k such that k c is A-small. This is a cycle because because k is a chain map. I want to compare this new cycle with c. That's what the chain homotopy  $T_k$  is designed for:

$$\$^k c - c = dT_k c + T_k dc = dT_k c$$

since c is a cycle. So  $\$^k c$  and c are homologous.

Now for injectivity. Suppose c is a cycle in  $S_n^{\mathcal{A}}(X)$  such that c = db for some  $b \in S_{n+1}(X)$ . We want c to be a boundary of an  $\mathcal{A}$ -small chain. Use the chain homotopy  $T_k$  again: Suppose that k is such that  $\$^k c$  is  $\mathcal{A}$ -small. Compute:

$$d\$^k b - c = d(\$^k - 1)b = d(dT_k + T_k d)b = dT_k c$$

so

$$c = d\$^k b - dT_k c = d(\$^k b - T_k c).$$

Now,  $\$^k b$  is  $\mathcal{A}$ -small, by choice of k. Is  $T_k c$  also  $\mathcal{A}$ -small? I claim that it is. Why? It is enough to show that  $T_k \sigma$  is  $\mathcal{A}$ -small if  $\sigma$  is. We know that  $\sigma = \sigma_* \iota_n$ . Because  $\sigma$  is  $\mathcal{A}$ -small, we know that  $\sigma : \Delta^n \to X$  is the composition  $i_*\overline{\sigma}$  where  $\overline{\sigma} : \Delta^n \to A$  and  $i : A \to X$  is the inclusion of some  $A \in \mathcal{A}$ . By naturality, then,  $T_k \sigma = T_k i_* \overline{\sigma} = i_* T_k \overline{\sigma}$ , which certainly is  $\mathcal{A}$ -small.

This completes the proof of the Eilenberg Steenrod axioms for singular homology. In the next chapter, we will develop a variety of practical tools, using these axioms to compute the singular homology of many spaces.

# Lefschetz progeny

According to the Mathematical Genealogy Project, Solomon Lefschetz had 9312 academic descendents as of March 2018. Here are just a few, with special attention to MIT faculty (marked with an asterisk).

# Chapter 2

# Computational methods

#### 14 CW-complexes

There are various ways to model geometrically interesting spaces. Manifolds provide one important model, well suited to analysis. Another model, one we have not talked about, is given by simplicial complexes. It's very combinatorial, and constructing a simplicial complex model for a given space involves making a lot of choices that are combinatorial rather than topological in character. A more flexible model, one more closely reflecting topological information, is given by the theory of CW-complexes.

In building up a space as a CW-complex, we will successively "glue" cells onto what has been already built. This is a general construction.

Suppose we have a pair (B, A), and a map  $f : A \to X$ . Define a space  $X \cup_f B$  (or  $X \cup_A B$ ) in the diagram

$$\begin{array}{ccc}
A & \xrightarrow{f} & X \\
\downarrow & & \downarrow \\
B & \longrightarrow X \cup_{f} B
\end{array}$$

by

$$X \cup_f B = X \sqcup B / \sim$$

where the equivalence relation is generated by requiring that  $a \sim f(a)$  for all  $a \in A$ . We say that we have "attached B to X along f (or along A)."

There are two kinds of equivalence classes in  $X \cup_f B$ : (1) singletons containing elements of B - A, and (2)  $\{x\} \sqcup f^{-1}(x)$  for  $x \in X$ . The topology on  $X \cup_f B$  is the quotient topology, and is characterized by a universal property: any solid-arrow commutative diagram

can be uniquely filled in. It's a "push-out."

**Example 14.1.** If X = \*, then  $* \cup_f B = B/A$ .

**Example 14.2.** If  $A = \emptyset$ , then  $X \cup_f B$  is the coproduct  $X \sqcup B$ .

Example 14.3. If both,

$$B/\varnothing = * \cup_\varnothing B = * \sqcup B.$$

For example,  $\emptyset/\emptyset = *$ . This is creation from nothing. We won't get into the religious ramifications.

**Example 14.4** (Attaching a cell). A basic collection of pairs of spaces is given by the disks relative to their boundaries:  $(D^n, S^{n-1})$ . (Recall that  $S^{-1} = \emptyset$ .) In this context,  $D^n$  is called an "n-cell," and a map  $f: S^{n-1} \to X$  allows us to attach an n-cell to X, to form

$$S^{n-1} \xrightarrow{f} X$$

$$\downarrow \qquad \qquad \downarrow$$

$$D^n \longrightarrow X \cup_f D^r$$

You might want to generalize this a little bit, and attach a bunch of n-cells all at once:

$$\coprod_{\alpha \in A} S_{\alpha}^{n-1} \xrightarrow{f} X$$

$$\downarrow \qquad \qquad \downarrow$$

$$\coprod_{\alpha \in A} D_{\alpha}^{n} \xrightarrow{} X \cup_{f} \coprod_{\alpha \in A} D_{\alpha}^{n}$$

What are some examples? When n = 0,  $(D^0, S^{-1}) = (*, \emptyset)$ , so you are just adding a discrete set to X:

$$X \cup_f \coprod_{\alpha \in A} D^0 = X \sqcup A$$

More interesting: Let's attach two 1-cells to a point:

$$S^{0} \sqcup S^{0} \xrightarrow{f} *$$

$$\downarrow \qquad \qquad \downarrow$$

$$D^{1} \sqcup D^{1} \longrightarrow * \cup_{f} (D^{1} \sqcup D^{1})$$

Again there's just one choice for f, and  $* \cup_f (D^1 \sqcup D^1)$  is a figure 8, because you start with two 1-disks and identify the four boundary points together. Let me write  $S^1 \vee S^1$  for this space. We can go on and attach a single 2-cell to manufacture a torus. Think of the figure 8 as the perimeter of a square with opposite sides identified.

14. CW-COMPLEXES 37

The inside of the square is a 2-cell, attached to the perimeter by a map I'll denote by  $aba^{-1}b^{-1}$ :

$$S^{1} \xrightarrow{aba^{-1}b^{-1}} S^{1} \vee S^{1}$$

$$\downarrow \qquad \qquad \downarrow$$

$$D^{2} \longrightarrow (S^{1} \vee S^{1}) \cup_{f} D^{2} = T^{2}.$$

This example illuminates the following definition.

**Definition 14.5.** A CW-complex is a space X equipped with a sequence of subspaces

$$\emptyset = \operatorname{Sk}_{-1} X \subseteq \operatorname{Sk}_0 X \subseteq \operatorname{Sk}_1 X \subseteq \cdots \subseteq X$$

such that

- X is the union of the  $Sk_nX$ 's, and
- for all n, there is a pushout diagram like this:

$$\coprod_{\alpha \in A_n} S_{\alpha}^{n-1} \xrightarrow{f_n} \operatorname{Sk}_{n-1} X .$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$\coprod_{\alpha \in A_n} D_{\alpha}^n \xrightarrow{g_n} \operatorname{Sk}_n X$$

The subspace  $\operatorname{Sk}_n X$  is the *n*-skeleton of X. Sometimes it's convenent to use the alternate notation  $X_n$  for the *n*-skeleton. The first condition is intended topologically, so that a subset of X is open if and only if its intersection with each  $\operatorname{Sk}_n X$  is open; or, equivalently, a map  $f: X \to Y$  is continuous if and only if its restriction to each  $\operatorname{Sk}_n X$  is continuous. The maps  $f_n$  are the attaching maps and the maps  $g_n$  are characteristic maps.

**Example 14.6.** We just constructed the torus as a CW complex with  $Sk_0T^2 = *$ ,  $Sk_1T^2 = S^1 \vee S^1$ , and  $Sk_2T^2 = T^2$ .

**Definition 14.7.** A CW-complex is *finite-dimensional* if  $Sk_nX = X$  for some n; of *finite type* if each  $A_n$  is finite, i.e., finitely many cell in each dimension; and *finite* if it's finite-dimensional and of finite type.

The dimension of a CW complex is the largest n for which there are n-cells. This is not obviously a topological invariant, but, have no fear, it turns out that it is.

In "CW," the "C" is for cell, and the "W" is for weak, because of the topology on a CW-complex. This definition is due to J. H. C. Whitehead. Here are a couple of important facts about them.

**Theorem 14.8.** Any CW-complex is Hausdorff, and it's compact if and only if it's finite. Any compact smooth manifold admits a CW structure.

*Proof.* See [2] Prop. IV.8.1, [6] Prop. A.3.

#### 15 CW-complexes II

We have a few more general things to say about CW complexes.

Suppose X is a CW complex, with skeleton filtration  $\emptyset = X_{-1} \subseteq X_0 \subseteq X_1 \subseteq \cdots \subseteq X$  and cell structure

$$\coprod_{\alpha \in A_n} S_{\alpha}^{n-1} \xrightarrow{f_n} X_{n-1} .$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$\coprod_{\alpha \in A_n} D_{\alpha}^n \xrightarrow{g_n} X_n$$

In each case, the boundary of a cell gets identified with part of the previous skeleton, but the "interior"

$$Int D^n = \{x \in D^n : |x| < 1\}$$

does not. (Note that  $Int D^0 = D^0$ .) Thus as sets – ignoring the topology –

$$X = \coprod_{n>0} \coprod_{\alpha \in A_n} \operatorname{Int}(D_{\alpha}^n).$$

The subsets  $\operatorname{Int} D_{\alpha}^{n}$  are called "open *n*-cells," despite the fact that they not generally open in the topology on X, and (except when n=0) they are not homeomorphic to compact disks.

**Definition 15.1.** Let X be a CW-complex with a cell structure  $\{g_{\alpha}: D_{\alpha}^n \to X_n : \alpha \in A_n, n \geq 0\}$ . A subcomplex is a subspace  $Y \subseteq X$  such that for all n, there is a subset  $B_n$  of  $A_n$  such that  $Y_n = Y \cap X_n$  provides Y with a CW-structure with characteristic maps  $\{g_{\beta}: \beta \in B_n, n \geq 0\}$ .

**Example 15.2.**  $\operatorname{Sk}_n X \subseteq X$  is a subcomplex.

**Proposition 15.3.** Let X be a CW-complex with a chosen cell structure. Any compact subspace of X lies in some finite subcomplex.

Remark 15.4. For fixed cell structures, unions and intersections of subcomplexes are subcomplexes.

The *n*-sphere  $S^n$  (for n > 0) admits a very simple CW structure: Let  $* = \operatorname{Sk}_0(S^n) = \operatorname{Sk}_1(S^n) = \cdots = \operatorname{Sk}_{n-1}(S^n)$ , and attach an *n*-cell using the unique map  $S^{n-1} \to *$ . This is a minimal CW structure – you need at least two cells to build  $S^n$ .

This is great – much simpler than the simplest construction of  $S^n$  as a simplicial complex – but it is not ideal for all applications. Here's another CW-structure on  $S^n$ . Regard  $S^n \subseteq \mathbf{R}^{n+1}$ , filter the Euclidean space by leading subspaces

$$\mathbf{R}^k = \langle e_1, \dots, e_k \rangle$$
.

and define

$$\operatorname{Sk}_k S^n = S^n \cap \mathbf{R}^{k+1} = S^k$$
.

Now there are two k-cells for each k with  $0 \le k \le n$ , given by the two hemispheres of  $S^k$ . For each k there are two characteristic maps,

$$u, \ell: D^k \to S^k$$

defining the upper and lower hemispheres:

$$u(x) = (x, \sqrt{1 - |x|^2}), \quad \ell(x) = (x, -\sqrt{1 - |x|^2}).$$

Note that if |x| = 1 then  $|u(x)| = |\ell(x)| = 1$ , so each characteristic map restricts on the boundary to a map to  $S^{k-1}$ , and serves as an attaching map. This cell structure has the advantage that  $S^{n-1}$  is a subcomplex of  $S^n$ .

The case  $n = \infty$  is allowed here. Then  $\mathbf{R}^{\infty}$  denotes the countably infinite dimensional inner product space that is the topological union of the leading subspaces  $\mathbf{R}^n$ . The CW-complex  $S^{\infty}$  is of finite type but not finite dimensional. It has the following interesting property. We know that  $S^n$  is not contractible (because the identity map and a constant map have different behavior in homology), but:

#### **Proposition 15.5.** $S^{\infty}$ is contractible.

*Proof.* This is an example of a "swindle," making use of infinite dimensionality. Let  $T: \mathbf{R}^{\infty} \to \mathbf{R}^{\infty}$  send  $(x_1, x_2, \ldots)$  to  $(0, x_1, x_2, \ldots)$ . This sends  $S^{\infty}$  to itself. The location of the leading nonzero entry is different for x and Tx, so the line segment joining x to Tx doesn't pass through the origin. Therefore

$$x \mapsto \frac{tx + (1-t)Tx}{|tx + (1-t)Tx|}$$

provides a homotopy  $1 \simeq T$ . On the other hand, T is homotopic to the constant map with value  $(1,0,0,\ldots)$ , again by an affine homotopy.

This "inefficient" CW structure on  $S^n$  has a second advantage: it's equivariant with respect to the antipodal involution. This provides us with a CW structure on the orbit space for this action.

Recall that  $\mathbf{RP}^k = S^k / \sim$  where  $x \sim -x$ . The quotient map  $\pi : S^k \to \mathbf{RP}^k$  is a double cover, identifying upper and lower hemispheres. The inclusion of one sphere in the next is compatible with this equivalence relation, and gives us "linear" embeddings  $\mathbf{RP}^{k-1} \subseteq \mathbf{RP}^k$ . This suggests that

$$\varnothing \subseteq \mathbf{RP}^0 \subseteq \mathbf{RP}^1 \subseteq \dots \subseteq \mathbf{RP}^n$$

might serve as a CW filtration. Indeed, for each k,

$$S^{k-1} \longrightarrow D^k$$

$$\downarrow^{\pi} \qquad \qquad \downarrow^{u}$$

$$\mathbf{RP}^{k-1} \longrightarrow \mathbf{RP}^k$$

is a pushout: A line in  $\mathbf{R}^{k+1}$  either lies in  $\mathbf{R}^k$  or is determined by a unique point in the upper hemisphere of  $S^k$ .

#### 16 Homology of CW-complexes

The skeleton filtration of a CW complex leads to a long exact sequence in homology, showing that the relative homology  $H_*(X_k, X_{k-1})$  controls how the homology changes when you pass from  $X_{k-1}$  to  $X_k$ . What is this relative homology? If we pick a set of attaching maps, we get the following diagram.

$$\coprod_{\alpha} S^{k-1} \longrightarrow \coprod_{\alpha} D_{\alpha}^{k} \longrightarrow \bigvee_{\alpha} S_{\alpha}^{k} \\
\downarrow^{f} \qquad \qquad \downarrow^{q} \\
X_{k-1} \longrightarrow X_{k} \cup_{f} B \longrightarrow X_{k}/X_{k-1}$$

where  $\bigvee$  is the wedge sum (disjoint union with all basepoints identified):  $\bigvee_{\alpha} S_{\alpha}^{k}$  is a bouquet of spheres. The dotted map exists and is easily seen to be a homeomorphism.

Luckily, the inclusion  $X_{k-1} \subseteq X_k$  satisfies what's needed to conclude that

$$H_q(X_k, X_{k-1}) \to H_q(X_k/X_{k-1}, *)$$

is an isomorphism. After all,  $X_{k-1}$  is a deformation retract of the space you get from  $X_k$  by deleting the center of each k-cell.

We know  $H_q(X_k/X_{k-1},*)$  very well:

$$H_q(\bigvee_{\alpha \in A_k} S_{\alpha}^k, *) \cong \begin{cases} \mathbf{Z}[A_k] & q = k \\ 0 & q \neq k \end{cases}.$$

Lesson: The relative homology  $H_k(X_k, X_{k-1})$  keeps track of the k-cells of X.

**Definition 16.1.** The group of *cellular n-chains* in a CW complex X is

$$C_k(X) := H_k(X_k, X_{k-1}) = \mathbf{Z}[A_k].$$

If we put the fact that  $H_q(X_k, X_{k-1}) = 0$  for  $q \neq k, k+1$  into the homology long exact sequence of the pair, we find first that

$$H_q(X_{k-1}) \xrightarrow{\cong} H_q(X_k)$$
 for  $q \neq k, k-1$ ,

and then that there is a short exact sequence

$$0 \to H_k(X_k) \to C_k(X) \to H_{k-1}(X_{k-1}) \to 0$$
.

So if we fix a dimension q, and watch how  $H_q$  varies as we move through the skelata of X, we find the following picture. Say q > 0. Since  $X_0$  is discrete,  $H_q(X_0) = 0$ . Then  $H_q(X_k)$  continues to

be 0 till you get up to  $X_q$ .  $H_q(X_q)$  is a subgroup of the free abelian group  $C_q(X)$  and hence is free abelian. Relations may get introduced into it when we pass to  $X_{q+1}$ ; but thereafter all the maps

$$H_a(X_{a+1}) \to H_a(X_{a+2}) \to \cdots$$

are isomorphisms. All the q-dimensional homology of X is created on  $X_q$ , and all the relations in  $H_q(X)$  occur by  $X_{q+1}$ .

This stable value of  $H_q(X_k)$  maps isomorphically to  $H_q(X)$ , even if X is infinite dimensional. This is because the union of the images of any finite set of singular simplices in X is compact and so lies in a finite subcomplex and in particular lies in a finite skeleton. So any chain in X is the image of a chain in some skeleton. Since  $H_q(X_k) \stackrel{\cong}{\to} H_q(X_{k+1})$  for k > q, we find that  $H_q(X_q) \to H_q(X)$  is surjective. Similarly, if  $c \in S_q(X_k)$  is a boundary in X, then it's a boundary in  $X_\ell$  for some  $\ell \geq k$ . This shows that the map  $H_q(X_{q+1}) \to H_q(X)$  is injective. We summarize:

Proposition 16.2. Let  $k, q \ge 0$ . Then

$$H_q(X_k) = 0$$
 for  $k < q$ 

and

$$H_q(X_k) \xrightarrow{\cong} H_q(X)$$
 for  $k > q$ .

In particular,  $H_q(X) = 0$  if q exceeds the dimension of X.

We have defined the cellular n-chains of a CW complex X,

$$C_n(X) = H_n(X_n, X_{n-1}),$$

and found that it is the free abelian group on the set of n cells. We claim that these abelian groups are related to each other; they form the groups in a chain complex.

What should the boundary of an n-cell be? It's represented by a characteristic map  $D^n \to X_n$  whose boundary is the attaching map  $\alpha: S^{n-1} \to X_{n-1}$ . This is a lot of information, and hard to interpret because  $X_{n-1}$  is itself potentially a complicated space. But things get much simpler if I pinch out  $X_{n-2}$ . This suggests defining

$$d: C_n(X) = H_n(X_n, X_{n-1}) \xrightarrow{\partial} H_{n-1}(X_n) \to H_{n-1}(X_{n-1}, X_{n-2}) = C_{n-1}(X)$$
.

The fact that  $d^2 = 0$  is embedded in the following large diagram, in which the two columns and the central row are exact.

$$C_{n+1}(X) = H_{n+1}(X_{n+1}, X_n) \qquad 0 = H_{n-1}(X_{n-2})$$

$$\downarrow \partial_n \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad$$

Now,  $\partial_{n-1} \circ j_n = 0$ . So the composite of the diagonals is zero, i.e.,  $d^2 = 0$ , and we have a chain complex! This is the "cellular chain complex" of X.

We should compute the homology of this chain complex,  $H_n(C_*(X)) = \ker d / \operatorname{im} d$ . Now

$$\ker d = \ker(j_{n-1} \circ \partial_{n-1}).$$

But  $j_{n-1}$  is injective, so

$$\ker d = \ker \partial_{n-1} = \operatorname{im} j_n = H_n(X_n).$$

On the other hand

$$\operatorname{im} d = j_n(\operatorname{im} \partial_n) = \operatorname{im} \partial_n \subseteq H_n(X_n).$$

So

$$H_n(C_*(X)) = H_n(X_n) / \operatorname{im} \partial_n = H_n(X_{n+1})$$

by exactness of the left column; but as we know this is exactly  $H_n(X)$ ! We have proven the following result.

**Theorem 16.3.** For a CW complex X, there is an isomorphism

$$H_*(C_*(X)) \cong H_*(X)$$

natural with respect to filtration-preserving maps between CW complexes.

This has an immediate and surprisingly useful corollary.

**Corollary 16.4.** Suppose that the CW complex X has only even cells – that is,  $X_{2k} \hookrightarrow X_{2k+1}$  is an isomorphism for all k. Then

$$H_*(X) \cong C_*(X)$$
.

That is,  $H_n(X) = 0$  for n odd, is free abelian for all n, and the rank of  $H_n(X)$  for n even is the number of n-cells.

**Example 16.5.** Complex projective space  $\mathbb{CP}^n$  has a CW structure in which

$$\operatorname{Sk}_{2k}\mathbf{CP}^n = \operatorname{Sk}_{2k+1}\mathbf{CP}^n = \mathbf{CP}^k$$
.

The attaching  $S^{2k-1} \to \mathbf{CP}^k$  sends  $v \in S^{2k-1} \subseteq \mathbf{C}^n$  to the complex line through v. So

$$H_k(\mathbf{CP}^n) = \begin{cases} \mathbf{Z} & \text{for } 0 \le k \le 2n, \ k \text{ even} \\ 0 & \text{otherwise}. \end{cases}$$

Finally, notice that in our proof of Theorem 16.3 we used only properties contained in the Eilenberg-Steenrod axioms. As a result, any construction of a homology theory satisfying the Eilenberg-Steenrod axioms gives you the same values on CW complexes as singular homology.

## 17 Real projective space

Let's try to compute  $H_*(\mathbf{RP}^n)$ . This computation will invoke a second way to think of the cellular chain group  $C_n(X)$ . Each cell has a characteristic map  $D^n \to X_n$ , and we have the diagram

$$\coprod (D^n, S^{n-1}) \longrightarrow (X_n, X_{n-1})$$

$$\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$

We've shown that the vertical map induces an isomorphism in homology, and the diagonal does as well. (For example,  $\coprod D^n$  has a CW structure in which the (n-1)-skeleton is  $\coprod S^{n-1}$ .) So

$$H_n(\coprod (D^n, S^{n-1})) \xrightarrow{\cong} C_n(X).$$

We have a CW structure on  $\mathbf{RP}^n$  with  $\mathrm{Sk}_k(\mathbf{RP}^n) = \mathbf{RP}^k$ ; there is one k-cell – which we'll denote by  $e_k$  – for each k between 0 and n. So the cellular chain complex looks like this:

$$0 \longleftarrow C_0(\mathbf{R}\mathbf{P}^n) \longleftarrow C_1(\mathbf{R}\mathbf{P}^n) \longleftarrow \cdots \longleftarrow C_n(\mathbf{R}\mathbf{P}^n) \longleftarrow 0$$

$$\parallel \qquad \qquad \parallel \qquad \qquad \parallel$$

$$0 \longleftarrow \mathbf{Z}\langle e^0 \rangle \stackrel{d=0}{\longleftarrow} \mathbf{Z}\langle e^1 \rangle \longleftarrow \cdots \longleftarrow \mathbf{Z}\langle e^n \rangle \longleftarrow 0$$

The first differential is zero because we know what  $H_0(\mathbf{RP}^n)$  is (it's  $\mathbf{Z}!$ ). The differential in the cellular chain complex is given by the top row in the following commutative diagram.

$$C_{n} = H_{n}(\mathbf{R}\mathbf{P}^{n}, \mathbf{R}\mathbf{P}^{n-1}) \xrightarrow{\partial} H_{n-1}(\mathbf{R}\mathbf{P}^{n-1}) \longrightarrow H_{n-1}(\mathbf{R}\mathbf{P}^{n-1}, \mathbf{R}\mathbf{P}^{n-2}) = C_{n-1}$$

$$\uparrow \cong \qquad \qquad \uparrow \pi_{*} \qquad \qquad \cong \downarrow$$

$$H_{n}(D^{n}, S^{n-1}) \xrightarrow{\partial} H_{n-1}(S^{n-1}) \longrightarrow H_{n-1}(D^{n-1}/S^{n-2}, *).$$

The map  $\pi: S^{n-1} \to \mathbf{RP}^{n-1}$  is the attaching map of the top cell of  $RP^n$ ; that is, the double cover. The diagonal composite pinches the subspace  $\mathbf{RP}^{n-2}$  to a point. The composite map  $S^{n-1} \to D^{n-1}/S^{n-2}$  factors as follows:

$$S^{n-1}$$
 double cover  $\rightarrow$   $\mathbf{RP}^{n-1}$   $\longrightarrow$   $D^{n-1}/S^{n-2} \cong S^{n-1}$   $\longrightarrow$   $S^{n-1}/S^{n-2} = S^{n-1} \vee S^{n-1}$ 

One of the maps  $S^{n-1} \toup S^{n-1}$  from the wedge is the identity, and the other map is the antipodal map  $\alpha: S^{n-1} \toup S^{n-1}$ . Write  $\sigma$  for a generator of  $H_{n-1}(S^{n-1})$ . Then in  $H_{n-1}$  we have  $\sigma \mapsto (\sigma, \sigma) \mapsto \sigma + \alpha_* \sigma$ . So we need to know the degree of the antipodal map on  $S^{n-1}$ . The antipodal map reverses all n coordinates in  $\mathbb{R}^n$ . Each reversal is a reflection, and acts on  $S^{n-1}$  by a map of degree -1. So

$$\deg \alpha = (-1)^n.$$

Therefore the cellular complex of  $\mathbf{RP}^n$  is as follows:

dim 
$$-1$$
 0 1  $\cdots$   $n$   $n+1$   $\cdots$ 

$$0 \stackrel{0}{\longleftarrow} \mathbf{Z} \stackrel{2}{\longleftarrow} \mathbf{Z} \stackrel{0}{\longleftarrow} \cdots \stackrel{2 \text{ or } 0}{\longleftarrow} \mathbf{Z} \stackrel{\cdots}{\longleftarrow} 0 \stackrel{\cdots}{\longleftarrow} \cdots$$

The homology is then easy to read off.

**Proposition 17.1.** The homology of real projective space is as follows.

$$H_k(\mathbf{RP}^n) = \begin{cases} \mathbf{Z} & k = 0 \ \mathbf{Z} & k = n \ odd \ \mathbf{Z}/2\mathbf{Z} & k \ odd, \ 0 < k < n \ 0 & otherwise \ . \end{cases}$$

Here's a table. Missing entries are 0.

| $\dim$          | 0         | 1              | 2 | 3              | 4 | 5          | • • • |   |   |   |   |   |
|-----------------|-----------|----------------|---|----------------|---|------------|-------|---|---|---|---|---|
| $\mathbf{RP}^0$ | ${\bf z}$ |                |   |                |   |            |       |   |   |   |   |   |
| ${\bf RP}^1$    | ${\bf z}$ | ${\bf Z}$      |   |                |   |            |       |   |   |   |   |   |
| $\mathbf{RP}^2$ | ${\bf z}$ | $\mathbf{Z}/2$ |   |                |   |            |       |   |   |   |   |   |
| $\mathbf{RP}^3$ | ${\bf Z}$ | $\mathbf{Z}/2$ | 0 | ${\bf Z}$      |   |            |       |   |   |   |   |   |
| ${\bf RP}^4$    | ${\bf Z}$ | $\mathbf{Z}/2$ | 0 | $\mathbf{Z}/2$ |   |            |       |   |   |   |   |   |
| $\mathbf{RP}^5$ | ${\bf z}$ | ${\bf Z}/2$    | 0 | $\mathbf{Z}/2$ | 0 | <b>Z</b> : | :     | : | : | : | : | : |

Summary: In real projective space, odd cells create new generators; even cells (except for the zero-cell) create torsion in the previous dimension.

This example illustrates the significance of cellular homology, and, therefore, of singular homology. A CW structure involves attaching maps

$$\coprod S^{n-1} \to \operatorname{Sk}_{n-1} X$$
.

Knowing these, up to homotopy, determines the full homotopy type of the CW complex. Homology does not record all this information. Instead, it records only information about the composite obtained by pinching out  $Sk_{n-2}X$ .

$$\coprod_{a \in A_n} S_a^{n-1} \longrightarrow \operatorname{Sk}_{n-1} X$$

$$\bigvee_{b \in A_{n-1}} S_b^{n-1}$$

In  $H_{n-1}$ , this can be identified with a map

$$\partial: \mathbf{Z}[A_n] \to \mathbf{Z}[A_{n-1}]$$

that is none other than the differential in the cellular chain complex.

The moral: homology picks off only the "first order" structure of a CW complex.

On the other hand, we'll see in the next lecture that it does a very good job of that.

## 18 Euler characteristic and homology approximation

**Theorem 18.1.** Let X be a finite CW-complex with  $a_n$  n-cells. Then

$$\chi(X) = \sum_{k=0}^{\infty} (-1)^k a_k$$

depends only on the homotopy type of X; it is independent of the choice of CW structure.

This integer  $\chi(X)$  is called the *Euler characteristic* of X. We will prove this theorem by showing that  $\chi(X)$  equals a number computed from the homology groups of X, which are themselves homotopy invariants.

We'll need a little bit of information about the structure of finitely generated abelian groups. Let A be an abelian group. The set of torsion elements of A,

$$Tors(A) = \{ a \in A : na = 0 \text{ for some } n \neq 0 \}.$$

is a subgroup of A. A group is torsion free if Tors(A) = 0. For any A the quotient group A/Tors(A) is torsion free.

For a general abelian group, that's about all you can say. But now assume A is finitely generated. Then Tors(A) is a finite abelian group and A/Tors(A) is a finitely generated free abelian group, isomorphic to  $\mathbf{Z}^r$  for some integer r called the rank of A. Pick elements of A that map to a set of generators of A/Tors(A), and use them to define a map  $A/TorsA \to A$  splitting the projection map. This shows that if A is finitely generated then

$$A \cong \operatorname{Tors}(A) \oplus \mathbf{Z}^r$$
.

A finite abelian group A is necessarily of the form

$$\mathbf{Z}/n_1 \oplus \mathbf{Z}/n_2 \oplus \cdots \oplus \mathbf{Z}/n_t$$
 where  $n_1|n_2|\cdots|n_t$ .

The  $n_i$  are the "torsion coefficients" of A. They are well defined natural numbers.

**Lemma 18.2.** Let  $0 \to A \to B \to C \to 0$  be a short exact sequence of finitely generated abelian groups. Then

$$\operatorname{rank} A - \operatorname{rank} B + \operatorname{rank} C = 0$$
.

**Theorem 18.3.** Let X be a finite CW complex. Then

$$\chi(X) = \sum_{k} (-1)^k \operatorname{rank} H_k(X).$$

*Proof.* Pick a CW-structure with, say,  $a_k$  k-cells for each k. We have the cellular chain complex  $C_*$ . Write  $H_*, Z_*$ , and  $B_*$  for the homology, the cycles, and the boundaries, in this chain complex. From the definitions, we have two families of short exact sequences:

$$0 \to Z_k \to C_k \to B_{k-1} \to 0$$

and

$$0 \to B_k \to Z_k \to H_k \to 0$$
.

Let's use them and facts about rank rewrite the alternating sum:

$$\sum_{k} (-1)^{k} a_{k} = \sum_{k} (-1)^{k} \operatorname{rank}(C_{k})$$

$$= \sum_{k} (-1)^{k} (\operatorname{rank}(Z_{k}) + \operatorname{rank}(B_{k-1}))$$

$$= \sum_{k} (-1)^{k} (\operatorname{rank}(B_{k}) + \operatorname{rank}(H_{k}) + \operatorname{rank}(B_{k-1}))$$

The terms rank  $B_k$  + rank  $B_{k-1}$  cancel because it's an alternating sum. This leaves  $\sum_k (-1)^k \operatorname{rank} H_k$ . But  $H_k \cong H_k^{\operatorname{sing}}(X)$ .

In the early part of the 20th century, "homology groups" were not discussed. It was Emmy Noether who first described things that way. Instead, people worked mainly with the sequence of ranks,

$$\beta_k = \operatorname{rank} H_k(X)$$
,

which are known (following Poincaré) as the Betti numbers of X.

Given a CW-complex X of finite type, can we give a lower bound on the number of k-cells in terms of the homology of X? Let's see.  $H_k(X)$  is finitely generated because  $C_k(X) \leftarrow Z_k(X) \twoheadrightarrow H_k(X)$ . Thus

$$H_k(X) = \bigoplus_{i=1}^{t(k)} \mathbf{Z}/n_i(k)\mathbf{Z} \oplus \mathbf{Z}^{r(k)}$$

where the  $n_1(k)|\cdots|n_{t(k)}(k)$  are the torsion coefficients of  $H_k(X)$  and r(k) is the rank.

The minimal chain complex with  $H_k = \mathbf{Z}^r$  and  $H_q = 0$  for  $q \neq k$  is just the chain complex with 0 everywhere except for  $\mathbf{Z}^r$  in the kth degree. The minimal chain complex of free abelian groups with  $H_k = \mathbf{Z}/n\mathbf{Z}$  and  $H_q = 0$  for  $q \neq k$  is the chain complex with 0 everywhere except in dimensions k+1 and k, where we have  $\mathbf{Z} \xrightarrow{n} \mathbf{Z}$  These small complexes are called elementary chain complexes.

This implies that a lower bound on the number of k-cells is

$$r(k) + t(k) + t(k-1).$$

The first two terms give generators for  $H_k$ , and the last gives relations for  $H_{k-1}$ .

These elementary chain complexes can be realized as the reduced cellular chains of CW complexes (at least if k > 0). A wedge of r copies of  $S^k$  has a CW structure with one 0-cell and r k-cells, so its cellular chain complex has  $\mathbf{Z}^r$  in dimension k and 0 in other positive dimensions. To construct a CW complex with cellular chain complex given by  $\mathbf{Z} \xrightarrow{n} \mathbf{Z}$  in dimensions k+1 and k and 0 in other positive dimensions, start with  $S^k$  as k-skeleton and attach a k+1-cell by a map of degree n. For example, when k=1 and n=2, you have  $\mathbf{RP}^2$ . These CW complexes are called "Moore spaces."

This maximally efficient construction of a CW complex in a homotopy type can in fact be achieved, at least in the simply connected case:

**Theorem 18.4** (Wall, [10]). Let X be a simply connected CW-complex of finite type. Then there exists a CW complex Y with r(k) + t(k) + t(k-1) k-cells, for all k, and a homotopy equivalence  $Y \to X$ .

We will prove this theorem in 18.906.

The construction of Moore spaces can be generalized:

**Proposition 18.5.** For any graded abelian group  $A_*$  with  $A_k = 0$  for  $k \leq 0$ , there exists a CW complex X with  $\widetilde{H}_*(X) = A_*$ .

*Proof.* Let A be any abelian group. Pick generators for A. They determine a surjection from a free abelian group  $F_0$ . The kernel  $F_1$  of that surjection is free, being a subgroup of a free abelian group. Write  $G_0$  for minimal set of generators of  $F_0$ , and  $G_1$  for a minimal set of generators for  $F_1$ .

Let  $k \geq 1$ . Define  $X_k$  to be the wedge of  $|G_0|$  copies of  $S^k$ , so  $H_k(X_k) = \mathbf{Z}G_0$ . Now define an attaching map

$$\alpha: \coprod_{b \in G_1} S_b^k \to X_k$$

19. COEFFICIENTS 47

by specifying it on each summand  $S_b^k$ . The generator  $b \in G_1$  is given by a linear combination of the generators of  $F_0$ , say

$$b = \sum_{i=1}^{s} n_i a_i.$$

We want to mimic this in topology. To do this, first map  $S^k \to \bigvee^s S^k$  by pinching (s-1) tangent circles to points. In homology, this map takes a generator of  $H_k(S^k)$  to the sum of the generators of the k-dimensional homology of the various spheres in the bouquet. Map the ith sphere in the wedge to  $S_{a_i}^k \subseteq X_k$  by a map of degree  $n_i$ . The map on the summand  $S_b^k$  is then the composite of these two maps,

$$S_b^k \to \bigvee_{i=1}^s S^k \to \bigvee_a S_a^k$$
.

Altogether, we get a map  $\alpha$  that realizes  $F_1 \to F_0$  in  $H_k$ . So using it as an attaching map produces a CW complex X with  $\widetilde{H}_q(X) = A$  for q = k and 0 otherwise. Write M(A, k) for a CW complex produced in this way.

Finally, given a graded abelian group  $A_*$ , form the wedge over k of the spaces  $M(A_k, k)$ .

Such a space M(A, k), with  $\widetilde{H}_q(M(A, k)) = A$  for q = k and 0 otherwise, is called a *Moore space* of type (A, k) [9]. The notation is a bit deceptive, since M(A, k) cannot be made into a functor  $\mathbf{Ab} \to \mathbf{HoTop}$ .

#### 19 Coefficients

Abelian groups can be quite complicated, even finitely generated ones. Vector spaces over a field are so much simpler! A vector space is determined up to isomorphism by a single cardinality, its dimension. Wouldn't it be great to have a version of homology that took values in the category of vector spaces over a field?

We can do this, and more. Let R be any commutative ring at all. Instead of forming the free abelian group on  $Sin_*(X)$ , we could just as well form the free R-module:

$$S_*(X;R) = R\mathrm{Sin}_*(X)$$

This gives, first, a simplicial object in the category of R-modules. Forming the alternating sum of the face maps produces a chain complex of R-modules:  $S_n(X;R)$  is an R-module for each n, and  $d: S_n(X;R) \to S_{n-1}(X;R)$  is an R-module homomorphism. The homology groups are then again R-modules:

$$H_n(X;R) = \frac{\ker(d: S_n(X;R) \to S_{n-1}(X;R))}{\operatorname{im}(d: S_{n+1}(X;R) \to S_n(X;R))}.$$

This is the singular homology of X with coefficients in the commutative ring R. It satisfies all the Eilenberg-Steenrod axioms, with

$$H_n(*;R) = \begin{cases} R & \text{for } n = 0\\ 0 & \text{otherwise.} \end{cases}$$

(We could actually have replaced the ring R by any abelian group here, but this will become much clearer after we have the tensor product as a tool.) This means that all the work we have done for "integral homology" carries over to homology with any coefficients. In particular, if X is a

CW complex we have the cellular homology with coefficients in R,  $C_*(X;R)$ , and its homology is isomorphic to  $H_*(X;R)$ .

The coefficient rings that are most important in algebraic topology are simple ones: the integers and the prime fields  $\mathbf{F}_{p}$  and  $\mathbf{Q}$ ; almost always a PID.

As an experiment, let's compute  $H_*(\mathbf{RP}^n; R)$  for various rings R. Let's start with  $R = \mathbf{F}_2$ , the field with 2 elements. This is a favorite among algebraic topologists, because using it for coefficients eliminates all sign issues. The cellular chain complex has  $C_k(\mathbf{RP}^n; \mathbf{F}_2) = \mathbf{F}_2$  for  $0 \le k \le n$ , and the differential alternates between multiplication by 2 and by 0. But in  $\mathbf{F}_2$ , 2 = 0: so d = 0, and the cellular chains coincide with the homology:

$$H_k(\mathbf{RP}^n; \mathbf{F}_2) = \begin{cases} \mathbf{F}_2 & \text{for } 0 \le k \le n \\ 0 & \text{otherwise}. \end{cases}$$

On the other hand, suppose that R is a ring in which 2 is invertible. The universal case is  $\mathbf{Z}[1/2]$ , but any subring of the rationals containing 1/2 would do just as well, as would  $\mathbf{F}_p$  for p odd. Now the cellular chain complex (in dimensions 0 through n) looks like

$$R \stackrel{0}{\leftarrow} R \stackrel{\cong}{\leftarrow} R \stackrel{0}{\leftarrow} R \stackrel{\cong}{\leftarrow} \cdots \stackrel{\cong}{\leftarrow} R$$

for n even, and

$$R \stackrel{0}{\leftarrow} R \stackrel{\cong}{\leftarrow} R \stackrel{0}{\leftarrow} R \stackrel{\cong}{\leftarrow} \cdots \stackrel{0}{\leftarrow} R$$

for n odd. Therefore for n even

$$H_k(\mathbf{RP}^n; R) = \begin{cases} R & \text{for } k = 0\\ 0 & \text{otherwise} \end{cases}$$

and for n odd

$$H_k(\mathbf{RP}^n; R) = \begin{cases} R & \text{for } k = 0 \\ R & \text{for } k = n \\ 0 & \text{otherwise.} \end{cases}$$

You get a much simpler result: Away from 2, even projective spaces look like points, and odd projective spaces look like spheres!

I'd like to generalize this process a little bit, and allow coefficients not just in a commutative ring, but more generally in a module M over a commutative ring; in particular, any abelian group. This is most cleanly done using the mechanism of the tensor product. That mechanism will also let us address the following natural question:

Question 19.1. Given  $H_*(X;R)$ , can we deduce  $H_*(X;M)$  for an R-module M?

The answer is called the "universal coefficient theorem". I'll spend a few days developing what we need to talk about this.

## 20 Tensor product

The category of R-modules is what might be called a "categorical ring," in which addition corresponds to the direct sum, the zero element is the zero module, 1 is R itself, and multiplication is ...well, the subject for today. We care about the tensor product for two reasons: First, it allows us to deal smoothly with bilinear maps such that the cross-product. Second, and perhaps more

important, it will allow us relate homology with coefficients in an any R-module to homology with coefficients in the PID R; for example, relate  $H_*(X; M)$  to  $H_*(X)$ , where M is any abelian group. Let's begin by recalling the definition of a bilinear map over a commutative ring R.

**Definition 20.1.** Given three *R*-modules, M, N, P, a bilinear map (or, to be explicit, *R*-bilinear map) is a function  $\beta: M \times N \to P$  such that

$$\beta(x + x', y) = \beta(x, y) + \beta(x', y), \quad \beta(x, y + y') = \beta(x, y) + \beta(x, y'),$$

and

$$\beta(rx, y) = r\beta(x, y), \quad \beta(x, ry) = r\beta(x, y),$$

for  $x, x' \in M$ ,  $y, y' \in N$ , and  $r \in R$ .

**Example 20.2.**  $\mathbf{R}^n \times \mathbf{R}^n \to \mathbf{R}$  given by the dot product is an  $\mathbf{R}$ -bilinear map. The cross product  $\mathbf{R}^3 \times \mathbf{R}^3 \to \mathbf{R}^3$  is  $\mathbf{R}$ -bilinear. If R is a ring, the multiplication  $R \times R \to R$  is R-bilinear, and the multiplication on an R-module M given by  $R \times M \to M$  is R-bilinear. This enters into topology because the cross-product  $H_m(X;R) \times H_n(Y;R) \xrightarrow{\times} H_{m+n}(X \times Y;R)$  is R-bilinear.

Wouldn't it be great to reduce stuff about bilinear maps to linear maps? We're going to do this by means of a universal property.

**Definition 20.3.** Let M, N be R-modules. A tensor product of M and N is an R-module P and a bilinear map  $\beta_0: M \times N \to P$  such that for every R-bilinear map  $\beta: M \times N \to Q$  there is a unique factorization

$$M \times N \xrightarrow{\beta_0} P$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$

through an R-module homomorphism f.

We should have pointed out that the composition  $f \circ \beta_0$  is indeed again R-bilinear; but this is easy to check.

So  $\beta_0$  is a universal bilinear map out of  $M \times N$ . Instead of  $\beta_0$  we're going to write  $\otimes : M \times N \to P$ . This means that  $\beta(x,y) = f(x \otimes y)$  in the above diagram. There are lots of things to say about this. When you have something that is defined via a universal property, you know that it's unique ... but you still have to check that it exists!

Construction 20.4. I want to construct a univeral R-bilinear map out of  $M \times N$ . Let  $\beta : M \times N \to Q$  be any R-bilinear map. This  $\beta$  isn't linear. Maybe we should first extend it to a linear map. There is a unique R-linear extension over the free R-module  $R(M \times N)$  generated by the set  $M \times N$ :

The map [-], including a basis, isn't bilinear. So we should quotient  $R\langle M \times N \rangle$  by a submodule S of relations to make it bilinear. So S is the sub R-module generated by the four familes of elements (corresponding to the four relations in the definition of R-bilinearity):

1. 
$$[(x+x',y)] - [(x,y)] - [(x'-y)]$$

2. 
$$[(x, y + y')] - [(x, y)] - [(x, y')]$$

3. 
$$[(rx,y)] - r[(x,y)]$$

4. 
$$[(x,ry)] - r[(x,y)]$$

for  $x, x' \in M$ ,  $y, y' \in N$ , and  $r \in R$ . Now the composite  $M \times N \to R\langle M \times N \rangle / S$  is R-bilinear - we've quotiented out by all things that prevented it from being so! And the map  $R\langle M \times N \rangle \to Q$  factors as  $R\langle M \times N \rangle \to R\langle M \times N \rangle / S \xrightarrow{f} Q$ , where f is R-linear, and uniquely because the map to the quotient is surjective. This completes the construction.

If you find yourself using this construction, stop and think about what you're doing. You're never going to use this construction to compute anything. Here's an example: for any abelian group A,

$$A \times \mathbf{Z}/n\mathbf{Z} \to A/nA$$
,  $(a,b) \mapsto ba \mod nA$ 

is clearly bilinear, and is universal as such. Just look: If  $\beta: A \times \mathbf{Z}/n\mathbf{Z} \to Q$  is bilinear then  $\beta(na,b) = n\beta(a,b) = \beta(a,nb) = \beta(a,0) = 0$ , so  $\beta$  factors through A/nA; and  $A \times \mathbf{Z}/n\mathbf{Z} \to A/nA$  is surjective. So  $A \otimes \mathbf{Z}/n\mathbf{Z} = A/nA$ .

**Remark 20.5.** The image of  $M \times N$  in  $R\langle M \times N \rangle / S$  generates it as an R-module. These elements  $x \otimes y$  are called "decomposable tensors."

What are the properties of such a universal bilinear map?

**Property 20.6** (Uniqueness). Suppose  $\beta_0: M \times N \to P$  and  $\beta'_0: M \times N \to P'$  are both universal. Then there's a linear map  $f: P \to P'$  such that  $\beta'_0 = f\beta_0$  and a linear map  $f': P' \to P$  such that  $\beta_0 = f'\beta'_0$ . The composite  $f'f: P \to P$  is a linear map such that  $f'f\beta_0 = f'\beta'_0 = \beta_0$ . The identity map is another. But by universality, there's only one such linear map, so  $f'f = 1_P$ . An identical argument shows that  $ff' = 1_{P'}$  as well, so they are inverse linear isomorphism. In brief:

The target of a univeral R-bilinear map  $\beta_0: M \times N \to P$  is unique up to a unique R-linear isomorphism compatible with the map  $\beta_0$ .

This entitles us to speak of "the" universal bilinear map out of  $M \times N$ , and give the target a symbol:  $M \otimes_R N$ . If R is the ring of integers, or otherwise understood, we will drop it from the notation.

**Property 20.7** (Functoriality). Suppose  $f: M \to M'$  and  $N \to N'$ . Study the diagram

$$\begin{array}{c|c} M\times N & \xrightarrow{\otimes} M\otimes N \\ \downarrow^{f\times g} & \downarrow^{l}f\otimes g \\ M'\times N' & \xrightarrow{\otimes} M'\otimes N' \end{array}$$

There is a unique R-linear map  $f \otimes g$  because the diagonal map is R-bilinear and the map  $M \times N \to M \otimes N$  is the universal R-bilinear map out of  $M \times N$ . You are invited to show that this construction is functorial.

**Property 20.8** (Unitality, associativity, commutativity). I said that this was going to be a "categorical ring," so we should check various properties of the tensor product. For example,  $R \otimes_R M$  should be isomorphic to M. Let's think about this for a minute. We have an R-bilinear map  $R \times M \to M$ , given by multiplication. We just need to check the universal property. Suppose we have an R-bilinear map  $\beta: R \times M \to P$ . We have to construct a map  $f: M \to P$  such that  $\beta(r,x) = f(rx)$  and show it's unique. Our only choice is  $f(x) = \beta(1,x)$ , and that works.

Similarly, we should check that there's a unique isomorphism  $L \otimes (M \otimes N) \xrightarrow{\cong} (L \otimes M) \otimes N$  that's compatible with  $L \times (M \times N) \cong (L \times M) \times N$ , and that there's a unique isomorphism  $M \otimes N \to N \otimes M$  that's compatible with the switch map  $M \times N \to N \times M$ . There are a few other things to check, too: Have fun!

**Property 20.9** (Sums). What happens with  $M \otimes \bigoplus_{\alpha \in A} N_{\alpha}$ ? This might be a finite direct sum, or maybe an uncountable collection. How does this relate to  $\bigoplus_{\alpha \in A} (M \otimes N_{\alpha})$ ? Let's construct a map

$$f: \bigoplus_{\alpha \in A} (M \otimes N_{\alpha}) \to M \otimes \left(\bigoplus_{\alpha \in A} N_{\alpha}\right).$$

We just need to define maps  $M \otimes N_{\alpha} \to M \otimes \bigoplus_{\alpha \in A} N_{\alpha}$  because the direct sum is the coproduct. We can use  $1 \otimes \operatorname{in}_{\alpha}$  where  $\operatorname{in}_{\alpha} : N_{\alpha} \to \bigoplus_{\alpha \in A} N_{\alpha}$ . These give you a map f.

What about a map the other way? We'll define a map out of the tensor product using the universal property. So we need to define a bilinear map out of  $M \times \bigoplus_{\alpha \in A} N_{\alpha}$ . By linearity in the second factor, it will suffice to say where to send elements of the form  $(x, y) \in M \otimes N_{\beta}$ . Just send it to  $x \otimes \text{in}_{\beta} y$ , where  $\text{in}_{\beta} : N_{\beta} \to \bigoplus_{\alpha \in A} N_{\alpha}$  is the inclusion of a summand. It's up to you to check that these are inverses.

**Property 20.10** (Distributivity). Suppose  $f: M' \to M$ ,  $r \in R$ , and  $g_0, g_1: N' \to N$ . Then

$$f \otimes (g_0 + g_1) = f \otimes g_0 + f \otimes g_1 : M' \otimes N' \to M \otimes N$$

and

$$f \otimes rq_0 = r(f \otimes q_0) : M' \otimes N' \to M \otimes N$$
.

Again I'll leave this to you to check.

Our immediate use of this construction is to give a clean definition of "homology with coefficients in M," where M is any abelian group. First, endow singular chains with coefficients in M like this:

$$S_*(X;M) = S_*(X) \otimes M$$

Then we define

$$H_n(X;M) = H_n(S_*(X;M)).$$

Since  $S_n(X) = \mathbf{Z}\mathrm{Sin}_n(X)$ ,  $S_n(X; M)$  is a direct sum of copies of M indexed by the n-simplices in X. If M happens to be a ring, this coincides with the notation used in the last lecture. The boundary maps are just  $d \otimes 1 : S_n(X) \otimes M \to S_{n-1}(X) \otimes M$ .

As we have noted, the sequence

$$0 \to S_n(A) \to S_n(X) \to S_n(X,A) \to 0$$

is split short exact, and therefore applying the functor  $-\otimes M$  to it produces another split short exact sequence. So

$$S_n(X,A) \otimes M = S_n(A;M)/S_n(X;M)$$
,

and it makes sense to use the notation  $S_n(X, A; M)$  for this. This is again a chain complex (by functoriality of the tensor product), and we define

$$H_n(X, A; M) = H_n(S_n(X, A; M)).$$

Notice that

$$H_n(*;M) = \begin{cases} M & \text{for } n = 0\\ 0 & \text{otherwise} \end{cases}$$

The following result is immediate:

**Proposition 20.11.** For any abelian group M,  $(X, A) \mapsto H_*(X, A; M)$  provides a homology theory satisfying the Eilenberg-Steenrod axioms with  $H_0(*; M) = M$ .

Suppose R is a commutative ring and A is an abelian group. Then  $A \otimes R$  is naturally an R-module. So  $S_*(X;R)$  is a chain complex of R-modules – free R-modules. We can go a little further: suppose that M is an R-module. Then  $A \otimes M$  is an R-module; and  $S_*(X;M)$  is a chain complex of R-modules. We can also write

$$S_*(X;M) = S_*(X;R) \otimes_R M$$
.

This construction is natural in the R-module M; and, again using the fact that sums of exact sequences are exact, a short exact sequence of R-modules

$$0 \to M' \to M \to M'' \to 0$$

leads to a short exact sequence of chain complexes

$$0 \to S_*(X; M') \to S_*(X; M) \to S_*(X; M'') \to 0$$

and hence to a long exact sequence in homology, a "coefficient long exact sequence":

$$H_{n}(X; M') \xrightarrow{\partial} H_{n}(X; M) \xrightarrow{\partial} H_{n}(X; M'')$$

$$H_{n-1}(X; M') \xrightarrow{\partial} \cdots$$

A particularly important case is when R is a field; then  $S_*(X;R)$  is a chain complex of vector spaces over R, and  $H_*(X;R)$  is a graded vector space over R.

**Question 20.12.** A reasonable question is this: Suppose we know  $H_*(X)$ . Can we compute  $H_*(X;M)$  for an abelian group M? More generally, suppose we know  $H_*(X;R)$  and M is an R-module. Can we compute  $H_*(X;M)$ ?

#### 21 Tensor and Tor

We continue to study properties of the tensor product. Recall that

$$A \otimes \mathbf{Z}/n\mathbf{Z} = A/nA$$
.

Consider the exact sequence

$$0 \to \mathbf{Z} \xrightarrow{2} \mathbf{Z} \to \mathbf{Z}/2\mathbf{Z} \to 0$$
.

Let's tensor it with  $\mathbb{Z}/2\mathbb{Z}$ . We get

$$0 \rightarrow \mathbf{Z}/2\mathbf{Z} \rightarrow \mathbf{Z}/2\mathbf{Z} \rightarrow \mathbf{Z}/2\mathbf{Z} \rightarrow 0$$
.

This cannot be a short exact sequence! This is a major tragedy: tensoring doesn't preserve exact sequences; one says that the functor  $\mathbb{Z}/n\mathbb{Z} \otimes -$  is not "exact." This is why we can't form homology with coefficients in M by simply tensoring homology with M.

Tensoring does respect certain exact sequences:

**Proposition 21.1.** The functor  $N \mapsto M \otimes_R N$  preserves cokernels; it is right exact.

*Proof.* Suppose that  $N' \to N \to N'' \to 0$  is exact and let  $f: M \otimes N \to Q$ . We wish to show that there is a unique factorization as shown in the diagram

$$M \otimes N' \longrightarrow M \otimes N \longrightarrow M \otimes N'' \longrightarrow 0$$

$$\downarrow f$$

$$Q.$$

This is equivalent to asking whether there is a unique factorization of the corresponding diagram of bilinear maps,

$$M \times N' \longrightarrow M \times N \longrightarrow M \times N'' \longrightarrow 0$$

$$\downarrow \beta$$

$$Q$$

– uniqueness of the linear factorization is guaranteed by the fact that  $M \times N''$  generates  $M \otimes N''$ . This unique factorization reflects the fact that  $M \times -$  preserves cokernels.

Failure of exactness is bad, so let's try to repair it. A key observation is that if M is free, then  $M \otimes_R - is$  exact. If M = RS, the free R-module on a set S, then  $M \otimes_R N = \bigoplus_S N$ , since tensoring distributes over direct sums. Then we remember the following "obvious" fact:

**Lemma 21.2.** If  $M'_i \to M_i \to M''_i$  is exact for all  $i \in I$ , then so is

$$\bigoplus M_i' \to \bigoplus M_i \to \bigoplus M_i''.$$

Proof. Clearly the composite is zero. Let  $(x_i \in M_i, i \in I) \in \bigoplus M_i$  and suppose it maps to zero. That means that each  $x_i$  maps to zero in  $M_i''$  and hence is in the image of some  $x_i' \in M_i'$ . Just make sure to take  $x_i' = 0$  if  $x_i = 0$ .

To exploit this observation, we'll "resolve" M by free modules. This means: find a surjection from a free R-module,  $F_0 \to M$ . This amounts to specifying R-module generators. For a general ring R, the kernel of  $F_0 \to M$  may not be free. For the moment, let's make sure that it is by assuming that R is a PID, and write  $F_1$  for the kernel. The failure of  $M \otimes -$  to be exact is measured, at least partially, by the leftmost term (defined as a kernel) in the exact sequence

$$0 \to \operatorname{Tor}_1^R(M,N) \to F_1 \otimes_R N \to F_0 \otimes_R N \to M \otimes_R N \to 0$$
.

The notation suggests that this Tor term is independent of the resolution. This is indeed the case, as we shall show presently. But before we do, let's compute some Tor groups.

**Example 21.3.** For any PID R, if M = F is free over R we can take  $F_0 = F$  and  $F_1 = 0$ , and discover that then  $\text{Tor}_1^R(F, N) = 0$  for any N.

**Example 21.4.** Let  $R = \mathbf{Z}$  and  $M = \mathbf{Z}/n\mathbf{Z}$ , and N any abelian group. When  $R = \mathbf{Z}$  it is often omitted from the notation for Tor. There is a nice free resolution staring at us:  $F_0 = F_1 = \mathbf{Z}$ , and  $F_1 \to F_0$  given by multiplication by n. The sequence defining Tor<sub>1</sub> looks like

$$0 \to \operatorname{Tor}_1(\mathbf{Z}/n\mathbf{Z}, N) \to \mathbf{Z} \otimes N \xrightarrow{n \otimes 1} \mathbf{Z} \otimes N \to \mathbf{Z}/n\mathbf{Z} \otimes N \to 0,$$

SO

$$\mathbf{Z}/n\mathbf{Z} \otimes N = N/nN$$
,  $\operatorname{Tor}_1(\mathbf{Z}/n\mathbf{Z}, N) = \ker(n|N)$ .

The torsion in this case is the "n-torsion" in N. This accounts for the name.

Functors like Tor<sub>1</sub> can be usefully defined for any ring, and moving to that general case makes their significance clearer and illuminates the reason why Tor<sub>1</sub> is independent of choice of generators.

So let R be any ring and M a module over it. By picking R-module generators I can produce a surjection from a free R-module,  $F_0 \to M$ . Write  $K_0$  for the kernel of this map. It is the module of relations among the generators. We can no longer guarantee that it's free, but we can at least find a set of module generators for it, and construct a surjection from a free R-module,  $F_1 \to K_0$ . Continuing in this way, we get a diagram like this –

– in which the upside-down V subdiagrams are short exact sequences and  $F_s$  is free for all s. Splicing these exact sequences gives you an exact sequence in the top row. This is a free resolution of N. The top row,  $F_*$ , is a chain complex. It maps to the very short chain complex with N in degree 0 and 0 elsewhere, and this chain map is a homology isomorphism (or "quasi-isomorphism"). We have in effect replaced N with this chain complex of free modules. The module N may be very complicated, with generators, relations, relations between relations . . . . All this is laid out in front of us by the free resolution. Generators of  $F_0$  map to generators for N, and generators for  $F_1$  map to relations among those generators.

Now we can try to define higher Tor functors by tensoring  $F_*$  with N and taking homology. If R is a PID and the resolution is just  $F_1 \to F_0$ , forming homology is precisely taking cokernel and kernel, as we did above. In general, we define

$$\operatorname{Tor}_n^R(M,N) = H_n(M \otimes_R F_*).$$

In the next lecture we will check that this is well-defined – independent of free resolution, and functorial in the arguments. For the moment, notice that

$$\operatorname{Tor}_n^R(M, F) = 0$$
 for  $n > 0$  if  $F$  is free,

since I can take  $F \stackrel{\cong}{\leftarrow} F \leftarrow 0 \leftarrow \cdots$  as a free resolution; and that

$$\operatorname{Tor}_0^R(M,N) = M \otimes_R N$$

since we know that  $M \otimes_R$  – is right-exact.

## 22 The fundamental theorem of homological algebra

We will now show that the R-modules  $\operatorname{Tor}_n^R(M,N)$  are well-defined and functorial. This will be an application of a very general principle.

**Theorem 22.1** (Fundamental Theorem of Homological Algebra). Let M and N be R-modules; let

$$0 \leftarrow M \leftarrow E_0 \leftarrow E_1 \leftarrow \cdots$$

be a sequence in which each  $E_n$  is free; let

$$0 \leftarrow N \leftarrow F_0 \leftarrow F_1 \leftarrow \cdots$$

be an exact sequence; and let  $f: M \to N$  be a homomorphism. Then we can lift f to a chain map  $f_*: E_* \to F_*$ , uniquely up to chain homotopy.

*Proof.* Let's try to construct  $f_0$ . Consider:

$$0 \longrightarrow K_0 = \ker(\epsilon_M) \longrightarrow E_0 \xrightarrow{\epsilon_M} M$$

$$\downarrow g_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f$$

$$\downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad \downarrow f_0 \qquad \qquad$$

We know that  $E_0 = RS$  for some set S. What we do is map the generators of  $E_0$  into M via  $\epsilon_M$  and then into F via f, and then lift them to  $F_0$  via  $\epsilon_N$  (which is possible because it's surjective). Then extend to a homomorphism, to get  $f_0$ . You can restrict  $f_0$  to kernels to get  $g_0$ .

Now the map  $d: E_1 \to E_0$  satisfies  $\epsilon_M \circ d = 0$ , and so factors through a map to  $K_0 = \ker \epsilon_M$ . Similarly,  $d: F_1 \to F_0$  factors through a map  $F_1 \to L_0$ , and this map must be surjective because the sequence  $F_1 \to F_0 \to N$  is exact. We find ourselves in exactly the same situation:

$$0 \longrightarrow K_1 \longrightarrow E_1 \longrightarrow K_0$$

$$\downarrow g_1 \qquad \downarrow f_1 \qquad \downarrow g_0$$

$$\downarrow g_0 \qquad \qquad \downarrow f_1 \qquad \downarrow g_0$$

$$\downarrow g_0 \qquad \qquad \downarrow f_1 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0$$

$$\downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_0 \qquad \qquad \downarrow g_$$

So we construct  $f_*$  by induction.

Now we need to prove the chain homotopy claim. So suppose I have  $f_*, f_*': E_* \to F_*$ , both lifting  $f: M \to N$ . Then  $f_n' - f_n$  (which we'll rename  $\ell_n$ ) is a chain map lifting  $0: M \to N$ . We want to consruct a chain null-homotopy of  $\ell_*$ ; that is, we want  $h: E_n \to F_{n+1}$  such that  $dh + hd = \ell_n$ . At the bottom,  $E_{-1} = 0$ , so we want  $h: E_0 \to F_1$  such that  $dh = \ell_0$ . This factorization happens in two steps.

$$\begin{array}{ccc}
E_0 \longrightarrow M \\
\downarrow & \downarrow & \downarrow \\
F_1 & \longrightarrow E_0 & \stackrel{\epsilon_N}{\longrightarrow} N.
\end{array}$$

First,  $\epsilon_N \ell_0 = 0$  implies that  $\ell_0$  factors through  $L_0 = \ker \epsilon_N$ . Next,  $F_1 \to L_0$  is surjective, by exactness, and  $E_0$  is free, so we can lift generators and extend R-linearly to get  $h: E_0 \to F_1$ ..

The next step is organized by the diagram

This diagram doesn't commute;  $dh = \ell_0$ , but the  $(d, h, \ell_1)$  triangle doesn't commute. Rather, we want to construct  $h: E_1 \to F_2$  such that  $dh = \ell_1 - hd$ . Since

$$d(\ell_1 - hd) = \ell_0 d - dhd = (\ell_0 - dh)d = 0.$$

the map  $\ell_1 - hd$  lifts to  $L_1 = \ker d$ . But then it lifts through  $F_2$ , since  $F_2 \to L_1$  is surjective and  $E_1$  is free.

Exactly the same process continues.

This proof uses a property of freeness that is shared by a broader class of modules.

**Definition 22.2.** An R-module P is projective if any map out of P factors through any surjection:

Every free module is projective, and this is the property of freeness that we jave been using; the Fundamental Theorem of Homological Algebra holds under the weaker assumption that each  $E_n$  is projective.

Any direct summand in a projective is also projective. Any projective module is a direct summand of a free module. Over a PID, every projective is free, because any submodule of a free is free. But there are examples of nonfree projectives:

**Example 22.3.** Let k be a field and let R be the product ring  $k \times k$ . It acts on k in two ways, via (a,b)c = ac and via (a,b)c = bc. These are both projective R-modules that are not free.

Now we will apply Theorem 22.1 to verify that our proposed construction of Tor is independent of free (or projective!) resolution, and is functorial.

Suppose I have  $f: N' \to N$ . Pick arbitrary free resolutions  $N' \leftarrow F'_*$  and  $N \leftarrow F_*$ , and pick any chain map  $f_*: F'_* \to F_*$  lifting f. We claim that the map induced in homology by  $1 \otimes f_*: M \otimes_R F'_* \to M \otimes_R F_*$  is independent of the choice of lift. Suppose  $f'_*$  is another lift, and pick a chain homotopy  $h: f_* \simeq f'_*$ . Since  $M \otimes_R -$  is additive, the relation

$$1 \otimes h : 1 \otimes f_* \simeq 1 \otimes f'_*$$

still holds. So  $1 \otimes f_*$  and  $1 \otimes f'_*$  induce the same map in homology.

For example, suppose that  $F_*$  and  $F'_*$  are two projective resolutions of N. Any two lifts of the identity map are chain-homotopic, and so induce the same map  $H_*(M \otimes_R F_*) \to H_*(M \otimes_R F'_*)$ . So if  $f: F_* \to F'_*$  and  $g: F'_* \to F_*$  are chain maps lifting the identity, then  $f_* \circ g_*$  induces the same self-map of  $H_*(M \otimes_R F'_*)$  as the identity self-map does, and so (by functoriality) is the identity. Similarly,  $g_* \circ f_*$  induces the identity map on  $H_*(M \otimes_R F_*)$ . So they induce inverse isomorphisms.

Putting all this together shows that any two projective resolutions of N induce canonically isomorphic modules  $\operatorname{Tor}_n^R(M,N)$ , and that a homomorphism  $f:N'\to N$  induces a well defined map  $\operatorname{Tor}_n^R(M,N')\to\operatorname{Tor}_n^R(M,N)$  that renders  $\operatorname{Tor}_n^R(M,-)$  a functor.

My last comment about Tor is that there's a symmetry there. Of course,  $M \otimes_R N \cong N \otimes_R M$ . This uses the fact that R is commutative. This leads right on to saying that  $\operatorname{Tor}_n^R(M,N) \cong \operatorname{Tor}_n^R(N,M)$ . We've been computing Tor by taking a resolution of the second variable. But I could equally have taken a resolution of the first variable. This follows from Theorem 22.1.

**Example 22.4.** I want to give an example when you do have higher Tor modules. Let k be a field, and let  $R = k[d]/(d^2)$ . This is sometimes called the "dual numbers," or the exterior algebra over k. What is an R-module? It's just a k-vector space M with an operator d (given by multiplication by d) that satisfies  $d^2 = 0$ . Even though there's no grading around, I can still define the "homology" of M:

$$H(M;d) = \frac{\ker d}{\operatorname{im} d}$$
.

This k-algebra is augmented by an algebra map  $\epsilon: R \to k$  splitting the unit;  $\epsilon(d) = 0$ . This renders k an R-module. Let's construct a free R-module resolution of this module. Here's a picture.

The vertical lines indicate multiplication by d. We could write this as

$$0 \leftarrow k \xleftarrow{\epsilon} R \xleftarrow{d} R \xleftarrow{d} R \leftarrow \cdots.$$

Now tensor this over R with an R-module M; so M is a vector space equipped with an operator d with  $d^2 = 0$ . Each copy of R gets replaced by a copy of M, and the differential gives multiplication by d on M. So taking homology gives

$$\operatorname{Tor}_{n}^{R}(k,M) = \begin{cases} k \otimes_{R} M = M/dM & \text{for } n = 0\\ H(M;d) & \text{for } n > 0. \end{cases}$$

So for example

$$\operatorname{Tor}_n^R(k,k) = k \quad \text{for } n \ge 0.$$

#### 23 Hom and Lim

We will now develop more properties of the tensor product: its relationship to homomorphisms and to direct limits.

The tensor product arose in our study of bilinear maps. Even more natural are *linear maps*. Given a commutative ring R and two R-modules M and N, we can think about the collection of all R-linear maps from M to N. Not only does this set form an abelian group (under pointwise addition of homomorphisms); it forms an R-module, with

$$(rf)(y) = f(ry) = rf(y), \quad r \in R, y \in M.$$

The check that this is again an R-module homomorphism uses commutativity of R. We will write  $\operatorname{Hom}_R(M,N)$ , or just  $\operatorname{Hom}(M,N)$ , for this R-module.

Since  $\operatorname{Hom}(M,N)$  is an R-module, we are entitled to think about what an R-module homomorphism into it is. Given

$$f: L \to \operatorname{Hom}(M, N)$$

we can define a new function

$$\hat{f}: L \times M \to N$$
,  $\hat{f}(x,y) = (f(x))(y) \in N$ .

You should check that this new function  $\hat{f}$  is R-bilinear! So we get a natural map

$$\operatorname{Hom}(L, \operatorname{Hom}(M, N)) \to \operatorname{Hom}(L \otimes M, N)$$
.

Conversely, given a map  $\hat{f}: L \otimes M \to N$  and  $x \in L$ , we can define  $f(x): M \to N$  by the same formula. These are inverse operations, so:

**Lemma 23.1.** The natural map  $\operatorname{Hom}(L,\operatorname{Hom}(M,N)) \to \operatorname{Hom}(L\otimes M,N)$  is an isomorphism.

One says that  $\otimes$  and Hom are *adjoint*, a word suggested by Sammy Eilenberg to Dan Kan, who first formulated this relationship between functors [7].

The second thing we will discuss is a generalization of one perspective on how the rational numbers are constructed from the integers – by a limit process: there are compatible maps in the diagram

$$\mathbf{Z} \xrightarrow{2} \mathbf{Z} \xrightarrow{3} \mathbf{Z} \xrightarrow{4} \mathbf{Z} \xrightarrow{5} \cdots$$

$$\downarrow 1 \qquad \downarrow 1/2 \qquad \downarrow 1/3! \qquad \downarrow 1/4!$$

$$\mathbf{Q} \xrightarrow{=} \mathbf{Q} \xrightarrow{=} \mathbf{Q} \xrightarrow{=} \mathbf{Q} \xrightarrow{=} \cdots$$

and **Q** is the "universal," or "initial," abelian group you can map to.

We will formalize this process, using partially ordered sets as indexing sets. Recall from Lecture 3 that a partially ordered set, or poset, is a small category  $\mathcal{I}$  such that  $\#\mathcal{I}(i,j) \leq 1$  and the only isomorphisms are the identity maps. We will be interested in a particular class of posets.

**Definition 23.2.** A poset  $(\mathcal{I}, \leq)$  is *directed* if for every  $i, j \in \mathcal{I}$  there exists  $k \in \mathcal{I}$  such that  $i \leq k$  and  $j \leq k$ .

**Example 23.3.** This is a very common condition. A first example is the natural numbers  $\mathbb{N}$  with  $\leq$  as the order. Another example is the positive natural numbers, with  $i \leq j$  if i|j. This is because i, j|(ij). A topological example: if X is a space, A a subspace, and I is the set of open subsets of X containing A, directed by saying that  $U \leq V$  if  $U \supseteq V$ . This is because an intersection of two opens is again open.

23. HOM AND LIM 59

**Definition 23.4.** Let  $\mathcal{I}$  be a directed set. An  $\mathcal{I}$ -directed system in a category  $\mathcal{C}$  is a functor  $\mathcal{I} \to \mathcal{C}$ . This means that for every  $i \in \mathcal{I}$  we are given an object  $X_i \in \mathcal{C}$ , and for every  $i \leq j$  we are given a map  $f_{i,j}: X_i \to X_j$ , in such a way that  $f_{i,i} = 1_{X_i}$  and if  $i \leq j \leq k$  then  $f_{i,k} = f_{j,k} \circ f_{i,j}: X_i \to X_k$ .

**Example 23.5.** If  $\mathcal{I} = (\mathbb{N}, \leq)$ , then you get a "linear system"  $X_0 \xrightarrow{f_{01}} X_1 \xrightarrow{f_{12}} X_2 \to \cdots$ .

**Example 23.6.** Suppose  $\mathcal{I} = (\mathbb{N}_{>0}, |)$ , i.e., the second example above. You can consider  $\mathcal{I} \to \mathbf{Ab}$ , say assigning to each i the integers  $\mathbf{Z}$ , and  $f_{ij} : \mathbf{Z} \xrightarrow{j/i} \mathbf{Z}$ .

These directed systems can be a little complicated. But there's a simple one, namely the constant one.

**Example 23.7.** Let  $\mathcal{I}$  be any directed system. Any object  $A \in \mathcal{C}$  determines an  $\mathcal{I}$ -directed set, namely the constant functor  $c_A : \mathcal{I} \to \mathcal{C}$ .

Not every directed system is constant, but we can try to find a best approximating constant system. To compare systems, we need morphisms.  $\mathcal{I}$ -directed systems in  $\mathcal{C}$  are functors  $\mathcal{I} \to \mathcal{C}$ . They are related by natural transformations, and those are the morphisms in the category of  $\mathcal{I}$ -directed systems. That is to say, a morphism is a choice of map  $g_i: X_i \to Y_i$ , for each  $i \in \mathcal{I}$ , such that

$$X_{i} \longrightarrow X_{j}$$

$$\downarrow g_{i} \qquad \downarrow g_{j}$$

$$Y_{i} \longrightarrow Y_{j}$$

commutes for all  $i \leq j$ .

**Definition 23.8.** Let  $X: \mathcal{I} \to \mathcal{C}$  be a directed system. A *direct limit* is an object L and a map  $X \to c_L$  that is initial among maps to constant systems. This means that given any other map to a constant system, say  $X \to c_A$ , there is a unique map  $f: L \to A$  such that

$$X = \begin{pmatrix} c_L \\ c_f \\ c_A \end{pmatrix}$$

commutes.

This is a "universal property." So two different direct limits are canonically isomorphic; but a directed system may fail to have a direct limit. For example, the linear directed systems we used to create the rational numbers exists in the category of finitely generated abelian groups; but **Q** is not finitely generated, and there's no finitely generated group that will serve as a direct limit of this system in the category of finitely generated abelian groups.

**Example 23.9.** Suppose we have an increasing sequence of subspaces,  $X_0 \subseteq X_1 \subseteq \cdots \subseteq X$ . This gives us a directed system of spaces, directed by the poset  $(\mathbb{N}, \leq)$ . It's pretty clear that as a *set* the direct limit of this system is the union of the subspaces. Saying that X is the direct limit of this directed system of spaces is saying first that X is the union of the  $X_i$ 's, and second that the topology on X is determined by the topology on the subspaces; it's the "weak topology," characterized by the property that a map  $f: X \to Y$  is continuous if and only if the restriction of f to each  $X_n$  is continuous. This is saying that a subset of X is open if and only if its intersection with each  $X_n$  is open in X. Our example is that a CW-complex is the direct limit of its skelata.

Direct limits may be constructed from the material of coproducts and quotients. So suppose  $X : \mathcal{I} \to \mathcal{C}$  is a directed system. To construct the direct limit, begin by forming the coproduct over the elements of  $\mathcal{I}$ ,

$$\coprod_{i\in\mathcal{I}}X_i$$
.

There are maps in<sub>i</sub>:  $X_i \to \coprod X_i$ , but they are not yet compatible with the order relation in  $\mathcal{I}$ . Form a quotient of the coproduct to enforce that compatibility:

$$\lim_{i \in \mathcal{I}} X_i = \left( \coprod_{i \in \mathcal{I}} X_i \right) / \sim$$

where  $\sim$  is the equivalence relation generated by requiring that for any  $i \in \mathcal{I}$  and any  $x \in X_i$ ,

$$\operatorname{in}_{i}x \sim \operatorname{in}_{i}f_{ii}(x)$$
.

The process of forming the coproduct and the quotient will depend upon the category you are working in, and may not be possible. In sets, coproduct is disjoint union and the quotient just forms equivalence classes. In abelian groups, the coproduct is the direct sum and to form the quotient you divide by the subgroup generated by differences.

Direct limits and the tensor product are nicely related, and the way to see that is to use the adjunction with Hom that we started with today.

**Proposition 23.10.** Let  $\mathcal{I}$  be a direct set, and let  $M: \mathcal{I} \to \mathbf{Mod}_R$  be a  $\mathcal{I}$ -directed system of R-modules. There is a natural isomorphism

$$(\varinjlim_{I} M_{i}) \otimes_{R} N \cong \varinjlim_{I} (M_{i} \otimes_{R} N).$$

Proof. Let's verify that both sides satisfy the same universal property. A map from  $(\varinjlim_I M_i) \otimes_R N$  to an R-module L is the same thing as a linear map  $\varinjlim_I M_i \to \operatorname{Hom}_R(N, L)$ . This is the same as a compatible family of maps  $M_i \to \operatorname{Hom}_R(N, L)$ , which in turn is the same as a compatible family of maps  $M_i \otimes_R N \to L$ , which is the same as a linear map  $\varinjlim_I (M_i \otimes_R N) \to L$ .

Here's a lemma that lets us identify when a map to a constant functor is a direct limit.

**Lemma 23.11.** Let  $X : \mathcal{I} \to \mathbf{Ab}$  (or  $\mathbf{Mod}_R$ ). A map  $f : X \to c_L$  (given by  $f_i : X_i \to L$  for  $i \in \mathcal{I}$ ) is the direct limit if and only if:

- 1. For every  $x \in L$ , there exists an i and an  $x_i \in X_i$  such that  $f_i(x_i) = x$ .
- 2. Let  $x_i \in X_i$  be such that  $f_i(x_i) = 0$  in L. Then there exists some  $j \ge i$  such that  $f_{ij}(x_i) = 0$  in  $X_j$ .

*Proof.* Straightforward.

**Proposition 23.12.** The direct limit functor  $\varinjlim_I : \operatorname{Fun}(\mathcal{I}, \mathbf{Ab}) \to \mathbf{Ab}$  is exact. In other words, if  $X \xrightarrow{p} Y \xrightarrow{q} Z$  is an exact sequence of  $\mathcal{I}$ -directed systems (meaning that at every degree we get an exact sequence of abelian groups), then  $\varinjlim_I X \to \varinjlim_I Z$  is exact.

Proof. First of all,  $qp: X \to Z$  is zero, which is to say that it factors through the constant zero object, so  $\varinjlim_I X \to \varinjlim_I Z$  is certainly the zero map. Let  $y \in \varinjlim_I Y$ , and suppose y maps to 0 in  $\varinjlim_I Z$ . By condition (1) of Lemma 23.11, there exists i such that  $y = f_i(y_i)$  for some  $y_i \in Y_i$ . Then  $0 = q(y) = f_i q(y_i)$  because q is a map of direct systems. By condition (2), this means that there is  $j \geq i$  such that  $f_{ij}q(y_i) = 0$  in  $Z_j$ . So  $qf_{ij}y_i = 0$ , again because q is a map of direct systems. We have an element in  $Y_j$  that maps to zero under q, so there is some  $x_j \in X_j$  such that  $p(x_j) = y_j$ . Then  $f_j(x_j) \in \varinjlim_I X$  maps to y.

The exactness of the direct limit has many useful consequences. For example:

Corollary 23.13. Let  $i \mapsto C(i)$  be a directed system of chain complexes. Then there is a natural isomorphism

$$\lim_{i \in \mathcal{I}} H_*(C(i)) \to H_*(\varinjlim_{i \in \mathcal{I}} C(i)).$$

Putting together things we have just said:

Corollary 23.14. 
$$H_*(X; \mathbf{Q}) = H_*(X) \otimes \mathbf{Q}$$
.

So we can redefine the Betti numbers of a space X as

$$\beta_n = \dim_{\mathbf{Q}} H_n(X; \mathbf{Q})$$

and discuss the Euler characteristic entirely in terms of the rational vector spaces making up the rational homology of X.

## 24 Universal coefficient theorem

Suppose that we are given  $H_*(X; \mathbf{Z})$ . Can we compute  $H_*(X; \mathbf{Z}/2\mathbf{Z})$ ? This is non-obvious. Consider the map  $\mathbf{RP}^2 \to S^2$  that pinches  $\mathbf{RP}^1$  to a point. Now  $H_2(\mathbf{RP}^2; \mathbf{Z}) = 0$ , so in  $H_2$  this map is zero. But in  $\mathbf{Z}/2\mathbf{Z}$ -coefficients, in dimension 2, this map gives an isomorphism. This shows that there's no functorial determination of  $H_*(X; \mathbf{Z}/2)$  in terms of  $H_*(X; \mathbf{Z})$ ; the effect of a map in integral homology does not determine its effect in mod 2 homology. So how do we go between different coefficients?

Let R be a commutative ring and M an R-module, and suppose we have a chain complex  $C_*$  of R-modules. It could be the singular complex of a space, but it doesn't have to be. Let's compare  $H_n(C_*) \otimes M$  with  $H_n(C_* \otimes M)$ . (Here and below we'll just write  $\otimes$  for  $\otimes_R$ .) The latter thing gives homology with coefficients in M. How can we compare these two? Let's investigate, and build up conditions on R and  $C_*$  as we go along.

First, there's a natural map

$$\alpha: H_n(C_*) \otimes M \to H_n(C_* \otimes M)$$
,

sending  $[z] \otimes m$  to  $[z \otimes m]$ . We propose to find conditions under which it is injective. The map  $\alpha$  fits into a commutative diagram with exact columns like this:

Now,  $Z_n(C_* \otimes M)$  is a submodule of  $C_n \otimes M$ , but the map  $Z_n(C) \otimes M \to C_n \otimes M$  need not be injective . . . unless we impose more restrictions. If we can guarantee that it is, then a diagram chase shows that  $\alpha$  is a monomorphism.

So let's assume that R is a PID and that  $C_n$  is a free R-module for all n. Then the submodule  $B_{n-1}(C_*) \subseteq C_{n-1}$  is again free, so the short exact sequence

$$0 \longrightarrow Z_n(C_*) \longrightarrow C_n \longrightarrow B_{n-1}(C_*) \longrightarrow 0$$

$$\downarrow d \qquad \downarrow \qquad \qquad \downarrow C_{n-1}$$

splits. So  $Z_n(C_*) \to C_n$  is a split monomorphism, and hence  $Z_n(C_*) \otimes M \to C_n \otimes M$  is too.

In fact, a little thought shows that this argument produces a splitting of the map  $\alpha$ .

Now,  $\alpha$  is not always an isomorphism. But it certainly is if M = R, and it's compatible with direct sums, so it certainly is if M is free. The idea is now to resolve M by frees, and see where that idea takes us.

So let

$$0 \to F_1 \to F_0 \to M \to 0$$

be a free resolution of M. Again, we're using the assumption that R is a PID, to guarantee that  $\ker(F_0 \to M)$  is free. Again using the assumption that each  $C_n$  is free, we get a short exact sequence of chain complexes

$$0 \to C_* \otimes F_1 \to C_* \otimes F_0 \to C_* \otimes M \to 0$$
.

In homology, this gives a long exact sequence. Unsplicing it gives the left-hand column in the

following diagram.

$$coker(H_n(C_* \otimes F_1) \to H_n(C_* \otimes F_0)) \xrightarrow{\cong} coker(H_n(C_*) \otimes F_1 \to H_n(C_*) \otimes F_0))$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \downarrow \qquad \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow$$

The right hand column occurs because  $\alpha$  is an isomorphism when the module involved is free. But

$$\operatorname{coker}(H_n(C_*) \otimes F_1 \to H_n(C_*) \otimes F_0)) = H_n(C_*) \otimes M$$

and

$$\ker(H_{n-1}(C_*) \otimes F_1 \to H_{n-1}(C_*) \otimes F_0) = \operatorname{Tor}_1^R(H_{n-1}(C_*), M).$$

We have proved the following theorem.

**Theorem 24.1** (Universal Coefficient Theorem). Let R be a PID and  $C_*$  a chain complex of Rmodules such that  $C_n$  is free for all n. Then there is a natural short exact sequence of R-modules

$$0 \to H_n(C_*) \otimes M \xrightarrow{\alpha} H_n(C_* \otimes M) \xrightarrow{\partial} \operatorname{Tor}_1^R(H_{n-1}(C_*), M) \to 0$$

that splits (but not naturally).

**Example 24.2.** The pinch map  $\mathbf{RP}^2 \to S^2$  induces the following map of universal coefficient short exact sequences:

$$0 \longrightarrow H_2(\mathbf{RP}^2) \otimes \mathbf{Z}/2\mathbf{Z} \longrightarrow H_2(\mathbf{RP}^2; \mathbf{Z}/2\mathbf{Z}) \xrightarrow{\cong} \operatorname{Tor}_1(H_1(\mathbf{RP}^2), \mathbf{Z}/2\mathbf{Z}) \longrightarrow 0$$

$$\downarrow 0 \qquad \qquad \downarrow \cong \qquad \qquad \downarrow 0$$

$$0 \longrightarrow H_2(S^2) \otimes \mathbf{Z}/2\mathbf{Z} \xrightarrow{\cong} H_2(S^2; \mathbf{Z}/2\mathbf{Z}) \longrightarrow \operatorname{Tor}_1(H_1(S^2), \mathbf{Z}/2\mathbf{Z}) \longrightarrow 0$$

This shows that the splitting of the universal coefficient short exact sequence cannot be made natural, and it explains the mystery that we began with.

**Exercise 24.3.** The hypotheses are essential. Construct two counterexamples: one with  $R = \mathbf{Z}$  but in which the groups in the chain complex are not free, and one in which  $R = k[d]/d^2$  and the modules in  $C_*$  are free over R.

## 25 Künneth and Eilenberg-Zilber

We want to compute the homology of a product. Long ago, in Lecture 7, we constructed a bilinear map  $S_p(X) \times S_q(Y) \to S_{p+q}(X \times Y)$ , called the cross product. So we get a linear map  $S_p(X) \otimes S_q(Y) \to S_{p+q}(X \times Y)$ , and it satisfies the Leibniz formula, i.e.,  $d(x \times y) = dx \times y + (-1)^p x \times dy$ . The method we used works with any coefficient ring, not just the integers.

**Definition 25.1.** Let  $C_*, D_*$  be two chain complexes. Their tensor product is the chain complex with

$$(C_* \otimes D_*)_n = \bigoplus_{p+q=n} C_p \otimes D_q.$$

The differential  $(C_* \otimes D_*)_n \to (C_* \otimes D_*)_{n-1}$  sends  $C_p \otimes D_q$  into the submodule  $C_{p-1} \otimes D_q \bigoplus C_p \otimes D_{q-1}$  by

$$x \otimes y \mapsto dx \otimes y + (-1)^p x \otimes dy$$
.

So the cross product is a map of chain complexes  $S_*(X) \otimes S_*(Y) \to S_*(X \times Y)$ . There are two questions:

- (1) Is this map an isomorphism in homology?
- (2) How is the homology of a tensor product of chain complexes related to the tensor product of their homologies?

It's easy to see what happens in dimension zero, because  $\pi_0(X) \times \pi_0(Y) = \pi_0(X \times Y)$  implies that  $H_0(X) \otimes H_0(Y) \xrightarrow{\cong} H_0(X \times Y)$ .

Let's dispose of the purely algebraic question (2) first.

**Theorem 25.2.** Let R be a PID and  $C_*$ ,  $D_*$  be chain complexes of R-modules. Assume that  $C_n$  is a free R-module for all n. There is a short exact sequence

$$0 \to \bigoplus_{p+q=n} H_p(C) \otimes H_q(D) \to H_n(C_* \otimes D_*) \to \bigoplus_{p+q=n-1} \operatorname{Tor}_1^R(H_p(C), H_q(D)) \to 0$$

natural in these data, that splits (but not naturally).

*Proof.* This is exactly the same as the proof for the UCT. It's a good idea to work through this on your own.  $\Box$ 

Corollary 25.3. Let R be a PID and assume  $C'_n$  and  $C_n$  are R free for all n. If  $C'_* \to C_*$  and  $D'_* \to D_*$  are homology isomorphisms then so is  $C'_* \otimes D'_* \to C_* \otimes D_*$ .

Our attack on question (1) is via the method of "acyclic models." This is really a special case of the Fundamental Theorem of Homological Algebra, Theorem 22.1.

**Definition 25.4.** Let  $\mathcal{C}$  be a category, and fix a set  $\mathcal{M}$  of objects in  $\mathcal{C}$ , to be called the "models." A functor  $F:\mathcal{C}\to \mathbf{Ab}$  is  $\mathcal{M}$ -free if it is the free abelian group generated by a coproduct of corepresentable functors. That is, F is a direct sum of functors of the form  $\mathbf{Z}\mathcal{C}(M,-)$  where  $M\in\mathcal{M}$ .

**Example 25.5.** Since we are interested in the singular homology of a product of two spaces, it may be sensible to take as  $\mathcal{C}$  the category of ordered pairs of spaces,  $\mathcal{C} = \mathbf{Top}^2$ , and for  $\mathcal{M}$  the set of pairs of simplicies,  $\mathcal{M} = \{(\Delta^p, \Delta^q) : p, q \geq 0\}$ . Then

$$S_n(X\times Y)=\mathbf{Z}[\mathbf{Top}(\Delta^n\times X)\times\mathbf{Top}(\Delta^n,Y)]=\mathbf{ZTop}^2((\Delta^n,\Delta^n),(X,Y))\,.$$

is  $\mathcal{M}$ -free.

**Example 25.6.** With the same category and models,

$$(S_*(X) \otimes S_*(Y))_n = \bigoplus_{p+q=n} S_p(X) \otimes S_q(Y),$$

is  $\mathcal{M}$ -free, since the tensor product has as free basis the set

$$\coprod_{p+q=n} \operatorname{Sin}_p(X) \times \operatorname{Sin}_q(Y) = \coprod_{p+q=n} \operatorname{Top}^2((\Delta^p, \Delta^q), (X, Y)).$$

**Definition 25.7.** A natural transformation of functors  $\theta: F \to G$  is an  $\mathcal{M}$ -epimorphism if  $\theta_M: F(M) \to G(M)$  is a surjection of abelian groups for every  $M \in \mathcal{M}$ . A sequence of natural transformations is a composable pair  $G' \to G \to G''$  with trivial composition. Let K be the objectwise kernel of  $G \to G''$ . There is a factorization  $G' \to K$ . The sequence is  $\mathcal{M}$ -exact if  $G' \to K$  is a  $\mathcal{M}$ -epimorphism. Equivalently,  $G'(M) \to G(M) \to G''(M)$  is exact for all  $M \in \mathcal{M}$ .

Example 25.8. We claim that

$$\cdots \to S_n(X \times Y) \to S_{n-1}(X \times Y) \to \cdots \to S_0(X \times Y) \to H_0(X \times Y) \to 0$$

is  $\mathcal{M}$ -exact. Just plug in  $(\Delta^p, \Delta^q)$ : you get an exact sequence, since  $\Delta^p \times \Delta^q$  is contractible.

Example 25.9. The sequence

$$\cdots \to (S_*(X) \otimes S_*(Y))_n \to (S_*(X) \otimes S_*(Y))_{n-1} \to \cdots \to S_0(X) \otimes S_0(Y) \to H_0(X) \otimes H_0(Y) \to 0$$
. is also  $\mathcal{M}$ -exact, by Corollary 25.3.

The terms " $\mathcal{M}$ -free" and " $\mathcal{M}$ -exact" relate to each other in the expected way:

**Lemma 25.10.** Let C be a category with a set of models M and let  $F, G, G' : C \to \mathbf{Ab}$  be functors. Suppose that F is M-free, let  $G' \to G$  be a M-epimorphism, and let  $f : F \to G$  be any natural transformation. Then there is a lifting:

$$F \xrightarrow{\overline{f}} G'$$

$$F \xrightarrow{f} G$$

*Proof.* Clearly we may assume that  $F(X) = \mathbf{Z}\mathcal{C}(M,X)$ . Suppose that  $X = M \in \mathcal{M}$ . We get:

$$\begin{array}{c|c} G'(M) \\ \hline f_M & \nearrow & \downarrow \\ \mathbf{Z}\mathcal{C}(M,M) \xrightarrow{f_M} & G(M) \end{array}$$

Consider  $1_M \in \mathbf{Z}\mathcal{C}(M,M)$ . Its image  $f_M(1_M) \in G(M)$  is hit by some element in  $c_M \in G'(M)$ , since  $G' \to G$  is an  $\mathcal{M}$ -epimorphism. Define  $\overline{f}_M(1_M) = c_M$ .

Now we exploit naturality! Any  $\varphi: M \to X$  produces a commutative diagram

$$C(M, M) \xrightarrow{\overline{f}_M} G'(M)$$

$$\downarrow^{\varphi_*} \qquad \qquad \downarrow^{\varphi_*}$$

$$C(M, X) \xrightarrow{\overline{f}_X} G'(X)$$

Chase  $1_M$  around the diagram, to see what the value of  $\overline{f}_X(\varphi)$  must be:

$$\overline{f}_X(\varphi) = \overline{f}_X(\varphi_*(1_M)) = \varphi_*(\overline{f}_M(1_M)) = \varphi_*(c_M).$$

Now extend linearly. You should check that this does define a natural transformation.

This is precisely the condition required to prove the Fundamental Theorem of Homological Algebra. So we have the

**Theorem 25.11** (Acyclic Models). Let  $\mathcal{M}$  be a set of models in a category  $\mathcal{C}$ . Let  $\theta: F \to G$  be a natural transformation of functors from  $\mathcal{C}$  to  $\mathbf{Ab}$ . Let  $F_*$  and  $G_*$  be functors from  $\mathcal{C}$  to chain complexes, with augmentations  $F_0 \to F$  and  $G_0 \to G$ . Assume that  $F_n$  is  $\mathcal{M}$ -free for all n, and that  $G_* \to G \to 0$  is an  $\mathcal{M}$ -exact sequence. Then there is a unique chain homotopy class of chain maps  $F_* \to G_*$  covering  $\theta$ .

Corollary 25.12. Suppose furthermore that  $\theta$  is a natural isomorphism. If each  $G_n$  is  $\mathcal{M}$ -free and  $F_* \to F \to 0$  is an  $\mathcal{M}$ -exact sequence, then any natural chain map  $F_* \to G_*$  covering  $\theta$  is a natural chain homotopy equivalence.

Applying this to our category  $\mathbf{Top}^2$  with models as before, we get the following theorem that completes work we did in Lecture 7.

**Theorem 25.13** (Eilenberg-Zilber theorem). There are unique chain homotopy classes of natural chain maps:

$$S_*(X) \otimes S_*(Y) \leftrightarrows S_*(X \times Y)$$

covering the usual isomorphism

$$H_0(X) \otimes H_0(Y) \cong H_0(X \times Y)$$
,

and they are natural chain homotopy inverses.

Corollary 25.14. There is a canonical natural isomorphism  $H(S_*(X) \otimes S_*(Y)) \cong H_*(X \times Y)$ .

Combining this theorem with the algebraic Künneth theorem, we get:

**Theorem 25.15** (Künneth theorem). Take coefficients in a PID R. There is a short exact sequence

$$0 \to \bigoplus_{p+q=n} H_p(X) \otimes_R H_q(Y) \to H_n(X \times Y) \to \bigoplus_{p+q=n-1} \operatorname{Tor}_1^R(H_p(X), H_q(Y)) \to 0$$

natural in X, Y. It splits as R-modules, but not naturally.

**Example 25.16.** If R = k is a field, every module is free, so the Tor term vanishes, and you get a Künneth *isomorphism*:

$$\times: H_*(X;k) \otimes_k H_*(Y;k) \xrightarrow{\cong} H_*(X \times Y;k)$$

This is rather spectacular. For example, what is  $H_*(\mathbf{RP}^3 \times \mathbf{RP}^3; k)$ , where k is a field? Well, if k has characteristic different from 2,  $\mathbf{RP}^3$  has the same homology as  $S^3$ , so the product has the same homology as  $S^3 \times S^3$ : the dimensions are 1, 0, 0, 2, 0, 0, 1. If char k = 2, on the other hand, the cohomology modules are either 0 or k, and we need to form the graded tensor product:

$$k k k k k k k k k k k k k k k k k k k$$

so the dimensions of the homology of the product are 1, 2, 3, 4, 3, 2, 1.

The palindromic character of this sequence will be explained by Poincaré duality. Let's look also at what happens over the integers. Then we have the table of tensor products

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

There is only one nonzero Tor group, namely

$$\operatorname{Tor}_{1}^{\mathbf{Z}}(H_{1}(\mathbf{RP}^{3}), H_{1}(\mathbf{RP}^{3})) = \mathbf{Z}/2\mathbf{Z}.$$

Putting this together, we get the groups

$$\begin{array}{c|c} H_0 & {\bf Z} \\ H_1 & {\bf Z}/2{\bf Z} \oplus {\bf Z}/2{\bf Z} \\ H_2 & {\bf Z}/2{\bf Z} \\ H_3 & {\bf Z} \oplus {\bf Z} \oplus {\bf Z}/2{\bf Z} \\ H_4 & {\bf Z}/2{\bf Z} \oplus {\bf Z}/2{\bf Z} \\ H_5 & 0 \\ H_6 & {\bf Z} \end{array}$$

The failure of perfect symmetry here is interesting, and will also be explained by Poincaré duality.

# Chapter 3

# Cohomology and duality

#### 26 Coproducts, cohomology

The next topic is cohomology. This is like homology, but it's a contravariant rather than covariant functor of spaces. There are three reasons why you might like a contravariant functor.

- (1) Many geometric contructions pull back; that is, they behave contravariantly. For example, if I have some covering space  $\widetilde{X} \to X$  and a map  $f: Y \to X$ , I get a pullback covering space  $f^*\widetilde{X}$ . A better example is vector bundles (that we'll talk about in 18.906) they don't push out, they pullback. So if we want to study them by means of "natural" invariants, these invariants will have to lie in a (hopefully computable) group that also behaves contravariantly. This will lead to the theory of characteristic classes.
- (2) The structure induced by the diagonal map from a space to its square induces stucture in contravariant functors that is more general and easier to study.
- (3) Cohomology turns out to be the target of the Poincaré duality map.

Let's elaborate on point (2). Every space has a diagonal map

$$X \xrightarrow{\Delta} X \times X$$
.

This induces a map  $H_*(X;R) \to H_*(X \times X;R)$ , for any coefficient group R. Now, if R is a ring, we get a cross product map

$$\times: H_*(X;R) \otimes_R H_*(X;R) \to H_*(X \times X;R)$$
.

If R is a PID, the Künneth Theorem tells us that this map is a monomorphism. If the remaining term in the Künneth Theorem is zero, the cross product is an isomorphism. So if  $H_*(X;R)$  is free over R (or even just flat over R), we get a "diagonal" or "coproduct"

$$\Delta: H_*(X;R) \to H_*(X;R) \otimes_R H_*(X;R)$$
.

If R is a field, this map is universally defined, and natural in X.

This kind of structure is unfamiliar, and at first seems a bit strange. After all, the tensor product is defined by a universal property for maps *out* of it; maps *into* it just are what they are.

Still, it's often useful, and we pause to fill in some of its properties.

**Definition 26.1.** Let R be a ring. A *(graded) coalgebra* over R is a (graded) R-module M equipped with a "comultiplication"  $\Delta: M \to M \otimes_R M$  and a "counit" map  $\varepsilon: M \to R$  such that the following

diagrams commute.

It is *commutative* if in addition

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

commutes, where  $\tau(x \otimes y) = (-1)^{|x| \cdot |y|} y \otimes x$  is the twist map.

Using acyclic models, you saw for homework that the Künneth map is associative and commutative: The diagrams

$$S_{*}(X) \otimes S_{*}(Y) \otimes S_{*}(Z) \xrightarrow{\times \otimes 1} S_{*}(X \times Y) \otimes S_{*}(Z)$$

$$\downarrow^{1 \otimes \times} \qquad \qquad \downarrow^{\times}$$

$$S_{*}(X) \otimes S_{*}(Y \times Z) \xrightarrow{\times} S_{*}(X \times Y \times Z)$$

and

$$S_*(X) \otimes S_*(Y) \xrightarrow{\tau} S_*(Y) \otimes S_*(X)$$

$$\downarrow^{\times} \qquad \qquad \downarrow^{\times}$$

$$S_*(X \times Y) \xrightarrow{T_*} S_*(Y \times X)$$

commute up to natural chain homotopy, where  $\tau$  is as defined above on the tensor product and  $T: X \times Y \to Y \times X$  is the swap map. Similar diagrams apply to the standard comparison map for the homology of tensor products of chain complexes,

$$\mu: H_*(C) \otimes H_*(D) \to H_*(C \otimes D)$$
,

and the result is this:

Corollary 26.2. Suppose R is a PID and  $H_*(X;R)$  is free over R. Then  $H_*(X;R)$  has the natural structure of a commutative graded coalgebra over R.

We could now just go on and talk about coalgebras. But they are less familiar, and available only if  $H_*(X;R)$  is free over R. So instead we're going to dualize, talk about cohomology, and get an algebra structure. Some say that cohomology is better because you have algebras, but that's more of a sociological statement than a mathematical one.

Let's get on with it.

**Definition 26.3.** Let N be an abelian group. A singular n-cochain on X with values in N is a function  $Sin_n(X) \to N$ .

If N is an R-module, then I can extend linearly to get an R-module homomorphism  $S_n(X;R) \to N$ .

#### Notation 26.4. Write

$$S^n(X; N) = \operatorname{Map}(\operatorname{Sin}_n(X), N) = \operatorname{Hom}_R(S_n(X; R), N).$$

This is going to give us something contravariant, that's for sure. But we haven't quite finished dualizing. The differential  $d: S_{n+1}(X;R) \to S_n(X;R)$  induces a "coboundary map"

$$d: S^n(X; N) \to S^{n+1}(X; N)$$

defined by

$$(df)(\sigma) = (-1)^{n+1} f(d\sigma).$$

The sign is a little strange, and we'll see an explanation in a minute. Anyway, we get a "cochain complex," with a differential that *increases* degree by 1. We still have  $d^2 = 0$ , since

$$(d^2 f)(\sigma) = \pm d(f(d\sigma)) = \pm f(d^2 \sigma) = \pm f(0) = 0$$

so we can still take homology of this cochain complex.

**Definition 26.5.** The nth singular cohomology group of X with coefficients in an abelian group N is

$$H^{n}(X; N) = \frac{\ker(S^{n}(X; N) \to S^{n+1}(X; N))}{\operatorname{im}(S^{n-1}(X; N) \to S^{n}(X; N))}.$$

If N is an R-module, then  $H^n(X; N)$  is again an R-module.

Let's first compute  $H^0(X; N)$ . A 0-cochain is a function  $Sin_0(X) \to N$ ; that is, a function (not required to be continuous!)  $f: X \to N$ . To compute df, take a 1-simplex  $\sigma: \Delta^1 \to X$  and evaluate f on its boundary:

$$(df)(\sigma) = -f(d\sigma) = -f(\sigma(e_0) - \sigma(e_1)) = f(\sigma(e_1)) - f(\sigma(e_0)).$$

So f is a co*cycle* if it's constant on path components. That is to say:

**Lemma 26.6.**  $H^0(X; N) = \text{Map}(\pi_0(X), N)$ .

Warning 26.7.  $S^n(X; \mathbf{Z}) = \operatorname{Map}(\operatorname{Sin}_n(X); \mathbf{Z}) = \prod_{\operatorname{Sin}_n(X)} \mathbf{Z}$ , which is probably an uncountable product. An awkward fact is that this is never free abelian.

The first thing a cohomology class does is to give a linear functional on homology, by "evaluation." Let's spin this out a bit.

We want to tensor together cochains and chains. But to do that we should make the differential in  $S^*(X)$  go down, not up. Just as a notational matter, let's write

$$S_{-n}^{\vee}(X;N) = S^n(X;N)$$

and define a differential  $d: S_{-n}^{\vee}(X) \to S_{-n-1}^{\vee}(X)$  to be the differential  $d: S^{n}(X) \to S^{n+1}(X)$ . Now  $S_{*}^{\vee}(X)$  is a chain complex, albeit a negatively graded one. Form the graded tensor product, with

$$\left(S_*^{\vee}(X;N)\otimes S_*(X)\right)_n = \bigoplus_{p+q=n} S_p^{\vee}(X;N)\otimes S_q(X).$$

Now evaluation is a map of graded abelian groups

$$\langle -, - \rangle : S_*^{\vee}(X; N) \otimes S_*(X) \to N$$
,

where N is regarded as a chain complex concentrated in degree 0. We would like this map to be a chain map. So let  $f \in S^n(X; N)$  and  $\sigma \in S_n(X)$ , and compute

$$0 = d\langle f, \sigma \rangle = \langle df, \sigma \rangle + (-1)^n \langle f, d\sigma \rangle.$$

This forces

$$(df)(\sigma) = \langle df, \sigma \rangle = -(-1)^n f(d\sigma),$$

explaining the odd sign in our definition above.

Here's the payoff: There's a natural map

$$H_{-n}(S_*^{\vee}(X;N)) \otimes H_n(S_*(X)) \xrightarrow{\mu} H_0\left(S_*^{\vee}(X;N) \otimes S_*(X)\right) \to N$$

This gives us the Kronecker pairing

$$\langle -, - \rangle : H^n(X; N) \otimes H_n(X) \to N$$
.

We can develop the properties of cohomology in analogy with properties of homology. For example: If  $A \subseteq X$ , there is a restriction map  $S^n(X;N) \to S^n(A;N)$ , induced by the injection  $\operatorname{Sin}_n(A) \hookrightarrow \operatorname{Sin}_n(X)$ . And as long as A is nonempty, we can split this injection, so any function  $\operatorname{Sin}_n(A) \to N$  extends to  $\operatorname{Sin}_n(X) \to N$ . This means that  $S^n(X;N) \to S^n(A;N)$  is surjective. (This is the case if  $A = \emptyset$ , as well!)

**Definition 26.8.** The relative n-cochain group with coefficients in N is

$$S^n(X,A;N) = \ker (S^n(X;N) \to S^n(A;N))$$
.

This defines a sub cochain complex of  $S^*(X; N)$ , and we define

$$H^{n}(X, A; N) = H^{n}(S^{*}(X, A; N)).$$

The short exact sequence of cochain complexes

$$0 \to S^*(X, A; N) \to S^*(X; N) \to S^*(A; N) \to 0$$

induces the long exact cohomology sequence

$$H^{1}(X,A;N) \xrightarrow{\delta} H^{1}(X;N) \xrightarrow{\delta} H^{1}(A;N)$$

$$\downarrow \delta$$

$$H^{0}(X,A;N) \xrightarrow{\delta} H^{0}(X;N) \xrightarrow{\delta} H^{0}(A;N)$$

27. EXT AND UCT 73

#### 27 Ext and UCT

Let R be a ring (probably a PID) and N an R-module. The singular cochains on X with values in N.

$$S^*(X; N) = \operatorname{Map}(\operatorname{Sin}_*(X), N),$$

then forms a cochain complex of R-modules. It is contravariantly functorial in X and covariantly functorial in N. The Kronecker pairing defines a map

$$H^n(X;N) \otimes_R H_n(X;R) \to N$$

whose adjoint

$$\beta: H^n(X; N) \to \operatorname{Hom}_R(H_n(X; R), N)$$

gives us an estimate of the cohomology in terms of the homology of X. Here's how well it does:

**Theorem 27.1** (Mixed variance Universal Coefficient Theorem). Let R be a PID and N an R-module, and let  $C_*$  be a chain-complex of free R-modules. Then there is a short exact sequence of R-modules,

$$0 \to \operatorname{Ext}_R^1(H_{n-1}(C_*), N) \to H^n(\operatorname{Hom}_R(C_*, N)) \to \operatorname{Hom}_R(H_n(C_*), N) \to 0$$

natural in  $C_*$  and N, that splits (but not naturally).

Taking  $C_* = S_*(X; R)$ , we have the short exact sequence

$$0 \to \operatorname{Ext}_R^1(H_{n-1}(X;R),N) \to H^n(X;N) \xrightarrow{\beta} \operatorname{Hom}_R(H_n(X;R),N) \to 0$$

that splits, but not naturally. This also holds for relative cohomology.

What is this Ext?

The problem that arises is that  $\operatorname{Hom}_R(-,N):\operatorname{\mathbf{Mod}}_R\to\operatorname{\mathbf{Mod}}_R$  is not exact. Suppose I have an injection  $M'\to M$ . Is  $\operatorname{Hom}(M,N)\to\operatorname{Hom}(M',N)$  surjective? Does a map  $M\to N$  necessarily extend to a map  $M\to N$ ? No! For example,  $\mathbf{Z}/2\mathbf{Z}\hookrightarrow\mathbf{Z}/4\mathbf{Z}$  is an injection, but the identity map  $\mathbf{Z}/2\mathbf{Z}\to\mathbf{Z}/2\mathbf{Z}$  does not extend over  $\mathbf{Z}/4\mathbf{Z}$ .

On the other hand, if  $M' \xrightarrow{i} M \xrightarrow{p} M'' \to 0$  is an exact sequence of R-modules then

$$0 \to \operatorname{Hom}_R(M'', N) \to \operatorname{Hom}_R(M, N) \to \operatorname{Hom}_R(M', N)$$

is again exact. Check this statement!

Now homological algebra comes to the rescue to repair the failure of exactness. Pick a free resolution of M,

$$0 \leftarrow M \leftarrow F_0 \leftarrow F_2 \leftarrow \cdots$$
.

Apply Hom(-, N) to get a cochain complex

$$0 \to \operatorname{Hom}_R(F_0, N) \to \operatorname{Hom}_R(F_1, N) \to \operatorname{Hom}_R(F_2, N) \to \cdots$$

**Definition 27.2.**  $\operatorname{Ext}_R^n(M,N) = H^n(\operatorname{Hom}_R(F_*,N)).$ 

**Remark 27.3.** Ext is well-defined and functorial, by the Fundamental Theorem of Homological Algebra, Theorem 22.1. If M is free (or projective) then  $\operatorname{Ext}_R^n(M,-)=0$  for n>0, since we can take M as its own projective resolution. If R is a PID, then we can assume  $F_1=\ker(F_0\to M)$  and  $F_n=0$  for n>1, so  $\operatorname{Ext}_R^n=0$  if n>1. If R is a field, then  $\operatorname{Ext}_R^n=0$  for n>0.

**Example 27.4.** Let  $R = \mathbf{Z}$  and take  $M = \mathbf{Z}/k\mathbf{Z}$ . This admits a simple free resolution:  $0 \to \mathbf{Z} \xrightarrow{k} \mathbf{Z} \to \mathbf{Z}/k\mathbf{Z} \to 0$ . Apply  $\operatorname{Hom}(-,N)$  to it, and remember that  $\operatorname{Hom}(\mathbf{Z},N) = N$ , to get the very short cochain complex, with entries in dimensions 0 and 1:

$$0 \to N \xrightarrow{k} N \to 0$$
.

Taking homology gives us

$$\operatorname{Hom}(\mathbf{Z}/k\mathbf{Z}, N) = \ker(k|N) \quad \operatorname{Ext}^{1}(\mathbf{Z}/k\mathbf{Z}, N) = N/kN.$$

Proof of Theorem 27.1. First of all, we can't just copy the proof (in Lecture 24) of the homology universal coefficient theorem, since  $\operatorname{Ext}_R^1(-,R)$  is not generally trivial.

Instead, we start by thinking about what an n-cocycle in  $\operatorname{Hom}_R(C_*, N)$  is: it's a homomorphism  $C_n \to N$  such that the composite  $C_{n+1} \to C_n \to N$  is trivial. Write  $B_n \subseteq C_n$  for the submodule of boundaries. We have a homomorphism that kills  $B_n$ ; that is,

$$Z^n(\operatorname{Hom}_R(C_*, N)) \xrightarrow{\cong} \operatorname{Hom}_R(C_n/B_n, N)$$
.

Now  $H_n(C_*)$  (which we'll abbreviate as  $H_n$ ) is the submodule  $Z_n/B_n$  of  $C_n/B_n$ ; we have an exact sequence

$$0 \to H_n \to C_n/B_n \to B_{n-1} \to 0$$
.

Apply  $\operatorname{Hom}_R(-,N)$  to this short exact sequence. The result is again short exact, because  $B_{n-1}$  is a submodule of the free R-module  $C_{n-1}$  and hence is free. This gives us the bottom line in the map of short exact sequences

$$0 \longrightarrow B^{n} \operatorname{Hom}_{R}(C_{*}, N) \longrightarrow Z^{n} \operatorname{Hom}_{R}(C_{*}, N) \longrightarrow H^{n}(\operatorname{Hom}_{R}(C_{*}, N)) \longrightarrow 0$$

$$\downarrow \qquad \qquad \downarrow \cong \qquad \qquad \downarrow \beta$$

$$0 \longrightarrow \operatorname{Hom}_{R}(B_{n-1}, N) \longrightarrow \operatorname{Hom}_{R}(C_{n}/B_{n}, N) \longrightarrow \operatorname{Hom}_{R}(H_{n}, N) \longrightarrow 0$$

The map  $\beta$  is the one we started with. The snake lemma now shows that it is surjective and that

$$\ker \beta \cong \operatorname{coker}(B^n \operatorname{Hom}_R(C_*, N) \to \operatorname{Hom}_R(B_{n-1}, N))$$
.

An element of  $B^n \operatorname{Hom}_R(C_*, N)$  is a map  $C_n \to N$  that factors as  $C_n \xrightarrow{d} C_{n-1} \to N$ . The observation is now that this is the same as factoring as  $C_n \xrightarrow{d} Z_{n-1} \to N$ ; once this factorization has been achieved, the map  $Z_{n-1} \to N$  automatically extends to all of  $C_{n-1}$ . This is because  $Z_{n-1} \subseteq C_{n-1}$  as a direct summand: the short exact sequence

$$0 \to Z_{n-1} \to C_{n-1} \to B_{n-2} \to 0$$

splits since  $B_{n-2}$  is free. Consequently we can rewrite our forumula for ker  $\beta$  as

$$\ker \beta \cong \operatorname{coker}(\operatorname{Hom}_R(Z_{n-1}, N) \to \operatorname{Hom}_R(B_{n-1}, N))$$

But after all

$$0 \leftarrow H_{n-1} \leftarrow Z_{n-1} \leftarrow B_{n-1} \leftarrow 0$$

is a free resolution, so this cokernel is precisely  $\operatorname{Ext}_{R}^{1}(H_{n-1}(C_{*}), N)$ .

27. EXT AND UCT 75

#### Question 27.5. Why is Ext called Ext?

**Answer:** It classifies extensions. Let R be a commutative ring, and let M, N be two R-modules. I can think about "extensions of M by N," that is, short exact sequences of the form

$$0 \to N \to L \to M \to 0$$
.

For example, I have two extensions of  $\mathbb{Z}/2\mathbb{Z}$  by  $\mathbb{Z}/2\mathbb{Z}$ :

$$0 \to \mathbf{Z}/2\mathbf{Z} \to \mathbf{Z}/2\mathbf{Z} \oplus \mathbf{Z}/2\mathbf{Z} \to \mathbf{Z}/2\mathbf{Z} \to 0$$

and

$$0 \rightarrow \mathbf{Z}/2\mathbf{Z} \rightarrow \mathbf{Z}/4\mathbf{Z} \rightarrow \mathbf{Z}/2\mathbf{Z} \rightarrow 0$$
.

We'll say that two extensions are equivalent if there's a map of short exact sequences between them that is the identity on N and on M. The two extensions above aren't equivalent, for example.

Another definition of  $\operatorname{Ext}_R^1(M,N)$  is: the set of extensions like this modulo this notion of equivalence. The zero in the group is the split extension.

The universal coefficient theorem is useful in transferring properties of homology to cohomology. For example, if  $f: X \to Y$  is a map that induces an isomorphism in  $H_*(-; R)$ , then it induces an isomorphism in  $H^*(-; N)$  for any R-module N, at least provided that R is a PID. (This is in fact true in general.)

Cohomology satisfies the appropriate analogues of the Eilenberg-Steenrod axioms.

**Homotopy invariance:** If  $f_0 \simeq f_1 : (X, A) \to (Y, B)$ , then

$$f_0^* = f_1^* : H^*(Y, B; N) \to H^*(X, A; N)$$
.

I can't use the UCT to address this. But we established a chain homotopy  $f_{0,*} \simeq f_{1,*} : S_*(X, A) \to S_*(Y, B)$ , and applying Hom converts chain homotopies to cochain homotopies.

**Excision:** If  $U \subseteq A \subseteq X$  such that  $\overline{U} \subseteq \text{Int}(A)$ , then  $H^*(X, A; N) \to H^*(X - U, A - U; N)$  is an isomorphism. This follows from excision in homology and the mixed variance UCT.

Milnor axiom: The inclusions induce an isomorphism

$$H^*(\coprod_{\alpha} X_{\alpha}; N) \to \prod_{\alpha} H^*(X_{\alpha}; N)$$
.

As a result, it enjoys the fruit of these axioms, such as:

The Mayer-Vietoris sequence: If  $A, B \subseteq X$  are such that their interiors cover X, then there is a long exact sequence

$$H^{n+1}(X;N) \xrightarrow{\longrightarrow} H^{n}(A;N) \oplus H^{n}(B;N) \xrightarrow{\longrightarrow} H^{n}(A \cap B;N)$$

$$\cdots \xrightarrow{\longrightarrow} H^{n-1}(A \cap B;N)$$

#### 28 Products in cohomology

We'll talk about the cohomology cross product first. The first step is to produce a map on chains that goes in the reverse direction from the cross product we constructed in Lecture 7.

Construction 28.1. For each pair of natural numbers p, q, we will define a natural homomorphism

$$\alpha: S_{p+q}(X \times Y) \to S_p(X) \otimes S_q(Y)$$
.

It suffices to define this on simplices, so let  $\sigma: \Delta^{p+q} \to X \times Y$  be a singular (p+q)-simplex in the product. Let

$$\sigma_1 = \operatorname{pr}_1 \circ \sigma : \Delta^{p+q} \to X \quad \text{and} \quad \sigma_2 = \operatorname{pr}_2 \circ \sigma : \Delta^{p+q} \to Y$$

be the two coordinates of  $\sigma$ . I have to produce a p-simplex in X and a q-simplex in Y.

First define two maps in the simplex category:

- the "front face"  $\alpha_p:[p]\to[p+q]$ , sending i to i for  $0\leq i\leq p$ , and
- the "back face"  $\omega_q:[q]\to[p+q]$ , sending j to j+p for  $0\leq j\leq q$ .

Use the same symbols for the affine extensions to maps  $\Delta^p \to \Delta^{p+q}$  and  $\Delta^q \to \Delta^{p+q}$ . Now let

$$\alpha(\sigma) = (\sigma_1 \circ \alpha_p) \otimes (\sigma_2 \circ \omega_q).$$

This seems like a very random construction; but it works! It's named after two great early algebraic topologists, James W. Alexander and Hassler Whitney. For homework, you will show that these maps assemble into a chain map

$$\alpha: S_*(X \times Y) \to S_*(X) \otimes S_*(Y)$$
.

This works over any ring R. To get a map in cohomology, we should form a composite

$$S^{p}(X;R) \otimes_{R} S^{q}(Y;R) \to \operatorname{Hom}_{R}(S_{p}(X;R) \otimes_{R} S_{q}(Y;R),R) \xrightarrow{\alpha^{*}} \operatorname{Hom}_{R}(S_{p+q}(X \times Y;R),R) = S^{p+q}(X \times Y;R).$$

The first map goes like this: Given chain complexes  $C_*$  and  $D_*$ , we can consider the dual cochain complexes  $\operatorname{Hom}_R(C_*, R)$  and  $\operatorname{Hom}_R(D_*, R)$ , and construct a chain map

$$\operatorname{Hom}_R(C_*,R) \otimes_R \operatorname{Hom}_R(D_*,R) \to \operatorname{Hom}_R(C_* \otimes_R D_*,R)$$

by

$$f \otimes g \mapsto \begin{cases} (x \otimes y \mapsto (-1)^{pq} f(x) g(y)) & |x| = |f| = p, \ |y| = |g| = q \\ 0 & \text{otherwise.} \end{cases}$$

Again, I leave it to you to check that this is a cochain map.

Altogether, we have constructed a natural cochain map

$$\times: S^p(X) \otimes S^q(Y) \to S^{p+q}(X \times Y)$$

From this, we get a homomorphism

$$H^*(S^*(X) \otimes S^*(Y)) \to H^*(X \times Y)$$
.

I'm not quite done! As in the Künneth theorem, there is an evident natural map

$$\mu: H^*(X) \otimes H^*(Y) \to H^*(S^*(X) \otimes S^*(Y))$$
.

The composite

$$\times: H^*(X) \otimes H^*(Y) \to H^*(S^*(X) \otimes S^*(Y)) \to H^*(X \times Y)$$

is the cohomology cross product.

It's not very easy to do computations with this, directly. We'll find indirect means. Let me make some points about this construction, though.

**Definition 28.2.** The *cup product* is the map obtained by taking X = Y and composing with the map induced by the diagonal  $\Delta: X \to X \times X$ :

$$\cup: H^p(X) \otimes H^q(X) \xrightarrow{\times} H^{p+q}(X \times X) \xrightarrow{\Delta^*} H^{p+q}(X),.$$

These definitions make good sense with any ring for coefficients.

Let's explore this definition in dimension zero. I claim that  $H^0(X;R) \cong \operatorname{Map}(\pi_0(X),R)$  as rings. When p=q=0, both  $\alpha_0$  and  $\omega_0$  are the identity maps, so we are just forming the pointwise product of functions.

There's a distinguished element in  $H^0(X)$ , namely the the function  $\pi_0(X) \to R$  that takes on the value 1 on every path component. This is the identity for the cup product. This comes about because when p=0 in our above story, then  $\alpha_0$  is just including the 0-simplex, and  $\omega_q$  is the identity.

The cross product is also associative, even on the chain level.

**Proposition 28.3.** Let  $f \in S^p(X)$ ,  $g \in S^q(Y)$ , and  $h \in S^r(Z)$ , and let  $\sigma : \Delta^{p+q+r} \to X \times Y \times Z$  be any simplex. Then

$$((f \times g) \times h)(\sigma) = (f \times (g \times h))(\sigma).$$

*Proof.* Write  $\sigma_{12}$  for the composite of  $\sigma$  with the projection map  $X \times Y \times Z \to X \times Y$ , and so on. Then

$$((f \times g) \times h)(\sigma) = (-1)^{(p+q)r} (f \times g)(\sigma_{12} \circ \alpha_{p+q}) h(\sigma_3 \circ \omega_r).$$

But

$$(f \times g)(\sigma_{12} \circ \alpha_{p+q}) = (-1)^{pq} f(\sigma_1 \circ \alpha_p) g(\sigma_2 \circ \mu_q),$$

where  $\mu_q$  is the "middle face," sending  $\ell$  to  $\ell+p$  for  $0 \leq \ell \leq q$ . In other words,

$$((f \times g) \times h)(\sigma) = (-1)^{pq+qr+rp} f(\sigma_1 \circ \alpha_p) g(\sigma_2 \circ \mu_q) h(\sigma_3 \circ \omega_r).$$

I've used associativity of the ring. You get exactly the same thing when you expand  $(f \times (g \times h))(\sigma)$ , so the cross product is associative.

Of course the diagonal map is "associative," too, and we find that the cup product is associative:

$$(\alpha \cup \beta) \cup \gamma = \alpha \cup (\beta \cup \gamma).$$

## 29 Cup product, continued

We have constructed an explicit map  $S^p(X) \otimes S^q(Y) \xrightarrow{\times} S^{p+q}(Y)$  via:

$$(f \times g)(\sigma) = (-1)^{pq} f(\sigma_1 \circ \alpha_p) g(\sigma_2 \circ \omega_q)$$

where  $\alpha_p: \Delta^p \to \Delta^{p+q}$  sends i to i for  $0 \le i \le p$  and  $\omega_q: \Delta^q \to \Delta^{p+q}$  sends j to j+p for  $0 \le j \le q$ . This is a cochain map; it induces a "cross product"  $H^p(X) \otimes H^q(Y) \to H_{p+q}(X \times Y)$ , and, by composing with the map induced by the diagonal embedding, the "cup product"

$$\cup: H^p(X) \otimes H^q(X) \to H^{p+q}(X)$$
.

We formalize the structure that this product imposes on cohomology.

**Definition 29.1.** Let R be a commutative ring. A graded R-algebra is a graded R-module  $\ldots, A_{-1}, A_0, A_1, A_2, \ldots$  equipped with maps  $A_p \otimes_R A_q \to A_{p+q}$  and a map  $\eta: R \to A_0$  that make the following diagram commute.

A graded R-algebra A is commutative if the following diagram commutes:

where  $\tau(x \otimes y) = (-1)^{pq} y \otimes x$ .

We claim that  $H^*(X; R)$  forms a commutative graded R-algebra under the cup product. This is nontrivial. On the cochain level, this is clearly not graded commutative. We're going to have to work hard – in fact, so hard that you're going to do it for homework. What needs to be checked is that the following diagram commutes up to natural chain homotopy.

$$S_{*}(X \times Y) \xrightarrow{T_{*}} S_{*}(Y \times X)$$

$$\downarrow^{\alpha_{X,Y}} \qquad \qquad \downarrow^{\alpha_{Y,X}}$$

$$S_{*}(X) \otimes_{R} S_{*}(Y) \xrightarrow{\tau} S_{*}(Y) \otimes_{R} S_{*}(X)$$

Acyclic models helps us prove things like this.

You might hope that there is some way to produce a commutative product on a chain complex modeling  $H^*(X)$ . With coefficients in  $\mathbb{Q}$ , this is possible, by a construction due to Dennis Sullivan. With coefficients in a field of nonzero characteristic, it is not possible. Steenrod operations provide the obstruction.

My goal now is to compute the cohomology algebras of some spaces. Some spaces are easy! There is no choice for the product structure on  $H^*(S^n)$ , for example. (When n = 0, we get a free module of rank 2 in dimension 0. This admits a variety of commutative algebra structures; but we

have already seen that  $H^0(S^0) = \mathbf{Z} \times \mathbf{Z}$  as an algebra.) Maybe the next thing to try is a product of spheres. More generally, we should ask whether there is an algebra structure on  $H^*(X) \otimes H^*(Y)$  making the cross product an algebra map. If A and B are two graded algebras, there is a natural algebra structure on  $A \otimes B$ , given by  $1 = 1 \otimes 1$  and

$$(a' \otimes b')(a \otimes b) = (-1)^{|b'| \cdot |a|} a'a \otimes b'b.$$

If A and B are commutative, then so is  $A \otimes B$  with this algebra structure.

Proposition 29.2. The cohomology cross product

$$\times: H^*(X) \otimes H^*(Y) \to H^*(X \times Y)$$

is an R-algebra homomorphism.

*Proof.* I have diagonal maps  $\Delta_X: X \to X \times X$  and  $\Delta_Y: Y \to Y \times Y$ . The diagonal on  $X \times Y$  factors as

$$X \times Y \xrightarrow{\Delta_{X \times Y}} X \times Y \times X \times Y$$

$$X \times X \times Y \times Y.$$

Let  $\alpha_1, \alpha_2 \in H^*(X)$  and  $\beta_1, \beta_2 \in H^*(Y)$ . Then  $\alpha_1 \times \beta_1, \alpha_2 \times \beta_2 \in H^*(X \times Y)$ , and I want to calculate  $(\alpha_1 \times \beta_1) \cup (\alpha_2 \times \beta_2)$ . Let's see:

$$(\alpha_1 \times \beta_1) \cup (\alpha_2 \times \beta_2) = \Delta_{X \times Y}^* (\alpha_1 \times \beta_1 \times \alpha_2 \times \beta_2)$$

$$= (\Delta_X \times \Delta_Y)^* (1 \times T \times 1)^* (\alpha_1 \times \beta_1 \times \alpha_2 \times \beta_2)$$

$$= (\Delta_X \times \Delta_Y)^* (\alpha_1 \times T^* (\beta_1 \times \alpha_2) \times \beta_2)$$

$$= (-1)^{|\alpha_2| \cdot |\beta_1|} (\Delta_X \times \Delta_Y)^* (\alpha_1 \times \alpha_2 \times \beta_1 \times \beta_2).$$

Naturality of the cross product asserts that the diagram

$$H^{*}(X \times Y) \xleftarrow{\times_{X \times Y}} H^{*}(X) \otimes_{R} H^{*}(Y)$$

$$(\Delta_{X} \times \Delta_{Y})^{*} \uparrow \qquad \qquad \Delta_{X}^{*} \otimes \Delta_{Y}^{*} \uparrow$$

$$H^{*}(X \times X \times Y \times Y) \xleftarrow{\times_{X \times X, Y \times Y}} H^{*}(X \times X) \otimes H^{*}(Y \times Y).$$

commute. We learn:

$$(\alpha_1 \times \beta_1) \cup (\alpha_2 \times \beta_2) = (-1)^{|\alpha_2| \cdot |\beta_1|} (\Delta_X \times \Delta_Y)^* (\alpha_1 \times \alpha_2 \times \beta_1 \times \beta_2)$$
$$= (-1)^{|\alpha_2| \cdot |\beta_1|} (\alpha_1 \cup \alpha_2) \times (\beta_1 \cup \beta_2).$$

That's exactly what we wanted.

We will see later, in Theorem 33.3, that the cross product map is often an isomorphism.

**Example 29.3.** How about  $H^*(S^p \times S^q)$ ? I'll assume that p and q are both positive, and leave the other cases to you. The Künneth theorem guarantees that  $\times : H^*(S^p) \otimes H^*(S^q) \to H^*(S^p \times S^q)$  is an isomorphism. Write  $\alpha$  for a generator of  $S^p$  and  $\beta$  for a generator of  $S^q$ ; and use the same notations for the pullbacks of these elements to  $S^p \times S^q$  under the projections. Then

$$H^*(S^p \times S^q) = \mathbf{Z}\langle 1, \alpha, \beta, \alpha \cup \beta \rangle$$
.

and

$$\alpha^2 = 0$$
,  $\beta^2 = 0$ ,  $\alpha\beta = (-1)^{pq}\beta\alpha$ .

This calculation is useful!

Corollary 29.4. Let p, q > 0. Any map  $S^{p+q} \to S^p \times S^q$  induces the zero map in  $H^{p+q}(-)$ .

Proof. Let  $f: S^{p+q} \to S^p \times S^q$  be such a map. It induces an algebra map  $f^*: H^*(S^p \times S^q) \to H^*(S^{p+q})$ . This map must kill  $\alpha$  and  $\beta$ , for degree reasons. But then it also kills their product, since  $f^*$  is multiplicative.

The space  $S^p \vee S^q \vee S^{p+q}$  has the same homology and cohomology groups as  $S^p \times S^q$ . Both are built as CW complexes with cells in dimensions 0, p, q, and p+q. But they are not homotopy equivalent. We can see this now because there is a map  $S^{p+q} \to S^p \vee S^q \vee S^{p+q}$  inducing an isomorphism in  $H^{p+q}(-)$ , namely, the inclusion of that summand.

#### 30 Surfaces and nondegenerate symmetric bilinear forms

We are aiming towards a proof of a fundamental cohomological property of manifolds.

**Definition 30.1.** A (topological) manifold is a Hausdorff space such that every point has an open neighborhood that is homeomorphic to some (finite dimensional) Euclidean space.

If all these Euclidean spaces can be chosen to be  $\mathbb{R}^n$ , we have an n-manifold.

In this lecture we will state a case of the Poincaré duality theorem and study some consequences of it, especially for compact 2-manifolds. This whole lecture will be happening with coefficients in  $\mathbf{F}_2$ .

**Theorem 30.2.** Let M be a compact manifold of dimension n. There exists a unique class  $[M] \in H_n(M)$ , called the fundamental class, such that for every p, q with p + q = n the pairing

$$H^p(M) \otimes H^q(M) \xrightarrow{\cup} H^n(M) \xrightarrow{\langle -, [M] \rangle} \mathbf{F}_2$$

is perfect.

This means that the adjoint map

$$H^p(M) \to \operatorname{Hom}(H^q(M), \mathbf{F}_2)$$

is an isomorphism. Since cohomology vanishes in negative dimensions, one thing this implies is that  $H^p(M) = 0$  for p > n. Since M is compact,  $\pi_0(M)$  is finite, and

$$H^{n}(M) = \text{Hom}(H^{0}(M), \mathbf{F}_{2}) = \text{Hom}(\text{Map}(\pi_{0}(M), \mathbf{F}_{2}), \mathbf{F}_{2}) = \mathbf{F}_{2}[\pi_{0}(M)].$$

A vector space V admitting a perfect pairing  $V \otimes W \to \mathbf{F}_2$  is necessarily finite dimensional; so  $H^p(M)$  is in fact finite-dimensional for all p.

Combining this pairing with the universal coefficient theorem, we get isomorphisms

$$H^p(M) \xrightarrow{\cong} \operatorname{Hom}(H^p(M), \mathbf{F}_2) \xleftarrow{\cong} H_q(M)$$
.

The homology and cohomology classes corresponding to each other under this isomorphism are said to be "Poincaré dual."

Using these isomorphisms, the cup product pairing can be rewritten as a homology pairing:

$$H_p(M) \otimes H_q(M) \xrightarrow{\ \ } H_{n-p-q}(M)$$

$$\downarrow \cong \qquad \qquad \downarrow \cong$$

$$H^{n-p}(M) \otimes H^{n-q}(M) \xrightarrow{\cup} H^{2n-p-q}(M).$$

This is the intersection pairing. Here's how to think of it. Take homology classes  $\alpha \in H_p(M)$  and  $\beta \in H_q(M)$  and represent them (if possible!) as the image of the fundamental classes of submanifolds of M, of dimensions p and q. Move them if necessary to make them intersect "transversely." Then their intersection will be a submanifold of dimension n-p-q, and it will represent the homology class  $\alpha \pitchfork \beta$ .

This relationship between the cup product and the intersection pairing is the source of the symbol for the cup product.

**Example 30.3.** Let  $M = T^2 = S^1 \times S^1$ . We know that

$$H^1(M) = \mathbf{F}_2\langle a, b \rangle$$

and  $a^2 = b^2 = 0$ , while ab = ba generates  $H^2(M)$ . The Poincaré duals of these classes are represented by cycles  $\alpha$  and  $\beta$  wrapping around one or the other of the two factor circles. They can be made to intersect in a single point. This reflects the fact that

$$\langle a \cup b, [M] \rangle = 1$$
.

Similarly, the fact that  $a^2 = 0$  reflects the fact that its Poincaré dual cycle  $\alpha$  can be moved so as not to intersect itself. The picture below shows two possible  $\alpha$ 's.

This example exhibits a particularly interesting fragment of the statement of Poincaré duality: In an even dimensional manifold – say n = 2k – the cup product pairing gives us a nondegenerate symmetric bilinear form on  $H^k(M)$ . As indicated above, this can equally well be considered a bilinear form on  $H_k(M)$ , and it is then to be thought of as describing the number of points (mod 2) two k-cycles intersect in, when put in general position relative to one another. It's called the intersection form. We'll denote it by

$$\alpha \cdot \beta = \langle a \cup b, [M] \rangle,$$

where again a and  $\alpha$  are Poincaré dual, and b and  $\beta$  are dual.

**Example 30.4.** In terms of the basis  $\alpha, \beta$ , the intersection form for  $T^2$  has matrix

$$\left[\begin{array}{cc} 0 & 1 \\ 1 & 0 \end{array}\right].$$

This is a "hyperbolic form."

Let's discuss finite dimensional nondegenerate symmetric bilinear forms over  $\mathbf{F}_2$  in general. A form on V restricts to a form on any subspace  $W \subseteq V$ , but the restricted form may be degenerate. Any subspace has an *orthogonal complement* 

$$W^{\perp} = \{ v \in V : v \cdot w = 0 \text{ for all } w \in W \}.$$

**Lemma 30.5.** The restriction of a nondegenerate bilinear form on V to a subspace W is nondegenerate exactly when  $W \cap W^{\perp} = 0$ . In that case  $W^{\perp}$  is also nondegenerate, and the splitting

$$V \cong W \oplus W^{\perp}$$

respects the forms.

Using this easy lemma, we may inductively decompose a general (finite dimensional) symmetric bilinear form. First, if there is a vector  $v \in V$  such that  $v \cdot v = 1$ , then it generates a nondegenerate subspace and

$$V = \langle v \rangle \oplus \langle v \rangle^{\perp}.$$

Continuing to split off one-dimensional subspaces brings us to the situation of a nondegenerate symmetric bilinear form such that  $v \cdot v = 0$  for every vector. Unless V = 0 we can pick a nonzero vector v. Since the form is nondegenerate, we may find another vector w such that  $v \cdot w = 1$ . The two together generate a 2-dimensional hyperbolic subspace. Split it off and continue. We conclude:

**Proposition 30.6.** Any finite dimensional nondegenerate symmetric bilinear form over  $\mathbf{F}_2$  splits as an orthogonal direct sum of forms with matrices [1] and  $\begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}$ .

Let **Bil** be the set of isomorphism classes of finite dimensional nondegenerate symmetric bilinear forms over  $\mathbf{F}_2$ . We've just given a classification of these things. This is a commutative monoid under orthogonal direct sum. It can be regarded as the set of nonsingular symmetric matrices modulo the equivalence relation of "similarity": Two matrices M and N are similar if  $N = AMA^T$  for some nonsingular A.

Claim 30.7.

$$\left[\begin{array}{cc} 1 \\ 1 \\ & 1 \end{array}\right] \sim \left[\begin{array}{cc} 1 \\ & 1 \\ & & 1 \end{array}\right]$$

*Proof.* This is the same thing as saying that  $\begin{bmatrix} 1 \\ 1 \\ 1 \end{bmatrix} = AA^T$  for some nonsingular A. Let

$$A = \begin{bmatrix} 1 & 1 & 1 \\ 1 & 0 & 1 \\ 0 & 1 & 1 \end{bmatrix}.$$

It's easy to see that there are no further relations; **Bil** is the commutative monoid with two generators I and H, subject to the relation I + H = 3I.

Let's go back to topology. Let n = 2. Then you get an intersection pairing on  $H_1(M)$ . Consider  $\mathbf{RP}^2$ . We know that  $H_1(\mathbf{RP}^2) = \mathbf{F}_2$ . This must be the form we labelled I. This says that anytime you have a nontrivial cycle on a projective plane, there's nothing you can do to remove its self intersections. You can see this. The projective plane is a Möbius band with a disk sown on along

the boundary. The waist of the Möbius band serves as a generating cycle. The observation is that if this cycle is moved to intersect itself tranversely, it must intersect itself an odd number of times.

We can produce new surfaces from old by a process of "addition." Given two connected surfaces  $\Sigma_1$  and  $\Sigma_2$ , cut a disk out of each one and sew them together along the resulting circles. This is the connected sum  $\Sigma_1 \# \Sigma_2$ .

Proposition 30.8. There is an isomorphism

$$H^1(\Sigma_1 \# \Sigma_2) \cong H^1(\Sigma_1) \oplus H^1(\Sigma_2)$$

compatible with the intersection forms.

*Proof.* Let's compute the cohomology of  $\Sigma_1 \# \Sigma_2$  using Mayer-Vietoris. The two dimensional cohomology of  $\Sigma_i - D^2$  vanishes because the punctured surface retracts onto its 1-skeleton. The relevant fragment is

$$0 \to H^1(\Sigma_1 \# \Sigma_2) \to H^1(\Sigma_1 - D^2) \oplus H^1(\Sigma_2 - D^2) \to H^1(S^1) \xrightarrow{\delta} H^2(\Sigma_1 \# \Sigma_2) \to 0.$$

The boundary map must be an isomorphism, because the connected sum is a compact connected surface so has nontrivial  $H^2$ . We leave the verification that the direct sum is orthogonal to you.  $\Box$ 

Write **Surf** for the set of homeomorphism classes of compact connected surfaces. Connected sum provides it with the structure of a commutative monoid. The classification of surfaces may now be summarized as follows:

**Theorem 30.9.** Formation of the intersection bilinear form gives an isomorphism of commutative monoids  $Surf \rightarrow Bil$ .

This is a kind of model result of algebraic topology! – a complete algebraic classification of a class of geometric objects. The oriented surfaces correspond to the bilinear forms of type gH; g is the *genus*. But it's a little strange. We must have a relation corresponding to  $H \oplus I = 3I$ , namely

$$T^2 \# \mathbf{RP}^2 \cong (\mathbf{RP}^2)^{\#3}$$
.

You should verify this for yourself!

There's more to be said about this. Away from characteristic 2, symmetric bilinear forms and quadratic forms are interchangeable. But over  $\mathbf{F}_2$  you can ask for a quadratic form q such that

$$q(x+y) = q(x) + q(y) + x \cdot y.$$

This is a "quadratic refinement" of the symmetric bilinear form. Of course it implies that  $x \cdot x = 0$  for all x, so this will correspond to some further structure on an oriented surface. This structure is a "framing," a trivialization of the normal bundle of an embedding into a high dimensional Euclidean space. There are then further invariants of this framing; this is the story of the Kervaire invariant.

#### 31 Local coefficients and orientations

The fact that a manifold is locally Euclidean puts surprising constraints on its cohomology, captured in the statement of Poincaré duality. To understand how this comes about, we have to find ways to promote *local information* – like the existence of Euclidean neighborhoods – to *global information* –

like restrictions on the structure of the cohomology. Today we'll study the notion of an orientation, which is the first link between local and global.

The local-to-global device relevant to this is the notion of a "local coefficient system," which is based on the more primitive notion of a covering space. We merely summarize that theory, since it is a prerequisite of this course.

**Definition 31.1.** A continuous map  $p: E \to B$  is a covering space if

- (1) every point pre-image is a discrete subspace of E, and
- (2) every  $b \in B$  has a neighborhood V admitting a map  $p^{-1}(V) \to p^{-1}(b)$  such that the induced map

is a homeomorphism.

The space B is the "base," E the "total space."

**Example 31.2.** A first example is given by the projection map  $pr_1 : B \times F \to B$  where F is discrete. A covering space of this form is said to be *trivial*, so the covering space condition can be rephrased as "local triviality."

The first interesting example is the projection map  $S^n \to \mathbf{RP}^n$  obtained by identifying antipodal maps on the sphere. This example generalizes in the following way.

**Definition 31.3.** An action of a group  $\pi$  on a space X is *principal* or *totally discontinuous* (terrible language, since we are certainly assuming that every group element acts by homeomorphisms) provided every element  $x \in X$  has a neighborhood U such that the only time U and gU intersect is when g = 1.

This is a strong form of "freeness" of the action. It is precisely what is needed to guarantee:

**Lemma 31.4.** If  $\pi$  acts principally on X then the orbit projection map  $X \to \pi \backslash X$  is a covering space.

It is not hard to use local triviality to prove the following:

**Theorem 31.5** (Unique path lifting). Let  $p: E \to B$  be a covering space, and  $\omega: I \to B$  a path in the base. For any  $e \in E$  such that  $p(e) = \omega(0)$ , there is a unique path  $\widetilde{\omega}: I \to E$  in E such that  $p\widetilde{\omega} = \omega$  and  $\widetilde{\omega}(0) = e$ .

This leads to a right action of  $\pi_1(B, b)$  on  $F = p^{-1}(b)$ : Represent an element of  $\pi_1(B)$  by a loop  $\omega$ ; for an element  $e \in p^{-1}(b)$  let  $\widetilde{\omega}$  be the lift of  $\omega$  with  $\widetilde{\omega}(0) = e$ ; and define

$$e \cdot [\omega] = \widetilde{\omega}(1) \in E$$
.

This element lies in F because  $\omega$  was a *loop*, ending at b. One must check that this action by  $[\omega] \in \pi_1(B,b)$  does not depend upon the choice of representative  $\omega$ , and that we do indeed get a right action:

$$e \cdot (ab) = (e \cdot a) \cdot b$$
,  $e \cdot 1 = e$ .

Given a principal  $\pi$ -action on X, with orbit space B, we can do more than just form the orbit space! If we also have a right action of  $\pi$  on a set F, we can form a new covering space over B with

F as "generic" fiber. Write  $F \times_{\pi} X$  for the quotient of the product space  $F \times X$  by the equivalence relation

$$(s, gx) \sim (sg, x), \quad g \in \pi.$$

The composite projection  $F \times X \to X \to B$  factors through a map  $F \times_{\pi} X \to B$ , which is easily seen to be a covering space. Any element  $x \in X$  determines a homeomorphism

$$F \to p^{-1}p(x)$$
 by  $s \mapsto [s, x]$ .

Of course  $*\times_{\pi} X = B$ , and if we let  $\pi$  act on itself by right translation,  $\pi \times_{\pi} X = X$ .

Covering spaces of a fixed space B form a category  $\mathbf{Cov}_B$ , in which a morphism  $E' \to E$  is "covering transformation," that is, a map  $f: E' \to E$  making

commute. Sending  $p: E \to B$  to  $p^{-1}(b)$  with its action by  $\pi_1(B,b)$  gives a functor

$$\mathbf{Cov}_B \to \mathbf{Set} - \pi_1(B, b)$$

to the category of right actions of  $\pi_1(B, b)$  on sets. For connected spaces, this is usually an equivalence of categories. The technical assumption required is this: A space B is semilocally simply connected if is path connected and for every point b and every neighborhood U of b, there exists a smaller neighborhood V such that  $\pi_1(V, b) \to \pi_1(X, b)$  is trivial. This is a very weak condition.

**Theorem 31.6.** Assume that B is semi-locally simply connected. Then the functor  $\mathbf{Cov}_B \to \mathbf{Set} - \pi_1(B, b)$  is an equivalence of categories.

This is another one of those perfect theorems in algebraic topology!

The covering space corresponding under this equivalence to the translation action of  $\pi_1(B,b)$  on itself is the *universal cover* of B, denoted by  $\widetilde{B} \to B$ . It is simply connected. Since the automorphism group of  $\pi$  as a right  $\pi$ -set is  $\pi$  (acting by left translation), the automorphism group of  $\widetilde{B} \to B$  as a covering space of B is  $\pi_1(B,b)$ . This action is principal, and the covering space corresponding to a  $\pi_1(B,b)$ -set S is given by the balanced product  $S \times_{\pi_1(B,b)} \widetilde{B}$ .

Covering spaces come up naturally in our study of topological manifolds. For any space X, we can probe the structure of X in the neighborhood of  $x \in X$  by studying the graded R-module  $H_*(X, X - x; R)$ , the local homology of X at x. By excision, this group depends only on the structure of X "locally at x": For any neighborhood U of x, excising the complement of U gives an isomorphism

$$H_*(U, U - x) \xrightarrow{\cong} H_*(X, X - x)$$
.

When the space is an n-manifold – let's write M for it – the local homology is very simple. It's nonzero only in dimension n. This has a nice immediate consequence, by the way: there is a well-defined locally constant function dim :  $M \to \mathbb{N}$ , sending x to the dimension in which  $H_*(M, M - x)$  is nontrivial. For an n-manifold, it's the constant function with value n.

In fact the whole family of homology groups  $H_n(M, M-x)$  is "locally constant." This is captured in the statement that taken together, as x varies over M, they constitute a covering space over M. So begin by defining

$$o_M = \coprod_{x \in M} H_n(M, M - x)$$

as sets. There is an evident projection map  $p:o_M\to M$ . We aim to put a topology on  $o_M$  with the property that this map is a covering space. This will use an important map  $j_{A,x}$ , defined for any closed set  $A\subseteq M$  and  $x\in A$  as the map induced by an inclusion of pairs:

$$j_{A,x}: H_n(M,M-A) \to H_n(M,M-x)$$

Define a basis of opens  $V_{U,x,\alpha}$  in  $o_M$  indexed by triples  $(U,x,\alpha)$  where U is open in  $M, x \in U$ , and  $\alpha \in H_n(M, M - \overline{U})$ :

$$V_{U,x,\alpha} = \{j_{\overline{U},x}(\alpha) : x \in U\}.$$

Each  $\alpha \in H_n(M, M - \overline{U})$  thus defines a "sheet" of  $o_M$  over U. We leave it to you to check that this is indeed a covering space.

This covering space has more structure: each fiber is an abelian group, an infinite cyclic abelian group. These structures vary continuously as you move from one fiber to another. To illuminate this structure, observe that the category  $\mathbf{Cov}_B$  has finite products; they are given by the fiber product or pullback,  $E' \times_B E \to B$ . The empty product is the terminal object,  $B \to B$ . This lets us define an "abelian group object" in  $\mathbf{Cov}_B$ ; it's an object  $E \to B$  together with maps  $E \times_B E \to E$  and  $B \to E$  over B, satisfying some evident conditions that are equivalent to requiring that they render each fiber an abelian group. If you have a ring around you can also ask for a map  $(B \times R) \times_B E \to E$  making each fiber an R-module.

The structure we have defined is a *local coefficient system* (of R-modules). We already have an example; if M is an n-manifold, we have the *orientation local system*  $o_M$  over M.

It's useful to allow coefficients in a commutative ring R; so denote by

$$o_M \otimes R$$

the local system of R-modules obtained by tensoring each fiber with R.

The classification theorem for covering spaces has as a corollary:

**Theorem 31.7.** Let B be path connected and semi-locally simply connected. Then forming the fiber over a point gives an equivalence of categories from the category of local coefficient systems of R-modules over B and the category of modules over the group algebra  $R[\pi_1(B,b)]$ .

The fibers of our local coefficient system  $o_M$  are quite simple: they are free of rank 1. Since any automorphism of such an R-module is given by multiplication by a unit in R, we find that the local coefficient system is defined by giving a homomorphism

$$\pi_1(M,b) \to R^{\times}$$

or, what is the same, an element of  $H^1(M; \mathbb{R}^{\times})$ .

When  $R = \mathbf{Z}$ , this homomorphism

$$w_1: \pi_1(M,b) \to \{\pm 1\}$$

is the "first Stiefel-Whitney class." If it is trivial, you can pick consistent generators for  $H_n(M, M-x)$  as x runs over M: the manifold is "orientable," and is *oriented* by one of the two possible choices. If it is nontrivial, the manifold is *nonorientable*. I hope it's clear that the Möbius band is nonorientable, and hence any surface containing the Möbius band is as well.

The set of abelian group generators of the fibers of  $o_M$  form a sub covering space, a double cover of M, denoted by  $o_M^{\times}$ . It is the "orientation double cover." If M is orientable (and connected) it is trivial; it consists of two copies of M. An orientation consists in chosing one or the other of the

components. If M is nonorientable (and connected) the orientation double cover is again connected. An interesting and simple fact is that its total space is a manifold in its own right, and is orientable; in fact it carries a canonical orientation.

Similarly we can form the sub covering space of R-module generators of the fibers of  $o_M \otimes R$ ; write  $(o_M \otimes R)^{\times}$  for it.

Now if  $p: E \to B$  is a covering space, one of the things you may want to do is consider a section of p; that is, a continuous function  $\sigma: B \to E$  such that  $p \circ \sigma = 1_B$ . Write  $\Gamma(B; E)$  for the set of sections of  $p: E \to B$ . Under the correspondence between covering spaces and actions of  $\pi$ ,

$$\Gamma(B; E) = (p^{-1}(b))^{\pi_1(B,b)},$$

the fixed point set for the action of  $\pi_1(B, b)$  on  $p^{-1}(b)$ . If E is a local system of R-modules, this is a sub R-module.

A "local R-orientation at x" is a choice of R-module generator of  $H_n(M, M-x; R)$ , and we make the following definition.

**Definition 31.8.** An *R*-orientation of an *n*-manifold *M* is a section of  $(o_M \otimes R)^{\times}$ .

For example, when  $R = \mathbf{F}_2$ , every manifold is orientable, and uniquely so, since  $\mathbf{F}_2^{\times} = \{1\}$ . A **Z**-orientation (or simply "orientation") is a section of the orientation double cover. A manifold is "R-orientable" if it admits an R-orientation. A connected n-manifold is either non-orientable, or admits two orientations. Euclidean space is orientable.

This relates to the "globalization" project we started out talking about. A section over B is in fact called a "global section." In the case of the orientation local system, we have a canonical map

$$j: H_n(M; R) \to \Gamma(M; o_M \otimes R)$$
,

described as follows. The value of j(a) at  $x \in M$  is the restriction of a to  $H_n(M, M - x)$ . The first "local-to-global" theorem, a special case of Poincaré duality, is this:

**Theorem 31.9** (Orientation Theorem). If M is compact, the map  $j: H_n(M; R) \to \Gamma(M; o_M \otimes R)$  is an isomorphism.

We will prove this theorem in the next lecture.

The representation of  $\pi_1(B)$  on the fiber of  $o_M \otimes R$  over b is given by the composite  $\pi_1(B) \to \{\pm 1\} \to R^{\times}$ . If this is the trivial homomorphism, the fixed points of this representation on R form all of R. If not, the fixed points are the subgroup of R of elements of order 2, written R[2].

Corollary 31.10. If M is a compact connected n-manifold, then

$$H_n(M;R) \cong \begin{cases} R & \text{if } M \text{ is orientable} \\ R[2] & \text{if not.} \end{cases}$$

In the first case, a generator of  $H_n(M;R)$  is a fundamental class for the manifold. You should think of the manifold itself as a cycle representing this homology class. It is characterized as a class restricting to a generator of  $H_n(M, M - x)$  for all x; this is saying that the cycle "covers" the point x once.

The first isomorphism in the theorem depends upon this choice of fundamental class. But in the second case, the isomorphism is canonical. Over  $\mathbf{F}_2$ , any compact connected manifold has a unique fundamental class, the generator of  $H_n(M; \mathbf{F}_2) = \mathbf{F}_2$ .

#### 32 Proof of the orientation theorem

We are studying the way in which local homological information gives rise to global information, especially on an n-manifold M. The tool was the map

$$j: H_n(M; R) \to \Gamma(M; o_M \otimes R)$$

sending a class c to the section of the orientation local coefficient system given at  $x \in M$  by the restriction  $j_x(c) \in H_n(M, M - x)$ . We asserted that if M is compact then j is an isomorphism and that  $H_q(M) = 0$  for q > n. The proof will be by induction.

To make the induction go, we will need a refinement of this construction. Let  $A \subseteq M$  be a compact subset. A class in  $H_n(M, M-A)$  is represented by a cycle whose boundary lies outside of A. It may cover A evenly. We can give meaning to this question as follows. Let  $x \in A$ . Then  $M - A \subseteq M - x$ , so we have a map

$$j_{A,x}: H_n(M,M-A) \to H_n(M,M-x)$$

that tests whether the chain covers x. As x ranges over A, these maps together give us a map to the group of sections of  $o_M$  over A,

$$j_A: H_n(M, M-A) \to \Gamma(A; o_M)$$
.

Because  $H_n(M, M - A)$  deals with homology classes that "stretch over A," we will write

$$H_n(M, M - A) = H_n(M|A)$$
.

**Theorem 32.1.** Let M be an n-manifold and let A be a compact subset of M. Then  $H_q(M|A;R) = 0$  for q > n, and the map  $j_A : H_n(M|A;R) \to \Gamma(A;o_M \otimes R)$  is an isomorphism.

Taking A = M (assuming M compact) we find that  $H_q(M; R) = 0$  for q > n and

$$j_M: H_n(M;R) \xrightarrow{\cong} \Gamma(M;o_M \otimes R)$$
.

But the theorem covers much more exotic situations as well; perhaps A is a Cantor set in some Euclidean space, for example.

We follow [2] in proving this, and refer you to that reference for the modifications appropriate for the more general statement when A is assumed merely closed rather than compact.

First we establish two general results.

**Proposition 32.2.** Let A and B be closed subspaces of M, and suppose the result holds for A, B, and  $A \cap B$ . Then it holds for  $A \cup B$ .

*Proof.* The relative Mayer-Vietoris theorem and the hypothesis that  $H_{n+1}(M|A \cap B) = 0$  gives us exactness of the top row in the ladder

$$0 \longrightarrow H_n(M|A \cup B) \longrightarrow H_n(M|A) \oplus H_n(M|B) \longrightarrow H_n(M|A \cap B)$$

$$\downarrow^{j_{A \cap B}} \qquad \qquad \downarrow^{j_{A \oplus j_B}} \qquad \qquad \downarrow^{j_{A \cap B}}$$

$$0 \longrightarrow \Gamma(A \cup B; o_M) \longrightarrow \Gamma(A; o_M) \oplus \Gamma(B; o_M) \longrightarrow \Gamma(A \cap B; o_M).$$

Exactness of the bottom row is clear: A section over  $A \cup B$  is precisely a section over A and a section over B that agree on the intersection. So the five-lemma shows that  $j_{A \cup B}$  is an isomorphism. Looking further back in the Mayer-Vietoris sequence gives the vanishing of  $H_q(M|A)$  for q > n.  $\square$ 

**Proposition 32.3.** Let  $A_1 \supseteq A_2 \supseteq \cdots$  be a decreasing sequence of compact subsets of M, and assume that the theorem holds for each  $A_n$ . Then it holds for the intersection  $A = \bigcap A_i$ .

The proof of this proposition entails two lemmas, which we'll dispose of first.

**Lemma 32.4.** Let  $A_1 \supseteq A_2 \supseteq \cdots$  be a decreasing sequence of compact subsets of a space X, with intersection A. Then

$$\varinjlim_{i} H_{q}(X, X - A_{i}) \xrightarrow{\cong} H_{q}(X, X - A).$$

*Proof.* Let  $\sigma: \Delta^q \to X$  be any q-simplex in X - A. The subsets  $X - A_i$  form an open cover of  $\operatorname{im}(\sigma)$ , so by compactness it lies in some single  $X - A_i$ . This shows that

$$\lim_{\longrightarrow i} S_q(X - A_i) \xrightarrow{\cong} S_q(X - A).$$

Thus

$$\lim_{\longrightarrow i} S_q(X|A_i) \xrightarrow{\cong} S_q(X|A_i)$$

by exactness of direct limit, and the claim then follows for the same reason.

**Lemma 32.5.** Let  $A_1 \supseteq A_2 \supseteq \cdots$  be a decreasing sequence of compact subsets in a Hausdorff space X with intersection A. For any open neighborhood U of A there exists i such that  $A_i \subseteq U$ .

*Proof.* A is compact, being a closed subset of the compact Hausdorff space  $A_1$ . Since A is the intersection of the  $A_i$ , and  $A \subseteq U$ , the intersection of the decreasing sequence of compact sets  $A_i - U$  is empty. Thus by the finite intersection property one of them must be empty; but that says that  $A_i \subseteq U$ .

Proof of Proposition 32.3. By Lemma 32.4,  $H_q(M|A) = 0$  for q > n. In dimension n, we contemplate the commutative diagram

$$\varinjlim_{i} H_{n}(M|A_{i}) \xrightarrow{\cong} H_{n}(M|A)$$

$$\downarrow^{\cong} \qquad \qquad \downarrow$$

$$\varinjlim_{i} \Gamma(A_{i}; o_{M}) \xrightarrow{\cong} \Gamma(A; o_{M}).$$

The top map an isomorphism by Lemma 32.4.

To see that the bottom map is an isomorphism, we'll verify the two conditions for a map to be a direct limit from Lecture 23. First let x be a section of  $o_M$  over A. By compactness, we may cover A by a finite set of opens over each of which  $o_M$  is trivial. The section extends over their union U, by unique path lifting. By Lemma 32.5 this open set contains some  $A_i$ , and we conclude that any section over A extends to some  $A_i$ .

On the other hand, suppose that a section  $x \in \Gamma(A_i; o_M)$  vanishes on A. Then it vanishes on some open set containing A, again by unique path lifting and local triviality. Some  $A_j$  lies in that open set, again by Lemma 32.5. We may assume that  $j \geq i$ , and conclude that x already vanishes on  $A_j$ .

Proof of Theorem 32.1. There are five steps. In describing them, we will call a subset of M "Euclidean" if it lies inside some open set homeomorphic to  $\mathbb{R}^n$ .

- (1)  $M = \mathbb{R}^n$ , A a compact convex subset.
- (2)  $M = \mathbb{R}^n$ , A a finite union of compact convex subsets.
- (3)  $M = \mathbf{R}^n$ , A any compact subset.
- (4) M arbitrary, A a finite union of compact Euclidean subsets.
- (5) M arbitrary, A an arbitrary compact subset.

Notes on the proofs: (1) To be clear, "convex" implies nonempty. By translating A, we may assume that  $0 \in A$ . The compact subset A lies in some disk, and by a homothety we may assume that the disk is the unit disk  $D^n$ . Then we claim that the inclusion  $i: S^{n-1} \to \mathbf{R}^n - A$  is a deformation retract. A retraction is given by r(x) = x/||x||, and a homotopy from ir to the identity is given by

$$h(x,t) = \left(t + \frac{1-t}{||x||}\right)x.$$

It follows that  $H_q(\mathbf{R}^n, \mathbf{R}^n - A) \cong H_q(\mathbf{R}^n, \mathbf{R}^n - D^n)$  for all q. This group is zero for q > n. In dimension n, note that restricting to the origin gives an isomorphism  $H_n(\mathbf{R}^n, \mathbf{R}^n - D^n) \to H_n(\mathbf{R}^n, \mathbf{R}^n - 0)$  since  $\mathbf{R}^n - D$  is a deformation retract of  $\mathbf{R}^n - 0$ . The local system  $o_{\mathbf{R}^n}$  is trivial, since  $\mathbf{R}^n$  is simply connected, so restricting to the origin gives an isomorphism  $\Gamma(D^n, o_{\mathbf{R}^n}) \to H_n(\mathbf{R}^n, \mathbf{R}^n - 0)$ . This implies that  $j_{D^n}: H_n(\mathbf{R}^n, \mathbf{R}^n - D^n) \to \Gamma(D^n, o_{\mathbf{R}^n})$  is an isomorphism. The restriction  $\Gamma(D^n, o_{\mathbf{R}^n}) \to \Gamma(A, o_{\mathbf{R}^n})$  is also an isomorphism, since  $A \to D^n$  is a deformation retract. So by the commutative diagram

$$H_n(\mathbf{R}^n, \mathbf{R}^n - D^n) \xrightarrow{\cong} H_n(\mathbf{R}^n, \mathbf{R}^n - A)$$

$$\downarrow^{j_{D^n}} \qquad \qquad \downarrow^{j_A}$$

$$\Gamma(D^n, o_{\mathbf{R}^n}) \xrightarrow{\longrightarrow} \Gamma(A, o_{\mathbf{R}^n})$$

we find that  $j_A: H_n(\mathbf{R}^n, \mathbf{R}^n - A) \to \Gamma(A; o_{\mathbf{R}^n})$  is an isomorphism.

- (2) by Proposition 32.2.
- (3) For each  $j \geq 1$ , let  $C_j$  be a finite subset of A such that

$$A \subseteq \bigcup_{x \in C_j} B_{1/j}(x) .$$

Since any intersection of convex sets is either empty or convex,

$$A_k = \bigcap_{j=1}^k \bigcup_{x \in C_j} B_{1/j}(x)$$

is a union of finitely many convex sets, and since A is closed it is the intersection of this decreasing family. So the result follows from (1), (2), and Proposition 32.3.

- (4) by (3) and (2).
- (5) Cover A by finitely many open subsets that embed in Euclidean opens as open disks with compact closures. Their closures then form a finite cover by closed Euclidean disks  $D_i$  in Euclidean opens  $U_i$ . For each i, excise the closed subset  $M U_i$  to see that

$$H_q(M, M - A \cap D_i) \cong H_q(U_i, U_i - A \cap D_i) \cong H_q(\mathbf{R}^n, \mathbf{R}^n - A \cap D_i)$$
.

By (4), the theorem holds for each of these. Each intersection  $(A \cap D_i) \cap (A \cap D_j)$  is again a compact Euclidean subset, so the result holds for them by excision as well. The result then follows by (1).  $\square$ 

#### 33 A plethora of products

We are now heading towards a statement of Poincaré duality.

Recall that we have the Kronecker pairing

$$\langle -, - \rangle : H^p(X; R) \otimes H_p(X; R) \to R$$
.

It's obviously not "natural," because  $H^p$  is contravariant while homology is covariant. But given  $f: X \to Y$ ,  $b \in H^p(Y)$ , and  $x \in H_p(X)$ , we can ask: How does  $\langle f^*b, x \rangle$  relate to  $\langle b, f_*x \rangle$ ?

Claim 33.1. 
$$\langle f^*b, x \rangle = \langle b, f_*x \rangle$$
.

*Proof.* This is easy! I find it useful to write out diagrams to show where things are. We're going to work on the chain level.

$$\operatorname{Hom}(S_p(Y), R) \otimes S_p(X) \xrightarrow{1 \otimes f_*} \operatorname{Hom}(S_p(Y), R) \otimes S_p(Y)$$

$$\downarrow^{f^* \otimes 1} \qquad \qquad \downarrow^{\langle -, -\rangle}$$

$$\operatorname{Hom}(S_p(X), R) \otimes S_p(X) \xrightarrow{\langle -, -\rangle} R$$

We want this diagram to commute. Suppose  $[\beta] = b$  and  $[\xi] = x$ . Then going to the right and then down gives

$$\beta \otimes \xi \mapsto \beta \otimes f_*(\xi) \mapsto \beta(f_*\xi)$$
.

The other way gives

$$\beta \otimes \xi \mapsto f^*(\beta) \otimes \xi = (\beta \circ f_*) \otimes \xi \mapsto (\beta \circ f_*)(\xi)$$
.

This is exactly  $\beta(f_*\xi)$ .

There's actually another product in play here:

$$\mu: H(C_*) \otimes H(D_*) \to H(C_* \otimes D_*)$$

given by  $[c] \otimes [d] \mapsto [c \otimes d]$ . I used it to pass from the chain level computation we did to the homology statement.

We also have the two cross products:

$$\times: H_p(X) \otimes H_q(Y) \to H_{p+q}(X \times Y)$$

and

$$\times: H^p(X) \otimes H^q(Y) \to H^{p+q}(X \times Y)$$
.

You might think this is fishly because both maps are in the same direction. But it's OK, because we used different things to make these constructions: the chain-level cross product (or Eilenberg-Zilber map) for homology and the Alexander-Whitney map for cohomology. Still, they're related:

**Lemma 33.2.** Let  $a \in H^p(X), b \in H^q(Y), x \in H_p(X), y \in H_q(Y)$ . Then:

$$\langle a \times b, x \times y \rangle = (-1)^{|x| \cdot |b|} \langle a, x \rangle \langle b, y \rangle.$$

*Proof.* Look at the chain-level cross product and the Alexander-Whitney maps:

$$\times : S_*(X) \otimes S_*(Y) \leftrightarrows S_*(X \times Y) : \alpha$$

They are inverse isomorphisms in dimension 0, and both sides are projective resolutions with respect to the models  $(\Delta^p, \Delta^q)$ ; so by acyclic models they are natural chain homotopy inverses.

Say  $[f] = a, [g] = b, [\xi] = x, [\eta] = y$ . Write fg for the composite

$$S_p(X) \otimes S_q(Y) \xrightarrow{\times} S_{p+q}(X \times Y) \xrightarrow{f \otimes g} R \otimes R \to R$$

Then:

$$(f \times g)(\xi \times \eta) = (fg)\alpha(\xi \times \eta) \simeq (fg)(\xi \otimes \eta) = (-1)^{pq}f(\xi)g(\eta).$$

We can use this to prove a restricted form of the Künneth theorem in cohomology.

**Theorem 33.3.** Let R be a PID. Assume that  $H_p(X)$  is a finitely generated free R-module for all p. Then

$$\times: H^*(X;R) \otimes_R H^*(Y;R) \to H^*(X \times Y;R)$$

is an isomorphism.

*Proof.* Write  $M^{\vee}$  for the linear dual of an R-module M. By our assumption about  $H_p(X)$ , the map

$$H_p(X)^{\vee} \otimes H_q(Y)^{\vee} \to (H_p(X) \otimes H_q(Y))^{\vee}$$
,

sending  $f \otimes g$  to  $(x \otimes y \mapsto (-1)^{pq} f(x)g(y))$ , is an isomorphism. The homology Künneth theorem guarantees that the bottom map in the following diagram is an isomorphism.

$$\bigoplus_{p+q=n} H^p(X) \otimes H^q(Y) \xrightarrow{\times} H^n(X \times Y)$$

$$\downarrow^{\cong} \qquad \qquad \downarrow^{\cong}$$

$$\bigoplus_{p+q=n} H_p(X)^{\vee} \otimes H_q(Y)^{\vee} \xrightarrow{\cong} \left(\bigoplus_{p+q=n} H_p(X) \otimes H_q(Y)\right)^{\vee} \stackrel{\cong}{\longleftarrow} H_n(X \times Y)^{\vee}$$

Commutativity of this diagram is exactly the content of Lemma 33.2.

We saw before that  $\times$  is an algebra map, so under the conditions of the theorem it is an isomorphism of algebras. You do need some finiteness assumption, even if you are working over a field. For example let T be an infinite set, regarded as a space with the discrete topology. Then  $H^0(T; R) = \operatorname{Map}(T, R)$ . But

$$\operatorname{Map}(T,R) \otimes \operatorname{Map}(T,R) \to \operatorname{Map}(T \times T,R)$$

sending  $f \otimes g$  to  $(s,t) \to f(s)g(t)$  is not surjective; the characteristic function of the diagonal is not in the image, for example (unless R = 0).

There are more products around. For example, there is a map

$$H^p(Y) \otimes H^q(X, A) \to H^{p+q}(Y \times X, Y \times A)$$
.

Constructing this is on your homework. Suppose Y = X. Then I get

$$\cup: H^*(X) \otimes H^*(X,A) \to H^*(X \times X, X \times A) \xrightarrow{\Delta^*} H^*(X,A)$$

where  $\Delta: (X, A) \to (X \times X, X \times A)$  is the "relative diagonal." This relative cup product makes  $H^*(X, A)$  into a module over the graded algebra  $H^*(X)$ . The relative cohomology is not a ring – it doesn't have a unit, for example – but it is a module. And the long exact sequence of the pair is a sequence of  $H^*(X)$ -modules.

I want to introduce you to one more product, one that will enter into our expression of Poincaré duality. This is the *cap product*. What can I do with  $S^p(X) \otimes S_n(X)$ ? Well, I can form the composite:

$$\cap: S^p(X) \otimes S_n(X) \xrightarrow{1 \times (\alpha \circ \Delta_*)} S^p(X) \otimes S_p(X) \otimes S_{n-p}(X) \xrightarrow{\langle -, - \rangle \otimes 1} S_{n-p}(X)$$

Using our explicit formula for  $\alpha$ , we can write:

$$\cap: \beta \otimes \sigma \mapsto \beta \otimes (\sigma \circ \alpha_p) \otimes (\sigma \circ \omega_q) \mapsto (\beta(\sigma \circ \alpha_p)) (\sigma \circ \omega_q)$$

We are evaluating the cochain on part of the chain, leaving a lower dimensional chain left over.

This composite is a chain map, and so induces a map in homology:

$$\cap: H^p(X) \otimes H_n(X) \to H_{n-p}(X)$$
.

Notice how the dimensions work. Long ago a bad choice was made: If cohomology were graded with negative integers, the way the gradations work here would look better.

There are also two slant products. Maybe I won't talk about them. In the next lecture, I'll check a few things about cap products, and then get into the machinery of Poincaré duality.

#### 34 Cap product and "Cech" cohomology

We have a few more things to say about the cap product, and will then use it to give a statement of Poincaré duality.

**Proposition 34.1.** The cap product enjoys the following properties.

- (1)  $(a \cup b) \cap x = a \cap (b \cap x)$  and  $1 \cap x = x$ :  $H_*(X)$  is a module for  $H^*(X)$ .
- (2) Given a map  $f: X \to Y$ ,  $b \in H^p(Y)$ , and  $x \in H_n(X)$ ,

$$f_*(f^*(b) \cap x) = b \cap f_*(x)$$
.

(3) Let  $\epsilon: H_*(X) \to R$  be the augmentation. Then

$$\varepsilon(b \cap x) = \langle b, x \rangle$$
.

(4) Cap and cup are adjoint:

$$\langle a \cap b, x \rangle = \langle a, b \cap x \rangle$$
.

Proof. (1) Easy.

(2) Let  $\beta$  be a cocycle representing b, and  $\sigma$  an n-simplex in X. Then

$$f_*(f^*(\beta) \cap \sigma) = f_*((f^*(\beta)(\sigma \circ \alpha_p)) \cdot (\sigma \circ \omega_q))$$

$$= f_*(\beta(f \circ \sigma \circ \alpha_p) \cdot (\sigma \circ \omega))$$

$$= \beta(f \circ \sigma \circ \alpha_p) \cdot f_*(\sigma \circ \omega_q)$$

$$= \beta(f \circ \sigma \circ \alpha_p) \cdot (f \circ \sigma \circ \omega_q)$$

$$= \beta \cap f_*(\sigma)$$

This formula goes by many names: the "projection formula," or "Frobenius reciprocity." (3) We get zero unless p = n. Again let  $\sigma \in \operatorname{Sin}_n(X)$ , and compute:

$$\varepsilon(\beta \cap \sigma) = \varepsilon(\beta(\sigma) \cdot c_{\sigma(n)}^0) = \beta(\sigma)\varepsilon(c_{\sigma(n)}^0) = \beta(\sigma) = \langle \beta, \sigma \rangle.$$

Here now is a statement of Poincaré duality. It deals with the homological structure of compact topological manifolds. We recall the notion of an orientation, and Theorem 31.9 asserting the existence of a fundamental class  $[M] \in H_n(M; R)$  in a compact R-oriented n-manifold.

**Theorem 34.2** (Poincaré duality). Let M be a topological n-manifold that is compact and oriented with respect to a PID R. Then there is a unique class  $[M] \in H_n(M;R)$  that restricts to the orientation class in  $H_n(M, M-a; R)$  for every  $a \in M$ . It has the property that

$$-\cap [M]: H^p(M;R) \to H_q(M;R), \quad p+q=n,$$

is an isomorphism for all p.

You might want to go back to Lecture 25 and verify that  $\mathbf{RP}^3 \times \mathbf{RP}^3$  satisfies this theorem.

Our proof of Poincaré duality will be by induction. In order to make the induction go we will prove a substantially more general theorem, one that involves relative homology and cohomology. So we begin by understanding how the cap product behaves in relative homology.

Suppose  $A \subseteq X$  is a subspace. We have:

The left sequence is exact because  $0 \to S_n(A) \to S_n(X) \to S_n(X,A) \to 0$  splits and tensoring with  $S^p(X)$  (which is not free!) therefore leaves it exact. The solid arrow diagram commutes precisely by the chain-level projection formula. There is therefore a uniquely defined map on cokernels.

This chain map yields the relative cap product

$$\cap: H^p(X) \otimes H_n(X,A) \to H_q(X,A)$$

It renders  $H_*(X, A)$  a module for the graded algebra  $H^*(X)$ .

I want to come back to an old question, about the significance of relative homology. Suppose that  $K \subseteq X$  is a subspace, and consider the relative homology  $H_*(X, X - K)$ . Since the complement of X - K in X is K, these groups should be regarded as giving information about K. If I enlarge

K, I make X - K smaller:  $K \subseteq L$  induces  $H_*(X, X - L) \to H_*(X - K)$ ; the relative homology is contravariant in the variable K (regarded as an object of the poset of subspaces of X).

Excision gives insight into how  $H_*(X, X - K)$  depends on K. Suppose  $K \subseteq U \subseteq X$  with  $\overline{K} \subseteq \text{Int}(U)$ . To simplify things, let's just suppose that K is closed and U is open. Then X - U is closed, X - K is open, and  $X - U \subseteq X - K$ , so excision asserts that the inclusion map

$$H_*(U, U - K) \rightarrow H_*(X, X - K)$$

is an isomorphism.

The cap product puts some structure on  $H_*(X, X - K)$ : it's a module over  $H^*(X)$ . But we can do better! We just decided that  $H_*(X, X - K) = H_*(U, U - K)$ , so the  $H^*(X)$  action factors through an action by  $H^*(U)$ , for any open set U containing K. How does this refined action change when I decrease U?

**Lemma 34.3.** Let  $K \subseteq V \subseteq U \subseteq X$ , with K closed and U, V open. Then:

commutes.

*Proof.* This is just the projection formula again!

Let  $\mathcal{U}_K$  be the set of open neighborhoods of K in X. It is partially ordered by reverse inclusion. This poset is directed, since the intersection of two opens is open. By the lemma,  $H^p: \mathcal{U}_K \to \mathbf{Ab}$  is a directed system.

**Definition 34.4.** The *Cech cohomology* of K is

$$\check{H}^p(K) = \varinjlim_{U \in \mathcal{U}_K} H^p(U) .$$

I apologize for this bad notation; its possible dependence on the way K is sitting in X is not recorded. The maps in this directed systen are all maps of graded algebras, so the direct limit is naturally a commutative graded algebra. Since tensor product commutes with direct limits, we now get a cap product pairing

$$\cap : \check{H}^p(K) \otimes H_n(X, X - K) \to H_q(X, X - K)$$

satisfying the expected properties. This is the best you can do. It's the natural structure that this relative homology has:  $H_*(X, X - K)$  is a module over  $\check{H}^*(K)$ .

There are compatible restriction maps  $H^p(U) \to H^p(K)$ , so there is a natural map

$$\check{H}^*(K) \to H^*(K)$$
.

This map is often an isomorphism. Suppose  $K \subseteq X$  satisfies the following "regular neighborhood" condition: For every open  $U \supseteq K$ , there exists an open V with  $U \supseteq V \supseteq K$  such that  $K \hookrightarrow V$  is a homotopy equivalence (or actually just a homology isomorphism).

**Lemma 34.5.** Under these conditions,  $\check{H}^*(K) \to H^*(K)$  is an isomorphism.

*Proof.* We will check that the map to  $H^p(K)$  satisfies the conditions we established in Lecture 23 to be a direct limit.

So let  $x \in H^p(K)$ . Let U be a neighborood of K in X such that  $H^p(U) \to H^p(K)$  is an isomorphism. Then indeed x is in the image of  $H^p(U)$ .

Then let U be a neighborhood of K and let  $x \in H^p(U)$  restrict to 0 in  $H^p(K)$ . Let V be a sub-neighborhood such that  $H^p(V) \to H^p(K)$  is an isomorphism. Then x restricts to 0 in  $H^p(V)$ .  $\square$ 

On the other hand, here's an example that distinguishes  $\check{H}^*$  from  $H^*$ . This is a famous example. The "topologist's sine curve" is the subspace of  $\mathbf{R}^2$  defined as follows. It is union of three subsets, A, B, and C. A is the graph of  $\sin(\pi/x)$  where 0 < x < 1. B is the interval  $0 \times [-1,1]$ . C is a continuous curve from (0,-1) to (1,0) and meeting  $A \cup B$  only at its endpoints. This is a counterexample for a lot of things; you've probably seen it in 18.901.

What is the singular homology of the topologist's sine curve? Use Mayer-Vietoris! I can choose V to be some connected portion of the continuous curve from (0,-1) to (1,0), and U to contain the rest of the space in a way that intersects V in two open intervals. Then V is contractible, and U is made up of two contractible connected components. (This space is not locally path connected, and one of these path components is not closed.)

The Mayer-Vietoris sequence looks like

$$0 \to H_1(X) \xrightarrow{\partial} H_0(U \cap V) \to H_0(U) \oplus H_0(V) \to H_0(X) \to 0.$$

The two path components of  $U \cap V$  do not become connected in U, so  $\partial = 0$  and we find that  $\varepsilon : H_*(X) \xrightarrow{\cong} H_*(*)$  and hence  $H^*(X) \cong H^*(*)$ .

How about  $\check{H}^*$ ? Let  $X \subset U$  be an open neighborhood. The interval  $0 \times [-1,1]$  has an  $\epsilon$ -neighborhood, for some small  $\epsilon$ , that's contained in U. This implies that there exists a neighborhood  $X \subseteq V \subseteq U$  such that  $V \simeq S^1$ . This implies that

$$\varinjlim_{U \in \mathcal{U}_X} H^*(U) \cong H^*(S^1)$$

by a cofinality argument that we will detail later. So  $\check{H}^*(X) \neq H^*(X)$ .

Nevertheless, under quite general conditions the Čech cohomology of a compact Hausdorff space is a topological invariant. The Čech construction forms a limit over open covers of the cohomology of the nerve of the cover. It is a topological invariant by construction.

**Theorem 34.6.** Let X be a compact subset of some Euclidean space. If there is an open neighborhood of which it is a retract, then  $\check{H}^*(X;R)$  is canonically isomorphic to the cohomology defined using the Čech construction, and is therefore independent of the embedding into Euclidean space.

See Dold's beautiful book [3] for this and other topics discussed in this chapter.

#### 35 Cech cohomology as a cohomology theory

Let X be any space, and let  $K \subseteq X$  be a closed subspace. We've defined the Čech cohomology of K as the direct limit of  $H^*(U)$  as U ranges over the poset  $\mathcal{U}_K$  of open neighborhoods of K. This often coincides with  $H^*(K)$  but will not be the same in general. Nevertheless it behaves like a cohomology theory. To expand on this claim, we should begin by defining a relative version.

Suppose  $L \subseteq K$  is a pair of closed subsets of a space X. Let (U, V) be a "neighborhood pair" for (K, L):

$$\begin{array}{cccc} L & \subseteq & K \\ & \cap & & \cap \\ V & \subset & U \end{array}$$

with U and V open. These again form a directed set  $\mathcal{U}_{K,L}$ , with partial order given by reverse inclusion of pairs. Then define

$$\check{H}^p(K,L) = \varinjlim_{(U,V)\in\mathcal{U}_{K,L}} H^p(U,V).$$

We will want to verify versions of the Eilenberg-Steenrod axioms for these functors. For a start, I have to explain how maps induce maps.

Let  $\mathcal{I}$  be a directed set and  $A: \mathcal{I} \to \mathbf{Ab}$  a functor. If we have an order-preserving map – a functor –  $\varphi: \mathcal{J} \to \mathcal{I}$  from another directed set, we get  $A\varphi: \mathcal{J} \to \mathbf{Ab}$ ; so  $(A\varphi)_j = A_{\varphi(j)}$ . I can form two direct limits:  $\varinjlim_{\mathcal{I}} A\varphi$  and  $\varinjlim_{\mathcal{I}} A$ . I claim that they are related by a map

$$\varinjlim_{\mathcal{I}} A\varphi \to \varinjlim_{\mathcal{I}} A$$
.

Using the universal property of direct limits, we need to come up with compatible maps  $f_j: A_{\varphi(j)} \to \varinjlim_{\mathcal{I}} A$ . We have compatible maps  $\operatorname{in}_i: A_i \to \varinjlim_{\mathcal{I}} A$  for  $i \in \mathcal{I}$ , so we can take  $f_j = \operatorname{in}_{\varphi(j)}$ .

These maps are compatible under composition of order-preserving maps.

**Example 35.1.** A closed inclusion  $i: K \supseteq L$  induces an order-preserving map  $\varphi: \mathcal{U}_K \to \mathcal{U}_L$ . The functor  $H^p: \mathcal{U}_K \to \mathbf{Ab}$  restricts to  $H^p: \mathcal{U}_L \to \mathbf{Ab}$ , so we get maps

$$\lim_{\mathcal{U}_K} H^p = \lim_{\mathcal{U}_K} H^p \varphi \to \lim_{\mathcal{U}_L} H^p.$$

i.e.

$$i^*: \check{H}^p(K) \to \check{H}^p(L)$$
.

This makes  $\check{H}^p$  into a contravariant functor on the partially ordered set of closed subsets of X.

I can do the same thing for relative cohomology, and get the maps involved in the following two theorems, whose proofs will come in due course.

**Theorem 35.2** (Long exact sequence). Let (K, L) be a closed pair in X. There is a long exact sequence

$$\cdots \to \check{H}^p(K,L) \to \check{H}^p(K) \to \check{H}^p(L) \xrightarrow{\delta} \check{H}^{p+1}(K,L) \to \cdots$$

that is natural in the pair.

**Theorem 35.3** (Excision). Suppose A and B are closed subsets of a normal space, or compact subsets of a Hausdorff space. Then the map

$$\check{H}^p(A \cup B, A) \xrightarrow{\cong} \check{H}^p(B, A \cap B)$$

induced by the inclusion is an isomorphism.

Each of these theorems relates direct limits defined over different directed sets. To prove them, I will want to rewrite the various direct limits as direct limits over the same directed set. This raises the following . . .

Question 35.4. When does  $\varphi: \mathcal{J} \to \mathcal{I}$  induce an isomorphism  $\varinjlim_{\mathcal{J}} A\varphi \to \varinjlim_{\mathcal{I}} A$ ?

This is a lot like taking a sequence and a subsequence and asking when they have the same limit. There's a cofinality condition in analysis, that has a similar expression here.

**Definition 35.5.**  $\varphi: \mathcal{J} \to \mathcal{I}$  is *cofinal* if for all  $i \in \mathcal{I}$ , there exists  $j \in \mathcal{J}$  such that  $i \leq \varphi(j)$ .

Example 35.6. Any surjective order-preserving map is cofinal.

For another example, let  $(\mathbb{N}_{>0}, <)$  be the positive integers with their ususal order, and  $(\mathbb{N}_{>0}, |)$  the same set but with the divisibility order. There is an order-preserving map  $\varphi : (\mathbb{N}_{>0}, <) \to (\mathbb{N}_{>0}, |)$  given by  $n \mapsto n!$ . This map is far from surjective, but any integer n divides some factorial (n divides n!, for example), so  $\varphi$  is cofinal. We claimed that both these systems produce  $\mathbf{Q}$  as direct limit.

**Lemma 35.7.** If  $\varphi: \mathcal{J} \to \mathcal{I}$  is cofinal then  $\varinjlim_{\mathcal{J}} A\varphi \to \varinjlim_{\mathcal{I}} A$  is an isomorphism.

*Proof.* Check that  $\{A_{\varphi(j)} \to \varinjlim_{\mathcal{T}} A\}$  satisfies the necessary and sufficient conditions to be  $\varinjlim_{\mathcal{T}} A\varphi$ .

- 1. For each  $a \in \varinjlim_{\mathcal{I}} A$  there exists  $j \in \mathcal{J}$  and  $a_j \in A_{\varphi(j)}$  such that  $a_j \mapsto a$ : We know that there exists some  $i \in \mathcal{I}$  and  $a_i \in A$  such that  $a_i \mapsto a$ . Pick j such that  $i \leq \varphi(j)$ . Then  $a_i \mapsto a_{\varphi(j)}$ , and by compatibility we get  $a_{\varphi(j)} \mapsto a$ .
- 2. Suppose  $a \in A_{\varphi(j)}$  maps to  $0 \in \varinjlim_{\mathcal{I}} A$ . Then there is some  $i \in \mathcal{I}$  such that  $\varphi(j) \leq i$  and  $a \mapsto 0$  in  $A_i$ . But then there is  $j' \in \mathcal{J}$  such that  $i \leq \varphi(j')$ , and  $a \mapsto 0 \in A_{\varphi(j')}$  as well.

Proof of Theorem 35.2, the long exact sequence. Let (K, L) be a closed pair in the space X. We have

$$\check{H}^p(K,L) = \varinjlim_{(U,V) \in \mathcal{U}_{K,L}} H^p(U,V) \,, \quad \check{H}^p(K) = \varinjlim_{U \in \mathcal{U}_K} H^p(U) \,, \quad \text{and} \quad \check{H}^p(L) = \varinjlim_{V \in \mathcal{V}_L} H^p(V) \,.$$

We can rewrite the entire sequence as the direct limit of a directed system of exact sequences indexed by  $\mathcal{U}_{K,L}$ , since the order-preserving maps

$$\mathcal{U}_K \leftarrow \mathcal{U}_{K,L} \rightarrow \mathcal{U}_L$$

$$U \leftarrow (U, V) \mapsto V$$

are both surjective and hence cofinal. So the long exact sequence of a pair in Čech cohomology is the direct limit of the system of long exact sequences of the neighborhood pairs (U, V) and so is exact.

The proof of the excision theorem depends upon another pair of cofinalities.

**Lemma 35.8.** Assume that X is a normal space and A, B closed subsets, or that X is a Hausdorff space and A, B compact subsets. Then the order-preserving maps

$$\mathcal{U}_{(A \cup B,B)} \leftarrow \mathcal{U}_A \times \mathcal{U}_B \rightarrow \mathcal{U}_{(A,A \cap B)}$$

given by

$$(W \cup Y, Y) \longleftrightarrow (W, Y) \mapsto (W, W \cap Y)$$

are both cofinal.

*Proof.* The left map is surjective, because if  $(U, V) \in \mathcal{U}_{A \cup B, B}$  then  $U \in \mathcal{U}_A$ ,  $V \in \mathcal{U}_B$ , and  $(U, V) = (U \cup V, V)$ .

To see that the right map is cofinal, start with  $(U, V) \in \mathcal{U}_{A.A \cap B}$ .

Note that A is disjoint from  $B \cap (X - V)$ , so by normality, or compactness in a Hausdorff space, there exist non-intersecting open sets S and T with  $A \subseteq S$  and  $B \cap (X - V) \subseteq T$ . Then take  $W = U \cap S \in \mathcal{U}_A$  and  $Y = V \cup T \in \mathcal{U}_B$ , and observe that  $W \cap Y = V \cap S$  and so  $(W, W \cap Y) \subseteq (U, V)$ .  $\square$ 

Proof of Theorem 35.3. Combine Lemma 35.8 with excision for singular cohomology:

$$\lim_{(W,Y)\in\mathcal{U}_A\times\mathcal{U}_B} H^p(W\cup Y,Y) \xrightarrow{\cong} \lim_{U_A\times\mathcal{U}_B} H^p(W,W\cap Y)$$

$$\downarrow^{\cong} \qquad \qquad \downarrow^{\cong} \qquad \qquad \downarrow^{\cong}$$

$$\lim_{(U,V)\in\mathcal{U}_{A\cup B,B}} H^p(U,V) \xrightarrow{} \lim_{U,V)\in\mathcal{U}_{A,A\cap B}} H^p(U,V)$$

$$\parallel \qquad \qquad \parallel$$

$$\check{H}^p(A\cup B,B) \xrightarrow{} \check{H}^p(A,A\cap B)$$

The Mayer-Vietoris long exact sequence is a consequence of these two results.

**Corollary 35.9** (Mayer-Vietoris). Suppose A and B are closed subsets of a normal space, or compact subsets of a Hausdorff space. There is a natural long exact sequence:

$$\cdots \to \check{H}^{p-1}(A \cup B) \to \check{H}^{p-1}(A) \oplus \check{H}^p(B) \to \check{H}^{p-1}(A \cap B) \to H^p(A \cup B) \to \cdots.$$

*Proof.* Apply Lemma 11.6 to the ladder

$$\cdots \longrightarrow \check{H}^{p-1}(A \cup B) \longrightarrow \check{H}^{p-1}(B) \longrightarrow \check{H}^{p}(A \cup B, B) \longrightarrow \check{H}^{p}(A \cup B) \longrightarrow \check{H}^{p}(B) \longrightarrow \cdots$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$\cdots \longrightarrow \check{H}^{p-1}(A) \longrightarrow \check{H}^{p-1}(A \cap B) \longrightarrow \check{H}^{p}(A, A \cap B) \longrightarrow \check{H}^{p}(A) \longrightarrow \check{H}^{p}(A \cap B) \longrightarrow \cdots$$

#### 36 The fully relative cap product

Čech cohomology appeared as the natural algebra acting on  $H^*(X, X - K)$ , where K is a closed subspace of X:

$$\cap : \check{H}^p(K) \otimes H_n(X, X - K) \to H_q(X, X - K), \quad p + q = n.$$

If we fix  $x_K \in H_n(X, X - K)$ , then capping with  $x_K$  gives a map

$$\cap x_K : \check{H}^p(K) \to H_q(X, X - K), \quad p + q = n.$$

We will be very interested in showing that this map is an isomorphism under certain conditions. This is a kind of duality result, comparing cohomology and relative homology and reversing the dimensions. We'll try to show that such a map is an isomorphism by embedding it in a map of long exact sequences and using the five-lemma.

For a start, let's think about how these maps vary as we change K. So let L be a closed subset of K, so  $X - K \subseteq X - L$  and we get a "restriction map"

$$i_*: H_n(X, X-K) \to H_n(X, X-L)$$
.

Define  $x_L$  as the image of  $x_K$ . The diagram

$$\check{H}^{p}(K) \longrightarrow \check{H}^{p}(L)$$

commutes by the projection formula. This embeds into a ladder shown in the theorem below. We will accompany this ladder with a second one, to complete the picture.

**Theorem 36.1.** Let  $L \subseteq K$  be closed subspaces of a space X. There is a "fully relative" cap product

$$\cap: \check{H}^p(K,L) \otimes H_n(X,X-K) \to H_q(X-L,X-K), \quad p+q=n,$$

such that for any  $x_K \in H_n(X, X - K)$  the ladder

commutes, where  $x_L$  is the restriction of  $x_K$  to  $H_n(X, X - L)$ , and for any  $x \in H_n(X)$ 

commutes, where  $x_K$  is the restriction of x to  $H_n(X, X - K)$ .

*Proof.* What I have to do is define a cap product along the bottom row of the diagram (with p + q = n)

$$\check{H}^p(K) \otimes H_n(X, X - K) \xrightarrow{\cap} H_q(X, X - K)$$

$$\uparrow \qquad \qquad \uparrow \qquad \qquad \uparrow$$

$$\check{H}^p(K, L) \otimes H_n(X, X - K) - \xrightarrow{\cap} H_q(X - L, X - K)$$

This requires going back to the origin of the cap product. Our map  $\check{H}^p(K) \otimes H_n(X, X - K) \to H_q(X, X - K)$  came (via excision) from a chain map  $S^p(U) \otimes S_n(U, U - K) \to S_q(U, U - K)$  where  $U \supseteq K$ , defined by  $\beta \otimes \sigma \mapsto \beta(\sigma \circ \alpha_p) \cdot (\sigma \circ \omega_q)$ . Now given inclusions

$$\begin{array}{ccc}
L & \subseteq & K \\
 & \cap & & \cap \\
V & \subset & U
\end{array}$$

we can certainly fill in the bottom row of the diagram

$$S^{p}(U) \otimes S_{n}(U)/S_{n}(U-K) \longrightarrow S_{q}(U)/S_{q}(U-K)$$

$$\uparrow \qquad \qquad \uparrow \qquad \qquad \uparrow$$

$$S^{p}(U,V) \otimes S_{n}(U)/S_{n}(U-K) \longrightarrow S_{q}(U-L)/S_{q}(U-K)$$

Since cochains in  $S^p(U,V)$  kill chains in V, we can extend the bottom row to

$$S^{p}(U) \otimes S_{n}(U, U - K) \longrightarrow S_{q}(U, U - K)$$

$$\uparrow \qquad \qquad \uparrow \qquad \qquad \uparrow$$

$$S^{p}(U, V) \otimes (S_{n}(U - L) + S_{n}(V))/S_{n}(U - K) \longrightarrow S_{q}(U - L)/S_{q}(U - K)$$

$$\downarrow \simeq$$

$$S^{p}(U, V) \otimes S_{n}(U)/S_{n}(U - K)$$

But  $L \subseteq V$ , so  $(U-L) \cup V = U$ , and the locality principle then guarantees that  $S_n(U-L) + S_n(V) \to S_n(U)$  is a quasi-isomorphism. By excision,  $H_n(U, U - K) \to H_n(X, X - K)$  is an isomorphism. Now use our standard map  $\mu: H_*(C) \otimes H_*(D) \to H_*(C \otimes D)$ .

This gives the construction of the fully relative cap product. We leave the checks of commutativity to the listener.  $\Box$ 

The diagram

$$\check{H}^{p}(L) \xrightarrow{\delta} \check{H}^{p+1}(K, L) 
\downarrow^{-\cap x_{L}} \qquad \qquad \downarrow^{-\cap x_{K}} 
H_{q}(X, X - L) \xrightarrow{\partial} H_{q-1}(X - L, X - K)$$

provides us with the memorable formula

$$(\delta b) \cap x_K = \partial (b \cap x_L)$$
.

The construction of the Mayer-Vietoris sequences now gives:

**Theorem 36.2.** Let A, B be closed in a normal space or compact in a Hausdorff space. The Čech cohomology and singular homology Mayer-Vietoris sequences are compatible: for any  $x_{A \cup B} \in H_n(X, X - A \cup B)$ , there is a commutative ladder (where again we use the notation  $H_q(X|A) = H_q(X, X - A)$ , and again p + q = n)

$$\cdots \longrightarrow \check{H}^{p}(A \cup B) \longrightarrow \check{H}^{p}(A) \oplus \check{H}^{p}(B) \longrightarrow \check{H}^{p}(A \cap B) \longrightarrow \check{H}^{p+1}(A \cup B) \longrightarrow \cdots$$

$$\downarrow \cap x_{A \cup B} \qquad \qquad \downarrow (\cap x_{A}) \oplus (\cap x_{B}) \qquad \qquad \downarrow \cap x_{A \cap B} \qquad \qquad \downarrow \cap x_{A \cup B}$$

$$\cdots \longrightarrow H_{q}(X|A \cup B) \longrightarrow H_{q}(X|A) \oplus H_{q}(X|B) \longrightarrow H_{q}(X|A \cap B) \longrightarrow H_{q-1}(X|A \cup B) \longrightarrow \cdots$$

in which the homology classes  $x_A, x_B, x_{A \cap B}$  are restrictions of the class  $x_{A \cup B}$  in the diagram

## 37 Poincaré duality

Let M be a n-manifold and K a compact subset. By Theorem 32.1

$$H_n(M, M - K; R) \xrightarrow{\cong} \Gamma(K; o_M \otimes R)$$
.

An orientation along K is a section of  $o_M \otimes R$  over K that restricts to a generator of  $H_n(M, M-x; R)$  for every  $x \in K$ . The corresponding class in  $H_n(M, M-K; R)$  is a fundamental class along K,  $[M]_K$ . We recall also the fully relative cap product pairing (in which p+q=n and L is a closed subset of K)

$$\cap : \check{H}^p(K,L;R) \otimes_R H_n(M,M-K;R) \to H_q(M-L,M-K;R)$$
.

We now combine all of this in the following climactic result.

**Theorem 37.1** (Fully relative Poincaré duality). Let M be an n-manifold and  $K \supseteq L$  a pair of compact subsets. Assume given an R-orientation along K, with corresponding fundamental class  $[M]_K$ . With p + q = n, the map

$$\cap [M]_K : \check{H}^p(K,L;R) \to H_q(M-L,M-K;R)$$
.

is an isomorphism.

We have seen that these isomorphisms are compatible; they form the rungs of the commuting ladder

Also, if M is compact and R-oriented with fundamental class [M] restricting along K to  $[M]_K$ , we have the ladder of isomorphisms

To prove this theorem, we will follow the same five-step process we used to prove the Orientation Theorem 32.1. We have already prepared the Mayer-Vietoris ladder for this purpose. We will also need:

**Lemma 37.2.** Let  $A_1 \supseteq A_2 \supseteq \cdots$  be a decreasing sequence of compact subspaces of M. Then

$$\check{H}^p(A_k) \to \check{H}^p(A)$$

is an isomorphism.

*Proof.* This follows from the observation that a direct limit of direct limits is a direct limit.  $\Box$ 

*Proof of Theorem 37.1.* By the top ladder and the five-lemma, we may assume  $L = \emptyset$ ; so we want to prove that

$$\cap [M]_K : \check{H}^p(K;R) \to H_q(M,M-K;R)$$

is an isomorphism.

(1)  $M = \mathbb{R}^n$ , K a compact convex set. We claim that

$$\check{H}^*(K) \xrightarrow{\cong} H^*(K)$$
.

For any  $\epsilon > 0$ , let  $U_{\epsilon}$  denote the  $\epsilon$ -neighborhood of K,

$$U_{\epsilon} = \bigcup_{x \in K} B_{\epsilon}(x) .$$

For any  $y \in U_{\epsilon}$  there is a closest point in K, since the distance function to y is continuous and bounded below on the compact set K and so achieves its infimum. If  $x', x'' \in K$  are the same distance from y, then the midpoint of the segment joining x' and x'' is closer, but lies in K since K is convex. So there is a unique closest point, f(y). We let the listener check that  $f: U_{\epsilon} \to K$  is continuous. It is also clear that if  $i: K \to U_{\epsilon}$  is the inclusion then  $i \circ f$  is homotopic to the identity on Y, by an affine homotopy.

Now let  $D^n$  be a disk centered at the origin and containing the compact set K, and consider the commutative diagram

$$H^{p}(K) \xrightarrow{\bigcap [\mathbf{R}^{n}]_{K}} H_{q}(\mathbf{R}^{n}, \mathbf{R}^{n} - K)$$

$$\stackrel{\cong}{\downarrow} \cong \qquad \qquad \stackrel{\cong}{\downarrow} \cong$$

$$H^{p}(D^{n}) \xrightarrow{\longrightarrow} H_{q}(\mathbf{R}^{n}, \mathbf{R}^{n} - D^{n})$$

$$\stackrel{\cong}{\downarrow} \cong \qquad \qquad \stackrel{\cong}{\downarrow} \cong$$

$$H^{p}(*) \xrightarrow{\longrightarrow} H_{q}(\mathbf{R}^{n}, \mathbf{R}^{n} - *).$$

The groups are zero unless p = 0, q = n. By naturality of the cap product, the bottom map is given by  $1 \mapsto 1 \cap [\mathbf{R}^n]_*$ , and this is  $[\mathbf{R}^n]_*$  since capping with 1 is the identity, and this fundamental class is a generator of  $H_n(\mathbf{R}^n, \mathbf{R}^n - *)$ .

- (2) K a finite union of compact convex subsets of  $\mathbb{R}^n$ . This follows by induction and the five lemma applied to the Mayer-Vietoris ladder 36.2.
- (3) K is any compact subset of  $\mathbb{R}^n$ . This follows as before by a limit argument, using Lemmas 32.4 and 37.2.
- (4) M arbitrary, K is a finite union of compact Euclidean subsets of M. This follows from (3) and Theorem 36.2.
- (5) M arbitrary, K an arbitrary compact subset. This follows just as in the proof of Theorem 32.1.

Let's point out some special cases. With K = M, we get:

**Corollary 37.3.** Suppose that M is a compact R-oriented n-manifold, and let L be a closed subset. Then (with p + q = n) we have the commuting ladder whose rungs are isomorphisms:

With  $L = \emptyset$ , we get:

**Corollary 37.4.** Suppose that M is an n-manifold, and let K be a compact subset. An R-orientation along K determines (with p + q = n) an isomorphism

$$\cap [M]_K : \check{H}^p(K;R) \to H_q(M,M-K;R)$$
.

The intersection of these two special cases is:

Corollary 37.5 (Poincaré duality). Let M be a compact R-oriented n-manifold. Then

$$\cap [M]: H^p(M;R) \to H_{n-p}(M;R)$$

is an isomorphism.

38. APPLICATIONS 105

## 38 Applications

Today we harvest consequences of Poincaré duality. We'll use the form

**Theorem 38.1.** Let M be an n-manifold and K a compact subset. An R-orientation along K determines a fundamental class  $[M]_K \in H_n(M, M - K)$ , and capping gives an isomorphism:

$$\cap [M]_K : \check{H}^{n-q}(K;R) \xrightarrow{\cong} H_q(M,M-K;R).$$

Corollary 38.2.  $\check{H}^p(K;R) = 0$  for p > n.

We can contrast this with singular (co)homology. Here's an example:

**Example 38.3** (Barratt-Milnor, [1]). A two-dimensional version K of the Hawaiian earring, i.e., nested spheres all tangent to a point whose radii are going to zero. What they proved is that  $H_q(K; \mathbf{Q})$  is uncountable for every q > 1. But Čech cohomology is much more well-behaved.

**Theorem 38.4** (Alexander duality). For any compact subset K of  $\mathbb{R}^n$ , the composite

$$\check{H}^{n-q}(K;R) \xrightarrow{\cap [\mathbf{R}^n]_K} H_q(\mathbf{R}^n, \mathbf{R}^n - K; R) \xrightarrow{\partial} \widetilde{H}_{q-1}(\mathbf{R}^n - K; R)$$

is an isomorphism.

Proof. 
$$\widetilde{H}^*(\mathbf{R}^n;R)=0$$
.

This is extremely useful! For example

Corollary 38.5. If K is a compact subset of  $\mathbb{R}^n$  then  $\check{H}^n(K;R)=0$ .

Corollary 38.6. The complement of a knot in  $S^3$  is a homology circle.

**Example 38.7.** Take the case q = 1:

$$\check{H}^{n-1}(K;R) \xrightarrow{\cong} \widetilde{H}_0(\mathbf{R}^n - K;R) = \ker(\varepsilon : R\pi_0(\mathbf{R}^n - K) \to R).$$

The augmentation is a split surjection, so this is a free R-module. This shows, for example, that  $\mathbf{RP}^2$  can't be embedded in  $\mathbf{R}^3$  – at least not with a regular neighborhood.

If we take n = 2 and suppose that  $\check{H}^*(K) = H^*(S^1)$ , we find that the complement of K has two path components. This is the Jordan Curve Theorem.

There is a useful purely cohomological consequence of Poincaré duality, obtained by combining it with the universal coefficient theorem

$$0 \to \operatorname{Ext}^1_{\mathbf{Z}}(H_{q-1}(X), \mathbf{Z}) \to H^q(X) \to \operatorname{Hom}(H_q(X), \mathbf{Z}) \to 0$$
.

First, note that  $\operatorname{Hom}(H_q(X), \mathbf{Z})$  is always torsion-free. If I assume that  $H_{q-1}(X)$  is finitely generated, then  $\operatorname{Ext}^1_{\mathbf{Z}}(H_{q-1}(X), \mathbf{Z})$  is a finite abelian group. So the UCT is providing the short exact sequence

$$0 \to \mathrm{tors} H^q(X) \to H^q(X) \to H^q(X)/\mathrm{tors} \to 0$$

- that is,

$$H^q(X)/\mathrm{tors} \xrightarrow{\cong} \mathrm{Hom}(H_q(X)/\mathrm{tors}, \mathbf{Z})$$
.

That is to say, the Kronecker pairing descends to a perfect pairing

$$\frac{H^q(X)}{\mathrm{tors}} \otimes \frac{H_q(X)}{\mathrm{tors}} \to \mathbf{Z}$$
.

Let's combine this with Poincaré duality. Let X=M be a compact oriented n-manifold, so that

$$\cap [M]: H^{n-q}(M) \xrightarrow{\cong} H_q(M)$$
.

We get a perfect pairing

$$\frac{H^q(X)}{\mathrm{tors}}\otimes \frac{H^{n-q}(X)}{\mathrm{tors}}\to \mathbf{Z}$$
.

And what is that pairing? It's given by the composite

$$H^{q}(M) \otimes H^{n-q}(M) \longrightarrow \mathbf{Z}$$

$$1 \otimes (-\cap [M]) \downarrow \qquad (-,-)$$

$$H^{q}(M) \otimes H_{q}(M)$$

and we've seen that

$$\langle a, b \cap [M] \rangle = \langle a \cup b, [M] \rangle$$

We have used  $R = \mathbf{Z}$ , but the same argument works for any PID – in particular for any field, in which case tors V = 0. We have proven:

**Theorem 38.8.** Let R be a PID an M a compact R-oriented n-manifold. Then

$$a \otimes b \mapsto \langle a \cup b, [M] \rangle$$

induces a perfect pairing (with p + q = n)

$$\frac{H^p(M;R)}{\mathrm{tors}} \otimes_R \frac{H^q(M;R)}{\mathrm{tors}} \to R.$$

**Example 38.9.** Complex projective 2-space is a compact 4-manifold, orientable since it is simply connected. It has a cell structure with cells in dimensions 0, 2, and 4, so its homology is  $\mathbf{Z}$  in those dimensions and 0 elsewhere, and so the same is true of its cohomology. Up till now the cup product structure has been a mystery. But now we know that

$$H^2(\mathbf{CP}^2) \otimes H^2(\mathbf{CP}^2) \to H^4(\mathbf{CP}^2)$$

is a perfect pairing. So if we write a for a generator of  $H^2(\mathbf{CP}^2)$ , then  $a \cup a = a^2$  is a free generator for  $H^4(\mathbf{CP}^2)$ . We have discovered that

$$H^*(\mathbf{CP}^2) = \mathbf{Z}[a]/a^3.$$

By the way, notice that if we had chosen -a as a generator, we would still produce the same generator for  $H^4(\mathbf{CP}^2)$ : so there is a preferred orientation, the one whose fundamental class pairs to 1 against  $a^2$ .

This calculation shows that while  $\mathbb{CP}^2$  and  $S^2 \vee S^4$  are both simply connected and have the same homology, they are not homotopy equivalent. This implies that the attaching map  $S^3 \to S^2$  for the top cell in  $\mathbb{CP}^2$  – the  $Hopf\ map$  – is essential.

How about  $\mathbb{CP}^3$ ? It just adds a 6-cell, so now  $H^6(\mathbb{CP}^3) \cong \mathbb{Z}$ . The pairing  $H^2(\mathbb{CP}^3) \otimes H^4(\mathbb{CP}^3) \to H^6(\mathbb{CP}^3)$  is perfect, so we find that  $a^3$  generates  $H^6(\mathbb{CP}^3)$ . Continuing in this way, we have

$$H^*(\mathbf{CP}^n) = \mathbf{Z}[a]/(a^{n+1}).$$

38. APPLICATIONS 107

Example 38.10. Exactly the same argument shows that

$$H^*(\mathbf{RP}^n; \mathbf{F}_2) = \mathbf{F}_2[a]/(a^{n+1})$$

where |a| = 1.

I'll end with the following application.

**Theorem 38.11** (Borsuk-Ulam). Think of  $S^n$  as the unit vectors in  $\mathbb{R}^{n+1}$ . For any continuous function  $f: S^n \to \mathbb{R}^n$ , there exists  $x \in S^n$  such that f(x) = f(-x).

*Proof.* Suppose that no such x exists. Then we may define a continuous function  $g: S^n \to S^{n-1}$  by

$$g: x \mapsto \frac{f(x) - f(-x)}{||f(x) - f(-x)||}.$$

Note that g(-x) = -g(x): g is equivariant with respect to the antipodal action. It descends to a map  $\overline{g}: \mathbf{RP}^n \to \mathbf{RP}^{n-1}$ .

We claim that  $\overline{g}_*: H_1(\mathbf{RP}^n) \to H_1(\mathbf{RP}^{n-1})$  is nontrivial. To see this, pick a basepoint  $b \in S^n$  and choose a 1-simplex  $\sigma: \Delta^1 \to S^n$  such that  $\sigma(e_0) = b$  and  $\sigma(e_1) = -b$ . The group  $H_1(\mathbf{RP}^n)$  is generated by the cycle  $p\sigma$ . The image of this cycle in  $H_1(\mathbf{RP}^{n-1})$  is represented by the loop  $gp\sigma$  at  $\overline{b} = pb$ , which is the image of the 1-simplex  $g\sigma$  joining gb to g(-b) = -g(b). The class of this 1-simplex thus generates  $H_1(\mathbf{RP}^{n-1})$ .

Therefore  $\overline{g}$  is nontrivial in  $H_1(-; \mathbf{F}_2)$ , and hence also in  $H^1(-; \mathbf{F}_2)$ . Writing  $a_n$  for the generator of  $H^1(\mathbf{RP}^n; \mathbf{F}_2)$ , we must have  $a_n = g^*a_{n-1}$ , and consequently  $a_n^n = (g^*a_{n-1})^n = g^*(a_{n-1}^n)$ . But  $H^n(\mathbf{RP}^{n-1}; \mathbf{F}_2) = 0$ , so  $a_{n-1}^n = 0$ ; while  $a_n^n \neq 0$ . This is a contradiction.

# **Bibliography**

- [1] M. G. Barratt and J. Milnor, An example of anomalous singular homology, Proc. Amer. Math. Soc. 13 (1962) 293–297.
- [2] G. Bredon, Topology and Geometry, Springer-Verlag, 1993.
- [3] A. Dold, Lectures on Algebraic Topology, Springer-Verlag, 1980.
- [4] S. Eilenberg and J. C. Moore, Homology and fibrations, I: Coalgebras, cotensor product and its derived functors, Comment. Math. Helv. 40 (1965) 199–236.
- [5] S. Eilenberg and N. Steenrod, Foundations of Algebraic Topology, Princeton University Press, 1952.
- [6] A. Hatcher, Algebraic Topology, Cambridge University Press, 2002.
- [7] D. Kan, Adjoint funtors, Trans. Amer. Math. Soc. 87 (1958) 294–329.
- [8] J. Milnor, On axiomatic homology theory, Pacific J. Math 12 (1962) 337–341.
- [9] J. C. Moore, On the homotopy groups of spaces with a single non-vanishing homology group, Ann. Math. 59 (1954) 549–557.
- [10] C. T. C Wall, Finiteness conditions for CW complexes, Ann. Math. 81 (1965) 56–69.

MIT OpenCourseWare https://ocw.mit.edu

18.905 Algebraic Topology I Fall 2016

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.