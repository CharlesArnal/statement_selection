# Lectures on Algebraic Topology II

Lectures by Haynes Miller
Notes based in part on liveTrXed record made by Sanath Devalapurkar

Spring 2020

These notes represent my lectures in 18.906, the second half of a two-semester course on Algebraic Topology offered at MIT in spring 2020. I led both 18.905 and 18.906 in 2016–2017, and the record of lectures in the first course is available on MIT OpenCourseWare. The lectures of both the earlier courses were live TeXed by Sanath Devalapurkar, and his notes formed the invaluable starting point, especially for 18.905. I made many changes in the 2020 version of 18.906 and less remains of Sanath's notes in the present text.

This second course was about homotopy theory and its applications. The course divides into five units. As in the first semester, I emphasize basic categorical structures – here, limits, colimits, and adjunctions. These suggest the "convenient" refinement of the category of topological spaces provided by the cartesian closed category of compactly generated spaces. I discuss fibrations, cofibrations, and homotopy groups. Much of the second unit deals with the conveniences afforded by working with CW complexes. I state the Hurewicz and Whitehead theorems, but delay proofs till we have Serre's machinery set up, at which point their generalization modulo a Serre class can be proven simultaneously. I gave some hints about obstruction theory, but not complete proofs.

In the third unit I discuss vector bundles and principal bundles. I briefly develop the theory of G-CW-complexes to give a proof that the  $\operatorname{Bun}_G$  is a homotopy functor. In these notes I develop the theory of classifying spaces from Graeme Segal's simplicial perspective, since these method have proven so valuable and provide a very concrete construction of these spaces. Unfortunately, this was the spring of COVID-19, and this topic fell prey to four cancelled classes. The remaining two units were conducted online.

Next is the theory of spectral sequences, with special reference to the Serre spectral sequence. I set up the theory of Serre classes, and carry out Serre's proof of the Hurewicz theorem. In lieu of a detailed treatment of multiplicative structure, I describe Dress's bisimplicial construction of the Serre (or more generally Leray) spectral sequence. This section ends with applications to the Gysin sequence and Thom isomorphism.

The final unit applies this machinery to the study of characteristic classes, and sketches some of their applications. I start with Grothendieck's construction of Chern (and Stiefel-Whitney) classes, verify the splitting principle, and discuss the Thom isomorphism and the Thom class. I introduce the Pontryagin classes and sketch a computation of the cohomology of BSO(n) and BO(n) away from 2. Then I construct Steenrod operations, talk about cobordism, the Pontryagin-Thom collapse, and transversality; then introduce Hopf algebras as a useful tool and sketch Thom's work, including a brief account of his counterexample to Steenrod's question; and end with a discussion of the rational oriented bordism ring and the proof of the Hirzebruch signature theorem.

These notes reflect approximately what actually happened in the classroom. Many details are consequently omitted, in favor of more discussion of examples and how the theory fits together.

# Contents

| $\mathbf{C}_{0}$          | Contents                                         |                                                                                                                                                                                                                                                                                                                        |                                                 |  |
|---------------------------|--------------------------------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------------|--|
| 1                         | Bas<br>1<br>2<br>3<br>4<br>5<br>6<br>7<br>8<br>9 | Limits, colimits, and adjunctions Cartesian closure and compactly generated spaces Basepoints and the homotopy category Fiber bundles Fibrations, fundamental groupoid Cofibrations Cofibration sequences and co-exactness Weak equivalences and Whitehead's Theorems Homotopy long exact sequence and homotopy fibers | 1<br>4<br>8<br>11<br>13<br>17<br>20<br>23<br>27 |  |
| 2                         | The 10 11 12 13 14 15                            |                                                                                                                                                                                                                                                                                                                        | 31<br>34<br>37<br>40<br>43<br>47                |  |
| 3                         | Vec<br>16<br>17<br>18<br>19<br>20<br>21          | tor bundles and principal bundles         Vector bundles          Principal bundles, associated bundles $I$ -invariance of $Bun_G$ , and $G$ -CW-complexes          The classifying space of a group          Simplicial sets and classifying spaces          The Čech category and classifying maps                   | 53<br>56<br>59<br>62<br>65<br>68                |  |
| 4                         | Spe 22 23 24 25 26 27 28 29                      | Ctral sequences and Serre classes  Why spectral sequences?  The spectral sequence of a filtered complex  Serre spectral sequence  Exact couples  The Gysin sequence  Serre and Hurewicz  Double complexes and the Dress spectral sequence  Cohomological spectral sequences                                            | 73 76 80 83 86 91                               |  |
|                           | 30                                               | Serre classes                                                                                                                                                                                                                                                                                                          | 104                                             |  |
|                           | 31                                               | Mod ${\bf C}$ Hurewicz and Whitehead theorems                                                                                                                                                                                                                                                                          | 108                                             |  |
|                           | 32                                               | Freudenthal, James, and Bousfield                                                                                                                                                                                                                                                                                      | 112                                             |  |
| 5                         | Cha                                              | aracteristic classes                                                                                                                                                                                                                                                                                                   | 119                                             |  |
|                           | 33                                               | Chern Classes                                                                                                                                                                                                                                                                                                          | 119                                             |  |
|                           | 34                                               | $H^*(BU(n))$ and the splitting principle                                                                                                                                                                                                                                                                               | 124                                             |  |
|                           | 35                                               | The Thom class and Whitney sum formula                                                                                                                                                                                                                                                                                 | 129                                             |  |
|                           | 36                                               | Closing the Chern circle, and Pontryagin classes                                                                                                                                                                                                                                                                       | 133                                             |  |
|                           | 37                                               | Steenrod operations                                                                                                                                                                                                                                                                                                    | 137                                             |  |
|                           | 38                                               | Cobordism                                                                                                                                                                                                                                                                                                              | 143                                             |  |
|                           | 39                                               | Hopf algebras                                                                                                                                                                                                                                                                                                          | 148                                             |  |
|                           | 40                                               | Applications of cobordism                                                                                                                                                                                                                                                                                              | 152                                             |  |
| $\mathbf{B}^{\mathbf{i}}$ | ibliog                                           | graphy                                                                                                                                                                                                                                                                                                                 | 159                                             |  |

CONTENTS iii

# Chapter 1

# Basic homotopy theory

# 1 Limits, colimits, and adjunctions

#### Limits and colimits

I want to begin by developing a little more category theory. I still refer to the classic text *Categories* for the Working Mathematician by Saunders Mac Lane [20] for this material.

**Definition 1.1.** Suppose  $\mathcal{I}$  is a small category (so that it has a *set* of objects), and let  $\mathcal{C}$  be another category. Let  $X: \mathcal{I} \to \mathcal{C}$  be a functor. A *cone under* X is a natural transformation e from X to a constant functor; to be explicit, this means that for every object i of  $\mathcal{I}$  we have a map  $e_i: X_i \to Y$ , and these maps are compatible in the sense that for every  $f: i \to j$  in  $\mathcal{I}$  the following diagram commutes:

$$X_{i} \xrightarrow{e_{i}} Y$$

$$\downarrow f_{*} \qquad \downarrow =$$

$$X_{j} \xrightarrow{e_{j}} Y$$

A colimit of X is an initial cone  $(L, t_i)$  under X; to be explicit, this means that for any cone  $(Y, e_i)$  under X, there exists a unique map  $h: L \to Y$  such that  $h \circ t_i = e_i$  for all i.

Any two colimits are isomorphic by a unique isomorphism compatible with the structure maps; but existence is another matter. Also, as always for category theoretic concepts, some examples are in order.

**Example 1.2.** If  $\mathcal{I}$  is a discrete category (that is, the only maps are identity maps;  $\mathcal{I}$  is entirely determined by its set of objects), the colimit of a functor  $\mathcal{I} \to \mathcal{C}$  is the coproduct in  $\mathcal{C}$  (if this coproduct exists!).

**Example 1.3.** In Lecture 23 we discussed directed posets and the direct limit of a directed system  $X: \mathcal{I} \to \mathcal{C}$ . The colimit simply generalizes this to arbitrary indexing categories rather than restricting to directed partially ordered sets.

**Example 1.4.** Let G be a group; we can view this as a category with one object, where the morphisms are the elements of the group and composition is given by the group structure. If  $\mathcal{C} = \mathbf{Top}$  is the category of topological spaces, a functor  $G \to \mathcal{C}$  is simply a group action on a topological space X. The colimit of this functor is the orbit space of the G-action on X (together with the projection map to the orbit space).

Similarly, a functor from G into vector spaces over a field k is a representation of G on a vector space. Question for you: What is the colimit in this case?

**Example 1.5.** Let  $\mathcal{I}$  be the category whose objects and non-identity morphisms are described by the following directed graph:

$$b \leftarrow a \rightarrow c$$
.

The colimit of a diagram  $\mathcal{I} \to \mathcal{C}$  is called a *pushout*. With  $\mathcal{C} = \mathbf{Top}$ , again, a functor  $\mathcal{I} \to \mathcal{C}$  is determined by a diagram of spaces:

$$A \stackrel{f}{\leftarrow} B \stackrel{g}{\rightarrow} C$$
.

The colimit of such a functor is just the pushout  $B \cup_A C := B \sqcup C / \sim$ , where  $f(a) \sim g(a)$  for all  $a \in A$ . We have already seen this in action before: a special case of this construction appears in the process of attaching cells to build up a CW-complex.

If C is the category of groups, instead, the colimit of such a functor is the free product quotiented out by a certain relation; this is called the *amalgamated free product*.

**Example 1.6.** Suppose  $\mathcal{I}$  is the category with two objects and two parallel morphisms:

$$a \Longrightarrow b$$
.

The colimit of a diagram  $\mathcal{I} \to \mathcal{C}$  is called the *coequalizer* of the diagram. If  $\mathcal{C} = \mathbf{Top}$ , the coequalizer of  $f, g : A \Rightarrow B$  is the quotient of B by the equivalence relation generated by  $f(a) \sim g(a)$  for  $a \in A$ .

One can also consider cones *over* a diagram  $X: \mathcal{I} \to \mathcal{C}$ : this is simply a cone in the opposite category.

**Definition 1.7.** The *limit* of a diagram  $X: \mathcal{I} \to \mathcal{C}$  is a terminal object in cones over X.

**Exercise 1.8.** Revisit the examples provided above: what is the limit of each diagram? For instance, a product is a limit over a discrete category, and the limit of a group action is just the fixed points. A diagram indexed by the category  $b \to a \leftarrow c$  is a diagram  $B \xrightarrow{f} A \xleftarrow{g} C$ , and its limit is the "pullback," denoted  $B \times_A C$ . In **Set**, or **Top**,

$$B \times_A C = \{(b, c) \in B \times C : f(b) = g(c) \in A\}.$$

**Definition 1.9.** A category C is *cocomplete* if all functors from small categories to C have colimits. Similarly, C is *complete* if all functors from small categories to C have limits.

All the large categories we typically deal with are both cocomplete and complete; in particular both **Set** and **Top** are, as well as algebraic categories like **Gp** and  $R - \mathbf{Mod}$ .

#### Adjoint functors

The notion of a colimit as a special case of the more general concept of an adjoint functor, as long as we are dealing with a cocomplete category.

Let's write  $\mathcal{C}^{\mathcal{I}}$  for the category of functors from  $\mathcal{I}$  to  $\mathcal{C}$ , and natural transformations between them. There is a functor  $c: \mathcal{C} \to \mathcal{C}^{\mathcal{I}}$ , given by sending any object to the constant functor taking on that value. The process of taking the colimit of a diagram supplies us with a functor colim<sub> $\mathcal{I}$ </sub>:  $\mathcal{C}^{\mathcal{I}} \to \mathcal{C}$ . (To be precise, we pick a specific colimit for each diagram, and then observe that a natural transformation of diagrams canonically defines a morphism between the corresponding colimits; and that these morphisms compose correctly.) We can characterize this functor via the formula

$$C(\underset{i \in \mathcal{I}}{\operatorname{colim}} X_i, Y) = \mathcal{C}^{\mathcal{I}}(X, c_Y),$$

where X is any functor from  $\mathcal{I}$  to  $\mathcal{C}$ , Y is any object of  $\mathcal{C}$ , and  $c_Y$  denotes the constant functor with value Y. This formula is reminiscent of the adjunction operation in linear algebra, and is in fact our first example of a category-theoretic adjunction.

**Definition 1.10.** Let  $\mathcal{C}, \mathcal{D}$  be categories, and suppose given functors  $F : \mathcal{C} \to \mathcal{D}$  and  $G : \mathcal{D} \to \mathcal{C}$ . An adjunction between F and G is an isomorphism

$$\mathcal{D}(FX,Y) = \mathcal{C}(X,GY)$$

that is natural in X and Y. In this situation, we say that F is a *left adjoint* of G and G is a *right adjoint* of F.

This notion was invented by the late MIT Professor Dan Kan, in 1958.

We've already seen one example of adjoint functors. Here is another one.

**Example 1.11** (Free groups). There is a forgetful functor  $u : \mathbf{Grp} \to \mathbf{Set}$ . Any set X gives rise to a group FX, the free group on X. It is determined by a universal property: For any group  $\Gamma$ , set maps  $X \to u\Gamma$  are the same as group homomorphisms  $FX \to \Gamma$ . This is exactly saying that the free group functor the left adjoint to the forgetful functor u.

In general, "free objects" come from left adjoints of forgetful functors.

As a general notational practice, try to write the left adjoint as the top arrow:

$$F: \mathcal{C} \rightleftharpoons \mathcal{D}: G$$
 or  $G: \mathcal{D} \leftrightarrows \mathcal{C}: F$ .

These examples suggest that if a functor F has a right adjoint then any two right adjoints are canonically isomorphic. This is true and easily checked. We'll always speak of *the* right adjoint, or *the* left adjoint.

Lemma 1.12. Suppose that

$$\mathcal{C} \stackrel{F}{\underset{G}{\rightleftarrows}} \mathcal{D} \stackrel{F'}{\underset{G'}{\rightleftarrows}} \mathcal{E}$$

is a composable pair of adjoint functors. Then F'F, GG' form an adjoint pair.

*Proof.* Compute:

$$\mathcal{E}(F'FX,Z) = \mathcal{D}(FX,G'Y) = \mathcal{C}(X,GG'Y).$$

**Proposition 1.13.** Let  $F: \mathcal{C} \to \mathcal{D}$  be a functor. If F admits a right adjoint then it preserves colimits, in the sense that if  $X: \mathcal{I} \to \mathcal{C}$  is a diagram in  $\mathcal{C}$  with colimit cone  $X \to c_L$ , then  $F \circ X \to F(c_L)$  is a colimit cone in  $\mathcal{D}$ . Dually, if F admits a left adjoint then it preserves limits.

*Proof.* This follows from the lemma. The adjoint pair  $F: \mathcal{C} \rightleftharpoons \mathcal{D}: G$  induces an adjoint pair

$$F \cdot \mathcal{C}^{\mathcal{I}} \rightharpoonup \mathcal{D}^{\mathcal{I}} \cdot G$$

Clearly  $c_{GY} = Gc_Y$ ; this is an equality of right adjoints, so the corresponding left adjoints must be equal:

$$\begin{array}{c|c}
\mathcal{C}^{\mathcal{I}} & \xrightarrow{F} \mathcal{D}^{\mathcal{I}} \\
c & & c \\
c & & colim & c \\
C & \xrightarrow{F} \mathcal{D}
\end{array}$$

That is to say,  $\operatorname{colim} FX = F \operatorname{colim} X$ .

For example, the free group on a disjoint union of sets is the free product of the two groups (which is the coproduct in the category of groups). The dual statement says, for example, that the product (in the category of groups) of groups is a group structure on the product of their underlying sets.

#### The Yoneda lemma

An important and rather Wittgensteinian principle in category theory is that an object is determined by the collection of all maps out of it. The Yoneda lemma is a way of making this precise. Observe that for any  $X \in \mathcal{C}$  the association  $Y \mapsto \mathcal{C}(X,Y)$  gives us a functor  $\mathcal{C} \to \mathbf{Set}$ . This functor is said to be *corepresented* by X. Suppose that  $G: \mathcal{C} \to \mathbf{Set}$  is any functor. An element  $x \in G(X)$  determines a natural transformation

$$\theta_x: \mathcal{C}(X,-) \to G$$

in the following way. Let  $Y \in \mathcal{C}$  and  $f: X \to Y$ , and define

$$\theta_x(f) = f_*(x) \in G(Y)$$
.

**Lemma 1.14** (Yoneda lemma). The association  $x \mapsto \theta_x$  provides a bijection

$$G(X) \xrightarrow{\cong} \operatorname{nt}(\mathcal{C}(X, -), G).$$

*Proof.* The inverse sends a natural transformation  $\theta: \mathcal{C}(X, -) \to G$  to  $\theta_X(1_X) \in G(X)$ .

In particular, if G is also corepresentable –  $G = \mathcal{C}(Y, -)$ , say – then

$$\operatorname{nt}(\mathcal{C}(X,-),\mathcal{C}(Y,-)) \cong \mathcal{C}(Y,X)$$
.

That is, each natural transformation  $\mathcal{C}(X,-) \to \mathcal{C}(Y,-)$  is induced by a unique map  $Y \to X$ . Consequently any natural isomorphism  $\mathcal{C}(X,-) \xrightarrow{\cong} \mathcal{C}(Y,-)$  is induced by a unique isomorphism  $Y \xrightarrow{\cong} X$ .

# 2 Cartesian closure and compactly generated spaces

The category of topological spaces has a lot to recommend it, but it does not accommodate constructions from algebraic topology gracefully. For example, the product of two CW complexes may fail to have a CW structure. (This is a classic example due to Clifford Dowker, 1952, nicely explained in [12, Appendix]. The CW complexes involved are one-dimensional!) This is closely related to the observation that if  $X \to Y$  is a quotient map, the induced map  $W \times X \to W \times Y$  may fail to be a quotient map.

It turns out that these problems can be avoided by working in a carefully designed subcategory of  $\mathbf{Top}$ , the category  $k\mathbf{Top}$  of "compactly generated spaces." The key idea is that the unwanted behavior of  $\mathbf{Top}$  is related to the fact that there isn't a well-behaved topology on the set of continuous maps between two spaces. The compact-open topology is available to us – and we'll recall it later. But it suffers from some defects. To clarify how a mapping object should behave in an ideal world, I want to make another category-theoretical digression. Again, Mac Lane's book [20] is a good reference.

#### Cartesian closure

How should function objects behave? In the category **Set**, for example, the set of maps from X to Y can be characterized by the natural bijection

$$\mathbf{Set}(W \times X, Y) = \mathbf{Set}(W, \mathbf{Set}(X, Y))$$

under which  $f: W \times X \to Y$  corresponds to  $w \mapsto (x \mapsto f(w,x))$  and  $g: W \to \mathbf{Set}(X,Y)$  corresponds to  $(w,x) \mapsto g(w)(x)$ . This suggests the following definition.

**Definition 2.1.** Let  $\mathcal{C}$  be a category with finite products. It is *Cartesian closed* if for any object X in  $\mathcal{C}$ , the functor  $-\times X$  has a right adjoint.

We'll write the right adjoint to  $-\times X$  using exponential notation,

$$Y \mapsto Y^X$$
,

so that there is a bijection natural in the pair (W, Y):

$$C(W \times X, Y) = C(W, Y^X).$$

In a Cartesian closed category,  $Y^X$  serves as a "mapping object" from X to Y. Let me convince you that this is reasonable. Take  $Y = W \times X$ : the identity map on  $W \times X$  then corresponds to a map

$$\eta_W: W \to (W \times X)^X$$
.

Take  $W = Y^X$ : the identity map  $Y^X \to Y^X$  corresponds to a map

$$\epsilon_Y: Y^X \times X \to Y$$
.

These maps are natural transformations. In the example of **Set**, the first is given by

$$w \mapsto (x \mapsto (w, x))$$
, inclusion of a slice,

and the second is given by

$$(f,x) \mapsto f(x)$$
, evaluation.

Here are some direct consequences of Cartesian closure. Note: the assumption that finite products exist in  $\mathcal{C}$  includes the case in which the indexing set is empty, in which case the universal property of the product characterizes the terminal object of  $\mathcal{C}$ , which thus exist in a Cartesian closed category. We'll denote it by \*. You might call  $\mathcal{C}(*, X)$  the "set of points" in X.

**Proposition 2.2.** Let C be Cartesian closed.

- (1)  $(X,Z) \mapsto Z^X$  extends canonically to a functor  $\mathcal{C}^{op} \times \mathcal{C} \to \mathcal{C}$ , and the bijection  $\mathcal{C}(X \times Y,Z) = \mathcal{C}(Y,Z^X)$  is natural in all three variables.
- $(2) \mathcal{C}(X,Z) = \mathcal{C}(*,Z^X).$
- (3)  $X \times -$  preserves colimits: If  $Y : \mathcal{I} \to \mathcal{C}$  has a colimit, then the natural map  $X \times Y \to X \times \operatorname{colim} Y$  is a colimit cone.
- (4)  $-^X$  preserves limits: if  $Z: \mathcal{I} \to \mathcal{C}$  has a limit, then the natural map  $(\lim Z)^X \to (Z^X)$  is a limit cone.

Many otherwise well-behaved categories are not Cartesian-closed. A category is *pointed* if it has an initial object  $\varnothing$  and a final object \*, and the unique map  $\varnothing \to *$  is an isomorphism. There are many pointed categories! – abelian groups  $\mathbf{Ab}$  and groups  $\mathbf{Gp}$ , for example. By (2), the only way a pointed category can be Cartesian closed is if there is exactly one map between any two objects.

#### k-spaces

The category **Top** is not Cartesian closed. We can see this using the observation (for which see for example MIT professor emeritus Jim Munkres's Topology [30]) that if  $X \to Y$  is a quotient map, the induced map  $W \times X \to W \times Y$  may fail to be a quotient map. We can characterize quotient maps in **Top** categorically using the following definition.

**Definition 2.3.** An effective epimorphism in a category  $\mathcal{C}$  is a map  $X \to Y$  in  $\mathcal{C}$  such that the pullback  $X \times_Y X$  exists and the map  $X \to Y$  is the coequalizer of the two projection maps  $X \times_Y X \to X$ .

**Lemma 2.4.** A map in **Top** is a quotient map if and only if it is an effective epimorphism.

So item 3 of Proposition 2.2 shows that, sadly, **Top** is not Cartesian closed.

On the other hand, Henry Whitehead showed that crossing with a locally compact Hausdorff space *does* preserve quotient maps. This will often suffice, but often not: for example CW complexes may fail to be locally compact. And the convenience of working in a Cartesian closed category is compelling.

Inspired by Whitehead's theorem, we agree to accept only properties of a space that can be observed by mapping compact Hausdorff spaces into it.

**Definition 2.5.** Let X be a space. A subspace  $F \subseteq X$  is said to be *compactly closed*, or k-closed, if for any map  $k: K \to X$  from a compact Hausdorff space K the preimage  $k^{-1}(F) \subseteq K$  is closed.

It is clear that any closed subset is compactly closed, but there might be compactly closed sets that are not closed in the topology on X. This motivates the definition of a k-space:

**Definition 2.6.** A topological space X is *compactly generated* or is a k-space if every compactly closed set is closed.

The k comes from the German "kompact," though it might have referred to the general topologist John Kelley, who explored this condition.

A more categorical characterization of this property is: X is compactly generated if and only if a map  $X \to Y$  is continuous precisely when for every compact Hausdorff space K and map  $K: K \to X$  the composite  $K \to X \to Y$  is continuous. For instance, compact Hausdorff spaces are K-spaces. First countable spaces (so for example metric spaces) and CW-complexes are also K-spaces.

While not all topological spaces are k-spaces, any space can be "k-ified." The procedure is simple: endow the underlying set of a space X with an new topology, one for which the closed sets are precisely the sets that are compactly closed with respect to the original topology. You should check that this is indeed a topology on X. The resulting topological space is denoted kX. This construction immediately implies that the identity  $kX \to X$  is continuous, and is the terminal map to X from a k-space.

Let k**Top** be the category of k-spaces, as a full subcategory of **Top**. We will write j: k**Top**  $\to$  **Top** for the inclusion functor. The process of k-ification gives a functor k:**Top**  $\to k$ **Top** with the property that

$$k$$
**Top** $(X, kY) =$  **Top** $(jX, Y)$ .

This is another example of an adjunction! In this case the unit  $\eta: X \to kjX$  is a homeomorphism. We can conclude from this that limits in k**Top** may be computed by k-ifying limits in **Top**: For any functor  $X: \mathcal{I} \to k$ **Top**,

$$\lim^{k \operatorname{Top}} X \xrightarrow{\cong} \lim^{k \operatorname{Top}} kjX \xleftarrow{\cong} k \lim^{\operatorname{Top}} jX.$$

The second map is an isomorphism because k is a right adjoint. In particular, the product in k**Top** is formed by k-ifying the product in **Top**. Similarly, colimit (in k**Top**) of any diagram of k-spaces can be computed by k-ifying the colimit in **Top**:

$$\operatorname{colim}^{k\mathbf{Top}} X \xrightarrow{\cong} k j \operatorname{colim}^{k\mathbf{Top}} X \xleftarrow{\cong} k \operatorname{colim}^{\mathbf{Top}} j X$$
.

The second map is an isomorphism because j is a left adjoint.

The category k**Top** has good categorical properties inherited from **Top**: it is a complete and cocomplete category. In fact it has even better categorical properties than **Top** does:

**Proposition 2.7.** The category k**Top** is Cartesian closed.

Proof. See 
$$[39, 10]$$
.

I owe you a description of the mapping object  $Y^X$ . It consists of the set of continuous maps from X to Y endowed with a certain topology. For general topological spaces X and Y, the set  $\mathbf{Top}(X,Y)$  can be given the "compact-open topology": a basis for open sets for the compact-open topology is given by

$$V(F,U) = \{ f : X \to Y : f(F) \subseteq U \}$$

where F runs over compact subsets of X and U runs over open subsets of Y. This space is not generally compactly generated, however, and does not serve as a right adjoint to the product.

If X and Y are k-spaces, it's natural to make a slight modification: To start with, replace the compact subsets F in this definition by "k-compact" subsets, that is, subsets that are compact from the perspective of compact Hausdorff spaces: A subset  $F \subseteq X$  is k-compact if there exists a compact Hausdorff space K and a map  $k: K \to X$  such that k(K) = F. This is to overcome the sad fact that there are compact spaces that do not accept surjections from compact Hausdorff spaces.

The sets V(F, U) where F runs over k-compact subsets of X and U runs over open subsets of Y form the basis of a new topology on  $\mathbf{Top}(X,Y)$ . Even if we assume that X and Y are k-spaces, this new topology may not be compactly generated. But we know what to do: k-ify it. This defines a k-space  $Y^X$ , and this turns out to witness the fact that k  $\mathbf{Top}$  is Cartesian closed.

# 3 Basepoints and the homotopy category

#### More on k-spaces

The ancients (mainly Felix Hausdorff, in 1914) came up with a good definition of a topology – but k-spaces are better!

Most spaces encountered in real life are k-spaces already, and many operations in **Top** preserve the subcategory k**Top**.

**Proposition 3.1** (see [39, 10]). (1) Any locally compact Hausdorff space is compactly generated.

- (2) Quotient spaces and closed subspaces of compactly generated spaces are compactly generated.
- (3) If X is a locally compact Hausdorff space and Y is compactly generated then  $X \times Y$  is again compactly generated.
  - (4) The colimit of any diagram of compactly generated spaces is compactly generated.

As a result of (4), in the homeomorphism

$$k \operatorname{colim}^{\mathbf{Top}} jX_{\bullet} \to \operatorname{colim}^{k\mathbf{Top}} X_{\bullet}$$

that we considered in the last lecture, the space  $\operatorname{colim}^{\mathbf{Top}} jX_{\bullet}$  is in fact already compactly generated; no k-ification is necessary – the colimit constructed in  $\mathbf{Top}$  is the same as the colimit constructed in  $k\mathbf{Top}$ .

When we say "space" in this course, we will always mean k-space, and the various constructions – products, mapping spaces, and so on – will take place in k**Top**.

I should add that there is a version of the Hausdorff condition that is well suited to the compactly generated setting. Check out the sources [39, 10] for this.

Here's a simple example of how useful the formation of mapping spaces can be. We already know that a *homotopy* between maps  $f, g: X \to Y$  is a map  $h: I \times X \to Y$  such that the following diagram commutes.

We write  $f \sim g$  to indicate that f and g are homotopic. This is an equivalence relation on the set  $\mathbf{Top}(X,Y)$ , and we write

$$[X,Y] = \mathbf{Top}(X,Y)/\sim$$

for the set of homotopy classes of maps from X to Y.

The maps f and g are points in the space  $Y^X$ , and the homotopy h is the same thing as a path  $\hat{h}: I \to Y^X$  from f to g. So

$$[X,Y] = \pi_0(Y^X).$$

Another important feature of k-spaces is this:

**Theorem 3.2** (see [12, Theorem A.6]). Let X and Y be CW-complexes with skeleta  $Sk_iX$  and  $Sk_jY$ . Then the k-space product  $X \times Y$  admits the structure of a CW complex in which

$$\operatorname{Sk}_n(X \times Y) = \bigcup_{i+j=n} \operatorname{Sk}_i X \times \operatorname{Sk}_j Y.$$

#### **Basepoints**

To talk about the fundamental group and higher homotopy groups we have to get basepoints into the picture.

A pointed space is a space X together with a specified point in it, to be called the basepoint. It is conventionally denoted by \*, though other symbols may be used as well. The term "basepoint" leads some people refer to "based spaces," but to my ear this makes it sound as if we are doing chemistry, or worse, and I prefer "pointed." We may put restrictions on the choice of basepoint; for example we may require that  $\{*\}$  be a closed subset. We will put a further restriction on  $\{*\} \hookrightarrow X$  in 6.2.

This gives a category k**Top** $_*$  where the morphisms respect the basepoints. This category is complete and cocomplete. For example

$$(X,*) \times (Y,*) = (X \times Y, (*,*))$$

The coproduct is not the disjoint union; which basepoint would you pick? So you identify the two basepoints; the coproduct in k**Top** $_*$  is the "wedge"

$$X \vee Y = \frac{X \sqcup Y}{*_X \sim *_Y} \,.$$

The one-point space \* is the terminal object in  $k\mathbf{Top}_*$ , as in  $k\mathbf{Top}$ , but it is also *initial* in  $k\mathbf{Top}_*$ :  $k\mathbf{Top}_*$  is a pointed category. As we saw, this precludes it from being Cartesian closed. But we still know what we would like to take as a "mapping object" in  $k\mathbf{Top}_*$ : Define  $Y_*^X$  to be the subspace of  $Y^X$  consisting of the pointed maps. In general we may have to k-ify this subspace, but if  $\{*\}$  is closed in Y then  $Y_*^X$  is closed in  $Y^X$  and hence is already a k-space. As a replacement for Cartesian closure, let's ask: For fixed  $X \in k\mathbf{Top}_*$ , does the functor  $Y \mapsto Y_*^X$  have a left adjoint? This would be an analogue in  $\mathbf{Top}_*$  of the functor  $A \otimes -$  in  $\mathbf{Ab}$ . Compute:

$$k\mathbf{Top}(W, Y^X) = \{f : W \times X \to Y\}$$

$$\cup \cup$$

$$k\mathbf{Top}(W, Y_*^X) = \{f : f(w, *) = * \forall w \in W\}$$

$$\cup \cup$$

$$k\mathbf{Top}_*(W, Y_*^X) = \{f : f(w, *) = * \forall w \in W\}$$

$$= \{f : f(w, *) = * \forall w \in W\}$$

$$f(*, x) = * \forall x \in X\}.$$

So the map  $W \times X \to Y$  corresponding to  $f: W \to Y_*^X$  sends the wedge  $W \vee X \subseteq X \times W$  to the basepoint of Y, and hence factors (uniquely) through the *smash product* 

$$W \wedge X = \frac{W \times X}{W \vee X}$$

obtained by pinching the "axes" in the product to a point. We have an adjoint pair

$$-\wedge X: k\mathbf{Top}_* \rightleftarrows k\mathbf{Top}_*: (-)_*^X.$$

A good way to produce a pointed space is to start with a pair (X, A) (with A a closed subspace of X) and collapse A to a point. Thus

$$k\mathbf{Top}_{*}(X/A, Y) = \{f : X \to Y : f(A) \subseteq \{*\}\}.$$

What if  $A = \emptyset$ ? Then the condition is empty, so

$$k\mathbf{Top}_*(X/\varnothing,Y) = \mathbf{Top}(X,uY)$$
.

where uY is Y with the basepoint forgotten. The solution to this is X with a disjoint basepoint adjoined. Notation:

$$X/\emptyset = X_+$$
.

We have another adjoint pair!

It's often useful to know that if  $A \subseteq X$  and  $B \subseteq Y$  then

$$(X/A) \wedge (Y/B) = \frac{X \times Y}{(A \times Y) \cup_{A \times B} (X \times B)}.$$

For example, if we think of  $I^m/\partial I^m$  as our model of  $S^m$  as a pointed space, we find that

$$S^m \wedge S^n = (I^m/\partial I^m) \wedge (I^n/\partial I^n) = \frac{I^{m+n}}{(\partial I^m \times I^n) \cup (I^m \times \partial I^n)} = I^{m+n}/\partial I^{m+n} = S^{m+n}.$$

Smashing with  $S^1$  is a critically important operation in homotopy theory, known as (reduced) suspension:

$$\Sigma X = S^1 \wedge X = \frac{I \times X}{(\partial I \times X) \cup (I \times *)}.$$

That is, the suspension is obtained from the cylinder by collapsing the top and the bottom to a point, as well as the line segment along a basepoint.

You are invited to check the various properties enjoyed by the smash product, analogous to properties of the tensor product. So it's functorial in both variables; the two-point pointed space serves as a unit; and it is associative and commutative. Associativity is a blessing bestowed by assuming compact generation; notice that in forming it we are mixing limits (the product) with colimits (the quotient by the axes), and indeed the smash product turns out *not* to be associative in the full category of spaces. By induction, the *n*-fold suspension is thus

$$\Sigma^n X = S^1 \wedge \Sigma^{n-1} X = S^1 \wedge (S^{n-1} \wedge X) = (S^1 \wedge S^{n-1}) \wedge X = S^n \wedge X.$$

The smash product and its adjoint render  $k\mathbf{Top}_*$  a "closed symmetric monoidal category."

We can also think about the *loop space* of a pointed space,

$$\Omega X = X_*^{S^1},$$

or the iterated loop space  $\Omega^n X$ , which we claim equals  $X_*^{S^n}$ : by induction,

$$\Omega^{n}X = \Omega(\Omega^{n-1}X) = (X_{*}^{S^{n-1}})_{*}^{S^{1}} = X_{*}^{S^{n-1} \wedge S^{1}} = X_{*}^{S^{n}}.$$

You may be alarmed at the prospect of trying to understand the algebraic topology of a function space like  $\Omega X$ . Perhaps the following theorem of John Milnor will be of some solace.

**Theorem 3.3** (Milnor; see [9]). If X is a pointed countable CW complex, then  $\Omega X$  has the homotopy type of a pointed countable CW complex.

4. FIBER BUNDLES 11

#### The homotopy category

From now on, **Top** will mean k**Top**.

Formation of sets of homotopy classes of maps leads to a new category, the *homotopy category* (of spaces) Ho**Top**. The objects of Ho**Top** are the same as those of **Top**, but the set of morphisms from X to Y is given by [X,Y]. You should check that composition in **Top** descends to composition in Ho**Top**.

Be warned that the homotopy category has rather poor categorical properties. Products and coproducts in **Top** provide products and coproducts in Ho**Top**, but most other types of limits and colimits do not exist in Ho**Top**.

If we have basepoints around, we will naturally want our homotopies to respect them. A "pointed homotopy" between pointed maps is a function  $h: I \times X \to Y$  such that h(t, -) is pointed for all t. This means that it factors through the quotient of  $I \times X$  obtained by pinching  $I \times *$  to a point. This quotient space may be expressed in terms of the smash product:

$$\frac{I \times X}{I \times *} = I_+ \wedge X .$$

Pointed homotopy is again an equivalence relation, and we have the *pointed homotopy category*, or, more properly, the *homotopy category of pointed spaces* Ho $\mathbf{Top}_*$ . We'll write  $[X,Y]_*$  for the set of maps in this category.

**Definition 3.4.** Let (X,\*) be a pointed space and n a positive integer. The nth homotopy group of X is

$$\pi_n(X) = [S^n, X]_*.$$

Note the long list of aliases for this set: for any k with  $0 \le k \le n$ ,

$$\pi_n(X) = [S^n, X]_* = [S^0, \Omega^n X]_* = [S^k, \Omega^{n-k} X]_* = \pi_k(\Omega^{n-k} X).$$

Since  $\pi_1$  group-valued,  $\pi_n(X)$  is indeed a group for any  $n \geq 1$ . These groups look innocuous, but they turn out to hold the solutions to many important geometric problems, and are correspondingly difficult to compute. For example, if a simply connected finite complex is not contractible then infinitely many of its homotopy are nonzero, and only finitely many of them are known.

#### 4 Fiber bundles

Much of this course will revolve around variations on the following concept.

**Definition 4.1.** A fiber bundle is a map  $p: E \to B$ , such that for every  $b \in B$ , there exists an open subset  $U \subseteq B$  containing b and a map  $p^{-1}(U) \to p^{-1}(b)$  such that  $p^{-1}(U) \to U \times p^{-1}(b)$  is a homeomorphism.

When  $p: E \to B$  is a fiber bundle, E is called the *total space*, B the *base space*, and p the *projection*. The point pre-image  $p^{-1}(b) \subseteq$  for  $b \in B$  is the the *fiber over b*. We may use the symbol  $\xi$  for the bundle, and write  $\xi: E \downarrow B$ .

An *isomorphism* from  $p:E\to B$  to  $p':E'\to B$  is a homeomorphism  $f:E\to E'$  such that  $p'\circ f=p$ . The map  $p:E\to B$  is a fiber bundle if it is "locally trivial," i.e. locally (in the base) isomorphic to a "trivial" bundle  $\operatorname{pr}_1:U\times F\to U$ .

Fiber bundles are naturally occurring objects. For instance, a covering space  $E \to B$  is precisely a fiber bundle with discrete fibers.

**Example 4.2.** The "Hopf fibration" provides a beautiful example of a fiber bundle. Let  $S^3 \subset \mathbf{C}^2$  be the unit 3-sphere. Write  $p: S^3 \to \mathbf{C}P^1 \cong S^2$  for the map sending a vector v to the complex line through v and the origin. This is a fiber bundle whose fiber is  $S^1$ .

We said "the fiber" of p is  $S^1$ . It's not hard to see that any two fibers of a fiber bundle over a path connected base space are homeomorphic, so this language isn't too bad. If we envision  $S^3$  as the one-point compactification of  $\mathbb{R}^3$ , we can visualize how the various fibers relate to each other. The fiber through the point at infinity is a line in  $\mathbb{R}^3$ ; imagine it as the z-axis. All the other fibers are circles. It's a great exercise to envision [15] how they fill up Euclidean space.

This map  $S^3 \to S^2$  is the attaching map for the 4-cell in the standard CW structure on  $\mathbb{C}P^2$ . The nontriviality of the cup-square in  $H^*(\mathbb{C}P^2)$  shows that it is *essential*, that is, not null-homotopic. This example is due to Heinz Hopf (1894–1971), a German mathematician working mainly at ETH in Zürich. He discovered the Hopf fibration and its nontriviality during a visit to Princeton in 1927–28. This was the first indication that spheres might have interesting higher homotopy groups.

**Example 4.3.** The Stiefel manifold  $V_k(\mathbb{R}^n)$  is the space of orthogonal "k-frames," that is, ordered k-element orthonormal sets of vectors in  $\mathbb{R}^n$ . Equivalently, it is the space of linear isometric embeddings of  $\mathbb{R}^k$  into  $\mathbb{R}^n$ ; or the set of  $n \times k$  matrices A such that  $AA^T = I_k$ . It is a compact manifold. (Eduard Stiefel (1909–1978) was a Swiss mathematician at ETH Zürich.)

We also have the Grassmannian  $Gr_k(\mathbb{R}^n)$ , the space of k-dimensional vector subspaces of  $\mathbb{R}^n$ . (Hermann Grassmann (1809–1877) discovered much of the theory of linear algebra, but his work was not appreciated during his lifetime. He taught at a Gymnasium in Stettin, Poland, and wrote on linguistics.) By forming the span, we get a map

$$V_k(\mathbb{R}^n) \to \operatorname{Gr}_k(\mathbb{R}^n)$$

generalizing the double cover  $S^{n-1} \to \mathbb{R}P^{n-1}$  (which is the case k=1). There is of course a complex analogue,

$$V_k(\mathbb{C}^n) \to \operatorname{Gr}_k(\mathbb{C}^n)$$

generalizing the Hopf bundle (which is the case n = 2, k = 1).

These maps are fiber bundles (with fiber over V given by the space of ordered orthonormal bases of V). We can regard fact this as a special case of the following general theorem about homogeneous spaces of compact Lie groups (such as O(n), U(n), or a finite group).

**Proposition 4.4.** Let G be a compact Lie group and let  $G \supseteq H \supseteq K$  a sequence of closed subgroups (also then compact Lie groups in their own right). Then the projection map between homogeneous spaces  $G/K \to G/H$  is a fiber bundle.

The orthogonal group O(n) acts on the Stiefel manifold  $V_k(\mathbb{R}^n)$  from the left, by postcomposition. This action is transitive, and the isotropy group of the basepoint is the subgroup  $O(n-k) \times I_k \subseteq O(n)$ . This means that

$$V_k(\mathbb{R}^n) = O(n)/O(n-k) \times I_k$$
,

and we have a fibration  $O(n) \to V_k(\mathbb{R}^n)$  with fiber O(n-k). For example,  $V_1(\mathbb{R}^n)$  is the unit sphere  $S^{n-1}$  in  $\mathbb{R}^n$ , so we have a fibration  $O(n) \to S^{n-1}$  with fiber O(n-1). This will be useful in an analysis of this topological group.

Another interesting map occurs if we forget all but the first vector in a k-frame. This gives us a map  $V_k(\mathbb{R}^n) \to S^{n-1}$ . This is the bundle of tangent (k-1)-frames on the (n-1)-sphere. A deep question asks for which n and k this bundle has a section.

The Grassmannian  $Gr_k(\mathbb{R}^n)$  is obtained by dividing by the larger subgroup  $O(n-k) \times O(k)$ , and Proposition 4.4 implies that the map  $V_k(\mathbb{R}^n) \to Gr_k(\mathbb{R}^n)$  is a fiber bundle.

Proposition 4.4 is a corollary of the following general criterion.

**Theorem 4.5** (Ehresmann, 1951; see [8]). Suppose E and B are smooth manifolds, and let  $p: E \to B$  be a smooth (i.e.,  $C^{\infty}$ ) map. If p is a proper (preimages of compact sets are compact) submersion (that is,  $dp: T_eE \to T_{p(e)}B$  is a surjection for all  $e \in E$ ), then it is a fiber bundle.

Much of this course will consist of a study of fiber bundles such as these through various essentially algebraic lenses. To bring them into play, we will always demand a further condition of our bundles.

**Definition 4.6.** An open cover  $\mathcal{U}$  of a space X is numerable if there exists subordinate partition of unity; i.e., there is a family of functions  $\varphi_U: X \to [0,1] = I$ , indexed by the elements of  $\mathcal{U}$ , such that  $\varphi_U^{-1}((0,1]) = U$  and any  $x \in X$  belongs to only finitely many  $U \in \mathcal{U}$ . The space X is paracompact if any open cover admits a numerable refinement. A fiber bundle is numerable if it admits a numerable trivializing cover.

So any fiber bundle over a paracompact space is numerable. This isn't too restrictive for us:

**Proposition 4.7** (Miyazaki; see Theorem 1.3.5 in [9]). CW-complexes are paracompact.

# 5 Fibrations, fundamental groupoid

#### Fibrations and path liftings

During the 1940s, much effort was devoted to extracting homotopy-theoretic features of fiber bundles. It came to be understood that the desired consequences relied entirely on a "homotopy lifting property." One of the revolutions in topology around 1950 was the realization that it was advantageous to simply take that property as a *definition*. This extension of the notion of a fiber bundle included wonderful new examples, but still retained the homotopy theoretic consequences. Here is the definition.

**Definition 5.1.** A fibration is a map  $p: E \to B$  that satisfies the homotopy lifting property ("HLP"): Given any  $f: W \to E$  and any homotopy  $h: I \times W \to B$  with h(0, w) = pf(w), there is a map  $\overline{h}$  that lifts h and extends f: that is, making the following diagram commute.

$$W \xrightarrow{f} E$$

$$\downarrow_{\text{in}_0} \overline{h} \nearrow \uparrow \downarrow_p$$

$$I \times W \xrightarrow{h} B$$

$$(1.1)$$

For example, for any space X (even the empty space!) the unique map  $X \to *$  is a fibration (A lift is given by  $\overline{h}(t,w) = f(w)$ .) as is the unique map  $\varnothing \to X$  (Why?). In general, though, this seems like an alarming definition, since the HLP has to be checked for all spaces W, all maps f, and all homotopies h!

On the other hand, an advantage of this type of definition, by means of a lifting condition, is that it enjoys various easily checked persistence properties.

• Base change: If  $p: E \to B$  is a fibration and  $X \to B$  is any map, then the induced map  $E \times_B X \to X$  is again a fibration. In particular, any product projection is a fibration.

- Products: If  $p_i: E_i \to B_i$  is a family of fibrations then the product map  $\prod p_i$  is again a fibration.
- Exponentiation: If  $p:E\to B$  is a fibration and A is any space, then  $E^A\to B^A$  is again fibration.
- Composition: If  $p: E \to B$  and  $q: B \to X$  are both fibrations, then the composite  $qp: E \to X$  is again a fibration.

Not all of these persistence properties are true for fiber bundles. Which ones fail?

There is a nice geometric interpretation of what it means for a map to be a fibration, in terms of "path liftings". We'll use Cartesian closure! The adjoint of the solid arrow part of (1.1) is

$$W \xrightarrow{f} E$$

$$\downarrow_{\widehat{h}} \qquad \downarrow_{p}$$

$$B^{I} \xrightarrow{\text{ev}_{0}} B$$

$$(1.2)$$

By the definition of the pullback, the data of this diagram is equivalent to a map  $W \to B^I \times_B E$ . Explicitly,

$$B^I \times_B E = \{(\omega, e) \in B^I \times E : \omega(0) = p(e)\}.$$

This space comes equipped with a map from  $E^I$ , given by sending a path  $\omega: I \to E$  to

$$\widetilde{p}(\omega) = (p\omega, \omega(0)) \in B^I \times_B E$$
.

In these terms, giving a lift  $\overline{h}$  in (1.1) is equivalent to giving a lift

$$W \xrightarrow{\widetilde{h}} B^{I} \times_{B} E$$

This again needs to be checked for every W and every map to  $B^I \times_B E$ . But at least there is now a universal case to consider:  $W = B^I \times_B E$  mapping by the identity map! So p is a fibration if and only if a lift  $\lambda$  exists in the following diagram; that is, a section of  $\widetilde{p}$ :

$$B^{I} \times_{B} E \xrightarrow{1} B^{I} \times_{B} E$$

The section  $\lambda$  is called a path lifting function. To understand why, suppose  $(\omega, e) \in B^I \times_B E$ , so that  $\omega$  is a path in B with  $\omega(0) = p(e)$ . Then  $\lambda(\omega, e)$  is then a path in E lying over  $\omega$  and starting at e. The path lifting function provides a continuous lift of paths in B. The existence (or not) of a section of  $\widetilde{p}$  provides a single condition that needs to be checked if you want to see that p is a fibration.

There is no mention of local triviality in this definition. However:

**Theorem 5.2** (Albrecht Dold, 1963; see [42], Chapter 13). Let  $p: E \to B$  be a continuous map. Assume that there is a numerable cover of B, say  $\mathcal{U}$ , such that for every  $U \in \mathcal{U}$  the restriction  $p|_{p^{-1}(U)}: p^{-1}U \to U$  is a fibration. Then p itself is a fibration.

Corollary 5.3. Any numerable fiber bundle is a fibration.

#### Comparing fibers over different points

If  $p: E \to B$  is a covering space, then unique path lifting provides, for any path  $\omega$  from a to b, a homeomorphism  $F_a \to F_b$  depending only on the path homotopy class of  $\omega$ . Our next goal is to construct an analogous map for a general fibration.

Consider the solid arrow diagram:

$$F_{a} \xrightarrow{p} E$$

$$\downarrow_{\text{in}_{0}} \qquad \downarrow_{p} \qquad \downarrow_{p}$$

$$I \times F_{a} \xrightarrow{\text{pr}_{1}} I \xrightarrow{\omega} B.$$

This commutes since  $\omega(0) = a$ . By the homotopy lifting property, there is a dotted arrow that makes the entire diagram commute. If  $x \in F_a$ , the image h(1,x) is in  $F_b$ . This supplies us with a map  $f: F_a \to F_b$ , given by f(x) = h(1,x).

Since we are not working with a covering space, there will in general be many lifts h and so many choices of f. But we may at least hope that the homotopy class of f is determined by the path homotopy class of  $\omega$ .

So suppose we have two paths  $\omega_0, \omega_1$ , with  $\omega_0(0) = \omega_1(0) = a$  and  $\omega_0(1) = \omega_1(1) = b$ , and a homotopy  $g: I \times I \to B$  between them (so that  $g(0,t) = \omega_0(t)$ ,  $g(1,t) = \omega_1(t)$ , g(s,0) = a, g(s,1) = b). Here's a picture.

Choose lifts  $h_0$  and  $h_1$  as above. These data are captured by a diagram of the form

$$((\partial I \times I) \cup (I \times \{0\})) \times F_a \xrightarrow{\text{in}_0} E \downarrow^p$$

$$I \times I \times F_a \xrightarrow{\text{pr}_1} I \times I \xrightarrow{g} B$$

The map along the top is given by  $h_0$  and  $h_1$  on  $\partial I \times I \times F_a$  and by  $\operatorname{pr}_2 : I \times F_a \to F_a$  followed by the inclusion on the other summand.

If the dotted lift exists, it would restrict on  $I \times \{1\} \times F_a$  to a homotopy between  $f_0$  and  $f_1$ . Well, the subspace  $(\partial I \times I) \cup (I \times \{0\})$  of  $I \times I$  wraps around three edges of the square. It's easy enough to create a homeomorphism with the pair  $(I \times I, \{0\} \times I)$ , so the HLP (with  $W = I \times F_a$ ) gives us the dotted lift.

So the map  $F_a \to F_b$  is well-defined up to homotopy by the path homotopy class of the path  $\omega$  from a to b. Let's denote it by  $f_{\omega}$ .

#### The fundamental groupoid

We can set this up in categorical terms. The space B defines a category whose objects are the points of B and in which a morphism from a to b is a homotopy class of paths from a to b. Composition

is given by the juxtaposition rule

$$(\sigma \cdot \omega)(t) = \begin{cases} \omega(2t) & 0 \le t \le 1/2\\ \sigma(2t-1) & 1/2 \le t \le 1. \end{cases}$$

The constant path  $c_a$  serves as an identity at up to homotopy: here are pictures of the homotopy between  $c_b \cdot \omega$  and  $\omega$ , and between  $\sigma \cdot c_a$  and  $\sigma$ .

Similar pictures show that  $(\alpha \cdot \sigma) \cdot \omega \simeq \alpha \cdot (\sigma \cdot \omega)$  and that every morphism has an inverse, given by  $\overline{\omega}(t) = \omega(1-t).$ 

This gives us a *qroupoid* – a small category in which every morphism is an isomorphism – called the fundamental groupoid of B, and written with a capital  $\pi$ :  $\Pi_1(X)$ .

Our work can be succinctly summarized as follows.

**Proposition 5.4.** Formation of fibers of a fibration  $p: E \to B$  determines a functor  $\Pi_1(B) \to B$ HoTop.

*Proof.* We should check functoriality: if  $\omega:a\sim b$  and  $\sigma:b\sim c$ , then hopefully the induced homotopy classes compose:

$$f_{\sigma\omega} = f_{\sigma} \circ f_{\omega} .$$

To see this, pick lifts  $h_{\omega}$  and  $h_{\sigma}$  in

$$F_{a} \xrightarrow{F} E \qquad F_{b} \xrightarrow{F} E$$

$$\downarrow \inf_{\inf 0} h_{\sigma} \qquad \downarrow$$

$$I \times F_{a} \xrightarrow{\omega} B \qquad I \times F_{b} \xrightarrow{\sigma} B$$

$$F_b \longrightarrow E$$

$$\downarrow^{\ln_0 h_\sigma} \qquad \downarrow$$

$$I \times F_b \stackrel{\sigma}{\longrightarrow} B$$

so that  $f_{\omega}(e) = h_{\omega}(1, e)$  and  $f_{\sigma}(e) = h_{\sigma}(1, e)$ . Then construct a lifting in

$$F_{a} \xrightarrow{F_{a}} E$$

$$\downarrow^{\text{in}_{0}} / \downarrow$$

$$I \times F_{a} \xrightarrow{\sigma \omega} B$$

by using  $h_{\omega}$  in the left half of the interval and  $h_{\sigma} \circ f_{\omega}$  in the right half. The resulting map  $F_a \to F_b$ is then precisely  $f_{\sigma} \circ f_{\omega}$ .

**Remark 5.5.** Last semester we defined the product of loops as juxtaposition but in the reverse order. That convention would have produced a contravariant functor  $\Pi_1(X) \to \text{Ho}\mathbf{Top}$ .

Remark 5.6. Since any functor carries isomorphisms to isomorphisms, Proposition 5.4 implies that a path from a to b determines a homotopy class of homotopy equivalences from  $F_a$  to  $F_b$ .

6. COFIBRATIONS

Fix a map  $p: E \to Y$ . The pullback of E along a map  $f: X \to Y$  can vary wildly as f is deformed; it is far from being a homotopy invariant. Just think of the case X = \*, for example, when the pullback along  $f: * \to Y$  is the point preimage  $p^{-1}(f(*))$ . One of the great features of fibrations is this:

**Proposition 5.7.** Let  $p: E \to Y$  be a fibration and  $f_0, f_1: X \to Y$  two maps. Write  $E_0$  and  $E_1$  for pullbacks of E along  $f_0$  and  $f_1$ . If  $f_0$  and  $f_1$  are homotopic then  $E_0$  and  $E_1$  are homotopy equivalent.

*Proof.* We construct a fibration over  $Y^X$  whose fiber over f is  $f^*E$ , the pullback of  $E \to Y$  along f. It occurs as the middle vertical composite in the following diagram of pullbacks.

The middle horizontal composite is the map f, so the pullback is  $f^*E$  as shown. Now a homotopy between  $f_0$  and  $f_1$  is a path in  $Y^X$  from  $f_0$  to  $f_1$ , and so by Lemma 5.4 the fibers over them are homotopy equivalent.

**Remark 5.8.** We could ask for more: We could ask that  $E_0$  and  $E_1$  are homotopy equivalent by maps and homotopies respecting the projections to X: that there is a *fiber homotopy equivalence* between them. This is in fact the case, as you will show for homework.

**Corollary 5.9.** Let  $p: E \to B$  be a fibration. If B is contractible to  $* \in B$ , then the inclusion of the fiber  $p^{-1}(*) \hookrightarrow E$  is a homotopy equivalence.

*Proof.* The identity map  $1_B$  and the constant map  $c: B \to B$  with value \* are homotopic, so pulling back  $E \downarrow B$  along them produce homotopy equivalent spaces. One gives E, the other  $B \times p^{-1}(*)$ . The projection  $\operatorname{pr}_2: B \times p^{-1}(*) \to p^{-1}(*)$  is a homotopy equivalence since B is contractible. We leave you to check that the resulting equivalence is the inclusion.

#### 6 Cofibrations

Let  $i: A \to X$  be a map of spaces, and Y some other space. When is the induced map  $Y^X \to Y^A$  a fibration? For example, if  $a \in X$ , does evaluation at a produce a fibration  $Y^X \to Y$ ?

By the definition of a fibration, we want a lifting in the solid-arrow diagram

$$W \longrightarrow Y^{X}$$

$$\downarrow_{\text{in}_{0}} \qquad \qquad \downarrow$$

$$I \times W \longrightarrow Y^{A}.$$

Adjointing over, we get:

Adjointing over again, this diagram transforms to:

This discussion motivates the following definition of a cofibration, "dual" to the notion of fibration.

**Definition 6.1.** A cofibration is a map  $i: A \to X$  that satisfies homotopy extension property (sometimes abbreviated as "HEP"): for any solid-arrow commutative diagram as below, a dotted arrow exists making the whole diagram commutative.

How shall we check that a map is a cofibration? By the universal property of a pushout,  $A \to X$  is a cofibration if and only if there is an extension in

$$(X \times 0) \cup_A (A \times I) \xrightarrow{j} X \times I$$

for every map f. Now there is a universal example, namely  $Z = (X \times 0) \cup_A (A \times I)$ , f = id. So a map i is a cofibration if and only if the map  $j: (X \times 0) \cup_A (A \times I) \to X \times I$  admits a retraction: a map  $r: X \times I \to (X \times 0) \cup_A (A \times I)$  such that rj = 1.

The space involved is called the *mapping cylinder*, and written

$$M(i) = (X \times 0) \cup_A (A \times I)$$
.

It's not hard to check (using the mapping cylinder) that any cofibration is a subspace embedding. But the map j may not be an embedding; the map  $(X \times 0) \cup_A (A \times I) \to \operatorname{im}(j) \subseteq X \times I$  is a continuous bijection but it may not be a homeomorphism. If  $A \subseteq X$  is a *closed* subset then  $A \times I \subseteq X \times I$  is

6. COFIBRATIONS

a closed map, and  $X \times 0 \subseteq X \times I$  is also, so the map from the pushout is a closed map and hence is then a homeomorphism to its image.

So the inclusion of a closed subspace  $A \subseteq X$  is a cofibration if and only if there is a retraction from  $X \times I$  onto its subspace  $(X \times 0) \cup (A \times I)$ .

**Definition 6.2.** A basepoint \* in X is nondegenerate if  $\{*\} \hookrightarrow X$  is a closed cofibration. One also says that (X,\*) is well-pointed.

Any point in a CW complex, for example, will serve as a nondegenerate basepoint. If \* is a nondegenerate basepoint of A, the evaluation map  $\operatorname{ev}:X^A\to X$  is a fibration, The fiber of  $\operatorname{ev}$  over the basepoint of X is then exactly the space of pointed maps  $X^A_*$ . Whenever convenient we will assume our basepoints are nondegenerate.

**Example 6.3.**  $i: S^{n-1} \hookrightarrow D^n$  is a cofibration: The map

$$j: D^n \cup_{S^{n-1}} (S^{n-1} \times I) \hookrightarrow D^n \times I$$

is the inclusion of the open tin can into the closed can full of soup –

The illustrated retraction of  $D^n \times I$  onto the open can send a point in the soup to its shadow on the open tin can.

In particular, setting n=1 in this example,  $\{0,1\} \hookrightarrow I$  is a cofibration, so evaluation at the pair of endpoints,

$$\operatorname{ev}_{0,1}: Y^I \to Y \times Y$$
,

is a fibration. Every point in I is nondegenerate, so  $ev_a: Y^I \to Y$  is a fibration for any  $a \in I$ .

The class of cofibrations is closed under the following operations.

- Cobase change: if  $A \to X$  is a cofibration and  $A \to B$  is any map, the pushout  $B \to X \cup_A B$  is again a cofibration.
- Coproducts: if  $A_j \to X_j$  is a cofibration for every j, then the coproduct map  $\coprod A_j \to \coprod X_j$  is again a cofibration.
- Product: If  $A \to X$  is a cofibration and B is any space, then  $A \times B \to X \times B$  is again a cofibration.
- Composition: If  $A \to B$  and  $B \to X$  are both cofibrations, then the composite  $A \to X$  is again a cofibration.

It follows from these inheritance properties and the single example  $S^{n-1} \hookrightarrow D^n$  that if X is a CW complex and A is a subcomplex then  $A \to X$  is a cofibration. CW complexes are Hausdorff spaces, and in any such a case a cofibration is a closed embedding.

Cofibrance provides a natural condition under which a contractible subspace can be collapsed with out damage.

**Proposition 6.4.** Let  $A \to X$  be a cofibration, and write X/A for the pushout of  $* \leftarrow A \to X$ . If A is contractible then  $X \to X/A$  is a homotopy equivalence.

*Proof.* Pick a contracting homotopy  $h: A \times I \to A$ , so that h(a,0) = a and  $h(a,1) = * \in A$  for all  $a \in A$ . By cofibrance there is an extension of  $f \circ h$  to a homotopy  $g: X \times I \to X$  such that g(x,0) = x. g(-,1) then factors through the projection  $p: X \to X/A$ : there is a map  $r: X/A \to X$  such that  $r \circ p$  is homotopic the identity.

To construct a homotopy from  $p \circ r$  to  $1: X/A \to X/A$ , note that the homotopy g sends  $A \times I$  into A, so its composite with  $p: X \to X/A$  factors through a map  $\overline{g}: (X/A) \times I \to X/A$ . At t = 0 this is the identity; at t = 1 it is just  $p \circ r$ .

# 7 Cofibration sequences and co-exactness

There is a pointed version of the cofibration condition: but you only ask to extend *pointed* homotopies; so the condition is weaker than the unpointed version. (It's true that we seek an extension to a *pointed homotopy*, but since the basepoint is in the source space this is automatic.) A pointed homotopy can be thought of as a pointed map

$$X \wedge I_{+} = \frac{X \times I}{* \times I} \to Y$$

The condition that the embedding of a closed subspace  $i: A \subseteq X$  is a pointed cofibration can again be expressed as requiring that the inclusion of the (now "reduced") mapping cylinder

$$M(i) = (X \times 0) \cup_{A \times 0} (A \wedge I_{+})$$

into  $X \wedge I_+$  admits a retraction. Today we'll work entirely in the pointed context, and I'll tend to omit the adjectives "reduced" and "pointed." (Maybe I should have written  $M^u$  for the unpointed variant!)

Any pointed map  $f: X \to Y$  admits a canonical factorization as a closed pointed cofibration followed by a pointed homotopy equivalence:

$$Y \stackrel{f}{\longleftarrow} M(f)$$

where i embeds X along t = 1. For example, the *cone* on a space X is a mapping cylinder:

$$CX = M(X \to *) = X \land I$$
.

The map  $X \to *$  factors as the cofibration  $X \to CX$  followed by the homotopy equivalence  $CX \to *$ .

Since i is a cofibration, we should feel entitled to collapse it to a point; that is, form the pushout in

$$X \longrightarrow *$$

$$\downarrow i \qquad \qquad \downarrow$$

$$Y \stackrel{\simeq}{\longleftarrow} M(f) \longrightarrow C(f)$$

C(f) is the mapping cone of f. If the mapping cylinder is a top hat, the mapping cone is a witch's hat. One example: the suspension functor is given by

$$\Sigma X = C(X \to *)$$
.

Since i is a cofibration, the pushout  $* \to C(f)$  is again a cofibration; the cone point is always nondegenerate.

This pushout can be expressed differently: Instead of replacing  $f: X \to Y$  with a cofibration, let's replace  $X \to *$  with a cofibration, namely, the inclusion  $X \hookrightarrow CX$ . So we have a pushout diagram

$$X \xrightarrow{\text{in}_1} CX$$

$$\downarrow^f \qquad \qquad \downarrow$$

$$Y \xrightarrow{i(f)} C(f).$$

This pushout is homeomorphic to the earlier one; but notice that the homeomorphism uses the automorphism of the unit interval sending t to 1-t.

If f is already a cofibration, the cobase change property implies that  $CX \to C(f)$  is again cofibration. CX is contractible, so by Proposition 6.4, collapsing it to a point is a homotopy equivalence. But collapsing CX in C(f) is the same as collapsing Y in X:

**Lemma 7.1.** If  $f: X \to Y$  is a cofibration then the collapse map  $C(f) \to Y/X$  is a homotopy equivalence.

#### Co-exactness

**Definition 7.2.** A cofibration sequence is a diagram that that is homotopy equivalent to

$$X \xrightarrow{f} Y \xrightarrow{i(f)} C(f)$$

for some map f.

The composite  $X \to C(f)$  is *null-homotopic*; that is, it's homotopic to the constant map (with value the basepoint). The homotopy is given by  $h: (x,t) \mapsto [x,t]$ : When t=0 we can use  $[x,0] \sim f(x)$  to see the composite, while when t=1 we get the constant map.

The pair (i(f), h) is universal with this property: giving a map  $g: Y \to Z$  along with a null-homotopy of the composite  $g \circ f$  is the same thing as giving a map  $C(f) \to Z$  that extends g.

An implication of this is the following:

**Lemma 7.3.** For any pointed map  $f: X \to Y$  and any pointed space Z, the sequence of pointed sets

$$[X,Z]_* \stackrel{f^*}{\longleftarrow} [Y,Z]_* \stackrel{i(f)^*}{\longleftarrow} [C(f),Z]_*$$

is exact, in the sense that

$$\operatorname{im}(i(f)^*) = \{g : Y \to Z : g \circ f \simeq *\}.$$

Any sequence of composable arrows with this property is "co-exact': so cofibration sequences are coexact.

The map  $f: X \to Y$  functorially determines the map  $i(f): Y \to C(f)$ , and we may form its mapping cone, and continue:

$$X \xrightarrow{f} Y \xrightarrow{i(f)} C(f) \xrightarrow{i^2(f)} C(i(f)) \xrightarrow{i^3(f)} C(i^2(f)) \xrightarrow{i^4(f)} \cdots$$

This looks like it will lead off into the wilderness, but luckily there is a kind of periodicity at work. Here's a picture of C(i(f)):

The map i(f) is the pushout of the cofibration  $X \to CX$  along  $X \to Y$ , so it is a cofibration. Therefore, by Lemma 7.1 the collapse map  $C(i(f)) \to C(f)/Y$  is a homotopy equivalence. But

$$C(f)/Y = \Sigma X$$
,

the suspension of X. So we have the commutative diagram

$$X \xrightarrow{f} Y \xrightarrow{i(f)} C(f) \xrightarrow{i^2(f)} C(i(f))$$

$$\uparrow^{\pi(f)} \downarrow \simeq$$

$$\Sigma X.$$

Now we have two ways to continue! I combine them in the homotopy commutative diagram

$$X \xrightarrow{f} Y \xrightarrow{i(f)} C(f) \xrightarrow{i^{2}(f)} C(i(f)) \xrightarrow{i^{3}(f)} C(i^{2}(f)) \xrightarrow{i^{4}(f)} \cdots$$

$$\uparrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \uparrow \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

Notice the minus sign! It means that instead of  $[t,x] \mapsto [t,f(x)]$ , we have to use  $[t,x] \mapsto [1-t,f(x)]$ . This is needed to make the triangle commute, even up to homotopy, as you can see by being careful with the parametrization of the cones.

The resulting long sequence of maps

$$X \to Y \to C(f) \to \Sigma X \to \Sigma Y \to \Sigma C(f) \to \Sigma^2 X \to \cdots$$

is the Barratt-Puppe sequence associated to the map f. Each two-term subsequence is a cofiber sequence and is co-exact.

The Barratt-Puppe sequence is a "homotopy theoretic" version of the long exact homology sequence of a pair. Suppose that A is a subspace of X. Then I claim that

$$\overline{H}_*(X \cup CA) \cong H_*(X, A)$$

If you combine that with the suspension isomorphism in reduced homology, the Barratt-Puppe sequence gives you the homology long exact sequence of the pair.

To see the equality, just use homotopy invariance and excision:

$$\overline{H}_*(X \cup CA) = H_*(X \cup CA, *) = H_*(X \cup CA, CA)$$

$$= H_*(X \cup C_{<(1/2)}A, C_{<(1/2)}A) = H_*(X \cup A \times I, A \times I) = H_*(X, A).$$

Since  $X \cup CA \simeq X/A$  if  $A \to X$  is a cofibration, this is a good condition to guarantee that

$$H_*(X,A) = \overline{H}_*(X/A)$$
.

# 8 Weak equivalences and Whitehead's Theorems

We now have defined the homotopy groups of a pointed space,

$$\pi_n(X) = [S^n, X]_*.$$

So  $\pi_0(X)$  is the pointed set of path components. For n > 0,  $\pi_n$  only sees the path component of the basepoint. It's a group for n = 1, and hence also for  $n \ge 1$  since  $\pi_n(X) = \pi_1(\Omega^{n-1})$ .

Here's another very useful way to represent an element of  $\pi_n(X,*)$ . Recall our description of the *n*-sphere as a pointed space:

$$S^n = I^n/\partial I^n$$
.

So an element of  $\pi_n(X,*)$  is a homotopy class of maps of pairs

$$(I^n, \partial I^n) \to (X, *)$$
.

**Lemma 8.1.** For  $n \geq 2$ ,  $\pi_n(X)$  is abelian.

Proof. I'll give you two proofs of this fact. Since  $\pi_n(X) = \pi_2(\Omega^{n-2}X)$ , it suffices to consider n=2. First, geometric: Given  $f,g:I^2\to X$ , both sending  $\partial I^2$  to \*, we can form another one by putting the two side by side (and compressing the horizontal coordinate by a factor of 2 in each). This is the sum in  $\pi_n(X)$ . This is homotopic to the map that does f and g in much smaller rectangles and fills in the rest of the square with maps to the basepoint. Now I'm free to move these two smaller rectangles around one another, exchanging positions. Then I can re-expand, to get the addition g+f.

Now, algebraic: An *H-space* is a pointed space Y together with map  $\mu: Y \times Y \to Y$  such that

$$Y \xrightarrow{\text{in}_1} Y \times Y \xrightarrow{\text{in}_2} Y$$

$$\downarrow \mu \qquad \downarrow \mu \qquad \downarrow \chi$$

commutes in Ho(**Top**<sub>\*</sub>). The relevant example here is  $Y = \Omega X$ . Then  $\pi_1(Y, *)$  has extra structure: Since  $\pi_1(Y \times Y, *) = \pi_1(Y, *) \times \pi_1(Y, *)$  (as groups) we get a group G together with a group homomorphism  $\mu: G \times G \to G$  such that

$$G \xrightarrow{\operatorname{in}_1} G \times G \xleftarrow{\operatorname{in}_2} G$$

$$\downarrow^{\mu} \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$

commutes. That is to say,  $\mu(a,1) = a$ ,  $\mu(1,d) = d$ , and, since  $(a,b) \cdot (c,d) = (ac,bd)$  in  $G \times G$ ,

$$\mu(ac,bd) = \mu(a,b) \cdot \mu(c,d)$$
.

Take b=1=c so  $\mu(a,d)=ad$ : that is, the "multiplication"  $\mu$  is none other than the group multiplication. Then take a=1=d so  $\mu(c,b)=bc$ : that is, the group structure is commutative.  $\square$ 

We can trace what happens when we move the basepoint. Let  $\omega: I \to X$  be a path from a to b. It induces a map

$$\omega_{\#}:\pi_n(X,a)\to\pi_n(X,b)$$

in the following way. Given  $f: I^n \to X$  representing  $\alpha \in \pi_n(X, *)$ , define a map

$$(I^n \times 0) \cup (\partial I^n \times I) \to X$$

by

$$(v,t) \mapsto \begin{cases} f(v) & \text{for } v \in I^n, t = 0\\ \omega(t) & \text{for } v \in \partial I^n. \end{cases}$$

Precompose this map with the map from the face  $I^n \times 1$  given by projecting from the point (b, 2), where b is the center of  $I^n$ . The result is a new map  $I^n \to X$ ; it sends the middle part of the cube by f, and the peripheral part by  $\omega$ .

It's easy to check that this gives rise to a functor  $\Pi_1(X) \to \mathbf{Set}$ , and hence to an action of  $\pi_1(X,*)$  on  $\pi_n(X,*)$ . For n=1, this is the conjugation action,

$$\omega \cdot \alpha = \omega \alpha \omega^{-1}$$
.

For all  $n \ge 1$  it is an action by group homomorphisms; for  $n \ge 2$ ,  $\pi_n(X, *)$  is a  $\mathbb{Z}[\pi_1(X, *)]$ -module.

**Definition 8.2.** A space is *simple* if this action is trivial for every choice of basepoint.

**Example 8.3.** If all path components are simply connected, the space is simple. A topological group is a simple space.

This action can be used to explain how homotopic maps act on homotopy groups.

**Proposition 8.4.** Let  $h: f_0 \sim f_1$  be a ("free," as opposed to pointed) homotopy of maps  $X \to Y$ . Let  $* \in X$ , and let  $\omega: I \to X$  by  $\omega(t) = h(*, t)$ . Then

commutes.

*Proof.* The homotopy h fills in the cube  $I^n \times I$ , and provides a pointed homotopy from  $\omega \cdot f_0$  to  $f_1$ .

While it may be hard to compute homotopy groups, we can think about what sort of maps induce isomorphisms in them.

**Definition 8.5.** A map  $f: X \to Y$  is a *weak equivalence* if it induces an isomorphism in  $\pi_0$  and in  $\pi_n$  for all  $n \ge 1$  and every choice of basepoint in X.

Of course it suffices to pick one point in each path component.

Weak equivalences may not have any kind of map going in the opposite direction. The definition seems very base-point focused, but in fact it is not. For example,

**Proposition 8.6.** Any homotopy equivalence is a weak equivalence.

*Proof.* Let  $f: X \to Y$  be a homotopy equivalence with homotopy inverse  $g: Y \to X$ , and pick a homotopy  $h: 1_X \sim gf$ . Define  $\omega: I \to X$  by  $\omega(t) = h(*,t)$ . Then by Proposition 8.4 we have a commutative diagram

$$\pi_n(X, *) \xrightarrow{f_*} \pi_n(Y, f(*))$$

$$\downarrow^{g_*}$$

$$\pi_n(X; gf(*))$$

in which the diagonal is an isomorphism. Picking a homotopy  $1 \sim fg$  gives the rest of the diagram

$$\pi_n(X,*) \xrightarrow{f_*} \pi_n(Y,f(*))$$

$$\cong \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$

It follows that  $g_*$  is an isomorphism, and therefore  $f_*$  is also.

Here are three fundamental theorems about weak equivalences, all due more or less to J.H.C. Whitehead. (John Henry Constantine Whitehead (fl. 1930–1961, Oxford) was a pioneer in the development of homotopy theory, inventor i.a. of CW complexes.)

**Theorem 8.7.** Any weak equivalence induces an isomorphism in singular homology.

Since  $H_0(X)$  is the free abelian group generated by  $\pi_0(X)$ , this is obvious in dimension 0, and on each path component Poincaré's theorem implies it in dimension 1.

**Theorem 8.8.** Let X and Y be simple spaces. Any map from X to Y that induces an isomorphism in homology is a weak equivalence.

**Theorem 8.9.** Let X and Y be CW complexes. Any weak equivalence from X to Y is in fact a homotopy equivalence.

Theorem 8.8 clearly provides a powerful way to construct weak equivalences, and, when combined with Theorem 8.9, homotopy equivalences. We will prove a vast generalization of Theorem 8.8 later in the course.

Here is a useful strengthening of Theorem 8.9:

**Theorem 8.10** ("Whitehead's little theorem"). A map  $f: X \to Y$  is a weak equivalence if and only if  $f \circ -: [W, X] \to [W, Y]$  is bijective for all CW complexes W.

Proof of  $8.10 \Rightarrow 8.9$ . We assume that

$$f \circ -: [K, X] \to [K, Y]$$

is bijective for every CW complex K. Taking K = Y, we find that there is a map  $g: Y \to X$  such that  $f \circ g = 1_Y$ . We claim that  $g \circ f = 1_X$  as well. To see this we take K = X: so

$$f \circ -: [X, X] \to [X, Y]$$

is a monomorphism. Under it  $1 \mapsto f$ , but  $g \circ f$  does as well:

$$g \circ f \mapsto f \circ (g \circ f) = (f \circ g) \circ f = 1_Y \circ g = f$$
.

So 
$$g \circ f = 1_X$$
.

Remark 8.11. There is a deep shift of focus involved here. In the beginning, homotopy theory dealt with what happens when you define an equivalence relation ("homotopy") on maps. Focusing on weak equivalences is an entirely different perspective: we are picking out a collection of maps that will be regarded as "equivalences." They are to become the isomorphism in the homotopy category. The fact that they satisfy 2-out-of-3 makes the collection of weak equivalences an appropriate choice.

This change in perspective may be attributed to Daniel Quillen, who, in *Homotopical Algebra* (written while Quillen was a professor at MIT, in collaboration with his colleague Dan Kan), set out an axiomatization of homotopy theory using three classes of maps, which he termed "weak equivalences," "cofibrations," and "fibrations." They are assumed to be related to each other through appropriate factorization and lifting properties. The resulting theory of "model categories" dominated the underlying framework of homotopy theory for thirty years, and is still a critically important tool.

# 9 Homotopy long exact sequence and homotopy fibers

#### Relative homotopy groups

We'll continue to think of  $\pi_n(X,*)$  as a set of homotopy classes of maps of pairs:

$$\pi_n(X,*) = [(I^n, \partial I^n), (X,*)].$$

As usual in algebraic topology, there is much to be gained from establishing a "relative" version. We will use the sequence of subspaces

$$I^n \supset \partial I^n \supset \partial I^{n-1} \times I \cup I^{n-1} \times 0$$

in this definition. We will write  $J_n$  for the last subspace, so for example  $J_1 = \{0\} \subset I$ . In general it's an "open box":

**Definition 9.1.** Let (X, A, \*) be a pointed pair. For  $n \geq 1$ , define a pointed set

$$\pi_n(X, A, *) = [(I^n, \partial I^n, J_n), (X, A, *)].$$

This definition is set up in such a way that

$$\pi_n(X, \{*\}, *) = \pi_n(X, *)$$

so that the inclusion  $\{*\} \hookrightarrow A$  induces a map

$$\pi_n(X,*) \to \pi_n(X,A,*)$$
.

Also, restricting to the "back face"  $I^{n-1} \times 0$  provides a map

$$\partial: \pi_n(X, A, *) \to \pi_{n-1}(A, *)$$

and the composite of these two is obviously "trivial," meaning that its image is the basepoint  $* \in \pi_{n-1}(A, *)$ . We get a sequence of pointed sets

$$\pi_{2}(A, *) \xrightarrow{\partial} \pi_{3}(X, A, *)$$

$$\pi_{2}(A, *) \xrightarrow{\partial} \pi_{2}(X, A, *)$$

$$\pi_{1}(A, *) \xrightarrow{\partial} \pi_{1}(X, *) \xrightarrow{\partial} \pi_{1}(A, X, *)$$

$$\pi_{0}(A, *) \xrightarrow{\partial} \pi_{0}(X, *)$$

We claim that this is an exact sequence of pointed sets: the long exact homotopy sequence of a pair. For example, an element of  $\pi_1(X, A, *)$  is represented by a path starting at the basepoint and ending in A. Its boundary is the component of that point in A. Saying that the component of  $a \in A$  maps to the base point component of X is exactly saying that  $[a] \in \pi_0(A)$  is in the image of  $\partial: \pi_1(X, A, *) \to \pi_0(A, *)$ .

We will investigate the structure of these relative homotopy groups, and explain why the sequence is exact, by developing an analogue of the Barratt-Puppe sequence that will turn out to give rise to the homotopy long exact sequence of a pair.

#### Fiber sequences

In the pointed category, we could redefine "fibration" slightly (as is done in [21], for example) so that  $p: E \to B$  is a fibration if every pointed solid arrow diagram

$$W \longrightarrow E$$

$$\downarrow_{\text{in}_0} \nearrow \downarrow_p$$

$$I_+ \land W \longrightarrow B$$

admits a lift. There are fewer diagrams, but more is demanded of the lift.

Instead we'll leave the fibrations as they are, but in compensation insist that our basepoints should be nondegenerate. Lifting is then contained in the following lemma. See [40] for the proof, which we forgo, preferring to give the proof of similar result 10.4 later.

**Lemma 9.2** (Relative homotopy lifting property). Let  $A \subseteq X$  be a closed cofibration and  $E \to B$  a fibration. Then a lifting exists in any solid arrow diagram

$$(X \times 0) \cup (A \times I) \xrightarrow{F} E$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$X \times I \xrightarrow{F} B.$$

Exactly the same proof we did before shows that if  $A \to B$  is a pointed cofibration and the basepoints are nondegenerate then  $X_*^B \to X_*^A$  is a fibration. For example we can take  $(B,A,*) = (I,\partial I,0)$  to see that the map from the path space

$$P(X) = X_*^I = \{\omega : I \to X : \omega(0) = *\}$$

to X by evaluation at 1 is a fibration.

Taking A to be a singleton in Lemma 9.2:

**Corollary 9.3.** Let  $p: E \to B$  be a fibration and suppose given  $f: W \to E$  and  $g: W \to B$  such that  $pf \simeq g$ : so g is a lift of f up to homotopy. Then f is homotopic to a lift "on the nose," that is, a function  $\overline{f}: W \to E$  such that  $p\overline{f} = g$ .

So if  $g:W\to B$  is such that  $pg\simeq *$ , then g is homotopic to a map that lands in the fiber  $p^{-1}(*)=F$  of p over \*. This shows that the sequence – the "fiber sequence" – of pointed spaces

$$F \to E \to B$$

is "exact," in the sense that for any well-pointed space W the sequence

$$[W, F]_* \to [W, E]_* \to [W, B]_*$$

is exact.

Not every map is a fibration, but every map factors as

$$X \xrightarrow{\simeq} T(f) = \{(x,\omega) \in X \times Y^I : \omega(1) = f(x)\}$$

where  $X \to T(f)$  is a homotopy equivalence and p is a fibration.

The fiber of p is the homotopy fiber of f, written F(f):

$$F(f) = \{(x, \omega) \in X \times Y_*^I : \omega(1) = f(x)\}.$$

Here we take  $0 \in I$  as the basepoint, so  $\omega$  is a path in Y from \* to f(x).

As in our discussion of the Barratt-Puppe cofibration sequence, there is an equivalent way of constructing F(f), by replacing  $* \to Y$  with a fibration, namely the path space  $Y_*^I$ , and forming the pullback over X:

$$F(f) \longrightarrow P(Y) = Y_*^I$$

$$\downarrow \qquad \qquad \downarrow$$

$$X \longrightarrow Y$$

**Lemma 9.4.** Let  $p: E \to B$  be a fibration and  $* \in B$ . The natural map  $p^{-1}(*) \to F(p)$  is a homotopy equivalence.

*Proof.* Regard F(p) as the pullback of p along  $PB \downarrow B$ . The induced map on fibers is a homeomorphism; but PB is contractible so the inclusion of the fiber of  $F(p) \downarrow PB$  into F(p) is a homotopy equivalence, by Corollary 5.9.

Continuing with the analogy with cofibrations, the map  $p(f): F(f) \to X$  is a fibration, with fiber  $\Omega X$ , and we have the Barratt-Puppe fibration sequence

$$Y \stackrel{f}{\leftarrow} X \stackrel{p}{\leftarrow} F(f) \stackrel{i}{\leftarrow} \Omega Y \stackrel{\Omega f}{\leftarrow} \Omega X \stackrel{\Omega p}{\leftarrow} \Omega F(f) \stackrel{\Omega i}{\leftarrow} \cdots$$

that is exact. It gives rise to the long exact homotopy sequence:

**Lemma 9.5.** Let (X, A, \*) be a pointed pair, and let F denote the homotopy fiber of the inclusion  $A \to X$ . For each  $n \ge 1$  there is a natural isomorphism

$$\pi_n(X,A) \xrightarrow{\cong} \pi_{n-1}(F,*)$$

such that

commutes.

Corollary 9.6. The sequence homotopy long exact sequence of a pair is in fact exact; for  $n \ge 2$  the set  $\pi_n(X, A, *)$  is a group, abelian for  $n \ge 3$ ; and all the maps between groups in the sequence are homomorphisms.

Furthermore the bottom sequence makes sense (and is exact) even if  $A \to X$  is not a subspace inclusion.

Proof of Lemma 9.5. To begin with, notice that  $\pi_1(X, A, *)$  is the set of path components of the space of maps

$$(I, \partial I, J_1) \to (X, A, *)$$
.

This is the space of paths in X from \* to some element of a: that is, it's precisely  $F(A \to X)$ . In fact, for any  $n \ge 1$ , the space of maps

$$(I^n, \partial I^n, J_n) \to (X, A, *)$$

is precisely  $\Omega^{n-1}F(A\to X)$ . For example, when n=2, an element in the given space is given by a map  $I^2\to X$  that is the basepoint along the bottom and takes values in A along the top – so a path in  $F(A\to X)$  – and also is the basepoint along the left and right edges – so it's a loop in  $F(A\to X)$ .

The diagram is easily seen to commute.

There is another perspective on the homotopy long exact sequence, arising from Lemma 9.4.

**Lemma 9.7.** Let  $p: E \to B$  be a fibration and  $* \in E$ . Write \* also for the image of \* in B, and let F be the fiber over \*. Then

$$p_*: \pi_*(E, F, *) \to \pi_*(B, *)$$

is an isomorphism.

*Proof.*  $F(p) \to E$  is a fibration, so by Proposition 5.7 and Lemma 9.4,

$$hofib(F \to E) \cong hofib(F(p) \to E) \cong fib(F(p) \to E) = \Omega B$$
.

We leave to you the check that the resulting composite isomorphism

$$\pi_n(E,F) \to \pi_{n-1}(\mathrm{hofib}(F \to E)) \to \pi_{n-1}(\Omega B) \to \pi_n(B)$$

is indeed the map induced by  $p_*$ .

We saw that  $\pi_1(A,*)$  acts on  $\pi_n(A,*)$ . The map  $\pi_n(A,*) \to \pi_n(X,*)$  is equivariant, if we let  $\pi_1(A,*)$  act on  $\pi_n(X,*)$  via the group homomorphism  $\pi_1(A,*) \to \pi_1(X,*)$ . The group  $\pi_1(A,*)$  also acts on  $\pi_n(X,A,*)$ , compatibly.

It's clear from the picture that the maps in the homotopy long exact sequence are equivariant.

# Chapter 2

# The homotopy theory of CW complexes

# 10 Serre fibrations and relative lifting

#### Relative CW complexes

We will do many proofs by induction over cells in a CW complex. We might as well base the induction arbitrarily. This suggests the following definition.

**Definition 10.1.** A relative CW-complex is a pair (X, A) together with a filtration

$$A = X_{-1} \subseteq X_0 \subseteq X_1 \subseteq \cdots \subseteq X$$
,

such that (1) for all n the space  $X_n$  sits in a pushout square:

$$\coprod_{\alpha \in \Sigma_n} S_{\alpha}^{n-1} \longrightarrow \coprod_{\alpha \in \Sigma_n} D_{\alpha}^n \\
\downarrow \qquad \qquad \downarrow \\
X_{n-1} \longrightarrow X_n,$$

and (2)  $X = \underline{\lim} X_n$  topologically.

The maps  $S^{n-1} \to X_{n-1}$  are "attaching maps" and the maps  $D^n \to X_n$  are "characteristic maps." If  $A = \emptyset$ , this is just the definition of a CW-complex. Often X will be a CW-complex and A a subcomplex.

#### Serre fibrations

If we're going to restrict our attenton to CW complexes, we might as well weaken the lifting condition defining fibrations.

**Definition 10.2.** A map  $p: E \to B$  is a *Serre fibration* if it has the homotopy lifting property ("HLP") with respect to all CW complexes. That is, for every CW complex X and every solid arrow diagram

$$X \xrightarrow{\longrightarrow} E$$

$$\downarrow_{\text{in}_0} \nearrow \qquad \downarrow_p$$

$$X \times I \longrightarrow B$$

there is a lift as indicated.

For contrast, what we called a fibration is also known as a *Hurewicz fibration*. (Witold Hurewicz was a faculty member at MIT from 1945 till his death in 1958 from a fall from the top of the Uxmal Pyramid in Mexico.)

Clearly things like the homotopy long exact sequence of a fibration extend to the context of Serre fibrations. So for example:

**Lemma 10.3.** Suppose that  $p: E \to B$  is both a Serre fibration and a weak equivalence. Then each fiber is weakly contractible; i.e. the map to \* is a weak equivalence.

Proof. Since  $\pi_0(E) \to \pi_0(B)$  is bijective, we may assume that both E and B are path connected. The long exact homotopy sequence shows that  $\partial : \pi_1(B) \to \pi_0(F)$  is surjective with kernel given by the image of the surjection  $\pi_1(E) \to \pi_1(B)$ : so  $\pi_0(F) = *$ . Moving up the sequence then shows that all the higher homotopy groups of F are also trivial.

No new ideas are required to prove the following two facts.

**Proposition 10.4.** Let  $p: E \to B$ . The following are equivalent.

- 1. p is a Serre fibration.
- 2. p has HLP with respect to  $D^n$  for all  $n \geq 0$ .
- 3. p has relative HLP with respect to  $S^{n-1} \hookrightarrow D^n$  for all n > 0.
- 4. p has relative HLP with respect to  $A \hookrightarrow X$  for all relative CW complexes (X, A).

**Proposition 10.5** (Relative straightening). Assume that (X, A) is a relative CW complex and that  $p: E \to B$  is a Serre fibration, and that the diagram

$$\begin{array}{ccc}
A \longrightarrow E \\
\downarrow j & \downarrow p \\
X \longrightarrow B
\end{array}$$

commutes. If g is homotopic to a map g' still making the diagram commute and for which there is a filler, then there is a filler for g.

#### Proof of "Whitehead's little theorem"

We are moving towards a proof of this theorem of J.H.C. Whitehead.

**Theorem 10.6.** Let  $f: X \to Y$  be a weak equivalence and W any CW complex. The induced map  $[W, X] \to [W, Y]$  is bijective.

The key fact is this:

**Proposition 10.7.** Suppose that  $j: A \hookrightarrow X$  is a relative CW complex and  $p: E \to B$  is both a Serre fibration and a weak equivalence. Then a filler exists in any diagram

$$\begin{array}{ccc}
A \longrightarrow E \\
\downarrow j & \uparrow & \downarrow p \\
X \longrightarrow B.
\end{array}$$

In the language of Quillen's  $Homotopical\ Algebra$ , this says that j satisfies the left lifting property with respect to "acyclic" Serre fibrations, and acyclic Serre fibrations satisfy the right lifting property with respect to relative CW complex inclusions.

*Proof (following [29]).* The proof will of course go by induction. The inductive step is this: Assuming that  $p: E \to B$  is a Serre fibration and a weak equivalence, any diagram

$$S^{n-1} \xrightarrow{} E$$

$$\downarrow^j \qquad \downarrow^p$$

$$D^n \xrightarrow{} B$$

admits a filler.

First let's think about the special case in which B=\*. This is true because for any path connected space X the evident surjection

$$\pi_n(X,*) \to [S^n,X]$$

is none other than the orbit projection associated to the action of  $\pi_1(X, *)$  on  $\pi_n(X, *)$ . This fact is why I wanted to focus on this otherwise rather obscure action. You'll verify it for homework.

For the general case, we begin by using Lemma 10.5 replacing the map g by a homotopic map g' with properties that will let us construct a filler. To define g', let  $\varphi: D^n \to D^n$  by

$$\varphi: v \mapsto \begin{cases} 0 & \text{if } |v| \le 1/2\\ (2|v|-1)v & \text{if } |v| \ge 1/2. \end{cases}$$

This map is homotopic to the identity (by a piecewise linear homotopy that fixes  $S^{n-1}$ ), so  $g' = g \circ \varphi \simeq g$ .

The virtue of g' is that we can treat the two parts of  $D^n$  separately. The annulus  $\{v \in D^n : |v| \ge 1/2\}$  is homeomorphic to  $I \times S^{n-1}$ , so a lifting exists on it since p is a Serre fibration. On the other hand g' is constant on the inner disk  $D^n_{1/2}$ , with value g(0). We just constructed a lift on  $S^{n-1}_{1/2}$ , but it actually lands in the fiber of p over g(0). We can fill in that map with a map  $D^n_{1/2} \to p^{-1}(g(0))$  since the fiber is weakly contractible.

Proof of Theorem 10.6. Begin by factoring  $f: X \to Y$  as a homotopy equivalence followed by a fibration; so as a weak equivalence followed by a Serre fibration p. Weak equivalences satisfy "2 out of 3" (as you'll check for homework), so p is again a weak equivalence. Thus we may assume that f is a Serre fibration (as well as being a weak equivalence).

To see that the map is onto, apply Proposition 10.7 to

To see that the map is one-to-one, apply Proposition 10.7 to

$$W \times \partial I \longrightarrow X$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$

This style of proof – using lifting conditions and factorizations – is very much in the spirit of Daniel Quillen's formalization of homotopy theory in his development of "model categories."

# 11 Connectivity and approximation

#### The language of connectivity

An analysis of the proof of "Whitehead's little theorem" shows that if the CW complex we are using as a source has dimension at most n, then we only needed to know that the map  $X \to Y$  was an "n-equivalence" in the following sense.

**Definition 11.1.** Let n be a positive integer. A map  $f: X \to Y$  is an n-equivalence provided that  $f_*: \pi_0(X) \to \pi_0(Y)$  is an isomorphism, and for every choice of basepoint  $a \in X$  the map  $f_*: \pi_q(X, a) \to \pi_q(Y, f(a))$  is an isomorphism for q < n and an epimorphism for q = n. It is a 0-equivalence if  $f_*: \pi_0(X) \to \pi_0(Y)$  is an epimorphism.

So a map is a weak equivalence if it is an n-equivalence for all n. We restate:

**Theorem 11.2.** Let n be a nonnegative integer and W a CW complex. If  $f: X \to Y$  is an n-equivalence then the map  $f_*: [W, X] \to [W, Y]$  is bijective if dim W < n and surjective if dim W = n.

The odd edge condition in the definition of n-equivalence might be made more palatable by noticing that the long exact homotopy sequence shows that (for n > 0) f is an n-equivalence if and only if  $\pi_0(X) \to \pi_0(Y)$  is bijective and for any  $b \in Y$  the group  $\pi_q(F(f, b))$  is trivial for q < n.

This suggests some further language.

**Definition 11.3.** Let n be a positive integer. A space X is n-connected if it is path connected and for any choice of basepoint a the set  $\pi_q(X, a)$  is trivial for all  $q \leq n$ . A space X is 0-connected if it is path connected.

So "1-connected" and "simply connected" are synonymous. The homotopy long exact sequence shows that for n > 0 a map  $X \to Y$  is an *n*-equivalence if it is bijective on connected components and for every  $b \in Y$  the homotopy fiber F(f, b) is *n*-connected.

The language of connectivity extends to pairs:

**Definition 11.4.** Let n be a non-negative integer. A pair (X, A) is n-connected if  $\pi_0(A) \to \pi_0(X)$  is surjective and for every basepoint  $a \in A$  the set  $\pi_q(X, A, a)$  is trivial for  $q \leq n$ .

That is, (X, A) is n-connected if the inclusion map  $A \to X$  is an n-equivalence.

#### Skeletal approximation

**Theorem 11.5** (The skeletal approximation theorem). Let (X, A) and (Y, B) be relative CW complexes. Any map  $f:(X, A) \to (Y, B)$  is homotopic rel A to a skeletal map – a map sending  $X_n$  into  $Y_n$  for all n. Any homotopy between skeletal maps can be deformed rel A to one sending  $X_n$  into  $Y_{n+1}$  for all n.

I will not give a proof of this theorem. You have to inductively push maps off of cells, using smooth or simplicial approximation techniques. I am following Norman Steenrod in calling such a map "skeletal" rather than the more common "cellular," since it is after all not required to send cells to cells. See for example [4, p. 208]

**Corollary 11.6.** Any map  $X \to Y$  of CW complexes is homotopic to a skeletal map, and any homotopy between skeletal maps can be deformed to one sending  $X_n$  to  $Y_{n+1}$ .

For example, the *n*-sphere  $I^n/\partial I^n$  has a CW structure in which  $\operatorname{Sk}_{n-1}S^n = *$  and  $\operatorname{Sk}_nS^n = S^n$ . The characteristic map is given by a choice of homeomorphism  $D^n \to I^n$ . So if q < n, then any map  $S^q \to S^n$  factors through the basepoint up to homotopy. This shows that

$$\pi_q(S^n) = 0$$
 for  $q < n$ 

– the *n*-sphere is (n-1)-connected. So also is any CW complex with one 0-cell and no other *q*-cells for q < n.

As a special case (one used in proving the theorem in fact):

**Proposition 11.7.** Let (X, A) be a relative CW complex in which all the cells of X are in dimension greater than n. Then (X, A) is n-connected.

For example (with  $A = \emptyset$ )  $\pi_0(X_0) \to \pi_0(X)$  is surjective: every path component of X contains a vertex. And  $\pi_1(X_1) \to \pi_1(X)$  is surjective: any path between vertices can be deformed onto the 1-skeleton. Moreover, any homotopy between paths in the 1-skeleton can be deformed to lie in the 2-skeleton;  $\pi_1(X_2) \to \pi_1(X)$  is an isomorphism.

For n > 0, this is saying that for any choice of basepoint in X,  $\pi_q(X, X_n)$  is trivial for  $q \le n$ .

#### CW approximation

Any space is weakly equivalent to a CW complex. In fact:

**Theorem 11.8.** Any map  $f: A \to Z$  admits a factorization as

$$A \xrightarrow{i} X \xrightarrow{j} Z$$

where i is a relative CW inclusion and j is a weak equivalence.

This is analogous to the factorization as a cofibration followed by a homotopy equivalence. This factorization is part of the "Quillen model structure" on spaces, while the earlier one is part of the "Strøm model structure." An important special case:  $A = \emptyset$ : so any space admits a weak equivalence from a CW complex.

*Proof.* Fix a space Y. To begin with, pick a point in each path component of Y not meeting A and adjoin to A a discrete set mapping to those points. This gives us a factorization  $A \to X_0 \to Y$  in which  $X_0$  is obtained from A by attaching 0-simplices and  $X_0 \to Y$  is a 0-equivalence.

Next, for each pair of distinct components of A that map to the same component in Y pick points a, b in them and a path in Y from f(a) to f(b). These data determine a map to Y from the pushout

that is bijective on  $\pi_0$ .

These constructions let us assume that both A and Y are path connected, and we do so henceforth. Pick a point in A to use as a basepoint, and use its image in Y as a basepoint there.

We want to add 1-cells to A to obtain a path-connected space X, along with an extension of f to a 1-equivalence  $X \to Y$ . This just means a surjection in  $\pi_1$ . So pick a subset of  $\pi_1(Y)$  that together with  $\operatorname{im}(\pi_1(A) \to \pi_1(Y))$  generate  $\pi_1(Y)$ , and pick a representative loop for each element of that set. This defines a map  $X = A \vee \bigvee S^1 \to Y$  that is surjective on  $\pi_1$ .

Now suppose that  $f: A \to Y$  is a 1-equivalence. We will adjoin 2-cells to A to produce a space X, together with an extension of f to a 2-equivalence.

As a convenience, we first factor f as  $A \hookrightarrow Y' \to Y$  in which the first map is a closed cofibration and the second is a homotopy equivalence. This lets us assume that A is in fact a subspace of Y.

We want to adjoin 2-cells to produce an extension of f to a 2-equivalence  $X \to Y$ . The group  $\pi_2(Y, A)$  measures the failure of f itself to be a 2-equivalence. It is a group with an action of  $\pi_1(A)$ . Pick generators of it as such, and for each pick a representative map

$$(D^2, S^1, *) \to (Y, A, *)$$

Together they determine a map to Y from the pushout in

We want to see that  $\pi_1(X) \to \pi_1(Y)$  is an isomorphism and  $\pi_2(X) \to \pi_2(Y)$  is an epimorphism. The factorization  $A \to X \to Y$  determines a map of homotopy long exact sequences of groups:

$$\pi_{2}(A) \longrightarrow \pi_{2}(X) \longrightarrow \pi_{2}(X, A) \xrightarrow{\partial} \pi_{1}(A) \longrightarrow \pi_{1}(X) \longrightarrow *$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow = \qquad \qquad \downarrow$$

$$\pi_{2}(A) \longrightarrow \pi_{2}(Y) \longrightarrow \pi_{2}(Y, A) \xrightarrow{\partial} \pi_{1}(A) \longrightarrow \pi_{1}(Y) \longrightarrow *$$

By construction, the middle arrow is surjective. The usual diagram chases show that  $\pi_1(X) \to \pi_1(Y)$  is an isomorphism and that  $\pi_2(X) \to \pi_2(Y)$  is an epimorphism.

An identical argument continues the induction. We carried out this case because it's slightly nonstandard, involving nonabelian groups.

At the end, we have to observe that the direct limit of a sequence of cell attachments enjoys the property that

$$\lim_{\to} \pi_q(X_n) \to \pi_q(\lim_{\to} X_n)$$

is an isomorphism.

Notice that if we only want to get to an n-equivalence, we need only add cells up to dimension n: Any space is n-equivalent to a CW complex of dimension at most n.

This construction is of course very ineffective: at each stage you have to compute some relative homotopy group! And since finite complexes have infinitely much homotopy, it seems that this process might go on for ever even for very simple spaces. The cellular chain complex of a CW complex suggests that one might be able to do better. In fact you can, as long as your space is simply connected.

**Theorem 11.9** (C.T.C. Wall: [44],[43]). Let Y be a simply connected space such that  $H_n(Y)$  is finitely generated for all n. Let  $\beta_n$  be the nth Betti number (the rank of  $H_n(Y)$ ) and let  $\tau_n$  be the nth torsion number (the number of finite cyclic summands in  $H_n(Y)$ ). Then there is a CW complex with  $(\beta_n + \tau_{n-1})$  n-cells for each n that admits a weak equivalence to Y.

This is clearly optimal, since in order to produce a finite cyclic summand in the nth homology of a chain complex of finitely generated abelian groups you need generators in dimension n and n + 1.

#### 12 The Postnikov tower

#### Postnikov sections

The cell attaching method used in the proof of CW approximation has other applications.

**Theorem 12.1.** For any space X and any nonnegative integer n, there is a map  $X \to P_n(X)$  with the following properties.

- (1) For every basepoint  $* \in X$ ,  $\pi_q(X,*) \to \pi_q(P_n(X),*)$  is an isomorphism for  $q \le n$ .
- (2) For every basepoint  $* \in P_n(X)$ ,  $\pi_q(P_n(X), *) = 0$  for q > n.
- (3)  $(P_n(X), X)$  is a relative CW complex with cells of dimension not less than (n+2).

When n = 0, the space  $P_0(X)$  is "weakly discrete"; a CW approximation to it is given by a map  $\pi_0(X) \to P_0(X)$ .

When X is path connected and n = 1, this is asserting the existence of a path connected space  $P_1(X)$  with  $\pi_1(P_1(X)) = \pi_1(X)$  and no higher homotopy groups, and a map  $X \to P_1(X)$  inducing an isomorphism on  $\pi_1$ . Assuming  $P_1(X)$  is nice enough to have a universal cover, its universal cover will be weakly contractible. Such a space is said to be "aspherical." Thus any group G is the fundamental group of an aspherical space, because it occurs as  $\pi_1(X)$  for a suitable 2-dimensional CW complex: Express G in terms of generators and relations; form a wedge of circles indexed by the generators, and map in a wedge of circles according to the relations. By the van Kampen theorem, the cofiber of this map will have the desired fundamental group.

*Proof.* Work one connected component at a time. We'll progressively clean out the higher homotopy of the space X, constructing a sequence of spaces

$$X = (n) \to X(n+1) \to X(n+2) \to \cdots$$

all sharing the same  $\pi_q$  for  $q \leq n$  but with

$$\pi_q(X(t)) = 0$$
 for  $n < q \le t$ .

We can take X(n) = X. Thereafter X(t) will be built from X(t-1) by attaching (t+1)-cells, so by Corollary 11.7 the pair (X(t), X(t-1)) is t-connected: the inclusion induces isomorphisms in  $\pi_q$  for q < t and  $\pi_t(X(t), X(t-1)) = 0$ .

So we just want to be sure to kill  $\pi_t(X(t-1))$ , while not introducing anything new in  $\pi_t(X(t))$ . Pick a set of generators for  $\pi_t(X(t-1))$ , and pick representatives  $S^t \to X(t-1)$  for them. Attach (t+1)-cells to X(t-1) using these maps as attaching maps, to form a space X(t). Here's a fragment of the homotopy long exact sequence.

$$\pi_{t+1}(X(t), X(t-1)) \xrightarrow{\partial} \pi_t(X(t-1)) \to \pi_t(X(t)) \to \pi_t(X(t), X(t-1)) = 0.$$

By construction, the boundary map is surjective, so  $\pi_t(X(t)) = 0$ .

Now pass to the limit;

$$P_n(X) = \lim_{n \to \infty} X(t) \,. \qquad \Box$$

If X was a CW complex, we can use skeletal approximation to make all the attaching maps skeletal. They then join any cells of the same dimension in X, and the resulting space  $P_n(X)$  admits the structure of a CW complex in which X is a subcomplex.

What's this about passing to the limit?

Lemma 12.2. Any compact subspace of a CW complex lies in a finite subcomplex.

*Proof.* The "interior" of  $D^n$  is  $D^n \setminus S^{n-1}$  (so for example the interior of  $D^0$  is  $D^0$  itself). A CW complex X is, as a set, the disjoint union of the interiors of its cells. These subspaces are sometimes called "open cells," but since they are rarely open in X I prefer "cell interiors." Any subset of X that meets each cell interior in a finite set is a discrete subspace of X. So any compact subset of X meets only finitely many cell interiors. In particular a CW complex is compact if and only if it is finite.

The boundary of an n-cell (i.e. the image of the corresponding attaching map) is a compact subspace of the (n-1)-skeleton. It meets only finitely many of the cell interiors in that (n-1)-dimensional CW complex. By induction on dimension, all of those cells lie in finite complexes, so the n-cell we began with lies in a finite subcomplex.

Now let K be a compact subspace of X. It lies in the union of the finite subcomplexes containing the finite number of cell interiors meeting K. This union is a finite subcomplex of X.

If (X, A) is a relative CW complex, the quotient X/A is a CW complex, where we can apply this lemma.

Corollary 12.3. Let  $X(0) \subseteq X(1) \subseteq \cdots$  be a sequence of relative CW inclusions. Then for each q

$$\lim_{\to} \pi_q(X(n)) \xrightarrow{\cong} \pi_q(\lim_{\to} X(n))$$

*Proof.* Both  $S^q$  and  $D^{q+1}$  are compact.

Now we have really gotten into homotopy theory! The space  $P_n(X)$  is called the *nth Postnikov section* of X. (Mikhail Postnikov (1927–2004) worked at Steklov Institute in Moscow. This work was published in 1951.) Most of the time they are infinite dimensional, and you usually can't even compute their cohomology.

#### The Postnikov tower

How unique is the map  $X \to P_n(X)$ ? How natural is this construction? To answer these questions, observe:

**Proposition 12.4.** Let n be a nonnegative integer, and let Y be a space such that  $\pi_q(Y, *) = 0$  for every choice of basepoint and all q > n. Let (X, A) be a relative CW complex. If all the cells in  $X \setminus A$  are of dimension at least n + 2 then the map

$$[X,Y] \rightarrow [A,Y]$$
.

is bijective. If there are also (n+1)-cells, the map is still injective.

*Proof.* This uses the fact that if  $\pi_q(Y,*) = 0$  then any map  $S^q \to Y$  landing in the path component containing \* extends to a map from  $D^{q+1}$ .

Surjectivity: We extend a map  $A \to Y$  to a map from X. For each attaching map  $g: S^{q-1} \to \operatorname{Sk}_{q-1}X$  (where  $q \geq n+2$ ) the composite  $f \circ g: S^{q-1} \to Y$  extends over the disk  $D^q$  since q-1 > n. Injectivity: Regard  $(X \times I, X \times \partial I \cup A \times I)$  as a relative CW complex, in which the cells are of dimension one larger than those of X.

Corollary 12.5. Let X be an n-connected CW complex and Y a space with homotopy concentrated in dimension at most n. Then every map from X to Y is homotopic to a constant map.

*Proof.* By CW approximation, we may assume that X has a 0-cell and no other cells of dimension less than n+1. The pair (X,\*) satisfies the requirement necessary to conclude that  $[X,Y] \to [*,Y]$  is injective.

Now let  $f: X \to Y$  be any map. Construct  $X \to P_m(X)$  and  $Y \to P_n(Y)$ , so that  $P_m(X)$  is attached using cells of dimension at least m+2 and  $\pi_q(P_n(Y))=0$  for q>n. If  $m\geq n$ , then by Proposition 12.4 there is a unique homotopy class of maps  $P_m(X) \to P_n(X)$  making

$$X \xrightarrow{f} Y$$

$$\downarrow \qquad \qquad \downarrow$$

$$P_m(X) - - > P_n(Y)$$

commute.

For example we could take X = Y and use the identity map: For  $m \ge n$  there is a unique homotopy class  $P_m(X) \to P_n(X)$  making

commute. When m = n, this shows that the map  $X \to P_m(X)$  is unique up to a unique weak equivalence. When m = n + 1, it gives us a tower of spaces, the *Postnikov tower*:

As you go up in the tower you capture more and more of the homotopy groups of X. The Postnikov tower is functorial on the level of the homotopy category. We have a lot of control over how each space  $P_n(X)$  is constructed, but very little control over what the resulting space looks like – e.g. what its homology is in high dimensions. There is likely to be a lot, even if X is a finite complex.

In a weak sense this tower is Eckmann-Hilton dual to a skeleton filtration: instead of building up a space as a direct limit of a sequence of spaces approximating the homology dimension by dimension, we are building it as the inverse limit of a sequence approximating the homotopy dimension by dimension.

More generally, Proposition 12.4 shows that  $X \to P_n(X)$  is the *initial* map (in Ho**Top**) to a space with nontrivial homotopy only in dimension at most n.

Another common notation for  $P_n(X)$  is  $\tau_{\leq n}X$ : the "truncation" of X at dimension n.

## 13 Hurewicz, Moore, Eilenberg, Mac Lane, and Whitehead

#### Hurewicz theorem

I have claimed that homotopy groups carry a lot of geometric information, but are correspondingly hard to compute. Homology groups are much easier; they are "local," in the sense that you can compute the homology of pieces of a space and glue the results together using Mayer-Vietoris. A cell structure quickly determines the homology (as we'll recall in the next lecture).

So it would be great if we had a way to compare homotopy and homology, maybe by means of a map

$$h: \pi_n(X) \to H_n(X)$$
.

First we have to fix an orientation for the sphere  $S^n = I^n/\partial I^n$  (for n > 0). Do this by declaring the standard ordered basis to be positively ordered. This gives us a preferred generator  $\sigma_n \in H_n(S^n)$ .

Now let  $\alpha \in \pi_n(X)$ . This homotopy class of maps  $S^n \to X$  determines a map  $H_n(S^n) \to H_n(X)$ . Define

$$h(\alpha) = \alpha_*(\sigma_n).$$

This is a well-defined map  $h: \pi_n(X) \to H_n(X)$ , the Hurewicz map.

**Lemma 13.1.** h is a homomorphism.

*Proof.* The product in  $\pi_n(X)$  is given by the composite

$$S^{n} \xrightarrow{\alpha\beta} X$$

$$\downarrow^{\delta} \qquad \uparrow^{\nabla}$$

$$S^{n} \vee S^{n} \xrightarrow{\alpha\vee\beta} X \vee X$$

where  $\delta$  pinches an equator and  $\nabla$  is the fold map. Apply  $\overline{H}_n$  and trace where  $\sigma_n$  goes:

$$\begin{array}{ccc}
\sigma_n & h(\alpha) + h(\beta) \\
\downarrow & & \downarrow \\
(\sigma_n, \sigma_n) & \longmapsto (h(\alpha), h(\beta)).
\end{array}$$

When n=1, the Hurewicz homomorphism factors through the abelianization of  $\pi_1(X)$ .

**Theorem 13.2** (Hurewicz). If X is path-connected,  $\pi_1(X)^{ab} \to H_1(X)$  is an isomorphism. If X is (n-1)-connected for n > 1,  $\pi_n(X) \to H_n(X)$  is an isomorphism.

This can be proved by "elementary means," but we'll prove an improved form of this theorem later and I'd prefer to defer the proof. The n = 1 case is due to Poincaré.

This lowest dimension in which homotopy can occur is the "Hurewicz dimension." If X is an (n-1)-connected CW complex, it has a CW approximation that begins in dimension n, and the reduced homology (being isomorphic to the cellular homology) vanishes below dimension n.

In the simply connected case there is a converse.

Corollary 13.3. Let X be a simply connected space. If  $\overline{H}_q(X) = 0$  for q < n then X is (n-1)-connected.

*Proof.* If n > 2, the Hurewicz theorem says that  $\pi_2(X) = H_2(X) = 0$ , so X is 2-connected. And so on.

Simple connectivity is required here. A good example is provided by the "Poincaré sphere." Let I be the group of orientation-preserving symmetries of the regular icosohedron. It is a subgroup of SO(3) of order 60. Its preimage  $\widetilde{I}$  in the double cover  $S^3$  of SO(3) is a perfect group (of order 120). The quotient space  $S^3/\widetilde{I}$  thus has  $H_1=0$ , and so by Poincaré duality  $H_2=0$  as well. The group acts freely by oriented diffeomorphisms, so the quotient is an oriented 3-manifold with the same homology as  $S^3$ . But its fundamental group is  $\widetilde{I}$ , so it is not even homotopy equivalent to  $S^3$  ... and it's certainly not 2-connected. You can't decide whether or not you need 1-cells or 2-cells by looking at homology alone, in this non-simply connected example. In fact  $\widetilde{I}$  can be presented with two generator and two relations, so  $S^3/\widetilde{I}$  has a CW structure with two 1-cells and two 2-cells. The boundary map  $C_2 \to C_1$  is an isomorphism.

#### Moore spaces

A *Moore space* is a simple space with only one nonzero reduced homology group.

**Proposition 13.4.** Let  $\pi$  be an abelian group and n a positive integer. There is a CW complex M with cells in dimensions 0, n, and n + 1, such that

$$\overline{H}_q(M) = \begin{cases} \pi & \text{if } q = n \\ 0 & \text{otherwise} \,. \end{cases}$$

*Proof.* If  $\pi$  is a free abelian group, we can pick generators and take a corresponding wedge of n-spheres.

For a general abelian group  $\pi$ , pick a resolution by free abelian groups,

$$0 \leftarrow \pi \leftarrow F_0 \stackrel{d}{\leftarrow} F_1 \leftarrow 0$$
.

Pick generators for  $F_0$  and  $F_1$ , say  $\{\alpha_i : i \in I\}$  and  $\{\beta_j : j \in J\}$ . Build the corresponding wedges of n-spheres. If we can realize the map d as  $\overline{H}_n(f)$  for some map between those wedges, then we can take M to be the mapping cone.

A pointed map from a wedge is given by pointed maps from each factor. The map d is determined by

$$d\beta_j = \sum_i a_{ji} \alpha_i$$

for some set of integers  $\{a_{ji}\}$ , finitely nonzero for fixed j. For each i we have an inclusion

$$\operatorname{in}_i:S^n\to\bigvee_{i\in I}S^n$$

determining an element in<sub>i</sub>  $\in \pi_n(\bigvee_i S^n)$ . The sum

$$\sum_{i} a_{ji} \operatorname{in}_{i}.$$

determines a map from  $S^n$  to  $\bigvee_i S^n$ . Use this on the jth copy of  $\bigvee_i S^n$  to get a map

$$\bigvee_{i} S^{n} \leftarrow \bigvee_{i} S^{n}$$

that realizes d. We can then build M as an n+1-dimensional CW complex by taking the mapping cone of this map.

For example the Moore space for  $\pi = \mathbb{Z}/2\mathbb{Z}$  and n = 1 is the familiar space  $\mathbb{R}P^2$ , and when n > 1 we can use  $\Sigma^{n-1}\mathbb{R}P^2$ .

By wedging together Moore spaces we can form a space with any prescribed sequence of homology groups.

#### Eilenberg Mac Lane spaces

Now let M be a Moore space for  $\pi, n$ . Our construction of it began with n-cells, so by skeletal approximation it has no homotopy below dimension n. (We don't need to appeal to Corollary 13.3 for this.) It probably has lots above dimension n, but we can kill all that by forming the Postnikov stage or truncation

$$P_n(M) = \tau_{\leq n} M$$

This is now a space with just one homotopy group, in dimension n. The Hurewicz theorem tells us that this single homotopy group is canonically isomorphic to  $\pi$ .

If n=1 we can start with any group  $\pi$ , abelian or not, form the 2-dimensional complex we just made with  $\pi_1 = \pi$ , and form its Postnikov 1-section.

So we have now constructed a space with a single nonzero homotopy group, in dimension n. This is an *Eilenberg Mac Lane space*, denoted

$$K(\pi, n)$$
.

You know some examples of Eilenberg Mac Lane spaces already.

- $K(\mathbb{Z},1) = S^1$ .  $K(\mathbb{Z}^n,1) = (S^1)^n$ .
- Any closed surface other than  $S^2$  and  $\mathbb{R}P^2$  has contractible universal cover and so is aspherical. There are many other examples of aspherical compact manifolds. But as soon as there is torsion in a group, the Eilenberg Mac Lane space is infinite dimensional.
- The space  $\mathbb{R}P^n$  has  $S^n$  as universal cover, and as  $n \to \infty$  the space  $S^n$  loses all its homotopy groups. So

$$K(\mathbb{Z}/2\mathbb{Z},1) = \mathbb{R}P^{\infty}$$
.

Similarly,

$$K(\mathbb{Z},2) = \mathbb{C}P^{\infty}$$
.

The Eilenberg Mac Lane space  $K(\pi, n)$  can be constructed functorially in  $\pi$ . This is not the case with the Moore space construction. This is why I resisted incorporating the pair  $(\pi, n)$  into a symbol for a Moore space.

Sammy Eilenberg (1913–1998) was born in Poland and worked mainly at Columbia. In addition to constructing their spaces, he and Saunders Mac Lane (1909–2005, Chicago) wrote the foundational paper on category theory. Eilenberg wrote several foundational texts: *Homological Algebra* with Henri Cartan (1904–2008, Paris), and *Foundations of Algebraic Topology* with Norman Steenrod (1910–1971, Princeton University)

#### The Whitehead tower

One further thing we can do at this point: Endow X with a basepoint \* and form the homotopy fiber of the map  $X \to \tau_{\leq n} X$ . By the homotopy long exact sequence, the map from the homotopy fiber will induce isomorphisms in  $\pi_q$  for q > n, while the homotopy groups of the homotopy fiber will be trivial for  $q \leq n$ : it is n-connected. Let's write  $\tau_{>n} X$  for this space. For example,  $\tau_{>0} X$  is the basepoint component of X (assuming  $X \to \pi_0(X)$  is continuous).  $\tau_{\geq 2} X$  is the universal cover of X (assuming that X is path connected and is nice enough to admit a universal cover).

The example of covering spaces shows that  $\tau_{>n}X \to X$  is not unique in quite the same sense that  $X \to \tau_{>n}X$  is; you need a basepoint condition. In the pointed homotopy category,  $\tau_{>n}X \to X$  is the terminal map from an n-connected space.

These spaces fit into a tower also, this time with X at the bottom:

This is the *Whitehead tower*. (George Whitehead, 1918–2004, MIT faculty member, was apparently related neither to Alfred North Whitehead nor to J.H.C. Whitehead. John Moore (1923–2016, working at Princeton) was a student of his, by the way (and an MIT alum), and I was a student of Moore's.)

# 14 Representability of cohomology

I want to think a little more about the significance of Eilenberg Mac Lane spaces. First, how unique are they?

Let  $\pi$  be an abelian group and n a positive integer. Pick a free resolution

$$0 \to F_1 \to F_0 \to \pi \to 0$$
,

pick generators for  $F_0$  and  $F_1$ , and build the corresponding cofiber sequence

$$\bigvee_{j} S^{n} \to \bigvee_{i} S^{n} \to M.$$

So M is a Moore space with  $H_n(M) = \pi$ . Our first model for  $K(\pi, n)$  is the Postnikov section  $\tau_{\leq n}M$ .

**Lemma 14.1.** Let n be a positive integer and let Y be any pointed space such that  $\pi_q(Y, *) = 0$  for  $q \neq n$ , and write G for  $\pi_n(Y, *)$ . Then

$$\pi_n: [\tau_{\leq n}M, Y]_* \to \operatorname{Hom}(\pi, G)$$

is an isomorphism.

*Proof.* Since  $M \to \tau_{\leq n} M$  is universal among maps to spaces with homotopy concentrated in dimensions at most n, it's enough to show that

$$\pi_n: [M,Y]_* \to \operatorname{Hom}(\pi,G)$$

is an isomorphism. Since the sequence defining M is co-exact, we have an exact sequence

$$[\bigvee_{i} S^{n}, Y]_{*} \leftarrow [\bigvee_{i} S^{n}, Y]_{*} \leftarrow [M, Y]_{*} \leftarrow [\bigvee_{i} S^{n+1}, Y]_{*}.$$

Our assumptions on Y imply that this sequence reads

$$\operatorname{Hom}(F_1,G) \leftarrow \operatorname{Hom}(F_0,G) \leftarrow [M,Y]_* \leftarrow 0$$
.

But a homomorphism  $F_0 \to G$  that restricts to zero on  $F_1$  is exactly a homomorphism  $\pi \to G$ .

We phrased this for  $\pi$  and G abelian, but if n=1 the same proof works with both groups arbitrary.

In particular, we could take  $G = \pi$ , and discover that there is a unique homotopy class of maps  $\tau_{\leq n}M \to Y$  inducing the identity in  $\pi_n$ . This map is a weak equivalence. So if Y is also a CW complex, the map is a homotopy equivalence.

We learn from this that any two CW complexes of type  $K(\pi, n)$  are homotopy equivalent by a homotopy equivalence inducing the identity on  $\pi_n$ , and that homotopy equivalence is unique up to homotopy. This leads to:

Corollary 14.2. For any positive integer n there is a functor

$$\mathbf{Ab} \to \mathrm{Ho}(\mathbf{CW}_*)$$

sending  $\pi$  to a space of type  $K(\pi,n)$ , unique up to isomorphism. When n=1 this extends to a functor

$$\mathbf{Gp} \to \mathrm{Ho}(\mathbf{CW}_*)$$
.

In fact it is possible to construct  $K(\pi, n)$  as a functor from **Ab** to the category of topological abelian groups.

The case n=1 is due to Heinz Hopf: There is, up to homotopy, a unique aspherical space with any prescribed fundamental group. The theory of covering spaces can be used in that case to check functoriality. This provides a collection of invariants of groups,  $H_n(K(\pi,1);G)$  and  $H^n(K(\pi,1);G)$ . More generally, any  $\pi$ -module M determines a local coefficient system  $\widetilde{M}$  over  $K(\pi,1)$ , and one then has local homology and cohomology groups. It's not hard to show these are the homology and cohomology of the group with these coefficients:

$$H_n(K(\pi,1);\widetilde{M}) = \operatorname{Tor}_n^{\mathbb{Z}[\pi]}(\mathbb{Z},M), \quad H^n(K(\pi,1);\widetilde{M}) = \operatorname{Ext}_{\mathbb{Z}[\pi]}^n(\mathbb{Z},M).$$

#### Fundamental classes

Let n be a positive integer and Y an (n-1)-connected space. Then  $\overline{H}_q(Y) = 0$  for q < n. Let  $\pi$  be an abelian group. The universal coefficient theorem asserts the existence of a short exact sequence

$$0 \to \operatorname{Ext}^1(H_{q-1}(Y), \pi) \to H^q(Y; \pi) \to \operatorname{Hom}(H_q(Y), \pi) \to 0$$

for any q. This shows that  $H^q(Y;\pi) = 0$  for q < n. When q = n, the Ext term vanishes so the second map is an isomorphism. If we take  $\pi = \pi_n(Y)$ , for example, the inverse of the Hurewicz isomorphism is an element in Hom, and so delivers to us a canonical cohomology class in  $H^n(Y;\pi_n(Y))$ .

In particular, with  $Y = K(\pi, n)$  we obtain a canonical class

$$\iota_n \in H^n(K(\pi,n);\pi)$$

called the fundamental class. Using it, we get a canonical natural transformation

$$[X, K(\pi, n)] \to H^n(X; \pi)$$

sending f to  $f^*(\iota_n)$ .

**Theorem 14.3.** If X is a CW complex, this map is an isomorphism.

That is: On CW complexes, cohomology is a representable functor; the representing object is the appropriate Eilenberg Mac Lane space; and  $\iota_n$  is the universal n-dimensional cohomology class with coefficients in  $\pi$ .

Test cases: We decided that  $K(\mathbb{Z}/2\mathbb{Z}, 1) = \mathbb{R}P^{\infty}$ . So the claim is that  $H^1(X; \mathbb{Z}/2\mathbb{Z}) = [X, \mathbb{R}P^{\infty}]$ . We'll discuss this in more detail later, but  $\mathbb{R}P^{\infty}$  carries the universal real line bundle, so the set of homotopy classes of maps into it (from a CW complex X) is in bijection with the set of isomorphism classes of real line bundles over X. As you may know, that set is indeed given by  $H^1(X; \mathbb{Z}/2\mathbb{Z}) = \text{map}(\pi_1(X), \mathbb{Z}/2\mathbb{Z})$ .

Similar story for  $H^2(X; \mathbb{Z}) = [X, \mathbb{C}P^{\infty}].$ 

One other case is of interest:

$$H^1(X,\mathbb{Z}) = [X,S^1].$$

Other cases are less geometric!

*Proof of Theorem 14.3.* We'll prove a pointed version of the statement:

$$[X, K(\pi, n)]_* \xrightarrow{\cong} \overline{H}^n(X; \pi)$$
.

Fix  $\pi$ , and pick any sequence of Eilenberg Mac Lane CW complexes,  $K(\pi, n)$ ,  $n \geq 0$ . Thus for example  $K(\pi, 0)$  is a CW complex that is homotopy equivalent to the discrete group  $\pi$ : we can take it to be  $\pi$  as a discrete group if we want.

The space  $\Omega K(\pi, n+1)$  accepts a map from  $K(\pi, n)$  that is an isomorphism on  $\pi_n$ ; a CW replacement for  $\Omega K(\pi, n+1)$  thus serves as another model for  $K(\pi, n)$ . Thus  $K(\pi, n)$  has the structure of an H-group. In fact one can use  $\Omega^2 K(\pi, n+2)$ , by the same argument; so this H-group structure is abelian, and the functor  $[-, K(\pi, n)]_*$  takes values in abelian groups.

The map  $[X, K(\pi, n)]_* \to \overline{H}^n(X; \pi)$  is a homomorphism. To see this, use the pinch map  $\Sigma X \to \Sigma X \vee \Sigma X$  to produce a homomorphism

$$\overline{H}^{n+1}(\Sigma X;\pi) \times \overline{H}^{n+1}(\Sigma X;\pi) \to \overline{H}^{n+1}(\Sigma X \vee \Sigma X;\pi) \to \overline{H}^{n+1}(\Sigma X;\pi)$$
.

The argument proving that  $\pi_2$  is abelian shows that this map coincides with the addition in the group  $\overline{H}^{n+1}(\Sigma X;\pi) = \overline{H}^n(X;\pi)$ .

The group structure in

$$[X, K(\pi, n)]_* = [X, \Omega K(\pi, n+1)]_* = [\Sigma X, K(\pi, n+1)]_*$$

has the same source; so the map is a homomorphism by naturality.

Now I will try to prove that the map is an isomorphism by induction on skelata.

When  $X = X_0$ , we can agree that

$$\max_*(X_0, \pi) = \overline{H}^0(X_0, \pi), \quad [X_0, K(\pi, n)]_* = 0 = \overline{H}^n(X_0; \pi), \text{ for } n > 0.$$

We may henceforth assume that X is connected. In general we have a cofiber sequence  $\bigvee S^{q-1} \to X_{q-1} \to X_q$ . It is co-exact and hence induces an exact sequence in  $[-, K(\pi, n)]_*$ . It also induces an exact sequence in reduced cohomology, one that can be regarded as coming from the same geometric source. Since both  $S^{q-1}$  and  $X_{q-1}$  are of dimension less than q, the map is an isomorphism for them. So by the 5-lemma it's an isomorphism on  $X_q$ .

There is still a limiting argument to worry about, if X is infinite dimensional.

Remark 14.4. One can also prove directly that cohomology is a representable functor on CW complexes, and then define Eilenberg Mac Lane spaces as the representing objects. The relevant theorem is "Brown representability" [5]. (Edgar Brown is professor emeritus at Brandeis University.) The fact that contravariant functors satisfying the kind of "descent" embodied by the Mayer-Vietoris theorem are representable gives homotopy theory a special character. Most of the time you can just work with spaces, which are much more concrete than functors!

**Remark 14.5.** Note that the suspension isomorphism in reduced cohomology is represented by the weak equivalence

$$K(\pi, n) \to \Omega K(\pi, n+1)$$

adjoint to the map representing the suspension of the fundamental class. A family of pointed spaces  $\ldots, E_0, E_1, \ldots$  equipped with maps  $E_n \to \Omega E_{n+1}$  (or equivalently  $\Sigma E_n \to E_{n+1}$ ) is a (topological) spectrum. It's an  $\Omega$ -spectrum if the maps  $E_n \to \Omega E_{n+1}$  are all weak equivalences. Much of what we just did above carries over to  $\Omega$ -spectra in general; the (abelian!) groups

$$\overline{E}^n(X) := [X, E_n]_*$$

form the groups in a (reduced generalized) cohomology theory. There are many examples. Any generalized cohomology theory is representable on CW complexes by an  $\Omega$  spectrum.

**Remark 14.6.** One asset of representability is the "Yoneda lemma": Given a functor  $F: \mathcal{C} \to \mathbf{Set}$  and an object Y in  $\mathcal{C}$ , we get inverse isomorphisms

$$n.t.(\mathcal{C}(-,Y),F) \rightleftarrows F(Y)$$
$$\theta \mapsto \theta_Y(1_Y)$$
$$(f \mapsto f^*(y)) \longleftrightarrow y$$

In particular

$$\mathrm{n.t.}(\mathcal{C}(-,Y),\mathcal{C}(-,Z)) = \mathcal{C}(Y,Z) \,.$$

So for example

$$\text{n.t.}(H^m(-,A),H^n(-,B)) = [K(A,m),K(B,n)] = H^n(K(A,m);B).$$

Understanding the natural transformations acting between different dimensions of  $H^*(-; \mathbb{F}_2)$ , for example, is addressing the optimal value category for mod 2 cohomology. It's a graded  $\mathbb{F}_2$  algebra, yes, but much more as well. This is the story of Steenrod operations, and it's addressed in full by computing  $H^*(K(\mathbb{F}_2, n); \mathbb{F}_2)$ .

## 15 Obstruction theory

#### Cellular homology

Let (X, A) be a relative CW-complex with skelata

$$A = X_{-1} \subset X_0 \subset X_1 \subset \cdots \subset X$$
.

The inclusion  $X_{n-1} \hookrightarrow X_n$  is a cofibration, so  $H_*(X_n, X_{n-1}) \cong \overline{H}_*(X_n/X_{n-1})$ . A choice of cell structure establishes a homeomorphism

$$X_n/X_{n-1} = \bigvee_{i \in \Sigma_n} S_i^n,$$

where  $\Sigma_n$  is the set of *n*-cells, so

$$H_*(X_n, X_{n-1}) \cong \mathbf{Z}[\Sigma_n]$$

This group is the cellular chain group  $C_n = C_n(X, A)$ .

There is a boundary map  $d: C_{n+1} \to C_n$ , defined by

$$d: C_{n+1} = H_{n+1}(X_{n+1}, X_n) \xrightarrow{\partial} H_n(X_n) \to H_n(X_n, X_{n-1}) = C_n$$

This gives us the *cellular chain complex*. In terms of the basis given by a choice of cell structure, the differential  $d: C_{n+1} \to C_n$  is giving exactly the data of the *relative attaching maps* 

$$S^n \xrightarrow{\alpha_i} X_n \to X_n/X_{n-1}$$

where  $\alpha_i$  runs through the attaching maps of the (n+1)-cells. Passage to the relative attaching maps forgets a great deal of information about the homotopy type of X; homology is a rather weak invariant in this sense.

A theorem proved last term (at least when  $A = \emptyset$ ) asserts that

$$H_n(X,A) \cong H_n(C_*(X,A))$$
.

Of course, the same story runs for cohomology: one gets a chain complex which, in dimension n, is given by

$$C^n(X, A; \pi) = \operatorname{Hom}(C_n(X, A), \pi) = \operatorname{Map}(\Sigma_n, \pi),$$

where  $\pi$  is any abelian group, and

$$H^{n}(X, A; \pi) = H^{n}(C^{*}(X, A; \pi)).$$

#### Obstruction theory

We've seen that when the dimension of the CW complex X is less than the connectivity of the space Y, any map from X to Y is null-homotopic. What if there is some overlap? Here's a more general type of question we can try to answer.

**Question 15.1.** Let  $f: A \to Y$  be a map from a space A to Y. Suppose (X, A) is a relative CW-complex. When can we find an extension in the diagram below?

$$A \xrightarrow{f} Y$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$X$$

We've seen that answering this kind of question can also lead to results about the uniqueness of an extension, by considering  $X \times \partial I \cup A \times I \subset X \times I$ .

Let's try to make this extension skeleton by skeleton, and find what obstructions occur. We can start easily enough! If Y is empty then A is too, and there's an extension if and only if X is empty as well.

More realistically, as long as Y is nonempty we can certainly extend to  $X_0$  by sending the new points anywhere you like in Y.

So make such a choice:  $f: X_0 \to Y$ . Can we extend f further over  $X_1$ ? Well, we can extend if and only if for every pair a and b of 0-cells in  $X_0$  that are in the same path component of  $X_1$ , the images f(a) and f(b) are in the same path component in Y. Note that we might do better at this stage if we could go back and choose f better. This simple observation serves as a model for the whole process.

Let's now assume we have constructed  $f: X_n \to Y$ , for  $n \ge 1$ , and hope to extend it over  $X_{n+1}$ . Pick attaching maps for the (n+1)-cells, so we have the diagram

$$\coprod_{i \in \Sigma_{n+1}} S^n \xrightarrow{\alpha} X_n \xrightarrow{f} Y$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$\coprod_{i \in \Sigma_{n+1}} D^n \longrightarrow X_{n+1}$$

The desired extension exists if the composite  $S^n \xrightarrow{\alpha_i} X_n \to Y$  is nullhomotopic for each  $i \in \Sigma_{n+1}$ . Now is the moment to assume that Y is path connected and simple, so that

$$[S^n, Y] = \pi_n(Y, *)$$

canonically for any choice of basepoint. We will therefore omit basepoints from the notation.

This procedure produces a map  $\theta_g: \Sigma_{n+1} \to \pi_n(Y)$ , that is, an *n*-cochain,  $\theta_f \in C^{n+1}(X, A; \pi_n(Y))$ , and  $\theta_f = 0$  if and only if f extends to a map  $X_{n+1} \to Y$ .

**Proposition 15.2.**  $\theta_f$  is a cocycle in  $C^{n+1}(X, A; \pi_n(Y))$ .

*Proof.*  $\theta_f$  gives a map  $H_{n+1}(X_{n+1}, X_n) \to \pi_n(Y)$ . We would like to show that the composite

$$H_{n+2}(X_{n+2}, X_{n+1}) \xrightarrow{\partial} H_{n+1}(X_{n+1}) \to H_{n+1}(X_{n+1}, X_n) \xrightarrow{\theta_f} \pi_n(Y)$$

is trivial.

We'll see this by relating the homotopy long exact sequence to the homology long exact sequence. A relative homotopy class is represented by a map

$$(I^q, \partial I^q, J_a) \to (X, A, *)$$
.

Our choice of orientation for  $I^q/\partial I^q$  specifies a generator for  $H_q(I^q, \partial I^q)$ . Evaluation of  $H_n$  then determines a map

$$h: \pi_q(X, A, *) \to H_q(X, A)$$
,

the *relative Hurewicz homomorphism*. It is again a homomorphism, extending the definition of the absolute Hurewicz homomorphism, and gives us a map of long exact sequences.

The characteristic maps in the cell structure for X give us elements of  $\pi_{n+1}(X_{n+1}, X_n)$  that map to the generators of  $H_{n+1}(X_{n+1}, X_n)$ .

These observations lead to part of the commutative diagram below.

The bottom square commutes by definition of  $\theta_f$ . Tracing around the left side goes through two successive maps in the homotopy long exact sequence, and so sends these elements to zero.

This cochain  $\theta_f$  is the "obstruction cocycle" associated to  $f: X_n \to Y$ . It obstructs the extension of f over the (n+1)-skeleton. This theorem gives a way of extending a map  $A \to Y$  skeleton by skeleton all the way to a map  $X \to Y$ .

But it could happen that the extension you made to  $X_n$  doesn't admit a further extension to  $X_{n+1}$ , while some other extension to  $X_n$  would. In order to maintain some control, let's fix the extension to  $X_{n-1}$ , but allow the extension to  $X_n$  to vary.

**Theorem 15.3.** Let (X, A) be a relative CW-complex and Y a path-connected simple space, and let  $n \ge 1$ . Let  $f: X_n \to Y$  be a map from the n-skeleton of X, and let  $\theta_f \in C^{n+1}(X, A; \pi_n(Y))$  be the associated obstruction cocycle. Then  $f|_{X_{n-1}}$  extends to  $X_{n+1}$  if and only if  $[\theta_f] \in H^{n+1}(X, A; \pi_n(Y))$  is zero.

*Proof.* The proof begins with the construction a "difference cochain"  $\delta$  associated to maps  $f', f'': X_n \to Y$  together with a homotopy from  $f'|_{X_{n-1}}$  to  $f''|_{X_{n-1}}$  rel A. It will not be a cocycle. Instead, it will provide a homology between the obstruction cocycles associated to f' and f''.

We'll lighten notation by dropping indication of the subspace A. Fix a cell structure on X. This is about homotopies, so let's begin by giving  $X \times I$  the CW structure in which

$$(X \times I)_n = (X_n \times \partial I) \cup (X_{n-1} \times I).$$

Each n-cell e in X produces in  $X \times I$  an (n+1)-cell  $e \times I$  and two n-cells  $e \times 0$  and  $e \times 1$ . Thus there is a map

$$-\times I: C_n(X) \to C_{n+1}(X \times I)$$
,

given by linearly extending the assignment on cells. This is not a chain map; rather

$$d(e \times I) = (de) \times I + (-1)^n (e \times 1 - e \times 0)$$

(by choice of orientation of the unit interval).

This construction defines a map

$$C^{n+1}(X; \pi_n(Y)) \to C^n(X; \pi_n(Y))$$

by sending a cochain c to  $e \mapsto c(e \times I)$ .

Define a map  $g:(X\times I)_n\to Y$  as follows. Send  $X_n\times 0$  by  $f_0$ ,  $X_n\times 1$  by  $f_1$ , and  $X_{n-1}\times I$  by a homotopy between the restrictions of  $f_0$  and  $f_1$  to  $X_{n-1}$ . We then have the obstruction cocycle  $\theta_g\in C^{n+1}(X\times I;\pi_n(Y))$  associated to the map g.

Our difference cochain  $\delta \in C^n(X; \pi_n(Y))$  is defined by

$$\delta(e) = \theta_q(e \times I)$$
.

For any n-cell e in X, calculate as follows, using the definition of the differential in the cellular cochain complex:

$$0 = (d\theta_q)(e \times I) = \theta_q(d(e \times I)) = \theta_q((de) \times I) \pm (\theta_q(e \times 0) - \theta_q(e \times 1)).$$

The three terms can be re-expressed as follows.

$$\theta_q((de) \times I) = \delta(de) = (d\delta)(e)$$
,

$$\theta_g(e \times 0) = \theta_{f'}(e), \quad \theta_g(e \times 1) = \theta_{f''}(e).$$

This verifies that

$$d\delta = \pm (\theta_{f'} - \theta_{f''}).$$

So for a map  $f: X_n \to Y$ , the cohomology class of the obstruction cocycle  $\theta_f$  depends only on  $f|_{X_{n-1}}$ . In particular if  $f|_{X_{n-1}}$  does extend to a map from  $X_{n+1}$ , then this cohomology class vanishes.

For the converse, we observe that for any  $f': X_n \to Y$  and  $\delta \in C^n(X; \pi_n(Y))$  there exists an extension f'' of  $f'|_{X_{n-1}}$  such that  $\delta$  is precisely the difference cochain associated to the pair (f', f'') and the constant homotopy between their restrictions to  $X_{n-1}$ . We leave this to you; it uses the homotopy extension property.

We can now argue as follows. Suppose that  $[\theta_{f'}] = 0 \in H^{n+1}(X; \pi_n(Y))$ . Pick a null-homology  $\delta$  of  $\theta_{f'}$ , and pick f'' in such a way that  $\delta$  is the difference cocycle between f' and f''. Then (adjusting the sign if necessary)

$$\theta_{f''} = \theta_{f'} - d\delta = 0,$$

so f'' extends to  $X_{n+1}$ .

The easiest way to check that an obstruction class vanishes is to know that it lies in a zero group.

**Corollary 15.4.** Let Y be a path connected simple space and (X, A) a relative CW complex. If  $H^{n+1}(X, A; \pi_n(Y)) = 0$  for all  $n \ge 1$  then any map  $A \to Y$  extends to a map  $X \to Y$ . If moreover  $H^n(X, A; \pi_n(Y)) = 0$  for all  $n \ge 1$  then such an extension is unique up to homotopy rel A.

*Proof.* The second assertion follows from the isomorphism

$$H^{n+1}(X \times I, A \times I \cup X \times \partial I; \pi) = H^n(X, A; \pi).$$

This raises important questions. The reduced cohomology of a space may well be trivial with coefficients in a finite p-group, for a fixed prime p, for example. Are there homological conditions on Y guaranteeing that each homotopy group is a finite p-group? The power to prove results of that sort is part of the revolution in homotopy theory engineered by Jean-Pierre Serre, developments we will get to later in this course.

# Chapter 3

# Vector bundles and principal bundles

#### 16 Vector bundles

Each point in a smooth manifold M has a "tangent space." This is a real vector space, whose elements are equivalence classes of smooth paths  $\sigma : \mathbb{R} \to M$  such that  $\sigma(0) = x$ . The equivalence relation retains only the velocity vector at t = 0. These vector spaces "vary smoothly" over the manifold. The notion of a vector bundle is a topological extrapolation of this idea.

Let B be a topological space. To begin with, let's define the "category of spaces over B,"  $\mathbf{Top}/B$ . An object is just a map  $E \to B$ . To emphasize that this is single object, and that it is an object "over B," we may give it a symbol and display the arrow vertically:  $\xi : E \downarrow B$ . A morphism from  $p' : E' \to B$  to  $p : E \to B$  is a map  $E' \to E$  making

commute.

This category has products, given by the fiber product over B:

$$E' \times_B E = \{(e', e) : p'e' = pe\} \subseteq E' \times E.$$

Using it we can define an "abelian group over B": an object  $E \downarrow B$  together with a "zero section"  $0: B \to E$  (that is, a map from the terminal object of  $\mathbf{Top}/B$ ) and an "addition"  $E \times_B E \to E$  (of spaces over B) satisfying the usual properties.

As an example, any topological abelian group A determines an abelian group over B, namely  $\operatorname{pr}_1: B\times A\to B$  with its evident structure maps. If A is a ring, then  $\operatorname{pr}_1: B\times A\to B$  is a "ring over B." For example, we have the "reals over B," and hence can define a "vector space over B." Each fiber has the structure of a vector space, and this structure varies continuously as you move around in the base.

Vector spaces over B form a category in which the morphisms are maps covering the identity map of B that are linear on each fiber.

**Example 16.1.** Let S be the subspace of  $\mathbb{R}^2$  consisting of the x and y axes, and consider  $\operatorname{pr}_1: S \to \mathbb{R}$ . Then  $\operatorname{pr}_1^{-1}(0) = \mathbb{R}$  and  $\operatorname{pr}_1^{-1}(s) = 0$  for  $s \neq 0$ . With the evident structure maps, this is a perfectly good ("skyscraper") vector space over  $\mathbb{R}$ . This example is peculiar, however; it is not locally constant. Our definition of vector bundles will exclude it and similar oddities. Sheaf theory is the proper home for examples like this.

But this example occurs naturally even if you restrict to trivial bundles and maps between them. The trivial bundle  $\operatorname{pr}_1:\mathbb{R}\times\mathbb{R}\to\mathbb{R}$  has as an endomorphism the map

$$(s,t)\mapsto (s,st)$$
.

This map is an isomorphism on almost all fibers, but is zero over s = 0. So if you want to form a kernel or the cokernel, you will get the skyscraper vector space over  $\mathbb{R}$ . The image will be a vector space over X with a complementary peculiarity.

**Definition 16.2.** A vector bundle over B is a vector space E over B that is locally trivial – that is, every point  $b \in B$  has a neighborhood over which E is isomorphic to a trivial bundle – and whose fiber vector spaces are all of finite dimension.

**Remark 16.3.** As in our definition of fiber bundles, we will always assume that a vector bundle admits a numerable trivializing cover. On the other hand, there is nothing to stop us from replacing  $\mathbb{R}$  with  $\mathbb{C}$  or even with the quaternions  $\mathbb{H}$ , and talking about complex or quaternionic vector bundles.

If  $\xi : E \downarrow B$  is a vector bundle, then E is called the *total space*, the map  $p : E \to B$  is called the *projection map*, and B is called the *base space*. We may write  $E(\xi), B(\xi)$  for the total space and base space, and  $\xi_b$  for the fiber of  $\xi$  over  $b \in B$ .

If all the fibers are of dimension n, we have an n-dimensional vector bundle or an "n-plane bundle."

**Example 16.4.** The "trivial" n-dimensional vector bundle over B is the projection  $\operatorname{pr}_1: B \times \mathbb{R}^n \to B$ . We may write  $n\epsilon$  for it.

Example 16.5. At the other extreme, Grassmannians support highly nontrivial vector bundles. We can form Grassmannians over any one of the three (skew)fields  $\mathbb{R}, \mathbb{C}, \mathbb{H}$ . Write K for one of them, and consider the (left) K-vector space  $K^n$ . The Grassmannian (or Grassmann manifold)  $Gr_k(K^n)$  is the space of k-dimensional K-subspaces of  $K^n$ . As we saw last term, this is a topologized as a quotient space of a Stiefel variety  $V_k(K^n)$  of k-frames in  $K^n$ . To each point in  $Gr_k(K^n)$  is associated a k-dimensional subspace of  $K^n$ . This provides us with a k-dimensional K-vector bundle  $\xi_{n,k}$  over  $Gr_k(K^n)$ , with total space

$$E(\xi_{n,k}) = \{ (V, x) \in \operatorname{Gr}_k(K^n) \times K^n : x \in V \}$$

This is the canonical or tautologous vector bundle over  $Gr_k(K^n)$ . It occurs as a subbundle of  $n\epsilon$ .

**Exercise 16.6.** Prove that  $\xi_{n,k}$ , as defined above, is locally trivial, so is a vector bundle over  $Gr_k(K^n)$ .

For instance, when k = 1, we have  $\operatorname{Gr}_1(\mathbb{R}^n) = \mathbf{R}P^{n-1}$ . The tautologous bundle  $\xi_{n,1}$  is 1-dimensional; it is a *line bundle*, the canonical line bundle over  $\mathbf{R}P^{n-1}$ . We may write  $\lambda$  for this or any line bundle.

**Example 16.7.** Let M be a smooth manifold. Define  $\tau_M$  to be the tangent bundle  $TM \downarrow M$  over M. For example, if  $M = S^{n-1}$ , then

$$TS^{n-1} = \{(x, v) \in S^{n-1} \times \mathbb{R}^n : v \cdot x = 0\}.$$

#### Constructions with vector bundles

Just about anything that can be done for vector spaces can also be done for vector bundles:

1. The pullback of a vector bundle is again a vector bundle: If  $p: E \to B$  is a vector bundle then the map p' in the pullback diagram below is also a vector bundle.

$$E' \xrightarrow{\overline{f}} E$$

$$\downarrow_{p'} \qquad \downarrow_{p}$$

$$B' \xrightarrow{f} B$$

The pullback of  $\xi: E \downarrow B$  bundle may be denoted  $f^*\xi$ .

There's a convenient way characterize a pullback: the top map  $\overline{f}$  in the pullback diagram has two key properties: It covers f, and it is a linear isomorphism on fibers. These conditions suffice to present p' as the pullback of p along f.

- 2. If  $p: E \to B$  and  $p': E' \to B'$ , then the product map  $p \times p': E \times E' \to B \times B'$  is a vector bundle whose fiber over (x, y) is the vector space  $p^{-1}(x) \times p'^{-1}(y)$ .
- 3. If B = B', we can form the pullback:

$$E \oplus E' \longrightarrow E \times E'$$

$$\downarrow \qquad \qquad \downarrow$$

$$B \xrightarrow{\Delta} B \times B$$

The bundle  $\xi \oplus \xi' : E \oplus E' \downarrow B$  is called the Whitney sum of  $\xi : E \downarrow B$  and  $\xi' : E' \downarrow B$ . (Hassler Whitney (1907–1989) working mainly at the Institute for Advanced Study in Princeton, is responsible for many early ideas in geometric topology.) For instance,

$$n\epsilon = \epsilon \oplus \cdots \oplus \epsilon$$
.

4. If  $\xi : E \downarrow B$  and  $\xi' : E' \downarrow B$  are two vector bundles over B, we can form another vector bundle  $\xi \otimes \xi'$  over B by taking the fiberwise tensor product. Likewise, taking the fiberwise Hom produces a vector bundle  $\text{Hom}(\xi, \xi')$  over B.

**Example 16.8.** Recall from Example 16.5 the tautological bundle  $\lambda$  over  $\mathbb{R}P^{n-1}$ . The tangent bundle  $\tau_{\mathbb{R}P^{n-1}}$  also lives over  $\mathbb{R}P^{n-1}$ . It is natural to wonder what is the relationship between these two bundles. We claim that

$$\tau_{\mathbf{R}P^{n-1}} = \mathrm{Hom}(\lambda, \lambda^{\perp})$$

where  $\lambda^{\perp}$  denotes the fiberwise orthogonal complement of  $\lambda$  in  $n\epsilon$ . To see this, make use of the double cover  $S^{n-1} \downarrow \mathbf{R}P^{n-1}$ . The projection map is smooth, and covered by a fiberwise isomorphism of tangent bundles. The fibers  $T_x S^{n-1}$  and  $T_{-x} S^{n-1}$  are both identified with the orthogonal complement of  $\mathbb{R}x$  in  $\mathbb{R}^n$ , and the differential of the antipodal map sends v to -v. So the tangent vector to  $\pm x \in \mathbf{R}P^{n-1}$  represented by (x,v) is the same as the tangent vector represented by (-x,-v). This tangent vector determines a homomorphism  $\lambda_x \to \lambda_x^{\perp}$  sending tx to tv.

Exercise 16.9. Prove that

$$\tau_{\operatorname{Gr}_k(\mathbb{R}^n)} = \operatorname{Hom}(\xi_{n,k}, \xi_{n,k}^{\perp}).$$

#### Metrics and splitting exact sequences

A map of vector bundles,  $\xi \to \eta$ , over a fixed base can be identified with a section of  $\text{Hom}(\xi, \eta)$ . We have seen that the kernel and cokernel of a homomorphism will be vector bundles only if the rank is locally constant.

In particular, we can form kernels of surjections and cokernels of injections; and consider short exact sequences of vector bundles. It is a characteristic of topology, as opposed to analytic or algebraic geometry, that short exact sequences of vector bundles always split. To see this we use a "metric."

**Definition 16.10.** A *metric* on a vector bundle is a continuous choice of inner products on the fibers.

**Lemma 16.11.** Any (numerable) vector bundle  $\xi$  admits a metric.

*Proof.* This will use the fact that if g, g' are both inner products on a vector space then tg + (1-t)g' (for t between 0 and 1) is another. So the space of metrics on a vector bundle  $E \downarrow B$  forms a convex subset of the vector space of continuous functions  $E \times_B E \to \mathbb{R}$ .

Pick a trivializing open cover  $\mathcal{U}$  for  $\xi$ , and for each  $U \in \mathcal{U}$  an isomorphism  $\xi|_U \cong U \times V_U$ . Pick an inner product  $g_U$  on each of the vector spaces  $V_U$ . Pick a partition of unity subordinate to  $\mathcal{U}$ ; that is, functions  $\phi_U : U \to [0, 1]$  such that the preimage of (0, 1] is U and

$$\sum_{x \in U} \phi_U(x) = 1.$$

Now the sum

$$g = \sum_{U} \phi_{U} g_{U}$$

is a metric on  $\xi$ .

**Corollary 16.12.** Any exact sequence  $0 \to \xi' \to \xi \to \xi'' \to 0$  of vector bundles (over the same base) splits.

*Proof.* Pick a metric for  $\xi$ . Using it, form the orthogonal complement  $\xi'^{\perp}$ . The composite

$$\xi'^{\perp} \hookrightarrow \xi \to \xi''$$

is an isomorphism. This provides a splitting of the surjection  $\xi \to \xi''$  and hence of the short exact sequence.

# 17 Principal bundles, associated bundles

#### *I*-invariance

We will denote by Vect(B) the set of isomorphism classes of vector bundles over B, and  $Vect_n(B)$  the set of n-plane bundles.

Exercise 17.1. Justify the use of the word "set"!

Vector bundles pull back, and isomorphic vector bundles pull back to isomorphic vector bundles. This establishes Vect as a contravariant functor on **Top**:

$$\text{Vect}: \mathbf{Top}^{op} \to \mathbf{Set}$$
.

How computable is this functor? As a first step in answering this, we note that it satisfies the following characteristic property of bundle theories.

**Theorem 17.2.** The functor Vect is I-invariant (where I denotes the unit interval): that is, the projection  $\operatorname{pr}_1: X \times I \to X$  induces an isomorphism  $\operatorname{Vect}(X) \to \operatorname{Vect}(X \times I)$ .

We will prove this in the next lecture. The map  $\operatorname{pr}_1:X\times I\to X$  is a split surjection, so  $\operatorname{pr}_1^*:\operatorname{Vect}(X)\to\operatorname{Vect}(X\times I)$  is a split injection. Surjectivity is harder.

An important corollary of this result is:

#### Corollary 17.3. Vect is a homotopy functor.

*Proof.* Let  $\xi: E \downarrow B$  be a vector bundle and suppose  $H: B' \times I \to B$  a homotopy between two maps  $f_0$  and  $f_1$ . We are claiming that  $f_0^* \xi \cong f_1^* \xi$ . This is far from obvious!

In the diagram

the map  $\operatorname{pr}_1$  induces a surjection in Vect by Theorem 17.2. It follows that  $\operatorname{in}_0^* = \operatorname{in}_1^*$ , so  $f_0^* = \operatorname{in}_0^* \circ h^* = \operatorname{in}_1^* \circ h^* = f_1^*$ .

#### Principal bundles

**Definition 17.4.** Let G be a topological group. A *principal G-bundle* is a right action of G on a space P such that:

- 1. G acts freely.
- 2. The orbit projection  $P \to P/G$  is a fiber bundle.

There's a famous video of J.-P. Serre talking about writing mathematics. In it he says you have to know the difference between "principle" and "principal". He contemplated what a "bundle of principles" might be – varying over a moduli space of individuals, perhaps.

We will only care about Lie groups, among which are discrete groups.

Principal bundles are not unfamiliar objects, as the next example shows.

**Example 17.5.** Suppose G is discrete. Then the fibers of the orbit projection  $P \to P/G$  are all discrete. Therefore, the condition that  $P \to P/G$  is a fiber bundle is simply that it's a covering projection. Such an action is sometimes said to be "properly discontinuous."

As a special case, let X be a space with universal cover  $X \downarrow X$  (so X is path connected and semi-locally simply connected). Then  $\pi_1(X)$  acts freely on  $\widetilde{X}$ , and  $p:\widetilde{X}\to X$  is the orbit projection; we have a principal  $\pi_1(X)$ -bundle. Explicit examples include the principal  $C_2$ -bundles  $S^{n-1} \downarrow \mathbb{R}P^{n-1}$ .

We can use the universal cover to classify covering spaces of X. Remember how this goes: The fundamental group at \* acts on the fiber over \* of any covering projection to produce a left  $\pi_1(X)$ -set. A functor in the other direction is given as follows. Let F be any set with left  $\pi_1(X)$ -action, and form the "balanced product"

$$\widetilde{X} \times_{\pi_1(X)} F = \widetilde{X} \times F / \sim$$

where  $(y, gz) \sim (yg, z)$ , for elements  $y \in \widetilde{X}$ ,  $z \in F$ , and  $g \in \pi_1(X)$ . The composite  $p \circ \operatorname{pr}_1 : \widetilde{X} \times F \to X$  factors to give a map

$$\widetilde{X} \times_{\pi_1(X)} F \to X$$

that is a covering projection.

**Theorem 17.6** (Covering space theory). Suppose that X is path-connected and semi-locally simply connected. Then these constructions provide an equivalence of categories

$$\left\{ \frac{Left \ \pi_1(X)\text{-}sets}{equivariant \ bijections} \right\} \cong \left\{ \frac{Covering \ spaces \ of \ X}{isomorphisms} \right\}.$$

This story motivates constructions in the more general setting of principal G-bundles.

**Construction 17.7.** Let  $P \downarrow B$  be a principal G-bundle. If F is a left G-space, we can define a new fiber bundle, "associated" to  $P \downarrow B$ , exactly as above:

$$P \times_G F$$

$$\downarrow_q$$

$$B$$

Let's check that the fibers are homeomorphic to F. Let  $x \in B$ , and pick  $y \in P$  over x. Map  $F \to q^{-1}(x)$  by  $z \mapsto [y, z]$ . We claim that this is a homeomorphism. The inverse  $q^{-1}(x) \to F$  is given by

$$[y', z'] = [y, gz'] \mapsto gz',$$

where y' = yg for some g (which is necessarily unique since the G action is simply transitive on fibers of P). These two maps are inverse homeomorphisms.

If F is a finite dimensional vector space on which G acts linearly, then we get a vector bundle from this construction.

Let  $\xi: E \downarrow B$  be an *n*-plane bundle. Construct a principal  $GL_n(\mathbb{R})$ -bundle  $P(\xi)$  by defining

$$P(\xi)_b = \{ \text{ordered bases for } E(\xi)_b = \text{Iso}(\mathbb{R}^n, E(\xi)_b) \}.$$

To define the topology, think of  $P(\xi)$  as a quotient of the disjoint union of trivial bundles over the open sets in a trivializing cover for  $\xi$ ; while for trivial bundles

$$P(B \times \mathbb{R}^n) = B \times \operatorname{Iso}(\mathbb{R}^n, \mathbb{R}^n)$$

topologically, where  $\text{Iso}(\mathbb{R}^n, \mathbb{R}^n) = GL_n(\mathbb{R})$  is given the usual topology as a subspace of  $\mathbb{R}^{n^2}$ .

There is a right action of  $GL_n(\mathbb{R})$  on  $P(\xi)$ , given by precomposition. It is easy to see that this action is free and simply transitive on fibers. One therefore has a principal action of  $GL_n(\mathbb{R})$  on  $P(\xi)$ . The bundle  $P(\xi)$  is called the *principalization* of  $\xi$ .

Given the principalization  $P(\xi)$ , we can recover the total space  $E(\xi)$ , using the defining linear action of  $GL_n(\mathbb{R})$  on  $\mathbb{R}^n$ :

$$E(\xi) \cong P(\xi) \times_{GL_n(\mathbb{R})} \mathbb{R}^n$$
.

These two constructions are inverses: the theories of n-plane bundles and of principal  $GL_n(\mathbb{R})$ -bundles are equivalent.

**Remark 17.8.** Suppose that we have a metric on  $\xi$ . Instead of looking at all ordered bases, we can use instead all ordered orthonormal bases in each fiber. This give the *frame bundle* 

 $\operatorname{Fr}(\xi)_b = \{ \text{ordered orthonormal bases of } E(\xi)_b \} = \{ \text{isometric isomorphisms } \mathbb{R}^n \to E(\xi)_b \}.$ 

The orthogonal group O(n) acts freely and fiberwise transitively on this space, endowing  $Fr(\xi)$  with the structure of a principal O(n)-bundle.

Providing a vector bundle with a metric, when viewed in terms of the associated principal bundles, is an example of "reduction of the structure group." We are giving a principal O(n) bundle P together with an isomorphism of principal  $GL_n(\mathbb{R})$  bundles from  $P \times_{O(n)} GL_n(\mathbb{R})$  to the principalization of  $\xi$ . Many other geometric structures can be described in this way. An orientation of  $\xi$ , for example, consists of a principal  $SL_n(\mathbb{R})$  bundle Q together with an isomorphism from  $Q \times_{SL_n(\mathbb{R})} GL_n(\mathbb{R})$  to the principalization of  $\xi$ .

Fix a topological group G. Define  $\operatorname{Bun}_G(B)$  as the set of isomorphism classes of G-bundles over B. An isomorphism is a G-equivariant homeomorphism over the base. Again, arguing as above, this leads to a contravariant functor  $\operatorname{Bun}_G:\operatorname{Top}\to\operatorname{\mathbf{Set}}$ . The above discussion gives a natural isomorphism of functors:

$$\operatorname{Bun}_{GL_n(\mathbb{R})}(B) \cong \operatorname{Vect}(B).$$

The *I*-invariance of Vect is therefore a special case of:

**Theorem 17.9.** Bun<sub>G</sub> is I-invariant, and hence is a homotopy functor.

One case is easy to prove: If X is contractible, then any principal G-bundle  $P \downarrow X$  is trivial. It's enough to construct a section. Since the identity map on X is homotopic to a constant map (with value  $* \in X$ , say), the constant map  $c_p : X \to Q$  for any  $p \in P$  over  $* \in X$  makes

$$X \xrightarrow{c_p} X$$

commute up to homotopy. But since  $P \downarrow X$  is a fibration, this implies that there is then an *actual* section. And a section of a principal bundle determines a trivialization of it.

We have considered only isomorphisms of principal bundles. But any continuous equivariant map of principal bundles over the same base that covers the identity endomorphism of the base is in fact an isomorphism.

# 18 *I*-invariance of $Bun_G$ , and *G*-CW-complexes

Let G be a topological group. We want to show that the functor  $\operatorname{Bun}_G:\operatorname{\mathbf{Top}}^{op}\to\operatorname{\mathbf{Set}}$  is I-\ninvariant, i.e., the projection  $\operatorname{pr}_1:X\times I\to X$  induces an isomorphism  $\operatorname{Bun}_G(X)\stackrel{\cong}{\to}\operatorname{Bun}_G(X\times I)$ .

Injectivity is easy: the composite  $X \xrightarrow{\text{in}_0} X \times I \xrightarrow{\text{pr}_1} X$  is the identity and gives you a splitting  $\text{Bun}_G(X) \xrightarrow{\text{pr}_1^*} \text{Bun}_G(X \times I) \xrightarrow{\text{in}_0^*} \text{Bun}_G(X)$ .

The rest of this lecture is devoted to proving surjectivity. There are various ways to do this. Husemoller does the general case; see [13,  $\S4.9$ ]. Steve Mitchell has a nice treatment in [28]. We will prove this when X is a CW-complex, by adapting CW methods to the equivariant situation.

To see the point of this approach, notice that the word "free" is used somewhat differently in the context of group actions than elsewhere. The left adjoint of the forgetful functor from G-spaces to spaces sends a space X to the G-space  $X \times G$  in which G acts, from the right, by (x,g)h = (x,gh). If G and X are discrete, any free action of G on X has this form. But this is not true topologically: just think of the antipodal action of G on the circle, for instance.

The condition that an action is principal is one way to demand that an action should be "locally" free in the stronger sense. G-CW complexes afford a different way.

#### G-CW-complexes

We would like to set up a theory of CW-complexes with an action of the group G. The relevant question is, "What is a G-cell?" There is a choice here. For us, and for the standard definition of a G-CW-complex, the right thing to say is that it is a G-space of the form

$$D^n \times H \backslash G$$
.

Here H is a closed subgroup of G, and  $H \setminus G$  is the orbit space of the action of H on G by left translation, viewed as a right G-space. The "boundary" of the G-cell  $D^n \times H \setminus G$  is just  $\partial D^n \times H \setminus G$  (with the usual convention that  $\partial D^0 = \emptyset$ ).

**Definition 18.1.** A relative G-CW-complex is a (right) G-space X with a filtration

$$A = X_{-1} \subseteq X_0 \subseteq X_1 \subseteq \cdots \subseteq X$$

by G-subspaces such that for all  $n \geq 0$  there exists a pushout square of G-spaces

$$\coprod \partial D_i^n \times H_i \backslash G \longrightarrow \coprod D_i^n \times H_i \backslash G$$

$$\downarrow \qquad \qquad \downarrow$$

$$X_{n-1} \longrightarrow X_n,$$

and X has the direct limit topology.

**Remarks 18.2.** A CW-complex is just a G-CW-complex for the trivial group G. If G is discrete, the skeleton filtration provides X with the structure of a CW-complex by neglect of the G-action. The subspace  $X_n$  is called the n-skeleton of X, even though if G is itself of positive dimension  $X_n$  may well have dimension larger than n.

If X is a G-CW-complex, then X/G inherits a CW-structure whose n-skeleton is given by  $(X/G)_n = X_n/G$ .

If  $P \downarrow X$  is a principal G-bundle, a CW-structure on X lifts to a G-CW-structure on P.

The action of G on a G-CW complex is principal if and only if all the isotropy groups are trivial. A good source for much of this is [18]; see for example Remark 2.8 there.

**Theorem 18.3** (Illman [14], Verona). If G is a compact Lie group and M a smooth manifold on which G acts by diffeomorphisms, then M admits a G-CW structure.

It's quite challenging in general to write down a G-CW structure even in simple cases, such as when the manifold is the unit sphere in an orthogonal representation of G. But sometimes it's easy. For example, the standard CW structure on  $\mathbb{R}P^{n-1}$ , with one k-cell for each k with  $0 \le k \le n-1$ , lifts to a  $C_2$ -CW structure on  $S^{n-1}$ . In it, the (k-1)-skeleton is  $S^{k-1}$ , for each  $k \le n$ , and there are two k-cells, given by the upper and lower hemisphere of  $S^k$ .

For another example, regard  $S^1$  as the complex numbers of magnitude 1, equipped with a  $C_2$  action by complex conjugation. This has a  $C_2$ -CW structure with 0-skeleton given by  $\{\pm 1\}$  a single free 1-cell.

#### Proof of *I*-invariance

Recall that our goal is to prove that every principal G-bundle  $p: P \to X \times I$  is pulled back from some principle G-bundle over X. Actually there's no choice here; since  $pr_1 \circ \text{in}_0 = 1$ , P must be pulled back from  $\text{in}_0^* P$ , that is, from the restriction of P to  $X \times 0$ .

For notational convenience, let us write  $Y = X \times I$ . Remember that we are assuming that X is a CW-complex. We will filter Y by subcomplexes, as follows. Let  $Y_0 = X \times 0$ ; in general, we define

$$Y_n = X_n \times 0 \cup X_{n-1} \times I$$
.

We may construct  $Y_n$  from  $Y_{n-1}$  via a pushout:

$$\coprod (\partial D^{n-1} \times I \cup D^{n-1} \times 0) \longrightarrow \coprod (D^{n-1} \times I)$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$Y_{n-1} \longrightarrow Y_n,$$

The restriction of P to  $Y_n$  is a principal bundle with total space

$$P_n = p^{-1}(Y_n) \,.$$

So  $P_0 \downarrow Y_0$  is just  $\operatorname{in}_0^* P \downarrow X$ .

We will show that P and  $\operatorname{pr}_1^*\operatorname{in}_0^*P$  are isomorphic over Y. For this it will be enough to construct an equivariant map  $P \to \operatorname{in}_0^*P$  covering the projection map  $\operatorname{pr}_1: Y \to X$ . We'll do this by inductively constructing compatible equivariant maps  $P_n \to P_0$  covering the composites  $Y_n \hookrightarrow Y \to X$ , starting with the identity map  $P_0 \to \operatorname{in}_0^*P$  covering the isomorphism  $Y_0 \to X$ .

We can build  $P_n$  from  $P_{n-1}$  by lifting the pushout construction of  $Y_n$  from  $Y_{n-1}$ :

$$\coprod (\partial D^{n-1} \times I \cup D^{n-1} \times 0) \times G \longrightarrow \coprod (D^{n-1} \times I) \times G$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$P_{n-1} \longrightarrow P_n$$

So to extend  $P_{n-1} \to P_0$  to  $P_n \to P_0$ , we must construct an equivariant map f in

$$\coprod (\partial D^{n-1} \times I \cup D^{n-1} \times 0) \longrightarrow \coprod (D^{n-1} \times I) \qquad (3.1)$$

$$\coprod (\partial D^{n-1} \times I \cup D^{n-1} \times 0) \times G \longrightarrow \coprod (D^{n-1} \times I) \times G$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$

covering the map  $Y_n \to Y_0$ . Since the action is free, it's enough to define f on  $D^{n-1} \times I$  for each cell, in such a way that the diagram

commutes, and then extend by equivariance. Since

$$(D^{n-1}\times I,\partial D^{n-1}\times I\cup D^{n-1}\times 0)\cong (D^{n-1}\times I,D^{n-1}\times 0)\,,$$

what we have is:

$$D^{n-1} \times 0 \longrightarrow P_0$$

$$\downarrow \qquad \qquad \downarrow$$

$$D^{n-1} \times I \longrightarrow Y_0$$

So the dotted map exists, since  $P_0 \to Y_0$  is a fibration!

#### The classifying space of a group 19

#### Representability

**Theorem 19.1.** Let G be a topological group and  $\xi: E \downarrow B$  a principal G-bundle such that E is weakly contractible (just as a space, forgetting the G-action). For any CW complex X, the map

$$[X,B] \to \operatorname{Bun}_G(X)$$

sending a map  $f: X \to B$  to the isomorphism class of  $f^*\xi$  is bijective.

This theorem as two parts: surjectivity and injectivity. Both are proved using the following proposition.

**Proposition 19.2.** Let E be a G-space that is weakly contractible as a space. Let (P, A) be a free relative G-CW complex. Then any equivariant map  $f: A \to E$  extends to an equivariant map  $P \to E$ , and this extension is unique up to an equivariant homotopy rel A.

*Proof.* Just do what comes naturally, after the experience of the proof of I-invariance!

Proof of Theorem 19.1. Surjectivity is immediate; take  $A = \emptyset$ .

To prove injectivity, let  $f_0, f_1: P \to E$  be two equivariant maps. We wish to show that they are homotopic by an equivariant homotopy, which thus descends to a homotopy between the induced maps on orbit spaces. Our data give an equivariant map  $A = P \times \partial I \to E$ , which we extend to an equivariant map from  $P \times I$  again using Proposition 19.2.

As usual, the representing object is unique up to isomorphism (in the homotopy category). Any choice of contractible free G-CW complex will be written EG, and its orbit space BG.  $EG \downarrow BG$  is the universal principal G-space, and BG classifies principal G-bundles.

What remains is to *construct* a *G*-CW complex that is both free and contractible. There are many ways to do this. One can use Brown Representability, for example.

When the group is discrete, say  $\pi$ , this amounts to finding a  $K(\pi,1)$ : the action of  $\pi$  on the universal cover is "properly discontinuous," which is to say principal. So we have a bunch of examples! For instance, let  $\pi = \pi_1(\Sigma)$  where  $\Sigma$  is any closed connected surface other than  $S^2$  and  $\mathbb{R}P^2$ . Then any principal  $\pi$ -bundle over any CW-complex B is pulled back from the universal cover of  $\Sigma$  under a unique homotopy class of maps  $B \to \Sigma$ .

If G is a compact Lie group – for example a finite group – there is a very geometric way to go about this, based on the following result.

**Theorem 19.3** (Peter-Weyl, [17, Corollary IV.4.22]). Any compact Lie group admits a finite-dimensional faithful unitary representation.

Clearly, if P is free as a G-space then it is also free as an H-space for any subgroup H of G. It's also the case that a if P is a principal G-space then it is also a principal H space, provided that H is a closed subgroup of G.

Combining these facts, we see that in order to construct a universal principal G action, for any compact Lie group G, it suffices to construct such a thing for the particular Lie groups U(n).

#### Gauss maps

Before we look for highly connected spaces on which U(n) acts, let's look at the case in which the base space is a compact Hausdorff space (for example a finite complex). In this case we can be more geometically explicit about the classifying map.

**Lemma 19.4.** Over a compact Hausdorff space, any vector bundle embeds in a trivial bundle.

*Proof.* Let  $\mathcal{U}$  be a trivializing open cover of the base B; since B is compact, we may assume that  $\mathcal{U}$  is finite, with, say, k elements  $U_1, \ldots, U_k$ . We agreed that our vector bundles would always be numerable, but we don't even have to mention this here since compact Hausdorff spaces are paracompact. So we can choose a partition of unity  $\{\phi_i\}$  subordinate to  $\mathcal{U}$ . By treating path components separately if need be, we may assume that our vector bundle  $\xi: E \downarrow B$  is an n-plane bundle, with projection p. The trivializations are fiberwise isomorphisms  $g_i: p^{-1}(U_i) \to \mathbb{R}^n$ . We can assemble these maps using the partition of unity, and define  $g: E \to (\mathbb{R}^n)^k$  as the unique map such that

$$\operatorname{pr}_{i} g(e) = \phi_{i}(p(e))g_{i}(e)$$
.

This is a fiberwise linear embedding. The map  $e \mapsto (p(e), g(e))$  is an embedding into the trivial bundle  $B \times \mathbb{R}^{nk}$ .

We can now use the standard inner product on  $\mathbb{R}^{nk}$  (or any other metric on  $B \times \mathbb{R}^{nk}$ ) to form the complement of E:

**Corollary 19.5.** Over a compact Hausdorff space, any vector bundle has a complement (i.e. a vector bundle  $\xi^{\perp}$  such that  $\xi \oplus \xi^{\perp}$  is trivial).

Suppose our vector bundle has fiber dimension n. The image of  $g(E_x)$  is an n-plane in  $\mathbb{R}^{nk}$ ; that is, an element  $f(x) \in Gr_n(\mathbb{R}^{nk})$ . We have produced a diagram

$$E \xrightarrow{g} E(\xi_{nk,n})$$

$$\xi \downarrow \qquad \qquad \downarrow$$

$$B \xrightarrow{f} \operatorname{Gr}_{n}(\mathbb{R}^{nk})$$

that expresses  $\xi$  as the pullback of the tautologous bundle  $\xi_{nk,n}$  under a map  $f: B \to Gr_n(\mathbb{R}^{nk})$ . This map f, covered by a bundle map, is a Gauss map for  $\xi$ .

#### The Grassmannian model

The frame bundle of the tautologous vector bundle over the Grassmannian  $\operatorname{Gr}_n(\mathbb{C}^{n+k})$  is the complex Stiefel manifold

$$V_n(\mathbb{C}^{n+k}) = \{\text{isometric embeddings } \mathbb{C}^n \hookrightarrow \mathbb{C}^{n+k}\}.$$

Ehresmann's Theorem 4.5 (for example) tells us that the projection map

$$V_n(\mathbb{C}^{n+k}) \downarrow \operatorname{Gr}_n(\mathbb{C}^{n+k})$$

sending an embedding to its image is a fiber bundle, so we have a principal U(n)-bundle.

How connected is this complex Stiefel variety? U(q) acts transitively on the unit sphere in  $\mathbb{C}^q$  and the isotropy group of the basis vector  $e_q$  is U(q-1) embedded in U(q) in the upper left corner. So we get a tower of fiber bundles with the indicated fibers:

$$S^{2k+1} \xrightarrow{\hspace{1cm}} U(n+k)/U(k) = V_n(\mathbb{C}^{n+k})$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$

The long exact homotopy sequence shows that  $V_n(\mathbb{C}^{n+k})$  is (2k)-connected. It's a "twisted product" of the spheres  $S^{2k+1}, S^{2k+3}, \dots, S^{2(n+k)-1}$ .

So forming the direct limit

$$V_n(\mathbb{C}^\infty) = \lim_{k \to \infty} V_n(\mathbb{C}^{n+k})$$

gives us a contractible CW complex with a principal action of U(n). The quotient map

$$V_n(\mathbb{C}^{\infty}) \downarrow V_n(\mathbb{C}^{\infty})/U(n) = \operatorname{Gr}_k(\mathbb{C}^{\infty})$$

provides us with a universal principal U(n) bundle, and hence also a universal n-plane bundle  $\xi_n$ . An element of  $E(\xi_n)$  is an n-dimensional subspace of the countably infinite dimensional vector space  $\mathbb{C}^{\infty}$ . This is the "infinite Grassmannian," and it deserves the symbol BU(n).

Dividing by a closed subgroup  $G \subseteq U(n)$  provides us with a model for BG. Of course sometimes we have more direct constructions; for example the same observations show that BO(n) is the space of n-planes in  $\mathbb{R}^{\infty}$ .

# 20 Simplicial sets and classifying spaces

We encountered simplicial sets at the very beginning of 18.905, as a step on the way to constructing singular homology. We will take this story up again here, briefly, because simplicial methods provide a way to organize the combinatorial data needed for the construction of classifying spaces and maps. It turns out that simplicial sets actually afford a completely combinatorial model for homotopy theory, though that is a story for another time.

#### Simplex category and nerve

The simplex category  $\Delta$  has as objects the finite totally ordered sets

$$[n] = \{0, 1, \dots, n\}, n \ge 0,$$

and as morphisms the order preserving maps. In particular the "coface" map  $d^i : [n] \to [n+1]$  is injection omitting i and the "codegeneracy" map  $s^i : [n] \to [n-1]$  is the surjection repeating i. Any order-preserving map can be written as the composite of these maps, and there are famous relations that they satisfy. They generate the category  $\Delta$ .

The standard (topological) simplex is the functor  $\Delta : \Delta \to \mathbf{Top}$  defined by sending [n] to the "standard n-simplex"  $\Delta^n$ , the convex hull of the standard basis vectors  $e_0, e_1, \ldots, e_n$  in  $\mathbb{R}^{n+1}$ . Order-preserving maps get sent to the affine extension of the map on basis vectors. So  $d^i$  includes the *i*th codimension 1 face, and  $s^i$  collapses onto a codimension 1 face.

**Definition 20.1.** Let  $\mathcal{C}$  be a category. Denote by  $s\mathcal{C}$  the category of *simplicial objects* in  $\mathcal{C}$ , i.e., the category  $\operatorname{Fun}(\Delta^{op},\mathcal{C})$ . We write  $X_n = X([n])$  for the "object of *n*-simplices."

A simplicial object can be defined by giving an object  $X_n \in \mathcal{C}$  for every  $n \geq 0$  along with maps  $d_i: X_{n+1} \to X_n$  and  $s_i: X_{n-1} \to X_n$  satisfying certain quadratic identities.

Our first example of a simplicial object is the singular simplicial set Sin(X) of a space X:

$$\operatorname{Sin}(X)_n = \operatorname{Sin}_n(X) = \operatorname{Top}(\Delta^n, X)$$
.

There is a categorical analogue of  $\Delta : \Delta \to \mathbf{Top}$ . After all, the ordered set [n] is a particularly simple small category:  $\Delta$  is a full subcategory of the category of small categories. So a small category C determines a simplicial set NC, the *nerve* of C, with

$$(NC)_n = N_n C = \operatorname{Fun}([n], C)$$
.

Thus  $N_0C$  is the set of objects of C;  $N_1C$  is the set of morphisms;  $d_0: N_1C \to N_0C$  sends a morphism to its target, and  $d_1: N_1C \to N_0C$  sends a morphism to its source;  $s_0: N_0C \to N_1C$ 

sends an object to its identity morphism. In general  $N_nC$  is the set of n-chains in C: composable sequences of n morphisms. For 0 < i < n, the face map  $d_i : N_nC \to N_{n-1}C$  forms the composite of two adjacent morphisms, while  $d_0$  omits the initial morphism and  $d_n$  omits the terminal morphism. Degeneracies interpose identity maps.

For example, a group G can be regarded as a small category, one with just one object. We denote it again by G. Then  $N_n G = G^n$ , and for 0 < i < n

$$d_i(g_1,\ldots,g_n) = (g_1,\ldots,g_{i-1},g_ig_{i+1},g_{i+2},\ldots,g_n).$$

while

$$d_0(g_1,\ldots,g_n)=(g_2,\ldots,g_n)\,,\quad d_n(g_1,\ldots,g_n)=(g_1,\ldots,g_{n-1})\,.$$

In general, the nerve construction allows us to regard small categories as a special class of simplicial sets. This attitude is the starting point for the theory of "quasi-categories" or " $\infty$ -categories," which constitute a somewhat more general class of simplicial sets.

#### Realization

The functor Sin transported us from spaces to simplicial sets. Milnor [24] described how to go the other way.

Let K be a simplicial set. The geometric realization |K| of K is

$$|K| = \left(\prod_{n>0} \Delta^n \times K_n\right)/\sim$$

where  $\sim$  is the equivalence relation defined by:

$$\Delta^m \times K_m \ni (v, \phi^* x) \sim (\phi_* v, x) \in \Delta^n \times K_n$$

for all maps  $\phi : [m] \to [n]$ .

**Example 20.2.** The equivalence relation is telling us to glue together simplices as dictated by the simplicial structure on K. To see this in action, let us look at  $\phi^* = d_i : K_{n+1} \to K_n$  and  $\phi_* = d^i : \Delta^n \to \Delta^{n+1}$ . In this case, the equivalence relation then says that  $(v, d_i x) \in \Delta^n \times K_n$  is equivalent to  $(d^i v, x) \in \Delta^{n+1} \times K_{n+1}$ . In other words: the *i*th face of the n+1 simplex labeled by x is identified with the n-simplex labeled by  $d_i x$ .

There's a similar picture for the degeneracies  $s^i$ , where the equivalence relation dictates that every element of the form  $(v, s_i x)$  is already represented by a simplex of lower dimension. A simplex in a simplicial set is "nondegenerate" if it is not in the image of a degeneracy map. Neglecting the topology, |X| is the disjoint union of (topological) simplex interiors labeled by the nondegenerate simplices of K.

**Example 20.3.** Let  $n \ge 0$ , and consider the simplicial set  $\Delta(-, [n])$ . This is called the "simplicial n-simplex", for good reason: Its geometric realization is canonically homeomorphic to the geometric n-simplex  $\Delta^n$ .

The realization |K| of a simplicial set has a naturally defined CW structure with

$$\operatorname{sk}_n|K| = \left(\prod_{k \le n} \Delta^k \times K_k\right)/\sim.$$

The face maps give the attaching maps; for more details, see [11, Proposition I.2.3]. This is a very combinatorial way to produce CW-complexes.

The geometric realization functor and the singular simplicial set functor form one of the most important and characteristic examples of an adjoint pair:

$$|-|: s\mathbf{Set} \rightleftarrows \mathbf{Top} : \mathbf{Sin}$$

The adjunction morphisms are easy to describe. For  $K \in s\mathbf{Set}$ , the unit for the adjunction  $K \to \operatorname{Sin}|K|$  sends  $x \in K_n$  to the map  $\Delta^n \to |K|$  defined by  $v \mapsto [(v,x)]$ .

To describe the counit, let X be a space. There is a continuous map  $\Delta^n \times \operatorname{Sin}_n(X) \to X$  given by  $(v, \sigma) \mapsto \sigma(v)$ . The equivalence relation defining  $|\operatorname{Sin}(X)|$  says precisely that the map factors through the dotted map in the following diagram:

$$|\operatorname{Sin}(X)| - - - \to X$$

$$\downarrow \qquad \qquad \downarrow$$

$$\coprod \Delta^n \times \operatorname{Sin}_n(X)$$

A theorem of Milnor [24] asserts that this map is a weak equivalence. This provides a functorial (and therefore spectacularly inefficient) CW approximation for any space.

This adjoint pair enjoys properties permitting the wholesale comparison of the homotopy theory of spaces with a combinatorially defined homotopy theory of simplicial sets. For more details, see for example [11].

#### Classifying spaces

Combining the two constructions we have just discussed, we can assign to any small category C a space

$$BC = |NC|$$
,

known as its classifying space. For example,  $B[n] = \Delta^n$ .

When C is a group, G, this space does in fact support a principal G-bundle. Before we explain that, let's look at the example of the group  $C_2$  of order 2. Write t for the non-identity element of  $C_2$ . There is just one non-degenerate n simplex in  $NC_2$  for any  $n \geq 0$ , namely  $(t, t, \ldots, t)$ . So the realization  $BC_2$  has a single n-cell for every n. Not bad, since it's supposed to be a CW structure on  $\mathbb{R}P^{\infty}$ ! Think about what the low skelata are. There's just one object, so  $(BC_2)_0 = *$ . There is just one nondegenerate 1-simplex,  $(t) \in C_2^1$ , so  $(BC_2)_1$  is a circle. There's just one nondegenerate 2-simplex,  $(t,t) \in C_2^2$ . Its faces are

$$d_0(t,t) = t$$
,  $d_1(t,t) = t^2 = 1$ ,  $d_2(t,t) = t$ .

The middle face has been identified with \* since it's degenerate, and we see a standard representation of  $\mathbb{R}P^2$  as a "lune" with its two edges identified. A similar analysis shows that  $(BC_2)_n = \mathbb{R}P^n$  for any n.

The projection maps  $C \times D \to C$  and  $C \times D \to D$  together induce a natural map

$$B(C \times D) \to BC \times BD$$
.

**Lemma 20.4.** The classifying space construction sends natural transformations to homotopies.

*Proof.* A natural transformation of functors  $C \to D$  is the same thing as a functor  $C \times [1] \to D$ . Since  $B[1] = \Delta^1$ , we can form the homotopy

$$BC \times \Delta^1 = BC \times B[1] \to B(C \times [1]) \to BD$$

Corollary 20.5. An adjoint pair induces a homotopy equivalence on classifying spaces.

Corollary 20.6. If C contains an initial object or a terminal object then BC is contractible.

*Proof.* Saying that  $o \in C$  is initial is saying that the inclusion  $o : [0] \to C$  is a left adjoint.

The following is a nice surprise, and requires the use of the compactly generated topology on the product.

**Theorem 20.7.** The natural map  $B(C \times D) \to BC \times BD$  is a homeomorphism.

Sketch of proof. This is nontrivial – not "categorical" – because it asserts that certain limits commute with certain colimits. The underlying fact is the Eilenberg-Zilber theorem, which gives a simplicial decomposition of  $\Delta^m \times \Delta^n$  and verifies the result when C = [m] and D = [n]. The general result follows since every simplicial set is a colimit of its "diagram of simplicies," and B respects colimits.

#### The translation groupoid

An action of G on a set X determines a category, a groupoid in fact, the "translation groupoid," which I will denote by GX. Its object set is X, and

$$GX(x,y) = \{ g \in G : gx = y \}$$

Composition comes from the group multiplication. This is a special case of the "Grothendieck construction."

When X = \* we recover the category G. Another case of interest is when X = G with G acting from the left by translation. The category GG is "unicursal": there is exactly one morphism between any two objects; every object is both initial and terminal. This implies that B(GG) is contractible.

The association

$$X \mapsto GX \mapsto N(GX) \mapsto |N(GX)| = B(GX)$$

is functorial. In particular, right multiplication by  $g \in G$  on the set G is equivariant with respect to the left action of G on it. Therefore G acts from the right on GG and hence on B(GG). This is a "free" action: no  $g \in G$  except the identity element fixes any simplex. This implies that B(GG) admits the structure of a free G-CW complex. It's not hard to verify that B(GG)/G = BG, so we have succeeded in constructing a functorial classifying space for any discrete group.

# 21 The Čech category and classifying maps

In this lecture I'll sketch a program due to Graeme Segal [33] (1941–, Oxford) for classifying principal G-bundles using the simplicial description of the classifying space proposed in the last lecture. That machinery admits an extension to general topological groups.

#### Top-enrichment

The Grassmannian model provides a classifying space for any compact Lie group. This includes finite discrete groups, which are also covered by the construction we just did. But we'd like to provide a construction to cover arbitrary topological groups.

**Definition 21.1.** A category *enriched in* **Top** is a category  $\mathcal{C}$  together with topologies on all the morphism sets, with the property that the composition maps are continuous.

The fact that **Top** is Cartesian closed provides us with an enrichment in **Top** of the category **Top** itself. A simpler (and smaller) example is given by any topological group (or monoid), regarded as a category with one object. Then a continuous action of G on a space X is just a functor  $G \to \mathbf{Top}$  that is continuous on hom spaces: a "topological functor."

The "nerve" construction now produces a simplicial space,

$$NG \in s$$
**Top**

associated to any topological group G. The formula for geometric realization still makes perfectly good sense for a simplicial space. (It won't generally be a CW complex anymore, but it does have a useful "skeleton" filtration given by assembling only simplices of dimension up to n.) Combining the two constructions, we may form the "classifying space"

$$BG = |NG|$$
.

This provides a functorially defined classifying space for topological groups.

#### Internal categories

To justify this language, we should produce a principal G-bundle over this space with contractible total space. This construction requires one further invasion of topology into category theory (or vice versa), namely, an "internal category" in **Top**.

**Definition 21.2. Top-**category is a pair of spaces  $C_0$  and  $C_1$  (to be thought of as the space of objects and the space of morphisms), together with continuous structure maps

source, target : 
$$C_1 \Rightarrow C_0$$
, identity :  $C_0 \rightarrow C_1$ 

composition: 
$$C_1 \times_{C_0} C_1 \to C_1$$

satisfying the axioms of a category.

If the object space is discrete, this is just an enrichment in **Top**. But there are other important examples. The simplest one is entirely determined by a space X: write cX for it. Just take it  $(cX)_0 = (cX)_1 = X$  with the "identity" map  $(cX)_0 \to (cX)_1$  given by the identity map.

The nerve and classifying space constructions carry over without change to this new setting.  $(NC)_0$  will no longer be discrete. The classifying space of cX is just X, for example. The observation that an adjoint pair yields a homotopy equivalence still holds.

Now suppose that G acts on a space X. The construction of GX carried out in the previous lecture provides us with a **Top**-category. Its classifying space maps to that of G, since X maps to a point.

**Proposition 21.3.** If G is a Lie group (and much more generally as well) the map  $B(GG) \to BG$  is a principal G-bundle, and B(GG) is contractible.

So this gives the classifying space of G, functorially in G. It's not hard to see that in fact

$$B(GX) = B(GG) \times_G X.$$

This degree of generality provides an inductive way to construct Eilenberg Mac Lane spaces explicitly. Begin with any discrete abelian group  $\pi$ . Apply the classifying space construction we've just described, to obtain a  $K(\pi,1)$ . Now being abelian is equivalent to the multiplication map  $\pi \times \pi \to \pi$  being a homomorphism. So we may leverage the functoriality of B, and the fact that it commutes with products, and form

$$B\pi \times B\pi \cong B(\pi \times \pi) \to B\pi$$
.

This provides on  $B\pi$  the structure of a topological abelian group. So we can apply B again:  $BB\pi = K(\pi, 2)$ . And so on:

$$B^n\pi = K(\pi, n)$$
.

#### Descent

Let  $\pi: Y \to X$  be a map of spaces. We can use it to define a **Top**-category, the "descent category" or "Čech category"  $\check{C}(\pi)$ , as follows. The space of objects is X, and the space of morphisms is  $Y \times_X Y$ . The structure maps are given by

$$\begin{split} \operatorname{id} &= \Delta: Y \to Y \times_X Y \quad y \mapsto (y,y) \\ \operatorname{source} &= \operatorname{pr}_1: Y \times_X Y \to Y \quad (y_1,y_2) \to y_1 \\ \operatorname{target} &= \operatorname{pr}_2: Y \times_X Y \to Y \quad (y_1,y_2) \to y_2 \\ \operatorname{composition} &: (Y \times_X Y) \times_Y (Y \times_X Y) \to Y \times_X Y \quad ((y_1,y_2),(y_2,y_3)) \mapsto (y_1,y_3) \,. \end{split}$$

There is a continuous functor

$$\check{\pi}: \check{C}(\pi) \to cX$$

determined by mapping the object space by the identity.

This construction is best understood from its motivating case. Suppose that  $\mathcal{U}$  is a cover of X and let

$$Y = \coprod_{U \in \mathcal{U}} U,$$

mapping to X by sending  $x \in U$  to  $x \in X$ . Then

$$Y \times_X Y = \coprod_{(U,V) \in \mathcal{U} \times \mathcal{U}} U \cap V,$$

the disjoint union of intersections of ordered pairs of elements of  $\mathcal{U}$ . Source and target just embed  $U \cap V$  into U and V.

In this case let's write  $\dot{C}(\mathcal{U})$  for the Čech category. In good cases we can recover X from  $\dot{C}(\mathcal{U})$ :

**Proposition 21.4.** If the open cover  $\mathcal{U}$  of X admits a subordinate partition of unity, then  $B\check{\pi}$ :  $B\check{C}(\mathcal{U}) \to X$  is a homotopy equivalence.

*Proof.* A sequence  $U_0, U_1, \dots U_n$  of elements of  $\mathcal{U}$  together with a point x in their intersection determines a chain  $(x \in U_0) \to (x \in U_1) \to \dots \to (x \in U_n)$  in the category  $\check{C}(\mathcal{U})$ . The counit of the realization-singular adjunction then gives a map

$$\epsilon: \Delta^n \times (U_0 \cap U_1 \cap \cdots \cap U_n) \to B\check{C}(\mathcal{U}).$$

Now let  $\{\phi_U : U \in \mathcal{U}\}$  be a partition of unity subordinate to  $\mathcal{U}$ , so that, for every  $x \in X$ ,  $\phi_U(x) = 0$  for all but finitely many  $U \in \mathcal{U}$ , and  $\sum_U \phi_U = 1$ . Pick a partial order on the elements of  $\mathcal{U}$  that is total on any subset with nonempty intersection. For any x let  $U_0(x), \ldots, U_{n(x)}(x)$  be the ordered sequence of elements of  $\mathcal{U}$  that contain x. Then define

$$X \to B\check{C}(\mathcal{U})$$

by sending

$$x \mapsto \epsilon((\phi_{U_0(x)}(x), \dots, \phi_{U_{n(x)}(x)}(x)), x).$$

It's not hard to check that this gives a well-defined map that is homotopy inverse to  $B\check{\pi}$ .

**Remark 21.5.** A final comment: In [33] Segal explains how to use these methods to construct a spectral sequence from this approach, one that includes the Serre spectral sequence and more generally the topological version of the Leray spectral sequence. We won't pursue that avenue in these lectures, though, but instead will describe two other approaches.

#### Transition functions, cocycles, and classifying maps

Now suppose that  $p: P \to B$  is a principal G-bundle. Pick a trivializing open cover  $\mathcal{U}$ , along with trivializations  $\varphi_U: p^{-1}U \to U \times G$  for  $U \in \mathcal{U}$ . These data determine a continuous functor

$$\check{C}(\mathcal{U}) \to G$$

as follows. There's no choice about behavior on objects. On morphisms, we use the "transition functions" associated with the given trivializations. So for  $U, V \in \mathcal{U}$ , the intersection  $U \cap V$  is a subspace of the space of morphisms in  $\check{C}(\mathcal{U})$ . We map it to G by

$$x \mapsto \varphi_V(x)\varphi_U(x)^{-1} \in G$$
.

The "cocycle condition" on these transition functions is the statement that together these maps constitute a functor.

Therefore we get a diagram

$$B\check{C}(\mathcal{U}) \longrightarrow BG$$

$$\downarrow \downarrow \simeq X$$

and one can check that the bundle  $EG \downarrow BG$  pulls back to  $P \downarrow X$  under the composite  $X \to BG$ .

# Chapter 4

# Spectral sequences and Serre classes

# 22 Why spectral sequences?

When we're solving a complicated problem, it's smart to break the problem into smaller pieces, solve them, and then put the pieces back together. Spectral sequences provide a powerful and flexible tool for bridging the "local to global" divide. They contain a lot of information, and can be queried in a variety of ways, so we will spend quite a bit of time getting to know them.

Homology is relatively computable precisely because you can break a space into smaller parts and then use Mayer-Vietoris to put the pieces back together. The long exact homology sequence (along with excision) is doing the same thing. We have seen how useful this is, in our identification of singular homology with the cellular homology of a CW complex. This puts a filtration on a space X, the skeleton filtration, and then makes use of the long exact sequences of the various pairs  $(X_n, X_{n-1})$ . Things are particularly simple here, since  $H_q(X_n, X_{n-1})$  is nonzero for only one value of q.

There are interesting filtrations that do not have that property. For example, suppose that  $p: E \to B$  is a fibration. A CW structure on B determines a filtration of E in which

$$F_s E = p^{-1}(\operatorname{Sk}_s B) .$$

Now the situation is more complicated: For each s we get a long exact sequence involving  $H_*(F_{s-1}E)$ ,  $H_*(F_sE)$ , and  $H_*(F_sE,F_{s-1}E)$ . The relevant structure of this tangle of long exact sequences is a "spectral sequence." It will describe the exact relationship between the homologies of the fiber, the base, and the total space.

We can get a somewhat better idea of how this might look by thinking of the case of a product projection,  $pr_2: B \times F \to B$ . Then the Künneth theorem is available. Let's assume that we are in the lucky situation in which there is a Künneth isomorphism, so that

$$H_*(B) \otimes H_*(F) \xrightarrow{\cong} H_*(E)$$
.

You should visualize this tensor product of graded modules by putting the the summand  $H_s(B) \otimes H_t(F)$  in degree n = s + t of the graded tensor product in position (s, t) in the first quadrant of the plane. Then the graded tensor product in degree n sums along each "total degree" n = s + t. Along the x-axis we see  $H_s(B) \otimes H_0(F)$ ; if F is path connected this is just the homology of the base space. Along the y-axis we see  $H_0(B) \otimes H_t(F) = H_t(F)$ ; if B is path-connected this is just the homology of the fiber. Cross-products of classes of these two types fill out the first quadrant.

The Künneth theorem can't generalize directly to nontrivial fibrations, though, because of examples like the Hopf fibration  $S^3 \to S^2$  with fiber  $S^1$ . The tensor product picture looks like this

| 2 |              |   |              |   |
|---|--------------|---|--------------|---|
| 1 | $\mathbf{z}$ |   | $\mathbf{Z}$ |   |
| 0 | $\mathbf{Z}$ |   | ${\bf z}$    |   |
|   | 0            | 1 | 2            | 3 |

and definitely gives the wrong answer!

What's going on here? We can represent a generating cycle for  $H_2(S^2)$  using a relative homeomorphism  $\sigma: (\Delta^2, \partial \Delta^2) \to (S^2, o)$ . If  $c_o$  represents the constant 2-simplex at the basepoint  $o \in S^2$ ,  $\sigma - c_o$  is a cycle representing a generator of  $H_2(S^2)$ . We can lift each of these simplices to simplices in  $S^3$ . But a lift of  $\sigma$  sends  $\partial \Delta^2$  to one of the fiber circles, and the lift of  $\sigma - c_o$  is no longer a cycle. Rather, its boundary is a cycle in the fiber over o, and it represents a generator for  $H_1(p^{-1}(o)) \cong H_1(S^1)$ .

This can be represented by adding an arrow to our picture.

This diagram now reflects several facts:  $H_1(S^1)$  maps to zero in  $H_1(S^3)$  (because the representing cycle of a generator becomes a boundary!); the image of  $H_2(S^3) \to H_2(S^2)$  is trivial (because no nonzero multiple of a generator of  $H_2(S^2)$  lifts to a cycle in  $S^3$ ); and the homology of  $S^3$  is left with just two generators, in dimensions 0 and 3.

In terms of the filtration on the total space  $S^3$ , the lifted chain lay in filtration 2 (saying nothing, since  $F_2S^3 = S^3$ ) but not in filtration 1. Its boundary lies two filtration degrees lower, in filtration 0. That is reflected in the differential moving two columns to the left.

The Hopf fibration  $S^7 \downarrow S^4$  (which you will study in homework) shows a similar effect. The boundary of the 4-dimensional chain lifting a generating cycle lies again in filtration 0, i.e. on the fiber. This represents a drop of filtration by 4, and is represented by a differential of bidegree (-4,3).

In every case, the total degree of the differential is of course -1.

The Künneth theorem provides a "first approximation" to the homology of the total space. It's generally too big, but never too small. Cancellation can occur: lifted cycles can have nontrivial boundaries, and cycles that were not boundaries in the fiber can become boundaries in the total space. More complicated cancellation can occur as well, involving the product classes.

#### Some history

Now I've told you almost the whole story of the Serre spectral sequence. A structure equivalent to a spectral sequence was devised by Jean Leray while he was in a prisoner of war camp during World War II. He discovered an elaborate structure determined in cohomology by a map of spaces. This was much more that just the functorial effect of the map. He was worked in cohomology, and in fact invented a new cohomology theory for the purpose. He restricted himself to locally compact spaces, but on the other hand he allowed *any* continuous map – no restriction to fibrations. This is the "Leray spectral sequence." It's typically developed today in the context of sheaf theory – another local-to-global tool invented by Leray at about the same time.

Leray called his structure an "anneau spectral": he was specifically interested in its multiplicative structure, and he saw an analogy between his analysis of the cohomology of the source of his map and the spectral decomposition of an operator. Before the war he had worked in analysis, especially the Navier-Stokes equation, and said that he found in algebraic topology a study that the Nazis would not be able to use in their war effort, in contrast to his expertise as a "mechanic."

It's fair to say that nobody other than Leray understood spectral sequences till well after the war was over. Henri Cartan was a leading figure in post-war mathematical reconstruction. He befriended Leray and helped him explain himself better. He set his students to thinking about Leray's ideas. One was named Jean-Louis Koszul, and it was Koszul who formulated the algebraic object we now call a spectral sequence. Another was Jean-Pierre Serre. Serre wanted to use this method to compute things in homotopy theory proper – homotopy groups, and the cohomology of Eilenberg Mac Lane spaces. He had to recast the theory to work with singular cohomology, on much more general spaces, but in return he considered only what we now call Serre fibrations. This restriction allowed a homotopy-invariant description of the spectral sequence. Leray had used "anneau spectral"; Cartan used "suite de Leray-Koszul"; and now Serre, in his thesis, brought the two parties together and coined the term "suite spectral". For more history see [22].

La science ne s'apprend pas: elle se comprend. Elle n'est pas lettre morte et les livres n'assurent pas sa pérennité: elle est une pensée vivante. Pour s'intéresser à elle, puis la

maîtriser, notre eprit doit, habilement guidé, la redécouvrir, de même que notre corps a dû revivre, dans le sien maternel, l'évolution qui créa notre espèce; non point tout ses détails, mais son schéma. Aussi n'y a-t-il qu'une façon efficace de faire acquérir par nos enfants les principes scientifiques qui sont stable, et les procédés techniques qui évoluent rapidement: c'est donner à nos enfants l'esprit de recherche. — Jean Leray [32]

# 23 The spectral sequence of a filtered complex

We are trying find ways to use a filtration of a space to compute the homology of that space. A simple example is given by the skeleton filtration of a CW complex. Let's recall how that goes. The singular chain complex receives a filtration by sub chain complexes by setting

$$F_s S_*(X) = S_*(\operatorname{Sk}_s X) .$$

We then pass to the quotient chain complexes

$$S_*(Sk_sX, Sk_{s-1}X) = F_sS_*(X)/F_{s-1}S_*(X)$$
.

The homology of the sth chain complex in this list vanishes except in dimension s, and the group of cellular s-chains is defined by

$$C_s(X) = H_s(\operatorname{Sk}_s X, \operatorname{Sk}_{s-1} X)$$
.

In turn, these groups together form a chain complex with differential

$$d: C_s(X) = H_s(\operatorname{Sk}_s X, \operatorname{Sk}_{s-1} X) \xrightarrow{\partial} H_{s-1}(\operatorname{Sk}_{s-1} X) \to H_{s-1}(\operatorname{Sk}_{s-1} X, \operatorname{Sk}_{s-2} X) = C_{s-1}(X).$$

Then  $d^2 = 0$  since it factors through two consecutive maps in the long exact sequence of the pair  $(Sk_{s-1}X, Sk_{s-2}X)$ .

We want to think about filtrations

$$\cdots \subset F_{s-1}X \subset F_sX \subset F_{s+1}X \subset \cdots X$$

of a space X that don't behave so simply. But the starting point is the same: filter the singular complex accordingly:

$$F_{\mathfrak{s}}S_{\mathfrak{s}}(X) = S_{\mathfrak{s}}(F_{\mathfrak{s}}X) \subset S_{\mathfrak{s}}(X)$$

This is a filtered (chain) complex.

To abstract a bit, suppose we are given a chain complex  $C_*$  whose homology we wish to compute by means of a filtration

$$\cdots F_{s-1}C_* \subseteq F_sC_* \subseteq F_{s+1}C_* \subseteq \cdots$$

by sub chain complexes. Note that at this point we are allowing the filtration to extend in both directions. And do we need to suppose that the intersection is zero, nor that the union is all of  $C_*$ . (And  $C_*$  might be nonzero in negative degrees, as well.)

The first step is to form the quotient chain complexes.

$$\operatorname{gr}_{s} C_{*} = F_{s} C_{*} / F_{s-1} C_{*}$$
.

This is a sequence of chain complexes, a *graded* object in the category of chain complexes, and is termed the "associated graded" complex.

What is the relationship between the homologies of these quotient chain complexes and the homology of  $C_*$  itself?

We'll set up grading conventions following the example of the filtration by preimages of a skeleton filtration under a fibration, as described in the previous lecture: name the coordinates in the plane (s,t), with the s-axis horizontal and the t-axis vertical. So s will be the filtration degree, and s+t will be the total topological dimension. t is the "complementary degree." This suggests that we should put  $\operatorname{gr}_s C_{s+t}$  in bidegree (s,t). Here then is a standard notation:

$$E_{s,t}^0 = \operatorname{gr}_s C_{s+t} = F_s C_{s+t} / F_{s-1} C_{s+t}$$

The differential then has bidegree (0, -1). In parallel with the superscript in " $E^0$ ," this differential is written  $d^0$ .

Next we pass to homology. Let's use the notation

$$E_{s,t}^1 = H_{s,t}(E_{*,*}^0, d^0)$$

for the homology of  $E^0$ . This in turn supports a differential. In the case of the skeleton filtration, this is the differential in the cellular chain complex. The definition in general is identical:

$$d^{1}: E_{s,t}^{1} = H_{s+t}(F_{s}/F_{s-1}) \xrightarrow{\partial} H_{s+t-1}(F_{s-1}) \to H_{s+t-1}(F_{s-1}/F_{s-2}) = E_{s-1,t}^{1}.$$

Thus  $d^1$  has bidegree (-1,0). Of course we will write

$$E_{s,t}^2 = H_{s,t}(E_{*,*}^1, d^1)$$
.

In the case of the skeleton filtration,  $E_{s,t}^1 = 0$  unless t = 0, and the fact that cellular homology equals singular homology is the assertion that

$$E_{s,0}^2 = H_s(X) .$$

In general the situation is more complicated because  $E^1$  may be nonzero off the s-axis. So now the magic begins. The claim is that the bigraded group  $E_{*,*}^2$  in turn supports a natural differential, written, of course,  $d^2$ , this time of bidegree (-2,1); that this pattern continues ad infinitum; and that in the end you get (essentially)  $H_*(C_*)$ . In fact the proof we gave last term that cellular homology agrees with singular homology is no more than a degenerate case of this fact.

Here's the general picture.

**Theorem 23.1.** A filtered complex  $F_*C_*$  determines a natural spectral sequence, consisting of

- bigraded abelian groups  $E_{s,t}^r$  for  $r \geq 0$ ,
- differentials  $d^r: E^r_{s,t} \to E^r_{s-r,t+r-1}$  for  $r \ge 0$ , and
- isomorphisms  $E_{s,t}^{r+1} \cong H_{s,t}(E_{*,*}^r, d^r)$  for  $r \geq 0$ ,

such that for r = 0, 1, 2,  $(E_{*,*}^r, d^r)$  is as described above, and that under further hypotheses "converges" to  $H_*(C_*)$ .

Here are further conditions that will suffice to guarantee that the spectral sequence is actually computing  $H_*(C_*)$ .

**Definition 23.2.** The filtered complex  $F_*C_*$  is first quadrant if

- $F_{-1}C_* = 0$ ,
- $H_n(\operatorname{gr}_s C_*) = 0$  for n < s, and
- $C_* = \bigcup F_s C_*$ .

Under these conditions,  $E^1$  is zero outside of the first quadrant, and so all the higher "pages"  $E^r$  have the same property. It's called a "first quadrant spectral sequence."

The differentials all have total degree -1, but their slopes vary. The longest possibly nonero differential emanating from (s,t) is

$$d^s: E^s_{s,t} \to E^s_{0,t+s-1}$$
,

and the longest differential attacking (s, t) is

$$d^{t+1}: E^{t+1}_{s+t+1,0} \to E^{t+1}_{s,t}$$
.

What this says is that for any value of (s,t), the groups  $E_{s,t}^r$  stabilize for large r. That stable value is written

$$E_{s,t}^{\infty}$$

Here's the rest of Theorem 23.1. It uses the natural filtration on  $H_*(C_*)$  given by

$$F_s H_n(C_*) = \operatorname{im}(H_n(F_s C_*) \to H_n(C_*))$$
.

**Theorem 23.3.** The spectral sequence of a first quadrant filtered complex converges to  $H_*(C_*)$ , in the sense that

$$F_{-1}H_*(C_*) = 0$$
,  $\bigcup_s F_sH_*(C_*) = H_*(C_*)$ ,

and for each s, t there is a natural isomorphism

$$E_{s,t}^{\infty} \cong \operatorname{gr}_{s} H_{s+t}(C_{*})$$
.

In symbols, we may write (for any  $r \geq 0$ )

$$E^r_* \Longrightarrow H_*(C_*)$$
,

or, if you want to be explicit about the degrees and which degree is the filtration degree,

$$E_{s,t}^r \Longrightarrow H_{s+t}(C_*)$$
.

Notice right off that this contains the fact that cellular homology computes singular homology: In the spectral sequence associated to the skeleton filtration,

$$E_{s,t}^{0} = S_{s+t}(\operatorname{Sk}_{s}X, \operatorname{Sk}_{s-1}X)$$

$$E_{s,t}^{1} = H_{s+t}(\operatorname{Sk}_{s}X, \operatorname{Sk}_{s-1}X) = \begin{cases} C_{s}(X) & \text{if } t = 0\\ 0 & \text{otherwise} \end{cases}$$

$$E_{s,t}^{2} = \begin{cases} H_{s}^{\operatorname{cell}}(X) & \text{if } t = 0\\ 0 & \text{otherwise} \end{cases}$$

In a given total degree n there is only one nonzero group left by  $E^2$ , namely  $E_{n,0}^2 = H_n^{\text{cell}}(X)$ . Thus no further differentials are possible:

$$E_{*,*}^2 = E_{*,*}^{\infty}$$
.

The convergence theorem then implies that

$$\operatorname{gr}_s H_n(X) = \begin{cases} E_{n,0}^{\infty} = H_n^{\operatorname{cell}}(X) & \text{if } s = n \\ 0 & \text{otherwise} \end{cases}$$

So the filtration of  $H_n(X)$  changes only once:

$$0 = \dots = F_{n-1}H_n(X) \subseteq F_nH_n(X) = \dots = H_n(X),$$

and

$$F_n H_n(X)/F_{n-1} H_n(X) = E_{n,0}^{\infty} = H_n^{\text{cell}}(X)$$
.

So

$$H_n(X) = H_n^{\text{cell}}(X)$$
.

Before we explain how to construct the spectral sequence, let me point out one corollary at the present level of generality.

**Corollary 23.4.** Let  $f: C \to D$  be a map of first quadrant filtered chain complexes. If  $E_{*,*}^r(f)$  is an isomorphism for some r, then  $f_*: H_*(C) \to H_*(D)$  is an isomorphism.

Proof. The map  $E^r(f)$  is an isomorphism which is also also a chain map, i.e., it is compatible with the differential  $d^r$ . It follows that  $E^{r+1}(f)$  is an isomorphism. By induction, we conclude that  $E_{s,t}^{\infty}(f)$  is an isomorphism for all s,t. By Theorem 23.3, the map  $\operatorname{gr}_s(f_*): \operatorname{gr}_s H_*(C) \to \operatorname{gr}_s H(D)$  is an isomorphism. Now the conditions in Definition 23.2) let us use induction and the five lemma to conclude the proof.

#### Direct construction

In a later lecture I will describe a structure known as an "exact couple" that provides a construction of a spectral sequence that is both clean and flexible. But the direct construction from a filtered complex has its virtues as well. Here it is. The detailed computations are annoying but straightforward.

Define the following subspaces of  $E_{s,t}^0 = F_s C_{s+t} / F_{s-1} C_{s+t}$ , for  $r \ge 1$ .

$$\begin{split} Z^r_{s,t} = & \left\{c: \exists \, x \in c \text{ such that } dx \in F_{s-r}C_{s+t-1} \right\}, \\ B^r_{s,t} = & \left\{c: \exists \, y \in F_{s+r-1}C_{s+t+1} \text{ such that } dy \in c \right\}. \end{split}$$

So an "r-cycle" is a class that admits a representative whose boundary is r filtrations smaller; the larger r is the closer the class is to containing an actual cycle. An "r-boundary" is a class admitting a representative that is a boundary of an element allowed to lie in filtration degree r-1 stages larger. When r=1, these are exactly the cycles and boundaries with respect to the differential  $d^0$  on  $E^0_{**}$ .

We have inclusions

$$B^1_{*,*} \subseteq B^2_{*,*} \subseteq \dots \subseteq Z^2_{*,*} \subseteq Z^1_{*,*}$$

and define

$$E_{s,t}^r = Z_{s,t}^r / B_{s,t}^r .$$

These pages are successively smaller groups of cycles modulo successively larger subgroups of boundaries. The differential  $d^r$  is of course induced from the differential d in  $C_*$ , and  $H_{s,t}(E^r_{*,*},d^r) \cong E^{r+1}_{s,t}$ . In the first quadrant situation, the r-boundaries and the r-cycles stabilize to

$$Z_{s,t}^{\infty} = \{c : \exists x \in c \text{ such that } dx = 0\},$$
  
$$B_{s,t}^{\infty} = \{c : \exists y \in C_{s+t+1} \text{ such that } dy \in c\}.$$

The quotient,  $E_{s,t}^{\infty}$ , is exactly  $F_sH_{s+t}(C_{*,*})/F_{s-1}H_{s+t}(C_{*,*})$ .

## 24 Serre spectral sequence

Fix a fibration  $p: E \to B$ , with B a CW-complex. We obtain a filtration on E by taking the preimage of the s-skeleton of B:  $E_s = p^{-1} Sk_s B$ . This induces a filtration on  $S_*(E)$  given by

$$F_s S_*(E) = S_*(p^{-1}\operatorname{Sk}_s(B)) \subseteq S_*(E)$$
.

The spectral sequence resulting from Theorem 23.1 is the Serre spectral sequence.

This was not Serre's construction [35], by the way; he did not employ a CW structure at all, but rather worked directly with a singular theory – but rather than simplices, he used cubes, which are well adapted to the study of bundles since a product of cubes is again a cube. We will describe a variant of Serre's construction in a later lecture, one that is technically easier to work with and that makes manifest important multiplicative features of the spectral sequence. We will not try to dot all the i's in the construction we describe in this lecture, and for simplicity we'll imagine that p is actually a fiber bundle.

In this spectral sequence,

$$E_{s,t}^1 = H_{s+t}(F_s E, F_{s-1} E)$$
.

Pick a cell structure

$$\coprod_{i \in \Sigma_s} S_i^{s-1} \longrightarrow \coprod_{i \in \Sigma_s} D_i^s$$

$$\downarrow \qquad \qquad \downarrow$$

$$B_{s-1} \longrightarrow B_s$$

Let  $\alpha: D_i^s \to B_s$  be characteristic map, and let  $F_i$  be the fiber over the center of  $e_i^s$  in B. The pullback of  $E \downarrow B$  under  $\alpha$  is a trivial fibration since  $D_i^s$  is contractible. Now

$$\coprod_{i \in \Sigma_s} (D_i^s, S_i^{s-1}) \times F_i \to (F_s E, F_{s-1} E)$$

is a relative homeomorphism, so by excision

$$E_{s,t}^{1} = H_{s+t}(F_{s}E, F_{s-1}E) = \bigoplus_{i \in \Sigma_{s}} H_{s+t}((D_{i}^{s}, S_{i}^{s-1}) \times F_{i}) = \bigoplus_{i \in \Sigma_{s}} H_{t}(F_{i}).$$

In particular, this filtration satisfies the requirements of Definition 23.2, since  $H_t(F_i) = 0$  for t < 0. We have a convergent spectral sequence. It remains to work out what  $d^1$  is. I won't do this in detail but I'll tell you how it turns out.

It's important to appreciate that the fibers  $F_i$  vary from one cell to the next. If B is not path-connected, these fibers don't even have to be of the same homotopy type. If B is path connected,

then they do, but the homotopy equivalence is determined by a homotopy class of paths from one center to the other and so is not canonical. If B is not simply connected, the functor

$$p^{-1}(-):\Pi_1(B)\to \operatorname{Ho}(\mathbf{Top})$$

may not be constant. But at least we see that the fibration defines functors

$$H_t(p^{-1}(-)): \Pi_1(B) \to \mathbf{Ab} \text{ with } b \mapsto H_t(p^{-1}(b)).$$

This is, or determines, a local coefficient system. We encountered these before, in our exploration of orientability. There a "local coefficient system" was a covering space with continuously varying abelian group structures on the fibers. If the space is path connected and semi-locally simply connected, there is a universal cover, and giving a covering space is equivalent to giving an action of the fundamental group on a set. We can free this equivalence from dependence on path connectedness (and choice of basepoint) by speaking of functors from the fundamental groupoid to abelian groups. CW complexes are locally contractible [12, e.g. Appendix on CW complexes, Proposition 4] and so this equivalence applies in our case.

If this local system is in fact constant (for example if B is simply connected) the differential in  $E^1$  is none other than the cellular differential in

$$C_*(B; H_t(F))$$

(where we write F for any fiber), and so

$$E_{s,t}^2 = H_s(B; H_t(F)).$$

This is the case we will mostly be concerned with. But the general case is the same, with the understanding that we mean homology of B with coefficients in the local system  $H_t(p^{-1}(-))$ .

Here's a base-point dependent way of thinking of how to compute homology or cohomology of a space with coefficients in a local system. We assume that our space X is path-connected and nice enough to admit a universal cover  $\widetilde{X}$ . Pick a basepoint \*. Giving a local coefficient system is the same as giving a  $\mathbb{Z}[\pi_1(X,*)]$ -module. Write M for both. The fundamental group acts on  $\widetilde{X}$  and so on its singular chain complex. Now we can say that

$$H_*(X;M) = H_*(S_*(\widetilde{X}) \otimes_{\mathbb{Z}[\pi_1(X,*)]} M), \quad H^*(X;M) = H^*(\text{Hom}_{\mathbb{Z}[\pi_1(X,*)]}(S_*(\widetilde{X}),M).$$

Here's the general result.

**Theorem 24.1.** Let  $p: E \to B$  be a Serre fibration, R a commutative ring, and M an R-module. There is a first quadrant spectral sequence of R-modules with

$$E_{s,t}^2 = H_s(B; H_t(p^{-1}(-); M))$$

that converges to  $H_*(E; M)$ . It is natural from  $E^2$  on for maps of fibrations.

This theorem expresses one important perspective on spectral sequences: They can serve to implement a "local-to-global" strategy. A fiber bundle is locally a product. The spectral sequence explains how the "local" (in the base) homology of E gets integrated to produce the "global" homology of E itself.

#### Loops on spheres

Here's a first application of the Serre spectral sequence: a computation of the homology of the space of pointed loops on a sphere,  $\Omega S^n$ . It is the fiber of the fibration  $PS^n \to S^n$ , where  $PS^n$  is the space of pointed maps  $(S^n)^I_*$ . The space  $PS^n$  is contractible, by the spaghetti move.

It is often said that the Serre spectral sequence is designed to compute the homology of the total space starting with the homologies of the fiber and of the base. This is not true! Rather, it establishes a relationship between these three homologies, one that can be used in many different ways. Here we know the homology of the total space (since  $PS^n$  is contractible) and of the base, and we want to know the homology of the fiber.

The case n=1 is special:  $S^1$  is a Eilenberg Mac Lane space  $K(\mathbb{Z},1)$ , so  $\Omega S^1$  is weakly equivalent to the discrete space  $\mathbb{Z}$ .

So suppose  $n \geq 2$ . Then the base is simply connected and torsion-free, so in the Serre spectral sequence

$$E_{s,t}^2 = H_s(S^n; H_t(\Omega S^n)) = H_s(S^n) \otimes H_t(\Omega S^n).$$

Here's a picture, for n=4.

As you can see, the only possible nonzero differentials are of the form

$$d^n: E_{n,t}^n \to E_{0,t+n-1}^n$$
.

So 
$$E_{*,*}^2 = E_{*,*}^{n-1}$$
 and  $E_{*,*}^{n+1} = E_{*,*}^{\infty}$ .

The spectral sequence converges to  $H_*(PS^n)$ , which is  $\mathbb{Z}$  in dimension 0 and 0 elsewhere. This immediately implies that

$$H_t(\Omega S^n) = 0$$
 for  $0 < t < n-1$ 

since nothing could kill these groups on the fiber.

The fiber is path connected,  $H_0(\Omega S^n) = \mathbb{Z}$ , so we know the bottom row in  $E^2$ .  $E_{n,0}^2$  must die. It can't be killed by being hit by a differential, since everything below the s-axis is trivial (and also because everything to its right is trivial). So it must die by virtue of  $d^n$  being injective on it. In fact that differential must be an isomorphism, since if it fails to surject onto  $E_{0,n-1}^n$  there would be something left in  $E_{0,n-1}^{n+1} = E_{0,n-1}^{\infty}$ , and it would contribute nontrivially to  $H_{n-1}(PS^n) = 0$ .

This language of mortal combat gives extra meaning to the "spectral" in "spectral sequence."

25. EXACT COUPLES 83

So  $H_{n-1}(\Omega S^n) = \mathbb{Z}$ . This feeds back into the spectral sequence:  $E_{n,n-1}^2 = \mathbb{Z}$ . Now that class has to kill or be killed. It can't be killed because everything to its right is zero, so  $d^n$  must be injective on it. And it must surject onto  $E_{0,2(n-1)}^n$ , for the same reason as before.

This establishes the inductive step. We have shown that all the  $d^n$ 's are isomorphisms (except the ones involving  $E_{0,0}^n$ ), and established:

Proposition 24.2. Let  $n \geq 2$ . Then

$$H_t(\Omega S^n) = \begin{cases} \mathbb{Z} & if \quad (n-1)|t \ge 0\\ 0 & otherwise. \end{cases}$$

#### **Evenness**

Sometimes it's easy to see that a spectral sequence collapses. For example, suppose that

$$E_{s\,t}^r = 0$$
 unless both s and t are even.

Then all differentials in  $E^r$  and beyond must vanish, because they all have total degree -1. Actually all that is needed for this argument is that  $E^r_{s,t} = 0$  unless s+t is even. There may still be extension problems, though.

# 25 Exact couples

Today I would like to show you a very simple piece of linear algebra called an *exact couple*. A filtered complex gives rise to an exact couple, and an exact couple gives rise to a spectral sequence. Exact couples were discovered by Bill Massey (1920–2017, Professor at Yale) independently of the French development of spectral sequences.

**Definition 25.1.** An exact couple is a diagram of abelian groups

that is exact at each node.

As jkjk = 0, the map  $jk : E \to E$  is a differential, denoted d. An exact couple determines a "derived couple"

where

$$A' = \operatorname{im}(i)$$
 and  $E' = H(E, d)$ .

Iterating this procedure, we get a sequence of exact couples

If we impose appropriate gradings, the "E" terms will form a spectral sequence.

We have to explain the maps in the derived couple.

i': this is just i restricted to  $A' = \operatorname{im}(i)$ . Obviously i carries  $\operatorname{im}(i)$  into  $\operatorname{im}(i)$ .

j': Note that ja is a cycle in E: dja = jkja = 0. Define

$$j'(ia) = [ja].$$

To see that this is well defined, we need to see that if ia = 0 then ja is a boundary. By exactness there is an element  $e \in E$  such that ke = a. Then de = jke = ja.

k': Let  $e \in E$  be a cycle. Since 0 = de = jke,  $ke \in \text{im}(i) = A'$  by exactness. Define

$$k'([e]) = ke$$
.

To see that this is well defined, suppose that e = de'. Then ke = kde' = kjke' = 0.

Exercise 25.2. Check that these maps indeed yield an exact couple.

#### Gradings

Now suppose we are given a filtered complex. It will define an exact couple in which A is given by the homology groups of the filtration degrees and E is given by the homology groups of the associated quotient chain complexes.

In order to accommodate this example we need to add gradings – in fact, bigradings. Here's the relevant definition.

**Definition 25.3.** An exact couple of bigraded abelian groups is of type r if the structure maps have the following bidegrees.

$$||i|| = (1, -1)$$
  
 $||j|| = (0, 0)$   
 $||k|| = (-r, r - 1)$ 

It's clear from this that ||d|| = ||jk|| = (-r, r-1), the bidegree appropriate for the rth stage of a spectral sequence. We should specify the gradings on the abelian groups in the derived couple. Define  $A'_{s,t}$  to sit in the factorization

$$A_{s,t} \xrightarrow{i} A_{s+1,t-1}$$

$$A'_{s,t}$$

and  $E'_{s,t} = H_{s,t}(E_{*,*})$ . Then if  $e \in E_{s,t}$ ,  $ke \in A_{s-r,t+r-1}$ , but if e is a cycle then ke lies in the subgroup  $A'_{s-r-1,t-r}$ , so ||k'|| = (r+1,-r): the derived couple is of type (r+1).

Given a filtered complex

$$\cdots \subseteq F_{s-1}C_* \subseteq F_sC_* \subseteq F_{s+1}C_* \subseteq \cdots$$

define

$$A_{s,t}^1 = H_{s+t}(F_sC_*)$$
 ,  $E_{s,t}^1 = H_{s+t}(\operatorname{gr}_sC_*)$ .

25. EXACT COUPLES 85

This agrees with our earlier use of the notation  $E_{s,t}^1$ . The structure maps are given in the obvious way:  $i^1$  is induced by the inclusion of one filtration degree into the next (and has bidegree (1,-1));  $j^1$  is induced from the quotient map (and has bidegree (0,0)); and  $k^1$  is the boundary homomorphism in the homology long exact sequence (and has bidegree (-1,0)).

Given any exact couple of type 1,  $(A^1, E^1)$ , we'll write

$$A^r = (A^1)^{(r-1)}, \quad E^r = (E^1)^{(r-1)}$$

for the (r-1) times derived exact couple, which is of type r.

#### **Differentials**

An exact couple can be unfolded in a series of linked exact triangles, like this (taking r = 1 for concreteness, and omitting the second index):

The triangles marked with  $\circ$  are exact; the lower ones commute, and define  $d^1$ .

This image is useful in understanding the differentials in the associated spectral sequence. Start with an element  $x \in E^1_s$ . Suppose it's a cycle. Then its image  $kx \in A^1_{s-1}$  is killed by j and hence pulls back under i, to, say,  $x_1 \in A^1_{s-2}$ . The image in  $E^1_{s-2}$  of  $x_1$  under j is a representative for  $d^2[x]$ . Suppose that  $d^2[x] = 0$ . Then we can improve the lift  $x_1$  to one that pulls back one step further, to, say,  $x_2 \in A^1_{s-3}$ ; and  $d^3[x] = [jx_2]$ . This pattern continues. The further you can pull kx back, the longer x survives in the spectral sequence. If it pulls back forever, then you appeal to a convergence condition to conclude that kx = 0, and x therefore lifts under j to an element  $\overline{x}$  in  $A^1_s$ . The direct limit

$$L = \lim_{\longrightarrow} (\cdots \to A_s^1 \to A_{s+1}^1 \to A_{s+2}^1 \to \cdots)$$

is generally what one is interested in (it's  $H_*(C_*)$  in the first quadrant filtered complex situation, for example) and one may say that "x survives to" the image of  $\overline{x}$  in L.

#### Other examples

Topology is inhabited by many spectral sequences that do not arise from a filtered complex. For example, if you have a tower of fibrations, you get an exact couple by linking together the homotopy long exact sequences of the individual fibrations. Well, almost. The problem is what happens at the bottom: groups may not be abelian, or even groups; and even if they are, you may not be able to guarantee exactness at  $\pi_0$ . For example, form the Whitehead tower of a space Y and map some

well-pointed space X into it. We get a new tower of fibrations

The homotopy groups of the spaces on the right form the  $E^1$ -term, and are easy to compute:

$$\pi_n(K(\pi_p(Y), p)_*^X) = [S^n \wedge X, K(\pi_p(Y), p)]_* = [X, K(\pi_p(Y), p - n)]_* = \overline{H}^{p-n}(X; \pi_p(Y)).$$

Insofar as this is a spectral sequence at all, the  $E^1$  term is given by

$$E_{s,t}^{1} = \overline{H}^{-2s-t}(X; \pi_{-s}(Y, *)).$$

It's concentrated between the lines t = -s and t = -2s, in the second quadrant of the plane.

This picture is very closely related to obstruction theory, and indeed obstruction theory can be set up using it. Its failings as a spectral sequence can be repaired in various ways I won't discuss. If it can be repaired, the spectral sequence converges to  $\pi_*(Y_*^X)$ , or wants to.

For another example, there are many "generalized homology theories" – sequences of functors satisfying the Eilenberg-Steenrod axioms other than the dimension axiom – K-theory, bordism theories, and many others. Write  $R_*(-)$  for any such theory. The skeleton filtration construction of the Serre spectral sequence can be applied to compute the R-homology of the total space of a fibration  $p: E \to B$ : To construct the exact couple, all you need is the long exact sequence of a pair, which is available in R-homology. You find for each t a local coefficient system  $R_t(p^{-1}(-))$ , and

$$E_{s,t}^2 = H_s(B; R_t(p^{-1}(-))) \Longrightarrow_s R_{s+t}(E)$$

Even the case  $p: E \xrightarrow{\equiv} B$  is interesting: then the local coefficient system is guaranteed to be trivial, and we get

$$E_{s,t}^2 = H_s(E; R_t(*)) \Longrightarrow_s R_{s+t}(E)$$
.

This is the "Atiyah-Hirzebruch spectral sequence," and it provides a powerful tool for computing these generalized homology theories.

Both of these spectral sequences require us to move out of the first quadrant setting. The Atiyah-Hirzebruch-Serre spectral sequence can fill up the right half-plane.

# The Gysin sequence, edge homomorphisms, and the transgression

Now we'll discuss a general situation, a common one, that displays many of the ways in which the Serre spectral sequence relates the homology groups of fiber, total space, and base.

Suppose  $p: E \to B$  is a fibration; assume the base is path-connected, and that the fiber has homology isomorphic to that of  $S^{n-1}$  with n > 1. Let us use the Serre spectral sequence to determine how the homologies of E and of B are related. We will assume that this "spherical fibration" is orientable, and choose an orientation. This means that the local coefficient system  $H_{n-1}(p^{-1}(-))$  is trivial, and provided with a trivialization: a preferred generator of  $H_{n-1}(p^{-1}(b))$  that varies continuously with  $b \in B$ . For example, we might be looking at  $S^{2k-1} \downarrow \mathbb{C}P^{k-1}$  or  $S^{4k-1} \downarrow \mathbb{H}P^{k-1}$ , or the complement of the zero-section in the tangent bundle of an oriented n-manifold.

There are just two nonzero rows in this spectral sequence. This means that there's just one possibly nonzero differential:

$$E_{*,*}^2 = E_{*,*}^3 = \dots = E_{*,*}^n$$
;

then a differential

$$d^n: E_{s,0}^n \to E_{s-n,n-1}^n$$

occurs; and then

$$E_{*,*}^{n+1} = \dots = E_{*,*}^{\infty}$$
.

Taking homology with respect to  $d^n$  gives the top row of

$$0 \longrightarrow E_{s,0}^{\infty} \longrightarrow E_{s,0}^{n} \xrightarrow{d^{n}} E_{s-n,n-1}^{n} \longrightarrow E_{s-n,n-1}^{\infty} \longrightarrow 0$$

$$\downarrow = \qquad \qquad \downarrow = \qquad \qquad \downarrow$$

$$H_{s}(B) \longrightarrow H_{s-n}(B)$$

To explain the rest of this diagram, path connectedness of  $S^{n-1}$  gives the isomorphism

$$E_{s,0}^n = E_{s,0}^2 = H_s(B) \,,$$

and the oriention determines

$$E_{s-n,n-1}^n = E_{s-n,n-1}^2 = H_{s-n}(B; H_{n-1}(S^{n-1})) = H_{s-n}(B)$$
.

Now look at total degree n. The filtration of  $H_n(E)$  changes at most twice, with associated quotients given by the  $E^{\infty}$  term: so there is a short exact sequence

$$0 \to E_{s-n+1,n-1}^{\infty} \to H_s(E) \to E_{s,0}^{\infty} \to 0$$
.

These two families of exact sequences splice together to give a long exact sequence:

**Proposition 26.1.** Let  $p: E \to B$  be a Serre fibration whose fiber is a homology (n-1)-sphere, and assume it is oriented (so the local coefficient system  $H_{n-1}(p^{-1}(-))$  is trivialized). There is a naturally associated long exact sequence, the Gysin sequence

$$\cdots \to H_{s+1}(B) \to H_{s-n+1}(B) \to H_s(E) \xrightarrow{p_*} H_s(B) \to H_{s-n}(B) \to \cdots$$

(Werner Gysin (1915-1998) described this in his thesis at ETH under Heinz Hopf.) The only part of this that we have not proven is that the middle map here is in fact the map induced by the projection p. That's the story of "edge homomorphisms," which we take up next.

First, though, and example. The Gysin sequence of the  $S^1$ -bundle  $S^{\infty} \downarrow \mathbb{C}P^{\infty}$  looks like this:

Working inductively up the tower, you compute what we know:

$$H_n(\mathbb{C}P^{\infty}) = \begin{cases} \mathbb{Z} & \text{if } 2|n \ge 0\\ 0 & \text{otherwise} . \end{cases}$$

#### Edge homomorphisms

In the Serre spectral sequence for the fibration  $p: E \to B$ , what can we say about the evolution of the bottom edge, or of the left edge? Let's assume that the fiber is path connected and that the local coefficient system is trivial, so in

$$E_{s,t}^2 = H_s(B; H_t(F)) \Longrightarrow H_{s+t}(E)$$

the bottom edge is canonically isomorphic to  $H_*(B)$ .

Being at the bottom, no nontrivial differentials can ever hit it. So the successive process of taking homology will be a succession of taking kernels:

$$E_{n,0}^{r+1} = \ker(d^r : E_{n,0}^r \to E_{n-r,r-1}^r)$$
.

Of course when r > s things quiet down. So

$$E_{n,0}^2 \supseteq E_{n,0}^3 \supseteq \cdots \supseteq E_{n,0}^{n+1} = E_{n,0}^{\infty}$$

Now  $H_n(E)$  enters the picture, along with its filtration. The whole of  $H_n(E)$  is already hit by  $H_n(p^{-1}Sk_nB)$ . This is confirmed by the fact that the associated graded  $gr_sH_n(E)=E_{s,n-s}^{\infty}$  vanishes for s>n. So  $F_nH_n(E)=H_n(E)$ .

Putting all this together, we get a map

$$H_n(E) = F_n H_n(E) \rightarrow \operatorname{gr}_n H_n(E) = E_{n,0}^{\infty} = E_{n,0}^{n+1} \hookrightarrow E_{n,0}^n \hookrightarrow \cdots \hookrightarrow E_{n,0}^2 = H_n(B)$$
.

This composite is an *edge homomorphism* for the spectral sequence. It's something you can define for any first quadrant filtered complex. In the Serre spectral sequence case, it has a direct interpretation:

**Proposition 26.2.** This edge homomorphism coincides with the map  $p_*: H_n(E) \to H_n(B)$ .

This explains the role of the differentials off the bottom row of the spectral sequence. They are obstructions to classes lifting to the homology of the total space. This reflects the intuition we tried to develop several lectures ago. The image of  $p_*: H_n(E) \to H_n(B)$  is precisely the intersection (so to speak) of the kernels of the differentials coming off of  $E_{n,0}^2$ .

Before we prove this, let's notice that there is a dual picture for the vertical axis. Now all differentials leaving  $E^r_{0,n}$  are trivial, so we get surjections

$$E_{0,n}^2 \to E_{0,n}^3 \to \cdots \to E_{0,n}^{n+2} = E_{0,n}^\infty$$
.

On the other hand, the smallest nonzero filtration degree of  $H_n(E)$  is  $F_0H_n(E)$ . Thus we have another "edge homomorphism,"

$$H_n(F) = E_{0,n}^2 \twoheadrightarrow E_{0,n}^3 \twoheadrightarrow \cdots \twoheadrightarrow E_{0,n}^{n+2} = E_{0,n}^\infty = F_0 H_n(E) \hookrightarrow H_n(E)$$
.

**Proposition 26.3.** This edge homomorphism coincides with the map  $i_*: H_n(F) \to H_n(E)$  induced by the inclusion of the fiber.

So the kernel of  $i_*$  is union of the images (so to speak) of the differentials coming into  $E_{0,n}^2$ . These represent chains in E which serve as null-homologies of cycles in F.

Proof of Propositions 26.2 and 26.3. The map of fibrations

induces a commutative diagram in which the top and bottom arrows are edge homomorphisms:

$$H_n(E) \longrightarrow H_n(B)$$

$$\downarrow^{p_*} \qquad \qquad \downarrow^{(1_B)_*}$$

$$H_n(B) \longrightarrow H_n(B).$$

So we just need to check that the bottom edge homomorphism associated to the identity fibration  $1_B: B \to B$  is the identity map  $H_n(B) \to H_n(B)$ . This I leave to you.

The proof of Proposition 26.3 is similar.

Very often you begin with some homomorphism, and you are interested in whether it is an isomorphism, or how it can be repaired to become an isomorphism. If you can write it as an edge homomorphism in a spectral sequence, then you can regard the spectral sequence as measuring how far from being an isomorphism your map is; it provides the reasons why the map fails to be either injective or surjective.

#### Transgression

There is a third aspect of the Serre spectral sequence that deserves attention, namely, the differential going clear across the spectral sequence, all the way from base to fiber. We'll study it in case the fiber and the base are both path connected and the local coefficient systems  $H_t(p^{-1}(-))$  are trivial. Write F for the fiber.

The differentials

$$d^n: E_{n,0}^n \to E_{0,n-1}^n$$

are known as transgressions, and an element of  $E_{n,0}^2 = H_n(B)$  that survives to  $E_{n,0}^n$  is said to be transgressive. The first one is a homomorphism

$$d^2: H_2(B) \to H_1(F)$$
,

but after that  $d^n$  is merely an additive relation between  $H_n(B)$  and  $H_{n-1}(F)$ : It has a domain of definition

$$E_{n,0}^s \subseteq E_{n,0}^2 = H_n(B)$$

and indeterminacy

$$\ker(H_{n-1}(F) = E_{0,n-1}^2 \to E_{0,n-1}^n)$$
.

Let me expand on what I mean by an additive relation. A good reference is [19, II §6].

**Definition 26.4.** An additive relation  $R: A \rightharpoonup B$  is a subgroup  $R \subseteq A \times B$ .

For example the graph of a homomorphism  $A \to B$  is an additive relation. Additive relations compose in the evident way: the composite of  $R: A \to B$  with  $S: B \to C$  is

$$\{(a,c): \exists b \in B \text{ such that } (a,b) \in R \text{ and } (b,c) \in S\} \subseteq A \times C$$
.

Every additive relation has a "converse,"

$$R^{-1} = \{(b, a) : (a, b) \in R\} : B \to A.$$

An additive relation has a domain

$$D = \{a \in A : \exists b \in B \text{ such that } (a, b) \in R\} \subseteq A$$

and an indeterminancy

$$I = \{b \in B : (0, b) \in R\},\$$

and determines a homomorphism

$$f: D \to B/I$$

by

$$f(a) = b + I$$
 for  $b \in B$  such that  $(a, b) \in R$ .

Conversely, such a triple (D, I, f) determines an additive relation,

$$R = \{(a, b) : a \in D \text{ and } b \in f(a)\}.$$

An additive relation is defined as a subspace of  $A \times B$ , but any "span"

determines one by taking the image of the resulting map  $C \to A \times B$ .

End of digression. We have the transgression  $d^n: H_n(B) \to H_{n-1}(F)$ . Another such additive relation is determined by the span

$$H_n(B) = H_n(B, *) \stackrel{p_*}{\longleftarrow} H_n(E, F) \stackrel{\partial}{\longrightarrow} H_{n-1}(F)$$
.

**Proposition 26.5.** These two linear relations coincide.

Proof sketch. This phenomenon is actually how we began our discussion of spectral sequences. Let  $x \in H_n(B)$ . Since n > 0 we can just as well regard it as a class in  $H_n(B,*)$ . Represent it by a cycle  $c \in Z_n(B,*)$ . (In the Hopf fibration case this simplifies the representative by making the constant cycle optional.) Lift it to a chain in the total space E. In general, this chain will not be a cycle (consider the Hopf fibration). The differentials record this boundary; let us recall the explicit construction of the differential in §??. Saying that the class x survives to  $E^n$  is the same as saying that we can find a lift to a chain c in E, with  $dc \in S_{n-1}(F)$ , that is, to a relative cycle in  $S_{n-1}(E,F)$ . Then  $d^n(x)$  is represented by the class  $[dc] \in H_{n-1}(F)$ . This is precisely the transgression.

# 27 The Serre exact sequence and the Hurewicz theorem

#### Serre exact sequence

Suppose  $\pi: E \to B$  is a fibration over a path-connected base. Pick a point  $* \in E$ , use its image  $* \in B$  as a basepoint in B, write  $F = \pi^{-1}(*) \subseteq E$  for the fiber over \*, and equip it with the point  $* \in E$  as a basepoint. Suppose also that F is path connected.

Pick a coefficient ring R. Everything we've done works perfectly with coefficients in R – all abelian groups in sight come equipped with R-module structures. Let's continue to suppress the coefficient ring from the notation. Suppose that the low-dimensional homology of both fiber and base vanishes:

$$H_s(B) = 0$$
 for  $0 < s < p$   
 $H_t(F) = 0$  for  $0 < t < q$ .

Assume that  $\pi_1(B, *)$  act trivially on  $H_*(F)$ , so the Serre spectral sequence (now with coefficients in R!) takes the form

$$E_{s,t}^2 = H_s(B; H_t(F)) \Longrightarrow H_{s+t}(E)$$
.

Our assumptions imply that  $E_{0,0}^2 = R$  is all alone; otherwise everything with s < p vanishes and everything with t < q vanishes.

For a while, the only possibly nonzero differentials are the transgressions

$$d^s: E^s_{s,0} \to E^s_{0,s-1}$$
.

The result, in this range, is an exact sequence

$$0 \to E_{s,0}^{\infty} \to H_s(B) \xrightarrow{d^s} H_{s-1}(F) \to E_{0,s-1}^{\infty} \to 0$$
.

Again, in this range, these end terms are the only two possibly nonzero associated quotients in  $H_n(E)$  – there is a short exact sequence

$$0 \to E_{0,n}^{\infty} \to H_n(E) \to E_{n,0}^{\infty} \to 0$$
.

- and splicing things together we arrive again at a long exact sequence

$$H_{p+q-1}(F) \xrightarrow{i_*} H_{p+q-1}(E) \xrightarrow{p_*} H_{p+q-1}(B)$$

$$H_{p+q-2}(F) \xrightarrow{i_*} H_{p+q-2}(E) \xrightarrow{p_*} H_{p+q-2}(B)$$

$$H_{p+q-3}(F) \xrightarrow{i_*} \cdots$$

This is the Serre exact sequence: in this range of dimensions homology and homotopy behave the same! We can't extend it further to the left because the kernel of the edge homomorphism  $H_{p+q-1}(F) \to H_{p+q-1}(E)$  has two sources: the image of  $d^p: E^p_{p,q} \to E^p_{0,p+q-1}$ , and the image of  $d^{p+q}: E^{p+q}_{p+q,0} \to E^{p+q}_{0,p+q-1}$ .

#### Comparison with homotopy

The Serre exact sequence mimics the homotopy long exact sequence of the fibration.

**Proposition 27.1.** The Hurewicz map participates in a commutative ladder

$$\cdots \longrightarrow \pi_{p+q-1}(F) \xrightarrow{i_*} \pi_{p+q-1}(E) \xrightarrow{\pi_*} \pi_{p+q-1}(B) \longrightarrow \pi_{p+q-2}(F) \longrightarrow \cdots$$

$$\downarrow h \qquad \qquad \downarrow h \qquad \qquad \downarrow h$$

$$H_{p+q-1}(F) \xrightarrow{i_*} H_{p+q-1}(E) \xrightarrow{\pi_*} H_{p+q-1}(B) \longrightarrow H_{p+q-2}(F) \longrightarrow \cdots$$

*Proof.* The left two squares commutes by naturality of the Hurewicz map. The right square commutes because, according to our geometric interpretation of the transgression, both boundary maps arise in the same way:

$$\pi_n(B) \stackrel{\cong}{\longleftarrow} \pi_n(E, F) \xrightarrow{\partial} \pi_{n-1}(F)$$

$$\downarrow^h \qquad \qquad \downarrow^h \qquad \qquad \downarrow^h$$

$$H_n(B) \stackrel{\cong}{\longleftarrow} H_n(E, F) \xrightarrow{\partial} H_{n-1}(F)$$

The isomorphism  $\pi_n(E, F) \to \pi_n(B)$  is Lemma 9.7.

Let us now specialize to the case of the path-loop fibration

$$\Omega X \to PX \to X$$

where X is a simply-connected pointed space. The coefficient system is trivial. Suppose that in fact  $\overline{H}_i(X) = 0$  for i < n. Since the spectral sequence converges to the homology of a point, we find that  $\overline{H}_i(\Omega X) = 0$  for i < n-1. The Serre exact sequence, or direct use of the spectral sequence as in the computation of  $H_*(\Omega S^n)$ , shows this:

**Lemma 27.2.** Let X be an (n-1)-connected pointed space. The transgression relation provides an isomorphism

$$\overline{H}_i(X) \to \overline{H}_{i-1}(\Omega X)$$

for i < 2n - 2.

For example, if X is simply connected, we get a commutative diagram

$$\pi_2(X) \xrightarrow{\cong} \pi_1(\Omega X)$$

$$\downarrow \qquad \qquad \downarrow$$

$$H_2(X) \xrightarrow{\cong} H_1(\Omega X)$$

Since  $\Omega X$  is an H-space its fundamental group is abelian, so Poincaré's theorem shows that the Hurewicz homomorphism on the right is an isomorphism. Therefore the map on the left is. This is a case of the Hurewicz theorem! In fact, continuing by induction we discover a proof of the general case of the Hurewicz theorem.

**Theorem 27.3** (Hurewicz). Let  $n \geq 1$ . Suppose X is a pointed space that is (n-1)-connected:  $\pi_i(X) = 0$  for i < n. Then  $\overline{H}_i(X) = 0$  for i < n and the Hurewicz map  $\pi_n(X)^{ab} \to H_n(X)$  is an isomorphism.

#### Going relative

Any topological concept seems to get more useful if you can extend it to a relative form. So let (B, A) be a pair of spaces. To make the construction for the Serre spectral sequence that we proposed earlier work, we should assume that this is a relative CW complex. Suppose that  $E \downarrow B$  is a fibration. The pullback or restriction

$$E_A \longrightarrow E$$

$$\downarrow \qquad \qquad \downarrow$$

$$A \longrightarrow B$$

provides us with a "fibration pair"  $(E, E_A)$ . Suppose that B is path-connected and A nonempty, pick a basepoint  $* \in A$ , write F for the fiber of  $E \downarrow B$  over \* (which is of course also the fiber of  $E|_A \downarrow A$  over \*), and suppose that  $\pi_1(B,*)$  acts trivially on  $H_*(F)$ . With these assumptions, pulling back skelata of B rel A yields the relative Serre spectral sequence

$$E_{s,t}^2 = H_s(B, A; H_t(F)) \Longrightarrow H_{s+t}(E, E_A)$$
.

Let's apply this right away to prove a relative version of the Hurewicz theorem. We will develop conditions under which

$$h: \pi_i(X,A) \to H_i(X,A)$$

is an isomorphism for all  $i \leq n$ . We will of course assume that X is path connected and that A is nonempty, which together imply that  $H_0(X,A) = 0$ . Since  $\pi_1(X,A)$  is in general only a pointed set let's begin by assuming that it vanishes. This implies that A is also path connected and that  $\pi_1(A) \to \pi_1(X)$  is surjective. The induced map on abelianizations is then also surjective, so by Poincaré's theorem  $H_1(A) \to H_1(X)$  is surjective and so  $H_1(X,A) = 0$ .

Moving up to the next dimension, we may hope that  $h: \pi_2(X,A) \to H_2(X,A)$  is then an isomorphism, but  $\pi_2(X,A)$  is not necessarily abelian so this can't be right in general. This can be fixed – in fact if we kill the action of  $\pi_1(A)$  on  $\pi_2(X,A)$  it becomes abelian and the resulting homomorphism to  $H_2(X,A)$  is an isomorphism (see [37, Ch. 5, Sec. 7]). But we'll be assuming that  $\pi_1(X) = 0$  in a minute anyway, so let's just go ahead now and assume that  $\pi_1(A) = 0$ . The long exact homotopy sequence then shows that  $\pi_2(X,A)$  is a quotient of  $\pi_2(X)$  and so is abelian. We'll show that  $h: \pi_2(X,A) \to H_2(X,A)$  is then an isomorphism.

We will use the fact (Homework for Lecture 47) that the projection map induces a isomorphism

$$\pi_n(E, E_A) \xrightarrow{\cong} \pi_n(B, A)$$

for any  $n \ge 1$ . In particular, let F be the homotopy fiber of the inclusion map  $A \hookrightarrow X$ : that is, the pullback in

$$F \longrightarrow PX$$

$$\downarrow \qquad \qquad \downarrow$$

$$A \longrightarrow X.$$

The path space PX is contractible, so from the long exact homotopy sequence for the pair (PX, F) we find that the maps on the top row of the following commutative diagram are isomorphisms.

$$\pi_{n-1}(F) \stackrel{\cong}{\longleftarrow} \pi_n(PX, F) \stackrel{\cong}{\longrightarrow} \pi_n(X, A)$$

$$\downarrow^h \qquad \qquad \downarrow^h \qquad \qquad \downarrow^h$$

$$\overline{H}_{n-1}(F) \stackrel{\cong}{\longleftarrow} H_n(PX, F) \stackrel{p_*}{\longrightarrow} H_n(X, A).$$

Returning to our n=2 case, the left arrow is an isomorphism by Poincaré's theorem, since F is path connected and by our assumptions its fundamental group is abelian. What remains in this case then is to show that homology behaves like homotopy, in the sense that  $H_2(PX, F) \to H_2(X, A)$  is an isomorphism.

In general, if we assume that, for some  $n \geq 3$ ,  $\pi_i(X, A) = 0$  for i < n, then the absolute case of the Hurewicz theorem implies that the left Hurewicz homomorphism is an isomorphism, and we are left wanting to show that  $H_n(PX, F) \to H_n(X, A)$  is an isomorphism.

For this we can appeal to the relative Serre spectral sequence for the fibration pair  $(PX, F) \downarrow (X, A)$ . It takes the form

$$E_{s,t}^2 = H_s(X, A; H_t(\Omega X)) \Longrightarrow_s H_{s+t}(PX, F) = \overline{H}_{s+t-1}(F).$$

provided the coefficient system is trivial. Since  $H_0(\Omega X) = \mathbb{Z}[\pi_1(X)]$ , we are pretty much forced to assume that X is simply connected if we want simple coefficients.

The universal coefficient theorem gives us a handle on the  $E^2$  term:

$$0 \to H_s(X, A) \otimes H_t(\Omega X) \to H_s(X, A; H_t(\Omega X)) \to \operatorname{Tor}(H_{s-1}(X, A), H_t(\Omega X)) \to 0$$
.

Now is the time to think about using induction on n: This will allow us to use the assumption that  $\pi_i(X,A) = 0$  for i < n-1 to conclude that  $H_i(X,A) = 0$  for i < n-1 and that  $\pi_{n-1}(X,A) \stackrel{\cong}{\to} H_{n-1}(X,A)$ ; but we have the additional assumption that  $\pi_{n-1}(X,A) = 0$  as well, so  $H_{n-1}(X,A) = 0$  too. The induction begins with the case n = 2.

So when s < n both end terms vanish, and the entire spectral sequence is concentrated along and to the right of s = n.

We glean two facts from this vanishing result: First,  $H_i(PX, F) = 0$  for i < n, so  $\overline{H}_i(F) = 0$  for i < n - 1. We knew this already from the absolute Hurewicz theorem.

The second fact is that  $E_{n,0}^2$  survives intact to  $E_{n,0}^{\infty}$ : Nothing can hit it, and it can hit nothing. This is also the only nonzero group along the total degree line n, so (using what we know about the bottom edge homomorphism) the projection map induces an isomorphism  $H_n(PX, F) \to H_n(X, A)$ . This is a spectral sequence "corner argument."

Putting this together:

**Theorem 27.4** (Relative Hurewicz theorem). Let X be a space and A a subspace. Assume both of them are simply connected, and let  $n \geq 2$ . Assume that  $\pi_i(X, A) = 0$  for  $2 \leq i < n$ . Then  $H_i(X, A) = 0$  for i < n, and the relative Hurewicz map

$$\pi_n(X,A) \to H_n(X,A)$$

is an isomorphism.

With more care (see [37, Ch. 5, Sec. 7]) you can avoid the simple connectivity assumption. However, with it in place, you get a converse statement: Suppose that both X and A are simply connected, let  $n \geq 2$ , and assume that  $H_q(X, A) = 0$  for q < n. Simple connectivity of X implies that  $\pi_1(X, A)$  is trivial, so we have the hypotheses of the relative Hurewicz theorem with n = 2, and conclude from  $H_2(X, A) = 0$  that  $\pi_2(X, A) = 0$ . Continuing in this manner, we have the

Corollary 27.5. Let X be a space and A a subspace. Assume both of them are simply connected, and let  $n \geq 2$ . Assume that  $H_i(X, A) = 0$  for  $2 \leq i < n$ . Then  $\pi_i(X, A) = 0$  for i < n, and the relative Hurewicz map

$$\pi_n(X,A) \to H_n(X,A)$$

is an isomorphism.

By replacing a general map by a relative CW complex, up to weak homotopy, we find the following important corollary (which we state without the simple connectivity assumptions needed to apply our work so far).

**Corollary 27.6** (Whitehead theorem). Let  $f: X \to Y$  be a map of path connected spaces and let  $n \geq 1$ . If  $f_*: \pi_q(X) \to \pi_q(Y)$  is an isomorphism for q < n and an epimorphism for q = n then  $f_*: H_q(X) \to H_q(Y)$  is an isomorphism for q < n and an epimorphism for q = n. The converse holds if both X and Y are simply connected.

Taking  $n = \infty$  gives the further corollary:

**Corollary 27.7.** Any weak equivalence induces a isomorphism in homology. Conversely, if X and Y are simply connected then any homology isomorphism  $f: X \to Y$  is a weak equivalence.

Combining this with "Whitehead's little theorem," we conclude that if a map between simply connected CW complexes induces an isomorphism in homology then it is a homotopy equivalence.

# 28 Double complexes and the Dress spectral sequence

A certain very rigid way of constructing a filtered complex occurs quite frequently – and, indeed, the Serre or even the Leray spectral sequence can be constructed in this way. It leads to an easy treatment of the multiplicative properties of the Serre spectral sequence (as well as, in due course, an account of the behavior of Steenrod operations in it).

#### Double complexes

A double complex is a bigraded abelian group  $A = A_{*,*}$  together with differentials  $d_h : A_{s,t} \to A_{s-1,t}$  and  $d_v : A_{s,t} \to A_{s,t-1}$  that commute:

$$d_{\nu}d_{h}=d_{h}d_{\nu}$$
.

For our purposes we might as well assume that  $A_{s,t}$  is "first quadrant":

$$A_{s,t} = 0$$
 unless  $s > 0$  and  $t > 0$ .

An example is provided by the tensor product of two chain complexes  $C_*$  and  $D_*$ : define

$$A_{s,t} = C_s \otimes D_t$$
,  $d_h(a \otimes b) = da \otimes b$ ,  $d_v(a \otimes b) = a \otimes db$ .

The graded tensor product is then the "total complex," which in general is the chain complex tA given by

$$(tA)_n = \bigoplus_{s+t=n} A_{s,t}$$

with differential determined by sending  $a \in A_{s,t}$  to

$$da = d_h a + (-1)^s d_v a.$$

Then

$$d^{2}a = d(d_{h}a + (-1)^{s}d_{v}a) = (d_{h}^{2}a + (-1)^{s}d_{h}d_{v}a) + (-1)^{s-1}(d_{v}d_{h}a + (-1)^{s}d_{v}^{2}a) = 0.$$

Define a filtration on the chain complex tA as follows:

$$F_p(tA)_n = \bigoplus_{s+t=n, \, s < p} A_{s,t} \subseteq (tA)_n.$$

Let's compute the low pages of the resulting spectral sequence. For a start,

$$E_{s,t}^0 = \operatorname{gr}_s(tA)_{s+t} = (F_s/F_{s-1})_{s+t} = A_{s,t}$$
.

The differential in this associated graded object is determined by the vertical differential in A:

$$d^0a = \pm d_va$$
.

Then

$$E_{s,t}^1 = H_{s,t}(E^0, d^0) = H_{s,t}(A; d_v),$$

which we might write as  $H_{s,t}^v(A)$ .

Now  $d^1$  is the part of the differential d that decreases s by 1: for a  $d_v$  cycle in  $A^{s,t}$ ,

$$d^1[a] = [d_h a].$$

So

$$E_{s,t}^2 = H_{s,t}^h(H^v(A)) \Longrightarrow_s H_{s+t}(tA)$$
.

But we can do something else as well. A double complex A can be "transposed" to produce a new double complex  $A^{\mathsf{T}}$  with

$$A_{t,s}^{\mathsf{T}} = A_{s,t}$$

and for  $a \in A_{t,s}^{\mathsf{T}}$ 

$$d_b^{\mathsf{T}}(a) = (-1)^s d_v a$$
 ,  $d_v^{\mathsf{T}}(a) = (-1)^t d_h a$ .

When I set the signs up like that, then

$$tA^{\mathsf{T}} \cong tA$$

as complexes. The double complex  $A^{\mathsf{T}}$  has its own filtration and its own spectral sequence,

$${}^{\mathsf{T}}E^2_{t,s} = H^v_{t,s}(H^h(A)) \Longrightarrow_{t} H_{s+t}(tA) \,,$$

converging to the same thing.

If  $A_{*,*}$  has a compatible multiplication – and we'll let you decide what that means – then the associated spectral sequences are multiplicative, as can easily be seen from the direct construction given in §??.

#### Dress spectral sequence

Andreas Dress [7] (1938–, Bielefeld) developed the following variation of the approach to the Serre spectral sequence originally employed by Serre himself. He proposed to model a general fibration – indeed, a general map – by the product projections

$$\operatorname{pr}_1:\Delta^s\times\Delta^t\to\Delta^s$$
.

He used these models to form a "singular" construction associated to any map  $\pi: E \to B$ .

$$\operatorname{Sin}_{s,t}(\pi) = \left\{ (f, \sigma) : \begin{array}{c} \Delta^s \times \Delta^t \xrightarrow{f} E \\ \downarrow^{\operatorname{pr}_1} & \downarrow_{\pi} \\ \Delta^s \xrightarrow{\sigma} B \end{array} \right\}.$$

Since  $\Delta^s \times \Delta^t \downarrow \Delta^s$  is surjective,  $\sigma$  is determined by f. Commutativity says that the map  $\sigma$  is "fiberwise."

This construction sends any map  $\pi: E \to B$  to a functor

$$\operatorname{Sin}_{*,*}(\pi): \boldsymbol{\Delta}^{op} \times \boldsymbol{\Delta}^{op} \to \operatorname{Set},$$

a "bisimplicial set."

Continuing to imitate the construction of singular homology, we will next apply the free R-module functor to this, to get a bisimplicial R-module  $RSin_{*,*}(\pi)$ . The final step is to define boundary maps by taking alternating sums of the face maps. This provides us with a double complex, that I will write  $S_{*,*}(\pi)$ .

There are two associated spectral sequences. One of them is a singular homology version of the Leray spectral sequence, and specializes to the Serre spectral sequence in case  $\pi$  is a fibration. The other serves to identify what the first one converges to. I will sketch the arguments.

Let's compute the spectral sequence attached to the transposed double complex first. For this, observe that an element of  $\operatorname{Sin}_{s,t}(\pi)$  may be regarded as a pair of dotted arrows in the commutative diagram

$$\Delta^{s} - \hat{f} > E^{\Delta^{t}}$$

$$\downarrow \sigma \qquad \qquad \downarrow \pi$$

$$R \xrightarrow{c} R^{\Delta^{t}}$$

where c denotes the inclusion of the constant maps. If we form the pullback  $E'_t$  in

$$E'_t \longrightarrow E^{\Delta^t}$$

$$\downarrow^{\pi}$$

$$B \stackrel{c}{\longrightarrow} B^{\Delta^t}$$

this is saying that  $\operatorname{Sin}_{s,t}(\pi) = \operatorname{Sin}_s(E'_t)$ , so

$$S_{s,t}(\pi) = S_s(E'_t)$$
.

But the map  $E'_t \to E^{\Delta^t}$  is a weak equivalence (because  $c: B \to B^{\Delta^t}$  is), so

$$S_*(E'_t) \to S_*(E)$$

is a quasi-isomorphism. This shows that

$$^{\mathsf{T}}E^1_{s,t} = H_s(E)$$

for every t > 0.

Now we should think about what the differential in the t direction does. Each face map will induce the identity, so the alternating sums will induce alternately 0 and the identity. The result is that

$${}^{\mathsf{T}}E_{s,t}^2 = \begin{cases} H_s(E) & \text{if } t = 0\\ 0 & \text{otherwise} \end{cases}$$

The spectral sequence collapses at this point, and we learn that there is a canonical isomorphism

$$H_*(tS_{*,*}(\pi)) = H_*(E)$$
.

This is then what the un-transposed spectral sequence will converge to. So how does it begin? Fix a singular simplex  $\sigma: \Delta^s \to B$ , and pull  $E \downarrow B$  back along it. Any  $f: \Delta^s \times \Delta^t \to E$  compatible with  $\sigma$  then factors uniquely as

$$\begin{array}{c|c}
f \\
 & \\
\Delta^s \times \Delta^t - - > \sigma^{-1}E \longrightarrow E \\
 & \downarrow \pi_\sigma & \downarrow \pi \\
 & \Delta^s \longrightarrow B
\end{array}$$

Adjointing this, we find that the set of such f's forms the set of singular t-simplices in a space of sections:

$$\operatorname{Sin}_t\Gamma(\Delta^s,\sigma^{-1}E)$$
.

Forming the free R-module and then taking the corresponding chain complex gives a chain complex for each  $\sigma \in \operatorname{Sin}_s(B)$ , namely

$$S_*(\Gamma(\Delta^s, \sigma^{-1}E))$$
.

So

$$E_{s,t}^1 = \bigoplus_{\sigma: \Delta^s \to B} H_t(\Gamma(\Delta^s, \sigma^{-1}E)).$$

The association  $\sigma \mapsto H_t(\Gamma(\Delta^s, \sigma^{-1}E))$  is a kind of "sheaf," and the  $E^2$ -term that results is a kind of sheaf homology of B with these coefficients. This much you can say for a general map  $\pi$ ; this is a singular homology form of the Leray spectral sequence.

If  $\pi$  is a fibration, the map  $\sigma^{-1}E \downarrow \Delta^s$  is a fibration, and hence trivial because  $\Delta^s$  is contractible. So the space of sections is then just the space of maps from the base to the fiber. Write  $F_{\sigma}$  for the fiber over the barycenter of  $\Delta^s$ , so that

$$\Gamma(\Delta^s, \sigma^{-1}E) \simeq F_{\sigma}^{\Delta^s} \simeq F_{\sigma}$$
.

and

$$E_{s,t}^1 \simeq \bigoplus_{\sigma \in \operatorname{Sin}_s(B)} H_t(F_\sigma).$$

The resulting  $E^2$ -term is the homology of B with coefficients in a corresponding local coefficient system:

$$E_{s,t}^2 = H_s(B; H_t(p^{-1}(-))).$$

There are many advantages to this construction. It is transparently natural in the fibration, and a version exists for *any* map.

# 29 Cohomological spectral sequences

#### Upper indexing

We have set everything up for homology, but of course there are cohomology versions of everything as well. Given a filtered space

$$\cdots \subset F_{-1}X \subset F_0X \subset F_1X \subset \cdots$$

we filtered the singular chains  $S_*(X)$  by

$$F_s S_*(x) = S_*(F_s X).$$

Now we will filter the cochains with values in M by

$$F_{-s}S^*(X;M) = \ker(S^*(X;M) \to S^*(F_{s-1}X;M)).$$

Note the -s; this is necessary to produce an *increasing* filtration of  $S^*(X; M)$ . Note also the s-1. This will make the indexing of the multiplicative structure better. For example, most of our filtered spaces will have  $F_{-1} = \emptyset$ , in which case  $F_0S^*(X; M) = S^*(X; M)$  and all the other filtration degrees are subcomplexes of this. In fact, it's standard and convenient to change notation to "upper indexing" as follows:

$$F^s = F_{-s}$$
.

Then  $F^*$  is a decreasing filtration:  $F^s \supseteq F^{s+1}$ . If  $F_{-1}X = \emptyset$ , then  $F^0S^*(X;M) = S^*(X;M)$ .

The singular cochain complex as normally written is the outcome of a similar sign reversal; so the differential is of degree +1. The combination of these two reversals produces a spectral sequence with the following "cohomological" indexing:

$$d_r: E_r^{s,t} \to E_r^{s+r,t-r+1}$$
.

To set this up slightly more generally, suppose that  $C^*$  is a cochain complex equipped with a decreasing filtration  $F^*C^*$ . Write

$$\operatorname{gr}^s C^n = F^s C^n / F^{s+1} C^n.$$

Call it first quadrant if

- $F^0C^* = C^*$ ,
- $H^n(\operatorname{gr}^s C^*) = 0$  for n < s,
- $\bullet \cap F^sC^* = 0.$

Filter the cohomology of  $C^*$  by

$$F^{s}H^{n}(C^{*}) = \ker(H^{n}(C^{*}) \to H^{n}(F^{s-1}C^{*})).$$

**Theorem 29.1.** Let  $C^*$  be a cochain complex with a first quadrant decreasing filtration. There is a naturally associated convergent cohomological spectral sequence

$$E_r^{s,t} \Longrightarrow_s H^{s+t}(C)$$

with

$$E_1^{s,t} = H^{s+t}(\operatorname{gr}^s C^*).$$

In particular we have the cohomology Serre spectral sequence of a fibration  $p: E \to B$ :

$$E_2^{s,t} = H^s(B; H^t(p^{-1}(-)) \Longrightarrow H_{s+t}(E)$$
.

#### Product structure

One of the reasons for passing to cohomology is to take advantage of the cup-product. It turns out that the cup product behaves itself in the cohomology Serre spectral sequence of a fibration  $p: E \to B$ . With a commutative coefficient ring R understood, the local coefficient system  $H^*(p^{-1}(-))$  is now a contravariant functor from  $\Pi_1(B)$  to graded commutative R-algebras. Such coefficients produce bigraded R-algebra

$$E_2^{s,t} = H^s(B; H^t(p^{-1}(-)))$$

that is graded commutative in the sense that

$$yx = (-1)^{|x||y|}xy$$

where |x| and |y| denote total degrees of elements. The entire spectral sequence is then "multiplicative" in the following sense.

- Each  $E_r^{*,*}$  is a commutative bigraded R-algebra
- $d_r$  is a derivation:  $d_r(xy) = (d_r x)y + (-1)^{|x|}x(d_r y)$ .
- The isomorphism  $E_{r+1}^{*,*} \cong H^{*,*}(E_r^{*,*})$  is one of bigraded algebras.
- $E_2^{*,*} = H^*(B; H^*(p^{-1}(-)))$  as bigraded *R*-algebras.
- The filtration on  $H^*(E)$  satisfies

$$F^{s}H^{n}(E) \cdot F^{s'}H^{n'}(E) \subseteq F^{s+s'}H^{n+n'}(E),$$

and the isomorphisms

$$E^{s,t}_{\infty} \cong \operatorname{gr}^s H^{s+t}(E)$$

together form an isomorphism of bigraded R-algebras.

**Theorem 29.2.** Let  $p: E \to B$  be a Serre fibration, and assume given a commutative coefficient ring R. There is a naturally associated multiplicative cohomological first quadrant spectral sequence of R-modules

$$E_2^{s,t} = H^s(B; H^t(p^{-1}(-)) \Longrightarrow H^{s+t}(E).$$

One of the virtues of the construction of the Serre (or more generally Leray) spectral sequence by the method described in Lecture 28 is that the multiplicative structure arises in a natural and explicit way. The bisimplicial set  $S_{*,*}(\pi)$  gives rise to a bicosimplicial R-algebra  $\operatorname{Map}(S_{*,*}(\pi), R)$ , where the R-algebra structure is obtained by simply multiplying in R. Then applying the Alexander-Whitney map in both directions produces a (non-commutative but associative) algebra structure on a double complex, and the resulting filtered complex has the structure of a filtered differential graded algebra. The multiplicative structure of the spectral sequence is then easy to produce, and extends to a description of the effect of Steenrod operations in it as well [36]. The construction from a CW filtration of the base requires us to choose a skeletal approximation of the diagonal. Anyway, I will not make a further attempt to justify the multiplicative behavior of the Serre spectral sequence.

Instead, let's look at an example: The cohomology Gysin sequence for a fibration  $p: E \to B$  whose fibers are R-homology (n-1)-spheres with compatible R-orientations takes the form

$$\cdots \to H^{s-n}(B) \xrightarrow{\pm e(\xi)} H^s(B) \xrightarrow{p^*} H^s(E) \xrightarrow{p_*} H^{s-n+1}(B) \to \cdots$$

The identity of the middle map with  $p^*$  follows from the edge-homomorphism arguments above but reformulated in cohomology. How about the other two maps?

#### Euler class

To understand them let's look at the cohomological Serre spectral sequence giving rise to the Gysin exact sequence. It has two nonzero rows,  $E_r^{*,0}$  and  $E_r^{*,n-1}$ . The multiplicative structure provides  $E_r^{*,n-1}$  with the structure of a module over  $E_r^{*,0}$ . The assumed orientation of the spherical fibration determines a distinguished class  $\sigma$  in the R-module  $E_2^{0,n-1} = H^0(B; H^{n-1}(F))$  (one that evaluates to 1 on each orientation class – remember, the base may not be connected!), and  $E_2^{*,n-1}$  is free as  $E_2^{*,0} = H^*(B)$ -module on this generator.

The transgression of this element,

$$e = d_n \sigma \in E_n^{n,0} = H^n(B)$$
,

is a canonically defined class, called the Euler class of the R-oriented spherical fibration.

This class determines the entire transgression  $H^*(B) \to H^*(B)$  in the Gysin sequence:

$$x \mapsto d_n(x \cdot \sigma) = (-1)^{|x|} xe = \pm ex$$

by the Leibnitz formula, since  $d_n x = 0$ .

The Euler class is a "characteristic class," in the sense that if we use  $f: B' \to B$  to pull the spherical fibration  $\xi: E \downarrow B$  back to  $f^*\xi: E' \downarrow B'$  (along with the chosen orientation), then

$$f^*(e(\xi)) = e(f^*\xi).$$

In particular E might be the complement of the zero section of an R-oriented real n-plane bundle. The universal case is then  $\xi_n : ESO(n) \downarrow BSO(n)$ , and we receive a canonical cohomology class

$$e_n = e(\xi_n) \in H^n(BSO(n); R)$$
.

If we use coefficients in  $\mathbb{F}_2$ , every *n*-plane bundle is canonically oriented and we receive a class  $e_n \in H^n(BO(n); \mathbb{F}_2)$ .

In a sense the Euler class is the fundamental characteristic class: it rules all others. To illustrate its importance, notice that if  $p: E \to B$  has a section  $s: B \to E$  then the map  $p^*: H^*(B) \to H^*(E)$  is a split injection. The Gysin sequence becomes a short exact sequence;  $p_* = 0$ . Said differently, the edge homomorphism story shows that in that case all differentials hitting the base are trivial; in particular  $e(\xi) = 0$ . So if  $e(\xi) \neq 0$  then the bundle doesn't admit a section. If the bundle was the complement of the zero section in an R-oriented vector bundle,  $e(\xi)$  is an obstruction to the existence of a nowhere zero section.

The Euler class gets its name from the following theorem.

**Theorem 29.3.** Let M be an R-oriented closed manifold. Then evaluating the Euler class of the tangent bundle  $\tau$  on the fundamental class of M produces the image in R of the Euler characteristic of M:

$$\langle e(\tau), [M] \rangle = \chi(M) \in R$$
.

Remark 29.4. If B is a finite CW complex of dimension at most the fiber dimension of the vector bundle, then the Euler class is the only obstruction to compressing a classifying map  $B \to BSO(n)$  through a map to BSO(n-1), and the Euler class is a complete obstruction to a section. Thus for example the Euler characteristic closed oriented n-manifold vanishes if and only if the manifold admits a nowhere vanishing vector field.

So if M admits a nonvanishing vector field then  $\chi(M) = 0$ .

#### Integration along the fiber

How about the last map,  $H^s(E) \to H^{s-n+1}(B)$ ? This is a "wrong-way" or "Umkher" map – it moves in the opposite direction from  $p^*: H^s(B) \to H^s(E)$  – and also decreases dimension by the dimension of the fiber. In fact let  $p: E \to B$  be any fibration such that  $H^*(B; H^t(p^{-1}(-))) = 0$  for all t > n, and suppose we are given a map of local systems

$$H^n(p^{-1}(-)) \to R$$

to the trivial local system of R-modules. For example the fibers might be closed (n-1)-manifolds, equipped with compatible orientations.

Now we have a new edge, an upper edge, and our map is given by a new edge homomorphism:

$$p_*: H^s(E) = F^0 H^s(E) = F^{s-n+1} H^s(E) \twoheadrightarrow E_{\infty}^{s-n+1,n-1} \hookrightarrow E_2^{s-n+1,n-1} \to H^{s-n+1}(B) \, .$$

This edge homomorphism can sometimes be given geometric meaning as well. With real coefficients, for example, we can use deRham cohomology, and regard the map  $p_*$  as "integration along the fiber."

The multiplicative structure of the spectral sequence implies that the Umkher map  $p_*$  is a module homomorphism for the graded algebra  $H^*(B)$ :

$$p_*((p^*x)\cdot y) = x\cdot p_*y.$$

This important formula has various names: "Frobenius reciprocity," or the "projection formula."

#### Loop space of $S^n$ again

Let's try to compute the cup product structure in the cohomology of  $\Omega S^n$ , again using the Serre spectral sequence for  $PS^n \downarrow S^n$ . One way to analyze this would be to set up the cohomology version of the Wang sequence, subject of a homework problem. But let's just use the spectral sequence directly. Take n > 1.

To begin,

$$E_2^{s,t} = H^s(S^n; H^t(\Omega S^n)) = H^s(S^n) \otimes H^t(\Omega S^n).$$

There are two nonzero columns. Write  $\iota_n \in H^n(S^n)$  for the dual of the orientation class. The cohomology transgression  $d_n : E_2^{0,n-1} \to E_2^{n,0}$  must be an isomorphism. Write  $x \in H^{n-1}(\Omega S^n)$  for the unique class mapping to  $\iota_n$ .

As in the homology calculation (or because of it) we know that  $H^{k(n-1)}(\Omega S^n)$  is an infinite cyclic group. A first question then is: Is the the cup k-th power  $x^k$  a generator?

First assume that n is odd, so that |x| = n - 1 is even. Then by the Leibniz rule

$$d_n x^2 = 2(d_n x)x = 2\iota_n x.$$

This is twice the generator of  $E_2^{n,n-1}$ . In order to kill the generator itself, we must be able to divide  $x^2$  by 2 in  $H^{2(n-1)}(\Omega S^n)$ . So there is a unique element, call it  $\gamma_2$ , such that  $2\gamma_2 = x^2$ , and it serves as a generator for the infinite cyclic group  $H^{2(n-1)}(\Omega S^n)$ .

With this in the bag, let's observe that the transgression of  $x^k$  is

$$d_n x^k = k(d_n x) x^{k-1} = k \iota_n x^{k-1}.$$

For example

$$d_n x^3 = 3\iota_n x^2 = 3 \cdot 2\iota_n \gamma_2.$$

Since  $\iota_n \gamma_2$  is a generator of  $E_2^{n,2(n-1)}$ , the element  $x^3$  must be divisible by  $3 \cdot 2 = 3!$ : there is a unique element of  $H^{3(n-1)}(\Omega S^n)$ , call it  $\gamma_3$ , such that  $x^3 = 3!\gamma_3$ .

This evidently continues:  $H^{k(n-1)}(\Omega S^n)$  is generated by a class  $\gamma_k$  such that  $x^k = k! \gamma_k$ . This implies that these generators satisfy the product formula

$$\gamma_j \gamma_k = (j, k) \gamma_{j+k}$$
 ,  $(j, k) = \frac{(j+k)!}{j!k!}$ .

This is a divided power algebra, denoted by  $\Gamma[x]$ :

$$H^*(\Omega S^n) = \Gamma[x]$$
 for  $n$  odd,  $|x| = n - 1$ .

The answer is the same for any coefficients. With rational coefficient, these divided classes are already present, so

$$H^*(\Omega S^n; \mathbb{Q}) = \mathbb{Q}[x]$$
.

Then  $H^*(\Omega S^n; \mathbb{Z})$ , being torsion-free, sits inside this as the sub-algebra generated additively by the classes  $x^k/k!$ .

Now let's turn to the case in which n is even. Then |x| is odd, so by commutativity  $2x^2 = 0$ . But  $H^{2(n-1)}(\Omega S^n)$  is torsion-free, so  $x^2 = 0$ .

So we need a new indecomposable element in  $H^{2(n-1)}(\Omega S^n)$ : Call it y. Choose the sign so that

$$d_n y = \iota_n x \in E_n^{n,n-1}$$
.

Now |y| = 2(n-1) is even, so

$$d_n y^k = k \iota_n y^{k-1} x$$

and

$$d_n(xy^k) = \iota_n y^k - x \cdot ky^{k-1} \iota_n x = \iota_n y^k$$

(since  $x^2 = 0$ ). Reasoning as before, we find that

$$H^*(\Omega S^n) = E[x] \otimes \Gamma[y]$$
 for  $n$  even,  $|x| = n - 1$ ,  $|y| = 2(n - 1)$ ,

as algebras, again with any coefficients.

#### 30 Serre classes

Let X be a simply connected space. Suppose that  $\overline{H}_q(X)$  is a torsion group for all q: every element  $x \in H_q(X)$  is killed by some positive integer. This is the same as saying that X has the same rational homology as a point. Is every homotopy group also a torsion group, or can rational homotopy make an appearance? What if the reduced homology was all p-torsion (i.e. every element is killed by some power of p) – must  $\pi_*(X)$  also be entirely p-torsion? What if the homology is assumed to be of finite type (finitely generated in every dimension) – must the same be true of homotopy? Serre explained how things like this can be checked, without explicit computation (which is not an option!) by describing what is required of a class  $\mathbf{C}$  of abelian groups that allow it to be considered "negligible."

**Definition 30.1.** A class **C** of abelian groups is a *Serre class* if  $0 \in \mathbb{C}$ , and, for any short exact sequence  $0 \to A \to B \to C \to 0$ , A and C lie in **C** if and only if B does.

Here are some immediate consequences of this definition.

30. SERRE CLASSES 105

- A Serre class is closed under isomorphisms.
- A Serre class is closed under formation of subgroups and quotient groups.

• Let  $A \xrightarrow{i} B \xrightarrow{p} C$  be exact at B. If  $A, C \in \mathbb{C}$ , then  $B \in \mathbb{C}$ : In

the row is exact and the indicated factorizations exist since pi = 0; the surjectivity and injectivity follow from exactness.

Here are the main examples.

**Example 30.2.** The class of trivial abelian groups; the class  $C_{\rm fin}$  of all finite abelian groups; the class  $C_{\rm fg}$  of all finitely generated abelian groups; the class of all abelian groups.

**Example 30.3.**  $C_{tors}$ , the class of all torsion abelian groups. To see that this is a Serre class, start with a short exact sequence

$$0 \to A \xrightarrow{i} B \xrightarrow{p} C \to 0$$
.

It's clear that if B is torsion then so are A and C. Conversely, suppose that A and C are torsion groups. Let  $b \in B$ . Then p(nb) = np(b) = 0 for some n > 0, since C is torsion; so there is  $a \in A$  such that i(a) = nb. But A is torsion too, so ma = 0 for some m > 0, and hence mnb = 0.

**Example 30.4.** Fix a prime p. The class of p-torsion groups forms a Serre class. More generally, let  $\mathcal{P}$  be a set of primes. Define  $\mathbf{C}_{\mathcal{P}}$  to be the class of torsion abelian groups A such that if p divides the order of  $a \in A$  for some  $p \in \mathcal{P}$  then a = 0. If  $\mathcal{P} = \emptyset$  this is just  $\mathbf{C}_{tors}$ . Write  $\mathbf{C}_p$  for  $\mathbf{C}_{\{p\}}$ . This is the class of torsion abelian groups without p-torsion. Since  $\mathbb{Z}_{(p)}$  is a direct limit of copies of  $\mathbb{Z}$  with bonding maps running through the natural numbers prime to p,  $A \in \mathbf{C}_p$  if and only if  $A \otimes \mathbb{Z}_{(p)} = 0$ . These are the kinds of groups you're willing to ignore if you are only interested in "p-primary" information.

**Example 30.5.** The intersection of a collection of Serre classes is again a Serre class. For example,  $C_{\text{fin}} \cap C_p$  is the class of finite abelian groups of order prime to p.

The definition of a Serre class is set up so that it makes sense to work "modulo  $\mathbb{C}$ ." So we'll say that A is "zero mod  $\mathbb{C}$ " if  $A \in \mathbb{C}$ . A homomorphism is a "mod  $\mathbb{C}$  monomorphism" if its kernel lies in  $\mathbb{C}$ ; a "mod  $\mathbb{C}$  epimorphism" if its cokernel lies in  $\mathbb{C}$ ; and a "mod  $\mathbb{C}$  isomorphism" if both kernel and cokernel lie in  $\mathbb{C}$ . So for example  $f: A \to B$  is a mod  $\mathbb{C}_{tors}$  isomorphism exactly when  $f \otimes 1: A \otimes \mathbb{Q} \to B \otimes \mathbb{Q}$  is an isomorphism of rational vector spaces.

**Lemma 30.6.** Let **C** be a Serre class. The classes of mod **C** monomorphisms, epimorphisms, and isomorphisms contain all isomorphisms and are closed under composition. The class of mod **C** isomorphisms satisfies 2-out-of-3.

Proof. Form

and check that the outside path is exact.

Here are some straightforward consequences of the definition:

- Let  $C_*$  be a chain complex. If  $C_n \in \mathbf{C}$  then  $H_n(C_*) \in \mathbf{C}$ .
- Suppose  $F_*A$  is a filtration on an abelian group. If  $A \in \mathbb{C}$ , then  $\operatorname{gr}_s A \in \mathbb{C}$  for all s. If the filtration is finite (i.e.  $F_m = 0$  and  $F_n = A$  for some m, n) and  $\operatorname{gr}_s A \in \mathbb{C}$  for all s, then  $A \in \mathbb{C}$ .
- Suppose we have a spectral sequence  $\{E_{s,t}^r\}$ . If  $E_{s,t}^2 \in \mathbb{C}$ , then  $E_{s,t}^r \in \mathbb{C}$  for  $r \geq 2$ . If  $\{E^r\}$  is a first quadrant spectral sequence (so that  $E_{s,t}^{\infty}$  is defined and achieved at a finite stage) it follows that  $E_{s,t}^{\infty} \in \mathbb{C}$ . Thus if the spectral sequence comes from a first quadrant filtered complex C and  $E_{s,t}^2 \in \mathbb{C}$  for all s+t=n, then  $H_n(C) \in \mathbb{C}$ .

The first implication in homology is this: Suppose that  $A \subseteq X$  is a pair of path-connected spaces. If two of  $\overline{H}_n(A)$ ,  $\overline{H}_n(X)$ ,  $H_n(X,A)$  are zero mod  $\mathbf{C}$  for all n, then so is the third. More generally, if you have a ladder of abelian groups (a map of long exact sequences) and two out of every three consecutive rungs are mod  $\mathbf{C}$  isomorphisms then so is the third: a mod  $\mathbf{C}$  five-lemma.

#### Serre rings and Serre ideals

To apply this theory to the Serre spectral sequence we need to know that our class is compatible with tensor product. Let's say that a Serre class  $\mathbb{C}$  is a Serre ring if whenever A and B are in  $\mathbb{C}$ ,  $A \otimes B$  and Tor(A,B) are too. It's a Serre ideal if we only require one of A and B to lie in  $\mathbb{C}$  to have this conclusion.

All of the examples given above are Serre rings. The ones without finiteness assumptions are Serre ideals.

Here's another closure property we might investigate, and will need. Suppose that  $\mathbf{C}$  is a Serre ring and  $A \in \mathbf{C}$ . Form the classifying space or Eilenberg Mac Lane space BA = K(A, 1). We know that  $H_1(K(A, 1)) = A$  (for example by Poincaré's theorem) so it lies in  $\mathbf{C}$ . How about the higher homology groups? If they are again in  $\mathbf{C}$ , the Serre ring is acyclic.

Acyclicity is a computational issue. Suppose  $\mathbf{C} = \mathbf{C}_{\text{fin}}$  for example. By the Künneth theorem (and the fact that  $\mathbf{C}_{\text{fin}}$  is a Serre ring), it's enough to consider finite cyclic groups. What is  $H_*(BC_n)$ ,

30. SERRE CLASSES 107

where  $C_n$  is a cyclic group of order n? To answer this we can embed  $C_n$  into the circle group  $S^1$  as nth roots of unity. The group of complex numbers of norm 1 acts principally on the unit vectors in  $\mathbb{C}^{\infty}$ , and that space,  $S^{\infty}$ , is contractible. So  $\mathbb{C}P^{\infty} = BS^1$ . The subgroup  $C_n \subset S^1$  acts principally on this contractible space as well, so

$$BC_n = C_n \backslash S^{\infty} = (C_n \backslash S^1) \times_{S^1} S^{\infty}$$

fibers over  $\mathbb{C}P^{\infty}$  with fiber  $C_n \setminus S^1 \cong S^1$ . Let's study the resulting Serre spectral sequence, first in homology.

In it,  $E_{s,t}^2 = H_s(\mathbb{C}P^{\infty}) \otimes H_t(S^1)$ . The only possible differential is  $d^2$ . The one thing we know about  $K(C_n,1)$  is that is fundamental group is  $C_n$  – abelian, so  $H_1(K(C_n,1)) = C_n$ . The only way to accomplish this in the spectral sequence is by  $d^2a = n\sigma$ , where  $\sigma \in H_1(S^1)$  is one of the generators.

This implies that in the cohomology spectral sequence  $d_2e = nx$ , where e generates  $H^1(S^1)$  and x generates  $H^2(\mathbb{C}P^{\infty})$ . Then the multiplicative structure takes over:  $d_2(x^ie) = nx^{i+1}$ .

The effect is that  $E_3^{s,t} = 0$  for t > 0. The edge homomorphism  $H^*(\mathbb{C}P^{\infty}) \to H^*(BC_n)$  is thus surjective, and we find

$$H^*(BC_n) = \mathbb{Z}[x]/(nx), \quad |x| = 2.$$

Passing back to homology, we find that  $\overline{H}_i(BC_n)$  is cyclic of order n if i is a positive odd integer and zero otherwise. In particular, it is finite, so  $\mathbf{C}_{\text{fin}}$  is acyclic.

Since any torsion abelian group A is the direct limit of the directed system of its finite subgroups, we find that  $\overline{H}_q(K(A,1))$  is then torsion as well: so  $\mathbf{C}_{tors}$  is also acyclic.

The calculation also shows that the class of finite p-groups and the class  $C_p$  are acyclic.

To deal with  $C_{fg}$ , we just have to add the infinite cyclic group, whose homology is certainly finitely generated in each degree. So all our examples of Serre rings are in fact acyclic.

#### Serre classes in the Serre spectral sequence

Let **C** be a Serre ideal. If  $H_n(X)$  and  $H_{n-1}(X)$  are zero mod **C** then  $H_n(X; M)$  is zero mod **C** for any abelian group M, by the universal coefficient theorem. If **C** is only a Serre ring, we still reach this conclusion provided  $M \in \mathbf{C}$ .

The convergence theorem for the Serre spectral sequence shows this:

**Proposition 30.7** (Mod C Vietoris-Begle Theorem). Let  $\pi: E \to B$  be a fibration such that B and the fiber F are path connected, and suppose  $\pi_1(B)$  acts trivially on  $H_*(F)$ . Let  $\mathbf{C}$  be a Serre ideal and suppose that  $H_t(F) \in \mathbf{C}$  for all t > 0. Then  $\pi_*: H_n(E) \to H_n(B)$  is a mod  $\mathbf{C}$  isomorphism for all n

*Proof.* The universal coefficient theorem guarantees that  $E_{s,t}^2 = H_s(B; H_t(F)) \in \mathbf{C}$  as long as t > 0. The same is thus true of  $E_{s,t}^r$  and hence of  $E_{s,t}^\infty$ , so the edge homomorphism  $\pi_* : H_n(E) \to H_n(B)$  is a mod  $\mathbf{C}$  isomorphism.

This theorem admits a refinement that will be useful in proving the mod C Hurewicz theorem. For one thing, we would like a result that works for a Serre ring, not merely an Serre ideal, in order to cover cases like  $C_{\rm fg}$ 

**Proposition 30.8.** Let  $\pi: E \to B$  be a fibration such that B is simply connected and the fiber F is path connected. Let  $\mathbf{C}$  be a Serre ring and suppose that

•  $H_s(B) \in \mathbb{C}$  for all s with 0 < s < n, and

•  $H_t(F) \in \mathbb{C}$  for all 0 < t < n - 1.

Then  $\pi_*: H_i(E,F) \to H_i(B,*)$  is an isomorphism mod  $\mathbb{C}$  for all  $i \leq n$ .

*Proof.* We appeal to the relative Serre spectral sequence

$$E_{s,t}^2 = \overline{H}_s(B; H_t(F)) \Longrightarrow H_{s+t}(E, F)$$
.

At  $E_{s,t}^2$ , both the s=0 column and the s=1 column vanish. Also,  $E_{s,t}^2\in C$  for (s,t) in the rectangle

$$2 \le s \le n-1$$
,  $1 \le t \le n-2$ .

In total degree  $i, i \leq n$ , the only group not vanishing mod  $\mathbf{C}$  is  $E_{i,0}^2$ . So the edge homomorphism  $\pi_*: H_i(E,F) \to \overline{H}_i(B)$  is a mod  $\mathbf{C}$  isomorphism.

**Theorem 30.9** (Mod **C** Hurewicz theorem). Assume that **C** is an acyclic Serre ring. Let X be a simply connected space and let  $n \geq 2$ . Then  $\pi_q(X) \in \mathbf{C}$  for all q < n if and only if  $\overline{H}_q(X) \in \mathbf{C}$  for all q < n, and in that case the Hurewicz map  $\pi_n(X) \to H_n(X)$  is a mod **C** isomorphism.

We'll present the proof in the next lecture. For now, a small selection of corollaries:

**Corollary 30.10.** Let X be a simply connected space and  $n \geq 2$  or  $n = \infty$ .

- (1)  $H_q(X)$  is finitely generated for all q < n if and only if  $\pi_q(X)$  is finitely generated for all q < n.
- (2) Let p be a prime number.  $H_q(X)$  is p-torsion for all q < n if and only if  $\pi_q(X)$  is p-torsion for all q < n.
- (3) If  $\overline{H}_q(X;\mathbb{Q}) = 0$  for q < n, then  $\pi_q(X) \otimes \mathbb{Q} = 0$  for q < n, and  $h : \pi_n(X) \otimes \mathbb{Q} \to H_n(X;\mathbb{Q})$  is an isomorphism.

#### 31 Mod C Hurewicz and Whitehead theorems

Proof of Theorem 30.9. This follows the proof of the Hurewicz theorem, but some extra care is needed. Again we use induction and the path-loop fibration. Again, it will suffice to show that if  $\pi_q(X) \in \mathbf{C}$  for q < n then  $\pi_n(X) \to H_n(X)$  is an isomorphism – now mod  $\mathbf{C}$ . To start the induction, with n = 2, we can appeal to the Hurewicz isomorphism: the map  $\pi_2(X) \to H_2(X)$  is an actual isomorphism.

The inductive step uses the commutative diagram

$$\pi_{q}(X) \overset{\cong}{\longleftarrow} \pi_{q}(PX, \Omega X) \overset{\cong}{\longrightarrow} \pi_{q-1}(\Omega X)$$

$$\downarrow^{h} \qquad \qquad \downarrow^{h} \qquad \qquad \downarrow^{h}$$

$$\overline{H}_{q}(X) \overset{\cong}{\longleftarrow} H_{q}(PX, \Omega X) \overset{\cong}{\longrightarrow} H_{q-1}(\Omega X).$$

Two thing need checking: (1) the map  $H_n(PX, \Omega X) \to \overline{H}_n(X)$  is an isomorphism mod  $\mathbb{C}$ , and (2) the map  $h: \pi_{n-1}(\Omega X) \to H_{n-1}(\Omega X)$  is an isomorphism mod  $\mathbb{C}$ .

Neither of these facts follow from an inductive hypothesis if  $\pi_2(X) \neq 0$  (unless **C** is the trivial class), but we begin by showing that they do follow from the inductive hypothesis if  $\pi_2(X) = 0$ .

Suppose  $\pi_2(X) = 0$ , so that  $\Omega X$  is simply connected. Since  $\pi_i(\Omega X) = \pi_{i+1}(X)$  we know it lies in  $\mathbb{C}$  for i < n-1. The inductive hypothesis applies to  $\Omega X$  and shows that  $\overline{H}_i(\Omega X) \in \mathbb{C}$  for i < n-1 and that  $h: \pi_{n-1}(\Omega X) \to H_{n-1}(\Omega X)$  is a mod  $\mathbb{C}$  isomorphism. The inductive hypothesis

also applies to X of course, and shows that  $\overline{H}_i(X) \in \mathbf{C}$  for i < n. So we are in position to apply Proposition 30.8 from last lecture to see fact (1).

But if  $\pi_2(X) \neq 0$ ,  $\Omega X$  is not simply connected. To deal with that, let's take the 2-connected cover in the Whitehead tower: This is a fibration  $Y \downarrow X$  with fiber  $K = K(\pi_2(X), 1)$ . This is where the acyclic condition comes in: since  $\pi_2(X) \in \mathbf{C}$ ,  $H_i(K) \in \mathbf{C}$  for i > 0. The long exact sequence for the pair (Y, K) shows that

$$\overline{H}_i(Y) \to H_i(Y,K)$$

is a mod **C** isomorphism. We will apply Proposition 30.8 to  $(Y, K) \downarrow (X, *)$ , using the fact that X is simply connected and  $H_i(X) \in \mathbf{C}$  for 0 < i < n. We find that

$$H_i(Y,K) \to H_i(X,*)$$

is a mod **C** isomorphism for  $i \leq n$ . Therefore the projection map  $\overline{H}_i(Y) \to \overline{H}_i(X)$  is a mod **C** isomorphism for  $i \leq n$ .

The map  $\pi_i(Y) \to \pi_i(X)$  is an isomorphism for  $i \geq 2$ , so our hypothesis applies to Y, and we can perform the inductive step on it instead of an X.

Corollary 31.1. Let X be a simply connected space, p a prime, and  $n \ge 2$ . Then  $\pi_i(X) \otimes \mathbb{Z}_{(p)} = 0$  for all i < n if and only if  $\overline{H}_i(X; \mathbb{Z}_{(p)}) = 0$  for all i < n, and in that case

$$h: \pi_n(X) \otimes \mathbb{Z}_{(p)} \to H_n(X; \mathbb{Z}_{(p)})$$

is an isomorphism.

*Proof.* The acyclic Serre ring  $\mathbf{C}_p$  consists of abelian groups such that  $A \otimes \mathbb{Z}_{(p)} = 0$ .

Now for the relative version!

**Theorem 31.2** (Relative mod **C** Hurewicz theorem). Let **C** be an acyclic Serre ideal, and (X, A) a pair of spaces, both simply connected. Fix  $n \ge 1$ . Then  $\pi_i(X, A) \in \mathbf{C}$  for all i with  $2 \le i < n$  if and only if  $H_i(X, A) \in \mathbf{C}$  for all i with  $2 \le i < n$ , and in that case  $h : \pi_n(X, A) \to H_n(X, A)$  is a mod **C** isomorphism.

The proof follows the same line as in the absolute case. But note the requirement here, in the relative case, that  $\mathbf{C}$  is a Serre *ideal*. Let me just point out where that assumption is required. We use the same diagram, in which F is the homotopy fiber of the inclusion  $A \hookrightarrow X$ :

$$\pi_{n-1}(F) \stackrel{\cong}{\longleftarrow} \pi_n(PX, F) \stackrel{\cong}{\longrightarrow} \pi_n(X, A)$$

$$\downarrow^h \qquad \qquad \downarrow^h \qquad \qquad \downarrow^h$$

$$\overline{H}_{n-1}(F) \stackrel{\cong}{\longleftarrow} H_n(PX, F) \stackrel{p_*}{\longrightarrow} H_n(X, A).$$

In the proof that  $p_*$  is an isomorphism, we'll again use the relative Serre spectral sequence, but now the  $E^2$  term is  $E_{s,t}^2 = H_s(X, A; H_t(X))$ , and we have no control over  $H_t(X)$ : all our assumptions related to the relative homology.

And this leads on to a mod **C** Whitehead theorem:

**Theorem 31.3** (Mod C Whitehead theorem). Let C be an acyclic Serre ideal, and  $f: X \to Y$  a map of simply connected spaces. Fix  $n \ge 2$ . The following are equivalent.

- (1)  $f_*: \pi_i(X) \to \pi_i(Y)$  is a mod  $\mathbb{C}$  isomorphism for  $i \leq n-1$  and a mod  $\mathbb{C}$  epimorphism for i = n, and
- (2)  $f_*: H_i(X) \to H_i(Y)$  is a mod  $\mathbb{C}$  isomorphism for  $i \leq n-1$  and a mod  $\mathbb{C}$  epimorphism for i = n.

The theory of Serre classes is quite beautiful, but it does not relate easily to the standard way of working with homology with coefficients. The following lemma forms the link between mod p homology and the mod  $\mathbf{C}_p$  Whitehead theorem.

**Lemma 31.4.** Let X and Y be spaces whose p-local homology is of finite type, and suppose  $f: X \to Y$  induces an isomorphism in mod p homology. Then it induces a mod  $\mathbf{C}_p$  isomorphism in integral homology.

*Proof.* Since  $\mathbb{Z}_{(p)}$  is flat, a homomorphism  $f:A\to B$  is a mod  $\mathbb{C}$  isomorphism if and only if  $f\otimes 1:A\otimes \mathbb{Z}_{(p)}\to B\otimes \mathbb{Z}_{(p)}$  is an isomorphism.

A finitely generated module over  $\mathbb{Z}_{(p)}$  is trivial if it's trivial mod p. So we want to show that the kernel and cokernel of  $f_*: H_*(X) \to H_*(Y)$  are trivial after tensoring with  $\mathbb{F}_p$ .

Form the mapping cone Z of the map f. By assumption it has trivial mod p reduced homology. Since  $\mathbb{Z}_{(p)}$  is Noetherian,  $H_*(Z;\mathbb{Z}_{(p)})$  is of finite type. The universal coefficient theorem shows that  $\overline{H}_*(Z;\mathbb{Z}_{(p)})\otimes \mathbb{F}_p \hookrightarrow \overline{H}_*(Z;\mathbb{F}_p)$ , so we conclude that  $\overline{H}_*(Z)\otimes \mathbb{Z}_{(p)}=\overline{H}_*(Z;\mathbb{Z}_{(p)})=0$ , and hence that  $f_*\otimes 1: H_*(X)\otimes \mathbb{Z}_{(p)}\to H_*(Y)\otimes \mathbb{Z}_{(p)}$  is an isomorphism.

**Corollary 31.5.** Let X and Y be simply connected spaces whose p-local homology is of finite type, and suppose  $f: X \to Y$  induces an isomorphism in mod p homology. Then  $f_*: \pi_*(X) \otimes \mathbb{Z}_{(p)} \to \pi_*(Y) \otimes \mathbb{Z}_{(p)}$  is an isomorphism.

This is every topologist's favorite theorem! Absent the fundamental group, you can treat primes one by one.

#### Some calculations

Let's first compute the homology – well, at least the rational homology – of Eilenberg Mac Lane space K(A, n), for A finitely generated. By the Künneth isomorphism it suffices to do this for A cyclic. When A is any torsion group, the mod  $C_{\text{tors}}$  Hurewicz theorem shows that  $\overline{H}_*(K(A, n); \mathbb{Q}) = 0$ . So we will focus on  $K(\mathbb{Z}, n)$ .

The case n=1 is the circle, whose cohomology is an exterior algebra on one generator of dimension 1:  $H^*(K(\mathbb{Z},1);\mathbb{Q}) = E[\iota_1], |\iota_1| = 1.$ 

We know what  $H^*(K(\mathbb{Z},2);\mathbb{Q})$  is, too, but let's compute it in a way that starts an induction. It also follows the path laid down by Serre in his computation of the mod 2 cohomology of K(A, n), using the fiber sequence

$$K(A, n-1) \to PK(A, n) \to K(A, n)$$
.

When n=2 there are only two rows – this is a spherical fibration. The class  $\iota_1$  must transgress to a generator, call it  $\iota_2 \in H^2(K(\mathbb{Z},2);\mathbb{Q})$ . Proceeding inductively, using  $d_2(\iota_2^k \iota_1) = \iota_2^{k+1}$ , you find that

$$H^*(K(\mathbb{Z},2);\mathbb{Q}) = \mathbb{Q}[\iota_2].$$

When n=3, there is a polynomial algebra in the fiber. Again the fundamental class must transgress to a generator,  $\iota_3=d_3\iota_2\in H^3(K(\mathbb{Z},3);\mathbb{Q})$ . The Leibniz formula gives  $d^3(\iota_2^k)=k\iota_3\iota_2^{k-1}$ . This differential is an isomorphism: this is where working over  $\mathbb{Q}$  separates from working anywhere else. So we discover that

$$H^*(K(\mathbb{Z},3);\mathbb{Q}) = E[\iota_3].$$

This starts the induction, and leads to

$$H^*(K(\mathbb{Z}, n); \mathbb{Q}) = \begin{cases} E[\iota_n] & \text{if } n \text{ is odd} \\ \mathbb{Q}[\iota_n] & \text{if } n \text{ is even} \end{cases}$$

In both cases, the cohomology is free as a graded commutative algebra.

**Proposition 31.6.** The homotopy group  $\pi_i(S^n)$  is finite for all i except for i = n and if n is even for i = 2n - 1, when it is finitely generated of rank 1.

*Proof.* The case n=1 is special and simple, so suppose  $n \geq 2$ . Let

$$S^n \to K(\mathbb{Z}, n)$$

represent a generator of  $H^n(S^n)$ . It induces an isomorphism in  $\pi_n$  and in  $H_n$ .

When n is odd, it induces an isomorphism in rational homology, and therefore in rational homotopy.

When n is even, we should compute the cohomology of the fiber F. The class  $\iota_n$  on the base survives to a generator of  $H^n(S^n;\mathbb{Q})$ , but  $\iota_n^2$  must die. The only way to kill it is by a transgression from a class  $\iota_{2n-1} \in H^{2n-1}(F)$ :  $d_{2n}\iota_{2n-1} = \iota_n^2$ . Then the Leibniz formula gives  $d_{2n}(\iota_n^k\iota_{2n-1}) = k\iota_n^{k-1}$ , leaving precisely the cohomology of  $S^n$ . So the fiber has the same rational cohomology as  $K(\mathbb{Z}, 2n-1)$ . The generator  $\iota_{2n-1}$  gives a map  $F \to K(\mathbb{Z}, 2n-1)$  that induces an isomorphism in rational homology, and hence in rational homotopy.

You might ask: Why couldn't this cancellation happen some other way? You can complete this argument, but perhaps you'll prefer a different approach. Loop the Barratt-Puppe sequence back one notch, to a fiber sequence  $K(\mathbb{Z}, n-1) \to F \to S^n$ , and work directly in homology. Now n-1 is odd, so the entire  $E^2$  term has just four generators. The generator  $x \in H_n(S^n)$  must transgress to the fiber (else F would have the wrong homology in dimension n-1, or using the relationship between the transgression and the boundary map in homotopy), and what's left at  $E^{n+1}$  is just a  $\mathbb{Q}$  for  $E_{0,0}^2$  and a  $\mathbb{Q}$  for  $E_{n,n-1}^2$ .

We can identify an element of infinite order in  $\pi_{4k-1}(S^{2k})$  in several ways. Here's one. The space  $S^m \times S^n$  admits a CW structure with (m+n-1)-skeleton given by the wedge  $S^m \vee S^n$ . There is thus a map

$$\omega: S^{m+n-1} \to S^m \vee S^n$$

that serves as the attaching map for the top cell. Given homotopy classes  $\alpha \in \pi_m(X)$  and  $\beta \in \pi_n(X)$ , we an form the composite

$$S^{m+n-1} \xrightarrow{\omega} S^m \vee S^n \xrightarrow{\alpha \vee \beta} X \vee X \xrightarrow{\nabla} X$$

This defines the Whitehead product

$$[-,-]:\pi_m(X)\times \pi_n(X)\to \pi_{m+n-1}(X).$$

When m=1, this is the action of  $\pi_1(X)$  on  $\pi_n(X)$ . Now we can define the Whitehead square

$$w_n = [\iota_n, \iota_n] \in \pi_{2n-1}(S^n).$$

When n = 2k, it generates an infinite cyclic subgroup.

The same calculation works for a while locally at a prime. Let's look at  $S^3$  for definiteness. Follow the Barratt-Puppe sequence back one stage, to get a fibration sequence

$$K(\mathbb{Z},2) \to \tau \geq 4S^3 \to S^3$$

In the spectral sequence, with integral coefficients,

$$E_2^{*,*} = E[\sigma] \otimes \mathbb{Z}[\iota_2].$$

The class  $\iota_2$  must transgress to  $\sigma$  (at least up to sign), and then

$$d_2(\iota_2^k) = k\sigma \iota_2^{k-1}.$$

This map is always injective, leaving

$$E_3^{3,2k-2} = \mathbb{Z}/k\mathbb{Z}$$

and nothing else except for  $E_3^{0,0} = \mathbb{Z}$ . The result is that

$$H_{2k}(\tau_{>4}S^3) = \mathbb{Z}/k\mathbb{Z}, \quad k \ge 1.$$

The first time *p*-torsion appears is in dimension 2p:  $H_{2p}(\tau_{\geq 4}S^3) = \mathbb{Z}/p\mathbb{Z}$ . This is the mod  $\mathbb{C}_p$  Hurewicz dimension, so  $\pi_i(S^3)$  has no *p*-torsion in dimension less than 2p, and  $\pi_{2p}(S^3) \otimes \mathbb{Z}_{(p)} = \mathbb{Z}/p\mathbb{Z}$ .

# 32 Freudenthal, James, and Bousfield

#### Suspension

The transgression takes on a particularly simple form if the total space is contractible. Remember the adjoint pair

$$\Sigma : \mathbf{Top}_* \rightleftarrows \mathbf{Top}_* : \Omega$$
.

The adjunction morphisms

$$\sigma: X \to \Omega \Sigma X$$
, ev:  $\Sigma \Omega X \to X$ 

are given by

$$\sigma(x)(t) = [x, t], \quad \text{ev}(\omega, t) = \omega(t).$$

**Proposition 32.1.** Let X be a path connected space. The transgression relation

$$\overline{H}_n(X) \rightharpoonup \overline{H}_{n-1}(\Omega X)$$

associated to the path loop fibration  $p: PX \to X$  is the converse of the relation defined by the map

$$\overline{H}_{n-1}(\Omega X) = \overline{H}_n(\Sigma \Omega X) \xrightarrow{\operatorname{ev}_*} \overline{H}_n(X).$$

*Proof.* Recall that the transgression relation is given (in this case) by the span

It consists of the subgroup

$$\left\{(x,y)\in \overline{H}_n(X)\times \overline{H}_{n-1}(\Omega X): \exists\ z\in H_n(PX,\Omega X) \text{ such that } p_*z=x \text{ and } \partial z=y\right\}.$$

We are claiming that this is the same as the subgroup

$$\{(x,y)\in \overline{H}_n(X)\times \overline{H}_{n-1}(\Omega X): \exists\ w\in \overline{H}_n(\Sigma\Omega X) \text{ such that } \mathrm{ev}_*w=x \text{ and } iw=y\}$$

determined by the span

where  $i: \overline{H}_{n-1}(\Omega X) \xrightarrow{\cong} \overline{H}_n(\Sigma \Omega X)$  is the canonical isomorphism.

To see this, we just have to remember how the boundary map and the isomorphism i are related. This is a general point. So suppose we have a space X and a subspace A, so we are interested in  $i: \overline{H}_n(\Sigma X) \to \overline{H}_{n-1}(X)$  and the the boundary map  $\partial: H_n(X,A) \to \overline{H}_{n-1}(A)$ . The latter may be described geometrically in the following way. Form the mapping cylinder M of the inclusion map  $A \to X$ . Then  $A \hookrightarrow M$  is a cofibration with cofiber  $\Sigma A$ , and we have the span

in which the left arrow is a homology isomorphism. The boundary map is induced by this span, together with the isomorphism i.

Specializing to the pair  $(PX, \Omega X)$  gives commutativity of part of the diagram

The other part follows from homotopy commutativity of

$$(M,\Omega X) \longrightarrow (\Sigma \Omega X,*) \qquad \qquad \sigma; (\omega,t) \longmapsto *; [\omega,t]$$

$$\downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$(PX,\Omega X) \xrightarrow{p} (X,*) \qquad \qquad \sigma(0); \omega \longmapsto \sigma(0); * \qquad *; \omega(t).$$

Notation: the first entry is the map on  $PX = \{\sigma : I \to X \text{ such that } \sigma(0) = *\}$ ; the second entry is the map on  $\Omega X \times I$ . A homotopy between the two branches is given at time s by

$$\sigma; \omega \mapsto \sigma(s); (t \mapsto \omega(st))$$
.

This diagram shows that the two relations are identical.

The evaluation map  $\Sigma\Omega X \to X$  also admits an interesting interpretation in cohomology, with coefficients in an abelian group  $\pi$ :

$$\overline{H}^{n}(X;\pi) \xrightarrow{\longrightarrow} \overline{H}^{n-1}(\Omega X;\pi)$$

$$\downarrow^{\cong} \qquad \qquad \qquad \downarrow^{\cong}$$

$$\downarrow^{\cong} \qquad \qquad \qquad \downarrow^{\cong}$$

$$\downarrow^{\cong} \qquad \qquad \downarrow^{\cong}$$

$$[X,K(\pi,n)]_{*} \xrightarrow{\Omega} [\Omega X,\Omega K(\pi,n)]_{*}$$

commutes.

Our identification of the evaluation map as the converse of a transgression allows us to invoke the Serre exact sequence. After all, if the total space is contractible, every third term in the Serre exact sequence vanishes, and the remaining map, the transgression, is an isomorphism. In fact, in that case we get just a little extra, the last clause in the following proposition, which we state in the generality of working modulo a Serre ring.

**Proposition 32.2.** Let  $\mathbf{C}$  be a Serre ring. Let  $n \geq 1$  and suppose X is simply connected and that  $\overline{H}_i(X) \in \mathbf{C}$  for all i < n. Then the evaluation map  $ev_* : \overline{H}_{i-1}(\Omega X) \to \overline{H}_i(X)$  is an isomorphism mod  $\mathbf{C}$  for i < 2n - 1 and an epimorphism mod  $\mathbf{C}$  for i = 2n - 1.

This result leads the way to the "suspension theorem" of Hans Freudenthal (1905–1990; German, working in Amsterdam, escaped from a labor camp during World War II). The relevant adjunction morphism is now the "suspension"

$$\sigma_X: X \to \Omega \Sigma X$$
.

The formalism of adjunction guarantees commutativity of

which shows for a start that  $\sigma_X$  induces a split monomorphism in reduced homology. But we also know from 32.2 that if X is (n-1) connected, the evaluation map in

$$H_{i}(X) \xrightarrow{(\sigma_{X})_{*}} H_{i}(\Omega \Sigma X)$$

$$= \bigvee_{(\operatorname{ev}_{\Sigma X})_{*}} (\operatorname{ev}_{\Sigma X})_{*}$$

$$H_{i+1}(\Sigma X)$$

is an isomorphism mod **C** for i < 2n: so the same is true for  $(\sigma_X)_*$ . Now we can apply the mod **C** Whitehead theorem to conclude:

**Theorem 32.3** (Mod **C** Freudenthal suspension theorem). Let **C** be an acyclic Serre ideal and  $n \geq 1$ . Let X be a simply connected space such that  $\overline{H}_i(X)$  is zero mod **C** for i < n. Then the suspension map

$$\pi_i(X) \to \pi_i(\Omega \Sigma X) = \pi_{i+1}(\Sigma X)$$

is a mod C isomorphism for i < 2n-1 and a mod C epimorphism for i = 2n-1.

Corollary 32.4. Let  $n \geq 2$ . The suspension map

$$\pi_i(S^n) \to \pi_{i+1}(S^{n+1})$$

is an isomorphism for i < 2n - 1 and an epimorphism for i = 2n - 1.

For example,  $\pi_2(S^2) \to \pi_3(S^3)$  is an isomorphism (the degree is a stable invariant), while  $\pi_3(S^2) \to \pi_4(S^3)$  is only an epimorphism: the Hopf map  $S^3 \to S^2$  suspends to a generator of  $\pi_4(S^3)$ , which as we saw has order 2.

In any case, the Freudenthal suspension theorem show that the sequence

$$\pi_k(X) \to \cdots \to \pi_{n+k}(\Sigma^n X) \to \pi_{n+1+k}(\Sigma^{n+1} X) \to \cdots$$

stabilizes. The direct limit is the reduced kth stable homotopy group of the pointed space X,  $\pi_k^s(X)$ . These functors turn out to form a generalized homology theory. The coefficients form a graded commutative ring, the stable homotopy ring

$$\pi_*^s = \pi_*^s(S^0) = \lim_{n \to \infty} \pi_{*+n}(S^n).$$

#### EHP sequence

The homotopy groups of spheres are related to each other via the suspension maps, but it turns out that there is more, based on the following theorem of Ioan James. (Ioan Mackenzie James (1928–) worked mainly at Oxford.)

**Proposition 32.5.** Let  $n \geq 2$ . There is a map  $h: \Omega S^n \to \Omega S^{2n-1}$  that induces an isomorphism in  $H_{2n-2}(-)$ .

Granting this, we can compute the entire effect in cohomology. When n is even, n=2k, the generator  $y \in H^{4k-2}(\Omega S^{4k-1})$  hits the divided power generator in  $H^{4k-2}(\Omega S^{2k})$ , and hence embeds  $H^*(\Omega S^{4k-1})$  into  $H^*(\Omega S^{2k})$  isomorphically in dimensions divisible by (4k-2). The induced map in homology thus has the same behavior. It follows that the homotopy fiber has the homology of  $S^{2k-1}$ . But the suspension map  $S^{2k-1} \to \Omega S^{2k}$  certainly composes into  $\Omega S^{4k-1}$  to a null map, and hence lifts to a map to the homotopy fiber inducing a homology isomorphism. By Whitehead's theorem, it is a weak equivalence.

The Whitehead square  $w_{2k}: S^{4k-1} \to S^{2k}$  has the property that the composite

$$\Omega S^{4k-1} \xrightarrow{\Omega w_{2k}} \Omega S^{2k} \xrightarrow{h} \Omega S^{4k-1}$$

is an isomorphism in homology away from 2. So, using the multiplication in  $\Omega S^{2k}$ , there is a map,

$$S^{2k-1} \times \Omega S^{4k-1} \to \Omega S^{2k}$$

that induces an isomorphism in homology away from 2, and hence by the mod  $\mathbf{C}$  Whitehead theorem in homotopy away from 2. For this reason, even spheres are not very interesting homotopy theoretically away from 2.

When n is odd,  $y \in H^{2n-2}(\Omega S^{2n-1})$  maps to the divided square of  $x \in H^{n-1}(\Omega S^n)$ . This implies that

$$\gamma_k(y) = \frac{y^k}{k!} \mapsto \frac{(x/2)^k}{k!} = \frac{(2k)!}{2^k k!} \gamma_{2k}(x).$$

A little thought shows that the fraction here is odd, so the map is still an isomorphism in  $\mathbb{Z}_{(2)}$  homology in dimensions divisible by 2n-2, and hence the fiber has the 2-local homology of  $S^{n-1}$ . The mod  $\mathbb{C}_2$  Whitehead theorem shows that it also has the 2-local homotopy of  $S^{n-1}$ . We conclude:

**Theorem 32.6.** For any positive even integer n there is a fiber sequence

$$S^{n-1} \to \Omega S^n \to \Omega S^{2n-1}$$
.

Localized at 2, this sequence exists for n odd as well.

The long exact homotopy sequence then gives us the EHP sequence

of homotopy groups (localized at 2 if n is odd).

These sequences link together to form an exact couple! You can see this clearly from the diagram of fiber sequences obtained by looping down the sequences of Theorem 32.6. Locally at 2, we have a diagram in which each L is a fiber sequence.

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

The limiting space  $\Omega^{\infty} S^{\infty}$  has homotopy equal to  $\pi_*^s$ .

The resulting spectral sequence, the EHP spectral sequence, has the form

$$E_{s,t}^1 = \pi_{2s+1+t}(S^{2s+1}) \Longrightarrow_s \pi_{s+t}^s$$
.

Here's a picture, taken from [23]. In it,  $2^3$  represents the elementary abelian group of order 8 and " $\infty$ " means an infinite cyclic group.

FIGURE 3. The EHP spectral sequence

#### **Bousfield localization**

I can't leave the subject of Serre classes without mentioning a more recent and more geometric approach to localization in algebraic topology, due to Bousfield (following diverse early ideas of Dennis Sullivan, Mike Artin and Barry Mazur, and Frank Adams). (A. K. ("Pete") Bousfield was a student of Dan Kan's at MIT.)

**Theorem 32.7** (Bousfield, [3]). Let  $E_*$  be any generalized homology theory and X any CW complex. There is a space  $L_EX$  and a map  $X \to L_EX$  that is terminal in the homotopy category among  $E_*$ -equivalences from X.

So  $L_E X$  is as far away (to the right) from X as possible while still receiving an  $E_*$ -equivalence from it. The localization strips away all features not detected by E-homology.

The class of maps given by  $E_*$ -equivalences determines a class of objects: A space W is  $E_*$ -local if for every  $E_*$ -equivalence  $X \to Y$  between CW complexes the induced map  $[X, W] \leftarrow [Y, W]$  is bijective. You can't tell two  $E_*$ -equivalent spaces apart by mapping them into an  $E_*$ -local space.

**Theorem 32.8** (Addendum to Theorem 32.7). For any CW complex X,  $L_EX$  is  $E_*$ -local, and the localization map  $X \to L_EX$  is initial among maps to  $E_*$ -local spaces.

The functor  $L_E$  is "Bousfield localization" at the homology theory  $E_*$ . The subcategory of  $E_*$ -local spaces affords the ultimate extension of the Whitehead theorem:

**Lemma 32.9.** Any  $E_*$ -equivalence  $f: X \to Y$  between  $E_*$ -local CW complexes is a homotopy equivalence.

*Proof.* Take W = X in the definition of " $E_*$ -local": then the identity map  $X \to X$  lifts in the homotopy category uniquely through a map  $g: Y \to X$ . By construction  $gf = 1_X$ . But then both fg and  $1_Y$  lift  $f: X \to Y$  across f, and hence must be equal by uniqueness.

So the Whitehead theorem can be phrased as saying that any simply connected CW complex is  $H\mathbb{Z}_*$ -local.

Another example is given by rational homology  $H\mathbb{Q}_*$ .

**Proposition 32.10.** A simply connected CW complex is  $H\mathbb{Q}_*$ -local if and only if its homology in each positive dimension is a rational vector space.

In this case we can also compute the homotopy: For a simply connected CW complex X,  $\pi_*(X) \to \pi_*(L_{H\mathbb{Q}}X)$  simply tensors the homotopy with  $\mathbb{Q}$ . This is the beginning of an extensive development of "rational homotopy theory," pioneered independently by Daniel Quillen and Dennis Sullivan. The entire homotopy theory of simply connected rational spaces of finite type over  $\mathbb{Q}$  is equivalent to the opposite of the homotopy theory of commutative differential graded  $\mathbb{Q}$ -algebras that are simply connected and of finite type. The quest for analogous completely algebraic descriptions of other sectors of homotopy theory has been a major research objective over the past half century.

Bousfield localization at  $H\mathbb{F}_p$  is trickier, because the map from  $S^n$  to the Moore space M with homology given by the p-adic integers  $\mathbb{Z}_p$  in dimension n is an isomorphism in mod p homology. In fact  $L_{H\mathbb{F}_p}S^n=M$ : so in this case Bousfield localization behaves like a completion.

When the fundamental group is nontrivial, even localization at  $H\mathbb{Z}$  can lead to unexpected results. For example, let  $\Sigma_{\infty}$  be the group of permutations of a countably infinite set that move only finitely many elements. Then

$$L_{H\mathbb{Z}}B\Sigma_{\infty}\simeq\Omega_{0}^{\infty}S^{\infty}$$
.

a single component of the union of  $\Omega^s S^s$ 's. This is the "Barratt-Priddy-Quillen theorem."

For another example, let R be a ring and  $GL_{\infty}(R)$  the increasing union of the groups  $GL_n(R)$ . The homotopy groups of the space  $L_{H\mathbb{Z}}BGL_{\infty}(R)$  formed Quillen's first definition of the higher algebraic K-theory of R.

# Chapter 5

# Characteristic classes, Steenrod operations, and cobordism

# 33 Chern classes, Stiefel-Whitney classes, and the Leray-Hirsch theorem

A good supply of interesting geometric objects is provided by the theory of principal G-bundles, for a topological group G. For example giving a principal  $GL_n(\mathbb{C})$ -bundle over X is the same thing as giving a complex n-plane bundle over X.

Principle bundles reflect a great deal of geometric information in their topology. This is a great asset, but it can make them correspondingly hard to visualize. It's reasonable to hope to construct invariants of principal G-bundles of some more understandable sort. A good candidate is a cohomology class.

So let's fix an integer n and an abelian group A, and try to associate, in some way, a class  $c(\xi) \in H^n(Y; A)$  to any principal G-bundle  $\xi$  over Y. To make this useful, this association should be natural: given  $f: X \to Y$  and a principal G-bundle  $\xi$  over Y, we can pull  $\xi$  back under f to a principal G-bundle  $f^*\xi$  over X, and find ourselves with two classes in  $H^n(X; A)$ :  $f^*c(\xi)$  and  $c(f^*(\xi))$ . Naturality insists that these two classes coincide. This means, incidentally, that  $c(\xi)$  depends only on the isomorphism class of  $\xi$ . Let  $\operatorname{Bun}_G(X)$  denote the set of isomorphism classes of principal G-bundles over X; it is a contravariant functor of X. We have come to the definition:

**Definition 33.1.** Let G be a topological group, A an abelian group, and  $n \geq 0$ . A *characteristic class* for principal G-bundles with values in  $H^n(-; A)$  is a natural transformation of functors  $\mathbf{Top} \to \mathbf{Set}$ :

$$c: \operatorname{Bun}_G(X) \to H^n(X; A)$$
.

Cohomology classes are more formal or algebraic, and are correspondingly relatively easy to work with.  $\operatorname{Bun}_G(X)$  is often hard (or impossible) to compute, partly because it has no algebraic structure and partly exactly because its elements are interesting geometrically, while  $H^n(X;A)$  is relatively easy to compute but its elements are not very geometric. A characteristic class provides a bridge between these two, and information flows across this bridge in both directions. It gives computable information about certain interesting geometric objects, and provides a geometric interpretation of certain formal or algebraic things.

**Example 33.2.** The Euler class is the first and most fundamental characteristic class. Let R be a commutative ring. The Euler class takes an R-oriented real n-plane bundle  $\xi$  and produces an

n-dimensional cohomology class  $e(\xi)$ , given by the transgression of the class in  $H^0(B; H^{n-1}(\mathbb{S}\xi))$  that evaluates to 1 on every orientation class. Naturality of the Gysin sequence shows that this assignment is natural. There are really only two cases:  $R = \mathbb{Z}$  and  $R = \mathbb{F}_2$ . A  $\mathbb{Z}$ -orientation of a vector bundle is the same thing as an orientation in the usual sense, and the Euler class is a natural transformation

$$e: \operatorname{Vect}_n^{or}(X) = \operatorname{Bun}_{SO(n)}(X) \to H^n(X; \mathbb{Z})$$
.

Any vector bundle is canonically  $\mathbb{F}_2$ -oriented, so the mod 2 Euler class is a natural transformation

$$e: \operatorname{Vect}_n(X) = \operatorname{Bun}_{O(n)}(X) \to H^n(X; \mathbb{F}_2)$$
.

On CW complexes,  $\operatorname{Bun}_G(-)$  is representable: there is a "universal" principal G-bundle  $\xi_G:EG\downarrow BG$  such that

$$[X, BG] \to \operatorname{Bun}_G(X), \quad f \mapsto f^* \xi_G$$

is a bijection. A characteristic classes  $\operatorname{Bun}_G(-) \to H^n(-; A)$  is the same thing as a class in  $H^n(BG; A)$ , or, since cohomology is also representable, as a homotopy class of maps  $BG \to K(A, n)$ .

Thus for example set of all integral characteristic classes of complex line bundles is given by  $H^*(BU(1)) = \mathbb{Z}[e]$ . Is there an analogous classification of characteristic classes for higher dimensional complex bundles? How about real bundles?

#### Chern classes

We'll begin with complex vector bundles. Any complex vector bundle (numerable of course) admits a Hermitian metric, well defined up to homotopy. This implies that  $\operatorname{Bun}_{U(n)}(X) \to \operatorname{Bun}_{GL_n(\mathbb{C})}(X)$  is bijective;  $BU(n) \to BGL_n(\mathbb{C})$  is a homotopy equivalence. I will tend to favor using U(n) and BU(n).

A finite dimensional complex vector space V determines an orientation of the underlying real vector space: Pick an ordered basis  $(e_1, \ldots, e_n)$  for V over  $\mathbb{C}$ , and provide V with the ordered basis over  $\mathbb{R}$  given by  $(e_1, ie_1, \ldots, e_n, ie_n)$ . The group  $\operatorname{Aut}_{\mathbb{C}}(V)$  acts transitively on the space of complex bases. But choosing a basis for V identifies  $\operatorname{Aut}(V)$  with  $GL_n(\mathbb{C})$ , which is path connected. So the set of oriented real bases obtained in this way are all in the same path component of the set of all oriented real bases, and hence defines an orientation of V.

This construction yields a natural transformation  $\operatorname{Vect}_{\mathbb{C}}^{(r)}(-) \to \operatorname{Vect}_{\mathbb{R}}^{or}(-)$ . In particular, the real 2-plane bundle underlying a complex line bundle has a preferred orientation – the determined in each fiber  $\xi_x$  by (v, iv) where  $v \neq 0$  in  $\xi_x$ . A complex line bundle  $\xi$  over B thus has a well-defined Euler class  $e(\xi) \in H^2(B; \mathbf{Z})$ .

**Theorem 33.3** (Chern classes). There is a unique family of characteristic classes for complex vector bundles that assigns to a complex n-plane bundle  $\xi$  over X its kth Chern class  $c_k^{(n)}(\xi) \in H^{2k}(X; \mathbf{Z})$ ,  $k \in \mathbb{N}$ , such that:

- $c_0^{(n)}(\xi) = 1.$
- $c_1^{(1)}(\xi) = -e(\xi)$ .
- The Whitney sum formula holds: if  $\xi$  is a p-plane bundle and  $\eta$  is a q-plane bundle, then

$$c_k^{(p+q)}(\xi \oplus \eta) = \sum_{i+j=k} c_i^{(p)}(\xi) \cup c_j^{(q)}(\eta) \in H^{2k}(X; \mathbf{Z}).$$

33. CHERN CLASSES 121

Moreover, if  $\xi_n$  is the universal n-plane bundle, then

$$H^*(BU(n); \mathbf{Z}) \cong \mathbf{Z}[c_1^{(n)}, \dots, c_n^{(n)}]$$

where 
$$c_k^{(n)} = c_k^{(n)}(\xi_n)$$
.

This result says that all characteristic classes for complex vector bundles are given by polynomials in the Chern classes, and that there are no universal algebraic relations among the Chern classes. (Shiing-Shen Chern (1911–2004) was a father of twentieth century differential geometry, and a huge force in the development of mathematics in China.)

**Remark 33.4.** Since BU(n) supports the universal n-plane bundle  $\xi_n$ , the Chern classes  $c_k^{(n)} = c_k^{(n)}(\xi_n)$  are themselves universal, pulling back to the Chern classes of any other n-plane bundle.

The (p+q)-plane bundle  $\xi_p \times \xi_q = \operatorname{pr}_1^* \xi_p \oplus \operatorname{pr}_2^* \xi_q$  over  $BU(p) \times BU(q)$  is classified by a map  $\mu: BU(p) \times BU(q) \to BU(p+q)$ . The Whitney sum formula computes the effect of  $\mu$  on cohomology:

$$\mu^*(c_k^{(n)}) = \sum_{i+j=k} c_i^{(p)} \times c_j^{(q)} \in H^{2k}(BU(p) \times BU(q)),$$

where, you'll recall,  $x \times y = \operatorname{pr}_1^* x \cup \operatorname{pr}_2^* y$ .

The Chern classes are "stable" in the following sense. Let  $\epsilon$  be the trivial one-dimensional complex vector bundle over X and let  $\xi$  be an n-dimensional vector bundle over X. What is  $c_k^{(n+q)}(\xi \oplus q\epsilon)$ ? The trivial bundle is obtained by pulling back under  $X \to *$ :

$$X \times \mathbf{C}^q = E(q\epsilon) \longrightarrow \mathbf{C}^q$$

$$\downarrow \qquad \qquad \downarrow$$

$$X \longrightarrow *$$

By naturality, we find that  $c_j^{(n)}(n\epsilon) = 0$  for j > 0. The Whitney sum formula therefore implies that

$$c_k^{(n+q)}(\xi \oplus q\epsilon) = c_k^{(n)}(\xi).$$

Thus the Chern class only depends on the "stable equivalence class" of the vector bundle. Also, the map  $BU(n-1) \to BU(n)$  classifying  $\xi_{n-1} \oplus \epsilon$  sends  $c_k^{(n)}$  to  $c_k^{(n-1)}$  for k < n and  $c_n^{(n)}$  to 0.

For this reason, we will drop the superscript on  $c_k^{(n)}(\xi)$ , and simply write  $c_k(\xi)$ .

#### Grothendieck's construction

Let  $\xi: E \xrightarrow{p} X$  be a complex *n*-plane bundle. Associated to it is a fiber bundle whose fiber over  $x \in X$  is  $\mathbb{P}(p^{-1}(x))$ , the projective space of the vector space given by the fiber of  $\xi$  over x. This "projectivization" can also be described using the  $GL_n(\mathbb{C})$  action on  $\mathbb{C}P^{n-1} = \mathbb{P}(\mathbb{C}^n)$  induced from its action on  $\mathbb{C}^n$ , and forming the balanced product

$$\mathbb{P}(\xi) = P \times_{GL_n(\mathbb{C})} \mathbf{C} P^{n-1}$$

where  $P \downarrow X$  is the principalization of  $\xi$ .

Let us attempt to compute the cohomology of  $\mathbb{P}(\xi)$  using the Serre spectral sequence:

$$E_2^{s,t} = H^s(X; H^t(\mathbf{C}P^{n-1})) \Rightarrow H^{s+t}(\mathbb{P}(\xi)).$$

We claim that this spectral sequence almost completely determines the cohomology of  $\mathbb{P}(\xi)$  as a ring. Here is a general theorem that tells us what to look for, and what we get.

**Theorem 33.5** (Leray-Hirsch). Let  $\pi: E \to B$  be a fibration and R a commutative ring. Assume that B is path connected, so that the fiber is well defined up to homotopy. Call it F, and suppose that for each t the R-module  $H^t(F)$  is free of finite rank. Finally, assume that the restriction  $H^*(E) \to H^*(F)$  is surjective. (One says that the fibration is "totally non-homologous to zero.") Because  $H^t(F)$  is a free R-module for each t, the surjection  $H^*(E) \to H^*(F)$  admits a splitting; pick one, say  $s: H^*(F) \to H^*(E)$ . The projection map renders  $H^*(E)$  a module over  $H^*(B)$ . The  $H^*(B)$ -linear extension of s,

$$\overline{s}: H^*(B) \otimes_R H^*(F) \to H^*(E)$$

is then an isomorphism of  $H^*(B)$ -modules.

*Proof.* First we claim that the group  $\pi_1(B)$  acts trivially on the cohomology of  $F = \pi^{-1}(*)$ . The map of fibrations

$$E \xrightarrow{1} E$$

$$\downarrow^{\pi} \qquad \downarrow$$

$$B \xrightarrow{*} *$$

shows that the map  $H_*(F) \to H_*(E)$  is equivariant with respect to the group homomorphisms  $\pi_1(B) \to \pi_1(*)$ . In cohomology, this says that the restriction  $H^*(E) \to H^*(F)$  has image in the  $\pi_1(B)$ -invariant subgroup (which, by the way, is  $H^0(B; H^*(F))$ ). So the assumption that this map is surjective guarantees that the action of  $\pi_1(B)$  on  $H_*(F)$  is trivial.

Now the edge homomorphism in the Serre spectral sequence

$$E_2^{s,t} = H^s(B; H^t(F)) \Longrightarrow_s H^{s+t}(E)$$

is that restriction map. Our assumption that  $H^t(F)$  is free of finite rank implies that

$$E_2^{s,t} = H^s(B) \otimes_R H^t(F)$$

as R-algebras. All the generators lie on either t = 0 or s = 0. The ones on the base survive because the differentials hit zero groups. The generators on the fiber survive by assumption. So inductively you find that  $E_r = E_{r+1}$ , and hence that the entire spectral sequence collapses at  $E_2$ .

We now define a new filtration on  $H^*(E)$  with the advantage that it is a filtration by  $H^*(B)$ modules. I call it the "Quillen filtration," though it is probably older. It's the *increasing* filtration
given by

$$F_tH^n(E) = F^{n-t}H^n(E)$$
.

For instance,  $F_0H^n(E) = F^nH^n(E) = \operatorname{im}(H^n(B) \to H^n(E)) \cong H^n(B)$ ; or

$$F_0H^*(E) = \operatorname{im}(H^*(B) \to H^*(E))$$
.

On the level of associated graded modules,

$$\operatorname{gr}_t H^n(E) = F^{n-t} H^n(E) / F^{n-t+1} H^n(E) = E_{\infty}^{n-t,t}$$

- that is, the tth row: so

$$\operatorname{gr}_t H^*(E) = E_{\infty}^{*,t} = E_2^{*,t} = H^*(B) \otimes H^t(F)$$

Now we can think about the map  $\overline{s}: H^*(B) \otimes H^*(F) \to H^*(E)$ . Filter  $H^*(B) \otimes H^*(F)$  by degree in  $H^*(F)$ :

$$F_t(H^*(B) \otimes H^*(F)) = H^*(B) \otimes \bigoplus_{i < t} H^i(F).$$

33. CHERN CLASSES 123

The map  $\overline{s}$  respects filtrations and is an isomorphism on associated graded modules: so it is an isomorphism.

Returning now to the example of the projectivization of a vector bundle,  $\mathbb{P}(\xi) \downarrow X$ , the hypotheses of the Leray-Hirsch Theorem are satisfied except perhaps surjectivity of the restriction to the fiber.

Here's where the representation of a cohomology class as a characteristic class comes in useful. The cohomology of the fiber over  $x \in X$  is generated as an R-module by powers of the Euler class of the canonical line bundle  $\lambda_x$  over  $\mathbb{P}(\xi_x)$ . Since  $i^*: H^*(E) \to H^*(\mathbb{C}P^{n-1})$  is an R-algebra map, it will suffice to see that  $e(\lambda_x)$  is in the image of  $i^*$ . Since the Euler class is natural, the natural thing to do is to construct a line bundle over the whole of  $\mathbb{P}(\xi)$  that restricts to  $\lambda_x$  on  $\xi_x$ . And indeed these line bundles over fibers assemble themselves into a tautologous line bundle, call it  $\lambda$ , over  $\mathbb{P}(\xi)$ .

So we have an expression for  $H^*(\mathbb{P}(\xi))$  as a module over  $H^*(X)$ :

$$H^*(\mathbb{P}(\xi)) = H^*(X)\langle 1, e, e^2, \dots, e^{n-1} \rangle$$
.

where  $e = e(\lambda) \in H^2(\mathbb{P}(\xi))$ . This gives us some information about the algebra structure in  $H^*(\mathbb{P}(\xi))$ , but not complete information. What is lacking is an expression for  $e^n$  in terms of the basis given by lower powers of e. The Euler class e satisfies a unique monic polynomial equation  $c_{\xi}(e) = 0$ , where  $c_{\xi}(t)$  is the "Chern polynomial"

$$c_{\xi}(t) = t^n + c_1 t^{n-1} + \dots + c_{n-1} t + c_n$$
.

with  $c_k \in H^{2k}(X)$ .

The naturality of this construction guarantees that the  $c_k$ 's are natural in the n-plane bundle  $\xi$ ; they are characteristic classes. We will see that they satisfy the axioms for Chern classes set out above.

Note that the Whitney sum formula has a nice expression in terms of the Chern polynomials:

$$c_{\xi}(t)c_{\eta}(t) = c_{\xi \oplus \eta}(t)$$
.

#### Stiefel-Whitney classes

Exactly parallel theorems hold for real n-plane bundles, with mod 2 coefficients:

**Theorem 33.6** (Stiefel-Whitney classes). There is a unique family of characteristic classes for real vector bundles that assigns to a real n-plane bundle  $\xi$  over X its "kth Stiefel-Whitney class"  $w_k(\xi) \in H^{2k}(X; \mathbb{F}_2), k \in \mathbb{N}$ , such that:

- $w_0(\xi) = 1$ .
- If n = 1 then  $w_1(\xi) = e(\xi)$ .
- The Whitney sum formula holds: if  $\xi$  is a p-plane bundle and  $\eta$  is a q-plane bundle, then

$$w_k(\xi \oplus \eta) = \sum_{i+j=k} w_i(\xi) \cup w_j(\eta) \in H^{2k}(X; \mathbb{F}_2).$$

Moreover, if  $\xi_n$  is the universal n-plane bundle, then

$$H^*(BO(n); \mathbb{F}_2) \cong \mathbb{F}_2[w_1, \dots, w_n]$$

where  $w_k = w_k(\xi_n)$ .

And the same construction produces them:

$$H^*(\mathbb{P}(\xi); \mathbb{F}_2) = H^*(B; \mathbb{F}_2)[e]/(e^n + w_1e^{n-1} + \dots + w_{n-1}e + w_n)$$

for unique elements  $w_i \in H^i(B; \mathbb{F}_2)$ .

Remark 33.7. The Euler class depends only on the sphere bundle of the vector bundle  $\xi$ , but these constructions depend heavily on the existence of an underlying vector bundle. This is a genuine dependence in the case of Chern classes, but it turns out that the Stiefel-Whitney classes depend only on the sphere bundle. We'll explain this a little while.

Remark 33.8. In the complex case, the triviality of the local coefficient system can be verified in other ways as well. After all, the action of  $\pi_1(X)$  on the fiber  $H^*(\mathbb{C}P^{n-1})$  is compatible with the action of  $\pi_1(BU(n))$  on the homology of the fiber of the projectivized universal example. But since U(n) is connected, its classifying space is simply connected.

You can't make this argument in the real case, but then you don't have to since we are looking at an action of  $\pi_1(B)$  on a one-dimensional vector space over  $\mathbb{F}_2$ .

**Example 33.9.** Complex projective space  $\mathbb{C}P^n$  is a complex manifold, and its tangent bundle is thereby endowed with a complex structure. A standard argument shows that

$$\tau_{\mathbf{C}P^n} = \mathrm{Hom}(\lambda, \lambda^{\perp}).$$

Adding  $\epsilon = \operatorname{Hom}(\lambda, \lambda)$ , we find

$$\tau_{{\bf C}P^n} \oplus \epsilon = (n+1)\lambda$$
.

Thus by the Whitney sum formula

$$c_{\tau}(t) = c_{\tau \oplus \epsilon}(t) = c_{\lambda}(t)^{n+1} = (1-e)^{n+1}$$

and so

$$c_k(\tau_{\mathbb{C}P^n}) = (-1)^k \binom{n+1}{k} e^k.$$

# 34 $H^*(BU(n))$ and the splitting principle

Here's another description of the Chern classes.

**Theorem 34.1.** Let  $n \geq 1$ . There is a unique family of characteristic classes  $c_i(\xi) \in H^{2i}(B(\xi))$ ,  $1 \leq i \leq n$ , for complex n-plane bundles  $\xi$  such that if  $\xi$  is isomorphic to  $\zeta \oplus (n-i)\epsilon$  then

$$c_i(\xi) = (-1)^i e(\zeta)$$

where  $e(\zeta)$  is the Euler class of the oriented real 2i-bundle underlying  $\zeta$ . These classes generate all characteristic classes for n-plane bundles and there are no universal algebraic relations among them.

We will prove this by computing the cohomology of BU(n), by induction on n. Here's how BU(n) and BU(n-1) are related. Embed  $U(n-1) \hookrightarrow U(n)$  by

$$A \mapsto \left[ \begin{array}{cc} A & 0 \\ 0 & 1 \end{array} \right] .$$

This subgroup is exactly the set of matrices fixing the last basis vector  $e_n$  in  $\mathbb{C}^n$ . The orbit of  $e_n$  is the subspace  $S^{2n-1}$  of unit vectors in  $\mathbb{C}^n$ , which is thus identified with the homogeneous space U(n)/U(n-1).

Make a choice of EU(n) – a contractible on which U(n) acts principally – the Stiefel model  $V_n(\mathbb{C}^{\infty})$  for example. The orbit space is then the Grassmann model for BU(n). The subgroup U(n-1) also acts principally on EU(n), so we get a model for BU(n-1):

$$BU(n-1) = EU(n)/U(n-1) = (EU(n) \times_{U(n)} U(n))/U(n-1) =$$

$$EU(n) \times_{U(n)} (U(n)/U(n-1)) = EU(n) \times_{U(n)} S^{2n-1}.$$

This establishes  $p: BU(n-1) \to BU(n)$  as the unit sphere bundle in the universal complex n-plane bundle  $\xi_n$ . The map  $BU(n-1) \to BU(n)$  classifies the n-plane bundle  $\xi_{n-1} \oplus \epsilon$ .

Here's a restatement of Theorem 34.1 in terms of universal examples.

**Theorem 34.2.** There exist unique classes  $c_i \in H^{2i}(BU(n))$  for  $1 \le i \le n$  such that:

1. the map  $p_*: H^*(BU(n)) \to H^*(BU(n-1))$  sends

$$c_i \mapsto \begin{cases} c_i & for & i < n \\ 0 & for & i = n \end{cases}$$

2. the Euler class e of the oriented real 2n-plane bundle underlying the universal complex n-plane bundle  $\xi_n$  is related to the top class  $c_n$  by the equation

$$c_n = (-1)^n e \in H^{2n}(BU(n)).$$

Moreover,

$$H^*(BU(n)) = \mathbf{Z}[c_1,\ldots,c_n].$$

We postpone the verification that the classes we constructed in the last lecture coincide with these.

*Proof.* We will study the Gysin sequence of the spherical fibration

$$S^{2n-1} \to BU(n-1) \xrightarrow{p} BU(n)$$
.

For a general oriented spherical fibration

$$S^{2n-1} \to E \xrightarrow{p} B$$

the Gysin sequence takes the form

$$\cdots \to H^{q-1}(E) \xrightarrow{p_*} H^{q-2n}(B) \xrightarrow{e^*} H^q(B) \xrightarrow{p^*} H^q(E) \xrightarrow{p_*} H^{q-2n+1}(B) \to \cdots$$

where  $e \in H^{2n}(B)$  is the Euler class.

Suppose we know that  $H^*(E)$  vanishes in odd dimensions. Then either the source or the target of each instance of the Umkher map  $p_*$  is zero, so we receive a short exact sequence

$$0 \to H^{q-2n}(B) \xrightarrow{e} H^q(B) \xrightarrow{p^*} H^q(E) \to 0$$
.

This shows several things:

- $e \in H^{2n}(B)$  is a non-zero-divisor;
- $p^*$  is surjective and induces an isomorphism  $H^*(B)/(e) \to H^*(E)$ ;
- $p^*$  is an isomorphism in dimensions less than 2n;
- $H^q(B) = 0$  for q odd.

The last is clear for q < 2n, but feeding this into the leftmost term we find by induction that  $H^q(B) = 0$  for all odd q.

Now let's suppose in addition that  $H^*(E)$  is a polynomial algebra. Lift the generators to elements in  $H^*(B)$ . (If they all happen to lie in dimension less than 2n, these lifts are unique.) Extending to a map of algebras gives a map  $H^*(E) \to H^*(B)$ . Further adjoining e gives us an algebra map

$$H^*(E)[e] \to H^*(B)$$

which when composed with  $p^*$  kills e and maps  $H^*(E)$  by the identity. We claim this map is an isomorphism. To see this, filter both sides by powers of e. Modulo e this map is an isomorphism from what we observed above. On both sides, multiplication by e induces an isomorphism from one associated quotient to the next, so the map induces an isomorphism on associated graded modules. The five-lemma shows that it induces an isomorphism mod  $e^k$  for any e. But the powers of e increase in dimension, so we obtain an isomorphism in each dimension.

These observations provide the inductive step. All that remains is to start the induction. We can, if we like, use what we know about  $H^*(\mathbb{C}P^{\infty})$  and start with n=2, though starting at n=1 makes sense too, and provides another perspective on the computation of  $H^*(\mathbb{C}P^{\infty})$ .

We define  $c_n \in H^{2n}(BU(n))$  to be  $(-1)^n e(\xi_n)$ , also a generator. The choice of sign will make it agree with our earlier definition.

Once we verify that these classes coincide with the classes constructed in the last lecture, we will have available an important interpretation of the top Chern class: up to sign it is the Euler class of the underlying oriented real vector bundle.

#### The splitting principle

A wonderful fact about Chern classes is that it suffices to check relations among them on sums of line bundles. This is captured by the following theorem.

**Theorem 34.3** (Splitting principle). Let  $\xi : E \downarrow X$  be a complex n-plane bundle. There exists a map  $f : \operatorname{Fl}(\xi) \to X$  such that:

- 1.  $f^*\xi \cong \lambda_1 \oplus \cdots \oplus \lambda_n$ , where the  $\lambda_i$  are line bundles on  $Fl(\xi)$ , and
- 2. the map  $f^*: H^*(X) \to H^*(Fl(\xi))$  is monic.

*Proof.* We have already done the hard work, in our study of the projectivization  $\pi: \mathbb{P}(\xi) \to X$ . We found that the Serre spectral sequence collapses at  $E^2$ . This implies that the projection map induces a monomorphism in cohomology. We used the "tautologous" line bundle  $\lambda$  on  $\mathbb{P}(\xi)$ . The key additional point about this construction is that there is a canonical embedding  $\lambda \hookrightarrow \pi^*\xi$  of vector bundles over  $\mathbb{P}(\xi)$ . A vector in  $E(\lambda)$  is  $(v \in L \subseteq \xi_x)$  (where L is a line in the fiber  $\xi_x$ ). A vector in the pullback  $\pi^*\xi$  is  $(v \in \xi_x, L \subseteq \xi_x)$ .

By picking a metric on  $\xi$  we see that when pulled back to  $\mathbb{P}(\xi)$  a line bundle splits off. Now just induct (using our important standing assumption that vector bundles have finite dimensional fibers).

It's worth being more explicit about what this "flag bundle"  $\operatorname{Fl}(\xi)$  is. The complement of  $\lambda$  in  $\pi^*\xi$  over  $\mathbb{P}(\xi)$  is the the space of vectors of the form  $(v \in L^{\perp}, L \subseteq \xi_x)$ . If we iterated this construction, we will get, in the end, the space of ordered orthogonal decompositions of fibers into lines. This can be built as a balanced product. Let  $\operatorname{Fl}_n$  be the space of "orthogonal flags," that is, decompositions of  $\mathbb{C}^n$  into an ordered sequence of n 1-dimensional subspaces. There is an evident action of U(n) on this space, and

$$Fl(\xi) = P \times_{U(n)} Fl_n$$

where  $P \downarrow X$  is the principal U(n) bundle associated to  $\xi$  (and a choice of Hermitian metric).

The action of U(n) on  $\mathrm{Fl}_n$  is transitive, and the isotropy subgroup of  $(\mathbb{C}e_1,\ldots,\mathbb{C}e_n)$  is the subgroup of diagonal unitary matrices,

$$T^n = (S^1)^n \subseteq U(n) \,,$$

so

$$\operatorname{Fl}_n = U(n)/T^n$$
.

In the universal case, over BU(n),

$$\operatorname{Fl}(\xi_n) = EU(n) \times_{U(n)} (U(n)/T^n) = EU(n)/T^n = BT^n$$

and this is just a product of n copies of  $\mathbb{C}P^{\infty}$ . So we have discovered that

$$H^*(BU(n)) \hookrightarrow H^*(BT^n) = \mathbb{Z}[t_1, \cdots, t_n]$$

where  $t_i$  is the Euler class of the line bundle  $\operatorname{pr}_i^*\lambda$ , the pull back of the universal line bundle under the projection onto the *i*th factor of  $\mathbb{C}P^{\infty}$ . What is the image?

Well, the symmetric group  $\Sigma_n$  sits inside the unitary group as matrices with a single 1 in each column. The maximal torus  $T^n$  is sent to itself by conjugation by a permutation matrix, which has the effect of reordering the diagonal entries. In cohomology, the action permutes the generators. These permutation matrices also act by conjugation on all of U(n), but there they act trivially on  $H^*(BU(n))$  since any matrix is connected to the identity matrix by a path in U(n). The consequence is that the image of  $H^*(BU(n))$  lies in the symmetric invariants:

$$H^*(BU(n)) \hookrightarrow H^*(BT^n)^{\Sigma_n}$$
.

These symmetric invariants are well-studied in Algebra! Define the elementary symmetric polynomials  $\sigma_i$  as the coefficients in the product of  $t - t_i$ 's:

$$\prod_{i=1}^{n} (t - t_i) = \sum_{j=0}^{n} \sigma_j t^{n-j}$$

For example,

$$\sigma_0 = 1$$
 ,  $\sigma_1 = -\sum_{j=1}^n t_j$  ,  $\sigma_n = (-1)^n \prod_{j=1}^n t_j$ .

The theorem from algebra is that the elementary symmetric polynonomials are algebraically independent and generate the ring of symmetric invariants –

$$R[t_1,\ldots,t_n]^{\Sigma_n}=R[\sigma_1,\ldots,\sigma_n]$$

– over any coefficient ring R.

If we give each  $t_i$  a grading of 2, the elementary symmetric polynomials are homogeneous and  $|\sigma_i| = 2i$ .

So  $H^*(BU(n))$  embeds into a graded algebra of exactly the same size. This does not yet show that the embedding is surjective! For each q, we know that  $H^q(BU(n))$  embeds into  $H^q(BT^n)$  as a subgroup of the same rank. If L is a free abelian group of finite rank and L' is a subgroup, the little exact sequence

$$0 \to \operatorname{Tor}_1(L/L', \mathbb{F}_p) \to L' \otimes \mathbb{F}_p \to L \otimes \mathbb{F}_p$$

shows that the *p*-torsion in L/L' vanishes if  $L' \otimes \mathbb{F}_p \to L \otimes \mathbb{F}_p$  is injective. Now our argument above actually works for any coefficient ring, so  $H^*(BU(n); \mathbb{F}_p) \to H^*(BT^n; \mathbb{F}_p)$  is monic for any prime p. Because  $H^*(BU(n))$  is torsion free this says that  $H^*(BU(n)) \otimes \mathbb{F}_p \to H^*(BT^n) \otimes \mathbb{F}_p$  is monic for any prime. The result is that the index of  $H^*(BU(n))$  in  $H^*(BT^n)^{\Sigma_n}$  is prime to p for every prime number p, and so this injection must also be surjective.

We have proven most of:

**Theorem 34.4.** The inclusion  $T^n \hookrightarrow U(n)$  induces an isomorphism

$$H^*(BU(n)) \xrightarrow{\cong} H^*(BT^n)^{\Sigma_n}$$
.

Under this identification, the classes  $c_i$  constructed in Theorem 2 map to the elementary symmetric functions.

In the context of Chern classes, the elements  $t_i$  are called "Chern roots." The extension  $H^*(BU(n)) \hookrightarrow H^*(BT^n)$  adjoins the roots of the Chern polynomial

$$c(t) = t^n + c_1 t^{n-1} + \dots + c_n$$

**Remark 34.5.** Everything we have done admits a version for real vector bundles, with mod 2 coefficients. One point deserves some special attention: the argument we gave for why conjugation by a permutation induces the identity on  $H^*(BU(n))$  fails because the group O(n) is not path-connected. However, there is a better and more general argument available.

**Lemma 34.6.** Let G be any topological group and  $g \in G$ . The self-map of BG induced by conjugation by g is homotopic to the identity.

*Proof.* The proof is an easy exercise using the material from Lecture 21. We regard G as a topological category with one object. Conjugation induces an endofunctor  $c_g$ . A natural transformation from the identity to  $c_g$  is given by the morphism g:

$$\begin{array}{ccc}
* & \xrightarrow{g} & * \\
\downarrow h & \downarrow c_g(h) = ghg^{-1} \\
* & \xrightarrow{g} & * .
\end{array}$$

And natural transformations induce homotopies.

Of course the map  $c_g: BG \to BG$  is not homotopic to the identity through basepoint preserving homotopies! On  $\pi_1(BG) = \pi_0(G)$  it induces conjugation by  $[g] \in \pi_0(G)$ .

# 35 The Thom class and Whitney sum formula

We now have four perspectives on Chern classes:

- 1. Axiomatic
- 2. Grothendieck's definition in terms of  $H^*(\mathbb{P}(\xi))$
- 3. In terms of Euler classes
- 4. As elementary symmetric polynomials via the splitting principle

In this lecture we will explain why these are four facets of the same gem, though at the expense of introducing a new perspective on the Euler class. Developing that perspective lets us introduce another important construction in topology, the Thom space. We'll use that to verify that (3) and (4) agree. Then we'll prove the Whitney sum formula from this perspective. We'll take the identification of Chern classes with symmetric polynomials as the starting point.

#### Thom space and Thom class

Let  $\xi: E \xrightarrow{p} B$  be a real *n*-plane bundle. The *Thom space* is obtained by forming the one-point compactification of each fiber, and then identifying all the newly adjoined basepoints to a single point. If B is a compact Hausdorff space, this amounts to the one-point compactification of the total space  $E(\xi)$ .

Example 35.1. There is a canonical homeomorphism

$$\operatorname{Th}(\lambda^* \downarrow \mathbb{R}P^{n-1}) \to \mathbb{R}P^n$$
.

It is given by sending  $(\varphi \in L^*, L \subseteq \mathbb{R}^n)$  to the graph of  $\varphi$  in  $\mathbb{R}^n \times \mathbb{R}$ . This map embeds  $E(\lambda^*)$  into  $\mathbb{R}P^n$ , and misses only the line  $\mathbb{R}e_{n+1}$ . This establishes  $\mathbb{R}P^n$  as the one-point compactification of  $E(\lambda^*)$ . (It also shows that  $\lambda^*$  is the normal bundle of the linear embedding  $\mathbb{R}P^{n-1} \hookrightarrow \mathbb{R}P^n$ .)

By choosing a metric we get a different expression for the same space. Let  $\mathbb{D}(\xi)$  and  $\mathbb{S}(\xi) = \partial \mathbb{D}(\xi)$  denote the unit disk and unit sphere bundles. The Thom space of  $\xi$  is the quotient space

$$Th(\xi) = \mathbb{D}(\xi)/\mathbb{S}(\xi)$$
.

Rather than this quotient space, you may prefer to think of the pair  $(\mathbb{D}(\xi), \mathbb{S}(\xi))$ ; it is homotopy equivalent to the pair  $(E(\xi), E(\xi)\backslash Z)$ , where Z is the image of the zero-section.

Note that  $Th(0) = B/\emptyset = B_+$ , the base with a disjoint basepoint adjoined. The Thom space of the *n*-plane bundle over a point is  $D^n/\partial D^n = S^n$ .

An important point about the Thom space construction is its behavior on the product of two bundles, say  $\xi$  and  $\eta$ . Since

$$\partial(D^p \times D^q) = (\partial D^p \times D^q) \cup (D^p \times \partial D^q),$$

we find

$$\mathrm{Th}(\xi \times \eta) = \frac{\mathbb{D}(\xi \times \eta)}{\partial \mathbb{D}(\xi \times \eta)} = \frac{\mathbb{D}(\xi) \times \mathbb{D}(\eta)}{\mathbb{S}(\xi) \times \mathbb{D}(\eta) \cup \mathbb{D}(\xi) \times \mathbb{S}(\eta)} = \mathrm{Th}(\xi) \wedge \mathrm{Th}(\eta) \,.$$

In particular, if  $\eta$  is the *n*-plane bundle over a point,  $\xi \times \eta = \xi \oplus n\epsilon$  and

$$\operatorname{Th}(\xi \oplus n\epsilon) = \operatorname{Th}(\xi) \wedge S^n = \Sigma^n \operatorname{Th}(\xi).$$

In general, the Thom space is a "twisted n-fold suspension."

The Thom space construction is natural for bundle maps: Given  $f: B' \to B$ , covered by a bundle map  $\xi' \to \xi$  (so that  $\xi' \cong f^*\xi$ ) we get a canonical pointed map

$$\overline{f}: \operatorname{Th}(\xi') \to \operatorname{Th}(\xi)$$
.

This construction can be used to define a relative product in the cohomology of the Thom space, in the following way. Notice that the bundle  $0 \times \xi$  over  $B \times B$  is just the pullback of  $\xi$  under  $\operatorname{pr}_2: B \times B \to B$ . The diagonal map  $\Delta: B \to B \times B$  satisfies  $\operatorname{pr}_2 \circ \Delta = 1_B$ , and is therefore covered by a bundle map  $\xi \to 0 \times \xi$ , which then induces a twisted diagonal map

$$\operatorname{Th}(\xi) \to \operatorname{Th}(0) \wedge \operatorname{Th}(\xi) = B_+ \wedge \operatorname{Th}(\xi)$$
.

This in turn induces a "relative cup product" in cohomology:

$$\cup: H^*(B) \otimes \overline{H}^*(\operatorname{Th}(\xi)) \to \overline{H}^*(\operatorname{Th}(0) \wedge \operatorname{Th}(\xi)) \to \overline{H}^*(\operatorname{Th}(\xi)).$$

Since the diagonal map is associative and unital, this map defines on  $\overline{H}^*(\operatorname{Th}(\xi))$  the structure of a module over the graded ring  $H^*(B)$ .

Here is the essential fact about the Thom space.

**Proposition 35.2** (Thom isomorphism theorem). Let R be a commutative ring and let  $\xi$  be an R-oriented real n-plane bundle over B. There is a unique class  $U \in \overline{H}^n(\operatorname{Th}(\xi); R)$  that restricts on each fiber to the dual of the orientation class, and the map

$$-\cup U: H^*(B) \to \overline{H}^*(\operatorname{Th}(\xi))$$

is an isomorphism.

*Proof.* The proof is very simple, if you grant yet another relative form of the Serre spectral sequence. This time I want to have a fibration  $p: E \to B$  – say a fiber bundle – together with a subbundle  $p_0: E_0 \to B$ . Then there is spectral sequence

$$E_2^{s,t} = H^s(B; H^t(p^{-1}(-), p_0^{-1}(-))) \Longrightarrow_s H^{s+t}(E, E_0)$$

We will apply this to the fiber bundle pair  $(\mathbb{D}(\xi), \mathbb{S}(\xi))$ . The fiber pair is then  $(D^n, S^{n-1})$ , which has cohomology in just one dimension! This spectral sequence has just one row: the *n*th row. It collapses at  $E_2$ , there are no extension problems, and we get a canonical isomorphism

$$H^{s}(B; H^{n}(p^{-1}(-), p_{0}^{-1}(-))) \to H^{s+n}(\mathbb{D}(\xi), \mathbb{S}(\xi)) = \overline{H}^{s+n}(\mathrm{Th}(\xi)).$$

The assumed orientation identifies the local coefficient system with the constant system R. The generator of  $E_2^{0,n}$  survives to a class U that restricts as stated, and the multiplicative structure of the spectral sequence implies that this is an isomorphism of modules over  $H^*(B)$ .

#### Thom and Euler

We now use this construction to define a new class in  $H^n(B)$  associated to the oriented n-plane bundle  $\xi$ , by means of the composite

$$\pi: B \rightleftharpoons \mathbb{D}(\xi) \to \mathrm{Th}(\xi)$$
.

The first map is the zero-section, homotopy inverse to the projection map. The second one is the collapse map. The Thom class  $U \in \overline{H}^n(\operatorname{Th}(\xi))$  pulls back under this map to a class in  $\overline{H}^n(B)$ .

This class is at least up to sign the Euler class as we defined it earlier:

**Lemma 35.3.** This class coincides up to sign with the Euler class:  $\pi^*U = \pm e$ .

It is easy to verify at least that they generate the same subgroup (which proves that they are the same with coefficients in  $\mathbb{F}_2$ ). Work in the universal case. As a notational choice, we will work over  $\mathbb{Z}$ , so we are looking at  $\xi_n$  over BSO(n). We've seen that the total space of its sphere bundle is BSO(n-1). The Serre spectral sequence for this fibration shows that the kernel of the projection map  $p^*: H^n(BSO(n-1)) \to H^n(BSO(n))$  is the image of the transgression  $H^{n-1}(S^{n-1}) \to H^n(BSO(n-1))$ . So the kernel is cyclic and generated by the Euler class. On the other hand, we have the cofibration sequence

$$BSO(n-1) \to BSO(n) \xrightarrow{\pi} MSO(n)$$

where we are using Thom's notation  $MSO(n) = \text{Th}(\xi_n)$ . The Thom class  $U \in H^n(MSO(n))$  generates this group (by the Thom isomorphism theorem) so its image in  $H^n(BSO(n))$  also generates  $\ker(H^n(BSO(n)) \to H^n(BSO(n-1))$ ).

We will see, as a consequence of a computation of  $H^*(BSO(n); \mathbf{Z}[1/2])$ , that this kernel is infinite cyclic if n is even, so then the generator is at least well defined up to sign. For homework you will show that 2e = 0 if n is even, so the generator is then unique.

But in fact, it's better just to take  $\pi^*U$  as the *definition* of the Euler class. With that definition, we get a new construction of the Gysin sequence: It is the long exact cohomology sequence of the pair  $(\text{Th}(\xi), B)$ , aided by the Thom isomorphism:

$$\cdots \longrightarrow H^{s-1}(B) \xrightarrow{p^*} H^{s-1}(E) \xrightarrow{\delta} \overline{H}^s(\operatorname{Th}(\xi)) \xrightarrow{\pi^*} H^s(B) \xrightarrow{p^*} H^s(E) \longrightarrow \cdots$$

$$\stackrel{p_*}{=} \bigwedge_{e} - \cup U \xrightarrow{e} H^{s-n}(B).$$

This is a long exact sequence of modules over  $H^*(B)$ . This gives a different perspective on integration along the fiber:

$$(p_*x) \cup U = \delta x$$
.

We'll just use this definition going forward. Notice that with this definition, the Euler class is multiplicative for Whitney sum. We should be careful about orientations. The direct sum of oriented vector spaces V and W has an orientation given by putting a positive ordered basis for V first and follow it by a positive ordered basis for W. This convention orients the Whitney sum of two vector bundles over a space.

**Proposition 35.4.** Let  $\xi$  and  $\eta$  be oriented vector bundles over spaces X and Y.

$$e(\xi \times \eta) = e(\xi) \times e(\eta)$$
.

*Proof.* First,  $U_{\xi} \wedge U_{\eta} \in \overline{H}^{p+q}(\operatorname{Th}(\xi) \wedge \operatorname{Th}(\eta))$  is a Thom class for  $\xi \times \eta$ , since it restricts on fiber pairs to the direct sum orientation. Then the collapse maps are compatible:

$$\begin{array}{ccc}
\operatorname{Th}(\xi \times \eta) & \stackrel{=}{\longrightarrow} \operatorname{Th}(\xi) \wedge \operatorname{Th}(\eta) \\
\uparrow^{\pi_{X \times Y}} & \uparrow^{\pi_{X} \wedge \pi_{Y}} \\
(X \times Y)_{+} & \stackrel{=}{\longrightarrow} X_{+} \wedge Y_{+}
\end{array}$$

commutes, and in cohomology we chase

$$U_{\xi} \wedge U_{\eta} \longmapsto U_{\xi \times \eta}$$

$$\downarrow \qquad \qquad \qquad \downarrow$$

$$e(\xi) \times e(\eta) \longmapsto e(\xi \times \eta)$$

If we take X = Y here and pull back along the diagonal,  $\xi \times \eta$  goes to the Whitney sum and  $e(\xi) \times e(\eta)$  goes to the cup-product:

$$e(\xi \oplus \eta) = e(\xi) \cdot e(\eta)$$
.

#### Euler class and symmetric polynomials

One of our descriptions of the Chern classes was this: If an n-plane bundle  $\xi$  splits  $\zeta \oplus (n-k)\epsilon$ , then  $c_k(\xi) = (-1)^k e(\zeta)$ . Let's check that this holds for the classes defined by means of elementary symmetric functions. It might be clearest if we look at the universal example, where the splitting map  $f: BT^n \to BU(n)$  pulls  $\xi_n$  back to the direct sum of line bundles  $\lambda_1 \oplus \cdots \oplus \lambda_n$  and induces an isomorphism  $f^*: H^*(BU(n)) \to H^*(BT^n)^{\Sigma_n}$ . Let's do the case k = n first, so I want to show that  $(-1)^n e(\xi_n)$  maps to  $\sigma_n$ . Using multiplicativity of the Euler class,

$$f^*e(\xi_n) = e(\lambda_1 \oplus \cdots \oplus \lambda_n) = e(\lambda_1) \cdots e(\lambda_n)$$
.

With the notation  $t_i = e(\lambda_i)$ , this shows that

$$f^*((-1)^n e(\xi_n)) = (-1)^n t_1 \cdots t_n = \sigma_n$$
.

For smaller k, we'll use the fact that the maximal tori  $T^k \subseteq U(k)$  are compatible as k increases. This gives the commutative diagram

$$H^{2k}(BU(n)) \longrightarrow H^{2k}(BT^n)^{\Sigma_n}$$

$$\downarrow \qquad \qquad \downarrow$$

$$H^{2k}(BU(k)) \longrightarrow H^{2k}(BT^k)^{\Sigma_k}$$

The elementary symmetric polynomial definition of  $c_k$  specifies that it maps to  $\sigma_k$  along the top arrow. We want to see that this class maps to  $(-1)^k e(\xi_k) \in H^{2k}(BU(k))$ . Well, by the k = n case that we just did, we know that that class maps to  $\sigma_k$  along the bottom. So what remains is to check that  $\sigma_k \in H^{2k}(BT^n)^{\Sigma_n}$  maps to the class of the same name in  $H^{2k}(BT^k)^{\Sigma_k}$ .

To keep things straight, let's write  $\sigma_k^{(n)}$  for the first class and  $\sigma_k^{(k)}$  for the second. The restriction  $H^*(BT^n) \to H^*(BT^k)$  sends  $t_i$  to  $t_i$  if  $i \leq k$  and to 0 if i > k. So

$$\sum_{i=0}^{n} \sigma_i^{(n)} t^{n-i} = \prod_{j=1}^{n} (t - t_j)$$

$$\left(\sum_{i=0}^{k} \sigma_i^{(k)} t^{k-i}\right) t^{n-k} = \left(\prod_{j=1}^{k} (t - t_j)\right) t^{n-k}$$

and comparing coefficients we see that  $\sigma_k^{(n)} \mapsto \sigma_k^{(k)}$ .

#### The Whitney sum formula

By our discussion above, the Whitney sum formula of Theorem 33.3 reduces to proving the following identity:

$$\sigma_k^{(p+q)} = \sum_{i+j=k} \sigma_i^{(p)} \cdot \sigma_j^{(q)} \tag{5.1}$$

inside  $\mathbf{Z}[t_1,\ldots,t_p,t_{p+1},\ldots,t_{p+q}]$ . Here,  $\sigma_i^{(p)}$  is thought of as a polynomial in  $t_1,\ldots,t_p$ , while  $\sigma_j^{(q)}$  is thought of as a polynomial in  $t_{p+1},\ldots,t_{p+q}$ . To derive Equation (5.1), simply compare coefficients in the following:

$$\begin{split} \sum_{k=0}^{p+q} \sigma_k^{(p+q)} t^{p+q-k} &= \prod_{i=1}^{p+q} (t-t_i) \\ &= \prod_{i=1}^p (x-t_i) \cdot \prod_{j=p+1}^{p+q} (t-t_j) \\ &= \left( \sum_{i=0}^p \sigma_i^{(p)} t^{p-i} \right) \left( \sum_{j=0}^q \sigma_j^{(p)} t^{q-j} \right) \\ &= \sum_{k=0}^{p+q} \left( \sum_{i+j=k} \sigma_i^{(p)} \sigma_j^{(q)} \right) t^{p+q-k} \,. \end{split}$$

Hassler Whitney once called this his hardest theorem. Apparently he didn't have the splitting principle working for him.

# 36 Closing the Chern circle, and Pontryagin classes

#### Back to Grothendieck

Now we'll use the splitting principle to show that the Chern classes (defined as corresponding to the elementary symmetric polynomials) participate in a monic polynomial satisfied by the Euler class of the tautologous bundle over the projectivization of a vector bundle. This will complete the identification of the various versions of Chern classes.

So we have an n-plane bundle  $\xi$  over B, and consider the projectivization  $\pi: \mathbb{P}(\xi) \to B$ . We observed in the last lecture that the tautologous bundle  $\lambda$  embeds (canonically) into the pullback  $\pi^*\xi$ . Let  $\overline{\lambda}$  denote the complex conjugate or inverse line bundle, so that  $\overline{\lambda} \otimes \lambda = \epsilon$ . Tensoring  $\pi^*\xi$  with  $\overline{\lambda}$  thus results in a bundle with a trivial summand; that is, with a nowhere vanishing section. Its Euler class therefore vanishes. We will compute what that Euler class is, using the splitting principle.

The splitting principle allows us to assume that  $\xi$  is a sum of line bundles, say  $\xi = \lambda_1 \oplus \cdots \oplus \lambda_n$ . Then

$$\overline{\lambda} \otimes \pi^* \xi = \bigoplus_{i=1}^n \overline{\lambda} \otimes \pi^* \lambda_i$$
.

By multiplicativity of the Euler class, we find

$$e(\overline{\lambda} \otimes \pi^* \xi) = \prod_{i=1}^n e(\overline{\lambda} \otimes \pi^* \lambda_i).$$

Write t for  $e(\lambda) \in H^2(\mathbb{P}(\xi))$ , so that  $e(\overline{\lambda}) = -t$ . Also write  $t_i = e(\lambda_i)$ , so that

$$e(\overline{\lambda} \otimes \pi^* \lambda_i) = \pi^* t_i - t$$

and

$$e(\overline{\lambda} \otimes \pi^* \xi) = \prod_{i=1}^n (\pi^* t_i - t) = (-1)^n \sum_{i=0}^n (\pi^* c_j(\xi)) t^{n-j}.$$

Since  $e(\overline{\lambda} \otimes \pi^* \xi) = 0$ , this shows that our new Chern classes satisfy the identity Grothendieck used to define them. Since these coefficients were unique, this identifies Grothendieck's definition with the others we have introduced.

#### Stiefel-Whitney classes

Same story! Well, almost. We don't have the even/odd argument working for us anymore. We want to know that the Euler class is a non-zero-divisor. We do have the splitting principle, which assures us that

$$f^*: H*(BO(n); \mathbb{F}_2) \hookrightarrow H^*(BC_2^n; \mathbb{F}_2)^{\Sigma_n}$$
.

By multiplicativity of the Euler class, it maps to  $t_1 \cdots t_n \in H^n(BC_2^n; \mathbb{F}_2)$ , which is nonzero in this integral domain and so is a non-zero-divisor. The result:

**Proposition 36.1.** 
$$H^*(BO(n); \mathbb{F}_2) = \mathbb{F}_2[w_1, ..., w_n]$$
.

While we are talking about Stiefel-Whitney classes, let me point out that  $w_1 \in H^1(B; \mathbb{F}_2)$  is precisely the obstruction to orientability of  $\xi : E \downarrow B$ . If B is path-connected, it can be identified with the homomorphism  $\pi_1(B) \to C_2$  that takes on the value -1 on  $\sigma$  if the orientation of the fiber is reversed under the homotopy endomorphism of the fiber given by  $\sigma$ . You can check this in the universal case: The class  $w_1 \in H^1(BO(n); \mathbb{F}_2)$  is represented by a map  $BO(n) \to K(\mathbb{F}_2, 1)$ . This map is the bottom Postnikov stage of BO(n), and its homotopy fiber is the simply connected Whitehead cover of BO(n). We know what that is, since  $SO(n) \hookrightarrow O(n)$  is the connected component of the identity (and is the kernel of det :  $O(n) \to C_2$ ).

The map  $BSO(n) \to BO(n)$  is (at least homotopy theoretically) a double cover; the fiber is  $S^0$ , so we are entitled to a Gysin sequence. The Euler class of this spherical fibration is exactly  $w_1$ , a non-zero-divisor, so we discover the short exact sequence

$$0 \to H^*(BO(n); \mathbb{F}_2) \xrightarrow{e \cdot} H^*(BO(n); \mathbb{F}_2) \to H^*(BSO(n); \mathbb{F}_2) \to 0.$$

This shows that  $H^*(BSO(n); \mathbb{F}_2)$  is the polynomial algebra on the images of  $w_2, \ldots, w_n$ :

$$H^*(BSO(n); \mathbb{F}_2) = \mathbb{F}_2[w_2, \dots, w_n].$$

It often happens that one cares about only the "stable" equivalence class of a vector bundle. This leads one to consider the direct limit or union

$$BO = \lim_{n \to \infty} BO(n)$$
.

Its cohomology is given by

$$H^*(BO) = \mathbb{F}_2[w_1, w_2, \ldots],$$

Of course the limit of the BSO(n)'s is written BSO. It is the simply-connected cover of BO. It's interesting to contemplate the rest of the Whitehead tower of BO. For a while the spaces involved have names:

#### Pontryagin classes

Real vector bundles have integral characteristic classes too! They were studied by Lev Pontryagin (1908–1988, Steklov Institute, blinded in an accident at age 14). The idea is to use Chern classes to define such things. Given a real vector bundle  $\xi$  we can tensor up to the complex vector bundle  $\mathbb{C} \otimes_{\mathbb{R}} \xi$ , and study its Chern classes.

Complex vector bundles arising in this way have some additional structure. Any complex vector bundle  $\zeta: E \downarrow B$  has a "complex conjugate" vector bundle  $\overline{\zeta}$  with the same underlying real vector bundle but with complex structure defined by letting  $z \in \mathbb{C}$  act on  $\overline{\zeta}$  the way  $\overline{z}$  acted on  $\zeta$ . We've already seen this construction for line bundles, when  $\lambda \otimes \overline{\lambda} = \epsilon$ .

The complexification  $\mathbb{C} \otimes_{\mathbb{R}} \xi$  of a real vector bundle comes equipped with an isomorphism

$$\mathbb{C} \otimes_{\mathbb{R}} \xi \cong \overline{\mathbb{C} \otimes_{\mathbb{R}} \xi}$$

given by  $z \otimes v \mapsto \overline{z} \otimes v$ . We discover that

$$c_i(\mathbb{C} \otimes_{\mathbb{R}} \xi) = c_i(\overline{\mathbb{C} \otimes_{\mathbb{R}} \xi}),$$

so we should ask: What are the Chern classes of the complex conjugate of a complex vector bundle?

**Lemma 36.2.** 
$$c_i(\overline{\xi}) = (-1)^i c_i(\xi)$$
.

*Proof.* Exercise; use any one of the perspectives on Chern classes that we have developed.  $\Box$ 

This puts no restriction on  $c_i(\mathbb{C} \otimes_{\mathbb{R}} \xi)$  for i even, but forces  $2c_i(\mathbb{C} \otimes_{\mathbb{R}} \xi) = 0$  for i odd. The 2-torsion will get in the way, so let's work with coefficients in a ring R in which 2 is invertible – a  $\mathbb{Z}[1/2]$ -algebra, such as  $\mathbb{Z}[1/2]$  itself, or  $\mathbb{F}_p$  for  $p \neq 2$ . We already have Stiefel-Whitney classes with mod 2 coefficients, so this is not so bad.

**Definition 36.3.** The kth Pontryagin class of a real vector bundle  $\xi$  is

$$p_k(\xi) = (-1)^k c_{2k}(\mathbb{C} \otimes_{\mathbb{R}} \xi) \in H^{4k}(X; R).$$

Of course  $p_k(\xi) = 0$  if k > n/2, since  $\xi \otimes \mathcal{C}$  is of complex dimension n. The strange sign does not interfere with the Whitney sum formula:

$$p_k(\xi \oplus \eta) = (-1)^k \sum_{i+j=k} c_{2i}(\mathbb{C} \otimes_{\mathbb{R}} \xi) c_{2j}(\mathbb{C} \otimes_{\mathbb{R}} \eta) = \sum_{i+j=k} p_i(\xi) p_j(\eta)$$

since the odd terms contribute only 2-torsion, which we have eliminated by working over a  $\mathbb{Z}[1/2]$ -algebra.

The Pontryagin classes are defined for vector bundles, orientable or not. They are independent of the orientation if there is one. But an oriented 2k-plane bundle over B has an Euler class  $e(\xi) \in H^{2k}(B)$ , and we might ask how it is related to the Pontryagin classes. The sign is there in the definition of the Pontryagin classes so that the following important relation is satisfied.

**Lemma 36.4.** For any oriented 2k-plane bundle,  $p_k(\xi) = e(\xi)^2$ .

*Proof.* We need to be careful about orientations. We have the isomorphism of real vector bundles

$$\xi \oplus \xi \xrightarrow{\cong} \mathbb{C} \otimes_{\mathbb{R}} \xi$$
,

defined  $(v, w) \mapsto v + iw$ . We have established an orientation on  $\mathbb{C} \otimes_{\mathbb{R}} \xi$ . But suppose that  $\xi$  itself came equipped with an orientation. This puts an orientation on the direct sum. How are the two orientations related to each other? If  $e_1, \ldots, e_n$  is a positive basis for an ordered vector space V, then we are comparing the ordered bases

$$e_1, e_2, \dots, e_n, ie_1, ie_2, \dots, ie_n$$
 for  $V \oplus V$  and  $e_1, ie_1, e_2, ie_2, \dots, e_n, ie_n$  for  $\mathbb{C} \otimes_{\mathbb{R}} V$ .

Relating them requires

$$(n-1) + (n-2) + \dots + 1 = \frac{n(n-1)}{2}$$

transpositions, so they give the same orientation if this number is even and opposite orientations if it is odd.

Now we can compute:

$$p_k(\xi) = (-1)^k c_{2k}(\mathbb{C} \otimes_{\mathbb{R}} \xi) = (-1)^k e(\mathbb{C} \otimes_{\mathbb{R}} \xi)$$
$$= (-1)^k (-1)^{2k(2k-1)/2} e(\xi \oplus \xi) = e(\xi)^2$$

since  $2k(2k-1)/2 \equiv k \mod 2$ .

We can now systematically compute the cohomology of BSO(n) away from 2 by induction on n using the Gysin sequence. Here's the result.

**Theorem 36.5.** With coefficients in any  $\mathbb{Z}[1/2]$ -algebra, the cohomology of BSO(n) is polynomial for all n. When n = 2k + 1, the generators are  $p_1, \ldots, p_k$ . When n = 2k, the generators are  $p_1, \ldots, p_{k-1}, e_n$ . The maps  $H^*(BSO(n)) \to H^*(BSO(n-1))$  take Pontryagin classes to themselves, except that  $H^{4k}(BSO(2k+1)) \to H^{4k}(BSO(2k))$  sends  $p_k$  to  $e_{2k}^2$ .

Here's a table of the algebra generators, with the squares of the Euler classes added in to indicate how  $p_k$  restricts.

|               | 2     | 4          | 6     | 8         | 10 | 12        |
|---------------|-------|------------|-------|-----------|----|-----------|
| $H^*(BSO(2))$ | $e_2$ | $(e_2^2)$  |       |           |    |           |
| $H^*(BSO(3))$ |       | $p_1$      |       |           |    |           |
| $H^*(BSO(4))$ |       | $p_1, e_4$ |       | $(e_4^2)$ |    |           |
| $H^*(BSO(5))$ |       | $p_1$      |       | $p_2$     |    |           |
| $H^*(BSO(6))$ |       | $p_1$      | $e_6$ | $p_2$     |    | $(e_6^2)$ |
| $H^*(BSO(7))$ |       | $p_1$      |       | $p_2$     |    | $p_3$     |

We can then compute  $H^*(BO(n); R)$  for R a  $\mathbb{Z}[1/2]$ -algebra by using the fiber sequence

$$BSO(n) \to BO(n) \to \mathbb{R}P^{\infty}$$
.

The spectral sequence has  $E_2^{s,t} = H^s(\mathbb{R}P^\infty; H^t(BSO(n)))$ . There are local coefficients here, but with any local coefficients the higher cohomology of  $\mathbb{R}P^\infty$  is killed by 2 and so vanishes for us. As a result the edge homomorphism

$$H^*(BO(n); R) \to H^*(BSO(n); R)^{C_2}$$

is an isomorphism. The generator of  $\pi_1(\mathbb{R}P^{\infty})$  tracks the effect of reversing orientations: it fixes the Pontryagin classes and negates the Euler classes. The result is that

$$H^*(BO(2k);R) \stackrel{\cong}{\leftarrow} H^*(BO(2k+1);R) \stackrel{\cong}{\rightarrow} H^*(BSO(2k+1);R)$$

and all are given by

$$R[p_1,\ldots,p_k]$$
.

# 37 Steenrod operations

We worked hard to show that mod 2 cohomology takes values not just in graded  $\mathbb{F}_2$ -vector spaces, but actually in graded commutative  $\mathbb{F}_2$ -algebras. This additional structure has proven extremely useful. What other natural structure is there on mod 2 cohomology? Both the sum and the cup product are natural operations on two variables. The identity element  $1 \in H^0$  is in a sense a natural operation on zero variables (and is the only nonzero natural element in mod 2 cohomology). This invites the question: are there nontrivial natural operations in one variable? Some of course are generated from the product:  $x \mapsto x^r$ , for example. When r is a power of 2, this is an additive operation. We know one other additive operation as well: the Bockstein,

$$\beta: H^n(X) \to H^{n+1}(X)$$
.

(All our coefficients will be in  $\mathbb{F}_2$  in this lecture.) This is obtained as the boundary map in the long exact sequence associated to the short exact sequence  $0 \to C_2 \to C_4 \to C_2 \to 0$ .

Our goal in this lecture is to establish the following theorem, due to Norman Steenrod (1910–1971, working at Princeton).

**Theorem 37.1.** For any  $n \geq 0$ , there is a unique family of additive natural transformations

$$\operatorname{Sq}^k: H^n \to H^{n+k}, \quad k \ge 0,$$

such that

$$\operatorname{Sq}^{0} x = x$$
,  $\operatorname{Sq}^{k}(x) = x^{2}$  if  $k = |x|$ ,  $\operatorname{Sq}^{k} x = 0$  if  $k > |x|$ ,

and the "Cartan formula"

$$\operatorname{Sq}^{k}(xy) = \sum_{i+j=k} (\operatorname{Sq}^{i} x)(\operatorname{Sq}^{j} y)$$

is satisfied.

It will transpire that  $Sq^1 = \beta$ .

By the Yoneda lemma, natural transformations  $H^n \to H^{n+k}$  are classified by  $H^{n+k}(K_n)$ , where we write

$$K_n = K(\mathbb{F}_2, n)$$
.

We won't try to compute the whole of  $H^*(K_n)$ , at least not right away, though eventually it will turn out that the entire cohomology of the mod 2 Eilenberg Mac Lane spaces is generated as an algebra by iterates of the operations we will construct. But at least we can notice right off that

$$H^i(K_n) = 0$$
 for  $0 < i < n$ 

and

$$H^n(K_n) = \mathbb{F}_2$$
 for  $n > 0$ 

by the Hurewicz theorem, so the only nonzero operation on n-dimensional classes that lowers degrees is the one sending every x to  $1 \in H^0$ .

The starting point is the failure of the map cochain cross product

$$S^*(X) \otimes S^*(X) \to S^*(X \times X)$$

– or of any natural chain map inducing the cross product in cohomology – to be  $C_2$ -equivariant. This failure reflects itself geometrically using the following construction.

**Definition 37.2.** The extended square of a space X is the balanced product

$$S^{\infty} \times_{C_2} X^2$$
.

Here  $C_2$  acts antipodally on  $S^{\infty}$ , and swaps the factors in  $X^2$ .

This is the total space of the bundle with fiber  $X^2$  associated to the universal principal  $C_2$  bundle  $S^{\infty} \downarrow \mathbb{R}P^{\infty}$ . We will study it by means of the Serre spectral sequence.

Actually, it will be important to consider a pointed refinement of this. So suppose given a basepoint  $* \in X$ . It determines the subset

$$X \lor X \subseteq X \times X$$

consisting of the "axes" in the product. The pair  $(X^2, X \vee X)$  is equivariant, and determines a bundle pair

$$S^{\infty} \times_{C_2} (X^2, X \vee X) \downarrow \mathbb{R}P^{\infty}$$
.

A point in  $S^{\infty}$  determines a fiber inclusion

$$i: (X^2, X \vee X) \to S^{\infty} \times_{C_2} (X^2, X \vee X)$$
.

We'll be working with the cohomology Künneth theorem, so let's restrict ourselves to spaces whose mod 2 cohomology is of finite type. Serre's mod  $\mathcal{C}$  theory guarantees that  $K_n$  is in this category, and the Künneth theorem guarantees that the category is closed under products.

**Proposition 37.3.** There is a unique natural transformation

$$P: \overline{H}^n(X) \to H^{2n}(S^{\infty} \times_{C_2} (X^2, X \vee X))$$

such that

$$i^*P(x) = x^{\otimes 2} \in H^{2n}(X^2, X \vee X).$$

*Proof.* We'll study the associated Serre spectral sequence,

$$H^s(\mathbb{R}P^\infty; H^t(X^2, X \vee X)) \Longrightarrow H^{s+t}(S^\infty \times_{C_2} (X^2, X \vee X))$$
.

While the chain-level cross product isn't equivariant, the cohomology cross product is: The cross relative product map

$$\overline{H}^*(X) \otimes \overline{H}^*(X) \to H^*(X^2, X \vee X)$$

is equivariant, if we let  $C_2$  act by exchanging factors on the left and on the right. This map is an isomorphism if  $H^*(X)$  is of finite type, and then the  $\mathbb{F}_2[C_2]$ -module featuring as coefficients in the spectral sequence can be written as  $\overline{H}^*(X)^{\otimes 2}$ . It's interesting and not hard to analyze this representation of  $C_2$ , but we do not need to know about that to construct Steenrod operations. All we need to know is that any  $x \in \overline{H}^n(X)$  determines an invariant class  $x \otimes x \in \overline{H}^n(X)^{\otimes 2}$ .

Now comes the trick: It suffices to consider the universal example,  $\iota_n \in \overline{H}^n(K_n)$ . Since  $\overline{H}^i(K_n) = 0$  for i < n, the entire  $E_2$  term of

$$H^s(\mathbb{R}P^\infty; H^t(K_n^2, K_n \vee K_n)) \Longrightarrow H^*(S^\infty \times_{C_2} (K_n^2, K_n \vee K_n))$$

lies in vertical dimensions  $t \geq 2n$ .

So the group

$$E_2^{0,2n} = H^{2n}(K_n^2, K_n \vee K_n) = \langle \iota_n \otimes \iota_n \rangle$$

survives to  $E_{\infty}^{0,2n}$ . The element  $\iota_n \otimes \iota_n$  lifts to an element of  $H^{2n}(S^{\infty} \times_{C_2} (K_n^2, K_n \vee K_n))$ , and this lift is unique because all the lower filtration degrees vanish. This lifted class is  $P\iota_n$ . By definition (and the edge homomorphism story) it restricts on  $(K_n^2, K_n \vee K_n)$  to  $\iota_n \otimes \iota_n$ .

The resulting natural transformation  $P: H^n(X) \to H^n(S^{\infty} \times_{C_2} (X^2, X \vee X))$  is the "total square." It's a prime example of a "power operation."

Now we "internalize," by pulling back under the diagonal map. The "commutativity" of the diagonal map becomes important:

$$\Delta: X \to X \times X$$

is equivariant, where  $C_2$  acts trivially on X and by swapping the factors in  $X \times X$ . It induces a map

$$S^{\infty} \times_{C_2} (X, *) \to S^{\infty} \times_{C_2} (X^2, X \vee X)$$
.

But

$$S^{\infty} \times_{C_2} (X, *) = \mathbb{R}P^{\infty} \times (X, *)$$

so we have

$$\delta: \mathbb{R}P^{\infty} \times (X, *) \to S^{\infty} \times_{C_2} (X^2, X \vee X).$$

Pick  $x \in \overline{H}^n(X)$  and consider the pullback  $\delta^*P(x)$ . By the Künneth theorem,

$$H^*(\mathbb{R}P^{\infty} \times (X,*)) = H^*(\mathbb{R}P^{\infty}) \otimes \overline{H}^*(X)$$

so  $\delta^*P(x)$  has an expression as a polynomial in the generator  $t \in H^1(\mathbb{R}P^{\infty})$ . The coefficients are the Steenrod squares:

$$\delta^* P(x) = (\operatorname{Sq}^n x) + (\operatorname{Sq}^{n-1} x)t + \dots + (\operatorname{Sq}^0 x)t^n \quad \operatorname{Sq}^i x \in \overline{H}^{n+i}(X).$$

Since  $\overline{H}^i(K_n) = 0$  for i < n, there are no natural transformations that decrease degree: so there are no negatively indexed squares; the sum terminates as indicated.

Any operation on  $\overline{H}^*$  induces one on  $H^*$  by using the isomorphism

$$H^*(X) = \overline{H}^*(X_+)$$
.

Note that  $(X_+)^2 = X^2 \sqcup (X_+ \vee X_+)$  so the total square specializes to a natural transformation

$$P: H^n(X) \to H^{2n}(S^\infty \times_{C_2} X^2)$$
.

**Proposition 37.4.** Sq<sup>n</sup>:  $H^n \to H^{2n}$  is the squaring map  $x \mapsto x^2$ .

*Proof.* This is the coefficient of  $1 \in H^0(\mathbb{R}P^{\infty})$ , so we should pick a basepoint for  $\mathbb{R}P^{\infty}$ , and watch the evolution of the class Px in the cohomology of the commutative diagram

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

# Proposition 37.5. $Sq^1 = \beta$ .

*Proof.* Acting on  $H^q$  for  $q \geq 1$ , both  $\operatorname{Sq}^1$  and  $\beta$  are nonzero. (Exercise: Provide examples.) We claim that  $\dim H^{n+1}(K_n) = 1$  for  $n \geq 1$ , so the two must coincide. Since  $K_1 = \mathbb{R}P^{\infty}$ , we know that case. For the inductive step, use the Serre exact sequence on the fibration sequence

$$K_{n-1} \to PK_n \to K_n$$
.

How about  $\operatorname{Sq}^0$ ? Since  $\overline{H}^n(K_n) = \mathbb{F}_2$ , there are only two natural transformations  $\overline{H}^n \to \overline{H}^n$ : the identity and the zero map. The Steenrod operation  $\operatorname{Sq}^0$  is one or the other; which is it? In a sense the operations  $\operatorname{Sq}^k$  get more sophisticated as k decreases; identifying  $\operatorname{Sq}^0$  is tricky. In fact there are many other contexts in which Steenrod operations can be defined, and in a sense the topological context is characterized by  $\operatorname{Sq}^0 = 1$ . We'll study the simplest case first.

# **Proposition 37.6.** $\operatorname{Sq}^0 = 1$ on $\overline{H}^1$ .

*Proof.* It suffices to come up with a single example of a space with a nonzero class  $x \in \overline{H}^1(X)$  such that  $\operatorname{Sq}^0 x = x$ . Our example will be  $S^1$  with the generator  $x \in \overline{H}^1(S^1)$ .

It suffices to look at the subspace of the extended square in which  $S^{\infty}$  is replaced by  $S^1$ . Passing to the quotient space of the pair  $S^1 \times_{C_2} (S^1 \times S^1, S^1 \vee S^1)$ , we arrive at the pointed space

$$\frac{S^1 \times_{C_2} (S^1 \wedge S^1)}{S^1 \times_{C_2} *}$$

in which  $C_2$  exchanges the two factors of  $S^1$ . The smash product may be identified with the one-point compactification of  $\mathbb{R}^2$ , with  $C_2$  acting linearly by permuting the two basis vectors. This representation of  $C_2$  is just  $1 \oplus \sigma$ , the sum of the trivial 1-dimensional representation with the sign representation.

We have the double cover  $S^1 \downarrow \mathbb{R}P^1$ . This is a principal  $C_2$ -bundle, and the space we are looking at is exactly the Thom space of the vector bundle over  $\mathbb{R}P^1$  associated to this principal  $C_2$  bundle

and the representation  $1 \oplus \sigma$ : it is  $\text{Th}(\epsilon \oplus \lambda)$  where  $\lambda$  is the tautological line bundle over  $\mathbb{R}P^1$ . Thus we arrive at

$$\frac{S^1 \times_{C_2} (S^1 \wedge S^1)}{S^1 \times_{C_2} *} = \Sigma \mathbb{R} P^2.$$

The fiber inclusion into the extended square corresponds under this identification with the fiber inclusion in the Thom space. So the nontrivial class in  $H^2(\Sigma \mathbb{R}P^2)$  is the Thom class; it restricts to  $x \otimes x$  in the fiber, and hence the Thom class is the total square Px.

The diagonal inclusion

$$\frac{S^1 \times_{C_2} S^1}{S^1 \times_{C_2} *} \to \frac{S^1 \times_{C_2} (S^1 \wedge S^1)}{S^1 \times_{C_2} *}$$

corresponds to including the fixed point subspace into the representation  $1 \oplus \sigma$ . This produces a bundle map  $\epsilon \to \epsilon \oplus \lambda$  covering the inclusion  $\mathbb{R}P^1 \hookrightarrow \mathbb{R}P^2$ . We obtain a map of Thom spaces

$$\Sigma \mathbb{R} P^1_+ \to \Sigma \mathbb{R} P^2$$

that (by naturality of the Thom isomorphism) is an isomorphism in dimension 2. This is generated by the class  $t \otimes x$ , and we conclude that  $\operatorname{Sq}^0 x = x$ .

The Cartan formula is quite easy to verify as well, but we won't carry that out here. Notice though that it has an important corollary.

**Proposition 37.7.** The Steenrod operations are stable: For all n and q the diagram

$$\overline{H}^{q}(X) \xrightarrow{\operatorname{Sq}^{n}} \overline{H}^{q+n}(X)$$

$$\downarrow^{\sigma} \qquad \qquad \downarrow^{\sigma}$$

$$\overline{H}^{q+1}(\Sigma X) \xrightarrow{\operatorname{Sq}^{n}} \overline{H}^{q+n+1}(\Sigma X)$$

commutes.

*Proof.* The suspension isomorphism is induced by the relative cross product

$$\wedge : \overline{H}^1(S^1) \otimes \overline{H}^q(X) \to \overline{H}^{q+1}(\Sigma X).$$

The Cartan formula together with the fact that  $\operatorname{Sq}^0=1$  on  $\overline{H}^1$  gives the result.

Corollary 37.8.  $\operatorname{Sq}^0$  is the identity on  $\overline{H}^q$  for any q.

*Proof.* We just check this on  $\iota_q \in H^q(K_q)$ . The map  $K_1 \times K_{q-1} \to K_q$  representing the cup product sends  $\iota_1 \otimes \iota_{q-1}$  to  $\iota_q$ , and the result then follows by induction and the Cartan formula.

Corollary 37.9.  $\operatorname{Sq}^n : \overline{H}^q \to \overline{H}^{q+n}$  is additive.

This is surprising, since the total power operation P is not additive.

*Proof.* Any stable operation  $K_q \to K_{q+n}$  is additive: Being stable means that

$$K_{q} \xrightarrow{\S_{\mathfrak{A}}} K_{q+n}$$

$$\downarrow^{\simeq} \qquad \downarrow^{\simeq}$$

$$\Omega^{k} K_{q+k} \xrightarrow{\Omega^{k} \operatorname{Sq}^{n}} K_{q+k+n}$$

commutes up to homotopy. The H-space structure of  $K_q$  as a loop space is the structure representing the sum in  $H^q$ , so  $Sq^n: K_q \to K_{q+n}$  induces a homomorphism in [X, -].

The Steenrod algebra  $A^*$  is the algebra of cohomology operations generated by the Steenrod operations. This is a noncommutative graded  $\mathbb{F}_2$ -algebra. It is not a free algebra: the Steenrod operations satisfy relations, starting with  $\operatorname{Sq}^1\operatorname{Sq}^1=0$ . In fact, all relations among them are determined by two facts:

- $\operatorname{Sq}^{2n-1}\operatorname{Sq}^n=0$  and
- The assignment  $\operatorname{Sq}^n \mapsto \operatorname{Sq}^{n-1}$  extends to a derivation on  $A^*$ .

An explicit generating family of relations is given by the Adem relations

$$\operatorname{Sq}^{i}\operatorname{Sq}^{j} = \sum_{k} {j-k-1 \choose i-2k} \operatorname{Sq}^{i+j-k} \operatorname{Sq}^{k}, \quad i < 2j.$$

(José Adem, 1921–1991, was a student of Steenrod and a founding father of algebraic topology in Mexico.) This relation looks quadratic, and almost is, but fails to be whenever the binomial coefficient with k=0 in the summation is nonzero. If n is not a power of 2, let j be the largest power of 2 less than n and i=n-j. Then the binomial coefficient  $\binom{j-1}{i}$  is nonzero, so the Adem relation shows that  $\operatorname{Sq}^n$  is decomposable: a sum of products of positive-dimensional elements. From this we learn:

**Proposition 37.10** (Adem).  $A^*$  is generated by  $\operatorname{Sq}^1, \operatorname{Sq}^2, \operatorname{Sq}^4, \operatorname{Sq}^8, \dots$ 

This leads to information about the "Hopf invariant." Among its many interpretations, the Hopf invariant asks how far the sequence of 3-cell complexes  $\mathbb{R}P^2$ ,  $\mathbb{C}P^2$ ,  $\mathbb{H}P^2$ , can be extended. The "octonions"  $\mathbb{O}$  provide us with one more,  $\mathbb{O}P^2$ . Adem's theorem puts a first restriction on such spaces:

Corollary 37.11. Suppose there is a space X such that  $H^*(X) = \mathbb{F}_2[x]/x^3$ . Then |x| is a power of 2.

*Proof.* Let n = |x|. Then  $\operatorname{Sq}^n x = x^2 \neq 0$ . But if n is not a power of 2, this operation factors through groups between dimension n and 2n.

This theorem was improved by Frank Adams to: |x| = 1, 2, 4 or 8; there are no examples beyond the classical ones. (John Frank Adams (1930–1989) was a key figure in the development of twentieth century homotopy theory, Lowndean Professor at Cambridge University.)

38. COBORDISM 143

## 38 Cobordism

René Thom [41] (1923–2002), IHES, discovered how to use all this machinery to give a classification of closed manifolds, which, while crude, is valid in all dimensions. His equivalence relation was *cobordism* (or "bordism" – opinions vary):

**Definition 38.1.** Let M and N be two closed smooth n-manifolds. A cobordism between them is an (n + 1)-manifold-with-boundary W together with a diffeomorphism

$$\partial W \cong M \sqcup N$$
.

If there is a cobordism, M and N are said to be "cobordant."

If M and N are diffeomorphic, we may use  $W = M \times I$  along with the diffeomorphism at one end to see that they are cobordant. Cobordism is an equivalence relation on the class of closed n-manifolds. Disjoint union endows the set (why "set"?)

$$\mathcal{N}_n = \Omega_n^O$$

of cobordism classes of n-manifolds with the structure of a commutative monoid. In fact it is a vector space over  $\mathbb{F}_2$ , since the same cylinder can be regarded as a null-bordism of  $M \sqcup M$ . The product of manifold actually renders the collection of bordism groups a graded commutative algebra. Thom proved:

**Theorem 38.2** (Thom).  $\mathcal{N}_* = \mathbb{F}_2[x_i : i+1 \text{ is positive and not a power of } 2]$ , where  $|x_i| = i$ .

We will sketch his proof of this amazing classification theorem over the next few lectures. (Thom actually only proved the additive statement. Bob Stong's notes [38] provide an excellent secondary source.)

Thom also addressed a question formulated by Norman Steenrod – but this question must have been in Poincaré's mind much earlier. There are two competing notions of an n-cycle: the singular one we have been using (or the equivalent but even more combinatorial version involving simplicial complexes), and the notion of the fundamental cycle of a closed n-manifold. Are they equivalent? Here's Steenrod's formulation of this question. Given an n-dimensional mod 2 homology class x in a space X, is there a closed n-manifold M and a continuous map  $f: M \to X$  such that  $f_*[M] = x$ ?

This question has an obvious integral variant as well, in which we demand that the manifold M is oriented.

**Theorem 38.3** (Thom [41]). The answer to these questions are: "Yes" in the unoriented case and "No" in the oriented case.

#### The Pontryagin-Thom collapse

A smooth map  $f: M \to N$  of manifolds is an *immersion* if it induces a monomorphism on all tangent spaces. One then has an embedding of vector bundles over M,  $df: \tau_M \hookrightarrow f^*\tau_N$ . The quotient bundle is the *normal bundle* of f,  $\nu_f$ . If we equip  $\tau_N$  with a metric, we receive a metric on  $f^*\tau_N$  and can identify  $\nu_f$  with the orthogonal complement of  $\tau_M$  in  $f^*\tau_N$ :

$$\tau_M \oplus \nu_f \cong f^* \tau_N$$
.

Suppose that M is compact. An embedding  $f: M \to N$  is an injective immersion: an immersion without double points. In that case, the tubular neighborhood theorem (see [4, p. 93], for example)

asserts that the subspace  $f(M) \subseteq N$  admits a "regular" neighborhood that is equipped with a diffeomorphism rel M to the normal bundle  $\nu_f$ . This regular neighborhood is moreover unique up to diffeomorphism rel M. In view of this identification we will denote the regular neighborhood by  $E(\nu)$ .

This observation provides a contravariant relationship between M and N: collapse the complement of  $E(\nu)$  to a point. This provides a map

$$c: N_+ \to \operatorname{Th}(\nu)$$

from the one-point compactification of N to the Thom space of the normal bundle. This is the  $Pontryagin-Thom\ collapse$ . It's a special case of the fact that one-point compactification provides a contravariant functor on the category of locally compact Hausdorff spaces and open inclusions.

When  $N = \mathbb{R}^{n+k}$ , this construction associates to an embedded *n*-manifold  $j: M \hookrightarrow \mathbb{R}^{n+k}$  a map  $S^{n+k} \to \text{Th}(\nu_j)$ . If we vary the embedding through an isotopy (a smooth homotopy through embeddings) and vary the tubular neighborhood, the resulting maps vary through a homotopy.

Now comes Thom's observation: the normal bundle is classified by a map  $M \to BO(k)$ , which induces a map on the level of Thom spaces. By composing, we get a map

$$S^{n+k} \to \operatorname{Th}(\nu_i) \to \operatorname{Th}(\xi_k) = MO(k)$$
.

This provides a map from the set of isotopy classes of embeddings of n-manifolds into  $\mathbb{R}^{n+k}$  to the homotopy group  $\pi_{n+k}(MO(k))$ . Separated disjoint unions get sent to the sum in the homotopy group. The empty manifold gets sent to zero.

But homotopy corresponds to a still broader equivalence relation on embedded n-manifolds. Given  $M_0$  and  $M_1$ , both embedded in  $\mathbb{R}^{n+k}$ , an ambient cobordism between them is a manifold with boundary, W, embedded in  $\mathbb{R}^{n+k} \times I$ , meeting  $\mathbb{R}^{n+k} \times 0$  and  $\mathbb{R}^{n+k} \times 1$  transversely in  $M_0$  (along  $\mathbb{R}^{n+k} \times 0$ ) and  $M_1$  (along  $\mathbb{R}^{n+k} \times 1$ ). Isotopies provide cobordisms, but the cobordism could have some more complicated topology as well, and the ends of a cobordism do not have to be even homotopy equivalent. It's not hard to see that cobordisms produce homotopies. Here's the geometric content of Thom's work.

**Theorem 38.4** (Thom). The Pontryagin-Thom collapse map from the set of ambient cobordism classes of closed n-manifolds in  $\mathbb{R}^{n+k}$  to the corresponding homotopy class in  $\pi_{n+k}(MO(k))$  is bijective.

For example,  $MO(1) = \mathbb{R}P^{\infty}$ , so  $\pi_2(MO(1)) = 0$ : a union of *i* circles embedded in  $\mathbb{R}^2$  can be written as the boundary of a 2-sphere with *i* discs removed.

The inverse map is just as interesting. Start with a map

$$f: S^{n+k} \to MO(k)$$
.

Compress it through an approximation,

$$g: S^{n+k} \to \operatorname{Th}(\xi_{q,k} \downarrow \operatorname{Gr}_k(\mathbb{R}^q)).$$

Approximate this by a nearby (and hence homotopic) map that is smooth on the pre-image of  $E(\xi_{q,k})$ , and deform it further so that it meets the image Z of the zero section transversely. Then the implicit function theorem guarantees that the preimage  $g^{-1}(Z)$  is a submanifold  $M \hookrightarrow S^{n+k}$ . The zero section has codimension k in  $E(\xi_{q,k})$ , so M is an n-manifold.

This construction is pretty clearly inverse to the Pontryagin-Thom collapse. The whole story generalizes to allow structure on the normal bundle: for example an orientation or a complex

38. COBORDISM 145

structure or a trivialization. The key observation is that the normal bundle of the zero section in the Thom space of an appropriate manifold approximation of the relevant universal bundle can be identified with the restriction of the universal bundle and so inherits the same structure. The relevant homotopy groups are then  $\pi_{n+k}(MSO(k))$  or  $\pi_{n+k}(MU(k/2))$  in the first two cases. Giving a trivialization of a vector bundle is the same thing as giving an isomorphism with the pullback of a bundle over a point, so we can take a point as the corresponding classifying space. The Thom space is a sphere; so in that case the relevant homotopy group is  $\pi_{n+k}(S^k)$ . This gives a spectacular interpretation of the homotopy groups of spheres. It is the case Pontryagin considered.

#### Stabilization

Now it is definitely interesting to consider embedded manifolds, but perhaps abstract manifolds, without a chosen embedding, are even more interesting, or at least simpler. Whitney proved that any closed manifold embeds in Euclidean space of twice its dimension, and if you allow the ambient space to be of even higher dimension you find that any two embeddings are isotopic. Similarly, in high codimension the cobordisms become unconstrained.

Passing from an embedding in  $\mathbb{R}^{n+k}$  to an embedding in  $\mathbb{R}^{n+k+1}$  replaces the normal bundle  $\nu$  with  $\nu \oplus \epsilon$ . Correspondingly, the map  $BO(k) \to BO(k+1)$  classifies  $\xi_k \oplus \epsilon$ . This gives us maps

$$\Sigma MO(k) \to MO(k+1)$$

for each  $k \geq 1$ , and hence maps

$$\pi_{n+k}(MO(k)) \to \pi_{n+k+1}(MO(k+1)) \to \pi_{n+k+2}(MO(k+2)) \to \cdots$$

that correspond to considering manifolds embedded in higher and higher dimension. We also get maps in homology,

$$\overline{H}_{n+k}(MO(k)) \to \overline{H}_{n+k+1}(MO(k+1)) \to \overline{H}_{n+k+2}(MO(k+2)) \to \cdots$$

This is a beautiful and motivating example of a (topological!) spectrum: A sequence of pointed spaces  $E_k$  together with maps  $\Sigma E_k \to E_{k+1}$ . The direct limit

$$\pi_n(E) = \lim_{k \to \infty} \pi_{n+k}(E_k)$$

is the nth homotopy group of the spectrum E. Similarly we can define the homology of the spectrum E as

$$H_i(E) = \lim_{k \to \infty} \overline{H}_{n+k}(E_k).$$

Spectra are by default "pointed"; there's no "unreduced" homology of a spectrum.

We have already seen a number of other spectra! For example, the *Eilenberg Mac Lane spectrum* HA for the abelian group A has K(A, n) as its nth space, and the map  $\Sigma K(A, n) \to K(A, n+1)$  that classifies the suspension of the fundamental class – the adjoint of the equivalence  $K(A, n) \to \Omega K(A, n+1)$ .

Spectra are the central objects of study in stable homotopy theory. Here's a tiny part of that theory. As an endofunctor of the stable homotopy category, suspension is an equivalence. It is a consequence of the definition of homotopy equivalence for spectra that the following two proposed definitions of the suspension of a spectrum E are equivalent.

•  $(\Sigma E)_n = \Sigma E_n$ , and the bonding maps are the suspensions of the bonding maps in E;

•  $(\Sigma E)_n = E_{n+1}$ , and the bonding maps are the same.

So for example  $\Sigma HA$  is equivalently given by

$$\Sigma K(A,0), \Sigma K(A,1), \ldots$$
 and  $K(A,1), K(A,2), \cdots$ .

The second definition of suspension is clearly a categorical equivalence on the category of spectra.

The spectrum built from Thom spaces as above is the unoriented Thom spectrum, and is denoted simply MO. The space MO(k) is (k-1)-connected, so the Freudenthal suspension theorem assures us that the direct limit defining  $\pi_n(MO)$  is achieved. We also have Thom spectra MSO and MU; the Thom spectrum corresponding to framed manifolds is the sphere spectrum S, with nth space  $S^n$ .

The ambient cobordism theorem stabilizes to give:

**Theorem 38.5** (Thom). The Pontryagin-Thom construction gives an isomorphism from the group of cobordism classes of closed n-manifolds to  $\pi_n(MO)$ :

$$\mathcal{N}_n \xrightarrow{\cong} \pi_n(MO)$$
.

So Thom's classification theorem amounts to computing the homotopy groups of the Thom spectrum MO.

#### Characteristic numbers

To compute these homotopy groups we need a way to distinguish cobordism classes from each other: We need a supply of "cobordism invariants." Characteristic classes afford such invariants.

Let M be an n-manifold. Embed it in some Euclidean space,  $M \hookrightarrow \mathbb{R}^{n+k}$ , and denote the normal bundle of the embedding by  $\nu$ . Its mod 2 characteristic classes are polynomials in the Stiefel-Whitney classes; there are lots of them. The ones that happen to lie in  $H^n(M)$  can be paired against the fundamental class [M]. The resulting elements of  $\mathbb{F}_2$  are characteristic numbers.

Lemma 38.6. Characteristic numbers are cobordism invariants.

*Proof.* We have to show that if  $M = \partial N$  then

$$\langle w(\nu), [M] \rangle = 0$$

for any  $w \in H^n(BO)$ . The class [M] is the boundary of the relative fundamental class  $[N, M] \in H^{n+1}(N, M)$ , so using the adjointness of the boundary and coboundary maps

$$\langle w(\nu), [M] \rangle = \langle \delta w(\nu), [N, M] \rangle$$
.

We claim that  $\delta w(\nu) = 0$ , and we will show that by exhibiting a class in  $H^n(N)$  that restricts to  $w(\nu)$ . By increasing the codimension if necessary, we can assume that the bounding manifold W embeds in  $\mathbb{R}^{n+k} \times [0,\infty)$ , meeting  $\mathbb{R}^{n+k} \times 0$  transversely in M. So the normal bundle  $\nu$  extends the normal bundle  $\nu_N$  of  $N \hookrightarrow \mathbb{R}^{n+k} \times [0,\infty)$ , and  $w(\nu) = w(i^*\nu_N) = i^*w(\nu_N)$  (where  $i: M \hookrightarrow N$  is the inclusion of the boundary).

Putting all the characteristic numbers in play at once, we get the "characteristic number map"

$$\mathcal{N}_n \to \operatorname{Hom}(H^n(BO), \mathbb{F}_2) = H_n(BO)$$
.

38. COBORDISM 147

We'll reinterpret this map in terms of the Thom spectrum MO.

Let  $\xi$  be a real n-plane bundle over a space B. The cohomology Thom isomorphism relied on the pairing

$$\operatorname{Th}(\xi) \to B_+ \wedge \operatorname{Th}(\xi)$$
,

and was given by pairing with the Thom class  $U \in H^n(\operatorname{Th}(\xi))$ . In homology, this pairing produces the top row in

$$\overline{H}_{*+n}(\operatorname{Th}(\xi)) \longrightarrow H_*(B) \otimes \overline{H}_n(\operatorname{Th}(\xi))$$

$$\cong \qquad \qquad \downarrow 1 \otimes \langle U, - \rangle$$

$$H_*(B)$$

The vertical map is defined using the Kronecker pairing with the Thom class. The diagonal map is the homology Thom isomorphism.

In the universal case we have isomorphisms

$$\overline{H}_{*+n}(MO(n)) \xrightarrow{\cong} H_n(BO(n))$$
.

These maps are compatible with stabilization and give the Thom isomorphism

$$\Phi: H_*(MO) \xrightarrow{\cong} H_*(BO)$$
.

These constructions fit together in the commutative diagram:

Thom proved that the mod 2 Hurewicz homomorphism h is a monomorphism. As a corollary:

Corollary 38.7. If the closed n-manifolds M and N have the same Stiefel-Whitney numbers, then they are cobordant.

This uses algebraic topology to guarantee a very geometric outcome! For example, if all the Stiefel-Whitney numbers vanish then the manifold is *null-bordant*: it is the boundary of some (n+1)-manifold-with-boundary.

Thom's basic homotopy-theoretic theorem is this:

**Theorem 38.8** (Thom). The spectrum MO is a product of suspensions of the mod 2 Eilenberg Mac Lane spectrum.

This implies a positive solution to Steenrod's question. A convenient way to explain this is via an observation of Michael Atiyah [2]. Let X be any space (a "background," in physics parlance), and consider the set of continuous maps from closed n-manifolds into X, modulo the equivalence relation given by cobordism of manifolds together with extension of the maps. This is an abelian group depending covariantly on X,

$$X \mapsto \Omega_n^O(X)$$

Atiyah showed that it is a generalized homology theory. Its "coefficients" are

$$\Omega_n^O(*) = \mathcal{N}_n$$
.

There is a natural map, the "Thom reduction,"

$$\Omega_n^O(X) \to H_n(X; \mathbb{F}_2)$$

given by sending  $f: M \to X$  to  $f_*([M]) \in H_n(X; \mathbb{F}_2)$ . Steenrod's question asks whether this map is surjective.

Generalized homology theories are "represented" by spectra. Given a spectrum E and a pointed space Y, one can form the "smash product" spectrum  $E \wedge Y$  with

$$(E \wedge Y)_n = E_n \wedge Y$$

and the obvious bonding maps.

**Theorem 38.9** (George Whitehead and Edgar Brown). Given any spectrum E, the functors

$$E_*: X \mapsto \pi_n(E \wedge X_+)$$

constitute a generalized homology theory, and any generalized homology theory admits such a representation.

In particular

$$\Omega_n^O(X) = \pi_n(MO \wedge X_+)$$
 and  $H_n(X; \mathbb{F}_2) = \pi_n(H\mathbb{F}_2 \wedge X_+)$ 

so the fact that there is a section of the Thom class  $U: MO \to H\mathbb{F}_2$  (given by including the bottom factor into the product) implies a positive answer to Steenrod's question.

# 39 Hopf algebras

#### Product structure

There is more structure to exploit in our study of the bordism groups. The product of a closed m-manifold M and a closed n-manifold N is a closed (m+n)-manifold. This is what gives  $\Omega_*^O = \Omega_*^O(*)$  its structure as a commutative graded ring. To pass this through the Pontryagin-Thom collapse, notice that  $M \times N$  embeds into the product of ambient Euclidean spaces, and the resulting normal bundle is the product of the two normal bundles. The universal case of a product of m-plane and n-plane bundles is represented by a map

$$BO(m) \times BO(n) \to BO(m+n)$$

which is covered by the bundle map  $\xi_m \times \xi_n \to \xi_{m+n}$  and hence induces a map on the level of Thom spaces:

$$MO(m) \wedge MO(n) \rightarrow MO(m+n)$$
.

These maps render MO a "ring spectrum," making  $\pi_*(MO)$  a graded ring, and the map

$$\Omega_*^O \to \pi_*(MO)$$

is a ring isomorphism. Equally,  $H_*(MO)$  is a graded ring and the Hurewicz map is a ring homomorphism. The homology Thom isomorphism is also multiplicative: The space BO has a commutative H-space structure derived from Whitney sum, and the map  $\Phi: H_*(BO) \to H_*(MO)$  is an isomorphism of graded rings.

39. HOPF ALGEBRAS 149

#### Hopf algebras

With a field for coefficients, the Künneth theorem delivers for any space X a map

$$\Delta: H_*(X) \to H_*(X \times X) \xleftarrow{\cong} H_*(X) \otimes H_*(X)$$

(all tensors over the coefficient field k) variously termed a "coproduct," "comultiplication," or "diagonal." The unique map  $X \to *$  gives us a "counit"  $H_*(X) \to k$ .

**Definition 39.1.** A k-coalgebra is an k-module A together with k-module maps  $\epsilon: A \to k$  and  $\Delta: A \to A \otimes A$  that are unital and associative:

It is *commutative* if also

commutes.

This makes sense in the graded context as well, when the swap map T should contribute its usual sign. In that case we say that A is connected if  $A_i = 0$  for i < 0 and  $\epsilon : A \to k$  is an isomorphism in dimension 0.

The diagonal in  $H_*(X)$  is dual to the cup product: the universal coefficient isomorphism

$$\operatorname{Hom}(H_*(X),k) \cong H^*(X)$$

sends the diagonal to the cup product (and  $\epsilon$  to the unit map  $k \to H^*(X;k)$ ).

If X is an H-space, the product induces the "Pontryagin product"  $\mu: H_*(X) \otimes H_*(X) \to H_*(X)$ . Since the product and the basepoint inclusion  $* \to X$  are maps of spaces, they are maps of coalgebras. We have to say what the coalgebra structure is on a tensor product of coalgebras, say A and B: define

$$\Delta_{A\otimes B}:A\otimes B\xrightarrow{\Delta\otimes\Delta}(A\otimes A)\otimes(B\otimes B)\xrightarrow{1\otimes T\otimes 1}(A\otimes B)\otimes(A\otimes B)$$

and

$$\epsilon_{A\otimes B}:A\otimes B\xrightarrow{\epsilon\otimes\epsilon}k\otimes k=k$$
.

We have described the structure of a bialgebra: an associative multiplication with unit and an associative comultiplication with counit on the same (possibly graded) vector space, that are compatible in the sense that the unit and multiplication are coalgebra maps, or, equivalently, that the counit and comultiplication are algebra maps.

If the *H*-space *X* has an "inverse" – a map  $x \mapsto x^{-1}$  making it into a group in the homotopy category – then  $A = H_*(X)$  becomes a *Hopf algebra*: there is a map  $\chi : A \to A$  such that

commutes. This "canonical anti-automorphism"  $\chi$  exists uniquely if A is a connected graded bialgebra.

An important and motivating example of an ungraded Hopf algebra is given by the group algebra of a group G: k[G] admits the diagonal determined by  $\Delta g = g \otimes g$  for  $g \in G$ . The anti-automorphism is induced by the map  $g \mapsto g^{-1}$ . Indeed, a Hopf algebra with commutative diagonal is just a group object in the category of commutative coalgebras.

The k-linear dual of a k-coalgebra is a k-algebra. If a Hopf algebra is of finite type, its dual is again a Hopf algebra. So if X is an H-space of finite type then  $H^*(X)$  is also a Hopf algebra; the coproduct comes from the multiplication in X. It's a good exercise to go through our list of H-spaces and understand the Hopf algebra structure on their homology and cohomology. Here's an example, with coefficients in  $\mathbb{F}_2$ .

**Proposition 39.2.** Whitney sum renders BO a commutative H-space, and the map  $BO(1) \to BO$  sends the vector space generators of  $\overline{H}_*(BO(1))$  to polynomial generators  $a_i$ :

$$H_*(BO) = \mathbb{F}_2[a_1, a_2, \ldots].$$

Thus  $H_*(BO)$  is "bipolynomial": both homology and cohomology are polynomial algebras. The diagonal puts strong restrictions on the algebra structure of a Hopf algebra.

**Proposition 39.3** (Hopf and Leray). Let A be a graded connected Hopf algebra of finite type over a field of characteristic zero, and suppose the product is commutative. Then A is a free commutative graded algebra.

This means that A is a tensor product of a polynomial algebra on even generators and an exterior algebra on odd generators.

Corollary 39.4 (Hopf). The rational cohomology of any connected Lie group is an exterior algebra on odd generators.

Here's an analogue in finite characteristic.

**Proposition 39.5** (Borel). Let A be a graded connected Hopf algebra of finite type over a perfect field of characteristic p, and suppose that the product is commutative. If p is odd, A is an exterior algebra on odd generators tensored with a polynomial algebra on even generators modulo the ideal generated by  $p^k$ th powers of some of those generators. If p = 2, it is a polynomial algebra modulo  $2^k$ th powers of some generators.

#### The Steenrod algebra and its dual

Given two modules M and N over a Hopf algebra A, their tensor product over k has a canonical structure of module over A again:

$$A\otimes M\otimes N\xrightarrow{\Delta\otimes 1\otimes 1}A\otimes A\otimes (M\otimes N)\xrightarrow{1\otimes T\otimes 1}(A\otimes M)\otimes (A\otimes N)\xrightarrow{\varphi\otimes \varphi}M\otimes N$$

When A = k[G], this is the familiar diagonal tensor product of representations.

John Milnor [25] made the observation that the Cartan formula may be formulated in terms of a Hopf algebra structure on the Steenrod algebra itself:

39. HOPF ALGEBRAS 151

Proposition 39.6. The association

$$\Delta: \mathrm{Sq}^k \to \sum_{i+j=k} \mathrm{Sq}^i \otimes \mathrm{Sq}^j$$

extends to an algebra map, and provides the (commutative!) coproduct in a Hopf algebra structure on the Steenrod algebra  $A^*$ .

The Cartan formula then merely asserts that the cup product  $H^*(X) \otimes H^*(X) \to H^*(X)$  is a map of  $A^*$ -modules.

This is pleasant, but much more striking is the insight this gives you into the structure of the Steenrod algebra. Write  $A_*$  for the Hopf algebra dual to  $A^*$ .

**Proposition 39.7.** There exist elements  $\zeta_i \in A_{2^i-1}$  such that

$$A_* = \mathbb{F}_2[\zeta_1, \zeta_2, \ldots]$$

and (with  $\zeta_0 = 1$ )

$$\Delta \zeta_k = \sum_{i+j=k} \zeta_i^{2^j} \otimes \zeta_j .$$

This is equivalent to the Adem relations, but it's much easier to remember!

#### Lagrange and Thom

**Theorem 39.8.**  $H^*(MO)$  is free as module over the Steenrod algebra  $A^*$ .

Thom gave a fairly elaborate combinatorial proof of this theorem, writing down a basis. It turns out that a little bit of Hopf algebra technology makes this a lot simpler (or at least more believable).

**Lemma 39.9** ("Lagrange"; see e.g. [38], p. 94). Let A be a connected Hopf algebra and C a connected coalgebra with compatible A-module structure (so that the counit and diagonal are A-module maps). Let  $u \in C^0$  be such that  $\epsilon u = 1$ . If Au is free, then C is free as A-module.

The reference to Lagrange is this: A common application of this lemma is to take C to be a Hopf algebra containing A as a subalgebra. The result is that C is automatically free as an A-module. This is analogous to an observation attributed to Lagrange: If G is a group and H < G a subgroup then the translation action of H on G is free.

We will apply it with  $A = A^*$  and  $C = H^*(MO)$ . Then  $H^0(MO)$  is generated by the Thom class U, so what we have to do is to check that  $A^*$  acts freely on the Thom class.

This is proved using the following amazing observation of Thom's:

**Proposition 39.10** ([41]). Let  $\xi$  be a vector bundle over B, with Thom space Th( $\xi$ ). Then

$$\operatorname{Sq}^{i}U = w_{i} \cup U$$
.

This provides a definition of the Stiefel-Whitney classes that only uses the spherical fibration determined by the vector bundle, and indeed one that makes sense for any spherical fibration. It's quite easy to prove that these classes satisfy the axioms.

Exercise 39.11. Let M be a closed smooth n-manifold. By Poincaré duality, there is for each k a unique class  $v_k \in H^k(M)$  such that  $\langle v_k x, [M] \rangle = \langle \operatorname{Sq}^k x, [M] \rangle$  for all  $x \in H^{n-k}(M)$ . These are the "Wu classes" of the manifold. Show that  $\operatorname{Sq} v = w(\tau_M)$ . The tangential Stiefel-Whitney classes are therefore homotopy invariants of the manifold. Show that the normal Stiefel-Whitney classes are as well, and conclude that if two closed manifolds are homotopy equivalent then they are cobordant.

#### Conclusion

Stably, cohomology is represented by the Eilenberg Mac Lane spectrum. Pick a basis B for  $H^*(MO)$  as an  $A^*$ -module. Each element  $b \in B$  determines a homotopy class  $MO \to \Sigma^{|b|} H\mathbb{F}_2$ . Assembling them gives a map

$$MO \to \prod_{b \in B} \Sigma^{|b|} H\mathbb{F}_2$$

that is an isomorphism in mod 2 cohomology. Since the homotopy of MO is all 2-torsion, this map is actually weak equivalence.

The Eilenberg Mac Lane spectrum  $H\mathbb{F}_2$  is a commutative ring spectrum as well; the ring structure represents the cup product in cohomology. Its homology is thus a graded commutative algebra, namely the dual of the Steenrod algebra (which is the cohomology of  $H\mathbb{F}_2$ !). We can now estimate the size of  $\pi_*(MO)$ : Each basis element produces a suspended copy of  $A_*$  in  $H_*(MO) = \mathbb{F}_2[a_1, a_2, \ldots]$ . It looks like the Milnor generators,  $\zeta_i \in A_{2^i-1}$  account for some of the  $a_i$ 's. The rest must come from the homotopy. Some further argumentation leads to the conclusion that

$$\pi_*(MO) = \mathbb{F}_2[x_i : i+1 \text{ is not a power of } 2].$$

# 40 Applications of cobordism

#### Oriented cobordism

The Pontryagin-Thom collapse/transversality story is very general, and provides for example an isomorphism

$$\Omega_*^{SO} \cong \pi_*(MSO)$$
.

The oriented bordism groups were computed completely by C.T.C. Wall. All torsion is killed by 2. The first few groups are

$$\begin{array}{c|c|c|c|c|c|c|c|c|c|c|c|c|c|c|c|c|c|c|$$

Wall's computation is involved, but at least it's quite easy to determine  $\pi_*(MSO) \otimes \mathbb{Q}$ , by virtue of a general observation.

**Proposition 40.1.** For any spectrum E, the rational Hurewicz map

$$\pi_*(E) \otimes \mathbb{Q} \to H_*(E; \mathbb{Q})$$

is an isomorphism.

There are many ways to see this. For example, up to weak equivalence we may build up a spectrum by attaching cells. Both  $\pi_*^s$  and  $H_*$  are generalized homology theories; they send cofiber sequences to long exact sequence. So it's enough to show that the map is an isomorphism for the case of the sphere spectrum, where it follows from Serre's calculation of the rational homotopy of spheres.

So we have the commutative diagram of algebra isomorphisms

$$\Omega_*^{SO} \otimes \mathbb{Q} \longrightarrow \operatorname{Hom}(H^*(BSO; \mathbb{Q}), \mathbb{Q})$$

$$\downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$

where the top arrow is the characteristic number map sending [M] to  $(p \mapsto \langle p(\nu), [M] \rangle)$ . This already says something important: The rational Pontryagin numbers of a manifold determine is position in the rational oriented bordism ring. If they all vanish on a manifold M, some multiple of M bounds an oriented manifold-with-boundary.

Again, BSO is a commutative H-space, so  $H_*(BSO; \mathbb{Q})$  is a  $\mathbb{Q}$ -Hopf algebra, and so by the Hopf-Leray theorem it is a polynomial algebra. Since  $H^*(BSO; \mathbb{Q}) = \mathbb{Q}[p_1, p_2, \ldots]$ , we find that the homology is also a polynomial algebra on generators of dimension 4k. An analysis of the characteristic numbers of projective spaces shows that we may take the classes of the even complex projective spaces as the polynomial generators:

$$\Omega_*^{SO} \otimes \mathbb{Q} = \mathbb{Q}[[\mathbf{C}P^2], [\mathbf{C}P^4], \ldots].$$

#### Steenrod operations on the Thom class

When Thom tried to move beyond this rational calculation, and follow his analysis of the homotopy type of MO, he ran into trouble at odd primes. There are odd primary Steenrod operations, constructed in the same way as the squares were. (A nice reference for this is [12].) They take the form

$$P^i: H^n(X; \mathbb{F}_p) \to H^{n+2(p-1)i}(X; \mathbb{F}_p)$$
.

Now  $P^0x = x$ ,  $P^nx = x^p$  if |x| = 2n,  $P^nx = 0$  if |x| < 2n. There is also the Bockstein operation  $\beta: H^n(X; \mathbb{F}_p) \to H^{n+1}(X; \mathbb{F}_p)$ . These operations generate all the additive operations on mod p cohomology. The dual of  $A^*$ , for p odd, has the form [25]

$$A_* = E[\tau_0, \tau_1, \ldots] \otimes \mathbb{F}_p[\xi_1, \xi_2, \ldots], \quad |\tau_i| = 2p^i - 1, \quad |\xi_i| = 2p^i - 2.$$

Now  $H^1(BSO) = 0$  (we've killed  $w_1!$ ), so  $H^1(MSO) = 0$  as well; the Thom class  $U \in H^0(MSO)$  is killed by the Bockstein. It turns out that at p = 2,  $\beta = \operatorname{Sq}^1$  generates the annihilator ideal of U. This isn't so bad, since in fact

$$H^*(H\mathbb{Z}; \mathbb{F}_2) = A^*/A^* \operatorname{Sq}^1$$

and indeed  $MSO_{(2)}$  splits as a product of Eilenberg Mac Lane spectra (but now not just  $H\mathbb{F}_2$ 's but also  $H\mathbb{Z}_{(2)}$ 's).

But at an odd prime the situation is worse; the annihilator of  $U \in H^0(MSO; \mathbb{F}_p)$  is the left ideal generated by  $\beta P^i$  for all i. This implies, for example, that  $\beta P^1$  kills the Thom class of the normal bundle for any embedding of an oriented manifold into Euclidean space. The Thom spectrum MSO does not split as a product of Eilenberg Mac Lane spectra at an odd prime.

#### Duality

To see how this behavior of Steenrod operations on the Thom class leads to Thom's counterexample to the oriented form of Steenrod's question, we have to explain something about duality in homotopy theory. One of the motivations for the development of the stable homotopy category was a desire to make this story smooth. We will be brief, however.

Any finite complex K may be embedded into some finite dimensional Euclidean space  $\mathbb{R}^m$ . It can be arranged that the complement has a finite subcomplex L as a deformation retract. Alexander duality then gives us an isomorphism

$$\alpha: H_{m-q}(K) \cong \widetilde{H}^{q-1}(L)$$

for any q.

A homotopy-theoretic duality underlies this homological duality: L (or an appropriate desuspension of it in the stable homotopy category) is the "Spanier-Whitehead dual" of  $K_+$ . This geometry implies that with mod p coefficients this isomorphism commutes with the action of Steenrod operations. To make sense of this, use the universal coefficient theorem to reexpress homology as the linear dual of cohomology:

$$H_{m-q}(K) = H^{m-q}(K)^{\vee}$$
.

This imposes a "contragredient" right action of  $A^*$  on homology, with  $\theta \in A^r$  acting in such a way that

$$\langle x, c\theta \rangle = \langle \theta x, c \rangle$$
.

The isomorphism  $\alpha$  demands a *left* action of  $A^*$ , which is achieved by acting in homology by  $\overline{\theta}$  where  $\theta \mapsto \overline{\theta}$  is the Hopf anti-automorphism. The duality isomorphism is compatible with this action; that is, for  $c \in H_{m-q}(K)$ ,

$$\theta(\alpha c) = \alpha(c\overline{\theta}).$$

Now suppose that  $M \hookrightarrow \mathbb{R}^{n+k}$  is an embedding of a closed manifold, with normal bundle  $\nu$ . Let N be the closure of a regular neighborhood of M; it may be identified with  $\mathbb{D}(\nu)$ .

The complement  $\mathbb{R}^{n+k} - E(\nu)$  is our finite complex L. Here's an important point: we have equivalent cofiber sequences

$$\mathbb{R}^{n+k} - E(\nu) \longrightarrow \mathbb{R}^{n+k} \longrightarrow \mathbb{R}^{n+k} / (\mathbb{R}^{n+k} - E(\nu)) \cong \mathbb{D}(\nu) / \mathbb{S}(\nu) = \operatorname{Th}(\nu)$$

$$\downarrow^{\simeq} \qquad \qquad \downarrow^{\simeq}$$

$$L \longrightarrow CL \longrightarrow \Sigma L$$

so

$$Th(\nu) \simeq \Sigma L$$
.

In short, the Thom space of the normal bundle is (up to suspension) the Spanier-Whitehead dual of  $M_+$ . This is "Milnor-Spanier duality." Atiyah [1] proved a version of this for manifolds-with-boundary and it is often called "Atiyah duality."

The duality isomorphism is thus

$$\alpha: H_{n-q}(M) \xrightarrow{\cong} \overline{H}^{q+k}(\operatorname{Th}(\nu)).$$

Combining this with the Thom isomorphism gives an isomorphism

$$H_{n-q}(M) \xrightarrow{\cong} H^q(M)$$
.

This is Poincaré duality! and indeed a proof of it can be given along these lines.

#### Thom's counterexample

The duality map sends the fundamental class  $[M] \in H_n(M)$  to the Thom class  $U \in H^{n+k}(\operatorname{Th}(\nu))$ . Thus if  $\theta \in A^q$  annihilates the Thom class, we find that

$$\alpha([M]\overline{\theta}) = \theta(\alpha[M]) = \theta U = 0,$$

so for any  $x \in H^{n-q}(M)$ 

$$0 = \langle x, [M]\overline{\theta} \rangle = \langle \overline{\theta}x, [M] \rangle.$$

The image of  $\overline{\theta}$  in  $H^n(M)$  annihilates the fundamental class.

Let  $f: M \to X$  be any map, and  $x \in H^{n-q}(X)$ , and compute

$$\langle \overline{\theta}x, f_*[M] \rangle = \langle f^* \overline{\theta}x, [M] \rangle = \langle \overline{\theta}(f^*x), [M] \rangle = 0.$$

So in order for a class in  $H_n(X)$  to be carried by an oriented n-manifold the image of  $\overline{\theta}$  in  $H^n(X)$  must annihilate it.

For a specific example, Thom looked at  $K_1 = K(\mathbb{Z}/3\mathbb{Z}, 1)$ . This is an infinite "lens space." The cohomology is

$$H^*(K_1; \mathbb{F}_3) = E[e] \otimes \mathbb{F}_3[x], \quad |e| = 1, |x| = 2.$$

The Steenrod action is determined by

$$\beta e = x$$
,  $P^1 x = x^3$ .

The anti-automorphism is easily seen to send both  $\beta$  and  $P^1$  to their negatives, so

$$\overline{\beta P^1} = P^1 \beta$$
.

The class  $x^3 \in H^6(K_1; \mathbb{F}_3)$  is in the image of this class, so the dual homology class cannot be carried by an oriented closed manifold.

This is mod p; how about integrally? The Bocksteins tell us that  $\overline{H}_*(K_1; \mathbb{Z})$  is unfortunately concentrated in odd degrees, while  $P^1\beta H^*(K_1; \mathbb{F}_3) = 0$  in odd degrees. So Thom moves up a dimension to  $K_2 = K(\mathbb{Z}/3\mathbb{Z}, 2)$ . It's known, and not hard to verify by pulling back under the map  $K_1 \times K_1 \to K_2$  classifying the cup product, that  $\beta P^1\beta \iota_2 \neq 0$ . In homology, then, there is a class  $c \in H_8(K_2; \mathbb{F}_3)$  such that  $c\beta P^1\beta \neq 0$  in  $H_2(K_2; \mathbb{F}_3)$ . The class  $c\beta \in H_7(K_2; \mathbb{F}_3)$  can't be carried by an oriented manifold since

$$\langle P^1 \beta \iota, c \beta \rangle = \langle \beta P^1 (\beta \iota), c \rangle \neq 0.$$

But the Bockstein factors as

$$H_8(K_2; \mathbb{F}_3) \xrightarrow{\partial} H_7(K_2; \mathbb{Z}) \xrightarrow{\rho} H_7(K_2, \mathbb{F}_3)$$

so  $\partial c \in H_7(K_2; \mathbb{Z})$  can't be carried by a manifold since its reduction  $\beta c \in H_7(K_2; \mathbb{F}_3)$  can't be. The Postnikov system for MSO provides further obstructions.

#### The Brown-Peterson spectrum

The annihilator ideal of  $U \in H^0(MSO)$  at an odd prime is the two-sided ideal generated by the Bockstein. The quotient by this ideal turns out to be the cohomology of a ring spectrum – not an Eilenberg Mac Lane spectrum, but rather a new gadget called the "Brown-Peterson spectrum" and denoted (without reference to the prime p) by BP. (Frank Peterson, 1930–2000, was an MIT faculty member and long-time treasurer of the AMS.) At odd primes, MSO splits into a product of suspensions of BP. The mod p Thom class restricts to a map  $BP \to H\mathbb{F}_p$  that induces an embedding of  $H_*(BP) \hookrightarrow A_*$  as the polynomial algebra on the  $\xi$ 's.

The homotopy type of MU was studied by Milnor using the Adams spectral sequence. It turns out that

$$\pi_*(MU) = \mathbb{Z}[x_1, x_2, \ldots], \quad |x_i| = 2i.$$

It turns out that MU localized at any prime p splits as a product of the p-local Brown-Peterson spectrum as well (even if p = 2). The homotopy of BP is also a polynomial algebra, but now much sparser:

$$\pi_*(BP) = \mathbb{Z}_{(p)}[v_1, v_2, \ldots], \quad |v_i| = 2p^i - 2.$$

#### Surgery

There is a simple way to modify a manifold to give a new manifold with different topology but related by a cobordism. The most classical example of surgery occurs in dimension 2. Start with an embedded loop L in a closed surface M. Assume that the normal bundle of L is framed (always the case if M is orientable), so that we have an embedding of  $S^1 \times D^1$  into M. This kind of product is familiar! In general

$$\partial (D^p \times D^q) = S^{p-1} \times D^q \cup_{S^{p-1} \times S^{q-1}} D^p \times S^{q-1}.$$

In our case p=2 and q=1. We can remove the interior of  $\partial D^2 \times D^1$  and replace it with the interior of  $D^2 \times \partial D^1 = D^2 \times S^0$ , to get a new manifold M'. If the regular neighborhood of the loop was a belt around a waste (or "handle"), this has the effect of removing the belt and capping off the two body parts. This process is called "surgery."

What's a little harder to see is that  $D^p \times D^q$  can be used to construct a cobordism between M and M'.

A proof using Morse theory [26] shows that any two closed n manifolds in the same bordism class can be connected by a bordism constructed by a series of surgeries.

The surgery operation, pioneered by Milnor and Wallace and later Browder, Novikov, and Wall, led to an enormous research program aimed at the classification of manifolds up to diffeomorphism.

Exercise 40.2. Show that any positive dimensional oriented bordism class contains a connected manifold. Show that any oriented cobordism class of dimension at least 2 contains a simply connected manifold. Display counterexamples to these to statements in lower dimensions.

**Remark 40.3.** The surgery process involves killing homology groups in a manifold. It requires establishing that (1) the class is spherical – in the image of the Hurewicz map; (2) the map from a sphere is a smooth embedding; and (3) the normal bundle of this embedded sphere is trivial.

Typically the first requirement is met using the Hurewicz theorem; we try to kill bottom dimensional homology. The second can be achieved by Whitney embedding theorem as long as we are below the middle dimension of the manifold. The third is much more problematic. One way to ensure that the process can continue above dimension one is to work with framed bordism. The Pontryagin-Thom theorem identifies this with stable homotopy, so there is considerable interest in this case. The surgery process then works to find a "highly connected" representative of a framed bordism class in which the homology is concentrated in the middle dimension. When n is odd, any class in  $\Omega_n^{fr}$  has is represented by a homotopy sphere, since there is then no middle dimension. The same turns out to be true when n = 4k. When n = 4k + 2, there is a potential obstruction, the Kervaire invariant, with values in  $C_2$ . It's already visible in dimension 2, when the square of the nontrivially framed circle (which represents the stable homotopy class  $\eta$  of the Hopf map  $S^3 \to S^2$ ) is not framed null-bordant (since in fact  $\eta^2 \neq 0$ ). The higher dimensional Hopf fibrations give other examples in dimensions 6 and 14. William Browder proved that the invariant could be nonzero only in dimensions of the form  $2^{j}-2$ , and identified the invariant in terms of the Adams spectral sequence. In the 1970's examples were constructed using homotopy theory in dimensions 30 and 62, and in 2015 work of Mike Hill, Mike Hopkins, and Doug Ravenel finally showed that the invariant is in fact trivial for dimensions larger than 126 (where it remains unknown today).

#### Signature

This ability to move around within a cobordism class suggests that there are very few bordism invariants that one an derive from cohomology. What homological features of a manifold are cobordism invariants?

When M is an oriented 4k-manifold,  $H^{2k}(M;\mathbb{Q})$  supports a symmetric bilinear form, the "intersection form"

$$x \cdot y = \langle xy, [M] \rangle$$

which is nondegenerate on account of Poincaré duality. A fact from linear algebra: Any symmetric bilinear form over  $\mathbb{Q}$  is diagonal with respect to some basis. If it is nondegenerate then all the diagonal entries in the diagonalization are nonzero, and the difference between the number of positive entries and the number of negative entries is a independent of the diagonalizing basis. It is the *signature* of the bilinear form.

**Lemma 40.4** (Thom). The signature of the intersection form of an oriented 4k-manifold is a multiplicative oriented bordism invariant.

This follows from Lefschetz duality and the Künneth theorem. The result is a graded ring homomorphism

$$\sigma: \Omega_*^{SO} \to \mathbb{Z}[u], \quad |u| = 4.$$

Such a ring homomorphism is a *genus*. (This term entered mathematics from biology through Gauss's work on quadratic forms, and then spread to the genus of a surface, and then to other numerical invariants of manifolds.) Since the characteristic number map is a rational isomorphism, the value of a rational genus on a 4k-manifold M is some Pontryagin number.

Since the even complex projective spaces generate  $\Omega_*^{SO}$  rationally, giving the value of a genus on them completely specifies the value of the genus on any oriented manifold. Since  $\mathbb{C}P^{2k}$  obviously has signature 1 for any k, the signature is in a sense the simplest genus. For each k there is a polynomial

$$L_k \in H^{4k}(BSO; \mathbb{Q})$$

in the Pontryagin classes such that for any closed oriented 4k-manifold M

$$\sigma(M) = \langle L_k(\nu_M), [M] \rangle$$
.

This is the "Hirzebruch signature theorem." Identifying these polynomials is a beautiful story. The results are for example that

$$L_1 = \frac{p_1}{3}$$
,  $L_2 = \frac{7p_2 - p_1^2}{45}$ ,  $L_3 = \frac{62p_3 - 13p_2p_1 + p_1^3}{945}$ , ...

These formulas put divisibility conditions on certain combinations of Pontryagin classes of the normal bundle of an embedding of a closed manifold into Euclidean space: while the L-class has denominators, you get an integral class when you pair it against the fundamental class. The first normal Pontryagin class of an orientable 4-manifold has to be divisible by 3, for example.

The signature theorem in dimension 8 played a key role in Milnor's proof that certain  $S^3$ -bundles over  $S^4$  are not diffeomorphic to the standard 7-sphere despite being homeomorphic to it.

# Bibliography

- [1] Michael Atiyah, Thom complexes, Proceedings of the London Philosophical Society **11** (1961) 291–310.
- [2] Michael Atiyah, Bordism and cobordism, Proceedings of the Cambridge Philosophical Society 57 (1961) 200–208.
- [3] Aldridge Knight Bousfield, The localization of spaces with respect to homology, Topology 14 (1975) 133–150.
- [4] Glen Bredon, *Topology and Geometry*, Graduate Texts in Mathematics **139**, Springer-Verlag, 1993.
- [5] Edgar Brown, Cohomology Theories, Annals of Mathematics **75** (1962) 467–484.
- [6] Albrecht Dold, Lectures on Algebraic Topology, Springer-Verlag, 1995.
- [7] Andreas Dress, Zur Spektralsequenz einer Faserung, Inventiones Mathematicae 3 (1967) 172-178.
- [8] Björn Dundas, A Short Course in Differential Topology, Cambridge Mathematical Textbooks, 2018.
- [9] Rudolph Fritsch and Renzo Piccinini, Cellular Structures in Topology, Cambridge University Press, 1990.
- [10] Martin Frankland, Math 527 Homotopy Theory: Additional notes, http://uregina.ca/~franklam/Math527/Math527\_0204.pdf
- [11] Paul Goerss and Rick Jardine, Simplicial Homotopy Theory, Progress in Mathematics 174, Springer-Verlag, 1999.
- [12] Alan Hatcher, Algebraic Topology, Cambridge University Press, 2002.
- [13] Dale Husemoller, Fiber Bundles, Graduate Texts in Mathematics 20, Springer-Verlag, 1993.
- [14] Sören Illman, The equivariant triangulation theorem for actions of compact Lie groups. Mathematische Annalen **262** (1983) 487–501.
- [15] Niles Johnson, Hopf fibration fibers and base, https://www.youtube.com/watch?v=AKotMPGFJYk.
- [16] Dan Kan, Adjoint funtors, Transactions of the American Mathematical Society 87 (1958) 294–329.

160 BIBLIOGRAPHY

[17] Anthony Knapp, *Lie Groups Beyond an Introduction*, Progress in Mathematics 140, Birkaüser, 2002.

- [18] Wolfgang Lück, Survey on classifying spaces for families of subgroups, https://arxiv.org/abs/math/0312378.
- [19] Saunders Mac Lane, *Homology*, Springer Verlag, 1967.
- [20] Saunders Mac Lane, Categories for the Working Mathematician, Graduate Texts in Mathematics 5, Springer-Verlag, 1998.
- [21] Jon Peter May, A Consise Course in Algebraic Topology, University of Chicago Press, 1999, https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf.
- [22] Haynes Miller, Leray in Oflag XVIIA: The origins of sheaf theory, sheaf cohomology, and spectral sequences, Jean Leray (1906–1998), Gazette des Mathematiciens 84 suppl (2000) 17–34. http://math.mit.edu/~hrm/papers/ss.pdf
- [23] Haynes Miller and Douglas Ravenel, Mark Mahowald's work on the homotopy groups of spheres, *Algebraic Topology, Oaxtepec 1991*, Contemporary Mathematics **146** (1993) 1–30.
- [24] John Milnor, The geometric realization of a semi-simplicial complex, Annals of Mathematics 65 (1957) 357–362.
- [25] John Milnor, The Steenrod algebra and its dual, Annals of Mathematics 67 (1958) 150–171.
- [26] John Milnor, A procedure for killing homotopy groups of differentiable manifolds, Proceedings of Symposia in Pure Mathematics, III (1961) 39–55.
- [27] John Milnor and Jim Stasheff, Fiber Bundles, Annals of Mathematics Studies 76, 1974.
- [28] Steve Mitchell, Notes on principal bundles and classifying spaces.
- [29] Steve Mitchell, Notes on Serre Fibrations.
- [30] James Munkres, Topology, Prentice-Hall, 2000.
- [31] Daniel Quillen, Homotopical Algebra, Springer Lecture Notes in Mathematics 43, 1967.
- [32] Hommes de Science: 28 portraits, Hermann, 1990.
- [33] Graeme Segal, Classifying spaces and spectral sequences, Publications mathématiques de l'IHES 34 (1968) 105–112.
- [34] Paul Selick, Introduction to Homotopy Theory, American Mathematical Society, 1997.
- [35] Jean-Pierre Serre, Homologie singulière des espaces fibrés. Applications. Annals of Mathematics 54 (1951), 425–505.
- [36] William Singer, Steenrod squares in spectral sequences. I, II. Transactions of the Amererican Mathematical Society 175 (1973) 327–336 and 337–353.
- [37] Edwin Spanier, Algebraic Topology, McGraw Hill, 1966, and later reprints.

BIBLIOGRAPHY 161

[38] Robert Stong, *Notes on Cobordism Theory*, Mathematical Notes, Princeton University Press, 1968.

- [39] Neil Strickland, The category of CGWH spaces, http://www.neil-strickland.staff.shef.ac.uk/courses/homotopy/cgwh.pdf.
- [40] Arne Strøm, A note on cofibrations, Mathematica Scandinavica 19 (1966) 11–14.
- [41] René Thom, Quelques propriétés globales des variétés différentiables, Commentarii Mathematici Helvitici 28 (1954) 17–86.
- [42] Tammo tom Dieck, Algebraic Topology, European Mathematical Society, 2008.
- [43] Kalathoor Varadarajan, *The finiteness obstruction of C. T. C. Wall*, Canadian Mathematical Society Series of Monographs and Advanced Texts, John Wiley and Sons, 1989.
- [44] Charles Terrence Clegg Wall, Finiteness conditions for CW-complexes, Annals of Mathematics 81 (1965) 56–69.
- [45] Charles Weibel, An Introduction to Homological Algebra, Cambridge Studies in Advanced Mathematics 38, 1994.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.906 Algebraic Topology II Spring 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.