#### REPRESENTATIONS OF LIE GROUPS

#### PAVEL ETINGOF

#### To David Vogan on his 70th birthday with admiration

#### Contents

| Intr  | roduction                                                       | 5             |
|-------|-----------------------------------------------------------------|---------------|
| 1.    | Continuous representations of topological groups                | 8             |
| 1.1.  | Topological vector spaces                                       | 8             |
| 1.2.  | Continuous representations                                      | 11            |
| 1.3.  | Subrepresentations, irreducible representations                 | 13            |
| 2.    | K-finite vectors and matrix coefficients                        | 15            |
| 2.1.  | K-finite vectors                                                | 15            |
| 2.2.  | Matrix coefficients                                             | 16            |
| 2.3.  | The Peter-Weyl theorem                                          | 17            |
| 2.4.  | Partitions of unity                                             | 17            |
| 3.    | Algebras of measures on locally compact groups                  | 18            |
| 3.1.  | The space of measures                                           | 18            |
| 3.2.  | Support of a measure                                            | 20            |
| 3.3.  | Finitely supported measures                                     | 20            |
| 3.4.  | The algebra of measures on a locally compact group              | 22            |
| 4.    | Plancherel formulas, Dirac sequences, smooth                    |               |
|       | vectors                                                         | 24            |
| 4.1.  | Plancherel formulas                                             | 24            |
| 4.2.  | Dirac sequences                                                 | 25            |
| 4.3.  | Density of $K$ -finite vectors                                  | 26            |
| 4.4.  | Smooth vectors                                                  | 26            |
| 5.    | Admissible representations and $(\mathfrak{g}, K)$ -modules     | 28            |
| 5.1.  | Admissible representations                                      | 28            |
| 5.2.  | $(\mathfrak{g}, K)$ -modules                                    | 30            |
| 5.3.  | Harish-Chandra's admissibility theorem                          | 31            |
| 6.    | Weakly analytic vectors                                         | 33            |
| 6.1.  | Weakly analytic vectors and Harish-Chandra's analyticity        | 33            |
| 6.2.  | Elliptic regularity                                             | 33            |
| 6.3.  | Proof of Harish-Chandra's analyticity Theorem                   | 35            |
| 6.4.  | Applications of weakly analytic vectors                         | 35            |
| 7.    | Infinitesimal equivalence and globalization                     | 37            |
|       | a a                                                             |               |
| 7.1.  | Infinitesimal equivalence                                       | 37            |
| 7.2.  | Dixmier's lemma and infinitesimal character                     | 38            |
| 7.3.  | Harish-Chandra's globalization theorem                          | 38            |
| 8.    | Highest weight modules and Verma modules                        | 41            |
| 8.1.  | g-modules with a weight decomposition                           | 41            |
| 8.2.  | Verma modules                                                   | 41            |
| 8.3.  | Irreducible highest weight g-modules                            | 43            |
| 8.4.  | Exercises                                                       | 43            |
| 9.    | Representations of $SL_2(\mathbb{R})$                           | 48            |
| 9.1.  | Irreducible $(\mathfrak{g}, K)$ -modules for $SL_2(\mathbb{R})$ | 48            |
| 9.2.  | Realizations                                                    | 50            |
| 9.3.  | Unitary representations                                         | 51            |
| 10.   | Chevalley restriction theorem and Chevalley-                    |               |
|       | Shephard-Todd theorem                                           | 54            |
| 10.1. | Chevalley restriction theorem                                   | 54            |
| 10.2. | Chevalley-Shephard-Todd theorem, part I                         | 56            |
| 11.   | Proof of the CST theorem, part I                                | 58            |
| 11.1. | Proof of the CST theorem, part I, the "if" direction            | 58            |
| 11.2. | 0 1                                                             | 60            |
| 11.3. | Proof of the CST theorem, part I, the "only if" direction       | 61            |
| 12.   | Chevalley-Shephard-Todd theorem, part II                        | 63            |
| 12.1. |                                                                 | 63            |
| 12.2. | $\mathbb{C}[V]$ as a $\mathbb{C}[V]^G$ -module                  | 63            |
| 12.3. | Graded modules                                                  | 64            |
| 12.4. | Koszul complexes                                                | 66            |
| 12.5. | Syzygies                                                        | 66            |
| 12.6. | 1 0                                                             | 67            |
| 12.7. | g i                                                             | 68            |
| 12.8. | ,                                                               | 69            |
| 13.   | Kostant's theorem                                               | 71            |
| 13.1. | ~                                                               | 71            |
| 13.2. |                                                                 | 73            |
| 13.3. | (2)                                                             | 74            |
| 14.   | Harish-Chandra isomorphism, maximal quotients                   | 76            |
| 14.1. | 1                                                               | 76            |
| 14.2. | Maximal quotients                                               | 77            |
| 15.   | Category $\mathcal{O}$ of $\mathfrak{g}$ -modules - I           | 79            |
| 15.1. |                                                                 | 79            |
| 15.2. | •                                                               | 81            |
| 15.3. |                                                                 | 82            |
| 15.4. | 1                                                               | 82            |
| 16.   | Category $\mathcal{O}$ of $\mathfrak{g}$ -modules - II          | 84            |
| 16 1  | Dominant weights                                                | 84            |
|       | Projective objects                                              | 84            |
|       | Projective objects in $\mathcal{O}$                             | 86            |
| 17.   | The nilpotent cone of g                                         | 88            |
| 17.1. | <u> </u>                                                        | 88            |
|       | The principal $\mathfrak{sl}_2$ subalgebra                      | 88            |
| 17.3. | Regular elements                                                | 89            |
| 17.4. |                                                                 | 89            |
| 18.   | Maps of finite type, Duflo-Joseph theorem                       | 92            |
|       | Maps of finite type                                             | 92            |
|       | The Duflo-Joseph theorem                                        | 94            |
|       | infinitesimal characters of Harish-Chandra bimodules            | 95            |
| 19.   | Principal series representations                                | 96            |
|       | Residual finiteness of $U(\mathfrak{g})$                        | 96            |
|       | Principal series                                                | 96            |
|       | The functor $H_{\lambda}$                                       | 99            |
| 20.   | BGG reciprocity and BGG Theorem                                 | 100           |
| 20.1. | - v                                                             | 100           |
|       | Standard filtrations                                            | 100           |
|       | BGG reciprocity                                                 | 102           |
|       | The duality functor                                             | 103           |
|       | The Jantzen filtration                                          | 104           |
| 20.6. | The BGG theorem                                                 | 104           |
| 21.   | Multiplicities in category $\mathcal{O}$                        | 106           |
| 21.1. | The Hecke algebra                                               | 106           |
| 21.2. | The Bruhat order                                                | 107           |
| 21.3. | Kazhdan-Lusztig polynomials                                     | 108           |
| 21.4. | Kazhdan-Lusztig conjecture                                      | 109           |
| 22.   | Projective functors - I                                         | 110           |
| 22.1. | Projective functors and projective $\theta$ -functors.          | 110           |
| 22.2. | Lifting projective $\theta$ -functors.                          | 111           |
| 22.3. | Decomposition of projective functors                            | 113           |
| 23.   | Projective functors - II                                        | 114           |
| 23.1. | The Grothendieck group of $\mathcal{O}$                         | 114           |
| 23.2. | W-invariance                                                    | 115           |
| 23.3. | Classification of indecomposable projective functors            | 117           |
| 24.   | Applications of projective functors - I                         | 119           |
| 24.1. | Translation functors                                            | 119           |
| 24.2. | Two-sided ideals in $U_{\theta}$ and submodules of Verma modu   |               |
| 25.   | Applications of projective functors - II                        | 123           |
| 25.1. | 1                                                               | 123           |
| 25.2. | Classification of simple Harish-Chandra bimodules               | 124           |
|       | 3                                                               |               |
| 25.3. | Equivalence between category $\mathcal{O}$ and category of      |               |
|       | Harish-Chandra bimodules                                        | 125           |
| 26.   | Representations of $SL_2(\mathbb{C})$                           | 129           |
| 26.1. | Harish-Chandra bimodules for $\mathfrak{sl}_2(\mathbb{C})$      | 129           |
| 26.2. | Representations of $SL_2(\mathbb{C})$ .                         | 130           |
| 27.   | Geometry of complex semisimple Lie groups                       | 133           |
| 27.1. | The Borel-Weil theorem                                          | 133           |
| 27.2. | The Springer resolution                                         | 135           |
| 27.3. | The symplectic structure on coadjoint orbits                    | 136           |
| 27.4. | The algebra of functions on $T^*\mathcal{F}$                    | 137           |
| 28.   | D-modules - I                                                   | 139           |
| 28.1. | Differential operators                                          | 139           |
| 28.2. | D-modules                                                       | 140           |
| 28.3. | D-modules on non-affine varieties                               | 140           |
| 28.4. | Connections                                                     | 141           |
| 28.5. | Direct and inverse images                                       | 142           |
| 29.   | The Beilinson-Bernstein Localization Theorem                    | 143           |
| 29.1. | The Beilinson-Bernstein localization theorem for the ze         | ero           |
|       | infinitesimal character                                         | 143           |
| 29.2. | Twisted differential operators and $D$ -modules                 | 144           |
| 29.3. | The localization theorem for non-zero infinitesimal             |               |
|       | characters                                                      | 145           |
| 30.   | D-modules - II                                                  | 147           |
| 30.1. | Support of a quasicoherent sheaf                                | 147           |
| 30.2. | Restriction to an open subset                                   | 147           |
| 30.3. | Kashiwara's theorem                                             | 149           |
| 30.4. | Equivariant $D$ -modules                                        | 150           |
| 31.   | Applications of D-modules to representation theorem             | <b>ry</b> 154 |
| 31.1. | Classification of irreducible equivariant $D$ -modules for      |               |
|       | actions with finitely many orbits                               | 154           |
| 31.2. | Classification of irreducible Harish-Chandra modules            | 155           |
| 31.3. | Applications to category $\mathcal{O}$                          | 156           |
| Refer | rences                                                          | 159           |

#### Introduction

These notes are based on the course "Representations of Lie groups" taught by the author at MIT in Fall 2021 and Fall 2023. This is the third semester of Lie theory, which follows the standard 2-semester introductory sequence, "Lie groups and Lie algebras I, II" (for the author's notes of these courses, see [E]). The notes cover the basic theory of representations of non-compact semisimple Lie groups, with a more in-depth study of (non-holomorphic) representations of complex groups.

Representation theory of (non-compact) semisimple Lie groups is an important and deep area of Lie theory with numerous applications, ranging from physics (quantum field theory) to analysis (harmonic analysis on homogeneous spaces) and number theory (the theory of automorphic forms, Langlands program). It is a synthetic subject which, besides basic Lie theory and representation theory, uses a plethora of techniques from many other fields, notably analysis, commutative and non-commutative algebra, category theory, homological algebra and algebraic geometry. For basic Lie theory (in particular, structure and finite-dimensional representations of compact Lie groups and semisimple complex Lie algebras) we will rely on the notes [E]. In other areas, most of the time we review the necessary material before using it, but at least a superficial previous familiarity with these subjects will be helpful to the reader.

Representation theory of semisimple Lie groups originated in the work of Bargmann Ba and Gelfand-Naimark GN in the late 1940s in the case of  $SL_2$  and was systematically developed by Harish-Chandra in 1950s and 1960s, and later developed by many prominent mathematicians, notably R. Langlands, who classified the irreducible representations (|La|). A new conceptual approach to the representation theory of complex semisimple Lie groups was proposed by J. Bernstein and S. Gelfand around 1980 ([BG]) based on their previous pioneering work with I. Gelfand on category  $\mathcal{O}$ . This ultimately made the representation theory of semisimple Lie groups a part of the new subject of geometric representation theory that emerged in early 1980s from the Kazhdan-Lusztig conjecture on multiplicities in category  $\mathcal{O}$  and its proof using geometric methods (D-modules and perverse sheaves) by Beilinson-Bernstein and Brylinski-Kashiwara. Since that time the theory has made giant strides forward (for example, computation of irreducible characters of real reductive groups by G. Lusztig and D. Vogan in 1980s, now implemented in the computer package ATLAS, as well as progress in the classification of unitary representations described in [ALTV]), and the connection with geometry has remained the main driving force of its development all along.

The organization of the notes is as follows. In Sections 1-7 we discuss the analytic aspects of the theory, arising from the fact that interesting representations of non-compact Lie groups are infinite-dimensional and realized in topological vector spaces. We introduce the main analytic tools, such as Fréchet spaces, the convolution algebra of measures on the group, K-finite, smooth and analytic vectors, matrix coefficients, and then discuss theorems of Harish-Chandra which allow one to reduce the study of representations of a semisimple Lie group G to the study of admissible  $(\mathfrak{g}, K)$ -modules, where  $\mathfrak{g} = \text{Lie}G$  and K is a maximal compact subgroup of G, and thereby to the purely algebraic problem of studying Harish-Chandra modules. Then in Section 8 we recall the theory of highest weight modules for  $\mathfrak{g}$ , and in Section 9 use the developed theory to classify irreducible and unitary irreducible representations of  $SL_2(\mathbb{R})$ .

The rest of the notes is almost completely algebraic. Namely, in Sections 10-14, we prove a number of fundamental properties of the action of the Weyl group W on the symmetric algebra  $S\mathfrak{h}$  on the Cartan subalgebra  $\mathfrak{h}$  and of the universal enveloping algebra  $U(\mathfrak{g})$  for a semisimple complex Lie algebra  $\mathfrak{g}$  – the Chevalley restriction theorem, Chevalley-Shephard-Todd theorems ([Che],[ST]), Kostant theorems ([Ko]). Then in Sections 15, 16 we develop the basic theory of the BGG category  $\mathcal{O}$ , and in Section 17 discuss the nilpotent cone of  $\mathfrak{g}$ , proving that it is a reduced irreducible variety. In Sections 18, 19 we prove the Duflo-Joseph theorem and discuss principal series representations of the complex Lie group G. Here we also introduce a functor  $H_{\lambda}$  which connects category  $\mathcal{O}$  with the category Harish-Chandra bimodules for  $\mathfrak{g}$ . In Sections 20, 21 we continue to study category  $\mathcal{O}$  (BGG theorem, BGG reciprocity, multiplicities, formulation of the Kazhdan-Lusztig conjectures). In Sections 22-25 we give an exposition of the theory of projective functors of J. Bernstein and S. Gelfand ([BG]) and give its applications to representation theory of complex groups (classification of irreducible representations, describing the category of Harish-Chandra bimodules in terms of category  $\mathcal{O}$ ) as well as to the structure theory of  $U(\mathfrak{g})$  (Duflo's theorem on primitive ideals). In Section 26, we apply these results to the group  $G = SL_2(\mathbb{C})$  and give an explicit classification of its irreducible and unitary irreducible representations. Finally, in Sections 27-31 we outline the geometric approach to representation theory of semisimple Lie groups, starting from Borel-Weil theorem and then proceeding to D-modules, the Beilinson-Bernstein

localization theorem, and classification of irreducible Harish-Chandra modules by data attached to K-orbits on G/B. In these sections the material is more advanced and the exposition is less detailed.

The notes are divided into 31 sections which roughly correspond to 80 minute lectures. So there is a bit more material than in a 1-semester course (which normally consists of 26 lectures). So if these notes are used to teach a course, some material (roughly equivalent to 5 sections) should be skipped. A lot of important material is included in exercises, which are often provided with detailed hints and may be assigned as homework.

**Disclaimer:** These notes contain nothing original except mistakes of the author, and in all sections the exposition is mostly adopted from various existing sources – original articles, textbooks and lecture notes. For example, the exposition in Sections 1-7 is mostly borrowed from [G] and [L], in Sections 20, 21 parts are adopted from [Hu], in Sections 22-25 we closely follow [BG], and in Sections 28-30 we follow [BCEY]. Since the material is standard, we do not always give a reference.

Also, these notes only scratch the surface in the deep subject of representations of semisimple Lie groups. For a more in-depth study of this theory, we recommend the books [K], [ABV] and the lectures [KT]; for recent progress on unitary representations see [ALTV]. For more about category  $\mathcal{O}$  we refer the reader to [Bez], [Hu]. For more on the theory of D-modules and their applications to representation theory we recommend the book [HTT].

Acknowledgments. I'd like to thank David Vogan who prompted me to rework the MIT Lie groups graduate sequence, of which this is part 3 (the notes for parts 1 and 2 can be found in [E]). It is my pleasure to dedicate this text to David's 70th birthday.

I am grateful to the students of the MIT course "Representations of Lie groups" in the academic years 2021/2022 and 2023/2024 for feedback, and to Jeffrey Lu and David Vogan for reading the manuscript and many corrections. This work was partially supported by the NSF grant DMS-DMS-2001318.

#### 1. Continuous representations of topological groups

This course will be about representations of Lie groups, with a focus on non-compact groups. While irreducible representations of compact groups are all finite-dimensional, this is not so for non-compact groups, whose most interesting irreducible representations are infinite-dimensional. Thus to have a sensible representation theory of non-compact Lie groups, we need to consider their **continuous** representations on **topological vector spaces**.

- 1.1. **Topological vector spaces.** All representations we'll consider will be over the field  $\mathbb{C}$ , which is equipped with its usual topology. Recall that a **topological vector space** over  $\mathbb{C}$  is a complex vector space V with a topology in which addition  $V \times V \to V$  and scalar multiplication  $\mathbb{C} \times V \to V$  are continuous. The topological vector spaces V we'll consider will always be assumed to have the following properties:
- $\bullet$  Hausdorff: any two distinct points of V have disjoint neighborhoods.
- locally convex:  $0 \in V$  (hence every point) has a base of convex neighborhoods.<sup>1</sup> Equivalently, the topology on V is defined by a family of **seminorms**<sup>2</sup>  $\{\nu_{\alpha}, \alpha \in A\}$ : a base of neighborhoods of 0 is formed by finite intersections of the sets  $U_{\alpha,\varepsilon} := \{v \in V | \nu_{\alpha}(v) < \varepsilon\}, \alpha \in A, \varepsilon > 0$ . I.e., it is the weakest of the topologies in which all  $\nu_{\alpha}$  are continuous.
  - sequentially complete: every Cauchy sequence<sup>3</sup> is convergent. Also, unless specified otherwise, we will assume that V is
- first countable:  $0 \in V$  (equivalently, every point of V) has a countable base of neighborhoods. By the Birkhoff-Kakutani theorem, this is equivalent to V being **metrizable** (topology defined by a metric), and moreover this metric can be chosen translation invariant: d(x,y) = D(x-y) for some function  $D: V \to \mathbb{R}_{\geq 0}$ .

In this case V is called a **Fréchet space**. For example, every **Banach space** (a complete normed space), in particular, **Hilbert space** is a Fréchet space.

Recall that a Hausdorff topological vector space V is said to be **complete** if whenever V is realized as a dense subspace of a Hausdorff

<sup>&</sup>lt;sup>1</sup>Recall that a set  $X \subset V$  is **convex** if for any  $x, y \in X$  and  $t \in [0, 1]$  we have  $tx + (1 - t)y \in X$ .

<sup>&</sup>lt;sup>2</sup>Recall that a **seminorm** on V is a function  $\nu: V \to \mathbb{R}_{\geq 0}$  such that  $\nu(x+y) \leq \nu(x) + \nu(y)$  and  $\nu(\lambda x) = |\lambda|\nu(x)$  for  $x, y \in V$ ,  $\lambda \in \mathbb{C}$ . A seminorm is a **norm** iff  $\nu(x) = 0$  implies x = 0.

<sup>&</sup>lt;sup>3</sup>Recall that a sequence  $a_n \in V$  is **Cauchy** if for any neighborhood U of  $0 \in V$  there exists N such that for  $n, m \geq N$  we have  $a_n - a_m \in U$ .

topological vector space  $\overline{V}$  with induced topology, we have  $V=\overline{V}$ . Every complete space is sequentially complete, and the converse holds for metrizable spaces (albeit not in general). Thus a Fréchet space can be defined as a locally convex complete metrizable topological vector space.

Alternatively, a Fréchet space may be defined as a complete topological vector space with topology defined by a *countable* system of seminorms  $\nu_n: V \to \mathbb{R}, n \geq 1$ . Thus, a sequence  $x_m \in V$  goes to zero iff  $\nu_n(x_m)$  goes to zero for all n. Note that the Hausdorff property is then equivalent to the requirement that any vector  $x \in V$  with  $\nu_n(x) = 0$  for all n is zero.

A translation-invariant metric on a Fréchet space may be defined by the formula

$$d(x,y) = D(x-y), \ D(x) := \sum_{n=1}^{\infty} \frac{1}{2^n} \frac{\nu_n(x)}{1 + \nu_n(x)}.$$

Note however that D is not a norm, as it is not homogeneous: for  $\lambda \in \mathbb{C}$ ,  $D(\lambda x) \neq |\lambda| D(x)$ . If we had a finite collection of seminorms, we could define a norm simply by  $D(x) := \sum_n \nu_n(x)$ , but if there are infinitely many, this sum may not converge, and we have to sacrifice the homogeneity property for convergence. In fact, the examples below show that there are important Fréchet spaces that are not Banach (i.e., do not admit a single norm defining the topology). We also note that the same Fréchet space structure on V can be defined by different systems of seminorms  $\nu_n$ , and there is also nothing canonical about the formula for D (e.g., we can replace  $\frac{1}{2^n}$  by any sequence  $a_n > 0$  with  $\sum_n a_n < \infty$ ), so  $\nu_n$  or D are not part of the data of a Fréchet space.

Finally, unless specified otherwise, we will assume that V is

• **second countable:** admits a countable base. For metrizable spaces, this is equivalent to being **separable** (having a dense countable subset).

**Example 1.1.** 1. Let X be a locally compact second countable Hausdorff topological space (e.g., a manifold). Then it is easy to see that X can be represented as a countable nested union of compact subsets:  $X = \bigcup_{n\geq 1} K_n$ ,  $K_1 \subset K_2 \subset \ldots$  Let C(X) be the space of continuous complex-valued functions on X. We can then define seminorms  $\nu_n$  by

$$\nu_n(f) = \max_{x \in K_n} |f(x)|.$$

(this is well defined since  $K_n$  are compact). This makes C(X) into a Fréchet space, and this structure is independent on the choice of the

The convergence in C(X) is uniform convergence on sequence  $K_n$ . compact sets.

By the Tietze extension theorem, if  $K \subset L$  are compact Hausdorff spaces then the restriction map  $C(L) \to C(K)$  is surjective. So  $C(X) = \lim_{n \to \infty} C(K_n)$  as a vector space. Alternatively, without making any choices, we may write  $C(X) = \underset{\longleftarrow}{\lim}_{K \subset X} C(K)$ , where K runs over compact subsets of X.

2. If X is a manifold and  $0 \le k \le \infty$ , we can similarly define a Fréchet space structure on the space  $C^k(X)$  of k times continuously differentiable functions on X. Namely, cover X by countably many closed balls  $K_n$ , each equipped with a local coordinate system, and set

$$\nu_{n,m}(f) = \max_{x \in K_n} \|d^m f(x)\|, \ 0 \le m \le k$$

where  $d^m f(x)$  is the m-th differential of f at x, comprising the m-th mixed partial derivatives of f at x with respect to the local coordinates (these are labeled by two indices rather than one, but it does not matter since this collection is still countable). The convergence in  $C^k(X)$  is uniform convergence with all derivatives up to k-th order on compact sets.

These spaces are not Banach unless X is compact. Moreover,  $C^{\infty}(X)$ is not Banach even for compact X (of positive dimension). For example, for  $C^{\infty}(S^1)$  we may take,

$$\nu_m(f) = \sum_{i=0}^{m} \max_{x \in S^1} |f^{(i)}(x)|,$$

but this is still an infinite collection. Note that these are all norms, not just seminorms, but each of them taken separately does not define the correct topology on  $C^{\infty}(S^1)$  (namely,  $\nu_m$  defines the incomplete topology induced by embedding  $C^{\infty}(S^1)$  as a dense subspace into the Banach space  $C^m(S^1)$  with norm  $\nu_m$ ).

3. The Schwartz space  $\mathcal{S}(\mathbb{R}) \subset C^{\infty}(\mathbb{R})$  is the space of functions fwith

$$\nu_{m,n}(f) := \sup_{x \in \mathbb{R}} |x^n \partial^m f(x)| < \infty, \ m, n \ge 0.$$

This system of seminorms can then be used to give  $\mathcal{S}(\mathbb{R})$  the structure of a (non-Banach) Fréchet space. The same definition can be used for the Schwartz space  $\mathcal{S}(\mathbb{R}^N)$ , by taking  $n=(n_1,...,n_N), m=(m_1,...,m_N)$ ,  $x = (x_1, ..., x_N), \ \partial = (\partial_1, ..., \partial_N), \ \text{and}$ 

$$x^n := \prod_i x_i^{n_i}, \ \partial^m := \prod_i \partial_i^{m_i}.$$

It is well known that all these spaces are separable (check it!).

1.2. Continuous representations. Let G be a locally compact topological group, for example, a Lie group.<sup>4</sup>

**Definition 1.2.** A **continuous representation** of G is a topological vector space V with a *continuous* linear action  $a: G \times V \to V$ .<sup>5</sup>

In particular, a continuous representation gives a homomorphism  $\pi: G \to \operatorname{Aut}(V)$  from G to the group of continuous automorphisms of V (i.e., continuous linear maps  $V \to V$  with continuous inverse).

**Definition 1.3.** A continuous representation is called **unitary** if V is a Hilbert space and for all  $g \in G$ , the operator  $\pi(g) : V \to V$  is unitary; in other words,  $\pi$  lands in the unitary group  $U(V) \subset \operatorname{Aut}(V)$ .

**Exercise 1.4.** Let  $1 \leq p < \infty$  and  $L^p(\mathbb{R})$  be the Banach space of measurable functions  $f : \mathbb{R} \to \mathbb{R}$  with

$$||f||_p = \left(\int_{\mathbb{R}} |f(x)|^p dx\right)^{\frac{1}{p}} < \infty$$

(modulo functions vanishing outside a set of measure zero), with norm  $f \mapsto ||f||_p$ . The Lie group  $\mathbb{R}$  acts on  $L^p(\mathbb{R})$  by translation.

- (i) Show that this is a continuous representation, which is unitary for p=2 (use approximation of  $L^p$  functions by continuous functions with compact support).
  - (ii) Prove the same for the Fréchet spaces  $C^k(\mathbb{R})$  and  $\mathcal{S}(\mathbb{R})$ .

Let G be a locally compact group, for example a Lie group. In this case G is known to have a unique up to scaling right-invariant **Haar** measure dx. For Lie groups, this measure is easy to construct by spreading a nonzero element of  $\wedge^n \mathfrak{g}^*$ ,  $\mathfrak{g} = \text{Lie}(G)$ ,  $n = \dim \mathfrak{g}$ , over the group G by right translations. Thus we can define the Banach space  $L^p(G)$  similarly to the case  $G = \mathbb{R}$ . It is easy to generalize Exercise 1.4 to show that the translation action of G on  $L^p(G)$  and  $C^k(G)$  is continuous, with  $L^2(G)$  unitary.

continuous operator has a continuous inverse.

<sup>&</sup>lt;sup>4</sup>Topological groups will always be assumed Hausdorff and second countable. Important examples of locally compact topological groups include groups  $\mathbf{G}(F)$ , where F is a local field and  $\mathbf{G}$  is an algebraic group defined over F. If F is archimedean ( $\mathbb{R}$  or  $\mathbb{C}$ ) then  $\mathbf{G}(F)$  is a real, respectively complex, Lie group. Another example important in number theory is  $\mathbf{G}(\mathbb{A}_k)$ , where k is a global field,  $\mathbb{A}_k$  is its ring of adéles, and  $\mathbf{G}$  is an algebraic group over k.

<sup>&</sup>lt;sup>5</sup>It is easy to see that it suffices to check this property at points (1, v) for  $v \in V$ . <sup>6</sup>Note that by the open mapping theorem, in a Fréchet space any invertible

**Example 1.5.** Let X be a manifold with a right action of a Lie group G. We'd like to say that we have a unitary representation of G on  $L^2(X)$  via (gf)(x) = f(xg). But for this purpose we need to fix a G-invariant measure on X, and such a nonzero measure does not always exist (e.g.,  $G = SL_2(\mathbb{R})$ ,  $X = \mathbb{RP}^1 = S^1$ ).

The way out is to use **half-densities** on X rather than functions. Namely, recall that if dim X = m then the canonical line bundle  $K_X := \wedge^m T^*X$  has structure group  $\mathbb{R}^\times$ . Consider the character  $\mathbb{R}^\times \to \mathbb{R}^{>0}$  given by  $t \mapsto |t|^s$ ,  $s \in \mathbb{R}$ , and denote the associated line bundle  $|K|^s$ . This is called the bundle of s-densities on X (in particular, densities for s = 1 and **half-densities** for  $s = \frac{1}{2}$ ). Thus in local coordinates s-densities are ordinary functions, but when we change coordinates by  $x \mapsto x' = x'(x)$ , these functions change as

$$f = f' |\det(\frac{\partial x'}{\partial x})|^s$$
.

The benefit of half-densities is that for any half-density f, the expression  $|f|^2$  is naturally a density on X, which canonically defines a measure that can be integrated over X. As a result, the space  $L^2(X)$  of half-densities f on X with

$$\|f\|_2 = \sqrt{\int_X |f|^2} < \infty$$

is a Hilbert space attached canonically to X (without choosing any additional structures), and any diffeomorphism  $g: X \to X$  defines a unitary operator on  $L^2(X)$ . Thus similarly to Exercise 1.4,  $L^2(X)$  is a unitary representation of G. Note that if X has a G-invariant measure, this is the same as a representation of G on  $L^2$ -functions on X.

In particular, we see that we have a unitary representation of  $G \times G$  on  $L^2(G)$  by left and right translation even though the right-invariant Haar measure is not always left-invariant.

If V is finite-dimensional,  $\operatorname{Aut}(V) = GL(V)$  is just the group of invertible matrices, and the continuity condition for representations of G is just that the map  $\pi: G \to \operatorname{Aut}(V)$  is continuous in the usual topology. Then it is well known that this map is smooth and is determined by the corresponding Lie algebra map  $\mathfrak{g} \to \operatorname{End}(V) = \mathfrak{gl}(V)$ , and this correspondence is a bijection if G is simply connected. In this way the theory of finite-dimensional continuous representations of connected Lie groups is immediately reduced to pure algebra.

On the other hand, for infinite-dimensional representations the situation is more tricky, as there are several natural topologies on Aut(V).

One of them is the **strong topology** of  $\operatorname{End}(V)$  (continuous endomorphisms of V), in which  $T_n \to T$  iff for all  $v \in V$  we have  $T_n v \to T v$ . It is clear that if  $(V, \pi)$  is a continuous representation of G then the map  $\pi: G \to \operatorname{Aut}(V)$  is continuous in the strong topology, but the converse is not true, in general. However, the converse holds for Banach spaces (in particular, for unitary representations).

**Proposition 1.6.** If V is a Banach space then a representation  $(V, \pi)$  of G is continuous if and only if the map  $\pi : G \to \operatorname{Aut}(V)$  is continuous in the strong topology.

*Proof.* Recall the **uniform boundedness principle**: If  $T_n$  is a sequence of bounded operators from a Banach space V to a normed space and for any  $v \in V$  the sequence  $T_n v$  is bounded then the sequence  $||T_n||$  is bounded.

Now assume that  $\pi$  is continuous in the strong topology. Let  $g_n \in G$ ,  $g_n \to 1$ , and  $v_n \to v \in V$ . Since G is second countable, our job is to show that  $\pi(g_n)v_n \to v$ . We know that  $\pi(g_n)v \to v$ , as  $\pi(g_n) \to 1$  in the strong topology. So it suffices to show that  $\pi(g_n)(v_n - v) \to 0$ . As  $v_n - v \to 0$ , it suffices to show that the sequence  $\|\pi(g_n)\|$  is bounded. But this follows from the uniform boundedness principle.

**Remark 1.7.** 1. Another topology on  $\operatorname{End}(V)$  for a Banach space V is the **norm topology**, defined by the operator norm. It is stronger than the strong topology, and a continuous representation  $\pi: G \to \operatorname{Aut}(V)$  does **not** have to be continuous in this topology. For example, the action of  $\mathbb{R}$  on  $L^2(\mathbb{R})$  is not. Indeed, denoting by  $T_a$  the operator  $\pi(a)$  given by  $(T_a f)(x) = f(x+a)$ , we have  $||T_a - 1|| = 2$  for all  $a \neq 0$  (show it!).

2. If dim  $V = \infty$  then  $\operatorname{Aut}(V)$  is **not** a topological group with respect to strong topology (multiplication is not continuous).

#### 1.3. Subrepresentations, irreducible representations.

**Definition 1.8.** A subrepresentation of a continuous representation V of G is a *closed* G-invariant subspace of V. We say that V is **irreducible** if its only subrepresentations are 0 and V.

**Example 1.9.** The translation representation of  $\mathbb{R}$  on  $L^2(\mathbb{R})$  is not irreducible, although this is not completely obvious. To see this, we apply Fourier transform, which is a unitary automorphism of  $L^2(\mathbb{R})$ . The Fourier transform maps the operator  $T_a$  to the operator of multiplication by  $e^{iax}$ . But it is easy to construct closed subspaces of  $L^2(\mathbb{R})$  invariant under multiplication by  $e^{iax}$ : take any measurable subset  $X \subset \mathbb{R}$  and the subspace  $L^2(X) \subset L^2(\mathbb{R})$  of functions that essentially vanish outside X (e.g., one can take  $X = [0, +\infty)$ ).

**Example 1.10.** Here is the most basic example of an irreducible infinite-dimensional representation of a Lie group. Let G be the **Heisenberg** group, i.e., the group of upper triangular unipotent real 3-by-3 matrices. It can be realized as the Euclidean space  $\mathbb{R}^3$  (with coordinates x, y, z being the above-diagonal matrix entries), with multiplication law

$$(a,b,c)(a',b',c') = (a+a',b+b',c+c'+ab').$$

Then we can define a unitary representation of G on  $V = L^2(\mathbb{R})$  by setting  $\pi(a,0,0) = e^{iax}$  (multiplication operator) and  $\pi(0,b,0) = T_b$  (shift by b).

**Exercise 1.11.** (i) Show that this gives rise to a well defined unitary representation of G, and compute  $\pi(a, b, c)$  for general (a, b, c).

(ii) Show that V is irreducible.

Hint. Suppose  $W \subset V$  is a proper subrepresentation, and denote by  $P: V \to V$  the orthogonal projector to W. We can write P as an integral operator with Schwartz kernel<sup>7</sup> K(x,y), a distribution on  $\mathbb{R}^2$ . Show that K is translation invariant, i.e., K(x+a,y+a)=K(x,y), and deduce K(x,y)=k(x-y) for some distribution k(x) on  $\mathbb{R}^8$ . Show that  $(e^{iax}-1)k(x)=0$  for all  $a\in\mathbb{R}$ . Deduce that P is a scalar operator. Conclude that P=0, so W=0.

$$(T_{\phi}f)(x) = \int_{\mathbb{R}} \phi(y,x)f(y)dy.$$

Then the Schwartz kernel K of a continuous endomorphism A of  $L^2(\mathbb{R})$  is defined by the formula  $(K, \phi) = \text{Tr}(AT_{\phi})$  (which is well defined since the operator  $AT_{\phi}$  is trace class).

<sup>&</sup>lt;sup>7</sup>Recall that every smooth function  $\phi(x,y)$  on  $\mathbb{R}^2$  with compact support defines a trace class operator  $T_{\phi}$  with kernel  $\phi(y,x)$ , i.e.,

<sup>&</sup>lt;sup>8</sup>This means that  $(K, \phi) = (k, \widetilde{\phi})$ , where  $\widetilde{\phi}(x) := \int_{\mathbb{R}} \phi(x + y, y) dy$ .

#### 2. K-finite vectors and matrix coefficients

2.1. K-finite vectors. Let K be a compact topological group. In this case K has a unique right-invariant Haar measure of volume 1, which is therefore also left-invariant; we will denote this measure by dg. Thus if V is a finite-dimensional (continuous) representation of K and B a positive definite Hermitian form on V then the form

$$\overline{B}(v,w) := \int_K B(gv, gw) dg$$

is positive definite and K-invariant, which implies that V is unitary. If V is irreducible then by Schur's lemma this unitary structure is unique up to scaling.

This implies that finite-dimensional representations of K are completely reducible: if  $W \subset V$  is a subrepresentation then  $V = W \oplus W^{\perp}$ , where  $W^{\perp}$  is the orthogonal complement of W under the Hermitian form

Now let V be any continuous representation of K (not necessarily finite-dimensional).

**Definition 2.1.** A vector  $v \in V$  is K-finite if it is contained in a finite-dimensional subrepresentation of V. The space of K-finite vectors of V is denoted by  $V^{\text{fin}}$ .

Let IrrK be the set of isomorphism classes of irreducible finite-dimensional representations of K. We have a natural K-invariant linear map

$$\xi: \bigoplus_{\rho \in \operatorname{Irr} K} \operatorname{Hom}(\rho, V) \otimes \rho \to V^{\operatorname{fin}}$$

(where K acts trivially on  $\text{Hom}(\rho, V)$ ) defined by

$$\xi(h\otimes u)=h(u).$$

Lemma 2.2.  $\xi$  is an isomorphism.

*Proof.* To show  $\xi$  is injective, assume the contrary, and let  $\widetilde{\rho}$  be an irreducible subrepresentation of Ker $\xi$ . Then  $\widetilde{\rho} = h \otimes \rho$  for a suitable  $h \in \text{Hom}(\rho, V)$ , so for any  $u \in \rho$  we have  $h(u) = \xi(h \otimes u) = 0$ . Thus h = 0, a contradiction.

It remains to show that  $\xi$  is surjective. For  $v \in V^{\text{fin}}$ , let  $W \subset V^{\text{fin}}$  be a finite-dimensional subrepresentation of V containing v. By complete reducibility, W is a direct sum of irreducible representations. Thus it suffices to assume that W is irreducible. Let  $h: W \hookrightarrow V$  be the corresponding inclusion. Then  $v = h(v) = \xi(h \otimes v)$ .

**Example 2.3.** Let  $K = S^1 = \mathbb{R}/2\pi\mathbb{Z}$ . The irreducible finite-dimensional representations of K are the characters  $\rho_n(x) = e^{inx}$  for integer n. Let

 $V = L^2(S^1)$ . Then  $\operatorname{Hom}(\rho_n, V)$  is the space of functions on  $S^1$  such that  $f(x+a) = e^{ina}f(x)$ , which is a 1-dimensional space spanned by the function  $e^{inx}$ . It follows that  $V^{\text{fin}}$  is the space of trigonometric polynomials  $\sum_n a_n e^{inx}$ , where only finitely many coefficients  $a_n \in \mathbb{C}$  are nonzero.

2.2. Matrix coefficients. Let us now consider the special case  $V = L^2(K)$ , and view it as a representation of  $K \times K$  via

$$(\pi(a,b)f)(x) = f(a^{-1}xb).$$

For every irreducible representation  $\rho \in \operatorname{Irr} K$  we have a homomorphism of representations of  $K \times K$ :

$$\xi_{\rho}: \operatorname{End}_{\mathbb{C}}\rho = \rho^* \otimes \rho \to L^2(K)$$

defined by

$$\xi_{\rho}(h \otimes v)(g) := h(gv).$$

This map is nonzero, hence injective (as  $\rho^* \otimes \rho$  is an irreducible  $K \times K$ module), and is called **the matrix coefficient map**, as the right hand
side is a matrix coefficient of the representation  $\rho$ . The **theorem on orthogonality of matrix coefficients** tells us that the images of  $\xi_{\rho}$ for different  $\rho$  are orthogonal, and for  $A, B \in \operatorname{End}_{\mathbb{C}} \rho$  we have

$$(\xi_{\rho}(A), \xi_{\rho}(B)) = \frac{\operatorname{Tr}(AB^{\dagger})}{\dim \rho},$$

where  $B^{\dagger}$  is the Hermitian adjoint of B with respect to the unitary structure on  $\rho$ . Thus, choosing orthonormal bases  $\{v_{\rho i}\}$  in each  $\rho$ , we find that the functions

$$\psi_{\rho ij} := (\dim \rho)^{\frac{1}{2}} \xi_{\rho}(E_{ij}),$$

where  $E_{ij} := v_{\rho j}^* \otimes v_{\rho i}$  are elementary matrices, form an orthonormal system in  $L^2(K)$ .

Let us view  $L^2(K)$  as a representation of K via left translations. Let  $\rho \in \operatorname{Irr} K$ . Then every  $h \in \rho$  defines a homomorphism of representations  $f_h : \rho^* \to L^2(K)$  which, when viewed as an element of  $L^2(K,\rho)$ , is given by the formula  $f_h(y) := yh$ . Conversely, suppose  $f : \rho \to V$  is a homomorphism. Then f can be represented by an  $L^2$ -function  $\widetilde{f} : K \to \rho$  such that for any  $b \in K$ , the function  $x \mapsto \widetilde{f}(bx) - b\widetilde{f}(x)$  vanishes outside a set  $S_b \subset K$  of measure 0. Let  $S \subset K \times K$  be the set of pairs (b,x) such that  $x \in S_b$ . Then S has measure 0, hence the set  $T_x$  of  $b \in K$  such that  $(b,x) \in S$  (i.e.,  $x \in S_b$ ) has measure zero almost everywhere with respect to x. So pick  $x \in K$  such that  $T_x$  has measure zero. For  $y = bx \notin T_x x$ , we have  $x \notin S_b$ , so  $\widetilde{f}(y) = yx^{-1}\widetilde{f}(x)$ . Thus

 $f = f_h$  where  $h = x^{-1}\widetilde{f}(x)$ . It follows that the assignment  $h \mapsto f_h$  is an isomorphism  $\rho \cong \operatorname{Hom}(\rho^*, L^2(K))$ . This shows that the map

$$\bigoplus_{\rho \in \operatorname{Irr} K} \xi_{\rho} : \bigoplus_{\rho \in \operatorname{Irr} K} \rho^* \otimes \rho \to L^2(K)^{\operatorname{fin}}$$

is an isomorphism, where  $L^2(K)^{\text{fin}}$  is the space of K-finite vectors in  $L^2(K)$  under left translations. Thus any K-finite function under left (or right) translations is actually  $K \times K$ -finite, and we have a natural orthogonal decomposition

$$L^2(K)^{\text{fin}} \cong \bigoplus_{\rho \in \text{Irr}K} \rho^* \otimes \rho.$$

Moreover, since  $L^2(K)$  is separable, it follows that IrrK is a countable set.

2.3. **The Peter-Weyl theorem.** The following non-trivial theorem is proved in the basic Lie groups course.

**Theorem 2.4.** (Peter-Weyl)  $L^2(K)^{fin}$  is a dense subspace of  $L^2(K)$ . Hence  $\{\psi_{\rho ij}\}$  form an orthonormal basis of  $L^2(K)$ , and we have

$$L^2(K) = \widehat{\bigoplus}_{\rho \in \operatorname{Irr} K} \rho^* \otimes \rho.$$

(completed orthogonal direct sum under the Hilbert space norm).

**Example 2.5.** For  $K = S^1 = \mathbb{R}/2\pi\mathbb{Z}$  the Peter-Weyl theorem says that the Fourier system  $\{e^{inx}\}$  is complete, i.e., a basis of  $L^2(S^1)$ .

2.4. **Partitions of unity.** Let X be a metric space with distance function d, and  $C \subset X$  a closed subset. For  $x \in X$  define

$$d(x,C) := \inf_{y \in C} d(x,y)$$

if  $C \neq \emptyset$ . This function is continuous, since  $d(x,C) \leq d(x,y) + d(y,C)$ , hence  $|d(x,C) - d(y,C)| \leq d(x,y)$ . Thus the function  $f_C(x) := \frac{d(x,C)}{1+d(x,C)}$  (defined to be 1 if  $C = \emptyset$ ) is continuous on X, takes values in [0,1], and  $f_C(x) = 0$  iff  $x \in C$ . So if  $\{U_i, i \in \mathbb{N}\}$  is a countable open cover of X then the function  $\sum_{i \in \mathbb{N}} 2^{-i} f_{U_i^c}$  is continuous and strictly positive, so we may define the continuous functions on X

$$\phi_i := \frac{2^{-i} f_{U_i^c}}{\sum_{i \in \mathbb{N}} 2^{-i} f_{U_i^c}}, i \in \mathbb{N}$$

These functions form a **partition of unity subordinate to the cover**  $\{U_i, i \in \mathbb{N}\}$ : each  $\phi_i$  is non-negative, vanishes outside  $U_i$ , and  $\sum_{i \in \mathbb{N}} \phi_i = 1$  (a uniformly convergent series on X).

#### 3. Algebras of measures on locally compact groups

3.1. The space of measures. Let X be a locally compact second countable Hausdorff topological space. It is well known that such a space is metrizable, so let us fix a metric d defining the topology on X.

As we have seen in Example 1.1, the space C(X) of continuous functions on X is a separable Fréchet space. So let us consider the topological dual space,  $C(X)^*$ , of continuous linear functionals on C(X). This space is denoted by  $\operatorname{Meas}_c(X)$ ; its elements are called (complex-valued) **compactly supported (Radon) measures on** X. We will often use the standard notation from measure theory: for  $f \in C(X)$  and  $\mu \in \operatorname{Meas}_c(X)$ ,

$$\mu(f) = \int_X f(x)d\mu(x).$$

We equip  $\operatorname{Meas}_c(X)$  with the **weak topology**,<sup>9</sup> in which  $\mu_n \to \mu$  iff  $\mu_n(f) \to \mu(f)$  for any  $f \in C(X)$  (this topology is commonly called the weak\* topology, but we will drop the \*). Namely, the weak topology is defined by the family of seminorms  $\mu \mapsto |\mu(f)|$ ,  $f \in C(X)$ , so  $\operatorname{Meas}_c(X)$  is Hausdorff and locally convex. We will also see that  $\operatorname{Meas}_c(X)$  is separable and sequentially complete, but, as shown by the example below, in general it is **not** first countable (so in particular not second countable or metrizable), nor complete, so it is not a Fréchet space.

**Example 3.1.** Let  $X = \mathbb{N}$  with discrete topology. Then C(X) is the space of complex sequences  $\mathbf{a} = \{a_n, n \in \mathbb{N}\}$  with topology defined by the seminorms  $\nu_n(\mathbf{a}) := |a_n|, n \in \mathbb{N}$  (i.e., topology of termwise convergence). So  $C(X)^* = \operatorname{Meas}_c(X)$  is the space of eventually vanishing complex sequences  $\mathbf{f} = \{f_n, n \in \mathbb{N}\}$  (acting on C(X) by  $\mathbf{f}(\mathbf{a}) = \sum_{n \in \mathbb{N}} f_n a_n$ ) with topology having base of neighborhoods of zero consisting of finite intersections of the sets  $U_{\mathbf{a},\varepsilon} = \{\mathbf{f} \in C(X)^* : |\mathbf{f}(\mathbf{a})| < \varepsilon\}$ ,  $\mathbf{a} \in C(X)$ ,  $\varepsilon > 0$ . This space has a basis  $\{\mathbf{e}_m, m \geq 0\}$  given by  $(\mathbf{e}_m)_n := \delta_{mn}$ , i.e., it is countable-dimensional.

We have  $\mathbf{f}_n \to 0$  in  $C(X)^*$  iff all  $\mathbf{f}_n$  are supported on some finite set  $S \subset \mathbb{N}$  and for all  $j \in S$ ,  $f_{nj} \to 0$ . This implies that  $C(X)^*$  is not first countable (hence all the more not second countable and not metrizable). Indeed if  $W_m, m \geq 1$  were a basis of neighborhoods of zero then by replacing  $W_m$  by  $W_1 \cap ... \cap W_m$  we can ensure that  $W_1 \supset W_2 \supset ...$  Assuming this is the case, pick  $N_m \geq 1$  such that the sequence  $\mathbf{a}_m := \frac{\mathbf{e}_m}{N_m}$  belongs to  $W_m$  (it exists since for each  $m, \frac{\mathbf{e}_m}{N} \to 0$  in

<sup>&</sup>lt;sup>9</sup>If X is compact then C(X) is a Banach space and thus so is  $\operatorname{Meas}_c(X)$ , in the corresponding norm topology. However, this norm topology is stronger than the weak topology and is not relevant here.

 $C(X)^*$  as  $N \to \infty$ ). Then the sequence  $\{\mathbf{a}_m, m \ge 1\}$  does not converge to 0, and yet for each  $m, \mathbf{a}_j \in W_m$  for all  $j \ge m$ , contradiction.

Also  $C(X)^*$  is not complete, as it is a dense subspace of the space  $C(X)^*_{alg}$  of all (not necessarily continuous) linear functionals on C(X) (uncountable-dimensional, hence bigger than  $C(X)^*$ ), from which it inherits the weak topology. On the other hand, it is sequentially complete. Indeed, if  $\{\mathbf{f}_n\}$  is a Cauchy sequence in  $\mathbb{C}(X)^*$  then  $\mathbf{f}_n - \mathbf{f}_{n+1}$  goes to 0 as  $n \to \infty$ , so for some N and  $n \ge N$ ,  $\mathbf{f}_n - \mathbf{f}_{n+1}$  is supported on some finite set  $S \subset \mathbb{N}$ . Hence for all n,  $\mathbf{f}_n$  is supported on the union of S and the supports of  $\mathbf{f}_i$ ,  $1 \le i \le N$ , which is a finite set. Hence it converges (as it is Cauchy). Also, the countable set  $C(X)^*_{rat}$  of eventually vanishing sequences of Gaussian rationals is dense in  $C(X)^*$ , so  $C(X)^*$  is separable.

Thus we see that  $C(X)^* = \bigcup_{i \geq 1} C(K_i)^*$  as a vector space, or, without making any choices,  $C(X)^* = \varinjlim_{K \subset X} C(K)^*$ , where K runs over compact subsets of X.

Pick a representation of X as a nested union of compact subsets  $K_i, i \geq 1$ . We claim that for any  $\mu \in C(X)^*$  there exists i such that if  $f \in C(X)$  satisfies  $f|_{K_i} = 0$  then  $\mu(f) = 0$ . Indeed, if not then for each i there is  $f_i \in C(X)$  with  $f_i|_{K_i} = 0$  but  $\mu(f_i) = 1$ . Then the series  $\sum_i f_i$  converges in C(X) (as it terminates on each  $K_i$ , and every compact subset of X is contained in some  $K_i$ ) while the series  $\mu(\sum_i f_i) = \sum_i \mu(f_i) = \sum_i 1$  diverges, a contradiction. Thus we see that  $C(X)^* = \bigcup_{i \geq 1} C(K_i)^*$  as a vector space, or, without making any choices,  $C(X)^* = \varinjlim_{K \subset X} C(K)^*$ , where K runs over compact subsets of X.

**Lemma 3.2.** (i) If a sequence  $\{\mu_n, n \geq 1\} \in C(X)^*$  is Cauchy then there is a compact subset  $K \subset X$  such that  $\mu_n \in C(K)^* \subset C(X)^*$  for all n

(ii)  $C(X)^*$  is sequentially complete.

Proof. (i) Otherwise for each  $j \geq 1$  there exists the largest positive integer  $N_j \geq 0$  such that if  $f \in C(X)$  and  $f|_{K_j} = 0$  then  $\mu_1(f) = \ldots = \mu_{N_j-1}(f) = 0$ . The numbers  $N_j$  form a nondecreasing sequence, and since  $C(X)^* = \bigcup_{i \geq 1} C(K_i)^*$ , we have  $N_j \to \infty$ . So let  $p(j) \geq j$  be the largest i for which  $N_i = N_j$ . By assumption, for every  $j \geq 1$  there is  $f_j \in C(X)$  with  $f_i|_{K_j} = 0$  and  $\mu_{N_j}(f_j) \neq 0$ . Then we can arrange that  $\mu_{N_j}(f_1 + \ldots + f_j) = j$ , and  $\mu_{N_j}(f_i) = 0$  if i > p(j). Now, the series  $f := \sum_{i \geq 1} f_i$  converges in C(X), and we have

$$\mu_{N_j}(f) = \mu_{N_j}(f_1 + \dots + f_{p(j)}) = \mu_{N_{p(j)}}(f_1 + \dots + f_{p(j)}) = p(j).$$

On the other hand, since  $\mu_n$  is Cauchy, we get

$$p(j+1) - p(j) = \mu_{N_{j+1}}(f) - \mu_{N_j}(f) \to 0, \ j \to \infty,$$

a contradiction since  $p(j) \geq j$ .

- (ii) Let  $\{\mu_n, n \geq 1\}$  be a Cauchy sequence in  $C(X)^*$ . By (i),  $\mu_n \in C(K)^*$  for some compact  $K \subset X$ , so we may assume that X is compact. Since  $\mu_n$  is Cauchy, so is  $\mu_n(f)$  for any  $f \in C(X)$ . Thus  $\mu_n$  weakly converges to some linear functional  $\mu: C(X) \to \mathbb{C}$  given by  $\mu(f) := \lim_{n \to \infty} \mu_n(f)$ , and our job is to show, that  $\mu$  is continuous. Since  $\mu_n(f)$  is convergent, it is bounded, so by the uniform boundedness principle, the sequence  $\|\mu_n\|$  is bounded above by some constant C, i.e.,  $|\mu_n(f)| \leq C \|f\|$ . But then  $|\mu(f)| \leq C \|f\|$ , so  $\|\mu\| \leq C$ , as desired
- 3.2. Support of a measure. Define the support of  $\mu \in C(X)^*$ , denoted  $\operatorname{supp}\mu$ , to be the set of all  $x \in X$  such that for any neighborhood U of x in X there exists  $f \in C(X)$  vanishing outside U with  $\mu(f) \neq 0$ . Thus the complement  $(\operatorname{supp}\mu)^c$  is the set of  $x \in X$  which admit a neighborhood U such that for every  $f \in C(X)$  vanishing outside U we have  $\mu(f) = 0$ . In this case,  $U \subset (\operatorname{supp}\mu)^c$ , so  $(\operatorname{supp}\mu)^c$  is open, hence  $\operatorname{supp}\mu$  is closed. Moreover, since  $C(X)^* = \varinjlim_{K \subset X} C(K)^*$ ,  $\operatorname{supp}\mu$  is contained in some compact subset  $K \subset X$ , so it is itself compact.

**Proposition 3.3.** If 
$$f \in C(X)$$
 and  $f|_{\text{supp}\mu} = 0$  then  $\mu(f) = 0$ .

Proof. For every  $z \in (\operatorname{supp}\mu)^c$  there is a neighborhood  $U_z \subset (\operatorname{supp}\mu)^c$  such that for any  $\phi \in C(X)$  vanishing outside  $U_z$ ,  $\mu(\phi) = 0$ . These neighborhoods form an open cover of  $(\operatorname{supp}\mu)^c$ . Since  $(\operatorname{supp}\mu)^c$  is second countable, this cover has a countable subcover  $\{U_i, i \in \mathbb{N}\}$ . Let  $\{\phi_i, i \in \mathbb{N}\}$  be a continuous partition of unity subordinate to this cover. Then  $\mu(\phi_i f) = 0$  for all i, so  $\mu(f) = \mu(\sum_i \phi_i f) = \sum_i \mu(\phi_i f) = 0$ , as claimed.

- 3.3. Finitely supported measures. A basic example of an element of  $\operatorname{Meas}_c(X)$  is a Dirac measure  $\delta_a$ ,  $a \in X$ , such that  $\delta_a(f) = f(a)$ . Thus if  $a_n \to a$  in X as  $n \to \infty$  then  $\delta_{a_n} \to \delta_a$  in the weak topology. A finite linear combination of Dirac measures is called a **finitely supported** measure, since such measures are exactly the measures with finite support. The subspace of finitely supported measures is denoted  $\operatorname{Meas}_c^0(X)$ .
- **Lemma 3.4.**  $\operatorname{Meas}_c^0(X)$  is a sequentially dense (in particular, dense) subspace in  $\operatorname{Meas}_c(X)$ , i.e., every element  $\mu \in \operatorname{Meas}_c(X)$  is the limit of a sequence  $\mu_n \in \operatorname{Meas}_c^0(X)$  in the weak topology.

*Proof.* By replacing X with supp $\mu$ , we may assume that X is compact. For every  $n \geq 1$ , let  $X_n$  be a finite subset of X such that the open balls  $B(x,\frac{1}{n})$  around  $x \in X_n$  cover X. Let  $\{\phi_{nx}, x \in X_n\}$  be a continuous partition of unity subordinate to this cover, and let

$$\mu_n := \sum_{x \in X_n} \mu(\phi_{nx}) \delta_x \in \operatorname{Meas}_c^0(X).$$

We claim that  $\mu_n \to \mu$  in the weak topology. Indeed, let  $f \in C(X)$ . Then

$$|\mu_n(f) - \mu(f)| = |\mu(\sum_{x \in X_n} \phi_{nx}(f - f(x))| \le ||\mu|| \sup_{y \in X} \sum_{x \in X_n} \phi_{nx}(y)|f(y) - f(x)|.$$

But f is uniformly continuous, so for every  $\varepsilon > 0$  there is N such that if  $d(x,y) < \frac{1}{N}$  then  $|f(x) - f(y)| < \varepsilon$ . So for  $n \ge N$ , whenever  $\phi_{nx}(y) \ne 0$ , we have  $|f(y) - f(x)| < \varepsilon$ . Thus we get

$$|\mu_n(f) - \mu(f)| \le \varepsilon \|\mu\| \sup_{y \in X} \sum_{x \in X_n} \phi_{nx}(y) = \varepsilon \|\mu\|,$$

which implies the desired statement.

Note that since X is separable, so is  $\operatorname{Meas}_{c}^{0}(X)$  (given a countable dense subset  $T \subset X$ , finitely supported measures with support in T and Gaussian rational coefficients form a countable, sequentially dense subset  $E_T \subset \operatorname{Meas}_c^0(X)$ . Thus we get that  $\operatorname{Meas}_c(X)$  is separable; moreover, since  $E_T$  is sequentially dense in  $\operatorname{Meas}_c(X)$ , the latter is sequentially separable.

Corollary 3.5. If X, Y are locally compact second countable Hausdorff spaces then the natural bilinear map

$$\boxtimes : \operatorname{Meas}_{c}^{0}(X) \times \operatorname{Meas}_{c}^{0}(Y) \to \operatorname{Meas}_{c}(X \times Y)$$

uniquely extends to a bilinear map

$$\boxtimes : \operatorname{Meas}_c(X) \times \operatorname{Meas}_c(Y) \to \operatorname{Meas}_c(X \times Y)$$

which is continuous in each variable.

*Proof.* It is clear that  $\boxtimes$  is continuous in each variable, so the result follows from the facts that  $\operatorname{Meas}_c^0(X)$  is sequentially dense in  $\operatorname{Meas}_c(X)$ and that  $\operatorname{Meas}_{c}(X)$  is sequentially complete.

**Remark 3.6.** Here is another proof of Corollary 3.5. We may assume that X, Y are compact. Given  $\mu \in C(X)^*, \nu \in C(Y)^*$ , define a linear functional  $\mu \boxtimes \nu$  on  $C(X) \otimes C(Y) \subset C(X \times Y)$  by

$$(\mu \boxtimes \nu)(f \otimes g) := \mu(f)\nu(g).$$

We claim that  $\|\mu \boxtimes \nu\| \leq \|\mu\| \|\nu\|$  (in fact, the opposite inequality is obvious, so we have an equality). Thus our job is to show that for  $f_i \in C(X), g_i \in C(Y), 1 \leq i \leq n$ , we have

$$|\sum_{i} \mu(f_i)\nu(g_i)| \le ||\mu|| ||\nu|| \max_{x \in X, y \in Y} |\sum_{i} f_i(x)g_i(y)|$$

i.e., that

$$|\nu(\sum_{i} \mu(f_i)g_i)| \le \|\mu\| \|\nu\| \max_{x \in X, y \in Y} |\sum_{i} f_i(x)g_i(y)|.$$

To this end, it suffices to show that

$$\max_{y \in Y} |\sum_{i} \mu(f_i) g_i(y)| \le \|\mu\| \max_{x \in X, y \in Y} |\sum_{i} f_i(x) g_i(y)|,$$

which would follow from the inequality

$$|\sum_{i} \mu(f_i)g_i(y)| \le ||\mu|| \max_{x \in X} |\sum_{i} f_i(x)g_i(y)|.$$

for all  $y \in Y$ . But this is just the inequality  $|\mu(F_y)| \leq ||\mu|| \max_{x \in X} |F_y(x)|$  applied to  $F_y(x) := \sum_i g_i(y) f_i(x)$ .

Now note that by the Stone-Weierstrass theorem,  $C(X) \otimes C(Y)$  is dense in  $C(X \times Y)$ , so  $\mu \boxtimes \nu$  extends continuously to  $C(X \times Y)$ .

3.4. The algebra of measures on a locally compact group. Now let G be a locally compact group. In this case  $\operatorname{Meas}_c^0(G) = \mathbb{C}G$  is the group algebra of G as an abstract group. Namely, the algebra structure is given by  $\delta_x \delta_y = \delta_{xy}$ . This multiplication is continuous in the weak topology, hence uniquely extends to  $\operatorname{Meas}_c(G)$ , since the latter is sequentially complete and  $\operatorname{Meas}_c^0(G)$  is sequentially dense in  $\operatorname{Meas}_c(G)$ . Thus  $\operatorname{Meas}_c(G)$  is a topological unital associative algebra with unit  $\delta_1$ . The multiplication in this algebra may be written as

$$(\mu_1 * \mu_2)(f) = (\mu_1 \boxtimes \mu_2, \Delta(f)) = \int_{G \times G} f(xy) d\mu_1(x) d\mu_2(y),$$

where  $\Delta: C(G) \to C(G \times G)$  is given by  $\Delta(f)(x,y) := f(xy)$ . This multiplication is called the **convolution product**.

Moreover, if dg is a right-invariant Haar measure on G then any compactly supported continuous function (or, more generally,  $L^1$ -function)  $\phi$  on G gives rise to a measure  $\mu = \phi dg \in \text{Meas}_c(G)$ . For such measures  $\mu_1 = \phi_1 dg$ ,  $\mu_2 = \phi_2 dg$  we have

$$(\mu_1 * \mu_2)(f) = \int_{G \times G} f(xy)\phi_1(x)\phi_2(y)dxdy = \int_{G \times G} f(z)\phi_1(zy^{-1})\phi_2(y)dzdy.$$

Thus  $\mu_1 * \mu_2 = \phi dg$  where

$$\phi(z) = \int_G \phi_1(zy^{-1})\phi_2(y)dy.$$

This is called the **convolution of functions**.

Now let V be a continuous representation of G with the associated homomorphism  $\pi: G \to \operatorname{Aut}(V)$ . This map  $\pi$  extends by linearity to a homomorphism  $\pi: \mathbb{C}G = \operatorname{Meas}^0_c(G) \to \operatorname{End}(V)$ .

Let us equip  $\mathbb{C}G$  with weak topology and introduce the corresponding product topology on  $\mathbb{C}G \times V$ .

**Lemma 3.7.** The map  $\mathbb{C}G \times V \to V$  given by  $g \mapsto \pi(g)v$  is continuous. Thus  $\pi$  is continuous in the weak topology of  $\mathbb{C}G$  and strong topology of  $\mathrm{End}(V)$ .

*Proof.* We need to show that for any seminorm  $\lambda$  (from the family defining the topology of V) there exists a neighborhood U of 0 in the space  $\mathbb{C}G \times V$  such that for  $(\mu, v) \in U$  we have  $\lambda(\pi(\mu)v) < 1$ . Let  $\mu = \sum_{i=1}^{n} c_i \delta_{x_i}$ , then this inequality takes the form

(1) 
$$\sum_{i=1}^{n} \lambda(c_i \pi(x_i) v) < 1.$$

Since  $\lambda$  is a seminorm, (1) would follow from the inequality

(2) 
$$\sum_{i=1}^{n} |c_i| \lambda(\pi(x_i)v) < 1.$$

We define  $|\mu| = \sum_{i=1}^{n} |c_i| \delta_{x_i}$  and  $f_v(x) := \lambda(\pi(x)v), f_v \in C(X)$ . Then (2) takes the form

$$(3) |\mu|(f_v) < 1.$$

Clearly, the map  $(\mu, v) \mapsto |\mu|(f_v)$  is continuous, so we may take U to be defined by (3).

Corollary 3.8. If  $(V, \pi)$  is a continuous representation of G then  $\pi$  the action  $G \times V \to V$  uniquely extends to a continuous bilinear map  $\operatorname{Meas}_c(G) \times V \to V$ , which gives rise to a continuous unital algebra homomorphism

$$\pi: \operatorname{Meas}_c(G) \to \operatorname{End}(V).$$

*Proof.* We need to show that for every  $v \in V$  the map  $\mu \mapsto \pi(\mu)v$  uniquely extends by continuity from  $\operatorname{Meas}_c^0(G)$  to  $\operatorname{Meas}_c(G)$ . This follows from Lemmas 3.4 and 3.7 since V is complete.

#### 4. Plancherel formulas, Dirac sequences, smooth vectors

4.1. **Plancherel formulas.** For a compactly supported  $L^1$ -function f on G, for brevity let us denote  $\pi(fdg)$  just by  $\pi(f)$ .

**Proposition 4.1.** (Plancherel's theorem for compact groups) Let K be a compact group and  $f_1, f_2 \in L^2(K)$ . Then

$$(f_1, f_2) = \sum_{\rho \in \operatorname{Irr} K} \dim \rho \cdot \operatorname{Tr}(\pi_{\rho}(f_1) \pi_{\rho}(f_2)^{\dagger})$$

and this series is absolutely convergent.

*Proof.* Recall that if  $e_i$  is an orthonormal basis of a Hilbert space H and  $f_1, f_2 \in H$  then

$$(f_1, f_2) = \sum_i (f_1, e_i)(e_i, f_2)$$

and this series is absolutely convergent. The result now follows by applying this formula to the orthonormal basis provided by the Peter-Weyl theorem:

$$\psi_{\rho ij} = \sqrt{\dim \rho} (\pi_{\rho}(g) v_{\rho i}, v_{\rho j}),$$

where  $\{v_{\rho i}\}$  is an orthonormal basis of  $\rho$ .

**Example 4.2.** If  $K = S^1$ , Plancherel's theorem reduces to the usual Parseval equality in Fourier analysis:

$$(f_1, f_2) = \sum_{n \in \mathbb{Z}} c_n(f_1) \overline{c_n(f_2)},$$

where  $c_n(f)$  are the Fourier coefficients of f.

**Proposition 4.3.** (Plancherel's formula) If K is a compact Lie group and  $f \in C^{\infty}(K)$  then

$$f(1) = \sum_{\rho \in \operatorname{Irr} K} \dim \rho \cdot \operatorname{Tr}(\pi_{\rho}(f))$$

and this series is absolutely convergent.

**Example 4.4.** If  $K = S^1$  then this formula says that for  $f \in C^{\infty}(S^1)$ 

$$f(1) = \sum_{n \in \mathbb{Z}} c_n(f),$$

i.e., the Fourier series of f absolutely converges at 1. Note that for  $f \in C(S^1)$  this is false in general!<sup>10</sup>

 $<sup>\</sup>overline{\phantom{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa$ 

*Proof.* Consider the integral operator A of convolution with the function f:

$$(A\psi)(x) = (f * \psi)(x) = \int_K f(xy^{-1})\psi(y)dy.$$

This operator is trace class, since it has smooth integral kernel  $F(x, y) = f(xy^{-1})$ , and

$$Tr(A) = \int_K F(x, x) dx = \int_K f(1) dx = f(1).$$

On the other hand, A is right-invariant, so it preserves the decomposition of  $L^2(K)$  into the direct sum of  $\rho \otimes \rho^*$  and acts on each such summand as  $\pi_{\rho}(f) \otimes 1$ . Thus we also have

$$\operatorname{Tr}(A) = \sum_{\rho \in \operatorname{Irr}K} \dim(\rho) \cdot \operatorname{Tr}(\pi_{\rho}(f)),$$

as desired.  $\Box$ 

4.2. **Dirac sequences.** If G is a locally compact group then multiplication by dg defines an inclusion  $C_c(G) \hookrightarrow \operatorname{Meas}_c(G)$  of compactly supported continuous functions into compactly supported measures as a (non-unital) subalgebra. Moreover, if G is a Lie group then we have a nested sequence of subalgebras  $C_c^k(G)$ ,  $0 \le k \le \infty$  (compactly supported  $C^k$ -functions). The following lemma shows that while these subalgebras are non-unital, they are "almost unital".

**Lemma 4.5.** There exists a sequence  $\phi_n \in C_c(G)$  such that  $\phi_n \to \delta_1$  in the weak topology as  $n \to \infty$ . Moreover, if G is a Lie group, we can choose  $\phi_n \in C_c^{\infty}(G)$ .

*Proof.* (sketch)  $\phi_n$  can be constructed as a sequence of "hat" functions supported on a decreasing sequence of balls  $B_1 \supset B_2 \supset ...$  whose intersection is  $1 \in G$ . Such hat functions can be chosen smooth if G is a Lie group.

Such sequences  $\phi_n$  are called **Dirac sequences**.

Corollary 4.6.  $C_c(G)$  is sequentially dense in  $\operatorname{Meas}_c(G)$ . For Lie groups,  $C_c^{\infty}(G)$  is sequentially dense in  $\operatorname{Meas}_c(G)$ .

*Proof.* By translating a Dirac sequence, for any  $g \in G$  we can construct a sequence  $\psi_n \to \delta_g$ . This implies that  $\operatorname{Meas}_c^0(G)$  is contained in the sequential closure of  $C_c(G)$  (and of  $C_c^{\infty}(G)$  in the Lie case). So the result follows from Lemma 3.4.

#### 4.3. Density of K-finite vectors.

**Corollary 4.7.** Let V be a continuous representation of a compact group K. Then  $V^{\text{fin}}$  is dense in V.

*Proof.* Let  $v \in V$ , and  $\phi_n \to \delta_1$  a continuous Dirac sequence, which exists by Lemma 4.5. Then  $\pi(\phi_n)v \to v$  as  $n \to \infty$ . But  $\phi_n \in L^2(K)$ , so by the Peter-Weyl theorem, there exists  $\psi_n \in L^2(K)^{\text{fin}} = \bigoplus_{\rho} \rho^* \otimes \rho$  such that

$$\left\|\psi_n - \phi_n\right\|_2 < \frac{1}{n}.$$

Then  $\psi_n - \phi_n \to 0$  in  $L^2(K)$ , hence in  $\operatorname{Meas}_c(K)$ . So by Corollary 3.8,  $\pi(\psi_n - \phi_n)v \to 0$  as  $n \to \infty$ . It follows that  $\pi(\psi_n)v \to v$  as  $n \to \infty$ . But  $\pi(\psi_n)v \in V^{\text{fin}}$ .

**Corollary 4.8.**  $L^2(K)^{\text{fin}} \subset C(K)$  is a dense subspace. Moreover, if K is a Lie group then  $L^2(K)^{\text{fin}} \subset C^k(K)$  is a dense subspace for  $0 \le k \le \infty$ .

*Proof.* The claimed inclusions follow since matrix coefficients of finite-dimensional representations of K are continuous, and moreover  $C^{\infty}$  in the case of Lie groups. The density then follows from Corollary 4.7.  $\square$ 

Corollary 4.9. If V is an irreducible continuous representation of K then V is finite-dimensional.

*Proof.* By Corollary 4.7,  $V^{\text{fin}}$  is dense in V. Hence  $V^{\text{fin}} \neq 0$ . Let  $\rho$  be a finite-dimensional subrepresentation of  $V^{\text{fin}}$ . Then  $\rho$  is a closed invariant subspace of V. Hence  $\rho = V$ .

4.4. **Smooth vectors.** Let G be a Lie group. As we have noted in Subsection 1.2, any continuous *finite-dimensional* representation  $\pi$ :  $G \to \operatorname{Aut}(V)$  is automatically smooth and thereby defines a representation  $\pi_*: \mathfrak{g} \to \operatorname{End}(V)$  of the corresponding Lie algebra, which determines  $\pi$  if G is connected. Moreover, if G is simply connected, this correspondence is an equivalence of categories. This immediately reduces the problem to pure algebra and is the main tool of studying finite-dimensional representations of Lie groups.

We would like to have a similar theory for infinite-dimensional representations. But in the infinite-dimensional setting the above statements don't hold in the literal sense.

**Example 4.10.** Consider the action of  $S^1$  on  $L^2(S^1)$ . Then the Lie algebra should act by  $\frac{d}{d\theta}$ . But this operator does not act on  $L^2(S^1)$ . The largest subspace of  $L^2(S^1)$  preserved by this operator (acting on distributions on  $S^1$ ) is  $C^{\infty}(S^1)$ .

This motivates the notion of a **smooth vector** in a continuous representation of a Lie group. To define this notion, for a manifold X and a topological vector space V, denote by  $C^{\infty}(X,V)$  the space of smooth maps  $X \to V$  (where smooth maps are defined in the same way as in the case of finite-dimensional V).

**Definition 4.11.** Let  $(V, \pi)$  be a continuous representation of a Lie group G. A vector  $v \in V$  is called **smooth** if the map  $G \to V$  given by  $g \mapsto \pi(g)v$  is smooth, i.e., belongs to  $C^{\infty}(G, V)$ . The space of smooth vectors is denoted by  $V^{\infty}$ .

It is clear that  $V^{\infty} \subset V$  is a G-invariant subspace (although not a closed one).

**Example 4.12.** For the representation of a compact Lie group K on  $V = L^2(K)$ , we have  $V^{\infty} = C^{\infty}(K)$ .

**Proposition 4.13.** Let  $(V, \pi)$  be a continuous representation of a Lie group G with  $\mathfrak{g} = \operatorname{Lie}(G)$ . Let  $v \in V^{\infty}$ . Then we have a linear map  $\pi_{*,v} : \mathfrak{g} \to V^{\infty}$  given by

$$\pi_{*,v}(b) = \frac{d}{dt}|_{t=0}\pi(e^{tb})v.$$

This defines a Lie algebra homomorphism  $\pi_* : \mathfrak{g} \to \operatorname{End}_{\mathbb{C}}(V^{\infty})$  (algebra of all linear endomorphisms of  $V^{\infty}$ ) given by  $\pi_*(b)v := \pi_{*,v}(b)$ .

Exercise 4.14. Prove Proposition 4.13.

**Proposition 4.15.** (i)  $V^{\infty}$  is dense in V. (ii)  $V^{\text{fin}} \subset V^{\infty}$ .

*Proof.* (i) Let  $\phi_n \to \delta_1$  be a smooth Dirac sequence. Then  $\pi(\phi_n)v \to v$  as  $n \to \infty$ . But it is easy to see that  $\pi(\phi_n)v \in V^{\infty}$ .

(ii) This follows since matrix coefficients of finite-dimensional representations are smooth.  $\Box$ 

#### 5. Admissible representations and $(\mathfrak{g}, K)$ -modules

5.1. Admissible representations. Now let G be a Lie group and  $K \subset G$  a compact subgroup. For a continuous representation V of G, denote by  $V^{K\text{-fin}}$  the space  $(V|_K)^{\text{fin}}$ . In general  $V^{K\text{-fin}}$  is not contained in  $V^{\infty}$ ; for example, if K=1 then  $V^{K\text{-fin}}=V$ . However, this inclusion holds if K is sufficiently large and V is sufficiently small.

**Definition 5.1.** V is said to be K-admissible (or of finite K-type) if for every finite-dimensional irreducible representation  $\rho$  of K, the space  $\text{Hom}_K(\rho, V)$  is finite-dimensional.

**Example 5.2.** Let G be a connected Lie group and  $V = L^2(G/B)$  where B is a closed subgroup of G (half-densities on G/B). Then V is K-admissible iff K acts transitively on G/B, i.e., KB = G. In this case setting  $T = K \cap B$ , we have G/B = K/T, so  $V = L^2(K/T)$  and  $\operatorname{Hom}_K(\rho, V) \cong (\rho^T)^*$ . 11

**Example 5.3.** For  $G = SL_2(\mathbb{C})$  and K = SU(2), the unitary representation of G on the space  $V = L^2(\mathbb{CP}^1)$  of square-integrable half-densities on  $\mathbb{CP}^1$  is K-admissible. Indeed, taking  $\rho_n$  to be the representation of SU(2) with highest weight n, we have dim  $\text{Hom}(\rho_n, V) = 0$  for odd n and 1 for even n.

More generally, for a real number s we may consider the representation  $V_s$  of square integrable  $\frac{1}{2} + is$ -densities on  $\mathbb{CP}^1$ ; this space is canonically defined since for a  $\frac{1}{2} + is$ -density f, the complex conjugate  $\overline{f}$  is a  $\frac{1}{2} - is$ -density, so  $|f|^2 = f\overline{f}$  is a density and can be integrated canonically over  $\mathbb{CP}^1$ . This representation has the same K-multiplicities as  $V = V_0$ .

Similarly, for  $G = SL_2(\mathbb{R})$ , K = SO(2), we have a unitary K-admissible representation  $V = L^2(\mathbb{RP}^1)$  (half-densities) and more generally  $V_s$  ( $\frac{1}{2} + is$ -densities). For the K-multiplicities we have equalities dim  $\text{Hom}(\chi_n, V_s) = 1$  for odd n and 0 for even n, where  $\chi_n(\theta) = e^{in\theta}$ .

We will see that the representations  $V_s$  in both cases are irreducible and  $V_s, V_t$  are isomorphic iff  $s = \pm t$ . The family of representations  $V_s$  is called the **unitary spherical principal series**.

<sup>&</sup>lt;sup>11</sup>Note that here we don't have to distinguish between half-densities and functions on K/T since K/T always has a K-invariant volume form as K is compact.

Note that this family makes sense also when s is a complex number which is not necessarily real. In this case  $V_s$  is not necessarily unitary but still a continuous representation on square integrable  $\frac{1}{2} + is$ -densities. The space of such densities is canonically defined as a topological vector space, although its Hilbert norm is not canonically defined unless s is real (however, we will see that for some non-real s, corresponding to so-called **complementary series**, this representation is still unitary, even though the inner product is not given by the standard formula). The family  $V_s$  with arbitrary complex s is called the **spherical principal series**.

Explicitly, the action of G on  $V_s$  looks as follows (realizing elements of  $V_s$  as functions on  $\mathbb{R}$  or  $\mathbb{C}$ , removing the point at infinity):

$$\left(\begin{pmatrix} a & b \\ c & d \end{pmatrix}^{-1} f\right)(z) = f\left(\frac{az+b}{cz+d}\right) |cz+d|^{-m(1+2is)},$$

where m=1 in the real case and m=2 in the complex case.

**Proposition 5.4.** If V is K-admissible then  $V^{K$ -fin}  $\subset V^{\infty}$ , and it is a  $\mathfrak{g}$ -submodule (although not in general a G-submodule).

*Proof.* For a finite-dimensional irreducible representation  $\rho$  of K, let  $V^{\rho} := \text{Hom}(\rho, V) \otimes \rho$  be the isotypic component of  $\rho$ .

We claim that for any continuous representation V the space  $V^{\infty} \cap V^{\rho}$  is dense in  $V^{\rho}$ . Indeed, let  $\psi_{\rho} \in L^{2}(K)^{fin}$  be the character of  $\rho$  given by

$$\psi_{\rho} = \sum_{i} \psi_{\rho ii}.$$

Let  $\xi_{\rho}$  be the pushforward of  $\psi_{\rho}dx$  from K to G (a measure on G supported on K). Then  $\pi(\xi_{\rho})$  is the projector to  $V^{\rho}$  annihilating  $\overline{\bigoplus_{\eta\neq\rho}V^{\eta}}$ . Let  $\phi_n\to\delta_1$  be a smooth Dirac sequence on G. Then for  $v\in V^{\rho}$ ,

$$\pi(\xi_{\rho} * \phi_n)v = \pi(\xi_{\rho})\pi(\phi_n)v \to \pi(\xi_{\rho})v = v$$

as  $n \to \infty$ . However,  $\xi_{\rho} * \phi_n$  is smooth, so  $\pi(\xi_{\rho} * \phi_n)v \in V^{\infty} \cap V^{\rho}$ .

Thus if  $V^{\rho}$  is finite-dimensional (which happens for K-admissible V) then  $V^{\infty} \cap V^{\rho} = V^{\rho}$ , so  $V^{\rho} \subset V^{\infty}$ . Hence  $V^{K\text{-fin}} \subset V^{\infty}$ .

Finally, it is clear that for  $b \in \mathfrak{g}$  and  $v \in V^{\rho}$ , the vector bv generates a K-submodule of a multiple of  $\mathfrak{g} \otimes \rho$ , so  $bv \in V^{K\text{-fin}}$ . It follows that  $V^{K\text{-fin}}$  is a  $\mathfrak{g}$ -submodule.

**Example 5.5.** If  $G = SL_2(\mathbb{R})$ , K = SO(2),  $V = V_s = L^2(S^1)$  is a spherical principal series representation, then  $V^{K\text{-fin}}$  is the space of trigonometric polynomials. Note that this space is *not* invariant under

the action of G. However, the Lie algebra  $\mathfrak{g} = \mathfrak{sl}_2(\mathbb{R})$  does act on this space.

**Exercise 5.6.** Compute this Lie algebra action in the basis  $v_n = e^{in\theta}$  and write it as first order differential operators in the angle  $\theta$ . (Pick generators e, h, f in  $\mathfrak{g}_{\mathbb{C}}$  so that h acts diagonally in the basis  $v_i$ ).

5.2.  $(\mathfrak{g}, K)$ -modules. This motivates the following definition. Let K be a compact connected Lie group and  $\mathfrak{k} = \text{Lie}K$ . Let  $\mathfrak{g}$  be a finite-dimensional real Lie algebra containing  $\mathfrak{k}$ , and suppose the adjoint action of  $\mathfrak{k}$  on  $\mathfrak{g}$  integrates to an action of K. In this case we say that  $(\mathfrak{g}, K)$  is a **Harish-Chandra pair**.

**Definition 5.7.** Let  $(\mathfrak{g}, K)$  be a Harish-Chandra pair.

- (i) A  $(\mathfrak{g}, K)$ -module is a vector space M with actions of K and  $\mathfrak{g}$  such that
  - $\bullet$  M is a direct sum of finite-dimensional continuous K-modules;
- the two actions of  $\mathfrak{k}$  on M (coming from the actions of  $\mathfrak{g}$  and K) coincide.
- (ii) Such a module is said to be **admissible** if for every  $\rho \in \operatorname{Irr} K$  we have  $\dim \operatorname{Hom}_K(\rho, M) < \infty$ .
- (iii) An admissible  $(\mathfrak{g}, K)$ -module which is finitely generated over  $U(\mathfrak{g})$  is called a **Harish-Chandra module**.

**Exercise 5.8.** Show that if M is a  $(\mathfrak{g}, K)$ -module then for every  $g \in K$ ,  $a \in \mathfrak{g}$ ,  $v \in M$  we have

$$gav = Ad(g)(a)gv,$$

where Ad denotes the K-action on  $\mathfrak{g}$ .

In fact, a  $(\mathfrak{g}, K)$ -module is a purely algebraic object, since finite-dimensional K-modules can be described as algebraic representations of the complex reductive group  $K_{\mathbb{C}}$ . Moreover, we can represent them even more algebraically in terms of the action of  $\mathfrak{k}$ . Namely, let us say that a finite-dimensional representation of  $\mathfrak{k}$  is **integrable** to K if it corresponds to a representation of K (note that this is automatic if K is simply connected). Then  $(\mathfrak{g}, K)$ -modules are simply  $\mathfrak{g}$ -modules which are locally integrable to K when restricted to  $\mathfrak{k}$  (i.e., sum of integrable modules). So if K is simply connected (in which case  $\mathfrak{k}$  is semisimple) then a  $(\mathfrak{g}, K)$ -module is the same thing as a  $\mathfrak{g}$ -module which is locally finite when restricted to  $\mathfrak{k}$  (i.e., sum of finite-dimensional modules).

Thus  $(\mathfrak{g}, K)$ -modules form an abelian category closed under extensions (and this category can be defined over any algebraically closed field of characteristic zero). The same applies to admissible  $(\mathfrak{g}, K)$ -modules and to Harish-Chandra modules (the latter is closed under

taking kernels of morphisms because the algebra  $U(\mathfrak{g})$  is Noetherian, as so is its associated graded  $S\mathfrak{g}$  by the Hilbert basis theorem).

**Example 5.9.** Let G be a connected complex semisimple Lie group. Then its maximal compact subgroup is the compact form  $K = G_c$ . Thus a  $(\mathfrak{g}, K)$ -module is a  $\mathfrak{g}$ -module M which is locally finite for  $\mathfrak{g}_c \subset \mathfrak{g}$ , where  $\mathfrak{g}_c = \text{Lie}G_c$ . Note that the action of  $\mathfrak{g}$  here is only **real linear**. Thus we may pass to complexifications:  $(\mathfrak{g}_c)_{\mathbb{C}} = \mathfrak{g}$ ,  $\mathfrak{g}_{\mathbb{C}} = \mathfrak{g} \oplus \mathfrak{g}$ , and  $\mathfrak{g}$  sits inside  $\mathfrak{g} \oplus \mathfrak{g}$  as the diagonal. Thus a  $(\mathfrak{g}, K)$ -module is simply a  $\mathfrak{g} \oplus \mathfrak{g}$ -module which is locally finite for the diagonal copy of  $\mathfrak{g}$ . This is the same as a  $\mathfrak{g}$ -bimodule<sup>12</sup> with locally finite adjoint action

$$ad(b)m := [b, m] = bm - mb.$$

For example, if I is any two-sided ideal in  $U(\mathfrak{g})$  then  $U(\mathfrak{g})/I$  is a  $(\mathfrak{g}, K)$ -module.

Thus we obtain the following proposition.

**Proposition 5.10.** If V is a K-admissible continuous representation of G then  $V^{K$ -fin} is an admissible  $(\mathfrak{g}, K)$ -module.

**Exercise 5.11.** Show that for any continuous representation V of G, the intersection  $V^{\infty} \cap V^{K\text{-fin}}$  is a  $(\mathfrak{g}, K)$ -module (not necessarily admissible).

**Exercise 5.12.** Show that if V is an admissible representation of G and L a finite-dimensional (continuous) representation of G then  $V \otimes L$  is also admissible. Prove the same statement for  $(\mathfrak{g}, K)$ -modules.

5.3. Harish-Chandra's admissibility theorem. We will now restrict our attention to semisimple Lie groups G. By this we will mean a connected linear real Lie group G with semisimple Lie algebra  $\mathfrak{g}$ . "Linear" means that it has a faithful finite-dimensional representation, i.e., is isomorphic to a closed subgroup of  $GL_n(\mathbb{C})$ . In other words, G is the connected component of the identity in  $G(\mathbb{R})$ , where G is a semisimple algebraic group defined over  $\mathbb{R}$ . Typical examples of such groups include  $SL_n(\mathbb{R})$  and  $SL_n(\mathbb{C})$  (in the latter case  $G = SL_n \times SL_n$  and the real structure defined by the involution permuting the two factors).

A fundamental result about the structure of semisimple Lie groups is

**Theorem 5.13.** (E. Cartan) Every semisimple Lie group G has a maximal compact subgroup  $K \subset G$  which is unique up to conjugation.

<sup>&</sup>lt;sup>12</sup>Indeed, every  $\mathfrak{g} \oplus \mathfrak{g}$ -module M with action  $(a, b, v) \mapsto (a, b) \circ v$ ,  $a, b \in \mathfrak{g}$ ,  $v \in M$  is a  $\mathfrak{g}$ -bimodule with  $av = (a, 0) \circ v$  and  $vb = (0, -b) \circ v$ , and vice versa.

**Example 5.14.** For  $G = SL_n(\mathbb{R})$  we have K = SO(n) and for  $G = SL_n(\mathbb{C})$  we have G = SU(n).

We will say that a continuous representation V of G is **admissible** if it is K-admissible with respect to a maximal compact subgroup  $K \subset G$  (does not matter which since they are all conjugate).

**Theorem 5.15.** (Harish-Chandra's admissibility theorem, [HC2]) Every irreducible unitary representation of a semisimple Lie group is admissible.

We will not give a proof (see [HC2],[Ga]).

**Remark 5.16.** 1. This theorem extends straightforwardly to the more general case of real reductive Lie groups.

2. Let  $G = SL_2(\mathbb{R})$  be the universal covering of  $SL_2(\mathbb{R})$ . Then G is not linear (why?) and so it is **not** viewed as a semisimple Lie group according to our definition. In fact, Harish-Chandra's theorem does not hold as stated for this group, since it has no nontrivial compact subgroups. This happens because when we take the universal cover, the maximal compact subgroup  $SO(2) = S^1$  gets replaced by the noncompact group  $\mathbb{R}$ . However, if we take for K the universal cover of SO(2) (even though it is not compact) then Harish-Chandra's theorem extends straightforwardly to this case.

**Exercise 5.17.** Let M be an admissible  $(\mathfrak{g}, K)$ -module and

$$M^{\vee} := \bigoplus_{V \in \operatorname{Irr} K} (\operatorname{Hom}(V, M) \otimes V)^* \subset M^*$$

be the restricted dual to M. Show that  $M^{\vee}$  has a natural structure of an admissible  $(\mathfrak{g}, K)$ -module, and  $(M^{\vee})^{\vee} \cong M$ .

#### 6. Weakly analytic vectors

6.1. Weakly analytic vectors and Harish-Chandra's analyticity. Let G be a Lie group and V a continuous representation of G.

**Definition 6.1.** A vector  $v \in V$  is called **weakly analytic** if for each  $h \in V^*$  the matrix coefficient h(gv) is a real analytic function of g.

**Example 6.2.** Let  $V=L^2(S^1)$  and  $G=S^1$  act by rotations. So if  $v(x)=\sum_{n\in\mathbb{Z}}v_ne^{inx}$  and  $h(x)=\sum_{n\in\mathbb{Z}}h_ne^{-inx}$  then for  $g=e^{i\theta}$  we have

$$h(g(\theta)v) = \sum_{n \in \mathbb{Z}} h_n v_n e^{in\theta}.$$

Thus v is a weakly analytic vector iff the sequence  $h_n v_n$  decays exponentially for any  $\ell_2$ -sequence  $\{h_n\}$ , which is equivalent to saying that  $v_n$  decays exponentially, i.e.,  $v(\theta)$  is analytic.

**Theorem 6.3.** (Harish-Chandra's analyticity theorem) If V is an admissible representation of a semisimple Lie group G with maximal compact subgroup K then every  $v \in V^{K-fin}$  is a weakly analytic vector.

Theorem 6.3 is proved in the next two subsections.

6.2. Elliptic regularity. The proof of Theorem 6.3 is based on the analytic elliptic regularity theorem, which is a fundamental result in analysis (see [Ca]). To state it, let X be a smooth manifold, and D(X) the algebra of (real) differential operators on X. This algebra has a filtration by order:  $D_0(X) = C^{\infty}(X) \subset D_1(X) \subset ...$ , such that

$$D_n(X) = \{ D \in \operatorname{End}_{\mathbb{C}} C^{\infty}(X) : [D, f] \in D_{n-1}(X) \forall f \in C^{\infty}(X) \}, \ n \ge 1,$$

and  $\operatorname{gr} D(X) = \bigoplus_{n \geq 0} \Gamma(X, S^n TX)$ , where  $\Gamma$  takes sections of the vector bundle. Thus for every differential operator D on X of order n we have its **symbol**  $\sigma(D) \in \operatorname{gr}_n D(X) = \Gamma(X, S^n TX)$ . For every  $x \in X$ ,  $\sigma(D)_x$  is thus a homogeneous polynomial of degree n on  $T_x^*X$ .

**Definition 6.4.** We say that D is **elliptic** at x if  $\sigma(D)_x(p) \neq 0$  for nonzero  $p \in T_x^*X$ . We say that D is **elliptic** (on X) if it is elliptic at all points  $x \in X$ .

**Example 6.5.** 1. If  $\dim X = 1$  then any differential operator with nonvanishing symbol is elliptic.

- 2. Fix a Riemannian metric on X and let  $\Delta$  be the corresponding Laplace operator,  $\Delta f = \text{div}(\text{grad } f)$ . Then  $\Delta$  is elliptic.
- 3. If D is elliptic then for any nonzero polynomial  $P \in \mathbb{R}[t]$  the operator P(D) is elliptic.

Note that ellipticity is an open condition, since it is equivalent to non-vanishing of  $\sigma(D)_x$  on the unit sphere in  $T_x^*X$  (under some inner product). Thus the set of  $x \in X$  on which a given operator D is elliptic is open in X.

**Theorem 6.6.** (Elliptic regularity) Suppose D is an elliptic operator with real analytic coefficients on an open set  $U \subset \mathbb{R}^N$ , and f(x) is a smooth solution of the PDE

$$Df = 0$$

on U. Then f is real analytic on U.

Corollary 6.7. Let X be a real analytic manifold and D an elliptic operator on X with analytic coefficients. Then every smooth solution of the equation Df = 0 on X is actually real analytic.

**Remark 6.8.** 1. This is, in fact, true much more generally, when f is a weak (i.e., distributional) solution of the equation Df = 0. Also the equation Df = 0 can be replaced by a more general inhomogeneous equation Df = g, where g is analytic.

2. If D is not elliptic, there is an obvious counterexample: the equation  $\frac{\partial^2 f}{\partial x \partial y} = 0$  on  $\mathbb{R}^2$  has smooth non-analytic solutions of the form f(x) + g(y),  $f, g \in C^{\infty}(\mathbb{R})$ .

**Example 6.9.** 1. For N=1 this theorem just says that a solution of an ODE

$$f^{(n)}(x) + a_1(x)f^{(n-1)}(x) + \dots + a_n(x)f(x) = 0$$

with real analytic coefficients is itself real analytic, a classical fact about ODE.

- 2. Let N=2 and  $D=\Delta$  be the Laplace operator on  $U\subset\mathbb{R}^2$  with respect to some Riemannian metric with real analytic coefficients. This metric defines a conformal structure with real analytic local complex coordinate z. Then every harmonic function f (i.e., one satisfying  $\Delta f=0$ ) is a real part of a holomorphic function of z, hence is real analytic, which proves elliptic regularity in this special case.
- 3. Suppose f,g are Schwartz functions on  $\mathbb{R}^n$  and  $D=Q(\partial)$  is an elliptic operator with constant coefficients, where Q is a real polynomial (so the leading term of Q is nonvanishing for nonzero vectors). Then elliptic regularity says that if g is analytic, so is f. This can be easily proved using Fourier transform. Indeed, for Fourier transforms we get  $Q(p)\widehat{f}(p)=\widehat{g}(p)$ . Thus  $\widehat{g}(p)=\frac{\widehat{f}(p)}{Q(p)}$ , so this must be a smooth function. Note that  $|Q(p)|\to\infty$  as  $p\to\infty$  because Q has non-vanishing leading

term. So, since g is analytic,  $\widehat{g}$  decays exponentially at infinity, hence so does  $\widehat{f}$ . Thus f is analytic.

6.3. Proof of Harish-Chandra's analyticity Theorem. We are now ready to prove Theorem 6.3. Let  $\mathfrak{g} = \text{Lie}G$  and  $b \in U(\mathfrak{g})$ . Then we have a linear operator  $\pi_*(b): V^{\infty} \to V^{\infty}$ , which we will write just as b for short. Moreover, if  $b \in U(\mathfrak{g})^K$  then it preserves the subspace  $V^{\rho} \subset V^{\infty}$  for each irreducible representation  $\rho$  of K. Therefore, since all  $V^{\rho}$  are finite-dimensional, for any  $v \in V^{K\text{-fin}}$  there exists a nonzero polynomial  $P \in \mathbb{R}[t]$  such that P(b)v = 0 (e.g., we can take P to be the product of the characteristic polynomial of b on Kv by its complex conjugate).

Now recall that  $U(\mathfrak{g})$  can be thought of as the algebra of left-invariant real differential operators on G. Let  $\psi_{h,v}(g) := h(gv)$  be the matrix coefficient function. We know that this function is smooth, and we have

$$(P(b)\psi_{h,v})(g) = h(gP(b)v) = 0.$$

Thus if b is an elliptic differential operator on G, it will follow from Corollary 6.7 that  $\psi_{h,v}$  is real analytic, as desired.

It remains to find  $b \in U(\mathfrak{g})^K$  which defines an elliptic operator on G. For this purpose fix a left-invariant Riemannian metric on G, and make it K-invariant (under right, or, equivalently, adjoint action) by averaging over K. Then the Laplace operator  $\Delta$  corresponding to this metric is elliptic and given by some element  $\Delta \in U(\mathfrak{g})^K$ , so we may take  $b = \Delta$ . This proves Theorem 6.3.

**Remark 6.10.** If G is simple, there exists a unique up to scaling two-sided invariant metric on G. This metric, however, is pseudo-Riemannian rather than Riemannian if G is not compact. Thus the corresponding Laplace operator is hyperbolic rather than elliptic, so not suitable for our purposes.

#### 6.4. Applications of weakly analytic vectors.

**Corollary 6.11.** The action of G on V is completely determined by the corresponding  $(\mathfrak{g}, K)$ -module  $V^{K\text{-}fin}$ .

Proof. Since  $V^{K\text{-fin}}$  is dense in V, it suffices to specify gv for  $v \in V^{K\text{-fin}}$ . For this it suffices to specify h(gv) for all  $h \in V^*$ . By Theorem 6.3 and the analytic continuation principle, this is determined by the derivatives of all orders of h(gv) at g = 1. But these have the form h(bv) where  $b \in U(\mathfrak{g})$ , so are determined by bv.

**Corollary 6.12.** Let  $W \subset V^{K\text{-}fin}$  be a sub- $(\mathfrak{g}, K)$ -module. Then the closure  $\overline{W} \subset V$  is G-invariant.

Proof. Let  $w \in W$ ,  $g \in G$ . It suffices to show that  $gw \in \overline{W}$ . If not, then the space  $W' := \overline{W} \oplus \mathbb{C} gw$  is a closed subspace of V containing  $\overline{W}$  as a subspace of codimension 1. So there exists a unique continuous linear functional  $h: W' \to \mathbb{C}$  such that h(gw) = 1 and  $h|_{\overline{W}} = 0$ . By the Hahn-Banach theorem, h can be extended to an element of  $V^*$ . Thus to get a contradiction, it is enough to show that for every  $h \in V^*$  that vanishes on  $\overline{W}$ , we have h(gw) = 0. But by Theorem 6.3, this function is analytic in g. So it suffices to check that its derivatives at g = 1 vanish. But these derivatives are of the form h(bw) for  $b \in U(\mathfrak{g})$ , so vanish since  $bw \in W$ .

**Corollary 6.13.** Let V be an admissible representation of G. There is a bijection between subrepresentations of V and  $(\mathfrak{g}, K)$ -submodules of  $V^{K\text{-fin}}$ , given by  $\alpha: U \subset V \mapsto U^{K\text{-fin}}$ . The inverse is given by  $\beta: W \mapsto \overline{W}$ .

*Proof.* Since  $U^{K\text{-fin}}$  is dense in U, we have  $\beta \circ \alpha = \text{Id}$ . To show that  $\alpha \circ \beta = \text{Id}$ , we need to show that  $\overline{W}^{K\text{-fin}} = W$ . Clearly  $\overline{W}^{K\text{-fin}}$  contains W, so we just need to prove the opposite inclusion. Let  $w \in \overline{W}^{\rho}$ , then we have a sequence  $w_n \to w$ ,  $w_n \in W$ . Now apply the projector  $\xi_{\rho}$ :

$$w'_n := \pi(\xi_\rho)w_n \to \pi(\xi_\rho)w = w, \ n \to \infty,$$

and  $w'_n \in W^{\rho}$ . Thus  $w \in \overline{W^{\rho}} = W^{\rho}$ , since  $W^{\rho}$  is finite-dimensional. Hence  $\overline{W}^{K\text{-fin}} = W$ .

Corollary 6.14. If V is irreducible then  $V^{K\text{-fin}}$  is an irreducible  $(\mathfrak{g}, K)$ module, and vice versa.

Corollary 6.15. If V is of finite length then  $V^{K\text{-fin}}$  is a Harish-Chandra module.

*Proof.* By Corollary 6.13,  $V^{K\text{-fin}}$  is a finite length  $(\mathfrak{g}, K)$ -module. But any finite length  $(\mathfrak{g}, K)$ -module is finitely generated over  $U(\mathfrak{g})$ , hence a Harish-Chandra module.

Let Rep G denote the category of admissible representations of G of finite length, and  $\mathcal{HC}_G$  the category of Harish-Chandra modules for G. Thus we obtain

**Theorem 6.16.** The assignment  $V \mapsto V^{K\text{-fin}}$  defines an exact, faithful functor  $\text{Rep } G \to \mathcal{HC}_G$ , which maps irreducibles to irreducibles.

#### 7. Infinitesimal equivalence and globalization

7.1. Infinitesimal equivalence. The functor of Theorem 6.16 is not full, however, since there exist pairs of non-isomorphic  $V, W \in \operatorname{Rep} G$  such that  $V^{K-\operatorname{fin}} \cong W^{K-\operatorname{fin}}$  as Harish-Chandra modules. Representations  $V, W \in \operatorname{Rep} G$  such that  $V^{K-\operatorname{fin}} \cong W^{K-\operatorname{fin}}$  as Harish-Chadra modules are called infinitesimally equivalent. In other words, infinitesimally equivalent representations with the same underlying Harish-Chandra module M differ by what topology we put on M (namely, the corresponding representation  $\widehat{M}$  is the completion of M is this topology). An example of infinitesimally equivalent but non-isomorphic representations are  $L^2(\mathbb{RP}^1)$  and  $C^{\infty}(\mathbb{RP}^1)$  as representations of  $G = SL_2(\mathbb{R})$  (with G-action on half-densities).

However, we have the following proposition.

**Proposition 7.1.** Let V, W be two unitary representations in Rep G. If  $V^{K-\operatorname{fin}} \cong W^{K-\operatorname{fin}}$  as Harish-Chandra modules, then  $V \cong W$  as unitary representations. In other words, infinitesimally equivalent unitary representations in Rep G are isomorphic.

Proof. Clearly, it suffices to assume that V,W are irreducible. If V is unitary irreducible then  $V^{K-\text{fin}}$  has an invariant positive Hermitian inner product  $B=B_V$  restricted from V. Moreover, B is the unique invariant Hermitian inner product on  $V^{K-\text{fin}}$  up to scaling. Indeed, if B' is another then pick a nonzero  $v \in V^{K-\text{fin}}$  and let  $\lambda := \frac{B'(v,v)}{B(v,v)}$ . Then  $B' - \lambda B$  has a nonzero kernel, which is a  $(\mathfrak{g},K)$ -submodule of  $V^{K-\text{fin}}$ . This kernel therefore must be the whole  $V^{K-\text{fin}}$ , so  $B' = \lambda B$ .

Thus if  $A: V^{K-\text{fin}} \to W^{K-\text{fin}}$  is an isomorphism then it is an isometry with respect to  $B_V$ ,  $B_W$  under suitable normalization of these forms. Then A extends by continuity to a unitary isomorphism  $V \to W$  which commutes with K.

It remains to show that A commutes with G. For  $v \in V$ ,  $w \in W$ , consider the function

$$f_{w,v}(g) := B_W((gA - Ag)v, w) = B_W(gAv, w) - B_V(gv, A^{-1}w), g \in G.$$
 Our job is to show that  $f_{w,v}(g) = 0$ . It suffices to check this when  $v \in V^{K-\text{fin}}$ , as it is dense in  $V$ . In this case by Harish-Chandra's analyticity theorem, the function  $f_{w,v}(g)$  is analytic on  $G$ . Also all its derivatives at 1 vanish since  $bA - Ab = 0$  for any  $b \in U(\mathfrak{g})$ . This implies that  $f_{w,v}$  is indeed zero, as desired.

<sup>&</sup>lt;sup>13</sup>An invariant inner product on a  $(\mathfrak{g}, K)$ -module is one that is invariant under both  $\mathfrak{g}$  and K, i.e., K-invariant and satisfying the equality B(av, w) + B(v, aw) = 0 for all  $a \in \mathfrak{g}$ .

7.2. **Dixmier's lemma and infinitesimal character.** The following is an infinite-dimensional analog of Schur's lemma.

**Lemma 7.2.** (Dixmier) Let A be a countable-dimensional  $\mathbb{C}$ -algebra and M a simple A-module. Then  $\operatorname{End}_A(M) = \mathbb{C}$ . In particular, the center Z of A acts on M by a character  $\chi: Z \to \mathbb{C}$ .

Note that the condition of countable dimension cannot be dropped. Without it, a counterexample is  $A = M = \mathbb{C}(x)$  (the field of rational functions in one variable), then  $\operatorname{End}_A(M) = \mathbb{C}(x)$ .

Proof. Let  $D := \operatorname{End}_A(M)$ . By the usual Schur lemma, D is a division algebra. Assume the contrary, that  $D \neq \mathbb{C}$ . Then for any  $x \in D \setminus \mathbb{C}$ , D contains the field  $\mathbb{C}(x)$  of rational functions of x (as  $\mathbb{C}$  has no finite field extensions). But  $\mathbb{C}(x)$  has uncountable dimension (contains linearly independent elements  $\frac{1}{x-a}$ ,  $a \in \mathbb{C}$ ), hence so does D. On the other hand, let  $v \in M$  be a nonzero vector, then M = Av and the map  $D \to M$  given by  $T \mapsto Tv$  is injective. Thus M is countable-dimensional, hence so is D, contradiction.

Now let  $\mathfrak{g}$  be a countable-dimensional complex Lie algebra and M a simple  $\mathfrak{g}$ -module. By Lemma 7.2, the center  $Z(\mathfrak{g})$  of  $U(\mathfrak{g})$  acts on M by a character,  $\chi: Z(\mathfrak{g}) \to \mathbb{C}$ . This character is called the **infinitesimal** character of M.

In particular, for semisimple groups we obtain

Corollary 7.3. (Schur's lemma for  $(\mathfrak{g}, K)$ -modules) Any endomorphism of an irreducible  $(\mathfrak{g}, K)$ -module M is a scalar. Thus the center  $Z(\mathfrak{g})$  of  $U(\mathfrak{g})$  acts on M by a infinitesimal character  $\chi: Z(\mathfrak{g}) \to \mathbb{C}$ .

The character  $\chi$  is often also called the **infinitesimal character** of M.

**Exercise 7.4.** Show that the action of  $Z(\mathfrak{g})$  on every admissible  $(\mathfrak{g}, K)$ -module M is locally finite.

#### 7.3. Harish-Chandra's globalization theorem.

**Theorem 7.5.** (Harish-Chandra's globalization theorem) Every unitary irreducible Harish-Chandra module M for G uniquely integrates (=globalizes) to an irreducible admissible unitary representation of G.

*Proof.* As before, fix a positive definite K-invariant inner product on  $\mathfrak{g}$ , and consider the element  $C_{\mathfrak{g}}^+ := \sum_{j=1}^{\dim \mathfrak{g}} a_j^2 \in U(\mathfrak{g})$ , where  $a_j$  is an orthonormal basis of  $\mathfrak{g}$  under this inner product. If  $C_{\mathfrak{g}}$  is the (suitably normalized) quadratic Casimir of  $\mathfrak{g}$ , then  $C_{\mathfrak{g}}^+ = C_{\mathfrak{g}} + 2C_{\mathfrak{k}}$ , where  $C_{\mathfrak{k}}$  is the Casimir of  $\mathfrak{k} := \operatorname{Lie} K$  corresponding to the restriction of the inner

product to  $\mathfrak{k}$ . If  $L_{\nu}$  is the highest weight irreducible representation with highest weight  $\nu$  then  $-C_{\mathfrak{k}}|_{L_{\nu}} = |\nu + \rho_{K}|^{2} - |\rho_{K}|^{2}$ , where  $\rho_{K}$  is the half-sum of positive roots of K. Also  $C_{\mathfrak{g}}|_{M} = C_{M}$  is a scalar. Thus if  $M^{\nu} := M^{L_{\nu}}$  then

$$-C_{\mathfrak{g}}^{+}|_{M^{\nu}} = 2|\nu + \rho_{K}|^{2} - 2|\rho_{K}|^{2} - C_{M} =: q(\nu).$$

Note that for  $v \in M^{\nu}$  we have

$$\sum_{j=1}^{\dim \mathfrak{g}} \|a_j v\|^2 = -(\sum_{j=0}^{\dim \mathfrak{g}} a_j^2 v, v) = -(C_{\mathfrak{g}}^+ v, v) = q(\nu) \|v\|^2;$$

in particular,  $q(\nu) \geq 0$  and  $q(\nu) \sim 2|\nu|^2$  for large  $\nu$ . It follows that for any  $a \in \mathfrak{g}, v \in M^{\nu}$ ,

$$||av||^2 \le q(\nu) ||a||^2 ||v||^2$$
.

Now, for  $a \in M^{\nu_0}$  all components of  $a^n v$  belong to  $M^{\nu}$ , where  $\nu = \nu_0 + \beta_1 + ... + \beta_n$  and  $\beta_j$  are weights of  $\mathfrak{g}$  as a K-module. So there exist  $R, c = c(\nu_0) > 0$  such that

$$||a^n v|| \le (Rn + c) ||a|| ||a^{n-1} v||, n \ge 1.$$

Thus

$$||a^n v|| \le (R+c)...(Rn+c) ||a||^n ||v||.$$

So the series

$$e^a v := \sum_{n>0} \frac{a^n v}{n!}$$

converges absolutely in the Hilbert space  $\widehat{M}$  in the region  $\|a\| < R^{-1}$ , and convergence is uniform on compact sets with all derivatives, and defines an analytic function of a. Moreover, it is easy to check that  $\|e^av\| = \|v\|$  (since a is skew-symmetric under the inner product of M). Thus the operator  $e^a: M \to \widehat{M}$  extends to a unitary operator on  $\widehat{M}$ . The formal Campbell-Hausdorff formula then implies that this defines a continuous unitary action  $\pi$  of a neighborhood U of 0 in G on  $\widehat{M}$  such that  $\pi(xy) = \pi(x)\pi(y)$  if  $x, y, xy \in U$ . It is well known that this implies that  $\pi$  extends to a unitary representation of the universal cover  $\widehat{G}$  of G on M. Now let  $\widehat{K}$  be the preimage of K in  $\widehat{G}$  (by the polar decomposition, it is also the universal cover of K). Since by definition  $\pi|_{\widehat{K}}$  extends to K, it follows that  $\pi$  actually factors through G.

Thus, using Harish-Chandra's admissibility theorem, we obtain

Corollary 7.6. For a semisimple Lie group G, the assignment  $V \mapsto V^{K-\text{fin}}$  is an equivalence of categories between unitary representations of G of finite length and unitary Harish-Chandra modules of finite

length (i.e., Harish-Chandra modules which admit an invariant positive Hermitian inner product).

However, while irreducible Harish-Chandra modules for any G have been classified, determining which of them are unitary is a very difficult problem which is not yet fully solved.

#### 8. Highest weight modules and Verma modules

8.1.  $\mathfrak{g}$ -modules with a weight decomposition. Let us recall basic results on highest weight modules and Verma modules for a complex semisimple Lie algebra  $\mathfrak{g}$ .

Let  $\mathfrak{g} = \mathfrak{n}_- \oplus \mathfrak{h} \oplus \mathfrak{n}_+$  be a triangular decomposition and  $\lambda \in \mathfrak{h}^*$  be a weight. We have  $\mathfrak{n}_{\pm} = \oplus_{\alpha \in R_{\pm}} \mathfrak{g}_{\alpha}$ , where  $R_{\pm}$  are the sets of positive and negative roots. Let  $Q \subset \mathfrak{h}^*$  be the root lattice of  $\mathfrak{g}$  spanned by its roots. Let  $e_i, f_i, h_i, i = 1, ..., r$  be the Chevalley generators of  $\mathfrak{g}$ . Let  $P \subset \mathfrak{h}^*$  be the weight lattice, consisting of  $\lambda \in \mathfrak{h}^*$  with  $\lambda(h_i) \in \mathbb{Z}$  for all i and  $P_+ \subset P$  be the set of dominant integral weights, defined by the condition  $\lambda(h_i) \in \mathbb{Z}_{\geq 0}$  for all i. Finally, let  $Q_+ \subset Q$  be the set of sums of positive roots.

**Definition 8.1.** Let V a representation of  $\mathfrak{g}$  (possibly infinite-dimensional). Then a vector  $v \in V$  is said to have **weight**  $\lambda$  if  $hv = \lambda(h)v$  for all  $h \in \mathfrak{h}$ . The subspace of such vectors is denoted by  $V[\lambda]$ . If  $V[\lambda] \neq 0$ , we say that  $\lambda$  is a weight of V, and the set of weights of V is denoted by P(V).

It is easy to see that  $\mathfrak{g}_{\alpha}V[\lambda] \subset V[\lambda + \alpha]$ .

Let  $V' \subset V$  be the span of all weight vectors in V. Then it is clear that  $V' = \bigoplus_{\lambda \in \mathfrak{h}^*} V[\lambda]$ .

Definition 8.2. We say that V has a weight decomposition (with respect to a Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}$ ), or is  $\mathfrak{h}$ -semisimple if V' = V, i.e., if  $V = \bigoplus_{\lambda \in \mathfrak{h}^*} V[\lambda]$ .

Note that not every representation of  $\mathfrak{g}$  has a weight decomposition (e.g., for  $V = U(\mathfrak{g})$  with  $\mathfrak{g}$  acting by left multiplication all weight subspaces are zero).

- Definition 8.3. A vector v in  $V[\lambda]$  is called a singular (or highest weight) vector of weight  $\lambda$  if  $e_i v = 0$  for all i, i.e., if  $\mathfrak{n}_+ v = 0$ . A representation V of  $\mathfrak{g}$  is a highest weight representation with highest weight  $\lambda$  if it is generated by such a nonzero vector.
- 8.2. Verma modules. The Verma module  $M_{\lambda}$  is defined as "the largest highest weight module with highest weight  $\lambda$ ". Namely, it is generated by a single highest weight vector  $v_{\lambda}$  with **defining relations**  $hv = \lambda(h)v$  for  $h \in \mathfrak{h}$  and  $e_iv = 0$ . More formally, we make the following definition.

**Definition 8.4.** Let  $I_{\lambda} \in U(\mathfrak{g})$  be the left ideal generated by the elements  $h - \lambda(h), h \in \mathfrak{h}$  and  $e_i, i = 1, ..., r$ . Then the **Verma module**  $M_{\lambda}$  is the quotient  $U(\mathfrak{g})/I_{\lambda}$ .

In this realization, the highest weight vector  $v_{\lambda}$  is just the class of the unit 1 of  $U(\mathfrak{g})$ .

**Proposition 8.5.** The map  $\phi: U(\mathfrak{n}_{-}) \to M_{\lambda}$  given by  $\phi(x) = xv_{\lambda}$  is an isomorphism of left  $U(\mathfrak{n}_{-})$ -modules.

*Proof.* By the PBW theorem, the multiplication map

$$\xi: U(\mathfrak{n}_{-}) \otimes U(\mathfrak{h} \oplus \mathfrak{n}_{+}) \to U(\mathfrak{g})$$

is a linear isomorphism. It is easy to see that  $\xi^{-1}(I_{\lambda}) = U(\mathfrak{n}_{-}) \otimes K_{\lambda}$ , where

$$K_{\lambda} := \sum_{i} U(\mathfrak{h} \oplus \mathfrak{n}_{+})(h_{i} - \lambda(h_{i})) + \sum_{i} U(\mathfrak{h} \oplus \mathfrak{n}_{+})e_{i}$$

is the kernel of the homomorphism  $\chi_{\lambda}: U(\mathfrak{h} \oplus \mathfrak{n}_{+}) \to \mathbb{C}$  given by  $\chi_{\lambda}(h) = \lambda(h), h \in \mathfrak{h}, \chi_{\lambda}(e_{i}) = 0$ . Thus, we have a natural isomorphism of left  $U(\mathfrak{n}_{-})$ -modules

$$U(\mathfrak{n}_{-}) = U(\mathfrak{n}_{-}) \otimes U(\mathfrak{h} \oplus \mathfrak{n}_{+})/K_{\lambda} \to M_{\lambda},$$

as claimed.  $\Box$ 

Remark 8.6. The definition of  $M_{\lambda}$  means that it is the **induced module**  $U(\mathfrak{g}) \otimes_{U(\mathfrak{h} \oplus \mathfrak{n}_+)} \mathbb{C}_{\lambda}$ , where  $\mathbb{C}_{\lambda}$  is the one-dimensional representation of  $\mathfrak{h} \oplus \mathfrak{n}_+$  on which it acts via  $\chi_{\lambda}$ .

Corollary 8.7.  $M_{\lambda}$  has a weight decomposition with  $P(M_{\lambda}) = \lambda - Q_{+}$ , dim  $M_{\lambda}[\lambda] = 1$ , and weight subspaces of  $M_{\lambda}$  are finite-dimensional.

**Proposition 8.8.** (i) If V is a representation of  $\mathfrak{g}$  and  $v \in V$  is a vector such that  $hv = \lambda(h)v$  for  $h \in h$  and  $e_iv = 0$  then there is a unique homomorphism  $\eta: M_{\lambda} \to V$  such that  $\eta(v_{\lambda}) = v$ . In particular, if V is generated by such  $v \neq 0$  (i.e., V is a highest weight representation with highest weight vector v) then V is a quotient of  $M_{\lambda}$ .

- (ii) Every highest weight representation has a weight decomposition into finite-dimensional weight subspaces.
- (iii) Every highest weight representation V has a unique highest weight generator, up to scaling.
- *Proof.* (i) Uniqueness follows from the fact that  $v_{\lambda}$  generates  $M_{\lambda}$ . To construct  $\eta$ , note that we have a natural map of  $\mathfrak{g}$ -modules  $\widetilde{\eta}: U(\mathfrak{g}) \to V$  given by  $\widetilde{\eta}(x) = xv$ . Moreover,  $\widetilde{\eta}|_{I_{\lambda}} = 0$  thanks to the relations satisfied by v, so  $\widetilde{\eta}$  descends to a map  $\eta: U(\mathfrak{g})/I_{\lambda} = M_{\lambda} \to V$ . Moreover, if V is generated by v then this map is surjective, as desired.
- (ii) This follows from (i) since a quotient of any representation with a weight decomposition must itself have a weight decomposition.

(iii) Suppose v, w are two highest weight generators of V of weights  $\lambda, \mu$ . If  $\lambda = \mu$  then they are proportional since dim  $V[\lambda] \leq \dim M_{\lambda}[\lambda] = 1$ , as V is a quotient of  $M_{\lambda}$ . On the other hand, if  $\lambda \neq \mu$ , then we can assume without loss of generality that  $\lambda - \mu \notin Q_+$  (otherwise switch  $\lambda, \mu$ ). Then  $\mu \notin \lambda - Q_+$ , hence  $\mu \notin P(V)$ , a contradiction.

#### 8.3. Irreducible highest weight g-modules.

**Proposition 8.9.** For every  $\lambda \in \mathfrak{h}^*$ , the Verma module  $M_{\lambda}$  has a unique irreducible quotient  $L_{\lambda}$ . Moreover,  $L_{\lambda}$  is a quotient of every highest weight  $\mathfrak{g}$ -module V with highest weight  $\lambda$ .

Proof. Let  $Y \subset M_{\lambda}$  be a proper submodule. Then Y has a weight decomposition, and cannot contain a nonzero multiple of  $v_{\lambda}$  (as otherwise  $Y = M_{\lambda}$ ), so  $P(Y) \subset (\lambda - Q_{+}) \setminus \{\lambda\}$ . Now let  $J_{\lambda}$  be the sum of all proper submodules  $Y \subset M_{\lambda}$ . Then  $P(J_{\lambda}) \subset (\lambda - Q_{+}) \setminus \{\lambda\}$ , so  $J_{\lambda}$  is also a proper submodule of  $M_{\lambda}$  (the maximal one). Thus,  $L_{\lambda} := M_{\lambda}/J_{\lambda}$  is an irreducible highest weight module with highest weight  $\lambda$ . Moreover, if V is any nonzero quotient of  $M_{\lambda}$  then the kernel K of the map  $M_{\lambda} \to V$  is a proper submodule, hence contained in  $J_{\lambda}$ . Thus the surjective map  $M_{\lambda} \to L_{\lambda}$  descends to a surjective map  $V \to L_{\lambda}$ . The kernel of this map is a proper submodule of V, hence zero if V is irreducible. Thus in the latter case  $V \cong L_{\lambda}$ .

Corollary 8.10. Irreducible highest weight  $\mathfrak{g}$ -modules are classified by their highest weight  $\lambda \in \mathfrak{h}^*$ , via the bijection  $\lambda \mapsto L_{\lambda}$ .

**Exercise 8.11.** Let  $\mathfrak{g} = \mathfrak{sl}_2$  with standard generators e, f, h and identify  $\mathfrak{h}^* \cong \mathbb{C}$  via  $\lambda \mapsto \lambda(h)$ . Show that  $M_{\lambda}$  is irreducible if  $\lambda \notin \mathbb{Z}_{\geq 0}$ , while for  $\lambda$  a nonnegative integer we have  $J_{\lambda} = M_{-\lambda-2}$ , so  $L_{\lambda}$  is the  $\lambda + 1$ -dimensional irreducible representation of  $\mathfrak{sl}_2$ .

It is known from the theory of finite-dimensional representations of  $\mathfrak{g}$  that its irreducible finite-dimensional representations are  $L_{\lambda}$  with  $\lambda \in P_{+}$ . Thus we have

**Proposition 8.12.**  $L_{\lambda}$  is finite-dimensional if and only if  $\lambda \in P_{+}$ .

Note that the "only if" direction of this proposition follows immediately from Exercise 8.11.

#### 8.4. Exercises.

Exercise 8.13. Let  $\mathfrak{g}$  be a finite-dimensional simple complex Lie algebra, and V a finite-dimensional representation of  $\mathfrak{g}$ . Let  $\lambda, \mu \in \mathfrak{h}^*$  be weights for  $\mathfrak{g}$ , and X, Y be representations of  $\mathfrak{g}$  with  $P(X) \subset \lambda - Q_+$ ,  $P(Y) \subset \mu - Q_+$ , and  $X[\lambda] = \mathbb{C}v_{\lambda}$ ,  $Y[\mu] = \mathbb{C}v_{\mu}$  for nonzero vectors

 $v_{\lambda}, v_{\mu}$ . Given a linear map  $\Phi: X \to V \otimes Y$ , let the **expectation value** of  $\Phi$  be defined by

$$\langle \Phi \rangle := (\mathrm{Id} \otimes v_{\mu}^*, \Phi v_{\lambda}) \in V$$

where  $v_{\mu}^* \in Y[\mu]^*$  is such that  $(v_{\mu}^*, v_{\mu}) = 1$ . In other words, we have

$$\Phi v_{\lambda} = \langle \Phi \rangle \otimes v_{\mu} + \text{lower terms}$$

where the lower terms have lower weight than  $\mu$  in the second component.

- (i) Show that if  $\Phi$  is a homomorphism then  $\langle \Phi \rangle$  has weight  $\lambda \mu$ .
- (ii) Let  $M_{\lambda}$  be the Verma module with highest weight  $\lambda \in \mathfrak{h}^*$ , and  $\overline{M}_{-\mu}$  be the **lowest weight** Verma module with lowest weight  $-\mu$ , i.e., generated by a vector  $v_{-\mu}$  with defining relations  $hv_{-\mu} = -\mu(h)v_{-\mu}$  for  $h \in \mathfrak{h}$  and  $f_iv_{-\mu} = 0$ . Show that the map  $\Phi \mapsto \langle \Phi \rangle$  defines an isomorphism

$$\operatorname{Hom}_{\mathfrak{g}}(M_{\lambda}, V \otimes \overline{M}_{-\mu}^*) \cong V[\lambda - \mu]$$

where \* denotes the restricted dual (the direct sum of duals of all weight subspaces).

- (iii) Let  $\lambda \in P_+$  and  $V[\nu]_{\lambda}$  be the subspace of vectors  $v \in V[\nu]$  of weight  $\nu$  which satisfy the equalities  $f_i^{(\lambda,\alpha_i^\vee)+1}v=0$  for all i. Show that a map  $\Phi \in \operatorname{Hom}_{\mathfrak{g}}(M_{\lambda}, V \otimes \overline{M}_{-\mu}^*)$  factors through  $L_{\lambda}$  iff  $\langle \Phi \rangle \in V[\lambda \mu]_{\lambda}$ , i.e.,  $f_i^{(\lambda,\alpha_i^\vee)+1}\langle \Phi \rangle = 0$  (for this, use that  $e_j f_i^{(\lambda,\alpha_i^\vee)+1}v_{\lambda} = 0$ , and that the kernel of  $M_{\lambda} \to L_{\lambda}$  is generated by the vectors  $f_i^{(\lambda,\alpha_i^\vee)+1}v_{\lambda}\rangle$ . Deduce that the map  $\Phi \mapsto \langle \Phi \rangle$  defines an isomorphism  $\operatorname{Hom}_{\mathfrak{g}}(L_{\lambda}, V \otimes \overline{M}_{-\mu}^*) \cong V[\lambda \mu]_{\lambda}$ .
- (iv) Now let both  $\lambda, \mu$  be in  $P_+$ . Show that every homomorphism  $L_{\lambda} \to V \otimes \overline{M}_{-\mu}^*$  in fact lands in  $V \otimes L_{\mu} \subset V \otimes \overline{M}_{-\mu}^*$ . Deduce that the map  $\Phi \mapsto \langle \Phi \rangle$  defines an isomorphism

$$\operatorname{Hom}_{\mathfrak{q}}(L_{\lambda}, V \otimes L_{\mu}) \cong V[\lambda - \mu]_{\lambda}.$$

- (v) Let  $V = \mathbb{C}^n$  be the vector representation of  $SL_n(\mathbb{C})$ . Determine the weight subspaces of  $S^mV$ , and compute the decomposition of  $S^mV \otimes L_\mu$  into irreducibles for all  $\mu \in P_+$  (use (iv)).
- (vi) For any  $\mathfrak{g}$ , compute the decomposition of  $\mathfrak{g} \otimes L_{\mu}$ ,  $\mu \in P_{+}$ , where  $\mathfrak{g}$  is the adjoint representation of  $\mathfrak{g}$  (again use (iv)).

In both (v) and (vi) you should express the answer in terms of the numbers  $k_i$  such that  $\mu = \sum_i k_i \omega_i$  and the Cartan matrix entries of  $\mathfrak{g}$ .

**Exercise 8.14.** (D. N. Verma) (i) Let  $\mathfrak{g} = \mathfrak{n}_- \oplus \mathfrak{h} \oplus \mathfrak{n}_+$  be a finite-dimensional simple complex Lie algebra, and  $\lambda, \mu \in \mathfrak{h}^*$ . Show that every nonzero homomorphism  $M_{\mu} \to M_{\lambda}$  is injective. (Use that  $U(\mathfrak{n}_-)$ 

has no zero divisors). Deduce that if  $M_{\lambda}$  is reducible then there exists  $\lambda' \in \lambda - Q_+, \ \lambda' \neq \lambda$  with  $M_{\lambda'} \subset M_{\lambda}$ .

(ii) Show that for every  $\lambda \in \mathfrak{h}^*$  there is  $\lambda' \in \lambda - Q_+$  with  $M_{\lambda'} \subset M_{\lambda}$  and  $M_{\lambda'}$  irreducible. (Assume the contrary and construct an infinite sequence of proper inclusions

...
$$M_{\lambda_2} \subset M_{\lambda_1} \subset M_{\lambda}$$
.

Then derive a contradiction by looking at the eigenvalues of the quadratic Casimir  $C \in U(\mathfrak{g})$ .

- (iii) Show that if  $M_{\mu}$  is irreducible then dim  $\operatorname{Hom}_{\mathfrak{g}}(M_{\mu}, M_{\lambda}) \leq 1$ . (Look at the growth of the dimensions of weight subspaces).
- (iv) Show that dim  $\operatorname{Hom}_{\mathfrak{g}}(M_{\mu}, M_{\lambda}) \leq 1$  for any  $\lambda, \mu \in \mathfrak{h}^*$ . (Look at the restriction of a homomorphism  $M_{\mu} \to M_{\lambda}$  to  $M_{\mu'} \subset M_{\mu}$  which is irreducible).

**Exercise 8.15.** (i) Keep the notation of Exercise 8.14. Let  $\lambda \in \mathfrak{h}^*$  be such that  $(\lambda, \alpha_i^{\vee}) = n - 1$  for a positive integer n and simple root  $\alpha_i$ . Show that there is an inclusion  $M_{\lambda - n\alpha_i} \hookrightarrow M_{\lambda}$ .

- (ii) Let  $\rho$  be the sum of fundamental weights of  $\mathfrak{g}$  and W be the Weyl group of  $\mathfrak{g}$ . For  $w \in W$ ,  $\lambda \in \mathfrak{h}^*$  let  $w \bullet \lambda := w(\lambda + \rho) \rho$  (the **shifted action** of W). Deduce from (i) that if  $\lambda \in P_+$  then for every  $w \in W$ , there is an inclusion  $\iota_w : M_{w \bullet \lambda} \hookrightarrow M_{\lambda}$ , and that if  $w = w_1 w_2$  with  $\ell(w) = \ell(w_1) + \ell(w_2)$  (where  $\ell(w)$  is the length of w) then  $\iota_w$  factors through  $\iota_{w_2}$ . In particular, we have an inclusion  $M_{w \bullet \lambda} \hookrightarrow M_{w_2 \bullet \lambda}$ .
- (iii) Show that  $M_{\lambda}$  is irreducible unless  $(\lambda + \rho, \alpha^{\vee}) = 1$  for some  $\alpha \in Q_{+} \setminus 0$ , where  $\alpha^{\vee} := \frac{2\alpha}{(\alpha,\alpha)}$  (look at the eigenvalues of the quadratic Casimir).
- (iv) For  $\beta \in Q_+$  define the **Kostant partition function**  $K(\beta)$  to be the number of unordered representations of  $\beta$  as a sum of positive roots of  $\mathfrak{g}$  (thus  $K(\beta) = \dim U(\mathfrak{n}_+)[\beta]$ ). Also define the **Shapovalov pairing**

$$B_{\beta}(\lambda): U(\mathfrak{n}_{+})[\beta] \times U(\mathfrak{n}_{-})[-\beta] \to \mathbb{C}$$

by the formula

$$xyv_{\lambda} = B_{\beta}(\lambda)(x, y)v_{\lambda},$$

where  $x \in U(\mathfrak{n}_+)[\beta], y \in U(\mathfrak{n}_-)[-\beta]$ , and  $v_{\lambda}$  is the highest weight vector of  $M_{\lambda}$ . Let

$$D_{\beta}(\lambda) := \det B_{\beta}(\lambda),$$

the determinant of the matrix of  $B_{\beta}(\lambda)$  in some bases of  $U(\mathfrak{n}_{+})[\beta]$ ,  $U(\mathfrak{n}_{-})[-\beta]$ . This is a (non-homogeneous) polynomial in  $\lambda$  well defined up to scaling.

Show that the leading term of  $D_{\beta}$  is

$$D_{\beta}^{0}(\lambda) = \operatorname{const} \cdot \prod_{\alpha \in R_{+}} (\lambda, \alpha^{\vee})^{\sum_{n \geq 1} K(\beta - n\alpha)}.$$

(Hint: show that the leading term comes from the product of the diagonal entries of the matrix of the Shapovalov pairing in the PBW bases).

(v) Show that

$$D_{\beta}(\lambda) = \text{const} \cdot \prod_{\alpha \in Q_{+} \setminus 0} ((\lambda + \rho, \alpha^{\vee}) - 1)^{m_{\alpha}}$$

for some nonnegative integers  $m_{\alpha} = m_{\alpha}(\beta)$ . Then use (iv) to show that moreover  $m_{\alpha} = 0$  unless  $\alpha$  is a multiple of a positive root.

- (vi) Let V, U be finite-dimensional vector spaces over a field k of dimension n and  $B(t): V \times U \to k[[t]]$  be a bilinear form. Denote by  $V_0 \subset V, U_0 \subset U$  the left and right kernels of B(0). Suppose that B'(0) is a perfect pairing  $V_0 \times U_0 \to k$ . Show that the vanishing order of  $\det B(t)$  at t = 0 (computed with respect to any bases of V, U) equals  $\dim V_0 = \dim U_0$ . (Hint: Pick a basis  $e_1, ..., e_m$  of  $V_0$ , complete it to a basis  $e_1, ..., e_n$  of V. Choose vectors  $f_{m+1}, ..., f_n \in U$  such that  $B(0)(e_i, f_j) = \delta_{ij}$  for  $m < i, j \leq n$ . Let  $f_1, ..., f_m$  be the basis  $U_0$  dual to  $e_1, ..., e_m$  with respect to B'(0). Show that  $\{f_i\}$  is a basis of U and the determinant of B(t) in the bases  $\{e_i\}$ ,  $\{f_i\}$  equals  $t^m + O(t^{m+1})$ .)
- (vii) Show that if  $\lambda$  is generic on the hyperplane  $(\lambda + \rho, \alpha^{\vee}) = n$  for  $n \in \mathbb{Z}_{>0}$  and  $\alpha \in R_+$  and  $m_{n\alpha}(\beta) > 0$  then  $M_{\lambda}$  contains an irreducible submodule  $M_{\lambda-n\alpha}$  and the quotient  $M_{\lambda}/M_{\lambda-n\alpha}$  is irreducible. (Use Casimir eigenvalues to show that the only irreducible modules which could occur in the composition series of  $M_{\lambda}$  are  $L_{\lambda}$  and  $L_{\lambda-n\alpha}$  and apply Exercise 8.14).
- (viii) Let  $\lambda$  be as in (vii) and let  $B(\beta, t) := B_{\beta}(\lambda + t\alpha)$ . Show that  $B(\beta, t)$  satisfies the assumption of (vi) for all  $\beta$ .

**Hint:** Use that  $\bigoplus_{\beta} \operatorname{Ker} B(\beta,0)$  is naturally identified with  $M_{\lambda-n\alpha}$  and  $B'(\beta,0)$  restricts on it to a multiple of its Shapovalov form, and show that one has  $B'_{n\alpha}(0)(v_{\lambda-n\alpha},v_{\lambda-n\alpha})\neq 0$ . For the latter, assume the contrary and show that there exists a homogeneous lift u of  $v_{\lambda-n\alpha}$  modulo  $t^2$  such that  $B_{n\alpha}(t)(u,w)=0$  modulo  $t^2$  for all w of weight  $\lambda+(t-n)\alpha$ . Deduce that  $e_iu$  vanishes modulo  $t^2$  for all i. Conclude that

$$Cu = ((\lambda + (t - n)\alpha + \rho)^2 - \rho^2)u + O(t^2)$$

and derive a contradiction with

$$Cu = ((\lambda + t\alpha + \rho)^2 - \rho^2)u.$$

- (ix) Deduce that  $m_{n\alpha}(\beta) = K(\beta n\alpha)$ ; in particular, in general  $m_{n\alpha}(\beta) \leq K(\beta n\alpha)$ .
  - (x) Prove the **Shapovalov determinant formula**:

$$D_{\beta}(\lambda) = \prod_{\alpha \in R_{+}} \prod_{n \ge 1} ((\lambda + \rho, \alpha^{\vee}) - n)^{K(\beta - n\alpha)}$$

up to scaling.

(xi) Determine all  $\lambda \in \mathfrak{h}^*$  for which  $M_{\lambda}$  is irreducible.

#### 9. Representations of $SL_2(\mathbb{R})$

9.1. Irreducible  $(\mathfrak{g}, K)$ -modules for  $SL_2(\mathbb{R})$ . Let us now apply the general theory to the simplest example – representations of the group  $G = SL_2(\mathbb{R})$  of real 2 by 2 matrices with determinant 1. Note that  $SL_2(\mathbb{R}) \cong SU(1,1)$ , and in this realization the maximal compact subgroup SO(2) becomes U(1). So we have  $\text{Lie}(G) = \mathfrak{g} = \mathfrak{su}(1,1)$ , hence  $\mathfrak{g}_{\mathbb{C}} = \mathfrak{sl}_2(\mathbb{C})$  with standard basis e, f, h, so that a maximal compact subgroup K of G consists of elements  $e^{ith}$ ,  $t \in [0, 2\pi)$ . Thus a  $(\mathfrak{g}, K)$ -module is the same thing as a  $\mathfrak{g}_{\mathbb{C}}$ -module with a weight decomposition and integer weights.

Let us classify irreducible  $(\mathfrak{g}, K)$ -modules M. To this end, recall that we have the central Casimir element  $C \in U(\mathfrak{g}_{\mathbb{C}})$  given by

$$C = fe + \frac{(h+1)^2}{4},$$

and note that by the PBW theorem,  $U(\mathfrak{g}_{\mathbb{C}})$  is free as a right module over the commutative subalgebra  $\mathbb{C}[h,fe]=\mathbb{C}[h,C]$  with basis  $1,f^n,e^n,n\geq 1$ . Thus if v is a nonzero weight vector of M then M is spanned by  $v,f^nv,e^nv$ . It follows that weight subspaces of M are 1-dimensional, and P(M) is an arithmetic progression with step 2. Thus we have four cases:

- 1. P(M) is finite. Then  $M = L_m$ , the m+1-dimensional irreducible representation.
- **2.** P(M) is infinite, bounded above. In this case let v have the maximal weight m. Then  $f^nv$ ,  $n \geq 0$  is a basis of M, and we have hv = mv, ev = 0. Thus  $M = M_m$  is the Verma module with highest weight  $m \in \mathbb{Z}$ . This module is irreducible iff m < 0 (Exercise 8.11). Thus in this case we get modules  $M_{-m} = M_{-m}^+, m \geq 1$ .
- **3.** P(M) is infinite, bounded below. The situation is completely parallel (with f replaced by e) and we obtain lowest weight Verma modules  $M_m^-$  for  $m \geq 1$ . The  $(\mathfrak{g}, K)$ -modules  $M_m^-, M_{-m}^+$  are called the **discrete series modules** for  $m \geq 2$ , and **limit of discrete series** for m = 1.
- **4.** P(M) is unbounded on both sides. Let c be the scalar by which C acts on M. We have two cases the even case  $P(M) = 2\mathbb{Z}$  and the odd case  $P(M) = 2\mathbb{Z} + 1$ . In both cases we have a basis  $v_n$ ,  $n \in P(M)$  such that

(4) 
$$hv_n = nv_n, \ fv_n = v_{n-2}, \ ev_n = \Lambda_n v_{n+2},$$

where  $\Lambda_n \neq 0$ . To compute  $\Lambda_n$ , we write

$$\Lambda_n v_n = fev_n = \left(C - \frac{(h+1)^2}{\frac{4}{48}}\right) v_n = \left(c - \frac{(n+1)^2}{4}\right) v_n.$$

Thus

$$\Lambda_n = c - \frac{(n+1)^2}{4}.$$

Let  $c = \frac{s^2}{4}$ . Then

(5) 
$$\Lambda_n = \frac{1}{4}(s-1-n)(s+1+n).$$

Thus we can replace  $v_n$  by its multiple  $w_n$  so that

$$hw_n = nw_n$$
,  $fw_n = \frac{1}{2}(s-1+n)w_{n-2}$ ,  $ew_n = \frac{1}{2}(s-1-n)w_{n+2}$ .

These formulas define  $\mathfrak{g}_{\mathbb{C}}$ -modules for any  $s \in \mathbb{C}$ . We will denote these modules by  $P_{\pm}(s)$  (plus for the even case, minus for the odd case). The  $(\mathfrak{g}, K)$ -modules  $P_{\pm}(s)$  are called the **principal series modules**. We see that  $P_{+}(s)$  is irreducible if  $s \notin 2\mathbb{Z} + 1$  and  $P_{-}(s)$  is irreducible iff  $s \notin 2\mathbb{Z}$ , and  $P_{\pm}(s) = P_{\pm}(-s)$  in this case.

Moreover, when these conditions fail, we have short exact sequences

$$0 \to L_{2m} \to P_+(2m+1) \to M_{-2m-2}^+ \oplus M_{2m+2}^- \to 0, \ m \in \mathbb{Z}_{\geq 0},$$

$$0 \to M_{-2m-2}^+ \oplus M_{2m+2}^- \to P_+(-2m-1) \to L_{2m} \to 0, \ m \in \mathbb{Z}_{\geq 0},$$

$$0 \to L_{2m+1} \to P_{-}(2m+2) \to M_{-2m-3}^{+} \oplus M_{2m+3}^{-} \to 0, \ m \in \mathbb{Z}_{\geq 0},$$

$$0 \to M_{-2m-3}^+ \oplus M_{2m+3}^- \to P_-(-2m-2) \to L_{2m+1} \to 0, \ m \in \mathbb{Z}_{\geq 0},$$

and for s = 0 we have an isomorphism

$$P_{-}(0) \cong M_{-1}^{+} \oplus M_{1}^{-}.$$

All these modules except  $P_{-}(0)$  are indecomposable. Thus we see that  $P_{\pm}(s) \ncong P_{\pm}(-s)$  when it is reducible and  $s \neq 0$ .

As a result, we get

**Proposition 9.1.** The simple  $(\mathfrak{g}, K)$ -modules (or equivalently, Harish-Chandra modules) are  $L_m, m \in \mathbb{Z}_{\geq 0}, M_m^-, M_{-m}^+, m \in \mathbb{Z}_{\geq 1},$  and  $P_+(s), s \notin 2\mathbb{Z} + 1, P_-(s), s \notin 2\mathbb{Z},$  with the only isomorphisms  $P_{\pm}(s) \cong P_{\pm}(-s)$ .

**Exercise 9.2.** Let  $\widetilde{P}_{+}(s)$ ,  $\widetilde{P}_{-}(s)$  be the modules defined by (4),(5); so they are isomorphic to  $P_{+}(s)$ ,  $P_{-}(s)$  when s is not an odd integer, respectively not a nonzero even integer. But we will consider  $\widetilde{P}_{+}(s)$  when s = 2k + 1 and  $\widetilde{P}_{-}(s)$  when s = 2k,  $k \neq 0$  (where k is an integer).

- (i) Compute the Jordan-Hölder series of  $\widetilde{P}_{+}(s)$ ,  $\widetilde{P}_{-}(s)$  and show that they are uniserial, i.e., have a unique filtration with irreducible successive quotients.
  - (ii) Do there exist isomorphisms  $\widetilde{P}_+(s)\cong P_+(s),\ \widetilde{P}_-(s)\cong P_-(s)$ ?

9.2. **Realizations.** Let us discuss realizations of these representations by admissible representations of G. For  $L_m$  there is nothing to discuss, so we'll focus on principal series and discrete series.

The realization of principal series has already been discussed in Example 5.3. Namely, let  $B \subset G$  be the subgroup of upper triangular matrices b with diagonal entries  $(t(b), t(b)^{-1})$ . As before we consider the spaces

$$\mathbb{V}_{+}(s) = \{ F \in C^{\infty}(G) : F(gb) = F(g)|t(b)|^{s-1} \},$$

$$\mathbb{V}_{-}(s) = \{ F \in C^{\infty}(G) : F(gb) = F(g)|t(b)|^{s-1} \operatorname{sign}(t(b)) \}.$$

These are admissible representations of G acting by left multiplication. Let us compute  $\mathbb{V}_{\pm}(s)^{\text{fin}}$ . To this end, note that the group  $K = U(1) = S^1$  acts transitively on G/B with stabilizer  $\mathbb{Z}/2 = \{\pm 1\}$ . Thus, pulling the function F back to K, we can realize  $\mathbb{V}_{\pm}(s)$  as the space  $\mathbb{V}_{\pm}$  of functions  $F \in C^{\infty}(S^1)$  such  $F(-z) = \pm F(z)$ .

A more geometric way of thinking about this is the following. Given a Lie group G and a closed subgroup B with Lie algebras  $\mathfrak{g}, \mathfrak{b}$ , every finite-dimensional representation V of B gives rise to a vector bundle  $E_V := (G \times V)/B$  over G/B, where the action of B on  $G \times V$  is given by  $(g,v)b = (gb,b^{-1}v)$ . For example, the tangent bundle T(G/B) is obtained from the representation  $V = \mathfrak{g}/\mathfrak{b}$ . In our example,  $\mathfrak{g}/\mathfrak{b}$  is the 1-dimensional representation of B given by  $b \mapsto t(b)^{-2}$ . Thus sections of the tangent bundle on G/B (i.e., vector fields) can be interpreted as functions F on G such that

$$F(gb) = F(g)t(b)^2.$$

It follows that elements of  $\mathbb{V}_+(s)$  can be interpreted as sections of the bundle  $K^{\frac{1-s}{2}}$  where  $K=T^*(G/B)$  is the canonical bundle, which coincides with the cotangent bundle since  $\dim(G/B)=1$  (this bundle is trivial topologically but the action of diffeomorphisms of  $G/B=S^1$ , in particular, of elements of  $SL_2(\mathbb{R})$  on its sections depends on s). In other words, elements of  $\mathbb{V}_+(s)$  can be interpreted as "tensor fields of non-integer rank":  $\phi(u)(d \operatorname{arg} u)^{\frac{1-s}{2}}$ , where  $u=e^{i\theta}$ ,  $\theta$  is the angle coordinate on  $G/B=\mathbb{RP}^1$  and  $\phi$  is a smooth function. Similarly, elements of  $\mathbb{V}_-(s)$  can be interpreted as expressions  $u^{\frac{1}{2}}\phi(u)(d \operatorname{arg} u)^{\frac{1-s}{2}}$ , i.e., two-valued smooth sections of the same bundle which change sign when one goes around the circle. Thus the Lie algebra action on these modules is by the vector fields

$$h = 2u\partial_u, \ f = \partial_u, \ e = -u^2\partial_u,$$

but they act on elements of  $\mathbb{V}_{\pm}(s)$  not as on functions but as on tensor fields. Thus  $\mathbb{V}_{\pm}(s)^{\text{fin}} \subset \mathbb{V}_{\pm}(s)$  is the subspace of vectors such that

 $\phi \in \mathbb{C}[u,u^{-1}]$ . Taking the basis  $w_{2k}=u^k(d \operatorname{arg} u)^{\frac{1-s}{2}}$  in the even case and  $w_{2k+1} = u^{k+\frac{1}{2}} (d \operatorname{arg} u)^{\frac{1-s}{2}}$  in the odd case, we have

$$hw_n = nw_n$$
,  $fw_n = \frac{1}{2}(s-1+n)w_{n-2}$ ,  $ew_n = \frac{1}{2}(s-1-n)w_{n+2}$ .

Thus we get that  $\mathbb{V}_{\pm}(s)^{\text{fin}} \cong P_{\pm}(s)$  for all  $s \in \mathbb{C}$ .

In particular, at points where  $P_{\pm}(s)$  are reducible, this gives realizations of the discrete series. Namely, consider the modules  $\mathbb{V}_{+}(-r)$  for odd  $r \geq 1$  and  $\mathbb{V}_{-}(-r)$  for even  $r \geq 1$ . The space  $\mathbb{V}_{+}(-r)$  consists of elements  $\phi(u)(\frac{du}{iu})^{\frac{1+r}{2}}$  where  $\phi$  is smooth (note that  $d \arg u = \frac{du}{iu}$ ). So it has the subrepresentation  $\mathbb{V}^0_+(-r)$  of forms that extend holomorphically to the disk  $|u| \leq 1$ . Thus means that  $\phi(u) = \sum_{N \geq 0} a_N u^{N + \frac{1+r}{2}}$ , where  $a_N$  is a rapidly decaying sequence (faster than any power of N). In other words,  $\mathbb{V}^0_+(-r)$  consists of elements  $\psi(u)(du)^{\frac{1+r}{2}}$ , where  $\psi$  is smooth on the disk  $|u| \leq 1$  and holomorphic for |u| < 1. Thus the eigenvalues of h on  $\mathbb{V}_{+}^{0}(-r)$  are 1+r+2N, hence  $\mathbb{V}_{+}^{0}(-r)^{\text{fin}}=M_{r+1}^{-}$ .

Also,  $\mathbb{V}_{+}(-r)$  has a subrepresentation  $\mathbb{V}_{+}^{\infty}(-r)$  of forms that extend holomorphically to  $|u| \geq 1$  (including infinity), which means that  $\phi(u) = \sum_{N>0} a_N u^{-N-\frac{1+r}{2}}$ . In other words,  $\mathbb{V}_+^{\infty}(-r)$  consists of elements  $\psi(u^{-1})(du^{-1})^{\frac{1+r}{2}}$ , where  $\psi$  is smooth on the disk  $|u| \leq 1$  and holomorphic for |u| < 1. Thus we get  $\mathbb{V}_+^{\infty}(-r)^{\text{fin}} = M_{-r-1}^+$ . Similarly, for even r we get  $\mathbb{V}_-^0(-r)^{\text{fin}} = M_{r+1}^-$ ,  $\mathbb{V}_-^{\infty}(-r)^{\text{fin}} = M_{-r-1}^+$ .

9.3. Unitary representations. These Fréchet space realizations can easily be made Hilbert space realizations, by completing with respect to the usual  $L^2$ -norm given by

$$\|\phi\|^2 = \frac{1}{2\pi} \int_0^{2\pi} |\phi(e^{i\theta})|^2 d\theta.$$

However, this norm is only preserved by G when s is imaginary. In this case we obtain that the completed representations  $\widehat{\mathbb{V}}_{+}(s)$ , in particular  $\widehat{\mathbb{V}}_{-}^{0}(0), \widehat{\mathbb{V}}_{-}^{\infty}(0),$  are unitary. It follows that the Harish-Chandra modules  $P_{\pm}(s)$  for  $s \in i\mathbb{R}$  and  $M_1^-, M_{-1}^+$  are unitary.

It turns out, however, that there are other irreducible unitary representations. Let us classify them. It suffices to classify irreducible unitary Harish-Chandra modules. Note that the relevant anti-involution on  $\mathfrak{g}$  is given by  $e^{\dagger} = -f$ ,  $f^{\dagger} = -e$ ,  $h^{\dagger} = h$ . Let M be irreducible and  $v \in M$  a vector of weight n. Then if (, ) is an invariant Hermitian form on M then

$$(ev, ev) = -(fev, v) = ((\frac{n+1}{2})^2 - c)(v, v),$$

where c is a Casimir eigenvalue on M. We see that a nonzero invariant Hermitian form exists iff  $c = \frac{s^2}{4} \in \mathbb{R}$ , and such a form can be chosen positive definite iff  $c < (\frac{n+1}{2})^2$  for every  $n \in P(M)$ . This shows that all discrete series representations are unitary and also determines the unitarity range of s for the principal series representations. Thus we obtain the following theorem.

**Theorem 9.3.** (Gelfand-Naimark [GN], Bargmann [Ba]). The irreducible unitary representations of  $SL_2(\mathbb{R})$  are Hilbert space completions of the following unitary Harish-Chandra modules:

- Discrete series and limit of discrete series  $M_m^-, M_{-m}^+, m \in \mathbb{Z}_{\geq 1}$ ;
- Unitary principal series  $P_{\pm}(s)$ ,  $s \in i\mathbb{R}$ ,  $s \neq 0$ ;
- The complementary series  $P_+(s)$ ,  $s \in \mathbb{R}$ , 0 < |s| < 1;
- The trivial representation  $\mathbb{C}$ .

Here  $P_{\pm}(s) \cong P_{\pm}(-s)$  and there are no other isomorphisms.

Let us discuss explicit Hilbert space realizations of the unitary representations. We have already described such unitary realizations of principal series in  $L^2(S^1)$ , except the complementary series. For discrete series we only gave realizations for m=1, as  $M_1^-, M_{-1}^+$  are direct summands in  $P_-(0)$ . However, one can give a realization for any m. To this end, note that  $G=SL_2(\mathbb{R})$  acts by fractional linear transformations on the disk  $|u| \leq 1$ . Moreover, we have the Poincaré (hyperbolic) metric on the disk which is G-invariant. The volume element for this metric looks like

$$\mu = \frac{dud\overline{u}}{(1 - |u|^2)^2}.$$

Thus for expressions  $\omega = \psi(u)(du)^{\frac{m}{2}}$  where  $m \geq 2$  is an integer and  $\psi(u)$  is holomorphic for |u| < 1 we may define the G-invariant norm

$$\|\omega\|^2 = \int_{|u|<1} \frac{\omega \overline{\omega}}{\mu^{\frac{m}{2}-1}} = \int_{|u|<1} |\psi(u)|^2 (1-|u|^2)^{m-2} du d\overline{u}.$$

Hence the Hilbert space completion  $\widehat{M}_m^-$  may be realized as the space  $H_m$  of holomorphic  $\frac{m}{2}$ -forms  $\omega = \psi(u)(du)^{\frac{m}{2}}$  for |u| < 1 for which  $\|\omega\|^2 < \infty$  (note that this space is nonzero only if  $m \geq 2$ ).

Likewise,  $\widehat{M}_{-m}^+$  can be similarly realized via antiholomorphic forms. Indeed, conjugation by the matrix  $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$  (of determinant -1) defines an outer automorphism of  $SL_2(\mathbb{R})$  which is induced by complex conjugation on the unit disk, and this automorphism exchanges  $M_m^-$  with  $M_{-m}^+$ .

**Exercise 9.4.** Let  $G_{\ell}$  be the  $\ell$ -fold cover of  $PSL_2(\mathbb{R})$  (for example,  $G_1 = PSL_2(\mathbb{R})$ ,  $G_2 = SL_2(\mathbb{R})$ ). Classify irreducible admissible representations (up to infinitesimal equivalence) and irreducible unitary representations of  $G_{\ell}$  for all  $\ell$ .

**Hint.** The maximal compact subgroup of  $G_{\ell}$  is  $K_{\ell}$ , the  $\ell$ -fold cover of PSO(2). Thus irreducible Harish-Chandra modules for  $G_{\ell}$  are irreducible  $\mathfrak{sl}_2(\mathbb{C})$ -modules on which the element h acts diagonalizably with eigenvalues in  $\frac{2}{\ell}\mathbb{Z}$ .

**Exercise 9.5.** Compute the matrix coefficients of the principal series modules,  $\psi_{m,n}(g) = (w_m, gw_n), g \in SL_2(\mathbb{R}).$ 

**Hint.** Write g as  $g = U_1DU_2$  where

$$U_k = \exp(i\theta_k h) \in SO(2), \ \theta_k \in \mathbb{R}/2\pi\mathbb{Z}$$

for k=1,2 and  $D=\operatorname{diag}(a,a^{-1})$  is diagonal, and express  $\psi_{m,n}(g)$  as  $e^{i(n\theta_2-m\theta_1)}\psi(m,n,a,s)$ . Write the function  $\psi(m,n,a,s)$  in terms of the Gauss hypergeometric function  ${}_2F_1$ .

**Exercise 9.6.** (i) Show that for -1 < s < 0 the formula

$$(f,g)_s := \int_{\mathbb{R}^2} f(y)\overline{g(z)}|y-z|^{-s-1}dydz$$

defines a positive definite inner product on the space  $C_0(\mathbb{R})$  of continuous functions  $f: \mathbb{R} \to \mathbb{C}$  with compact support (*Hint*: pass to Fourier transforms).

(ii) Deduce that if f is a measurable function on  $\mathbb{R}$  then

$$0 \le (f, f)_s \le \infty,$$

so measurable functions f with  $(f, f)_s < \infty$  modulo those for which  $(f, f)_s = 0$  form a Hilbert space  $\mathcal{H}_s$  with inner product  $(,)_s$ , which is the completion of  $C_0(\mathbb{R})$  under  $(,)_s$ .

(iii) Let us view  $\mathcal{H}_s$  as the space of tensor fields  $f(y)(dy)^{\frac{1-s}{2}}$ , where f is as in (ii). Show that the complementary series unitary representation  $\widehat{P}_+(s)$  of  $SL_2(\mathbb{R})$  may be realized in  $\mathcal{H}_s$  with G acting naturally on such tensor fields. (*Hint:* show that the differential form  $\frac{dydz}{(y-z)^2}$  is invariant under simultaneous Möbius transformations of y, z by the same matrix).

### 10. Chevalley restriction theorem and Chevalley-Shephard-Todd theorem

10.1. Chevalley restriction theorem. Let  $\mathfrak{g}$  be a semisimple complex Lie algebra with Cartan subalgebra  $\mathfrak{h}$ , and let W be the corresponding Weyl group. Given  $F \in \mathbb{C}[\mathfrak{g}]^{\mathfrak{g}}$ , let  $\mathrm{Res}(F)$  be its restriction to  $\mathfrak{h}$ .

**Theorem 10.1.** (Chevalley restriction theorem) (i)  $\operatorname{Res}(F) \in \mathbb{C}[\mathfrak{h}]^W$ . (ii) The map  $\operatorname{Res}: \mathbb{C}[\mathfrak{g}]^{\mathfrak{g}} \to \mathbb{C}[\mathfrak{h}]^W$  is a graded algebra isomorpohism.

*Proof.* (i) Let G be the adjoint complex Lie group corresponding to  $\mathfrak{g}$ . Then  $\mathbb{C}[\mathfrak{g}]^{\mathfrak{g}} = \mathbb{C}[\mathfrak{g}]^G$ , so F is G-invariant. Thus, denoting by H the maximal torus in G with Lie $H = \mathfrak{h}$ , we see that the normalizer N(H) preserves  $\mathrm{Res}(F)$ . Since H acts trivially on  $\mathfrak{h}$ , we get that W = N(H)/H preserves  $\mathrm{Res}(F)$ , as desired.

(ii) It is clear that Res is a graded algebra homomorphism, so we just need to show that it is bijective. The injectivity of this map follows immediately from the fact that Res(F) determines the values of F on the subset of semisimple elements  $\mathfrak{g}_s \subset \mathfrak{g}$ , and this subset is dense in  $\mathfrak{g}$ .

It remains to prove the surjectivity of Res. Consider the functions

$$F_{\lambda,n}(x) := \operatorname{Tr}_{L_{\lambda}}(x^n) = \chi_{\lambda}(x^n), \ x \in \mathfrak{g}$$

in  $\mathbb{C}[\mathfrak{g}]^{\mathfrak{g}}$ , where  $\chi_{\lambda}$  is the character of  $L_{\lambda}$ . We'll show that the functions  $\operatorname{Res}(F_{\lambda,n})$  for various  $\lambda$  span  $\mathbb{C}[\mathfrak{h}]^W[n] = (S^n\mathfrak{h}^*)^W$  for each n, which implies that Res is surjective.

To this end, for every dominant integral weight  $\lambda \in P_+$  let  $m_\lambda$  be the orbit sum

$$m_{\lambda} := \sum_{\mu \in W\lambda} e^{\mu} \in \mathbb{C}[P]^{W}.$$

We have

$$\chi_{\lambda} = \sum_{\mu \le \lambda} N_{\lambda\mu} m_{\mu},$$

where  $\mu \leq \lambda$  means that  $\lambda - \mu$  is a (possibly empty) sum of positive roots, and  $N_{\lambda\mu}$  is the matrix of weight multiplicities (in particular,  $N_{\lambda\lambda} = 1$ ). This matrix is triangular with ones on the diagonal, so we can invert it and get

(6) 
$$m_{\lambda} = \sum_{\mu \leq \lambda} \widetilde{N}_{\lambda\mu} \chi_{\mu}$$

for some integers  $\widetilde{N}_{\lambda\mu}$ . Now, for  $h \in \mathfrak{h}$ , let

$$M_{\lambda,n}(h) := \sum_{\mu \in W\lambda} \mu(h)^n = \frac{|W\lambda|}{|W|} \sum_{w \in W} \lambda(wh)^n.$$

(note that  $\mu(x)^n = \mu(x^n)$ ). By (6) we have

$$M_{\lambda,n}(h) = \sum_{\mu \le \lambda} \widetilde{N}_{\lambda\mu} F_{\mu,n}(h).$$

Thus it suffices to show that  $M_{\lambda,n}(h)$  for various  $\lambda$  span  $(S^n\mathfrak{h}^*)^W[n]$  for each n. Since averaging over W is a surjection  $S^n\mathfrak{h}^* \to (S^n\mathfrak{h}^*)^W$ , it suffices to show that the functions  $\lambda^n$  for  $\lambda \in P_+$  span  $S^n\mathfrak{h}^*$ .

Denote the span of these functions by Y. Since  $P_+$  is Zariski dense in  $\mathfrak{h}^*$ , we find that  $\lambda^n \in Y$  for all  $\lambda \in \mathfrak{h}^*$ . Thus  $Y \subset S^n\mathfrak{h}^*$  is a subrepresentation of  $GL(\mathfrak{h}^*)$ . But  $S^n\mathfrak{h}^*$  is an irreducible representation of  $GL(\mathfrak{h}^*)$ , hence  $Y = S^n\mathfrak{h}^*$ . This completes the proof of (ii).

**Remark 10.2.** 1. Since the Killing form allows us to identify  $\mathfrak{g} \cong \mathfrak{g}^*$  and  $\mathfrak{h} \cong \mathfrak{h}^*$ , the Chevalley restriction theorem is equivalent to the statement that the restriction map  $\operatorname{Res} : \mathbb{C}[\mathfrak{g}^*]^{\mathfrak{g}} = (S\mathfrak{g})^{\mathfrak{g}} \to \mathbb{C}[\mathfrak{h}^*]^W = (S\mathfrak{h})^W$  is a graded algebra isomorphism.

2. The Chevalley restriction theorem trivially generalizes to reductive Lie algebras.

**Example 10.3.** Let  $\mathfrak{g} = \mathfrak{gl}_n(\mathbb{C})$ . Then by the fundamental theorem on symmetric functions,  $\mathbb{C}[\mathfrak{h}]^W = \mathbb{C}[x_1,...,x_n]^{S_n} = \mathbb{C}[e_1,...,e_n]$  where

$$e_i(x_1, ..., x_n) = \sum_{k_1 < ... < k_i} x_{k_1} ... x_{k_i}$$

are elementary symmetric functions. The Chevalley restriction theorem thus says that restriction defines an isomorphism between the algebra  $\mathbb{C}[\mathfrak{g}]^{\mathfrak{g}}$  of conjugation-invariant polynomials of a single matrix A and  $\mathbb{C}[e_1,...,e_n]$ . Namely, let  $a_i := \operatorname{Tr}(\wedge^i A)$  be the coefficients of the characteristic polynomial of A (up to sign). Then  $\mathbb{C}[\mathfrak{g}]^{\mathfrak{g}} = \mathbb{C}[a_1,...,a_n]$  and  $a_i|_{\mathfrak{h}} = e_i(x_1,...,x_n)$ . Another set of generators are  $b_i := \operatorname{Tr}(A^i)$ ,  $1 \le i \le n$ ; we have  $b_i|_{\mathfrak{h}} = p_i(x_1,...,x_n)$ , where

$$p_i(x_1, ..., x_n) := \sum_{k=1}^n x_k^i$$

are the power sums, another set of generators of the algebra of symmetric functions. Yet another generating set is  $c_i := \text{Tr}(S^i A)$  which restrict to complete symmetric functions

$$h_i(x_1, ..., x_n) = \sum_{k_1 \le ... \le k_i} x_{k_1} ... x_{k_i}.$$

Thus

$$a_i(A) = e_i(x_1, ..., x_n), b_i(A) = p_i(x_1, ..., x_n), c_i(A) = h_i(x_1, ..., x_n),$$

where  $x_1, ..., x_n$  are the eigenvalues of A. Note that  $a_1(A) = b_1(A) = c_1(A) = \text{Tr}(A)$  and  $a_n(A) = \det A$ .

For  $\mathfrak{g} = \mathfrak{sl}_n$  (type  $A_{n-1}$ ), the story is the same, except that  $e_1 = p_1 = h_1 = 0$  and  $a_1 = b_1 = c_1 = 0$ , so they should be removed.

**Example 10.4.** Similarly, for  $\mathfrak{g} = \mathfrak{so}_{2n+1}(\mathbb{C})$  and  $\mathfrak{g} = \mathfrak{sp}_{2n}(\mathbb{C})$  (types  $B_n$  and  $C_n$ ) we have

$$\mathbb{C}[\mathfrak{h}]^W = \mathbb{C}[x_1, ..., x_n]^{S_n \ltimes (\mathbb{Z}/2)^n} =$$

 $\mathbb{C}[x_1^2,...,x_n^2]^{S_n}=\mathbb{C}[e_2,e_4,...,e_{2n}]=\mathbb{C}[p_2,p_4,...,p_{2n}]=C[h_2,h_4,...,h_{2n}],$  where  $e_k,p_k,h_k$  are symmetric functions of 2n variables evaluated at the point  $(x_1,...,x_n,-x_n,...,-x_1)$ , and  $e_{2i}=a_{2i}|_{\mathfrak{h}},\ p_{2i}=b_{2i}|_{\mathfrak{h}},\ h_{2i}=c_{2i}|_{\mathfrak{h}}$  (note that the odd-indexed symmetric functions evaluate to 0). This is so because the eigenvalues of A are  $x_1,...,x_n,-x_n,...,-x_1$ , and also 0 in the orthogonal case.

The case  $\mathfrak{g} = \mathfrak{so}_{2n}(\mathbb{C})$  (type  $D_n$ ) is a bit trickier. In this case the Weyl group is  $W = S_n \ltimes (\mathbb{Z}/2)_+^n$ , where  $(\mathbb{Z}/2)_+^n$  is the group of binary n-dimensional vectors with zero sum of coordinates. Thus it is easy to check that

$$\mathbb{C}[\mathfrak{h}]^W = \mathbb{C}[e_2, ..., e_{2n-2}, \sqrt{e_{2n}}].$$

where  $e_j = e_j(x_1, ..., x_n, -x_n, ..., -x_1)$ . The polynomial  $\sqrt{e_{2n}} = i^n x_1 ... x_n$  is the restriction of the **Pfaffian** Pf(A) =  $\sqrt{\det A}$ . Thus

$$\mathbb{C}[\mathfrak{g}]^{\mathfrak{g}} = \mathbb{C}[a_2(A), ..., a_{2n-2}(A), \operatorname{Pf}(A)].$$

The generators of  $\mathbb{C}[\mathfrak{g}]^{\mathfrak{g}}$  for exceptional  $\mathfrak{g}$  are less explicit, however.

10.2. Chevalley-Shephard-Todd theorem, part I. In Examples 10.3, 10.4 we observe that the algebras  $\mathbb{C}[\mathfrak{h}]^W$  of Weyl group invariant polynomials for classical groups are free (polynomial) algebras. This is not true for a general finite group: e.g. if  $G = \mathbb{Z}/2$  acting on  $\mathbb{C}^2$  by  $(x,y) \mapsto (-x,-y)$  then the ring of invariants  $\mathbb{C}[x,y]^{\mathbb{Z}/2}$  is  $\mathbb{C}[a,b,c]$  where  $a=x^2,b=xy,c=y^2$ , and it is not free – it has a relation  $ac=b^2$  (and the set of generators is minimal). It turns out, however, that this is true for all Weyl groups and more generally complex reflection groups.

**Definition 10.5.** A diagonalizable automorphism  $g: V \to V$  of a finite-dimensional complex vector space V is called a **complex reflection** if  $\operatorname{rank}(g-1) = 1$ ; in other words, in some basis  $g = \operatorname{diag}(\lambda, 1, ..., 1)$  where  $\lambda \neq 0, 1$ . A **complex reflection group** is a finite subgroup  $G \subset GL(V)$  generated by complex reflections.

For example, the Weyl group  $W \subset GL(\mathfrak{h})$  of a semisimple Lie algebra  $\mathfrak{g}$  and, more generally, a finite Coxeter group is a complex reflection group, but there are others, e.g.  $S_n \ltimes (\mathbb{Z}/m)^n$  acting on  $\mathbb{C}^n$  for m > 2,

or, more generally, the subgroup G(m, d, n) in this group consisting of elements for which the sum of  $\mathbb{Z}/m$ -coordinates lies in  $d \cdot \mathbb{Z}/m$  for some divisor d of m.

It is easy to see that any complex reflection group is uniquely a product of irreducible ones, and irreducible complex reflection groups were classified by Shephard and Todd in 1954. Besides symmetric groups  $S_n$  acting on  $\mathbb{C}^{n-1}$  and G(m,d,n) acting on  $\mathbb{C}^n$  (which includes dihedral groups), there are 34 exceptional groups, which include 19 subgroups of  $GL_2$ , 6 exceptional Coxeter groups of rank  $\geq 3$  ( $H_3, H_4, F_4, E_6, E_7, E_8$ ), and 9 other groups.

**Theorem 10.6.** (Chevalley-Shephard-Todd theorem, part I, [Che], [ST]) Let V be a finite-dimensional complex vector space and  $G \subset GL(V)$  be a finite subgroup. Then  $\mathbb{C}[V]^G$  is a polynomial algebra if and only if G is a complex reflection group.

#### 11. Proof of the CST theorem, part I

11.1. Proof of the CST theorem, part I, the "if" direction. We first need a lemma from invariant theory. Let  $G \subset GL(V)$  be a finite subgroup, and  $I \subset \mathbb{C}[V]$  be the ideal generated by positive degree elements of  $\mathbb{C}[V]^G$ . Let  $f_1, ..., f_r \in \mathbb{C}[V]^G$  be homogeneous generators of I (which exist by the Hilbert basis theorem).

**Lemma 11.1.** The algebra  $\mathbb{C}[V]^G$  is generated by  $f_1, ..., f_r$ ; in particular, it is finitely generated.

*Proof.* We need to show that every homogeneous  $f \in \mathbb{C}[V]^G$  is a polynomial of  $f_1, ..., f_r$ . The proof is by induction in  $d = \deg f$ . The base d = 0 is obvious. If d > 0, we have  $f \in I$ , so

$$f = s_1 f_1 + ... + s_r f_r$$

where  $s_i \in \mathbb{C}[V]$  are homogeneous of degrees < d.

For  $h \in \mathbb{C}[V]$  let  $h^* := \frac{1}{|G|} \sum_{g \in G} gh \in \mathbb{C}[V]^G$  be the G-average of h. Then we have

$$f = s_1^* f_1 + \dots + s_r^* f_r.$$

But by the induction assumption,  $s_i^*$  are polynomials of  $f_1, ..., f_r$ , which proves the lemma.

Remark 11.2. Let A be a finitely generated commutative  $\mathbb{C}$ -algebra with an action of a finite group G. Lemma 11.1 implies that the algebra  $A^G$  is also finitely generated (the **Hilbert-Noether lemma**). Indeed, pick generators  $a_1, ..., a_m$  of A and let  $V \subset A$  be the (finite-dimensional) G-submodule generated by them. Then  $A^G$  is a quotient of  $(SV)^G = \mathbb{C}[V^*]^G$ , which is finitely generated by Lemma 11.1.

The next lemma establishes a special property of algebras of invariants of complex reflection groups which will allow us to prove that they are polynomial algebras.

**Lemma 11.3.** Assume that G is a complex reflection group. Let I be as above,  $F_1, ..., F_m \in \mathbb{C}[V]^G$  be homogeneous, and suppose that  $F_1$  does not belong to the ideal in  $\mathbb{C}[V]^G$  generated by  $F_2, ..., F_m$ . Suppose  $g_i \in \mathbb{C}[V]$  for  $1 \leq i \leq m$  are homogeneous and  $\sum_{i=1}^m g_i F_i = 0$ . Then  $g_1 \in I$ .

*Proof.* Let  $J=(F_2,...,F_m)\subset\mathbb{C}[V]$ . We claim that  $F_1\notin J$ . Indeed, if  $F_1=s_2F_2+...+s_mF_m$  then  $F_1=s_2^*F_2+...+s_m^*F_m$ , contradicting our assumption.

We prove the lemma by induction in  $D := \deg g_1$ . If D = 0 then  $g_1 = 0$ , as  $F_1 \notin J$ . This establishes the base of induction.

Now assume D > 0. Let  $\sigma \in G$  be a complex reflection and  $\alpha$  be the linear function on V defining the reflection hyperplane  $V^{\sigma}$  (i.e., the eigenvector of  $\sigma$  in  $V^*$  with eigenvalue  $\neq 1$ ). Then  $\sigma g_i - g_i$  vanishes on  $V^{\sigma}$ , so is divisible by  $\alpha$ . Thus

$$\sigma g_i - g_i = h_i \alpha$$

for some polynomials  $h_i$  with deg  $h_i = \deg g_i - 1$ , in particular deg  $h_1 = D - 1$ . Applying the operator  $\sigma - 1$  to the relation  $\sum_{i=1}^{m} g_i F_i = 0$  and dividing by  $\alpha$ , we obtain

$$\sum_{i=1}^{m} h_i F_i = 0.$$

By the induction assumption  $h_1 \in I$ , so  $\sigma g_1 - g_1 \in I$ . Since W is generated by complex reflections, this implies that  $wg_1 - g_1 \in I$  for any  $w \in G$ . Thus  $g_1^* - g_1 \in I$ . But  $g_1^*$  is a positive degree invariant, so  $g_1^* \in I$ . Hence  $g_1 \in I$ , which justifies the induction step.

Now we are ready to prove the "if" direction of the Chevalley-Shephard-Todd theorem. Suppose that  $f_1, ..., f_r \in \mathbb{C}[V]^G$  are homogenous of positive degree and form a *minimal* set of homogeneous generators of I.

**Lemma 11.4.**  $f_1, ..., f_r$  are algebraically independent.

*Proof.* Assume the contrary, i.e.,

(7) 
$$h(f_1, ..., f_r) = 0,$$

where  $h(y_1, ..., y_r)$  is a nonconstant polynomial. Let  $d_i := \deg f_i$ . We may assume that h is quasi-homogeneous (with  $\deg y_i = d_i$ ), of the lowest possible degree. Let  $x_k$  be linear coordinates on V,  $\partial_k := \frac{\partial}{\partial x_k}$ . Differentiating (7) with respect to  $x_k$  and using the chain rule, we get

(8) 
$$\sum_{j=1}^{r} h_j(\mathbf{f}) \partial_k f_j = 0,$$

where  $\mathbf{f} := (f_1, ..., f_r)$  and  $h_j := \frac{\partial h}{\partial y_j}$ . By renumbering  $f_j$  if needed, we may assume that  $h_1(\mathbf{f}), ..., h_m(\mathbf{f})$  is a minimal generating set of the ideal  $(h_1(\mathbf{f}), ..., h_r(\mathbf{f})) \subset \mathbb{C}[V]$ . Moreover, since h is nonconstant,  $h_j \neq 0$  for some  $j \in [1, r]$ , and since h is of lowest degree, this implies that  $h_j(\mathbf{f}) \neq 0$ . So  $m \geq 1$ . Then for i > m we have

$$h_i(\mathbf{f}) = \sum_{\substack{j=1\\59}}^m g_{ij} h_j(\mathbf{f})$$

for some homogeneous polynomials  $g_{ij} \in \mathbb{C}[V]$  of degree

$$\deg h_i - \deg h_j = d_j - d_i.$$

Substituting this into (8), we get

$$\sum_{j=1}^{m} p_j h_j(\mathbf{f}) = 0,$$

where

$$p_j := \partial_k f_j + \sum_{i=m+1}^r g_{ij} \partial_k f_i.$$

Since  $h_1(\mathbf{f}) \notin (h_2(\mathbf{f}), ..., h_m(\mathbf{f}))$ , by Lemma 11.3 applied to  $F_i = h_i(\mathbf{f})$ ,  $1 \le i \le m$ , we have  $p_1 \in I$ . Thus

$$\partial_k f_1 + \sum_{i=m+1}^r g_{i1} \partial_k f_i = \sum_{i=1}^r q_{ik} f_i,$$

where  $q_{ik} \in \mathbb{C}[V]$  are homogeneous of degree  $d_1 - d_i - 1$ . Let us multiply this equation by  $x_k$  and add over all k. Then we get

(9) 
$$d_1 f_1 + \sum_{i=m+1}^r g_{i1} d_i f_i = \sum_{i=1}^r q_i f_i,$$

where  $q_i := \sum_k x_k q_{ik}$ . In particular,  $q_i$  are homogeneous of strictly positive degree. All terms in this equation are homogeneous of the same degree  $d_1$ , so we must have  $q_1 = 0$ . Thus (9) implies that  $f_1 \in (f_2, ..., f_r)$ , a contradiction with our minimality assumption.

Now, by Lemmas 11.4 and 11.1, we have  $\mathbb{C}[V]^G = \mathbb{C}[f_1, ..., f_r]$ . This proves the "if" direction of the Chevalley-Shephard-Todd theorem.

**Remark 11.5.** Note that  $r = \operatorname{trdeg}(\mathbb{C}(V)^G) = \operatorname{trdeg}(\mathbb{C}(V)) = n$ , where  $n = \dim V$  and trdeg denotes the transcendence degree of a field, since transcendence degree does not change under finite extensions.

#### 11.2. A lemma on group actions.

**Lemma 11.6.** Let U be an affine space over  $\mathbb{C}$  and G a finite group acting on U by polynomial automorphisms.

- (i) Let  $u \in U$  be a point with trivial stabilizer in G. Then there exists a local coordinate system on U near u consisting of elements of  $\mathbb{C}[U]^G$ .
- (ii) Maximal ideals in  $\mathbb{C}[U]^G$  (i.e., characters  $\chi : \mathbb{C}[U]^G \to \mathbb{C}$ ) are in bijection with G-orbits on U, which assigns to an orbit Gu the character  $\chi_u(f) := f(u)$ . Thus the set of maximal ideals in  $\mathbb{C}[U]^G$  is U/G.

- *Proof.* (i) Pick a basis  $\{e_i\}$  of  $T_u^*U$ . Since  $gu \neq u$  for any  $g \in G$ ,  $g \neq 1$ , there exist  $y_i \in \mathbb{C}[U]$ ,  $1 \leq i \leq \dim U$  such that the linear approximation of  $y_i$  at gu is zero for all  $g \neq 1$ ,  $y_i(u) = 0$ , and  $dy_i(u) = e_i$ . Let  $y_i^*$  be the average of  $y_i$  over G. Then  $\{y_i^*\}$  form a required coordinate system.
- (ii) Suppose  $v, u \in U, v \notin Gu$ , then  $Gu \cap Gv = \emptyset$ , so there exists  $f \in \mathbb{C}[U]$  such that  $f|_{Gv} = 0$ ,  $f|_{Gu} = 1$ . Moreover, by replacing f by  $f^*$ , we may choose such  $f \in \mathbb{C}[U]^G$ . Then  $\chi_v(f) = 0$  while  $\chi_u(f) = 1$ , so  $\chi_u \neq \chi_v$ , hence  $u \mapsto \chi_u$  is injective. To show that it's also surjective, take a maximal ideal  $\mathfrak{m} \subset \mathbb{C}[U]^G$ . It generates an ideal  $I \subset \mathbb{C}[U]$  whose projection to  $\mathbb{C}[U]^G$  is  $\mathfrak{m}$ . Thus I is a proper ideal, so by the Nullstellensatz, its zero set  $I \subset U$  is non-empty. Let  $I \in I$  then for any  $I \in \mathbb{C}[U]$  and  $I \in I$  then for  $I \in \mathbb{C}[U]$  where  $I \in I$  is a proper ideal.  $I \in I$  then for any  $I \in \mathbb{C}[U]$  is non-empty. Let  $I \in I$  then for any  $I \in \mathbb{C}[U]$  is non-empty. Let  $I \in I$  then for any  $I \in \mathbb{C}[U]$  is non-empty. Let  $I \in I$  then for any  $I \in \mathbb{C}[U]$  is non-empty. Let  $I \in I$  then for any  $I \in \mathbb{C}[U]$  is non-empty.

### 11.3. Proof of the CST theorem, part I, the "only if" direction.

Let  $G \subset GL(V)$  be a finite subgroup. Let H be the normal subgroup of G generated by the complex reflections of G. Then by the "if" part of the theorem,  $\mathbb{C}[V]^H$  is a polynomial algebra with an action of G/H. In other words, using Lemma 11.6(ii), U := V/H is an affine space with a (possibly non-linear) action of G/H.

Moreover, we claim that G/H acts freely on U outside of a set of codimension  $\geq 2$ . Indeed, if  $1 \neq s \in G/H$  and  $a \in s$  then a is not a reflection, so  $Y_s := \bigcup_{a \in s} V^a$  has codimension  $\geq 2$ . Now, for any v in the preimage of  $U^s$  in V and  $a \in s$  we have  $av = h^{-1}v$  for some  $h \in H$ , thus hav = v and  $v \in Y_s$ . Thus  $U^s$  is contained in the image of  $Y_s$  in U, hence  $\operatorname{codim}(U^s) \geq 2$ , as claimed.

Now assume that  $\mathbb{C}[V]^G$  is a polynomial algebra, and let V/G = W be the corresponding affine space. Consider the natural regular map  $\eta: V/H = U \to V/G = W$  between n-dimensional affine spaces, and let  $J \in \mathbb{C}[U]$  be the Jacobian of this map (well defined up to scaling). If  $u \in U$  and the stabilizer of u in G/H is trivial then by Lemma 11.6,  $\eta$  is étale at u, hence  $J(u) \neq 0$ . But as shown above, the complement of such points has codimension  $\geq 2$ . This implies that J = const, as a nonconstant polynomial would vanish on a subset of codimension 1. Thus by the inverse function theorem  $\eta$  is an isomorphism near 0, in particular bijective, hence H = G.

**Remark 11.7.** Let X be an smooth affine algebraic variety over  $\mathbb{C}$  and G be a finite group of automorphisms of X. Then by the Hilbert-Noether lemma,  $\mathbb{C}[X]^G$  is finitely generated, so  $X/G := \operatorname{Spec}\mathbb{C}[X]^G$  is an affine algebraic variety. The Chevalley-Shephard-Todd theorem

<sup>&</sup>lt;sup>14</sup>This proof uses some very basic algebraic geometry.

implies that X/G is smooth at the image  $x^* \in X/G$  of  $x \in X$  if and only if the stabilizer  $G_x$  of x is a complex reflection group in  $GL(T_xX)$ . In particular, X/G is smooth iff all stabilizers are complex reflection groups. This follows from the **formal Cartan lemma**: any action of a finite group G on a formal polydisk D over a field of characteristic zero is equivalent to its linearization (i.e., to the action of G on the formal neighborhood of 0 in the tangent space to D at its unique geometric point).

#### 12. Chevalley-Shephard-Todd theorem, part II

12.1. Degrees of a complex reflection group. The degrees  $d_i$  of the generators  $f_i$  of  $\mathbb{C}[V]^G$  for a complex reflection group G are uniquely determined up to relabelings (even though  $f_i$  themselves are not). Indeed, recall that for a  $\mathbb{Z}$ -graded vector space M with finite-dimensional homogeneous components its Hilbert series is

$$H(M,q) = \sum_{i \in \mathbb{Z}} \dim M[i]q^i$$

(also called Hilbert polynomial if dim  $M < \infty$ ). Then the Hilbert series of  $\mathbb{C}[V]^G$  is

$$H(\mathbb{C}[V]^G, q) = \frac{1}{\prod_{i=1}^r (1 - q^{d_i})},$$

which uniquely determines  $d_i$ . These numbers are usually arranged in non-decreasing order and are called the **degrees** of G. For instance, for Weyl groups of classical simple Lie algebras we saw in Examples 10.3,10.4 that in type  $A_{n-1}$  the degrees are 2,3,...,n, for  $B_n$  and  $C_n$ they are 2, 4, ..., 2n, and for  $D_n$  they are 2, 4, ..., 2n - 2 and n. In particular, in the last case, if n is even, the degree n occurs twice.

12.2.  $\mathbb{C}[V]$  as a  $\mathbb{C}[V]^G$ -module. Let R be a commutative ring. Let A be a commutative R-algebra with an R-linear action of a finite group G.

**Proposition 12.1.** (Hilbert-Noether theorem) (i) A is integral over  $A^{G}$ . In particular, if A finitely generated then it is module-finite over  $A^{G}$ .

(ii) If R is Noetherian and A is finitely generated then so is  $A^G$ .

*Proof.* (i) We will prove only the first statement, as the second one then follows immediately. For  $a \in A$ , consider the monic polynomial

$$P_a(x) := \prod_{g \in G} (x - ga).$$

It is easy to see that  $P_a \in A^G[x]$  and  $P_a(a) = 0$ , which implies the statement.

(ii) This follows from (i) and the Artin-Tate lemma: If  $B \subset A$  is an R-subalgebra of a finitely generated R-algebra A over a Noetherian ring R and A is module-finite over B then B is finitely generated.<sup>15</sup>

$$x_i = \sum_j b_{ij} y_j, \quad y_i y_j = \sum_k b_{ijk} y_k$$

<sup>&</sup>lt;sup>15</sup>Recall the proof of the Artin-Tate lemma. Let  $x_1,...,x_m$  generate A as an R-algebra and let  $y_1, ..., y_n$  generate A as a B-module. Then we can write

This shows for any finite  $G \subset GL(V)$ , the algebra  $\mathbb{C}[V]$  is module-finite over  $\mathbb{C}[V]^G$ . Note that in (ii) we again proved that  $\mathbb{C}[V]^G$  is finitely generated.

**Theorem 12.2.** (Chevalley-Shephard-Todd theorem, part II, [Che], [ST]) If G is a complex reflection group then for any irreducible representation  $\rho$  of G, the  $\mathbb{C}[V]^G$ -module  $\operatorname{Hom}_G(\rho, \mathbb{C}[V])$  is free of rank  $\dim \rho$ . Thus the G-module  $R_0 = \mathbb{C}[x_1, ..., x_n]/(f_1, ..., f_n)$  is the regular representation and  $\prod_{i=1}^n d_i = |G|$ . Moreover, the Hilbert polynomial  $H(R_0, q) := \sum_{N>0} \dim R_0[N]q^N$  is

$$H(R_0, q) = \prod_{i=1}^{n} [d_i]_q,$$

where 
$$[d]_q := \frac{1-q^d}{1-q} = 1 + q + \dots + q^{d-1}$$
.

Thus we see that the Hilbert polynomial of  $\operatorname{Hom}_G(\rho, R_0)$  is some polynomial  $K_{\rho}(q)$  with nonnegative integer coefficients and  $K_{\rho}(1) = \dim \rho$ . It is called the **Kostka polynomial**. We have

$$\sum_{\rho} K_{\rho}(q) \dim \rho = H(R_0, q) = \prod_{i=1}^{n} [d_i]_q.$$

For example, for  $G = S_3$  and V the reflection representation we have three irreducible representations:  $\mathbb{C}_+$  (trivial),  $\mathbb{C}_-$  (sign) and V. We have  $K_{\mathbb{C}_+}(q) = 1$  and

$$1 + 2K_V(q) + K_{\mathbb{C}_-}(q) = (1+q)(1+q^2) = 1 + 2q + 2q^2 + q^3.$$

It follows that

$$K_V(q) = q + q^2, \ K_{\mathbb{C}_-}(q) = q^3.$$

12.3. **Graded modules.** For the proof of Theorem 12.2 we need to recall some basics from commutative algebra, which we discuss in the next few subsections.

Let k be a field, S a  $\mathbb{Z}_+$ -graded (not necessarily commutative) kalgebra with generators  $f_i$  of positive integer degrees deg  $f_i = d_i$ , M a  $\mathbb{Z}_+$ -graded left S-module, and  $M_0 := M/S_+M$ , where  $S_+ \subset S$  is the
augmentation ideal.

with  $b_{ij}, b_{ijk} \in B$ . Then A is module-finite over the R-algebra  $B_0 \subset B$  generated by  $b_{ij}, b_{ijk}$  (namely, it is generated as a module over  $B_0$  by the  $y_i$ ). Using that R and hence  $B_0$  is Noetherian, we obtain that B is also module-finite over  $B_0$ . Since  $B_0$  is a finitely generated R-algebra, so is B.

**Lemma 12.3.** (i) Any homogeneous lift  $\{v_i^*\}$  of a homogeneous basis  $\{v_i\}$  of  $M_0$  to M is a system of generators for M; in particular, if  $\dim M_0 < \infty$  then M is finitely generated.

(ii) If in addition M is projective, then  $\{v_i^*\}$  is actually a basis of M (in particular, M is free). Thus if dim  $M_0[i] < \infty$  for all i then

$$H(M,q) = H(M_0,q)H(S,q).$$

In particular, if  $S = k[f_1, ..., f_n]$  then

$$H(M,q) = \frac{H(M_0,q)}{\prod_{i=1}^{n} (1 - q^{d_i})}.$$

*Proof.* (i) We prove that any homogeneous element  $u \in M$  is a linear combination of  $v_i^*$  with coefficients in S by induction in  $\deg u$  (with obvious base). Namely, if  $u_0$  is the image of u in  $M_0$  then  $u_0 = \sum_i c_i v_i$  for some  $c_i \in k$  ( $c_i = 0$  unless  $\deg v_i = \deg u$ ), and so

$$u - \sum_{i} c_i v_i^* = \sum_{j} f_j u_j,$$

with  $u_j \in M$ ,  $\deg u_j = \deg u - d_j$ . So by the induction assumption

$$u_j = \sum_i p_{ij} v_i^*$$

for some homogeneous  $p_{ij} \in S$  of degree  $\deg u - d_j - \deg v_i^*$ , and we get

$$u = \sum_{i} p_i v_i^*,$$

where  $p_i := c_i + \sum_j f_j p_{ij}$ .<sup>16</sup>

(ii) Let M' be the free graded S-module with basis  $w_i$  of degrees  $\deg w_i = \deg v_i$ , and  $f: M' \to M$  be the surjection sending  $w_i$  to  $v_i^*$ . Since M is projective, the map

$$f \circ : \operatorname{Hom}(M, M') \to \operatorname{Hom}(M, M)$$

is surjective, so we can pick a homogeneous  $g: M \to M'$  of degree 0 such that  $f \circ g = \mathrm{id}_M$ . Then  $g \circ f: M' \to M'$  is a projection which identifies M' with  $M \oplus \mathrm{Ker} f$  as a graded S-module. But the map  $f_0: M'_0 \to M_0$  induced by f sends the basis  $w_i$  of  $M'_0$  to the basis  $v_i$  of  $M_0$ , so is an isomorphism. It follows that  $(\mathrm{Ker} f)_0 = 0$ , so  $\mathrm{Ker} f = 0$  and f is an isomorphism, as claimed.

<sup>&</sup>lt;sup>16</sup>Note that for each i, one of these two summands is necessarily 0.

12.4. Koszul complexes. Let R be a commutative ring and  $f \in R$ . Then we can define a 2-step **Koszul complex**  $K_R(f) = [R \to R]$  with the differential given by multiplication by f (the two copies of R sit in degrees -1 and 0). We have  $H^0(K_R(f)) = R/(f)$ , and  $K_R(f)$  is exact in degree -1 if and only if f is not a zero divisor in R. This allows us to define the Koszul complex of several elements of R:

$$K_R(f_1,...,f_m) = K_R(f_1) \otimes_R ... \otimes_R K_R(f_m)$$

with  $H^0(K_R(f_1,...,f_m)) = R/(f_1,...,f_m)$ . Thus

$$K_R(f_1,...,f_m) = K_R(f_1,...,f_{m-1}) \otimes_R K_R(f_m).$$

For example, let  $R:=k[x_1,...,x_n]$  for a field k. Then the complex  $K_n:=K_R(x_1,...,x_n)=K_1^{\otimes n}$  is acyclic in negative degrees and has  $H^0 = k$ . Thus for any commutative k-algebra S, the complex  $K_{R\otimes S}(x_1,...,x_n):=K_R(x_1,...,x_n)\otimes S$  is acyclic in negative degrees and has  $H^0 = S$ . By taking S = R and making a linear change of variable, this yields a free resolution of R as an R-bimodule called the **Koszul resolution**, which we'll denote it by  $K_n$ :

$$0 \to R \otimes \wedge^n k^n \otimes R \to \dots \to R \otimes \wedge^2 k^n \otimes R \to R \otimes k^n \otimes R \to R \otimes R \to R.$$

Moreover, this exact sequence is split as a sequence of R-modules (under right multiplication by R), since all participating R-modules are free. Hence if M is any R-module then  $K_n \otimes_R M$  is a free resolution of M of length n. Thus we obtain

**Proposition 12.4.** If i > n then for any  $k[x_1, ..., x_n]$ -modules M, N, one has  $\operatorname{Ext}^{i}(M, N) = 0$ .

12.5. Syzygies. Now assume that M is a finitely generated graded module over  $R = k[x_1, ..., x_n]$ . Then  $M =: M_0$  is a quotient of  $R \otimes V_0$ , where  $V_0$  is a finite-dimensional graded vector space. By the Hilbert basis theorem, the kernel  $M_1$  of the map  $\phi_0: R \otimes V_0 \to M$  is finitely generated, so is a quotient of  $R \otimes V_1$  for some finite-dimensional graded space  $V_1$ , and the kernel  $M_2$  of  $\phi_1: R \otimes V_1 \to M_1$  is finitely generated, and so on. The long exact sequences of Ext groups associated to the short exact sequences

$$0 \to M_{j+1} \to R \otimes V_j \to M_j \to 0$$

and Proposition 12.4 then imply by induction in j that  $\operatorname{Ext}^i(M_j, N) = 0$ for any R-module N if i > n - j. In particular, the module  $M_n$  is projective, hence free by Lemma 12.3, i.e., we may take  $V_n$  such that  $M_n = R \otimes V_n$ . This gives a free resolution of M by finitely generated graded R-modules:

$$0 \to R \otimes V_n \to \dots \to R \otimes V_0 \to M.$$

Thus, taking graded Euler characteristic we obtain

Theorem 12.5. (Hilbert syzygies theorem) We have

$$H(M,q) = \frac{p(q)}{(1-q)^n},$$

where p is a polynomial with integer coefficients.

*Proof.* Indeed, p is just the alternating sum of the Hilbert polynomials of  $V_i$ . 

12.6. The Hilbert-Samuel polynomial. Let R be a commutative Noetherian ring and  $\mathfrak{m} \subset R$  a maximal ideal. Then  $R/\mathfrak{m} = k$  is a field and  $\mathfrak{m}^N/\mathfrak{m}^{N+1}$  is a finite-dimensional k-vector space. Thus  $\operatorname{gr}(R) := \bigoplus_{N>0} \mathfrak{m}^N/\mathfrak{m}^{N+1}$  (where  $\mathfrak{m}^0 := R$ ) is a graded algebra generated in degree 1. So by the Theorem 12.5, the Hilbert series

$$H(\operatorname{gr}(R),q) = \sum_{N>0} \dim_k(\mathfrak{m}^N/\mathfrak{m}^{N+1})q^N$$

is a rational function of the form  $\frac{p(q)}{(1-q)^m}$ , where p is a polynomial and  $m = \dim_k(\mathfrak{m}/\mathfrak{m}^2)$ . Hence

$$P_{R,\mathfrak{m}}(N) := \sum_{j=0}^{N-1} \dim_k(\mathfrak{m}^j/\mathfrak{m}^{j+1}) = \operatorname{length}(R/\mathfrak{m}^N)$$

is a polynomial in N for large enough N called the **Hilbert-Samuel polynomial** of R at  $\mathfrak{m}$ . The degree of this polynomial equals the order of the pole of H(gr(R), q) at q = 1. We call this degree the **dimension** of R at  $\mathfrak{m}$ , denoted  $\dim_{\mathfrak{m}} R$ . For example, if  $R = k[x_1, ..., x_n]$  and  $\mathfrak{m}$  is any maximal ideal then  $P_{R,\mathfrak{m}}(N) = \binom{N+n-1}{n}$ , so  $\dim_{\mathfrak{m}} R = n$ .

**Lemma 12.6.** Let  $f \in \mathfrak{m}$ . Then  $\dim_{\mathfrak{m}}(R/f) \ge \dim_{\mathfrak{m}} R - 1$ .

*Proof.* The ideal (f) in  $R/\mathfrak{m}^N$  is the image of  $fR/\mathfrak{m}^{N-1}$ . So we have

$$P_{R/f,\mathfrak{m}}(N) = \operatorname{length}((R/\mathfrak{m}^N)/f) \ge \operatorname{length}(R/\mathfrak{m}^N) - \operatorname{length}(R/\mathfrak{m}^{N-1})$$

$$= P_{R,\mathfrak{m}}(N) - P_{R,\mathfrak{m}}(N-1),$$

which implies the statement.

Let k be an algebraically closed field and  $\mathfrak{m}_p \subset k[x_1,...,x_n]$  be the maximal ideal corresponding to  $p \in k^n$ .

Corollary 12.7. Let  $f_1, ..., f_m \in k[x_1, ..., x_n]$  be homogeneous polynomials of positive degrees. Let Z be an irreducible component of the zero set  $Z(f_1,...,f_m) \subset k^n$ . Then  $\dim_{\mathfrak{m}_0} k[Z] \geq n-m$ .

Proof. Let  $p \in Z$  be not contained in other components of  $Z(f_1, ..., f_m)$ . Applying Lemma 12.6 repeatedly, we get  $\dim_{\mathfrak{m}_p} k[Z] \geq n - m$ . But  $\operatorname{gr}(k[Z]/\mathfrak{m}_p^N)$  (the associated graded under the filtration induced by the grading on k[Z]) is a quotient of  $k[Z]/\mathfrak{m}_0^N$ . Thus<sup>17</sup>

$$\dim_{\mathfrak{m}_0} k[Z] \ge \dim_{\mathfrak{m}_p} k[Z],$$

so  $\dim_{\mathfrak{m}_0} k[Z] \geq n - m$ .

12.7. **Regular sequences.** Let R be a commutative ring. A sequence  $f_1, ..., f_n \in R$  is called a **regular sequence** if for each  $j \in [1, n]$ ,  $f_j$  is not a zero divisor in  $R/(f_1, ..., f_{j-1})$ , and  $R/(f_1, ..., f_n) \neq 0$ .

**Lemma 12.8.** If  $f_1, ..., f_n \in R$  is a regular sequence then the complex  $K_R(f_1, ..., f_n)$  is exact in negative degrees.

*Proof.* The proof is by induction in n with obvious base. For the induction step, note that by the inductive assumption  $K_R(f_1, ..., f_{n-1})$  is exact in negative degrees with  $H^0 = R/(f_1, ..., f_{n-1})$ , so the cohomology of  $K_R(f_1, ..., f_n)$  coincides with the cohomology  $K_{R/(f_1, ..., f_{n-1})}(f_n)$ , which vanishes in negative degrees since  $f_n$  is not a zero divisor in  $R/(f_1, ..., f_{n-1})$ .

Now let k be an algebraically closed field.

**Proposition 12.9.** Suppose  $f_1, ..., f_n \in R := k[x_1, ..., x_n]$  are homogeneous polynomials of positive degree such that the zero set  $Z(f_1, ..., f_n)$  consists of the origin. Then  $f_1, ..., f_n$  is a regular sequence.

Proof. We need to show that for each  $m \leq n-1$ ,  $f_{m+1}$  is not a zero divisor in  $R_m := k[x_1, ..., x_n]/(f_1, ..., f_m)$ . Let  $Z_m = Z(f_1, ..., f_m)$ . It suffices to show that  $f_{m+1}$  does not vanish on any irreducible component of  $Z_m$ . Assume the contrary, i.e., that it vanishes on such a component  $Z_m^0$ . By Corollary 12.7, we have  $\dim_{\mathfrak{m}_0} k[Z_m^0] \geq n-m$ . Since  $f_{m+1}=0$  on  $Z_m^0$ , using Lemma 12.6 repeatedly, we get

$$\dim_{\mathfrak{m}_0} k[Z_m^0]/(f_{m+1},...,f_n) \ge 1,$$

which is a contradiction, as the zero set of  $f_{m+1}, ..., f_n$  on  $Z_m^0$  consists just of the origin, so this dimension must be zero.

**Proposition 12.10.** Suppose  $f_1, ..., f_n \in R := k[x_1, ..., x_n]$  are homogeneous polynomials of degrees  $d_1, ..., d_n > 0$  such that R is a finitely generated module over  $S := k[f_1, ..., f_n]$ . Then this module is free of rank  $\prod_{i=1}^n d_i$ . Moreover, the Hilbert polynomial of  $R_0 := k[x_1, ..., x_n]/(f_1, ..., f_m)$ 

 $<sup>^{17}</sup>$ In fact these dimensions are equal (to dim Z), but we don't use it here.

(or, equivalently, of a space of free homogeneous generators of this module) is

(10) 
$$H(R_0, q) = \prod_{i=1}^{n} [d_i]_q.$$

*Proof.* By Lemma 12.3, it suffices to show that R is a free S-module. By assumption  $R_0$  is finite-dimensional, i.e., the equations

$$f_1 = \dots = f_n = 0$$

have only the zero solution. By Proposition 12.9, this implies that  $f_1, ..., f_n$  is a regular sequence, so by Lemma 12.8 the Koszul complex  $K_R(f_1, ..., f_n)$  associated to this sequence is exact in negative degrees. Now, write S as  $k[a_1, ..., a_n]$  with  $\deg a_j = 0$  and consider the complex  $K_{R\otimes S}(f_1 - a_1, ..., f_n - a_n)$ . This complex is filtered by degree with associated graded being

$$K_{R\otimes S}(f_1,...,f_n) = K_R(f_1,...,f_n) \otimes S.$$

Thus  $K_{R\otimes S}(f_1-a_1,...,f_n-a_n)$  is also exact in nonzero degrees with

$$H^0 = k[x_1, ..., x_n, a_1, ..., a_n]/(f_1 - a_1, ..., f_n - a_n) = R.$$

and the associated graded under the above filtration is  $gr(R) = R_0 \otimes S$  as an S-module. This module is free over S, hence so is R.

Remark 12.11. Let  $f_1, ..., f_r$  be a regular sequence of homogeneous polynomials in  $k[x_1, ..., x_n]$  of positive degree and  $Z_m \subset k^n$  be the zero set of  $f_1, ..., f_m$ . Then  $f_{m+1}$  is not a zero divisor in  $k[x_1, ..., x_n]/(f_1, ..., f_m)$ , hence does not vanish identically on any irreducible component of  $Z_m$ . So by induction in m we get that the dimension of every irreducible component of  $Z_m$  is  $\leq n - m$ . By Corollary 12.7, this implies that this dimension is precisely n - m; in particular,  $r \leq n$ , and every irreducible component of the affine scheme  $\mathcal{Z} := \operatorname{Spec} k[x_1, ..., x_n]/(f_1, ..., f_r)$  has dimension n - r. Such a scheme is called a **complete intersection**. In fact, it follows by induction in r that  $\mathcal{Z}$  is a complete intersection precisely when all its irreducible components have dimension  $\leq n - r$  (in which case they have dimension exactly n - r). In particular, if r = n, this means that the only k-point of  $\mathcal{Z}$  is the origin, as indicated in Proposition 12.9. Thus the converse of this proposition also holds.

12.8. **Proof of the CST Theorem, Part II.** We are now ready to prove Theorem 12.2. It follows from Proposition 12.10, Lemma 12.1 and Theorem 10.6 that  $\mathbb{C}[V]$  is a free  $\mathbb{C}[V]^G$ -module. Since  $\mathbb{C}[V] = \bigoplus_{\rho} \operatorname{Hom}_G(\rho, \mathbb{C}[V]) \otimes \rho$ , it follows by Lemma 12.3(ii) that  $\operatorname{Hom}_G(\rho, \mathbb{C}[V])$ 

is also a free  $\mathbb{C}[V]^G\text{-module}$  (as it is graded and projective). Finally, the rank of this module equals

 $\dim_{\mathbb{C}(V)^G}(\mathbb{C}(V)^G \otimes_{\mathbb{C}[V]^G} \mathrm{Hom}_G(\rho,\mathbb{C}[V])) = \dim_{\mathbb{C}(V)^G} \mathrm{Hom}_G(\rho,\mathbb{C}(V)),$  which equals  $\dim \rho$  by basic Galois theory  $(\mathbb{C}(V)$  is a regular representation of G over  $\mathbb{C}(V)^G$ ).

#### 13. Kostant's theorem

13.1. Kostant's theorem for  $S\mathfrak{g}$ . Let  $\mathfrak{g}$  be a semisimple complex Lie algebra.

**Theorem 13.1.** (Kostant)  $S\mathfrak{g}$  is a free  $(S\mathfrak{g})^{\mathfrak{g}}$ -module. Moreover, for every finite-dimensional irreducible representation V of  $\mathfrak{g}$ , the space  $\operatorname{Hom}_{\mathfrak{g}}(V, S\mathfrak{g})$  is a free  $(S\mathfrak{g})^{\mathfrak{g}}$  module of rank  $\dim V[0]$ , the dimension of the zero weight space of V.

The rest of the subsection is dedicated to the proof of this theorem. Introduce a filtration on  $S\mathfrak{g}$  by setting  $\deg(\mathfrak{g}_{\alpha})=1$  for all roots  $\alpha$  and  $\deg\mathfrak{h}=2$ . Then  $\operatorname{gr}(S\mathfrak{g})=S\mathfrak{n}_{-}\otimes S\mathfrak{h}\otimes S\mathfrak{n}_{+}$  and by the Chevalley restriction theorem,  $\operatorname{gr}(S\mathfrak{g})^{\mathfrak{g}}$  is identified with the subalgebra  $(S\mathfrak{h})^{W}$  of the middle factor. Thus by the Chevalley-Shephard-Todd theorem,  $\operatorname{gr}(S\mathfrak{g})$  is a free  $\operatorname{gr}(S\mathfrak{g})^{\mathfrak{g}}$ -module. It follows that  $S\mathfrak{g}$  is a free  $(S\mathfrak{g})^{\mathfrak{g}}$ -module (namely, any lift of a homogeneous basis of the graded module is a basis of the filtered module).

Now recall that

(11) 
$$S\mathfrak{g} = \bigoplus_{V \in \operatorname{Irr}(\mathfrak{g})} V \otimes \operatorname{Hom}_{\mathfrak{g}}(V, S\mathfrak{g}).$$

Thus  $\operatorname{Hom}_{\mathfrak{g}}(V, S\mathfrak{g})$  is a graded direct summand in  $S\mathfrak{g}$ . It follows that  $\operatorname{Hom}_{\mathfrak{g}}(V, S\mathfrak{g})$  is a projective, hence free  $(S\mathfrak{g})^{\mathfrak{g}}$ -module (using Lemma 12.3(ii)).

It remains to prove the formula for the rank of  $\operatorname{Hom}_{\mathfrak{g}}(V, S\mathfrak{g})$ . To this end, consider the Q-graded Hilbert series of  $S\mathfrak{g}$ , i.e., the generating function of the characters of symmetric powers of  $\mathfrak{g}$ :

$$H_Q(S\mathfrak{g},q) := \sum_{m\geq 0} (\sum_{\mu\in Q} \dim S^m \mathfrak{g}[\mu] e^{\mu}) q^m \in \mathbb{C}[Q][[q]].$$

Since  $S\mathfrak{g} = S\mathfrak{h} \otimes \bigotimes_{\alpha \in R} S\mathfrak{g}_{\alpha}$ , we have

$$H_Q(S\mathfrak{g},q) = \frac{1}{(1-q)^r} \prod_{\alpha \in R} \frac{1}{1-qe^{\alpha}},$$

where  $r = \text{rank}(\mathfrak{g})$ . On the other hand, by (11),

$$H_Q(S\mathfrak{g},q) = \sum_{V \in Irr(\mathfrak{g})} H(Hom_{\mathfrak{g}}(V,S\mathfrak{g}),q)\chi_V,$$

where  $\chi_V$  is the character of V.

Now, by the Chevalley restriction theorem  $(S\mathfrak{g})^{\mathfrak{g}} \cong (S\mathfrak{h})^W$ , so

$$H(\operatorname{Hom}_{\mathfrak{g}}(V, S\mathfrak{g}), q) = H(\operatorname{Hom}_{\mathfrak{g}}(V, (S\mathfrak{g})_0), q) H((S\mathfrak{h})^W, q).$$

Thus by the Chevalley-Shephard-Todd theorem,

$$H(\operatorname{Hom}_{\mathfrak{g}}(V, S\mathfrak{g}), q) = H(\operatorname{Hom}_{\mathfrak{g}}(V, (S\mathfrak{g})_0), q) \prod_{i=1}^r \frac{1}{1 - q^{d_i}}.$$

So we get

$$\sum_{V \in Irr(\mathfrak{g})} H(Hom_{\mathfrak{g}}(V, (S\mathfrak{g})_0), q) \chi_V = \frac{\prod_{i=1}^r [d_i]_q}{\prod_{\alpha \in R} (1 - qe^{\alpha})}.$$

By character orthogonality,  $H(\operatorname{Hom}_{\mathfrak{g}}(V,(S\mathfrak{g})_0),q)$  is the inner product of the right hand side of this equality with  $\chi_V$ :

$$H(\operatorname{Hom}_{\mathfrak{g}}(V,(S\mathfrak{g})_0),q) = \left(\frac{\prod_{i=1}^r [d_i]_q}{\prod_{\alpha \in R} (1 - qe^{\alpha})}, \chi_V\right).$$

Recall that the inner product on  $\mathbb{C}[P]$  making the characters orthonormal is given by the formula

$$(\phi, \psi) = \frac{1}{|W|} \operatorname{CT}(\phi \psi^* \prod_{\alpha \in R} (1 - e^{\alpha})),$$

where where CT denotes the constant term and \* is the automorphism of  $\mathbb{C}[P]$  given by  $(e^{\mu})^* = e^{-\mu}$ . Thus, using that  $\chi_V^* = \chi_{V^*}$ , we get

(12) 
$$H(\operatorname{Hom}_{\mathfrak{g}}(V, (S\mathfrak{g})_{0}), q) = \frac{\prod_{i=1}^{r} [d_{i}]_{q}}{|W|} \operatorname{CT}\left(\chi_{V^{*}} \prod_{\alpha \in R} \frac{1 - e^{\alpha}}{1 - qe^{\alpha}}\right).$$

In this formula q is a formal parameter, but the right hand side converges to an analytic function in the disk |q| < 1, since it can be written as an integral:

$$H(\operatorname{Hom}_{\mathfrak{g}}(V,(S\mathfrak{g})_{0}),q) = \frac{\prod_{i=1}^{r} [d_{i}]_{q}}{|W|} \int_{\mathfrak{h}_{\mathbb{R}}/Q^{\vee}} \chi_{V^{*}}(e^{ix}) \prod_{\alpha \in \mathbb{R}} \frac{1 - e^{i\alpha(x)}}{1 - qe^{i\alpha(x)}} dx,$$

where  $Q^{\vee}$  is the coroot lattice. If  $0 \leq q < 1$ , this can also be written as (13)

$$H(\operatorname{Hom}_{\mathfrak{g}}(V,(S\mathfrak{g})_{0}),q) = \frac{\prod_{i=1}^{r} [d_{i}]_{q}}{|W|} \int_{\mathfrak{h}_{\mathbb{R}}/Q^{\vee}} \chi_{V^{*}}(e^{ix}) \left| \prod_{\alpha \in R_{+}} \frac{1 - e^{i\alpha(x)}}{1 - qe^{i\alpha(x)}} \right|^{2} dx.$$

**Lemma 13.2.** As  $q \to 1$  in (0,1), the function  $F_q(x) := \prod_{\alpha \in R_+} \frac{1 - e^{i\alpha(x)}}{1 - qe^{i\alpha(x)}}$  goes to 1 in  $L^2(\mathfrak{h}/Q^{\vee})$ .<sup>18</sup>

<sup>&</sup>lt;sup>18</sup>Note however that  $F_q(x)$  does not go to 1 pointwise (hence not in  $C(\mathfrak{h}/Q^{\vee})$ ) since  $F_q(0) = 0$ .

*Proof.* If  $x \in \mathbb{R}$ ,  $|x| \le 1$  then  $\min_{q \in [0,1]} (1 - 2qx + q^2)$  is 1 if  $x \le 0$  and  $1 - x^2$  if x > 0. So if z = x + iy is on the unit circle and  $0 \le q < 1$  then

$$\left| \frac{1-z}{1-qz} \right|^2 = \frac{2(1-x)}{1-2qx+q^2} \le \begin{cases} 2(1-x), & x \le 0\\ \frac{2}{1+x}, & x > 0 \end{cases} \le 4$$

Note also that by the residue formula

$$\int_0^1 \frac{dt}{|1 - qe^{2\pi it}|^2} = \frac{1}{2\pi i} \int_{|z|=1} \frac{z^{-1}dz}{(1 - qz)(1 - qz^{-1})} = \frac{1}{1 - q^2}.$$

Thus

$$\int_0^1 \left| \frac{1 - e^{2\pi it}}{1 - qe^{2\pi it}} - 1 \right|^2 dt = \int_0^1 \left| \frac{(q - 1)e^{2\pi it}}{1 - qe^{2\pi it}} \right|^2 dt = \frac{1 - q}{1 + q}.$$

So  $\frac{1-z}{1-qz} \to 1$  as  $q \to 1$  in  $L^2(S^1)$ . But if X is a finite measure space and for j=1,...,N,  $f_n^{(j)} \to f^{(j)}$  in  $L^2(X)$  as  $n \to \infty$  and  $|f_n^{(j)}(z)| \le C$  for all  $z \in X$  and all n, j then  $\prod_j f_n^{(j)} \to \prod_j f_j$  in  $L^2(X)$ . This implies the statement.

By Lemma 13.2 we may take the limit  $q \to 1$  under the integral in (13). Then, using that  $\prod_{i=1}^r d_i = |W|$ , we get

$$\dim\operatorname{Hom}_{\mathfrak{g}}(V,(S\mathfrak{g})_{0})=\int_{\mathfrak{h}/Q^{\vee}}\chi_{V^{*}}(e^{ix})dx=$$

$$CT(\chi_{V^*}) = \dim V^*[0] = \dim V[0],$$

which concludes the proof of Kostant's theorem.

## 13.2. The structure of $S\mathfrak{g}$ as a $(S\mathfrak{g})^{\mathfrak{g}}$ -module. As a by-product, we obtain

**Theorem 13.3.** (Kostant) For  $\lambda \in P_+$  we have

$$H(\operatorname{Hom}_{\mathfrak{g}}(L_{\lambda}^{*},(S\mathfrak{g})_{0}),q) = \frac{\prod_{i=1}^{r}[d_{i}]_{q}}{|W|}\operatorname{CT}\left(\prod_{\alpha\in R}\frac{1-e^{\alpha}}{1-qe^{\alpha}}\chi_{L_{\lambda}}\right) = \prod_{i=1}^{r}[d_{i}]_{q}\cdot\operatorname{CT}\left(\frac{e^{\lambda}\prod_{\alpha\in R_{+}}(1-e^{\alpha})}{\prod_{\alpha\in R}(1-qe^{\alpha})}\right).$$

Indeed, the first expression is (12) and second expression is obtained from (12) using the Weyl character formula for  $\chi_{L_{\lambda}}$  and observing that all terms in the resulting sum over W are the same.

Substituting  $\lambda = 0$ , we get

Corollary 13.4.

$$\frac{1}{|W|} \operatorname{CT} \left( \prod_{\alpha \in R} \frac{1 - e^{\alpha}}{1 - qe^{\alpha}} \right) = \operatorname{CT} \left( \frac{\prod_{\alpha \in R_{+}} (1 - e^{\alpha})}{\prod_{\alpha \in R} (1 - qe^{\alpha})} \right) = \frac{1}{\prod_{i=1}^{r} [d_{i}]_{q}}.$$

For example, if  $\mathfrak{g} = \mathfrak{sl}_2$ , this formula looks like (14)

$$\frac{1}{2}\operatorname{CT}\left(\frac{(1-z)(1-z^{-1})}{(1-qz)(1-qz^{-1})}\right) = \operatorname{CT}\left(\frac{1-z}{(1-qz)(1-qz^{-1})}\right) = \frac{1}{1+q},$$

which is easy to check using the residue formula.

For  $\mathfrak{g} = \mathfrak{sl}_n$  we obtain the identity

$$\frac{1}{n!} \operatorname{CT} \left( \prod_{1 \le i < j \le n} \frac{(1 - \frac{X_i}{X_j})(1 - \frac{X_j}{X_i})}{(1 - q\frac{X_i}{X_j})(1 - q\frac{X_j}{X_i})} \right) = \operatorname{CT} \left( \prod_{1 \le i < j \le n} \frac{1 - \frac{X_i}{X_j}}{(1 - q\frac{X_i}{X_j})(1 - q\frac{X_j}{X_i})} \right) \\
= \frac{1}{(1 + q)...(1 + q + ... + q^{n-1})}.$$

13.3. The structure of  $U(\mathfrak{g})$  as a  $Z(\mathfrak{g})$ -module. Recall that the universal enveloping algebra  $U(\mathfrak{g})$  of any Lie algebra  $\mathfrak{g}$  has the standard filtration defined on generators by  $\deg(\mathfrak{g})=1$ , which is called the **Poincaré-Birkhoff-Witt filtration**.

Let  $\mathfrak{g}$  be a semisimple complex Lie algebra of rank r, and W be the Weyl group of  $\mathfrak{g}$  with degrees  $d_i, i = 1, ..., r$ .

**Theorem 13.5.** (Kostant) (i) The center  $Z(\mathfrak{g}) = U(\mathfrak{g})^{\mathfrak{g}}$  of  $U(\mathfrak{g})$  is a polynomial algebra in r generators  $C_i$  of Poincaré-Birkhoff-Witt filtration degrees  $d_i$ .

(ii)  $U(\mathfrak{g})$  is a free module over  $Z(\mathfrak{g})$ , and for every irreducible finite-dimensional representation V of  $\mathfrak{g}$ , the space  $\operatorname{Hom}_{\mathfrak{g}}(V,U(\mathfrak{g}))$  is a free  $Z(\mathfrak{g})$ -module of rank dim V[0].

*Proof.* By the Poincaré-Birkhoff-Witt theorem, for any Lie algebra  $\mathfrak{g}$  we have  $\operatorname{gr}(U(\mathfrak{g})) = S\mathfrak{g}$ . Moreover, we have the symmetrization map  $S\mathfrak{g} \to U(\mathfrak{g})$  given by

$$a_1 \otimes ... \otimes a_n \mapsto \frac{1}{n!} \sum_{s \in S_n} a_{s(1)} ... a_{s(n)},$$

 $a_i \in \mathfrak{g}$ , which is an isomorphism of  $\mathfrak{g}$ -modules. Using this map, any homogeneous element of  $(S\mathfrak{g})^{\mathfrak{g}}$  can be lifted into  $U(\mathfrak{g})^{\mathfrak{g}}$ . It follows that  $\operatorname{gr}(U(\mathfrak{g})^{\mathfrak{g}}) = (S\mathfrak{g})^{\mathfrak{g}}$ . Thus Theorem 13.1 implies all the statements of the theorem.

**Example 13.6.** Suppose  $\mathfrak{g}$  is simple. Then  $d_1 = 2$  and  $C_1$  is the quadratic Casimir of  $\mathfrak{g}$ .

**Exercise 13.7.** Consider the Lie algebra  $\mathfrak{g} = \mathfrak{sl}_n(\mathbb{C})$  spanned by elementary matrices  $E_{ij}$  with  $\sum_{i=1}^{n} E_{ii} = 0$ . (i) Show that the center  $Z(\mathfrak{g})$  is freely generated by the elements

$$C_{k-1} := \sum_{i_1,\dots,i_k=1}^n \prod_{j=1}^k E_{i_j,i_{j+1}}, \ k = 2,\dots,n.$$

where j is viewed as an element of  $\mathbb{Z}/k$ .

Hint: It is slightly more convenient (and equivalent) to consider  $\mathfrak{g} = \mathfrak{gl}_n(\mathbb{C})$ , in which case one also has the generator  $C_0$ . Identify  $\mathfrak{g}$ with  $\mathfrak{g}^*$  using the trace pairing on  $\mathfrak{g}$ . Let  $T_k : \mathfrak{g}^{\otimes k} \to \mathbb{C}$  be the  $\mathfrak{g}$ -module map defined by  $T_k(a_1 \otimes ... \otimes a_k) := \operatorname{Tr}(a_k...a_1)$ . Let  $T_k^* : \mathbb{C} \to \mathfrak{g}^{\otimes k}$  be the dual map. Show that

$$T_k^*(1) = \sum_{i_1,\dots,i_k=1}^n E_{i_1i_2} \otimes E_{i_2i_3} \otimes \dots \otimes E_{i_ki_1}.$$

Use that this element is  $\mathfrak{g}$ -invariant to show that the element  $C_{k-1}$  is

(ii) Generalize these statements to  $\mathfrak{so}_{2n+1}(\mathbb{C})$  and  $\mathfrak{sp}_{2n}(\mathbb{C})$ . What happens for  $\mathfrak{so}_{2n}$ ?

#### 14. Harish-Chandra isomorphism, maximal quotients

14.1. The Harish-Chandra isomorphism. Let  $\mathfrak{g}$  be a complex semisimple Lie algebra. Fix a triangular decomposition  $\mathfrak{g} = \mathfrak{n}_- \oplus \mathfrak{h} \oplus \mathfrak{n}_+$ . By the PBW theorem, we then have a linear isomorphism

$$\mu: U(\mathfrak{n}_{-}) \otimes U(\mathfrak{h}) \otimes U(\mathfrak{n}_{+}) \to U(\mathfrak{g})$$

given by multiplication. We also have the linear map

$$\beta: U(\mathfrak{n}_{-}) \otimes U(\mathfrak{h}) \otimes U(\mathfrak{n}_{+}) \to U(\mathfrak{h})$$

given by

$$a_- \otimes h \otimes a_+ \mapsto \varepsilon(a_-)\varepsilon(a_+)h, \ a_\pm \in U(\mathfrak{n}_\pm), h \in U(\mathfrak{h}),$$

where  $\varepsilon: U(\mathfrak{n}_+) \to \mathbb{C}$  is the augmentation homomorphism (the counit). Thus we get a linear map

$$HC := \beta \circ \mu^{-1} : U(\mathfrak{g}) \to U(\mathfrak{h}) = S\mathfrak{h} = \mathbb{C}[\mathfrak{h}^*]$$

called the Harish-Chandra map.

**Theorem 14.1.** (Harish-Chandra) (i) If  $b \in U(\mathfrak{g})$  and  $c \in Z(\mathfrak{g})$  then HC(bc) = HC(b)HC(c). In particular, the restriction of HC to  $Z(\mathfrak{g})$ is an algebra homomorphism.

- (ii) Define the shifted action of W on  $\mathfrak{h}^*$  by  $w \bullet x := w(x+\rho) \rho$  where  $\rho$  is the half sum of positive roots (or, equivalently, sum of fundamental weights). Then HC maps  $Z(\mathfrak{g})$  into the space of invariants  $\mathbb{C}[\mathfrak{h}^*]^{W\bullet}$ . That is, for any  $b \in Z(\mathfrak{g})$  we have  $HC(b)(\lambda) = f_b(\lambda + \rho)$  for some  $f_b \in \mathbb{C}[\mathfrak{h}^*]^W$ .
- (iii) If V be a highest weight representation of  $\mathfrak{g}$  with highest weight  $\lambda$  then

$$f_b(\lambda + \rho) = (v_\lambda^*, bv_\lambda)$$

where  $v_{\lambda}$  is a highest weight vector of V and  $v_{\lambda}^{*}$  the lowest weight vector of  $V^*$  such that  $(v_{\lambda}^*, v_{\lambda}) = 1$ . Thus if  $b \in Z(\mathfrak{g})$  then  $HC(b)(\lambda)$  is the scalar by which b acts on a highest weight module with highest weight

- (iv) The map  $HC: Z(\mathfrak{g}) \to \mathbb{C}[\mathfrak{h}^*]^{W \bullet}$  is a filtered algebra homomorphism and gr(HC) = Res, the Chevalley restriction homomorphism  $(S\mathfrak{g})^{\mathfrak{g}} \to (S\mathfrak{h})^W$ .
  - (v) HC is an algebra isomorphism.

The isomorphism  $HC: Z(\mathfrak{g}) \to \mathbb{C}[\mathfrak{h}^*]^{W_{\bullet}}$  is called the **Harish**-Chandra isomorphism.

*Proof.* Let  $b = a_-ha_+ \in U(\mathfrak{g})$ . We have

$$(v_{\lambda}^*, bv_{\lambda}) = (v_{\lambda}^*, a_-ha_+v_{\lambda}) = \varepsilon(a_-)\varepsilon(a_+)\lambda(h) = HC(b)(\lambda).$$

Thus

$$HC(bc)(\lambda) = (v_{\lambda}^*, bcv_{\lambda}) = (v_{\lambda}^*, bv_{\lambda})(v_{\lambda}^*, cv_{\lambda}) = HC(b)(\lambda)HC(c)(\lambda)$$

since c is central; namely, the last factor is just the eigenvalue of c on V. This proves (i).

To establish (ii),(iii), it remains to show that for  $b \in Z(\mathfrak{g})$ , HC(b) is invariant under the shifted action of all  $w \in W$ . To this end, it suffices to show this for  $w = s_i$ , a simple reflection. For this purpose, consider the Verma module  $M_{\lambda}$  with  $(\lambda + \rho, \alpha_i^{\vee}) = n \in \mathbb{Z}_{>0}$ . Then  $f_i^n v_{\lambda}$  generates a copy of  $M_{\lambda - n\alpha_i} = M_{s_i \bullet \lambda}$  inside  $M_{\lambda}$ . Thus we get  $HC(b)(\lambda) = HC(b)(s_i \bullet \lambda)$ . Since this holds on a Zariski dense set, it holds identically, which yields (ii),(iii).

(iv) follows immediately from (iii).

Finally, (v) follows from (iv) and the Chevalley restriction theorem, since any filtered map whose associated graded is an isomorphism is itself an isomorphism.  $\Box$ 

Remark 14.2. Kostant theorems and the Harish-Chandra isomorphism extend trivially to reductive Lie algebras.

14.2. **Maximal quotients.** Let  $\mathfrak{g}$  be a semisimple Lie algebra and M a  $\mathfrak{g}$ -module on which the center  $Z(\mathfrak{g})$  acts by a character

$$\chi: Z(\mathfrak{g}) \to \mathbb{C}$$

(for example, M is irreducible). In view of the Harish-Chandra isomorphism theorem, we have  $\chi = \chi_{\lambda}$ , where

$$\chi_{\lambda}(z) = HC(z)(\lambda)$$

for a unique  $\lambda \in \mathfrak{h}^*$  modulo the shifted action of W. As mentioned in Subsection 7.2, the element  $\chi_{\lambda}$  is called the **infinitesimal character** or **central character** of M.

If M is a  $\mathfrak{g}$ -bimodule then it carries two actions of  $Z(\mathfrak{g})$ , by left and by right multiplication. If these actions are by characters, then they are called the **left and right infinitesimal characters** of M. The infinitesimal character of M is then the pair  $(\theta, \chi)$  where  $\theta$  is the left infinitesimal character and  $\chi$  the right infinitesimal character of M.

For a character  $\chi:Z(\mathfrak{g})\to\mathbb{C}$  let

$$U_{\chi} = U_{\chi}(\mathfrak{g}) := U(\mathfrak{g})/(z - \chi(z), z \in Z(\mathfrak{g})).$$

This algebra is called the **maximal quotient** of  $U(\mathfrak{g})$  with infinitesimal character  $\chi$ , as every  $U(\mathfrak{g})$ -module with such infinitesimal character factors through  $U_{\chi}$ . Note that  $U_{\chi}$  is a  $\mathfrak{g}$ -bimodule with infinitesimal character  $(\chi, \chi)$  (as it is a  $U_{\chi}$ -bimodule).

Theorem 13.5 immediately implies

Corollary 14.3. For any finite-dimensional irreducible  $\mathfrak{g}$ -module V we have  $\dim \operatorname{Hom}_{\mathfrak{g}}(V, U_{\chi}) = \dim V[0]$ , where  $\mathfrak{g}$  acts on  $U_{\chi}$  by the adjoint action. Thus  $U_{\chi}$  is a Harish-Chandra  $\mathfrak{g}$ -bimodule.

Corollary 14.4. If V is a finite-dimensional  $\mathfrak{g}$ -bimodule then  $V \otimes U_{\chi}$  is a Harish-Chandra  $\mathfrak{g}$ -bimodule.

*Proof.* This follows from Corollary 14.3 and Exercise 5.12.  $\Box$ 

**Corollary 14.5.** (i) Every irreducible  $\mathfrak{g}$ -bimodule M locally finite under the adjoint  $\mathfrak{g}$ -action is a quotient of  $V \otimes U_{\chi}$  for some finite-dimensional irreducible  $\mathfrak{g}$ -module V with trivial right action of  $\mathfrak{g}$ , where  $\chi$  is the right infinitesimal character of M.

(ii) Every irreducible  $\mathfrak{g}$ -bimodule locally finite under the adjoint  $\mathfrak{g}$ -action is a Harish-Chandra bimodule.

*Proof.* (ii) follows from (i) and Corollary 14.4, so it suffices to prove (i). By Dixmier's lemma (Lemma 7.2), M has some infinitesimal character  $(\theta, \chi)$ . Let  $V \subset M$  be an irreducible finite-dimensional subrepresentation under  $\mathfrak{g}_{ad}$ . Let us view  $V^*$  as a  $\mathfrak{g}$ -bimodule with action

$$(af)(x) = -f(ax), fb = 0$$

for  $a, b \in \mathfrak{g}, x \in V, f \in V^*$ , and consider the tensor product  $V^* \otimes M$ , which is a  $\mathfrak{g}$ -bimodule with action

$$a \circ (f \otimes m) := af \otimes m + f \otimes am, \ (f \otimes m) \circ b := f \otimes mb.$$

The canonical element  $u \in V^* \otimes V \subset V^* \otimes M$  is  $\mathfrak{g}_{ad}$ -invariant (i.e., commutes with  $\mathfrak{g}$ ). Thus we have a bimodule homomorphism  $\psi: U(\mathfrak{g}) \to V^* \otimes M$  given by  $\psi(c) := uc = \sum v_i^* \otimes v_i c$ , where  $v_i$  is a basis of V and  $v_i^*$  the dual basis of  $V^*$ . Moreover, since the right infinitesimal character of M is  $\chi$ , this homomorphism descends to  $\overline{\psi}: U_\chi \to V^* \otimes M$ . This gives rise to a nonzero homomorphism of bimodules  $\xi: V \otimes U_\chi \to M$ , where the right  $\mathfrak{g}$ -module structure of V is trivial. Since M is irreducible,  $\xi$  is surjective. Thus the result follows from Corollary 14.4.

#### 15. Category $\mathcal{O}$ of $\mathfrak{g}$ -modules - I

15.1. Category  $\mathcal{O}$ . Let  $\mathfrak{g}$  be a semisimple complex Lie algebra.

**Definition 15.1.** The category  $\mathcal{O} = \mathcal{O}_{\mathfrak{g}}$  is the full subcategory of  $\mathfrak{g}$ -mod, which consists of finitely generated  $\mathfrak{g}$ -modules M with weight decomposition and  $P(M) \subset \bigcup_{i=1}^{m} (\lambda_i - Q_+)$ , where  $\lambda_1, ..., \lambda_m \in \mathfrak{h}^*$ .

It is clear that  $\mathcal{O}$  is closed under taking subquotients and direct sums, so it is an abelian category (recall that a submodule of a finitely generated  $\mathfrak{g}$ -module is finitely generated since  $U(\mathfrak{g})$  is Noetherian).

Also it is easy to see that any nonzero object  $M \in \mathcal{O}$  has a singular vector (namely, take any nonzero vector of a maximal weight in P(M)). Thus the simple objects (=modules) of  $\mathcal{O}$  are  $L_{\lambda}$ ,  $\lambda \in \mathfrak{h}^*$ .

**Example 15.2.** All highest weight  $\mathfrak{g}$ -modules, in particular a Verma module  $M_{\lambda}$  and its simple quotient  $L_{\lambda}$  belong to  $\mathcal{O}$ . Another example is  $\overline{M}_{-\lambda}^*$ , the restricted dual to the lowest weight Verma module  $\overline{M}_{-\lambda}$ , introduced in Exercise 8.13(ii). This module is called the **contragredient Verma module** and denoted  $M_{\lambda}^{\vee}$ .

**Lemma 15.3.** If  $M \in \mathcal{O}$  then the weight subspaces of M are finite-dimensional.

Proof. Let  $v_1, ..., v_m$  be generators of M which are eigenvectors of  $\mathfrak{h}$  (they exist since M is finitely generated and has weight decomposition). Let  $E := \sum_{i=1}^m U(\mathfrak{h} \oplus \mathfrak{n}_+) v_i = \sum_{i=1}^m U(\mathfrak{n}_+) v_i$ . Then E is finite-dimensional by the condition on the weights of M. On the other hand, the natural map  $U(\mathfrak{n}_-) \otimes E \to M$  is surjective. The lemma follows, as weight subspaces of  $U(\mathfrak{n}_-) \otimes E$  are finite-dimensional.

Let  $\mathcal{R}$  be the ring of series  $F := \sum_{\mu \in \mathfrak{h}^*} c_{\mu} e^{\mu}$ , where  $c_{\mu} \in \mathbb{Z}$  and the set P(F) of  $\mu$  with  $c_{\mu} \neq 0$  is contained in a finite union of sets of the form  $\lambda - Q_+$ ,  $\lambda \in \mathfrak{h}^*$ . If M is an  $\mathfrak{h}$ -semisimple  $\mathfrak{g}$ -module with finite-dimensional weight spaces and weights in a finite union of sets  $\lambda - Q_+$  then we can define the **character** of M,

$$\operatorname{ch}(M) = \sum_{\lambda \in \mathfrak{h}^*} \dim M[\lambda] e^{\lambda} \in \mathcal{R}.$$

For example,

$$\operatorname{ch}(M_{\lambda}) = \frac{e^{\lambda}}{\prod_{\alpha \in R_{+}} (1 - e^{-\alpha})}.$$

We have  $ch(M \otimes N) = ch(M)ch(N)$  and

$$\operatorname{ch}(M) = \operatorname{ch}(L) + \operatorname{ch}(N)$$

when  $0 \to L \to M \to N \to 0$  is a short exact sequence. Lemma 15.3 implies that we can define such characters  $\mathrm{ch}(M)$  for  $M \in \mathcal{O}$ .

Corollary 15.4. The action of  $Z(\mathfrak{g})$  on every  $M \in \mathcal{O}$  factors through a finite-dimensional quotient.

Proof. Since  $Z(\mathfrak{g})$  is finitely generated, it suffices to show that every  $z \in Z(\mathfrak{g})$  satisfies a polynomial equation F(z) = 0 in M. Let  $\mu_1, ..., \mu_k$  be weights such that M is generated by  $E := M[\mu_1] \oplus ... \oplus M[\mu_k]$ . By Lemma 15.3, this space is finite-dimensional, and it is preserved by z. Let F be the minimal polynomial of z on E. Then F(z) = 0 on E, hence on the whole M (as z is central and E generates M).

**Exercise 15.5.** Show that the action of  $Z(\mathfrak{g})$  on any Harish-Chandra  $(\mathfrak{g}, K)$ -module factors through a finite-dimensional quotient. (Mimic the proof of Corollary 15.4).

**Exercise 15.6.** (i) Show that for any  $\mu \in \mathfrak{h}^*$ ,  $\operatorname{Ext}^1_{\mathcal{O}}(M_{\mu}, M_{\mu}) = 0$ .

(ii) Show that  $\operatorname{Ext}^1(M_{\mu}, M_{\mu})$  (Ext in the category of all  $\mathfrak{g}$ -modules) is nonzero.

Corollary 15.7. (i) Any  $M \in \mathcal{O}$  has a canonical decomposition

$$M = \bigoplus_{\chi \in \mathfrak{h}^*/W} M(\chi),$$

where  $M(\chi)$  is the generalized eigenspace of  $Z(\mathfrak{g})$  in M with eigenvalue  $\chi$ , and this direct sum is finite. In other words,

$$\mathcal{O} = \oplus_{\chi \in \mathfrak{h}^*/W} \mathcal{O}_{\chi},$$

where  $\mathcal{O}_{\chi}$  is the subcategory of  $\mathcal{O}$  of modules where every  $z \in Z(\mathfrak{g})$  acts with generalized eigenvalue  $\chi(z)$ .

(ii) Each  $M \in \mathcal{O}_{\chi}$  has a finite filtration with successive quotients having infinitesimal character  $\chi$ .

*Proof.* (i) Let  $R:=Z(\mathfrak{g})/\mathrm{Ann}(M)$  be the quotient of  $Z(\mathfrak{g})$  by its annihilator in M. This algebra is finite-dimensional, so has the form  $R=\prod_{i=1}^m R_i$ , where  $R_i$  are local with units  $\mathbf{e}_i$ , corresponding to the generalized eigenvalues  $\chi_1,...,\chi_m\in\mathfrak{h}^*/W$  of  $Z(\mathfrak{g})$  on M. So  $M=\oplus_{i=1}^m M(\chi_i)$ , where  $M(\chi_i):=\mathbf{e}_iM$ .

(ii) If  $M \in \mathcal{O}_{\chi}$  then the algebra R is local. Let  $\mathfrak{m}$  be its unique maximal ideal. Then the required finite filtration on M is

$$M \supset \mathfrak{m}M \supset \mathfrak{m}^2M...$$

f(0) are I where y = y is  $y \in Y$ 

We can partition the W-orbit  $\chi$  into equivalence classes according to the relation  $\mu \sim \nu$  if  $\mu - \nu \in Q$ . It is clear that this partition defines a decomposition  $\mathcal{O}_{\chi} = \bigoplus_{S} \mathcal{O}_{\chi}(S)$ , where S runs over the equivalence classes in  $\chi$  under the relation  $\sim$ . Namely,  $\mathcal{O}_{\chi}(S)$  is the subcategory of modules with all weights in  $\mu - \rho + Q$ , where  $\mu \in S$ .

**Example 15.8.** Suppose that  $\lambda \in \mathfrak{h}^*$  is such that  $w\lambda - \lambda \notin Q$  for any  $1 \neq w \in W$ . In this case the equivalence relation on  $W\lambda$  is trivial, so for any  $\mu \in W\lambda$  the category  $\mathcal{O}_{\chi_{\lambda}}(\mu)$  has a unique simple object  $M_{\mu-\rho}$ . It thus follows from Exercise 15.6 for any  $\mu \in W\lambda$ , the category  $\mathcal{O}_{\chi_{\lambda}}(\mu)$  is equivalent to the category of finite-dimensional vector spaces (as  $M_{\mu-\rho}$  has no nontrivial self-extensions), and the category  $\mathcal{O}_{\chi_{\lambda}}$  is semisimple with |W| simple objects.

**Lemma 15.9.** Every object of  $\mathcal{O}$  has finite length.

Proof. By Corollary 15.7 we may assume that M has infinitesimal character  $\chi_{\lambda}$ . We may also assume that  $P(M) \subset \mu + Q$  for some  $\mu \in \mathfrak{h}^*$ . Recall that the quadratic Casimir C of  $\mathfrak{g}$  acts on M in the same way as in  $M_{\lambda-\rho}$ , i.e., by the scalar  $\lambda^2 - \rho^2$ . Suppose that v is a singular vector in a nonzero subquotient M' of M of some weight  $\gamma \in \mu + Q$  (it must exist since weights of M' belong to a finite union of  $\lambda_i - Q_+$ ). Then  $Cv = (\gamma^2 - \rho^2)v$ , so we must have

$$\gamma^2 = \lambda^2$$
.

Since the inner product on Q is positive definite, this equation has a finite set S of solutions  $\gamma \in \mu + Q$ .

For a semisimple  $\mathfrak{h}$ -module Y set  $Y[S] := \bigoplus_{\gamma \in S} Y[\gamma]$ . It follows that  $M'[S] \neq 0$ . Also by Lemma 15.3 we have  $\dim M[S] < \infty$ . Thus length $(M) \leq \dim M'[S] \leq \dim M[S]$  is finite, as claimed.  $\square$ 

15.2. **Partial orders of**  $\mathfrak{h}^*$ . Introduce a partial order on  $\mathfrak{h}^*$ : we say that  $\mu \leq \lambda$  if  $\lambda - \mu \in Q_+$  and  $\mu < \lambda$  if  $\mu \leq \lambda$  but  $\mu \neq \lambda$ . We write  $\lambda \geq \mu$  if  $\mu \leq \lambda$  and  $\lambda > \mu$  if  $\mu > \lambda$ .

If  $\mu = s_{\alpha}\lambda$  for some  $\alpha \in R_{+}$  and  $\mu < \lambda$  (i.e.,  $(\lambda, \alpha^{\vee}) \in \mathbb{Z}_{\geq 1}$  and  $\mu = \lambda - (\lambda, \alpha^{\vee})\alpha$ ), then we write  $\mu <_{\alpha} \lambda$ . We write  $\mu \leq \lambda$  if there exist sequences  $\alpha^{1}, ..., \alpha^{m} \in R_{+}$  and  $\mu = \mu_{0}, \mu_{1}, ..., \mu_{m} = \lambda$  such that for all  $i, \mu_{i-1} <_{\alpha^{i}} \mu_{i}$ , and write  $\mu \prec \lambda$  if  $\mu \leq \lambda$  but  $\mu \neq \lambda$  (i.e.,  $m \neq 0$ ). We write  $\lambda \succeq \mu$  if  $\mu \leq \lambda$  and  $\lambda \succ \mu$  if  $\mu \prec \lambda$ .

**Remark 15.10.** It is easy to see that if  $\mu \prec \lambda$  then  $\mu < \lambda$  and  $\mu \in W\lambda$ , but the converse is false, in general. For example, consider the root system of type  $A_3$ , and let us realize  $\mathfrak{h}^*$  as  $\mathbb{C}^4/\mathbb{C}_{\text{diagonal}}$ . Let  $\mu = (0, 3, 1, 2), \lambda = (1, 2, 3, 0)$ . Then  $\mu \in W\lambda$  and  $\mu < \lambda$ , since  $\lambda - \mu = (1, -1, 2, -2) = \alpha_1 + 2\alpha_3$ . However,  $\mu \not\prec \lambda$ . Indeed, otherwise

there would exist  $\alpha \in R_+$  such that  $\mu \leq s_{\alpha}\lambda < \lambda$ , and it is easy to check that there is no such  $\alpha$ .

#### 15.3. Verma's theorem.

**Theorem 15.11.** (D. N. Verma) Let  $\lambda, \mu \in \mathfrak{h}^*$  and  $\mu \leq \lambda$ . Then  $\dim \operatorname{Hom}(M_{\mu-\rho}, M_{\lambda-\rho}) = 1$  and  $M_{\mu-\rho}$  can be uniquely realized as a submodule of  $M_{\lambda-\rho}$ . In particular,  $L_{\mu-\rho}$  occurs in the composition series of  $M_{\lambda-\rho}$ .

Proof. By Exercise 8.14, dim  $\operatorname{Hom}(M_{\mu-\rho}, M_{\lambda-\rho}) \leq 1$  and any nonzero homomorphism  $M_{\mu-\rho} \to M_{\lambda-\rho}$  is injective, so it suffices to show that dim  $\operatorname{Hom}(M_{\mu-\rho}, M_{\lambda-\rho}) \geq 1$ . By definition of the partial order  $\leq$ , it suffices to do so when  $\mu <_{\alpha} \lambda$  for some  $\alpha \in R_+$ , i.e., when  $\mu = s_{\alpha} \lambda = \lambda - n\alpha$  where  $n := (\lambda, \alpha^{\vee}) \in \mathbb{Z}_+$ . For generic  $\lambda$  with  $(\lambda, \alpha^{\vee}) = n \in \mathbb{Z}_+$ , this follows from the Shapovalov determinant formula (Exercise 8.15), and the general case follows by taking the limit.

We will see below that the converse to Verma's theorem also holds: if  $L_{\mu-\rho}$  occurs in the composition series of  $M_{\lambda-\rho}$  then  $\mu \leq \lambda$ . This was proved by J. Bernstein, I. Gelfand and S. Gelfand, see Theorem 20.13 below.

15.4. The stabilizer in W of a point in  $\mathfrak{h}^*/Q$ . Let  $x \in \mathfrak{h}^*/Q$  and  $W_x \subset W$  be the stabilizer of x.

**Proposition 15.12.**  $W_x$  is generated by the reflections  $s_\alpha \in W_x$ . Moreover, the roots  $\alpha$  such that  $s_\alpha \in W_x$  form a root system  $R_x \subset R$ , and  $W_x$  is the Weyl group of  $R_x$ . The corresponding dual root system  $R_x^{\vee}$  is a root subsystem of  $R^{\vee}$ , i.e.,  $R_x^{\vee} = \operatorname{span}_{\mathbb{Z}}(R_x^{\vee}) \cap R^{\vee}$ .

Proof. Let  $T:=\mathfrak{h}^*/Q$ . The ring  $\mathbb{C}[T/W]:=\mathbb{C}[T]^W$  is freely generated by the orbit sums  $m_i=\sum_{\beta\in W\omega_i^\vee}e^\beta$ , where  $\omega_i^\vee$  are the fundamental coweights. Hence T/W is smooth (in fact, an affine space). It follows by the Chevalley-Shephard-Todd theorem that for each  $x\in T$  the stabilizer  $W_x$  is generated by a subset of reflections of W. Moreover, if  $s_\alpha, s_\beta \in W_x$  then  $s_\alpha s_\beta s_\alpha = s_{s_\alpha(\beta)} \in W_x$ , which implies that the set  $R_x$  of  $\alpha$  such that  $s_\alpha \in W_x$  is a root system in R, and  $W_x$  is its Weyl group. Moreover, picking a preimage  $\widetilde{x}$  of x in  $\mathfrak{h}^*$ , we see that  $\alpha \in R_x$  if and only if  $(\alpha^\vee, \widetilde{x}) \in \mathbb{Z}$ . Thus  $R_x^\vee$  is a root subsystem of  $R^\vee$ .

**Remark 15.13.** 1. Note that unlike the case  $x \in \mathfrak{h}^*$ , for  $x \in \mathfrak{h}^*/Q$  the group  $W_x$  is not necessarily a **parabolic** subgroup of W, i.e., it is not necessarily conjugate to a subgroup generated by simple reflections. In fact, the Dynkin diagram of  $R_x$  or  $R_x^{\vee}$  may not be a subdiagram of

the Dynkin diagram of W. Such subgroups are called **quasiparabolic** subgroups.

For example, if R is of type  $B_2$  with simple roots  $\alpha_1 = (1,0)$  and  $\alpha_2 = (-1,1)$  then for  $x = (\frac{1}{2},0)$ ,  $R_x$  is the root system of type  $A_1 \times A_1$  consisting of  $\pm \alpha_1$  and  $\pm (\alpha_1 + \alpha_2)$ . The same example shows that  $R_x$  is not necessarily a root subsystem of R, as  $\alpha_1 + (\alpha_1 + \alpha_2) \notin R_x$ .

2. If  $G^{\vee}$  is the simply connected complex semisimple Lie group corresponding to  $R^{\vee}$  then T is the maximal torus of  $G^{\vee}$ , and it is easy to see that  $R_x^{\vee}$  is the root system of the centralizer  $\mathfrak{z}_x$  of x in  $\mathfrak{g}^{\vee} := \operatorname{Lie}(G^{\vee})$ .

#### 16. Category $\mathcal{O}$ of $\mathfrak{g}$ -modules - II

16.1. **Dominant weights.** Let us say that a weight  $\lambda \in \mathfrak{h}^*$  is **dominant** for the partial order  $\leq$  (respectively,  $\leq$ ) if it is maximal with respect to this order in its equivalence class (or, equivalently, in its W-orbit).

Corollary 16.1. The following conditions on a weight  $\lambda \in \mathfrak{h}^*$  are equivalent:

- (i)  $\lambda$  is dominant for  $\leq$ ;
- (ii)  $\lambda$  is dominant for  $\leq$ ;
- (iii) For every root  $\alpha \in R_+$ ,  $(\lambda, \alpha^{\vee}) \notin \mathbb{Z}_{<0}$ .
- (iv) For every  $w \in W_{\lambda+Q}$ ,  $w\lambda \leq \lambda$ .
- (v) For every  $w \in W_{\lambda+Q}$ ,  $w\lambda \leq \lambda$ .

Proof. It is clear that (iv) implies (v) implies (i) implies (ii). It is also easy to see that (ii) implies (iii), since if  $(\lambda, \alpha^{\vee}) \in \mathbb{Z}_{<0}$  then  $s_{\alpha}\lambda \sim \lambda$  and  $s_{\alpha}\lambda > \lambda$  so  $\lambda$  is not maximal under  $\leq$  in its equivalence class. It remains to show that (iii) implies (iv). By Proposition 15.12,  $W_{\lambda+Q}$  is the Weyl group of some root system  $R' \subset R$ , and the equivalence class S of  $\lambda$  is simply the orbit  $W_{\lambda+Q}\lambda$ . By our assumption, for  $\alpha \in R'_+$  we have  $(\lambda, \alpha^{\vee}) \in \mathbb{Z} \setminus \mathbb{Z}_{<0} = \mathbb{Z}_{\geq 0}$ . Thus,  $\lambda = \lambda' + \nu$  where  $\lambda'$  is a dominant integral weight for R' (meaning that  $(\lambda, \alpha^{\vee}) \in \mathbb{Z}_{\geq 0}$  for  $\alpha \in R'_+$ ) and  $(\nu, \alpha^{\vee}) = 0$  for all  $\alpha \in R'_+$ . Now for any  $w \in W_{\lambda+Q}$ , fix a reduced decomposition  $w = s_{i_m}...s_{i_1}$ , where  $s_i = s_{\beta_i}$  and  $\beta_i$  are the simple roots of R'. Let  $\lambda_k := s_{i_k}...s_{i_1}\lambda$ , so  $\lambda_0 = \lambda$  and  $\lambda_m = w\lambda$ . Setting  $\lambda'_k := s_{i_k}...s_{i_1}\lambda' = \lambda_k - \nu$ , we then have

$$\lambda_{k-1} - \lambda_k = \lambda'_{k-1} - \lambda'_k = (\lambda'_{k-1}, \beta_{i_k}^{\vee}) \beta_{i_k} = (\lambda', s_{i_1} \dots s_{i_{k-1}} \beta_{i_k}^{\vee}) \beta_{i_k}.$$

The coroot  $s_{i_1}...s_{i_{k-1}}\beta_{i_k}^{\vee}$  is positive, so we get that  $\lambda_k \leq \lambda_{k-1}$ , which yields (iv).

Corollary 16.1 shows that every equivalence class of weights contains a unique maximal element with respect to each of the orders  $\leq$  and  $\leq$ , namely the unique dominant weight in this class. The same is true for minimal elements by changing signs.

16.2. **Projective objects.** Let  $\mathcal{C}$  be an abelian category over a field k. Recall that  $\mathcal{C}$  is said to be **Noetherian** if any ascending chain of subobjects of any object  $X \in \mathcal{C}$  stabilizes. This holds, for instance, when objects of  $\mathcal{C}$  have finite length.

Recall also that an object  $P \in \mathcal{C}$  is **projective** if the functor Hom(P, -) is (right) exact, and that  $\mathcal{C}$  is said to have **enough projectives** if every object  $L \in \mathcal{C}$  is a quotient of a projective object P. Note that if

objects of  $\mathcal{C}$  have finite length then it is sufficient for this to hold for every simple L, then the property can be proved for all L by induction in length. Indeed, suppose we have a short exact sequence

$$0 \rightarrow L_1 \rightarrow L \rightarrow L_2 \rightarrow 0$$

with  $L_1, L_2 \neq 0$  and projectives  $P_1, P_2$  with epimorphisms  $p_j : P_j \twoheadrightarrow L_j$ . Then the map  $p_2$  lifts to  $\widetilde{p}_2 : P_2 \to L$ , which yields an epimorphism  $p_1 + \widetilde{p}_2 : P_1 \oplus P_2 \twoheadrightarrow L$ .

Suppose that Hom spaces in  $\mathcal{C}$  are finite-dimensional. Then by the **Krull-Schmidt theorem**, every object of  $\mathcal{C}$  has a unique representation as a finite direct sum of indecomposable ones (up to isomorphism and permutation of summands).

**Proposition 16.2.** Let C be a Noetherian abelian category with enough projectives and finite-dimensional Hom spaces over an algebraically closed field k. Then

- (i) Let I be the set labeling the isomorphism classes of indecomposable projectives  $P_i$  of C. Then the isomorphism classes of simple objects  $L_i$  of C are labeled by the same set I, and dim  $\text{Hom}(P_i, L_j) = \delta_{ij}$ ,  $i, j \in I$ .
- (ii) For  $M \in \mathcal{C}$  of finite length, the multiplicities  $[M : L_i]$  equal  $\dim \operatorname{Hom}(P_i, M)$ .

*Proof.* Let  $P \in \mathcal{C}$  be an indecomposable projective. Then  $\operatorname{End}(P)$  has no idempotents other than 0, 1, so  $\operatorname{End}(P) = k \oplus N$  where N is the nilradical, i.e., it is a local algebra.

Suppose  $Q \subset P$  is a maximal proper subobject (it exists by Zorn's lemma since C is Noetherian). Let  $Q' \subset P$  be a subobject not contained in Q. Then Q + Q' = P. So we have an epimorphism  $Q \oplus Q' \to P$ , which, by the projectivity of P, gives a surjection

$$\operatorname{Hom}(P,Q) \oplus \operatorname{Hom}(P,Q') \to \operatorname{End}(P).$$

So we have  $1_P = a + a'$ , where  $a, a' : P \to P$  factor through Q, Q'. Thus a is not an isomorphism (since Q is proper). As  $\operatorname{End}(P)$  is local, it follows that a' is an isomorphism, so Q' = P.

It follows that P has a unique maximal proper subobject J(P), and  $L_P := P/J(P)$  is simple. Moreover, if L := P/Q is simple then Q = J(P), so  $L = L_P$ . So if I' labels the isomorphism classes of simples in C, then we get a map  $\ell : I \to I'$  such that  $\ell(P) = L_P$ , and we have dim  $\operatorname{Hom}(P_i, L_{i'}) = \delta_{\ell(i),i'}$ . Moreover,  $\ell$  is surjective since every simple L is a quotient of some projective P which may be chosen indecomposable (if  $P \to L$  and  $P = \bigoplus_{i=1}^N P_i$  where  $P_i$  are indecomposable then there exists i such that the map  $P_i \to L$  is nonzero, hence an epimorphism as L is simple).

It remains to show that  $\ell$  is injective, i.e., if  $L_m \cong L_n$  then  $P_m \cong P_n$ . To this end, note that the epimorphisms  $a_0: P_m \to L_n$ ,  $b_0: P_n \to L_m$  lift to morphisms  $a: P_m \to P_n$ ,  $b: P_n \to P_m$ , such that  $ab \in \operatorname{End}(P_n)$  and  $ba \in \operatorname{End}(P_m)$  are not nilpotent (as they define isomorphisms on the corresponding simple quotients). Since the algebras  $\operatorname{End}(P_n)$ ,  $\operatorname{End}(P_m)$  are local, it follows that ab and ba are isomorphisms, as claimed.

This proves (i). Part (ii) now follows from the exactness of the functor  $\text{Hom}(P_i,?)$ .

The object  $P_i$  is called the **projective cover** of  $L_i$ , and  $L_i$  is called the **head** of  $P_i$ ; by Proposition 16.2, it is the unique simple quotient of  $P_i$ .

Remark 16.3. In general, objects of a category satisfying the assumptions of Proposition 16.2 need not have finite length. An example when they can have infinite length is the category of finitely generated  $\mathbb{Z}$ -graded  $\mathbb{C}[x]$ -modules, where  $\deg(x) = 1$ . The simple objects in this category are 1-dimensional modules  $L_n$ ,  $n \in \mathbb{Z}$ , which sit in degree n (with x acting by zero). The projective cover of  $L_n$  is  $P_n = \mathbb{C}[x]_n$ , the free rank 1 module sitting in degrees n, n+1, ..., which has infinite length.

#### 16.3. Projective objects in $\mathcal{O}$ .

**Proposition 16.4.** If  $\lambda$  is dominant then  $M_{\lambda-\rho}$  is a projective object in  $\mathcal{O}^{19}$ 

Proof. Our job is to show that the functor  $\operatorname{Hom}(M_{\lambda-\rho}, \bullet)$  is exact on  $\mathcal{O}$ . It suffices to show this on  $\mathcal{O}_{\chi_{\lambda}}(S)$ , where S is the equivalence class of  $\lambda$ . To this end, note that all weights of any  $X \in \mathcal{O}_{\chi_{\lambda}}(S)$  are not  $> \lambda - \rho$ . Thus every  $v \in X[\lambda - \rho]$  is singular, so there is a unique homomorphism  $M_{\lambda-\rho} \to X$  sending  $v_{\lambda-\rho}$  to v. It follows that that  $\operatorname{Hom}(M_{\lambda-\rho}, X) \cong X[\lambda - \rho]$ , which implies the statement.  $\square$ 

Now let V be a finite-dimensional  $\mathfrak{g}$ -module. Then we have an exact functor  $V \otimes : \mathcal{O} \to \mathcal{O}$ .

Corollary 16.5. (i) If  $P \in \mathcal{O}$  is projective then so is  $V \otimes P$ . (ii) If  $\lambda \in \mathfrak{h}^*$  is dominant then the object  $V \otimes M_{\lambda - \rho} \in \mathcal{O}$  is projective.

*Proof.* (i) For  $X \in \mathcal{O}$ 

$$\operatorname{Hom}_{\mathfrak{g}}(V \otimes P, X) = \operatorname{Hom}_{\mathfrak{g}}(P, V^* \otimes X),$$

 $<sup>^{19}</sup>$  Note that this does not mean that  $M_{\lambda}$  is a projective  $U(\mathfrak{g})$  -module; in fact, it is not.

which is exact since P is projective.

(ii) follows from (i) and Proposition 16.4.

Corollary 16.6. (i) For every  $\mu \in \mathfrak{h}^*$ , there exists dominant  $\lambda \in \mathfrak{h}^*$  and a finite-dimensional  $\mathfrak{g}$ -module V such that  $\operatorname{Hom}(V \otimes M_{\lambda-\rho}, L_{\mu}) \neq 0$ . Thus  $\mathcal{O}$  has enough projectives.

(ii) Every projective object P of  $\mathcal{O}$  is a free  $U(\mathfrak{n}_{-})$ -module.

Proof. (i) We have

$$\operatorname{Hom}(V \otimes M_{\lambda-\rho}, L_{\mu}) = \operatorname{Hom}_{\mathfrak{g}}(M_{\lambda-\rho}, V^* \otimes L_{\mu}).$$

Now take  $V = V^* = L_{N\rho}$  for large N and  $\lambda = \mu + (N+1)\rho$ . It is clear that  $\lambda$  is dominant, and  $\operatorname{Hom}_{\mathfrak{g}}(M_{\lambda-\rho}, V^* \otimes L_{\mu}) = \mathbb{C}$ , as claimed.

(ii) This follows by Lemma 12.3 since every indecomposable projective object  $P \in \mathcal{O}$  is an  $\mathfrak{h}^*$ -graded direct summand in  $V \otimes M_{\lambda-\rho}$ , which is a free graded  $U(\mathfrak{n}_-)$ -module.

It follows that every simple object  $L_{\lambda}$  of  $\mathcal{O}$  has a projective cover  $P_{\lambda}$ , with dim  $\operatorname{Hom}(P_{\lambda}, L_{\mu}) = \delta_{\lambda\mu}$ .

#### 17. The nilpotent cone of g

17.1. The nilpotent cone. Let  $(S\mathfrak{g})_0$  be the quotient of  $S\mathfrak{g}$  by the ideal generated by the positive degree part of  $(S\mathfrak{g})^{\mathfrak{g}}$ , i.e. by the free homogeneous generators  $p_1, ..., p_r$  of  $(S\mathfrak{g})^{\mathfrak{g}}$  (which exist by Kostant's theorem). The scheme

$$\mathcal{N} := \operatorname{Spec}(S\mathfrak{g})_0 \subset \mathfrak{g}^* \cong \mathfrak{g}$$

is called the **nilpotent cone** of  $\mathfrak{g}$ . It follows from the Kostant theorem that  $p_1, ..., p_r$  is a regular sequence, i.e., this scheme is a complete intersection of codimension r in  $\mathfrak{g}$  (see Remark 12.11), i.e., of dimension

$$\dim \mathcal{N} = \dim \mathfrak{g} - r = |R| = 2|R_+| = 2\dim \mathfrak{n}_+,$$

the number of roots of  $\mathfrak{g}$ .

Let  $x \in \mathfrak{g}$  be a nilpotent element. Recall that then x is conjugate to an element  $y \in \mathfrak{n}_+$  and  $\mathrm{Ad}(t^{2\rho^\vee})y \to 0$  as  $t \to 0$ , where  $\rho^\vee$  is the half-sum of positive coroots of  $\mathfrak{g}$ . Thus  $p_i(x) = p_i(y) = 0$  and hence  $x \in \mathcal{N}(\mathbb{C})$ . On the other hand, if x is not nilpotent then  $\mathrm{ad}(x)$  is not a nilpotent operator, so  $\mathrm{Tr}(\mathrm{ad}(x)^N) \neq 0$  for some N, hence  $x \notin \mathcal{N}(\mathbb{C})$ . It follows that  $\mathcal{N}(\mathbb{C})$  is exactly the set of nilpotent elements of  $\mathfrak{g}$ , hence the term "nilpotent cone".

For example, for  $\mathfrak{g} = \mathfrak{sl}_2$  we have r = 1 and

$$p_1(A) = -\det A = x^2 + yz$$

for  $A := \begin{pmatrix} x & y \\ z & -x \end{pmatrix} \in \mathfrak{g}$ , so  $\mathcal{N}$  is the usual quadratic cone in  $\mathbb{C}^3$  defined by the equation  $x^2 + yz = 0$ .

17.2. The principal  $\mathfrak{sl}_2$  subalgebra. The principal  $\mathfrak{sl}_2$  subalgebra of  $\mathfrak{g}$  is the subalgebra spanned by  $e := \sum_{i=1}^r e_i$ ,  $f := \sum_i c_i f_i$  and  $h := [e, f] = \sum_i c_i h_i = 2\rho^{\vee}$ . Thus  $c_i$  are found from the equations  $\sum_i c_i a_{ij} = 2$  for all j, where  $A = (a_{ij})$  is the Cartan matrix of  $\mathfrak{g}$ .

**Lemma 17.1.** The restriction of the adjoint representation of  $\mathfrak{g}$  to its principal  $\mathfrak{sl}_2$ -subalgebra is isomorphic to  $L_{2m_1} \oplus ... \oplus L_{2m_r}$  for appropriate  $m_i \in \mathbb{Z}_{>0}$ .

Proof. Consider the corresponding action of the group  $SL_2(\mathbb{C})$ . The element  $-1 \in SL_2(\mathbb{C})$  acts on  $\mathfrak{g}$  by  $\exp(2\pi i \rho^{\vee}) = 1$  since  $\rho^{\vee}$  is an integral coweight. Thus only even highest weight  $\mathfrak{sl}_2$ -modules may occur in the decomposition of  $\mathfrak{g}$ . Since  $\rho^{\vee}$  is regular, the 0-weight space of this module (the centralizer  $Z_{\mathfrak{g}}(\rho^{\vee})$ ) is  $\mathfrak{h}$ , i.e., has dimension r. Thus  $\mathfrak{g}$  has r indecomposable direct summands over the principal  $\mathfrak{sl}_2$ , as claimed.

The numbers  $m_i$  (arranged in non-decreasing order) are called the **exponents** of  $\mathfrak{g}$ . We will soon see that  $m_i = d_i - 1$ , where  $d_i$  are the degrees of  $\mathfrak{g}$ .

17.3. Regular elements. Recall that  $x \in \mathfrak{g}$  is regular if the dimension of its centralizer is  $r = \operatorname{rank}\mathfrak{g}$  (the smallest it can be). Thus regular elements form an open set  $\mathfrak{g}_{\operatorname{reg}} \subset \mathfrak{g}$ .

**Lemma 17.2.** The element  $e = \sum_{i=1}^{r} e_i$  is regular.

*Proof.* By Lemma 17.1, the centralizer  $Z_{\mathfrak{g}}(e)$  is spanned by the highest vectors of the representations  $L_{2m_1},...,L_{2m_r}$ , hence has dimension r.

Corollary 17.3. Let  $B_+$  be the Borel subgroup of G with Lie algebra  $\mathfrak{b}_+ := \mathfrak{h} \oplus \mathfrak{n}_+$ . Then  $\mathrm{Ad}(B_+)e$  is the set of elements  $\sum_{\alpha \in R_+} c_\alpha e_\alpha$  with  $c_\alpha \in \mathbb{C}$  and  $c_{\alpha_i} \neq 0$  for all i.

*Proof.* Since by Lemma 17.2 dim  $Z_{\mathfrak{g}}(e) = r$ , we have

$$\dim[e, \mathfrak{n}_+] \ge |R_+| - r = \dim[\mathfrak{n}_+, \mathfrak{n}_+].$$

Since  $[e, \mathfrak{n}_+] \subset [\mathfrak{n}_+, \mathfrak{n}_+]$ , we get that  $[e, \mathfrak{n}_+] = [\mathfrak{n}_+, \mathfrak{n}_+]$ . It follows that if  $N_+ = \exp(\mathfrak{n}_+)$  then  $\operatorname{Ad}(N_+)e = e + [\mathfrak{n}_+, \mathfrak{n}_+]$  is the set of expressions  $\sum_{\alpha \in R_+} c_\alpha e_\alpha$  with  $c_{\alpha_i} = 1$  for all i. The statement follows by adding the action of the maximal torus  $H = \exp(\mathfrak{h})$ , which allows to set  $c_{\alpha_i}$  to arbitrary nonzero values.

#### 17.4. Properties of the nilpotent cone.

Proposition 17.4. The nilpotent cone is reduced.

Proposition 17.4 is proved in the following exercise.

Exercise 17.5. Let  $\mathfrak{g}$  be a finite-dimensional simple Lie algebra.

- (i) Let  $R_0$  be the graded algebra in Theorem 12.2. Show that the top degree of this algebra is  $D := \sum_{i=1}^r (d_i 1)$  and  $R_0[D] = \mathbb{C}\Delta$ , where  $\Delta := \prod_{\alpha \in R_+} \alpha$ . Deduce that  $\sum_{i=1}^r (d_i 1) = |R_+|$ , the number of positive roots.
- (ii) Let  $\mathfrak{g} = \bigoplus_{i=1}^r L_{2m_i}$  be the decomposition of  $\mathfrak{g}$  as a module over the principal  $\mathfrak{sl}_2$ -subalgebra (e, f, h) given by Lemma 17.1, i.e.,  $m_i$  are the exponents of  $\mathfrak{g}$ . Show that  $m_1 = 1$  and  $\sum_{i=1}^r m_i = |R_+|$ . Moreover, show that if  $\mu_{\mathfrak{g}}$  is the partition  $(m_r, ..., m_1)$  then the conjugate partition  $\mu_{\mathfrak{g}}^{\dagger}$  is  $(n_1, ..., n_{h-1})$ , where  $n_i$  is the number of positive roots  $\alpha$  of height i (i.e.,  $(\rho^{\vee}, \alpha) = i$ ) and  $h := m_r + 1$ . Conclude that  $h = (\rho^{\vee}, \theta) + 1$  where  $\theta$  is the maximal root, i.e., the **Coxeter number** of  $\mathfrak{g}$ .

(iii)(a) Let  $b_i$  be the lowest weight vectors of  $L_{2m_i}$ , and

$$\mathfrak{z}_f := \bigoplus_{i=1}^r \mathbb{C} b_i \subset \mathfrak{g}$$

be the centralizer of f. Show that  $\mathfrak{g} = \mathfrak{z}_f \oplus T_e O_e$ , where  $O_e = \mathrm{Ad}(G)e$  is the orbit of e. Thus the affine space  $e + \mathfrak{z}_f$  is transversal to  $O_e$  at e. This affine space is called the **Kostant slice**.

(iii)(b) Consider the  $\mathbb{C}^{\times}$ -action on  $\mathfrak{g}$  given by

$$t \circ x = t^{\frac{1}{2}\operatorname{ad}(h) - 1}x.$$

Show that this action preserves the decomposition of (ii), and the linear coordinates  $b_i^*$  on  $\mathfrak{z}_f$  have homogeneity degrees  $m_i+1$  under this action.

(iv) Let  $(S\mathfrak{g}^*)^{\mathfrak{g}} = \mathbb{C}[p_1, ..., p_r]$ , deg  $p_i = d_i$ , and let  $\widetilde{p}_i(y) := p_i(e+y)$ ,  $y \in \mathfrak{z}_f$ . Show that  $\widetilde{p}_i$  are polynomials of  $b_j^*$  homogeneous under the  $\mathbb{C}^\times$ -action of (iii) of degrees  $d_i$ . Deduce from this and the identity  $\sum_i (d_i - 1) = \sum_i m_i$  proved in (i),(ii) that

$$d_i - 1 = m_i$$

and thus  $\widetilde{p}_i = b_i^*$  (under appropriate choice of basis). Conclude that the differentials  $dp_i$  are linearly independent at  $e \in \mathfrak{g}$ .

- (v) Work out (i)-(iv) explicitly for  $\mathfrak{g} = \mathfrak{sl}_n$ .
- (vi) Prove Proposition 17.4. **Hint:** View  $\mathcal{O}(\mathcal{N})$  as an algebra over  $\mathcal{R} := S\mathfrak{n}_+ \otimes S\mathfrak{n}_-$ . Use the arguments of Subsection 13.1 to show that it is a free  $\mathcal{R}$ -module of rank |W|. Show that the specialization of  $\mathcal{O}(\mathcal{N})$  at a generic point  $z \in \mathfrak{n}_+^* \times \mathfrak{n}_-^*$  is a semisimple algebra of dimension |W| (use (iv)). Now take  $f \in \mathcal{O}(\mathcal{N})$  such that  $f^k = 0$  for some k, and deduce that the specialization of f at z is zero. Conclude that f = 0.

**Proposition 17.6.** (i) The orbit  $O_e := Ad(G)e$  is open and dense in  $\mathcal{N}$ .

- (ii) All regular nilpotent elements in g are conjugate to e.
- (iii)  $\mathcal{N}$  is an irreducible affine variety. Thus  $(S\mathfrak{g})_0$  is an integral domain.
- *Proof.* (i) This follows from Corollary 17.3 and the fact that every nilpotent element in  $\mathfrak{g}$  can be conjugated into  $\mathfrak{n}_+$ .
- (ii) The orbit  $O_x$  of every regular nilpotent element x has the same dimension as  $O_e$ , so the statement follows from (i). Indeed, since  $O_e$  is open and dense,  $\mathcal{N} \setminus O_e$  has smaller dimension than  $\mathcal{N}$ , hence can't contain  $O_x$ .
- (iii) follows from (i) and Proposition 17.4, since  $O_e$  is smooth and connected (being an orbit of a connected group), hence irreducible.  $\square$

Corollary 17.7.  $U_{\chi}$  is an integral domain for all  $\chi$ .

*Proof.* This follows from Proposition 17.6(iii) since  $gr(U_{\chi}) = (S\mathfrak{g})_0$ .  $\square$ 

- **Exercise 17.8.** Let e be a nilpotent element in a semisimple complex Lie algebra  $\mathfrak{g}$ , and  $\mathfrak{g}^e$  be the centralizer of e. Let (,) be the Killing form of  $\mathfrak{g}$ .
- (i) Show that  $(e, \mathfrak{g}^e) = 0$  (prove that for any  $x \in \mathfrak{g}^e$ , the operator  $\mathrm{ad}_e \mathrm{ad}_x$  is nilpotent).
- (ii) Show that there exists  $h \in \mathfrak{g}$  such that [h, e] = 2e (use that  $\operatorname{Im}(\operatorname{ad}_e) = \mathfrak{g}^{e^{\perp}}$  to deduce that  $e \in \operatorname{Im}(\operatorname{ad}_e)$ ).
- (iii) Show that in (ii), h can be chosen semisimple (consider the Jordan decomposition h = s + n). From now on we choose h in such a way.
  - (iv) Show that  $\mathbb{C}h \oplus \mathfrak{g}^e$  is a Lie subalgebra of  $\mathfrak{g}$ .
- (v) Assume that  $\mathfrak{g}^e$  is nilpotent. Show that there is a basis of  $\mathfrak{g}$  in which the operator  $\mathrm{ad}_x$  is upper triangular for all  $x \in \mathbb{C}h \oplus \mathfrak{g}^e$  (use Lie's theorem). Deduce that (h,x)=0 for all  $x \in \mathfrak{g}^e$ .
- (vi) Show that if  $\mathfrak{g}^e$  is nilpotent then there are  $h, f \in \mathfrak{g}$  such that [h, e] = 2e, [e, f] = h and [h, f] = -2f. In other words, there is a homomorphism of Lie algebras  $\phi : \mathfrak{sl}_2 \to \mathfrak{g}$  such that  $\phi(E) = e$ ,  $\phi(H) = h$ ,  $\phi(F) = f$ . Show that h is semisimple and f is nilpotent.
- (vii) (Jacobson-Morozov theorem, part I) Show that the conclusion of (vi) holds for any e (without assuming that  $\mathfrak{g}^e$  is nilpotent). (**Hint:** use induction in dim  $\mathfrak{g}$ . If  $\mathfrak{g}^e$  is not nilpotent, use Jordan decomposition to find a nonzero semisimple element  $x \in \mathfrak{g}^e$  and consider the Lie algebra  $\mathfrak{g}^x$ . Show that  $\mathfrak{g}' := [\mathfrak{g}^x, \mathfrak{g}^x]$  is semisimple and  $e \in \mathfrak{g}'$ ).
- (viii) Show that for given e, h, the homomorphism  $\phi$  in (vi,vii) is unique (i.e., f is uniquely determined by e, h).
- (ix) (Jacobson-Morozov theorem, part II) Show that for a fixed e,  $\exp(\mathfrak{g}^e)$  (the Lie subgroup corresponding to  $\mathfrak{g}^e$ ) is a closed Lie subgroup of the adjoint group  $G_{\rm ad}$  corresponding to  $\mathfrak{g}$ , and the element h (hence also f) can be chosen uniquely up to conjugation by  $\exp(\mathfrak{g}_e)$ . (**Hint**: Let h' be another choice of h, and consider the element  $h' h \in \mathfrak{g}^e$ .)
- (x) Explain why the Jacobson-Morozov theorem extends to reductive Lie algebras (where by a nilpotent element we mean one that is nilpotent in any finite-dimensional representation). Give an elementary proof of this theorem for  $\mathfrak{g} = \mathfrak{gl}_n$  using only linear algebra.
- (xi) Show that there are finitely many conjugacy classes of nilpotent elements in  $\mathfrak{g}$ , i.e., the nilpotent cone  $\mathcal{N}$  has finitely many  $G_{\mathrm{ad}}$ -orbits. (**Hint:** Consider the variety X of homomorphisms  $\phi: \mathfrak{sl}_2 \to \mathfrak{g}$  and show that it is a disjoint union of finitely many closed  $G_{\mathrm{ad}}$ -orbits. To this end, show that the tangent space to X at each  $x \in X$  coincides with the tangent space of the orbit Gx at the same point, using that  $\mathrm{Ext}^1_{\mathfrak{sl}_2}(\mathbb{C},\mathfrak{g})=0$ ).

#### 18. Maps of finite type, Duflo-Joseph theorem

18.1. Maps of finite type. Let M, N be  $\mathfrak{g}$ -modules. Let  $\operatorname{Hom}_{\operatorname{fin}}(M, N)$  be the space of linear maps from M to N which generate a finite-dimensional  $\mathfrak{g}$ -module under the adjoint action  $a \circ T := [a, T]$ . The elements of  $\operatorname{Hom}_{\operatorname{fin}}(M, N)$  are called **linear maps of finite type**. For example, a module homomorphism is a map of finite type, as it generates a trivial 1-dimensional  $\mathfrak{g}$ -module.

**Exercise 18.1.** Show that any map of finite type has the form  $(f \otimes 1) \circ \Phi$ , where  $f \in V^*$  for some finite-dimensional  $\mathfrak{g}$ -module V and  $\Phi: M \to V \otimes N$  is a module homomorphism.

Note that  $\operatorname{Hom}_{\operatorname{fin}}(M,N)$  is a  ${\mathfrak g}$ -bimodule with bimodule structure given by

$$(a,b) \circ T := aT + Tb,$$

 $a, b \in \mathfrak{g}$ . Moreover, it is clear that if M has infinitesimal character  $\chi$  and N has infinitesimal character  $\theta$  then  $\operatorname{Hom}_{\operatorname{fin}}(M, N)$  has infinitesimal character  $(\theta, \chi)$ .

**Proposition 18.2.** If  $M, N \in \mathcal{O}$  then  $\operatorname{Hom}_{fin}(M, N)$  is an admissible  $\mathfrak{g}$ -bimodule.

*Proof.* We must show that for every simple finite-dimensional  $\mathfrak{g}$ -module V, the space

$$\operatorname{Hom}_{\mathfrak{g}}(V,\operatorname{Hom}_{\operatorname{fin}}(M,N))=\operatorname{Hom}_{\mathfrak{g}}(V,\operatorname{Hom}_{\mathbb{C}}(M,N))$$

is finite-dimensional. Let  $\mu(M, N, V)$  be its dimension (a nonnegative integer or infinity). Since the functor  $(M, N) \mapsto \operatorname{Hom}_{\mathbb{C}}(M, N)$  is exact in both arguments, for any short exact sequence

$$0 \to M_1 \to M_2 \to M_3 \to 0$$

we have

$$\mu(M_2, N, V) = \mu(M_1, N, V) + \mu(M_3, N, V),$$
  
$$\mu(N, M_2, V) = \mu(N, M_1, V) + \mu(N, M_3, V).$$

Thus, since M, N have finite length, it suffices to establish the result for M, N simple. Then M is a quotient of  $M_{\lambda}$  and N a submodule of  $M_{\mu}^{\vee}$  for some  $\lambda, \mu$ , so  $\operatorname{Hom}_{\mathbb{C}}(M, N) \subset \operatorname{Hom}_{\mathbb{C}}(M_{\lambda}, M_{\mu}^{\vee})$ . But by Exercise 8.13, for any finite-dimensional  $\mathfrak{g}$ -module V,

$$\operatorname{Hom}_{\mathfrak{g}}(V, \operatorname{Hom}_{\mathbb{C}}(M_{\lambda}, M_{\mu}^{\vee})) \cong \operatorname{Hom}_{\mathfrak{g}}(V \otimes M_{\lambda}, M_{\mu}^{\vee}) \cong$$

$$\operatorname{Hom}_{\mathfrak{g}}(M_{\lambda}, V^* \otimes M_{\mu}^{\vee}) \cong V^*[\lambda - \mu].$$

This implies the statement.

**Proposition 18.3.** For  $M, N \in \mathcal{O}$  and a finite-dimensional  $\mathfrak{g}$ -module V we have

$$\operatorname{Hom}_{\operatorname{fin}}(M, V \otimes N) = V \otimes \operatorname{Hom}_{\operatorname{fin}}(M, N).$$

Exercise 18.4. Prove Proposition 18.3.

**Proposition 18.5.** Let V be a finite-dimensional  $\mathfrak{g}$ -module. Then for any  $\lambda \in \mathfrak{h}^*$ , we have

$$\dim \operatorname{Hom}_{\mathfrak{a}}(M_{\lambda}, V \otimes M_{\lambda}) = \dim V[0].$$

Thus the multiplicity of V in  $\operatorname{Hom}_{\operatorname{fin}}(M_{\lambda}, M_{\lambda})$  equals  $\dim V[0]$ .

Proof. By Exercise 8.14, the statement holds if  $M_{\lambda}$  is irreducible, i.e., generically. Thus dim  $\operatorname{Hom}_{\mathfrak{g}}(M_{\lambda}, V \otimes M_{\lambda}) \geq \dim V[0]$ , and it remains to prove the opposite inequality. Let  $M_{\mu}$  be the simple Verma submodule of  $M_{\lambda}$ . Given  $\Phi: M_{\lambda} \to V \otimes M_{\lambda}$ , we claim that the restriction of  $\Phi$  to  $M_{\mu}$  must land in  $V \otimes M_{\mu}$ . Indeed, otherwise we will have a nonzero (hence injective) homomorphism  $M_{\mu} \to V \otimes (M_{\lambda}/M_{\mu})$ , which is impossible by growth considerations.

But by Exercise 8.14, the statement holds if  $\lambda$  is replaced by  $\mu$ . So if it does not hold for  $\lambda$  then there is a nonzero  $\Phi$  which kills  $M_{\mu}$ . Thus  $\Phi$  defines a nonzero homomorphism  $M_{\lambda}/M_{\mu} \to M_{\lambda} \otimes V$ , which is impossible since  $M_{\lambda} \otimes V$  is a free, hence torsion free  $U(\mathfrak{n}_{-})$ -module, while every homogeneous vector in  $M_{\lambda}/M_{\mu}$  is torsion (as this module does not contain free  $U(\mathfrak{n}_{-})$ -submodules by growth considerations). This establishes the proposition.

**Remark 18.6.** Note that Proposition 18.5 does not extend to maps  $M_{\lambda+\nu} \to V \otimes M_{\lambda}$  where  $\nu \in P$  is nonzero. Namely, if  $M_{\lambda}$  is irreducible then we have  $\dim \operatorname{Hom}_{\mathfrak{g}}(M_{\lambda+\nu}, V \otimes M_{\lambda}) = \dim V[\nu]$ , so in general  $\dim \operatorname{Hom}_{\mathfrak{g}}(M_{\lambda+\nu}, V \otimes M_{\lambda}) \geq \dim V[\nu]$ , and the inequality can, in fact, be strict. The simplest example is  $\mathfrak{g} = \mathfrak{sl}_2$ ,  $V = \mathbb{C}$ ,  $\lambda = 0$ ,  $\nu = -2$ , in which case the left hand side is 1 and the right hand side is 0.

Also the expectation value map

$$\langle,\rangle: \operatorname{Hom}_{\mathfrak{g}}(M_{\lambda}, V \otimes M_{\lambda}) \to V[0]$$

need not be an isomorphism, even though its source and target have the same dimension. The simplest example is  $\mathfrak{g} = \mathfrak{sl}_2$ ,  $\lambda = 0$ , and V is the adjoint representation. We have

$$\dim \operatorname{Hom}_{\mathfrak{g}}(M_0, V \otimes M_0) = \dim \operatorname{Hom}_{\mathfrak{g}}(M_0, V \otimes M_{-2}) = 1,$$

so the only (up to scaling) nonzero homomorphism  $\Phi: M_0 \to V \otimes M_0$  in fact lands in  $V \otimes M_{-2} \subset V \otimes M_0$ . Thus  $\langle \Phi \rangle = 0$ .

#### 18.2. The Duflo-Joseph theorem.

Proposition 18.7. The action homomorphism

$$\phi: U_{\chi_{\lambda+\alpha}} \to \operatorname{Hom}_{\operatorname{fin}}(M_{\lambda}, M_{\lambda})$$

is injective.

*Proof.* Let  $M_{\mu} \subset M_{\lambda}$  be a simple Verma submodule with highest weight vector v. Let  $B_{\mu,\beta}: U(\mathfrak{n}_+)[\beta] \otimes U(\mathfrak{n}_-)[-\beta] \to \mathbb{C}$  be the pairing defined by the equality

$$abv = B_{\mu,\beta}(a,b)v.$$

As  $M_{\mu}$  is simple, this pairing is nondegenerate.

Consider the multiplication map

$$\xi: U(\mathfrak{n}_{-}) \otimes U(\mathfrak{n}_{+}) \to U_{\chi_{\lambda+\rho}}.$$

We claim that the map  $\phi \circ \xi$  is injective, hence so are  $\xi$  and  $\phi|_{\operatorname{Im}\xi}$ . Indeed, let  $x \in U(\mathfrak{n}_-) \otimes U(\mathfrak{n}_+)$  be a nonzero element. We can uniquely write  $x = \sum_{\alpha \in Q_+} x_{\alpha}$ , where  $x_{\alpha} \in U(\mathfrak{n}_-) \otimes U(\mathfrak{n}_+)[\alpha]$ . Let  $\beta \in Q_+$  be a minimal element such that  $x_{\beta} = \sum_i b_i \otimes a_i \neq 0$ , where  $\{a_i\}$  is a basis of  $U(\mathfrak{n}_+)[\beta]$ . Let  $\{a_i^*\}$  be the dual basis of  $U(\mathfrak{n}_-)[-\beta]$  with respect to  $B_{\mu,\beta}$ . Then

$$(\phi \circ \xi)(x)a_i^*v = b_jv.$$

Since  $b_j$  are not all zero, there exists j such that  $b_j v \neq 0$ . It follows that  $(\phi \circ \xi)(x) \neq 0$ , as claimed.

Thus, denoting the PBW filtration by  $F_n$ , we have

$$\dim F_n(U_{\chi_{\lambda+n}}/\mathrm{Ker}\phi) \ge \dim F_n(U(\mathfrak{n}_-) \otimes U(\mathfrak{n}_+)) \ge Cn^{\dim \mathfrak{g}-r}$$

for some C>0. On the other hand, assume that  $\mathrm{Ker}\phi\neq 0$  and consider the nonzero ideal

$$\operatorname{gr}(\operatorname{Ker}\phi) \subset (S\mathfrak{g})_0 = \mathcal{O}(\mathcal{N}).$$

This ideal contains a principal ideal  $\mathcal{O}(\mathcal{N})f$ , where  $f \in \mathcal{O}(\mathcal{N})$  is a nonzero homogeneous element. Since  $\mathcal{O}(\mathcal{N})$  is a domain (Proposition 17.6(iii)), this ideal is a free  $\mathcal{O}(\mathcal{N})$ -module generated by f.

$$\dim F_n(U_{\chi_{\lambda+\rho}}/\mathrm{Ker}\phi) = \dim \mathrm{gr}_{\leq n}(\mathcal{O}(\mathcal{N})/\mathrm{gr}(\mathrm{Ker}\phi))$$

$$\leq \dim \operatorname{gr}_{\leq n}(\mathcal{O}(\mathcal{N})/\mathcal{O}(\mathcal{N})f) \leq C' n^{\dim \mathfrak{g}-r-1}.$$

for some C'>0. So we get that  $Cn^{\dim \mathfrak{g}-r}\leq C'n^{\dim \mathfrak{g}-r-1}$ . This is a contradiction, so  $\operatorname{Ker}\phi=0$  and thus  $\phi$  is injective.

Corollary 18.8. (The Duflo-Joseph theorem)  $\phi$  is an isomorphism.

| Proof. | Consider | the | ${\it restriction}$ | $\phi_V$ | of $q$ | b to | the | $V^*$ -isotypic | component |
|--------|----------|-----|---------------------|----------|--------|------|-----|-----------------|-----------|
| Thus   |          |     |                     |          |        |      |     |                 |           |

$$\phi_V : \operatorname{Hom}_{\mathfrak{g}}(V^*, (U_{\chi_{\lambda+a}})_{\operatorname{ad}}) \to \operatorname{Hom}_{\mathfrak{g}}(M_{\lambda}, V \otimes M_{\lambda}).$$

By Kostant's theorem, the source of this map has dimension dim V[0], while by Proposition 18.5, so does the target. Since by Proposition 18.7  $\phi_V$  is injective, it follows that  $\phi_V$  is an isomorphism for all V, hence so is  $\phi$ .

**Corollary 18.9.** If V is a finite-dimensional  $\mathfrak{g}$ -module then the natural map  $V \otimes U_{\chi_{\lambda+\rho}} \to \operatorname{Hom}_{\operatorname{fin}}(M_{\lambda}, V \otimes M_{\lambda})$  is an isomorphism.

*Proof.* This follows from Proposition 18.3 and Corollary 18.8.  $\square$ 

#### 18.3. infinitesimal characters of Harish-Chandra bimodules.

Corollary 18.10. Let V be a finite-dimensional  $\mathfrak{g}$ -module and  $\lambda \in \mathfrak{h}^*$ .

- (i) The left infinitesimal characters occurring in  $V \otimes U_{\chi_{\lambda}}$  are  $\chi_{\lambda+\nu}$  where  $\nu$  runs over weights of V.
- (ii) If M is a  $\mathfrak{g}$ -module with infinitesimal character  $\chi_{\lambda}$  then the infinitesimal characters occurring in  $V \otimes M$  are among  $\chi_{\lambda+\nu}$  where  $\nu$  runs over weights of V.
- (iii) If M is a nonzero Harish-Chandra  $\mathfrak{g}$ -bimodule with infinitesimal character  $(\chi_{\lambda}, \chi_{\mu})$  then there is  $w \in W$  such that  $w\lambda \mu \in P$ .
- Proof. (i) This follows from Corollary 18.9.
  - (ii) follows from (i) and the isomorphism

$$V \otimes M \cong (V \otimes U_{\chi_{\lambda}}) \otimes_{U_{\chi_{\lambda}}} M.$$

(iii) This follows from (i) since by Corollary 14.5 any irreducible Harish-Chandra bimodule is a quotient of  $V \otimes U_{\chi_{\mu}}$  for some  $\mu, V$ .  $\square$ 

Let  $HC_{\theta,\chi}(\mathfrak{g})$  be the category of Harish-Chandra  $\mathfrak{g}$ -bimodules with generalized infinitesimal character  $(\theta,\chi)$ .

Corollary 18.11. The category of Harish-Chandra  $\mathfrak{g}$ -bimodules  $HC(\mathfrak{g})$  has a decomposition according to generalized infinitesimal characters:

$$HC(\mathfrak{g}) = \bigoplus_{\gamma,\lambda} HC_{\chi_{\lambda+\gamma},\chi_{\lambda}}(\mathfrak{g}),$$

where  $\gamma \in P_+$  and  $\lambda \in \mathfrak{h}^*/\mathrm{Stab}(\gamma)$  (here  $\mathrm{Stab}(\gamma)$  is the stabilizer of  $\gamma$  in W). In particular, if  $(\theta, \chi)$  cannot be written as  $(\chi_{\lambda+\gamma}, \chi_{\lambda})$ ,  $\lambda \in \mathfrak{h}^*$ ,  $\gamma \in P_+$ , then  $HC_{\theta,\chi}(\mathfrak{g}) = 0$ .

*Proof.* This follows from Exercise 15.5 and Corollary 18.10.  $\Box$ 

#### 19. Principal series representations

#### 19.1. Residual finiteness of $U(\mathfrak{g})$ .

**Proposition 19.1.** The homomorphism  $\phi: U(\mathfrak{g}) \to \prod_{\lambda \in P_{\perp}} \operatorname{End}(L_{\lambda})$ is injective.

*Proof.* Let  $x \in \text{Ker}\phi$ , and G be the simply connected group with Lie algebra  $\mathfrak{g}$ . Then by the Peter-Weyl theorem, x acts by zero on  $\mathcal{O}(G) :=$  $\bigoplus_{\lambda \in P_+} L_\lambda \otimes L_\lambda^*$  (where x acts only on the first component). This means that the right-invariant differential operator on G defined by x is zero, i.e., x = 0. 

Exercise 19.2. Give another proof of Proposition 19.1 which does not use the Peter-Weyl theorem. Take  $x \in \text{Ker}\phi$ .

- (i) Show by interpolation that x acts by zero in every Verma module  $M_{\lambda}$ .
  - (ii) Show that if  $x \in U(\mathfrak{g})$  acts by zero in  $M_{\lambda}$  for all  $\lambda$  then x = 0.

Note that Proposition 19.1 implies that any  $z \in U(\mathfrak{g})$  which acts by a scalar in all  $L_{\lambda}$  belongs to  $Z(\mathfrak{g})$ . Indeed, in this case for any  $x \in U(\mathfrak{g})$ , [x,z] acts by zero in  $L_{\lambda}$ , hence [x,z]=0.

19.2. Principal series. Let  $\lambda, \mu \in \mathfrak{h}^*, \lambda - \mu \in P$ . Define the principal series bimodule

$$\mathbf{M}(\lambda,\mu) := \mathrm{Hom}_{\mathrm{fin}}(M_{\lambda-\rho}, M_{\mu-\rho}^{\vee}) \in HC_{\chi_{\mu},\chi_{\lambda}}(\mathfrak{g}).$$

Then we have

(15) 
$$\mathbf{M}(\lambda,\mu) = \bigoplus_{V \in \operatorname{irr}(\mathfrak{g})} V \otimes V^*[\lambda - \mu].$$

The bimodule  $\mathbf{M}(\lambda,\mu)$  represents a certain functor that has a nice independent description.

**Proposition 19.3.** Let  $X \in HC(\mathfrak{g})$ . Then

$$\operatorname{Hom}_{\mathfrak{g}-\operatorname{bimod}}(X, \mathbf{M}(\lambda, \mu)) \cong \operatorname{Hom}_{(\mathfrak{b}_{-},\mathfrak{b}_{+})-\operatorname{bimod}}(X \otimes \mathbb{C}_{\lambda-\rho}, \mathbb{C}_{\mu-\rho}).$$

where the  $(\mathfrak{b}_{-},\mathfrak{b}_{+})$ -bimodule structure on  $\mathbb{C}_{\mu-\rho}$  is defined by the character  $(\mu - \rho, 0)$  and on  $\mathbb{C}_{\lambda - \rho}$  by the character  $(0, \lambda - \rho)$ .

*Proof.* We have

$$\operatorname{Hom}_{\mathfrak{g}-\operatorname{bimod}}(X,\mathbf{M}(\lambda,\mu)) = \operatorname{Hom}_{\mathfrak{g}-\operatorname{bimod}}(X \otimes M_{\lambda-\rho}, M_{\mu-\rho}^{\vee}),$$

where the right copy of  $\mathfrak g$  acts trivially on  $M_{\mu-\rho}^{\vee}$  and the left copy of  $\mathfrak g$ acts trivially on  $M_{\lambda-\rho}$ . Frobenius reciprocity then yields

$$\operatorname{Hom}_{\mathfrak{g}-\operatorname{bimod}}(X,\mathbf{M}(\lambda,\mu)) = \operatorname{Hom}_{(\mathfrak{b}_+,\mathfrak{g})-\operatorname{bimod}}(X \otimes \mathbb{C}_{\lambda-\rho}, M_{\mu-\rho}^{\vee}).$$

Since  $X \otimes \mathbb{C}_{\lambda-\rho}$  is diagonalizable under the adjoint action of  $\mathfrak{h}$ , on the right hand side we may replace  $M_{\mu-\rho}^{\vee}$  with its completion  $\widehat{M}_{\mu-\rho}^{\vee}$  (the Cartesian product of all weight spaces). Then applying Frobenius reciprocity again, we get the desired statement.

Let us give an explicit realization of  $\mathbf{M}(\lambda, \mu)$ . By (15),  $\mathbf{M}(\lambda, \mu)$  is spanned by elements  $\Phi_{v,\ell}: M_{\lambda-\rho} \to M_{\mu-\rho}^{\vee}, v \in V, \ell \in V^*[\lambda-\mu]$ , where

$$\Phi_{v,\ell}u := (v \otimes 1, \Phi_{\ell}u),$$

and  $\Phi_{\ell}: M_{\lambda-\rho} \to V^* \otimes M_{\mu-\rho}^{\vee}$  is the homomorphism for which  $\langle \Phi_{\ell} \rangle = \ell$ , for finite-dimensional  $\mathfrak{g}$ -modules V. Moreover these elements easily express in terms of such elements for simple V. Thus for any V and  $y \in V \otimes V^*[0]$  we can define the linear map  $\Phi_V(y): M_{\lambda-\rho} \to M_{\mu-\rho}^{\vee}$  which depends linearly on y with  $\Phi_V(v \otimes \ell) = \Phi_{v,\ell}$ , and every element of  $\mathbf{M}(\lambda,\mu)$  is of this form.

**Proposition 19.4.** The right action of  $\mathfrak{g}$  on  $\mathbf{M}(\lambda, \mu)$  is given by the formula

$$\Phi_V(v \otimes \ell) \cdot b = \Phi_{\mathfrak{g} \otimes V}([b \otimes v] \bigotimes [(\lambda - \rho) \otimes \ell + \sum_{\alpha \in R_+} f_\alpha^* \otimes f_\alpha \ell]).$$

*Proof.* Consider the homomorphism

$$\Psi_{\ell} := \sum_{i} b_{i}^{*} \otimes \Phi_{\ell} b_{i} : M_{\lambda - \rho} \to \mathfrak{g}^{*} \otimes V^{*} \otimes M_{\mu - \rho}^{\vee},$$

where  $\{b_i\}$  is a basis of  $\mathfrak{g}$  and  $\{b_i^*\}$  the dual basis of  $\mathfrak{g}^*$ . We have

$$\langle \Psi_{\ell} \rangle = \sum b_i^* \otimes \langle \Phi_{\ell} b_i \rangle \in \mathfrak{g}^* \otimes V^*,$$

where the expectation value map  $\langle , \rangle$  is defined in Exercise 8.13. But

$$\langle \Phi_{\ell} h \rangle = (\lambda - \rho, h) \ell, \ \langle \Phi_{\ell} e_{\alpha} \rangle = 0, \ \langle \Phi_{\ell} f_{\alpha} \rangle = f_{\alpha} \ell$$

for  $\alpha \in R_+$ . Thus we get

$$\langle \Psi_{\ell} \rangle = (\lambda - \rho) \otimes \ell + \sum_{\alpha \in R_{+}} f_{\alpha}^{*} \otimes f_{\alpha} \ell,$$

hence

$$\Psi_{\ell} = \Phi_{(\lambda - \rho) \otimes \ell + \sum_{\alpha \in R_{+}} f_{\alpha}^{*} \otimes f_{\alpha} \ell}.$$

This implies the statement since

$$(\Phi_V(v \otimes \ell) \cdot b)u = (v \otimes 1, \Phi_\ell bu) = (b \otimes v \otimes 1, \Psi_\ell u), \ u \in M_{\lambda - \rho}.$$

This leads to a geometric construction of the principal series. Namely, let G be the simply connected group with Lie algebra  $\mathfrak{g}$ ,  $B=B_+$  be the Borel subgroup of G whose Lie algebra is  $\mathfrak{b}_+$  and H=B/[B,B] the corresponding torus. Fix  $\lambda, \mu \in \mathfrak{h}^*$  with  $\lambda - \mu \in P$ . Define a real-analytic character

$$\psi_{\lambda,\mu}: H \to \mathbb{C}^{\times}$$

by

$$\psi_{\lambda,\mu}(x) := \lambda(x)\mu(x^*)^{-1}$$

where  $x^*$  is the image of x under the compact antiholomorphic involution  $\sigma: H \to H$  (i.e., such that  $H^{\sigma} = H_c$ , the compact real form of H). For example, for  $G = SL_2$ ,  $\lambda, \mu$  are complex numbers with  $\lambda - \mu$  an integer and  $x^* = \overline{x}^{-1}$ , so

$$\psi_{\lambda,\mu}(x) = x^{\lambda} \overline{x}^{\mu} = x^{\lambda-\mu} |x|^{2\mu}.$$

Define  $C^{\infty}_{\lambda,\mu}(G/B)$  to be the space of smooth functions on G satisfying

$$F(gb) = F(g)\psi_{\lambda,\mu}(b).$$

This is naturally an admissible representation of G: we have  $G/B = G_c/H_c$ , so the multiplicity space of V in  $C_{\lambda,\mu}^{\infty}(G/B)$  is  $V^*[\lambda-\mu]$ ; namely,  $C_{\lambda,\mu}^{\infty}(G/B)^{\text{fin}} = C_{\lambda-\mu}^{\infty}(G_c/H_c)^{\text{fin}}$ , the space of  $G_c$ -finite functions on  $G_c$  (under left translations) such that

$$F(gx) = F(g)\lambda(x)\mu(x)^{-1}$$

for  $x \in H_c$ .

Proposition 19.5. We have an isomorphism

$$\xi: \mathbf{M}(\lambda,\mu) \to C^{\infty}_{\lambda-\rho,\mu-\rho}(G/B)^{\mathrm{fin}}$$

as Harish-Chandra bimodules. Namely,  $\xi(\Phi_{v,\ell})$  is the matrix coefficient  $\psi_{v,\ell}(g) := (v, g\ell), g \in G_c$ .

**Exercise 19.6.** Prove Proposition 19.5. **Hint:** Use Proposition 19.4 to show that  $\xi$  is a well defined isomorphism of  $\mathfrak{g}_{ad}$ -modules, and after applying  $\xi$  the right action of  $\mathfrak{g}$  looks like

$$(\psi \cdot b)(g) = (\lambda - \rho)(\operatorname{Ad}(g)b)\psi(g) + \sum_{\alpha \in R_+} f_{\alpha}^*(\operatorname{Ad}(g)b)(R(f_{\alpha})\psi)(g),$$

where  $R(f_{\alpha})$  is the left-invariant vector field equal to  $f_{\alpha}$  at 1. Then show that the right action of  $\mathfrak{g}$  on  $C^{\infty}_{\lambda-\rho,\mu-\rho}(G/B)$  is given by the same formula.

19.3. The functor  $H_{\lambda}$ . Define the functor  $H_{\lambda}: \mathcal{O}_{\theta} \to HC_{\theta,\chi_{\lambda}}$  given by

$$H_{\lambda}(X) := \operatorname{Hom}_{\operatorname{fin}}(M_{\lambda-\rho}, X).$$

Note that  $H_{\lambda}(M_{\mu-\rho}^{\vee}) = \mathbf{M}(\lambda, \mu)$ .

**Proposition 19.7.** The functor  $H_{\lambda}$  exact when  $\lambda$  is dominant.

*Proof.* If V is a finite-dimensional  $\mathfrak{g}$ -module then

$$\operatorname{Hom}_{\mathfrak{g}}(V,H_{\lambda}(X))=\operatorname{Hom}_{\mathfrak{g}}(V\otimes M_{\lambda-\rho},X),$$

which is exact as  $V \otimes M_{\lambda-\rho}$  is projective.

#### 20. BGG reciprocity and BGG Theorem

#### 20.1. A vanishing lemma for Ext groups.

**Lemma 20.1.** Let  $X \in \mathcal{O}$  be a free  $U(\mathfrak{n}_{-})$ -module. Then for any  $\mu \in \mathfrak{h}^*$  we have

$$\operatorname{Ext}_{\mathcal{O}}^{i}(X, M_{\mu}^{\vee}) = 0, \ i > 0.$$

*Proof.* Fix a projective resolution  $P_{\bullet}$  of X in  $\mathcal{O}$  and consider the complex  $\operatorname{Hom}_{\mathfrak{g}}(P_{\bullet}, M_{\mu}^{\vee})$  which computes the desired Ext groups. Since  $P_i$  have a weight decomposition,

$$\operatorname{Hom}_{\mathfrak{g}}(P_{\bullet}, M_{\mu}^{\vee}) = \operatorname{Hom}_{\mathfrak{g}}(P_{\bullet}, \widehat{M}_{\mu}^{\vee}),$$

where  $\widehat{M}_{\mu}^{\vee} := \prod_{\beta \in \mathfrak{h}^*} M_{\mu}^{\vee}[\beta]$  is the completion of  $M_{\mu}^{\vee}$ . We have

$$\widehat{M}_{\mu}^{\vee} = \operatorname{Coind}_{\mathfrak{b}_{-}}^{\mathfrak{g}}(\mathbb{C}_{\mu}) := \operatorname{Hom}_{\mathfrak{b}_{-}}(U(\mathfrak{g}), \mathbb{C}_{\mu}) \cong \operatorname{Hom}_{\mathbb{C}}(U(\mathfrak{n}_{+}), \mathbb{C}_{\mu}).$$

Thus, Frobenius reciprocity yields

$$\operatorname{Hom}_{\mathfrak{g}}(P_{\bullet}, \widehat{M}_{\mu}^{\vee}) = \operatorname{Hom}_{\mathfrak{b}_{-}}(P_{\bullet}, \mathbb{C}_{\mu}).$$

By Proposition 16.6(ii),  $P_i$  are free  $U(\mathfrak{n}_-)$ -modules, so the exact sequence of  $U(\mathfrak{n}_-)$ -modules

$$\dots \to P_1 \to P_0 \to X \to 0$$

is split. Thus the complex  $\operatorname{Hom}_{\mathfrak{b}_{-}}(P_{\bullet},\mathbb{C}_{\mu})$  is exact in positive degrees, which implies the statement.  $\square$ 

20.2. Standard filtrations. A standard (or Verma) filtration on  $X \in \mathcal{O}$  is a filtration for which successive quotients are Verma modules. X is called **standardly filtered** if it admits a standard filtration. It is clear that every standardly filtered object X is necessarily a free  $U(\mathfrak{n}_-)$ -module.

Corollary 20.2. If X is standardly filtered then  $\operatorname{Ext}_{\mathcal{O}}^{i}(X, M_{\mu}^{\vee}) = 0$  for all  $\mu \in \mathfrak{h}^{*}$  and i > 0.

The converse also holds. In fact, we have

**Theorem 20.3.** X is standardly filtered if and only if

$$\operatorname{Ext}^1_{\mathcal{O}}(X, M_{\lambda}^{\vee}) = 0$$

for all  $\lambda \in \mathfrak{h}^*$ .

*Proof.* Let E be a finite-dimensional vector space, and suppose we have a short exact sequence in  $\mathcal{O}$ :

$$0 \to K \to E \otimes M_{\lambda} \to Z \to 0$$

with  $K[\lambda] = 0$ .

**Lemma 20.4.** If  $\operatorname{Ext}^1_{\mathcal{O}}(Z, M_{\mu}^{\vee}) = 0$  for all  $\mu \in \mathfrak{h}^*$  then K = 0 and  $Z \cong E \otimes M_{\lambda}$ .

*Proof.* The long exact sequence of cohomology yields

... 
$$\to \operatorname{Hom}(E \otimes M_{\lambda}, M_{\mu}^{\vee}) \to \operatorname{Hom}(K, M_{\mu}^{\vee}) \to \operatorname{Ext}_{\mathcal{O}}^{1}(Z, M_{\mu}^{\vee}) = 0.$$

For  $\lambda \neq \mu$ , we have  $\operatorname{Hom}(M_{\lambda}, M_{\mu}^{\vee}) = 0$ , so it follows that  $\operatorname{Hom}(K, M_{\mu}^{\vee}) = 0$ . But we also have  $\operatorname{Hom}(K, M_{\lambda}^{\vee}) = 0$ , as  $K[\lambda] = 0$ , while every nonzero submodule of  $M_{\lambda}^{\vee}$  contains  $L_{\lambda}$ . It follows that K = 0.

Now let us prove the theorem. We only need to prove the "if" direction. We argue by induction in the length of X (with the base case X=0 being trivial). Let  $\lambda$  be a maximal weight in P(X) and  $E:=X[\lambda]$ . Let Z be the submodule of X generated by E; it is a quotient of  $E\otimes M_{\lambda}$  by a submodule K with  $K[\lambda]=0$ . We have a short exact sequence

$$0 \to Z \to X \to Y \to 0$$
.

Thus from the long exact sequence of cohomology we get an exact sequence

$$\dots \to \operatorname{Hom}(Z, M_{\mu}^{\vee}) \to \operatorname{Ext}_{\mathcal{O}}^{1}(Y, M_{\mu}^{\vee}) \to \operatorname{Ext}_{\mathcal{O}}^{1}(X, M_{\mu}^{\vee}) = 0.$$

It follows that for  $\mu \neq \lambda$  we have  $\operatorname{Ext}^1_{\mathcal{O}}(Y, M_{\mu}^{\vee}) = 0$ , as in this case  $\operatorname{Hom}(Z, M_{\mu}^{\vee}) = 0$  (since Z is a quotient of  $E \otimes M_{\lambda}$ ). On the other hand, if  $\mu = \lambda$  then by the argument in the proof of Lemma 20.1 we have

$$\operatorname{Ext}^1_{\mathcal{O}}(Y, M_{\lambda}^{\vee}) = \operatorname{Ext}^1_{\mathcal{C}}(Y, \mathbb{C}_{\lambda}),$$

where  $\mathcal{C}$  is the category of  $\mathfrak{h}$ -semisimple  $\mathfrak{b}_-$ -modules. But  $\operatorname{Ext}^1_{\mathcal{C}}(Y,\mathbb{C}_{\lambda}) = 0$ , as all weights of Y are not  $> \lambda$  and hence any short exact sequence of  $\mathfrak{b}_-$ -modules

$$0 \to \mathbb{C}_{\lambda} \to \widetilde{Y} \to Y \to 0$$

canonically splits. By the induction assumption, it follows that Y is standardly filtered, so by Corollary 20.2,  $\operatorname{Ext}^i(Y, M_\mu^\vee) = 0$  for all  $i \geq 1$ , in particular for i = 1, 2. Thus the long exact sequence of Ext groups gives

$$\operatorname{Ext}^1(Z,M_\mu^\vee) = \operatorname{Ext}^1(X,M_\mu^\vee) = 0,$$

hence  $Z=E\otimes M_{\lambda}$  by Lemma 20.4. This completes the induction step.  $\square$ 

Corollary 20.5. (i) Every  $X \in \mathcal{O}$  which is a free  $U(\mathfrak{n}_{-})$ -module is standardly filtered. In particular, for any  $\lambda \in \mathfrak{h}^*$  and finite-dimensional  $\mathfrak{g}$ -module V, the module  $V \otimes M_{\lambda}$  is standardly filtered.

(ii) Any projective object  $P \in \mathcal{O}$  is standardly filtered.

Proof. (i) Follows from Theorem 20.3 and Lemma 20.1.

(ii) Immediate from Theorem 20.3.

20.3. **BGG reciprocity.** Denote by  $d_{\lambda\mu}$  the multiplicity of  $L_{\mu}$  in the Jordan-Hölder series of  $M_{\lambda}$ . Since characters of  $L_{\mu}$  are linearly independent, these numbers are determined from the formula

$$\sum_{\mu} d_{\lambda\mu} \operatorname{ch}(L_{\mu}) = \operatorname{ch}(M_{\lambda}) = \frac{e^{\lambda}}{\prod_{\alpha \in R_{+}} (1 - e^{-\alpha})}.$$

Thus the knowledge of  $d_{\lambda\mu}$  is equivalent to the knowledge of the characters  $\operatorname{ch}(L_{\lambda})$ .

Since by Corollary 20.5(ii) the projective covers  $P_{\lambda}$  of  $L_{\lambda}$  are standardly filtered, we may also define the multiplicities  $d_{\lambda\mu}^*$  of  $M_{\mu}$  in  $P_{\lambda}$ . These are independent of the choice of the standard filtration and are determined by the formula

$$\operatorname{ch}(P_{\lambda}) = \sum_{\mu} d_{\lambda\mu}^* \operatorname{ch}(M_{\mu}) = \sum_{\mu} d_{\lambda\mu}^* \frac{e^{\lambda}}{\prod_{\alpha \in R_+} (1 - e^{-\alpha})}.$$

**Theorem 20.6.** (BGG reciprocity) We have  $d_{\lambda\mu}^* = d_{\mu\lambda}$ .

*Proof.* We compute dim  $\operatorname{Hom}(P_{\lambda}, M_{\mu}^{\vee})$  in two ways. First using the standard filtration of  $P_{\lambda}$  and Lemma 20.1, we have dim  $\operatorname{Hom}(P_{\lambda}, M_{\mu}^{\vee}) = d_{\lambda\mu}^*$ . On the other hand, using that the multiplicity of  $L_{\lambda}$  in  $M_{\mu}^{\vee}$  is  $d_{\mu\lambda}$ , we get dim  $\operatorname{Hom}(P_{\lambda}, M_{\mu}^{\vee}) = d_{\mu\lambda}$ .

Let  $c_{\lambda\mu} = \dim \operatorname{Hom}(P_{\lambda}, P_{\mu})$  be the entries of the Cartan matrix C of  $\mathcal{O}$ . They are equal to the multiplicities of  $L_{\lambda}$  in  $P_{\mu}$ .

Corollary 20.7. We have

$$c_{\lambda\mu} = \sum_{\nu} d_{\nu\lambda} d_{\nu\mu}.$$

In other words,  $C = D^T D$  where  $D = (d_{\lambda \mu})$ .

Note that since D is upper triangular with respect to the partial order  $\leq$  with ones on the diagonal, it can be uniquely recovered from C by Gauss decomposition. Thus the knowledge of D is equivalent to the knowledge of C.

**Example 20.8.** Consider the structure of the category  $\mathcal{O}_{\chi}$  for  $\mathfrak{g} = \mathfrak{sl}_2$ . The only interesting case is  $\chi = \chi_{\lambda+1}$  for  $\lambda \in \mathbb{Z}_{\geq 0}$ . Then the simple objects are  $X = L_{\lambda}$  (finite-dimensional) and  $Y = M_{-\lambda-2}$ . By Proposition 16.4, the projective cover  $P_X$  is just the Verma module  $M_{\lambda}$ , which has composition series [X,Y], starting from the head X. To determine  $P_Y$ , consider the tensor product  $P := M_{-1} \otimes L_{\lambda+1}$ . This is projective with character

$$ch(P) = ch(M_{\lambda}) + ch(M_{\lambda-2}) + ... + ch(M_{-\lambda-2}).$$

Thus denoting by  $\Pi_{\lambda}$  the projection functor to the generalized infinitesimal character  $\chi_{\lambda+1}$ , we get that

$$\operatorname{ch}(\Pi_{\lambda}(P)) = \operatorname{ch}(M_{\lambda}) + \operatorname{ch}(M_{-\lambda-2}).$$

Note that  $M_{-\lambda-2}$  is not projective since  $\operatorname{Ext}^1_{\mathcal{O}}(M_{-\lambda-2}, L_{\lambda}) \neq 0$  (there is a nontrivial extension  $M_{\lambda}^{\vee}$ ). Thus  $\Pi_{\lambda}(P)$  is indecomposable (otherwise one of the summands in the decomposition would have to be  $M_{-\lambda-2}$ ), i.e.,  $\Pi_{\lambda}(P) = P_Y$ . Since it maps to Y and receives an injection from  $M_{\lambda}$ , its composition series is [Y, X, Y]. This is the **big projective object** of  $\mathcal{O}_{\chi}$ . We this get for  $\mathcal{O}_{\chi}$ :

$$D = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}, \ C = \begin{pmatrix} 1 & 1 \\ 1 & 2 \end{pmatrix}.$$

We can now compute the (basic) algebra A whose module category is equivalent to  $\mathcal{O}_{\chi}$ . This is the algebra  $A = \operatorname{End}(P_X \oplus P_Y)$ , and it has dimension  $\sum_{i,j} c_{ij} = 5$ . The basis is formed by  $1_X, 1_Y$  and morphisms  $a: P_X \to P_Y$ ,  $b: P_Y \to P_X$  and  $ab: P_Y \to P_Y$ . Moreover, we have ba = 0. Thus the algebra A is the path algebra of the quiver with two vertices x, y with edges  $a: x \to y$  and  $b: y \to x$  with the only relation ba = 0.

20.4. The duality functor. Let  $\tau : \mathfrak{g} \to \mathfrak{g}$  be the Cartan involution given by  $\tau(e_i) = f_i$ ,  $\tau(f_i) = e_i$ ,  $\tau(h_i) = -h_i$ . For  $X \in \mathcal{O}$  let  $X^{\tau}$  be the module X twisted by  $\tau$ , and  $X^{\vee} = (X^{\tau})_{\text{fin}}^*$ , the  $\mathfrak{h}$ -finite part of  $(X^{\tau})^*$ . The following proposition is easy:

**Proposition 20.9.** (i)  $X^{\vee} \in \mathcal{O}$  and has the same character and composition series as X.

- (ii)  $(M_{\lambda})^{\vee} = M_{\lambda}^{\vee}, L_{\lambda}^{\vee} = L_{\lambda}.$
- (iii) the assignment  $X \mapsto X^{\vee}$  is an involutive equivalence of categories  $\mathcal{O} \to \mathcal{O}^{\mathrm{op}}$  which preserves the decomposition into  $\mathcal{O}_{\chi}(S)$ .

Corollary 20.10.  $\mathcal{O}$  has enough injectives, namely the injective hull of  $L_{\lambda}$  is  $P_{\lambda}^{\vee}$ .

20.5. The Jantzen filtration. It turns out that every Verma module  $M_{\lambda}$  carries a canonical finite filtration by submodules called the **Jantzen filtration**, which plays an important role in studying category  $\mathcal{O}$ . In fact, this filtration is defined much more generally, as follows.

Let k be a field and V, U be free k[[t]]-modules of the same rank  $d < \infty$ , and let  $B \in \text{Hom}(V, W)$  be such that det  $B := \wedge^d B$  is nonzero. Let  $V_0 := V/tV$ . Define  $V_m \subset V_0$  to be the space of all  $v_0 \in V_0$  such that there exists a lift  $v \in V$  of  $v_0$  for which  $Bv \in t^m W$ . It is clear that  $V_0 \supset V_1 \supset V_2 \supset \dots$  with  $V_1 = \text{Ker}B(0)$ , and  $V_m = 0$  for some m. Thus we get a finite descending filtration  $\{V_i\}$  of  $V_0$  called the **Jantzen filtration** attached to B.

Exercise 20.11. (i) Show that there exist unique nonnegative integers  $n_1 \leq ... \leq n_d$  such that for some bases  $e_1, ..., e_d$  of V and  $f_1, ..., f_d$  of W over k[[t]] one has  $Be_i = t^{n_i} f_i$ , and that  $\operatorname{Coker} B \cong \bigoplus_{i=1}^d (k[t]/t^{n_i})$  as a k[[t]]-module. Deduce that the order of vanishing of det B at t=0equals  $\dim_k \operatorname{Coker} B = \sum_{i=1}^d n_i$ .

- (ii) Suppose dim  $V_j = d_j$  (so  $d_0 = d$ ). Show that for all  $j \in \mathbb{Z}_{\geq 0}$ ,  $n_i = j$  if and only if  $d - d_j < i \le d - d_{j+1}$ , and deduce the **Jantzen sum formula**: the order of vanishing of det B at t = 0 equals  $\sum_{j>1} d_j$ .
- (iii) Suppose that V, W are modules over some k[[t]]-algebra A with  $A_0 := A/tA$  (for example,  $A = A_0[[t]]$  and V, W are  $A_0$ -modules), and B is an A-module homomorphism. Show that the Jantzen filtration of  $V_0$  attached to B is a filtration by  $A_0$ -submodules.

The Jantzen filtration on  $M_{\lambda}$  is now defined using the homomorphism  $B: M_{\lambda(t)} \to M_{\lambda(t)}^{\vee}$  over  $A_0 := U(\mathfrak{g})$  corresponding to the Shapovalov form, where  $\lambda(t) := \lambda + t\rho$ . Namely, we define it separately on each weight subspace. For example,  $(M_{\lambda})_1 = J_{\lambda}$  is the maximal proper submodule of  $M_{\lambda}$ .

**Exercise 20.12.** (Jantzen sum formula for  $M_{\lambda}$ ) Use the Jantzen sum formula of Exercise 20.11 and the formula for the determinant of the Shapovalov form (Exercise 8.15) to show that

$$\sum_{j\geq 1} \operatorname{ch}((M_{\lambda})_j) = \sum_{\alpha \in R_+: (\lambda + \rho, \alpha^{\vee}) \in \mathbb{Z}_{\geq 1}} \operatorname{ch}(M_{\lambda - (\lambda + \rho, \alpha^{\vee})\alpha}).$$

20.6. The BGG theorem. The following is the converse to Theorem 15.11.

**Theorem 20.13.** (Bernstein – I. Gelfand – S. Gelfand) If  $L_{\mu-\rho}$  occurs in the composition series of  $M_{\lambda-\rho}$  (i.e.,  $d_{\lambda-\rho,\mu-\rho} \neq 0$ ) then  $\mu \leq \lambda$ .

Proof. It is clear that  $\lambda - \mu \in Q_+$ . The proof is by induction in the integer  $n := (\lambda - \mu, \rho^{\vee})$ . If n = 0, the statement is obvious, so we only need to justify the induction step for n > 0. Then  $L_{\mu-\rho}$  occurs in  $J_{\lambda-\rho} = (M_{\lambda-\rho})_1$ , the degree 1 part of the Jantzen filtration of  $M_{\lambda}$ . Thus by the Jantzen sum formula (Exercise 20.12),  $L_{\mu-\rho}$  must occur in  $M_{\lambda-\rho-(\lambda,\alpha^{\vee})\alpha} = M_{s_{\alpha}\lambda-\rho}$  for some  $\alpha \in R_+$  such that  $(\lambda,\alpha^{\vee}) \in \mathbb{Z}_{\geq 1}$ . By the induction assumption, we then have  $\mu \leq s_{\alpha}\lambda$ . But  $s_{\alpha}\lambda \prec \lambda$ , so we get  $\mu \prec \lambda$ .

Corollary 20.14. The following conditions on  $\mu \leq \lambda$  are equivalent.

- (i)  $\mu \leq \lambda$
- (ii)  $L_{\mu-\rho}$  occurs in  $M_{\lambda-\rho}$ .
- (iii) dim  $\operatorname{Hom}(M_{\mu-\rho}, M_{\lambda-\rho}) \neq 0$ .

#### 21. Multiplicities in category $\mathcal{O}$

The multiplicities  $d_{\lambda\mu}$  are complicated in general, and the (eventually successful) attempt to understand them was one of the main developments that led to creation of geometric representation theory. These multiplicities are given by the **Kazhdan-Lusztig conjecture** (1979) proved by Beilinson-Bernstein and independently by Brylinski-Kashiwara in 1981. By now several proofs of this conjecture are known, but they are complicated and beyond the scope of this course. However, let us give the statement of this result. To simplify the exposition, we do so for  $\mathcal{O}_{\chi_{\lambda}}$  when  $\lambda \in P_{+}$ ; it turns out that this case captures all the complexity of the situation, and the general case is similar.

21.1. **The Hecke algebra.** Even to formulate the Kazhdan-Lusztig conjecture, we need to introduce an object which seemingly has nothing to do with our problem - the **Hecke algebra** of W. Namely, recall that W is defined by generators  $s_i$ , i = 1, ..., r subject to the braid relations

$$s_i s_j \dots = s_j s_i \dots, i \neq j,$$

where the length of both words is  $m_{ij}$  such that  $a_{ij}a_{ji} = 4\cos^2\frac{\pi}{m_{ij}}$  (for  $a_{ji}a_{ij} = 0, 1, 2, 3, m_{ij} = 2, 3, 4, 6$ ), and also the relations  $s_i^2 = 1$ . The same relations of course define the group algebra  $\mathbb{Z}W$ , in which the last relation can be written as the quadratic relation  $(s_i + 1)(s_i - 1) = 0$ . The **Hecke algebra**  $H_q(W)$  of W is defined over  $\mathbb{Z}[q^{\frac{1}{2}}, q^{-\frac{1}{2}}]$  by the generators  $T_i$  satisfying the same braid relations

$$T_i T_j \dots = T_j T_i \dots, i \neq j,$$

and the deformed quadratic relations

$$(T_i + 1)(T_i - q) = 0.$$

For every  $w \in W$  we can define the element  $T_w = T_{i_1}...T_{i_m}$  for every reduced decomposition  $w = s_{i_1}...s_{i_m}$ . This is independent on the reduced decomposition since any two of them can be related by using only the braid relations. Moreover, it is easy to see that the elements  $T_w$  span  $H_q(W)$ , since any non-reduced product of  $T_i$  can be expressed via shorter products by using the braid and quadratic relations for  $T_i$ . Moreover, we have

**Proposition 21.1.**  $T_w, w \in W$  are linearly independent, so they form a basis of  $H_q(W)$ . Thus  $H_q(W)$  is a free  $\mathbb{Z}[q^{\frac{1}{2}}, q^{-\frac{1}{2}}]$ -module of rank |W|.

*Proof.* Let V be the free  $\mathbb{Z}[q^{\frac{1}{2}}, q^{-\frac{1}{2}}]$ -module with basis  $X_w, w \in W$ . Define a left action of the free algebra with generators  $T_i$  on V by

$$T_i X_w = X_{s_i w}$$

if  $\ell(s_i w) = \ell(w) + 1$  and

$$T_i X_w = (q-1)X_w + qX_{s_i w}$$

if  $\ell(s_i w) = \ell(w) - 1$ . We claim that this action factors through  $H_q(W)$ . To show this, define a right action of the same free algebra on V by

$$X_w T_i = X_{ws_i}$$

if  $\ell(ws_i) = \ell(w) + 1$  and

$$X_w T_i = (q-1)X_w + qX_{ws_i}$$

if  $\ell(ws_i) = \ell(w) - 1$ . It is easy to check by a direct computation that these two actions commute:

$$(16) (T_i X_w) T_j = T_i (X_w T_j).$$

Also the elements  $X_1T_w$  clearly span V. Thus to prove the relations of  $H_q(W)$  for the left action, it suffices to check them on  $X_1$ , which is straightforward.

Since  $T_w X_1 = X_w$  are linearly independent, it follows that  $T_w$  are linearly independent, as claimed.

#### Exercise 21.2. Check identity (16).

The quadratic relation for  $T_i$  implies that it is invertible in the Hecke algebra, with inverse

$$T_i^{-1} = q^{-1}(T_i + 1 - q).$$

These inverses satisfy the relation  $(T_i^{-1}+1)(T_i^{-1}-q^{-1})=0$  (obtained by multiplying the quadratic relation for  $T_i$  by  $-T_i^{-2}q^{-1}$ ), and also the braid relations. It follows that the Hecke algebra has an involutive automorphism D that sends  $q^{\frac{1}{2}}$  to  $q^{-\frac{1}{2}}$  and each  $T_i$  to  $T_i^{-1}$ . More generally one has  $D(T_w)=T_{w^{-1}}^{-1}$ .

21.2. **The Bruhat order.** Recall that the partial **Bruhat order** on W is defined as follows:  $y \leq w$  if a reduced decomposition of y can be obtained from a reduced decomposition of w by crossing out some  $s_i$ ; thus  $y \leq w$  implies that  $\ell(y) \leq \ell(w)$ , and if the equality holds then y = w. Moreover, if  $\ell(w) = \ell(y) + 1$  then y < w iff  $y = y_1y_2$  and  $w = y_1s_iy_2$  for some i, where  $\ell(y) = \ell(y_1) + \ell(y_2)$ . In this case we say that w **covers** y, and  $y \leq w$  iff there exists a sequence  $y = x_0 < x_1 < ... < x_m = w$  such that  $x_{j+1}$  covers  $x_j$  for all j (here  $m = \ell(w) - \ell(y)$ ).

**Exercise 21.3.** Show that if  $y \leq w$  then for any dominant  $\lambda \in P$ ,  $w\lambda \leq y\lambda$ , and the converse holds if  $\lambda$  is regular (i.e.,  $W_{\lambda} = 1$ ).

**Example 21.4.** For type  $A_1$  the Bruhat order is the covering relation 1 < s. For type  $A_2$  the covering relations are

$$1 < s_1, s_2 < s_1 s_2, s_2 s_1 < s_1 s_2 s_1 = s_2 s_1 s_2.$$

#### 21.3. Kazhdan-Lusztig polynomials.

**Theorem 21.5.** There exist unique polynomials  $P_{y,w} \in \mathbb{Z}[q]$  such that

- (a)  $P_{y,w} = 0 \text{ unless } y \leq w, \text{ and } P_{w,w} = 1;$
- (b) If y < w then  $P_{y,w}$  has degree at most  $\frac{\ell(w) \ell(y) 1}{2}$ ;
- (c) The elements

$$C_w := q^{-\frac{\ell(w)}{2}} \sum_{y} P_{y,w}(q) T_y \in H_q(W)$$

satisfy  $D(C_w) = C_w$ .

*Proof.* Let  $y = s_{i_1}...s_{i_l}$  be a reduced decomposition of y. Then we have

$$T_{y^{-1}}^{-1} = \prod_{j=1}^{l} T_{i_j}^{-1} = q^{-\ell(y)} \prod_{j=1}^{l} (T_{i_j} + 1 - q).$$

Thus there exist unique polynomials  $R_{x,y} \in \mathbb{Z}[q]$  such that

$$D(T_y) = T_{y^{-1}}^{-1} = \sum_x q^{-\ell(x)} R_{x,y}(q^{-1}) T_x,$$

with  $R_{x,y} = 0$  unless x = y (in which case  $R_{x,y}(q) = 1$ ) or  $\ell(x) < \ell(y)$ . It is easy to check that  $R_{x,y}$  can be computed using the following recursive rules: for a simple reflection s,

$$R_{x,y} = R_{sx,sy}, \ sx < x, sy < y;$$
  
 $R_{x,y} = (q-1)R_{x,sy} + qR_{sx,sy}, sx > x, sy < y.$ 

(we have  $R_{x,1} = \delta_{x,1}$  and for  $y \neq 1$  there is always i such that  $s_i y < y$ ). This implies by induction in  $\ell(y)$  that  $R_{x,y} = 0$  unless  $x \leq y$ . Indeed, if x' := sx < x, y' := sy < y then  $R_{x,y} = R_{x',y'}$ , so if this is nonzero then by the induction assumption  $x' \leq y'$ , hence  $sx' \leq sy'$ , i.e.,  $x \leq y$ . On the other hand, if sx > x, sy < y and  $R_{x,y} \neq 0$  then either  $R_{x,sy} \neq 0$  or  $R_{sx,sy} \neq 0$ , hence either  $x \leq sy$  or  $sx \leq sy$ . But each one of the inequalities  $x \leq sy$ ,  $sx \leq sy$  implies  $x \leq y$ .

We also see by induction that  $\deg R_{x,y} \leq \ell(y) - \ell(x)$ .

Now it is easy to compute that the condition that  $D(C_w) = C_w$  is equivalent to the recursion

$$q^{\frac{\ell(w)-\ell(x)}{2}}P_{x,w}(q^{-1}) - q^{\frac{\ell(x)-\ell(w)}{2}}P_{x,w}(q) =$$

$$\sum_{x < y} (-1)^{\ell(x) + \ell(y)} q^{\frac{-\ell(x) + 2\ell(y) - \ell(w)}{2}} R_{x,y}(q^{-1}) P_{y,w}(q).$$

We can now see that this recursion has a unique solution  $P_{x,w}$  with required properties, as the two terms on the left are supposed to be polynomials in  $q^{\frac{1}{2}}$  and  $q^{-\frac{1}{2}}$  without constant terms.

The elements  $C_w$  form a basis of the Hecke algebra called the **Kazhdan-Lusztig** basis, and the polynomials  $P_{y,w}$  are called the **Kazhdan-Lusztig polynomials**.

21.4. **Kazhdan-Lusztig conjecture.** The Kazhdan-Lusztig conjecture (now a theorem) is:

**Theorem 21.6.** (i)  $P_{y,w}$  has non-negative coefficients. (ii) The multiplicity  $[M_{y \bullet \lambda} : L_{w \bullet \lambda}]$  equals  $P_{y,w}(1)$ .

The polynomials  $P_{y,w}$  have the property that if  $y \leq w$  then  $P_{y,w}(0) = 1$ , so if in addition  $\ell(w) - \ell(y) \leq 2$  then  $P_{y,w}(q) = 1$  (indeed, it has to be a polynomial of degree 0). Also if  $w = w_0$  then  $P_{y,w} = 1$  for all y.

**Example 21.7.** For type  $A_2$  ( $\mathfrak{g} = \mathfrak{sl}_3$ ) we have the following decompositions in the Grothendieck group of  $\mathcal{O}_{\chi_{\lambda}}$  (where we abbreviate  $s_{i_1}...s_{i_k} \cdot \lambda$  as  $i_1...i_k$ :

$$M_{121} = L_{121}$$
 $M_{12} = L_{12} + L_{121}$ 
 $M_{21} = L_{21} + L_{121}$ 
 $M_{1} = L_{1} + L_{12} + L_{121}$ 
 $M_{1} = L_{1} + L_{12} + L_{21} + L_{121}$ 
 $M_{2} = L_{2} + L_{12} + L_{21} + L_{121}$ 
 $M_{0} = L_{0} + L_{1} + L_{2} + L_{12} + L_{21} + L_{121}$ 

**Exercise 21.8.** Compute the Cartan matrix of the category  $\mathcal{O}_{\chi_{\lambda}}$  for  $\mathfrak{g} = \mathfrak{sl}_3$  for regular weights  $\lambda$ .

#### 22. Projective functors - I

22.1. Projective functors and projective  $\theta$ -functors. Let  $\text{Rep}(\mathfrak{g})_f$  be the category of  $\mathfrak{g}$ -modules in which the center  $Z(\mathfrak{g})$  of  $U(\mathfrak{g})$  acts through its finite-dimensional quotient. We have

$$\operatorname{Rep}(\mathfrak{g})_f = \bigoplus_{\theta \in \mathfrak{h}^*/W} \operatorname{Rep}(\mathfrak{g})_{\theta},$$

where  $\operatorname{Rep}(\mathfrak{g})_{\theta}$  is the category of modules with generalized infinitesimal character  $\theta$ . Recall that for a finite-dimensional  $\mathfrak{g}$ -module V we have an exact functor  $F_V : \operatorname{Rep}(\mathfrak{g}) \to \operatorname{Rep}(\mathfrak{g})$  given by  $X \mapsto V \otimes X$  (e.g.,  $F_{\mathbb{C}} = \operatorname{Id}$ ), and that if M has infinitesimal character  $\chi_{\lambda}$  then

$$F_V(M) = (V \otimes U_{\chi_{\lambda}}) \otimes_{U_{\chi_{\lambda}}} M.$$

Recall also that the infinitesimal characters occurring in the left  $\mathfrak{g}$ -module  $V \otimes U_{\chi_{\lambda}}$  are  $\chi_{\lambda+\beta}$  for  $\beta \in P(V)$  (Corollary 18.10); thus the infinitesimal characters occurring in  $F_V(M)$  belong to the same set. It follows that

$$F_V(\operatorname{Rep}(\mathfrak{g})_{\chi_{\lambda}}) \subset \bigoplus_{\beta \in P(V)} \operatorname{Rep}(\mathfrak{g})_{\chi_{\lambda+\beta}},$$

hence  $F_V$  maps  $\text{Rep}(\mathfrak{g})_f$  to itself. Finally note that  $F_{V^*}$  is both right and left adjoint to  $F_V$ .

**Definition 22.1.** A **projective functor** is an endofunctor of  $\text{Rep}(\mathfrak{g})_f$  which is isomorphic to a direct summand in  $F_V$  for some V.

**Example 22.2.** For  $\theta \in \mathfrak{h}^*/W$  let  $\Pi_{\theta} : \operatorname{Rep}(\mathfrak{g})_f \to \operatorname{Rep}(\mathfrak{g})_{\theta}$  be the projection. Then  $\operatorname{Id} = \bigoplus_{\theta \in \mathfrak{h}^*/W} \Pi_{\theta}$ , hence  $\Pi_{\theta}$  is a projective functor.

It is easy to see that projective functors form a category which is closed under taking compositions, direct summands and finite direct sums, and every projective functor admits a left and right adjoint which are also projective functors (we'll see that they are isomorphic). It is also clear that every projective functor F has a decomposition

$$F = \bigoplus_{\theta, \chi \in \mathfrak{h}^*/W} \Pi_{\chi} \circ F \circ \Pi_{\theta}.$$

Finally, projective functors obviously map category  $\mathcal{O}$  to itself and by Proposition 16.5(i) send projectives of this category to projectives.

For a infinitesimal character  $\theta: Z(\mathfrak{g}) \to \mathbb{C}$  let  $\operatorname{Rep}(\mathfrak{g})^n_{\theta} \subset \operatorname{Rep}(\mathfrak{g})_{\theta}$  be the subcategory of modules annihilated by  $(\operatorname{Ker}\theta)^n$ . In other words,  $\operatorname{Rep}(\mathfrak{g})^n_{\theta}$  is the category of left modules over the algebra

$$U_{\theta}^{(n)} := U(\mathfrak{g})/(\mathrm{Ker}\theta)^n U(\mathfrak{g}).$$

Every  $M \in \operatorname{Rep}(\mathfrak{g})_{\theta}$  is the nested union of submodules  $M_n \subset M$  of elements killed by  $(\operatorname{Ker}\theta)^n$ , and  $M_n \in \operatorname{Rep}(\mathfrak{g})^n_{\theta}$ . Note that  $U_{\theta}^{(1)} = U_{\theta}$  and  $\operatorname{Rep}(\mathfrak{g})^1_{\theta}$  is the category of modules with infinitesimal character  $\theta$ .

For a projective functor F denote by  $F(\theta)$  the restriction of F to  $\text{Rep}(\mathfrak{g})^1_{\theta}$ .

**Definition 22.3.** A **projective**  $\theta$ **-functor** is a direct summand in  $F_V(\theta)$ .

For example, if F is a projective functor then  $F(\theta)$  is a projective  $\theta$ -functor.

**Theorem 22.4.** Let  $F_1, F_2$  be projective  $\theta$ -functors for  $\theta = \chi_{\lambda}$ . Let

$$i_{\lambda}: \operatorname{Hom}(F_1, F_2) \to \operatorname{Hom}(F_1(M_{\lambda-\rho}), F_2(M_{\lambda-\rho})).$$

Then  $i_{\lambda}$  is an isomorphism.

*Proof.* It suffices to assume  $F_j = F_{V_j}(\theta)$ , j = 1, 2. Let  $V = V_1^* \otimes V_2$ . Then  $\text{Hom}(F_1, F_2) = \text{Hom}(\text{Id}(\theta), F_V(\theta))$  and

$$\operatorname{Hom}(F_1(M_{\lambda-\rho}), F_2(M_{\lambda-\rho})) = \operatorname{Hom}_{\mathfrak{q}}(M_{\lambda-\rho}, V \otimes M_{\lambda-\rho}).$$

Thus it suffices to show that the natural map

$$i_{\lambda}: \operatorname{Hom}(\operatorname{Id}(\theta), F_{V}(\theta)) \to \operatorname{Hom}_{\mathfrak{a}}(M_{\lambda-\rho}, V \otimes M_{\lambda-\rho})$$

is an isomorphism.

Recall that for associative unital algebras A, B, a right exact functor  $F: A - \text{mod} \to B - \text{mod}$  has the form  $F(X) = F(A) \otimes_A X$ , where F(A) is the corresponding (B, A)-bimodule. Thus if  $F_1, F_2$  are two such functors then  $\text{Hom}(F_1, F_2) \cong \text{Hom}_{(B,A)-\text{bimod}}(F_1(A), F_2(A))$ . Applying this to  $A = U_\theta$  and  $B = U(\mathfrak{g})$ , we get

$$\operatorname{Hom}(\operatorname{Id}(\theta), F_V(\theta)) = \operatorname{Hom}_{(U(\mathfrak{g}), U_{\theta}) - \operatorname{bimod}}(U_{\theta}, V \otimes U_{\theta}) = (V \otimes U_{\theta})^{\mathfrak{g}_{\operatorname{ad}}}.$$

Moreover, upon this identification the map  $i_{\lambda}$  becomes the natural map

$$i_{\lambda}: (V \otimes U_{\chi_{\lambda}})^{\mathfrak{g}_{\mathrm{ad}}} \to \mathrm{Hom}(M_{\lambda-\rho}, V \otimes M_{\lambda-\rho})^{\mathfrak{g}_{\mathrm{ad}}}.$$

But this map is an isomorphism by the Duflo-Joseph theorem, as it is obtained by restricting the Duflo-Joseph isomorphism

$$U_{\chi_{\lambda}} \cong \operatorname{Hom}_{\operatorname{fin}}(M_{\lambda-\rho}, M_{\lambda-\rho})$$

to the multiplicity space of  $V^*$ .

#### 22.2. Lifting projective $\theta$ -functors.

**Proposition 22.5.** (i) If  $F_1$ ,  $F_2$  are projective functors then every morphism  $\phi: F_1(\theta) \to F_2(\theta)$  lifts to a morphism  $\widehat{\phi}: F_1|_{\operatorname{Rep}(\mathfrak{g})_{\theta}} \to F_2|_{\operatorname{Rep}(\mathfrak{g})_{\theta}}$ .

(ii) If 
$$F_1 = F_2$$
 and  $\phi^2 = \phi$  then we can choose  $\widehat{\phi}$  so that  $\widehat{\phi}^2 = \widehat{\phi}$ .

(iii) If  $\phi$  is an isomorphism then so is  $\widehat{\phi}$ .

*Proof.* (i) It suffices to show that there exist morphisms

$$\phi_n: F_1|_{\operatorname{Rep}(\mathfrak{g})^n_{\theta}} \to F_2|_{\operatorname{Rep}(\mathfrak{g})^n_{\theta}}$$

such that  $\phi_n$  restricts to  $\phi_{n-1}$  and  $\phi_1 = \phi$ ; then  $\widehat{\phi}$  is the projective limit of  $\phi_n$ . As before, we may assume without loss of generality that  $F_1 = \text{Id}$  and  $F_2 = F_V$ . As explained in the proof of Theorem 22.4, we have

$$\operatorname{Hom}(F_1|_{\operatorname{Rep}(\mathfrak{g})_{\theta}^n}, F_2|_{\operatorname{Rep}(\mathfrak{g})_{\theta}^n}) = \operatorname{Hom}_{(U(\mathfrak{g}), U_{\theta}^{(n)}) - \operatorname{bimod}}(U_{\theta}^{(n)}, V \otimes U_{\theta}^{(n)}) = (V \otimes U_{\theta}^{(n)})^{\mathfrak{g}_{\operatorname{ad}}}.$$

This implies the statement, as the map  $U_{\theta}^{(n)} \to U_{\theta}^{(n-1)}$  is onto and  $V \otimes U_{\theta}^{(n)}$  is a semisimple  $\mathfrak{g}_{ad}$ -module.

(ii) Let F be a direct summand in  $F_V$ . Let  $p: F_V \to F_V$  be the projection to F. Let  $A := \operatorname{End}(F(\theta)) = p\operatorname{End}(F_V(\theta))p$  and  $\phi \in A$ . Let  $F^n(\theta)$  be the restriction of F to  $\operatorname{Rep}(\mathfrak{g})^n_{\theta}$ , so that  $F^1(\theta) = F(\theta)$ . We have

$$A_n := \operatorname{End}(F^n(\theta)) = p\operatorname{End}(F_V^n(\theta))p = p(\operatorname{EndV} \otimes U_{\theta}^{(n)})^{\mathfrak{g}_{\operatorname{ad}}}p.$$

So we have a chain of surjective homomorphisms

$$\dots \to A_n \to A_{n-1} \to \dots \to A_1 = A$$

and our job is to show that  $\phi$  admits a chain of lifts

$$\dots \mapsto \phi_n \mapsto \phi_{n-1} \mapsto \dots \mapsto \phi_1 = \phi$$

such that  $\phi_n \in A_n$  and  $\phi_n^2 = \phi_n$ .

To this end, note that the kernel I of the surjection  $A_n \to A_{n-1}$  satisfies  $I^2 = 0$ , so I is a left and right module over  $A_n/I = A_{n-1}$ . So we can construct the desired chain of lifts by induction in n as follows. Pick any lift  $e_*$  of  $e_0 := \phi_{n-1}$ . Then  $e_* - e_*^2 = a \in I$ , and  $e_0 a = a e_0$ . We look for an idempotent e in the form  $e = e_* + b$ ,  $b \in I$ . The equation  $e^2 = e$  is then equivalent to

$$e_0b + be_0 - b = a.$$

Set  $b = (2e_0 - 1)a$ . Then

$$e_0b + be_0 - b = 2e_0a + (1 - 2e_0)a = a,$$

as desired. Now we can set  $\phi_n = e$ .

(iii) If  $\phi: F_1(\theta) \to F_2(\theta)$  is an isomorphism then it has the inverse  $\psi: F_2(\theta) \to F_1(\theta)$  such that  $\phi \circ \psi = 1$ ,  $\psi \circ \phi = 1$ . Let  $\widehat{\phi} = (\phi_n)$  be a lift of  $\phi$ . Our job is to show that  $\phi_n$  are isomorphisms for all n, which yields (iii). We prove it by induction in n.

The base is trivial, so we just need to do the induction step from n-1 to n. By the induction assumption,  $\phi_{n-1}$  is invertible with  $\phi_{n-1}^{-1} = \psi_{n-1}$ .

Let  $\psi_n$  be a lift of  $\psi_{n-1}$  and consider the composition  $\psi_n \circ \phi_n$  in the corresponding algebra  $A_n$ . Let I be the kernel of the map  $A_n \to A_{n-1}$ . Then  $\psi_n \circ \phi_n = 1 + a$  where  $a \in I$ . Since  $I^2 = 0$ , setting  $\psi'_n := (1-a) \circ \psi_n$ , we get  $\psi'_n \circ \phi_n = 1$ . Similarly we can construct  $\psi''_n$  such that  $\phi_n \circ \psi''_n = 1$ . Thus  $\psi'_n = \psi''_n$  is the inverse of  $\phi_n$ . This completes the induction step.

Corollary 22.6. (i) Let  $F_1, F_2$  be projective functors. Then: any isomorphism  $F_1(M_{\lambda-\rho}) \cong F_2(M_{\lambda-\rho})$  lifts to an isomorphism

$$F_1|_{\operatorname{Rep}(\mathfrak{g})_{\chi_{\lambda}}} \to F_2|_{\operatorname{Rep}(\mathfrak{g})_{\chi_{\lambda}}};$$

- (ii) Let F be a projective functor. Then any decomposition  $F(M_{\lambda-\rho}) = \bigoplus_i M_i$  can be lifted to a decomposition  $F = \bigoplus_i F_i$  where  $F_i$  are projective functors and  $F_i(M_{\lambda-\rho}) = M_i$ ;
- (iii) Every projective  $\theta$ -functor is of the form  $F(\theta)$  for a projective functor F.
- *Proof.* (i) follows from Proposition 22.5(i),(iii) and Theorem 22.4.
  - (ii) follows from Proposition 22.5(ii).

To prove (iii), let H be a projective  $\theta$ -functor, so  $H \oplus H' = F_V(\theta)$ . Thus  $H(M_{\lambda-\rho}) \oplus H'(M_{\lambda-\rho}) = F_V(M_{\lambda-\rho})$ . So by (ii) there is a projective functor F with  $F(\theta)(M_{\lambda-\rho}) \cong F(M_{\lambda-\rho}) \cong H(M_{\lambda-\rho})$ . Thus  $H \cong F(\theta)$  by Theorem 22.4.

#### 22.3. Decomposition of projective functors.

**Proposition 22.7.** (i) Each projective functor F is a direct sum of indecomposable projective functors. Moreover, for  $F \circ \Pi_{\theta}$  this sum is finite.

- (ii) If  $F = F \circ \Pi_{\chi_{\lambda}}$  for dominant  $\lambda$  is an indecomposable projective functor then  $F(M_{\lambda-\rho}) = P_{\mu-\rho}$  for some  $\mu \in \mathfrak{h}^*$ .
- Proof. (i) We have  $F = \bigoplus_{\theta \in \mathfrak{h}^*/W} F \circ \Pi_{\theta}$ , so it suffices to show the statement for  $F \circ \Pi_{\theta}$ . Let  $\theta = \chi_{\lambda}$ , and consider  $F \circ \Pi_{\theta}(M_{\lambda \rho}) \in \mathcal{O}$ . Let us write this object as a finite direct sum of indecomposables,  $\bigoplus_{i=1}^{N} M_i$ . Then by Corollary 22.6(ii) we get a decomposition  $F \circ \Pi_{\theta} = \bigoplus_{i=1}^{N} F_i$ , and all  $F_i$  are indecomposable.
- (ii) Since F is indecomposable and  $M_{\lambda-\rho}$  is projective,  $F(M_{\lambda-\rho})$  is indecomposable and projective, so the statement follows.

#### 23. Projective functors - II

23.1. The Grothendieck group of  $\mathcal{O}$ . The Grothendieck group  $K(\mathcal{O})$  of  $\mathcal{O}$  is freely spanned by the classes of simple modules  $[L_{\lambda-\rho}]$  or, more conveniently, by the classes of Verma modules  $[M_{\lambda-\rho}]$ , which we'll denote  $\delta_{\lambda}$ ; so it is a basis of  $K(\mathcal{O})$ . Put an inner product on  $K(\mathcal{O})$  by declaring this basis to be orthonormal. Note that if P is projective then

$$([P], [M]) = \dim \operatorname{Hom}(P, M).$$

Indeed, in this case dim Hom(P, M) is a linear function of [M], and for  $M = M_{\mu}$  by the BGG reciprocity we have:

dim Hom
$$(P_{\lambda}, M_{\mu}) = d_{\mu\lambda} = d_{\lambda\mu}^* = (\sum_{\nu} d_{\lambda\nu}^* \delta_{\nu+\rho}, \delta_{\mu+\rho}) = ([P_{\lambda}], [M_{\mu}]).$$

Since every projective functor F is exact, it defines an endomorphism [F] of  $K(\mathcal{O})$ . For example,

$$[F_V]\delta_{\lambda} = \sum_{\beta} m_V(\beta)\delta_{\lambda+\beta},$$

where  $m_V(\beta)$  is the weight multiplicity of  $\beta$  in V. Clearly  $[F_1 \oplus F_2] = [F_1] + [F_2]$  and  $[F_1 \circ F_2] = [F_1][F_2]$ .

**Theorem 23.1.** (i) If  $F_1, F_2$  are projective functors with  $[F_1] = [F_2]$  then  $F_1 \cong F_2$ .

- (ii) If  $(F, F^{\vee})$  are an adjoint pair of projective functors then [F] is adjoint to  $[F^{\vee}]$  under the inner product on  $K(\mathcal{O})$ .
- (iii) For a projective functor F, its left and right adjoint are isomorphic.

*Proof.* (i) By Corollary 22.6, to prove (i), it suffices to show that

$$F_1(M_{\lambda-\rho}) \cong F_2(M_{\lambda-\rho})$$

for all dominant  $\lambda$ . These objects are projective, so it is enough to check that they have the same character (or define the same element of  $K(\mathcal{O})$ ). This implies the claim.

(ii) We need to show that  $([F]x, y) = (x, [F^{\vee}]y)$ . It suffices to take x = [P] for projective P and y = [M]. Then, since F(P) is projective, we have

$$([F][P], [M]) = ([F(P)], [M]) = \dim \operatorname{Hom}(F(P), M) =$$

 $\dim \mathrm{Hom}(P, F^{\vee}(M)) = ([P], [F^{\vee}(M)]) = ([P], [F^{\vee}][M]),$ 

as claimed.

(iii) follows from (i),(ii).

23.2. W-invariance. We have an action of the Weyl group W on  $K(\mathcal{O})$  by  $w\delta_{\lambda} := \delta_{w\lambda}$ .

**Theorem 23.2.** If F is a projective functor then [F] commutes with W on  $K(\mathcal{O})$ .

*Proof.* We may assume that  $F = \Pi_{\chi} \circ F \circ \Pi_{\theta}$  for  $\chi, \theta \in \mathfrak{h}^*/W$  and F is indecomposable. Let  $\lambda$  be a dominant weight such that  $\theta = \chi_{\lambda}$ . Define

$$S = \{ \mu \in \lambda + P : \chi_{\mu} = \chi \}.$$

Let us say that  $\lambda$  dominates  $\gamma$  if for every  $\mu \in S$  we have  $\lambda - \mu \in P_+$ .

**Lemma 23.3.** When  $\lambda$  dominates  $\chi$  then

- (i) Theorem 23.2 holds;
- (ii) For each  $\mu \in S$  there exists an indecomposable projective functor  $F_{\mu}$  sending  $M_{\lambda-\rho}$  to  $P_{\mu-\rho}$ .
- *Proof.* (i) For a finite-dimensional  $\mathfrak{g}$ -module V, let  $G_V := \Pi_{\chi} \circ F_V \circ \Pi_{\theta}$ . Since the character of V is W-invariant,  $[F_V]$  commutes with W, hence so does  $[G_V]$ . Thus its suffices to show that [F] is an integer linear combination of  $[G_V]$  for various V.

By Proposition 22.7(ii),  $F(M_{\lambda-\rho}) = P_{\mu-\rho}$ , where  $\mu \in S$ . Let  $\beta := \lambda - \mu$ . By our assumption,  $\beta \in P_+$ . Define  $n(\beta) := (\beta, 2\rho^{\vee})$ , a nonnegative integer. We will prove the required statement by induction in  $n(\beta)$ .

The base of induction is  $n(\beta) = 0$ , hence  $\beta = 0$  and  $\mu = \lambda$ . So  $F(M_{\lambda-\rho}) = P_{\lambda-\rho} = M_{\lambda-\rho}$ . This implies that  $F = \Pi_{\theta}$ , so [F] is clearly commutes with W.

So it remains to justify the induction step. Let  $L:=L^*_{\beta}$ , a finite-dimensional  $\mathfrak{g}$ -module. Consider the decomposition of the functor  $G_L$  into indecomposables (which we have shown to exist in Proposition 22.7(ii)):  $G_L = \bigoplus_j F_{\nu_j}$ , where  $\nu_j \in S$  and  $F_{\nu_j}(M_{\lambda-\rho}) = P_{\nu_j-\rho}$  (this direct sum may contain repetitions). So  $G_L(M_{\lambda-\rho}) = \bigoplus_j P_{\nu_j-\rho}$ . Thus

$$[G_L]\delta_\lambda = \sum_{j,\gamma} d^*_{\nu_j,\gamma} \delta_\gamma = \sum_{j,\gamma} d_{\gamma,\nu_j} \delta_\gamma = \sum_j \delta_{\nu_j} + \sum_{j,\gamma > \nu_j} d_{\gamma,\nu_j} \delta_\gamma.$$

On the other hand,

$$[G_L]\delta_{\lambda} = [G_L(M_{\lambda-\rho})] = [\Pi_{\chi}(L \otimes M_{\lambda-\rho})] = [\Pi_{\chi}] \sum_{\eta} m_L(\eta) \delta_{\lambda+\eta} =$$

$$\begin{split} [\Pi_{\chi}] \sum_{\eta} m_{L_{\beta}}(\eta) \delta_{\lambda - \eta} &= \sum_{\eta: \chi_{\lambda - \eta} = \chi} m_{L_{\beta}}(\eta) \delta_{\lambda - \eta} = \sum_{\nu: \chi_{\nu} = \chi} m_{L_{\beta}}(\beta + \mu - \nu) \delta_{\nu} = \\ \delta_{\mu} &+ \sum_{\nu > \mu: \chi_{\nu} = \chi} m_{L_{\beta}}(\beta + \mu - \nu) \delta_{\nu}. \end{split}$$

These two formulas for  $[G_L]\delta_{\lambda}$  jointly imply that  $\nu_j \geq \mu$  for all j, and only one of them equals  $\mu$ , i.e.,

(17) 
$$G_L = F_{\mu} \oplus \bigoplus_{\nu \in S, \nu > \mu} c_{\nu\mu} F_{\nu}$$

for some constants  $c_{\nu\mu} \in \mathbb{Z}_{\geq 0}$ . But if  $\nu > \mu$  then  $n(\lambda - \nu) < n(\lambda - \mu)$ , so by the induction assumption  $[F_{\nu}]$  for all  $\nu > \mu$  in this sum are linear combinations of  $[G_V]$  for various V. Thus so is  $F_{\mu}$ . But  $F(M_{\lambda-\rho}) = F_{\mu}(M_{\lambda-\rho})$ , so  $F \cong F_{\mu}$  and the induction step follows.

(ii) The functor 
$$F_{\mu}$$
 from (17) has the desired property.

Now we are ready to prove the theorem in the general case. So  $\lambda$  no longer needs to dominate  $\chi$ . However, for sufficiently large integer N, the weight  $\lambda + N\rho$  dominates both  $\chi$  and  $\theta$ . Let  $\theta_N := \chi_{\lambda+N\rho}$ . We have shown in Lemma 23.3(ii) that there exists an indecomposable projective functor  $G = \Pi_{\theta} \circ G \circ \Pi_{\theta_N}$  such that  $G(M_{\lambda+(N-1)\rho}) = P_{\lambda-\rho} = M_{\lambda-\rho}$ . Moreover, by Lemma 23.3(i), W commutes with both [G] and  $[F \circ G] = [F][G]$ . Thus for  $w \in W$ ,

$$w[F]\delta_{\lambda} = w[F][G]\delta_{\lambda+N\rho} = [F][G]w\delta_{\lambda+N\rho} = [F]w[G]\delta_{\lambda+N\rho} = [F]w\delta_{\lambda} = [F]\delta_{w\lambda}.$$
  
So for  $u \in W$ ,

$$u[F]\delta_{w\lambda} = uw[F]\delta_{\lambda} = [F]uw\delta_{\lambda} = [F]u\delta_{w\lambda},$$

i.e.,

$$u[F]\delta_{\mu} = [F]u\delta_{\mu}$$

for all  $\mu \in \mathfrak{h}^*$ , as claimed.

**Lemma 23.4.** Let  $\lambda \in \mathfrak{h}^*$  be dominant and  $\phi, \psi \in \lambda + P$ ,  $\psi \leq \phi$ . Then  $(\lambda - \phi)^2 \leq (\lambda - \psi)^2$ , and if  $(\lambda - \phi)^2 = (\lambda - \psi)^2$  then  $\psi \in W_{\lambda}\phi$ .

*Proof.* Consider the subgroup  $W_{\lambda+Q} \subset W$ . By Proposition 15.12, it is the Weyl group of a root system  $R' \subset R$ . Let us first prove the result when  $\mu <_{\alpha} \lambda$ ,  $\alpha \in R$ , i.e.,  $\psi = s_{\alpha} \phi$ ,  $\psi \neq \phi$ . Then  $\alpha \in R'$  and thus by Proposition 16.1

$$(\lambda, \alpha^{\vee}) = a \in \mathbb{Z}_{\geq 1}, \ (\phi, \alpha^{\vee}) = -(\psi, \alpha^{\vee}) = b \in \mathbb{Z}_{\geq 0}.$$

We have  $\lambda = \frac{1}{2}a\alpha + \lambda'$ ,  $\phi = \frac{1}{2}b\alpha + \phi'$ ,  $\psi = -\frac{1}{2}b\alpha + \phi'$ . where  $\lambda'$ ,  $\phi'$  are orthogonal to  $\alpha$ . Thus

$$(\lambda - \psi)^2 - (\lambda - \phi)^2 = ((\frac{a+b}{2})^2 - (\frac{a-b}{2})^2)\alpha^2 = ab\alpha^2.$$

So this is  $\geq 0$ , and if it is zero then either b=0, in which case  $\phi=\psi$  and there is nothing to prove, or a=0, so  $s_{\alpha}\lambda=\lambda$  and  $s_{\alpha}\in W_{\lambda}$ , as claimed.

Now let us consider the general case. By assumption, there is a chain

$$\psi = \psi_m <_{\alpha^m} \psi_{m-1} \dots <_{\alpha^1} \psi_0 = \phi,$$

where  $\alpha^1, ..., \alpha^m$  are positive roots of R. Thus, as we've shown,

$$(\lambda - \psi_i)^2 \le (\lambda - \psi_{i-1})^2$$

for all  $i \geq 1$ , so  $(\lambda - \phi)^2 \leq (\lambda - \psi)^2$ . Moreover, if  $(\lambda - \phi)^2 = (\lambda - \psi)^2$  then  $(\lambda - \psi_{i-1})^2 = (\lambda - \psi_i)^2$  for all  $i \geq 1$  so  $\psi_{i-1} \in W_{\lambda}\psi_i$ , hence  $\psi \in W_{\lambda}\phi$ .

**Remark 23.5.** The last statement of Lemma 23.4 fails if the partial order  $\leq$  is replaced with  $\leq$ . For example, take  $R = A_3$  and  $\psi = (0, 3, 1, 2)$ ,  $\phi = (1, 2, 3, 0)$ , as in Remark 15.10 (so  $\psi < \phi$  but  $\psi \not\prec \phi$ ), and let  $\lambda := (1, 1, 0, 0)$ . Then  $(\lambda - \phi)^2 = (\lambda - \psi)^2 = 10$ , but  $W_{\lambda} = \langle (12), (34) \rangle$ , so  $\psi \notin W_{\lambda} \phi$ .

23.3. Classification of indecomposable projective functors. Denote by  $\Xi_0$  the set of pairs  $(\lambda, \mu)$  of weights in  $\mathfrak{h}^*$  such that  $\lambda - \mu \in P$ , and let  $\Xi := \Xi_0/W$ . So in general an element  $\xi \in \Xi$  can be represented by more than one pair. Let us say that the pair  $(\mu, \lambda)$  representing  $\xi$  is **proper** if  $\lambda$  is dominant and  $\mu$  is a minimal element of  $W_{\lambda}\mu$  with respect to the partial order  $\preceq$  (where  $W_{\lambda}$  is the stabilizer of  $\lambda$  in W). It is clear that any  $\xi$  has a proper representative. This representative is not unique in general, but for every dominant  $\lambda$  in the W-orbit of the second coordinate of  $\xi$ , there is a unique  $\mu$  such that  $(\mu, \lambda)$  is a proper representation of  $\xi$  (indeed,  $W_{\lambda}\mu$  has a unique minimal element).

**Theorem 23.6.** For any  $\xi \in \Xi$  there exists an indecomposable projective functor  $F_{\xi}$  such that  $F_{\xi}(M_{\nu-\rho}) = 0$  if  $\chi_{\nu} \neq \chi_{\lambda}$  and  $F_{\xi}(M_{\lambda-\rho}) = P_{\mu-\rho}$  for any proper representation  $(\mu, \lambda)$  of  $\xi$ . The assignment  $\xi \mapsto F_{\xi}$  is a bijection between  $\Xi$  and the set of isomorphism classes of indecomposable projective functors.

*Proof.* For a projective functor F let

$$a_F(\mu,\lambda) := (\delta_\mu, [F]\delta_\lambda)$$

be the matrix coefficients of [F]. If  $\lambda$  is dominant then  $F(M_{\lambda-\rho})$  is projective, so  $a_F(\mu,\lambda) \geq 0$  for all  $\mu \in \mathfrak{h}^*$ . Since by Theorem 23.2 [F] commutes with W, this holds for all  $\lambda \in \mathfrak{h}^*$ .

Let  $S(F) := \{(\mu, \lambda) \in \mathfrak{h}^* \times \mathfrak{h}^* : a_F(\mu, \lambda) > 0\}$ . Since  $a_F(\mu, \lambda) \geq 0$ , if  $F = \bigoplus_i F_i$  then  $S(F) = \bigcup_i S(F_i)$ . Also it is clear that  $S(F_V) \subset \Xi_0$ . It follows that  $S(F) \subset \Xi_0$  for any F, so for  $(\mu, \lambda) \in S(F)$  we have  $\lambda - \mu \in P$ .

Let  $S_*(F)$  be the set of elements of S(F) for which  $(\lambda - \mu)^2$  has maximal value (it is clear that  $(\lambda - \mu)^2$  is bounded on S(F), so  $S_*(F)$ 

is nonempty if  $F \neq 0$ ). Since by Theorem 23.2 [F] commutes with W, both S(F) and  $S_*(F)$  are W-invariant.

We claim that if F is indecomposable, then  $S_*(F)$  is a single Worbit. More specifically, recall that  $F = F \circ \Pi_{\chi_{\lambda}}$  for some dominant  $\lambda$ and  $F(M_{\lambda-\rho}) = P_{\mu-\rho}$  for some  $\mu$ .

**Lemma 23.7.** In this case  $S_*(F) = \xi := W(\mu, \lambda)$  and  $(\mu, \lambda)$  is a proper representation of  $\xi$ .

*Proof.* It suffices to check that if  $(\phi, \lambda) \in S_*(F)$  then  $\phi \in W_{\lambda}\mu$  and  $\mu \leq \phi$ . So let  $(\phi, \lambda) \in S_*(F)$ . Since F is indecomposable,  $\chi_{\mu} = \chi_{\phi}$ , so there exists  $w \in W$  such that  $\mu = w\phi$ . Moreover, by Theorem 20.13,

$$[P_{\mu-\rho}] = \sum_{\mu \prec \eta} d_{\mu\eta}^* \delta_{\eta},$$

we get that  $\mu \leq \psi$ . Thus we may apply Lemma 23.4 with  $\psi = \mu$ . It follows that  $(\lambda - \phi)^2 \leq (\lambda - \mu)^2$ . But by the definition of  $S_*(F)$ , we have  $(\lambda - \phi)^2 \geq (\lambda - \mu)^2$ . Thus  $(\lambda - \phi)^2 = (\lambda - \mu)^2$ . Then Lemma 23.4 implies that  $\phi \in W_{\lambda}\mu$ , as claimed.

Thus to every indecomposable projective functor F we have assigned  $\xi = S_*(F)/W \in \Xi$ . If  $(\mu, \lambda)$  is a proper representation of  $\xi$  then it follows that  $F(M_{\lambda-\rho}) = P_{\mu-\rho}$ , so F is completely determined by  $\xi$  by Corollary 22.6. It remains to show that any  $\xi \in \Xi$  is obtained in this way. To this end, let  $\xi = W(\mu, \lambda)$  (a proper representation), and let V be a finite-dimensional  $\mathfrak{g}$ -module with extremal weight  $\mu - \lambda$ . Then  $(\mu - \lambda)^2 \geq \beta^2$  for any weight  $\beta$  of V, so  $(\mu, \lambda) \in S_*(F_V)$ . This implies that  $(\mu, \lambda) \in S_*(F)$  for some indecomposable direct summand F of  $F_V$ . Since  $S_*(F)/W$  consists of one element, this F must correspond to the element  $\xi$ .

#### 24. Applications of projective functors - I

24.1. **Translation functors.** Let  $\theta, \chi \in \mathfrak{h}^*/W$  and V be a finite-dimensional irreducible  $\mathfrak{g}$ -module. Write  $F_{\chi,V,\theta}$  for the projective functor  $\Pi_{\chi} \circ F_{V} \circ \Pi_{\theta}$ , and let us view it as a functor  $\operatorname{Rep}(\mathfrak{g})_{\theta} \to \operatorname{Rep}(\mathfrak{g})_{\chi}$ .

Pick dominant weights  $\lambda, \mu \in \mathfrak{h}^*$  such that  $\theta = \chi_{\lambda}, \chi = \chi_{\mu}$ , and  $\lambda - \mu \in P$  (this can be done if  $F_{\chi,V,\theta} \neq 0$ , which we will assume).

**Theorem 24.1.** If  $W_{\lambda} = W_{\mu}$  and V has extremal weight  $\mu - \lambda$  then  $F_{\chi,V,\theta} : \operatorname{Rep}(\mathfrak{g})_{\theta} \to \operatorname{Rep}(\mathfrak{g})_{\chi}$  is an equivalence of categories. A quasi-inverse equivalence is given by the functor  $F_{\theta,V^*,\chi}$ .

*Proof.* It suffices to show that

$$F_{\chi,V,\theta}(M_{\lambda-\rho}) = M_{\mu-\rho}, \ F_{\theta,V^*,\chi}(M_{\mu-\rho}) = M_{\lambda-\rho}.$$

Indeed, then

$$F_{\theta,V^*,\chi} \circ F_{\chi,V,\theta}(M_{\lambda-\rho}) = M_{\lambda-\rho}, \ F_{\chi,V,\theta} \circ F_{\theta,V^*,\chi}(M_{\mu-\rho}) = M_{\mu-\rho},$$

so

$$F_{\theta,V^*,\chi} \circ F_{\chi,V,\theta} \cong \mathrm{Id}_{\mathrm{Rep}(\mathfrak{q})_{\theta}}, \ F_{\chi,V,\theta} \circ F_{\theta,V^*,\chi} \cong \mathrm{Id}_{\mathrm{Rep}(\mathfrak{q})_{\chi}},$$

i.e.,  $F_{\chi,V,\theta}$ ,  $F_{\theta,V^*,\chi}$  are mutually quasi-inverse equivalences.

We only prove the first statement, the second one being similar. We have

$$F_{\chi,V,\theta}(M_{\lambda-\rho}) = \Pi_{\chi}(V \otimes M_{\lambda-\rho}).$$

By Corollary 20.5(i),  $V \otimes M_{\lambda-\rho}$  has a standard filtration whose composition factors are  $M_{\lambda+\beta-\rho}$  where  $\beta$  is a weight of V. The only ones among them that survive the application of  $\Pi_{\chi}$  are those for which  $\chi_{\lambda+\beta}=\chi_{\mu}$ , i.e.,  $\lambda+\beta=w\mu$  for some  $w\in W$ . So  $w\mu \leq \mu$  (as  $\mu$  is dominant). Thus, applying Lemma 23.4 with  $\phi=\mu,\psi=w\mu$ , we get

$$(\lambda - \mu)^2 \le (\lambda - w\mu)^2 = \beta^2.$$

On the other hand, since  $\mu - \lambda$  is an extremal weight of V, we have  $(\lambda - \mu)^2 \geq \beta^2$ . It follows that  $(\lambda - \mu)^2 = \beta^2 = (\lambda - w\mu)^2$ . Thus by Lemma 23.4 we may choose  $w \in W_{\lambda}$ . But since  $W_{\lambda} \subset W_{\mu}$ , it follows that  $w\mu = \mu$ , so  $\beta = \mu - \lambda$ . Since the weight multiplicity of an extremal weight is 1, it follows that  $F_{\chi,V,\theta}(M_{\lambda-\rho}) = M_{\mu-\rho}$ , as claimed.  $\square$ 

Theorem 24.1 shows that for dominant  $\lambda$  the category  $\operatorname{Rep}(\mathfrak{g})_{\chi_{\lambda}}$  depends (up to equivalence) only on the coset  $\lambda + P$  and the subgroup  $W_{\lambda} \subset W$ . In view of Theorem 24.1, the functors  $F_{\chi,V,\theta}$  are called **translation functors** (as they translate between different infinitesimal characters).

**Remark 24.2.** Suppose we only have  $W_{\lambda} \subset W_{\mu}$  instead of  $W_{\lambda} = W_{\mu}$  (with all the other assumptions being the same). Then the proof of Theorem 24.1 still shows that  $F_{\chi,V,\theta}(M_{\lambda-\rho}) = M_{\mu-\rho}$ . Thus  $[F_{\chi,V,\theta}]\delta_{\lambda} = \delta_{\mu}$ , and since by Theorem 23.2  $[F_{\chi,V,\theta}]$  is W-invariant, it follows that  $[F_{\chi,V,\theta}]\delta_{\nu} = \delta_{\mu}$  for all  $\nu \in W_{\mu}\lambda$ .

On the other hand, we no longer have  $F_{\theta,V^*,\chi}(M_{\mu-\rho})=M_{\lambda-\rho}$ , in general. Namely, the proof of Theorem 24.1 shows that  $F_{\theta,V^*,\chi}(M_{\mu-\rho})$  has a filtration whose successive quotients are  $M_{\nu-\rho}$ ,  $\nu \in W_{\mu}\lambda$ , each occurring with multiplicity 1 (so the length of this filtration is  $|W_{\mu}/W_{\lambda}|$ ). Thus

$$[F_{\theta,V^*,\chi}]\delta_{\mu} = \sum_{\nu \in W_{\mu}\lambda} \delta_{\nu}.$$

It follows that

$$[F_{\chi,V,\theta}][F_{\theta,V^*,\chi}]\delta_{\mu} = |W_{\mu}/W_{\lambda}|\delta_{\mu},$$

hence  $F_{\chi,V,\theta} \circ F_{\theta,V^*,\chi}(M_{\mu-\rho}) = |W_{\mu}/W_{\lambda}|M_{\mu-\rho}$  (as the left hand side is projective). Thus  $F_{\chi,V,\theta} \circ F_{\theta,V^*,\chi} \cong |W_{\mu}/W_{\lambda}| \mathrm{Id}$ .

**Remark 24.3.** Let  $\mathcal{C} \subset \text{Rep}(\mathfrak{g})$  be a full subcategory invariant under all  $F_V$  and  $\Pi_{\theta}$ , and  $\mathcal{C}_{\theta} := \Pi_{\theta}\mathcal{C} = \mathcal{C} \cap \text{Rep}(\mathfrak{g})_{\theta}$ . Then Theorem 24.1 implies that if  $W_{\lambda} = W_{\mu}$  then the functors  $F_{\chi,V,\theta}, F_{\theta,V^*,\chi}$  are mutually quasi-inverse equivalences between  $\mathcal{C}_{\theta}$  and  $\mathcal{C}_{\chi}$ . Interesting examples of this include:

- 1.  $C = \mathcal{O}$ . In this case we obtain that for dominant  $\lambda$  the category  $\mathcal{O}_{\chi_{\lambda}}$  up to equivalence depends only on  $\lambda + P$  and the stabilizer  $W_{\lambda}$ . In particular, for regular dominant integral  $\lambda$  all these categories are equivalent.
- 2.  $\mathcal{C}$  is the category of  $\mathfrak{g}$ -modules which are locally finite and semisimple with respect to a reductive Lie subalgebra  $\mathfrak{k} \subset \mathfrak{g}$ . If  $\mathfrak{k}$  is the fixed subalgebra of an involution of  $\mathfrak{g}$ , this category contains the category of  $(\mathfrak{g}_{\mathbb{R}}, K)$ -modules for any connected compact group K such that  $\text{Lie}K = \mathfrak{k}$ . Namely, it is just the subcategory of modules that integrate to K.
- 24.2. Two-sided ideals in  $U_{\theta}$  and submodules of Verma modules. Let  $\theta = \chi_{\lambda}$  for dominant  $\lambda$ . Let  $\Omega_{\theta}$  denote the lattice of two-sided ideals in  $U_{\theta}$  (i.e., the set of two-sided ideals equipped with the operations of sum and intersection). Likewise, let  $\Omega(\lambda)$  be the lattice of submodules of  $M_{\lambda-\rho}$ . We have a map  $\nu:\Omega_{\theta}\to\Omega(\lambda)$  given by  $\nu(J)=JM_{\lambda-\rho}$ . It is clear that  $\nu$  preserves inclusion and arbitrary sums.

**Theorem 24.4.** (i)  $I \subset J$  iff  $\nu(I) \subset \nu(J)$ . In particular,  $\nu$  is injective.

- (ii) The image of  $\nu$  is the set of submodules of  $M_{\lambda-\rho}$  which are quotients of direct sums of  $P_{\mu-\rho}$  where  $\chi_{\mu} = \chi_{\lambda}$ ,  $\mu \leq \lambda$  and  $\mu \leq W_{\lambda}\mu$ .
- (iii) If  $\lambda$  is regular (i.e.,  $W_{\lambda} = 1$ ) then  $\nu$  is an isomorphism of lattices.

Proof. (i) Let F be a projective  $\theta$ -functor, and  $\phi: F \to \mathrm{Id}_{\theta}$  a morphism of functors  $\mathrm{Rep}(\mathfrak{g})^1_{\theta} \to \mathrm{Rep}(\mathfrak{g})$ . Let  $M(\phi, F)$  be the image of the map  $\phi_{M_{\lambda-\rho}}: F(M_{\lambda-\rho}) \to M_{\lambda-\rho}$  and  $J(\phi, F)$  the image of  $\phi_{U_{\theta}}: F(U_{\theta}) \to U_{\theta}$ . Note that  $\phi_{U_{\theta}}$  is a morphism of  $(U(\mathfrak{g}), U_{\theta})$ -bimodules, so  $J(\phi, F)$  is a subbimodule of  $U_{\theta}$ , i.e., a 2-sided ideal. Let  $a: U_{\theta} \to M_{\lambda-\rho}$  be the surjection given by  $a(u) = uv_{\lambda-\rho}$ . Then by functoriality of  $\phi$ 

$$a \circ \phi_{U_{\theta}} = \phi_{M_{\lambda-\theta}} \circ a.$$

Hence

$$\nu(J(\phi, F)) = J(\phi, F)M_{\lambda - \rho} = J(\phi, F)v_{\lambda - \rho} = a(J(\phi, F)) =$$
$$\operatorname{Im}(a \circ \phi_{U_{\theta}}) = \operatorname{Im}(\phi_{M_{\lambda - \rho}} \circ a) = \operatorname{Im}(\phi_{M_{\lambda - \rho}}) = M(\phi, F).$$

Let us show that any 2-sided ideal J in  $U_{\theta}$  is of the form  $J(\phi, F)$  for some F,  $\phi$ . Since  $U_{\theta}$  is Noetherian, J is generated by some finite-dimensional subspace  $V \subset J$  which can be chosen  $\mathfrak{g}_{ad}$ -invariant. Then by Frobenius reciprocity the  $\mathfrak{g}_{ad}$ -morphism  $\iota: V \to U_{\theta}$  can be lifted to a morphism of  $(U(\mathfrak{g}), U_{\theta})$ -bimodules  $\widehat{\phi}: V \otimes U_{\theta} = F_V(U_{\theta}) \to U_{\theta}$ , i.e., to a functorial morphism  $\phi: F_V(\theta) \to \mathrm{Id}_{\theta}$ . It is clear that then  $J = J(\phi, F)$ .

We are now ready to prove (i), i.e., that  $M(\phi,F) \subset M(\phi',F')$  implies  $J(\phi,F) \subset J(\phi',F')$ . Since  $F(M_{\lambda-\rho})$ ,  $F'(M_{\lambda-\rho})$  are projective, the inclusion  $M(\phi,F) \hookrightarrow M(\phi',F')$  lifts to a map  $\widetilde{\alpha}:F(M_{\lambda-\rho}) \to F'(M_{\lambda-\rho})$ , i.e.,  $\phi'_{M_{\lambda-\rho}} \circ \widetilde{\alpha} = \phi_{M_{\lambda-\rho}}$ . But by Theorem 22.4, morphisms of projective  $\theta$ -functors are the same as morphisms of the images of  $M_{\lambda-\rho}$  under these functors. Thus there is  $\alpha:F\to F'$  which maps to  $\widetilde{\alpha}$  and such that  $\phi' \circ \alpha = \phi$ . Hence

$$J(\phi, F) = \operatorname{Im}(\phi_{U_{\theta}}) \subset \operatorname{Im}(\phi'_{U_{\theta}}) = J(\phi', F'),$$

and (i) follows.

(ii) The proof of (i) implies that the image of  $\nu$  consists exactly of the submodules  $M(\phi, F)$ . Such a submodule is the image of  $F(M_{\lambda-\rho})$  under a morphism. But F is a projective  $\theta$ -functor, so by Corollary 22.6(iii), it is of the form  $\widetilde{F}(\theta)$ , where  $\widetilde{F}$  is a projective functor. Also by Theorem 23.6,  $\widetilde{F}$  is a direct sum of  $F_{\xi}$ , so  $F(M_{\lambda-\rho})$  is a direct sum of  $P_{\mu-\rho}$ , where  $(\mu, \lambda)$  is a proper representation of  $\xi$ . Thus  $\mu \leq \lambda$  and  $\mu \leq W_{\lambda}\mu$ . Conversely, if for such  $\mu$  we have a homomorphism

 $\gamma: P_{\mu-\rho} = F_{\xi}(M_{\lambda-\rho}) \to M_{\lambda-\rho}$  then  $\gamma = \phi_{M_{\lambda-\rho}}$  where  $\phi: F_{\xi}(\theta) \to \mathrm{Id}_{\theta}$ . So  $\mathrm{Im}(\gamma) = \nu(J(\phi, F_{\xi}(\theta)))$ . Since  $\nu$  preserves sums, (ii) follows.

(iii) Every submodule of  $M_{\lambda-\rho}$  is a quotient of a direct sum of  $P_{\mu-\rho}$  with  $\chi_{\mu} = \chi_{\lambda}, \mu \leq \lambda$ . Hence by Proposition 16.1  $\mu \leq \lambda$ , as  $\lambda$  is dominant. (This also follows from Theorem 20.13). So if  $W_{\lambda} = 1$  then by (ii)  $\nu$  is surjective, hence bijective by (i). Since  $I \cap J$  is the largest of all ideals contained both in I and in J and similarly for submodules,  $\nu$  also preserves intersections by (i). Thus  $\nu$  is an isomorphism of lattices.

Corollary 24.5. Let  $\theta = \chi_{\lambda}$  where  $\lambda$  is dominant. If  $M_{\lambda-\rho}$  is irreducible then  $U_{\theta}$  is a simple algebra. Conversely, if  $U_{\theta}$  is simple then  $M_{\mu-\rho}$  is irreducible for all  $\mu$  with  $\chi_{\mu} = \theta$ .

*Proof.* The direct implication follows from Theorem 24.4. For the reverse implication, suppose for some distinct  $\mu_1, \mu_2 \in W\lambda$ , we have  $M_{\mu_1-\rho} \hookrightarrow M_{\mu_2-\rho}$  and  $M_{\mu_1-\rho}$  is simple. Then in view of the Duflo-Joseph theorem we have an inclusion

$$J := \operatorname{Hom}_{\operatorname{fin}}(M_{\mu_2 - \rho}, M_{\mu_1 - \rho}) \hookrightarrow \operatorname{Hom}_{\operatorname{fin}}(M_{\mu_2 - \rho}, M_{\mu_2 - \rho}) = U_{\theta},$$

and J is a proper 2-sided ideal (as it does not contain 1) which is not zero (as  $M_{\mu_1-\rho}\cong M_{\mu_1-\rho}^{\vee}$  and hence for a finite-dimensional  $\mathfrak{g}$ -module V,  $\operatorname{Hom}(M_{\mu_2-\rho},V\otimes M_{\mu_1-\rho})\cong V[\mu_2-\mu_1]$ ).

Using the determinant formula for the Shapovalov form, this gives an explicit description of the locus of  $\theta \in \mathfrak{h}^*/W$  where  $U_{\theta}$  is simple.

#### 25. Applications of projective functors - II

25.1. Duflo's theorem on primitive ideals in  $U_{\theta}$ . Recall that a **prime ideal** in a commutative ring R is a proper ideal I such that if  $xy \in I$  then  $x \in I$  or  $y \in I$ . This definition is not good for noncommutative rings: for example, the zero ideal in the matrix algebra  $\operatorname{Mat}_n(\mathbb{C})$ ,  $n \geq 2$ , would not be prime, even though this algebra is simple; so  $\operatorname{Mat}_n(\mathbb{C})$  would have no prime ideals at all. However, the definition can be reformulated so that it works well for noncommutative rings.

**Definition 25.1.** A proper 2-sided ideal I in a (possibly non-commutative) ring R is **prime** if whenever the product XY of two 2-sided ideals  $X, Y \subset R$  is contained in I, either X or Y must be contained in I.

Note that for commutative rings this coincides with the usual definition. Indeed, if I is prime in the noncommutative sense and if  $xy \in I$  then  $(x)(y) \subset I$ , so  $(x) \subset I$  or  $(y) \subset I$ , i.e. x or y is in I. Conversely, if I is prime in the commutative sense and X, Y are not contained in I then there exist  $x \in X, y \in Y$  not in I, so  $xy \notin I$ , i.e., XY is not contained in I. But in the noncommutative case the two definitions differ, e.g. 0 is clearly a prime ideal (in the noncommutative sense) in any simple algebra, e.g. in the matrix algebra  $Mat_n(\mathbb{C})$ .

A ring R is called **prime** if 0 is a prime ideal in R. For example, if R is an integral domain then it is prime, and the converse holds if R is commutative. On the other hand, there are many noncommutative prime rings which are not domains, e.g. simple rings, such as the matrix algebras  $\operatorname{Mat}_n(\mathbb{C}), n \geq 2$ . Also it is clear that an ideal  $I \subset R$  is prime iff the ring R/I is prime (thus every maximal ideal is prime, so prime ideals always exist). If moreover R/I is a domain, one says that I is **completely prime**.

Another important notion is that of a **primitive ideal**.

**Definition 25.2.** An ideal  $I \subset R$  is **primitive** if it is the annihilator of a simple R-module M.

It is easy to see that every primitive ideal I is prime: if X, Y are 2-sided ideals in R and  $XY \subset I$  then XYM = 0, so if Y is not contained in I then  $YM \neq 0$ . Thus YM = M (as M is simple), hence XM = XYM = 0, so  $X \subset I$ . Also for a commutative ring a primitive ideal is the same thing as a maximal ideal. Indeed, if I is maximal then R/I is a field, so a simple R-module, and I is the annihilator of R/I. Conversely, if I is primitive and is the annihilator of a simple module M then M = R/J is a field and I = J, so I is maximal.

Exercise 25.3. Show that every maximal ideal in a unital ring is primitive, and give a counterexample to the converse.

We see that in general a prime ideal need not be primitive, e.g. the zero ideal in  $\mathbb{C}[x]$ . Nevertheless, for  $U_{\theta}$  we have the following remarkable theorem due to M. Duflo:

**Theorem 25.4.** Every prime ideal  $J \subset U_{\theta}$  is primitive and moreover is the annihilator of a simple highest weight module  $L_{\mu-\rho}$ , where  $\chi_{\mu} = \theta$ .

Proof. The module  $M:=M_{\lambda-\rho}/\nu(J)$  has finite length, so let us endow it with a filtration by submodules  $F_k=F_kM$  with simple successive quotients  $L_1,...,L_n$  ( $L_k=F_k/F_{k-1}$ ). Let  $I_k\subset U_\theta$  be the annihilators of  $L_k$ . Since JM=0, we have  $J\subset I_k$  for all k. Also  $I_kF_k\subset F_{k-1}$ , so  $I_1...I_nM=0$ , hence  $I_1...I_nM_{\lambda-\rho}\subset JM_{\lambda-\rho}$ . By Theorem 24.1(i), this implies that  $I_1...I_n\subset J$ . Since J is prime, this means that there exists m such that  $I_m\subset J$ . Then  $J=I_m$ , i.e. J is the annihilator of  $L_m$ . But  $L_m=L_{\mu-\rho}$  for some  $\mu$  such that  $\chi_\mu=\chi_\lambda=\theta$ .

Note that the choice of  $\mu$  is not unique, for example, for J=0 and generic  $\theta$ , any of the |W| possible choices of  $\mu$  is good. In fact, the proof of Duflo's theorem shows that for every dominant  $\lambda$  such that  $\theta = \chi_{\lambda}$ , we can choose  $\mu \in W\lambda$  such that  $\mu \leq \lambda$ .

25.2. Classification of simple Harish-Chandra bimodules. Denote by  $HC_{\theta}^n$  the category of Harish-Chandra bimodules over  $\mathfrak{g}$  annihilated on the right by the ideal  $(\operatorname{Ker}\theta)^n$ . These categories form a nested sequence; denote the corresponding nested union by  $HC_{\theta}$ . Recall that we have a direct sum decomposition  $HC = \bigoplus_{\theta \in \mathfrak{h}^*/W} HC_{\theta}$ . This implies that every simple Harish-Chandra bimodule belongs to  $HC_{\theta}^1$  for some infinitesimal character  $\theta$ .

Recall also that for a finite-dimensional  $\mathfrak{g}$ -module V, in  $HC^1_{\theta}$  we have the object  $V \otimes U_{\theta}$ . Moreover, this object is projective: for  $Y \in HC^1_{\theta}$  we have

$$\operatorname{Hom}(V \otimes U_{\theta}, Y) = \operatorname{Hom}_{\mathfrak{g}-\operatorname{bimod}}(V \otimes U(\mathfrak{g}), Y) = \operatorname{Hom}_{\mathfrak{g}_{\operatorname{ad}}}(V, Y),$$

which is an exact functor since Y is a locally finite (hence semisimple)  $\mathfrak{g}_{ad}$ -module. Finally, since Y is a finitely generated bimodule locally finite under  $\mathfrak{g}_{ad}$ , there exists a finite-dimensional  $\mathfrak{g}_{ad}$ -submodule  $V \subset Y$  that generates Y as a bimodule. Then the homomorphism

$$\hat{i}: V \otimes U(\mathfrak{g}) \to Y$$

corresponding to  $i: V \hookrightarrow Y$  is surjective and factors through the module  $V \otimes U_{\theta}$ . Thus Y is a quotient of  $V \otimes U_{\theta}$ . Thus we have

**Lemma 25.5.** The abelian category  $HC^1_{\theta}$  has enough projectives.

We also note that this category has finite-dimensional Hom spaces. Indeed, If  $Y_1, Y_2 \in HC^1_\theta$  then  $Y_1$  is a quotient of  $V \otimes U_\theta$  for some V, so  $\operatorname{Hom}(Y_1, Y_2) \subset \operatorname{Hom}(V \otimes U_\theta, Y_2) = \operatorname{Hom}_{\mathfrak{g}_{\operatorname{ad}}}(V, Y_2)$ , which is finite-dimensional. Finally, note that this category is Noetherian: any nested sequence of subobjects of an object stabilizes.

It thus follows from the Krull-Schmidt theorem that in  $HC_{\theta}^1$ , every object of  $HC_{\theta}^1$  is uniquely a finite direct sum of indecomposables, and from Proposition 16.2 the indecomposable projectives and the simples of  $HC_{\theta}^1$  labeled by the same index set. It remains to describe this labeling set.

**Theorem 25.6.** The simples (and indecomposable projectives) in  $HC^1_{\theta}$  are labeled by the set  $\Xi$ , via  $\xi \in \Xi \mapsto \mathbf{L}_{\xi}, \mathbf{P}_{\xi}$ . Namely, if  $\xi = (\mu, \lambda)$  is a proper representation then  $\mathbf{P}_{\xi}$  is the unique indecomposable projective in  $HC^1_{\theta}$  such that  $\mathbf{P}_{\xi} \otimes_{U(\mathfrak{g})} M_{\lambda-\rho} = P_{\mu-\rho}$ .

*Proof.* Every indecomposable projective is a direct summand of  $V \otimes U_{\theta}$ . But  $(V \otimes U_{\theta}) \otimes_{U(\mathfrak{g})} Y = F_V(\theta)(Y)$ . Thus from the classification of projective functors (Theorem 23.6) it follows that the indecomposable summands of  $V \otimes U_{\theta}$  are  $\mathbf{P}_{\xi}$  such that  $\mathbf{P}_{\xi} \otimes = F_{\xi}(\theta)$ .

Corollary 25.7. Objects in  $HC_{\theta}^1$ , hence in  $HC_{\theta}$  and HC, have finite length.

*Proof.* Recall that  $HC_{\theta}^1 = \bigoplus_{\chi} HC_{\chi,\theta}^1$ , the decomposition according to left generalized infinitesimal characters. By Theorem 25.6, each subcategory  $HC_{\chi,\theta}^1$  has finitely many simple objects. Thus the statement follows from Proposition 16.2.

25.3. Equivalence between category  $\mathcal{O}$  and category of Harish-Chandra bimodules. Let  $\theta = \chi_{\lambda}$  where  $\lambda$  is dominant. Let  $\mathcal{O}_{\lambda+P}$  be the full subcategory of  $\mathcal{O}$  consisting of modules with weights in  $\lambda+P$ . Define the functor

$$T_{\lambda}:HC^{1}_{\theta}\to\mathcal{O}_{\lambda+P}$$

given by  $T_{\lambda}(Y) = Y \otimes_{U(\mathfrak{g})} M_{\lambda-\rho}$ . Also let  $\mathcal{O}(\lambda)$  be the full subcategory of  $\mathcal{O}_{\lambda+P}$  of modules M which admit a presentation

$$Q_1 \to Q_0 \to M \to 0$$
,

where  $Q_0, Q_1$  are direct sums of  $P_{\mu-\rho}$  with  $\mu \in \lambda + P$  and  $\mu \leq W_{\lambda}\mu$ . Note that the functor  $T_{\lambda}$  is left adjoint to the functor  $H_{\lambda}$  defined in Subsection 19.3:  $H_{\lambda}(X) = \operatorname{Hom}_{\operatorname{fin}}(M_{\lambda-\rho}, X)$ . Indeed,

$$\operatorname{Hom}(T_{\lambda}(Y), X) = \operatorname{Hom}(Y \otimes_{U(\mathfrak{g})} M_{\lambda - \rho}, X) =$$

 $\operatorname{Hom}(Y, \operatorname{Hom}(M_{\lambda-\rho}, X)) = \operatorname{Hom}(Y, \operatorname{Hom}_{\operatorname{fin}}(M_{\lambda-\rho}, X)) = \operatorname{Hom}(Y, H_{\lambda}(X)).$ 

**Theorem 25.8.** (J. Bernstein-S, Gelfand) (i) If  $\lambda$  is a regular weight then the functor  $T_{\lambda}$  is an equivalence of categories, with quasi-inverse  $H_{\lambda}$ .

(ii) In general,  $T_{\lambda}$  is fully faithful and defines an equivalence

$$HC^1_\theta \cong \mathcal{O}(\lambda),$$

with quasi-inverse  $H_{\lambda}$ .

**Remark 25.9.** Note that if  $\lambda$  is not regular then the subcategory  $\mathcal{O}(\lambda) \subset \mathcal{O}$  need not be closed under taking subquotients (even though it is abelian by Theorem 25.8). Also the functor  $T_{\lambda}$  (and thus the inclusion  $\mathcal{O}(\lambda) \hookrightarrow \mathcal{O}$ ) need not be (left) exact. So if  $f: X \to Y$  is a morphism in  $\mathcal{O}(\lambda)$  then its kernels in  $\mathcal{O}(\lambda)$  and in  $\mathcal{O}$  may differ, and in particular the latter may not belong to  $\mathcal{O}(\lambda)$ . See Example 26.2.

*Proof.* (i) is a special case of (ii), so let us prove (ii). To this end, we'll use the following general fact.

**Proposition 25.10.** Let  $\mathcal{A}, \mathcal{B}$  be abelian categories such that  $\mathcal{A}$  has enough projectives and  $T: \mathcal{A} \to \mathcal{B}$  a right exact functor which maps projectives to projectives. Suppose that T is fully faithful on projectives, i.e., for any projectives  $P_0, P_1 \in \mathcal{A}$ , the natural map  $\operatorname{Hom}(P_1, P_0) \to \operatorname{Hom}(T(P_1), T(P_0))$  is an isomorphism. Then T is fully faithful, and defines an equivalence of  $\mathcal{A}$  onto the subcategory of objects  $Y \in \mathcal{B}$  which admit a presentation

$$T(P_1) \to T(P_0) \to Y \to 0$$

for some projectives  $P_0, P_1 \in \mathcal{A}$ .

*Proof.* We first show that T is faithful. Let  $X, X' \in \mathcal{A}$  and  $a: X \to X'$ . Pick presentations

$$P_1 \to P_0 \to X \to 0, \ P'_1 \to P'_0 \to X' \to 0.$$

We have maps  $p_0: P_0 \to X$ ,  $p_0': P_0' \to X'$ ,  $p_1: P_1 \to P_0$ ,  $p_1': P_1' \to P_0'$ . There exist morphisms  $a_0: P_0 \to P_0'$ ,  $a_1: P_1 \to P_1'$  such that  $(a_1, a_0, a)$  is a morphism of presentations.

Suppose T(a) = 0. Then  $T(p'_0)T(a_0) = 0$ . Thus  $Y := \operatorname{Im} T(a_0) \subset \operatorname{Ker} T(p'_0) = \operatorname{Im} T(p'_1)$ . Thus the map  $T(a_0) : T(P_0) \to Y$  lifts to  $b: T(P_0) \to T(P'_1)$  such that  $T(a_0) = T(p'_1)b$ . Since T is full on projectives, we have b = T(c) for some  $c: P_0 \to P'_1$ , so  $T(a_0) = T(p'_1)T(c) = T(p'_1c)$ . Since T is faithful on projectives, this implies that  $a_0 = p'_1c$ . Thus  $\operatorname{Im} a_0 \subset \operatorname{Im} p'_1 = \operatorname{Ker} p'_0$ . It follows that  $p'_0a_0 = 0$ , hence  $ap_0 = 0$ . But  $p_0$  is an epimorphism, hence a = 0, as claimed.

Now let us show that T is full. Let  $X, X' \in \mathcal{A}$  and  $b: T(X) \to T(X')$ . The functor T maps the above presentations of X, X' into presentations of T(X), T(X') (as it is right exact and maps projectives to projectives):

$$T(P_1) \to T(P_0) \to T(X) \to 0, \ T(P'_1) \to T(P'_0) \to T(X') \to 0,$$

and we can find  $b_0: T(P_0) \to T(P_0'), b_1: T(P_1) \to T(P_1')$  such that  $(b_1, b_0, b)$  is a morphism of presentations. Since T is fully faithful on projectives, there exist  $a_0, a_1$  such that  $T(a_0) = b_0, T(a_1) = b_1$  and  $a_0p_1 = p_1'a_0$ . Thus  $a_0$  maps  $\text{Im}p_1 = \text{Ker}p_0$  into  $\text{Im}p_1' = \text{Ker}p_0'$ . This implies that  $a_0$  descends to  $a: X \to X'$ , and  $T(a)T(p_0) = T(p_0')b_0$ . Hence  $(T(a) - b)T(p_0) = 0$ , so since  $T(p_0)$  is an epimorphism we get T(a) = b, as claimed.

If  $Y \in \text{Im}(T)$  then Y = T(X) where X has presentation

$$P_1 \to P_0 \to X \to 0.$$

Thus Y has presentation

$$T(P_1) \to T(P_0) \to Y \to 0.$$

Conversely, if Y has such a presentation as a cokernel of a morphism  $f: T(P_1) \to T(P_0)$  then f = T(g) where  $g: P_1 \to P_0$ , and  $Y = T(\operatorname{Coker}(g))$ , which proves the last claim of the proposition.

Now we are ready to prove Theorem 25.8. By Lemma 25.5,  $HC_{\theta}^{1}$  has enough projectives. Also the functor  $T_{\lambda}$  is right exact, as it is given by tensor product. Further, if P is projective then  $\text{Hom}(T_{\lambda}(P), Y) = \text{Hom}(P, H_{\lambda}(Y))$  is exact in Y since  $H_{\lambda}$  is exact by Proposition 19.7 and P is projective. Thus  $T_{\lambda}(P)$  is projective. Finally, the fact that  $T_{\lambda}$  is fully faithful on projectives was one of the main results about projective functors (Theorem 22.4). So Proposition 25.10 applies to  $\mathcal{A} = HC_{\theta}^{1}$ ,  $\mathcal{B} = \mathcal{O}_{\lambda+P}$ ,  $T = T_{\lambda}$ . Moreover, the image of  $T_{\lambda}$  is precisely the category  $\mathcal{O}(\lambda)$  by the classification of projective functors (Theorem 23.6).

For an equivalence of categories, a right adjoint is a quasi-inverse. Thus  $H_{\lambda}$  is quasi-inverse of  $T_{\lambda}$ , as claimed. The theorem is proved.  $\square$ 

Corollary 25.11. Every Harish-Chandra bimodule M with right infinitesimal character  $\theta$  is realizable as  $\mathbb{V}^{\text{fin}}$  where  $\mathbb{V}$  is a (not necessarily unitary) admissible representation of the complex simply connected group G corresponding to  $\mathfrak{g}$  on a Hilbert space.

*Proof.* Let us prove the statement if  $\theta = \chi_{\lambda}$  where  $\lambda$  is a regular dominant weight (the general proof is similar).

We have seen in Subsection 19.3 that  $H_{\lambda}(M_{\mu-\rho}^{\vee})$  is the principal series module  $\mathbf{M}(\lambda,\mu) = \mathrm{Hom}_{\mathrm{fin}}(M_{\lambda-\rho},M_{\mu-\rho}^{\vee})$ . Thus by Theorem 25.8

 $\mathbf{M}(\lambda,\mu)$  is injective in  $HC^1_{\theta}$  if  $\mu$  is dominant (since  $M_{\mu-\rho}$  is projective, hence  $M^{\vee}_{\mu-\rho}$  is injective). Moreover, since every indecomposable projective in  $\mathcal{O}_{\lambda+P}$  is a direct summand of  $V\otimes M_{\mu-\rho}$  for some dominant  $\mu$  and finite-dimensional  $\mathfrak{g}$ -module V, it follows that every indecomposable injective is a direct summand in  $V\otimes M^{\vee}_{\mu-\rho}$  for some V and dominant  $\mu$ . Hence by Theorem 25.8, every indecomposable injective in  $HC^1_{\theta}$  is a direct summand in  $V\otimes \mathbf{M}(\lambda,\mu)$  for some V and dominant  $\mu$ . Thus any  $Y\in HC^1_{\theta}$  is contained in a direct sum of objects  $V\otimes \mathbf{M}(\lambda,\mu)$  for finite-dimensional V and dominant  $\mu$ . Since principal series modules  $\mathbf{M}(\lambda,\mu)$  are realizable in a Hilbert space by Proposition 19.5, we are done by Corollary 6.13.

**Exercise 25.12.** (i) Generalize the proof of Corollary 25.11 to non-regular dominant weights  $\lambda$ .

(ii) Generalize Corollary 25.11 to any Harish-Chandra bimodule with generalized infinitesimal character  $\theta$ , and then to any Harish-Chandra bimodule.

**Hint.** Recall that  $C_{\lambda,\mu}^{\infty}(G/B)$  is the space of smooth functions F on G which satisfy the differential equations

$$(R_b - \lambda(b))F = (R_{\overline{b}} - \mu(\overline{b}))F = 0$$

for  $b \in \mathfrak{b}$  and  $\overline{b} \in \overline{\mathfrak{b}}$  (here  $R_b$  is the vector field corresponding to the right translation by b). Now for  $N \geq 1$  consider the space  $C_{\lambda,\mu,N}^{\infty}(G/B)$  of smooth functions F on G satisfying the differential equations

$$(R_b - \lambda(b))^N F = (R_{\overline{b}} - \mu(\overline{b}))^N F = 0.$$

(Note that  $C^{\infty}_{\lambda,\mu,1}(G/B) = C^{\infty}_{\lambda,\mu}(G/B)$ .) Show that  $C^{\infty}_{\lambda,\mu,N}(G/B)$  are admissible representations of G on Fréchet spaces. Then mimic the proof of Corollary 25.11 using these instead of  $C^{\infty}_{\lambda,\mu}(G/B)$ .

#### 26. Representations of $SL_2(\mathbb{C})$

26.1. Harish-Chandra bimodules for  $\mathfrak{sl}_2(\mathbb{C})$ . Let us now work out the simplest example,  $\mathfrak{g} = \mathfrak{sl}_2(\mathbb{C})$ . In this case  $\mathfrak{h}^* = \mathbb{C}$ ,  $P = \mathbb{Z}$ ,  $\chi_{\lambda} = \lambda^2$ . So by Theorem 25.6, irreducible Harish-Chandra bimodules  $\mathbf{L}_{\xi}$  are parametrized by pairs  $\xi = (\mu, \lambda)$  of complex numbers such that  $\lambda - \mu$  is an integer, modulo the map  $(\mu, \lambda) \mapsto (-\mu, -\lambda)$ , and we may (and will) assume that  $(\mu, \lambda)$  is a proper representation of  $\xi$ , i.e.,  $\lambda \notin \mathbb{Z}_{<0}$  and if  $\lambda = 0$  then  $\mu \in \mathbb{Z}_{\leq 0}$ . Let us describe these bimodules in terms of the principal series bimodules  $\mathbf{M}(\lambda, \mu)$ .

**Proposition 26.1.** (i) The principal series bimodule  $\mathbf{M}(\lambda, \mu)$  is irreducible and isomorphic to  $\mathbf{M}(-\lambda, -\mu)$  unless  $\lambda, \mu$  are nonzero integers of the same sign. Otherwise such bimodules are pairwise non-isomorphic.

(ii) If  $\lambda$ ,  $\mu$  are both nonzero integers of the same sign then  $\mathbf{M}(\lambda, \mu)$  is indecomposable and has a finite-dimensional constituent  $L^*_{|\lambda|-1} \otimes L_{|\mu|-1}$ , which is a submodule if  $\lambda > 0$  and quotient if  $\lambda < 0$ . The other composition factor is  $\mathbf{M}(\lambda, -\mu) \cong \mathbf{M}(-\lambda, \mu)$ , which is irreducible.

(iii) If  $\xi = (\mu, \lambda)$  is a proper representation with  $\lambda \notin \mathbb{Z}_{\geq 1}$  then  $\mathbf{L}_{\xi} = \mathbf{M}(\lambda, \mu)$ . If  $\xi = (\mu, \lambda)$  where  $\lambda \in \mathbb{Z}_{\geq 1}$  then  $\mathbf{L}_{\xi} = L_{\lambda-1}^* \otimes L_{\mu-1}$  if  $\mu \geq 1$  and  $\mathbf{L}_{\xi} = \mathbf{M}(\lambda, \mu)$  if  $\mu \leq 0$ .

*Proof.* (i),(ii) Consider first the case when  $\lambda$  and  $\mu$  are both non-integers. Then the weights  $\pm \lambda$  are dominant and  $M_{\pm \mu-1}^{\vee}$  are simple, so by Theorem 25.8  $\mathbf{M}(\lambda, \mu)$  is also simple and isomorphic to  $\mathbf{M}(-\lambda, -\mu)$ .

Now suppose  $\lambda, \mu$  are integers. Recall that  $\mathbf{M}(\lambda, \mu)$  decomposes over the diagonal copy of  $\mathfrak{g}$  as

(18) 
$$\mathbf{M}(\lambda,\mu) = \bigoplus_{j\geq 0} L_{|\lambda-\mu|+2j}.$$

If  $\lambda = 0$  and  $\mu \geq 0$ , then the equivalence  $T_{\lambda} = T_0$  maps  $\mathbf{M}(0, \pm \mu)$  to  $M_{\pm \mu - 1}^{\vee}$ . So if  $\mu = 0$ , we have a simple bimodule  $\mathbf{M}(0, 0)$ . On the other hand, if  $\mu > 0$ , we have two bimodules  $\mathbf{M}(0, -\mu)$ ,  $\mathbf{M}(0, \mu)$  and a natural map

$$a: \mathbf{M}(0,\mu) = \mathrm{Hom}_{\mathrm{fin}}(M_{-1},M_{\mu-1}^{\vee}) \to \mathbf{M}(0,-\mu) = \mathrm{Hom}_{\mathrm{fin}}(M_{-1},M_{-\mu-1}^{\vee})$$

induced by the surjection  $M_{\mu-1}^{\vee} \to M_{-\mu-1}^{\vee}$ . The kernel of this map is  $\operatorname{Ker} a = \operatorname{Hom}_{\operatorname{fin}}(M_{-1}, L_{\mu-1}) = 0$ , which implies that a is an isomorphism (as the K-type of the bimodules  $\mathbf{M}(0,\mu), \mathbf{M}(0,-\mu)$  is the same by (18)). So we have the simple bimodule  $\mathbf{M}(\mu,0) = \mathbf{M}(-\mu,0)$ . If  $\mu = 0, \lambda \neq 0$ , the situation is similar, as  $\lambda$  and  $\mu$  play a symmetric role.

It remains to consider the situation when  $\lambda, \mu \in \mathbb{Z} \setminus 0$ . So let n, m be positive integers. By Theorem 25.8, the bimodule  $\mathbf{M}(n, -m)$  is simple,

as it corresponds to the simple module  $M_{-m-1}^{\vee}$ . Similarly,  $\mathbf{M}(-n,m)$  is simple. Now, we have homomorphisms

$$a: \mathbf{M}(n,m) \to \mathbf{M}(n,-m), b: \mathbf{M}(n,-m) \to \mathbf{M}(-n,-m).$$

Since  $\mathbf{M}(n, -m)$  is simple and  $a \neq 0$ , it is surjective, so in view of (18) we have a short exact sequence

$$0 \to L_{n-1}^* \otimes L_{m-1} \to \mathbf{M}(n,m) \to \mathbf{M}(n,-m) \to 0.$$

Similarly, since  $b \neq 0$ , it is injective, so in view of (18) we have a short exact sequence

$$0 \to \mathbf{M}(n, -m) \to \mathbf{M}(-m, -n) \to L_{n-1}^* \otimes L_{m-1} \to 0.$$

Moreover, these sequences are not split by Theorem 25.8. This proves (i),(ii).

(iii) follows immediately from (i),(ii). The proposition is proved.  $\Box$ 

**Example 26.2.** One may also describe explicitly the projectives  $\mathbf{P}_{\xi}$ . As an example let us do so for  $\xi = (-1,0)$ . Consider the tensor product  $L_1 \otimes U_0$ , which is a projective object. We have  $(L_1 \otimes U_0) \otimes_{U_0} M_{-1} = L_1 \otimes M_{-1} = P_{-2}$ , the big projective object with composition series  $[M_{-2}, \mathbb{C}, M_{-2}]$ . Thus  $L_1 \otimes U_0 = \mathbf{P}_{\xi}$ . Over the diagonal copy of  $\mathfrak{g}$  we have

$$\mathbf{P}_{\varepsilon} = L_1 \otimes U_0 = L_1 \otimes (L_0 \oplus L_2 \oplus \ldots) = 2L_1 \oplus 2L_3 \oplus \ldots$$

Thus we have a short exact sequence

$$(19) 0 \to \mathbf{L}_{\xi} \to \mathbf{P}_{\xi} \to \mathbf{L}_{\xi} \to 0,$$

where  $\mathbf{L}_{\xi} = \mathbf{M}(0, -1) = \mathbf{M}(0, 1)$ , which is not split.

This shows that the functor  $T_{\lambda} = T_0$  is not exact in this case. Indeed,  $T_0(\mathbf{L}_{\xi}) = M_0^{\vee} \ (M_0^{\vee} \in \mathcal{O}(0) \ \text{with presentation} \ P_{-2} \to P_{-2} \to M_0^{\vee} \to 0$  and  $H_0(M_0^{\vee}) = \mathbf{M}(0,1)$ ), so the image of (19) under  $T_0$  is the sequence

$$0 \to M_0^{\vee} \to P_{-2} \to M_0^{\vee} \to 0$$

which is not exact in the leftmost nontrivial term (the cohomology is  $\mathbb{C}$ ). This sequence is, however, exact in the category  $\mathcal{O}(0)$ , which has just two indecomposable objects  $M_0^{\vee}$  and  $P_{-2}$  (so  $\mathcal{O}(0)$  is not closed under taking subquotients and the inclusion  $\mathcal{O}(0) \hookrightarrow \mathcal{O}$  is not exact).

26.2. Representations of  $SL_2(\mathbb{C})$ . Let us now consider representations of  $G = SL_2(\mathbb{C})$ . We have  $\mathfrak{g} = \mathfrak{sl}_2(\mathbb{C})$ , K = SU(2). We have already classified the irreducible Harish-Chandra (bi)modules and shown that the only ones are finite-dimensional modules and principal series modules. Moreover, we realized the principal series module

 $\mathbf{M}(\lambda,\mu)$  as the space of K-finite vectors in the space of smooth functions  $F:G\to\mathbb{C}$  such that

$$F(gb) = F(g)t(b)^{\lambda-\mu}|t(b)|^{2\mu-2}, \ b \in B,$$

where  $B \subset G$  is the subgroup of upper triangular matrices. Thus, similarly to the real case, setting  $\mu - \lambda = m \in \mathbb{Z}$ , we may represent  $\mathbf{M}(\lambda, \mu)$  as the space of polynomial tensor fields on  $\mathbb{CP}^1 = S^2$  of the form

$$\omega = \phi(u)(du)^{\frac{m}{2}}|du|^{1-\mu},$$

and we have an admissible realization of  $\mathbf{M}(\lambda,\mu)$  by the vector space  $C^{\infty}_{\lambda-1,\mu-1}(G/B)$  of smooth tensor fields of the same form. The (right) action of the group G on this space is given by

$$\left(\phi \circ \begin{pmatrix} a & b \\ c & d \end{pmatrix}\right)(u) = \phi \left(\frac{au+b}{cu+d}\right)(cu+d)^{-m}|cu+d|^{2\mu-2}.$$

We may also upgrade this realization to a Hilbert space realization by completing it with respect to the inner product

$$\|\omega\|^2 = \int_{S^2} |\phi(u)|^2 dA,$$

where dA is the rotation-invariant probability measure on  $S^2$ . However, this inner product is not G-invariant, in general; it is only G-invariant if  $\operatorname{Re}\mu = \frac{m}{2}$ , i.e.,  $\mu = \frac{m}{2} + s$ ,  $s \in i\mathbb{R}$ . This shows that the  $(\mathfrak{g}, K)$ -modules  $\mathbf{M}(-\frac{m}{2} + s, \frac{m}{2} + s)$  are unitary and irreducible for any imaginary s, with the Hilbert space completion being  $L^2_{-\frac{m}{2}+s-1,\frac{m}{2}+s-1}(G/B)$  – the unitary principal series.

Also the trivial representation is obviously unitary. Are there any other unitary irreducible representations? Clearly, they cannot be finite-dimensional. However, the answer is yes. To find them, let us first determine which  $\mathbf{M}(\lambda,\mu)$  are Hermitian. It is easy to show that this happens whenever  $\lambda^2 = \overline{\mu}^2$ , i.e.,  $\lambda = \pm \overline{\mu}$ . If  $\lambda = -\overline{\mu}$ , we get  $2\mathrm{Re}\mu = m$ , so  $\mu = \frac{m}{2} + s$ ,  $\lambda = -\frac{m}{2} + s$ ,  $s \in i\mathbb{R}$ , exactly as above. On the other hand, if  $\lambda = \overline{\mu}$  then we get  $\mu - \overline{\mu} = m$ , which implies that m = 0, i.e.,  $\lambda = \mu \in \mathbb{R}$ . In this case by Theorem 25.6 the module  $\mathbf{M}(\mu,\mu)$  is irreducible if and only if  $\mu \notin \mathbb{Z}$ . Thus we see that for  $0 < |\mu| < 1$ , this module is unitary, as we have a continuous family of simple Hermitian modules  $X(c) := \mathbf{M}(\sqrt{c}, \sqrt{c})$  for  $c \in (-\infty, 1)$ , and these modules are in the unitary principal series for  $c \leq 0$ . This family of unitary modules for c > 0 ( $0 < |\mu| < 1$ ) is called the **complementary series**; it is analogous to the complementary series in the real case.

It remains to consider the intervals  $m < |\mu| < m+1$  for  $m \in \mathbb{Z}_{\geq 0}$ . If  $\mathbf{M}(\mu, \mu)$  is unitary for at least one point in such interval, then it is

so for the whole interval, and taking the limit  $\mu \to m+1$ , we see that  $L_{m+1}^* \otimes L_{m+1}$ , which is a composition factor of  $\mathbf{M}(m+1, m+1)$ , would have to be unitary, which it is not. This shows that we have no unitary modules in these intervals. Thus we obtain the following result.

**Theorem 26.3.** (Gelfand-Naimark) The irreducible unitary representations of  $SL_2(\mathbb{C})$  are Hilbert space completions of the following unitary Harish-Chandra modules:

- Unitary principal series  $\mathbf{M}(-\frac{m}{2}+s,\frac{m}{2}+s), m \in \mathbb{Z}, s \in i\mathbb{R};$
- Complementary series  $\mathbf{M}(s,s)$ , -1 < s < 1;
- The trivial representation  $\mathbb{C}$ .

Here  $\mathbf{M}(-\frac{m}{2}+s,\frac{m}{2}+s) \cong \mathbf{M}(\frac{m}{2}-s,-\frac{m}{2}-s), \ \mathbf{M}(s,s) = \mathbf{M}(-s,-s)$  and there are no other isomorphisms.

**Exercise 26.4.** Compute the map  $M \mapsto M^{\vee}$  from Exercise 5.17 on the set of irreducible Harish-Chandra modules for  $SL_2(\mathbb{R})$  and  $SL_2(\mathbb{C})$ .

Exercise 26.5. The following exercise is the complex analog of Exercise 9.6.

(i) Show that for -1 < s < 0 the formula

$$(f,g)_s := \int_{\mathbb{C}^2} f(y)\overline{g(z)}|y-z|^{-2s-2}dyd\overline{y}dzd\overline{z}$$

defines a positive definite inner product on the space  $C_0(\mathbb{C})$  of continuous functions  $f: \mathbb{C} \to \mathbb{C}$  with compact support (*Hint*: pass to Fourier transforms).

(ii) Deduce that if f is a measurable function on  $\mathbb C$  then

$$0 \le (f, f)_s \le \infty,$$

so measurable functions f with  $(f, f)_s < \infty$  modulo those for which  $(f, f)_s = 0$  form a Hilbert space  $\mathcal{H}_s$  with inner product  $(,)_s$ , which is the completion of  $C_0(\mathbb{C})$  under  $(,)_s$ .

(iii) Let us view  $\mathcal{H}_s$  as the space of tensor fields  $f(y)|dy|^{1-s}$ , where f is as in (ii). Show that the complementary series unitary representation  $\widehat{\mathbf{M}}(s,s)$  of  $SL_2(\mathbb{C})$  may be realized in  $\mathcal{H}_s$  with G acting naturally on such tensor fields.

#### 27. Geometry of complex semisimple Lie groups

27.1. **The Borel-Weil theorem.** Let G be a simply connected semisimple complex Lie group with Lie algebra  $\mathfrak{g}$  and a Borel subgroup B generated by a maximal torus  $T \subset G$  and the 1-parameter subgroups  $\exp(te_i)$ ,  $i \in \Pi$ . Given an integral weight  $\lambda \in P$ , we can define the corresponding algebraic (in particular, holomorphic) line bundle  $\mathcal{L}_{\lambda}$  on the flag variety G/B. Namely, the total space  $T(\mathcal{L}_{\lambda})$  of  $\mathcal{L}_{\lambda}$  is  $(G \times \mathbb{C})/B$ , where B acts by

$$(g, z)b = (gb, \lambda(b)^{-1}z),$$

and the line bundle  $\mathcal{L}_{\lambda}$  is defined by the projection  $\pi: T(\mathcal{L}_{\lambda}) \to G/B$  to the first component. So this bundle is G-equivariant, i.e., G acts on  $T(\mathcal{L}_{\lambda})$  by left multiplication preserving the projection map  $\pi$ . We also see that smooth sections of  $\mathcal{L}_{\lambda}$  are smooth functions  $F: G \to \mathbb{C}$  such that

$$(g, F(g))b = (gb, F(gb)), b \in B,$$

which yields

$$F(gb) = \lambda(b)^{-1}F(g), \ b \in B.$$

It follows that the space of smooth sections  $\Gamma_{C^{\infty}}(G/B, \mathcal{L}_{\lambda})$  coincides with the admissible G-module  $C^{\infty}_{-\lambda,0}(G/B)$ , realizing the principal series module  $\mathbf{M}(-\lambda+1,1) = \mathrm{Hom}_{\mathrm{fin}}(M_{-\lambda},M_0^{\vee})$ .

**Remark 27.1.** Recall that  $H^2(G/B, \mathbb{Z}) = P$ . It is easy to check that the first Chern class  $c_1(\mathcal{L}_{\lambda})$  equals  $\lambda$ . This motivates the minus sign in the definition of  $\mathcal{L}_{\lambda}$ .

**Example 27.2.** Let  $G = SL_2(\mathbb{C})$ , so that B is the subgroup of upper triangular matrices with determinant 1 and  $G/B = \mathbb{CP}^1$ . Then sections of  $\mathcal{L}_m$  are functions  $F: G \to \mathbb{C}$  such that  $F(gb) = t(b)^{-m}F(g)$ , where  $t(b) = b_{11}$ . Thus  $\mathcal{L}_m \cong \mathcal{O}(-m)$ .

Let us now consider holomorphic sections of  $\mathcal{L}_{\lambda}$ . The space  $V_{\lambda}$  of such sections is a proper subrepresentation of  $C^{\infty}_{-\lambda,0}(G/B)$ , namely the subspace where the left copy of  $\mathfrak{g}$  (acting by antiholomorphic vector fields) acts trivially. Thus  $V^{\text{fin}}_{\lambda} = \text{Hom}_{\text{fin}}(M_{-\lambda}, \mathbb{C}) \subset \text{Hom}_{\text{fin}}(M_{-\lambda}, M_0^{\vee})$ , and  $V_{\lambda} = V^{\text{fin}}_{\lambda}$  since  $V^{\text{fin}}_{\lambda}$  is finite-dimensional. It follows that  $V^{\text{fin}}_{\lambda} = 0$  unless  $\lambda \in -P_+$ , and in the latter case  $V_{\lambda} = L^*_{-\lambda} = L^-_{\lambda} = L_{w_0\lambda}$ , the finite-dimensional representation of G with lowest weight  $\lambda$ . Thus we obtain

**Theorem 27.3.** (Borel-Weil) Let  $\lambda \in P$ . If  $\lambda \in P_+$  then we have an isomorphism of G-modules

$$\Gamma(G/B, \mathcal{L}_{-\lambda}) \cong L_{\lambda}^*.$$

If  $\lambda \notin P_+$  then  $\Gamma(G/B, \mathcal{L}_{-\lambda}) = 0$ .

**Example 27.4.** Let  $G = SL_2(\mathbb{C})$ . Then Theorem 27.3 says that

$$\Gamma(\mathbb{CP}^1, \mathcal{O}(m)) \cong L_m = \mathbb{C}^{m+1}$$

as representations of G.

More generally, suppose  $\lambda \in P$  and  $(\lambda, \alpha_i^{\vee}) = 0$ ,  $i \in S$  for a subset  $S \subset \Pi$  of the set of simple roots. Then we have a parabolic subgroup  $P_S \subset G$  generated by B and also  $\exp(tf_i)$  for  $i \in S$ , and  $\lambda$  extends to a 1-dimensional representation of  $P_S$ . Thus we can define the line bundle  $\mathcal{L}_{\lambda,S}$  on the partial flag variety  $G/P_S$  in the same way as  $\mathcal{L}_{\lambda}$ , and we have  $\mathcal{L}_{\lambda} = p_S^* \mathcal{L}_{\lambda,S}$ , where  $p_S : G/B \to G/P_S$  is the natural projection.

Note that any holomorphic section of  $\mathcal{L}_{\lambda}$  is just a function when restricted to a fiber  $F \cong P_S/B$  of the fibration  $p_S$  (a compact complex manifold), so by the maximum principle it must be constant. It follows that  $\Gamma(G/B, \mathcal{L}_{\lambda}) = \Gamma(G/P_S, \mathcal{L}_{\lambda,S})$ . Thus we get

Corollary 27.5. Let  $\lambda \in P$  with  $(\lambda, \alpha_i^{\vee}) = 0$ ,  $i \in S$ . Then

$$\Gamma(G/P_S, \mathcal{L}_{-\lambda,S}) \cong L_{\lambda}^*$$
.

if  $\lambda \in P_+$ , otherwise  $\Gamma(G/P_S, \mathcal{L}_{-\lambda,S}) = 0$ .

**Example 27.6.** Let  $G = SL_n(\mathbb{C}) = SL(V)$ ,  $V = \mathbb{C}^n$ , and  $P_S \subset G$  be the subgroup of matrices b such that  $b_{r1} = 0$  for r > 1 (this corresponds to  $S = \{2, ..., n-1\}$ ). Then  $G/P_S = \mathbb{CP}^{n-1} = \mathbb{P}V$ . The condition  $(\lambda, \alpha_i^{\vee}) = 0$ ,  $i \in S$  means that  $\lambda = m\omega_1$ , and in this case  $\mathcal{L}_{m,S} = \mathcal{O}(-m)$ . So Corollary 27.5 says that

$$\Gamma(\mathbb{P}V, \mathcal{O}(m)) = L_{m\omega_{n-1}} = S^m V^*$$

for  $m \geq 0$ , and zero for m < 0. This is also clear from elementary considerations, as by definition  $\Gamma(\mathbb{P}V, \mathcal{O}(m))$  is the space of homogeneous polynomials on V of degree m.

In fact, for  $\lambda \in P_+$  we can construct an isomorphism  $L_{\lambda}^* \cong \Gamma(G/B, \mathcal{L}_{-\lambda})$  explicitly as follows. Let  $v_{\lambda}$  be a highest weight vector of  $L_{\lambda}$ ,  $\ell \in L_{\lambda}^*$ , and  $F_{\ell}(g) := (\ell, gv_{\lambda})$ . Then

$$F_{\ell}(gb) = \lambda(b)F_{\ell}(g), \ b \in B.$$

Thus the assignment  $\ell \to F_{\ell}$  defines a linear map  $L_{\lambda}^* \to \Gamma(G/B, \mathcal{L}_{-\lambda})$  which is easily seen to be an isomorphism.

This shows that the bundle  $\mathcal{L}_{-\lambda}$  is **globally generated**, i.e., for every  $x \in G/B$  there exists  $s \in \Gamma(G/B, \mathcal{L}_{-\lambda})$  such that  $s(x) \neq 0$ . In other words, we have a regular map  $i_{\lambda} : G/B \to \mathbb{P}L_{\lambda}$  defined as follows.

For  $x \in G/B$ , choose a basis vector u of the fiber of  $\mathcal{L}_{-\lambda}$  at x and define  $i_{\lambda}(x) \in L_{\lambda}$  by the equality

$$s(x) = i_{\lambda}(x)(s)u$$

for  $s \in \Gamma(G/B, \mathcal{L}_{-\lambda}) \cong L_{\lambda}^*$ . Then  $i_{\lambda}(x)$  is well defined (does not depend on the choice of u) up to scaling and is nonzero, so gives rise to a well defined element of the projective space  $\mathbb{P}L_{\lambda}$ . Another definition of this map is

$$i_{\lambda}(x) = x(\mathbb{C}v_{\lambda}).$$

This shows that  $i_{\lambda}$  is an embedding when  $\lambda$  is regular, i.e., in this case the line bundle  $\mathcal{L}_{\lambda}$  is **very ample**. On the other hand, if  $\lambda$  is not necessarily regular and S is the set of j such that  $(\lambda, \alpha_{j}^{\vee}) = 0$  then  $i_{\lambda}: G/P_{S} \to \mathbb{P}L_{\lambda}$  is an embedding, so the bundle  $\mathcal{L}_{-\lambda,S}$  over the partial flag variety  $G/P_{S}$  is very ample.

**Example 27.7.** Let  $G = SL_n(\mathbb{C})$  and  $\lambda = \omega_k$ . Then  $S = [1, n-1] \setminus k$ , so  $P_S \subset G$  is the subgroup of matrices with  $g_{ij} = 0$ , i > k,  $j \le k$  and  $G/P_S$  is the Grassmannian Gr(k, n) of k-dimensional subspaces in  $\mathbb{C}^n$ . In this case  $L_{\lambda} = \wedge^k \mathbb{C}^n$ , so  $i_{\lambda}$  is the Plücker embedding  $Gr(k, n) \hookrightarrow \mathbb{P}(\wedge^k \mathbb{C}^n)$ .

27.2. The Springer resolution. Recall that a resolution of singularities of an irreducible algebraic variety X is a morphism  $p: Y \to X$  from a smooth variety Y that is proper (for example, projective<sup>20</sup>) and birational. Hironaka proved in 1960s that any variety over a field of characteristic zero has a resolution of singularities. However, it is not unique and this theorem does not provide a nice explicit construction of a resolution.

A basic example of a singular variety arising in Lie theory is the nilpotent cone  $\mathcal{N}$  of a semisimple Lie algebra  $\mathfrak{g}$ . This variety turns out to admit a very explicit equivariant resolution called the **Springer resolution**, which plays an important role in representation theory.

To define the Springer resolution, consider the cotangent bundle  $T^*\mathcal{F}$  of the flag variety  $\mathcal{F}$  of G. Recall that  $\mathcal{F}$  is the variety of Borel subalgebras  $\mathfrak{b} \subset \mathfrak{g}$ . For  $\mathfrak{b} \in \mathcal{F}$ , we have an isomorphism  $\mathfrak{g}/\mathfrak{b} \cong T_{\mathfrak{b}}\mathcal{F}$  defined by the action of G. Thus  $T^*\mathcal{F}$  can be viewed as the set of pairs  $(\mathfrak{b}, x)$ , where  $x \in (\mathfrak{g}/\mathfrak{b})^*$ . Note that  $(\mathfrak{g}/\mathfrak{b})^* \cong \mathfrak{b}^{\perp}$  under the Killing form, and  $\mathfrak{b}^{\perp} = [\mathfrak{b}, \mathfrak{b}]$  is the maximal nilpotent subalgebra of  $\mathfrak{b}$ . Thus  $T^*\mathcal{F}$  is the variety of pairs  $(\mathfrak{b}, x)$  where  $\mathfrak{b} \in \mathcal{F}$  is a Borel subalgebra of  $\mathfrak{g}$  and  $x \in \mathfrak{b}$  is a nilpotent element.

<sup>&</sup>lt;sup>20</sup>Recall that a morphism  $f: X \to Y$  is said to be **projective** if  $f = \pi \circ \widetilde{f}$  where  $\widetilde{f}: X \to Z \times Y$  is a closed embedding for some projective variety Z and  $\pi: Z \times Y \to Y$  is the projection to the second component.

Now we can define the **Springer map**  $p: T^*\mathcal{F} \to \mathcal{N}$  given by  $p(\mathfrak{b}, x) = x$ . Note that this map is G-equivariant, so its fibers over conjugate elements of  $\mathcal{N}$  are isomorphic.

**Theorem 27.8.** The Springer map p is birational and projective, so it is a resolution of singularities.

*Proof.* To show that p is birational, it suffices to prove that if  $e \in \mathcal{N}$  is regular, the Borel subalgebra  $\mathfrak{b}$  containing e is unique. To this end, note that  $\dim T^*\mathcal{F} = 2\dim \mathcal{F} = \dim \mathcal{N}$  and the map p is surjective (as any nilpotent element is contained in a Borel subalgebra). Thus p is generically finite, i.e.,  $p^{-1}(e)$  is a finite set, and our job is to show that it consists of one element.

We may fix a decomposition  $\mathfrak{g}=\mathfrak{n}_+\oplus\mathfrak{h}\oplus\mathfrak{n}_-$  and assume that  $e=\sum_{i=1}^r e_i$ . Then we have  $[\rho^\vee,e]=e$ , so the group  $\{t^{\rho^\vee},t\neq 0\}\cong\mathbb{C}^\times$  acts on  $p^{-1}(e)$  (as any Borel subalgebra containing e also contains te). Since  $p^{-1}(e)$  is finite, this action must be trivial. Thus  $\rho^\vee$  normalizes every  $\mathfrak{b}\in p^{-1}(e)$ , hence is contained in every such  $\mathfrak{b}$ . But  $\rho^\vee$  is regular, so is contained in a unique Cartan subalgebra, namely  $\mathfrak{h}$ . Since every semisimple element in a Borel subalgebra  $\mathfrak{b}\subset\mathfrak{g}$  is contained in a Cartan subalgebra sitting inside  $\mathfrak{b}$ , it follows that  $\mathfrak{h}\subset\mathfrak{b}$  for all  $\mathfrak{b}\in p^{-1}(e)$ . Thus  $[\omega_i^\vee,e]=e_i\in\mathfrak{b}$  for all i. It follows that  $\mathfrak{b}=\mathfrak{b}_+:=\mathfrak{h}\oplus\mathfrak{n}_+$ , i.e.,  $|p^{-1}(e)|=1$ , as claimed.

Now let us show that p is projective. Let  $\widetilde{p}: T^*\mathcal{F} \to \mathcal{F} \times \mathcal{N}$  be the map defined by  $\widetilde{p}(\mathfrak{b},x) = (\mathfrak{b},x)$ . This is clearly a closed embedding (the image is defined by the equation  $x \in \mathfrak{b}$ ). But  $p = \pi \circ \widetilde{p}$  where  $\pi: \mathcal{F} \times \mathcal{N} \to \mathcal{N}$  is the projection to the second component. Thus p is projective, as claimed.

**Remark 27.9.** The preimage  $p^{-1}(e)$  for  $e \in \mathcal{N}$  is called the **Springer fiber**. If e is not regular,  $p^{-1}(e)$  has positive dimension. It is a projective variety, which is in general singular, reducible and has complicated structure, but it plays an important role in representation theory.

**Example 27.10.** Let  $\mathfrak{g} = \mathfrak{sl}_2$ . Then  $\mathcal{N}$  is the usual quadratic cone  $yz + x^2 = 0$  in  $\mathbb{C}^3$ , and  $T^*\mathcal{F} = T^*\mathbb{C}P^1$  is the blow-up of the vertex in this cone.

27.3. The symplectic structure on coadjoint orbits. Recall that a smooth real manifold, complex manifold or algebraic variety X is symplectic if it is equipped with a nondegenerate closed 2-form  $\omega$ . It is clear that in this case X has even dimension.

**Theorem 27.11.** (Kirillov-Kostant) Let G be a connected real or complex Lie group or complex algebraic group. Then every G-orbit in  $\mathfrak{g}^*$  has a natural symplectic structure.

Proof. Let O be a G-orbit in  $\mathfrak{g}^*$  and  $f \in O$ . Then  $T_fO = \mathfrak{g}/\mathfrak{g}_f$  where  $\mathfrak{g}_f$  is the set of  $x \in \mathfrak{g}$  such that f([x,y]) = 0 for all  $y \in \mathfrak{g}$ . Define a skew-symmetric bilinear form  $\omega_f : \mathfrak{g} \times \mathfrak{g} \to \mathbb{C}$  given by  $\omega_f(y,z) = f([y,z])$ . It is clear that  $\text{Ker}\omega_f = \mathfrak{g}_f$ , so  $\omega_f$  defines a nondegenerate form on  $\mathfrak{g}/\mathfrak{g}_f = T_fO$ . This defines a nondegenerate G-invariant differential 2-form  $\omega$  on O.

It remains to show that  $\omega$  is closed. Let  $L_x$  be the vector field on O defined by the action of  $x \in \mathfrak{g}$ ; thus  $L_{[x,y]} = [L_x, L_y]$ . It suffices to show that for any  $x, y, z \in \mathfrak{g}$  we have  $d\omega(L_x, L_y, L_z) = 0$ . By Cartan's differentiation formula we have

$$d\omega(L_x, L_y, L_z) = \text{Alt}(L_x\omega(L_y, L_z) - \omega([L_x, L_y], L_z)),$$

where Alt denotes the sum over cyclic permutations of x,y,z. Since  $\omega$  is G-invariant, this yields

$$d\omega(L_x, L_y, L_z)(f) = \text{Alt}(\omega(L_y, L_{[x,z]}))(f) = f(\text{Alt}([y, [x,z]])),$$
  
which vanishes by the Jacobi identity.

Corollary 27.12. The singular locus of the nilpotent cone N has codimension  $\geq 2$ .

*Proof.* This follows since  $\mathcal{N}$  has finitely many orbits (Exercise 17.8) and by Theorem 27.11 they all have even dimension.

Corollary 27.13.  $\mathcal{N}$  is normal (i.e., the algebra  $\mathcal{O}(\mathcal{N})$  is integrally closed in its quotient field).

*Proof.* This follows from Corollary 27.12 since  $\mathcal{N}$  is a complete intersection and any complete intersection whose singular locus has codimension  $\geq 2$  is necessarily normal ([H], Chapter II, Prop. 8.23).

27.4. The algebra of functions on  $T^*\mathcal{F}$ . We will first recall some facts about normal algebraic varieties.

**Proposition 27.14.** Let Y be an irreducible normal algebraic variety. Then

- (i) ([Eis], Proposition 11.5) The singular locus of Y has codimension > 2.
- (ii) ([Eis], Proposition 11.4) If  $U \subset Y$  is an open subset and  $Y \setminus U$  has codimension  $\geq 2$  then any regular function f on U extends to a regular function on Y. In particular, any regular function on the smooth locus of Y extends to a regular function on Y.
- (iii) Zariski main theorem ([H], Corollary III.11.4). If X is irreducible and  $p: X \to Y$  is a proper birational morphism then fibers of p are connected.

**Proposition 27.15.** Let Y be an irreducible normal affine algebraic variety and  $p: X \to Y$  be a resolution of singularities. Then the homomorphism  $p^*: \mathcal{O}(Y) \to \mathcal{O}(X)$  is an isomorphism.

*Proof.* It is clear that  $p^*$  is injective, so we only need to show it is surjective. Let  $f \in \mathcal{O}(X)$ . Since every fiber of p is proper, and also connected due to normality of Y by Proposition 27.14(iii), f is constant along this fiber. So  $f = h \circ p$  for  $h: Y \to \mathbb{C}$  a rational function. It remains to show that h is regular. We know that h is regular on the smooth locus of Y (as it is defined at all points of Y). Thus the result follows from the normality of Y and Proposition 27.14(i),(ii).

**Theorem 27.16.** Let  $p: T^*\mathcal{F} \to \mathcal{N}$  be the Springer resolution. Then the map  $p^*: \mathcal{O}(\mathcal{N}) \to \mathcal{O}(T^*\mathcal{F})$  is an isomorphism of graded algebras.

*Proof.* This follows from Proposition 27.15 and the normality of  $\mathcal{N}$  (Corollary 27.13).

#### 28. D-modules - I

We would now like to formulate the Beilinson-Bernstein localization theorems. We first review generalities about differential operators and D-modules.

28.1. **Differential operators.** Let K be an algebraically closed field of characteristic zero. Let X be a smooth affine algebraic variety over K. Let  $\mathcal{O}(X)$  be the algebra of regular functions on X. Following Grothendieck, we define inductively the notion of a differential operator of order (at most) N on X. Namely, a differential operator of order -1 is zero, and a K-linear operator  $K : \mathcal{O}(X) \to \mathcal{O}(X)$  is a differential operator of order  $K \ge 0$  if for all  $K \in \mathcal{O}(X)$ , the operator  $K \in \mathcal{O}(X)$  is a differential operator of order  $K \in \mathcal{O}(X)$ .

Let  $D_N(X)$  denote the space of differential operators of order N. We have

$$0 = D_{-1}(X) \subset \mathcal{O}(X) = D_0(X) \subset D_1(X) \subset ... \subset D_N(X) \subset ...$$

and  $D_i(X)D_j(X) \subset D_{i+j}(X)$ , which implies that the nested union  $D(X) := \bigcup_{i>0} D_i(X)$  is a filtered algebra.

Definition 28.1. D(X) is called the algebra of differential operators on X.

Exercise 28.2. Prove the following statements.

- 1.  $[D_i(X), D_j(X)] \subset D_{i+j-1}(X)$  for  $i, j \geq 0$ . In particular, [,] makes  $D_1(X)$  a Lie algebra naturally isomorphic to  $\text{Vect}(X) \ltimes \mathcal{O}(X)$ , where Vect(X) is the Lie algebra of vector fields on X.
- 2. Suppose  $x_1, ..., x_n \in \mathcal{O}(X)$  are regular functions such that  $dx_1, ..., dx_n$  form a basis in each cotangent space to X. Let  $\partial_1, ..., \partial_n$  be the corresponding vector fields. For  $\mathbf{m} = (m_1, ..., m_n) \in \mathbb{Z}_{\geq 0}^n$ , let  $|\mathbf{m}| := \sum_{i=1}^n m_i$  and  $\partial^{\mathbf{m}} := \partial_1^{m_1} ... \partial_n^{m_n}$ . Then  $D_N(X)$  is a free finite rank  $\mathcal{O}(X)$ -module (under left multiplication) with basis  $\{\partial^{\mathbf{m}}\}$  with  $|\mathbf{m}| \leq N$ , and D(X) is a free  $\mathcal{O}(X)$ -module with basis  $\{\partial^{\mathbf{m}}\}$  for all  $\mathbf{m}$ .
- 3. One has gr  $D(X) = \bigoplus_{i \geq 0} \Gamma(X, S^i TX) = \mathcal{O}(T^*X)$ . In particular, D(X) is left and right Noetherian.
- 4. D(X) is generated by  $\mathcal{O}(X)$  and elements  $L_v$ ,  $v \in \text{Vect}(X)$  (depending linearly on v), with defining relations

(20) 
$$[f,g] = 0, [L_v,f] = v(f), L_{fv} = fL_v, [L_v,L_w] = L_{[v,w]},$$

where  $f, g \in \mathcal{O}(X), v, w \in \text{Vect}(X)$ .

5. If  $U \subset X$  is an affine open set then the multiplication map  $\mathcal{O}(U) \otimes_{\mathcal{O}(X)} D(X) \to D(U)$  is a filtered isomorphism.

#### 28.2. *D*-modules.

**Definition 28.3.** A **left** (respectively, **right**) D-module on X is a left (respectively, right) D(X)-module.

**Example 28.4.** 1.  $\mathcal{O}(X)$  is an obvious example of a left D-module on X. Also,  $\Omega(X)$  (the space of top differential forms on X) is naturally a right D-module on X, via  $\rho(L) = L^*$  (the adjoint differential operator to L with respect to the "integration pairing" between functions and top forms). More precisely,  $f^* = f$  for  $f \in \mathcal{O}(X)$ , and  $L_v^*$  is the action of the vector field -v on top forms (by Lie derivative). Finally, D(X) is both a left and a right D-module on X.

2. Suppose  $\mathbf{k} = \mathbb{C}$ , and f is a holomorphic function defined on some open set in X (in the usual topology). Then M(f) := D(X)f is a left D-module. We have a natural surjection  $D(X) \to M(f)$  whose kernel is the left ideal generated by the linear differential equations satisfied by f. E.g.  $M(1) = \mathcal{O}(X) = D(X)/D(X)\mathrm{Vect}(X)$ ,  $M(x^s) = D(\mathbb{C})/D(\mathbb{C})(x\partial - s)$  if  $s \notin \mathbb{Z}_{\geq 0}$ ,  $M(e^x) = D(\mathbb{C})/D(\mathbb{C})(\partial - 1)$ . Similarly, if  $\xi$  is a distribution (e.g., a measure) then  $\xi \cdot D(X)$  is a right D-module. For instance,  $\delta \cdot D(\mathbb{C}) = D(\mathbb{C})/xD(\mathbb{C})$ , where  $\delta$  is the delta-measure on the line.

**Exercise 28.5.** Show that  $\mathcal{O}(X)$  is a simple D(X)-module. Deduce that for any nonzero regular function f on X,  $M(f) = \mathcal{O}(X)$ .

28.3. D-modules on non-affine varieties. Now assume that X is a smooth variety which is not necessarily affine. Recall that a **quasico-herent sheaf** on X is a sheaf M of  $\mathcal{O}_X$ -modules (in Zariski topology) such that for any affine open sets  $U \subset V \subset X$  the restriction map induces an isomorphism of  $\mathcal{O}(U)$ -modules  $\mathcal{O}(U) \otimes_{\mathcal{O}(V)} M(V) \cong M(U)$ . Exercise 28.2(5) implies that there exists a canonical quasicoherent sheaf of algebras  $D_X$  on X such that  $\Gamma(U, D_X) = D(U)$  for any affine open set  $U \subset X$ . This sheaf is called the **sheaf of differential operators on** X.

**Definition 28.6.** A **left** (respectively, **right**) D-**module** on X is a quasicoherent sheaf of left (respectively, right)  $D_X$ -modules. The categories of left (respectively, right) D-modules on X (with obviously defined morphisms) are denoted by  $\mathcal{M}_l(X)$  and  $\mathcal{M}_r(X)$ .

It is clear that these are abelian categories. We will mostly use the category  $\mathcal{M}_l(X)$  and denote it shortly by  $\mathcal{M}(X)$ .

Note that if X is affine, this definition is equivalent to the previous one (by taking global sections).

As before, the basic examples are  $\mathcal{O}_X$  (a left *D*-module),  $\Omega_X$  (a right *D*-module),  $D_X$  (both a left and a right *D*-module).

We see that the notion of a D-module on X is local. For this reason, many questions about D-modules are local and reduce to the case of affine varieties.

28.4. Connections. The definition of a  $D_X$ -module can be reformulated in terms of connections on an  $\mathcal{O}_X$ -module. Namely, in differential geometry we have a theory of connections on vector bundles. An algebraic vector bundle on X is the same thing as a coherent, locally free  $\mathcal{O}_X$ -module. It turns out that the usual definition of a connection, when written algebraically, makes sense for any  $\mathcal{O}_X$ -module (i.e., quasicoherent sheaf), not necessarily coherent or locally free.

Namely, let X be a smooth variety and  $\Omega_X^i$  be the  $\mathcal{O}_X$ -module of differential *i*-forms on X.

**Definition 28.7.** A **connection** on an  $\mathcal{O}_X$ -module M is a **k**-linear morphism of sheaves  $\nabla: M \to M \otimes_{\mathcal{O}_X} \Omega^1_X$  such that

$$\nabla(fm) = f\nabla(m) + m \otimes df$$

for local sections f of  $\mathcal{O}_X$  and m of M.

Thus for each  $v \in \text{Vect}(X)$  we have the operator of covariant derivative  $\nabla_v : M \to M$  given on local sections by  $\nabla_v(m) := \nabla(m)(v)$ .

**Exercise 28.8.** Let X be an affine variety. Show that the operator  $m \mapsto ([\nabla_v, \nabla_w] - \nabla_{[v,w]})m$  is  $\mathcal{O}(X)$ -linear in v, w, m.

Given a connection  $\nabla$  on M, define the  $\mathcal{O}_X$ -linear map

$$\nabla^2: M \to M \otimes_{\mathcal{O}_X} \Omega_X^2$$

given on local sections by

$$\nabla^2(m)(v,w) := ([\nabla_v, \nabla_w] - \nabla_{[v,w]})m.$$

This map is called the **curvature** of  $\nabla$ . We say that  $\nabla$  is **flat** if its curvature vanishes:  $\nabla^2 = 0$ .

**Proposition 28.9.** A left  $D_X$ -module is the same thing as an  $\mathcal{O}_X$ -module with a flat connection.

Proof. Given an  $\mathcal{O}_X$ -module M with a flat connection  $\nabla$ , we extend the  $\mathcal{O}_X$ -action to a  $D_X$ -action by  $\rho(L_v) = \nabla_v$ . The first three relations of (20) then hold for any connection, while the last relation holds due to flatness of  $\nabla$ . Conversely, the same formula can be used to define a flat connection  $\nabla$  on any  $D_X$ -module M.

**Exercise 28.10.** Show that if a left D-module M on X is  $\mathcal{O}$ -coherent (i.e. a coherent sheaf on X) then it is locally free, i.e., is a vector bundle with a flat connection, and vice versa.

28.5. **Direct and inverse images.** Let  $\pi: X \to Y$  be a morphism of smooth affine varieties. This morphism gives rise to a homomorphism  $\pi^*: \mathcal{O}(Y) \to \mathcal{O}(X)$ , making  $\mathcal{O}(X)$  an  $\mathcal{O}(Y)$ -module, and a morphism of vector bundles  $\pi_*: TX \to \pi^*TY$ . This induces a map on global sections  $\pi_*: \operatorname{Vect}(X) \to \mathcal{O}(X) \otimes_{\mathcal{O}(Y)} \operatorname{Vect}(Y)$ .

Define

$$D_{X\to Y} = \mathcal{O}(X) \otimes_{\mathcal{O}(Y)} D(Y).$$

This is clearly a right D(Y)-module. Let us show that it also has a commuting left D(X)-action. The left action of  $\mathcal{O}(X)$  is obvious, so it remains to construct a flat connection. Given a vector field v on X, let

(21) 
$$\nabla_v(f \otimes L) = v(f) \otimes L + f\pi_*(v)L, \ f \in \mathcal{O}(X), \ L \in D(Y),$$

where we view  $\pi_*(v)$  as an element of  $D_{X\to Y}$ . This is well defined since for  $a \in \mathcal{O}(Y)$  one has  $[\pi_*(v), a] = v(a) \otimes 1$ .

**Exercise 28.11.** Show that this defines a flat connection on  $D_{X\to Y}$ .

Now we define the **inverse image functor**  $\pi^* : \mathcal{M}_l(Y) \to \mathcal{M}_l(X)$  by

$$\pi^!(N) = D_{X \to Y} \otimes_{D(Y)} N$$

and the direct image functor  $\pi_*: \mathcal{M}_r(X) \to \mathcal{M}_r(Y)$  by

$$\pi_*(M) = M \otimes_{D(X)} D_{X \to Y}.$$

Note that at the level of quasicoherent sheaves,  $\pi^*$  is the usual inverse image.

These functors are right exact are compatible with compositions. Also by definition,  $D_{X\to Y} = \pi^!(D(Y))$ .

Note that  $\pi^!(N) = \mathcal{O}(X) \otimes_{\mathcal{O}(Y)} N$  as an  $\mathcal{O}(X)$ -module (i.e., the usual pullback of  $\mathcal{O}$ -modules), with the connection defined by the formula similar to (21):

$$\nabla_v(f \otimes m) = v(f) \otimes m + f \nabla_{\pi_*(v)}(m), \ f \in \mathcal{O}(X), \ m \in M.$$

This means that the definition of  $\pi^!$  is local both on X and on Y. On the contrary, the definition of  $\pi_*$  is local only on Y but not on X. For example, if Y is a point and dim X = d then  $\pi_*\Omega_X = H^d(X, \mathbf{k})$ , the algebraic de Rham cohomology of X of degree d.

Thus we can use the same definition locally to define  $\pi^!$  for any morphism of smooth varieties, and  $\pi_*$  for an affine morphism (i.e. such that  $\pi^{-1}(U)$  is affine for any affine open set  $U \subset Y$ ), for example, a closed embedding. On the other hand, due to the non-local nature of direct image with respect to X the correct functor  $\pi_*$  for a non-affine morphism is not the derived functor of anything and can be defined only in the derived category.

#### 29. The Beilinson-Bernstein Localization Theorem

29.1. The Beilinson-Bernstein localization theorem for the zero infinitesimal character. Let  $\mathfrak{g}$  be a complex semisimple Lie algebra and  $U_0$  be the maximal quotient of  $U(\mathfrak{g})$  corresponding to the infinitesimal character  $\chi_{\rho} = \chi_{-\rho}$  of the trivial representation of  $\mathfrak{g}$ . Recall that  $\operatorname{gr}(U_0) = \mathcal{O}(\mathcal{N})$ . Let G be the corresponding simply connected complex group and  $\mathcal{F}$  the flag variety of G; thus  $\mathcal{F} \cong G/B$  for a Borel subgroup  $B \subset G$ . Let  $D(\mathcal{F})$  be the algebra of global differential operators on  $\mathcal{F}$ ; it is clear that  $\operatorname{gr}D(\mathcal{F}) \subset \mathcal{O}(T^*\mathcal{F})$ . Also, we have a natural filtration-preserving action map  $a: U(\mathfrak{g}) \to D(\mathcal{F})$ , induced by the Lie algebra homomorphism  $\mathfrak{g} \to \operatorname{Vect}(\mathcal{F})$ .

**Theorem 29.1.** (Beilinson-Bernstein, [BB]) (i) The homomorphism  $a: U(\mathfrak{g}) \to D(\mathcal{F})$  factors through a homomorphism  $a_0: U_0 \to D(\mathcal{F})$ . (ii) One has  $gr(a_0) = p^*$  where p is the Springer map  $T^*\mathcal{F} \to \mathcal{N}$ . (iii)  $grD(\mathcal{F}) = \mathcal{O}(T^*\mathcal{F})$  and  $a_0$  is an isomorphism.

- Proof. (i) Let  $z \in Z(\mathfrak{g})$  be an element acting by zero in the trivial representation of  $\mathfrak{g}$ . Our job is to show that for any rational function  $f \in \mathbb{C}(\mathcal{F})$  we have a(z)f = 0. Writing  $\mathcal{F}$  as G/B, we may view f as a rational function on G such that f(gb) = f(g),  $b \in B$ . The function a(z)f on G is the result of action on f of the right-invariant differential operator  $L_z$  corresponding to z:  $a(z)f = L_z f$ . Since z is central, this operator is also left-invariant:  $L_z = R_z$ . Since z acts by zero on the trivial representation, using the Harish-Chandra isomorphism, we may write z as  $\sum_i c_i b_i$ , where  $b_i \in \mathfrak{b} := \text{Lie}(B)$  and  $c_i \in U(\mathfrak{g})$ . Thus  $R_z = \sum_i R_{c_i} R_{b_i}$ . But  $R_{b_i} f = 0$  since f is invariant under right translations by B. Thus  $R_z f = 0$  and we are done.
- (ii) It suffices to check the statement in degrees 0 and 1, where it is straightforward.
- (iii) The statement follows from (i), (ii) and the fact that  $p^*$  is an isomorphism (Theorem 27.16).

The isomorphism  $a_0$  gives rise to two functors: the functor of global sections  $\Gamma: \mathcal{M}(\mathcal{F}) \to D(\mathcal{F}) - \text{mod} \cong U_0 - \text{mod}$  and the functor of localization Loc:  $U_0 - \text{mod} \cong D(\mathcal{F}) - \text{mod} \to \mathcal{M}(\mathcal{F})$  given by  $\text{Loc}(M)(U) := D(U) \otimes_{D(\mathcal{F})} M$  for an affine open set  $U \subset \mathcal{F}$ . Note that by definition the functor Loc is left adjoint to  $\Gamma$ .

The following theorem is a starting point for the geometric representation theory of semisimple Lie algebras (in particular, for the original proof of the Kazhdan-Lusztig conjecture).

**Theorem 29.2.** (Beilinson-Bernstein localization theorem, [BB]) The functors  $\Gamma$  and Loc are mutually inverse equivalences. Thus the category  $U_0 - \text{mod}$  is canonically equivalent to the category of D-modules on the flag variety  $\mathcal{F}$ .

We will not give a proof of this theorem here.

Theorem 29.2 motivates the following definition.

**Definition 29.3.** A smooth algebraic variety X is said to be **D-affine** if the global sections functor  $\Gamma: \mathcal{M}(X) \to D(X)$  – mod is an equivalence (hence Loc is its inverse).

It is clear that any affine variety is D-affine. Also we have

**Corollary 29.4.** Partial flag varieties of semisimple algebraic groups are *D*-affine.

29.2. Twisted differential operators and D-modules. We would now like to generalize the localization theorem to nonzero infinitesimal characters. To do so, we have to replace usual differential operators and D-modules by twisted ones.

Let T be an algebraic torus with character lattice  $P := \operatorname{Hom}(T, \mathbb{C}^{\times})$  and  $\widetilde{X}$  be a principal T-bundle over a smooth algebraic variety X (with T acting on the right). In this case, given  $\lambda \in P$ , we can define the line bundle  $\mathcal{L}_{\lambda}$  on X whose total space is  $\widetilde{X} \times_{T} \mathbb{C}_{\lambda}$ , where  $\mathbb{C}_{\lambda}$  is the 1-dimensional representation of T corresponding to  $\lambda$ , and we can consider the sheaf  $D_{\lambda,X}$  of differential operators acting on local sections of  $\mathcal{L}_{\lambda}$  (rather than functions).

Moreover, unlike the bundle  $\mathcal{L}_{\lambda}$ , the sheaf  $D_{\lambda,X}$  makes sense not just for  $\lambda \in P$  but more generally for  $\lambda \in P \otimes_{\mathbb{Z}} \mathbb{C}$ . Namely, assuming for now that  $\lambda \in P$ , we may think of rational sections of  $\mathcal{L}_{\lambda}$  as rational functions F on  $\widetilde{X}$  such that  $F(yt) = \lambda(t)^{-1}F(y)$  for  $y \in \widetilde{X}$ . A differential operator D on  $\widetilde{X}$  may be applied to such a function, and if  $\xi \in \mathfrak{t} := \operatorname{Lie}(T)$  then the first order differential operator  $R_{\xi} - \lambda(\xi)$  acts by zero:  $(R_{\xi} - \lambda(\xi))F = 0$ . Thus given an affine open set  $U \subset X$  with preimage  $\widetilde{U} \subset \widetilde{X}$ , the space

$$D_{\lambda}(U) := (D(\widetilde{U})/D(\widetilde{U})(R_{\xi} - \lambda(\xi), \xi \in \mathfrak{t}))^{T}$$

is naturally an associative algebra which acts on rational sections of  $\mathcal{L}_{\lambda}$  (check it!). Moreover, it is easy to check that  $D_{\lambda}(U) = D_{\lambda,X}(U)$ . Now it remains to note that the definition of  $D_{\lambda}(U)$  does not use the integrality of  $\lambda$ , thus makes sense for all  $\lambda \in P \otimes_{\mathbb{Z}} \mathbb{C}$ .

Thus for any  $\lambda \in P \otimes_{\mathbb{Z}} \mathbb{C}$  we obtain a quasicoherent sheaf of algebras  $D_{\lambda,X}$  on X which is called the sheaf of  $\lambda$ -twisted differential

operators. If  $\lambda = 0$ , this sheaf coincides with the sheaf  $D_X$  of usual differential operators, and in general it has very similar properties, for example  $\operatorname{gr}(D_{\lambda,X}(U)) = \mathcal{O}(T^*U)$  for any affine open set  $U \subset X$ . A quasicoherent sheaf on X with the structure of a (left or right)  $D_{\lambda,X}$ -module is called a (left or right)  $\lambda$ -twisted D-module on X. For example, if  $\lambda \in P$  then  $\mathcal{L}_{\lambda}$  is a left  $D_{\lambda,X}$ -module. The category of such modules is denoted by  $\mathcal{M}^{\lambda}(X)$  (of course, it depends on the principal bundle  $\widetilde{X}$  but we do not indicate it in the notation). Note that for  $\beta \in P$  we have an equivalence  $\mathcal{M}^{\lambda}(X) \cong \mathcal{M}^{\lambda+\beta}(X)$  defined by tensoring with  $\mathcal{L}_{\beta}$ .

**Example 29.5.** Let  $\mathcal{L}$  be a line bundle on X and  $c \in \mathbf{k}$ . Let  $\widetilde{X}$  be the subset of nonzero vectors in the total space of  $\mathcal{L}$ . We have a natural action of  $T := \mathbf{k}^{\times}$  on  $\widetilde{X}$  by dilations, and c defines a character of Lie(T). Thus we can define the sheaf  $D_{c,L,X}$  of twisted differential operators on X, and if  $c \in \mathbb{Z}$  then  $D_{c,L,X} = D_X(L^{\otimes c})$  is the sheaf of differential operators on  $L^{\otimes c}$ . For example, if  $\Omega_X$  is the canonical bundle of X then  $D_{1,\Omega,X} = D_X(\Omega)$  is naturally isomorphic to the sheaf of usual differential operators with opposite multiplication,  $D_X^{\text{op}}$ .

Thus tensoring with  $\Omega$  defines a canonical equivalence

$$\mathcal{M}_l(X) \cong \mathcal{M}_r(X)$$

(i.e., the sheaf  $D_X$  is Morita equivalent, although not in general isomorphic, to  $D_X^{\text{op}}$ ). We may therefore not distinguish between these categories any more, identifying them by this equivalence, and can use left or right D-modules depending on what is more convenient.

29.3. The localization theorem for non-zero infinitesimal characters. We are now ready to generalize the localization theorem to non-zero infinitesimal characters. Let  $U_{\lambda}$  be the minimal quotient of  $U(\mathfrak{g})$  corresponding to the infinitesimal character  $\chi_{\lambda-\rho}$ . Recall that  $\operatorname{gr}(U_{\lambda}) = \mathcal{O}(\mathcal{N})$ .

Let  $\widetilde{\mathcal{F}} := G/[B,B]$ . We have a right action of T := B/[B,B] on this variety by  $y \mapsto yt$ , defining the structure of a principal T-bundle  $\widetilde{\mathcal{F}} \to \mathcal{F}$ . Thus for every  $\lambda \in P \otimes_{\mathbb{Z}} \mathbb{C} = \mathfrak{h}^*$  we have a sheaf of  $\lambda$ -twisted differential operators  $D_{\lambda,\mathcal{F}} = D_{\lambda}$  on  $\mathcal{F}$ . For example, if  $\lambda \in P$  then  $D_{\lambda}$  is the sheaf of differential operators acting on sections of the line bundle  $\mathcal{L}_{\lambda}$  appearing in the Borel-Weil theorem (Theorem 27.3). Let  $D_{\lambda}(\mathcal{F})$  be the algebra of global  $\lambda$ -twisted differential operators on  $\mathcal{F}$ ; it is clear that  $\operatorname{gr} D_{\lambda}(\mathcal{F}) \subset \mathcal{O}(T^*\mathcal{F})$ . Also, we have a natural filtration-preserving action map  $a: U(\mathfrak{g}) \to D_{\lambda}(\mathcal{F})$ .

Theorem 29.6. (Beilinson-Bernstein) (i) The map

$$a: U(\mathfrak{g}) \to D_{\lambda}(\mathcal{F})$$

factors through a map  $a_{\lambda}: U_{\lambda} \to D_{\lambda}(\mathcal{F})$ .

- (ii) One has  $gr(a_{\lambda}) = p^*$  where p is the Springer map  $T^*\mathcal{F} \to \mathcal{N}$ .
- (iii)  $\operatorname{gr} D_{\lambda}(\mathcal{F}) = \mathcal{O}(T^*\mathcal{F})$  and  $a_{\lambda}$  is an isomorphism.

*Proof.* The proof is completely parallel to the proof of Theorem 29.1.

As in the untwisted case, the isomorphism  $a_{\lambda}$  gives rise to two functors: the functor of global sections

$$\Gamma: \mathcal{M}^{\lambda}(\mathcal{F}) \to D_{\lambda}(\mathcal{F}) - \text{mod} \cong U_{\lambda} - \text{mod}$$

and the functor of localization

$$\operatorname{Loc}: U_{\lambda} - \operatorname{mod} \cong D_{\lambda}(\mathcal{F}) - \operatorname{mod} \to \mathcal{M}_{\lambda}(\mathcal{F})$$

given by  $\operatorname{Loc}(M)(U) := D_{\lambda}(U) \otimes_{D_{\lambda}(\mathcal{F})} M$  for an affine open set  $U \subset \mathcal{F}$ . Moreover, as before, Loc is left adjoint to  $\Gamma$ .

Let us say that  $\lambda \in \mathfrak{h}^*$  is **antidominant** if  $-\lambda$  is dominant (cf. Subsection 16.1).

**Theorem 29.7.** (Beilinson-Bernstein localization theorem) If  $\lambda$  is antidominant then the functors  $\Gamma$  and Loc are mutually inverse equivalences. Thus the category  $U_{\lambda}$  – mod is canonically equivalent to the category of  $D_{\lambda}$ -modules on the flag variety  $\mathcal{F}$ .

- **Remark 29.8.** 1. As explained above, for  $\beta \in P$  we have an equivalence  $\mathcal{M}^{\lambda}(\mathcal{F}) \cong \mathcal{M}^{\lambda+\beta}(\mathcal{F})$  defined by tensoring with  $\mathcal{L}_{\beta}$ . On the other side of the Beilinson-Bernstein equivalence this corresponds to translation functors defined in Subsection 24.1.
- 2. The first statement of Theorem 29.7 fails if  $\lambda$  is not assumed antidominant. Indeed, if  $\lambda$  is integral but not antidominant then by the Borel-Weil theorem (Theorem 27.3)  $\Gamma(\mathcal{F}, \mathcal{L}_{\lambda}) = 0$ , so the functor  $\Gamma$  is not faithful. The second statement of Theorem 29.7 also fails if  $\lambda \in P$  and  $\lambda \rho$  is not regular.

For example, for  $\mathfrak{g} = \mathfrak{sl}_2$  and  $\lambda \in \mathbb{Z}$ , the localization theorem holds for  $\lambda \leq 0$ . For  $\lambda \geq 2$  the first statement fails but we still have an equivalence  $\mathcal{M}^{\lambda}(\mathcal{F}) \cong U_{\lambda} - \text{mod}$  (as  $U_{\lambda} \cong U_{-\lambda+2}$ ), albeit not given by  $\Gamma$ . But for  $\lambda = 1$  there is no such equivalence at all; in fact, one can show that the category  $U_{\lambda} - \text{mod}$ , unlike  $\mathcal{M}^{\lambda}(\mathcal{F})$ , has infinite cohomological dimension.

#### 30. D-modules - II

We would now like to explain how the Beilinson-Bernstein localization theorem can be used to classify various kinds of irreducible representations of  $\mathfrak{g}$ . For this we will need to build up a bit more background on D-modules.

30.1. Support of a quasicoherent sheaf. Let M be a quasicoherent sheaf on a variety X, and  $Z \subset X$  a closed subvariety. We will say that M is supported on Z if for any affine open set  $U \subset X$ , regular function  $f \in \mathcal{O}(U)$  vanishing on Z, and  $v \in M(U)$ , there exists  $N \in \mathbb{Z}_{\geq 0}$  such that  $f^N v = 0$ . The support  $\operatorname{Supp}(M)$  is then defined as the intersection of all closed subvarietes  $Z \subset X$  such that M is supported on Z. So M is supported on Z iff the support of M is contained in Z.

In particular, we can talk about support of a (left or right, possibly twisted) D-module on a smooth variety X. The category of D-modules on X supported on Z will be denoted by  $\mathcal{M}_Z(X)$ .

**Example 30.1.** It is easy to see that  $\mathbb{C}[x,x^{-1}]$  is a left D-module on  $\mathbb{A}^1$ , and  $\mathbb{C}[x]$  is its submodule. These modules have full support  $\mathbb{A}^1$ . On the other hand, consider the quotient  $\delta_0 := \mathbb{C}[x,x^{-1}]/\mathbb{C}[x].^{21}$  It is clear that  $\delta_0$  has a basis  $v_i = x^{-i}$ ,  $i \geq 1$ , with  $xv_i = v_{i-1}$ ,  $xv_1 = 0$ ,  $\partial v_i = -iv_{i+1}$ . Thus the support of  $\delta_0$  is  $\{0\}$ .

30.2. Restriction to an open subset. Recall that if  $\mathcal{A}$  is an abelian category and  $\mathcal{B} \subset \mathcal{A}$  a Serre subcategory (i.e., a full subcategory closed under taking subquotients and extensions) then one can form the quotient category  $\mathcal{A}/\mathcal{B}$  with the same objects as  $\mathcal{A}$ , but with  $\operatorname{Hom}_{\mathcal{A}/\mathcal{B}}(X,Y)$  being the direct limit of  $\operatorname{Hom}_{\mathcal{A}}(X',Y/Y')$  over  $X' \subset X$  and  $Y' \subset Y$  such that  $X',Y' \in \mathcal{B}$ . One can show that  $\mathcal{A}/\mathcal{B}$  is an abelian category. The natural functor  $F: \mathcal{A} \to \mathcal{A}/\mathcal{B}$  is then called the **Serre quotient functor**. This functor is essentially surjective, its kernel is  $\mathcal{B}$ , and it maps simple objects to simple objects or zero. Thus F defines a bijection between simple objects of  $\mathcal{A}$  not contained in  $\mathcal{B}$  and simple objects of  $\mathcal{A}/\mathcal{B}$ .

For example, if X is a variety,  $Z \subset X$  a closed subvariety,  $\operatorname{Qcoh}(X)$  the category of quasicoherent sheaves on X and  $\operatorname{Qcoh}_Z(X)$  the full subcategory of sheaves supported on Z then  $\operatorname{Qcoh}(X)/\operatorname{Qcoh}_Z(X) \cong \operatorname{Qcoh}(X \setminus Z)$ . The corresponding Serre quotient functor is the restriction  $M \mapsto M|_{X \setminus Z}$ .

<sup>&</sup>lt;sup>21</sup>In analysis  $\delta_0$  arises as the *D*-module generated by the  $\delta$ -function at zero, which motivates the notation.

Now assume that X is smooth. Let  $j: X \setminus Z \hookrightarrow X$  be the open embedding. Then we have a **restriction functor** on D-modules

$$j!: \mathcal{M}(X) \to \mathcal{M}(X \setminus Z)$$

which is the usual restriction functor at the level of sheaves; it is also called the **inverse image** or **pull-back** functor, since it is a special case of the inverse image functor defined above. Thus  $j^!(M) = 0$  if and only if M is supported on Z and the functor  $j^!$  is a Serre quotient functor which induces an equivalence  $\mathcal{M}(X)/\mathcal{M}_Z(X) \cong \mathcal{M}(X \setminus Z)$ .

The functor  $j^!$  has a right adjoint **direct image (or push-forward)** functor

$$j_*: \mathcal{M}(X \setminus Z) \to \mathcal{M}(X),$$

which is just the sheaf-theoretic direct image (=push-forward). Namely, for an affine open  $U \subset X$ ,  $j_*M(U) := M(U \setminus Z)$  regarded as a module over  $D(U) \subset D(U \setminus Z)$ . While the functor  $j^!$  is exact, the functor  $j_*$  is only left exact, in general (as so is the push-forward functor for sheaves). In particular,  $j_*$  is **not** the (right exact) direct image defined above since the morphism j is not affine, in general; rather it is the zeroth cohomology of the full direct image functor defined on the derived category of D-modules, which we will not discuss here. They do agree, however, when j is affine (e.g., when Z is a hypersurface).

In particular,  $j^!$  defines a bijection between isomorphism classes of simple  $D_X$ -modules which are not supported on Z and simple  $D_{X\setminus Z}$ -modules, given by  $M\mapsto j^!M$ .

The inverse map is defined as follows. Given  $L \in \mathcal{M}(X \setminus Z)$ , consider the D-module  $j_*L$ . Since  $j_*$  is right adjoint to  $j^!$ , the module  $j_*L$  does not contain nonzero submodules supported on Z. Now define  $j_{!*}L$  to be the intersection of all submodules N of  $j_*L$  such that  $j_*L/N$  is supported on Z. This gives rise to a functor  $j_{!*}: \mathcal{M}(X \setminus Z) \to \mathcal{M}(X)$  (not left or right exact in general). Then if L is irreducible, so is  $j_{!*}L$ , and  $j^!j_{!*}L \cong L$ , while for  $M \in \mathcal{M}(X)$  irreducible and not supported on Z we have  $j_{!*}j^!M \cong M$ . The functor  $j_{!*}$  is called the **Goresky-MacPherson extension** or **minimal** (or intermediate) extension functor

**Proposition 30.2.** The support of an irreducible D-module is irreducible.

Proof. Let M be a  $D_X$ -module with support Z. Assume that Z is reducible:  $Z=Z_1\cup Z_2$  where  $Z_1$  is an irreducible component of Z and  $Z_2$  the union of all the other components. Let  $Y=Z_1\cap Z_2$ , a proper subset in  $Z_1$  and  $Z_2$ . Let  $Z^\circ=Z\setminus Y$ ,  $Z_i^\circ=Z_i\setminus Y$  and  $X^\circ=X\setminus Y$ . Then  $Z^\circ=Z_1^\circ\cup Z_2^\circ$  is disconnected:  $Z_1^\circ,Z_2^\circ$  are closed

nonempty subsets of  $Z^{\circ}$  and  $Z_1^{\circ} \cap Z_2^{\circ} = \emptyset$ . Let  $M_1, M_2$  be the sums of all subsheaves of  $M|_{X^{\circ}}$  which are killed by localization away from  $Z_1^{\circ}$ , respectively  $Z_2^{\circ}$ . It is easy to show that  $M_i$  are nonzero submodules of  $M|_{X^{\circ}}$  and  $M|_{X^{\circ}} \cong M_1 \oplus M_2$ . Thus  $M|_{X^{\circ}}$  is reducible and hence so is M.

30.3. **Kashiwara's theorem.** Let X be a smooth variety and  $Z \subset X$  a smooth closed subvariety with closed embedding  $i: Z \hookrightarrow X$ . For  $M \in \mathcal{M}(X)$  define  $M_Z$  to be the sheaf on X whose sections on an affine open set  $U \subset X$  are the vectors in M(U) annihilated by regular functions on U vanishing on Z. Thus the  $\mathcal{O}(U)$ -action on  $M_Z(U)$  factors through  $\mathcal{O}(Z \cap U)$ . Also it is easy to see that  $M_Z(U)$  depends only on  $Z \cap U$ , i.e., it gives rise to a quasicoherent sheaf  $i^{\dagger}M$  on Z with sections

$$i^{\dagger}M(V) := M_Z(U)$$

for affine open  $U \subset X$  such that  $V = Z \cap U$ . Moreover, if v is a vector field on U tangent to V then v preserves the ideal of V, hence acts naturally on  $i^{\dagger}M(V)$ . Furthermore, the action of v on this space depends only on the vector field on V induced by v. Thus  $i^{\dagger}M(V)$  carries an action of the Lie algebra Vect(V). Together with the action of  $\mathcal{O}(V)$ , this defines an action of D(V) on  $i^{\dagger}M(V)$ . We conclude that  $i^{\dagger}M$  is naturally a  $D_Z$ -module. Thus we have defined a left exact functor

$$i^{\dagger}: \mathcal{M}(X) \to \mathcal{M}(Z).$$

It is called the **shifted inverse image** functor. This terminology is motivated by the following exercise.

**Exercise 30.3.** Show that  $i^{\dagger} = L^d i^!$  and  $i^! = R^d i^{\dagger}$ , where  $L^d$ ,  $R^d$  are the d-th left, respectively right derived functors and  $d = \dim X - \dim Z$ .

**Theorem 30.4.** (Kashiwara) The functor  $i^{\dagger}$  is an equivalence of categories  $\mathcal{M}_Z(X) \to \mathcal{M}(Z)$ .

The proof is not difficult, but we will skip it (see [HTT]).

The inverse of the functor  $i^{\dagger}$  is called the **direct image** functor and denoted  $i_*: \mathcal{M}(Z) \to \mathcal{M}_Z(X)$ , as it is a special case of the direct image functor defined above for affine morphisms. If we view  $i_*$  as a functor  $\mathcal{M}(Z) \to \mathcal{M}(X)$  then it has both left and right adjoint, where are  $i^!$  and  $i^{\dagger}$ , respectively.

Let us give a prototypical example.

**Example 30.5.** Let  $X = \mathbb{A}^1$ ,  $Z = \{0\}$ . Then  $\mathcal{M}(Z) = \text{Vect}$  and  $i_*(V) = V \otimes \delta_0$ . So in this case Kashiwara's theorem reduces to the claim that  $\text{Ext}^1(\delta_0, \delta_0) = 0$ .

**Remark 30.6.** We note that the above formalism and results extend in a straightforward manner to the case of twisted D-modules.

30.4. Equivariant D-modules. Let X be an algebraic variety with an action of an affine algebraic group G. Let us review the notion of a G-equivariant quasicoherent sheaf on X. Roughly speaking, this is a quasicoherent sheaf  $\mathcal{E}$  on X equipped with a system of isomorphisms  $\phi_g: g(\mathcal{E}) \cong \mathcal{E}, g \in G$  such that  $\phi_{gh} = \phi_g \circ g(\phi_h)$  and  $\phi_g$  depends on g algebraically. To give a formal definition, note that the group structure gives us a multiplication map  $m: G \times G \twoheadrightarrow G$ , and the action of G gives us a map  $\rho: G \times X \twoheadrightarrow X$ . We have a commutative diagram

**Definition 30.7.** A G-equivariant quasicoherent sheaf on X is a quasicoherent sheaf  $\mathcal{E}$  on X equipped with an isomorphism

$$\phi: \rho^* \mathcal{E} \cong \mathcal{O}_G \boxtimes \mathcal{E}$$

making the following diagram commutative:

$$(\operatorname{id} \times \rho)^* \rho^* \mathcal{E} \xrightarrow{(\operatorname{id} \times \rho)^* \phi} (\operatorname{id} \times \rho)^* (\mathcal{O}_G \boxtimes \mathcal{E}) \xrightarrow{\mathcal{O}_G \boxtimes \rho^* \mathcal{E}} \downarrow^{\mathcal{O}_G \boxtimes \phi} \\ (m \times \operatorname{id})^* \rho^* \mathcal{E} \xrightarrow{(m \times \operatorname{id})^* \phi} (m \times \operatorname{id})^* (\mathcal{O}_G \boxtimes \mathcal{E}) \xrightarrow{\mathcal{O}_G \boxtimes \mathcal{O}_G \boxtimes \mathcal{E}}$$

Thus  $\phi$  comprises all the isomorphisms  $\phi_g$ , which therefore satisfy the equality  $\phi_{gh} = \phi_g \circ g(\phi_h)$  and depend on g algebraically.

We now wish to define the notion of a G-equivariant  $D_X$ -module. To this end, recall that for any  $D_X$ -module  $\mathcal{E}$ , the quasicoherent sheaf  $\rho^*\mathcal{E}$  carries a natural structure of a  $D_{G\times X}$ -module (the D-module inverse image). We now make the following definition.

**Definition 30.8.** A weakly G-equivariant D-module on X is a  $D_X$ -module  $\mathcal{E}$  with a G-equivariant quasicoherent sheaf structure, where  $\phi$  is  $D_X$ -linear.

Note that if  $\mathcal{E}$  is a weakly equivariant  $D_X$ -module then we have two (in general, different) actions of  $\mathfrak{g} = \text{Lie}(G)$  on  $\mathcal{E}$ . First of all, the G-action on X gives us maps  $\mathfrak{g} \to \text{Vect}(X) \to D(X)$ , and so the D-module structure on  $\mathcal{E}$  gives us a  $\mathfrak{g}$ -action  $x \mapsto b_0(x)$  on  $\mathcal{E}$ . Note that

this action does not depend on the choice of the weakly equivariant structure  $\phi$ .

On the other hand, we have a  $\mathfrak{g}$ -action on  $\mathcal{O}_G \boxtimes \mathcal{E}$  coming from the G-action on  $G \times X$  given by  $g \cdot (h, x) = (gh, x)$ . Translating this along  $\phi$ , we get a  $\mathfrak{g}$ -action on  $\rho^*\mathcal{E}$ . Restricting to  $1 \times X$ , this gives us another  $\mathfrak{g}$ -action  $x \mapsto b_{\phi}(x)$  on  $\mathcal{E}$ .

**Definition 30.9.** A (strongly) G-equivariant  $D_X$ -module is a weakly G-equivariant  $D_X$ -module where these two  $\mathfrak{g}$ -actions agree:  $b_{\phi} = b_0$  (or, equivalently, where  $\phi$  is  $D_{G \times X}$ -linear.)

In general, since  $[b_0(x), L] = [b_{\phi}(x), L]$  for  $L \in D_X$ , the operator  $\rho_{\phi}(x) := b_{\phi}(x) - b_0(x)$  is a D-module endomorphism of  $\mathcal{E}$ . Moreover, it is easy to see that  $\rho_{\phi}$  is a Lie algebra homomorphism  $\mathfrak{g} \to \operatorname{End}(\mathcal{E})$ . In particular, if  $\mathcal{E}$  is irreducible then by Dixmier's lemma (Lemma 7.2),  $\operatorname{End}(\mathcal{E}) = \mathbb{C}$ , so  $\rho_{\phi}$  is just a character of  $\mathfrak{g}$ . Thus if  $\mathfrak{g} = [\mathfrak{g}, \mathfrak{g}]$  is perfect (for example, semisimple) then every weakly G-equivariant irreducible  $D_X$ -module is actually (strongly) G-equivariant.

**Remark 30.10.** A given  $D_X$ -module may have many weakly G-equivariant structures, but if G is connected, then it can only have one G-equivariant structure. This is because the  $\mathfrak{g}$ -action on  $\mathcal{E}$  is determined by the map  $\mathfrak{g} \to D(X)$  and this action can be integrated to a G-equivariant structure in an unique way (recall that we always work over a field of characteristic 0.)

Furthermore, any  $D_X$ -linear map of G-equivariant  $D_X$ -modules is automatically compatible with the G-action. This is because such a map is necessarily  $\mathfrak{g}$ -linear, which implies that it is in fact G-linear. These two facts combined show that the category of G-equivariant  $D_X$ -modules is a full subcategory of the category of  $D_X$ -modules. Stated another way, G-equivariance of a  $D_X$ -module is a property, not a structure.

**Example 30.11.** Consider the case where X is a point. Then  $D_X \cong \mathbb{C}$  and so a  $D_X$ -module is a just a vector space. A weakly G-equivariant  $D_X$ -module is then simply a locally algebraic representation of G. This representation gives a G-equivariant structure if and only if  $\mathfrak{g}$  acts by 0, i.e., the connected component of the identity  $G_0 \subset G$  acts trivially. Thus a G-equivariant  $D_X$ -module is just a representation of the component group  $G/G_0$ . Conversely, any locally algebraic representation V of G gives rise to a weakly G-equivariant D-module on X which is equivariant iff  $G_0$  acts trivially on V, so that V is a representation of  $G/G_0$ .

**Example 30.12.** Let X = G/H, where G is an algebraic group and H a closed subgroup of G. Then we claim that a G-equivariant  $D_X$ -module is the same thing as an H-equivariant D-module on a point, i.e., a representation of the component group  $H/H_0$ . Indeed, given an  $H/H_0$ -module V, we can define a G-equivariant vector bundle

$$(G \times V)/H \to X = G/H,$$

where H acts on  $G \times V$  via  $(g, v)h = (gh, h^{-1}v)$ . Note that this can be written as  $\frac{(G/H_0)\times V}{H/H_0}$  (as  $H_0$  acts on V trivially). This shows that this vector bundle has a natural flat connection, i.e. is a  $D_X$ -module L(X, V), which is clearly G-equivariant. The assignment  $V \mapsto L(X, V)$  is the desired equivalence. In the case H = G, this reduces to Example 30.11.

**Exercise 30.13.** (i) Define the algebraic group  $L := G \times_{G/G_0} H/H_0$  of pairs (g, h),  $g \in G$ ,  $h \in H/H_0$  which map to the same element of  $G/G_0$ ; thus we have a short exact sequence

$$1 \to G_0 \to L \to H/H_0 \to 1$$
.

Show that the category of weakly G-equivariant D-modules on G/H is naturally equivalent to the category of representations of L, such that the subcategory of strongly G-equivariant D-modules is identified with the subcategory of representations of L pulled back from the second factor  $H/H_0$  (i.e., those with trivial action of  $G_0$ ), and the subcategory of modules of the form  $\mathcal{O}(G/H) \otimes V$  where V is a G-module is identified with the category of representations of L pulled back from the first factor G.

(ii) Let  $\Delta: H \to L$  be the map defined by  $\Delta(h) = (h, h)$ . Show that the forgetful functor from weakly G-equivariant D-modules on G/H to G-equivariant quasicoherent sheaves on G/H corresponds to the pullback functor  $\Delta^*$ .

**Exercise 30.14.** Let X be a smooth variety with an action of an affine algebraic group G and  $H \subset G$  be a closed subgroup. Show that the category of H-equivariant D-modules on X is naturally equivalent to the category of G-equivariant D-modules on  $X \times G/H$  with diagonal action of G (note that when X is a point, this reduces to Example 30.12).

**Exercise 30.15.** Let X be a principal G-bundle over a smooth variety Y. Show that the category of G-equivariant  $D_X$ -modules is naturally equivalent to the category of  $D_Y$ -modules. Namely, given a G-equivariant  $D_X$ -module M, for an affine open set  $U \subset Y$  let  $\widetilde{U}$  be the

preimage of U in X and let  $\overline{M}(U) := M(\widetilde{U})^G$ . Then  $\overline{M}$  is a  $D_Y$ -module, and the assignment  $M \mapsto \overline{M}$  is a desired equivalence.

The notion of a weakly equivariant D-module often arises in the following setting. Let T be an algebraic torus and let  $\widetilde{X}$  be a principal T-bundle over X.

**Definition 30.16.** A monodromic  $D_X$ -module (with respect to the bundle  $\widetilde{X} \to X$ ) is a weakly T-equivariant  $D_{\widetilde{X}}$ -module.

**Example 30.17.** A monodromic  $D_X$ -module with  $\rho_{\phi} = \lambda \in \text{Lie}(T)^*$  is the same thing as a  $\lambda$ -twisted D-module on X, i.e., a  $D_{\lambda,X}$ -module.

**Proposition 30.18.** Assume that X is a D-affine variety and that K is an affine algebraic group acting on X. Let D(X) be the ring of global sections of  $D_X$ . Then the category of K-equivariant  $D_X$ -modules is equivalent to the category of D(X)-modules M endowed with a locally finite K-action whose differential coincides with the action of Lie(K) on M coming from the map  $\text{Lie}(K) \to D(X)$ .

Exercise 30.19. Prove Proposition 30.18.

In particular, by the Beilinson-Bernstein localization theorem, Proposition 30.18 applies to  $X = \mathcal{F} \cong G/B$  and K a closed subgroup of G, and moreover it extends to the case of  $\lambda$ -twisted differential operators on  $\mathcal{F}$  for antidominant  $\lambda \in \mathfrak{h}^*$ . Thus we get

Corollary 30.20. If  $\lambda \in \mathfrak{h}^*$  is antidominant then the functors  $\Gamma$ , Loc restrict to mutually inverse equivalences between the category of  $(\mathfrak{g}, K)$ -modules with infinitesimal character  $\chi_{\lambda-\rho}$  and the category of K-equivariant  $D_{\lambda}$ -modules on  $\mathcal{F}$ .

#### 31. Applications of D-modules to representation theory

### 31.1. Classification of irreducible equivariant *D*-modules for actions with finitely many orbits.

**Theorem 31.1.** Let X be a smooth variety and K a connected algebraic group acting on X with finitely many orbits. Then there are finitely many irreducible K-equivariant D-modules on X. Namely, they are parametrized by pairs (O,V) where O is an orbit of K on X and V is an irreducible representation of the component group  $H/H_0$  of the stabilizer  $H := K_x$  for  $x \in O$ ,  $(O,V) \mapsto M(O,V)$ .

Proof. Let M be an irreducible K-equivariant D-module on X. Then by Proposition 30.2, the support Z of M is irreducible. Thus  $Z = \overline{O}$  for a single orbit O of K. Let  $Z_0 = \overline{O} \setminus O$ , and  $U = X \setminus Z_0$ . Then U is a K-stable open subset of X and O is closed in U. Also  $M|_U$  is a simple  $D_U$ -module supported on O. Let  $i:O \hookrightarrow X$  be the closed embedding. By Kashiwara's theorem (Theorem 30.4)  $i^{\dagger}M$  is a simple K-equivariant D-module on O. Thus by Example 30.12  $i^{\dagger}M = L(O,V)$  for some irreducible representation V of the component group of the stabilizer  $K_x$ ,  $x \in O$ . Also it is clear that L(O,V) gives rise to a simple K-equivariant D-module on X, namely,  $M(O,V) := j_{!*}i_*M(O,V)$ , where  $j:U \hookrightarrow X$  is the open embedding. This proves the theorem.  $\square$ 

Remark 31.2. Theorem 31.1 can be extended in a straightforward way to weakly equivariant D-modules. In this case, recall that the weakly equivariant structure on an irreducible D-module M defines a character  $\rho: \mathfrak{k} \to \mathbb{C}$ , where  $\mathfrak{k} = \text{Lie}K$ . Theorem 31.1 then holds with the only change: rather than being a representation of  $H/H_0$ , V now needs to be a representation of H in which Lie(H) acts by the character  $\rho$ . The proof is analogous to the case  $\rho = 0$ .

In particular, this applies to the case of twisted D-modules. In this case we have a principal T-bundle  $p: \widetilde{X} \to X$  and a character  $\lambda \in \mathfrak{t}^*$ ,  $\mathfrak{t} = \operatorname{Lie}(T)$ . Suppose K acts on X preserving this bundle; i.e., it acts on  $\widetilde{X}$  and commutes with T. So we have a  $K \times T$ -action on  $\widetilde{X}$  and a K-equivariant  $\lambda$ -twisted D-module on X is just a weakly  $K \times T$ -equivariant D-module on  $\widetilde{X}$  with  $\rho(k,t) := \lambda(t)$ . Now, for every K-orbit O on X, we have the stabilizer  $K_x$ ,  $x \in O$ , and a homomorphism  $\xi_x : K_x \to T$  defined by the condition that  $(g, \xi_x(g))$  acts trivially on  $p^{-1}(x)$  for  $g \in K_x$ . This defines a character  $\lambda_x = \lambda \circ d\xi_x$  of  $\operatorname{Lie}(K_x)$ , and the simple K-equivariant  $D_\lambda$ -modules on X are M(O, V) where V is an irreducible representation of  $K_x$  with  $\operatorname{Lie}(K_x)$  acting by the character  $\lambda_x$ .

31.2. Classification of irreducible Harish-Chandra modules. Let  $G_{\mathbb{R}}$  be a connected real semisimple algebraic group,  $K_{\mathbb{R}} \subset G_{\mathbb{R}}$  a maximal compact subgroup,  $G, K \subset G$  their complexifications. By Corollary 30.20, if  $\lambda$  is antidominant then the Beilinson-Bernstein equivalence restricts to an equivalence between the category of  $(\mathfrak{g}, K)$ -modules with infinitesimal character  $\chi_{\lambda-\rho}$  and the category of K-equivariant  $D_{\lambda}$ -modules on  $\mathcal{F} = G/B$ .

**Proposition 31.3.** The group K acts on  $\mathcal{F}$  with finitely many orbits.

We will not give a proof of this proposition. For the proof and description of the set of orbits, see [RS].

Proposition 31.3 along with Theorem 31.1 allows us to classify irreducible  $(\mathfrak{g}, K)$ -modules (i.e., Harish-Chandra modules) for a regular infinitesimal character (the general case can be handled similarly).

Namely, let  $H \subset B \subset G$  be a maximal torus and Borel subgroup of G; so  $H \cong B/[B,B]$ . Note that  $K \times H$  acts on  $\widetilde{\mathcal{F}} = G/[B,B]$ . So for a K-orbit O on  $\mathcal{F} = G/B$  and  $x \in O$ , we have a homomorphism  $\xi_x : K_x \to H$  such that  $(g, \xi_x(g))$  acts trivially on the fiber over x in  $\widetilde{\mathcal{F}}$  for  $g \in K_x$ .

Let  $\chi$  be a regular infinitesimal character for  $\mathfrak{g}$  and  $\lambda$  be an antidominant weight with  $\chi = \chi_{\lambda-\rho}$  (note that it always exists).

**Theorem 31.4.** Irreducible  $(\mathfrak{g}, K)$ -modules with (pure) infinitesimal character  $\chi$  are  $\pi(O, V)$  where O is a K-orbit on  $\mathcal{F}$  and V an irreducible representation of  $K_x$ ,  $x \in O$  such that  $\text{Lie}(K_x)$  acts via the character  $\lambda_x$ . Namely,  $\pi(O, V)$  corresponds to M(O, V) under the Beilinson-Bernstein equivalence.

**Example 31.5.** Let  $G_{\mathbb{R}} = SL_2(\mathbb{R})$ . Let  $\lambda \in \mathbb{C}$ ,  $\lambda \notin \mathbb{Z}_{>0}$  and set  $\chi = \chi_{\lambda-1}$  (so  $\chi \neq \chi_0$ ). In this case  $\mathcal{F} = \mathbb{CP}^1$  is the Riemann sphere, and  $K = \mathbb{C}^{\times}$  acts by  $k \circ z := k^2 z$ . Thus we have three orbits:  $0, \infty$ , and  $\mathbb{C}^{\times}$ . For the orbit  $\mathbb{C}^{\times}$  we have  $K_x = \mathbb{Z}/2$ , so we have two irreducible representations  $V = \mathbb{C}_{\pm}$ , which generically correspond to principal series representations  $\pi(\mathbb{C}^{\times}, V_{\pm}) = P_{\pm}(1 - \lambda)$  (see Section 9). The other two orbits have a connected stabilizer, and  $\lambda_x = \pm \lambda$ . Thus for such orbits representations exist only for  $\lambda \in \mathbb{Z}_{\leq 0}$ . It is easy to see that these are exactly the discrete series representations  $M_{\lambda-2}^+$ ,  $M_{-\lambda+2}^-$ . Also for such points one of the principal series representations is reducible  $(P_+(1-\lambda))$  for even  $\lambda$  and  $P_-(1-\lambda)$  for odd  $\lambda$ ) and  $\pi(\mathbb{C}^{\times}, V_+)$ , respectively  $\pi(\mathbb{C}^{\times}, V_-)$  is actually the finite-dimensional representation  $L_{-\lambda}$ . Thus we have four irreducible representations in this case.

Note that this agrees with our classification of irreducible representations of  $SL_2(\mathbb{R})$  for regular infinitesimal characters discussed in Section 9.

**Example 31.6.** Let G be a simply connected complex semisimple group regarded as a real group. Then its maximal compact subgroup is  $G_c$ , so its complexification is G, and  $G_{\mathbb{C}} = G \times G$ , so that the inclusion  $(G_c)_{\mathbb{C}} = G \hookrightarrow G_{\mathbb{C}} = G \times G$  is the diagonal embedding. The flag variety is  $\mathcal{F} \times \mathcal{F} = G/B \times G/B$ . Thus Harish-Chandra bimodules with infinitesimal character  $(\chi_{\mu-\rho},\chi_{\lambda-\rho})$  for antidominant  $\lambda,\mu$  are  $\pi(O,V)$  where O runs over orbits of G on  $G/B\times G/B$  and V over appropriate representations of isotropy groups. Note that orbits of Gon  $G/B \times G/B$  are in a natural bijection with orbits of B on G/B, which are the Schubert cells  $C_w$  labeled by  $w \in W$ . One can check that the condition for existence of V on the orbit  $C_w$  is that  $\lambda - w\mu$  is integral, and then V is unique (as the isotropy groups are connected in this case). Thus we find that the irreducible Harish-Chandra bimodules with such infinitesimal character are labeled by elements w such that  $\lambda - w\mu \in P$ , which agrees with the classification we obtained in Subsection 25.2.

**Exercise 31.7.** Classify irreducible Harish-Chandra modules for  $SL_3(\mathbb{R})$  with a regular infinitesimal character.

**Hint.** Classify orbits of  $SO_3(\mathbb{C})$  on  $SL_3(\mathbb{C})/B$ . This is equivalent to classification of flags in a 3-dimensional complex inner product space E under the action of SO(E). Then classify possible representations V of the isotropy group for each orbit.

Remark 31.8. The K-orbits on G/B can be classified in explicit combinatorial terms. Together with Theorem 31.4, this leads to an alternative proof, using the localization theorem, of the **Langlands classification** of irreducible Harish-Chandra modules (obtained by Langlands in 1973 by a different method, 8 years before the localization theorem was proved, [La]). This classification requires a serious separate discussion which is beyond the scope of these notes.

31.3. Applications to category  $\mathcal{O}$ . Let us now see how this approach allows us to study category  $\mathcal{O}$  for a semisimple Lie algebra  $\mathfrak{g}$ .

Consider the category  $\mathcal{C}$  of weakly  $B \times B$ -equivariant finitely generated D-modules on G which are equivariant under  $[B, B] \times [B, B]$  (it is easy to see that such modules have finite length). Thus for  $M \in \mathcal{C}$ , we have a homomorphism  $\rho : \mathfrak{h} \oplus \mathfrak{h} \to \operatorname{End}(M)$ , so  $M = \bigoplus_{\mu,\lambda} M(\mu,\lambda)$  where  $M(\mu,\lambda)$  is the generalized eigenspace for  $\mathfrak{h} \oplus \mathfrak{h}$  with eigenvalue  $(\mu,\lambda) \in \mathfrak{h}^* \times \mathfrak{h}^*$ . Thus we have a decomposition  $\mathcal{C} = \bigoplus_{\mu,\lambda} \mathcal{C}_{\mu,\lambda}$ .

Let  $C_{[\mu],\lambda}$ ,  $C_{\mu,[\lambda]}$ ,  $C_{[\mu],[\lambda]}$  be the full subcategories of  $C_{\mu,\lambda}$  consisting of objects on which the eigenvalues in square brackets are pure (without Jordan blocks). Thus we have

$$C_{\mu,\lambda}\supset C_{[\mu],\lambda}, C_{\mu,[\lambda]}\supset C_{[\mu],[\lambda]}$$

and all simple objects of  $\mathcal{C}_{\mu,\lambda}$  are contained in  $\mathcal{C}_{[\mu],[\lambda]}$ . These objects are labeled by Bruhat cells  $BwB \subset G$ ,  $w \in W$  and representations V of the isotropy group satisfying an appropriate condition. As before, the condition for V to exist is that  $\lambda - w\mu \in P$ , thus  $\mathcal{C}_{\mu,\lambda} = 0$  unless  $\lambda - w\mu \in P$  for some  $w \in W$ .

We also see that  $C_{\lambda,\mu} \cong C_{\lambda+\beta,\mu+\gamma}$  for  $\beta, \gamma \in P$ , and the same applies to its subcategories.

Let us now try to describe these categories representation-theoretically. To this end, note that we may interpret  $\mathcal{C}_{[\mu],[\lambda]}$  as the category of weakly B-equivariant  $D_{\lambda}$ -modules on G/B with (pure) equivariance character  $\mu$ . So if  $\lambda$  is antidominant, we get that  $\mathcal{C}_{[\mu],[\lambda]}$  is equivalent to the full subcategory  $\mathcal{O}_{[\mu],[\lambda]}$  of the category  $\mathcal{O}_{\chi_{\lambda-\rho}}$  of objects with pure infinitesimal character  $\chi_{\lambda-\rho}$  and weights in  $\mu+P$ . Similarly,  $\mathcal{C}_{\mu,\lambda}$ ,  $\mathcal{C}_{[\mu],\lambda}$ ,  $\mathcal{C}_{\mu,[\lambda]}$  are equivalent to  $\mathcal{O}_{\mu,\lambda}$ ,  $\mathcal{O}_{[\mu],\lambda}$ ,  $\mathcal{O}_{\mu,[\lambda]}$ , where the corresponding (infinitesimal) character is pure if square brackets are present and generalized if not.

Now note that flipping left and right, we get equivalences  $\mathcal{C}_{\lambda,\mu} \cong \mathcal{C}_{\mu,\lambda}$ ,  $\mathcal{C}_{[\lambda],\mu} \cong \mathcal{C}_{\mu,[\lambda]}$   $\mathcal{C}_{\lambda,[\mu]} \cong \mathcal{C}_{[\mu],\lambda}$   $\mathcal{C}_{[\lambda],[\mu]} \cong \mathcal{C}_{[\mu],[\lambda]}$ . If  $\lambda,\mu$  are both antidominant, this yields equivalences of representation categories  $\mathcal{O}_{\lambda,\mu} \cong \mathcal{O}_{\mu,\lambda}$ ,  $\mathcal{O}_{[\lambda],\mu} \cong \mathcal{O}_{\mu,[\lambda]}$   $\mathcal{O}_{\lambda,[\mu]} \cong \mathcal{O}_{[\mu],\lambda}$   $\mathcal{O}_{[\lambda],[\mu]} \cong \mathcal{O}_{[\mu],[\lambda]}$ . While the first equivalence is easy to see representation theoretically using translation functors, the others are not. They are clear from geometry but somewhat mysterious from the viewpoint of representation theory (although they can be understood using the Bernstein-Gelfand equivalence between category  $\mathcal{O}$  and the category of Harish-Chandra bimodules, Theorem 25.8).

Example 31.9. If  $\lambda, \mu \in P$ , these categories are independent of  $\lambda, \mu$ . Namely, let  $\mathcal{O}_0$  be the category  $\mathcal{O}$  for the trivial generalized infinitesimal character, and  $\widetilde{\mathcal{O}}_0$  be its Serre closure (the category of modules admitting a finite filtration whose successive quotients are in  $\mathcal{O}_0$ ; i.e. the action of  $\mathfrak{h}$  is not necessarily diagonalizable but is only assumed locally finite). We may also define the category  $\mathcal{O}_0^*$  of modules in  $\widetilde{\mathcal{O}}_0$  which have pure infinitesimal character, and  $\overline{\mathcal{O}}_0 \subset \mathcal{O}_0$  of modules with both pure infinitesimal character and diagonalizable action of  $\mathfrak{h}$ . Then the above four categories are exactly  $\widetilde{\mathcal{O}}_0, \mathcal{O}_0, \mathcal{O}_0^*, \overline{\mathcal{O}}_0$ . In particular, we

obtain an equivalence  $\mathcal{O}_0 \cong \mathcal{O}_0^*$  which is not obvious representation-theoretically.

Finally, we note that Exercise 30.14 applied to X=G/B and H=B gives a transparent geometric proof of Theorem 25.8.

#### References

- [ABV] J. Adams, D. Barbasch, D. Vogan, The Langlands Classification and Irreducible Characters for Real Reductive Groups, Springer, 1992, http://www.math.utah.edu/~ptrapa/math-library/abv/abv.pdf
- [ALTV] J. Adams, M. van Leeuwen, P. Trapa, D. Vogan, Unitary Representations of Real Reductive Groups, Astérisque, 417, 2020.
- [Ba] Bargmann, V. (1947), "Irreducible unitary representations of the Lorentz group", Annals of Mathematics, Second Series, 48 (3): 568–640.
- [BB] A. Beilinson, J. Bernstein, "Localisation de g-modules", Comptes Rendus de l'Académie des Sciences, Série I, 292 (1): 15–18.
- [BCEY] A. Braverman, T. Chmutova, P. Etingof, D. Yang, Algebraic D-modules, notes in progress.
- [BG] J. Bernstein, S. Gelfand, Tensor products of finite and infinite-dimensional representations of semisimple Lie algebras, Compositio Mathematica, Volume 41 (1980) no. 2, pp. 245–285.
- [Bez] R. Bezrukavnikov, Canonical bases and representation categories, notes by T. Kanstrup, 2013, https://math.mit.edu/~bezrukav/old/Course\_RT.pdf
- [Ca] W. Casselman, Essays in analysis, Elliptic differential equations analyticity, https://personal.math.ubc.ca/~cass/research/pdf/Analytic.pdf
- [Che] C. Chevalley (1955), "Invariants of finite groups generated by reflections", Amer. J. Math., 77 (4): 778–782.
- [E] P. Etingof, Lie groups and Lie algebras, https://arxiv.org/pdf/2201.09397.pdf
- [Eis] D. Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, Graduate texts in Mathematics, v.150, Springer, 1995.
- [G] D. Gaitsgory, Notes on representations of real reductive groups, https://people.mpim-bonn.mpg.de/gaitsgde/RepRealRed\_2017/Notes.pdf
- [Ga] P. Garrett, Proving admissibility of irreducible unitaries, https://www-users.cse.umn.edu/~garrett/m/v/proving\_admissibility.pdf
- [GN] I. Gelfand, M. Naimark, (1946), "Unitary representations of the Lorentz group", Acad. Sci. USSR. J. Phys., 10: 93–94.
- [HC1] Harish-Chandra, "On some applications of the universal enveloping algebra of a semisimple Lie algebra", Transactions of the American Mathematical Society, 70 (1): 28–96.
- [HC2] Harish-Chandra, Representations of semi-simple Lie groups, I, III, Trans.
   A.M.S., 75 (1953), 185-243; 76 (1954), 234-253; IV, Amer. J. Math., 77 (1955), 743-777.
- [H] R. Hartshorne, Algebraic geometry, Graduate texts in Mathematics, Springer, 1977.
- [HTT] R. Hotta, K. Takeuchi, T. Tanisaki, D-modules, perverse sheaves, and representation theory, Springer, 2008.
- [Hu] J. Humphreys, Representations of Semisimple Lie Algebras in the BGG Category  $\mathcal{O}$ , Graduate Studies in Mathematics, Volume 94, AMS, 2008.
- [K] A. Knapp, Representation Theory of Semisimple Groups: An Overview Based on Examples (PMS-36), 1986.

- [KT] A. Knapp, P. Trapa, Representations of semisimple Lie groups, in: Representation theory of Lie groups, IAS-Park City Mathematics Series, v. 8, J. Adams, D. Vogan, eds., 2000, http://www.math.utah.edu/~ptrapa/Knapp-Trapa.pdf
- [Ko] B. Kostant, Lie group representations on polynomial rings, Amer. J. Math. 85 (1963), 327–402.
- [La] R. P. Langlands, (1989) [1973], "On the classification of irreducible representations of real algebraic groups", in Sally, Paul J.; Vogan, David A. (eds.), Representation theory and harmonic analysis on semisimple Lie groups, Math. Surveys Monogr., vol. 31, Providence, R.I.: American Mathematical Society, pp. 101–170, ISBN 978-0-8218-1526-7, MR 1011897
- [L] M. Libine, Introduction to Representations of Real Semisimple Lie Groups https://arxiv.org/pdf/1212.2578.pdf.
- [RS] R. Richardson, T. Springer, Combinatorics and geometry of K-orbits on the flag manifold. In: Linear algebraic groups and their representations, Contemp. Math. 153, Amer. Math. Soc., 1993, 109–142.
- [ST] G. C. Shephard, J. A. Todd (1954), "Finite unitary reflection groups", Can. J. Math., 6: 274–304.

DEPARTMENT OF MATHEMATICS, MIT, CAMBRIDGE, MA 02139, USA

# 18.757 Representations of Lie Groups Fall 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.