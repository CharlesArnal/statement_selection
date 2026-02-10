MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Introduction (Lecture 1)

Let X be an algebraic variety defined over a field k. If k is the field  $\mathbf{C}$  of complex numbers, then X has an underlying topological space  $X(\mathbf{C})$ . We can therefore study X using the methods of algebraic topology: for example, for any commutative ring R we can consider algebraic invariants such as the cohomology ring

$$H^*(X(\mathbf{C}); R).$$

Algebraic geometers have expended a great deal of effort in trying to reconstruct these sorts of invariants in a purely algebraic way. For example, if X is an elliptic curve over the complex numbers, then the homology group

$$H_1(X(\mathbf{C}), \mathbf{Z}/n\mathbf{Z})$$

is canonically isomorphic to the group of n-torsion points of X. This latter definition has the advantage that it makes sense over any field (and behaves well over any algebraically closed field whose characteristic does not divide n).

Building on this example, Grothendieck and his school constructed the theory of étale cohomology. If X is an algebraic variety defined over any separably closed field k and R is any commutative ring, then one can consider the étale cohomology

$$\mathrm{H}^*_{et}(X;R).$$

These groups behave well provided that the ring R has finite cardinality n, and the characteristic of k does not divide n. Moreover, if k is the field of complex numbers, then there is a canonical isomorphism

$$\mathrm{H}^*_{et}(X; \mathbf{Z}/p\mathbf{Z}) \simeq \mathrm{H}^*(X(\mathbf{C}), \mathbf{Z}/p\mathbf{Z})$$

for every integer p. In other words, étale cohomology provides a purely algebraic recipe for extracting the cohomology groups  $H^*(X(\mathbf{C}); \mathbf{Z}/p\mathbf{Z})$ . This raises the question: to what extent can we recover the topological space  $X(\mathbf{C})$  itself in purely algebraic terms?

Of course, algebro-topological invariants like cohomology do not contain enough information to determine a space like  $X(\mathbf{C})$  up to homeomorphism. The best we might hope for is to recover  $X(\mathbf{C})$  up to homotopy equivalence. However, even this is generally too much to ask for: étale cohomology is generally only well-behaved when the coefficient ring R is a finite ring, such as  $\mathbf{Z}/p\mathbf{Z}$ . To what extent can a topological space M be recovered from the cohomology ring  $H^*(M; \mathbf{Z}/p\mathbf{Z})$ ? To answer this question, it is convenient to introduce the notion of p-adic completion for topological spaces, following ideas of Sullivan.

Let M be a topological space and p a prime number. For simplicity, we will assume that M is simply connected, and that each of the homology groups  $H_n(M; \mathbf{Z})$  is finitely generated. In this case, there exists a p-adic completion  $M^{\vee}$  of M. It is characterized up to homotopy equivalence by the following properties:

- (1) There is a map  $f: M \to M^{\vee}$ .
- (2) The space  $M^{\vee}$  is simply connected.
- (3) For each n > 1, the induced map  $H_n(M; \mathbf{Z}) \to H_n(M^{\vee}; \mathbf{Z})$  exhibits  $H_n(M^{\vee}; \mathbf{Z})$  as the *p*-adic completion of the (finitely generated) abelian group  $H_n(M; \mathbf{Z})$ .

Remark 1. The p-adic completion of a space M is, in some sense, determined up to homotopy equivalence by the mod-p cohomology  $H^*(M; \mathbf{Z}/p\mathbf{Z})$ . Of course, for this to be true one must consider  $H^*(M; \mathbf{Z}/p\mathbf{Z})$  as endowed with more structure than just a graded vector space. The precise statement is that  $M^{\vee}$  can be reconstructed from the cochain complex  $C^*(M; \mathbf{Z}/p\mathbf{Z})$ , viewed as an  $E_{\infty}$ -algebra over the finite field  $\mathbf{Z}/p\mathbf{Z}$ . This follows from the p-adic homotopy theory of Mandell and Dwyer-Hopkins, which we will study later in this course.

Building on the work of the Grothendieck school, several mathematicians (Sullivan, Artin-Mazur, Friedlander, and others) have explained how to use the formalism of étale cohomology to extract an p-adic étale homotopy type from an algebraic variety X defined over an arbitrary separably closed k of characteristic different from p. In particular, if k is the field of complex numbers and the topological space  $X(\mathbf{C})$  is simply connected, the p-adic étale homotopy type of X coincides with the p-adic completion of  $X(\mathbf{C})$  as defined above. This is a strong sense in which one can recover a close approximation to  $X(\mathbf{C})$  by purely algebraic methods.

Suppose that the algebraic variety X is defined instead over the field  $\mathbb{R}$  of *real* numbers. In this case, one has an underlying topological space of real points  $X(\mathbb{R})$ . To what extent can *this* topological space be reconstructed in purely algebraic terms? We note that there is a canonical inclusion

$$X(\mathbb{R}) \subseteq X(\mathbf{C}).$$

The group  $\mathbb{Z}/2\mathbb{Z}$  acts on  $X(\mathbb{C})$ , via complex conjugation, and we can identify  $X(\mathbb{R})$  with the fixed set  $X(\mathbb{C})^{\mathbb{Z}/2\mathbb{Z}}$  with respect to this action. For every prime number p, étale homotopy theory allows us to resconstruct the p-adic completion  $X(\mathbb{C})^{\vee}$ . Moreover, complex conjugation determines an action of  $\mathbb{Z}/2\mathbb{Z}$  on  $X(\mathbb{C})^{\vee}$ . It therefore seems natural to consider the fixed point set

$$(X(\mathbf{C})^{\vee})^{\mathbf{Z}/2\mathbf{Z}}.$$

However, it is important to keep in mind that the *p*-adic completion  $X(\mathbf{C})^{\vee}$  is defined only up to homotopy equivalence. Consequently, the fixed point set  $(X(\mathbf{C})^{\vee})^{\mathbf{Z}/2\mathbf{Z}}$  is not well-defined: given a  $\mathbf{Z}/2\mathbf{Z}$ -equivariant map  $M \to N$  which is a homotopy equivalence of topological spaces, the induced map

$$M^{\mathbf{Z}/2\mathbf{Z}} \rightarrow N^{\mathbf{Z}/2\mathbf{Z}}$$

need not be a homotopy equivalence. (In fact, we can always arrange that the left side is empty.) To rectify the situation, it is convenient to introduce the notion of homotopy fixed points.

Let G be a group acting on a topological space M. The fixed point set  $M^G$  can be identified with space of G-equivariant maps  $\operatorname{Map}_G(*,M)$ ; here \* denotes a point with G acting trivially. As noted above, the functor  $M \mapsto M^G$  need not preserve homotopy equivalences. One explanation for this is that the G-space \* is badly behaved. To get a better functor, we need to replace \* by a better G-space.

**Definition 2.** Let G be a group. We let EG denote a contractible space on which G acts freely, and BG the quotient space EG/G.

The topological space EG always exists, and is unique up to G-equivariant homotopy equivalence.

**Example 3.** Let G be the group  $\mathbb{Z}/2\mathbb{Z}$ . Then we can choose EG to be an infinite dimensional sphere  $S^{\infty}$ , with G acting via the antipodal map. In this case, the quotient BG = EG/G can be identified with the infinite dimensional real projective space  $\mathbb{R}P^{\infty}$ .

**Definition 4.** Let G be a group acting on a topological space M. The homotopy fixed set  $M^{hG}$  is the space of G-equivariant maps  $\operatorname{Map}_G(EG, M)$ .

The homotopy fixed set construction does not suffer the defect of the usual fixed point construction: given a G-equivariant map  $M \to N$  which is a homotopy equivalence, the induced map

$$M^{hG} \to N^{hG}$$

is again a (weak) homotopy equivalence. Moreover, the homotopy fixed point construction is closely related to the usual fixed point construction: every G-fixed point on a space M determines a (constant) G-equivariant map  $EG \to M$ . This construction yields a natural transformation

$$M^G \to M^{hG}$$
.

Let us now return to our algebraic variety X, defined over the field of real numbers  $\mathbb{R}$ . We have a sequence of maps

 $X(\mathbb{R}) \simeq X(\mathbf{C})^{\mathbf{Z}/2\mathbf{Z}} \to X(\mathbf{C})^{h\mathbf{Z}/2\mathbf{Z}} \to (X(\mathbf{C})^{\vee})^{h\mathbf{Z}/2\mathbf{Z}}$ 

Here  $X(\mathbf{C})^{\vee}$  denotes the *p*-adic completion of  $X(\mathbf{C})$ . The left hand side of the above diagram is what we are interested in: the space of  $\mathbb{R}$ -valued points of the algebraic variety X. The right hand side is what we can understand in purely algebraic terms, using étale homotopy theory. It is natural to ask what happens in between: how good an approximation is  $(X(\mathbf{C})^{\vee})^{h\mathbf{Z}/2\mathbf{Z}}$  to  $X(\mathbb{R})$ ? If p is odd, then  $X(\mathbf{C})$  is generally not a very good approximation at all:

**Example 5.** Let X be the projective line  $\mathbb{P}^1$ . Then the space  $X(\mathbf{C})$  is isomorphic to the two-sphere  $S^2$ . If p is an odd prime, then the homotopy groups of the p-adic completion  $X(\mathbf{C})^{\vee}$  are all 2-divisible. In this setting, the homotopy fixed point construction behaves like an exact functor: we have canonical isomorphisms

$$\pi_n(X(\mathbf{C})^{\vee})^{h\mathbf{Z}/2\mathbf{Z}} \simeq (\pi_n X(\mathbf{C})^{\vee})^{\mathbf{Z}/2\mathbf{Z}}.$$

In particular,  $X(\mathbf{C})^{\vee}$ ) $^{h\mathbf{Z}/2\mathbf{Z}}$  is simply connected. However, the actual fixed point set  $X(\mathbf{C})^{\mathbf{Z}/2\mathbf{Z}} \simeq X(\mathbb{R})$  is homeomorphic to a circle, which is definitely not simply connected.

What if p=2? In this case, the algebraic answer  $(X(\mathbf{C})^{\vee})^{h\mathbf{Z}/2\mathbf{Z}}$  turns out to be a reasonably close approximation to the topological space  $X(\mathbb{R})$ . This is a consequence of the following conjecture of Sullivan:

**Conjecture 6** (Sullivan). Let p be a prime number. Let M be a topological space with an action of a finite p-group G. Assume that M is sufficiently nice (for simplicity, a simply connected finite G-CW complex). Then the canonical map

$$M^G \to (M^\vee)^{hG}$$

induces an isomorphism on mod-p cohomology.

This conjecture is interesting (and highly nontrivial) even in the case where the group G acts trivially on the space M. In this case, the homotopy fixed set  $(M^{\vee})^{hG}$  can be identified with the space of maps  $\operatorname{Map}(BG, M^{\vee})$ , and the actual fixed point set can be identified with M itself. In this case, the conjecture is a consequence of the following theorem of Haynes Miller:

**Theorem 7** (Miller). Let M be a finite dimensional CW complex, and let G be a finite group. Then the space of maps Map(BG, M) is homotopy equivalent to M.

The general case of Sullivan's conjecture has also been proven (by Carlsson, Lannes, and Miller). The ultimate goal of this course is to give proofs of Conjecture 6 (and Theorem 7). Let us outline our strategy. For simplicity, let us consider the proof of Theorem 7 in the special case where  $G = V \simeq (\mathbf{Z}/p\mathbf{Z})^n$  is an elementary abelian p-group and M is simply connected. To prove that the mapping space  $\operatorname{Map}(BG, M)$  is equivalent to M, it suffices to prove the result after completing M at each prime number q. The essential case is that in which p = q. In this case, the essence of the problem is to compute the cohomology ring

$$H^*(Map(BG, M^{\vee}); \mathbf{Z}/p\mathbf{Z}),$$

and to show that it agrees with the cohomology ring

$$H^*(M^{\vee}; \mathbf{Z}/p\mathbf{Z}) \simeq H^*(M, \mathbf{Z}/p\mathbf{Z}).$$

This raises the question of whether it is possible to compute the cohomology of the mapping space

$$H^*(Map(BV, Y); \mathbf{Z}/p\mathbf{Z}).$$

Of course, we would expect the answer to be at least as complicated as the cohomology of Y (since, in the case where V is the trivial group, we recover precisely the cohomology of Y). So the best we might hope for is some recipe which will allow us to recover  $H^*(Map(BV,Y); \mathbf{Z}/p\mathbf{Z})$  from  $H^*(Y; \mathbf{Z}/p\mathbf{Z})$ .

It turns out that there is such a recipe. However, it requires a very thorough knowledge of the cohomology groups  $H^*(Y; \mathbf{Z}/p\mathbf{Z})$ . To be precise, we need to introduce the notion of a *cohomology operation*.

**Definition 8.** Fix a nonnegative integer k. A stable cohomology operation (of degree k) is a collection of maps

$$H^m(X, Y; \mathbf{Z}/p\mathbf{Z}) \to H^{m+k}(X, Y; \mathbf{Z}/p\mathbf{Z}),$$

defined for every pair of spaces (X,Y) and every integer m. We require that these operations depend functorially on the pair (X,Y), and behave well with respect the boundary maps in long exact sequences.

The collection of stable cohomology operations forms a graded ring, where multiplication is given by composition. This ring is called the mod-p Steenrod algebra and is usually denoted by  $\mathcal{A}$ . If Y is any topological space, then the cohomology  $H^*(Y; \mathbf{Z}/p\mathbf{Z})$  has the structure of a module over  $\mathcal{A}$ . In fact, a bit more is true:  $H^*(Y; \mathbf{Z}/p\mathbf{Z})$  is an unstable module over the Steenrod algebra (we will discuss this condition later). The collection of unstable modules over the Steenrod algebra can be organized into a category  $\mathcal{U}$ .

**Theorem 9.** [Lannes] Let p be a prime number, and let V be an elementary abelian p-group. There exists a functor  $T_V : \mathcal{U} \to \mathcal{U}$  with many pleasant properties:

- (1) The functor  $T_V$  is exact.
- (2) The functor  $T_V$  commutes with tensor products.
- (3) The functor  $T_V$  commutes with suspension.
- (4) For every topological space Y, there is a canonical map

$$T_V \operatorname{H}^*(Y; \mathbf{Z}/p\mathbf{Z}) \to \operatorname{H}^*(\operatorname{Map}(BV, Y), \mathbf{Z}/p\mathbf{Z}).$$

Moreover, this map is an isomorphism if Y is a sufficiently nice p-complete space.

The functor  $T_V$  is called Lannes' T-functor. Because of its many good properties, Lannes' T-functor is an extremely useful tool. In particular, it can be used to give very elegant proofs of Conjecture 6 and Theorem 7. We now sketch how to use Theorem 9 to prove THeorem 7 in a special case. Assume that M is the p-adic completion of a simply connected finite CW-complex. We wish to show that the canonical map

$$M \to \operatorname{Map}(BV, M)$$

induces an equivalence on mod-p cohomology. In view of Theorem 9, it will suffice to show that the canonical map

$$T_V \operatorname{H}^*(M; \mathbf{Z}/p\mathbf{Z}) \to \operatorname{H}^*(M; \mathbf{Z}/p\mathbf{Z})$$

is an isomorphism. This is purely an assertion about the object  $H^*(M; \mathbf{Z}/p\mathbf{Z}) \in \mathcal{U}$ . By assumption,  $H^*(M; \mathbf{Z}/p\mathbf{Z})$  is finite dimensional, and therefore admits a filtration by one-dimensional objects of  $\mathcal{U}$ . Each one dimensional object is a suspension of the trivial module  $H^*(*; \mathbf{Z}/p\mathbf{Z}) \in \mathcal{U}$ . Since  $T_V$  is exact and commutes with suspensions, we can reduce to the case where M is a single point, where the result is obvious.

Let us now conclude by giving a rough outline of what we will cover in this course (a more detailed outline, which may turn out to be grossly inaccurate, is given in the syllabus). We will begin by giving a construction of the Steenrod algebra  $\mathcal{A}$ , and establishing its basic properties. Though our ultimate goal is to

prove Sullivan's conjecture, we will take the scenic route: for example, we will begin not with the classical Steenrod algebra but with the "generalized Steenrod algebra" of May, which acts on the homotopy groups of any  $E_{\infty}$ -algebra over the field  $\mathbf{Z}/p\mathbf{Z}$ . Once we understand the Steenrod algebra well enough, we will proceed to study its category  $\mathcal{U}$  of unstable modules, and introduce the functor  $T_V$ . To establish the basic properties of  $T_V$  (such as exactness), we will need to have a good understanding of the structure of the category  $\mathcal{U}$ ; in particular, we will make a thorough study of injective objects of  $\mathcal{U}$ . Once we are done, we will turn to the proof of Theorem 9. It turns out that the hypothesis that X be "sufficiently nice" can be dropped if we work in the setting of p-profinite homotopy theory. After explaining these ideas, we apply them to give proofs of Conjecture 6 (in the p-profinite setting) and Theorem 7 (in the setting of classical homotopy theory). If time permits, we will then go on to study the algebraic structure of the category  $\mathcal{U}$  in more detail.

Warning 10. The mod-p Steenrod algebra  $\mathcal{A}$  has a somewhat different structure at the prime 2 than at odd primes. It is often difficult to give uniform arguments which apply at all primes simultaneously. To simplify the exposition, we will assume that the prime p is equal to 2 whenever it is convenient to do so. Generally speaking, we will do all calculations at the prime 2, though more conceptual arguments will usually work for any prime p.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Steenrod Operations (Lecture 2)

The objective of today's lecture is to introduce the Steenrod operations and establish some of their basic properties. We will work over the finite field  $\mathbf{F}_2 \simeq \mathbf{Z}/2\mathbf{Z}$  with two elements.

To this end, we will study the homotopy theory of cochain complexes

$$\dots \to V^{n-1} \stackrel{d_{n-1}}{\to} V^n \stackrel{d_n}{\to} V^{n+1} \to \dots$$

in the category of  $\mathbf{F}_2$ -vector spaces. We will refer to these objects simply as *complexes*. To each complex V we can associate cohomology groups

$$H^n V = \ker(d_n) / \operatorname{Im}(d_{n-1}).$$

Remark 1. It is possible to take a more sophisticated point of view: we can identify cochain complexes V over the field  $\mathbf{F}_2$  with module spectra over  $\mathbf{F}_2$ . The cohomology groups  $\mathrm{H}^n(V)$  should then be viewed as the homotopy groups  $\pi_{-n}$  of the corresponding spectra.

Given a pair of  $\mathbf{F}_2$ -module spectra V and W, we can form their tensor product  $V \otimes W$ . This is given by the usual tensor product of complexes of vector spaces:

$$(V \otimes W)^n = \bigoplus_{n=n'+n''} V^{n'} \otimes W^{n''},$$

with the usual differential (note that, since we are working over the field  $\mathbf{F}_2$ , we do not even have to worry about signs). In particular, we can form the tensor powers

$$V^{\otimes n} = V \otimes V \otimes \ldots \otimes V$$

of a fixed  $\mathbf{F}_2$ -module spectrum. The tensor power  $V^{\otimes n}$  inherits a natural action of the symmetric group  $\Sigma_n$ , by permuting the tensor factors.

One of the most important examples of an  $\mathbf{F}_2$ -module spectrum is the cochain complex

$$C^*(X; \mathbf{F}_2)$$

of a topological space X. The cohomology groups of this  $\mathbf{F}_2$ -module spectrum are simply the cohomology groups of X. The cohomology  $\mathrm{H}^*(X; \mathbf{F}_2)$  has the structure of a graded commutative ring. The multiplication on  $\mathrm{H}^*(X; \mathbf{F}_2)$  arises from a multiplication which exists on the cochain complex  $C^*(X; \mathbf{F}_2)$ . Namely, we can consider the composition

$$C^*(X; \mathbf{F}_2) \otimes C^*(X; \mathbf{F}_2) \to C^*(X \times X; \mathbf{F}_2) \to C^*(X; \mathbf{F}_2).$$

Here the first map is the classical Alexander-Whitney morphism, and the second is given by pullback along the diagonal inclusion  $X \to X \times X$ . The Alexander-Whitney map is *not* compatible with the action of the symmetric group  $\Sigma_2$  on the two sides. Consequently, the resulting multiplication

$$m: C^*(X; \mathbf{F}_2) \otimes C^*(X; \mathbf{F}_2) \to C^*(X; \mathbf{F}_2)$$

is not commutative until passing to homotopy. The failure of m to be strictly commutative turns out to be a very interesting phenomenon, which is responsible for the existence of Steenrod operations.

In the above situation, the multiplication m is not commutative. However, it does induce a commutative multiplication after passing to cohomology. In fact, more is true: the map m satisfies a symmetry condition up to coherent homotopy. The following definitions allow us to make this idea precise:

**Definition 2.** Let V be an  $\mathbf{F}_2$ -module spectrum and  $n \geq 0$  a nonnegative integer. The *nth extended power* of V is given by the homotopy coinvariants

$$V_{h\Sigma}^{\otimes n}$$

This is a complex which we will denote by  $D_n(V)$ .

**Remark 3.** In concrete terms,  $D_n(V)$  may be computed in the following way. Let M denote the vector space  $\mathbf{F}_2$ , with the trivial action of  $\Sigma_n$ . Choose a resolution

$$\dots \to P^{-1} \to P^0 \to M$$

by free  $\mathbf{F}_2[\Sigma_n]$ -modules. We let  $E\Sigma_n$  denote the complex  $P^{\bullet}$ . (We can think of  $E\Sigma_n$  as a contractible complex with a free action of  $\Sigma_n$ .) The extended power  $D_n(V)$  of a complex V can then be identified with the ordinary coinvariants

$$(V^{\otimes n} \otimes E\Sigma_n)_{\Sigma_n}$$
.

**Definition 4.** Let V be a complex. A symmetric multiplication on V is a map

$$D_2(V) \to V$$
.

**Example 5.** If X is any topological space, then the cochain complex  $C^*(X; \mathbf{F}_2)$  can be endowed with a symmetric multiplication. If X is equipped with a base point \*, then the reduced cochain complex  $C^*(X, *; \mathbf{F}_2)$  also inherits a symmetric multiplication.

**Example 6.** Let X be an infinite loop space. Then the chain complex  $C_*(X; \mathbf{F}_2)$  can be endowed with a symmetric multiplication.

Examples 5 and 6 are really special cases of the following:

**Example 7.** Let A be an  $E_{\infty}$ -algebra over the field  $\mathbf{F}_2$ . Then A has an underlying  $\mathbf{F}_2$ -module spectrum, which is equipped with a symmetric multiplication.

Our goal in this lecture is to study the consequences of the existence of a symmetric multiplication on a complex V.

**Notation 8.** Let n be an integer. We let  $\mathbf{F}_2[-n]$  denote the complex which consists of a 1-dimensional vector space in cohomological degree n, and zero elsewhere. Let  $e_n$  denote a generator for the  $\mathbf{F}_2$ -vector space  $\mathbf{H}^n \mathbf{F}_2[-n]$ , so we have isomorphisms

$$\mathrm{H}^k \, \mathbf{F}_2[-n] \simeq \begin{cases} \mathbf{F}_2 e_n & \mathrm{if} \ k=n \\ 0 & \mathrm{otherwise}. \end{cases}$$

Our first goal is to describe the extended squares of complexes of the form  $\mathbf{F}_2[-n]$ . This is easy: we observe that  $\mathbf{F}_2[-n]^{\otimes 2}$  is isomorphic to  $\mathbf{F}_2[-2n]$ , with the symmetric group  $\Sigma_2$  acting trivially (since we are working in characteristic 2, there are no signs to worry about). Consequently, we can identify  $D_2(\mathbf{F}_2[-n])$  with the tensor product

$$\mathbf{F}_2[-2n] \otimes (E\Sigma_2)_{\Sigma_2}$$
.

The second tensor factor can be identified with the chain complex of the space  $B\Sigma_2 \simeq \mathbf{R}P^{\infty}$ . Consequently, we get canonical isomorphisms

$$\mathrm{H}^k(D_2(\mathbf{F}_2[-n]) \simeq \mathrm{H}_{2n-k}(B\Sigma_2;\mathbf{F}_2)e_{2n}.$$

We now recall the structure of the homology and cohomology of the space  $B\Sigma_2 \simeq \mathbf{R}P^{\infty}$ . There is a (unique) isomorphism

$$H^*(\mathbf{R}P^\infty; \mathbf{F}_2) \simeq \mathbf{F}_2[t],$$

where the polynomial generator t lies in  $H^1(\mathbf{R}P^{\infty}; \mathbf{F}_2)$ . We have a dual description of the homology  $H_*(\mathbf{R}P^{\infty}; \mathbf{F}_2)$ : this is just a one-dimensional vector space in each degree m, with a unique generator which we will denote by  $x_m$ .

**Definition 9.** Let V be a complex, and let  $v \in \mathbb{H}^n V$ , so that v determines a homotopy class of maps

$$\eta: \mathbf{F}_2[-n] \to V.$$

For  $i \leq n$ , we let

$$\overline{\operatorname{Sq}}^i(v) \in \operatorname{H}^{n+i} D_2(V)$$

denote the image of

$$x_{n-i} \otimes e_{2n} \in \mathcal{H}_{n-i}(\mathbf{R}P^{\infty}; \mathbf{F}_2)e_{2n} \simeq \mathcal{H}^{n+i} D_2(\mathbf{F}_2[n])$$

under the induced map

$$D_2(\mathbf{F}_2[-n]) \stackrel{D_2(\eta)}{\to} D_2(V).$$

By convention, we will agree that  $\overline{\mathrm{Sq}}^i(v) = 0$  for i > n.

If V is equipped with a symmetric multiplication  $D_2(V) \to V$ , we let  $\operatorname{Sq}^i(v)$  denote the image of  $\operatorname{\overline{Sq}}^i(v)$  under the induced map

$$H^{n+i} D_2(V) \to H^{n+i} V.$$

The operations  $\operatorname{Sq}^i:\operatorname{H}^*V\to\operatorname{H}^{*+i}V$  are called the *Steenrod operations*, or *Steenrod squares*.

**Example 10.** Let V be an  $\mathbf{F}_2$ -module spectrum equipped with a symmetric multiplication, and let  $v \in \mathbf{H}^n V$ . Then  $\operatorname{Sq}^n(v) \in \mathbf{H}^{2n} V$  is simply the image of  $v \otimes v$  under the composite map

$$V \otimes V \to D_2(V) \to V$$
.

In other words,  $\operatorname{Sq}^n$  acts on  $\operatorname{H}^n V$  by simply "squaring" the elements with respect to the multiplication on V. This is why the operations  $\operatorname{Sq}^i$  are called "Steenrod squares".

**Example 11.** Let X be a topological space, and let  $V = C^*(X; \mathbf{F}_2)$  be the cochain complex of X, equipped with its usual symmetric multiplication. Then Definition 9 yields operations

$$\operatorname{Sq}^{i}: \operatorname{H}^{n}(X; \mathbf{F}_{2}) \to \operatorname{H}^{n+i}(X; \mathbf{F}_{2}).$$

These are the usual Steenrod operations.

**Remark 12.** The operations  $v \mapsto \overline{\operatorname{Sq}}^i v$  completely account for the cohomology groups of any extended square  $D_2(V)$ . More precisely, let us suppose that V is an  $\mathbf{F}_2$ -module spectrum, and that  $\{v_i\}_{i\in I}$  is an ordered basis for  $\pi_*V$ , where  $v_i\in H^{n_i}V$ . Then the collection

$$\{v_i v_j\}_{i < j} \cup \{\operatorname{Sq}^n v_i\}_{n \le n_i}$$

is a basis for  $\pi_*D_2(V)$ . The proof of this is easy. Using the fact that  $D_2$  commutes with filtered colimits, we can reduce to the case where only finitely many generators are involved. We then work by induction, using the formula

$$D_2(V \oplus W) \simeq (V \oplus W)_{h\Sigma_2}^{\otimes 2} \simeq V_{h\Sigma_2}^{\otimes 2} \oplus (V \otimes W) \oplus W_{h\Sigma_2}^{\otimes 2}$$

to reduce to the case of a single basis vector. The result is then obvious.

**Proposition 13.** The Steenrod squares are additive operations. Let V be a complex, and let  $v, v' \in H^n V$ . Then, for each integer k, we have

$$\overline{\operatorname{Sq}}^k(v+v') = \overline{\operatorname{Sq}}^k(v) + \overline{\operatorname{Sq}}^k(v') \in \operatorname{H}^{n+k}D_2(V).$$

In particular, if V is equipped with a symmetric multiplication, we have

$$\operatorname{Sq}^{k}(v + v') = \operatorname{Sq}^{k}(v) + \operatorname{Sq}^{k}(v') \in \operatorname{H}^{n+k} V.$$

*Proof.* If k > n, then both sides are zero and there is nothing to prove. If k = n, then

$$\overline{\operatorname{Sq}}^{k}(v+v') = (v+v')^{2} = \overline{\operatorname{Sq}}^{k}(v) + \overline{\operatorname{Sq}}^{k}(v') + (vv'+v'v).$$

Since the multiplication map

$$V \otimes V \to D_2(V)$$

is commutative on the level of homotopy, we have vv' + v'v = 2vv' = 0.

Now suppose that k < n. By functoriality, it will suffice to treat the universal case where  $V \simeq \mathbf{F}[-n] \oplus \mathbf{F}[-n]$ . Using Remark 12, we observe that the canonical map

$$\operatorname{H}^m D_2(V) \to \operatorname{H}^m D_2(\mathbf{F}_2[-n]) \times \operatorname{H}^m D_2(\mathbf{F}_2[-n])$$

is injective for m < 2n. We may therefore reduce to the case where either v or v' vanishes, in which case the result is obvious.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Topics in Algebraic Topology (18.917): Lecture 3

In this lecture we will establish some more of the basic properties of Steenrod operations. More precisely, we will show that the Steenrod squares are *stable* operations, and prove the Cartan formula which describes the interaction between Steenrod operations and multiplication in the cohomology of a space X. As before, we work in the setting of cochain complexes over the finite field  $\mathbf{F}_2 = \mathbf{Z}/2\mathbf{Z}$  with two elements.

Let  $\Omega$  denote the loop functor on complexes, so that we have canonical isomorphisms

$$(\Omega V)^n \simeq V^{n-1}$$

$$H^n(\Omega V) \simeq H^{n-1}(V).$$

Since the extended square functor  $V \mapsto D_2(V)$  preserves acyclic objects, there is a canonical map

$$D_2(\Omega V) \stackrel{\phi}{\to} \Omega D_2(V)$$

for any complex V (see below for an explicit construction of this map).

The stability of the Steenrod operations is a consequence of the following result:

**Proposition 1.** Let W be a complex and k an integer. Then the diagram

$$H^{*}(\Omega W) \xrightarrow{\sim} H^{*-1}(W)$$

$$\downarrow^{\overline{\operatorname{Sq}}^{k}} \qquad \qquad \downarrow^{\overline{\operatorname{Sq}}^{k}}$$

$$H^{*+k}(D_{2}(\Omega W)) \xrightarrow{\sim} H^{*+k}(\Omega(D_{2}W)) \xrightarrow{\sim} H^{*+k-1}(D_{2}(W))$$

is commutative.

Proof. Let  $V = \Omega W$ . Fix a class v in  $\mathrm{H}^n(V)$ , and let w denote the image of v in  $\mathrm{H}^{n-1}(W)$ . Without loss of generality, we may suppose that  $V \simeq \mathbf{F}_2[-n]$  is generated by v, so that  $W \simeq \mathbf{F}_2[1-n]$  is generated by w. We observe that  $\mathrm{H}^{n+k-1} D_2(W)$  vanishes for  $k \geq n$ , so that the result is automatic. Let us therefore assume that k < n. In this case,  $\mathrm{H}^{n+k-1} D_2 W$  and  $\mathrm{H}^{n+k} D_2 V$  are 1-dimensional vector spaces, generated by  $\overline{\mathrm{Sq}}^k(w)$  and  $\overline{\mathrm{Sq}}^k(v)$ , respectively. It will suffice to show that the map

$$H^m D_2(V) \to H^{m-1} D_2(W)$$

is an isomorphism for m < 2n.

Let U denote the complex

$$\dots \to 0 \to \mathbf{F}_2 w \xrightarrow{\sim} \mathbf{F}_2 v \to 0 \to \dots$$

so we have a homotopy pullback diagram

$$V \longrightarrow U$$

$$\downarrow \qquad \qquad \downarrow$$

$$0 \longrightarrow W.$$

We obtain an associated diagram

$$V^{\otimes 2} \longrightarrow U^{\otimes 2}$$

$$\downarrow \qquad \qquad \downarrow f$$

$$0 \longrightarrow W^{\otimes 2}.$$

The complex  $\Omega W^{\otimes 2}$  can be identified with the kernel of the map f, which is given by the two term complex

$$\dots \to 0 \to \mathbf{F}_2 v^2 \to \mathbf{F}_2 vw \oplus \mathbf{F}_2 wv \to 0 \to \dots$$

We therefore obtain a fiber sequence

$$V^{\otimes 2} \to \Omega W^{\otimes 2} \to \mathbf{F}_2^2[-2n+1]$$

of complexes with an action of the group  $\Sigma_2$ . The operation of taking homotopy coinvariants is exact, so we obtain a fiber sequence

$$D_2(V) \rightarrow \Omega D_2(W) \rightarrow \mathbf{F}_2[-2n+1].$$

The associated long exact sequence implies that  $\operatorname{H}^m D_2(V) \simeq \operatorname{H}^{m-1} D_2(W)$  for m < 2n, as desired.

To apply Proposition 1, we wish to study the relationship between symmetric multiplications and suspension. If V is a complex equipped with a symmetric multiplication  $m: D_2(V) \to V$ , then  $\Omega V$  inherits a symmetric multiplication, given by the composition

$$D_2(\Omega V) \to \Omega D_2(V) \to \Omega V.$$

By construction, we have a commutative diagram

$$H^{*+1}D_2(\Omega V) \longrightarrow H^{*+1}(\Omega V)$$

$$\downarrow^{\phi} \qquad \qquad \downarrow^{\sim}$$

$$H^*D_2(V) \longrightarrow H^*V$$

where  $\phi$  is the map appearing in Proposition 1. We immediately deduce the following:

Corollary 2. Let V be a complex equipped with a symmetric multiplication. Then  $\Omega V$  inherits a symmetric multiplication. Moreover, the canonical isomorphism

$$H^* V \simeq H^{*+1}(\Omega V)$$

commutes with the Steenrod operations  $Sq^k$ .

Corollary 3. Let X be a pointed topological space, and  $\Sigma X$  its suspension. Then the canonical isomorphism

$$\mathrm{H}^*(X; \mathbf{F}_2) \simeq \mathrm{H}^{*+1}(\Sigma X; \mathbf{F}_2)$$

commutes with the action of the Steenrod operations  $Sq^k$ .

We can apply Corollary 3 to compute the Steenrod operations in some simple cases:

**Example 4.** Let  $v \in H^n_{red}(S^n; \mathbf{F}_2)$  be the generator for the top cohomology of the *n*-sphere. Then

$$\operatorname{Sq}^{k}(v) = \begin{cases} v & \text{if } k = 0\\ 0 & \text{otherwise.} \end{cases}.$$

To prove this, use Corollary 3 to reduce to the case n = 0. In this case, Example ?? shows that the operation  $\operatorname{Sq}^0$  is the identity on  $\operatorname{H}^0_{\operatorname{red}}(S^0; \mathbf{F}_2)$ .

Corollary 5. Let X be a topological space, and let  $v \in H^n(X; \mathbf{F}_2)$ . Then

$$\operatorname{Sq}^{k}(x) = \begin{cases} x & \text{if } k = 0\\ 0 & \text{if } k < 0. \end{cases}$$

*Proof.* Recall that the cohomology group  $\operatorname{H}^n(X; \mathbf{F}_2)$  can be identified with the set of homotopy classes of maps from X into an Eilenberg-MacLane space  $K(\mathbf{F}_2, n)$ . More precisely, there exists a tautological cohomology class

$$\chi \in \mathrm{H}^n(K(\mathbf{F}_2,n);\mathbf{F}_2)$$

such that pulling back  $\chi$  induces a bijection

$$\pi_0 \operatorname{Map}(X, K(\mathbf{F}_2, n)) \to \operatorname{H}^n(X; \mathbf{F}_2)$$

for every CW complex X. By general nonsense, we can reduce to the case  $X = K(\mathbf{F}_2, n)$  and where  $x = \chi$ . Let  $v \in \mathrm{H}^n(S^n; \mathbf{F}_2)$  be the cohomology class described in Example 4. Then v induces a map

$$f: S^n \to K(\mathbf{F}_2, n).$$

The induced map

$$H^{n+k}(K(\mathbf{F}_2, n); \mathbf{F}_2) \to H^{n+k}(S^n; \mathbf{F}_2)$$

is injective (in fact, bijective) for  $k \leq 0$ . We may therefore reduce to the case where  $X = S^n$  and x = v. The desired result now follows from Example 4.

Warning 6. The negative Steenrod operations  $\{Sq^n\}_{n<0}$  act trivially on the cohomology of spaces, but are nontrivial in other examples. Similarly,  $Sq^0$  acts by the identity on the cohomology of spaces, but not in general.

We now turn to the second main topic of this lecture: the Cartan formula. We begin by studying the interaction between the extended square functor  $D_2$  and tensor products. Let V and W be complexes. We have equivalences

$$D_2(V) \otimes D_2(W) \simeq V_{h\Sigma_2}^{\otimes 2} \otimes W_{h\Sigma_2}^{\otimes 2} \simeq (V \otimes W)_{h(\Sigma_2 \times \Sigma_2)}^{\otimes 2}$$
$$D_2(V \otimes W) \simeq (V \otimes W)_{h\Sigma_2}^{\otimes 2}.$$

There is a canonical map

$$(V \otimes W)_{h\Sigma_2}^{\otimes 2} \to (V \otimes W)_{h(\Sigma_2 \times \Sigma_2)}^{\otimes 2},$$

given by the diagonal embedding of  $\Sigma_2$  into  $\Sigma_2 \times \Sigma_2$ . This induces a map  $\psi : D_2(V \otimes W) \to D_2(V) \otimes D_2(W)$ .

**Proposition 7.** Let V and W be complexes. Let  $v \in H^m V$ ,  $w \in H^n W$ , so that we can form a class  $v \otimes w \in H^{m+n}(V \otimes W)$ . For every integer k, we have an equality

$$\psi \overline{\operatorname{Sq}}^{k}(v \otimes w) = \sum_{k=k'+k''} \overline{\operatorname{Sq}}^{k'}(v) \otimes \overline{\operatorname{Sq}}^{k''}(w)$$

in the cohomology group  $H^{m+n+k}(D_2(V) \otimes D_2(W))$ .

**Remark 8.** The sum in this expression is well-defined, since  $\overline{\operatorname{Sq}}^{k'}(v) \otimes \overline{\operatorname{Sq}}^{k''}(w)$  vanishes for k' > m or k'' > n. There are only finitely many terms which do not satisfy either condition.

*Proof.* If k > m + n, then the result is obvious since both sides vanish. Let us therefore assume that k = m + n - i, where  $i \ge 0$ . We can rewrite the equation

$$\psi \, \overline{\operatorname{Sq}}^{m+n-i}(v \otimes w) = \Sigma_{i=i'+i''} \, \overline{\operatorname{Sq}}^{m-i'}(v) \otimes \overline{\operatorname{Sq}}^{n-i''}(w),$$

where the sum is taken over  $i', i'' \geq 0$ .

Without loss of generality, we may assume that  $V = \mathbf{F}_2[-m]$  and  $W = \mathbf{F}_2[-n]$ . In this case, we have canonical isomorphisms

$$H^*(D_2(V)) \simeq H_{2m-*}(B\Sigma_2; \mathbf{F}_2) e_{2m}$$

$$H^*(D_2(W)) \simeq H_{2n-*}(B\Sigma_2; \mathbf{F}_2) e_{2n}.$$

$$H^*(D_2(V \otimes W)) \simeq H_{2m+2n-*}(B\Sigma_2; \mathbf{F}_2) e_{2m+2n}.$$

For each  $j \ge 0$ , let  $x_j$  denote a generator of  $H_j(B\Sigma_2; \mathbf{F}_2)$ . Under the identifications above, we have

$$\overline{\operatorname{Sq}}^{m+n-i}(v \otimes w) \mapsto x_i e_{2m+2n}$$

$$\overline{\operatorname{Sq}}^{m-i'}(v) \mapsto x_{i'} e_{2m}$$

$$\overline{\operatorname{Sq}}^{n-i''}(w) \mapsto x_{i''} e_{2n}.$$

Moreover, the map  $\psi$  simply corresponds to the comultiplication

$$\Psi: \mathrm{H}_*(B\Sigma_2; \mathbf{F}_2) \to \mathrm{H}_*(B\Sigma_2; \mathbf{F}_2) \otimes \mathrm{H}_*(B\Sigma_2; \mathbf{F}_2)$$

on the homology of the space  $B\Sigma_2$ . The cohomology ring  $H^*(B\Sigma_2; \mathbf{F}_2) \simeq H^*(\mathbf{R}P^{\infty}; \mathbf{F}_2)$  is simply isomorphic to a polynomial ring  $\mathbf{F}_2[t]$  having a basis  $\{t^j\}_{j\geq 0}$ . The corresponding comultiplication is given in the dual basis  $\{x_i\}_{i\geq 0}$  by the formula

$$x_i \mapsto \sum_{i'+i''} x_{i'} \otimes x_{i''}.$$

We now simply compute

$$\overline{\operatorname{Sq}}^{m+n-i}(v\otimes w) = x_i e_{2m+2n} \mapsto \sum_{i=i'+i''} (x_{i'} e_{2m}) \otimes (x_{i''} e_{2n}) = \overline{\operatorname{Sq}}^{m-i'}(v) \otimes \overline{\operatorname{Sq}}^{n-i''}(w)$$

to obtain the desired formula.

For any complex V equipped with a symmetric multiplication  $m: D_2(V) \to V$ , we can form a diagram

$$D_{2}(V \otimes V) \xrightarrow{\hspace{1cm}} D_{2}(D_{2}(V)) \xrightarrow{D_{2}(m)} D_{2}(V)$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad$$

If m is good (see Lecture 4), then this diagram commutes up to homotopy. Passing to cohomology and applying Proposition 7, we deduce the following:

**Corollary 9.** Let V be a complex equipped with a good symmetric multiplication. Then, for every pair of elements  $v, w \in H^*(V)$ , the Cartan formula holds:

$$\operatorname{Sq}^{k}(vw) = \sum_{k=k'+k''} \operatorname{Sq}^{k'}(v) \operatorname{Sq}^{k''}(w).$$

Corollary 10. Let X be a topological space, and let  $x, y \in H^*(X; \mathbf{F}_2)$ . Then, for each  $n \geq 0$ ,

$$\operatorname{Sq}^{n}(xy) = \sum_{n=n'+n''} \operatorname{Sq}^{n'}(x) \operatorname{Sq}^{n''}(y).$$

It is convenient to summarize Corollary 10 by asserting that the total Steenrod square  $x \mapsto \sum_{n\geq 0} \operatorname{Sq}^n(x)$  is a multiplicative operation.

We can now compute the action of the Steenrod algebra in a situation where they are definitely nontrivial:

Corollary 11. Let  $H^*(\mathbf{R}P^{\infty}; \mathbf{F}_2) = \mathbf{F}_2[t]$ . Then the action of the Steenrod algebra on  $\mathbf{F}_2[t]$  can be described by the following formula:

$$\operatorname{Sq}^k t^n = \binom{n}{k} t^{n+k}.$$

Here  $\binom{n}{k}$  denotes the binomial coefficient

$$\frac{n!}{k!(n-k)!}$$

if  $0 \le k \le n$ ; by convention we will agree that  $\binom{n}{k}$  vanishes otherwise.

*Proof.* Let Sq denote the operation  $x \mapsto \sum_{n\geq 0} \operatorname{Sq}^n(x)$ . Since t has degree 1,  $\operatorname{Sq}^n(t)$  vanishes for n>1 and is equal to  $t^2$  when t=1. It follows that  $\operatorname{Sq}(t)=\operatorname{Sq}^0(t)+\operatorname{Sq}^1(t)=t+t^2$ . Since the operation Sq is multiplicative, we have

$$Sq(t^n) = (t + t^2)^n = \sum_{0 \le k \le n} \binom{n}{k} t^{n+k}.$$

The desired result now follows by extracting individual coefficients.

**Warning 12.** Our convention that  $\binom{n}{k}$  vanishes for n < 0 is somewhat nonstandard. For example, it has the consequence that  $\binom{n}{k}$  is *not* a polynomial function of n, even for k = 1.

The cohomology ring  $H^*(\mathbf{R}P^{\infty}; \mathbf{F}_2)$  is a very important example which will play a large role in the later part of this course.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Adem Relations (Lecture 4)

**Remark 1.** Throughout this lecture, we will work over the field  $\mathbf{F}_2$  with two elements. If X is a topological space, we will simply write  $H_*(X)$  and  $H^*(X)$  to denote the homology and cohomology of X with coefficients in  $\mathbf{F}_2$ . Similarly, we let  $C_*(X)$  and  $C^*(X)$  denote the chain and cochain complexes of X, respectively.

Our goal in this lecture is to prove the Adem relations. We begin by describing our context. For any chain complex V, we have defined the nth extended power  $D_n(V) = V_{h\Sigma_n}^{\otimes n}$ . We now observe that there is a canonical map

$$\phi: D_m(D_n(V)) \to D_{mn}(V).$$

More concretely, the left hand side is given by

$$(V_{h\Sigma_n}^{\otimes n})_{h\Sigma_m}^{\otimes m} \simeq V_{hG}^{\otimes mn},$$

where G denotes the wreath product  $\Sigma_n^m \rtimes \Sigma_m$ . The right hand side is simply given by  $V_{h\Sigma_{mn}}^{\otimes mn}$ . The map  $\phi$  is induced by the inclusion of finite groups  $G \hookrightarrow \Sigma_{mn}$ .

**Definition 2.** Let V be a complex equipped with a symmetric multiplication  $m: D_2(V) \to V$ . We will say that m is good if there exists a map  $m': D_4(V) \to V$  such that the diagram

$$D_2(D_2(V)) \xrightarrow{D_2(m)} D_2(V)$$

$$\downarrow^{\phi} \qquad \qquad \downarrow^{m}$$

$$D_4(V) \xrightarrow{m'} V.$$

**Example 3.** Let V be an  $E_{\infty}$ -algebra over the field  $\mathbf{F}_2$ . Then the symmetric multiplication on V is good. In particular, if X is a topological space then the cochain complex  $C^*(X)$  has a good symmetric multiplication.

**Notation 4.** Let i and j be integers. We let

$$(i,j) = \begin{cases} \binom{i+j}{i} = \binom{i+j}{j} = \frac{(i+j)!}{i!j!} & \text{if } i,j \geq 0 \\ 0 & \text{otherwise.} \end{cases}.$$

We will regard (i, j) as taking values in the finite field  $\mathbf{F}_2$ . We observe that if  $i, j \geq 0$ , then (i, j) is equal to 1 if the sum of i and j in base 2 can be computed "without carrying", and equal to zero otherwise.

Our goal in this lecture is to prove the following:

**Proposition 5** (Adem Relations). Let V be a complex equipped with a good symmetric multiplication, and let  $v \in H^n(V)$ . For any pair of integers a < 2b, we have

$$\operatorname{Sq}^{a} \operatorname{Sq}^{b}(v) = \sum_{k} (2k - a, b - k - 1) \operatorname{Sq}^{b+k} \operatorname{Sq}^{a-k}(v).$$

Actually, we will not give a complete proof in this lecture. We will instead show how to reduce the statement of Proposition 5 from a calculation in the homology of groups (Lemma ??). This calculation will be carried out in the next lecture.

**Remark 6.** The sum appearing in Proposition 5 is actually finite, since (2k - a, b - k - 1) vanishes unless  $a \le 2k < 2b$ .

**Definition 7.** Let  $\mathbf{F}_2\{\ldots, \operatorname{Sq}^{-1}, \operatorname{Sq}^0, \operatorname{Sq}^1, \ldots\}$  denote the free associative  $\mathbf{F}_2$ -algebra generated by the symbols  $\{\operatorname{Sq}^i\}_{i\in\mathbf{Z}}$ . The *big Steenrod algebra*  $\mathcal{A}^{\operatorname{Big}}$  is defined to be the quotient of  $\mathbf{F}_2\{\ldots, \operatorname{Sq}^{-1}, \operatorname{Sq}^0, \operatorname{Sq}^1, \ldots\}$  by imposing the Adem relations

$$\operatorname{Sq}^{a} \operatorname{Sq}^{b} = \sum_{b} (2k - a, b - k - 1) \operatorname{Sq}^{b+k} \operatorname{Sq}^{a-k}.$$

for every a < 2b.

We observe that  $\mathcal{A}^{\text{Big}}$  the structure of a graded algebra, where each generator  $\operatorname{Sq}^i$  is given degree i. A module over the big Steenrod algebra  $\mathcal{A}^{\text{Big}}$  is a graded vector space V over the field  $\mathbf{F}_2$ , equipped with an action  $\mathcal{A}^{\text{Big}} \otimes V \to V$  which respects the grading: if  $v \in V$  is homogeneous of degree n, then  $\operatorname{Sq}^k(v)$  is homogeneous of degree n + k. We will say that V is unstable if, whenever  $\operatorname{Sq}^k(v)$  vanishes whenever v is homogeneous of degree k.

**Example 8.** Let V be a complex equipped with a good symmetric multiplication. Then Proposition 5 implies that the cohomology  $H^*(V)$  has the structure of a unstable  $\mathcal{A}^{\text{Big}}$ -module.

**Definition 9.** The Steenrod algebra  $\mathcal{A}$  is defined to be the quotient of  $\mathcal{A}^{\text{Big}}$  by the (two-sided) ideal generated by the element  $1 - \text{Sq}^0$ . We will say that a (graded)  $\mathcal{A}$ -module is unstable if it is unstable when regarded as an  $\mathcal{A}^{\text{Big}}$ -module.

**Example 10.** Let X be a topological space. Since  $\operatorname{Sq}^0$  acts by the identity on the cohomology  $\operatorname{H}^*(X)$ , we conclude that  $\operatorname{H}^*(X)$  has the structure of an unstable module over the Steenrod algebra.

**Remark 11.** In the last lecture, we saw another feature of the action of Steenrod operations on the cohomology of spaces: the operations  $\operatorname{Sq}^{-a}$  vanish for a > 0. In fact, this is a formal consequence of Adem relations and the fact that  $\operatorname{Sq}^0$  acts by the identity. In other words, for a > 0 the element  $\operatorname{Sq}^{-a}$  is equal to zero in the Steenrod algebra  $\mathcal{A}$ . We will prove this by induction on a. For this, we invoke the Adem relations to deduce

$$\operatorname{Sq}^{-a} = \operatorname{Sq}^{-a} \operatorname{Sq}^{0} = \sum_{k} (2k + a, -k - 1) \operatorname{Sq}^{k} \operatorname{Sq}^{-a - k}.$$

If  $k \ge 0$  or  $-\frac{a}{2} < k$ , then the coefficient (2k+a, -k-1) vanishes. But if  $-\frac{a}{2} \le k < 0$ , then  $\operatorname{Sq}^{-a-k}$  is equal to zero in  $\mathcal{A}$  by the inductive hypothesis.

We now turn to the proof of Proposition 5. We begin with the following observation:

**Remark 12.** Recall that if V is a complex equipped with a symmetric multiplication, then  $\Omega V$  inherits a symmetric multiplication, and the isomorphism

$$H^*(V) \simeq H^{*+1}(\Omega V)$$

is compatible with the action of the Steenrod operations. The same argument shows that if V has a good symmetric multiplication, then the induced symmetric multiplication is also good. Consequently, in proving Proposition 5 we are free to replace V by any shift  $\Omega^{n'}(V)$ . In other words, we are free to enlarge the degree n of the cohomology class v.

The formula of Proposition 5 looks very assymetric: the left hand side has only one term, while the right hand side has many terms. We will deduce Proposition 5 from the following more symmetric looking assertion:

**Lemma 13.** Let p and q be positive integers, let V be a complex with a good symmetric multiplication, and let  $v \in H^n(V)$ . Then we have an equality

$$\sum_{l} (p - 2l, l) \operatorname{Sq}^{2n - q - l} \operatorname{Sq}^{n - p + l}(v) = \sum_{l'} (q - 2l', l') \operatorname{Sq}^{2n - p - l'} \operatorname{Sq}^{n - q - l'}(v)$$

in  $H^{4n-p-q}(V)$ .

Assuming Lemma 13, we can now prove Proposition 5.

*Proof.* Choose an integer  $m \gg 0$ . According to Remark 12, we are free to enlarge n as much as we like; in particular, we can choose  $n = 2^m - 1 + b$ . We will now apply Lemma 13 with  $p = 2^m - 1$  and q = 2n - a. Let us now evaluate both sides of the expression appearing in Lemma 13. The left hand side is given by

$$\sum_{l} (2^{m} - 1 - 2l, l) \operatorname{Sq}^{a-l} \operatorname{Sq}^{b+l}(v).$$

The coefficient  $(2^m - 1 - 2l, l)$  obviously vanishes if l < 0, or if  $l \ge 2^{m-1}$ . If  $0 < l < 2^{m-1}$ , then we can write  $l = 2^x + 2^{x+1}y$ , where  $0 \le x \le m-2$ . We now observe that  $2^x$  appears in the base 2 expansion of both  $2^m - 1 - 2l$  and l, so the coefficient  $(2^m - 1 - 2l, l)$  vanishes. It follows that the left hand side consists of only one nonzero term, given by the expression  $\operatorname{Sq}^a \operatorname{Sq}^b(v)$ .

We now evaluate the right hand side. Let  $k=2^m+b-l'-1$ , so that the left hand sum can be written as

$$\sum_{k} (2k - a, 2^{m} + b - k - 1) \operatorname{Sq}^{b+k} \operatorname{Sq}^{a-k}(v).$$

To complete the proof, it will suffice to show that for every integer k, either

$$(2k - a, 2^m + b - k - 1) = (2k - a, b - k - 1)$$

or  $\operatorname{Sq}^{b+k}\operatorname{Sq}^{a-k}(v)$  vanishes. We consider four cases:

(i) 2k < a: In this case, we have

$$(2k-a, 2^m+b-k-1) = (2k-a, b-k-1) = 0.$$

- (ii)  $a \le 2k < 2b$ : In this case,  $2k a < 2b a \le 2^m$ . It follows that  $(2k a, z) = (2k a, z + 2^m)$  for every nonnegative integer x (see Notation 4).
- (iii)  $2b \le 2k < a+2^m$ : The expression (2k-a,b-k-1) vanishes in this case. Moreover, we have  $2k-a \ge 2b-a > 0$ , so we can choose a nonnegative integer y such that  $2^y \le 2k-a \le 2^{y+1}-1$ . Our assumption implies that y < m. Since  $2k \le 2^{y+1}+a-1 \le 2^{y+1}+2b-2$ , we deduce that  $k-b+1 \le 2^y$ . We now observe that  $2^y$  appears in the base 2 expansion of both 2k-a and  $2^m-(k-b+1)$ , so the expression  $(2k-a, 2^m+b-k-1)$  vanishes.
- (iv)  $a + 2^m \le 2k$ : In this case, we have

$$\deg(\operatorname{Sq}^{a-k}(v)) = (a-k) + n = (a-k) + (2^m + b - 1).$$

Since  $a + 2^m \le 2k$ , we get  $\deg(\operatorname{Sq}^{a-k}(v)) \le k + b - 1 < k + b$ . Thus  $\operatorname{Sq}^{k+b} \operatorname{Sq}^{a-k}(v)$  vanishes for reasons of degree.

We now turn to the proof of Lemma 13. As usual, the equation among Steenrod operations on a complex V with a symmetric multiplication is an immediate consequence of the following more universal relation, which holds for any complex V:

**Lemma 14.** Let V be a complex, let p and q be positive integers, and let  $v \in H^n(V)$ . Then the sums

$$\sum_{l} (p-2l, l) \overline{\operatorname{Sq}}^{2n-q-l} \overline{\operatorname{Sq}}^{n-p+l}(v) \in \operatorname{H}^{4n-p-q}(D_2(D_2(V)))$$

$$\sum_{l'} (q - 2l', l') \, \overline{\mathrm{Sq}}^{2n - p - l'} \, \overline{\mathrm{Sq}}^{n - p + l'}(v) \in \mathrm{H}^{4n - p - q}(D_2(D_2(V)))$$

have the same image in  $H^{4n-p-q}(D_4(V))$  under the map  $\phi: D_2(D_2(V)) \to D_4(V)$ .

To prove Lemma 14, we may assume that  $V \simeq \mathbf{F}_2[-n]$  is generated by the cohomology class v. In this case,  $D_4(V) \simeq V_{h\Sigma_4}^{\otimes 4}$  can be identified with a (4n)-fold shift of the chain complex  $C_*(B\Sigma_4)$ . Similarly,

$$D_2(D_2(V)) \simeq D_2(C_*(B\Sigma_2)[-2n]) \simeq D_2(C_*(B\Sigma_2))[-4n]$$

can be identified with a shift of the chain complex  $C_*(BG)$ , where G is the semidirect product  $\Sigma_2 \times \Sigma_2 \times \Sigma_2$ , which we can identify with a 2-Sylow subgroup of  $\Sigma_4$ . Let us use our usual basis  $\{x_i\}_{i\leq 0}$  for the homology  $H_*(B\Sigma_2)$ . As we saw in the second lecture, this determines a basis for  $H_*(BG) \simeq H^{-*}D_2(C_*(B\Sigma_2))$ , consisting of pairwise products  $\{x_ix_j\}_{i\leq j}$  and Steenrod operations  $\{\overline{\operatorname{Sq}}^k x_i\}_{k\leq -i}$ . We have an isomorphism

$$H_*(BG) \simeq H^{4n-*}(D_2(D_2(V))),$$

which carries  $\overline{\operatorname{Sq}}^k x_i$  to  $\overline{\operatorname{Sq}}^{2n+k} \overline{\operatorname{Sq}}^{n-i}(v)$ . Consequently, Lemma 14 is an immediate consequence of the following assertion:

**Lemma 15.** Let p and q be positive integers. Then the expressions

$$\sum_{l} (p - 2l, l) \, \overline{\mathrm{Sq}}^{-q - l} \, x_{p - l} \in \mathrm{H}_{p + q}(BG)$$

$$\sum_{l} (q - 2l', l') \overline{\operatorname{Sq}}^{-p-l'} x_{q-l'} \in H_{p+q}(BG)$$

have the same image in  $H_{p+q}(B\Sigma_4)$ .

We will prove Lemma 15 in the next lecture.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Adem Relations (Continued) (Lecture 5)

We continue to work with complexes over the finite field  $\mathbf{F}_2$  with two elements. All homology and cohomology will be taken with coefficients in  $\mathbf{F}_2$ .

In the last lecture, we showed how to reduce the proof of the Adem relations to a calculation in group homology. Our goal in this lecture is to carry out that calculation. We begin with some generalities.

Let V be a complex with an action of the group  $\Sigma_2$ . In previous lectures, we have made extensive use of the homotopy coinvariants construction

$$V \mapsto V_{h\Sigma_2} \simeq (V \otimes E\Sigma_2)_{\Sigma_2}.$$

There is also a dual *homotopy invariants* construction, given by

$$V \mapsto V^{h\Sigma_2} \simeq \operatorname{Hom}(E\Sigma_2, V)^{\Sigma_2}$$
.

These constructions are related by a norm map  $N: V_{h\Sigma_2} \to V^{h\Sigma_2}$ , which has the property that the composition

$$V \to V_{h\Sigma_2} \xrightarrow{N} V^{h\Sigma_2} \to V$$

coincides with the usual norm map  $v \mapsto \sum_{g \in \Sigma_2} g(v)$ . The *Tate construction* on V is defined to be the cofiber of the norm map, and will be denoted by  $V^{T\Sigma_2}$ . By construction, we have a fiber sequence

$$V_{h\Sigma_2} \to V^{h\Sigma_2} \to V^{T\Sigma_2},$$

which induces a long exact sequence on cohomology.

To get a feel for how everything works, let's consider the case where  $V = \mathbf{F}_2$  is a complex concentrated in degree 0. In this case, we can identify  $V_{h\Sigma_2}$  with the chain complex  $C_*(B\Sigma_2)$ , and we can identify  $V^{h\Sigma_2}$  with the cochain complex  $C^*(B\Sigma_2)$ . The norm map induces a map

$$H_n(B\Sigma_2) \to H^{-n}(B\Sigma_2).$$

This is just the usual norm map in the theory of group cohomology. It vanishes for  $n \neq 0$  simply for degree reasons. For n = 0, it is given by multiplication by the order of the group  $B\Sigma_2$ , and therefore vanishes because we are taking coefficients in the field  $\mathbf{F}_2$ . Because the norm map vanishes in this case, it is convenient to rewrite the above fiber sequence as

$$V^{h\Sigma_2} \to V^{T\Sigma_2} \to V_{h\Sigma_2}[1].$$

The cohomology of  $V^{T\Sigma_2}$  is the *Tate cohomology* of the group  $\Sigma_2$ . The long exact sequence above gives isomorphisms

$$\mathrm{H}^n(V^{T\Sigma_2}) \simeq \mathrm{H}^n(B\Sigma_2)$$

$$H^{-n-1}(V^{T\Sigma_2}) \simeq H_n(B\Sigma_2)$$

for  $n \geq 0$ . In particular, we see that the Tate cohomology of  $\Sigma_2$  is 1-dimensional in every degree.

Recall that the cohomology ring  $H^*(B\Sigma_2)$  is isomorphic to the polynomial ring  $\mathbf{F}_2[t]$ . The multiplication on  $H^*(B\Sigma_2)$  extends to a multiplication defined on the Tate cohomology  $H^*(V^{T\Sigma_2})$ , which can be identified with the ring of Laurent polynomials  $\mathbf{F}_2[t,t^{-1}]$ . This induces an isomorphism

$$H_*(B\Sigma_2) \simeq \mathbf{F}_2[t, t^{-1}]/\mathbf{F}_2[t].$$

Using this isomorphism,  $H_*(B\Sigma_2)$  has a basis consisting of  $\{t^n\}_{n<0}$ . In previous lectures, we used a basis  $\{x_i\}_{i\geq 0}$  for  $H_*(B\Sigma_2)$  which was dual to the basis  $\{t^i\}_{i\geq 0}$  for  $H^*(B\Sigma_2)$ . By comparing degrees, we see that these bases are related by the following transformation

$$x_i \mapsto t^{-i-1}$$
.

It follows that the duality pairing between homology and cohomology can be written in the following suggestive form:

$$(f,g) \mapsto \operatorname{Res}(fg)$$
.

Here Res :  $\mathbf{F}_2[t, t^{-1}] \to \mathbf{F}_2$  denotes the residue map, which simply extracts the coefficient of  $t^{-1}$ .

Let us now consider some more interesting  $\Sigma_2$ -actions. For every complex V, there is a canonical action of  $\Sigma_2$  on the tensor square  $V \otimes V$ . We have defined the symmetric square  $D_2(V)$  to be the homotopy coinvariants  $(V \otimes V)_{h\Sigma_2}$ . This construction has the following counterparts for homotopy invariants and the Tate construction:

$$D^{2}(V) = (V \otimes V)^{h\Sigma_{2}}$$
$$D^{T}(V) = (V \otimes V)^{T\Sigma_{2}}$$

We now wish to describe the effects that these constructions have on cohomology. We can produce operations by repeating some of our earlier constructions.

**Definition 1.** Let V be a complex, and let  $v \in H^n(V)$ , so that v classifies a map  $\mathbf{F}_2[-n] \to V$ . We obtain induced maps

$$f: D^{2}(\mathbf{F}_{2})[-2n] \simeq D^{2}(\mathbf{F}_{2}[-n]) \to D^{2}(V)$$
  
$$f': D^{T}(\mathbf{F}_{2})[-2n] \simeq D^{2}(\mathbf{F}_{2}[-n]) \to D^{T}(V).$$

For every integer k, we let  $S^k(v) \in H^{n+k}(D^T(V))$  denote the image of  $t^{k-n} \in H^{k-n}(D^T(\mathbf{F}_2))$  under the map f'. If  $k \ge n$ , then

$$t^{k-n} \in \mathcal{H}^{k-n}(D^2(\mathbf{F}_2)) \subset \mathcal{H}^{k-n}(D^T(\mathbf{F}_2)).$$

In this case, we will denote the image of  $t^{k-n}$  under f by  $S^k(v) \in H^{n+k}(D^2(V))$ .

**Remark 2.** Our notation is potentially ambiguous, but will hopefully not result in any confusion since for  $k \geq n$ , the diagram

$$H^{n}(V) \xrightarrow{S^{k}} H^{n+k}(D^{2}(V))$$

$$\downarrow = \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$H^{n}(V) \xrightarrow{S^{k}} H^{n+k}(D^{T}(V))$$

is commutative.

Now suppose that V is equipped with a symmetric multiplication  $m: D_2(V) \to V$ . We can regard m as a homotopy fixed point for the action of  $\Sigma_2$  on the space  $\operatorname{Hom}(V \otimes V, V)$ . Consequently, m gives rise to a

commutative diagram

Here we regard  $\Sigma_2$  as acting trivially on V.

We wish to describe the induced maps on cohomology in terms the Steenrod operations on  $H^*(V)$ . For this, we need to introduce a mild finiteness restriction on V:

(\*) The cohomology groups  $H^n(V)$  are finite dimensional for every  $n \in \mathbb{Z}$ , and vanish for n sufficiently small.

Assuming condition (\*), we have equivalences

$$V^{h\Sigma_2} \simeq V \otimes (\mathbf{F}_2)^{h\Sigma_2}$$
$$V^{T\Sigma_2} \simeq V \otimes (\mathbf{F}_2)^{T\Sigma_2}$$
$$V_{h\Sigma_2} \simeq V \otimes (\mathbf{F}_2)_{h\Sigma_2}.$$

Passing to cohomology, we obtain isomorphisms

$$\begin{split} \mathbf{H}^*(V^{h\Sigma_2}) &\simeq \mathbf{H}^*(V)[t] \\ \\ \mathbf{H}^*(V^{T\Sigma_2}) &\simeq \mathbf{H}^*(V)[t,t^{-1}] \\ \\ \mathbf{H}^*(V_{h\Sigma_2}) &\simeq \mathbf{H}^{*+1}(V)[t,t^{-1}]/\mathbf{H}^*(V)[t]. \end{split}$$

We now have the following result:

**Proposition 3.** Let V be a complex equipped with a symmetric multiplication, and let  $v \in H^n(V)$ . Then:

(1) If  $k \geq n$ , then  $S^k(v) \in H^{n+k}(D^2(V))$  has image

$$\sum_{l} \operatorname{Sq}^{l}(v) t^{k-l} \in \operatorname{H}^{*}(V)[t].$$

(2) For all integers k, the element  $S^k(v) \in H^{n+k}(D^T(V))$  has image

$$\sum_{l} \operatorname{Sq}^{l}(v) t^{k-l} \in \operatorname{H}^{*}(V)[t, t^{-1}].$$

*Proof.* The implication (2)  $\Rightarrow$  (1) is clear. To prove (2), we consider the map  $\phi: H^*(D^T(V)) \to H^*(V)[t, t^{-1}]$ . We observe that  $\phi$  is a map of modules over the Tate cohomology ring  $H^*(\mathbf{F}_2^{T\Sigma_2}) \simeq \mathbf{F}_2[t,t^{-1}]$ , and that the action of this ring on  $H^*(D^T(V))$  satisfies  $t^m S^k(v) = S^{m+k}(v)$ . The coefficient of  $t^{k-l}$  in  $\phi(S^k(v))$  is given by

$$\operatorname{Res}(t^{l-k-1}\phi(S^k(v))) = \operatorname{Res}(\phi(S^{l-1}(v))).$$

We have a commutative diagram

$$H^{*}(V) \xrightarrow{S^{l-1}} H^{*}(D^{T}(V)) \longrightarrow H^{*}(V)[t, t^{-1}]$$

$$\downarrow^{\text{id}} \qquad \qquad \downarrow^{\text{Res}}$$

$$H^{*}(V) \xrightarrow{\operatorname{Sq}^{l}} H^{*}(D_{2}(V)) \longrightarrow H^{*}(V)[t, t^{-1}]/H^{*}(V)[t] \xrightarrow{\operatorname{Res}} H^{*}(V).$$

We now observe that the composition of the bottom arrows is the definition of the map  $\mathrm{Sq}^l$ .

We now wish to restrict further to the case where  $V \simeq C^*(\mathbf{R}P^{\infty})$  is the cochain complex which computes the cohomology of  $B\Sigma_2 \simeq \mathbf{R}P^{\infty}$ . To avoid confusion, let us identify this cohomology ring with the polynomial algebra  $\mathbf{F}_2[u]$ . We saw in a previous lecture that the action of the Steenrod algebra on  $\mathbf{F}_2[u]$  was given by

$$\operatorname{Sq}^{k}(u^{n}) = (n - k, k)u^{n+k}.$$

Let G denote the wreath product  $(\Sigma_2 \times \Sigma_2) \rtimes \Sigma_2$ , so the cochain complex  $C^*(BG)$  is equivalent to  $D^2(C^*(\Sigma_2))$ . We may view f as a map

$$C^*(BG) \to C^*(\Sigma_2)^{h\Sigma_2} \simeq C^*(\Sigma_2 \times \Sigma_2).$$

At the level of cohomology, this is simply the map induced by the inclusion of groups

$$\Sigma_2 \times \Sigma_2 \simeq \Sigma_2 \rtimes \Sigma_2 \xrightarrow{j} (\Sigma_2 \times \Sigma_2) \rtimes \Sigma_2 = G.$$

Applying Proposition 3 in this case, we obtain the following:

**Corollary 4.** The inclusion  $j: \Sigma_2 \times \Sigma_2 \to G$  induces a restriction map on cohomology  $H^*(BG) \to H^*(\Sigma_2 \times \Sigma_2) \simeq \mathbf{F}_2[t,u]$ . For  $k \geq n$ , this map carries  $S^k(u^n) \in H^{m+k}(BG)$  to

$$\sum_{n} (n-l,l)u^{n+l}t^{k-l}.$$

We observe that  $H_*(BG) \simeq H^{-*}(D_2(C_*(B\Sigma_2)))$  has a basis consisting of products  $\{x_ix_j\}_{0 \leq i < j}$  and Steenrod operations  $\{\overline{\operatorname{Sq}}^{-n}x_i\}_{0 \leq i \leq n}$ . We obtain a dual basis for  $H^*(BG)$  consisting of vectors  $\{v_{ij}\}_{0 \leq i < j}$  and Steenrod operations  $\{S^nu^i\}_{0 \leq i \leq n}$ . The basis vectors  $v_{ij}$  span the image of the norm map

$$H^*(D_2(C^*(\Sigma_2))) \to H^*(D^2(C^*(\Sigma_2))),$$

so the restriction map  $H^*(BG) \to H^*(\Sigma_2 \times \Sigma_2)$  vanishes on them. Thus Corollary 4 really gives a complete description of the restriction map  $H^*(BG) \to H^*(\Sigma_2 \times \Sigma_2)$ . Rewriting this information in terms of the dual bases, we obtain the following result:

**Corollary 5.** The inclusion  $j: \Sigma_2 \times \Sigma_2 \to G$  induces a map on homology

$$H_*(\Sigma_2 \times \Sigma_2) \to H_*(G)$$

which is described by the formula

$$x_p \otimes x_q \mapsto \sum_{l} (p - 2l, l) \overline{\operatorname{Sq}}^{-q - l} x_{p - l}.$$

We are now ready to complete the calculation of the last lecture. Recall that we need to show that for p, q > 0, the homology classes

$$\sum_{l} (p - 2l, l) \overline{\operatorname{Sq}}^{-q - l} x_{p - l} \in H_{p + q}(BG)$$

$$\sum_{l'} (q - 2l', l') \overline{\operatorname{Sq}}^{-p-l'} x_{q-l'} \in H_{p+q}(BG)$$

have the same image in  $H_*(B\Sigma_4)$ . Invoking Corollary 5, we see that it suffices to show that under the induced inclusion

$$\Sigma_2 \times \Sigma_2 \to \Sigma_4$$
,

the homology classes  $x_p \otimes x_q, x_q \otimes x_p \in H_{p+q}(B(\Sigma_2 \times \Sigma_2))$  have the same image in  $H_{p+q}(B\Sigma_4)$ . These two homology classes conjugate by the involution which permutes the two factors in the product  $\Sigma_2 \times \Sigma_2$ . We now observe that this involution is the restriction of an *inner* automorphism of  $\Sigma_4$ , and that inner automorphisms of a group H act trivially on the homology  $H_*(BH)$ .

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Admissible Monomials (Lecture 6)

Recall that we have define the big Steenrod algebra  $\mathcal{A}^{\mathrm{Big}}$  to be the quotient of the free associated  $\mathbf{F}_{2}$ -algebra

$$\mathbf{F}_{2}\{\ldots, \mathrm{Sq}^{-1}, \mathrm{Sq}^{0}, \mathrm{Sq}^{1}, \ldots\}$$

obtained by imposing the Adem relations:

$$\operatorname{Sq}^{a} \operatorname{Sq}^{b} = \sum_{k} (2k - a, b - k - 1) \operatorname{Sq}^{b+k} \operatorname{Sq}^{a-k}$$

for a < 2b, and the Steenrod algebra  $\mathcal{A}$  to be the quotient of of  $\mathcal{A}^{\text{Big}}$  by imposing the further relation  $\operatorname{Sq}^0 = 1$ . Our goal in this lecture is to explain some consequences of the Adem relations for the structure of the algebras  $\mathcal{A}^{\text{Big}}$  and  $\mathcal{A}$ .

We say that a monomial  $\operatorname{Sq}^a\operatorname{Sq}^b$  is admissible if  $a\geq 2b$ . If  $\operatorname{Sq}^a\operatorname{Sq}^b$  is not admissible, then the Adem relations allow us rewrite the monomial  $\operatorname{Sq}^a\operatorname{Sq}^b$  as a linear combination of other monomials. We observe that the coefficient (2k-a,b-k-1) appearing in the Adem relations vanishes unless  $\frac{a}{2}\leq k< b$ . Using the inequality  $k\geq \frac{a}{2}$ , we deduce

$$b+k \ge b+\frac{a}{2} > \frac{a}{2} + \frac{a}{2} = 2(a-\frac{a}{2}) \ge 2(a-k).$$

In other word, the Adem relations allow us rewrite each inadmissible expression  $\operatorname{Sq}^a\operatorname{Sq}^b$  as a sum of admissible monomials.

We would like to generalize the preceding observation. For every sequence of integers  $I = (i_n, i_{n-1}, \dots, i_0)$ , we let  $\operatorname{Sq}^I$  denote the product  $\operatorname{Sq}^{i_n} \operatorname{Sq}^{i_{n-1}} \dots \operatorname{Sq}^{i_0}$ . We will say that the sequence I is admissible if

$$i_{i} \geq 2i_{i-1}$$

for  $1 \leq j \leq n$ . In this case, we will also say that  $\operatorname{Sq}^I$  is an admissible monomial.

**Proposition 1.** The big Steenrod algebra  $A^{Big}$  is spanned (as an  $\mathbf{F}_2$ -vector space) by the admissible monomials  $\operatorname{Sq}^I$ . The usual Steenrod algebra A is spanned by the admissible monomials  $\operatorname{Sq}^I$  where I is a sequence of positive integers.

*Proof.* Recall that  $\operatorname{Sq}^{i}$  is equal to zero in  $\mathcal{A}$  if i < 0. It follows that  $\operatorname{Sq}^{I}$  vanishes in  $\mathcal{A}$  unless I is a sequence of nonnegative integers. Moreover, if I' is the sequence of integers obtained from I by deleting all occurrences of 0, then  $\operatorname{Sq}^{I} = \operatorname{Sq}^{I'}$  in  $\mathcal{A}$  (since  $\operatorname{Sq}^{0} = 1$ ); moreover, if  $\operatorname{Sq}^{I}$  is admissible then  $\operatorname{Sq}^{I'}$  is also admissible. Thus, the second assertion follows from the first.

The idea of the proof is now simple: let I be an arbitrary sequence of integers. We wish to show that we can use the Adem relations to rewrite  $\operatorname{Sq}^I$  as a linear combination of admissible monomials. The proof will use inducation. In order to make the induction work, we will need the following slightly stronger inductive hypothesis:

(\*) Let  $I = (i_n, ..., i_0)$  be a sequence of integers, and let x be an integer such that  $i_j \leq 2^j x$  for  $0 \leq j \leq n$ . Then in  $\mathcal{A}^{\text{Big}}$  there is a relation of the form

$$\operatorname{Sq}^{I} = \sum_{\alpha} \operatorname{Sq}^{I(\alpha)},$$

where each  $I(\alpha) = (i_n(\alpha), \dots, i_0(\alpha))$  is an admissible sequence satisfying  $i_j(\alpha) < 2^j x$  for  $0 \le j \le n$ .

We will prove this result by induction on n. For fixed n and x, we will use descending induction on  $i_n$  (this is justified since  $i_n$  is bounded above by  $2^n x$ , by assumption).

If n=0, then assertion (\*) is vacuous, since the expression  $\operatorname{Sq}^I$  is automatically admissible. Let us therefore assume that n>0. Let  $I=(i_n,\ldots,i_0)$ , and let  $I'=(i_{n-1},\ldots,i_0)$ . By the inductive hypothesis, we get an equation of the form

$$\operatorname{Sq}^{I'} = \sum_{\beta} \operatorname{Sq}^{I'(\beta)},$$

so that

$$\operatorname{Sq}^I = \operatorname{Sq}^{i_n} \operatorname{Sq}^{I'} = \sum_{\beta} \operatorname{Sq}^{i_n} \operatorname{Sq}^{I'(\beta)}.$$

It therefore suffices to prove (\*) for the sequences  $(i_n, i_{n-1}(\beta), \dots, i_0(\beta))$ . In other words, we may assume without loss of generality that the sequence  $I' = (i_{n-1}, \dots, i_0)$  is already admissible.

If  $i_n \geq 2i_{n-1}$ , then the sequence I is admissible and there is nothing to prove. Otherwise, we can invoke the Adem relations to deduce

$$\operatorname{Sq}^{i_n} \operatorname{Sq}^{i_{n-1}} = \sum_k (2k - i_n, i_{n-1} - k - 1) \operatorname{Sq}^{i_{n-1} + k} \operatorname{Sq}^{i_n - k}.$$

The terms on the right side vanish unless  $\frac{i_n}{2} \le k < i_{n-1}$ . In particular, we get

$$i_{n-1} + k < 2i_{n-1} < 2^n x$$

$$i_n - k \le i_n - \frac{i_n}{2} \le 2^{n-1}x$$

so that the new sequence  $J = (i_{n-1} + k, i_n - k, i_{n-2}, \dots, i_0)$  satisfies the hypotheses of (\*). Moreover,

$$i_{n-1} + k > \frac{i_n}{2} + \frac{i_n}{2} = i_n,$$

so the inductive hypothesis implies that  $Sq^{J}$  can be rewritten in the desired form.

**Scholium 2.** Let  $\mathcal{B}$  be the subspace of  $\mathcal{A}^{\text{Big}}$  generated by  $\text{Sq}^{I}$ , where  $I = (i_n, \dots, i_0)$  is an admissible sequence of nonpositive integers. Then  $\mathcal{B}$  is a subalgebra of  $\mathcal{A}^{\text{Big}}$ .

*Proof.* Apply (\*) in the case 
$$x = 0$$
.

The subalgebra  $\mathcal{B} \subseteq \mathcal{A}^{\text{Big}}$  is usually called the *Dyer-Lashof algebra*.

Proposition 1 is subsumed by the following stronger result:

**Proposition 3.** The admissible monomials  $\operatorname{Sq}^I$  form a basis for the big Steenrod algebra  $\mathcal{A}^{Big}$ . The admissible monomials of the form  $\operatorname{Sq}^I$ , where I is a sequence of positive integers, form a basis for the usual Steenrod algebra  $\mathcal{A}$ .

Proposition 1 already implies that  $\mathcal{A}^{\text{Big}}$  is generated (as a vector space) by the admissible monomials. Hence, the only thing we need to check is that the admissible monomials are linearly independent. This is a consequence of a more precise result, which we now formulate. First, we recall a bit of terminology. Let M be a module over  $\mathcal{A}^{\text{Big}}$  (always assumed to be graded). We say that M is unstable if  $\operatorname{Sq}^k(m) = 0$  whenever  $k > \deg(m)$ .

Let  $I = (i_n, i_{n-1}, \ldots, i_0)$  be an admissible sequence of integers, so we can write  $i_j = 2i_{j-1} + \epsilon_j$  where  $\epsilon_j \geq 0$ . The sum  $\epsilon_n + \ldots + \epsilon_1 + i_0$  is called the *excess* of I. Our reason for introducing this notion is the following:

**Lemma 4.** Let M be an unstable  $\mathcal{A}^{Big}$ -module, and let  $I = (i_n, \ldots, i_0)$  be an admissible sequence of integers. Then  $\operatorname{Sq}^I(m)$  vanishes whenever the excess of I is larger than the degree of m.

*Proof.* Let  $I' = (i_{n-1}, \ldots, i_0)$ . To show that  $\operatorname{Sq}^I(m)$  vanishes, it will suffice to show that  $i_n > \operatorname{deg}(\operatorname{Sq}^{I'}(m))$ . We now observe that

$$i_n - \deg(\operatorname{Sq}^{I'}(m)) = i_n - (i_{n-1} + \ldots + i_0 + \deg(m)) = (i_n - 2i_{n-1}) + (i_{n-1} - 2i_{n-2}) + \ldots + i_0 - \deg(m)$$

is positive if the excess of I is larger than the degree of m.

Given any graded  $\mathcal{A}^{\text{Big}}$ -module M, we can construct an unstable  $\mathcal{A}^{\text{Big}}$ -module by taking the quotient of M by the submodule generated by elements of the form  $\operatorname{Sq}^i(m)$ ,  $i > \deg(m)$ . In particular, if we take M to be the free  $\mathcal{A}^{\text{Big}}$ -module generated by a single class in degree n, then we obtain an unstable  $\mathcal{A}^{\text{Big}}$ -module which we will denote by  $\operatorname{F}^{\operatorname{Big}}(n)$ : we call  $\operatorname{F}^{\operatorname{Big}}(n)$  the free unstable  $\mathcal{A}^{\operatorname{Big}}$ -module on one generator in degree n. There is a canonical element  $\overline{\nu}_n \in \operatorname{F}^{\operatorname{Big}}(n)^n$ . By construction, this element has the following universal property: if N is any unstable  $\mathcal{A}^{\operatorname{Big}}$ -module, then evaluation at  $\overline{\nu}_n$  induces an isomorphism of  $\mathbf{F}_2$ -vector spaces  $\operatorname{Hom}_{\mathcal{A}^{\operatorname{Big}}}(\operatorname{F}^{\operatorname{Big}}(n), N) \to N^n$ .

Similarly, we can define the *free unstable* A-module on a generator in degree  $\nu_n$ , which we will denote by F(n).

Proposition 3 is an immediate consequence of the following result:

## **Proposition 5.** Let n be an integer. Then:

- (1) The free unstable  $A^{Big}$ -module  $F^{Big}(n)$  has a basis consisting of elements  $Sq^{I}\overline{\nu}_{n}$ , where I is an admissible sequence of excess  $\leq n$ .
- (2) The free unstable A-module F(n) has a basis consisting of elements  $\operatorname{Sq}^{I} \nu_{n}$ , where I is an admissible sequence of positive integers of excess  $\leq n$ .

Once again, half of Proposition 5 is clear: since  $\mathcal{A}^{\text{Big}}$  is generated by admissible monomials,  $F^{\text{Big}}(n)$  is generated by expressions of the form  $\operatorname{Sq}^I \overline{\nu}$ , where I is admissible. Lemma 4 implies that  $\operatorname{Sq}^I \overline{\nu}$  vanishes if I has excess > n. Thus  $F^{\text{Big}}(n)$  is generated by admissible monomials  $\operatorname{Sq}^I \overline{\nu}_n$ , where I is admissible and has excess  $\leq n$ . The same reasoning shows that F(n) is generated by elements of the form  $\operatorname{Sq}^I \nu_n$ , where I is admissible, positive and has excess  $\leq n$ .

To complete the proof of Proposition 5, we need to show:

- (1') The elements  $\{\operatorname{Sq}^I \overline{\nu}_n\}$  are linearly independent in  $\operatorname{F}^{\operatorname{Big}}(n)$ , where I ranges over admissible sequences of excess  $\leq n$ .
- (2') The elements  $\{\operatorname{Sq}^I \nu_n\}$  are linearly independent in F(n), where I ranges over positive admissible sequences of excess  $\leq n$ .

Our strategy is as follows. Let M be an unstable module over the Steenrod algebra  $\mathcal{A}$ , and let  $v \in M^n$ . Then, by construction, we get an induced map  $F(n) \to M$  of modules over the Steenrod algebra. To show that the generators  $\{\operatorname{Sq}^I v_n\}$  are linearly independent in F(n), it will suffice to show that the elements  $\{\operatorname{Sq}^I v\}$  are linearly independent in M. It will therefore suffice to find a particularly clever choice for the pair

(M, v). Fortunately, we have a host of examples of modules unstable  $\mathcal{A}$ -modules to choose from: namely, the cohomology  $H^*(X)$  of any space X is an unstable  $\mathcal{A}$ -module. We will therefore be able to deduce (2') by finding a sufficiently nontrivial example of a cohomology class on a topological space. We will return to this point in the next lecture.

Let us assume (2') for the moment, and show how to use (2') can be used to deduce (1'). The proof is based on the following observation:

**Lemma 6.** Let n and p be integers. Then there is a canonical isomorphism of vector spaces

$$\phi: \mathcal{F}^{Big}(n) \to \mathcal{F}^{Big}(n+p)$$

described by the formula

$$\operatorname{Sq}^{i_m} \dots \operatorname{Sq}^{i_1} \operatorname{Sq}^{i_0} \overline{\nu}_n \mapsto \operatorname{Sq}^{i_m + 2^k p} \dots \operatorname{Sq}^{i_1 + 2p} \operatorname{Sq}^{i_0 + p} \overline{\nu}_{n+n}$$

*Proof.* The above formula defines a map

$$\widetilde{\phi}: \mathbf{F}_2\{\ldots, \operatorname{Sq}^{-1}, \operatorname{Sq}^0, \ldots\} \overline{\nu}_n \to \mathbf{F}_2\{\ldots, \operatorname{Sq}^{-1}, \operatorname{Sq}^0, \ldots\} \overline{\nu}_{n+n}$$

of free modules over the free algebra  $R = \mathbf{F}_2\{\ldots, \mathrm{Sq}^{-1}, \mathrm{Sq}^0, \mathrm{Sq}^1, \ldots\}$ . To show that  $\phi$  is well-defined, we need to show that  $\widetilde{\phi}$  descends to the quotient. This amounts to two observations:

(a) Let J denote the two-sided ideal of R generated by the Adem relations. Then  $\widetilde{\phi}$  carries  $J\overline{\nu}_n$  into  $J\overline{\nu}_{n+p}$ . This amounts to a "translation-invariance" feature of the Adem relations: if a < 2b, then we have an Adem relation

$$\operatorname{Sq}^{a} \operatorname{Sq}^{b} = \sum_{k} (2k - a, b - k - 1) \operatorname{Sq}^{b+k} \operatorname{Sq}^{a-k}.$$

But we also have  $(a + 2^{l}p) < 2(b + 2^{l-1}p)$ , and a corresponding Adem relation

$$\operatorname{Sq}^{a+2^{l}p}\operatorname{Sq}^{b+2^{l-1}p} = \sum_{k} (2k-a-2^{l}p,b+2^{l-1}-k-1)\operatorname{Sq}^{b+2^{l-1}p+k}\operatorname{Sq}^{a+2^{l}p-k}.$$

Letting  $k' = k + 2^{l-1}p$ , we can rewrite this as

$$\operatorname{Sq}^{a+2^{l}p} \operatorname{Sq}^{b+2^{l-1}p} = \sum_{k'} (2k'-a, b-k'-1) \operatorname{Sq}^{b+2^{l}p+k'} \operatorname{Sq}^{a+2^{l-1}-k'}$$

which is precisely the sort of term that appears in the image of  $\widetilde{\phi}$ .

(b) Let  $x \in R\overline{\nu}_n$  have degree q, so that  $\operatorname{Sq}^a(x)$  vanishes in  $\operatorname{F}^{\operatorname{Big}}(n)$  for a > q. We wish to show that  $\widetilde{\phi}(\operatorname{Sq}^a(x))$  vanishes in  $\operatorname{F}^{\operatorname{Big}}(n+p)$ . Without loss of generality, we may suppose that

$$x = \operatorname{Sq}^{i_m} \dots \operatorname{Sq}^{i_0} \overline{\nu}_n,$$

where  $q = i_m + \ldots + i_0 + n$ . Then

$$\widetilde{\phi}(\operatorname{Sq}^a(x)) = \operatorname{Sq}^{a+2^{m+1}p} \operatorname{Sq}^{i_m+2^m p} \dots \operatorname{Sq}^{i_0+p} \overline{\nu}_p = \operatorname{Sq}^{a+2^{m+1}p} \widetilde{\phi}(x)$$

vanishes in  $F^{Big}(n+p)$  since

$$a + 2^{m+1}p > (i_m + \dots + i_0 + n) + 2^{m+1}p = (i_m + 2^m p) + \dots + (i_0 + p) + (n+p) = \deg(\widetilde{\phi}(x)).$$

This completes the proof that  $\phi$  is well-defined. To show that  $\phi$  induces an isomorphism  $F^{\text{Big}}(n) \to F^{\text{Big}}(n+p)$ , we observe that the same construction (applied to n+p and -p) gives a map  $F^{\text{Big}}(n+p) \to F^{\text{Big}}(n)$  which is inverse to  $\phi$ .

Proof of  $(2') \Rightarrow (1')$ . Fix an integer n. We wish to show the elements  $\operatorname{Sq}^I \overline{\nu}_n$  are linearly independent in  $\operatorname{F}^{\operatorname{Big}}(n)$ , where I ranges over admissible sequences of integers of excess  $\leq n$ . Assume otherwise; then there exists a nontrivial relation of the form

$$\sum_{\alpha} \operatorname{Sq}^{I(\alpha)} \overline{\nu}_n = 0.$$

Choose  $p \gg 0$ , and let  $\phi : F^{Big}(n) \to F^{Big}(n+p)$  be as in Lemma 6. We then get a nontrivial relation

$$\sum_{\alpha} \phi(\operatorname{Sq}^{I(\alpha)} \overline{\nu}_n) = \sum_{\alpha} \operatorname{Sq}^{J(\alpha)} \overline{\nu}_{n+p} = 0$$

in  $F^{Big}(n+p)$ . It follows that

$$\sum_{\alpha} \operatorname{Sq}^{J(\alpha)} \nu_{n+p} = 0$$

in F(n+p). The sequences  $J(\alpha)$  are distinct, admissible, and positive if p is chosen sufficiently large. Thus (1') implies that the elements  $\{\operatorname{Sq}^{J(\alpha)}\nu_{n+p}\}$  are linearly independent in F(n+p), and we obtain a contradiction.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Free Modules (Lecture 7)

We first recall a bit of notation: If  $I = (i_1, \ldots, i_k)$  is a sequence of integers, we write  $\operatorname{Sq}^I$  for the composition product  $\operatorname{Sq}^{i_1} \ldots \operatorname{Sq}^{i_k}$  in the Steenrod algebra  $\mathcal{A}$  (or the big Steenrod algebra  $\mathcal{A}^{\operatorname{Big}}$ ). We say that I is admissible if  $i_i \geq 2i_{i+1}$  for  $1 \leq j < k$ . The excess of I is defined to be the expression

$$i_1 - i_2 - i_3 - \dots - i_k = (i_1 - 2i_2) + (i_2 - 2i_3) + \dots + (i_{k-1} - 2i_k) + i_k$$

We wanted to prove that the Steenrod algebra has a basis  $\{\operatorname{Sq}^I\}$ , where I ranges over the admissible sequences of positive integers. This was reduced to the following assertion:

**Proposition 1.** Let F(n) denote the free unstable A-module generated by one generator  $\nu_n$  in degree n. Then the collection of elements  $\{\operatorname{Sq}^I\nu_n\}$  is linearly independent in F(n), where I ranges over admissible sequences of positive integers having excess  $\leq n$ .

To prove this, it will suffice to find any unstable A-module M with a element  $x \in M^n$  such that the set  $\{\operatorname{Sq}^I x\}$  is linearly independent in M (here again I ranges over admissible positive sequences of excess  $\leq n$ ). To see this, we observe that the freeness of F(n) implies that there is a (unique) map  $\phi: F(n) \to M$  with  $\phi(\nu_n) = x$ . Consequently, any linear relation among the expressions  $\{\operatorname{Sq}^I \nu_n\}$  would entail a linear relation among the expressions  $\{\operatorname{Sq}^I x\}$ .

It will therefore suffice to choose M to be some sufficiently nontrivial unstable A-module. We have seen that for any topological space X, the cohomology  $H^*(X)$  has the structure of an unstable module over the Steenrod algebra. The most interesting example we have studied so far is the case where  $X = B\Sigma_2 \simeq \mathbf{R}P^{\infty}$ . In this case, the cohomology ring  $H^*(X)$  is isomorphic to a polynomial ring  $\mathbf{F}_2[t]$ , and the action of the Steenrod algebra is described by the formula

$$\operatorname{Sq}^k t^m = \binom{m}{k} t^{m+k}.$$

We can obtain a more interesting example by taking X to be a product of n copies of the space  $\mathbb{R}P^{\infty}$ . In this case, the cohomology of X can be identified with a polynomial ring  $\mathbb{F}_2[t_1,\ldots,t_n]$  in several variables (obtained by pulling back the cohomology class t along the n different projections). Using the Cartan formula

$$\operatorname{Sq}^{k}(xy) = \sum_{k=k'+k''} \operatorname{Sq}^{k'}(x) \operatorname{Sq}^{k''}(y),$$

we deduce that the action of the Steenrod algebra on  $H^*(X)$  is described by the following formula:

$$\operatorname{Sq}^{k}(t_{1}^{a_{1}} \dots t_{n}^{a_{n}}) = \sum_{k=k_{1}, k_{1}, k_{2}, k_{3}} {a_{1} \choose k_{1}} \dots {a_{n} \choose k_{n}} t_{1}^{a_{1}+k_{1}} \dots t_{n}^{a_{n}+k_{n}}.$$

We now make a crucial observation about the formula above. Suppose that each exponent  $a_i$  is a power of 2. The binomial coefficient  $\binom{a_i}{k_i}$  is equal to 1 if  $k_i = 0$  or  $k_i = a_i$ , and vanishes otherwise (since we are working over the field  $\mathbf{F}_2$ ). Moreover, the exponents appearing on the right hand side have the form  $a_i + k_i$ ,

which will again be a power of two if  $k_i = 0$  or  $k_i = a_i$ . In other words, we can rewrite the preceding formula as follows:

$$\operatorname{Sq}^{k}(t_{1}^{2^{b_{1}}}\dots t_{n}^{2^{b_{n}}}) = \sum_{k=\delta_{1}2^{b_{1}}+\dots+\delta_{n}2^{b_{n}}} t_{1}^{2^{b_{1}+\delta_{1}}}\dots t_{n}^{2^{b_{n}+\delta_{n}}},$$

where the sum is taken over  $\delta_1, \ldots, \delta_n \in \{0, 1\}$ .

Let  $x = t_1 \dots t_n \in \mathbf{F}_2[t_1, \dots, t_n]$ . Then, for every sequence of integers I, the expression  $\operatorname{Sq}^I(x)$  can be identified with some polynomial  $f(t_1, \dots, t_n) \in \mathbf{F}_2[t_1, \dots, t_n]$ . This polynomial necessarily has the following properties:

- (a) Every monomial appearing in f has the form  $t_1^{2^{b_1}}\dots t_n^{2^{b_n}}.$
- (b) The polynomial f is symmetric in its arguments.

Let M denote the subspace of  $\mathbf{F}_2[t_1,\ldots,t_n]$  consisting of those polynomials which satisfy (a) and (b) above. We observe that M is invariant under the action of the Steenrod algebra  $\mathcal{A}$ , and is therefore an unstable  $\mathcal{A}$ -module in its own right. Moreover, M contains the element  $x=t_1\ldots t_n$  of degree n. To complete the proof of Proposition 1, it will suffice to show the following:

**Proposition 2.** The expressions  $\{\operatorname{Sq}^I(x)\}$  form a basis for M, where I ranges over admissible sequences of positive integers having excess  $\leq n$ .

Let us now introduce a bit of notation. Given a monomial  $f = t_1^{a_1} \dots t_n^{a_n}$ , let

$$\sigma(f) = \sum_{g \in \Sigma_n / G} f^g$$

be the symmetric polynomial obtained by summing the conjugates of f; here we take G to be the stabilizer of f in  $\Sigma_n$ , so that f itself appears in this sum exactly once. For example, if n = 2, we have

$$\sigma(t_1^a t_2^b) = \begin{cases} t_1^a t_2^b & \text{if } a = b \\ t_1^a t_2^b + t_1^b t_2^a & \text{if } a \neq b \end{cases}.$$

The space M has a basis consisting of symmetric polynomials of the form  $\sigma(t_1^{2^{b_1}} \dots t_n^{2^{b_n}})$ , where  $0 \leq b_1 \leq \dots \leq b_n$ . It will be convenient to index this set of polynomials a little bit differently. Given a sequence of nonnegative integers  $\epsilon = (\epsilon_0, \dots, \epsilon_k)$  with  $\epsilon_0 + \dots + \epsilon_k = n$ , there is a unique sequence  $0 \leq b_1 \leq \dots \leq b_n$  such that  $\epsilon_i$  is the cardinality of the set  $\{j: b_j = i\}$ . We then set  $f_{\epsilon} = \sigma(t_1^{2^{b_1}} \dots t_n^{2^{b_n}})$ . Thus M has a basis consisting of the polynomials  $\{f_{\epsilon}\}$ , where  $\epsilon$  ranges over sequences of nonnegative integers  $(\epsilon_0, \dots, \epsilon_k)$  such that  $n = \epsilon_0 + \dots + \epsilon_k$  and  $\epsilon_k$  is nonzero.

There is a corresponding indexing for positive admissible monomials of the form  $\operatorname{Sq}^I$ . Let  $I=(i_1,\ldots,i_k)$  be a sequence of positive integers. If I is admissible, then the integers  $\epsilon_1=i_1-2i_2,\,\epsilon_2=i_2-2i_3,\ldots,\epsilon_{k-1}=i_{k-1}-2i_k$  are all nonnegative. We then set  $\epsilon_k=i_k$ , which is positive so long as I is positive. The sum

$$\epsilon_1 + \ldots + \epsilon_k = i_1 - i_2 - \ldots - i_k$$

is equal to the excess of I. Thus, if I has excess  $\leq n$ , we can define  $\epsilon_0 = n - (\epsilon_1 + \ldots + \epsilon_k)$ , to obtain a sequence of nonnegative integers  $\epsilon = (\epsilon_0, \ldots, \epsilon_k)$ , where  $\epsilon_k$  is positive. Conversely, given such a sequence of integers, we can construct a unique admissible sequence  $I = (2^{k-1}\epsilon_k + \ldots + \epsilon_1, \ldots, 2\epsilon_k + \epsilon_{k-1}, \epsilon_k)$  of excess  $\leq n$ . We will denote this admissible sequence by  $I(\epsilon)$ .

We now wish to compare the expressions  $\{\operatorname{Sq}^{I(\epsilon)}(x)\}$  with the basis  $\{f_{\epsilon}\}$  for M. They do not coincide, but we get the next best thing: the translation between these two bases is upper triangular. To be more precise, we need to introduce an ordering on our index set. Let E be the collection of all finite sequences  $\epsilon = (\epsilon_0, \ldots, \epsilon_k)$  of nonnegative integers (here k is allowed to vary) such that  $\epsilon_k > 0$ , and  $\epsilon_0 + \ldots + \epsilon_k = n$ .

We equip E with the following lexicographical ordering:  $\epsilon < \epsilon'$  if there exists an integer i such that  $\epsilon_i < \epsilon'_i$ , while  $\epsilon_j = \epsilon'_j$  for j > i. Here we agree to the convention that  $\epsilon_i = 0$  if i is larger than the length of the sequence  $\epsilon$ .

To complete prove Proposition 2, it will suffice to verify the following:

## **Proposition 3.** Let $\epsilon \in E$ . Then

$$\operatorname{Sq}^{I(\epsilon)}(x) = f_{\epsilon} + \sum_{\alpha} f_{\alpha}$$

where  $\alpha$  ranges over some subset of  $\{\epsilon' \in E : \epsilon' < \epsilon\}$ .

*Proof.* We compute:

$$x = \sigma(t_1 \dots t_n)$$

$$\operatorname{Sq}^{\epsilon_k}(x) = \sigma(t_1^2 t_2^2 \dots t_{\epsilon_k}^2 t_{\epsilon_k + 1} \dots t_n)$$

$$\operatorname{Sq}^{\epsilon_{k-1} + 2\epsilon_k} \operatorname{Sq}^{\epsilon_k}(x) = \sigma(t_1^4 t_2^4 \dots t_{\epsilon_k}^4 t_{\epsilon_k + 1}^2 \dots t_{\epsilon_k + \epsilon_{k-1}}^2 t_{\epsilon_k + \epsilon_{k-1} + 1} \dots t_n) + \text{lower order}$$

$$\dots$$

$$\operatorname{Sq}^{I(\epsilon)}(x) = f_{\epsilon} + \text{lower order}$$

We now wish to reformulate some of the above ideas, using Kuhn's theory of "generic representations". In what follows, we let V denote a finite dimensional vector space over  $\mathbf{F}_2$ , and let  $V^{\vee}$  denote its dual space. We observe that

$$\mathrm{H}^*(BV^{\vee}) = \mathrm{H}^*(\mathbf{R}P^{\infty} \times \ldots \times \mathbf{R}P^{\infty}) \simeq \mathbf{F}_2[t_1, \ldots, t_N],$$

where N is the dimension of V. However, we can describe this cohomology ring more in a more invariant way: it is given by the symmetric algebra  $\operatorname{Sym}^*(V)$  generated by the vector space  $V \simeq \operatorname{H}^1(BV^{\vee})$ .

Every admissible monomial  $Sq^{I}$  in the Steenrod algebra of degree k determines a map

$$\mathrm{H}^*(BV^\vee) \to \mathrm{H}^{*+k}(BV^\vee).$$

Restricting to a particular degree n, we get a map

$$\operatorname{Sym}^n(V) \to \operatorname{Sym}^{n+k}(V)$$
.

This map depends functorially on V, and vanishes if the excess of I is larger than n.

To study the situation more systematically, let  $\operatorname{Vect}^f$  denote the category of finite dimensional vector spaces over  $\mathbf{F}_2$ , and Vect the category of all vector spaces over  $\mathbf{F}_2$ . We let Fun denote the category of functors from  $\operatorname{Vect}^f$  to  $\operatorname{Vect}$ .

**Remark 4.** Kuhn refers to objects of Fun as generic representations. If  $F : \operatorname{Vect}^f \to \operatorname{Vect}$  is a functor, then for every finite dimensional vector space  $V \in \operatorname{Vect}^f$ , we obtain a new vector space F(V) which is equipped with an action of  $\operatorname{Aut}(V) \simeq \operatorname{GL}_n(\mathbf{F}_2)$ . In other words, we can think of F as providing a family of representations of the groups  $\operatorname{GL}_n(\mathbf{F}_2)$ , which are somehow connected to one another as n grows.

**Example 5.** For every nonnegative integer n, the functor

$$V \mapsto \operatorname{Sym}^n(V)$$

is an object of Fun, which we will denote by  $\operatorname{Sym}^n$ . Let  $\operatorname{Sym}^*$  denote the direct sum of these functors, so that  $\operatorname{Sym}^*(V)$  is the free algebra generated by V.

If  $\operatorname{Sq}^I$  is an admissible monomial (or any element of the Steenrod algebra), then  $\operatorname{Sq}^I$  determines a natural transformation

$$\operatorname{Sym}^n \to \operatorname{Sym}^*$$
:

in other words, a morphism in the category Fun. This natural transformation vanishes if the excess of I is larger than n.

**Proposition 6.** Let n be a positive integer. Then the natural transformations  $\{Sq^I\}$  form a basis for  $Hom_{Fun}(Sym^n, Sym^*)$ , where I ranges over positive admissible sequences of excess  $\leq n$ .

Proof. We first show that the expressions  $\operatorname{Sq}^I$  are linearly independent in  $\operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n,\operatorname{Sym}^*)$ . For this, it suffices to choose a vector space V such that the functors  $\operatorname{Sq}^I$  are linearly independent in  $\operatorname{Hom}_{\mathbf{F}_2}(\operatorname{Sym}^n(V),\operatorname{Sym}^*(V))$ . Let V be the free vector space generated by a basis  $\{t_1,\ldots,t_n\}$ , and let  $x=t_1\ldots t_n$ ; then it will suffice to show that the elements  $\{\operatorname{Sq}^I(x)\}$  are linearly independent in  $\operatorname{Sym}^*(V)$ . This follows immediately from Proposition 2.

We now wish to prove that  $\operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n,\operatorname{Sym}^*)$  is spanned by the Steenrod operations  $\{\operatorname{Sq}^I\}$ . For this, we need to compute  $\operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n,\operatorname{Sym}^*)$ . Suppose  $\alpha:\operatorname{Sym}^n\to\operatorname{Sym}^*$  is a natural transformation. Choose  $V=\mathbf{F}_2\{t_1,\ldots,t_n\}$  as above, and let  $x=t_1\ldots t_n\in\operatorname{Sym}^n(V)$ . Then  $\alpha(x)=f(t_1,\ldots,t_n)\in\mathbf{F}_2[t_1,\ldots,t_n]\simeq\operatorname{Sym}^*(V)$ , for some polynomial f. The construction  $\alpha\mapsto f$  determines a linear map

$$\phi: \operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n, \operatorname{Sym}^*) \to \mathbf{F}_2[t_1, \dots, t_n].$$

We first claim that  $\phi$  is injective. For suppose that  $\phi(\alpha) = 0$ . Let W be any vector space over  $\mathbf{F}_2$ . We wish to prove that the induced map

$$\alpha_W : \operatorname{Sym}^n(W) \to \operatorname{Sym}^*(W)$$

is equal to zero. Since  $\alpha_W$  is a linear map, it will suffice to show that  $\alpha_W$  vanishes on each monomial  $w_1 \dots w_n$  in  $\operatorname{Sym}^n(W)$ . But in this case we have a map  $V \to W$ , given by  $t_i \mapsto w_i$ . This linear map determines a commutative diagram

$$\operatorname{Sym}^{n}(V) \xrightarrow{\phi} \operatorname{Sym}^{*}(V)$$

$$\downarrow \qquad \qquad \downarrow$$

$$\operatorname{Sym}^{n}(W) \xrightarrow{\alpha_{W}} \operatorname{Sym}^{*}(W),$$

so that  $\alpha_W(w_1 ... w_n) = f(w_1, ..., w_n) = 0 \in \text{Sym}^*(W)$ .

We now wish to describe the image of the map  $\phi$ . Fix  $\alpha : \operatorname{Sym}^n \to \operatorname{Sym}^*$ , and let  $f = \phi(\alpha)$ . Since  $x = t_1 \dots t_n \in \operatorname{Sym}^n(V)$  is invariant under the permutation action of the symmetric group, we deduce immediately that f is a *symmetric* polynomial.

Let V' be the  $\mathbf{F}_2$ -vector space spanned by a basis  $\{t_1,\ldots,t_n,t_{n+1}\}$ . Then we have an equation

$$t_1 \dots t_{n-1}(t_n + t_{n+1}) = t_1 \dots t_n + t_1 \dots t_{n-1} t_{n+1}.$$

Since the map  $\alpha_{V'}$  is linear, we get

$$f(t_1,\ldots,t_{n-1},t_n+t_{n+1})=f(t_1,\ldots,t_n)+f(t_1,\ldots,t_{n-1},t_{n+1})$$

In other words, the polynomial f is additive in its last argument. If we write

$$f(t_1, \dots, t_n) = \sum_k g_k(t_1, \dots, t_{n-1}) t_n^k,$$

then we deduce that  $g_k(t_1, \ldots, t_{n-1})$  vanishes unless k is a power of 2. Since f is symmetric, we can apply the same reasoning to each argument of f. It follows that f can be written as a sum of monomials of the form  $t_1^{2^{b_1}} \ldots t_n^{2^{b_n}}$ . Since f is symmetric, we conclude that  $f \in M \subseteq \mathbf{F}_2[t_1, \ldots, t_n]$ .

We therefore have a factorization

$$\phi: \operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n, \operatorname{Sym}^*) \hookrightarrow M \subset \mathbf{F}_2[t_1, \dots, t_n].$$

The map  $\phi$  carries  $\operatorname{Sq}^I$  to  $\operatorname{Sq}^I(x)$ . Proposition 2 implies that M is generated by these expressions, so that  $\phi$  restricts to an isomorphism  $\operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n,\operatorname{Sym}^*)\simeq M$ . Since the expressions  $\{\operatorname{Sq}^I(x)\}$  form a basis for M (where I ranges over admissible positive sequences of excess  $\leq n$ ), we conclude that the expressions  $\{\operatorname{Sq}^I\}$  form a basis for  $\operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n,\operatorname{Sym}^*)$ .

This gives another approach to constructing the Steenrod algebra (at least with mod-2 coefficients): it can be regarded as an algebra of natural transformations between functors of the form

$$\operatorname{Sym}^n:\operatorname{Vect}^f\to\operatorname{Vect}$$
.

We will return to this point of view in the next lecture.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## A Theorem of Gabriel-Kuhn-Popesco (Lecture 8)

Let  $\mathcal{C}$  be an abelian category. Suppose that  $\mathcal{C}$  is equivalent to the category Mod(R) of (right) modules over an associative ring R. How might we recognize this? To answer this, we first recall a very general definition:

**Definition 1.** Let  $\mathcal{C}$  be an abelian category which admits direct sums. A collection of objects  $\{C_{\alpha}\}$  generates  $\mathcal{C}$  if, for every object  $D \in \mathcal{C}$ , there exists an epimorphism

$$\bigoplus_i C_{\alpha_i} \to D$$
.

A Grothendieck abelian category is an abelian category C satisfying the following conditions:

- (1) The category C admits filtered colimits, and the formation of filtered colimits is exact (in other words, a filtered colimit of monomorphisms is a monomorphism).
- (2) There exists a set of generators  $\{C_{\alpha}\}$  for  $\mathcal{C}$ .

If  $\mathcal{C}$  is equivalent to  $\operatorname{Mod}(R)$ , then it has a distinguished object C, corresponding to R (regarded as a module over itself). We can then recover R as the ring of endomorphisms  $\operatorname{Hom}_{\mathcal{C}}(C,C)$ . More generally, given any object  $D \in \mathcal{C}$ , we can define a (right) R-module G(D) by the formula

$$G(D) = \operatorname{Hom}_{\mathcal{C}}(C, D).$$

If C is a Grothendieck abelian category, then the functor G has a left adjoint F, which we will denote by

$$M \mapsto M \otimes_R C$$
.

The adjoint functors F and G determine an equivalence between  $\mathcal{C}$  and  $\operatorname{Mod}_R$  if and only if the following three conditions are satisfied:

- (1) The object C generates  $\mathcal{C}$ .
- (2) The object C is projective: that is, the functor  $\operatorname{Hom}_{\mathfrak{C}}(C, \bullet)$  is exact.
- (3) The object C is compact: that is, the functor  $\operatorname{Hom}_{\mathbb{C}}(C, \bullet)$  commutes with filtered colimits (in view of (2), this is equivalent to requiring that  $\operatorname{Hom}_{\mathbb{C}}(C, \bullet)$  commutes with all colimits, or with direct sums).

If C fails to satisfy conditions (2) and (3), then there is still a close relationship between  $\mathfrak{C}$  and Mod(R): namely,  $\mathfrak{C}$  is a localization of Mod(R). This is the classical Gabriel-Popesco theorem.

Condition (1) is not very restrictive: every Grothendieck abelian category admits a generator. Note, for example, that if  $\mathcal{C}$  is generated by a set of objects  $\{C_{\alpha}\}$ , then  $\mathcal{C}$  is generated by the single object  $C = \bigoplus_{\alpha} C_{\alpha}$ . However, the ring  $R = \operatorname{Hom}_{\mathcal{C}}(C, C)$  in this case might be rather unwieldy. It will therefore be convenient to formulate a "many-object" version of the Gabriel-Popesco theorem. We will follow the presentation of Nick Kuhn.

Throughout the remainder of this lecture, we fix the following notation:

- C will be a Grothendieck abelian category.
- $\{C_{\alpha}\}$  will be a set of objects of  $\mathcal{C}$  which generates  $\mathcal{C}$ .
- $\Re$  will denote the full subcategory of  $\mathcal{C}$  spanned by the objects  $\{C_{\alpha}\}$ .

**Definition 2.** A  $\mathcal{R}$ -module is a contravariant functor M from  $\mathcal{R}$  to the category of abelian groups, which is linear in the following sense: for every pair of objects  $C, D \in \mathcal{R}$ , the map

$$\operatorname{Hom}_{\mathfrak{C}}(C,D) \times M(D) \to M(C)$$

is bilinear.

The collection of  $\mathcal{R}$ -modules can be organized into a category, which we will denote by  $\operatorname{Mod}(\mathcal{R})$ .

**Example 3.** If  $\mathcal{R}$  consists of a single object  $C \in \mathcal{C}$ , then a  $\mathcal{R}$ -module is simply a right module over the ring  $R = \text{Hom}_{\mathcal{C}}(C, C)$ .

**Example 4.** Let D be an object of  $\mathbb{C}$ . Then the functor  $C \mapsto \operatorname{Hom}_{\mathbb{C}}(C, D)$  is a  $\mathbb{R}$ -module. We will denote this  $\mathbb{R}$ -module by G(D). This construction determines a functor

$$G: \mathcal{C} \to \operatorname{Mod}(\mathcal{R})$$
.

**Theorem 5** (Kuhn, Gabriel-Popesco). (1) The functor G admits a left adjoint F.

- (2) The functor G is fully faithful.
- (3) The functor F is exact.

**Remark 6.** Theorem 5 implies that  $\mathcal{C}$  can be obtained as a *localization* of  $\operatorname{Mod}(\mathcal{R})$ . More precisely, let  $\mathcal{K}$  denote the full subcategory of  $\operatorname{Mod}(\mathcal{R})$  spanned by those modules M such that  $F(M) \simeq 0$ . Then  $\mathcal{K}$  is a Serre subcategory of  $\operatorname{Mod}(\mathcal{R})$ , and F induces an equivalence

$$\operatorname{Mod}(\mathfrak{R})/\mathfrak{K} \simeq \mathfrak{C}$$
.

The rest of this lecture is devoted to proving Theorem 5. We will later apply this theorem in the case where  $\mathcal{C}$  is the category Fun = Fun(Vect<sup>f</sup>, Vect). Combined with the results of the previous lecture, this will yield some interesting information on the category of unstable modules over the Steenrod algebra  $\mathcal{A}$ .

Assertion (1) follows from the adjoint functor theorem. To prove (2) and (3) we will follow the argument presented in Kuhn, "Generic Representations of the Finite General Linear GRoups and the Steenrod Algebra I".

**Lemma 7.** Let M be an  $\mathbb{R}$ -module and let  $D \in \mathbb{C}$ . If  $u : M \to G(D)$  is a monomorphism in  $Mod(\mathbb{R})$ , then the adjoint map  $u' : F(M) \to D$  is a monomorphism in  $\mathbb{C}$ .

*Proof.* We first observe that there is an epimorphism

$$\pi: \bigoplus_{\alpha \in M(C)} C \to F(M).$$

To prove that u' is a monomorphism, it will suffice to show that  $\ker(u' \circ \pi) = \ker(\pi)$ . Since  $\mathcal{R}$  generates  $\mathcal{C}$ , The direct sum  $\bigoplus_{\alpha \in M(C)} C$  is a direct limit of finite sums

$$\bigoplus_{i \in I} C_i$$

Let  $\pi_I$  denote the restriction of  $\pi$  to this finite sum. Since filtered colimits in  $\mathcal{C}$  are exact, we deduce that

$$\ker(u' \circ \pi) \simeq \operatorname{colim} \ker(u' \circ \pi_I)$$

$$\ker(\pi) \simeq \operatorname{colim} \ker(\pi_I).$$

It will therefore suffice to show that  $\ker(u' \circ \pi_I) = \ker(\pi_I)$  for every finite set I.

Since  $\mathcal{R}$  generates  $\mathcal{C}$ , it will suffice to show that for every,  $C \in \mathcal{R}$ , any map  $C \to \ker(u' \circ \pi_I)$  factors through  $\ker(\pi_I)$ . In other words, we must show that if we are given a diagram

$$C \xrightarrow{\beta} \bigoplus_{i \in I} C_i \xrightarrow{\pi_I} F(M) \xrightarrow{u'} D$$

such that  $u' \circ \pi_I \circ \beta = 0$ , then  $\pi_i \circ \beta = 0$ . The map  $\beta$  corresponds to a family of maps  $\{\beta_i : C \to C_i\}_{i \in I}$ , and the map  $\pi_I$  is given by a family of elements  $\{\alpha_i \in M(C_i)\}_{i \in I}$ . We now observe that  $\pi_I \circ \beta$  is the map given by

$$\gamma = \sum_{i \in I} \alpha_i \beta_i \in M(C).$$

The map  $u' \circ \pi_I \circ \beta$  can be identified with  $u(\gamma) \in G(D)(C) \simeq \operatorname{Hom}_{\mathbb{C}}(C, D)$ . Since the map u is a monomorphism, the equation  $u' \circ \pi_I \circ \beta = 0$  implies  $\gamma = 0$ , so that  $\pi_I \circ \beta$  also vanishes.

**Corollary 8.** Let  $C \in \mathcal{C}$ . The the counit map  $v : FG(C) \to C$  is an isomorphism.

*Proof.* The counit map is adjoint to the isomorphism  $G(C) \to G(C)$ . Lemma 7 implies that v is a monomorphism.

Let  $C' \in \mathbb{R}$ , and let  $\alpha : C' \to C$  be a morphism in  $\mathfrak{C}$ . Then  $\alpha$  can be viewed as an element of G(C)(C'), and therefore determines a map  $\alpha' : C' \to FG(C)$  such that  $v \circ \alpha' = \alpha$ . In other words, every map  $C' \to C$  factors through v if  $C' \in \mathbb{R}$ . Since  $\mathbb{R}$  generates  $\mathfrak{C}$ , we deduce that v is an epimorphism.

Corollary 9. The functor G is fully faithful.

*Proof.* For every pair of objects  $C, D \in \mathcal{C}$ , we have isomorphisms

$$\operatorname{Hom}_{\mathfrak{C}}(C,D) \simeq \operatorname{Hom}_{\mathfrak{C}}(FG(C),D) \simeq \operatorname{Hom}_{\operatorname{Mod}(\mathfrak{R})}(G(C),G(D)).$$

Let us say that an object  $M \in \text{Mod}(\mathcal{R})$  is *free* if it is a direct sum of objects of the form G(C), where  $C \in \mathcal{R}$ . For any  $\mathcal{R}$ -module N, Yoneda's lemma yields an isomorphism

$$\operatorname{Hom}_{\operatorname{Mod}(\mathcal{R})}(G(C), N) = N(C).$$

Since the evaluation functors  $N \mapsto N(C)$  are exact, we conclude that the free objects of  $\operatorname{Mod}(\mathcal{R})$  are projective. Moreover,  $\operatorname{Mod}(\mathcal{R})$  is generated by free objects: for any  $N \in \operatorname{Mod}(\mathcal{R})$ , the map

$$\bigoplus_{\alpha \in N(C)} G(C) \to N$$

is an epimorphism. Consequently, every  $N \in \operatorname{Mod}(\mathcal{R})$  admits a free resolution

$$\ldots \to P_1 \to P_0 \to N$$
.

We can therefore define the left derived functors of F: by definition,  $L^iF(N)$  is the ith homology of the complex

$$\ldots \to F(P_1) \to F(P_0).$$

Since the functor F preserves colimits, we deduce that

$$L^0F(N) \simeq \operatorname{coker}(F(P_1) \to F(P_0)) \simeq F \operatorname{coker}(P_1 \to P_0) \simeq F(N).$$

That is, F is its own 0th derived functor.

For every short exact sequence of  $\mathcal{R}$ -modules

$$0 \to M' \to M \to M'' \to 0$$

we get a long exact sequence of right derived functors

$$\ldots \to L^1 F(M'') \to F(M') \to F(M) \to F(M'') \to 0.$$

Consequently, to prove that F is exact it will suffice to show that the derived functors  $L^iF$  vanish for i > 0. In other words, it will suffice to show:

**Lemma 10.** Suppose given an exact sequence of  $\mathbb{R}$ -modules

$$\ldots \to P_1 \to P_0 \to N$$
,

where each  $P_i$  is free. Then the induced sequence

$$\ldots \to F(P_1) \to F(P_0) \to F(N)$$

is exact in C.

To prove Lemma 10, we note that a long exact sequence is obtained by can be obtained by splicing together short exact sequences

$$0 \to \operatorname{Im}(P_1 \to P_0) \to P_0 \to N$$
$$0 \to \operatorname{Im}(P_2 \to P_1) \to P_1 \to \operatorname{Im}(P_1 \to P_0) \to 0$$

. .

It will suffice to show that the functor F preserves each of these short exact sequences. Since F preserves colimits, it is automatically right exact. So the only question is whether or not F preserves the monic arrows which appear above. This follows from:

**Lemma 11.** Let P be a free  $\mathbb{R}$ -module, and let  $M \subseteq P$ . Then the induced map  $F(M) \to F(P)$  is a monomorphism in  $\mathbb{C}$ .

Proof. We can write  $P = \text{colim}\{P_{\alpha}\}$ , where each  $P_{\alpha}$  is a finitely generated free module. Let  $M_{\alpha} = M \cap P_{\alpha}$ . Then the map  $F(M) \to F(P)$  is a filtered colimit of maps of the form  $F(M_{\alpha}) \to F(P_{\alpha})$ . Since the collection of monomorphisms in  $\mathcal{C}$  is stable under filtered colimits, we may reduce to the case where  $P = P_{\alpha}$  is finitely generated.

In this case, we can choose a finite collection of objects  $\{C_i \in \mathbb{R}\}_{1 \leq i \leq n}$  such that  $P = \bigoplus_{1 \leq i \leq n} G(C_i)$ . Let  $C = \bigoplus_{1 \leq i \leq n} C_i$ , so that P = G(C). Then

$$F(P) \simeq \bigoplus_{1 \le i \le n} FG(C_i) \simeq \bigoplus_{1 \le i \le n} C_i \simeq C.$$

The map  $F(M) \to F(P) \simeq C$  is adjoint to the inclusion  $M \subseteq P \simeq G(C)$ , and is therefore a monomorphism by Lemma 7.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Injectivity of $H^*(BV)$ (Lecture 9)

Let n be a nonnegative integer, and let  $\operatorname{Sq}^I$  be an element of the Steenrod algebra  $\mathcal{A}$ . We have seen that  $\operatorname{Sq}^I$  determines a map  $\operatorname{Sym}^n \to \operatorname{Sym}^*$  in the category  $\operatorname{Fun} = \operatorname{Fun}(\operatorname{Vect}^f, \operatorname{Vect})$ , where  $\operatorname{Vect}$  is the category of  $\mathbf{F}_2$ -vector spaces and  $\operatorname{Vect}^f \subseteq \operatorname{Vect}$  is the category of finite dimensional  $\mathbf{F}_2$ -vector spaces. If we keep track of degrees, we can be more precise:  $\operatorname{Sq}^I$  determines a map  $\operatorname{Sq}^n \to \operatorname{Sq}^{n+\operatorname{deg}(I)}$ . This map vanishes if the excess of I is larger than n. Moreover, we proved:

**Proposition 1.** Let m and n be nonnegative integers. Then  $\operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n,\operatorname{Sym}^m)$  has a basis given by the Steenrod operations  $\{\operatorname{Sq}^I\}$ , where I ranges over positive admissible sequences of degree m-n and excess  $\leq n$ .

In particular, there are no nontrivial natural transformations from Sym<sup>n</sup> to Sym<sup>m</sup> for m < n.

We can express Proposition 1 in a slightly different way. Let F(n) denote the free unstable  $\mathcal{A}$ -module on a single generator  $\nu_n$ . Then the expressions  $\{\operatorname{Sq}^I\nu_n\}$  form a basis for F(n), where I ranges over the collection of positive admissible sequences of excess  $\leq n$ . If we restrict our attention to admissible sequences of degree m-n, then we get a basis for the mth graded piece  $F(n)^m \simeq \operatorname{Hom}_{\mathcal{A}}(F(m), F(n))$ . We may therefore reformulate Proposition 1 as follows:

**Proposition 2.** Let m and n be nonnegative integers. Then there is a canonical isomorphism

$$\operatorname{Hom}_{\operatorname{Fun}}(\operatorname{Sym}^n, \operatorname{Sym}^m) \simeq \operatorname{Hom}_{\mathcal{A}}(F(m), F(n)).$$

Let  $\mathcal{U}$  denote the category of unstable modules over the Steenrod algebra. Unwinding the definitions, we see that the isomorphism of Proposition 2 is compatible with composition. It therefore defines an *anti-equivalence* between the full subcategory of Fun spanned by the objects  $\{\operatorname{Sym}^n\}_{n\geq 0}$  and the full subcategory of  $\mathcal{U}$  spanned by the objects  $\{F(n)\}_{n\geq 0}$ . We wish to apply the results of the last lecture to this situation. First, we need to convert the anti-equivalence of Proposition 2 into a covariant equivalence.

**Definition 3.** Let  $F: \operatorname{Vect}^f \to \operatorname{Vect}$  be a functor. We let DF denote the functor

$$F \mapsto F(V^{\vee})^{\vee}$$
.

where  $V^{\vee}$  denotes the vector space dual to  $\vee$ . We will refer to DF as the dual to F.

We note that DF is again a covariant functor from  $Vect^f$  to Vect, and the the construction

$$F \mapsto DF$$

determines a contravariant functor from Fun to itself. Moreover, for every functor F there is a canonical map  $F \mapsto DDF$ , which is an isomorphism if and only if each of the vector spaces F(V) is finite-dimensional. It follows that if F and G take values in finite dimensional vector spaces, then we have a canonical isomorphism

$$\operatorname{Hom}_{\operatorname{Fun}}(F,G) \simeq \operatorname{Hom}_{\operatorname{Fun}}(DG,DF).$$

(In fact, we have such an isomorphism whenever the values of G are finite-dimensional.)

**Example 4.** For each  $n \geq 0$ , we let  $\Gamma^n : \operatorname{Vect}^f \to \operatorname{Vect}$  denote the functor

$$V \mapsto (V^{\otimes n})^{\Sigma_n}$$
.

Then  $\Gamma^n$  is isomorphic to the dual  $D\operatorname{Sym}^n$ .

We can reformulate Proposition 2 as follows:

**Proposition 5.** Let m and n be nonnegative integers. Then there is a canonical isomorphism

$$\operatorname{Hom}_{\operatorname{Fun}}(\Gamma^m, \Gamma^n) \simeq \operatorname{Hom}_{\mathcal{A}}(F(m), F(n)).$$

Let  $\mathcal{R}$  denote the full subcategory of Fun spanned by the functors  $\{\Gamma^n\}_{n\geq 0}$ . We would like to apply Kuhn's many-object version of the Gabriel-Popesco theorem to the subcategory  $\mathcal{R} \subseteq \text{Fun}$ . Unforumately, the hypotheses of the theorem are not satisfied: the category Fun is not generated by the objects  $\{\Gamma^n\}_{n\geq 0}$ . We can remedy the situation by passing to a suitable subcategory of Fun.

**Definition 6.** For every functor  $F \in \text{Fun}$ , we define a new functor  $\Delta(F)$  by the formula

$$\Delta(F)(V) = \ker(F(V \oplus \mathbf{F}_2) \to F(V)).$$

We say that a functor  $F \in \text{Fun}$  is polynomial of degree  $\leq n$  if  $\Delta^{n+1}(F)$  vanishes.

We observe that for any functor F, we have a canonical splitting

$$F(V \oplus \mathbf{F}_2) \simeq F(V) \oplus \Delta(F)(V).$$

It follows the functor  $F \mapsto \Delta(F)$  is exact. Moreover, it is clear that the functor  $\Delta$  commutes with infinite direct sums. From this we immediately deduce:

**Lemma 7.** The collection of polynomial functors of degree  $\leq n$  is closed under the formation of subobjects, quotient objects, and extensions in the category Fun.

**Remark 8.** Let  $F \in \text{Fun}$  be a functor which takes values in finite dimensional vector space, and let  $d_F : \mathbf{Z}_{>0} \to \mathbf{Z}_{>0}$  be the function defined by the formula

$$d_F(n) = \dim F(\mathbf{F}_2^n).$$

We note that  $d_{\Delta(F)}(n) = d_F(n+1) - d_F(n)$ , and that F vanishes if and only if  $d_F$  vanishes. It follows that F is polynomial of degree  $\leq n$  if and only if the function  $d_F$  is a polynomial of degree  $\leq n$ .

**Example 9.** Let  $n \geq 0$ . Then

$$d_{\operatorname{Sym}^n}(k) = d_{\Gamma^n}(k) = \binom{n+k-1}{n}.$$

Consequently, the functors  $\operatorname{Sym}^n$  and  $\Gamma^n$  are polynomial of degree exactly n.

**Lemma 10.** For every functor  $F \in \text{Fun}$ , there exists a maximal subfunctor  $F^{(n)} \subseteq F$  which is polynomial of degree  $\leq n$ .

*Proof.* Let  $F^{(n)}(V)$  denote the subspace of F(V) consisting of those vectors v with the following property:

(\*) There exists a functor  $G \in \text{Fun}$  which is polynomial of degree  $\leq n$ , and a natural transformation  $G \to F$  such that v lies in the image of the induced map  $G(V) \to F(V)$ .

Since the collection of polynomial functors of degree  $\leq n$  is stable under sums, we may assume that there exists a single natural transformation  $\alpha: G \to F$ , where G is polynomial of degree  $\leq n$ , and the image of each map  $G(V) \to F(V)$  coincides with  $F^{(n)}(V)$ . We can then define  $F^{(n)} = \text{Im}(\alpha)$ . Then  $F^{(n)}$  is a quotient of G, and therefore polynomial of degree  $\leq n$ . It is easy to see that  $F^{(n)}$  has the desired properties.  $\square$ 

**Definition 11.** A functor  $F \in \text{Fun}$  is *analytic* if it is the union of the polynomial subfunctors  $\{F^{(n)}\}_{n\geq 0}$ . Let Fun<sup>an</sup> denote the full subcategory of Fun spanned by the analytic functors.

**Lemma 12.** The subcategory Fun<sup>an</sup>  $\subseteq$  Fun is closed under the formation of quotients, subobjects, and direct sums in Fun. In particular, Fun<sup>an</sup> is an abelian category.

*Proof.* Suppose given an exact sequence

$$0 \to F' \to F \to F'' \to 0.$$

For each  $n \geq 0$ , we have an induced exact sequence

$$0 \to F' \cap F^{(n)} \to F^{(n)} \to \operatorname{Im}(F^{(n)} \to F'') \to 0.$$

Since the middle term in this sequence is polynomial of degree  $\leq n$ , we conclude that the outer terms are also polynomial of degree  $\leq n$ . Assume that F is analytic. Passing to the direct limit over n, we deduce that F' and F'' can be obtained as the direct limit of sequences of polynomial subfunctors, and are therefore analytic as well.

To prove the assertion regard sums, let us suppose that  $F = \bigoplus_{\alpha} F_{\alpha}$ . If each  $F_{\alpha}$  can be obtained as the direct limit of a sequence of polynomial subfunctors  $F_{\alpha}^{(n)}$ , then F can be obtained as the direct limit of the polynomial functors

$$\bigoplus_{\alpha} F_{\alpha}^{(n)}$$
.

We will need the following result, whose proof we defer until the next lecture:

**Proposition 13.** The category Fun<sup>an</sup> of analytic functors is generated by the objects  $\{\Gamma^n\}_{n\geq 0}$ .

Combining this with the results of the previous lecture, we obtain the following:

Corollary 14. Let  $\mathcal{R} \subseteq \text{Fun}^{\text{an}}$  denote the full subcategory spanned by the objects  $\{\Gamma^n\}_{n\geq 0}$ . Then we have a pair of adjoint functors

$$F: \operatorname{Mod}(\mathfrak{R}) \to \operatorname{Fun}^{\operatorname{an}}$$

$$G: \operatorname{Fun}^{\operatorname{an}} \to \operatorname{Mod}(\mathcal{R})$$

where F is exact and G is fully faithful.

*Proof.* The only other point to check is that  $\operatorname{Fun}^{\operatorname{an}}$  is a Grothendieck abelian category. Proposition 13 implies that  $\operatorname{Fun}^{\operatorname{an}}$  has a set of generators, so we just need to know that filtered colimits in  $\operatorname{Fun}^{\operatorname{an}}$  are exact. Since  $\operatorname{Fun}^{\operatorname{an}}$  is stable under colimits in  $\operatorname{Fun}$ , it suffices to show that filtered colimits in  $\operatorname{Fun}$  are exact. This follows from the observation that filtered colimits are exact in the category Vect.

The real point of Corollary 14 is that the category  $\operatorname{Mod}(\mathcal{R})$  can be identified with something concrete: namely, the category of unstable  $\mathcal{A}$ -modules. Let us sketch this identification. According to Proposition 5, we can identify  $\mathcal{R}$  with the full subcategory of  $\mathcal{U}$  spanned by the modules  $\{F(n)\}_{n\geq 0}$ . Let M be an  $\mathcal{R}$ -module: that is, a contravariant functor from  $\mathcal{R}$  to the category of abelian groups. We then let  $M^n$  denote the value of M on the object  $F(n) \in \mathcal{R}$ . For every n and every Steenrod operation  $\operatorname{Sq}^I$ , we have an object  $\operatorname{Sq}^I \nu_n \in F(n)$ , which we can identify with a map  $F(n + \deg(I)) \to F(n)$  in  $\mathcal{R}$ . This determines a map

$$M^n \to M^{n+\deg(I)}$$

It is easy to see that this endows M with the structure of a graded A-module. Moreover, since  $\operatorname{Sq}^I \nu_n$  vanishes whenever the excess of I is greater than n, we conclude that M is unstable. We leave it to the reader to verify that this determines an equivalence  $\operatorname{Mod}(\mathfrak{R}) \simeq \mathfrak{U}$ . We can therefore restate Corollary 14 as follows:

Corollary 15. There exists a pair of adjoint functors

$$F:\mathcal{U}\to\operatorname{Fun}^{\mathrm{an}}$$

$$G:\operatorname{Fun}^{\mathrm{an}} \to \mathcal{U}$$

where F is exact and G is fully faithful.

We conclude with an application of Corollary 15. Let V be a finite dimensional  $\mathbf{F}_2$ -vector space. Let  $P_V \in \text{Fun}$  be the functor given by the formula  $P_V(W) = \mathbf{F}_2[\text{Hom}(V,W)]$ , where  $\mathbf{F}_2[\text{Hom}(V,W)]$  denotes the free  $\mathbf{F}_2$ -vector space generated by the set Hom(V,W). It follows from Yoneda's lemma that for any  $F \in \text{Fun}$ , we have a canonical isomorphism

$$\operatorname{Hom}_{\operatorname{Fun}}(P_V, F) \simeq F(V).$$

The functors  $P_V$  form a set of projective generators for Fun. We let  $I_V$  denote the dual  $DP_{V^{\vee}}$ , so we have isomorphisms

$$\operatorname{Hom}_{\operatorname{Fun}}(F, I_V) \simeq \operatorname{Hom}_{\operatorname{Fun}}(F, DP_{V^{\vee}}) \simeq \operatorname{Hom}_{\operatorname{Fun}}(P_{V^{vee}}, DF) \simeq DF(V^{\vee}) = F(V)^{\vee}.$$

This is evidently an exact functor of F, so that  $I_V$  is an injective object of Fun. We observe that  $I_V$  can be described by the formula

$$W \mapsto \mathbf{F}_2^{\mathrm{Hom}(W,V)}$$
.

**Proposition 16.** Let V be a finite dimensional vector space over  $\mathbf{F}_2$ . Then the functor  $I_V$  is analytic.

*Proof.* We observe that the category Fun is equipped with a tensor product, described by the formula  $(F \otimes F')(V) = F(V) \otimes F'(V)$ . If F and F' are polynomial of degrees  $\leq n$  and n', respectively, then  $F \otimes F'$  is polynomial of degree  $\leq n + n'$ . It follows that a tensor product of analytic functors is analytic. Moreover, we have a canonical isomorphism  $I_{V \oplus V'} \simeq I_{V} \otimes I_{V'}$ . It will therefore suffice to prove Proposition 16 in the case where V has dimension 1. In this case, we can identify  $I_{V}$  with the functor

$$W\mapsto \mathbf{F}_2^{W^{\vee}}.$$

We now observe that there is a canonical surjection

$$\operatorname{Sym}^* \to I_V$$
,

since every function  $W^{\vee} \to \mathbf{F_2}$  is given by some polynomial. Since  $\operatorname{Sym}^* \simeq \oplus_n \operatorname{Sym}^n$  is analytic, we conclude that  $I_V$  is analytic as desired.

It follows that for every finite dimensional  $\mathbf{F}_2$ -vector space V, the functor  $I_V$  is an injective object of Fun<sup>an</sup>. Since the functor F is exact, we deduce that the functor

$$M \mapsto \operatorname{Hom}_{\mathcal{U}}(M, GI_V) \simeq \operatorname{Hom}_{\operatorname{Fun}}(FM, I_V)$$

is exact. In other words,  $GI_V$  is an injective object in the category  $\mathcal{U}$  of unstable modules over the Steenrod algebra. It is easy to identify this object: we have

$$(GI_V)^n = \operatorname{Hom}_{\operatorname{Fun}}(\Gamma^n, I_V) \simeq \Gamma^n(V)^{\vee} = \operatorname{Sym}^n(V^{\vee}) \simeq \operatorname{H}^n(BV).$$

It is not hard to show that this identification is compatible with the action of the Steenrod algebra. Consequently, we have proven the following:

**Proposition 17.** Let V be a finite dimensional vector space over  $\mathbf{F}_2$ . Then the cohomology ring  $H^*(BV)$  is an injective object of the category  $\mathcal{U}$ .

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Generating Analytic Functors (Lecture 10)

Let  $\operatorname{Fun}^{\operatorname{an}}$  denote the category of analytic functors from  $\operatorname{Vect}^f$  to  $\operatorname{Vect}$ , as defined in the last lecture. Our goal in this lecture is to prove the following, which we stated without proof in the last lecture:

**Theorem 1.** The abelian category Fun<sup>an</sup> is generated by the divided power functors  $\{\Gamma^n\}_{n>0}$ .

Let us say that a functor  $F: \operatorname{Vect}^f \to \operatorname{Vect}$  is good if there exists a surjection

$$\bigoplus_{\alpha} \Gamma^{n_{\alpha}} \to F$$
.

Clearly, every good functor is analytic. Theorem 1 asserts the converse: every analytic functor is good. We observe that the collection of good functors is stable under quotients and direct sums. Consequently, every colimit of good functors is good. Since every analytic functor F is the direct limit of its polynomial subfunctors  $F^{(n)} \subseteq F$ , Theorem 1 can be reformulated as follows:

**Proposition 2.** Every polynomial functor  $F : \text{Vect}^f \to \text{Vect is good.}$ 

Now recall the projective objects  $P_V \in \text{Fun}$ , defined in the last lecture by the formula  $P_V(W) = \mathbf{F}_2\{\text{Hom}_{\mathbf{F}_2}(V,W)\}$ . These functors are not analytic, but they generate the category Fun of *all* functors from Vect<sup>f</sup> to Vect. In particular, we have a surjection

$$\bigoplus_{i\in I} P_{V_i} \to F$$

in the category Fun. In particular, we can write F as a filtered colimit of subfunctors

$$F_{I_0} = \mathrm{i} m(\bigoplus_{i \in I_0} P_{V_i} \to F) \subseteq F.$$

where  $I_0$  ranges over finite subsets of I. Since the collection of good functors is stable under colimits, it will suffice to show that each  $F_{I_0}$  is a good functor. Proposition 2 is now an immediate consequence of the following assertion:

**Proposition 3.** Let F be a polynomial functor, and suppose there exists a surjection

$$\bigoplus_{i\in I} P_{V_i} \to F$$
,

where the set I is finite. Then there exists a surjection

$$\bigoplus_{\alpha \in A} \Gamma^{n_{\alpha}} \to F$$
,

where the set A is finite.

Let us say that a functor  $G \in \text{Fun}$  is *locally finite* if G(V) is finite dimensional for each  $V \in \text{Vect}^f$ . The functors  $P_{V_i}$  are locally finite, as are the functors  $\{\Gamma^n\}_{n\geq 0}$ . The duality functor D induces a (contravariant) equivalence from the category of locally finite functors to itself. Moreover, we observe that if G is locally finite, then we have an equality of dimension functors  $d_G = d_{DG}$ , so that G is polynomial if and only if G is polynomial. Proposition 3 can therefore be reformulated in the following dual form:

**Proposition 4.** Let F be a polynomial functor, and suppose that there exists an injection

$$F \hookrightarrow \bigoplus_{i \in I} I_{V_i}$$

where I is finite. Then there exists an injection

$$F \hookrightarrow \bigoplus_{\alpha \in A} \operatorname{Sym}^{n_{\alpha}}$$

where the set A is finite.

For each  $i \in I$ , let  $F_i$  denote the image of F in  $I_{V_i}$ . Then  $F_i$  is a quotient of F, and therefore a polynomial functor. Moreover, we have an inclusion  $F \hookrightarrow \bigoplus_{i \in I} F_i$ . It will therefore suffice to prove Proposition 4 after replacing F by each  $F_i$ ; in other words, we may suppose that I consists of a single element. We are therefore reduced to proving the following special case of Proposition 4:

**Proposition 5.** Let V be a finite dimensional vector space over  $\mathbf{F}_2$ , and let F be a polynomial subfunctor of  $I_V$ . Then there exists an injection

$$F \hookrightarrow \bigoplus_{\alpha \in A} \operatorname{Sym}^{n_{\alpha}}$$

where the set A is finite.

Let us now suppose that V has dimension n, so that the functor  $I_V$  can be written as a tensor product

$$I_{\mathbf{F}_2} \otimes I_{\mathbf{F}_2} \otimes \ldots \otimes I_{\mathbf{F}_2}$$
.

As we observed last time, there is a canonical surjection

$$\operatorname{Sym}^* \simeq \bigoplus_{n>0} \operatorname{Sym}^n \to I_{\mathbf{F}_2}$$
.

For  $0 < n \le \infty$ , let  $S^n \subseteq I_{\mathbf{F}_2}$  denote the image of the direct sum

$$\bigoplus_{1 \leq i \leq n} \operatorname{Sym}^i$$

in  $I_{\mathbf{F}_2}$ . Then we have a direct sum decomposition  $I_{\mathbf{F}_2} \simeq \operatorname{Sym}^0 \oplus S^{\infty}$ , so that  $I_V$  can be written as a finite sum  $\oplus_{j \in J} (S^{\infty})^{\otimes n_j}$ . We now apply our previous argument: for each  $j \in J$ , let  $F_j$  denote the image of F in  $(S^{\infty})^{\otimes n_j}$ . Then we have a monomorphism  $F \to \oplus_{j \in J} F_j$ , and it will suffice to prove the result after applying F by  $F_j$ . In other words, we may reformulate Proposition 5 as follows:

**Proposition 6.** Let F be a polynomial functor, and suppose there exists an injection

$$F \hookrightarrow S^{\infty} \otimes \ldots \otimes S^{\infty}$$
.

Then there exists an injection

$$F \hookrightarrow \operatorname{Sym}^m$$

for some m > 0.

We observe that the functor  $S^{\infty}$  is the direct limit of the subfunctors  $\{S^k \subseteq S^{\infty}\}_{k\geq 1}$ . Consequently, F is the direct limit of the subfunctors

$$F \cap (S^k \otimes S^k \otimes \ldots \otimes S^k).$$

We claim that one of these subfunctors must coincide with F. This is a consequence of the following general fact:

**Lemma 7.** Every locally finite polynomial functor F is a Noetherian object of Fun: in other words, there are no infinite ascending chains of subfunctors

$$F_0 \subset F_1 \subset \ldots \subset F$$
.

*Proof.* Let F be a polynomial functor of degree  $\leq m$ . Then the dimension function  $d_F$  is a polynomial of degree  $\leq m$ , and is therefore determined by its values on  $\{0, 1, \ldots, m\}$ . If we have an inclusion  $F' \subseteq F$ , then F' is also a polynomial of degree  $\leq m$  and we have an inequality

$$d_{F'}(0) + \ldots + d_{F'}(m) \le d_F(0) + \ldots + d_F(m)$$

If equality holds, then  $d_{F'} = d_F$ , so that F' = F. Thus every chain of proper subfunctors of F has length at most  $d_F(0) + \ldots + d_F(m)$ .

We can now Proposition 6 to the following:

**Proposition 8.** Let F be a functor of the form  $(S^k)^{\otimes n}$ , where  $k \geq 1$  and  $n \geq 0$ . Then there exists a monomorphism  $F \hookrightarrow \operatorname{Sym}^m$  for some  $m \geq 0$ .

Proposition 8 is obvious if n = 0 (in that case,  $F \simeq \operatorname{Sym}^0$  and we can take m = 0). The main difficulty is in the case n = 1, where we need the following result:

**Proposition 9.** Let  $k \geq 0$ . Then there exists a monomorphism of functors  $S^{k+1} \hookrightarrow \operatorname{Sym}^{2^k}$ .

We can reduce the general case to Proposition 9 using the following lemma:

**Lemma 10.** Let m, m' > 0. Then there exists m'' > 0 and a monomorphism of functors

$$\operatorname{Sym}^m \otimes \operatorname{Sym}^{m'} \to \operatorname{Sym}^{m''}$$
.

*Proof.* For  $q \geq 0$ , we have an iterated Frobenius map

$$\operatorname{Sym}^m \to \operatorname{Sym}^{2^q m}$$

$$f \mapsto f^{2^q}$$
.

It now suffices to observe that the composite map

$$\operatorname{Sym}^m \otimes \operatorname{Sym}^{m'} \to \operatorname{Sym}^{2^q m} \otimes \operatorname{Sym}^{m'} \hookrightarrow \operatorname{Sym}^{w^q m + m'}$$

is a monomorphism for  $2^q > m'$ .

We now prove Proposition 9 using an explicit construction of Kuhn. We note that the kernel of the map  $\operatorname{Sym}^*(V) \to I_{\mathbf{F}_2}(V)$  is generated by  $v^2 - v$  for  $v \in V$ . We can therefore describe the space  $S^{k+1}(V)$  as the quotient of  $\bigoplus_{1 \leq d \leq k+1} V^{\otimes d}$  by the following relations:

(1) If  $\sigma \in \Sigma_d$  is a permutation, then

$$v_1 \otimes \ldots \otimes v_d = v_{\sigma(1)} \otimes \ldots \otimes v_{\sigma(d)}$$

in  $S^{k+1}(V)$ .

(2) If d < k, and  $v \in V$ , then

$$v_1 \otimes \ldots \otimes v_d \otimes v = v_1 \otimes \ldots \otimes v_d \otimes v \otimes v$$

in  $S^{k+1}(V)$ .

We define a map  $\theta: \bigoplus_{1 < < k+1} V^{\otimes d} \to \operatorname{Sym}^{2^k}(V)$  by the formula

$$\theta(v_1 \otimes \ldots \otimes v_d) = \sum_{2^{i_1} + \ldots + 2^{i_d} = 2^k} v_1^{2^{i_1}} \ldots v_d^{2^{i_d}},$$

It is clear that  $\theta$  is compatible with the relations of type (1). We claim that  $\theta$  is also compatible with relations of the type (2): that is, if d < k, then

$$\theta(v_1 \otimes \ldots \otimes v_d \otimes v) = \theta(v_1 \otimes \ldots \otimes v_d \otimes v \otimes v).$$

To prove this, we observe that the right hand side is a sum of terms associated to sequences of integers  $(i_1,\ldots,i_d,j,k)$  where  $2^k=2^{i_1}+\ldots+2^{i_d}+2^j+2^k$ . The terms associated to  $(i_1,\ldots,i_d,j,k)$  and  $(i_1,\ldots,i_d,k,j)$  cancel if  $j\neq k$ , while the terms associated to the sequence  $(i_1,\ldots,i_d,j,j)$  appear on the left hand side as associated to the sequence  $(i_1,\ldots,i_d,j+1)$ . To complete the proof, it will suffice to show that no other terms appear on the left hand side. In other words, we must show that if  $2^{i_1}+\ldots+2^{i_d}+2^j=2^k$ , then j>0. If not, we have  $2^{i_1}+\ldots+2^{i_d}=2^k-1$ , which has k nonzero digits in its base 2-expansion. Since each term in the sum is a power of 2, the sum must include at least k terms, which contradicts our assumption that d< k.

We have now shown that  $\theta$  is compatible with the relations (1) and (2), and therefore defines a map  $\overline{\theta}: S^{k+1}(V) \to \operatorname{Sym}^{2^k}(V)$ . This map is evidently functorial in V, and so defines a natural transformation of functors  $\psi: S^{k+1} \to \operatorname{Sym}^{2^k}$ . To complete the proof of Proposition 9, it will suffice to show that this natural transformation is a monomorphism. In other words, we must show that each of the maps  $S^{k+1}(V) \to \operatorname{Sym}^{2^k}(V)$  is injective.

To prove this, we will need the following lemma:

**Lemma 11.** Let F and F' be nonzero subfunctors of  $S^{\infty}$ . Then  $F \cap F' \neq 0$ .

*Proof.* We compute that the endomorphism ring

$$R = \operatorname{Hom}_{\operatorname{Fun}}(I_{\mathbf{F}_2}, I_{\mathbf{F}_2}) \simeq I_{\mathbf{F}_2}(\mathbf{F}_2)^{\vee} \simeq \mathbf{F}_2 \oplus \mathbf{F}_2$$

has dimension 2 over the field  $\mathbf{F}_2$ . The endomorphism ring  $S^{\infty}$  is properly contained in R, and therefore has dimension 1 over  $\mathbf{F}_2$ . It follows that every nonzero endomorphism of  $S^{\infty}$  is an isomorphism.

Suppose  $F \cap F' = 0$ . Then the induced map  $F \to S^{\infty}/F'$  is a monomorphism. Since  $S^{\infty}$  is injective, we can solve the lifting problem depicted in the diagram

$$F \xrightarrow{f} S^{\infty}$$

$$S^{\infty}/F'.$$

Composing f with the projection map  $S^{\infty} \to S^{\infty}/F'$ , we obtain an endomorphism  $\overline{f}: S^{\infty} \to S^{\infty}$ . This endomorphism is not an isomorphism, since  $\overline{f}|F'=0$ . Consequently,  $\overline{f}=0$ . Since  $\overline{f}|F$  is the identity, we deduce that F=0, a contradiction.

Let us apply Lemma 11 in the case  $F = \operatorname{Sym}^1 \simeq S^1 \subseteq S^\infty$  and  $F' = \ker(\psi)$ . If  $\psi$  is not a monomorphism, then  $\ker(\psi)$  is nonzero, so  $F \cap F' \neq 0$ . In other words, for some vector space V the composite map

$$\operatorname{Sym}^{1}(V) \to S^{k+1}(V) \xrightarrow{\overline{\theta}} \operatorname{Sym}^{2^{k}}(V)$$

is not injective. But this map is simply the iterated Frobenius  $v \mapsto v^{2^k}$ , and we obtain a contradiction.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Tensor Products and Algebras (Lecture 11)

Recall that if X is a topological space, then the cohomology  $H^*(X)$  has the structure of an unstable module over the Steenrod algebra A. Moreover,  $H^*(X)$  is equipped with a multiplication which satisfies the Cartan formula:

$$\operatorname{Sq}^{n}(xy) = \sum_{n=n'+n''} \operatorname{Sq}^{n'}(x) \operatorname{Sq}^{n''}(y).$$

In other words, the multiplication map

$$H^*(X) \otimes H^*(X) \to H^*(X)$$

is compatible with the Steenrod operations  $Sq^n$ , if we let  $Sq^n$  act by the formula

$$\operatorname{Sq}^{n}(x \otimes y) = \sum_{n=n'+n''} \operatorname{Sq}^{n'}(x) \otimes \operatorname{Sq}^{n''}(y).$$

Our goal in this lecture is to prove that the preceding formula endows  $H^*(X) \otimes H^*$  with the structure of an unstable module over the Steenrod algebra. Moreover, a similar result is true for any pair M, N of unstable modules over the big Steenrod algebra  $\mathcal{A}^{\text{Big}}$ .

**Definition 1.** We let  $\mathcal{A}^{Big}$  denote the big Steenrod algebra, and  $\mathcal{U}^{Big}$  the category of (graded) unstable  $\mathcal{A}^{Big}$ -modules.

Let R denote the free  $\mathbf{F}_2$ -algebra  $\mathbf{F}_2[\ldots,\operatorname{Sq}^{-1},\operatorname{Sq}^0,\operatorname{Sq}^1,\ldots]$ , so that  $\mathcal{A}^{\operatorname{Big}}$  is the quotient of R by the ideal  $I\subseteq R$  generated by the Adem relations.

For every pair of objects  $M, N \in \mathcal{U}^{Big}$ , we let R act on  $M \otimes N$  by the formula

$$\operatorname{Sq}^{k}(x \otimes y) = \sum_{k=k'+k''} \operatorname{Sq}^{k'}(x) \otimes \operatorname{Sq}^{k''}(y).$$

Observe that the sum appearing above is automatically finite, since  $\operatorname{Sq}^{k'}(x) \otimes \operatorname{Sq}^{k''}(y)$  vanishes if  $k' > \deg(x)$  or  $k'' > \deg(y)$ . The same argument shows that  $M \otimes N$  is unstable, in the sense that  $\operatorname{Sq}^k(x \otimes y) = 0$  for  $k > \deg(x) + \deg(y)$ .

We would like to prove the following:

**Theorem 2.** For any pair of objects  $M, N \in \mathcal{U}^{Big}$ , the tensor product  $M \otimes N$  is again an unstable  $\mathcal{A}^{Big}$ -module.

In other words, we wish to show that the action of R on  $M \otimes N$  factors through the quotient  $R/I \simeq \mathcal{A}^{\mathrm{Big}}$ . In other words, we wish to show that the submodule  $I(M \otimes N) \subseteq M \otimes N$  vanishes. The submodule  $I(M \otimes N)$  is generated by the submodules  $I(x \otimes y) \subseteq M \otimes N$ , where x and y are homogeneous elements of M and N. Let  $m = \deg(x)$  and  $n = \deg(y)$ , so that x and y determine maps  $F^{\mathrm{Big}}(m) \to M$ ,  $F^{\mathrm{Big}}(n) \to N$ . Here  $F^{\mathrm{Big}}(k)$  denotes the free unstable  $\mathcal{A}^{\mathrm{Big}}$ -module on a single generator  $\overline{\nu}_k$  in degree k. The submodule  $I(x \otimes y) \subseteq M \otimes N$  is a quotient of  $I(\overline{\nu}_m \otimes \overline{\nu}_n) \subseteq F^{\mathrm{Big}}(m) \otimes F^{\mathrm{Big}}(n)$ . It will therefore suffice to prove that this latter submodule vanishes.

For every integer k, let  $\widetilde{\mathbf{F}^{\mathrm{Big}}}(k)$  denote the free R-module on a single generator  $\widetilde{\nu}_k$ , so that  $\widetilde{\mathbf{F}^{\mathrm{Big}}}(k)$  has a basis consisting of expressions  $\{\operatorname{Sq}^I \widetilde{\nu}_k\}$  where I ranges over all sequences of integers. We have canonical quotient maps

$$\widetilde{\mathbf{F}^{\mathrm{Big}}}(k) \to \mathbf{F}^{\mathrm{Big}}(k) \to F(k).$$

The construction of Definition 1 produces for us a map

$$\psi_{m,n}: \widetilde{\mathbf{F}^{\mathrm{Big}}}(m+n) \to \mathbf{F}^{\mathrm{Big}}(m) \otimes \mathbf{F}^{\mathrm{Big}}(n)$$

We wish to show that  $\psi_{m,n}$  factors through  $F^{Big}(m+n)$ .

In a previous lecture, we defined a shift isomorphism

$$\widetilde{S}: \widetilde{\mathrm{F}^{\mathrm{Big}}}(k) \to \widetilde{\mathrm{F}^{\mathrm{Big}}}(k+1)$$

by the formula

$$\operatorname{Sq}^{i_k} \dots \operatorname{Sq}^{i_0} \widetilde{\nu}_k \mapsto \operatorname{Sq}^{i_k+2^k} \dots \operatorname{Sq}^{i_0+1} \widetilde{\nu}_{k+1}$$

and showed that  $\widetilde{S}$  covers and isomorphism  $S: \mathcal{F}^{\mathrm{Big}}(k) \to \mathcal{F}^{\mathrm{Big}}(k+1)$ .

Suppose (for a contradiction) that there exists z in the kernel of the projection  $F^{\overline{\text{Big}}}(m+n) \to F^{\overline{\text{Big}}}(m+n)$  such that  $\psi(z) \neq 0$ . Then we can write  $\psi(z)$  as a nontrivial linear combination  $\sum \operatorname{Sq}^I \overline{\nu}_m \otimes \operatorname{Sq}^J \overline{\nu}_n$ , where I and J range over (finitely many) admissible sequences of integers having excess  $\leq m$  and  $\leq n$ , respectively. Consequently, for  $p \gg 0$ , we can write  $(S \otimes S)^p(\psi z)$  as a nontrivial linear combination  $\sum \operatorname{Sq}^{I'} \overline{\nu}_{m+p} \otimes \operatorname{Sq}^{J'} \overline{\nu}_{n+p}$ , where the sequences I' and J' consist entirely of positive integers. It follows that the image of  $\psi(z)$  under the composite map

$$F^{Big}(m) \otimes F^{Big}(n) \stackrel{S^p \otimes S^p}{\to} F^{Big}(m+p) \otimes F^{Big}(n+p) \to F(m+p) \otimes F(n+p)$$

is nonzero.

We now observe that the diagram

$$\widetilde{\mathbf{F}^{\mathrm{Big}}}(m+n) \xrightarrow{\psi_{m,n}} \mathbf{F}^{\mathrm{Big}}(m) \otimes \mathbf{F}^{\mathrm{Big}}(n) \\
\downarrow \widetilde{S}^{2p} \qquad \qquad \downarrow S^{p} \otimes S^{p} \\
\widetilde{\mathbf{F}^{\mathrm{Big}}}(m+n+2p) \xrightarrow{\psi_{m+p}, n \to 0} \widetilde{\mathbf{F}^{\mathrm{Big}}}(m+p) \otimes \mathbf{F}^{\mathrm{Big}}(m+p)$$

commutes, where the horizontal arrows are defined as in Notation 1. Replacing z by  $\tilde{S}^{2p}(z)$  if necessary, we may assume that the composition

$$\widetilde{\mathrm{F}^{\mathrm{Big}}}(m+n) \overset{\psi_{m,n}}{\to} \mathrm{F}^{\mathrm{Big}}(m) \otimes \mathrm{F}^{\mathrm{Big}}(n) \to F(m) \otimes F(n)$$

does not vanish on z.

We have seen that there are injections  $F(m) \hookrightarrow \mathrm{H}^*((\mathbf{R}P^{\infty})^m)$  and  $F(n) \hookrightarrow \mathrm{H}^*((\mathbf{R}P^{\infty})^n)$ . Amalgamating these, we obtain an injection  $F(m) \otimes F(n) \hookrightarrow \mathrm{H}^*((\mathbf{R}P^{\infty})^{m+n})$ . Since the Cartan formula holds in  $\mathrm{H}^*((\mathbf{R}P^{\infty})^{m+n})$ , the composite map

$$\phi: \widetilde{\mathbf{F}^{\mathrm{Big}}}(m+n) \overset{\psi_{m,n}}{\to} \mathbf{F}^{\mathrm{Big}}(m) \otimes \mathbf{F}^{\mathrm{Big}}(n) \to F(m) \otimes F(n) \hookrightarrow \mathbf{H}^*((\mathbf{R}P^{\infty})^{m+n})$$

is simply the map of R-modules determined by the element  $t_1t_2...t_{n+m} \in H^{n+m}(\mathbf{R}P^{\infty})^{m+n}$ ). Since  $H^*((\mathbf{R}P^{\infty})^{m+n})$  satisfies the Adem relations, we have  $\phi(z) = 0$ , a contradiction. This completes the proof of Theorem 2.

It follows that the tensor product of Definition 1 determines a functor  $\otimes : \mathcal{U}^{\mathrm{Big}} \times \mathcal{U}^{\mathrm{Big}} \to \mathcal{U}^{\mathrm{Big}}$ . It is easy to see that this operation is commutative and associative, up to coherent isomorphism. In other words, it endows  $\mathcal{U}^{\mathrm{Big}}$  with the structure of a symmetric monoidal category.

**Corollary 3.** Let M and N be unstable modules over the Steenrod algebra A. Then the tensor product  $M \otimes N$  inherits the structure of an unstable module over the Steenrod algebra.

*Proof.* We have seen that  $M \otimes N$  has the structure of an unstable module over  $\mathcal{A}^{\text{Big}}$ . To complete the proof, it will suffice to show that  $\operatorname{Sq}^0$  acts by the identity on  $M \otimes N$ . Unwinding the definition, we have

$$\operatorname{Sq}^{0}(x \otimes y) = \sum_{k} \operatorname{Sq}^{k}(x) \otimes \operatorname{Sq}^{-k}(y).$$

The right hand side vanishes if  $k \neq 0$ , and coincides with  $x \otimes y$  when k = 0.

The tensor product operation on the category of unstable Steenrod modules results from a comultiplicative structure which exists on the Steenrod algebra  $\mathcal{A}$  itself:

**Proposition 4.** There exists a ring homomorphism

$$\mathcal{A} \to \mathcal{A} \otimes \mathcal{A}$$

given by

$$\operatorname{Sq}^k \mapsto \sum_{k=k'+k''} \operatorname{Sq}^{k'} \otimes \operatorname{Sq}^{k''}.$$

*Proof.* The formula above evidently defines a ring homomorphism  $\Delta: R \to \mathcal{A} \otimes \mathcal{A}$ . Let K denote the kernel of the projection map  $R \to \mathcal{A}$ . It will suffice to show that  $\Delta(K) = 0$ . Suppose otherwise. Then there exists a nonzero element

$$T = \sum_{\alpha} \operatorname{Sq}^{I_{\alpha}} \otimes \operatorname{Sq}^{J_{\alpha}}$$

belonging to the image  $\Delta(K)$ , where  $(I_{\alpha}, J_{\alpha})$  ranges over some finite set of admissible positive sequences. Choose a pair of positive integers (m, n) such that for some index  $\alpha$ , m is at least as large as the excess of  $I_{\alpha}$  and n is at least as large as the excess of  $J_{\alpha}$ . Then we have  $T(\nu_m \otimes \nu_n) \neq 0 \in F(m) \otimes F(n)$ , which contradicts Corollary 3.

The comultiplication  $\mathcal{A} \to \mathcal{A} \otimes \mathcal{A}$  of Proposition 4 is in some respects simpler than the multiplication on  $\mathcal{A}$ : for example, it is commutative while the multiplication on  $\mathcal{A}$  is not. We will return to this point in a future lecture.

We now introduce some terminology which we will need later.

**Definition 5.** An unstable  $A^{Big}$ -algebra is an unstable  $A^{Big}$ -module M equipped with a commutative and associative multiplication  $m: M \otimes M \to M$  satisfying the following conditions:

(1) The Cartan formula is satisfied:

$$\operatorname{Sq}^{k}(xy) = \sum_{k=k'+k''} \operatorname{Sq}^{k'}(x) \operatorname{Sq}^{k''}(y).$$

In other words, m is a map of  $\mathcal{A}^{\text{Big}}$ -modules.

- (2) For every homogeneous element  $x \in M$ ,  $\operatorname{Sq}^{\operatorname{deg}(x)}(x) = x^2$ .
- (3) M contains a unit element 1 satisfying

$$\operatorname{Sq}^{i}(1) = \begin{cases} 1 & \text{if } i = 0\\ 0 & \text{otherwise.} \end{cases}$$

An unstable  $\mathcal{A}$ -algebra is an unstable  $\mathcal{A}^{\text{Big}}$ -algebra which is an  $\mathcal{A}$ -module: that is, an unstable  $\mathcal{A}^{\text{Big}}$ -algebra M which satisfies  $\operatorname{Sq}^0(x) = x$  for all  $x \in M$ .

**Example 6.** The cohomology  $H^*(X)$  of any space X has the structure of an unstable  $\mathcal{A}$ -algebra. The cohomology  $H^*(A)$  of any  $E_{\infty}$ -algebra over  $\mathbf{F}_2$  has the structure of an unstable  $\mathcal{A}^{\text{Big}}$ -algebra.

Our next goal is to understand the structure of free unstable algebras. For every integer n, we let  $F_{Alg}(n)$  denote the free unstable  $\mathcal{A}$ -algebra generated by a single element  $\mu_n$  of degree n, and  $F_{Alg}^{Big}(n)$  the free unstable  $\mathcal{A}^{Big}$ -algebra generated by a single element  $\overline{\mu}_n$  of degree n. We have an evident quotient map  $\pi: F_{Alg}^{Big}(n) \to F_{Alg}(n)$ , uniquely determined by the requirement that  $\pi(\overline{\mu}_n) = \mu_n$ .

Let X denote the subspace of  $F_{Alg}^{Big}(n)$  spanned by the products

$$\{\operatorname{Sq}^{I_1}(\overline{\mu_n})\operatorname{Sq}^{I_2}(\overline{\mu_n})\ldots\operatorname{Sq}^{I_k}(\overline{\mu_n})\}.$$

Using relations (1) and (3), we deduce that X is a subalgebra of  $\mathcal{F}^{\mathrm{Big}}_{\mathrm{Alg}}(n)$ , so that  $X = \mathcal{F}^{\mathrm{Big}}_{\mathrm{Alg}}(n)$ . Moreover, relation (2) allows us to reduce any such monomial to a form where the sequences  $I_1, \ldots, I_k$  are all distinct. Using the Adem relations and the instability condition, we can further reduce to considering such monomials where each sequence  $I_j$  is admissible and has excess  $\leq n$ . We have therefore proven half of the following result:

**Theorem 7.** (1) The free unstable  $A^{Big}$ -algebra  $F_{Alg}^{Big}(n)$  has a basis of monomials

$$\{\operatorname{Sq}^{I_1}(\overline{\mu_n})\operatorname{Sq}^{I_2}(\overline{\mu_n})\ldots\operatorname{Sq}^{I_k}(\overline{\mu_n})\}$$

where  $I_1 < \ldots < I_k$  (with respect to the lexicographical ordering, say) are admissible sequences of excess < n.

(2) The free unstable A-algebra  $F_{Alg}(n)$  has a basis of monomials

$$\{\operatorname{Sq}^{I_1}(\mu_n)\operatorname{Sq}^{I_2}(\mu_n)\ldots\operatorname{Sq}^{I_k}(\mu_n)\}$$

where  $I_1 < \ldots < I_k$  are admissible positive sequences of excess  $\leq n$ .

The proof follows the same lines as our proof of the analogous fact for modules, and our construction of tensor products earlier in this lecture: we will reduce assertion (1) to assertion (2), using a shifting argument. Namely, there exists an isomorphism of algebras  $F_{Alg}^{Big}(n) \to F_{Alg}^{Big}(n+1)$  given by the formula

$$(\operatorname{Sq}^{i_{j_{1}}^{1}} \dots \operatorname{Sq}^{i_{0}^{1}} \overline{\mu}_{n}) \dots (\operatorname{Sq}^{i_{j_{k}}^{k}} \dots \operatorname{Sq}^{i_{0}^{k}} \overline{\mu}_{n}) \mapsto (\operatorname{Sq}^{i_{j_{1}}^{1}+2^{j_{1}}} \dots \operatorname{Sq}^{i_{0}^{1}+1} \overline{\mu}_{n+1}) \dots (\operatorname{Sq}^{i_{j_{k}}^{k}+2^{j_{k}}} \dots \operatorname{Sq}^{i_{0}^{k}+1} \overline{\mu}_{n+1})$$

Consequently, any linear dependence among the expressions

$$M(I_1, \dots, I_k) = \operatorname{Sq}^{I_1}(\overline{\mu_n}) \operatorname{Sq}^{I_2}(\overline{\mu_n}) \dots \operatorname{Sq}^{I_k}(\overline{\mu_n}) \in \operatorname{F}^{\operatorname{Big}}_{\operatorname{Alg}}(n)$$

results in a linear dependence among analogous expressions  $M(I'_1, \ldots, I'_k) \in \mathcal{F}^{\mathrm{Big}}_{\mathrm{Alg}}(n+p)$ , for each  $p \geq 0$ . Choosing  $p \gg 0$ , we get a linear dependence involving monomials in which all of the sequences  $(I'_1, \ldots, I'_k)$  are positive, which contradicts (2).

To prove (2), we need to produce some examples of unstable A-algebras. We will return to this point in the next lecture.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Free Unstable Algebras (Lecture 12)

In the last lecture, we introduced the free unstable A-module  $F_{Alg}(n)$  on a generator  $\mu_n$  having degree n. Moreover, we asserted the following:

**Proposition 1.** For  $n \geq 0$ , the vector space  $F_{Alg}(n)$  has a basis consisting of

$$\{\operatorname{Sq}^{I_1}(\mu_n)\ldots\operatorname{Sq}^{I_k}(\mu_n)\},\$$

where  $I_1 < ... < I_k$  are admissible positive sequences of excess  $\leq n$ . Here we adopt the convention that the excess of the empty sequence is  $-\infty$ .

Moreover, we have already proven half of this result: namely, that the products  $\operatorname{Sq}^{I_1}(\mu_n) \dots \operatorname{Sq}^{I_k}(\mu_n)$  generate  $\operatorname{F}_{\operatorname{Alg}}(n)$ . To complete the proof, we must show that these elements are linearly independent. For this, it will suffice to construct a map  $\phi : \operatorname{F}_{\operatorname{Alg}}(n) \to M$ , where M is an unstable  $\mathcal{A}$ -algebra, such that the images  $\phi(\operatorname{Sq}^{I_1}(\mu_n) \dots \operatorname{Sq}^{I_k}(\mu_n))$  are linearly independent in M. Since  $\operatorname{F}_{\operatorname{Alg}}(n)$  is freely generated by  $\mu_n$ , the map  $\phi$  is determined by a single element  $x = \phi(\mu_n) \in M^n$ .

We have seen that for every topological space X, the cohomology ring  $\mathrm{H}^*(X)$  is an unstable  $\mathcal{A}$ -algebra. It is therefore natural to try to prove Proposition 1 by producing a space X and a cohomology class  $x \in \mathrm{H}^n(X)$  such that the elements  $\{\mathrm{Sq}^{I_1}(x)\ldots\mathrm{Sq}^{I_k}(x)\}$  are linearly independent in  $\mathrm{H}^*(X)$ . To guarantee this, we want to choose X such that the cohomology class is as nontrivial as possible. There is a natural candidate for X: namely, the Eilenberg-MacLane space  $K(\mathbf{F}_2,n)$ . This Eilenberg-MacLane space represents the cohomology functor  $X \mapsto \mathrm{H}^n(X)$  in the following sense: there is a canonical element  $\chi \in \mathrm{H}^n(K(\mathbf{F}_2,n))$ , and for every nice topological space, the pullback of  $\chi$  induces a bijection

$$[X, K(\mathbf{F}_2, n)] \simeq \operatorname{H}^n(X).$$

Here  $[X, K(\mathbf{F}_2, n)]$  denotes the set of homotopy classes of maps from X to  $K(\mathbf{F}_2, n)$ . Consequently, if we hope to prove Proposition 1 using the unstable  $\mathcal{A}$ -algebras provided by the cohomology of any space X, then we might as well replace X by  $K(\mathbf{F}_2, n)$ . Fortunately, this turns out to work. More precisely, Proposition ?? is a consequence of the following result:

**Theorem 2** (Cartan, Serre). For each  $n \geq 0$ , the cohomology ring  $H^*(K(\mathbf{F}_2, n))$  has a basis  $\{\operatorname{Sq}^{I_1}(\chi) \dots \operatorname{Sq}^{I_k}(\chi)\}$ , where  $I_1 < \dots < I_k$  are admissible positive sequences of excess  $\leq n$ .

**Corollary 3.** The canonical map  $\phi : F_{Alg}(n) \to H^*(K(\mathbf{F}_2, n))$  is an isomorphism.

To put Corollary 3 in perspective, let us recall a definition. A cohomology operation is a collection of maps

$$H^n(X) \to H^m(X)$$
,

defined for all topological spaces X and functorial in X. For example, every Steenrod operation  $\operatorname{Sq}^i$  determines a cohomology operation

$$\operatorname{Sq}^{i}: \operatorname{H}^{n}(X) \to \operatorname{H}^{n+i}(X).$$

Using Yoneda's lemma, we see that the set of cohomology operations from  $H^n$  to  $H^m$  can be identified with

$$[K(\mathbf{F}_2, n), K(\mathbf{F}_2, m)] \simeq \mathrm{H}^m(K(\mathbf{F}_2(n))) \simeq \mathrm{F}_{\mathrm{Alg}}(n)^m.$$

In other words, we can build *every* cohomology operation out of Steenrod squares, sums, and products. Moreover, the only relations among these operations are the ones we have built into the definition of an unstable A-algebra:

(i) The Adem relations

$$\operatorname{Sq}^{a} \operatorname{Sq}^{b}(x) = \sum_{k} (2k - a, b - k - 1) \operatorname{Sq}^{b+k} \operatorname{Sq}^{a-k}(x)$$

for a < 2b.

- (ii) The Cartan formula  $\operatorname{Sq}^{n}(xy) = \sum_{n=n'+n''} \operatorname{Sq}^{n'}(x) \operatorname{Sq}^{n''}(y)$
- (iii) The boundary conditions

$$\operatorname{Sq}^{n}(x) = \begin{cases} 0 & \text{if } n < 0 \\ x & \text{if } n = 0 \\ ? & \text{if } 0 < n < \operatorname{deg}(x) \\ x^{2} & \text{if } n = \operatorname{deg}(x) \\ 0 & \text{if } n > \operatorname{deg}(x). \end{cases}$$

We will later show that there is an analogous relationship between unstable  $\mathcal{A}^{\text{Big}}$ -modules and the cohomology of  $E_{\infty}$ -algebras over  $\mathbf{F}_2$ .

We now turn to the proof of Theorem 2. We begin by modifying the formulation a bit. Recall that the excess of a sequence of integers  $I = (i_m, \dots, i_0)$  is the difference

$$i_m - i_{m-1} - \ldots - i_0 = (i_m - 2i_{m-1}) + \ldots + (i_1 - 2i_0) + i_0.$$

This definition is rigged so that if I has excess  $> \deg(x)$ , then  $\operatorname{Sq}^{I}(x) = \operatorname{Sq}^{i_{m}}(\operatorname{Sq}^{I'}x) = 0$ , where  $I' = (i_{m-1}, \ldots, i_{0})$ , since

$$i_m > i_{m-1} + \ldots + i_0 + \deg(x) = \deg(\operatorname{Sq}^{I'} x).$$

If the excess of I is  $exactly \deg(x)$ , then we instead have the equality  $\operatorname{Sq}^I(x) = \operatorname{Sq}^{i_m} \operatorname{Sq}^{I'}(x) = (\operatorname{Sq}^{I'} x)^2$ . Applying this argument repeatedly, we see that every expression  $\operatorname{Sq}^{I_1}(\chi) \dots \operatorname{Sq}^{I_k}(\chi)$  appearing in Theorem

Applying this argument repeatedly, we see that every expression  $\operatorname{Sq}^{I_1}(\chi) \dots \operatorname{Sq}^{I_k}(\chi)$  appearing in Theorem 2 can be rewritten uniquely as a product  $(\operatorname{Sq}^{I'_1}(\chi))^{2^{a_1}} \dots (\operatorname{Sq}^{I'_k}(\chi))^{2^{a_k}}$ , where each  $I'_j$  is an admissible positive sequence of excess < n, and the  $a_j$  are nonnegative integers, and the pairs  $(a_j, I'_j)$  are disjoint. Since every nonnegative integer b has a unique expansion as a sum of distinct powers of 2, we obtain the following reformulation of the Cartan-Serre theorem:

**Theorem 4.** For  $n \ge 0$ . The cohomology ring  $H^*(K(\mathbf{F}_2,n))$  has a basis consisting of products  $\{\operatorname{Sq}^{J_1}(\chi)^{b_1} \ldots \operatorname{Sq}^{J_k}(\chi)^{b_k}\}$ , where  $J_1 < \ldots < J_k$  are admissible positive sequences of excess < n, and the  $b_j$  are nonnegative integers. In other words,  $H^*(K(\mathbf{F}_2,n))$  is a polynomial ring on generators  $\{\operatorname{Sq}^J(\chi)\}$ , where J ranges over admissible positive sequences of excess < n.

We now turn to the proof of this theorem. The case n=0 is trivial. To handle the case n=1, we observe that every nonempty positive admissible sequence  $(i_n,\ldots,i_0)$  has positive excess. Thus, there is only one sequence with excess < 1: the empty sequence J (which, by convention, has excess  $-\infty$ ). We have  $\operatorname{Sq}^J(\chi) = \chi$ , and Theorem 4 reduces to the following assertion: the cohomology ring  $\operatorname{H}^*(K(\mathbf{F}_2,1))$  is a polynomial ring on its canonical element  $\chi \in \operatorname{H}^1(K(\mathbf{F}_2,1))$ . But  $K(\mathbf{F}_2,1)$  is simply the classifying space  $B\Sigma_2 \simeq \mathbf{R}P^\infty$ , whose cohomology ring is indeed isomorphic to a polynomial ring  $\mathbf{F}_2[t]$  on a single generator.

To treat the general case, we will use induction on n and the Serre spectral sequence. We begin by reviewing the Serre spectral sequence in general.

Fact 5 (Serre). Suppose given a homotopy fiber sequence of topological spaces

$$F \to E \to B$$
.

Then there exists a (first quadrant) spectral sequence

$$\{E_r^{p,q}, d_r\}_{r>2}$$

with  $E_2^{p,q} \simeq H^p(B; H^q(F; \mathbf{F}_2))$  which converges to the cohomology  $H^{p+q}(E; \mathbf{F}_2)$ . Moreover:

- (1)  $\{E_r^{p,q}, d_r\}_{r>2}$  is a spectral sequence of algebras.
- (2) If the base B is simply connected and the cohomology groups  $H^q(F; \mathbf{F}_2)$  are finite dimensional, then obtain a canonical isomorphism  $E_2^{p,q} \simeq H^p(B) \otimes H^q(F)$ .

Since the Serre spectral sequence  $\{E_r^{p,q},d_r\}_{r\geq 2}$  is a first quadrant spectral sequence, we see that for each  $r\geq 2$ , the groups  $E_r^{0,q}$  can be identified with subgroups of  $E_2^{0,q}$  (namely, the subgroups consisting of elements killed by the differentials  $d_2,\ldots,d_{r-1}$ ), and the groups  $E_r^{p,0}$  can be identified with quotients of  $E_r^{p,0}$  (the quotient by the images of the differentials  $d_2,\ldots,d_{r-1}$ ).

We will be interested in studying the Serre spectral sequence in the case where the total space E of the fibration is contractible. In this case, we deduce that  $E^{p,q}_{\infty} \simeq 0$  unless p=q=0. In particular, for each  $m \geq 2$  the "final differential"  $d_m: E^{0,m-1}_m \to E^{m,0}_m$  must be an isomorphism. The composition

$$\tau: {\rm H}^m(B) \simeq E_2^{m,0} \to E_m^{m,0} \overset{d_m^{-1}}{\to} E_m^{0,m-1} \subseteq E_2^{0,m-1} \simeq {\rm H}^{m-1}(F)$$

is called the transgression map. Elements of  $H^{m-1}(F)$  which lie in the image of  $\tau$  are called transgressive.

There is a canonical example of a spectral sequence with a transfersive element x of degree m-1, which we will denote by  $\{E(m)_r^{p,q}, d_r\}_{r\geq 2}$ . Namely, we take

$$E(m)_r^{p,q} = \begin{cases} \mathbf{F}_2[y] \oplus \mathbf{F}_2[y]x & \text{if } r \leq m \\ \mathbf{F}_2 & \text{if } r > m \end{cases}$$

where x has degree (0, m-1) and y has degree (m, 0). The differentials  $d_r$  vanish unless r = m, and  $d_r$  is given by the formula

$$d_m(z) = \begin{cases} 0 & \text{if } z = y^a \\ y^{a+1} & \text{if } z = y^a x. \end{cases}$$

In this spectral sequence, the transgression map carries y to x, and vanishes in other degrees. Moreover, given any spectral sequence of algebras  $\{E_r^{p,q},d_r\}_{r\geq 2}$  with a transgressive element  $\chi'=\tau(\chi)\in E_2^{0,m-1}$ , there is a unique map of spectral sequences  $\{E(m)_r^{p,q}\}\to \{E_r^{p,q}\}$ , which is given by the formula  $y^a\mapsto \chi^a$ ,  $y^ax\mapsto \chi^a\chi'$ .

Let us now return to our discussion of the Serre spectral sequence of Fact 5, where we can describe the transgression map in topological terms. If we assume that the total space E of the fibration is contractible, then we can identify the fiber F with the based loop space  $\Omega B$ . We then have a canonical map  $\Sigma \Omega B \to B$ , which induces a pullback map on reduced cohomology

$$\tau: \widetilde{\operatorname{H}}^*(B) \to \widetilde{\operatorname{H}}^*(\Sigma \Omega B) \simeq \widetilde{\operatorname{H}}^{*-1}(\Omega B) = \widetilde{\operatorname{H}}^{*-1}(F).$$

From this description of the transgression map (and the stability of the Steenrod operations), we see that  $\tau$  commutes with the action of the Steenrod operations.

We now specialize to the case of interest: let the base B be the Eilenberg-MacLane space  $K(\mathbf{F}_2, n)$ , where  $n \geq 2$ . We will take the map  $E \to B$  to be the usual path fibration, so that E is contractible and the fiber F is isomorphic to  $\Omega K(\mathbf{F}_2, n) \simeq K(\mathbf{F}_2, n-1)$ . Let  $\chi \in H^n(K(\mathbf{F}_2, n))$  be the canonical generator, and

let  $\chi' = \tau(\chi) \in \mathrm{H}^{n-1}(K(\mathbf{F}_2, n-1))$ . For every positive admissible sequence I of excess < n, the element  $\mathrm{Sq}^I \chi' \in \mathrm{H}^*(K(\mathbf{F}_2, n-1))$  is the image of  $\mathrm{Sq}^I \chi$  under the transgression map. It follows from the above that we get a map of spectral sequences

$$\psi_I: \{E(n + \deg(I))_r^{p,q}\}_{r \ge 2} \to \{E_r^{p,q}\}_{r \ge 2},$$

given by  $y \mapsto \chi$ ,  $x \mapsto \chi'$ .

Let  $\{\tilde{E}_r^{p,q}\}_{r\geq 2}$  denote the tensor product of the spectral sequences  $\{E(n+\deg(I))_r^{p,q}\}$ , taken over all positive admissible sequences I of excess < n. Since the Serre spectral sequence  $\{E_r^{p,q}\}_{r\geq 2}$  is a spectral sequence of commutative algebras, we can multiply the maps  $\psi_I$  to obtain a single map

$$\psi: \{\widetilde{E}_r^{p,q}\}_{r\geq 2} \to \{E_r^{p,q}\}_{r\geq 2}.$$

We now make the following observations:

(a) The map  $\psi$  induces an isomorphism of columns

$$\widetilde{E}_{2}^{0,*} \to E_{2}^{0,*} \simeq \mathrm{H}^{*}(K(\mathbf{F}_{2}, n-1)).$$

This is simply a reformulation of Theorem 2 for the Eilenberg-MacLane space  $K(\mathbf{F}_2, n-1)$ , which follows from our inductive hypothesis.

- (b) The spectral sequence  $\{\widetilde{E}_r^{p,q}\}_{r\geq 2}$  is a spectral sequence of modules over the ring  $R=\widetilde{E}_2^{*,0}$ , which is a polynomial ring on a set of generators y(I), where I ranges over admissible positive sequences of excess  $\leq n$ .
- (c) The spectral sequence  $\{E_r^{p,q}\}_{r\geq 2}$  is a spectral sequence of modules over the ring  $\mathrm{H}^*(B)\simeq E_2^{*,0}$ . Moreover, the map  $\psi$  induces a ring homomorphism  $R\to\mathrm{H}^*(B)$  which carries y(I) to  $\mathrm{Sq}^I$   $\chi$ .
- (d) For each  $q \geq 0$ ,  $\widetilde{E}_2^{*,q}$  is freely generated by  $\widetilde{E}_2^{0,q}$  as an R-module. Similarly,  $E_2^{*,q}$  is freely generated by the same vector space  $E_2^{0,q} \simeq \widetilde{E}_2^{0,q}$  as an  $H^*(B)$ -module.
- (e) The map  $\psi$  induces an isomorphism  $\widetilde{E}_{\infty}^{p,q} \to E_{\infty}^{p,q}$ , since both sides vanish unless p=q=0.

To prove Theorem 4, we must show that the map  $R \to H^*(B)$  is an isomorphism of rings. In fact, we will prove the stronger assertion that  $\psi$  is an isomorphism of spectral sequences. It will suffice to show that  $\psi$  induces an isomorphism  $\widetilde{E}_2^{p,q} \to E_2^{p,q}$  for  $p,q \geq 0$ . The proof is by induction on p. If p = 0, the desired result follows from (a).

Suppose p>0. In view of (d), it will suffice to show that  $\psi$  induces an isomorphism  $\widetilde{E}_2^{p,0}\to E_2^{p,0}$ . For  $q\leq p-1$ , let D(q) denote the quotient of  $E_{q+1}^{p-q-1,q}$  by the images of the maps  $\{d_r\}_{r\geq q+1}$ , and let  $\widetilde{D}(q)$  be defined likewise. Since  $E_\infty^{p,0}\simeq 0$ , we conclude that  $E_2^{p,0}$  admits a finite filtration whose successive quotients are the vector spaces  $\{D(q)\}_{0\leq q\leq p-1}$ . Similarly,  $\widetilde{E}_2^{p,0}$  admits a filtration with successive quotients  $\{\widetilde{D}(q)\}_{0\leq q\leq p-1}$ . Using the inductive hypothesis, we see that  $\psi$  induces an isomorphism  $\widetilde{D}(q)\to D(q)$ . It follows that  $\psi$  also induces an isomorphism  $\widetilde{E}_2^{p,0}\to E_2^{p,0}$  as desired.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Dual Steenrod Algebra (Lecture 13)

We have seen that the Steenrod algebra **A** admits a comultiplication map  $\mathcal{A} \otimes \mathcal{A} \to \mathcal{A}$ , described by the formula

$$\operatorname{Sq}^n \mapsto \sum_{n=n'+n''} \operatorname{Sq}^{n'} \otimes \operatorname{Sq}^{n''}.$$

This comultiplication map is obviously symmetric, and therefore endows the graded dual  $\mathcal{A}^{\vee} = \bigoplus_{n} (\mathcal{A}^{n})^{\vee}$  with the structure of a *commutative* ring. Our goal in this lecture is to understand the structure of  $\mathcal{A}^{\vee}$ .

For the remainder of this lecture, we will work in the category of (affine) schemes over the field  $\mathbf{F}_2$ . (In other words, we work in the opposite to the category of commutative  $\mathbf{F}_2$ -algebras.)

The noncommutative multiplication on  $\mathcal{A}$  induces a *comultiplication* map  $\mathcal{A}^{\vee} \to \mathcal{A}^{\vee} \otimes \mathcal{A}^{\vee}$ , which in turn determines a map of  $\mathbf{F}_2$ -schemes

$$\operatorname{Spec} A^{\vee} \times \operatorname{Spec} A^{\vee} \to \operatorname{Spec} A^{\vee}$$
.

This map exhibits Spec  $\mathcal{A}^{\vee}$  as a *group scheme* over the field  $\mathbf{F}_2$ . Let us henceforth denote this group scheme by G.

For every topological space X, the Steenrod algebra acts on the cohomology ring  $H^*(X)$  via a map  $A \otimes H^*(X) \to H^*(X)$ . If the cohomology ring  $H^*(X)$  is finite dimensional, then we can transpose this action to obtain a map

$$\mathrm{H}^*(X) \to \mathrm{H}^*(X) \otimes \mathcal{A}^{\vee}$$
.

Rephrasing this in the language of algebraic geometry, we get a map

$$G \times \operatorname{Spec} H^*(X) \to \operatorname{Spec} H^*(X)$$
.

This map endows the scheme Spec  $H^*(X)$  with an action of the group scheme G.

If  $H^*(X)$  is not finite-dimensional, then we need to be a bit more careful. Suppose instead that  $H^*(X)$  is finite dimensional in each degree. For each  $n \geq 0$ , the direct sum  $R_n = \bigoplus_{0 \leq k \leq n} H^k(X)$  can be viewed as a quotient of the cohomology ring  $H^*(X)$ , and inherits the structure of an unstable  $\mathcal{A}$ -algebra. Using the above argument, we obtain an action

$$G \times \operatorname{Spec} R_n \to \operatorname{Spec} R_n$$
.

Moreover, if n = 1, then this action is trivial.

Let us now specialize to the case where X is the space  $\mathbb{R}P^{\infty}$ . In this case, the cohomology ring  $H^*(X)$  is isomorphic to  $\mathbb{F}_2[t]$ . We therefore have isomorphisms  $R_n \simeq \mathbb{F}_2[t]/(t^{n+1})$  for  $n \geq 0$ . For each  $n \geq 0$ , there exists a group scheme parametrizing automorphisms of Spec  $R_n$  which induce the identity on Spec  $R_1$ . We will denote this group scheme by  $H_n$ . By definition,  $H_n$  has the following universal property:

$$\operatorname{Hom}(\operatorname{Spec} B, H_n) \simeq \operatorname{Hom}^0(\operatorname{Spec} B \times \operatorname{Spec} R_n, \operatorname{Spec} R_n) \simeq \operatorname{Hom}^0(\mathbf{F}_2[t]/(t^{n+1}, B[t]/(t^{n+1})) \simeq t + t^2 B/(t^{n+1}B),$$

(here the superscripts indicate the requirement that the morphism reduce to the identity on  $R_1$ ) so  $H_n$  is just isomorphic to an (n-1)-dimensional affine space  $\mathbf{A}^n$ . Let  $H_{\infty}$  denote the inverse limit of the tower

$$\dots \to H_2 \to H_1 \to H_0$$

so that  $H_{\infty}$  is the infinite dimensional affine space which is the automorphism group of the formal scheme Spf  $\mathbf{F}_2[[t]]$ . More concretely, we are just saying that every automorphism of the power series ring B[[t]] which reduces to the identity modulo  $t^2$  is given by a transformation

$$t \mapsto t + b_1 t^2 + b_2 t^3 + \dots$$

so we get an identification  $H_{\infty} \simeq \operatorname{Spec} \mathbf{F}_2[b_1, b_2, \ldots]$ 

The above analysis gives us a map of group schemes  $\phi: G \to H_{\infty}$ . Our first result is:

**Proposition 1.** The map  $\phi: G \to H_{\infty}$  is a monomorphism.

To prove this, let  $G_0 \subseteq G$  be the kernel of the homomorphism  $\phi$ . Then  $G_0$  acts trivially on the formal spectrum Spf  $H^*(\mathbf{R}P^{\infty})$ . It follows that the diagonal action of  $G_0$  on

$$\operatorname{Spf} H^*(\mathbf{R}P^{\infty}) \times \ldots \times \operatorname{Spf} H^*(\mathbf{R}P^{\infty}) \simeq \operatorname{Spf} H^*((\mathbf{R}P^{\infty})^k)$$

is trivial for all k.

We observe that  $G_0 = \operatorname{Spec} C$ , where C is some Hopf algebra quotient of the dual Steenrod algebra  $\mathcal{A}^{\vee}$ . It is not difficult to see that C inherits a grading from  $\mathcal{A}^{\vee}$ , so that the graded dual  $C^{\vee}$  can be identified with a subalgebra of the Steenrod algebra  $\mathcal{A}$ . The above analysis shows that  $C^{\vee}$  acts trivially on the cohomology  $\operatorname{H}^*((\mathbf{R}P^{\infty})^k)$  for all  $k \geq 0$ . We claim that  $C^{\vee} \simeq \mathbf{F}_2$ . If not, then we can find some nonconstant element of  $C^{\vee}$  of the form  $\sum_{\alpha} \operatorname{Sq}^{I_{\alpha}}$ , where  $I_{\alpha}$  ranges over some collection of admissible positive sequences. Choosing k larger than the excess of each  $I_{\alpha}$ , we see that  $C^{\vee}$  acts nontrivially on  $t_1 \dots t_k \in \operatorname{H}^k((\mathbf{R}P^{\infty})^k)$ , a contradiction. Thus  $C^{\vee} \simeq \mathbf{F}_2$ , so  $G_0 \simeq \operatorname{Spec} \mathbf{F}_2$  and the map  $\phi$  is a monomorphism as desired.

We now wish to describe the image of the map  $\phi$ . For this, we observe that the formal affine line  $\hat{\mathbf{A}}^1 \simeq \operatorname{Spf} \mathbf{F}_2[[t]]$  is isomorphic to the *formal additive group* over the field  $\mathbf{F}_2$ . In other words, we have an addition map

$$\hat{\mathbf{A}}^1 \times \hat{\mathbf{A}}^1 \to \hat{\mathbf{A}}^1$$
,

which is described in coordinates by the map of power series rings

$$\mathbf{F}_{2}[[t]] \to \mathbf{F}_{2}[[t_{1}, t_{2}]]$$

$$t->t_1+t_2.$$

In fact, this map comes from topology. The group  $\Sigma_2$  is abelian, so the multiplication map

$$\Sigma_2 \times \Sigma_2 \to \Sigma_2$$

is a group homomorphism. It follows that we obtain a map of classifying spaces

$$B\Sigma_2 \times B\Sigma_2 \simeq B(\Sigma_2 \times \Sigma_2) \to B\Sigma_2.$$

The induced map on cohomology

$$H^*(\mathbf{R}P^{\infty}) \to H^*(\mathbf{R}P^{\infty} \times \mathbf{R}P^{\infty})$$

is also described by the formula

$$t \mapsto t_1 + t_2$$
.

It follows that the action of the Steenrod algebra  $\mathcal{A}$  is compatible with the comultiplication on  $H^*(\mathbf{R}P^{\infty})$ . In other words, the action of the group scheme  $G = \operatorname{Spec} \mathcal{A}^{\vee}$  on the formal affine line  $\hat{\mathbf{A}}^1$  preserves the group structure on  $\hat{\mathbf{A}}^1$ .

Let  $\operatorname{End}(\mathbf{A}^1)$  denote the subgroup scheme of  $H_{\infty}$  which preserves the group structure on  $\mathbf{A}^1$ . We note that a B-valued point of  $H_{\infty}$  is an automorphism of B[[t]] of the form

$$t \mapsto t + b_1 t^2 + b_2 t^3 + \dots$$

This B-valued point belong to End( $\mathbf{A}^1$ ) if and only if the power series  $f(t) = t + b_1 t^2 + b_2 t^3 + \dots$  is additive. in the sense that  $f(t_1 + t_2) = f(t_1) + f(t_2) \in B[[t_1, t_2]]$ . Since we are working in characteristic 2, additivity is equivalent to the requirement that the terms  $b_{i-1}t^i$  vanish unless i is a power of 2. In other words, we can identify  $\operatorname{End}(\mathbf{A}^1)$  with the infinite dimensional affine space parametrizing power series of the form

$$t + b_1 t^2 + b_3 t^4 + b_7 t^8 + \dots$$

**Theorem 2.** The map  $\phi$  induces an isomorphism  $G \to \text{End}(\mathbf{A}^1)$ .

In other words, we claim that the corresponding map of commutative rings

$$\psi: \mathbf{F}_2[b_1, b_3, b_7, \ldots] \to \mathcal{A}^{\vee}$$

is an isomorphism. Proposition 1 implies that  $\psi$  is surjective. Moreover,  $\psi$  is a map of graded rings, where each  $b_i$  is regarded as having degree i. It will therefore suffice to show that the algebras  $\mathbf{F}_2[b_1, b_3, b_7, \ldots]$  and  $\mathcal{A}^{\vee}$  have the same dimensions in each degree.

Fix an integer  $n \geq 0$ . The *n*th graded piece of  $\mathbf{F}_2[b_1, b_3, b_7, \ldots]$  is spanned by monomials

$$b_1^{\epsilon_1}b_3^{\epsilon_2}b_7^{\epsilon_3}\ldots,$$

which are indexed by sequences of nonnegative integers  $(\epsilon_1, \epsilon_2, ...)$  satisfying  $\sum_k (2^k - 1)\epsilon_k = n$ . We have also seen that the Steenrod algebra  $\mathcal{A}$  has a basis consisting of expressions  $\operatorname{Sq}^I = \operatorname{Sq}^{i_1} \operatorname{Sq}^{i_2} ... \operatorname{Sq}^{i_m}$ , where the quantities

$$\delta_k = \begin{cases} i_k - 2i_{k+1} & \text{if } k < m \\ i_m & \text{if } k = m \\ 0 & \text{if } k > m \end{cases}$$

are required to be nonnegative. Moreover, we have

$$i_k = \delta_k + 2\delta_{k+1} + 4\delta_{k+2} + \dots$$

so that the total degree of  $Sq^I$  is

$$\sum_{k>0} i_k = \sum_{k>0, m>0} \delta_{k+m} 2^m = \sum_{k'>0} \delta_{k'} (2^{k'} - 1).$$

We therefore obtain a bijection from a basis of  $\mathbf{F}_2[b_1, b_3, \ldots]^n$  to a basis of  $\mathcal{A}^n$ , given by the correspondence

$$(\epsilon_1, \epsilon_2, \ldots) \leftrightarrow (\delta_1, \delta_2, \delta_3, \ldots).$$

Remark 3. In fact, more is true: the bijection described above is actually upper-triangular with respect to duality between  $\mathcal{A}$  and  $\mathbf{F}_2[b_1, b_3, \ldots]$  determined by the ring homomorphism  $\psi$ . This is implicit in our proof that the admissible monomials are linearly independent in A.

Corollary 4. The dual Steenrod algebra  $A^{\vee}$  is isomorphic to a polynomial ring  $\mathbf{F}_2[b_1, b_3, b_7, \ldots]$ .

We can describe the comultiplication on  $\mathcal{A}^{\vee}$  (and therefore the multiplication on  $\mathcal{A}$ ) very concretely in terms of the isomorphism of Corollary 4. This comultiplication correpsonds to the group structure on  $\operatorname{End}(\mathbf{A}^1)$ : in other words, it corresponds to composition of transformations having the form  $t \mapsto t + b_1 t^2 + b_2 t^2 + b_3 t^2 + b_4 t^2 + b_4 t^2 + b_4 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2 + b_5 t^2$  $b_3t^4 + \dots$  Let  $f(t) = \sum_{i \ge 0} b_{2^i - 1}t^{2^i}$  and  $g(t) = \sum_{j \ge 0} b'_{2^j - 1}t^{2^j}$ . Then

$$(f \circ g)(t) = \sum_{i,j>0} b_{2^{i}-1} (b'_{2^{j}-1})^{2^{i}} t^{2^{i+j}}.$$

Consequently, the comultiplication on the ring  $\mathbf{F}_2[b_1,b_3,\ldots]$  can be described by the formula

$$b_{2^k-1} \mapsto \sum_{k=i+j} b_{2^i-1} \otimes b_{2^j-1}^{2^i}.$$

Here we include the extreme possibilities i=0 and j=0, in which case we agree to the convention that  $b_0=1\in \mathbf{F}_2[b_1,b_3,\ldots]$ .

**Remark 5.** The results above describe the dual Steenrod algebra  $\mathcal{A}^{\vee}$  as the algebra of functions on the algebraic group  $G \simeq \operatorname{End}(\mathbf{A}^1)$ . We get a dual description of the Steenrod algebra  $\mathcal{A}$  itself as an algebra of distributions on the group G: namely,  $\mathcal{A}$  is isomorphic to the space of distributions on G which are set-theoretically supported at the identity. In this language, the (noncommutative) multiplication on  $\mathcal{A}$  is induced by convolution.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Frobenius (Lecture 14)

Our goal in this lecture is to study some of the basic features of the category  $\mathcal{U}$  of unstable modules over the Steenrod algebra  $\mathcal{A}$ . We begin with a few general remarks.

For every commutative algebra R over the field  $\mathbf{F}_2$ , there is a canonical ring homomorphism  $F: R \to R$ , called the *Frobenius morphism*, given by  $F(x) = x^2$ . The Frobenius map is functorial with respect to all homomorphisms between commutative  $\mathbf{F}_2$ -algebras: in other words, every map  $f: R \to R'$  fits into a commutative diagram

$$\begin{array}{ccc}
R & \xrightarrow{f} R' \\
\downarrow_{F} & \downarrow_{F} \\
\downarrow_{R} & \xrightarrow{f} R'.
\end{array}$$

In particular, if R is a commutative Hopf algebra over  $\mathbf{F}_2$  with comultiplication  $\Delta: R \to R \otimes R$ , then we have a commutative diagram

$$R \xrightarrow{\Delta} R \otimes R$$

$$\downarrow^F \qquad \qquad \downarrow^{F \otimes F}$$

$$R \xrightarrow{\Delta} R \otimes R.$$

In other words, the Frobenius map F is a homomorphism of Hopf algebras.

We apply this remark in the case where R is the dual Steenrod algebra  $\mathcal{A}^{\vee} \simeq \mathbf{F}_2[b_1, b_3, b_7, \ldots]$ . We have a map of Hopf algebras

$$F: \mathcal{A}^{\vee} \to \mathcal{A}^{\vee}$$

Passing to the graded dual, we obtain another map of Hopf algebras  $V: \mathcal{A} \to \mathcal{A}$ , called the *Verschiebung*. Let us compute the map V. Since V is a map of algebras, it will suffice to compute  $V(\operatorname{Sq}^n)$  for each  $n \geq 0$ . Let  $\langle , \rangle : \mathcal{A} \otimes \mathcal{A}^{\vee} \to \mathbf{F}_2$  denote the pairing between the Steenrod algebra and its dual. By definition, we have

$$\langle V(\operatorname{Sq}^n), x \rangle = \langle \operatorname{Sq}^n, x^2 \rangle.$$

Since the algebra structure on  $\mathcal{A}^{\vee}$  is dual to the comultiplication  $\Delta: \mathcal{A} \to \mathcal{A} \otimes \mathcal{A}$ , we get

$$\langle \operatorname{Sq}^n, x^2 \rangle = \langle \Delta \operatorname{Sq}^n, x \otimes x \rangle = \sum_{n=i+j} \langle \operatorname{Sq}^i, x \rangle \langle \operatorname{Sq}^j, x \rangle.$$

We note that the terms in this sum for which  $i \neq j$  cancel in pairs. Moreover, if n is even, the term with  $i = j = \frac{n}{2}$  coincides with

$$\langle \operatorname{Sq}^i, x \rangle \langle \operatorname{Sq}^j, x \rangle = \langle \operatorname{Sq}^{\frac{n}{2}}, x \rangle.$$

We can summarize this calculation as follows:

**Proposition 1.** The Vershiebung map  $V: A \to A$  is given by the formula

$$V(\operatorname{Sq}^n) = \begin{cases} \operatorname{Sq}^{\frac{n}{2}} & n \text{ even} \\ 0 & n \text{ odd.} \end{cases}$$

**Remark 2.** We could instead regard V as being *defined* by the formula of Proposition 1. Then we would need to check that V is well-defined, which is an exercise in manipulating the Adem relations.

Let M be a module over the Steenrod algebra  $\mathcal{A}$ , so that we have a ring homomorphism  $\mathcal{A} \to \operatorname{End}(M)$ . Composing with the Vershiebung map  $V : \mathcal{A} \to \mathcal{A}$ , we get a new homomorphism  $\mathcal{A} \to \operatorname{End}(M)$ , which gives a new  $\mathcal{A}$ -module structure on M. We will denote this new  $\mathcal{A}$ -module by  $\Phi M$ . More concretely:

- (1) The elements of  $\Phi M$  can be identified with the elements of M. When it is important to distinguish between the M and  $\Phi M$ , we let  $\Phi(x)$  denote the element of  $\Phi M$  corresponding to  $x \in M$ .
- (2) The Steenrod algebra acts on  $\Phi M$  by the formula

$$\operatorname{Sq}^n \Phi(x) = \begin{cases} \Phi(\operatorname{Sq}^{\frac{n}{2}} x) & \text{n even} \\ 0 & \text{n odd.} \end{cases}$$

The map V does not preserve the grading on the Steenrod algebra A: we have instead deg  $V(a) = \frac{\deg(a)}{2}$  if a is homogeneous of even degree (and V(a) vanishes if a has odd degree). If M is a graded A-module, then  $\Phi M$  again has the structure of a graded A-module via the following convention:

(3) For each  $n \geq 0$ , we let

$$(\Phi M)^n = \begin{cases} M^{\frac{n}{2}} & \text{n even} \\ 0 & \text{n odd.} \end{cases}$$

Note that if M is an unstable  $\mathcal{A}$ -module, then  $\Phi M$  is again unstable: if x is a nonzero element of  $(\Phi M)^n$ , then n=2k is even and  $x=\Phi(x_0)$  for some  $x_0\in M^k$ . If m>n, then  $\operatorname{Sq}^m(x)$  vanishes by definition if m is odd, and is equal to  $\Phi(\operatorname{Sq}^{\frac{m}{2}}(x_0))$  if m is even; this will also vanish since  $\frac{m}{2}>k$  and M is assumed to be unstable.

**Proposition 3.** Let M be an unstable module over the Steenrod algebra A. Then there is a canonical homomorphism of A-modules

$$f: \Phi M \to M$$

defined by the formula  $f(\Phi(x)) = \Phi(\operatorname{Sq}^{\operatorname{deg} x}(x))$  when x is homogeneous.

**Remark 4.** If M is an unstable algebra over  $\mathcal{A}$ , we can rewrite the definition of f as  $f(\Phi(x)) = \Phi(x^2)$ . In other words, we can think of f as a kind of Frobenius map.

*Proof.* We must show that f is compatible with the action of the Steenrod algebra: in other words, we must show that for every homogeneous element x, we have

$$f(\operatorname{Sq}^n \Phi(x)) = \operatorname{Sq}^n \operatorname{Sq}^{\operatorname{deg} x}(x).$$

There are three cases to consider.

If  $n > 2 \deg(x)$ , then both sides vanish in view our our assumption that M is unstable. If  $n = 2 \deg(x)$ , then we have

$$f(\operatorname{Sq}^n\Phi(x)) = f(\Phi(\operatorname{Sq}^{\operatorname{deg} x}(x)) = \operatorname{Sq}^{2\operatorname{deg} x}\operatorname{Sq}^{\operatorname{deg} x}x = \operatorname{Sq}^n\operatorname{Sq}^{\operatorname{deg} x}x.$$

If  $n < 2\deg(x)$ , then we can rewrite  $\operatorname{Sq}^n \operatorname{Sq}^{\deg x}(x)$  using the Adem relations. We get

$$\operatorname{Sq}^{n} \operatorname{Sq}^{\operatorname{deg} x}(x) = \sum_{k} (2k - n, \operatorname{deg}(x) - k - 1) \operatorname{Sq}^{\operatorname{deg}(x) + k} \operatorname{Sq}^{n - k}(x).$$

Terms with 2k > n vanish since  $\deg(x) + k > \deg(\operatorname{Sq}^{n-k}(x)) = n - k + \deg(x)$ . Terms with 2k < n vanish since 2k - n < 0. We therefore have

$$\operatorname{Sq}^n \operatorname{Sq}^{\operatorname{deg} x}(x) = \begin{cases} 0 & \text{n odd} \\ \operatorname{Sq}^{\operatorname{deg} x + \frac{n}{2}} \operatorname{Sq}^{\frac{n}{2}} x & \text{n even.} \end{cases}$$

On the other hand, we have

$$\operatorname{Sq}^n(\Phi(x)) = \begin{cases} 0 & \text{n odd} \\ \Phi(\operatorname{Sq}^{\frac{n}{2}}) & \text{n even.} \end{cases}$$

and in the latter case  $\deg(\operatorname{Sq}^{\frac{n}{2}}(x)) = \deg(x) + \frac{n}{2}$ , so the desired equality holds.

Let us study the behavior of the homomorphism f in the case where M = F(n) is the free unstable  $\mathcal{A}$ -module on one generator  $\nu_n$ . In this case, M has a basis  $\{\operatorname{Sq}^I \nu_n\}$ , where I ranges over admissible positive sequences  $(i_1, \ldots, i_k)$  of excess  $\leq n$ . We observe that  $f(\Phi(\operatorname{Sq}^I \nu_n)) = \operatorname{Sq}^{I'} \nu_n$ , where I' is the sequence  $(i_0, i_1, i_2, \ldots, i_k)$  with

$$i_0 = \deg \operatorname{Sq}^I \nu_n = i_1 + i_2 + \ldots + i_k + n.$$

In particular, the excess  $i_0 - i_1 - \ldots - i_k$  of I' is precisely n. Conversely, if I' is an admissible sequence of excess n, then  $I' = (\deg \operatorname{Sq}^I \nu_n, i_1, i_2, \ldots, i_k)$ , where  $I = (i_1, i_2, \ldots, i_k)$ . In other words:

**Proposition 5.** The map  $f: \Phi F(n) \to F(n)$  is injective, and its image is spanned by expressions  $\{\operatorname{Sq}^I \nu_n\}$  where I is positive, admissible, and has excess exactly n.

The cokernel of the map  $f: \Phi F(n) \to F(n)$  has a basis given by the images of the expressions  $\{\operatorname{Sq}^I \nu_n\}$ , where I ranges over admissible positive sequences of excess < n. Up to a change of grading, this is identical to the structure of the free unstable module F(n-1). In order to describe the situation more systematically, we introduce the following definition:

**Definition 6.** Let M be an unstable module over the Steenrod algebra  $\mathcal{A}$ . We define a new unstable  $\mathcal{A}$ -module  $\Sigma M$  as follows:

- (1) As a vector space,  $\Sigma M \simeq M$ , and this isomorphism is compatible with the action of the Steenrod algebra.
- (2) The grading on  $\Sigma M$  is defined by the formula  $(\Omega M)^n \simeq M^{n-1}$ .

In other words,  $\Sigma M$  is the module  $M \otimes \mathbf{F}_2[-1]$ , where  $\mathbf{F}_2[-1]$  denotes a single copy of  $\mathbf{F}_2$  in degree 1 (with its unique A-module structure).

Warning 7. The notation introduced in Definition 6 is incompatible with our notation for suspensions of complexes used in previous lectures: if V is a complex with a good symmetric multiplication, we have an isomorphism of A-modules  $H^*(\Omega V) = \Sigma H^*(V)$ .

If M is an unstable A-module, then  $\Sigma M$  is again unstable. However,  $\Sigma$  does not define an equivalence from the category  $\mathcal{U}$  to itself, because the obvious "inverse" construction does not preserve instability. For each unstable A-module M, let  $\overline{\Omega}M$  denote the A-module M, with the grading  $(\overline{\Omega}M)^n \simeq M^{n+1}$ . Then  $\overline{\Omega}M$  is not necessarily unstable: an element  $x \in (\overline{\Omega}M)^n$  can be identified with an element  $x \in M^{n+1}$ , so that x need not be annihilated by  $\operatorname{Sq}^{n+1}$ . However, we can correct this deficiency by passing to a quotient: let  $\Omega M$  denote the quotient of  $\overline{\Sigma}M$  by the submodule generated by  $\operatorname{Sq}^k x$  for k > n,  $x \in (\overline{\Sigma}M)^n$ . (In fact, it suffices to take k = n + 1 here). Then the construction  $M \mapsto \Omega M$  defines a functor from the category of unstable A-modules to itself, and this construction is left adjoint to the functor  $\Sigma$ .

We observe that, for every unstable A-module M, we have a canonical isomorphism

$$\operatorname{Hom}_{\mathcal{A}}(\Omega F(n), M) \simeq \operatorname{Hom}_{\mathcal{A}}(F(n), \Sigma M) \simeq (\Sigma M)^n \simeq M^{n-1}.$$

Conequently, we can identify  $\Omega F(n)$  with F(n-1) as an unstable  $\mathcal{A}$ -module. The adjoint of this identification is a map  $F(n) \to \Sigma F(n-1)$ . We can restate Proposition 5 as follows:

**Proposition 8.** For each n > 0, we have a short exact sequence

$$0 \to \Phi F(n) \xrightarrow{f} F(n) \xrightarrow{u} \Sigma \Omega F(n) \to 0$$

where u is the unit map for the adjunction between  $\Omega$  and  $\Sigma$  and f is the map of Proposition 3.

Proposition 8 admits a generalization where we replace F(n) by an arbitrary unstable  $\mathcal{A}$ -module M. We observe that the functors  $M \mapsto \Phi M$  and  $M \to \Sigma M$  are obviously exact. However, the functor  $M \mapsto \Omega M$  is only right exact. We can therefore define left-derived functors  $L^i\Omega M$  to be the homologies of the complex

$$\ldots \to \Omega P_2 \to \Omega P_1 \to \Omega P_0 \to 0$$
,

where ...  $\rightarrow P_1 \rightarrow P_0 \rightarrow M$  is a resolution of M by free unstable A-modules. A standard argument in homological algebra shows that this definition is independent of the choice of resolution, up to canonical isomorphism.

**Theorem 9.** For every unstable A-module M, there is a canonical exact sequence

$$0 \to \Sigma L^1 \Omega M \to \Phi M \xrightarrow{f} M \xrightarrow{u} \Sigma \Omega M \to 0$$

where u is the unit map for the adjunction between  $\Sigma$  and  $\Omega$ , and f is the map described in Proposition 3. Moreover, the derived functors  $L^i\Omega$  vanish for i > 1.

*Proof.* Choose a free resolution  $P_{\bullet}$  of M. Using Proposition 8, we get a short exact sequence of complexes

$$0 \to \Phi P_{\bullet} \to P_{\bullet} \to \Sigma \Omega P_{\bullet} \to 0.$$

The desired result now follows from the associated long exact sequence, since the complexes  $\Phi P_{\bullet}$  and  $P_{\bullet}$  are exact in degrees > 0.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Finiteness Conditions (Lecture 15)

Our goal in this lecture is to prove that the category  $\mathcal{U}$  of unstable  $\mathcal{A}$ -modules is locally Noetherian. We begin with by recalling a few definitions.

**Definition 1.** An object X of a Grothendieck abelian category  $\mathcal{C}$  is *Noetherian* if every ascending chain of subobjects

$$X_0 \subseteq X_1 \subseteq X_2 \subseteq \dots$$

eventually stabilizes.

We will say that a Grothendieck abelian category  $\mathcal{C}$  is locally Noetherian if every object  $X \in \mathcal{C}$  is the direct limit of its Noetherian subobjects. direct limit

Remark 2. Suppose given an exact sequence

$$0 \to X' \to X \to X'' \to 0$$

in a Grothendieck abelian category  $\mathcal{C}$ . Then X is Noetherian if and only if X' and X'' are Noetherian. The "only if" direction is clear: any infinite ascending sequence of subobjects of X' or X'' gives rise to an infinite ascending sequence of subobjects of X. For the converse, we observe that an infinite ascending sequence of objects

$$X_0 \subseteq X_1 \subseteq X_2 \subseteq \ldots \subseteq X$$

gives rise to a collection of long exact sequences

$$0 \to X_i \cap X' \to X_i \to (\operatorname{Im} X_i \to X'') \to 0.$$

If X' and X'' are Noetherian, then the subobjects  $X_i \cap X'$  and  $\operatorname{Im} X_i \to X''$  are independent of i for  $i \gg 0$ , so that  $X_i$  is also independent of i for  $i \gg 0$ .

In particular, the collection of Noetherian objects of C is closed under finite direct sums.

**Example 3.** Let R be a (left) Noetherian ring. Then the category  $\mathcal{C}$  of (left) R-modules is locally Noetherian. An object  $X \in \mathcal{C}$  is Noetherian if and only if it is finitely generated as an R-module.

The Steenrod algebra  $\mathcal{A}$  itself is *not* left Noetherian. For example, the left ideal of  $\mathcal{A}$  generated by  $\{Sq^i\}_{i>0}$  is not finitely generated. Nevertheless, we have the following analogue of Example 3:

**Theorem 4.** (1) The category U of unstable A-algebras is locally Noetherian.

(2) An object  $M \in \mathcal{U}$  is Noetherian if and only if it is finitely generated as a A-module.

The implication  $(2) \Rightarrow (1)$  is clear, since every object in  $\mathcal{U}$  is the direct limit of its finitely generated subobjects. The "only if" direction follows formally from the following observation:

**Lemma 5.** An object  $M \in \mathcal{U}$  is Noetherian if and only if every submodule  $M' \subseteq M$  is finitely generated.

*Proof.* If  $M' \subseteq M$  is not finitely generated, then we can find an infinite ascending sequence of submodules

$$A x_1 \subset A x_1 + A x_2 \subset \ldots \subseteq M'$$

by choosing each  $x_i$  to be an element of M' which does not belong to the submodule generated by  $\{x_j\}_{j< i}$ . Conversely, if M is not Noetherian, we can find an infinite ascending sequence of submodules

$$M_0 \subset M_1 \subset M_2 \subset \dots$$

Let  $M' = \bigcup M_i \subseteq M$ . Then M' cannot be finitely generated: if it were, then it would be generated by elements belonging to  $M_n$  for  $n \gg 0$ , so that  $M_{n+1} \subseteq M_n$ , contrary to our assumption.

We wish to prove that *every* finitely generated unstable A-module M is Noetherian. In this case, we can write M as a quotient of a finite sum  $\bigoplus_i F(n_i)$ . Remark 2 implies that the collection of Noetherian objects of  $\mathcal{U}$  is stable under finite direct sums and quotients. In view of Lemma 5, it will suffice to prove the following:

**Theorem 6.** Let F(n) denote the free unstable A-module on a single generator  $\nu_n$  in degree n. Then every submodule  $M \subseteq F(n)$  is finitely generated.

We will prove Theorem 6 using induction on n. The case n = 0 is obvious. To handle the general case, we will need the following:

**Lemma 7.** Let M be an unstable A-module. If  $\Omega M$  is finitely generated and  $M^0$  is finitely generated, then M is finitely generated.

*Proof.* If  $\Omega M$  is finitely generated, then  $\Sigma \Omega M$  is finitely generated. In the last lecture, we saw that there is an exact sequence

$$\Phi M \to M \to \Sigma \Omega M \to 0$$
.

Choose a finite set of (homogeneous) generators  $\{\overline{x}_i\}$  for  $\Sigma\Omega M$ , and lift them to (homogeneous) elements  $\{x_i \in M\}$ . Let N be the submodule of M generated by  $M^0$  and  $\{x_i\}$ . We claim that N = M. We will prove by induction that  $N^n = M^n$  for all integers n. If n = 0 there is nothing to prove. If n is odd, then the exact sequence above gives  $M^n \simeq (\Sigma\Omega M)^n$ , and the result is obvious. If n = 2k > 0 is even, then our exact sequence can be rewritten

$$M^k \stackrel{\operatorname{Sq}^k}{\to} M^{2k} \to (\Sigma \Omega M)^{2k} \to 0.$$

It is clear that  $M^{2k}$  is generated by  $N^{2k}$  together with the image of  $\operatorname{Sq}^k$ . The inductive hypothesis guarantees that  $\operatorname{Sq}^k M^k = \operatorname{Sq}^k N^k \subseteq N^{2k}$ , so that  $M^{2k} = N^{2k}$  as desired.

We are now ready to proceed with the proof of Theorem 6.

We define an ascending chain of submodules

$$M = M_0 \subseteq M_1 \subseteq \ldots \subseteq F(n)$$

as follows: let  $M_n$  be defined so that  $\Phi^n M_n$  is the inverse image of  $M=M_0$  under the iterated Frobenius map

$$\Phi^n F(n) \to \Phi^{n-1} F(n) \to \ldots \to F(n).$$

We have for each  $m \geq 0$  an exact sequence

$$\Phi M_{m+1} \to M_m \to M'_m \to 0$$
,

where  $M'_m$  denotes the image of  $M_m$  in  $\Sigma\Omega F(n)\simeq \Sigma F(n-1)$ . The inductive hypothesis implies that every ascending sequence of submodules of F(n-1) stabilizes, so that  $M'_m=M'_{m+1}$  for  $m\geq m_0$ .

We claim also that  $M_m = M_{m+1}$  for  $m \ge m_0$ . To prove this, we show by induction on k that the sequence

$$M_{m_0}^k \subseteq M_{m_0+1}^k \subseteq M_{m_0+2}^k \subseteq \dots$$

is constant. If k=0 there is nothing to prove. For k>0, we have exact sequences

$$M_{m+1}^{\frac{k}{2}} \stackrel{\operatorname{Sq}^{\frac{k}{2}}}{\to} M_m^k \to M_m^{\prime k} \to 0$$

(here the left term vanishes by convention if k is odd). The desired result follows from the inductive hypothesis (since  $\frac{k}{2} < k$ ).

We now prove that each  $M_m$  is finitely generated, using descending induction on m. We observe that  $\Sigma\Omega M_{m_0}\simeq M'_{m_0}$  is a submodule of  $\Sigma F(n-1)$ , and therefore finitely generated by our inductive hypothesis. Therefore  $M_{m_0}$  is finitely generated by Lemma 7.

To handle the general case, we use the exact sequence

$$\Phi M_{m+1} \to M_m \to M_m' \to 0.$$

The inductive hypothesis guarantees that  $M_{m+1}$  is finitely generated. Let  $\{x_i\}$  be a finite set of generators for  $M_{m+1}$ . Then  $\{\Phi(x_i)\}$  is a finite set of generators for  $\Phi M_{m+1}$ . Let  $\{y_i\}$  denote the images of these generators in  $M_m$ . Since  $M'_m$  is a submodule of  $\Sigma F(n-1)$ , we deduce that  $M'_m$  is generated by a finite set of elements  $\{\overline{z}_j\}$ . Choose elements  $\{z_j\}$  in  $M_m$  which lift these elements. It is now clear that  $M_m$  is generated by the finite set  $\{y_i\} \cup \{z_j\}$ . This completes the proof of Theorem 6.

Our next goal in this lecture is to prove the following result:

**Proposition 8.** The collection of finitely generated unstable A-modules is closed under the formation of tensor products.

In other words, we wish to show that if M and N are finitely generated, then  $M \otimes N$  is finitely generated. We can write M as a quotient some finite sum  $\bigoplus_i F(m_i)$ , so that  $M \otimes N$  is a quotient of some finite sum  $\bigoplus_i (F(m_i) \otimes N)$ . It will therefore suffice to show that each  $F(m_i) \times N$  is finitely generated. Applying the same argument to N, we are reduced to proving the following special case of Proposition 8:

**Proposition 9.** For every pair of nonnegative integers  $m, n \ge 0$ , the tensor product  $F(m) \otimes F(n)$  is finitely generated.

To prove Proposition 9, we first recall the structure of the free unstable  $\mathcal{A}$ -module F(n). Let X denote a product of n copies of  $\mathbf{R}P^{\infty}$ , so that  $\mathrm{H}^*(X) \simeq \mathbf{F}_2[t_1,t_2,\ldots,t_n]$ . Then we can identify F(n) with the  $\mathcal{A}$ -submodule of  $\mathrm{H}^*(X)$  generated by the element  $t_1 \ldots t_n \in \mathrm{H}^n(X)$ . Moreover, we have an explicit description of this submodule: it consists of those polynomials  $f(t_1,\ldots,t_n)$  which are symmetric and whose exponents involve only powers of 2. In particular, F(1) can be identified with the  $\mathcal{A}$ -module of  $\mathbf{F}_2[t]$  spanned by  $\{t,t^2,t^4,\ldots\}$ . We can therefore identify F(n) with the submodule of  $F(1)^{\otimes n}$  spanned by the symmetric polynomials: in other words, we have an isomorphism

$$F(n) \simeq (F(1)^{\otimes n})^{\Sigma_n} \subseteq F(1)^{\otimes n}$$
.

Let us turn to the proof of Proposition 9. We have an inclusion

$$F(m) \otimes F(n) \subset (F(1)^{\otimes m}) \otimes (F(1)^{\otimes n}) \simeq F(1)^{\otimes m+n}$$

Since the collection of finitely generated unstable A-modules is closed under the formation of subobjects, it will suffice to prove the following:

**Proposition 10.** For each n > 0, the A-module  $F(1)^{\otimes n}$  is finitely generated.

The proof goes by induction on n, the case n=0 being obvious. To handle the general case, we use Lemma 7: it will suffice to show that  $\Sigma\Omega F(1)^{\otimes n}$  is finitely generated. We observe that  $F(1)^{\otimes n}$  can be identified with the submodule of  $\mathbf{F}_2[t_1,\ldots,t_n]$  spanned by monomials of the form  $t_1^{2^{b_1}}\ldots t_n^{2^{b_n}}$ . We have an exact sequence

$$\Phi F(1)^{\otimes n} \xrightarrow{f} F(1)^{\otimes n} \to \Sigma \Omega F(1)^{\otimes n} \to 0$$

The map f can be identified with the usual Frobenius map which sends each element to its square. Its image consists of the span of those monomials  $t_1^{2^{b_1}} \dots t_n^{2^{b_n}}$  such that each  $b_i$  is positive. Consequently,  $\Sigma \Omega F(1)^{\otimes n}$  can be identified with a submodule of

$$\bigoplus_{1 \leq i \leq n} F(1)^{\otimes i} \otimes \Sigma \mathbf{F}_2 \otimes F(1)^{\otimes n-i-1} \simeq \bigoplus_{1 \leq i \leq n} \Sigma F(1)^{\otimes n-1},$$

which is finitely generated by the inductive hypothesis.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Some Unstable Injectives (Lecture 16)

Let  $\mathcal{U}$  denote the category of unstable modules over the Steenrod algebra  $\mathcal{A}$ . Then  $\mathcal{U}$  has enough projective objects: that is, for every unstable  $\mathcal{A}$ -module M, there exists a surjection  $P \to M$ , where P is projective. For example, we can take  $P = \bigoplus_{x \in M^n} F(n)$ , equipped with its evident map to M.

The category  $\mathcal{U}$  also has enough injective objects: that is, for every unstable  $\mathcal{A}$ -module M, there exists an injection  $M \to I$ , where I is injective. This is a general property of Grothendieck abelian categories (as demonstrated by Grothendieck). However, in the case of the category  $\mathcal{U}$  we can verify this directly, by producing a large class of injective objects:

**Proposition 1.** Let  $n \ge 0$  be a nonnegative integer. Then there exists an unstable A-module J(n) equipped with a map  $\chi : J(n)^n \to \mathbf{F}_2$  with the following universal property: for every unstable A-module M, composition with  $\chi$  induces a bijection

$$\operatorname{Hom}_{\mathcal{A}}(M,J(n)) \to \operatorname{Hom}_{\mathbf{F}_2}(M^n,\mathbf{F}_2).$$

*Proof.* We sketch two different arguments.

First, the existence of J(n) follows by abstract nonsense. If  $\mathcal{C}$  is any category, then we say a functor  $F: \mathcal{C}^{op} \to \text{Set}$  is representable if there exists an object  $X \in \mathcal{C}$  and a collection of bijections

$$F(C) \simeq \operatorname{Hom}_{\mathfrak{C}}(C, X),$$

depending functorially on C. Any representable functor carries colimits in  $\mathcal{C}$  to limits in  $\mathcal{S}$ et (essentially by definition). If  $\mathcal{C}$  is a Grothendieck abelian category, then the converse holds (more generally, the converse holds whenever  $\mathcal{C}$  is a *presentable* category). We apply this observation to the case  $\mathcal{C} = \mathcal{U}$ , and  $F : \mathcal{U}^{op} \to \mathcal{S}$ et is defined by the formula

$$M \mapsto (M^n)^{\vee}$$
.

It is easy to see that F carries colimits to limits, so that F is representable by an unstable A-module J(n). An alternative approach is to describe J(n) directly. The universal property of J(n) dictates its structure: for each integer k, we have

$$J(n)^k \simeq \operatorname{Hom}_{\mathcal{A}}(F(k), J(n)) \simeq (F(k)^n)^{\vee}.$$

For each  $i \ge 0$ , the map  $\operatorname{Sq}^i: J(n)^k \to J(n)^{k+i}$  is dual to the map  $F(k+i)^n \to F(k)^n$  induced by the map of unstable  $\mathcal{A}$ -modules  $F(k+i) \to F(k)$  classified by the element  $\operatorname{Sq}^i \nu_k \in F(k)^{k+i}$ . It is not difficult to check that this endows

$$J(n) = \bigoplus_k J(n)^k = \bigoplus_k (F(k)^n)^{\vee}$$

with the structure of an unstable A-module, and that this module has the desired universal property (exercise).

The A-modules J(n) are called *Brown-Gitler modules*, because they arise as the  $\mathbf{F}_2$ -homology of certain spectra called *Brown-Gitler spectra*. We will not use this description in this course.

For each  $n \geq 0$ , the Brown-Gitler module J(n) represents the functor  $M \mapsto (M^n)^{\vee}$ . Since this functor is exact, the object  $J(n) \in \mathcal{U}$  is injective.

Corollary 2. The category U has enough injective objects.

*Proof.* Let M be an unstable A-module. To every map  $f: M^n \to \mathbf{F}_2$ , we can associate a map of A-modules  $M \to J(n)$ . Taking the product over all pairs (n, f), we obtain a map

$$M \to \prod_{f:M^n \to \mathbf{F}_2} J(n).$$

This map is clearly injective. The right hand side is a product of Brown-Gitler modules, and therefore injective.  $\Box$ 

Our next goal is to describe some other examples of injective objects in  $\mathcal{U}$ .

We have already met some other examples of injective objects of  $\mathcal{U}$ : namely, the cohomology rings  $H^*(BV)$ , where V is a finite dimensional vector space over  $\mathbf{F}_2$ . These are very different from the Brown-Gitler modules J(n). For example, for n > 0, the Brown-Gitler module J(n) is nilpotent: that is, for every homogeneous element  $x \in J(n)$ , the sequence

$$x, \operatorname{Sq}^{\operatorname{deg}(x)} x, \operatorname{Sq}^{2\operatorname{deg}(x)} \operatorname{Sq}^{\operatorname{deg}(x)} x, \dots$$

is eventually zero (since J(n) vanishes in degrees > n). On the other hand, the cohomology ring  $H^*(BV)$  is isomorphic to a polynomial ring, and is therefore reduced: the map  $x \mapsto \operatorname{Sq}^{\operatorname{deg}(x)} x$  is injective.

The injective objects  $H^*(BV)$  have an unusual property: namely, the tensor product of any pair  $H^*(BV) \otimes H^*(BW)$  isomorphic to  $H^*(B(V \oplus W))$ , and is therefore again injective. In fact, the operation  $M \mapsto H^*(BV) \otimes M$  preserves injective objects in general. We wish to prove this in the case where M is a Brown-Gitler module. For this, we need to introduce some auxiliary constructions.

**Proposition 3.** The inverse limit K of any sequence

$$\ldots \to J(n_2) \to J(n_1) \to J(n_0)$$

of Brown-Gitler modules is injective as an unstable A-module.

*Proof.* By definition, we have

$$\operatorname{Hom}_{\mathcal{A}}(M,K) \simeq \operatorname{proj} \lim \operatorname{Hom}_{\mathcal{A}}(M,J(n_i))$$
  
 $\simeq \operatorname{proj} \lim (M^{n_i})^{\vee}$   
 $\simeq (\operatorname{inj} \lim M^{n_i})^{\vee}.$ 

This is an exact functor, since it is dual to the exact functor

$$M \mapsto \operatorname{inj} \lim (M^{n_0} \to M^{n_1} \to \dots).$$

To apply Proposition 3, we need to understand maps between the Brown-Gitler modules J(k). This is easy: by definition, we have

$$\begin{array}{ccc} \operatorname{Hom}_{\mathcal{A}}(J(m),J(n)) & \simeq & (J(m)^n)^{\vee} \\ & \simeq & \operatorname{Hom}_{\mathcal{A}}(F(n),J(m))^{\vee} \\ & \simeq & ((F(n)^m)^{\vee})^{\vee} \\ & \simeq & F(n)^m \\ & \simeq & \operatorname{Hom}_{\mathcal{A}}(F(m),F(n)) \end{array}$$

In particular,  $\operatorname{Hom}_{\mathcal{A}}(J(m), J(n))$  has a basis consisting of Steenrod operations  $\{\operatorname{Sq}^I\}$ , where I is positive, admissible,  $\deg(I) = m - n$ , and the excess of I is  $\leq n$ . We will abuse notation and identify the elements  $\operatorname{Sq}^I \in \mathcal{A}$  with the corresponding maps between Brown-Gitler modules.

**Definition 4.** Let n be a nonnegative integer. The Carlsson module K(n) is defined to be the inverse limit of the sequence

$$\dots \to J(4n) \stackrel{\operatorname{Sq}^{2n}}{\to} J(2n) \stackrel{\operatorname{Sq}^n}{\to} J(n).$$

From Proposition 3 we immediately deduce:

**Corollary 5.** For each  $n \geq 0$ , the Carlsson module K(n) is an injective object of  $\mathcal{U}$ .

From this description, we immediately deduce:

**Proposition 6.** Let M be an unstable A-module, and let n be a nonnegative integer. Then the canonical map  $\Phi M \to M$  induces an isomorphism

$$\operatorname{Hom}_{\mathcal{A}}(M,K(n)) \to \operatorname{Hom}_{\mathcal{A}}(\Phi M,K(n)).$$

Corollary 7. Let M be an unstable A-module, and let n be a nonnegative integer. Then  $\operatorname{Hom}_{\mathcal{A}}(\Sigma M, K(n)) = 0$ .

*Proof.* This follows from Proposition 6, since the map  $\Phi \Sigma M \to \Sigma M$  vanishes (this follows from the instability condition on M).

An unstable  $\mathcal{A}$ -module M is reduced if the canonical map  $f: \Phi M \to M$ . In other words, M is reduced if  $\operatorname{Sq}^{\operatorname{deg} x} x = 0$  implies that x = 0, for every homogeneous element  $x \in M$ . If M is an unstable  $\mathcal{A}$ -algebra, then the map  $x \mapsto \operatorname{Sq}^{\operatorname{deg} x} x$  coincides with the map  $x \mapsto x^2$ , so that M is reduced if and only if it contains no nilpotent elements (this is the usual meaning of the term reduced in commutative algebra).

Corollary 8. For every nonnegative integer n, the Carlsson module K(n) is reduced.

*Proof.* Let M denote the submodule of K(n) generated by those homogeneous elements  $x \in K(n)^k$  such that  $\operatorname{Sq}^k x = 0$ . Then the map  $\Phi M \to M$  vanishes, so  $M \simeq \Sigma \Omega M$ . Applying Corollary 7, we conclude that the inclusion  $M \subseteq K(n)$  is the zero map, so that M = 0.

Suppose that M is a reduced unstable A-module. Then any map  $M \to J(n)$  factors through K(n). Equivalently, any functional on  $M^n$  can be extended to the direct limit

$$M^n \stackrel{\operatorname{Sq}^n}{\to} M^{2n} \stackrel{\operatorname{Sq}^{2n}}{\to} M^{4n} \to \dots;$$

this follows from the observation that  $M^n$  injects into this direct limit. Consequently, the embedding

$$M \to \prod_{f:M^n \to \mathbf{F}_2} J(n)$$

of Corollary 2 can be lifted to a map

$$M \to \prod_{f:M^n \to \mathbf{F}_2} K(n).$$

It is easy to see that this map is again injective. We have therefore proven:

**Proposition 9.** Let M be a reduced unstable A-module. Then there exists a monomorphism

$$M \to \prod_{\alpha} K(n_{\alpha})$$

for some collection of nonnegative integers  $\{n_{\alpha}\}.$ 

Corollary 10. Let V be a finite dimensional vector space over  $\mathbf{F}_2$ . Then the unstable A-module  $\mathbf{H}^*(BV)$  is isomorphic to a direct summand of some product  $\prod_{\alpha} K(n_{\alpha})$ .

*Proof.* The cohomology ring  $H^*(BV)$  is isomorphic to a polynomial ring  $\mathbf{F}_2[t_1,\ldots,t_n]$ , and therefore contains no nilpotent elements. Consequently,  $H^*(BV)$  is reduced as an unstable  $\mathcal{U}$ -module. Applying Proposition 9, we deduce the existence of a monomorphism

$$j: \mathrm{H}^*(BV) \to \prod_{\alpha} K(n_{\alpha}).$$

We saw earlier that the unstable A-module  $H^*(BV)$  is injective. Consequently, the identity map id:  $H^*(BV) \to H^*(BV)$  can be extended to a map  $p: \prod_{\alpha} K(n_{\alpha}) \to H^*(BV)$ , which is a left inverse to j. We therefore obtain a direct sum decomposition

$$\prod_{\alpha} K(n_{\alpha}) \simeq \mathrm{H}^{*}(BV) \oplus \ker(p).$$

Since the Brown-Gitler modules J(k) are finite-dimensional in each degree, the operation  $M \mapsto M \otimes J(k)$  preserves products. Consequently, we deduce the following:

Corollary 11. Let V be a finite dimensional vector space over  $\mathbf{F}_2$ , and k a nonnegative integer. Then the tensor product

$$H^*(BV) \otimes J(k)$$

is a direct summand of some product

$$\prod_{\alpha} K(n_{\alpha}) \otimes J(k).$$

Consequently, to prove that a tensor product  $H^*(BV) \otimes J(k)$  is injective, it will suffice to show that each tensor product  $K(n) \otimes J(k)$  is injective. We will return to this point next time.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Injectivity of Tensor Products (Lecture 17)

Our goal in this lecture is to prove the following result:

**Theorem 1.** Let n and k be nonnegative integers. Then the tensor product  $K(n) \otimes J(k)$  is an injective object in the category of unstable A-modules.

We begin with some general remarks. For every nonnegative integer p, the Brown-Gitler module J(p) comes equipped with a canonical functional  $J(p)^p \to \mathbf{F}_2$ . Given a pair of integers  $p, q \geq 0$ , we obtain an induced map

$$(J(p) \otimes J(q))^{p+q} \to J(p)^p \otimes J(q)^q \to \mathbf{F}_2 \otimes F_2 \simeq \mathbf{F}_2,$$

which induces a map

$$\mu_{p,q}: J(p) \otimes J(q) \to J(p+q).$$

The proof of Theorem 1 depends on the following observation:

**Lemma 2.** Fix nonnegative integers n, k, and a. Then the map

$$\mu_{2^p n, k}^a : (J(2^p n) \otimes J(k))^a \to J(2^p n + k)^a$$

is an isomorphism for  $p \gg 0$ .

We now give the proof of Theorem 1, assuming Lemma 2. For each  $m \geq 0$ , let  $f: J(2m) \to J(m)$  be the map of Brown-Gitler modules corresponding to the Steenrod operation  $\operatorname{Sq}^m$ . For  $0 \leq p \leq q$ , let  $F_{p,q}: J(2^q n) \to J(2^p n)$  denote the composition

$$J(2^q n) \xrightarrow{f} \dots \xrightarrow{f} J(2^p n).$$

We will construct a sequence of integers  $0 = p_0 < p_1 < p_2 < \dots$  and maps  $G_i : J(2^{p_{i+1}}n + k) \to J(2^{p_i}n + k)$  such that the diagrams

$$J(2^{p_{i+1}}n) \otimes J(k) \longrightarrow J(2^{p_{i+1}}n+k)$$

$$\downarrow^{F_{p_{i+1},p_i} \otimes \mathrm{id}} \qquad \qquad \downarrow^{G_i}$$

$$J(2^{p_i}n) \otimes J(k) \longrightarrow J(2^{p_i}n+k)$$

are commutative. In fact, the existence and uniqueness of  $G_i$  are clear as soon as the upper horizontal map is an isomorphism in degree  $2^{p_i}n + k$ . Lemma 2 implies that this is true provided that  $p_{i+1}$  is chosen large enough.

By definition, the Carlsson module K(n) is defined to be the inverse limit of the sequence

$$\dots \to J(4n) \to J(2n) \xrightarrow{f} J(n).$$

It can equally well be defined as the inverse limit of the subsequence

$$\dots \to J(2^{p_2}n) \to J(2^{p_1}n) \to J(2^{p_0}n).$$

Since J(k) is finite dimensional, we can identify  $K(n) \otimes J(k)$  with the inverse limit of the sequence

$$\dots \to J(2^{p_2}n) \otimes J(k) \to J(2^{p_1}n) \otimes J(k) \to J(2^{p_0}n) \otimes J(k).$$

The multiplication maps  $\mu_{2^{p_i}n,k}$  determine a homomorphism from this inverse system to the inverse system

$$\dots \to J(2^{p_2}n+k) \xrightarrow{G_1} J(2^{p_1}n+k) \xrightarrow{G_0} J(2^{p_0}n+k).$$

For every  $a \ge 0$ , Lemma 2 guarantees that  $\mu_{2^{p_i}n,k}$  is an isomorphism in degree a for  $i \gg 0$ . Consequently, we get an isomorphism of inverse limits

$$K(n) \otimes J(k) \simeq \lim \{J(2^{p_i} + k)\}_{i > 0}.$$

In the last lecture, we saw that any inverse limit of Brown-Gitler modules is injective. It follows that  $K(n) \otimes J(k)$  is injective, as desired.

We now turn to the proof of Lemma 2. The domain of  $\mu_{2p_{n,k}}^{a_{p_{n,k}}}$  can be identified with the direct sum

$$\bigoplus_{a=a'+a''} J(2^p n)^{a'} \otimes J(k)^{a''}.$$

Recall that, for every pair of integers x and y, we have canonical isomorphisms

$$J(x)^y \simeq \operatorname{Hom}_{\mathcal{A}}(F(y), J(x)) = (F(y)^x)^{\vee}.$$

Using these isomorphisms, we can identify  $\mu_{2p_{n,k}}^{a}$  with the dual of the canonical map

$$\phi: F(a)^{2^p n + k} \to \bigoplus_{a = a' + a''} F(a')^{2^p n} \otimes F(a'')^k.$$

Let us identify F(m) with the subspace of the polynomial ring  $\mathbf{F}_2[t_1,\ldots,t_m]$  consisting of symmetric additive polynomials. For each monomial  $f=t_1^{i_1}\ldots t_m^{i_m}$ , let  $\sigma(f)$  denote the symmetrization of f as in Lecture 7, so that f appears in  $\sigma(f)$  with multiplicity one. Then  $F(a)^{2^p n+k}$  has a basis consisting of the symmetrizations of monomials of the form

$$t_1^{2^{i_1}} \dots t_a^{2^{i_a}}$$

where  $i_1 \leq i_2 \leq \ldots \leq i_a$ , and  $\sum 2^{i_j} = 2^p n + k$ . If  $p \gg 0$ , then Lemma 3 below implies that there exists a unique  $a'' \leq a$  such that

$$2^{i_1} + \ldots + 2^{i_{a''}} = k$$
$$2^{i_{a''+1}} + \ldots + 2^{i_a} = 2^p n$$

We now observe that  $\phi$  carries  $\sigma(t_1^{2^{i_1}} \dots t_a^{2^{i_a}})$  to the tensor product

$$\sigma(t_1^{2^{i_{a''+1}}} \dots t_{a'}^{2^{i_a}}) \otimes \sigma(t_1^{2^{i_1}} \dots t_{a''}^{2^{i_{a''}}}),$$

and that these tensor products form a basis for

$$\bigoplus_{a=a'+a''} F(a')^{2^p n} \otimes F(a'')^k.$$

It remains only to verify:

**Lemma 3.** Fix nonnegative integers n, k, and a. Then for every sufficiently large integer p and every equation

$$2^p n + k = 2^{i_1} + \ldots + 2^{i_a},$$

there exists a unique partition  $\{1, \ldots, a\} = J \coprod J'$ , such that

$$2^p n = \sum_{i \in J} 2^{i_j}$$

$$k = \sum_{i \in J'} 2^{i_j}.$$

*Proof.* Let  $2^b$  be the smallest power of 2 larger than k. We will prove that the assertion is true provided that Let  $J_0 = \{1 \le j \le a : i_j > b\}$ , and let  $J_0' = \{1 \le j \le a : i_j \le b\}$ . It is clear that any decomposition  $\{1, \ldots, a\} = J \coprod J'$  must satisfy  $J' \subseteq J_0'$ : otherwise, we have

$$\sum_{j \in J'} 2^{i_j} > 2^b \ge k.$$

We will show that  $\sum_{j \in J'_0} 2^{i_j} = k$  provided that p is sufficiently large. Then the containment  $J' \subseteq J'_0$  forces  $J' = J'_0$ , so that  $(J_0, J'_0)$  is the unique partition with the desired property.

Since every base 2-digit of k must appear in the sum  $2^{i_1} + \ldots + 2^{i_a}$ , we deduce that  $\sum_{j \in J'_0} 2^{i_j} \geq k$ . Let  $k' = (\sum_{i \in J'_0} 2^{i_j}) - k$ . We wish to prove that k' = 0. Suppose otherwise. We note that  $k' \leq a 2^b$ . Moreover,

$$k' + \sum_{j \in J_0} 2^{i_j} = 2^p n$$

is divisible by  $2^p$ . It follows that the largest nonzero digit of k' is at least  $2^{p-a}$ . On the other hand, k' is bounded above by  $a2^b$ , which is  $< 2^{p-a}$  provided that  $p \gg 0$ .

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lannes' T-functor (Lecture 18)

In this lecture we will introduce Lannes' T-functor and verify some of its basic properties. We begin with a definition.

**Definition 1.** Let M be an unstable A-module. We will say that M is *finite type* if each graded piece  $M^n$  is finite dimensional.

**Proposition 2.** Let M be an unstable A-module of finite type. Then the functor

$$N \mapsto M \otimes N$$

admits a left adjoint, which we will (temporarily) denote by  $D_M$ .

*Proof.* According to the adjoint functor theorem, the main thing we need to check is that the functor  $N \mapsto M \otimes N$  preserves limits. This follows immediately from the assumption that M is of finite type. Thus, the existence of  $D_M$  follows from abstract categorical nonsense.

We will sketch another proof which described how to compute  $D_M$  in practice. We first describe the value of  $D_M$  on a free unstable A-module F(n). By definition, we need

$$\operatorname{Hom}_{\mathcal{A}}(D_{M}F(n), N) \simeq \operatorname{Hom}_{\mathcal{A}}(F(n), M \otimes N)$$

$$\simeq (M \otimes N)^{n}$$

$$\simeq \oplus_{n=n'+n''} M^{n'} \otimes N^{n''}$$

$$\simeq \oplus_{n=n'+n''} \operatorname{Hom}_{\mathcal{A}}((M^{n'})^{\vee} \otimes F(n''), N).$$

This is obviously satisfied if we take  $D_M F_n = \bigoplus_{n=n'+n''} (M^{n'})^{\vee} \otimes F(n'')$ .

We now extend the definition of  $D_M$  to the category of all unstable A-modules in such a way that  $D_M$  commutes with colimits. To define  $D_M(N)$ , we choose an exact sequence

$$\bigoplus_{\beta} F(n_{\beta}) \to \bigoplus_{\alpha} F(n_{\alpha}) \to N \to 0,$$

and define  $D_M(N)$  to be the cokernel of the induced map

$$\bigoplus_{\beta} D_M F(n_{\beta}) \to \bigoplus_{\alpha} D_M F(n_{\alpha}).$$

It is easy to verify that this cokernel has the desired universal property.

**Example 3.** Let  $M = \Sigma \mathbf{F}_2$ , so that the functor  $N \mapsto N \otimes M$  is equivalent to the suspension functor  $\Sigma$ . Then  $D_M$  is isomorphic to the functor  $\Omega$  studied in a previous lecture.

**Definition 4.** Let V be a finite dimensional vector space over  $\mathbf{F}_2$ . Then the cohomology ring  $M = \mathrm{H}^*(BV)$  is an unstable  $\mathcal{A}$ -module of finite type. We will denote the functor  $D_M$  in this case by  $T_V$ . The functor  $T_V$  is called Lannes' T-functor.

**Remark 5.** Let X be an arbitrary topological space, and let  $X^{BV}$  denote the space of maps from BV into X. We have a canonical evaluation map

$$X^{BV} \times BV \to X$$
.

This induces a pullback map on cohomology

$$\mathrm{H}^*(X) \to \mathrm{H}^*(X^{BV} \times BV) \simeq \mathrm{H}^*(X^{BV}) \otimes \mathrm{H}^*(BV).$$

This determines an adjoint map

$$T_V \operatorname{H}^*(X) \to \operatorname{H}^*(X^{BV}).$$

We will later see that this adjoint map is often an isomorphism. Therefore, Lannes' T-functor provides a purely algebraic mechanism for understanding the cohomology of mapping spaces.

For now, we will be content to establish some of the basic formal properties of the functor  $T_V$ . We begin with the following result, which is a reformulation of the work of the previous lectures:

**Proposition 6.** Let V be a finite dimensional vector space over  $\mathbf{F}_2$ . Then the functor  $T_V$  is exact.

*Proof.* Choose an exact sequence

$$0 \to M' \to M \to M'' \to 0$$
.

We wish to show that the induced sequence

$$0 \to T_V M' \to T_V M \to T_V M'' \to 0$$

is also exact. It will suffice to show that this sequence is exact in each degree. For this, we need only show that for each  $n \ge 0$ , the sequence

$$0 \to \operatorname{Hom}_{\mathcal{A}}(T_V M'', J(n)) \to \operatorname{Hom}_{\mathcal{A}}(T_V M, J(n)) \to \operatorname{Hom}_{\mathcal{A}}(T_V M', J(n)) \to 0.$$

Invoking the definition of  $T_V$ , we can rewrite this sequence as

$$0 \to \operatorname{Hom}_{\mathcal{A}}(M'', J(n) \otimes \operatorname{H}^*(BV)) \to \operatorname{Hom}_{\mathcal{A}}(M, J(n) \otimes \operatorname{H}^*(BV)) \to \operatorname{Hom}_{\mathcal{A}}(M', J(n) \otimes \operatorname{H}^*(BV)) \to 0.$$

The exactness now follows from the injectivity of the object  $J(n) \otimes H^*(BV)$ .

We now discuss the relationship between the functor  $T_V$  and suspension. Recall that the suspension functor  $\Sigma$  can be identified with the functor  $M \mapsto M \otimes \Sigma(\mathbf{F}_2)$ . Consequently, the functors  $\Sigma$  and  $M \mapsto M \otimes H^*(V)$  commute with one another: composing them in either order yields the functor

$$M \mapsto M \otimes \Sigma \operatorname{H}^*(V)$$
.

Passing to left adjoints, we get a canonical isomorphism of functors

$$T_V\Omega \simeq \Omega T_V$$
.

This isomorphism induces a natural transformation

$$T_{V}\Sigma \rightarrow \Sigma\Omega T_{V}\Sigma$$

$$\simeq \Sigma T_{V}\Omega\Sigma$$

$$\rightarrow \Sigma T_{V}$$

We wish to prove that this map is also an isomorphism of functors. For this, we first construct a *right* adjoint to the functor  $\Sigma$ . The functor  $\Sigma$  commutes with all limits and colimits, and therefore admits a right adjoint by the adjoint functor theorem. However, we can describe this right adjoint more concretely.

**Proposition 7.** Let M be an unstable module over the Steenrod algebra, and let M' denote the subspace of M spanned by those homogeneous elements x such that  $\operatorname{Sq}^{\operatorname{deg} x} x = 0$ . Then:

- (1) M' is a A-submodule of M.
- (2) M' has the form  $\Sigma \widetilde{\Sigma} M$ , for some A-module  $\widetilde{\Sigma} M$ .
- (3) For every unstable A-module N, the inclusion  $\Sigma \widetilde{\Sigma} M \subseteq M$  induces an isomorphism

$$\operatorname{Hom}_{\mathcal{A}}(N,\widetilde{\Sigma}M) \to \operatorname{Hom}_{\mathcal{A}}(\Sigma N, M).$$

(4) The functor  $M \mapsto \widetilde{\Sigma}M$  is right adjoint to the suspension functor.

*Proof.* To prove (1), we observe that M' can be identified (as a vector space) with the kernel of the canonical map  $f: \Phi M \to M$ . Since f is a map of A-modules, we deduce that M' is stable under the action of the Steenrod algebra on  $\Phi M$ . In other words, M' is a A-submodule of M, where A acts on M via the composition

$$\mathcal{A} \xrightarrow{V} \mathcal{A} \to \operatorname{End}(M)$$

where V is the Verschiebung map  $\operatorname{Sq}^n \mapsto \operatorname{Sq}^{\frac{n}{2}}$ . Since V is surjective, we conclude that M' is also stable under the usual action of  $\mathcal{A}$  on M.

To prove (2), we observe that the map  $\Phi M' \to M'$ , vanishes, so that we obtain an isomorphism  $M' \to \Sigma \Omega M'$ . We can now take  $\widetilde{\Sigma} M = \Omega M'$ .

To prove (3), we observe that  $\Sigma$  is fully faithful, so we have an isomorphism

$$\operatorname{Hom}_{\mathcal{A}}(N, \widetilde{\Sigma}M) \simeq \operatorname{Hom}_{\mathcal{A}}(\Sigma N, \Sigma \widetilde{\Sigma}M) = \operatorname{Hom}_{\mathcal{A}}(\Sigma N, M').$$

To complete the proof, it will suffice to show that  $\operatorname{Hom}_{\mathcal{A}}(\Sigma N, M') = \operatorname{Hom}_{\mathcal{A}}(\Sigma N, M)$ : in other words, that every map from  $\Sigma N$  into M factors through M'. This follows from the observation that for  $x \in \Sigma N$ , we have  $\operatorname{Sq}^{\deg x}(x) = 0$ .

Assertion (4) is an immediate consequence of (3).

**Proposition 8.** Let V be a finite dimensional  $\mathbf{F}_2$ -vector space. The natural transformation

$$T_V \Sigma \to \Sigma T_V$$

is an isomorphism of functors.

*Proof.* It will suffice to prove that the induced map between right adjoints is an isomorphism of functors. In other words, we must show that for every unstable A-module M, the induced map

$$H^*(BV) \otimes \widetilde{\Sigma}M \to \widetilde{\Sigma}(H^*(BV) \otimes M)$$

is an isomorphism. Unwinding the definitions, we must show that the map

$$i: H^*(BV) \otimes M' \to (H^*(BV) \otimes M)'$$

is an isomorphism, where M' denotes the submodule of M defined in Proposition 7 and  $(H^*(BV) \otimes M)'$  is defined similarly. The injectivity of i is obvious, since both sides can be identified with submodules of  $H^*(BV) \otimes M$ .

To prove the surjectivity, let us define by  $f_M$  the Frobenius map  $x \mapsto \operatorname{Sq}^{\operatorname{deg} x}(x)$ . It is easy to see that for every pair of unstable A-modules M and N, we have

$$f_{M\otimes N}=f_M\otimes f_N,$$

so that

$$\ker(f_{M\otimes N}) = (\ker(f_M)\otimes N) + (M\otimes\ker(f_N)).$$

In particular, if N is reduced, then  $\ker f_N=0$ , so

$$\ker(f_{M\otimes n}) = \ker(f_M) \otimes N.$$

We now conclude the proof by observing that  $H^*(BV) \simeq \mathbf{F}_2[t_1, \dots, t_k]$  is reduced.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Properties of T (Lecture 19)

Let V be a finite dimensional vector space over  $\mathbf{F}_2$ . In this lecture, we will continue to establish some of the basic properties of Lannes' T-functor  $T_V$ . More precisely, we will show that  $T_V$  commutes with the functor  $\Phi$  and with the formation of tensor products.

To begin, we observe that for every unstable A-module M comes equipped with a canonical map

$$M \to (T_V M) \otimes H^*(BV).$$

This induces a map

$$\Phi M \to \Phi(T_V M \otimes H^*(BV)) \simeq (\Phi T_V M) \otimes (\Phi H^*(BV)).$$

Composing with the Frobenius map  $\Phi H^*(BV) \to H^*(BV)$ , we obtain a map

$$\Phi M \to (\Phi T_V M) \otimes H^* M$$
,

which is adjoint to a map

$$h_M: T_V \Phi M \to \Phi T_V M$$
.

**Proposition 1.** For every unstable A-module M, the map  $h_M: T_V\Phi M \to \Phi T_VM$  is an isomorphism.

*Proof.* Choose a resolution

$$\bigoplus_{\beta} F(n_{\beta}) \to \bigoplus_{\alpha} F(n_{\alpha}) \to M \to 0.$$

Since the functors  $T_V$  and  $\Phi$  both preserve cokernels and direct sums, we conclude that  $h_M$  is an isomorphism provided that the maps  $h_{F(n)}$  are isomorphisms, for each  $n \geq 0$ . We now work by induction on n, the case n = 0 being obvious.

Recall that we have an exact sequence

$$0 \to \Phi F(n) \to F(n) \to \Sigma \Omega F(n) \to 0.$$

Applying  $T_V$ , we obtain another exact sequence

$$0 \to T_V \Phi F(n) \to T_V F(n) \to T_V \Sigma \Omega F(n) \to 0.$$

The functor  $T_V$  commutes with  $\Sigma$  and  $\Omega$ , so we can identify  $T_V \Phi F(n)$  with the kernel K of the unit map  $T_V F(n) \to \Sigma \Omega T_V F(n)$ . On the other hand, we have an exact sequence

$$\Phi T_V F(n) \to T_V F(n) \to \Sigma \Omega T_V F(n) \to 0$$
,

which determines a surjective map  $g: \Phi T_V F(n) \to K$ . The module  $T_V F(n)$  is a direct sum of free unstable  $\mathcal{A}$ -modules, and therefore reduced. It follows that g is also injective, and determines an isomorphism  $\Phi T_V F(n) \simeq T_V \Phi F(n)$ . We now observe that this map is an inverse to  $h_{F(n)}$ .

We now discuss the behavior of  $T_V$  with tensor products. Let M and N be unstable A-modules. We have unit maps

$$M \to T_V M \otimes H^*(BV)$$

$$N \to T_V N \otimes \mathrm{H}^*(BV)$$
.

Tensoring these together and composing with the multiplication on  $H^*(BV)$ , we get a map

$$M \otimes N \to T_V M \otimes T_V N \otimes H^*(BV)$$

which has an adjoint

$$\mu_{M,N}: T_V(M\otimes N) \to T_VM\otimes T_VN.$$

Our goal is to prove the following:

**Theorem 2.** For every pair of unstable A-modules M and N, the map

$$\mu_{M,N}: T_V(M\otimes N) \to T_VM\otimes T_VN$$

is an isomorphism.

The proof proceeds in a series of steps. We begin with the following observation:

**Remark 3.** Let  $V = V_0 \oplus V_1$ . Then we have a canonical isomorphism

$$H^*(BV) \simeq H^*(BV_0) \otimes H^*(BV_1).$$

It follows that the functor  $M \mapsto M \otimes H^*(BV)$  can be written as a composition of functors, given by tensor product with  $H^*(BV_0)$  and  $H^*(BV_1)$  respectively. Passing to left adjoints, we get a canonical isomorphism

$$T_V \simeq T_{V_0} \circ T_{V_1}$$
.

The isomorphism of Remark 3 is compatible with the construction of the transformations  $\mu_{M,N}$ . Consequently, to prove Theorem 2, it will suffice to treat the case where  $V \simeq \mathbf{F}_2$  is one-dimensional.

**Notation 4.** If  $V = \mathbf{F}_2$ , then we denote Lannes' T-functor simply by T.

The following is a special case of Theorem 2:

**Lemma 5.** For every unstable A-module N, the canonical map

$$T(F(1) \otimes N) \to T(F(1)) \otimes T(N)$$

is an isomorphism.

Let us assume Lemma 5 for the moment, and use it to complete the proof of Theorem 2 in general.

*Proof of Theorem 2.* We wish to show that a canonical map

$$T(M \otimes N) \to T(M) \otimes T(N)$$

is an isomorphism. As functors of M, both sides are compatible with the formation of cokernels and direct sums. We may therefore argue as in the proof of Proposition 1 to reduce to the case where  $M \simeq F(m)$  is a free module. Recall that F(m) is canonically isomorphic to  $\Sigma_m$ -invariants in the tensor product  $F(1)^{\otimes m}$ . Since the functor T is exact, it commutes with the formation of fixed points. It will therefore suffice to prove the result in the case  $M = F(1)^{\otimes m}$ . We have a commutative diagram

$$T(F(1)^{\otimes m} \otimes N) \xrightarrow{\mu_{M,N}} T(F(1)^{\otimes m}) \otimes T(N)$$

$$\downarrow^{\mu'}$$

$$T(F(1))^{\otimes m} \otimes T(N).$$

It follows from repeated application of Lemma 5 that the maps  $\mu'$  and  $\mu''$  are isomorphisms, so that  $\mu_{M,N}$  is an isomorphism as well.

Proof of Lemma 5. We wish to show that the canonical map

$$\mu_{F(1),N}: T(F(1)\otimes N) \to T(F(1))\otimes T(N)$$

is an isomorphism. As functors of N, both sides preserve direct sums and cokernels. We may therefore assume that  $N \simeq F(n)$  is a free unstable  $\mathcal{A}$ -module. We proceed by induction on n. We need to prove three things:

(a) The map  $\mu_{F(1),N}$  is an isomorphism in every positive degree k. To prove this, we observe that N is reduced, so we have a map of exact sequences

$$0 \to T(F(1) \otimes \Phi N) \longrightarrow T(F(1) \otimes N) \longrightarrow T(F(1) \otimes \Sigma F(n-1)) \longrightarrow 0$$

$$\downarrow^{\mu_{F(1),\Phi N}} \qquad \qquad \downarrow^{\mu_{F(1),N}} \qquad \qquad \downarrow^{\mu_{F(1),\Sigma F(n-1)}}$$

$$0 \to T(F(1)) \otimes T(\Phi(N)) \longrightarrow T(F(1)) \otimes T(N) \longrightarrow T(F(1)) \otimes T(\Sigma F(n-1)) \longrightarrow 0.$$

Since T commutes with suspension, the inductive hypothesis guarantees that  $\mu_{F(1),\Sigma F(n-1)}$  is an isomorphism. Consequently, to show that  $\mu_{F(1),N}$  is an isomorphism in degree k, it will suffice to show that  $\mu_{F(1),\Phi N}$  is an isomorphism in degree k. We have a second map of exact sequences

$$0 \to T(\Phi F(1) \otimes \Phi N) \longrightarrow T(F(1) \otimes \Phi N) \longrightarrow T(\Sigma F(0) \otimes \Phi N) \longrightarrow 0$$

$$\downarrow^{\mu_{\Phi F(1), \Phi N}} \qquad \qquad \downarrow^{\mu_{F(1), \Phi N}} \qquad \qquad \downarrow^{\mu_{\Sigma F(0), \Phi N}}$$

$$0 \to T(\Phi F(1)) \otimes T(\Phi(N)) \longrightarrow T(F(1)) \otimes T(\Phi N) \longrightarrow T(\Sigma F(0)) \otimes T(\Phi N) \longrightarrow 0.$$

Since T commutes with  $\Sigma$ , the map  $\mu_{\Sigma F(0),\Phi F(n)}$  is an isomorphism. Consequently, to prove that  $\mu_{F(1),N}$  is an isomorphism in degree k, it will suffice to show that  $\mu_{\Phi F(1),\Phi N}$  is an isomorphism in degree k. Since T commutes with  $\Phi$ , this is equivalent to the assertion that  $\mu_{F(1),N}$  is an isomorphism in degree  $\frac{k}{2}$ , which follows from the inductive hypothesis.

(b) The map  $\mu_{F(1),N}$  is surjective in degree 0. For each  $p \geq 0$ , the vector space  $(TF(p))^0$  is dual to

$$\operatorname{Hom}_{\mathcal{A}}(TF(p), J(0)) \simeq \operatorname{Hom}_{\mathcal{A}}(F(p), \operatorname{H}^*(B\mathbf{F}_2)) \simeq \operatorname{H}^p(B\mathbf{F}_2).$$

In particular, it is a one-dimensional vector space over  $\mathbf{F}_2$ , generated by  $t^p \in \mathrm{H}^*(B\mathbf{F}_2) \simeq \mathbf{F}_2[t]$ . It follows that  $T(F(1)) \otimes T(F(n))$  is also one-dimensional in degree 0. Moreover, in degree zero the map  $\mu_{F(1),N}$  is dual to the composition

$$\mathbf{F}_2 \simeq \operatorname{Hom}_{\mathcal{A}}(T(F(1)) \otimes T(N), J(0)) \to \operatorname{Hom}_{\mathcal{A}}(T(F(1) \otimes N), J(0)) \simeq \operatorname{Hom}_{\mathcal{A}}(F(1) \otimes N, H^*(B\mathbf{F}_2)).$$

We wish to show that this map is injective. For this, it suffices to observe that the image of the nontrivial element of  $\mathbf{F}_2$  is a homomorphism  $F(1) \otimes N \to H^*(B\mathbf{F}_2)$  given by multiplying the nontrivial maps  $F(1) \to H^*(B\mathbf{F}_2)$  and  $N \to H^*(B\mathbf{F}_2)$ , and that this map is nontrivial in degree n + 1.

- (c) The map  $\mu_{F(1),N}$  is injective in degree zero. Given (b) and the observation that  $T(F(1)) \otimes T(N)$  is one-dimensional in degree 0, it will suffice to show that the dimension of  $T(F(1) \otimes N)^0$  is at most 1. We will prove the following more general assertion:
  - $(*_p)$  The dimension of  $T(\Phi^p F(1) \otimes F(n))^0$  is at most 1.

For p large, we will invoke the following lemma:

**Lemma 6.** Fix an integer n. Then for  $p \gg 0$ , the tensor product  $\Phi^p F(1) \otimes F(n)$  is generated by a single element.

Assuming Lemma 6, we deduce that for  $p \gg 0$  we have a surjection  $F(m) \to \Phi^p F(1) \otimes F(n)$ . This induces a surjection

$$F(m) \oplus F(m-1) \oplus \ldots \oplus F(0) \simeq TF(m) \to T(\Phi^p F(1) \otimes F(n)).$$

Since the left hand side has dimension 1 in degree 0, assertion  $(*_p)$  follows.

To prove  $(*_p)$  in general, we use descending induction on p. We have an exact sequence

$$0 \to \Phi^{p+1}F(1) \otimes F(n) \to \Phi^pF(1) \otimes F(n) \to \Sigma^{2^p}F(n) \to 0$$

Since T is an exact functor which commutes with  $\Sigma$ , this reduces to an isomorphism  $T(\Phi^{p+1}F(1)\otimes F(n))^0\simeq T(\Phi^pF(1)\otimes F(n))^0$ , so that  $(*_{p+1})$  implies  $(*_p)$  as desired.

We will give the proof of Lemma 6 in the next lecture.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The T-functor and Unstable Algebras (Lecture 20)

Our first order of business is to prove the following assertion, which was stated without proof in the previous lecture:

**Lemma 1.** Fix an integer n. Then for  $p \gg 0$ , the tensor product  $\Phi^p F(1) \otimes F(n)$  is generated by a single element

*Proof.* We may identify F(n) with the subspace of  $\mathbf{F}_2[t_1,\ldots,t_n]$  spanned by those polynomials which are symmetric and additive in each variable. The module  $\Phi^pF(1)$  can similarly be identified with the subspace of  $\mathbf{F}_2[t]$  spanned by those polynomials of the form  $\{t^{2^k}\}_{k\geq p}$ . We wish to show that the tensor product  $\Phi^pF(1)\otimes F(n)$  is generated by the element  $t^{2^p}\otimes (t_1\ldots t_n)$ . This element determines a map

$$F(n+2^p) \to \Phi^p F(1) \otimes F(n);$$

it will therefore suffice to show that  $\beta$  is surjective. The right hand side has a basis consisting of expressions of the form

$$t^{2^{p+q}}\otimes\sigma(t_1^{2^{b_1}}\ldots t_n^{2^{b_n}}),$$

where  $\sigma$  denotes the operation of symmetrization. We now observe that this basis element is the image of

$$\sigma(t_1^{2^{b_1}}\dots t_n^{2^{b_n}}t_{n+1}^{2^q}t_{n+2}^{2^q}\dots t_{n+2^p}^{2^q})\in F(n+2^p)$$

provided that  $2^p > n$ .

In the last lecture, we saw that Lemma 1 implies that Lannes' T-functor  $T_V$  commutes with tensor products. It follows that M is an unstable A-module equipped with a multiplication map  $M \otimes M \to M$ , then  $T_V(M)$  inherits a multiplication

$$T_V M \otimes T_V M \simeq T_V (M \otimes M) \to T_V M.$$

**Proposition 2.** Suppose that M is an unstable A-algebra. Then the multiplication defined above endows  $T_VM$  with the structure of an unstable A-algebra.

*Proof.* Since M is commutative, associative, and unital, we deduce immediately that  $T_V M$  has the same properties. The only nontrivial point is to verify that  $\operatorname{Sq}^{\deg(x)}(x) = x^2$  for every homogeneous element  $x \in T_V M$ . Before proving this, we indulge in a slight digression.

Let M be an unstable A-module. There is a canonical map  $f'_M: \Phi M \to \operatorname{Sym}^2 M$ , given by the formula

$$\Phi(x) \mapsto x^2$$

By definition, an unstable A-algebra is an unstable A-module M equipped with a commutative, associative, and unital multiplication  $m: M \otimes M \to M$  such that the diagram

commutes. Here  $f_M: \Phi M \to M$  is the map described by the formula  $x \mapsto \operatorname{Sq}^{\operatorname{deg}(x)} x$ . Applying  $T_V$  to the commutative diagram above, we get a new commutative diagram

Since the functor  $T_V$  preserves colimits and tensor products, we have a canonical isomorphism  $\alpha$ :  $T_V \operatorname{Sym}^2 M \simeq \operatorname{Sym}^2 T_V M$ ; similarly we have an identification  $\beta: T_V \Phi M \simeq \Phi T_V M$ . Under the isomorphism  $\alpha$ , the map  $T_V M$  corresponds to the multiplication map  $\operatorname{Sym}^2 T_V M \to T_V M$  given by the ring structure on  $T_V M$ . To prove that  $T_V M$  is an unstable A-algebra, it will suffice to show that the maps  $T_V f_M$  and  $T_V f_M'$  can be identified, by means of  $\alpha$  and  $\beta$ , with  $f_{T_V M}$  and  $f'_{T_V M}$ , respectively. We will give a proof for  $f'_{T_V M}$ , leaving the first case as an exercise to the reader.

We wish to show that the diagram

$$T_V \Phi M \xrightarrow{T_V f'_M} T_V \operatorname{Sym}^2 M$$

$$\downarrow^{\alpha} \qquad \qquad \downarrow^{\beta}$$

$$\Phi T_V M \xrightarrow{f'_{T_V} M} \operatorname{Sym}^2 T_V M$$

is commutative. Using the definition of  $T_V$ , we are reduced to proving that the adjoint diagram

$$\Phi M \xrightarrow{f'_M} \operatorname{Sym}^2 M \\
\downarrow \qquad \qquad \downarrow \\
(\Phi T_V M) \otimes \operatorname{H}^*(BV) \longrightarrow (\operatorname{Sym}^2 T_V M) \otimes \operatorname{H}^*(BV).$$

To prove this, we consider the larger diagram

$$\Phi M \xrightarrow{f'_{M}} \operatorname{Sym}^{2} M \\
\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \\
\Phi(T_{V}M \otimes \operatorname{H}^{*}(BV)) \xrightarrow{} \operatorname{Sym}^{2}(T_{V}M \otimes \operatorname{H}^{*}(BV)) \\
\downarrow \sim \qquad \qquad \downarrow \qquad \qquad \downarrow \\
\Phi(T_{V}M) \otimes \Phi \operatorname{H}^{*}(BV) \xrightarrow{} \operatorname{Sym}^{2}(T_{V}M) \otimes \operatorname{Sym}^{2} \operatorname{H}^{*}(BV) \\
\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \\
\Phi(T_{V}M) \otimes \operatorname{H}^{*}(BV) \xrightarrow{} \operatorname{Sym}^{2}(T_{V}M) \otimes \operatorname{H}^{*}(BV).$$

The top square obviously commutes. The middle square commutes because the construction of the map  $f'_M$  is compatible with the formation of tensor products in M. The lower square commutes because  $H^*(BV)$  is an unstable A-algebra. It follows that the outer square commutes as well, as desired.

Let M be an unstable A-algebra, so that  $T_V M$  inherits the structure of an unstable A-algebra. We now characterize  $T_V M$  by a universal property.

**Proposition 3.** Let  $\mathcal{K}$  denote the category of unstable  $\mathcal{A}$ -algebras. For every pair of objects  $M, N \in \mathcal{K}$ , the image of the inclusion

$$\operatorname{Hom}_{\mathcal{K}}(T_VM,N) \subseteq \operatorname{Hom}_{\mathcal{A}}(T_VM,N) \simeq \operatorname{Hom}_{\mathcal{A}}(M,N \otimes \operatorname{H}^*(BV))$$

consists of those maps  $M \to N \otimes H^*(BV)$  which are compatible with the ring structure.

*Proof.* We will show that a map  $u: T_VM \to N$  is compatible with multiplication if and only if the adjoint map  $v:M\to N\otimes \operatorname{H}^*(BV)$  is compatible with multiplication; an analogous (but easier) argument shows that u is unital if and only if v is unital.

By definition, u is compatible with multiplication if and only if the diagram

is commutative. This is equivalent to the commutativity of the adjoint diagram

$$T_{V}M \otimes T_{V}M \otimes \operatorname{H}^{*}(BV) \xrightarrow{w_{1}} N \otimes N \otimes \operatorname{H}^{*}(BV)$$

$$\downarrow w_{0} \\ M \otimes M \\ \downarrow w_{2} \\ M \xrightarrow{v} N \otimes \operatorname{H}^{*}(BV)$$

To prove that this is equivalent to the assumption that v is compatible with multiplication, it will suffice to show that the composition  $w_2 \circ w_1 \circ w_0$  coincides with the composition

$$M \otimes M \stackrel{v \otimes v}{\to} (N \otimes H^*(BV)) \otimes (N \otimes H^*(BV)) \to N \otimes H^*(BV).$$

This follows from the commutativity of the diagram

Corollary 4. Regarded as a functor from K to itself, Lannes' T-functor is left adjoint to the functor  $N \mapsto N \otimes \mathrm{H}^*(BV)$ .

**Corollary 5.** Let  $F_{Alg}(n)$  denote the free unstable A-algebra on one generator in degree n. Then we have a canonical isomorphism of unstable A-algebras

$$TF_{Alg}(n) \simeq F_{Alg}(n) \otimes \ldots \otimes F_{Alg}(0).$$

*Proof.* Let M be an arbitrary unstable A-algebra. Then

$$\begin{array}{lll} \operatorname{Hom}_{\mathfrak{K}}(TF_{\operatorname{Alg}}(n),M) & \simeq & \operatorname{Hom}_{\mathfrak{K}}(F_{\operatorname{Alg}}(n),M\otimes \mathbf{F}_{2}[t]) \\ & \simeq & (M\otimes \mathbf{F}_{2}[t])^{n} \\ & \simeq & M^{n}\times M^{n-1}\times \ldots \times M^{0} \\ & \simeq & \operatorname{Hom}_{\mathfrak{K}}(F_{\operatorname{Alg}}(n),M)\times \ldots \times \operatorname{Hom}_{\mathfrak{K}}(F_{\operatorname{Alg}}(0),M) \\ & \simeq & \operatorname{Hom}_{\mathfrak{K}}(F_{\operatorname{Alg}}(n)\otimes \ldots \otimes F_{\operatorname{Alg}}(0),M). \end{array}$$

Recall that  $F_{Alg}(n)$  can be identified with the cohomology of the Eilenberg-MacLane space  $K(\mathbf{F}_2, n)$ . Similarly, the Kunneth theorem allows us to identify the tensor product  $F_{Alg}(n) \otimes \ldots \otimes F_{Alg}(0)$  with the cohomology of the product

$$K(\mathbf{F}_2, n) \times K(\mathbf{F}_2, n-1) \times \ldots \times K(\mathbf{F}_2, 0) \simeq K(\mathbf{F}_2, n)^{B\mathbf{F}_2}$$
.

The isomorphism of Corollary 5 is induced by the canonical map

$$\eta_X: T_V \operatorname{H}^*(X) \to \operatorname{H}^*(X^{BV})$$

in the special case where  $X = K(\mathbf{F}_2, n)$  and  $V = \mathbf{F}_2$ . We may therefore restate Corollary 5 in the following more conceptual form: if X is an Eilenberg-MacLane space  $K(\mathbf{F}_2, n)$  and  $V = \mathbf{F}_2$ , then the map  $\eta_X$  is an isomorphism. Our next goal in this course is to prove this statement for a much larger class of spaces.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Free $E_{\infty}$ -Algebras (Lecture 21)

In this lecture we will review the theory of  $E_{\infty}$ -algebras over the field  $\mathbf{F}_2$  of two elements.

Roughly speaking, an  $E_{\infty}$ -algebra over  $\mathbf{F}_2$  is a chain complex V of  $\mathbf{F}_2$ -vector spaces, equipped with a multiplication

$$m: V \otimes V \to V$$

which is commutative, associative, and unital, up to coherent homotopy. We summarize some of the basic properties of this notion:

- (1) For every topological space X, the cochain complex  $C^*(X)$  has the structure of an  $E_{\infty}$ -algebra over  $\mathbf{F}_2$ .
- (2) If V is an  $E_{\infty}$ -algebra over  $\mathbf{F}_2$ , then the product map m descends to a good symmetric multiplication  $D_2(V) \to V$ , in the sense of our previous lectures. Consequently, the cohomology  $H^*(V)$  is endowed with the structure of an unstable  $\mathcal{A}^{\text{Big}}$ -module, where  $\mathcal{A}^{\text{Big}}$  denotes the big Steenrod algebra.
- (3) The forgetful functor

$$\{E_{\infty} - \text{algebras over } \mathbf{F}_2\} \rightarrow \{\text{chain complexes over } \mathbf{F}_2\}$$

admits a left adjoint  $\mathcal{F}$ . The functor  $\mathcal{F}$  carries a chain complex V to the symmetric algebra

$$\mathfrak{F}(V) \oplus_{n \geq 0} V_{h\Sigma_n}^{\otimes n} = \oplus_{n \geq 0} D_n(V),$$

where  $D_n$  denotes the *n*th extended power functor.

For every integer n, we let  $\mathcal{F}(n) = \mathcal{F}(\mathbf{F}_2[-n])$  denote the free  $E_{\infty}$ -algebra over  $\mathbf{F}_2$  generated by a single class of cohomological degree n. By construction, we have a canonical map of complexes

$$\mathbf{F}_2[-n] \to \mathfrak{F}(n),$$

which determines an element  $\eta \in H^n \mathcal{F}(n)$ . Since  $H^* \mathcal{F}(n)$  has the structure of an unstable  $\mathcal{A}^{\text{Big}}$ -algebra, the element  $\eta$  determines a map

$$\theta_n: F_{\mathrm{Alg}}^{\mathrm{Big}}(n) \to \mathrm{H}^*\,\mathfrak{F}(n).$$

Here  $F_{\text{Alg}}^{\text{Big}}(n)$  denotes the free unstable  $\mathcal{A}^{\text{Big}}$ -module on one generator  $\mu_n$  in degree n, whose structure was determined in Lecture 11.

Our goal in this lecture is to prove the following result:

**Theorem 1.** For every integer n, the map  $\theta_n$  is an isomorphism.

To prove Theorem 1, we will show by two separate arguments that  $\theta_n$  is injective and that  $\theta_n$  is surjective. We begin with the injectivity. Recall that  $F_{\text{Alg}}^{\text{Big}}(n)$  has a basis consisting of expressions

$$\{\operatorname{Sq}^{I_1}(\mu_n)\operatorname{Sq}^{I_2}(\mu_n)\ldots\operatorname{Sq}^{I_k}(\mu_n)\},$$

where  $I_1, \ldots, I_k$  range over distinct admissible sequences of excess  $\leq n$ . This module has a grading by cohomological degree, but also another grading by rank, where we declare

$$rk(1) = 0$$

$$rk(\mu_n) = 1$$

$$rk(xy) = rk(x) + rk(y)$$

$$rk(Sq^i(x)) = 2 rk(x).$$

Similarly, the cohomology  $H^* \mathcal{F}(n)$  can be written as a direct sum

$$\bigoplus_{k>0} \mathrm{H}^* D_k(\mathbf{F}_2[-n])$$

is equipped with a grading by rank, where elements  $H^*D_k(\mathbf{F}_2[-n])$  have rank k. The multiplication on  $\mathfrak{F}(n)$  carries  $D_k(\mathbf{F}_2[-n]) \otimes D_{k'}(\mathbf{F}_2[-n])$  into  $D_{k+k'}(\mathbf{F}_2[-n])$ , and Steenrod operations  $\mathrm{Sq}^i$  carry  $H^*D_k(\mathbf{F}_2[-n])$  into  $H^{*+i}D_{2k}(\mathbf{F}_2[-n])$ . It follows that the map  $\theta_n$  is compatible with the grading by rank.

Recall that we defined shift isomorphisms

$$S: F_{\mathrm{Alg}}^{\mathrm{Big}}(n) \to F_{\mathrm{Alg}}^{\mathrm{Big}}(n+1).$$

The map S is an isomorphism of commutative rings (not compatible with the action of  $\mathcal{A}^{\text{Big}}$ ), which is uniquely determined by the following requirements:

$$S(\mu_n) = \mu_{n+1}$$

$$S(\operatorname{Sq}^{i}(x)) = \operatorname{Sq}^{i+\operatorname{rk}(x)} S(x).$$

The shift maps S do not respect degree, but instead satisfy the formula

$$\deg(Sx) = \deg(x) + \operatorname{rk}(x)$$

whenever x is homogeneous in both degree and rank.

We have similar isomorphisms  $S': H^* \mathcal{F}(n) \to H^* \mathcal{F}(n+1)$ , obtained by taking the direct sum of the canonical isomorphisms

$$H^* D_k(\mathbf{F}_2[-n]) = H^{*-nk}(B\Sigma_k, \mathbf{F}_2) \simeq H^{*+k} D_k(\mathbf{F}_2[-n-1]).$$

For every integer n, we have a commutative diagram

$$\begin{split} F_{\mathrm{Alg}}^{\mathrm{Big}}(n) & \stackrel{S}{\longrightarrow} F_{\mathrm{Alg}}^{\mathrm{Big}}(n+1) \\ \downarrow^{\theta_{n}} & \downarrow^{\theta_{n+1}} \\ \mathrm{H}^{*}\,\mathfrak{F}(n) & \stackrel{S'}{\longrightarrow} \mathrm{H}^{*}\,\mathfrak{F}(n+1), \end{split}$$

We are now ready to prove injectivity of  $\theta_n$ . Suppose that  $\theta_n$  fails to be injective. Choose some nonzero element

$$x = \sum_{\alpha} \operatorname{Sq}^{I_1^{\alpha}}(\mu_n) \dots \operatorname{Sq}^{I_{k_{\alpha}}^{\alpha}}(\mu_n)$$

in the kernel of  $\theta^n$ , where the sequences  $I_i^{\alpha}$  are admissible, distinct (for fixed  $\alpha$ ), and have excess  $\leq n$ . Then for every integer  $p \geq 0$ , the element

$$S^{p}(x) = \sum_{\alpha} \operatorname{Sq}^{J_{1}^{\alpha}}(\mu_{n+p}) \dots \operatorname{Sq}^{J_{k_{\alpha}}^{\alpha}}(\mu_{n+p})$$

lies in the kernel of  $\theta_{n+p}$ . Choosing  $p \gg 0$  and replacing x by  $S^p(x)$ , we may assume that each of the sequences  $I_i^{\alpha}$  is positive. It follows that the image of x in the free algebra  $F_{\text{Alg}}(n)$  is nonzero. But the Cartan-Serre theorem identifies  $F_{\text{Alg}}(n)$  with the cohomology ring

$$H^*K(\mathbf{F}_2, n).$$

which is the cohomology of the  $E_{\infty}$ -algebra  $C^*K(\mathbf{F}_2, n)$ . The universal property of  $\mathfrak{F}(n)$  gives a map of  $E_{\infty}$ -algebra  $\mathfrak{F}(n) \to C^*K(\mathbf{F}_2, n)$ , which fits into a commutative diagram

It follows that  $\theta_n(x) \neq 0$ , a contradiction.

We now prove the surjectivity of  $\theta_n$ . The proof is based on the following elementary lemma:

**Lemma 2.** Let  $H \subseteq G$  be finite groups, and suppose that |G/H| is odd. Then the induced map on homology

$$p: H_*(BH) \to H_*(BG)$$

is an isomorphism.

*Proof.* We can realize the map of classifying spaces  $BH \to BG$  as a covering space map, whose fiber has cardinality |G/H|. We therefore have a transfer map

$$t: \mathrm{H}_*(BG) \to \mathrm{H}_*(BH).$$

The composition  $p \circ t$  is given by multiplication by |G/H|, and is therefore an isomorphism. Since  $p \circ t$  is surjective, the map p must also be surjective.

We now return to the proof of Theorem 1. We will show, by induction on  $k \geq 0$ , that the map

$$\theta_n: F_{\mathrm{Alg}}^{\mathrm{Big}}(n)_k \to \mathrm{H}^*\,\mathfrak{F}(n)_k = \mathrm{H}^*\,D_k(\mathbf{F}_2[-n])$$

is surjective; here the subscripts indicate that we consider only the component consisting of elements of rank k. If k=0, this is clear: the only element of rank 0 on the right hand side is the unit 1, and we have  $\theta_n(1)=1$ . Similarly, the only element of rank 1 on the right hand side is the generator  $\eta \in H^n \mathcal{F}(n)$ , and we have  $\theta_n(\mu_n)=\eta$  by construction. We may therefore assume that k>1. There are two cases to consider:

• Suppose that k is not a power of 2. Then we can write k = k' + k'', where  $\binom{k}{k'} = \frac{k!}{k'!k''!}$  is odd. Multiplication yields a commutative diagram

$$F_{\mathrm{Alg}}^{\mathrm{Big}}(n)_{k'} \otimes F_{\mathrm{Alg}}^{\mathrm{Big}}(n)_{k''} \longrightarrow F_{\mathrm{Alg}}^{\mathrm{Big}}(n)_{k}$$

$$\downarrow^{\theta_{n} \otimes \theta_{n}} \qquad \qquad \downarrow^{\theta_{n}}$$

$$\mathrm{H}^{*} D_{k'}(\mathbf{F}_{2}[-n]) \otimes \mathrm{H}^{*} D_{k''}(\mathbf{F}_{2}[-n]) \longrightarrow \mathrm{H}^{*} D_{k}(\mathbf{F}_{2}[-n]).$$

The inductive hypothesis guarantees that the left vertical map is surjective. To prove that the right vertical map is surjective, it will suffice to show that the lower horizontal map is surjective. Up to a shift, this agrees with the pushforward map

$$H_*(B(\Sigma_{k'} \times \Sigma_{k''})) \to H_*(B\Sigma_k),$$

which is surjective by Lemma 2 since

$$|\Sigma_k/(\Sigma_{k'} \times \Sigma_{k''})| = \frac{k!}{k'!k''!}$$

is odd by assumption.

• Suppose that k is a power of 2, and let  $k' = \frac{k}{2}$ . We have a map of extended powers

$$D_2D_{k'}\mathbf{F}_2[-n] \to D_k\mathbf{F}_2[-n].$$

Up to a shift, the induced map on cohomology can be identified with the map

$$p: \mathrm{H}_*(BG) \to \mathrm{H}_*(B\Sigma_k),$$

where  $G \subset \Sigma_k$  is the wreath product  $\Sigma_{k'}^2 \rtimes \Sigma_2$ . We observe that  $|\Sigma_k/G|$  is odd, so the map p is surjective by Lemma 2.

Recall that if V is a complex of  $\mathbf{F}_2$ -vector spaces such that the cohomology  $\mathbf{H}^*V$  has a basis  $\{v_i\}$ , then the cohomology  $\mathbf{H}^*D_2(V)$  has a basis consisting of pairwise products  $\{v_iv_j\}_{i< j}$ , together with Steenrod operations  $\{\overline{\mathbf{Sq}}\,v_i\}$ . It follows that  $\mathbf{H}^*D_k\mathbf{F}_2[-n]$  is generated by  $\mathbf{H}^*D_{k'}\mathbf{F}_2[-n]$  under the operations of pairwise product and Steenrod operations  $\mathbf{Sq}^i$ . The map  $\theta_n$  is a map of unstable  $\mathcal{A}^{\mathrm{Big}}$ -algebras, so the image of  $\theta_n$  is stable under the formation of products and closed under the operations  $\mathbf{Sq}^i$ . The inductive hypothesis implies that  $\mathbf{H}^*D_{k'}\mathbf{F}_2[-n]$  belongs to the image of  $\theta_n$ , so that  $\mathbf{H}^*D_k\mathbf{F}_2[-n]$  belongs to the image of  $\theta_n$  as well.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## A Pushout Square (Lecture 22)

In the last lecture we saw that the cohomology  $H^* \mathcal{F}(n)$  of the free  $E_{\infty}$ -algebra on one generator was itself freely generated by one element, as an unstable algebra over the big Steenrod algebra  $\mathcal{A}^{\mathrm{Big}}$ . The Cartan-Serre theorem implies that the cohomology ring  $H^* K(\mathbf{F}_2, n)$  is the free unstable  $\mathcal{A}$ -module on one generator, in the same degree. This suggests a close relationship between  $H^* \mathcal{F}(n)$  and  $H^* K(\mathbf{F}_2, n)$ . In fact, we can say more: there is a close relationship between the  $E_{\infty}$ -algebras  $\mathcal{F}(n)$  and  $C^* K(\mathbf{F}_2, n)$  for each  $n \geq 0$ .

To make this precise, we begin by observing that the canonical element  $\nu \in H^n K(\mathbf{F}_2, n)$  gives rise to a map of  $E_{\infty}$ -algebras

$$f: \mathfrak{F}(n) \to C^*K(\mathbf{F}_2, n).$$

Let  $\mu$  denote the canonical generator of  $H^* \mathcal{F}(n)$ , so that f carries  $\mu$  to  $\nu$ .

The map f is certainly not a homotopy equivalence. The target  $H^*K(\mathbf{F}_2, n)$  is a module over the usual Steenrod algebra  $\mathcal{A}$ , so that  $\operatorname{Sq}^0$  acts by the identity on  $H^*K(\mathbf{F}_2, n)$ . However,  $\operatorname{Sq}^0$  does not act by the identity on the cohomology of the left hand side. We therefore have

$$f(\mu - \operatorname{Sq}^{0} \mu) = f(\mu) - \operatorname{Sq}^{0} f(\mu) = \nu - \operatorname{Sq}^{0} \nu = 0,$$

so that f fails to be injective on cohomology.

However, this turns out to be the *only* obstruction to f being a homotopy equivalence. To make this precise, we observe that there is map  $g: \mathcal{F}(n) \to \mathcal{F}(n)$ , which is determined up to homotopy by the requirement that  $g(\mu) = \mu - \operatorname{Sq}^0 \mu \in \operatorname{H}^n \mathcal{F}(n)$ . The above calculation shows that  $f \circ g$  carries  $\mu$  to zero in  $\operatorname{H}^n K(\mathbf{F}_2, n)$ . We therefore obtain a (homotopy) commutative diagram of  $E_{\infty}$ -algebras

$$\begin{array}{ccc} \mathfrak{F}(n) & \stackrel{g}{\longrightarrow} \mathfrak{F}(n) \\ \downarrow & & \downarrow^{f} \\ \mathbf{F}_{2} & \longrightarrow C^{*}K(\mathbf{F}_{2}, n). \end{array}$$

Our goal in this lecture is to prove:

**Theorem 1.** The above diagram is a homotopy pushout square in the category of  $E_{\infty}$ -algebras over  $\mathbf{F}_2$ .

In other words, the cochain complex  $C^*K(\mathbf{F}_2, n)$  has a very simple presentation as an  $E_{\infty}$ -algebra over  $\mathbf{F}_2$ . It is "generated" by the tautological class  $\nu \in H^n K(\mathbf{F}_2, n)$ , and subject only to the "relation" that  $\nu$  is fixed by  $\operatorname{Sq}^0$ .

To prove Theorem 1, we need to understand homotopy pushouts in the world of  $E_{\infty}$ -algebras. We first recall the situation for ordinary commutative rings. Given a pair of commutative ring homomorphisms

$$A \leftarrow R \rightarrow B$$
,

the pushout  $A \coprod_R B$  in the category of commutative rings is given by the relative tensor product  $A \otimes_R B$ . In the case of  $E_{\infty}$ -algebras, the situation is more or less identical. More precisely:

- Given an  $E_{\infty}$ -algebra R, there is a good theory of R-modules (or R-module spectra).
- Given any map  $R \to A$  of  $E_{\infty}$ -algebras, we can regard A as an R-module.
- Given an  $E_{\infty}$ -ring R, the collection of R-module spectra is endowed with a tensor product operation  $(M, N) \mapsto M \otimes_R N$ . (More traditionally, this is denoted by  $M \wedge_R N$  and called the *smash product over* R).
- Given a pair of  $E_{\infty}$ -algebra maps

$$A \leftarrow R \rightarrow B$$
.

the homotopy pushout of A and B over R in the setting of  $E_{\infty}$ -rings is again an R-algebra, and the underlying R-module is given by the tensor product  $A \otimes_R B$ .

Given these facts, we can restate Theorem 1. We have a canonical map

$$\mathfrak{F}(n) \otimes_{\mathfrak{F}(n)} \mathbf{F}_2 \to C^*K(\mathbf{F}_2, n),$$

and we wish to show that this map is a homotopy equivalence. In other words, we wish to show that it induces an isomorphism after passing to cohomology. The cohomology of the right side is given by the Cartan-Serre theorem:  $H^*K(\mathbf{F}_2, n)$  can be identified with the polynomial ring on generators  $\{\operatorname{Sq}^I \nu\}$ , where I ranges over admissible positive sequences of excess < n. It therefore remains to compute the cohomology of the left hand side.

The calculation will be based on the following lemma:

**Lemma 2.** Let R be an  $E_{\infty}$ -algebra over  $\mathbf{F}_2$ , and let M and N be R-modules. Then  $H^*M$  and  $H^*N$  are modules over the cohomology ring  $H^*R$ . Suppose that  $H^*M$  is free as a graded  $H^*R$ -module. Then the canonical map

$$H^*M \otimes_{H^*R} H^*N \to H^*(M \otimes_R N)$$

is an isomorphism.

*Proof.* Choose elements  $\{x_i \in H^{n_i} M\}$  which freely generate  $H^* M$  as an  $H^* R$ -module. Each  $x_i$  determines a map of R-modules  $R[-n_i] \to M$ . Adding these together, we obtain a map  $\oplus R[-n_i] \to M$ . By assumption this map induces an isomorphism on cohomology, and is therefore a homotopy equivalence. Thus, M is a direct sum of *free* R-modules (in various degrees).

Let us say that an R-module M is good if the canonical map

$$H^*M \otimes_{H^*R} H^*N \to H^*(M \otimes_R N)$$

is an isomorphism. Both the left hand side and the right hand side above are functors of M, which commute with shifting and with the formation of direct sums. Therefore, to show that  $\oplus R[-n_i]$  is good, it will suffice to show that R is good. But this is clear, since

$$H^*R \otimes_{H^*R} H^*N \simeq H^*N \simeq H^*(R \otimes_R N).$$

To prove Theorem 1, we will show that Lemma 2 applies: namely, that  $H^* \mathcal{F}(n)$  is *free* when regarded s an  $H^* \mathcal{F}(n)$ -module via the map g. It then follows that we have an isomorphism

$$\mathrm{H}^*(\mathfrak{F}(n) \otimes_{\mathfrak{F}(n)} \mathbf{F}_2) \simeq \mathrm{H}^* \, \mathfrak{F}(n) \otimes_{\mathrm{H}^* \, \mathfrak{F}(n)} \mathbf{F}_2 = \mathrm{H}^* \, \mathfrak{F}(n) / I$$

where I is the ideal of  $H^* \mathcal{F}(n)$  generated by the elements g(x), where  $x \in H^* \mathcal{F}(n)$  has positive degree.

In the last lecture, we proved that  $H^* \mathcal{F}(n)$  is isomorphic to the free unstable  $\mathcal{A}^{\text{Big}}$ -module  $F^{\text{Big}}_{\text{Alg}}(n)$ . It is therefore isomorphic to a polynomial ring on generators  $\{\operatorname{Sq}^I \mu\}$ , where I ranges over admissible sequences of excess < n. For every such sequence I, we let  $X_I = g(\operatorname{Sq}^I \mu) = \operatorname{Sq}^I \mu - \operatorname{Sq}^I \operatorname{Sq}^0 \mu \in H^* \mathcal{F}(n)$ . To complete the proof of Theorem 1, it will suffice to verify the following:

**Proposition 3.** The cohomology ring  $H^* \mathcal{F}(n)$  is a polynomial ring on generators  $\{X_I\}_{Iadmissible \ of \ excess < n}$  and  $\{\operatorname{Sq}^I \mu\}_{Iadmissible \ and \ positive \ of \ excess < n}$ .

*Proof.* Let  $\mathcal{J}$  denote the collection of all admissible sequences of integers of excess < n. We have a decomposition  $\mathcal{J} = \mathcal{J}' \coprod \mathcal{J}''$ , where  $\mathcal{J}'$  consists of those sequences  $(i_1, \ldots, i_k)$  such that k > 0 and  $i_k < 0$ . The complement  $\mathcal{J}''$  has a further decomposition

$$\mathfrak{J}''=\mathfrak{J}''(0)\coprod\mathfrak{J}''(1)\coprod\ldots$$

where  $\mathcal{J}''(m)$  consists of those sequence  $(i_1, \ldots, i_k)$  which end with precisely k zeroes. For each  $I \in \mathcal{J}''(k)$ , let  $I^+ \in \mathcal{J}''(k+1)$  be the result of appending a zero to the sequence I. We have a decomposition

$$\mathrm{H}^* \, \mathfrak{F}(n) \simeq \mathbf{F}_2[\mathrm{Sq}^I \, \mu]_{I \in \mathcal{J}'} \otimes \mathbf{F}_2[\mathrm{Sq}^I \, \mu]_{I \in \mathcal{J}''}.$$

To complete the proof, it will suffice to show:

- (1) The polynomial ring  $\mathbf{F}_2[\operatorname{Sq}^I \mu]_{I \in \mathcal{J}'}$  is also polynomial on the generators  $\{X_I\}_{I \in \mathcal{J}'}$ .
- (2) The polynomial ring  $\mathbf{F}_2[\operatorname{Sq}^I \mu]_{I \in \mathcal{J}''}$  is also polynomial on the generators  $\{X_I\}_{I \in \mathcal{J}''}$  and  $\{\operatorname{Sq}^I \mu\}_{I \in \mathcal{J}''(0)}$ .

Assertion (2) follows immediately from the observation that  $X_I = \operatorname{Sq}^I \mu - \operatorname{Sq}^{I^+} \mu$  for  $I \in \mathcal{J}''$ . We can divide the proof of (1) further into three steps:

- (1a) The map  $\theta : \mathbf{F}_2[X_I]_{I \in \mathcal{J}'} \to \mathbf{F}_2[\operatorname{Sq}^I \mu]_{I \in \mathcal{J}'}$  is well-defined. In other words, if  $I \in \mathcal{J}'$ , then  $X_I$  belongs to  $\mathbf{F}_2[\operatorname{Sq}^I \mu]_{I \in \mathcal{J}'}$ .
- (1b) The map  $\theta$  is injective.
- (1c) The map  $\theta$  is surjective.

Assertion (1a) is an immediate consequence of the following:

**Lemma 4.** Let  $I=(i_m,\ldots,i_1)$  be a sequence of integers with  $i_1<0$ . Then in  $\mathcal{A}^{Big}$  we have an equality

$$\operatorname{Sq}^{I}\operatorname{Sq}^{0}=\sum_{\alpha}\operatorname{Sq}^{J_{\alpha}}$$

where each  $J_{\alpha}$  is an admissible sequence of the form  $(j_m, \ldots, j_0)$ , where  $j_0 < 0$ .

*Proof.* We first apply the Adem relations to write

$$\operatorname{Sq}^{i_1} \operatorname{Sq}^0 = \sum_{k} (2k - i_1, -k - 1) \operatorname{Sq}^k \operatorname{Sq}^{i_1 - k}.$$

The coefficient  $(2k-i_1, -k-1)$  vanishes unless

$$\frac{i_1}{2} \le k < 0.$$

We may therefore restrict our attention to those integers k for which  $i_1 - k \leq \frac{i_1}{2} < 0$ , so the sequence  $I'(k) = (i_m, \ldots, i_2, k, i_1 - k)$  ends with a negative integer.

Each I'(k) can be rewritten as a sum of admissible monomials using the Adem relations. Let us analyze this process. Given a sequence

$$J = (j_m, \dots, a, b, \dots, j_0)$$

with a < 2b, we have

$$\operatorname{Sq}^{J} = \sum_{k} (2k - a, b - k - 1) \operatorname{Sq}^{J_{k}},$$

where  $J_k$  is obtained from J by replacing a by b+k and b by a-k. The coefficient (2k-a,b-k-1) vanishes unless  $\frac{a}{2} \leq k < b$ ; in particular, we always have  $a-k \leq \frac{a}{2} < b$ . Thus, if the final entry in J is negative, the final entry in  $J_k$  will be negative.

We now prove (1b). Recall that the cohomology ring  $H^* \mathcal{F}(n) \simeq \mathbf{F}_2[\operatorname{Sq}^I \mu]_{I \in \mathcal{J}}$  has a natural grading by rank, where  $\operatorname{Sq}^I \mu$  has rank  $2^k$  for every sequence  $I = (i_1, \ldots, i_k)$ . This grading restricts to a grading on  $\mathbf{F}_2[\operatorname{Sq}^I \mu]_{I \in \mathcal{J}'}$ . We have an analogous grading on  $\mathbf{F}_2[X_I]_{I \in \mathcal{J}'}$ , where we declare  $\operatorname{rk}(X_I) = 2^k$  if  $I = (i_1, \ldots, i_k)$ . The map  $\theta : \mathbf{F}_2[X_I]_{I \in \mathcal{J}'} \to \mathbf{F}_2[\operatorname{Sq}^I \mu]_{I \in \mathcal{J}'}$  is not compatible with the gradings by rank. Instead we have

$$\theta(X_I) = \operatorname{Sq}^I \mu - \operatorname{Sq}^I \operatorname{Sq}^0 \mu = \operatorname{Sq}^I \mu + \text{ higher rank.}$$

We have an evident isomorphism  $\theta' : \mathbf{F}_2[X_I]_{I \in \mathfrak{J}'} \to \mathbf{F}_2[\operatorname{Sq}^I \mu]_{I \in \mathfrak{J}'}$ , given by  $X_I \mapsto \operatorname{Sq}^I \mu$ . Let  $x \in \mathbf{F}_2[X_I]_{I \in \mathfrak{J}'}$  be a nonzero element, and write x as a sum  $x = x_{k_0} + x_{k_1} + \ldots + x_{k_m}$  of homogeoneous elements of ranks  $k_0 < k_1 < \ldots < k_m$ . Then we have

$$\theta(x) = \theta'(x) + \text{ terms of rank } i.k.$$

In particular,  $\theta(x) = 0$  implies  $\theta'(x_{k_0}) = 0$ . Since  $\theta'$  is an isomorphism, we get  $x_{k_0} = 0$ , a contradiction. This completes the proof that  $\theta$  is injective.

We now prove that  $\theta$  is surjective. This is an immediate consequence of the following statement:

**Lemma 5.** Let  $I = (i_k, ..., i_1)$  be a sequence of integers with  $i_1 < 0$  (not necessarily admissible). Then  $\operatorname{Sq}^I \mu$  lies in the image of  $\theta$ .

*Proof.* We use descending induction on  $i_1$ . Observe that

$$\operatorname{Sq}^{I} \mu = (\operatorname{Sq}^{I} \mu - \operatorname{Sq}^{I} \operatorname{Sq}^{0} \mu) + (\operatorname{Sq}^{I} \operatorname{Sq}^{0} \mu) = \theta(X_{I}) + \operatorname{Sq}^{I} \operatorname{Sq}^{0} \mu.$$

It will therefore suffice to show that  $\operatorname{Sq}^I \operatorname{Sq}^0 \mu$  belongs to the image of  $\theta$ . Using the Adem relations, we can write

$$\operatorname{Sq}^{I} \operatorname{Sq}^{0} = \sum_{k} (2k - i_{1}, -k - 1) \operatorname{Sq}^{I_{k}}$$

with  $I_k = (i_k, \dots, i_2, k, i_1 - k)$ . The coefficient  $(2k - i_1, -k - 1)$  vanishes unless  $\frac{i_1}{2} \le k < 0$ . This inequality forces

$$i_1 < i_1 - k \le \frac{i_1}{2} < 0.$$

Therefore  $\operatorname{Sq}^{I_k}$  belongs to the image of  $\theta$  by the inductive hypothesis.

**Corollary 6.** For each  $n \geq 0$ , the homotopy pullback square

$$K(\mathbf{F}_{2}, n) \longrightarrow *$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$* \longrightarrow K(\mathbf{F}_{2}, n+1)$$

of topological spaces determines a homotopy pushout square

$$C^*K(\mathbf{F}_2,n) \longleftarrow \mathbf{F}_2$$

$$\uparrow \qquad \qquad \uparrow$$

$$\mathbf{F}_2 \longleftarrow C^*K(\mathbf{F}_2,n+1)$$

of  $E_{\infty}$ -algebras.

*Proof.* Theorem 1 implies that  $C^*K(\mathbf{F}_2, n+1)$  is freely generated by a single class  $\nu$  in degree (n+1), subject to the single relation killing  $\nu - \operatorname{Sq}^0 \nu$ . We can regard the homotopy pushout

$$\mathbf{F}_2 \otimes_{C^*K(\mathbf{F}_2,n+1)} \mathbf{F}_2$$

as the suspension of  $C^*K(\mathbf{F}_2, n+1)$  in the world of (augmented)  $E_{\infty}$ -algebras. Consequently, it has an analogous presentation as the free  $E_{\infty}$ -algebra generated by a class  $\Sigma(\nu)$  in degree n, subject to a single relation killing  $\Sigma(\nu - \operatorname{Sq}^0 \nu)$ . Since the Steenrod operation  $\operatorname{Sq}^0$  is stable, we can identify  $\Sigma(\nu - \operatorname{Sq}^0 \nu)$  with  $\Sigma(\nu) - \operatorname{Sq}^0 \Sigma(\nu)$ . Applying Theorem 1 again, we can identify this suspension with  $C^*K(\mathbf{F}_2, n)$ . It is easy to see that this identification is given by the map

$$\mathbf{F}_2 \otimes_{C^*K(\mathbf{F}_2,n+1)} \mathbf{F}_2 \to C^*K(\mathbf{F}_2,n)$$

described in the statement of Corollary 6.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Topics in Algebraic Topology (18.917): Lecture 23

In this lecture, we will discuss the convergence of the cohomological Eilenberg-Moore spectral sequence. We begin with a definition.

**Definition 1.** Let p be a prime number. A topological space X is p-finite if the following conditions are satisfied:

- The set  $\pi_0 X$  is finite.
- For every point  $x \in X$  and every i > 0, the group  $\pi_i(X, x)$  is a finite p-group.
- The groups  $\pi_i(X, x)$  vanish for  $i \gg 0$ .

**Example 2.** Every Eilenberg-MacLane space of the form  $K(\mathbf{Z}/p^k\mathbf{Z}, n)$  is p-finite.

**Remark 3.** Suppose given a fibration  $f: E \to B$ , where B is p-finite. Then E is p-finite if and only if each fiber of f is p-finite (this follows from the long exact sequence of homotopy groups).

**Lemma 4.** A path connected topological space X is p-finite if and only if there exists a sequence of fibrations

$$X \simeq X_m \to X_{m-1} \to \ldots \to X_0 \simeq *$$

where each  $X_i$  is a principal fibration over  $X_{i-1}$  with fiber  $K(\mathbf{F}_p, j)$  for some integer  $j \geq 1$ .

*Proof.* The "if" direction follows from Remark 3. To prove the converse, we work by induction on  $p^k = \prod_i |\pi_i(X, x)|$ , where x is some fixed base point of X. If k = 0 then X is weakly contractible and there is nothing to prove. Otherwise, there exists some largest i > 0 such that  $\pi_i(X, x)$  does not vanish.

Each orbit of  $\pi_1(X,x)$  on  $\pi_i(X,x)$  has cardinality a power of p, and the sum of the cardinality of the orbits is again a power of p. Since there is an orbit of size 1 (the orbit of the identity element), there must be at least p orbits of size 1: in other words, the subgroup G of  $\pi_1(X,x)$ -invariants in  $\pi_i(X,x)$  is nontrivial. Since G is a finite p-group, there exists an element of G of order p; let  $G_0$  be the cyclic subgroup of order p. Let X' be the space obtained from X by killing the subgroup  $G_0 \subseteq \pi_i(X,x)$ . Then  $X \to X'$  is equivalent to a principal fibration with fiber  $K(\mathbf{F}_p,i)$ . We now conclude by applying the inductive hypothesis to X'.  $\square$ 

Corollary 5. Let X be a p-finite space. Then each cohomology group  $H^n(X; \mathbf{F}_p)$  is a finite dimensional vector space over  $\mathbf{F}_p$ .

*Proof.* The result is true when  $X = K(\mathbf{F}_p, n)$  by an explicit calculation (which we performed in a previous lecture when p = 2). The result follows in general from Lemma 4 and the Serre spectral sequence.

The main result of today's lecture is the following:

Theorem 6. Suppose given a homotopy pullback square

$$X' \longrightarrow X$$

$$\downarrow \qquad \qquad \downarrow$$

$$Y' \longrightarrow Y$$

of p-finite spaces. Then the induced square

$$C^*(X'; \mathbf{F}_p) \longleftarrow C^*(X; \mathbf{F}_p)$$

$$\uparrow \qquad \qquad \uparrow$$

$$C^*(Y'; \mathbf{F}_p) \longleftarrow C^*(Y; \mathbf{F}_p)$$

is a homotopy pushout square of  $E_{\infty}$ -algebras.

**Remark 7.** The proof of Theorem 6 really requires much weaker hypotheses than *p*-finiteness, but this version will be sufficient for our immediate needs.

For the remainder of this lecture, we let  $C^*(Z)$  denote the mod-p cochain complex  $C^*(Z; \mathbf{F}_p)$  of a topological space Z. Theorem 6 asserts that the canonical map

$$C^*(X) \otimes_{C^*(Y)} C^*(Y') \to C^*(X')$$

induces an isomorphism after passing to cohomology. In the case where Y is a point, we can identify  $C^*(Y)$  with  $\mathbf{F}_p$ ; then Theorem 6 follows from the Kunneth theorem (since  $H^*(X)$  and  $H^*(Y')$  are finite dimensional in each degree thanks to Corollary 5).

In general, it is natural to try to prove Theorem 6 using a relative version of the same argument. For each point  $y \in Y$ , let  $X_y$ ,  $X_y'$ , and  $Y_y'$  denote the (homotopy) fibers of X, X', and Y' over the point y. We then have an identification  $X_y' \simeq X_y \times Y_y'$ , which induces an equivalence of  $E_{\infty}$ -algebras

$$C^*(X_y) \otimes C^*(Y_y') \to C^*(X_y').$$

The  $E_{\infty}$ -algebras  $C^*(X'_y)$  and  $C^*(X'_{y'})$  are equivalent whenever y and y' lie in the same path component of Y, and are *canonically* equivalent if we specify a path from y to y' (since the choice of such a path induces a weak homotopy equivalence of fibers  $X'_y \simeq X'_{y'}$ ). In other words, we can regard the construction

$$y \mapsto C^*(X'_y)$$

as providing a local system L of  $E_{\infty}$ -algebras over Y. Moreover, we can identify  $C^*(X')$  with the cochain complex  $C^*(Y;L)$  of Y with coefficients in L. Similarly, we have local systems

$$L_0: y \mapsto C^*(X_y)$$

$$L_1: y \mapsto C^*(Y_y').$$

and equivalences  $C^*(X) \simeq C^*(Y; L_0)$ ,  $C^*(Y') \simeq C^*(Y; L_1)$ . The Kunneth theorem provides an equivalence  $L \simeq L_0 \otimes L_1$  of local systems on Y. Theorem 6 then reduces to a special case of the following result:

**Theorem 8.** Let Y be a p-finite space. Let  $L_0$  and  $L_1$  be local systems (of cochain complexes of  $\mathbf{F}_p$ -vector spaces) on Y satisfying the following condition:

(\*) The cohomology groups  $H^* L_0$  and  $H^* L_1$  vanish for \* < 0.

Then the canonical map

$$C^*(Y; L_0) \otimes_{C^*(Y)} C^*(Y; L_1) \to C^*(Y; L_0 \otimes L_1)$$

is an isomorphism on cohomology.

Let us say that a local system (of cochain complexes)  $L_0$  on Y is good if it satisfies (\*), and the conclusion of Theorem 8 is satisfied for  $L_0$  (and for any other local system  $L_1$  satisfying (\*)). We wish to show that every  $L_0$  which satisfies (\*) is good.

For every local system  $L_0$ , we can define a new local system  $\tau^{\leq n}L_0$  equipped with a map  $\tau^{\leq n}L_0 \to L_0$ , uniquely determined (up to quasi-isomorphism) by the following condition:

$$\mathrm{H}^k \, \tau^{\leq n} L_0 \simeq \begin{cases} \mathrm{H}^k \, L_0 & \text{if } k \leq n \\ 0 & \text{otherwise.} \end{cases}$$

Then  $L_0$  is equivalent to the filtered colimit inj  $\lim \{ \tau^{\leq n} L_0 \}$ . To prove that  $L_0$  is good, it will therefore suffice to show that each  $\tau^{\leq n} L_0$  is good. In other words, we may assume that  $L_0$  has cohomology only in finitely many degrees.

The collection of good local systems is also closed under extensions. We may therefore suppose that L is concentrated in a single degree, corresponding to a representation V of the fundamental group  $\pi_1 Y$  (in some degree). Since  $\pi_1 Y$  is finite, we can write V as a filtered colimit of finite-dimensional representations of  $\pi_1 Y$ . It therefore suffices to prove the result when V is finite dimensional, and we work by induction on the dimension of V. If  $V \simeq 0$  there is nothing to prove. Assume that V is of positive dimension. The counting argument used in the proof of Lemma 4 shows that V contains a one-dimensional subspace  $V_0 \subseteq V$  on which  $\pi_1 Y$  acts trivially. By the inductive hypothesis, the local system  $V/V_0$  is good. It will therefore suffice to show that  $V_0$  is good. In other words, we have reduced the proof of Theorem 8 to the case where the local system  $L_0$  is trivial.

Using the same argument, we can reduce to the case where  $L_1$  is trivial. We can now restate Theorem 8 as the assertion that the canonical map

$$C^*(Y) \otimes_{C^*(Y)} C^*(Y) \to C^*(Y)$$

is an isomorphism on cohomology, which is obvious.

We conclude with an explanation of the relationship of Theorem 6 with the convergence of the Eilenberg-Moore spectral sequence. Let A be an  $E_{\infty}$ -algebra, and let M and N be A-modules. Choosing a resolution of M or N (or both) by free modules, we obtain a spectral sequence for computing cohomology  $H^*(M \otimes_A N)$ , with  $E_2$ -term given by

$$E_2^{p,q} = \operatorname{Tor}_{-p}^{\operatorname{H}^* A} (\operatorname{H}^* M \otimes \operatorname{H}^* N)^q.$$

This spectral sequence is of "homological type", and therefore converges without any additional assumptions. Given a homotopy pullback square

$$X' \longrightarrow X$$

$$\downarrow \qquad \qquad \downarrow$$

$$Y' \longrightarrow Y,$$

we get an induced map

$$C^*(X) \otimes_{C^*(Y)} C^*(Y') \to C^*(X').$$

The conclusion of Theorem 6 is that this map induces an isomorphism on cohomology, so we have a spectral sequence with  $E_2$ -term

$$E_2^{p,q} = \operatorname{Tor}_{-p}^{\operatorname{H}^*Y}(\operatorname{H}^*X, \operatorname{H}^*Y')^q$$

converging to  $H^*(X')$ . This is the classical cohomological Eilenberg-Moore spectral sequence.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Operations on $E_{\infty}$ -Algebras: (Lecture 24)

In this lecture, we will change our notation in discussing  $E_{\infty}$ -algebras: we will think of them as spectra, rather than complexes of  $\mathbf{F}_2$ -vector spaces. We will therefore view the cohomology of the underlying complex as a homotopy group of the underlying spectrum, so we have

$$\pi_n A \simeq H^{-n} A$$
.

We have constructed the big Steenrod algebra  $\mathcal{A}^{\text{Big}}$  so that it acts by stable operations on homotopy of  $E_{\infty}$ -algebras over  $\mathbf{F}_2$ . Our goal in this lecture is to reformulate this in a more functorial way. Our discussion will be somewhat informal. To make these ideas precise, we really need to work in the setting of higher categories, but we will ignore this point.

We begin with some remarks about the category  $\mathfrak{S}$  of spectra. For every pair of spectra X and Y, we have a smash product which we will denote by  $X \otimes Y$ . The smash product endows  $\mathfrak{S}$  with a symmetric monoidal structure, and this symmetric monoidal structure is *closed*: that is, for every pair of spectra X and Y we can define a function spectrum  $\operatorname{Map}(X,Y)$  with the following universal property:

$$\operatorname{Hom}(Z, \operatorname{Map}(X, Y)) = \operatorname{Hom}(X \otimes Z, Y).$$

The function spectrum  $\operatorname{Map}(X,Y)$  has the property that  $\pi_i \operatorname{Map}(X,Y)$  can be identified with the set of homotopy classes of maps from X into the *i*-fold suspension Y[i].

In the special case where X = Y, the spectrum  $\operatorname{Map}(X, X)$  is equipped with additional structure, given by composition of maps from X to X. The spectrum  $\operatorname{Map}(X, X)$  is an example of an  $A_{\infty}$  (or associative) ring spectrum. It should be viewed as a ring of endomorphisms of X, and X is an example of a *module* over the spectrum  $\operatorname{Map}(X, X)$ .

More generally, for any category  $\mathcal{C}$ , the category of functors  $\operatorname{Fun}(\mathcal{C},\mathfrak{S})$  from  $\mathcal{C}$  to spectra is *enriched* over spectra; that is, given a pair of functors  $F, F' : \mathcal{C} \to \mathfrak{S}$ , we can define a spectrum of maps  $\operatorname{Map}(F, F')$ . Again, in the special case where F = F', we get an associative ring spectrum  $R = \operatorname{Map}(F, F)$ . For every object  $C \in \mathcal{C}$ , the spectrum F(C) has a canonical action of the  $A_{\infty}$ -algebra R.

We wish to study the special case in which  $\mathcal{C}$  is the category of  $E_{\infty}$ -algebras over  $\mathbf{F}_2$ , and the functor  $G:\mathcal{C}\to\mathfrak{S}$  assigns to each  $E_{\infty}$ -algebra A its underlying spectrum G(A). The ring spectrum  $R=\mathrm{Map}(G,G)$  then acts on the underlying spectrum of every  $E_{\infty}$ -algebra A over  $\mathbf{F}_2$ , so that every element of  $\pi_n R$  gives a map  $A\to A[n]$ , and therefore a map  $\pi_k A\to \pi_{n+k} A$ . This construction is functorial in A; we can therefore think of elements of  $\pi_* R$  as giving rise to operations which act on the homotopy groups  $\pi_* A$  for every  $E_{\infty}$ -algebra A over  $\mathbf{F}_2$ .

Our goal in this lecture is to understand what the  $A_{\infty}$ -algebra R looks like. More precisely, we will compute the homotopy groups of R and show that they coincide a suitably completion of the graded pieces of the big Steenrod algebra  $\mathcal{A}^{\text{Big}}$ .

The forgetful functor G from  $E_{\infty}$ -algebras over  $\mathbf{F}_2$  to spectra can be described as a composition

$$\{E_{\infty} - \text{algebras over } \mathbf{F}_2\} \to \{\text{complexes over } \mathbf{F}_2\} \to \{\text{spectra}\}$$

where the first map forgets the multiplication, and the second map carries a complex V to the generalized Eilenberg-MacLane spectrum HV. This functor has a left adjoint  $F: \mathfrak{S} \to \mathfrak{C}$ , given by the formula

$$F(X) = (\bigoplus_{n \ge 0} X_{h\Sigma_n}^{\otimes n}) \otimes \mathbf{F}_2.$$

Here the tensor product indicates the smash product of spectra, and we identify  $\mathbf{F}_2$  with the Eilenberg-MacLane spectrum  $H\mathbf{F}_2$ . The adjointness between F and G yields a canonical identification of spectra

$$\operatorname{Map}_{\operatorname{Fun}(\mathfrak{C},\mathfrak{S})}(G,G) \simeq \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id},G \circ F).$$

We therefore need to be able to understand maps in the category of functors  $\operatorname{Fun}(\mathfrak{S},\mathfrak{S})$  from spectra to spectra. To this end, we need to introduce a definition:

**Definition 1.** Let E be a functor from spectra to spectra. We say that E is exact if the following conditions are satisfied:

- (1) The functor E carries zero objects to zero objects (i.e., if X is weakly contractible, then E(X) is weakly contractible).
- (2) For every spectrum X, the canonical map  $\Sigma E(X) \to E(\Sigma X)$  (which exists in virtue of assumption (1)) is a weak homotopy equivalence.

Our calculation rests on the following observation:

**Lemma 2.** Let E be an exact functor from spectra to spectra. Then the canonical map

$$\alpha: \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id}, E) \to \operatorname{Map}_{\mathfrak{S}}(S, E(S)) \simeq E(S)$$

is a weak equivalence. Here S denotes the sphere spectrum.

Sketch of proof. We will describe how to construct a map

$$E(S) \to \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id},E)$$

which is homotopy inverse to  $\alpha$ . We can identify this with a collection of maps,  $E(S) \otimes X \to E(X)$ , depending functorially on the spectrum X.

Let  $X_n$  denote the nth space  $\Omega^{\infty-n}X$  of the spectrum X, so we can identify X with the colimit of the sequence

$$\Sigma^{\infty} X_0 \to \Sigma^{-1} \Sigma^{\infty} X_1 \to \Sigma^{-2} \Sigma^{\infty} X_2 \to \dots$$

We can identify  $E(S) \otimes X$  with the colimit of the sequence  $\Sigma^{-n}(E(S) \otimes \Sigma^{\infty} X_n)$ , and we have a canonical map

$$\operatorname{colim} \Sigma^{-n} E(\Sigma^{\infty} X_n) \simeq \operatorname{colim} E(\Sigma^{-n} \Sigma^{\infty} X_n) \to E(X).$$

It therefore suffices to construct a compatible family of maps from  $E(S) \otimes \Sigma^{\infty} X_n$  to  $E(\Sigma^{\infty} X_n)$ . Such a map is simply a map from  $X_n$  to the mapping space  $[E(S), E(\Sigma^{\infty} X_n)]$ , which arises by applying E to the canonical map from  $X_n$  to the mapping space  $[*, X_n]$ .

Unfortunately, the composition  $G \circ F \in \text{Fun}(\mathfrak{S}, \mathfrak{S})$  does not satisfy the hypotheses of Lemma 2. We have

$$(G \circ F)(X) \simeq \bigoplus_n (X_{h\Sigma_n}^{\otimes n}) \otimes \mathbf{F}_2;$$

in particular

$$(G \circ F)(0) \simeq \mathbf{F}_2.$$

To address this first obstruction, we have the following result:

**Lemma 3.** Let E be a functor from spectra to spectra. For every spectrum X, the canonical map  $X \to 0$  induces a map  $E(X) \to E(0)$ ; let  $E_0(X)$  denote the fiber of this map. Then the natural transformation  $E_0 \to E$  induces a weak homotopy equivalence

$$\alpha: \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id}, E_0) \to \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id}, E).$$

Sketch of proof. Let  $Y = \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id}, E)$ , so that we have a canonical map  $Y \otimes \operatorname{id} \to E$ . Then, for every spectrum X, we get a commutative diagram

$$\begin{array}{ccc}
Y \otimes X \longrightarrow E(X) \\
\downarrow & & \downarrow \\
0 \longrightarrow E(0),
\end{array}$$

which determines a map  $Y \otimes X \to E_0(X)$ . These maps together constitute a map  $Y \to \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id}, E_0)$ , which is homotopy inverse to  $\alpha$ .

Applying Lemma 3 to the composition  $G \circ F$ , we obtain the functor

$$X \mapsto (\bigoplus_{n>0} X_{h\Sigma_n}^{\otimes n}) \otimes \mathbf{F}_2.$$

This functor is still not exact. However, we can address the situation using Goodwillie's calculus of functors.

**Lemma 4** (Goodwillie). Let E be a functor from spectra to spectra, and suppose that  $E(0) \simeq 0$ . Define a new functor  $E' : \mathfrak{S} \to \mathfrak{S}$  by the formula

$$E'(X) = \operatorname{proj lim}\{\ldots \to \Sigma^2 E(\Omega^2 X) \to \Sigma E(\Omega X) \to E(X)\}.$$

Then E' is exact, and the canonical map

$$\operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id},E') \to \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id},E)$$

is a weak homotopy equivalence.

*Proof.* We will only prove the second statement. Since  $\Sigma^n$  and  $\Omega^n$  are mutually inverse equivalences from the category of spectra to itself, we have canonical homotopy equivalences

$$\operatorname{Map}(\operatorname{id}, \Sigma^n \circ E \circ \Omega^n) \simeq \operatorname{Map}(\Omega^n \circ \operatorname{id} \circ \Sigma^n, E) \simeq \operatorname{Map}(\operatorname{id}, E).$$

The desired result now follows by passing to the limit.

We are now ready to compute the homotopy groups of the  $A_{\infty}$ -algebra

$$R = \operatorname{Map}_{\operatorname{Fun}(\mathcal{C},\mathfrak{S})}(G,G).$$

We first use Lemma 3 to replace  $G \circ F$  by the pointed functor

$$E: X \mapsto \bigoplus_{n>0} X_{h\Sigma_n}^{\otimes n} \otimes \mathbf{F}_2,$$

and then Lemma 4 to replace E by its dual Goodwillie derivative E'. The functor E' is exact, and we have

$$R = \operatorname{Map}_{\operatorname{Fun}(\mathfrak{C},\mathfrak{S})}(G,G)$$

$$\simeq \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id},G\circ F)$$

$$\simeq \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id},E)$$

$$\simeq \operatorname{Map}_{\operatorname{Fun}(\mathfrak{S},\mathfrak{S})}(\operatorname{id},E')$$

$$\simeq E'(S)$$

$$\simeq \operatorname{proj}\lim \Sigma^k E(S^{-k}).$$

It follows for every integer n, we have an exact sequence

$$0 \to \text{proj lim}\{\pi_{n+1-k}E(S^{-k})\} \to \pi_n R \to \text{proj lim}\{\pi_{n-k}E(S^{-k})\} \to 0.$$

We will show that the proj lim<sup>1</sup>-term vanishes, and compute the limit on the right hand side.

By definition,  $(G \circ F)(S^{-k})$  is the free  $E_{\infty}$ -algebra  $\mathfrak{F}(k)$  on one generator in cohomological degree k, and  $E(S^{-k})$  is its "augmentation ideal", so we have a canonical decomposition

$$\mathfrak{F}(k) = E(S^{-k}) \oplus \mathbf{F}_2.$$

Therefore, we can identify  $\pi_{n-k}E(S^{-k})$  with the summand of

$$F_{\text{Alg}}^{\text{Big}}(k)^{k-n} \simeq \mathbf{F}_2[\operatorname{Sq}^I \mu_k]^{k-n}$$
:

spanned by those expressions of positive degree; here I ranges over all admissible sequences of integers having excess < k. Let us denote this summand by  $\mathbf{F}_2[\operatorname{Sq}^I \mu_k]_0^{k-n}$ .

We have an inverse system of graded vector spaces

$$\dots \to \mathbf{F}_2[\operatorname{Sq}^I \mu_{k+1}] \xrightarrow{\theta_k} \mathbf{F}_2[\operatorname{Sq}^I \mu_k]_0 \to \dots$$

where each map  $\theta_k$  lowers cohomological degrees by 1. Moreover, we have  $\theta_k(\mu_{k+1}) = \mu_k$ . Since the Steenrod operations are stable, it follows that  $\theta_k(\operatorname{Sq}^I \mu_{k+1}) = \operatorname{Sq}^I \mu_k$ . The map  $\theta_k$  is induced by a map of  $E_{\infty}$ -algebras

$$\mathfrak{F}(k+1) \to \mathbf{F}_2 \times_{\mathfrak{F}(k)} \mathbf{F}_2,$$

and the multiplication on the right hand side is trivial at the level of homotopy groups. It follows that  $\theta_k$  vanishes on products.

The inverse system

$$\dots \to \mathbf{F}_2[\operatorname{Sq}^I \mu_{k+1}] \xrightarrow{\theta_k} \mathbf{F}_2[\operatorname{Sq}^I \mu_k]_0 \to \dots$$

is equivalent to the inverse system obtained by replacing each of the spaces  $\mathbf{F}_2[\operatorname{Sq}^I \mu_k]_0$  by the image of  $\theta_k$ . The above analysis shows that this subspace has a basis given by  $\{\operatorname{Sq}^I \mu_k\}$ , where I is an admissible sequence of integers having excess  $\leq k$ . We then obtain an inverse system of vector spaces

$$\dots \to \mathbf{F}_2\{\operatorname{Sq}^I \mu_{k+1}\} \xrightarrow{\theta'_k} \mathbf{F}_2\{\operatorname{Sq}^I \mu_k\} \to \dots$$

where the maps  $\theta'_k$  are surjective. This proves the vanishing of the  $\lim^{1}$ -term, and shows that  $\pi_n R$  is isomorphic to the inverse limit of the free vector spaces generated by the sets

$$\{\operatorname{Sq}^{I} \mu_{k} : I \text{ admissible of excess } \leq k \text{ and degree} = -n\}.$$

This vector space can be identified with a completion of  $\mathcal{A}^{\text{Big}^{-n}}$ . Recall that elements of  $\mathcal{A}^{\text{Big}}$  of degree -n can be written as a finite sum

$$\sum_{\alpha} \operatorname{Sq}^{I_{\alpha}}$$

where  $I_{\alpha}$  ranges over some collection of admissible sequences of integers which sum to -n. The vector space  $\pi_n R$  is similar, except that we allow infinite sums

$$f = \operatorname{Sq}^{I_0} + \operatorname{Sq}^{I_1} + \dots$$

so long as the excess of the sequences  $\{I_k\}$  tends to  $\infty$ . (Note that, in this case, we can act by f on the cohomology of any  $E_{\infty}$ -algebra A, since for each  $x \in H^n A$  almost all of the expressions  $\operatorname{Sq}^{I_k} x$  will vanish by virtue of instability).

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## T and the Cohomology of Spaces (Lecture 25)

In the last lecture, we showed that if G denotes the forgetful functor from the category of  $E_{\infty}$ -algebras over  $\mathbf{F}_2$  to spectra, then  $R = \operatorname{Map}(G, G)$  is an  $A_{\infty}$ -ring spectrum whose homotopy groups  $\pi_* R$  form a graded ring, isomorphic to a suitable completion of the big Steenrod algebra  $\mathcal{A}^{\operatorname{Big}}$ .

Remark 1. If A is an  $E_{\infty}$ -algebra over  $\mathbf{F}_2$ , then A is in particular an  $\mathbf{F}_2$ -module, so that  $\mathbf{F}_2$  acts on the underlying spectrum of A. This construction is functorial in A, and so gives rise to a map of  $A_{\infty}$ -algebras from  $\mathbf{F}_2$  into R. This map is *not* central. That is, R is an  $A_{\infty}$ -ring spectrum, but it cannot be regarded as an  $A_{\infty}$ -algebra over the ring  $\mathbf{F}_2$ .

This result has an analogue for the ordinary Steenrod algebra. More precisely, let  $R' = \text{Map}(\mathbf{F}_2, \mathbf{F}_2)$  be the  $A_{\infty}$ -algebra of endomorphisms of the Eilenberg-MacLane spectrum  $H\mathbf{F}_2$ . Then R' can be identified with the homotopy inverse limit of reduced cochain complexes

$$\operatorname{proj lim} \overline{C}^*(K(\mathbf{F}_2, n); \mathbf{F}_2)[n],$$

so we get short exact sequences

$$0 \to \lim_{n \to \infty} \{ H^{n+k+1} K(\mathbf{F}_2, n) \} \to \pi_{-k} R' \to \lim_{n \to \infty} \{ H^{n+k} K(\mathbf{F}_2, n) \} \to 0.$$

Using the same argument as in the previous lecture, we deduce that the  $\lim^{1}$ -term vanishes, and the right hand side can be identified with the inverse limit of vector spaces having basis  $\{\operatorname{Sq}^{I} \mu_{n}\}$ , where I ranges over positive admissible monomials of degree k and excess  $\leq n$ . This sequence of vector spaces stabilizes, since every positive admissible sequence  $I = (i_{1}, \ldots, i_{m})$  has excess  $i_{1} - i_{2} - \ldots - i_{m} \leq i_{1} + i_{2} + \ldots + i_{m} = \deg(I)$ . Passing to the inverse limit, we get an isomorphism of graded rings

$$\pi_* R' \simeq A$$
.

By construction, R acts on the underlying spectrum of every  $E_{\infty}$ -algebra over  $\mathbf{F}_2$ . In particular, R acts on  $\mathbf{F}_2$  itself, via a map  $R \to R'$  which induces, on the level of homotopy groups, the canonical surjection  $\mathcal{A}^{\text{Big}} \to \mathcal{A}$ .

We now turn to the real goal of this lecture. Let X be a topological space, and V a finite dimensional vector space over  $\mathbf{F}_2$ . We have a canonical evaluation map

$$X^{BV}\times BV\to X$$

which induces on cohomology a map

$$H^* X \to H^* (X^{BV} \times BV) \simeq H^* X^{BV} \otimes H^* BV.$$

This is adjoint to a map

$$\theta_X: T_V \operatorname{H}^* X \to \operatorname{H}^* X^{BV}$$

of unstable A-algebras. We will prove:

**Theorem 2.** Suppose that X is a 2-finite space. Then the map  $\theta_X$  is an isomorphism.

**Remark 3.** If X is 2-finite, then any mapping space  $X^{BV}$  is again 2-finite. To see this, we first use induction on V to reduce to the case where  $V \simeq \mathbf{F}_2$ . Choose a filtration  $X \simeq X_m \to \ldots \to X_0 \simeq *$ , where each map is a fibration whose fiber is an Eilenberg-MacLane space  $K(\mathbf{F}_2, n)$ . Then we have an induced filtration

$$X^{B\mathbf{F}_2} \simeq X_m^{B\mathbf{F}_2} \to \ldots \to X_0^{B\mathbf{F}_2} \simeq *,$$

and each map is a fibration whose fiber is a generalized Eilenberg-MacLane space  $K(\mathbf{F}_2, n) \times K(\mathbf{F}_2, n-1) \times \dots \times K(\mathbf{F}_2, 0)$  (and in particular 2-finite).

We have already proven Theorem 2 in the case where  $V = \mathbf{F}_2$  and X is an Eilenberg-MacLane space  $K(\mathbf{F}_2, n)$ . It follows, by induction on the dimension of V, that Theorem 2 holds in general when  $X = K(\mathbf{F}_2, n)$ . (It is also possible to prove this by repeating the original argument.)

If X is a disjoint union of path components  $X_{\alpha}$  (necessarily finite in number), then  $\theta_X$  can be identified with the product of the maps  $\theta_{X_{\alpha}}$ . Therefore, to prove Theorem 2 it suffices to treat the case where X is path connected. In this case, we have seen that X admits a finite filtration

$$X \simeq X_m \to X_{m-1} \to \ldots \to X_0 \simeq *$$

where each  $X_{i+1}$  is a principal fibration over  $X_i$  with fiber  $K(\mathbf{F}_2, n_i)$ . We will prove that each  $\theta_{X_i}$  is an isomorphism, using induction on i: the case i = 0 is obvious. To handle, the inductive step, we study the homotopy pullback square

$$X_{i+1} \longrightarrow *$$

$$\downarrow \qquad \qquad \downarrow$$

$$X_{i} \longrightarrow K(\mathbf{F}_{2}, n_{i} + 1).$$

It will suffice to prove the following:

Proposition 4. Suppose given a homotopy pullback diagram

$$X' \longrightarrow X$$

$$\downarrow \qquad \qquad \downarrow$$

$$Y' \longrightarrow Y$$

of 2-finite spaces. If  $\theta_X$ ,  $\theta_Y$ , and  $\theta_{Y'}$  are isomorphisms, then so is  $\theta_{X'}$ .

We begin with a few general remarks. Let A be an  $E_{\infty}$ -algebra over  $\mathbf{F}_2$ , and let M and N be a pair of A-modules. The relative tensor product  $M \otimes_A N$  is defined to be the geometric realization of a simplicial spectrum  $B^A_{\bullet}(M,N)$ , with

$$B_n^A(M,N) = M \otimes A \otimes \ldots \otimes A \otimes N$$

(here the factor A appears n-times, and all tensor products are taken over  $\mathbf{F}_2$ ).

For any simplicial spectrum  $X_{\bullet}$ , the homotopy groups of the geometric realization  $|X_{\bullet}|$  can be computed by means of a spectrum sequence with  $E_1$  term given by

$$E_1^{p,q} = \pi_p X_q.$$

If R is an  $A_{\infty}$ -algebra, and  $X_{\bullet}$  is a simplicial R-module spectrum, then this spectral sequence is a spectral sequence of  $\pi_*R$ -modules: that is, for each  $1 \le r \le \infty$  we have maps

$$E_r^{p,q}\otimes\pi_{p'}R\to E_r^{p+p',q}$$

which exhibit each  $E_r^{*,q}$  as a module over  $\pi_*R$ , and the differentials are compatible with this module structure.

In particular, suppose that A is an  $E_{\infty}$ -algebra over  $\mathbf{F}_2$ , and that M and N are  $E_{\infty}$ -algebras over A. Then the simplicial object  $B_n^A(M,N)$  is a simplicial  $E_{\infty}$ -algebra over  $\mathbf{F}_2$ , and in particular a simplicial R-module, where R is the ring spectrum studied in the previous lecture. It follows that the homotopy groups  $\pi_*(M \otimes_A N)$  can be computed by a spectral sequence  $\{E_r^{p,q}, d_r\}$  satisfying the following:

- (a) Each  $E_r^{*,q}$  is a module over the big Steenrod algebra  $\mathcal{A}^{\text{Big}}$ .
- (b) Each differential  $d_r$  is compatible with the action of  $\mathcal{A}^{\text{Big}}$ .
- (c) Each  $E_1^{*,q}$  is isomorphic (as an  $\mathcal{A}^{\text{Big}}$ -module) to the tensor product

$$\pi_* M \otimes \pi_* A \otimes \ldots \otimes \pi_* A \otimes \pi_* N$$
,

where the factor  $\pi_*A$  occurs q times.

We now return to the situation of Proposition 4. The convergence result of the previous lecture guarantees that the natural map

$$C^*Y' \otimes_{C^*Y} C^*X \to C^*X'$$

is an equivalence. It follows that  $H^*X'$  can be computed by a spectral sequence  $\{E_r^{p,q}, d_r\}$  satisfying conditions (a) and (b), with

$$E_1^{-*,q} = H^* Y' \otimes H^* Y \otimes \ldots \otimes H^* Y \otimes H^* X.$$

It follows that each of the  $\mathcal{A}^{\text{Big}}$ -modules  $E_1^{-*,q}$  is actually an unstable  $\mathcal{A}$ -module. Since this condition is stable under passage to subquotients, we obtain the following stronger version of condition (a):

(a') Each  $E_r^{*,q}$  is an unstable  $\mathcal{A}$ -module.

We have another homotopy pullback diagram

$$X'^{BV} \longrightarrow X^{BV}$$

$$\downarrow \qquad \qquad \downarrow$$

$$Y'^{BV} \longrightarrow Y^{BV},$$

which consists of 2-finite spaces in virtue of Remark 3. Applying the same reasoning, we get another spectral sequence  $\{E'_r^{p,q}, d'_r\}$  satisfying (a') and (b), with

$$E'_1^{-*,q} \simeq \operatorname{H}^* Y'^{BV} \otimes \operatorname{H}^* Y^{BV} \otimes \ldots \otimes \operatorname{H}^* Y^{BV} \otimes \operatorname{H}^* X^{BV}.$$

The evaluation maps  $Z^{BV} \times BV \to Z$  give rise to a collection of maps

$$E_r^{*,q} \to E_r^{\prime *,q} \otimes H^* BV.$$

Passing to adjoints and using the exactness of  $T_V$ , we get a map of spectral sequences

$$T_V E_r^{*,q} \to {E'}_r^{*,q}$$
.

Since  $T_V$  is compatible with tensor products, our hypothesis on Y', Y and X guarantees that these maps are isomorphisms when r = 1. It then follows by induction on r that these maps are isomorphisms for all  $r < \infty$ . For r > q, we have a sequence of surjections

$$E_r^{*,q} \to E_{r+1}^{*,q} \to \dots$$

$$E_r^{\prime *,q} \to E_{r+1}^{\prime *,q} \to \dots$$

Since  $T_V$  commutes with colimits (being a left adjoint, we conclude by passing to the limit that the map  $T_V E_{\infty}^{*,q} \to {E'}_{\infty}^{*,q}$  is an isomorphism. We now consider the canonical map

$$T_V \operatorname{H}^* X' \to \operatorname{H}^* X'^{BV}$$
.

The preceding spectral sequences give increasing filtrations

$$0 \subseteq F_0 \operatorname{H}^* X' \subseteq F_1 \operatorname{H}^* X' \subseteq \ldots \subseteq \operatorname{H}^* X'$$
$$0 \subseteq F_0 \operatorname{H}^* X'^{BV} \subseteq F_1 \operatorname{H}^* X'^{BV} \subseteq \ldots \subseteq \operatorname{H}^* X'^{BV}$$

by A-submodules. Using the exactness of  $T_V$ , we get a map of exact sequences

$$0 \longrightarrow T_{V}F_{i-1} \operatorname{H}^{*} X' \longrightarrow T_{V}F_{i} \operatorname{H}^{*} X' \longrightarrow T_{V}E_{\infty}^{*,i} \longrightarrow 0$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$0 \longrightarrow F_{i-1} \operatorname{H}^{*} X'^{BV} \longrightarrow F_{i} \operatorname{H}^{*} X'^{BV} \longrightarrow E_{\infty}^{*,i} \longrightarrow 0.$$

Using induction on i and the snake Lemma, we deduce that each of the maps

$$T_V F_i \operatorname{H}^* X' \to F_i \operatorname{H}^* X'^{BV}$$

is an isomorphism. Passing to the limit over i (and using the fact that  $T_V$  commutes with direct limits), we deduce that  $\theta_{X'}: T_V \to^* X' \to^* X'^{BV}$  is an isomorphism, as desired.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Profinite Spaces (Lecture 26)

Let p be a prime number. In this lecture we will introduce the category of p-profinite spaces. We begin by reviewing an example from classical algebra.

Let  $\mathcal{C}$  be the category of abelian groups, and let  $\mathcal{C}_0 \subseteq \mathcal{C}$  be the full subcategory consisting of *finitely generated* abelian groups. Every abelian group A is the union of its finitely generated subgroups. Consequently, every object of  $\mathcal{C}$  can be obtained as a (filtered) direct limit of objects in  $\mathcal{C}_0$ . Moreover, the morphisms in  $\mathcal{C}$  are determined by the morphisms in  $\mathcal{C}_0$ . If A is a finitely generated abelian group and  $\{B_\beta\}$  is any filtered system of abelian groups, then we have a bijection

$$\lim_{A \to \infty} \operatorname{Hom}(A, B_{\beta}) \operatorname{Hom}(A, \lim_{A \to \infty} B_{\beta}).$$

More generally, if A is given as a filtered colimit of abelian groups, then we get a bijection

$$\operatorname{Hom}(\varinjlim A_{\alpha}, \varinjlim B_{\beta}) \simeq \varprojlim_{\alpha} \operatorname{Hom}(A_{\alpha}, \varinjlim B_{\beta}) \simeq \varprojlim_{\alpha} \varinjlim_{\beta} \operatorname{Hom}(A_{\alpha}, B_{\beta}).$$

We can summarize the situation by saying that  $\mathcal{C}$  is equivalent to the category of Ind-objects of  $\mathcal{C}_0$ :

**Definition 1.** Let  $\mathcal{C}_0$  be a category. The category  $\operatorname{Ind}(\mathcal{C}_0)$  of  $\operatorname{Ind}$ -objects of  $\mathcal{C}_0$  is defined as follows:

- (1) The objects of  $\operatorname{Ind}(\mathcal{C}_0)$  are formal direct limits " $\varprojlim C_{\alpha}$ ", where  $\{C_{\alpha}\}$  is a filtered diagram in  $\mathcal{C}_0$ .
- (2) Morphisms in  $\operatorname{Ind}(\mathcal{C}_0)$  are given by the formula

$$\operatorname{Hom}("\varinjlim C_{\alpha}", "\varinjlim D_{\beta}") = \varprojlim_{\alpha} \varinjlim_{\beta} \operatorname{Hom}(C_{\alpha}, D_{\beta}).$$

**Remark 2.** There is a fully faithful embedding from  $\mathcal{C}_0$  into  $\operatorname{Ind}(\mathcal{C}_0)$ , which carries an object  $C \in \mathcal{C}_0$  to the constant diagram consisting of the single object C. We will generally abuse notation and identify  $\mathcal{C}_0$  with its image under this embedding.

The category  $\operatorname{Ind}(\mathcal{C}_0)$  admits filtered colimits. Moreover, an object " $\varinjlim C_{\alpha}$ " in  $\operatorname{Ind}(\mathcal{C}_0)$  actually does coincide with the colimit of the diagram  $\{C_{\alpha}\}$  in  $\operatorname{Ind}(\mathcal{C}_0)$ .

**Remark 3.** The category  $\operatorname{Ind}(\mathcal{C}_0)$  can be characterized by the following universal property: for any category  $\mathcal{D}$  which admits filtered colimits, the restriction functor

$$\operatorname{Fun}_0(\operatorname{Ind}(\mathfrak{C}_0), \mathfrak{D}) \to \operatorname{Fun}(\mathfrak{C}_0, \mathfrak{D})$$

is an equivalence of categories, where the left side is the category of functors from  $\operatorname{Ind}(\mathcal{C}_0)$  to  $\mathcal{D}$  which preserve filtered colimits.

**Example 4.** Let  $\mathcal{C}$  be the category of groups (or rings, or any other type of algebraic structure). Then  $\mathcal{C}$  is equivalent to  $\operatorname{Ind}(\mathcal{C}_0)$ , where  $\mathcal{C}_0 \subseteq \mathcal{C}$  is the full subcategory spanned by the finitely presented groups (or rings, etcetera).

There is a dual construction, which replaces a category  $\mathcal{C}_0$  by the category  $\operatorname{Pro}(\mathcal{C}_0)$  of  $\operatorname{pro-objects}$  in  $\mathcal{C}_0$ : that is, formal inverse limits " $\lim C_{\alpha}$ " of filtered diagrams in  $\mathcal{C}_0$ .

**Example 5.** Let  $\mathcal{C}_0$  be the category of *finite* groups. Then  $Pro(\mathcal{C}_0)$  is equivalent to the category of *profinite* groups: that is, topological groups which are compact, Hausdorff, and totally disconnected.

The construction  $\mathcal{C}_0 \mapsto \operatorname{Pro}(\mathcal{C}_0)$  makes sense not only for ordinary categories, but also for homotopy theories. In other words, suppose that  $\mathcal{C}_0$  is a category enriched over topological spaces (so that for every pair of objects  $X, Y \in \mathcal{C}_0$ , we have a mapping space  $\operatorname{Map}_{\mathcal{C}_0}(X, Y)$ ). Then we can define a new topological category  $\operatorname{Pro}(\mathcal{C}_0)$ . Roughly speaking, the objects of  $\operatorname{Pro}(\mathcal{C}_0)$  are given by formal filtered limits " $\varprojlim \mathcal{C}_{\alpha}$ " in  $\mathcal{C}_0$ , and the morphisms are described by the formula

$$\operatorname{Map}(\operatorname{"lim} C_{\alpha}, \operatorname{"lim} D_{\beta}) = \operatorname{holim}_{\beta} \operatorname{hocolim}_{\alpha} \operatorname{Map}(C_{\alpha}, D_{\beta}).$$

To really make this idea precise requires the machinery of higher category theory; we will be content to work with this construction in an informal way.

We now specialize this construction to the case of interest. Let  $\mathfrak{S}$  denote the category of spaces,  $\mathfrak{S}_p$  the category of *p*-finite spaces, and  $\mathfrak{S}_p^{\vee}$  the category  $\operatorname{Pro}(\mathfrak{S}_p)$  of pro-objects in  $\mathfrak{S}_p$ . We will refer to  $\mathfrak{S}_p^{\vee}$  as the category of *p*-profinite spaces.

There is a canonical functor  $G: \mathfrak{S}_p^{\vee} \to \mathfrak{S}$ , which carries a formal inverse limit " $\varprojlim C_{\alpha}$ " to the space holim  $C_{\alpha}$ . If we restrict to a suitable subcategory of  $\mathfrak{S}_p^{\vee}$  by imposing finiteness and connectivity conditions, then the functor G is fully faithful; its essential image being (a suitable subcategory of) the category of p-complete spaces. We will discuss this point in more detail in a future lecture.

The functor G has a left adjoint  $X \mapsto X^{\vee}$ , which we will refer to as the functor of p-profinite completion. The functor  $^{\vee}$  carries a topological space X to the formal inverse limit  $X^{\vee} = \text{``lim } X_{\alpha}\text{''}$ , where  $X_{\alpha}$  ranges over all p-finite spaces equipped with a map to X. If X is itself p-finite, then we can identify this inverse limit with X itself.

**Definition 6.** Let X be a p-profinite space. We let  $H^n(X) = H^n(X; \mathbf{F}_p)$  denote the set of homotopy classes of maps from X into an Eilenberg-MacLane space  $K(\mathbf{F}_p, n)$  in the p-profinite category  $\mathfrak{S}_p^{\vee}$ .

Since  $K(\mathbf{F}_p, n)$  is p-finite, we see that

$$\mathrm{H}^n(\text{"lim }X_\alpha\text{"})\simeq \mathrm{lim }\mathrm{H}^n(X_\alpha).$$

It follows that for any p-profinite space X, the cohomology  $H^*(X) \simeq \bigoplus_n H^n(X)$  is a filtere colimit of the cohomology rings of a collection of p-finite spaces, and therefore inherits the structure of an unstable algebra over the Steenrod algebra.

**Remark 7.** If X is a topological space, then the cohomology  $H^*(X; \mathbf{F}_p)$  (in the usual sense) can be identified with the cohomology  $H^*(X^{\vee})$  of the p-profinite completion of X, defined as in Definition 6.

The process of extracting cohomology does *not* generally commute with the inverse limit functor  $G: \mathfrak{S}_p^{\vee} \to \mathfrak{S}$ , unless we make suitable finiteness assumptions.

We now discuss the existence of mapping objects in the p-profinite category.

**Proposition 8.** Let X be a p-profinite space, and let V be a finite dimensional vector space over  $\mathbf{F}_p$ . Then there exists a p-profinite space  $X^{BV}$  equipped with an evaluation map  $X^{BV} \times BV \to X$  with the following universal property: for any p-profinite space Y, the induced map

$$\theta: \operatorname{Map}(Y, X^{BV}) \to \operatorname{Map}(Y \times BV, X)$$

is a weak homotopy equivalence.

*Proof.* If  $X = "\varprojlim X_{\alpha}"$ , then we can take  $X^{BV} = "\varprojlim X_{\alpha}^{BV}"$  (here we are using the fact that each  $X_{\alpha}^{BV}$  is again p-finite). We claim tht  $X^{BV}$  has the appropriate universal property. For any p-profinite space Y, we can identify  $\theta$  with a map

$$\operatorname{holim} \operatorname{Map}(Y, X_{\alpha}^{BV}) \simeq \operatorname{Map}(Y, X^{BV}) \to \operatorname{Map}(Y \times BV, X) \simeq \operatorname{holim} \operatorname{Map}(Y \times BV, X_{\alpha}).$$

It will therefore suffice to prove the result after replacing X by  $X_{\alpha}$ , so we may assume that X is p-finite. Let  $Y = \text{``lim } Y_{\beta}$ ''. Then the map  $\theta$  can be identified with

$$\operatorname{hocolim} \operatorname{Map}(Y_{\beta}, X^{BV}) \simeq \operatorname{Map}(Y, X^{BV}) \to \operatorname{Map}(Y \times BV, X) \simeq \operatorname{hocolim} \operatorname{Map}(Y_{\beta} \times BV, X),$$

where the last equivalence follows from the observation that

$$Y \times BV \simeq$$
 "lim  $Y_{\beta} \times BV$ "

is a product for Y and BV in the p-profinite category. We may therefore assume that Y is p-finite as well, in which case the result is obvious.

**Remark 9.** Proposition 9 remains valid if we replace BV by an arbitrary p-finite space. However, it is not valid if BV is a general p-profinite space; the p-profinite category  $\mathfrak{S}_p^{\vee}$  does not have internal mapping objects in general.

**Remark 10.** Let  $X = \lim_{\longleftarrow} X_{\alpha}$  and  $Y = \lim_{\longleftarrow} Y_{\beta}$  be p-profinite spaces. Then  $\lim_{\longleftarrow} X_{\alpha} \times Y_{\beta}$  is a product for X and Y in the category of p-profinite spaces. Applying the Kunneth theorem to the p-finite spaces  $X_{\alpha}$  and  $Y_{\beta}$ , we deduce

$$\mathrm{H}^*(X\times Y)\simeq \lim_{\alpha}\mathrm{H}^*(X_{\alpha}\times Y_{\beta})\simeq \lim_{\alpha}\mathrm{H}^*X_{\alpha}\otimes \mathrm{H}^*Y_{\beta}\simeq \mathrm{H}^*X\otimes \mathrm{H}^*Y.$$

Let us now assume that p=2. Let X be a p-profinite space. The evaluation map  $X^{BV}\times BV\to X$  induces a map on cohomology

$$H^* X \to H^*(X^{BV} \times BV) \simeq H^*(X^{BV}) \otimes H^*(BV),$$

which is adjoint to a map  $\psi: T_V H^*(X) \to H^*(X^{BV})$ .

**Theorem 11.** The map  $\psi$  is an isomorphism, for every 2-profinite space X.

*Proof.* The proof when X is 2-finite was given in the previous lecture. In general, write  $X = \lim_{n \to \infty} X_{\alpha}$ . Then we have

$$T_{V} \operatorname{H}^{*}(X) \simeq T_{V} \varinjlim \operatorname{H}^{*}(X_{\alpha})$$

$$\simeq \varinjlim \operatorname{H}^{*}(X_{\alpha}^{BV})$$

$$\simeq \varinjlim \operatorname{H}^{*}(X_{\alpha}^{BV}).$$

Using this result, we get a measure of exactly how the  $\psi$  might fail to be an isomorphism when we work in the usual category of spaces. For any space X, we have

$$T_V \operatorname{H}^*(X) \simeq T_V \operatorname{H}^*(X^{\vee}) \simeq \operatorname{H}^*(X^{\vee})^{BV} \to \operatorname{H}^*(X^{BV})^{\vee}.$$

In other words, the failure of  $T_V$  to compute the cohomology of mapping spaces is measured by the failure of the formation of mapping spaces to commute with profinite completion.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## p-adic Homotopy Theory (Lecture 27)

In this lecture we will continue to study the category  $\mathfrak{S}_p^{\vee}$  of p-profinite spaces, where p is a prime number. Our main goal is to connect  $\mathfrak{S}_p^{\vee}$  with the category of  $E_{\infty}$ -algebras over the field  $\overline{\mathbf{F}}_p$ , following the ideas of Dwyer, Hopkins, and Mandell.

We begin with a brief review of rational homotopy theory. For any topological space X, Sullivan showed how to construct a model for the rational cochain complex  $C^*(X; \mathbf{Q})$  which admits the structure of a differential graded algebra over  $\mathbf{Q}$ . The work of Quillen and Sullivan shows that the differential graded algebra  $C^*(X; \mathbf{Q})$  completely encodes the "rational" structure of the space X. For example, if X is a simply connected space whose homology groups  $H_i(X; \mathbf{Z})$  are finitely generated, then the space  $X_{\mathbf{Q}} = \operatorname{Map}(C^*(X; \mathbf{Q}), \mathbf{Q})$  is a rationalization of X: that is, there is a map  $X \to X_{\mathbf{Q}}$  which induces an isomorphism on rational homology. Here the mapping space  $\operatorname{Map}(C^*(X; \mathbf{Q}), \mathbf{Q})$  is computed in the homotopy theory of differential graded algebras over  $\mathbf{Q}$ .

Our goal is to establish an analogue of this result, where we replace the field  $\mathbf{Q}$  by a field  $\mathbf{F}_p$  of characteristic p. In this case, we cannot generally choose a model for  $C^*(X; \mathbf{F}_p)$  by a differential graded algebra (this is the origin of the existence of Steenrod operations). However, we can still view  $C^*(X; \mathbf{F}_p)$  as an  $E_{\infty}$ -algebra, and ask to what extent this  $E_{\infty}$ -algebra determines the homotopy type of X. We first observe that  $C^*(X; \mathbf{F}_p)$  depends only on the p-profinite completion of X. For any p-profinite space  $Y = \lim_{X \to \infty} T_{\infty}$ , we can define  $T_{\infty}$  define  $T_{\infty}$  induce a map of  $T_{\infty}$ -algebras

$$\theta: C^*(Y; \mathbf{F}_n) \simeq \lim_{n \to \infty} C^*(Y_n; \mathbf{F}_n) \to C^*(X; \mathbf{F}_n).$$

Since the Eilenberg-MacLane spaces  $K(\mathbf{F}_p, n)$  are p-finite and represent the functor  $X \mapsto \mathrm{H}^n(X; \mathbf{F}_p)$ , we deduce that  $\theta$  is an isomorphism on cohomology.

Let k be any field of characteristic p. Then, for every p-profinite space  $Y = \text{``lim } Y_{\Omega}$ ", we define

$$C^*(Y;k) = C^*(Y; \mathbf{F}_n) \otimes_{\mathbf{F}_n} k \simeq \lim_{n \to \infty} C^*(Y_n; k).$$

Warning 1. If Y is the p-profinite completion of a space X, then we again have a canonical map of  $E_{\infty}$ algebras

$$C^*(Y;k) \to C^*(X;k),$$

but this map is generally not an isomorphism on cohomology, since the Eilenberg-MacLane spaces K(k, n) are generally not p-finite.

Our goal is to prove the following:

**Theorem 2.** Let k be an algebraically closed field of characteristic p. The functor

$$X \mapsto C^*(X;k)$$

induces a fully faithful embedding from the homotopy theory of p-profinite spaces to the homotopy theory of  $E_{\infty}$ -algebras over k.

We first need the following lemma:

**Lemma 3.** The functor F defined by the formula

$$X \mapsto C^*(X;k)$$

carries homotopy limits of p-profinite spaces to homotopy colimits of  $E_{\infty}$ -algebras over k.

*Proof.* By general nonsense, it will suffice to prove that F carries filtered limits to filtered colimits and finite limits to finite colimits.

For any category  $\mathcal{C}$ , the category  $\operatorname{Pro}(\mathcal{C})$  can be characterized by the following universal property: it is freely generated by  $\mathcal{C}$  under filtered limits. In other words,  $\operatorname{Pro}(\mathcal{C})$  admits filtered limits, and if  $\mathcal{D}$  is any other category which admits filtered limits, then functors from  $\mathcal{C}$  to  $\mathcal{D}$  extend uniquely (up to equivalence) to functors from  $\operatorname{Pro}(\mathcal{C})$  to  $\mathcal{D}$  which preserve filtered limits. By construction, the functor F is the unique extension of the functor  $X \mapsto C^*(X; \mathbf{F}_p)$  on p-finite spaces which carries filtered limits to filtered colimits.

To show that F preserves finite limits to finite colimits, it will suffice to show that F carries final objects to initial objects, and homotopy pullback diagrams to homotopy pushout diagrams. The first assertion is evident:  $F(*) \simeq k$  is the initial  $E_{\infty}$ -algebra over k. To handle the case of pullbacks, we note that every homotopy pullback square

$$X' \longrightarrow X$$

$$\downarrow \qquad \qquad \downarrow$$

$$Y' \longrightarrow Y$$

of p-profinite spaces is a filtered limit of homotopy pullback squares between p-finite spaces. We may therefore assume that the diagram consists of p-finite spaces, in which case we proved earlier that the diagram

$$C^*(X'; \mathbf{F}_p) \longleftarrow C^*(X; \mathbf{F}_p)$$

$$\uparrow \qquad \qquad \uparrow$$

$$C^*(Y'; \mathbf{F}_p) \longleftarrow C^*(Y; \mathbf{F}_p)$$

is a homotopy pushout square of  $E_{\infty}$ -algebras over  $\mathbf{F}_p$ . The desired result now follows by tensoring over  $\mathbf{F}_p$  with k.

**Lemma 4.** Let  $\mathcal{K}$  be a collection of p-profinite spaces. Suppose that  $\mathcal{K}$  contains every Eilenberg-MacLane space  $K(\mathbf{F}_p, n)$  and is closed under the formation of homotopy limits. Then  $\mathcal{K}$  contains all p-profinite spaces  $\mathcal{K}$ 

*Proof.* Every p-profinite space X is a filtered homotopy limit of p-finite spaces. We may therefore assume that X is finite. In this case, X admits a finite filtration

$$X \simeq X_m \to X_{m-1} \to \ldots \to X_0 \simeq *$$

where, for each i, we have a homotopy pullback diagram

$$X_{i+1} \longrightarrow *$$

$$\downarrow \qquad \qquad \downarrow$$

$$X_{i} \longrightarrow K(\mathbf{F}_{p}, n_{i}).$$

It follows by induction on i that each  $X_i$  belongs to  $\mathfrak{K}$ .

We now turn to the proof of Theorem 2. Fix a p-profinite space Y. For every p-profinite space X, we have a canonical map

$$\theta_X : \operatorname{Map}(Y, X) \to \operatorname{Map}_k(C^*(X; k), C^*(Y; k)).$$

Let  $\mathcal{K}$  denote the collection of all p-profinite spaces X for which  $\theta_X$  is a homotopy equivalence. Lemma 3 implies that both sides above are compatible with the formation of homotopy limits in X, so  $\mathcal{K}$  is closed under the formation of homotopy limits. It will therefore suffice to show that every Eilenberg-MacLane space  $K(\mathbf{F}_p, n)$  belongs to  $\mathcal{K}$ .

For each i, the map  $\theta_{K(\mathbf{F}_n,n)}$  induces a map

$$\mathrm{H}^{n-i}(Y;\mathbf{F}_p) \simeq \pi_i \operatorname{Map}(Y,K(\mathbf{F}_p,n)) \to \pi_i \operatorname{Map}_k(C^*(K(\mathbf{F}_p,n);k),C^*(Y;k)) \simeq \pi_i \operatorname{Map}_{\mathbf{F}_p}(C^*(K(\mathbf{F}_p,n);\mathbf{F}_p),C^*(Y;k));$$

we wish to show that these maps are isomorphisms.

We now specialize to the case p=2, where we have described the cochain complex  $C^*(K(\mathbf{F}_p, n); \mathbf{F}_p)$  as an  $E_{\infty}$ -algebra over  $\mathbf{F}_p$ : namely, we have a pushout diagram of  $E_{\infty}$ -algebras

$$\begin{array}{ccc}
\mathfrak{F}(n) & \xrightarrow{u} & \mathfrak{F}(n) \\
\downarrow & & \downarrow \\
\mathbf{F}_{p} & \xrightarrow{} & C^{*}(K(\mathbf{F}_{p}, n); \mathbf{F}_{p})
\end{array}$$

where the map u classifies the cohomology operation  $id - Sq^0$ . It follows that we have a long exact sequence of homotopy groups

$$\dots \to \mathrm{H}^{n-i-1}(Y;k) \to \pi_i \operatorname{Map}_{\mathbf{F}_p}(C^*(K(\mathbf{F}_p,n);\mathbf{F}_p),C^*(Y;k)) \to \mathrm{H}^{n-i}(Y;k) \overset{\mathrm{id}-\operatorname{Sq}^0}{\to} \mathrm{H}^{n-i}(Y;k) \to \dots$$

To compute the homotopy groups of  $\operatorname{Map}_{\mathbf{F}_p}(C^*(K(\mathbf{F}_p,n);\mathbf{F}_p),C^*(Y;k))$ , we need to understand the cohomology ring  $\operatorname{H}^*(Y;k)$  as an algebra over the big Steenrod algebra  $\mathcal{A}^{\operatorname{Big}}$ . We observe that

$$\mathrm{H}^*(Y;k) \simeq \mathrm{H}^*(Y;\mathbf{F}_n) \otimes_{\mathbf{F}_n} k.$$

The operation  $\operatorname{Sq}^0$  acts by the identity on the first factor, and by the Frobenius map  $x \mapsto x^p$  on the field k. Since k is algebraically closed, we have an Artin-Schreier sequence

$$0 \to \mathbf{F}_n \to k \xrightarrow{v} k \to 0$$

where v is given by  $v(x) = x - x^p$ . It follows that the operation  $\mathrm{id} - \mathrm{Sq}^0$  on  $\mathrm{H}^*(Y;k)$  is surjective, with kernel  $\mathrm{H}^*(Y;\mathbf{F}_p)$ . Thus the long exact sequence above yields a sequence of isomorphisms

$$\pi_i \operatorname{Map}_{\mathbf{F}_n}(C^*(K(\mathbf{F}_p, n); \mathbf{F}_p)C^*(Y; k)) \simeq \operatorname{H}^{n-i}(Y; \mathbf{F}_p)$$

as desired.

**Remark 5.** The proof of Theorem 2 does not require that k is algebraically closed, only that k admits no Artin-Schreier extensions (that is, that any equation  $x - x^p = \lambda$  admits a solution in k). Equivalently, it requires that the absolute Galois group  $\operatorname{Gal}(\overline{k}/k)$  have vanishing mod-p cohomology.

**Remark 6.** Theorem 2 is false for a general field k of characteristic p; for example, it fails when  $k = \mathbf{F}_p$ . However, we can obtain a more general statement as follows. Suppose that X is a p-profinite sheaf of spaces on the étale topos of Spec k; in other words, that X is a p-profinite space equipped with a suitably continuous action  $\sigma$  of the Galois group  $\operatorname{Gal}(\overline{k}/k)$ . In this case, we get a Galois action on the cochain complex

$$C^*(X; \overline{k}).$$

Using descent theory, we can extract from this an  $E_{\infty}$ -algebra of Galois invariants  $C^*_{\sigma}(X;k)$ , which we can regard as a  $\sigma$ -twisted version of the usual cochain complex  $C^*(X;k)$  (these cochain complexes can be identified in the case where the action of  $\sigma$  is trivial). The construction

$$(X,\sigma)\mapsto C^*_\sigma(X;k)$$

determines a functor from p-profinite sheaves on Spec k to the category of  $E_{\infty}$ -algebras over k, and this functor is again fully faithful.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Atomicity (Lecture 28)

Let V be a finite dimensional vector space over  $\mathbf{F}_2$ , and let  $T_V$  denote Lannes's T-functor. In previous lectures we have established two very important properties of  $T_V$ :

- The functor  $T_V$  is exact.
- $\bullet$  For every 2-profinite space X, there is a canonical isomorphism

$$T_V \operatorname{H}^* X \simeq \operatorname{H}^* X^{BV}$$
.

Our goal in this lecture is to deduce a conceptual consequence of these facts, which makes no mention of modules over the Steenrod algebra.

**Definition 1.** Let  $\mathcal{C}$  be a (topological) category which admits finite (homotopy) limits and colimits. We will say that an object  $K \in \mathcal{C}$  is *atomic* if the following conditions are satisfied:

(a) For every  $X \in \mathcal{C}$ , there exists an object  $X^K \in \mathcal{C}$  and an evaluation map  $e: X^K \times K \to X$  with the following universal property: for every  $Y \in \mathcal{C}$ , composition with e induces a homotopy equivalence

$$\operatorname{Map}(Y, X^K) \to \operatorname{Map}(Y \times K, X).$$

(b) The functor  $X \mapsto X^K$  preserves finite (homotopy) colimits.

**Example 2.** Let  $\mathcal{C}$  be the category of spaces. Then the point K = \* is an atomic object of  $\mathcal{C}$ .

We will be primarily interested in the case where  $\mathcal{C} = \mathfrak{S}_p^{\vee}$  is the category of p-profinite spaces. We note that  $\mathcal{C}$  admits homotopy colimits. This is perhaps not completely obvious, since the collection of p-finite spaces is not closed under homotopy colimits. For example, given a diagram of p-finite spaces

$$X \leftarrow Y \rightarrow X'$$

the (homotopy) pushout of this diagram in  $\mathfrak{S}_p^\vee$  is obtained as the *p*-profinite completion of the analogous homotopy pushout  $X\coprod_Y X'$  in the category of spaces.

Suppose that K is a p-finite space; we wish to study the condition that K be atomic. Condition (a) is automatic. Condition (b) can be divided into two assertions:

- $(b_0)$  The functor  $X \mapsto X^K$  preserves initial objects. This is true if and only if K is nonempty.
- $(b_1)$  The functor  $X \mapsto X^K$  preseves homotopy pushouts.

Condition  $(b_1)$  implies, for example, that for every pair of p-profinite spaces X and Y, we have  $(X \coprod Y)^K \simeq X^K \coprod Y^K$ ; in other words, every map from K to a disjoint union must factor through one of the summands. This is equivalent to the assertion that K is connected. A priori, the condition of atomicity is much stronger: it implies, for example, that K cannot be written nontrivially as a homotopy pushout of p-profinite spaces. Nevertheless, we have the following result:

**Theorem 3.** Let K be a connected p-finite space. Then K is an atomic object of the p-profinite category.

We will prove Theorem 3 in the next lecture. For now, we will be content to study the special case where K = BV, where V is a finite dimensional vector space over  $\mathbf{F}_p$  (and the prime p is equal to 2). In this case, we need to show:

**Proposition 4.** Let V be a finite dimensional vector space over  $\mathbf{F}_p$ , and let

$$\begin{array}{ccc} X \longrightarrow X' \\ \downarrow & \downarrow \\ Y \longrightarrow Y' \end{array}$$

be a homotopy pushout diagram of p-profinite spaces. Then the induced diagram

$$X^{BV} \longrightarrow X'^{BV}$$

$$\downarrow \qquad \qquad \downarrow$$

$$Y^{BV} \longrightarrow Y'^{BV}$$

is also a homotopy pushout diagram.

**Remark 5.** Let  $f: X \to Y$  be a map of p-profinite spaces. Then f is an equivalence if and only if induces an isomorphism  $H^*(Y) \to H^*(X)$ . The "only if" direction is obvious. For the converse, let us suppose that f induces an isomorphism of cohomology. We will show that f induces a weak homotopy equivalence

$$\phi_Z : \operatorname{Map}(Y, Z) \to \operatorname{Map}(X, Z)$$

for every p-profinite space Z. We may immediately reduce to the case where Z is p-finite (since the class of weak homotopy equivalences is stable under homotopy limits). In this case, we have a finite filtration

$$Z \simeq Z_m \to Z_{m-1} \to \ldots \to Z_0 \simeq *$$

by principal fibrations with fiber  $K(\mathbf{F}_p, n_i)$ ; we will show that  $\phi_{Z_i}$  is a weak homotopy equivalence using induction on i. We have a homotopy pullback diagram

$$Z_{i+1} \xrightarrow{\qquad \qquad *} *$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$Z_{i} \longrightarrow K(\mathbf{F}_{p}, n_{i} + 1).$$

Consequently, to show that  $\phi_{Z_{i+1}}$  is a homotopy equivalence, it will suffice to show that  $\phi_*$ ,  $\phi_{Z_i}$ , and  $\phi_{K(\mathbf{F}_p,n_i+1)}$  are weak homotopy equivalences. The first claim is obvious, the second follows from the inductive hypothesis, and the third follows from our hypothesis on f since

$$\pi_k\operatorname{Map}(Y,K(\mathbf{F}_p,n_i+1))\simeq\operatorname{H}^{n_i+1-k}(Y)\simeq\operatorname{H}^{n_i+1-k}(X)\simeq\pi_k\operatorname{Map}(X,K(\mathbf{F}_p,n_i+1)).$$

Proof of Proposition 4. Let Z denote a homotopy pushout of  $Y^{BV}$  and  $X'^{BV}$  over  $X^{BV}$ . The evaluation maps  $Y^{BV} \times BV \to Y$  and  $X'^{BV} \times BV \to X'$  glue together to give a map  $Z \times BV \to Y'$ . We therefore have a map of homotopy pushout diagrams

$$X^{BV} \times BV \longrightarrow X'^{BV} \times BV \qquad X \longrightarrow X'$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$Y^{BV} \times BV \longrightarrow Z \times BV \qquad Y \longrightarrow Y',$$

which induces a map of long exact sequences

Since  $T_V$  is exact, this diagram is adjoint to another map of long exact sequences

Using the five-lemma, we deduce that the map  $T_V \operatorname{H}^* Y' \to \operatorname{H}^* Z$  is an isomorphism. This map fits into a commutative diagram

where  $\alpha$  is induced by the map of p-profinite space  $f: Z \to {Y'}^{BV}$ . Using the two-out-of-three property, we deduce that  $\alpha$  is an isomorphism. It follows from Remark 5 that f is an equivalence of p-profinite spaces, as desired.

We now wish to prove the atomicity of a larger class of p-finite spaces. First, we reformulate the definition of atomicity. First, we introduce a bit of notation. For every p-finite space K, we let  $\mathfrak{S}_{p,/K}^{\vee}$  denote the category of p-profinite spaces over K, so that an object of  $\mathfrak{S}_{p,/K}^{\vee}$  is a map  $X \to K$  in the p-profinite category. Given a map  $q: K \to K'$ , we have a pullback functor  $q^*: \mathfrak{S}_{p,/K'}^{\vee} \to \mathfrak{S}_{p,/K}^{\vee}$ , which is given by forming the homotopy pullback

$$X \mapsto X \times_K K'$$
.

This functor has a right adjoint, which we will denote by  $q_*$ . In the case where K' is a point,  $q_*$  assigns to a map  $f: X \to K$  the p-profinite space of sections of f (more precisely,  $q_*X$  has the following universal property: for every p-profinite space Y, we have

$$\operatorname{Map}(Y, q_*X) \simeq \operatorname{Map}(Y \times K, X) \times_{\operatorname{Map}(Y \times K, K)} \{\pi_2\},\$$

where  $\pi_2$  denotes the projection onto the second factor. In particular, if X is a product  $X_0 \times K$ , then  $q_*X$  is equivalent to the mapping space  $X_0^K$ .

**Proposition 6.** Let K be a p-finite space. The following conditions are equivalent:

- (1) K is an atomic object of the p-profinite category.
- (2) Let  $q: K \to *$  denote the projection. Then the functor  $q_*: \mathfrak{S}_{p,/K}^{\vee} \to \mathfrak{S}_p^{\vee}$  preserves finite homotopy colimits.

*Proof.* By definition, K is atomic if and only if the composite functor  $q_*q^*$  preserves finite homotopy colimits. Since  $q^*$  preserves finite homotopy colimits (being a left adjoint), the implication  $(2) \Rightarrow (1)$  is obvious. For the converse, we observe that we have a natural equivalence

$$q_*X \simeq X^K \times_{K^K} \{ \mathrm{id}_K \},$$

and the functor  $Y \mapsto Y \times_{K^K} \{ id_K \}$  preserves all homotopy colimits.

## Corollary 7. Suppose given a fiber sequence

$$F \xrightarrow{f} E \xrightarrow{g} B$$

of connected p-finite spaces. If F and B are atomic (when regarded as p-profinite spaces), then E is atomic (when regarded as a p-profinite space).

*Proof.* Let q denote the projection from B to a point. We wish to show that the functor  $(q \circ g)_* = q_* \circ g_*$  preserves finite homotopy colimits. Since B is atomic,  $q_*$  preserves finite homotopy colimits. It will therefore suffice to show that  $g_*$  preserves finite homotopy colimits. For this, it suffices to show that  $i^*g_*$  preserves finite homotopy colimits, where i denotes the inclusion of any point b into B. We have an equivalence

$$i^*g_* \simeq g'_*f^*$$

where g' denotes the projection  $E \times_B \{b\} \simeq F \to \{b\}$ . The functor  $f^*$  preserves all homotopy colimits (since it is a left adjoint), and  $g'_*$  preserves finite homotopy colimits since F is assumed to be atomic.

Corollary 8. Let G be a finite p-group. Then the classifying space BG is an atomic object in the p-profinite category.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Atomicity of Connected p-Finite Spaces (Lecture 29)

In this lecture, we will show that every connected p-finite space K is an atomic object of the category of p-profinite spaces. We begin with the following result, which is a soft version of the convergence of the homology spectral sequence for a cosimplicial space:

**Proposition 1.** Consider the functor F:

$$X \mapsto C^*X$$

from the category of p-profinite spaces  $\mathfrak{S}_p^{\vee}$  to the category of complexes of  $\mathbf{F}_p$ -vector spaces. Then F carries totalizations (of cosimplicial p-profinite spaces) to geometric realizations (of simplicial objects in the category of complexes).

*Proof.* The functor F factors as a composition  $F'' \circ F'$ , where:

• The functor F' is given by the formula

$$X \mapsto C^*X$$
.

but  $C^*X$  is regarded as an  $E_{\infty}$ -algebra over  $\mathbf{F}_n$ .

• The functor F'' is the forgetful functor from  $E_{\infty}$ -algebras over  $\mathbf{F}_p$  to complexes of  $\mathbf{F}_p$ -vector spaces.

We have shown that the functor F' carries arbitrary homotopy limits of p-profinite spaces to homotopy colimits of  $E_{\infty}$ -algebras; in particular, it carries totalizations to geometric realizations. It now suffices to observe that F'' preserves geometric realizations of simplicial objects.

Remark 2. In concrete terms, the statement that F'' preserves geometric realizations amounts to the following observation. Let  $A_{\bullet}$  be a simplicial object in the category of  $E_{\infty}$ -algebras over  $\mathbf{F}_p$ , and let  $|A_{\bullet}|$  be the geometric realization of  $A_{\bullet}$  as a complex of  $\mathbf{F}_p$ -vector spaces. Then  $|A_{\bullet}|$  inherits the structure of an  $E_{\infty}$ -algebra. For example, the multiplication on  $|A_{\bullet}|$  arises in the following way: the tensor product  $|A_{\bullet}| \otimes |A_{\bullet}|$  can be identified with the homotopy colimit of the bisimplicial complex  $B_{\bullet,\bullet}$  given by the formula  $B_{m,n} = A_m \otimes A_n$ . This homotopy colimit can be computed as the geometric realization of the diagonal simplicial object  $B_{\bullet}: [n] \mapsto B_{n,n}$ , and we have a map

$$|B_{\bullet}| \to |A_{\bullet}|$$

which is induced by the maps  $B_n = B_{n,n} = A_n \otimes A_n \to A_n$  given by the multiplication on  $A_n$ .

**Theorem 3.** Let  $\mathfrak{S}_p^{\vee}$  denote the category of p-profinite spaces, and  $c\mathfrak{S}_p^{\vee}$  the category of cosimplicial p-profinite spaces. Then the totalization functor

$$c\,\mathfrak{S}_p^\vee\to\mathfrak{S}_p^\vee$$

commutes with homotopy pushouts.

*Proof.* Suppose given a homotopy pushout diagram

$$X^{\bullet} \longrightarrow X'^{\bullet}$$

$$\downarrow \qquad \qquad \downarrow$$

$$Y^{\bullet} \longrightarrow Y'^{\bullet}$$

of p-profinite spaces. We wish to show that the associated diagram

$$Tot(X^{\bullet}) \longrightarrow Tot(X'^{\bullet})$$

$$\downarrow \qquad \qquad \downarrow$$

$$Tot(Y^{\bullet}) \longrightarrow Tot(Y'^{\bullet})$$

is again a homotopy pushout diagram. In other words, we wish to show that the canonical map

$$\operatorname{Tot}(X'^{\bullet}) \coprod_{\operatorname{Tot}(X^{\bullet})} \operatorname{Tot}(Y^{\bullet}) \to \operatorname{Tot}(Y'^{\bullet})$$

is an equivalence of p-profinite spaces. As we saw in the last lecture, it will suffice to show that this map induces an isomorphism on cohomology. In other words, it suffices to show that the induced map

$$C^*(\mathrm{Tot}(Y'^{\bullet})) \to C^*(\mathrm{Tot}(X'^{\bullet}) \coprod_{\mathrm{Tot}(X^{\bullet})} \mathrm{Tot}(Y^{\bullet}))$$

is a quasi-isomorphism. By excision, the right hand side can be identified with the homotopy fiber product

$$(C^* \operatorname{Tot} X'^{\bullet}) \times_{C^* \operatorname{Tot} X^{\bullet}} (C^* \operatorname{Tot} Y^{\bullet}).$$

In other words, we must show that the diagram

$$C^* \operatorname{Tot}(X^{\bullet}) \longleftarrow C^* \operatorname{Tot}(X'^{\bullet})$$

$$\uparrow \qquad \qquad \uparrow \qquad \qquad \uparrow$$

$$C^* \operatorname{Tot}(Y^{\bullet}) \longleftarrow C^* \operatorname{Tot}(Y'^{\bullet})$$

is a homotopy pullback square (in the category of complexes of  $\mathbf{F}_p$ -vector spaces). Using Proposition 1 we can rewrite this square as

$$|C^*X^{\bullet}| \longleftarrow |C^*X'^{\bullet}|$$

$$\uparrow \qquad \qquad \uparrow$$

$$|C^*Y^{\bullet}| \longleftarrow |C^*Y'^{\bullet}|.$$

The homotopy theory of complexes of  $\mathbf{F}_p$ -vector spaces is *stable*: that is, homotopy pullback squares are the same as homotopy pushout squares. It will therefore suffice to show that the diagram above is a homotopy pushout square. Since the collection of homotopy pushout squares is stable under homotopy colimits (and in particular under geometric realizations), we are reduced to showing that each diagram

$$C^*X^n \longleftarrow C^*X'^n$$

$$\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$$

is a homotopy pushout square. Using stability again, we need only show that this diagram is a homotopy pullback square. This follows by excision from the assumption that

$$X^{n} \longrightarrow X'^{n}$$

$$\downarrow \qquad \qquad \downarrow$$

$$Y^{n} \longrightarrow Y'^{n}$$

is a homotopy pushout square of p-profinite spaces.

**Remark 4.** The same argument can be used to show that the formation of filtered limits of p-profinite spaces preserves homotopy pushout squares.

Corollary 5. Let  $K_{\bullet}$  be a simplicial object in the category of p-finite spaces. Suppose that each  $K_n$  is atomic in the p-profinite category, and that the geometric realization  $K = |K_{\bullet}|$  is again p-finite. Then K is also atomic in the p-profinite category.

*Proof.* Let X be any p-profinite space. Since each  $K_n$  is atomic, we can construct a mapping object  $X^{K_n}$ . The universal property of  $X^{K_n}$  shows that it depends on  $K_n$  in a contravariantly functorial manner, so that  $F(X) = X^{K_{\bullet}}$  is a cosimplicial object in the category of p-profinite spaces, and the totalization of this cosimplicial object can be identified with  $X^K$ . Consequently, the functor

$$X \mapsto X^K$$

can be factored as a composition

$$\mathfrak{S}_p^{\vee} \xrightarrow{F} c \, \mathfrak{S}_p^{\vee} \xrightarrow{\mathrm{Tot}} \mathfrak{S}_p^{\vee}.$$

Since each  $K_n$  is atomic, the functor F preserves homotopy pushouts. Theorem 3 implies that Tot preserves homotopy pushouts as well, so the functor  $X \mapsto X^K$  preserves homotopy pushouts. Since K is clearly nonempty, we deduce that K is atomic.

**Corollary 6.** Let G be a finite p-group and  $n \ge 1$  an integer; assume that G is abelian if n > 1. Then the Eilenberg-MacLane space K(G, n) is an atomic object of the p-profinite category.

*Proof.* The case n=1 was handled in the previous lecture, using Lannes' T-functor. The proof in general goes by induction on n. Choose a fibration  $E_0 \to K(G,n)$ , where  $E_0$  is contractible, and consider the associated simplicial object defined by the formula

$$E_k = E_0 \times_{K(G,n)} E_0 \times \ldots \times_{K(G,n)} E_0$$

(where the factor  $E_0$  appears (k+1)-times). Then  $E_{\bullet}$  is a simplicial object whose geometric realization  $|E_{\bullet}|$  can be identified with K(G, n). Moreover, each  $E_k$  is homotopy equivalent to the Eilenberg-MacLane space  $K(G^k, n-1)$ . The inductive hypothesis implies that each  $E_k$  is atomic. Using Corollary 5, we conclude that  $|E_{\bullet}| \simeq K(G, n)$  is atomic as well.

**Theorem 7.** Let X be a connected p-finite space. Then X is an atomic object of the p-profinite category.

*Proof.* The space X admits a Postnikov tower

$$X \simeq X_m \to X_{m-1} \to \ldots \to X_0 \simeq *,$$

where

$$\pi_k X_i = \begin{cases} \pi_k X & \text{if k i i} \\ 0 & \text{otherwise.} \end{cases}$$

We will show by induction that each  $X_i$  is atomic. For each i, we have a fiber sequence

$$K(\pi_i X, i) \to X_i \to X_{i-1}$$

of connected p-finite spaces. Consequently, to show that  $X_i$  is atomic, it will suffice to show that  $X_{i-1}$  and  $K(\pi_i X, i)$  are atomic. The first follows from the inductive hypothesis and the second from Corollary 6.  $\square$ 

We conclude this lecture with a complement to Theorem 7, which indicates the strength of the atomicity condition.

**Proposition 8.** Let X be an atomic object in the category  $\mathfrak{S}$  of spaces. Then X is (weakly) contractible.

*Proof.* By assumption  $\operatorname{Map}(X, \bullet)$  commutes with finite colimits. In particular,  $\operatorname{Map}(X, \emptyset)$  is empty; this implies that X is nonempty. Since  $\operatorname{Map}(X, \bullet)$  commutes with disjoint unions, we conclude that X is connected. Suppose (for a contradiction) that X is not weakly contractible.

Without loss of generality, we can assume that X is a CW complex. It can therefore be written as the homotopy colimit of its skeleta

$$\operatorname{sk}^0 X \to \operatorname{sk}^1 X \to \operatorname{sk}^2 X \to \dots$$

Let X' denote the mapping telescope for this sequence of maps, so that we have a canonical homotopy equivalence  $X' \simeq X$ . The telescope X' admits a decomposition

$$X_1' \coprod_{X_0'} X_2'$$

where:

- The space  $X'_0$  is the disjoint union of the spaces  $\operatorname{sk}^i X$ .
- The space  $X'_1$  is the disjoint union of the mapping cylinders for the inclusions  $\mathrm{sk}^i X \subseteq \mathrm{sk}^{i+1} X$ , where i is odd.
- The space  $X_2'$  is the disjoint union of the mapping cylinders for the inclusions  $\mathrm{sk}^i X \subseteq \mathrm{sk}^{i+1} X$ , where i is even.

Since X is atomic, the equivalence  $X \simeq X'$  factors (up to homotopy) through either  $X_1'$  or  $X_2'$ . Since X is connected, we this map factors through the mapping cylinder of the inclusion  $\operatorname{sk}^i X \subseteq \operatorname{sk}^{i+1} X$ , for some integer i. Consequently, we deduce that the identity map from X to itself factors up to homotopy through the finite dimensional spaces $k^{i+1} X$ .

We now prove, by induction descending induction on j, that the identity map  $\mathrm{id}_X$  factors (up to homotopy) through  $\mathrm{sk}^j X$ . The case j=i+1 follows from the above argument. For the inductive step, we use the homotopy pushout diagram

$$\coprod S^{j-1} \longrightarrow \operatorname{sk}^{j-1} X$$

$$\downarrow \qquad \qquad \downarrow$$

$$\coprod D^{j} \longrightarrow \operatorname{sk}^{j} X.$$

Since X is atomic, we conclude that  $\mathrm{id}_X$  factors (up to homotopy) either through  $\mathrm{sk}^{j-1}X$  or through  $\coprod D^j$ . Since X is connected, the latter possibility implies that  $\mathrm{id}_X$  factors up to homotopy through some disk  $D^j$ , which contradicts our assumption that X is not contractible. Therefore  $\mathrm{id}_X$  factors through  $\mathrm{sk}^{j-1}$ .

Applying the above argument repeatedly, we deduce that  $id_X$  factors through the  $sk^{-1}X = \emptyset$ . Since X is nonempty, we obtain a contradiction.

Where does the above argument go wrong if we work in the p-profinite category?

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Sullivan Conjecture (Lecture 30)

In this lecture we will combine some of our previous results to deduce a version of the Sullivan conjecture.

**Theorem 1.** Let X be a finite-dimensional CW complex,  $X^{\vee}$  its p-profinite completion, and K a connected p-profinite space. Then the diagonal map

$$X^{\vee} \to (X^{\vee})^K$$

is an equivalence of p-profinite spaces.

*Proof.* Let us say that a space X is good if  $X^{\vee} \to (X^{\vee})^K$  is an equivalence. Since p-profinite completion preserves homotopy pushout squares (being a left adjoint) and K is atomic in the p-profinite category, the collection of good spaces is stable under the formation of homotopy pushouts. We now show that every space X of finite dimension n is good, using induction on n. We have a homotopy pushout diagram

$$\coprod S^{n-1} \longrightarrow \operatorname{sk}^{n-1} X$$

$$\downarrow \qquad \qquad \downarrow$$

$$\coprod D^n \longrightarrow X.$$

The inductive hypothesis guarantees that  $\operatorname{sk}^{n-1}X$  and  $\coprod S^{n-1}$  are good. It will therefore suffice to show that  $\coprod D^n$  is good. But this coproduct is homotopy equivalent to a discrete topological space, which is obviously good.

**Corollary 2.** Let X be a finite dimensional CW complex, and K a connected p-profinite space. Then every map  $K \to X^{\vee}$  in the p-profinite category is homotopic to a constant map.

In the special case where K = BG, where G is a finite p-group, we can identify  $(X^{\vee})^K$  with the homotopy fixed point set  $(X^{\vee})^{hG}$ , where G acts trivially on X. There is a more general form of Theorem 1 where we do not assume that the action of G is trivial.

**Lemma 3.** Let G be a finite p-group, and let  $\mathfrak{S}_p^{\vee}(G)$  denote the category of p-profinite spaces with an action of G. Then the functor

$$\mathfrak{S}_p^{\vee}(G) \to \mathfrak{S}_p^{\vee}$$

$$X \mapsto X^{hG}$$

preserves finite homotopy colimits.

*Proof.* We can identify  $\mathfrak{S}_p^{\vee}(G)$  with  $\mathfrak{S}_{p,/BG}^{\vee}$ , and the formation of homotopy fixed points with the pushforward functor  $f_*$ , where  $f:BG\to *$  is the projection. The desired result now follows from the observation that BG is atomic.

**Theorem 4.** Let G be a finite p-group, X a finite-dimensional G-CW complex, and  $X^G$  the subcomplex of G-fixed points. Then the composite map

$$\phi: (X^G)^{\vee} \to (X^{hG})^{\vee} \to (X^{\vee})^{hG}$$

is a homotopy equivalence of p-profinite spaces.

*Proof.* The space X admits a filtration

$$X^G = Y_{-1} \subseteq Y_0 \subseteq \ldots \subseteq Y_n = X,$$

where  $Y_j$  denotes the union of  $X^G$  with the j-skeleton of X. We will prove by induction on j that the conclusion of the theorem is valid for  $Y_j$ . The case j = -1 follows from Theorem 1. In the general case, we have a homotopy pushout diagram

$$\coprod_{\alpha} S^{j-1} \times G/H_{\alpha} \longrightarrow Y_{j-1}$$

$$\downarrow \qquad \qquad \downarrow$$

$$\coprod_{\alpha} D^{j} \times G/H_{\alpha} \longrightarrow Y_{j},$$

where each  $H_{\alpha}$  is a proper subgroup of G. Since p-profinite completion and passage to homotopy fixed points with respect to G preserve homotopy pushout squares, we get a homotopy pushout square

$$((\coprod_{\alpha} S^{j-1} \times G/H_{\alpha})^{\vee})^{hG} \longrightarrow (Y_{j-1}^{\vee})^{hG}$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$((\coprod_{\alpha} D^{j} \times G/H_{\alpha})^{\vee})^{hG} \longrightarrow (Y_{j}^{\vee})^{hG}$$

of p-profinite spaces. By the inductive hypothesis, the upper right corner is equivalent to the p-profinite completion of  $X^G$ . It will therefore suffice to show that the p-profinite spaces in the left column are empty. We will show that  $Z = ((\coprod_{\alpha} S^{j-1} \times G/H_{\alpha})^{\vee})^{hG}$  is empty; the same argument will show that  $((\coprod_{\alpha} D^j \times G/H_{\alpha})^{\vee})^{hG}$ 

We will show that  $Z = ((\coprod_{\alpha} S^{j-1} \times G/H_{\alpha})^{\vee})^{hG}$  is empty; the same argument will show that  $((\coprod_{\alpha} D^{j} \times G/H_{\alpha})^{\vee})^{hG}$  is empty as well. The group G has only finitely many proper subgroups H. We can therefore decompose Z as a coproduct of spaces of the form

$$Z_H = \left( \left( \prod_{H_\alpha = H} S^{j-1} \times G/H \right)^{\vee} \right)^{hG}.$$

It will therefore suffice to show that each  $Z_H$  is empty. But  $Z_H$  can be identified with

$$((\coprod S^{j-1})^{\vee}\times G/H)^{hG}.$$

We therefore have a map from  $Z_H$  to the homotopy fixed set  $(G/H)^{hG}$ , which is empty because H is a proper subgroup of G.

**Remark 5.** We can formulate Theorem ?? as follows: the map  $\phi$  identifies the homotopy fixed set  $(X^{\vee})^{hG}$  with the p-profinite completion of the actual fixed set  $X^G$ .

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## p-adic Completion of Spaces (Lecture 31)

In this lecture, we will discuss the relationship between the category  $\mathfrak{S}_p^{\vee}$  of p-profinite spaces and the usual category  $\mathfrak{S}$  of spaces. As we have seen earlier, there is a pair of adjoint functors

$$\mathfrak{S} \xrightarrow{\bigvee} \mathfrak{S}_p^{\vee}$$
.

The composition

$$X\mapsto \lim X^\vee$$

is a functor from the category of spaces to itself. We will denote this functor by  $X \mapsto \widehat{X}$ . We think of this functor as "p-adically completing" the homotopy type of X. The following assertion makes this idea precise:

**Theorem 1.** Let X be a simply connected space, and assume that every homotopy group  $\pi_i X$  is finitely generated (as an abelian group). Then  $\widehat{X}$  is again simply connected, and the unit map  $X \to \widehat{X}$  induces isomorphisms

$$\pi_i X \otimes_{\mathbf{Z}} \mathbf{Z}_p \simeq \pi_i \widehat{X},$$

where  $\mathbf{Z}_p$  denotes the ring of p-adic integers.

We will reduce the proof of Theorem 1 to the following calculation:

**Lemma 2.** For each  $i \geq 0$ , the canonical map

$$H_i K(\mathbf{Z}, 1) \rightarrow \text{"lim } H_i K(\mathbf{Z}/p^k \mathbf{Z}, 1) \text{"}$$

is an isomorphism in the category of pro- $\mathbf{F}_p$ -vector spaces.

*Proof.* If  $i \leq 1$ , then the pro-system on the right is constant (and isomorphic to the  $H_i K(\mathbf{Z}, 1)$ ). If i > 1, then the homology group on the left vanishes, and the inverse system on the right can be identified with the system

$$\ldots \to \mathbf{F}_p \xrightarrow{0} \mathbf{F}_p \xrightarrow{0} \mathbf{F}_p,$$

which is trivial as a pro-vector space.

**Corollary 3.** For each  $i \ge 0$  and each n > 0, the canonical map

$$\phi: H_i K(\mathbf{Z}, n) \to " \varprojlim H_i K(\mathbf{Z}/p^k \mathbf{Z}, n) "$$

is an isomorphism in the category of pro- $\mathbf{F}_p$ -vector spaces.

*Proof.* We work by induction on n, the case n = 1 having been handled above. For every abelian group A, the Eilenberg-Moore spectral sequence has  $E_2$ -term given by

$$E_2^{a,b}(A) \simeq \operatorname{Tor}_a^{\operatorname{H}_* K(A,n-1)}(\mathbf{F}_p,\mathbf{F}_p)_b$$

and converges to  $H_*K(A,n)$ . It follows from the inductive hypothesis that the canonical map

$$E_2^{a,b}(\mathbf{Z}) \to \text{``lim } E_2^{a,b}(\mathbf{Z}/p^k\mathbf{Z})\text{''}$$

induces an isomorphism of pro-vector spaces for each a,b. It follows that we get an isomorphism of pro-vector spaces at the  $E_{\infty}$ -term. The convergence of the spectral sequence them implies that  $\phi$  is an isomorphism of pro-vector spaces.

**Corollary 4.** For each  $i \ge 0$  and each n > 0, the canonical map

$$\lim_{n \to \infty} \mathrm{H}^* \, K(\mathbf{Z}/p^k\mathbf{Z},n) \to \mathrm{H}^* \, K(\mathbf{Z},n)$$

is an isomorphism of  $\mathbf{F}_n$ -vector spaces.

**Corollary 5.** Let  $X = K(\mathbf{Z}, n)$ , where  $n \geq 1$ . Then the p-profinite completion  $X^{\vee}$  can be identified with the formal inverse limit

$$Y = "\underline{\lim} K(\mathbf{Z}/p^k\mathbf{Z}, n)".$$

*Proof.* We have a canonical map  $X^{\vee} \to Y$  of p-profinite spaces. To show that it is a homotopy equivalence, it will suffice to show that it induces an isomorphism on cohomology. This follows immediately from Corollary 4.

Corollary 6. If  $X = K(\mathbf{Z}, n)$ , then the canonical map  $\widehat{X} \to K(\mathbf{Z}_p, 1)$  is a homotopy equivalence.

The following result will allow us to promote this result to more general Eilenberg-MacLane spaces:

**Lemma 7.** Let X and Y be spaces such that  $H^*(X; \mathbf{F}_p)$  and  $H^*(Y; \mathbf{F}_p)$  are finite dimensional in each degree. Then the canonical ma  $\widehat{X \times Y} \to \widehat{X} \times \widehat{Y}$  is a homotopy equivalence.

*Proof.* Since the functor  $\lim : \mathfrak{S}_p^{\vee} \to \mathfrak{S}$  preserves homotopy limits, it will suffice to show that the canonical map  $(X \times Y)^{\vee} \to X^{\vee} \times Y^{\vee}$  is an equivalence of p-profinite spaces. For this, it suffices to show that this map induces an isomorphism on cohomology. In general, we have isomorphisms

$$\mathrm{H}^*(X^\vee \times Y^\vee) \simeq \mathrm{H}^*(X^\vee) \otimes \mathrm{H}^*(Y^\vee) \simeq \mathrm{H}^*(X) \otimes \mathrm{H}^*(Y)$$

If the cohomology groups of X and Y are finite dimensional in each degree, then the Kunneth theorem allows us to identify this tensor product with  $H^*(X \times Y) \simeq H^*((X \times Y)^{\vee})$ , as desired.

**Corollary 8.** Let A be a finitely generated abelian group and  $n \ge 1$ . Set  $A^{\vee} = A \otimes_{\mathbf{Z}} \mathbf{Z}_p$ . Then the canonical map  $\widehat{K(A,n)} \to K(A^{\vee},n)$  is a homotopy equivalence.

Proof. Using Lemma 7 and the structure theory for finitely generated abelian groups, we can assume either that  $A = \mathbf{Z}$  or that  $A \simeq \mathbf{Z}/l^k\mathbf{Z}$ , where l is some prime number. In the first case, the desired result follows from Corollary 6. If l = p, then  $K(A, n) = K(A^{\vee}, n)$  is p-finite and the result is obvious. If l is distinct from p, then K(A, n) has trivial cohomology (with coefficients in  $\mathbf{F}_p$ ), so that  $\widehat{K(A, n)}$  and  $K(A^{\vee}, n)$  are both contractible.

**Lemma 9.** Suppose given a homotopy pullback square

$$X' \longrightarrow X$$

$$\downarrow \qquad \qquad \downarrow$$

$$Y' \longrightarrow Y$$

of simply connected spaces, whose cohomology groups (with coefficients in  $\mathbf{F}_p$ ) are finite dimensional in each degree. Then the induced square

$$\widehat{X'} \longrightarrow \widehat{X}$$

$$\downarrow \qquad \qquad \downarrow$$

$$\widehat{Y'} \longrightarrow \widehat{Y}$$

is a homotopy pullback diagram.

*Proof.* As before, it suffices to show that the diagram

$$X'^{\vee} \longrightarrow X^{\vee}$$

$$\downarrow \qquad \qquad \downarrow$$

$$V'^{\vee} \longrightarrow V^{\vee}$$

is a homotopy pullback diagram of p-profinite spaces, which is equivalent to the assertion that the diagram

$$C^*(X') \longleftarrow C^*(X)$$

$$\uparrow \qquad \qquad \uparrow$$

$$C^*(Y') \longleftarrow C^*(Y)$$

is a homotopy pushout diagram of  $E_{\infty}$ -algebras over  $\mathbf{F}_p$ . This is equivalent to the convergence of the cohomological Eilenberg-Moore spectral sequence; we proved this result in the case where all of the spaces involved were p-finite. However, our proof only used the finite dimensionality of cohomology groups and the nilpotence of the spaces involved; in particular, it remains valid when each space is simply connected and has cohomology of finite type.

We are now ready to prove our main result:

Proof of Theorem 1. Let X be a simply connected space whose homotopy groups are finitely generated. Then X has a Postnikov tower

$$\dots \to \tau_{\leq 3} X \to \tau_{\leq 2} X \to \tau_{\leq 1} X \simeq *,$$

where  $\tau_{\leq n}X$  is obtained from X by killing the homotopy groups of X above dimension n. In particular, the map  $X \to \tau_{\leq n}X$  is highly connected if n is large, so that  $H^*X \simeq \varinjlim H^*\tau_{\leq n}X$ . It follows that we have an equivalence of p-profinite spaces

$$X^{\vee} \simeq \lim (\tau_{\leq n} X)^{\vee}.$$

Passing to the homotopy inverse limit, we get a homotopy equivalence

$$\widehat{X} \simeq \underline{\lim} \, \widehat{\tau_{\leq n} X}.$$

It will therefore suffice to prove the analogous result after replacing X by  $\tau_{\leq n}X$ . We now proceed by induction on n, using the existence of a homotopy pullback square

$$\tau_{\leq n} X \longrightarrow * \\
\downarrow \qquad \qquad \downarrow \\
\tau_{\leq n-1} X \longrightarrow K(\pi_n X, n+1).$$

The desired result now follows by combining the inductive hypothesis, Lemma 9, and Corollary 8.  $\Box$ 

We conclude this section by giving a characterization of  $\widehat{X}$  by a universal property. We first recall Bousfield's notion of an  $\mathbf{F}_p$ -local space.

**Definition 10.** A map  $f: X \to Y$  of spaces is said to be an  $\mathbf{F}_p$ -equivalence if the induced map on cohomology  $\mathrm{H}^*(Y) \to \mathrm{H}^*(X)$  is an isomorphism.

A space Z is said to be  $\mathbf{F}_p$ -local if, for every  $\mathbf{F}_p$ -equivalence  $f: X \to Y$ , the induced map  $\mathrm{Map}(Y,Z) \to \mathrm{Map}(X,Z)$  is a homotopy equivalence.

**Example 11.** Every Eilenberg-MacLane space  $K(\mathbf{F}_p, n)$  is  $\mathbf{F}_p$ -local (since the homotopy groups of the mapping space  $Map(X, K(\mathbf{F}_p, n))$  can be identified with cohomology groups of X with coefficients in  $\mathbf{F}_p$ ).

It is clear that the collection of  $\mathbf{F}_p$ -local spaces is closed under homotopy limits. Since every p-finite space X can be built from Eilenberg-MacLane spaces  $K(\mathbf{F}_p, n)$  using finite homotopy limits, we conclude that p-finite spaces are  $\mathbf{F}_p$ -local. It follows that any homotopy limit of p-finite spaces is again  $\mathbf{F}_p$ -local. In particular, for any space X, the space  $\hat{X} = \varprojlim X^{\vee}$  is  $\mathbf{F}_p$ -local.

**Definition 12.** We say that a map of spaces  $f: X \to X'$  exhibits X' as an  $\mathbf{F}_p$ -localization of X if f is an  $\mathbf{F}_p$ -equivalence and X' is  $\mathbf{F}_p$ -local.

**Remark 13.** For any space X, there exists an  $\mathbf{F}_p$ -localization X' of X, and X' is uniquely determined up to weak homotopy equivalence.

**Proposition 14.** Let X be a simply connected space whose homotopy groups are finitely generated. Then the unit map  $f: X \to \widehat{X}$  exhibits  $\widehat{X}$  as an  $\mathbf{F}_p$ -localization of X.

*Proof.* We have seen above that  $\widehat{X}$  is  $\mathbf{F}_p$ -local. It will therefore suffice to show that f induces an isomorphism on cohomology with coefficients modulo p. Using the Serre spectral sequence repeatedly, we can reduce to the case where X is an Eilenberg-MacLane space K(A, n), where A is a finitely generated abelian group. Then  $\widehat{X} = K(A^{\vee}, n)$ . We then have a fiber sequence

$$X \to \widehat{X} \to K(A^{\vee}/A, n).$$

Using the Serre spectral sequence again, it will suffice to show that the space  $K(A^{\vee}/A, n)$  has trivial cohomology with coefficients in  $\mathbf{F}_p$ . We can then invoke the following Lemma:

**Lemma 15.** Let B be an abelian group such that multiplication by p is an isomorphism from B to itself, and let  $n \ge 1$ . Then  $H_* K(B, n)$  vanishes for \* > 0.

*Proof.* Since the functor  $B \mapsto H_* K(B,n)$  commutes with filtered colimits, we may assume without loss of generality that B is a finitely generated module over  $\mathbf{Z}[\frac{1}{p}]$ . Using the Eilenberg-Moore spectral sequence, we can assume n=1. Using the structure theorem for finitely generated abelian groups and the Kunneth formula, we may assume either that  $B = \mathbf{Z}[\frac{1}{p}]$  or that  $B = \mathbf{Z}/l^k\mathbf{Z}$ , where  $l \neq p$ . In the second case the result is clear: the homology of a finite group G is always trivial at any prime which does not divide the order |G|. In the first case, K(B,1) is the homotopy colimit of the sequence

$$S^1 \xrightarrow{p} S^1 \xrightarrow{p} S^1 \to \dots$$

so we have  $H_*K(B,1) \simeq \lim_{\to \infty} H_*S^1$  and the result follows by inspection.

**Remark 16.** For a general space X, the unit map  $X \to \widehat{X}$  need *not* induce an isomorphism on  $\mathbf{F}_p$ -cohomology, so that  $\widehat{X}$  need not be an  $\mathbf{F}_p$ -localization of X.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Arithmetic Square (Lecture 32)

Our goal in this lecture is to address the following question: given a nice space X, to what extent can X be recovered from its completions at all primes? We begin by reviewing the situation for abelian groups.

Let A be a finitely generated abelian group. For each prime p, let  $A_p$  denote the p-adic completion  $A \otimes_{\mathbf{Z}} \mathbf{Z}_p$ . Let  $A_{\mathbf{Q}}$  denote the rationalization  $A \otimes_{\mathbf{Z}} \mathbf{Q}$ . We have canonical maps

$$A_{\mathbf{Q}} \leftarrow A \rightarrow \prod_{p} A_{p},$$

which fit into a commutative diagram

$$A \longrightarrow \prod_{p} A_{p}$$

$$\downarrow \qquad \qquad \downarrow$$

$$A_{\mathbf{Q}} \longrightarrow (\times_{p} A_{p})_{\mathbf{Q}}$$

Remark 1. This diagram is a pullback square: in other words, it determines a short exact sequence

$$0 \to A \to A_{\mathbf{Q}} \times \prod_{p} A_{p} \to (\times_{p} A_{p})_{\mathbf{Q}} \to 0.$$

We wish to prove an analogue of this result where the abelian group A is replaced by a nice topological space X.

We first discuss the rationalization of topological spaces.

**Definition 2.** Let  $f: X \to Y$  be a map of topological spaces. We say that f is a rational homotopy equivalence if it induces an isomorphism on rational cohomology  $H^*(Y; \mathbf{Q}) \to H^*(X; \mathbf{Q})$  (this is equivalent to the assertion that f induces an isomorphism on rational homology). We say that a space Z is rational (or  $\mathbf{Q}$ -local) if, for every rational homotopy equivalence  $f: X \to Y$ , the induced map

$$\operatorname{Map}(Y, Z) \to \operatorname{Map}(X, Z)$$

is a homotopy equivalence.

Given a topological space X, a rationalization of X is a topological space X' equipped with a rational homotopy equivalence  $X \to X'$ , such that X' is rational.

If X is any topological space, then a rationalization X' of X is determined by X, up to canonical homotopy equivalence. This follows from Yoneda's lemma: for any rational space Z, we have an equivalence of mapping spaces  $\operatorname{Map}(X',Z) \simeq \operatorname{Map}(X,Z)$ , so that the functor co-represented by X' (on rational spaces) is already determined by X. A fundamental result of Bousfield implies that every space X admits a rationalization. We will be content to prove the following less general, but more explicit result:

**Theorem 3.** Let X be a simply connected topological space. Then:

- (1) A map  $X \to X'$  is a rationalization of X if and only if X' is simply connected, and for each i > 1 the map  $\pi_i X \to \pi_i X'$  induces an isomorphism  $\pi_i X \otimes_{\mathbf{Z}} \pi_i X'$ .
- (2) X admits a rationalization  $X_{\mathbf{Q}}$ .

The proof proceeds in several steps.

**Lemma 4.** Let Z be a simply connected topological space. Assume that each homotopy group  $\pi_i Z$  is a vector space over the rational numbers. Then Z is rational.

**Remark 5.** The converse is also true; this follows from Theorem 3.

*Proof.* Suppose first that Z is an Eilenberg-MacLane space K(V, n), where V is a rational vector space. Then, for any space X, we have

$$\pi_i \operatorname{Map}(X, Z) \simeq \operatorname{H}^{n-i}(X; V).$$

If  $f: X \to Y$  is a rational equivalence, then f induces an isomorphism on rational homology. It follows from the universal coefficient theorem that f induces an isomorphism on cohomology with coefficients in V, so that f induces a homotopy equivalence  $\operatorname{Map}(Y, Z) \to \operatorname{Map}(X, Z)$ . This proves that Z is rational.

We now consider the general case. The space Z is the homotopy limit of its Postnikov tower

$$\ldots \to \tau_{\leq n} Z \to \ldots \tau_{\leq 1} Z \simeq *.$$

Since the collection of rational spaces is stable under homotopy limits, it will suffice to show that each  $\tau_{\leq n}Z$  is rational. The proof proceeds by induction on n. We have a homotopy pullback diagram

$$\tau_{\leq n}Z \xrightarrow{} * \downarrow \qquad \qquad \downarrow \\ \tau_{\leq n-1}Z \xrightarrow{} K(\pi_n Z, n+1).$$

The inductive hypothesis implies that  $\tau_{\leq n-1}Z$  is rational, and the first part of the proof shows that  $K(\pi_n Z, n+1)$  is rational. It follows that  $\tau_{\leq n}Z$  is also rational, as desired.

We now prove the "if" direction of assertion (1) in Theorem 3. Let  $f: X \to X'$  be a map of simply connected spaces which induces isomorphisms  $\pi_i X \otimes_{\mathbf{Z}} \mathbf{Q} \to \pi_i X'$  for i > 1. We wish to show that X' is a rationalization of X. Lemma 4 shows that X' is rational; it therefore suffices to show that f induces an isomorphism on rational cohomology. We have a fiber sequence

$$F \to X \to X'$$

In view of the Serre spectral sequence, it suffices to show that the rational cohomology of F is trivial in positive degrees. The long exact sequence of homotopy groups shows that the homotopy groups of F consist entirely of torsion. The desired result is therefore an immediate consequence of the following:

**Lemma 6.** Let F be a connected space, and assume that the homotopy groups of F are abelian torsion groups. Then  $H_*(F; \mathbf{Q})$  vanishes for \*>0.

Proof. We will prove by induction on i that the statement holds for the Postnikov section  $\tau_{\leq i}F$ . Since  $H_i(F; \mathbf{Q}) \simeq H_i(\tau_{\leq i}F; \mathbf{Q})$ , this will imply the desired result. Using the inductive hypothesis and the Serre spectral sequence, we can reduce to the case where F is an Eilenberg-MacLane space K(A, i), where A is an abelian torsion group. Then A is a filtered colimit of finite abelian groups; we may therefore reduce to the case where A is finite. Using the Eilenberg-Moore spectral sequence, we can reduce to the case where i = 1. We now appeal to the following fact: in positive degrees, the homology groups of a finite group A are annihilated by the order |A|; in particular, the rational homology groups vanish.

We now prove the following version of the second part of Theorem 3:

(2') Let X be a simply connected topological space. Then there exists a map  $f: X \to X_{\mathbf{Q}}$ , where  $X_{\mathbf{Q}}$  is simply connected and f induces isomorphisms  $\pi_i X \otimes_{\mathbf{Z}} \mathbf{Q} \to \pi_i X_{\mathbf{Q}}$ .

In view of what we have proven above, the space  $X_{\mathbf{Q}}$  will automatically be a rationalization of X, and therefore functorially determined by X.

We now prove (2') under the additional assumption that the homotopy groups  $\pi_i X$  vanish for i > n, using induction on n. If n = 1, then X is contractible and there is nothing to prove. In general, if we let  $\tau X$  denote the space obtained by killing the nth homotopy group of X, then we have a homotopy pullback diagram

$$\begin{array}{ccc}
X & \longrightarrow * \\
\downarrow & & \downarrow \\
\tau X & \longrightarrow K(\pi_n X, n+1).
\end{array}$$

Using the inductive hypothesis and the first step, we can extend this diagram as follows:

Here we have invoked the fact that  $(\tau X)_{\mathbf{Q}}$  is a rationalization of  $\tau X$  to complete the bottom square. The outer square determines a map from X into the homotopy pullback

$$X_{\mathbf{Q}} = (\tau X)_{\mathbf{Q}} \times_{K(\pi_n X \otimes_{\mathbf{Z}} \mathbf{Q}, n+1} *.$$

It is easily checked that  $X_{\mathbf{Q}}$  has the desired properties.

We now handle the general case. The simply connected space admits a Postnikov tower

$$\dots \to \tau_{\leq n} X \to \tau_{\leq n-1} X \to \dots \to \tau_{\leq 1} X \simeq *.$$

Since the process of rationalization is functorial and (2') is satisfied by each  $\tau_{\leq k}X$ , we get an induced tower

$$\ldots \to (\tau_{\leq n} X)_{\mathbf{Q}} \to \ldots \to (\tau_{\leq 1} X)_{\mathbf{Q}} \simeq *.$$

Let  $X_{\mathbf{Q}}$  denote the homotopy inverse limit of this tower; it is easy to see that  $X_{\mathbf{Q}}$  has the desired properties. This completes the proof of (2'), and therefore the proof of part (2) of Theorem 3.

We now prove the "only if" direction of Theorem 3. Let X be a simply connected topological space. In view of (2'), there exists a rationalization  $X \to X_{\mathbf{Q}}$  which induces isomorphisms  $\pi_i X \otimes_{\mathbf{Z}} \mathbf{Q} \to \pi_i X_{\mathbf{Q}}$ . Since a rationalization of X is determined up to homotopy equivalence by X, it follows that any rationalization of X has the same property.

We are now ready to return to the main theme of this lecture. Let X be a simply connected topological space, and assume that each homotopy group  $\pi_i X$  is finitely generated. For every prime p, let  $\widehat{X}_p = \varprojlim X_p^{\vee}$  denote the p-adic completion of X discussed in the last lecture. We have a canonical map

$$X \to \prod_p \widehat{X}_p.$$

Both sides are simply connected, and therefore admit rationalizations. We get a homotopy commutative diagram

$$X \longrightarrow (\prod_{p} \widehat{X}_{p})$$

$$\downarrow \qquad \qquad \downarrow$$

$$X_{\mathbf{Q}} \longrightarrow (\prod_{p} \widehat{X}_{p})_{\mathbf{Q}}$$

**Theorem 7.** Let X be a simply connected space whose homotopy groups are finitely generated. Then the preceding diagram is a homotopy pullback square.

In other words, under reasonable connectedness and finiteness assumptions, any space X can be recovered by "gluing" together its rationalizations and its completions at all primes.

*Proof.* Let Y denote the homotopy fiber product

$$\left(\prod_{p} \widehat{X}_{p}\right) \times_{\left(\prod_{p} \widehat{X}_{p}\right)_{\mathbf{Q}}} X_{\mathbf{Q}},$$

so that we have a canonical map  $\alpha: X \to Y$  and we wish to show that it is a homotopy equivalence. By construction, the homotopy groups of Y fit into a long exact sequence

$$\ldots \to \pi_n Y \to \pi_n X_{\mathbf{Q}} \times \pi_n (\prod_p \widehat{X}_p) \xrightarrow{\phi_n} \pi_n (\prod_p \widehat{X}_p)_{\mathbf{Q}} \to \ldots$$

Let  $A = \pi_n X$ . Then we can identify the domain of  $\phi_n$  with the product  $A_{\mathbf{Q}} \times \prod_p A_p$ , and the codomain of  $\phi_n$  with  $(\prod_p A_p)_{\mathbf{Q}}$ . Remark 1 implies that  $\phi_n$  is surjective. It follows that the long exact sequences above breaks up into short exact sequences, and gives isomorphisms

$$\pi_n Y \simeq \ker(\phi_n) \simeq A.$$

These isomorphisms are induced by the map  $A \to \pi_n X \to \pi_n Y$ , so that  $\alpha$  is a homotopy equivalence as desired.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Sullivan Conjecture Revisited (Lecture 33)

In this lecture we will prove the following version of the Sullivan conjecture:

**Theorem 1.** Let X be a simply connected finite cell complex, and let G be a finite group. Then the diagonal inclusion

$$X \to X^{BG}$$

is a weak homotopy equivalence.

In the last lecture, we saw that X fits into a homotopy pullback square

$$X \longrightarrow \prod \widehat{X}_{p}$$

$$\downarrow \qquad \qquad \downarrow$$

$$X_{\mathbf{Q}} \longrightarrow (\prod \widehat{X}_{p})_{\mathbf{Q}}$$

Let us say that a space Y is good if, for every finite group G, the diagonal map  $Y \to Y^{BG}$  is a weak homotopy equivalence. The collection of good spaces is obviously stable under homotopy limits. Consequently, Theorem 1 is an immediate consequence of the following:

**Proposition 2.** Let X be a simply connected finite cell complex. Then:

- (1) For every prime p, the p-adic completion  $\hat{X}_p$  is good.
- (2) The rationalization  $X_{\mathbf{Q}}$  is good.
- (3) The "adelic completion"  $(\prod_p \widehat{X}_p)_{\mathbf{Q}}$  is good.

Assertions (2) and (3) follow from the following more general statement:

**Lemma 3.** Let Y be a rational space. Then Y is good.

*Proof.* We wish to show that the map

$$\operatorname{Map}(*,Y) \to \operatorname{Map}(BG,Y)$$

is a homotopy equivalence, for every finite group G. Since Y is rational, it will suffice to show that the projection  $BG \to *$  is a rational homotopy equivalence. In other words, we must show that  $H^*(BG; \mathbf{Q})$  vanishes for \*>0. This is clear: the higher cohomology of a finite group G is annihilated by the order |G| of G.

We now focus on the proof of part (1) in Proposition 2. Fix a prime number p. We will begin by studying the situation where the finite group G is a p-group. In this case, we have

$$(\widehat{X}_p)^{BG} \simeq (\varprojlim X_p^{\vee})^{BG}$$
  
 $\simeq \varprojlim ((X_p^{\vee})^{BG}).$ 

Since X is finite dimensional, our p-profinite version of the Sullivan conjecture implies that the canonical map  $X_p^{\vee} \to (X_p^{\vee})^{BG}$  is an equivalence of p-profinite spaces. Passing to the homotopy inverse limit, we get a homotopy equivalence

$$\widehat{X}_p \to (\widehat{X}_p)^{BG},$$

as desired.

Now let G be an arbitrary finite group. Let H be a p-Sylow subgroup of G. We have a canonical map  $BH \to BG$ ; without loss of generality, we may arrange that this is a covering map whose fibers can be identified with the finite set G/H. We define a simplicial space  $K_{\bullet}$  by the formula

$$K_n = BH \times_{BG} BH \times_{BG} \times \ldots \times_{BG} BH$$
,

where the factor BH appears (n+1)-times. We have a canonical homotopy equivalence

$$|K_{\bullet}| \to BG$$
.

We can describe the space  $K_{\bullet}$  more carefully as follows. Let  $M_{\bullet}$  be the simplicial set with  $M_n = (G/H)^{n+1}$ . Then G acts (diagonally) on the simplicial set  $M_{\bullet}$ , and the simplicial space  $K_{\bullet}$  can be identified with the homotopy quotient  $(M_{\bullet})_{hG}$ . Let  $K'_{\bullet}$  be the simplicial set defined by the formula

$$K_n' = \pi_0 K_n,$$

so that  $K'_{\bullet}$  can be identified with the ordinary quotient  $(M_{\bullet})_G$ . We can identify an element of  $K'_n$  with an equivalence class of sequences  $(g_0H,\ldots,g_nH)$ , where each  $c_i$  is a (right) coset of H in G, and two sequences  $(g_0H,\ldots,g_nH)$  and  $(g'_0H,\ldots,g'_nH)$  are equivalence if there exists an element  $g \in G$  such that  $g_iH = gg'_iH$  for  $0 \le i \le n$ .

For each n, the fiber of the map  $K_n \to K'_n$  over an n-tuple  $(g_0H,\ldots,g_nH)$  can be identified with the classifying space BP, where  $P=g_0Hg_0^{-1}\cap g_1Hg_1^{-1}\cap\ldots\cap g_nHg_n^{-1}$ . In particular, P is conjugate to a subgroup of H, and is therefore a finite p-group. It follows that the diagonal map  $\widehat{X}_p \to (\widehat{X}_p)^{BP}$  is a homotopy equivalence. Taking a product over all elements of  $K'_n$ , we conclude that the map

$$(\widehat{X}_p)^{K'_n} \to (\widehat{X}_p)^{K_n}$$

is a homotopy equivalence.

We now compute

$$\begin{split} (\widehat{X}_p)^{BG} &\simeq (\widehat{X}_p)^{|K_{\bullet}|} \\ &\simeq \varprojlim (\widehat{X}_p)^{K_n} \\ &\simeq \varprojlim (\widehat{X}_p)^{K'_n} \\ &\simeq (\widehat{X}_p)^{|K'_{\bullet}|}. \end{split}$$

It will therefore suffice to show that the diagonal map

$$\widehat{X}_p \to \operatorname{Map}(|K'_{\bullet}|, \widehat{X}_p)$$

is a homotopy equivalence. Since  $\hat{X}_p$  is an  $\mathbf{F}_p$ -local space, this is an immediate consequence of the following lemma:

**Lemma 4.** The projection  $|K'_{\bullet}| \to *$  induces an equivalence on  $\mathbf{F}_p$ -homology.

In other words, we claim that the homology groups  $H_*(|K'_{\bullet}|; \mathbf{F}_p)$  vanish for \*>0. These are the homology groups of the complex

$$\ldots \to \mathbf{F}_p[K_2'] \to \mathbf{F}_p[K_1'] \to \mathbf{F}_p[K_0'] \to 0,$$

where  $\mathbf{F}_p[Z]$  denotes the free  $\mathbf{F}_p$ -vector space on a basis given by the elements of  $\mathbf{Z}$ . The simplicial set  $K'_{\bullet}$  can be extended to an *augmented* simplicial set by defining  $K'_{-1} = * \simeq ((G/H)^0)_G$ , so we get an augmented chain complex

$$\dots \to \mathbf{F}_p[K_2'] \to \mathbf{F}_p[K_1'] \to \mathbf{F}_p[K_0'] \to \mathbf{F}_p[K_{-1}'] \to 0.$$

We will show that this chain complex is acyclic (in all degrees). For this, it suffices to exhibit a contracting chain homotopy h. We choose a homotopy h given by the formula

$$(g_0H,\ldots,g_nH)\mapsto \frac{1}{|G/H|}\sum_{g\in G/H}(gH,g_0H,\ldots,g_nH).$$

This map is well-defined since it is clearly G-invariant, and the expression  $\frac{1}{|G/H|}$  makes sense in virtue of our assumption that H is a p-Sylow subgroup of G. A simple calculation shows that this map is indeed a contracting homotopy. This completes the proof of Theorem 1.

**Remark 5.** We have assumed that X is a simply connected finite CW complex. This assumption was used in two ways:

- (1) We invoked the fact that X was simply connected and that the homotopy groups  $\pi_i X$  are finitely generated, in order to use the arithmetic square discussed in the previous lecture.
- (2) We invoked the fact that X was finite dimensional so that we could appeal to our p-profinite version of the Sullivan conjecture.

Assumptions (1) and (2) guarantee that X is a finite complex, at least up to homotopy equivalence. But Haynes Miller's original proof of Theorem 1 actually works in a much more general setting: one only needs to assume that X is finite dimensional (in particular, the fundamental group  $\pi_1 X$  can be arbitrary).

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Quaternionic Projective Space (Lecture 34)

The three-sphere  $S^3$  can be identified with SU(2), and therefore has the structure of a topological group. In this lecture, we will address the question of how canonical this structure is. In the category of topological groups, the group structure on  $S^3$  is unique up to isomorphism. However, the purely homotopy-theoretic situation is not quite so nice: there exist uncountably many pairwise inequivalent group structures on spaces which are homotopy equivalent to  $S^3$  (we will return to this point at the end of the lecture). However, the situation is much simpler in p-adic homotopy theory, where p is a fixed prime. In this case, we again have a unique group structure on (the p-adic completion) of the homotopy type of  $S^3$ . We will sketch a proof of this result when p is odd, following the ideas of Dwyer, Miller and Wilkerson.

We begin by formulating the problem more precisely. In homotopy theory, giving a group structure on a homotopy type G is equivalent to realizing G as the loop space of a pointed space X. In this case, we have a fiber sequence

$$G \to * \to X$$
.

If  $G = S^3$ , then we can use the Serre spectral sequence to compute the (mod p) cohomology ring of X:  $H^*(X) \simeq \mathbf{F}_p[t]$ , where t lies in degree 4 (and transgresses to the fundamental class of  $G = S^3$ ). Moreover, we have the same picture in the p-profinite category. We can now state the main result:

**Theorem 1** (Dwyer, Miller, Wilkerson). Let X be a p-profinite space such that  $H^*(X) \simeq \mathbf{F}_p[t]$ , where t lies in degree 4. Then X is equivalent to the p-profinite completion  $BSU(2)_p^{\vee}$  of the classifying space of the group SU(2) (in other words, infinite dimensional quaternionic projective space).

The first step is to describe the cohomology  $H^*(X)$  as a representation of the mod-p Steenrod algebra  $\mathcal{A}_p$ . To simplify the exposition, we will consider only the case  $p \neq 2$ . We therefore begin with a few recollections on the structure of  $\mathcal{A}_p$ :

- For any space X (or any p-profinite space), the algebra  $\mathcal{A}_p$  acts on the cohomology ring  $H^*(X; \mathbf{F}_p)$ .
- The algebra  $A_p$  is generated the Bockstein operator  $\beta$  of degree 1, together with operations  $P^i$  of degree 2i(p-1), for i>0.
- We have a Cartan formula

$$P^{n}(xy) = \sum_{n=n'+n''} P^{n'}(x) P^{n''}(y),$$

and a similar formula for  $\beta$  (which involves a sign). Here we agree by convention that  $P^0 = \mathrm{id}$ .

- If  $x \in H^{2i}(X; \mathbf{F}_p)$ , then  $P^i(x) = x^p$  and  $P^j(x) = 0$  for j > i (instability).
- We have  $P^1P^1=2P^2$  (this is a special case of the Adem relations, which we will not write out in full).

**Lemma 2.** Let X be as in the statement of Theorem 1. Then there exists an isomorphism  $\alpha : H^*(X) \simeq \mathbf{F}_p[t]$  such that the action of  $\mathcal{A}_p$  on  $H^*(X) \simeq \mathbf{F}_p[t]$  is determined by the Cartan formula, together with the relations

$$\beta t = 0$$

$$P^{i}t = \begin{cases} 2t^{\frac{p+1}{2}} & \text{if } i = 1\\ t^{p} & \text{if } i = 2\\ 0 & \text{otherwise}. \end{cases}$$

*Proof.* The formula  $\beta t = 0$  is obvious, since  $H^5(X) \simeq 0$ . The expressions  $P^i t$  vanishes for i > 2 by instability, and  $P^2 t = t^p$ . We have  $P^1(t) = ct^{\frac{p+1}{2}}$  for some constant  $c \in \mathbf{F}_p$ ; the only nontrivial point is to compute c. For this, we observe

$$2t^{p} = 2P^{2}(t)$$

$$= P^{1}P^{1}(t)$$

$$= cP^{1}t^{\frac{p+1}{2}}$$

$$= c^{2}\frac{p+1}{2}t^{p}$$

so that  $c^2 = \frac{4}{p+1} = 4$ . This has solutions  $c = \pm 2$ . However, if c = -2 then we can adjust the isomorphism  $\alpha$  via the substitution  $t \mapsto \lambda t$ , where  $\lambda \in \mathbf{F}_p$  is not a quadratic residue, to obtain an isomorphism with the desired property.

Corollary 3. There exists an isomorphism  $\alpha: H^*(X) \simeq H^*(BSU(2))$  of unstable  $\mathcal{A}_p$ -algebras.

We now make a few remarks about the structure of the group SU(2). We have injective group homomorphisms

$$\mathbf{Z}/p\mathbf{Z} \hookrightarrow S^1 \hookrightarrow SU(2).$$

These induce maps of classifying spaces

$$B\mathbf{Z}/p\mathbf{Z} \to BS^1 \to BSU(2),$$

hence we get maps on cohomology

$$H^*(B\mathbf{Z}/p\mathbf{Z}) \leftarrow H^*(BS^1) \leftarrow H^*(BSU(2)).$$

A simple computation shows that each of these maps is injective, and we can identify the above with the sequence

$$\mathbf{F}_{p}[u,\epsilon] \longleftrightarrow \mathbf{F}_{p}[u] \longleftrightarrow \mathbf{F}_{p}[t].$$

Here  $t \mapsto u^2$ , where u has degree 2, and  $\epsilon$  has degree 1 in  $H^*(B\mathbf{Z}/p\mathbf{Z})$  (and therefore squares to zero).

**Lemma 4.** There exists a map  $\beta: B\mathbf{Z}/p\mathbf{Z} \to X$  such that the diagram

commutes.

*Proof.* We have

$$\pi_0 \operatorname{Map}(B\mathbf{Z}/p\mathbf{Z}, X) \simeq \operatorname{Hom}(\mathrm{H}^*(X^{B\mathbf{Z}/p\mathbf{Z}}), \mathbf{F}_p)$$
  
 $\simeq \operatorname{Hom}(T \operatorname{H}^*(X), \mathbf{F}_p)$   
 $\simeq \operatorname{Hom}(\mathrm{H}^*(X), \mathrm{H}^*(B\mathbf{Z}/p\mathbf{Z}))$ 

Here the Hom-sets on the right hand side are computed in the category of unstable  $\mathcal{A}_p$ -algebras. In other words, any map of  $\mathcal{A}_p$ -algebras from  $H^*(X)$  to  $H^*(B\mathbf{Z}/p\mathbf{Z})$  is necessarily induced by a map of p-profinite spaces  $B\mathbf{Z}/p\mathbf{Z}$  to X (which is then uniquely determined up to homotopy).

Let Y be the connected component of the mapping space  $X^{B\mathbf{Z}/p\mathbf{Z}}$  containing the map  $\beta$ . We then have isomorphisms

$$H^{*}(Y) \simeq H^{*}(X^{B\mathbf{Z}/p\mathbf{Z}}) \otimes_{H^{0}(X^{B\mathbf{Z}/p\mathbf{Z}})} \mathbf{F}_{p}$$
  
$$\simeq T H^{*}(X) \otimes_{(T H^{*}(X))^{0}} \mathbf{F}_{p}.$$

Consequently, the cohomology ring  $H^*(Y)$  depends only on  $H^*(X)$ .

Let us temporarily assume that  $X = BSU(2)_p^{\vee}$  and that  $\beta$  is the map induced by the group homomorphism  $\mathbb{Z}/p\mathbb{Z} \to SU(2)$ . The loop space  $\Omega Y$  can be identified with the space of homotopies from  $\beta$  to itself, which is a space of sections of a certain fibration

$$E \to B\mathbf{Z}/p\mathbf{Z}$$

with fiver  $SU(2)_p^{\vee}$ . This fibration corresponds to an action of  $\mathbf{Z}/p\mathbf{Z}$  on  $SU(2)_p^{\vee}$ , which is simply induced by the action of  $\mathbf{Z}/p\mathbf{Z}$  by conjugation. We therefore may therefore identify  $\Omega Y$  with the homotopy fixed set  $(SU(2)_p^{\vee})^{h\mathbf{Z}/p\mathbf{Z}}$ . Using the p-profinite Sullivan conjecture, this can be identified with the p-profinite completion of the actual fixed set  $SU(2)^{\mathbf{Z}/p\mathbf{Z}}$ , which is simply the centralizer of  $\mathbf{Z}/p\mathbf{Z}$  in SU(2). A simple calculation shows that this centralizer coincides with the circle group  $S^1 \subseteq SU(2)$ . It follows that  $\Omega Y \simeq (S^1)_p^{\vee}$ . Using the Serre spectral sequence, we conclude that  $H^*(Y)$  is isomorphic to  $\mathbf{F}_p[u]$ , where u lies in degree 2. Moreover, the translation action of  $B\mathbf{Z}/p\mathbf{Z}$  on itself determines a map  $B\mathbf{Z}/p\mathbf{Z} \to Y$ , which (after scaling u if necessary) is given on cohomology by the canonical inclusion

$$\mathbf{F}_p[u] \hookrightarrow \mathbf{F}_p[u,\epsilon].$$

We now return to the general case. Since  $H^*(Y)$  depends only on  $H^*(X)$ , we conclude that  $H^* \simeq \mathbf{F}_p[u]$  in general. Evaluation at the base point of  $B\mathbf{Z}/p\mathbf{Z}$  induces a map  $e: Y \to X$ . Moreover, the composition

$$B\mathbf{Z}/p\mathbf{Z} \to Y \xrightarrow{e} X$$

can be identified with the map  $\beta$ . It follows that the above sequence induces, on cohomology, the maps

$$\mathbf{F}_p[u,\epsilon] \longleftrightarrow \mathbf{F}_p[u] \longleftrightarrow \mathbf{F}_p[t].$$

Consider the map from  $X^{B\mathbf{Z}/p\mathbf{Z}}$  to itself, given by composition with the map

$$\mathbf{Z}/p\mathbf{Z} \stackrel{-1}{\to} \mathbf{Z}/p\mathbf{Z}.$$

This map induces the identify on  $\mathrm{H}^4(B\mathbf{Z}/p\mathbf{Z})$ , and therefore induces the identity map on  $\mathrm{Hom}(\mathrm{H}^*(X),\mathrm{H}^*(B\mathbf{Z}/p\mathbf{Z})) \simeq \pi_0 X^{B\mathbf{Z}/p\mathbf{Z}}$ . It therefore induces an involution on Y, which we will denote by i. We have a commutative diagram

$$B\mathbf{Z}/p\mathbf{Z} \longrightarrow Y$$

$$\downarrow^{-1} \qquad \qquad \downarrow_{i}$$

$$B\mathbf{Z}/p\mathbf{Z} \longrightarrow Y,$$

which gives a commutative diagram of cohomology groups

$$\mathbf{F}_{p}[u,\epsilon] \longleftarrow \mathbf{F}_{p}[u]$$

$$\uparrow \qquad \qquad \uparrow$$

$$\mathbf{F}_{p}[u,\epsilon] \longleftarrow \mathbf{F}_{p}[u]$$

Since the left vertical map carries u to -u, the right vertical map does as well. Let  $Y_{h\mathbf{Z}/2\mathbf{Z}}$  denote the homotopy coinvariants of the involution on Y. Then the canonical map  $Y \to Y_{h\mathbf{Z}/2\mathbf{Z}}$  induces an isomorphism

$$\mathrm{H}^*(Y_{h\mathbf{Z}/2\mathbf{Z}}) \simeq \mathrm{H}^*(Y)^{\mathbf{Z}/2\mathbf{Z}} \simeq \mathbf{F}_p[u^2].$$

The base point of  $B\mathbf{Z}/p\mathbf{Z}$  is invariant under the map given by multiplication by (-1), so the evaluation map  $e: Y \to X$  is invariant under the action of i. Consequently, we obtain a factorization

This induces a commutative diagram of cohomology groups

We conclude that e' induces an isomorphism on cohomology, and therefore a homotopy equivalence of p-profinite spaces  $Y_{h\mathbf{Z}/2\mathbf{Z}} \to X$ .

We now identify the p-profinite space Y. Since the cohomology of Y lies entirely in even degrees, we can choose a compatible family of cohomology classes  $u_i \in H^2(Y; \mathbf{Z}/p^i\mathbf{Z})$  lifting u. These cohomology classes determine a map of p-profinite spaces

$$Y \to "\varprojlim K(\mathbf{Z}/p^k, 2)",$$

which we can identify with a map  $Y \to (BS^1)_p^{\vee}$ . This map induces an isomorphism on cohomology, and is therefore an equivalence of p-profinite spaces. We may therefore identify Y with the (p-profinite) Eilenberg-MacLane space  $K(\mathbf{Z}_p, 2)$ .

Now consider the involution i on Y. We claim that the homotopy fixed set  $Y^{h\mathbf{Z}/2\mathbf{Z}}$  is nonempty: this follows from the vanishing of the cohomology group  $\mathrm{H}^3(B\mathbf{Z}/2\mathbf{Z};\mathbf{Z}_p)$  (since p is different from 2). We may therefore assume without loss of generality that Y contains a point fixed by the involution i. In this case, i can be regarded as a pointed map from the Eilenberg-MacLane space  $K(\mathbf{Z}_p,2)$  to itself, which is given by a group homomorphism  $h:\mathbf{Z}_p\to\mathbf{Z}_p$ . Since h has order 2, we deduce that h is given by the formula  $h(z)=\lambda z$ , where  $\lambda=\pm 1$ . Since i carries  $u\in \mathrm{H}^2(Y)$  to -u, we deduce that  $\lambda=-1$ . We have therefore proven:

**Theorem 5.** Let X be as in Theorem 1 and p an odd prime. Then there is an equivalence of p-profinite spaces

$$X \simeq K(\mathbf{Z}_n, 2)_{h\mathbf{Z}/2\mathbf{Z}},$$

where the group  $\mathbb{Z}/2\mathbb{Z}$  acts on  $\mathbb{Z}_p$  by the sign involution.

In particular, there is only one possibility for the homotopy type of X. Theorem 1 follows.

Let us now consider the same problem in the non-p-profinite world. Let X be a simply connected space such that  $H^*(X; \mathbf{Z}) \simeq H^*(BSU(2); \mathbf{Z}) \simeq \mathbf{Z}[t]$ , where t lies in degree 4 (this is equivalent to the assertion that the loop space  $\Omega X$  is homotopy equivalent to a three sphere  $S^3$ , by the Serre spectral sequence). We have a homotopy pullback diagram

$$X \longrightarrow \prod_{p} \widehat{X}_{p}$$

$$\downarrow \qquad \qquad \downarrow$$

$$X_{\mathbf{Q}} \longrightarrow (\prod_{p} \widehat{X}_{p})_{\mathbf{Q}}$$

Using Theorem 1 (and its analogue in the case p=2), we deduce that for each prime p we have a homotopy equivalence  $\widehat{X}_p \simeq \widehat{BSU(2)}_p$ . A much easier argument shows that  $X_{\mathbf{Q}} \simeq K(\mathbf{Q},4) \simeq BSU(2)_{\mathbf{Q}}$ . We can therefore rewrite the above homotopy pullback diagram as

However, this does not imply that  $X \simeq BSU(2)$ , because the map  $\phi$  has not been determined. The domain of  $\phi$  can be identified with an Eilenberg-MacLane space  $K(\mathbf{Q}, 4)$ , and the codomain of  $\phi$  with an Eilenberg-MacLane space  $K((\prod_p \mathbf{Z}_p)_{\mathbf{Q}}, 4)$ , so that  $\phi$  is determined up to homotopy by specifying an element  $\eta \in (\prod_p \mathbf{Z}_p)_{\mathbf{Q}}$ . Every invertible element  $\eta \in (\prod_p \mathbf{Z}_p)_{\mathbf{Q}}$  gives rise to a space X which is a delooping of the sphere  $S^3$ . Not all of these choices are distinct (as an exercise, you can try to figure out when two choices of  $\eta$  give homotopy equivalent deloopings), but this "mixing" construction nevertheless yields uncountably many group structures on the homotopy type  $S^3$ .

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Analytic Functors Revisited (Lecture 35)

In this lecture, we will revisit the relationship between unstable modules over the (mod 2) Steenrod algebra  $\mathcal{A}$  and analytic functors from the category of  $\mathbf{F}_2$  vector spaces to itself.

Let Vect denote the category of  $\mathbf{F}_2$ -vector spaces,  $\operatorname{Vect}^f$  the full subcategory consisting of finite dimensional vector spaces, and Fun the category of all functors from  $\operatorname{Vect}^f$  to  $\operatorname{Vect}$ . Recall that  $\operatorname{Fun}^{\operatorname{an}}$  denotes the category of analytic functors: that is, functors which can be obtained as colimits of functors  $F: \operatorname{Vect}^f \to \operatorname{Vect}$  having the property that the function

$$n \mapsto \dim F(\mathbf{F}_2^n)$$

is a polynomial. In particular, Fun<sup>an</sup> contains the divided power functors  $\Gamma^n$  defined by the formula

$$\Gamma^n(V) = (V^{\otimes n})^{\Sigma_n}.$$

Let  $\mathcal{U}$  denote the category of unstable modules over the Steenrod algebra. In a previous lecture, we studied a pair of adjoint functors

$$\mathcal{U} \xrightarrow{f} \operatorname{Fun}^{\operatorname{an}}$$
.

This adjunction was essentially uniquely determined by the requirement that f carries a free unstable module F(n) to the analytic functor  $\Gamma^n$ . We begin by reformulating this construction using Lannes' T-functor.

Let M be an unstable A-module. For every  $\mathbf{F}_2$ -vector space V, the A-module  $T_VM$  is defined by the universal property

$$\operatorname{Hom}(T_V M, N) \simeq \operatorname{Hom}(M, N \otimes \operatorname{H}^*(BV)).$$

In particular, given a map  $V \to W$ , the composition

$$M \to T_W M \otimes H^*(BW) \to T_W M \otimes H^*(BV)$$

is classified by a map  $T_VM \to T_WM$ . In other words,  $T_VM$  is a covariant functor of V.

**Proposition 1.** The functor  $f: \mathcal{U} \to \operatorname{Fun}^{\operatorname{an}}$  is defined by the formula

$$f(M)(V) = (T_V M)^0$$
.

*Proof.* This formula evidently defines a colimit-preserving functor from  $\mathcal{U}$  to Fun<sup>an</sup>. It is therefore determined by its values on free unstable  $\mathcal{A}$ -modules (since any module admits a free resolution). We will show that the above formula has the correct behavior on objects, and leave to the reader to check that the behavior on morphisms is correct. For this, we compute

$$(T_V F(n))^0 \simeq \operatorname{Hom}(T_V F(n), \mathbf{F}_2)^{\vee}$$
  
 $\simeq \operatorname{Hom}(F(n), \operatorname{H}^*(BV))^{\vee}$   
 $\simeq \operatorname{H}^n(BV)^{\vee}$   
 $\simeq \operatorname{Sym}^n(V^{\vee})^{\vee}$   
 $\simeq \Gamma^n V.$ 

From this description and the exactness of  $T_V$ , we immediately deduce that the functor  $f: \mathcal{U} \to \text{Fun}^{\text{an}}$  is exact. Of course, this reasoning is circular: earlier, we used the exactness of f to prove that  $H^*(BV)$  was an injective object of  $\mathcal{U}$ , which was a key step in the proof that the functor  $T_V$  is exact.

We now wish to generalize the above construction. We first expand on the observation that  $T_V M$  depends functorially on V. Fix an integer  $n \geq 0$ . We will say that an unstable  $\mathcal{A}$ -module M is n-truncated if  $M^i = 0$  for i > n. Given any unstable  $\mathcal{A}$ -module M, we can define an n-truncated  $\mathcal{A}$ -module  $\tau^{\leq n} M$  by the formula

$$(\tau^{\leq n} M)^i = \begin{cases} M^i & \text{if } i \leq n \\ 0 & \text{otherwise.} \end{cases}$$

In other words,  $\tau^{\leq n}M$  is the quotient of M obtained by killing all elements of degree larger than n. The collection of all n truncated unstable  $\mathcal{A}$ -modules forms a category which we will denote by  $\mathcal{U}^{\leq n}$ . This category inherits a symmetric monoidal structure  $\boxtimes$ , given by the formula

$$M \boxtimes N \mapsto \tau^{\leq n}(M \otimes N)$$

where  $\otimes$  denotes the usual tensor product of A-modules.

We now define a category  $\mathcal{C}_n$  which is enriched over the *opposite* of  $\mathcal{U}^{\leq n}$ , as follows:

- The objects of  $\mathcal{C}_n$  are finite dimensional  $\mathbf{F}_2$ -vector spaces V.
- Given a pair of objects V and W, we have

$$\operatorname{Map}_{\mathcal{C}}(V, W) = T_V \operatorname{H}^*(BW) \simeq \operatorname{H}^*(BW)^{BV}.$$

• Composition in  $\mathcal{C}_n$  is induced by the maps

$$(BW)^{BV} \times (BV)^{BU} \to (BW)^{BU}$$
.

We let  $\operatorname{Fun}_n$  denote the category consisting of all  $\mathcal{U}^{\leq n,op}$ -enriched functors from  $\mathcal{C}_n$  to  $\mathcal{U}^{\leq n}$ . In other words, an object F of  $\operatorname{Fun}_n$  can be described as follows:

- For every finite dimensional  $\mathbf{F}_2$ -vector space V, F(V) is an n-truncated unstable  $\mathcal{A}$ -module.
- For every pair of  $\mathbf{F}_2$ -vector spaces V and W, we have an associated map of A-modules

$$F(V) \to \tau^{\leq n}(T_V \operatorname{H}^*(BW) \otimes F(W)).$$

• These maps are compatible with composition in the obvious sense.

**Example 2.** Let M be an unstable A-module, and define  $P_M(V)$  by the formula

$$P_M(V) = \tau^{\leq n} T_V(M).$$

For every pair of  $\mathbf{F}_2$ -vector spaces V and W, the canonical map

$$M \to T_W M \otimes H^*(BW) \to T_W M \otimes T_V H^*(BW) \otimes H^*(BV)$$

is adjoint to a map

$$T_V M \to T_W M \otimes T_V H^*(BW)$$
.

Truncating, we obtain a map

$$P_M(V) \to \tau^{\leq n}(P_M(W) \otimes T_V \operatorname{H}^*(BW)),$$

so that  $P_M$  can be viewed as an object of Fun<sub>n</sub>.

**Example 3.** Suppose n = 0. An n-truncated  $\mathcal{A}$ -module M can be identified with its underlying  $\mathbf{F}_2$ -vector space  $M^0$ . An object  $F \in \operatorname{Fun}_0$  associates to each  $\mathbf{F}_2$ -vector space V a new vector space F(V), and to each pair (V, W) a map

$$F(V) \to F(W) \otimes \mathrm{H}^0(BW)^{BV} \simeq F(W) \otimes \mathbf{F}_2^{\mathrm{Hom}(V,W)}.$$

This is equivalent to giving a map  $F(V) \to F(W)$  for every map of vector spaces from V to W. In other words, we can identify F with a functor from  $\operatorname{Vect}^f$  to  $\operatorname{Vect}$ . Consequently,  $\operatorname{Fun}_0$  is canonically equivalent to the category Fun defined above.

**Remark 4.** More generally, for any  $n \geq 0$  and any  $F \in \operatorname{Fun}_n$ , we have canonical maps

$$F(V) \to F(W) \otimes \mathrm{H}^0(BW)^{BV} \simeq F(W) \otimes \mathbf{F}_2^{\mathrm{Hom}(V,W)}$$
.

which allow us to view  $F(V) \in \mathcal{U}$  as a covariant functor of V. We will say that F is analytic (polynomial, etcetera) if this underlying functor is analytic. Let  $\operatorname{Fun}_n^{\operatorname{an}}$  denote the full subcategory of  $\operatorname{Fun}_n$  consisting of analytic functors.

The construction  $M \mapsto P_M$  defines a functor

$$f_n: \mathcal{U} \to \operatorname{Fun}_n$$
.

In the special case n = 0, we recover the functor studied earlier in this course. We now generalize some of our previous results:

## **Proposition 5.** Let $n \geq 0$ .

- (1) For every unstable A-module M, the functor  $f_nM \in \operatorname{Fun}_n$  is analytic.
- (2) The functor  $f_n$  determines an adjunction

$$\mathcal{U} \xrightarrow{f_n} \operatorname{Fun}_n^{\operatorname{an}}$$
.

- (3) The functor  $f_n$  is exact.
- (4) The functor  $g_n$  is fully faithful.

*Proof.* To prove (1), it suffices to treat the case where M is a free unstable module F(k). In this case, we have we will prove the following stronger assertion:

(1') The functor  $f_n F(k) = P_{F(k)}$  is polynomial and each  $P_{F(k)}(V)^i$  is finite dimensional.

To prove this, we simply compute

$$(f_n F(k))(V)^i \simeq (T_V F(k))^i$$

$$\simeq \operatorname{Hom}(T_V F(k), J(i))^\vee$$

$$\simeq \operatorname{Hom}(F(k), J(i) \otimes \operatorname{H}^*(BV))^\vee$$

$$\simeq \oplus_{k=k'+k''} (J(i)^{k'})^\vee \otimes \Gamma^{k'}(V).$$

Assertion (2) follows from the adjoint functor theorem. Moreover, assertion (1') yields a little bit more:

(2') The functor  $g_n$  preserves filtered colimits.

To see this, we observe that for every integer i, we have

$$(g_{n} \varinjlim G_{\alpha})^{i} \simeq \operatorname{Hom}_{\mathcal{U}}(F(i), g_{n} \varinjlim G_{\alpha})$$

$$\simeq \operatorname{Hom}_{\operatorname{Fun}_{n}^{\operatorname{an}}}(f_{n}F(i), \varinjlim G_{\alpha})$$

$$\simeq \varinjlim \operatorname{Hom}_{\operatorname{Fun}_{n}^{\operatorname{an}}}(f_{n}F(i), G_{\alpha})$$

$$\simeq \varinjlim \operatorname{Hom}_{\mathcal{U}}(F(i), g_{n}G_{\alpha})$$

$$\simeq \varinjlim (g_{n}G_{\alpha})^{i}$$

Assertion (3) follows from the exactness of Lannes' T-functor. To prove (4), we need to introduce a bit of notation. For  $0 \le i \le n$ , let  $I_{W,J(i)}$  denote the object  $f_n(J(i) \otimes H^*(BW)) \in \operatorname{Fun}_n$ . Since  $T_V$  commutes with products and carries J(i) to itself, we have

$$I_{W,J(i)}(V) = \tau^{\leq n}(J(i) \otimes T_V \operatorname{H}^*(BW)).$$

Using Yoneda's lemma, we deduce the existence of a canonical isomorphism

$$\operatorname{Hom}_{\operatorname{Fun}_n}(F, I_{W,J(i)}) = \operatorname{Hom}_{\mathcal{U}}(F(W), J(i)).$$

In particular  $I_{W,J(i)}$  is injective in Fun<sub>n</sub>. We claim that  $I_{W,J(i)}$  is analytic. To prove this, it suffices to show that for  $j \leq n$  the functor

$$V \mapsto \bigoplus_{j=j'+j''} J(i)^{j'} \otimes \operatorname{H}^{j''}(BW)^{BV}$$

is analytic. For this, it suffices to show that the functor

$$V \mapsto \operatorname{H}^{i''}(BW)^{BV}$$

is analytic. This functor is a summand of the functor

$$V \mapsto \mathrm{H}^*(BW)^{BV} \simeq \mathrm{H}^*(BW) \otimes \mathbf{F}_2^{\mathrm{Hom}(V,W)}.$$

The first factor is constant, and the second factor was shown to be analytic in a previous lecture. Let M be an unstable A-module. We compute

$$\begin{array}{lcl} \operatorname{Hom}_{\operatorname{Fun}_n}(f_nM,I_{W,J(i)}) & \simeq & \operatorname{Hom}_{\operatorname{\mathfrak{U}}}((f_nN)(W),J(i)) \\ & \simeq & \operatorname{Hom}_{\operatorname{\mathfrak{U}}}(\tau^{\leq n}T_WM,J(i)) \\ & \simeq & \operatorname{Hom}_{\operatorname{\mathfrak{U}}}(T_WM,J(i)) \\ & \simeq & \operatorname{Hom}_{\operatorname{\mathfrak{U}}}(M,J(i)\otimes\operatorname{H}^*(BW)). \end{array}$$

In other words, we can identify  $g_n I_{W,J(i)}$  with  $J(i) \otimes H^*(BW)$ . It follows that the unit map  $f_n g_n \to id$  is an isomorphism when evaluated on  $I_{W,J(i)}$ .

Every object  $F \in \operatorname{Fun}_n^{\operatorname{an}}$  can be written as a union of its finitely generated subfunctors, which are polynomial functors of finite type and therefore have finite length as objects of  $\operatorname{Fun}_n^{\operatorname{an}}$ . It follows that  $\operatorname{Fun}_n^{\operatorname{an}}$  is a locally Noetherian abelian category in which every Noetherian object has finite length. It follows that the indecomposable injective objects of  $\operatorname{Fun}_n^{\operatorname{an}}$  are precisely the injective hulls of the simple objects. Let F be simple, and let I be an injective hull of F. Then for some vector space W, we have  $F(W) \neq 0$  so there exists a nontrivial map  $F(W) \to J(i)$  for  $0 \leq i \leq n$ . This classifies a nonzero map  $F \to I_{W,J(i)}$ . Since  $I_{W,J(i)}$  is injective, we can extend this to a map  $\phi: I \to I_{W,J(i)}$ . The kernel of this map does not intersect  $F \subseteq I$ , and is therefore itself zero (since I is an injective hull of F). It follows that  $\phi$  is a monomorphism between injective objects of  $\operatorname{Fun}_n^{\operatorname{an}}$ , so that  $\phi$  splits. In other words, every indecomposable injective can be obtained as a direct summand of some  $I_{W,J(i)}$ . Since every injective object of  $\operatorname{Fun}_n^{\operatorname{an}}$  can be written as a direct sum of indecomposable injectives (this is true in any Grothendieck abelian category), we conclude that every injective can be obtained as a summand of an expression of the form  $\bigoplus_{i=1}^n I_{W_0,J(i)}$ .

It follows that any functor  $G \in \operatorname{Fun}_n^{\operatorname{an}}$  admits an injective resolution

$$0 \to G \to \bigoplus_{\alpha} I_{W_{\alpha}, J(i_{\alpha})} \to \bigoplus_{\beta} I_{W_{\beta}, J(i_{\beta})}$$

Since  $f_n$  and  $g_n$  are both left exact, we get a diagram of short exact sequences

To prove that the left vertical arrow is an isomorphism, it suffices to show that the other two vertical arrows are isomorphisms. Since  $f_n$  and  $g_n$  both commute with direct sums, we can reduce to the case where  $G = I_{W,J(i)}$ , which was handled above.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Nil-Filtration (Lecture 36)

In the last lecture, we showed that the category U of unstable Steenrod modules fits into an adjunction

$$\mathcal{U} \xrightarrow{f_n} \operatorname{Fun}_n$$

where  $f_n$  is exact and  $g_n$  is fully faithful. Our goal in this lecture is to put this result into a more general context.

**Definition 1.** Let  $\mathcal{C}$  be a Grothendieck abelian category. A *Serre class* in  $\mathcal{C}$  is a full subcategory  $\mathcal{C}_0 \subseteq \mathcal{C}$  such that:

(1) Given a short exact sequence

$$0 \to X' \to X \to X'' \to 0$$

in  $\mathcal{C}$ , the object X belongs to  $\mathcal{C}_0$  if and only if X' and X" belong to  $\mathcal{C}_0$ .

- (2) The subcategory  $\mathcal{C}_0$  is closed under small colimits in  $\mathcal{C}$  (in virtue of (1), this is equivalent to being closed under direct sums).
- (3) The abelian category  $\mathcal{C}_0$  is Grothendieck: in other words, there exists a set of objects of  $\mathcal{C}_0$  which generates  $\mathcal{C}_0$  under colimits.

We say that a morphism  $f: X \to Y$  in  $\mathfrak{C}$  is a  $\mathfrak{C}_0$ -equivalence if the kernel and cokernel of f belong to  $\mathfrak{C}_0$ .

In what follows, we fix a Grothendieck abelian category  $\mathcal{C}$  and a Serre subcategory  $\mathcal{C}_0$ .

**Lemma 2.** Let X be an object of  $\mathbb{C}$ . The following conditions are equivalent:

- (1) For every  $\mathcal{C}_0$ -equivalence  $Y \to Y'$ , the induced map  $\operatorname{Hom}_{\mathcal{C}}(Y',X) \to \operatorname{Hom}_{\mathcal{C}}(Y,X)$  is a bijection.
- (2) For every object  $Z \in \mathcal{C}_0$ , we have  $\operatorname{Hom}_{\mathcal{C}}(Z,X) = \operatorname{Ext}_{\mathcal{C}}(Z,X) = 0$ .

*Proof.* Suppose first that (1) is satisfied. If  $Z \in \mathcal{C}_0$ , then the map  $0 \to Z$  is a  $\mathcal{C}_0$ -equivalence, so we get  $\operatorname{Hom}_{\mathcal{C}}(Z,X) \simeq \operatorname{Hom}_{\mathcal{C}}(0,X) \simeq 0$ . To prove that  $\operatorname{Ext}_{\mathcal{C}}(Z,X)$  vanishes, we consider an arbitrary extension

$$0 \to X \xrightarrow{f} Y \to Z \to 0$$

and show that it is split. The map f is a  $\mathcal{C}_0$ -equivalence, so composition with f induces a bijection  $\operatorname{Hom}_{\mathcal{C}}(Y,X) \to \operatorname{Hom}_{\mathcal{C}}(X,X)$ . In particular, the identity map from X to itself factors through f, so the above exact sequence splits.

Now suppose that (2) is satisfied, and let  $g: Y \to Y'$  be a  $\mathcal{C}_0$ -equivalence. Then g factors as a composition

$$Y \xrightarrow{g'} \operatorname{Im}(g) \xrightarrow{g''} Y',$$

where g' is an epimorphism and g'' is a monomorphism. We may therefore assume that g is either epic or monic. In the epic case, we have a short exact sequence

$$0 \to \ker(a) \to Y \to Y' \to 0$$

which yields an exact sequence

$$0 \to \operatorname{Hom}_{\mathcal{C}}(Y', Z) \to \operatorname{Hom}_{\mathcal{C}}(Y, Z) \to \operatorname{Hom}_{\mathcal{C}}(\ker(q), Z) = 0.$$

In the monic case, we have a short exact sequence

$$0 \to Y \to Y' \to \operatorname{coker}(g) \to 0$$

which gives rise to an exact sequence

$$0 \simeq \operatorname{Hom}_{\mathcal{C}}(\operatorname{coker}(g), Z) \to \operatorname{Hom}_{\mathcal{C}}(Y', Z) \to \operatorname{Hom}_{\mathcal{C}}(Y, Z) \to \operatorname{Ext}_{\mathcal{C}}(\operatorname{coker}(g), Z) \simeq 0.$$

**Definition 3.** We will say that an object  $X \in \mathcal{C}$  is  $\mathcal{C}_0$ -local if the equivalent conditions of Lemma 2 are satisfied. We let  $\mathcal{C} / \mathcal{C}_0$  denote the full subcategory of  $\mathcal{C}$  consisting of  $\mathcal{C}_0$ -local objects.

**Example 4.** Let  $\mathcal{C}$  be the category of abelian groups, and  $\mathcal{C}_0$  the full subcategory consisting of abelian groups M such that every element  $m \in M$  satisfies  $p^k m = 0$  for  $k \gg 0$ . Then  $\mathcal{C}_0$  is a Serre class in  $\mathcal{C}$ . An abelian group is  $\mathcal{C}_0$ -local if and only if it is a module over the ring  $\mathbf{Z}[\frac{1}{n}]$ .

**Example 5.** Let  $\mathcal{U}$  be the category of unstable modules over the Steenrod algebra  $\mathcal{A}$ , and let Nil  $\subseteq \mathcal{U}$  denote the subcategory of *nilpotent* modules. Then Nil is a Serre class in  $\mathcal{U}$ .

**Remark 6.** It is clear from characterization (1) of Lemma 2 that the collection of  $C_0$ -local objects of C is stable under arbitrary limits.

**Proposition 7.** Let C be a Grothendieck abelian category and  $C_0 \subseteq C$  a Serre class. Then:

- (1) The inclusion  $C / C_0 \subseteq C$  admits a left adjoint L.
- (2) The category  $\mathcal{C} / \mathcal{C}_0$  is a Grothendieck abelian category.
- (3) The functor L is exact.

**Warning 8.** The inclusion  $\mathcal{C}/\mathcal{C}_0 \subseteq \mathcal{C}$  is *not* an exact functor in general. The formation of cokernels in  $\mathcal{C}/\mathcal{C}_0$  is given by first forming cokernels in  $\mathcal{C}$ , and then applying the functor L.

*Proof.* Using the small object argument, one can show that every object  $X \in \mathcal{C}$  admits a  $\mathcal{C}_0$ -equivalence  $X \to LX$ , where LX is  $\mathcal{C}_0$ -local. One can then show that LX depends functorially on X and yields the desired adjoint.

We will prove (2). First, we show that  $\mathcal{A} = \mathcal{C}/\mathcal{C}_0$  is an abelian category. It is easy to see that  $\mathcal{A}$  is additive and admits kernels and cokernels. To avoid confusion, if  $f: X \to Y$  is a morphism in  $\mathcal{A}$ , we let  $\operatorname{coker}_{\mathcal{A}}(f)$  denote the cokernel of f in the category  $\mathcal{A}$ , and  $\operatorname{coker}_{\mathcal{C}}(f)$  its cokernel in the category  $\mathcal{C}$ , so that we have an identification  $\operatorname{coker}_{\mathcal{A}}(f) \simeq L \operatorname{coker}_{\mathcal{C}}(f)$ . (There is no need to introduce any complicated notation for kernels, since these can be computed either in  $\mathcal{A}$  or in  $\mathcal{C}$ .) To prove that  $\mathcal{A}$  is an abelian category, we must show that if  $f: X \to Y$  is a morphism in  $\mathcal{A}$ , then the canonical map

$$\operatorname{coker}_{A}(\ker(f) \to X) \to \ker(Y \to \operatorname{coker}_{A}(f))$$

is an isomorphism. In other words, we must show that the map

$$L\operatorname{coker}_{\mathfrak{C}}(\ker(f) \to X) \to \ker(Y \to L\operatorname{coker}_{\mathfrak{C}}(f))$$

is an equivalence. This is equivalent to showing that the map

$$\phi: \operatorname{coker}_{\mathcal{C}}(\ker(f) \to X) \to \ker(Y \to L \operatorname{coker}_{\mathcal{C}}(f))$$

is a  $\mathcal{C}_0$ -equivalence. Since  $\mathcal{C}$  is an abelian category, we can identify the left hand side with  $\ker(Y \to \operatorname{coker}_{\mathcal{C}}(f))$ . We have a short exact sequence

$$0 \to \ker(Y \to \operatorname{coker}_{\mathcal{C}}(f)) \xrightarrow{\phi} \ker(Y \to L \operatorname{coker}_{\mathcal{C}}(f)) \to \ker(\operatorname{coker}_{\mathcal{C}}(f) \to L \operatorname{coker}_{\mathcal{C}}(f).$$

The desired result now follows, since  $\operatorname{coker}(\phi)$  is a subobject of an object of  $\mathcal{C}_0$ , and therefore belongs to  $\mathcal{C}_0$ . Assuming (3) for the moment, we now show that  $\mathcal{A}$  is a Grothendieck abelian category. The existence of colimits and a set of generators follows from general categorical nonsense. It therefore suffices to show that filtered colimits are exact. In other words, we must show that if  $\{f_{\alpha}X_{\alpha} \to Y_{\alpha}\}$  is a filtered diagram of monomorphisms in  $\mathcal{A}$ , then the colimit  $\varprojlim_{\mathcal{A}} \{f_{\alpha}\}$  is a monomorphism. We have

$$\lim_{A} \{f_{\alpha}\} \simeq L \lim_{C} \{f_{\alpha}\},$$

so the desired result follows from the exactness of L and the assumption that  $\mathcal{C}$  is Grothendieck.

We now prove (3). Since L is a left adjoint, it is automatically right exact. It will therefore suffice to prove that L preserves monomorphisms. Let  $f: X \to Y$  be a monomorphism in  $\mathcal{C}$ ; we wish to prove that  $Lf: LX \to LY$  is again a monomorphism. Let  $K = \ker(Lf)$ , and let  $K' = K \times_{LX} X \subseteq X$ . Since f is a monomorphism, f induces a monomorphism

$$K' \to \ker(\alpha) \subseteq Y$$

where  $\alpha: Y \to LY$  is the canonical map. Since  $\alpha$  is a  $\mathcal{C}_0$ -equivalence, we deduce that  $K' \in \mathcal{C}_0$ . We have an exact sequence

$$K' \to K \to \operatorname{coker}(X \to LX)$$
,

so that  $K \in \mathcal{C}_0$  as well. But then the inclusion  $K \subseteq LX$  must be the zero map, so that  $K \simeq 0$  as desired.  $\square$ 

The next result shows that  $\mathcal{C}/\mathcal{C}_0$  can really be viewed as a "quotient" of  $\mathcal{C}$  by  $\mathcal{C}_0$ :

**Proposition 9.** Let  $\mathbb D$  be a Grothendieck abelian category, and  $F: \mathbb C \to \mathbb D$  a colimit-preserving functor. Then:

(1) The functor F is isomorphic to a composition

$$\mathfrak{C} \xrightarrow{L} \mathfrak{C} / \mathfrak{C}_0 \xrightarrow{F'} \mathfrak{D}$$

if and only if F carries  $C_0$ -equivalences to isomorphisms in D. Moreover, in this case, F' is determined up to unique isomorphism (and is colimit preserving).

(2) The functor F' is exact if and only if F is exact.

Proof. Note that  $F' = F \mid \mathcal{C} \mid \mathcal{C}_0$  is, up to isomorphism, the only functor satisfying the condition of (1); the condition that  $F \simeq F \circ L$  is equivalent to the requirement that F carries  $\mathcal{C}_0$ -equivalences to isomorphisms. This proves (1). We now prove (2). The "only if" direction is clear, since L is exact. Conversely, suppose that F is exact. Since F' preserves colimits, it is automatically right exact; it therefore suffices to show that F' preserves monomorphisms. This follows from the exactness of F, since  $F' \simeq F \mid \mathcal{C} \mid \mathcal{C}_0$  and a morphism  $f: X' \to X$  is a monomorphism in  $\mathcal{C}$  if and only if it is a monomorphism in  $\mathcal{C} \mid \mathcal{C}_0$ . This proves (2).

**Remark 10.** Note that, if F is exact, then F carries  $\mathcal{C}_0$ -equivalences to isomorphisms if and only if F annihilates every object of  $\mathcal{C}_0$ .

**Corollary 11.** Let  $F: \mathcal{C} \to \mathcal{D}$  be an exact, colimit preserving functor between Grothendieck abelian categories. Then:

- (1) Let  $\mathcal{C}_0 \subseteq \mathcal{C}$  be the full subcategory consisting of objects  $X \in \mathcal{C}$  such that  $FX \simeq 0$ . Then  $\mathcal{C}_0$  is a Serre class in  $\mathcal{C}$ .
- (2) The functor F factors as a composition  $\mathfrak{C} \to \mathfrak{C}/\mathfrak{C}_0 \xrightarrow{F'} \mathfrak{D}$ , where F' is an exact colimit preserving functor.
- (3) The functor F admits a right adjoint G.
- (4) The functor F' is an equivalence if and only if G is fully faithful.

Proof. Assertion (1) follows immediately from the definitions, and (2) follows from Proposition 9. Assertion (3) follows from the adjoint functor theorem. The "only if" direction of (4) is clear, since the localization functor  $L: \mathcal{C} \to \mathcal{C} / \mathcal{C}_0$  is left adjoint to the fully faithful inclusion  $\mathcal{C} / \mathcal{C}_0 \subseteq \mathcal{C}$ . For the converse, let us suppose that G is fully faithful. Replacing  $\mathcal{C}$  by  $\mathcal{C} / \mathcal{C}_0$  if necessary, we may reduce to the case  $\mathcal{C}_0 = 0$ . We wish to show that F is an equivalence of categories. Since G is fully faithful, the counit map  $\beta_D: FG(D) \to D$  is an isomorphism for any  $D \in \mathcal{D}$ . We want to show that the unit map  $\alpha: C \to GF(C)$  is an isomorphism for each  $C \in \mathcal{C}$ . The map  $F(\alpha)$  is a right inverse to the invertible morphism  $\beta_{FC}: FG(F(C)) \to F(C)$ , so  $F(\alpha)$  is an isomorphism. It follows that  $\ker(\alpha)$  and  $\operatorname{coker}(\alpha)$  are annihilated by F, so  $\ker(\alpha) \simeq \operatorname{coker}(\alpha) \simeq 0$  and  $\alpha$  is an isomorphism as desired.

We now return to our main example:

Corollary 12. Let  $f_n: \mathcal{U} \to \operatorname{Fun}_n$  be the functor defined in the last lecture, so that  $f_n(M)(V) = \tau^{\leq n} T_V M$ . Then  $f_n$  induces an equivalence of categories  $\mathcal{U} / \mathcal{K}_n \simeq \operatorname{Fun}_n$ , where  $\mathcal{K}_n$  denotes the Serre class consisting of all unstable A-modules M such that  $\tau^{\leq n} T_V M$  vanishes for every finite dimensional  $\mathbf{F}_2$ -vector space V.

The following more precise description of  $\mathcal{K}_n$  is available:

**Theorem 13.** For each  $n \geq 0$ , the Serre class  $\mathcal{K}_n \subseteq \mathcal{U}$  is the smallest Serre class containing  $\Sigma^{n+1}M$ , for every  $M \in \mathcal{U}$ .

*Proof.* Since  $T_V$  commutes with suspension, we have

$$\tau^{\leq n} T_V \Sigma^{n+1} M \simeq \tau^{\leq n} \Sigma^{n+1} T_V M \simeq 0$$

for every  $M \in \mathcal{U}$ . This proves that  $\Sigma^{n+1}M$  is contained in  $\mathcal{K}_n$ . The reverse inclusion is a nontrivial result which we will discuss in the next lecture.

**Example 14.** The Serre classes Nil,  $\mathcal{K}_0 \subseteq \mathcal{U}$  coincide. The containment  $\mathcal{K}_0 \subseteq \text{Nil}$  is clear, since every suspension  $\Sigma M$  is nilpotent (in fact, the Frobenius map  $\Phi M \to M$  is identically zero). Conversely, suppose that M is nilpotent. For each  $k \geq 0$ , let M(k) denote the submodule of M consisting of elements x such that

$$\operatorname{Sq}^{2^k \operatorname{deg}(x)} \dots \operatorname{Sq}^{2 \operatorname{deg}(x)} \operatorname{Sq}^{\operatorname{deg} x} x = 0.$$

Then  $M = \bigcup_k M(k)$ , so it will suffice to show that each  $M(k) \in \mathcal{K}_0$ . The proof then proceeds by induction on k. Since  $\mathcal{K}_0$  is closed under extensions, it suffices to show that each N = M(k)/M(k-1) belongs to  $\mathcal{K}_0$ . But the Frobenius map  $\Phi N \to N$  is zero by construction, so the exact sequence

$$\Phi N \to N \to \Sigma \Omega N \to 0$$

proves that N is a suspension and therefore belongs to  $\mathcal{K}_0$ .

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## The Krull Filtration (Lecture 37)

Let A be a commutative Noetherian ring. Recall that the Zariski spectrum Spec A is defined to be the set of all prime ideals  $\{\mathfrak{p} \subseteq A\}$ . Let  $\mathrm{Mod}_A$  denote the category of A-modules. It is possible to recover Spec A directly from the category  $\mathrm{Mod}_A$ . For this, we need to recall a few definitions and facts:

**Definition 1.** Let  $\mathcal{C}$  be a Grothendieck abelian category. An object  $X \in \mathcal{C}$  is *Noetherian* if every ascending chain of subobjects of X eventually stabilizes. We say that  $\mathcal{C}$  is *locally Noetherian* if every object of  $\mathcal{C}$  is the direct limit of its Noetherian subobjects.

An object  $I \in \mathcal{C}$  is *injective* if the functor  $M \mapsto \operatorname{Hom}_{\mathcal{C}}(M, I)$  is exact. We say that an injective object I is *indecomposable* if, whenever I is written as a direct sum  $I \simeq I' \oplus I''$ , either I' or I'' is zero.

Let  $X \in \mathcal{C}$  be an object. An *injective hull* of X is a monomorphism  $X \to I$  such that I is injective, and every nonzero subobject  $I' \subseteq I$  satisfies  $I' \times_I X \neq 0$ .

**Proposition 2.** Let C be a locally Noetherian abelian category. Then:

- (1) Every object  $M \in \mathcal{C}$  admits an injective hull  $M \to I$ . Moreover, I is uniquely determined up to (noncanonical) isomorphism. If M is simple, then I is indecomposable.
- (2) Every direct sum  $\bigoplus_{\alpha} I_{\alpha}$  of injective objects is injective.
- (3) Every injective object  $I \in \mathcal{C}$  can be obtained as a direct sum  $\bigoplus_{\alpha} I_{\alpha}$ , where each summand  $I_{\alpha}$  is an indecomposable injective.

This motivates the following definition:

**Definition 3.** Let  $\mathcal{C}$  be a locally Noetherian abelian category. Then we let Spec  $\mathcal{C}$  denote the collection of all isomorphism classes of indecomposable injective objects of  $\mathcal{C}$ .

**Remark 4.** A priori, the collection Spec  $\mathcal{C}$  might be very large, since  $\mathcal{C}$  has a proper class of injective objects. However, if I is an indecomposable injective object of  $\mathcal{C}$ , then I can be regarded as the injective hull of any nonzero submodule  $I_0 \subseteq I$ . In particular, I can be regarded as the injective hull of a Noetherian object of  $\mathcal{C}$ . It follows that Spec  $\mathcal{C}$  is actually a set.

**Example 5.** Let A be a Noetherian ring. Then there is a canonical bijection

$$\operatorname{Spec} A \to \operatorname{Spec} \operatorname{Mod}_A$$

which carries a prime ideal  $\mathfrak{p} \subseteq A$  to the injective hull of the A-module  $A/\mathfrak{p}$ .

For example, if  $A = \mathbf{Z}$ , then the indecomposable injective objects of  $\operatorname{Mod}_A$  are precisely the abelian groups  $\mathbf{Q}$  and  $\mathbf{Z}\left[\frac{1}{n}\right]/\mathbf{Z}$ , where p is a prime number.

**Example 6.** Let  $\mathcal{U}$  denote the category of unstable Steenrod modules. The simple objects of  $\mathcal{U}$  are precisely the modules  $\Sigma^k \mathbf{F}_2$ , where  $k \geq 0$ . The injective hull of  $\Sigma^k \mathbf{F}_2$  can be identified with the Brown-Gitler module J(k).

If A is a Noetherian ring, then Spec A has a good deal more structure than just that of a set. For example, we can (at least in good cases) assign a *Krull dimension* to every point of Spec A. The points of Krull dimension zero correspond to the maximal ideals of A. Note that the collection of maximal ideals of A can be described very simply in terms of  $\text{Mod}_A$ : they are isomorphism classes of simple objects of  $\text{Mod}_A$  (more precisely, an A-module M is simple if and only if it is isomorphic to a quotient  $A/\mathfrak{m}$ , where  $\mathfrak{m}$  is a maximal ideal of A). Therefore, the corresponding points of Spec  $\text{Mod}_A$  are precisely the injective hulls of the simple objects of A. We now wish to generalize this picture to more general categories.

**Definition 7.** Let  $\mathcal{C}$  be a locally Noetherian abelian category. Then  $\operatorname{Krull}^0(\mathcal{C})$  is the smallest Serre class in  $\mathcal{C}$  which contains every simple object in  $\mathcal{C}$ .

**Remark 8.** If  $\mathcal{C} \neq 0$ , then  $\operatorname{Krull}^0(\mathcal{C}) \neq 0$ . In other words,  $\mathcal{C}$  contains a simple object. To prove this, choose a nonzero object  $M \in \mathcal{C}$ . Since  $\mathcal{C}$  is locally Noetherian, M is the union of its Noetherian subobjects. We may therefore assume that M is Noetherian. Let  $M_0$  be a maximal proper submodule of M. Then  $M/M_0$  is a simple object of  $\mathcal{C}$ .

**Proposition 9.** Let C be a locally Noetherian abelian category, and let I be an injective object of C. Then exactly one of the following statements holds:

- (1) The object I is the injective hull of a simple object  $C \in \mathfrak{C}$  (which is then determined up to isomorphism).
- (2) The object I belongs to  $\mathbb{C}$  / Krull<sup>0</sup>( $\mathbb{C}$ ) (and is injective as an object of  $\mathbb{C}$  / Krull<sup>0</sup>( $\mathbb{C}$ )).

*Proof.* Let  $\mathcal{C}_0 = \{C \in \mathcal{C} : \operatorname{Hom}_{\mathcal{C}}(C, I) = 0\}$ . Since I is injective,  $\mathcal{C}_0$  is a Serre class in  $\mathcal{C}$ .

By definition, I belongs to  $\mathbb{C}/\mathrm{Krull}^0(\mathbb{C})$  if and only if, for every object  $C \in \mathrm{Krull}^0(\mathbb{C})$ , we have  $\mathrm{Hom}_{\mathbb{C}}(C,I) = \mathrm{Ext}_{\mathbb{C}}(C,I) = 0$ . The second equality is automatic, since I is injective, and the first is equivalent to the assertion that  $C \in \mathbb{C}_0$ . In other words,  $I \in \mathbb{C}/\mathrm{Krull}^0(\mathbb{C})$  if and only if  $\mathrm{Krull}^0(\mathbb{C}) \subseteq \mathbb{C}_0$ . Consequently, (2) holds if and only if  $\mathrm{Hom}_{\mathbb{C}}(C,I) = 0$  for every simple object  $C \in \mathbb{C}$ .

Suppose that (2) does not hold, and choose a nonzero map  $f:C\to I$  where C is simple. Then f must be a monomorphism. Choose an injective hull  $C\subseteq I'$ . Since I is injective, we can extend f to a map  $\overline{f}:I'\to I$ . Since  $\ker(\overline{f})\cap C\simeq \ker(f)\simeq 0$ , we deduce that  $\overline{f}$  is injective. Since I' is injective, the injective map  $\overline{f}$  splits and we get an isomorphism  $I\simeq I'\oplus I''$ . Since I is indecomposable,  $I''\simeq 0$  so that  $\overline{f}$  is an isomorphism. This proves (1), except for the uniqueness of C. To establish the uniqueness, we note that given injective maps

$$C \hookrightarrow I \hookleftarrow D$$
,

the intersection  $C \times_I D$  can be regarded as a nonzero submodule of both C and D. If C and D are simple, this gives isomorphisms

$$C \hookleftarrow C \times_I D \hookrightarrow D$$
.

This motivates the following definition:

**Definition 10.** Let  $\mathcal{C}$  be a Grothendieck abelian category. For each n > 0, we let  $\mathrm{Krull}^n(\mathcal{C})$  denote the inverse image of  $\mathrm{Krull}^0(\mathcal{C} / \mathrm{Krull}^{n-1}(\mathcal{C}))$  under the localization functor

$$L: \mathcal{C} \to \mathcal{C} / \mathrm{Krull}^{n-1}(\mathcal{C}).$$

We will say that an indecomposable injective  $I \in \operatorname{Spec} \mathcal{C}$  has  $\mathit{Krull\ dimension} > n$  if I belongs to  $\mathcal{C} / \operatorname{Krull}^n \mathcal{C}$ .

We have a filtration of C by Serre classes

$$\operatorname{Krull}^{0}(\mathfrak{C}) \subset \operatorname{Krull}^{1}(\mathfrak{C}) \subset \operatorname{Krull}^{2}(\mathfrak{C}) \subset \dots$$

By construction, each of the successive quotients  $\operatorname{Krull}^{n+1}(\mathcal{C})/\operatorname{Krull}^n(\mathcal{C})$  is generated by simple objects.

**Remark 11.** If A is a well-behaved commutative ring (such as a finitely generated algebra over a field), then the Krull filtration above is *finite*: we have  $\operatorname{Krull}^n(\operatorname{Mod}_A) = \operatorname{Mod}_A$  as soon as  $n \ge \dim(A)$ . In general, the filtration need not terminate nor exhaust  $\mathbb{C}$  (to obtain the whole of  $\mathbb{C}$ , one needs to define an analogous filtration indexed by the ordinals).

We wish to study the Krull filtration on the abelian category  $\mathcal{U}$  of unstable  $\mathcal{A}$ -modules. We begin by determining  $\mathrm{Krull}^0(\mathcal{A})$ .

**Definition 12.** An unstable A-module M is *locally finite* if, for each  $x \in M$ , the cyclic submodule A  $x \subseteq M$  has finite dimension over  $\mathbf{F}_2$ .

**Proposition 13.** An unstable A-module M belongs to Krull<sup>0</sup>( $\mathcal{U}$ ) if and only if M is locally finite.

*Proof.* We first observe that the collection of locally finite  $\mathcal{A}$ -modules forms a Serre class in  $\mathcal{U}$ . Consequently, to prove the "only if" direction it will suffice to show that every simple  $\mathcal{A}$ -module is locally finite. This follows from the characterization of simple objects given in Remark ??.

For the converse, let us suppose that M is locally finite. We wish to prove that  $M \in \text{Krull}^0(\mathcal{U})$ . Write M as the union of its finitely generated submodules  $M_{\alpha}$ . Since  $\text{Krull}^0(\mathcal{U})$  is a Serre class, it will suffice to show that each  $M_{\alpha}$  belongs to  $\text{Krull}^0(\mathcal{U})$ . Since M is locally finite, each  $M_{\alpha}$  is finite dimensional over  $\mathbf{F}_2$ . We may therefore assume that M has finite dimension over  $\mathbf{F}_2$ . We now work by induction on the dimension of M. Let x be a nonzero element of M of maximal degree k. Then x determines an exact sequence

$$0 \to \Sigma^k \mathbf{F}_2 \to M \to M' \to 0.$$

By construction, we have  $\Sigma^k \mathbf{F}_2 \in \mathrm{Krull}^0(\mathfrak{U})$ , and  $M' \in \mathrm{Krull}^0(\mathfrak{U})$  by the inductive hypothesis. It follows that  $M \in \mathrm{Krull}^0(\mathfrak{U})$ , as desired.

We now wish to give another characterization of  $\operatorname{Krull}^0(\mathfrak{U})$ , this time using Lannes' T-functor. We first observe that  $\operatorname{H}^*(B\mathbf{F}_2)$  canonically decomposes as a direct sum  $\mathbf{F}_2 \oplus \operatorname{H}^*_{\operatorname{red}}(B\mathbf{F}_2)$ . Consequently, we get a canonical isomorphism of functors

$$(\bullet \otimes \mathrm{H}^*(B\mathbf{F}_2)) \simeq \bullet \oplus (\bullet \otimes \mathrm{H}^*_{\mathrm{red}}(B\mathbf{F}_2)).$$

Passing to adjoints, we get a decomposition of functors

$$T \sim \mathrm{id} \oplus \overline{T}$$

from the category  $\mathcal{U}$  to itself. Moreover, formal properties of T are inherited by  $\overline{T}$ : for example, since T is exact and commutes with suspension and  $\Phi$ , we deduce that  $\overline{T}$  is exact and commutes with suspension and  $\Phi$ 

**Proposition 14.** Let M be an unstable A-module. Then  $M \in \text{Krull}^0(\mathfrak{U})$  if and only if  $\overline{T}M = 0$ .

*Proof.* The "only if" direction is easy: let  $\mathcal{C} = \{M \in \mathcal{U} : \overline{T}M = 0\}$ . Then  $\mathcal{C}$  is a Serre class in  $\mathcal{U}$ . To show that  $\mathrm{Krull}^0(\mathcal{U}) \subseteq \mathcal{C}$ , it suffices to show that every simple object  $\Sigma^k \mathbf{F}_2$  belongs to  $\mathcal{C}$ . Since  $\overline{T}$  commutes with suspensions, it suffices to show that  $\overline{T}\mathbf{F}_2$  vanishes. This is equivalent to the assertion that  $T\mathbf{F}_2 \simeq \mathbf{F}_2$ , which was established in an earlier lecture.

The converse is much more difficult to prove. It relies on the following classification of the injective objects of U:

**Theorem 15.** Every indecomposable injective object of U appears as a summand of  $J(m) \otimes (H^*_{red}(B\mathbf{F}_2))^{\otimes n}$  for some integers m and n.

Let us assume Theorem 15 and complete the proof. Let  $M \in \mathcal{U}$  be such that  $\overline{T}M = 0$ . We wish to show that  $M \in \mathrm{Krull}^0(\mathcal{U})$ . Equivalently, we wish to show that the localization functor  $L : \mathcal{U} \to \mathcal{U} / \mathrm{Krull}^0(\mathcal{U})$  annihilates M. If not, there exists a nonzero map  $\eta \in \mathrm{Hom}(LM, I) \simeq \mathrm{Hom}(M, I)$ , where I is an indecomposable

injective of  $\mathcal{U}/\text{Krull}^0(\mathcal{U})$ . According to Proposition 9, we can identify I with an indecomposable injective of  $\mathcal{U}$  which is *not* the injective hull of a simple object (in other words, I is not isomorphic to a Brown-Gitler module J(m)). Invoking Theorem 15, we get a nonzero map

$$M \to J(m) \otimes \mathrm{H}^*_{\mathrm{red}}(B\mathbf{F}_2)^{\otimes n}$$

for some n > 0. This is adjoint to a nonzero map  $\overline{T}^n M \to J(m)$ , so that  $\overline{T}M \neq 0$ .

We now extend the previous result to describe each step of the Krull filtration.

**Proposition 16.** Let M be an unstable A-module. Then  $M \in \mathrm{Krull}^n(\mathfrak{U})$  if and only if  $\overline{T}^{n+1}M \simeq 0$ .

*Proof.* The proof goes by induction on n, the case n=0 being Proposition 14. Suppose first that  $\overline{T}^{n+1}M \simeq 0$ . We wish to prove that  $M \in \operatorname{Krull}^n(\mathfrak{U})$ . Writing M as the union of its finitely generated submodules, we may reduce to the case where M is finitely generated. Let  $L: \mathcal{U} \to \mathcal{U} / \operatorname{Krull}^{n-1}(\mathcal{U})$  be the localization functor. We wish to show that LM belongs to  $\operatorname{Krull}^0(\mathcal{U} / \operatorname{Krull}^{n-1}(\mathcal{U}))$ . For this, we will show that LM has finite length in  $\mathcal{U} / \operatorname{Krull}^{n-1}\mathcal{U}$ .

By the inductive hypothesis, the functor  $\overline{T}^n$  factors as a composition

$$\mathcal{U} \xrightarrow{L} \mathcal{U} / \operatorname{Krull}^{n-1} \mathcal{U} \xrightarrow{F} \mathcal{U}$$
.

Consequently, for any subobject  $N \subseteq LM$ , we can identify FN with a subobject of  $\overline{T}^nM$ . Note that  $\overline{T}^nM$  is locally finite (by Proposition 14) and finitely generated (since  $\overline{T}$  preserves finitely generated objects), and therefore finite dimensional. Thus there are only finitely many possibilities for the subobject  $FN \subseteq \overline{T}^nM$ . But if  $FN = FN' \subseteq \overline{T}^nM$ , then the inclusions

$$N \hookrightarrow N \cap N' \hookrightarrow N'$$

induce isomorphisms

$$FN \longleftrightarrow F(N \cap N') \hookrightarrow FN'$$
.

Using the inductive hypothesis, we deduce that  $N = N \cap N' = N'$ . Thus, there are only finitely many subobjects of  $LM \in \mathcal{U}/\mathrm{Krull}^{n-1}\mathcal{U}$ , so that LM has finite length.

We now prove the reverse inclusion:  $\operatorname{Krull}^n(\mathcal{U}) \subseteq \{M : \overline{T}^{n+1}M \simeq 0\}$ . As before, the right side is a Serre class, to it will suffice to show that  $\overline{T}^{n+1}M = 0$  whenever LM is a simple object of  $\mathcal{U}/\operatorname{Krull}^{n-1}(\mathcal{U})$ . We have a sequence of surjective maps

$$M \to \Sigma \Omega M \to \Sigma^2 \Omega^2 M \to$$

whose colimit is zero. Since LM is simple, we conclude that there exists an integer k such that the map

$$LM \to L\Sigma^k\Omega^kM$$

is an isomorphism and  $L\Sigma^{k+1}\Omega^{k+1}M=0$ . We then have isomorphisms

$$\overline{T}^n M \to \overline{T}^n \Sigma^k \Omega^k M \sim \Sigma^k \overline{T}^n \Omega^k M$$

Moreover, the inductive hypothesis implies that  $\Sigma$  and  $\Omega$  induce adjoint functors on the localized category  $\mathcal{U}/\mathrm{Krull}^{n-1}(\mathcal{U})$ ; it is not difficult to deduce from this that  $L\Omega^k M$  is again simple. We may therefore replace M by  $\Omega^k M$ , and thereby assume that  $L\Sigma\Omega M\simeq 0$ .

Consider the exact sequence

$$\Phi M \to M \to \Sigma \Omega M \to 0.$$

This gives rise to an exact sequence of localizations

$$L\Phi M \xrightarrow{\alpha} LM \rightarrow L\Sigma\Omega M \rightarrow 0$$

in the category  $\mathbb{U}/\mathrm{Krull}^{n-1}(\mathbb{U})$ . Since LM is simple and the last term vanishes, we conclude that  $\alpha$  is an epimorphism.

Applying the functor F, we get an epimorphism  $\overline{T}^n \Phi M \to \overline{T}^n M$ . Let  $N = \overline{T}^n M$ . Since  $\Phi$  commutes with  $\overline{T}$ , we deduce that the canonical map  $\Phi N \to N$  is *surjective*. It then follows by induction on m that  $N^m \simeq 0$  for m > 0. In other words, N is concentrated in degree zero, and is a direct sum of copies of  $\mathbf{F}_2$ . It follows that  $0 \simeq \overline{T}N \simeq \overline{T}^{n+1}M$ , as desired.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

18.917 Topics in Algebraic Topology: The Sullivan Conjecture Fall 2007

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Epilogue (Lecture 38)

Let  $\mathcal{U}$  denote the category of unstable modules over the Steenrod algebra  $\mathcal{A}$ . In the last two lectures, we defined two different filtrations of  $\mathcal{U}$  by Serre classes. On the one hand, we have the classes

$$\ldots \subseteq Nil_2 \subseteq Nil_1 \subseteq Nil_0 = \mathcal{U}$$

such that Nil<sub>i</sub> is the kernel of the localization functor

$$\mathcal{U} \stackrel{f_n}{\to} \operatorname{Fun}_n^{\operatorname{an}}$$
.

In other words, Nil<sub>i</sub> consists of the collection of all unstable Steenrod modules M such that  $(T_V M)^j = 0$  for all j < i and all finite dimensional vector spaces V. (We can also describe Nil<sub>i</sub> as the smallest Serre class which contains all i-fold suspensions, though have not proven this.)

On the other hand, we have the Krull filtration

$$Krull^0 \subseteq Krull^1 \subseteq \dots,$$

where Krull<sup>i</sup> consists of all unstable  $\mathcal{A}$ -modules M such that  $\overline{T}^iM=0$ .

Our first goal in this lecture is to answer the following three questions:

- (A) In what sense do these filtrations "converge" to  $\mathcal{U}$ ?
- (B) How do these filtrations interact?
- (C) What do the successive quotients look like?

We begin by discussing (A).

**Lemma 1.** The canonical functor  $f_{\infty}: \mathcal{U} \to \varprojlim_n \operatorname{Fun}_n^{\operatorname{an}}$  is fully faithful.

*Proof.* The (2)-limit of the categories  $\operatorname{Fun}_n$  can be identified with a category of enriched functors  $\operatorname{Vect}^f \to \mathcal{U}$ . Then  $f_{\infty}$  is defined by the formula

$$(f_{\infty}M)(V) = T_VM.$$

This functor has a left inverse, given by evaluation at the zero vector space.

Lemma 2. The Krull filtration

$$Krull^0 \subseteq Krull^1 \subseteq \dots$$

on U is exhaustive. In other words, the smallest Serre class containing each Krull<sup>i</sup> is U itself.

*Proof.* The category  $\mathcal{U}$  is generated under colimits by the free unstable modules F(n). We will show that  $F(n) \in \text{Krull}^n$  for each  $n \geq 0$ , using induction on n. Recall that we computed

$$TF(n) \simeq F(n) \oplus F(n-1) \oplus \ldots \oplus F(0).$$

Consequently,  $\overline{T}F(n) \simeq F(n-1) \oplus \ldots \oplus F(0)$ . By the inductive hypothesis,  $\overline{T}F(n) \in \text{Krull}^{n-1}$ , so  $\overline{T}^{n+1}F(n) \simeq \overline{T}^n \overline{T}F(n) \simeq 0$  as desired.

We now address question (B). For each  $n \ge 0$ , we can define a "shift" functor S from  $\operatorname{Fun}_n^{\operatorname{an}}$  to itself by the formula  $S(G)(V) = G(V \oplus \mathbf{F}_2)$ . By construction, the diagram

$$\begin{array}{ccc}
\mathcal{U} & \xrightarrow{T} & \mathcal{U} \\
\downarrow^{f_n} & & \downarrow^{f_n} \\
\operatorname{Fun}_n^{\operatorname{an}} & \xrightarrow{S} & \operatorname{Fun}_n^{\operatorname{an}}
\end{array}$$

commutes up to isomorphism. We note that the functor S(G) contains G as a retract (since  $V \oplus \mathbf{F}_2$  contains V as a retract); we therefore have  $S(G) = G \oplus \Delta G$ , where  $\Delta$  is another functor from  $\operatorname{Fun}_n^{\operatorname{an}}$  to itself fitting into a commutative diagram

$$\mathcal{U} \xrightarrow{\overline{T}} \mathcal{U}$$

$$\downarrow^{f_n} \qquad \downarrow^{f_n}$$

$$\operatorname{Fun}_n^{\operatorname{an}} \xrightarrow{\Delta} \operatorname{Fun}_n^{\operatorname{an}}$$

By definition, the kernel of  $\Delta^{k+1}$  can be identified with the subcategory  $\operatorname{Fun}_n^{(k)} \subseteq \operatorname{Fun}_n^{\operatorname{an}}$  consisting of functors which are polynomial of degree  $\leq k$ . One can show that  $\operatorname{Fun}_n^{(k)}$  is precisely the image of  $\operatorname{Krull}^k$  in  $\operatorname{Fun}_n$ , so that the Krull filtration on  $\mathcal U$  induces the filtration

$$\operatorname{Fun}_n^{(0)} \subseteq \operatorname{Fun}_n^{(1)} \subseteq \dots$$

on  $\operatorname{Fun}_n^{\operatorname{an}}$ .

**Warning 3.** This is *not* the Krull filtration on the category  $\operatorname{Fun}_n$ . In fact, we have seen that every Noetherian object of  $\operatorname{Fun}_n$  has finite length, so that  $\operatorname{Krull}^0(\operatorname{Fun}_n) = \operatorname{Fun}_n$ .

We now address question (C). We begin by considering the associated graded of the Nil-filtration:

**Proposition 4.** The iterated suspension functor  $\Sigma^n$  induces an equivalence of categories

$$\mathcal{U}/\operatorname{Nil}_1 \to \operatorname{Nil}_n/\operatorname{Nil}_{n+1}$$

*Proof.* We can identify  $\mathcal{U}/\mathrm{Nil}_{n+1}$  with the category  $\mathrm{Fun}_n^{\mathrm{an}}$  of enriched analytic functors from  $\mathrm{Vect}^f$  to  $\mathcal{U}^{\leq n}$ . The Serre class  $\mathrm{Nil}_n/\mathrm{Nil}_{n+1}$  can be identified with the kernel of the further localization obtained by composing these functors with the truncation  $\tau^{\leq n-1}: \mathcal{U}^{\leq n} \to \mathcal{U}^{\leq n-1}$ . This is equivalent to functors which land in the category  $\mathcal{U}^{=n}$  of unstable  $\mathcal{A}$ -modules which are concentrated in degree n. But this category can be identified with the category of vector spaces, via the functor  $V \mapsto \Sigma^n V$ .

We will therefore restrict our attention to the category  $\operatorname{Fun}^{\operatorname{an}} = \operatorname{Fun}_0^{\operatorname{an}}$  consisting of analytic functors from  $\operatorname{Vect}^f$  to  $\operatorname{Vect}$ . This has a filtration by subcategories

$$\operatorname{Fun}^{(0)} \subset \operatorname{Fun}^{(1)} \subset \dots$$

where  $\operatorname{Fun}^{(n)}$  denotes the class of polynomial functors of degree  $\leq n$ .

**Example 5.** Let R be a representation of the symmetric group  $\Sigma_n$ . Then the functor

$$V \mapsto (V^{\otimes n} \otimes R)_{\Sigma_{-}}$$

is a polynomial functor of degree n, which we will denote by  $F_R$ .

The structure of the homogeneous layers  $\operatorname{Fun}^{(n)}/\operatorname{Fun}^{(n-1)}$  can be described by the following result:

**Proposition 6.** Let  $\operatorname{Mod}_{\Sigma_n}$  denote the category of modules over the group ring  $\mathbf{F}_2[\Sigma_n]$ . Then the construction

$$R \mapsto F_B$$

defines a functor  $\operatorname{Mod}_{\Sigma_n} \to \operatorname{Fun}^{(n)}$ . Moreover, the composition

$$\operatorname{Mod}_{\Sigma_n} \to \operatorname{Fun}^{(n)} \to \operatorname{Fun}^{(n)} / \operatorname{Fun}^{(n-1)}$$

is an equivalence of categories.

*Proof.* Let F be a polynomial functor of degree  $\leq n$ . Let S be a set of cardinality n, and let  $\mathbf{F}_2^S$  denote the corresponding n-dimensional vector space over  $\mathbf{F}_2$ . Let R be the kernel of the map

$$F(\mathbf{F}_2^S) \to \prod_{s \in S} F(\mathbf{F}_2^{S - \{s\}}).$$

Then R is a vector space over  $\mathbf{F}_2$ , equipped with an action of the symmetric group  $\Sigma_n$  of permutations of S. Moreover, if F has degree < n, then R vanishes. This construction furnishes a functor  $\operatorname{Fun}^{(n)}/\operatorname{Fun}^{(n-1)} \to \operatorname{Mod}_{\Sigma_n}$  which is inverse to the construction above.

We can summarize our results as follows:

**Theorem 7.** (1) The category U admits a filtration by Serre classes

$$\ldots \subseteq Nil_2 \subseteq Nil_1 \subseteq Nil_0 = \mathcal{U}$$
.

Moreover,  $\mathcal{U}$  embeds fully faithfully into the inverse limit  $\varprojlim \mathcal{U} / \mathrm{Nil}_n$ , and the successive quotients  $\mathrm{Nil}_n / \mathrm{Nil}_{n+1}$  are equivalent to  $\mathrm{Fun}^{\mathrm{an}}$ .

(2) The Krull filtration on  $\mathbb{U}$  induces a filtration on each  $\operatorname{Nil}_n/\operatorname{Nil}_{n+1}$ , which can be identified with the filtration of  $\operatorname{Fun}^{\operatorname{an}}$  by polynomial functors

$$\operatorname{Fun}^{(0)} \subset \operatorname{Fun}^{(1)} \subset \dots$$

(3) Each successive quotient  $\operatorname{Fun}^{(n)}/\operatorname{Fun}^{(n-1)}$  can be identified with the category of representations of the symmetric group  $\Sigma_n$  (in the category of  $\mathbf{F}_2$ -vector spaces).

We conclude this lecture (and this course) with a digression on another topic. We have shown that if G is a finite p-group, then the classifying space BG is an atomic object in the category of p-profinite spaces  $\mathfrak{S}_p^{\vee}$ . However, we have also shown that BG is not atomic in the category of spaces unless G is the trivial group. Nevertheless, some consequences of the atomicity of G still carry over to the setting of spaces: for example, we used the atomicity of BG in  $\mathfrak{S}_p^{\vee}$  to show that every map from BG into a simply connected finite complex is nullhomotopic.

One might try to prove that BG is atomic in  $\mathfrak{S}$  using the same techniques. Of course, such an attempt is doomed to failure, but might still teach us something or yield a weaker result. The basic idea is simple: given an arbitrary space X, we can attempt to compute the mapping space  $X^{BG}$  using an arithmetic square

$$X \longrightarrow \prod_{p} \widehat{X}_{p}$$

$$\downarrow \qquad \qquad \downarrow$$

$$X_{\mathbf{Q}} \longrightarrow (\prod_{p} \widehat{X}_{p})_{\mathbf{Q}}$$

and show that each term in this square behaves well with respect to pushouts in X. Of course, there are potentially many difficulties:

- (1) The space X might fail to be simply connected.
- (2) The space X might fail to be of finite type, in which case the p-profinite completion is not the appropriate thing to put into the arithmetic square.
- (3) We might not be able to assemble local information about pushout squares into global information, since homotopy pushouts and homotopy pullbacks generally do not commute.

Rather than address these questions, we want to discuss a classical result which suggests that problem (1) is not as difficult as it seems:

**Theorem 8.** Let G and H be groups and  $G \star H$  their free product. Let F be any finite group. Then any homomorphism  $\phi : F \to G \star H$  is either conjugate to a homomorphism from F into G or conjugate to a homomorphism from F into H.

**Remark 9.** We can rephrase this result in terms of homotopy theory: any map

$$BF \rightarrow BG \vee BH$$

is homotopic to a map from BF into BG or to a map from BF into BH. This is a kind of "atomicity" property enjoyed by the classifying space BF.

Proof. We define a bipartite graph X as follows: the vertex set of X is  $V_0 \coprod V_1$ , where  $V_0 = (G \star H)/G$  and  $V_1 = (G \star H)/H$ . The edge set of X is  $G \star H$ , where an element  $g \in G \star H$  determines an edge from  $gG \in V_0$  to  $vH \in V_1$ . The graph X is a tree, which admits an action of  $G \star H$  by left translation. Given a homomorphism  $\phi : F \to G \star H$ , we see that the finite group F acts on the tree X. By the Bruhat-Tits fixed point theorem, the fixed point set  $X^F$  is nonempty. In particular,  $X^F$  contains a vertex of X. Without loss of generality, we may assume that this vertex has the form gG, for  $g \in G \star H$ . In this case, conjugation by G carries G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism G to a homomorphism

Of course, this is only the tip of the iceberg as far as what can be proven using these sorts of techniques. For example, a more elaborate version of the same proof can be used to show the following:

• Suppose given injections of groups

$$G_0 \hookleftarrow G \hookrightarrow G_1$$
.

Let F be a finite group. Then the diagram

$$(BG)^{BF} \longrightarrow (BG_0)^{BF}$$

$$\downarrow \qquad \qquad \downarrow$$

$$(BG_1)^{BF} \longrightarrow B(G_0 \coprod_G G_1)^{BF}$$

is a homotopic pushout square.

This raises the following question: exactly how close is BF to being atomic in the category of spaces? It seems likely that a satisfying answer to this question will involve both the sort of combinatorial group theory argument sketched above, and the technology of unstable Steenrod modules developed in these lectures.
