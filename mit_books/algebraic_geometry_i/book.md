## 18.725 Algebraic Geometry I Lecture Notes

Taught by Roman Bezrukavnikov in Fall 2015 Notes taken by Vishal Arul, Yuchen Fu, Sveta Makarova, Lucas Mason-Brown, Jiewon Park and Soohyun Park

## $\mathrm{May}~8,~2016$

## Contents

| Lecture 1: Course Introduction, Zariski topology                  | 3  |
|-------------------------------------------------------------------|----|
| Lecture 2: Affine Varieties                                       | 5  |
| Lecture 3: Projective Varieties, Noether Normalization            | 7  |
| Lecture 4: Grassmannians, Finite and Affine Morphisms             | 11 |
| Lecture 5: More on Finite Morphisms and Irreducible Varieties     | 15 |
| Lecture 6: Function Field, Dominant Maps                          | 17 |
| Lecture 7: Product of Varieties, Separateness                     | 19 |
| Lecture 8: Product Topology, Complete Varieties                   | 21 |
| Lecture 9: Chow's Lemma, Blowups                                  | 24 |
| Lecture 10: Sheaves, Invertible Sheaves on $\mathbb{P}^1$         | 26 |
| Lecture 11: Sheaf Functors and Quasi-coherent Sheaves             | 28 |
| Lecture 12: Quasi-coherent and Coherent Sheaves                   | 30 |
| Lecture 13: Invertible Sheaves                                    | 32 |
| Lecture 14: (Quasi)coherent sheaves on Projective Spaces          | 34 |
| Lecture 15: Divisors and the Picard Group                         | 36 |
| Lecture 16: Bezout's Theorem                                      | 39 |
| Lecture 17: Abel-Jacobi Map, Elliptic Curves                      | 41 |
| Lecture 18: Kähler Differentials                                  | 43 |
| Lecture 19: Smoothness, Canonical Bundles, the Adjunction Formula | 45 |
| Lecture 20: (Co)tangent Bundles of Grassmannians                  | 47 |
| Lecture 21: Riemann-Hurwitz Formula, Chevalley's Theorem          | 49 |

| Lecture 22: | Bertini's Theorem, Coherent Sheves on Curves       | 51         |
|-------------|----------------------------------------------------|------------|
| Lecture 23: | Derived Functors, Existence of Sheaf Cohomology    | 54         |
| Lecture 24: | Birkhoff-Grothendieck, Riemann-Roch, Serre Duality | <b>5</b> 6 |
| Lecture 25: | Proof of Serre Duality                             | <b>5</b> 9 |

## Lecture 1: Course Introduction, Zariski topology

**Some teasers** So what is algebraic geometry? In short, geometry of sets given by algebraic equations. Some examples of questions along this line:

- 1. In 1874, H. Schubert in his book *Calculus of enumerative geometry* proposed the question that given 4 generic lines in the 3-space, how many lines can intersect all 4 of them.
  - The answer is 2. The proof is as follows. Move the lines to a configuration of the form of two pairs, each consists of two intersecting lines. Then there are two lines, one of them passing the two intersection points, the other being the intersection of the two planes defined by each pair. Now we need to show somehow that the answer stays the same if we are truly in a generic position. This is answered by *intersection theory*, a big topic in AG.
- 2. We can generalize this statement. Consider 4 generic polynomials over  $\mathbb{C}$  in 3 variables of degrees  $d_1, d_2, d_3, d_4$ , how many lines intersect the zero sets of each polynomial? The answer is  $2d_1d_2d_3d_4$ . This is given in general by "Schubert calculus."
- 3. Take  $\mathbb{C}^4$ , and 2 generic quadratic polynomials of degree two, how many lines are on the common zero set? The answer is 16.
- 4. For a generic cubic polynomial in 3 variables, how many lines are on the zero set? There are exactly 27 of them. (This is related to the exceptional Lie group  $E_6$ .)

Another major development of AG in the 20th century was on counting the numbers of solutions for polynomial equations over  $\mathbb{F}_q$  where  $q = p^n$ . Here's an example question:  $y^2 = x^3 + 1$ . The answer, assuming  $p = 2 \pmod{3}$  and  $p \neq 2$ , is  $p^n$  if  $p = 2 \pmod{3}$  and  $p \neq 3$ , is  $p^n = 2 \pmod{3}$ .

A third idea is to study "the shape" (i.e. the topology) of the set of solutions of a system of polynomial equations. For instance, if we consider  $y^2 = x^3 = ax + b$  in  $\mathbb{C}^2$ , this will yield ' $T^1 \times T^1$  with a point removed. Another example: if we have a generic degree 4 equations in  $\mathbb{C}^3$  (a K3 surface), then the rank of  $H^2$  (second cohomology) of this space is 22.

**Algebraic Varieties** We always assume working over some algebraically closed field k. Algebraic varieties are glued from affine varieties.

For instance, consider  $\mathbb{A}^n_k = k^n$ . It comes with the coordinate ring  $R = k[x_1, \dots, x_n] = k[\mathbb{A}^n]$ , which is a commutative k-algebra. How do we recover  $k^n$  from  $R = k[x_1, \dots, x_n]$ ? The first answer, the tautological one, is that  $k^n \cong \operatorname{Hom}_{k-\operatorname{alg}}(R, k)$ . Namely, given a point  $(a_1, \dots, a_n)$ , we can map  $x_i$  to  $a_i$ . However, there is a second answer: that  $k^n$  is the set of maximal ideals of R, which we denotes as Spec R.

To see this, first note that  $k^n$  embeds into Spec R. This is simple: you just map each point  $(a_1, \ldots, a_n)$  to the kernel of the map  $R \to \mathbb{C}$  given by  $x_i \mapsto a_i$ . Surjectivity is less trivial: it is the essential Nullstellensatz.

**Theorem 1.1** (Essential Nullstellensatz). If K/k is a field extension, and K is a finitely generated k-algebra, then K/k is algebraic. In particular, if  $k = \overline{k}$ , then K = k.

Assuming this statement, and that  $\mathfrak{m}$  is an maximal ideal, then  $K = R/\mathfrak{m}$  is a field, and it contains k, so K = k, thus  $R = k \oplus \mathfrak{m}$ , thus for each  $x_i$  there's some  $a_i$  such that  $x_i - a_i \in \mathfrak{m}$ , so  $\mathfrak{m}$  is the kernel of  $x_i \mapsto a_i$ .

Proof of essential Nullstellensatz. Let's prove this when k is not countable. (Note in particular this excludes the case of  $\overline{\mathbb{Q}}/\mathbb{Q}$ .) Assume  $t \in K$  is not algebraic over k, then  $k(t) \subseteq K$ . Note that  $(t-a)^{-1} \in k(t)$  for each  $a \in k$ . But K is at most countably dimensional as a vector space over k, so  $(t-a_i)^{-1}$  are linearly dependent, so there is some relation  $\sum_{i} b_i (t-a_i)^{-1} = 0$ . Then after getting rid of the denominator by multiplying by

 $\prod (t-a_i)$ , we obtain a polynomial having t as a zero.

**Definition 1.** A Zariski closed subset in  $k^n$  is a set given by the zero set of polynomial equations.

**Theorem 1.2.** Zariski closed subsets in  $k^n$  are in bijection with radical ideals in  $R = k[x_1, \ldots, x_n]$ . (Recall that I is a radical ideal if R/I has no nilpotents.)

Proof. An ideal I maps to  $Z_I$ , the set of common zeroes of elements of I. A Zariski closed set Z goes to  $I_Z = \{f \mid f \mid_Z = 0\}$ . Clearly  $Z_{I_Z} = Z$ . Need to check  $I_{Z_I} = I$ . Let's first consider  $Z_I = \emptyset$ , then we want I = R. If  $I \neq R$ , then choose  $\mathfrak{m} \supseteq I$ , then we know that  $\mathfrak{m}$  corresponds to some point  $a \in Z_I$ , contradiction. Now in general, if  $f|_{Z_I} = 0$ , then  $f^n \in I$  for some n. Consider the localization  $R_{(f)} = R[t]/(1-ft)$ , which can also be written as  $\{p/f^n \mid p \in R\}$  mod out a certain equivalence relation  $\sim$ . Clearly there is an embedding  $R \to R_{(f)}$ , and hence  $\operatorname{Spec}(R_{(f)}) \hookrightarrow \operatorname{Spec}(R)$ , where the first is the set of  $\{\mathfrak{m} \in R \mid f \notin \mathfrak{m}\}$ , thus  $IR_{(f)}$  is not contained in a maximal ideal, i.e.  $IR_{(f)} = R_{(f)} \implies p/f^n$  for some  $p \in I$ , then  $f^n = p \in I$ .

Corollary 1. There is a Zariski topology on  $\mathbb{A}^n$ , where the closed sets are the Zariski closed sets.

*Proof.* One just need to check the condition for union and intersection.

Let's introduce some notions to begin with. (This can be found as [Kem93], Section 1.1 and 1.2.) A space with function is a topological space X, where we attach to each open set U a k-albegra, denoted by k[U] and called the regular functions on U. They need to satisfy some conditions:

- 1. If  $U = \bigcup_{\alpha} U_{\alpha}$ , and f is regular on U, then  $f|_{U_{\alpha}}$  is regular on  $U_{\alpha}$  for each  $\alpha$ .
- 2. If f is regular on U, then  $D(f) = \{x \in U \mid f(x) \neq 0\}$  is open and 1/f is regular on D(f).

A morphism between spaces with functions is a map  $f: X \to Y$  between spaces, such that if g is regular on U, then  $f^*g$  is regular on  $f^{-1}(U)$ . The map  $f \mapsto f^*$  gives us a mapping  $*: \text{Morphism}(X,Y) \to k - \text{Hom}(k[Y], k[X])$ .

**Definition 2.** An affine variety is a space with functions Y such that \* is bijective for every X and k[Y] a finitely generated k-algebra.

#### Lecture 2: Affine Varieties

**Side Remark** Recall that we introduced three types of questions in the last lecture: counting over  $\mathbb{C}$ , counting over  $\mathbb{F}_q$  and the slope of the set of solutions over  $\mathbb{C}$ . It is worth pointing out that there is indeed a connection between the two latter types, as sketched out by the Weil conjectures.

Last time we defined Spec A, where A is a finitely generated k-algebra with no nilpotents. Namely, Spec  $A = \operatorname{Hom}_{k-alg}(A, k) = \{\text{maximal ideals in } A\}$ . Zariski closed set are defined in [Kem93]. Now recall that there is a bijection between Zariski closed subsets of Spec A and the radical ideals of A. Suppose  $Z_1, Z_2$  correspond to  $I_1, I_2$ , then  $Z_1 \cup Z_2$  corresponds to  $I_1 \cap I_2$ . Note that  $I_1 + I_2$  may not be reduced even if  $Z_1, Z_2$  are varieties. For instance, let A = k[x, y],  $I_1 = (y - x^2)$ ,  $I_2 = (y)$ , then  $A/(I_1 + I_2) = k[x]/x^2$ .

**Theorem 2.1.** Let k[U] denote functions associated with the set U, as specified in last lecture. Then  $k[\operatorname{Spec} A] \cong A$ .

*Proof.* (This was done in [Kem93], Section 1.3-1.5.) Recall that as a set, Spec A is k-Hom(A, k), because each maximal ideal is the kernel of a homomorphism  $A \to k$  and vice versa. So there's a map  $\phi : A \to k$ [Spec A] given by  $a \mapsto (x \mapsto x(a))$ , which we shall prove to be a bijection.

We first want the topological structure on Spec A. This is given by  $Z(I) = \{x \in \text{Spec } A \mid i(x) = 0 \ \forall i \in I\}$ , where I is a subset of A. One can directly check that this gives a topology on Spec A. Next we need to make it a space with functions. The construction is given as:  $k[U] = \{f : U \to k \mid \exists (U_{\alpha}, a_{\alpha}, b_{\alpha}), \bigcup U_{\alpha} =$

 $U, f|_{U_{\alpha}} = \phi(a_{\alpha})/\phi(b_{\alpha}), \phi(b_{\alpha})(x) \neq 0 \ \forall x \in U_{\alpha}\}.$ 

To show injectivity, let  $a \neq 0 \in A$ , then we need to find some  $x : A \to k \in \text{Spec } A$  such that  $\phi(a)(x) = x(a) \neq 0$ . To do so we'd need the following fact, the proof of which is standard commutative algebra:

**Lemma 1** (Noether Normalization). Given A a finitely-generated k-algebra, there exists some algebraically independent elements  $X_1, \ldots, X_d$  over k such that A is a finitely generated  $k[X_1, \ldots, X_d]$ -module.

Apply this fact with the localization  $A_{(a)}$ , which is nonempty because A has no nilpotent (otherwise if 1=0 in the localization ring, then  $a^n=a^n\cdot 1=0$ ), and is finitely generated as we just need to add 1/a to A. Thus we get some  $X_1,\ldots,X_d$  such that  $A_{(a)}\supseteq B=k[X_1,\ldots,X_d]$ , then there is a surjection  $\psi:k-\operatorname{Hom}(A_{(a)},k)\to k-\operatorname{Hom}(B,k)$ . Let  $\varphi\neq 0\in k-\operatorname{Hom}(B,k)$ , and let  $\psi(\tilde{\varphi})=\varphi$ , and let  $x=A\hookrightarrow A_{(a)}\stackrel{\tilde{\varphi}}{\to}k$ , then  $1=x(1)=\tilde{\varphi}(a)\tilde{\varphi}(1/a)=x(a)\tilde{\varphi}(1/a)$ , so  $x(a)\neq 0$ .

Now we need surjectivity. Take  $f \in k[\operatorname{Spec} A]$  and we need to show it is in A. Assume the data is given by  $(U_{\alpha}, a_{\alpha}, b_{\alpha})$ , where we can assume that each  $U_{\alpha} = D(c_{\alpha})$ . By the replacement  $a_{\alpha} \mapsto a_{\alpha}c_{\alpha}, b_{\alpha} \mapsto b_{\alpha}c_{\alpha}$ , one can assume that  $U_{\alpha} = D(b_{\alpha})$ . Since the  $D(b_{\alpha})$  sets cover Spec A, we know that the ideal generated by  $\{b_{\alpha}^2\}_{\alpha}$  corresponds to empty set, thus by Nullstellensatz (c.f. [Kem93], Theorem 1.4.5), there must be some finite

set  $b_1, \ldots, b_m$  and some constants  $z_1, \ldots, z_m \in A$  such that  $\sum_{i=1}^m z_i b_i^2 = 1 \in A$ . Now  $b_\alpha^2 f$  agrees with  $a_\alpha b_\alpha$  both

on  $U_{\alpha}$  and its complement, so they are equal in A, which means  $f = f \cdot 1 = \sum_{i} z_{i}(fb_{i}^{2}) = \sum_{i} z_{i}a_{i}b_{i} \in A$ .  $\square$ 

Note this last part can also give us the following:

**Proposition 1.** Spec A is quasi-compact for any commutative ring A.

*Proof.* Take a covering  $X = \bigcup U_{\alpha}$ , then can pick  $U_{f_{\alpha}} \subseteq U_{\alpha}$ , then we have  $(f_{\alpha}) = 1$ , and thus there's a finite subset  $(f_{d_1}, \ldots, f_{d_n}) = 1$ .

What we really want to say is:

**Theorem 2.2.** Given a space of functions X, X is an affine variety if and only if X = Spec A for a finitely generated commutative ring A with no nilpotents.

*Proof.* Let's show that Spec A is affine; the other direction will be done in the next lecture. Let X be any space with functions, then we need to show that  $*: Morphism(X, \operatorname{Spec} A) \to k - Hom(A, k[X])$  is injective and surjective. For injectivity, let  $f: X \to \operatorname{Spec} A$  be a morphism and let x be any point on X, then  $\delta_{f(x)}$ ,

the evaluation map at f(x), is given by  $\delta_{f(x)}(a) = a(f(x)) = (f^*a)(x)$  for  $a \in A$ , i.e. f(x), equivalently  $\delta_{f(x)}$ , is specified by x and  $f^*$ . On the other hand, define  $*^{-1}$  by  $\delta_{*^{-1}(g)(x)} = \delta_x \circ g$ , then one can check this gives a well-defined inverse to \* and thus \* is bijective.

**Definition 3.** An algebraic variety over k is a space with functions which is a finite union of open subspaces, each one is an affine variety.

**Lemma 2.** A closed subspace in an affine variety is also affine, and global regular functions restrict surjectively.

*Proof.*  $X = \operatorname{Spec} A$ ,  $Z = Z_I$ , I is a radical. Then  $Z_I \cong \operatorname{Spec}(A/I)$ . Surjectivitly follows from the fact that  $k[\operatorname{Spec} A] = A$ .

Corollary 2. A closed subspace of a variety is a variety.

**Theorem 2.3** (Hilbert Basis Theorem).  $k[x_1, \ldots, x_n]$ , and hence any finitely generated k-algebra is Noetherian.

**Corollary 3.** An algebraic variety is a Noetherian topological space (that is, every descending chains of closed subsets terminate; equivalently, every open subset is quasicompact).

Corollary 4. An open subspace of an algebraic variety is an algebraic variety. (Contrast with affine variety.)

*Proof.* Need to check that an open subset of an affine variety is covered by finitely many affine varieties. This follow from quasi-compactness.  $\Box$ 

Combine the two corollaries above, we see that a locally closed subspace (intersection of open and closed) of an algebraic variety is again a variety. However, the union of an open set and a closed set need not be a variety. For an counterexample, consider  $(\mathbb{A}^2 - \{x = 0\}) \cup \{0\}$ .

**Definition 4** (Projective Space). Topologically, the projective space  $\mathbb{P}^n$  is given by the quotient topology  $\mathbb{A}^{n+1} - \{0\}/(x_0, \dots, x_n) \sim (\lambda x_0, \dots, \lambda x_n) \forall \lambda \neq 0$ . A function on  $U \subseteq \mathbb{P}^n$  is regular if its pullback by  $\mathbb{A}^{n+1} - \{0\} \xrightarrow{\pi} \mathbb{P}^n$  is regular on  $\pi^{-1}(U)$ .

## Lecture 3: Projective Varieties, Noether Normalization

**Review of last lecture** Recall that Spec  $A = \text{Hom}_{k-\text{alg}}(A, k)$ . Let I and J be ideals of A. The following question was asked while we were discussing the topology on Spec A.

**Question 1.** When do we have that  $IJ = I \cap J$ ?

**Answer** (From MO.) When  $\operatorname{Tor}_1^A(A/I, A/J) = 0$  ( $\operatorname{Tor}_1^A$  is the derived functor of tensor products  $\otimes_A$ ). For example, we can take A = k[V],  $I = Z_W$ , and  $J = Z_U$ , where U and W are subspaces of a vector space V such that U + W = V.

Last time, we started the proof of the following theorem:

**Theorem 3.1.** Let X be a space with functions. Then, X is affine if and only if  $X = Spec\ A$  for some finitely generated k-algebra A with no nilpotents.

*Proof.* The proof that X is affine if  $X = \operatorname{Spec} A$  for some A was done in the last lecture. It remains to check that  $X = \operatorname{Spec} A$  for some A if X is affine. Assume that X is affine. Note that k[X] =: A is a finitely generated k-algebra which is a nilpotent ring (since it is an algebra of functions). Take  $X' = \operatorname{Spec} A$ . Since X is affine, the isomorphism  $k[X] = A \cong k[X']$  gives a map  $X' \longrightarrow X$ . We also know that X' is affine. So, we get a map  $X \longrightarrow X'$ . Applying the affineness of X and X' to the two compositions, we see that these are inverse isomorphisms and  $X = \operatorname{Spec} A$ .

Closed subvarieties of  $\mathbb{P}^n$  At the end of last lecture, we defined the projective space  $\mathbb{P}^n_k$  over a field k and described the regular functions on it. Recall that  $\mathbb{P}^n_k = \mathbb{A}^{n+1} \setminus \{0\}/k^{\times}$ . This space has an affine cover

$$\mathbb{P}_{k}^{n} = \bigcup_{i=0}^{n} \mathbb{A}_{i}^{n}, \text{ where } \mathbb{A}_{i}^{n} = \{(x_{0}, x_{1}, \dots, x_{n}) : x_{i} \neq 0\}/k^{\times} \cong \{(x_{0}, x_{1}, \dots, x_{i-1}, 1, x_{i+1}, \dots, x_{n})\}. \text{ Note that it}$$

is a disjoint union of locally closed subsets since  $\mathbb{P}^n_k \setminus \mathbb{A}^n_k \cong \mathbb{P}^{n-1}_k$  and  $\mathbb{P}^n = \coprod_{i=0}^n S_i$ , where  $S_i$  is locally closed and isomorphic to  $\mathbb{A}^i$ .

**Example 1.** If  $k = \mathbb{C}$ , we can take  $\mathbb{P}^n_{\mathbb{C}}$  to be a topological space with the complex (classical) topology. Since it a union of cells of even real dimension, we have

$$\dim H^i(\mathbb{P}^n_{\mathbb{C}}) = \begin{cases} 1 & i \text{ even} \\ 0 & i \text{ odd.} \end{cases}$$

Now consider the antipodal map  $S^{2n+1} \twoheadrightarrow \mathbb{P}^n_{\mathbb{C}}$ . Since this map is continuous and onto, it follows that  $\mathbb{P}^n_{\mathbb{C}}$  is compact.

**Example 2.** Suppose that  $k = \mathbb{F}_q$ . Then, we have  $|\mathbb{P}_k^n| = \sum_{i=0}^n q^i = \frac{q^{n+1}-1}{q-1} := [n]_q$  (q-analogues).

**Definition 5.** An algebraic variety is projective if it is isomorphic to a closed subvariety of a projective space.

**Remark 1.** If X is a projective variety over  $\mathbb{C}$ , then X taken in the classical topology is compact.

**Definition 6.** An algebraic variety is quasiprojective if it is a locally closed subvariety in a projective space. Most of the things we use have this property.

**Remark 2.** It is important to check whether we are working with the Zariski topology or the classical topology. If a set is closed in the Zariski topology, it is also closed in the classical topology over  $\mathbb C$  since polynomials are continuous functions. However, a set which is closed in the classical topology may not be Zariski closed.

Next, we describe the closed subvarieties of  $\mathbb{P}^n$ . Note that closed subvarieties in  $\mathbb{P}^n$  correspond to the  $k^{\times}$ -invariant subvarieties of  $\mathbb{A}^{n+1} \setminus \{0\}$ . Let  $V = k[x_0, \dots, x_n]$  and  $X \subset \mathbb{P}^n$  be a closed subvariety. Then, V is a graded vector space  $V = \bigoplus V_n$ , where  $V_n$  is the set of homogenous polynomials of degree n. Now

consider the action of  $t \in k^{\times}$  on V. Since we have  $t|_{V_n} = t^n \mathrm{Id}$ , we have that  $f \in V$  vanishes on X if and only if all of its homogeneous components  $f_n$  vanish on X. Thus, we have that  $I_X$  is a homogeneous (= graded) ideal. If k is algebraically closed, we have the following correspondence ([SH77, p. 41-42]):

closed subvarieties in  $\mathbb{P}^n \longleftrightarrow$  radical (nonunital) homogeneous (= graded) ideals in  $k[x_0,\ldots,x_n]$ 

We can also obtain closed subvarieties of  $\mathbb{P}^n$  by taking projective closures of closed subvarieties X of  $\mathbb{A}^n$ . Recall that there is an open  $\mathbb{A}^n_0 = \{(x_0,\ldots,x_n): x_0 \neq 0\} = \mathbb{A}^n \subset \mathbb{P}^n$ . For closed  $X \subset \mathbb{A}^n$ , we get  $\overline{X}$ , which is the closure of X in  $\mathbb{P}^n$ . If  $P \in k[Y_1,\ldots,Y_n]$  vanishes on X, then  $\tilde{P} = x_0^d P\left(\frac{x_1}{x_0},\frac{x_2}{x_0},\ldots,\frac{x_n}{x_0}\right)$  vanishes on  $\overline{X}$ , where  $d = \deg P$ . Note that  $P = \tilde{P}(1,Y_1,\ldots,Y_n)$ . For example, if  $P = X^3 - Y^2 - Y + 1$ , then  $\tilde{P} = X^3 - ZY^2 - Z^2Y + Z^3$ . We also have that  $I_{\overline{X}} = (\tilde{P}: P \in I_X)$ .

**Example 3** (Linear subvarieties in  $\mathbb{P}^n$ ). If  $I_X$  can be generated by linear polynomials, then X can be sent to  $\{(x_0:\dots:x_n):x_{i+1}=\dots=x_n=0\}$  by a linear change of variables (i.e. invariant matrices acting on  $\mathbb{P}^n$ ). Let  $X\subset\mathbb{P}^2$  be a degree d irreducible curve and  $I_X=(P)$ , where  $P\in k[X,Y,Z]$  is a degree d irreducible polynomial.

Case 1: d = 1 This is the case where  $X = \mathbb{P}^1$ .

Case 2: d=2 (char  $k \neq 2$ ) Claim:  $X \cong \mathbb{P}^1$  again. Proof sketch: By linear algebra, all irreducible degree 2 polynomials in 3 variables are permuted transitively by a linear change of variables. Without loss of generality, we can assume that  $P = XY - Z^2$ . On  $\mathbb{A}^2$  ( $Z \neq 0$ ), we get (XY = 1)  $\cong \mathbb{A}^1 \setminus \{0\}$ . Exercise: Finish this.

Here is another construction of the isomorphism  $X \cong \mathbb{P}^1$ . Fix  $x \in X$ . Consider the following correspondences:

 $\{lines\ in\ \mathbb{P}^1\ passing\ through\ x\} \leftrightarrow \{dim.\ 2\ subvarieties\ of\ \mathbb{A}^3 := V\ containing\ L_x\} \leftrightarrow \{dim.\ 1\ subvarieties\ in\ V/L_x\}$ 

Note that the last set is isomorphic to  $\mathbb{P}^1$ . Here,  $L_x \subset \mathbb{A}^3$  is the set of lines passing through x. Now construct the map  $X \setminus x \longrightarrow \mathbb{P}^1$  sending y to the line passing through x and y. Exercise: Finish this.

Case 3: d=3 X is not necessarily isomorphic to  $\mathbb{P}^1$  in this case. For example, suppose that X is an elliptic curve. Claim: By a linear change of variables, we can get X to the Weierstrass normal form  $y^2=x^3+ax+b$ . The closure of this curve in  $\mathbb{P}^2$  intersects the line at infinity at 1 point:

$$ZY^2 = X^3 + aXZ^2 + bZ^3$$
 
$$Z = 0 \Rightarrow X = 0$$
 
$$Intersection\ point: (0:1:0)$$

Note that  $\mathbb{P}^1$  also has one point at infinity. Comparing the set regular functions on the affine parts of X and  $\mathbb{P}^1$  and noting that  $k[X,Y]/(Y^2-X^3-aX-b)$  is not generated by one element (has a filtration with the associated graded ring  $k[X,Y]/(Y^2=X^2)$ ), we find that  $X \ncong \mathbb{P}^1$ .

#### Noether normalization lemma and applications

**Theorem 3.2.** (Noether normalization lemma)

Let A be a finitely generated k-algebra, where k is any field (not necessarily algebraically closed). Then, we can find  $B \subset A$  such that  $B \cong k[x_1, \ldots, x_n]$  for some n and A is finitely generated as a B-module.

Remark 3. Here is a "geometric" version of the theorem which has to do with subvarieties in affine space:

If  $B \subset A$  and A is a finitely generated B-module, then the map Spec  $A \longrightarrow \operatorname{Spec} B$  is onto and has finite fibers.

We will prove the theorem in the case where k is infinite.

**Lemma 3.** Take  $P \in k[x_1, ..., x_n]$  be a nonconstant polynomial and let  $d = \deg P$ . There is a linear change of variables such that P has for form  $x_n^d + (terms \ of \ \deg_{x_n} < d)$ .

Proof. Write  $x_i = x_i' + \lambda_i x_n'$  for  $1 \le i \le n-1$  and  $x_n' = \lambda_n x_n$ . If  $d = \deg P$  and  $P = P_d + (\text{terms of } \deg < d)$ , then  $P(x_i) = x_n^d P_d(\lambda_1, \ldots, \lambda_n) + (\text{terms of } \deg_{x_n} < d)$ . Thus, we would like to find  $\lambda_1, \ldots, \lambda_n$  such that  $P_d(\lambda_1, \ldots, \lambda_n) = 1$ . Since  $P_d$  is homogeneous, it suffices to show that there exist  $\mu_1, \ldots, \mu_n$  such that  $P_d(\mu_1, \ldots, \mu_n) \ne 0$ . Thus, the proof reduces to the following claim:

Claim: A nonzero polynomial over an infinite field takes nonzero values.

This can be proved using induction in number of variables.

Now we begin the proof of the Noether normalization lemma.

Proof. Since A is finitely generated, we have a surjection  $\phi: k[x_1,\ldots,x_n] \to A$ . We use induction on n. Let  $I = \ker \phi$ . If I = (0), we are done. Now suppose that  $I \neq (0)$ . Take  $0 \neq P \in I$ . By the lemma above, we can assume without loss of generality that  $P = x_n^d + (\operatorname{terms of deg}_{x_n} < d)$ . Note that  $k[x_1,\ldots,x_n]/(P) \to A$  and  $k[x_1,\ldots,x_n]/(P)$  is finite over  $k[x_1,\ldots,x_{n-1}]$ . Let  $A' = \phi(k[x_1,\ldots,x_{n-1}])$ . Applying the induction assumption to A', there exists  $B \cong k[x_1,\ldots,x_m]$  such that A' is finite over B. Since A is finite over A', A is finite over A' and we are done.

Next, we can show that  $k[x_1, \ldots, x_n]$  is Noetherian.

**Proposition 2.** (Hilbert basis theorem)  $k[x_1, ..., x_n]$  is Noetherian.

*Proof.* It is enough to check that every ideal is finitely generated. As above, we use induction on n. Let I be a nonzero ideal of A and  $0 \neq P$  be an element of I. Without loss of generality, we can assume that A/(P) is finite as a module over  $k[x_1, \ldots, x_{n-1}]$ . Since  $k[x_1, \ldots, x_{n-1}]$  is Noetherian by induction, every submodule of A/(P) is finitely generated over  $k[x_1, \ldots, x_{n-1}]$ . Hence, I/(P) is finitely generated, which implies that I is finitely generated.

We need another result in order to finish the proof of the "essential Nullstellensatz" from the first lecture.

#### Lemma 4. (Nakayama lemma)

Let M be a finitely generated module over a commutative ring A. If I is an ideal of A such that IM = M, then there exists  $a \in A$  such that aM = 0 and  $a \equiv 1 \pmod{I}$ .

*Proof.* Let  $\{m_i\}$  be generators of M. Then,  $m_i = \sum a_{ij}m_j$ , where  $a_{ij} \in I$ . Then, we can set  $a = \det(1 - a_{ij})$ .

Finally, we can finish the proof of the essential Nullstellensatz.

**Theorem 3.3.** ("essential Nullstellensatz") Let A be a finitely generated k-algebra. If A is a field, then A/k is algebraic.

*Proof.* Since A is a finitely generated k-algebra, it follows from the Noether normalization lemma that there exists  $B \cong k[x_1, \ldots, x_n]$  such that  $A \supset B$  and A is finitely generated as a B-module. If n = 0, we are done since A/k would be a finite extension, which must be algebraic. Suppose that  $n \geq 1$ . Then,  $A \supset \mathfrak{m}$ , where  $\mathfrak{m}$  is a maximal ideal of B. It follows from Nakayama's lemma that  $\mathfrak{m}A \neq A$ . Otherwise, there exists  $b \in B$  such that bA = 0 and  $b \equiv 1 \pmod{\mathfrak{m}}$ . This would imply that  $bB = 0 \Rightarrow B/\mathfrak{m} = 0$ , which is impossible since  $\mathfrak{m} \subseteq B$ . Since A has a proper ideal  $\mathfrak{m}A$ , it is not a field.

**Irreducibility** Here is a list of some definitions and properties of topological spaces which will be discussed in more detail in the next lecture.

**Definition 7.** A topological space is irreducible if any two nonempty open subsets intersect. Equivalently, it is not a union of two proper closed subsets. Another equivalent definition is a space where a nonempty open subset is dense (sort of opposite to Hausdorff...).

Remark 4. An irreducible topological space is connected, but a connected space is not necessarily irreducible.

Remark 5. Every variety is a union of irreducible pieces.

**Proposition 3.** Spec A is irreducible if and only if A has no zerodivisors.

**Definition 8.** A component of a topological space is a maximal irreducible closed subset.

**Proposition 4.** A Noetherian topological space is the union of its components (finite in number).

Corollary 5. We have the following correspondences:

Irreducible closed subsets in Spec  $A \leftrightarrow \text{Prime ideals}$  in A

Components  $\leftrightarrow$  minimal prime ideals (i.e. prime ideals not containing any other prime ideals)

Corollary 6.  $0 = \bigcap$  (minimal prime ideals).

## Lecture 4: Grassmannians, Finite and Affine Morphisms

#### Remarks on last time

1. Last time, we proved the *Noether normalization lemma*: If A is a finitely generated k-algebra, then, A contains  $B \cong k[x_1, \ldots, x_n]$  (free subring) such that A is a finitely generated B-module.

Question: When is A a finitely generated B-module?

Answer: If and only if A is a Cohen-Macauley ring. In particular, this doesn't depend on the choice of B (which is very not unique...)

2. A remark on the homework problem (Problem 3(e) of Problem Set 2):

The answer to the optional problem:  $|\mathbb{P}^{2n}(\mathbb{F}_q)| = (1 + \ldots + q^{2n}) + q^n$ . This is a quadric in  $\mathbb{P}^{2n+1}(\mathbb{F}_q)$ . The "middle" term  $q^n$  also comes up elsewhere and this generalizes to the Weil conjectures.

Also, the same problem can be used to compute  $H^*(Q_{\mathbb{C}})$  (classical topology). This has the same cohomology as projective space for the middle degree.  $H^*$  is 1-dimensional in degree  $2, 4, \ldots, 4n$  except for  $H^{2n}$ , which is 2-dimensional. The fact that the cohomology  $H^*$  is the same as for  $\mathbb{CP}^n$  except for the middle degree generalizes to the *Lefschetz Hyperplane Theorem*, which will be covered in 18.726.

3. On the isomorphism  $X \cong \mathbb{P}^1$  for irreducible degree 2 curves  $X \subset \mathbb{P}^2$ :

The degree 2 curve  $C = (XY - Z^2)$  in  $\mathbb{P}^2$  from last lecture can be covered by two affine open pieces:

(a) 
$$X \neq 0$$
:  $a = \frac{Y}{X}$ ,  $b = \frac{Z}{X}$ ,  $(a = b^2) \cong \mathbb{A}^1 = U_1$ 

(b) 
$$Y \neq 0$$
:  $a' = \frac{X}{Y}$ ,  $b' = \frac{Z}{Y}$ ,  $(a' = b'^2) \cong \mathbb{A}^1 = U_2$ 

Note that  $U_1 \cap U_2 \cong \mathbb{A}^1 \setminus \{0\}$ .

By changing coordinates, we can take the degree 2 curve in  $\mathbb{P}^2$  to be  $X^2+Y^2=Z^2$ . Connect points in a quadric to a fixed point. In practice, we can work with the point (1:0:1). We identify the set of all lines through a given point with  $\mathbb{P}^1$ . Taking this to affine coordinates, we send  $(a,b)\mapsto \frac{a-1}{b}$ . Writing a=tb+1, we express a and b via t. Then, we get a bijection  $\mathbb{P}^1_k\longleftrightarrow X$ . This map sends points with rational coordinates to points with rational coordinates. One application is the classification of Pythagorean triples. (Exercise: Work out the details.)

#### Noetherian topological spaces and irreducible components

**Proposition 5.** A Noetherian topological space X is a finite union of its components (i.e. maximal irreducible subsets).

**Remark 6.** Here, we can see that the condition that X is Noetherian can be an analogue of compactness.

**Lemma 5.** A Noetherian topological space X is a finite union of closed irreducible subsets.

*Proof.* We are done if X is irreducible. Suppose that X is *not* such a finite union. Write  $X = X_1 \cup X_2$ , where  $X_1$  and  $X_2$  are proper closed subsets of X. If the claim is false, then one of either  $X_1$  or  $X_2$  is not a union of finitely many irreducibles. Continuing this process, we get a sequence of closed subsets  $X \supsetneq X_1 \supsetneq X_2 \supsetneq \cdots$ , which contradicts the assumption that X is Noetherian.

Now we begin the proof of the proposition.

*Proof.* Write  $X = \bigcup_{i=1}^{n} X_i$ , where the  $X_i$  are closed irreducible subsets of X. Without loss of generality, we

can assume that none of the  $X_i$  are a subset of another. Then,  $X_i$  is not a subset of  $\bigcup_{i \neq i} X_i$  (follows from

irreducibility). Otherwise, we would have that  $X_i$  is a union of proper closed subsets  $X_j \cap X_i$ . Since every irreducible closed subset  $Z \subset X$  is a subset of  $X_i$  for some i, the  $X_i$  are exactly the components (i.e. maximal irreducible closed subsets) of X.

**Remark 7.** A lot of things are *not* Noetherian in the classical topology (e.g.  $\mathbb{R}^n$ ).

Corollary 7. A radical ideal in a finitely generated ring without nilpotents A is a finite intersection of prime ideals.

Remark 8. This gives us a correspondence

prime ideals of  $A \longleftrightarrow$  irreducible subsets of Spec A.

Proof. Let I be a radical ideal of A. Then,  $I = I_Z$  for some closed subset  $Z \subset \operatorname{Spec} A$ . Since Z is Noetherian,  $Z = \bigcup_{i=1}^n Z_i$ , where the  $Z_i$  are irreducible components of Z. Then,  $I = \bigcap_{i=1}^n I_{Z_i}$ . Note that  $I_{Z_i}$  is prime since  $Z_i$  is irreducible. Thus, I is a finite intersection of prime ideals.

Claim: Spec A is irreducible if and only if A has no zerodivisors.

**Corollary 8.** A closed subset  $Z \subset Spec\ A$  is irreducible if and only if  $I_Z$  is prime.

Now we begin the proof of the claim.

Proof. Let f and g be nonzero elements of  $A \subset \operatorname{Fun}_k(\operatorname{Spec} A)$ , where  $\operatorname{Fun}_k(\operatorname{Spec} A)$  is the set of k-valued functions on  $\operatorname{Spec} A$ . Suppose that  $\operatorname{Spec} A$  is irreducible. If fg = 0, then  $Z_f \cup Z_g = \operatorname{Spec} A$ , where  $Z_f$  are the zeros of f and  $Z_g$  are the zeros of g. If  $Z_f, Z_g \subsetneq \operatorname{Spec} A$ , then  $\operatorname{Spec} A$  is reducible. Thus, we must either have f = 0 or g = 0 and A has no zerodivisors.

Conversely, suppose that Spec A is not irreducible. Let X = Spec A. Then, we can write  $X = Z_1 \cup Z_2$ , where  $Z_1, Z_2 \subseteq X$  are proper closed subsets of X. Since proper closed subsets correspond to nonzero ideals, we can pick nonzero  $f \in I_{Z_1}$  and nonzero  $g \in I_{Z_2}$ . Then, fg = 0 and f and g are zerodivisors of A.

An example of a projective variety (Grassmannians) Last time, we started to discuss some properties of projective varieties and looked at linear subvarieties of  $\mathbb{P}^n$ . Here is another example of a projective variety.

**Example 4.** The Grassmannian Gr(k,n) is the set of linear subspaces of dimension k in the n-dimensional vector space  $K^n := V$ . For example,  $Gr(1,n) = \mathbb{P}^{n-1}$ . Here, we have the "usual" topology and regular functions on  $\mathbb{P}^{n-1}$ .

In general, the topology and regular functions are characterized as follows:

Let W be a k-dimensional subspace of V with complement U (i.e.  $V = W \oplus U$ ). If  $T \in Gr(k, n)$  is transversal to U (i.e.  $T \cap U = \{0\}$ ), then T is the graph of a unique linear map  $W \longrightarrow U$ . In other words, we have

$$\begin{split} \{T \in Gr(k,n): T \cap U &= \{0\}\} = \operatorname{Hom}_k(W,U) \\ &\cong Mat_{k,n-k}(K) \\ &\cong \mathbb{A}^{k(n-k)}. \end{split}$$

where  $Mat_{k,n-k}(K)$  is the set of  $k \times (n-k)$  matrices with entries in K.

We require that this subset is open and that the isomorphism with  $\mathbb{A}^{k(n-k)}$  is an isomorphism of varieties.

Notation:  $\mathbb{P}V := \mathbb{P}^n$  is the projectivization of  $V = k^n$  (choose a basis for this).

**Theorem 4.1.** This defines a projective algebraic variety. The embedding of Gr(k,n) into projective space is defined by  $W \mapsto the$  line  $\bigwedge^k W \subset \bigwedge^k V$ .

Claim: This map realizes Gr(k,n) as a closed subvariety in  $\mathbb{P}\left(\bigwedge^k V\right) = \mathbb{P}^{\binom{n}{k}-1}$ .

**Example 5.** Consider the case n=4 and k=2. These are lines in  $\mathbb{P}^3$ .

There is a lemma from linear algebra which gives a basic classification of elements of  $\bigwedge^2 V$ .

**Lemma 6.** Take  $\omega \in \bigwedge^2 V$ . If  $\omega = v_1 \wedge v_2$ , then  $\omega \wedge \omega \in \bigwedge^4 V = 0$ . If dim V = 4, then the converse holds.

*Proof.* An element  $\omega$  of  $\bigwedge^2 V$  can be thought of as a bilinear skew form (2-form) of the 4-dimensional vector space  $V^*$ . Note that  $\ker \omega$  is of even dimension. If  $\dim \ker \omega = 0$ , then  $\omega = v_1 \wedge v_2 \wedge v_3 \wedge v_4$  for some basis  $\langle v_1, v_2, v_3, v_4 \rangle$  of V. If  $\dim \ker \omega = 2$  (pullback from 3-dimensional quotient), then  $\omega = v_1 \wedge v_2$  for some  $v_1, v_2$ . Finally,  $\omega = 0$  if  $\dim \ker \omega = 4$ , then the form  $\omega = 0$ .

Thus, Gr(2,4) is isomorphic to a quadric in  $\mathbb{P}^5$  and  $Gr(2,4) \cong Q(\mathbb{P}^5)$ , where Q is defined by  $\omega \wedge \omega = 0$ . (Exercise: Show this is an isomorphism of varieties.) Using some linear algebra, we can show that the quadratic form is not degenerate.

For more details on work above and on Grassmannians in general: See Chapter 6 of Algebraic Geometry (1992) by Joe Harris or p. 42 – 44 (in 3rd edition) in Section 1.4.1 ("Closed Subsets of Projective Space") of Basic Algebraic Geometry 1 by Igor Shafarevich.

#### Finite and affine morphisms

**Definition 9.** A morphism of algebraic varieties  $f: X \longrightarrow Y$  is called affine if Y has an open cover  $Y = \bigcup U_i$  where the  $U_i$  are affine open pieces such that the  $f^{-1}(U_i) \subset X$  are affine.

The affine pieces allow us to use commutative algebra. Note that we have an equivalence of categories

 $\{Affine \ varieties\} \cong \{Finitely \ generated \ k-algebras \ with \ no \ nilpotents\},\$ 

where the second category is the opposite category of the first one.

**Definition 10.** The morphism f is finite if there is an affine open cover  $Y = \bigcup U_i$  such that  $f^{-1}(U_i) = Spec\ A$  and  $U_i = Spec\ B$  with A a finitely generated B-module (see Noether normalization theorem/Noether's lemma).

This reduces everything to commutative algebra locally on a line.

**Lemma 7.** A finite map satisfies the following properties:

- 1. It is closed:  $f(Z) \subset Y$  is closed for every closed  $Z \subset X$ .
- 2. It has finite fibers.

**Corollary 9.** If  $B \subset A$  and A is finitely generated over B as a B-module ("A is finite over B"), then  $Spec\ A \longrightarrow Spec\ B$  has finite nonempty fibers.

*Proof.* We only need to check that the map Spec  $A \longrightarrow \operatorname{Spec} B$  is onto. The image is *not* contained in  $Z_I$  for all nonzero  $I \subset B$  since  $B \subset A$ . Otherwise, we would have an ideal of B which kills A. Since a finite map is closed, we have that the map is surjective.

Now we begin the proof of the lemma (use similar ideas as last time) (compare with Lemma 2.4.3 on p. 19 of Kempf).

*Proof.* Let  $f: X \longrightarrow Y$  be a finite map. We can assume X and Y are affine (statement local on line). Since the composition of two finite maps is finite, we can also assume that Z = X. Write  $X = \operatorname{Spec} A$  and  $Y = \operatorname{Spec} B$  and let  $I = \operatorname{Ann}_B(A)$ . This is a radical ideal since A has no nilpotents. Since I is a radical ideal, it corresponds to the closed subset  $Z_I$  of  $\operatorname{Spec} B$ . Then, we have the surjection  $X \to Z_I$  and  $f(X) \subset Z_I$ .

For  $x \in Z_I$ , we have that  $A/\mathfrak{m}_x A \neq 0$  by Nakayama's lemma. Otherwise, there exists  $r \equiv 1 \pmod{\mathfrak{m}_x}$  such that rA = 0. However, this is not possible since  $r \equiv 1 \pmod{\mathfrak{m}_x} \Rightarrow r \notin I$ . It follows from Hilbert's Nullstellensatz that  $Z_I \subset f(X)$ . Since A is a finite B-module,  $A/\mathfrak{m}_x A$  is a finite dimensional nonzero k-algebra. This means that there exists a maximal ideal  $\mathfrak{m}_x$  such that Spec  $A/\mathfrak{m}_x A = \operatorname{Hom}(A/\mathfrak{m}_x A, k)$  is a finite nonempty set (nonempty since quotient ring nonzero). Thus, f has finite nonempty fibers.

**Example 6.** (Examples of affine morphisms)

- 1. Let  $Z \subset X$  be a closed subvariety. Then, the map  $i: Z \hookrightarrow X$  is affine and finite since Spec A/I is a closed subset of Spec A (this is a local question). Any affine open covering of X works.
- 2. Let Y be any algebraic variety and  $X = Y \setminus Z_f$ , where  $f \in k[X]$ . Consider the open embedding  $X \hookrightarrow Y$ . This map is affine, but usually not finite. Locally, it looks like Spec  $A_{(f)} = A[t]/(1 tf) \longrightarrow \text{Spec } A$ .

**Example 7.** The morphism  $\mathbb{A}^2 \setminus \{0\} \longrightarrow \mathbb{A}^2$  is *not* affine. This is similar to an exercise in the homework (Problem 3 of Problem Set 1). It actually follows from this and the exactness of localization. Let  $U \subset \mathbb{A}^2$  be an open neighborhood of 0 such that  $U = \mathbb{A}^2 \setminus Z_f$  for some f. Since  $k[U] = k[U \setminus \{0\}]$ ,  $U \setminus \{0\}$  is not affine. We also have a short exact sequence

$$0 \longrightarrow k[U \setminus \{0\}] \longrightarrow k[U_1] \oplus k[U_2] \longrightarrow k[U_1 \cap U_2],$$

where  $U = U_1 \cup U_2$  ( $U_1 = (X \neq 0)$ ,  $U_2 = (Y \neq 0)$ ). The sequence above is exact because it is obtained from the corresponding sequence in  $\mathbb{A}^2$  by localization, which is an exact functor. Thus, there is no affine neighborhood of 0 whose complement is affine.

#### Preview of next lecture

**Lemma 8.** Let  $Z_1 \subsetneq Z_2$  be irreducible closed subsets of an algebraic variety X. If  $f: X \longrightarrow Y$  is a finite morphism, then  $f(Z_1) \subsetneq f(Z_2)$ .

Note that  $f(Z_1)$  and  $f(Z_2)$  are closed by the previous lemma. We also have that the image of an irreducible set is irreducible. This lemma shows that the images are actually distinct. We will check this result (see Lemma 2.4.4 on p. 19 of Kempf) in the next lecture.

**Definition 11.** The *dimension* of a Noetherian topological space is the maximal number such that there exists a chain  $X \supset Z_n \supseteq Z_{n-1} \supseteq Z_{n-2} \supseteq \cdots \supseteq Z_0$  of irreducible subsets in X.

For example, the dimension of a point is equal to 0.

**Remark 9.** The dimension may not necessarily be finite since the Noetherian condition is only for a *given* chain.

Here are some facts about the dimension of a Noetherian topological space:

- $\dim \mathbb{A}^n = n$
- If  $X = \bigcup_{i=1}^{n} U_i$ , then dim  $X = \max_{i} \dim U_i$ .
- If  $f: X \longrightarrow Y$  is a finite and surjective morphism, then  $\dim X = \dim Y$ .

## Lecture 5: More on Finite Morphisms and Irreducible Varieties

**Lemma 9.** Let  $f: X \to Y$  be a finite map of varieties and  $Z_1 \subsetneq Z_2$  irreducible subvarieties of X. Then  $f(Z_1) \subsetneq f(Z_2)$ .

*Proof.* We can assume WLOG that  $f: X = Spec(A) \to Spec(B) = Y$  is surjective and  $Z_2 = X$ . Pick a nonzero function  $g \in I(Z_1)$ . Since f is finite, the ring map  $B \to A$  turns A into a finitely-generated B-module. In particular, the B-subalgebra of A generated by g is finitely-generated as a B-module. Hence,

$$g^n = \sum_{i=0}^{n-1} h_i g^i$$
 for some natural number  $n$  and  $h_0 \neq 0$ . Since  $h_0 = g^n - \sum_{i=1}^{n-1} h_i g^i$  vanishes on  $Z_1$ ,  $h_0$  vanishes on  $f(Z_1)$ .

**Lemma 10.** If  $f: X \to Y$  is a finite surjection of varieties, then dim(X) = dim(Y).

Proof. Let  $X_0 \subsetneq X_1 \subsetneq ... \subsetneq X_n$  be any chain of non-empty irreducible closed subsets of X. Set  $Y_i = f(X_i)$ . Since f is continuous,  $\{Y_i\}$  are irreducible and since f is finite  $\{Y_i\}$  are closed. By the previous lemma, the sequence  $Y_0 \subset ... \subset Y_n$  is strictly increasing. Hence,  $dim(Y) \geq dim(X)$ . Conversely, let  $Y_0 \subsetneq Y_1 \subsetneq ... \subsetneq Y_m$  be a chain of non-empty irreducible closed subsets of Y. We wish to show that there is a sequence (of non-empty irreducible closed subsets)  $X_0 \subsetneq ... \subset X_m$  of X such that  $f(X_i) = Y_i$ . Write  $f^{-1}Y_m$  as a union of irreducible components  $V_1 \cup ... \cup V_t$ . Since f is surjective and finite,  $Y_m = f(V_1) \cup ... \cup f(V_t)$ , where  $f(V_t)$  are closed and irreducible. Since  $Y_m$  is irreducible, we must have  $Y_m = f(V_j)$  for some index j. By induction on m, we may find a chain of non-empty closed irreducibles  $X_0 \subsetneq ... \subsetneq X_{m-1}$  of  $V_j$  with  $f(X_i) = Y_i$ . Then  $X_0 \subsetneq ... \subsetneq X_{m-1} \subsetneq V_j$  is the desired sequence in X.

Theorem 5.1.  $dim(\mathbb{A}^n) = n$ 

Proof.  $dim(\mathbb{A}^n) \geq n$  is clear. Suppose  $Z_0 \subsetneq ... \subsetneq Z_m$  is a saturated chain of non-empty closed irreducible subsets of  $\mathbb{A}^n$ . We need to show that  $m \leq n$ . Then  $Z_m = \mathbb{A}^n$  and  $Z_{m-1}$  is a closed, proper subset of  $\mathbb{A}^n$ . In particular, one can find a non-constant function  $g \in k[X_1, ..., X_n]$  such that  $Z_{m-1} \subseteq Z(g)$ . By (the proof of) Noether normalization, there is a finite surjective morphism  $Z(g) \to \mathbb{A}^{n-1}$ . Then the previous lemma implies  $dim(Z(g)) = dim(\mathbb{A}^{n-1})$ . Inducting on n, we can assume  $dim(\mathbb{A}^{n-1}) = n-1$ . Hence  $m-1 \leq dim(Z(g)) = dim(\mathbb{A}^{n-1}) = n-1$ , which completes the proof.

Corollary 10. If X is a hypersurface in  $\mathbb{A}^n$  defined by a non-constant polynomial then  $\dim(X) = n - 1$ .

Corollary 11. Every variety has finite dimension.

We now return to curves.

**Proposition 6.** All irreducible curves over a given field (or even various fields of equal cardinality!) are homeomorphic

*Proof.* From the definition of dimension it is clear that a closed irreducible subset of an irreducible curve X is either zero dimensional or X. Any proper closed subset of X is therefore finite. Hence, any bijection between irreducible curves is a homeomorphism. But a curve over a field k has as many points as k. The proposition follows.

**Definition 12.** Let  $X \subset \mathbb{A}^n$  be a hypersurface defined by a polynomial g. Write g as a sum of homogenous components  $g = g_m + g_{m+1} + ...$  with  $g_m \neq 0$ . If  $0 \in X$ , the multiplicity of X at 0 is defined to be the natural number m. The multiplicity at  $p \in X$  is the multiplicity at 0 after applying a linear change of coordinates mapping p to 0.

**Definition 13.** Let X, Y be two curves in  $\mathbb{A}^2$  with no common component and (a,b) be an intersection point. If  $I_X$  and  $I_Y$  are the ideals in k[x,y] defining X and Y, respectively. Then  $V = k[x,y]/(I_X + I_Y)$  is a finite dimensional vector spaces and multiplication by x,y induce two commuting operators on V. The multiplicity of intersection of X and Y at (a,b) is defined as dimension of the common generalized eigenspace of the two operators, with eigenvalues a,b respectively.

**Theorem 5.2** (Bezout). Let  $X,Y \subset \mathbb{P}^2$  be curves without a common component, of degree d and e, respectively. Then  $X \cap Y$  contains de points, counted with multiplicities.

*Proof.* Proof in lecture notes from 11/5.

**Theorem 5.3** (Pascal). Let Q be a circle in  $\mathbb{P}^2$  and X a hexagon inscribed in C. Then the three pairs of opposite sides of X intersect at three points which lie on a straight line.

Proof. Let A, B, C be linear equations of three pairwise nonintersecting sides of our hexagon inscribed in Q and A', B', C' be the equations of the remaining three ones with A' opposite to A etc. Pick a 7th point on Q and consider a degree 3 homogeneous polynomial P=ABC - t A'B'C' where t is such that P vanishes at the chosen 7th point. By Bezout's theorem, the intersection of Q with a deg 3 curve has at most 6 points, unless they have a common component. Since P has at least 7 zeroes, the latter must be true. Hence, the vanishing locus of P is the union of Q with some other component, which has to be a line P by a degree count. Now the intersection point of P and P has to lie on P, as well as that of P with P and P with P.

**Theorem 5.4.** Let X be an irreducible variety of dimension n and let g be a non-constant function on X. Then any irreducible component of Z(g) has dimension n-1.

**Lemma 11.**  $dim(Z(g)) \ge n - 1$ .

Proof. The special case  $X = \mathbb{A}^n$  is proved above. We will reduce to this special case by Noether's lemma: choose  $B = k[x_1, ..., x_n] \subset k[X] = A$  such that A is a finitely-generated B-module. Then g is the root of some monic irreducible polynomial  $P \in B[t] = k[x_1, ..., x_n, t]$ . Write  $P = a_0 + a_1t + ... + t^n$  with  $a_i \in B$ . The inclusion  $B \subset A$  descends to a map  $B/(a_0) \to A/(g)$ . It is enough to show that the map of spectra  $Spec(A/(g)) \to Spec(B/(a_0))$  is surjective. Let C = B[t]/(P) and factor  $B \subset A$  as  $B \subset C \subset A$ . Spec(C) is irreducible of dimension n. Thus  $\pi : Spec(A) \to Spec(C)$  is onto, so the preimage  $\pi^{-1}(Z(t)) = Z(g)$  maps onto Z(t). But  $B/(a_0) \subset C/(t) = B/(free terms of polynomials in <math>P$ ).

**Lemma 12.** Let X be an irreducible variety and  $U \subset X$  a non-empty open subset. Then  $\dim(U) = \dim(X)$ .

Proof. If we replace X by  $\mathbb{A}^n$  the lemma is clear:  $dim(U) \leq dim(X)$  since  $U \subseteq X$  and the chain (point in U)  $\subseteq$  line  $\subseteq ... \subseteq \mathbb{A}^n$  of closed irreducibles in U shows that  $dim(U) \geq dim(X)$ . For X affine, use Noether's lemma to get a finite surjection  $\pi: X \to \mathbb{A}^n$ . Since  $\pi$  is closed,  $V = \mathbb{A}^n - \pi(X - U)$  is open. Let  $U' = \pi^{-1}V$ . Then  $\pi: U' \to V$  is a finite surjection. Hence, dim(U') = dim(V) = n. On the other hand,  $U' \subseteq U$  so  $dim(U') \leq dim(U) \leq dim(X) = n$ . So dim(U) = n as desired. For general X, reduce to the affine case by using  $dim(X) = \max\{dim(U); U \text{ affine}\}$ .

Proof of Theorem 5.4. Assume Z is a component of Z(g) and  $dim(Z) \leq dim(X) - 2$ . We can find an open affine subvariety U of X such that  $U \cap Z(g) = Z \cap U$  is non-empty. Then by lemma 12 we have  $dim(U \cap Z) = dim(Z) \leq dim(X) - 2 = dim(U) - 2$ . Then by lemma 11,  $g|_U$  is constant. But U is an open subset in an irreducible variety and therefore dense, so continuity implies g is globally constant.  $\square$ 

## Lecture 6: Function Field, Dominant Maps

**Definition 14.** Let X be an irreducible variety. The function field of X, denoted k(X) is defined as the limit

$$K(X) = \lim_{U \subset X} k[U]$$

taken over all open subsets of X with the obvious restriction morphisms.

If X is irreducible, k(X) is just the fraction field of the integral domain k[U] for any open affine subset  $U \subseteq X$ . A morphism of varieties  $f: X \to Y$  is dominant if the image of f is dense. Suppose  $f: X \to Y$  is dominant and  $\phi$  is a rational function on Y. Then by definition  $\phi$  is an equivalence class  $(U, g \in k[U])$ , where (U,g) and (U',g') are equivalent if they restrict to the same function on an open subset of  $U \cap U'$ . Pick a representative (U,g) for  $\phi$ . Since f(X) is dense,  $f^{-1}(U)$  is non-empty. Hence,  $(f^{-1}(U), f^*g)$  is a rational function on X. It is easy to see that 'equivalent' functions on Y pull back to 'equivalent' functions on X. Thus, we obtain a map of function fields  $f^*: k(Y) \to k(X)$ .

**Definition 15.** For any dominant map of irreducible varieties  $f: X \to Y$  we obtain a field extension  $k(X)/f^*k(Y)$ . The degree of f is the degree of this field extension.

**Lemma 13.** Let X and Y be irreducible varieties with Y normal and  $f: X \to Y$  a finite dominant map. Then for any  $y \in Y$ ,  $\#f^{-1}(y) \leq deg(f)$ .

Proof. Since f is finite (hence affine) we may reduce to the case where X = Spec(A) and Y = Spec(B). Finiteness implies that A is a finitely-generated B-module. Suppose  $\#f^{-1}(y) = m$  and let  $\phi \in A$  be a function taking distinct values on the elements of  $f^{-1}(y)$ . Let  $P \in B[t]$  be the minimal polynomial for  $\phi$ . Then  $deg(P) \leq deg(f)$ . Since Y is normal, B is integrally closed. Hence, the coefficients of P are elements of P and are therefore constant on  $f^{-1}(y)$ . Let  $\tilde{P} \in k[t]$  denote the polynomial obtained from P by replacing the coefficients with their values at p. P has at least p roots and hence p degp degp elements of p which completes the proof.

**Definition 16.** Let X, Y be irreducible varieties, and let  $f: X \to Y$  be a dominant map of degree n. f is unramified over  $y \in Y$  if  $\#f^{-1}(y) = n$ . Otherwise, we say that f is ramified at y or that y is a ramification point of f.

**Proposition 7.** Let  $f: X \to Y$  be a finite dominant map of irreducible varieties and let  $R \subseteq Y$  be the set of ramification points. R is a closed subset of X and if the field extension  $k(X)/f^*k(Y)$  is separable, then  $R \neq X$ .

Proof. Since f is finite (hence affine), we may reduce to the case where X,Y are affine. We will first prove that Y-R is open. Suppose f is unramified over g. Choose g as in the proof of lemma 13. Since g is unramified at g, g has g distinct roots, where g degree g. Write g for the discriminant of g. Degree g implies g unramified at g. But g degree g for g in a neighborhood of g by continuity. Hence, g is open. Suppose g for g is separable. Then g is generated over g for g by a single element g by field theory. Let g denote the minimal polynomial for g. Then g for g in the proof of lemma 13. Since g is unramified at g is generated over g by continuity. Hence, g is open. Suppose g for g is separable. Then g for g is generated over g for g is a single element g for g in the proof of lemma 13. Since g is unramified at g is unramified at g is unramified at g is unramified at g. Thence, g is unramified at g is unramified at g is unramified at g. Thence, g is unramified at g is unramified at g is unramified at g. Thence, g is unramified at g is unramified at g is unramified at g. Thence g is unramified at g is unramified at g is unramified at g is unramified at g. Thence g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g. Thence g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g is unramified at g

We finish the lecture by stating an easy but extremely important general categorical result called Yoneda's Lemma. It says roughly that an object in a category is uniquely determined by a functor it represents. The standard way to apply it in algebraic geometry is as follows. Due to Yoneda's Lemma, to define an algebraic variety X, it suffices to describe the functor represented by X and then check that the functor is representable. This a standard tool used to make sense of the intuitive idea "the variety X parametrizing algebraic (or algebro-geometric) data of a given kind" – such as the Grassmannian variety parametrizing linear subspaces of a given dimension in  $k^n$ . More complicated examples (beyond the scope of 18.725) involve subvarieties in a given variety with fixed numerical invariants etc. In the next lecture we will use Yoneda Lemma to define products of algebraic varieties.

**Lemma 14** (Yoneda). Let C be a category. For every  $x \in C$  define a covariant functor

$$h^x: C \to Set$$
  
 $c \mapsto Hom(x, c)$ 

Then the assignment  $x \mapsto h^x$  defines a functor  $h: C \to Functors(C, Set)$ . h is fully faithful and therefore injective on objects (up to isomorphism).

#### Lecture 7: Product of Varieties, Separateness

Here are some additions to last time. Recall that if  $R(X) \cong R(Y)$ , then there are open subsets  $U \subseteq X$ ,  $V \subseteq Y$  which are isomorphic. To see this, replace X, Y with U, V such that we have morphisms  $f: U \to V$  and  $g: V' \to U$  (where  $V' \subseteq V$ ) which are induced by the isomorphism  $R(X) \cong R(Y)$ . Then  $fg: V' \to V'$  is the identity (induced by  $R(Y) \to R(X) \to R(Y)$  which is the identity). Then  $g: V' \to f^{-1}(V')$ , and set  $U' = f^{-1}(V')$ . Then  $gf: U' \to U'$  is the identity for similar reasons. Hence  $U' \simeq V'$ .

In the proof of a lemma from last time (that the set of unramified points is open), we used that if  $\operatorname{Spec} A \to \operatorname{Spec} (C = B[t]/P) \to \operatorname{Spec} B$  (where everything has dimension n), then  $C \subseteq A$ ; that is,  $C \to A$  is an injection. If not, then the kernel is nontrivial, and consequently  $\operatorname{Spec}(\operatorname{image})$  has dimension less than n, and hence  $\operatorname{dim} \operatorname{Spec} A < n$ .

**Products** Let C be any category and  $X,Y \in \mathrm{Ob}(C)$ . Then  $X \times Y$  is an object  $Z \in \mathrm{Ob}(C)$  together with maps  $\pi_X : Z \to X$ ,  $\pi_Y : Z \to Y$  such that for any other  $T \in \mathrm{Ob}(C)$ , there is an isomorphism  $\mathrm{Hom}(T,Z) \xrightarrow{\sim} \mathrm{Hom}(T,X) \times \mathrm{Hom}(T,Y)$  given by  $f \mapsto (\pi_X \circ f, \pi_Y \circ f)$ . Equivalently,  $X \times Y$  is the object corresponding to the functor  $T \mapsto \mathrm{Hom}(T,X) \times \mathrm{Hom}(T,Y)$ , if it exists. Yoneda's lemma implies that if it exists, then it is unique up to unique isomorphism.

Similarly, the coproduct  $X \coprod Y$  is defined such that  $\operatorname{Hom}(X \coprod Y, T) \xrightarrow{\sim} \operatorname{Hom}(X, T) \times \operatorname{Hom}(Y, T)$ .

**Example 8.** Let C be the category of commutative k-algebras. Then the product is the usual direct product, or direct sum. The coproduct of A, B would be  $A \otimes_k B$ . We have an equivalence of categories

 $\{affine algebraic varieties\} = \{finitely generated commutative nilpotent - free k-algebras\}^{op},$ 

where the op means the opposite category; the objects are the same, but the arrows are reversed. Thus, product of affine algebraic varieties corresponds to the tensor product of their global sections.

Exercise 1. Describe the product and coproduct in the category of not necessarily commutative k-algebras.

**Lemma 15.** If A, B are nilpotent-free k-algebras, so is  $A \otimes_k B$ .

Proof. We check that  $A \otimes_k B$  injects into  $\operatorname{Hom}_{k-\operatorname{alg}}(\operatorname{Spec} A \times \operatorname{Spec} B)$ . For contradiction, take a nonzero element  $\sum a_i \otimes b_i \in A \otimes_k B$  in the kernel. Without loss of generality, the  $a_i$  are linearly independent, as well as the  $b_i$ . Find  $x \in \operatorname{Spec} A$  such that for some  $i, a_i(x) \neq 0$ . Restricting to  $\{x\} \times \operatorname{Spec} B$ , we get a contradiction to linear independence of the  $b_i$ . Therefore, we can identify  $A \otimes_k B$  with a subspace of  $\operatorname{Hom}_{k-\operatorname{alg}}(\operatorname{Spec} A \times \operatorname{Spec} B)$ , which clearly contains no nilpotents.

Therefore,  $\operatorname{Spec} A \otimes_k B$  makes sense, and  $\operatorname{Hom}(X,\operatorname{Spec} A \otimes_k B) = \operatorname{Hom}(A \otimes_k B, k[X]) \simeq \operatorname{Hom}(A, k[X]) \times \operatorname{Hom}(B, k[X]) = \operatorname{Hom}(X,\operatorname{Spec} A) \times \operatorname{Hom}(X,\operatorname{Spec} B)$  implies that  $\operatorname{Spec} A \times \operatorname{Spec} B = \operatorname{Spec} A \otimes_k B$ .

Remark 10. Caution: The topology on the product of spaces with functions is **not** the product topology.

Suppose X, Y are algebraic varieties, or spaces with functions. We define a basis of open sets on  $X \times Y$  to be those subsets of the form  $U \subseteq V_1 \times V_2$ , where  $V_1 \subseteq X$ ,  $V_2 \subseteq Y$  are open and U is the complement to zeroes $(f = \sum f_i g_i)$  where  $f_i$  are regular on  $V_1$ ,  $g_i$  are regular on  $V_2$ . Another construction can be given as follows: suppose that X and Y can be written as  $X = \cup U_i$ ,  $Y = \cup V_j$  for  $U_i = \operatorname{Spec} A_i$  and  $V_j = \operatorname{Spec} B_j$ . Then  $X \times Y$  will be  $\cup \operatorname{Spec}(A_i \otimes B_j)$ , glued properly.

**Theorem 7.1.**  $\dim(X \times Y) = \dim(X) + \dim(Y)$ 

*Proof.* The computation is local, so assume X, Y are affine of dimension n, m respectively. Then there are finite onto maps  $X \to \mathbb{A}^n$ ,  $Y \to \mathbb{A}^m$ , so their product is a finite onto map  $X \times Y \to \mathbb{A}^{n+m}$ , which implies that  $X \times Y$  is of dimension n + m.

**Lemma 16.** Suppose that for  $i \in \{1, 2\}$ ,  $X_i$  is a closed subvariety of  $Y_i$ . Then  $X_1 \times X_2$  is a closed subvariety of  $Y_1 \times Y_2$ .

*Proof.* Work locally to reduce to the case when  $Y_1, Y_2$  are affine. The corresponding algebraic statement to check is that the tensor product of two surjective maps is still surjective; this is true.

**Proposition 8.** The product of projective varieties is projective.

Proof. By the previous lemma, it suffices to check that  $\mathbb{P}^n \times \mathbb{P}^m$  is projective. To do so, use the Segre embedding into  $\mathbb{P}^{nm+n+m}$ . Geometrically, the Segre embedding takes  $(x,y) \in \mathbb{P}^n \times \mathbb{P}^m$ , considers the duals of x,y given by lines  $L_x \subseteq k^{n+1} = V$ ,  $L_y \subseteq k^{m+1} = W$ , takes the line  $L_x \otimes L_y \subseteq V \times W = k^{(n+1)(m+1)}$ , and identifies that with its dual, which is a point in  $\mathbb{P}^{nm+n+m}$ . More concretely, it takes  $((x_0 : \cdots : x_n), (y_0 : \cdots : y_m)) \mapsto (\cdots : x_i y_j : \cdots)$ . If the coordinate are given by  $z_{ij}$  such that the  $x_i y_j$  belongs to the  $z_{ij}$  coordinate, then the image of the Segre embedding is cut out by  $z_{ij} z_{kl} - z_{kj} z_{il}$ .

#### Separatedness

**Example 9.** Here is a non-quasiprojective variety: the line with a double point. It is given by  $\mathbb{A}^1 \times \{0,1\}/((x,0) \sim (x,1) \text{ unless} x = 0)$ .

**Definition 17.** An algebraic variety is separated if its diagonal  $\Delta_X$  is a closed subvariety in  $X \times X$ .

In general, the diagonal is always a locally closed subvariety. Furthermore, affine varieties are separated because if  $X = \operatorname{Spec} A$ , then the multiplication map  $A \otimes A \twoheadrightarrow A$  is surjective. Therefore, if X is an algebraic variety such that  $X = \cup U_i$  where the  $U_i$  are affine, then  $\Delta_X \cap (U_i \times U_i)$  is closed in  $U_i$ .

**Lemma 17.** A locally closed subvariety in a separated variety is separated.

*Proof.* Suppose X is separated and  $Z \subseteq X$  is a subvariety. Then  $Z \times Z \subseteq X \times X$  is a subvariety, and  $\Delta_Z = \Delta_X \times (Z \times Z)$ .

**Lemma 18.**  $\mathbb{P}^n$  is separated.

*Proof.* Write  $\mathbb{P}^n = \bigcup \mathbb{A}_i^n$ . Then  $\mathbb{A}_i^n \times \mathbb{A}_j^n \supseteq \Delta \cap (\mathbb{A}_i^n \times \mathbb{A}_j^n)$ . When i = j, we are reduced to the affine case. When  $i \neq j$ , say i = 0 and j = 1, we take coordinates  $x_1, \dots, x_n$  and  $y_0, y_2, \dots, y_n$  and see that being on the diagonal is the closed condition  $x_a y_b = x_b y_a$ .

Corollary 12. A quasiprojective variety is separated.

The line with a doubled origin is not separated. To see this, denote this algebraic variety by X, and note that we have a natural map  $X \to \mathbb{A}^1$ . Then  $X^2 \to \mathbb{A}^2$ , and over 0 we have  $\{0_{ij}\}_{i,j\in\{1,2\}}$ . The closure of diagonal contains all four points, while only two points  $0_{11}$  and  $0_{22}$  belong to the diagonal. In particular, X cannot be quasiprojective as it is not separated.

Remark 11. Often (including Hartshorne), an "abstract variety" is taken to be separated and irreducible.

**Definition 18.** Let  $f: X \to Y$  be a morphism. Then  $\Gamma_f$ , called the graph of f, is the image of  $id \times f$  in  $X \times Y$ .

Note that  $\Gamma_f$  is a subvariety isomorphic to X, and  $\Gamma_{\rm id}$  is the diagonal. Furthermore,  $\Gamma_f$  is always locally closed. If Y is separated, then  $\Gamma$  is a closed subvariety.

**Corollary 13.** If X is irreducible and Y is separated and  $f, g: X \to Y$  agree on a nonempty open set, then f = g.

*Proof.* Suppose f, g agree on a nonempty open set  $U \subseteq X$ . Then  $\Gamma_f|_U = \Gamma_g|_U$ , and taking closures gives that  $\Gamma_f = \overline{\Gamma_f|_U} = \overline{\Gamma_g|_U} = \Gamma_g$ . Therefore, f = g.

**Corollary 14.** Suppose X is irreducible, Y is separated, U is a nonempty open subset of X, and  $f:U\to Y$  is a morphism. Then there is a maximal open subset V of X to which f extends.

## Lecture 8: Product Topology, Complete Varieties

To check that  $\mathbb{P}^n$  is separated, we used an affine covering of  $\mathbb{P}^n$  as  $\cup \mathbb{A}_i^n$ . Instead, we could have checked that the preimage of  $\Delta \subseteq \mathbb{P}^n \times \mathbb{P}^n$  in  $(\mathbb{A}^{n+1} \setminus 0)^2$  is closed; this is given by the equation  $X \wedge Y = 0$  (recall that  $\mathbb{P}^n = (\mathbb{A}^{n+1} \setminus 0)/k^{\times}$ .

**Remark 12.** We have that X is Hausdorff if and only if the diagonal in  $X^2$  is closed with respect to the **product topology**, and **not** the Zariski topology.

**Corollary 15.** If  $k = \mathbb{C}$ , then X is separated iff and only if  $X_{cl}$  (which is X with the classical topology coming from  $\mathbb{C}$ ) is Hausdorff.

*Proof.* Let X be a variety over k, and  $Z \subseteq X$  be a Zariski locally closed subset. We claim that Z is Zariski closed if and only if it is classically closed. To see this, it suffices to check that if Z is Zariski locally closed and classically closed, then it is Zariski closed. Note that Z is Zariski open in  $\overline{Z}_{Zar}$ , and so it is open dense in  $\overline{Z}_{cl}$ , so  $\overline{Z}_{Zar} = \overline{Z}_{cl}$ . Since the diagonal  $\Delta$  is Zariski locally closed, we are done.

**Remark 13.** The image of a morphism may not be a subvariety. For example, take the map from  $\mathbb{A}^2$  to itself induced by the polynomial mapping  $k[a,b] \to k[x,y]$ ,  $a \mapsto x, b \mapsto xy$ . The image is  $\{a \neq 0\} \cup \{(0,0)\}$ . It is not a subvariety, but it will be a constructible subset (this is Chevalley's Theorem, which will be proven later). Suppose X, Y are irreducible and  $f: X \to Y$  is a morphism. Then either f(X) is contained in a closed subset  $Z \supseteq Y$ , or f(X) contains an open dense subset U.

**Proposition 9.** X is separated if and only if for any affine open  $U, V \subseteq X$ ,  $U \cap V$  is affine and  $k[U \cap V]$  is generated by k[U] and k[V].

*Proof.* Consider an open  $U \times V \subseteq X \times X$  where U, V are open subsets in X. Since X is separated, the intersection of diagonal with  $U \times V$  is closed in  $U \times V$ ; furthermore, this intersection equals  $U \cap V$ . As  $U \times V$  is affine and  $U \cap V$  is closed, we see that  $U \cap V$  is affine. We also have  $k[U] \otimes k[V] = k[U \times V] \twoheadrightarrow k[U \cap V]$ . For the converse, the second condition implies that  $(U \times V) \cap \Delta$  is closed in  $U \times V$ , so  $\Delta$  is closed.  $\square$ 

**Example 10.** Let X be the affine line with a doubled origin, with the usual affine open covering  $U \cup V$  where  $U = \mathbb{A}^1_1$ ,  $V = \mathbb{A}^1_2$ . Then this covering corresponds to  $k[t_1, t_2] \mapsto k[t, t^{-1}]$  where  $t_1, t_2 \mapsto t$ . This is not surjective.

Consider X to now be the affine plane with a doubled origin, with affine open covering  $U \cup V$  where  $U = \mathbb{A}_1^2$ ,  $V = \mathbb{A}_2^2$ . In this case,  $U \cap V = \mathbb{A}^2 \setminus \{0\}$  is not affine.

Also, we checked last time that for Y separated,  $f: X \to Y$  is determined by  $f|_U$  where U is a dense open subset of X.

**Proposition 10.** (Caternary property). Let X be an algebraic variety, with  $X = Z_n \supsetneq Z_{n-1} \supsetneq \cdots \supsetneq Z_0$  where each  $Z_i$  is closed irreducible. If this chain cannot be refined, then dim  $Z_i = i$ .

*Proof.* Theorem 2.6.7 of [K].

Now we consider "dimension and rate of growth." Let A be a finitely generated k-algebra. Let V be the space of generators. Set  $V_n = \operatorname{span}\{x_1 \cdots x_k : x_i \in V, k \leq n\}$  and  $D_V(n) = \dim V_n$ . The asymptotic behavior of  $D_V(n)$  actually does not depend on V. For if  $V' \subseteq V_d$ , then  $D_{V'}(n) \leq D_V(nd)$ .

**Proposition 11.** If A = k[X] where X is affine of dimension d, then  $D_V(n) = \Theta(n^d)$ ; that is, there exist constants c', c such that for all n,

$$c'n^d \le D_V(n) \le cn^d \tag{*}$$

Proof. Suppose  $B \subseteq A$  and A is finite over B. If (\*) holds for B, then it holds for A. Given  $V_B$  to be generators for B,  $V_A = V_B \cup W$  where W are generators for A as a B-module, note each  $x \in W$  satisfies an equation of the form  $x^r = b_{r-1}x^{r-1} + \cdots + b_0$  for  $b_i \in B$ . We can assume without loss of generality that  $b_i \in V_B$ . Then  $D_{V_B}(n) \leq D_{V_A}(n) \leq D_{V_B}(n) \cdot c$  where  $c = r^{\dim W}$ . Setting  $B = k[x_1, \cdots, x_d]$ , an explicit computation gives a polynomial in n of degree d.

#### Remark 14.

- (1) The order of growth function has been used to generalized the concept of dimension to noncommutative algebras, groups etc. in the works of Artin, Gromov and others.
- (2) In our commutative setting the function  $D_V(n)$  can in fact be analyzed much more precisely. It turns out that for large n we have  $D_V(n) = P(n)$  for a certain polynomial P. It is closely related to the so called Hilbert polynomial, to be described in 18.726.

**Theorem 8.1.** Suppose X, Y are irreducible subvarieties in  $\mathbb{A}^n$ . Then each component of  $X \cap Y$  has codimension at most  $\operatorname{codim} X + \operatorname{codim} Y$ .

Proof. Rewrite  $X \cap Y = (X \times Y) \cap \Delta_{\mathbb{A}^n} \subseteq \mathbb{A}^n \times \mathbb{A}^n$ . From last time,  $\dim(X \times Y) = \dim X + \dim Y$ . The diagonal in affine space is cut out by the n linear equations  $x_i = y_i$ . By a theorem of last time we know that each component of  $Z_f \subseteq X$  has dimension equal to  $\dim X - 1$ , so  $\dim(X \cap Y) \ge \dim(X \times Y) - n = \dim X + \dim Y - n$ .

**Remark 15.** This theorem doesn't exclude empty intersections. The obvious example is the intersection of subvarieties  $x_1 = 0$  and  $x_1 = 1$ .

**Theorem 8.2.** The previous theorem holds for  $X, Y \subseteq \mathbb{P}^n$ ; moreover, the intesection  $X \cap Y$  is nonempty if  $\dim X + \dim Y > n$ .

*Proof.* Here is a lemma: the dimension of  $C_X$  (the cone over X) equals dim X+1. To see this, note that  $C_X \cap \{x_i = 1\}$  is isomorphic to  $U_i = X \cap \mathbb{A}_i^n \subseteq X$ , and from this it is a straightforward exercise to complete the proof of this lemma.

Using this, the proof of the theorem goes as follows:  $\dim(X \cap Y) = \dim C_{X \cap Y} - 1 = \dim(C_X \cap C_Y) - 1 \ge \dim C_X + \dim C_Y - (n+1) - 1 = \dim X + \dim Y - n$ . The intersection of cones is nonempty as it contains 0.

#### Complete varieties

**Definition 19.** A variety X is complete if it is separated and universally closed, which means that for all Y, the projection map  $Y \times X \to Y$  sends closed sets to closed sets.

We will see that for  $k = \mathbb{C}$ , X is complete if and only if  $X_{cl}$  is compact. Also, if X is quasiprojective, we will see that complete is equivalent to projective. For the forward direction, suppose  $\iota : X \hookrightarrow \mathbb{P}^n$  is locally closed. Then X is in the image of the closed embedding  $\Gamma_{\iota} \hookrightarrow X \times \mathbb{P}^n$ , so  $X \subseteq \mathbb{P}^n$  is closed.

#### Lemma 19.

- (i) Suppose Z is closed in X. Then X is complete implies Z is complete.
- (ii) If  $f: X \to Z$  is a morphism with Z separated and X complete, then  $f(X) \subseteq Z$  is a closed complete subvariety.
- (iii) If X, Y are complete, then so is  $X \times Y$ .
- *Proof.* (i) We see that  $Y \times Z$  is closed in  $Y \times X$ , so by considering the projection to Y, this is clear.
- (ii) Identify f(X) with  $\Gamma_f$  in  $X \times Z$ . As X, Z are separated, so is  $X \times Z$ . As  $\Gamma_f$  is a closed subvariety of  $X \times Z$ , it is also separated (for these facts, see Lemma 3.3.2 of [K]). Hence f(x) is separated. To check that f(X) is universally closed, take a variety Y and closed subset  $T \subseteq f(X) \times Y$ . It suffices to check that the image of T in Y is closed. Consider the map  $f \times \operatorname{id} : X \times Y \to f(X) \times Y$ , and let  $\widetilde{T} = (f \times \operatorname{id})^{-1}(T) \subseteq X \times Y$ . Then it suffices to check that the image of  $\widetilde{T}$  under the projection  $X \times Y \to Y$  is closed, which follows from X being complete.

(iii) As X, Y are both separated, so is  $X \times Y$  (Lemma 3.3.2 of [K]).

Let Z be any variety and  $T \subseteq X \times Y \times Z$  closed. As X is universally closed, the image of T in  $Y \times Z$  is closed. As Y is universally closed, the image of T in Z is closed. Hence,  $X \times Y$  is universally closed.

#### **Proposition 12.** $\mathbb{P}^n$ is complete.

Proof. We know  $\mathbb{P}^n$  is separated (Lemma 3.3.2 of [K]), so it suffices to check that it is universally closed. We use an "elimination theory" argument. Let Y be any variety and  $Z \subseteq \mathbb{P}^n \times Y$  be a closed subset. Then Z comes from a closed subset  $\widetilde{Z} \subseteq \mathbb{A}^{n+1} \times Y$ . Suppose  $I_{\widetilde{Z}}$ , the ideal of functions vanishing on  $\widetilde{Z}$ , is generated by some homogeneous polynomials  $P_i \in k[Y][x_0, \cdots, x_n]$ . For  $y \in Y$ , let  $P_{i,y} = P_i(y, -) \in k[x_0, \cdots, x_n]_d$  for some d (this is the degree d homogeneous polynomials). Then  $(P_{i,y})$  is an ideal of  $k[x_0, \cdots, x_n]$ , so we let  $U_d = \{y \in Y : (P_{i,y}) \supseteq k[x_0, \cdots, x_n]_d\}$ . Letting  $\operatorname{pr}(Z)$  be the image of Z in  $\mathbb{P}^n \times Y \to Y$ , we see that  $y \notin \operatorname{pr}(Z)$  iff there is no point  $(x_0, \cdots, x_n)$  which makes all of the  $P_{i,y}$  vanish, iff it lies in some  $U_d$ . Therefore,  $Y \setminus \operatorname{pr}(Z) = \bigcup_d U_d$ . It is enough to check that each  $U_d$  is open, which is equivalent to checking that the natural map  $\bigoplus_i k[x_0, \cdots, x_n]_{d-d_i} \to k[x_0, \cdots, x_n]_d$  (where  $d_i$  is the degree of  $P_i$ ) defined by sending  $(g_i) \mapsto \sum_i g_i P_{i,y}$  is surjective. This is equivalent to requiring that some matrix with k[Y]-entries, when evaluated at y, has maximal rank, which is some condition of non-vanishing of minors. So it is an open condition.

So projective varieties are complete, and a quasiprojective variety is complete if and only if it is projective.

## Lecture 9: Chow's Lemma, Blowups

Last time we showed that projective varieties are complete. The following result from Wei-Liang Chow gives a partial converse. Recall that a birational morphism between two varieties is an isomorphism on some pair of open subsets.

**Lemma 20** (Chow's Lemma). If X is a complete, irreducible variety, then there exists a projective variety  $\tilde{X}$  that is birational to X.

*Proof.* This proof is a standard one. Here we follow the proof presented by [SH77]. Choose an affine covering  $X = U_1 \cup \ldots \cup U_n$ , and let  $Y_i \supseteq U_i$  be projective varieties containing  $U_i$  as open subsets. Now consider  $\Delta: U \to U^n \to \prod_i U_i \to Y$  where  $U = \bigcap_i U_i, Y = \prod_i Y_i$ , and  $\phi: U \to X \times Y$  be induced by the standard

inclusion  $U \to X$  and  $\Delta$ . Let  $\tilde{X}$  be the closure of  $\phi(U)$ , and  $\pi_1$  gives a map  $f: \tilde{X} \to X$ . This map is birational because  $f^{-1}(U) = \phi(U)$ , and on U the map  $\pi_1 \circ \phi$  is just identity. (To see the first claim, note that it means  $(U \times Y) \cap \tilde{X} = \phi(U)$ , i.e.  $\phi(U)$  is closed in  $U \times Y$ , which is true because  $\phi(U)$  in  $U \times Y$  is just the graph of  $\Delta$ , which is closed as Y is separated.)

So it remains to check that  $\tilde{X}$  is projective. We show this by showing that the restriction of  $\pi_2: X \times Y \to Y$  to  $\tilde{X}$ , which we write as  $g: \tilde{X} \to Y$ , is a closed embedding. Let  $V_i = p_i^{-1}(U_i)$ , where  $p_i$  is the projection map from Y to  $Y_i$ . First we claim that  $\pi_2^{-1}(V_i)$  cover  $\tilde{X}$ , which easily follow from the statement that  $\pi_2^{-1}(V_i) = f^{-1}(U_i)$ , since  $U_i$  cover X. Consider  $W = f^{-1}(U) = \phi(U)$  as an open subset in  $f^{-1}(U_i)$ : on W we have  $f = p_i g$ , so the same holds on  $f^{-1}(U_i)$  and the covering property follows.

It remains to show that  $\tilde{X} \cap V_i \to U_i$  are closed embeddings. Noting that  $V_i = Y_1 \times \ldots \times Y_{i-1} \times U_i \times Y_{i+1} \times \ldots \times Y_n$ , we write  $Z_i$  to denote the graph of  $V_i \xrightarrow{p_i} U_i \hookrightarrow X$ , and note that it is closed and isomorphic to  $V_i$  via projection. Noting that  $\phi(U) \subseteq Z_i$  and that  $Z_i$  is closed, taking closure we see that  $\tilde{X} \cap V_i \to U_i$  is closed in  $Z_i$ .

Blowing up of a point in  $\mathbb{A}^n$  The blow-up of the affine n-space at the origin is defined as  $\widehat{\mathbb{A}^n} = Bl_0(\mathbb{A}^n) \subseteq \mathbb{A}^n \times \mathbb{P}^{n-1} = \{(x,L) : x \in \mathbb{A}^n, L \in \mathbb{P}^{n-1}, x \in L\}$ . It is a variety defined by equations  $x_it_j = x_jt_i$ . We have a projection  $\pi : \widehat{\mathbb{A}^n} \to \mathbb{A}^n$ . Atop 0 there is an entire  $\mathbb{P}^{n-1}$ , and on the remaining open set the projection is an isomorphism.

Now consider X an closed subset of  $\mathbb{A}^n$ , such that  $\{0\}$  is not a component. The **proper transform** of X (a.k.a. the **blowup** of X at 0), denoted  $\tilde{X}$ , is the closure of the preimage of  $X \setminus 0$  under  $\pi$ . Suppose X contains 0, then  $\pi^{-1}(X) = \tilde{X} \cup \mathbb{P}^{n-1}$ . If  $X \subseteq \mathbb{A}^n$ , then  $\mathbb{P}^{n-1} \not\subseteq \tilde{X}$  because  $\dim(\mathbb{P}^{n-1}) \ge \dim(\tilde{X})$ . If X is irreducible, then  $\tilde{X}$  is the irreducible component of  $\pi^{-1}(X)$  other than  $\mathbb{P}^{n-1}$ . The preimage of 0 within  $\tilde{X}$  is called the **exceptional locus**.

Next, observe that  $\widehat{\mathbb{A}}^n$  is covered by n affine charts. More explicitly,  $\widehat{\mathbb{A}}^n{}_i \subseteq \mathbb{A}^{n-1}_i \times \mathbb{A}^n$  has coordinates  $(t^i_1, \ldots, t^i_{i-1}, t^i_{i+1}, \ldots, t^i_n)$ . On there, the defining equation becomes  $x_j = t^i_j x_i$  for  $j \neq i$ , so  $\widehat{\mathbb{A}}^n{}_i \cong \mathbb{A}^n$  with coordinates  $(t^i_1, \ldots, t^i_{i-1}, x_i, t^i_{i+1}, \ldots, t^i_n)$ . In other words, if  $P(x_1, \ldots, x_n) \subseteq I_X$ , then  $P(t^i_1 x_i, \ldots, t^i_{i-1} x_i, x_i, \ldots) \subseteq I_{\tilde{X} \cap \widehat{\mathbb{A}}^n{}_i}$ .

**Example 11.** Let  $X = (y^2 = x^3 + x^2) \subseteq \mathbb{A}^n$ . Suppose y = tx, then  $t^2x^2 = x^3 + x^2 \implies t^2 = x + 1$ , so the preimage of (0,0) is  $\{(t = \pm 1, x = 0)\}$ . Thus X is not normal because the map  $\tilde{X} \to X$  is not 1-to-1, though  $\deg(\tilde{X} \to X) = 1$  (recall that a finite birational morphism to a normal variety is isomorphism).

**Definition 20.** Let X an affine variety,  $x \in X$ , we write  $Bl_x(X) = \tilde{X}_x$  to denote  $\tilde{X}$  for an embedding  $X \subseteq \mathbb{A}^n$  where  $x \mapsto 0$ .

**Remark 16.**  $Bl_x(X)$  contains  $X \setminus x$  as an open set, so this generalizes to any variety X.

**Proposition 13.** Suppose X embeds via two embeddings  $i_1, i_2$  to  $\mathbb{A}^n$  and  $\mathbb{A}^m$  respectively, such that there exists some x such that  $i_1(x) = i_2(x) = 0$ , then  $\tilde{X}_1 = \tilde{X}_2$  for two blowups at x.

In particular, this tells us that blowup is an intrinsic operation that does not depend on the embedding.

Proof. First consider the special case  $X = \mathbb{A}^n$ ,  $i_1 = id$ , and  $i_2$  given by  $(x_1, \dots, x_n) \mapsto (x_1, \dots, x_n, f)$  for some polynomial f. Write  $\widehat{\mathbb{A}^{n+1}} = \bigcup_{i=1}^{n+1} \mathbb{A}_i^{n+1}$ , and observe that  $\bigcup_{i=1}^n \mathbb{A}_i^{n+1} = \widehat{\mathbb{A}^{n+1}} \setminus \{(0:0:\dots:0:1) \in \mathbb{P}^n\}$ .

Call that point  $\infty$ , then one can check that  $\infty \notin \tilde{\mathbb{A}}^n$ . Now note that  $\tilde{\mathbb{A}}^n \cap \mathbb{A}_i^{n+1} \cong \mathbb{A}_i^n \subseteq \widehat{\mathbb{A}}^n$  (Locally write it as  $t_{n+1}x_i = f(t_1x_i, \dots, x_i, \dots, t_nx_i)$ , and observe we have a  $x_i$  on both sides so the closure would be of shape  $t_{n+1} = f'(t_1, \dots, x_i, \dots, t_n)$ , which gives an entire  $\mathbb{A}^n$ ), so together we see that the blowup is nothing but  $\widehat{\mathbb{A}}^n$ . Second, consider  $X = \mathbb{A}^n$ ,  $i_1 = id$ ,  $i_2 : \mathbb{A}^n \hookrightarrow \mathbb{A}^{n+m}$  being a graph of a morphism  $\mathbb{A}^n \to \mathbb{A}^m$ . This can be reduced to the first case by induction on m (or really, just the exactly same argument applied several times). Now consider the general case of arbitrary  $i_1, i_2$ . First extend the embedding  $i_2 : X \to \mathbb{A}^m$  to a map  $\mathbb{A}^n \to \mathbb{A}^m$  by lifting each generator (one can switch to the algebraic side, suppose  $X = \operatorname{Spec} A$ , then we get two surjective maps  $\psi_1 : k[x_1, \dots, x_m] \to A$  and  $\psi_2 : k[y_2, \dots, y_n] \to A$ , lift  $\psi_1$  to  $\psi_2 \circ \phi$  for  $\phi : k[x_1, \dots, x_m] \to k[y_1, \dots, y_n]$  where we map each  $x_i$  into A then lift), then one can use part 2.  $(x \mapsto i_1(x) \mapsto i_1(x)$  has the same blowup as  $x \mapsto i_1(x) \mapsto i_2(x)$  by the same argument applied on the other direction.)

As an application, consider an example of a complete non-projective surface: start with  $\mathbb{P}^1 \times \mathbb{P}^1$ , blow it up at (0,0), consider the projection to the second factor. For any  $x \neq 0$ , the preimage of x is a projective line; for x = 0, the preimage is the union of two projective lines (one can see this by passing to affine chart then consider closure). Consider two copies of this blow up, call them X, Y, and call the two exceptional lines  $L_1, L_2$  for both of them, Now consider the disjoint union of X and Y where we identify  $L_1$  of X with the fiber of  $\infty$  of Y, and vise versa.

## Lecture 10: Sheaves, Invertible Sheaves on $\mathbb{P}^1$

In this lecture, definition of sheaves will be given. In particular, we will talk about invertible sheaves on  $\mathbb{P}^1$ .

Presheaves and Sheaves on Topological Spaces Let X be a topological space.

**Definition 21.** A presheaf of sets  $\mathcal{F}$  on the topological space X is an assignment for an open subset  $U \subset X$  of a set  $\mathcal{F}(U)$  and for a pair of open subsets  $V \subset U \subset X$  of a so called restriction map  $\phi_V^U : \mathcal{F}(U) \to \mathcal{F}(V)$  such that the following axioms hold:

- 1. for each triple of open subsets  $W \subset V \subset U \subset X$  the composition of the restriction maps  $\phi_W^V \circ \phi_V^U$  is equal to the restriction  $\phi_W^U$ ;
- 2. for each open subset  $U \subset X$ , the restriction  $\phi_U^U$  is equal to the identity map.

Elements of the sets  $\mathcal{F}(U)$  are called sections of the presheaf  $\mathcal{F}$  over the open subset U.

**Example 12.** Let X be a topological space. Then the assignment for an open subset U of the set of all functions on U defines a presheaf. The same for all continuous functions.

**Example 13.** Let X be a manifold. Then the assignment for an open subset U of the set of all smooth functions defines a presheaf. Analogously, one can define the presheaf of all holomorphic functions on a complex manifold.

**Definition 22.** A presheaf  $\mathcal{F}$  on the topological space X is called a sheaf if the following is true for any (possibly infinite) open covering of an open subset  $U = \bigcup U_{\alpha}$ :

- 1. for a collection of sections  $(s_{\alpha}) \in \prod_{\alpha} \mathcal{F}(U_{\alpha})$ , if they coincide on intersections, that is  $s_{\alpha}|_{\beta} = s_{\beta}|_{\alpha}$ , then there exists a section s on U such that  $s|_{\alpha} = s_{\alpha}$ ;
- 2. the map  $\prod_{\alpha} \phi_{U_{\alpha}}^{U}$  is injective.

**Remark 17.** Note that the second property of the sheaf means that the section s from the first property is unique.

Now we will introduce two essential constructions regarding presheaves and sheaves. Let X and Y be two topological spaces, and let  $f: X \to Y$  be a continuous map.

**Definition 23.** Let  $\mathcal{F}$  be a presheaf on X. Then its pushforward along f is a presheaf  $f_*\mathcal{F}$  on Y, and is defined on an open subset  $V \subset Y$  as  $f_*\mathcal{F}(V) \stackrel{def}{=} \mathcal{F}(f^{-1}V)$ .

**Exercise 2.** Check that  $f_*\mathcal{F}$  is indeed a preasheaf. Check that if  $\mathcal{F}$  is a sheaf, then the pushforward  $f_*\mathcal{F}$  is also a sheaf.

**Definition 24.** Let  $\mathcal{G}$  be a presheaf on Y. Then its pullback along f is a presheaf  $f^*\mathcal{G}$  on X, and is defined on an open subset  $U \subset X$  as  $f^*\mathcal{G}(U) \stackrel{def}{=} \lim_{V \supset f(U)} \mathcal{G}(V)$ .

**Exercise 3.** Check that  $f^*\mathcal{G}$  is a preasheaf.

Note that the pullback of a sheaf is not generally a sheaf. However, the notion of the pullback of a sheaf does exist, and it is introduced using the so called sheafification, which will be discussed in the next lecture.

**Remark 18.** Both pushforward and pullback constructions are functorial, that is if we also have a continuous map  $g: Y \to Z$ , then  $g_* \circ f_* = (g \circ f)_*$  and  $f^* \circ g^* = (g \circ f)^*$ .

Sheaves in Algebraic Geometry The situation with sheaves in algebraic geometry differs from the general case, because we want to endow our sets of sections with the structure of modules over regular functions. To make these words more rigorous, we first introduce the *structure sheaf*  $\mathcal{O}_X$  of an algebraic variety X over  $\mathbb{K}$ . Recall that we have defined an algebraic variety as a certain space with functions, so secretly we have already introduced the structure sheaf in the very beginning of the course. Now we will just denote rings of regular functions over an open subset  $U \subset X$  by  $\mathcal{O}_X(U)$ .

**Exercise 4.** Check that  $\mathcal{O}_X$  is a sheaf. Check that all restriction maps are ring homomorphisms. The latter means that  $\mathcal{O}_X$  is a sheaf of rings.

**Definition 25.** Let  $\mathcal{M}$  be a sheaf on X. We say that  $\mathcal{M}$  is a sheaf of  $\mathcal{O}_X$ -modules if for any open subset  $U \subset X$  the set  $\mathcal{M}(U)$  is an  $\mathcal{O}_X(U)$ -module, and all restriction maps commute with the ring action.

**Example 14.** The sheaf  $\mathcal{O}_X$  considered as a module over itself is an example of a sheaf of  $\mathcal{O}_X$ -modules. We can define the direct sum  $\mathcal{M} \oplus \mathcal{N}$  of two sheaves of modules as  $(\mathcal{M} \oplus \mathcal{N})(U) \stackrel{\text{def}}{=} \mathcal{M}(U) \oplus \mathcal{N}(U)$  with the obvious ring action. So we can also introduce the sheaves of modules  $\mathcal{O}_X \oplus \cdots \oplus \mathcal{O}_X$ . They are called free sheaves.

**Definition 26.** A locally free sheaf  $\mathcal{M}$  of rank n on an algebraic variety X is a sheaf of  $\mathcal{O}_X$ -modules such that for some open cover of the variety  $X = \bigcup U_i$ , the restrictions  $\mathcal{M}|_{U_i}$  are free sheaves on  $U_i$  of rank n, that is  $\mathcal{M}|_{U_i} \cong (\mathcal{O}_X|_{U_i})^n$ .

**Example 15.** Let p be a point in  $\mathbb{P}^1$ , then we can define the ideal sheaf  $\mathcal{O}(-p)$  of this point as a certain subsheaf of the structure sheaf  $\mathcal{O}$ :

$$\mathcal{O}(-p)(U) = \{ f \in \mathcal{O}(U) \mid f(p) = 0 \}.$$

This sheaf is locally free and of rank one.

More generally, we can define the ideal sheaf of any closed subvariety of an algebraic variety in the same way — as the sheaf whose sections are exactly those sections of the structure sheaf which vanish on the closed subset. Ideal sheaves need not be locally free.

**Exercise 5.** An ideal sheaf is locally free if and only if it is principal.

Operations of taking direct sum and tensor product of the sheaves take locally free sheaves to locally free sheaves.

We will see in the sequel that locally free sheaves of rank one form a group under the operation of tensor product, with identity being the structure sheaf. This group is called *Picard group*.

#### Lecture 11: Sheaf Functors and Quasi-coherent Sheaves

Recall that last time we defined a sheaf and a presheaf on a topological space, respectively denoted as  $\mathbf{Sh}(X) \subseteq \mathbf{PreSh}(X)$ . We'll work with sheaves of abelian groups on k-vector spaces. (Recall that  $\mathcal{F}(X) \in$ **PreSh**(X) if F(U) is a k-vector space, and  $\mathcal{F}(U)$  restricts to  $\mathcal{F}(V)$  if  $V \subseteq U$ .)

**Proposition 14.** Presheaf of abelian groups on k-vector space is an abelian category.

*Proof.* If 
$$\mathcal{F} \xrightarrow{f} G$$
, then  $\ker(f)(U) = \ker(\mathcal{F}(U) \to \mathcal{F}(U))$ , and same for cokernel.

Note that  $\mathbf{Sh}(X)$  is a full abelian subcategory. Now we introduce the sheafification functor: the embedding functor  $Sh \to PreSh$  has a left adjoint, sending a presheaf  $\mathcal{F}$  to its associated sheaf  $\mathcal{F}^{\#}$ . Recall that a presheaf is a sheaf if for all  $U = \bigcup U_{\alpha}$ , we have the exact sequence  $0 \to \mathcal{F}(U) \to \prod_{\alpha} \mathcal{F}(U_{\alpha}) \to \prod_{\alpha,\beta} \mathcal{F}(U_{\alpha} \cap U_{\beta})$ . So we define  $\mathcal{F}^{\#}(U) = \varinjlim_{U = \bigcup_{\alpha} U_{\alpha}} \ker(\prod \mathcal{F}(U_{\alpha}) \to \prod_{\alpha,\beta} \mathcal{F}(U_{\alpha} \cap U_{\beta}))$ . Another description is via stalks: let  $\mathcal{F}$  be a presheaf on X,  $x \in X$ , and define  $\mathcal{F}_{x} = \varinjlim_{x \in U} \mathcal{F}(U)$ . Then  $\mathcal{F}^{\#}(U) = \{\sigma \in \prod_{x \in U} \mathcal{F}_{x} \mid \forall x \in \mathcal{F}_{x} \in \mathcal{F}_{x} \mid \forall x \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F}_{x} \in \mathcal{F$ 

 $U,\exists V\ni x\subseteq U,s\in\mathcal{F}(V), \mathrm{s.t.}\ \{\sigma_y\}_{y\in V} \mathrm{comes\ from\ }s\}.$  This shows in particular colimits exist in  $\mathbf{Sh}(X)$ :  $\operatorname{coker}_{\mathbf{Sh}}(\mathcal{F} \to \mathcal{G}) = \operatorname{coker}_{\mathbf{Presh}}(\mathcal{F} \to \mathcal{G})^{\#}$ . This just follows from general abstract nonsense.

**Example 16.** An example of a cokernel in **Presh** that is not a sheaf: take  $X = S^1$ , let  $\mathcal{F}$  be the continuous function sheaf  $C(X,\mathbb{R})$  (i.e.  $\mathcal{F}(U)$  are the continuous maps  $U \to \mathbb{R}$ ), and  $\mathcal{G}$  be the constant sheaf  $\mathbb{Z}$  (i.e.  $\mathcal{G}(U)$  consists of constant  $\mathbb{Z}$ -valued function on each connected U; more precisely,  $\mathcal{G}(U)$  are continuous maps  $U \to \mathbb{Z}$  where the latter has the discrete topology), then  $(\mathcal{F}/\mathcal{G})_{Sh}(U)$  would be continuous maps  $U \to \mathbb{R}/\mathbb{Z}$ , whereas  $(\mathcal{F}/\mathcal{G})_{Presh}(U)$  would be the continuous maps  $(U,\mathbb{R})$  mod out the constant maps.

#### **Proposition 15.** Some properties:

- 1.  $\mathcal{F} \to \mathcal{F}^{\#}$  is exact; in particular it doesn't change the stalks.
- 2.  $\mathcal{F} \to \mathcal{F}^{\#}$  is left adjoint to the embedding  $\mathbf{Presh} \to \mathbf{Sh}$ , and is an isomorphism if  $\mathcal{F}$  itself is a sheaf. As an example, consider the constant presheaf V given by  $\mathcal{F}(U) = V$  constant. Then  $\mathcal{F}^{\#}$  is a constant sheaf given by  $\mathcal{F}^{\#}(U) = \{\text{locallyconstantmaps } U \to V\}$ . (Why is  $\mathcal{F}$  not a sheaf itself? Answer: it fails the local identity axiom on  $U = \emptyset$ .)
- 3.  $\mathcal{F} \mapsto \mathcal{F}_x$  is an exact functor; in other words, a sequence of sheaves  $0 \to \mathcal{F} \to \mathcal{F}' \to \mathcal{F}'' \to 0$  is exact iff  $0 \to \mathcal{F}_x \to \mathcal{F}_x' \to \mathcal{F}_x'' \to 0$  is exact for all x.

**Pullback and Pushforward** If  $f: X \to Y$  is a continuous map, then we have  $f^*: \mathbf{Sh}(Y) \to \mathbf{Sh}(X)$ , and  $f_*: \mathbf{Sh}(X) \to \mathbf{Sh}(Y)$ . The latter (pushforward) is given by  $f_*\mathcal{F}(U) = \mathcal{F}(f^{-1}(U))$ , and the former (pullback) is given by the sheafification of the presheaf  $\underline{\lim} \mathcal{F}(V)$ . In particular, we have  $\mathcal{F}_x = i_x^*(\mathcal{F})$ ; so  $f(U) \subseteq V$ 

 $f^*(\mathcal{F})_x = \mathcal{F}_{f(x)}$ , and in particular, we see that  $f^*$  is exact. On the other hand,  $f_*$  is only left exact (to see it is not necessarily exact, note that the pushforward to a point is the same as the global section, which is not necessarily exact).

Structure Sheaf Suppose X is a space with functions, then X carries the structure sheaf  $\mathcal{O}_X$ , given by  $\mathcal{O}_X(U) = k[U]$ . Say  $X = \operatorname{Spec}(A)$  is affine, and  $x \in X$ , then  $\mathcal{O}(X)_x$  is the localization of A at the maximal ideal  $\mathfrak{m}_x$ . This makes X a ringed space, i.e. a topological space equipped with a sheaf of rings.

A sheaf of modules over a ringed space (X, A) is a sheaf  $\mathcal{F}$  where  $\mathcal{F}(U)$  is an A(U) module, such that the restriction to subsets respects the module structure. A sheaf of modules  $\mathcal{F}$  on a ringed space (X,A) is quasicoherent, if  $\forall x \exists U \ni x$  such that there exists an exact sequence  $A_U^{\oplus I} \to A_U^{\oplus J} \to \mathcal{F}_U \to 0$ , where the first two are free modules (with possibly infinite dimensions).

**Remark 19.** Caution:  $\bigoplus_{j \in J} A$  is the sum in the category of sheaves, given by  $(\bigoplus_{PreSh} A)^{\#} = \{s \in \prod_{j \in J} A(U) \mid a_j \in A\}$ 

locally  $s \in \bigoplus\}$ , i.e.  $\forall x \in U \exists V \ni x, V \subseteq U$  such that only finitely many components of  $s|_V$  are nonzero. One can check that the section matches with the normal notion of  $\bigoplus_J A(U)$  if U is quasicompact. If X is Noetherian, then any open U is quasicompact, so  $(A^{\oplus J})(U) = A(U)^{\oplus J}$ .

**Lemma 21.** If X is Noetherian, then  $\Gamma(\varinjlim \mathcal{F})(U) = \varinjlim \mathcal{F}(U)$ , where the right side is the filtered direct limit.

In general, if X is a topological space,  $\Gamma$  is the global section functor  $\mathbf{Sh}(X) \to \mathbf{Vect}_k$ , then it has a left adjoint  $L(\Gamma)$  where  $L(\Gamma)(V)$  the locally constant sheaf with values in V.

**Quasicoherent**  $\mathcal{O}$ -modules We denote the category of quasicoherent  $O_X$  modules by  $\mathbf{QCoh}(X)$ , where X is an algebraic variety.

**Theorem 11.1.** If 
$$X = \operatorname{Spec}(A)$$
, then  $\operatorname{\mathbf{QCoh}}(X) \cong \operatorname{\mathbf{Mod}}(A)$ , given by  $\mathcal{F} \to \Gamma(\mathcal{F}) = \mathcal{F}(X)$ .

*Proof.* First construct the adjoint (localization) functor Loc, where we use  $\tilde{M}$  to denote Loc(M). To do so, first construct a presheaf L that sends U to  $k[U] \otimes_A M$ , then sheafify this presheaf. The functor L is left adjoint to the canonical functor  $\mathbf{Mod}(k[U]) \to \mathbf{Mod}(A)$ , then one can deduce that L is left adjoint to  $\Gamma$ , which sends presheaves of  $\mathcal{O}$ -modules to A-modules, from which the theorem follows.

Note that Loc is an exact functor, which follows from the description of the stalks. Note that  $\mathcal{F}^{\#}$  is defined by  $\mathcal{F}(U)$ , where U is an fixed base of topology. In particular, use the base  $\{U_f = X - Z_f\}$  (the Zariski topology), and note that  $k[U_f] = A_{(f)}$ , thus  $k[U_f] \otimes_A M = M_{(f)}$ , and note that  $M \mapsto M_{(f)}$  is exact. Finally,  $\tilde{M}_x = \varinjlim_{f \mid f(x) \neq 0} M_{\mathfrak{m}_x}$  is exact. It's clear that  $\tilde{A} = \mathcal{O}$ . As a corollary,

Corollary 16.  $\tilde{M}$  is a quasicoherent  $O_X$  module.

To see this, choose a presentation, and observe that  $\widetilde{\bigoplus_{i\in I} M_i} = \widetilde{\bigoplus_i} \widetilde{M_i}$ .

## Lecture 12: Quasi-coherent and Coherent Sheaves

We finish the proof of the following statement:

**Theorem 12.1.** Let  $X = \operatorname{Spec}(A)$  be an affine variety. Then there is an equivalence of categories  $f : \operatorname{\mathbf{QCoh}}(X) \cong \operatorname{\mathbf{Mod}}(A)$ .

*Proof.* Last time we defined the left adjoint functor Loc:  $M \to \tilde{M}$ , where the latter is the sheaf assigned to the presheaf  $\mathcal{F}(U) = k[U] \otimes_A M$ . Note that it is an exact functor. We have a natural functor  $\mathbf{Mod}(A) \to \mathbf{Sh}(X) \to \mathbf{QCoh}(X)$ .

**Lemma 22.** Let  $i \in I$  be a directed system indexing sheaves  $\mathcal{F}_i$ . If X is a Noetherian topological space, then  $\varinjlim_{PreSh} \mathcal{F}_i$  is a sheaf. Hence  $\varinjlim_{PreSh} \mathcal{F}_i = \varinjlim_{Sh} \mathcal{F}_i$ . (Note that  $\varinjlim_{PreSh} (\mathcal{F}_i)(U) = \varinjlim_{Sh} \mathcal{F}_i(U)$  whereas  $\varinjlim_{Sh} (\mathcal{F}_i) = \varinjlim_{Sh} (\mathcal{F}_i)^{\#}$ .) This shows that  $\varinjlim_{Sh} \mathcal{F}_i(U) = \varinjlim_{Sh} (\mathcal{F}_i(U))$ .

**Example 17.** Take 
$$X = \mathbb{Z}$$
, then  $\Gamma(\bigoplus k_n)$  (where  $k_n$  is supported at  $n$ ) =  $\prod_n k \supsetneq \bigoplus_n k_n$ .

Back to the proof of the theorem. We need to check that the sheaf condition holds for  $U = \bigcup_{\alpha} U_{\alpha}$ . U can be made quasicompact since we're Noetherian, so enough to consider the case where  $\{U_{\alpha}\}$  is finite. Using induction we can reduce to  $U = U_1 \cup U_2$ . Now observe the following sequence is exact:

$$0 \to \varinjlim \mathcal{F}_i(U) \to \varinjlim F(U_1) \oplus \varinjlim F(U_2) \to \varinjlim F(U_1 \cap U_2)$$

Now suppose X is an algebraic variety.  $U = U_f = X \setminus Z_f$ , and  $\mathcal{F}$  is quasicoherent.

**Proposition 16.**  $j_*j^*\mathcal{F} = \varinjlim(f^{-n}\mathcal{F})$ , where  $j: U \hookrightarrow X$ ,  $j_*\mathcal{F}$  means the sheaf whose section on V is  $\mathcal{F}(U \cap V)$ , and the right side is the formal notation denoting copies of  $\mathcal{F}$ , where  $\{f^{-n}\mathcal{F}, n = 0, 1, \ldots\}$  are combined in a direct system, and we have the mapping

$$\mathcal{F} \xrightarrow{f} f^{-1} \mathcal{F} \xrightarrow{f} f^{-2} \mathcal{F} \xrightarrow{f} \dots$$

Proof. From each  $f^{-n}\mathcal{F}$  there is an obvious map  $f^{-n}\mathcal{F} \to j_*j^*\mathcal{F}$  and thereby there is an induced map  $\varinjlim f^{-n}\mathcal{F} \to j_*j^*\mathcal{F}$ , which we want to show is an isomorphism. Suffices to assume X is affine. Recall that taking direct limit in presheaves and sheaves yield the same result for Noetherian spaces; in other words, for each U we have  $(\varinjlim f^{-n}\mathcal{F})(U) = \varinjlim (f^{-n}\mathcal{F}(U))$ , so it suffices to check that  $\Gamma(X, j_*j^*\mathcal{F}) = \Gamma(X, j^*\mathcal{F}) = \varinjlim (f^{-n}\mathcal{F}(X))$ , which holds because if  $\Gamma(X, \mathcal{F}) = M$ , then  $\Gamma(X, j^*\mathcal{F}) = M_f = \varinjlim f^{-n}M = \varinjlim (f^{-n}\mathcal{F}(X))$ .

We'll write this limit as  $\mathcal{F}_f$ . To finish the proof, let us first check that  $\Gamma: \mathbf{QCoh}(X) \to \mathbf{Mod}(A)$  is exact (Proposition II.5.6 of Hartshorne). Assuming X is separated, this is in fact true if and only if X is affine; this is known as **Serre's criterion**. Let  $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$  and let  $\sigma \in \Gamma(\mathcal{F}'')$ , First, check for any  $x \in X$  there exists  $f \in A$  such that  $f(x) \neq 0$ ,  $f^n \sigma \in \mathrm{Im}(\Gamma(\mathcal{F}))$ . By the exactness of the short exact sequence,  $\exists U = U_f \ni x, \tilde{\sigma} \in \mathcal{F}(U), \tilde{\sigma} \to \sigma|_U$ . Let  $s/f^n = \tilde{\sigma} \in \Gamma(\mathcal{F})_f = \mathcal{F}(U)$ , where  $s \in \Gamma(\mathcal{F})$ , then it goes into  $\Gamma(\mathcal{F}'')_f = \mathcal{F}''(U)$ .  $s \mapsto f^n \sigma$  is the localized map, so  $f^m s \mapsto f^{n+m} \sigma$  under the map  $\Gamma(\mathcal{F}) \to \Gamma(\mathcal{F}'')$ . Now let  $s \in \mathrm{Coker}$ , By what we just said, we can cover X by open sets  $U_f$  such that  $f_i^n s = 0 \in \mathrm{Coker}$ . Thus since  $f_i$  together generate 1, s = 0. So indeed it is onto.

Now we know  $\Gamma(\tilde{A}) = A$ . Loc commute with  $\bigoplus \Gamma(\widetilde{A^{\oplus I}}) = A^{\oplus I}$ . Given  $M \in \mathbf{Mod}(A)$ , take some presentation  $A^{\oplus J} \to A^{\oplus I} \to M \to 0$ , then the canonical map  $\Gamma(\tilde{M}) \to M$  is an isomorphism. Now we need to check that  $\Gamma(\mathcal{F}) \to \mathcal{F}$  is also an isomorphism. (The rest follows [Har77] as the proof in class was not recorded.) Quasicoherence of  $\mathcal{F}$  means that there exists some open covering  $X = \bigcup D(g_i)$  such that  $\mathcal{F}|_{D(g_i)} = \tilde{M}_i$  for some modules  $(M_i)$ . On the other hand, by Lemma 5.3 of [Har77], applied to  $D(g_i)$ , gives that  $\mathcal{F}(D(g_i)) = \Gamma(\mathcal{F})_{g_i}$  (the localized module), so in fact we have  $M_i = \Gamma(\mathcal{F})_{g_i}$  (as one can check on stalks), and thus  $\Gamma(\mathcal{F}) \to \mathcal{F}$  is isomorphism on each  $D(g_i)$ , hence overall an isomorphism.

A sheaf  $\mathcal{F} \in \mathbf{QCoh}(X)$  is coherent if locally we have a s.e.s.  $O_U^{\oplus I} \to O_U^{\oplus J} \to \mathcal{F} \to 0$ , with I, J finite.

**Lemma 23.** If  $X = \operatorname{Spec} A$ , then  $\mathcal{F} = \tilde{M}$  is coherent iff M is finitely generated.

Proof. If M is finitely generated we clearly have a coherent sheaf. On the other hand, Suppose  $\tilde{M}$  is coherent, then take an open cover of X by  $D(f_i)$  such that on each  $D(f_i)$ , the restriction (which we denote by  $\tilde{M}_i$ ) is a finitely-generated  $k[X]_{f_i}$ -module. Now observe that  $\tilde{M}_i = M_{(f_i)}$ , and since there are only finitely many  $f_i$ , after clearing the denominators we can get a finite generating set for M.

Let  $f: X \to Y$  morphism of algebraic varieties. For  $\mathcal{F} \in \mathbf{Sh}_{O-\mathrm{mod}}(X)$ , we can define  $f_*F \in \mathbf{Sh}_{O-\mathrm{mod}}(Y)$  (pushforward or direct image) by  $f_*(F)(U) = F(f^{-1}(U))$ .

**Lemma 24.**  $f_*$  sends QCoh(X) to QCoh(Y). Note that it does not send coherent module to coherent module. e.g.  $f: \mathbb{A}^1 \to *$ .

*Proof.* First consider when X, Y affine. This becomes  $\operatorname{Spec}(A) \to \operatorname{Spec}(B)$ ,  $f_*(\tilde{M}) = \tilde{M_B}$  clear by inspection. Now for general X, Y, we can assume Y affine since the question is local. Let  $X = \bigcup U_i$  and denote  $U_i \cap U_j = \bigcup U_{ij}^k$ , then there is an exact sequence

$$0 \to f_*(\mathcal{F}) \to \bigoplus_i (f|_{U_i})_*(\mathcal{F}|_{U_i}) \to \bigoplus_{i,j,k} (f|_{U_{ij}^k})_*(\mathcal{F}|_{U_{ij}^k})$$

Now apply Proposition II.5.7 of Hartshorne.

Corollary 17.  $f_*$  is exact for a map of affine varieties. It is left exact in general.

We claim tha  $f_*$  has the left adjoint functor  $f^*: \mathbf{QCoh}(Y) \to \mathbf{QCoh}(X)$ . Recall that  $M \mapsto M_B$  has left adjoint  $M \mapsto A \otimes_B M$ . This defines  $f^*$  for a map of affine varieties. In general,  $f^*(F) = [O_X \otimes_{f^*(O_Y)} f^*(F)]^\#$ . General property about pullback: suppose  $X \to Y$ ,  $U = \mathrm{Spec}(A)$  in X and  $V = \mathrm{Spec}(B)$  in Y. Let  $F|_V = \tilde{M}$ , then  $f^*(F)|_U = A \otimes_B M$ . We see that  $f^*U$  is right exact by adjointness (or from the fact that tensor products are right adjoint).

A particular example of this is the pullback to a point. Consider  $i:\{x\}=*\hookrightarrow X$ . Then  $i^*(\mathcal{F})$  is the fiber of  $\mathcal{F}$  at x. If X is just quasicoherent, it may have zero fibers at points. (Consider the example  $X=\mathbb{A}^1$ , and  $j:\mathbb{A}^1-\{0\}$ , and let  $\mathcal{F}=j_*O/\mathcal{O}$ , let  $\tilde{M}=\mathcal{F}$ , where  $M=\frac{k[t,t^{-1}]}{k[t]}=\{a_{-1}t^{-1}+\ldots+a_nt^{-n}\}$ , then the multiplication by t is surjective. What is the fiber of  $\mathcal{F}$  at 0? it is M/tM=0.) Also  $\mathcal{F}|_{\mathbb{A}^1-\{0\}}=0$ , so fiber at  $x\neq 0$  is also 0.

#### **Lemma 25.** If $\mathcal{F}$ is coherent, then:

- 1. Fiber is always finite dimensional:
- 2. Fiber of  $\mathcal{F}$  at x is zero iff  $\exists U \supseteq x, F|_U = 0$ ;
- 3. The function  $d: x \mapsto \dim(\operatorname{fiber}(x))$  is (upper) semicontinuous.
- 4. The function d is locally constant if and only if F is locally free.

Proof. Part 1) is obvious. Now denote the fiber by  $F_x(\mathcal{F})$ . Let  $I_x$  be the stalk, i.e. module over the stalk of O, i.e.  $O_{x,X}$ -local ring of x. The claim is that  $F_x(\mathcal{F}) = F_x/\mathfrak{m}_x I_x = I_x \otimes_{O_{x,X}} k$ . Let  $\overline{m_1}, \ldots, \overline{m_n}$  be a basis in  $F_x(\mathcal{F})$ , use Nakayama to find some  $m_i \in F_{x_i}$  such that  $m_i$  generate  $F_x$ . So  $F_x(\mathcal{F}) = 0 \implies F_x = 0 \implies F|_U = 0$  for some  $U \ni x$ . This finishes part 2). Now,  $\exists U_i$  and action  $s_i \in F(U) \mapsto m_i$ ,  $s_i$  generate F(U) as k(U) module. This is part 3). Part 4) is left as exercise.

#### Lecture 13: Invertible Sheaves

Last time we showed that when  $X = \operatorname{Spec} A$  is an affine scheme, we have the equivalence  $\operatorname{QCoh}(X) \cong \operatorname{\mathbf{Mod}}(A)$  given by the  $\Gamma$  and the Loc functors. In particular, these functors are exact, and we have  $\Gamma(\mathcal{F}) = 0 \Longrightarrow \mathcal{F} = 0$ . This in particular implies that  $\Gamma \circ \operatorname{Loc} = 1$  (We know this holds for A, now check the general case by choosing a presentation.). We need to check the other direction:  $\operatorname{Loc} \circ \Gamma(\mathcal{F}) = \mathcal{F}$ .

**Definition 27.** A functor  $\mathcal{F}: \mathcal{C}_1 \to \mathcal{C}_2$  is called conservative if for every  $g \in \text{Hom}(\mathcal{C}_1)$ ,  $\mathcal{F}(g)$  is an isomorphism implies that g is an isomorphism. Note that this does not say that  $\mathcal{F}(A) \cong \mathcal{F}(B) \implies A \cong B$ .

**Example 18.** Let  $C_1, C_2$  be abelian categories, and  $\mathcal{F}$  an exact functor. Then  $\ker(\mathcal{F}(f)) = \mathcal{F}(\ker(f))$ , and the same holds for cokernels.

**Lemma 26.** Let  $\mathcal{L}$ ,  $\mathcal{R}$  be adjoint functors,  $\mathcal{L}$  fully faithful (i.e.  $\mathcal{R} \circ \mathcal{L} \cong Id$ ),  $\mathcal{R}$  is conservative, then the two functors are inverse pairs in an categorical equivalence.

*Proof.* We need  $\mathcal{RL} \cong Id$ , which follows from  $\mathcal{RLR} \cong \mathcal{R}$  by conservative property, which in turns follows from the fully faithfulness of  $\mathcal{F}$ .

Now back to the discussion on Loc and  $\Gamma$ . We already know that Loc is fully faithful, and it is sufficient to show it is essentially surjective, i.e. every  $\mathcal{F}$  has some M such that  $\mathcal{F} = \widetilde{M}$ . The image of  $\widetilde{M}$  are the functors that have presentations, i.e.  $\mathcal{O}^{\oplus I} \to \mathcal{O}^{\oplus J} \to \mathcal{F} \to 0$ , so it suffices to check that every  $\mathcal{F}$  has a presentation. We check that for every  $\mathcal{F}$ , there exists a surjection  $\mathcal{O}^{\oplus J} \twoheadrightarrow \mathcal{F}$ . To see so, consider  $\Gamma(\mathcal{F}) = \operatorname{Hom}(\mathcal{O}, \mathcal{F})$  (structure sheaf is the terminal object in the category of sheaves). So if we take a set of generators  $m_j, j \in J$  of  $\mathcal{F}$ , we obtain an onto map  $\Gamma(\mathcal{O}^{\oplus J}) \to \Gamma(\mathcal{F})$ , so  $\mathcal{O}^{\oplus J} \to \mathcal{F}$  is surjective.

Remark 20. Results of this type are generally referred to as Morita theories.

Now suppose A contains arbitrary direct sums and that  $\operatorname{Hom}(P, \bullet)$  commutes with the direct sum. We say  $P \in A$  is a projective generator if the P-projection functor,  $X \mapsto \operatorname{Hom}(P, X)$ , is an exact functor, and that  $\operatorname{Hom}(P, X) = 0 \Leftrightarrow X = 0$ . In this case, one can show that  $A \cong \operatorname{\mathbf{Mod}}(\operatorname{End} P)^{opp}$ , and, in particular, as a corollary, we have  $\operatorname{\mathbf{Mod}}(A)_{f,g} \cong \operatorname{\mathbf{Coh}}(X)$ .

**Lemma 27.**  $f: X \to Y$  is an affine morphism if and only if for every open  $U \subseteq U$ ,  $f^{-1}(U)$  is affine.  $f: X \to Y$  is a finite morphism if and only if it is affine and, for every open  $U \subseteq Y$  such that  $U = \operatorname{Spec} A$ , if  $f^{-1}(U) = \operatorname{Spec} B$  then B is a finite A-algebra.

Proof. Let U be affine. By definition, there exists some affine cover  $U = \bigcup U_i$  such that  $f^{-1}(U_i)$  is affine. Write  $V = f^{-1}(U)$ , then we want to have  $V = \operatorname{Spec} A$ . Note that  $k[U_i] = f_*(\mathcal{O})(U_{f_i}) = f_*(\mathcal{O})(U)_{f_i} = A_{(f_i)}$ , and each  $A_{(f_i)}$  is finitely generated. Take all those rings together as an algebra over B = k[U], we obtain a finitely generated ring A. The check that  $V = \operatorname{Spec} A$  is routine. For the second part, suppose  $f: X \to Y$  finite (in the old definition), then  $f_*\mathcal{O}_X$  is a coherent sheaf on Y, i.e.  $f_*\mathcal{O}_X(U)$  is finite over  $\mathcal{O}_Y$  for some open set U.

**Proposition 17.** For any fixed Y, the category of X that has an affine morphism to Y corresponds to the opposite category of quasicoherent sheaves of  $\mathcal{O}_{Y}$ -algebra (which is finitely generated and reduced).

To see this, given any map  $f: X \to Y$  we obviously obtain a sheaf  $f_*\mathcal{O}_X$ . Conversely, given a sheaf  $\mathcal{A}$  of  $\mathcal{O}_Y$  algebra, pick an affine cover  $Y = \bigcup_i U_i$ , glue together all the Spec  $\mathcal{A}[U_i]$  by identifying Spec  $\mathcal{A}[U_i \cap U_j]$  that sits in two copies (here we assume separatedness).

**Proposition 18.** Suppose  $X \to Y$  is affine. Let  $A = f_*\mathcal{O}_X$ , then  $\mathbf{Qcoh}(X) = {\mathbf{Qcoh}(Y) \text{ with an } A \text{ action}}$ , where the map is  $\mathcal{F} \mapsto f_*\mathcal{F}$ .

Let  $i: Z \hookrightarrow X$  be an embedding of a closed subvariety, then  $i_*$  is a full embedding of a subcategory, with one-sided inverse  $i^*$ . It is easy to see that the image of  $i_*$  consists of those  $\mathcal{F}$  such that  $\mathcal{F}|_{X-Z}=0$ . On the other hand, for every  $Z\subseteq X$  we have a subsheaf  $\mathcal{I}_Z\subseteq \mathcal{O}_X$  consisting of those f that vanish on Z. It is obviously an ideal sheaf, and we in fact have a correspondence between closed subvarieties and radical ideal sheaves.

**Proposition 19.**  $i_*: \mathbf{Qcoh}(Z) \to \mathbf{Qcoh}(X)$  (or coherent to coherent) is a full embedding and the image are the  $\mathcal{F}s$  such that  $\mathcal{I}_Z\mathcal{F}=0$ .

For example, consider  $X = \operatorname{Spec} A$ , and let  $Z = \operatorname{Spec} A/I$ , then A/I modules are the A modules that are killed by I. Let U = X - Z, then  $i_*\mathcal{F}|_U = 0$ . Note the converse doesn't hold: there might be  $\mathcal{F}$  that restricts to U to be trivial, but does not come from  $i_*M$  for any M. For instance, let  $X = \mathbb{A}^1, Z = \{0\}$ , let  $M = k[t]/t^2$ ,  $\mathcal{F} = \widetilde{M}$ , and let  $i : k[t] \to k$  that sends t to 0. There does exist a weaker property: if  $\mathcal{F}|_U = 0$ ,  $\sigma$  is a section of  $\mathcal{F}$ , then there exists some n such that  $\mathcal{I}_Z^n \sigma = 0$ . In addition, if  $\mathcal{F}$  is coherent, then we actually have ssome n such that  $\mathcal{I}_Z^n \mathcal{F} = 0$ .

Locally free sheaves of rank 1 are called **invertible sheaves**.

**Example 19.** Let  $X = \mathbb{P}^n$ , then  $\mathcal{O}_{\mathbb{P}^n}(d)(U) = k[\tilde{U}]_d = \{p/q \mid \deg p - \deg q = d, q|_{\tilde{U}} \neq 0\}$  is an invertible sheaf on X, where  $\tilde{U} \hookrightarrow U$  is the projection compatible with  $\mathbb{A}^{n+1} - \{0\} \hookrightarrow \mathbb{A}^{n+1}$ .

We would like to understand maps  $X \to \mathbb{P}^n$ , by which we mean the similar knowledge as the fact that T.F.A.E.:

- Maps  $X \to \mathbb{A}^n$ ;
- Homs  $k[x_1, \ldots, x_n] \to k[X]$ ;
- n-tuple elements in k[X].

And our claim is that T.F.A.E.:

- Maps  $X \to \mathbb{P}^n$ ;
- Invertible sheaves  $\mathcal{L}$  on X with (n+1) elements  $s_0, \ldots, s_n$  in  $\Gamma(\mathcal{L})$  such that they generate  $\mathcal{L}$ .

Here to a map  $f: X \to \mathbb{P}^n$  we assign  $f^*\mathcal{O}(1)$  with sections  $t_0, \ldots, t_n$ . Conversely, given  $\mathcal{L}$  generated by  $s_0, \ldots, s_n$  set  $f = (s_0 : \ldots : s_n)$ , locally we can identify  $\mathcal{L}$  with  $\mathcal{O}$  so  $s_0, \ldots, s_n$  give functions on U with no common zeroes. If  $f_0, \ldots, f_n$  are these functions, then  $x \mapsto (f_0(x) : \ldots : f_n(x))$  is a map  $U \mapsto \mathbb{P}^n$  independent of choice that gives an isomorphism  $\mathcal{L} \cong \mathcal{O}$ .

## Lecture 14: (Quasi)coherent sheaves on Projective Spaces

First an abstract lemma. Let  $\mathcal{L}: \mathcal{C}_1 \to \mathcal{C}_2, \mathcal{R}: \mathcal{C}_2 \to \mathcal{C}_1$  be an adjoint pair; if  $\mathcal{L}$  is fully faithful and  $\mathcal{R}$  is conservative, then they are inverses. The unit is  $Id \xrightarrow{u} \mathcal{L} \circ \mathcal{R}$  and the counit is  $Id \xrightarrow{\varepsilon} \mathcal{R} \circ \mathcal{L}$ . Additionally, we have  $\mathcal{R} \xrightarrow{\varepsilon(\mathcal{R})} \mathcal{R} \circ \mathcal{L} \circ \mathcal{R} \xrightarrow{\mathcal{R}(u)} \mathcal{R} = Id$ .

**Example 20.**  $C_1 = C_2 = \textbf{Vect}$ . Let V be a finite dimensional vector space. Let  $\mathcal{R}: U \to V \otimes U$ ,  $\mathcal{L}: U \to V^* \otimes U = \operatorname{Hom}(V, U)$ . Then the operation above becomes  $V \xrightarrow{\delta \mapsto Id \otimes \delta} V \otimes V^* \otimes V \xrightarrow{E \otimes \delta \mapsto E(\delta)} V$ .

 $\mathcal{L}$  is fully faithful implies  $Id \cong \mathcal{R} \circ \mathcal{L}$ . What about  $\mathcal{L} \circ \mathcal{R} \cong Id$ ? It suffices to use  $\mathcal{R} \to \mathcal{R} \circ \mathcal{L} \circ \mathcal{R} \to \mathcal{R}$ . Last time we showed that the set of affine maps between X and Y is the same as the set of quasicoherent sheaves of  $\mathcal{O}_{X}$ -algebras (which are locally finitely generated and reduced).

**Definition 28.**  $X \to Y$  is a vector bundle if locally  $\cong \mathbb{A}^n \times Y$ , i.e. there exists a covering  $f^{-1}(U_i) \cong \mathbb{A}^n \times U_i$  and agree on the intersection, i.e. the two copies of  $\mathbb{A}^n \times (U_i \cap U_j)$  are glued together using  $GL_n(k[U_i \cap U_j])$ .

The equivalence between the category of locally free sheaves and the category of vector bundles is given by  $\mathcal{E} \mapsto \operatorname{Spec}(\oplus_i \operatorname{Sym}^i(\mathcal{E}))$ , which is a contravariant functor. The opposite maps are from a vector bundle to the sheaf of sections of the dual bundle. Note that the total space is given by  $\operatorname{Tot}(\mathcal{E}) = \operatorname{Spec}(\operatorname{Sym}(\mathcal{E}^{\vee}))$  where  $\mathcal{E}^{\vee} = \operatorname{Hom}(\mathcal{E}, \mathcal{O})$ .

We know that quasicoherent sheaves over an affine variety correspond to the modules over its coordinate ring. What about projective varieties? For a graded module M, define a quasicoherent sheaf on  $\mathbb{P}^n$ , denoted  $\tilde{M}_{\mathbb{P}^n}$ , as follows: its section on U is  $\left(\tilde{M}_{\mathbb{A}^{n+1}}(\tilde{U})\right)_0$ , where  $\tilde{U}$  is the lifting of U to the cone  $\mathbb{A}^{n+1} - \{0\}$ . Say if

 $\mathbb{P}^n \setminus U = Z_f$ , f is a degree d homogeneous polynomial, then  $\tilde{M} = \varinjlim_{f} \frac{1}{f^i} \tilde{M}_{di}$  (again this is formal symbol).

**Proposition 20.** The following are true:

- 1.  $M \mapsto \tilde{M}_{\mathbb{P}^n}$  is an exact functor.
- 2. Every  $\mathcal{F}$  that is a quasicoherent sheaf on  $\mathbb{P}^n$  is of the form  $\tilde{M}$  for some M, every coherent such  $\mathcal{F}$  comes from some finitely generated M.

Moreover, given a quasicoherent sheaf  $\mathcal{F}$  on  $\mathbb{P}^n$ ,  $\mathcal{F} \cong \tilde{M}$  where  $M = \bigoplus_{n \geq 0} \Gamma(\mathcal{F}(n))$ .

**Remark 21.**  $M \to \tilde{M}_{\mathbb{P}^n}$  is not an equivalence. If M is finite dimensional, then  $\tilde{M} = 0$ . Also,  $\tilde{M}_{\mathbb{P}^n}$  depends on the grading. For instance, if M = A (a finite dimensional polynomial ring) is the standard grading, then  $\tilde{M} = 0$ ; but if we use the shifted grading M = A[i], i.e.  $M_d = A_{i+d}$ , then  $\tilde{M} = \mathcal{O}(i)$ .

*Proof.* We have 
$$\mathcal{F} \in \mathbf{QCoh}(\mathbb{P}^n)$$
,  $\mathbb{A}^{n+1} - \{0\} \xrightarrow{j} \mathbb{A}^{n+1}$  and also  $\mathbb{A}^{n+1} \xrightarrow{\pi} \mathbb{P}^n$ . Exercise:  $\pi_* \pi^* \mathcal{F} = \bigoplus_{n \in \mathbb{Z}} \mathcal{F}(n)$ .

On the other hand,  $j_*\pi^*(\mathcal{F})$  is a quasicoherent sheaf on  $\mathbb{A}^{n+1}$ , and its global sections are the same as that of  $\pi^*\mathcal{F}$ , which is the same as that of  $\pi_*\pi^*(\mathcal{F})$ , which is  $\bigoplus_{n\in\mathbb{Z}}\Gamma(\mathcal{F}(n))$ . Let this be denoted M', which contains

 $M = \bigoplus_{n>0} \Gamma(\mathcal{F}(n))$ , and M'/M is concentrated on negative degrees, then we see that  $\widetilde{M'/M}_{\mathbb{P}^n} = 0$ , thus

 $\widetilde{M'}_{\mathbb{P}^n} = \widetilde{M}_{\mathbb{P}^n}$ . On the other hand,  $\widetilde{M'}_{\mathbb{A}^n} = j_*\pi^*\mathcal{F}$ ,  $\widetilde{M'}_{\mathbb{P}^n}(U) = j_*\pi^*(\mathcal{F}(\widetilde{U}))_0 = \pi^*(\mathcal{F})(\widetilde{U})_0 = \mathcal{F}(U)$ . Now suppose the sheaf is coherent. Then  $\mathcal{F} = \widetilde{M}_{\mathbb{P}^n}$  for some  $M, M = \bigcup M^i$ , where each  $M^i$  is a finitely generated module, then  $\mathcal{F} = \bigcup \widetilde{M}^i$ .  $\mathcal{F}$  being coherent implies  $\mathcal{F} = \widetilde{M}^i$  for some i.

**Corollary 18.** If  $\mathcal{F}$  is coherent, then there exists d, k, such that  $\mathcal{O}(-d)^{\oplus k} \to \mathcal{F}$  is a surjection (equivalently, a surjection  $\mathcal{O}^{\oplus k} \to \mathcal{F}(d)$ ). In other words, every coherent sheaf is a quotient of a vector bundle.

Proof. If  $\mathcal{F} = \tilde{M}$ , M finitely generated, pick  $d \geq$  degrees of all generators, it follows then that  $M_{\geq d}$  is generated by  $M_d$ . But then  $\tilde{M}_{\geq d} = \tilde{M}$ . On the other hand, by definition of being finitely generated, we have  $A^{\oplus k}[-d] \to M$  surjective, and then we have  $\mathcal{O}^{\oplus k}(-d) \to \tilde{M}$  surjective.

We have checked that the map  $\mathbf{Mod}_{gr}(A) \to \mathbf{QCoh}(\mathbb{P}^n)$  and  $\mathbf{Mod}_{gr,f.g.}(A) \to \mathbf{Coh}(\mathbb{P}^n)$  are both exact surjective on isomorphism classes and both kill some objects. In the second case,  $\tilde{M} = 0$  iff M is finitely dimensional; in the first case,  $\tilde{M} = 0$  iff M is locally nilpotent, i.e. for every x there exists some d such that  $t_i^d x = 0$  for every i.

**Serre Subcategory** Given an abelian category A, a *Serre subcategory* is a full subcategory closed under extension. If B is a Serre subcategory, then one can define a new Serre quotient category A/B, universal among categories with a functor from A sending B to 0.

**Proposition 21.**  $QCoh(\mathbb{P}^n)$  is equivalent to  $Mod_{gr}(A)$  mod out the locally nilpotent elements, and  $Coh(\mathbb{P}^n)$  is equivalent to  $Mod_{gr,f,g}(A)$  mod out the finite dimensional elements.

Proof. More generally, suppose  $U \subseteq X$  is open, and  $X \setminus U = Z$ , we show that  $\mathbf{QCoh}(U) = \mathbf{QCoh}(X)/\{\mathcal{F} \mid \operatorname{Supp}(\mathcal{F}) \subseteq Z\}$ . The same holds for coherent sheaves. (To get the statement above, take  $X = \mathbb{A}^{n+1}$ ,  $Z = \{0\}$ ,  $U = \mathbb{A}^{n+1} - \{0\}$ .) Recall that A-module M is the same as a quasicoherent sheaf on X. A graded A-module M, on the other hand, corresponds to a quasicoherent sheaf that is equivariant with respect to the multiplicative group  $G_m$  action by definition, where  $G_m = \operatorname{Spec}(k[t, t^{-1}]) \cong \mathbb{A}^1 - \{0\}$ . Then  $\mathbb{P}^n = (\mathbb{A}^{n+1} - 0)/G_m$ , thus  $\mathbf{QCoh}(\mathbb{P}^n) = \mathbf{QCoh}^{G_m}(\mathbb{A}^{n+1} - 0) = \mathbf{QCoh}^{G_m}(\mathbb{A}^{n+1})/(\mathcal{F} \text{ such that } \operatorname{Supp}(\mathcal{F}) \subseteq Z)$ .

Internal Hom and tensor product of quasicoherent sheaves If we have  $\mathcal{F}, \mathcal{G}$  quasicoherent, define the internal hom  $\underline{\mathrm{Hom}}_{\mathbf{QCoh}(U)}(\mathcal{F},\mathcal{G})(U) = \mathrm{Hom}(\mathcal{F}(U),\mathcal{G}(U))$ , then obviously this is a sheaf of  $\mathcal{O}$ -modules. If  $\mathcal{F}$  is coherent, then this is quasicoherent.  $\mathcal{F} \otimes \mathcal{G}$  is the sheafification of the presheaf given by section-wise tensor product, and is a quasicoherent sheaf. In particular, note if X is affine, we have  $\tilde{M} \otimes_{\mathcal{O}} \tilde{N} = M \otimes_A N$ .

**Invertible Sheaves** If  $\mathcal{F}$  is a locally free of rank 1 (a.k.a. an invertible sheaf),  $\mathcal{F} \otimes \mathcal{G}$  is locally isomorphic to  $\mathcal{G}$ . Example:  $\mathcal{O}(n) = \mathcal{O}(1)^{\otimes n}$ . Why are they called invertible? if  $\mathcal{F}$  is locally free of rank n, form  $\mathcal{F}^{\vee} = \underline{\mathrm{Hom}}(\mathcal{F}, \mathcal{O})$ , then  $\mathcal{F}^{\vee\vee} = \mathcal{F}$ , and  $\underline{\mathrm{Hom}}(\mathcal{F}, \mathcal{G}) = \mathcal{F}^{\vee} \otimes_{\mathcal{O}} \mathcal{G}$ . Now if  $\mathcal{F} = \mathcal{L}$  is locally free of rank 1, then  $\mathcal{L}^{\vee} \otimes \mathcal{L} = \underline{\mathrm{Hom}}(\mathcal{L}, \mathcal{L}) = \mathcal{O}$ . Additionally, if  $\mathcal{L}_1, \mathcal{L}_2$  are rank 1 locally free, then their tensor product is again locally free of rank 1. And obviously,  $\mathcal{O} \otimes \mathcal{F} = \mathcal{F}$ .

Corollary 19. Isomorphism classes of invertible sheaves on X is an abelian group under tensor product.

This is known as the Picard group Pic(X). Now let's describe it. For now, let X be irreducible.

**Definition 29.** The Weil divisor group DW(X) is a free abelian group spanned by irreducible codimension 1 subvarieties.

A typical element in there has the form  $D = \sum_{i} n_i D_i$  where  $n_i \in \mathbb{Z}$ , and  $D_i$  are the said subvarieties. If all the  $n_i \geq 0$ , then D is called *effective*.

**Definition 30.** The Cartier divisor group  $DC(X) = \Gamma(\mathcal{K}^*/\mathcal{O}^*)$ , where \* means nonzero, and  $\mathcal{K}$  is the sheaf of rational functions. Another way to describe it is the set of invertible fractional ideals. It can be seen as a subsheaf realized in  $\mathcal{K}^*$ .

**Theorem 14.1.** When X is factorial (for instance, when X is smooth), DW(X) = DC(X). Generally,  $Pic(X) = DC(X)/K^*$ , i.e. the quotient of Cartier divisors by the principal divisors.

We'll see next time that  $Pic(\mathbb{P}^n) = \mathbb{Z} = \{\mathcal{O}(d)\}.$ 

**Example 21.** Using invertible sheaf to embed a variety X in  $\mathbb{P}^n$ . In particular,  $X = \mathbb{P}^1$ . Let  $\mathcal{L} = \mathcal{O}(n)$ , where  $n \geq 1$ ,  $V = H^0(\mathcal{O}(n)) = \operatorname{Sym}^n(k \oplus k)$  (of dimension (n+1)), then we get a map from  $\mathbb{P}^1$  to the projectivization of this space, which is  $\mathbb{P}^n$ . The image of this emdedding corresponds to degree n polynomials that are nth power of linear polynomials.

## Lecture 15: Divisors and the Picard Group

Suppose X is irreducible. The (Weil) divisor  $\text{Div}_W(X)$  is defined as the formal  $\mathbb{Z}$  combinations of subvarieties of codimension 1. On the other hand, the Cartier divisor group,  $\text{Div}_C(X)$ , consists of subvariety locally given by a nonzero rational function defined up to multiplication by a nonvanishing function.

**Definition 31.** An element of  $Div_C(X)$  is given by

- 1. a covering  $U_i$ ; and
- 2. Rational functions  $f_i$  on  $U_i$ ,  $f_i \neq 0$ ,

such that on  $U_i \cap U_j$ ,  $f_j = \varphi_{ij} f_i$ , where  $\varphi_{ij} \in O^*(U_i \cap U_j)$ .

Another way to express this is that  $\operatorname{Div}_C(X) = \Gamma(K^*/\mathcal{O}^*)$ , where  $K^*$  is the sheaf of nonzero rational functions, where  $\mathcal{O}^*$  is the sheaf of regular functions.

Remark 22. Cartier divisors and invertible sheaves are equivalent (categorically). Given  $D \in \operatorname{Div}_{\mathbb{C}}(X)$ , then we get an invertible subsheaf in K, locally it's  $f_i\mathcal{O}$ , the  $\mathcal{O}$ -submodule generated by  $f_i$  by construction it is locally isomorphic to  $\mathcal{O}$ . Conversely if  $L \subseteq K$  is locally isomorphic to  $\mathcal{O}$ , A system of local generators defines the data as above. Note that the abelian group structure on  $\Gamma(\mathcal{K}^*/\mathcal{O}^*)$  corresponds to multiplying by the ideals.

**Proposition 22.**  $\operatorname{Pic}(X) = \operatorname{Div}_C(X)/\operatorname{Im}(\mathcal{K}^*) = \Gamma(\mathcal{K}^*/\mathcal{O}^*)/\operatorname{im}\Gamma(\mathcal{K}^*).$ 

Proof. We already have a function  $\operatorname{Div}_C(X) = \operatorname{IFI} \to \operatorname{Pic}$  (IFI: invertible frational ideals) given by  $(\mathcal{L} \subseteq \mathcal{K}) \mapsto \mathcal{L}$ . This map is an homomorphism. It is also onto: choosing a trivialization  $\mathcal{L}|_U = \mathcal{O}|_U$  gives an isomorphism  $\mathcal{L} \otimes_{\mathcal{O} \supseteq \mathcal{L}} \mathcal{K} \cong \mathcal{K}$ . Now let's look at its kernel: it consits of sections of  $\mathcal{K}^*/\mathcal{O}^*$  coming from  $\mathcal{O} \subseteq \mathcal{K}$ , which is just the same as the set of nonzero rational functions, which is  $\operatorname{im} \Gamma(\mathcal{K}^*) = \Gamma(\mathcal{K}^*)/\Gamma(\mathcal{O}^*)$ .

In many scenarios, we can actually obtain explicit descriptions of the Picard group.

**Theorem 15.1.** If X is locally factorial (i.e.  $\mathcal{O}_{X,x}$  is always an UFD), then  $\mathrm{Div}_W(X) = \mathrm{Div}_C(X)$ .

A remark about factoriality:

- 1.  $k[x_1, ..., x_n]$  is an UFD, and a localization of an UFD is an UFD, from which it follows that  $\mathbb{A}^n$  and  $\mathbb{P}^n$  are locally factorial.
- 2. More generally, for a normal curve X,  $U \subseteq X$ ,  $\mathcal{O}(U)$  is a Dedekind domain (so that it is Noetherian, integrally closed, Krull dimension 1, equivalently, all frational ideals are invertible). In this case,  $\mathcal{O}_{X,x}$  is a DVR, and therefore is an UFD.

**Smoothness** What we care in particular is that if X is smooth, then X is locally factorial. What is smoothness? One description is that if  $x \in X$ , then completion by the topology of the maximal ideal  $\varprojlim \mathcal{O}_{X,x}/\mathfrak{m}_x^n = \widehat{\mathcal{O}_{X,x}}$  (the completed local ring) is isomorphic to  $k[[x_1,\ldots,x_n]]$ .

**Proposition 23.** The following are true:

- 1.  $k[[x_1, ..., x_n]]$  is a UFD.
- 2. If A is a Noetherian local ring such that its completion is an UFD, then A itself is an UFD.

**Remark 23.** The intuition that these local completion rings are the same as local charts for manifolds can be deceptive. For instance, the converse of b) may not be true, i.e. A is an UFD, but its completion is not. Also it may happen that A is an UFD, but A[[x]] is not.

Now observe that if X is a smooth variety, then  $\mathcal{O}_{X,x}$  is a regular local ring, i.e. the maximal ideal  $\mathfrak{m}_x$  is generated by a regular sequence, i.e.  $x_1, \ldots, x_n$  such that  $x_i$  is not a zero divisor in the quotient  $\mathcal{O}_{X,x}/(x_1,\ldots,x_{i-1})$  (in particular,  $x_1$  is not a zero divisor). Observe that every Noetherian regular local ring is a UFD (AuslanderBuchsbaum theorem).

Proof of the Proposition. For the first statement, every finitely generated module has a finite resolution by free finitely generated modules, i.e.  $0 \to F_n \to \ldots \to F_0 \to M \to 0$ . For the second statement, this can be found as [Bou98, VII.7. Corollary 2]. If  $I \subseteq A$  is Notherian local, then it is an intersection of principal ideals, and it has a finite free resolution, then it must be principal.

Now back to the equivalence between Weil and Cartier divisors.

Proof of the Theorem. Consider the map  $\mathrm{Div}_W(X) \to \mathrm{Div}_C(X)$  given by  $[D] \mapsto J_D = \mathcal{O}(-D) \subseteq \mathcal{O} \subseteq \mathcal{K}$ , where  $\mathcal{O}(-D)$  denotes sheaf of functions vanishing on D. We need to know that  $J_D$  is locally principal. (The rest of this paragraph is slightly different from the original proof given in class.) Recall that when we have an UFD, every prime ideal of height one is principal.  $J_D$  is locally induced by a prime ideal of height 1 by definition, so when we pass to the stalk it is induced by  $(f_x)$  for some  $f_x \in \mathcal{K}$ . Now  $(f_x)$  and  $J_D$  only differ on components that do not pass x (as they agree on the stalk), which can only happen on finitely many other components, so after shrinking our local neighborhood we can have  $(f_x)$  agreeing with  $J_D$  on some neighborhood.

Now the map  $[D] \mapsto J_D$  is clearly injective: enough to see that  $[nD] \not\mapsto 0$  when  $n \neq 0$ , wlog when n > 0, but then the image is  $J_D^n \subseteq J_D \neq 0$ . It remains to check that the map is onto. First consider  $\mathcal{L} \subseteq \mathcal{O}$ , we want to find a Weil divisor D that goes to  $\mathcal{L}$ . Can assume that we know this for all  $\mathcal{L}'$  such that  $\mathcal{L} \subseteq \mathcal{L}' \subseteq \mathcal{O}$ . Now pick  $f \in \mathcal{L}$  such that locally  $\mathcal{L} = (f)$ , then we know that all components of  $Z_f$  have codimension 1, i.e. are Weil divisors. If D is such a component, then  $J_D$  contains  $\mathcal{L}$ ; we can assume  $J_D = (\varphi)$ , then  $\varphi^{-1}\mathcal{L}$  strictly contains  $\mathcal{L}$  and is, by assumption, coming from some D', then  $\mathcal{L}$  comes from D + D'. Finally, in the general case,  $\mathcal{L} = (f)$  locally, where  $f = \frac{\alpha}{\beta}$  where  $\alpha, \beta \in \mathcal{O}(U)$ , then we have shown that  $\alpha$  comes from some D,  $\beta$  from some D', then f comes from D - D'.

**Example 22.** Suppose X is a normal curve, and  $\mathcal{L} = (f)$ , coming from  $D = \sum_{i} n_i x_i$ , where  $x_i$  are just points. So what are those values? The local multiplicity of  $x_i$ , i.e.  $n_i$ , is given by  $\operatorname{val}_{x_i}(f)$ .

Another way to describe it is via  $\mathcal{C} = \operatorname{coker}(\mathcal{O} \xrightarrow{f} \mathcal{O})$ . Note that this is a coherent sheaf supported on the zeroes of f, so it splits as  $\bigoplus_{x_i} \mathcal{C}_{x_i}$ , and we claim that each has dim  $\Gamma(\mathcal{C}_{x_i})$  finite, which equals the length of

the sheaf.<sup>1</sup> To see this equivalence, consider the ideal sheaf  $\mathcal{L} = J_x$ , which comes from -(x) by construction, then  $\mathcal{L} = (f)$  is locally isomorphic to  $J_x^n$  (another way of saying the local ring is DVR), then it would come from -(nx), but dim  $\mathcal{O}_{X,x}/\mathfrak{m}_x^n = n$ .

Remark 24. In fact, for any irreducible X, we have a homomorphism in the other direction:  $\operatorname{Div}_{C}(X) \to \operatorname{Div}_{W}(X)$ . For instance, if X is a curve that is irreducible (but not necessarily normal), then we can send  $\mathcal{L} = (f)$  to  $\sum_{i} n_{i}x_{i}$ , where  $n_{i} = \dim \Gamma(\mathcal{C}_{x_{i}})$ . If X is separated, irreducible, regular in codimension 1 (there exists  $Z \subseteq X$ , such that  $\operatorname{codim} Z \geq 2$ , and X - Z is regular), then this is an isomorphism.

Let's do some easy examples.

**Example 23.** The Picard group of  $\mathbb{A}^n$  is trivial (every codimension 1 subvariety is given by a global function).

**Example 24.** What about  $\mathbb{P}^n$ ? it is  $\mathbb{Z}$ , and is generated by  $\{\mathcal{O}(d) \mid d \in \mathbb{Z}\}$ .

Proof. First see  $\mathbb{Z}$  is contained in it because  $\mathcal{O}(d_1) \otimes \mathcal{O}(d_2) = \mathcal{O}(d_1 + d_2)$ , and that  $\mathcal{O}(d) \neq \mathcal{O}$  when d < 0 because the global section vanishes for d < 0. The other inclusion holds because for any  $D \subseteq \mathbb{P}^n$  of codimension 1, there is a homogeneous polynomial P of some degree d generating the homogeneous ideal vanishing on D, then  $J_D = \mathcal{O}_{\mathbb{P}^n}(-d)$  by multiplication by P.

<sup>&</sup>lt;sup>1</sup>A coherent sheaf supported at x is an successive extension of  $\mathcal{O}_x$ , and the length of the sheaf is just the length of this filtration, i.e. number of extension steps needed.

Let's discuss the curve case in more detail. Let X be an irreducible, complete curve (not necessarily normal). Then one invariant of the divisor is the degree (which is  $\deg(\sum_i n_i x_i) = \sum_i n_i$  for Weil divisor, and the degree of the corresponding image in Weil divisor if we have a Cartier divisor). Recall that Picard group is all Cartier divisors mod out all the principal divisors.

Proposition 24. The degree of a principal divisor is zero.

Thus we get a degree homomorphism from the Picard group to  $\mathbb{Z}$ .

#### Lecture 16: Bezout's Theorem

**Definition 32.** Two (Cartier) divisors are linearly equivalent if  $D_1$  -  $D_2$  are principal.

Given an effective divisor D, we have an associated line bundle  $\mathcal{L} = \mathcal{O}(D)$  given (on each open set U) by the sections of  $\mathcal{K}$  whose locus of poles (i.e. locus of zeroes in the dual sheaf) is contained in D. Now suppose X is complete, then given an invertible sheaf  $\mathcal{L}$  on X, a section  $\sigma$  is uniquely (up to multiplication by a constant) determined by its corresponding divisor  $Z(\sigma)$ , so we have a correspondence  $D \overset{(\mathcal{O}(D),1)}{\underset{Z(\sigma)}{\longleftarrow}} (L,\sigma)$ .

Now if  $\sigma_1$ ,  $\sigma_2$  are nonzero sections, then  $f = \sigma_1/\sigma_2$  is an rational function on X, and if  $Z(\sigma_1)$  and  $Z(\sigma_2)$  are linearly equivalent, then f has no pole and no zero; in other words, linearly equivalent divisors correspond to isomorphic line bundles. So the set of all effective divisors linearly equivalent to a fixed effective divisor D form a projective space  $\mathbb{P}\Gamma(\mathcal{O}(D))$ , and is called a *complete linear system of divisors*.

**Proposition 25.** X irreducible curve, deg(D) = 0 if D is a principal divisor.

Proof. D is principal, so let  $D = (f) = D_0 - D_\infty$  where  $f : X \to \mathbb{P}^1$ ,  $X = U_1 \cup U_2$ ,  $f \in k[U_1], 1/f \in k[U_2]$ , (This is clear for X normal: all local rings are DVR, so either f or 1/f is in  $\mathcal{O}_{X,x}$ .) where  $D_0 \subseteq f(\mathbb{P}^1 - \{\infty\})$  is the divisor of zeroes of f, and similarly  $D_\infty \subseteq 1/f(\mathbb{P}^1 - \{0\})$  is the divisor of zeroes of 1/f. We need to check that degree of  $D_0$  is the same as that of  $D_\infty$ , and that the degree of both slices are that of  $\deg(f)$ .

check that degree of 
$$D_0$$
 is the same as that of  $D_{\infty}$ , and that the degree of both slices are that of  $\deg(f)$ .

Recall that  $D_0 = \sum_{x \in f^{-1}(\mathbb{P}^1 - \{\infty\}), f(x) = 0} m_x x$ , where  $m_x = \operatorname{length}(\mathcal{O}/f\mathcal{O})_x = \dim(\Gamma((\mathcal{O}/f\mathcal{O})_x))^2$ . Clearly

 $f: U = f^{-1}(\mathbb{A}^1) \to \mathbb{A}^1$  is finite, and that  $f_*(\mathcal{O}_X|_U)$  is a locally free sheaf of rank equal to the degree of f. From classification of finitely generated modules over k[t], we know that every module is the sum of its torsion and a free module; but this one cannot have torsion because there can be no function of X that vanishes away from finitely many points, so it's free.

 $f_*\mathcal{O}$  is coherent follows from f being finite, which follows from that f is complete and has finite fibers. Now suppose  $k[f^{-1}(\mathbb{A}^1)]$  is a free module of rank d over  $k[t] = k[\mathbb{A}^1]$ . Then  $[K(X):K(\mathbb{A}^1)] = d$ , which is the degree of the map. Thus  $d = \dim(k[f^{-1}(\mathbb{A}^1)]/t)$  (dimension of fiber of  $f_*\mathcal{O}$  at 0) =  $\dim(\Gamma(\mathcal{O}_{U_1}/f\mathcal{O}_{U_1})) = \dim(\Gamma(\mathcal{O}_{U_1}/f\mathcal{O}_{U_1})_x)$ ) =  $\deg(D_0)$ , where  $U_1 = f^{-1}(\mathbb{A}^1)$ . The other half is dealt with similarly.

**Remark 25.**  $k = \mathbb{C}$ , X normal,  $X(\mathbb{C})$  (the set X equipped with the complex topology) is a smooth compact Riemann surface (1-dimensional  $\mathbb{C}$ -manifold).  $f \in K(X)$  defines a meromorphic function on  $X(\mathbb{C})$ ,  $(f) = \sum n_x x$ , n being the order of zero/pole, or just  $\operatorname{Res}_x \frac{df}{f}$ , which tells us that  $\sum_{x \in X(\mathbb{C})} \operatorname{Res}_x \frac{df}{f} = 0$ .

**Proof of Bezout's Theorem** The multiplicity of intersection of two curves X, Y in  $\mathbb{P}^2$  at x (X, Y have no common components) is defined as  $\operatorname{mult}_x(X, Y) = \operatorname{length}(i_*\mathcal{O}_X \otimes_{\mathcal{O}(\mathbb{P}^2)} j_*\mathcal{O}_Y)_x = \dim \Gamma((i_*\mathcal{O}_X \otimes_{\mathcal{O}(\mathbb{P}^2)} j_*\mathcal{O}_Y)_x)$ . Note that  $(i_*\mathcal{O}_X \otimes_{\mathcal{O}(\mathbb{P}^2)} j_*\mathcal{O}_Y) = \bigoplus_{x \in X \cap Y} (i_*\mathcal{O}_X \otimes_{\mathcal{O}(\mathbb{P}^2)} j_*\mathcal{O}_Y)_x$ . This agrees with earlier definition.

**Theorem 16.1** (Bezout's Theorem). 
$$\sum_{x \in X \cap Y} \operatorname{mult}_x(X,Y) = \deg(X) \deg(Y).$$

*Proof.* Both sides are additive under  $X = X_1 \cup X_2$  where the two curves have no common components. (Clear for RHS, LHS as exercise.) Now we can assume X is irreducible, and we'll show LHS =  $\deg(\mathcal{O}(Y)|_X)$ .  $\mathcal{O}(Y)$  is a line bundle with a section  $\sigma$  such that  $(\sigma) = Y$ . We know that  $\mathcal{O}_Y = \mathcal{O}/\mathcal{O}(-Y)$  from which

it follows that  $\mathcal{O}_X \otimes \mathcal{O}_Y = \mathcal{O}_X/\text{im } \sigma|_X$  (where  $\sigma$  denotes  $\mathcal{O}(-Y) \xrightarrow{\sigma} \mathcal{O}$ ). Compare with the definition of multiplicity above, it follows that the divisor of zeroes of  $\sigma|_X$ , i.e. the pullback of  $\sigma$ , is  $\sum \text{mult}_x(X,Y)x$ .

Now we know that  $\mathcal{O}(Y) \cong \mathcal{O}(d)$  where  $d = \deg(Y)$ , so the isomorphism class and hence the degree of  $\mathcal{O}(Y)|_X$  depends only on the degree of Y. Now we can take Y to be the union of d lines; by additivity, we reduce to the case where Y is a line. Since Y and X are symmetric, also reduce to X is a line, from which the result follows.

 $<sup>^{2}</sup>$ The subscript here refers to the canonical split of sheaves supported at finitely many points, NOT stalks; the same for below.

The analytic story Let X be an irreducible normal curve over  $\mathbb{C}$ , then  $X(\mathbb{C})$  is a compact 1-dimensional  $\mathbb{C}$ -manifold homeomorphic to a sphere with g handles, g being the genus of the curve. One can look at the topological homology  $H^1(X,\mathbb{Z})=\mathbb{Z}^{2g}$ . The important variant here is the space of differential forms. Define  $\Omega^1$  to be the sheaf of holomorphic 1-forms, e.g. f(z)dz. The global section  $\Gamma(\Omega^1)\cong\mathbb{C}^g$ . Now, since we have Poincare duality, we can define a map from de Rham classes to singular cohomology as follows: given an 1-form  $\omega$ , we map it to  $\operatorname{Hom}(H_1(X,\mathbb{C}),\mathbb{C})=H^1(X,\mathbb{C})=\mathbb{C}^{2g}$  as  $[c]\mapsto \int_c\omega$ . Thus we have  $H^1(X,\mathbb{C})=\operatorname{Im}(\Gamma(\Omega^1))\oplus \overline{\operatorname{Im}(\Gamma(\Omega^1))}=H^{1,0}\oplus H^{0,1}$ , usually called the  $\operatorname{Hodge}$  decomposition.

Recall the GAGA theorem, which states that holomorphic line bundles are the same as algebraic line bundles, which are parametrized by the Picard group. Now Picard group is (Divisors) / (Principle Divisors), and there is a degree homomorphism  $\operatorname{Pic} \to \mathbb{Z}$ , with the kernel denoted  $\operatorname{Pic}^{\circ}$ . It turns out that  $\operatorname{Pic}^{\circ} \cong \Gamma(\Omega^1)^*/H_1(X,\mathbb{Z})$  (image of  $H_1(X,\mathbb{Z}) \subseteq H_1(X,\mathbb{C})$  under the integral map)  $\cong \mathbb{C}^g/\mathbb{Z}^{2g}$ . The structure  $\Gamma(\Omega^1)^*/H_1(X,\mathbb{Z})$  is usually called the *Jacobian* of the curve, and the isomorphism the *Abel-Jacobi map*.

If D=(f) is a principal divisor, D gets mapped into 0 by the Abel-Jacobi map above. Sketch of proof: given f from  $X \to \mathbb{P}^1$ , consider a family of divisors  $D_0 - D_z$ ,  $z \in \mathbb{P}^1$ . If z=0, then this is the 0 divisor; when  $z=\infty$ , we get our divisor D=(f). Easy to see that  $z\mapsto AJ(D_0-D_z)$  is a holomorphic function  $\mathbb{CP}^1 \to \mathbb{C}^g/\mathbb{Z}^{2g}$ . Since  $\mathbb{CP}^1$  is simply connected, it lifts to  $\mathbb{CP}^1 \to \mathbb{C}^g$ , which is constant by maximal principle.

Our next topic is smoothness, which is a local property. Let X be an algebraic variety, and x be a point. Define  $\dim_x(X)$  to be the maximum of dimensions of components passing through x.

**Definition 33.** x is a smooth point on X if  $\dim_x(X) = \dim(\mathfrak{m}_x/\mathfrak{m}_x^2)$ , where  $\mathfrak{m}_x$  is the maximal ideal in  $\mathcal{O}_{X,x}$ .

**Example 25.** Suppose X in  $\mathbb{A}^n$  is a hypersurface (so codimension 1),  $I_X = (f)$ . Then x is a smooth point iff  $\partial f/\partial z_i \neq 0$  at x for some i.

**Corollary 20.** For X, Y curves in  $\mathbb{P}^2$ , the intersection multiplicity is greater than 1 if either X or Y is not smooth at x.

To see this, suppose  $x = (0,0) \in \mathbb{A}^2$ , then  $\mathcal{O}_X \twoheadrightarrow k[x,y]/(x,y)^2$ , then  $\mathcal{O}_X \otimes \mathcal{O}_Y \twoheadrightarrow \mathcal{O}_Y/\mathfrak{m}_{\mathcal{O}_Y}^2$ .

## Lecture 17: Abel-Jacobi Map, Elliptic Curves

Few more remarks on the analytics theory. Last time we let X be a smooth compact  $\mathbb{C}$ -manifold of dimension 1, obtained from a normal, complete curve over  $\mathbb{C}$ . (In fact, any smooth compact  $\mathbb{C}$ -manifold of dimension 1 is obtained from an algebraic curve; note that this fails for dimension  $\geq 2$ ). In this case,  $\operatorname{Pic}^{\circ}(X) = \operatorname{Div}(X)/\operatorname{PDiv}(X)$ . We remarked that we have a map from it to  $\Gamma(\Omega^{1}(X))^{*}/H_{1}(X,\mathbb{Z}) = \mathbb{C}^{g}/\mathbb{Z}^{2g}$  (the Abel-Jacobi map).

**Theorem 17.1.** X can be reconstructed from the lattice  $H_1(X,\mathbb{Z}) \subseteq \Gamma(\Omega^1)^*$ .

This can be generalized to smooth complete varieties in any dimension. Instead of degree, we consider a map  $\text{Div} \to H_{n-2}(X)$ , and principal divisors are the preimages of 0. There is another  $\text{Pic}(X) \to H_{n-2}(X)$  with kernel  $\text{Pic}^{\circ}(X)$ , and the theorem reads  $\text{Pic}^{\circ}(X) = \Gamma(\Omega^{n-1}(X))^*/H_1(X,\mathbb{Z})$ .

**Proposition 26.** Pic $^{\circ}(X)$  is itself a complex variety as well as a compact abelian Lie group. In fact, one can define an algebraic group Jac(X) on it, such that for a curve X, the A-J map is algebraic.

To formally define the Jacobian, one defines a functor it represents. More explicitly, for a variety S, one define a family of invertible sheaves of X parametrized by S, which is essentially an invertible sheaf on  $S \times X$ , modulo the line bundles pulled back from S.

**Theorem 17.2.** Let g be the (geometric) genus of X and assume it equals 1. Then  $\mathbb{C}^g/\mathbb{Z}^{2g} = \mathbb{C}/\mathbb{Z}^2$  has dimension 1 and is therefore a curve. Fix  $x_0 \in X$ . The A-J map gives a map  $X \to \operatorname{Pic}^{\circ}(X)$ , where we send x to  $x - x_0$ . Then this is an isomorphism.

Corollary 21. Every normal curve of genus 1 has a group structure (they are called the elliptic curves).

As an example, consider  $X \subseteq \mathbb{P}^2$  is the projective closure  $y^2 = P(x) = x^3 + ax + b$  (char  $k \neq 2, 3$ ) (and assume no multiple roots). We'll check today that X is a smooth curve by showing it's normal and irreducible

Assume  $k = \mathbb{C}$ , we claim that g = 1, i.e. the topological Euler character is 0. Consider the map  $(x,y) \mapsto x$ , which extends to a morphism  $X \to \mathbb{P}^1$ . This is of degree 2 and has four ramification points: the roots of P(x) as well as the infinity. Thinking in classical topology and choose your favorite argument, we know that  $\text{Eul}(X) = 2\text{Eul}(\mathbb{CP}^1) - 4 = 0$ .

Now let's consider how to write down the composition (group) law. To do so, we first fix the initial point  $x_0=(0:1:0)$ , where we see that  $\{x_0\}=X\cap\mathbb{P}^1_\infty$ . The complex story suggests that we have a group law on X, such that for every  $x,y\in X$ , we have the divisor equivalence  $(x+y)-x_0\sim (x-x_0)+(y-x_0)$  (where +E denotes the addition using the group law), in other words,  $(x+y)-x_0-x_0$ . We know that for every two lines  $l,l'=\mathbb{P}^1\subseteq\mathbb{P}^2$  we have  $(l\cap X)\sim (l'\cap X)$  (we discussed this before). Now take  $l'=\mathbb{P}^1$ , then  $(l'\cap X)=3x_0$ . Write  $l\cap X=x_1+x_2+x_3$ , then  $(x_1-x_0)+(x_2-x_0)+(x_3-x_0)\sim 0$  in  $\mathrm{Pic}(X)$ . So we should expect  $x_1+x_2+x_3=0$ . Now we construct the group law. For  $x=(a,b)\subseteq X$ , x'=(a,-b), we have  $x+x'+x_0\sim 3x_0\in \mathrm{Pic}$ , so we define x+x'=0. Now in general, define x+x to be the 3rd point in  $l\cap X$ , where l passes through x' and y'. One can directly check that this is a group law that makes X an abelian algebraic group.

**Remark 26.** Over  $\mathbb{C}$ ,  $X = \mathbb{C}/\mathbb{Z}^2$  makes it clear that for all N > 0 we have  $\{x \in X \mid Nx = 0\} \cong (\mathbb{Z}/N\mathbb{Z})^2$ . This can be checked algebraically to hold for k of characteristic  $p \nmid N$ . If N = p, then this group is  $\mathbb{Z}/p$ , or trivial if X is respectively ordinary or supersingular.

Consider  $X_0 \subseteq \mathbb{A}^2$  given by  $\{(x,y) \mid y^2 = P(x)\}$ . If  $X_0 - \{z\}$  is affine, then it corresponds to  $k[X_0]_{(f)}$  where f is a function in  $k[X_0]$  such that  $f(x) = 0 \Leftrightarrow x = z$ , which is iff  $(f) = Nz - Nx_0$  for some N (where  $x_0$  is the group law identity, which is the infinite point). For a given N there are  $N^2 - 1$  such z.

Last time we proved that if X is normal irreducible complete curve,  $f \in K(X)$ , then it defines some  $f: X \to \mathbb{P}^1$ , then the divisor (f) is  $(f_0) - (f_\infty)$  where  $\deg(f_0) = \deg(f_\infty) = \deg(f)$ . We proved this modulo the following proposition, which we shall prove today:

**Proposition 27.** A non-constant map between irreducible compact curves is finite.

**Normalization** Let X be an irreducible variety, F = K(X) be the field of rational functions on X. Let E/F be a (finite) field extension. Then build a new variety as follows:

**Proposition 28.** There exists a variety Y along with a finite map  $f: Y \to X$  such that for every affine open  $U \subseteq X$ ,  $k[f^{-1}(U)] = \overline{k[U]}_E$  (the integral closure).

If E=F, then Y is called a renormalization of X. In fact, Y is the unique normal variety with a finite onto map to X with the fractional field being E.  $\overline{k[U]}_E$  is finitely generated as a k[U]-module, or equivalently, as a ring. In other words k[U] is a Nagata ring. Sketch of proof to this: using Noether normalization reduce to  $X=\mathbb{A}^n$ . Consider separately the case of purely inseparable and the separable extensions. For separable extension case, the bilinear form  $(x,y)\mapsto \operatorname{Tr}(xy)$  on E as an F-vector space is not degenerate, so if we pick a basis  $(y_i)$  for E/F which lies in  $\overline{k[x_1,\ldots,x_n]_E}$ , then  $\overline{k[x_1,\ldots,x_n]_E}\subseteq \{e\in E\mid \operatorname{Tr}(ex_i)\in A\}$  is a finitely generated algebra for  $A=k[x_1,\ldots,x_n]$ . Now the assignment  $U\mapsto \overline{k[U]}_E$  extends to a coherent sheaf A of rings on X, and let  $Y=\operatorname{Spec}_X(A)$ .

**Corollary 22.** Given  $f: X \to Y$  where X, Y are irreducible, if X is normal, f is finite, onto, then X can be reconstructed from Y and  $f^{-1}(U)$  for some open  $U \neq \emptyset \subseteq Y$ .

**Example 26.** Let  $X = V(x^3 - y^2)$ , then the normalization of X is  $\mathbb{A}^1$ , and the map is  $t \mapsto (t^2, t^3)$ .

**Lemma 28.** If  $f: X \to Y$  is a map of irreducible curves, suppose f is onto, birational, Y is normal, then f is an isomorphism.

*Proof.* Let  $\varphi \in K(Y)$ ,  $\varphi$  on  $f^{-1}(U) \Leftrightarrow \varphi$  is regular on U. If  $\varphi$  is not,  $\varphi^{-1}$  is regular and is 0 at some  $x \in U$ . Suppose  $y \mapsto x$ , then  $\varphi$  is not regular at y.

**Lemma 29.** Suppose  $X \to Y$  is birational map, X is complete, Y is normal, then  $X \cong Y$  iso.

*Proof.* Since f(X) is closed and not finite, we know f must be onto.

Proof of Proposition 27.  $X \to Y$  is a map of complete curves. We can assume X is normal. Then it factors through normalization  $X \to \text{Nor}(Y) \to Y$ . The first is isomorphism by assumption, and the second map is finite by construction.

**Tangent Space** Now let X be an algebraic variety,  $x \in X$ . Let us define the Zariski tangent space  $T_xX$ . We first we note the tangent space to a smooth manifold is the fiber of the bundle of vector fields  $\operatorname{Vect}(M) = \operatorname{Der}(\mathcal{C}^{\infty}(M))$ . Each vector field v gives a linear map  $\delta_v : \operatorname{Fun}(M) \to \mathbb{C}$  that maps f to  $v \cdot f|_x$ , so we see that  $\delta_v(fg) = f(x)\delta_v(g) + g(x)\delta_v(f)$ . This suggests the definition  $T_xX \subseteq \operatorname{Hom}_k(\mathcal{O}_{X,x},k)$  given by  $\{\xi \mid \xi(fg) = f(x)\xi(g) + g(x)\xi(f)\}$ . The cotangent space  $T_x^*X$  is the dual  $(T_xX)^*$ , and we can describe it as  $\mathfrak{m}_x/\mathfrak{m}_x^2$ . In particular, for  $X = \operatorname{Spec}(A)$ ,  $\operatorname{Vect}(X) = \operatorname{Der}(A) = \{\delta : A \to A \text{ $k$-linear } | \delta(fg) = \delta(f)(g) + f\delta(g)\}$ .

#### Lecture 18: Kähler Differentials

Last time we proved that principal divisors on a complete normal curve has degree zero. This actually remains true for Cartier divisors on irreducible non-normal curves. To prove this, we show that the degree of a divisor is preserved under pull-back to normalization. Let D be a principal divisor on a non-normal irreducible curve X. We may assume that D=(f) is supported at a point x, the curve is complete and normal away from x, so that f defines a map  $X \to \mathbb{P}^1$ . The total degree of the divisor of zeroes of f is the same on X and on the normalization Nm(X), both are equal to the degree  $deg(\tilde{f})$ , where  $\tilde{f}$  is the composition  $Nm(X) \to X \to \mathbb{P}^1$ .

Today we begin the discussion of tangent and cotangent spaces and smoothness. The first step is to define (Kähler) differentials.

**Definition 34.** Let A be a commutative k-algebra.  $\Omega_A$  is defined to be the A-module generated by expressions  $da, a \in A$ , modulo the following equations:

- d(a+b) = da + db;
- $d(\lambda a) = \lambda da$ ;
- d(ab) = (da)b + a(db),

where  $a, b \in A$ ,  $\lambda \in k$ . Then  $\Omega_A$  is characterized by a universal property:  $Hom(\Omega_A, M) = Der(A, M)$  for any A-module M, where Der(A, M) is the k-module of k-linear derivations from A to M.

As an alternative way to define  $\Omega_A$ , suppose that A is generated by  $a_1, \ldots, a_n$ . Let  $X = \operatorname{Spec} A$  and  $I_m$  be the ideal of X in the diagonal  $X \subset X \times X$ . Then  $(a_i \otimes 1 - 1 \otimes a_i)$  generate  $I_m \subset A \otimes A$ . Therefore  $\Omega_A$  is finitely generated. This approach also allows us to define a coherent sheaf  $\Omega_X$  on X, called the sheaf of differentials on X.

Let  $f: A \to B$  be a morphism of rings. Then there is a canonical morphism  $B \otimes_A \Omega_A \to \Omega_B$  given by  $da \mapsto d(fa)$ . Let Y = Spec B. Then this morphism of rings gives rise to the morphism of varieties  $Y \to X$ ,  $df: f^*\Omega_X \to \Omega_Y$ .

Now for an arbitrary variety X over k, we may define the sheaf  $\Omega_X$  by gluing the above constructions on affine charts. Then it is straightforward to check that  $Hom(\Omega_X, \mathcal{F}) = Der(\mathcal{O}_X, \mathcal{F})$ , where  $\mathcal{F}$  is a coherent sheaf on X, and  $Der(\mathcal{O}_X, \mathcal{F})$  is the set of k-linear derivations  $\mathcal{O}_X \to \mathcal{F}$ , i.e. sheaf morphisms satisfying Leibniz rule on each chart.

**Definition 35.** Let X be a variety. The Zariski cotangent space of X at  $x \in X$  is defined to be the vector space  $\{\xi : \mathcal{O}_{X,x} \to k \mid \xi \text{ is linear and } \xi(fg) = f(x)\xi(g) + g(x)\xi(f)\}$ , i.e. it is the set of derivations at x, and it is denoted as  $T_x^*X$ .

One can check that  $(\Omega_X)_x = T_x^* X$ .

Now we define the tangent sheaf  $\mathcal{T}_X$  on X as  $\mathcal{T}_X = Hom(\Omega_X, \mathcal{O}_X)$ . Note however that even though there is always a map  $\Omega_X \to Hom(\mathcal{T}_X, \mathcal{O}_X)$ , it is not necessarily an isomorphism.

Lemma 30.  $\dim(T_x^*X) \geq \dim_x(X)$ .

*Proof.* We may assume  $X = \operatorname{Spec} A$  and  $\mathfrak{m}$  the maximal ideal corresponding to x. Let  $df_1, \dots, df_n$  be the generators of  $\mathfrak{m}/\mathfrak{m}^2$ , where each  $df_i$  is lifted to  $f_i \in \mathfrak{m}$ . By Nakayama lemma,  $f_i$  generate  $\mathfrak{m}$ . Now, as a consequence of the hypersurface theorem,  $\dim_x X \leq n$ .

**Definition 36.** Let  $x \in X$ . X is said to be smooth at x if  $\dim(T_x^*X) = \dim_x(X)$ .

**Proposition 29.** X is smooth at  $x \in X$  if and only if  $\Omega_X$  is locally free on a neighborhood of x.

*Proof.* One direction (from right to left) will follow from the next proposition. For the other direction (from left to right), recall the lemma stated during the lecture on October 22th, asserting that if all fibers of a coherent sheaf have the same dimension, then the sheaf is locally free, combined with the fact (that we will prove next time) that smooth varieties are locally irreducible.

**Proposition 30.** For a variety X, the set of smooth points in X is open and dense in X.

denote by  $X_{sm}$ , is open in X. Now, to prove that  $X_{sm}$  is dense in X, we may assume X is affine and irreducible, and is actually embedded as a closed subset  $X \subset \mathbb{A}^n$ . Let  $d = n - \dim X$ . We proceed by induction on d. If d = 0 then  $X = \mathbb{A}^n$ , which is smooth everywhere, and there is nothing to prove. Now for d > 0, we may find  $g \in k[\mathbb{A}^n]$  vanishing on X. choose g to have minimal degree among such functions. We claim that  $\frac{\partial g}{\partial x_i}$  is not identically zero on X for at least one  $x_i$ . To see this, suppose to the contrary that  $\frac{\partial g}{\partial x_i}$  is identically vanishing on X. If chark = 0, by the minimality of degree of g, this means g is a constant function which is not zero. Then g cannot vanish on X, a contradiction. if chark = p, then replacing g with  $g^{1/p}$  gives a function identically vanishing on X with a smaller degree than g, a contradiction. Hence the claim holds. After a change of coordinate, we may assume that g is monic in  $x_n$  and  $\frac{\partial g}{\partial x_n}$  is not identically zero on X. now, consider the projection  $\pi: \mathbb{A}^n = \operatorname{Spec} k[x_1, \cdots, x_n] \to \mathbb{A}^{n-1} = \operatorname{Spec} k[x_1, \cdots, x_{n-1}]$ . Let Y be the image of X under this projection. Then since  $\pi$  is finite,  $\dim Y = \dim X$ . Since Y is a closed subset of  $\mathbb{A}^{n-1}$  we may apply the induction hypothesis on Y, so that the smooth points of Y consist an open and dense subset of Y. Now we claim that if  $x \in X$  is such that  $\frac{\partial g}{\partial x_n} \neq 0$  at x and  $\pi(x)$  is a smooth point of Y, then X is smooth at x. Indeed, for such x,  $\pi: X \to Y$  induces a surjection  $T^*_{\pi(x)}Y \oplus (gdx_n|_x)/dg|_x \to T^*_xX$ . Therefore,  $\dim T^*_x X \leq \dim T^*_y Y = \dim Y = \dim X$ . By a previous lemma,  $\dim T^*_x X = \dim X$ . Hence x is a smooth point of X. The set of all such x is dense in X, hence  $X_{sm}$  is dense in X.

*Proof.* It follows from the previous proposition (left to right) that the set of smooth points in X, which we

**Remark 27.** A curve is defined to be a variety of dimension one. For a curve X, the following are equivalent:

- X is smooth.
- All the local rings of X are  $DVR(=discrete\ valuation\ ring)s$ .
- X is normal.

**Remark 28.** As a final remark, let X be a hypersurface in  $\mathbb{A}^n$  with  $I_X = (f)$ . Let  $x \in X$ . Then X is smooth at x if and only if  $I_X$  is locally generated by some  $f_1, \dots, f_m$  such that  $\operatorname{rank}(\frac{\partial f_i}{\partial x_j}) = m$ . This is also equivalent to saying that  $\widehat{\mathcal{O}_{X,x}} := \varprojlim_{x} \mathcal{O}_{X,x}/\mathfrak{m}_x^n \cong k[[x_1, \dots x_m]]$ .

# Lecture 19: Smoothness, Canonical Bundles, the Adjunction Formula

Last time we defined  $\Omega_X$ ,  $T_xX$  and smoothness. We proved that any X contains an open dense smooth subset, that X is smooth at x if and only if  $\Omega_X$  is locally free around x, and X is smooth if and only if  $\Omega_X$  is locally free.

Here's a trivial observation: suppose we have a surjection  $f: A \to B$  and  $\mathfrak{m}_B \in B$  an maximal ideal, let  $\mathfrak{m}_A = f^{-1}\mathfrak{m}_B$ , then  $\mathfrak{m}_B/\mathfrak{m}_B^2 = \mathfrak{m}_A/\mathfrak{m}_A^2 + I$  where  $I = \ker(f)$ . If  $Y = \operatorname{Spec} B$  contains  $X = \operatorname{Spec} A$ ,  $y \in X \subseteq Y$ , then  $T_y^*Y = T_y^*X/(df_i)$ , where  $f_i$  are generators of I.

#### Corollary 23. We have the following:

- 1. If  $X \subseteq \mathbb{A}^n$  is a hypersurface given by the equation  $I_X = (P)$ , then  $x \in X$  is smooth if and only if  $dP|_x \in T_x^* \mathbb{A}^n \neq 0$ , i.e.  $\frac{\partial P}{\partial x_i}\Big|_x \neq 0$  for some i.
- 2. Suppose  $X \subseteq \mathbb{A}^n$  has dimension n-m where  $I_X = (f_1, \ldots, f_m)$  (this is not true for all X), then X is smooth at a point x if and only if  $df_i|_x \in T_x^* \mathbb{A}^n = k^n$  are linearly independent, i.e. the m-by-m matrix  $\left( \left. \frac{\partial f_i}{\partial x_j} \right|_x \right)$  has rank m.

*Proof.* The first claim is a particular case of the second.  $\dim(X) \ge \dim_x X \ge n - m \implies \dim_x X = n - m$ . Now apply the definition of smoothness, and that  $T_x^*X = T^*\mathbb{A}^n/(df_i|_x)$ .

If  $X \subseteq \mathbb{P}^m$  has dimension n-m,  $I_X = (F_1, \dots, F_m)$  for homogeneous polynomials, then  $x = (x_0, \dots, x_n)$  is a smooth point if and only if  $\left(\frac{\partial f_i}{\partial x_j}\Big|_x\right)$  has rank m. To see this, note that X is smooth at x if and only if  $C_X$  (the cone) is smooth at  $\tilde{x}$  because  $C_X$  is locally isomorphic to  $X \times \mathbb{A}^1$ , and note that  $T^*_{(x,y)}(X \times Y) = T^*_x X \oplus T^*_y Y$ .

**Proposition 31.** Suppose  $X \subseteq \mathbb{A}^n$ ,  $x \in X$  is a smooth point if and only if  $\exists f_1, \ldots f_m \in I_X \subseteq k[x_1, \ldots, x_n]$  which locally generate  $I_X$  and  $df_i|_x$  are linearly independent.

Proof. If  $f_1, \ldots, f_n$  as above exists, then  $\dim(T_x^*X) = n - m$  while  $\dim_x X \geq n - m$  also  $\dim_x X \leq (\dim T_x^*X) \Longrightarrow \dim_x X = \dim T_x^*X$  i.e. x is a smooth point. Conversely, suppose X is smooth at x, pick  $f_1, \ldots, f_m \in I_X$  such that  $f_i|_x$  form a basis in  $\ker(T_x^*\mathbb{A}^n \to T_x^*X)$ . Then by the first part of the proof,  $Z = (f_1, \ldots, f_m)$  is smooth at x with  $\dim_x Z = n - m = \dim_x X$ , where  $Z \supseteq X$ . So we are done if we know that Z is locally irreducible, which follows from the next lemma:

**Lemma 31.** 
$$\widehat{\mathcal{O}_{Z,x}} = \varprojlim_n k[Z]/\mathfrak{m}_x^n \cong k[[t_1,\ldots,t_{n-m}]]$$
 (i.e. is a free ring).

Why does this imply Z locally irreducible? Z locally irreducible means  $\mathcal{O}_{Z,x}$  has no zero divisors, which would follow from the fact that  $\mathcal{O}_{Z,x}\subseteq\widehat{\mathcal{O}_{Z,x}}$  which follows from Nakayama. In particular,  $\ker(\mathcal{O}_{Z,x}\to\widehat{\mathcal{O}_{Z,x}})=\bigcap_{x}\mathfrak{m}_x^n$  which is a finitely generated ideal  $\mathcal{O}_{Z,x}$  is Noetherian, and we have  $\mathfrak{m}_xI=I\Longrightarrow I=0$ .

**Remark 29.** This lemma is equivalent to that  $\bigoplus_n \mathfrak{m}_x^n/\mathfrak{m}_x^{n+1}$  (the associated graded ring) is isomorphic to  $k[t_1,\ldots,t_n]$ . The general case is given in the next lemma.

**Lemma 32.** Let A be a ring,  $\mathfrak{m}$  a maximal ideal,  $a \in A$ . Suppose  $a \in \mathfrak{m}^p$ , write  $\overline{a} \in \overline{A}_p = \mathfrak{m}^p/\mathfrak{m}^{p+1}$  and  $\overline{A} = \bigoplus_n \mathfrak{m}^n/\mathfrak{m}^{n+1}$ . Then  $\overline{A/(a)} = \bigoplus_n (A/a)^n/(A/a)^{n+1} = \overline{A}/(\overline{a})$  if  $\overline{a}$  is not a zero divisor.

*Proof.*  $(\overline{A/(a)})_n = \mathfrak{m}^n/(\mathfrak{m}^{n+1} + (aA \cap \mathfrak{m}^n)), \overline{A}/(\overline{a}) = \mathfrak{m}^n/\mathfrak{m}^{n+1} + a\mathfrak{m}^{n-p}$ . For any  $x \in \mathfrak{m}^k$ , we have  $ax \in \mathfrak{m}^{k+p}$ ; if  $\overline{a}$  is not a zero divisor, then  $x \notin \mathfrak{m}^{k+1}$ , then  $ax \notin \mathfrak{m}^{k+p+1}$ .

Now we return to the first lemma.  $f_1, \ldots, f_n$  have linearly independent differential at x, by induction check  $k[x_1, \ldots, \widehat{x_n}]/(f_1, \ldots, f_i) = k[[t_1, \ldots, t_{n-1}]]$ , i.e.  $\operatorname{gr}(k[x_1, \ldots, x_n]/(f_1, \ldots, f_i)) \cong k[t_1, \ldots, t_{n-1}]$ , and if so, wlog can assume  $f_{i+1} = t_1$ .

**Proposition 32.** X is smooth at x iff  $\widehat{\mathcal{O}_{X,x}} \cong k[[t_1,\ldots,t_d]]$  where  $d = \dim_x X$ .

Proof. The forward direction follows from the proof of the previous proposition where we deduced this from the fact that X is locally given by equations with independent differentials. For the other direction, assume  $\widehat{O}_{X,x} \cong k[[t_1,\ldots,t_d]]$  then we want to conclude  $d=\dim T_x^*X$ . It suffices to check that  $\dim_x X \geq d$ . Pick  $f_1,\ldots,f_d\in\mathfrak{m}_x$  with linearly independent differentials, and we claim that  $(f_1,\ldots,f_d)$  is a regular sequence, i.e.  $f_{i+1}$  is not a zero divisor in  $\mathcal{O}_{X,x}/(f_1,\ldots,f_i)$ . Then  $f_{i+1}\neq 0$  on each component of  $Z_{f_1,\ldots,f_i}$  passing through x, so we get  $X\supsetneq Z_1\supsetneq Z_2\ldots\supsetneq Z_d\ni x$ , where  $Z_i$  is a component in  $Z_{f_1,\ldots,f_i}$ . Why is it a regular sequence? because  $\mathcal{O}_{X,x}/(f_1,\ldots,f_i)\cong k[[t_1,\ldots,t_{m-i}]]\supseteq \mathcal{O}_{X,x}/(f_1,\ldots,f_i)$  (check by induction).

This concludes the proof of the proposition.

**Proposition 33.** Suppose  $Z \subseteq X$  is a closed subvariety.

- 1. We have an exact sequence  $\mathscr{I}_Z/\mathscr{I}_Z^2=\mathscr{I}_Z|_Z\to\Omega_X|_Z\to\Omega_Z\to0$  (recall  $\mathscr{F}|_Z=\mathscr{O}_Z\otimes_{\mathscr{O}_X}\mathscr{F}=\mathscr{F}/\mathscr{I}_Z\mathscr{F}$  allows us to identify a sheaf  $\mathscr{F}$  on Z with  $i_*\mathscr{F}$ ).
- 2. If for all  $x \in Z$ ,  $\mathscr{I}_Z$  is locally (around x) generated by  $f_1, \ldots, f_m$  such that  $df_i|_x$  are linearly independent at x, then the sequence is short exact, and  $\mathscr{I}_Z/\mathscr{I}_Z^2$  is a locally free sheaf of rank m where m is the codimension.

In the situation of (2),  $\mathscr{I}_Z/\mathscr{I}_Z^2$  is called the *conormal* bundle.

**Example 27.** X, Z are smooth irreducible,  $\dim(Z) = \dim(X) - 1$ , Z = D is a divisor,  $\mathscr{I}_Z = \mathcal{O}(-D)$  is an invertible sheaf. A local section of it is a function vanishing on Z. We can send f to a 1-form df vanishing on D, and it defines a section of the conormal bundle.

**Definition 37.** If X is a smooth irreducible variety of dimension d, then  $\Omega(X)$  is a locally free sheaf of rank d. Then the top exterior power  $\omega(X) = \bigwedge^d \Omega(X)$  is a locally free sheaf of rank 1. We call it the canonical line bundle or the canonical sheaf ("canonical" because any smooth variety gets it for free).

If  $0 \to A \to B \to C \to 0$  is a short exact sequence of locally free sheaves, then we have

$$\bigwedge^{top}(B) = \bigwedge^{top}(C) \otimes \bigwedge^{top}(A).$$

Corollary 24 (Adjunction Formula).  $\omega_D = \omega_X(-D)|_D$ .

One last comment: the graded algebra has a nice geometric property as follows:

**Definition 38.** Spec(gr( $\mathcal{O}_{X,x}$ )) is called the tangent cone to X at x.

**Proposition 34.** The tangent cone is the cone over the exceptional locus in the blowup at x.

## Lecture 20: (Co)tangent Bundles of Grassmannians

Last time we proved that  $X \subseteq \mathbb{A}^n$  is smooth at x if and only if locally given by equations  $f_1, \ldots, f_m$  such that  $df_i|_x$  are linearly independent. We say that  $\mathscr{I}_X$  is locally generated by  $f_1, \ldots, f_m$ . In fact, any  $f_1, \ldots, f_m$  such that  $df_i|_x$  is a basis for  $\ker(T_x^*\mathbb{A}^n \to T_x^*X)$  would work. Take Z generated by the equations  $f_1, \ldots, f_m$ . We checked that  $\dim_x(Z) = \dim_x(X)$ .

**Proposition 35.** The following hold:

- 1. If  $Z \subseteq X$  is a closed subvariety, then we have  $\mathscr{I}_Z/\mathscr{I}_Z^2 \to \Omega_X|_Z \to \Omega_Z \to 0$ .
- 2. If  $\mathscr{I}_Z$  is locally generated by functions with linearly independent differential (that is, for all x in Z, there exists  $U \ni x, f_1, \ldots, f_m$  on U such that  $\mathscr{I}_{Z \cap U} = (f_1, \ldots, f_m), df_i|_y$  is linearly independent for any  $y \in U$ ), then the sequence is exact at left.
- 3. If X is smooth, the last condition can be checked at x. ( $\Omega_X$  is locally linearly independent of  $df_i|_x$  is an open condition.)
- Proof. 1.  $\Omega_X|_Z$  surjects to  $\Omega_Z$  by sending fdg to  $f|_Zdg|_Z$ , and we claim that the kernel is generated by  $fg,g\in\mathscr{I}_Z$ . This would follow from  $\mathrm{Der}(\mathcal{O}_Z,M)=\{\delta\in\mathrm{Der}(\mathcal{O}_X,M)\mid\delta(\mathscr{I}_Z)=0\}$ , so it remains to see that  $f\mapsto df|_Z$  is a well-defined map of  $\mathcal{O}_Z$  mod  $\mathscr{I}_Z/\mathscr{I}_Z^2\to\mathcal{O}_X|_Z$ . Observe that  $f,g\in\mathscr{I}_Z\Longrightarrow d(fg)|_Z=0$ .
  - 2. If  $\mathscr{I}_Z = (f_1, \ldots, f_m)$ , we have the following diagram:

where the diagonal map is guaranteed to be injective on every fiber by condition b), so is injective.

3. We always have it for affine space  $\mathbb{A}^n$ . General case is proved similarly.

**Corollary 25.** X smooth,  $Z \subseteq X$  closed, then Z is smooth if and only if locally Z is given by equation with linearly independent differentials.

*Proof.* Use proposition 3) above. Locally we assume  $X \subseteq \mathbb{A}^n$ , and then X is cut out by some  $g_1, \ldots, g_p$  with linearly independent differentials, so  $(g_1, \ldots, g_p, \tilde{f}_1, \ldots, \tilde{f}_n)$  are equations for Z with linearly independent differentials, so Z is smooth.

Last time we defined  $\omega$ , the canonical bundle. Let K be the corresponding canonical divisor class.

Corollary 26. If X, Z smooth, Z closed in X, then we get a s.e.s. of locally free sheaves  $0 \to \mathscr{I}_Z/\mathscr{I}_Z^2 = T_Z^*X \to \Omega_X|_Z \to \Omega_Z \to 0$ , and thus  $K|_Z = K_Z\omega(\mathscr{I}_Z/\mathscr{I}_Z^2)$ . If Z is a divisor, then  $\omega(\mathscr{I}_Z/\mathscr{I}_Z^2) = \mathscr{I}_Z/\mathscr{I}_Z^2 = \mathscr{O}(-D)|_Z$ , thus  $K_X(D)|_D = K_D$ , which is the adjunction formula.

**Remark 30.** Sections of  $K_X(D)$  are top degree forms on X with poles of order  $\leq 1$  on D. The map  $K_X(D)|_D \to K_D$  sends  $\omega$  to its residue.

**Proposition 36.** We have a s.e.s.  $0 \to \Omega_{\mathbb{P}^n} \to \mathcal{O}(-1)^{\oplus (n+1)} = \mathcal{O}(-1) \otimes V^* \to \mathcal{O} \to 0$  where  $\mathbb{P}V = \mathbb{P}^n$ . As a corollary,  $K_{\mathbb{P}^n} = \mathcal{O}(-(n+1))$ .

More generally, consider the Grassmannian Gr(k,n), consisting of all k-dimensional linear subspaces V of an n-dimensional space W. Then  $\mathcal{O}_{Gr(k,n)}^{\oplus n}$  has a locally free tautological subsheaf V of rank k (that is locally a direct summand) such that a section s of  $\mathcal{O} \otimes W$ , i.e. a map  $s: Gr(k,n) \to W$ , belongs to V if for all  $x, s(x) \subseteq V_x$ .

**Proposition 37.**  $T_{Gr(k,n)} = \text{Hom}(\mathcal{V}, W \otimes \mathcal{O}/\mathcal{V})$  and  $\Omega_{Gr(k,n)} = \text{Hom}(W \otimes \mathcal{O}/\mathcal{V}, \mathcal{V}).$ 

Let's see how this implies the last proposition: let  $k = 1, \mathcal{V} = \mathcal{O}(-1)$ . Then  $\operatorname{Hom}\left(\mathcal{O}(-1), \frac{\mathcal{O}^{\oplus (n+1)}}{\mathcal{O}(-1)}\right) = \frac{\operatorname{Hom}(\mathcal{O}(-1), \mathcal{O}^{\oplus (n+1)})}{\operatorname{Hom}(\mathcal{O}(-1), \mathcal{O}(-1))} = \frac{\mathcal{O}(1)^{\oplus (n+1)}}{\mathcal{O}}$  and  $\Omega = \ker(\mathcal{O}(-1)^{n+1}, \mathcal{O})$ .

Proof of the Second Proposition. For any point V on Gr(k,n), we have an isomorphism  $T_VGr(k,n) \cong Hom(V,W/V)$  by identifying a neighborhood of V with Hom(V,V'). Check this is independent of the choice of V', so let V' = W/V, and glue together these open charts.

Second Proof of the First Proposition. It suffices to construct an s.e.s. of sheaves on  $\mathbb{A}^{n+1} - \{0\}$  that is compatible with the  $G_m$  action. Let  $\pi: \mathbb{A}^{n+1} - \{0\} \to \mathbb{P}^n$ , and consider the s.e.s.  $0 \to \pi^* \Omega_{\mathbb{P}^n} \to \Omega_{\mathbb{A}^{n+1} - \{0\}} \to \mathcal{O} \to 0$ . See [Kem93] for more details.

**Application** Let  $X \subseteq \mathbb{P}^n$  be a smooth hypersutrface of degree d = n + 1, then  $K_X \cong \mathcal{O}_X$  is trivial. (Proof:  $K_X = K_{\mathbb{P}^m}(X)|_X = \mathcal{O}(-(n+1)+d)|_X$ .)

Here are some examples of X:

- 1. n=2, d=3. This gives us the elliptic curves.
- 2. n = 3, d = 4. These are the K3 surfaces.
- 3. n = 2, d = any. We see that the degree of the canonical class is  $\deg(K_X) = \deg(\mathcal{O}(-3+d)|_X) = d(d-3)$ . Recall that complete smooth curves have genus as an invariant, such that  $\deg(K_X) = 2g 2$ , so we have g = d(d-3)/2 + 1.

Now let X be an affine variety, X = Hom(k[X], k). We can write the tangent bundle as  $TX = \coprod_{x \in Y} T_x X =$ 

Hom $(k[X], k[\varepsilon]/\varepsilon^2)$  = Hom $(\operatorname{Spec}(k[\varepsilon]/\varepsilon^2), X)$  where the first object,  $\operatorname{Spec}(k[\varepsilon]/\varepsilon^2)$ , is a scheme rather than a variety. <sup>3</sup> Each such homomorphism  $h: k[X] \to k[\varepsilon]/\varepsilon^2$  is given by  $f \mapsto h_0(f) + \varepsilon h_1(f)$ , where  $h_0: k[X] \to k$  is given by  $h_0(f) = f(x)$  for some x, and  $h_1: f \to k$  is a derivation where the target k is made a k[X]-module by evaluation at x, i.e. if  $h_0(f) = f(x)$  then  $h_1(fg) = f(x)h_1(g) + g(x)h_1(x)$ .

**Proposition 38.** Let E be the exceptional locus over x when blowing up  $X \ni x$ . Then the cone of E is the same as  $\operatorname{Spec}(\bigoplus_{n\geq 0} \mathfrak{m}_x^n/\mathfrak{m}_x^{n+1})_{\operatorname{red}}$ , which we call the tangent cone. If we know that x is a smooth point, then

$$\bigoplus_{n\geq 0} \mathfrak{m}_x^n/\mathfrak{m}_x^{n+1} \text{ is given by } \operatorname{Sym}(T_x^*X).$$

*Proof.* Let  $A = k[x_1, \ldots, x_n]$ , then it surjects to  $\bigoplus_{n \ge 0} \mathfrak{m}_x^n/\mathfrak{m}_x^{n+1} = \operatorname{gr}_x(A)$  (the associated graded ring). So

Cone(E) and Spec( $\operatorname{gr}_x(A)$ ) both sit above  $\mathbb{A}^n$ , so let's compare their associated ideals. We can do it on each of the affine coverings for  $E \subset \mathbb{P}^{n-1}$ , which has coordinates, say,  $(\lambda, t_1, \ldots, t_n)$  (this is for  $\mathbb{A}^n_0$ ) such that the map to  $\mathbb{A}^n$  is generated by  $(\lambda, t_1, \ldots, t_n) \mapsto (\lambda, \lambda t_1, \ldots, \lambda t_n)$ . The ideal of  $E \cap \mathbb{A}^n_0$  is generated by polynomials  $P(\lambda, \lambda t_1, \ldots, \lambda t_n)/\lambda^d$  evaluated at  $\lambda = 0$  (where d is the highest degree of  $\lambda$  divisible by  $P(\lambda, \lambda t_1, \ldots, \lambda t_n)$ ), where  $P \in \mathscr{I}_X$ . We need to compare those with  $\ker(A \to \operatorname{gr}_x(A))$ : invert  $x_1$  and take the degree 0 part, we see the latter is generated by  $\{P_d \mid P = P_d + P_{d+1} + \ldots \in \mathscr{I}_X\}$ .

<sup>&</sup>lt;sup>3</sup>There was a question why  $k[\varepsilon]/\varepsilon^2$  was called the *dual* number; answer: dual refers to the fact that there are *two parts* of each element.

## Lecture 21: Riemann-Hurwitz Formula, Chevalley's Theorem

We begin with a remark on the tangent cone. Let X be a variety and  $x \in X$ .

- We checked that  $Spec((\oplus \mathfrak{m}_x^n/\mathfrak{m}_x^{n+1})_{red})$  is the tangent cone over  $\pi^{-1}(x) \subset \mathbb{P}^n$ , where  $\pi: \hat{X} \to X$  is the blow-up of X at x. If  $X = \operatorname{Spec} A$  we can do this for any ideal in A; indeed, applying it to  $\mathscr{I}_Z$ , where  $Z \subset X$  is a closed subvariety, we get that the "normal cone" to Z is  $\operatorname{Spec}((\oplus \mathscr{I}_Z^n/\mathscr{I}_Z^{n+1})_{red})$ . Using the relative  $\operatorname{Spec}$ , we can generalize this to non-affine case. If X and Z are smooth then we get the total space of the normal bundle.
- X can be degenerated into the normal cone, i.e. there is a morphism of varieties  $\tilde{X} \to \mathbb{A}^1$  which satisfies the following situation:

$$N_X(Z) \longrightarrow \tilde{X} \longleftarrow X \times (\mathbb{A}^1 \setminus \{0\})$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$\{0\} \longrightarrow \mathbb{A}^1 \longleftarrow \mathbb{A}^1 \setminus \{0\}$$

Compare this with the fact that a filtered space can be degenerated into its associated graded ring:

{A locally free coherent sheaf on  $\mathbb{A}^1$  equivariant with respect to  $\mathbb{G}_m$ }  $\leftrightarrow$  {filtered vector spaces}.

To describe the equivalence, let  $\mathcal{E}$  be a locally free coherent sheaf on  $\mathbb{A}^1$  corresponding to a module M over k[t], and V be a filtered vector space. Then the equivalence is given by  $\mathcal{E} \mapsto \mathcal{E}_1 = M/(t-1)M$  with the filteration  $(\mathcal{E}_1)_i = \operatorname{im}(M_i \to M/(t-1)M)$  and  $V = V_j \supset \cdots \supset V_{i+1} \supset V_i = 0$   $(i \ll 0, j \gg 0) \mapsto M$ ,  $M_i = V_{\leq i}$ .

**Theorem 21.1** (Riemann-Hurwitz formula). Let  $f: X \to Y$  be a morphism of smooth irreducible curves. Then k(X)/k(Y) is a separable extension.

Recall from the lecture on September 22th, that for  $x \in X$  we have the ramification index d at x if the divisor  $f^{-1}(f(x))$  has coefficient of the irreducible divisor x equal to d. This is equivalent to saying that in the extension of DVRs  $\mathcal{O}_{x,Y} \subset \mathcal{O}_{x,X}$ ,  $(\operatorname{val}_{\mathcal{O}_{x,Y}})|_{\mathcal{O}_{x,Y}} = d \cdot \operatorname{val}_{\mathcal{O}_{x,Y}}$ .

the extension of DVRs  $\mathcal{O}_{y,Y} \subset \mathcal{O}_{x,X}$ ,  $(\operatorname{val}_{\mathcal{O}_{x,X}})|_{\mathcal{O}_{y,Y}} = d \cdot \operatorname{val}_{\mathcal{O}_{y,Y}}$ . Let  $d_x$  be the ramification index at x. Assume that  $d_x$  is prime to  $\operatorname{char}(k)$ . Then  $f^*K_Y \to K_X$  extends to an isomorphism  $f^*K_Y(R) \simeq K_X$  where  $R = \sum_{x \in X} (d_x - 1)x$ .

Corollary 27. If X, Y are complete then 
$$\deg K_X = n \cdot \deg K_Y + \sum_{x \in X} (d_x - 1)$$
.

Let's consider the example of elliptic curves. Let X be the projective plane curve defined by the equation  $y^2 = x^3 + ax + b$ . Then the projection  $(x:y) \mapsto x$  extends to a map  $X \to \mathbb{P}^1$ , which is ramified at the roots of the polynomial  $P(x) = x^3 + ax + b$  and the point at infinity  $\infty$ , with a unique point over each ramification point. Moreover, from the adjunction formula,  $\deg K_{\mathbb{P}^1} = -2$ . Therefore,  $\deg K_X = 2(-2) + 4 = 0$ . Observe that if  $x \in X$  is a smooth point on a curve and f is a function on X not equal to 0 with f(x) = 0, then  $\frac{df}{f}$  has a pole of order exactly 1 at x, i.e. it is a local generator of  $K_X(x)$  (an exception is when char k = p,  $(f) = n_x(x) + (\text{other points}), p|n_x)$ . If  $f \in \mathfrak{m}_x/\mathfrak{m}_x^2$  then df is a local generator for  $K_X \simeq \Omega_X$ . In general, if  $f = \varphi g^n$  where  $\varphi(x) \neq 0$  and  $g \in \mathfrak{m}_x/\mathfrak{m}_x^2$ , then  $d \cdot \deg f = d \cdot \deg \varphi + dn_x \cdot \deg g$ . Now, take  $f \in \mathfrak{m}_x \subset \mathcal{O}_{x,X}$ . Then  $f^*K_Y \to K_X$  extends to a local isomorphism  $f^*K_Y(y) \simeq K_X(x)$ , where  $f^*K_Y(y) = f^*K_Y \otimes f^*y$  and similarly for  $K_X(x)$ . Therefore,  $f^*K_Y(R) \simeq K_X(\sum_{x \in X} x)$ .

Recall that a smooth irreducible variety is normal, but the converse is true only in dimension 1.

**Proposition 39.** Let X be a normal irreducible affine variety and  $X \subset X$  be a closed subvariety. If  $\dim Z \leq \dim X - 2$  then  $k[X] = k[X \setminus Z]$ . Therefore, for normal varieties, the regular functions extend from the complement of a codimension  $\geq 2$  closed subvariety to the whole space.

Proof. We may assume that X is irreducible. Using induction on dim Z we can reduce to showing that any  $f \in k[X \setminus Z]$  is regular generically on Z, i.e. there exists an open subset  $U \supset X \setminus Z$  such that f is regular on U. Suppose that this is not true for some  $f \in k[X \setminus Z]$ . Then f generates a coherent sheaf  $\mathscr{F} \subset \mathrm{Rat}(X)$  where  $\mathrm{Rat}(X)$  is the sheaf of rational function on X, such that  $\mathscr{F}|_{X\setminus Z} \subset \mathcal{O}$ . Thus  $\mathscr{F}/\mathscr{F} \cap \mathcal{O}$  is coherent, supported on Z, and killed by  $\mathscr{F}_Z^m$ . After modifying the choice of f we can assume that m=1, i.e.  $\mathscr{F}_Z(\mathscr{F}/\mathscr{F} \cap \mathcal{O})=0$ . Thus, for any  $\varphi \in \mathscr{F}_Z$ ,  $\varphi f \in k[X]$ , but for any open subset  $U \supset X \setminus Z$ ,  $f \notin k[U]$ . Now we claim that for any  $\varphi \in \mathscr{F}_Z$ ,  $\varphi f \in \mathscr{F}_Z \subset k[X]$ . Indeed, by the hypersurface theorem,  $\varphi|_D=0$  for some Weil divisor  $D \supset Z$ . Suppose that  $z \in Z$  and  $\varphi f(z) \neq 0$ . Then  $\varphi f \neq 0$  on some neighborhood U of z and, by assumption on f, f is not regular on  $D \cap U$ , a contradiction. Hence,  $\varphi f \in \mathscr{F}_Z$ . By replacing  $\varphi$  with  $\varphi f$ , we obtain that  $\varphi f^2 \in \mathscr{F}_Z$ . Using induction we conclude that  $\varphi f^n \in \mathscr{F}_Z$ . To get a contradiction it is enough to check that  $\{f^n\}$  generates a finite  $\mathcal{O}_X$ -module. But, by the previous argument,  $f^n \in \{\psi | \mathscr{F}_Z \psi \in k[X]\} \subset (\varphi f)^{-1} k[X]$ , the last one being a finite  $\mathcal{O}_X$ -module. Therefore  $\{f^n\}$  generates a finite  $\mathcal{O}_X$ -module, finishing the proof.  $\square$ 

Note that the normality assumption in the above proposition is necessary: Let  $A = \{a_0 + a_2P_2 + a_3P_3 + \cdots \}$ , where  $P_i$  is a homogeneous polynomial in n indeterminates of degree i. Then  $\operatorname{Spec}(A)$  is non-normal with the normalization  $\mathbb{A}^n \to X = \operatorname{Spec}(A)$ , which is bijective and an isomorphism away from zero. However,  $A = k[X] \neq k[X \setminus \{0\}] = k[\mathbb{A}^n \setminus \{0\}]$ .

We say a set is *constructible* if it is a finite union of locally closed subvarieties of Y.

**Theorem 21.2** (Chevalley's theorem). Let  $f: X \to Y$  be a morphism of varieties. Then:

- im(f) is constructible.
- Furthermore, if we assume that X, Y are irreducible and that  $\operatorname{im}(f)$  is dense in Y, then the function on  $\operatorname{im}(f)$  given by  $f(x) \mapsto \dim f^{-1}(f(x))$  (the dimension of the fiber) is upper semi-continuous. In other words, for any d,  $\{f(x)|\dim f^{-1}(f(x))\geq d\}$  is close in  $\operatorname{im}(f)$ .
- Finally, under the previous assumptions, there exist a non-empty open subset U in Y such that  $\dim f^{-1}(y) = \dim X \dim Y$  for all  $y \in U$ .

**Lemma 33.** Let  $f: X \to Y$  be a morphism of irreducible affine varieties with  $\operatorname{im}(f)$  dense in Y. Then there is a nonempty open subset  $U \in Y$  such that  $f^{-1}(U) \to U$  factors as  $f: f^{-1}(U) \xrightarrow{\operatorname{finite,onto}} U \times \mathbb{A}^n \xrightarrow{\pi_1} U$ .

*Proof.* Let  $\mathcal{K}$  be the fraction field of k[Y]. Consider  $k[X] \otimes_{k[Y]} \mathcal{K}$  which is finitely generated over  $\mathcal{K}$  and has no nilpotents. We can apply Noether normalization lemma to find  $f_1, \dots, f_n \in k[X] \otimes \mathcal{K} = A$  such that A is finite over  $k[f_1, \dots, f_n]$ . Let  $\{g_i\}$  be generators of k[X]. The  $\{g_i\}$  must satisfy monic equations over  $k[f_1, \dots, f_n]$ . We can now choose U so that all  $f_i$  and the coefficients of the equations are in k[U].

The lemma implies that if f has a dense image, then im(f) contains a dense affine open subset.

Proof of Chevalley's theorem. The first part of the theorem now follows from the implication of the lemma, and by Noetherian induction. To prove the remaining, we can assume, without loss of generality, that X, Y are both affine. By the lemma, obtain an open subset U in Y such that  $\dim f^{-1}(y) = \dim X - \dim Y$ ,  $\forall y \in U$ . Use the hypersurface theorem and induction on  $\dim Y$  to conclude that the dimension of every nonempty fiber is at least  $\dim X - \dim Y$ . Now, using Noether normalization for Y, obtain a finite surjective morphism  $g: Y \to \mathbb{A}^m$  where  $m = \dim Y$ . Let  $z \in \mathbb{A}^m$  and  $y \in \operatorname{im}(f) \cap g^{-1}(z)$ . Then the fiber  $f^{-1}(y)$  is a union of components of  $(gf)^{-1}(z)$ . By the hypersurface theorem, every such component has dimension  $\geq \dim X - m$ .

#### Lecture 22: Bertini's Theorem, Coherent Sheves on Curves

Let's consider some ways to construct smooth varieties.

**Theorem 22.1** (Bertini's Theorem). Let  $X \subseteq \mathbb{P}V$  be a smooth subvariety. Then for a generic hyperplane  $H, Y = X \cap H$  is again smooth.

Recall that the set of hyperplanes is parametrized by the dual projective space  $\mathbb{P}V^{\vee}$ . To say that a hyperplane is *generic* is equivalent to saying that there is a nonempty open subset  $U \subseteq \mathbb{P}V^{\vee}$  containing the point in  $\mathbb{P}V^{\vee}$  corresponding to that hyperplane and such that each hyperplane in U possesses the desired property.

*Proof.* We can assume that X is irreducible. Indeed, if X has multiple irreducible components (i.e. is not connected) and if we know the claim for each irreducible component, then we have a finite set of open subsets in  $\mathbb{P}V^{\vee}$ , whose intersection is again open and consists of hyperplanes whose intersection with X is smooth.

Let  $d = \dim(X)$ ,  $n = \dim(\mathbb{P}V)$ . For all  $x \in X$ , we have  $T_x X$  of dimension d, and  $T_x X \subseteq T_x \mathbb{P}V$ . If  $x \in H$ , then  $H \cap X$  will be smooth at x if  $T_x H \not\supset T_x X$ . Consider the following subset  $Z \stackrel{\text{def}}{=} \{(H, x) \mid H \ni x, T_x H \supset T_x X\}$  of the product  $\mathbb{P}V^{\vee} \times X$ . One easily sees that is closed. The set of H for which  $H \cap X$  is singular is the image of Z under the projection  $\mathbb{P}V^{\vee} \times X \to \mathbb{P}V^{\vee}$ .

We will now proceed by dimension count. First, we want to calculate the dimension of Z. For this, consider the projection  $Z \to X$ . The two conditions from the definition of Z clearly say that if  $(H,x) \in Z$ , then H contains a subspace W of dimension d isomorphic to  $\mathbb{P}^d$ , so the fiber at each point is  $\{H \in \mathbb{P}V^{\vee} \mid H \supset W\} = \mathbb{P}(V/W)^{\vee}$ . Since  $\dim(V) = n+1$ ,  $\dim(W) = d+1$ , we have the fiber isomorphic to  $\mathbb{P}^{n-d-1}$ . Recall from a theorem last time that a generic fiber has dimension equal to the difference of the dimensions of the two spaces, so  $\dim(Z) = n-1$ .

If we let  $\pi: Z \to \mathbb{P}V^{\vee}$ , then  $\overline{\pi(Z)}$  has dimension at most n-1, so the complement  $\mathbb{P}V^{\vee} \setminus \overline{\pi(Z)}$  is not empty. Moreover, this complement is exactly the desired open subset, and this concludes the proof.

**Corollary 28.** A generic hypersurface of degree d is smooth. Moreover, if  $X \subset \mathbb{P}^n$  is smooth, for a generic hypersurface S of degree d,  $S \cap X$  is smooth.

*Proof.* Use Veronese embedding, consider  $\mathbb{P}^n \subset \mathbb{P}^N$  where  $(t_1, \ldots, t_n) \to (t^I)$  where I ranges over all monomials of degree d. Then a hypersurface becomes a hyperplane in this case, then we reduce to the previous case.

**Remark 31.** Assume that X is irreducible of dimension d. If X is not contained in a hyperplane H, then we know that each component of  $X \cap H$  has dimension d-1. If X is projective, then  $X \cap H$  is nonempty. In fact, one can check that if  $\dim(X) > 1$  and H is a general hyperplane, then  $X \cap H$  is irreducible.

**Remark 32.** Bertini's theorem refers to a range of theorems. For instance, we can allow X to be singular, and one of the variations of Bertini's theorems will say something about the singularities of  $X \cap H$ .

**Remark 33.** We can also relate the topology of X and that of  $X \cap H$  — this is called the Lefschetz Hyperplane Theorem. For instance, the map  $H^i(X,\mathbb{C}) \to H^i(X \cap H,\mathbb{C})$  is an isomorphism up to the middle degree for a general hyperplane H.

**Coherent Sheaves on Curves** Now we start the last main topic — the sheaf cohomology. We will mostly focus on the case of sheaves on curves.

Let  $\mathcal{F}$  be a coherent sheaf on a smooth irreducible curve.

**Definition 39.** The torsion subsheaf  $\mathcal{T} \subseteq \mathcal{F}$  is a subsheaf of  $\mathcal{F}$  generated by torsion sections.

The torsion subsheaf  $\mathcal{T}$  has finite support (by Noetherian property and due to the dimension equal to one), and  $\mathcal{F}/\mathcal{T}$  is a torsion free sheaf. But we know that a finitely-generated torsion free module over a DVR is free, so a torsion free sheaf is locally free. Moreover,  $0 \to \mathcal{T} \to \mathcal{F} \to \mathcal{F}/\mathcal{T} \to 0$  splits noncanonically by constructing a surjection  $\mathcal{F} \to \mathcal{T}$ ; this follows from the corresponding result about modules over DVRs. It follows that a coherent sheaf  $\mathcal{F}$  on a curve can be decomposed into a direct sum  $\mathcal{T} \oplus \mathcal{F}'$ , where the first summand is a torsion sheaf and the second one is torsion-free.

Every torsion sheaf  $\mathcal{T}$  has finite length. If its support is irreducible, then it is just a point, so in this case  $\mathcal{T} \cong \mathcal{O}_x$  for some x. Actually, a torsion sheaf has a filtration with gr  $T = \bigoplus \mathcal{O}_{x_i}$ . In fact, this result is true for a torsion sheaf on any variety X if the sheaf has finite support.

Now let  $\mathcal{E}$  be a locally free sheaf, and  $\mathcal{E}' \subset \mathcal{E}$  be a subsheaf. Of course, if  $\mathcal{E}$  is torsion-free, then so is  $\mathcal{E}'$ . However, this is not the case for  $\mathcal{E}/\mathcal{E}'$ . Consider the following example where we have torsion in the quotient:

$$0 \to \mathcal{O}(-x) \to \mathcal{O} \to \mathcal{O}_x \to 0.$$

Another example is when we can take  $X = \operatorname{Spec}(k[t])$ , and consider  $\mathcal{O} \xrightarrow{t} \mathcal{O}$ .

Locally we have  $\mathcal{E} = \mathcal{O}^{\oplus r}, \mathcal{E}' = \mathcal{O}^{\oplus r'}$ , then  $\mathcal{E}' \to \mathcal{E}$  can be given by a  $r' \cdot r$  matrix with entries in  $\mathcal{O}$ .

**Exercise 6.** Using Nakayama lemma, show that the quotient has torsion at x if and only if evaluating matrix coefficients at x gives us a matrix of rank less than r'.

We want to call a subbundle such a locally free sheaf that taking quotient with respect to it gives a locally free sheaf.

**Example 28.** For example, if r' = 1, this just means sections can vanish at that point. Consider  $\mathcal{O} \to \mathcal{O}^{\oplus r}$ , given by  $(f_1, \ldots, f_r)$ , then cokernel has torsion at x iff  $f_i(x) = 0$  for all i. Recall that  $f_i \in \mathcal{O}_{x,X}$ , and this holds if the valuation of each  $f_i$  is greater than 0. If d is the minimum of these valuations, and t is some element of  $\mathcal{O}_{x,X}$  with valuation 1 (i.e.  $t \in \mathfrak{m}_x - \mathfrak{m}_x^2$ ), then we have  $\mathcal{O} \xrightarrow{f_i/t^d} \mathcal{O}^r$  which is the same as the map above. The second map has no cotorsion (i.e. torsion in the cokernel), and the image is independent of the choices.

In general, for  $\mathcal{E}' \subset \mathcal{E}$ , there exists unique  $\mathcal{E}''$ , such that  $\mathcal{E}' \hookrightarrow \mathcal{E}'' \hookrightarrow \mathcal{E}$  where the second map has no cotorsion, and the rank of  $\mathcal{E}''$  is the same as rank of  $\mathcal{E}'$  i.e.  $\mathcal{E}''/\mathcal{E}'$  is torsion. To construct such a sheaf  $\mathcal{E}''$ , we first take the torsion subsheaf  $\mathcal{T} \subset \mathcal{E}/\mathcal{E}'$  and then consider its preimage with respect to the surjection  $\mathcal{E} \to \mathcal{E}/\mathcal{E}'$ . The latter will be the desired  $\mathcal{E}''$ , as one can easily verify.

**Definition 40.** We call  $\mathcal{E}''$  the saturation of  $\mathcal{E}'$  in  $\mathcal{E}$ .

#### Basic invariants of a coherent sheaf: rank and degree

**Definition 41.** Let  $\mathcal{F}$  be a coherent sheaf. The rank of  $\mathcal{F}$  is defined as the rank of the locally free sheaf  $(\mathcal{F}/\text{torsion})$  when we work over smooth varieties. More generically (for any irreducible variety), one defines rank as follows. For a field  $K \stackrel{\text{def}}{=} \varinjlim_{U} k[U]$ , we have the following K-vector space:  $V_{\mathcal{F}} \stackrel{\text{def}}{=} \varinjlim_{U} \mathcal{F}[U]$ . The rank is the dimension  $\text{rk}(\mathcal{F}) \stackrel{\text{def}}{=} \dim_{K}(V_{\mathcal{F}})$ .

One can show that rank is equal to the dimension of a generic fiber of  $\mathcal{F}$ .

It is clear from the definition that rank is additive in short exact sequences.

**Definition 42.**  $K^0(A)$ , the Grothendieck group of an abelian category A, is the free abelian group generated by isomorphism classes in A modulo the relation that, given  $0 \to A \to B \to C \to 0$ , we have [B] = [A] + [C].

This is the universal object for invariants that are additive in short exact sequences. Thus for instance rank is a homomorphism  $K^0(\text{Coh}(X)) \to \mathbb{Z}$ . Note that  $K^0(\text{Coh}(X))$  can be explicitly described for X of dimension one.

Assume now that X is complete. Define another homomorphism  $\delta: K^0(\operatorname{Coh}(X)) \to \mathbb{Z}$  such that  $\delta([\mathcal{E}]) \mapsto \deg(\det(\mathcal{E}))$  where  $\mathcal{E}$  is locally free. Additivity comes from multiplicativity of the determinant in short exact sequences. For torsion sheaves, we set  $\delta$  to be the length of  $\mathcal{T}$ , which is the same as the dimension

of  $\Gamma(\mathcal{T})$ . (Recall that the length  $\ell$  is defined as the number of summands in gr  $\mathcal{T} = \bigoplus_{i=1}^{r} \mathcal{O}_{x_i}$ .)

This would make sense. Consider the short exact sequence  $0 \to \mathcal{O} \to \mathcal{O}(D) \to \mathcal{O}_D \to 0$ . The first sheaf has degree 0, the second second one has degree deg(D), whereas the leftmost has length deg(D). But we still need a formal check.

**Proposition 40.**  $\delta$  is a well-defined homomorphism.

**Lemma 34.** If we have a short exact sequence  $0 \to \mathcal{E} \to \mathcal{E}' \to \mathcal{T} \to 0$ , where  $\mathcal{T}$  is torsion and the other two sheaves are torsion free, then  $\deg(\mathcal{E}') = \deg(\mathcal{E}) + \ell(\mathcal{T})$ .

*Proof.* Induction on  $\ell(\mathcal{T})$ , reduce to  $\mathcal{T} = \mathcal{O}_x$ , and  $r = \operatorname{rank}(\mathcal{E}) = \operatorname{rank}(\mathcal{E}')$ . We claim that  $\Lambda^r(\mathcal{E}) \to \Lambda^r(\mathcal{E}')$ 

has a zero of order 1 at 
$$x$$
. Locally it looks like  $\begin{pmatrix} 1 & 0 & \dots & 0 \\ 0 & 1 & \dots & 0 \\ 0 & 0 & \dots & t \end{pmatrix}$  where  $t \in \mathfrak{m} - \mathfrak{m}^2$ .

Proof of the Proposition. We have  $\delta(\mathcal{E} \oplus \mathcal{T}) = \deg(\det(\mathcal{E})) + \ell(\mathcal{T})$ . Need to check that for  $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$ , we have the additive property. First consider  $0 \to \mathcal{T}' \to \mathcal{T} \to \mathcal{T}/\mathcal{T}' \subseteq \mathcal{T}'' \to 0$ , then we have  $\delta(\mathcal{T}) = \delta(\mathcal{T}') + \delta(\mathcal{T}/\mathcal{T}')$  also  $\delta(\mathcal{F}) = \delta(\mathcal{F}/\mathcal{T}) + \delta(\mathcal{T})$  and same for  $\mathcal{F}', \mathcal{F}''$ , so we reduce to the case where  $\mathcal{F} = \mathcal{E}$  is torsion free. If  $\mathcal{F}'_s$  is the saturation of  $\mathcal{F}'$ , then  $\delta(\mathcal{F}'_s) = \delta(\mathcal{F}') + \delta(\text{torsionof }\mathcal{F}'')$ , so replacing  $\mathcal{F}'$  by  $\mathcal{F}'_s$  doesn't check the RHS of  $\delta(\mathcal{F}) + \delta(\mathcal{F}') + \delta(\mathcal{F}'')$ , so we can check all three of them to locally free, which we have already discussed above.

**Remark 34.** The homomorphism  $\delta$  can be refined to a homomorphism  $K^0(\operatorname{Coh}(X)) \to \operatorname{Pic}(X)$  followed by the degree map  $\operatorname{Pic}(X) \to \mathbb{Z}$ .

Cohomology of quasicoherent sheaves Cohomology is an important invariant of quasicoherent sheaves. To cut a long story short, cohomology of a sheaf is the derived functor of the global sections. Some theory can be found in Grothendieck's Tohoku paper, which is worth reading. A derived functor accounts for the nonexactness of the initial functor between abelian categories.

**Definition 43.** Let  $F: A \to B$  be a left exact functor between abelian categories. A  $\delta$ -functor is a collection of functors  $F^i: A \to B$  such that for every short exact sequence  $0 \to A \to B \to C \to 0$  we have a long exact sequence  $0 \to F(A) \to F(B) \to F(C) \to F^1(A) \to F^1(B) \to F^1(C) \to F^2(A) \to \dots$  that is functorial in short exact sequences.

**Definition 44.** A  $\delta$ -functor is universal if it has a canonical morphism from any  $\delta$ -functor. In other words, it is the terminal object in the category of  $\delta$ -functors.

**Definition 45.** The universal  $\delta$ -functor is called the derived functor, and is of course unique if exists. We denote it by  $\mathcal{R}^i F$ .

In our case,  $\mathcal{A} = \mathrm{QCoh}(X)$ ,  $\mathcal{B} = \mathbf{Vect}$ ,  $F = \Gamma$ .

Next class we'll show the existence along with some properties, including Serre duality for curves.

## Lecture 23: Derived Functors, Existence of Sheaf Cohomology

**Prelude:** the cousin problem How do we integrate a rational function  $\frac{P(x)}{Q(x)}$ ? We decompose it into a sum  $\sum \frac{a_i}{(x-b_i)^{d_i}}$  + polynomial. Conversely, given a complete curve X, and a locally free sheaf  $\mathcal{E}$ , one may want to understand if  $\mathcal{E}$  has a section with singularities at some fixed  $x_1, \ldots, x_n$  with fixed prescribed singular terms of  $x_1, \ldots, x_n$ . To be more specific,  $\sigma \in \Gamma(\mathcal{E}|_{X = \{x_1, \ldots, x_n\}}) = \Gamma(j_* j^* \mathcal{E})$  where  $j : X = \{x_1, \ldots, x_n\} \to X$ , and by singular term we mean a section of  $j_*j^*\mathcal{E}/\mathcal{E}$ , which is a quasicoherent sheaf supported at  $x_1,\ldots,x_n$ . Or one can write  $\sigma \in \Gamma(\mathcal{E}(D))$  where  $D = \sum d_i x_i$ , and the singular term is given by a section of  $\mathcal{E}(D)/\mathcal{E}$ .

This problem can be solved using cohomology. For instance, let  $\mathcal{E} = K_X$  be the canonical class, X being smooth irreducible. For instance, let  $X = \mathbb{P}^1$ , and  $x_1 = 0, x_2 = \infty$ . Consider the form that takes the shape  $\frac{dz}{z}$  + (regular at 0), and  $2\frac{dt}{t}$  + (regular at  $\infty$ ). Can such form exist? No. This follows from Stoke's theorem, which basically says  $\sum \operatorname{res}_x \omega = 0$ . However, in fact for  $\mathcal{E} = K_X$  this is the only obstruction: this follows from the fact that  $H^1(K_X)$  is one-dimensional.

Back to the main topic Last time we talked about universal  $\delta$ -functors  $\mathcal{R}^i\mathcal{F}$  for a given functor between abelian categories.

**Proposition 41** (Grothendieck). A  $\delta$ -functor ( $\mathcal{F}^i$ ) for given  $\mathcal{F}$  is universal provided that  $\mathcal{F}^i$  for i > 0 is effaceable: for any  $M \in A$  and any  $m \in F^iM$ , there exists some monomorphism  $\varphi: M \to N$ , such that  $\mathcal{F}^{\imath}(\varphi)(m) = 0.$ 

In practice, we often check the stronger condition that  $\exists \varphi : M \hookrightarrow N$ , such that  $\mathcal{F}^i(\varphi) = 0$ . Or even stronger one: there exists N such that  $\mathcal{F}^i(N) = 0$ .

Let X be a separated algebraic variety. Fix an affine open cover  $X = U_1 \cup \ldots \cup U_n$ . Recall that we have  $0 \to \Gamma(F) \to \bigoplus_{i} \Gamma(F|_{U_i}) \to \bigoplus_{i,j} \Gamma(F|_{U_i \cap U_j}).$  This can be extended to a Čech complex  $\check{C}(F)$  of the covering:  $0 \to \bigoplus_{i} \Gamma(F|_{U_i}) \to \ldots \to \bigoplus_{i \in C} \Gamma(F|_{U_{i_1} \cap \ldots \cap U_{i_k}}) \to \ldots$ 

$$0 \to \bigoplus_{i} \Gamma(F|_{U_i}) \to \dots \to \bigoplus_{i_1 < \dots < i_k} \Gamma(F|_{U_{i_1} \cap \dots \cap U_{i_k}}) \to \dots$$

with the obvious map having the necessary sign change. One can easily check this is a complex and thus defines a functor  $\mathbf{QCoh}(X) \to \mathbf{Complexes}$ , which is exact by exactness of  $\Gamma$  on  $\mathbf{QCoh}(X)$ .

**Proposition 42** (Snake Lemma). A short exact sequence of complexes yields a long exact sequence of cohomology (see Wikipedia for the exact statement).

We also mentioned that  $H^0(\check{C}(\mathscr{F})) = \Gamma(X,\mathscr{F})$ . Now we claim that  $\mathscr{F} \mapsto H^i(\check{C}(\mathscr{F}))$  is an universal  $\delta$ -functor. Let's show it's effeceable. Let  $j_i:U_i\to X$ . Consider the embedding  $\mathscr{F}\hookrightarrow\bigoplus j_i^*j_{i_*}\mathscr{F}$ , where

we denote the latter object by  $\mathscr{G}$ . Claim:  $H^i(\check{C}(\mathscr{G})) = 0$  for i > 0 (reads:  $\check{C}(\mathscr{G})$  is acyclic). Note that  $\Gamma_{i_1,...,i_k}(\mathscr{G}) \xrightarrow{\sim} \Gamma_{i_1,...,i_k,n}(\mathscr{G})$  when  $i_k \neq n$ . So  $\check{C}(\mathscr{F})$  contains a subcomplex  $\check{C}' = \bigoplus \Gamma_{i_1,...,i_k|i_k=n}$ , and we have a quotient complex  $\check{C}''$  given by  $\bigoplus \Gamma_{i_1,...,i_k|i_k < n}$ . Then we have a s.e.s.  $\check{C}'(\mathscr{G}) \to \check{C}(\mathscr{G}) \to \check{C}''(\mathscr{G})$ , to which if you apply Snake lemma, then the connecting homomorphism will be an iso, thus yielding that the central one is acyclic. (This follows from the observation that  $\check{C}(\mathscr{G}) = \operatorname{Cone}(\check{C}'' \to \check{C}'[1])$ .) Thus  $\mathcal{R}^i\Gamma(\mathscr{F})=\mathrm{H}^i(C(\mathscr{F}))$  for any quasicoherent sheaf F.

Remark 35. More generally, we can use a similar construction with the Čech complex that is the direct limit over all coverings. A theorem of Grothendieck's states that if X is paracompact, then this computes the cohomology for any sheaf F.

**Example 29.** Let X be an algebraic variety. Let  $\mathscr{F} = \mathcal{O}^*$  be the sheaf of invertible regular functions. Let's consider  $H^1(\mathcal{O}^*)$ . First fix an covering  $X = \bigcup U_i$ . Then consider the set  $f_{ij} \in k[U_i \cap U_j]^*$  such that on  $U_i \cap U_j \cap U_k$ ,  $f_{ij}f_{jk} = f_{ik}$ , modulo  $f_{ij} = \varphi_i \varphi_j^{-1}$ ,  $\varphi_i \in k[U_i]^*$ . This defines an invertible sheaf on X. Modulo proof, we know that  $H^1(X, \mathcal{O}^*) \cong \operatorname{Pic}(X)$ .

**Remark 36.** For any  $\mathscr{F}$  and any covering  $U_i$ , there exists a canonical map  $H^i(\check{C}(\mathscr{F})) \to H^i(\mathscr{F})$ .

Remark 37. We have the following:

- 1. For  $\mathscr{F}$  quasicoherent,  $\mathcal{R}^i\Gamma_{Sh(X)}(\mathscr{F}) = \mathcal{R}^i\Gamma_{\mathcal{O}-Mod(X)}(\mathscr{F}) = \mathcal{R}^i\Gamma_{QCoh(X)}(\mathscr{F}).$
- 2. Other relevant derived functors: we have a parallel definition for right exact functors, which then yields  $\mathcal{L}^{-i}(\mathcal{F}) = \mathcal{L}_i(\mathcal{F})$  (two different notations) that goes as follows:

$$\ldots \to \mathcal{L}^{-1}(C) \to \mathcal{F}(A) \to \mathcal{F}(B) \to \mathcal{F}(C) \to 0$$

the case relevant to us is tensor product of modules. For commutative ring A, and a fixed module M, let  $\mathcal{F}(N) = M \otimes_A N$ , then  $\mathcal{L}^{-i}\mathcal{F}(N) = \operatorname{Tor}_i^A(M,N)$ . Another functor:  $f: X \to Y$ , then  $f^*: \mathbf{QCoh}(Y) \to \mathbf{QCoh}(X)$ . The dual example: fix some  $M \in A$  (say  $A = \mathbf{QCoh}(X)$ ), and let  $\mathcal{F}(N) = \operatorname{Hom}(M,N)$ , then  $\mathcal{R}^i\mathcal{F} = \operatorname{Ext}^i(M,N)$ . For instance for  $\mathcal{O}$  the structure sheaf, we have  $\operatorname{Ext}^i(\mathcal{O},\mathcal{F}) = \operatorname{H}^i(\mathcal{F})$ .

3. From a homological point of view, all of  $\mathcal{R}^i\mathcal{F}$  can be combined into a functor between derived categories, and is usually called the derived functor.

In general, the procedure to compute  $\mathcal{R}^i(\mathcal{F})$  (and  $\mathcal{L}^{-i}(\mathcal{F})$  likewise) is to use resolutions. Given  $M \in A$ , take its resolution  $C = (0 \to M^0 = M \to M^1 \to \ldots)$ , where  $H^i(M) = 0$  for i > 0, and  $H^0(C) = M$ . Given a resolution C, then  $\mathcal{F}(C)$  is a complex in B, and then we can compute its cohomology there.

**Proposition 43.** There is always a canonical map  $H^i(\mathcal{F}(C)) \to \mathcal{R}^i \mathcal{F}(M)$ ; moreover, it is an isomorphism if  $M^i$  are adjusted to  $\mathcal{F}$ . (An object M is called adjusted to  $\mathcal{F}$  if  $\mathcal{R}^i \mathcal{F}(M) = 0$ . Of course, for left exact functors we use left resolutions.)

An injective object is adjusted to any left exact functor. If we have enough injectives (i.e. for any M there is a monomorphism  $M \hookrightarrow I$  into some injective object I), then any left exact functor has derived functors. Similarly we have the concept of projective objects and projective resolution. (Recall from homework that  $\mathbf{QCoh}(X)$  doesn't have enough projectives, but it does have enough injectives.) One more concept: Flabby (flasque) sheaves are adjusted to  $\Gamma$ ; by flabby we mean that for any  $U \supset V, \Gamma(U, \mathcal{F}) \to \Gamma(V, \mathcal{F})$  is onto.

Recall that  $\Gamma(X,\mathscr{F}) = \pi_*(\mathscr{F})$  where  $\pi: X \to \operatorname{pt.}$  Also recall that  $f_*$  is left exact for any  $f: X \to Y$  of algebraic varieties, so we can also consider  $\mathcal{R}^i f_*$ . Recall also that  $f_*$  is exact if f is an affine morphism. In general (say X is separated) we can write  $X = \bigcup U_i$  such that  $f|_{U_i}$  is affine (e.g.  $U_i$  are affine), then compute  $\mathcal{R}^i f_i \mathscr{F}$  using the Čech complex.

**Proposition 44.** If f is affine,  $\mathscr{F}$  is quasicoherent, then  $H^i f_* \mathscr{F} = H^i(\mathscr{F})$ .

*Proof.* For separated Y, the Čech complexes agree if we use an affine covering of Y and cover X with their preimages under f. In general, can take limit over all affine coverings.

Let X be a curve, consider  $\mathscr{F} \to j_*j^*\mathscr{F} \to j_*j^*\mathscr{F}/\mathscr{F} \to 0$  for  $j: U \hookrightarrow X$  of an affine set U, then we claim this is an adjusted resolution of  $\mathscr{F}$  to  $\Gamma$ . (This links back to the beginning of the lecture.)

## Lecture 24: Birkhoff-Grothendieck, Riemann-Roch, Serre Duality

**Homework Related Stuff** Remark on the 10th homework: we do have counterexamples to 5(b) if the characteristic is not 0. Consider the Drinfeld curve a.k.a. the Deligne-Lusztig variety of dimension 1, given by  $x^py - y^px - z^{p+1} = 0$  in  $\mathbb{F}_p$ .  $SL_2(\mathbb{F}_p)$  acts on X, (a, b, c, d) acts by sending (x, y) to (ax + b, cx + d) is an isomorphism of this curve. Also, in 2b) one doesn't need the finiteness condition.

**Back to Cohomology** Recall that  $H^*(X, \mathscr{F})$  can be computed using 1) Čech cohomology for a fixed affine covering, or 2) adjusted e.g. flabby resolution.

**Remark 38.** 1) is a particular case of 2). In particular, let  $j: U \to X$  be an open embedding of U affine in X separated, then  $j_*$  is adjusted to  $\Gamma$ . Proof: j is an affine map, so  $H^i(j_*\mathscr{F}) = H^i(\mathscr{F}) = 0$  for i > 0.

If  $X = U_1 \cup \ldots \cup U_n$ , then as an example,  $\bigoplus j_{i*}j_i^*\mathscr{F} \to \bigoplus j_{i_1,i_2*}j_{i_1,i_2}^*\mathscr{F} \to \ldots$  is an resolution. Another example: suppose X is an irreducible curve,  $X \supset Y$ , and Y is an affine open, say  $X - \{x_1, \ldots, x_n\}$ . If  $\mathscr{F}$  has sections supported on  $x_i$ , then we have an s.e.s.  $0 \to \mathscr{F} \to j_*j^*\mathscr{F} \to j_*j^*\mathscr{F}/\mathscr{F} \to 0$ . Last term is flabby, since it's supported on a finite set.

**Example 30.** Let's compute  $H^i(\mathcal{O}_{\mathbb{P}^1}(n))$  using the 2-term complex

$$0 \to \Gamma(\mathcal{O}_{\mathbb{P}^1}(n)) = k[X] \to \Gamma(\mathcal{O}_{\mathbb{P}^1}(n)|_{\mathbb{A}^1})/\mathcal{O}_{\mathbb{P}^1}(n)) \to 0$$

Using affine charts, one can compute the second term to be  $\frac{k[x,x^{-1}]}{x^nk[x^{-1}]}$ . The map is onto for  $n \geq 0$ , and the kernel consists polynomials of degree  $\leq n$ . Thus for  $n \geq 0$ , dimension of  $H^0(\mathcal{O}(n)) = n+1$ , and  $H^1(\mathcal{O}(n)) = 0$ . For the negative cases, do inverse induction using  $0 \to \mathcal{O}(n-1) \to \mathcal{O}(n) \to \mathcal{O} \to 0$  or run the same argument again. In particular, when n < 0,  $H^0$  is 0, and  $H^1$  has dimension -n-1. So  $H^0(\mathcal{O}(-1)) = H^1(\mathcal{O}(-1)) = 0$ .

This yields a classification of locally free sheaves on  $\mathbb{P}^1$ :

**Theorem 24.1** (Grothendieck-Birkhoff). A locally free coherent sheaf of rank n on  $\mathbb{P}^1$  is isomorphic to  $\bigoplus_{i=1}^n \mathcal{O}_{\mathbb{P}^1}(d_i)$  for a unique collection  $d_i$ .

*Proof.* Uniqueness is left as an exercise; one way is to recover  $d_i$  from dimensions of  $H^i(\mathcal{E}(d))$  for  $i = 0, 1, d \in \mathbb{Z}$ . Now let's prove existence. We use induction on rank.

Claim:  $H^0(\mathcal{E}(d)) \neq 0$  for  $d \gg 0$ , and = 0 for  $d \ll 0$ . Proof:  $\mathcal{E}$  is a quotient, i.e.  $\mathcal{O}(-m)^N \twoheadrightarrow \mathcal{E}$ ,  $\mathcal{O}(-m')^{N'} \twoheadrightarrow \mathcal{E}^{\vee} \implies \mathcal{E} \subset \mathcal{O}(m')^{N'}$  and so  $H^0(\mathcal{E}(-d)) = 0$  for d > m'. For d > m,  $\mathcal{O}(d-m)^N \twoheadrightarrow \mathcal{E}(d)$ , and the first is generated by global sections. Pick d such that  $\Gamma(\mathcal{E}(d)) \neq 0$  but = 0 for d' < d, and replace  $\mathcal{E}$  with  $\mathcal{E}(d)$ , then we can assume  $\Gamma(\mathcal{E}) = 0$  and  $\Gamma(\mathcal{E}(d)) = 0$  for d < 0.

Pick some  $\sigma: \mathcal{O} \to \mathcal{E}$ , claim:  $\mathcal{E}/\operatorname{im}(\sigma)$  has no torsion. Proof: otherwise  $\mathcal{O}(D) \hookrightarrow \mathcal{E}$  for some effective divisor D, then  $\Gamma(\mathcal{E}(-D)) = \Gamma(\mathcal{E}(-d)) \neq 0$  for  $d = \deg(D)$ , contradiction. So we have  $0 \to \mathcal{O} \to \mathcal{E} \to \mathcal{E}' \to 0$ , where the third is locally free. By induction,  $\mathcal{E}' = \bigoplus \mathcal{O}(d_i)$ .

Claim:  $d_i \leq 0$ . Proof: otherwise we can write  $0 \to \mathcal{O}(-1) \to \mathcal{E}(-1) \to \mathcal{E}'(-1) \to 0$ .  $H^1(\mathcal{O}(-1)) = 0 \implies H^0(\mathcal{E}(-1)) \twoheadrightarrow H^0(\mathcal{E}'(-1))$ . Suppose for some  $d \geq 0$ , we can write  $\mathcal{E}' = \mathcal{O}(d) \oplus \ldots$ , then we have  $\mathcal{E}'(-1) = \mathcal{O}(d-1) \oplus \ldots$ , hence  $H^0(\mathcal{E}'(-1)) \neq 0 \implies H^0(\mathcal{E}(-1)) \neq 0$ , contradiction.

It remains to check that the s.e.s.  $0 \to \mathcal{C} \to \mathcal{E}' \to 0$  splits. Easier to check that the dual sequence  $0 \to \mathcal{E}'^{\vee} \to \mathcal{E}^{\vee} \to \mathcal{O} \to 0$  splits. To see this, it's enough to see that  $\Gamma(\mathcal{E}^{\vee}) \to \Gamma(\mathcal{O})$  is onto. First one is  $\text{Hom}(\mathcal{O}, \mathcal{E}^{\vee})$ , second being k. But  ${\mathcal{E}'}^{\vee}$  is the sum of all  $\mathcal{O}(d_i)$  where  $d_i \geq 0$ , so  $H^1(\mathcal{E}'^{\vee}) = 0$ , and this is the obstruction to the surjectivity using the l.e.s.

Or we can invoke a little homological algebra and just say the following:  $\operatorname{Ext}^1(A, B)$  parametrizes the isomorphism classes of extensions  $0 \to B \to C \to A \to 0$ . Note that  $\operatorname{Ext}^1(\mathcal{E}', 0) = H^1(\mathcal{E}') = 0$ .

Here are some general facts, probably to be covered in 18.726:

- 1.  $H^i(X, \mathscr{F}) = 0$  for  $i > \dim(X)$ , where  $\mathscr{F}$  is an quasicoherent sheaf.
- 2. If X is complete and  $\mathscr{F}$  coherent, then  $H^i(X,\mathscr{F})$  is finite-dimensional.

The proof of these statements are beyond the scope of this course, but at least we can prove them for X of dimension 1.

*Proof.* We can first reduce to the case of X a smooth (eqv. normal) curve. Let  $q: Y \to X$  be the normalization of X, and  $\mathscr{F}$  a coherent sheaf on X. Consider  $\varphi: \mathscr{F} \to q_*q^*\mathscr{F}$ : the kernel and cokernel of this map are supported at singular points of X, and thus are torsion sheaves. Coherent torsion sheaves are extensions of copies of skyscraper sheaves supported at the singular points, so they have finite dimensional  $H^0$  and higher cohomology groups vanish, so by the cohomology les it suffices to prove the corresponding statements for  $q_*q^*\mathscr{F}$ . Since q is an affine map,  $H^i(X, q_*q^*\mathscr{F}) = H^i(q^*X, q^*\mathscr{F})$ , so we reduce to the smooth case.

Now a smooth curve X admits an affine map f to the projective line  $\mathbb{P}^1$ , which is defined by any nonconstant element of the field of rational functions when X is connected, and is finite when X is complete. We have that  $H^*(X, \mathscr{F}) = H^*(\mathbb{P}^1, f_*\mathscr{F})$ , so we further reduce to proving the following statements for any quasicoherent sheaf  $\mathscr{F}$  on  $\mathbb{P}^1$ :

- 1.  $H^{i}(\mathbb{P}^{1}, \mathscr{F}) = 0 \text{ for } i > 1;$
- 2. If  $\mathscr{F}$  is coherent, then  $H^0$  and  $H^1$  are finite dimensional.

The first statement is clear from the Cech cohomology computation, where we use the standard 2-piece affine covering. For the second one, write  $\mathscr{F}$  as a sum of a locally free sheaf and a torsion sheaf. A coherent torsion sheaf on curve clearly has  $H^0$  finite dimensional and  $H^1$  vanishing, and the case for locally free sheaf follows from Grothendieck-Birkhoff.

**Euler Characteristic** Define the *Euler characteristic*  $\chi: K^0(\mathbf{Coh}(X)) \to \mathbb{Z}$  for X a complete algebraic variety. One can compute that  $\chi([\mathscr{F}]) = \sum_i (-1)^i \dim H^i(\mathscr{F})$ , and the l.e.s. of cohomology shows that  $\chi$  is additive on short exact sequences.

**Theorem 24.2** (Riemann-Roch for Curves). Let X be irreducible complete (or smooth, for convenience's sake) curve. Then  $\chi(\mathscr{F}) = \deg(\mathscr{F}) - \operatorname{rank}(\mathscr{F})(g_a - 1)$  where  $g_a = \dim H^1(\mathcal{O})$ .

 $g_a$  is the arithmetic genus, which equals the geometric genus for nonsingular curves.

*Proof.* Enough to check on generators of  $K^0(\mathbf{Coh}(X))$ .

**Lemma 35.**  $\mathcal{O}(X)$  along with  $\mathcal{O}_x$  generate the group.

To see it implies the theorem: if  $\mathscr{F} = \mathcal{O}_x$ , lhs = 1 = rhs. if  $\mathcal{O}_X$ , lhs = 1 -  $g_a$  = rhs. Proof of the lemma: recall that if  $\mathscr{F}$  is torsion then it is some  $\bigoplus \mathcal{O}_{x_i}$ . Now we do induction on rank: if  $\mathscr{F}$  has rank i and torsion-free, find some  $\mathscr{F}|_U = X \setminus \{x_1, \dots, x_n\}$  that has a section  $\sigma : \mathcal{O} \to \mathscr{F}$ . Then it extends to  $\mathcal{O}(-D) \hookrightarrow \mathscr{F}$  for  $D = \sum d_i x_i$  for some  $d_i > 0$ , then we're done because  $\mathscr{F}/\mathcal{O}(-D)$  has smaller rank, and  $\mathcal{O}(-D) \equiv [\mathcal{O}] - \sum_i d_i [\mathcal{O}_{x_i}]$ .

**Theorem 24.3** (Serre Duality). If  $\mathcal{E}$  is a locally free sheaf on a complete smooth (this time essential) irreducible curve, then we have a canonical isomorphism  $\Gamma(\mathcal{E})^* \cong H^1(\mathcal{E}^{\vee} \otimes K_X)$ .

Noting that  $H^1(K_X) \cong k$ , and we said there's a map  $H^i(\mathscr{F}) \otimes H^j(\mathscr{G}) \to H^{i+j}(\mathscr{F} \otimes \mathscr{G})$ , so the pairing comes from  $\mathscr{E} \otimes (\mathscr{E}^{\vee} \otimes K) \to K$ . The proof we shall present below is based on Tate's paper [Tat68].

Proof. Recall that for  $x \in X$ ,  $\widehat{\mathcal{O}_{x,X}} \cong k[[t]]$ , and the residue field is just k((t)), the Laurent power series. So  $\widehat{\mathcal{O}_{x,X}}$  is a complete topological vector space (with Tychonoff topology), and the residue field is a linear topological vector space. Also recall an elementary duality that generalizes the usual linear duality of vector spaces, as a functor from discrete spaces to complete vector spaces, given by  $V \mapsto \operatorname{Hom}(V,k)$ , and the other way by  $W \mapsto \operatorname{Hom}_{\mathbf{Cont}}(W,k)$ . In particular,  $k((t))^{\vee} \cong k((t))$  (the topological dual), and  $k[[t]]^{\vee} \cong t^{-1}k[t^{-1}] \Longrightarrow t^{-1}k[t^{-1}]^{\vee} \cong k[[t]]$  (notice this is non-canonical). Observation: we have  $k((t))^{\vee} \cong \Omega(k((t))/k) \cong k((t))dt$  coming from the pairing  $(f,\omega) \mapsto \operatorname{res}(f\omega)$ .

On the other hand, we have

$$(\mathcal{E}_x \otimes_{\mathcal{O}_x, X} F_{\mathrm{res}}(\widehat{\mathcal{O}_{x,X}}))^{\vee} \cong (\mathcal{E}^{\vee} \otimes K_X) \otimes_{\mathcal{O}_{x,X}} F_{\mathrm{res}}(\widehat{\mathcal{O}_{x,X}})$$

where  $F_{\text{res}}$  denotes the residue field. Here's the overall plan of the proof: we have  $Y = X \setminus \{x_1, \dots, x_n\}$  affine. Call the left side  $(\widehat{E_x}^{\circ})^{\vee}$ , and define  $\widehat{E_x} = \mathcal{E}_x \otimes_{\mathcal{O}_{x,X}} \widehat{\mathcal{O}_{x,X}}$ . Then cohomology of  $\mathcal{E}$  is computed using the complex  $\bigoplus_x \widehat{\mathcal{E}_x} \oplus \Gamma(\mathcal{E}|_Y) \to \bigoplus_x \widehat{E_x}^{\circ}$ . We'll check that  $\widehat{E_x}^{\perp} = (\mathcal{E}^{\vee} \otimes K_X)$  and  $\Gamma(\mathcal{E}|_Y)^{\vee} = \Gamma(\mathcal{E}^{\vee} \otimes K_X)$ , and conclude that  $(\widehat{\mathcal{E}_x}^{\circ})^{\vee} = \mathcal{E}^{\vee} \otimes K_X^{\vee}$ .

## Lecture 25: Proof of Serre Duality

We'll deduce the Serre duality of curves from a linear algebra observation: let  $V_1, V_2 \subset V$ , and define  $V_1^{\perp} = \{\lambda \in V^* \mid \lambda(v') = 0 \ \forall v' \in V_1\}$ , then  $V_1^{\perp}, V_2^{\perp} \subset V^*$ , then  $V_1 \cap V_2 = (V^*/V_1^{\perp} + V_2^{\perp})^*$  and  $V_1^{\perp} \cap V_2^{\perp} = (V_1 + V_2)^{\perp} = (V/(V_1 + V_2))^*$ . In particular, let  $C = (V_1 \oplus V_2 \to V)$  and  $C' = (V_1^{\perp} \oplus V_2^{\perp} \to V^*)$ , then  $H^0(C') = H^1(C)^*$  and  $H^1(C') = H^0(C)^*$ .

**Definition 46.** A Tate vector space is vector space with a topology, such that there exists a basis of neighborhoods of 0 consisting of vector subspaces which are commensurable.<sup>4</sup>

**Example 31.** V = k(t) is a Tate vector space, where we consider  $t^i k[[t]]$  as the neighborhoods of 0.

**Residue** Let  $x \in X$  a smooth point on a curve.  $\widehat{\mathcal{O}_{x,X}} = \varinjlim_{n} \mathcal{O}_{x,X}/\mathfrak{m}_{x}^{n} \cong k[[t]]$ , and  $\widehat{\mathcal{O}_{x,X}}^{\circ} = F_{res}(\widehat{\mathcal{O}_{x,X}}) \cong k((t))$ . Then there is a residue map  $\operatorname{Res}: \Omega_{\widehat{\mathcal{O}_{x,X}}} \otimes \widehat{\mathcal{O}_{x,X}}^{\circ} \to k$  by mapping  $\omega = \sum_{n} at^{i}dt$  to  $a_{-1}$ . This is independent of the choice of t. In char k = 0, the residue map is characterized by 1)  $\operatorname{Res}(df) = 0$  and 2)  $\operatorname{Res}(df/f) = 1$  for f a uniformizer. Note that suppose  $f = \varphi t$  for  $\varphi$  invertible, then  $df/f = dt/t + d\varphi/\varphi$ , and the second term creates residue 0. In case of char k = p > 0, of course residue is no longer characterized by

the second term creates residue 0. In case of char k = p > 0, of course residue is no longer characterized by those two, so we need to use a stronger version of 2). A possible choice is that the residue is invariant under automorphisms of the formal Taylor series k[[t]]. For any scalar s in k we have an automorphism  $t^n dt \mapsto s^{n+1}t^n dt$ , and it's clear that the only invariant linear functional is proportional to taking the coefficient at  $t^{-1}dt$ .

For an algebraic group G over any field one has its Lie algebra g which acts on every G-module (as derivations). For a connected group G over a field of characteristic 0 and a G-module M, the (co)invariants of G and of g on M are the same; but this is false in characteristic p. The simplest example comes from  $\mathbb{F}_p[x,y]$ : the polynomial  $x^p$  is not invariant for the group  $\mathrm{GL}(2)$  of linear transformations of the variables, but it's invariant under its Lie algebra, because derivatives of a p-th power vanish.

The group of automorphisms of k[[t]] belongs to a larger class of groups; in particular, it is an infinite dimensional algebraic group (a.k.a. a group scheme of infinite type). Much of the theory goes through for this generalization. The Lie algebra is the Lie algebra of vector fields of the form f(t)d/dt, where  $f(t) \in t^{-1}k[[t]]$ . (One can consider the group  $\operatorname{Aut}(k((t)))$  whose Lie algebra is the more natural thing  $\{f(t)d/dt \mid f \in k((t))\}$ , but this group is even "more infinite dimensional" and there are additional technical subtleties.) Vector fields act on differential forms by Lie derivatives:  $v(\omega) = L_v(\omega) = d(i_v(\omega))$ , where  $L_v$  is the Lie derivative,  $i_v(\omega) \in k((t))$  is the "insertion" (pairing) of the vector field and the 1-form. The condition  $\operatorname{Res}(df) = 0$  is equivalent to invariance of residue under the action of the Lie algebra, which is the same as invariance under the group if we are over a field of characteristic zero, but not in general.

the group if we are over a field of characteristic zero, but not in general. Now we can define a pairing  $\widehat{\mathcal{O}_{x,X}} \times \left(\widehat{\mathcal{O}_{x,X}}^{\circ} \otimes \Omega\right) \to k$  that sends  $(f,\omega)$  to  $\mathrm{Res}(f\omega)$ . Under this we have  $(\widehat{\mathcal{O}_{x,X}}^{\circ} \otimes \Omega) \cong (\widehat{\mathcal{O}_{x,X}}^{\circ})^{\vee}$  as dual topological spaces, where the dual basis for  $t^i$  on the left is  $t^{-i-1}dt$  on the right. (Check that left equals  $k[t^{-1}] \oplus k[[t]]$ , and  $k[t^{-1}]^{\vee} = k[[t]]dt$  and  $k[[t]]^{\vee} = t^{-1}k[t^{-1}]dt$ .) So if we take the non-localized version  $(\widehat{\mathcal{O}_{x,X}} \otimes \Omega)^{\perp} \cong \widehat{\mathcal{O}_{x,X}}$ , then again we can do calculation:  $\sum_{X}^{\infty} a_i t^i dt$  pairing with

$$\sum_{i=0}^{\infty} b_i t^i \text{ yield } 0 \text{ for all } b_i \text{ iff } a_i = 0 \text{ for } i < 0.$$

**Lemma 36.** Suppose X is a complete smooth curve,  $\omega \in \Gamma(U,\Omega)$ , U is a nontrivial open subset, then  $\sum_{x \in X \setminus U} \operatorname{Res}_{x_i} \omega = 0.$ 

Sketch of Proof. (See [Tat68] for another proof.) If  $X = \mathbb{P}^1$ , then it is an explicit computation, as  $\omega$  is a linear combination of  $\frac{dz}{(z-a)^n}$ . For general X, reduce to  $X = \mathbb{P}^1$  as follows: Find a finite separable map  $X \xrightarrow{\varphi} \mathbb{P}^1$ ,  $\omega = f \circ \varphi^*(\theta), f \in R(X), R(X)/R(\mathbb{P}^1)$  is a finite extension, and let  $\overline{f} = \text{Tr}(f) \in R(\mathbb{P}^1)$  under

<sup>&</sup>lt;sup>4</sup>We say  $V_1$  and  $V_2$  are *commensurable* if  $V_1/(V_1 \cap V_2)$  has finite dimension.

this extension. Then one can check that  $\mathrm{Res}_x\overline{f}\theta=\sum_{x_i\mapsto x}\mathrm{Res}_{x_i}(\omega)$  for any  $x\in\mathbb{P}^1$ . As a corollary, we have

$$\sum_{x \in X} \operatorname{Res}(\omega) = \sum_{y \in \mathbb{P}^1} \operatorname{Res}(\overline{f}\theta) = 0.$$

Proof for Serre duality for curves. Let  $\mathcal{E}$  be locally free,  $Y = X \setminus \{x_1, \dots, x_n\}$  be affine, and  $j: Y \to X$ .  $\widehat{\mathcal{E}_x} = \varinjlim \mathcal{E}_x / \mathfrak{m}_x^n = \mathcal{E}_x \otimes_{\mathcal{O}_{x,X}} \widehat{\mathcal{O}_{x,X}} \cong k[[t]]^r$  and  $\widehat{\mathcal{E}_x}^{\circ} = \widehat{\mathcal{E}_x} \otimes_{\widehat{\mathcal{O}_{x,X}}} \widehat{\mathcal{O}_{x,X}} \cong k((t))^r$  where r is the rank of  $\mathcal{E}$ . We claim that  $H^*(X, \mathcal{E})$  is computed by the complex

$$\Gamma(\mathcal{E}|_Y) \oplus \bigoplus_i \widehat{\mathcal{E}_{x_i}} \to \bigoplus_i \widehat{\mathcal{E}_{x_i}}^{\circ}$$

One can check its cohomology is the same as the cohomology of the complex

$$\Gamma(\mathcal{E}|_Y) \to \bigoplus_i \widehat{\mathcal{E}_{x_i}}^{\circ} / \widehat{\mathcal{E}_{x_i}}$$

But the right hand side is just the global section of  $j_*j^*\mathcal{E}/\mathcal{E}$ . Note that rhs at x is  $\mathcal{E}_x \otimes_{\mathcal{O}_{x,X}} \left(\frac{\widehat{\mathcal{O}_{x,X}}^{\circ}}{\widehat{\mathcal{O}_{x,X}}}\right)$ ,

and this is the stalk of  $j_*j^*\mathcal{E}/\mathcal{E}$  at x. (Some more explanation:  $\widehat{\mathcal{O}_{x,X}}^{\circ} = F_{\mathrm{res}}(\mathcal{O}_{x,X})/\mathcal{O}_{x,X} = k[U-x]/k[U]$  where U is an affine neighborhood of x. This is a mathematical probability of  $\mathcal{O}_{x,X}$ .

where U is an affine neighborhood of x. This is a module where  $\mathfrak{m}_x$  acts by a local map where neither localizing by elements in  $\mathfrak{m}_x$  nor replacing  $\mathcal{O}_{x,X}$  by  $\widehat{\mathcal{O}_{x,X}}$  affects it.)

Now set  $V = \bigoplus \widehat{\mathcal{E}_{x_i}}^{\circ} \supset V_1 = \Gamma(\mathcal{E}|_Y), V_2 = \bigoplus \widehat{\mathcal{E}_{x_i}}$ . Then we have the topological dual  $V^{\vee} = \bigcup_{i=1}^{n} \widehat{\mathcal{E}_{x_i}}$ .

 $\bigoplus_{i} (\widehat{\mathcal{E}^{\vee} \otimes \Omega})_{x_{i}}^{\circ}; \text{ set } V_{1}' = \Gamma(\Omega \otimes \mathcal{E}^{\vee}|_{Y}), V_{2}' = \bigoplus \widehat{\Omega \otimes \mathcal{E}_{x_{i}}^{\vee}}. \text{ By the linear algebra discussed above, it re-}$ 

mains to check  $V_1^{\perp} = V_1'$  and  $V_2^{\perp} = V_2'$ .  $V_2^{\perp} = V_2'$  reduces to  $k[[t]]^{\perp} \cong k[[t]]dt$ . We also have  $V_1' \subset V_1^{\perp}$ , which follows from  $\sum \operatorname{Res}_{x_i} \omega = 0$  (the lemma above), and it remains to see  $V_1' = V_1^{\perp}$ . Notice that  $V_1' = V_1^{\perp} \Leftrightarrow \dim(H^i(\mathcal{E}^{\vee} \otimes \Omega)) = \dim(H^{1-i}(\mathcal{E}))$  by what we know.

We want to check that  $V_1^{\perp}/V_1'$  is finite dimensional.  $V_1 \subset V = k[[t]]]^r$ , and as a subspace it is discrete and cocompact, i.e. has a compact complement. Discrete follows from  $H^0$  being finite dimensional, and cocompact follows from  $H^1$  being finite dimensional. Now,  $V_1$  is discrete implies  $V_1^*$  is compact (complete) which implies  $V_1^{\perp}$  is cocompact, and  $V_1$  cocompact implies  $V_1^{\perp} = (V/V_1)^*$  is discrete since  $V/V_1$  is compact. Now in general, for discrete cocompact subspaces  $U \subset W$  of V, one can check that the quotient W/U is discrete compact and finite dimensional.

Now we have that  $V_1^{\perp}$  contains  $V_1'$  with finite codimension (thus the quotient k[Y]-module  $V_1^{\perp}/V_1'$  is supported at finitely many points  $y_1, \ldots, y_m$ ), we can consider it as a subspace of  $K(\Omega \otimes \mathcal{E}^{\vee}|_Y)$ , the space of rational sections of  $\Omega \otimes \mathcal{E}^{\vee}|_Y$ .

From here there are two ways to proceed: on one hand, we can replace Y by  $Y' = Y \setminus \{y_1, \ldots, y_m\}$ . Then  $\Gamma(\mathcal{E}|_{Y'})^{\perp} = \Gamma(\mathcal{E}|_Y)^{\perp}_{(f_1,\ldots,f_m)}$  where localization by  $f_i$  correspond to removing  $y_i$  (observe that if  $s \in \Gamma(\mathcal{E}|_{Y'})^{\perp} \subset K(\Omega \otimes \mathcal{E}^{\vee}|_Y)$  and s is regular at each  $y_i$ , then  $s \in \Gamma(\mathcal{E}|_Y)$ ), and we still get rational sections that may be singular at  $y_i$ ; on the other hand,  $\Gamma(\Omega \otimes \mathcal{E}^{\vee}|_{Y'})$  consists of rational sections of  $\Omega \otimes \mathcal{E}^{\vee}$  on Y that may be singular on  $y_i$ , so we have  $V_1^{\perp} = V_1'$  for Y'. On the other hand, we can directly check  $V_1^{\perp} \supset V_1'$ : suppose s is a rational section in  $V_1^{\perp}$ , and has singularities  $y_1, \ldots, y_m$ . Then since Y is affine, one can find a section s' of  $\mathcal{E}$  such that (s, s'), which is a section of  $\Omega$ , is regular at  $y_i$  for i > 1, but  $\operatorname{Res}_{y_1}(s, s') \neq 0$ . Then we see that s cannot be orthogonal to s'.

Now we state some standard corollaries.

Corollary 29. Define the arithmetic genus  $g_a = \dim(H^1(\mathcal{O}))$ , and the geometric genus  $g_m = \dim(G(K_X))$ . Then apply Serre duality to  $\mathcal{E} = \mathcal{O}$  to get  $g_a = g_m$ .

Corollary 30. Riemann-Roch implies  $\dim(\Gamma(\mathcal{E})) - \dim(\Gamma(K \otimes \mathcal{E}^*)) = \deg(\mathcal{E}) + \operatorname{rank}(\mathcal{E})(1-g)$ . This is Riemann's form of the theorem.

Corollary 31. deg(K) = 2g - 2.

*Proof.* 
$$\chi(\mathcal{O}) = -\chi(K)$$
 by Serre duality.  $\deg(K) = \chi(K) + g - 1 = 2g - 2$ .

The statement of the Serre duality generalizes: let X be a smooth complete (irreducible) variety of dimension n, and let  $\mathcal{E}$  be a locally free sheaf, then there is a duality  $H^{n-i}(\mathcal{E}^{\vee} \otimes K) \cong H^i(\mathcal{E})^*$ . It can also be generalized to not locally free sheaves and non-smooth varieties (best described using derived categories).

For instance, let X be a smooth affine curve, and  $\mathscr{F}$  a torsion sheaf. Then there exists a canonical isomorphism  $\Gamma(\mathscr{F})^* \cong \operatorname{Ext}^1(\mathcal{F}, K_X)$ . Suppose X is smooth of dimension n, and  $\mathscr{F}$  torsion is supported at a 0-dimensional set, then  $\Gamma(\mathscr{F})^* \cong \operatorname{Ext}^m(\mathscr{F}, K_X)$ . Generalizations of Riemann-Roch include the Hirzebruch-Riemann-Roch theorem and the Grothendieck-Riemann-Roch theorem.

Let X complete,  $\mathscr{F}$  coherent sheaf,  $\chi(\mathscr{F})$  is a topological invariant of  $\mathscr{F}$ , i.e. one can give a formula for  $\chi(\mathscr{F})$  in terms of topological invariants of  $\mathscr{F}$  and that of the tangent bundle of X. For instance, suppose X is locally free and is over  $\mathbb{C}$ , then it corresponds to a vector bundle, and has Chern classes. Then  $\chi(\mathscr{F})$  is expressed via the Chern classes. In particular, it's constant in families. Even more generally, recall that the global section functor is the same as direct image of the map to a point, and cohomology are the higher direct images. So if we replace  $X \to \operatorname{pt}$  to an arbitrary map  $X \to Y$ , we get Grothendieck's version of Riemann-Roch.

A major theme of AG is the question of how to reconstruct topological invariants of  $X(\mathbb{C})_{cl}$  (classical) from AG data. This of course can also generalize to other fields. There are two approaches: the de Rham approach (using differentials, e.g. if X is an affine smooth variety, then X's regular cohomology can be

computed using its algebraic de Rham complex  $k[X] \xrightarrow{d} \Gamma(\Omega^1 X) \xrightarrow{d} \Gamma(\Omega^2 X) \to \dots$  where  $\Omega^i X = \bigwedge^i \Omega X$ , and the etale approach (related to counting of  $X(\mathbb{F}_q)$  and the Weil conjectures).

## References

- [Bou<br/>98] N. Bourbaki. Commutative Algebra: Chapters 1-7. Vol. 1. Springer Science & Business Media,<br/>1998.
- [Har77] Robin Hartshorne. Algebraic geometry. Vol. 52. Springer Science & Business Media, 1977.
- [Kem93] George Kempf. Algebraic varieties. Vol. 172. Cambridge University Press, 1993.
- [SH77] Igor Rostislavovich Shafarevich and Kurt Augustus Hirsch. Basic algebraic geometry. Vol. 1. Springer, 1977.
- [Tat68] J. Tate. "Residues of differentials on curves." English. In: Ann. Sci. Éc. Norm. Supér. (4) 1.1 (1968), pp. 149–159. ISSN: 0012-9593.

MIT OpenCourseWare http://ocw.mit.edu

18.725 Algebraic Geometry Fall 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.