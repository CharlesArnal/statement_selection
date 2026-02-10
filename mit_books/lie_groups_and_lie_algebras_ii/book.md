# LIE GROUPS AND LIE ALGEBRAS

# PAVEL ETINGOF

# Contents

| Intr  | roduction                                                   | 8   |
|-------|-------------------------------------------------------------|-----|
| 1.    | Manifolds                                                   | 11  |
| 1.1.  | Topological spaces and groups                               | 11  |
| 1.2.  | Topological manifolds                                       | 11  |
| 1.3.  | $C^k$ , real analytic and complex analytic manifolds        | 14  |
| 1.4.  | Regular functions                                           | 15  |
| 1.5.  | Tangent spaces                                              | 16  |
| 1.6.  | Regular maps                                                | 17  |
| 1.7.  | Submersions and immersions, submanifolds                    | 18  |
| 2.    | Lie groups, I                                               | 20  |
| 2.1.  | The definition of a Lie group                               | 20  |
| 2.2.  | Homomorphisms                                               | 20  |
| 2.3.  | Examples                                                    | 20  |
| 2.4.  | The connected component of 1                                | 21  |
| 3.    | Lie groups, II                                              | 23  |
| 3.1.  | A crash course on coverings                                 | 23  |
| 3.2.  | Coverings of Lie groups                                     | 25  |
| 3.3.  | Closed Lie subgroups                                        | 26  |
| 3.4.  | Generation of connected Lie groups by a neighborhood of     |     |
|       | the identity                                                | 27  |
| 4.    | Homogeneous spaces, Lie group actions                       | 28  |
| 4.1.  | Homogeneous spaces                                          | 28  |
| 4.2.  | Lie subgroups                                               | 29  |
| 4.3.  | Actions and representations of Lie groups                   | 30  |
| 4.4.  | Orbits and stabilizers                                      | 31  |
| 4.5.  | Left translation, right translation, and adjoint action     | 32  |
| 5.    | Tensor fields                                               | 33  |
| 5.1.  | A crash course on vector bundles                            | 33  |
| 5.2.  | Vector fields                                               | 35  |
|       | Tensor fields, differential forms                           | 36  |
| 5.4.  | Left and right invariant tensor fields on Lie groups        | 36  |
| 6.    | Classical Lie groups                                        | 38  |
|       | 1                                                           |     |
|       |                                                             |     |
| 6.1.  | First examples of classical groups                          | 38  |
| 6.2.  | Quaternions                                                 | 40  |
| 6.3.  | More classical groups                                       | 41  |
| 7.    | The exponential map of a Lie group                          | 44  |
| 7.1.  | The exponential map                                         | 44  |
| 7.2.  | The commutator                                              | 46  |
| 8. ]  | Lie algebras                                                | 49  |
| 8.1.  | The Jacobi identity                                         | 49  |
| 8.2.  | Lie algebras                                                | 49  |
| 8.3.  | Lie subalgebras and ideals                                  | 50  |
| 8.4.  | The Lie algebra of vector fields                            | 51  |
| 9. ]  | Fundamental theorems of Lie theory                          | 53  |
| 9.1.  | Proofs of Theorem 3.13, Proposition 4.12, Proposition 4.7   | 53  |
| 9.2.  | The center of $G$ and $\mathfrak{g}$                        | 54  |
| 9.3.  | The statements of the fundamental theorems of Lie theory    | 55  |
| 9.4.  | Complexification of real Lie groups and real forms of       |     |
|       | complex Lie groups                                          | 56  |
| 10.   | Proofs of the fundamental theorems of Lie theory            | 58  |
| 10.1. |                                                             | 58  |
| 10.2. | Proofs of the fundamental theorems of Lie theory            | 60  |
| 11.   | Representations of Lie groups and Lie algebras              | 62  |
| 11.1. | Representations                                             | 62  |
| 11.2. | Schur's lemma                                               | 64  |
| 11.3. | Unitary representations                                     | 65  |
| 11.4. | Representations of $\mathfrak{sl}_2$                        | 65  |
| 12.   | The universal enveloping algebra of a Lie algebra           | 69  |
| 12.1. | The definition of the universal enveloping algebra          | 69  |
| 12.2. | Graded and filtered algebras                                | 70  |
| 12.3. | The coproduct of $U(\mathfrak{g})$                          | 71  |
| 12.4. | Differential operators on manifolds and Lie groups          | 72  |
| 13.   | The Poincaré-Birkhoff-Witt theorem                          | 74  |
| 13.1. | The statement of the Poincaré-Birkhoff-Witt theorem         | 74  |
| 13.2. | Proof of the PBW theorem                                    | 75  |
| 14.   | Free Lie algebras, the Baker-Campbell-Hausdorff             |     |
|       | formula                                                     | 78  |
| 14.1. | Primitive elements                                          | 78  |
| 14.2. | Free Lie algebras                                           | 78  |
| 14.3. | The Baker-Campbell-Hausdorff formula                        | 79  |
| 15.   | Solvable and nilpotent Lie algebras, theorems of            |     |
|       | Lie and Engel                                               | 81  |
| 15.1. | Ideals and commutant                                        | 81  |
| 15.2. | Solvable Lie algebras                                       | 81  |
| 15.3. | Nilpotent Lie algebras                                      | 82  |
| 15.4. | Lie's theorem                                               | 82  |
| 15.5. | Engel's theorem                                             | 85  |
| 16.   | Semisimple and reductive Lie algebras, the Cartan           | L   |
|       | criteria                                                    | 87  |
| 16.1. | Semisimple and reductive Lie algebras, the radical          | 87  |
| 16.2. | Invariant inner products                                    | 89  |
| 16.3. | The Killing form and the Cartan criteria                    | 90  |
| 16.4. | Jordan decomposition                                        | 90  |
|       | Proofs of the Cartan criteria, properties of                |     |
|       | semisimple Lie algebras                                     | 92  |
| 17.1. | Proof of the Cartan solvability criterion                   | 92  |
| 17.2. | Proof of the Cartan semisimplicity criterion                | 93  |
| 17.3. | Properties of semisimple Lie algebras                       | 93  |
| 18.   | Extensions of representations, Whitehead's                  |     |
|       | theorem, complete reducibility                              | 96  |
| 18.1. | Extensions                                                  | 96  |
| 18.2. | Whitehead's theorem                                         | 98  |
| 18.3. | Proof of Theorem 18.4                                       | 98  |
| 18.4. | Complete reducibility of representations of semisimple      |     |
|       | Lie algebras                                                | 100 |
| 19.   | Structure of semisimple Lie algebras, I                     | 101 |
| 19.1. | Semisimple elements                                         | 101 |
| 19.2. | O .                                                         | 102 |
| 19.3. | Cartan subalgebras                                          | 102 |
| 19.4. | Root decomposition                                          | 103 |
| 20.   | Structure of semisimple Lie algebras, II                    | 107 |
| 20.1. | Strongly regular (regular semisimple) elements              | 107 |
| 20.2. | Conjugacy of Cartan subalgebras                             | 109 |
| 20.3. | Root systems of classical Lie algebras                      | 110 |
| 21.   | Root systems                                                | 112 |
| 21.1. |                                                             | 112 |
| 21.2. | The Weyl group                                              | 113 |
| 21.3. | Root systems of rank 2                                      | 113 |
| 21.4. | Positive and simple roots                                   | 114 |
| 21.5. | Dual root system                                            | 116 |
| 21.6. | Root and weight lattices                                    | 116 |
| 22.   | Properties of the Weyl group                                | 118 |
| 22.1. | v                                                           | 118 |
| 22.2. | <u>.</u>                                                    | 119 |
| 22.3. | , O 1                                                       | 120 |
| 23.   | Dynkin diagrams                                             | 122 |
|       |                                                             |     |
| 23.1. | Cartan matrices and Dynkin diagrams                         | 122 |
| 23.2. | · · · · · · · · · · · · · · · · · · ·                       | 123 |
| 23.3. |                                                             | 124 |
| 23.4. | · · · · · · · · · · · · · · · · · · ·                       | 125 |
| 23.5. | · ·                                                         | 125 |
| 23.6. |                                                             | 126 |
| 23.7. | · · · · · · · · · · · · · · · · · · ·                       | 126 |
| 23.8. | · · · · · · · · · · · · · · · · · · ·                       | 127 |
| 23.9. | Simply laced and non-simply laced diagrams                  | 128 |
| 24.   | Construction of a semisimple Lie algebra from a             |     |
|       | Dynkin diagram                                              | 129 |
| 24.1. | Serre relations                                             | 129 |
| 24.2. | The Serre presentation for semisimple Lie algebras          | 130 |
| 25.   | Representation theory of semisimple Lie algebras            | 133 |
| 25.1. |                                                             | 133 |
| 25.2. | Verma modules                                               | 134 |
| 25.3. | Finite dimensional modules                                  | 136 |
| 26.   | The Weyl character formula                                  | 138 |
| 26.1. | Characters                                                  | 138 |
| 26.2. | Category $\mathcal{O}$                                      | 138 |
| 26.3. | The Weyl character formula                                  | 140 |
| 26.4. | Proof of the Weyl character formula                         | 140 |
| 26.5. |                                                             | 142 |
| 27.   | Representations of $GL_n$ , I                               | 145 |
| 27.1. | Tensor products of fundamental representations              | 145 |
| 27.2. |                                                             | 145 |
| 27.3. | Representations of $GL_n(\mathbb{C})$                       | 146 |
| 27.4. | Schur-Weyl duality                                          | 147 |
| 28.   | Representations of $GL_n$ , II                              | 151 |
| 28.1. |                                                             | 151 |
| 28.2. | The fundamental theorem of invariant theory                 | 153 |
| 29.   | Representations of $GL_n$ , III                             | 155 |
| 29.1. |                                                             |     |
|       | the symmetric group                                         | 155 |
| 29.2. | Howe duality                                                | 156 |
| 30.   | Fundamental and minuscule weights                           | 158 |
| 30.1. | Minuscule weights                                           | 158 |
| 30.2. | 9                                                           | 160 |
| 30.3. |                                                             | 164 |
| 30.4. |                                                             | 164 |
| 31.   | Fundamental representations of classical Lie                |     |
|       | algebras                                                    | 165 |
|       |                                                             |     |
| 31.1. | Type $C_n$                                                  | 165 |
| 31.2. | Type $B_n$                                                  | 165 |
| 31.3. | Type $D_n$                                                  | 167 |
| 31.4. | The Clifford algebra                                        | 169 |
| 32.   | Maximal root, exponents, Coxeter numbers, dual              |     |
|       | representations                                             | 172 |
| 32.1. | Duals of irreducible representations                        | 172 |
| 32.2. | The maximal root                                            | 173 |
| 32.3. | Principal $\mathfrak{sl}_2$ , exponents                     | 174 |
| 32.4. | The Coxeter number and the dual Coxeter number              | 175 |
| 32.5. | Representations of complex, real and quaternionic type      | 176 |
| 33.   | Differential forms, partitions of unity                     | 178 |
| 33.1. | Locally compact spaces                                      | 178 |
| 33.2. | Reminder on differential forms                              | 178 |
| 33.3. | Partitions of unity                                         | 180 |
| 34.   | Integration on manifolds                                    | 182 |
| 34.1. | Integration of top differential forms on oriented manifolds | 182 |
| 34.2. | Nonvanishing forms                                          | 183 |
| 34.3. | Stokes formula                                              | 184 |
| 34.4. | Integration on Lie groups                                   | 185 |
| 35.   | Representations of compact Lie groups                       | 187 |
| 35.1. | Unitary representations                                     | 187 |
| 35.2. | Matrix coefficients                                         | 187 |
| 35.3. | The Peter-Weyl theorem                                      | 189 |
| 35.4. | An alternative formulation of the Peter-Weyl theorem        | 190 |
| 35.5. | Orthogonality and completeness of characters                | 192 |
| 36.   | Proof of the Peter-Weyl theorem                             | 193 |
| 36.1. | Compact operators and the Hilbert-Schmidt theorem           | 193 |
| 36.2. | Proof of the Peter-Weyl theorem                             | 195 |
| 36.3. | Existence of faithful representations                       | 195 |
| 36.4. | Density in continuous functions                             | 196 |
| 37.   | Representations of compact topological groups               | 199 |
| 37.1. |                                                             | 199 |
| 37.2. | The Peter-Weyl theorem for compact topological groups       | 202 |
| 38.   | The hydrogen atom, I                                        | 204 |
| 38.1. | The Schrödinger equation                                    | 204 |
| 38.2. | Bound states                                                | 205 |
| 39.   | The hydrogen atom, II                                       | 209 |
| 39.1. | Quantum numbers                                             | 209 |
| 39.2. | Coulomb waves                                               | 209 |
| 39.3. | Spin                                                        | 210 |
| 39.4. |                                                             | 210 |
|       | 5                                                           |     |

| 40.   | Forms of semisimple Lie algebras over an arbitrary     |     |  |  |  |  |  |  |
|-------|--------------------------------------------------------|-----|--|--|--|--|--|--|
|       | field                                                  | 213 |  |  |  |  |  |  |
| 40.1. | Automorphisms of semisimple Lie algebras               | 213 |  |  |  |  |  |  |
|       | 1 0                                                    | 214 |  |  |  |  |  |  |
| 40.3. | Real forms of a semisimple Lie algebra                 | 215 |  |  |  |  |  |  |
| 41.   | Classification of real forms of semisimple Lie         |     |  |  |  |  |  |  |
|       | algebras                                               | 218 |  |  |  |  |  |  |
| 41.1. | The compact real form                                  | 218 |  |  |  |  |  |  |
| 41.2. | Other examples of real forms                           | 219 |  |  |  |  |  |  |
| 41.3. | Classification of real forms                           | 220 |  |  |  |  |  |  |
| 41.4. | 1.4. Real forms of classical Lie algebras              |     |  |  |  |  |  |  |
| 42.   | Real forms of exceptional Lie algebras                 | 225 |  |  |  |  |  |  |
| 42.1. | Equivalence of Vogan diagrams                          | 225 |  |  |  |  |  |  |
| 42.2. | Classification of real forms                           | 225 |  |  |  |  |  |  |
| 43.   | Classification of connected compact and complex        |     |  |  |  |  |  |  |
|       | g <b>1</b>                                             | 230 |  |  |  |  |  |  |
| 43.1. | Connected compact Lie groups                           | 230 |  |  |  |  |  |  |
| 43.2. | Polar decomposition                                    | 232 |  |  |  |  |  |  |
| 43.3. | Connected complex reductive groups                     | 233 |  |  |  |  |  |  |
|       | 0 1                                                    | 234 |  |  |  |  |  |  |
| 44.   | Maximal tori in compact groups, Cartan                 |     |  |  |  |  |  |  |
|       | 1                                                      | 235 |  |  |  |  |  |  |
| 44.1. | Maximal tori in connected compact Lie groups           | 235 |  |  |  |  |  |  |
| 44.2. | Semisimple and unipotent elements                      | 236 |  |  |  |  |  |  |
| 44.3. | Maximal abelian subspaces of $\mathfrak{p}_{\theta}$   | 237 |  |  |  |  |  |  |
| 44.4. |                                                        | 238 |  |  |  |  |  |  |
| 44.5. | 1 0 1                                                  | 238 |  |  |  |  |  |  |
| 44.6. | Cartan subalgebras in real semisimple Lie algebras     | 241 |  |  |  |  |  |  |
| 44.7. | ů ,                                                    | 243 |  |  |  |  |  |  |
| 45.   | Topology of Lie groups and homogeneous spaces, I       |     |  |  |  |  |  |  |
| 45.1. | The Chevalley-Eilenberg complex of a compact connected |     |  |  |  |  |  |  |
|       | 0 1                                                    | 245 |  |  |  |  |  |  |
| 45.2. | Cohomology of Lie algebras                             | 247 |  |  |  |  |  |  |
| 46.   | Topology of Lie groups and homogeneous spaces, II      |     |  |  |  |  |  |  |
| 46.1. | 1 0, 0                                                 | 250 |  |  |  |  |  |  |
| 46.2. | The cohomology ring of a simple compact connected Lie  |     |  |  |  |  |  |  |
|       | group                                                  | 252 |  |  |  |  |  |  |
| 46.3. |                                                        | 253 |  |  |  |  |  |  |
| 47.   | Topology of Lie groups and homogeneous spaces,         |     |  |  |  |  |  |  |
|       |                                                        | 256 |  |  |  |  |  |  |
| 47.1. |                                                        | 256 |  |  |  |  |  |  |
| 47.2. | Schubert cells                                         | 257 |  |  |  |  |  |  |

| 47.3. | Flag manifolds                                             | 258 |
|-------|------------------------------------------------------------|-----|
| 48.   | Levi decomposition                                         | 260 |
| 48.1. | Cohomology of Lie algebras with coefficients               | 260 |
| 48.2. | Levi decomposition                                         | 264 |
| 49.   | The third fundamental theorem of Lie theory                | 265 |
| 49.1. | Exponentiating nilpotent and solvable Lie algebras and     |     |
|       | the third fundamental theorem of Lie theory                | 265 |
| 49.2. | Formal groups                                              | 266 |
| 50.   | Ado's theorem                                              | 271 |
| 50.1. | The nilradical                                             | 271 |
| 50.2. | Algebraic Lie algebras                                     | 271 |
| 50.3. | Faithful representations of nilpotent Lie algebras         | 272 |
| 50.4. | Faithful representations of general finite dimensional Lie |     |
|       | algebras                                                   | 274 |
| 51.   | Borel subgroups and the flag manifold of a complex         |     |
|       | reductive Lie group                                        | 275 |
| 51.1. | Borel subgroups and subalgebras                            | 275 |
| 51.2. | The flag manifold of a connected complex reductive         |     |
|       | group                                                      | 275 |
| 51.3. | The Borel fixed point theorem                              | 276 |
| 51.4. | Parabolic and Levi subalgebras                             | 277 |
| 51.5. | Maximal solvable and maximal nilpotent subalgebras         | 277 |
| 51.6. | Iwasawa decomposition of a real semisimple linear group    | 279 |
| 51.7. | The Bruhat decomposition                                   | 279 |
| Refer | rences                                                     | 281 |

#### Introduction

The purpose of **group theory** is to give a mathematical treatment of **symmetries**. For example, symmetries of a set of n elements form the symmetric group  $S_n$ , and symmetries of a regular n-gon – the dihedral group  $D_n$ . Likewise, **Lie group theory** serves to give a mathematical treatment of **continuous symmetries**, i.e., families of symmetries continuously depending on several real parameters.

The theory of Lie groups was founded in the second half of the 19th century by the Norwegian mathematician **Sophus Lie**, after whom it is named. It was then developed by many mathematicians over the last 150 years, and has numerous applications in mathematics and science, especially physics.

A prototypical example of a Lie group is the group SO(3) of rotational symmetries of the 2-dimensional sphere; in this case the parameters are the Euler angles  $\phi, \theta, \psi$ .

It turns out that unlike ordinary parametrized curves and surfaces, Lie groups are determined by their linear approximation at the identity element. This leads to the notion of the **Lie algebra** of a Lie group. This notion allows one to reformulate the theory of continuous symmetries in purely algebraic terms, which provides an extremely effective way of studying such symmetries. The goal of these notes is to give a detailed study of Lie groups and Lie algebras and interactions between them, with numerous examples.

These notes are based on a year-long introductory course on Lie groups and Lie algebras given by the author at MIT in 2020-2021 (in particular, they contain no original material). The first half (Sections 1-26) corresponds to the first semester and follows rather closely the excellent book "An introduction to Lie groups and Lie algebras" by A. Kirillov Jr. ([K]), but also discusses some additional topics. Namely, after a brief review of geometry and topology of manifolds, it covers the basic theory of Lie groups and Lie algebras, including the three fundamental theorems of Lie theory (except the proof of the third theorem, which is given in the second half). Then it proceeds to nilpotent and solvable Lie algebras, theorems of Lie and Engel, representations of  $\mathfrak{sl}_2$ , enveloping algebras and the Poincaré-Birkhoff Witt theorem, free Lie algebras, the Baker-Campbell-Hausdorff formula, and concludes with a detailed study and classification of complex semisimple Lie algebras, their representations, and the Weyl character formula.

The second half (starting with Section 27) covers representation theory of  $GL_n$  and other classical groups, minuscule representations, spin representations and spin groups, representation theory of compact Lie

groups (again following [K]) and, more generally, compact topological groups, including existence of the Haar measure and the Peter-Weyl theorem. Then it discusses applications to quantum mechanics (a fairly complete treatment of the hydrogen atom) and proceeds to real forms of semisimple Lie algebras and groups, discussing the classification of such forms in terms of Vogan diagrams, maximal tori and maximal compact subgroups, the polar and Cartan decompositions, and classification of connected compact Lie groups and complex reductive groups. Then we discuss topology of Lie groups and homogeneous spaces (in particular, their cohomology rings), cohomology of Lie algebras, prove the third fundamental theorem of Lie theory and Ado's theorem on the existence of a faithful representation for a finite dimensional Lie algebra, and conclude with the study of Borel and parabolic subgroups, the flag manifold of a complex semisimple group and the Iwasawa decomposition for real groups.

Some other sources covering the same material are [E, FH, Hu, Kn]. Each section roughly corresponds to one 80-minute lecture. Part I consists of 26 sections, which corresponds to a 1-semester course. Part II consists of 25 sections, to allow for a review of Part I. Also, a lot of material is contained in exercises, which are often provided with detailed hints. These exercises were assigned as homework problems.<sup>1</sup>

Finally, we note that Lie theory is an inherently synthetic subject. While the main technical tools ultimately boil down to various parts of algebra (notably linear algebra and the theory of noncommutative rings and modules, and, at more advanced stages, algebraic geometry), Lie theory also relies in important ways on analysis, differential equations, differential geometry and topology. Thus, while we try to recall basic notions from these subjects along the way, the reader will need some degree of dexterity with them, which increases as we dig deeper into the material.

Acknowledgments. I'd like to thank David Vogan for inspiring me to write these notes and useful comments, and the students of the MIT courses "Lie groups and Lie algebras, I,II" for feedback. I am especially grateful to Frank Wang and Atticus Wang for careful reading and many corrections to parts I and II, respectively. This work was partially supported by the NSF grant DMS-2001318.

<sup>&</sup>lt;sup>1</sup>During the first semester and at the beginning of the second one homework problems were also assigned from [K].

# Lie groups and Lie algebras, I

#### 1. Manifolds

1.1. **Topological spaces and groups.** Recall that the mathematical notion responsible for describing continuity is that of a **topological space**. Thus, to describe continuous symmetries, we should put this notion together with the notion of a group. This leads to the concept of a **topological group**.

Recall:

- A **topological space** is a set X, certain subsets of which (including  $\emptyset$  and X) are declared to be **open**, so that an arbitrary union and finite intersection of open sets is open.
  - The collection of open sets in X is called **the topology** of X.
- A subset  $Z \subset X$  of a topological space X is **closed** if its complement is open.
- If X, Y are topological spaces then the Cartesian product  $X \times Y$  has a natural **product topology** in which open sets are (possibly infinite) unions of products  $U \times V$ , where  $U \subset X, V \subset Y$  are open.
- Every subset  $Z \subset X$  of a topological space X carries a natural **induced topology**, in which open sets are intersections of open sets in X with Z.
- A map  $f: X \to Y$  between topological spaces is **continuous** if for every open set  $V \subset Y$ , the preimage  $f^{-1}(V)$  is open in X.

For example, the open sets of the usual topology of the real line  $\mathbb{R}$  are (disjoint) unions of open intervals (a, b), where  $-\infty \le a < b \le \infty$ .

**Definition 1.1.** A topological group is a group G which is also a topological space, so that the multiplication map  $m: G \times G \to G$  and the inversion map  $\iota: G \to G$  are continuous.

For example, the group  $(\mathbb{R}, +)$  of real numbers with the operation of addition and the usual topology of  $\mathbb{R}$  is a topological group, since the functions  $(x, y) \mapsto x + y$  and  $x \mapsto -x$  are continuous. Also a subgroup of a topological group is itself a topological group, so another example is rational numbers with addition,  $(\mathbb{Q}, +)$ . This last example is not a very good model for continuity, however, and shows that general topological groups are not very well behaved. Thus, we will focus on a special class of topological groups called **Lie groups**.

Lie groups are distinguished among topological groups by the property that as topological spaces they belong to a very special class called **topological manifolds.** So we need to start with reviewing this notion.

#### 1.2. **Topological manifolds.** Recall:

- A **neighborhood** of a point  $x \in X$  in a topological space X is an open set containing x.
- A base for a topological space X is a collection  $\mathcal{B}$  of open sets in X such that for every neighborhood U of a point  $x \in X$  there exists a neighborhood  $V \subset U$  of x which belongs to  $\mathcal{B}$ . Equivalently, every open set in X is a union of members of  $\mathcal{B}$ .

For example, open intervals form a base of the usual topology of  $\mathbb{R}$ . Moreover, we may take only intervals whose endpoints have rational coordinates, which gives a *countable* base for  $\mathbb{R}$ . Also if X, Y are topological spaces with bases  $\mathcal{B}_X, \mathcal{B}_Y$  then products  $U \times V$ , where  $U \in \mathcal{B}_X, V \in \mathcal{B}_Y$ , form a base of the product topology of  $X \times Y$ . Thus if X and Y have countable bases, so does  $X \times Y$ ; in particular,  $\mathbb{R}^n$  with its usual (product) topology has a countable base (boxes whose vertices have rational coordinates).

- $\bullet$  X is **Hausdorff** if any two distinct points have disjoint neighborhoods.
- If X is Hausdorff, we say that a sequence of points  $x_n \in X$ ,  $n \in \mathbb{N}$  **converges** to  $x \in X$  as  $n \to \infty$  (denoted  $x_n \to x$ ) if every neighborhood of x contains almost all terms of this sequence. Then one also says that the **limit** of  $x_n$  is x and writes

$$\lim_{n \to \infty} x_n = x.$$

It is easy to show that the limit is unique when it exists. In a Hausdorff space with a countable base, a closed set is one that is closed under taking limits of sequences.

- A Hausdorff space X is **compact** if every open cover  $\{U_{\alpha}, \alpha \in A\}$  of X (i.e.,  $U_{\alpha} \subset X$  for all  $\alpha \in A$  and  $X = \bigcup_{\alpha \in A} U_{\alpha}$ ) has a finite subcover.
- A continuous map  $f: X \to Y$  is a **homeomorphism** if it is a bijection and  $f^{-1}: Y \to X$  is continuous.

**Definition 1.2.** A Hausdorff topological space X is said to be an n-dimensional topological manifold if it has a countable base and for every  $x \in X$  there is a neighborhood  $U \subset X$  of x and a continuous map  $\phi: U \to \mathbb{R}^n$  such that  $\phi: U \to \phi(U)$  is a homeomorphism and  $\phi(U) \subset \mathbb{R}^n$  is open.

The second property is often formulated as the condition that X is locally homeomorphic to  $\mathbb{R}^n$ .

It is true (although not immediately obvious) that if a nonempty open set in  $\mathbb{R}^n$  is homeomorphic to one in  $\mathbb{R}^m$  then n=m. Therefore, the number n is uniquely determined by X as long as  $X \neq \emptyset$ . It is

called **the dimension** of X. (By convention,  $\emptyset$  is a manifold of any integer dimension).

**Example 1.3.** 1. Obviously  $X = \mathbb{R}^n$  is an n-dimensional topological manifold: we can take U = X and  $\phi = \mathrm{Id}$ .

- 2. An open subset of a topological manifold is itself a topological manifold of the same dimension.
- 3. The circle  $S^1 \subset \mathbb{R}^2$  defined by the equation  $x^2 + y^2 = 1$  is a topological manifold: for example, the point (1,0) has a neighborhood  $U = S^1 \setminus \{(-1,0)\}$  and a map  $\phi: U \to \mathbb{R}$  given by the stereographic projection:

$$\phi(\theta) = \tan(\frac{\theta}{2}), -\pi < \theta < \pi.$$

and similarly for every other point. More generally, the sphere  $S^n \subset \mathbb{R}^{n+1}$  defined by the equation  $x_0^2 + \ldots + x_n^2 = 1$  is a topological manifold, for the same reason. The stereographic projection for the 2-dimensional sphere is shown in the following picture.

4. The curve  $\infty$  is not a manifold, since it is not locally homeomorphic to  $\mathbb{R}$  at the self-intersection point (show it!)

A pair  $(U, \phi)$  with the above properties is called a **local chart**. An **atlas** of local charts is a collection of charts  $(U_{\alpha}, \phi_{\alpha}), \alpha \in A$  such that  $\bigcup_{\alpha \in A} U_{\alpha} = X$ ; i.e.,  $\{U_{\alpha}, \alpha \in A\}$  is an open cover of X. Thus any topological manifold X admits an atlas labeled by points of X. There are also much smaller atlases. For instance, an open set in  $\mathbb{R}^n$  has an atlas with just one chart, while the sphere  $S^n$  has an atlas with two charts. Very often X admits an atlas with finitely many charts. For example, if X is compact then there is a finite atlas, since every atlas has a finite subatlas. Moreover, there is always a countable atlas, due to the following lemma:

**Lemma 1.4.** If X is a topological space with a countable base then every open cover of X has a countable subcover.

*Proof.* Let  $\{V_i, i \in \mathbb{N}\}$  be a countable base of X. If  $\{U_\alpha\}$  is an open cover of X then for each  $x \in X$  pick indices i(x) and  $\alpha(x)$  such that

 $x \in V_{i(x)} \subset U_{\alpha(x)}$ . Let  $I \subset \mathbb{N}$  be the image of the map i. For each  $j \in I$  pick  $x \in X$  such that i(x) = j and set  $\alpha_j := \alpha(x)$ . Then  $\{U_{\alpha_j}, j \in I\}$  is a countable subcover of  $\{U_{\alpha}\}$ .

Now let  $(U, \phi)$  and  $(V, \psi)$  be two charts such that  $V \cap U \neq \emptyset$ . Then we have the **transition map** 

$$\phi \circ \psi^{-1} : \psi(U \cap V) \to \phi(U \cap V),$$

which is a homeomorphism between open subsets in  $\mathbb{R}^n$ . For example, consider the atlas of two charts for the circle  $S^1$  (Example 1.3(3)), one missing the point (-1,0) and the other missing the point (1,0). Then  $\phi(\theta) = \tan(\frac{\theta}{2})$  and  $\psi(\theta) = \cot(\frac{\theta}{2})$ ,  $\phi(U \cap V) = \psi(U \cap V) = \mathbb{R} \setminus 0$ , and  $(\phi \circ \psi^{-1})(x) = \frac{1}{x}$ .

1.3.  $C^k$ , real analytic and complex analytic manifolds. The notion of topological manifold is too general for us, since continuous functions on which it is based in general do not admit a linear approximation. To develop the theory of Lie groups, we need more regularity. So we make the following definition.

**Definition 1.5.** An atlas on X is said to be **of regularity class**  $C^k$ ,  $1 \le k \le \infty$ , if all transition maps between its charts are of class  $C^k$  (k times continuously differentiable). An atlas of class  $C^\infty$  is called **smooth**. Also an atlas is said to be **real analytic** if all transition maps are real analytic. Finally, if n = 2m is even, so that  $\mathbb{R}^n = \mathbb{C}^m$ , then an atlas is called **complex analytic** if all its transition maps are complex analytic (i.e., holomorphic).

**Example 1.6.** The two-chart atlas for the circle  $S^1$  defined by stereographic projections (Example 1.3(3)) is real analytic, since the function  $f(x) = \frac{1}{x}$  is analytic. The same applies to the sphere  $S^n$  for any n. For example, for  $S^2$  it is easy to see that the transition map  $\mathbb{R}^2 \setminus 0 \to \mathbb{R}^2 \setminus 0$  is given by the formula

$$f(x,y) = \left(\frac{x}{x^2 + y^2}, \frac{y}{x^2 + y^2}\right).$$

Using the complex coordinate z = x + iy, we get

$$f(z) = z/|z|^2 = 1/\overline{z}.$$

So this atlas is not complex analytic. But it can be easily made complex analytic by replacing one of the stereographic projections  $(\phi \text{ or } \psi)$  by its complex conjugate. Then we will have  $f(z) = \frac{1}{z}$ . On the other hand, it is known (although hard to prove) that  $S^n$  does not admit a complex analytic atlas for (even)  $n \neq 2, 6$ . For n = 6 this is a famous conjecture.

**Definition 1.7.** Two  $C^k$ , real analytic, or complex analytic atlases  $U_{\alpha}, V_{\beta}$  are said to be **compatible** if the transition maps between  $U_{\alpha}$  and  $V_{\beta}$  are of the same class  $(C^k, \text{ real analytic}, \text{ or complex analytic})$ .

It is clear that compatibility is an equivalence relation.

Definition 1.8. A  $C^k$ , real analytic, or complex analytic structure on a topological manifold X is an equivalence class of  $C^k$ , real analytic, or complex analytic atlases. If X is equipped with such a structure, it is said to be a  $C^k$ , real analytic, or complex analytic manifold. Complex analytic manifolds are also called **complex manifolds**, and a  $C^{\infty}$ -manifold is also called **smooth**. A **diffeomorphism** (or **isomorphism**) between such manifolds is a homeomorphism which respects the corresponding classes of atlases.

Remark 1.9. This is really a structure and not a property. For example, consider  $X = \mathbb{C}$  and  $Y = D \subset \mathbb{C}$  the open unit disk, with the usual complex coordinate z. It is easy to see that X, Y are isomorphic as real analytic manifolds. But they are not isomorphic as complex analytic manifolds: a complex isomorphism would be a holomorphic function  $f : \mathbb{C} \to D$ , hence bounded, but by Liouville's theorem any bounded holomorphic function on  $\mathbb{C}$  is a constant. Thus we have two different complex structures on  $\mathbb{R}^2$  (Riemann showed that there are no others). Also, it is true, but much harder to show, that there are uncountably many different smooth structures on  $\mathbb{R}^4$ , and there are 28 (oriented) smooth structures on  $S^7$ .

Note that the Cartesian product  $X \times Y$  of manifolds X, Y is naturally a manifold (of the same regularity type) of dimension dim  $X + \dim Y$ .

**Exercise 1.10.** Let  $f_1, ..., f_m$  be functions  $\mathbb{R}^n \to \mathbb{R}$  which are  $C^k$  or real analytic. Let  $X \subset \mathbb{R}^n$  be the set of points P such that  $f_i(P) = 0$  for all i and  $df_i(P)$  are linearly independent. Use the implicit function theorem to show that X is a topological manifold of dimension n-m and equip it with a natural  $C^k$ , respectively real analytic structure. Prove the analogous statement for holomorphic functions  $\mathbb{C}^n \to \mathbb{C}$ , namely that in this case X is naturally a complex manifold of (complex) dimension n-m

1.4. **Regular functions.** Now let  $P \in X$  and  $(U, \phi)$  be a local chart such that  $P \in U$  and  $\phi(P) = 0$ . Such a chart is called a **coordinate chart** around P. In particular, we have **local coordinates**  $x_1, ..., x_n : U \to \mathbb{R}$  (or  $U \to \mathbb{C}$  for complex manifolds), which are just the components of  $\phi$ , i.e.,  $\phi(Q) = (x_1(Q), ..., x_n(Q))$ . Note that  $x_i(P) = 0$ , and  $x_i(Q)$  determine Q if  $Q \in U$ .

**Definition 1.11.** A regular function on an open set  $V \subset X$  in a  $C^k$ , real analytic, or complex analytic manifold X is a function  $f: V \to \mathbb{R}, \mathbb{C}$  such that  $f \circ \phi_{\alpha}^{-1}: \phi_{\alpha}(V \cap U_{\alpha}) \to \mathbb{R}, \mathbb{C}$  is of the corresponding regularity class, for some (and then any) atlas  $(U_{\alpha}, \phi_{\alpha})$  defining the corresponding structure on X.

In other words, f is regular if it is expressed as a regular function in local coordinates near every point of V. Clearly, this is independent on the choice of coordinates.

The space (in fact, algebra) of regular functions on V will be denoted by O(V).

**Definition 1.12.** Let V, U be neighborhoods of  $P \in X$ . Let us say that  $f \in O(V)$ ,  $g \in O(U)$  are **equal near** P if there exists a neighborhood  $W \subset U \cap V$  of P such that  $f|_W = g|_W$ .

It is clear that this is an equivalence relation.

**Definition 1.13.** A **germ** of a regular function at P is an equivalence class of regular functions defined on neighborhoods of P which are equal near P.

The algebra of germs of regular functions at P is denoted by  $O_P$ . Thus we have  $O_P = \varinjlim O(U)$ , where the direct limit is taken over neighborhoods of P.

1.5. **Tangent spaces.** From now on we will only consider smooth, real analytic and complex analytic manifolds. By a **derivation at** P we will mean a linear map  $D: O_P \to \mathbb{R}$  in the smooth and real analytic case and  $D: O_P \to \mathbb{C}$  in the complex analytic case, satisfying the Leibniz rule

(1.1) 
$$D(fg) = D(f)g(P) + f(P)D(g).$$

Note that for any such D we have D(1) = 0.

Let  $T_PX$  be the space of all such derivations. Thus  $T_PX$  is a real vector space for smooth and real analytic manifolds and a complex vector space for complex manifolds.

**Lemma 1.14.** Let  $x_1, ..., x_n$  be local coordinates at P. Then  $T_PX$  has basis  $D_1, ..., D_n$ , where

$$D_i(f) := \frac{\partial f}{\partial x_i}(0).$$

 $<sup>^2</sup>$ More precisely, for  $C^k$  and real analytic manifolds regular functions will be assumed real-valued, unless specified otherwise. In the complex analytic case there is, of course, no choice, and regular functions are automatically complex-valued.

Proof. We may assume  $X = \mathbb{R}^n$  or  $\mathbb{C}^n$ , P = 0. Clearly,  $D_1, ..., D_n$  is a linearly independent set in  $T_PX$ . Also let  $D \in T_PX$ ,  $D(x_i) = a_i$ , and consider  $D_* := D - \sum_i a_i D_i$ . Then  $D_*(x_i) = 0$  for all i. Now given a regular function f near 0, for small  $x_1, ..., x_n$  by the fundamental theorem of calculus and the chain rule we have:

$$f(x_1, ..., x_n) = f(0) + \int_0^1 \frac{df(tx_1, ..., tx_n)}{dt} dt = f(0) + \sum_{i=1}^n x_i h_i(x_1, ..., x_n),$$

where

$$h_i(x_1,...,x_n) := \int_0^1 (\partial_i f)(tx_1,...,tx_n)dt$$

are regular near 0. So by the Leibniz rule

$$D_*(f) = \sum_{i} D_*(x_i) h_i(0, ..., 0) = 0,$$

hence 
$$D_* = 0$$
.

**Definition 1.15.** The space  $T_PX$  is called the **tangent space** to X at P. Elements  $v \in T_PX$  are called **tangent vectors** to X at P.

Observe that every tangent vector  $v \in T_PX$  defines a derivation  $\partial_v : O(U) \to \mathbb{R}, \mathbb{C}$  for every neighborhood U of P, satisfying (1.1). The number  $\partial_v f$  is called the **derivative of** f **along** v. For usual curves and surfaces in  $\mathbb{R}^3$  these coincide with the familiar notions from calculus.<sup>3</sup>

#### 1.6. Regular maps.

**Definition 1.16.** A continuous map  $F: X \to Y$  between manifolds (of the same regularity class) is **regular** if for any regular function h on an open set  $U \subset Y$  the function  $h \circ F$  on  $F^{-1}(U)$  is regular. In other words, F is regular if it is expressed by regular functions in local coordinates.

It is easy to see that the composition of regular maps is regular, and that a homeomorphism F such that F,  $F^{-1}$  are both regular is the same thing as a diffeomorphism (=isomorphism).

Let  $F: X \to Y$  be a regular map and  $P \in X$ . Then we can define the **differential** of F at  $P, d_P F$ , which is a linear map  $T_P X \to T_{F(P)} Y$ . Namely, for  $f \in O_{F(P)}$  and  $v \in T_P X$ , the vector  $d_P F \cdot v$  is defined by the formula

$$(d_P F \cdot v)(f) := v(f \circ F).$$

<sup>&</sup>lt;sup>3</sup>Note however that  $\partial_v f$  differs from the *directional derivative*  $D_v f$  defined in calculus. Namely,  $D_v f = \frac{\partial_v f}{|v|}$  (thus defined only for  $v \neq 0$ ) and depends only on the direction of v.

The differential of F is also denoted by  $F_*$ ; namely, for  $v \in T_P X$  one writes  $dF_P \cdot v = F_* v$ .

Moreover, if  $G:Y\to Z$  is another regular map, then we have the usual **chain rule**,

$$d(G \circ F)_P = dG_{F(P)} \circ dF_P.$$

In particular, if  $\gamma:(a,b)\to X$  is a regular **parametrized curve** then for  $t\in(a,b)$  we can define the **velocity vector**  $\gamma'(t)\in T_{\gamma(t)}X$  by

$$\gamma'(t) := d_t \gamma \cdot 1$$

(where  $1 \in \mathbb{R} = T_t(a, b)$ ).

# 1.7. Submersions and immersions, submanifolds.

**Definition 1.17.** A regular map of manifolds  $F: X \to Y$  is a submersion if  $dF_P: T_PX \to T_{F(P)}Y$  is surjective for all  $P \in X$ .

The following proposition is a version of the implicit function theorem for manifolds.

**Proposition 1.18.** If F is a submersion then for any  $Q \in Y$ ,  $F^{-1}(Q)$  is a manifold of dimension  $\dim X - \dim Y$ .

*Proof.* This is a local question, so it reduces to the case when X, Y are open subsets in Euclidean spaces. In this case it reduces to Exercise 1.10.

**Definition 1.19.** A regular map of manifolds  $f: X \to Y$  is an **immersion** if  $d_P F: T_P X \to T_{F(P)} Y$  is injective for all  $P \in X$ .

**Example 1.20.** The inclusion of the sphere  $S^n$  into  $\mathbb{R}^{n+1}$  is an immersion. The map  $F: S^1 \to \mathbb{R}^2$  given by

(1.2) 
$$x(t) = \frac{\cos \theta}{1 + \sin^2 \theta}, \ y(t) = \frac{\sin \theta \cos \theta}{1 + \sin^2 \theta}$$

is also an immersion; its image is the lemniscate (shaped as  $\infty$ ). This shows that an immersion need not be injective. On the other hand, the map  $F: \mathbb{R} \to \mathbb{R}^2$  given by  $F(t) = (t^2, t^3)$  parametrizing a semicubic parabola  $\prec$  is injective, but not an immersion, since F'(0) = (0, 0).

**Definition 1.21.** An immersion  $f: X \to Y$  is an **embedding** if the map  $F: X \to F(X)$  is a homeomorphism (where F(X) is equipped with the induced topology from Y). In this case,  $F(X) \subset Y$  is said to be an **(embedded) submanifold.**<sup>4</sup>

<sup>&</sup>lt;sup>4</sup>Recall that a subset Z of a topological space X is called **locally closed** if it is a closed subset in an open subset  $U \subset X$ . It is clear that embedded submanifolds

**Example 1.22.** The immersion of  $S^n$  into  $\mathbb{R}^{n+1}$  and of (0,1) into  $\mathbb{R}$  are embeddings, but the parametrization of the lemniscate by the circle given by (1.2) is not. The parametrization of the curve  $\rho$  by  $\mathbb{R}$  is also not an embedding; it is injective but the inverse is not continuous.

**Definition 1.23.** An embedding  $F: X \to Y$  of manifolds is **closed** if  $F(X) \subset Y$  is a closed subset. In this case we say that F(X) is a **closed (embedded) submanifold** of Y.

**Example 1.24.** The embedding of  $S^n$  into  $\mathbb{R}^{n+1}$  is closed but of (0,1) into  $\mathbb{R}$  is not. Also in Proposition 1.18,  $f^{-1}(Q)$  is a closed submanifold of X.

are locally closed. For this reason they are often called locally closed (embedded) submanifolds.

#### 2. Lie groups, I

# 2.1. The definition of a Lie group.

**Definition 2.1.** A  $C^k$ , real or complex analytic **Lie group** is a manifold G of the same class, with a group structure such that the multiplication map  $m: G \times G \to G$  is regular.

Thus, in a Lie group G for any  $g \in G$  the left and right translation maps  $L_q, R_q : G \to G$ ,  $L_q(x) := gx, R_q(x) := xg$ , are diffeomorphisms.

**Proposition 2.2.** In a Lie group G, the inversion map  $\iota: G \to G$  is a diffeomorphism, and  $d\iota_1 = -\mathrm{Id}$ .

*Proof.* For the first statement it suffices to show that  $\iota$  is regular near 1, the rest follows by translation. So let us pick a coordinate chart near  $1 \in G$  and write the map m in this chart in local coordinates. Note that in these coordinates,  $1 \in G$  corresponds to  $0 \in \mathbb{R}^n$ . Since m(x,0) = x and m(0,y) = y, the linear approximation of m(x,y) at 0 is x+y. Thus by the implicit function theorem, the equation m(x,y) = 0 is solved near 0 by a regular function  $y = \iota(x)$  with  $d\iota(0) = -\mathrm{Id}$ . This proves the proposition.

Remark 2.3. A  $C^0$  Lie group is a topological group which is a topological manifold. The **Hilbert 5th problem** was to show that any such group is actually a real analytic Lie group (i.e., the regularity class does not matter). This problem is solved by the deep **Gleason-Yamabe theorem**, proved in 1950s. So from now on we will not pay attention to regularity class and consider only real and complex Lie groups.

Note that any complex Lie group of dimension n can be regarded as a real Lie group of dimension 2n. Also the Cartesian product of real (complex) Lie groups is a real (complex) Lie group.

### 2.2. Homomorphisms.

**Definition 2.4.** A homomorphism of Lie groups  $f: G \to H$  is a group homomorphism which is also a regular map. An **isomorphism** of Lie groups is a homomorphism f which is a group isomorphism, such that  $f^{-1}: H \to G$  is regular.

We will see later that the last condition is in fact redundant.

#### 2.3. Examples.

**Example 2.5.** 1.  $(\mathbb{R}^n, +)$  is a real Lie group and  $(\mathbb{C}^n, +)$  is a complex Lie group (both *n*-dimensional).

- 2.  $(\mathbb{R}^{\times}, \times)$ ,  $(\mathbb{R}_{>0}, \times)$  are real Lie groups,  $(\mathbb{C}^{\times}, \times)$  is a complex Lie group (all 1-dimensional).
- 3.  $S^1 = \{z \in \mathbb{C} : |z| = 1\}$  is a 1-dimensional real Lie group under multiplication of complex numbers.

Note that  $\mathbb{R}^{\times} \cong \mathbb{R}_{>0} \times \mathbb{Z}/2$ ,  $\mathbb{C}^{\times} \cong \mathbb{R}_{>0} \times S^1$  as real Lie groups (trigonometric form of a complex number) and  $(\mathbb{R}, +) \cong (\mathbb{R}_{>0}, \times)$  via  $x \mapsto e^x$ .

- 4. The groups of invertible n by n matrices:  $GL_n(\mathbb{R})$  is a real Lie group and  $GL_n(\mathbb{C})$  is a complex Lie group. These are open sets in the corresponding spaces of all matrices and have dimension  $n^2$ .
- 5. SU(2), the special unitary group of size 2. This is the set of complex 2-by-2 matrices A such that

$$AA^{\dagger} = \mathbf{1}, \det A = 1.$$

So writing

$$A = \begin{pmatrix} a & b \\ c & d \end{pmatrix}, \quad A^{\dagger} = \begin{pmatrix} \overline{a} & \overline{c} \\ \overline{b} & \overline{d} \end{pmatrix},$$

we get

$$a\overline{a} + b\overline{b} = 1$$
,  $a\overline{c} + b\overline{d} = 0$ ,  $c\overline{c} + d\overline{d} = 1$ .

The second equation implies that  $(c,d) = \lambda(-\overline{b},\overline{a})$ . Then we have

$$1 = \det A = ad - bc = \lambda(a\overline{a} + b\overline{b}) = \lambda,$$

so  $\lambda = 1$ . Thus SU(2) is identified with the set of  $(a, b) \in \mathbb{C}^2$  such that  $a\overline{a} + b\overline{b} = 1$ . Writing a = x + iy, b = z + it, we have

$$SU(2) = \{(x, y, z, t) \in \mathbb{R}^4 : x^2 + y^2 + z^2 + t^2 = 1\}.$$

Thus SU(2) is a 3-dimensional real Lie group which as a manifold is the 3-dimensional sphere  $S^3 \subset \mathbb{R}^4$ .

- 6. Any countable group G with **discrete topology** (i.e., such that every set is open) is a (real and complex) Lie group.
- 2.4. The connected component of 1. Recall:
- A topological space X is **path-connected** if for any  $P, Q \in X$  there is a continuous map  $x : [0,1] \to X$  such that x(0) = P, x(1) = Q (such x is called **a path connecting** P **to** Q).
- If X is any topological space, then for  $P \in X$  we can define its **path-connected component** to be the set  $X_P$  of  $Q \in X$  for which there is a path connecting P to Q. Then  $X_P$  is the largest path-connected subset of X containing P. Clearly, the relation that Q belongs to  $X_P$  is an equivalence relation, which splits X into equivalence classes called **path-connected components**. The set of such components is denoted  $\pi_0(X)$ .

- A topological space X is **connected** if the only subsets of X that are both open and closed are  $\emptyset$  and X. For  $P \in X$ , the **connected component** of X is the union  $X^P$  of all connected subsets of X containing P, which is obviously connected itself (so it is the largest connected subset of X containing P). A path-connected space X is always connected but not vice versa (the classic counterexample is the graph of the function  $y = \sin(\frac{1}{x})$  together with the interval [-1,1] of the y-axis); however, a connected manifold is path-connected (show it!), so for manifolds the notions of connected component and path-connected component coincide.
- If Y is a topological space, X is a set and  $p: Y \to X$  is a surjective map (i.e.,  $X = Y / \sim$  is the quotient of Y by an equivalence relation) then X acquires a topology called the **quotient topology**, in which open sets are subsets  $V \subset X$  such that  $p^{-1}(V)$  is open.

Now let G be a real or complex Lie group, and  $G^{\circ}$  the connected component of  $1 \in G$ . Then the connected component of any  $g \in G$  is  $gG^{\circ}$ .

**Proposition 2.6.** (i)  $G^{\circ}$  is a normal subgroup of G.

- (ii)  $\pi_0(G) = G/G^{\circ}$  with quotient topology is a discrete and countable group.
- *Proof.* (i) Let  $g \in G$ ,  $a \in G^{\circ}$ , and  $x : [0,1] \to G$  be a path connecting 1 to a. Then  $gxg^{-1}$  is a path connecting 1 to  $gag^{-1}$ , so  $gag^{-1} \in G^{\circ}$ , hence  $G^{\circ}$  is normal.
- (ii) Since G is a manifold, for any  $g \in G$ , there is a neighborhood of g contained in  $G_g = gG^{\circ}$ . This implies that any coset of  $G^{\circ}$  in G is open, hence  $G/G^{\circ}$  is discrete. Also  $G/G^{\circ}$  is countable since G has a countable base.

Thus we see that any Lie group is an extension of a discrete countable group by a connected Lie group. This essentially reduces studying Lie groups to studying connected Lie groups. In fact, one can further reduce to simply connected Lie groups, which is done in the next subsections.

#### 3. Lie groups, II

3.1. A crash course on coverings. Now we need to review some more topology. Let X, Y be Hausdorff topological spaces, and  $p: Y \to X$  a continuous map. Then p is called a **covering** if every point  $x \in X$  has a neighborhood U such that  $p^{-1}(U)$  is a union of disjoint open sets (called **sheets** of the covering) each of which is mapped homeomorphically onto U by p:

In other words, there exists a homeomorphism  $h: U \times F \to p^{-1}(U)$  for some discrete space F with  $(p \circ h)(u, f) = u$  for all  $u \in U$ ,  $f \in F$ . I.e., informally speaking, a covering is a map that locally on X looks like the projection  $X \times F \to X$  for some discrete F.

We will consider only coverings with countable fibers, and just call them coverings. It is clear that a covering of a manifold ( $C^k$ , real or complex analytic) is a manifold of the same type, and the covering map is regular.

Two paths  $x_0, x_1 : [0,1] \to X$  such that  $x_i(0) = P, x_i(1) = Q$  are said to be **homotopic** if there is a continuous map

$$x:[0,1]\times[0,1]\to X,$$

called a **homotopy** between  $x_0$  and  $x_1$ , such that  $x(t,0) = x_0(t)$  and  $x(t,1) = x_1(t)$ , x(0,s) = P, x(1,s) = Q. See a movie here: https://commons.wikimedia.org/wiki/File:Homotopy.gif#/media/File:HomotopySmall.gif

For example, if x(t) is a path and  $g:[0,1] \to [0,1]$  is a change of parameter with g(0) = 0, g(1) = 1 then the paths  $x_1(t) = x(t)$  and  $x_2(t) = x(g(t))$  are clearly homotopic.

A path-connected Hausdorff space X is said to be **simply connected** if for any  $P, Q \in X$ , any paths  $x_0, x_1 : [0, 1] \to X$  such that  $x_i(0) = P, x_i(1) = Q$  are homotopic.

**Example 3.1.**  $S^1$  is not simply connected but  $S^n$  is simply connected for  $n \geq 2$ .

It is easy to show that any covering has a **homotopy lifting property**: if  $b \in X$  and  $\tilde{b} \in p^{-1}(b) \subset Y$  then any path  $\gamma$  starting at b admits a unique lift to a path  $\tilde{\gamma}$  starting at  $\tilde{b}$ , i.e.,  $p(\tilde{\gamma}) = \gamma$ . Moreover, if  $\gamma_1, \gamma_2$  are homotopic paths on X then  $\tilde{\gamma}_1, \tilde{\gamma}_2$  are homotopic on Y (in particular, have the same endpoint). Thus, if Z is a simply connected space with a point z then any continuous map  $f: Z \to X$  with f(z) = b lifts to a unique continuous map  $\tilde{f}: Z \to Y$  satisfying  $\tilde{f}(z) = \tilde{b}$ ; i.e.,  $p \circ \tilde{f} = f$ . Namely, to compute  $\tilde{f}(w)$ , pick a path  $\beta$  from z to w, let  $\gamma = f(\beta)$  and consider the path  $\tilde{\gamma}$ . Then the endpoint of  $\tilde{\gamma}$  is  $\tilde{f}(w)$ , and it does not depend on the choice of  $\beta$ .

If Z, X are manifolds (of any regularity type), Z is simply connected, and  $f: Z \to X$  is a regular map then the lift  $\widetilde{f}: Z \to Y$  is also regular. Indeed, if we introduce local coordinates on Y using the homeomorphism between sheets of the covering and their images then  $\widetilde{f}$  and f will be locally expressed by the same functions.

A covering  $p: Y \to X$  of a path-connected space X is called **universal** if Y is simply connected.

If X is a sufficiently nice space, e.g., a manifold, its universal covering can be constructed as follows. Fix  $b \in X$  and let  $\widetilde{X}_b$  be the set of homotopy classes of paths on X starting at b. We have a natural map  $p: \widetilde{X}_b \to X$ ,  $p(\gamma) = \gamma(1)$ . If  $U \subset X$  is a small ball around a point  $x \in X$  then U is simply connected, so we have a natural identification  $h: U \times F \to p^{-1}(U)$  with  $(p \circ h)(u, f) = u$ , where  $F = p^{-1}(x)$  is the set of homotopy classes of paths from b to x; namely, h(u, f) is the concatenation of f with any path connecting x with u inside U.

Here the **concatenation**  $\gamma_1 \circ \gamma_2$  of paths  $\gamma_1, \gamma_2 : [0, 1] \to X$  with  $\gamma_2(1) = \gamma_1(0)$  is the path  $\gamma = \gamma_1 \circ \gamma_2 : [0, 1] \to X$  such that  $\gamma(t) = \gamma_2(2t)$  for  $t \leq 1/2$  and  $\gamma(t) = \gamma_1(2t-1)$  for  $t \geq 1/2$ .

The topologies on all such  $p^{-1}(U)$  induced by these identifications glue together into a topology on  $\widetilde{X}_b$ , and the map  $p:\widetilde{X}_b\to X$  is then a covering. Moreover, the homotopy lifting property implies that  $\widetilde{X}_b$  is simply connected, so this covering is universal.

It is easy to see that a universal covering  $p: Y \to X$  covers any pathconnected covering  $p': Y' \to X$ , i.e., there is a covering  $q: Y \to Y'$ such that  $p = p' \circ q$ ; this is why it is called universal. Therefore a universal covering is unique up to an isomorphism (indeed, if Y, Y' are universal then we have coverings  $q_1: Y \to Y'$  and  $q_2: Y' \to Y$  and  $q_1 \circ q_2 = q_2 \circ q_1 = \mathrm{Id}$ ).

**Example 3.2.** 1. The map  $z \mapsto z^n$  defines an *n*-sheeted covering  $S^1 \to S^1$ .

2. The map  $x \to e^{ix}$  defines the universal covering  $\mathbb{R} \to S^1$ .

Now denote by  $\pi_1(X,x)$  the set of homotopy classes of *closed* paths on a path-connected space X, starting and ending at x. Then  $\pi_1(X,x)$  is a group under concatenation of paths (concatenation is associative since the paths a(bc) and (ab)c differ only by parametrization and are hence homotopic). This group is called the **fundamental group** of X relative to the point x. It acts on the fiber  $p^{-1}(x)$  for every covering  $p: Y \to X$  (by lifting  $\gamma \in \pi_1(X,x)$  to Y), which is called the action by **deck transformations**. This action is transitive iff Y is path-connected and moreover free iff Y is universal.

Finally, the group  $\pi_1(X, x)$  does not depend on x up to an isomorphism. More precisely, conjugation by any path from  $x_1$  to  $x_2$  defines an isomorphism  $\pi_1(X, x_1) \to \pi_1(X, x_2)$  (although two non-homotopic paths may define different isomorphisms if  $\pi_1$  is non-abelian).

**Example 3.3.** 1.  $\pi_1(S^1) = \mathbb{Z}$ .

- 2.  $\pi_1(\mathbb{C} \setminus \{z_1, ..., z_n\}) = F_n$  is a free group in n generators.
- 3. We have a 2-sheeted universal covering  $S^n \to \mathbb{RP}^n$  (real projective space) for  $n \geq 2$ . Thus  $\pi_1(\mathbb{RP}^n) = \mathbb{Z}/2$  for  $n \geq 2$ .

Exercise 3.4. Make sure you can fill all the details in this subsection!

3.2. Coverings of Lie groups. Let G be a connected (real or complex) Lie group and  $\widetilde{G} = \widetilde{G}_1$  be the universal covering of G, consisting of homotopy classes of paths  $x : [0,1] \to G$  with x(0) = 1. Then  $\widetilde{G}$  is a group via  $(x \cdot y)(t) = x(t)y(t)$ , and also a manifold.

**Proposition 3.5.** (i)  $\widetilde{G}$  is a simply connected Lie group. The covering  $p: \widetilde{G} \to G$  is a homomorphism of Lie groups.

(ii)  $\operatorname{Ker}(p)$  is a central subgroup of  $\widetilde{G}$  naturally isomorphic to  $\pi_1(G) = \pi_1(G,1)$ . Thus,  $\widetilde{G}$  is a central extension of G by  $\pi_1(G)$ . In particular,  $\pi_1(G)$  is abelian.

*Proof.* We will only prove (i). We only need to show that  $\widetilde{G}$  is a Lie group, i.e., that the multiplication map  $\widetilde{m}: \widetilde{G} \times \widetilde{G} \to \widetilde{G}$  is regular. But  $\widetilde{G} \times \widetilde{G}$  is simply connected, and  $\widetilde{m}$  is a lifting of the map

$$m' := m \circ (p \times p) : \widetilde{G} \times \widetilde{G} \to G \times G \to G,$$

so it is regular. In other words,  $\widetilde{m}$  is regular since in local coordinates it is defined by the same functions as m.

Exercise 3.6. Prove Proposition 3.5(ii).

Remark 3.7. The same argument shows that more generally, the fundamental group of any path-connected topological group is abelian.

**Example 3.8.** 1. The map  $z \mapsto z^n$  defines an *n*-sheeted covering of Lie groups  $S^1 \to S^1$ .

2. The map  $x \to e^{ix}$  defines the universal covering of Lie groups  $\mathbb{R} \to S^1$ .

**Exercise 3.9.** Consider the action of SU(2) on the 3-dimensional real vector space of traceless Hermitian 2-by-2 matrices by conjugation.

- (i) Show that this action preserves the positive inner product (A, B) = Tr(AB) and has determinant 1. Deduce that it defines a homomorphism  $\phi: SU(2) \to SO(3)$ .
- (ii) Show that  $\phi$  is surjective, with kernel  $\pm 1$ , and is a universal covering map (use that  $SU(2) = S^3$  is simply connected). Deduce that  $\pi_1(SO(3)) = \mathbb{Z}/2$  and that  $SO(3) \cong \mathbb{RP}^3$  as a manifold.

This is demonstrated by the famous **Dirac belt trick**, which illustrates the notion of a **spinor**; namely, spinors are vectors in  $\mathbb{C}^2$  acted upon by matrices from SU(2). Here are some videos of the belt trick:

https://www.youtube.com/watch?v=17Q0tJZcsnY https://www.youtube.com/watch?v=Vfh21o-JW9Q

#### 3.3. Closed Lie subgroups.

**Definition 3.10.** A closed Lie subgroup of a (real or complex) Lie group G is a subgroup which is also an embedded submanifold.

This terminology is justified by the following lemma.

**Lemma 3.11.** A closed Lie subgroup of G is closed in G.

# Exercise 3.12. Prove Lemma 3.11.

We also have

**Theorem 3.13.** Any closed subgroup of a real Lie group G is a closed Lie subgroup.

This theorem is rather nontrivial, and we will not prove it at this time (it will be proved much later in Exercise 36.13), but we will soon prove a weaker version which suffices for our purposes.

**Example 3.14.** 1.  $SL_n(\mathbb{K})$  is a closed Lie subgroup of  $GL_n(\mathbb{K})$  for  $\mathbb{K} = \mathbb{R}$ ,  $\mathbb{C}$ . Indeed, the equation det A = 1 defines a smooth hypersurface in the space of matrices (show it!).

2. Let  $\phi : \mathbb{R} \to S^1 \times S^1$  be the irrational torus winding given by the formula  $\phi(x) = (e^{ix}, e^{ix\sqrt{2}})$ :

Then  $\phi(\mathbb{R})$  is a subgroup of  $S^1 \times S^1$  but not a closed Lie subgroup, since it is not an embedded submanifold: although  $\phi$  is an immersion, the map  $\phi^{-1}:\phi(\mathbb{R})\to\mathbb{R}$  is not continuous.

# 3.4. Generation of connected Lie groups by a neighborhood of the identity.

**Proposition 3.15.** (i) If G is a connected Lie group and U a neighborhood of 1 in G then U generates G.

(ii) If  $f: G \to K$  is a homomorphism of Lie groups, K is connected, and  $df_1: T_1G \to T_1K$  is surjective, then f is surjective.

*Proof.* (i) Let H be the subgroup of G generated by U. Then H is open in G since  $H = \bigcup_{h \in H} hU$ . Thus H is an embedded submanifold of G, hence a closed Lie subgroup. Thus by Lemma 3.11  $H \subset G$  is closed. So H = G since G is connected.

(ii) Since  $df_1$  is surjective, by the implicit function theorem f(G) contains some neighborhood of 1 in K. Thus it contains the whole K by (i).

# 4. Homogeneous spaces, Lie group actions

4.1. Homogeneous spaces. A regular map of manifolds  $p: Y \to X$  is a said to be a **locally trivial fibration** (or **fiber bundle**) with **base** X, **total space** Y and **fiber** being a manifold F if every point  $x \in X$  has a neighborhood U such that there is a diffeomorphism  $h: U \times F \cong p^{-1}(U)$  with  $(p \circ h)(u, f) = u$ . In other words, locally p looks like the projection  $X \times F \to X$  (the trivial fiber bundle with fiber F over X), but not necessarily globally so. This generalizes the notion of a covering, in which case F is 0-dimensional (discrete).

**Theorem 4.1.** (i) Let G be a Lie group of dimension n and  $H \subset G$  a closed Lie subgroup of dimension k. Then the **homogeneous space** G/H has a natural structure of an n-k-dimensional manifold, and the map  $p: G \to G/H$  is a locally trivial fibration with fiber H.

- (ii) If moreover H is normal in G then G/H is a Lie group.
- (iii) We have a natural isomorphism  $T_1(G/H) \cong T_1G/T_1H$ .

Proof. Let  $\overline{g} \in G/H$  and  $g \in p^{-1}(\overline{g})$ . Then  $gH \subset G$  is an embedded submanifold (image of H under left translation by g). Pick a sufficiently small transversal submanifold U passing through g (i.e.,  $T_qG = T_q(gH) \oplus T_qU$ ).

By the inverse function theorem, the set UH is open in G. Let  $\overline{U}$  be the image of UH in G/H. Since  $p^{-1}(\overline{U}) = UH$  is open,  $\overline{U}$  is open in the quotient topology. Also it is clear that  $p: U \to \overline{U}$  is a homeomorphism. This defines a local chart near  $\overline{g} \in G/H$ , and it is easy to check that transition maps between such charts are regular. So G/H acquires the structure of a manifold, which is easily checked to be independent on the choices we made. Also the multiplication map  $U \times H \to UH$  is a diffeomorphism, which implies that  $p: G \to G/H$  is a locally trivial fibration with fiber H. Finally, we have a surjective linear map  $T_gG \to T_{\overline{g}}G/H$  whose kernel is  $T_g(gH)$ . So in particular for g=1 we get  $T_1(G/H) \cong T_1G/T_1H$ . This proves all parts of the proposition.

Recall that a sequence of group homomorphisms  $d_i: C^i \to C^{i+1}$  is a **complex** if for all  $i, d_i \circ d_{i-1}$  is the trivial homomorphism  $C^{i-1} \to C^{i+1}$ . (One may consider finite complexes, semi-infinite to the left or to the right, or infinite in both directions). In this case  $\operatorname{Im}(d_{i-1}) \subset \operatorname{Ker}(d_i)$  is a subgroup. The i-th **cohomology**  $H^i(C^{\bullet})$  of the complex  $C^{\bullet}$  is the quotient  $\operatorname{Ker}(d_i)/\operatorname{Im}(d_{i-1})$ . In general it is just a set but if  $C^i$  are abelian groups, it is also an abelian group. Also recall that a complex  $C^{\bullet}$  is called **exact** in the i-th term if  $\operatorname{Ker}(d_i) = \operatorname{Im}(d_{i-1})$ , i.e., if  $H^i(C^{\bullet})$  is trivial (consists of one element). A complex exact in all its terms (except possibly first and last, where this condition makes no sense) is called an **exact sequence**.

Corollary 4.2. Let  $H \subset G$  be a closed Lie subgroup.

- (i) If H is connected then the map  $p_0: \pi_0(G) \to \pi_0(G/H)$  is a bijection.
  - (ii) If also G is connected then there is an exact sequence

$$\pi_1(H) \to \pi_1(G) \to \pi_1(G/H) \to 1.$$

*Proof.* This follows from the theory of covering spaces using that  $p: G \to G/H$  is a fibration.

Exercise 4.3. Fill in the details in the proof of Corollary 4.2.

Remark 4.4. The sequence in Corollary 4.2(ii) is the end portion of the infinite long exact sequence of homotopy groups of a fibration,

... 
$$\rightarrow \pi_i(H) \rightarrow \pi_i(G) \rightarrow \pi_i(G/H) \rightarrow \pi_{i-1}(H) \rightarrow ...,$$

where  $\pi_i(X)$  is the *i*-th homotopy group of X.

4.2. **Lie subgroups.** We will call the image of an injective immersion of manifolds **an immersed submanifold**; it has a manifold structure coming from the source of the immersion.

**Definition 4.5.** A **Lie subgroup** of a Lie group G is a subgroup H which is also an immersed submanifold (but need not be an embedded submanifold, nor a closed subset).

It is clear that in this case H is still a Lie group and the inclusion  $H \hookrightarrow G$  is a homomorphism of Lie groups.

**Example 4.6.** 1. The winding of a torus in Example 3.14(2) realizes  $\mathbb{R}$  as a Lie subgroup of  $S^1 \times S^1$  which is not closed.

2. Any countable subgroup of G is a 0-dimensional Lie subgroup, but not always a closed one (e.g.,  $\mathbb{Q} \subset \mathbb{R}$ ).

**Proposition 4.7.** Let  $f: G \to K$  be a homomorphism of Lie groups. Then  $H := \operatorname{Ker} f$  is a closed normal Lie subgroup in G and  $\operatorname{Im} f$  is a Lie subgroup in K, closed if and only if it is an embedded submanifold. In the latter case, we have an isomorphism of Lie groups  $G/H \cong \operatorname{Im} f$ .

We will prove Proposition 4.7 in Subsection 9.1.

4.3. Actions and representations of Lie groups. Let X be a manifold, G a Lie group, and  $a: G \times X \to X$  a set-theoretical left action of G on X.

**Definition 4.8.** This action is called **regular** if the map a is regular.

From now on, by an action of G on X we will always mean a regular action.

**Example 4.9.** 1. Any Lie subgroup of  $GL_n(\mathbb{R})$  acts on  $\mathbb{R}^n$  by linear transformations. Likewise, any Lie subgroup of  $GL_n(\mathbb{C})$  acts on  $\mathbb{C}^n$ . 2. SO(3) acts on  $S^2$  by rotations.

Definition 4.10. A (real analytic) finite dimensional representation of a real Lie group G is a linear action of G on a finite dimensional vector space V over  $\mathbb{R}$  or  $\mathbb{C}$ . Similarly, a (complex analytic) finite dimensional representation of a *complex* Lie group G is a linear action of G on a finite dimensional vector space V over  $\mathbb{C}$ .

In other words, a representation is a homomorphism of Lie groups  $\pi_V: G \to GL(V).$ 

Definition 4.11. A (homo)morphism of representations (or in**tertwining operator**)  $A:V\to W$  is a linear map which commutes with the G-action, i.e.,  $A\pi_V(g) = \pi_W(g)A$ ,  $g \in G$ . In particular, if V = W, such A is called an **endomorphism** of V.

As usual, an **isomorphism of representations** is an invertible morphism. With these definitions, finite dimensional representations of G form a category.

Note also that we have the operations of dual and tensor product on representations. Namely, given a representation V of G, we can define its representation on the dual space  $V^*$  by

$$\pi_{V^*}(g) = \pi_V(g^{-1})^*,$$

and if W is another representation of G then we can define a representation of G on  $V \otimes W$  (the tensor product of vector spaces) by

$$\pi_{V\otimes W}(g) = \pi_V(g) \otimes \pi_W(g).$$

Also if  $V \subset W$  is a **subrepresentation** (i.e., a subspace invariant under G) then W/V is also a representation of G, called the **quotient representation**.

4.4. **Orbits and stabilizers.** As in ordinary group theory, if G acts on X and  $x \in X$  then we can define the **orbit**  $Gx \subset X$  of x as the set of gx,  $g \in G$ , and the **stabilizer**, or **isotropy group**  $G_x \subset G$  to be the group of  $g \in G$  such that gx = x.

**Proposition 4.12.** (The orbit-stabilizer theorem for Lie group actions) The stabilizer  $G_x \subset G$  is a closed Lie subgroup, and the natural map  $G/G_x \to X$  is an injective immersion whose image is G.

Proposition 4.12 will be proved in Subsection 9.1.

**Corollary 4.13.** The orbit  $Gx \subset X$  is an immersed submanifold, and we have a natural isomorphism  $T_x(Gx) \cong T_1G/T_1G_x$ . If Gx is an embedded submanifold then the map  $G/G_x \to Gx$  is a diffeomorphism.

**Remark 4.14.** Note that Gx need not be closed in X. E.g., let  $\mathbb{C}^{\times}$  act on  $\mathbb{C}$  by multiplication. The orbit of 1 is  $\mathbb{C}^{\times} \subset \mathbb{C}$ , which is not closed.

**Example 4.15.** Suppose that G acts on X transitively. Then we get that  $X \cong G/G_x$  for any  $x \in X$ , i.e., X is a **homogeneous space**.

**Corollary 4.16.** If G acts transitively on X then the map  $p: G \to X$  given by p(g) = gx is a locally trivial fibration with fiber  $G_x$ .

**Example 4.17.** 1. SO(3) acts transitively on  $S^2$  by rotations,  $G_x = S^1 = SO(2)$ , so  $S^2 = SO(3)/S^1$ . Thus  $SO(3) = \mathbb{RP}^3$  fibers over  $S^2$  with fiber  $S^1$ .

2. SU(2) acts on  $S^2 = \mathbb{CP}^1$ , and the stabilizer is  $S^1 = U(1)$ . Thus  $SU(2)/S^1 = S^2$ , and  $SU(2) = S^3$  fibers over  $S^2$  with fiber  $S^1$  (the **Hopf fibration**). Here is D. Richter's keyring model of the Hopf fibration:

3. Let  $\mathbb{K} = \mathbb{R}$  or  $\mathbb{C}$  and  $\mathcal{F}_n(\mathbb{K})$  the set of flags  $0 \subset V_1 \subset ... \subset V_n = \mathbb{K}^n$  (dim  $V_i = i$ ). Then  $G = GL_n(\mathbb{K})$  acts transitively on  $\mathcal{F}_n(\mathbb{K})$  (check it!). Also let  $P \in \mathcal{F}_n(\mathbb{K})$  be the flag for which  $V_i = \mathbb{K}^i$  is the subspace of vectors whose all coordinates but the first i are zero. Then  $G_P$  is the subgroup  $B_n(\mathbb{K}) \subset GL_n(\mathbb{K})$  of invertible upper triangular matrices.

Thus  $\mathcal{F}_n(\mathbb{K}) = GL_n(\mathbb{K})/B_n(\mathbb{K})$  is a homogeneous space of  $GL_n(\mathbb{K})$ , in particular, a  $\mathbb{K}$ -manifold. It is called the **flag manifold**.

4.5. Left translation, right translation, and adjoint action. Recall that a Lie group G acts on itself by left translations  $L_g(x) = gx$  and right translations  $R_{g^{-1}}(x) = xg^{-1}$  (note that both are left actions).

**Definition 4.18.** The **adjoint action**  $\mathrm{Ad}_g: G \to G$  is the action  $\mathrm{Ad}_g = L_g \circ R_{g^{-1}} = R_{g^{-1}} \circ L_g$ ; i.e.,  $\mathrm{Ad}_g(x) = gxg^{-1}$ .

Note this is an action by (inner) automorphisms. Also since  $\mathrm{Ad}_g(1) = 1$ , we have a linear map  $d_1\mathrm{Ad}_g : \mathfrak{g} \to \mathfrak{g}$ , where  $\mathfrak{g} = T_1G$ . We will abuse notation and denote this map just by  $\mathrm{Ad}_g$ . This defines a representation of G on  $\mathfrak{g}$  called the **adjoint representation**.

# 5. Tensor fields

5.1. A crash course on vector bundles. Let X be a real manifold. A vector bundle on X is, informally speaking, a (locally trivial) fiber bundle on X whose fibers are finite dimensional vector spaces. In other words, it is a family of vector spaces parametrized by  $x \in X$  and varying regularly with x. More precisely, we have the following definition.

Let  $\mathbb{K} = \mathbb{R}$  or  $\mathbb{C}$ .

**Definition 5.1.** A  $\mathbb{K}$ -vector bundle of rank n on X is a manifold E with a surjective regular map  $p: E \to X$  and a  $\mathbb{K}$ -vector space structure on each fiber  $p^{-1}(x)$  such that every  $x \in X$  has a neighborhood U admitting a diffeomorphism  $g: U \times \mathbb{K}^n \to p^{-1}(U)$  with the following properties:

- (i)  $(p \circ g)(u, v) = u$ , and
- (ii) the map g is  $\mathbb{K}$ -linear on the second factor.

In other words, locally on X, E is isomorphic to  $X \times \mathbb{K}^n$ , but not necessarily globally so.

As for ordinary fiber bundles, E is called the **total space** and X the **base** of the bundle.

Note that even if X is a complex manifold and  $\mathbb{K} = \mathbb{C}$ , E need not be a complex manifold.

**Definition 5.2.** A complex vector bundle  $p: E \to X$  on a complex manifold X is said to be **holomorphic** if E is a complex manifold and the diffeomorphisms  $g_U$  can be chosen holomorphic.

From now on, unless specified otherwise, all complex vector bundles on complex manifolds we consider will be holomorphic.

It follows from the definition that if  $p: E \to X$  is a vector bundle then X has an open cover  $\{U_{\alpha}\}$  such that E trivializes on each  $U_{\alpha}$ , i.e., there is a diffeomorphism  $g_{\alpha}: U_{\alpha} \times \mathbb{K}^{n} \to p^{-1}(U_{\alpha})$  as above. In this case we have **clutching functions** 

$$h_{\alpha\beta}: U_{\alpha} \cap U_{\beta} \to GL_n(\mathbb{K})$$

(holomorphic if E is a holomorphic bundle), defined by the formula

$$(g_{\alpha}^{-1} \circ g_{\beta})(x, v) = (x, h_{\alpha\beta}(x)v)$$

which satisfy the consistency conditions

$$h_{\alpha\beta}(x) = h_{\beta\alpha}(x)^{-1}$$

and

$$h_{\alpha\beta}(x) \circ h_{\beta\gamma}(x) = h_{\alpha\gamma}(x)$$

for  $x \in U_{\alpha} \cap U_{\beta} \cap U_{\gamma}$ . Moreover, the bundle can be reconstructed from this data, starting from the disjoint union  $\sqcup_{\alpha} U_{\alpha} \times \mathbb{K}^{n}$  and identifying (gluing) points according to

$$h_{\alpha\beta}:(x,v)\in U_{\beta}\times\mathbb{K}^n\sim(x,h_{\alpha\beta}(x)v)\in U_{\alpha}\times\mathbb{K}^n.$$

The consistency conditions ensure that the relation  $\sim$  is symmetric and transitive, so it is an equivalence relation, and we define E to be the space of equivalence classes with the quotient topology. Then E has a natural structure of a vector bundle on X.

This can also be used for constructing vector bundles. Namely, the above construction defines a  $\mathbb{K}$ -vector bundle on X once we are given a cover  $\{U_{\alpha}\}$  on X and a collection of clutching functions

$$h_{\alpha\beta}: U_{\alpha} \cap U_{\beta} \to GL_n(\mathbb{K})$$

satisfying the consistency conditions.

**Remark 5.3.** All this works more generally for non-linear fiber bundles if we drop the linearity conditions along fibers.

**Example 5.4.** 1. The **trivial bundle**  $p: E = X \times \mathbb{K}^n \to X, p(x, v) = x.$ 

2. The **tangent bundle** is the vector bundle  $p: TX \to X$  constructed as follows. For the open cover we take an atlas of charts  $(U_{\alpha}, \phi_{\alpha})$  with transition maps

$$\theta_{\alpha\beta} = \phi_{\alpha} \circ \phi_{\beta}^{-1} : \phi_{\beta}(U_{\alpha} \cap U_{\beta}) \to \phi_{\alpha}(U_{\alpha} \cap U_{\beta}),$$

and we set

$$h_{\alpha\beta}(x) := d_{\phi_{\beta}(x)}\theta_{\alpha\beta}.$$

(Check that these maps satisfy consistency conditions!)

Thus the tangent bundle TX is a vector bundle of rank dim X whose fiber  $p^{-1}(x)$  is naturally the tangent space  $T_xX$  (indeed, the tangent vectors transform under coordinate changes exactly by multiplication by  $h_{\alpha\beta}(x)$ ). In other words, it formalizes the idea of "the tangent space  $T_xX$  varying smoothly with  $x \in X$ ".

**Definition 5.5.** A section of a map  $p: E \to X$  is a map  $s: X \to E$  such that  $p \circ s = \mathrm{Id}_x$ .

**Example 5.6.** If  $p: X \times Y = E \to X$ , p(x,y) = x is the trivial bundle then a section  $s: X \to E$  is given by s(x) = (x, f(x)) where y = f(x) is a function  $X \to Y$ , and the image of s is the graph of f. So the notion of a section is a generalization of the notion of a function.

In particular, we may consider sections of a vector bundle  $p: E \to X$  over an open set  $U \subset X$ . These sections form a vector space denoted  $\Gamma(U, E)$ .

**Exercise 5.7.** Show that a vector bundle  $p: E \to X$  is trivial (i.e., globally isomorphic to  $X \times \mathbb{K}^n$ ) if and only if it admits sections  $s_1, ..., s_n$  which form a basis in every fiber  $p^{-1}(x)$ .

### 5.2. Vector fields.

**Definition 5.8.** A vector field on X is a section of the tangent bundle TX.

Thus in local coordinates a vector field looks like

$$\mathbf{v} = \sum_{i} v_i \frac{\partial}{\partial x_i},$$

 $v_i = v_i(\mathbf{x})$ , and if  $x_i \mapsto x_i'$  is a change of local coordinates then the expression for  $\mathbf{v}$  in the new coordinates is

$$\mathbf{v} = \sum_{i} v_i' \frac{\partial}{\partial x_i'}$$

where

$$v_i' = \sum_j \frac{\partial x_i'}{\partial x_j} v_j,$$

i.e., the clutching function is the **Jacobi matrix** of the change of variable. Thus, every vector field  $\mathbf{v}$  on X defines a derivation of the algebra O(U) for every open set  $U \subset X$  compatible with restriction maps  $O(U) \to O(V)$  for  $V \subset U$ ; in particular, a derivation  $O_x \to O_x$  for all  $x \in X$ . Conversely, it is easy to see that such a collection of derivations gives rise to a vector field, so this is really the same thing.

A manifold X is called **parallelizable** if its tangent bundle is trivial. By Exercise 5.7, this is equivalent to having a collection of vector fields  $\mathbf{v}_1, ..., \mathbf{v}_n$  which form a basis in every tangent space (such a collection is called a **frame**). For example, the circle  $S^1$  and hence the torus  $S^1 \times S^1$  are parallelizable. On the other hand, the sphere  $S^2$  is not parallelizable, since it does not even have a single nowhere vanishing vector field (the **Hairy Ball theorem**, or **Hedgehog theorem**). The same is true for any even-dimensional sphere  $S^{2m}$ ,  $m \geq 1$ .

<sup>&</sup>lt;sup>5</sup>In other words, using a fancier language,  $\mathbf{v}$  defines a derivation of the **sheaf** of regular functions on X.

5.3. **Tensor fields, differential forms.** Since vector bundles are basically just smooth families of vector spaces varying over some base manifold X, we can do with them the same things we can do with vector spaces - duals, tensor products, symmetric and exterior powers, etc. E.g., the **cotangent bundle**  $T^*X$  is dual to the tangent bundle TX.

More generally, we make the following definition.

**Definition 5.9.** A **tensor field** of rank (k, m) on a manifold X is a section of the tensor product  $(TX)^{\otimes k} \otimes (T^*X)^{\otimes m}$ .

For example, a tensor field of rank (1,0) is a vector field. Also, a skew-symmetric tensor field of rank (0,m) is called a **differential** m-form on X. In other words, a differential m-form is a section of the vector bundle  $\Lambda^m T^*X$ .

For instance, if  $f \in O(X)$  then we have a differential 1-form df on X, called **the differential of** f (indeed, recall that  $d_x f : T_x X \to \mathbb{K}$ ). A general 1-form can therefore be written in local coordinates as

$$\omega = \sum_{i} a_i dx_i.$$

where  $a_i = a_i(\mathbf{x})$ . If coordinates are changed as  $x_i \mapsto x_i'$ , then in new coordinates

$$\omega = \sum_{i} a'_{i} dx'_{i}$$

where

$$a_i' = \sum_j \frac{\partial x_j}{\partial x_i'} a_j.$$

Thus the clutching function is the **inverse of the Jacobi matrix** of the change of variable. For instance,

$$df = \sum_{i} \frac{\partial f}{\partial x_i} dx_i.$$

More generally, a differential m-form in local coordinates looks like

$$\omega = \sum_{1 \le i_1 \le \dots \le i_m \le n} a_{i_1 \dots i_m}(x) dx_{i_1} \wedge \dots \wedge dx_{i_m}.$$

5.4. Left and right invariant tensor fields on Lie groups. Note that if a Lie group G acts on a manifold X, then it automatically acts on the tangent bundle TX and thus on vector and, more generally, tensor fields on X. In particular, G acts on tensor fields on itself by left and right translations; we will denote this action by  $L_q$  and  $R_q$ ,

respectively. We say that a tensor field T on G is **left invariant** if  $L_qT = T$  for all  $g \in G$ , and **right invariant** if  $R_qT = T$  for all  $g \in G$ .

**Proposition 5.10.** (i) For any  $\tau \in \mathfrak{g}^{\otimes k} \otimes \mathfrak{g}^{*\otimes m}$  there exists a unique left invariant tensor field  $\mathbf{L}_{\tau}$  and a unique right invariant tensor field  $\mathbf{R}_{\tau}$  whose value at 1 is  $\tau$ . Thus, the spaces of such tensor fields are naturally isomorphic to  $\mathfrak{g}^{\otimes k} \otimes \mathfrak{g}^{*\otimes m}$ .

(ii)  $L_{\tau}$  is also right invariant iff  $R_{\tau}$  is also left invariant iff  $\tau$  is invariant under the adjoint representation  $Ad_{q}$ .

Proof. We only prove (i). Consider the tensor fields  $\mathbf{L}_{\tau}(g) := L_g \tau$ ,  $\mathbf{R}_{\tau}(g) := R_{g^{-1}\tau}$  (i.e., we "spread"  $\tau$  from  $1 \in G$  to other points  $g \in G$  by left/right translations). By construction,  $R_{g^{-1}\tau}$  is right invariant, while  $L_g\tau$  is left invariant, both with value  $\tau$  at 1, and it is clear that these are unique.

Exercise 5.11. Prove Proposition 5.10(ii).

Corollary 5.12. A Lie group is parallelizable.

*Proof.* Given a basis  $e_1, ..., e_n$  of  $\mathfrak{g} = T_1G$ , the vector fields  $L_g e_1, ..., L_g e_n$  form a frame.

Remark 5.13. In particular,  $S^1$  and  $SU(2) = S^3$  are parallelizable. It turns out that  $S^n$  for  $n \ge 1$  is parallelizable if and only if n = 1, 3, 7 (a deep theorem in differential topology). So spheres of other dimensions don't admit a Lie group structure. The sphere  $S^7$  does not admit one either, although it admits a weaker structure of a "homotopy Lie group", or H-space (arising from octonions) which suffices for parallelizability. Thus the only spheres admitting a Lie group structure are  $S^0 = \{1, -1\}$ ,  $S^1$  and  $S^3$ . This result is fairly elementary and will be proved in Section 46.

#### 6. Classical Lie groups

6.1. First examples of classical groups. Roughly speaking, classical groups are groups of matrices arising from linear algebra. More precisely, classical groups are the following subgroups of the general linear group  $GL_n(\mathbb{K})$ :  $GL_n(\mathbb{K})$ ,  $SL_n(\mathbb{K})$  (the special linear group),  $O_n(\mathbb{K})$ ,  $SO_n(\mathbb{K})$ ,  $Sp_{2n}(\mathbb{K})$ , O(p,q), SO(p,q), U(p,q), SU(p,q), Sp(2p,2q) :=  $Sp_{2n}(\mathbb{C}) \cap U(2p,2q)$  for p+q=n (and also some others we'll consider later).

Namely,

- The **orthogonal group**  $O_n(\mathbb{K})$  is the group of matrices preserving the nondegenerate quadratic form in n variables,  $Q = x_1^2 + ... + x_n^2$  (or, equivalently, the corresponding bilinear form  $x_1y_1 + ... + x_ny_n$ );
- The symplectic group  $Sp_{2n}(\mathbb{K})$  is the group of matrices preserving a nondegenerate skew-symmetric form in 2n variables;
- The **pseudo-orthogonal group** O(p,q), p+q=n is the group of real matrices preserving a nondegenerate quadratic form of signature (p,q),  $Q=x_1^2+\ldots+x_p^2-x_{p+1}^2-\ldots-x_n^2$  (or, equivalently, the corresponding bilinear form);
- The **pseudo-unitary group** U(p,q), p+q=n is the group of complex matrices preserving a nondegenerate Hermitian quadratic form of signature (p,q),  $Q=|x_1|^2+...+|x_p|^2-|x_{p+1}|^2-...-|x_n|^2$  (or, equivalently, the corresponding sesquilinear form);
- The special pseudo-orthogonal, pseudo-unitary, and orthogonal groups  $SO(p,q) \subset O(p,q)$ ,  $SU(p,q) \subset U(p,q)$ ,  $SO_n \subset O_n$  are the subgroups of matrices of determinant 1.

Note that the groups don't change under switching p, q and that  $(S)O_n(\mathbb{R}) = (S)O(n, 0)$ ; it is also denoted (S)O(n). Also (S)U(n, 0) is denoted by (S)U(n).

Exercise 6.1. Show that the special (pseudo)orthogonal groups are index 2 subgroups of the (pseudo)orthogonal groups.

Let us show that they are all Lie groups. For this purpose we'll use the **exponential map** for matrices. Namely, recall from linear algebra that we have an analytic function  $\exp: \mathfrak{gl}_n(\mathbb{K}) \to GL_n(\mathbb{K})$  given by the formula

$$\exp(a) = \sum_{n=0}^{\infty} \frac{a^n}{n!},$$

and the matrix-valued analytic function log near  $1 \in GL_n(\mathbb{K})$ ,

$$\log(A) = -\sum_{\substack{n=1\\38}}^{\infty} \frac{(1-A)^n}{n}.$$

Namely, this is well defined if the spectral radius of 1-A is < 1 (i.e., all eigenvalues are in the open unit disk). These maps have the following properties:

- 1. They are mutually inverse.
- 2. They are conjugation-invariant.
- 3.  $d \exp_0 = d \log_1 = \text{Id}$ .
- 4. If xy = yx then  $\exp(x + y) = \exp(x) \exp(y)$ . If XY = YX then  $\log(XY) = \log(X) + \log(Y)$  (for X, Y sufficiently close to 1).
- 5. For  $x \in \mathfrak{gl}_n(\mathbb{K})$  the map  $t \mapsto \exp(tx)$  is a homomorphism of Lie groups  $\mathbb{K} \to GL_n(\mathbb{K})$ .
  - 6.  $\det \exp(a) = \exp(\operatorname{Tr} a), \log(\det A) = \operatorname{Tr}(\log A).$

Now we can look at classical groups and see what happens to the equations defining them when we apply log.

- 1.  $G = SL_n(\mathbb{K})$ . We already showed that it is a Lie group in Example 3.14 but let us re-do it by a different method. The group G is defined by the equation  $\det A = 1$ . So for A close to 1 we have  $\log(\det A) = 0$ , i.e.,  $\operatorname{Tr}\log(A) = 0$ . So  $\log(A) \in \mathfrak{sl}_n(\mathbb{K}) = \mathfrak{g}$ , the space of matrices with trace 0. This defines a local chart near  $1 \in G$ , showing that G is a manifold, hence a Lie group (namely, local charts near other points are obtained by translation).
- 2.  $G = O_n(\mathbb{K})$ . The equation is  $A^T = A^{-1}$ , thus  $\log(A)^T = -\log(A)$ , so  $\log(A) \in \mathfrak{so}_n(\mathbb{K}) = \mathfrak{g}$ , the space of skew-symmetric matrices.
- 3. G = U(n). The equation is  $\overline{A}^T = A^{-1}$ , thus  $\overline{\log(A)}^T = -\log(A)$ , so  $\log(A) \in \mathfrak{u}_n = \mathfrak{g}$ , the space of skew-Hermitian matrices.

**Exercise 6.2.** Do the same for all classical groups listed above.

We see that the logarithm map identifies the neighborhood of 1 in the group G with a neighborhood of 0 in a finite-dimensional vector space. Thus we obtain

**Proposition 6.3.** Every classical group G from the above list is a Lie group, with  $\mathfrak{g} = T_1G \subset \mathfrak{gl}_n(\mathbb{K})$ . Moreover, if  $\mathfrak{u} \subset \mathfrak{gl}_n(\mathbb{K})$  is a small neighborhood of 0 and  $U = \exp(\mathfrak{u})$  then  $\exp$  and  $\log$  define mutually inverse diffeomorphisms between  $\mathfrak{u} \cap \mathfrak{g}$  and  $U \cap G$ .

**Exercise 6.4.** Which of these groups are complex Lie groups?

**Exercise 6.5.** Use this proposition to compute the dimensions of classical groups:  $\dim SL_n = n^2 - 1$ ,  $\dim O_n = n(n-1)/2$ ,  $\dim Sp_{2n} = n(2n+1)$ ,  $\dim SU_n = n^2 - 1$ , etc. (Note that for complex groups we give the dimension over  $\mathbb{C}$ ).

6.2. Quaternions. An important role in the theory of Lie groups is played by the algebra of quaternions, which is the only noncommutative finite dimensional division algebra over  $\mathbb{R}$ , discovered in the 19th century by W. R. Hamilton.

**Definition 6.6.** The algebra of quaternions is the  $\mathbb{R}$ -algebra with basis 1,  $\mathbf{i}$ ,  $\mathbf{j}$ ,  $\mathbf{k}$  and multiplication rules

$$\mathbf{i}\mathbf{j} = -\mathbf{j}\mathbf{i} = \mathbf{k}, \ \mathbf{j}\mathbf{k} = -\mathbf{k}\mathbf{j} = \mathbf{i}, \ \mathbf{k}\mathbf{i} = -\mathbf{i}\mathbf{k} = \mathbf{j}, \mathbf{i}^2 = \mathbf{j}^2 = \mathbf{k}^2 = -1.$$

This algebra is associative but not commutative. Given a quaternion

$$\mathbf{q} = a + b\mathbf{i} + c\mathbf{j} + d\mathbf{k}, \ a, b, c, d \in \mathbb{R},$$

we define the **conjugate quaternion** by the formula

$$\overline{\mathbf{q}} = a - b\mathbf{i} - c\mathbf{j} - d\mathbf{k}.$$

Thus

$$q\overline{q} = |q|^2 = a^2 + b^2 + c^2 + d^2 \in \mathbb{R},$$

where  $|\mathbf{q}|$  is the length of  $\mathbf{q}$  as a vector in  $\mathbb{R}^4$ . So if  $\mathbf{q} \neq 0$  then it is invertible and

$$\mathbf{q}^{-1} = \frac{\overline{\mathbf{q}}}{|\mathbf{q}|^2}.$$

Thus  $\mathbb{H}$  is a **division algebra** (i.e., a skew-field). One can show that the only finite dimensional associative division algebras over  $\mathbb{R}$  are  $\mathbb{R}$ ,  $\mathbb{C}$  and  $\mathbb{H}$ . (See Exercise 6.9).

In particular, we can do linear algebra over  $\mathbb{H}$  in almost the same way as we do over ordinary fields. Namely, every (left or right) module over  $\mathbb{H}$  is free and has a basis; such a module is called a (left or right) **quaternionic vector space**. In particular, any (say, right) quaternionic vector space of dimension n (i.e., with basis of n elements) is isomorphic to  $\mathbb{H}^n$ . Moreover,  $\mathbb{H}$ -linear maps between such spaces are given by left multiplication by quaternionic matrices. Finally, it is easy to see that Gaussian elimination works the same way as over ordinary fields; in particular, every invertible square matrix over  $\mathbb{H}$  is a product of elementary matrices of the form  $1 + (\mathbf{q} - 1)E_{ii}$  and  $1 + \mathbf{q}E_{ij}$ ,  $i \neq j$ , where  $\mathbf{q} \in \mathbb{H}$  is nonzero.

Also it is easy to show that

$$\overline{\mathbf{q}_1}\overline{\mathbf{q}_2} = \overline{\mathbf{q}_2} \cdot \overline{\mathbf{q}_1}, \ |\mathbf{q}_1\mathbf{q}_2| = |\mathbf{q}_1| \cdot |\mathbf{q}_2|$$

(check this!). So quaternions are similar to complex numbers, except they are non-commutative. Finally, note that  $\mathbb H$  contains a copy of  $\mathbb C$  spanned by 1,  $\mathbf i$ ; however, this does not make  $\mathbb H$  a  $\mathbb C$ -algebra since  $\mathbf i$  is not a central element.

**Proposition 6.7.** The group of unit quaternions  $\{\mathbf{q} \in \mathbb{H} : |\mathbf{q}| = 1\}$  under multiplication is isomorphic to SU(2) as a Lie group.

*Proof.* We can realize  $\mathbb{H}$  as  $\mathbb{C}^2$ , where  $\mathbb{C} \subset \mathbb{H}$  is spanned by 1, **i**; namely,  $(z_1, z_2) \mapsto z_1 + \mathbf{j} z_2$ . Then left multiplication by quaternions on  $\mathbb{H} = \mathbb{C}^2$  commutes with right multiplication by  $\mathbb{C}$ , i.e., is  $\mathbb{C}$ -linear. So it is given by complex 2-by-2 matrices. It is easy to compute that the corresponding matrix is

$$z_1 + z_2 \mathbf{j} \mapsto \begin{pmatrix} z_1 & -\overline{z_2} \\ z_2 & \overline{z_1} \end{pmatrix},$$

and we showed in Example 2.3(5) that such matrices (with  $|z_1|^2 + |z_2|^2 = 1$ ) are exactly the matrices from SU(2).

This is another way to see that  $SU(2) \cong S^3$  as a manifold (since the set of unit quaternions is manifestly  $S^3$ ).

Corollary 6.8. The map  $\mathbf{q} \mapsto (\frac{\mathbf{q}}{|\mathbf{q}|}, |\mathbf{q}|)$  is an isomorphism of Lie groups  $\mathbb{H}^{\times} \cong SU(2) \times \mathbb{R}_{>0}$ .

This is the quaternionic analog of the trigonometric form of complex numbers, except the "phase" factor  $\frac{\mathbf{q}}{|\mathbf{q}|}$  is now not in  $S^1$  but in  $S^3 = SU(2)$ .

**Exercise 6.9.** Let D be a finite dimensional division algebra over  $\mathbb{R}$ .

- (i) Show that if D is commutative then  $D = \mathbb{R}$  or  $D = \mathbb{C}$ .
- (ii) Assume that D is not commutative. Take  $\mathbf{q} \in D$ ,  $\mathbf{q} \notin \mathbb{R}$ . Show that there exist  $a, b \in \mathbb{R}$  such that  $\mathbf{i} := a + b\mathbf{q}$  satisfies  $\mathbf{i}^2 = -1$ .
- (iii) Decompose D into the eigenspaces  $D_{\pm}$  of the operator of conjugation by  $\mathbf{i}$  with eigenvalues  $\pm 1$  and show that  $1, \mathbf{i}$  is a basis of  $D_{+}$ , i.e.,  $D_{+} \cong \mathbb{C}$ .
- (iv) Pick  $\mathbf{q} \in D_-$ ,  $\mathbf{q} \neq 0$ , and show that  $D_- = D_+\mathbf{q}$ , so  $\{1, \mathbf{i}, \mathbf{q}, \mathbf{iq}\}$  is a basis of D over  $\mathbb{R}$ . Deduce that  $\mathbf{q}^2$  is a central element of D.
  - (v) Conclude that  $\mathbf{q}^2 = -\lambda$  where  $\lambda \in \mathbb{R}_{>0}$  and deduce that  $D \cong \mathbb{H}$ .
- 6.3. More classical groups. Now we can define a new classical group  $GL_n(\mathbb{H})$ , a real Lie group of dimension  $4n^2$ , called the **quaternionic** general linear group. For example, as we just showed,  $GL_1(\mathbb{H}) = \mathbb{H}^{\times} \cong SU(2) \times \mathbb{R}_{>0}$ .

For  $A \in GL_n(\mathbb{H})$ , let  $\det A$  be the determinant of A as a linear operator on  $\mathbb{C}^{2n} = \mathbb{H}^n$ .

**Lemma 6.10.** We have  $\det A > 0$ .

*Proof.* For n = 1,  $A = \mathbf{q} \in \mathbb{H}^{\times}$  and  $\det \mathbf{q} = |\mathbf{q}|^2 > 0$ . It follows that  $\det(1 + (\mathbf{q} - 1)E_{ii}) = |\mathbf{q}|^2 > 0$ . Also it is easy to see that  $\det(1 + \mathbf{q}E_{ij}) = \mathbf{q}$ 

1 for  $i \neq j$ . It then follows by Gaussian elimination that for any A we have det(A) > 0.

Let  $SL_n(\mathbb{H}) \subset GL_n(\mathbb{H})$  be the subgroup of matrices A with det A = 1, called the **quaternionic special linear group**.

**Exercise 6.11.** Show that  $SL_n(\mathbb{H}) \subset GL_n(\mathbb{H})$  is a normal subgroup, and  $GL_n(\mathbb{H}) \cong SL_n(\mathbb{H}) \times \mathbb{R}_{>0}$ .

Thus  $SL_n(\mathbb{H})$  is a real Lie group of dimension  $4n^2 - 1$ .

We can also define groups of quaternionic matrices preserving various sesquilinear forms. Namely, let  $V \cong \mathbb{H}^n$  be a right quaternionic vector space.

**Definition 6.12.** A **sesquilinear form** on V is a biadditive function  $(,): V \times V \to \mathbb{H}$  such that

$$(\mathbf{x}\alpha, \mathbf{y}\beta) = \overline{\alpha}(\mathbf{x}, \mathbf{y})\beta, \ \mathbf{x}, \mathbf{y} \in V, \ \alpha, \beta \in \mathbb{H}.$$

Such a form is called **Hermitian** if  $(\mathbf{x}, \mathbf{y}) = \overline{(\mathbf{y}, \mathbf{x})}$  and **skew-Hermitian** if  $(\mathbf{x}, \mathbf{y}) = -\overline{(\mathbf{y}, \mathbf{x})}$ .

Note that the order of factors is important here!

**Proposition 6.13.** (i) Every nondegenerate Hermitian form on V in some basis takes the form

$$(\mathbf{x}, \mathbf{y}) = \overline{x_1}y_1 + \dots + \overline{x_p}y_p - \overline{x_{p+1}}y_{p+1} - \dots - \overline{x_n}y_n$$

for a unique pair (p,q) with p+q=n.

(ii) Every nondegenerate skew-Hermitian form on V in some basis takes the form

$$(\mathbf{x}, \mathbf{y}) = \overline{x_1} \mathbf{j} y_1 + \dots + \overline{x_n} \mathbf{j} y_n.$$

Exercise 6.14. Prove Proposition 6.13.

In (i), the pair (p,q) is called the **signature** of the quaternionic Hermitian form.

**Exercise 6.15.** Show that a nondegenerate quaternionic Hermitian form of signature (p, q) can be written as

$$(\mathbf{x}, \mathbf{y}) = B_1(\mathbf{x}, \mathbf{y}) + \mathbf{j}B_2(\mathbf{x}, \mathbf{y}),$$

with  $B_1, B_2$  taking values in  $\mathbb{C} = \mathbb{R} + \mathbb{R}\mathbf{i} \subset \mathbb{H}$ , where  $B_1$  is a usual nondegenerate Hermitian form of signature (2p, 2q) and  $B_2$  is a non-degenerate skew-symmetric bilinear form on V as a (2n-dimensional)  $\mathbb{C}$ -vector space. Show that  $B_2(\mathbf{x}, \mathbf{y}) = B_1(\mathbf{x}\mathbf{j}, \mathbf{y})$ . Deduce that any complex linear transformation preserving  $B_1$  and  $B_2$  is  $\mathbb{H}$ -linear.

Thus the group of symmetries of a nondegenerate quaternionic Hermitian form of signature (p,q) is  $Sp(2p,2q) = Sp_{2n}(\mathbb{C}) \cap U(2p,2q)$ . It is called the **quaternionic pseudo-unitary group**.

One also sometimes uses the notation  $U(p,q,\mathbb{R})=O(p,q), U(p,q,\mathbb{C})=U(p,q), \ U(p,q,\mathbb{H})=Sp(2p,2q), \ \text{and} \ U(n,0,\mathbb{K})=U(n,\mathbb{K}) \ \text{for} \ \mathbb{K}=\mathbb{R},\mathbb{C},\mathbb{H}.$ 

**Exercise 6.16.** Show that a nondegenerate quaternionic skew-Hermitian form can be written as

$$(\mathbf{x}, \mathbf{y}) = B_1(\mathbf{x}, \mathbf{y}) + \mathbf{j}B_2(\mathbf{x}, \mathbf{y}),$$

with  $B_1, B_2$  taking values in  $\mathbb{C} = \mathbb{R} + \mathbb{R}\mathbf{i} \subset \mathbb{H}$ , where  $B_1$  is an ordinary skew-Hermitian form, while  $B_2$  is a symmetric bilinear form (both nondegenerate). Show that  $B_2(\mathbf{x}, \mathbf{y}) = B_1(\mathbf{x}\mathbf{j}, \mathbf{y})$ . Deduce that any complex linear transformation preserving  $B_1$  and  $B_2$  is  $\mathbb{H}$ -linear. Also show that the signature of the Hermitian form  $iB_1$  is necessarily (n, n).

Thus the group of symmetries of a nondegenerate quaternionic skew-Hermitian form is  $O_{2n}(\mathbb{C}) \cap U(n,n)$ . This group is denoted by  $O^*(2n)$  and called the **quaternionic orthogonal group**. There is also the subgroup  $SO^*(2n) \subset O^*(2n)$  of matrices of determinant 1 (having index 2).

All of these groups are Lie groups, which is shown similarly to Subsection 6.1, using the exponential map.

Exercise 6.17. Compute the dimensions of all classical groups introduced above.

# 7. The exponential map of a Lie group

7.1. **The exponential map.** We will now generalize the exponential and logarithm maps from matrix groups to arbitrary Lie groups.

Let G be a real Lie group,  $\mathfrak{g} = T_1G$ .

**Proposition 7.1.** Let  $x \in \mathfrak{g}$ . There is a unique morphism of Lie groups  $\gamma = \gamma_x : \mathbb{R} \to G$  such that  $\gamma'(0) = x$ .

*Proof.* For such a morphism we should have

$$\gamma(t+s) = \gamma(t)\gamma(s), \ t, s \in \mathbb{R},$$

so differentiating by s at s = 0, we get<sup>6</sup>

$$\gamma'(t) = \gamma(t)x.$$

Thus  $\gamma(t)$  is a solution of the ODE defined by the left-invariant vector field  $\mathbf{L}_x$  corresponding to  $x \in \mathfrak{g}$  with initial condition  $\gamma(0) = 1$ . By the existence and uniqueness theorem for solutions of ODE, this equation has a unique solution with this initial condition defined for  $|t| < \varepsilon$  for some  $\varepsilon > 0$ . Moreover, if  $|s| + |t| < \varepsilon$ , both  $\gamma_1(t) := \gamma(s+t)$  and  $\gamma_2(t) := \gamma(s)\gamma(t)$  satisfy this differential equation with initial condition  $\gamma_1(0) = \gamma_2(0) = \gamma(s)$ , so  $\gamma_1 = \gamma_2$ . Thus

$$\gamma(s+t) = \gamma(s)\gamma(t), |s| + |t| < \varepsilon;$$

hence  $\gamma(t)x = x\gamma(t)$  for  $|t| < \varepsilon$ .

We claim that the solution  $\gamma(t)$  extends to all values of  $t \in \mathbb{R}$ . Indeed, let us prove that it extends to  $|t| < 2^n \varepsilon$  for all  $n \ge 0$  by induction in n. The base of induction (n = 0) is already known, so we only need to justify the induction step from n - 1 to n. Given t with  $|t| < 2^n \varepsilon$ , we define

$$\gamma(t) := \gamma(\frac{t}{2})^2$$
.

This agrees with the previously defined solution for  $|t| < 2^{n-1}\varepsilon$ , and we have

$$\gamma'(t) = \frac{1}{2} (\gamma'(\frac{t}{2})\gamma(\frac{t}{2}) + \gamma(\frac{t}{2})\gamma'(\frac{t}{2})) = \frac{1}{2}\gamma(\frac{t}{2})x\gamma(\frac{t}{2}) + \frac{1}{2}\gamma(\frac{t}{2})^2x = \gamma(\frac{t}{2})^2x = \gamma(t)x,$$
as desired

Thus, we have a regular map  $\gamma : \mathbb{R} \to G$  with  $\gamma(s+t) = \gamma(s)\gamma(t)$  and  $\gamma'(0) = x$ , which is unique by the uniqueness of solutions of ODE.  $\square$ 

**Definition 7.2.** The **exponential map**  $\exp : \mathfrak{g} \to G$  is defined by the formula  $\exp(x) = \gamma_x(1)$ .

Thus  $\gamma_x(t) = \exp(tx)$ . So we have

<sup>&</sup>lt;sup>6</sup>For brevity for  $g \in G$ ,  $x \in \mathfrak{g}$  we denote  $L_q x$  by gx and  $R_q x$  by xg.

**Proposition 7.3.** The flow defined by the right-invariant vector field  $\mathbf{R}_x$  is given by  $g \mapsto \exp(tx)g$ , and the flow defined by the left-invariant vector field  $\mathbf{L}_x$  is given by  $g \mapsto g \exp(tx)$ .

**Example 7.4.** 1. Let  $G = \mathbb{K}^n$ . Then  $\exp(x) = x$ .

2. Let  $G = GL_n(\mathbb{K})$  or its Lie subgroup. Then  $\gamma_x(t)$  satisfies the matrix differential equation

$$\gamma'(t) = \gamma(t)x$$

with  $\gamma(0) = 1$ , so

$$\gamma_x(t) = e^{tx},$$

the matrix exponential. For example, if n=1, this is the usual exponential function.

The following theorem describes the basic properties of the exponential map. Let G be a real or complex Lie group.

**Theorem 7.5.** (i)  $\exp : \mathfrak{g} \to G$  is a regular map which is a diffeomorphism of a neighborhood of  $0 \in \mathfrak{g}$  onto a neighborhood of  $1 \in G$ , with  $\exp(0) = 1$ ,  $\exp'(0) = \operatorname{Id}_{\mathfrak{g}}$ .

- (ii)  $\exp((s+t)x) = \exp(sx) \exp(tx)$  for  $x \in \mathfrak{g}$ ,  $s, t \in \mathbb{K}$ .
- (iii) For any morphism of Lie groups  $\phi: G \to K$  and  $x \in T_1G$  we have

$$\phi(\exp(x)) = \exp(\phi_* x);$$

i.e., the exponential map commutes with morphisms.

(iv) For any  $g \in G$ ,  $x \in \mathfrak{g}$ , we have

$$g \exp(x)g^{-1} = \exp(\mathrm{Ad}_g x).$$

*Proof.* (i) The regularity of exp follows from the fact that if a differential equation depends regularly on parameters then so do its solutions. Also  $\gamma_0(t) = 1$  so  $\exp(0) = 1$ . We have  $\exp'(0)x = \frac{d}{dt}\exp(tx)|_{t=0} = x$ , so  $\exp'(0) = \text{Id}$ . By the inverse function theorem this implies that exp is a diffeomorphism near the origin.

- (ii) Holds since  $\exp(tx) = \gamma_x(t)$ .
- (iii) Both  $\phi(\exp(tx))$  and  $\exp(\phi_*(tx))$  satisfy the equation  $\gamma'(t) = \gamma(t)\phi_*(x)$  with the same initial conditions.
  - (iv) is a special case of (iii) with  $\phi: G \to G$ ,  $\phi(h) = ghg^{-1}$ .

Thus exp has an inverse  $\log: U \to \mathfrak{g}$  defined on a neighborhood U of  $1 \in G$  with  $\log(1) = 0$ . This map is called the **logarithm**. For  $GL_n(\mathbb{K})$  and its Lie subgroups it coincides with the matrix logarithm. The logarithm map defines a canonical coordinate chart on G near 1, so a choice of a basis of  $\mathfrak{g}$  gives a local coordinate system.

**Proposition 7.6.** Let G be a connected Lie group and  $\phi: G \to K$  a morphism of Lie groups. Then  $\phi$  is completely determined by the linear map  $\phi_*: T_1G \to T_1K$ .

Proof. We have  $\phi(\exp(x)) = \exp(\phi_*(x))$ , so since exp is a diffeomorphism near 0,  $\phi$  is determined by  $\phi_*$  on a neighborhood of  $1 \in G$ . This completely determines  $\phi$  since this neighborhood generates G by Proposition 3.15.

Exercise 7.7. (i) Show that a connected compact complex Lie group is abelian. (**Hint:** consider the adjoint representation and use that a holomorphic function on a compact complex manifold is constant, by the maximum principle.)

- (ii) Classify such Lie groups of dimension n up to isomorphism (Show that they are compact complex tori whose isomorphism classes are bijectively labeled by elements of the set  $GL_n(\mathbb{C})\backslash GL_{2n}(\mathbb{R})/GL_{2n}(\mathbb{Z})$ .)
- (iii) Work out the classification explicitly in the 1-dimensional case (this is the classification of complex elliptic curves). Namely, show that isomorphism classes are labeled by points of  $\mathbb{H}/\Gamma$ , where  $\mathbb{H}$  is the upper half-plane and  $\Gamma = SL_2(\mathbb{Z})$  acting on  $\mathbb{H}$  by Möbius transformations  $\tau \mapsto \frac{a\tau+b}{c\tau+d}$  (where  $\text{Im}(\tau) > 0$ ).
- 7.2. The commutator. In general (say, for  $G = GL_n(\mathbb{K}), n \geq 2$ ),  $\exp(x+y) \neq \exp(x) \exp(y)$ . So let us consider the map

$$(x,y) \mapsto \mu(x,y) = \log(\exp(x)\exp(y))$$

which maps  $U \times U \to \mathfrak{g}$ , where  $U \subset \mathfrak{g}$  is a neighborhood of 0. This map expresses the product in G in the coordinate chart coming from the logarithm map. We have  $\mu(x,0) = \mu(0,x) = x$  and  $\mu_*(x,y) = x+y$ . So, since  $\mu$  is regular, we have the second Taylor approximation

$$\mu(x,y) = x + y + \frac{1}{2}\mu_2(x,y) + \dots$$

where  $\mu_2 = d^2 \mu_{(0,0)}$  is the quadratic part and ... are higher terms. Moreover,  $\mu_2(x,0) = \mu_2(0,y) = 0$ , hence  $\mu_2$  is a bilinear map  $\mathfrak{g} \times \mathfrak{g} \to \mathfrak{g}$ . It is easy to see that  $\mu(x,-x) = 0$ , hence  $\mu_2$  is skew-symmetric.

**Definition 7.8.** The map  $\mu_2$  is called the **commutator** and denoted by  $x, y \mapsto [x, y]$ .

Thus we have

(7.1) 
$$\exp(x) \exp(y) = \exp(x + y + \frac{1}{2}[x, y] + \dots).$$

**Example 7.9.** Let  $G = GL_n(\mathbb{K})$ . Then

$$\exp(x)\exp(y) = (1+x+\frac{x^2}{2}+\ldots)(1+y+\frac{y^2}{2}+\ldots) = 1+x+y+\frac{x^2}{2}+xy+\frac{y^2}{2}+\ldots = \frac{x^2}{2}+xy+\frac{y^2}{2}+\ldots = \frac{x^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+\ldots = \frac{x^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+\ldots = \frac{x^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+\ldots = \frac{x^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+\ldots = \frac{x^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2}+xy+\frac{y^2}{2$$

$$1 + (x + y) + \frac{(x+y)^2}{2} + \frac{xy-yx}{2} + \dots = \exp(x + y + \frac{xy-yx}{2} + \dots)$$

Thus

$$[x, y] = xy - yx.$$

This justifies the term "commutator": it measures the failure of x and y to commute.

Corollary 7.10. If  $G \subset GL_n(\mathbb{K})$  is a Lie subgroup then  $\mathfrak{g} = T_1G \subset$  $\mathfrak{gl}_n(\mathbb{K})$  is closed under the commutator [x,y]=xy-yx, which coincides with the commutator of G.

For  $x \in \mathfrak{g}$  define the linear map  $adx : \mathfrak{g} \to \mathfrak{g}$  by

$$adx(y) = [x, y].$$

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

*Proof.* (i) Follows since  $\phi$  commutes with the exponential map.

- (ii) Follows from (i) by setting  $\phi = \mathrm{Ad}_a$ .
- (iii) By (7.1), modulo cubic and higher terms we have

$$\log(\exp(x)\exp(y)) = \log(\exp(y)\exp(x)) + [x, y] + \dots,$$

which implies the statement by exponentiation.

(iv) Let  $\log X(t) = x(t)$ ,  $\log Y(s) = y(s)$ . Then by (iii) we have

$$\log(X(t)Y(s)X(t)^{-1}Y(s)^{-1}) =$$

$$\begin{split} \log(\exp(x(t))\exp(y(s))\exp(x(t))^{-1}\exp(y(s))^{-1}) &= ts([x,y]+o(1)),\ t,s\to 0.\\ \text{This implies the first two statements. The last statement follows by taking the limit in $s$ first, then in $t$.}\\ \text{(v) follows from (iii)}. & \Box \end{split}$$

# 8. Lie algebras

8.1. The Jacobi identity. The matrix commutator [x, y] = xy - yx obviously satisfies the identity

$$[[x, y], z] + [[y, z], x] + [[z, x], y] = 0$$

called the **Jacobi identity**. Thus it is satisfied for any Lie subgroup of  $GL_n(\mathbb{K})$ .

**Proposition 8.1.** The Jacobi identity holds for any Lie group G.

*Proof.* Let  $\mathfrak{g} = T_1G$ . The Jacobi identity is equivalent to  $\mathrm{ad}x$  being a derivation of the commutator:

$$adx([y, z]) = [adx(y), z] + [y, adx(z)], \ x, y, z \in \mathfrak{g}.$$

To show that it is indeed a derivation, let  $q(t) = \exp(tx)$ , then

$$Ad_{g(t)}([y, z]) = [Ad_{g(t)}(y), Ad_{g(t)}(z)].$$

The desired identity is then obtained by differentiating this equality by t at t = 0 and using the Leibniz rule and Proposition 7.11(iv).

Corollary 8.2. We have ad[x, y] = [adx, ady].

*Proof.* This is also equivalent to the Jacobi identity.  $\Box$ 

**Proposition 8.3.** For  $x \in \mathfrak{g}$  one has  $\exp(\operatorname{ad} x) = \operatorname{Ad}_{\exp(x)} \in GL(\mathfrak{g})$ .

*Proof.* We will show that  $\exp(t \operatorname{ad} x) = \operatorname{Ad}_{\exp(tx)}$  for  $t \in \mathbb{R}$ . Let  $\gamma_1(t) = \exp(t \operatorname{ad} x)$  and  $\gamma_2(t) = \operatorname{Ad}_{\exp(tx)}$ . Then  $\gamma_1, \gamma_2$  both satisfy the differential equation  $\gamma'(t) = \gamma(t) \operatorname{ad} x$  and equal 1 at t = 0. Thus  $\gamma_1 = \gamma_2$ .

# 8.2. Lie algebras.

**Definition 8.4.** A **Lie algebra** over a field **k** is a vector space  $\mathfrak{g}$  over **k** equipped with bilinear operation  $[,]:\mathfrak{g}\times\mathfrak{g}\to\mathfrak{g}$ , called the **commutator** or (**Lie**) **bracket** which satisfies the following identities:

- (i) [x, x] = 0 for all  $x \in \mathfrak{g}$ ;
- (ii) the Jacobi identity: [[x, y], z] + [[y, z], x] + [[z, x], y] = 0.

A (homo)morphism of Lie algebras is a linear map between Lie algebras that preserves the commutator.

**Remark 8.5.** If **k** has characteristic  $\neq 2$  then the condition [x, x] = 0 is equivalent to skew-symmetry [x, y] = -[y, x], but in characteristic 2 it is stronger.

**Example 8.6.** Any subspace of  $\mathfrak{gl}_n(\mathbf{k})$  closed under [x,y] := xy - yx is a Lie algebra.

**Example 8.7.** The map ad :  $\mathfrak{g} \to \operatorname{End}(\mathfrak{g})$  is a morphism of Lie algebras.

Thus we have

**Theorem 8.8.** If G is a  $\mathbb{K}$ -Lie group (for  $\mathbb{K} = \mathbb{R}, \mathbb{C}$ ) then  $\mathfrak{g} := T_1G$  has a natural structure of a Lie algebra over  $\mathbb{K}$ . Moreover, if  $\phi : G \to K$  is a morphism of Lie groups then  $\phi_* : T_1G \to T_1K$  is a morphism of Lie algebras.

We will denote the Lie algebra  $\mathfrak{g} = T_1G$  by LieG or Lie(G) and call it the **Lie algebra of** G. We see that the assignment  $G \mapsto \text{Lie}G$  is a functor from the category of Lie groups to the category of Lie algebras. Thus we have a map  $\text{Hom}(G, K) \to \text{Hom}(\text{Lie}G, \text{Lie}K)$ , which is injective if G is connected.

Motivated by Proposition 7.11(v), a Lie algebra  $\mathfrak{g}$  is said to be **commutative** or **abelian** if [x, y] = 0 for all  $x, y \in \mathfrak{g}$ .

8.3. Lie subalgebras and ideals. A Lie subalgebra of a Lie algebra  $\mathfrak{g}$  is a subspace  $\mathfrak{h} \subset \mathfrak{g}$  closed under the commutator. It is called a Lie ideal if moreover  $[\mathfrak{g},\mathfrak{h}] \subset \mathfrak{h}$ .

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

**Proposition 8.10.** If  $\mathbf{v}, \mathbf{w}$  are derivations of an algebra A then so is  $[\mathbf{v}, \mathbf{w}] := \mathbf{v}\mathbf{w} - \mathbf{w}\mathbf{v}$ .

*Proof.* We have

$$(\mathbf{v}\mathbf{w} - \mathbf{w}\mathbf{v})(ab) = \mathbf{v}(\mathbf{w}(a)b + a\mathbf{w}(b)) - \mathbf{w}(\mathbf{v}(a)b + a\mathbf{v}(b)) =$$

$$\mathbf{v}\mathbf{w}(a)b + \mathbf{w}(a)\mathbf{v}(b) + \mathbf{v}(a)\mathbf{w}(b) + a\mathbf{v}\mathbf{w}(b)$$

$$-\mathbf{w}\mathbf{v}(a)b - \mathbf{v}(a)\mathbf{w}(b) - \mathbf{w}(a)\mathbf{v}(b) - a\mathbf{w}\mathbf{v}(b) =$$

$$(\mathbf{v}\mathbf{w} - \mathbf{w}\mathbf{v})(a)b + a(\mathbf{v}\mathbf{w} - \mathbf{w}\mathbf{v})(b).$$

Thus, the space Vect(X) of vector fields on X is a Lie algebra under the operation

$$\mathbf{v},\mathbf{w}\mapsto [\mathbf{v},\mathbf{w}],$$

called the Lie bracket of vector fields.<sup>7</sup>

In local coordinates we have

$$\mathbf{v} = \sum_{i} v_i \frac{\partial}{\partial x_i}, \ \mathbf{w} = \sum_{i} w_j \frac{\partial}{\partial x_j},$$

SO

$$[\mathbf{v}, \mathbf{w}] = \sum_{i} \left( \sum_{j} (v_j \frac{\partial w_i}{\partial x_j} - w_j \frac{\partial v_i}{\partial x_j}) \right) \frac{\partial}{\partial x_i}.$$

This implies that if vector fields  $\mathbf{v}$ ,  $\mathbf{w}$  are tangent to a k-dimensional submanifold  $Y \subset X$  then so is their Lie bracket  $[\mathbf{v}, \mathbf{w}]$ . Indeed, in local coordinates Y is given by equations  $x_{k+1} = \dots = x_n = 0$ , and in such coordinates a vector field is tangent to Y iff it does not contain terms with  $\frac{\partial}{\partial x_j}$  for j > k.

<sup>&</sup>lt;sup>7</sup>Note that this Lie algebra is infinite dimensional for all real manifolds and many (but not all) complex manifolds of positive dimension.

**Exercise 8.11.** Let  $U \subset \mathbb{R}^n$  be an open subset,  $\mathbf{v}, \mathbf{w} \in \text{Vect}(U)$  and  $g_t, h_t$  be the associated flows, defined in a neighborhood of every point of U for small t. Show that for any  $\mathbf{x} \in U$ 

$$\lim_{t,s\to 0}\frac{g_th_sg_t^{-1}h_s^{-1}(\mathbf{x})-\mathbf{x}}{ts}=[\mathbf{v},\mathbf{w}](\mathbf{x}).$$

Now let G be a Lie group and  $\operatorname{Vect}_L(G)$ ,  $\operatorname{Vect}_R(G) \subset \operatorname{Vect}(G)$  be the subspaces of left and right invariant vector fields.

**Proposition 8.12.**  $\operatorname{Vect}_L(G)$ ,  $\operatorname{Vect}_R(G) \subset \operatorname{Vect}(G)$  are Lie subalgebras which are both canonically isomorphic to  $\mathfrak{g} = \operatorname{Lie} G$ .

*Proof.* The first statement is obvious, so we prove only the second statement. Let  $\mathbf{x}, \mathbf{y} \in \mathrm{Vect}_L(G)$ . Then  $\mathbf{x} = \mathbf{L}_x$ ,  $\mathbf{y} = \mathbf{L}_y$  for  $x = \mathbf{x}(1)$ ,  $y = \mathbf{y}(1) \in \mathfrak{g}$ , where  $\mathbf{L}_z$  denotes the vector field on G obtained by left translations of  $z \in \mathfrak{g}$ . Then  $[\mathbf{L}_x, \mathbf{L}_y] = \mathbf{L}_z$ , where  $z = [\mathbf{L}_x, \mathbf{L}_y](1)$ . So let us compute z.

Let f be a regular function on a neighborhood of  $1 \in G$ . We have shown that for  $u \in \mathfrak{g}$ 

$$(\mathbf{L}_u f)(g) = \frac{d}{dt}|_{t=0} f(g \exp(tu)).$$

Thus,

$$z(f) = x(\mathbf{L}_y f) - y(\mathbf{L}_x f) = x(\frac{\partial}{\partial s}|_{s=0} f(\bullet \exp(sy))) - y(\frac{\partial}{\partial t}|_{t=0} f(\bullet \exp(tx))) = \frac{\partial}{\partial t}|_{t=0} \frac{\partial}{\partial s}|_{s=0} f(\exp(tx) \exp(sy)) - \frac{\partial}{\partial s}|_{s=0} \frac{\partial}{\partial t}|_{t=0} f(\exp(sy) \exp(tx)) = \frac{\partial^2}{\partial t\partial s}|_{t=s=0} (F(tx+sy+\frac{1}{2}ts[x,y]+...) - F(tx+sy-\frac{1}{2}ts[x,y]+...)),$$
 where  $F(u) := f(\exp(u))$ . It is easy to see by using Taylor expansion that this expression equals to  $[x,y](f)$ . Thus  $z = [x,y]$ , i.e., the map  $\mathfrak{g} \to \operatorname{Vect}_L(G)$  given by  $x \mapsto \mathbf{L}_x$  is a Lie algebra isomorphism. Similarly, the map  $\mathfrak{g} \to \operatorname{Vect}_R(G)$  given by  $x \mapsto -\mathbf{R}_x$  is a Lie algebra isomorphism, as claimed.

# 9. Fundamental theorems of Lie theory

9.1. Proofs of Theorem 3.13, Proposition 4.12, Proposition 4.7. Let G be a Lie group with Lie algebra  $\mathfrak{g}$  and X be a manifold with an action  $a: G \times X \to X$ . Then for any  $z \in \mathfrak{g}$  we have a vector field  $a_*(z)$  on X given by

$$(a_*(z)f)(x) = \frac{d}{dt}|_{t=0} f(\exp(-tz)x),$$

where  $t \in \mathbb{R}$ ,  $f \in O(U)$  for some open set  $U \subset X$  and  $x \in U$ .

**Proposition 9.1.** The map  $a_*$  is linear and we have

$$a_*([z, w]) = [a_*(z), a_*(w)].$$

In other words, the map  $a_* : \mathfrak{g} \to \operatorname{Vect}(X)$  is a homomorphism of Lie algebras.

Exercise 9.2. Prove Proposition 9.1.

This motivates the following definition.

**Definition 9.3.** An action of a Lie algebra  $\mathfrak{g}$  on a manifold X is a homomorphism of Lie algebras  $\mathfrak{g} \to \operatorname{Vect}(X)$ .

Thus an action of a Lie group G on X induces an action of the Lie algebra  $\mathfrak{g}=\mathrm{Lie}G$  on X.

Now let  $x \in X$ . Then we have a linear map  $a_{*x} : \mathfrak{g} \to T_x X$  given by  $a_{*x}(z) := a_*(z)(x)$ .

**Theorem 9.4.** (i) The stabilizer  $G_x$  is a closed subgroup of G with Lie algebra

$$\mathfrak{g}_x := \operatorname{Ker}(a_{*x}).$$

(ii) The map  $G/G_x \to X$  given by  $g \mapsto gx$  is an immersion. So the orbit Gx is an immersed submanifold of X, and

$$T_x(Gx) \cong \operatorname{Im}(a_{*x}) \cong \mathfrak{g}/\mathfrak{g}_x.$$

Part (i) of Theorem 9.4 is the promised weaker version of Theorem 3.13 sufficient for our purposes. Also, part (ii) implies Proposition 4.12.

*Proof.* (i) It is clear that  $G_x$  is closed in G, but we need to show it is a Lie subgroup and compute its Lie algebra.<sup>8</sup> It suffices to show that for some neighborhood U of 1 in G,  $U \cap G_x$  is a (closed) submanifold of U such that  $T_1(U \cap G_x) = \mathfrak{g}_x$ .

Note that  $\mathfrak{g}_x \subset \mathfrak{g}$  is a Lie subalgebra, since the commutator of vector fields vanishing at x also vanishes at x (by the formula for commutator

<sup>&</sup>lt;sup>8</sup>Although we claimed in Theorem 3.13 that a closed subgroup of a Lie group is always a Lie subgroup, we did not prove it, so we need to prove it in this case.

in local coordinates). Also, for any  $z \in \mathfrak{g}_x$ ,  $\exp(tz)x$  is a solution of the ODE  $\gamma'(t) = a_{*\gamma(t)}(z)$  with initial condition  $\gamma(0) = x$ , and  $\gamma(t) = x$  is such a solution, so by uniqueness of ODE solutions  $\exp(tz)x = x$ , thus  $\exp(tz) \in G_x$ .

Now choose a complement  $\mathfrak{u}$  of  $\mathfrak{g}_x$  in  $\mathfrak{g}$ , so that  $\mathfrak{g} = \mathfrak{g}_x \oplus \mathfrak{u}$ . Then  $a_{*x} : \mathfrak{u} \to T_x X$  is injective. By the implicit function theorem, the map  $\mathfrak{u} \to X$  given by  $u \mapsto \exp(u)x$  is injective for small u, so  $\exp(u) \in G_x$  for small  $u \in \mathfrak{u}$  if and only if u = 0.

But in a small neighborhood U of 1 in G, any element g can be uniquely written as  $g = \exp(u) \exp(z)$ , where  $u \in \mathfrak{u}$  and  $z \in \mathfrak{g}_x$ . So we see that  $g \in G_x$  iff u = 0, i.e.,  $\log(g) \in \mathfrak{g}_x$ . This shows that  $U \cap G_x$  coincides with  $U \cap \exp(\mathfrak{g}_x)$ , as desired.

(ii) The same proof shows that we have an isomorphism  $T_1(G/G_x) \cong \mathfrak{g}/\mathfrak{g}_x = \mathfrak{u}$ , so the injectivity of  $a_{*x} : \mathfrak{u} \to T_xX$  implies that the map  $G/G_x \to X$  given by  $g \mapsto gx$  is an immersion, as claimed.

Corollary 9.5. (Proposition 4.7) Let  $\phi: G \to K$  be a morphism of Lie groups and  $\phi_*: \text{Lie}G \to \text{Lie}K$  be the corresponding morphism of Lie algebras. Then  $H:=\text{Ker}(\phi)$  is a closed normal Lie subgroup with Lie algebra  $\mathfrak{h}:=\text{Ker}(\phi_*)$ , and the map  $\overline{\phi}:G/H\to K$  is an immersion. Moreover, if  $\text{Im}\overline{\phi}$  is a submanifold of K then it is a closed Lie subgroup, and we have an isomorphism of Lie groups  $\overline{\phi}:G/H\cong \text{Im}\overline{\phi}$ .

*Proof.* Apply Theorem 9.4 to the action of G on X = K via  $g \circ k = \phi(g)k$ , and take x = 1.

**Corollary 9.6.** Let V be a finite dimensional representation of a Lie group G, and  $v \in V$ . Then the stabilizer  $G_v$  is a closed Lie subgroup of G with Lie algebra  $\mathfrak{g}_v := \{z \in \mathfrak{g} : zv = 0\}$ .

**Example 9.7.** Let A be a finite dimensional algebra (not necessarily associative, e.g. a Lie algebra). Then the group  $G = \operatorname{Aut}(A) \subset GL(A)$  is a closed Lie subgroup with Lie algebra  $\operatorname{Der}(A) \subset \operatorname{End}(A)$  of derivations of A, i.e., linear maps  $d: A \to A$  such that

$$d(ab) = d(a) \cdot b + a \cdot d(b).$$

Indeed, consider the action of GL(A) on  $Hom(A \otimes A, A)$ . Then  $G = G_{\mu}$  where  $\mu : A \otimes A \to A$  is the multiplication map. Also, if  $g_t$  is a smooth family of automorphisms of A such that  $g_0 = \operatorname{id}$  (i.e.,  $g_t(ab) = g_t(a)g_t(b)$ ) and  $d = \frac{d}{dt}|_{t=0}g_t$  then  $d(ab) = d(a) \cdot b + a \cdot d(b)$ , and conversely, if d is a derivation then  $g_t := \exp(td)$  is an automorphism.

9.2. The center of G and  $\mathfrak{g}$ . Let G be a Lie group with Lie algebra  $\mathfrak{g}$  and Z = Z(G) the center of G, i.e. the set of  $z \in G$  such that zg = gz

for all  $g \in G$ . Also let  $\mathfrak{z} = \mathfrak{z}(\mathfrak{g})$  be the set of  $x \in \mathfrak{g}$  such that [x, y] = 0 for all  $y \in \mathfrak{g}$ ; it is called the **center** of  $\mathfrak{g}$ .

**Proposition 9.8.** If G is connected then Z is a closed (normal, commutative) Lie subgroup of G with Lie algebra  $\mathfrak{z}$ .

Proof. Since G is connected, an element  $g \in G$  belongs to Z iff it commutes with  $\exp(tu)$  for all  $u \in \mathfrak{g}$ , i.e., iff  $\operatorname{Ad}_g(u) = u$ . Thus  $Z = \operatorname{Ker}(\operatorname{Ad})$ , where  $\operatorname{Ad}: G \to GL(\mathfrak{g})$  is the adjoint representation. Thus by Proposition 4.7,  $Z \subset G$  is a closed Lie subgroup with Lie algebra  $\operatorname{Ker}(\operatorname{Ad})$ , as claimed.

**Remark 9.9.** In general (when G is not necessarily connected), it is easy to show that  $G/G^{\circ}$  acts on  $\mathfrak{z}$ , and Z is a closed Lie subgroup of G with Lie algebra  $\mathfrak{z}^{G/G^{\circ}}$  (the subspace of invariant vectors).

**Definition 9.10.** For a connected Lie group G, the group G/Z(G) is called the **adjoint group** of G.

It is clear that G/Z(G) is naturally isomorphic to the image of the adjoint representation  $Ad: G \to GL(\mathfrak{g})$ , which motivates the terminology.

# 9.3. The statements of the fundamental theorems of Lie theory.

**Theorem 9.11.** (First fundamental theorem of Lie theory) For a Lie group G, there is a bijection between connected Lie subgroups  $H \subset G$  and Lie subalgebras  $\mathfrak{h} \subset \mathfrak{g} = \mathrm{Lie} G$ , given by  $\mathfrak{h} = \mathrm{Lie} H$ .

**Theorem 9.12.** (Second fundamental theorem of Lie theory) If G and K are Lie groups with G simply connected then the map

$$\operatorname{Hom}(G,K) \to \operatorname{Hom}(\operatorname{Lie}G,\operatorname{Lie}K)$$

given by  $\phi \mapsto \phi_*$  is a bijection.

**Theorem 9.13.** (Third fundamental theorem of Lie theory) Any finite dimensional Lie algebra is the Lie algebra of a Lie group.

These theorems hold for real as well as complex Lie groups. Thus we have

Corollary 9.14. For  $\mathbb{K} = \mathbb{R}$ ,  $\mathbb{C}$ , the assignment  $G \mapsto \text{Lie}G$  is an equivalence between the category of simply connected  $\mathbb{K}$ -Lie groups and the category of finite dimensional  $\mathbb{K}$ -Lie algebras. Moreover, any connected Lie group K has the form  $G/\Gamma$  where G 'is simply connected and  $\Gamma \subset G$  is a discrete central subgroup.

*Proof.* The second fundamental theorem says that the functor  $G \mapsto \text{Lie}G$  is fully faithful, and the third fundamental theorem says that it is essentially surjective. Thus it is an equivalence of categories. The last statement follows from Proposition 3.5 (G is the universal covering of K).

We will discuss proofs of the fundamental theorems of Lie theory in Subsection 10.2. The third theorem is the hardest one, and we will give its complete proof only in Section 49.

9.4. Complexification of real Lie groups and real forms of complex Lie groups. Let  $\mathfrak{k}$  be a real Lie algebra. Then  $\mathfrak{k}_{\mathbb{C}} := \mathfrak{k} \otimes_{\mathbb{R}} \mathbb{C}$  is a complex Lie algebra. We say that  $\mathfrak{g} := \mathfrak{k}_{\mathbb{C}}$  is the **complexification** of  $\mathfrak{k}$ , and  $\mathfrak{k}$  is a **real form** of  $\mathfrak{g}$ . Thus a real form of  $\mathfrak{g}$  is a real Lie subalgebra  $\mathfrak{k} \subset \mathfrak{g}$  such that the natural map  $\mathfrak{k} \otimes_{\mathbb{R}} \mathbb{C} \to \mathfrak{g}$  is an isomorphism.

In this case we have an antilinear involution  $\sigma:\mathfrak{g}\to\mathfrak{g}$  given by  $\sigma(a+ib)=a-ib$  for  $a,b\in\mathfrak{k}$ , and  $\mathfrak{k}:=\mathfrak{g}^{\sigma}$  is the set of fixed points of  $\sigma$ . Conversely, it is easy to see that if  $\sigma$  is an antilinear involution of a complex Lie algebra  $\mathfrak{g}$  (i.e., an automorphism as a real Lie algebra such that  $\sigma^2=1$  and  $\sigma(\lambda a)=\overline{\lambda}\sigma(a)$  for  $a\in\mathfrak{g},\lambda\in\mathbb{C}$ ), then  $\mathfrak{k}:=\mathfrak{g}^{\sigma}\subset\mathfrak{g}$  is a real form of  $\mathfrak{g}$ . Thus real forms of a complex Lie algebra are in natural bijection with its antilinear involutions.

Note that two non-isomorphic real Lie algebras can have isomorphic complexifications; in other words, the same complex Lie algebra can have non-isomorphic real forms. For example,

$$\mathfrak{u}(n)_{\mathbb{C}}\cong\mathfrak{gl}_n(\mathbb{R})_{\mathbb{C}}\cong\mathfrak{gl}_n(\mathbb{C})$$

while for n > 1,

$$\mathfrak{u}(n)\ncong\mathfrak{gl}_n(\mathbb{R}),$$

since in the first algebra any element x with nilpotent adx must be zero, while in the second one it does not have to.

Let us now discuss real forms of complex Lie groups. By analogy with the case of Lie algebras, we make the following definition.

**Definition 9.15.** Let G be a complex Lie group with Lie algebra  $\mathfrak{g}$  and  $\sigma: G \to G$  be an involutive automorphism of G as a real Lie group such that the induced map  $\sigma: \mathfrak{g} \to \mathfrak{g}$  is antilinear (i.e.,  $\sigma$  is antiholomorphic). Then the fixed point subgroup  $K:=G^{\sigma}$  is called a **real form** of G and G is called a **complexification** of K.

<sup>&</sup>lt;sup>9</sup>Note that this definition is not quite equivalent to Definition 3.51 in [K] of the same notion, which is less conventional. For example, according to the definition of [K], every complex elliptic curve has a real form, which does not agree with the definition from algebraic geometry (cf. Example 9.16).

Note that a real Lie group K may not admit a complexification. For example, Exercise 11.20 shows that this happens if  $K^{\circ} \cong \widetilde{SL_2}(\mathbb{R})$ , the universal cover of  $SL_2(\mathbb{R})$ . On the other hand, Example 9.16 shows that K may admit several (in fact, infinitely many) non-isomorphic complexifications.

For example, both U(n) and  $GL_n(\mathbb{R})$  are real forms of  $GL_n(\mathbb{C})$ , with  $\sigma(g) = \overline{g}$  and  $\sigma(g) = (\overline{g}^T)^{-1}$  respectively. Note that  $GL_n(\mathbb{R})$  is not connected, so a real form of a connected Lie group may be disconnected.

We see that every real form (i.e., antilinear involution) of  $\mathfrak{g}$  defines at most one such form for G. However, it could be none since the involution  $\sigma: \mathfrak{g} \to \mathfrak{g}$  may not lift to G. This is demonstrated by the following example.

Example 9.16. Let  $\Lambda \subset \mathbb{C}$  be a lattice generated by 1 and  $\tau \in \mathbb{C}$  with  $\mathrm{Im} \tau > 0$ ,  $-\frac{1}{2} < \mathrm{Re} \tau \leq \frac{1}{2}$ , and let  $E := \mathbb{C}/\Lambda$  be the corresponding complex elliptic curve (a 1-dimensional complex Lie group). We have  $\mathrm{Lie} E = \mathbb{C}$ , so the only real form of  $\mathrm{Lie} E$  is defined by the antilinear involution  $\sigma(z) = \overline{z}$ . The condition for this involution to lift to E is that  $\sigma(\Lambda) = \Lambda$ , or, equivalently,  $\overline{\tau} = a\tau + b$  for some  $a, b \in \mathbb{Z}$  coprime. Taking imaginary parts, we get that a = -1, so E has a real form if and only if  $\overline{\tau} + \tau \in \mathbb{Z}$ . This coincides with the definition of a real elliptic curve in algebraic geometry saying that E can be defined by a Weierstrass equation  $y^2 = P(x)$  where P is a cubic polynomial with real coefficients (check it!). There are two types of such elliptic curves:  $\tau \in i\mathbb{R}$  (P has one real root) and  $\tau \in \frac{1}{2} + i\mathbb{R}$  (P has three real roots). In the first case the corresponding real group  $E^{\sigma}$  is  $\mathbb{Z}/2 \times \mathbb{R}/\mathbb{Z}$  (the two components are the images of  $\mathbb{R}$  and  $\mathbb{R} + \frac{1}{2}\tau$ ), while in the second case it is  $\mathbb{R}/\mathbb{Z}$  (the image of  $\mathbb{R}$ ).

However, if G is a simply connected complex Le group, then every real form of  $\mathfrak{g}$  necessarily defines one for G. Indeed, in this case by the second fundamental theorem of Lie theory, the antilinear involution  $\sigma: \mathfrak{g} \to \mathfrak{g}$  lifts to an antiholomorphic involution  $G \to G$ .

Exercise 9.17. (i) Classify complex Lie algebras of dimension at most 3, up to isomorphism.

- (ii) Classify real Lie algebras of dimension at most 3.
- (iii) Classify connected complex and real Lie groups of dimension at most 3.

#### 10. Proofs of the fundamental theorems of Lie theory

10.1. **Distributions and the Frobenius theorem.** The proofs of the fundamental theorems of Lie theory are based on the notion of an integrable distribution in differential geometry, and the Frobenius theorem about such distributions.

**Definition 10.1.** A k-dimensional **distribution** on a manifold X is a rank k subbundle  $D \subset TX$ .

This means that in every tangent space  $T_xX$  we fix a k-dimensional subspace  $D_x$  which varies regularly with x. In other words, on some neighborhood  $U \subset X$  of every  $x \in X$ , D is spanned by vector fields  $\mathbf{v}_1, ..., \mathbf{v}_k$  linearly independent at every point of U.

**Definition 10.2.** A distribution D is **integrable** if every point  $x \in X$  has a neighborhood U and local coordinates  $x_1, ..., x_n$  on U such that D is defined at every point of U by the equations  $dx_{k+1} = ... = dx_n = 0$ , i.e., it is spanned by vector fields  $\partial_i = \frac{\partial}{\partial x_i}$ , i = 1, ..., k.

This is equivalent to saying that every point x of X is contained in an **integral submanifold** for D, i.e., an immersed submanifold  $S = S_x \subset X$  such that for any  $y \in S$  the tangent space  $T_y S \subset T_y X$  coincides with  $D_y$ . Namely,  $S_x$  is the set of all points of  $y \in X$  that can be connected to x by a smooth curve  $\gamma : [0,1] \to X$  with  $\gamma(0) = x, \gamma(1) = y$  and  $\gamma'(t) \in D_{\gamma(t)}$  for all  $t \in [0,1]$  (show it!).

For this reason an integrable distribution is also called a **foliation** and the integral submanifolds  $S_x$  are called the **sheets of the foliation**. The manifold X falls into a disjoint union of such sheets. But note that the sheets need not be closed (i.e., think of the irrational torus winding!)

**Example 10.3.** A 1-dimensional distribution is the same thing as a **direction field.** It is always integrable, as follows from the existence theorem for ODE, and its integral submanifolds are called **integral curves**. They are geometric realizations of solutions of the corresponding ODE.

However, for  $k \geq 2$  a distribution is not always integrable.

**Theorem 10.4.** (The Frobenius theorem) A distribution D is integrable if and only if for every two vector fields  $\mathbf{v}, \mathbf{w}$  contained in D, their commutator  $[\mathbf{v}, \mathbf{w}]$  is also contained in D.

**Example 10.5.** Let  $\mathbf{v} = \partial_x$ ,  $\mathbf{w} = x\partial_y + \partial_z$  in  $\mathbb{R}^3$ , and D be the 2-dimensional distribution spanned by  $\mathbf{v}$ ,  $\mathbf{w}$ . Then  $[\mathbf{v}, \mathbf{w}] = \partial_y \notin D$ . So D is not integrable.

*Proof.* If D is integrable, a vector field is contained in D iff it is tangent to integral submanifolds of D. But the commutator of two vector fields tangent to a submanifold is itself tangent to this submanifold. This establishes the "only if" part.

It remains to prove the "if" part. The proof is by induction in the rank k of D. The base case k=0 is trivial, so it suffices to establish the inductive step. The question is local, so we may work in a neighborhood U of  $P \in X$ . Suppose that  $\mathbf{v}_1, ..., \mathbf{v}_k \in \mathrm{Vect}(U)$  is a basis of D in U (on every tangent space). By local existence and uniqueness of solutions of ODE, in some local coordinates  $x_1, ..., x_n = z$ , the vector field  $\mathbf{v}_k$  equals  $\partial_z$ . By subtracting from  $\mathbf{v}_i, i < k$  a suitable multiple of  $\mathbf{v}_k$  we can make sure that  $\mathbf{v}_i$  has no  $\partial_z$ -component. Then

$$\mathbf{v}_i = \sum_{j=1}^{n-1} a_{ij}(x_1, ..., x_{n-1}, z) \partial_{x_j}.$$

Thus, since by assumption  $[\partial_z, \mathbf{v}_i] = [\mathbf{v}_k, \mathbf{v}_i]$  is a linear combination of  $\mathbf{v}_m$  with functional coefficients, we have

$$[\partial_z, \mathbf{v}_i] = \sum_{m=1}^{k-1} b_{im}(x_1, ..., x_{n-1}, z) \mathbf{v}_m$$

( $\mathbf{v}_k$  does not occur since there is no  $\partial_z$  component on the left hand side). Hence

$$\partial_z a_{ij}(x_1, ..., x_{n-1}, z) = \sum_{m=1}^{k-1} b_{im}(x_1, ..., x_{n-1}, z) a_{mj}(x_1, ..., x_{n-1}, z).$$

So, setting  $A = (a_{mj}(x_1, ..., x_{n-1}, z))$  (a  $(k-1) \times (n-1)$ -matrix) and  $B = (b_{im}(x_1, ..., x_{n-1}, z))$  (a  $(k-1) \times (k-1)$  matrix), we have

$$\partial_{\gamma}A = BA.$$

Let  $A_0$  be the solution of this linear ODE in  $(k-1) \times (k-1)$  matrices with  $A_0(x_1,...,x_{n-1},0)=1$ . Then  $A=A_0C$ , where  $C=C(x_1,...,x_{n-1})$  is a  $(k-1)\times (n-1)$ -matrix which does not depend on z. So we have a new basis of D given by  $\mathbf{w}_k=\partial_z$  and

$$\mathbf{w}_i = \sum_{j} c_{ij}(x_1, ..., x_{n-1}) \partial_{x_j}, \ 1 \le i \le k-1.$$

Thus there is a neighborhood U of P which can be represented as  $U = (-a, a) \times U'$ , where dim U' = n - 1, so that  $D = \mathbb{R} \oplus D'$ , where D' is a k - 1-dimensional distribution on U' spanned by  $\mathbf{w}_i$ ,  $1 \le i \le k - 1$ . It is clear that for any two vector fields  $\mathbf{v}$ ,  $\mathbf{w}$  on U' contained in D', so is

 $[\mathbf{v}, \mathbf{w}]$ . Hence D' is integrable by the induction assumption. Therefore, so is D, justifying the inductive step.

#### 10.2. Proofs of the fundamental theorems of Lie theory.

10.2.1. Proof of Theorem 9.11. Let G be a Lie group with Lie algebra  $\mathfrak{g}$ . Let  $\mathfrak{h} \subset \mathfrak{g}$  be a Lie subalgebra. We need to show that there is a unique (not necessarily closed) connected Lie subgroup  $H \subset G$  with Lie algebra  $\mathfrak{h}$ . The proof of existence of H is based on the Frobenius theorem.

Define the distribution D on G by left-translating  $\mathfrak{h} \subset \mathfrak{g} = T_1G$ , i.e.,  $D_g = L_g \mathfrak{h}$ . So any vector field contained in D is of the form

$$\mathbf{v} = \sum f_i \mathbf{L}_{a_i},$$

where  $a_i$  is a basis of  $\mathfrak{h}$  and  $f_i$  are regular functions. Now if

$$\mathbf{w} = \sum g_j \mathbf{L}_{a_j}$$

is another such field then

$$[\mathbf{v}, \mathbf{w}] = \sum_{i,j} (f_i \mathbf{L}_{a_i}(g_j) \mathbf{L}_{a_j} - g_j \mathbf{L}_{a_j}(f_i) \mathbf{L}_{a_i} + f_i g_j [\mathbf{L}_{a_i}, \mathbf{L}_{a_j}]).$$

But  $[a_i, a_j] = \sum_k c_{ij}^k a_k$ , so

$$[\mathbf{L}_{a_i}, \mathbf{L}_{a_j}] = \sum_k c_{ij}^k \mathbf{L}_{a_k}.$$

Thus if  $\mathbf{v}$ ,  $\mathbf{w}$  are contained in D then so is  $[\mathbf{v}, \mathbf{w}]$ . Hence by the Frobenius theorem, D is integrable.

Now consider the integral (embedded) submanifold H of D going through  $1 \in G$ . We claim that H is a Lie subgroup of G with Lie algebra  $\mathfrak{h}$ . Indeed, it suffices to show that H is a subgroup of G. But this is clear since H is the collection of elements of G of the form

$$g = \exp(a_1) \dots \exp(a_m),$$

where  $a_i \in \mathfrak{h}$ .

Moreover, H is unique since it has to be generated by the image of the exponential map  $\exp: \mathfrak{h} \to G$ .

10.2.2. Proof of Theorem 9.12. We need to show that the natural map  $\operatorname{Hom}(G,K) \to \operatorname{Hom}(\operatorname{Lie}G,\operatorname{Lie}K)$  is a bijection if G is simply connected. We know this map is injective so we only need to establish surjectivity. For any morphism  $\psi: \operatorname{Lie}G \to \operatorname{Lie}K$ , consider the morphism

$$\theta = (\mathrm{id}, \psi) : \mathrm{Lie}G \to \mathrm{Lie}(G \times K) = \mathrm{Lie}G \oplus \mathrm{Lie}K$$

The previous proposition implies that there is a connected Lie subgroup  $H \subset G \times K$  whose Lie algebra is  $\operatorname{Im} \theta$ . We have projection homomorphisms  $p_1 : H \to G$ ,  $p_2 : H \to K$ , and  $(p_1)_* = \operatorname{id}$ , so  $p_1$  is a covering. Since G is simply connected,  $p_1$  is an isomorphism, so we can define  $\phi := p_2 \circ p_1^{-1} : G \to K$ , and it is easy to see that  $\psi = \phi_*$ .

10.2.3. Proof of Theorem 9.13. Finally, let us discuss a proof of Theorem 9.13, stating that any finite dimensional Lie algebra  $\mathfrak{g}$  over  $\mathbb{K} = \mathbb{R}$  or  $\mathbb{C}$  is the Lie algebra of a Lie group. We will deduce it from the following purely algebraic Ado's theorem.

**Theorem 10.6.** Any finite dimensional Lie algebra over  $\mathbb{K}$  is a Lie subalgebra of  $\mathfrak{gl}_n(\mathbb{K})$ .

Ado's theorem in fact holds over any ground field, but it is rather nontrivial and we won't prove it now. A proof can be found, for example, in [J]. But Ado's theorem immediately implies Theorem 9.13. Indeed, using Theorem 9.11, Ado's theorem implies the following even stronger statement:

**Theorem 10.7.** Any finite dimensional  $\mathbb{K}$ -Lie algebra is the Lie algebra of a Lie subgroup of  $GL_n(\mathbb{K})$  for some n.

This implies

Corollary 10.8. Any simply connected Lie group is the universal covering of a linear Lie group, i.e., of a Lie subgroup of  $GL_n(\mathbb{K})$ .

However, it is not true that any Lie group is isomorphic to a Lie subgroup of  $GL_n(\mathbb{K})$ , see Exercise 11.20.

One can also prove Theorem 9.13 directly and then deduce Ado's theorem as a corollary. We will do this in Sections 49 and 50. We note that Theorem 9.13 will not be used in proofs of other results until that point.

#### 11. Representations of Lie groups and Lie algebras

11.1. **Representations.** We have previously defined (finite dimensional) representations of Lie groups and (iso)morphisms between them. We can do the same for Lie algebras:

**Definition 11.1.** A representation of a Lie algebra  $\mathfrak{g}$  over a field  $\mathbf{k}$  (or a  $\mathfrak{g}$ -module) is a vector space V over  $\mathbf{k}$  equipped with a homomorphism of Lie algebras  $\rho = \rho_V : \mathfrak{g} \to \mathfrak{gl}(V)$ . A (homo)morphism of representations  $A: V \to W$  (also called an intertwining operator) is a linear map which commutes with the  $\mathfrak{g}$ -action:  $A\rho_V(b) = \rho_W(b)A$  for  $b \in \mathfrak{g}$ . Such A is an isomorphism if it is an isomorphism of vector spaces.

The first and second fundamental theorems of Lie theory imply:

Corollary 11.2. Let G be a Lie group and  $\mathfrak{g} = \text{Lie}G$ .

- (i) Any finite dimensional representation  $\rho: G \to GL(V)$  gives rise to a Lie algebra representation  $\rho_*: \mathfrak{g} \to \mathfrak{gl}(V)$ , and any morphism of G-representations is also a morphism of  $\mathfrak{g}$ -representations.
- (ii) If G is connected then any morphism of  $\mathfrak{g}$ -representations is a morphism of G-representations.
- (iii) If G is simply connected then the assignment  $\rho \mapsto \rho_*$  is an equivalence of categories  $\operatorname{Rep} G \to \operatorname{Rep} \mathfrak{g}$  between the corresponding categories of finite dimensional representations. In particular, any finite dimensional representation of the Lie algebra  $\mathfrak{g}$  can be uniquely exponentiated to the group G.

**Example 11.3.** 1. The trivial representation:  $\rho(g) = 1, g \in G$ ,  $\rho_*(x) = 0, x \in \mathfrak{g}$ .

2. The adjoint representation:  $\rho(g) = \mathrm{Ad}_g$ ,  $\rho_*(x) = \mathrm{ad}x$ .

**Exercise 11.4.** Let  $\mathfrak{g}$  be a complex Lie algebra. Show that  $\mathfrak{g}_{\mathbb{C}} \cong \mathfrak{g} \oplus \mathfrak{g}$ . Deduce that if G is a simply connected complex Lie group then  $\operatorname{Rep}_{\mathbb{R}} G \cong \operatorname{Rep}(\mathfrak{g} \oplus \mathfrak{g})$ , where  $\operatorname{Rep}_{\mathbb{R}} G$  is the category of finite dimensional representations of G regarded as a real Lie group.

As usual, a **subrepresentation** of a representation V is a subspace  $W \subset V$  invariant under the G-action (resp.  $\mathfrak{g}$ -action). In this case the quotient space V/W has a natural structure of a representation, called the **quotient representation**. The notion of **direct sum** of representations is defined in an obvious way:

$$\rho_{V \oplus W}(x) = \rho_V(x) \oplus \rho_W(x).$$

Also we have the notion of **dual representation**:

$$\rho_{V^*}(g) = \rho_V(g^{-1})^*, g \in G; \ \rho_{V^*}(x) = -\rho_V(x)^*, x \in \mathfrak{g},$$

and tensor product:

$$\rho_{V \otimes W}(g) = \rho_V(g) \otimes \rho_W(g), \ \rho_{V \otimes W}(x) = \rho_V(x) \otimes 1_W + 1_V \otimes \rho_W(x).$$

Thus we have the notion of **symmetric and exterior powers**  $S^mV$ ,  $\wedge^mV$  of a representation V, which can be defined either as quotients or (over a field of characteristic zero) as subrepresentations of  $V^{\otimes n}$ . Also for representations V, W,  $\operatorname{Hom}(V, W)$  is a representation via

$$g \circ A = \rho_W(g) A \rho_V(g^{-1}), \ x \circ A = \rho_W(x) A - A \rho_V(x),$$

so if V is finite dimensional then  $\operatorname{Hom}(V,W)\cong V^*\otimes W$ . Finally, for every representation V we have the notion of invariants:

$$V^G = \{ v \in V : gv = v \ \forall g \in G \}, \ V^{\mathfrak{g}} = \{ v \in V : xv = 0 \ \forall x \in \mathfrak{g} \}.$$

Thus  $V^G \subset V^{\mathfrak{g}}$  and  $V^G = V^{\mathfrak{g}}$  for connected G (in general,  $V^G = (V^{\mathfrak{g}})^{G/G^{\circ}}$ ). Also  $\operatorname{Hom}(V,W)^G \cong \operatorname{Hom}_G(V,W)$  and  $\operatorname{Hom}(V,W)^{\mathfrak{g}} = \operatorname{Hom}_{\mathfrak{g}}(V,W)$ , the spaces of intertwining operators. Note that in all cases the formula for Lie algebras is determined by the formula for groups by the requirement that these definitions should be consistent with the assignment  $\rho \mapsto \rho_*$ .

**Definition 11.5.** A representation  $V \neq 0$  of G or  $\mathfrak{g}$  is **irreducible** if any subrepresentation  $W \subset V$  is either 0 or V and is **indecomposable** if for any decomposition  $V \cong V_1 \oplus V_2$ , we have  $V_1 = 0$  or  $V_2 = 0$ .

It is clear that any finite dimensional representation is isomorphic to a direct sum of indecomposable representations (in fact, uniquely so up to order of summands by the Krull-Schmidt theorem). However, not any V is a direct sum of irreducible representations, e.g.

$$\rho: \mathbb{C} \to GL_2(\mathbb{C}), \ \rho(x) = \begin{pmatrix} 1 & x \\ 0 & 1 \end{pmatrix}.$$

**Definition 11.6.** A representation V is called **completely reducible** if it is isomorphic to a direct sum of irreducible representations.

Some of the main problems of representation theory are:

- 1) Classify irreducible representations;
- 2) If V is a completely reducible representation, find its decomposition into irreducibles.
  - 3) For which G are all representations completely reducible?

**Example 11.7.** Let V be a finite dimensional  $\mathbb{C}$ -representation of  $\mathfrak{g}$  or G and  $A:V\to V$  be a homomorphism of representations (e.g., defined by a central element). Then we have a decomposition of representations  $V=\oplus_{\lambda}V(\lambda)$ , where  $V(\lambda)$  is the generalized eigenspace of A with eigenvalue  $\lambda$ .

**Example 11.8.** Let V be the vector representation of GL(V). Then V is irreducible, and more generally so are  $S^mV, \wedge^nV$  (show it!). Thus  $V \otimes V$  is completely reducible:  $V \otimes V \cong S^2V \oplus \wedge^2V$ .

# 11.2. Schur's lemma.

**Lemma 11.9.** (Schur's lemma) Let V, W be irreducible finite dimensional complex representations of G or  $\mathfrak{g}$ . Then  $\text{Hom}_{G,\mathfrak{g}}(V,W)=0$  if V,W are not isomorphic, and every endomorphism of the representation V is a scalar.

Proof. Let  $A:V\to W$  be a nonzero morphism of representations. Then  $\mathrm{Im}(A)\subset W$  is a nonzero subrepresentation, hence  $\mathrm{Im}(A)=W$ . Also  $\mathrm{Ker}(A)\subset V$  is a proper subrepresentation, so  $\mathrm{Ker}(A)=0$ . Thus A is an isomorphism, i.e., we may assume that W=V. In this case, let  $\lambda$  be an eigenvalue of A. Then  $A-\lambda\cdot\mathrm{Id}:V\to V$  is a morphism of representations but not an isomorphism, hence it must be zero, so  $A=\lambda\cdot\mathrm{Id}$ .

Note that the second statement of Schur's lemma (unlike the first one) does not hold over  $\mathbb{R}$ . For example, consider the rotation group SO(2) (or any of its finite subgroups of order > 2) acting on  $V = \mathbb{R}^2$  by rotations. Then  $\operatorname{End}(V) = \mathbb{C} \neq \mathbb{R}$ . Similarly, if V is the representation of SU(2) on  $\mathbb{H}$  defined by right multiplication by unit quaternions then V is an irreducible real representation but  $\operatorname{End}(V) = \mathbb{H} \neq \mathbb{R}$ . For this reason, in representation theory of Lie groups and Lie algebras one usually considers complex representations. Thus from now on all representations we consider will be assumed complex unless specified otherwise.  $^{10}$ 

**Corollary 11.10.** The center of G,  $\mathfrak{g}$  acts on an irreducible representation by a scalar. In particular, if G or  $\mathfrak{g}$  is abelian then every irreducible representation of G is 1-dimensional.

**Example 11.11.** Irreducible representations of  $\mathbb{R}$  are  $\chi_s$  given by  $\chi_s(a) = \exp(sa)$ ,  $s \in \mathbb{C}$ . Irreducible representations of  $\mathbb{R}^{\times} = \mathbb{R}_{>0} \times \mathbb{Z}/2$  are  $\chi_{s,+}(a) = |a|^s$ ,  $\chi_{s,-}(a) = |a|^s \operatorname{sign}(a)$ . Irreducible representations of  $S^1$  are  $\chi_n(z) = z^n$ ,  $n \in \mathbb{Z}$ . Irreducible representations of the real group  $\mathbb{C}^{\times} = \mathbb{R}_{>0} \times S^1$  are  $\chi_{s,n}(z) = |z|^s (z/|z|)^n$ ,  $s \in \mathbb{C}$ ,  $n \in \mathbb{Z}$ .

Corollary 11.12. Let  $V_i$  be irreducible and  $V = \bigoplus_i n_i V_i$ ,  $W = \bigoplus_i m_i V_i$  be completely reducible complex representations of G or  $\mathfrak{g}$ . Then we have a natural linear isomorphism

$$\operatorname{Hom}_{G,\mathfrak{g}}(V,W) \cong \bigoplus_{i} \operatorname{Mat}_{m_{i},n_{i}}(\mathbb{C}).$$

<sup>&</sup>lt;sup>10</sup>An exception is the adjoint representation of a real Lie group and associated tensor representations, which are real.

Moreover, if V = W then this is an isomorphism of algebras.

11.3. Unitary representations. A finite dimensional representation V of G is said to be unitary if it is equipped with a positive definite Hermitian inner product B(,) invariant under G, i.e., B(gv,gw) =B(v, w) for  $v, w \in V, g \in G$ .

**Proposition 11.13.** Any unitary representation can be written as an orthogonal direct sum of irreducible unitary representations. In particular, it is completely reducible.

*Proof.* If  $W \subset V$  is a subrepresentation of a unitary representation Vthen let  $W^{\perp}$  be its orthogonal complement under B. Then  $W^{\perp}$  is also a subrepresentation since B is invariant, and  $V = W \oplus W^{\perp}$  since B is positive definite.

Now we can prove that V is an orthogonal direct sum of irreducible unitary representations by induction in dim V. The base dim V=1 is clear so let us make the inductive step. Pick an irreducible  $W \subset V$ . Then  $V = W \oplus W^{\perp}$ , and  $W^{\perp}$  is a unitary representation of dimension smaller than  $\dim V$ , so is an orthogonal direct sum of irreducible unitary representations by the induction assumption. 

**Proposition 11.14.** Any finite dimensional representation V of a finite group G is unitary. Moreover, if V is irreducible, the unitary structure is unique up to a positive factor.

*Proof.* Let B be any positive definite inner product on V. Let

$$\widehat{B}(v,w) := \sum_{g \in G} B(gv, gw).$$

Then  $\widehat{B}$  is positive definite and invariant, so V is unitary.

If V is irreducible and  $B_1, B_2$  are two unitary structures on V then  $B_1(v,w) = B_2(Av,w)$  for some homomorphism  $A: V \to V$ . Thus by Schur's lemma  $A = \lambda \cdot \mathrm{Id}$ , and  $\lambda > 0$  since  $B_1, B_2$  are positive definite.

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

# Theorem 11.16. (i) $V_n$ is irreducible.

- (ii) If  $V \neq 0$  is a finite dimensional representation of  $\mathfrak{sl}_2$  then  $e|_V$  and  $f|_V$  are nilpotent, so  $U := \operatorname{Ker}(e) \neq 0$ . Moreover, h preserves U and acts diagonalizably on it, with nonnegative integer eigenvalues.
- (iii) Any irreducible finite dimensional representation V of  $\mathfrak{sl}_2$  is isomorphic to  $V_n$  for some n.
- (iv) Any finite dimensional representation V of  $\mathfrak{sl}_2$  is completely reducible.
- *Proof.* (i) Let  $W \subset V_n$  be a nonzero subrepresentation. Since it is h-invariant, it must be spanned by vectors  $v_{p,n-p}$  for p from a nonempty subset  $S \subset [0,n]$ . Since W is e-invariant and f-invariant, if  $m \in S$  then so are m+1, m-1 (if they are in [0,n]). Thus S=[0,n] and  $W=V_n$ .
- (ii) Let V be a finite dimensional representation of  $\mathfrak{sl}_2$ . We can write V as a direct sum of generalized eigenspaces of h:  $V = \bigoplus_{\lambda} V(\lambda)$ . Since he = e(h+2), hf = f(h-2), we have  $e: V(\lambda) \to V(\lambda+2)$ ,  $f: V(\lambda) \to V(\lambda-2)$ . Thus  $e|_V$ ,  $f|_V$  are nilpotent, so  $U \neq 0$ .

If  $v \in U$  then e(hv) = (h-2)ev = 0, so  $hv \in U$ , i.e., U is h-invariant. Given  $v \in U$ , consider the vector  $v_m := e^m f^m v$ . We have

(11.1)

$$ef^{m}v = fef^{m-1}v + hf^{m-1}v = fef^{m-1}v + f^{m-1}(h - 2(m-1))v = \dots$$
  
=  $f^{m-1}m(h - m + 1)v$ .

Thus

$$v_m = e^{m-1} f^{m-1} m(h-m+1)v = m(h-m+1)v_{m-1}.$$

Hence

$$v_m = m!h(h-1)...(h-m+1)v.$$

But for large enough m,  $v_m = 0$ , since f is nilpotent, so

$$h(h-1)...(h-m+1)v = 0.$$

Thus h acts diagonalizably on U with nonnegative integer eigenvalues. (iii) Let  $v \in U$  be an eigenvector of h, i.e.,  $hv = \lambda v$ . Let  $w_m = f^m v$ . Then

$$fw_m = w_{m+1}, hw_m = (\lambda - 2m)w_m.$$

Also, it follows from (11.1) that

$$ew_m = m(\lambda - m + 1)w_{m-1}.$$

Thus if  $w_m \neq 0$  and  $\lambda \neq m$  then  $w_{m+1} \neq 0$ . Also the nonzero vectors  $w_m$  are linearly independent since they have different eigenvalues of h. Thus  $\lambda = n$  must be a nonnegative integer (as also follows from (ii)), and  $w_{n+1} = 0$ . So V, being irreducible, has a basis  $w_m$ , m = 0, ..., n. Now it is easy to see that  $V \cong V_n$ , via the assignment

$$w_m \mapsto n(n-1)...(n-m+1)x^m y^{n-m}$$
.

(iv) Consider the Casimir operator

$$C = 2fe + \frac{h^2}{2} + h.$$

It is easy to check that [C, e] = [C, f] = [C, h] = 0, so  $C: V \to V$  is a homomorphism. Thus  $C|_{V_n} = \frac{n(n+2)}{2}$  (it is a scalar by Schur's lemma, and acts with such eigenvalue on  $v_{n0} \in V_n$ ); note that these are different for different n. For a general representation, we have  $V = \bigoplus_c V_c$ , the direct sum of generalized eigenspaces of C.

Assume V is indecomposable. Then by Example 11.7 C has a single eigenvalue c on V. Fix a **Jordan-Hölder filtration** on V, i.e. a filtration

$$0 = F_0 V \subset F_1 V \subset ... \subset F_m V = V$$

such that  $Y_i := F_i V / F_{i-1} V$  are irreducible for all i. By (iii), for each i we have  $Y_i \cong V_n$  for some n, so  $c = \frac{n(n+2)}{2}$  and thus this n is the same for all i. Thus V(k) has dimension m, with h acting on it by  $k \cdot \mathrm{Id}$  for k = n, n - 2, ..., -n and V(k) = 0 otherwise, by (ii); in particular,  $\dim V = m(n+1)$ . Let  $u_1, ..., u_m$  be a basis of V(n). As in (iii), we define subrepresentations  $W_i \subset V$  generated by  $u_i$ . It is easy to see that  $W_i \cong V_n$  and the natural morphism  $W_1 \oplus ... \oplus W_m \to V$  is injective. Hence it is an isomorphism by dimension count, i.e., V is completely reducible.

Corollary 11.17. (The Jacobson-Morozov lemma for GL(V)) Let V be a finite dimensional complex vector space and  $N: V \to V$  be a

nilpotent operator. Then there is a unique up to isomorphism action of  $\mathfrak{sl}_2$  on V for which e acts by N.

*Proof.* This follows from Theorem 11.16 and the Jordan normal form theorem for operators on V.

For a representation V define its **character** by

$$\chi_V(z) = \operatorname{Tr}_V(z^h) = \sum_m \dim V(m) z^m.$$

Thus

$$\chi_{V_n}(z) = z^n + z^{n-2} + \dots + z^{-n} = \frac{z^{n+1} - z^{-n-1}}{z - z^{-1}}.$$

It is easy to see that

$$\chi_{V \oplus W} = \chi_V + \chi_W, \chi_{V \otimes W} = \chi_V \chi_W.$$

Since the functions  $\chi_{V_n}$  are linearly independent, we see that a finite dimensional representation of  $\mathfrak{sl}_2$  is determined by its character.

Theorem 11.18. (The Clebsch-Gordan rule) We have

$$V_m \otimes V_n \cong \bigoplus_{i=0}^{\min(m,n)} V_{|m-n|+2i}.$$

*Proof.* It suffices to note that we have the corresponding character identity:

$$\chi_{V_m} \chi_{V_n} = \sum_{i=0}^{\min(m,n)} \chi_{V_{|m-n|+2i}}.$$

**Exercise 11.19.** Show that  $V_n$  has an invariant nondegenerate inner product (i.e., such that (av, w) + (v, aw) = 0 for  $a \in \mathfrak{sl}_2$ ,  $v, w \in V_n$ ) which is symmetric for even n and skew-symmetric for odd n. In particular,  $V_n^* \cong V_n$ .

**Exercise 11.20.** Let G be the universal cover of  $SL_2(\mathbb{R})$ . Show that G is not isomorphic to a Lie subgroup of  $GL_n(\mathbb{R})$  for any n and that moreover, the only quotients of G that are such subgroups are  $SL_2(\mathbb{R})$  and  $PSL_2(\mathbb{R})$ .

#### 12. The universal enveloping algebra of a Lie algebra

12.1. The definition of the universal enveloping algebra. Let V be a vector space over a field  $\mathbf{k}$ . Recall that the **tensor algebra** of V is the  $\mathbb{Z}$ -graded associative algebra  $TV := \bigoplus_{n \geq 0} V^{\otimes n}$  (with  $\deg(V^{\otimes n}) = n$ ), with multiplication given by  $a \cdot b = a \otimes b$  for  $a \in V^{\otimes m}$  and  $b \in V^{\otimes n}$ . If  $\{x_i\}$  is a basis of V then TV is just the free algebra with generators  $x_i$  (i.e., without any relations). Its basis consists of various words in the letters  $x_i$ .

Let  $\mathfrak{g}$  be a Lie algebra over  $\mathbf{k}$ .

**Definition 12.1.** The universal enveloping algebra of  $\mathfrak{g}$ , denoted  $U(\mathfrak{g})$ , is the quotient of  $T\mathfrak{g}$  by the ideal I generated by the elements  $xy - yx - [x, y], x, y \in \mathfrak{g}$ .

Recall that any associative algebra A is also a Lie algebra with operation [a,b] := ab - ba. The following proposition follows immediately from the definition of  $U(\mathfrak{g})$ .

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

**Example 12.3.** 1. If  $\mathfrak{g}$  is abelian (i.e.,  $c_{ij}^k = 0$ ) then  $U(\mathfrak{g}) = S\mathfrak{g} = \mathbf{k}[\{x_i\}]$  is the symmetric algebra of  $\mathfrak{g}$ ,  $S\mathfrak{g} = \bigoplus_{n\geq 0} S^n\mathfrak{g}$ , which in terms of the basis is the polynomial algebra in  $x_i$ .

2.  $U(\mathfrak{sl}_2(\mathbf{k}))$  is generated by e, f, h with defining relations

$$he - eh = 2e, hf - fh = -2f, ef - fe = h.$$

Recall that  $\mathfrak{g}$  acts on  $T\mathfrak{g}$  by derivations via the adjoint action. Moreover, using the Jacobi identity, we have

$$adz(xy - yx - [x, y]) = [z, x]y + x[z, y] - [z, y]x - y[z, x] - [z, [x, y]] = ([z, x]y - y[z, x] - [[z, x], y]) + (x[z, y] - [z, y]x - [x, [z, y]]).$$

Thus  $\operatorname{ad}z(I) \subset I$ , and hence the action of  $\mathfrak{g}$  on  $T\mathfrak{g}$  descends to its action on  $U(\mathfrak{g})$  by derivations (also called the adjoint action). It is easy to see that these derivations are in fact inner:

$$adz(a) = za - az$$

for  $a \in U(\mathfrak{g})$  (although this is not so for  $T\mathfrak{g}$ ). Indeed, it suffices to note that this holds for  $a \in \mathfrak{g}$  by the definition of  $U(\mathfrak{g})$ .

Thus we get

**Proposition 12.4.** The center  $Z(U(\mathfrak{g}))$  of  $U(\mathfrak{g})$  coincides with the subalgebra of invariants  $U(\mathfrak{g})^{ad\mathfrak{g}}$ .

**Example 12.5.** The Casimir operator  $C = 2fe + \frac{h^2}{2} + h$  which we used to study representations of  $\mathfrak{g} = \mathfrak{sl}_2$  is in fact a central element of  $U(\mathfrak{g})$ .

12.2. Graded and filtered algebras. Recall that a  $\mathbb{Z}_{\geq 0}$ -filtered algebra is an algebra A equipped with a filtration

$$0 = F_{-1}A \subset F_0A \subset F_1A \subset \dots \subset F_nA \subset \dots$$

such that  $1 \in F_0A$ ,  $\bigcup_{n\geq 0}F_nA = A$  and  $F_iA \cdot F_jA \subset F_{i+j}A$ . In particular, if A is generated by  $\{x_\alpha\}$  then a filtration on A can be obtained by declaring  $x_\alpha$  to be of degree 1; i.e.,  $F_nA = (F_1A)^n$  is the span of all words in  $x_\alpha$  of degree  $\leq n$ .

If  $A = \bigoplus_{i \geq 0} A_i$  is  $\mathbb{Z}_{\geq 0}$ -graded then we can define a filtration on A by setting  $F_n A := \bigoplus_{i=0}^n A_i$ ; however, not any filtered algebra is obtained in this way, and having a filtration is a weaker condition than having a grading. Still, if A is a filtered algebra, we can define its **associated graded algebra**  $\operatorname{gr}(A) := \bigoplus_{n \geq 0} \operatorname{gr}_n(A)$  (also denoted  $\operatorname{gr} A$ ),

where  $\operatorname{gr}_n(A) := F_n A / F_{n-1} A$ . The multiplication in  $\operatorname{gr}(A)$  is given by the "leading terms" of multiplication in A: for  $a \in \operatorname{gr}_i(A)$ ,  $b \in \operatorname{gr}_j(A)$ , pick their representatives  $\widetilde{a} \in F_i A$ ,  $\widetilde{b} \in F_j A$  and let ab be the projection of  $\widetilde{ab}$  to  $\operatorname{gr}_{i+j}(A)$ .

**Proposition 12.6.** If gr(A) is a domain (has no zero divisors) then so is A.

Exercise 12.7. Prove Proposition 12.6.

**Example 12.8.** Let  $\mathfrak{g}$  be a Lie algebra over  $\mathbf{k}$ . Define a filtration<sup>11</sup> on  $U(\mathfrak{g})$  by setting  $\deg(\mathfrak{g}) = 1$ . Thus  $F_nU(\mathfrak{g})$  is the image of  $\bigoplus_{i=0}^n \mathfrak{g}^{\otimes i} \subset T\mathfrak{g}$ . Note that since

$$xy - yx = [x, y], \ x \in \mathfrak{g},$$

we have  $[F_iU(\mathfrak{g}), F_jU(\mathfrak{g})] \subset F_{i+j-1}U(\mathfrak{g})$ . Thus,  $\operatorname{gr} U(\mathfrak{g})$  is commutative; in other words, we have a surjective algebra morphism

$$\phi: S\mathfrak{g} \to \operatorname{gr} U(\mathfrak{g}).$$

12.3. The coproduct of  $U(\mathfrak{g})$ . For a vector space  $\mathfrak{g}$  define the algebra homomorphism  $\Delta: T\mathfrak{g} \to T\mathfrak{g} \otimes T\mathfrak{g}$  given for  $x \in \mathfrak{g} \subset T\mathfrak{g}$  by  $\Delta(x) = x \otimes 1 + 1 \otimes x$  (it exists and is unique since  $T\mathfrak{g}$  is freely generated by  $\mathfrak{g}$ ).

**Lemma 12.9.** If  $\mathfrak{g}$  is a Lie algebra then the kernel I of the map  $T\mathfrak{g} \to U(\mathfrak{g})$  satisfies the property  $\Delta(I) \subset I \otimes T\mathfrak{g} + T\mathfrak{g} \otimes I \subset T\mathfrak{g} \otimes T\mathfrak{g}$ . Thus  $\Delta$  descends to an algebra homomorphism  $U(\mathfrak{g}) \to U(\mathfrak{g}) \otimes U(\mathfrak{g})$ .

*Proof.* For  $x, y \in \mathfrak{g}$  and a = a(x, y) := xy - yx - [x, y] we have  $\Delta(a) = a \otimes 1 + 1 \otimes a$ . The lemma follows since the ideal I is generated by elements of the form a(x, y).

The homomorphism  $\Delta$  is called the **coproduct** (of  $T\mathfrak{g}$  or  $U(\mathfrak{g})$ ).

**Example 12.10.** Let  $\mathfrak{g} = V$  be abelian (a vector space). Then  $U(\mathfrak{g}) = SV$ , which for dim  $V < \infty$  can be viewed as the algebra of polynomial functions on  $V^*$ . Similarly,  $SV \otimes SV$  is the algebra of polynomial functions on  $V^* \times V^*$ . In terms of this identification, we have  $\Delta(f)(x,y) = f(x+y)$ .

<sup>&</sup>lt;sup>11</sup>The grading on  $T\mathfrak{g}$  does not descend to  $U(\mathfrak{g})$ , in general, since the relation xy - yx = [x, y] is not homogeneous: the right hand side has degree 1 while the left hand side has degree 2. So  $U(\mathfrak{g})$  is not graded but is only filtered.

12.4. Differential operators on manifolds and Lie groups. We have seen in Subsection 5.2 that a vector field on a manifold X is the same thing as a derivation of the algebra O(U) for every open set  $U \subset X$  compatible with restriction maps  $O(U) \to O(V)$  for  $V \subset U$ ; in particular, on every U we have  $[\mathbf{v}, m_f] = m_{\mathbf{v}(f)}$  where  $f \in O(U)$  and  $m_f : O(U) \to O(U)$  is the operator of multiplication by  $f \in O(U)$ . Thus if also  $g \in O(U)$  then  $[[\mathbf{v}, m_f], m_g] = 0$ . Conversely, if A is an endomorphism of the space O(U) for every open  $U \subset X$  compatible with restriction maps and  $[[A, m_f], m_g] = 0$  for any  $f, g \in O(U)$  then  $A = \mathbf{v} + m_h$  for a unique vector field  $\mathbf{v}$  and regular function h on X (check this!). This gives rise to the following generalization of the notion of a vector field.

**Definition 12.11.** (Grothendieck) A **differential operator** of order  $\leq N$  on X is an endomorphism of the space O(U) for every open set  $U \subset X$  compatible with restriction maps  $O(U) \to O(V)$  for  $V \subset U$  such that for any  $f_0, ..., f_N \in O(U)$  one has

$$[...[A, f_0], f_1], ..., f_N] = 0.$$

It is easy to show that the latter condition is equivalent to the classical condition for a differential operator of order  $\leq N$ : in local coordinates  $(x_i)$  on a chart  $U \subset X$  the operator A looks like

$$A = \sum_{k=0}^{N} \sum_{i_1 \leq \dots \leq i_k} F_{i_1,\dots,i_k} \frac{\partial^k}{\partial x_{i_1} \dots \partial x_{i_k}},$$

where  $F_{i_1,...,i_k} \in O(U)$  (check this!). The space of such operators is denoted by  $D_N(X)$ . Thus we have a nested sequence of spaces

$$O(X) = D_0(X) \subset D_1(X) \subset ... \subset D_N(X) \subset ...$$

The nested union  $\bigcup_{N\geq 0} D_N(X)$  is a filtered associative algebra called the **algebra of differential operators on** X and denoted by D(X).

Now suppose that a Lie group G with Lie algebra  $\mathfrak{g}$  acts on X. Then we have a homomorphism of Lie algebras  $\mathfrak{g} \to \operatorname{Vect}(X)$ , which can be viewed as a Lie algebra homomorphism  $\mathfrak{g} \to D(X)$ . Thus by the universal property of the universal enveloping algebra, we obtain an associative algebra homomorphism  $\xi: U(\mathfrak{g}) \to D(X)$ . Moreover, this homomorphism preserves filtrations.

For example, if X = G and G acts by right translations, then the corresponding map  $\mathfrak{g} \to \operatorname{Vect}(G)$  identifies  $\mathfrak{g}$  with the Lie algebra  $\operatorname{Vect}_L(G)$  of left-invariant vector fields on G. Thus the map  $\xi : U(\mathfrak{g}) \to D(G)$  lands in the subalgebra  $D_L(G)$  of left-invariant differential operators on G.

**Exercise 12.12.** Show that the map  $\xi:U(\mathfrak{g})\to D_L(G)$  is a filtered algebra isomorphism.

#### 13. The Poincaré-Birkhoff-Witt theorem

13.1. The statement of the Poincaré-Birkhoff-Witt theorem. Let  $\mathfrak{g}$  be a Lie algebra over a field  $\mathbf{k}$ . Recall from Example 12.8 that we have a surjective algebra homomorphism

$$\phi: S\mathfrak{g} \to \operatorname{gr} U(\mathfrak{g}).$$

**Theorem 13.1.** (Poincaré-Birkhoff-Witt theorem) The homomorphism  $\phi$  is an isomorphism.

We will prove Theorem 13.1 in Subsection 13.2. Now let us discuss its reformulation in terms of a basis and corollaries.

Given a basis  $\{x_i\}$  of  $\mathfrak{g}$ , fix an ordering on this basis and consider ordered monomials  $\prod_i x_i^{n_i}$ , where the product is ordered according to the ordering of the basis. The statement that  $\phi$  is surjective is equivalent to saying that ordered monomials span  $U(\mathfrak{g})$ . This is also easy to see directly: any monomial can be ordered using the commutation relations at the cost of an error of lower degree, so proceeding recursively, we can write any monomial as a linear combination of ordered ones. Thus the PBW theorem can be formulated as follows:

**Theorem 13.2.** The ordered monomials are linearly independent, hence form a basis of  $U(\mathfrak{g})$ .

For instance, if  $\mathbf{k} = \mathbb{R}$  or  $\mathbb{C}$  and  $\mathfrak{g} = \text{Lie}(G)$  where G is a Lie group, this theorem is easy to deduce from Exercise 12.12 (do this!).

Corollary 13.3. The map  $\rho: \mathfrak{g} \to U(\mathfrak{g})$  is injective. Thus  $\mathfrak{g} \subset U(\mathfrak{g})$ .

**Remark 13.4.** Let  $\mathfrak{g}$  be a vector space equipped with a bilinear map  $[,]: \mathfrak{g} \times \mathfrak{g} \to \mathfrak{g}$ . Then one can define the algebra  $U(\mathfrak{g})$  as above. However, if the map  $\rho: \mathfrak{g} \to U(\mathfrak{g})$  is injective then we clearly must have [x,x]=0 for  $x\in \mathfrak{g}$  and the Jacobi identity, i.e.,  $\mathfrak{g}$  has to be a Lie algebra. Thus the PBW theorem and even Corollary 13.3 fail without the axioms of a Lie algebra.

Corollary 13.5. Let  $\mathfrak{g}_i$ ,  $1 \leq i \leq n$ , be Lie subalgebras of  $\mathfrak{g}$  such that  $\mathfrak{g} = \bigoplus_i \mathfrak{g}_i$  as a vector space (but  $[\mathfrak{g}_i, \mathfrak{g}_j]$  need not be zero). Then the multiplication map  $\otimes_i U(\mathfrak{g}_i) \to U(\mathfrak{g})$  in any order is a linear isomorphism.

*Proof.* The corollary follows immediately from the PBW theorem by choosing a basis of each  $\mathfrak{g}_i$ .

**Remark 13.6.** 1. Corollary 13.5 applies to the case of infinitely many  $\mathfrak{g}_i$  if we understand the tensor product accordingly: the span of tensor products of elements of  $U(\mathfrak{g}_i)$  where almost all of these elements are equal to 1.

2. Note that if dim  $\mathfrak{g}_i = 1$ , this recovers the PBW theorem itself, so Corollary 13.5 is in fact a generalization of the PBW theorem.

Let char( $\mathbf{k}$ ) = 0. Define the **symmetrization map**  $\sigma: S\mathfrak{g} \to U(\mathfrak{g})$  given by

$$\sigma(y_1 \otimes ... \otimes y_n) = \frac{1}{n!} \sum_{s \in S_n} y_{s(1)} ... y_{s(n)}.$$

It is easy to see that this map commutes with the adjoint action of  $\mathfrak{g}$ .

Corollary 13.7.  $\sigma$  is an isomorphism.

*Proof.* It is easy to see that  $gr\sigma$  (the induced map on the associated graded algebra) coincides with  $\phi$ , so the result follows from the PBW theorem.

Let  $Z(U(\mathfrak{g}))$  denote the center of  $U(\mathfrak{g})$ .

Corollary 13.8. The map  $\sigma$  defines a filtered vector space isomorphism  $\sigma_0: (S\mathfrak{g})^{\mathrm{ad}\mathfrak{g}} \to Z(U(\mathfrak{g}))$  whose associated graded is the algebra isomorphism  $\phi|_{(S\mathfrak{g})^{\mathrm{ad}\mathfrak{g}}}: (S\mathfrak{g})^{\mathrm{ad}\mathfrak{g}} \to \mathrm{gr} Z(U(\mathfrak{g}))$ .

In the case when  $\mathfrak{g} = \text{Lie}G$  for a connected Lie group G, we thus obtain a filtered vector space isomorphism of the center of  $U(\mathfrak{g})$  with  $(S\mathfrak{g})^{\text{Ad}G}$ .

Remark 13.9. The map  $\sigma_0$  is not, in general, an algebra homomorphism; however, a nontrivial theorem of M. Duflo says that if  $\mathfrak{g}$  is finite dimensional then there exists a canonical filtered *algebra isomorphism*  $\eta: Z(U(\mathfrak{g})) \to (S\mathfrak{g})^{\mathrm{ad}\mathfrak{g}}$  (a certain twisted version of  $\sigma_0$ ) whose associated graded is  $\phi|_{Z(U(\mathfrak{g}))}$ . A construction of the Duflo isomorphism can be found in [CR].

**Example 13.10.** Let  $\mathfrak{g} = \mathfrak{sl}_2 = \mathfrak{so}_3$ . Then  $\mathfrak{g}$  has a basis x, y, z with [x,y]=z, [y,z]=x, [z,x]=y, and G=SO(3) acts on these elements by ordinary rotations of the 3-dimensional space. So the only G-invariant polynomials of x,y,z are polynomials of  $r^2=x^2+y^2+z^2$ . Thus we get that  $Z(U(\mathfrak{g}))=\mathbb{C}[x^2+y^2+z^2]$ . In terms of e,f,h, we have

$$x^{2} + y^{2} + z^{2} = -fe - \frac{h^{2} + 2h}{4} = -\frac{C}{2},$$

where C is the Casimir element.

13.2. **Proof of the PBW theorem.** The proof of Theorem 13.1 is based on the following key lemma.

**Lemma 13.11.** There exists a unique linear map  $\varphi : T\mathfrak{g} \to S\mathfrak{g}$  such that

- (i) for an **ordered** monomial  $X := x_{i_1}...x_{i_m} \in \mathfrak{g}^{\otimes m}$  one has  $\varphi(X) = X$ ;
- (ii) one has  $\varphi(I) = 0$ ; in other words,  $\varphi$  descends to a linear map  $\overline{\varphi}: U(\mathfrak{g}) \to S\mathfrak{g}$ .

**Remark 13.12.** The map  $\varphi$  is not canonical and depends on the choice of the ordered basis  $x_i$  of  $\mathfrak{g}$ .

Note that Lemma 13.11 immediately implies the PBW theorem, since by this lemma the images of ordered monomials under  $\varphi$  are linearly independent in  $S\mathfrak{g}$ , implying that these monomials themselves are linearly independent in  $U(\mathfrak{g})$ .

*Proof.* It is clear that  $\varphi$  is unique if exists since ordered monomials span  $U(\mathfrak{g})$ . We will construct  $\varphi$  by defining it inductively on  $F_nT\mathfrak{g}$  for  $n \geq 0$ .

Suppose  $\varphi$  is already defined on  $F_{n-1}T\mathfrak{g}$  and let us extend it to  $F_nT\mathfrak{g}=F_{n-1}T\mathfrak{g}\oplus\mathfrak{g}^{\otimes n}$ . So we should define  $\varphi$  on  $\mathfrak{g}^{\otimes n}$ . Since  $\varphi$  is already defined on ordered monomials X (by  $\varphi(X)=X$ ), we need to extend this definition to all monomials.

Namely, let X be an ordered monomial of degree n, and let us define  $\varphi$  on monomials of the form s(X) for  $s \in S_n$ , where

$$s(y_1...y_n) := y_{s(1)}...y_{s(n)}.$$

To this end, fix a decomposition D of s into a product of transpositions of neighbors:

$$s = s_{j_r}...s_{j_1},$$

and define  $\varphi(s(X))$  by the formula

$$\varphi(s(X)) := X + \Phi_D(s, X),$$

where

$$\Phi_D(s,X) := \sum_{m=0}^{r-1} \varphi([,]_{j_{m+1}}(s_{j_m}...s_{j_1}(X))),$$

and

$$[,]_j(y_1...y_jy_{j+1}...y_n) := y_1...[y_j, y_{j+1}]...y_n.$$

We need to show that  $\varphi(s(X))$  is well defined, i.e.,  $\Phi_D(s, X)$  does not really depend on the choice of D and s but only on s(X). We first show that  $\Phi_D(s, X)$  is independent on D.

To this end, recall that the symmetric group  $S_n$  is generated by  $s_j, 1 \le j \le n-1$  with defining relations

$$s_j^2 = 1$$
;  $s_j s_k = s_k s_j$ ,  $|j - k| \ge 2$ ;  $s_j s_{j+1} s_j = s_{j+1} s_j s_{j+1}$ .

Thus any two decompositions of s into a product of transpositions of neighbors can be related by a sequence of applications of these relations somewhere inside the decomposition.

Now, the first relation does not change the outcome by the identity [x, y] = -[y, x].

For the second relation, suppose that j < k and we have two decompositions  $D_1, D_2$  of s given by  $s = ps_js_kq$  and  $s = ps_ks_jq$ , where q is a product of m transpositions of neighbors. Let q(X) = YabZcdT where  $a, b, c, d \in \mathfrak{g}$  stand in positions j, j + 1, k, k + 1. Let  $\Phi_1 := \Phi_{D_1}(s, X)$ ,  $\Phi_2 := \Phi_{D_2}(s, X)$ . Then the sums defining  $\Phi_1$  and  $\Phi_2$  differ only in the m-th and m + 1-th term, so we get

$$\Phi_1 - \Phi_2 =$$

 $\varphi(YabZ[c,d]T) + \varphi(Y[a,b]ZdcT) - \varphi(Y[a,b]ZcdT) - \varphi(YbaZ[c,d]T),$  which equals zero by the induction assumption.

For the third relation, suppose that we have two decompositions  $D_1, D_2$  of s given by  $s = ps_js_{j+1}s_jq$  and  $s = ps_{j+1}s_js_{j+1}q$ , where q is a product of k transpositions of neighbors. Let q(X) = YabcZ where  $a, b, c \in \mathfrak{g}$  stand in positions j, j+1, j+2. Let  $\Phi_1 := \Phi_{D_1}(s, X)$ ,  $\Phi_2 := \Phi_{D_2}(s, X)$ . Then the sums defining  $\Phi_1$  and  $\Phi_2$  differ only in the k-th, k+1-th, and k+2-th terms, so we get

$$\begin{split} \Phi_1 - \Phi_2 = \\ (\varphi(Y[a,b]cZ) + \varphi(Yb[a,c]Z) + \varphi(Y[b,c]aZ)) - \\ (\varphi(Ya[b,c]Z) + \varphi(Y[a,c]bZ) + \varphi(Yc[a,b]Z)) \,. \end{split}$$

So the Jacobi identity

$$[[b, c], a] + [b, [a, c]] + [[a, b], c] = 0$$

combined with property (ii) in degree n-1 implies that  $\Phi_1 - \Phi_2 = 0$ , i.e.,  $\Phi_1 = \Phi_2$ , as claimed. Thus we will denote  $\Phi_D(s, X)$  just by  $\Phi(s, X)$ .

It remains to show that  $\Phi(s, X)$  does not depend on the choice of s and only depends on s(X). Let  $X = x_{i_1}...x_{i_n}$ ; then s(X) = s'(X) if and only if s = s't, where t is the product of transpositions  $s_k$  for which  $i_k = i_{k+1}$ . Thus, it suffices to show that  $\Phi(s, X) = \Phi(ss_k, X)$  for such k. But this follows from the fact that [x, x] = 0.

Now, it follows from the construction of  $\varphi$  that for any monomial X of degree n (not necessarily ordered),  $\varphi(s_j(X)) = \varphi(X) + \varphi([,]_j(X))$ . Thus  $\varphi$  satisfies property (ii) in degree n. This concludes the proof of Lemma 13.11 and hence Theorem 13.1.

- 14. Free Lie algebras, the Baker-Campbell-Hausdorff formula
- 14.1. **Primitive elements.** Let  $\mathfrak{g}$  be a Lie algebra over a field  $\mathbf{k}$ . Let us say that  $x \in U(\mathfrak{g})$  is **primitive** if  $\Delta(x) = x \otimes 1 + 1 \otimes x$ . It is clear that if  $x \in \mathfrak{g} \subset U(\mathfrak{g})$  then x is primitive.
- **Lemma 14.1.** If the ground field  $\mathbf{k}$  has characteristic zero then every primitive element of  $U(\mathfrak{g})$  is contained in  $\mathfrak{g}$ .
- Proof. Let  $0 \neq f \in U(\mathfrak{g})$  be a primitive element. Suppose that the filtration degree of f is n. Let  $f_0 \in S^n \mathfrak{g}$  be the leading term of f (it is well defined by the PBW Theorem). Then  $f_0$  is primitive in  $S\mathfrak{g}$ , and in fact in SV for some finite dimensional subspace  $V \subset \mathfrak{g}$ . So  $f_0(x+y) = f_0(x) + f_0(y)$ ,  $x, y \in V^*$ . In particular,  $2^n f_0(x) = f_0(2x) = 2f_0(x)$ , so  $2^n 2 = 0$ , which implies that n = 1 as  $\operatorname{char}(\mathbf{k}) = 0$ . Thus  $f = c + f_0$  where  $f_0 \in \mathfrak{g}$ ,  $c \in \mathbf{k}$  and c = 0 since f is primitive.
- **Remark 14.2.** Note that the assumption of characteristic zero is essential. Indeed, if the characteristic of  $\mathbf{k}$  is p > 0 and  $x \in \mathfrak{g}$  then  $x^{p^i} \in U(\mathfrak{g})$  is primitive for all i.
- 14.2. Free Lie algebras. Let V be a vector space over a field  $\mathbf{k}$ . The free Lie algebra L(V) generated by V is the Lie subalgebra of TV generated by V. Note that L(V) is a  $\mathbb{Z}_{>0}$ -graded Lie algebra:  $L(V) = \bigoplus_{m \geq 1} L_m(V)$ , with grading defined by  $\deg V = 1$ ; thus  $L_m(V)$  is spanned by commutators of m-tuples of elements of V inside TV.
- **Example 14.3.** The free Lie algebra  $FL_2 = L(\mathbf{k}^2)$  in two generators x, y is generated by x, y with  $FL_2[1]$  having basis  $x, y, FL_2[2]$  having basis  $[x, y], FL_2[3]$  having basis [x, [x, y]], [y, [x, y]], etc. Similarly,  $FL_3 = L(\mathbf{k}^3)$  is generated by x, y, z with  $FL_3[1]$  having basis  $x, y, z, FL_3[2]$  having basis  $[x, y], [x, z], [y, z], FL_3[3]$  having basis [x, [x, y]], [y, [x, y]], [y, [y, z]], [z, [x, z]], [x, [x, z]], [x, [y, z]], [y, [z, x]] (note that [x, [x, y]] expresses in terms of the last two using the Jacobi identity).

The Lie algebra embedding  $L(V) \hookrightarrow TV$  gives rise to an associative algebra homomorphism  $\psi: U(L(V)) \to TV$ .

**Proposition 14.4.** (i)  $\psi$  is an isomorphism, so  $U(L(V)) \cong TV$ .

- (ii)  $\psi$  preserves the coproduct.
- (iii) (The universal property of free Lie algebras) If  $\mathfrak{g}$  is any Lie algebra over  $\mathbf{k}$  then restriction to V defines an isomorphism

$$\mathbf{res} : \mathrm{Hom}_{\mathrm{Lie}}(L(V), \mathfrak{g}) \cong \mathrm{Hom}_{\mathbf{k}}(V, \mathfrak{g}).$$

*Proof.* (i) By definition, U(L(V)) is generated by V as an associative algebra, so U(L(V)) = TV/J for some 2-sided ideal J. Moreover,

the map  $\psi: TV/J \to TV$  restricts to the identity on the space V of generators. Thus J=0 and  $\psi=\mathrm{Id}$ .

- (ii) is clear since the two coproducts agree on generators.
- (iii) Let  $a:V\to\mathfrak{g}$  be a linear map. Then a can be viewed as a linear map  $V \to U(\mathfrak{g})$ . So it extends to a map of associative algebras  $\widetilde{a}: TV \to U(\mathfrak{g})$  which restricts to a Lie algebra map  $\widehat{a}: L(V) \to \mathbb{R}$  $U(\mathfrak{g})$ . Moreover, since  $\widehat{a}(V) \subset \mathfrak{g} \subset U(\mathfrak{g})$  and L(V) is generated by V as a Lie algebra, we obtain that  $\hat{a}:L(V)\to\mathfrak{g}$ . It is easy to see that the assignment  $a \mapsto \hat{a}$  is inverse to **res**, implying that **res** is an isomorphism.

**Exercise 14.5.** Let dim V = n and  $d_m(n) = \dim L_m(V)$ . Use the PBW theorem to show that  $d_m(n)$  are uniquely determined from the identity

$$\prod_{m=1}^{\infty} (1 - q^m)^{d_m(n)} = 1 - nq.$$

14.3. The Baker-Campbell-Hausdorff formula. We have defined the commutator [x,y] on  $\mathfrak{g}=\mathrm{Lie}G$  as the quadratic part of  $\mu(x,y)=$  $\log(\exp(x)\exp(y))$ . So one may wonder if taking higher order terms in the Taylor explansion of  $\mu(x,y)$ ,

(14.1) 
$$\mu(x,y) \sim \sum_{n=1}^{\infty} \frac{\mu_n(x,y)}{n!}$$

would yield new operations on g. It turns out, however, that all these operations express via the commutator. Namely, we have

**Theorem 14.6.** For each  $n \geq 1$ ,  $\mu_n(x,y)$  may be written as a  $\mathbb{Q}$ -Lie polynomial of x, y (i.e., a  $\mathbb{Q}$ -linear combination of Lie monomials, obtained by taking successive commutators of x, y), which is universal (i.e., independent on G).

*Proof.* Expansion (14.1) is equivalent to the equality

(14.2) 
$$\exp(tx)\exp(ty) = \exp\left(\sum_{n=1}^{\infty} \frac{t^n \mu_n(x,y)}{n!}\right)$$

inside  $U(\mathfrak{g})[[t]] \subset D(G)[[t]]$  for  $x, y \in \mathfrak{g}$  (see Subsection 12.4). Let  $T\mathbb{C}^2 = \mathbb{C}\langle x,y\rangle$  be the free noncommutative algebra in the letters x,y. The series  $X = \exp(tx) := \sum_{n=0}^{\infty} \frac{x^n}{n!}$  can be viewed as an element of  $\mathbb{C}\langle x,y\rangle[[t]]$ , and similarly for  $Y:=\exp(ty)$ . Thus we may define

$$\mu := \log(XY) \in \mathbb{C}\langle x, y \rangle[[t]],$$

where

$$\log A := -\sum_{n=1}^{\infty} \frac{(1-A)^n}{n}.$$

Then  $\mu = \sum_{n=1}^{\infty} \frac{t^n \mu_n}{n!}$  where  $\mu_n \in \mathbb{C}\langle x, y \rangle$  is homogeneous of degree n. These  $\mu_n$  are the desired universal expressions, and it remains to show that they are Lie polynomials, i.e., can be expressed solely in terms of commutators.

To this end, note that since  $\Delta(x) = x \otimes 1 + 1 \otimes x$ , the element X is **grouplike**, i.e.,  $\Delta(X) = X \otimes X$  (where we extend the coproduct to the completion by continuity). The same property is shared by Y and hence by Z := XY, i.e., we have  $\Delta(Z) = Z \otimes Z$ . Thus

$$\Delta(\log Z) = \log \Delta(Z) = \log(Z \otimes Z) = \log((Z \otimes 1)(1 \otimes Z))$$
$$= \log Z \otimes 1 + 1 \otimes \log Z.$$

Thus  $\mu = \log Z$  is primitive, hence so is  $\mu_n$  for each n. Thus by Lemma 14.1,  $\mu_n \in FL_2 = L(\mathbb{C}^2)$ , where  $FL_2 \subset \mathbb{C}\langle x, y \rangle$  is the free Lie algebra generated by x, y. This implies the statement.

# Example 14.7.

$$\mu_3(x,y) = \frac{1}{2}([x,[x,y]] + [y,[y,x]]).$$

Thus

$$\mu(x,y) = x + y + \frac{1}{2}[x,y] + \frac{1}{12}([x,[x,y]] + [y,[y,x]]) + \dots$$

**Remark 14.8.** 1. The universal expressions  $\mu_n$  are unique, see Example 28.10 below.

2. E. Dynkin derived an explicit formula for  $\mu(x, y)$  making it apparent that it expresses solely in terms of commutators. Several proofs of this formula may be found in the expository paper [Mu].

# 15. Solvable and nilpotent Lie algebras, theorems of Lie and Engel

15.1. **Ideals and commutant.** Let  $\mathfrak{g}$  be a Lie algebra. Recall that an ideal in  $\mathfrak{g}$  is a subspace  $\mathfrak{h}$  such that  $[\mathfrak{g},\mathfrak{h}] \subset \mathfrak{h}$ . If  $\mathfrak{h} \subset \mathfrak{g}$  is an ideal then  $\mathfrak{g}/\mathfrak{h}$  has a natural structure of a Lie algebra. Moreover, if  $\phi: \mathfrak{g}_1 \to \mathfrak{g}_2$  is a homomorphism of Lie algebras then  $\operatorname{Ker}\phi$  is an ideal in  $\mathfrak{g}_1$ ,  $\operatorname{Im}\phi$  is a Lie subalgebra in  $\mathfrak{g}_2$ , and  $\phi$  induces an isomorphism  $\mathfrak{g}_1/\operatorname{Ker}\phi \cong \operatorname{Im}\phi$  (check it!).

**Lemma 15.1.** If  $I_1, I_2 \subset \mathfrak{g}$  are ideals then so are  $I_1 \cap I_2, I_1 + I_2$  and  $[I_1, I_2]$  (the set of linear combinations of  $[a_1, a_2]$ ,  $a_m \in I_m, m = 1, 2$ ).

Exercise 15.2. Prove Lemma 15.1.

**Definition 15.3.** The commutant of  $\mathfrak{g}$  is the ideal  $[\mathfrak{g}, \mathfrak{g}]$ .

**Lemma 15.4.** The quotient  $\mathfrak{g}/[\mathfrak{g},\mathfrak{g}]$  is abelian; moreover, if  $I \subset \mathfrak{g}$  is an ideal such that  $\mathfrak{g}/I$  is abelian then  $I \supset [\mathfrak{g},\mathfrak{g}]$ .

Exercise 15.5. Prove Lemma 15.4.

**Example 15.6.** The commutant of  $\mathfrak{gl}_n(\mathbf{k})$  is  $\mathfrak{sl}_n(\mathbf{k})$  (check it!).

**Exercise 15.7.** (i) Prove that if G is a connected Lie group with Lie algebra  $\mathfrak{g}$  then the group commutant [G,G] (the subgroup of G generated by elements  $ghg^{-1}h^{-1}$ ,  $g,h\in G$ ) is a Lie subgroup of G with Lie algebra  $[\mathfrak{g},\mathfrak{g}]$ .

(ii) Let  $\widetilde{G} = \mathbb{R} \times H$ , where H is the **Heisenberg group** of real matrices of the form

$$M(a,b,c) := \begin{pmatrix} 1 & a & b \\ 0 & 1 & c \\ 0 & 0 & 1 \end{pmatrix}, \ a,b,c \in \mathbb{R}.$$

Let  $\Gamma \cong \mathbb{Z}^2 \subset \widetilde{G}$  be the (closed) central subgroup generated by the pairs (1, M(0,0,0) = Id) and  $(\sqrt{2}, M(0,0,1))$ . Let  $G = \widetilde{G}/\Gamma$ . Show that [G, G] is not closed in G (although by (i) it is a Lie subgroup).

- (iii) Does [G, G] have to be closed in G if G is simply connected? (Consider  $\text{Hom}(G, \mathbb{R})$  and apply the second fundamental theorem of Lie theory).
- 15.2. Solvable Lie algebras. For a Lie algebra  $\mathfrak{g}$  define its derived series recursively by the formulas  $D^0(\mathfrak{g}) = \mathfrak{g}$ ,  $D^{n+1}(\mathfrak{g}) = [D^n(\mathfrak{g}), D^n(\mathfrak{g})]$ . This is a descending sequence of ideals in  $\mathfrak{g}$ .

**Definition 15.8.** A Lie algebra  $\mathfrak{g}$  is said to be **solvable** if  $D^n(\mathfrak{g}) = 0$  for some n.

**Proposition 15.9.** The following conditions on  $\mathfrak{g}$  are equivalent:

- (i)  $\mathfrak{g}$  is solvable;
- (ii) There exists a sequence of ideals  $\mathfrak{g} = \mathfrak{g}_0 \supset \mathfrak{g}_1 \supset ... \supset \mathfrak{g}_m = 0$  such that  $\mathfrak{g}_i/\mathfrak{g}_{i+1}$  is abelian.

*Proof.* It is clear that (i) implies (ii), since we can take  $\mathfrak{g}_i = D^i \mathfrak{g}$ . Conversely, by induction we see that  $D^i \mathfrak{g} \subset \mathfrak{g}_i$ , as desired.

**Proposition 15.10.** (i) Any Lie subalgebra or quotient of a solvable Lie algebra is solvable.

(ii) If  $I \subset \mathfrak{g}$  is an ideal and  $I, \mathfrak{g}/I$  are solvable then  $\mathfrak{g}$  is solvable.

Exercise 15.11. Prove Proposition 15.10.

15.3. Nilpotent Lie algebras. For a Lie algebra  $\mathfrak{g}$  define its lower central series recursively by the formulas  $D_0(\mathfrak{g}) = \mathfrak{g}$ ,  $D_{n+1}(\mathfrak{g}) = [\mathfrak{g}, D_n(\mathfrak{g})]$ . This is a descending sequence of ideals in  $\mathfrak{g}$ .

**Definition 15.12.** A Lie algebra  $\mathfrak{g}$  is said to be **nilpotent** if  $D_n(\mathfrak{g}) = 0$  for some n.

**Proposition 15.13.** The following conditions on  $\mathfrak{g}$  are equivalent:

- (i)  $\mathfrak{g}$  is nilpotent;
- (ii) There exists a sequence of ideals  $\mathfrak{g} = \mathfrak{g}_0 \supset \mathfrak{g}_1 \supset ... \supset \mathfrak{g}_m = 0$  such that  $[\mathfrak{g}, \mathfrak{g}_i] \subset \mathfrak{g}_{i+1}$ .

*Proof.* It is clear that (i) implies (ii), since we can take  $\mathfrak{g}_i = D_i \mathfrak{g}$ . Conversely, by induction we see that  $D_i \mathfrak{g} \subset \mathfrak{g}_i$ , as desired.

**Remark 15.14.** Any nilpotent Lie algebra is solvable since  $[\mathfrak{g}, \mathfrak{g}_i] \subset \mathfrak{g}_{i+1}$  implies  $[\mathfrak{g}_i, \mathfrak{g}_i] \subset \mathfrak{g}_{i+1}$ , hence  $\mathfrak{g}_i/\mathfrak{g}_{i+1}$  is abelian.

**Proposition 15.15.** Any Lie subalgebra or quotient of a nilpotent Lie algebra is nilpotent.

Exercise 15.16. Prove Proposition 15.15.

**Example 15.17.** (i) The Lie algebra of upper triangular matrices of size n is solvable, but it is not nilpotent for  $n \geq 2$ .

- (ii) The Lie algebra of strictly upper triangular matrices is nilpotent.
- (iii) The Lie algebra of all matrices of size  $n \geq 2$  is not solvable.
- 15.4. **Lie's theorem.** One of the main technical tools of the structure theory of finite dimensional Lie algebras is **Lie's theorem** for solvable Lie algebras. Before stating and proving this theorem, we will prove the following auxiliary lemma, which will be used several times.

**Lemma 15.18.** Let  $\mathfrak{g} = \mathbf{k}x \oplus \mathfrak{h}$  be a Lie algebra over a field  $\mathbf{k}$  in which  $\mathfrak{h}$  is an ideal (but  $[x,\mathfrak{h}]$  need not be 0). Let V be a finite dimensional  $\mathfrak{g}$ -module and  $v \in V$  a common eigenvector of  $\mathfrak{h}$ :

$$av = \lambda(a)v, \ a \in \mathfrak{h}$$

where  $\lambda: \mathfrak{h} \to \mathbf{k}$  is a character. Then:

- (i)  $W := \mathbf{k}[x]v$  is a  $\mathfrak{g}$ -submodule of V on which  $a \lambda(a)$  is nilpotent for all  $a \in \mathfrak{h}$ .
- (ii) If in addition  $\lambda$  vanishes on  $[\mathfrak{g},\mathfrak{h}]$  (i.e.,  $\lambda([a,x])=0$  for all  $a\in\mathfrak{h}$ ) then every  $a\in\mathfrak{h}$  acts on W by the scalar  $\lambda(a)$ . Thus the common eigenspace  $V_{\lambda}\subset V$  of  $\mathfrak{h}$  is a  $\mathfrak{g}$ -submodule.
- (iii) The assumption (hence the conclusion) of (ii) always holds if  $char(\mathbf{k}) = 0$ .

*Proof.* (i) For  $a \in \mathfrak{h}$  we have

(15.1) 
$$ax^{i}v = xax^{i-1}v + [a, x]x^{i-1}v.$$

Therefore, it follows by induction in i that  $ax^iv$  is a linear combination of  $v, xv, ..., x^iv$ , hence  $W \subset V$  is a submodule.

Let n be the smallest integer such that  $x^n v$  is a linear combination of  $x^i v$  with i < n. Then  $v_i := x^{i-1} v$  for i = 1, ..., n is a basis of W and  $\dim W = n$ . It follows from (15.1) that the element a acts in this basis by an upper triangular matrix with all diagonal entries equal  $\lambda(a)$ , as claimed.

- (ii) It follows from (15.1) by induction in i that for every  $a \in \mathfrak{h}$ ,  $ax^iv = \lambda(a)x^iv$ , as desired.
- (iii) By (i),  $\operatorname{Tr}(a|_W) = n\lambda(a)$  for all  $a \in \mathfrak{h}$ . On the other hand, if  $a \in [\mathfrak{g}, \mathfrak{g}]$  then  $\operatorname{Tr}(a|_W) = 0$ , thus  $n\lambda(a) = 0$  in  $\mathbf{k}$ . Since  $\operatorname{char}(\mathbf{k}) = 0$ , this implies that  $\lambda(a) = 0$ .

**Theorem 15.19.** (Lie's theorem) Let  $\mathbf{k}$  be an algebraically closed field of characteristic zero, and  $\mathfrak{g}$  a finite dimensional solvable Lie algebra over  $\mathbf{k}$ . Then any irreducible finite dimensional representation of  $\mathfrak{g}$  is 1-dimensional.

*Proof.* Let V be a finite dimensional representation of  $\mathfrak{g}$ . It suffices to show that V contains a common eigenvector of  $\mathfrak{g}$ . The proof is by induction in dim  $\mathfrak{g}$ . The base is trivial so let us justify the induction step. Since  $\mathfrak{g}$  is solvable,  $\mathfrak{g} \neq [\mathfrak{g}, \mathfrak{g}]$ , so fix a subspace  $\mathfrak{h} \subset \mathfrak{g}$  of codimension 1 containing  $[\mathfrak{g}, \mathfrak{g}]$ . Since  $\mathfrak{g}/[\mathfrak{g}, \mathfrak{g}]$  is abelian,  $\mathfrak{h}$  is an ideal in  $\mathfrak{g}$ , hence solvable. Thus by the induction assumption, there is a nonzero common eigenvector  $v \in V$  for  $\mathfrak{h}$ , i.e., there is a linear functional  $\lambda : \mathfrak{h} \to \mathbf{k}$  such that  $av = \lambda(a)v$  for all  $a \in \mathfrak{h}$ .

Let  $x \in \mathfrak{g}$  be an element not belonging to  $\mathfrak{h}$  and W be the subspace of V spanned by  $v, xv, x^2v, ...$  By Lemma 15.18(i), W is a  $\mathfrak{g}$ -submodule of V and  $a - \lambda(a)$  is nilpotent on W. Thus by Lemma 15.18(ii),(iii) every  $a \in \mathfrak{h}$  acts on W by  $\lambda(a)$ , in particular  $[\mathfrak{g}, \mathfrak{g}]$  acts by zero. Hence W is a representation of the abelian Lie algebra  $\mathfrak{g}/[\mathfrak{g}, \mathfrak{g}]$ . Now the statement follows since every finite dimensional representation of an abelian Lie algebra has a common eigenvector.

**Remark 15.20.** Lemma 15.18(iii) and Lie's theorem do not hold in characteristic p > 0. Indeed, let  $\mathfrak{g}$  be the Lie algebra with basis x, y and [x, y] = y, and let V be the space with basis  $v_0, ..., v_{p-1}$  and action of  $\mathfrak{g}$  given by

$$xv_i = iv_i, \ yv_i = v_{i+1},$$

where i + 1 is taken modulo p. It is easy to see that V is irreducible.

Here is another formulation of Lie's theorem:

Corollary 15.21. Every finite dimensional representation V of a finite dimensional solvable Lie algebra  $\mathfrak g$  over an algebraically closed field  $\mathbf k$  of characteristic zero has a basis in which all elements of  $\mathfrak g$  act by upper triangular matrices. In other words, there is a sequence of subrepresentations  $0 = V_0 \subset V_1 \subset ... \subset V_n = V$  such that  $\dim(V_{k+1}/V_k) = 1$ .

In the case  $\dim \mathfrak{g} = 1$ , this recovers the well known theorem in linear algebra that any linear operator on a finite dimensional **k**-vector space is upper triangular in some basis (which is actually true in any characteristic).

Proof. The proof is by induction in dim V (where the base is obvious). By Lie's theorem, there is a common eigenvector  $v_0 \in V$  for  $\mathfrak{g}$ . Let  $V' := V/\mathbf{k}v_0$ . Then by the induction assumption V' has a basis  $v'_1, ..., v'_n$  in which  $\mathfrak{g}$  acts by upper triangular matrices. Let  $v_1, ..., v_n$  be any lifts of  $v'_1, ..., v'_n$  to V. Then  $v_0, v_1, ..., v_n$  is a basis of V in which  $\mathfrak{g}$  acts by upper triangular matrices.

Corollary 15.22. Over an algebraically closed field of characteristic zero, the following hold.

- (i) A solvable finite dimensional Lie algebra  $\mathfrak{g}$  admits a sequence of ideals  $0 = I_0 \subset I_1 \subset ... \subset I_n = \mathfrak{g}$  such that  $\dim(I_{k+1}/I_k) = 1$ .
- (ii) A finite dimensional Lie algebra  $\mathfrak{g}$  is solvable if and only if  $[\mathfrak{g}, \mathfrak{g}]$  is nilpotent.
- *Proof.* (i) Apply Corollary 15.21 to the adjoint representation of g.
- (ii) If  $[\mathfrak{g},\mathfrak{g}]$  is nilpotent then it is solvable and  $\mathfrak{g}/[\mathfrak{g},\mathfrak{g}]$  is abelian, so  $\mathfrak{g}$  is solvable. Conversely, if  $\mathfrak{g}$  is solvable then by Corollary 15.21 elements

of  $[\mathfrak{g},\mathfrak{g}]$  act on  $\mathfrak{g}$ , hence on  $[\mathfrak{g},\mathfrak{g}]$  by strictly upper triangular matrices, which implies the statement.

**Example 15.23.** Let  $\mathfrak{g}, V$  be as in Remark 15.20 and  $\mathfrak{h} = \mathfrak{g} \ltimes V$  be the semidirect product, i.e.  $\mathfrak{h} = \mathfrak{g} \oplus V$  as a space with

$$[(g_1, v_1), (g_2, v_2)] = ([g_1, g_2], g_1v_2 - g_2v_1).$$

Then  $\mathfrak{h}$  is a counterexample to Corollary 15.22 both (i) and (ii) in characteristic p > 0.

15.5. **Engel's theorem.** Another key tool of the structure theory of finite dimensional Lie algebras is **Engel's theorem**. Before stating and proving this theorem, we prove an auxiliary result.

**Theorem 15.24.** Let  $V \neq 0$  be a finite dimensional vector space over any field  $\mathbf{k}$ , and  $\mathfrak{g} \subset \mathfrak{gl}(V)$  be a Lie algebra consisting of nilpotent operators. Then there exists a nonzero vector  $v \in V$  such that  $\mathfrak{g}v = 0$ .

*Proof.* The proof is by induction on the dimension of  $\mathfrak{g}$ . The base case  $\mathfrak{g} = 0$  is trivial and we assume the dimension of  $\mathfrak{g}$  is positive.

First we find an ideal  $\mathfrak{h}$  of codimension one in  $\mathfrak{g}$ . Let  $\mathfrak{h}$  be a maximal (proper) subalgebra of  $\mathfrak{g}$ , which exists by finite-dimensionality of  $\mathfrak{g}$ . We claim that  $\mathfrak{h} \subset \mathfrak{g}$  is an ideal and has codimension one.

Indeed, for each  $a \in \mathfrak{h}$ , the operator  $\mathrm{ad}a$  induces a linear operator  $\mathfrak{g}/\mathfrak{h} \to \mathfrak{g}/\mathfrak{h}$ , and this operator is nilpotent (since a acts nilpotently on V, it also acts nilpotently on  $\mathfrak{gl}(V) = V \otimes V^*$ , hence the operator  $\mathrm{ad}a : \mathfrak{g} \to \mathfrak{g}$  is nilpotent). Thus, by the inductive hypothesis, there exists a nonzero element  $\overline{x}$  in  $\mathfrak{g}/\mathfrak{h}$  such that  $\mathrm{ad}a \cdot \overline{x} = 0$  for each  $a \in \mathfrak{h}$ . Let x be a lift of  $\overline{x}$  to  $\mathfrak{g}$ . Then  $[a,x] \in \mathfrak{h}$  for all  $a \in \mathfrak{h}$ . Let  $\mathfrak{h}'$  be the span of  $\mathfrak{h}$  and x. Then  $\mathfrak{h}' \subset \mathfrak{g}$  is a Lie subalgebra in which  $\mathfrak{h}$  is an ideal. Hence, by maximality,  $\mathfrak{h}' = \mathfrak{g}$ . This proves the claim.

Now let  $W = V^{\mathfrak{h}} \subset V$ . By the inductive hypothesis,  $W \neq 0$ . Also by Lemma 15.18(ii) (with  $\lambda = 0$ ), W is a  $\mathfrak{g}$ -subrepresentation of V.

Now take  $w \neq 0$  in W. Let k be the smallest positive integer such that  $x^k w = 0$ ; it exists since x acts nilpotently on V. Let  $v = x^{k-1}w \in W$ . Then  $v \neq 0$  but  $\mathfrak{h}v = xv = 0$ , so  $\mathfrak{g}v = 0$ , as desired.  $\square$ 

**Definition 15.25.** An element  $x \in \mathfrak{g}$  is said to be **nilpotent** if the operator  $adx : \mathfrak{g} \to \mathfrak{g}$  is nilpotent.

**Corollary 15.26.** (Engel's theorem) A finite dimensional Lie algebra  $\mathfrak{g}$  is nilpotent if and only if every element  $x \in \mathfrak{g}$  is nilpotent.

*Proof.* The "only if" direction is easy. To prove the "if" direction, note that by Theorem 15.24, in some basis  $v_i$  of  $\mathfrak{g}$  all elements  $\mathrm{ad}x$  act by strictly upper triangular matrices. Let  $I_m$  be the subspace of  $\mathfrak{g}$  spanned

by the vectors  $v_1,...,v_m$ . Then  $I_m\subset I_{m+1}$  and  $[\mathfrak{g},I_{m+1}]\subset I_m$ , hence  $\mathfrak{g}$  is nilpotent.  $\square$ 

# 16. Semisimple and reductive Lie algebras, the Cartan criteria

16.1. Semisimple and reductive Lie algebras, the radical. Let  $\mathfrak{g}$  be a finite dimensional Lie algebra over a field  $\mathbf{k}$ .

**Proposition 16.1.** The sum of all solvable ideals of  $\mathfrak{g}$  is a solvable ideal.

**Definition 16.2.** This ideal is called **the radical** of  $\mathfrak{g}$  and denoted rad( $\mathfrak{g}$ ).

*Proof.* Let I, J be solvable ideals of  $\mathfrak{g}$ . Then  $I + J \subset \mathfrak{g}$  is an ideal, and  $(I + J)/I = J/(I \cap J)$  is solvable, so I + J is solvable. Thus the sum of finitely many solvable ideals is solvable. Hence the sum of all solvable ideals in  $\mathfrak{g}$  is a solvable ideal, as desired.

**Definition 16.3.** (i)  $\mathfrak{g}$  is called **semisimple** if  $rad(\mathfrak{g}) = 0$ , i.e.,  $\mathfrak{g}$  does not contain nonzero solvable ideals.

(ii) A non-abelian  $\mathfrak{g}$  is called **simple** if it contains no ideals other than  $0, \mathfrak{g}$ . In other words, a non-abelian  $\mathfrak{g}$  is simple if its adjoint representation is irreducible (=simple).

Thus if  $\mathfrak{g}$  is both solvable and semisimple then  $\mathfrak{g} = 0$ .

**Proposition 16.4.** (i) We have  $rad(\mathfrak{g} \oplus \mathfrak{h}) = rad(\mathfrak{g}) \oplus rad(\mathfrak{h})$ . In particular, the direct sum of semisimple Lie algebras is semisimple.

(ii) A simple Lie algebra is semisimple. Thus a direct sum of simple Lie algebras is semisimple.

*Proof.* (i) The images of  $rad(\mathfrak{g} \oplus \mathfrak{h})$  in  $\mathfrak{g}$  and in  $\mathfrak{h}$  are solvable, hence contained in  $rad(\mathfrak{g})$ , respectively  $rad(\mathfrak{h})$ . Thus

$$\mathrm{rad}(\mathfrak{g}\oplus\mathfrak{h})\subset\mathrm{rad}(\mathfrak{g})\oplus\mathrm{rad}(\mathfrak{h}).$$

But  $rad(\mathfrak{g}) \oplus rad(\mathfrak{h})$  is a solvable ideal in  $\mathfrak{g} \oplus \mathfrak{h}$ , so

$$\mathrm{rad}(\mathfrak{g}\oplus\mathfrak{h})=\mathrm{rad}(\mathfrak{g})\oplus\mathrm{rad}(\mathfrak{h}).$$

(ii) The only nonzero ideal in  $\mathfrak{g}$  is  $\mathfrak{g}$ , and  $[\mathfrak{g},\mathfrak{g}]=\mathfrak{g}$  since  $\mathfrak{g}$  is not abelian. Hence  $\mathfrak{g}$  is not solvable. Thus  $\mathfrak{g}$  is semisimple.

**Example 16.5.** The Lie algebra  $\mathfrak{sl}_2(\mathbf{k})$  is simple if  $\operatorname{char}(\mathbf{k}) \neq 2$ . Likewise,  $\mathfrak{so}_3(\mathbf{k})$  is simple.

**Theorem 16.6.** (weak Levi decomposition) The Lie algebra  $\mathfrak{g}_{ss} = \mathfrak{g}/\mathrm{rad}(\mathfrak{g})$  is semisimple. Thus any  $\mathfrak{g}$  can be included in an exact sequence

$$0 \to \operatorname{rad}(\mathfrak{g}) \to \mathfrak{g} \to \mathfrak{g}_{ss} \to 0,$$

where  $rad(\mathfrak{g})$  is a solvable ideal and  $\mathfrak{g}_{ss}$  is semisimple. Moreover, if  $\mathfrak{h} \subset \mathfrak{g}$  is a solvable ideal such that  $\mathfrak{g}/\mathfrak{h}$  is semisimple then  $\mathfrak{h} = rad(\mathfrak{g})$ .

*Proof.* Let  $I \subset \mathfrak{g}_{ss}$  be a solvable ideal, and let  $\widetilde{I}$  be its preimage in  $\mathfrak{g}$ . Then  $\widetilde{I}$  is a solvable ideal in  $\mathfrak{g}$ . Thus  $\widetilde{I} = \operatorname{rad}(\mathfrak{g})$  and I = 0.

In fact, in characteristic zero there is a stronger statement, which says that the extension in Theorem 16.6 splits. Namely, given a Lie algebra  $\mathfrak h$  and another Lie algebra  $\mathfrak a$  acting on  $\mathfrak h$  by derivations, we may form the **semidirect product** Lie algebra  $\mathfrak a \ltimes \mathfrak h$  which is  $\mathfrak a \oplus \mathfrak h$  as a vector space with commutator defined by

$$[(a_1, h_1), (a_2, h_2)] = ([a_1, a_2], a_1 \circ h_2 - a_2 \circ h_1 + [h_1, h_2]).$$

Note that a special case of this construction has already appeared in Example 15.23.

**Theorem 16.7.** (Levi decomposition) If  $\operatorname{char}(\mathbf{k}) = 0$  then we have  $\mathfrak{g} \cong \operatorname{rad}(\mathfrak{g}) \oplus \mathfrak{g}_{ss}$  as vector spaces, where  $\mathfrak{g}_{ss} \subset \mathfrak{g}$  is a semisimple subalgebra (but not necessarily an ideal); i.e.,  $\mathfrak{g}$  is isomorphic to the semidirect product  $\mathfrak{g}_{ss} \ltimes \operatorname{rad}(\mathfrak{g})$ . In other words, the projection  $p : \mathfrak{g} \to \mathfrak{g}_{ss}$  admits an (in general, non-unique) splitting  $q : \mathfrak{g}_{ss} \to \mathfrak{g}$ , i.e., a Lie algebra map such that  $p \circ q = \operatorname{Id}$ .

Theorem 16.7 will be proved in Subsection 48.2.

**Example 16.8.** Let G be the group of motions of the Euclidean space  $\mathbb{R}^3$  (generated by rotations and translations). Then  $G = SO_3(\mathbb{R}) \ltimes \mathbb{R}^3$ , so  $\mathfrak{g} = \text{Lie}G = \mathfrak{so}_3(\mathbb{R}) \ltimes \mathbb{R}^3$ , hence  $\text{rad}(\mathfrak{g}) = \mathbb{R}^3$  (abelian Lie algebra) and  $\mathfrak{g}_{ss} = \mathfrak{so}_3(\mathbb{R})$ .

**Proposition 16.9.** Let  $\operatorname{char}(\mathbf{k}) = 0$ ,  $\mathbf{k}$  algebraically closed, and V be an irreducible representation of  $\mathfrak{g}$ . Then  $\operatorname{rad}(\mathfrak{g})$  acts on V by scalars, and  $[\mathfrak{g}, \operatorname{rad}(\mathfrak{g})]$  by zero.

Proof. By Lie's theorem, there is a nonzero  $v \in V$  and  $\lambda \in \operatorname{rad}(\mathfrak{g})^*$  such that  $av = \lambda(a)v$  for  $a \in \operatorname{rad}(\mathfrak{g})$ . Let  $x \in \mathfrak{g}$  and  $\mathfrak{g}_x \subset \mathfrak{g}$  be the Lie subalgebra spanned by  $\operatorname{rad}(\mathfrak{g})$  and x. Let W be the span of  $x^nv$  for  $n \geq 0$ . By Lemma 15.18(i), W is a  $\mathfrak{g}_x$ -subrepresentation of V on which  $a \in \operatorname{rad}(\mathfrak{g})$  has the only eigenvalue  $\lambda(a)$ . Thus by Lemma 15.18(iii), for  $a \in \operatorname{rad}(\mathfrak{g})$  we have  $\lambda([x,a]) = 0$ , so the  $\lambda$ -eigenspace  $V_{\lambda}$  of  $\operatorname{rad}(\mathfrak{g})$  in V is a  $\mathfrak{g}$ -subrepresentation of V, which implies that  $V_{\lambda} = V$  since V is irreducible.

**Definition 16.10.**  $\mathfrak{g}$  is called **reductive** if  $rad(\mathfrak{g})$  coincides with the center  $\mathfrak{z}(\mathfrak{g})$  of  $\mathfrak{g}$ .

In other words,  $\mathfrak{g}$  is reductive if  $[\mathfrak{g}, rad(\mathfrak{g})] = 0$ .

The Levi decomposition theorem implies that a reductive Lie algebra in characteristic zero is a direct sum of a semisimple Lie algebra and an abelian Lie algebra (its center). We will also prove this in Corollary 18.8.

16.2. **Invariant inner products.** Let B be a bilinear form on a Lie algebra  $\mathfrak{g}$ . Recall that B is invariant if B([x,y],z)=B(x,[y,z]) for any  $x,y,z\in\mathfrak{g}$ .

**Example 16.11.** If  $\rho: \mathfrak{g} \to \mathfrak{gl}(V)$  is a finite dimensional representation of  $\mathfrak{g}$  then the form

$$B_V(x,y) := \operatorname{Tr}(\rho(x)\rho(y))$$

is an invariant symmetric bilinear form on  $\mathfrak{g}$ . Indeed, the symmetry is obvious and

$$B_V([x, y], z) = B_V(x, [y, z]) = \text{Tr}|_V(\rho(x)\rho(y)\rho(z) - \rho(x)\rho(z)\rho(y)).$$

**Proposition 16.12.** If B is a symmetric invariant bilinear form on  $\mathfrak{g}$  and  $I \subset \mathfrak{g}$  is an ideal then the orthogonal complement  $I^{\perp} \subset \mathfrak{g}$  is also an ideal. In particular,  $\mathfrak{g}^{\perp} = \operatorname{Ker}(B)$  is an ideal in  $\mathfrak{g}$ .

Exercise 16.13. Prove Proposition 16.12.

**Proposition 16.14.** If  $B_V$  is nondegenerate for some V then  $\mathfrak{g}$  is reductive.

*Proof.* Let  $V_1, ..., V_n$  be the simple composition factors of V; i.e., V has a filtration by subrepresentations such that  $F_iV/F_{i-1}V = V_i$ ,  $F_0V = 0$  and  $F_nV = V$ . Then  $B_V(x,y) = \sum_i B_{V_i}(x,y)$ . Now, if  $x \in [\mathfrak{g}, \operatorname{rad}(\mathfrak{g})]$  then  $x|_{V_i} = 0$ , so  $B_{V_i}(x,y) = 0$  for all  $y \in \mathfrak{g}$ , hence  $B_V(x,y) = 0$ .

**Example 16.15.** It is clear that if  $\mathfrak{g} = \mathfrak{gl}_n(\mathbf{k})$  and  $V = \mathbf{k}^n$  then the form  $B_V$  is nondegenerate, as  $B_V(E_{ij}, E_{kl}) = \delta_{il}\delta_{jk}$ . Thus  $\mathfrak{g}$  is reductive. Also if n is not divisible by the characteristic of  $\mathbf{k}$  then  $\mathfrak{sl}_n(\mathbf{k})$  is semisimple, since it is orthogonal to scalars under  $B_V$  (hence reductive), and has trivial center. In fact, it is easy to show that in this case  $\mathfrak{sl}_n(\mathbf{k})$  is a simple Lie algebra (another way to see that it is semisimple).

In fact, we have the following proposition.

**Proposition 16.16.** All classical Lie algebras over  $\mathbb{K} = \mathbb{R}$  and  $\mathbb{C}$  are reductive.

*Proof.* Let  $\mathfrak{g}$  be a classical Lie algebra and V its standard matrix representation. It is easy to check that the form  $B_V$  on  $\mathfrak{g}$  is nondegenerate, which implies that  $\mathfrak{g}$  is reductive.

For example, the Lie algebras  $\mathfrak{so}_n(\mathbb{K})$ ,  $\mathfrak{sp}_{2n}(\mathbb{K})$ ,  $\mathfrak{su}(p,q)$  have trivial center and therefore are semisimple.

# 16.3. The Killing form and the Cartan criteria.

**Definition 16.17.** The **Killing form** of a Lie algebra  $\mathfrak{g}$  is the form  $B_{\mathfrak{g}}(x,y) = \operatorname{Tr}(\operatorname{ad} x \cdot \operatorname{ad} y).$ 

The Killing form is denoted by  $K_{\mathfrak{g}}(x,y)$  or shortly by K(x,y).

**Theorem 16.18.** (Cartan criterion of solvability) A Lie algebra  $\mathfrak{g}$  over a field **k** of characteristic zero is solvable if and only if  $[\mathfrak{g},\mathfrak{g}] \subset \operatorname{Ker}(K)$ .

**Theorem 16.19.** (Cartan criterion of semisimplicity) A Lie algebra  $\mathfrak g$  over a field k of characteristic zero is semisimple if and only if its Killing form is nondegenerate.

Theorems 16.18 and 16.19 will be proved in the next section.

Corollary 16.20. On a simple Lie algebra, the Killing form is the unique up to scaling invariant bilinear form.

*Proof.* Let g be a simple Lie algebra. Then the Killing form is a nonzero (in fact, nondegenerate) invariant bilinear form on g. Also any invariant bilinear form B on  $\mathfrak{g}$  can be viewed as a homomorphism of representations  $B: \mathfrak{g} \to \mathfrak{g}^*$ . Thus by Schur's lemma it is unique up to scaling. 

16.4. **Jordan decomposition.** To prove the Cartan criteria, we will use the Jordan decomposition of a square matrix. Let us recall it.

**Proposition 16.21.** A square matrix  $A \in \mathfrak{gl}_N(\mathbf{k})$  over a field  $\mathbf{k}$  of characteristic zero can be uniquely written as  $A_s + A_n$ , where  $A_s \in$  $\mathfrak{gl}_N(\mathbf{k})$  is semisimple (i.e. diagonalizes over the algebraic closure of **k**) and  $A_n \in \mathfrak{gl}_N(\mathbf{k})$  is nilpotent in such a way that  $A_sA_n = A_nA_s$ . Moreover,  $A_s = P(A)$  for some  $P \in \mathbf{k}[x]$ .

*Proof.* By the Chinese remainder theorem, there exists a polynomial  $P \in \overline{\mathbf{k}}[x]$  such that for every eigenvalue  $\lambda$  of A we have  $P(x) = \lambda$ modulo  $(x-\lambda)^N$ , i.e.,

$$P(x) - \lambda = (x - \lambda)^N Q_{\lambda}(x)$$

for some polynomial  $Q_{\lambda}$ . Then on the generalized eigenspace  $V(\lambda)$  for A, we have

$$P(A) - \lambda = (A - \lambda)^N Q_{\lambda}(A) = 0,$$

so  $A_s := P(A)$  is semisimple and  $A_n = A - P(A)$  is nilpotent, with  $A_n A_s = A_s A_n$ . If  $A = A'_s + A'_n$  is another such decomposition then  $A'_s, A'_n$  commute with A, hence with  $A_s$  and  $A_n$ . Also we have

$$A_s - A_s' = A_n' - A_n.$$

Thus this matrix is both semisimple and nilpotent, so it is zero. Finally, since  $A_s$ ,  $A_n$  are unique, they are invariant under the Galois group of  $\overline{\mathbf{k}}$  over  $\mathbf{k}$  and therefore have entries in  $\mathbf{k}$ .

**Remark 16.22.** 1. If **k** is algebraically closed, then A admits a basis in which it is upper triangular, and  $A_s$  is the diagonal part while  $A_n$  is the off-diagonal part of A.

2. Proposition 16.21 holds with the same proof in characteristic p if the field  $\mathbf{k}$  is perfect, i.e., the Frobenius map  $x \to x^p$  is surjective on  $\mathbf{k}$ . However, if  $\mathbf{k}$  is not perfect, the proof fails: the fact that  $A_s$ ,  $A_n$  are Galois invariant does not imply that their entries are in  $\mathbf{k}$ . Also the statement fails: if  $\mathbf{k} = \mathbb{F}_p(t)$  and  $Ae_i = e_{i+1}$  for i = 1, ..., p-1 while  $Ae_p = te_1$  then A has only one eigenvalue  $t^{1/p}$ , so  $A_s = t^{1/p} \cdot \mathrm{Id}$ , i.e., does not have entries in  $\mathbf{k}$ .

# 17. Proofs of the Cartan criteria, properties of semisimple Lie algebras

17.1. Proof of the Cartan solvability criterion. It is clear that  $\mathfrak{g}$  is solvable if and only if so is  $\mathfrak{g} \otimes_{\mathbf{k}} \overline{\mathbf{k}}$ , so we may assume that  $\mathbf{k}$  is algebraically closed.

For the "only if" part, note that by Lie's theorem,  $\mathfrak{g}$  has a basis in which the operators  $\mathrm{ad} x, \, x \in \mathfrak{g}$ , are upper triangular. Then  $[\mathfrak{g}, \mathfrak{g}]$  acts in this basis by strictly upper triangular matrices, so K(x,y) = 0 for  $x \in [\mathfrak{g}, \mathfrak{g}]$  and  $y \in \mathfrak{g}$ .

To prove the "if" part, let us prove the following lemma.

**Lemma 17.1.** Let  $\mathfrak{g} \subset \mathfrak{gl}(V)$  be a Lie subalgebra such that for any  $x \in [\mathfrak{g}, \mathfrak{g}]$  and  $y \in \mathfrak{g}$  we have  $\operatorname{Tr}(xy) = 0$ . Then  $\mathfrak{g}$  is solvable.

*Proof.* Let  $x \in [\mathfrak{g}, \mathfrak{g}]$ . Let  $\lambda_i, i = 1, ..., m$ , be the distinct eigenvalues of x. Let  $E \subset \mathbf{k}$  be a  $\mathbb{Q}$ -span of  $\lambda_i$ . Let  $b : E \to \mathbb{Q}$  be a linear functional. There exists an interpolation polynomial  $Q \in \mathbf{k}[t]$  such that  $Q(\lambda_i - \lambda_j) = b(\lambda_i - \lambda_j) = b(\lambda_i) - b(\lambda_j)$  for all i, j.

By Proposition 16.21, we can write x as  $x = x_s + x_n$ . Then the operator  $adx_s$  is diagonalizable with eigenvalues  $\lambda_i - \lambda_j$ . So

$$Q(\mathrm{ad}x_s) = \mathrm{ad}b,$$

where  $b: V \to V$  is the operator acting by  $b(\lambda_j)$  on the generalized  $\lambda_j$ -eigenspace of x.

Also we have

$$adx = adx_s + adx_n$$

a sum of commuting semisimple and nilpotent operators. Thus

$$adx_s = (adx)_s = P(adx),$$

and P(0) = 0 since 0 is an eigenvalue of adx. Thus

$$adb = R(adx),$$

where R(t) = Q(P(t)) and R(0) = 0.

Let  $x = \sum_j [y_j, z_j], y_j, z_j \in \mathfrak{g}$ , and  $d_j$  be the dimension of the generalized  $\lambda_j$ -eigenspace of x. Then

$$\sum_{j} d_{j}b(\lambda_{j})\lambda_{j} = \operatorname{Tr}(bx) =$$

$$\operatorname{Tr}(\sum_{j} b[y_j, z_j]) = \operatorname{Tr}(\sum_{j} [b, y_j] z_j) = \operatorname{Tr}(\sum_{j} R(\operatorname{ad} x)(y_j) z_j).$$

Since R(0) = 0, we have  $R(adx)(y_j) \in [\mathfrak{g}, \mathfrak{g}]$ , so by assumption we get

$$\sum_{j} d_j b(\lambda_j) \lambda_j = 0.$$

Applying b, we get  $\sum_j d_j b(\lambda_j)^2 = 0$ . Thus  $b(\lambda_j) = 0$  for all j. Hence b = 0, so E = 0.

Thus, the only eigenvalue of x is 0, i.e., x is nilpotent. But then by Engel's theorem,  $[\mathfrak{g},\mathfrak{g}]$  is nilpotent. Thus  $\mathfrak{g}$  is solvable. Thus proves the lemma.

Now the "if" part of the Cartan solvability criterion follows easily by applying Lemma 17.1 to  $V = \mathfrak{g}$  and replacing  $\mathfrak{g}$  by the quotient  $\mathfrak{g}/\mathfrak{z}(\mathfrak{g})$ .

17.2. Proof of the Cartan semisimplicity criterion. Assume that  $\mathfrak{g}$  is semisimple, and let  $I = \operatorname{Ker}(K_{\mathfrak{g}})$ , an ideal in  $\mathfrak{g}$ . Then  $K_I = (K_{\mathfrak{g}})|_{I} = 0$ . Thus by Cartan's solvability criterion I is solvable. Hence I = 0

Conversely, suppose  $K_{\mathfrak{g}}$  is nondegenerate. Then  $\mathfrak{g}$  is reductive. Moreover, the center of  $\mathfrak{g}$  is contained in the kernel of  $K_{\mathfrak{g}}$ , so it must be trivial. Thus  $\mathfrak{g}$  is semisimple.

# 17.3. Properties of semisimple Lie algebras.

**Proposition 17.2.** Let  $\operatorname{char}(\mathbf{k}) = 0$  and  $\mathfrak{g}$  be a finite dimensional Lie algebra over  $\mathbf{k}$ . Then  $\mathfrak{g}$  is semisimple iff  $\mathfrak{g} \otimes_{\mathbf{k}} \overline{\mathbf{k}}$  is semisimple.

*Proof.* Immediately follows from Cartan's criterion of semisimplicity. Here is another proof (of the nontrivial direction): if  $\mathfrak{g}$  is semisimple and I is a nonzero solvable ideal in  $\mathfrak{g} \otimes_{\mathbf{k}} \overline{\mathbf{k}}$  then it has a finite Galois orbit  $I_1, ..., I_n$  and  $I_1 + ... + I_n$  is a Galois invariant solvable ideal, so it comes from a solvable ideal in  $\mathfrak{g}$ .

**Remark 17.3.** This theorem fails if we replace the word "semisimple" by "simple": e.g., if  $\mathfrak{g}$  is a simple complex Lie algebra regarded as a real Lie algebra then  $\mathfrak{g}_{\mathbb{C}} \cong \mathfrak{g} \oplus \mathfrak{g}$  is semisimple but not simple.

**Theorem 17.4.** Let  $\mathfrak{g}$  be a semisimple Lie algebra and  $I \subset \mathfrak{g}$  an ideal. Then there is an ideal  $J \subset \mathfrak{g}$  such that  $\mathfrak{g} = I \oplus J$ .

*Proof.* Let  $I^{\perp}$  be the orthogonal complement of I with respect to the Killing form, an ideal in  $\mathfrak{g}$ . Consider the intersection  $I \cap I^{\perp}$ . It is an ideal in  $\mathfrak{g}$  with the zero Killing form. Thus, by the Cartan solvability criterion, it is solvable. By definition of a semisimple Lie algebra, this means that  $I \cap I^{\perp} = 0$ , so we may take  $J = I^{\perp}$ .

We will see below (in Proposition 17.7) that J is in fact unique and must equal  $I^{\perp}$ .

Corollary 17.5. A Lie algebra  $\mathfrak{g}$  is semisimple iff it is a direct sum of simple Lie algebras.

*Proof.* We have already shown that a direct sum of simple Lie algebras is semisimple. The opposite direction easily follows by induction from Theorem 17.4.  $\Box$ 

Corollary 17.6. If  $\mathfrak{g}$  is a semisimple Lie algebra, then  $[\mathfrak{g},\mathfrak{g}] = \mathfrak{g}$ .

*Proof.* For a simple Lie algebra it is clear because  $[\mathfrak{g}, \mathfrak{g}]$  is an ideal in  $\mathfrak{g}$  which cannot be zero (otherwise,  $\mathfrak{g}$  would be abelian). So the result follows from Corollary 17.5.

**Proposition 17.7.** Let  $\mathfrak{g} = \mathfrak{g}_1 \oplus ... \oplus \mathfrak{g}_k$  be a semisimple Lie algebra, with  $\mathfrak{g}_i$  being simple. Then any ideal I in  $\mathfrak{g}$  is of the form  $I = \bigoplus_{i \in S} \mathfrak{g}_i$  for some subset  $S \subset \{1, ..., k\}$ .

Proof. The proof goes by induction in k. Let  $p_k: \mathfrak{g} \to \mathfrak{g}_k$  be the projection. Consider  $p_k(I) \subset \mathfrak{g}_k$ . Since  $\mathfrak{g}_k$  is simple, either  $p_k(I) = 0$ , in which case  $I \subset \mathfrak{g}_1 \oplus ... \oplus \mathfrak{g}_{k-1}$  and we can use the induction assumption, or  $p_k(I) = \mathfrak{g}_k$ . Then  $[\mathfrak{g}_k, I] = [\mathfrak{g}_k, p_k(I)] = \mathfrak{g}_k$ . Since I is an ideal,  $I \supset \mathfrak{g}_k$ , so  $I = I' \oplus \mathfrak{g}_k$  for some subspace  $I' \subset \mathfrak{g}_1 \oplus \mathfrak{g}_{k-1}$ . It is immediate that then I' is an ideal in  $\mathfrak{g}_1 \oplus \mathfrak{g}_{k-1}$  and the result again follows from the induction assumption.

Corollary 17.8. Any ideal in a semisimple Lie algebra is semisimple. Also, any quotient of a semisimple Lie algebra is semisimple.

Let Derg be the Lie algebra of derivations of a Lie algebra  $\mathfrak{g}$ . We have a homomorphism  $\mathrm{ad}:\mathfrak{g}\to\mathrm{Derg}$  whose kernel is the center  $\mathfrak{z}(\mathfrak{g})$ . Thus if  $\mathfrak{g}$  has trivial center (e.g., is semisimple) then the map ad is injective and identifies  $\mathfrak{g}$  with a Lie subalgebra of Derg. Moreover, for  $d\in\mathrm{Derg}$  and  $x\in\mathfrak{g}$ , we have

$$[d, adx](y) = d[x, y] - [x, dy] = [dx, y] = ad(dx)(y).$$

Thus  $\mathfrak{g} \subset \operatorname{Der}\mathfrak{g}$  is an ideal.

Proposition 17.9. If  $\mathfrak{g}$  is semisimple then  $\mathfrak{g} = \operatorname{Der} \mathfrak{g}$ .

*Proof.* Consider the invariant symmetric bilinear form

$$K(a,b) = \operatorname{Tr}|_{\mathfrak{g}}(ab)$$

on Derg. This is an extension of the Killing form of  $\mathfrak{g}$  to Derg, so its restriction to  $\mathfrak{g}$  is nondegenerate. Let  $I = \mathfrak{g}^{\perp}$  be the orthogonal complement of  $\mathfrak{g}$  in Derg under K. It follows that I is an ideal,  $I \cap \mathfrak{g} = 0$ , and  $I \oplus \mathfrak{g} = \text{Derg}$ . Since both I and  $\mathfrak{g}$  are ideals, we have  $[\mathfrak{g}, I] = 0$ . Thus for  $d \in I$  and  $x \in \mathfrak{g}$ , [d, adx] = ad(dx) = 0, so dx belongs to

the center of  $\mathfrak{g}$ . Thus dx=0, i.e., d=0. It follows that I=0, as claimed.  $\square$ 

Corollary 17.10. Let  $\mathfrak{g}$  be a real or complex semisimple Lie algebra, and  $G = \operatorname{Aut}(\mathfrak{g}) \subset GL(\mathfrak{g})$ . Then G is a Lie group with  $\operatorname{Lie} G = \mathfrak{g}$ . Thus G acts on  $\mathfrak{g}$  by the adjoint action.

*Proof.* It is easy to show that for any finite dimensional real or complex Lie algebra  $\mathfrak{g}$ ,  $\operatorname{Aut}(\mathfrak{g})$  is a Lie group with Lie algebra  $\operatorname{Der}(\mathfrak{g})$ , so the statement follows from Proposition 17.9.

# 18. Extensions of representations, Whitehead's theorem, complete reducibility

18.1. Extensions. Let  $\mathfrak{g}$  be a Lie algebra and U, W be representations of  $\mathfrak{g}$ . We would like to classify all representations V which fit into a short exact sequence

$$(18.1) 0 \to U \to V \to W \to 0,$$

i.e.,  $U \subset V$  is a subrepresentation such that the surjection  $p: V \to W$ has kernel U and thus defines an isomorphism  $V/U \cong W$ . In other words, V is endowed with a 2-step filtration with  $F_0V = U$  and  $F_1V =$ V such that  $F_1V/F_0V=W$ , so  $gr(V)=U\oplus W$ . To do so, pick a splitting of this sequence as a sequence of vector spaces, i.e. an injection  $i: W \to V$  (not a homomorphism of representations, in general) such that  $p \circ i = \mathrm{Id}_W$ . This defines a linear isomorphism  $i : U \oplus W \to V$ given by  $(u, w) \mapsto u + i(w)$ , which allows us to rewrite the action of  $\mathfrak{g}$ on V as an action on  $U \oplus W$ . Since i is not in general a morphism of representations, this action is given by

$$\rho(x)(u, w) = (xu + a(x)w, xw)$$

where  $a: \mathfrak{g} \to \operatorname{Hom}_{\mathbf{k}}(W,U)$  is a linear map, and  $\widetilde{i}$  is a morphism of representations iff a=0.

What are the conditions on a to give rise to a representation? We compute:

$$\rho([x,y])(u,w) = ([x,y]u + a([x,y])w, [x,y]w),$$

$$[\rho(x),\rho(y)](u,w) = ([x,y]u + ([x,a(y)] + [a(x),y])w, [x,y]w).$$

Thus the condition to give a representation is the Leibniz rule

$$a([x,y]) = [x,a(y)] + [a(x),y] = [x,a(y)] - [y,a(x)].$$

In general, if E is a representation of g then a linear function  $a: \mathfrak{g} \to E$ such that

$$a([x,y]) = x \circ a(y) - y \circ a(x)$$

is called a  $1 - \mathbf{cocycle}$  of  $\mathfrak{g}$  with values in E. The space of 1-cocycles is denoted by  $Z^1(\mathfrak{g}, E)$ .

**Example 18.1.** We have 
$$Z^1(\mathfrak{g}, \mathbf{k}) = (\mathfrak{g}/[\mathfrak{g}, \mathfrak{g}])^*$$
 and  $Z^1(\mathfrak{g}, \mathfrak{g}) = \text{Der}\mathfrak{g}$ .

Thus we see that in our setting  $a: \mathfrak{g} \to \operatorname{Hom}_{\mathbf{k}}(W,U)$  defines a representation if and only if  $a \in Z^1(\mathfrak{g}, \operatorname{Hom}_{\mathbf{k}}(W, U))$ . Denote the representation V attached to such a by  $V_a$ . Then we have a natural short exact sequence

$$0 \to U \to V_a \to W \to 0.$$

It may, however, happen that some  $a \neq 0$  defines a trivial extension  $V \cong U \oplus W$ , i.e.,  $V_a \cong V_0$ , and more generally  $V_a \cong V_b$  for  $a \neq b$ . Let us determine when this happens. More precisely, let us look for isomorphisms  $f: V_a \to V_b$  preserving the structure of the short exact sequences, i.e., such that gr(f) = Id. Then

$$f(u, w) = (u + Aw, w)$$

where  $A:W\to U$  is a linear map. Then we have

$$xf(u,w) = x(u + Aw, w) = (xu + xAw + b(x)w, xw)$$

and

$$fx(u, w) = f(xu + a(x)w, xw) = (xu + a(x)w + Axw, xw),$$

so we get that xf = fx iff

$$[x, A] = a(x) - b(x).$$

In particular, setting b=0, we see that V is a trivial extension if and only if a(x) = [x, A] for some A.

More generally, if E is a  $\mathfrak{g}$ -module, the linear function  $a:\mathfrak{g}\to E$ given by a(x) = xv for some  $v \in E$  is called the **1-coboundary** of v, and one writes a = dv. The space of 1-coboundaries is denoted by  $B^1(\mathfrak{g}, E)$ ; it is easy to see that it is a subspace of  $Z^1(\mathfrak{g}, E)$ , i.e., a 1-coboundary is always a 1-cocycle. Thus in our setting  $f: V_a \to V_b$  is an isomorphism of representations iff

$$a - b = dA$$
.

i.e., there is an isomorphism  $f: V_a \cong V_b$  with gr(f) = Id if and only if a = b in the quotient space

$$\operatorname{Ext}^{1}(W,U) := Z^{1}(\mathfrak{g}, \operatorname{Hom}_{\mathbf{k}}(W,U))/B^{1}(\mathfrak{g}, \operatorname{Hom}_{\mathbf{k}}(W,U)).$$

The notation is justified by the fact that this space parametrizes extensions of W by U. More precisely, every short exact sequence (18.1)gives rise to a class  $[V] \in \operatorname{Ext}^1(W, U)$ , and the extension defined by this sequence is trivial iff [V] = 0.

More generally, for a  $\mathfrak{g}$ -module E the space

$$H^1(\mathfrak{g}, E) := Z^1(\mathfrak{g}, E)/B^1(\mathfrak{g}, E)$$

is called the **first cohomology** of  $\mathfrak{g}$  with coefficients in E. Thus,

$$\operatorname{Ext}^{1}(W, U) = H^{1}(\mathfrak{g}, \operatorname{Hom}_{\mathbf{k}}(W, U)).$$

**Lemma 18.2.** A short exact sequence  $0 \to U \to V \to W \to 0$  gives rise to an exact sequence

$$H^1(\mathfrak{g},U) \to H^1(\mathfrak{g},V) \to H^1(\mathfrak{g},W).$$

Exercise 18.3. Prove Lemma 18.2.

18.2. Whitehead's theorem. We have shown in Corollary 17.6 and Proposition 17.9 that for a semisimple  $\mathfrak{g}$  over a field of characteristic zero,  $H^1(\mathfrak{g}, \mathbf{k}) = (\mathfrak{g}/[\mathfrak{g}, \mathfrak{g}])^* = 0$ , and  $H^1(\mathfrak{g}, \mathfrak{g}) = \mathrm{Der}\mathfrak{g}/\mathfrak{g} = 0$ . In fact, these are special cases of a more general theorem.

**Theorem 18.4.** (Whitehead) If  $\mathfrak{g}$  is semisimple in characteristic zero then for every finite dimensional representation V of  $\mathfrak{g}$ ,  $H^1(\mathfrak{g}, V) = 0$ .

18.3. **Proof of Theorem 18.4.** We will use the following lemma, which holds over any field.

**Lemma 18.5.** Let E be a representation of a Lie algebra  $\mathfrak{g}$  and  $C \in U(\mathfrak{g})$  be a central element which acts by 0 on the trivial representation of  $\mathfrak{g}$  and by some scalar  $\lambda \neq 0$  on E. Then  $H^1(\mathfrak{g}, E) = 0$ .

*Proof.* We have seen that  $H^1(\mathfrak{g}, E) = \operatorname{Ext}^1(\mathbf{k}, E)$ , so our job is to show that any extension

$$0 \to E \to V \to \mathbf{k} \to 0$$

splits. Let  $p: V \to \mathbf{k}$  be the projection. We claim that there exists a unique vector  $v \in V$  such that p(v) = 1 and Cv = 0. Indeed, pick some  $w \in V$  with p(w) = 1. Then  $Cw \in E$ , so set  $v = w - \lambda^{-1}Cw$ . Since  $C^2w = \lambda Cw$ , we have Cv = 0. Also if v' is another such vector then  $v - v' \in E$  so  $C(v - v') = \lambda(v - v') = 0$ , hence v = v'.

Thus  $\mathbf{k}v \subset V$  is a  $\mathfrak{g}$ -invariant complement to E (as C is central), which implies the statement.

It remains to construct a central element of  $U(\mathfrak{g})$  for a semisimple Lie algebra  $\mathfrak{g}$  to which we can apply Lemma 18.5. This can be done as follows. Let  $a_i$  be a basis of  $\mathfrak{g}$  and  $a^i$  the dual basis under an invariant inner product on  $\mathfrak{g}$  (for example, the Killing form). Define the (quadratic) Casimir element

$$C := \sum_{i} a_i a^i.$$

It is easy to show that C is independent on the choice of the basis (although it depends on the choice of the inner product). Also C is central: for  $y \in \mathfrak{g}$ ,

$$[y, C] = \sum_{i} ([y, a_i]a^i + a_i[y, a^i]) = 0$$

since

$$\sum_{i} ([y, a_i] \otimes a^i + a_i \otimes [y, a^i]) = 0$$

(this is seen by taking the inner product of the first tensorand with  $a^j$  and using the invariance of the inner product). Finally, note that for  $\mathfrak{g} = \mathfrak{sl}_2$ , C is proportional to the Casimir element  $2fe + \frac{h^2}{2} + h = ef + fe + \frac{h^2}{2}$  considered previously, as the basis  $f, e, \frac{h}{\sqrt{2}}$  is dual to the basis  $e, f, \frac{h}{\sqrt{2}}$  under an invariant inner product of  $\mathfrak{g}$ .

The key lemma used in the proof of Theorem 18.4 is the following.

**Lemma 18.6.** Let  $\mathfrak{g}$  be semisimple in characteristic zero and V be a nontrivial finite dimensional irreducible  $\mathfrak{g}$ -module. Then there is a central element  $C \in U(\mathfrak{g})$  such that  $C|_{\mathbf{k}} = 0$  and  $C|_{V} \neq 0$ .

*Proof.* Consider the invariant symmetric bilinear form on g

$$B_V(x,y) = \text{Tr}|_V(xy).$$

We claim that  $B_V \neq 0$ . Indeed, let  $\bar{\mathfrak{g}} \subset \mathfrak{gl}(V)$  be the image of  $\mathfrak{g}$ . By Lemma 17.1, if  $B_V = 0$  then  $\bar{\mathfrak{g}}$  is solvable, so, being the quotient of a semisimple Lie algebra  $\mathfrak{g}$ , it must be zero, hence V is trivial, a contradiction.

Let  $I = \operatorname{Ker}(B_V)$ . Then  $I \subset \mathfrak{g}$  is an ideal, so by Proposition 17.7,  $\mathfrak{g} = I \oplus \mathfrak{g}'$  for some semisimple Lie algebra  $\mathfrak{g}'$ , and  $B_V$  is nondegenerate on  $\mathfrak{g}'$ . Let C be the Casimir element of  $U(\mathfrak{g}')$  corresponding to the inner product  $B_V$ . Then  $\operatorname{Tr}_V(C) = \sum_i B_V(a_i, a^i) = \dim \mathfrak{g}'$ , so  $C|_V = \frac{\dim \mathfrak{g}'}{\dim V} \neq 0$ . Also it is clear that  $C|_{\mathbf{k}} = 0$ , so the lemma follows.  $\square$ 

Corollary 18.7. For any irreducible finite dimensional representation V of a semisimple Lie algebra  $\mathfrak{g}$  over a field  $\mathbf{k}$  of characteristic zero, we have  $H^1(\mathfrak{g}, V) = 0$ .

*Proof.* If V is nontrivial, this follows from Lemmas 18.5 and 18.6. On the other hand, if  $V = \mathbf{k}$  then  $H^1(\mathfrak{g}, V) = (\mathfrak{g}/[\mathfrak{g}, \mathfrak{g}])^* = 0$ .

Now we can prove Theorem 18.4. By Lemma 18.2, it suffices to prove the theorem for irreducible V, which is guaranteed by Corollary 18.7.

Corollary 18.8. A reductive Lie algebra  $\mathfrak{g}$  in characteristic zero is uniquely a direct sum of a semisimple and abelian Lie algebra.

*Proof.* Consider the adjoint representation of  $\mathfrak{g}$ . It is a representation of  $\mathfrak{g}' = \mathfrak{g}/\mathfrak{z}(\mathfrak{g})$ , which fits into a short exact sequence

$$0 \to \mathfrak{z}(\mathfrak{g}) \to \mathfrak{g} \to \mathfrak{g}' \to 0.$$

By complete reducibility, this sequence splits, i.e. we have a decomposition  $\mathfrak{g} = \mathfrak{g}' \oplus \mathfrak{z}(\mathfrak{g})$  as a direct sum of ideals, and it is clearly unique.  $\square$ 

# 18.4. Complete reducibility of representations of semisimple Lie algebras.

**Theorem 18.9.** Every finite dimensional representation of a semisimple Lie algebra  $\mathfrak{g}$  over a field of characteristic zero is completely reducible, i.e., isomorphic to a direct sum of irreducible representations.

*Proof.* Theorem 18.4 implies that for any finite dimensional representations W, U of  $\mathfrak{g}$  one has  $\operatorname{Ext}^1(W, U) = 0$ . Thus any short exact sequence

$$0 \to U \to V \to W \to 0$$

splits, which implies the statement.

#### 19. Structure of semisimple Lie algebras, I

19.1. Semisimple elements. Let x be an element of a Lie algebra  $\mathfrak{g}$  over an algebraically closed field  $\mathbf{k}$ . Let  $\mathfrak{g}_{\lambda} \subset \mathfrak{g}$  be the generalized eigenspace of  $\mathrm{ad} x$  with eigenvalue  $\lambda$ . Then  $\mathfrak{g} = \bigoplus_{\lambda} \mathfrak{g}_{\lambda}$ .

**Lemma 19.1.** We have  $[\mathfrak{g}_{\lambda},\mathfrak{g}_{\mu}] \subset \mathfrak{g}_{\lambda+\mu}$ .

*Proof.* Let  $y \in \mathfrak{g}_{\lambda}, z \in \mathfrak{g}_{\mu}$ . We have

$$(\operatorname{ad} x - \lambda - \mu)^{N}([y, z]) = \sum_{p+q+r+s=N} (-1)^{r+s} \frac{N!}{p!q!r!s!} \lambda^{r} \mu^{s}[(\operatorname{ad} x)^{p}(y), (\operatorname{ad} x)^{q}(z)] = \sum_{k+\ell=N} \frac{N!}{k!\ell!} [(\operatorname{ad} x - \lambda)^{k}(y), (\operatorname{ad} x - \mu)^{\ell}(z)].$$

Thus if  $(\operatorname{ad} x - \lambda)^n(y) = 0$  and  $(\operatorname{ad} x - \mu)^m(z) = 0$  then  $(\operatorname{ad} x - \lambda - \mu)^{m+n}([y, z]) = 0$ ,

so 
$$[y,z] \in \mathfrak{g}_{\lambda+\mu}$$
.

**Definition 19.2.** An element x of a Lie algebra  $\mathfrak{g}$  is called **semisimple** if the operator adx is semisimple and **nilpotent** if this operator is nilpotent.

It is clear that any element which is both semisimple and nilpotent is central, so for a semisimple Lie algebra it must be zero. Note also that for  $\mathfrak{g} = \mathfrak{sl}_n(\mathbf{k})$  this coincides with the usual definition.

**Proposition 19.3.** Let  $\mathfrak{g}$  be a semisimple Lie algebra over a field of characteristic zero. Then every element  $x \in \mathfrak{g}$  has a unique decomposition as  $x = x_s + x_n$ , where  $x_s$  is semisimple,  $x_n$  is nilpotent and  $[x_s, x_n] = 0$ . Moreover, if  $y \in \mathfrak{g}$  and [x, y] = 0 then  $[x_s, y] = [x_n, y] = 0$ .

Proof. Recall that  $\mathfrak{g} \subset \mathfrak{gl}(\mathfrak{g})$  via the adjoint representation. So we can consider the Jordan decomposition  $x = x_s + x_n$ , with  $x_s, x_n \in \mathfrak{gl}(\mathfrak{g})$ . We have  $x_s(y) = \lambda y$  for  $y \in \mathfrak{g}_{\lambda}$ . Thus  $y \mapsto x_s(y)$  is a derivation of  $\mathfrak{g}$  by Lemma 19.1. But by Proposition 17.9 every derivation of  $\mathfrak{g}$  is inner, which implies that  $x_s \in \mathfrak{g}$ , hence  $x_n \in \mathfrak{g}$ . It is clear that  $x_s$  is semisimple,  $x_n$  is nilpotent, and  $[x_s, x_n] = 0$ . Also if [x, y] = 0 then ady preserves  $\mathfrak{g}_{\lambda}$  for all  $\lambda$ , hence  $[x_s, y] = 0$  as linear operators on  $\mathfrak{g}$  and thus as elements of  $\mathfrak{g}$ . This also implies that the decomposition is unique since if  $x = x_s' + x_n'$  then  $[x_s, x_s'] = [x_n, x_n'] = 0$ , so  $x_s - x_s' = x_n' - x_n$  is both semisimple and nilpotent, hence zero.

Corollary 19.4. Any semisimple Lie algebra  $\mathfrak{g} \neq 0$  over a field of characteristic zero contains nonzero semisimple elements.

*Proof.* Otherwise, by Proposition 19.3, every element  $x \in \mathfrak{g}$  is nilpotent, which by Engel's theorem would imply that  $\mathfrak{g}$  is nilpotent, hence solvable, hence zero.

19.2. **Toral subalgebras.** From now on we assume that  $char(\mathbf{k}) = 0$  unless specified otherwise.

**Definition 19.5.** An abelian Lie subalgebra  $\mathfrak{h} \subset \mathfrak{g}$  is called a **toral subalgebra** if it consists of semisimple elements.<sup>12</sup>

**Proposition 19.6.** Let  $\mathfrak{g}$  be a semisimple Lie algebra,  $\mathfrak{h} \subset \mathfrak{g}$  a toral subalgebra, and B a nondegenerate invariant symmetric bilinear form on  $\mathfrak{g}$  (e.g., the Killing form).

- (i) We have a decomposition  $\mathfrak{g} = \bigoplus_{\alpha \in \mathfrak{h}^*} \mathfrak{g}_{\alpha}$ , where  $\mathfrak{g}_{\alpha}$  is the subspace of  $x \in \mathfrak{g}$  such that for  $h \in \mathfrak{h}$  we have  $[h, x] = \alpha(h)x$ , and  $\mathfrak{g}_0 \supset \mathfrak{h}$ .
  - (ii) We have  $[\mathfrak{g}_{\alpha},\mathfrak{g}_{\beta}] \subset \mathfrak{g}_{\alpha+\beta}$ .
  - (iii) If  $\alpha + \beta \neq 0$  then  $\mathfrak{g}_{\alpha}$  and  $\mathfrak{g}_{\beta}$  are orthogonal under B.
  - (iv) B restricts to a nondegenerate pairing  $\mathfrak{g}_{\alpha} \times \mathfrak{g}_{-\alpha} \to \mathbf{k}$ .

*Proof.* (i) is just the joint eigenspace decomposition for  $\mathfrak{h}$  acting in  $\mathfrak{g}$ . (ii) is a very easy special case of Lemma 19.1. (iii) and (iv) follow from the fact that B is nondegenerate and invariant.

Corollary 19.7. (i) The Lie subalgebra  $\mathfrak{g}_0 \subset \mathfrak{g}$  is reductive.

- (ii) if  $x \in \mathfrak{g}_0$  then  $x_s, x_n \in \mathfrak{g}_0$ .
- *Proof.* (i) This follows from Proposition 16.14 and the fact that the form  $(x, y) \mapsto \text{Tr}|_{\mathfrak{g}}(xy)$  on  $\mathfrak{g}_0$  is nondegenerate (Proposition 19.6(iv) for the Killing form of  $\mathfrak{g}$ ).
  - (ii) We have [h, x] = 0 for  $h \in \mathfrak{h}$ , so  $[h, x_s] = 0$ , hence  $x_s \in \mathfrak{g}_0$ .  $\square$

#### 19.3. Cartan subalgebras.

**Definition 19.8.** A Cartan subalgebra of a semisimple Lie algebra  $\mathfrak{g}$  is a toral subalgebra  $\mathfrak{h} \subset \mathfrak{g}$  such that  $\mathfrak{g}_0 = \mathfrak{h}$ .

**Example 19.9.** Let  $\mathfrak{g} = \mathfrak{sl}_n(\mathbf{k})$ . Then the subalgebra  $\mathfrak{h} \subset \mathfrak{g}$  of diagonal matrices is a Cartan subalgebra.

It is clear that any Cartan subalgebra is a maximal toral subalgebra of  $\mathfrak{g}$ . The following theorem, stating the converse, shows that Cartan subalgebras exist.

**Theorem 19.10.** Let  $\mathfrak{h}$  be a maximal toral subalgebra of  $\mathfrak{g}$ . Then  $\mathfrak{h}$  is a Cartan subalgebra.

<sup>&</sup>lt;sup>12</sup>In fact, we will see later that over an algebraically closed field of characteristic zero, a finite dimensional Lie algebra consisting of semisimple elements is automatically abelian.

*Proof.* Let  $x \in \mathfrak{g}_0$ , then by Corollary 19.7(ii)  $x_s \in \mathfrak{g}_0$ , so  $x_s \in \mathfrak{h}$  by maximality of  $\mathfrak{h}$ . Thus  $\mathrm{ad}x|_{\mathfrak{g}_0} = \mathrm{ad}x_n|_{\mathfrak{g}_0}$  is nilpotent. So by Engel's theorem  $\mathfrak{g}_0$  is nilpotent. But it is also reductive, hence abelian.

Now let us show that every  $x \in \mathfrak{g}_0$  which is nilpotent in  $\mathfrak{g}$  must be zero. Indeed, in this case, for any  $y \in \mathfrak{g}_0$ , the operator  $\mathrm{ad} x \cdot \mathrm{ad} y : \mathfrak{g} \to \mathfrak{g}$  is nilpotent (as [x,y]=0), so  $\mathrm{Tr}|_{\mathfrak{g}}(\mathrm{ad} x \cdot \mathrm{ad} y)=0$ . But this form is nondegenerate on  $\mathfrak{g}_0$ , which implies that x=0.

Thus for any  $x \in \mathfrak{g}_0$ ,  $x_n = 0$ , so  $x = x_s$  is semisimple. Hence  $\mathfrak{g}_0 = \mathfrak{h}$  and  $\mathfrak{h}$  is a Cartan subalgebra.

We will show in Theorem 20.10 that all Cartan subalgebras of  $\mathfrak{g}$  are conjugate under  $\operatorname{Aut}(\mathfrak{g})$ , in particular they all have the same dimension, which is called the **rank** of  $\mathfrak{g}$ .

# 19.4. Root decomposition.

**Proposition 19.11.** Let  $\mathfrak{g}$  be a semisimple Lie algebra,  $\mathfrak{h} \subset \mathfrak{g}$  a Cartan subalgebra, and B a nondegenerate invariant symmetric bilinear form on  $\mathfrak{g}$  (e.g., the Killing form).

- (i) We have a decomposition  $\mathfrak{g} = \mathfrak{h} \oplus \bigoplus_{\alpha \in R} \mathfrak{g}_{\alpha}$ , where  $\mathfrak{g}_{\alpha}$  is the subspace of  $x \in \mathfrak{g}$  such that for  $h \in \mathfrak{h}$  we have  $[h, x] = \alpha(h)x$ , and R is the (finite) set of  $\alpha \in \mathfrak{h}^*$ ,  $\alpha \neq 0$ , such that  $\mathfrak{g}_{\alpha} \neq 0$ .
  - (ii) We have  $[\mathfrak{g}_{\alpha},\mathfrak{g}_{\beta}] \subset \mathfrak{g}_{\alpha+\beta}$ .
  - (iii) If  $\alpha + \beta \neq 0$  then  $\mathfrak{g}_{\alpha}$  and  $\mathfrak{g}_{\beta}$  are orthogonal under B.
  - (iv) B restricts to a nondegenerate pairing  $\mathfrak{g}_{\alpha} \times \mathfrak{g}_{-\alpha} \to \mathbf{k}$ .

*Proof.* This immediately follows from Theorem 19.6.

**Definition 19.12.** The set R is called the **root system** of  $\mathfrak{g}$  and its elements are called **roots**.

**Proposition 19.13.** Let  $\mathfrak{g}_1,...,\mathfrak{g}_n$  be simple Lie algebras and let  $\mathfrak{g} = \bigoplus_i \mathfrak{g}_i$ .

- (i) Let  $\mathfrak{h}_i \subset \mathfrak{g}_i$  be Cartan subalgebras of  $\mathfrak{g}_i$  and  $R_i \subset \mathfrak{h}_i^*$  the corresponding root systems of  $\mathfrak{g}_i$ . Then  $\mathfrak{h} = \bigoplus_i \mathfrak{h}_i$  is a Cartan subalgebra in  $\mathfrak{g}$  and the corresponding root system R is the disjoint union of  $R_i$ .
- (ii) Each Cartan subalgebra in  $\mathfrak{g}$  has the form  $\mathfrak{h} = \bigoplus_i \mathfrak{h}_i$  where  $\mathfrak{h}_i \subset \mathfrak{g}_i$  is a Cartan subalgebra in  $\mathfrak{g}_i$ .
- *Proof.* (i) is obvious. To prove (ii), given a Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}$ , let  $\mathfrak{h}_i$  be the projections of  $\mathfrak{h}$  to  $\mathfrak{g}_i$ . It is easy to see that  $\mathfrak{h}_i \subset \mathfrak{g}_i$  are Cartan subalgebras. Also  $\mathfrak{h} \subset \oplus_i \mathfrak{h}_i$  and the latter is toral, which implies that  $\mathfrak{h} = \oplus_i \mathfrak{h}_i$  since  $\mathfrak{h}$  is a Cartan subalgebra.

**Example 19.14.** Let  $\mathfrak{g} = \mathfrak{sl}_n(\mathbf{k})$ . Then the subspace of diagonal matrices  $\mathfrak{h}$  is a Cartan subalgebra (cf. Example 19.9), and it can be naturally

identified with the space of vectors  $\mathbf{x} = (x_1, ..., x_n)$  such that  $\sum_i x_i = 0$ . Let  $\mathbf{e}_i$  be the linear functionals on this space given by  $\mathbf{e}_i(\mathbf{x}) = x_i$ . We have  $\mathfrak{g} = \mathfrak{h} \oplus \bigoplus_{i \neq j} \mathbf{k} E_{ij}$  and  $[\mathbf{x}, E_{ij}] = (x_i - x_j) E_{ij}$ . Thus the root system R consists of vectors  $\mathbf{e}_i - \mathbf{e}_j \in \mathfrak{h}^*$  for  $i \neq j$  (so there are n(n-1) roots).

Now let  $\mathfrak{g}$  be a semisimple Lie algebra and  $\mathfrak{h} \subset \mathfrak{g}$  a Cartan subalgebra. Let (,) be a nondegenerate invariant symmetric bilinear form on  $\mathfrak{g}$ , for example the Killing form. Since the restriction of (,) to  $\mathfrak{h}$  is nondegenerate, it defines an isomorphism  $\mathfrak{h} \to \mathfrak{h}^*$  given by  $h \mapsto (h,?)$ . The inverse of this isomorphism will be denoted by  $\alpha \mapsto H_{\alpha}$ . We also have the inverse form on  $\mathfrak{h}^*$  which we also will denote by (,); it is given by  $(\alpha, \beta) := \alpha(H_{\beta}) = (H_{\alpha}, H_{\beta})$ .

**Lemma 19.15.** For any  $e \in \mathfrak{g}_{\alpha}$ ,  $f \in \mathfrak{g}_{-\alpha}$  we have

$$[e, f] = (e, f)H_{\alpha}.$$

*Proof.* We have  $[e, f] \in \mathfrak{h}$  so it is enough to show that the inner product of both sides with any  $h \in \mathfrak{h}$  is the same. We have

$$([e, f], h) = (e, [f, h]) = \alpha(h)(e, f) = ((e, f)H_{\alpha}, h),$$

as desired.  $\Box$ 

**Lemma 19.16.** (i) If  $\alpha$  is a root then  $(\alpha, \alpha) \neq 0$ .

- (ii) Let  $e \in \mathfrak{g}_{\alpha}$ ,  $f \in \mathfrak{g}_{-\alpha}$  be such that  $(e, f) = \frac{2}{(\alpha, \alpha)}$ , and let  $h_{\alpha} := \frac{2H_{\alpha}}{(\alpha, \alpha)}$ . Then  $e, f, h_{\alpha}$  satisfy the commutation relations of the Lie algebra  $\mathfrak{sl}_2$ .
  - (iii)  $h_{\alpha}$  is independent on the choice of (,).

*Proof.* (i) Pick  $e \in \mathfrak{g}_{\alpha}, f \in \mathfrak{g}_{-\alpha}$  with  $(e, f) \neq 0$ . Let  $h := [e, f] = (e, f)H_{\alpha}$  (by Lemma 19.15) and consider the Lie algebra  $\mathfrak{a}$  generated by e, f, h. Then we see that

$$[h,e] = \alpha(h)e = (\alpha,\alpha)(e,f)e, \ [h,f] = -\alpha(h)f = -(\alpha,\alpha)(e,f)f.$$

Thus if  $(\alpha, \alpha) = 0$  then  $\mathfrak{a}$  is a solvable Lie algebra. By Lie's theorem, we can choose a basis in  $\mathfrak{g}$  such that operators  $\mathrm{ad}e$ ,  $\mathrm{ad}f$ ,  $\mathrm{ad}h$  are upper triangular. Since h = [e, f],  $\mathrm{ad}h$  will be strictly upper-triangular and thus nilpotent. But since  $h \in \mathfrak{h}$ , it is also semisimple. Thus,  $\mathrm{ad}h = 0$ , so h = 0 as  $\mathfrak{g}$  is semisimple. On the other hand,  $h = (e, f)H_{\alpha} \neq 0$ . This contradiction proves the first part of the theorem.

- (ii) This follows immediately from the formulas in the proof of (i).
- (iii) It's enough to check the statement for a simple Lie algebra, and in this case this is easy since (, ) is unique up to scaling by Corollary 16.20.  $\hfill\Box$

The Lie subalgebra of  $\mathfrak{g}$  spanned by  $e, f, h_{\alpha}$ , which we've shown to be isomorphic to  $\mathfrak{sl}_2(\mathbf{k})$ , will be denoted by  $\mathfrak{sl}_2(\mathbf{k})_{\alpha}$  (we will see that  $\mathfrak{g}_{\alpha}$  are 1-dimensional so it is independent on the choices).

**Proposition 19.17.** Let  $\mathfrak{a}_{\alpha} = \mathbf{k} H_{\alpha} \oplus \bigoplus_{k \neq 0} \mathfrak{g}_{k\alpha} \subset \mathfrak{g}$ . Then  $\mathfrak{a}_{\alpha}$  is a Lie subalgebra of  $\mathfrak{g}$ .

*Proof.* This follows from the fact that for  $e \in \mathfrak{g}_{k\alpha}$ ,  $f \in \mathfrak{g}_{-k\alpha}$  we have  $[e,f]=(e,f)H_{k\alpha}=k(e,f)H_{\alpha}$ .

Corollary 19.18. (i) The space  $\mathfrak{g}_{\alpha}$  is 1-dimensional for each root  $\alpha$  of  $\mathfrak{g}$ .

(ii) If  $\alpha$  is a root of  $\mathfrak{g}$  and  $k \geq 2$  is an integer then  $k\alpha$  is not a root of  $\mathfrak{g}$ .

Proof. For a root  $\alpha$  the Lie algebra  $\mathfrak{a}_{\alpha}$  contains  $\mathfrak{sl}_{2}(\mathbf{k})_{\alpha}$ , so it is a finite dimensional representation of this Lie algebra. Also the kernel of  $h_{\alpha}$  on this representation is spanned by  $h_{\alpha}$ , hence 1-dimensional, and eigenvalues of  $h_{\alpha}$  are even integers since  $\alpha(h_{\alpha}) = 2$ . Thus by the representation theory of  $\mathfrak{sl}_{2}$  (Subsection 11.4), this representation is irreducible, i.e., eigenspaces of  $h_{\alpha}$  (which are  $\mathfrak{g}_{k\alpha}$  and  $\mathbf{k}H_{\alpha}$ ) are 1-dimensional. Therefore the map  $[e,?]:\mathfrak{g}_{\alpha}\to\mathfrak{g}_{2\alpha}$  is zero (as  $\mathfrak{g}_{\alpha}$  is spanned by e). So again by representation theory of  $\mathfrak{sl}_{2}$  we have  $\mathfrak{g}_{k\alpha}=0$  for  $|k|\geq 2$ .

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

Corollary 19.20. Let  $\mathfrak{h}_{\mathbb{R}}$  be the  $\mathbb{R}$ -span of all  $h_{\alpha}$ . Then  $\mathfrak{h} = \mathfrak{h}_{\mathbb{R}} \oplus i\mathfrak{h}_{\mathbb{R}}$  and the restriction of the Killing form to  $\mathfrak{h}_{\mathbb{R}}$  is real-valued and positive definite.

*Proof.* It follows from the previous theorem that the eigenvalues of adh,  $h \in \mathfrak{h}_{\mathbb{R}}$ , are real. So  $\mathfrak{h}_{\mathbb{R}} \cap i\mathfrak{h}_{\mathbb{R}} = 0$ , which implies the first statement. Now,  $K(h,h) = \sum_{i} \lambda_{i}^{2}$  where  $\lambda_{i}$  are the eigenvalues of adh (which are not all zero if  $h \neq 0$ ). Thus K(h,h) > 0 if  $h \neq 0$ .

#### 20. Structure of semisimple Lie algebras, II

20.1. Strongly regular (regular semisimple) elements. In this section we will discuss another way of constructing Cartan subalgebras. First consider an example.

**Example 20.1.** Let  $\mathfrak{g} = \mathfrak{sl}_n(\mathbb{C})$  and  $x \in \mathfrak{g}$  be a diagonal matrix with distinct eigenvalues. Then the centralizer  $\mathfrak{h} = C(x)$  is the space of all diagonal matrices of trace 0, which is a Cartan subalgebra. Thus the same applies to any diagonalizable matrix with distinct eigenvalues, i.e., a generic matrix (one for which the discriminant of the characteristic polynomial is nonzero).

So we may hope that if we take a generic element x in a semisimple Lie algebra then its centralizer is a Cartan subalgebra. But for that we have to define what we mean by generic.

**Definition 20.2.** The **nullity** n(x) of an element  $x \in \mathfrak{g}$  is the multiplicity of the eigenvalue 0 for the operator  $\operatorname{ad} x$  (i.e., the dimension of the generalized 0-eigenspace). The **rank**  $\operatorname{rank}(\mathfrak{g})$  of  $\mathfrak{g}$  is the minimal value of n(x). An element x is **strongly regular** if  $n(x) = \operatorname{rank}(\mathfrak{g})$ .

**Example 20.3.** It is easy to check that for  $\mathfrak{g} = \mathfrak{sl}_n$ , x is strongly regular if and only if its eigenvalues are distinct.

We will need the following auxiliary lemma.

**Lemma 20.4.** Let  $P(z_1,...,z_n)$  be a nonzero complex polynomial, and  $U \subset \mathbb{C}^n$  be the set of points  $(z_1,...,z_n) \in \mathbb{C}^n$  such that  $P(z_1,...,z_n) \neq 0$ . Then U is path-connected, dense and open.

Proof. It is clear that U is open, since it is the preimage of the open set  $\mathbb{C}^{\times} \subset \mathbb{C}$  under a continuous map. It is also dense, as its complement, the hypersurface P = 0, cannot contain a ball. Finally, to see that it is path-connected, take  $\mathbf{x}, \mathbf{y} \in U$ , and consider the polynomial  $Q(t) := P((1-t)\mathbf{x} + t\mathbf{y})$ . It has only finitely many zeros, hence the entire complex line  $\mathbf{z} = (1-t)\mathbf{x} + t\mathbf{y}$  except finitely many points is contained in U. Clearly,  $\mathbf{x}$  and  $\mathbf{y}$  can be connected by a path inside this line avoiding this finite set of points.

**Lemma 20.5.** Let  $\mathfrak{g}$  be a complex semisimple Lie algebra. Then the set  $\mathfrak{g}^{sr}$  of strongly regular elements is connected, dense and open in  $\mathfrak{g}$ .

*Proof.* Consider the characteristic polynomial  $P_x(t)$  of adx. We have

$$P_x(t) = t^{\text{rank}(\mathfrak{g})} (t^m + a_{m-1}(x)t^{m-1} + \dots + a_0(x)),$$

where  $m = \dim \mathfrak{g} - \operatorname{rank} \mathfrak{g}$  and  $a_i$  are some polynomials of x, with  $a_0 \neq 0$ . Then x is strongly regular if and only if  $a_0(x) \neq 0$ . This implies the statement by Lemma 20.4.

**Proposition 20.6.** Let  $\mathfrak{g}$  be a complex semisimple Lie algebra and  $\mathfrak{h} \subset \mathfrak{g}$  a Cartan subalgebra. Then

- (i) dim  $\mathfrak{h} = \operatorname{rank}(\mathfrak{g})$ ; and
- (ii) the set  $\mathfrak{h}^{\rm reg}:=\mathfrak{h}\cap\mathfrak{g}^{\rm sr}$  coincides with the set

$$V := \{ h \in \mathfrak{h} : \alpha(h) \neq 0 \ \forall \alpha \in R \}.$$

In particular,  $\mathfrak{h}^{reg}$  is open and dense in  $\mathfrak{h}$ .

*Proof.* (i) Let G be a connected Lie group with Lie algebra  $\mathfrak{g}$  (we know it exists, e.g. we can take G to be the connected component of the identity in  $\operatorname{Aut}(\mathfrak{g})$ ).

**Lemma 20.7.** Let  $\phi: G \times \mathfrak{h} \to \mathfrak{g}$  be the map defined by  $\phi(g,x) := \operatorname{Ad} q \cdot x$ . Then the set  $U := \phi(G \times V) \subset \mathfrak{g}$  is open.

*Proof.* Let us compute the differential  $\phi_* : \mathfrak{g} \oplus \mathfrak{h} \to \mathfrak{g}$  at the point (1, x) for  $x \in \mathfrak{h}$ . We obtain

$$\phi_*(y,h) = [y,x] + h.$$

The kernel of this map is identified with the set of  $y \in \mathfrak{g}$  such that  $[y,x] \in \mathfrak{h}$ . But then K([y,x],z) = K(y,[x,z]) = 0 for all  $z \in \mathfrak{h}$ , so [y,x] = 0. Thus  $\text{Ker}\phi_* = C(x)$ .

Now let  $x \in V$ . Then  $C(x) = \mathfrak{h}$ . Thus  $\phi_*$  is surjective by dimension count, hence  $\phi$  is a submersion at (1,x). This means that  $U := \operatorname{Im} \phi$  contains x together with its neighborhood in  $\mathfrak{g}$ . Hence the same holds for  $\operatorname{Ad} g \cdot x$ , which implies that U is open.

Since  $\mathfrak{g}^{sr}$  is open and dense and U is open by Lemma 20.7 and non-empty, we see that  $U \cap \mathfrak{g}^{sr} \neq \emptyset$ . But

$$n(\operatorname{Ad}g \cdot x) = n(x) = \dim C(x) = \dim \mathfrak{h}.$$

for  $x \in V$ . This implies that rank $\mathfrak{g} = \dim \mathfrak{h}$ , which yields (i).

(ii) It is clear that for  $x \in \mathfrak{h}$ , we have

$$n(x) = \dim \operatorname{Ker}(\operatorname{ad} x) = \dim \mathfrak{h} + \#\{\alpha \in R : \alpha(x) = 0\}.$$

This implies the statement.

# 20.2. Conjugacy of Cartan subalgebras.

**Theorem 20.8.** (i) Let  $\mathfrak{g}$  be a complex semisimple Lie algebra and let  $x \in \mathfrak{g}$  be a strongly regular semisimple element (which exists by Proposition 20.6). Then the centralizer C(x) of x in  $\mathfrak{g}$  is a Cartan subalgebra of  $\mathfrak{g}$ .

(ii) Any Cartan subalgebra of g is of this form.

*Proof.* Consider the eigenspace decomposition of  $\operatorname{ad} x$ :  $\mathfrak{g} = \bigoplus_{\lambda} \mathfrak{g}_{\lambda}$ . Since  $\mathbb{C}x$  is a toral subalgebra, the Lie algebra  $\mathfrak{g}_0 = C(x)$  is reductive, with  $\dim(\mathfrak{g}_0) = \operatorname{rank}\mathfrak{g}$ .

We claim that  $\mathfrak{g}_0$  is also nilpotent. By Engel's theorem, to establish this, it suffices to show that the restriction of ady to  $\mathfrak{g}_0$  is nilpotent for  $y \in \mathfrak{g}_0$ . But  $\mathrm{ad}(x+ty) = \mathrm{ad}x + t\mathrm{ad}y$  is invertible on  $\mathfrak{g}/\mathfrak{g}_0$  for small t, since it is so for t=0 and the set of invertible matrices is open. Thus  $\mathrm{ad}(x+ty)$  must be nilpotent on  $\mathfrak{g}_0$ , as the multiplicity of the eigenvalue 0 for this operator must be (at least) rank  $\mathfrak{g} = \dim \mathfrak{g}_0$ . But  $\mathrm{ad}(x+ty) = t\mathrm{ad}y$  on  $\mathfrak{g}_0$ , which implies that  $\mathrm{ad}y$  is nilpotent on  $\mathfrak{g}_0$ , as desired.

Thus  $\mathfrak{g}_0$  is abelian. Moreover, for  $y, z \in \mathfrak{g}_0$  the operator  $\operatorname{ad} y_n \cdot \operatorname{ad} z$  is nilpotent on  $\mathfrak{g}$  (as the product of two commuting operators one of which is nilpotent), so  $K_{\mathfrak{g}}(y_n, z) = 0$ , which implies that  $y_n = 0$ , as  $K_{\mathfrak{g}}$  restricts to a nondegenerate form on  $\mathfrak{g}_0$  and z is arbitrary. It follows that any  $y \in \mathfrak{g}_0$  is semisimple, so  $\mathfrak{g}_0$  is a toral subalgebra. Moreover, it is maximal since any element commuting with x is in  $\mathfrak{g}_0$ . Thus  $\mathfrak{g}_0$  is a Cartan subalgebra.

- (ii) Let  $\mathfrak{h} \subset \mathfrak{g}$  be a Cartan subalgebra. By Proposition 20.6 it contains a strongly regular element x, which is automatically semisimple. Then  $\mathfrak{h} = C(x)$ .
- Corollary 20.9. (i) Any strongly regular element  $x \in \mathfrak{g}$  is semisimple. (ii) Such x is contained in a unique Cartan subalgebra, namely  $\mathfrak{h}_x = C(x)$ .
- *Proof.* (i) It is clear that if x is strongly regular then so is  $x_s$ . Since  $x \in C(x_s)$  and as shown above  $C(x_s)$  is a Cartan subalgebra, it follows that x is semisimple.
- (ii) Let  $\mathfrak{h} \subset \mathfrak{g}$  be a Cartan subalgebra containing x. Then  $\mathfrak{h} \supset \mathfrak{h}_x$ , thus by dimension count  $\mathfrak{h} = \mathfrak{h}_x$ .

We note that there is also a useful notion of a **regular element**, which is an  $x \in \mathfrak{g}$  for which the **ordinary** (rather than generalized) 0-eigenspace of adx (i.e., the centralizer C(x) of x) has dimension rank $\mathfrak{g}$ . Such elements don't have to be semisimple, e.g. the nilpotent Jordan

block in  $\mathfrak{sl}_n$  is regular. It follows from Corollary 20.9(i) that an element is strongly regular if and only if it is both regular and semisimple. For this reason, from now on we will follow standard terminology and call strongly regular elements **regular semisimple**.

**Theorem 20.10.** Any two Cartan subalgebras of a complex semisimple Lie algebra  $\mathfrak{g}$  are conjugate. I.e., if  $\mathfrak{h}_1, \mathfrak{h}_2 \subset \mathfrak{g}$  are two Cartan subalgebras and G a connected Lie group with Lie algebra  $\mathfrak{g}$  then there exists an element  $g \in G$  such that  $Adg \cdot \mathfrak{h}_1 = \mathfrak{h}_2$ .

Proof. By Corollary 20.9(ii), every element  $x \in \mathfrak{g}^{sr}$  is contained in a unique Cartan subalgebra  $\mathfrak{h}_x$ . Introduce an equivalence relation on  $\mathfrak{g}^{sr}$  by setting  $x \sim y$  if  $\mathfrak{h}_x$  is conjugate to  $\mathfrak{h}_y$ . It is clear that if  $x, y \in \mathfrak{h}$  are regular elements in a Cartan subalgebra  $\mathfrak{h}$  then  $\mathfrak{h}_x = \mathfrak{h}_y = \mathfrak{h}$ , so for any  $g \in G$ ,  $\mathrm{Ad}g \cdot x \sim y$ , and any element equivalent to y has this form. So by Lemma 20.7 the equivalence class  $U_y$  of y is open. However, by Lemma 20.5,  $\mathfrak{g}^{sr}$  is connected. Thus there is only one equivalence class. Hence any two Cartan subalgebras of the form  $\mathfrak{h}_x$  for regular x are conjugate. This implies the result, since by Theorem 20.8 any Cartan subalgebra is of the form  $\mathfrak{h}_x$ .

**Remark 20.11.** The same results and proofs apply over any algebraically closed field  $\mathbf{k}$  of characteristic zero if we use the Zariski topology instead of the usual topology of  $\mathbb{C}^n$  when working with the notions of a connected, open and dense set.

### 20.3. Root systems of classical Lie algebras.

**Example 20.12.** Let  $\mathfrak{g}$  be the symplectic Lie algebra  $\mathfrak{sp}_{2n}(\mathbf{k})$ . Thus  $\mathfrak{g}$  consists of square matrices A of size 2n such that

$$AJ + JA^T = 0$$

where  $J = \begin{pmatrix} 0 & \mathbf{1} \\ -\mathbf{1} & 0 \end{pmatrix}$ , with blocks being of size n. So we get A =

 $\begin{pmatrix} a & b \\ c & -a^T \end{pmatrix}$ , where b, c are symmetric. A Cartan subalgebra  $\mathfrak h$  is then

spanned by matrices A such that  $a = \operatorname{diag}(x_1, ..., x_n)$  and b = c = 0. So  $\mathfrak{h} \cong \mathbf{k}^n$ . In this case we have roots coming from the a-part, which are simply the roots  $\mathbf{e}_i - \mathbf{e}_j$  of  $\mathfrak{gl}_n \subset \mathfrak{sp}_{2n}$  (defined by the condition that b = c = 0) and also the roots coming from the b-part, which are  $\mathbf{e}_i + \mathbf{e}_j$  (including i = j, when we get  $2\mathbf{e}_i$ ), and the c-part, which gives the negatives of these roots,  $-\mathbf{e}_i - \mathbf{e}_j$ , including  $-2\mathbf{e}_i$ .

This is the root system of type  $C_n$ .

**Example 20.13.** Let  $\mathfrak{g}$  be the orthogonal Lie algebra  $\mathfrak{so}_{2n}(\mathbf{k})$ , preserving the quadratic form  $Q = x_1 x_{n+1} + ... + x_n x_{2n}$ . Then the story is

almost the same. The Lie algebra  $\mathfrak g$  consists of square matrices A of size 2n such that

$$AJ + JA^T = 0$$

where  $J = \begin{pmatrix} 0 & \mathbf{1} \\ \mathbf{1} & 0 \end{pmatrix}$ , with blocks being of size n. So we get A =

 $\begin{pmatrix} a & b \\ c & -a^T \end{pmatrix}$ , where b, c are now skew-symmetric. A Cartan subalgebra  $\mathfrak{h}$  is again spanned by matrices A such that  $a = \operatorname{diag}(x_1, ..., x_n)$  and b = c = 0. So  $\mathfrak{h} \cong \mathbf{k}^n$ . In this case we again have roots coming from the a-part, which are simply the roots  $\mathbf{e}_i - \mathbf{e}_j$  of  $\mathfrak{gl}_n \subset \mathfrak{so}_{2n}$  (defined by the condition that b = c = 0) and also the roots coming form the b-part, which are  $\mathbf{e}_i + \mathbf{e}_j$  (but now excluding i = j, so only for  $i \neq j$ ), and the c-part, which gives the negatives of these roots,  $-\mathbf{e}_i - \mathbf{e}_j$ ,  $i \neq j$ .

This is the root system of type  $D_n$ .

**Example 20.14.** Let  $\mathfrak{g}$  be the orthogonal Lie algebra  $\mathfrak{so}_{2n+1}(\mathbf{k})$ , preserving the quadratic form  $Q = x_0^2 + x_1 x_{n+1} + ... + x_n x_{2n}$ . Then the Lie algebra  $\mathfrak{g}$  consists of square matrices A of size 2n + 1 such that

$$AJ + JA^T = 0$$

where

$$J = \begin{pmatrix} \mathbf{1}_1 & 0 & 0 \\ 0 & 0 & \mathbf{1}_n \\ 0 & \mathbf{1}_n & 0 \end{pmatrix},$$

So we get

$$A = \begin{pmatrix} 0 & u & -u \\ w & a & b \\ -w & c & -a^T \end{pmatrix},$$

where b, c are skew-symmetric. A Cartan subalgebra  $\mathfrak{h}$  is spanned by matrices A such that  $a = \operatorname{diag}(x_1, ..., x_n)$  and b = c = 0, u = w = 0. So  $\mathfrak{h} \cong \mathbf{k}^n$ . In this case we again have roots coming from the a-part, which are simply the roots  $\mathbf{e}_i - \mathbf{e}_j$  of  $\mathfrak{gl}_n \subset \mathfrak{so}_{2n+1}$  (defined by the condition that b = c = 0, u = w = 0) and also the roots coming form the b-part, which are  $\mathbf{e}_i + \mathbf{e}_j$ ,  $i \neq j$ , and the c-part, which gives the negatives of these roots,  $-\mathbf{e}_i - \mathbf{e}_j$ ,  $i \neq j$ . But we also have the roots coming from the w-part, which are  $\mathbf{e}_i$ , and from the u part, which are  $-\mathbf{e}_i$ .

This is the root system of type  $B_n$ .

### 21. Root systems

21.1. **Abstract root systems.** Let  $E \cong \mathbb{R}^r$  be a Euclidean space with a positive definite inner product.

**Definition 21.1.** An **abstract root system** is a finite set  $R \subset E \setminus 0$  satisfying the following axioms:

- (R1) R spans E;
- (R2) For all  $\alpha, \beta \in R$  the number  $n_{\alpha\beta} := \frac{2(\alpha,\beta)}{(\alpha,\alpha)}$  is an integer;
- (R3) If  $\alpha, \beta \in R$  then  $s_{\alpha}(\beta) := \beta n_{\alpha\beta}\alpha \in R$ .

Elements of R are called **roots**. The number  $r = \dim E$  is called the **rank** of R.

In particular, taking  $\beta=\alpha$  in R3 yields that R is centrally symmetric, i.e., R=-R. Also note that  $s_{\alpha}$  is the reflection with respect to the hyperplane  $(\alpha,x)=0$ , so R3 just says that R is invariant under such reflections.

Note also that if  $R \subset E$  is a root system,  $\overline{E} \subset E$  a subspace, and  $R' = R \cap \overline{E}$  then R' is also a root system inside  $E' = \operatorname{Span}(R') \subset \overline{E}$ .

For a root  $\alpha$  the corresponding **coroot**  $\alpha^{\vee} \in E^*$  is defined by the formula  $\alpha^{\vee}(x) = \frac{2(\alpha,x)}{(\alpha,\alpha)}$ . Thus  $\alpha^{\vee}(\alpha) = 2$ ,  $n_{\alpha\beta} = \alpha^{\vee}(\beta)$  and  $s_{\alpha}(\beta) = \beta - \alpha^{\vee}(\beta)\alpha$ .

**Definition 21.2.** A root system R is **reduced** if for  $\alpha, c\alpha \in R$ , we have  $c = \pm 1$ .

**Proposition 21.3.** If  $\mathfrak{g}$  is a semisimple Lie algebra and  $\mathfrak{h} \subset \mathfrak{g}$  a Cartan subalgebra then the corresponding set of roots R is a reduced root system, and  $\alpha^{\vee} = h_{\alpha}$ .

*Proof.* This follows immediately from Theorem 19.19.  $\Box$ 

**Example 21.4.** 1. The root system of  $\mathfrak{sl}_n$  is called  $A_{n-1}$ . In this case, as we have seen in Example 19.14, the roots are  $\mathbf{e}_i - \mathbf{e}_j$ , and  $s_{\mathbf{e}_i - \mathbf{e}_j} = (ij)$ , the transposition of the *i*-th and *j*-th coordinates.

2. The subset  $\{1, 2, -1, -2\}$  of  $\mathbb{R}$  is a root system which is not reduced.

**Definition 21.5.** Let  $R_1 \subset E_1$ ,  $R_2 \subset E_2$  be root systems. An **isomorphism of root systems**  $\phi: R_1 \to R_2$  is an isomorphism  $\phi: E_1 \to E_2$  which maps  $R_1$  to  $R_2$  and preserves the numbers  $n_{\alpha\beta}$ .

So an isomorphism does not have to preserve the inner product, e.g. it may rescale it.

# 21.2. The Weyl group.

**Definition 21.6.** The Weyl group of a root system R is the group of automorphisms of E generated by  $s_{\alpha}$ .

**Proposition 21.7.** W is a finite subgroup of O(E) which preserves R.

*Proof.* Since  $s_{\alpha}$  are orthogonal reflections,  $W \subset O(E)$ . By R3,  $s_{\alpha}$  preserves R. By R1 an element of W is determined by its action on R, hence W is finite.

**Example 21.8.** For the root system  $A_{n-1}$ ,  $W = S_n$ , the symmetric group. Note that for  $n \geq 3$ , the automorphism  $x \mapsto -x$  of R is not in W, so W is, in general, a proper subgroup of Aut(R).

21.3. Root systems of rank 2. If  $\alpha, \beta$  are linearly independent roots in R and  $E' \subset E$  is spanned by  $\alpha, \beta$  then  $R' = R \cap E'$  is a root system in E' of rank 2. So to classify reduced root systems, it is important to classify reduced root systems of rank 2 first.

**Theorem 21.9.** Let R be a reduced root system and  $\alpha, \beta \in R$  be two linearly independent roots with  $|\alpha| \geq |\beta|$ . Let  $\phi$  be the angle between  $\alpha$  and  $\beta$ . Then we have one of the following possibilities:

```
 \begin{array}{l} (1) \ \phi = \pi/2, \ n_{\alpha\beta} = n_{\beta\alpha} = 0; \\ (2a) \ \phi = 2\pi/3, \ |\alpha|^2 = |\beta|^2, \ n_{\alpha\beta} = n_{\beta\alpha} = -1; \\ (2b) \ \phi = \pi/3, \ |\alpha|^2 = |\beta|^2, \ n_{\alpha\beta} = n_{\beta\alpha} = 1; \\ (3a) \ \phi = 3\pi/4, \ |\alpha|^2 = 2|\beta|^2, \ n_{\alpha\beta} = -1, \ n_{\beta\alpha} = -2; \\ (3b) \ \phi = \pi/4, \ |\alpha|^2 = 2|\beta|^2, \ n_{\alpha\beta} = 1, \ n_{\beta\alpha} = 2; \\ (4a) \ \phi = 5\pi/6, \ |\alpha|^2 = 3|\beta|^2, \ n_{\alpha\beta} = -1, \ n_{\beta\alpha} = -3; \\ (4b) \ \phi = \pi/6, \ |\alpha|^2 = 3|\beta|^2, \ n_{\alpha\beta} = 1, \ n_{\beta\alpha} = 3. \end{array}
```

*Proof.* We have  $(\alpha, \beta) = 2|\alpha| \cdot |\beta| \cos \phi$ , so  $n_{\alpha\beta} = 2\frac{|\beta|}{|\alpha|} \cos \phi$ . Thus  $n_{\alpha\beta}n_{\beta\alpha} = 4\cos^2\phi$ . Hence this number can only take values 0, 1, 2, 3 (as it is an integer by R2) and  $\frac{n_{\alpha\beta}}{n_{\beta\alpha}} = \frac{|\alpha|^2}{|\beta|^2}$  if  $n_{\alpha\beta} \neq 0$ . The rest is obtained by analysis of each case.

In fact, all these possibilities are realized. Namely, we have root systems  $A_1 \times A_1$ ,  $A_2$ ,  $B_2 = C_2$  (the root system of the Lie algebras  $\mathfrak{sp}_4$  and  $\mathfrak{so}_5$ , which are in fact isomorphic, consisting of the vertices and midpoints of edges of a square), and  $G_2$ , generated by  $\alpha, \beta$  with  $(\alpha, \alpha) = 6$ ,  $(\beta, \beta) = 2$ ,  $(\alpha, \beta) = -3$ , and roots being  $\pm \alpha, \pm \beta, \pm (\alpha + \beta)$ ,  $\pm (\alpha + 2\beta), \pm (\alpha + 3\beta), \pm (2\alpha + 3\beta)$ .

**Theorem 21.10.** Any reduced rank 2 root system R is of the form  $A_1 \times A_1$ ,  $A_2$ ,  $B_2$  or  $G_2$ .

*Proof.* Pick independent roots  $\alpha, \beta \in R$  such that the angle  $\phi$  is as large as possible. Then  $\phi \geq \pi/2$  (otherwise can replace  $\alpha$  with  $-\alpha$ ), so we are in one of the cases 1, 2a, 3a, 4a. Now the statement follows by inspection of each case, giving  $A_1 \times A_1$ ,  $A_2$ ,  $B_2$  and  $G_2$  respectively.  $\square$ 

**Corollary 21.11.** If  $\alpha, \beta \in R$  are independent roots with  $(\alpha, \beta) < 0$  then  $\alpha + \beta \in R$ .

*Proof.* This is easy to see from the classification of rank 2 root systems.

The root systems of rank 2 are shown in the following picture.

21.4. **Positive and simple roots.** Let R be a reduced root system and  $t \in E^*$  be such that  $t(\alpha) \neq 0$  for any  $\alpha \in R$ . We say that a root is **positive** (with respect to t) if  $t(\alpha) > 0$  and **negative** if  $t(\alpha) < 0$ . The set of positive roots is denoted by  $R_+$  and of negative ones by  $R_-$ , so  $R_+ = -R_-$  and  $R = R_+ \cup R_-$  (disjoint union). This decomposition is called a **polarization** of R; it depends on the choice of t.

**Example 21.12.** Let R be of type  $A_{n-1}$ . Then for  $t = (t_1, ..., t_n)$  we have  $t(\alpha) \neq 0$  for all  $\alpha$  iff  $t_i \neq t_j$  for any i, j. E.g. suppose  $t_1 > t_2 > ... > t_n$ , then we have  $\mathbf{e}_i - \mathbf{e}_j \in R_+$  iff i < j. We see that polarizations are in bijection with permutations in  $S_n$ , i.e., with elements of the Weyl group, which acts simply transitively on them. We will see that this is, in fact, the case for any reduced root system.

**Definition 21.13.** A root  $\alpha \in R_+$  is **simple** if it is not a sum of two other positive roots.

Lemma 21.14. Every positive root is a sum of simple roots.

*Proof.* If  $\alpha$  is not simple then  $\alpha = \beta + \gamma$  where  $\beta, \gamma \in R_+$ . We have  $t(\alpha) = t(\beta) + t(\gamma)$ , so  $t(\beta), t(\gamma) < t(\alpha)$ . If  $\beta$  or  $\gamma$  is not simple, we can continue this process, and it will terminate since t has finitely many values on R.

**Lemma 21.15.** If  $\alpha, \beta \in R_+$  are simple roots then  $(\alpha, \beta) \leq 0$ .

*Proof.* Assume  $(\alpha, \beta) > 0$ . Then  $(-\alpha, \beta) < 0$  so by Lemma 21.11  $\gamma := \beta - \alpha$  is a root. If  $\gamma$  is positive then  $\beta = \alpha + \gamma$  is not simple. If  $\gamma$  is negative then  $-\gamma$  is positive so  $\alpha = \beta + (-\gamma)$  is not simple.  $\square$ 

**Theorem 21.16.** The set  $\Pi \subset R_+$  of simple roots is a basis of E.

*Proof.* We will use the following linear algebra lemma:

**Lemma 21.17.** Let  $v_i$  be vectors in a Euclidean space E such that  $(v_i, v_j) \leq 0$  when  $i \neq j$  and  $t(v_i) > 0$  for some  $t \in E^*$ . Then  $v_i$  are linearly independent.

*Proof.* Suppose we have a nontrivial relation

$$\sum_{i \in I} c_i v_i = \sum_{i \in J} c_i v_i$$

where I, J are disjoint and  $c_i > 0$  (clearly, every nontrivial relation can be written in this form). Evaluating t on this relation, we deduce that both sides are nonzero. Now let us compute the square of the left hand side:

$$0 < |\sum_{i \in I} c_i v_i|^2 = (\sum_{i \in I} c_i v_i, \sum_{j \in J} c_j v_j) \le 0.$$

This is a contradiction.

Now the result follows from Lemma 21.15 and Lemma 21.17.  $\Box$ 

Thus the set  $\Pi$  of simple roots has r elements:  $\Pi = (\alpha_1, ..., \alpha_r)$ .

**Example 21.18.** Let us describe simple roots for classical root systems. Suppose the polarization is given by  $t = (t_1, ..., t_n)$  with decreasing coordinates. Then:

- 1. For type  $A_{n-1}$ , i.e.,  $\mathfrak{g} = \mathfrak{sl}_n$ , the simple roots are  $\alpha_i := \mathbf{e}_i \mathbf{e}_{i+1}$ , 1 < i < n-1.
  - 2. For type  $C_n$ , i.e.,  $\mathfrak{g} = \mathfrak{sp}_{2n}$ , the simple roots are

$$\alpha_1 = \mathbf{e}_1 - \mathbf{e}_2, ..., \ \alpha_{n-1} = \mathbf{e}_{n-1} - \mathbf{e}_n, \ \alpha_n = 2\mathbf{e}_n.$$

3. For type  $B_n$ , i.e.,  $\mathfrak{g} = \mathfrak{so}_{2n+1}$ , we have the same story as for  $C_n$  except  $\alpha_n = \mathbf{e}_n$  rather than  $2\mathbf{e}_n$ . Thus the simple roots are

$$\alpha_1 = \mathbf{e}_1 - \mathbf{e}_2, ..., \ \alpha_{n-1} = \mathbf{e}_{n-1} - \mathbf{e}_n, \ \alpha_n = \mathbf{e}_n.$$

4. For type  $D_n$ , i.e.,  $\mathfrak{g} = \mathfrak{so}_{2n}$ , the simple roots are

$$\alpha_1 = \mathbf{e}_1 - \mathbf{e}_2, ..., \ \alpha_{n-2} = \mathbf{e}_{n-2} - \mathbf{e}_{n-1}, \ \alpha_{n-1} = \mathbf{e}_{n-1} - \mathbf{e}_n, \ \alpha_n = \mathbf{e}_{n-1} + \mathbf{e}_n.$$

We thus obtain

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

**Example 21.20.** Let R be of type  $A_1$ . Then  $(\alpha, \alpha^{\vee}) = 2$  for the unique positive root  $\alpha$ , so  $\omega = \frac{1}{2}\alpha$ , thus  $P/Q = \mathbb{Z}/2$ . More generally, if R is of type  $A_{n-1}$  and we identify  $Q \cong Q^{\vee}, P \cong P^{\vee}$ , then P becomes the set of

 $\lambda = (\lambda_1, ..., \lambda_n) \in \mathbb{R}^n$  such that  $\sum_i \lambda_i = 0$  and  $\lambda_i - \lambda_j \in \mathbb{Z}$ . So we have a homomorphism  $\phi : P \to \mathbb{R}/\mathbb{Z}$  given by  $\phi(\lambda) = \lambda_i \mod \mathbb{Z}$  (for any i). Since  $\sum_i \lambda_i = 0$ , we have  $\phi : P \to \mathbb{Z}/n$ , and  $\operatorname{Ker} \phi = Q$  (integer vectors with sum zero). Also it is easy to see that  $\phi$  is surjective (we may take  $\lambda_i = \frac{k}{n}$  for  $i \neq n$  and  $\lambda_n = \frac{k}{n} - k$ , then  $\phi(\lambda) = \frac{k}{n}$ ). Thus  $P/Q \cong \mathbb{Z}/n$ .

#### 22. Properties of the Weyl group

22.1. Weyl chambers. Suppose we have two polarizations of a root system R defined by  $t, t' \in E$ , and  $\Pi, \Pi'$  are the corresponding systems of simple roots. Are  $\Pi, \Pi'$  equivalent in a suitable sense? The answer turns out to be yes. To show this, we will need the notion of a Weyl chamber.

Note that the polarization defined by t depends only on the signs of  $(t, \alpha)$ , so does not change when t is continuously deformed without crossing the hyperplanes  $(t, \alpha) = 0$ . This motivates the following definition:

**Definition 22.1.** A **Weyl chamber** is a connected component of the complement of the root hyperplanes  $L_{\alpha}$  given by the equations  $(\alpha, x) = 0$  in E ( $\alpha \in R$ ).

Thus a Weyl chamber is defined by a system of strict homogeneous linear inequalities  $\pm(\alpha, x) = 0$ ,  $\alpha \in R$ . More precisely, the set of solutions of such a system is either empty or a Weyl chamber.

Thus the polarization defined by t depends only on the Weyl chamber containing t.

The following lemma is geometrically obvious.

**Lemma 22.2.** (i) The closure  $\overline{C}$  of a Weyl chamber C is a convex cone.

(ii) The boundary of  $\overline{C}$  is a union of codimension 1 faces  $F_i$  which are convex cones inside one of the root hyperplanes defined inside it by a system of non-strict homogeneous linear inequalities.

The root hyperplanes containing the faces  $F_i$  are called the **walls** of C.

We have seen above that every Weyl chamber defines a polarization of R. Conversely, every polarization defines the corresponding **positive** Weyl chamber  $C_+$  defined by the conditions  $(\alpha, x) > 0$  for  $\alpha \in R_+$  (this set is nonempty since it contains t, hence is a Weyl chamber). Thus  $C_+$  is the set of vectors of the form  $\sum_{i=1}^r c_i \omega_i$  with  $c_i > 0$ . So  $C_+$  has r faces  $L_{\alpha_1} \cap \overline{C}_+, ..., L_{\alpha_r} \cap \overline{C}_+$ .

**Lemma 22.3.** These assignments are mutually inverse bijections between polarizations of R and Weyl chambers.

#### Exercise 22.4. Prove Lemma 22.3.

Since the Weyl group W permutes the roots, it acts on the set of Weyl chambers.

**Theorem 22.5.** W acts transitively on the set of Weyl chambers.

Proof. Let us say that Weyl chambers C, C' are **adjacent** if they share a common face  $F \subset L_{\alpha}$ . In this case it is easy to see that  $s_{\alpha}(C) = C'$ . Now given any Weyl chambers C, C', pick generic  $t \in C, t' \in C'$  and connect them with a straight segment. This will define a sequence of Weyl chambers visited by this segment:  $C_0 = C, C_1, ..., C_m = C'$ , and  $C_i, C_{i+1}$  are adjacent for each i. So  $C_i, C_{i+1}$  lie in the same W-orbit. Hence so do C, C'.

Corollary 22.6. Every Weyl chamber has r walls.

*Proof.* This follows since it is true for the positive Weyl chamber and by Theorem 22.5 the Weyl group acts transitively on the Weyl chambers.

**Corollary 22.7.** Any two polarizations of R are related by the action of an element  $w \in W$ . Thus if  $\Pi, \Pi'$  are systems of simple roots corresponding to two polarizations then there is  $w \in W$  such that  $w(\Pi) = \Pi'$ .

22.2. Simple reflections. Given a polarization of R and the corresponding system of simple roots  $\Pi = \{\alpha_1, ..., \alpha_r\}$ , the simple reflections are the reflections  $s_{\alpha_i}$ , denoted by  $s_i$ .

**Lemma 22.8.** For every Weyl chamber C there exist  $i_1, ..., i_m$  such that  $C = s_{i_1}...s_{i_m}(C_+)$ .

Proof. Pick  $t \in C, t_+ \in C_+$  generically and connect them with a straight segment as before. Let m be the number of chamber walls crossed by this segment. The proof is by induction in m (with obvious base). Let C' be the chamber entered by our segment from C and  $L_{\alpha}$  the wall separating C, C', so that  $C = s_{\alpha}(C')$ . By the induction assumption  $C' = u(C_+)$ , where  $u = s_{i_1}...s_{i_{m-1}}$ . So  $L_{\alpha} = u(L_{\alpha_j})$  for some j. Thus  $s_{\alpha} = us_ju^{-1}$ . Hence  $C = s_{\alpha}(C') = s_{\alpha}u(C_+) = us_j(C_+)$ , so we get the result with  $i_m = j$ .

Corollary 22.9. (i) The simple reflections  $s_i$  generate W; (ii)  $W(\Pi) = R$ .

*Proof.* (i) This follows since for any root  $\alpha$ , the hyperplane  $L_{\alpha}$  is a wall of some Weyl chamber, so  $s_{\alpha}$  is a product of  $s_{i}$ .

(ii) Follows from (i).  $\Box$ 

Thus R can be reconstructed from  $\Pi$  as  $W(\Pi)$ , where W is the subgroup of O(E) generated by  $s_i$ .

**Example 22.10.** For root system  $A_{n-1}$  part (i) says that any element of  $S_n$  is a product of transpositions of neighbors.

22.3. Length of an element of the Weyl group. Let us say that a root hyperplane  $L_{\alpha}$  separates two Weyl chambers C, C' if they lie on different sides of  $L_{\alpha}$ .

**Definition 22.11.** The **length**  $\ell(w)$  of  $w \in W$  is the number of root hyperplanes separating  $C_+$  and  $w(C_+)$ .

We have  $t \in C_+, w(t) \in w(C_+)$ , so  $\ell(w)$  is the number of roots  $\alpha$  such that  $(t, \alpha) > 0$  but  $(w(t), \alpha) = (t, w^{-1}\alpha) < 0$ . Note that if  $\alpha$  is a root satisfying this condition then  $\beta = -w^{-1}\alpha$  satisfies the conditions  $(t, \beta) > 0$ ,  $(t, w\beta) < 0$ . Thus  $\ell(w) = \ell(w^{-1})$  and  $\ell(w)$  is the number of positive roots which are mapped by w to negative roots. Note also that the notion of length depends on the polarization of R (as it refers to the positive chamber  $C_+$  defined using the polarization).

**Example 22.12.** Let  $s_i$  be a simple reflection. Then  $s_i(C_+)$  is adjacent to  $C_+$ , with the only separating hyperplane being  $L_{\alpha_i}$ . Thus  $\ell(s_i) = 1$ . It follows that the only positive root mapped by  $s_i$  to a negative root is  $\alpha_i$  (namely,  $s_i(\alpha_i) = -\alpha_i$ ), and thus  $s_i$  permutes  $R_+ \setminus {\alpha_i}$ .

**Proposition 22.13.** Let  $\rho = \frac{1}{2} \sum_{\alpha \in R_+} \alpha$ . Then  $(\rho, \alpha_i^{\vee}) = 1$  for all i. Thus  $\rho = \sum_{i=1}^r \omega_i$ .

*Proof.* We have  $\rho = \frac{1}{2}\alpha_i + \frac{1}{2}\sum_{\alpha \in R_+, \alpha \neq \alpha_i} \alpha$ . Since  $s_i$  permutes  $R_+ \setminus \{\alpha_i\}$ , we get  $s_i \rho = \rho - \alpha_i$ . But for any  $\lambda$ ,  $s_i \lambda = \lambda - (\lambda, \alpha_i^{\vee})\alpha_i$ . This implies the statement.

The weight  $\rho$  plays an important role in representation theory of semisimple Lie algebras. For instance, it occurs in the Weyl character formula for these representations which we will soon derive.

**Theorem 22.14.** Let  $w = s_{i_1}...s_{i_l}$  be a representation of  $w \in W$  as a product of simple reflections that has minimal possible length. Then  $l = \ell(w)$ .

Proof. As before, define a chain of Weyl chambers  $C_k = s_{i_1}...s_{i_k}(C_+)$ , so that  $C_0 = C_+$  and  $C_l = w(C_+)$ . We have seen that  $C_k$  and  $C_{k-1}$  are adjacent. So there is a zigzag path from  $C_+$  to  $w(C_+)$  that intersects at most l root hyperplanes (namely, the segment from  $C_{k-1}$  to  $C_k$  intersects only one hyperplane). Thus  $\ell(w) \leq l$ . On the other hand, pick generic points in  $C_+$  and  $w(C_+)$  and connect them with a straight segment. This segment intersects every separating root hyperplane exactly once and does not intersect other root hyperplanes, so produces an expression of w as a product of  $\ell(w)$  simple reflections. This implies the statement.

An expression  $w = s_{i_1}...s_{i_l}$  is called **reduced** if  $l = \ell(w)$ .

**Proposition 22.15.** The Weyl group W acts simply transitively on Weyl chambers.

*Proof.* By Theorem 22.5 the action is transitive, so we just have to show that if  $w(C_+) = C_+$  then w = 1. But in this case  $\ell(w) = 0$ , so w has to be a product of zero simple reflections, i.e., indeed w = 1.

Thus we see that  $\overline{C}_+$  is a fundamental domain of the action of W on E.

Moreover, we have

**Proposition 22.16.**  $E/W = \overline{C}_+$ , i.e., every W-orbit on E has a unique representative in  $\overline{C}_+$ .

Proof. Suppose  $\lambda, \mu \in \overline{C}_+$  and  $\lambda = w\mu$ , where  $w \in W$  is shortest possible. Assume the contrary, that  $w \neq 1$ . Pick a reduced decomposition  $w = s_{i_l}...s_{i_1}$ . Let  $\gamma$  be the positive root which is mapped to a negative root by w but not by  $s_{i_l}w$ , i.e.,  $\gamma = s_{i_1}...s_{i_{l-1}}\alpha_{i_l}$ . Then  $0 \leq (\mu, \gamma) = (\lambda, w\gamma) \leq 0$ . so  $(\mu, \gamma) = 0$ . Thus

$$\lambda = w\mu = s_{i_1}...s_{i_1}\mu = s_{i_{l-1}}...s_{i_1}s_{\gamma}\mu = s_{i_{l-1}}...s_{i_1}\mu$$

which is a contradiction since w was the shortest possible.

Corollary 22.17. Let  $C_- = -C_+$  be the negative Weyl chamber. Then there exists a unique  $w_0 \in W$  such that  $w_0(C_+) = C_-$ . We have  $\ell(w_0) = |R_+|$  and for any  $w \neq w_0$ ,  $\ell(w) < \ell(w_0)$ . Also  $w_0^2 = 1$ .

Exercise 22.18. Prove Corollary 22.17.

The element  $w_0$  is therefore called the **longest element** of W.

**Example 22.19.** For the root system  $A_{n-1}$  the element  $w_0$  is the order reversing involution:  $w_0(1, 2, ..., n) = (n, ..., 2, 1)$ .

# 23. Dynkin diagrams

23.1. Cartan matrices and Dynkin diagrams. Our goal now is to classify reduced root systems, which is a key step in the classification of semisimple Lie algebras. We have shown that classifying root systems is equivalent to classifying sets  $\Pi$  of simple roots. So we need to classify such sets  $\Pi$ . Before doing so, note that we have a nice notion of **direct product** of root systems.

Namely, let  $R_1 \subset E_1$  and  $R_2 \subset E_2$  be two root systems. Let  $E = E_1 \oplus E_2$  (orthogonal decomposition) and  $R = R_1 \sqcup R_2$  (with  $R_1 \perp R_2$ ). If  $t_1 \in E_1, t_2 \in E_2$  define polarizations of  $R_1, R_2$  with systems of simple roots  $\Pi_1, \Pi_2$  then  $t = t_1 + t_2$  defines a polarization of R with  $\Pi = \Pi_1 \sqcup \Pi_2$  (with  $\Pi_1 \perp \Pi_2$  and  $\Pi_i = \Pi \cap R_i$ ).

**Definition 23.1.** A root system R is **irreducible** if it cannot be written (nontrivially) in this way.

**Lemma 23.2.** If R is a root system with system of simple roots  $\Pi = \Pi_1 \sqcup \Pi_2$  with  $\Pi_1 \perp \Pi_2$  then  $R = R_1 \sqcup R_2$  where  $R_i$  is the root system generated by  $\Pi_i$ .

*Proof.* If  $\alpha \in \Pi_1, \beta \in \Pi_2$  then  $s_{\alpha}(\beta) = \beta$ ,  $s_{\beta}(\alpha) = \alpha$  and  $s_{\alpha}$  and  $s_{\beta}$  commute. So if  $W_i$  is the group generated by  $s_{\alpha}, \alpha \in \Pi_i$  then  $W = W_1 \times W_2$ , with  $W_1$  acting trivially on  $\Pi_2$  and  $W_2$  on  $\Pi_1$ . Thus

$$R = W(\Pi) = W(\Pi_1 \sqcup \Pi_2) = W_1(\Pi_1) \sqcup W_2(\Pi_2) = R_1 \sqcup R_2.$$

**Proposition 23.3.** Any root system is uniquely a union of irreducible ones.

*Proof.* The decomposition is given by the maximal decomposition of  $\Pi$  into mutually orthogonal systems of simple roots.

Thus it suffices to classify irreducible root systems.

As noted above, a root system is determined by pairwise inner products of positive roots. However, it is more convenient to encode them by the  $\mathbf{Cartan\ matrix}\ A$  defined by

$$a_{ij} = n_{\alpha_j \alpha_i} = (\alpha_i^{\vee}, \alpha_j).$$

The following properties of the Cartan matrix follow immediately from Lemma 21.15, Theorem 21.9 and Theorem 21.16:

**Proposition 23.4.** (*i*)  $a_{ii} = 2$ ;

- (ii)  $a_{ij}$  is a nonpositive integer;
- (iii) for any  $i \neq j$ ,  $a_{ij}a_{ji} = 4\cos^2\phi \in \{0,1,2,3\}$ , where  $\phi$  is the angle between  $\alpha_i$  and  $\alpha_j$ ;

(iv) Let  $d_i = |\alpha_i|^2$ . Then the matrix  $d_i a_{ij}$  is symmetric and positive definite.

We will see later that conversely, any such matrix defines a root system.

**Example 23.5.** 1. Type  $A_{n-1}$ :  $a_{ii} = 2, a_{i,i+1} = a_{i+1,i} = -1, a_{ij} = 0$  otherwise.

- 2. Type  $B_n$ :  $a_{ii} = 2$ ,  $a_{i,i+1} = a_{i+1,i} = -1$  except that  $a_{n,n-1} = -2$ .
- 3. Type  $C_n$ : transposed to  $B_n$ .
- 4. Type  $D_n$ : same as  $B_n$  but  $a_{n-1,n-2}=a_{n,n-2}=a_{n-2,n}=a_{n-2,n-1}=-1, a_{n,n-1}=a_{n-1,n}=0.$

5. Type 
$$G_2$$
:  $A = \begin{pmatrix} 2 & -1 \\ -3 & 2 \end{pmatrix}$ .

It is convenient to encode such matrices by **Dynkin diagrams:** 

- Indices i are vertices;
- Vertices i and j are connected by  $a_{ij}a_{ji}$  lines;
- If  $a_{ij} \neq a_{ji}$ , i.e.,  $|\alpha_i|^2 \neq |\alpha_j|^2$ , then the arrow on the lines goes from long root to short root ("less than" sign).

It is clear that such a diagram completely determines the Cartan matrix (if we fix the labeling of vertices), and vice versa. Also it is clear that the root system is irreducible if and only if its Dynkin diagram is connected.

**Proposition 23.6.** The Cartan matrix determines the root system uniquely.

*Proof.* We may assume the Dynkin diagram is connected. The Cartan matrix determines, for any pair of simple roots, the angle between them (which is right or obtuse) and the ratio of their lengths if they are not orthogonal. By the classification of rank 2 root systems, this determines the inner product on simple roots, up to scaling, which implies the statement.

23.2. Classification of Dynkin diagrams. The following theorem gives a complete classification of irreducible root systems.

**Theorem 23.7.** (i) Connected Dynkin diagrams are classified by the list given in the picture below, i.e., they are  $A_n, B_n, C_n, D_n, G_2$  which we have already met, along with four more:  $F_4, E_6, E_7, E_8$ .

(ii) Every matrix satisfying the conditions of Proposition 23.4 is a Cartan matrix of some root system.

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

The proof of Theorem 23.7 is rather long but direct. It consists of several steps. The first step is construction of the remaining root systems  $F_4$ ,  $E_6$ ,  $E_7$ ,  $E_8$ .

# 23.3. The root system $F_4$ .

**Definition 23.8.** The root system  $F_4$  is the union of the root system  $B_4 \subset \mathbb{R}^4$  with the vectors

$$(\pm \frac{1}{2}, \pm \frac{1}{2}, \pm \frac{1}{2}, \pm \frac{1}{2}) = \sum_{i=1}^{4} (\pm \frac{1}{2} \mathbf{e}_i),$$

for all choices of signs.

Thus besides the roots of  $B_4$ , which are  $\pm \mathbf{e}_i \pm \mathbf{e}_j$  (24 of them, squared length 2) and  $\pm \mathbf{e}_i$  (8 of them, squared length 1), we have the 16 new roots  $\sum_{i=1}^4 (\pm \frac{1}{2} \mathbf{e}_i)$  (squared length 1); this gives a total of 48.

Exercise 23.9. Check that this is an irreducible root system.

To give a polarization of the  $F_4$  root system, pick  $t = (t_1, t_2, t_3, t_4)$  with  $t_1 \gg t_2 \gg t_3 \gg t_4$ .

**Exercise 23.10.** Check that for this polarization, the simple positive roots are,  $\alpha_1 = \frac{1}{2}(\mathbf{e}_1 - \mathbf{e}_2 - \mathbf{e}_3 - \mathbf{e}_4)$ ,  $\alpha_2 = \mathbf{e}_4$ ,  $\alpha_3 = \mathbf{e}_3 - \mathbf{e}_4$ ,  $\alpha_4 = \mathbf{e}_2 - \mathbf{e}_3$ . Thus  $\alpha_1^{\vee} = \mathbf{e}_1 - \mathbf{e}_2 - \mathbf{e}_3 - \mathbf{e}_4$ ,  $\alpha_2^{\vee} = 2\mathbf{e}_4$ ,  $\alpha_3^{\vee} = \mathbf{e}_3 - \mathbf{e}_4$ ,  $\alpha_4^{\vee} = \mathbf{e}_2 - \mathbf{e}_3$ . So the Cartan matrix has the form

$$A = \begin{pmatrix} 2 & -1 & 0 & 0 \\ -1 & 2 & -2 & 0 \\ 0 & -1 & 2 & -1 \\ 0 & 0 & -1 & 2 \end{pmatrix}$$

which gives the Dynkin diagram of  $F_4$ .

### 23.4. The root system $E_8$ .

**Definition 23.11.** The root system  $E_8$  is the union of the root system  $D_8 \subset \mathbb{R}^8$  with the vectors  $\sum_{i=1}^8 (\pm \frac{1}{2} \mathbf{e}_i)$ , for all choices of signs with even number of minuses.

Thus besides the roots of  $D_8$ ,  $\pm \mathbf{e}_i \pm \mathbf{e}_j$  (112 of them), we have 128 new roots  $\sum_{i=1}^{8} (\pm \frac{1}{2} \mathbf{e}_i)$ . So in total we have 240 roots. All roots have squared length 2.

Exercise 23.12. Show that it is an irreducible root system.

To give a polarization of the  $E_8$  root system, pick t so that  $t_i \gg t_{i+1}$ .

**Exercise 23.13.** Check that for this polarization, the simple positive roots are,  $\alpha_1 = \frac{1}{2}(\mathbf{e}_1 + \mathbf{e}_8 - \sum_{i=2}^7 \mathbf{e}_i)$ ,  $\alpha_2 = \mathbf{e}_7 + \mathbf{e}_8$  and  $\alpha_i = \mathbf{e}_{10-i} - \mathbf{e}_{11-i}$  for  $3 \le i \le 8$ . Thus the roots  $\alpha_2, ..., \alpha_8$  generate the root system  $D_7$ , while  $a_{13} = -1$  and  $a_{1i} = 0$  for all  $i \ne 1, 3$ . In other words, the Cartan matrix has the form

$$A = \begin{pmatrix} 2 & 0 & -1 & 0 & 0 & 0 & 0 & 0 \\ 0 & 2 & 0 & -1 & 0 & 0 & 0 & 0 \\ -1 & 0 & 2 & -1 & 0 & 0 & 0 & 0 \\ 0 & -1 & -1 & 2 & -1 & 0 & 0 & 0 \\ 0 & 0 & 0 & -1 & 2 & -1 & 0 & 0 \\ 0 & 0 & 0 & 0 & -1 & 2 & -1 & 0 \\ 0 & 0 & 0 & 0 & 0 & -1 & 2 & -1 \\ 0 & 0 & 0 & 0 & 0 & 0 & -1 & 2 \end{pmatrix}$$

This recovers the Dynkin diagram  $E_8$ .

#### 23.5. The root system $E_7$ .

**Definition 23.14.** The root system  $E_7$  is the subsystem of  $E_8$  generated by  $\alpha_1, ..., \alpha_7$ .

Note that these roots (unlike  $\alpha_8 = \mathbf{e}_2 - \mathbf{e}_3$ ) satisfy the equation  $x_1 + x_2 = 0$ . Thus  $E_7$  is the intersection of  $E_8$  with this subspace. So it includes the roots  $\pm \mathbf{e}_i \pm \mathbf{e}_j$  with  $3 \le i, j \le 8$  distinct (60 roots),  $\pm (\mathbf{e}_1 - \mathbf{e}_2)$  (2 roots) and  $\sum_{i=1}^8 (\pm \frac{1}{2} \mathbf{e}_i)$  with even number of minuses and the opposite signs for  $\mathbf{e}_1$  and  $\mathbf{e}_2$  (64 roots). Altogether we get 126 roots. The Cartan matrix is the upper left corner 7 by 7 submatrix of

the Cartan matrix of  $E_8$ , so it is

$$A = \begin{pmatrix} 2 & 0 & -1 & 0 & 0 & 0 & 0 \\ 0 & 2 & 0 & -1 & 0 & 0 & 0 \\ -1 & 0 & 2 & -1 & 0 & 0 & 0 \\ 0 & -1 & -1 & 2 & -1 & 0 & 0 \\ 0 & 0 & 0 & -1 & 2 & -1 & 0 \\ 0 & 0 & 0 & 0 & -1 & 2 & -1 \\ 0 & 0 & 0 & 0 & 0 & -1 & 2 \end{pmatrix}$$

# 23.6. The root system $E_6$ .

**Definition 23.15.** The root system  $E_6$  is the subsystem of  $E_8$  and  $E_7$  generated by  $\alpha_1, ..., \alpha_6$ .

Note that these roots (unlike  $\alpha_8 = \mathbf{e}_2 - \mathbf{e}_3$  and  $\alpha_7 = \mathbf{e}_3 - \mathbf{e}_4$ ) satisfy the equations  $x_1 + x_2 = 0$ ,  $x_2 - x_3 = 0$ . Thus  $E_6$  is the intersection of  $E_8$  with this subspace. So it includes the roots  $\pm \mathbf{e}_i \pm \mathbf{e}_j$  with  $4 \le i, j \le 8$  distinct (40 roots), and  $\sum_{i=1}^8 (\pm \frac{1}{2} \mathbf{e}_i)$  with even number of minuses and the opposite signs for  $\mathbf{e}_1$  and  $\mathbf{e}_2$  and for  $\mathbf{e}_1$  and  $\mathbf{e}_3$  (32 roots). Altogether we get 72 roots. The Cartan matrix is the upper left corner 6 by 6 submatrix of the Cartan matrix of  $E_8$ , so it is

$$A = \begin{pmatrix} 2 & 0 & -1 & 0 & 0 & 0 \\ 0 & 2 & 0 & -1 & 0 & 0 \\ -1 & 0 & 2 & -1 & 0 & 0 \\ 0 & -1 & -1 & 2 & -1 & 0 \\ 0 & 0 & 0 & -1 & 2 & -1 \\ 0 & 0 & 0 & 0 & -1 & 2 \end{pmatrix}$$

This recovers the Dynkin diagram  $E_6$ .

23.7. The elements  $\rho$  and  $\rho^{\vee}$ . Recall that the elements  $\rho \in \mathfrak{h}^*$  and  $\rho^{\vee} \in \mathfrak{h}$  for a simple Lie algebra  $\mathfrak{g}$  are defined by the conditions  $(\rho, \alpha_i^{\vee}) = (\rho^{\vee}, \alpha_i) = 1$  for all i (note that  $\rho$  is not a root in general, and  $\rho^{\vee}$  is not an instance of the assignment  $\alpha \mapsto \alpha^{\vee}$  for roots  $\alpha$ ). So for classical Lie algebras they can be computed from Example 21.18. Namely, we get

$$\rho_{A_{n-1}} = \rho_{A_{n-1}}^{\vee} = \left(\frac{n-1}{2}, \frac{n-3}{2}, \dots, -\frac{n-1}{2}\right),$$

$$\rho_{B_n} = \rho_{C_n}^{\vee} = \left(\frac{2n-1}{2}, \dots, \frac{3}{2}, \frac{1}{2}\right),$$

$$\rho_{C_n} = \rho_{B_n}^{\vee} = (n, n-1, \dots, 1),$$

$$\rho_{D_n} = \rho_{D_n}^{\vee} = (n-1, n-2, \dots, 0).$$

**Exercise 23.16.** Show that the elements  $\rho$  and  $\rho^{\vee}$  for exceptional root systems (in the above realizations) are as follows:

$$\rho_{G_2} = 3\alpha + 5\beta, \ \rho_{G_2}^{\vee} = 5\alpha^{\vee} + 3\beta^{\vee},$$

$$\rho_{F_4} = (\frac{11}{2}, \frac{5}{2}, \frac{3}{2}, \frac{1}{2}), \ \rho_{F_4}^{\vee} = (8, 3, 2, 1),$$

$$\rho_{E_8} = \rho_{E_8}^{\vee} = (23, 6, 5, 4, 3, 2, 1, 0),$$

$$\rho_{E_7} = \rho_{E_7}^{\vee} = (\frac{17}{2}, -\frac{17}{2}, 5, 4, 3, 2, 1, 0),$$

$$\rho_{E_6} = \rho_{E_6}^{\vee} = (4, -4, -4, 4, 3, 2, 1, 0).$$

(recall that we realized  $E_6, E_7, E_8$  inside  $\mathbb{R}^8$ ).

23.8. Proof of Theorem 23.7. Now that we have shown that there exist root systems attached to all Cartan matrices, it remains to classify Cartan matrices (or Dynkin diagrams), i.e. show that there are no others than those we have considered. For this purpose we consider Dynkin diagrams as graphs with certain kind of special edges (with one, two or three lines and a possible orientation). Note first that any subgraph of a Dynkin diagram must itself be a Dynkin diagram, since a principal submatrix of a positive definite symmetric matrix is itself positive definite. On the other hand, consider untwisted and twisted affine Dynkin diagrams depicted on the first picture at https://en.wikipedia.org/wiki/Affine\_Lie\_algebra. These are not Dynkin diagrams since the corresponding matrix A is degenerate, hence not positive definite.

Exercise 23.17. Prove this by showing that in each case there exists a nonzero vector v such that Av = 0. For example, in the simply laced case (only simple edges), this amounts to finding a labeling of the vertices by nonzero numbers such that the sum of labels of the neighbors to each vertex is twice the label of that vertex, and in the non-simply laced case it's a weighted version of that.

Thus they cannot occur inside a Dynkin diagram.

We conclude that a Dynkin diagram is a tree. Indeed, it cannot have a loop with simple edges, since this is the affine diagram  $\widetilde{A}_{n-1}$ , which has a null vector (1, ..., 1). If there is a loop with non-simple edges, this is even worse - this vector will have a negative inner product with itself.

Further, it cannot have vertices with more than four simple edges coming out since it cannot have a subdiagram  $\widetilde{D}_4$  (and for non-simple edges it is even worse, as before). Thus all the vertices of our tree are i-valent for i < 3.

Also we cannot have a subdiagram  $\widetilde{D}_n$ ,  $n \geq 5$ , which implies that there is at most one trivalent vertex.

Further, if there is a triple edge then the diagram is  $G_2$ . There is no way to attach any edge to the  $G_2$  diagram because  $D_4^{(3)}$  and  $\widetilde{G}_2$  are forbidden.

Next, if there is a trivalent vertex then there cannot be a non-simple edge anywhere in the diagram (as we have forbidden affine diagrams  $A_{2k-1}^{(2)}, \widetilde{B}_n$ ). So in this case the diagram is simply laced, so it must be on our list  $(D_n, E_6, E_7, E_8)$  since it cannot contain affine diagrams  $\widetilde{E}_6, \widetilde{E}_7, \widetilde{E}_8$ .

It remains to consider chain-shaped diagrams. They can't contain two double edges (affine diagrams  $A_{2k}^{(2)}, D_{k+1}^{(2)}, \widetilde{C}_n$ ). Thus if the double edge is at the end, we can only get  $B_n$  and  $C_n$ .

Finally, if the double edge is in the middle, we can't have affine subdiagram  $\widetilde{F}_4$  or  $E_6^{(2)}$ , so our diagram must be  $F_4$ . Theorem 23.7 is proved.

Remark 23.18. Note that we have exceptional isomorphisms  $D_2 \cong A_1 \times A_1$ ,  $D_3 \cong A_3$ ,  $B_2 \cong C_2$ . Otherwise the listed root systems are distinct.

23.9. Simply laced and non-simply laced diagrams. As we already mentioned, a Dynkin diagram (or the corresponding root system) is called **simply laced** if all the edges are simple, i.e.  $a_{ij} = 0, -1$  for  $i \neq j$ . This is equivalent to the Cartan matrix being symmetric, or to all roots having the same length. The connected simply-laced diagrams are  $A_n, n \geq 1$ ;  $D_n, n \geq 4$ ;  $E_6, E_7, E_8$ . The remaining diagrams  $B_n, C_n, F_4, G_2$  are not simply laced, but they contain roots of only two squared lengths, whose ratio is 2 for double edge  $(B_n, C_n, F_4)$  and 3 for triple edge  $(G_2)$ . The roots of the bigger length are called **long** and of the smaller length are called **short**.

It is easy to see that long and short roots form a root system of the same rank (but not necessarily irreducible). For instance, in  $G_2$  both form a root system of type  $A_2$ , and in  $B_2$  both are  $A_1 \times A_1$ . In  $B_3$  long roots form  $D_3$  and short ones form  $A_1 \times A_1 \times A_1$ . However, only long roots form a root subsystem, since a long positive root can be the sum of two short ones, but not vice versa.

# 24. Construction of a semisimple Lie algebra from a Dynkin diagram

24.1. Serre relations. Let  $\mathbf{k}$  be an algebraically closed field of characteristic zero. We would like to show that any reduced root system gives rise to a semisimple Lie algebra over  $\mathbf{k}$ , and moreover a unique one. To this end, it suffices to show that any reduced *irreducible* root system gives rise to a unique (finite dimensional) *simple* Lie algebra.

Let  $\mathfrak{g}$  be a finite dimensional simple Lie algebra over  $\mathbf{k}$  with Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}$  and root system  $R \subset \mathfrak{h}^*$  (which is thus reduced and irreducible). Fix a polarization of R with the set of simple roots  $\Pi = (\alpha_1, ..., \alpha_r)$ , and let  $A = (a_{ij})$  be the Cartan matrix of R. We have a decomposition  $\mathfrak{g} = \mathfrak{n}_+ \oplus \mathfrak{h} \oplus \mathfrak{n}_-$ , where  $\mathfrak{n}_{\pm} := \oplus_{\alpha \in R_{\pm}} \mathfrak{g}_{\alpha}$  are the Lie subalgebras spanned by positive, respectively negative root vectors. Pick elements  $e_i \in \mathfrak{g}_{\alpha_i}$ ,  $f_i \in \mathfrak{g}_{-\alpha_i}$  so that  $e_i, f_i, h_i = [e_i, f_i]$  form an  $\mathfrak{sl}_2$ -triple.

**Theorem 24.1.** (Serre relations) (i) The elements  $e_i$ ,  $f_i$ ,  $h_i$ , i = 1, ..., r generate  $\mathfrak{g}$ .

(ii) These elements satisfy the following relations:

$$[h_i, h_j] = 0, [h_i, e_j] = a_{ij}e_j, [h_i, f_j] = -a_{ij}f_j, [e_i, f_j] = \delta_{ij}h_i,$$
  
 $(ade_i)^{1-a_{ij}}e_j = 0, (adf_i)^{1-a_{ij}}f_j = 0, i \neq j.$ 

The last two sets of relations are called **Serre relations**. Note that if  $a_{ij} = 0$  then the Serre relations just say that  $[e_i, e_j] = [f_i, f_j] = 0$ .

*Proof.* (i) We know that  $h_i$  form a basis of  $\mathfrak{h}$ , so it suffices to show that  $e_i$  generate  $\mathfrak{n}_+$  and  $f_i$  generate  $\mathfrak{n}_-$ . We only prove the first statement, the second being the same for the opposite polarization.

Let  $\mathfrak{n}'_{+} \subset \mathfrak{n}_{+}$  be the Lie subalgebra generated by  $e_{i}$ . It is clear that  $\mathfrak{n}'_{+} = \bigoplus_{\alpha \in R'_{+}} \mathfrak{g}_{\alpha}$  where  $R'_{+} \subset R_{+}$ . Assume the contrary, that  $R'_{+} \neq R_{+}$ . Pick  $\alpha \in R_{+} \setminus R'_{+}$  with the smallest height (it is not a simple root). Then  $\mathfrak{g}_{\alpha-\alpha_{i}} \subset \mathfrak{n}'_{+}$ , so  $[e_{i}, \mathfrak{g}_{\alpha-\alpha_{i}}] = 0$ . Let  $x \in \mathfrak{g}_{-\alpha}$  be a nonzero element. We have

$$([x, e_i], y) = (x, [e_i, y]) = 0$$

for any  $y \in \mathfrak{g}_{\alpha-\alpha_i}$ . Thus  $[x,e_i] = 0$  for all i, which implies, by the representation theory of  $\mathfrak{sl}_2$  (Subsection 11.4), that  $(\alpha,\alpha_i^{\vee}) \leq 0$  for all i, hence  $(\alpha,\alpha_i) \leq 0$  for all i. This would imply that  $(\alpha,\alpha) \leq 0$ , a contradiction. This proves (i).

(ii) All the relations except the Serre relations follow from the definition and properties of root systems. So only the Serre relations require proof. We prove only the relation involving  $f_i$ , the other one

being the same for the opposite polarization. Consider the  $(\mathfrak{sl}_2)_i$ submodule  $M_{ij}$  of  $\mathfrak{g}$  generated by  $f_j$ . It is finite dimensional and
we have  $[h_i, f_j] = -a_{ij}f_j$ ,  $[e_i, f_j] = 0$ . Thus by the representation
theory of  $\mathfrak{sl}_2$  (Subsection 11.4) we must have  $M_{ij} \cong V_{-a_{ij}}$ . Hence  $(\operatorname{ad} f_i)^{-a_{ij}+1}f_j = 0$ .

24.2. The Serre presentation for semisimple Lie algebras. Now for any reduced root system R let  $\mathfrak{g}(R)$  be the Lie algebra generated by  $e_i, f_i, h_i, i = 1, ..., r$ , with **defining relations** being the relations of Theorem 24.1. Precisely, this means that  $\mathfrak{g}(R)$  is the quotient of the free Lie algebra  $FL_{3r}$  with generators  $e_i, f_i, h_i$  modulo the Lie ideal generated by the differences of the left and right hand sides of these relations.

**Theorem 24.2.** (Serre) (i) The Lie subalgebra  $\mathfrak{n}_+$  of  $\mathfrak{g}(R)$  generated by  $e_i$  has the Serre relations  $(ade_i)^{1-a_{ij}}e_j=0$  as the defining relations. Similarly, the Lie subalgebra  $\mathfrak{n}_-$  of  $\mathfrak{g}(R)$  generated by  $f_i$  has the Serre relations  $(adf_i)^{1-a_{ij}}f_j=0$  as the defining relations. In particular,  $e_i, f_i \neq 0$  in  $\mathfrak{g}(R)$ . Moreover,  $h_i$  are linearly independent.

- (ii)  $\mathfrak{g}(R)$  is a sum of finite dimensional modules over every simple root subalgebra  $(\mathfrak{sl}_2)_i = (e_i, f_i, h_i)$ .
  - (iii)  $\mathfrak{g}(R)$  is finite dimensional.
  - (iv)  $\mathfrak{g}(R)$  is semisimple and has root system R.

*Proof.* It is easy to see that  $\mathfrak{g}(R_1 \sqcup R_2) = \mathfrak{g}(R_1) \oplus \mathfrak{g}(R_2)$ , so it suffices to prove the theorem for irreducible root systems.

(i) Consider the (in general, infinite dimensional) Lie algebra  $\mathfrak{g}(\bar{R})$  generated by  $e_i$ ,  $f_i$ ,  $h_i$  with the defining relations of Theorem 24.1 without the Serre relations. This Lie algebra is  $\mathbb{Z}$ -graded, with  $\deg(e_i)=1$ ,  $\deg(f_i)=-1$ ,  $\deg(h_i)=0$ . Thus we have a decomposition

$$\widetilde{\mathfrak{g}(R)} = \widetilde{\mathfrak{n}_+} \oplus \widetilde{\mathfrak{h}} \oplus \widetilde{\mathfrak{n}_-},$$

where  $\widetilde{\mathfrak{n}_+}$ ,  $\widetilde{\mathfrak{h}}$  and  $\widetilde{\mathfrak{n}_-}$  are Lie subalgebras spanned by elements of positive, zero and negative degree, respectively. Moreover, it is easy to see that  $\widetilde{\mathfrak{n}_+}$  is generated by  $e_i$ ,  $\widetilde{\mathfrak{n}_-}$  is generated by  $f_i$ , and  $\widetilde{\mathfrak{h}}$  is spanned by  $h_i$  (indeed, any commutator can be simplified to have only  $e_i$ , only  $f_i$ , or only a single  $h_i$ ).

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

**Corollary 24.4.** Isomorphism classes of simple Lie algebras over  $\mathbf{k}$  are in bijection with Dynkin diagrams  $A_n$ ,  $n \geq 1$ ,  $B_n$ ,  $n \geq 2$ ,  $C_n$ ,  $n \geq 3$ ,  $D_n$ ,  $n \geq 4$ ,  $E_6$ ,  $E_7$ ,  $E_8$ ,  $F_4$  and  $G_2$ .

#### 25. Representation theory of semisimple Lie algebras

25.1. Representations of semisimple Lie algebras. We will now develop representation theory of complex semisimple Lie algebras. The representation theory of semisimple Lie algebras over an algebraically closed field of characteristic zero is completely parallel, so we will stick to the complex case. So all representations will be over  $\mathbb{C}$ . We will mostly be interested in finite dimensional representations; as we know, they can be exponentiated to holomorphic representations of the corresponding simply connected Lie group G, which defines a bijection between isomorphism classes of such representations of  $\mathfrak{g}$  and G.

Let  $\mathfrak{g}$  be a semisimple Lie algebra. Recall that by Theorem 18.9, every finite dimensional representation of  $\mathfrak{g}$  is completely reducible, so to classify finite dimensional representations it suffices to classify irreducible representations.

As in the simplest case of  $\mathfrak{sl}_2$ , a crucial tool is the decomposition of a representation in a direct sum of eigenspaces of a Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}$ .

**Definition 25.1.** Let  $\lambda \in \mathfrak{h}^*$ , and V a representation of  $\mathfrak{g}$  (possibly infinite dimensional). Then a vector  $v \in V$  is said to have **weight**  $\lambda$  if  $hv = \lambda(h)v$  for all  $h \in \mathfrak{h}$ ; such vectors are called **weight vectors**. The subspace of such vectors is called the **weight subspace of** V **of weight**  $\lambda$  and denoted by  $V[\lambda]$ . If  $V[\lambda] \neq 0$ , we say that  $\lambda$  is a weight of V, and the set of weights of V is denoted by P(V).

It is easy to see that  $\mathfrak{g}_{\alpha}V[\lambda] \subset V[\lambda + \alpha]$ .

Let  $V' \subset V$  be the span of all weight vectors in V. Then it is clear that  $V' = \bigoplus_{\lambda \in \mathfrak{h}^*} V[\lambda]$ .

**Definition 25.2.** We say that V has a weight decomposition (with respect to a Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}$ ) if V' = V, i.e., if  $V = \bigoplus_{\lambda \in \mathfrak{h}^*} V[\lambda]$ .

Note that not every representation of  $\mathfrak{g}$  has a weight decomposition (e.g., for  $V = U(\mathfrak{g})$  with  $\mathfrak{g}$  acting by left multiplication all weight subspaces are zero).

**Proposition 25.3.** Any finite dimensional representation V of  $\mathfrak{g}$  has a weight decomposition. Moreover, all weights of V are integral, i.e., P(V) is a finite subset of the weight lattice  $P \subset \mathfrak{h}^*$  of  $\mathfrak{g}$ .

Proof. For each i=1,...,r,V is a finite dimensional representation of the root subalgebra  $(\mathfrak{sl}_2)_i$ , so its element  $h_i$  acts semisimply on V. Thus  $\mathfrak{h}$  acts semisimply on V, hence V has a weight decomposition. Also eigenvalues of  $h_i$  are integers, so for any  $\lambda \in P(V)$  we have  $\lambda(h_i) = (\lambda, \alpha_i^{\vee}) \in \mathbb{Z}$ , hence  $\lambda \in P$ .

Definition 25.4. A vector v in  $V[\lambda]$  is called a **highest weight vector** of weight  $\lambda$  if  $e_i v = 0$  for all i, i.e., if  $\mathfrak{n}_+ v = 0$ . A representation V of  $\mathfrak{g}$  is a **highest weight representation with highest weight**  $\lambda$  if it is generated by such a nonzero vector.

**Proposition 25.5.** Any finite dimensional representation  $V \neq 0$  contains a nonzero highest weight vector of some weight  $\lambda$ . Thus every irreducible finite dimensional representation of  $\mathfrak{g}$  is a highest weight representation.

*Proof.* Note that P(V) is a finite set. Let  $\rho^{\vee} = \sum_{i=1}^{r} \omega_i^{\vee}$ . Pick  $\lambda \in P(V)$  so that  $(\lambda, \rho^{\vee})$  is maximal. Then  $\lambda + \alpha_i \notin P(V)$  for any i, since  $(\lambda + \alpha_i, \rho^{\vee}) = (\lambda, \rho^{\vee}) + 1$ . Hence for any nonzero  $v \in V[\lambda]$  (which exists as  $\lambda \in P(V)$ ) we have  $e_i v = 0$ .

The second statement follows since an irreducible representation is generated by any of its nonzero vectors.  $\Box$ 

25.2. **Verma modules.** Even though we are mostly interested in finite dimensional representations of  $\mathfrak{g}$ , it is useful to consider some infinite dimensional representations, which are called **Verma modules**.

The Verma module  $M_{\lambda}$  is defined as "the largest highest weight representation with highest weight  $\lambda$ ". Namely, it is generated by a single highest weight vector  $v_{\lambda}$  with **defining relations**  $hv = \lambda(h)v$  for  $h \in \mathfrak{h}$  and  $e_iv = 0$ . More formally speaking, we make the following definition.

**Definition 25.6.** Let  $I_{\lambda} \subset U(\mathfrak{g})$  be the left ideal generated by the elements  $h - \lambda(h), h \in \mathfrak{h}$  and  $e_i, i = 1, ..., r$ . Then the **Verma module**  $M_{\lambda}$  is the quotient  $U(\mathfrak{g})/I_{\lambda}$ .

In this realization, the highest weight vector  $v_{\lambda}$  is just the class of the unit 1 of  $U(\mathfrak{g})$ .

**Proposition 25.7.** The map  $\phi: U(\mathfrak{n}_{-}) \to M_{\lambda}$  given by  $\phi(x) = xv_{\lambda}$  is an isomorphism of left  $U(\mathfrak{n}_{-})$ -modules.

*Proof.* By the PBW theorem, the multiplication map

$$\xi: U(\mathfrak{n}_-) \otimes U(\mathfrak{h} \oplus \mathfrak{n}_+) \to U(\mathfrak{g})$$

is a linear isomorphism. It is easy to see that  $\xi^{-1}(I_{\lambda}) = U(\mathfrak{n}_{-}) \otimes K_{\lambda}$ , where

$$K_{\lambda} := \sum_{i} U(\mathfrak{h} \oplus \mathfrak{n}_{+})(h_{i} - \lambda(h_{i})) + \sum_{i} U(\mathfrak{h} \oplus \mathfrak{n}_{+})e_{i}$$

is the kernel of the homomorphism  $\lambda_+: U(\mathfrak{h} \oplus \mathfrak{n}_+) \to \mathbb{C}$  given by  $\lambda_+(h) = \lambda(h), h \in \mathfrak{h}, \lambda_+(e_i) = 0$ . Thus, we have a natural isomorphism

of left  $U(\mathfrak{n}_{-})$ -modules

$$U(\mathfrak{n}_{-}) = U(\mathfrak{n}_{-}) \otimes U(\mathfrak{h} \oplus \mathfrak{n}_{+})/K_{\lambda} \to M_{\lambda},$$

as claimed.  $\Box$ 

Remark 25.8. The definition of  $M_{\lambda}$  means that it is the **induced** module  $U(\mathfrak{g}) \otimes_{U(\mathfrak{h} \oplus \mathfrak{n}_+)} \mathbb{C}_{\lambda}$ , where  $\mathbb{C}_{\lambda}$  is the one-dimensional representation of  $\mathfrak{h} \oplus \mathfrak{n}_+$  on which it acts via  $\lambda_+$ .

Recall that  $Q_+$  denotes the set of elements  $\sum_{i=1}^r k_i \alpha_i$  where  $k_i \in \mathbb{Z}_{\geq 0}$ . We obtain

Corollary 25.9.  $M_{\lambda}$  has a weight decomposition with  $P(M_{\lambda}) = \lambda - Q_{+}$ , dim  $M_{\lambda}[\lambda] = 1$ , and weight subspaces of  $M_{\lambda}$  are finite dimensional.

**Proposition 25.10.** (i) (Universal property of Verma modules) If V is a representation of  $\mathfrak{g}$  and  $v \in V$  is a vector such that  $hv = \lambda(h)v$  for  $h \in h$  and  $e_iv = 0$  for  $1 \leq i \leq r$  then there is a unique homomorphism  $\eta: M_{\lambda} \to V$  such that  $\eta(v_{\lambda}) = v$ . In particular, if V is generated by such  $v \neq 0$  (i.e., V is a highest weight representation with highest weight vector v) then V is a quotient of  $M_{\lambda}$ .

- (ii) Every highest weight representation has a weight decomposition into finite dimensional weight subspaces.
- *Proof.* (i) Uniqueness follows from the fact that  $v_{\lambda}$  generates  $M_{\lambda}$ . To construct  $\eta$ , note that we have a natural homomorphism of  $\mathfrak{g}$ -modules  $\widetilde{\eta}: U(\mathfrak{g}) \to V$  given by  $\widetilde{\eta}(x) = xv$ . Moreover,  $\widetilde{\eta}|_{I_{\lambda}} = 0$  thanks to the relations satisfied by v, so  $\widetilde{\eta}$  descends to a map  $\eta: U(\mathfrak{g})/I_{\lambda} = M_{\lambda} \to V$ . Moreover, if V is generated by v then this map is surjective, as desired.
- (ii) This follows from (i) since a quotient of any representation with a weight decomposition must itself have a weight decomposition.  $\Box$

Corollary 25.11. Every highest weight representation V has a unique highest weight generator, up to scaling.

*Proof.* Suppose v, w are two highest weight generators of V of weights  $\lambda, \mu$ . If  $\lambda = \mu$  then they are proportional since  $\dim V[\lambda] \leq \dim M_{\lambda}[\lambda] = 1$ , as V is a quotient of  $M_{\lambda}$ . On the other hand, if  $\lambda \neq \mu$ , then we can assume without loss of generality that  $\lambda - \mu \notin Q_+$  (otherwise switch  $\lambda, \mu$ ). Then  $\mu \notin \lambda - Q_+$ , hence  $\mu \notin P(V)$ , a contradiction.

**Proposition 25.12.** For every  $\lambda \in \mathfrak{h}^*$ , the Verma module  $M_{\lambda}$  has a unique irreducible quotient  $L_{\lambda}$ . Moreover,  $L_{\lambda}$  is a quotient of every highest weight  $\mathfrak{g}$ -module V with highest weight  $\lambda$ .

*Proof.* Let  $Y \subset M_{\lambda}$  be a proper submodule. Then Y has a weight decomposition, and cannot contain a nonzero multiple of  $v_{\lambda}$  (as otherwise

 $Y=M_{\lambda}$ ), so  $P(Y)\subset (\lambda-Q_{+})\setminus\{\lambda\}$ . Now let  $J_{\lambda}$  be the sum of all proper submodules  $Y\subset M_{\lambda}$ . Then  $P(J_{\lambda})\subset (\lambda-Q_{+})\setminus\{\lambda\}$ , so  $J_{\lambda}$  is also a proper submodule of  $M_{\lambda}$  (the maximal one). Thus,  $L_{\lambda}:=M_{\lambda}/J_{\lambda}$  is an irreducible highest weight module with highest weight  $\lambda$ . Moreover, if V is any nonzero quotient of  $M_{\lambda}$  then the kernel K of the map  $M_{\lambda}\to V$  is a proper submodule, hence contained in  $J_{\lambda}$ . Thus the surjective map  $M_{\lambda}\to L_{\lambda}$  descends to a surjective map  $V\to L_{\lambda}$ . The kernel of this map is a proper submodule of V, hence zero if V is irreducible. Thus in the latter case  $V\cong L_{\lambda}$ .

Corollary 25.13. Irreducible highest weight  $\mathfrak{g}$ -modules are classified by their highest weight  $\lambda \in \mathfrak{h}^*$ , via the bijection  $\lambda \mapsto L_{\lambda}$ .

25.3. Finite dimensional modules. Since every finite dimensional irreducible  $\mathfrak{g}$ -module is highest weight, it is of the form  $L_{\lambda}$  for  $\lambda$  belonging to some subset  $P_F \subset P$ , the set of weights  $\lambda$  such that  $L_{\lambda}$  is finite dimensional. So to obtain a final classification of finite dimensional irreducible representations of  $\mathfrak{g}$ , we should determine the subset  $P_F$ .

Let  $P_+ \subset P$  be the intersection of P with the closure of the dominant Weyl chamber  $C_+$ ; i.e.,  $P_+$  is the set of nonnegative integer linear combinations of the fundamental weights  $\omega_i$ . In other words,  $P_+$  is the set of  $\lambda \in P$  such that  $(\lambda, \alpha_i^{\vee}) \in \mathbb{Z}_+$  for  $1 \leq i \leq r$ . Weights belonging to  $P_+$  are called **dominant integral**.

#### **Proposition 25.14.** We have $P_F \subset P_+$ .

*Proof.* The vector  $v_{\lambda}$  is highest weight for  $(\mathfrak{sl}_2)_i$  with highest weight  $\lambda(h_i) = (\lambda, \alpha_i^{\vee})$ . This must be a nonnegative integer for the corresponding  $\mathfrak{sl}_2$ -module to be finite dimensional.

**Lemma 25.15.** If  $\lambda \in P_+$  then in  $L_{\lambda}$ , we have  $f_i^{\lambda(h_i)+1}v_{\lambda}=0$ .

Proof. By the representation theory of  $\mathfrak{sl}_2$  (Subsection 11.4), we have  $e_i f_i^{\lambda(h_i)+1} v_{\lambda} = 0$ . Also  $e_j f_i^{\lambda(h_i)+1} v_{\lambda} = 0$  for  $j \neq i$  since  $[e_j, f_i] = 0$ . Thus,  $w := f_i^{\lambda(h_i)+1} v_{\lambda}$  is a highest weight vector in  $L_{\lambda}$ . So w cannot be a generator (as the highest weight generator is unique up to scaling). Thus w generates a proper submodule in  $L_{\lambda}$ , which must be zero since  $L_{\lambda}$  is irreducible.

**Lemma 25.16.** Let V be a  $\mathfrak{g}$ -module with weight decomposition into finite dimensional weight subspaces. If V is a sum of finite dimensional  $(\mathfrak{sl}_2)_i$ -modules for each i = 1, ..., r, then for each  $\lambda \in P$  and  $w \in W$ ,  $\dim V[\lambda] = \dim V[w\lambda]$ . In particular, P(V) is W-invariant.

*Proof.* Since the Weyl group W is generated by the simple reflections  $s_i$ , it suffices to prove the statement for  $w = s_i$ , and in fact to prove that dim  $V[\lambda] \leq \dim V[s_i\lambda]$  (as  $s_i^2 = 1$ ).

If  $(\lambda, \alpha_i^{\vee}) = m \geq 0$  then consider the operator  $f_i^m : V[\lambda] \to V[s_i\lambda]$ . We claim that this operator is injective, which implies the desired inequality. Indeed, let  $v \in V[\lambda]$  be a nonzero vector and E be the representation of  $(\mathfrak{sl}_2)_i$  generated by v. Then E is finite dimensional, and  $v \in E[m]$ , so by the representation theory of  $\mathfrak{sl}_2$  (Subsection 11.4),  $f_i^m v \neq 0$ , as claimed.

Similarly, if  $(\lambda, \alpha_i^{\vee}) = -m \leq 0$  then the operator  $e_i^m : V[\lambda] \to V[s_i\lambda]$  is injective. This proves the lemma.

Now we are ready to state the main classification theorem.

**Theorem 25.17.** For any  $\lambda \in P_+$ ,  $L_{\lambda}$  is finite dimensional; i.e.,  $P_F = P_+$ . Thus finite dimensional irreducible representations of  $\mathfrak{g}$  are classified, up to an isomorphism, by their highest weight  $\lambda \in P_+$ , via the bijection  $\lambda \mapsto L_{\lambda}$ . Moreover, for any  $\mu \in P$  and  $w \in W$ ,  $\dim L_{\lambda}[\mu] = \dim L_{\lambda}[w\mu]$ .

*Proof.* Since  $f_i^{\lambda(h_i)+1}v_{\lambda}=0$ , we see that  $v_{\lambda}$  generates the irreducible finite dimensional  $(\mathfrak{sl}_2)_i$ -module of highest weight  $\lambda(h_i)$ . Also, every nonzero element of  $\mathfrak{g}$  generates a finite dimensional  $(\mathfrak{sl}_2)_i$ -module. But every vector of  $L_{\lambda}$  is a linear combination of vectors of the form  $a_1...a_Nv_{\lambda}, a_i \in \mathfrak{g}$ . Hence every vector in  $L_{\lambda}$  generates a finite dimensional  $(\mathfrak{sl}_2)_i$ -module. Thus by Lemma 25.16,  $P(L_{\lambda})$  is W-invariant.

Now let  $\mu \in P(L_{\lambda}) \cap P_{+}$ . Then  $\mu = \lambda - \beta$ ,  $\beta \in Q_{+}$ , so

$$(\mu, \rho^{\vee}) = (\lambda, \rho^{\vee}) - (\beta, \rho^{\vee}) \le (\lambda, \rho^{\vee}).$$

So if  $\mu = \sum_i m_i \omega_i$ ,  $m_i \in \mathbb{Z}_+$  then  $\sum_i m_i(\omega_i, \rho^{\vee}) \leq (\lambda, \rho^{\vee})$ . Since  $(\omega_i, \rho^{\vee}) \geq \frac{1}{2}$ , this implies that  $P(L_{\lambda}) \cap P_+$  is finite. But we know that  $WP_+ = P$ , hence  $W(P(L_{\lambda}) \cap P_+) = P(L_{\lambda})$ , as  $P(L_{\lambda})$  is W-invariant. It follows that  $P(L_{\lambda})$  is finite, hence  $L_{\lambda}$  is finite dimensional.  $\square$ 

**Example 25.18.** For  $\mathfrak{g} = \mathfrak{sl}_2$  the dominant integral weights are positive integers  $n \in \mathbb{Z}_{\geq 0}$ , and it is easy to see that  $L_n = V_n$ .

#### 26. The Weyl character formula

26.1. Characters. Let V be a finite dimensional representation of a semisimple Lie algebra  $\mathfrak{g}$ . Recall that the action of  $\mathfrak{g}$  on V can be exponentiated to the action of the corresponding simply connected complex Lie group G. Recall also that the **character** of a finite dimensional representation V of any group G is the function

$$\chi_V(g) = \text{Tr}|_V(g).$$

Let us compute this character in our case. To this end, let  $\mathfrak{h} \subset \mathfrak{g}$  be a Cartan subalgebra,  $h \in \mathfrak{h}$ , and let us compute  $\chi_V(e^h)$ . Note that this completely determines  $\chi_V$  since it determines  $\chi_V(e^x)$  for any semisimple element  $x \in \mathfrak{g}$ , and semisimple elements form a dense open set in  $\mathfrak{g}$  (complement of zeros of some polynomial). So elements of the form  $e^x$  as above form a dense open set at least in some neighborhood of 1 in G, and an analytic function on G is determined by its values on any nonempty open set.

We know that V has a weight decomposition:  $V = \bigoplus_{\mu \in P} V[\mu]$ . Thus we have

$$\chi_V(e^h) = \sum_{\mu \in P} \dim V[\mu] e^{\mu(h)}.$$

Consider the group algebra  $\mathbb{Z}[P]$ . It sits naturally inside the algebra of analytic functions on  $\mathfrak{h}$  via  $\lambda \mapsto e^{\lambda}$ , where  $e^{\lambda}(h) := e^{\lambda(h)}$ , and we see that  $\chi_V \in \mathbb{Z}[P]$ , namely

$$\chi_V = \sum_{\mu \in P} \dim V[\mu] e^{\mu}.$$

We will call the element  $\chi_V$  the character of V.

26.2. Category  $\mathcal{O}$ . Note that the above definition of character is a purely formal algebraic definition, i.e.,  $\chi_V$  is simply the generating function of dimensions of weight subspaces of V. So it makes sense for any (possibly infinite dimensional) representation V with a weight decomposition into finite dimensional weight subspaces, except we may obtain an infinite sum. More precisely, we make the following definition.

**Definition 26.1.** The category  $\mathcal{O}_{\text{int}}$  is the category of representations V of  $\mathfrak{g}$  with weight decomposition into finite dimensional weight spaces  $V = \bigoplus_{\mu \in P} V[\mu]$ , such that P(V) is contained in the union of sets  $\lambda^i - Q_+$  for a finite collection of weights  $\lambda^1, ..., \lambda^N \in P$  (depending on V).<sup>13</sup>

<sup>&</sup>lt;sup>13</sup>Usually one also adds the condition that V is a finitely generated  $U(\mathfrak{g})$ -module, but we don't need this condition here, so we won't impose it.

Here the subscript "int" indicates that we consider only integral weights (i.e., ones in P). However, for brevity we will drop this subscript in this section and just denote this category by  $\mathcal{O}$ .

For example, any highest weight module belongs to  $\mathcal{O}$ .

Let  $\mathcal{R}$  be the ring of series  $a := \sum_{\mu \in P} a_{\mu} e^{\mu}$   $(a_{\mu} \in \mathbb{Z})$  such that the set P(a) of  $\mu$  with  $a_{\mu} \neq 0$  is contained in the union of sets  $\lambda^{i} - Q_{+}$  for a finite collection of weights  $\lambda^{1}, ..., \lambda^{N} \in P$ . Then for every  $V \in \mathcal{O}$  we can define the character  $\chi_{V} \in \mathcal{R}$ . Moreover, it is easy to see that if

$$0 \to X \to Y \to Z \to 0$$

is a short exact sequence in  $\mathcal{O}$  then  $\chi_Y = \chi_X + \chi_Z$ , and that for any  $V, U \in \mathcal{O}$  we have  $V \otimes U \in \mathcal{O}$  and  $\chi_{V \otimes U} = \chi_V \chi_U$ .

**Example 26.2.** Let  $V = M_{\lambda}$  be the Verma module. Recall that as a vector space  $M_{\lambda} = U(\mathfrak{n}_{-})v_{\lambda}$ , and that  $U(\mathfrak{n}_{-}) = \bigotimes_{\alpha \in R_{+}} \mathbb{C}[e_{-\alpha}]$  (using the PBW theorem). Thus

$$\sum_{\mu} U(\mathfrak{n}_{-})[\mu] e^{\mu} = \frac{1}{\prod_{\alpha \in R_{+}} (1 - e^{-\alpha})}$$

and hence

$$\chi_{M_{\lambda}} = \frac{e^{\lambda}}{\prod_{\alpha \in R_{+}} (1 - e^{-\alpha})}.$$

It is convenient to rewrite this formula as follows:

$$\chi_{M_{\lambda}} = \frac{e^{\lambda+\rho}}{\Delta}, \ \Delta := \prod_{\alpha \in R_+} (e^{\alpha/2} - e^{-\alpha/2}).$$

The (trigonometric) polynomial  $\Delta$  is called the **Weyl denominator**.

Note that we have a homomorphism  $\varepsilon: W \to \mathbb{Z}/2$  given by the formula  $w \mapsto \det(w|_{\mathfrak{h}})$ , i.e.  $w \mapsto (-1)^{\ell(w)}$ ; it is defined on simple reflections by  $s_i \mapsto -1$ . This homomorphism is called the **sign character**. For example, for type  $A_{n-1}$  this is the sign of a permutation in  $S_n$ . We will say that an element of  $f \in \mathbb{C}[P]$  is **anti-invariant** under W if  $w(f) = (-1)^{\ell(w)} f$  for all  $w \in W$ .

**Proposition 26.3.** The Weyl denominator  $\Delta$  is anti-invariant under W.

*Proof.* Since  $s_i$  permutes positive roots not equal to  $\alpha_i$  and sends  $\alpha_i$  to  $-\alpha_i$ , it follows that  $s_i\Delta = -\Delta$ .

# 26.3. The Weyl character formula.

**Theorem 26.4.** (Weyl character formula) For any  $\lambda \in P_+$  the character  $\chi_{\lambda} := \chi_{L_{\lambda}}$  of the irreducible finite dimensional representation  $L_{\lambda}$  is given by

$$\chi_{\lambda} = \frac{\sum_{w \in W} (-1)^{\ell(w)} e^{w(\lambda + \rho)}}{\Lambda}.$$

The proof of this theorem is in the next subsection.

Corollary 26.5. (Weyl denominator formula) One has

$$\Delta = \sum_{w \in W} (-1)^{\ell(w)} e^{w\rho}.$$

*Proof.* This follows from the Weyl character formula by setting  $\lambda = 0$  (as  $L_0 = \mathbb{C}$  is the trivial representation).

For example, for  $\mathfrak{g} = \mathfrak{sl}_n$  Corollary 26.5 reduces to the usual product formula for the Vandermonde determinant.

26.4. **Proof of the Weyl character formula.** Consider the product  $\Delta \chi_{\lambda} \in \mathbb{Z}[P]$ . We know that  $\chi_{\lambda}$  is W-invariant, so this product is W-anti-invariant. Thus,

$$\Delta \chi_{\lambda} = \sum_{\mu \in P} c_{\mu} e^{\mu},$$

where  $c_{w\mu} = (-1)^{\ell(w)} c_{\mu}$ . Moreover,  $c_{\mu} = 0$  unless  $\mu \in \lambda + \rho - Q_{+}$ , and  $c_{\lambda+\rho} = 1$ . Thus to prove the Weyl character formula, we need to show that  $c_{\mu} = 0$  if  $\mu \in P_{+} \cap (\lambda + \rho - Q_{+})$  and  $\mu \neq \lambda + \rho$ .

To this end, we will construct the above decomposition  $\Delta \chi_{\lambda}$  using representation theory, so that this vanishing property is apparent from the construction.

First recall from Subsection 18.3 that we have the Casimir element C of  $U(\mathfrak{g})$  given by the formula  $C = \sum_i a_i a^i$  for a basis  $a_i \in \mathfrak{g}$  with dual basis  $a^i$  of  $\mathfrak{g}$  under the Killing form. This element is central, so acts by a scalar on every highest weight (in particular, finite dimensional irreducible) representation. We can write C in the form

$$C = \sum_{j} x_j^2 + \sum_{\alpha \in R_+} (e_{-\alpha}e_{\alpha} + e_{\alpha}e_{-\alpha}),$$

for an orthonormal basis  $x_j$  of  $\mathfrak{h}$ . Since  $[e_{\alpha}, e_{-\alpha}] = h_{\alpha}$ , we find that

$$C = \sum_{j} x_j^2 + 2 \sum_{\alpha \in R_+} e_{-\alpha} e_{\alpha} + \sum_{\alpha \in R_+} h_{\alpha}.$$

Thus we get

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

**Exercise 26.7.** Let Q be the root lattice of a simple Lie algebra  $\mathfrak{g}$ ,  $Q_+$  its positive part. Define the **Kostant partition function** to be the function  $p: Q \to \mathbb{Z}_{>0}$  which attaches to  $\beta \in Q_+$  the number of ways

to write  $\beta$  as a sum of positive roots of  $\mathfrak{g}$  (where the order does not matter), and  $p(\beta) = 0$  if  $\beta \notin Q_+$ .

(i) Show that

$$\sum_{\beta \in Q_+} p(\beta)e^{-\beta} = \frac{1}{\prod_{\alpha \in R_+} (1 - e^{-\alpha})}.$$

(ii) Prove the Kostant multiplicity formula

$$\dim L_{\lambda}[\gamma] = \sum_{w \in W} (-1)^{\ell(w)} p(w(\lambda + \rho) - \rho - \gamma).$$

- (iii) Compute  $p(k_1\alpha_1 + k_2\alpha_2)$  for  $\mathfrak{g} = \mathfrak{sl}_3$  and  $\mathfrak{g} = \mathfrak{sp}_4$ .
- (iv) Use (iii) to compute explicitly the weight multiplicities of the irreducible representations  $L_{\lambda}$  for  $\mathfrak{g} = \mathfrak{sl}_3$  and  $\mathfrak{g} = \mathfrak{sp}_4$ . (You should get a sum of 6, respectively 8 terms, not particularly appealing, but easily computable in each special case).

26.5. The Weyl dimension formula. Recall that the Weyl character formula can be written as a trace formula: for  $h \in \mathfrak{h}$ 

$$\chi_{\lambda}(e^{h}) = \text{Tr}|_{L_{\lambda}}(e^{h}) = \frac{\sum_{w \in W} (-1)^{\ell(w)} e^{(w(\lambda + \rho), h)}}{\prod_{\alpha \in R_{+}} (e^{\frac{1}{2}(\alpha, h)} - e^{-\frac{1}{2}(\alpha, h)})}.$$

The dimension of  $L_{\lambda}$  should be obtained from this formula when h=0. However, we do not immediately get the answer since this formula gives the character as a ratio of two trigonometric polynomials which both vanish at h=0, giving an indeterminacy. We know the limit exists since the character is a trigonometric polynomial, but we need to compute it. This can be done as follows.

Let us restrict attention to  $h=2th_{\rho}$  where  $t\in\mathbb{R}$  and  $h_{\rho}\in\mathfrak{h}$  corresponds to  $\rho\in\mathfrak{h}^*$  using the identification induced by the invariant form. We have

$$\chi_{\lambda}(e^{2th_{\rho}}) = \frac{\sum_{w \in W} (-1)^{\ell(w)} e^{2t(w(\lambda+\rho),\rho)}}{\prod_{\alpha \in R_{+}} (e^{t(\alpha,\rho)} - e^{-t(\alpha,\rho)})}.$$

The key idea is that for this specialization the numerator can also be factored using the denominator formula, which will allow us to resolve the indeterminacy. Namely, we have

(26.2) 
$$\chi_{L_{\lambda}}(e^{2th_{\rho}}) = \frac{\prod_{\alpha \in R_{+}} (e^{t(\alpha,\lambda+\rho)} - e^{-t(\alpha,\lambda+\rho)})}{\prod_{\alpha \in R_{+}} (e^{t(\alpha,\rho)} - e^{-t(\alpha,\rho)})}.$$

Now sending  $t \to 0$ , we obtain

Proposition 26.8. We have

$$\dim L_{\lambda} = \frac{\prod_{\alpha \in R_{+}} (\alpha, \lambda + \rho)}{\prod_{\alpha \in R_{+}} (\alpha, \rho)}.$$

Note that this number is an integer, but this is not obvious without its interpretation as the dimension of a representation.

Formula (26.2) has a meaning even before taking the limit. Namely, the eigenvalues of the element  $2h_{\rho}$  define a  $\mathbb{Z}$ -grading on the representation  $L_{\lambda}$  called the **principal grading**, and we obtain a product formula for the Poincaré polynomial of this grading.

# Lie groups and Lie algebras II

# 27. Representations of $GL_n$ , I

We begin with a more detailed study of finite dimensional represen-tations of semisimple Lie algebras and the corresponding complex Lie groups.

27.1. Tensor products of fundamental representations. The following result shows that if we understand fundamental representations of a semisimple Lie algebra  $\mathfrak{g}$  (i.e., irreducible representations with fundamental highest weights  $\omega_i$ ), we can gain some insight into general finite dimensional representations.

**Proposition 27.1.** Let  $\lambda = \sum_{i=1}^r m_i \omega_i$  be a dominant integral weight for  $\mathfrak{g}$ . Consider the tensor product  $T_{\lambda} := \bigotimes_i L_{\omega_i}^{\otimes m_i}$ , and let  $v := \bigotimes_i v_{\omega_i}^{\otimes m_i}$  be the tensor product of the highest weight vectors. Let V be the sub-representation of  $T_{\lambda}$  generated by v. Then  $V \cong L_{\lambda}$ .

Proof. We have  $V = L_{\lambda} \oplus \bigoplus_{\mu \in (\lambda - Q_+) \cap P_+} N_{\lambda\mu} L_{\mu}$  where  $N_{\lambda\mu}$  are positive integers. Let  $C \in U(\mathfrak{g})$  be the Casimir element for  $\mathfrak{g}$ . Recall that  $C|_{L_{\mu}} = (\mu, \mu + 2\rho)$ . Thus  $C|_{V} = (\lambda, \lambda + 2\rho)$ . But we have seen in the proof of the Weyl character formula that for any  $\mu \in (\lambda - Q_+) \cap P_+$  such that  $\mu \neq \lambda$ , we have  $(\mu, \mu + 2\rho) < (\lambda, \lambda + 2\rho)$ . Therefore we see that  $N_{\lambda\mu} = 0$  for  $\mu \neq \lambda$ .

27.2. Representations of  $SL_n(\mathbb{C})$ . Let us now discuss more explicitly the representation theory of  $SL_n(\mathbb{C})$ . We will consider its finite dimensional complex analytic representations as a complex Lie group. We have shown that this is equivalent to considering finite dimensional representations of the Lie algebra  $\mathfrak{sl}_n(\mathbb{C})$ . We have also seen that these are completely reducible and the irreducible representations are  $L_{\lambda}$ , where  $\lambda = \sum_{i=1}^{n-1} m_i \omega_i$ ,  $\omega_i$  are the fundamental weights, and  $m_i \in \mathbb{Z}_{\geq 0}$ .

First let us compute  $\omega_i$ . Recall that the standard Cartan subalgebra  $\mathfrak{h}$  is the space  $\mathbb{C}_0^n$  of vectors in  $\mathbb{C}^n$  with zero sum of coordinates (diagonal matrices with trace zero). So elements of  $\mathfrak{h}^*$  can be viewed as vectors  $(x_1, ..., x_n) \in \mathbb{C}^n$  modulo simultaneous shift of all coordinates by the same number (i.e.,  $\mathfrak{h}^* = \mathbb{C}^n/\mathbb{C}_{\text{diag}}$ ).

Recall that the simple roots are  $\alpha_i^{\vee} = \mathbf{e}_i - \mathbf{e}_{i+1}$ . Thus  $\omega_i$  are determined by the conditions

$$(\omega_i, \mathbf{e}_j - \mathbf{e}_{j+1}) = \delta_{ij}.$$

This means that  $\omega_i = (1, ..., 1, 0, ..., 0)$  where there are *i* copies of 1. Thus a dominant integral weight  $\lambda$  has the form

$$\lambda = (m_1 + \dots + m_{n-1}, m_2 + \dots + m_{n-1}, \dots, m_{n-1}, 0).$$

So dominant integral weights are parametrized by non-increasing sequences  $\lambda_1 \geq ... \geq \lambda_{n-1}$  of nonnegative integers. This agrees with the representation theory of  $SL_2(\mathbb{C})$  that we worked out before: in this case the sequence has just one term.

Let us now describe explicitly the fundamental representations  $L_{\omega_i}$ . Consider first the representation  $V=\mathbb{C}^n$  with the usual action of matrices. It is called the **vector representation** or the **tautological representation** (as every matrix goes to itself). It is irreducible and has a standard basis  $v_1, ..., v_n$ . To find its highest weight, we have to find a vector  $v \neq 0$  such that  $e_i v = 0$ . As  $e_i = E_{i,i+1}$ , we have  $v = v_1$ . It is easy to see that  $hv = \omega_1(h)v$ , so we see that v has weight  $\omega_1$ , hence  $L_{\omega_1} = V$ .

To construct  $L_{\omega_m}$  for m > 1, consider the exterior power  $\wedge^m V$ . It is easy to show that it is irreducible. A basis of  $\wedge^m V$  consists of wedges  $v_{i_1} \wedge ... \wedge v_{i_m}$  where  $i_1 < ... < i_m$ . The highest weight vector is clearly  $v_1 \wedge ... \wedge v_m$ , and it has weight  $\omega_m$ . Thus  $L_{\omega_m} = \wedge^m V$ .

Note that  $\wedge^n V = \mathbb{C}$  (the trivial representation) since every matrix in  $SL_n(\mathbb{C})$  acts by its determinant, which is 1, and  $\wedge^m V = 0$  for m > n. Also  $V^* \cong \wedge^{n-1} V$  since the wedge pairing  $V \otimes \wedge^{n-1} V \to \wedge^n V = \mathbb{C}$  is invariant and nondegenerate. Similarly,  $\wedge^m V^* \cong \wedge^{n-m} V$ .

We now see from Proposition 27.1 that the irreducible representation  $L_{\lambda}$  for  $\lambda = \sum_{i} m_{i}\omega_{i}$  is generated inside  $\bigotimes_{i=1}^{n-1} (\wedge^{i}V)^{\bigotimes m_{i}}$  by the tensor product of the highest weight vectors.

**Example 27.2.**  $L_{N\omega_1} = S^N V$ , generated by the vector  $v_1^{\otimes N} \in V^{\otimes N}$ .

27.3. Representations of  $GL_n(\mathbb{C})$ . Let us now explain how to extend these results to  $GL_n(\mathbb{C})$ . This is easy to do since  $GL_n(\mathbb{C})$  is not very different from the direct product  $\mathbb{C}^\times \times SL_n(\mathbb{C})$ . Namely,  $GL_n(\mathbb{C}) = (\mathbb{C}^\times \times SL_n(\mathbb{C}))/\mu_n$  where  $\mu_n$  is the group of roots of unity of order n embedded as  $z \mapsto (z^{-1}, z\mathbf{1}_n)$ . Indeed, the corresponding covering homomorphism  $\mathbb{C}^\times \times SL_n(\mathbb{C}) \to GL_n(\mathbb{C})$  is given by  $(z, A) \mapsto zA$ . So it suffices to classify irreducible holomorphic representations of the complex Lie group  $\mathbb{C}^\times \times SL_n(\mathbb{C})$ ; the irreducible holomorphic representations of  $GL_n(\mathbb{C})$  are a subset of them.

For n=1 this is just the problem of describing the holomorphic representations of  $\mathbb{C}^{\times}$ . This is easy. The Lie algebra is spanned by a single element h such that  $e^{2\pi ih}=1$ . This element must act in a representation by an operator H such that  $e^{2\pi iH}=1$ . It follows that H is diagonalizable with integer eigenvalues. Thus representations of  $\mathbb{C}^{\times}$  are completely reducible, with irreducibles  $\chi_N$  one-dimensional and labeled by integers  $N \in \mathbb{Z}$ ,  $\chi_N(z) = z^N$ .

The same argument leads to a similar answer for  $\mathbb{C}^{\times} \times SL_n$ : representations are completely reducible with irreducibles being  $L_{\lambda,N} = \chi_N \otimes L_{\lambda}$ . Moreover, the ones factoring through  $GL_n$  just have  $N = nr + \sum_{i=1}^{n-1} \lambda_i$  for some integer r.

Recall that  $GL_n$  has reductive Lie algebra  $\mathfrak{gl}_n$  with Cartan subalgebra  $\mathfrak{h} = \mathbb{C}^n$ . The highest weight of  $L_{\lambda,nm_n+\sum_{i=1}^{n-1}\lambda_i}$  is easily computed and equals  $(m_1+\ldots+m_{n-1}+m_n,\ldots,m_{n-1}+m_n,m_n)$ . Thus highest weights of finite dimensional representations are non-increasing sequences  $(\lambda_1,\ldots,\lambda_n)$  of integers which don't have to be positive. The fundamental representations are still  $L_{\omega_m} = \wedge^m V$ , and the only difference with  $SL_n$  is that now the top exterior power  $\wedge^n V$  is not trivial but rather is a 1-dimensional **determinant character** with highest weight  $\omega_n = (1,\ldots,1)$ . The highest weight of a finite dimensional representation then has the form  $\lambda = \sum_{i=1}^n m_i \omega_i$ , where  $m_i \geq 0$  for  $i \neq n$ , while  $m_n$  is an arbitrary integer. Consequently,  $L_{\lambda}$  is found inside  $\bigotimes_{i=1}^n (\wedge^i V)^{\otimes m_i}$  as the representation generated by the product of highest weight vectors. Note that it makes sense to take  $m_n < 0$ , as for a one-dimensional representation and k < 0 it is natural to define  $\chi^{\otimes k} := (\chi^*)^{\otimes -k}$ .

The representations with  $m_n \geq 0$  are especially important; it is easy to see that these are exactly the ones that occur inside  $V^{\otimes N}$  for some N (check it!). These representations are called **polynomial** since their matrix coefficients are polynomial functions of the matrix entries  $x_{ij}$  of  $X \in GL_n(\mathbb{C})$ , and consequently they extend by continuity to representations of the semigroup  $\operatorname{Mat}_n(\mathbb{C}) \supset GL_n(\mathbb{C})$ . Note that any irreducible representation is a polynomial one tensored with a non-positive power of the determinant character  $\wedge^n V$ .

27.4. Schur-Weyl duality. Note that highest weights of polynomial representations are non-increasing sequences of nonnegative integers  $(\lambda_1, ..., \lambda_n)$ , i.e. **partitions** with  $\leq n$  parts. Namely, they are partitions of  $|\lambda| = \sum_i \lambda_i$ , which is just the eigenvalue of  $\mathbf{1}_n \in \mathfrak{gl}_n$  on  $L_{\lambda}$  and can also be defined as the number N such that  $L_{\lambda}$  occurs in  $V^{\otimes N}$ .

Traditionally partitions are encoded by **Young diagrams.** Namely, the Young diagram of a partition  $\lambda = (\lambda_1, ..., \lambda_n)$  consists of n rows of boxes, the i-th row consisting of  $\lambda_i$  boxes, so that row i is placed directly under row i-1 and all rows start on the same vertical line. For example, here are the Young diagrams of the partitions (4,3,2) (left) and (3,3,2,1) (right):

Thus we have

$$V^{\otimes N} = \bigoplus_{\lambda: |\lambda| = N} L_{\lambda} \otimes \pi_{\lambda},$$

where  $\pi_{\lambda} := \operatorname{Hom}_{GL_n(\mathbb{C})}(L_{\lambda}, V^{\otimes N})$  are multiplicity spaces. Here the summation is over partitions of N, and  $L_{\lambda} = 0$  if  $\lambda$  has more than n parts. To understand the spaces  $\pi_{\lambda}$ , note that the symmetric group  $S_N$  acts on  $V^{\otimes N}$  and commutes with  $GL_n(\mathbb{C})$ , so it gets to act on each  $\pi_{\lambda}$ .

Let A be the image of  $U(\mathfrak{gl}_n)$  in  $\operatorname{End}_{\mathbb{C}}(V^{\otimes N})$ , and B be the image there of  $\mathbb{C}S_N$ . The algebras A, B commute.

**Theorem 27.3.** (Schur-Weyl duality) (i) The centralizer of A is B and vice versa.

- (ii) If  $\lambda$  has at most n parts then the representation  $\pi_{\lambda}$  of B (hence  $S_N$ ) is irreducible, and such representations are pairwise non-isomorphic.
- (iii) If dim  $V \geq N$  then  $\pi_{\lambda}$  exhaust all irreducible representations of  $S_N$ .

*Proof.* We start with

**Lemma 27.4.** If U is a  $\mathbb{C}$ -vector space then  $S^NU$  is spanned by elements  $x \otimes ... \otimes x$ ,  $x \in U$ .

*Proof.* It suffices to consider the case when U is finite dimensional. Then the span of these vectors is a nonzero subrepresentation in the irreducible GL(U)-representation  $S^NU$ , which implies the statement.

**Lemma 27.5.** For any associative algebra R over  $\mathbb{C}$ , the algebra  $S^NR$  is generated by elements

$$\Delta_N(x) := x \otimes 1 \otimes ... \otimes 1 + 1 \otimes x \otimes ... \otimes 1 + ... + 1 \otimes ... \otimes 1 \otimes x$$
 for  $x \in R$ .

*Proof.* Let  $P_N$  be the Newton polynomial expressing  $z_1...z_N$  via  $p_k := \sum_{i=1}^N z_i^k$ , k = 1, ..., N (it exists and is unique by the fundamental theorem on symmetric functions). Then we have

$$x \otimes ... \otimes x = P_N(\Delta_N(x), ..., \Delta_N(x^N)).$$

Hence the lemma follows from Lemma 27.4.

Let us now show that A is the centralizer  $Z_B$  of B. Note that  $Z_B = S^N(\text{End}V)$ . Thus the statement follows from Lemma 27.5.

We will now use the following easy but important lemma (which actually holds over any field).

**Lemma 27.6.** (Double centralizer lemma) Let V be a finite dimensional vector space and  $A, B \subset \operatorname{End} V$  be subalgebras such that B is isomorphic to a direct sum of matrix algebras and A is the centralizer of B. Then A is also isomorphic to a direct sum of matrix algebras, and moreover

$$V = \bigoplus_{i=1}^{n} W_i \otimes U_i,$$

where  $W_i$  run through all irreducible A-modules and  $U_i$  through irreducible B-modules. In particular, B is the centralizer of A and we have a natural bijection between irreducible A-modules and irreducible B-modules which matches  $W_i$  and  $U_i$ .

Proof. We have  $V = \bigoplus_{i=1}^n W_i \otimes U_i$  where  $U_i$  run through irreducible representations of B and  $W_i = \operatorname{Hom}_B(U_i, V) \neq 0$  are multiplicity spaces. Thus  $A = \bigoplus_{i=1}^n \operatorname{End} W_i$  and  $B = \bigoplus_{i=1}^n \operatorname{End} U_i$ , which implies the statement.

Since the algebra B is a direct sum of matrix algebras (by complete reducibility of representations of finite groups), Lemma 27.6 yields (i).<sup>14</sup>

To prove (ii), it suffices to note that if  $\lambda$  has  $\leq n$  parts then  $L_{\lambda}$  occurs in  $V^{\otimes N}$ , so  $\pi_{\lambda} \neq 0$ . The rest follows from (i) and Lemma 27.6.

(iii) If dim  $V \geq N$  then pick N linearly independent vectors  $v_1, ..., v_N \in V$ . It is easy to see that the map  $\mathbb{C}S_N \to V^{\otimes N}$  defined by  $s \mapsto s(v_1 \otimes ... \otimes v_N)$  is injective. Thus  $B = \mathbb{C}S_N$ . This implies the statement.

# Remark 27.7. The algebra A is called the Schur algebra and B the centralizer algebra.

Thus we see that representations of  $S_N$  are labeled by partitions  $\lambda$  of N, and those that occur in  $V^{\otimes N}$  correspond to the partitions that have  $\leq \dim V$  parts. Moreover, we claim that this labeling of representations by partitions does not depend on  $\dim V$ . To show this, suppose  $\lambda$  has  $\leq n$  parts and  $V = \mathbb{C}^n$ . We have the Schur-Weyl decomposition of  $GL_{n+1}(\mathbb{C}) \times S_N$ -modules

$$(V \oplus \mathbb{C})^{\otimes N} = \bigoplus_{\mu} L_{\mu}^{(n+1)} \otimes \pi_{\mu}^{(n+1)},$$

<sup>&</sup>lt;sup>14</sup>This also gives another proof of the fact that A is a direct sum of matrix algebras, i.e. complete reducibility of  $V^{\otimes N}$ .

Let us restrict this sum to  $GL_n(\mathbb{C}) \times S_N$ , and consider what happens to the summand  $L_{\lambda}^{(n+1)} \otimes \pi_{\lambda}^{(n+1)}$ . The highest weight vector v in  $L_{\lambda}^{(n+1)}$  tensored with any element w of  $\pi_{\lambda}^{(n+1)}$  sits in  $V^{\otimes N} \subset (V \oplus \mathbb{C})^{\otimes N}$ , since the n+1-th component of its weight is zero. Hence  $v \otimes w$  generates a copy of  $L_{\lambda}^{(n)} \otimes \pi_{\lambda}^{(n)}$  as a  $GL_n(\mathbb{C}) \times S_N$ -module. This implies that  $\pi_{\lambda}^{(n+1)} \cong \pi_{\lambda}^{(n)}$ .

**Exercise 27.8.** Let  $R = \mathbb{C}[x_1, ..., x_N, y_1, ..., y_N]^{S_N}$  (the algebra of invariant polynomials). Show that R is generated by the elements  $Q_{rs} := \sum_{i=1}^{N} x_i^r y_i^s$  where  $1 \le r + s \le N$ .

**Exercise 27.9.** Let  $\lambda = (\lambda_1, ..., \lambda_n)$  be a partition. Let us fill the Young diagram of  $\lambda$  with numbers, placing c(i, j) := i - j in the j-th box in the i-th row. Thus the number written in each box depends only of its position (i, j); it is called the **content** of this box. The **content** of  $\lambda$  is the sum  $c(\lambda)$  of contents of all its boxes:

$$c(\lambda) = \sum_{(i,j)\in\lambda} c(i,j).$$

(i) Show that

$$c(\lambda) = \sum_{i=1}^{n} \frac{\lambda_i(\lambda_i - 2i + 1)}{2}.$$

(ii) Let  $\mathbf{c} = \sum_{1 \leq i < j \leq N} (ij) \in \mathbb{C}S_N$  be the **Jucys-Murphy element** (the sum of all transpositions). Show that  $\mathbf{c}$  is a central element of  $\mathbb{C}S_N$  which acts on the irreducible representation  $\pi_{\lambda}$  of  $S_N$  by the scalar  $c(\lambda)$ . (**Hint:** Consider the action of  $\mathbf{c}$  on  $V^{\otimes N}$  and use Schur-Weyl duality to relate it to the diagonal action of the quadratic Casimir of  $\mathfrak{gl}_n$ ).

# 28. Representations of $GL_n$ , II

### 28.1. Schur functors.

**Definition 28.1.** For a partition  $\lambda$  of N we define the **Schur functor**  $S^{\lambda}$  on the category of complex vector spaces (or complex representations of any group or Lie algebra) by  $S^{\lambda}V = \operatorname{Hom}_{S_N}(\pi_{\lambda}, V^{\otimes n})$ .

Thus we have

$$V^{\otimes N} = \bigoplus_{\lambda} S^{\lambda} V \otimes \pi_{\lambda},$$

and if  $\lambda$  has  $\leq n$  parts and  $V = \mathbb{C}^n$  then  $S^{\lambda}V = L_{\lambda}$  as a representation of  $GL(V) = GL_n(\mathbb{C})$ .

**Example 28.2.** 1. We have  $S^{(n)}V = S^nV$ ,  $S^{(1^n)}V = \wedge^nV$ .

2. We have

$$V \otimes V = S^{(2)}V \otimes \mathbb{C}_+ \oplus S^{(1,1)}V \otimes \mathbb{C}_- = S^2V \oplus \wedge^2V$$

where  $S_2$  acts in the first summand trivially and in the second one by sign.

Consider now the decomposition of  $V \otimes V \otimes V$ . We have

$$V \otimes V \otimes V = S^{(3)}V \otimes \mathbb{C}_{+} \oplus S^{(2,1)}V \otimes \mathbb{C}^{2} \oplus S^{(1,1,1)}V \otimes \mathbb{C}_{-}$$
$$= S^{3}V \oplus S^{(2,1)}V \otimes \mathbb{C}^{2} \oplus \wedge^{3}V.$$

Thus

$$S^2V \otimes V = S^3V \oplus S^{(2,1)}V, \ \wedge^2V \otimes V = \wedge^3V \oplus S^{(2,1)}V.$$

We conclude that  $S^{(2,1)}V$  can be described as the space of tensors symmetric in the first two components whose full symmetrization is zero, or tensors antisymmetric on the first two components whose full antisymmetrization is zero.

**Exercise 28.3.** 1. Let  $V = \mathbb{C}^n$ ,  $n \geq 4$ . Decompose  $V^{\otimes 4}$  as a direct sum of irreducible representations of  $GL_n(\mathbb{C}) \times S_4$ . Characterize the occurring Schur functors as spaces of tensors with certain symmetry properties, similarly to the above description of  $S^{(2,1)}V$ . Compute the decompositions of  $V \otimes S^3V$ ,  $V \otimes \wedge^3V$ ,  $S^2V \otimes S^2V$ ,  $S^2V \otimes \wedge^2V$  and  $\wedge^2V \otimes \wedge^2V$  into Schur functors.

2. Decompose  $V \otimes V^*$ ,  $V \otimes V \otimes V^*$  into a direct sum of irreducible representations. Describe the algebra  $\operatorname{End}_{GL_n(\mathbb{C})}(V \otimes V^* \otimes V^*)$ .

Let us compute the dimension of  $S^{\lambda}V$  when dim V=N and  $\lambda$  has k parts. We have  $\rho=(N-1,N-2,...,1,0)$  (for  $SL_N$ ), so the Weyl dimension formula tells us that

$$\dim S^{\lambda}V = \prod_{1 \le i < j \le N} \frac{\lambda_i - \lambda_j + j - i}{j - i} =$$

$$\prod_{1 \leq i < j \leq k} \frac{\lambda_i - \lambda_j + j - i}{j - i} \prod_{1 \leq i \leq k < j \leq N} \frac{\lambda_i + j - i}{j - i} =$$

$$\prod_{1 \leq i < j \leq k} \frac{\lambda_i - \lambda_j + j - i}{j - i} \prod_{i=1}^k \frac{(N+1-i)...(N+\lambda_i - i)}{(k+1-i)...(k+\lambda_i - i)}.$$

We obtain

**Proposition 28.4.** dim  $S^{\lambda}V = P_{\lambda}(N)$  where  $P_{\lambda}$  is a polynomial of degree  $|\lambda|$  with rational coefficients and integer roots. Moreover, the roots of  $P_{\lambda}$  are all the integers in the interval  $[1 - \lambda_1, k - 1]$  (occurring with multiplicities).

Moreover, we see that  $P_{\lambda}(N)$  is an integer-valued polynomial, i.e., it takes integer values at integer points (this is equivalent to being an integer linear combination of  $\binom{N}{i}$ ).

### Example 28.5.

$$P_{(n)}(N) = \dim S^n V = \binom{N+n-1}{n}, \ P_{(1^n)}(N) = \dim \wedge^n V = \binom{N}{n}.$$

Also

$$P_{(a,b)}(N) = (a-b+1)\frac{N...(N+a-1)\cdot(N-1)...(N+b-2)}{(a+1)!b!} = \frac{a-b+1}{a+1}\binom{N+a-1}{a}\binom{N+b-2}{b}$$

E.g.,  $P_{(2,1)}(N) = \dim S^{(2,1)}V = \frac{N(N+1)(N-1)}{3}$ . Also,

$$P_{(a,a)}(N) = \frac{1}{a+1} \binom{N+a-1}{a} \binom{N+a-2}{a} =$$

$$\frac{1}{N+a-1} \binom{N+a-1}{N-1} \binom{N+a-2}{N-2} = \text{Nar}(N+a-1, N-1),$$

the Narayana numbers.

**Exercise 28.6.** Let  $g_q$  be the diagonal matrix with diagonal elements  $1, q, q^2, ..., q^{N-1}$ . Compute the trace of  $g_q$  in  $S^{\lambda}V$  in the product form. Write the answer explicitly (as a polynomial in q) with positive coefficients in the case  $|\lambda| \leq 3$ .

**Exercise 28.7.** Draw the weights of the representation  $S^{(2,2)}\mathbb{C}^3$  of SL(3) on the hexagonal lattice, and indicate their multiplicities.

28.2. The fundamental theorem of invariant theory. Suppose we have a finite dimensional vector space V and a collection of tensors  $T_i \in V^{\otimes m_i} \otimes V^{*\otimes n_i}$ , i = 1, ..., k. An important problem is to describe "coordinate free" invariants of such a collection of tensors, i.e., polynomials functions  $F(T_1, ..., T_k)$  which are invariant under the action of GL(V). How can we classify such functions? This sounds formidably hard in such generality, but turns out to be very easy using Schur-Weyl duality.

It suffices to study such functions that have homogeneity degree  $d_i$  with respect to each  $T_i$ . To do so, we will depict each  $T_i$  by a vertex with  $m_i$  incoming and  $n_i$  outgoing arrows. We should think of incoming arrows as V-components and outgoing ones as V\*-components. Let us draw  $d_i$  such vertices for each i. To construct an invariant, let us connect the arrows preserving orientation so that all the arrows are used (this will only be possible if the number of incoming arrows equals the number of outgoing ones; otherwise every invariant of the multidegree  $(d_1, ..., d_k)$  will be zero). To the obtained graph  $\Gamma$  we can assign the **convolution** of tensors, which gives an invariant function  $F_{\Gamma}$  of the correct multidegree.

**Theorem 28.8.** The functions  $F_{\Gamma}$  for various  $\Gamma$  span the space of invariant functions.

Proof. An invariant function may be viewed as an invariant element of the space  $\bigotimes_{i=1}^k (V^{*\otimes m_i} \otimes V^{\otimes n_i})^{\otimes d_i}$ , which we may write as the space of linear maps  $V^{\otimes M} \to V^{\otimes N}$ , where  $M = \sum d_i m_i$  is the number of incoming arrows and  $N = \sum d_i n_i$  the number of outgoing arrows. If  $M \neq N$ , there are no nonzero invariant maps. Otherwise, by the Schur-Weyl duality, the space of such maps is spanned by maps defined by permutations. But any such permutation defines a graph  $\Gamma$ , so the corresponding invariant is just the convolution  $F_{\Gamma}$ , which implies the statement.

Remark 28.9. Note that this proof also implies that if dim V is large compared to  $m_i, n_i, d_i$  then the functions  $F_{\Gamma}$  for non-isomorphic graphs  $\Gamma$  are linearly independent, so they form a basis in the algebra of A of invariant functions. (Here the vertices of  $\Gamma$  are colored by k colors corresponding to the types of tensors, and at every vertex of color i the incoming edges are labeled by  $[1, n_i]$  and outgoing edges by  $[1, m_i]$ . Isomorphisms are required to preserve these colorings and labelings).

**Example 28.10.** Assume that  $m_i = n_i = 1$ , i.e.,  $T_1, ..., T_k$  are just matrices with  $GL_n$  acting by conjugation. Then all graphs that we can get are unions of cycles, so Theorem 28.8 implies that the algebra  $A_{k,n}$ 

of such invariants (where  $n = \dim V$ ) is generated by traces of cyclic words

$$F_{j_1,\dots,j_r} = \operatorname{Tr}(T_{j_1}\dots T_{j_r})$$

(here "cyclic" means that words differing by a cyclic permutation are considered to be the same). Moreover, by Remark 28.9, these elements are "asymptotically algebraically independent", i.e. there is no nonzero polynomial of them that vanishes for all sizes of matrices n.

This implies that there are no universal polynomial identities for matrices of all sizes. Indeed, if  $P(T_1,...,T_k)=0$  for square matrices  $T_1,...,T_k$  of any size n (where P is a fixed nonzero noncommutative polynomial) then adding another matrix  $T_{k+1}$ , we get  $\text{Tr}(P(T_1,...,T_k)T_{k+1})=0$ , which contradicts linear independence of  $F_{j_1,...,j_r}$ .

In particular, this implies that the universal Lie polynomials  $\mu_n(x, y)$  of degree n occurring in the Baker-Campbell-Hausdorff formula, i.e., such that

$$\log(\exp(x)\exp(y)) \sim \sum_{m>1} \frac{\mu_m(x,y)}{n!}$$

for  $x \in \text{Lie}(G)$  for any Lie group G, are unique (in fact, they are already unique for the family of groups  $GL_n(\mathbb{C})$  for all n).

This is false, however, if the size of matrices is fixed; in this case there are plenty of polynomial identities for each matrix size. For example, for matrices of size 1 we have [X,Y]=0 and for matrices of size 2 we have  $[Z,[X,Y]^2]=0$ . For general n there is the Amitsur-Levitzki identity given in Exercise 28.11.

**Exercise 28.11.** Let  $X_1, ..., X_{2n}$  be complex n by n matrices. Let  $\Lambda = \wedge(\xi_1, ..., \xi_{2n})$  be the exterior algebra generated by  $\xi_i$  with relations  $\xi_i \xi_j = -\xi_j \xi_i, \xi_i^2 = 0$ . Let X be the matrix over  $\Lambda$  given by

$$X := X_1 \xi_1 + \dots + X_{2n} \xi_{2n}.$$

- (i) Let  $Y = X^2$ . Show that  $Y \in \operatorname{Mat}_n(\Lambda_+)$  where  $\Lambda_+$  is the commutative subalgebra of  $\Lambda$  spanned by the elements of even degrees. Compute  $Y^n$ .
  - (ii) Show that  $Tr(Y^k) = 0 \in \Lambda_+$  for k = 1, ..., n.
- (iii) Deduce that  $Y^n = 0$ . This should yield the **Amitsur-Levitzki** identity

$$\sum_{\sigma \in S_{2n}} \operatorname{sign}(\sigma) X_{\sigma(1)} ... X_{\sigma(2n)} = 0.$$

(iv) Deduce the same identity over any commutative ring R.

# 29. Representations of $GL_n$ , III

29.1. Schur polynomials and characters of representations of the symmetric group. Using Schur-Weyl duality and the character formula for representations of  $GL_n$ , we can obtain information about characters of the symmetric group. Namely, it follows from the Weyl character formula that the characters of representations of  $GL_n$  are given by the formula

$$s_{\lambda}(x_1, ..., x_n) = \frac{\sum_{\sigma \in S_n} \operatorname{sign}(\sigma) x_{\sigma(1)}^{\lambda_1 + N - 1} ... x_{\sigma(n)}^{\lambda_n}}{\prod_{i < j} (x_i - x_j)} = \frac{\det(x_i^{\lambda_j + N - j})}{\prod_{i < j} (x_i - x_j)}.$$

These symmetric polynomials are called **Schur polynomials**. For example, the character of  $S^mV$  is

$$s_{(m)}(x_1,...,x_n) = \sum_{1 \le j_1 \le ... \le j_m \le n} x_{j_1}...x_{j_m} = h_m(x_1,...,x_n),$$

the *m*-th **complete symmetric function**, and the character of  $\wedge^m V$  is

$$s_{(1^m)}(x_1, ..., x_n) = \sum_{1 \le j_1 < ... < j_m \le n} x_{j_1} ... x_{j_m} = e_m(x_1, ..., x_m),$$

the *m*-th elementary symmetric function.

Let us now compute the trace in  $V^{\otimes N}$  of  $x\otimes \sigma$ , where  $x=\operatorname{diag}(x_1,...,x_n)$  is a diagonal matrix and  $\sigma\in S_N$  a permutation. Let  $\sigma$  have  $m_i$  cycles of length i. Then we have

$$\operatorname{Tr}|_{V\otimes N}(x\otimes\sigma)=\prod_{i}(x_1^i+\ldots+x_n^i)^{m_i}.$$

On the other hand, using Schur-Weyl duality, we get

$$\operatorname{Tr}|_{V^{\otimes N}}(x\otimes\sigma)=\sum_{\lambda}\chi_{\lambda}(\sigma)s_{\lambda}(x),$$

where  $\chi_{\lambda}(\sigma) = \text{Tr}|_{\pi_{\lambda}}(\sigma)$  is the character of the representation  $\pi_{\lambda}$  of  $S_N$ . Thus we have

$$\sum_{\lambda} \chi_{\lambda}(\sigma) s_{\lambda}(x) = \prod_{i} (x_1^i + \dots + x_n^i)^{m_i}.$$

Multiplying this by the discriminant, we get

$$\sum_{\lambda} \chi_{\lambda}(\sigma) \det(x_i^{\lambda_j + N - j}) = \prod_{i < j} (x_i - x_j) \cdot \prod_i (x_1^i + \dots + x_n^i)^{m_i}.$$

Thus we get

**Theorem 29.1.** (Frobenius character formula) The character value  $\chi_{\lambda}(\sigma)$  is the coefficient of  $x_1^{\lambda_1+N-1}...x_N^{\lambda_N}$  in the polynomial

$$\prod_{i < j} (x_i - x_j) \cdot \prod_i (x_1^i + ... + x_n^i)^{m_i}.$$

**Exercise 29.2.** Let  $V = \mathbb{C}^2$  be the 2-dimensional tautological representation of  $GL_2(\mathbb{C})$ . Decompose  $V^{\otimes N}$  into a direct sum of irreducible representations of  $GL_2(\mathbb{C}) \times S_N$  and compute the characters and dimensions of all the irreducible representations of  $GL_2$  and  $S_N$  that occur.

29.2. **Howe duality.** Howe duality is another instance when we have a double centralizer property. Consider two finite dimensional complex vector spaces V, W, and consider the symmetric power  $S^n(V \otimes W)$  as a representation of  $GL(V) \times GL(W)$ .

**Theorem 29.3.** (Howe duality) We have a decomposition

$$S^n(V \otimes W) = \bigoplus_{\lambda: |\lambda| = n} S^{\lambda} V \otimes S^{\lambda} W.$$

Note that if  $\lambda$  has more parts than dim V or dim W then the corresponding summand is zero.

*Proof.* We have

$$S^{n}(V \otimes W) = ((V \otimes W)^{\otimes n})^{S_{n}} = (V^{\otimes n} \otimes W^{\otimes n})^{S_{n}}$$

So using the Schur-Weyl duality, we get

$$S^{n}(V \otimes W) = ((\bigoplus_{\lambda:|\lambda|=n} S^{\lambda}V \otimes \pi_{\lambda}) \otimes (\bigoplus_{\mu:|\mu|=n} S^{\mu}W \otimes \pi_{\mu}))^{S_{n}} = \bigoplus_{\lambda,\mu:|\lambda|=|\mu|=n} S^{\lambda}V \otimes S^{\mu}W \otimes (\pi_{\lambda} \otimes \pi_{\mu})^{S_{n}}.$$

But the character of  $\pi_{\lambda}$  is integer-valued, so  $\pi_{\lambda} = \pi_{\lambda}^{*}$ . Thus by Schur's lemma  $(\pi_{\lambda} \otimes \pi_{\mu})^{S_{n}} = \mathbb{C}^{\delta_{\lambda\mu}}$ , and we get

$$S^n(V \otimes W) = \bigoplus_{\lambda:|\lambda|=n} S^{\lambda}V \otimes S^{\lambda}W,$$

as claimed.  $\Box$ 

Note that we never used that V, W were finite dimensional, so the statement is valid for any complex vector spaces V, W.

Corollary 29.4. (Cauchy identity) If  $x = (x_1, ..., x_r)$  and  $y = (y_1, ..., y_s)$  then one has

$$\sum_{\lambda} s_{\lambda}(x) s_{\lambda}(y) z^{|\lambda|} = \prod_{i=1}^{r} \prod_{j=1}^{s} \frac{1}{1 - z x_{i} y_{j}}.$$

Proof.

**Lemma 29.5.** (Molien formula). Let  $A: V \to V$  be a linear operator on a finite dimensional vector space V. Denote by  $S^nA$  the induced linear operator  $A^{\otimes n}$  on  $S^nV$ . Then

$$\sum_{n=0}^{\infty} \operatorname{Tr}(S^n A) z^n = \frac{1}{\det(1 - zA)}.$$

*Proof.* Let A have eigenvalues  $x_1, ..., x_r$ . Then the eigenvalues of  $S^n A$  are all possible monomials in  $x_i$  of degree r. Thus  $\text{Tr}(S^n A)$  is the sum of these monomials, which is the complete symmetric function  $h_n(x_1, ..., x_r)$ . So

$$\sum_{n=0}^{\infty} \operatorname{Tr}(S^n A) z^n = \sum_{n \ge 0} h_n(x_1, ..., x_r) z^n = \prod_{i=1}^r \frac{1}{1 - zx_i} = \frac{1}{\det(1 - zA)}.$$

Now let  $X \in GL(V)$  with eigenvalues  $x_1, ..., x_r$  and  $Y \in GL(W)$  with eigenvalues  $y_1, ..., y_s$ . Then by Howe duality

$$\operatorname{Tr}(S^n(X \otimes Y)) = \sum_{\lambda:|\lambda|=n} s_{\lambda}(x)s_{\lambda}(y).$$

On the other hand, by Molien's formula

$$\sum_{n\geq 0} \operatorname{Tr}(S^n(X\otimes Y))z^n = \frac{1}{\det(1-z(X\otimes Y))} = \prod_{i,j} \frac{1}{1-zx_iy_j}.$$

Comparing the two formulas, we obtain the statement.

#### 30. Fundamental and minuscule weights

30.1. Minuscule weights. Let  $\mathfrak{g}$  be a simple complex Lie algebra. Minuscule weights for  $\mathfrak{g}$  are highest weights for which irreducible representations are especially simple.

**Definition 30.1.** A dominant integral weight  $\omega$  for  $\mathfrak{g}$  is called **minuscule** if  $(\omega, \beta) \leq 1$  for all positive coroots  $\beta$ .

Equivalently,  $|(\omega, \beta)| \leq 1$  for any coroot  $\beta$ .

Obviously,  $\omega = 0$  is minuscule, but there may exist other minuscule weights. For example, for  $\mathfrak{g} = \mathfrak{sl}_n$ , all fundamental weights are minuscule, since  $(\omega_i, \mathbf{e}_j - \mathbf{e}_k) = 0$  if  $j, k \leq i$  or j, k > i and  $(\omega_i, \mathbf{e}_j - \mathbf{e}_k) = 1$  if  $j \leq i < k$ .

It is easy to see that any minuscule weight  $\omega \neq 0$  is fundamental. Indeed, we can have  $(\omega, \alpha_i^{\vee}) = 1$  only for one i, and for all other simple coroots this inner product must be zero. Otherwise we will have  $(\omega, \theta^{\vee}) \geq 2$ , where  $\theta^{\vee}$  is the maximal coroot (the maximal root of the dual root system  $R^{\vee}$ ).<sup>15</sup>

On the other hand, not all fundamental weights are minuscule. In fact, we will see that the simple Lie algebras of types  $G_2$ ,  $F_4$  and  $E_8$  do not have any nonzero minuscule weights. To formulate a criterion for a fundamental weight to be minuscule, recall that  $\theta^{\vee} = \sum_i m_i \alpha_i^{\vee}$ , where  $m_i = (\omega_i, \theta^{\vee})$  are strictly positive integers.

**Lemma 30.2.** A fundamental weight  $\omega_i$  is minuscule if and only if  $m_i = 1$ .

*Proof.* The definition of minuscule means that  $m_i \leq 1$ . On the other hand, if  $m_i = 1$  then given a positive coroot  $\beta = \sum_j n_j \alpha_j^{\vee}$ , we have  $n_j \leq m_j$ , in particular  $n_i \leq 1$ , so  $\omega_i$  is minuscule.

**Lemma 30.3.** Let  $\omega \in Q$  and  $|(\omega, \beta)| \leq 1$  for all coroots  $\beta$ . Then  $\omega = 0$ .

*Proof.* Assume the contrary. Choose a counterexample  $\omega = \sum_i m_i \alpha_i$  so that  $\sum_i |m_i|$  is minimal possible. We have

$$(\omega, \omega) = \sum_{i} m_i(\omega, \alpha_i) > 0.$$

<sup>&</sup>lt;sup>15</sup>The maximal coroot  $\theta^{\vee}$  should not be confused with the coroot  $\widetilde{\theta}^{\vee}$  corresponding to the maximal root  $\theta$  (highest weight of the adjoint representation) under a W-invariant identification  $\mathfrak{h}^* \cong \mathfrak{h}$ . In the non-simply-laced case they are not even proportional: e.g., for the root system  $B_2$ ,  $\theta^{\vee} = (1,1)$  while  $\widetilde{\theta}^{\vee} = (2,0)$ . This may be confusing since according to the general coroot notation,  $\widetilde{\theta}^{\vee}$  should be denoted by  $\theta^{\vee}$ .

So there exists j such that  $m_j$  and  $(\omega, \alpha_j^{\vee})$  are nonzero and have the same sign. Replacing  $\omega$  with  $-\omega$  if needed, we may assume that both are positive, then  $(\omega, \alpha_j^{\vee}) = 1$ . Then  $s_j \omega = \omega - \alpha_j = \sum_j m_i' \alpha_i$  where  $m_j' = m_j - 1$  and  $m_i' = m_i$  for all  $i \neq j$  is another counterexample. But we have  $\sum_i |m_i'| = \sum_i |m_i| - 1$ , a contradiction.

Why are minuscule weights interesting? It is because of the following result.

**Proposition 30.4.** The following conditions on a dominant integral weight  $\omega$  are equivalent:

- (1)  $\omega$  is minuscule;
- (2) all weights of the representation  $L_{\omega}$  belong to the orbit  $W\omega$ ;
- (3) if  $\lambda$  is a dominant integral weight such that  $\omega \lambda \in Q_+$  then  $\lambda = \omega$ .

Proof. Let us prove that (1) implies (3). If  $\omega = 0$ , there is nothing to prove, since then  $-\lambda \in Q_+$ , so  $(\lambda, \rho) \leq 0$ , hence  $\lambda = 0$ . So suppose that  $\omega = \omega_i$  is minuscule. We have  $\omega_i - \lambda = \sum_k m_k \alpha_k$  with  $m_k \geq 0$ . If  $m_k = 0$  for some  $k \neq i$  then the problem reduces to smaller rank by deleting the vertex k from the Dynkin diagram. So we may assume  $m_k > 0$  for all  $k \neq i$ . Let  $\beta$  be a positive coroot. Then

$$(\omega_i - \lambda, \beta) = (\omega_i, \beta) - (\lambda, \beta) \le (\omega_i, \beta) \le 1$$

and if  $\alpha_i^{\vee}$  does not occur in  $\beta$  then it is  $\leq 0$ . So in particular we have  $(\omega_i - \lambda, \alpha_j^{\vee}) \leq 0$  if  $j \neq i$ . If also  $(\omega_i - \lambda, \alpha_i^{\vee}) \leq 0$  then  $(\omega_i - \lambda, \omega_i - \lambda) \leq 0$ , so  $\omega_i = \lambda$ , as claimed. Thus we may assume that  $(\omega_i - \lambda, \alpha_i^{\vee}) = 1$ , i.e.,  $m_i > 0$ , so  $m_j > 0$  for all j. Thus,  $(\omega_i - \lambda, \theta^{\vee}) \geq 1$  (as  $\theta^{\vee}$  is a dominant coweight). Hence  $(\lambda, \theta^{\vee}) \leq 0$ , i.e.,  $\lambda = 0$ , as  $\theta^{\vee}$  contains all  $\alpha_j^{\vee}$  with positive coefficients. Thus  $\omega_i \in Q$ . But this is impossible by Lemma 30.3.

To see that (3) implies (2), note that if  $\mu$  is any weight of  $L_{\omega}$  then for some  $w \in W$  the weight  $\lambda = w\mu$  is dominant and  $\omega - \lambda \in Q_+$ , so  $\lambda = \omega$  and  $\mu = w^{-1}\omega$ .

Finally, we show that (2) implies (1). Assume (2) holds. If  $\omega$  is not minuscule then there is a positive root  $\alpha$  such that  $(\omega, \alpha^{\vee}) > 1$ , hence  $2(\omega, \alpha) > (\alpha, \alpha)$ . Then  $\omega - \alpha$  is a weight of  $L_{\omega}$  (the weight of the nonzero vector  $f_{\alpha}v_{\omega}$ ), and it is not W-conjugate to  $\omega$ , as

$$(\omega - \alpha, \omega - \alpha) = (\omega, \omega) - 2(\omega, \alpha) + (\alpha, \alpha) < (\omega, \omega).$$

This immediately implies

Corollary 30.5. The character of  $L_{\omega}$  with minuscule  $\omega$  is

$$\chi_{\omega} = \sum_{\gamma \in W_{\omega}} e^{\gamma}.$$

**Proposition 30.6.**  $\omega \in P_+$  is minuscule if and only if the restriction of  $L_{\omega}$  to any root  $\mathfrak{sl}_2$ -subalgebra of  $\mathfrak{g}$  is the direct sum of 1-dimensional and 2-dimensional representations.

*Proof.* Let  $\omega$  be minuscule and  $v \in L_{\omega}$  be a weight vector which is a highest weight vector for  $(\mathfrak{sl}_2)_{\alpha}$ . Then  $h_{\alpha}v = (w\omega, \alpha^{\vee})v = (\omega, w^{-1}\alpha^{\vee})v$  for some  $w \in W$ . Thus  $h_{\alpha}v = 0$  or  $h_{\alpha}v = v$ , as claimed.

On the other hand, if  $\omega$  is not minuscule then there is a positive root  $\alpha$  such that  $(\omega, \alpha^{\vee}) = m > 1$ . So  $h_{\alpha}v_{\omega} = mv_{\omega}$  and  $v_{\omega}$  generates the irreducible m + 1-dimensional representation of  $(\mathfrak{sl}_2)_{\alpha}$ .

# 30.2. Tensor product with a minuscule representation.

Corollary 30.7. If  $\omega$  is minuscule then for any dominant integral weight  $\lambda$  of  $\mathfrak{g}$  we have

$$L_{\omega} \otimes L_{\lambda} = \bigoplus_{\gamma \in W \omega} L_{\lambda + \gamma},$$

where if  $\lambda + \gamma$  is not dominant then we agree that  $L_{\lambda+\gamma} = 0$ .

*Proof.* By the Weyl character formula and Corollary 30.5, the character of  $L_{\omega} \otimes L_{\lambda}$  is

$$\chi_{L_{\omega} \otimes L_{\lambda}} = \frac{\sum_{\mu \in W_{\omega}} \sum_{w \in W} (-1)^{\ell(w)} e^{w(\lambda + \rho) + \mu}}{\prod_{\alpha \in R_{+}} (e^{\alpha/2} - e^{-\alpha/2})} = \frac{\sum_{\gamma \in W_{\omega}} \sum_{w \in W} (-1)^{\ell(w)} e^{w(\lambda + \gamma + \rho)}}{\prod_{\alpha \in R_{+}} (e^{\alpha/2} - e^{-\alpha/2})}.$$

If  $\lambda + \gamma \notin P_+$  then for some i we have  $(\lambda + \gamma, \alpha_i^{\vee}) < 0$ . But  $(\gamma, \alpha_i^{\vee}) \ge -1$ . So  $(\lambda + \gamma, \alpha_i^{\vee}) = -1$  and thus  $(\lambda + \gamma + \rho, \alpha_i^{\vee}) = 0$ . So for such  $\gamma$ , for any  $w \in W$  the summand for w cancels with the summand for  $ws_i$ . Thus we get

$$\chi_{L_{\omega}\otimes L_{\lambda}} = \frac{\sum_{\gamma\in W\omega: \lambda+\gamma\in P_{+}} \sum_{w\in W} (-1)^{\ell(w)} e^{w(\lambda+\gamma+\rho)}}{\prod_{\alpha\in R_{+}} (e^{\alpha/2} - e^{-\alpha/2})} = \sum_{\gamma\in W\omega: \lambda+\gamma\in P_{+}} \chi_{L_{\lambda+\gamma}}.$$

**Example 30.8.** 1. Let V be the vector representation of  $GL_n$ . Then for a partition  $\lambda$ ,  $V \otimes L_{\lambda} = \bigoplus_{\mu \in \lambda + \square} L_{\mu}$ , where  $\mu$  runs over all partitions obtained by adding one **addable** box to the Young diagram of  $\lambda$ , i.e., such that it remains a Young diagram. For example,

$$V\otimes S^{(3,3,2,1)}V=S^{(4,3,2,1)}V\oplus S^{(3,3,3,1)}V\oplus S^{(3,3,2,2)}V\oplus S^{(3,3,2,1,1)}V.$$

2. More generally,  $\wedge^m V \otimes L_{\lambda} = \bigoplus_{\mu \in \lambda + m \square} L_{\mu}$ , where we sum over partitions obtained by adding m addable boxes to different rows of the Young diagram of  $\lambda$  (going from top to bottom), i.e. a collection of m boxes in different rows after adding which we still have a Young diagram. This follows immediately from Corollary 30.7. For example,

$$\wedge^2 V \otimes S^{(3,1)}V = S^{(4,2)}V \oplus S^{(4,1,1)}V \oplus S^{(3,2,1)}V \oplus S^{(3,1,1,1)}V.$$

**Proposition 30.9.** (i) Let  $\lambda$  be a partition of N. Then we have

$$\mathbb{C}S_{N+1}\otimes_{\mathbb{C}S_N}\pi_\lambda=\bigoplus_{\mu\in\lambda+\square}\pi_\mu.$$

(ii) Let  $\mu$  be a partition of N+1. Then we have

$$\pi_{\mu}|_{S_N} = \bigoplus_{\lambda \in \mu - \square} \pi_{\mu}.$$

Here in (ii) we sum over all ways to delete a **removable box** from the Young diagram of  $\mu$ , i.e., such that the remaining collection of boxes is still a Young diagram.

*Proof.* (i) Let V be a vector space of sufficiently large dimension. Using Frobenius reciprocity and Schur-Weyl duality, we have

$$\operatorname{Hom}_{S_{N+1}}(\mathbb{C}S_{N+1} \otimes_{\mathbb{C}S_N} \pi_{\lambda}, V^{\otimes N+1}) = \operatorname{Hom}_{S_N}(\pi_{\lambda}, V \otimes V^{\otimes N}) = V \otimes S^{\lambda}V.$$

On the other hand, again by the Schur-Weyl duality,

$$\operatorname{Hom}_{S_{N+1}}(\bigoplus_{\mu\in\lambda+\square}\pi_{\mu},V^{\otimes N+1})=\bigoplus_{\mu\in\lambda+\square}S^{\mu}V.$$

So the statement follows from Example 30.8(1).

Let  $\lambda^{\dagger}$  be the **conjugate partition** to  $\lambda$ , which consists of the boxes (j,i) where  $(i,j) \in \lambda$ . In other words, the Young diagram of  $\lambda^{\dagger}$  is obtained by transposing the Young diagram of  $\lambda$ . For example,  $(3,3,2,1)^{\dagger}=(4,3,2)$ .

Corollary 30.10. Let  $\mathbb{C}_-$  be the sign representation of  $S_N$ . Then

$$\pi_{\lambda} \otimes \mathbb{C}_{-} \cong \pi_{\lambda^{\dagger}}$$
.

*Proof.* We argue by induction in  $N = |\lambda|$ , with obvious base N = 1. Suppose the statement is known for N and let us prove it for N + 1. Given a partition  $\nu$  of N + 1, let  $\lambda$  be obtained from  $\nu$  by deleting a removable box (i, j). Note that we have a natural isomorphism

$$\xi: (\mathbb{C}S_{N+1} \otimes_{\mathbb{C}S_N} \pi_{\lambda}) \otimes \mathbb{C}_- \to \mathbb{C}S_{N+1} \otimes_{\mathbb{C}S_N} (\pi_{\lambda} \otimes \mathbb{C}_-) = \mathbb{C}S_{N+1} \otimes_{\mathbb{C}S_N} \pi_{\lambda^{\dagger}}.$$

This can be written as an isomorphism

$$\bigoplus_{\mu \in \lambda + \square} \pi_{\mu} \otimes \mathbb{C}_{-} \cong \bigoplus_{\eta \in \lambda^{\dagger} + \square} \pi_{\eta}.$$

Suppose  $\pi_{\nu} \otimes \mathbb{C}_{-} = \pi_{\overline{\nu}}$ . Then  $\overline{\nu} \in \lambda^{\dagger} + \square$ . But by Exercise 27.9,  $\pi_{\nu}$  is the eigenspace of the Jucys-Murphy element  $\mathbf{c} \in \mathbb{C}S_{N+1}$  in  $\mathbb{C}S_{N+1} \otimes_{\mathbb{C}S_{N}} \pi_{\lambda}$  with eigenvalue  $c(\nu)$  (as  $c(\mu)$  are all distinct for  $\mu \in \lambda + \square$ ). Hence the eigenvalue of  $\mathbf{c}$  on  $\pi_{\overline{\nu}}$  is  $-c(\nu)$ . This implies that  $\overline{\nu} = \nu^{\dagger}$ , which justifies the induction step.

**Proposition 30.11.** (Skew Howe duality) Let V, W be complex vector spaces. Show that

$$\wedge^n(V \otimes W) \cong \bigoplus_{\lambda: |\lambda| = n} S^{\lambda}V \otimes S^{\lambda^{\dagger}}W$$

as  $GL(V) \times GL(W)$ -modules.

Exercise 30.12. Prove Proposition 30.11.

**Hint:** Repeat the proof of the usual Howe duality (Subsection 29.2), using Corollary 30.10.

**Exercise 30.13.** Compute characters and dimensions of irreducible representations  $L_{a+b,b,0}$  of  $SL_3(\mathbb{C})$ , where  $a,b \geq 0$ . Compute the weight multiplicities and draw the weights on the hexagonal lattice for  $a+b \leq 3$ , indicating the multiplicities. What are the special features of the case b=0?

**Hint.** The best way to do this exercise is to compute the characters recursively, using that  $V \otimes L_{a+b,b,0} = L_{a+b+1,b,0} \oplus L_{a+b,b+1,0} \oplus L_{a+b-1,b-1,0}$  (if a=0, the second summand drops out and if b=0 then the third one drops out), by the "addable boxes" rule. This allows one to express the characters for b+1 in terms of the characters for b and b-1. And we know the characters of  $L_{a,0,0}$  - they are the complete symmetric functions  $h_a$ .

**Exercise 30.14.** Compute the decomposition of  $\wedge^m V \otimes S^k V$ ,  $\wedge^m V \otimes \wedge^k V$ ,  $S^2(\wedge^m V)$ ,  $\wedge^2(\wedge^m V)$  into irreducible representations of GL(V).

**Exercise 30.15.** Let  $\mathfrak{g}$  be a finite dimensional simple complex Lie algebra, and V a finite dimensional representation of  $\mathfrak{g}$ . Given a homomorphism  $\Phi: L_{\lambda} \to V \otimes L_{\mu}$ , let  $\langle \Phi \rangle := (\mathrm{Id} \otimes v_{\mu}^*, \Phi v_{\lambda}) \in V$ , where  $v_{\lambda}$  is a highest weight vector of  $L_{\lambda}$  and  $v_{\mu}^*$  the lowest weight vector of  $L_{\mu}^*$ . In other words, we have

$$\Phi v_{\lambda} = \langle \Phi \rangle \otimes v_{\mu} + \text{lower terms}$$

where the lower terms have lower weight than  $\mu$  in the second component.

- (i) Show that  $\langle \Phi \rangle$  has weight  $\lambda \mu$ .
- (ii) Show that  $f_i^{(\lambda,\alpha_i^\vee)+1}\langle\Phi\rangle=0$  for all i.
- (iii) Let  $V[\nu]_{\lambda}$  be the subspace of vectors  $v \in V[\nu]$  of weight  $\nu$  which satisfy the equalities  $f_i^{(\lambda,\alpha_i^\vee)+1}v=0$  for all i. Show that the map  $\Phi \mapsto \langle \Phi \rangle$  defines an isomorphism of vector spaces  $\operatorname{Hom}_{\mathfrak{g}}(L_{\lambda},V\otimes L_{\mu})\cong V[\lambda-\mu]_{\lambda}$ .

Hint. Let  $M_{\lambda}$  be the Verma module with highest weight  $\lambda$ , and  $\overline{M}_{-\mu}$  be the lowest weight Verma module with lowest weight  $-\mu$ , i.e., generated by a vector  $v_{-\mu}$  with defining relations  $hv_{-\mu} = -\mu(h)v_{-\mu}$  for  $h \in \mathfrak{h}$  and  $f_iv_{-\mu} = 0$ . Show first that the map  $\Phi \mapsto \langle \Phi \rangle$  defines an isomorphism  $\operatorname{Hom}_{\mathfrak{g}}(M_{\lambda}, V \otimes \overline{M}_{-\mu}^*) \cong V[\lambda - \mu]$ . Next, show that  $\Phi \in \operatorname{Hom}_{\mathfrak{g}}(M_{\lambda}, V \otimes \overline{M}_{-\mu}^*)$  factors through  $L_{\lambda}$  iff  $\langle \Phi \rangle \in V[\lambda - \mu]_{\lambda}$ , i.e.,  $f_i^{(\lambda, \alpha_i^{\vee}) + 1} \langle \Phi \rangle = 0$  (for this, use that  $e_j f_i^{(\lambda, \alpha_i^{\vee}) + 1} v_{\lambda} = 0$ , and that the kernel of  $M_{\lambda} \to L_{\lambda}$  is generated by the vectors  $f_i^{(\lambda, \alpha_i^{\vee}) + 1} v_{\lambda}$ ). This implies that the above map defines an isomorphism  $\operatorname{Hom}_{\mathfrak{g}}(L_{\lambda}, V \otimes \overline{M}_{-\mu}^*) \cong V[\lambda - \mu]_{\lambda}$ . Finally, show that every homomorphism  $L_{\lambda} \to V \otimes \overline{M}_{-\mu}^*$  in fact lands in  $V \otimes L_{\mu} \subset V \otimes \overline{M}_{-\mu}^*$ .

- (iv) Let V be the vector representation of  $SL_n(\mathbb{C})$ . Determine the weight subspaces of  $S^mV$ , and compute the decomposition of  $S^mV \otimes L_{\mu}$  into irreducibles for all  $\mu$  (use (iii)).
- (v) For any  $\mathfrak{g}$ , compute the decomposition of  $\mathfrak{g} \otimes L_{\mu}$ , where  $\mathfrak{g}$  is the adjoint representation of  $\mathfrak{g}$  (again use (iii)).

In both (iv) and (v) you should express the answer in terms of the numbers  $k_i$  such that  $\mu = \sum_i k_i \omega_i$  and the Cartan matrix entries.

**Proposition 30.16.** Every coset in P/Q contains a unique minuscule weight. This gives a bijection between P/Q and minuscule weights. So the number of minuscule weights equals  $\det A$ , where A is the Cartan matrix.

Proof. Let  $C := a + Q \in P/Q$  be a coset, and consider the intersection  $C \cap P_+$ . Let  $\omega \in C \cap P_+$  be an element with smallest  $(\omega, \rho^{\vee})$ . If  $\lambda$  is a dominant weight of  $L_{\omega}$  then  $\lambda \in C \cap P_+$ , so  $(\lambda, \rho^{\vee}) \geq (\omega, \rho^{\vee})$ , hence  $(\omega - \lambda, \rho^{\vee}) \leq 0$ . But  $\omega - \lambda \in Q_+$ , so  $\lambda = \omega$ . Thus  $\omega$  is minuscule. On the other hand, if  $\omega_1, \omega_2 \in C$  are minuscule and distinct then  $\omega_1 - \omega_2 \in Q$ , so by Lemma 30.3, there is a coroot  $\beta$  such that  $(\omega_1 - \omega_2, \beta) \geq 2$ . So  $(\omega_1, \beta) = 1$  and  $(\omega_2, \beta) = -1$ . The first identity implies  $\beta > 0$  and the second one  $\beta < 0$ , a contradiction.

30.3. Fundamental weights of classical Lie algebras. Let us now determine the fundamental weights of classical Lie algebras of types  $B_n, C_n, D_n$ .

**Type**  $C_n$ . Then  $\mathfrak{g} = \mathfrak{sp}_{2n}$ . The positive roots are  $\mathbf{e}_i \pm \mathbf{e}_j$ ,  $2\mathbf{e}_i$ , the simple roots  $\alpha_1 = \mathbf{e}_1 - \mathbf{e}_2, ..., \alpha_n = 2\mathbf{e}_n$ , so  $\alpha_i^{\vee} = \alpha_i$  for  $i \neq n$  and  $\alpha_n^{\vee} = \mathbf{e}_n$ . So  $\omega_i = (1, ..., 1, 0, ..., 0)$  (*i* ones) for  $1 \leq i \leq n$ .

**Type**  $B_n$ . Then  $\mathfrak{g} = \mathfrak{so}_{2n+1}$ , so we have the same story as for  $C_n$  except  $\alpha_n = \mathbf{e}_n$  and  $\alpha_n^{\vee} = 2\mathbf{e}_n$ , so we have the same  $\omega_i$  for i < n but  $\omega_n = (\frac{1}{2}, ..., \frac{1}{2})$ .

**Type**  $D_n$ . Then  $\mathfrak{g} = \mathfrak{so}_{2n}$ , so the positive roots are  $\mathbf{e}_i \pm \mathbf{e}_j$ , the simple roots  $\alpha_1 = \mathbf{e}_1 - \mathbf{e}_2, ..., \alpha_{n-2} = \mathbf{e}_{n-2} - \mathbf{e}_{n-1}, \ \alpha_{n-1} = \mathbf{e}_{n-1} - \mathbf{e}_n, \ \alpha_n = \mathbf{e}_{n-1} + \mathbf{e}_n$ . So  $\omega_i = (1, ..., 1, 0, ..., 0)$  (*i* ones) for i = 1, ..., n-2, but  $\omega_{n-1} = (\frac{1}{2}, ..., \frac{1}{2}, \frac{1}{2}), \ \omega_n = (\frac{1}{2}, ..., \frac{1}{2}, -\frac{1}{2})$ .

30.4. Minuscule weights outside type A. Proposition 30.16 immediately tells us how many minuscule weights we have. For type A we saw that all fundamental weights are minuscule. For  $G_2, F_4, E_8$ ,  $\det A = 1$ , so the only minuscule weight is 0. For type  $B_n$  we have  $\det A = 2$ , so we should have one nonzero minuscule weight, and this is the weight  $(\frac{1}{2}, ..., \frac{1}{2})$ . The corresponding representation has weights  $(\pm \frac{1}{2}, ..., \pm \frac{1}{2})$ , so it has dimension  $2^n$ . It is called the **spin representation**, denoted S.

For  $C_n$  we also have  $\det A = 2$ , so we again have a unique nonzero minuscule weight. Namely, it is the weight (1,0,...,0) (so the minuscule representation is the tautological representation of  $\mathfrak{sp}_{2n}$ , of dimension 2n). For  $D_n$  we have  $\det A = 4$ , so we have three nontrivial minuscule representations, with highest weights  $\omega_1, \omega_{n-1}, \omega_n$ , of dimensions  $2n, 2^{n-1}, 2^{n-1}$ . The first one is the tautological representation and the remaining two are the **spin representations**  $S_+, S_-$ , whose weights are  $(\pm \frac{1}{2}, ..., \pm \frac{1}{2})$  with even, respectively odd number of minuses.

For  $E_6$  there are two nontrivial minuscule representations  $V, V^*$  of dimension 27. For  $E_7$  there is just one of dimension 56. These dimensions are computed easily by counting elements in the corresponding Weyl group orbits.

#### 31. Fundamental representations of classical Lie algebras

31.1. **Type**  $C_n$ . Since the fundamental weights for  $\mathfrak{g} = \mathfrak{sp}_{2n}$  are  $\omega_i = (1, ..., 1, 0, ..., 0)$  (i ones), same as for  $\mathfrak{gl}_n$ , one may think that the fundamental representations are also "the same", i.e.  $\wedge^i V$ , where V is the 2n-dimensional vector representation. Indeed, a Cartan subalgebra in  $\mathfrak{g}$  is the space of matrices  $\operatorname{diag}(a_1, ..., a_n, -a_1, ..., -a_n)$ , so  $L_{\omega_1} = V$ , with highest weight vector  $e_1$ . However, the representation  $\wedge^2 V$  is not irreducible, even though it has the correct highest weight  $\omega_2$ . Indeed, we have  $\wedge^2 V = \wedge_0^2 V \oplus \mathbb{C}$ , where  $\mathbb{C}$  is the trivial representation spanned by the inverse  $B^{-1} = \sum_i e_{i+n} \wedge e_i$  of the invariant nondegenerate skew-symmetric form  $B = \sum_i e_i^* \wedge e_{i+n}^* \in \wedge^2 V^*$  preserved by  $\mathfrak{g}$ , and  $\wedge_0^2 V$  is the orthogonal complement of B.

It turns out that  $\wedge_0^2 V$  is irreducible. (You can show it directly or using the Weyl dimension formula). Thus we have  $L_{\omega_2} = \wedge_0^2 V$  (if  $n \geq 2$ ).

So what happens for  $L_{\omega_j}$  with any  $j \geq 2$ ? To determine this, note that we have a homomorphism of representations  $\iota_B : \wedge^{i+1}V \to \wedge^{i-1}V$ , which is just the contraction with B (we agree that  $\wedge^j V = 0$  for j < 0). So we may consider the subrepresentation  $\wedge_0^i V = \operatorname{Ker}(\iota_B|_{\wedge^i V}) \subset \wedge^i V$ .

**Exercise 31.1.** (i) Let  $m_B: \wedge^{i-1}V \to \wedge^{i+1}V$  be the operator defined by  $m_B(u) := B^{-1} \wedge u$ . Show that the operators  $m_B, \iota_B$  generate a representation of the Lie algebra  $\mathfrak{sl}_2$  on  $\wedge V := \bigoplus_{i=0}^{2n} \wedge^i V$  where they are proportional to the operators e, f, such that h acts on  $\wedge^i V$  by multiplication by i - n.

- (ii) Show that  $\iota_B$  is injective when  $i \geq n$  and surjective when  $i \leq n$  (so an isomorphism for i = n).
- (iii) Show that  $\operatorname{Ker}(\iota_B|_{\wedge^j V})$  is irreducible for  $j \leq n$ , and is isomorphic to  $L_{\omega_j}$ , where we agree that  $\omega_0 = 0$ . Deduce that

$$\wedge V = \bigoplus_{i=0}^{n} L_{\omega_i} \otimes L_{n-j}$$

as a representation of  $\mathfrak{sp}_{2n} \oplus \mathfrak{sl}_2$ , where  $L_m$  is the m+1-dimensional irreducible representation of  $\mathfrak{sl}_2$  of highest weight m.

(iv) Show that every irreducible representation of  $\mathfrak{sp}_{2n}$  occurs in  $V^{\otimes N}$  for some N.

Thus we see another instance of the double centralizer property.

31.2. **Type**  $B_n$ . We have  $\mathfrak{g} = \mathfrak{so}_{2n+1}$ , preserving the quadratic form  $Q = \sum_{i=1}^n x_i x_{i+n} + x_{2n+1}^2$ . A Cartan subalgebra consists of matrices diag $(a_1, ..., a_n, -a_1, ..., -a_n, 0)$ . So the representations  $\wedge^i V$ ,  $1 \leq i \leq n$ , where V is the 2n + 1-dimensional vector representation, have highest weight (1, ..., 1, 0, ...0) (i ones), which is  $\omega_i$  if  $i \leq n - 1$ .

**Exercise 31.2.** Show that the representation  $\wedge^i V$  is irreducible for  $0 \le i \le n$ .

Thus for  $1 \leq i \leq n-1$  we have  $\wedge^i V = L_{\omega_i}$ . On the other hand, the representation  $\wedge^n V$ , even though irreducible, is not fundamental. Indeed, its highest weight is  $(1, ..., 1) = 2\omega_n$ , as  $\omega_n = (\frac{1}{2}, ..., \frac{1}{2})$ . In fact, we see that the representation  $L_{\omega_n}$  does not occur in  $V^{\otimes N}$  for any N, since coordinates of its highest weight are not integer. As mentioned above, this representation is called the **spin representation** S. Vectors in S are called **spinors**. The weights of S are Weyl group translates of  $\omega_n$ , so they are  $(\pm \frac{1}{2}, ..., \pm \frac{1}{2})$  for any choices of signs, so dim  $S = 2^n$ , and the character of S is given by the formula

$$\chi_S(x_1,...,x_n) = (x_1^{\frac{1}{2}} + x_1^{-\frac{1}{2}})...(x_n^{\frac{1}{2}} + x_n^{-\frac{1}{2}}).$$

This is supposed to be the trace of  $\operatorname{diag}(x_1, ..., x_n, x_1^{-1}, ..., x_n^{-1}, 1) \in SO_{2n+1}(\mathbb{C})$ , which does not make sense since the square roots on the right hand side are defined only up to sign. This shows that the spin representation S does not lift to the group  $SO_{2n+1}(\mathbb{C})$ . Namely, the group  $SO_{2n+1}(\mathbb{C})$  is not simply connected, and the representation S only lifts to the universal covering group  $\widetilde{SO}_{2n+1}(\mathbb{C})$ , which is called the **spin group**, and is denoted  $\operatorname{Spin}_{2n+1}(\mathbb{C})$ .

**Example 31.3.** Let n = 1. Then  $\mathfrak{g} = \mathfrak{so}_3(\mathbb{C}) = \mathfrak{sl}_2(\mathbb{C})$  and S is the 2-dimensional irreducible representation. We know that this representation does not lift to  $SO_3(\mathbb{C})$  but only to its double cover  $SL_2(\mathbb{C})$ , which is simply connected (so  $\pi_1(SO_3(\mathbb{C})) = \mathbb{Z}/2$ , demonstrated by the famous **belt trick**). So we have  $Spin_3(\mathbb{C}) = SL_2(\mathbb{C})$ . This is related to the spin phenomenon in quantum mechanics which we will discuss later. This explains the terminology.

**Proposition 31.4.** For  $n \geq 3$  we have  $\pi_1(SO_n(\mathbb{C})) = \mathbb{Z}/2$ .

Proof.

**Lemma 31.5.** Let  $X_n$  be the hypersurface in  $\mathbb{C}^n$  given by the equation  $z_1^2 + ... + z_n^2 = 1$ . Then for any  $1 \le k \le n-2$  we have  $\pi_k(X_n) = 0$ , i.e., every continuous map  $S^k \to X_n$  contacts to a point. E.g.,  $X_n$  is connected for  $n \ge 2$ , simply connected for  $n \ge 3$ , doubly connected for  $n \ge 4$ , etc.

*Proof.* The surface  $X_n$  is the complexification of the n-1-sphere,  $X_n^{\mathbb{R}} := X_n \cap \mathbb{R}^n = S^{n-1}$ . We will define a continuous family of maps  $f_t : X_n \to X_n$  such that  $f_1 = \operatorname{Id}$  and  $f_0$  lands in  $X_n^{\mathbb{R}}$ , with  $f_t|_{X_n^{\mathbb{R}}} = \operatorname{Id}$ . This will show that  $X_n^{\mathbb{R}}$  is a retract of  $X_n$ , so  $X_n$  has the required

properties since so does  $X_n^{\mathbb{R}}$  (indeed, any map  $\gamma = f_1 \circ \gamma : S^k \to X_n$  is homotopic to the map  $f_0 \circ \gamma$  in  $X_n^{\mathbb{R}}$ , the homotopy being  $f_t \circ \gamma$ ). Let  $z = x + iy \in X_n$ , where  $x, y \in \mathbb{R}^n$ . Then  $z^2 = 1$ , so we have

 $x^2 - y^2 = 1, xy = 0$ . Hence

$$(x+tiy)^2 = x^2 - t^2y^2 = 1 + (1-t^2)y^2 \ge 1.$$

So we may define

$$f_t(z) := \frac{x + tiy}{\sqrt{x^2 - t^2 y^2}}.$$

Then  $f_t(z)^2 = 1$ ,  $f_1(z) = z$ , and  $f_0(z) = \frac{x}{|x|}$  lands in the sphere  $S^{n-1}$ , as needed.

In particular, for n=4, changing coordinates, we see that the surface ad-bc=1 is doubly connected, i.e.,  $SL_2(\mathbb{C})$  is doubly connected and thus  $\pi_1(SO_3(\mathbb{C})) = \mathbb{Z}/2$  (which we already knew).

Now, the group  $SO_n(\mathbb{C})$  acts on  $X_n$  transitively with stabilizer  $SO_{n-1}(\mathbb{C})$ , so we have a fibration  $SO_n \to X_n$  with fiber  $SO_{n-1}$ . Therefore, we have an exact sequence

$$\pi_2(X_n) \to \pi_1(SO_{n-1}(\mathbb{C})) \to \pi_1(SO_n(\mathbb{C})) \to \pi_1(X_n)$$

(a portion of the long exact sequence of homotopy groups). By Lemma 31.5, the first and the last group in this sequence are trivial for  $n \geq 4$ which implies that in this case  $\pi_1(SO_{n-1}(\mathbb{C})) \cong \pi_1(SO_n(\mathbb{C}))$ , so we conclude by induction that  $\pi_1(SO_n(\mathbb{C})) = \mathbb{Z}/2$  for all  $n \geq 3$  (using the case n=3 as the base).

Corollary 31.6. For  $n \geq 1$  the simply connected group  $\operatorname{Spin}_{2n+1}(\mathbb{C})$  is a double cover of  $SO_{2n+1}(\mathbb{C})$ .

Exercise 31.7. (i) Use a similar argument to show that the groups  $SL_{n+1}(\mathbb{C})$  and  $Sp_{2n}(\mathbb{C})$  are simply connected for  $n \geq 1$  (consider their action on nonzero vectors in the vector representation and compute the stabilizer).

- (ii) Generalize this argument to show that for any  $k \geq 1$  the higher homotopy group  $\pi_k$  for the classical groups  $SL_{n+1}(\mathbb{C})$ ,  $SO_n(\mathbb{C})$ ,  $Sp_{2n}(\mathbb{C})$ stabilizes (i.e., becomes independent on n) when n is large enough. How large does n have to be for that?
- 31.3. Type  $D_n$ . We have  $\mathfrak{g} = \mathfrak{so}_{2n}$ , preserving the quadratic form

$$Q = \sum_{i=1}^{n} x_i x_{i+n}.$$

A Cartan subalgebra consists of matrices diag $(a_1, ..., a_n, -a_1, ..., -a_n)$ . So the representation  $\wedge^i V$ ,  $1 \leq i \leq n$ , where V is the 2n-dimensional vector representation, have highest weight (1, ..., 1, 0, ...0) (i ones), which is  $\omega_i$  if  $i \leq n-2$ .

**Exercise 31.8.** Show that the representation  $\wedge^i V$  is irreducible for  $0 \le i \le n-1$ .

Thus  $L_{\omega_i} = \wedge^i V$  for  $i \leq n-2$ . On the other hand, while the representation  $L_{(1,\dots,1,0)}$  is irreducible, it is not fundamental, as  $(1,\dots,1,0) = \omega_{n-1} + \omega_n$ , where  $\omega_{n-1} = (\frac{1}{2},\dots,\frac{1}{2},\frac{1}{2})$  and  $\omega_n = (\frac{1}{2},\dots,\frac{1}{2},-\frac{1}{2})$ . The fundamental representations  $L_{\omega_{n-1}},L_{\omega_n}$  are called the **spin representations** and denoted  $S_+,S_-$ ; their elements are called **spinors**. Similarly to the odd dimensional case, they have dimensions  $2^{n-1}$  and characters

$$\chi_{S_{\pm}} = \left( (x_1^{\frac{1}{2}} + x_1^{-\frac{1}{2}}) ... (x_n^{\frac{1}{2}} + x_n^{-\frac{1}{2}}) \right)_{+}$$

where the subscript  $\pm$  means that we take the monomials with odd (for –), respectively even (for +) number of minuses. This shows that, similarly to the odd dimensional case,  $S_+, S_-$  don't occur in  $V^{\otimes N}$  and don't lift to  $SO_{2n}(\mathbb{C})$  but require the universal covering  $\operatorname{Spin}_{2n}(\mathbb{C}) = \widetilde{SO}_{2n}(\mathbb{C})$ , called the **spin group**. Proposition 31.4 implies

Corollary 31.9. For  $n \geq 2$  the group  $\mathrm{Spin}_{2n}(\mathbb{C})$  is a double cover of  $SO_{2n}(\mathbb{C})$ .

**Example 31.10.** Consider the spin groups and representations for small dimensions. We have seen that  $\mathrm{Spin}_3 = SL_2$ ,  $S = \mathbb{C}^2$ . We also have  $\mathrm{Spin}_4 = SL_2 \times SL_2$ , with  $S_+, S_-$  being the 2-dimensional representations of the factors. We have  $\mathrm{Spin}_5 = \mathrm{Sp}_4$ , with S being the 4-dimensional vector representation. So  $SO_5 = \mathrm{Sp}_4/(\pm 1)$ . Finally,  $\mathrm{Spin}_6 = SL_4$ , with  $S_+, S_-$  being the 4-dimensional representation V and its dual  $V^*$ . Thus  $SO_6 = SL_4/(\pm 1)$ .

**Exercise 31.11.** Let V be a finite dimensional vector space with a nondegenerate inner product. Consider the algebra SV of polynomial functions on  $V^*$ . Let  $x_1, ..., x_n$  be an orthonormal basis of V, so that  $SV \cong \mathbb{C}[x_1, ..., x_n]$ , and let  $R^2 := \sum_{i=1}^n x_i^2 \in S^2V$  be the "squared radius". Also let  $\Delta = \sum_{i=1}^n \frac{\partial^2}{\partial x_i^2}$  be the **Laplace operator.** Note that the Lie algebra  $\mathfrak{so}(V)$  acts on SV by automorphisms and  $R^2$  and  $\Delta$  are  $\mathfrak{so}(V)$ -invariant. A polynomial  $P \in SV$  is called **harmonic** if  $\Delta P = 0$ .

- (i) Show that the operator of multiplication by  $R^2$  and the Laplace operator  $\Delta$  define an action of  $\mathfrak{sl}_2$  on SV which commutes with  $\mathfrak{so}(V)$ . Namely, they are proportional to f, e respectively. Compute the operator h (it will be a first order differential operator in  $x_i$ ).
- (ii) Let  $H_m \subset S^m V$  be the space of harmonic polynomials of degree m (a representation of  $\mathfrak{so}(V)$ ). Show that as an  $\mathfrak{so}(V) \oplus \mathfrak{sl}_2$ -module,

SV decomposes as

$$SV = \bigoplus_{m=0}^{\infty} H_m \otimes W_m,$$

where  $W_m$  are irreducible (infinite dimensional) representations of  $\mathfrak{sl}_2$ . Find the dimensions of  $H_m$ .

- (iii) Show that  $H_m$  is irreducible, in fact  $H_m = L_{m\omega_1}$ . Decompose  $S^mV$  into a direct sum of irreducible representations of  $\mathfrak{so}(V)$ .
- (iv) Show that  $W_m$  are Verma modules and compute their highest weights.
  - (v) For  $s \in \mathbb{C}$  consider the algebra

$$A_s := \mathbb{C}[x_1, ..., x_n]/(x_1^2 + ... + x_n^2 - s),$$

the algebra of polynomial functions on the hypersurface  $x_1^2 + ... + x_n^2 = s$  (here (f) denotes the principal ideal generated by f). This algebra has a natural action of  $\mathfrak{so}(V)$ . Decompose A into a direct sum of irreducible representations of  $\mathfrak{so}(V)$ .

31.4. The Clifford algebra. It is important to be able to realize the spin representations explicitly. The reason it is somewhat tricky is that these representations don't occur in tensor powers of V (as they have half-integer weights). However, the tensor product of a spin representation with its dual,  $S \otimes S^*$ , has integer weights and does express in terms of V. So we need to extract "the square root" from this representation, in the sense that "the space of vectors of size n is the square root of the space of square matrices of size n". This is the idea behind the Clifford algebra construction.

**Definition 31.12.** Let V be a finite dimensional vector space over an algebraically closed field  $\mathbf{k}$  of characteristic  $\neq 2$  with a nondegenerate symmetric inner product (,). The **Clifford algebra**  $\mathrm{Cl}(V)$  is the algebra generated by vectors  $v \in V$  with defining relations

$$v^2 = \frac{1}{2}(v, v), v \in V.$$

Thus for  $a, b \in V$  we have

$$ab + ba = (a + b)^2 - a^2 - b^2 = \frac{1}{2}((a + b, a + b) - (a, a) - (b, b)) = (a, b).$$

This is a deformation of the exterior algebra  $\wedge V$  which is defined in the same way but  $v^2=0$ . More precisely,  $\operatorname{Cl}(V)$  has a filtration (defined by setting  $\deg(v)=1,\ v\in V$ ) such that the associated graded algebra receives a surjective map  $\phi: \wedge V \to \operatorname{grCl}(V)$ . We will show that this is a nice ("flat") deformation, in the sense that  $\dim \operatorname{Cl}(V)=\dim \wedge V=2^{\dim V}$ , so that  $\phi$  is an isomorphism. This is a kind of Poincaré-Birkhoff-Witt theorem (namely, it is similar to the PBW theorem for Lie algebras, and in fact a special case of one if you

pass from Lie algebras to more general Lie superalgebras). Namely, we have the following theorem.

**Theorem 31.13.** The algebra Cl(V) is isomorphic to  $Mat_{2^n}(\mathbf{k})$  if  $\dim V = 2n$  and to  $Mat_{2^n}(\mathbf{k}) \oplus Mat_{2^n}(\mathbf{k})$  if  $\dim V = 2n + 1$ .

*Proof.* Let us start with the even case. Pick a basis  $a_1, ..., a_n, b_1, ..., b_n$  of V so that the inner product is given by

$$(a_i, a_j) = (b_i, b_j) = 0, \ (a_i, b_j) = \delta_{ij}.$$

We have  $a_i a_j + a_j a_i = 0$ ,  $b_i b_j + b_j b_i = 0$ ,  $b_i a_j + a_j b_i = 1$ . Define the Cl(V)-module  $M = \wedge (a_1, ..., a_n)$  with the action of Cl(V) defined by

$$\rho(a_i)w = a_i w, \ \rho(b_i)w = \frac{\partial w}{\partial a_i},$$

where

$$\frac{\partial}{\partial a_i} a_{k_1} \dots a_{k_r} = (-1)^{j-1} a_{k_1} \dots \widehat{a_{k_j}} \dots a_{k_r}$$

if  $i = k_j$  for some j (where hat means that the term is omitted), and otherwise the result is zero. It is easy to check that this is indeed a representation.

Now for  $I = (i_1 < ... < i_k), J = (j_1 < ... < j_m)$  consider the elements  $c_{IJ} = a_{i1}...a_{i_k}b_{j_1}...b_{j_m} \in Cl(V)$ . It is easy to see that these elements span Cl(V). Also it is not hard to do the following exercise.

**Exercise 31.14.** Show that the operators  $\rho(c_{IJ})$  are linearly independent.

Thus  $\rho: \mathrm{Cl}(V) \to \mathrm{End}M$  is an isomorphism, which proves the proposition in even dimensions.

Now, if dim V = 2n + 1, we pick a basis as above plus an additional element z such that  $(z, a_i) = (z, b_i) = 0$ , (z, z) = 2. So we have

$$za_i + a_i z = 0$$
,  $zb_i + b_i z = 0$ ,  $z^2 = 1$ .

Now we can define the module  $M_{\pm}$  on which  $a_i, b_i$  act as before and  $zw = \pm (-1)^{\deg w}w$ . It is easy to see as before that the map

$$\rho_+ \oplus \rho_- : \mathrm{Cl}(V) \to \mathrm{End}M_+ \oplus \mathrm{End}M_-.$$

is an isomorphism. This takes care of the odd case.

We will now construct an inclusion of the Lie algebra  $\mathfrak{so}(V)$  into the Clifford algebra. This will allow us to regard representations of the Clifford algebra as representations of  $\mathfrak{so}(V)$ , which will give us a construction of the spin representations.

Consider the linear map  $\xi: \wedge^2 V = \mathfrak{so}(V) \to \mathrm{Cl}(V)$  given by the formula

$$\xi(a \wedge b) = \frac{1}{2}(ab - ba) = ab - \frac{1}{2}(a, b).$$

Then

$$[\xi(a \land b), \xi(c \land d)] = [ab, cd] = abcd - cdab = (b, c)ad - acbd - cdab = (b, c)ad - (b, d)ac + acdb - cdab = (b, c)ad - (b, d)ac + (a, c)db - cadb - cdab = (b, c)ad - (b, d)ac + (a, c)db - (a, d)cb = (b, c)ad - (b, d)ac + (a, c)db - (a, d)cb = (b, c)ad - (b, d)ac + (a, c)db - (a, d)cb = (b, c)ad - (a, d)cb = (b, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)ac + (a, c)ad - (a, d)a$$

 $(b,c)\xi(a\wedge d)-(b,d)\xi(a\wedge c)+(a,c)\xi(d\wedge b)-(a,d)\xi(c\wedge b)=\xi([a\wedge b,c\wedge d]).$ Thus  $\xi$  is a homomorphism of Lie algebras and we can define the representations  $\xi^*M$  for even dim V and  $\xi^*M_{\pm}$  for odd dim V by  $\rho_{\xi^*M}(a):=\rho_M(\xi(a)).$ 

The representation  $\xi^*M$  is reducible, namely

$$\xi^* M = (\xi^* M)_0 \oplus (\xi^* M)_1,$$

where subscripts 0 and 1 indicate the even and odd degree parts.

**Exercise 31.15.** (i) Show that for even dim V, the representations  $(\xi^*M)_0, (\xi^*M)_1$  are isomorphic to  $S_+, S_-$  respectively.

(ii) Show that for odd dim V, the representations  $\xi^*M_+$  and  $\xi^*M_-$  are both isomorphic to S.

**Hint.** Find the highest weight vector for each of these representations and compute the weight of this vector. Then compare dimensions.

# 32. Maximal root, exponents, Coxeter numbers, dual representations

32.1. **Duals of irreducible representations.** Now let  $\mathfrak{g}$  be any complex semisimple Lie algebra. How to compute the dual of the irreducible representation  $L_{\lambda}$ ? It is clear that the highest weight of  $L_{\lambda}^*$  equals  $-\mu$ , where  $\mu$  is the lowest weight of  $L_{\lambda}$ , so we should compute the latter. For this purpose, recall that the Weyl group W of  $\mathfrak{g}$  contains a unique element  $w_0$  which maps dominant weights to antidominant weights, i.e., maps positive roots to negative roots. This is the maximal element, which is the unique element whose length is  $|R_+|$ . For example, if  $-1 \in W$  then clearly  $w_0 = -1$ . It is easy to see that the lowest weight of  $L_{\lambda}$  is  $w_0\lambda$ .

Thus we get

# Proposition 32.1. $L_{\lambda}^* = L_{-w_0\lambda}$ .

The map  $-w_0$  permutes fundamental (co)weights and simple (co)roots, so it is induced by an automorphism of the Dynkin diagram of  $\mathfrak{g}$ . So if  $\mathfrak{g}$  is simple and its Dynkin diagram has no nontrivial automorphisms, we have  $w_0 = -1$ , so  $-w_0 = 1$  and thus  $L_{\lambda}^* = L_{\lambda}$  for all  $\lambda$ . This happens for  $A_1$ ,  $B_n$ ,  $C_n$ ,  $G_2$ ,  $F_4$ ,  $E_7$  and  $E_8$ . In general, note that  $s_i$  and hence the whole Weyl group W acts trivially on P/Q, which implies that  $-w_0$  acts on P/Q by inversion. Thus we see that for  $A_{n-1}$ ,  $n \geq 3$ , when  $P/Q = \mathbb{Z}/n$ , the map  $-w_0$  is the flip of the chain. Another way to see it is to note that  $L_{\omega_1}^* = V^* = \wedge^{n-1}V = L_{\omega_{n-1}}$  (as dim V = n). For  $E_6$ ,  $P/Q = \mathbb{Z}/3$ , so  $-w_0$  must exchange the two nonzero minuscule weights and thus must also be the flip.

**Exercise 32.2.** (i) Show that for  $D_{2n+1}$  we have  $S_+^* = S_-$  while for  $D_{2n}$  we have  $S_+^* = S_+$ ,  $S_-^* = S_-$ . (**Hint:** Show that in the first case  $P/Q \cong \mathbb{Z}/4$  while in the second case  $P/Q \cong (\mathbb{Z}/2)^2$ .)

- (ii) Show that the restriction of the spin representation S of  $\mathfrak{so}_{2n+1}$  to  $\mathfrak{so}_{2n}$  is  $S_+ \oplus S_-$ .
- (iii) Show that there exist unique up to scaling nonzero **Clifford** multiplication homomorphisms

$$V \otimes S \to S$$
,  $V \otimes S_+ \to S_-$ ,  $V \otimes S_- \to S_+$ .

(iv) Compute the decomposition of the tensor products

$$S \otimes S^*, S_+ \otimes S_+^*, S_- \otimes S_-^*, S_+ \otimes S_-^*$$

into irreducible representations.

**Hint.** In the odd dimensional case, use that  $\mathrm{Cl}(V) = 2S \otimes S^*$  as an  $\mathfrak{so}(V)$ -module, that  $\mathrm{grCl}(V) = \wedge V$ , and that representations of  $\mathfrak{so}(V)$  are completely reducible.

The even case is similar:

$$Cl(V) = S_+ \otimes S_+^* \oplus S_- \otimes S_-^* \oplus S_- \otimes S_+^* \oplus S_+ \otimes S_-^*.$$

If dim V = 2n and n is even, use that all representations of  $\mathfrak{so}(V)$  are selfdual to conclude that the last two summands are isomorphic. (If n is odd, they will not be isomorphic).

Also in this case you need to pay attention to the middle exterior power - it should split into two parts. Namely, if  $\dim V = 2n$  then on  $\wedge^n V$  we have two invariant bilinear forms: one symmetric coming from the one on V, denoted  $B(\xi,\eta)$ , and the other given by wedge product  $\wedge : \wedge^n V \times \wedge^n V \to \wedge^{2n} V = \mathbb{C}$ , which is symmetric for even n and skew-symmetric for odd n. Since the wedge product form is nondegenerate, there is a unique linear operator  $*: \wedge^n V \to \wedge^n V$  called the **Hodge \*-operator** such that  $B(\xi, \eta) = \xi \wedge *\eta$ . You should show that  $*^2 = 1$  in the even case and  $*^2 = -1$  in the odd case (use an orthonormal basis of V). Thus we have an eigenspace decomposition  $\wedge^n V = \wedge_+^n V \oplus \wedge_-^n V$ , into eigenspaces of \* with eigenvalues  $\pm 1$  in the even case (called **selfdual** and **anti-selfdual** forms respectively) and  $\pm i$  in the odd case. You will see that these pieces are irreducible and isomorphic to each other in the odd case but not in the even case, and that one of them (which?) goes into  $S_+ \otimes S_+^*$  and the other into  $S_{-}\otimes S_{-}^{*}$ .

32.2. The maximal root. Let  $\mathfrak{g}$  be a complex simple Lie algebra and  $\theta$  be the maximal root of  $\mathfrak{g}$ , i.e., the highest weight of the adjoint representation. For example, for  $\mathfrak{g} = \mathfrak{sl}_n$  the adjoint representation is generated by the highest weight vector of  $V \otimes V^*$ , where  $V = \mathbb{C}^n$  is the vector representation. Thus we have

$$\theta = \omega_1 + \omega_{n-1} = (2, 1, ..., 1, 0) = (1, 0, ..., 0, -1),$$

the sum of the highest weights of V and  $V^*$  (recall that weights for  $\mathfrak{sl}_n$  are n-tuples of complex numbers modulo simultaneous translation by the same number). Thus,  $\theta$  is not fundamental. Similarly, for  $\mathfrak{g} = \mathfrak{sp}_{2n}$ , we have  $\mathfrak{g} = S^2V$  where V is the vector representation, so  $\theta = 2\omega_1$  is again not fundamental. Nevertheless, we have the following proposition.

**Proposition 32.3.** For any simple Lie algebra  $\mathfrak{g} \neq \mathfrak{sl}_n, \mathfrak{sp}_{2n}$ ,  $\theta$  is a fundamental weight.

*Proof.* If  $\mathfrak{g} = \mathfrak{so}_N$ ,  $N \geq 7$  (i.e. of type B or D but not A or C) then  $\mathfrak{g} = \wedge^2 V = L_{\omega_2}$ , so  $\theta = \omega_2$ .

If  $\mathfrak{g} = G_2$ ,  $\alpha_1 = \alpha$  is the long simple root and  $\alpha_2 = \beta$  is the short one, then we easily see that  $\theta = 2\alpha_1 + 3\alpha_2 = \omega_1$ .

If  $\mathfrak{g} = F_4$  then using the conventions of Subsection 23.3, we have  $\theta = \mathbf{e}_1 + \mathbf{e}_2 = \omega_4$ .

If  $\mathfrak{g} = E_8$  then using the conventions of Subsection 23.4, we have  $\theta = \mathbf{e}_1 + \mathbf{e}_2 = \omega_8$ .

If  $\mathfrak{g} = E_7$  then using the conventions of Subsection 23.5, we have  $\theta = \mathbf{e}_1 - \mathbf{e}_2 = \omega_1$ .

If  $\mathfrak{g} = E_6$  then using the conventions of Subsection 23.6, we have

$$\theta = \frac{1}{2}(\mathbf{e}_1 - \mathbf{e}_2 - \mathbf{e}_3 + \sum_{i=4}^{8} \mathbf{e}_i) = \omega_2.$$

32.3. **Principal**  $\mathfrak{sl}_2$ , **exponents.** Let  $\mathfrak{g}$  be a simple Lie algebra and let  $e = \sum_i e_i$  and  $h \in \mathfrak{h}$  be such that  $\alpha_i(h) = 2$  for all i (i.e.,  $h = 2\rho^{\vee}$ ). We have [h, e] = 2e and  $h = \sum_i (2\rho^{\vee}, \omega_i)h_i$ . So defining  $f := \sum_i (2\rho^{\vee}, \omega_i)f_i$ , we have [h, f] = -2f, [e, f] = h. So e, f, h span an  $\mathfrak{sl}_2$ -subalgebra of  $\mathfrak{g}$  called the **principal**  $\mathfrak{sl}_2$ -subalgebra.

**Exercise 32.4.** Let  $\mathfrak{g} = \mathfrak{sl}_{n+1}$ . Show that the restriction of the n+1-dimensional vector representation V of  $\mathfrak{g}$  to the principal  $\mathfrak{sl}_2$ -subalgebra is the irreducible representation  $L_n$ .

Consider now  $\mathfrak{g}$  as a module over its principal  $\mathfrak{sl}_2$ -subalgebra. How does it decompose? To see this, we can look at the weight decomposition of  $\mathfrak{g}$  under h. We have  $\mathfrak{g} = \mathfrak{n}_- \oplus \mathfrak{h} \oplus \mathfrak{n}_+$ , and these summands correspond to negative, zero and positive weights, respectively. Moreover, all weights are even, and for m > 0, dim  $\mathfrak{g}[2m] = r_m$  is the number of positive roots of height m, i.e., representable as a sum of m simple roots, while  $\mathfrak{g}[0] = \mathfrak{h}$  (as  $\rho^{\vee}$  is a regular coweight), so dim  $\mathfrak{g}[0] = r$ , the rank of  $\mathfrak{g}$ .

**Definition 32.5.** m is called an **exponent** of  $\mathfrak{g}$  if  $r_m > r_{m+1}$ . The multiplicity of m is  $r_m - r_{m+1}$ .

Since  $r_m$  is zero for large m while  $r_0 = r$ , there are r exponents counting multiplicities. The exponents of  $\mathfrak{g}$  are denoted  $m_i$  and are arranged in non-decreasing order:  $m_1 \leq m_2 \leq ... \leq m_r$  (including multiplicities). Note that roots of height 2 are  $\alpha_i + \alpha_j$  where i, j are connected by an edge. Thus we have  $r_0 = r_1 = r$ ,  $r_2 = r - 1$  (as the Dynkin diagram of  $\mathfrak{g}$  is a tree), so  $m_1 = 1$  and  $m_2 > 1$ . We also have  $m_r = (\rho^{\vee}, \theta) := h_{\mathfrak{g}} - 1$ , where  $\theta$  is the maximal root. The number  $h_{\mathfrak{g}}$  is called the **Coxeter number** of  $\mathfrak{g}$ . Finally, we have  $\sum_{i=1}^r m_i = |R_+|$ .

**Proposition 32.6.** The restriction of  $\mathfrak{g}$  to the principal  $\mathfrak{sl}_2$ -subalgebra decomposes as  $\bigoplus_{i=1}^r L_{2m_i+1}$ .

*Proof.* This easily follows from the representation theory of  $\mathfrak{sl}_2$  (Subsection 11.4) and the definition of  $m_i$ .

**Example 32.7.** The exponents of  $\mathfrak{sl}_n$  are 1, 2, ..., n-1.

**Exercise 32.8.** (i) Show that the exponents of  $\mathfrak{so}_{2n+1}$  and  $\mathfrak{sp}_{2n}$  are 1, 3, ..., 2n-1, and the exponents of  $\mathfrak{so}_{2n+2}$  are 1, 3, ..., 2n-1 and n (so in the latter case, when n is odd, the exponent n has multiplicity 2).

(ii) Show that the exponents of  $G_2$  are 1 and 5.

**Exercise 32.9.** Show that the exponents of  $F_4$  are 1, 5, 7, 11, the exponents of  $E_6$  are 1, 4, 5, 7, 8, 11, the exponents of  $E_7$  are 1, 5, 7, 9, 11, 13, 17, and the exponents of  $E_8$  are 1, 7, 11, 13, 17, 19, 23, 29.

**Hint:** For  $m \ge 1$ , use the data from Subsections 23.3,23.4,23.5,23.6 to count roots satisfying the equation  $(\rho^{\vee}, \alpha) = m$ , and find m where the number of such roots drops as m is increased.

**Exercise 32.10.** Use the Weyl character formula for the adjoint representation and the Weyl denominator formula to prove the following identity for a simple Lie algebra  $\mathfrak{g}$ :

$$\sum_{i=1}^{r} \frac{q^{2m_i+1} - q^{-2m_i-1}}{q - q^{-1}} = \prod_{\alpha \in R_+: (\theta, \alpha^{\vee}) > 0} \frac{q^{(\theta + \rho, \alpha^{\vee})} - q^{-(\theta + \rho, \alpha^{\vee})}}{q^{(\rho, \alpha^{\vee})} - q^{-(\rho, \alpha^{\vee})}}.$$

(**Hint:** Compute the character of  $\mathfrak{g}$  as a module over the principal  $\mathfrak{sl}_2$ -subalgebra in two different ways.)

32.4. The Coxeter number and the dual Coxeter number. We have defined the Coxeter number of a simple complex Lie algebra  $\mathfrak{g}$  (or a reduced irreducible root system R) to be  $h_R = h_{\mathfrak{g}} := (\theta, \rho^{\vee}) + 1 = m_r + 1$ , where  $m_r$  is the largest exponent of  $\mathfrak{g}$ . One can also define the dual Coxeter number of  $\mathfrak{g}$  (or R) as  $h_R^{\vee} = h_{\mathfrak{g}}^{\vee} := (\widetilde{\theta}^{\vee}, \rho) + 1$ , cf. footnote 15 (clearly,  $h_R^{\vee} = h_R$  if R is simply laced). So the dual Coxeter number is the eigenvalue  $\frac{1}{2}(\theta, \theta + 2\rho)$  of  $\frac{1}{2}C$  on the adjoint representation  $\mathfrak{g}$ , where  $C \in U(\mathfrak{g})$  is the quadratic Casimir element defined using the inner product in which  $(\theta, \theta) = 2$  (or, equivalently, long roots have squared length 2). Indeed, if we identify  $\mathfrak{h}$  and  $\mathfrak{h}^*$  using this inner product then  $\theta$  gets identified with  $\widetilde{\theta}^{\vee}$ .

Using the formulas from Subsections 23.7 and 32.2, we get

$$\begin{aligned} \mathbf{h}_{A_{n-1}} &= n, \\ \mathbf{h}_{B_n} &= 2n, \ \mathbf{h}_{B_n}^{\vee} &= 2n-1, \\ \mathbf{h}_{C_n} &= 2n, \ \mathbf{h}_{C_n}^{\vee} &= n+1, \\ \mathbf{h}_{D_n} &= 2n-2, \\ && \\ && \\ && \\ && \\ && \\ && \\ && \\$$

$$h_{G_2} = (2\alpha + 3\beta, 5\alpha^{\vee} + 3\beta^{\vee}) + 1 = 6, \ h_{G_2}^{\vee} = \frac{1}{3}(2\alpha + 3\beta, 3\alpha + 5\beta) + 1 = 4,$$

$$h_{F_4} = (8, 3, 2, 1) \cdot (1, 1, 0, 0) + 1 = 12, \ h_{F_4}^{\vee} = (\frac{11}{2}, \frac{5}{2}, \frac{3}{2}, \frac{1}{2}) \cdot (1, 1, 0, 0) + 1 = 9,$$

$$h_{E_8} = (23, 6, 5, 4, 3, 2, 1, 0) \cdot (1, 1, 0, 0, 0, 0, 0, 0) + 1 = 30,$$

$$h_{E_7} = (\frac{17}{2}, -\frac{17}{2}, 5, 4, 3, 2, 1, 0) \cdot (1, -1, 0, 0, 0, 0, 0, 0) + 1 = 18,$$

$$h_{E_6} = (4, -4, -4, 4, 3, 2, 1, 0) \cdot \frac{1}{2}(1, -1, -1, 1, 1, 1, 1, 1) + 1 = 12.$$

Note that we always have  $h_R = h_{R^{\vee}}$ , but if R is not simply laced then, as we see, the numbers  $h_R$ ,  $h_{R^{\vee}}^{\vee}$ ,  $h_R^{\vee}$  are different, in general.

# 32.5. Representations of complex, real and quaternionic type.

**Definition 32.11.** An irreducible finite dimensional  $\mathbb{C}$ -representation V of a group G or Lie algebra  $\mathfrak{g}$  is **complex type** when  $V \ncong V^*$ , **real type** if there is a symmetric isomorphism  $V \to V^*$  (i.e., an invariant symmetric inner product of V), and **quanternionic type** if there is a skew-symmetric isomorphism  $V \to V^*$  (i.e., an invariant skew-symmetric inner product of V).

It is easy to see that any irreducible finite dimensional representation is of exactly one of these three types (check it!).

**Exercise 32.12.** Let V be an irreducible finite dimensional representation of a finite group G.

- (i) Show that  $\operatorname{End}_{\mathbb{R}G}V$  is  $\mathbb{C}$  for complex type,  $\operatorname{Mat}_2(\mathbb{R})$  for real type and the quaternion algebra  $\mathbb{H}$  for quaternionic type. This explains the terminology.
- (ii) Show that V is of real type if and only if in some basis of V the matrices of all elements of G have real entries.

You may find helpful to look at [E], Problem 5.1.2 (it contains a hint).

**Example 32.13.** Let  $L_n$  be the irreducible representation of  $\mathfrak{sl}_2(\mathbb{C})$  with highest weight n (i.e., of dimension n+1). Then  $L_n$  is of real type for even n and quaternionic type for odd n. Indeed,  $L_n = S^n V$ , where  $V = L_1 = \mathbb{C}^2$ , so the invariant form on  $L_n$  is  $S^n B$ , where B is the invariant form on V, which is skew-symmetric.

Now let  $\mathfrak{g}$  be any simple Lie algebra and  $\lambda \in P_+$  be such that  $\lambda = -w_0\lambda$ , so that  $L_\lambda$  is selfdual. How to tell if it is of real or quaternionic type?

**Proposition 32.14.**  $L_{\lambda}$  is of real type if  $(2\rho^{\vee}, \lambda)$  is even and of quaternionic type if it is odd.

Proof. The number  $n := (2\rho^{\vee}, \lambda)$  is the eigenvalue of the element h of the principal  $\mathfrak{sl}_2$ -subalgebra on the highest weight vector  $v_{\lambda}$ . All the other eigenvalues are strictly less. Thus the restriction of  $L_{\lambda}$  to the principal  $\mathfrak{sl}_2$ -subalgebra is of the form  $L_n \oplus \bigoplus_{m < n} k_m L_m$ , i.e.,  $L_n$  occurs with multiplicity 1. Hence the nondegenerate invariant form on  $L_{\lambda}$  restricts to a nondegenerate invariant form on  $L_n$ , so by Example 32.13 it is skew-symmetric if n is odd and symmetric if n is even.  $\square$ 

**Example 32.15.** Consider  $\mathfrak{g} = \mathfrak{so}_{2n}$ . Then we have

$$\rho^{\vee} = \rho = \sum_{i} \omega_{i} = (n - 1, n - 2, ..., 1, 0).$$

So  $(2\rho^{\vee}, \omega_{n-1}) = (2\rho^{\vee}, \omega_n) = \frac{n(n-1)}{2}$ . This is odd if n = 2, 3 modulo 4 and even if n = 0, 1 modulo 4. Thus  $S_{\pm}$  carry a symmetric form when n = 0 mod 4 and a skew-symmetric form if n = 2 mod 4.

Consider now  $\mathfrak{g} = \mathfrak{so}_{2n+1}$ . Then  $\rho^{\vee} = \sum_{i} \omega_{i}^{\vee} = (n, n-1, ..., 1)$ . So  $(2\rho^{\vee}, \omega_{n}) = \frac{n(n+1)}{2}$ . So S carries a skew-symmetric form if  $n = 1, 2 \mod 4$  and a symmetric form if  $n = 0, 3 \mod 4$ .

We obtain the following result.

**Theorem 32.16.** (Bott periodicity for spin representations) The behavior of the spin representations of the orthogonal Lie algebra  $\mathfrak{so}_m$  is determined by the remainder r of m modulo 8. Namely:

For r = 1, 7, S is of real type.

For r = 3, 5, S is of quaternionic type.

For r = 0,  $S_+, S_-$  are of real type.

For  $r = 2, 6, S_{+}^{*} = S_{-}$  (complex type).

For r = 4,  $S_+$ ,  $S_-$  are of quaternionic type.

# 33. Differential forms, partitions of unity

Now we want to develop an integration theory on Lie groups. First we need to recall the basics about integration on manifolds.

33.1. Locally compact spaces. A Hausdorff topological space X is called **locally compact** if every point has a neighborhood whose closure is compact. For example,  $\mathbb{R}^n$  and thus every manifold is locally compact.

**Lemma 33.1.** If X is a locally compact topological space with a countable base then it can be represented as a nested union of compact subsets:  $X = \bigcup_{n \in \mathbb{N}} K_n$ ,  $K_i \subset K_{i+1}$ , such that every point  $x \in X$  has a neighborhood  $U_x$  contained in some  $K_n$ .

*Proof.* For each  $x \in X$  fix a neighborhood  $U_x$  of x such that  $\overline{U}_x$  is compact. By Lemma 1.4 the open cover  $\{U_x\}$  of X has a countable subcover  $\{W_i, i \in \mathbb{N}\}$ . Then the sets  $K_n = \bigcup_{i=0}^n \overline{W_i}$  form a desired nested sequence of compact subsets of X.

An open cover of a topological space X is said to be **locally finite** if every point of X has a neighborhood intersecting only finitely many members of this cover.

**Lemma 33.2.** Let X be a locally compact topological space with a countable base. Then every base of X has a countable, locally finite subcover.

Proof. Use Lemma 33.1 to write X as a nested union of compact sets  $K_n$  such that every point is contained in some  $K_n$  together with its neighborhood. We construct the required subcover inductively as follows. Choose finitely many sets  $U_1, ..., U_{N_0}$  of the base covering  $K_0$ , and remove all other members of the base which meet  $K_0$ . The remaining collection of open sets is no longer a base but still an open cover of X. So add finitely many new sets  $U_{N_0+1}, ..., U_{N_1}$  from this cover (all necessarily disjoint from  $K_0$ ) to our list so that it now covers  $K_1$ , and remove all other members that meet  $K_1$ , and so on. The remaining sequence  $U_1, U_2, ...$  has only finitely many members which meets every  $K_n$ , so every point of X has a neighborhood meeting only finitely many  $U_i$ .

33.2. Reminder on differential forms. Let M be a real smooth n-dimensional manifold. Recall that a differential k-form on M is a smooth section of the vector bundle  $\wedge^i T^*M$ , i.e., a skew-symmetric (n,0)-tensor field (see Subsection 5.3). Thus, for example, a 1-form is a section of  $T^*M$ . If  $x_1, ..., x_n$  are local coordinates on M near some

point  $p \in M$  then the differentials  $dx_1, ..., dx_n$  form a basis in fibers of  $T^*M$  near this point, so a general 1-form in these coordinates has the form

$$\omega = \sum_{i=1}^{n} f_i(x_1, ..., x_n) dx_i.$$

If we change the coordinates  $x_1, ..., x_n$  to  $y_1, ..., y_n$  then  $x_i$  are smooth functions of  $y_1, ..., y_n$  and in the new coordinates  $\omega$  looks like

$$\omega = \sum_{i,j=1}^{n} f_i(x_1, ..., x_n) \frac{\partial x_i}{\partial y_j} dy_j.$$

Similarly, a differential k-form in the coordinates  $x_i$  looks like

$$\omega = \sum_{1 \le i_1 \le \dots \le i_k \le n} f_{i_1, \dots, i_k}(x_1, \dots, x_n) dx_{i_1} \wedge \dots \wedge dx_{i_k}$$

where  $f_{i_1,\dots,i_k}$  are smooth functions, and in the coordinates  $y_j$  it looks like

$$\omega = \sum_{1 \le i_1 < \dots < i_k \le n} \sum_{1 \le j_1 < \dots < j_k \le n} f_{i_1, \dots, i_k}(x_1, \dots, x_n) \det \left(\frac{\partial x_{i_r}}{\partial y_{j_s}}\right) dy_{j_1} \wedge \dots \wedge dy_{j_k}.$$

The space of differential k-forms on M is denoted  $\Omega^k(M)$ . For instance,  $\Omega^0(M) = C^\infty(M)$  and  $\Omega^k(M) = 0$  for k > n. Consider now the extremal case k = n. The bundle  $\wedge^n T^*M$  is a line bundle (a vector bundle of rank 1), so locally any differential n-form in coordinates  $x_i$  has the form

$$\omega = f(x_1, ..., x_n) dx_1 \wedge ... \wedge dx_n,$$

which in coordinates  $y_i$  takes the form

$$\omega = f(x_1, ..., x_n) \det \left( \frac{\partial x_i}{\partial y_i} \right) dy_1 \wedge ... \wedge dy_n.$$

We have a canonical differentiation operator  $d:\Omega^0(M)\to\Omega^1(M)$  given in local coordinates by

$$df = \sum_{i=1}^{n} \frac{\partial f}{\partial x_i} dx_i.$$

It is easy to check that this operator does not depend on the choice of coordinates (this becomes obvious if you define it without coordinates,  $df(v) = \partial_v f$  for  $v \in T_p M$ ). Also  $\Omega^{\bullet}(M) := \bigoplus_{k=0}^n \Omega^k(M)$  is a graded algebra under wedge product, and d naturally extends to a degree 1 derivation  $d: \Omega^{\bullet}(M) \to \Omega^{\bullet}(M)$  defined in coordinates by

$$d(fdx_{i_1} \wedge \dots \wedge dx_{i_k}) = df \wedge dx_{i_1} \wedge \dots \wedge dx_{i_k}.$$

Namely, this is independent on choices and gives rise to a derivation in the "graded" sense:

$$d(a \wedge b) = da \wedge b + (-1)^{\deg a} a \wedge db.$$

A form  $\omega$  is **closed** if  $d\omega = 0$  and **exact** if  $\omega = d\eta$  for some  $\eta$ . It is easy to check that  $d^2 = 0$ , so any exact form is closed. However, not every closed form is exact: on the circle  $S^1 = \mathbb{R}/\mathbb{Z}$  the form dx is closed but the function x is defined only up to adding integers, so dx is not exact. The space  $\Omega^k_{\text{closed}}(M)/\Omega^k_{\text{exact}}(M)$  is called the k-th **de Rham cohomology** of M, denoted  $H^k(M)$ .

If  $f: M \to N$  is a differentiable mapping then for a differential form  $\omega \in \Omega^k(N)$  we can define the pullback  $f^*\omega \in \Omega^k(N)$ , given by  $(f^*\omega)(v_1, ..., v_k) = \omega(f_*v_1, ..., f_*v_k)$  for  $v_1, ..., v_k \in T_pM$ . This operation commutes with wedge product and the differential, and  $(f \circ g)^* = g^* \circ f^*$ .

33.3. Partitions of unity. Let M be a manifold and  $\{U_i, i \in I\}$  be an open cover of M.

**Definition 33.3.** A smooth **partition of unity** subordinate to  $\{U_i, i \in I\}$  is a collection  $\{f_s, s \in S\}$  of smooth nonnegative functions on M such that

- (i) for all s the support of  $f_s$  is contained in  $U_i$  for some i = i(s);
- (ii) Any  $y \in M$  has a neighborhood in which all but finitely many  $f_s$  are zero;

(iii) 
$$\sum_{s} f_{s} = 1$$
.

Note that the sum in (iii) makes sense because of condition (ii). Note also that given any partition of unity  $\{f_s\}$  subordinate to  $\{U_i\}$ ,

we can define 
$$F_i := \sum_{s: i(s)=i} f_s,$$

and this is a new partition of unity subordinate to the same cover now labeled by the set I, with the support of  $F_i$  contained in  $U_i$ .

Finally, note that in every partition of unity on M, the set of s such that  $f_s$  is not identically zero is countable, and moreover finite if M is compact. This follows from the fact that by Lemma 1.4, any open cover of a manifold M has a countable subcover, and moreover a finite one if M is compact (applied to the neighborhoods from condition (ii)).

**Proposition 33.4.** Any open cover  $\{U_i, i \in I\}$  of a manifold M admits a partition of unity subordinate to this cover.

*Proof.* Define a function  $h:[0,\infty]\to\mathbb{R}$  given by h(t)=0 for  $t\geq 1$  and  $h(t)=\exp(\frac{1}{t-1})$  for t<1. It is easy to check that h is smooth.

Thus we can define the smooth **hat function**  $H(x) := h(|x|^2)$  on  $\mathbb{R}^n$ , supported on the closed unit ball  $\overline{B(0,1)}$ .

If  $\phi: \overline{B(0,1)} \to M$  is a  $C^{\infty}$ -map which is a diffeomorphism onto the image, we will say that the image of  $\phi$  is a **closed ball** in M. Thus given a closed ball  $\overline{B}$  on M (equipped with a diffeomorphism  $\phi: \overline{B(0,1)} \to \overline{B}$ ), we have a hat function  $H_B(y) := H(\phi^{-1}(y))$  on  $\overline{B}$ , which we extend by zero to a smooth function on M whose support is  $\overline{B}$  and which is strictly positive in its interior  $B \subset \overline{B}$ .

Now let  $\{\overline{B}_s, s \in J\}$  be the collection of all closed balls in M such that their interiors  $B_s$  are contained in some  $U_i$ . Then  $\{B_s, s \in J\}$  is clearly a base for M. Thus by Lemma 33.2, this base has a countable, locally finite subcover  $\{B_s, s \in S\}$ . Picking diffeomorphisms  $\phi_s : \overline{B(0,1)} \to \overline{B}_s, s \in S$ , we can define the smooth function  $F(y) := \sum_{s \in S} H_{B_s}(y)$ , which is strictly positive on M since  $B_s$  cover M (this makes sense by the local finiteness). Now define the smooth functions  $f_s(y) := \frac{H_{B_s}(y)}{F(y)}$ . This collection is a partition of unity subordinate to the cover  $\{U_i\}$ , as desired.

#### 34. Integration on manifolds

34.1. Integration of top differential forms on oriented manifolds. An important operation with top degree differential forms is **integration**. Namely, if  $\omega$  is a differential n-form on an open set  $U \subset \mathbb{R}^n$  (with the usual orientation),  $\omega = f(x_1, ..., x_n) dx_1 \wedge ... \wedge dx_n$ , then we can set

$$\int_{U} \omega := \int_{U} f(x_1, ..., x_n) dx_1 ... dx_n.$$

(provided this integral is absolutely convergent). This, however, is not completely canonical: if we change coordinates (so that U maps diffeomorphically to U'), the change of variable formula in a multiple integral tells us that

$$\int_{U} f(x_1, ..., x_n) dx_1 \wedge ... \wedge dx_n = \int_{U'} f(x_1(\mathbf{y}), ..., x_n(\mathbf{y})) \left| \det \left( \frac{\partial x_i}{\partial y_j} \right) \right| dy_1 \wedge ... \wedge dy_n,$$

while the transformation law for  $\omega$  is the same but without the absolute value. This shows that our definition is invariant only under orientation preserving transformations of coordinates, i.e., ones whose Jacobian  $\det\left(\frac{\partial x_i}{\partial y_j}\right)$  is positive. Consequently, we will only be able to define integration of top differential forms on **oriented manifolds**, i.e., ones equipped with an atlas of charts in which transition maps have a positive Jacobian; such an atlas defines an **orientation** on M. To fix an orientation, we just need to say which local coordinate systems (or bases of tangent spaces) are right-handed, and do so in a consistent way. But this cannot always be done globally (the classic counterexamples are Möbius strip and Klein bottle).

Now let us proceed to define integration of a continuous top form  $\omega$  over an oriented manifold M. For this pick an atlas of local charts  $\{U_i, i \in I\}$  on M and pick a partition of unity  $\{f_s\}$  subordinate to this cover, which is possible by Proposition 33.4. First assume that  $\omega$  is nonnegative, i.e.,  $\omega(v_1, ..., v_n) \geq 0$  for a right-handed basis  $v_i$  of any tangent space of M. Then define

(34.1) 
$$\int_{M} \omega := \sum_{s} \int_{U_{i(s)}} f_{i(s)} \omega$$

where in each  $U_i$  we use a right-handed coordinate system to compute the corresponding integral. This makes sense (as a nonnegative real number or  $+\infty$ ), and is also independent of the choice of a partition of unity. Indeed, it is easy to see that for two atlases  $\{U_i\}$ ,  $\{V_j\}$  and two partitions of unity  $\{f_s\}$ ,  $\{g_t\}$  the answer is the same, by comparing both to the answer for the atlas  $\{U_i \cap V_j\}$  and partition of unity  $\{f_sg_t\}$ . In fact, this makes sense for any measurable  $\omega$  (i.e., given by a measurable function in every local chart) if we use Lebesgue integration.

Now, if  $\omega$  is not necessarily nonnegative, we may define the nonnegative form  $|\omega|$  which is  $\omega$  at points where  $\omega$  is nonnegative and  $-\omega$  otherwise. Then, if

$$\int_{M} |\omega| < \infty,$$

we can define  $\int_M \omega$  by the same formula (34.1) which will now be a not necessarily positive but absolutely convergent series (a finite sum in the compact case).

Importantly, the same definition works for manifolds M with boundary  $\partial M$  (an n-1-manifold); the only difference is that at boundary points the manifold locally looks like  $\mathbb{R}^n_+$  (the space of vectors with nonnegative last coordinate) rather than  $\mathbb{R}^n$ . Note that the boundary of an oriented manifold carries a canonical orientation as well (a basis of  $T_p\partial M$  is right-handed if adding to it a vector looking inside M produces a right-handed basis of  $T_pM$ ).

**Remark 34.1.** If the manifold M is non-orientable, we cannot integrate top differential forms on M. However, we can integrate **densities** on M, which are sections of the line bundle  $| \wedge^n T^*M |$ , the absolute value of the orientation bundle. This bundle is defined by transition functions  $|g_{ij}(x)|$ , where  $g_{ij}(x)$  are the transition functions of  $\wedge^n T^*M$ . Thus its sections, called densities on M, transform under changes of coordinates according to the rule

$$f(x_1,...,x_n)|dx_1\wedge...\wedge dx_n| = f(x_1(\mathbf{y}),...,x_n(\mathbf{y}))|\det\left(\frac{\partial x_i}{\partial y_j}\right)|\cdot|dy_1\wedge...\wedge dy_n|,$$

i.e., exactly the one needed for the integral to be defined canonically. This procedure actually makes sense for any manifold, and in the oriented case reduces to integration of top forms described above.

Using partitions of unity, it is not hard to show that the bundle  $|\wedge^n T^*M|$  is trivial (check it!). A positive smooth section of this bundle (i.e., positive in every chart) therefore exists and is nothing but a **positive smooth measure** on M, and any two such measures differ by multiplication by a positive smooth function. Moreover, given such a measure  $\mu$  and a measurable function f on M such that  $\int_M |f| d\mu < \infty$  (i.e.,  $f \in L^1(M,\mu)$ ), we can define  $\int_M f d\mu$  as usual.

34.2. Nonvanishing forms. Let us say that a top degree continuous differential form  $\omega$  on M is **non-vanishing** if for any  $x \in M$ ,  $\omega_x \in \wedge^n T_x^* M$  is nonzero. In this case,  $\omega$  defines an orientation on M by declaring a basis  $v_1, ..., v_n$  of  $T_x M$  right-handed if  $\omega(v_1, ..., v_n) > 0$ 

(in particular, there are no non-vanishing top forms on non-orientable manifolds). Thus we can integrate top differential forms on M, and in particular  $\omega$  defines a positive measure  $\mu = \mu_{\omega}$  on M, namely

$$\mu(U) = \int_{U} \omega$$

for an open set  $U \subset M$  (this integral may be  $+\infty$ , but is finite if U is a small enough neighborhood of any point  $x \in M$ ). Thus we can integrate functions on M with respect to this measure:

$$\int_{M} f d\mu = \int_{M} f \omega.$$

This, of course, only makes sense if f is measurable and  $\int_M |f| d\mu < \infty$ , i.e., if  $f \in L^1(M,\mu)$ . Note also that if  $\lambda \in \mathbb{R}^\times$  then  $\mu_{\lambda\omega} = |\lambda| \mu_\omega$ .

**Example 34.2.** If M is an open set in  $\mathbb{R}^n$  with the usual orientation and  $\omega = dx_1 \wedge ... \wedge dx_n$  then  $\int_M \omega = \int_M dx_1...dx_n$  is just the volume of M. For this reason top differential forms are often called **volume forms**, especially when they are non-vanishing and thus define an orientation and a measure on M, and in the latter case  $\int_M \omega$ , if finite, is called the **volume of** M with respect to  $\omega$ .

**Proposition 34.3.** If M is compact and  $\omega$  is non-vanishing then M has finite volume under the measure  $\mu = \mu_{\omega}$ , and every bounded measurable (in particular, any continuous) function on M is in  $L^1(M, \mu)$ .

Proof. For each  $x \in M$  choose a neighborhood  $U_x$  of x such that  $\mu(U_x) < \infty$ . The collection of sets  $U_x$  forms an open cover of M, so it has a finite subcover  $U_1, ..., U_N$ , and  $\mu(M) \leq \mu(U_1) + ... + \mu(U_N) < \infty$ . Then  $\int_M |f| d\mu \leq \mu(M) \sup |f| < \infty$  for bounded measurable f.

34.3. Stokes formula. A central result about integration of differential forms is

**Theorem 34.4.** (Stokes formula) If M is an n-dimensional oriented manifold with boundary and  $\omega$  a differential n-1-form on M of class  $C^1$  then

$$\int_{M} d\omega = \int_{\partial M} \omega.$$

In particular, if M is closed (has no boundary) then  $\int_M d\omega = 0$ , and if  $\omega$  is closed  $(d\omega = 0)$  then  $\int_{\partial M} \omega = 0$ .

When M is an interval in  $\mathbb{R}$ , this reduces to the fundamental theorem of calculus. If M is a region in  $\mathbb{R}^2$ , this reduces to Green's formula. If M is a surface in  $\mathbb{R}^3$ , this reduces to the classical Stokes formula from

vector calculus. Finally, if M is a region in  $\mathbb{R}^3$  then this reduces to the Gauss formula (Divergence theorem).

The proof of the Stokes formula is not difficult. Namely, by writing  $\omega$  as  $\sum_s f_s \omega$  for some partition of unity, it suffices to prove the formula for M being a box in  $\mathbb{R}^n$ , which easily follows from the fundamental theorem of calculus.

34.4. **Integration on Lie groups.** Now let G be a real Lie group of dimension n. In this case given any  $\xi \in \wedge^n \mathfrak{g}^*$ , we can extend it to a left-invariant skew-symmetric tensor field (i.e., top differential form)  $\omega_{\xi}$  on G. Also, if  $\xi \neq 0$  then  $\omega = \omega_{\xi}$  is non-vanishing and thus defines an orientation and a left-invariant positive measure  $\mu_{\omega}$  on G. Note that  $\xi$  is unique up to scaling by a real number  $\lambda \in \mathbb{R}^{\times}$ . So, since  $\mu_{\lambda\omega} = |\lambda|\mu_{\omega}$ , we see that  $\mu_{\omega}$  is defined uniquely up to scaling by positive numbers. This measure is called the **left-invariant Haar measure** and we'll denote it just by  $\mu_L$  (assuming that the normalization has been chosen somehow).

In a similar way we can define the **right invariant Haar measure**  $\mu_R$  on G. One may ask if these measures coincide (or, rather, are proportional, since they are defined only up to normalization). This question is answered by the following proposition.

Given a 1-dimensional real representation V of a group G, let |V| be the representation of G on the same space with  $\rho_{|V|}(g) = |\rho_V(g)|$ , where  $\rho: G \to \operatorname{Aut}(V) = \mathbb{R}^{\times}$ .

**Proposition 34.5.**  $\mu_L = \mu_R$  if and only if  $| \wedge^n \mathfrak{g}^* |$  (or, equivalently,  $| \wedge^n \mathfrak{g} |$ ) is a trivial representation of G.

Proof. It is clear that  $\mu_L = \mu_R$  if and only if the left-invariant top volume form  $\omega$  on G is also right invariant up to sign. This is equivalent to saying that  $\omega$  is conjugation invariant up to sign, i.e., that  $\omega_1 \in \wedge^n \mathfrak{g}^*$  is invariant up to sign under the action of G. This implies the statement.

If  $\mu_L = \mu_R$  then G is called **unimodular**. In this case we have a **bi-invariant Haar measure**  $\mu = \mu_L = \mu_R$  on G (under some normalization).

In particular, we see that if G has no nontrivial continuous characters  $G \to \mathbb{R}^{\times}$  then it is unimodular.

**Example 34.6.** If G is a discrete countable group then G is unimodular and  $\mu$  is the counting measure:  $\mu(U) = |U|$  (number of elements in U).

**Exercise 34.7.** (i) Let us say that a finite dimensional real Lie algebra  $\mathfrak{g}$  of dimension n is unimodular if  $\wedge^n \mathfrak{g}$  is a trivial representation of  $\mathfrak{g}$ .

Show that a connected Lie group G is unimodular if and only if so is LieG.

- (ii) Show that a perfect Lie algebra (such that  $\mathfrak{g} = [\mathfrak{g}, \mathfrak{g}]$ ) is unimodular. In particular, a semisimple Lie algebra is unimodular.
- (iii) Show that a nilpotent (in particular, abelian) Lie algebra is unimodular.
- (iv) Show that if  $\mathfrak{g}_1, \mathfrak{g}_2$  are unimodular then so is  $\mathfrak{g}_1 \oplus \mathfrak{g}_2$ . Deduce that a reductive Lie algebra is unimodular.
- (v) Show that the Lie algebra of upper triangular matrices of size n is **not** unimodular for n > 1. Give an example of a Lie algebra  $\mathfrak{g}$  and ideal I such that I and  $\mathfrak{g}/I$  are unimodular but  $\mathfrak{g}$  is not.
- (vi) Give an example of a non-unimodular Lie group G such that its connected component of the identity  $G^{\circ}$  is unimodular (try groups of the form  $\mathbb{Z} \ltimes \mathbb{R}$ ).

For a unimodular Lie group G, we will sometimes denote the integral of a function f with respect to the Haar measure by

$$\int_{G} f(g)dg.$$

**Proposition 34.8.** A compact Lie group is unimodular.

*Proof.* The representation of G on  $| \wedge^n \mathfrak{g}^* |$  defines a continuous homomorphism  $\rho: G \to \mathbb{R}^+$ . Since G is compact, the image  $\rho(G)$  of  $\rho$  is a compact subgroup of  $\mathbb{R}^+$ . But the only such subgroup is the trivial group. This implies the statement.

Thus, on a compact Lie group we have a (bi-invariant) Haar measure  $\mu$ . Moreover, in this case  $\int_G d\mu = \text{Volume}(G) < \infty$ , so we have a canonical normalization of  $\mu$  by the condition that it is a probability measure:

$$\int_G d\mu = 1.$$

E.g., for finite groups this normalization is the averaging measure, which is  $|G|^{-1}$  times the counting measure. This is the normalization we will use if G is compact.

#### 35. Representations of compact Lie groups

35.1. Unitary representations. Now we can extend to compact groups the result that representations of finite groups are unitary. Namely, let V be a finite dimensional (continuous) complex representation of a compact Lie group G.

**Proposition 35.1.** V admits a G-invariant unitary structure.

*Proof.* Fix a positive Hermitian form B on V and define a new Hermitian form on V by

$$B_{\mathrm{av}}(v,w) = \int_G B(\rho_V(g)v, \rho_V(g)w)dg.$$

This form is well defined since G is compact and is G-invariant by construction (since the measure dg is invariant). Also  $B_{av}(v, v) > 0$  for  $v \neq 0$  since B(w, w) > 0 for any  $w \neq 0$ .

Corollary 35.2. Every finite dimensional representation V of a compact Lie group G is completely reducible.

*Proof.* Let  $W \subset V$  be a subrepresentation and B be an invariant positive Hermitian form on V. Let  $W^{\perp} \subset V$  be the orthogonal complement of W under B. Then  $V = W \oplus W^{\perp}$ , which implies the statement.  $\square$ 

In particular, this applies to the special unitary group SU(n). Recall that  $SU(n)/SU(n-1) = S^{2n-1}$ , which implies that SU(n) is simply connected. Thus (smooth) representations of SU(n) is the same thing as representations of the Lie algebra  $\mathfrak{su}(n)$  or its complexification  $\mathfrak{sl}_n$ . Thus we get a new, analytic proof that finite dimensional representations of  $\mathfrak{sl}_n$  are completely reducible (this is called **Weyl's unitary trick**). In fact, we will see that complete reducibility of finite dimensional representations of all semisimple Lie algebras can be proved in this way.

35.2. Matrix coefficients. Let V be a finite dimensional continuous complex representation of a Lie group G. A matrix coefficient of V is a function  $G \to \mathbb{C}$  of the form  $(f, \rho_V(g)v)$  for some  $v \in V$  and  $f \in V^*$ . Obviously, such a function is continuous.

**Proposition 35.3.** Matrix coefficients are smooth.

*Proof.* Let us say that  $v \in V$  is smooth if the function  $f(\rho_V(g)v)$  is smooth for any  $f \in V^*$ ; it is clear that such vectors form a subspace  $V_{\text{sm}}$  of V. Our job is to show that, in fact,  $V_{\text{sm}} = V$ . To this end let

us first construct some smooth vectors. For this let  $\phi: G \to \mathbb{C}$  be a smooth function with compact support, and let

$$w = w(\phi, v) := \int_G \phi(g) \rho_V(g) v dg,$$

where dg is a left-invariant Haar measure on G and  $v \in V$ . We claim that w is a smooth vector. Indeed,

$$f(\rho_V(h)w) = f\left(\rho_V(h) \int_G \phi(g)\rho_V(g)vdg\right) =$$
$$\int_G f(\phi(g)\rho_V(hg)v)dg = \int_G f(\phi(h^{-1}g)\rho_V(g)v)dg,$$

and this is manifestly smooth in h (we can differentiate indefinitely under the integral sign).

Define a **delta-like sequence** (or a **Dirac sequence**) around a point  $x_0 \in M$  on a manifold M with a smooth measure dx to be a sequence of continuous functions  $\phi_n$  on M such that for every neighborhood U of  $x_0$  the supports of almost all  $\phi_n$  are contained in U, and  $\int_M \phi_n(x) dx = 1$ . The "hat" function construction implies that delta-like sequences exist and can be chosen non-negative and smooth. Namely, we can pick a sequence of non-negative smooth functions satisfying the first condition and then normalize it to satisfy the second one.

Now let  $\phi_n$  be a smooth delta-like sequence around 1 on G with left-invariant Haar measure. Let  $w_n := w(\phi_n, v)$ . It is obvious that  $w_n \to v$  as  $n \to \infty$ . Thus  $V_{\rm sm}$  is dense in V. Since V is finite dimensional, it follows that  $V_{\rm sm} = V$ , as claimed.

Now let V be an irreducible representation of a compact Lie group G. As shown above, it has an invariant positive Hermitian inner product, which we'll denote by (,). Moreover, this product is unique up to scaling. Pick an orthonormal basis  $v_1, ..., v_n$  of V under this inner product, and let  $v_1^*, ..., v_n^*$  be the dual basis of  $V^*$ . Now consider the matrix coefficients of V in this basis:

$$\psi_{V,ij}(g) := v_j^*(\rho_V(g)v_i) = (\rho_V(g)v_i, v_j).$$

Note that these functions are independent on the normalization of (,). Suppose now that we also have another such representation W with orthonormal basis  $w_i$ .

**Theorem 35.4.** (Orthogonality of matrix coefficients) We have

$$\int_{G} \psi_{V,ij}(g) \overline{\psi_{W,kl}(g)} dg = 0$$

if V is not isomorphic to W. Also

$$\int_{G} \psi_{V,ij}(g) \overline{\psi_{V,kl}(g)} dg = \frac{\delta_{ik} \delta_{jl}}{\dim V}.$$

*Proof.* We have

$$\int_{G} \psi_{V,ij}(g) \overline{\psi_{W,kl}(g)} dg = \int_{G} ((\rho_{V}(g) \otimes \rho_{\overline{W}}(g))(v_{i} \otimes w_{k}), v_{j} \otimes w_{l}) dg = (P(v_{i} \otimes w_{k}), v_{j} \otimes w_{l})$$

where

$$P := \int_{G} \rho_{V}(g) \otimes \rho_{\overline{W}}(g) dg = \int_{G} \rho_{V \otimes \overline{W}}(g) dg.$$

Since W is unitary,  $\overline{W} \cong W^*$ , so we have

$$P = \int_{G} \rho_{V \otimes W^{*}}(g) dg : V \otimes W^{*} \to V \otimes W^{*}.$$

By construction,  $\operatorname{Im}(P) \subset (V \otimes W^*)^G$ , which is zero if  $V \ncong W$ . Thus we have proved the proposition in this case.

It remains to consider the case V=W. In this case  $V\otimes W^*=V\otimes V^*=V\otimes \overline{V}$ , and the only invariant in this space up to scaling is  $\mathbf{u}:=\sum_k v_k\otimes v_k$ . Also P is conjugation invariant under G, so by decomposing  $V\otimes V^*$  into irreducibles we see that it is the orthogonal projector to  $\mathbb{C}\mathbf{u}$ :

$$P\mathbf{x} = \frac{(\mathbf{x}, \mathbf{u})}{(\mathbf{u}, \mathbf{u})}\mathbf{u} = \frac{(\mathbf{x}, \mathbf{u})\mathbf{u}}{\dim V}.$$

In particular,

$$(P(v_i \otimes w_k), v_j \otimes w_l) = \frac{\delta_{ik}\delta_{jl}}{\dim V},$$

as claimed.

35.3. The Peter-Weyl theorem. Thus we see that the functions  $\psi_{V,ij}$  for various V,i,j form an orthogonal system in the Hilbert space  $L^2(G) = L^2(G,dg)$  of measurable functions  $f: G \to \mathbb{C}$  such that

$$||f||^2 = \int_G |f(g)|^2 dg < \infty.$$

A fundamental result about compact Lie groups is that this system is, in fact, complete:

**Theorem 35.5.** (Peter-Weyl theorem) The functions  $\psi_{V,ij}$  form an orthogonal basis of  $L^2(G)$ .

Theorem 35.5 will be proved in Section 36.

35.4. An alternative formulation of the Peter-Weyl theorem. Given a finite dimensional irreducible representation V of G, consider the space  $\text{Hom}_G(V, L^2(G))$  of G-homomorphisms for the action of G on  $L^2(G)$  by left translations. We have an obvious inclusion

$$\iota_V: V^* \hookrightarrow \operatorname{Hom}_G(V, L^2(G))$$

via the matrix coefficient map  $f \mapsto [v \mapsto (\rho_{V^*}(-)f)(v)]$ . Clearly, this is a map of G-modules, where now G acts on  $L^2(G)$  by right translations. We claim that  $\iota_V$  is surjective, i.e., an isomorphism. For this, note that an element  $\phi \in \operatorname{Hom}_G(V, L^2(G))$  can be viewed a left G-equivariant  $L^2$ -function  $\phi: G \to V^*$ , i.e. such that for almost all  $g \in G$  (with respect to the Haar measure) we have

(35.1) 
$$\phi(x) = \rho_{V^*}(xg^{-1})\phi(g)$$

for almost all  $x \in G$ . But then by changing  $\phi$  on a set of measure zero if needed, we may replace it by a continuous function (the right hand side of (35.1)). Then, setting g = 1, we have  $\phi(x) = \rho_{V^*}(x)\phi(1)$ , as claimed.

Thus we have a natural inclusion

$$\xi: \bigoplus_{V \in \operatorname{Irrep}(G)} V \otimes V^* \cong \bigoplus_{V \in \operatorname{Irrep}(G)} V \otimes \operatorname{Hom}_G(V, L^2(G)) \hookrightarrow L^2(G),$$

which is actually an embedding of  $G \times G$ -modules, and we will denote the image of  $\xi$  by  $L^2_{\rm alg}(G)$  (the "algebraic part" of  $L^2(G)$ ). Note that if  $\psi \in L^2(G)$  generates a finite dimensional representation V under the action of G by left translations then  $\psi$  belongs to the image of a homomorphism  $V \to L^2(G)$ , hence to  $L^2_{\rm alg}(G)$ . Thus  $L^2_{\rm alg}(G)$  is just the subspace of  $\psi \in L^2(G)$  which generate a finite dimensional representation under left translations by G. We also see that it may be equivalently characterized as the subspace of  $\psi \in L^2(G)$  which generate a finite dimensional representation under right translations by G.

**Theorem 35.6.** (Peter-Weyl theorem, alternative formulation) The space  $L^2_{alg}(G)$  is dense in  $L^2(G)$ . In other words, the map  $\xi$  gives rise to an isomorphism

$$\widehat{\oplus}_{V \in \operatorname{Irrep}(G)} V \otimes V^* \to L^2(G)$$

where the first copy of G acts on V and the second one on  $V^*$  and the hat denotes the Hilbert space completion of the direct sum.

Note that this is again an instance of the double centralizer property! Namely, it expresses representation-theoretically the fact that the centralizer of the group of left translations on G is the group of right translations on G, and vice versa.

For example, let  $G = S^1$ . Then the irreducible representations of G are the characters  $\psi_n(\theta) = e^{in\theta}$ . So the Peter-Weyl theorem in this case says that  $\{e^{in\theta}\}$  is an orthonormal basis of  $L^2(S^1)$  with norm

$$||f||^2 := \frac{1}{2\pi} \int_0^{2\pi} |f(\theta)|^2 d\theta,$$

which is the starting point for Fourier analysis. So the Peter-Weyl theorem is similarly a starting point for **nonabelian Fourier** (or harmonic) analysis.

**Exercise 35.7.** Let G be a compact Lie group and  $H \subset G$  a closed subgroup. Then we have a compact homogeneous space G/H and the Haar measure on G defines a probability measure on G/H. So we can define the infinite dimensional unitary representation  $L^2(G/H)$  of G.

(i) Show that have a decomposition

$$L^2(G/H) = \widehat{\bigoplus}_{V \in \operatorname{Irrep}G} N_H(V) V,$$

where  $N_H(V) = \dim V^H$ , the dimension of the space of H-invariants of V.

(ii) Let G = SO(3), so the irreducible representations are  $L_{2m}$  for  $m \geq 0$ . Thus

$$L^2(G/H) = \widehat{\oplus}_{m \ge 0} N_H(m) L_{2m}.$$

Compute this decomposition (i.e., the numbers  $N_H(m)$ ) for  $H = \mathbb{Z}/n\mathbb{Z}$  acting by rotations around an axis by angles  $2\pi k/n$  (rotations of a regular n-gon).

- (iii) Do the same for the dihedral group  $H = \mathbf{D}_n$  of symmetries of the regular n-gon (where reflections in the plane are realized as rotations around a line in this plane).
- (iv) Do the same for the groups H = SO(2) and H = O(2) of rotations and symmetries of the circle.
- (v) Do the same for H being the group of symmetries of a platonic solid (tetrahedron, cube, icosahedron).

It may be more convenient to give  $N_V(m)$  in the form of the generating function  $\sum_m N_V(m)t^m$ .

**Exercise 35.8.** Let  $G = GL_n(\mathbb{C})$ . A regular algebraic function on G is a polynomial of  $X_{ij}$  and  $\det(X)^{-1}$  for  $X \in G$ . Denote by  $\mathcal{O}(G)$  the algebra of regular algebraic functions on G.

- (i) Show that  $G \times G$  acts on  $\mathcal{O}(G)$  by left and right multiplication.
- (ii) (Algebraic Peter-Weyl theorem) Show that as a  $G \times G$ -module, we have

$$\mathcal{O}(G) = \bigoplus_{V \in \operatorname{Irrep}(G)} V \otimes V^*.$$

**Hint.** Compute  $\operatorname{Hom}_G(V, \mathcal{O}(G))$  where G acts on  $\mathcal{O}(G)$  by right translations. For this, interpret elements of this space as equivariant functions  $G \to V^*$  and show that such functions are automatically regular algebraic.

(iii) Generalize (i) and (ii) to orthogonal and symplectic groups.

# 35.5. Orthogonality and completeness of characters.

Corollary 35.9. Let  $\chi_V(g) = \text{Tr}(\rho_V(g))$  be the character of V. Then  $\{\chi_V(g), V \in \text{Irrep}G\}$  is an orthonormal basis of  $L^2(G)^G$ , the space of conjugation-invariant functions in  $L^2(G)$  (i.e., such that  $f(gxg^{-1}) = f(x)$ ).

Proof. We have  $\chi_V(g) = \sum_i \psi_{V,ii}(g)$ , so by orthogonality of matrix coefficients  $\chi_V$  are orthonormal in  $L^2(G)^G$ . So it remains to show that they are complete. For this observe that  $L^2_{\rm alg}(G)^G = \xi(\bigoplus_V (V \otimes V^*)^G) = \bigoplus_V \mathbb{C}\chi_V$ . Thus our job is to show that  $L^2_{\rm alg}(G)^G$  is dense in  $L^2(G)^G$ . To this end, for  $\psi \in L^2(G)^G$  fix a sequence  $\psi_n \in L^2_{\rm alg}(G)$  such that  $\psi_n \to \psi$  as  $n \to \infty$ . Such a sequence exists by the Peter-Weyl theorem. Let

$$\psi_n^{\text{av}}(x) = \int_G \psi_n(gxg^{-1})dg.$$

It is easy to see that  $\psi_n^{\text{av}} \in L^2_{\text{alg}}(G)$ . Also  $||\psi_n^{\text{av}} - \psi|| \le ||\psi_n - \psi|| \to 0$ ,  $n \to \infty$ , as claimed.

#### 36. Proof of the Peter-Weyl theorem

36.1. Compact operators and the Hilbert-Schmidt theorem. To prove the Peter-Weyl theorem, we will use the Hilbert-Schmidt theorem – the spectral theorem for compact self-adjoint operators in a Hilbert space.

Recall that a **bounded** operator  $A: H \to H$  on a Hilbert space H is a linear operator such that for some  $C \geq 0$  we have  $||A\mathbf{v}|| \leq C||\mathbf{v}||$ ,  $\mathbf{v} \in H$ . The smallest constant C with this property is called the **norm** of A and denoted ||A||. Recall also that A is **compact** if there is a sequence of finite rank operators  $A_n: H \to H$  such that  $||A_n - A|| \to 0$  as  $n \to \infty$ . In other words, the space K(H) of compact operators on H is the closure of the space  $K_f(H)$  of finite rank operators under the norm  $A \mapsto ||A||$  on the space of bounded operators B(H).

**Lemma 36.1.** If A is compact then it maps bounded sets to precompact sets (i.e., ones whose closure is compact). In other words, for every bounded sequence  $\mathbf{v}_n \in H$ , the sequence  $A\mathbf{v}_n$  has a convergent subsequence.<sup>16</sup>

*Proof.* Let  $\mathbf{v}_n \in H$ ,  $||\mathbf{v}_n|| \le 1$ . Pick a sequence of finite rank operators  $A_n$  such that  $||A_n - A|| < \frac{1}{n}$ . Let  $\mathbf{v}_n^1$  be a subsequence of  $\mathbf{v}_n$  such that  $A_1\mathbf{v}_n^1$  is convergent. Let  $\mathbf{v}_n^2$  be a subsequence of  $\mathbf{v}_n^1$  such that  $A_2\mathbf{v}_n^2$  is convergent, and so on. Finally, let  $\mathbf{w}_n = \mathbf{v}_n^n$ . Note that

$$||A\mathbf{v}_i^k - A\mathbf{v}_j^k|| \le ||A_k\mathbf{v}_i^k - A_k\mathbf{v}_j^k|| + ||A - A_k|| \cdot ||\mathbf{v}_i^k - \mathbf{v}_j^k||$$
  
$$\le ||A_k\mathbf{v}_i^k - A_k\mathbf{v}_j^k|| + \frac{2}{k} - \varepsilon_k.$$

for some  $\varepsilon_k > 0$ . Since  $A_k \mathbf{v}_i^k$ ,  $i \geq 1$  is convergent, it is a Cauchy sequence, so there is  $M_k$  such that for  $i, j \geq M_k$ ,  $||A_k \mathbf{v}_i^k - A_k \mathbf{v}_j^k|| < \varepsilon_k$ , hence

$$||A\mathbf{v}_i^k - A\mathbf{v}_i^k|| < \frac{2}{k}.$$

But  $\mathbf{w}_n$  is a subsequence of  $\mathbf{v}_n^k$  starting from the k-th term. So there is  $N_k$  such that

$$||A\mathbf{w}_i - A\mathbf{w}_j|| < \frac{2}{k}, \ i, j \ge N_k.$$

In other words, the sequence  $A\mathbf{w}_n$  is Cauchy. Hence it is convergent, as desired.

**Proposition 36.2.** Let M be a compact manifold with positive smooth probability measure  $d\mathbf{x}$  and  $K(\mathbf{x}, \mathbf{y})$  a continuous function on  $M \times M$ . Then the operator

$$(A\psi)(\mathbf{y}) := \int_M K(\mathbf{x}, \mathbf{y}) \psi(\mathbf{x}) d\mathbf{x}.$$

 $<sup>^{16}</sup>$ The converse statement also holds, but we will not need it.

on  $L^2(M)$  is compact.

Proof. By using a partition of unity, the problem can be reduced to the case when M is replaced by the hypercube  $[0,1]^n$ . Let us split it in  $m^n$  pixels of sidelength  $\frac{1}{m}$  and approximate  $K(\mathbf{x},\mathbf{y})$  by its maximal value on each of the  $m^{2n}$  pixels in  $[0,1]^{2n}$ . Denote the corresponding approximation by  $K_m(\mathbf{x},\mathbf{y})$  and the corresponding operator by  $A_m$ ; it has rank  $\leq m^n$ . Let  $\varepsilon_m := \sup |K - K_m|$ , then  $||A - A_m|| \leq \varepsilon_m$ . Finally, by Cantor's theorem,  $K_m = 0$  as  $K_m = 0$ 0 as  $K_m = 0$ 1.

Recall that a bounded operator A is **self-adjoint** if  $(A\mathbf{v}, \mathbf{w}) = (\mathbf{v}, A\mathbf{w})$  for  $\mathbf{v}, \mathbf{w} \in H$ .

**Theorem 36.3.** (Hilbert-Schmidt) Let  $A: H \to H$  be a compact self-adjoint operator. Then there is an orthogonal decomposition

$$H = \operatorname{Ker} A \oplus \widehat{\bigoplus}_{\lambda} H_{\lambda},$$

where  $\lambda$  runs over non-zero eigenvalues of A, and  $A|_{H_{\lambda}} = \lambda \cdot \text{Id}$ . Moreover, the spaces  $H_{\lambda}$  are finite dimensional and the eigenvalues  $\lambda$  are real and either form a finite set or a sequence going to 0.

Note that for finite rank operators, this obviously reduces to the standard theorem in linear algebra: a self-adjoint (Hermitian) operator on a finite dimensional space V with a positive Hermitian form has an orthogonal eigenbasis, and its eigenvalues are real.

Proof. We first prove the theorem for the operator  $A^2$ . Let  $\beta := ||A||^2 = \sup_{||\mathbf{v}||=1} (A^2\mathbf{v}, \mathbf{v}) \geq 0$ . We may assume without loss of generality that  $\beta \neq 0$ . Let  $A_n$  be a sequence of self-adjoint finite rank operators converging to A, and let  $\beta_n = ||A_n||^2$ , which is also the maximal eigenvalue of  $A_n^2$ . We have  $\beta_n \to \beta$ . Let  $\mathbf{v}_n$  be a sequence of unit vectors in H such that  $A_n^2\mathbf{v}_n = \beta_n\mathbf{v}_n$ . By Lemma 36.1, the sequence  $A^2\mathbf{v}_n$  has a convergent subsequence, so passing to this subsequence we may assume that  $A^2\mathbf{v}_n$  is convergent to some  $\mathbf{w} \in H$ . Hence  $A_n^2\mathbf{v}_n \to \mathbf{w}$ , so  $\mathbf{v}_n \to \beta^{-1}\mathbf{w}$ . Thus  $A^2\mathbf{w} = \beta\mathbf{w}$ . We can now replace H with the orthogonal complement of  $\mathbf{w}$  and iterate this procedure.

As a result we'll get a sequence of numbers  $\beta_1 > \beta_2 > \dots > 0$ , which is either finite (in which case the theorem is obvious) or tends to 0 (by compactness of  $A^2$ ), and the corresponding sequence of finite dimensional orthogonal eigenspaces  $H_{\beta_k}$  (also by compactness of  $A^2$ ). Let  $\mathbf{v}$  be a vector orthogonal to all  $H_{\beta_k}$ . Then  $||A\mathbf{v}||^2 \leq \beta_k ||\mathbf{v}||^2$  for all

 $<sup>^{17}\</sup>mathrm{Cantor}$ 's theorem says that any continuous function on a compact set X is uniformly continuous.

k, so if  $\beta_k$  is an infinite sequence going to 0, it follows that  $A\mathbf{v} = 0$ , as desired.

Now, we have  $H = \operatorname{Ker} A^2 \oplus \widehat{\bigoplus}_n H_{\beta_n}$ , and A preserves this decomposition, acting by 0 on  $\operatorname{Ker} A^2$  and with eigenvalues  $\pm \sqrt{\beta_n}$  on  $H_{\beta_n}$ . This implies the theorem.

36.2. **Proof of the Peter-Weyl theorem.** Let G be a compact Lie group and  $h_N$  a delta-like sequence around 1 on G. By replacing  $h_N(x)$  with  $\frac{1}{2}(h_N(x) + h_N(x^{-1}))$ , we may assume that  $h_N$  is invariant under inversion. Define the **convolution operators**  $B_N$  on  $L^2(G)$  by

$$(B_N \psi)(y) = \int_G h_N(x)\psi(x^{-1}y)dx = \int_G h_N(yz^{-1})\psi(z)dz.$$

By Proposition 36.2, these operators are compact (as the kernel  $K(y, z) := h_N(yz^{-1})$  is continuous). Moreover, they are clearly self-adjoint (as  $h_N(x) = h_N(x^{-1})$  and  $h_N$  is real) and commute with right translations by G. So by the Hilbert-Schmidt theorem, we have the corresponding spectral decomposition

$$L^2(G) = \operatorname{Ker} B_N \oplus \widehat{\bigoplus}_{\lambda} H_{N,\lambda}$$

invariant under right translations. Since  $H_{N,\lambda}$  are finite dimensional and invariant under right translations, they are contained in  $L^2_{\text{alg}}(G)$  (this is the key step of the proof). Thus the closure  $\overline{L^2_{\text{alg}}(G)}$  contains the image of  $B_N$ . So for any  $\psi \in L^2(G)$  we can find  $\psi_N \in L^2_{\text{alg}}(G)$  such that  $||B_N\psi - \psi_N|| < \frac{1}{N}$ .

Now let  $\psi \in C(G)$ . By Cantor's theorem,  $\psi$  is uniformly continuous. It follows that  $B_N \psi$  uniformly converges to  $\psi$  as  $N \to \infty$  (check it!). Thus

$$||\psi - \psi_N|| \le ||\psi - B_N \psi|| + ||B_N \psi - \psi_N|| < ||\psi - B_N \psi|| + \frac{1}{N} \to 0$$

as  $N \to \infty$ . So  $\overline{L^2_{\mathrm{alg}}(G)}$  contains C(G). But C(G) is dense in  $L^2(G)$  (namely, by using a partition of unity this reduces to the case of a box in  $\mathbb{R}^n$ , where it is well known). Thus  $\overline{L^2_{\mathrm{alg}}(G)} = L^2(G)$ . This completes the proof of the Peter-Weyl theorem.

### 36.3. Existence of faithful representations.

**Lemma 36.4.** Let G be a compact Lie group and  $G = G_0 \supset G_1 \supset ...$  be a nested sequence of closed subgroups without repetitions. Then this sequence is finite.

*Proof.* Assume the contrary, i.e. that it is infinite. The dimensions must stabilize, so we may assume that  $\dim G_n$  are all the same. Then  $K = G_n^{\circ}$  is independent on n, and we have a nested sequence

$$G_0/K \supset G_1/K \supset ...$$

of finite groups, without repetitions. But such a sequence can't have length bigger than  $|G_0/K|$ , contradiction.

**Corollary 36.5.** Any compact Lie group has a faithful finite dimensional representation, so it is isomorphic to a closed subgroup of the unitary group U(n).

Proof. Pick a nontrivial finite dimensional representation  $V_1$  of  $G = G_0$ , and let  $G_1$  be the kernel of this representation. Now pick another representation  $V_2$  of G which is nontrivial as a  $G_1$ -representation, and let  $G_2$  be the kernel of  $V_2$  in  $G_1$ , and so on. By Lemma 36.4, at some point we will have a subgroup  $G_k \subset G$  such that every finite dimensional representation of G is trivial when restricted to  $G_k$ . But then by the Peter-Weyl theorem,  $G_k$  acts trivially on  $L^2(G)$ , so  $G_k = 1$ . Thus  $V_1 \oplus \ldots \oplus V_k$  is a faithful G-representation.

**Remark 36.6.** Conversely, any closed subgroup of U(n) is a compact Lie group, see Exercise 36.13 below.

Remark 36.7. Corollary 36.5 is false for non-compact Lie groups, even for connected ones. For example, let G be the universal cover of  $SL_2(\mathbb{R})$  (it has fiber  $\mathbb{Z} = \pi_1(SL_2(\mathbb{R}))$ ). Indeed, any finite dimensional continuous representation V of G is smooth, so gives a finite dimensional representation of the Lie algebra  $\mathfrak{sl}_2(\mathbb{R})$ , hence of  $\mathfrak{sl}_2(\mathbb{C})$ , which is therefore a direct sum of  $L_n$ . So V exponentiates to  $SL_2(\mathbb{C})$ , and thus its restriction to  $\mathfrak{sl}_2(\mathbb{R})$  exponentiates to  $SL_2(\mathbb{R})$ , so is not faithful for G.

Exercise 36.8. Show that any compact Lie group admits a structure of a metric space such that the metric is invariant under left and right translations.

36.4. **Density in continuous functions.** In fact, we can now prove an even stronger version of the Peter-Weyl theorem. For this note that  $L^2_{\text{alg}}(G)$  is a unital algebra.

**Theorem 36.9.** The algebra  $L^2_{alg}(G)$  is dense in the algebra of continuous functions C(G) in the supremum norm

$$||f|| = \max_{g \in G} |f(g)|.$$

*Proof.* Consider the closure  $\mathcal{A}$  of  $L^2_{\text{alg}}(G)$  inside C(G) (under the supremum norm). Then  $\mathcal{A}$  is a closed subalgebra invariant under complex conjugation, and by Corollary 36.5 it separates points on G. Therefore, by the Stone-Weierstrass theorem,  $\mathcal{A} = C(G)$ .

**Remark 36.10.** If  $G = S^1$ , this is the usual theorem of uniform approximation of continuous functions on the circle by trigonometric polynomials. If we restrict to even functions, this will be just the usual Weierstrass theorem on approximation of continuous functions on an interval by polynomials.

Corollary 36.11. Let  $A \subset L^2_{alg}(G)$  be a left-invariant subalgebra stable under complex conjugation and separating points on G. Then  $A = L^2_{alg}(G)$ .

Proof. By the Stone-Weierstrass theorem, A is dense in C(G) in uniform metric, hence in  $L^2(G)$  in the Hilbert norm. Thus for every irreducible representation V of G,  $\operatorname{Hom}_G(V,A)$  must be dense in the space  $\operatorname{Hom}_G(V,L^2(G)_{\operatorname{left}})=V^*$ . So  $\operatorname{Hom}_G(V,A)=V^*$ , hence  $A=L^2_{\operatorname{alg}}(G)$ .

Let us call a finite dimensional representation V of a group G unimodular if  $\wedge^{\dim V} V \cong \mathbb{C}$  is the trivial representation.

**Proposition 36.12.** Let V be a faithful finite dimensional representation of a compact Lie group G. Then:

- (i) If V is unimodular then the subalgebra  $A \subset C(G)$  generated by matrix coefficients  $f(\rho_V(g)v)$ ,  $v \in V$ ,  $f \in V^*$ , coincides with  $L^2_{alg}(G)$ .
- (ii) If Y an irreducible finite dimensional representation of G, then for some n, m, the representation Y is contained as a direct summand in  $V^{\otimes n} \otimes V^{*\otimes m}$ . Moreover, if V is unimodular then one may take m = 0.
- *Proof.* (i) Let  $d := \dim(V)$ . It is clear that  $A \subset L^2_{\text{alg}}(G)$  is G-invariant and A separates points on G, since V is faithful. Also G is a closed subgroup of  $SU(V) \subset V \otimes V^*$ , and for a unitary matrix with determinant 1 one has  $g^{\dagger} = g^{-1} = \wedge^{d-1}g$ . Thus A is invariant under complex conjugation. So by Corollary 36.11  $A = L^2_{\text{alg}}(G)$ .
- (ii) It suffices to establish the unimodular case since in general we may replace V with the unimodular representation  $V \oplus V^*$ . But then by (i),  $L^2_{alg}(G)$  is a quotient of  $S(V \otimes V^*)$ , which implies the statement.  $\square$

**Exercise 36.13.** In this exercise you will show that a closed subgroup of a Lie group G is a closed Lie subgroup (Theorem 3.13).

Clearly, it suffices to assume that G is connected. Let  $\mathfrak{g}=\mathrm{Lie}G$  and  $H\subset G$  be a closed subgroup.

(i) Let  $\mathfrak{h}$  be the set of vectors  $a \in \mathfrak{g}$  such that there is a sequence  $h_n \in H, h_n \to 1$ , and nonzero real numbers  $c_n$  such that

$$c_n \log h_n \to a, \ n \to \infty.$$

This is clearly a subset of  $\mathfrak{g}$  invariant under scalar multiplication (since we can rescale  $c_n$ ). Show that  $\mathfrak{h}$  consists of all  $a \in \mathfrak{g}$  for which the 1-parameter subgroup  $\exp(ta)$  is contained in H. (Consider the elements  $h_n^{[c_n]}$ , where [c] is the floor of c).

- (ii) Show that  $\mathfrak{h}$  is a subspace of  $\mathfrak{g}$ . (For  $a, b \in \mathfrak{h}$  consider the elements  $h_N := \exp(\frac{a}{N}) \exp(\frac{b}{N})$  to show that  $a + b \in \mathfrak{h}$ ).
- (iii) Show that  $\mathfrak h$  is a Lie subalgebra of  $\mathfrak g$ . (For  $a,b\in\mathfrak h$  consider the elements

$$h_N := \exp(\frac{a}{N}) \exp(\frac{b}{N}) \exp(-\frac{a}{N}) \exp(-\frac{b}{N})$$

to show that  $[a, b] \in \mathfrak{h}$ ).

- (iv) Let  $H_0 \subset G$  be the connected Lie subgroup with Lie algebra  $\mathfrak{h}$ . Given a sequence  $h_N \in H$ ,  $h_N \to 1$ , show that  $h_N \in H_0$  for  $N \gg 1$ . To this end, pick a transverse slice  $S \subset G$  to  $H_0$  near 1, and write  $h_N = s_N h_{N,0}$ , where  $h_{N,0} \in H_0$ ,  $s_N \in S$ . Look at the asymptotics of  $\log s_N$  as  $N \to \infty$ , and deduce that  $s_N = 1$  for large enough N.
- (v) Conclude that G/H is a manifold, and S defines a local chart on this manifold near 1. Deduce that H is a closed Lie subgroup of G, and  $H_0 = H^{\circ}$ .

#### 37. Representations of compact topological groups

37.1. Existence of the Haar measure. One can generalize integration theory to arbitrary compact and even to locally compact topological groups. For simplicity we will describe this generalization in the case of compact topological groups with a countable base.

Namely, let X be a compact Hausdorff topological space with a countable base. For compact Hausdorff spaces this is equivalent to being metrizable. Let  $C(X,\mathbb{R})$  be the space of continuous real-valued functions on X. This is a real Banach space with norm

$$||f|| = \max_{x \in X} |f(x)|.$$

Recall that by the **Riesz-Markov-Kakutani representation theorem**, a finite Borel measure  $\mu$  on X is the same thing as a positive continuous linear functional  $I: C(X,\mathbb{R}) \to \mathbb{R}$  (i.e., such that  $I(f) \geq 0$  for  $f \geq 0$ ), namely,

$$I(f) = \int_X f d\mu.$$

Moreover,  $\mu$  is a probability measure if and only if I(1) = 1, and any  $\mu \neq 0$  has positive volume and so can be normalized to be a probability measure.

Now let G be a compact topological group with a countable base. It acts on  $C(G,\mathbb{R})$  by left and right translations, so acts on nonnegative probability measures of G.

**Theorem 37.1.** (Haar, von Neumann) G admits a unique left-invariant probability measure.

This measure is also automatically right-invariant (since it is unique) and is called the **Haar measure** on G.

Remark 37.2. A unique up to scaling left-invariant regular Haar measure (albeit of infinite volume and not always right-invariant in the non-compact case) exists more generally for any locally compact group G (not necessarily having a countable base). We will not prove this here, but we remark that Haar measures on Lie groups that we have constructed using top differential forms are a special case of this.

*Proof.* Let  $g_i, i \geq 1$  be a dense sequence in G (it exists since G has a countable base, hence is separable, as you can pick a point in every open set of this base). Let  $p_i$  be a sequence of positive numbers

<sup>18</sup> Note that a finite Borel measure on a compact Hausdorff space with a countable base is necessarily regular.

such that  $\sum_i p_i = 1$ . To this data attach the **averaging operator**  $A: C(G, \mathbb{R}) \to C(G, \mathbb{R})$  given by

$$(Af)(x) = \sum_{i} p_i f(xg_i).$$

This operator can be interpreted as follows: we have a Markov chain with states being points of G and the transition probability from x to  $xg_i$  equal to  $p_i$ , then (Af)(x) is the expected value of f after one transition starting from x. It is clear that A is a left-invariant bounded operator (of norm 1). Moreover, A acts by the identity on the line  $L \subset C(G, \mathbb{R})$  of constant functions.

For  $f \in C(G, \mathbb{R})$  denote by  $\nu(f)$  the distance from f to L, i.e.,

$$\nu(f) = \frac{1}{2}(\max f - \min f).$$

Then  $\nu(Af) < \nu(f)$  unless  $f \in L$ . Indeed, if f is not constant and  $x \in G$ , pick j such that  $f(xg_j) < \max f$  (exists since the sequence  $xg_i$  is dense in G), then

$$(Af)(x) = \sum_{i} p_i f(xg_i) \le (1 - p_j) \max f + p_j f(xg_j) < \max f.$$

So  $\max(Af) < \max f$ . Similarly,  $\min(Af) > \min f$ .

Now fix  $f \in C(G, \mathbb{R})$  and consider the sequence  $f_n := A^n f$ ,  $n \geq 0$ . This means that we let our Markov chain run for n steps. We know that for finite Markov chains there is an asymptotic distribution, and we'll show that this is also the case in the situation at hand, giving rise to a construction of the invariant integral.

Obviously, the sequence  $f_n$  is uniformly bounded by  $\max |f|$ . Also it is **equicontinuous**: for any  $\varepsilon > 0$  there exists a neighborhood  $1 \in U \subset G$  such that for any  $x \in G$  and  $u \in U$ ,

$$|f_n(x) - f_n(ux)| < \varepsilon.$$

Indeed, it suffices to show that f is uniformly continuous, i.e., for any  $\varepsilon$  find U such that for all  $x \in G$ ,  $u \in U$  we have  $|f(x)-f(ux)| < \varepsilon$ ; this U will then work for all  $f_n$ . But this is guaranteed by Cantor's theorem. Namely, assume the contrary, that there is no such U. Then there are two sequences  $x_i, u_i \in G$ ,  $u_i \to 1$ , with  $|f(x_i) - f(u_i x_i)| \ge \varepsilon$ . The sequence  $x_i$  has a convergent subsequence, so we may assume without loss of generality that  $x_i \to x \in G$ . Then taking the limit  $i \to \infty$ , we get that  $\varepsilon \le 0$ , a contradiction.

Therefore, by the **Ascoli-Arzela theorem** the sequence  $f_n$  has a convergent subsequence. Let us remind the proof of this theorem. We construct subsequences  $f_n^k$  of  $f_n$  inductively by picking  $f_n^k$  from  $f_n^{k-1}$  so that  $f_n^k(g_k)$  converges (with  $f_n^0 = f_n$ ), which can be done by the

boundedness assumption, and then set  $h_m := f_m^m = f_{n(m)}$ . Then  $h_m(g_i)$  converges, hence Cauchy, for all i, which by equicontinuity implies that  $h_m(x)$  is a Cauchy sequence in  $C(G, \mathbb{R})$ , hence converges to some  $h \in \mathbb{C}(G, \mathbb{R})$ .

We claim that  $h \in L$ . Indeed, we have

$$\nu(f_{n(m)}) \ge \nu(f_{n(m)+1}) = \nu(Af_{n(m)}) \ge \nu(f_{n(m+1)}),$$

so taking the limit when  $m \to \infty$ , we get

$$\nu(h) \ge \nu(Ah) \ge \nu(h)$$
,

i.e.,  $\nu(Ah) = \nu(h)$ . The assignment  $f \mapsto h$  is therefore a continuous left-invariant positive linear functional  $I: C(G, \mathbb{R}) \to L = \mathbb{R}$ , and I(1) = 1, as claimed.

Similarly, we may construct a right-invariant integral

$$I_*: C(G, \mathbb{R}) \to L = \mathbb{R}$$

with  $I_*(1) = 1$ , and by construction for any left invariant integral J we have  $J(f) = J(I_*(f))$ . Thus for every left invariant integral J with J(1) = 1 we have  $J(f) = I_*(f)$ ; in particular  $I(f) = I_*(f)$ . This shows that I is unique, invariant on both sides and independent on the choice of  $g_i, p_i$ , and hence that  $A^n f \to I(f)$  as  $n \to \infty$ .

**Example 37.3.** A basic example of a compact topological group with countable base which is, in general, not a Lie group, is a **profinite group**. Namely, let  $G_1, G_2, ...$  be finite groups and  $\phi_i : G_{i+1} \to G_i$  be surjective homomorphisms. Then the **inverse limit**  $G := \varprojlim G_n$  is the group consisting of sequences  $g_1 \in G_1, g_2 \in G_2, ...$  where  $\phi_i(g_{i+1}) = g_i$ . This group G has projections  $p_n : G \to G_n$  and a natural topology, for which a base of neighborhoods of 1 consists of  $\operatorname{Ker}(p_n)$ . (This topology can be defined by a bi-invariant mertic:  $d(\mathbf{a}, \mathbf{b}) = C^{n(\mathbf{a}, \mathbf{b})}$ , where  $n(\mathbf{a}, \mathbf{b})$  is the first position at which  $\mathbf{a}, \mathbf{b}$  differ, and 0 < C < 1). A sequence  $\mathbf{a}^n$  converges to  $\mathbf{a}$  in this topology if for each k,  $a_k^n$  eventually stabilizes to  $a_k$ . It is easy to show that G is compact.

Profinite groups are ubiquitous in mathematics. For example, the p-adic integers  $\mathbb{Z}_p$  for a prime p form a profinite group, namely the inverse limit of  $\mathbb{Z}/p^n\mathbb{Z}$ ; in fact, it is a profinite ring. The multiplicative group of this ring  $\mathbb{Z}_p^{\times}$  is also a profinite group. One may also consider non-abelian profinite groups  $GL_n(\mathbb{Z}_p)$ ,  $O_n(\mathbb{Z}_p)$ ,  $Sp_{2n}(\mathbb{Z}_p)$ , etc. Finally, absolute Galois groups, such as  $Gal(\overline{\mathbb{Q}}/\mathbb{Q})$ , are (very complicated) profinite groups.

Note that infinite profinite groups are uncountable and **totally disconnected**, i.e.,  $G^{\circ} = 1$ .

More generally, the inverse limit makes sense if  $G_i$  are compact Lie groups. In this case G is equipped with the product topology, so also compact (by Tychonoff's theorem). For example, consider the sequence of Lie groups  $G_n = \mathbb{R}/\mathbb{Z}$  and maps  $\phi_i : G_{i+1} \to G_i$  given by  $\phi_i(x) = px$  for a prime p. We can realize  $G_n$  as  $\mathbb{R}/p^n\mathbb{Z}$ , then  $\phi_i(y) = y \mod p^i$ . Let  $G := \varprojlim G_n$ . We have projections  $p_n : G \to G_n$ , and an element  $a \in \operatorname{Ker}(p_1)$  is a sequence of elements  $a_n \in \mathbb{Z}/p^n$  such that  $a_{n+1}$  projects to  $a_n$ , i.e.,  $\operatorname{Ker}(p_1) = \mathbb{Z}_p$ . Thus we have a short exact sequence of compact topological groups

$$0 \to \mathbb{Z}_n \to G \to \mathbb{R}/\mathbb{Z} \to 0$$

(non-split, as G is connected). In fact, we can obtain G as a quotient  $(\mathbb{R} \times \mathbb{Z}_p)/\mathbb{Z}$  where  $\mathbb{Z}$  is embedded diagonally.

Corollary 37.4. Finite dimensional (continuous) representations of a compact topological group G with a countable base are unitary and completely reducible.

The proof is the same as for Lie groups, once we have the integration theory, which we now do.

#### 37.2. The Peter-Weyl theorem for compact topological groups.

**Theorem 37.5.** (i) (Peter-Weyl theorem) Let G be a compact topological group with a countable base. Then the set IrrepG is countable, and

$$L^2(G) = \widehat{\oplus}_{V \in \mathrm{Irrep}(G)} V \otimes V^*$$

as a  $G \times G$ -module.

(ii) The subspace  $L^2_{alg}(G) = \bigoplus_{V \in Irrep(G)} V \otimes V^*$  is dense in C(G) in the supremum norm.

Again, the proof is analogous to Lie groups, using a delta-like sequence of continuous hat functions. Namely, we may take

$$h_N(x) = c_N \max(\frac{1}{N} - d(x, 1), 0),$$

where d is some metric defining the topology of G, and  $c_N > 0$  are normalization constants such that  $\int_G h_N(x) dx = 1$ .

**Remark 37.6.** If G is profinite then finite dimensional representations of G are just representations of  $G_n$  for various n:

$$\operatorname{Irrep} G = \bigcup_{n>1} \operatorname{Irrep} G_n$$

(nested union).

**Corollary 37.7.** Any compact topological group with countable base is an inverse limit of a sequence of compact Lie groups ...  $\rightarrow G_1 \rightarrow G_0$ , where the maps  $G_{i+1} \rightarrow G_i$  are surjective.

*Proof.* Let  $V_1, V_2, ...$  be the irreducible representations of G. Let  $K_m = \operatorname{Ker}(\rho_{V_1} \oplus ... \oplus \rho_{V_m}) \subset G$ , a closed normal subgroup. Then  $G/K_m \subset U(V_1 \oplus ... \oplus V_n)$  is a compact Lie group, and  $\cap_m K_m = 1$ , so G is the inverse limit of  $G/K_m$ .

**Exercise 37.8.** (i) Let  $\mathbb{Q}_p = \mathbb{Z}_p[1/p]$  be the field of p-adic numbers, i.e., the field of fractions of  $\mathbb{Z}_p$ . Construct the Haar measure |dx| on the additive group of  $\mathbb{Q}_p$  in which the volume of  $\mathbb{Z}_p$  is 1 using the Haar measure on  $\mathbb{Z}_p$ .

- (ii) Show that  $\mathbb{Q} \subset \mathbb{Q}_p$  and  $\mathbb{Q}_p = \mathbb{Q} + \mathbb{Z}_p$ , and use this to define an embedding  $\mathbb{Q}_p/\mathbb{Z}_p \to \mathbb{Q}/\mathbb{Z}$ . Show that  $\mathbb{Q}/\mathbb{Z} = \bigoplus_{p \text{ prime}} \mathbb{Q}_p/\mathbb{Z}_p$ .
- (iii) Define the additive character  $\psi : \mathbb{Q}_p \to U(1) \subset \mathbb{C}^{\times}$  by  $\psi(x) := \exp(2\pi i \overline{x})$ , where  $\overline{x}$  is the image of x in  $\mathbb{Q}/\mathbb{Z}$ . Use  $\psi$  to label the characters (=irreducible representations) of  $\mathbb{Z}_p$  by  $\mathbb{Q}_p/\mathbb{Z}_p$ .
- (iv) Let |x| be the p-adic norm of  $x \in \mathbb{Q}_p$  ( $|x| = p^{-n}$  if  $x \in p^n \mathbb{Z}_p$  but  $x \notin p^{n+1} \mathbb{Z}_p$ , and |0| = 0). For which  $s \in \mathbb{C}$  is the function  $|x|^s$  in  $L^2(\mathbb{Z}_p)$ ?
- (v) The Peter-Weyl theorem in particular implies that any  $L^2$  function f on a compact abelian group G with a countable base can be expanded in a Fourier series

$$f(x) = \sum_{j} c_j \psi_j(x),$$

where  $\psi_j$  are the characters of G. Write the Fourier expansion of  $|x|^s$  when it is in  $L^2(\mathbb{Z}_p)$ .

- (vi) Show that  $\frac{|dx|}{|x|}$  is a Haar measure on the multiplicative group  $\mathbb{Q}_p^{\times} = GL_1(\mathbb{Q}_p)$ . More generally, show that  $|dX| := \frac{\prod_{1 \leq i,j \leq n} |dx_{ij}|}{|\det(X)|^n}$  is a Haar measure on  $GL_n(\mathbb{Q}_p)$  (where  $X = (x_{ij})$ ).
  - (vii) Classify characters of  $\mathbb{Z}_p^{\times}$ .
- (viii) Let S be the space of locally constant functions on  $\mathbb{Q}_p$  with compact support (i.e., linear combinations of indicator functions of sets of the form  $a+p^n\mathbb{Z}_p$ ,  $a\in\mathbb{Q}_p$ ). Show that the Fourier transform operator

$$\mathcal{F}(f) = \int_{\mathbb{Q}_p} \psi(xy) f(y) |dy|$$

maps S to itself, and  $(\mathcal{F}^2 f)(x) = f(-x)$ . Show that  $\mathcal{F}$  preserves the integration pairing on S,  $(f,g) = \int_{\mathbb{Q}_p} f(x)\overline{g(x)}|dx|$ , and therefore extends to a unitary operator  $L^2(\mathbb{Q}_p) \to L^2(\mathbb{Q}_p)$ .

#### 38. The hydrogen atom, I

38.1. The Schrödinger equation. Let us now apply our knowledge of non-abelian harmonic analysis to solve a basic problem in quantum mechanics – describe the dynamics of the hydrogen atom.

The mechanics of the hydrogen atom is determined by motion of a charged quantum particle (electron) in a rotationally invariant attracting electric field. The potential of such a field is  $-\frac{1}{r}$ , where  $r^2 = x^2 + y^2 + z^2$  (since this theory does not have nontrivial dimensionless quantities, we may choose the units of measurement so that all constants are equal to 1). Thus, the wave function  $\psi(x, y, z, t)$  for our particle obeys the **Schrödinger equation** 

$$i\partial_t \psi = H\psi$$

where H is the quantum Hamiltonian

$$H := -\frac{1}{2}\Delta - \frac{1}{r},$$

and  $\Delta = \partial_x^2 + \partial_y^2 + \partial_z^2$  is the Laplace operator. Recall also that for each t, the function  $\psi(-,-,-,t)$  is in  $L^2(\mathbb{R}^3)$  and  $||\psi|| = 1$ . The problem is to solve this equation given the initial value  $\psi(x,y,z,0)$ .<sup>19</sup>

The Schrödinger equation can be solved by separation of variables as follows. Suppose we have an orthonormal basis  $\psi_N$  of  $L^2(\mathbb{R}^3)$  such that  $H\psi_N=E_N\psi_N$ . Then if

$$\psi(x, y, z, 0) = \sum_{N} c_N \psi_N(x, y, z)$$

(i.e.,  $c_N = (\psi, \psi_N)$ ) then

$$\psi(x, y, z, t) = \sum_{N} c_N e^{-iE_N t} \psi_N(x, y, z),$$

So our job is to find such basis  $\psi_N$ , i.e., diagonalize the self-adjoint operator H.

Note that the operator H is unbounded and defined only on a dense subspace of  $L^2(\mathbb{R})$ , and although it is symmetric  $((H\psi, \eta) = (\psi, H\eta))$  for compactly supported functions), it is very nontrivial to say what precisely it means that H is self-adjoint. Also, this operator turns out to have both discrete and continuous spectrum, which means that there is actually no basis with the desired properties – eigenfunctions of H which lie in  $L^2(\mathbb{R}^3)$  span a proper closed subspace of this Hilbert space. However, this will not be a problem for our calculation.

<sup>&</sup>lt;sup>19</sup>Recall that  $\psi$  determines the probability p(U,t) to find the electron in a region  $U \subset \mathbb{R}^3$  at a time t, which is given by the formula  $p(U,t) = \int_U |\psi(x,y,z,t)|^2 dx dy dz$ .

# 38.2. **Bound states.** We first focus on **bound states**, i.e., solutions of the **stationary Schrödinger equation**

$$H\psi = E\psi$$

which belong to  $L^2(\mathbb{R}^3)$  and thus decay at infinity in the sense of  $L^2$ norm (this is the situation when the electron does not have enough\nenergy to escape from the nucleus, i.e., it is "bound" to it and thus unlikely to be found far from the origin, which explains the terminology).
In particular, such eigenfunctions must have negative energy, E < 0.
To do so, let us utilize the rotational symmetry and write this equation\nin spherical coordinates. For this we just need to write the Laplacian  $\Delta$  in spherical coordinates. Let us write  $\mathbf{r} = r\mathbf{u}$ , where  $\mathbf{u} \in S^2$  (i.e.,  $|\mathbf{u}| = 1$ ). We have

$$\Delta = \Delta_r + \frac{1}{r^2} \Delta_{\rm sph}$$

where

$$\Delta_{\rm sph} = \frac{1}{\sin^2 \phi} \partial_{\theta}^2 + \frac{1}{\sin \phi} \partial_{\phi} \sin \phi \partial_{\phi}$$

is a differential operator on  $S^2$  (the **spherical Laplacian**, or the **Laplace-Beltrami operator**) and

$$\Delta_r = \partial_r^2 + \frac{2}{r}\partial_r$$

is the radial part of  $\Delta$  (check it!). So our equation looks like

$$\partial_r^2 \psi + \frac{2}{r} \partial_r \psi + \frac{2}{r} \psi + \frac{1}{r^2} \Delta_{\rm sph} \psi = -2E\psi.$$

This equation can be solved by again applying separation of variables. Namely, we look for solutions in the form

$$\psi(r, \mathbf{u}) = f(r)\xi(\mathbf{u}),$$

where

(38.1) 
$$\Delta_{\rm sph}\xi + \lambda\xi = 0.$$

Then we obtain the following equation for f:

(38.2) 
$$f''(r) + \frac{2}{r}f'(r) + (\frac{2}{r} - \frac{\lambda}{r^2} + 2E)f(r) = 0.$$

So now we have to solve equation (38.1) and in particular determine which values of  $\lambda$  occur.

To this end, recall that the operator  $\Delta_{\rm sph}$  is rotationally invariant, so it preserves the space  $L^2_{\rm alg}(S^2)$  of functions on  $S^2$  belonging to finite dimensional representations of SO(3). Moreover, it preserves the decomposition  $L^2_{\rm alg}(S^2) = \bigoplus_{\ell \geq 0} L_{2\ell}$  of this space into irreducible representations of SO(3) (Exercise 35.7(ii)), and on each  $L_{2\ell}$  it acts by a certain scalar  $-\lambda_{\ell}$ . To compute this scalar, consider the vector  $Y^0_{\ell}$  in  $L_{2\ell}$  of weight zero. This vector is invariant under SO(2) changing  $\theta$ ,

so it depends only on  $\phi$ ; in fact, it is a polynomial of degree  $\ell$  in  $\cos \phi$ :  $Y_{\ell}^{0} = P_{\ell}(\cos \phi)$ . Also orthogonality of the decomposition implies that

$$\int_{-1}^{1} P_k(z) P_n(z) dz = 0, \ k \neq n.$$

This means that  $P_n$  are the **Legendre polynomials**. Also

$$\Delta_{\rm sph} P_{\ell}(z) = \partial_z (1 - z^2) \partial_z P_{\ell}(z) = -\lambda_{\ell} P_{\ell}(z),$$

which shows (by looking at the leading term) that

$$\lambda_{\ell} = \ell(\ell+1), \ \ell \in \mathbb{Z}_{>0}$$

and the space of solutions of (38.1) with  $\lambda = \lambda_{\ell}$  is  $2\ell + 1$ -dimensional and is isomorphic to  $L_{2\ell}$  as an SO(3)-module.

Consider now the vector  $Y_{\ell}^m \in L_{2\ell}$  of any integer weight  $-\ell \leq m \leq \ell$ . We will be interested in these vectors up to scaling. We have

$$Y_{\ell}^{m}(\phi,\theta) = e^{im\theta} P_{\ell}^{m}(\cos\phi),$$

where  $P_{\ell}^m$  are certain functions. These functions are called **spherical harmonics**. Moreover, it follows from representation theory of SO(3) that  $Y_{\ell}^m$  are trigonometric polynomials which are even for even m and odd for odd m (check it!), so  $P_{\ell}^m(z)$  are polynomials in z when m is even and are of the form  $(1-z^2)^{1/2}$  times a polynomial in z when m is odd.

Let us calculate the functions  $P_{\ell}^{m}$ . Since they are eigenfunctions of the spherical Laplacian, we obtain that  $P_{\ell}^{m}$  satisfy the **Legendre differential equation** 

$$\partial_z (1-z^2)\partial_z P - \frac{m^2}{1-z^2} P + \ell(\ell+1)P = 0.$$

**Exercise 38.1.** Show that this equation has a unique up to scaling continuous solution on [-1,1] when  $-\ell \leq m \leq \ell$  and m is an integer, given by the formula

$$P_{\ell}^{m}(z) = (1-z^{2})^{m/2} \partial_{z}^{\ell+m} (1-z^{2})^{\ell}$$

These functions are called **associated Legendre polynomials** (even though they are not quite polynomials when m is odd).

Now we can return to equation (38.2). It now has the form

(38.3) 
$$f''(r) + \frac{2}{r}f'(r) + (\frac{2}{r} - \frac{\ell(\ell+1)}{r^2} + 2E)f(r) = 0.$$

To simplify this equation, write

$$f(r) = r^{\ell} e^{-\frac{r}{n}} h(\frac{2r}{n}),$$

where n can be chosen at our convenience. Then for h we get the equation

$$\rho h''(\rho) + (2\ell + 2 - \rho)h'(\rho) + (n - \ell - 1 + \frac{1}{4}(1 + 2En^2)\rho)h(\rho) = 0.$$

We see that the equation simplifies when  $n = \frac{1}{\sqrt{-2E}}$ , i.e.,  $E = -\frac{1}{2n^2}$ , so let us make this choice. Then we have

$$\rho h''(\rho) + (2\ell + 2 - \rho)h'(\rho) + (n - \ell - 1)h(\rho) = 0,$$

which is the **generalized Laguerre equation**. Moreover, we have  $||\psi||^2 < \infty$ , which translates to

(38.4) 
$$\int_0^\infty \rho^{2\ell+2} e^{-\rho} |h(\rho)|^2 d\rho < \infty$$

(the factor  $\rho^2$  comes from the Jacobian of the spherical coordinates). How do solutions of the generalized Laguerre equation behave at  $\rho = 0$ ? Let us look for a solution of the form  $\rho^s(1 + o(1))$ . The characteristic equation for s then has the form

$$s(s+2\ell+1) = 0,$$

which gives s=0 or  $s=-2\ell-1$ . Thus, for  $\ell \geq 1$  the solution  $\rho^{-2\ell-1}(1+o(1))$  does not satisfy (38.4), so we are left with a unique solution  $h_n(\rho)$  which is regular at  $\rho=0$  and  $h_n(0)=1$ . On the other hand, if  $\ell=0$ , the solution  $\rho^{-1}(1+o(1))$ , even though it satisfies (38.4), gives rise to a rotationally invariant function  $\psi \sim \frac{1}{r}$  as  $r \to 0$ , so we don't get  $H\psi = E\psi$ , but rather get  $H\psi = E\psi + C\delta_0$ , where  $\delta_0$  is the delta function concentrated at zero. So  $\psi$  does not really satisfy the stationary Schrödinger equation as a distribution and has to be discarded, leaving us, as before, with the unique solution  $h_n(\rho)$  such that  $h_n(0) = 1$ .

Using the power series method, we obtain

$$h_n(\rho) = \sum_{k=0}^{\infty} \frac{(1+\ell-n)...(k+\ell-n)}{(2\ell+2)...(2\ell+1+k)} \frac{\rho^k}{k!}.$$

It is easy to see that this series converges for all  $\rho$  and

$$\lim_{\rho \to +\infty} \frac{\log h_n(\rho)}{\rho} = 1$$

unless the series terminates, which happens iff  $n - \ell - 1$  is a non-negative integer. (To check the latter, show that the Taylor coefficients  $a_k$  of  $h_n$  are bounded below by  $\frac{1}{(k+N)!}$  for some N). So it fails (38.4)

unless  $n-\ell-1\in\mathbb{Z}_{>0}$ . In this case,

$$h_n(\rho) = \sum_{k=0}^{n-\ell-1} \frac{(1+\ell-n)...(k+\ell-n)}{(2\ell+2)...(2\ell+1+k)} \frac{\rho^k}{k!} = L_{n-\ell-1}^{2\ell+1}(\rho),$$

the  $n-\ell-1$ -th **generalized Laguerre polynomial** with parameter  $\alpha=2\ell+1$ , a polynomial of degree  $n-\ell-1$ . Namely, the generalized Laguerre polynomials  $L_N^{\alpha}$  are defined by the formula

$$L_N^{\alpha}(\rho) := \sum_{k=0}^N (-1)^N \frac{N...(N-k+1)}{(\alpha+1)...(\alpha+k)} \frac{\rho^k}{k!}.$$

Thus we obtain the following theorem.

**Theorem 38.2.** The bound states of the hydrogen atom, up to scaling, are

$$\psi_{n\ell m}(r,\phi,\theta) = r^{\ell} e^{-\frac{r}{n}} L_{n-\ell-1}^{2\ell+1}(\frac{2r}{n}) Y_{\ell}^{m}(\theta,\phi),$$

where  $Y_{\ell}^{m}(\theta, \phi) = e^{im\theta}P_{\ell}^{m}(\phi)$  are spherical harmonics, where  $n \in \mathbb{Z}_{>0}$ ,  $\ell$  an integer between 0 and n-1, and m is an integer between  $\ell$  and  $-\ell$ . The energy of the state  $\psi_{n\ell m}$  is  $E_n = -\frac{1}{2n^2}$ .

#### 39. The hydrogen atom, II

39.1. Quantum numbers. The number n in Theorem 38.2 is called the **principal quantum number**; it characterizes the energy of the state. The number  $\ell$  is called the **azimuthal quantum number**; it characterizes the eigenvalue of the spherical Laplacian  $\Delta_{\rm sph}$ , which has the physical interpretation as (minus) the **orbital angular momentum operator**  $\mathbf{L}^2 = L_x^2 + L_y^2 + L_z^2$ . Note that the operators  $iL_x$ ,  $iL_y$  and  $iL_z$  are just the generators of the Lie algebra  $\mathrm{Lie}(SO(3))$  acting on  $\mathbb{R}^3$ , i.e., we have

$$[L_x, L_y] = -iL_z, \ [L_y, L_z] = -iL_x, \ [L_z, L_x] = -iL_y.$$

Thus,  $\mathbf{L}^2$  is simply a Casimir of Lie(SO(3)). Namely, recall that the standard Casimir C acts on  $L_{2\ell}$  as  $\frac{2\ell(2\ell+2)}{4} = \ell(\ell+1)$ , so  $\mathbf{L}^2 = C$ .

Finally, m is called the **magnetic quantum number**, and it is the eigenvalue of  $L_z = -i\partial_{\theta}$  (in spherical coordinates).

Corollary 39.1. The space  $W_n$  of states with principal quantum number n has dimension  $n^2$ .

*Proof.* By Theorem 38.2, this dimension is 
$$\sum_{\ell=0}^{n-1} (2\ell+1) = n^2$$
.

In fact, this analysis applies not just to hydrogen but to other chemical elements whose nucleus has charge > 1, if we neglect interaction between electrons. Thus it can potentially be used to explain patterns of the periodic table.

39.2. Coulomb waves. We note, however, that  $\psi_{n\ell m}$  do not form a basis of  $L^2(\mathbb{R}^3)$ . Instead, they span (topologically) a proper closed subspace of  $L^2_0(\mathbb{R}^3)$  of  $L^2(\mathbb{R}^3)$  on which the operator H is bounded and negative definite. So if a smooth function  $\varphi$  on  $\mathbb{R}^3$  (say, with compact support away from the origin) satisfies  $(H\varphi, \varphi) \geq 0$  then  $\varphi \notin L^2_0(\mathbb{R}^3)$ . It is easy to construct such examples: let  $\varphi$  be a hat function and  $\varphi_s(\mathbf{r}) = \varphi(\mathbf{r} + s\mathbf{a})$ , where  $\mathbf{a}$  is any nonzero vector. We then have

$$(H\varphi_s, \varphi_s) = \frac{1}{2} \int_{\mathbb{R}^3} |\nabla \varphi(\mathbf{r})|^2 dV - \int_{\mathbb{R}^3} \frac{|\varphi(\mathbf{r})|^2}{|\mathbf{r} - s\mathbf{a}|} dV,$$

and we observe that the first term is positive and the second one goes to zero as  $s \to \infty$ , so for large s this expression is positive. This happens because besides bound states the hydrogen atom also has **continuous spectrum**  $[0,\infty)$  corresponding to free electrons which are not bound by the nucleus. This part of the spectrum can be computed similarly to the discrete (bound state) spectrum, except that the energy will take arbitrary **nonnegative** values. The corresponding wavefunctions are not normalizable (i.e., not in  $L^2$ ), and are given by similar formulas to

bound states but with imaginary n. Their continuous linear combinations satisfying appropriate boundary conditions are called **Coulomb** waves.

39.3. **Spin.** Also, the answer  $n^2$  for the number of states in the n-th energy level does not quite agree with the periodic table, which suggests it should rather be  $2n^2$ : the numbers of electrons at each level are 2, 8, 18, 32... This is because the Schrödinger model which we computed is not quite right, as it does not take into account an additional degree of freedom called **spin** (a sort of intrinsic angular momentum). Namely, it turns out that the space of states of an electron is not  $L^2(\mathbb{R}^3)$  but rather  $L^2(\mathbb{R}^3) \otimes \mathbb{C}^2$ , with the same Hamiltonian as before but the Lie algebra Lie(SO(3)) acting diagonally (where  $\mathbb{C}^2$  is the 2-dimensional irreducible representation of this Lie algebra). Thus the space of states of the n-th energy level taking spin into account is

$$V_n = (L_0 \oplus L_2 \oplus ... \oplus L_{2n-2}) \otimes L_1 = 2L_1 \oplus 2L_3 \oplus ... \oplus 2L_{2n-3} \oplus L_{2n-1}$$

and dim  $V_n = 2n^2$ . In other words, we have the additional **spin operator**, which is just the operator

$$S = \begin{pmatrix} \frac{1}{2} & 0\\ 0 & -\frac{1}{2} \end{pmatrix}$$

acting on the  $\mathbb{C}^2$  factor (in the standard basis  $\mathbf{e}_+, \mathbf{e}_-$ ). So the **total spin** (=angular momentum) of a state is m+s, where s is the eigenvalue of S, and we have the basic states  $\psi_{n\ell m+} = \psi_{n\ell m} \otimes \mathbf{e}_+$  and  $\psi_{n\ell m-} = \psi_{n\ell m} \otimes \mathbf{e}_-$  with spins  $m+\frac{1}{2}$  and  $m-\frac{1}{2}$  respectively.

Note also that  $V_n$  is **not** a representation of SO(3) but is only a representation of its double cover SU(2) where -Id acts by -1. However, this **anomaly** does not mean a violation of the SO(3) symmetry, since true quantum states are unit vectors in the Hilbert space **up to a phase factor**.

39.4. The Pauli exclusion principle. Suppose now that we have k electrons, each at the n-th energy level. If the electrons had been marked, the space of states for them would have been  $V_n^{\otimes k}$ . But in real life they are indistinguishable, so we need to mod out by permutations. So we might think the space of states is  $S^kV_n$ . However, as electrons are fermions, this answer turns out to be not correct: the correct answer is  $\wedge^k V_n$  rather than  $S^kV_n$ . In other words, when two identical electrons are switched, the corresponding vector changes sign. This is another example of a sign which does not violate symmetry since states are well defined only up to a phase factor.

In particular, this implies that if  $k > 2n^2$  then the space of states is zero, i.e., there cannot be more than  $2n^2$  electrons at the *n*-th energy level (the **Pauli exclusion principle**). This is exactly the kind of pattern we see in the periodic table.

| Group<br>Period | <b>→</b> 1 | 2        | 3         | 4         | 5         | 6         | 7         | 8         | 9         | 10        | 11        | 12        | 13        | 14        | 15        | 16        | 17        | 18        |
|-----------------|------------|----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|-----------|
| 1               | 1<br>H     |          |           |           |           |           |           |           |           |           |           |           |           |           |           |           |           | 2<br>He   |
| 2               | 3<br>Li    | 4<br>Be  |           |           |           |           |           |           |           |           |           |           | 5<br>B    | 6         | 7<br>N    | 8         | 9<br>F    | 10<br>Ne  |
| 3               | 11<br>Na   | 12<br>Mg |           |           |           |           |           |           |           |           |           |           | 13<br>Al  | 14<br>Si  | 15<br>P   | 16<br>S   | 17        | 18<br>Ar  |
| 4               | 19<br>K    | 20<br>Ca | 21<br>Sc  | 22<br>Ti  | 23<br>V   | 24<br>Cr  | 25<br>Mn  | 26<br>Fe  | 27<br>Co  | 28<br>Ni  | 29<br>Cu  | 30<br>Zn  | 31<br>Ga  | 32<br>Ge  | 33<br>As  | 34<br>Se  | 35<br>Br  | 36<br>Kr  |
| 5               | 37<br>Rb   | 38<br>Sr | 39<br>Y   | 40<br>Zr  | 41<br>Nb  | 42<br>Mo  | 43<br>Tc  | 44<br>Ru  | 45<br>Rh  | 46<br>Pd  | 47<br>Ag  | 48<br>Cd  | 49<br>In  | 50<br>Sn  | 51<br>Sb  | 52<br>Te  | 53<br>I   | 54<br>Xe  |
| 6               | 55<br>Cs   | 56<br>Ba | 71<br>Lu  | 72<br>Hf  | 73<br>Ta  | 74<br>W   | 75<br>Re  | 76<br>Os  | 77<br>Ir  | 78<br>Pt  | 79<br>Au  | 80<br>Hg  | 81<br>TI  | 82<br>Pb  | 83<br>Bi  | 84<br>Po  | 85<br>At  | 86<br>Rn  |
| 7               | 87<br>Fr   | 88<br>Ra | 103<br>Lr | 104<br>Rf | 105<br>Db | 106<br>Sg | 107<br>Bh | 108<br>Hs | 109<br>Mt | 110<br>Ds | 111<br>Rg | 112<br>Cn | 113<br>Nh | 114<br>FI | 115<br>Mc | 116<br>Lv | 117<br>Ts | 118<br>Og |
|                 |            | 4        | 57<br>La  | 58<br>Ce  | 59<br>Pr  | 60<br>Nd  | 61<br>Pm  | 62<br>Sm  | 63<br>Eu  | 64<br>Gd  | 65<br>Tb  | 66<br>DV  | 67<br>Ho  | 68<br>Er  | 69<br>Tm  | 70<br>Yb  |           |           |
|                 |            | 4        | 89        | 90<br>Th  | 91<br>Pa  | 92<br>U   | 93<br>Np  | 94<br>Pu  | 95<br>Am  | 96<br>Cm  | 97<br>Bk  | 98<br>Cf  | 99<br>Es  | 100<br>Fm | 101<br>Md | 102<br>No |           |           |

Image courtesy of <u>Double\_sharp</u> on <u>Wikipedia</u>. License: CC BY-SA. This content is excluded from our Creative Commons license. For more information, see <a href="https://ocw.mit.edu/help/faq-fair-use">https://ocw.mit.edu/help/faq-fair-use</a>.

Namely, the first energy level has two slots (the first row, or period, of the table), and the second one has 8 slots (the second period of the table). Further down interactions between electrons start to matter and the picture is modified (giving still 8 slots in the next period instead of 18), but we still see a similar pattern: 8 slots in the third period, 18 in periods 4,5, and 32 in periods 6,7. This arrangement is justified by the fact that the columns (groups) of elements, which have the same number of electrons at the last level, have similar chemical properties. For example, in the first column we have alkali metals (except hydrogen) and in the last one we have inert gases.

**Exercise 39.2.** Let  $\mathbf{r} = (x, y, z)$  and  $\mathbf{p} = (-i\partial_x, -i\partial_y, -i\partial_z)$  be the position and momentum operators in  $\mathbb{R}^3$ . Let  $\mathbf{L} = \mathbf{r} \times \mathbf{p}$  be the angular momentum operator (these are actually vectors Whose components are operators on functions in  $\mathbb{R}^3$ ). Let  $r = |\mathbf{r}| = \sqrt{x^2 + y^2 + z^2}$  (the operator of multiplication by this function) and  $H = \frac{1}{2}\mathbf{p}^2 + U(r) = -\frac{1}{2}\Delta + U(r)$  be a rotationally symmetric Schrödinger operator on  $\mathbb{R}^3$  with potential U(r) (smooth for r > 0).

- (i) Show that the components of  $i\mathbf{L}$  are vector fields that define the action of the Lie algebra  $\mathrm{Lie}(SO(3))$  on functions on  $\mathbb{R}^3$  induced by rotations. Deduce that  $[\mathbf{L}, \mathbf{p}^2] = 0$  (componentwise).
- (ii) Let  $\mathbf{A}_0 = \frac{1}{2}(\mathbf{p} \times \mathbf{L} \mathbf{L} \times \mathbf{p})$ . Show that  $[\mathbf{A}_0, \mathbf{p}^2] = 0$  (again componentwise).
- (iii) Let  $\mathbf{A} := \mathbf{A}_0 + \phi(r)\mathbf{r}$ . Show that there exists a function  $\phi$  such that  $[\mathbf{A}, H] = 0$  if and only if U is the Coulomb potential  $\frac{C}{r} + D$ , and

then  $\phi$  is uniquely determined, and compute  $\phi$ . The corresponding operator **A** is called the **quantum Laplace-Runge-Lenz vector**.<sup>20</sup>

- (iv) (Hidden symmetry of the hydrogen atom). By virtue of (iii), the components of  $\mathbf{A}$  act (by second order differential operators) on functions on  $\mathbb{R}^3$  commuting with H. In particular, they act on each  $W_n$  (note that in this problem we ignore spin). Use these components to define an action of  $\mathfrak{so}_4 = \mathfrak{so}_3 \oplus \mathfrak{so}_3 = \mathfrak{sl}_2 \oplus \mathfrak{sl}_2$  on  $W_n$  so that the geometric one (generated by the components of  $\mathbf{L}$ ) is the diagonal copy.
  - (v) Show that  $W_n = L_{n-1} \boxtimes L_{n-1}$  as a representation of  $\mathfrak{sl}_2 \oplus \mathfrak{sl}_2$ .
- (vi) Now include spin by tensoring with the representation  $\mathbb{C}^2$  of SU(2) and show that  $V_n = L_{n-1} \boxtimes L_{n-1} \boxtimes L_1$  as a representation of  $\mathfrak{so}_4 \oplus \mathfrak{su}_2 = \mathfrak{sl}_2 \oplus \mathfrak{sl}_2 \oplus \mathfrak{sl}_2$ . This representation is irreducible, which explains why the n-th energy level of H is degenerate, with multiplicity (i.e., dimension)  $2n^2$ .

**Exercise 39.3.** Let  $H = -\frac{1}{2}\Delta + \frac{1}{2}r^2$  be the Hamiltonian of the quantum harmonic oscillator in  $\mathbb{R}^n$ , where  $r = \sqrt{x_1^2 + ... + x_n^2}$ . Compute the eigenspaces of H in  $L^2(\mathbb{R}^n)$  as representations of SO(n) and find the eigenvalues of H with multiplicities and an orthogonal eigenbasis.

**Hint.** Show that the operator  $e^{r^2/2} \circ H \circ e^{-r^2/2}$  preserves the space of polynomials  $\mathbb{C}[x_1,...,x_n]$ , and find an eigenbasis  $P_{i_1i_2...i_n}$  for this operator in this space (these should express via Hermite polynomials; use that  $H = H_1 + ... + H_n$  is the sum of operators  $H_i$  depending only on  $x_i$ ). This will give orthogonal eigenfunctions

$$\psi_{i_1\dots i_n}(\mathbf{r}) = P_{i_1\dots i_n}(\mathbf{r})e^{-r^2/2}$$

in  $L^2(\mathbb{R}^n)$ . Using properties of Hermite polynomials, conclude that these are complete. Then use Exercise 31.11.

<sup>&</sup>lt;sup>20</sup>In the classical mechanics setting, the existence of this conservation law is the reason why orbits for Coulomb potential are periodic (Kepler's law), while this is not so for other rotationally invariant potentials, except harmonic oscillator. It was discovered many times over the last 300 years. This is one of the most basic examples of "hidden symmetry".

#### 40. Forms of semisimple Lie algebras over an arbitrary field

40.1. Automorphisms of semisimple Lie algebras. We showed in Corollary 17.10 that for a complex semisimple  $\mathfrak{g}$ , the group  $\operatorname{Aut}(\mathfrak{g})$  is a Lie group with Lie algebra  $\mathfrak{g}$ . We also showed in Theorem 20.10 that its connected component of the identity  $\operatorname{Aut}(\mathfrak{g})^{\circ}$  acts transitively on the set of Cartan subalgebras in  $\mathfrak{g}$ . This group is called the **adjoint group** attached to  $\mathfrak{g}$ , and we will denote it by  $G_{\operatorname{ad}}$ .

Let  $\mathfrak{h} \subset \mathfrak{g}$  be a Cartan subalgebra, and  $H \subset G_{\mathrm{ad}}$  be the corresponding connected Lie subgroup. This subgroup can be viewed as the group of linear operators  $\mathfrak{g} \to \mathfrak{g}$  which act by 1 on  $\mathfrak{h}$  and by  $e^{\alpha(x)}$ ,  $x \in \mathfrak{h}$ , on each  $\mathfrak{g}_{\alpha}$ . Thus the exponential map  $\mathfrak{h} \to H$  defines an isomorphism  $\mathfrak{h}/2\pi i P^{\vee} \cong H$ . The group H is called the **maximal torus** of  $G_{\mathrm{ad}}$  corresponding to  $\mathfrak{h}$ .

**Proposition 40.1.** The normalizer N(H) of H in  $G_{ad}$  coincides with the stabilizer of  $\mathfrak{h}$  and contains H as a normal subgroup, so that N(H)/H is naturally isomorphic to the Weyl group W.

*Proof.* First note that since  $SL_2(\mathbb{C})$  is simply connected, for any simple root  $\alpha_i$  we have a homomorphism  $\eta_i: SL_2(\mathbb{C}) \to G_{\mathrm{ad}}$  which identifies  $\mathrm{Lie}(SL_2(\mathbb{C}))$  with the  $\mathfrak{sl}_2$ -subalgebra of  $\mathfrak{g}$  corresponding to this simple root. Let

$$(40.1) S_i := \eta_i \left( \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix} \right).$$

Given  $w \in W$ , pick a decomposition  $w = s_{i_1}...s_{i_n}$ , and let  $\widetilde{w} := S_{i_1}...S_{i_n} \in G_{\mathrm{ad}}$ . Note that  $\widetilde{w}$  acts on  $\mathfrak{h}$  by w. So if  $w = w_1w_2 \in W$  then  $\widetilde{w} = \widetilde{w}_1\widetilde{w}_2h$ , where h preserves the root decomposition and acts trivially on  $\mathfrak{h}$ . Thus if  $h|_{\mathfrak{g}_{\alpha_j}} = \exp(b_j)$  then  $h = \exp(\sum_j b_j \omega_j^{\vee}) \in H$ . So the elements  $\widetilde{w}$  and H generate a subgroup  $N \subset N(H)$  of  $G_{\mathrm{ad}}$  such that  $N/H \cong W$ .

It remains to show that N(H) = N. To this end, for  $x \in N(H)$ , let  $\alpha'_i = x(\alpha_i)$ . Then  $\alpha'_i$  form a system of simple roots, so there exists  $w \in W$  such that  $w(\alpha'_i) = \alpha_{p(i)}$ , where p is some permutation. Then  $\widetilde{w}x(\alpha_i) = \alpha_{p(i)}$ . So  $\widetilde{w}x$  defines a Dynkin diagram automorphism of  $\mathfrak{g}$ . Since this automorphism is defined by an element of  $G_{\rm ad}$ , it stabilizes all fundamental representations, so  $p = \mathrm{id}$ , hence  $\widetilde{w}x \in H$ , as claimed.  $\square$ 

In particular, we see that H is a maximal commutative subgroup of  $G_{\text{ad}}$ , hence the terminology "maximal torus".

<sup>&</sup>lt;sup>21</sup>The element  $\widetilde{w}$  in general depends on the decomposition of w as a product of simple reflections. One can show it does not if we take only reduced decompositions, but we will not need this.

**Remark 40.2.** Note that in general N(H) is **not** isomorphic to  $W \ltimes H$ : it can be a non-split extension of W by H.

Another obvious subgroup of  $\operatorname{Aut}(\mathfrak{g})$  is the finite group  $\operatorname{Aut}(D)$  of automorphisms of the Dynkin diagram of  $\mathfrak{g}$ , which just permutes the generators  $e_i, f_i, h_i$  in the Serre presentation. Thus we have a natural homomorphism

$$\xi: \operatorname{Aut}(D) \ltimes G_{\operatorname{ad}} \to \operatorname{Aut}(\mathfrak{g}),$$

which is the identity map on the connected components of 1. This homomorphism is clearly injective, since the center of  $G_{ad}$  is trivial and any nontrivial element of  $\operatorname{Aut}(D)$  nontrivially permutes fundamental representations of  $\mathfrak{g}$ .

# **Proposition 40.3.** $\xi$ is an isomorphism.

*Proof.* Our job is to show that  $\xi$  is surjective, i.e. for  $a \in \operatorname{Aut}(\mathfrak{g})$  show that  $a \in \operatorname{Im} \xi$ . By Theorem 20.10, we may assume without loss of generality that a preserves a Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}$  (indeed, this can be arranged by multiplying by an element of  $G_{\operatorname{ad}}$ , since  $G_{\operatorname{ad}}$  acts transitively on Cartan subalgebras of  $\mathfrak{g}$ ). Then by multiplying by an element of  $\operatorname{Aut}(D) \cdot N(H)$  we can make sure that a acts trivially on  $\mathfrak{h}$  and  $\mathfrak{g}_{\alpha_i}$ . Then a = 1, which implies the proposition.

40.2. Forms of semisimple Lie algebras. We have classified semisimple Lie algebras over  $\mathbb{C}$ , but what about other fields (say of characteristic zero), notably  $\mathbb{R}$  (the case relevant to the theory of Lie groups)?

To address this question, note that the Serre presentation of a semisimple Lie algebra is defined over  $\mathbb{Q}$ , so it defines a Lie algebra of the same dimension over any such field, by imposing the same generators and relations. Such a Lie algebra is called **split**. So for example, over an algebraically closed field of characteristic zero, any semisimple Lie algebra is automatically split.

Now let  $\mathfrak{g}$  be a semisimple Lie algebra over a field K of characteristic zero which splits over a Galois extension L of K, i.e.,  $\mathfrak{g} \otimes_K L = \mathfrak{g}_L$  is split (corresponds to a Dynkin diagram via Serre's presentation). Can we classify such  $\mathfrak{g}$ ?

To this end, let  $\Gamma = \operatorname{Gal}(L/K)$  be the Galois group of L over K and observe that we can recover  $\mathfrak{g}$  as the subalgebra of invariants  $\mathfrak{g}_L^{\Gamma}$ . So  $\mathfrak{g}$  is determined by the action of  $\Gamma$  on the split semisimple Lie algebra  $\mathfrak{g}_L$ . Note that this action is **twisted-linear**, i.e., additive and  $g(\lambda x) = g(\lambda)g(x)$  for  $x \in \mathfrak{g}_L$ ,  $\lambda \in L$ ,  $g \in \Gamma$ . The simplest example of such an action is the action  $\rho_0(g)$  which preserves all the generators  $e_i, f_i, h_i$  and just acts on the scalars, which corresponds to the split form of  $\mathfrak{g}$ .

So any twisted-linear action  $\rho$  can be written as

$$\rho(g) = \eta(g)\rho_0(g)$$

for some map

$$\eta:\Gamma\to\operatorname{Aut}(\mathfrak{g}_L).$$

In order that  $\rho$  be a homomorphism, we need

$$\eta(gh)\rho_0(gh) = \eta(g)\rho_0(g)\eta(h)\rho_0(h),$$

which is equivalent to

$$\eta(qh) = \eta(q) \cdot q(\eta(h)),$$

where for  $a \in \operatorname{Aut}(\mathfrak{g}_L)$ ,  $g(a) := \rho_0(g)a\rho_0(g)^{-1}$ . In other words,  $\eta$  is a 1-cocycle. We will denote the Lie algebra attached to such cocycle  $\eta$  by  $\mathfrak{g}_{\eta}$ .

It remains to determine when  $\mathfrak{g}_{\eta_1}$  is isomorphic to  $\mathfrak{g}_{\eta_2}$ . This will happen exactly when the corresponding representations  $\rho_1$  and  $\rho_2$  are isomorphic, i.e., there is  $a \in \operatorname{Aut}(\mathfrak{g}_L)$  such that  $\rho_1(g)a = a\rho_2(g)$ , i.e.,

$$\eta_1(g)\rho_0(g)a = a\eta_2(g)\rho_0(g),$$

or

$$\eta_1(g) = a\eta_2(g)g(a)^{-1}.$$

Two 1-cocycles related in this way are called **cohomologous** (obviously, an equivalence relation), and the set of equivalence classes of cohomologous cocycles is called the **first Galois cohomology** of  $\Gamma$  with coefficients in  $\operatorname{Aut}(\mathfrak{g}_L)$  and denoted by  $H^1(\Gamma, \operatorname{Aut}(\mathfrak{g}_L))$ . Note that this is cohomology with coefficients in a nonabelian group, so it is just a set and not a group.

So we obtain

**Proposition 40.4.** Semisimple Lie algebras  $\mathfrak{g}$  over K which split over a Galois extension L of K are classified by the first Galois cohomology  $H^1(\Gamma, \operatorname{Aut}(\mathfrak{g}_L))$ .

Remark 40.5. There is nothing special about semisimplicity or about Lie algebras here – this works for any kind of linear algebraic structures, such as associative algebras, algebraic varieties, schemes, etc.

40.3. Real forms of a semisimple Lie algebra. Let us now make this classification more concrete in the case  $K = \mathbb{R}$ ,  $L = \mathbb{C}$ , which is relevant to classification of real semisimple Lie groups. In this case,  $\Gamma = \mathbb{Z}/2$  generated by complex conjugation  $s \mapsto \overline{s}$  and, as we have shown,  $\operatorname{Aut}(\mathfrak{g}_L) = \operatorname{Aut}(D) \ltimes G_{\operatorname{ad}}$ , where D is the Dynkin diagram of  $\mathfrak{g}$  and  $G_{\operatorname{ad}}$  is the corresponding connected adjoint complex Lie group. Also since we always have  $\eta(1) = 1$ , the cocycle  $\eta$  is determined by

the element  $s = \eta(-1) \in \operatorname{Aut}(D) \ltimes G_{\operatorname{ad}}$ . Moreover, s must satisfy the cocycle condition

$$s\overline{s} = 1$$

and the corresponding real Lie algebra, up to isomorphism, depends only on the cohomology class of s, which is the equivalence class modulo transformations  $s\mapsto as\overline{a}^{-1}$ . We thus obtain the following theorem.

**Theorem 40.6.** Real semisimple Lie algebras whose complexification is  $\mathfrak{g}$  (i.e., **real forms** of  $\mathfrak{g}$ ) are classified by  $s \in \operatorname{Aut}(D) \ltimes G_{\operatorname{ad}}$  such that  $s\overline{s} = 1$  modulo equivalence  $s \mapsto as\overline{a}^{-1}$ ,  $a \in \operatorname{Aut}(\mathfrak{g})$ , where complex conjugation acts trivially on  $\operatorname{Aut}(D)$ .

We denote the real form of  $\mathfrak{g}$  corresponding to s by  $\mathfrak{g}_{(s)}$ . Namely,  $\mathfrak{g}_{(s)} = \{x \in \mathfrak{g} : \overline{x} = s(x)\}$ . For example,  $\mathfrak{g}_{(1)}$  is the split form, consisting of real  $x \in \mathfrak{g}$ , i.e., such that  $\overline{x} = x$ .

Alternatively, one may define the **antilinear involution**  $\sigma_s(x) = \overline{s(x)}$ , and  $\mathfrak{g}_{(s)}$  is the set of fixed points of  $\sigma_s$  in  $\mathfrak{g}$ .

In particular, such s defines an element  $s_0 \in \operatorname{Aut}(D)$  such that  $s_0^2 = 1$ . Note that the conjugacy class of  $s_0$  is invariant under equivalences. The element  $s_0$  permutes connected components of D, preserving some and matching others into pairs. Thus every semisimple real Lie algebra is a direct sum of simple ones, and each simple one either has a connected Dynkin diagram D (i.e., the complexified Lie algebra  $\mathfrak{g}$  is still simple) or consists of two identical components (i.e., the complexified Lie algebra is  $\mathfrak{g} = \mathfrak{a} \oplus \mathfrak{a}$  for some simple complex  $\mathfrak{a}$ ). In the latter case  $s = (g, \overline{g}^{-1})s_0$  where  $s_0$  is the transposition and  $g \in \operatorname{Aut}(\mathfrak{a})$ , so s is cohomologous to  $s_0$  by taking a = (g, 1). Thus in this case  $\mathfrak{g}_{(s)} = \mathfrak{g}_{(s_0)} = \mathfrak{a}$ , a complex simple Lie algebra regarded as a real Lie algebra.

It remains to consider the case when D is connected, i.e.,  $\mathfrak{g}$  is simple.

**Definition 40.7.** (i) A real form  $\mathfrak{g}_{(s)}$  of a complex simple Lie algebra  $\mathfrak{g}$  is said to be **inner** to  $\mathfrak{g}_{(s')}$  if s' = gs up to equivalence, where  $g \in G_{\mathrm{ad}}$  (i.e., s and s' differ by an inner automorphism). The **inner class** of  $\mathfrak{g}_{(s)}$  is the collection of all real forms inner to  $\mathfrak{g}_{(s)}$ . In particular, an **inner form** is a form inner to the split form.

(ii)  $\mathfrak{g}_{(s)}$  is called **quasi-split** if  $s = s_0 \in \operatorname{Aut}(D)$  (modulo equivalence).

So in particular any real form is inner to a unique quasi-split form, and a real form that is both inner and quasi-split is split.

Exercise 40.8. Let  $\mathfrak{g}_{\mathbb{R}}$  be a real semisimple Lie algebra and  $\mathfrak{h}_{\mathbb{R}} \subset \mathfrak{g}_{\mathbb{R}}$  a Cartan subalgebra (the centralizer of a regular semisimple element

- of  $\mathfrak{g}_{\mathbb{R}}$ ). Let  $\mathfrak{h} \subset \mathfrak{g}$  be their complexifications, and  $H \subset G_{\mathrm{ad}}$  the corresponding complex Lie groups. Let  $\mathbf{K}$  be the kernel of the natural map of Galois cohomology sets  $H^1(\mathbb{Z}/2, N(H)) \to H^1(\mathbb{Z}/2, G_{\mathrm{ad}})$  (i.e., the preimage of the unit element), where  $\mathbb{Z}/2$  acts on  $G_{\mathrm{ad}}$  by complex conjugation associated to the real form  $\mathfrak{g}_{\mathbb{R}}$  of  $\mathfrak{g}$ .
- (i) Show that conjugacy classes of Cartan subalgebras in  $\mathfrak{g}_{\mathbb{R}}$  are bijectively labeled by elements of K, with the unit element corresponding to  $\mathfrak{h}_{\mathbb{R}}$ .
  - (ii) Show that K is a finite set.<sup>22</sup>

 $<sup>^{22}</sup>$ For classical Lie algebras the set **K** will be computed explicitly in Exercise 44.18. The explicit answer is known for exceptional Lie algebras as well, but we will not discuss it here.

### 41. Classification of real forms of semisimple Lie algebras

41.1. The compact real form. An important example of a real form of simple complex Lie algebra  $\mathfrak g$  is the compact real form. It is determined by the automorphism  $\tau$  (called the Cartan involution) defined by the formula

$$\tau(h_j) = -h_j, \ \tau(e_j) = -f_j, \ \tau(f_j) = -e_j.$$

Let us denote this real form  $\mathfrak{g}_{(\tau)}$  by  $\mathfrak{g}^c$ .

**Proposition 41.1.** The Killing form of  $\mathfrak{g}^c$  is negative definite.

*Proof.* We have an orthogonal decomposition

$$\mathfrak{g}^c = (\mathfrak{h} \cap \mathfrak{g}^c) \oplus \bigoplus_{\alpha \in R_+} (\mathfrak{g}_\alpha \oplus \mathfrak{g}_{-\alpha}) \cap \mathfrak{g}^c.$$

Moreover, the Killing form is clearly negative definite on  $\mathfrak{h} \cap \mathfrak{g}^c$ , since the inner product on the coroot lattice is positive definite, and  $\{i\alpha_j^{\vee}\}$  is a basis of  $\mathfrak{h} \cap \mathfrak{g}^c$ . So it suffices to show that the Killing form is negative definite on  $(\mathfrak{g}_{\alpha} \cap \mathfrak{g}_{-\alpha}) \cap \mathfrak{g}^c$  for any  $\alpha \in R_+$ .

First consider the case  $\mathfrak{g} = \mathfrak{sl}_2$ . Then  $\mathfrak{g}^c$  is spanned by the Pauli matrices ih, e - f, i(e + f), so  $\mathfrak{g}^c = \mathfrak{su}(2)$ . It follows that the trace form of any finite dimensional representation of  $\mathfrak{g}^c$  is negative definite.

Thus for a general  $\mathfrak{g}$ , the elements  $S_i$  given by (40.1) preserve  $\mathfrak{g}^c$ ; this follows since the matrix  $S := \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$  belongs to SU(2), and  $\text{Lie}(SU(2)_i) \subset \mathfrak{g}^c$ . It follows that for any  $w \in W$  the element  $\widetilde{w}$  preserves  $\mathfrak{g}^c$ . Thus the restriction of the Killing form of  $\mathfrak{g}^c$  to  $\mathfrak{g}^c \cap (\mathfrak{sl}_2)_\alpha$  is negative definite for any root  $\alpha$  (since it is so for simple roots, as follows from the case of  $\mathfrak{sl}_2$ ). This implies the statement.

Now consider the group  $\operatorname{Aut}(\mathfrak{g}^c)$ . Since the Killing form on  $\mathfrak{g}^c$  is negative definite, it is a closed subgroup in the orthogonal group  $O(\mathfrak{g}^c)$ , hence is compact. Moreover, it is a Lie group with Lie algebra  $\mathfrak{g}^c$ . Thus we obtain

Corollary 41.2. Let  $G_{\text{ad}}^c = \text{Aut}(\mathfrak{g}^c)^{\circ}$ . Then  $G_{\text{ad}}^c$  is a connected compact Lie group with Lie algebra  $\mathfrak{g}^c$ .

In particular, this gives a new proof that representations of a finite dimensional semisimple Lie algebra are completely reducible (by using Weyl's unitary trick, see Subsection 35.1).

**Exercise 41.3.** (i) Show that if  $\mathfrak{g} = \mathfrak{sl}_n$  then  $G_{\mathrm{ad}}^c = PSU(n) = SU(n)/\mu_n$ , where  $\mu_n$  is the group of roots of unity of order n.

- (ii) Show that if  $\mathfrak{g} = \mathfrak{so}_n$  then  $G_{\mathrm{ad}}^c = SO(n)$  for odd n and  $SO(n)/\pm 1$  for even n.
- (iii) Show that if  $\mathfrak{g} = \mathfrak{sp}_{2n}$  then  $G_{\mathrm{ad}}^c = U(n, \mathbb{H})/\pm 1$ , where  $U(n, \mathbb{H})$  is the quaternionic unitary group  $Sp_{2n}(\mathbb{C}) \cap U(2n)$  (see Exercise 6.15).
- **Exercise 41.4.** (i) Compute the signature of the Killing form of the split form  $\mathfrak{g}^{\text{spl}}$  of a complex simple Lie algebra  $\mathfrak{g}$  in terms of its dimension and rank, and show that the compact form is never split.
- (ii) Show that the compact form is inner to the quasi-split form defined by the flip of the Dynkin diagram corresponding to taking the dual representation (i.e., induced by  $-w_0$ ), but is never quasi-split itself (show that the quasi-split form contains nonzero nilpotent elements). For which simple Lie algebras is the compact form inner?
- 41.2. Other examples of real forms. So let us list real forms of simple Lie algebras that we know so far.
- 1. Type  $A_{n-1}$ . We have the split form  $\mathfrak{sl}_n(\mathbb{R})$ , the compact form  $\mathfrak{su}(n)$ , and also for n > 2 the quasi-split form associated to the automorphism  $s(A) = -JA^TJ^{-1}$ , where  $J_{ij} = (-1)^i\delta_{i,n+1-j}$  (this automorphism sends  $e_i$ ,  $f_i$ ,  $h_i$  to  $e_{n+1-i}$ ,  $f_{n+1-i}$ ,  $h_{n+1-i}$ ). So the corresponding real Lie algebra is the Lie algebra of traceless matrices preserving the hermitian or skew-hermitian form defined by the matrix J, which has signature (p,p) if n=2p and (p+1,p) or (p,p+1) if n=2p+1. Thus in the first case we have  $\mathfrak{su}(p,p)$  and in the second case we have  $\mathfrak{su}(p+1,p)$ . Note that for n=2 we have  $\mathfrak{su}(1,1)=\mathfrak{sl}_2(\mathbb{R})$ , so in this special case this form is not new. We also observe that for  $n\geq 4$  there are other forms, e.g.  $\mathfrak{su}(n-p,p)$  with  $1\leq p\leq \frac{n}{2}-1$ .
- 2. Type  $B_n$ . We have the split form  $\mathfrak{so}(n+1,n)$ , the compact form  $\mathfrak{so}(2n+1)$ . The Dynkin diagram has no nontrivial automorphisms, so there are no non-split quasi-split forms. In particular, since  $A_1 = B_1$ , we have  $\mathfrak{so}(3) = \mathfrak{su}(2)$  and  $\mathfrak{so}(2,1) = \mathfrak{su}(1,1)$ .
- 3. Type  $C_n$ . We have the split form  $\mathfrak{sp}_{2n}(\mathbb{R})$  and compact form  $\mathfrak{u}(n,\mathbb{H})$ . The Dynkin diagram has no nontrivial automorphisms, so there are no non-split quasi-split forms. The equality  $B_2 = C_2$  implies that  $\mathfrak{so}(3,2) = \mathfrak{sp}_4(\mathbb{R})$  and  $\mathfrak{so}(5) = \mathfrak{u}(2,\mathbb{H})$ .
- 4. Type  $D_n$ . We have the split form  $\mathfrak{so}(n,n)$ , the compact form  $\mathfrak{so}(2n)$ . Moreover, in this case we have a unique nontrivial involution of the Dynkin diagram. More precisely, this is true for  $n \neq 4$ , while for n = 4 we have  $\operatorname{Aut}(D) = S_3$ , but there is still a unique nontrivial involution up to conjugation. So we also have a non-split quasisplit form. To compute it, recall that the split form is defined by the equation  $A = -JA^TJ^{-1}$  where  $J_{ij} = \delta_{i,2n+1-j}$ . The quasi-split form is obtained by replacing J by J' = gJ, where g permutes  $e_n$

and  $e_{n+1}$  (this is the automorphism that switches  $\alpha_{n-1}$  and  $\alpha_n$  while keeping other simple roots fixed). The signature of the form defined by J' is (n+1, n-1), so we get that the non-split quasi-split form is  $\mathfrak{so}(n+1, n-1)$ . In particular, since  $D_2 = A_1 + A_1$ , for n=2 we get

$$\mathfrak{so}(4) = \mathfrak{su}(2) \oplus \mathfrak{su}(2), \ \mathfrak{so}(2,2) = \mathfrak{su}(1,1) \oplus \mathfrak{su}(1,1), \ \mathfrak{so}(3,1) = \mathfrak{sl}_2(\mathbb{C})$$

(the Lie algebra of the Lorentz group of special relativity). Also, since  $D_3 = A_3$ , for n = 3 we get  $\mathfrak{so}(6) = \mathfrak{su}(4)$ ,  $\mathfrak{so}(3,3) = \mathfrak{sl}_4(\mathbb{R})$ , and  $\mathfrak{so}(4,2) = \mathfrak{su}(2,2)$ .

- 5. Type  $G_2$ . We have the split and compact forms  $G_2(\mathbb{R}), G_2^c$ .
- 6. Type  $F_4$ . We have the split and compact forms  $F_4(\mathbb{R}), F_4^c$ .
- 7. Type  $E_6$ . We have the split and compact forms  $E_6(\mathbb{R})$ ,  $E_6^c$  and the quasi-split form  $E_6^{qs}$  attached to the non-trivial automorphism.
  - 8. Type  $E_7$ . We have the split and compact forms  $E_7(\mathbb{R}), E_7^c$ .
  - 9. Type  $E_8$ . We have the split and compact forms  $E_8(\mathbb{R}), E_8^c$ .
- 41.3. Classification of real forms. However, we are not done with the classification of real forms yet, as we still need to find all real forms and show there are no others. To this end, consider a complex simple Lie algebra  $\mathfrak{g} = \mathfrak{g}^c \otimes_{\mathbb{R}} \mathbb{C}$ . We have the compact antilinear involution  $\omega = \sigma_{\tau}$  of  $\mathfrak{g}$  whose set of fixed points is  $\mathfrak{g}^c$ . Another real structure on  $\mathfrak{g}$  is then defined by the antilinear involution  $\sigma = \omega \circ g$ , where  $g \in \operatorname{Aut}(\mathfrak{g})$  is such that  $\omega(g)g = 1$ . But it is easy to see that

$$\omega(g) = (g^{\dagger})^{-1},$$

where  $x^{\dagger}$  is the adjoint to  $x \in \operatorname{End}(\mathfrak{g})$  under the negative definite Hermitian form  $(X,Y) = \operatorname{Tr}(\operatorname{ad}X\operatorname{ad}\omega(Y))$  (the Hermitian extension of the Killing form on  $\mathfrak{g}^c$  to  $\mathfrak{g}$ ). It follows that the operator g is self-adjoint. Thus it is diagonalizable with real eigenvalues, and we have a decomposition

$$\mathfrak{g}=\oplus_{\gamma\in\mathbb{R}}\mathfrak{g}(\gamma),$$

where  $\mathfrak{g}(\gamma)$  is the  $\gamma$ -eigenspace of g, such that  $[\mathfrak{g}(\beta),\mathfrak{g}(\gamma)] = \mathfrak{g}(\beta\gamma)$ . Now consider the operator  $|g|^t$  for any  $t \in \mathbb{R}$ . It acts on  $\mathfrak{g}(\gamma)$  by  $|\gamma|^t$ , so  $|g|^t = \exp(t \log |g|) \in G_{\mathrm{ad}}$  is a 1-parameter subgroup. Now define  $\theta := g|g|^{-1}$ . We have  $\theta \circ \omega = \omega \circ \theta$  and  $\theta^2 = 1$ . Also g and  $\theta$  define the same real structure since  $\theta = |g|^{-1/2}g\omega(|g|^{1/2})$ . This shows that without loss of generality we may assume that  $g = \theta$  with  $\theta \circ \omega = \omega \circ \theta$  (i.e.,  $\theta \in \mathrm{Aut}(\mathfrak{g}^c)$ ) and  $\theta^2 = 1$ .

<sup>&</sup>lt;sup>23</sup>The advantage of passing from g to  $\theta$  is that the equation  $\theta^2 = 1$  is much easier to solve than  $g\omega(g) = 1$ , as it just means that we have a decomposition of  $\mathfrak{g}$  into the +1- and -1-eigenspaces of  $\theta$ .

Moreover, another such element  $\theta'$  defines the same real form if and only if  $\theta' = x\theta\omega(x)^{-1}$  for some  $x \in \text{Aut}(\mathfrak{g})$ . So we get

$$x\theta\omega(x)^{-1} = \omega(x)\theta x^{-1},$$

so setting  $z := \omega(x)^{-1}x$ , we get  $\omega(z) = z^{-1}$ ,  $\theta z = z^{-1}\theta$ . Note that  $z = x^{\dagger}x$  is positive definite. So setting  $y = xz^{-1/2}$ , we have

$$\omega(y) = \omega(x)z^{1/2} = xz^{-1/2} = y$$

i.e.,  $y \in Aut(\mathfrak{g}^c)$  and

$$\theta' = x\theta\omega(x)^{-1} = x\theta zx^{-1} = xz^{-1/2}\theta z^{1/2}x^{-1} = y\theta y^{-1}.$$

Thus we obtain

**Theorem 41.5.** Real forms of  $\mathfrak{g}$  are in bijection with conjugacy classes of involutions  $\theta \in \operatorname{Aut}(\mathfrak{g}^c)$ , via  $\theta \mapsto \omega_{\theta} := \theta \circ \omega = \omega \circ \theta$ .

Theorem 41.5 provides a different classification of real forms from the one given in Subsection 40.3, obtained by "counting" from the compact form rather than the split form (as we did in Subsection 40.3). We denote the real form of  $\mathfrak{g}$  assigned in Theorem 41.5 to an involution  $\theta: \mathfrak{g} \to \mathfrak{g}$  by  $\mathfrak{g}_{\theta}$ . For example,  $\mathfrak{g}_1 = \mathfrak{g}^c = \mathfrak{g}_{(\tau)}$ .

Thus we have a canonical (up to automorphisms of  $\mathfrak{g}^c$ ) decomposition  $\mathfrak{g} = \mathfrak{k} \oplus \mathfrak{p}$ , into the eigenspaces of  $\theta$  with eigenvalues 1 and -1, such that  $\mathfrak{k}$  is a Lie subalgebra,  $\mathfrak{p}$  is a module over  $\mathfrak{k}$  and  $[\mathfrak{p},\mathfrak{p}] \subset \mathfrak{k}$ . We also have the corresponding decomposition for the underlying real Lie algebra  $\mathfrak{g}^c = \mathfrak{k}^c \oplus \mathfrak{p}^c$ . Moreover, the corresponding real form  $\mathfrak{g}_\theta$  is just  $\mathfrak{g}_\theta = \mathfrak{k}^c \oplus \mathfrak{p}_\theta$ , where  $\mathfrak{p}_\theta := i\mathfrak{p}^c$ .

**Exercise 41.6.** Show that  $\mathfrak{k}$  is a reductive Lie algebra. Does it have to be semisimple?

**Proposition 41.7.** There exists a Cartan subalgebra  $\mathfrak{h}$  in  $\mathfrak{g}$  invariant under  $\theta$ , such that  $\mathfrak{h} \cap \mathfrak{k}$  is a Cartan subalgebra in  $\mathfrak{k}$ .

*Proof.* Take a generic  $t \in \mathfrak{k}^c$ ; as  $\mathfrak{k}$  is reductive, it is regular semisimple. Let  $\mathfrak{h}^c_+$  be the centralizer of t in  $\mathfrak{k}^c$ . Then  $\mathfrak{h}_+ := \mathfrak{h}^c_+ \otimes_{\mathbb{R}} \mathbb{C} \subset \mathfrak{k}$  is a Cartan subalgebra. Let  $\mathfrak{h}^c_-$  be a maximal subspace of  $\mathfrak{p}^c$  for the property that  $\mathfrak{h}^c := \mathfrak{h}^c_+ \oplus \mathfrak{h}^c_-$  is a commutative Lie subalgebra of  $\mathfrak{g}^c$ .

We claim that  $\mathfrak{h} := \mathfrak{h}^c \otimes_{\mathbb{R}} \mathbb{C}$  is a Cartan subalgebra in  $\mathfrak{g}$ . Indeed, it obviously consists of semisimple elements (as all elements in  $\mathfrak{g}^c$  are semisimple, being anti-hermitian operators on  $\mathfrak{g}^c$ ). Now, if  $z \in \mathfrak{g}$  commutes with  $\mathfrak{h}$  then  $z = z_+ + z_-$ ,  $z_+ \in \mathfrak{k}$  and  $z_- \in \mathfrak{p}$ , and both  $z_+, z_-$  commute with  $\mathfrak{h}$ . Thus  $z_+ \in \mathfrak{h}_+$  and  $z_- = x + iy$ , where  $x, y \in \mathfrak{p}^c$  and both commute with  $\mathfrak{h}$ . Hence  $x, y \in \mathfrak{h}^c_-$  by the definition of  $\mathfrak{h}^c_-$ . Thus  $z \in \mathfrak{h}$ , as claimed. It is clear that  $\mathfrak{h}$  is  $\theta$ -stable, so the proposition is proved.

Thus we have a decomposition  $\mathfrak{h} = \mathfrak{h}_+ \oplus \mathfrak{h}_-$ , and  $\theta$  acts by 1 on  $\mathfrak{h}_+$  and by -1 on  $\mathfrak{h}_-$ .

**Lemma 41.8.** The space  $\mathfrak{h}_{-}$  does not contain any coroots of  $\mathfrak{g}$ .

Proof. Suppose that  $\alpha^{\vee} \in \mathfrak{h}_{-}$  is a coroot. Thus  $\theta(\alpha^{\vee}) = -\alpha^{\vee}$ , so  $\theta(e_{\alpha}) = e_{-\alpha}$  and  $\theta(e_{-\alpha}) = e_{\alpha}$  for some nonzero  $e_{\pm \alpha} \in \mathfrak{g}_{\pm \alpha}$ . Let  $x = e_{\alpha} + e_{-\alpha}$ . We have  $\theta(x) = x$ , so  $x \in \mathfrak{k}$ . On the other hand,  $x \notin \mathfrak{h}_{+}$  (as x is orthogonal to  $\mathfrak{h}_{+}$  and nonzero) and  $[\mathfrak{h}_{+}, x] = 0$  since  $\alpha$  vanishes on  $\mathfrak{h}_{+}$ . This is a contradiction, since  $\mathfrak{h}_{+}$  is a maximal commutative subalgebra of  $\mathfrak{k}$ .

By Lemma 41.8, a generic element  $t \in \mathfrak{h}_+$  is regular in  $\mathfrak{g}$ . So let us pick one for which  $\operatorname{Re}(t,\alpha^\vee)$  is nonzero for any coroot  $\alpha^\vee$  of  $\mathfrak{g}$ , and use it to define a polarization of R: set  $R_+ := \{\alpha \in R : \operatorname{Re}(t,\alpha^\vee) > 0\}$ . Then  $\theta(R_+) = R_+$ . So  $\theta(\alpha_i) = \alpha_{\theta(i)}$ , where  $\theta(i)$  is the action of  $\theta$  on the Dynkin diagram D of  $\mathfrak{g}$ . Thus if  $\theta(i) = i$  then  $\theta(e_i) = \pm e_i$ ,  $\theta(h_i) = h_i$ ,  $\theta(f_i) = \pm f_i$  while if  $\theta(i) \neq i$ , we can normalize  $e_i, e_{\theta(i)}, f_i, f_{\theta(i)}$  so that  $\theta(e_i) = e_{\theta(i)}, \theta(f_i) = f_{\theta(i)}, \theta(h_i) = h_{\theta(i)}$ . Thus  $\theta$  can be encoded in a marked Dynkin diagram of  $\mathfrak{g}$ : we connect vertices i and  $\theta(i)$  if  $\theta(i) \neq i$  and paint a  $\theta$ -stable vertex i white if  $\theta(e_i) = e_i$  (i.e.,  $e_i \in \mathfrak{k}$ , a **compact root**), and black if  $\theta(e_i) = -e_i$  (i.e.,  $e_i \in \mathfrak{p}$ , a **non-compact root**). Such a decorated Dynkin diagram is called a **Vogan diagram**. So we see that every Vogan diagram gives rise to a real form, and every real form is defined by some Vogan diagram.

- **Exercise 41.9.** (i) Show that the signature of the Killing form of a real form  $\mathfrak{g}_{\theta}$  of a complex semisimple Lie algebra  $\mathfrak{g}$  corresponding to involution  $\theta$  equals (dim  $\mathfrak{p}$ , dim  $\mathfrak{k}$ ). In particular, the Killing form of  $\mathfrak{g}_{\theta}$  is negative definite if and only if  $\theta = 1$ , i.e.,  $\mathfrak{g}_{\theta} = \mathfrak{g}^{c}$  is the compact form
- (ii) Deduce that for the split form  $\dim \mathfrak{k} = |R_+|$ , the number of positive roots of  $\mathfrak{g}$ .
- (iii) Show that for a real form of  $\mathfrak{g}$  in the compact inner class, we have  $\operatorname{rank}(\mathfrak{k}) = \operatorname{rank}(\mathfrak{g})$ .
- 41.4. **Real forms of classical Lie algebras.** We are not finished yet with the classification of real forms since different Vogan diagrams can define the same real form (they could arise from different choices of  $R_+$  coming from different choices of the element t). However, we are now ready to classify real forms of classical Lie algebras.
- 1. Type  $A_{n-1}$ , compact inner class. In this case  $\theta$  is an inner automorphism, conjugation by an element of order  $\leq 2$  in PSU(n). Obviously, such an element can be lifted to  $q \in U(n)$  such that  $q^2 = 1$ ,

- so  $\theta(x) = gxg^{-1}$ . Thus  $g = \mathrm{Id}_p \oplus (-\mathrm{Id}_q)$  where p + q = n and we may assume that  $p \geq q$ . It is easy to see that this defines the real form  $\mathfrak{g}_{\theta} = \mathfrak{su}(p,q)$ , and  $\mathfrak{k} = \mathfrak{gl}_p \oplus \mathfrak{sl}_q$ . These are all pairwise non-isomorphic since the corresponding automorphisms  $\theta$  are not conjugate to each other. So we get  $\left[\frac{n}{2}\right] + 1$  real forms. Note that for n = 2 this exhausts all real forms, so we have only two  $-\mathfrak{su}(2)$  and  $\mathfrak{su}(1,1) = \mathfrak{sl}_2(\mathbb{R})$  with  $\mathfrak{k} = \mathfrak{gl}_1$ .
- **2.** Type  $A_{n-1}$ , n > 2, the split inner class. If n is odd, there is no choice as all the vertices of the Vogan diagram are connected into pairs, so we only get the split form  $\mathfrak{g}_{\theta} = \mathfrak{sl}_{n}(\mathbb{R})$ . However, if n = 2k is even, there is one unmatched vertex in the middle of the Vogan diagram, which can be either white or black. It is easy to check that in the first case (white vertex)  $\mathfrak{k} = \mathfrak{sp}_{2k}$  and in the second one (black vertex)  $\mathfrak{k} = \mathfrak{so}_{2k}$ . So the first case is  $\mathfrak{g}_{\theta} = \mathfrak{sl}(k, \mathbb{H})$ , the Lie algebra of quaternionic matrices of size k whose trace has zero real part (See Subsection 6.3), while the second case is the split form  $\mathfrak{g}_{\theta} = \mathfrak{sl}_{n}(\mathbb{R})$ .
- **3.** Type  $B_n$ . Then  $\theta$  is an inner automorphism, given by an element of order  $\leq 2$  in SO(2n+1). So  $\theta = \operatorname{Id}_{2p+1} \oplus (-\operatorname{Id}_{2q})$  where p+q=n. Thus all the real forms are  $\mathfrak{so}(2p+1,2q)$  (all distinct),  $\mathfrak{k} = \mathfrak{so}_{2p+1} \oplus \mathfrak{so}_{2q}$ .
- **4.** Type  $C_n$ . Then  $\theta$  is an inner automorphism, given by an element  $g \in \operatorname{Sp}_{2n}(\mathbb{C})$  such that  $g^2 = 1$  or  $g^2 = -1$ . In the first case the 1-eigenspace of g has dimension 2p and the -1-eigenspace has dimension 2q (since they are symplectic), where p + q = n, and we may assume  $p \geq q$  (replacing g by -g if needed). So the real form we get is  $\mathfrak{g}_{\theta} = \mathfrak{u}(p,q,\mathbb{H})$ , the quaternionic pseudo-unitary Lie algebra for a quaternionic Hermitian form (see Subsection 6.3). In this case  $\mathfrak{k} = \mathfrak{sp}_{2p} \oplus \mathfrak{sp}_{2q}$ . On the other hand, if  $g^2 = -1$  then  $\mathbb{C}^{2n} = V(i) \oplus V(-i)$  (eigenspaces of g, which in this case are Lagrangian subspaces), so  $\mathfrak{k} = \mathfrak{gl}_n(\mathbb{C})$ . The corresponding real form is the split form  $\mathfrak{g}_{\theta} = \mathfrak{sp}_{2n}(\mathbb{R})$ .
- 5. Type  $D_n$ , compact inner class. We again have an inner automorphism  $\theta$  given by  $g \in SO(2n)$  such that  $g^2 = \pm 1$ . If  $g^2 = 1$  then  $\mathbb{C}^{2n} = V(1) \oplus V(-1)$ , the direct sum of eigenspaces, and since  $\det(g) = 1$ , the eigenspaces are even-dimensional, of dimensions 2p and 2q where p+q=n, and, as in the case of type  $C_n$ , we may assume  $p \geq q$ . So the corresponding real form is  $\mathfrak{g}_{\theta} = \mathfrak{so}(2p, 2q)$  with  $\mathfrak{k} = \mathfrak{so}_{2p} \oplus \mathfrak{so}_{2q}$ . On the other hand, if  $g^2 = -1$  then we have  $\mathbb{C}^{2n} = V(i) \oplus V(-i)$ , and these are Lagrangian subspaces of dimension n. So  $\mathfrak{k} = \mathfrak{gl}_n(\mathbb{C})$ . The corresponding real form is the quaternionic orthogonal Lie algebra (symmetries of a quaternionic skew-Hermitian form),  $\mathfrak{g}_{\theta} = \mathfrak{so}^*(2n)$  (see Subsection 6.3).

6. Type  $D_n$ , the other inner class. In this case  $\theta$  is given by an element g of O(2n) such that  $\det(g) = -1$  and  $g^2 = \pm 1$ . Note that if  $g^2 = -1$  then, as shown above,  $\det(g) = 1$ , so in the case at hand we always have  $g^2 = 1$ . Then  $\mathbb{C}^{2n} = V(1) \oplus V(-1)$ , but now the dimensions of these spaces are odd, 2p + 1 and 2q - 1 where p + q = n, and we may assume that  $p + 1 \ge q$ . So the real form is  $\mathfrak{g}_{\theta} = \mathfrak{so}(2p + 1, 2q - 1)$ , with  $\mathfrak{k} = \mathfrak{so}_{2p+1} \oplus \mathfrak{so}_{2q-1}$ . Note that for n = 3,  $D_3 = A_3$ , so we have  $\mathfrak{so}(5,1) = \mathfrak{sl}(2,\mathbb{H})$ . Note also that this agrees with what we found before: the split form  $\mathfrak{so}(n,n)$  is in the compact inner class for even n and in the other one for odd n, and the quasi-split form  $\mathfrak{so}(n+1,n-1)$  the other way around.

Exercise 41.10. Compute the subalgebras  $\mathfrak{k}$  for all the real forms of classical simple Lie algebras.

#### 42. Real forms of exceptional Lie algebras

42.1. Equivalence of Vogan diagrams. For exceptional Lie algebras, it is convenient to make a more systematic use of Vogan diagrams (we could do this also for classical Lie algebras, but there we can also do everything explicitly using linear algebra). Recall that any real form comes from a certain Vogan diagram, but different Vogan diagrams may be equivalent, i.e., define the same real form. So our job is to describe this equivalence relation.

First consider the case of the compact inner class. In this case the Vogan diagram is just the Dynkin diagram with black and white vertices (i.e., no matched vertices). Moreover, the case of all white vertices corresponds to the compact form, while the case when there are black vertices to noncompact forms. So let us focus on the latter case. Thus we have an element  $\theta \in H \subset G_{ad}$  such that  $\theta \neq 1$  but  $\theta^2 = 1$ , but we are allowed to conjugate  $\theta$  by elements of N(H), i.e., transform it by elements of the Weyl group W. So how do simple reflections  $s_i$  act on  $\theta$  (in terms of its Vogan diagram)?

The Vogan diagram of  $\theta$  is determined by the numbers  $\alpha_j(\theta) = \pm 1$ : if this number is 1 then j is white, and if it is -1 then j is black. Now, we have

$$\alpha_j(s_i(\theta)) = (s_i\alpha_j)(\theta) = (\alpha_j - a_{ij}\alpha_i)(\theta) = \alpha_j(\theta)\alpha_i(\theta)^{-a_{ij}}.$$

This equals  $\alpha_j(\theta)$  unless  $\alpha_i(\theta) = -1$  and  $a_{ij}$  is odd. Thus we obtain the following lemma.

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

Thus we can always arrange all vertices on the long leg except possibly the neighbor of the node to be black, while the short leg and the node also remain black. In addition, as seen from the pictures above, in the cases  $E_6$  and  $E_8$  these two configurations are equivalent by transformations inside the leg.

Now we can consider the configurations on the remaining leg (of length 2). The equivalence classes are  $\circ \circ$  and  $\bullet \circ = \circ \bullet = \bullet \bullet$ .

So in the case of  $E_6$  and  $E_8$  we get just two cases. It turns out that both for  $E_6$  and  $E_8$  these give two different real forms, one of which is split in the case of  $E_8$ .

Consider first the  $E_6$  case. One option is to take the Vogan diagram with just one black vertex, at the end of the long leg:

Then  $\mathfrak{k} = \mathfrak{so}_{10} \oplus \mathfrak{so}_2$  (as the black vertex corresponds to a minuscule weight). We denote this real form by  $E_6^2$ . On the other hand, if there

is only one black vertex on the short leg,

then  $\mathfrak{t}$  contains  $\mathfrak{sl}_6$ , so this real form is different (as  $\mathfrak{sl}_6$  is not a Lie subalgebra of  $\mathfrak{so}_{10}$ ). It's not difficult to show that in this case  $\mathfrak{t} = \mathfrak{sl}_6 \oplus \mathfrak{sl}_2$ . We denote this real form by  $E_6^3$ .

Now consider the  $E_8$  case. Again one option is the Vogan diagram with just one black vertex, at the end of the long leg:

Then  $\mathfrak{k}$  contains  $E_7$ , so this is not the split form since  $\dim \mathfrak{k} \geq 133$  but for the split form it should be 120. In fact, it is not hard to see that  $\mathfrak{k} = E_7 \oplus \mathfrak{sl}_2$ . We denote this real form by  $E_8^1$ . The second form is the split one,  $E_8^{\rm spl}$ . It can, for example, be obtained if we color black only one vertex, at the end of the middle leg:

In fact, it's not hard to show that the algebra  $\mathfrak{k}$  in this case is  $\mathfrak{so}_{16}$ . Finally, consider the  $E_7$  case. In this case we have four options, but two of them end up being equivalent. Namely, we have

So we are left with three cases, which all turn out different. The first one is just one black vertex at the end of the long leg:

In this case  $\mathfrak{k}$  contains  $E_6$ , so this is not the split form, as dim  $\mathfrak{k} \geq 78$  but for the split form it is 63. It is easy to see that  $\mathfrak{k} = E_6 \oplus \mathfrak{so}_2$  in this case (the black vertex corresponds to the minuscule weight). We denote this real form by  $E_7^1$ . The second option is a black vertex at the

end of the middle leg:

Then  $\mathfrak{t}$  contains  $\mathfrak{so}_{12}$ , of dimension 66, so again not the split form. One can show that for this form  $\mathfrak{k} = \mathfrak{so}_{12} \oplus \mathfrak{sl}_2$ . We denote it by  $E_7^2$ . Finally, the split form  $E_7^{\rm spl}$  is obtained when one colors black just the end of the short leg:

**Exercise 42.2.** Work out the details of computation of  $\mathfrak{k}$  for real forms of exceptional Lie algebras.

**Exercise 42.3.** Let  $\mathfrak{g}$  be the complex Lie algebra of type  $G_2$ , and G the corresponding Lie group. Let  $\mathfrak{sl}_3 \subset \mathfrak{g}$  be the Lie subalgebra generated by long root elements and  $SU(3) \subset G^c$  be the corresponding subgroup. Show that  $G^c/SU(3) \cong S^6$ . Use this to construct embeddings  $G^c \hookrightarrow$ SO(7) and  $G^c \hookrightarrow Spin(7)$ .

**Hint.** Consider the 7-dimensional irreducible representation of  $G^c$ . Show that it is of real type (obtained by complexifying a real representation V) and then consider the action of  $G^c$  on the set of unit vectors in V under a positive invariant inner product. Then compute the Lie algebra of the stabilizer and use that the sphere is simply connected.

**Exercise 42.4.** Keep the notation of Exercise 42.3. Show that one has  $\operatorname{Spin}(7)/G^c = S^7 \text{ and } SO(7)/G^c = \mathbb{RP}^7.$ 

**Hint.** Let S be the spin representation of Spin(7). Use that it is of real type (this can be deduced from Proposition 32.14) and then consider the action of Spin(7) on vectors of norm 1 in  $S_{\mathbb{R}}$ . Compute the Lie algebra of the stabilizer and use that the sphere is simply connected.

**Remark 42.5.** More generally, one can classify automorphisms of a simple complex Lie algebra  $\mathfrak{g}$  of arbitrary finite order. This was done by V. Kac using diagrams now known as **Kac diagrams**, see [OV], Subsection 4.7. In particular, this approach can be applied to classify automorphisms of order 2 which correspond to real forms of  $\mathfrak{g}$ , see [OV], Subsection 5.5.

# 43. Classification of connected compact and complex reductive groups

43.1. Connected compact Lie groups. We are now ready to classify connected compact Lie groups. We start with the following exercise.

**Exercise 43.1.** Show that if  $K^c$  is a compact Lie group then  $\mathfrak{k} := \text{Lie}(K^c)_{\mathbb{C}}$  is a reductive Lie algebra.

**Hint.** First use integration over  $K^c$  to show that  $\mathfrak{k}$  has a  $K^c$ -invariant positive definite Hermitian form. Then show that if I is an ideal in  $\mathfrak{k}$  then its orthogonal complement  $I^{\perp}$  is also an ideal.

Now we can proceed. We already know many examples of compact connected Lie groups - namely tori  $(S^1)^r$  and also groups  $G^c_{\rm ad}$  where  $G_{\rm ad} = {\rm Aut}(\mathfrak{g})^\circ$  for a semisimple Lie algebra  $\mathfrak{g}$ . We can also consider products  $(S^1)^r \times G^c_{\rm ad}$ . Exercise 43.1 shows that the Lie algebra of any compact Lie group is isomorphic to one of such a product, so this should be an exhaustive list up to taking coverings and quotients by finite central subgroups. It thus remains to understand the nature of these coverings, which reduces to understanding  $\pi_1(G^c_{\rm ad})$ . So our next task is to compute this group. In particular, we will show that it is finite.

So let  $\mathfrak{g}$  be a semisimple complex Lie algebra and G the corresponding simply connected complex Lie group (the universal cover of  $G_{\rm ad}$ ). Let Z be the kernel of the covering map  $G \to G_{\rm ad}$ , which is also  $\pi_1(G_{\rm ad})$  and the center of G. The finite dimensional representations of G are the same as those of  $\mathfrak{g}$ , so the irreducible ones are  $L_{\lambda}$ ,  $\lambda \in P_+$ . The center Z acts by a certain character  $\chi_{\lambda}: Z \to \mathbb{C}^{\times}$  on each  $L_{\lambda}$ . Since  $L_{\lambda+\mu}$  is contained in  $L_{\lambda} \otimes L_{\mu}$ , we have  $\chi_{\lambda+\mu} = \chi_{\lambda}\chi_{\mu}$ , so  $\chi$  uniquely extends to a homomorphism  $\chi: P \to \operatorname{Hom}(Z, \mathbb{C}^{\times})$ . Also, by definition  $\chi_{\theta} = 1$  (since the maximal root  $\theta$  is the highest weight of the adjoint representation on which Z acts trivially).

Now, by Exercise 30.15, if  $\lambda(h_i)$  are sufficiently large then for every root  $\alpha$  of  $\mathfrak{g}$  we have  $L_{\lambda+\alpha}\subset L_\lambda\otimes\mathfrak{g}$ . Thus  $\chi_{\lambda+\alpha}=\chi_\lambda$ , hence  $\chi_\alpha=1$ . So  $\chi$  is trivial on the root lattice Q, i.e., defines a homomorphism  $P/Q\to \operatorname{Hom}(Z,\mathbb{C}^\times)$ , or, equivalently,  $Z\to P^\vee/Q^\vee$ .

Note that the same argument works for  $G_{\text{ad}}^c$ , its universal cover  $G^c$ , and its center  $Z^c$  instead of  $G_{\text{ad}}$ , G, Z.

**Proposition 43.2.** A representation  $L_{\lambda}$  of  $\mathfrak{g}$  of highest weight  $\lambda \in P_+$  lifts to a representation of  $G_{\mathrm{ad}}$  (or, equivalently,  $G_{\mathrm{ad}}^c$ ) if and only if  $\lambda \in P_+ \cap Q$ .

*Proof.* We have just shown that if  $\lambda \in P_+ \cap Q$  then  $L_\lambda$  lifts. The converse follows from Proposition 36.12 applied to  $V = \mathfrak{g}$ .

Now we can proceed with the classification of semisimple compact connected Lie groups. We begin with the following lemma from topology (see e.g. [M], Supplementary exercises to Chapter 13, p.500, Exercise 4).

**Lemma 43.3.** If X is a connected compact manifold then the fundamental group  $\pi_1(X)$  is finitely generated.

*Proof.* (sketch) Cover X by small balls, pick a finite subcover, connect the centers. We get a finite graph whose fundamental group maps surjectively to  $\pi_1(X)$ .

**Theorem 43.4.** Let  $\mathfrak{g}$  be a semisimple complex Lie algebra and  $G_{\mathrm{ad}}^c$  the corresponding adjoint compact group. Then  $\pi_1(G_{\mathrm{ad}}^c) = P^{\vee}/Q^{\vee}$ . Thus the universal cover  $G^c$  of  $G_{\mathrm{ad}}^c$  is a compact Lie group.

Proof. Let  $G^c_*$  be a finite cover of  $G^c_{\mathrm{ad}}$ , and  $Z_{G^c_*} \subset G^c_*$  be the kernel of the projection  $G^c_* \to G^c_{\mathrm{ad}}$ . Then finite dimensional irreducible representations of  $G^c_*$  are a subset of finite dimensional irreducible representations of  $\mathfrak{g}$ , labeled by a subset  $P_+(G^c_*) \subset P_+$  containing  $P_+ \cap Q$  (as by Proposition 43.2 these are highest weights of representations of  $G^c_{\mathrm{ad}}$ ). Let  $P(G^c_*) \subset P$  be generated by  $P_+(G^c_*)$ . Let  $\chi_\lambda$  be the character by which  $Z_{G^c_*}$  acts on the irreducible representation  $L_\lambda$  of  $G^c_*$ . By Proposition 43.2,  $\chi$  defines an injective homomorphism  $\xi: P(G^c_*)/Q \to Z^\vee_{G^c_*}$ . Since  $G^c_*$  is compact, by the Peter-Weyl theorem this homomorphism is surjective, hence is an isomorphism.

It remains to show that  $\pi_1(G_{\mathrm{ad}}^c)$  is finite (then we can take  $G_*^c$  to be the universal cover of  $G_{\mathrm{ad}}^c$ , in which case  $P(G_*^c) = P$ , so we get  $P/Q \cong Z^{\vee}$ , hence  $Z = \pi_1(G_{\mathrm{ad}}) \cong P^{\vee}/Q^{\vee}$ ). To this end, note that by Lemma 43.3,  $\pi_1(G_{\mathrm{ad}}^c)$  is a finitely generated abelian group. Take a subgroup of finite index N in  $\pi_1(G_{\mathrm{ad}}^c)$  and let  $G_*^c$  be the corresponding cover. As we have shown, then  $N = |Z_{G_*^c}| \leq |P(G_*^c)/Q| \leq |P/Q|$ . But for finitely generated abelian groups this implies that the group is finite.

This immediately implies the following corollary.

Corollary 43.5. (i) If  $\mathfrak{g}$  is a simple complex Lie algebra then the simply connected Lie group  $G^c$  corresponding to the Lie algebra  $\mathfrak{g}^c$  is compact, and its center is  $P^{\vee}/Q^{\vee}$ , which also equals  $\pi_1(G^c_{\mathrm{ad}})$ .

- (ii) Let  $\Gamma \subset P^{\vee}/Q^{\vee}$  be a subgroup. Then the irreducible representations of  $G/\Gamma$  are  $L_{\lambda}$  such that  $\lambda$  defines the trivial character of  $\Gamma$ .
- (iii) Let  $G_i^c$  be the simply connected compact Lie group corresponding to a simple summand  $\mathfrak{g}_i$  of a semisimple Lie algebra  $\mathfrak{g} = \bigoplus_{i=1}^n \mathfrak{g}_i$ . Then any connected Lie group with Lie algebra  $\mathfrak{g}^c$  is compact and has the

form  $(\prod_{i=1}^n G_i^c)/Z$ , where  $Z = \pi_1(G^c)$  is a subgroup of  $\prod_i Z_i$ , and  $Z_i = P_i^{\vee}/Q_i^{\vee}$  are the centers of  $G_i^c$ . Moreover, every semisimple connected compact Lie group has this form.

In particular, it follows that simply connected semisimple compact Lie groups are of the form  $\prod_{i=1}^n G_i^c$ , where  $G_i^c$  are simply connected and simple.<sup>24</sup>

**Corollary 43.6.** Any connected compact Lie group is the quotient of  $T \times C$  by a finite central subgroup, where  $T = (S^1)^m$  is a torus and C is compact, semisimple and simply connected.

Proof. Let L be such a group,  $\mathfrak{l}$  its Lie algebra. It is reductive, so we can uniquely decompose  $\mathfrak{l}$  as  $\mathfrak{t} \oplus \mathfrak{c}$  where  $\mathfrak{t}$  is the center and  $\mathfrak{c}$  is semisimple. Let  $T, C \subset L$  be the connected Lie subgroups corresponding to  $\mathfrak{t}, \mathfrak{c}$ . It is clear that  $\mathrm{Lie}\overline{T} = \mathfrak{t} = \mathrm{Lie}T$ , so T is closed, hence compact, hence a torus. Also C is compact, so also closed, with  $\mathrm{Lie}C = \mathfrak{c}$ . Thus we have a surjective homomorphism  $T \times C \to L$  whose kernel is finite, as desired.

43.2. **Polar decomposition.** Now let us study the structure of the Lie subgroup  $G_{\mathrm{ad},\theta} \subset G_{\mathrm{ad}}$  corresponding to the real form  $\mathfrak{g}_{\theta} \subset \mathfrak{g}$  of a semisimple complex Lie algebra  $\mathfrak{g}$ , namely, the group of fixed points of the antiholomorphic involution  $\omega_{\theta} = \omega \circ \theta$  in  $G_{\mathrm{ad}}$ . It is clear that this subgroup is closed ( $\mathrm{Lie}\overline{G_{\mathrm{ad},\theta}} = \mathfrak{g}_{\theta} = \mathrm{Lie}G_{\mathrm{ad},\theta}$ ), but it may be disconnected: e.g. if  $\mathfrak{g}_{\theta} = \mathfrak{sl}_2(\mathbb{R})$  then  $G_{\mathrm{ad}} = PGL_2(\mathbb{C})$ , so  $G_{\mathrm{ad},\theta} = PGL_2(\mathbb{R})$ , the quotient of  $GL_2(\mathbb{R})$  by scalars, which has two components. However, the results below apply mutatis mutandis to the connected group  $G_{\mathrm{ad},\theta}^{\circ}$ .

Let  $K^c \subset G_{\mathrm{ad},\theta}$  be the subgroup of elements acting on  $\mathfrak{g}$  by unitary operators); namely,  $K^c$  is the set of fixed points of  $\omega_{\theta}$  on  $G_{\mathrm{ad}}^c$ .<sup>25</sup> This a closed (possibly disconnected) subgroup of  $G_{\mathrm{ad}}^c$  since  $\mathrm{Lie}\overline{K^c} = \mathfrak{k}^c = \mathrm{Lie}K^c$ , hence it is compact. Also let  $P_{\theta} := \exp(\mathfrak{p}_{\theta}) \subset G_{\mathrm{ad},\theta}$  (note that it is not a subgroup!). Since  $\mathfrak{p}_{\theta}$  acts on  $\mathfrak{g}$  by Hermitian operators, the exponential map  $\exp: \mathfrak{p}_{\theta} \to P_{\theta}$  is a diffeomorphism, so  $P_{\theta} \subset G_{\mathrm{ad},\theta}$  is a closed embedded submanifold (the set of elements acting on  $\mathfrak{g}$  by positive Hermitian operators).

 $<sup>^{24}</sup>$ We say that a connected Lie group G is **simple** if so is its Lie algebra. Thus this does not quite mean that G is simple as an abstract group: it may have a finite center (e.g., G = SU(2) or  $SL_2(\mathbb{C})$ ). For this reason such "simple" groups are sometimes called **almost simple**. However, the corresponding adjoint group  $G_{\rm ad}$  is indeed simple as an abstract group.

<sup>&</sup>lt;sup>25</sup>Of course, the group  $K^c$  depends on  $\theta$ , but for simplicity we will not indicate this dependence in the notation.

**Theorem 43.7.** (Polar decomposition for  $G_{ad,\theta}$ ) The multiplication map  $\mu: K^c \times P_\theta \to G_{ad,\theta}$  is a diffeomorphism. Thus  $G_{ad,\theta} \cong K^c \times \mathbb{R}^{\dim \mathfrak{p}}$  as a manifold (in particular,  $G_{ad,\theta}$  is homotopy equivalent to  $K^c$ ).

Proof. Recall that every invertible complex matrix A can be uniquely written as a product  $A = U_A R_A$ , where  $U = U_A$  is a unitary matrix and  $R = R_A$  a positive Hermitian matrix, namely  $R = (A^{\dagger}A)^{1/2}$ ,  $U = A(A^{\dagger}A)^{-1/2}$  (the classical polar decomposition). Let us consider this decomposition for  $g \in G_{\mathrm{ad},\theta} \subset \mathrm{Aut}(\mathfrak{g}) \subset GL(\mathfrak{g})$ . Since  $g^{\dagger}g$  is an automorphism of  $\mathfrak{g}$  with positive eigenvalues, so is  $(g^{\dagger}g)^{1/2} = R_g$ , so  $R_g \in P_{\theta}$  (a positive self-adjoint element in  $G_{\mathrm{ad},\theta}$ ). Also since  $U_g$  is unitary, it belongs to  $K^c$ . Thus the regular map  $g \mapsto (U_g, R_g)$  is the inverse to  $\mu$  (using the uniqueness of the polar decomposition).

In particular, applying Theorem 43.7 to complex Lie groups, we get

Corollary 43.8. The multiplication map defines a diffeomorphism

$$G_{\mathrm{ad}}^c \times \mathbf{P} \cong G_{\mathrm{ad}}$$
,

where **P** is the set of elements of  $G_{ad}$  acting on  $\mathfrak{g}$  by positive Hermitian operators. In particular,  $\pi_1(G_{ad}) = \pi_1(G_{ad}^c) = P^{\vee}/Q^{\vee}$ .

Corollary 43.9. If G is a semisimple complex Lie group then the center Z of G is contained in  $G^c$ , i.e., coincides with the center  $Z^c$  of  $G^c$ . Thus the restriction of finite dimensional representations from G to  $G^c$  is an equivalence of categories.

This also implies that by taking coverings the polar decomposition applies verbatim to the real form  $G_{\theta} = G^{\omega_{\theta}} \subset G$  of any connected complex semisimple Lie group G instead of  $G_{ad}$ . We note, however, that if G is simply connected, then  $G_{\theta}^{\circ}$  need not be. In fact, its fundamental group could be infinite. The simplest example is  $G = SL_2(\mathbb{C})$ , then for the split form  $G_{\theta} = SL_2(\mathbb{R})$ , which as we showed is homotopy equivalent to  $SO(2) = S^1$ , i.e. its fundamental group is  $\mathbb{Z}$ .

**Example 43.10.** 1. For  $G_{\theta} = SL_n(\mathbb{C})$  we have  $K^c = SU(n)$  and  $P_{\theta}$  is the set of positive Hermitian matrices of determinant 1, so the polar decomposition in this case is the usual polar decomposition of complex matrices.

2. For  $G_{\theta} = SL_n(\mathbb{R})$  we have  $K^c = SO(n)$  and  $P_{\theta}$  is the set of positive symmetric matrices of determinant 1, so the polar decomposition in this case is the usual polar decomposition of real matrices.

#### 43.3. Connected complex reductive groups.

**Definition 43.11.** A connected complex Lie group G is **reductive** if it is of the form  $((\mathbb{C}^{\times})^r \times G_{ss})/Z$  where  $G_{ss}$  is semisimple and Z is a finite central subgroup. A complex Lie group G is reductive if  $G^{\circ}$  is reductive and  $G/G^{\circ}$  is finite.

**Example 43.12.**  $GL_n(\mathbb{C}) = (\mathbb{C}^{\times} \times SL_n(\mathbb{C}))/\mu_n$  is reductive.

It is clear that the Lie algebra LieG of any complex reductive Lie group G is reductive, and any complex reductive Lie algebra is the Lie algebra of a connected complex reductive Lie group. However, a simply connected complex Lie group with a reductive Lie algebra need not be reductive (e.g.  $G = \mathbb{C}$ ).

If  $G = ((\mathbb{C}^{\times})^r \times G_{ss})/Z$  is a connected complex reductive Lie group then by Corollary 43.9,  $Z \subset (S^1)^r \times G_{ss}^c \subset (\mathbb{C}^{\times})^r \times G_{ss}$ , so we can define the compact subgroup  $G^c \subset G$  by  $G^c := ((S^1)^r \times G_{ss}^c)/Z$ . Then it is easy to see that restriction of finite dimensional representations from G to  $G^c$  is an equivalence, so representations of G are completely reducible. The irreducible representations are parametrized by collections  $(n_1, ..., n_r, \lambda)$ ,  $\lambda \in P_+(G_{ss})$ ,  $n_i \in \mathbb{Z}$ , which define the trivial character of Z.

43.4. **Linear groups.** A connected Lie group G (real or complex) is called **linear** if it can be realized as a Lie subgroup of  $GL_n(\mathbb{R})$ , respectively  $GL_n(\mathbb{C})$ . We have seen that any complex semisimple group is linear. However, for real semisimple groups this is not so (e.g. the universal cover of  $SL_2(\mathbb{R})$  is not linear, see Exercise 11.20). In fact, we see that we can characterize connected real semisimple linear groups as follows.

**Proposition 43.13.** Suppose  $\mathfrak{g}_{\theta}$  is a real form of a semisimple complex Lie algebra  $\mathfrak{g}$ , G a connected complex Lie group with Lie algebra  $\mathfrak{g}$ , and  $G_{\theta} = G^{\omega_{\theta}}$ . Then  $G_{\theta}$ ,  $G_{\theta}^{\circ}$  are linear groups. Moreover, every connected real semisimple linear Lie group is of the form  $G_{\theta}^{\circ}$ 

Exercise 43.14. Classify simply connected real semisimple linear Lie groups.

#### 44. Maximal tori in compact groups, Cartan decomposition

44.1. Maximal tori in connected compact Lie groups. Let  $\mathfrak{g}$  be a complex semisimple Lie algebra,  $\mathfrak{g}^c$  its compact form, G a connected Lie group with Lie algebra  $\mathfrak{g}$ ,  $G^c \subset G$  its compact part (the connected Lie subgroup with Lie algebra  $\mathfrak{g}^c$ ), as above.

A Cartan subalgebra  $\mathfrak{h}^c \subset \mathfrak{g}^c$  is a maximal commutative Lie subalgebra (note that it automatically consists of semisimple elements since all elements of  $\mathfrak{g}^c$  are semisimple). In other words, it is a subspace such that  $\mathfrak{h}^c \otimes_{\mathbb{R}} \mathbb{C}$  is a Cartan subalgebra of  $\mathfrak{g}$ .

Recall that all Cartan subalgebras of  $\mathfrak{g}$  are conjugate, even if equipped with a system of simple roots (Theorem 20.10). Namely, given two such subalgebras  $(\mathfrak{h}, \Pi)$  and  $(\mathfrak{h}', \Pi')$ , there is  $g \in G$  such that  $\mathrm{Ad}_g(\mathfrak{h}, \Pi) = (\mathfrak{h}', \Pi')$ . It turns out that the same result holds for  $\mathfrak{g}^c$ .

**Lemma 44.1.** Any two Cartan subalgebras in  $\mathfrak{g}^c$  equipped with systems of simple roots are conjugate under  $G^c$ .

Proof. Given  $(\mathfrak{h}^c, \Pi)$  and  $(\mathfrak{h}^{c'}, \Pi')$ , there is  $g \in G$  such that  $\mathrm{Ad}_g(\mathfrak{h}^c, \Pi) = (\mathfrak{h}^{c'}, \Pi')$ . Then we also have  $\mathrm{Ad}_{\overline{g}}(\mathfrak{h}^c, \Pi) = (\mathfrak{h}^{c'}, \Pi')$ , where  $\overline{g} := \omega(g)$ . So  $\overline{g}^{-1}g$  commutes with  $\mathfrak{h}^c$  and preserves  $\Pi$ , i.e.,  $\overline{g}h = g$ ,  $h \in H := \exp(\mathfrak{h}_{\mathbb{C}}^c)$ . Writing g = kp, where  $k \in G^c$ ,  $p \in \mathbf{P}$ , we have  $kp^{-1}h = kp$ , so  $h = p^2$ . Since p is positive,  $p = h^{1/2}$ , so it commutes with  $\mathfrak{h}^c$  and preserves  $\Pi$ , thus  $\mathrm{Ad}_k(\mathfrak{h}^c, \Pi) = (\mathfrak{h}^{c'}, \Pi')$ , as claimed.

Note that for every Cartan subalgebra  $\mathfrak{h}^c \subset \mathfrak{g}^c$ ,  $H^c = \exp(\mathfrak{h}^c) \subset G^c$  is a torus, which is clearly a **maximal torus** (as the complexified Lie algebra of a larger torus would be a larger commutative subalgebra than  $\mathfrak{h}^c$ ). Conversely, if  $H^c \subset G^c$  is a maximal torus then  $\text{Lie}(H^c)$  can be included in a Cartan subalgebra, hence it is itself a Cartan subalgebra. So we have a bijection between Cartan subalgebras in  $\mathfrak{g}^c$  and maximal tori in  $G^c$ . Similarly, there is a bijection between Cartan subalgebras in  $\mathfrak{g}$  and maximal tori in G.

This implies

Corollary 44.2. Any two maximal tori in G or  $G^c$  equipped with systems of simple roots are conjugate.

We also have

**Theorem 44.3.** Every element of a connected compact Lie group K is contained in a maximal torus, and all maximal tori in K are conjugate (even when equipped with systems of simple roots).

*Proof.* We may assume without loss of generality that K is semisimple, i.e.,  $K = G^c$  for a connected semisimple complex Lie group G, which

implies the second statement. To prove the first statement, let  $K' \subset K$  be the set of elements contained in a maximal torus. Fix a maximal torus  $T \subset K$  and consider the map  $f: K \times T \to K$  given by  $f(k,t) = ktk^{-1}$ , whose image is K'. This implies that K' is compact, hence closed, so  $K \setminus K'$  is open.

On the other hand, recall from Subsection 20.1 that a generic  $x \in \mathfrak{g}^c$  is **regular**, meaning that its centralizer  $\mathfrak{z}_x$  has dimension  $\leq \operatorname{rank}(\mathfrak{g})$ , in which case it must have dimension exactly  $\operatorname{rank}(\mathfrak{g})$  and be a Cartan subalgebra. It is clear that every regular element x is contained in a unique maximal torus, namely  $\exp(\mathfrak{z}_x)$ , so the elements of  $K \setminus K'$  are all non-regular. But the set of non-regular elements is defined by polynomial equations in  $\operatorname{Ad}_x$  (the minors of  $\operatorname{Ad}_x$  of codimension  $\operatorname{rank}(\mathfrak{g})$  all vanish), so  $K \setminus K'$  must be empty (as it is an open set contained in the set of solutions of nontrivial polynomial equations in  $\operatorname{Ad}_x$ ).

This immediately implies

Corollary 44.4. The exponential map  $\exp: \mathfrak{g}^c \to G^c$  is surjective.<sup>26</sup>

**Exercise 44.5.** Is the exponential map surjective for the group  $SL_2(\mathbb{C})$ ?

44.2. Semisimple and unipotent elements. Let G be a connected reductive complex Lie group. An element  $g \in G$  is called **semisimple** if it acts in every finite dimensional representation of G by a semisimple (=diagonalizable) operator, and **unipotent** if it acts in every finite dimensional representation of G by a unipotent operator (all eigenvalues are 1).

**Exercise 44.6.** Let Y be a faithful finite dimensional representation of G (it exists by Corollary 36.5). Show that  $g \in G$  is semisimple if and only if it acts semisimply on Y, and unipotent if and only if it acts unipotently on Y.

**Hint:** Use Proposition 36.12.

**Exercise 44.7.** Show that if G is semisimple then the exponential map defines a homeomorphism between the set of nilpotent elements in  $\mathfrak{g} = \text{Lie}G$  and the set of unipotent elements in G.

**Exercise 44.8.** Let Z be the center of a connected complex reductive group G.

<sup>&</sup>lt;sup>26</sup>Here is another proof of this corollary. Let K(x,y) be the Killing form of  $\mathfrak{g}^c$ . Since K is negative definite, the form -K extends to a bi-invariant Riemannian metric on  $G_c$ . Since  $G^c$  is compact, the Hopf-Rinow theorem guarantees that for any  $g \in G^c$  there is a geodesic on  $G^c$  in this metric connecting 1 and g. But it is easy to see that this geodesic is a segment of a one-parameter subgroup of  $G^c$ , which implies the statement.

- (i) Show that the homomorphism  $\pi: G \to G/Z$  defines a bijection between unipotent elements of G and G/Z.
- (ii) Show that the set of semisimple elements of G is the preimage under  $\pi$  of the set of semisimple elements of G/Z.

**Proposition 44.9.** (Jordan decomposition in G). Every element  $g \in G$  has a unique factorization  $g = g_s g_u$ , where  $g_s \in G$  is semisimple,  $g_u \in G$  is unipotent and  $g_s g_u = g_u g_s$ .

# Exercise 44.10. Prove Proposition 44.9.

- **Hint.** Use Exercise 44.8 to reduce to the case when  $G = G_{ad}$  is a semisimple adjoint group. In this case, write  $Ad_g$  as su, where s is a semisimple and u a unipotent operator with su = us (Jordan decomposition for matrices). Show that  $s = Ad_{g_s}$  and  $u = Ad_{g_u}$  for some commuting  $g_s, g_u \in G_{ad}$ . Then establish uniqueness using the uniqueness of Jordan decomposition of matrices.
- 44.3. Maximal abelian subspaces of  $\mathfrak{p}_{\theta}$ . Let G be a connected complex semisimple group,  $G_{\theta} \subset G$  a real form,  $\mathfrak{g}_{\theta} \subset \mathfrak{g}$  their Lie algebras. We have the polar decomposition  $G_{\theta} = K^c P_{\theta}$  and the additive version  $\mathfrak{g}_{\theta} = \mathfrak{k}^c \oplus \mathfrak{p}_{\theta}$ , with  $\mathfrak{p}_{\theta} = i\mathfrak{p}^c$ . Also  $\mathfrak{g}^c = \mathfrak{k}^c \oplus \mathfrak{p}^c$ .
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

**Theorem 44.12.** (The Cartan decomposition) We have  $G_{\theta} = K^{c}AK^{c}$ . In other words, every element  $g \in G_{\theta}$  has a factorization  $g = k_{1}ak_{2}$ ,  $k_{1}, k_{2} \in K^{c}$ ,  $a \in A$ .<sup>27</sup>

Proof. Recall that we have the polar decomposition  $G_{\theta} = K^{c}P_{\theta}$ . Thus it suffices to show that every  $K^{c}$ -orbit on  $P_{\theta}$  intersects A. To do so, take  $Y \in P_{\theta}$  and let  $y = \log Y \in \mathfrak{p}_{\theta}$ . By Proposition 44.11 there is  $k \in K^{c}$  such that  $\mathrm{Ad}_{k}(y) \in \mathfrak{a}$ . Then  $\mathrm{Ad}_{k}(Y) \in A$ , as claimed.

**Remark 44.13.** Theorem 44.12 has a straightforward generalization to reductive groups.

- **Example 44.14.** 1. For  $G_{\theta} = GL_n(\mathbb{C})$ , Theorem 44.12 reduces to a classical theorem in linear algebra: any invertible complex matrix can be written as  $U_1DU_2$ , where  $U_1, U_2$  are unitary and D is diagonal with positive entries.
- 2. Similarly, for  $G_{\theta} = GL_n(\mathbb{R})$ , Theorem 44.12 says that any invertible real matrix can be written as  $O_1DO_2$ , where  $O_1, O_2$  are orthogonal and D is diagonal with positive entries.

#### 44.5. Maximal compact subgroups.

**Theorem 44.15.** (E. Cartan) Let  $G_{\theta}$  be a real form of a connected semisimple complex group G. Then any compact subgroup L of  $G_{\theta}$  is conjugate to a subgroup of  $K^c$  by an element of  $P_{\theta}$ . Also every compact subgroup of  $G_{\theta}$  is contained in a maximal one. Thus all maximal compact subgroups of  $G_{\theta}$  are conjugate (to  $K^c$ ).

<sup>&</sup>lt;sup>27</sup>This factorization is not unique.

*Proof.* We give a simplified version of Cartan's proof, due to G. D. Mostow.

First note that  $K^c$  is a maximal compact subgroup of  $G^{\theta}$ . Indeed, if  $K \supset K_c$  is a compact subgroup then the polar decomposition implies that  $K = K_c \cdot (P_{\theta} \cap K)$ . But if  $Y \in P_{\theta} \cap K$  and  $Y \neq 1$  then the sequence  $Y^n \in K$  has no convergent subsequence (which is clear by looking at the eigenvalues of  $Y^n$  on  $\mathfrak{g}_{\theta}$ . Thus  $K = K_c$ .

It remains to prove that every compact subgroup  $L \subset G_{\theta}$  can be conjugated into  $K^c$  by an element of  $P_{\theta}$ . The idea of proof is to define an L-invariant continuous real-valued function f on  $P_{\theta}$  and show that it has a unique minimum Y using a convexity argument. Then the required conjugating element is obtained as  $Y^{-\frac{1}{2}}$ .

So let us proceed with this plan. Recall that we have a decomposition of the Lie algebra  $\mathfrak{g}_{\theta} := \text{Lie}(G_{\theta})$  given by  $\mathfrak{g}_{\theta} = \mathfrak{k}^c \oplus \mathfrak{p}_{\theta}$ , which is the eigenspace decomposition of  $\theta$ , and that the Killing form  $B = B_{\mathfrak{g}}$  is positive on  $\mathfrak{p}_{\theta}$ , negative on  $\mathfrak{k}^c$ , and  $\theta$ -invariant. Thus we have a positive definite inner product on the real vector space  $\mathfrak{g}_{\theta}$  given by

$$B_{\theta}(x,y) := -B(x,\theta(y)).$$

Denote by  $A^{\dagger}$  the adjoint operator to  $A \in \operatorname{End}(\mathfrak{g}_{\theta})$  under this inner product. Then  $A := \operatorname{Ad}_g$  is orthogonal  $(A^{\dagger} = A^{-1})$  for  $g \in K^c$ , while for  $g \in P_{\theta}$  it is self-adjoint  $(A^{\dagger} = A)$ , unimodular and positive definite as its eigenvalues are positive). So if g = kp with  $k \in K^c$ ,  $p \in P_{\theta}$  then  $\overline{g} = kp^{-1}$ , hence

$$(44.1) Ad_g^{\dagger} = Ad_{kp}^{\dagger} = Ad_p^{\dagger}Ad_k^{\dagger} = Ad_pAd_k^{-1} = Ad_{pk^{-1}} = Ad_{\overline{g}}^{-1}.$$

Let

$$S := \int_{L} \mathrm{Ad}_{h}^{\dagger} \mathrm{Ad}_{h} dh \in \mathrm{End}(\mathfrak{g}_{\theta}).$$

Then S is a self-adjoint positive definite operator. So it admits an orthonormal eigenbasis  $v_i$  with eigenvalues  $\lambda_i > 0$ . Let  $\lambda_{\min}$  be the smallest of these eigenvalues.

Consider the function  $f: P_{\theta} \to \mathbb{R}$  given by

$$f(X) := \operatorname{Tr}(\operatorname{Ad}_X \cdot S) = \sum_i \lambda_i B_{\theta}(\operatorname{Ad}_X v_i, v_i).$$

So, since  $Ad_X$  is positive definite, we have

$$(44.2) f(X) \ge \lambda_{\min} \operatorname{Tr}(\operatorname{Ad}_X).$$

Note also that the group  $G_{\theta}$  acts on  $P_{\theta}$  by  $g \circ X = gX\overline{g}^{-1}$ , and by (44.1) the function f is L-invariant.

Recall that for any R > 0 the set of unimodular positive symmetric matrices A with  $Tr(A) \leq R$  is compact, since so is its subset of diagonal

matrices, and any such matrix can be diagonalized by an orthogonal transformation. Since  $\operatorname{Ad}_X$  is a positive self-adjoint operator on  $\mathfrak{g}_{\theta}$  with respect to  $B_{\theta}$ , it follows from (44.2) that the set of  $X \in P_{\theta}$  with  $f(X) \leq R$  is compact. This implies that f, being continuous, attains a minimum on  $P_{\theta}$ . Suppose it attains a minimum at the point  $Y = \exp(y), y \in \mathfrak{p}_{\theta}$ .

Proposition 44.16. This minimum point is unique.

*Proof.* Suppose  $Z = \exp(z)$ ,  $z \in \mathfrak{p}_{\theta}$  is another minimum point. Consider the Cartan decomposition of the element  $\exp(-\frac{z}{2})\exp(\frac{y}{2}) \in G_{\theta}$ :

$$\exp(\frac{z}{2})\exp(-\frac{y}{2}) = k\exp(\frac{z}{2}),$$

 $k \in K^c$ ,  $x \in \mathfrak{p}_{\theta}$ . It follows that

$$\exp(\frac{x}{2}) = \exp(-\frac{y}{2}) \exp(\frac{z}{2})k = k^{-1} \exp(\frac{z}{2}) \exp(-\frac{y}{2}),$$

so multiplying, we get

$$\exp(x) = \exp(-\frac{y}{2}) \exp(z) \exp(-\frac{y}{2})$$

and thus

(44.3) 
$$\exp(z) = \exp(\frac{y}{2}) \exp(x) \exp(\frac{y}{2}).$$

Consider the function

$$F(t) = f(\exp(\frac{y}{2})\exp(tx)\exp(\frac{y}{2})), \ t \in \mathbb{R}.$$

This function has a global minimum at t = 0, and also at t = 1 in view of (44.3). Thus the function F is not strictly convex. On the other hand, we have the following lemma.

**Lemma 44.17.** Let a, M be symmetric real matrices such that M is positive definite. Then the function

$$\phi(t) := \text{Tr}(\exp(ta)M), \ t \in \mathbb{R}$$

is convex, and is strictly convex if  $a \neq 0$ .

*Proof.* Conjugating a, M simultaneously by an orthogonal matrix, we may assume that a is diagonal, with diagonal entries  $a_i$ . Then we have

$$\phi(t) := \sum_{i} M_{ii} \exp(ta_i).$$

Since M is positive definite,  $M_{ii} > 0$  and the statement follows.

Using Lemma 44.17 for  $a := \operatorname{ad} x$  and  $M := \exp(\frac{\operatorname{ad} y}{2})S\exp(\frac{\operatorname{ad} y}{2})$  and the fact that F(t) is not strictly convex, we get that  $\operatorname{ad} x = 0$ , hence x = 0 (as  $\mathfrak{g}$  is semisimple) and y = z, as claimed.

Now, since the function f has a unique minimum point and is L-invariant, this minimum point must also be L-invariant. Thus we have  $h \exp(y) = \exp(y)\overline{h}$  for all  $h \in L$ . It follows that

$$\exp(-\frac{y}{2})h\exp(\frac{y}{2}) = \exp(\frac{y}{2})\overline{h}\exp(-\frac{y}{2}) = \overline{\exp(-\frac{y}{2})h\exp(\frac{y}{2})}.$$

Thus the element  $p := \exp(-\frac{y}{2}) = Y^{-\frac{1}{2}}$  conjugates L into  $K^c$ .

44.6. Cartan subalgebras in real semisimple Lie algebras. We have seen that Cartan subalgebras in a complex semisimple Lie algebra are conjugate, but this is not so for real semisimple Lie algebras, as demonstrated by the following exercise.

**Exercise 44.18.** (i) Let  $\mathfrak{g} = \mathfrak{sl}_n(\mathbb{R})$ . For  $0 \leq m \leq \frac{n}{2}$ , let  $\mathfrak{h}_m$  be the space of matrices of the form

$$A = \bigoplus_{i=1}^{m} \begin{pmatrix} a_i & b_i \\ -b_i & a_i \end{pmatrix} \oplus \operatorname{diag}(c_1, ..., c_{n-2m})$$

such that Tr(A) = 0. Show that  $\mathfrak{h}_m$  is a Cartan subalgebra of  $\mathfrak{g}$  and that  $\mathfrak{h}_m$  is not conjugate to  $\mathfrak{h}_n$  when  $m \neq n$  (look at eigenvalues of elements of  $\mathfrak{h}_m$  in the vector representation). Conclude that Lemma 44.1 does not necessarily hold for non-compact forms of  $\mathfrak{g}$ .

- (ii) Show that every Cartan subalgebra in  $\mathfrak{g}$  is conjugate to one of the form  $\mathfrak{h}_m$  for some m.
- (iii) Classify Cartan subalgebras in other classical real simple Lie algebras (up to conjugacy).

Let us say that a semisimple element of  $\mathfrak{g}_{\theta}$  is **split** if it acts on  $\mathfrak{g}_{\theta}$  with real eigenvalues, and say that a commutative Lie subalgebra of  $\mathfrak{g}_{\theta}$  is a **split subalgebra** if it consists of split elements. An invariant of a Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}_{\theta}$  under conjugation is the dimension  $s(\mathfrak{h})$  of the largest split subalgebra of  $\mathfrak{h}$  (consisting of all split elements of  $\mathfrak{h}$ ). For example, a split real form  $\mathfrak{g}_{\theta}$  has a split Cartan subalgebra with  $s(\mathfrak{h}) = r = \operatorname{rank}(\mathfrak{g})$ , and conversely, a real form that admits a split Cartan subalgebra is split. Also, in Exercise 44.18,  $s(\mathfrak{h}_m) = n - 1 - m$ .

Let us say that  $\mathfrak{h}$  is **maximally split** if  $s(\mathfrak{h})$  is the largest possible, and **maximally compact** if  $s(\mathfrak{h})$  is the smallest possible. For example, in Exercise 44.18,  $\mathfrak{h}_0$  is maximally split and  $\mathfrak{h}_{[n/2]}$  is maximally compact (where [n/2] is the floor of n/2). Also, a split Cartan subalgebra is maximally split and a compact one (i.e., one for which  $\exp(\mathfrak{h})$  is a compact torus) is maximally compact, if they exist. Finally, the Cartan subalgebra  $\mathfrak{h}_+^c \oplus i\mathfrak{h}_-^c$ , where  $\mathfrak{h}_+^c, \mathfrak{h}_-^c$  are as in the proof of Proposition 41.7, is maximally compact.

Note that  $s(\mathfrak{h})$  may also be interpreted as the signature of the Killing form restricted to  $\mathfrak{h}$ , which equals  $(s(\mathfrak{h}), r - s(\mathfrak{h}))$ .

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

# 44.7. Integral form of the Weyl character formula.

**Proposition 44.20.** Let f be a conjugation-invariant continuous function on a compact connected Lie group K with a maximal torus  $T \subset K$  and Haar probability measure dk. Then

$$\int_{K} f(k)dk = \frac{1}{|W|} \int_{T} f(t) |\Delta(t)|^{2} dt,$$

where  $\Delta(t)$  is the Weyl denominator,<sup>28</sup>

$$\Delta(t) = \rho(t)^{-1} \prod_{\alpha \in R^+} (\alpha(t) - 1).$$

Proof. Since characters of irreducible representations span a dense subspace in the space of conjugation-invariant continuous functions on K, it suffices to check this for  $f = \chi_{\lambda}$ , the character of the irreducible representation  $L_{\lambda}$ . Then the left hand side is  $\delta_{0\lambda}$  by orthogonality of characters. On the other hand, the Weyl character formula implies that the right hand side also equals  $\delta_{0\lambda}$ .

**Example 44.21.** Let f be a conjugation-invariant continuous function on U(n). Then

$$\int_{U(n)} f(k)dk =$$

<sup>&</sup>lt;sup>28</sup>Note that the function  $\rho(t)$  may be multivalued, but its branches differ from each other by a root of unity, so the function  $|\Delta(t)|$  is well defined. Namely,  $|\Delta(t)| = |\Delta_0(t)|$  where  $\Delta_0(t) = \prod_{\alpha \in R^+} (\alpha(t) - 1)$ .

$$\frac{1}{(2\pi)^n n!} \int_{|z_1| = \dots = |z_n| = 1} f(\operatorname{diag}(z_1, \dots, z_n)) \prod_{m < j} |z_m - z_j|^2 d\theta_1 \dots d\theta_n$$

where  $z_j = e^{i\theta_j}$ .

Thus we see that the orthogonality of characters can be written as

$$\frac{1}{|W|} \int_{T} \chi_{\lambda}(t) \overline{\chi_{\mu}(t)} |\Delta(t)|^{2} dt = \delta_{\lambda,\mu}.$$

**Exercise 44.22.** (i) Let  $\mathfrak{k} = \text{Lie}K$  with Cartan subalgebra  $\mathfrak{k}$  and f be a compactly supported K-invariant continuous function on  $\mathfrak{k}$ . Show that

$$\int_{\mathfrak{k}} f(a)da = \frac{1}{|W|} \int_{\mathfrak{k}} f(u) |\Delta_{\mathrm{rat}}(u)|^2 du,$$

where  $\Delta_{\mathrm{rat}}(u)=\prod_{\alpha\in R_+}\alpha(u)$  is the rational version of the Weyl denominator.

(ii) Write explicitly the identity you get if you set  $f(a) := e^{B_{\mathfrak{k}}(a,a)}$  (compute the Gaussian integral on the left hand side).

**Hint.** In Proposition 44.20, make a change of variable  $k = \exp(\varepsilon a)$ ,  $t = e^{\varepsilon u}$  for small  $\varepsilon > 0$  and then send  $\varepsilon$  to zero.

#### 45. Topology of Lie groups and homogeneous spaces, I

45.1. The Chevalley-Eilenberg complex of a compact connected Lie group. We would now like to study topology of connected Lie groups. The Cartan decomposition implies that any real semisimple Lie group  $G_{\theta}$  is diffeomorphic to the product of its maximal compact subgroup  $K^c$  and a Euclidean space. This combined with weak Levi decomposition (Theorem 16.6) implies that topology of connected Lie groups essentially reduces to topology of compact ones, as any simply-connected solvable Lie group has a filtration by normal subgroups with successive quotients being the 1-dimensional group  $\mathbb{R}$ , hence is diffeomorphic to  $\mathbb{R}^n$  (cf. Theorem 49.1, Corollary 49.6 below).

So let us study cohomology of compact connected Lie groups.

We first recall some generalities on cohomology of manifolds. As we mentioned before, the cohomology of an n-dimensional manifold M can be computed by the **de Rham complex** 

$$0 \to \Omega^0(M) \to \Omega^1(M) \to \dots \to \Omega^n(M) \to 0$$
,

where  $\Omega^i(M)$  is the space of smooth (complex-valued) differential iforms on M. The maps in this complex are given by the differential  $d: \Omega^i(M) \to \Omega^{i+1}(M)$ , which satisfies the equation  $d^2 = 0$ . Namely, we define the i-th **de Rham cohomology** of M as the quotient

$$H^i(M,\mathbb{C}) := \Omega^i_{\mathrm{closed}}(M)/\Omega^i_{\mathrm{exact}}(M)$$

where  $\Omega^{i}_{\text{closed}}(M) \subset \Omega^{i}(M)$  is the space of **closed forms** (such that  $d\omega = 0$ ) and  $\Omega^{i}_{\text{exact}}(M) \subset \Omega^{i}(M)$  is the space of **exact forms** (such that  $\omega = d\eta$  for some  $\eta \in \Omega^{i-1}(M)$ ).

If M is compact then the spaces  $H^i(M,\mathbb{C})$  are known to be finite dimensional, so we can define the **Betti numbers** of M,  $b_i(M) := \dim H^i(M,\mathbb{C})$ . Note that  $b_0(M)$  is the number of connected components of M, so if M is connected then  $b_0(M) = 1$ .

The wedge product of differential forms descends to the cohomology, which makes  $H^{\bullet}(M,\mathbb{C}) := \bigoplus_{i=0}^{n} H^{i}(M,\mathbb{C})$  into a graded algebra. This algebra is associative and **graded-commutative**:  $ab = (-1)^{\deg(a)\deg(b)}ba$  (since the wedge product of differential forms has these properties). Moreover, if  $f: M \to N$  is a differentiable map of manifolds then we have the pullback map  $f^*: \Omega^i(N) \to \Omega^i(M)$  which commutes with d and hence descends to the cohomology. Also  $f^*$  preserves the wedge product, hence defines a graded algebra homomorphism  $f^*: H^{\bullet}(N,\mathbb{C}) \to H^{\bullet}(M,\mathbb{C})$ .

**Exercise 45.1.** Let  $f:[0,1]\times M\to N$  be a differentiable map and  $f_t:M\to N$  be given by  $f_t(x)=f(t,x)$ . Then  $f_0^*=f_1^*$  on  $H^{\bullet}(N,\mathbb{C})$ . In other words,  $f^*$  is invariant under (smooth) homotopies of f.

Recall that for a vector field v on M, the Lie derivative

$$L_v: \Omega^{\bullet}(M) \to \Omega^{\bullet}(M)$$

is the unique derivation of the algebra of differential forms which commutes with the de Rham differential and equals the usual derivative of a function along v on  $\Omega^0(M)$ .

**Lemma 45.2.** (Cartan's magic formula) Let v be a vector field on M,  $L_v: \Omega^i(M) \to \Omega^i(M)$  the Lie derivative and  $\iota_v: \Omega^i(M) \to \Omega^{i-1}(M)$  the contraction operator. Then

$$L_v = \iota_v d + d\iota_v$$
.

*Proof.* It suffices to check this identity on local charts. It is easy to see that both sides are derivations, so it suffices to check the equation on functions (0-forms) and on 1-forms of the form df where f is a function. For functions we have  $L_v f = \iota_v df$ , which is essentially the definition of  $L_v$ , while for  $\omega = df$  we have

$$L_v(df) = d(L_v f) = d\iota_v(df) = (\iota_v d + d\iota_v)(df),$$
  
since  $d^2 = 0$ .

Corollary 45.3.  $L_v$  maps closed forms to exact forms, hence acts trivially in cohomology.

**Corollary 45.4.** If a connected Lie group G acts on a manifold M then G acts trivially on  $H^{\bullet}(M, \mathbb{C})$ .

Suppose now that a compact connected Lie group G acts on a manifold M. Then we have the averaging operator  $P: \Omega^{\bullet}(M) \to \Omega^{\bullet}(M)$  over G which commutes with d and satisfies the equation  $P^2 = P$ , so we have a decomposition of complexes

$$\Omega^{\bullet}(M) = \Omega^{\bullet}(M)^G \oplus \Omega^{\bullet}(M)_0$$

where the first summand is the image of P and the second one is the kernel of P.

**Theorem 45.5.** The complex  $\Omega^{\bullet}(M)_0$  is exact. Thus the cohomology  $H^{\bullet}(M,\mathbb{C})$  is computed by the complex of invariant differential forms  $\Omega^{\bullet}(M)^G$ .

*Proof.* If  $\omega \in \Omega^i(M)_0$  is closed then by Corollary 45.4 the cohomology class  $[\omega]$  of  $\omega$  coincides with the cohomology class of  $[g\omega]$  for all  $g \in G$ . Thus

$$[\omega] = \int_{G} [g\omega] dg = \left[ \int_{G} g\omega dg \right] = 0.$$

It follows that  $\omega = d\eta$  for some  $\eta \in \Omega^i(M)$ . Then  $\omega = (1 - P)\omega = d(1 - P)\eta$ , and  $(1 - P)\eta \in \Omega^i(M)_0$ . So the complex  $\Omega^{\bullet}(M)_0$  is exact, which implies the statement.

Corollary 45.6. If G is a compact Lie group then  $H^{\bullet}(G, \mathbb{C})$  is computed by the complex  $\Omega^{\bullet}(G)^G$  of left-invariant differential forms on G.

The complex  $\Omega^{\bullet}(G)^G$  is called the **Chevalley-Eilenberg complex** of G.

45.2. Cohomology of Lie algebras. It turns out that the Chevalley-Eilenberg complex of G can be described purely algebraically in terms of the Lie algebra  $\mathfrak{g} = \text{Lie}(G)_{\mathbb{C}}$ . To this end, we will need another lemma from basic differential geometry.

**Lemma 45.7.** (Cartan differentiation formula) Let  $\omega \in \Omega^m(M)$  and  $v_0, ..., v_m$  be vector fields on M. Then

$$d\omega(v_0, ..., v_m) = \sum_{i} (-1)^i L_{v_i}(\omega(v_0, ..., \widehat{v}_i, ..., v_m)) +$$

$$\sum_{i < j} (-1)^{i+j} \omega([v_i, v_j], v_0, ..., \widehat{v}_i, ..., \widehat{v}_j, ..., v_m)$$

(where the hats indicate the omitted terms).

*Proof.* It is easy to show that the right hand side is linear over functions on M with respect to each  $v_i$  (the first derivatives of the function cancel out). Therefore, it suffices to assume that  $v_i = \frac{\partial}{\partial x_{k_i}}$  (in local coordinates), and  $\omega = f dx_{j_1} \wedge ... \wedge dx_{j_m}$ . Then the second summand on the RHS vanishes and the verification is straightforward.

Corollary 45.8. Let G be a Lie group and  $\omega \in \Omega^m(G)^G$  be a left-invariant differential form. Then for any left-invariant vector fields  $v_0, ..., v_m$  we have

$$(45.1) d\omega(v_0, ..., v_m) = \sum_{i < j} (-1)^{i+j} \omega([v_i, v_j], v_0, ..., \widehat{v}_i, ..., \widehat{v}_j, ..., v_m).$$

*Proof.* This follows since the functions  $\omega(v_0,...,\widehat{v}_i,...,v_m)$  are constant.

Now observe that  $\Omega^m(G)^G = \wedge^m \mathfrak{g}^*$ . Thus we get

Corollary 45.9. For any Lie group G the complex  $\Omega^{\bullet}(G)^G$  coincides with the complex

$$0 \to \mathbb{C} \to \mathfrak{g}^* \to (\wedge^2 \mathfrak{g})^* \to \dots (\wedge^m \mathfrak{g})^* \to \dots$$

with differential defined by (45.1), where  $\mathfrak{g} = \text{Lie}(G)_{\mathbb{C}}$ .

This purely algebraic complex can be defined for any Lie algebra  $\mathfrak{g}$  over any field (the equality  $d^2 = 0$  follows from the Jacobi identity).<sup>29</sup> It is called the **standard complex** or the **Chevalley-Eilenberg complex** of  $\mathfrak{g}$ , denoted  $CE^{\bullet}(\mathfrak{g})$ , and its cohomology is called the **Lie algebra cohomology** of  $\mathfrak{g}$ , denoted  $H^{\bullet}(\mathfrak{g})$ .<sup>30</sup>

Also note that the complex  $CE^{\bullet}(\mathfrak{g})$  has wedge product multiplication, which descends to the cohomology. Thus  $H^{\bullet}(\mathfrak{g})$  is a graded-commutative associative algebra. Furthermore, if  $\mathfrak{g}=\mathrm{Lie}(G)_{\mathbb{C}}$  for a compact connected Lie group G then  $H^{\bullet}(\mathfrak{g})\cong H^{\bullet}(G,\mathbb{C})$  as a graded algebra. However, this may fail even at the level of vector spaces (i.e., Betti numbers) if G is not compact.

**Example 45.10.** Let  $\mathfrak{g}$  be abelian, dim  $\mathfrak{g} < \infty$ . Then  $CE^{\bullet}(\mathfrak{g}) = \wedge^{\bullet}\mathfrak{g}^{*}$ , with zero differential, so  $H^{\bullet}(\mathfrak{g}) = \wedge^{\bullet}\mathfrak{g}^{*}$ . So if  $G = (S^{1})^{n}$  is a torus then we get  $H^{\bullet}(G,\mathbb{C}) = \wedge^{\bullet}\mathfrak{g}^{*} = \wedge^{\bullet}(\xi_{1},...,\xi_{n})$  where  $\xi_{i}$  have degree 1. In particular,  $H^{\bullet}(S^{1}) = \wedge^{\bullet}(\xi)$ . However, for the universal cover  $\mathbb{R}$  of  $S^{1}$  this is clearly false.

Remark 45.11. Corollary 45.9 implies that for compact Lie groups  $K_1, K_2$  the map  $\Omega^{\bullet}(K_1) \otimes \Omega^{\bullet}(K_2) \to \Omega^{\bullet}(K_1 \times K_2)$  (i.e., in components,  $\Omega^i(K_1) \otimes \Omega^j(K_2) \to \Omega^{i+j}(K_1 \times K_2)$ ) defines an isomorphism of cohomology rings  $H^{\bullet}(K_1, \mathbb{C}) \otimes H^{\bullet}(K_2, \mathbb{C}) \to H^{\bullet}(K_1 \times K_2, \mathbb{C})$ . This is a special case of the **Künneth theorem**, which actually holds for any manifolds (and more generally for sufficiently nice topological spaces), which need not have any group structure. We warn the reader, however, that the **tensor product of algebras here is in the graded sense**, i.e.

$$(a \otimes b)(a' \otimes b') = (-1)^{\deg(b) \deg(a')} (aa' \otimes bb').$$

**Theorem 45.12.** If G is a connected compact Lie group with  $\text{Lie}(G)_{\mathbb{C}} = \mathfrak{g}$  then  $H^{\bullet}(G,\mathbb{C}) \cong (\wedge^{\bullet}\mathfrak{g}^*)^{\mathfrak{g}}$  as a ring.

*Proof.* We have an action of  $G \times G$  on G, so the cohomology of G is computed by the complex of invariants  $\Omega^{\bullet}(G)^{G \times G} = (\wedge^{\bullet} \mathfrak{g}^*)^G$ . So our job is to show that the differential in this complex is actually zero.

<sup>&</sup>lt;sup>29</sup>Note that if  $\mathfrak{g}$  is finite dimensional then  $\wedge^i \mathfrak{g}^* = (\wedge^i \mathfrak{g})^*$ .

<sup>&</sup>lt;sup>30</sup>Note that  $H^1(\mathfrak{g})$  already appeared earlier in Section 18.

But this follows immediately from the definition of the differential in  $\wedge^{\bullet}\mathfrak{g}^*$ .

We also have

**Proposition 45.13.** If G is a connected Lie group,  $\Gamma \subset G$  a finite subgroup, and  $\pi : G \to G/\Gamma$  is the canonical map then  $\pi^*$  defines an isomorphism  $H^{\bullet}(G/\Gamma, \mathbb{C}) \to H^{\bullet}(G, \mathbb{C})$ .

*Proof.* The map  $\pi^*$  is an isomorphism  $H^{\bullet}(G/\Gamma, \mathbb{C}) \to H^{\bullet}(G, \mathbb{C})^{\Gamma}$ , but  $\Gamma$ , being a subgroup of G, acts trivially on  $H^{\bullet}(G, \mathbb{C})$ .

Thus it suffices to determine the cohomology of simple, simply connected compact Lie groups.

#### 46. Topology of Lie groups and homogeneous spaces, II

46.1. The coproduct on the cohomology ring. To understand the algebra  $R := H^{\bullet}(G) = H^{\bullet}(G, \mathbb{C})$  better, note that the multiplication map  $G \times G \to G$  induces the graded algebra homomorphism  $\Delta : H^{\bullet}(G) \to H^{\bullet}(G \times G) = H^{\bullet}(G) \otimes H^{\bullet}(G)$ , which is coassociative:

$$(\Delta \otimes id) \circ \Delta = (id \otimes \Delta) \circ \Delta.$$

(Note that the warning in Remark 45.11 about tensor product in the graded sense still applies here!) Such a map  $\Delta$  is called a **coproduct** since it defines an algebra structure on the dual space  $R^*$  (see Subsection 12.3). We also have the augmentation map  $\varepsilon: R \to \mathbb{C}$  such that

$$(\varepsilon \otimes 1)(\Delta(x)) = (1 \otimes \varepsilon)(\Delta(x)) = x$$

for all  $x \in R$ . Such a structure is called a **graded bialgebra**.<sup>31</sup>

**Exercise 46.1.** (Hopf theorem) Let R be a finite dimensional graded-commutatitive bialgebra over a field  $\mathbf{k}$  of characteristic zero, and  $R[0] = \mathbf{k}$  (where the grading is by nonnegative integers). Show that R is a **free** graded commutative algebra on some homogeneous generators of odd degrees, i.e.,  $R = \wedge_{\mathbf{k}}^{\bullet}(\xi_1, ..., \xi_r)$  with  $\deg \xi_i = 2m_i + 1$  for some nonnegative integers  $m_i$ . Thus  $\dim R = 2^r$ .

**Hint.** Recall from Subsection 14.1 that an element  $x \in R$  is **primitive** if  $\Delta(x) = x \otimes 1 + 1 \otimes x$ . Show that any homogeneous primitive x has odd degree (use that  $\dim R < \infty$ ), thus  $x^2 = 0$ , and that R is generated by homogeneous primitive elements. Then show that linearly independent primitive elements in R cannot satisfy any nontrivial relation (take a relation of lowest degree, compute its coproduct and find a relation of even lower degree, getting a contradiction).

For more hints see [C], Subsection 2.4.

Let us now determine the number r. We have  $2^r = \dim(\wedge^{\bullet}\mathfrak{g}^*)^{\mathfrak{g}}$ . But this dimension can be computed using the Weyl character formula. Namely, the character of  $\wedge^{\bullet}\mathfrak{g}^*$  is

$$\chi_{\wedge \bullet_{\mathfrak{g}^*}}(t) = 2^{\operatorname{rank}(\mathfrak{g})} \prod_{\alpha > 0} (1 + \alpha(t))(1 + \alpha(t)^{-1}),$$

where  $T \subset G$  is a maximal torus and  $t \in T$ . So

$$\dim(\wedge^{\bullet}\mathfrak{g}^*)^{\mathfrak{g}} = \frac{2^{\operatorname{rank}(\mathfrak{g})}}{|W|} \int_T \prod_{\alpha>0} (\alpha(t^2) - 1)(1 - \alpha(t^{-2}))dt = 2^{\operatorname{rank}(\mathfrak{g})}.$$

<sup>&</sup>lt;sup>31</sup>Moreover, we have an algebra homomorphism  $S: R \to R$  induced by the inversion map  $G \to G$  called the **antipode**. This makes R into what is called a **graded Hopf algebra**.

So  $r = \operatorname{rank}(\mathfrak{g})$ .

Thus we have

$$H^{\bullet}(G) = H^{\bullet}(\mathfrak{g}) = (\wedge^{\bullet}\mathfrak{g}^*)^{\mathfrak{g}} = \wedge^{\bullet}(\xi^{(1)}, ..., \xi^{(r)}),$$

where  $r = \text{rank}(\mathfrak{g})$ . and  $\deg(\xi^{(i)}) = 2m_i + 1$ . Moreover, it suffices to consider the case when  $\mathfrak{g}$  is simple. What are the numbers  $m_i$  in this case?

Let us order  $m_i$  as follows:  $m_1 \leq m_2 \leq ... \leq m_r$ . We know that  $r + 2\sum m_i = \dim \mathfrak{g}$ , so  $\sum_i m_i = |R_+|$ . Also it is not hard to see that  $m_1 = 1, m_2 > 1$ :

**Exercise 46.2.** Show that for a simple Lie algebra  $\mathfrak{g}$  we have  $(\wedge^3 \mathfrak{g}^*)^{\mathfrak{g}} = \mathbb{C}$ , spanned by the triple product ([xy], z).

**Hint.** Let  $\omega \in (\wedge^3 \mathfrak{g}^*)^{\mathfrak{g}}$ .

1. Show that

$$\omega(e_i, [f_i, h_i], h) + \omega(e_i, h_i, [f_i, h]) = 0$$

for  $h \in \mathfrak{h}$  and deduce that

$$\omega(e_i, f_i, h) = \frac{1}{2}\alpha_i(h)\omega(e_i, f_i, h_i).$$

2. Take  $y, z \in \mathfrak{h}$  and show that

$$\omega(h_i, y, z) + \omega(f_i, [e_i, y], z) + \omega(f_i, y, [e_i, z]) = 0.$$

Deduce that  $\omega(x,y,z)=0$  for  $x,y,z\in\mathfrak{h}$ . Conclude that  $\omega$  is completely determined by  $\omega(e_{\alpha},e_{-\alpha},h)$  for all roots  $\alpha$  and  $h\in\mathfrak{h}$ . Use the Weyl group to reduce to  $\omega(e_i,f_i,h)$  and then to  $\omega(e_i,f_i,h_i)$ .

3. Finally, use that

$$\omega([e_i,e_j],f_i,f_j) = \omega(e_j,f_j,h_i) = \omega(e_i,f_i,h_j)$$

to show that all possible  $\omega$  are proportional.

In particular, we see that for a simple compact connected Lie group G, one has  $H^3(G,\mathbb{C}) \cong \mathbb{C}$ . Thus, the sphere  $S^n$  admits a Lie group structure if and only if n = 0, 1, 3.

**Example 46.3.** We get  $m_2 = 2$  for  $A_2$ ,  $m_2 = 3$  for  $B_2 = C_2$ ,  $m_2 = 5$  for  $G_2$ . Thus the Poincaré polynomials  $P_{\mathfrak{g}}(q) := \sum_{n \geq 0} \dim H^n(G, \mathbb{C}) q^n$  for compact simple Lie groups of rank  $\leq 2$  are:

$$P_{A_1}(q) = 1 + q^3, \ P_{A_2}(q) = (1 + q^3)(1 + q^5),$$

$$P_{B_2}(q) = (1+q^3)(1+q^7), P_{G_2}(q) = (1+q^3)(1+q^{11}).$$

46.2. The cohomology ring of a simple compact connected Lie group. In fact, we have the following classical theorem, which we will not prove in general, but will prove below for type A and also in exercises for classical groups and  $G_2$ .

**Theorem 46.4.** Let G be a simple compact Lie group with complexified Lie algebra  $\mathfrak{g}$ . Then the numbers  $m_i$  are the exponents of  $\mathfrak{g}$  defined in Subsection 32.3. In other words, the degrees  $2m_i + 1$  of generators of the cohomology ring are the dimensions of simple modules occurring in the decomposition of  $\mathfrak{g}$  over its principal  $\mathfrak{sl}_2$ -subalgebra. Thus the cohomology ring  $H^{\bullet}(G,\mathbb{C})$  is the exterior algebra  $\wedge^{\bullet}(\xi_{2m_1+1},...,\xi_{2m_r+1})$ , where  $\xi_j$  has degree j.

A modern general proof of this theorem can be found in [R].

**Remark 46.5.** The Poincaré polynomial  $P_{\mathfrak{g}}(q)$  of  $(\wedge^{\bullet}\mathfrak{g}^*)^{\mathfrak{g}}$  is given by the formula

$$P_{\mathfrak{g}}(q) = \frac{(1+q)^r}{|W|} \int_T \prod_{\alpha \in B} (1+q\alpha(t)) \prod_{\alpha > 0} (\alpha(t)^{\frac{1}{2}} - \alpha(t)^{-\frac{1}{2}})^2.$$

So Theorem 46.4 is equivalent to the statement that this integral equals  $\prod_{i} (1 + q^{2m_i+1})$ .

We will prove Theorem 46.4 in the case of type A.

**Corollary 46.6.** For  $\mathfrak{g} = \mathfrak{sl}_n$  we have  $m_i = i$ . Equivalently, the same is true for  $\mathfrak{g} = \mathfrak{gl}_n$  if we add  $m_0 = 0$ .

*Proof.* Let  $\mathfrak{g} = \mathfrak{gl}_n$ ,  $V = \mathbb{C}^n$ . We need to compute the Poincaré polynomial of  $\wedge^{\bullet}(V \otimes V^*)^{\mathfrak{g}}$ . The skew Howe duality (Proposition 30.11) implies that this Poincaré polynomial is

$$P(q) = \sum_{\lambda = \lambda^t} q^{|\lambda|},$$

where the summation is over  $\lambda$  with  $\leq n$  parts. But there are exactly  $2^n$  such symmetric partitions  $\lambda$ : they consist of a sequence of hooks  $(k, 1^{k-1})$  with decreasing values of k, with each of them either present or not. The degree of such a hook is 2k-1, which implies that

(46.1) 
$$P_{\mathfrak{gl}_n}(q) = (1+q)(1+q^3)(1+q^5)...(1+q^{2n-1}).$$

Thus we get that the cohomology  $H^{\bullet}(U(n), \mathbb{C}) = H^{\bullet}(GL_n(\mathbb{C}), \mathbb{C})$  is  $\wedge^{\bullet}(\xi_1, \xi_3, ..., \xi_{2n-1})$  (where subscripts are degrees) with Poincaré polynomial (46.1), and  $H^{\bullet}(SU(n), \mathbb{C}) = H^{\bullet}(SL_n(\mathbb{C}), \mathbb{C}) = \wedge^{\bullet}(\xi_3, ..., \xi_{2n-1})$  with Poincaré polynomial  $(1+q^3)(1+q^5)...(1+q^{2n-1})$ .

In the next exercise and the following subsections we will use the notions of a **cell complex** and its **cellular homology and cohomology** with coefficients in any commutative ring, and the fact that if a manifold is equipped with a cell decomposition (i.e., represented as a disjoint union of cells) then its cellular cohomology with  $\mathbb{C}$ -coefficients (=dual to the cellular homology) is canonically isomorphic to the de Rham cohomology via the integration pairing (the **de Rham theorem**). More details can be found, for instance, in [H].

Exercise 46.7. (i) Give another proof of Theorem 46.4 for type  $A_{n-1}$  as follows. Use that  $SU(n)/SU(n-1) = S^{2n-1}$  to construct a cellular decomposition of SU(n) into  $2^{n-1}$  cells (use the decomposition of  $S^{2n-1}$  into a point and its complement). Then show that the differential in the corresponding cochain complex with  $\mathbb{C}$ -coefficients is zero (compare its dimension to the dimension of the cohomology). Derive Theorem 46.4 for SU(n) by induction in n.

- (ii) Use the same idea and the fact that  $U(n, \mathbb{H})/U(n-1, \mathbb{H}) = S^{4n-1}$  to establish Theorem 46.4 in type  $C_n$ . Conclude that the cohomology ring of  $U(n, \mathbb{H})$  (and  $\operatorname{Sp}_{2n}(\mathbb{C})$ ) is  $\wedge(\xi_3, \xi_7, ..., \xi_{4n-1})$  with Poincaré polynomial is  $(1+q^3)(1+q^7)...(1+q^{4n-1})$ .
- (iii) Show that these Poincaré polynomials are valid for cohomology of the same Lie groups with any coefficients.<sup>32</sup>
- 46.3. Cohomology of homogeneous spaces. Let G be a connected compact Lie group,  $\mathfrak{g} = \operatorname{Lie}(G)_{\mathbb{C}}$ ,  $K \subset G$  a closed subgroup,  $\mathfrak{k} = \operatorname{Lie}(K)_{\mathbb{C}}$ , and consider the homogeneous space G/K. How to compute the cohomology  $H^{\bullet}(G/K,\mathbb{C})$ ?

Since the group G acts on G/K, this cohomology is computed by the complex  $\Omega^{\bullet}(G/K)^G = (\wedge^{\bullet}(\mathfrak{g}/\mathfrak{k})^*)^K$ . Let us denote this complex by  $CE^{\bullet}(\mathfrak{g},K)$ . It is called the **relative Chevalley-Eilenberg complex**.

For example, if  $K = \Gamma$  is finite, this is just the  $\Gamma$ -invariant part of the usual Chevalley-Eilenberg complex. But  $\Gamma$  acts trivially on the cohomology, so we get  $H^{\bullet}(G/\Gamma) = H^{\bullet}(G)$  (as already noted above).

But what happens if  $\dim K > 0$ ? Can we describe the differential in this complex algebraically as we did for K = 1?

This question is answered by the following proposition. Let  $\mathfrak{k} \subset \mathfrak{g}$  be a pair of Lie algebras (not necessarily finite dimensional, over any field). Denote by  $CE^i(\mathfrak{g},\mathfrak{k})$  the spaces  $(\wedge^{\bullet}(\mathfrak{g}/\mathfrak{k})^*)^{\mathfrak{k}}$ .

**Proposition 46.8.**  $CE^{\bullet}(\mathfrak{g},\mathfrak{k})$  is a subcomplex of  $CE^{\bullet}(\mathfrak{g})$ .

 $<sup>^{32}</sup>$ A similar idea can be used to find the cohomology of Spin(n) (see Exercise 46.13 below) but it is a bit more complicated since there is no cell decomposition with zero boundary map, and thus any cell decomposition has strictly more than  $2^r$  cells for sufficiently large n (as there is 2-torsion in the integral cohomology).

Exercise 46.9. Prove Proposition 46.8.

Definition 46.10. The complex  $CE^{\bullet}(\mathfrak{g}, \mathfrak{k})$  is called the **relative Chevalley-Eilenberg complex**, and its cohomology is called the **relative Lie** algebra cohomology, denoted by  $H^{\bullet}(\mathfrak{g}, \mathfrak{k})$ .

Now note that, going back to the setting of compact Lie groups, we have  $CE^{\bullet}(\mathfrak{g},K) = CE^{\bullet}(\mathfrak{g},\mathfrak{k})^{K/K^{\circ}}$ , so we obtain

Corollary 46.11.  $H^{\bullet}(G/K, \mathbb{C}) \cong H^{\bullet}(\mathfrak{g}, \mathfrak{k})^{K/K^{\circ}}$  as algebras.

Thus, the computation of the cohomology of G/K reduces to the computation of the relative Lie algebra cohomology, which is again a purely algebraic problem.

Corollary 46.12. Suppose  $z \in K$  is an element that acts by -1 on  $\mathfrak{g}/\mathfrak{k}$ . Then  $(\wedge^i(\mathfrak{g}/\mathfrak{k})^*)^K = 0$  for odd i. Hence the differential in  $CE^{\bullet}(\mathfrak{g},K)$  vanishes and thus  $H^{\bullet}(G/K,\mathbb{C}) \cong (\wedge^{\bullet}(\mathfrak{g}/\mathfrak{k})^*)^K$ , with cohomology present only in even degrees.

Exercise 46.13. The real Stiefel manifold  $\operatorname{St}_{n,k}(\mathbb{R})$ , k < n, is the manifold of all orthonormal k-tuples of vectors in  $\mathbb{R}^n$ . For example,  $\operatorname{St}_{n,1}(\mathbb{R}) = S^{n-1}$  and  $\operatorname{St}_{n,n-1}(\mathbb{R}) = SO(n)$ .

- (i) Show that  $\operatorname{St}_{n,k}(\mathbb{R}) = SO(n)/SO(n-k)$  and hence  $\dim \operatorname{St}_{n,k}(\mathbb{R}) = k(n-k) + \frac{k(k-1)}{2}$ .
- (ii) Show that for  $n \geq 3$ , the manifold  $\operatorname{St}_{n,2}(\mathbb{R})$  is a fiber bundle over  $S^{n-1}$  with fiber  $S^{n-2}$ . Conclude that  $\operatorname{St}_{n,2}(\mathbb{R})$  has a cell decomposition with four cells of dimensions 0, n-2, n-1, 2n-3. Show that the boundary of the n-1-dimensional cell is zero if n is even and twice the n-2-dimensional cell if n is odd. Compute the cohomology groups of  $\operatorname{St}_{n,2}(\mathbb{R})$  with any coefficient ring. In particular, show that if n is odd then the cohomology groups with coefficients in any field of characteristic  $\neq 2$  are the same as for the sphere  $S^{2n-3}$ .
- (iii) Use the relative Chevalley-Eilenberg complex to compute the cohomology  $H^*(\mathrm{St}_{n,2}(\mathbb{R}),\mathbb{C})$  in another way. Compare to (ii).
- **Exercise 46.14.** (i) Prove Theorem 46.4 for type  $B_n$  using the method of Exercise 46.7. Namely, use that  $SO(2n+1)/SO(2n-1) = \operatorname{St}_{2n+1,2}(\mathbb{R})$  and Exercise 46.13(ii) or (iii). Conclude that the cohomology ring of SO(2n+1) (and  $SO_{2n+1}(\mathbb{C})$ ) over  $\mathbb{C}$  is  $\wedge^{\bullet}(\xi_3, \xi_7, ..., \xi_{4n-1})$  with Poincaré polynomial is  $(1+q^3)(1+q^7)...(1+q^{4n-1})$ .
- (ii) Use the conclusion of (i) for  $B_{n-1}$  and that  $SO(2n)/SO(2n-1) = S^{2n-1}$  to prove Theorem 46.4 for type  $D_n$  (again using the method of Exercise 46.7). Conclude that the cohomology ring of SO(2n) (and  $SO_{2n}(\mathbb{C})$ ) over  $\mathbb{C}$  is  $\wedge^{\bullet}(\xi_3, \xi_7, ..., \xi_{4n-5}, \eta_{2n-1})$  with Poincaré polynomial having the form  $(1+q^3)(1+q^7)...(1+q^{4n-5})\cdot (1+q^{2n-1})$ .

(iii) Show that these Poincaré polynomials are valid for cohomology of the same Lie groups with coefficients in any ring containing  $\frac{1}{2}$ .

### 47. Topology of Lie groups and homogeneous spaces, III

47.1. **Grassmannians.** Let  $G = U(m+n), K = U(n) \times U(m)$ , so that G/K is the **Grassmannian**  $G_{m+n,n}(\mathbb{C}) \cong G_{m+n,m}(\mathbb{C})$  (the manifold of m-dimensional or n-dimensional subspaces of  $\mathbb{C}^{m+n}$ ). The element  $z = I_n \oplus (-I_m)$  acts by -1 on  $\mathfrak{g}/\mathfrak{k} = V \otimes W^* \oplus W \otimes V^*$ , where V, W are the tautological representations of U(n) and U(m). So we get that the Grassmannian has cohomology only in even degrees, and

$$H^{2i}(G_{m+n,m}(\mathbb{C})) = \wedge^{2i}(V \otimes W^* \oplus W \otimes V^*)^{U(n) \times U(m)}$$

We can therefore use the skew Howe duality (Proposition 30.11) to see that

$$\dim H^{2i}(G_{m+n,m}(\mathbb{C})) = N_i(n,m),$$

where  $N_i(n, m)$  is the number of partitions  $\lambda = (\lambda_1, ..., \lambda_k)$  whose Young diagrams has i boxes and fit into the rectangle  $m \times n$  (i.e., such that  $k \leq m, \lambda_1 \leq n$ ).

To compute  $N_i(m,n)$ , consider the generating function

$$f_{n,m}(q) = \sum_{i} N_i(n,m)q^i.$$

Then, denoting by  $p_i$  the jumps  $\lambda_i - \lambda_{i+1}$  of  $\lambda$  (with  $p_0 = n - \lambda_1$ ), we have

$$\sum_{n>0} f_{n,m}(q)z^n =$$

$$\sum_{p_0,p_1,\dots,p_m\geq 0} z^{p_0+p_1+\dots+p_m} q^{p_1+2p_2+\dots+mp_m} = \prod_{j=0}^m \frac{1}{1-q^j z}.$$

So the Betti numbers of Grassmannians are the coefficients of this series. For example, if m=1 we get

$$\sum_{n>0} f_{n,m}(q)z^n = \frac{1}{(1-z)(1-qz)} = \sum_n (1+q+\ldots+q^n)z^n.$$

So we recover the Poincaré polynomial  $1 + q + ... + q^n$  of the complex projective space  $\mathbb{CP}^n$ . More precisely, this is the Poincaré polynomial evaluated at  $q^{\frac{1}{2}}$ , which is actually a polynomial in q since we have nontrivial cohomology only in even degrees.

The polynomials  $f_{n,m}(q)$  are called the Gaussian binomial coefficients and they can be computed explicitly. Namely, we have

#### Proposition 47.1.

$$f_{m,n}(q) = {m+n \choose n}_q = {m+n \choose m}_q = \frac{[m+n]_q!}{[m]_q![n]_q!},$$

where  $[m]_q := \frac{q^m - 1}{q - 1}$  and  $[m]_q! := [1]_q...[m]_q$ .

*Proof.* This follows immediately from the q-binomial theorem<sup>33</sup>

(47.1) 
$$\sum_{n \ge 0} {m+n \choose n}_q z^n = \prod_{j=0}^m \frac{1}{1 - q^j z}.$$

Exercise 47.2. Prove (47.1).

**Hint.** Let F(z) be the RHS of this identity. Write a q-difference equation expressing F(qz) in terms of F(z). Show that this equation has a unique solution such that F(0) = 1. Then prove that the LHS satisfies the same equation.

**Exercise 47.3.** Compute the Betti numbers of  $G_{N,2}(\mathbb{C})$ .

47.2. Schubert cells. There is actually a more geometric way to obtain the same result. This way is based on decomposing the Grassmannians into Schubert cells. Namely, let  $F_i \subset \mathbb{C}^{m+n}$  be spanned by the first i basis vectors  $e_1, ..., e_i$ ; thus

$$0 = F_0 \subset F_1 \subset ... \subset F_{m+n} = \mathbb{C}^{m+n}$$

Given an *m*-dimensional subspace  $V \subset \mathbb{C}^{m+n}$ , let  $\ell_j$  be the smallest integer for which  $\dim(F_{\ell_i} \cap V) = j$ . Then

$$1 \le \ell_1 < \ell_2 < \dots < \ell_m \le m + n,$$

which defines a partition with parts

$$\lambda_1 = \ell_m - m, \lambda_2 = \ell_{m-1} - m + 1, ..., \lambda_m = \ell_1 - 1$$

fitting in the  $m \times n$  box. Let  $S_{\lambda} \subset G_{m+n,m}(\mathbb{C})$  be the set of V giving such numbers  $\lambda_i$ .

**Exercise 47.4.** Show that  $S_{\lambda}$  is a locally closed embedded complex submanifold of the Grassmannian isomorphic to the affine space  $\mathbb{C}^{|\lambda|}$  of dimension  $|\lambda| = \sum_{i} \lambda_{i}$  (i.e., a closed embedded submanifold in an open subset of the Grassmannian).

**Hint.** Show that for  $V \in S_{\lambda}$ , the elements  $f_k := e_{\ell_k}^*|_V$  form a basis of  $V^*$ . For  $\ell_j + 1 \le i \le \ell_{j+1}$  (with  $\ell_{m+1} := m+n$ ), show that  $e_i^*|_V$  is a linear combination of  $f_k$ ,  $j+1 \le k \le m$ , and denote the corresponding

$$\sum_{n>0} \binom{m+n}{m} z^n = \frac{1}{(1-z)^{m+1}}.$$

 $<sup>^{33}</sup>$ Note that setting q=1 in the q-binomial theorem, we get the familiar formula from calculus, often called the binomial theorem:

coefficients by  $a_{ik}(V)$ . Show that the assignment  $V \mapsto (a_{ik}(V))$  is an isomorphism  $S_{\lambda} \cong \mathbb{C}^{|\lambda|}$ .

**Definition 47.5.** The subset  $S_{\lambda}$  of the Grassmannian is called the **Schubert cell** corresponding to  $\lambda$ .

So we see that  $G_{m+n,m}(\mathbb{C})$  has a **cell decomposition** into a disjoint union of Schubert cells.

Now we can rederive the same formula for the Poincaré polynomial of the Grassmannian from the following well-known fact from algebraic topology:

**Proposition 47.6.** If X is a connected cell complex which only has even-dimensional cells, then the cohomology of X vanishes in odd degrees, and the groups  $H^{2i}(X,\mathbb{Z})$  are free abelian groups of ranks  $b_{2i}(X)$ , where the Betti number  $b_{2i}(X)$  is just the number of cells in X of dimension i. Moreover, X is simply connected.

Indeed, the boundary map in this cell complex has to be zero, and its fundamental group must be trivial, as it is a quotient of the fundamental group of the 1-skeleton of X, which is a single point (why?).

So we obtain an even stronger statement than before:

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

**Remark 47.8.** We have a map  $\pi_m : \mathcal{F}_{m+n}(\mathbb{C}) \to G_{m+n,m}(\mathbb{C})$  sending  $(V_1, ..., V_{m+n-1})$  to  $V_m$ . This is a fibration with fiber  $\mathcal{F}_m(\mathbb{C}) \times \mathcal{F}_n(\mathbb{C})$ . This gives another proof of the formula for Betti numbers of the Grassmannian (Proposition 47.1).

We can also define the **partial flag manifold**  $\mathcal{F}_S(\mathbb{C})$ , where  $S \subset [1, n-1]$  is a subset, namely the space of **partial flags**  $(V_s, s \in S)$ ,  $V_s \subset \mathbb{C}^n$ , dim  $V_s = s$ ,  $V_s \subset V_t$  if s < t.

**Exercise 47.9.** Let  $S = \{n_1, n_1 + n_2, ..., n_1 + ... + n_{k-1}\}$ , and  $n_k = n - n_1 - ... - n_{k-1}$ . Show that the even Betti numbers of the partial flag manifold are the coefficients of the polynomial

$$P_S(q) := \frac{[n]_q!}{[n_1]_q!...[n_k]_q!}$$

called the Gaussian multinomial coefficient (and the odd Betti numbers vanish). Show that the partial flag manifold is simply connected.

#### 48. Levi decomposition

48.1. Cohomology of Lie algebras with coefficients. The definition of cohomology of Lie algebras may be generalized to define the cohomology with coefficients in a module, so that the cohomology considered above is the one for the trivial module.

Let  $\mathfrak{g}$  be a Lie algebra and V a  $\mathfrak{g}$ -module. The **Chevalley-Eilenberg** (or standard) complex of  $\mathfrak{g}$  with coefficients in V is defined by

$$CE^{\bullet}(\mathfrak{g}, V) := \operatorname{Hom}(\wedge^{\bullet}\mathfrak{g}, V)$$

with differential defined by the full Cartan formula (without dropping the first term):

$$d\omega(a_0, ..., a_m) = \sum_{i} (-1)^i a_i \omega(a_0, ..., \widehat{a}_i, ..., a_m) +$$

$$\sum_{i < j} (-1)^{i+j} \omega([a_i, a_j], a_0, ..., \widehat{a}_i, ..., \widehat{a}_j, ..., a_m).$$

The cohomology of this complex is called the **cohomology of g with** coefficients in V and denoted  $H^{\bullet}(\mathfrak{g}, V)$ . Note that the previously defined cohomology  $H^{\bullet}(\mathfrak{g})$  is  $H^{\bullet}(\mathfrak{g}, \mathbb{C})$ .

If  $\mathfrak{g}$  is the Lie algebra of a Lie group G (or its complexification) and V is finite dimensional, then we simply have  $CE^{\bullet}(\mathfrak{g},V):=(\Omega^{\bullet}(G)\otimes V)^{G}$  (and the differential is just the de Rham differential). So in particular by Theorem 45.5 we have (using that the smallest i>0 such that  $H^{i}(\mathfrak{g},\mathbb{C})\neq 0$  is 3):

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

**Proposition 48.2.** (i) If V, W are representations of  $\mathfrak{g}$  then  $\operatorname{Ext}^1(V, W) = H^1(\mathfrak{g}, \operatorname{Hom}_{\mathbf{k}}(V, W))$ .

(ii) Consider the action of the additive group of V on the Lie algebra  $\mathfrak{g} \ltimes V$  (with trivial commutator on V) by

$$v \circ (x, w) = (x, w + xv).$$

Then  $H^1(\mathfrak{g}, V)$  classifies Lie algebra homomorphisms  $\mathfrak{g} \to \mathfrak{g} \ltimes V$  of the form  $x \mapsto (x, \omega(x))$  modulo this action.

*Proof.* (i) Suppose the space  $W \oplus V$  is equipped with the action of  $\mathfrak{g}$  so that W is a submodule and V the quotient. Thus the action of  $\mathfrak{g}$  on  $W \oplus V$  is given by

$$\rho(x) = \begin{pmatrix} \rho_W(x) & \omega(x) \\ 0 & \rho_V(x) \end{pmatrix},$$

where  $\omega: \mathfrak{g} \to \operatorname{Hom}_{\mathbf{k}}(V, W)$ . So the identity  $\rho([x, y]) = [\rho(x), \rho(y)]$  translates into

$$\omega([x,y]) = \rho_W(x)\omega(y) - \omega(y)\rho_V(x) - \rho_W(y)\omega(x) + \omega(x)\rho_V(y).$$

i.e.,  $\rho \in Z^1(\mathfrak{g}, \operatorname{Hom}_{\mathbf{k}}(V, W))$ . Also it is easy to check that for two such representations  $\rho_1, \rho_2$  there is an isomorphism  $\rho_1 \to \rho_2$  acting trivially on W and V/W if and only if the corresponding maps  $\omega_1, \omega_2$  differ by a coboundary:  $\omega_1 - \omega_2 \in B^1(\mathfrak{g}, \operatorname{Hom}_{\mathbf{k}}(V, W))$ . This implies the statement.

- (ii) We leave this to the reader as an exercise.
- **3.**  $Z^1(\mathfrak{g},\mathfrak{g})$  is the Lie algebra of derivations of  $\mathfrak{g}$ , and  $B^1(\mathfrak{g},\mathfrak{g})$  is the ideal of inner derivations. So  $H^1(\mathfrak{g},\mathfrak{g})$  is the Lie algebra of **outer derivations**, the quotient of all derivations by inner derivations. In particular, we rederive the fact proved earlier that all derivations of a semisimple complex Lie algebra  $\mathfrak{g}$  are inner  $(H^1(\mathfrak{g},\mathfrak{g})=0)$ .
- **4.** Suppose we want to define an **abelian extension**  $\widetilde{\mathfrak{g}}$  of  $\mathfrak{g}$  by V, i.e., a Lie algebra which can be included in the short exact sequence

$$0 \to V \to \widetilde{\mathfrak{g}} \to \mathfrak{g} \to 0$$

where V is an abelian ideal. To classify such extensions, pick a vector space splitting  $\widetilde{\mathfrak{g}} = \mathfrak{g} \oplus V$ , then the commutator looks like

$$[(x, v), (y, w)] = ([x, y], xw - yv + \omega(x, y)),$$

where  $\omega : \wedge^2 \mathfrak{g} \to V$  is a linear map. The Jacobi identity is then equivalent to  $\omega$  being in the space  $Z^2(\mathfrak{g}, V)$  of 2-cocycles. Moreover, it is easy to check that for two such extensions  $\widetilde{\mathfrak{g}}_1, \widetilde{\mathfrak{g}}_2$  there is an isomorphism

 $\phi: \widetilde{\mathfrak{g}}_1 \to \widetilde{\mathfrak{g}}_2$  which acts trivially on V and  $\mathfrak{g}$  if and only if the corresponding cocycles  $\omega_1, \omega_2$  differ by a coboundary:  $\omega_1 - \omega_2 \in B^2(\mathfrak{g}, V)$ . Thus, we get

**Proposition 48.3.** Abelian extensions of  $\mathfrak{g}$  by V modulo isomorphisms which act trivially on V and  $\mathfrak{g}$  are classified by  $H^2(\mathfrak{g}, V)$ . For example, the space  $H^2(\mathfrak{g}, \mathbb{C})$  classifies 1-dimensional central extensions of  $\mathfrak{g}$ :

$$0 \to \mathbb{C} \to \widetilde{\mathfrak{g}} \to \mathfrak{g} \to 0.$$

**Example 48.4.** Let  $\mathfrak{g} = \mathbb{C}^2$  be the 2-dimensional abelian Lie algebra. Then we have seen that the Poincaré polynomial of the cohomology of  $\mathfrak{g}$  is  $1+2q+q^2$  (cohomology of the 2-torus). So  $H^2(\mathfrak{g},\mathbb{C})=\mathbb{C}$ . The only cocycle up to scaling is given by  $\omega(x,y)=1$ , where x,y is a basis of  $\mathfrak{g}$ , and all coboundaries are zero. So we have a central extension of  $\mathfrak{g}$  defined by this cocycle with basis x,y,c and [x,y]=c,[x,c]=[y,c]=0. This is the **Heisenberg Lie algebra**, which is isomorphic to the Lie algebra of strictly upper-triangular 3 by 3 matrices.

**5.** Let us now study deformations of Lie algebras. Suppose  $\mathfrak{g}$  is a Lie algebra over a field  $\mathbf{k}$  and we want to deform the bracket, with deformation parameter t. So the new bracket will be

$$[x, y]_t = [x, y] + tc_1(x, y) + t^2c_2(x, y) + ...,$$

where  $c_i : \wedge^2 \mathfrak{g} \to \mathfrak{g}$  are linear maps. This bracket should satisfy the Jacobi identity, i.e., define a new Lie algebra structure on  $\mathfrak{g}[[t]]$  (over  $\mathbf{k}[[t]]$ ). Such deformations are distinguished up to linear isomorphisms

$$a = 1 + ta_1 + t^2 a_2 + \dots$$

where  $a_i \in \operatorname{End}_{\mathbf{k}}(\mathfrak{g})$ .

In particular, in first order, i.e., modulo  $t^2$ , we get a new Lie algebra structure on  $\mathfrak{g}[t]/t^2\mathfrak{g}[t] = \mathfrak{g} \oplus t\mathfrak{g}$  such that this Lie algebra can be included in the short exact sequence

$$0 \to t\mathfrak{g} \to \mathfrak{g} \oplus t\mathfrak{g} \to \mathfrak{g} \to 0$$

where  $t\mathfrak{g} \cong \mathfrak{g}$  is an abelian ideal with adjoint action of  $\mathfrak{g}$  (note that this Lie algebra structure is automatically  $\mathbf{k}[t]/t^2$ -linear). So this is an abelian extension of  $\mathfrak{g}$  by  $t\mathfrak{g}$ , and we know that such extensions are classified by  $H^2(\mathfrak{g},\mathfrak{g})$ . So we obtain

**Proposition 48.5.** First-order deformations of  $\mathfrak{g}$  as a Lie algebra are classified by  $H^2(\mathfrak{g}, \mathfrak{g})$ .

Thus if  $H^2(\mathfrak{g},\mathfrak{g}) = 0$ , every deformation is isomorphic to the trivial one, with  $c_1 = c_2 = \dots = 0$ . Indeed, applying automorphisms

 $a = 1 + ta_1 + t^2a_2 + ...$ , we can kill successively  $c_1$ , then  $c_2$ , then  $c_3$ , and so on. Thus from Whitehead's theorem we obtain

Corollary 48.6. If  $\mathfrak{g}$  is semisimple then it is rigid, i.e., has no non-trivial Lie algebra deformations.

**Example 48.7.** Let  $\mathfrak{g}$  be the 2-dimensional abelian Lie algebra over  $\mathbb{C}$ . Then  $H^2(\mathfrak{g},\mathfrak{g})=\mathbb{C}^2$ , and we get a 2-parameter family of deformations with bracket [x,y]=tx+sy. These, however, turn out to be all equivalent (for  $(t,s)\neq (0,0)$ ) under the action of  $GL_2(\mathbb{C})$ : they are all isomorphic to the Lie algebra with basis x,y and commutator [x,y]=y.

However, not all first order deformations of a Lie algebra lift to second order, i.e., modulo  $t^3$ . Namely, the Jacobi identity in the second order tells us that  $dc_2 = [c_1, c_1]$ , where  $[c_1, c_1]$  is the **Schouten bracket** of  $c_1$  with itself:

$$[c_1, c_1](x, y, z) = c_1(c_1(x, y), z) + c_1(c_1(y, z), x) + c_1(c_1(z, x), y).$$

This expression is automatically a cocycle (check it!), but we need it to be a coboundary. So the cohomology class of  $[c_1, c_1]$  in  $H^3(\mathfrak{g}, \mathfrak{g})$  is an obstruction to lifting the deformation modulo  $t^3$ . Thus the space  $H^3(\mathfrak{g}, \mathfrak{g})$  is the home for **obstructions to deformations**. For example, if  $\mathfrak{g}$  is abelian then  $H^2(\mathfrak{g}, \mathfrak{g}) = \operatorname{Hom}_{\mathbf{k}}(\wedge^2 \mathfrak{g}, \mathfrak{g})$ , and the obstruction to extending  $c = tc_1$  modulo  $t^3$  is

$$\operatorname{Jacobi}(c_1) := [c_1, c_1] \in H^3(\mathfrak{g}, \mathfrak{g}) = \operatorname{Hom}_{\mathbf{k}}(\wedge^3 \mathfrak{g}, \mathfrak{g}).$$

**6.** In a similar way we can study deformations V[[t]] of a module V over  $\mathfrak{g}$ :

$$\rho_t(x) = \rho(x) + t\rho_1(x) + t^2\rho_2(x) + \dots$$

Modulo  $t^2$  we get a  $\mathfrak{g}$ -module structure on  $V[t]/t^2V[t]=V\oplus tV$  such that we have a short exact sequence

$$0 \to tV \to V \oplus tV \to V \to 0.$$

Thus first order deformations of V are classified by  $\operatorname{Ext}^1_{\mathfrak{g}}(V,V) = H^1(\mathfrak{g},\operatorname{End}_{\mathbf{k}}V)$ . Again, lifting of this deformation modulo  $t^3$  is not automatic, and we get an obstruction in  $\operatorname{Ext}^2_{\mathfrak{g}}(V,V) = H^2(\mathfrak{g},\operatorname{End}_{\mathbf{k}}(V))$ .

**Exercise 48.8.** (i) Let  $\mathfrak{a}, \mathfrak{g}$  be Lie algebras and  $\phi : \mathfrak{a} \to \mathfrak{g}$  a homomorphism. Show that first order deformations of  $\phi$  are classified by  $H^1(\mathfrak{a}, \mathfrak{g})$ , where  $a \in \mathfrak{a}$  acts on  $\mathfrak{g}$  by  $\mathrm{ad}\phi(a)$ .

- (ii) Show that if  $\mathfrak{a}$  is semisimple and  $\mathfrak{g}$  finite dimensional over  $\mathbb{C}$  then  $H^1(\mathfrak{a},\mathfrak{g})=0$ .
- (iii) Show that if  $\mathfrak{a}, \mathfrak{g}$  are semisimple complex Lie algebras then there are only finitely many homomorphisms  $\mathfrak{a} \to \mathfrak{g}$  up to conjugation by

 $G_{\mathrm{ad}}$ . (**Hint**: Consider the affine algebraic variety  $X \subset \mathrm{Hom}_{\mathbb{C}}(\mathfrak{a},\mathfrak{g})$  of all homomorphisms and show that the tangent space  $T_{\phi}X$  is  $Z^{1}(\mathfrak{a},\mathfrak{g})$ , the space of 1-cocycles. Then use (ii) to deduce that X is the union of finitely many orbits of  $G_{\mathrm{ad}}$ .)

(iv) How many conjugacy classes do we have in (iii) if  $\mathfrak{a} = \mathfrak{sl}_2$  and  $\mathfrak{g} = \mathfrak{sl}_n, \mathfrak{so}_n, \mathfrak{sp}_{2n}$ ?

#### 48.2. Levi decomposition.

**Theorem 48.9.** (Levi decomposition, Theorem 16.7) Over real or complex numbers we have  $\mathfrak{g} \cong \operatorname{rad}(\mathfrak{g}) \oplus \mathfrak{g}_{ss}$ , where  $\mathfrak{g}_{ss} \subset \mathfrak{g}$  is a semisimple subalgebra (but not necessarily an ideal); i.e.,  $\mathfrak{g}$  is isomorphic to the semidirect product  $\mathfrak{g}_{ss} \ltimes \operatorname{rad}(\mathfrak{g})$ . In other words, the projection  $p: \mathfrak{g} \to \mathfrak{g}_{ss}$  admits an (in general, non-unique) splitting  $q: \mathfrak{g}_{ss} \to \mathfrak{g}$ , i.e., a Lie algebra map such that  $p \circ q = \operatorname{Id}$ .

*Proof.* We can write  $\mathfrak{g} = \mathfrak{g}_{ss} \oplus \operatorname{rad}(\mathfrak{g})$  as a vector space. Then the commutator looks like

 $[(a, x), (b, y)] = ([x, b] - [y, a] + [a, b] + \omega(x, y), [x, y]), x, y \in \mathfrak{g}_{ss}, a, b \in rad(\mathfrak{g}).$ 

Let  $\operatorname{rad}(\mathfrak{g}) = D^0 \supset D^1 \supset \ldots$  be the upper central series of  $\operatorname{rad}(\mathfrak{g})$ , i.e.,  $D^{i+1} = [D^i, D^i]$ . Suppose  $D^n \neq 0$  but  $D^{n+1} = 0$  (so  $D^n$  is an abelian ideal). Using induction in dimension of  $\mathfrak{g}$  and replacing  $\mathfrak{g}$  by  $\mathfrak{g}/D^n$ , we may assume that  $\omega(x,y) \in D^n$ . But then  $\omega \in Z^2(\mathfrak{g}_{ss},D^n)$ , which equals  $B^2(\mathfrak{g}_{ss},D^n)$  by Whitehead's theorem, i.e.,  $\omega = d\eta$ . Using  $\eta$ , we can modify the splitting  $\mathfrak{g} = \mathfrak{g}_{ss} \oplus \operatorname{rad}(\mathfrak{g})$  to make sure that  $\omega = 0$ . This implies the statement.<sup>35</sup>

<sup>&</sup>lt;sup>35</sup>In other words, we have reduced to the case when  $rad(\mathfrak{g}) = V$  is abelian, and we have shown above that abelian extensions are classified by  $H^2(\mathfrak{g}_{ss}, V)$ , which is zero by Whitehead's theorem.

### 49. The third fundamental theorem of Lie theory

49.1. Exponentiating nilpotent and solvable Lie algebras and the third fundamental theorem of Lie theory. The following theorem implies the third fundamental theorem of Lie theory for solvable Lie algebras. Let  $\mathfrak{g}$  be a finite dimensional solvable Lie algebra over  $\mathbb{K} = \mathbb{R}$  or  $\mathbb{C}$  of dimension n.

**Theorem 49.1.** There is a simply connected Lie group G over  $\mathbb{K}$  with  $\text{Lie}(G) = \mathfrak{g}$ , diffeomorphic to  $\mathbb{K}^n$ . Moreover, if  $\mathfrak{g}$  is nilpotent then the exponential map  $\exp : \mathfrak{g} \to G$  is a diffeomorphism, and if we use it to identify G with  $\mathfrak{g}$  then the multiplication map  $\mu : \mathfrak{g} \times \mathfrak{g} \to \mathfrak{g}$  is polynomial.

Proof. The proof is by induction in n, with trivial base n=0. Namely, fix a nonzero homomorphism  $\chi: \mathfrak{g} \to \mathbb{K}$  (which exists since  $\mathfrak{g}$  is solvable), and let  $\mathfrak{g}_0 = \operatorname{Ker} \chi$ . Then we have  $\mathfrak{g} = \mathbb{K} \mathbf{d} \ltimes \mathfrak{g}_0$ , the semidirect product, where  $\mathbf{d} \in \mathfrak{g}$  acts as a derivation d on  $\mathfrak{g}_0$ . Let  $G_0$  be the simply connected Lie group corresponding to  $\mathfrak{g}_0$ , which is defined by the induction assumption. So we have a 1-parameter group of automorphisms  $e^{td}: \mathfrak{g}_0 \to \mathfrak{g}_0$  which by the second fundamental theorem of Lie theory gives rise to a 1-parameter group of automorphisms  $e^{td}: G_0 \to G_0$ . Thus we can define a group structure on  $G:=G_0 \times \mathbb{K}$  by the formula

$$(x,t) \cdot (y,s) = (x \cdot e^{td}(y), t+s), \ x, y \in G_0, \ t, s \in \mathbb{K}.$$

Otherwise formulated,  $G = \mathbb{K} \ltimes G_0$ . This gives a desired group G with Lie algebra  $\mathfrak{g}$ .

Moreover, if  $\mathfrak{g}$  is nilpotent then by the induction assumption the exponential map  $\mathfrak{g}_0 \to G_0$  is a diffeomorphism, and if we use it to identify  $\mathfrak{g}_0$  with  $G_0$  then the multiplication  $\mu_0 : \mathfrak{g}_0 \times \mathfrak{g}_0 \to \mathfrak{g}_0$  is polynomial. So we may realize G as  $\mathfrak{g} = \mathfrak{g}_0 \times \mathbb{K}$  with multiplication law

$$(X,t)*(Y,s) = \mu((X,t),(Y,s)) = (\mu_0(X,e^{td}(Y)),t+s), X,Y \in \mathfrak{g}_0, t,s \in \mathbb{K}.$$

By nilpotency  $d^N = 0$  for some N, so

$$e^{td}(Y) = \sum_{n=0}^{N-1} \frac{t^n d^n(Y)}{n!},$$

so we see that  $\mu$  is polynomial. Also

$$\exp(X, t) = (\exp(X_t), t),$$

where

$$X_{t} = \frac{e^{td} - 1}{td}(X) = \sum_{n=1}^{N} \frac{t^{n-1}d^{n-1}(X)}{n!}.$$

Thus

$$X = \left(\sum_{n=1}^{N} \frac{t^{n-1}d^{n-1}}{n!}\right)^{-1} (X_t),$$

which makes sense since  $d^N = 0$ . This implies that the exponential map for  $\mathfrak{g}$  is a diffeomorphism.

**Example 49.2.** Let  $\mathfrak{g}$  be the Heisenberg Lie algebra, i.e. the Lie algebra of strictly upper triangular 3-by-3 matrices. Then under such identification the multiplication map in the corresponding Heisenberg group G has the form

$$(x, y, z) * (x', y', z') = (x + x', y + y', z + z' + \frac{1}{2}(xy' - x'y)).$$

**Exercise 49.3.** Show that if  $\mathfrak{g}$  is the 2-dimensional non-abelian complex Lie algebra and G the corresponding simply connected Lie group then  $\exp : \mathfrak{g} \to G$  is not injective.

**Definition 49.4.** The simply connected Lie group whose Lie algebra is nilpotent is called **unipotent**.<sup>36</sup>

**Corollary 49.5.** (Third fundamental theorem of Lie theory, Theorem 9.13) For any finite dimensional Lie algebra  $\mathfrak{g}$  over  $\mathbb{R}$  or  $\mathbb{C}$  there is a simply connected Lie group G with  $\text{Lie}(G) = \mathfrak{g}$ .

*Proof.* By Theorem 49.1, we have such a group A for  $\mathfrak{a} = \operatorname{rad}(\mathfrak{g})$ . Moreover, by the Levi decomposition theorem, the simply connected semisimple group  $G_{ss}$  corresponding to  $\mathfrak{g}_{ss}$  acts on  $\operatorname{rad}(\mathfrak{g})$ . Hence by the second fundamental theorem of Lie theory,  $G_{ss}$  acts on A, and the simply connected Lie group  $G_{ss} \ltimes A$  has the Lie algebra  $\mathfrak{g}_{ss} \ltimes \operatorname{rad}(\mathfrak{g}) = \mathfrak{g}$ .

Corollary 49.6. A simply connected complex Lie group G is of the form  $G_{ss} \times A$ , where A is solvable simply connected, hence diffeomorphic to  $\mathbb{C}^n$ , and  $G_{ss}$  is a simply connected semisimple complex Lie group. Thus G has the homotopy type of  $G_{ss}^c$ .

49.2. Formal groups. The third fundamental theorem of Lie theory assigns a simply connected Lie group G to any finite dimensional Lie algebra  $\mathfrak{g}$  over  $\mathbb{R}$  or  $\mathbb{C}$ , such that Lie $G = \mathfrak{g}$ . But what about infinite dimensional Lie algebras? There are some examples when this is possible, for instance for  $\mathfrak{g} = \operatorname{Vect}(M)$ , the Lie algebra of vector fields for a smooth manifold M, we can take G to be the universal cover of

<sup>&</sup>lt;sup>36</sup>The reason for this terminology is that these groups act by unipotent operators on the adjoint representation.

 $\operatorname{Diff}_0(M)$ , the group of diffeomorphisms of M homotopic to the identity, and for  $\mathfrak{g}=C^\infty(S^1,\mathfrak{k})$  for a finite dimensional Lie algebra  $\mathfrak{k}$  we can take  $G=C^\infty(S^1,K)$ , where K is the simply connected Lie group corresponding to  $\mathfrak{k}$  (although we would need to explain in what sense G is a Lie group and  $\operatorname{Lie} G=\mathfrak{g}$ ). However, for a general infinite dimensional  $\mathfrak{g}$ , such an assignment is typically impossible and a suitable group G does not exist.

However, this assignment becomes possible (and in fact not just over  $\mathbb{R}$  and  $\mathbb{C}$  but over any field of characteristic zero) if we replace the notion of a Lie group with a purely algebraic notion of a **formal group**. Roughly speaking, the notion of a formal group is the analog of the notion of a real or complex analytic Lie group where analytic functions are replaced by formal power series, and we don't worry about their convergence. This allows us to work with infinite dimensional Lie algebras and over arbitrary fields of characteristic zero.

Let us give a precise definition. Given a vector space V over a field  $\mathbf{k}$  of characteristic zero, define the algebra  $\mathbf{k}[[V]]$  of **formal regular functions** on V to be  $(SV)^*$ , the dual of the symmetric algebra of V. Since SV has a bialgebra structure  $\Delta_0: SV \to SV \otimes SV$  defined by  $\Delta_0(v) = v \otimes 1 + 1 \otimes v$  for  $v \in V$ , the dual map  $\Delta_0^*$  gives a commutative associative product on  $\mathbf{k}[[V]]$ , which is continuous in the weak topology of the dual space. If  $x_i, i \in I$  is a linear coordinate system on V corresponding to a basis  $v_i, i \in I$ , then we have a natural identification  $\mathbf{k}[[V]] \cong \mathbf{k}[[x_i, i \in I]]$  of  $\mathbf{k}[[V]]$  with the algebra of formal power series in  $x_i$ . Note that here I can be a set of any cardinality, not necessarily finite or countable. Moreover, if dim  $V < \infty$  then  $\mathbf{k}[[V]] = \prod_{n \geq 0} S^n V^*$ .

Finally, note that we have the augmentation homomorphism (counit)  $\varepsilon : \mathbf{k}[[V]] \to \mathbf{k}$  given by  $\varepsilon(f) = f(0)$ , i.e., obtained by taking the quotient by the maximal ideal  $\mathbf{m} \subset \mathbf{k}[[V]]$ .

**Definition 49.7.** A formal group structure on V is a (topological) coproduct  $\Delta : \mathbf{k}[[V]] \to \mathbf{k}[[V \oplus V]]$ , i.e., a continuous<sup>38</sup> homomorphism which is coassociative and compatible with the counit:

$$(\Delta \otimes \operatorname{Id}) \circ \Delta(f) = (\operatorname{Id} \otimes \Delta) \circ \Delta(f), \ (\varepsilon \otimes \operatorname{Id}) \circ \Delta(f) = (\operatorname{Id} \otimes \varepsilon) \circ \Delta(f) = f.$$

A formal group over  $\mathbf{k}$  is a pair  $G = (V, \Delta)$ . We will denote  $\mathbf{k}[[V]]$  by  $\mathcal{O}(G)$  and call it the **algebra of regular functions** on G. We define the **dimension** of G by dim  $G := \dim V$ .

 $<sup>^{37}</sup>$ Recall that if E is a vector space then the dual space  $E^*$  carries the weak topology whose basis of neighborhoods of zero is given by orthogonal complements of finite dimensional subspaces of E.

<sup>&</sup>lt;sup>38</sup>Note that if dim  $V < \infty$ , any such homomorphism is automatically continuous.

A (homo)morphism of formal groups  $\phi: G_1 \to G_2$  is a (continuous) algebra homomorphism  $\mathcal{O}(G_2) \to \mathcal{O}(G_1)$  preserving the coproduct.<sup>39</sup>

For example, a 1-dimensional formal group is defined by a power series  $F(x,y) \in \mathbf{k}[[x,y]], \ F(x,y) = x+y+...$ , where ... denotes quadratic and higher terms, which is associative:

$$F(F(x,y),z) = F(x,F(y,z)).$$

Such a series F is called a **formal group law**. Namely, the map  $\Delta : \mathbf{k}[[x]] \to \mathbf{k}[[x_1, x_2]]$  is defined by the formula

$$\Delta(f)(x_1, x_2) = f(F(x_1, x_2)).$$

Higher-dimensional formal groups G can also be presented in this way, with F, x, y being vectors with dim G entries rather than scalars.

**Example 49.8.** 1. The additive formal group:  $\Delta(f) = f \otimes 1 + 1 \otimes f$ ,  $f \in V^*$ . In other words, F(x,y) = x + y and  $\Delta(f)(x,y) = f(x+y)$ .

2. Let G be a real or complex Lie group. Then the multiplication map  $G \times G \to G$  is smooth. So we can take its Taylor expansion at the unit element, which defines a formal group  $G_{\text{formal}}$  called the **formal completion of** G at the identity. Its coproduct is defined by the formula  $\Delta(f)(x,y) = f(x \circ y)$  where  $(x,y) \mapsto x \circ y$  denotes the group law of G. The same construction is valid for an algebraic group over any field.

So what does it have to do with groups? In fact, a lot: if G is a formal group then it defines a functor from the category of local commutative finite dimensional  $\mathbf{k}$ -algebras to the category of groups,

$$R \mapsto G(R) = \operatorname{Hom}_{\operatorname{continuous}}(\mathcal{O}(G), R)$$

(where the topology on R is discrete).<sup>40</sup> Namely, the group law on such homomorphisms is defined by

$$(a \circ b)(f) = (a \otimes b)(\Delta(f)).$$

This makes sense even though  $\Delta(f)$  does not belong to  $\mathbf{k}[[V]] \otimes \mathbf{k}[[V]]$  but only to its completion  $\mathbf{k}[[V \oplus V]]$  since R is finite dimensional.

**Exercise 49.9.** Show that  $(G(R), \circ)$  is a group.

<sup>&</sup>lt;sup>39</sup>Thus we forget the linear structure on V (it does not have to be preserved by homomorphisms). In other words, to specify a formal group, we don't need to specify a vector space V but only need to specify a (topological) ring isomorphic to  $\mathbf{k}[[V]]$  for some V and equipped with a coproduct.

Moreover, any (homo)morphism of formal groups  $G_1 \to G_2$  defines a morphism of functors  $G_1(?) \to G_2(?)$ , and this assignment is compatible with composition. Furthermore, it is not hard to show that this assignment can be inverted, which allows us to define formal groups as representable functors from local finite dimensional commutative algebras to groups.

Any formal group G defines a Lie algebra LieG, which as a vector space is the continuous dual  $\mathfrak{g}:=(\mathfrak{m}/\mathfrak{m}^2)^*$ . In other words, it is the underlying vector space V of  $G=(V,\Delta)$ . Note that by compatibility of  $\Delta$  with  $\varepsilon$ , for  $f\in\mathfrak{m}$  the element  $\Delta(f)-f\otimes 1-1\otimes f$  belongs to the completed tensor product  $\mathfrak{m}\widehat{\otimes}\mathfrak{m}$ , thus projects to a well defined element of  $(\mathfrak{g}\otimes\mathfrak{g})^*$ . Thus the same is true for the element  $\Delta(f)-\Delta^{\mathrm{op}}(f)$  (where  $\Delta^{\mathrm{op}}$  is obtained from  $\Delta$  by swapping components); in fact, it defines an element of  $(\wedge^2\mathfrak{g})^*$ . Moreover, this element only depends on the residue  $\overline{f}$  of f in  $\mathfrak{g}^*=\mathfrak{m}/\mathfrak{m}^2$  (check it!). Denote the projection of  $\Delta(f)-\Delta^{\mathrm{op}}(f)$  to  $(\wedge^2\mathfrak{g})^*$  by  $\delta(\overline{f})$ . Then  $\delta:\mathfrak{g}^*\to(\wedge^2\mathfrak{g})^*$  is continuous, so it is dual to the map  $[,]=\delta^*:\wedge^2\mathfrak{g}\to\mathfrak{g}$ , and it is easy to show that [,] is a Lie bracket on  $\mathfrak{g}$ ; namely, the Jacobi identity follows from the coassociativity of  $\Delta$  (check it!).

Conversely, given a Lie algebra  $\mathfrak{g}$  over  $\mathbf{k}$  (not necessarily finite dimensional), we can use the Baker-Campbell-Hausdorff formula (Subsection 14.3) to assign a formal group to  $\mathfrak{g}$ . Namely, take  $V = \mathfrak{g}$  and define  $\Delta : \mathbf{k}[[\mathfrak{g}]] \to \mathbf{k}[[\mathfrak{g} \oplus \mathfrak{g}]]$  by

$$\Delta(f)(x,y) = f(\mu(x,y)),$$

where  $\mu(x,y) = x + y + \frac{1}{2}[x,y] + \dots$  is the Baker-Campbell-Hausdorff series. Then the coassociativity of  $\Delta$  follows from the associativity of  $\mu$ . In other words, we define G by setting its formal group law F to be equal to  $\mu$ .

**Example 49.10.** Let  $\mathfrak{g}$  be a Lie algebra and G be the corresponding formal group. Let R be a finite dimensional local commutative algebra with maximal ideal  $\mathfrak{m}_R$ . Then  $G(R) = \mathfrak{m}_R \otimes \mathfrak{g}$  with group law

$$(x,y)\mapsto \mu(x,y)$$

(which makes sense since the series terminates).

**Theorem 49.11.** (The fundamental theorems of Lie theory for formal groups) These assignments are mutually inverse equivalences between the category of formal groups over  $\mathbf{k}$  and the category of Lie algebras over  $\mathbf{k}$ .

*Proof.* The proof is analogous to the proof of the first two fundamental theorems for usual Lie groups (but without the analytic details), and

we leave it as an exercise. Note that the third theorem, which was the hardest for usual Lie groups, assigning a group to a Lie algebra, has already been proved above by using the series  $\mu(x, y)$ .

**Corollary 49.12.** Every 1-dimensional formal group G over a field of characteristic zero is isomorphic to the additive formal group, with  $\Delta(f)(x,y) = f(x+y)$ .

Over a field of positive characteristic (or over a commutative ring, such as  $\mathbb{Z}$ ), much, but not all, of this story extends; let us for simplicity consider the finite dimensional case over a field. Namely, the definition of a formal group structure (say, on a finite dimensional space) is the same: it's a coproduct on  $\mathbf{k}[[x_1,...,x_n]]$  with the same properties as above. The definition of the Lie algebra of a formal group also goes along for the ride. However, the reverse assignment fails, since the series  $\mu(x,y)$  is only defined over  $\mathbb{Q}$  and has all primes occurring in denominators of its coefficients. As a result, not any Lie algebra gives rise to a formal group, and the fundamental theorems of Lie theory for formal groups don't hold.

In particular, there are many non-isomorphic 1-dimensional formal groups. For example, we have the additive group law F(x,y) = x+y as above, but also the **multiplicative group law** F(x,y) = x+y+xy, which is called so because this means that 1+F(x,y)=(1+x)(1+y). In characteristic zero these are isomorphic by the map

$$x \mapsto e^x - 1 = \sum_{n \ge 1} \frac{x^n}{n!},$$

(not surprisingly in view of Corollary 49.12), but in positive characteristic this series does not make sense and in fact the additive and multiplicative formal groups are not isomorphic (check it!). There are also many other 1-dimensional formal group laws, commutative and not. Such (commutative) formal group laws are very important in algebraic topology, since they parametrize (complex-oriented) cohomology theories. For example, the additive group law corresponds to ordinary cohomology and the multiplicative one to K-theory. In characteristic zero the isomorphism between the additive and multiplicative formal groups leads to the **Chern character map** which identifies cohomology and K-theory of a topological space with  $\mathbb{Q}$ -coefficients.

<sup>&</sup>lt;sup>41</sup>More precisely, instead of SV we should take the **symmetric algebra with divided powers**  $\Gamma V$ , defined by  $\Gamma^m V := (S^m V^*)^*$ . Note that in characteristic p,  $\Gamma^m V$  is not naturally isomorphic to  $S^m V$  for  $m \geq p$ .

#### 50. Ado's theorem

50.1. The nilradical. Consider now a solvable Lie algebra  $\mathfrak{a}$  over  $\mathbb{C}$  and its adjoint representation. By Lie's theorem, in some basis  $\mathfrak{a}$  acts in this representation by upper triangular matrices. Let  $\mathfrak{n} \subset \mathfrak{a}$  be the subset of nilpotent elements (the nilradical of  $\mathfrak{a}$ ). Thus  $\mathfrak{n}$  is the set of  $x \in \mathfrak{a}$  that act in this basis by strictly upper triangular matrices. In particular,  $\mathfrak{n} \supset [\mathfrak{a}, \mathfrak{a}]$ , so  $\mathfrak{a}/\mathfrak{n}$  is abelian.

**Proposition 50.1.** If  $d : \mathfrak{a} \to \mathfrak{a}$  is a derivation then  $d(\mathfrak{a}) \subset \mathfrak{n}$ . Thus if  $\mathfrak{a} = \operatorname{rad}(\mathfrak{g})$  is the radical of  $\mathfrak{g}$  then  $\mathfrak{g}$  acts trivially on  $\mathfrak{a}/\mathfrak{n}$ .

*Proof.* The derivation d defines a solvable Lie algebra  $\widetilde{\mathfrak{a}} := \mathbb{C}d \ltimes \mathfrak{a}$ , so  $[\widetilde{\mathfrak{a}}, \widetilde{\mathfrak{a}}] \subset \mathfrak{a}$  consists of nilpotent elements. In particular it lies in  $\mathfrak{n}$ .

50.2. Algebraic Lie algebras. Let us say that a finite dimensional complex Lie algebra  $\mathfrak{g}$  is algebraic if  $\mathfrak{g}$  is the Lie algebra of a group  $G = K \ltimes N$ , where K is a reductive group and N a unipotent group. It turns out that this is equivalent to being the Lie algebra of an **affine** algebraic group over  $\mathbb{C}$  (i.e., a closed subgroup in  $GL_n(\mathbb{C})$  defined by polynomial equations), which motivates the terminology.

A finite dimensional complex Lie algebra need not be algebraic:

**Example 50.2.** Let  $\mathfrak{g}_1$  be a 3-dimensional Lie algebra with basis d, x, y and [x, y] = 0, [d, x] = x,  $[d, y] = \sqrt{2}y$ . Similarly, let  $\mathfrak{g}_2$  have basis d, x, y with [x, y] = 0, [d, x] = x, [d, y] = y + x. Then  $\mathfrak{g}_1, \mathfrak{g}_2$  are not algebraic (check it!).

Nevertheless, we have the following proposition.

**Proposition 50.3.** Any finite dimensional complex Lie algebra is a Lie subalgebra of an algebraic one.

*Proof.* Let us say that  $\mathfrak{g}$  is n-algebraic if it is the Lie algebra of a group  $G := K \ltimes A$ , where K is reductive and  $\mathfrak{a} = \operatorname{Lie}(A)$  is solvable with  $\dim(\mathfrak{a}/\mathfrak{n}) \leq n$ , where  $\mathfrak{n}$  is the nilradical of  $\mathfrak{a}$ . Thus 0-algebraic is the same as algebraic. Note that for any  $\mathfrak{g}$  we have the Levi decomposition  $\mathfrak{g} = \mathfrak{g}_{ss} \ltimes \mathfrak{a}$ , where  $\mathfrak{a} = \operatorname{rad}(\mathfrak{g})$ , which shows that any  $\mathfrak{g}$  is n-algebraic for some n. So it suffices to show that any n-algebraic Lie algebra for n > 0 embeds into an n - 1-algebraic one.

<sup>&</sup>lt;sup>42</sup>Here is another proof of this proposition. The one-parameter group  $e^{td}$  of automorphisms of  $\mathfrak{a}$  preserves the set of characters of  $\mathfrak{a}$  occurring in its adjoint representation. Hence must preserve each of them individually, as there are finitely many and this group is connected. But by definition of  $\mathfrak{n}$  these characters span  $(\mathfrak{a}/\mathfrak{n})^*$ . Thus d acts trivially on  $\mathfrak{a}/\mathfrak{n}$ .

To this end, let  $\mathfrak{g} = \operatorname{Lie}(G)$  be n-algebraic, with  $G = K \ltimes A$  and A simply connected. Let  $\mathfrak{a} = \operatorname{Lie}(A)$ , so  $\dim(\mathfrak{a}/\mathfrak{n}) = n$ . Pick  $d \in \mathfrak{a}$ ,  $d \notin \mathfrak{n}$  such that d is K-invariant. This can be done since by Proposition 50.1 K acts trivially on  $\mathfrak{a}/\mathfrak{n}$  and its representations are completely reducible. We have a decomposition  $\mathfrak{a} = \bigoplus_{i=1}^r \mathfrak{a}[\beta_i]$  of  $\mathfrak{a}$  into generalized eigenspaces of d. It is clear that K preserves each  $\mathfrak{a}[\beta_i]$ . Pick a character  $\chi : \mathfrak{a} \to \mathbb{C}$  such that  $\chi(d) = 1$ .

Consider the subgroup  $\Gamma$  of  $\mathbb{C}$  generated by  $\beta_i$  and let  $\alpha_1, ..., \alpha_m$  be a basis of  $\Gamma$ , so that  $\beta_i = \sum_j b_{ij}\alpha_j$  for  $b_{ij} \in \mathbb{Z}$ . Let  $T = (\mathbb{C}^\times)^m$  and make T act on G so that it commutes with K and acts on  $\mathfrak{a}[\beta_i]$  by  $(z_1, ..., z_m) \mapsto \prod_j z_j^{b_{ij}}$ . Now consider the group  $\widetilde{G} := (K \times T) \ltimes A$ . Let  $\mathfrak{a}' \subset \operatorname{Lie}(T) \ltimes \mathfrak{a} \subset \operatorname{Lie}(\widetilde{G})$  be spanned by  $\operatorname{Ker}\chi$  and  $d - \alpha$  where  $\alpha = (\alpha_1, ..., \alpha_m) \in \operatorname{Lie}(T)$ . Then the nilradical  $\mathfrak{n}'$  of  $\mathfrak{a}'$  is spanned by  $\mathfrak{n}$  and  $d - \alpha$  (as the latter is nilpotent). Moreover, if A' is the simply connected group corresponding to  $\mathfrak{a}'$ , then  $(K \times T) \ltimes A \cong (K \ltimes T) \ltimes A'$  Thus, the Lie algebra  $\widetilde{\mathfrak{g}} := \operatorname{Lie}(\widetilde{G})$  is n - 1-algebraic (as  $\dim(\mathfrak{a}'/\mathfrak{n}') = n - 1$ ), and it contains  $\mathfrak{g}$ , as claimed.

**Example 50.4.** The Lie algebras  $\mathfrak{g}_1, \mathfrak{g}_2$  in the Example 50.2 are 1-algebraic.

To embed  $\mathfrak{g}_1$  into an algebraic Lie algebra, add element  $\delta$  with  $[\delta, x] = 0$ ,  $[\delta, y] = y$ ,  $[\delta, d] = 0$ . Then the Lie algebra  $\mathfrak{g}'_1$  spanned by  $\delta, d, x, y$  is  $\mathfrak{b} \oplus \mathfrak{b}$ , where  $\mathfrak{b}$  is the non-abelian 2-dimensional Lie algebra (so it is algebraic). Namely, the first copy of  $\mathfrak{b}$  is spanned by  $\delta, y$  and the second by  $d - \sqrt{2}\delta, x$ .

To embed  $\mathfrak{g}_2$  into an algebraic Lie algebra, add element  $\delta$  with  $[\delta, x] = 0$ ,  $[\delta, y] = x$ ,  $[\delta, d] = 0$ . Then the Lie algebra  $\mathfrak{g}_2'$  spanned by  $\delta, d, x, y$  is  $\mathbb{C} \times \mathcal{H}$ , where  $\mathcal{H}$  is the 3-dimensional Heisenberg Lie algebra with basis  $\delta, x, y$ , and  $\mathbb{C}$  is spanned by  $d - \delta$  (so it is algebraic, as  $d - \delta$  acts diagonalizably with integer eigenvalues).

50.3. Faithful representations of nilpotent Lie algebras. Let  $\mathfrak n$  be a finite dimensional nilpotent Lie algebra over  $\mathbb C$ . In this subsection we will show that  $\mathfrak n$  has a finite dimensional faithful representation.

To this end, recall that by Theorem 49.1,  $\mathfrak{n} = \text{Lie}(N)$  where N is a simply connected Lie group, and the exponential map  $\exp : \mathfrak{n} \to N$  is bijective. Moreover, the multiplication law of N, when rewritten on  $\mathfrak{n}$  using the exponential map, is given by polynomials.

**Proposition 50.5.** Let  $\mathcal{O}(N)$  be the space of polynomial functions on  $N \cong \mathfrak{n}$  (identified using the exponential map). Then  $\mathcal{O}(N)$  is invariant under the action of  $\mathfrak{n}$  by left-invariant vector fields. Moreover, we have

a canonical filtration  $\mathcal{O}(N) = \bigcup_{n \geq 1} V_n$ , where  $V_n \subset \mathcal{O}(N)$  are finite dimensional subspaces such that  $V_1 \subset V_2 \subset ...$  and  $\mathfrak{n}V_n \subset V_{n-1}$ .

*Proof.* Let  $\mu: \mathfrak{n} \times \mathfrak{n} \to \mathfrak{n}$  be the polynomial multiplication law. Let  $x \in \mathfrak{n}$  and  $L_x$  be the corresponding left-invariant vector field. Let  $f \in \mathcal{O}(N) = S\mathfrak{n}^*$ . Then for  $y \in \mathfrak{n}$  we have

$$(L_x f)(y) = \frac{d}{dt}|_{t=0} f(\mu(y, tx)).$$

Since f and  $\mu$  are polynomials, this is clearly a polynomial in y. Thus  $L_x: \mathcal{O}(N) \to \mathcal{O}(N)$ .

We have a lower central series filtration on  $\mathfrak{n}$ :

$$\mathfrak{n} = D_0(\mathfrak{n}) \supset [\mathfrak{n}, \mathfrak{n}] = D_1(\mathfrak{n}) \supset ... \supset D_m(\mathfrak{n}) = 0.$$

This gives an ascending filtration

$$0 = D_0(\mathfrak{n})^{\perp} \subset \dots \subset D_m(\mathfrak{n})^{\perp} = \mathfrak{n}^*.$$

We assign to  $D_j(\mathfrak{n})^{\perp}$  filtration degree  $d^j$ , where d is a sufficiently large positive integer. This gives rise to an ascending filtration  $F^{\bullet}$  on  $S\mathfrak{n}^* = \mathcal{O}(N)$ . Note that

$$\mu(x,y) = x + y + \sum_{i>1} Q_i(x,y),$$

where  $Q_i : \mathfrak{n} \times \mathfrak{n} \to [\mathfrak{n}, \mathfrak{n}]$  has degree i in x. Thus

$$(L_x f)(y) = (\partial_x f)(y) + (\partial_{Q_1(x,y)} f)(y).$$

The first term clearly lowers the degree, and so does the second one if d is large enough. So we may take  $V_n = F_n(S\mathfrak{n}^*)$  to be the space of polynomials of degree  $\leq n$ , then  $L_xV_n \subset V_{n-1}$ , as claimed.

**Example 50.6.** We illustrate this proof on the example of the Heisenberg algebra  $\mathcal{H} = \langle x, y, c \rangle$  with [x, y] = c and [x, c] = [y, c] = 0. In this case

$$e^{tx}e^{sy} = e^{tx + sy + \frac{1}{2}tsc},$$

so writing  $u = px + qy + rc \in \mathcal{H}$ , we get

$$\mu((p_1, q_1, r_1), (p_2, q_2, r_2)) = (p_1 + p_2, q_1 + q_2, r_1 + r_2 + \frac{1}{2}(p_1q_2 - p_2q_1)).$$

Thus

$$L_c = \partial_r, \ L_x = \partial_p - \frac{1}{2}q\partial_r, \ L_y = \partial_q + \frac{1}{2}p\partial_r.$$

We have  $D_1(\mathcal{H}) = \mathbb{C}c$ , so  $D_1(\mathcal{H})^{\perp}$  is spanned by p,q. Thus we have  $\deg(p) = \deg(q) = d$ ,  $\deg(r) = d^2$ . So for any d > 1,  $L_c, L_x, L_y$  lower the degree. So setting  $V_n = F_n(S\mathcal{H}^*)$  to be the (finite dimensional) space of polynomials of degree  $\leq n$ , we see that  $L_c, L_x, L_y$  map  $V_n$  to  $V_{n-1}$ .

Corollary 50.7. Every finite dimensional nilpotent Lie algebra  $\mathfrak n$  over  $\mathbb C$  has a faithful finite dimensional representation where all its elements act by nilpotent operators. Thus  $\mathfrak n$  is isomorphic to a subalgebra of the Lie algebra of strictly upper triangular matrices of some size.

*Proof.* By definition,  $\mathcal{O}(N)$  is a faithful  $\mathfrak{n}$ -module. Hence so is  $V_n$  for some n.

# 50.4. Faithful representations of general finite dimensional Lie algebras.

**Theorem 50.8.** (Ado's theorem) Every finite dimensional Lie algebra over  $\mathbb{C}$  has a finite dimensional faithful representation.

Proof. Let  $\mathfrak{g}$  be a finite dimensional complex Lie algebra. By Proposition 50.3,  $\mathfrak{g}$  can be embedded into an algebraic Lie algebra, so we may assume without loss of generality that  $\mathfrak{g}$  is algebraic. Thus  $\mathfrak{g} = \operatorname{Lie}(G)$  where  $G = K \ltimes N$  for reductive K and unipotent N. Also we may assume that  $\mathfrak{g} \neq \mathfrak{g}' \oplus \mathfrak{g}''$  for  $\mathfrak{g}', \mathfrak{g}'' \neq 0$ , otherwise the problem reduces to a smaller algebraic Lie algebra (indeed if V', V'' are faithful representations of  $\mathfrak{g}', \mathfrak{g}''$  then  $V' \oplus V''$  is a faithful representation of  $\mathfrak{g}' \oplus \mathfrak{g}''$ ). Then  $\mathfrak{k} = \operatorname{Lie}(K)$  acts faithfully on  $\mathfrak{n} = \operatorname{Lie}(N)$ . Now,  $\mathfrak{g}$  acts on  $\mathcal{O}(N)$  preserving the subspaces  $V_n$  ( $\mathfrak{n} = \operatorname{Lie}(N)$  acts by left invariant vector fields and  $\mathfrak{k}$  by the adjoint action).

As we have shown in the proof of Corollary 50.7,  $\mathfrak n$  acts faithfully on  $V_n$  for some n. We claim that this  $V_n$  is, in fact, a faithful representation of the whole  $\mathfrak g$ , which implies the theorem. Indeed, let  $\mathfrak a \subset \mathfrak g$  be the ideal of elements acting by zero on  $V_n$ , and let  $\overline{\mathfrak a}$  be the projection of  $\mathfrak a$  to  $\mathfrak k$  (an ideal in  $\mathfrak k$ ). Since  $\mathfrak n$  acts faithfully on  $V_n$ , we have  $\mathfrak a \cap \mathfrak n = 0$ . Given  $a \in \mathfrak a$ , we have  $a = \overline{a} + b$  where  $\overline{a} \in \overline{\mathfrak a}$  is the projection of a and  $b \in \mathfrak n$ . For  $x \in \mathfrak n$  we have  $[a, x] \in \mathfrak a \cap \mathfrak n = 0$ . Thus  $[\overline{a}, x] = -[b, x]$ . Hence the operator  $x \mapsto [\overline{a}, x]$  on  $\mathfrak n$  is nilpotent. So  $\overline{\mathfrak a}$  acts on  $\mathfrak n$  by nilpotent operators. Since K is reductive and  $\overline{\mathfrak a} \subset \mathfrak k$  is an ideal, this means that  $\overline{\mathfrak a}$  acts on  $\mathfrak n$  by zero. Thus  $\overline{\mathfrak a} = 0$  and  $\mathfrak a \subset \mathfrak n$ . Hence  $\mathfrak a = 0$ .

# 51. Borel subgroups and the flag manifold of a complex reductive Lie group

51.1. Borel subgroups and subalgebras. Let G be a connected complex reductive Lie group,  $\mathfrak{g} = \operatorname{Lie}(G)$ . Fix a Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g}$  with a system of simple positive roots  $\Pi$ , and consider the corresponding triangular decomposition  $\mathfrak{g} = \mathfrak{n}_- \oplus \mathfrak{h} \oplus \mathfrak{n}_+$ , where  $\mathfrak{n}_+$  is spanned by positive root elements and  $\mathfrak{n}_-$  by negative root elements. Let H be the maximal torus in G corresponding to  $\mathfrak{h}$ ,  $N_+$  the unipotent subgroup of G corresponding to  $\mathfrak{n}_+$ , and  $B_+ = HN_+$  the solvable subgroup with  $\operatorname{Lie}(B_+) = \mathfrak{b}_+ := \mathfrak{h} \oplus \mathfrak{n}_+$ ; these are all closed Lie subgroups.

**Definition 51.1.** A Borel subalgebra of  $\mathfrak{g}$  is a Lie subalgebra conjugate to  $\mathfrak{b}_+$ . A Borel subgroup of G is a Lie subgroup conjugate to  $B_+$ .

Since all pairs  $(\mathfrak{h}, \Pi)$  are conjugate, this definition does not depend on the choice of  $(\mathfrak{h}, \Pi)$ .

**Lemma 51.2.**  $B_+$  is its own normalizer in G.

Proof. Let  $\gamma \in G$  be such that  $\operatorname{Ad}\gamma(B_+) = B_+$ . Let  $H' = \operatorname{Ad}\gamma(H) \subset B_+$ . It is easy to show that we can conjugate H' back into H inside  $B_+$ , so we may assume without loss of generality that H' = H. Then  $\gamma \in N(H)$ , and it preserves positive roots. Hence the image of  $\gamma$  in W is 1, so  $\gamma \in H \subset B_+$ , as claimed.

51.2. The flag manifold of a connected complex reductive group. Thus the set of all Borel subalgebras (or subgroups) in G is the homogeneous space  $G/B_+$ , a complex manifold. It is called the flag manifold of G. Note that it only depends on the semisimple part  $\mathfrak{g}_{ss} \subset \mathfrak{g}$  and does not depend on the choice of the Cartan subalgebra and triangular decomposition.

Let  $G^c \subset G$  be the compact form of G, with Lie algebra  $\mathfrak{g}^c \subset \mathfrak{g}$ . It is easy to see that  $\mathfrak{g}^c + \mathfrak{b}_+ = \mathfrak{g}$ . Thus the  $G^c$ -orbit  $G^c \cdot 1$  of  $1 \in G/B_+$  contains a neighborhood of 1 in  $G/B_+$ . Hence the same holds for any point of this orbit, i.e.,  $G^c \cdot 1 \subset G/B_+$  is an open subset. But it is also compact, since  $G^c$  is compact, hence closed. As  $G/B_+$  is connected, we get that  $G^c \cdot 1 = G/B_+$ , i.e.,  $G^c$  acts transitively on  $G/B_+$ .

Also the Cartan involution  $\omega$  maps positive root elements to negative ones, so  $G^c \cap B_+ \subset w_0(B_+) \cap B_+ = H$ . Thus  $G^c \cap B_+ = H^c$ , a maximal torus in  $G^c$ . So we get

**Proposition 51.3.** We have  $G/B_+ = G^c/H^c$ . In particular,  $G/B_+$  is a compact complex manifold of dimension  $|R_+| = \frac{1}{2}(\dim \mathfrak{g} - \operatorname{rank}\mathfrak{g})$ .

**Example 51.4.** 1. For  $G = SL_2$  we have  $G/B_+ = SU(2)/U(1) = S^2$ , the Riemann sphere.

2. For  $G = GL_n$  we have  $G/B_+ = U(n)/U(1)^n = \mathcal{F}_n$ , the set of flags in  $\mathbb{C}^n$  that we considered in Subsection 47.3.

Another realization of the flag manifold is one as the G-orbit of the line spanned by the highest weight vector in an irreducible representation with a regular highest weight. Namely, let  $\lambda \in P_+$  be a dominant integral weight with  $\lambda(h_i) \geq 1$  for all i (i.e.,  $\lambda = \mu + \rho$  for  $\mu \in P_+$ ). Let  $L_{\lambda}$  be the corresponding irreducible representation with highest weight vector  $v_{\lambda}$ . We have  $\mathfrak{b}_+ \cdot \mathbb{C}v_{\lambda} = \mathbb{C}v_{\lambda}$ , but  $e_{-\alpha}v_{\lambda} \neq 0$  for any  $\alpha \in R_+$  (as  $e_{\alpha}e_{-\alpha}v_{\lambda} = h_{\alpha}v_{\lambda} = (\lambda, \alpha^{\vee})v_{\lambda}$ , and  $(\lambda, \alpha^{\vee}) > 0$ ). Moreover, these vectors have different weights, so are linearly independent. Thus  $\mathfrak{b}_+$  is the stabilizer of  $\mathbb{C}v_{\lambda}$  in  $\mathfrak{g}$ . Hence any  $g \in G$  which preserves  $\mathbb{C}v_{\lambda}$  belongs to the normalizer of  $\mathfrak{b}_+$  (or, equivalently,  $B_+$ ), i.e.,  $g \in B_+$ . Thus  $\mathcal{O} := G \cdot \mathbb{C}v_{\lambda} \subset \mathbb{P}L_{\lambda}$  is identified with  $G/B_+$ . This shows that  $\mathcal{O}$  is compact, hence closed, i.e.,  $\mathcal{O} = G/B_+$  is a smooth complex projective variety.

Let  $A = \exp(i\mathfrak{h}^c) \subset H$ ,  $K = G^c$ ,  $N = N_+$ . Proposition 51.3 immediately implies

Corollary 51.5. (The Iwasawa decomposition of G) The multiplication map  $K \times A \times N \to G$  is a diffeomorphism. In particular, we have G = KAN.

A similar theorem holds for *real* reductive groups (Theorem 51.14).

51.3. The Borel fixed point theorem. Let V be a finite dimensional representation of a finite dimensional  $\mathbb{C}$ -Lie algebra  $\mathfrak{a}$ , and  $X \subset \mathbb{P}V$  be a subset. We will say that X is  $\mathfrak{a}$ -invariant (or fixed by  $\mathfrak{a}$ ) if it is  $\exp(\mathfrak{a})$ -invariant.

**Theorem 51.6.** Let  $\mathfrak{a}$  be a solvable Lie algebra over  $\mathbb{C}$ , V a finite dimensional  $\mathfrak{a}$ -module. Let  $X \subset \mathbb{P}V$  be a closed  $\mathfrak{a}$ -invariant subset. Then there exists  $x \in X$  fixed by  $\mathfrak{a}$ .

*Proof.* The proof is by induction in  $n = \dim \mathfrak{a}$ . The base n = 0 is trivial, so we only need to justify the induction step. Since  $\mathfrak{a}$  is solvable, it has an ideal  $\mathfrak{a}'$  of codimension 1. By the induction assumption,  $Y := X^{\mathfrak{a}'}$  (the set of  $\exp(\mathfrak{a}')$ -fixed points in X) is a nonempty closed subset of X, so it suffices to show that the 1-dimensional Lie algebra  $\mathfrak{a}/\mathfrak{a}'$  has a fixed point on Y. Thus it suffices to prove the theorem for n = 1.

So let  $\mathfrak{a}$  be 1-dimensional, spanned by  $a \in \mathfrak{a}$ . We can choose the normalization of a so that all eigenvalues of a on V have different real parts. Fix  $x_0 \in X$  and consider the curve  $e^{ta}x_0$  for  $t \in \mathbb{R}$ . It is easy

to see that there exists  $x := \lim_{t \to \infty} e^{ta} x_0 \in \mathbb{P}V$ . Then  $x \in X$  as X is closed and, and x is fixed by  $\mathfrak{a}$ , as desired.

51.4. Parabolic and Levi subalgebras. A Lie subalgebra  $\mathfrak{p} \supset \mathfrak{b}$  of a reductive Lie algebra  $\mathfrak{g}$  containing some Borel subalgebra  $\mathfrak{b} \subset \mathfrak{g}$  is called a **parabolic subalgebra** of  $\mathfrak{g}$ . The corresponding connected Lie subgroup  $P \subset G$  is called a **parabolic subgroup**. It is easy to see that  $P \subset G$  is necessarily closed (check it!).

**Exercise 51.7.** Show that parabolic subalgebras  $\mathfrak{p}$  containing  $\mathfrak{b}_+$  are in bijection with subsets  $S \subset \Pi$  of the set of simple roots of  $\mathfrak{b}_+$ , namely,  $\mathfrak{p}$  is sent to the set  $S_{\mathfrak{p}}$  of  $i \in \Pi$  such that  $f_i \in \mathfrak{p}$ , and S is sent to the Lie subalgebra  $\mathfrak{p}_S$  of  $\mathfrak{g}$  generated by  $\mathfrak{b}_+$  and  $f_i, i \in S$ .

Let  $P \subset G$  be a parabolic subgroup with Lie algebra  $\mathfrak{p}$ . Let  $\mathfrak{u} \subset \mathfrak{p}$  be the nilpotent radical of  $\mathfrak{p}$ ; for instance, if  $\mathfrak{p} \supset \mathfrak{b}_+$  then  $\mathfrak{u}$  is the Lie subalgebra spanned by  $e_{\alpha}$  such that  $e_{-\alpha} \notin \mathfrak{p}$ . It is easy to see that there exists a (non-unique) Lie subalgebra  $\mathfrak{l} \subset \mathfrak{p}$  complementary to  $\mathfrak{u}$ , which therefore projects isomorphically to  $\mathfrak{p}/\mathfrak{u}$ ; indeed, if  $\mathfrak{p} \supset \mathfrak{b}_+$  then we can take  $\mathfrak{l}$  to be the Lie subalgebra spanned by  $\mathfrak{h}$  and  $e_{\alpha}, e_{-\alpha}$  where  $\alpha$  runs through positive roots for which  $e_{-\alpha} \in \mathfrak{p}$ . Such a subalgebra  $\mathfrak{l}$  is called a **Levi subalgebra** of  $\mathfrak{p}$ , and we have  $\mathfrak{p} = \mathfrak{l} \ltimes \mathfrak{u}$ , which is  $\mathfrak{l} \oplus \mathfrak{u}$  as a vector space.

Let  $U = \exp(\mathfrak{u})$ . The quotient P/U is a reductive group with Lie algebra  $\mathfrak{p}/\mathfrak{u}$ . A **Levi subgroup** of P is a subgroup L in P such that  $\mathfrak{l} := \operatorname{Lie}(L)$  is a Levi subalgebra of  $\mathfrak{p}$ ; equivalently, L projects isomorphically to P/U, so we have  $P = L \ltimes U$ , written shortly as P = LU. It is not difficult to show that all Levi subgroups of P (or, equivalently, all Levi subalgebras of  $\mathfrak{p}$ ) are conjugate by the action of U (check it!).

For example, L is a maximal torus if and only if P is a Borel subgroup, and L = G if and only if P = G.

**Example 51.8.** Let  $n = n_1 + ... + n_k$  where  $n_i$  are positive integers. Then the subgroup P of block upper triangular matrices with diagonal blocks of size  $n_1, ..., n_k$  is a parabolic subgroup of  $GL_n(\mathbb{C})$ , and the subgroup L of block diagonal matrices in P is a Levi subgroup. The unipotent radical U of P is the subgroup of block upper triangular matrices with identity matrices on the diagonal.

51.5. Maximal solvable and maximal nilpotent subalgebras. Note that  $\mathfrak{b}_+$  is a maximal solvable subalgebra of  $\mathfrak{g}$ ; indeed, any bigger parabolic subalgebra contains a negative root vector, hence the corresponding root  $\mathfrak{sl}_2$ -subalgebra, so it is not solvable. Moreover,  $B_+$  is a maximal solvable subgroup of G: if  $P \supset B_+$  then some element  $g \in P$ 

does not normalize  $\mathfrak{b}_+$ , so Lie(P) has to be larger than  $\mathfrak{b}_+$ , hence not solvable. Thus any Borel subalgebra (subgroup) is a maximal solvable one. It turns out that the converse also holds.

**Proposition 51.9.** Any solvable Lie subalgebra of  $\mathfrak{g}$  (respectively, connected solvable subgroup of G) is contained in a Borel subalgebra (subgroup).

*Proof.* Let  $\mathfrak{a} \subset \mathfrak{g}$  be a solvable Lie subalgebra. By the Borel fixed point theorem,  $\mathfrak{a}$  has a fixed point  $\mathfrak{b} \in G/B_+$ . Thus  $\mathfrak{a}$  normalizes  $\mathfrak{b}$ . Hence  $\mathfrak{a} \subset \mathfrak{b}$ , as claimed.

**Corollary 51.10.** Any element of  $\mathfrak{g}$  is contained in a Borel subalgebra  $\mathfrak{b} \subset \mathfrak{g}$ .

Let us say that a Lie subalgebra  $\mathfrak{a} \subset \mathfrak{g}$  is a nilpotent subalgebra if it consists of nilpotent elements. Note that this is a stronger condition than just being nilpotent as a Lie algebra; for example, a Cartan subalgebra is a nilpotent Lie algebra (since it is abelian) but it is not a nilpotent subalgebra of  $\mathfrak{g}$ .

Corollary 51.11. Any nilpotent subalgebra of  $\mathfrak g$  is conjugate to a Lie subalgebra of  $\mathfrak n_+$ . Thus  $\mathfrak n_+$  is a maximal nilpotent subalgebra of  $\mathfrak g$ , and any maximal nilpotent subalgebra of  $\mathfrak g$  is conjugate to  $\mathfrak n_+$ .

*Proof.* By Proposition 51.9 there is  $g \in G$  such that  $\mathrm{Ad}_g \mathfrak{a} \subset \mathfrak{b}_+$ , but since  $\mathfrak{a}$  is nilpotent we actually have  $\mathrm{Ad}_g \mathfrak{a} \subset \mathfrak{n}_+$ .

A similar result holds for groups, with the same proof:

Corollary 51.12. Any unipotent subgroup of G is conjugate to a (closed) Lie subgroup of  $N_+$ . Thus  $N_+$  is a maximal unipotent subgroup of G, and any maximal unipotent subgroup of G is conjugate to  $N_+$ .

We also have

**Proposition 51.13.** The normalizer of  $\mathfrak{n}_+$  and  $N_+$  in G is  $B_+$ . Thus every maximal nilpotent subalgebra (unipotent subgroup) is contained in a unique Borel subgroup. Hence such subalgebras (subgroups) are parametrized by the flag manifold  $G/B_+$ .

*Proof.* Clearly  $B_+$  is contained in the normalizer of  $N_+$ , so this normalizer is a parabolic subgroup. We have seen that such a subgroup, if larger than  $B_+$ , must have a Lie algebra larger that  $\mathfrak{b}_+$ , so it must be  $\mathfrak{p}_S$  for some  $S \neq \emptyset$ , hence contains some root  $\mathfrak{sl}_2$ -subalgebra. But the group corresponding to such a subalgebra does not normalize  $\mathfrak{n}_+$ , a contradiction.

51.6. Iwasawa decomposition of a real semisimple linear group. Let  $G_{\theta} = K^{c}P_{\theta}$  be the polar decomposition of a real form of a complex semisimple group G,  $\mathfrak{g}_{\theta} = \mathfrak{k}^{c} \oplus \mathfrak{p}_{\theta}$  the additive version,  $\mathfrak{a} \subset \mathfrak{p}_{\theta}$  a maximal abelian subspace. Let  $A = \exp(\mathfrak{a}) \subset P_{\theta}$  be the corresponding abelian subgroup of  $G_{\theta}$ . Pick a generic element  $a \in \mathfrak{a}$ . Let  $\mathfrak{z} = \mathfrak{g}_{\theta}^{a}$  be the centralizer of a in  $\mathfrak{g}_{\theta}$  and let  $\mathfrak{n}_{a,\pm}$  be the (nilpotent) Lie subalgebras of  $\mathfrak{g}_{\theta}$  spanned by eigenvectors of ada with positive, respectively negative eigenvalues, so that  $\mathfrak{g}_{\theta} = \mathfrak{n}_{a-} \oplus \mathfrak{z} \oplus \mathfrak{n}_{a+}$ . Let  $N_{a\pm} = \exp(\mathfrak{n}_{a\pm})$ .

The following theorem is a generalization of Proposition 51.5.

**Theorem 51.14.** (Iwasawa decomposition) The multiplication map  $K^c \times A \times N_{a+} \to G_\theta$  is a diffeomorphism.

Theorem 51.14 is proved in the following exercise.

**Exercise 51.15.** (i) Let  $\mathfrak{m} = \mathfrak{z} \cap \mathfrak{k}^c$ . Show that  $\mathfrak{z} = \mathfrak{m} \oplus \mathfrak{a}$  (use Proposition 44.11(ii)).

- (ii) Given  $x \in \mathfrak{p}$ , write  $x = x_- + x_0 + x_-$ ,  $x_{\pm} \in \mathfrak{n}_{a\pm}$ ,  $x_0 \in \mathfrak{z}$ . Show that  $\theta(x_{\pm}) = -x_{\mp}$ ,  $\theta(x_0) = -x_0$ . Deduce the **additive Iwasawa** decomposition  $\mathfrak{g}_{\theta} = \mathfrak{k}^c \oplus \mathfrak{a} \oplus \mathfrak{n}_{a+}$  (write x as  $(x_- x_+) + x_0 + 2x_+$ ).
- (iii) Show that  $\mathfrak{z} \oplus \mathfrak{n}_{a+} = \mathfrak{m} \oplus \mathfrak{a} \oplus \mathfrak{n}_{\mathfrak{a}+}$  is a parabolic subalgebra in  $\mathfrak{g}_{\theta}$  with Levi subalgebra  $\mathfrak{z}$  (i.e., their complexifications are a parabolic subalgebra in  $\mathfrak{g}$  and its Levi subalgebra) and its unipotent radical is  $\mathfrak{n}_{a+}$ .
- (iv) Let M be the centralizer of a in  $K^c$ . Show that  $\mathbb{P} := MAN_{a+}$  is a subgroup of  $G_{\theta}$  and  $X := G_{\theta}/\mathbb{P}$  is a compact homogeneous space.
- (v) Show that  $K^c$  acts transitively on X, and  $X \cong K^c/M$  as a homogeneous space for  $K^c$  (generalize the argument in Subsection 51.2). Deduce Theorem 51.14.
- 51.7. **The Bruhat decomposition.** Let G be a connected complex reductive group,  $H \subset G$  a maximal torus,  $B = B_+ \supset H$  a Borel subgroup. The Bruhat decomposition is the decomposition of G into double cosets of B.

Let N(H) be the normalizer of H in G and W = N(H)/H be the Weyl group. Given  $w \in W$ , let  $\widetilde{w}$  be a lift of w to N(H) and consider the double coset  $B\widetilde{w}B \subset G$ . Since any two lifts of w differ by an element of H which is contained in B, the set  $B\widetilde{w}B$  does not depend on the choice of  $\widetilde{w}$ , so we will denote it by BwB.

**Proposition 51.16.** The double cosets BwB,  $w \in W$  are disjoint.

Proof. Let  $w_1, w_2 \in N(H)$  be such that  $Bw_1B = Bw_2B$ . Then there exist elements  $b_1, b_2 \in B$  such that  $b_1w_1 = w_2b_2$ . Let us apply this identity to a highest weight vector  $v_{\lambda}$  of an irreducible representation

 $L_{\lambda}$  of G, where  $\lambda \in P_{+}$  is regular. We have  $w_{2}b_{2}v_{\lambda} = Cv_{w_{2}\lambda}$  for some  $C \in \mathbb{C}^{\times}$ , where  $v_{w_{2}\lambda}$  is an extremal vector of weight  $w_{2}\lambda$ . On the other hand,  $b_{1}w_{1}v_{\lambda} = C'b_{1}v_{w_{1}\lambda}$  for some  $C' \in \mathbb{C}^{\times}$ . Thus  $Cv_{w_{2}\lambda} = C'b_{1}v_{w_{1}\lambda}$ . But  $b_{1}v_{w_{1}\lambda}$  equals  $C''v_{w_{1}\lambda}$  plus terms of weight  $> w_{1}\lambda$ , where  $C'' \in \mathbb{C}^{\times}$ . It follows that  $w_{1}\lambda = w_{2}\lambda$ , hence  $w_{1} = w_{2}h$ ,  $h \in H$ .

**Theorem 51.17.** (Bruhat decomposition) The union of the double cosets BwB,  $w \in W$  is the entire group G. Thus they define a partition of G into double cosets of B.

Theorem 51.17 can be reformulated as a classification of B-orbits on the flag manifold G/B. Namely, given  $w \in W$ , the set BwB/B is an orbit of B on G/B, which we will denote by  $C_w$ . By Theorem 51.16,  $C_w$  are disjoint, and Theorem 51.17 is equivalent to

**Theorem 51.18.** (Schubert decomposition)  $C_w, w \in W$  give the partition of G/B into B-orbits.

The sets BwB are called **Bruhat cells** and the sets  $C_w$  are called **Schubert cells**.<sup>43</sup>

Note that for type  $A_{n-1}$  ( $G = SL_n(\mathbb{C})$  or its quotient), we have already proved Theorem 51.18 in Subsection 47.3, where we decomposed the flag manifold  $\mathcal{F}_n$  into Schubert cells labeled by permutations.

A proof of Theorem 51.18 can be found, for example, in the textbook [CG]. It is also sketched in the following exercise.

**Exercise 51.19.** (i) Let  $B = B_+$  and  $w \in W$ . Consider the multiplication map  $\mu_{i,w} : Bs_iB \times_B C_w \to G/B$ . Show that if  $\ell(s_iw) = \ell(w) + 1$  then  $\mu_{i,w}$  is an isomorphism onto  $C_{s_iw}$ , while if  $\ell(s_iw) = \ell(w) - 1$  then the image of  $\mu_{i,w}$  consists of  $C_w$  and  $C_{s_iw}$ .

**Hint:** Reduce to the  $SL_2$ -case.

- (ii) For  $i \in \Pi$  let  $P_i$  be the **minimal parabolic** subgroup of G generated by B and the 1-parameter subgroup  $\exp(tf_i)$ . Show that  $P_i/B = C_{s_i} \cup C_1 \cong \mathbb{CP}^1 \subset G/B$  (where  $C_1$  is a point and  $C_{s_i} \cong \mathbb{C}$ ).
- (iii) Let  $w = s_{i_1}...s_{i_l}$  be a reduced decomposition of  $w \in W$  (so  $l = \ell(w)$ ); denote this decomposition by  $\overline{w}$ . The product  $\prod_{k=1}^{l} P_{i_k}$  carries a free action of  $B^l$  via

$$(b_1,...,b_l) \circ (p_1,...,p_l) := (p_1b_1^{-1},b_1p_2b_2^{-1},...,b_{l-1}p_lb_l^{-1}).$$

Define the **Bott-Samelson variety**  $X_{\overline{w}} := (\prod_{k=1}^{l} P_{i_k})/B^l$ . Use (ii) to show that if  $\overline{w} = s_i \overline{u}$  then  $X_{\overline{w}}$  fibers over  $\mathbb{CP}^1$  with fiber  $X_{\overline{u}}$ . Deduce that  $X_{\overline{w}}$  is a smooth projective variety of dimension  $\ell(w)$ .

<sup>&</sup>lt;sup>43</sup>We note that Bruhat cells, unlike Schubert cells, are not literally cells in the topological sense – they are not homeomorphic to an affine space, but are homeomorphic to the product of an affine space and a torus.

# (iv) Define the **Bott-Samelson map**

$$\mu_{\overline{w}}: X_{\overline{w}} \to G/B$$

given by multiplication. Use (i) to show that the image of  $\mu_{\overline{w}}$  is the **Schubert variety**  $\overline{C}_w$ , the closure of  $C_w$  in G/B. Moreover, show that  $\overline{C_w} \setminus C_w$  is the union of  $C_u$  over some  $u \in W$  with  $\ell(u) < \ell(w)$ .

(v) Apply (iv) to the maximal element  $w = w_0 \in W$ . In this case, show that  $\mu_{\overline{w}}$  is surjective, and deduce Theorem 51.18.

Let us derive some corollaries of Theorem 51.18.

**Corollary 51.20.** (i) Any pair of Borel subgroups of G is conjugate to the pair (B, w(B)) for a unique  $w \in W$ . In particular, any two Borel subgroups of G share a maximal torus.

(ii) The cell  $C_w$  is isomorphic to  $\mathbb{C}^{\ell(w)}$ .

*Proof.* (i) Let  $(B_1, B_2)$  be a pair of Borel subgroups in G. Then we can conjugate  $B_1$  to B, and  $B_2$  will be conjugated to some Borel subgroup  $B_3$ . This subgroup is conjugate to B, i.e., is of the form  $gBg^{-1}$  for some  $g \in G$ . By Bruhat decomposition, we can write g as  $g = b_1 \widetilde{w} b_2$ ,  $b_1, b_2 \in B$ ,  $\widetilde{w} \in N(H)$ . So conjugating by  $b_1^{-1}$ , we will bring our pair to the required form (B, w(B)), where w is the image of  $\widetilde{w}$  in W. Uniqueness follows from Proposition 51.16.

(ii) By (i) we have  $C_w \cong B/(B \cap w(B))$ . Since B = NH, where N = [B, B] and  $B \cap w(B) \supset H$ , we get  $C_w = N/(N \cap w(B)) = N/(N \cap w(N))$ . This is a complex affine space of dimension equal to the number of positive roots mapped to negative roots by w, i.e.,  $\ell(w)$ .

Corollary 51.21. The Poincaré polynomial of the flag manifold G/B is

$$\sum_{i>0} b_{2i}(G/B)q^{i} = \sum_{w \in W} q^{\ell(w)}.$$

**Remark 51.22.** Similarly to the type A case, one can show that this polynomial can also be written as  $\prod_{i=1}^{r} [m_i + 1]_q$ , where  $m_i$  are the exponents of G, but we will not give a proof of this identity.

#### References

- [C] P. Cartier, A Primer of Hopf algebras, 2006, http://preprints.ihes.fr/ 2006/M/M-06-40.pdf
- [CR] D. Calaque, C. Rossi, Lectures on Duflo Isomorphisms in Lie Algebra and Complex Geometry, EMS Series of Lectures in Mathematics, v. 14, 2011.
- [CG] N. Chriss, V. Ginzburg, Representation theory and complex geometry, Springer, 2020.

- [E] P. Etingof, O. Golberg, S. Hensel, T. Liu, A. Schwendner, D. Vaintrob, E. Yudovina, with historical interludes by S. Gerovitch, AMS, 2011, http://www-math.mit.edu/~etingof/reprbook.pdf
- [FH] W. Fulton, J. Harris, Representation theory, a first course, Graduate texts in Mathematics, Springer, 1991.
- [H] A. Hatcher, Algebraic topology, Cambridge University Press, 2002.
- [Hu] J. Humphreys, Introduction to Lie algebras and representation theory, Graduate texts in mathematics, Springer, 2017.
- [J] N. Jacobson, Lie algebras, Dover, 1979.
- [K] A. Kirillov Jr., An introduction to Lie groups and Lie algebras, Cambridge University Press, 2008.
- [Kn] A, Knapp, Lie groups beyond an introduction, Springer, 1996.
- [M] J. Munkres, Topology, Second edition, Pearson, 2000.
- [Mu] M. Müger, Notes on the theorem of Baker-Campbell-Hausdorff-Dynkin, https://www.math.ru.nl/~mueger/PDF/BCHD.pdf
- [OV] A. Onishchik, E. Vinberg, Lie groups and algebraic groups, Springer-Verlag, 1990.
- [R] M. Reeder, On the Cohomology of Compact Lie Groups. L'Ens. Math. 41(1995),181–200.

18.755 Lie Groups and Lie Algebras II Spring 2024

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.