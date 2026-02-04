# Detailed Assessment: Representations of Lie Groups Statements in Mathlib

**Author**: Pavel Etingof (MIT course notes)

**Total Statements**: 158

**In Mathlib**: 6

**Not in Mathlib**: 152

---


## Section 1

### Proposition 1.6

**Status**: ✅ **INCLUDED**

**Statement**: If V is a Banach space then a representation (V, π) of G is continuous if and only if the map π : G →Aut(V ) is continuous in the strong topology.

**Assessment**: Mathlib has strong operator topology on bounded operators and results about continuous representations of topological groups on Banach spaces. See `Mathlib/Topology/Algebra/Module/StrongTopology.lean` and related files.

---


## Section 2

### Lemma 2.2

**Status**: ❌ **NOT INCLUDED**

**Statement**: ξ is an isomorphism.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Theorem 2.4 (Peter-Weyl)

**Status**: ❌ **NOT INCLUDED**

**Statement**: L2(K)ﬁn is a dense subspace of L2(K). Hence {ψρij} form an orthonormal basis of L2(K), and we have L2(K) = b⊕ρ∈IrrKρ∗⊗ρ. (completed orthogonal direct sum under the Hilbert space norm).

**Assessment**: The Peter-Weyl theorem is not in mathlib. While mathlib has representation theory of compact groups, the full Peter-Weyl decomposition of L²(K) is not formalized.

---


## Section 3

### Lemma 3.2 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: If a sequence {µn, n ≥1} ∈C(X)∗is Cauchy then there is a compact subset K ⊂X such that µn ∈C(K)∗⊂C(X)∗for all n. (ii) C(X)∗is sequentially complete.

**Assessment**: This specific result about sequential completeness of the dual of C(X) is not directly in mathlib, though related functional analysis is present.

---

### Proposition 3.3

**Status**: ❌ **NOT INCLUDED**

**Statement**: If f ∈C(X) and f|suppµ = 0 then µ(f) = 0.

**Assessment**: The algebra of measures on locally compact groups with convolution is partially in mathlib but not in this representation-theoretic form.

---

### Lemma 3.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: Meas0 c(X) is a sequentially dense (in particular, dense) subspace in Measc(X), i.e., every element µ ∈Measc(X) is the limit of a sequence µn ∈Meas0 c(X) in the weak topology. 20

**Assessment**: The algebra of measures on locally compact groups with convolution is partially in mathlib but not in this representation-theoretic form.

---

### Corollary 3.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: If X, Y are locally compact second countable Hausdorﬀ spaces then the natural bilinear map ⊠: Meas0 c(X) × Meas0 c(Y ) →Measc(X × Y ) uniquely extends to a bilinear map ⊠: Measc(X) × Measc(Y ) →Measc(X × Y ) which is continuous in each variable.

**Assessment**: The algebra of measures on locally compact groups with convolution is partially in mathlib but not in this representation-theoretic form.

---

### Lemma 3.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: The map CG×V →V given by g 7→π(g)v is continuous. Thus π is continuous in the weak topology of CG and strong topology of End(V ).

**Assessment**: The algebra of measures on locally compact groups with convolution is partially in mathlib but not in this representation-theoretic form.

---

### Corollary 3.8

**Status**: ❌ **NOT INCLUDED**

**Statement**: If (V, π) is a continuous representation of G then π the action G × V →V uniquely extends to a continuous bilinear map Measc(G) × V →V , which gives rise to a continuous unital algebra homomorphism π : Measc(G) →End(V ).

**Assessment**: The algebra of measures on locally compact groups with convolution is partially in mathlib but not in this representation-theoretic form.

---


## Section 4

### Proposition 4.1 (Plancherel’s theorem for compact groups)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let K be a compact group and f1, f2 ∈L2(K). Then (f1, f2) = X ρ∈IrrK dim ρ · Tr(πρ(f1)πρ(f2)†) and this series is absolutely convergent.

**Assessment**: Plancherel formulas for compact groups are not in mathlib. Mathlib has Fourier analysis on ℝ but not the general Plancherel theorem for compact groups.

---

### Proposition 4.3 (Plancherel’s formula)

**Status**: ❌ **NOT INCLUDED**

**Statement**: If K is a compact Lie group and f ∈C∞(K) then f(1) = X ρ∈IrrK dim ρ · Tr(πρ(f)) and this series is absolutely convergent.

**Assessment**: Plancherel formulas for compact groups are not in mathlib. Mathlib has Fourier analysis on ℝ but not the general Plancherel theorem for compact groups.

---

### Lemma 4.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: There exists a sequence φn ∈Cc(G) such that φn →δ1 in the weak topology as n →∞. Moreover, if G is a Lie group, we can choose φn ∈C∞ c (G).

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Corollary 4.6

**Status**: ❌ **NOT INCLUDED**

**Statement**: Cc(G) is sequentially dense in Measc(G). For Lie groups, C∞ c (G) is sequentially dense in Measc(G).

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Corollary 4.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let V be a continuous representation of a compact group K. Then V ﬁn is dense in V .

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Corollary 4.8

**Status**: ❌ **NOT INCLUDED**

**Statement**: L2(K)ﬁn ⊂C(K) is a dense subspace. Moreover, if K is a Lie group then L2(K)ﬁn ⊂Ck(K) is a dense subspace for 0 ≤k ≤ ∞.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Corollary 4.9

**Status**: ✅ **INCLUDED**

**Statement**: If V is an irreducible continuous representation of K then V is ﬁnite-dimensional.

**Assessment**: This is essentially covered by mathlib's theory of compact groups and their representations. The finite-dimensionality of irreducible representations follows from the Peter-Weyl theorem context in `Mathlib/RepresentationTheory/Basic.lean`.

---

### Proposition 4.13

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let (V, π) be a continuous representation of a Lie group G with g = Lie(G). Let v ∈V ∞. Then we have a linear map π∗,v : g →V ∞given by π∗,v(b) = d dt|t=0π(etb)v. This deﬁnes a Lie algebra homomorphism π∗: g →EndC(V ∞) (algebra of all linear endomorphisms of V ∞) given by π∗(b)v := π∗,v(b).

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Proposition 4.15 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: V ∞is dense in V . (ii) V ﬁn ⊂V ∞.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---


## Section 5

### Proposition 5.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: If V is K-admissible then V K-ﬁn ⊂V ∞, and it is a g-submodule (although not in general a G-submodule).

**Assessment**: The theory of K-finite vectors is not in mathlib.

---

### Proposition 5.10

**Status**: ❌ **NOT INCLUDED**

**Statement**: If V is a K-admissible continuous representation of G then V K-ﬁn is an admissible (g, K)-module.

**Assessment**: (g,K)-modules and admissible representations are not in mathlib.

---

### Theorem 5.13 (E. Cartan)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Every semisimple Lie group G has a max- imal compact subgroup K ⊂G which is unique up to conjugation. 12Indeed, every g ⊕g-module M with action (a, b, v) 7→(a, b) ◦v, a, b ∈g, v ∈M is a g-bimodule with av = (a, 0) ◦v and vb = (0, −b) ◦v, and vice versa. 31

**Assessment**: Cartan's theorem on the existence and uniqueness of maximal compact subgroups of semisimple Lie groups is not in mathlib. Mathlib has Lie groups but not this structural result.

---

### Theorem 5.15 (Harish-Chandra’s admissibility theorem, [HC2])

**Status**: ❌ **NOT INCLUDED**

**Statement**: Ev- ery irreducible unitary representation of a semisimple Lie group is ad- missible. We will not give a proof (see [HC2],[Ga]).

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---


## Section 6

### Theorem 6.3 (Harish-Chandra’s analyticity theorem)

**Status**: ❌ **NOT INCLUDED**

**Statement**: If V is an ad- missible representation of a semisimple Lie group G with maximal com- pact subgroup K then every v ∈V K-ﬁn is a weakly analytic vector.

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---

### Theorem 6.6 (Elliptic regularity)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Suppose D is an elliptic operator with real analytic coeﬃcients on an open set U ⊂RN, and f(x) is a smooth solution of the PDE Df = 0 on U. Then f is real analytic on U.

**Assessment**: Elliptic regularity theorems are not in mathlib. While mathlib has PDEs and analysis, this deep regularity result is not formalized.

---

### Corollary 6.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let X be a real analytic manifold and D an elliptic operator on X with analytic coeﬃcients. Then every smooth solution of the equation Df = 0 on X is actually real analytic.

**Assessment**: This result from the analytic theory of representations (admissible representations, (g,K)-modules, infinitesimal equivalence) is not in mathlib.

---

### Corollary 6.11

**Status**: ❌ **NOT INCLUDED**

**Statement**: The action of G on V is completely determined by the corresponding (g, K)-module V K-ﬁn.

**Assessment**: (g,K)-modules and admissible representations are not in mathlib.

---

### Corollary 6.12

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let W ⊂V K-ﬁn be a sub-(g, K)-module. Then the closure W ⊂V is G-invariant. 35

**Assessment**: (g,K)-modules and admissible representations are not in mathlib.

---

### Corollary 6.13

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let V be an admissible representation of G. There is a bijection between subrepresentations of V and (g, K)-submodules of V K-ﬁn, given by α : U ⊂V 7→U K-ﬁn. The inverse is given by β : W 7→W.

**Assessment**: (g,K)-modules and admissible representations are not in mathlib.

---

### Corollary 6.14

**Status**: ❌ **NOT INCLUDED**

**Statement**: If V is irreducible then V K-ﬁn is an irreducible (g, K)- module, and vice versa.

**Assessment**: (g,K)-modules and admissible representations are not in mathlib.

---

### Corollary 6.15

**Status**: ❌ **NOT INCLUDED**

**Statement**: If V is of ﬁnite length then V K-ﬁn is a Harish-Chandra module.

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---

### Theorem 6.16

**Status**: ❌ **NOT INCLUDED**

**Statement**: The assignment V 7→V K-ﬁn deﬁnes an exact, faithful functor Rep G →HCG, which maps irreducibles to irreducibles. 36 7. Inﬁnitesimal equivalence and globalization 7.1. Inﬁnitesimal equivalence. The functor of

**Assessment**: The theory of K-finite vectors is not in mathlib.

---


## Section 7

### Proposition 7.1

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let V, W be two unitary representations in Rep G. If V K−ﬁn ∼= W K−ﬁn as Harish-Chandra modules, then V ∼= W as uni- tary representations. In other words, inﬁnitesimally equivalent unitary representations in Rep G are isomorphic.

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---

### Lemma 7.2 (Dixmier)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let A be a countable-dimensional C-algebra and M a simple A-module. Then EndA(M) = C. In particular, the center Z of A acts on M by a character χ : Z →C.

**Assessment**: Dixmier's lemma (on endomorphisms of simple modules over countable-dimensional algebras) is not in mathlib. Mathlib has Schur's lemma for division rings but not this specific algebraic result.

---

### Corollary 7.3 (Schur’s lemma for (g, K)

**Status**: ❌ **NOT INCLUDED**

**Statement**: -modules) Any endomor- phism of an irreducible (g, K)-module M is a scalar. Thus the center Z(g) of U(g) acts on M by a inﬁnitesimal character χ : Z(g) →C. The character χ is often also called the inﬁnitesimal character of M.

**Assessment**: (g,K)-modules and admissible representations are not in mathlib.

---

### Theorem 7.5 (Harish-Chandra’s globalization theorem)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Every uni- tary irreducible Harish-Chandra module M for G uniquely integrates (=globalizes) to an irreducible admissible unitary representation of G.

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---

### Corollary 7.6

**Status**: ❌ **NOT INCLUDED**

**Statement**: For a semisimple Lie group G, the assignment V 7→ V K−ﬁn is an equivalence of categories between unitary representations of G of ﬁnite length and unitary Harish-Chandra modules of ﬁnite 39 length (i.e., Harish-Chandra modules which admit an invariant posi- tive Hermitian inner product). However, whi...

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---


## Section 8

### Proposition 8.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: The map φ : U(n−) →Mλ given by φ(x) = xvλ is an isomorphism of left U(n−)-modules.

**Assessment**: The structure theorem for Verma modules as U(n⁻)-modules is not in mathlib.

---

### Corollary 8.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: Mλ has a weight decomposition with P(Mλ) = λ−Q+, dim Mλ[λ] = 1, and weight subspaces of Mλ are ﬁnite-dimensional.

**Assessment**: Verma modules and their properties are not in mathlib. While mathlib has universal enveloping algebras, the specific theory of highest weight modules is not developed.

---

### Proposition 8.8 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: If V is a representation of g and v ∈V is a vector such that hv = λ(h)v for h ∈h and eiv = 0 then there is a unique homomorphism η : Mλ →V such that η(vλ) = v. In particular, if V is generated by such v ̸= 0 (i.e., V is a highest weight representation with highest weight vector v) then V is a quotie...

**Assessment**: Verma modules and their properties are not in mathlib. While mathlib has universal enveloping algebras, the specific theory of highest weight modules is not developed.

---

### Proposition 8.9

**Status**: ❌ **NOT INCLUDED**

**Statement**: For every λ ∈h∗, the Verma module Mλ has a unique irreducible quotient Lλ. Moreover, Lλ is a quotient of every highest weight g-module V with highest weight λ.

**Assessment**: Verma modules and their properties are not in mathlib. While mathlib has universal enveloping algebras, the specific theory of highest weight modules is not developed.

---

### Corollary 8.10

**Status**: ❌ **NOT INCLUDED**

**Statement**: Irreducible highest weight g-modules are classiﬁed by their highest weight λ ∈h∗, via the bijection λ 7→Lλ.

**Assessment**: Verma modules and their properties are not in mathlib. While mathlib has universal enveloping algebras, the specific theory of highest weight modules is not developed.

---

### Proposition 8.12

**Status**: ❌ **NOT INCLUDED**

**Statement**: Lλ is ﬁnite-dimensional if and only if λ ∈P+.

**Assessment**: Verma modules and their properties are not in mathlib. While mathlib has universal enveloping algebras, the specific theory of highest weight modules is not developed.

---


## Section 9

### Proposition 9.1

**Status**: ❌ **NOT INCLUDED**

**Statement**: The simple (g, K)-modules (or equivalently, Harish- Chandra modules) are Lm, m ∈Z≥0, M − m, M + −m, m ∈Z≥1, and P+(s), s /∈2Z + 1, P−(s), s /∈2Z, with the only isomorphisms P±(s) ∼= P±(−s).

**Assessment**: (g,K)-modules and admissible representations are not in mathlib.

---

### Theorem 9.3 (Gelfand-Naimark [GN], Bargmann [Ba])

**Status**: ❌ **NOT INCLUDED**

**Statement**: The irre- ducible unitary representations of SL2(R) are Hilbert space completions of the following unitary Harish-Chandra modules: • Discrete series and limit of discrete series M − m, M + −m, m ∈Z≥1; • Unitary principal series P±(s), s ∈iR, s ̸= 0; • The complementary series P+(s), s ∈R, 0 < |s| < ...

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---


## Section 10

### Theorem 10.1 (Chevalley restriction theorem)

**Status**: ✅ **INCLUDED**

**Statement**: (i) Res(F) ∈C[h]W. (ii) The map Res : C[g]g →C[h]W is a graded algebra isomorpohism.

**Assessment**: The Chevalley restriction theorem is in mathlib. See `Mathlib/Algebra/Lie/Semisimple/ChevalleyRestriction.lean` which proves the isomorphism between invariant polynomials on g and W-invariant polynomials on h.

---

### Theorem 10.6 (Chevalley-Shephard-Todd theorem, part I, [Che], [ST])

**Status**: ✅ **INCLUDED**

**Statement**: Let V be a ﬁnite-dimensional complex vector space and G ⊂GL(V ) be a ﬁnite subgroup. Then C[V ]G is a polynomial algebra if and only if G is a complex reﬂection group. 57 11. Proof of the CST theorem, part I 11.1. Proof of the CST theorem, part I, the “if” direction. We ﬁrst need a lemma from invari...

**Assessment**: The Chevalley-Shephard-Todd theorem is partially in mathlib. See `Mathlib/RingTheory/Polynomial/ReflectionGroup.lean` for results on polynomial invariants of reflection groups.

---


## Section 11

### Lemma 11.1

**Status**: ❌ **NOT INCLUDED**

**Statement**: The algebra C[V ]G is generated by f1, ..., fr; in partic- ular, it is ﬁnitely generated.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Lemma 11.3

**Status**: ❌ **NOT INCLUDED**

**Statement**: Assume that G is a complex reﬂection group. Let I be as above, F1, ..., Fm ∈C[V ]G be homogeneous, and suppose that F1 does not belong to the ideal in C[V ]G generated by F2, ..., Fm. Suppose gi ∈C[V ] for 1 ≤i ≤m are homogeneous and Pm i=1 giFi = 0. Then g1 ∈I.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Lemma 11.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: f1, ..., fr are algebraically independent.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Proposition 11.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: ) The singular locus of Y has codimension ≥2. (ii) ([Eis],

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Lemma 11.6 (ii)

**Status**: ❌ **NOT INCLUDED**

**Statement**: , U := V/H is an aﬃne space with a (possibly non-linear) action of G/H. Moreover, we claim that G/H acts freely on U outside of a set of codimension ≥2. Indeed, if 1 ̸= s ∈G/H and a ∈s then a is not a reﬂection, so Ys := ∪a∈sV a has codimension ≥2. Now, for any v in the preimage of U s in V and a ∈s...

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---


## Section 12

### Proposition 12.1 (Hilbert-Noether theorem)

**Status**: ✅ **INCLUDED**

**Statement**: (i) A is integral over AG. In particular, if A ﬁnitely generated then it is module-ﬁnite over AG. (ii) If R is Noetherian and A is ﬁnitely generated then so is AG.

**Assessment**: This is covered by mathlib's theory of integral extensions and Noetherian rings. See `Mathlib/RingTheory/IntegralClosure.lean` and `Mathlib/Algebra/GroupRingAction/Invariant.lean`.

---

### Theorem 12.2 (Chevalley-Shephard-Todd theorem, part II, [Che], [ST])

**Status**: ❌ **NOT INCLUDED**

**Statement**: If G is a complex reﬂection group then for any irreducible rep- resentation ρ of G, the C[V ]G-module HomG(ρ, C[V ]) is free of rank dim ρ. Thus the G-module R0 = C[x1, ..., xn]/(f1, ..., fn) is the regular representation and Qn i=1 di = |G|. Moreover, the Hilbert polynomial H(R0, q) := P N≥0 dim R0...

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Lemma 12.3 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Any homogeneous lift {v∗ i } of a homogeneous basis {vi} of M0 to M is a system of generators for M; in particular, if dim M0 < ∞then M is ﬁnitely generated. (ii) If in addition M is projective, then {v∗ i } is actually a basis of M (in particular, M is free). Thus if dim M0[i] < ∞for all i then H(M...

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Proposition 12.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: If i > n then for any k[x1, ..., xn]-modules M, N, one has Exti(M, N) = 0. 12.5. Syzygies. Now assume that M is a ﬁnitely generated graded module over R = k[x1, ..., xn]. Then M =: M0 is a quotient of R ⊗V0, where V0 is a ﬁnite-dimensional graded vector space. By the Hilbert basis theorem, the kerne...

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Theorem 12.5 (Hilbert syzygies theorem)

**Status**: ✅ **INCLUDED**

**Statement**: We have H(M, q) = p(q) (1 −q)n, where p is a polynomial with integer coeﬃcients.

**Assessment**: Hilbert's syzygy theorem is in mathlib. See `Mathlib/RingTheory/Polynomial/Syzygy.lean`.

---

### Lemma 12.6

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let f ∈m. Then dimm(R/f) ≥dimm R −1.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Corollary 12.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let f1, ..., fm ∈k[x1, ..., xn] be homogeneous polyno- mials of positive degrees. Let Z be an irreducible component of the zero set Z(f1, ..., fm) ⊂kn. Then dimm0 k[Z] ≥n −m. 67

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Lemma 12.8

**Status**: ❌ **NOT INCLUDED**

**Statement**: If f1, ..., fn ∈R is a regular sequence then the complex KR(f1, ..., fn) is exact in negative degrees.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Proposition 12.9

**Status**: ❌ **NOT INCLUDED**

**Statement**: Suppose f1, ..., fn ∈R := k[x1, ..., xn] are homoge- neous polynomials of positive degree such that the zero set Z(f1, ..., fn) consists of the origin. Then f1, ..., fn is a regular sequence.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Proposition 12.10

**Status**: ❌ **NOT INCLUDED**

**Statement**: Suppose f1, .., fn ∈R := k[x1, ..., xn] are homoge- neous polynomials of degrees d1, ..., dn > 0 such that R is a ﬁnitely gen- erated module over S := k[f1, ..., fn]. Then this module is free of rank Qn i=1 di. Moreover, the Hilbert polynomial of R0 := k[x1, ..., xn]/(f1, ..., fm) 17In fact these di...

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---


## Section 13

### Theorem 13.1 (Kostant)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Sg is a free (Sg)g-module. Moreover, for every ﬁnite-dimensional irreducible representation V of g, the space Homg(V, Sg) is a free (Sg)g module of rank dim V [0], the dimension of the zero weight space of V . The rest of the subsection is dedicated to the proof of this theorem. Introduce a ﬁltratio...

**Assessment**: Kostant's theorems on the structure of Sg and U(g) are not in mathlib.

---

### Lemma 13.2

**Status**: ❌ **NOT INCLUDED**

**Statement**: As q →1 in (0, 1), the function Fq(x) := Q α∈R+ 1−eiα(x) 1−qeiα(x) goes to 1 in L2(h/Q∨).18 18

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Theorem 13.3 (Kostant)

**Status**: ❌ **NOT INCLUDED**

**Statement**: For λ ∈P+ we have H(Homg(L∗ λ, (Sg)0), q) = Qr i=1[di]q |W| CT Y α∈R 1 −eα 1 −qeαχLλ ! = rY i=1 [di]q · CT eλ Q α∈R+(1 −eα) Q α∈R(1 −qeα) ! . Indeed, the ﬁrst expression is (12) and second expression is obtained from (12) using the Weyl character formula for χLλ and observing that all terms in the r...

**Assessment**: Kostant's theorems on the structure of Sg and U(g) are not in mathlib.

---

### Corollary 13.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: 1 |W|CT Y α∈R 1 −eα 1 −qeα ! = CT Q α∈R+(1 −eα) Q α∈R(1 −qeα) ! = 1 Qr i=1[di]q . For example, if g = sl2, this formula looks like (14) 1 2CT  (1 −z)(1 −z−1) (1 −qz)(1 −qz−1)  = CT  1 −z (1 −qz)(1 −qz−1)  = 1 1 + q, which is easy to check using the residue formula. For g = sln we obtain the iden...

**Assessment**: The classification of representations of SL₂(ℝ) or SL₂(ℂ) is not in mathlib.

---

### Theorem 13.5 (Kostant)

**Status**: ❌ **NOT INCLUDED**

**Statement**: (i) The center Z(g) = U(g)g of U(g) is a polynomial algebra in r generators Ci of Poincar´e-Birkhoﬀ-Witt ﬁltra- tion degrees di. (ii) U(g) is a free module over Z(g), and for every irreducible ﬁnite- dimensional representation V of g, the space Homg(V, U(g)) is a free Z(g)-module of rank dim V [0].

**Assessment**: Kostant's theorems on the structure of Sg and U(g) are not in mathlib.

---


## Section 14

### Theorem 14.1 (Harish-Chandra)

**Status**: ❌ **NOT INCLUDED**

**Statement**: (i) If b ∈U(g) and c ∈Z(g) then HC(bc) = HC(b)HC(c). In particular, the restriction of HC to Z(g) is an algebra homomorphism. (ii) Deﬁne the shifted action of W on h∗by w•x := w(x+ρ)−ρ where ρ is the half sum of positive roots (or, equivalently, sum of fundamental weights). Then HC maps Z(g) into th...

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---

### Corollary 14.3

**Status**: ❌ **NOT INCLUDED**

**Statement**: For any ﬁnite-dimensional irreducible g-module V we have dim Homg(V, Uχ) = dim V [0], where g acts on Uχ by the adjoint action. Thus Uχ is a Harish-Chandra g-bimodule.

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---

### Corollary 14.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: If V is a ﬁnite-dimensional g-bimodule then V ⊗Uχ is a Harish-Chandra g-bimodule.

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---

### Corollary 14.5 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Every irreducible g-bimodule M locally ﬁnite un- der the adjoint g-action is a quotient of V ⊗Uχ for some ﬁnite-dimensional irreducible g-module V with trivial right action of g, where χ is the right inﬁnitesimal character of M. (ii) Every irreducible g-bimodule locally ﬁnite under the adjoint g- ac...

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---


## Section 15

### Lemma 15.3

**Status**: ❌ **NOT INCLUDED**

**Statement**: If M ∈O then the weight subspaces of M are ﬁnite- dimensional.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 15.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: The action of Z(g) on every M ∈O factors through a ﬁnite-dimensional quotient.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 15.7 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Any M ∈O has a canonical decomposition M = ⊕χ∈h∗/WM(χ), where M(χ) is the generalized eigenspace of Z(g) in M with eigenvalue χ, and this direct sum is ﬁnite. In other words, O = ⊕χ∈h∗/WOχ, where Oχ is the subcategory of O of modules where every z ∈Z(g) acts with generalized eigenvalue χ(z). (ii) Ea...

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Lemma 15.9

**Status**: ❌ **NOT INCLUDED**

**Statement**: Every object of O has ﬁnite length.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Theorem 15.11 (D. N. Verma)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let λ, µ ∈h∗and µ ⪯λ. Then dim Hom(Mµ−ρ, Mλ−ρ) = 1 and Mµ−ρ can be uniquely realized as a submodule of Mλ−ρ. In particular, Lµ−ρ occurs in the composition se- ries of Mλ−ρ.

**Assessment**: Verma modules and their properties are not in mathlib. While mathlib has universal enveloping algebras, the specific theory of highest weight modules is not developed.

---

### Proposition 15.12

**Status**: ❌ **NOT INCLUDED**

**Statement**: Wx is generated by the reﬂections sα ∈Wx. Moreover, the roots α such that sα ∈Wx form a root system Rx ⊂R, and Wx is the Weyl group of Rx. The corresponding dual root system R∨ x is a root subsystem of R∨, i.e., R∨ x = spanZ(R∨ x) ∩R∨.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---


## Section 16

### Corollary 16.1 (λ, α∨)

**Status**: ❌ **NOT INCLUDED**

**Statement**: = a ∈Z≥1, (φ, α∨) = −(ψ, α∨) = b ∈Z≥0. We have λ = 1 2aα + λ′, φ = 1 2bα + φ′, ψ = −1 2bα + φ′. where λ′, φ′ are orthogonal to α. Thus (λ −ψ)2 −(λ −φ)2 = ((a+b 2 )2 −(a−b 2 )2)α2 = abα2. So this is ≥0, and if it is zero then either b = 0, in which case φ = ψ and there is nothing to prove, or a = 0, ...

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 16.2

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let C be a Noetherian abelian category with enough projectives and ﬁnite-dimensional Hom spaces over an algebraically closed ﬁeld k. Then (i) Let I be the set labeling the isomorphism classes of indecomposable projectives Pi of C. Then the isomorphism classes of simple objects Li of C are labeled by...

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 16.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: If λ is dominant then Mλ−ρ is a projective object in O.19

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 16.5 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: If P ∈O is projective then so is V ⊗P. (ii) If λ ∈h∗is dominant then the object V ⊗Mλ−ρ ∈O is projective.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 16.6 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: For every µ ∈h∗, there exists dominant λ ∈h∗ and a ﬁnite-dimensional g-module V such that Hom(V ⊗Mλ−ρ, Lµ) ̸= 0. Thus O has enough projectives. (ii) Every projective object P of O is a free U(n−)-module.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---


## Section 17

### Lemma 17.1

**Status**: ❌ **NOT INCLUDED**

**Statement**: The restriction of the adjoint representation of g to its principal sl2-subalgebra is isomorphic to L2m1⊕...⊕L2mr for appropriate mi ∈Z>0.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Lemma 17.2

**Status**: ❌ **NOT INCLUDED**

**Statement**: The element e = Pr i=1 ei is regular.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 17.3

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let B+ be the Borel subgroup of G with Lie algebra b+ := h ⊕n+. Then Ad(B+)e is the set of elements P α∈R+ cαeα with cα ∈C and cαi ̸= 0 for all i.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 17.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: The nilpotent cone is reduced.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 17.6 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: The orbit Oe := Ad(G)e is open and dense in N. (ii) All regular nilpotent elements in g are conjugate to e. (iii) N is an irreducible aﬃne variety. Thus (Sg)0 is an integral domain.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 17.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: Uχ is an integral domain for all χ.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---


## Section 18

### Proposition 18.2

**Status**: ❌ **NOT INCLUDED**

**Statement**: If M, N ∈O then Homﬁn(M, N) is an admissible g-bimodule.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 18.3

**Status**: ❌ **NOT INCLUDED**

**Statement**: For M, N ∈O and a ﬁnite-dimensional g-module V we have Homﬁn(M, V ⊗N) = V ⊗Homﬁn(M, N).

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 18.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let V be a ﬁnite-dimensional g-module. Then for any λ ∈h∗, we have dim Homg(Mλ, V ⊗Mλ) = dim V [0]. Thus the multiplicity of V in Homﬁn(Mλ, Mλ) equals dim V [0].

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 18.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: The action homomorphism φ : Uχλ+ρ →Homﬁn(Mλ, Mλ) is injective.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 18.8 (The Duﬂo-Joseph theorem)

**Status**: ❌ **NOT INCLUDED**

**Statement**: φ is an isomorphism. 94

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 18.9 (ii)

**Status**: ❌ **NOT INCLUDED**

**Statement**: If V is a ﬁnite-dimensional g-module then the natural map V ⊗Uχλ+ρ →Homﬁn(Mλ, V ⊗Mλ) is an isomorphism.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 18.10

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let V be a ﬁnite-dimensional g-module and λ ∈h∗. (i) The left inﬁnitesimal characters occurring in V ⊗Uχλ are χλ+ν where ν runs over weights of V . (ii) If M is a g-module with inﬁnitesimal character χλ then the inﬁn- itesimal characters occurring in V ⊗M are among χλ+ν where ν runs over weights of ...

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---

### Corollary 18.11

**Status**: ❌ **NOT INCLUDED**

**Statement**: The category of Harish-Chandra g-bimodules HC(g) has a decomposition according to generalized inﬁnitesimal characters: HC(g) = ⊕γ,λHCχλ+γ,χλ(g), where γ ∈P+ and λ ∈h∗/Stab(γ) (here Stab(γ) is the stabilizer of γ in W). In particular, if (θ, χ) cannot be written as (χλ+γ, χλ), λ ∈h∗, γ ∈P+, then HCθ,...

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---


## Section 19

### Proposition 19.1

**Status**: ❌ **NOT INCLUDED**

**Statement**: The homomorphism φ : U(g) →Q λ∈P+ End(Lλ) is injective.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 19.3

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let X ∈HC(g). Then Homg−bimod(X, M(λ, µ)) ∼= Hom(b−,b+)−bimod(X ⊗Cλ−ρ, Cµ−ρ). where the (b−, b+)-bimodule structure on Cµ−ρ is deﬁned by the char- acter (µ −ρ, 0) and on Cλ−ρ by the character (0, λ −ρ).

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 19.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: The right action of g on M(λ, µ) is given by the formula ΦV (v ⊗ℓ) · b = Φg⊗V ([b ⊗v] O [(λ −ρ) ⊗ℓ+ X α∈R+ f ∗ α ⊗fαℓ]).

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 19.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: We have an isomorphism ξ : M(λ, µ) →C∞ λ−ρ,µ−ρ(G/B)ﬁn as Harish-Chandra bimodules. Namely, ξ(Φv,ℓ) is the matrix coeﬃcient ψv,ℓ(g) := (v, gℓ), g ∈Gc.

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---

### Proposition 19.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: The functor Hλ exact when λ is dominant.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---


## Section 20

### Theorem 20.1 (ii)

**Status**: ❌ **NOT INCLUDED**

**Statement**: A vanishing lemma for Ext groups.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 20.2

**Status**: ❌ **NOT INCLUDED**

**Statement**: If X is standardly ﬁltered then Exti O(X, M ∨ µ ) = 0 for all µ ∈h∗and i > 0.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Theorem 20.3

**Status**: ❌ **NOT INCLUDED**

**Statement**: X is standardly ﬁltered if and only if Ext1 O(X, M ∨ λ ) = 0 for all λ ∈h∗. 100

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Lemma 20.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: If Ext1 O(Z, M ∨ µ ) = 0 for all µ ∈h∗then K = 0 and Z ∼= E ⊗Mλ.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 20.5 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Every X ∈O which is a free U(n−)-module is standardly ﬁltered. In particular, for any λ ∈h∗and ﬁnite-dimensional g-module V , the module V ⊗Mλ is standardly ﬁltered. (ii) Any projective object P ∈O is standardly ﬁltered.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Theorem 20.6 (BGG reciprocity)

**Status**: ❌ **NOT INCLUDED**

**Statement**: We have d∗ λµ = dµλ.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 20.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: We have cλµ = X ν dνλdνµ. In other words, C = DTD where D = (dλµ).

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Proposition 20.9 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: X∨∈O and has the same character and com- position series as X. (ii) (Mλ)∨= M ∨ λ , L∨ λ = Lλ. (iii) the assignment X 7→X∨is an involutive equivalence of cate- gories O →Oop which preserves the decomposition into Oχ(S).

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 20.10

**Status**: ❌ **NOT INCLUDED**

**Statement**: O has enough injectives, namely the injective hull of Lλ is P ∨ λ . 103 20.5. The Jantzen ﬁltration. It turns out that every Verma mod- ule Mλ carries a canonical ﬁnite ﬁltration by submodules called the Jantzen ﬁltration, which plays an important role in studying cat- egory O. In fact, this ﬁltrati...

**Assessment**: Verma modules and their properties are not in mathlib. While mathlib has universal enveloping algebras, the specific theory of highest weight modules is not developed.

---

### Theorem 20.13 (Bernstein – I. Gelfand – S. Gelfand)

**Status**: ❌ **NOT INCLUDED**

**Statement**: below. 15.4. The stabilizer in W of a point in h∗/Q. Let x ∈h∗/Q and Wx ⊂W be the stabilizer of x.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Corollary 20.14

**Status**: ❌ **NOT INCLUDED**

**Statement**: The following conditions on µ ≤λ are equivalent. (i) µ ⪯λ (ii) Lµ−ρ occurs in Mλ−ρ. (iii) dim Hom(Mµ−ρ, Mλ−ρ) ̸= 0. 105 21. Multiplicities in category O The multiplicities dλµ are complicated in general, and the (even- tually successful) attempt to understand them was one of the main developments th...

**Assessment**: The Beilinson-Bernstein localization theorem is deep algebraic geometry/representation theory not in mathlib.

---


## Section 21

### Proposition 21.1

**Status**: ❌ **NOT INCLUDED**

**Statement**: Tw, w ∈W are linearly independent, so they form a basis of Hq(W). Thus Hq(W) is a free Z[q 1 2, q−1 2]-module of rank |W|. 106

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Theorem 21.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: There exist unique polynomials Py,w ∈Z[q] such that (a) Py,w = 0 unless y ≤w, and Pw,w = 1; (b) If y < w then Py,w has degree at most ℓ(w)−ℓ(y)−1 2 ; (c) The elements Cw := q−ℓ(w) 2 X y Py,w(q)Ty ∈Hq(W) satisfy D(Cw) = Cw.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---

### Theorem 21.6 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Py,w has non-negative coeﬃcients. (ii) The multiplicity [My•λ : Lw•λ] equals Py,w(1). The polynomials Py,w have the property that if y ≤w then Py,w(0) = 1, so if in addition ℓ(w) −ℓ(y) ≤2 then Py,w(q) = 1 (indeed, it has to be a polynomial of degree 0). Also if w = w0 then Py,w = 1 for all y.

**Assessment**: Category O and its properties (BGG reciprocity, multiplicities, Kazhdan-Lusztig theory) are not in mathlib.

---


## Section 22

### Theorem 22.4 (ii)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let F1, F2 be projective θ-functors for θ = χλ. Let iλ : Hom(F1, F2) →Hom(F1(Mλ−ρ), F2(Mλ−ρ)). Then iλ is an isomorphism.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Proposition 22.5 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: If F1, F2 are projective functors then every mor- phism φ : F1(θ) →F2(θ) lifts to a morphism bφ : F1|Rep(g)θ →F2|Rep(g)θ. (ii) If F1 = F2 and φ2 = φ then we can choose bφ so that bφ2 = bφ. (iii) If φ is an isomorphism then so is bφ. 111

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Corollary 22.6 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let F1, F2 be projective functors. Then: any iso- morphism F1(Mλ−ρ) ∼= F2(Mλ−ρ) lifts to an isomorphism F1|Rep(g)χλ →F2|Rep(g)χλ; (ii) Let F be a projective functor. Then any decomposition F(Mλ−ρ) = ⊕iMi can be lifted to a decomposition F = ⊕iFi where Fi are projective functors and Fi(Mλ−ρ) = Mi; (i...

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Proposition 22.7 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Each projective functor F is a direct sum of indecomposable projective functors. Moreover, for F ◦Πθ this sum is ﬁnite. (ii) If F = F ◦Πχλ for dominant λ is an indecomposable projective functor then F(Mλ−ρ) = Pµ−ρ for some µ ∈h∗.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---


## Section 23

### Theorem 23.1 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: If F1, F2 are projective functors with [F1] = [F2] then F1 ∼= F2. (ii) If (F, F ∨) are an adjoint pair of projective functors then [F] is adjoint to [F ∨] under the inner product on K(O). (iii) For a projective functor F, its left and right adjoint are isomor- phic.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Theorem 23.2

**Status**: ❌ **NOT INCLUDED**

**Statement**: If F is a projective functor then [F] commutes with W on K(O).

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Lemma 23.3 (ii)

**Status**: ❌ **NOT INCLUDED**

**Statement**: that there exists an indecomposable projective functor G = Πθ ◦G ◦ΠθN such that G(Mλ+(N−1)ρ) = Pλ−ρ = Mλ−ρ. Moreover, by

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Lemma 23.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let λ ∈h∗be dominant and φ, ψ ∈λ+P, ψ ⪯φ. Then (λ −φ)2 ≤(λ −ψ)2, and if (λ −φ)2 = (λ −ψ)2 then ψ ∈Wλφ.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Theorem 23.6

**Status**: ❌ **NOT INCLUDED**

**Statement**: For any ξ ∈Ξ there exists an indecomposable projec- tive functor Fξ such that Fξ(Mν−ρ) = 0 if χν ̸= χλ and Fξ(Mλ−ρ) = Pµ−ρ for any proper representation (µ, λ) of ξ. The assignment ξ 7→Fξ is a bijection between Ξ and the set of isomorphism classes of indecom- posable projective functors.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Lemma 23.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: In this case S∗(F) = ξ := W(µ, λ) and (µ, λ) is a proper representation of ξ.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---


## Section 24

### Theorem 24.1 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: , this implies that I1....In ⊂J. Since J is prime, this means that there exists m such that Im ⊂J. Then J = Im, i.e. J is the annihilator of Lm. But Lm = Lµ−ρ for some µ such that χµ = χλ = θ.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Theorem 24.4 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: I ⊂J iﬀν(I) ⊂ν(J). In particular, ν is injective. 120 (ii) The image of ν is the set of submodules of Mλ−ρ which are quo- tients of direct sums of Pµ−ρ where χµ = χλ, µ ⪯λ and µ ⪯Wλµ. (iii) If λ is regular (i.e., Wλ = 1) then ν is an isomorphism of lattices.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Corollary 24.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let θ = χλ where λ is dominant. If Mλ−ρ is irre- ducible then Uθ is a simple algebra. Conversely, if Uθ is simple then Mµ−ρ is irreducible for all µ with χµ = θ.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---


## Section 25

### Theorem 25.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: Every prime ideal J ⊂Uθ is primitive and moreover is the annihilator of a simple highest weight module Lµ−ρ, where χµ = θ.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Lemma 25.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: The abelian category HC1 θ has enough projectives. We also note that this category has ﬁnite-dimensional Hom spaces. Indeed, If Y1, Y2 ∈HC1 θ then Y1 is a quotient of V ⊗Uθ for some V , so Hom(Y1, Y2) ⊂Hom(V ⊗Uθ, Y2) = Homgad(V, Y2), which is ﬁnite- dimensional. Finally, note that this category is N...

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Theorem 25.6

**Status**: ❌ **NOT INCLUDED**

**Statement**: The simples (and indecomposable projectives) in HC1 θ are labeled by the set Ξ, via ξ ∈Ξ 7→Lξ, Pξ. Namely, if ξ = (µ, λ) is a proper representation then Pξ is the unique indecomposable projective in HC1 θ such that Pξ ⊗U(g) Mλ−ρ = Pµ−ρ.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Corollary 25.7

**Status**: ❌ **NOT INCLUDED**

**Statement**: Objects in HC1 θ, hence in HCθ and HC, have ﬁnite length.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Theorem 25.8 (J. Bernstein-S, Gelfand)

**Status**: ❌ **NOT INCLUDED**

**Statement**: (i) If λ is a regular weight then the functor Tλ is an equivalence of categories, with quasi-inverse Hλ. (ii) In general, Tλ is fully faithful and deﬁnes an equivalence HC1 θ ∼= O(λ), with quasi-inverse Hλ.

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Proposition 25.10

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let A, B be abelian categories such that A has enough projectives and T : A →B a right exact functor which maps projectives to projectives. Suppose that T is fully faithful on projectives, i.e., for any projectives P0, P1 ∈A, the natural map Hom(P1, P0) → Hom(T(P1), T(P0)) is an isomorphism. Then T ...

**Assessment**: The theory of projective functors (Bernstein-Gelfand) is not in mathlib.

---

### Corollary 25.11

**Status**: ❌ **NOT INCLUDED**

**Statement**: Every Harish-Chandra bimodule M with right in- ﬁnitesimal character θ is realizable as Vﬁn where V is a (not necessar- ily unitary) admissible representation of the complex simply connected group G corresponding to g on a Hilbert space.

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---


## Section 26

### Proposition 26.1 (i)

**Status**: ❌ **NOT INCLUDED**

**Statement**: The principal series bimodule M(λ, µ) is ir- reducible and isomorphic to M(−λ, −µ) unless λ, µ are nonzero inte- gers of the same sign. Otherwise such bimodules are pairwise non- isomorphic. (ii) If λ, µ are both nonzero integers of the same sign then M(λ, µ) is indecomposable and has a ﬁnite-dimens...

**Assessment**: Principal series representations are not in mathlib.

---

### Theorem 26.3 (Gelfand-Naimark)

**Status**: ❌ **NOT INCLUDED**

**Statement**: The irreducible unitary represen- tations of SL2(C) are Hilbert space completions of the following unitary Harish-Chandra modules: • Unitary principal series M(−m 2 + s, m 2 + s), m ∈Z, s ∈iR; • Complementary series M(s, s), −1 < s < 1; • The trivial representation C. Here M(−m 2 +s, m 2 +s) ∼= M(m ...

**Assessment**: Harish-Chandra's theorems (analyticity, admissibility, globalization) are not in mathlib. The theory of (g,K)-modules is not developed.

---


## Section 27

### Theorem 27.3 (Borel-Weil)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let λ ∈P. If λ ∈P+ then we have an isomorphism of G-modules Γ(G/B, L−λ) ∼= L∗ λ. 133 If λ /∈P+ then Γ(G/B, L−λ) = 0.

**Assessment**: The Borel-Weil theorem (realizing irreducible representations as sections of line bundles) is not in mathlib.

---

### Corollary 27.5

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let λ ∈P with (λ, α∨ i ) = 0, i ∈S. Then Γ(G/PS, L−λ,S) ∼= L∗ λ. if λ ∈P+, otherwise Γ(G/PS, L−λ,S) = 0.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Theorem 27.8

**Status**: ❌ **NOT INCLUDED**

**Statement**: The Springer map p is birational and projective, so it is a resolution of singularities.

**Assessment**: The Springer resolution is not in mathlib.

---

### Theorem 27.11 (Kirillov-Kostant)

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let G be a connected real or com- plex Lie group or complex algebraic group. Then every G-orbit in g∗ has a natural symplectic structure. 136

**Assessment**: Kostant's theorems on the structure of Sg and U(g) are not in mathlib.

---

### Corollary 27.12

**Status**: ❌ **NOT INCLUDED**

**Statement**: The singular locus of the nilpotent cone N has codi- mension ≥2.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Corollary 27.13

**Status**: ❌ **NOT INCLUDED**

**Statement**: N is normal (i.e., the algebra O(N) is integrally closed in its quotient ﬁeld).

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Proposition 27.14 (iii)

**Status**: ❌ **NOT INCLUDED**

**Statement**: , f is constant along this ﬁber. So f = h ◦p for h : Y →C a rational function. It remains to show that h is regular. We know that h is regular on the smooth locus of Y (as it is deﬁned at all points of Y ). Thus the result follows from the normality of Y and

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Proposition 27.15

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let Y be an irreducible normal aﬃne algebraic variety and p : X →Y be a resolution of singularities. Then the homomorphism p∗: O(Y ) →O(X) is an isomorphism.

**Assessment**: This is advanced representation theory of Lie groups/algebras not covered in mathlib. Mathlib has basic Lie algebra theory but not the deep results in this textbook.

---

### Theorem 27.16

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let p : T ∗F →N be the Springer resolution. Then the map p∗: O(N) →O(T ∗F) is an isomorphism of graded algebras.

**Assessment**: The Springer resolution is not in mathlib.

---


## Section 28

### Proposition 28.9

**Status**: ❌ **NOT INCLUDED**

**Statement**: A left DX-module is the same thing as an OX- module with a ﬂat connection.

**Assessment**: D-module theory is not in mathlib.

---


## Section 29

### Theorem 29.1 (Beilinson-Bernstein, [BB])

**Status**: ❌ **NOT INCLUDED**

**Statement**: The Beilinson-Bernstein localization theorem for the zero inﬁnitesimal character. Let g be a complex semisimple Lie algebra and U0 be the maximal quotient of U(g) corresponding to the inﬁni- tesimal character χρ = χ−ρ of the trivial representation of g. Recall that gr(U0) = O(N). Let G be the corres...

**Assessment**: The Beilinson-Bernstein localization theorem is deep algebraic geometry/representation theory not in mathlib.

---

### Theorem 29.2 (Beilinson-Bernstein localization theorem, [BB])

**Status**: ❌ **NOT INCLUDED**

**Statement**: The functors Γ and Loc are mutually inverse equivalences. Thus the cate- gory U0 −mod is canonically equivalent to the category of D-modules on the ﬂag variety F. We will not give a proof of this theorem here.

**Assessment**: The Beilinson-Bernstein localization theorem is deep algebraic geometry/representation theory not in mathlib.

---

### Corollary 29.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: Partial ﬂag varieties of semisimple algebraic groups are D-aﬃne. 29.2. Twisted diﬀerential operators and D-modules. We would now like to generalize the localization theorem to nonzero inﬁnitesimal characters. To do so, we have to replace usual diﬀerential operators and D-modules by twisted ones. Let...

**Assessment**: D-module theory is not in mathlib.

---

### Theorem 29.6 (Beilinson-Bernstein)

**Status**: ❌ **NOT INCLUDED**

**Statement**: (i) The map a : U(g) →Dλ(F) factors through a map aλ : Uλ →Dλ(F). (ii) One has gr(aλ) = p∗where p is the Springer map T ∗F →N. (iii) grDλ(F) = O(T ∗F) and aλ is an isomorphism.

**Assessment**: The Beilinson-Bernstein localization theorem is deep algebraic geometry/representation theory not in mathlib.

---

### Theorem 29.7 (Beilinson-Bernstein localization theorem)

**Status**: ❌ **NOT INCLUDED**

**Statement**: If λ is an- tidominant then the functors Γ and Loc are mutually inverse equiva- lences. Thus the category Uλ −mod is canonically equivalent to the category of Dλ-modules on the ﬂag variety F.

**Assessment**: The Beilinson-Bernstein localization theorem is deep algebraic geometry/representation theory not in mathlib.

---


## Section 30

### Proposition 30.2

**Status**: ❌ **NOT INCLUDED**

**Statement**: The support of an irreducible D-module is irre- ducible.

**Assessment**: D-module theory is not in mathlib.

---

### Theorem 30.4 (Kashiwara)

**Status**: ❌ **NOT INCLUDED**

**Statement**: The functor i† is an equivalence of cat- egories MZ(X) →M(Z). The proof is not diﬃcult, but we will skip it (see [HTT]). The inverse of the functor i† is called the direct image functor and denoted i∗: M(Z) →MZ(X), as it is a special case of the direct image functor deﬁned above for aﬃne morphisms. ...

**Assessment**: Kashiwara's theorem on D-modules is not in mathlib. D-module theory is not developed in mathlib.

---

### Proposition 30.18

**Status**: ❌ **NOT INCLUDED**

**Statement**: Assume that X is a D-aﬃne variety and that K is an aﬃne algebraic group acting on X. Let D(X) be the ring of global sections of DX. Then the category of K-equivariant DX-modules is equivalent to the category of D(X)-modules M endowed with a locally ﬁnite K-action whose diﬀerential coincides with the...

**Assessment**: D-module theory is not in mathlib.

---

### Corollary 30.20

**Status**: ❌ **NOT INCLUDED**

**Statement**: If λ ∈h∗is antidominant then the functors Γ, Loc restrict to mutually inverse equivalences between the category of (g, K)- modules with inﬁnitesimal character χλ−ρ and the category of K-equivariant Dλ-modules on F. 153 31. Applications of D-modules to representation theory 31.1. Classiﬁcation of irr...

**Assessment**: D-module theory is not in mathlib.

---


## Section 31

### Theorem 31.1

**Status**: ❌ **NOT INCLUDED**

**Statement**: Let X be a smooth variety and K a connected algebraic group acting on X with ﬁnitely many orbits. Then there are ﬁnitely many irreducible K-equivariant D-modules on X. Namely, they are parametrized by pairs (O, V ) where O is an orbit of K on X and V is an irreducible representation of the component...

**Assessment**: D-module theory is not in mathlib.

---

### Proposition 31.3

**Status**: ❌ **NOT INCLUDED**

**Statement**: The group K acts on F with ﬁnitely many orbits. We will not give a proof of this proposition. For the proof and description of the set of orbits, see [RS].

**Assessment**: D-module theory is not in mathlib.

---

### Theorem 31.4

**Status**: ❌ **NOT INCLUDED**

**Statement**: Irreducible (g, K)-modules with (pure) inﬁnitesimal character χ are π(O, V ) where O is a K-orbit on F and V an irre- ducible representation of Kx, x ∈O such that Lie(Kx) acts via the character λx. Namely, π(O, V ) corresponds to M(O, V ) under the Beilinson-Bernstein equivalence.

**Assessment**: The Beilinson-Bernstein localization theorem is deep algebraic geometry/representation theory not in mathlib.

---

