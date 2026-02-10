# Detailed Assessment: Topics in Combinatorial Optimization Statements in Mathlib

## Statement 1: Proposition 1 (Matching size <= vertex cover size)
**Status**: non-included
**Explanation**: The statement that for any matching M and vertex cover C, |M| <= |C| is not formalized in mathlib. While mathlib has definitions of both matchings (`SimpleGraph.Subgraph.IsMatching` in `Matching.lean`) and vertex covers (`SimpleGraph.IsVertexCover` in `VertexCover.lean`), including vertex cover numbers and matching properties, there is no theorem relating matching size to vertex cover size. No `matchingNum` definition exists, so the inequality cannot be stated in the current framework.
**Mathlib references**: Related but insufficient: `Mathlib/Combinatorics/SimpleGraph/Matching.lean`, `Mathlib/Combinatorics/SimpleGraph/VertexCover.lean`.

## Statement 2: Theorem 2 (Tutte-Berge Formula)
**Status**: non-included
**Explanation**: The Tutte-Berge formula, which gives the matching number as a min-max expression involving odd components, is not formalized in mathlib. Mathlib has Tutte's theorem (`SimpleGraph.tutte` in `Tutte.lean`) which characterizes when a *perfect* matching exists (iff no Tutte violator), but the general Tutte-Berge formula computing the maximum matching size nu(G) = min_{U} (|V| + |U| - o(G-U))/2 is a strictly stronger result that is not present. Mathlib does define `oddComponents` but does not have a matching number definition or the min-max formula.
**Mathlib references**: Related: `Mathlib/Combinatorics/SimpleGraph/Tutte.lean` (Tutte's theorem for perfect matchings only), `Mathlib/Combinatorics/SimpleGraph/Connectivity/WalkCounting.lean` (oddComponents definition).

## Statement 3: Theorem 3 (Tutte-Berge equality for A(G))
**Status**: non-included
**Explanation**: The Edmonds-Gallai decomposition theorem (characterizing the sets A(G), D(G), C(G) and their roles in the Tutte-Berge formula) is not formalized in mathlib. This is a structural refinement of the Tutte-Berge formula which itself is not in mathlib. No formalization of factor-critical graphs exists in mathlib either.
**Mathlib references**: None.

## Statement 4: Theorem 4 (Berge's augmenting path characterization)
**Status**: non-included
**Explanation**: Berge's theorem that a matching M is maximum if and only if no M-augmenting path exists is not formalized in mathlib. There is no definition of augmenting path for matchings in the mathlib codebase. While alternating and augmenting structures are used internally in the proof of Tutte's theorem, they are not exposed as standalone definitions or theorems.
**Mathlib references**: None. The `Matching.lean` file has matching definitions but no augmenting path characterization.

## Statement 5: Theorem 1 Lecture 2 (Maximum matching iff no augmenting path)
**Status**: non-included
**Explanation**: This is the same as Statement 4 (Berge's theorem). Not formalized in mathlib.
**Mathlib references**: None.

## Statement 6: Lemma 2 Lecture 2 (Shortest alternating walk gives augmenting path or flower)
**Status**: non-included
**Explanation**: This lemma about the structural analysis of shortest alternating walks (giving either an augmenting path or an M-flower/blossom) is a technical component of Edmonds' blossom algorithm. It is not formalized in mathlib. No formalization of blossoms or flowers exists.
**Mathlib references**: None.

## Statement 7: Theorem 3 Lecture 2 (Maximum matching preserved under blossom contraction)
**Status**: non-included
**Explanation**: The theorem that M is a maximum matching in G if and only if M/B is a maximum matching in G/B (blossom contraction) is not formalized. Mathlib has no formalization of blossom contraction or the Edmonds algorithm.
**Mathlib references**: None.

## Statement 8: Theorem 4 Lecture 2 (Tutte-Berge Formula)
**Status**: non-included
**Explanation**: Same as Statement 2. The Tutte-Berge formula is not in mathlib.
**Mathlib references**: None.

## Statement 9: Theorem 5 Lecture 2 (Edmonds-Gallai Decomposition)
**Status**: non-included
**Explanation**: Same as Statement 3. The Edmonds-Gallai decomposition is not in mathlib. The decomposition of a graph into D(G), A(G), C(G) with the properties that A(G) achieves the Tutte-Berge minimum, D(G) contains odd components, and odd components are factor-critical, is not formalized.
**Mathlib references**: None.

## Statement 10: Claim 6 Lecture 2 (Alternating walk from Even to v)
**Status**: non-included
**Explanation**: This is a technical claim about the structure of alternating walks in the Edmonds algorithm framework (relating Even vertices to alternating walk existence). Not formalized.
**Mathlib references**: None.

## Statement 11: Corollary 7 Lecture 2 (No edge between Even and Free)
**Status**: non-included
**Explanation**: Technical corollary in the Edmonds algorithm analysis. Not formalized.
**Mathlib references**: None.

## Statement 12: Claim 8 Lecture 2 (No edge between Even vertices in G0)
**Status**: non-included
**Explanation**: Technical claim in the Edmonds algorithm analysis. Not formalized.
**Mathlib references**: None.

## Statement 13: Claim 9 Lecture 2 (Even = D(G))
**Status**: non-included
**Explanation**: Technical claim relating the Even set in the Edmonds algorithm to D(G) in the Edmonds-Gallai decomposition. Not formalized.
**Mathlib references**: None.

## Statement 14: Claim 10 Lecture 2 (Odd = A(G))
**Status**: non-included
**Explanation**: Technical claim relating the Odd set to A(G). Not formalized.
**Mathlib references**: None.

## Statement 15: Claim 11 Lecture 2 (Free = C(G))
**Status**: non-included
**Explanation**: Technical claim relating the Free set to C(G). Not formalized.
**Mathlib references**: None.

## Statement 16: Claim 12 Lecture 2 (Matching properties of free and odd vertices)
**Status**: non-included
**Explanation**: Technical structural claim about how the matching interacts with the Free and Odd vertex sets. Not formalized.
**Mathlib references**: None.

## Statement 17: Claim 13 Lecture 2 (Components of G \ A(G))
**Status**: non-included
**Explanation**: Detailed structural claim about components of G minus the Edmonds-Gallai decomposition set A(G). Not formalized.
**Mathlib references**: None.

## Statement 18: Claim 14 Lecture 2 (Matching size formula with A(G))
**Status**: non-included
**Explanation**: The specific formula |M| = (|V| + |A(G)| - c_o(G \ A(G)))/2 for a maximum matching M is not formalized. This is a consequence of the Edmonds-Gallai decomposition which is not in mathlib.
**Mathlib references**: None.

## Statement 19: Theorem 1 Lecture 3 (Petersen: bridgeless cubic graphs have perfect matching)
**Status**: non-included
**Explanation**: Petersen's theorem that every bridgeless cubic graph has a perfect matching is not formalized in mathlib. There is no formalization of cubic graphs or bridges (in the graph-theoretic sense of edges whose removal disconnects the graph) in mathlib. The `Tutte.lean` file provides the general Tutte criterion but the specific application to cubic bridgeless graphs is not derived.
**Mathlib references**: None.

## Statement 20: Theorem 2 Lecture 3 (Vizing's theorem)
**Status**: non-included
**Explanation**: Vizing's theorem (every graph has an edge coloring with at most Delta + 1 colors, where Delta is the max degree) is not formalized in mathlib. The `Coloring.lean` file defines vertex colorings and chromatic numbers but has no edge coloring or chromatic index definitions or theorems. No Vizing-related results exist.
**Mathlib references**: None. `Mathlib/Combinatorics/SimpleGraph/Coloring.lean` is for vertex coloring only.

## Statement 21: Theorem 3 Lecture 3 (Tait: planar cubic bridgeless and 4-color)
**Status**: non-included
**Explanation**: Tait's 1878 theorem relating edge-3-colorability of planar cubic bridgeless graphs to the four-color conjecture is not formalized. Mathlib has no formalization of planarity or the four-color theorem.
**Mathlib references**: None.

## Statement 22: Conjecture 1 Lecture 3 (Fulkerson's conjecture)
**Status**: non-included
**Explanation**: Fulkerson's conjecture about bridgeless cubic graphs having 6 perfect matchings covering each edge exactly twice is an open conjecture and is not formalized in mathlib.
**Mathlib references**: None.

## Statement 23: Claim 4 Lecture 3 (Odd components of G-A(G) are factor-critical)
**Status**: non-included
**Explanation**: This claim about factor-criticality of odd components in the Edmonds-Gallai decomposition is not formalized. Mathlib has no definition of factor-critical graphs.
**Mathlib references**: None.

## Statement 24: Theorem 5 Lecture 3 (Robbins: 2-connected iff proper ear decomposition)
**Status**: non-included
**Explanation**: Robbins' theorem characterizing 2-connected graphs via ear decompositions is not formalized in mathlib. There is no definition of ear decomposition. While `Connectivity/Connected.lean` has connectivity definitions, the structural characterization via ear decomposition is absent.
**Mathlib references**: None.

## Statement 25: Theorem 6 Lecture 3 (Factor-critical iff odd ear decomposition)
**Status**: non-included
**Explanation**: The characterization of factor-critical graphs via odd ear decompositions is not formalized. Neither factor-critical graphs nor ear decompositions are defined in mathlib.
**Mathlib references**: None.

## Statement 26: Theorem 7 Lecture 3 (Near-perfect matchings >= |E(G)|)
**Status**: non-included
**Explanation**: The theorem that a 2-connected factor-critical graph has at least |E(G)| near-perfect matchings is not formalized. Factor-critical graphs and near-perfect matchings are not defined in mathlib.
**Mathlib references**: None.

## Statement 27: Theorem 1 Lecture 4 (Edmonds: matching polytope description)
**Status**: non-included
**Explanation**: Edmonds' theorem characterizing the matching polytope using odd-set inequalities is not formalized. Mathlib has no LP theory, polytope machinery, or matching polytope definitions.
**Mathlib references**: None.

## Statement 28: Theorem 2 Lecture 4 (Edmonds-Giles: TDI + integral b implies integral polytope)
**Status**: non-included
**Explanation**: The Edmonds-Giles theorem on total dual integrality (TDI) is not formalized in mathlib. There is no definition of TDI systems or integral polyhedra in the LP sense. While `Matrix.IsTotallyUnimodular` exists, the TDI concept is not present.
**Mathlib references**: None.

## Statement 29: Theorem 3 Lecture 4 (TDI system exists for rational polyhedron)
**Status**: non-included
**Explanation**: The existence of TDI systems for rational polyhedra is not formalized. No LP theory or polyhedra framework exists in mathlib.
**Mathlib references**: None.

## Statement 30: Theorem 1 Lecture 5 (TDI + integral b implies integral polytope)
**Status**: non-included
**Explanation**: Same as Statement 28. Not formalized.
**Mathlib references**: None.

## Statement 31: Proposition 2 Lecture 5 (TU matrix implies integral polytope)
**Status**: non-included
**Explanation**: While the definition of totally unimodular matrices exists in mathlib (`Matrix.IsTotallyUnimodular`), the consequence that TU constraint matrices yield integral polytopes for integral b is not formalized. There is no LP duality or integral polytope framework.
**Mathlib references**: Partially related: `Mathlib/LinearAlgebra/Matrix/Determinant/TotallyUnimodular.lean` (TU definition only).

## Statement 32: Proposition 3 Lecture 5 (TU matrix implies TDI)
**Status**: non-included
**Explanation**: The proposition that totally unimodular matrices yield TDI systems is not formalized. While TU matrices are defined, TDI systems are not.
**Mathlib references**: None.

## Statement 33: Theorem 4 Lecture 5 (Kronecker Approximation Theorem)
**Status**: non-included
**Explanation**: The Kronecker approximation theorem (Ax = b has an integral solution iff y^T b is integer whenever y^T A is integral) is not formalized in mathlib. This specific result from integer programming is not present.
**Mathlib references**: None.

## Statement 34: Corollary 5 Lecture 5 (Integral polytope iff supporting hyperplanes contain integral vector)
**Status**: non-included
**Explanation**: The characterization of integral polyhedra via integral points in supporting hyperplanes is not formalized. No polytope integrality framework exists.
**Mathlib references**: None.

## Statement 35: Theorem 6 Lecture 5 (Cunningham-Marsh weighted matching formula)
**Status**: non-included
**Explanation**: The Cunningham-Marsh formula for maximum weight matching is not formalized. This is an advanced weighted matching duality result requiring LP theory.
**Mathlib references**: None.

## Statement 36: Theorem 7 Lecture 5 (Tutte-Berge formula)
**Status**: non-included
**Explanation**: Same as Statement 2. The Tutte-Berge formula is not in mathlib.
**Mathlib references**: None.

## Statement 37: Theorem 1 Lecture 6 (Odd-set inequality necessary iff factor-critical and 2-connected)
**Status**: non-included
**Explanation**: This characterization of when odd-set inequalities are necessary for the matching polytope is not formalized. Requires matching polytope theory and factor-critical graph definitions.
**Mathlib references**: None.

## Statement 38: Theorem 2 Lecture 6 (Max chain = min antichain partition, Mirsky's theorem)
**Status**: non-included
**Explanation**: Mirsky's theorem (the dual of Dilworth's theorem, stating that the maximum chain length equals the minimum number of antichains needed to partition) is not formalized in mathlib. There is no chain/antichain partition machinery or Dilworth-type results.
**Mathlib references**: None.

## Statement 39: Theorem 3 Lecture 6 (Dilworth's theorem)
**Status**: non-included
**Explanation**: Dilworth's theorem (the maximum antichain size equals the minimum number of chains partitioning the poset) is not formalized in mathlib. While mathlib has extensive order theory including antichains (`Order/Antichain.lean`) and chains, the min-max theorem of Dilworth is not present.
**Mathlib references**: None. Related: `Mathlib/Order/Antichain.lean` (antichain definition).

## Statement 40: Theorem 4 Lecture 6 (Konig's theorem: nu = tau in bipartite graphs)
**Status**: non-included
**Explanation**: Konig's theorem (the matching number equals the vertex cover number in bipartite graphs) is not formalized in mathlib. While matchings and vertex covers are both defined, there is no matching number definition, and no theorem relating matching number to vertex cover number in bipartite graphs. The Konig results found in mathlib relate to Konig's lemma in topology, not Konig's matching theorem.
**Mathlib references**: None. Related but insufficient: `Mathlib/Combinatorics/SimpleGraph/Matching.lean`, `Mathlib/Combinatorics/SimpleGraph/VertexCover.lean`, `Mathlib/Combinatorics/SimpleGraph/Hall.lean`.

## Statement 41: Theorem 5 Lecture 6 (Weighted max chain = min antichain cover)
**Status**: non-included
**Explanation**: The weighted version of the chain-antichain duality is not formalized in mathlib.
**Mathlib references**: None.

## Statement 42: Theorem 6 Lecture 6 (Weighted max antichain = min chain cover)
**Status**: non-included
**Explanation**: The weighted version of Dilworth's theorem is not formalized in mathlib.
**Mathlib references**: None.

## Statement 43: Theorem 1 Lecture 7 (Gallai-Milgram)
**Status**: non-included
**Explanation**: The Gallai-Milgram theorem (vertices of any digraph can be partitioned into alpha(D) vertex-disjoint directed paths) is not formalized. Mathlib has no digraph path-partition theory.
**Mathlib references**: None.

## Statement 44: Theorem 2 Lecture 7 (Bessy-Thomasse)
**Status**: non-included
**Explanation**: The Bessy-Thomasse theorem on covering vertices of strongly connected digraphs by directed cycles is not formalized. Mathlib has no directed graph cycle-cover theory.
**Mathlib references**: None.

## Statement 45: Lemma 3 Lecture 7 (Path partition refinement)
**Status**: non-included
**Explanation**: The lemma on refining path partitions in digraphs is not formalized.
**Mathlib references**: None.

## Statement 46: Theorem 4 Lecture 7 (Strongly connected implies valid cyclic ordering)
**Status**: non-included
**Explanation**: The existence of valid cyclic orderings for strongly connected digraphs is not formalized. Mathlib has no formalization of strongly connected digraphs or cyclic orderings in the combinatorial optimization sense.
**Mathlib references**: None.

## Statement 47: Corollary 5 Lecture 7 (Strongly connected tournament has Hamiltonian cycle)
**Status**: non-included
**Explanation**: While mathlib defines Hamiltonian cycles (`SimpleGraph.Walk.IsHamiltonianCycle` in `Hamiltonian.lean`), it does not have tournaments or the theorem that strongly connected tournaments have Hamiltonian cycles. The Hamiltonian file provides definitions but no existence theorems of this type.
**Mathlib references**: Related but insufficient: `Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean` (definitions only).

## Statement 48: Theorem 1 Lecture 8 (Bessy-Thomasse min-max for cyclic stable sets)
**Status**: non-included
**Explanation**: The min-max theorem for cyclic stable sets in strongly connected digraphs is not formalized.
**Mathlib references**: None.

## Statement 49: Lemma 2 Lecture 8 (No forward paths implies cyclic stable set)
**Status**: non-included
**Explanation**: This technical lemma about cyclic stable sets and forward paths is not formalized.
**Mathlib references**: None.

## Statement 50: Theorem 1 Lecture 10 (Whitney: M(G) = M(H) iff switching, 2-connected)
**Status**: non-included
**Explanation**: Whitney's theorem relating graphic matroids of 2-connected graphs via switching operations is not formalized. Mathlib has no formalization of graphic matroids or Whitney's theorem.
**Mathlib references**: None.

## Statement 51: Theorem 2 Lecture 10 (Whitney: M(G) = M(H) iff G = H, 3-connected)
**Status**: non-included
**Explanation**: Whitney's uniqueness theorem for 3-connected graphs is not formalized. No graphic matroid or 3-connectivity formalization exists.
**Mathlib references**: None.

## Statement 52: Theorem 3 Lecture 10 (Tutte: dual of graphic is graphic iff planar)
**Status**: non-included
**Explanation**: Tutte's theorem relating planarity to graphic matroid duality is not formalized. Mathlib has matroid duality (`Matroid.Dual`) but no graphic matroids or planarity.
**Mathlib references**: Related but insufficient: `Mathlib/Combinatorics/Matroid/Dual.lean` (matroid duality definition).

## Statement 53: Theorem 4 Lecture 10 (Dual of representable matroid is representable)
**Status**: non-included
**Explanation**: The theorem that if a matroid is representable over a field F, then so is its dual, is not formalized. While matroid duality is defined and the concept of representability is mentioned in comments, there is no formal definition of representable matroid or a proof of this duality result.
**Mathlib references**: Related: `Mathlib/Combinatorics/Matroid/Dual.lean` (duality definition only).

## Statement 54: Theorem 5 Lecture 10 (Binary matroid iff excludes U_4^2)
**Status**: non-included
**Explanation**: The characterization of binary matroids as those excluding the uniform matroid U(2,4) as a minor is not formalized. Mathlib has matroid minors (`Matroid.IsMinor`) but no definition of binary matroids, uniform matroids U(k,n), or excluded minor characterizations.
**Mathlib references**: Related: `Mathlib/Combinatorics/Matroid/Minor/Order.lean` (minor definition).

## Statement 55: Theorem 6 Lecture 10 (Regular binary iff excludes Fano and dual)
**Status**: non-included
**Explanation**: The characterization of regular matroids among binary matroids via Fano plane exclusion is not formalized. No definitions of regular matroids, binary matroids, or the Fano matroid exist.
**Mathlib references**: None.

## Statement 56: Theorem 7 Lecture 10 (Ternary matroids exclude U_5^2, U_5^3, F_7, F_7*)
**Status**: non-included
**Explanation**: The excluded minor characterization of ternary matroids is not formalized.
**Mathlib references**: None.

## Statement 57: Lemma 8 Lecture 10 (Rank of matroid union)
**Status**: non-included
**Explanation**: The formula for the rank function of a matroid union (r_M(U) = min over T of |U-T| + sum r_i(T cap S_i)) is not formalized. While mathlib has `Matroid.Sum` (disjoint sum of matroids), this is different from the matroid union operation. The matroid union is not defined in mathlib.
**Mathlib references**: Related but insufficient: `Mathlib/Combinatorics/Matroid/Sum.lean` (disjoint sum, not union).

## Statement 58: Theorem 9 Lecture 10 (Greedy algorithm for max weight independent set)
**Status**: non-included
**Explanation**: The theorem that the greedy algorithm finds a maximum weight independent set in a matroid is not formalized. There is no algorithmic content or greedy algorithm formalization in the matroid theory portion of mathlib.
**Mathlib references**: None.

## Statement 59: Theorem 10 Lecture 10 (Edmonds matroid polytope is integral)
**Status**: non-included
**Explanation**: The integrality of Edmonds' matroid polytope is not formalized. No polytope theory exists in the matroid section of mathlib.
**Mathlib references**: None.

## Statement 60: Theorem 1 Lecture 11 (Matroid intersection min-max)
**Status**: non-included
**Explanation**: The matroid intersection theorem (max |I| over common independent sets = min r1(U) + r2(S\U)) is not formalized. Mathlib has no matroid intersection theory.
**Mathlib references**: None.

## Statement 61: Lemma 2 Lecture 11 (Unique circuit in I + x)
**Status**: included
**Explanation**: The statement that if I is independent and I + x is not independent, then I + x contains a unique minimal circuit, is formalized in mathlib. The `fundCircuit` construction gives this unique circuit, and `Matroid.IsCircuit.eq_fundCircuit_of_subset` proves uniqueness. Specifically, `Matroid.Indep.fundCircuit_isCircuit` shows that `fundCircuit M e I` is a circuit when `e` is in the closure of `I` but not in `I`, and `Matroid.IsCircuit.eq_fundCircuit_of_subset` shows it is the unique circuit contained in `insert e I`.
**Mathlib references**: `Mathlib/Combinatorics/Matroid/Circuit.lean` -- `Matroid.fundCircuit`, `Matroid.Indep.fundCircuit_isCircuit`, `Matroid.IsCircuit.eq_fundCircuit_of_subset`.

## Statement 62: Lemma 3 Lecture 11 (Strong basis exchange)
**Status**: non-included
**Explanation**: The strong (symmetric) basis exchange property -- that for bases B1 and B2 and x in B1 \ B2, there exists y in B2 \ B1 such that BOTH B1 - x + y and B2 - y + x are bases -- is not formalized. Mathlib has the standard (one-way) exchange property (`IsBase.exchange`): for x in B1 \ B2, there exists y in B2 \ B1 such that B1 - x + y is a base (i.e., `insert y (B1 \ {e})` is a base). But the simultaneous condition that B2 - y + x is also a base is not proved.
**Mathlib references**: Related but insufficient: `Mathlib/Combinatorics/Matroid/Basic.lean` -- `Matroid.IsBase.exchange` (one-way exchange only).

## Statement 63: Lemma 4 Lecture 11 (Exchange graph matching on symmetric difference)
**Status**: non-included
**Explanation**: The lemma about the exchange graph A(I) containing a matching on the symmetric difference of two independent sets of equal size is not formalized. This is part of matroid intersection theory which is absent from mathlib.
**Mathlib references**: None.

## Statement 64: Lemma 5 Lecture 11 (Unique matching implies independence)
**Status**: non-included
**Explanation**: The lemma that a unique matching on the symmetric difference of I and J in the exchange graph implies J is independent is not formalized.
**Mathlib references**: None.

## Statement 65: Theorem 1 Lecture 12 (Matroid intersection min-max)
**Status**: non-included
**Explanation**: Same as Statement 60. The matroid intersection theorem is not formalized.
**Mathlib references**: None.

## Statement 66: Theorem 2 Lecture 12 (MIA algorithm correctness)
**Status**: non-included
**Explanation**: The correctness of the matroid intersection algorithm (MIA) is not formalized. No algorithmic matroid content exists.
**Mathlib references**: None.

## Statement 67: Lemma 3 Lecture 12 (Unique matching implies independence)
**Status**: non-included
**Explanation**: Same as Statement 64. Not formalized.
**Mathlib references**: None.

## Statement 68: Theorem 4 Lecture 12 (3-matroid intersection is NP-hard)
**Status**: non-included
**Explanation**: Computational complexity results (NP-hardness of 3-matroid intersection) are not formalized in mathlib. Mathlib has no computational complexity theory.
**Mathlib references**: None.

## Statement 69: Theorem 5 Lecture 12 (Shannon switching game)
**Status**: non-included
**Explanation**: The characterization of winning strategies in the Shannon switching game via disjoint bases is not formalized. No game theory on matroids exists in mathlib.
**Mathlib references**: None.

## Statement 70: Theorem 1 Lecture 13 (Matroid intersection polytope TDI)
**Status**: non-included
**Explanation**: The TDI property of the matroid intersection polytope is not formalized. Neither matroid intersection nor TDI systems are in mathlib.
**Mathlib references**: None.

## Statement 71: Theorem 2 Lecture 13 (Union of two laminar families is TU)
**Status**: non-included
**Explanation**: The total unimodularity of incidence matrices of unions of laminar families is not formalized. While TU matrices are defined, laminar families and their incidence matrices are not.
**Mathlib references**: Related: `Mathlib/LinearAlgebra/Matrix/Determinant/TotallyUnimodular.lean` (TU definition only).

## Statement 72: Theorem 3 Lecture 13 (Union matroid is a matroid)
**Status**: non-included
**Explanation**: The theorem that the matroid union construction yields a matroid is not formalized. Mathlib has `Matroid.Sum` for disjoint sums of matroids (direct sum on the sigma type), but not the matroid union where independent sets are unions of independent sets from individual matroids on a common ground set.
**Mathlib references**: Related but different: `Mathlib/Combinatorics/Matroid/Sum.lean` (disjoint sum).

## Statement 73: Lemma 4 Lecture 13 (Image of matroid under function is a matroid)
**Status**: non-included
**Explanation**: The specific lemma that for a matroid M' and a function f: S' -> S (not necessarily injective), M = (S, f(I')) is a matroid, is partially related to content in mathlib. Mathlib has `Matroid.map` and `Matroid.comap` constructions, but `Matroid.map` requires injectivity on the ground set. The statement about arbitrary (non-injective) functions producing a matroid via image of independent sets is not formalized.
**Mathlib references**: Related but insufficient: `Mathlib/Combinatorics/Matroid/Map.lean` (requires injectivity).

## Statement 74: Lemma 5 Lecture 13 (Rank function of image matroid)
**Status**: non-included
**Explanation**: The formula for the rank function of the image matroid under a non-injective function (r(U) = min_{T in U} (|U\T| + r'(f^{-1}(T)))) is not formalized. Since the non-injective image matroid construction itself is not in mathlib, neither is this rank formula.
**Mathlib references**: None.

## Statement 75: Theorem 1 Lecture 14 (Union independence augmentation)
**Status**: non-included
**Explanation**: The augmentation characterization for matroid union (I + s is independent in the union iff there exists an F-s path in the auxiliary digraph D) is not formalized. Matroid union is not in mathlib.
**Mathlib references**: None.

## Statement 76: Claim 2 Lecture 14 (Maximal independent subset in matroid partition)
**Status**: non-included
**Explanation**: Not formalized.
**Mathlib references**: None.

## Statement 77: Corollary 3 Lecture 14 (Max size of union of k independent sets)
**Status**: non-included
**Explanation**: The formula for the maximum size of the union of k independent sets in a matroid (min over U of |S\U| + k*r(U)) is not formalized. This is part of matroid union theory.
**Mathlib references**: None.

## Statement 78: Corollary 4 Lecture 14 (Matroid base covering condition)
**Status**: non-included
**Explanation**: The condition for a ground set to be coverable by k bases (for all U: k*r(U) >= |U|) is not formalized.
**Mathlib references**: None.

## Statement 79: Corollary 5 Lecture 14 (Matroid base packing condition)
**Status**: non-included
**Explanation**: The condition for the existence of k disjoint bases is not formalized.
**Mathlib references**: None.

## Statement 80: Theorem 6 Lecture 14 (Nash-Williams forest covering)
**Status**: non-included
**Explanation**: Nash-Williams' theorem that G can be covered by k forests iff |E(T)| <= k(|T|-1) for all T is not formalized. This is a classic result in matroid theory / graph theory that is not present in mathlib.
**Mathlib references**: None.

## Statement 81: Theorem 7 Lecture 14 (Tutte-Nash-Williams spanning trees)
**Status**: non-included
**Explanation**: The Tutte-Nash-Williams theorem characterizing when a graph contains k edge-disjoint spanning trees is not formalized.
**Mathlib references**: None.

## Statement 82: Lemma 8 Lecture 14 (Rank function is submodular)
**Status**: included
**Explanation**: The submodularity of the matroid rank function (r(A) + r(B) >= r(A cap B) + r(A cup B)) is formalized in mathlib for both the ENat-valued and Cardinal-valued rank functions. The ENat version is `Matroid.eRk_inter_add_eRk_union_le` (also aliased as `eRk_submod`), and the Cardinal version is `cRk_inter_add_cRk_union_le`.
**Mathlib references**: `Mathlib/Combinatorics/Matroid/Rank/ENat.lean` -- `Matroid.eRk_inter_add_eRk_union_le` (alias `eRk_submod`); `Mathlib/Combinatorics/Matroid/Rank/Cardinal.lean` -- `cRk_inter_add_cRk_union_le`.

## Statement 83: Lemma 9 Lecture 14 (Basis partition exchange)
**Status**: non-included
**Explanation**: The lemma that for bases B1 and B2 with B1 = X1 union Y1, there exists a partition of B2 into X2 union Y2 such that X1 union Y2 and X2 union Y1 are both bases, is not formalized. This is a strengthening of the basis exchange property that is not in mathlib.
**Mathlib references**: None.

## Statement 84: Theorem 1 Lecture 15 (Lovasz matroid matching formula)
**Status**: non-included
**Explanation**: Lovasz's matroid matching formula is not formalized. This is an advanced result combining matroid and matching theory.
**Mathlib references**: None.

## Statement 85: Proposition 2 Lecture 15 (Linear matroid satisfies condition (3))
**Status**: non-included
**Explanation**: This is a technical proposition about linear matroids satisfying a specific condition. Not formalized, as linear matroids (representable matroids) are not formally defined in mathlib.
**Mathlib references**: None.

## Statement 86: Claim 1 Lecture 16 (Bases of matroid form jump system)
**Status**: non-included
**Explanation**: Jump systems are not defined or studied in mathlib.
**Mathlib references**: None.

## Statement 87: Claim 2 Lecture 16 (Degree sequences form jump system)
**Status**: non-included
**Explanation**: Jump systems are not in mathlib.
**Mathlib references**: None.

## Statement 88: Claim 3 Lecture 16 (Sum of jump systems is jump system)
**Status**: non-included
**Explanation**: Jump systems are not in mathlib.
**Mathlib references**: None.

## Statement 89: Claim 4 Lecture 16 (Greedy algorithm for jump system)
**Status**: non-included
**Explanation**: Jump systems are not in mathlib.
**Mathlib references**: None.

## Statement 90: Theorem 1 Lecture 16 (Lovasz: J_B is a jump system)
**Status**: non-included
**Explanation**: Jump systems are not in mathlib.
**Mathlib references**: None.

## Statement 91: Theorem 2 Lecture 16 (Equality in min-max for jump system)
**Status**: non-included
**Explanation**: Jump systems are not in mathlib.
**Mathlib references**: None.

## Statement 92: Theorem 3 Lecture 18 (Robbins: 2-edge-connected iff strongly orientable)
**Status**: non-included
**Explanation**: Robbins' theorem that a graph is 2-edge-connected if and only if it has a strongly connected orientation is not formalized. While mathlib has k-edge-connectivity definitions (`SimpleGraph.IsEdgeConnected` in `Connectivity/EdgeConnectivity.lean`), it has no graph orientation theory or strongly connected digraph formalization.
**Mathlib references**: Related but insufficient: `Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean` (edge connectivity definition only).

## Statement 93: Theorem 4 Lecture 18 (Nash-Williams: 2k-edge-connected iff k-arc-orientable)
**Status**: non-included
**Explanation**: Nash-Williams' orientation theorem is not formalized. No graph orientation theory exists in mathlib.
**Mathlib references**: None.

## Statement 94: Theorem 5 Lecture 18 (2k-edge-connected graph construction)
**Status**: non-included
**Explanation**: The constructive characterization of 2k-edge-connected graphs via pinching operations is not formalized.
**Mathlib references**: None.

## Statement 95: Theorem 6 Lecture 18 (Nash-Williams orientation theorem)
**Status**: non-included
**Explanation**: The general Nash-Williams orientation theorem is not formalized.
**Mathlib references**: None.

## Statement 96: Theorem 9 Lecture 18 (Lucchesi-Younger theorem)
**Status**: non-included
**Explanation**: The Lucchesi-Younger theorem (min dijoin = max number of disjoint directed cuts in a weakly connected digraph) is not formalized. No directed cut or dijoin theory exists in mathlib.
**Mathlib references**: None.

## Statement 97: Conjecture 10 Lecture 18 (Woodall's conjecture)
**Status**: non-included
**Explanation**: Woodall's conjecture is an open problem in combinatorial optimization. Not formalized.
**Mathlib references**: None.

## Statement 98: Proposition 11 Lecture 18 (Dijoin iff strongly connected)
**Status**: non-included
**Explanation**: The characterization of dijoins via strong connectivity is not formalized. No dijoin definition exists in mathlib.
**Mathlib references**: None.

## Statement 99: Corollary 12 Lecture 18 (Planar digraph: min feedback arc set = max disjoint directed cuts)
**Status**: non-included
**Explanation**: This corollary about planar digraphs is not formalized. No planarity, feedback arc set, or directed cut theory exists.
**Mathlib references**: None.

## Statement 100: Theorem 19 Lecture 18 (Edmonds-Giles: submodular flow polyhedron is Box-TDI)
**Status**: non-included
**Explanation**: The Box-TDI property of submodular flow polyhedra is not formalized. No submodular flow theory exists in mathlib.
**Mathlib references**: None.

## Statement 101: Corollary 20 Lecture 18 (2k-edge-connected iff k-arc-orientable)
**Status**: non-included
**Explanation**: Same as Statement 93. Not formalized.
**Mathlib references**: None.

## Statement 102: Corollary 21 Lecture 18 (Min dijoin = max disjoint directed cuts)
**Status**: non-included
**Explanation**: Same as Statement 96. Not formalized.
**Mathlib references**: None.

## Statement 103: Theorem 1 Lecture 19 (Edmonds-Giles TDI for crossing families)
**Status**: non-included
**Explanation**: The Edmonds-Giles TDI theorem for crossing families is not formalized. No crossing family or TDI theory exists.
**Mathlib references**: None.

## Statement 104: Theorem 2 Lecture 19 (Cross-free family incidence matrix is TU)
**Status**: non-included
**Explanation**: The total unimodularity of cross-free family incidence matrices is not formalized.
**Mathlib references**: None.

## Statement 105: Proposition 3 Lecture 19 (M2 is a matroid)
**Status**: non-included
**Explanation**: The specific matroid construction M2 from the lecture is not formalized.
**Mathlib references**: None.

## Statement 106: Proposition 4 Lecture 19 (Independence testing by network flows)
**Status**: non-included
**Explanation**: The algorithmic result about testing independence via network flows is not formalized. No network flow theory exists in mathlib.
**Mathlib references**: None.

## Statement 107: Lemma 1 Lecture 20 (Crossing family + crossing submodular gives matroid)
**Status**: non-included
**Explanation**: The matroid construction from crossing families and crossing submodular functions is not formalized.
**Mathlib references**: None.

## Statement 108: Theorem 2 Lecture 20 (Splitting off theorem)
**Status**: non-included
**Explanation**: The splitting-off theorem for edge connectivity is not formalized. While edge connectivity is defined in mathlib, the splitting-off operation is not.
**Mathlib references**: None.

## Statement 109: Lemma 3 Lecture 20 (Edge-minimal k-edge-connected has vertex of degree k)
**Status**: non-included
**Explanation**: This structural result about edge-minimal k-edge-connected graphs is not formalized.
**Mathlib references**: None.

## Statement 110: Theorem 4 Lecture 20 (Construction of 2k-edge-connected graphs)
**Status**: non-included
**Explanation**: Same as Statement 94. Not formalized.
**Mathlib references**: None.

## Statement 111: Lemma 5 Lecture 20 (Edge augmentation to k-edge-connected)
**Status**: non-included
**Explanation**: The edge augmentation characterization is not formalized.
**Mathlib references**: None.

## Statement 112: Theorem 6 Lecture 20 (Edge augmentation characterization)
**Status**: non-included
**Explanation**: The full edge augmentation characterization theorem is not formalized.
**Mathlib references**: None.

## Statement 113: Theorem 1 Lecture 21 (Lovasz splitting-off)
**Status**: non-included
**Explanation**: Lovasz's refined splitting-off theorem is not formalized.
**Mathlib references**: None.

## Statement 114: Claim 2 Lecture 21 (Submodular function minimizer)
**Status**: non-included
**Explanation**: The claim about finding submodular function minimizers is not formalized. No submodular function optimization exists in mathlib.
**Mathlib references**: None.

## Statement 115: Claim 3 Lecture 21 (Greedy vector in base polyhedron)
**Status**: non-included
**Explanation**: The claim that greedy vectors lie in the base polyhedron of a submodular function is not formalized. No base polyhedron or submodular function optimization theory exists.
**Mathlib references**: None.

## Statement 116: Lemma 4 Lecture 21 (Convex combination in base polyhedron)
**Status**: non-included
**Explanation**: The convex combination representation in base polyhedra is not formalized.
**Mathlib references**: None.

## Statement 117: Theorem 1 Lecture 22 (Rothschild-Whinston: integer two-commodity flow)
**Status**: non-included
**Explanation**: The Rothschild-Whinston theorem on integer two-commodity flow is not formalized. No multi-commodity flow theory exists in mathlib.
**Mathlib references**: None.

## Statement 118: Theorem 2 Lecture 22 (Max biflow = min bicut)
**Status**: non-included
**Explanation**: The max biflow equals min bicut theorem is not formalized. No flow theory exists in mathlib.
**Mathlib references**: None.

## Statement 119: Theorem 1 Lecture 23 (Okamura-Seymour)
**Status**: non-included
**Explanation**: The Okamura-Seymour theorem on edge-disjoint paths in planar graphs is not formalized. No planarity or edge-disjoint path theory exists in mathlib.
**Mathlib references**: None.

## Statement 120: Lemma 2 Lecture 23 (Cut condition equivalence for connected subsets)
**Status**: non-included
**Explanation**: The technical lemma about cut conditions in edge-disjoint path problems is not formalized.
**Mathlib references**: None.

## Statement 121: Lemma 3 Lecture 23 (WLOG 2-connected)
**Status**: non-included
**Explanation**: The reduction to 2-connected case is not formalized.
**Mathlib references**: None.

## Statement 122: Lemma 4 Lecture 23 (Cut condition preserved under re-pairing)
**Status**: non-included
**Explanation**: The invariance of cut conditions under re-pairing is not formalized.
**Mathlib references**: None.
