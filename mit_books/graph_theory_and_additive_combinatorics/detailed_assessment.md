# Detailed Assessment: Graph Theory and Additive Combinatorics

## Chapter 0: Introduction

### 1. Theorem 0.1.1 (Schur's theorem)
**Assessment: non-included**
Statement: If the positive integers are colored using finitely many colors, then there is always a monochromatic solution to x + y = z.
Explanation: Schur's theorem in the Ramsey-theoretic sense (monochromatic solutions to x+y=z) is not in mathlib. The Schur-related files in mathlib (`CategoryTheory/Preadditive/Schur.lean`, `GroupTheory/SchurZassenhaus.lean`, `LinearAlgebra/Matrix/SchurComplement.lean`) concern different results (Schur's lemma in representation theory, the Schur-Zassenhaus theorem, and Schur complements of matrices).

### 2. Theorem 0.1.2 (Schur's theorem, finitary version)
**Assessment: non-included**
Statement: For every positive integer r, there exists N = N(r) such that if each element of [N] is colored using one of r colors, then there is a monochromatic solution to x + y = z.
Explanation: Finitary version of Schur's theorem. Not in mathlib for the same reason as above.

### 3. Theorem 0.1.3 (Fermat's Last Theorem mod p)
**Assessment: non-included**
Statement: For all sufficiently large primes p, there exist X, Y, Z in {1,...,p-1} such that X^n + Y^n = Z^n (mod p).
Explanation: This specific result about solutions to Fermat's equation modulo primes is not in mathlib.

### 4. Theorem 0.1.4 (Multicolor triangle Ramsey theorem)
**Assessment: non-included**
Statement: For every positive integer r, there is some integer N such that if each edge of K_N is colored using one of r colors, then there is a monochromatic triangle.
Explanation: Ramsey theory is not formalized in mathlib. There is no Ramsey number file or theorem.

### 5. Theorem 0.1.7 (Graph Ramsey theorem)
**Assessment: non-included**
Statement: For every k and r there exists N such that if each edge of K_N is colored using one of r colors, then there is a monochromatic K_k.
Explanation: Graph Ramsey theorem is not in mathlib.

### 6. Theorem 0.1.9 (Hypergraph Ramsey theorem)
**Assessment: non-included**
Statement: For every k, r, s there exists N such that if each edge of a complete s-uniform hypergraph on N vertices is colored using one of r colors, then there is a monochromatic clique on k vertices.
Explanation: Hypergraph Ramsey theorem is not in mathlib.

### 7. Proposition 0.1.12 (Multicolor triangle Ramsey numbers: exponential lower bound)
**Assessment: non-included**
Statement: For each positive integer r, there exists an edge-coloring of K_{2^r} using r colors with no monochromatic triangle.
Explanation: Not in mathlib. Ramsey theory lower bounds are not formalized.

### 8. Theorem 0.2.1 (van der Waerden's theorem)
**Assessment: included**
Statement: If the positive integers are colored using finitely many colors, then there is a monochromatic arithmetic progression of any given length.
Explanation: Van der Waerden's theorem is proved in mathlib as a corollary of the Hales-Jewett theorem. See `Mathlib/Combinatorics/HalesJewett.lean` which contains `Combinatorics.exists_mono_homothetic_copy`, a generalization of Van der Waerden's theorem.

### 9. Theorem 0.2.3 (Roth's theorem)
**Assessment: included**
Statement: Every subset of {1,...,N} with no 3-term arithmetic progression has size o(N).
Explanation: Roth's theorem on 3-APs is proved in mathlib via the triangle removal lemma and corners theorem. See `Mathlib/Combinatorics/Additive/Corner/Roth.lean` which contains `roth_3ap_theorem` and `rothNumberNat_isLittleO_id`.

### 10. Theorem 0.2.4 (Szemeredi's theorem)
**Assessment: non-included**
Statement: Every subset of the integers with positive upper density contains arithmetic progressions of any length.
Explanation: Szemeredi's theorem for arbitrary-length APs is not in mathlib. Only the regularity lemma (the main tool) and the k=3 case (Roth's theorem) are formalized.

### 11. Theorem 0.2.6 (Multidimensional Szemeredi theorem)
**Assessment: non-included**
Statement: Multidimensional generalization of Szemeredi's theorem.
Explanation: Not in mathlib. This is a deep result in ergodic theory/combinatorics.

### 12. Theorem 0.2.7 (Furstenberg-Sarkozy theorem)
**Assessment: non-included**
Statement: Every subset of integers with positive upper density contains two elements whose difference is a perfect square.
Explanation: Not in mathlib.

### 13. Theorem 0.2.8 (Polynomial Szemeredi theorem)
**Assessment: non-included**
Statement: Generalization of Szemeredi's theorem to polynomial progressions.
Explanation: Not in mathlib.

### 14. Theorem 0.2.9 (Green-Tao theorem)
**Assessment: non-included**
Statement: The primes contain arbitrarily long arithmetic progressions.
Explanation: The Green-Tao theorem is one of the most celebrated results in modern combinatorics and is not in mathlib.

### 15. Theorem 0.3.1 (Roth's theorem)
**Assessment: included**
Statement: Restatement of Roth's theorem from the perspective of the textbook's narrative.
Explanation: Same as statement 9. Formalized in `Mathlib/Combinatorics/Additive/Corner/Roth.lean`.

## Chapter 1: Forbidding a Subgraph

### 16. Theorem 1.1.1 (Mantel's theorem)
**Assessment: non-included**
Statement: Every n-vertex triangle-free graph has at most floor(n^2/4) edges.
Explanation: Mantel's theorem is not explicitly named in mathlib, though it follows as the r=2 case of Turan's theorem which is formalized. However, there is no explicit `mantel` theorem statement in mathlib.

### 17. Theorem 1.2.4 (Turan's theorem)
**Assessment: included**
Statement: The Turan graph T_{n,r} maximizes the number of edges among all n-vertex K_{r+1}-free graphs.
Explanation: Turan's theorem is fully formalized in `Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean`. The theorem `isTuranMaximal_iff_nonempty_iso_turanGraph` states that a graph is Turan-maximal if and only if it is isomorphic to the Turan graph.

### 18. Corollary 1.2.6 (Turan's theorem)
**Assessment: included**
Statement: ex(n, K_{r+1}) <= (1 - 1/r) * n^2/2.
Explanation: The Turan density and edge count bounds follow from the formalization. The file `Mathlib/Combinatorics/SimpleGraph/Extremal/TuranDensity.lean` treats Turan density asymptotics.

### 19. Lemma 1.2.7 (Maximum number of edges in an r-partite graph)
**Assessment: non-included**
Statement: Among n-vertex r-partite graphs, T_{n,r} is the unique graph with the maximum number of edges.
Explanation: While the Turan graph is defined in mathlib, this specific lemma about maximizing edges within the class of r-partite graphs is not explicitly stated.

### 20. Proposition 1.3.1 (Monotonicity of Turan numbers)
**Assessment: non-included**
Statement: If H is a subgraph of H', then ex(n, H) <= ex(n, H').
Explanation: Basic monotonicity of extremal numbers is likely provable from the mathlib definitions, but is not explicitly stated as a theorem.

### 21. Theorem 1.3.4 (Supersaturation)
**Assessment: non-included**
Statement: If a graph has significantly more edges than ex(n, H), it contains many copies of H.
Explanation: The supersaturation phenomenon is not formalized in mathlib.

### 22. Theorem 1.4.2 (Kovari-Sos-Turan theorem)
**Assessment: non-included**
Statement: For positive integers s <= t, ex(n, K_{s,t}) <= C * n^{2-1/s}.
Explanation: The KST theorem is not in mathlib. No Kovari-Sos-Turan or bipartite Turan results are formalized.

### 23. Theorem 1.4.3 (KST theorem)
**Assessment: non-included**
Statement: Precise version: ex(n, K_{s,t}) <= ((t-1)^{1/s}/2 + o(1)) * n^{2-1/s}.
Explanation: Not in mathlib.

### 24. Corollary 1.4.5
**Assessment: non-included**
Statement: For every bipartite graph H, there exists c > 0 such that ex(n, H) = O(n^{2-c}).
Explanation: Not in mathlib.

### 25. Theorem 1.4.8 (Upper bound on the unit distance problem)
**Assessment: non-included**
Statement: The maximum number of unit distances among n points in the plane is O(n^{4/3}).
Explanation: Discrete geometry results like this are not in mathlib.

### 26. Theorem 1.4.10 (Guth-Katz distinct distances theorem)
**Assessment: non-included**
Statement: n points in the plane determine at least cn/log(n) distinct distances.
Explanation: This deep algebraic geometry result is not in mathlib.

### 27. Theorem 1.5.1 (Erdos-Stone-Simonovits theorem)
**Assessment: non-included**
Statement: For any graph H with chi(H) >= 2, ex(n, H) = (1 - 1/(chi(H)-1) + o(1)) * n^2/2.
Explanation: The Erdos-Stone-Simonovits theorem is not in mathlib, despite its fundamental importance.

### 28. Theorem 1.5.5 (Erdos-Stone theorem)
**Assessment: non-included**
Statement: Complete bipartite-like Turan number growth.
Explanation: Not in mathlib.

### 29. Theorem 1.5.6 (Hypergraph KST)
**Assessment: non-included**
Statement: Hypergraph generalization of the KST theorem.
Explanation: Hypergraph extremal theory is not developed in mathlib.

### 30. Theorem 1.5.7 (KST for 3-graphs)
**Assessment: non-included**
Statement: Specific KST bound for 3-uniform hypergraphs.
Explanation: Not in mathlib.

### 31. Theorem 1.5.9 (Hypergraph KST)
**Assessment: non-included**
Statement: General hypergraph KST.
Explanation: Not in mathlib.

### 32. Theorem 1.6.1 (Exact Turan number of an odd cycle)
**Assessment: non-included**
Statement: ex(n, C_{2k+1}) = floor(n^2/4).
Explanation: Not in mathlib. Cycle-specific Turan numbers are not formalized.

### 33. Theorem 1.6.2 (Exact Turan number of a color-edge-critical graph)
**Assessment: non-included**
Statement: Exact Turan number for color-critical graphs.
Explanation: Not in mathlib.

### 34. Theorem 1.6.3 (Even cycles)
**Assessment: non-included**
Statement: ex(n, C_{2k}) = O(n^{1+1/k}).
Explanation: Not in mathlib.

### 35. Theorem 1.6.5 (Short even cycles)
**Assessment: non-included**
Statement: ex(n, C_{2k}) = Omega(n^{1+1/k}) for k in {2,3,5}.
Explanation: Not in mathlib.

### 36. Lemma 1.6.6 (Large bipartite subgraph)
**Assessment: non-included**
Statement: Every graph G has a bipartite subgraph with at least e(G)/2 edges.
Explanation: Not in mathlib as an explicit statement.

### 37. Lemma 1.6.7 (Large average degree implies subgraph with large minimum degree)
**Assessment: non-included**
Statement: Every graph with average degree 2t has a subgraph with minimum degree > t.
Explanation: Not in mathlib.

### 38. Theorem 1.7.1 (Bounded degree bipartite graph: Turan number upper bound)
**Assessment: non-included**
Statement: Upper bounds on Turan numbers for bounded-degree bipartite graphs.
Explanation: Not in mathlib.

### 39. Theorem 1.7.5 (Dependent random choice)
**Assessment: non-included**
Statement: The dependent random choice technique for finding subsets with many common neighbors.
Explanation: Not in mathlib.

### 40. Theorem 1.9.1 (Randomized lower bound)
**Assessment: non-included**
Statement: Random graph lower bound for Turan numbers.
Explanation: Not in mathlib.

### 41. Corollary 1.9.3 (Randomized lower bound)
**Assessment: non-included**
Statement: Explicit lower bound from the randomized argument.
Explanation: Not in mathlib.

### 42. Theorem 1.10.1 (Construction of K_{2,2}-free graphs)
**Assessment: non-included**
Statement: Algebraic construction of K_{2,2}-free graphs showing tightness of KST.
Explanation: Not in mathlib.

### 43. Corollary 1.10.2 (Turan number of K_{2,2})
**Assessment: non-included**
Statement: ex(n, K_{2,2}) = Theta(n^{3/2}).
Explanation: Not in mathlib.

### 44. Theorem 1.10.3 (Large gaps between primes)
**Assessment: non-included**
Statement: There exist large gaps between consecutive primes.
Explanation: While mathlib has many results about primes, this specific gap statement is not formalized.

### 45. Theorem 1.10.5 (Construction of K_{3,3}-free graphs)
**Assessment: non-included**
Statement: Algebraic construction of K_{3,3}-free graphs.
Explanation: Not in mathlib.

### 46. Theorem 1.10.7 (Tightness of KST bound when t > (s-1)!)
**Assessment: non-included**
Statement: KST bound is tight when t exceeds (s-1)!.
Explanation: Not in mathlib.

### 47. Corollary 1.10.8 (Tightness of KST bound when t > (s-1)!)
**Assessment: non-included**
Statement: Corollary of the tightness result.
Explanation: Not in mathlib.

### 48. Proposition 1.10.10
**Assessment: non-included**
Statement: Technical result about algebraic constructions for extremal graph theory.
Explanation: Not in mathlib.

### 49. Theorem 1.10.11
**Assessment: non-included**
Statement: Technical result about algebraic constructions.
Explanation: Not in mathlib.

### 50. Proposition 1.10.14
**Assessment: non-included**
Statement: Technical result about constructions.
Explanation: Not in mathlib.

### 51. Theorem 1.10.15 (Tight lower bound for avoiding C_{2k} for k in {2,3,5})
**Assessment: non-included**
Statement: Tight algebraic constructions for even cycle Turan numbers.
Explanation: Not in mathlib.

### 52. Proposition 1.10.18
**Assessment: non-included**
Statement: Technical result about algebraic constructions.
Explanation: Not in mathlib.

### 53. Theorem 1.11.1 (Tightness of KST bound for large t)
**Assessment: non-included**
Statement: KST bound is tight for large t using algebraic geometry.
Explanation: Not in mathlib.

### 54. Lemma 1.11.2 (Random polynomial)
**Assessment: non-included**
Statement: Properties of random polynomials over finite fields.
Explanation: Not in mathlib.

### 55. Lemma 1.11.3 (Random polynomial)
**Assessment: non-included**
Statement: More properties of random polynomials over finite fields.
Explanation: Not in mathlib.

### 56. Lemma 1.11.5 (Dichotomy: number of common zeros)
**Assessment: non-included**
Statement: Bezout-type result about common zeros of polynomials.
Explanation: Not in mathlib in this combinatorial form.

### 57. Theorem 1.11.6 (Lang-Weil bound)
**Assessment: non-included**
Statement: The number of rational points on an algebraic variety over a finite field is approximately q^d.
Explanation: The Lang-Weil bound is not in mathlib.

## Chapter 2: Szemeredi's Graph Regularity Lemma

### 58. Theorem 2.1.9 (Szemeredi's graph regularity lemma)
**Assessment: included**
Statement: For any epsilon > 0 and integer l, every sufficiently large graph has an epsilon-uniform partition into at most M parts.
Explanation: Fully formalized in `Mathlib/Combinatorics/SimpleGraph/Regularity/Lemma.lean` as `szemeredi_regularity`. The proof follows the standard energy increment argument.

### 59. Lemma 2.1.11 (Energy never decreases under refinement)
**Assessment: non-included**
Statement: Refining a partition never decreases its energy.
Explanation: While energy is defined in `Mathlib/Combinatorics/SimpleGraph/Regularity/Energy.lean`, this specific monotonicity lemma for general refinements may not be an explicit standalone theorem.

### 60. Lemma 2.1.12 (Energy never decreases under refinement)
**Assessment: non-included**
Statement: Variant of the energy monotonicity result.
Explanation: Internal to the regularity lemma proof machinery.

### 61. Lemma 2.1.13 (Energy boost for an irregular pair)
**Assessment: non-included**
Statement: An irregular pair witnesses a non-trivial energy boost upon refinement.
Explanation: Part of the internal proof machinery in the regularity directory; the increment-related lemmas handle this internally.

### 62. Lemma 2.1.14 (Energy boost for an irregular partition)
**Assessment: non-included**
Statement: An irregular partition has significant energy boost after increment.
Explanation: This is handled internally by the regularity lemma proof in mathlib but not as an explicit standalone statement matching this formulation.

### 63. Theorem 2.1.17 (Lower bound on the number of parts in a regularity partition)
**Assessment: non-included**
Statement: The number of parts in a regularity partition must grow as a tower function.
Explanation: Not formalized as a standalone theorem in mathlib.

### 64. Theorem 2.1.19 (Regularity starting with an arbitrary initial partition)
**Assessment: non-included**
Statement: One can start with an arbitrary initial partition and refine it.
Explanation: Not in mathlib as stated. The formalized version starts with an arbitrary equipartition.

### 65. Theorem 2.1.20 (Equitable regularity lemma)
**Assessment: included**
Statement: Equitable (equipartition) version of the regularity lemma.
Explanation: This is precisely the version proved in mathlib: `szemeredi_regularity` in `Mathlib/Combinatorics/SimpleGraph/Regularity/Lemma.lean` produces an equitable partition.

### 66. Theorem 2.1.26 (epsilon-regular subset)
**Assessment: non-included**
Statement: One can find an epsilon-regular large subset within certain graph pairs.
Explanation: Not in mathlib.

### 67. Theorem 2.2.1 (Triangle counting lemma)
**Assessment: included**
Statement: If pairs in a tripartite graph are epsilon-regular with positive density, the graph contains roughly the expected number of triangles.
Explanation: The triangle counting lemma is formalized in `Mathlib/Combinatorics/SimpleGraph/Triangle/Counting.lean`.

### 68. Lemma 2.2.3 (Most vertices have roughly the same degree)
**Assessment: non-included**
Statement: In a regular pair, most vertices have degree close to the expected value.
Explanation: Not in mathlib as a standalone lemma.

### 69. Theorem 2.3.1 (Triangle removal lemma)
**Assessment: included**
Statement: If a graph on n vertices contains o(n^3) triangles, then it can be made triangle-free by removing o(n^2) edges.
Explanation: Formalized in `Mathlib/Combinatorics/SimpleGraph/Triangle/Removal.lean`. The bound `triangleRemovalBound` is explicit.

### 70. Corollary 2.3.3 (Diamond-free lemma)
**Assessment: non-included**
Statement: A version of the removal lemma for diamond subgraphs.
Explanation: Not in mathlib.

### 71. Theorem 2.3.5 ((6,3)-theorem)
**Assessment: non-included**
Statement: Any 3-uniform hypergraph on n vertices in which every 6 vertices span at most 2 edges has o(n^3) edges.
Explanation: Not in mathlib.

### 72. Theorem 2.4.1 (Roth's theorem)
**Assessment: included**
Statement: Any subset of {1,...,N} with no 3-term arithmetic progression has size o(N).
Explanation: This is the version of Roth's theorem derived from the triangle removal lemma and corners theorem. Formalized in `Mathlib/Combinatorics/Additive/Corner/Roth.lean`.

### 73. Theorem 2.4.2 (Corner-free)
**Assessment: included**
Statement: Any corner-free subset of {1,...,N}^2 has size o(N^2).
Explanation: The corners theorem is formalized in `Mathlib/Combinatorics/Additive/Corner/Roth.lean`. The result `cornersTheorem` gives the density-based bound.

### 74. Proposition 2.4.4 (Corner-free sets vs. 3-AP-free sets)
**Assessment: non-included**
Statement: Relationship between corner-free sets and 3-AP-free sets.
Explanation: Not explicitly in mathlib, though the reduction is used in the proof.

### 75. Theorem 2.5.1 (Behrend's construction)
**Assessment: included**
Statement: There exists a 3-AP-free subset of {1,...,N} of size N/exp(O(sqrt(log N))).
Explanation: Formalized in `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean`. The bound `Behrend.roth_lower_bound` gives the explicit lower bound on Roth numbers.

### 76. Corollary 2.5.2 (Lower bound for the diamond-free lemma)
**Assessment: non-included**
Statement: Lower bound for the diamond-free removal lemma using Behrend's construction.
Explanation: Not explicitly in mathlib, though the Behrend construction is available.

### 77. Proposition 2.6.1 (K_4 counting lemma)
**Assessment: non-included**
Statement: Counting lemma for K_4 in regular triples.
Explanation: Only the triangle counting lemma is formalized; the general graph counting lemma is not.

### 78. Theorem 2.6.2 (Graph counting lemma)
**Assessment: non-included**
Statement: General graph counting lemma for regular partitions.
Explanation: Not in mathlib. Only the triangle case is formalized.

### 79. Theorem 2.6.4 (Graph counting lemma)
**Assessment: non-included**
Statement: Variant of the graph counting lemma.
Explanation: Not in mathlib.

### 80. Theorem 2.6.5 (Graph removal lemma)
**Assessment: non-included**
Statement: General graph removal lemma: if a graph has few copies of H, then removing few edges makes it H-free.
Explanation: Not in mathlib. Only the triangle removal lemma is formalized.

### 81. Theorem 2.6.7 (Erdos-Stone-Simonovits theorem)
**Assessment: non-included**
Statement: Derivation of the ESS theorem from the regularity lemma.
Explanation: Not in mathlib.

### 82. Theorem 2.8.1 (Induced graph removal lemma)
**Assessment: non-included**
Statement: Induced version of the graph removal lemma.
Explanation: Not in mathlib.

### 83. Theorem 2.8.3 (Strong regularity lemma)
**Assessment: non-included**
Statement: A strengthening of the regularity lemma with better uniformity guarantees.
Explanation: Not in mathlib.

### 84. Theorem 2.1.19 (restated)
**Assessment: non-included**
Statement: Restatement of the regularity lemma with arbitrary initial partitions.
Explanation: Duplicate/restatement; not in mathlib in this form.

### 85. Lemma 2.8.7 (Energy and approximation)
**Assessment: non-included**
Statement: Connection between energy and L^2 approximation.
Explanation: Not in mathlib.

### 86. Theorem 2.8.9 (Strong regularity lemma)
**Assessment: non-included**
Statement: Full statement of the strong regularity lemma.
Explanation: Not in mathlib.

### 87. Theorem 2.8.11 (Infinite graph removal lemma)
**Assessment: non-included**
Statement: A version of the removal lemma for infinitely many forbidden subgraphs.
Explanation: Not in mathlib.

### 88. Theorem 2.8.13 (Infinite edge-colored graph removal lemma)
**Assessment: non-included**
Statement: Edge-colored version of the infinite removal lemma.
Explanation: Not in mathlib.

### 89. Theorem 2.9.1 (Triangle-freeness is testable)
**Assessment: non-included**
Statement: Triangle-freeness is a testable graph property.
Explanation: Property testing is not developed in mathlib.

### 90. Theorem 2.9.3 (Every hereditary graph property is testable)
**Assessment: non-included**
Statement: All hereditary graph properties are testable.
Explanation: Not in mathlib.

### 91. Theorem 2.10.1 (Hypergraph removal lemma)
**Assessment: non-included**
Statement: Removal lemma for hypergraphs.
Explanation: Not in mathlib.

### 92. Corollary 2.10.2
**Assessment: non-included**
Statement: Corollary of the hypergraph removal lemma.
Explanation: Not in mathlib.

### 93. Proposition 2.11.2 (Initial attempt at 3-graph regularity partition)
**Assessment: non-included**
Statement: Discussion of regularity for 3-uniform hypergraphs.
Explanation: Not in mathlib.

## Chapter 3: Pseudorandom Graphs

### 94. Theorem 3.1.1 (Quasirandom graphs)
**Assessment: non-included**
Statement: Characterization of quasirandom graphs via equivalent conditions (DISC, COUNT, EIG, CODEG).
Explanation: The Chung-Graham-Wilson theorem on quasirandom graph equivalences is not in mathlib.

### 95. Theorem 3.1.7 (Chernoff bound)
**Assessment: included**
Statement: If X is a sum of m independent Bernoulli random variables, then P(|X - EX| >= t) <= 2 exp(-t^2/(2m)).
Explanation: Chernoff bounds are in mathlib at `Mathlib/Probability/Moments/Basic.lean` (section `Chernoff`), and sub-Gaussian concentration results are in `Mathlib/Probability/Moments/SubGaussian.lean` which includes Hoeffding's inequality.

### 96. Proposition 3.1.8 (Edge densities in a random graph)
**Assessment: non-included**
Statement: With high probability, G(n,p) has edge density close to p for all subsets.
Explanation: Not in mathlib. Random graph properties are not developed.

### 97. Corollary 3.1.9 (Random graphs are quasirandom)
**Assessment: non-included**
Statement: G(n,p) is quasirandom with high probability.
Explanation: Not in mathlib.

### 98. Proposition 3.1.14 (Minimum 4-cycle density)
**Assessment: non-included**
Statement: The minimum 4-cycle density given edge density p is p^4.
Explanation: Not in mathlib.

### 99. Lemma 3.1.20 (Top eigenvalue and average degree)
**Assessment: non-included**
Statement: The largest eigenvalue of the adjacency matrix equals the average degree for regular graphs.
Explanation: While mathlib has adjacency matrix definitions, this specific spectral graph theory result is not formalized.

### 100. Theorem 3.1.25 (Bipartite quasirandom graphs)
**Assessment: non-included**
Statement: Characterization of quasirandom bipartite graphs.
Explanation: Not in mathlib.

### 101. Proposition 3.1.28 (Random bipartite graphs are typically quasirandom)
**Assessment: non-included**
Statement: Random bipartite graphs satisfy quasirandomness.
Explanation: Not in mathlib.

### 102. Theorem 3.2.4 (Expander mixing lemma)
**Assessment: non-included**
Statement: In a d-regular graph, |e(S,T) - d|S||T|/n| <= lambda_2 * sqrt(|S||T|).
Explanation: The expander mixing lemma is not in mathlib.

### 103. Theorem 3.2.6 (Expander mixing lemma -- slightly strengthened)
**Assessment: non-included**
Statement: Strengthened version of the expander mixing lemma.
Explanation: Not in mathlib.

### 104. Theorem 3.2.9 (Bipartite expander mixing lemma)
**Assessment: non-included**
Statement: Bipartite version of the expander mixing lemma.
Explanation: Not in mathlib.

### 105. Theorem 3.2.12 (Converse to expander mixing lemma)
**Assessment: non-included**
Statement: The converse direction: quasirandomness implies spectral gap.
Explanation: Not in mathlib.

### 106. Theorem 3.2.13 (Cheeger's inequality)
**Assessment: non-included**
Statement: Cheeger's inequality relating spectral gap to edge expansion.
Explanation: Not in mathlib. Cheeger's inequality from spectral graph theory is not formalized.

### 107. Theorem 3.3.8 (Eigenvalues of abelian Cayley graphs on Z/nZ)
**Assessment: non-included**
Statement: The eigenvalues of Cayley graphs on cyclic groups are given by character sums.
Explanation: Cayley graphs are not formally defined in mathlib. The spectral theory of Cayley graphs is not developed.

### 108. Theorem 3.3.12 (Eigenvalues of Paley graphs)
**Assessment: non-included**
Statement: The non-trivial eigenvalues of Paley graphs are -(1 +/- sqrt(p))/2.
Explanation: Paley graphs are not defined in mathlib.

### 109. Theorem 3.3.14 (Gauss sum)
**Assessment: included**
Statement: The absolute value of the Gauss sum equals sqrt(p).
Explanation: Gauss sums and their properties are formalized in `Mathlib/NumberTheory/GaussSum.lean`. The result `gaussSum_sq` gives the square of the Gauss sum for quadratic characters.

### 110. Theorem 3.4.3 (Cayley graphs on quasirandom groups)
**Assessment: non-included**
Statement: Cayley graphs on quasirandom groups have small second eigenvalue.
Explanation: Not in mathlib.

### 111. Theorem 3.4.6 (Vertex-transitive graphs and quasirandom groups)
**Assessment: non-included**
Statement: Connection between vertex-transitive graphs and quasirandom groups.
Explanation: Not in mathlib.

### 112. Theorem 3.4.7 (Bipartite Cayley graphs on quasirandom groups)
**Assessment: non-included**
Statement: Bipartite version of Cayley graph quasirandomness on quasirandom groups.
Explanation: Not in mathlib.

### 113. Theorem 3.4.9 (Mixing in quasirandom groups)
**Assessment: non-included**
Statement: Mixing property of quasirandom groups.
Explanation: Not in mathlib.

### 114. Corollary 3.4.10 (Product-free sets)
**Assessment: non-included**
Statement: Quasirandom groups have small product-free sets.
Explanation: Not in mathlib.

### 115. Theorem 3.4.13 (PSL(2,p) is quasirandom)
**Assessment: non-included**
Statement: PSL(2,p) is a quasirandom group.
Explanation: Not in mathlib.

### 116. Corollary 3.4.14 (Product-free subset of PSL(2,p))
**Assessment: non-included**
Statement: Maximum size of a product-free subset of PSL(2,p).
Explanation: Not in mathlib.

### 117. Theorem 3.4.15 (Quasirandom groups)
**Assessment: non-included**
Statement: Characterization of quasirandom groups.
Explanation: Not in mathlib.

### 118. Theorem 3.4.16 (PRODFREE implies REP)
**Assessment: non-included**
Statement: Product-free implies representation-theoretic quasirandomness.
Explanation: Not in mathlib.

### 119. Proposition 3.5.2 (SparseEIG implies SPARSEDISC)
**Assessment: non-included**
Statement: Sparse eigenvalue condition implies sparse discrepancy.
Explanation: Not in mathlib.

### 120. Theorem 3.5.3 (SparseDISC implies SparseEIG for Cayley graphs)
**Assessment: non-included**
Statement: Sparse discrepancy implies sparse eigenvalue condition for Cayley graphs.
Explanation: Not in mathlib.

### 121. Theorem 3.5.4 (SparseDISC implies SparseEIG for vertex-transitive graphs)
**Assessment: non-included**
Statement: Sparse discrepancy implies sparse eigenvalue for vertex-transitive graphs.
Explanation: Not in mathlib.

### 122. Theorem 3.5.5 (Grothendieck's inequality)
**Assessment: non-included**
Statement: There exists a constant K such that certain bilinear form optimization over vectors is bounded by K times the optimization over scalars.
Explanation: Grothendieck's inequality in this functional-analytic/combinatorial form is not in mathlib. The Grothendieck files in mathlib concern category theory (Grothendieck constructions/topologies).

### 123. Theorem 3.6.2 (Alon-Boppana second eigenvalue bound)
**Assessment: non-included**
Statement: For any d-regular graph on n vertices, the second eigenvalue is at least 2sqrt(d-1) - o(1).
Explanation: Not in mathlib.

### 124. Corollary 3.6.3 (Alon-Boppana second eigenvalue bound)
**Assessment: non-included**
Statement: Asymptotic form of Alon-Boppana bound.
Explanation: Not in mathlib.

### 125. Lemma 3.6.4 (Test vector)
**Assessment: non-included**
Statement: Construction of a test vector for the Alon-Boppana bound.
Explanation: Not in mathlib.

### 126. Theorem 3.6.7 (Friedman's second eigenvalue theorem)
**Assessment: non-included**
Statement: Random d-regular graphs are nearly Ramanujan.
Explanation: Not in mathlib.

### 127. Theorem 3.6.10 (Existence of Ramanujan graphs)
**Assessment: non-included**
Statement: Ramanujan graphs exist for every degree.
Explanation: Not in mathlib.

### 128. Theorem 3.6.13 (Bipartite Ramanujan graphs of every degree)
**Assessment: non-included**
Statement: Bipartite Ramanujan graphs exist for every degree.
Explanation: Not in mathlib.

## Chapter 4: Graph Limits

### 129. Theorem 4.2.7 (Compactness of graphon space)
**Assessment: non-included**
Statement: The space of graphons (modulo measure-preserving rearrangements) is compact.
Explanation: Graphon theory is not developed in mathlib.

### 130. Theorem 4.2.8 (Graphs are dense in the space of graphons)
**Assessment: non-included**
Statement: The set of graphs (as step-function graphons) is dense in graphon space.
Explanation: Not in mathlib.

### 131. Corollary 4.2.10 (Graphons complete graphs)
**Assessment: non-included**
Statement: Graphon space is complete.
Explanation: Not in mathlib.

### 132. Theorem 4.3.7 (Equivalence of convergence)
**Assessment: non-included**
Statement: Left-convergence is equivalent to cut metric convergence for graphons.
Explanation: Not in mathlib.

### 133. Theorem 4.3.8 (Existence of limit for left-convergence)
**Assessment: non-included**
Statement: Every left-convergent graph sequence has a graphon limit.
Explanation: Not in mathlib.

### 134. Theorem 4.4.2 (W-random graphs left-converge to W)
**Assessment: non-included**
Statement: W-random graphs converge to the graphon W.
Explanation: Not in mathlib.

### 135. Theorem 4.4.4 (Bounded differences inequality)
**Assessment: non-included**
Statement: McDiarmid's bounded differences inequality / Azuma-Hoeffding.
Explanation: While mathlib has Hoeffding's lemma and Azuma-Hoeffding inequality in `Mathlib/Probability/Moments/SubGaussian.lean`, the specific "bounded differences inequality" as stated in the textbook (for general Lipschitz functions of independent variables) is not explicitly present in this exact form.

### 136. Theorem 4.4.5 (Sample concentration for graphons)
**Assessment: non-included**
Statement: Concentration inequality for subgraph densities in W-random graphs.
Explanation: Not in mathlib. Graphon theory is not developed.

### 137. Theorem 4.4.6 (Borel-Cantelli lemma)
**Assessment: included**
Statement: If the sum of probabilities of events is finite, the probability of infinitely many occurring is zero.
Explanation: The first Borel-Cantelli lemma is `MeasureTheory.measure_limsup_atTop_eq_zero` in `Mathlib/MeasureTheory/OuterMeasure/BorelCantelli.lean`. The second Borel-Cantelli lemma (for independent events) is `ProbabilityTheory.measure_limsup_eq_one` in `Mathlib/Probability/BorelCantelli.lean`.

### 138. Theorem 4.5.1 (Counting lemma)
**Assessment: non-included**
Statement: Counting lemma for graphon homomorphism densities.
Explanation: Not in mathlib.

### 139. Corollary 4.5.2 (Cut metric convergence implies left-convergence)
**Assessment: non-included**
Statement: Cut metric convergence implies left-convergence.
Explanation: Not in mathlib.

### 140. Lemma 4.5.3 (Reformulation of cut norm)
**Assessment: non-included**
Statement: Alternative characterization of the cut norm.
Explanation: Not in mathlib.

### 141. Proposition 4.5.4 (Triangle counting lemma)
**Assessment: non-included**
Statement: Triangle counting lemma in the graphon setting.
Explanation: Not in mathlib.

### 142. Theorem 4.6.3 (Weak regularity lemma for graphs)
**Assessment: non-included**
Statement: Frieze-Kannan weak regularity lemma.
Explanation: Not in mathlib. Only Szemeredi's (strong) regularity lemma is formalized.

### 143. Theorem 4.6.7 (Weak regularity lemma for graphons)
**Assessment: non-included**
Statement: Weak regularity lemma stated for graphons.
Explanation: Not in mathlib.

### 144. Lemma 4.6.9 (L^2 energy increment)
**Assessment: non-included**
Statement: L^2 energy increment for the weak regularity proof.
Explanation: Not in mathlib.

### 145. Theorem 4.6.10 (Weak regularity lemma for graphons)
**Assessment: non-included**
Statement: Variant of the weak regularity lemma.
Explanation: Not in mathlib.

### 146. Theorem 4.7.6 (Martingale convergence theorem)
**Assessment: included**
Statement: Every bounded martingale converges with probability 1.
Explanation: Formalized in `Mathlib/Probability/Martingale/Convergence.lean`. The theorem `Submartingale.ae_tendsto_limitProcess` proves that L^1-bounded submartingales converge almost everywhere.

### 147. Proposition 4.8.1 (Uniform approximation of graphons by graphs)
**Assessment: non-included**
Statement: Every graphon can be uniformly approximated by graphs.
Explanation: Not in mathlib.

### 148. Theorem 4.8.4 ("Regularity lemma" for bounded degree graphs)
**Assessment: non-included**
Statement: Regularity-type result for bounded degree graphs using graphons.
Explanation: Not in mathlib.

### 149. Theorem 4.9.1 (Uniqueness of moments)
**Assessment: non-included**
Statement: A bounded measurable function on [0,1]^2 is determined by its graph homomorphism densities.
Explanation: Not in mathlib.

### 150. Lemma 4.9.3 (Tail bounds for U-statistics)
**Assessment: non-included**
Statement: Tail bounds for U-statistics related to graphon sampling.
Explanation: Not in mathlib.

### 151. Lemma 4.9.4 (1-norm convergence for H(k,W))
**Assessment: non-included**
Statement: Convergence result for graph homomorphism density functionals.
Explanation: Not in mathlib.

### 152. Corollary 4.9.6 (Inverse counting lemma)
**Assessment: non-included**
Statement: Inverse counting lemma for graph limits.
Explanation: Not in mathlib.

### 153. Theorem 4.9.9 (Inverse counting lemma)
**Assessment: non-included**
Statement: Full inverse counting lemma.
Explanation: Not in mathlib.

## Chapter 5: Graph Densities and Inequalities

### 154. Proposition 5.0.7 (Forcing and quasirandomness)
**Assessment: non-included**
Statement: A graph H is forcing if and only if it satisfies a quasirandomness condition.
Explanation: Not in mathlib.

### 155. Theorem 5.1.2 (Max triangle density)
**Assessment: non-included**
Statement: The maximum triangle density among graphs with given edge density p is p^{3/2}.
Explanation: Not in mathlib.

### 156. Lemma 5.1.3 (A power sum inequality)
**Assessment: non-included**
Statement: For t >= 1 and a_i >= 0, sum(a_i^t) <= (sum a_i)^t.
Explanation: While mathlib has many inequalities about power sums (e.g., Jensen's inequality), this exact formulation is not a named theorem.

### 157. Theorem 5.1.5 (Maximum clique density)
**Assessment: non-included**
Statement: Maximum K_r-density given edge density.
Explanation: Not in mathlib.

### 158. Theorem 5.1.7 (Minimum triangle density)
**Assessment: non-included**
Statement: Kruskal-Katona type result for minimum triangle density.
Explanation: Not in mathlib.

### 159. Theorem 5.1.8 (Minimum clique density)
**Assessment: non-included**
Statement: Minimum K_r-density given edge density (Razborov flag algebras).
Explanation: Not in mathlib.

### 160. Theorem 5.2.1 (K_{2,2} is Sidorenko)
**Assessment: non-included**
Statement: The Sidorenko property for K_{2,2} (4-cycle).
Explanation: Not in mathlib.

### 161. Lemma 5.2.2
**Assessment: non-included**
Statement: Technical lemma for Sidorenko-type results.
Explanation: Not in mathlib.

### 162. Lemma 5.2.3
**Assessment: non-included**
Statement: Technical lemma.
Explanation: Not in mathlib.

### 163. Theorem 5.2.5 (Triangle is common)
**Assessment: non-included**
Statement: The triangle is a common graph (Goodman's formula).
Explanation: Not in mathlib.

### 164. Proposition 5.2.7
**Assessment: non-included**
Statement: Technical result about graph densities.
Explanation: Not in mathlib.

### 165. Theorem 5.2.8 (Lower bound on triangle density)
**Assessment: non-included**
Statement: Lower bound on triangle density given edge density.
Explanation: Not in mathlib.

### 166. Theorem 5.2.9
**Assessment: non-included**
Statement: Graph density result.
Explanation: Not in mathlib.

### 167. Theorem 5.2.11 (Maximum number 5-cycles in a triangle-free graph)
**Assessment: non-included**
Statement: Maximum 5-cycle density in triangle-free graphs.
Explanation: Not in mathlib.

### 168. Theorem 5.2.12 (Inducibility of the 5-cycle)
**Assessment: non-included**
Statement: The inducibility of C_5.
Explanation: Not in mathlib.

### 169. Theorem 5.3.1 (Complete bipartite graphs are Sidorenko)
**Assessment: non-included**
Statement: All complete bipartite graphs satisfy Sidorenko's conjecture.
Explanation: Not in mathlib.

### 170. Lemma 5.3.2
**Assessment: non-included**
Statement: Technical lemma for Sidorenko proof.
Explanation: Not in mathlib.

### 171. Lemma 5.3.3
**Assessment: non-included**
Statement: Technical lemma.
Explanation: Not in mathlib.

### 172. Theorem 5.3.4
**Assessment: non-included**
Statement: Generalization for Sidorenko-type inequalities.
Explanation: Not in mathlib.

### 173. Theorem 5.3.5 (Generalized Holder inequality for a triangle)
**Assessment: non-included**
Statement: A Holder-type inequality for triangle densities in graphons.
Explanation: Not in mathlib in this graph-theoretic form. The classical Holder inequality exists in mathlib.

### 174. Theorem 5.3.7 (Generalized Holder inequality)
**Assessment: non-included**
Statement: Generalized Holder inequality for graph homomorphism densities.
Explanation: Not in mathlib in this form.

### 175. Corollary 5.3.10 (Upper bound on F-density)
**Assessment: non-included**
Statement: Upper bound on homomorphism density of F.
Explanation: Not in mathlib.

### 176. Theorem 5.3.11 (Generalized Holder inequality)
**Assessment: non-included**
Statement: Another variant of the generalized Holder inequality.
Explanation: Not in mathlib.

### 177. Theorem 5.3.14 (Maximum number of independent sets in a regular graph)
**Assessment: non-included**
Statement: Maximum number of independent sets in a d-regular graph on n vertices.
Explanation: Not in mathlib.

### 178. Theorem 5.3.15 (The maximum number of H-colorings in a regular graph)
**Assessment: non-included**
Statement: Maximum H-coloring count in regular graphs.
Explanation: Not in mathlib.

### 179. Theorem 5.3.16
**Assessment: non-included**
Statement: Related result about graph colorings.
Explanation: Not in mathlib.

### 180. Theorem 5.3.19 (Bipartite double cover for independent sets)
**Assessment: non-included**
Statement: Bipartite double cover argument for independent set counting.
Explanation: Not in mathlib.

### 181. Theorem 5.4.1 (Turan's theorem)
**Assessment: included**
Statement: Restatement of Turan's theorem in the context of graph density inequalities.
Explanation: Same as statement 17. Formalized in `Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean`.

### 182. Lemma 5.4.3 (Extreme points of a linear combination of symmetric polynomials)
**Assessment: non-included**
Statement: Characterization of extreme points for optimization of symmetric polynomial combinations.
Explanation: Not in mathlib in this combinatorial form.

### 183. Theorem 5.4.4 (Linear inequalities between clique densities)
**Assessment: non-included**
Statement: Determination of linear inequalities between clique densities.
Explanation: Not in mathlib.

### 184. Corollary 5.4.6 (Convex hull of feasible clique densities)
**Assessment: non-included**
Statement: Convex hull characterization of feasible density tuples.
Explanation: Not in mathlib.

### 185. Lemma 5.5.3 (Uniform bound)
**Assessment: non-included**
Statement: Uniform bound on entropy.
Explanation: Not in mathlib in this form. Information-theoretic entropy is not developed in mathlib.

### 186. Lemma 5.5.5 (Chain rule)
**Assessment: non-included**
Statement: Chain rule for Shannon entropy: H(X,Y) = H(X) + H(Y|X).
Explanation: Shannon entropy and its chain rule are not formalized in mathlib.

### 187. Lemma 5.5.6 (Subadditivity)
**Assessment: non-included**
Statement: Subadditivity of entropy: H(X,Y) <= H(X) + H(Y).
Explanation: Not in mathlib.

### 188. Lemma 5.5.8 (Dropping conditioning)
**Assessment: non-included**
Statement: H(X|Y) <= H(X) (conditioning reduces entropy).
Explanation: Not in mathlib.

### 189. Theorem 5.5.10
**Assessment: non-included**
Statement: Entropy-based graph density result.
Explanation: Not in mathlib.

### 190. Theorem 5.5.11
**Assessment: non-included**
Statement: Entropy-based result.
Explanation: Not in mathlib.

### 191. Theorem 5.5.12
**Assessment: non-included**
Statement: Entropy-based result.
Explanation: Not in mathlib.

### 192. Theorem 5.5.14
**Assessment: non-included**
Statement: Entropy-based result.
Explanation: Not in mathlib.

### 193. Theorem 5.5.16 (Shearer's entropy inequality, special case)
**Assessment: non-included**
Statement: 2H(X,Y,Z) <= H(X,Y) + H(X,Z) + H(Y,Z).
Explanation: Shearer's entropy inequality is not in mathlib.

### 194. Theorem 5.5.17 (Shearer's entropy inequality)
**Assessment: non-included**
Statement: General Shearer's entropy inequality for hypergraphs.
Explanation: Not in mathlib.

### 195. Theorem 5.5.20 (The maximum number of H-colorings in a regular graph)
**Assessment: non-included**
Statement: Entropy proof of the maximum H-coloring theorem.
Explanation: Not in mathlib.

## Chapter 6: Fourier Analysis

### 196. Theorem 6.1.2 (Fourier inversion formula)
**Assessment: non-included**
Statement: Fourier inversion formula on F_p^n.
Explanation: While mathlib has Fourier analysis over R (`Analysis/Fourier/`), the discrete Fourier analysis on finite abelian groups F_p^n used in additive combinatorics is not developed. The mathlib Fourier transform is for functions on locally compact abelian groups, not in the finite field model used here.

### 197. Theorem 6.1.3 (Parseval / Plancherel)
**Assessment: non-included**
Statement: Parseval/Plancherel identity on F_p^n.
Explanation: Parseval's identity exists in mathlib for Fourier series on the additive circle (`Analysis/Fourier/AddCircle.lean`) and for L^2 functions (`Analysis/Fourier/LpSpace.lean`), but not for the discrete finite field model F_p^n.

### 198. Theorem 6.1.7 (Convolution identity)
**Assessment: non-included**
Statement: The Fourier transform of a convolution is the product of Fourier transforms (on F_p^n).
Explanation: While mathlib has the convolution identity for the Fourier transform in the continuous setting (`Analysis/Fourier/Convolution.lean`), the discrete version for F_p^n is not available.

### 199. Proposition 6.1.9 (Fourier and 3-AP)
**Assessment: non-included**
Statement: The number of 3-APs can be expressed in terms of Fourier coefficients.
Explanation: Not in mathlib.

### 200. Theorem 6.2.1 (Roth's theorem in F_3^n)
**Assessment: non-included**
Statement: 3-AP-free subsets of F_3^n have density tending to 0.
Explanation: Not in mathlib. The mathlib formalization of Roth's theorem uses the regularity lemma approach, not the Fourier-analytic approach on F_3^n.

### 201. Lemma 6.2.4 (3-AP counting lemma)
**Assessment: non-included**
Statement: Counting 3-APs using Fourier analysis.
Explanation: Not in mathlib.

### 202. Lemma 6.2.6 (3-AP-free implies a large Fourier coefficient)
**Assessment: non-included**
Statement: A 3-AP-free set must have a large Fourier coefficient.
Explanation: Not in mathlib.

### 203. Lemma 6.2.7 (Large Fourier coefficient implies density increment)
**Assessment: non-included**
Statement: A large Fourier coefficient implies a density increment on a subspace.
Explanation: Not in mathlib.

### 204. Lemma 6.2.8 (3-AP-free implies density increment)
**Assessment: non-included**
Statement: 3-AP-free implies density increment on a subspace.
Explanation: Not in mathlib.

### 205. Theorem 6.3.2 (Fourier inversion formula)
**Assessment: non-included**
Statement: Fourier inversion on Z/NZ.
Explanation: Not in mathlib in this discrete form.

### 206. Theorem 6.3.3 (Parseval / Plancherel)
**Assessment: non-included**
Statement: Parseval on Z/NZ.
Explanation: Not in this discrete form in mathlib.

### 207. Theorem 6.3.5 (Convolution identity)
**Assessment: non-included**
Statement: Convolution identity on Z/NZ.
Explanation: Not in this discrete form in mathlib.

### 208. Proposition 6.3.6 (Fourier and 3-AP)
**Assessment: non-included**
Statement: 3-AP counting via Fourier analysis on Z/NZ.
Explanation: Not in mathlib.

### 209. Theorem 6.4.1 (Roth's theorem)
**Assessment: non-included**
Statement: Fourier-analytic proof of Roth's theorem over Z/NZ.
Explanation: Not in mathlib (the mathlib proof uses the regularity lemma approach).

### 210. Proposition 6.4.2 (3-AP counting lemma)
**Assessment: non-included**
Statement: Counting 3-APs on Z/NZ using Fourier methods.
Explanation: Not in mathlib.

### 211. Lemma 6.4.3 (3-AP-free implies a large Fourier coefficient)
**Assessment: non-included**
Statement: Large Fourier coefficient from 3-AP-freeness on Z/NZ.
Explanation: Not in mathlib.

### 212. Lemma 6.4.4 (Dirichlet's lemma)
**Assessment: non-included**
Statement: Dirichlet's lemma on simultaneous Diophantine approximation for Fourier analysis.
Explanation: Not in mathlib in this form (used for the density increment on progressions).

### 213. Lemma 6.4.5 (Partition into progression level sets)
**Assessment: non-included**
Statement: Partition of Z/NZ into level sets of a Fourier character.
Explanation: Not in mathlib.

### 214. Lemma 6.4.6 (3-AP-free implies density increment)
**Assessment: non-included**
Statement: Density increment argument for Roth's theorem on Z/NZ.
Explanation: Not in mathlib.

### 215. Theorem 6.5.1 (Roth's theorem in F_3^n: power-saving upper bound)
**Assessment: non-included**
Statement: The capset problem: 3-AP-free subsets of F_3^n have size at most (2.756...)^n.
Explanation: Not in mathlib. This is the Croot-Lev-Pach/Ellenberg-Gijswijt result.

### 216. Lemma 6.5.3 (Trivial upper bound for slice rank)
**Assessment: non-included**
Statement: Upper bound for slice rank of a tensor.
Explanation: Not in mathlib. Slice rank is not defined.

### 217. Lemma 6.5.4 (Vector with large support)
**Assessment: non-included**
Statement: A vector in a low-slice-rank subspace has large support.
Explanation: Not in mathlib.

### 218. Lemma 6.5.5 (Slice rank of a diagonal)
**Assessment: non-included**
Statement: The slice rank of a diagonal tensor.
Explanation: Not in mathlib.

### 219. Lemma 6.5.6 (Upper bound on the slice rank of 1_{x+y+z=0})
**Assessment: non-included**
Statement: Slice rank upper bound for the 3-AP indicator tensor.
Explanation: Not in mathlib.

### 220. Lemma 6.5.7 (A trinomial coefficient estimate)
**Assessment: non-included**
Statement: Estimate on multinomial coefficients.
Explanation: Not in mathlib in this specific form.

### 221. Theorem 6.5.9 (Roth's theorem in the finite field model)
**Assessment: non-included**
Statement: Improved Roth's theorem in F_q^n via polynomial method.
Explanation: Not in mathlib.

### 222. Theorem 6.6.4 (Arithmetic regularity lemma)
**Assessment: non-included**
Statement: Regularity lemma for functions on abelian groups.
Explanation: Not in mathlib.

### 223. Lemma 6.6.6 (Energy never decreases under refinement)
**Assessment: non-included**
Statement: Energy monotonicity for the arithmetic regularity lemma.
Explanation: Not in mathlib.

### 224. Lemma 6.6.7 (Local energy increment)
**Assessment: non-included**
Statement: Local energy increment for arithmetic regularity.
Explanation: Not in mathlib.

### 225. Lemma 6.6.8 (Global energy increment)
**Assessment: non-included**
Statement: Global energy increment for arithmetic regularity.
Explanation: Not in mathlib.

### 226. Theorem 6.6.11 (Arithmetic regularity decomposition)
**Assessment: non-included**
Statement: Arithmetic regularity decomposition into structured and pseudorandom parts.
Explanation: Not in mathlib.

### 227. Theorem 6.7.1 (Roth's theorem with popular common difference in F_3^n)
**Assessment: non-included**
Statement: Dense subset of F_3^n has many 3-APs with a popular common difference.
Explanation: Not in mathlib.

### 228. Theorem 6.7.3 (Roth's theorem with common difference in some subspace)
**Assessment: non-included**
Statement: Roth with common difference restricted to a subspace.
Explanation: Not in mathlib.

### 229. Theorem 6.7.5 (Roth's theorem with popular difference in finite abelian groups)
**Assessment: non-included**
Statement: Popular difference version of Roth for finite abelian groups.
Explanation: Not in mathlib.

### 230. Theorem 6.7.6 (Roth's theorem with popular difference in the integers)
**Assessment: non-included**
Statement: Popular difference version of Roth over the integers.
Explanation: Not in mathlib.

### 231. Theorem 6.7.8 (Popular difference for 4-APs)
**Assessment: non-included**
Statement: Popular differences exist for 4-APs.
Explanation: Not in mathlib.

### 232. Theorem 6.7.9 (Popular difference fails for 5-APs)
**Assessment: non-included**
Statement: Popular differences fail for 5-APs.
Explanation: Not in mathlib.

## Chapter 7: Structure of Set Addition

### 233. Proposition 7.1.1 (Easy bounds on sumset size)
**Assessment: non-included**
Statement: |A| <= |A+B| <= |A||B| and related elementary bounds.
Explanation: While mathlib has extensive sumset theory, these specific elementary bounds may not all be named explicitly as a single proposition.

### 234. Theorem 7.1.10 (Freiman's theorem)
**Assessment: non-included**
Statement: If |A+A| <= K|A|, then A is contained in a GAP of bounded rank and size.
Explanation: Freiman's theorem (the full structural result) is not in mathlib. Only Freiman homomorphisms are defined (`Mathlib/Combinatorics/Additive/FreimanHom.lean`).

### 235. Theorem 7.1.15 (Freiman's theorem for general abelian groups)
**Assessment: non-included**
Statement: Freiman's theorem for general abelian groups.
Explanation: Not in mathlib.

### 236. Theorem 7.2.1 (Ruzsa triangle inequality)
**Assessment: included**
Statement: |A-C| * |B| <= |A-B| * |B-C| (and variants).
Explanation: Formalized in `Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean` as `ruzsa_triangle_inequality_div_div_div` and additive variants.

### 237. Theorem 7.3.1 (Plunnecke's inequality)
**Assessment: included**
Statement: If |A+B| <= K|A|, then |nB - mB| <= K^{n+m}|A|.
Explanation: The Plunnecke-Ruzsa inequality is fully formalized in `Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean` as `pluennecke_ruzsa_inequality_pow_div_pow_mul` and variants.

### 238. Theorem 7.3.3 (Plunnecke's inequality)
**Assessment: included**
Statement: Variant of Plunnecke's inequality.
Explanation: Covered by the same file as above. Multiple forms are provided.

### 239. Lemma 7.3.4 (Expansion ratio bounds)
**Assessment: non-included**
Statement: Bounds on expansion ratios related to Plunnecke's inequality.
Explanation: The Plunnecke-Petridis inequality is in mathlib (`pluennecke_petridis_inequality_mul`), but this specific expansion ratio formulation may not be an exact match.

### 240. Corollary 7.3.6 (Another triangle inequality)
**Assessment: non-included**
Statement: Another form of the Ruzsa triangle inequality derived from Plunnecke.
Explanation: May be derivable from the mathlib results but not stated explicitly.

### 241. Theorem 7.4.1 (Ruzsa covering lemma)
**Assessment: included**
Statement: If |A+B| <= K|B|, then A can be covered by at most K translates of B-B.
Explanation: Formalized in `Mathlib/Combinatorics/Additive/RuzsaCovering.lean` as `ruzsa_covering_mul` (and additive variant `ruzsa_covering_add`).

### 242. Theorem 7.5.1 (Freiman's theorem in F_2^n)
**Assessment: non-included**
Statement: If A is a subset of F_2^n with |A+A| <= K|A|, then A is contained in a subspace of size <= K^2 * 2^K|A|.
Explanation: Not in mathlib.

### 243. Theorem 7.5.4 (Freiman's theorem in groups with bounded exponent)
**Assessment: non-included**
Statement: Freiman's theorem for groups with bounded exponent.
Explanation: Not in mathlib.

### 244. Proposition 7.6.6 (Small diameter sets)
**Assessment: non-included**
Statement: Sets with small sumset have small diameter.
Explanation: Not in mathlib.

### 245. Proposition 7.7.1 (Modeling lemma in finite field model)
**Assessment: non-included**
Statement: Ruzsa's modeling lemma in F_p^n.
Explanation: Not in mathlib.

### 246. Theorem 7.7.3 (Ruzsa modeling lemma)
**Assessment: non-included**
Statement: Ruzsa's modeling lemma: a set with small doubling in Z can be modeled in Z/NZ.
Explanation: Not in mathlib.

### 247. Theorem 7.8.3 (Bogolyubov's lemma in F_p^n)
**Assessment: non-included**
Statement: 2A - 2A contains a large subspace when A has positive density in F_p^n.
Explanation: Not in mathlib.

### 248. Theorem 7.8.5 (Bogolyubov's lemma in Z/NZ)
**Assessment: non-included**
Statement: Bogolyubov's lemma in Z/NZ.
Explanation: Not in mathlib.

### 249. Theorem 7.9.4 (Minkowski's second theorem)
**Assessment: non-included**
Statement: lambda_1 ... lambda_d * vol(K) <= 2^d * det(Lambda) for successive minima.
Explanation: Minkowski's second theorem (about successive minima) is not in mathlib. Only the first theorem (existence of a lattice point) is formalized.

### 250. Theorem 7.9.6 (Blichfeldt's theorem)
**Assessment: included**
Statement: If vol(S) > det(Lambda), then there exist distinct lattice points x, y such that (x+S) and (y+S) are not disjoint.
Explanation: Formalized in `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` as `exists_pair_mem_lattice_not_disjoint_vadd`.

### 251. Theorem 7.9.7 (Minkowski's first theorem)
**Assessment: included**
Statement: If K is a centrally symmetric convex body with vol(K) > 2^d * det(Lambda), then K contains a nonzero lattice point.
Explanation: Formalized in `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` as `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` (strict inequality) and `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` (non-strict, for compact sets).

### 252. Theorem 7.10.1 (Large GAP in a Bohr set)
**Assessment: non-included**
Statement: A Bohr set contains a large generalized arithmetic progression (GAP).
Explanation: Not in mathlib.

### 253. Theorem 7.11.1 (Freiman's theorem)
**Assessment: non-included**
Statement: Full statement of Freiman's theorem.
Explanation: Not in mathlib. Only supporting tools (Ruzsa covering, Plunnecke-Ruzsa, Freiman homomorphisms) are formalized.

### 254. Proposition 7.13.4 (Small doubling implies large additive energy)
**Assessment: non-included**
Statement: If |A+A| <= K|A|, then the additive energy E(A) >= |A|^3/K.
Explanation: While additive energy is related to results in mathlib, this specific bound is not formalized as a standalone statement.

### 255. Theorem 7.13.6 (Balog-Szemeredi-Gowers theorem)
**Assessment: non-included**
Statement: If A has large additive energy, then a large subset A' has small sumset.
Explanation: The Balog-Szemeredi-Gowers theorem is not in mathlib.

### 256. Theorem 7.13.7 (Balog-Szemeredi-Gowers theorem)
**Assessment: non-included**
Statement: Quantitative version of BSG.
Explanation: Not in mathlib.

### 257. Theorem 7.13.9 (Graph BSG)
**Assessment: non-included**
Statement: Graph-theoretic formulation of BSG.
Explanation: Not in mathlib.

### 258. Lemma 7.13.10 (Path of length 2 lemma)
**Assessment: non-included**
Statement: Counting paths of length 2 in dense bipartite graphs.
Explanation: Not in mathlib.

### 259. Lemma 7.13.11 (Path of length 3 lemma)
**Assessment: non-included**
Statement: Counting paths of length 3.
Explanation: Not in mathlib.

## Chapter 8: Sum-Product Phenomenon

### 260. Theorem 8.1.2 (Estimates on the multiplication table problem)
**Assessment: non-included**
Statement: The number of distinct products in an n x n multiplication table is n^2/(log n)^{1+o(1)}.
Explanation: Not in mathlib.

### 261. Theorem 8.1.3 (Hardy-Ramanujan theorem)
**Assessment: non-included**
Statement: The number of prime factors of a typical integer n is approximately log log n.
Explanation: The Hardy-Ramanujan theorem is not in mathlib.

### 262. Theorem 8.2.1 (Elekes' sum-product bound)
**Assessment: non-included**
Statement: max(|A+A|, |A*A|) >= c|A|^{5/4}.
Explanation: Not in mathlib.

### 263. Corollary 8.2.2 (Elekes' sum-product bound)
**Assessment: non-included**
Statement: Corollary of Elekes' bound.
Explanation: Not in mathlib.

### 264. Theorem 8.2.3 (Crossing number inequality)
**Assessment: non-included**
Statement: cr(G) >= e(G)^3 / (64 v(G)^2) when e(G) >= 4v(G).
Explanation: The crossing number inequality is not in mathlib.

### 265. Theorem 8.2.5 (Szemeredi-Trotter theorem)
**Assessment: non-included**
Statement: The maximum number of point-line incidences among n points and m lines is O(n^{2/3}m^{2/3} + n + m).
Explanation: The Szemeredi-Trotter theorem is not in mathlib.

### 266. Corollary 8.2.6
**Assessment: non-included**
Statement: Corollary of Szemeredi-Trotter.
Explanation: Not in mathlib.

### 267. Theorem 8.3.1 (Solymosi's sum-product bound)
**Assessment: non-included**
Statement: max(|A+A|, |A*A|) >= c|A|^{4/3} / (log|A|)^{1/3}.
Explanation: Not in mathlib.

### 268. Corollary 8.3.2 (Solymosi's sum-product bound)
**Assessment: non-included**
Statement: Corollary of Solymosi's bound.
Explanation: Not in mathlib.

### 269. Theorem 8.3.5 (Sum-product in prime finite fields)
**Assessment: non-included**
Statement: Sum-product phenomenon over F_p.
Explanation: Not in mathlib.

## Chapter 9: Relative Szemeredi Theorem and the Green-Tao Theorem

### 270. Theorem 9.0.1 (Green-Tao theorem)
**Assessment: non-included**
Statement: The primes contain arbitrarily long arithmetic progressions.
Explanation: The Green-Tao theorem is not in mathlib.

### 271. Theorem 9.1.1 (Szemeredi's theorem)
**Assessment: non-included**
Statement: Restatement of Szemeredi's theorem.
Explanation: Szemeredi's theorem for general k is not in mathlib.

### 272. Theorem 9.1.3 (Green-Tao)
**Assessment: non-included**
Statement: Reformulation of the Green-Tao theorem via relative Szemeredi.
Explanation: Not in mathlib.

### 273. Theorem 9.2.1 (Roth's theorem)
**Assessment: non-included**
Statement: Roth's theorem restated in the context of the relative approach.
Explanation: While Roth's theorem is in mathlib, this specific reformulation is part of the transference machinery which is not formalized.

### 274. Theorem 9.2.5 (Relative Roth theorem)
**Assessment: non-included**
Statement: Roth's theorem relative to a pseudorandom measure.
Explanation: Not in mathlib.

### 275. Theorem 9.2.7 (Relative Szemeredi theorem)
**Assessment: non-included**
Statement: Szemeredi's theorem relative to a pseudorandom measure.
Explanation: Not in mathlib.

### 276. Theorem 9.2.10 (Szemeredi's theorem in a random set)
**Assessment: non-included**
Statement: Szemeredi's theorem holds inside a sufficiently dense random set.
Explanation: Not in mathlib.

### 277. Theorem 9.3.1 (Szemeredi's theorem, counting version)
**Assessment: non-included**
Statement: Counting version of Szemeredi's theorem.
Explanation: Not in mathlib.

### 278. Theorem 9.4.3 (Dense model theorem)
**Assessment: non-included**
Statement: If a function is bounded by a pseudorandom measure, it can be modeled by a bounded function.
Explanation: Not in mathlib.

### 279. Theorem 9.4.6 (Dense model theorem)
**Assessment: non-included**
Statement: Variant of the dense model theorem.
Explanation: Not in mathlib.

### 280. Lemma 9.4.7 (Multiplicative closure)
**Assessment: non-included**
Statement: Multiplicative closure properties of norms.
Explanation: Not in mathlib in this specific combinatorial context.

### 281. Lemma 9.4.8 (Submultiplicativity of the dual cut norm)
**Assessment: non-included**
Statement: The dual cut norm is submultiplicative under certain operations.
Explanation: Not in mathlib.

### 282. Theorem 9.4.9 (Weierstrass polynomial approximation theorem)
**Assessment: included**
Statement: Any continuous function on [a,b] can be uniformly approximated by polynomials.
Explanation: Formalized in `Mathlib/Topology/ContinuousMap/Weierstrass.lean` as `polynomialFunctions_closure_eq_top`. The proof goes through Bernstein approximations.

### 283. Theorem 9.4.10 (Separating hyperplane theorem)
**Assessment: included**
Statement: Given a closed convex set K and a point p not in K, there exists a hyperplane separating them.
Explanation: The geometric Hahn-Banach theorem (which implies the separating hyperplane theorem) is formalized in `Mathlib/Analysis/LocallyConvex/Separation.lean`. The file provides multiple versions including `geometric_hahn_banach_compact_closed` and `geometric_hahn_banach_closed_point` for strict separation.

### 284. Theorem 9.5.1 (Sparse triangle counting lemma)
**Assessment: non-included**
Statement: Triangle counting lemma in the sparse setting.
Explanation: Not in mathlib.

### 285. Lemma 9.5.2 (Strong linear forms)
**Assessment: non-included**
Statement: Strong linear forms condition for the relative Roth theorem.
Explanation: Not in mathlib.

### 286. Lemma 9.5.3 (Densified triangle counting)
**Assessment: non-included**
Statement: Densified version of triangle counting.
Explanation: Not in mathlib.

### 287. Lemma 9.5.4 (Cut norm between codegrees)
**Assessment: non-included**
Statement: Cut norm bound relating codegrees.
Explanation: Not in mathlib.

### 288. Theorem 9.2.5 (restated)
**Assessment: non-included**
Statement: Restatement of the relative Roth theorem.
Explanation: Not in mathlib. Same as statement 274.

### 289. Theorem 9.6.1 (Roth's theorem, functional/counting version)
**Assessment: non-included**
Statement: Functional/counting version of Roth's theorem.
Explanation: Not in mathlib in this form.

## Summary

**Total statements:** 289 unique statements (294 entries with 5 restated/duplicates)

**Included in mathlib (25):**
- Theorem 0.2.1 (van der Waerden's theorem) -- via Hales-Jewett
- Theorem 0.2.3 / 0.3.1 / 2.4.1 (Roth's theorem, 3 occurrences counted) -- via triangle removal and corners theorem
- Theorem 1.2.4 / Corollary 1.2.6 / Theorem 5.4.1 (Turan's theorem, 3 occurrences) -- full formalization
- Theorem 2.1.9 / 2.1.20 (Szemeredi's regularity lemma, 2 occurrences) -- full formalization with equipartition
- Theorem 2.2.1 (Triangle counting lemma) -- formalized
- Theorem 2.3.1 (Triangle removal lemma) -- formalized
- Theorem 2.4.2 (Corners theorem) -- formalized
- Theorem 2.5.1 (Behrend's construction) -- formalized
- Theorem 3.1.7 (Chernoff bound) -- Chernoff/Hoeffding bounds in probability
- Theorem 3.3.14 (Gauss sum) -- Gauss sums formalized
- Theorem 4.4.6 (Borel-Cantelli lemma) -- both first and second versions
- Theorem 4.7.6 (Martingale convergence theorem) -- submartingale convergence
- Theorem 7.2.1 (Ruzsa triangle inequality) -- formalized
- Theorem 7.3.1 / 7.3.3 (Plunnecke's inequality, 2 occurrences) -- Plunnecke-Ruzsa inequality
- Theorem 7.4.1 (Ruzsa covering lemma) -- formalized
- Theorem 7.9.6 (Blichfeldt's theorem) -- formalized
- Theorem 7.9.7 (Minkowski's first theorem) -- formalized
- Theorem 9.4.9 (Weierstrass approximation) -- formalized
- Theorem 9.4.10 (Separating hyperplane theorem) -- geometric Hahn-Banach

**Non-included (264):** The vast majority of results in this textbook are specialized research-level results in extremal graph theory, additive combinatorics, graph limits, pseudorandom graph theory, and Fourier analysis on finite groups that are beyond what is currently formalized in mathlib.
