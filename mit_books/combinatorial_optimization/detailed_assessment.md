# Detailed Assessment: Combinatorial Optimization Statements in Mathlib

## Statement 1: Claim 1 (Matching characterization)
**Status**: included
**Explanation**: The basic definition and characterization of matchings in graphs is formalized in mathlib. A matching is defined as a subgraph where every vertex in its vertex set has exactly one neighbor, which directly captures the condition that no vertex has more than one incident edge in the matching.
**Mathlib references**: `Mathlib/Combinatorics/SimpleGraph/Matching.lean` — `SimpleGraph.Subgraph.IsMatching`, defined as `∀ v, v ∈ M.verts → ∃! w, M.Adj v w`.

## Statement 2: Theorem 2 (Minkowski-Weyl)
**Status**: non-included
**Explanation**: The Minkowski-Weyl theorem (that every convex polytope is a polyhedron and vice versa) is not formalized in mathlib. Mathlib has extensive convex analysis infrastructure (convex hulls, convex sets, etc.) but does not have the polyhedral combinatorics framework needed for this theorem. There is no definition of polyhedra as intersections of half-spaces, and no formalization of the equivalence between the H-representation and V-representation of convex polytopes.
**Mathlib references**: None. Related but insufficient: `Mathlib/Analysis/Convex/Hull.lean`, `Mathlib/Analysis/Convex/Basic.lean`.

## Statement 3: Definitions (Polyhedral — full-dimensional, facet, vertex/extreme point, face)
**Status**: non-included
**Explanation**: While mathlib has the notion of extreme points (`Set.extremePoints`) in `Mathlib/Analysis/Convex/Extreme.lean`, the specific polyhedral combinatorics definitions (full-dimensional polyhedron, essential inequalities, facets of polyhedra, faces of polyhedra as subsets satisfying certain inequalities as equalities) are not formalized. The polyhedral geometry framework is missing from mathlib.
**Mathlib references**: Partially related: `Mathlib/Analysis/Convex/Extreme.lean` (extreme points in convex sets). No polyhedron-specific definitions.

## Statement 4: Euler's Formula (for polytopes)
**Status**: non-included
**Explanation**: Euler's formula for polytopes ($\sum_{i=0}^{n-1} (-1)^i f_i = 1 - (-1)^n$) is not formalized in mathlib. While Euler's totient function and Euler products exist in mathlib, the Euler characteristic formula for polytopes (or even the $V - E + F = 2$ formula for polyhedra in 3D) is not present. This would require a formalization of polytope face lattices.
**Mathlib references**: None directly relevant. `Mathlib/Data/Nat/Totient.lean` is Euler's totient, not the polytope formula.

## Statement 5: Theorem 1 (Bipartite Matching Polytope: P = M)
**Status**: non-included
**Explanation**: The theorem that for bipartite graphs the matching polytope equals the LP relaxation polytope is not formalized. This is a result from polyhedral combinatorics that requires LP theory and the concept of matching polytopes, neither of which exists in mathlib. Mathlib has matchings and bipartite graphs but not their polytope characterizations.
**Mathlib references**: None. Related: `Mathlib/Combinatorics/SimpleGraph/Matching.lean`, `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`.

## Statement 6: Observation 2 (Integrality of vertex solutions via Cramer's rule)
**Status**: non-included
**Explanation**: This observation about integrality of LP vertices using Cramer's rule is a statement in linear programming / polyhedral theory that is not formalized in mathlib. While Cramer's rule itself is available in mathlib's linear algebra, the application to LP vertex integrality is not.
**Mathlib references**: None directly. Cramer's rule is in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`.

## Statement 7: Definition 3 (Totally Unimodular Matrix)
**Status**: included
**Explanation**: The definition of a totally unimodular matrix is formalized in mathlib. `Matrix.IsTotallyUnimodular` states that every square submatrix has determinant in $\{0, 1, -1\}$, matching the textbook definition exactly.
**Mathlib references**: `Mathlib/LinearAlgebra/Matrix/Determinant/TotallyUnimodular.lean` — `Matrix.IsTotallyUnimodular`.

## Statement 8: Lemma 4 (Bipartite constraint matrix is totally unimodular)
**Status**: non-included
**Explanation**: The specific result that the vertex-edge incidence matrix of a bipartite graph is totally unimodular is not formalized in mathlib. While the definition of totally unimodular matrices exists, this specific theorem connecting bipartite graphs and total unimodularity is not present.
**Mathlib references**: None. The TU definition is in `Mathlib/LinearAlgebra/Matrix/Determinant/TotallyUnimodular.lean` but the bipartite incidence matrix result is missing.

## Statement 9: Theorem 1 (Edmonds' Perfect Matching Polytope)
**Status**: non-included
**Explanation**: Edmonds' theorem characterizing the perfect matching polytope for general graphs using odd-set constraints is not formalized. This is a deep result in polyhedral combinatorics that requires LP theory, which is absent from mathlib.
**Mathlib references**: None.

## Statement 10: Claim 2 (Convex decomposition in Edmonds' proof)
**Status**: non-included
**Explanation**: This is a technical claim within the proof of Edmonds' theorem, showing that $x$ can be written as a convex combination of perfect matchings using contracted graphs. It is not formalized in mathlib.
**Mathlib references**: None.

## Statement 11: Lemma 1 (Randomized Min Cut probability bound)
**Status**: non-included
**Explanation**: The probability analysis of Karger's randomized contraction algorithm for minimum cuts (probability at least $1/\binom{n}{2}$) is not formalized in mathlib. Mathlib has no formalization of graph cut algorithms or their probabilistic analysis.
**Mathlib references**: None.

## Statement 12: Weak Duality Theorem (LP)
**Status**: non-included
**Explanation**: The weak duality theorem for linear programs ($\max c^T x \le \min b^T y$ for primal-dual pair) is not directly formalized in mathlib as an LP duality result. While mathlib has some cone duality results and Farkas' lemma in a geometric/cone setting, the classical LP weak duality is not stated in its standard form.
**Mathlib references**: None in the LP sense. Related cone duality exists in `Mathlib/Analysis/Convex/Cone/Basic.lean`.

## Statement 13: Theorem 1 (Complementary Slackness)
**Status**: non-included
**Explanation**: The complementary slackness conditions for linear programming optimality are not formalized in mathlib. This is an LP-specific result that requires LP duality theory, which is not present in mathlib.
**Mathlib references**: None.

## Statement 14: Theorem 1 (Menger's Theorem)
**Status**: non-included
**Explanation**: Menger's theorem (the number of edge-disjoint $s$-$t$ paths equals the minimum $s$-$t$ cut size) is not formalized in mathlib. Mathlib has basic graph theory (paths, connectivity) but not the max-flow/min-cut or Menger's theorem framework.
**Mathlib references**: None.

## Statement 15: Lemma 2 (Flow bounded by cut capacity)
**Status**: non-included
**Explanation**: The fundamental lemma that the value of any flow is at most the capacity of any cut is not formalized in mathlib. Network flow theory is entirely absent from mathlib.
**Mathlib references**: None.

## Statement 16: Theorem 3 (Flow is maximum iff no augmenting paths)
**Status**: non-included
**Explanation**: The characterization of maximum flows via absence of augmenting paths is not formalized. Network flow theory and augmenting path concepts are not in mathlib.
**Mathlib references**: None.

## Statement 17: Theorem 4 (Max Flow-Min Cut)
**Status**: non-included
**Explanation**: The Max Flow-Min Cut theorem is not formalized in mathlib. This fundamental theorem of combinatorial optimization requires network flow definitions that do not exist in mathlib.
**Mathlib references**: None.

## Statement 18: Claim 1 (Augmenting path = directed path in residual graph)
**Status**: non-included
**Explanation**: The correspondence between augmenting paths and directed paths in the residual graph is not formalized. Residual graphs are not defined in mathlib.
**Mathlib references**: None.

## Statement 19: Claim 2 (Flow decomposition into paths)
**Status**: non-included
**Explanation**: The flow decomposition theorem (any flow can be decomposed into at most $m$ paths) is not formalized in mathlib.
**Mathlib references**: None.

## Statement 20: Theorem 5 (Max capacity path lower bound)
**Status**: non-included
**Explanation**: The theorem that there exists an augmenting path with capacity at least $(f^* - f)/m$ is not formalized. This is an algorithmic result about network flows.
**Mathlib references**: None.

## Statement 21: Observation (Shortest augmenting path lengths non-decreasing)
**Status**: non-included
**Explanation**: This observation about the monotonicity of shortest augmenting path lengths in the Edmonds-Karp algorithm is an algorithmic property not formalized in mathlib.
**Mathlib references**: None.

## Statement 22: Lemma 6 (Bottleneck edge bound O(n))
**Status**: non-included
**Explanation**: This bound on the number of times an edge can be the bottleneck in the shortest augmenting path algorithm is an algorithmic complexity result not formalized in mathlib.
**Mathlib references**: None.

## Statement 23: Theorem 1 (Hall's Marriage Theorem)
**Status**: included
**Explanation**: Hall's marriage theorem is fully formalized in mathlib in multiple forms: as a combinatorial result about injective functions from indexed families, and specifically for bipartite graphs (finding matchings and perfect matchings). The bipartite graph version states that a perfect matching exists iff for every subset $U$ of one side, $|N(U)| \ge |U|$.
**Mathlib references**: `Mathlib/Combinatorics/Hall/Basic.lean` — `Finset.all_card_le_biUnion_card_iff_exists_injective`; `Mathlib/Combinatorics/SimpleGraph/Hall.lean` — `SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le`, `SimpleGraph.exists_isMatching_of_forall_ncard_le`.

## Statement 24: Lemma 2 (Matching is maximum iff no augmenting paths)
**Status**: non-included
**Explanation**: The Berge lemma (a matching is maximum iff it has no augmenting paths) is not formalized in mathlib. While matchings are defined, the concept of augmenting paths for matchings is not present.
**Mathlib references**: None. Matchings defined in `Mathlib/Combinatorics/SimpleGraph/Matching.lean` but no augmenting path theory.

## Statement 25: Lemma 3 (Bipartite matching optimality via alternating forest)
**Status**: non-included
**Explanation**: The characterization of maximum matchings in bipartite graphs using alternating forests is algorithmic in nature and not formalized in mathlib.
**Mathlib references**: None.

## Statement 26: Theorem 4 (Konig's Theorem)
**Status**: non-included
**Explanation**: Konig's theorem (maximum matching size equals minimum vertex cover size in bipartite graphs) is not formalized in mathlib. While mathlib has definitions of both matchings (`Mathlib/Combinatorics/SimpleGraph/Matching.lean`) and vertex covers (`Mathlib/Combinatorics/SimpleGraph/VertexCover.lean`), the equality between them for bipartite graphs is not proven.
**Mathlib references**: Definitions exist but theorem is missing: `Mathlib/Combinatorics/SimpleGraph/Matching.lean`, `Mathlib/Combinatorics/SimpleGraph/VertexCover.lean`.

## Statement 27: Theorem 5 (Frobenius-Hall)
**Status**: included
**Explanation**: The Frobenius-Hall theorem ($A$ has a matching into $B$ iff $|X| \le |\Gamma(X)|$ for all $X \subseteq A$) is equivalent to Hall's marriage theorem, which is formalized in mathlib. The graph version is available through the bipartite matching formulation in Hall.lean.
**Mathlib references**: `Mathlib/Combinatorics/Hall/Basic.lean`, `Mathlib/Combinatorics/SimpleGraph/Hall.lean`.

## Statement 28: Theorem 6 (Bipartite matching in O(m sqrt n) time)
**Status**: non-included
**Explanation**: Algorithmic complexity results (the Hopcroft-Karp algorithm runs in $O(m\sqrt{n})$ time) are not formalized in mathlib. Mathlib is focused on mathematical theorems, not algorithm complexity analysis.
**Mathlib references**: None.

## Statement 29: Observation 7 (Shortest augmenting path length increases)
**Status**: non-included
**Explanation**: This is a key property of the Hopcroft-Karp matching algorithm. Algorithmic properties of this nature are not formalized in mathlib.
**Mathlib references**: None.

## Statement 30: Lemma 8 (Cycle Shrinking / Blossom Lemma)
**Status**: non-included
**Explanation**: The blossom shrinking lemma from Edmonds' matching algorithm (contracting a blossom preserves maximality of matching) is not formalized in mathlib. While matchings are defined, the blossom/cycle shrinking theory is absent.
**Mathlib references**: None.

## Statement 31: Lemma 9 (Edmonds' algorithm progress)
**Status**: non-included
**Explanation**: This progress lemma for Edmonds' blossom algorithm is an algorithmic result not formalized in mathlib.
**Mathlib references**: None.

## Statement 32: Theorem 10 (General matching in O(n^4) time)
**Status**: non-included
**Explanation**: The $O(n^4)$ complexity bound for the general matching algorithm is an algorithmic result not formalized in mathlib.
**Mathlib references**: None.

## Statement 33: Theorem 11 (Tutte's Theorem)
**Status**: included
**Explanation**: Tutte's theorem is fully formalized in mathlib. It states that a graph has a perfect matching if and only if for every subset of vertices $X$, the number of odd-sized connected components of $G \setminus X$ is at most $|X|$. This is stated as `SimpleGraph.tutte`.
**Mathlib references**: `Mathlib/Combinatorics/SimpleGraph/Tutte.lean` — `SimpleGraph.tutte : (∃ M : Subgraph G, M.IsPerfectMatching) ↔ ∀ u, ¬ G.IsTutteViolator u`.

## Statement 34: Lemma 1 (Farkas' Lemma)
**Status**: included
**Explanation**: Farkas' lemma is formalized in mathlib in its geometric interpretation. While the exact matrix-vector form from the textbook may not be directly stated, the geometric version (a point is either in a proper cone or separated from it by a hyperplane) is proven and is equivalent.
**Mathlib references**: `Mathlib/Analysis/Convex/Cone/Dual.lean` — `ProperCone.hyperplane_separation`, `ProperCone.hyperplane_separation_point`; `Mathlib/Analysis/Convex/Cone/InnerDual.lean` — geometric Farkas' lemma for Hilbert spaces.

## Statement 35: Theorem 2 (Weak Duality)
**Status**: non-included
**Explanation**: The weak duality theorem for linear programs in its standard LP form is not formalized in mathlib. While Farkas' lemma exists in a cone-theoretic form, the LP primal-dual framework and weak duality theorem $\operatorname{opt}(P) \le \operatorname{opt}(D)$ are not stated.
**Mathlib references**: None in LP form. Related: `Mathlib/Analysis/Convex/Cone/Basic.lean` mentions duality but not LP-specific.

## Statement 36: Corollary 3 (Duality implications)
**Status**: non-included
**Explanation**: This corollary about the relationship between primal and dual feasibility/boundedness is not formalized. LP duality theory is not present in mathlib.
**Mathlib references**: None.

## Statement 37: Theorem 4 (Strong Duality)
**Status**: non-included
**Explanation**: The strong duality theorem for linear programs ($\operatorname{opt}(P) = \operatorname{opt}(D)$ when both are bounded and feasible) is not formalized in mathlib. While cone duality results exist, the full LP strong duality theorem is absent.
**Mathlib references**: None. `Mathlib/Analysis/Convex/Cone/Basic.lean` mentions strong duality as a future goal but does not prove it for LPs.

## Statement 38: Problem 1 (Ellipsoid feasibility)
**Status**: non-included
**Explanation**: The ellipsoid algorithm for LP feasibility is not formalized in mathlib. This is an algorithmic/computational result that goes beyond pure mathematical formalization.
**Mathlib references**: None.

## Statement 39: Lemma 1 (Ellipsoid volume bound)
**Status**: non-included
**Explanation**: The technical lemma about the minimum volume ellipsoid and its volume ratio bound ($e^{-1/(2n+2)}$) is not formalized in mathlib. This is part of the ellipsoid algorithm theory which is not present in mathlib.
**Mathlib references**: None.
