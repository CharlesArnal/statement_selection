# All Mathematical Statements in Advanced Algorithms (MIT 6.854J)

## Lecture 1: Fibonacci Heaps

**Lemma 1** (Line 138): Consider a node x with rank (number of children) d. Let y_1, y_2, ..., y_d be those children in the order they were added to the tree. Then every child y_i has rank at least i-2.

**Lemma 2** (Line 144): Let N(d) be the smallest possible number of nodes in a subtree rooted at a node of rank d. Then N(d) >= F_{d+2}. Thus, the rank of any node in a Fibonacci heap with n elements is O(log n).

## Lecture 2: Network Flows

**Lemma 1** (Line 330): Let G be a network with source s and sink t. Then for every flow f and every s-t cut (S:S_bar), we have |f| = sum_{(v,w) in (S:S_bar)} f(v,w). In particular, this implies that |f| <= u(S:S_bar).

**Corollary 2** (Weak-Duality Lemma) (Line 368): Let G be a network with source vertex s and sink vertex t. Then max_f |f| <= min_{(S:S_bar)} u(S:S_bar).

**Theorem 3** (Duality Theorem/Maxflow Mincut Theorem) (Line 378): In a network G, the following equality holds: max_f |f| = min_{(S:S_bar)} u(S:S_bar).

**Lemma 4** (Line 404): If a residual network G_f has at least one augmenting path P, then f is not a maximum flow.

**Theorem 5** (Max-Flow Min-Cut Theorem) (Line 436): Let G be a network and f be a flow on G. Then, the following statements are equivalent: (1) f is a flow of maximal value; (2) G_f has no augmenting path; and (3) |f| = u(S:S_bar) for some s-t cut (S:S_bar).

## Lecture 3: Bipartite Matching, Flow Decomposition, Fattest Path

**Theorem 1** (Line 558): Let G = (V, E) be a bipartite graph with vertex partition V = A union B, and let G' = (V', E') be the capacitated network constructed as above. If M is a matching in G, then there is an integer-valued flow f in G' with value |f| = |M|. Conversely, if f is an integer-valued flow in G', then there is a matching M in G with cardinality |M| = |f|.

**Theorem 2** (Line 573): Any (raw) s-t flow r can be decomposed into at most m flows along either paths from s to t or cycles, where m is the number of edges in the network. More precisely, it can be decomposed into at most |{e: r(e) > 0}| <= m paths and cycles.

**Theorem 3** (Line 603): Assuming that capacities are integral and bounded by U, the optimal flow for a network can be found in O(m log(mU)) = O(m log(nU)) iterations of augmenting along the fattest path.

**Corollary 4** (Line 637): We can find a maximum flow in an integer-capacitated network with maximum capacity U in O((m + n log n)m log(nU)) time.

## Lecture 3 (continued): Minimum Cost Circulation

**Proposition 5** (Line 670): The reduced cost function c_p satisfies the following properties: (i) Skew-Symmetry: c_p(v,w) = -c_p(w,v). (ii) Cycle Equivalence: for a cycle C, c(C) = c_p(C). (iii) Circulation Equivalence: for all circulations, c(f) = c_p(f).

**Theorem 6** (Optimality Condition) (Line 695): Let f be a circulation. The following are equivalent: (i) f is of minimum cost. (ii) There exists no negative-cost cycle in the residual graph G_f. (iii) There exists a potential function p such that for all (v,w) in E_f, c_p(v,w) >= 0.

## Lecture 4: Goldberg-Tarjan Min-Cost Circulation

**Theorem 1** (Line 809): For all circulations f, epsilon(f) = -mu(f).

**Remark 1** (Progress) (Line 825): Let f be a circulation. If we push flow along the minimum mean cost cycle Gamma in G_f and obtain circulation f' then epsilon(f) >= epsilon(f').

**Lemma 2** (Line 837): If costs are integer valued and epsilon(f) < 1/n then f is optimal.

**Lemma 3** (Line 841): Let f be a circulation and let f' be the circulation after m iterations of the algorithm. Then epsilon(f') <= (1 - 1/n) * epsilon(f).

**Corollary 4** (Line 853): If the costs are integer, then the number of iterations is at most mn log(nC).

**Theorem 5** (Line 871): Let f be a circulation and p be a potential such that f is epsilon(f)-optimal with respect to p. Then if |c_p(v,w)| >= 2n*epsilon for some edge (v,w) in E, the edge (v,w) is epsilon-fixed.

**Lemma 6** (Line 881): After O(mn log n) iterations, another edge becomes fixed.

**Corollary 7** (Line 891): The number of iterations of the Goldberg-Tarjan algorithm, even with irrational costs, is O(m^2 n log n).

## Lecture 5: Cancel-and-Tighten, Splay Trees

**Lemma 1** (Line 941): Let f be any circulation, and f' be the circulation obtained after m iterations of the Goldberg-Tarjan algorithm. Then epsilon(f') <= (1 - 1/n) * epsilon(f).

**Lemma 2** (Line 971): Let f be a circulation and f' be the circulation obtained by performing the Cancel step. Then we cancel at most m cycles, and epsilon(f') <= (1 - 1/n) * epsilon(f).

**Claim 3** (Line 998): The new potential function p'(v) = p(v) - l(v)*epsilon/n satisfies the property that f is epsilon'-optimal with respect to p' for some constant epsilon' <= (1 - 1/n)*epsilon.

## Lecture 6: Splay Trees

**Lemma 1** (Line 1169): For a splay-step operation on x that transforms the rank function r into r', the amortized cost is a_i <= 3(r'(x) - r(x)) + 1 if the parent of x is the root, and a_i <= 3(r'(x) - r(x)) otherwise.

**Lemma 2** (Line 1235): The amortized cost of the splay operation on a node x in a splay tree is O(1 + log(s(root)/s(x))).

**Theorem 3** (Line 1304): For any sequence of m operations on a splay tree containing at most n keys, the total cost is O((m+n) log n).

**Theorem 4** (Static Optimality Property) (Line 1324): Define a static binary search tree to be one that uses no rotation operations. Let m_i be the number of times element i is accessed for i = 1, ..., n. We assume m_i >= 1 for all i. Then the total cost for accessing every element i m_i times is at most a constant times the total cost of any static binary search tree.

## Lecture 7: Dynamic Trees

**Theorem 1** (Line 1392): The total running time of any sequence of m dynamic tree operations is O((m + n) log n), where n is the number of nodes.

## Lecture 8: Dynamic Trees (continued)

**Theorem 1** (Line 1686): Any m operations on a dynamic tree with n nodes run in O((m+n) log n) time.

## Lecture 9: Linear Programming

**Lemma 1** (Farkas' Lemma) (Line 1778): Exactly one of the following holds: (1) There exists x in R^n: Ax = b, x >= 0. (2) There exists y in R^m: A^T y >= 0, b^T y < 0.

**Theorem 2** (Line 1808): Exactly one of the following holds: (1) There exists x in Z^n: Ax = b. (2) There exists y in R^m: A^T y in Z^n and b^T y not in Z.

**Theorem 3** (The Projection Theorem) (Line 1828): If K is a nonempty, closed, convex set in R^m and b not in K, define p = proj_K(b). Then, for all z in K: (z - p)^T (b - p) <= 0.

**Corollary 4** (Line 1854): Exactly one of the following holds: (1) There exists x in R^n: Ax <= b. (2) There exists y in R^m: y >= 0, A^T y = 0, b^T y < 0.

**Theorem 5** (Weak Duality) (Line 1878): If the primal P is a minimization linear program with optimum value z, then it has a dual D, which is a maximization problem with optimum value w and z >= w.

**Theorem 6** (Strong Duality) (Line 1890): If P or D is feasible, then z = w.

## Lecture 10: LP Duality and Geometry

**Theorem 1** (Complementary Slackness) (Line 2037): Let x* be feasible in the primal, and (y*, s*) be feasible in the dual. Then the following are equivalent: (1) x* is optimal in the primal, and (y*, s*) is optimal in the dual; (2) For all j: x_j* > 0 implies s_j* = 0; (3) For all j: x_j* s_j* = 0; (4) sum_j x_j* s_j* = 0.

**Lemma 2** (Line 2056): For P = {x : Ax = b, x >= 0} and x in P, x is a vertex of P if and only if A_J has linearly independent columns for J = {j : x_j > 0}.

**Theorem 3** (Line 2080): Given a polyhedral set P = {x : Ax = b, x >= 0} such that rank(A) = m, and a point x in P, x is a vertex of P if and only if it is a basic feasible solution of P.

**Theorem 4** (Line 2092): Given a polyhedral set P = {x : Ax = b, x >= 0}, if min{c^Tx : x in P} is finite, and x in P, then there exists a vertex x' of P such that c^Tx' <= c^Tx.

## Lecture 11: LP Continuation, Ellipsoid Algorithm Introduction

**Theorem 1** (Line 2147): Consider the polyhedral set P = {x : Ax = b, x >= 0} where rank(A) = m. A point x is a vertex of P if and only if it is a basic feasible solution.

**Theorem 2** (Line 2163): Let P = {x : Ax = b, x >= 0}. Assume min{c^Tx : x in P} is finite. Then, for any x in P, there exists a vertex x' in P such that c^Tx' <= c^Tx.

**Claim 5** (Line 2258): LP is in NP.

**Theorem 6** (Line 2262): Let x be a vertex (or basic feasible solution) of Ax = b, x >= 0. Then x_i = p_i/q for i=1,...,n where p_i, q in N and p_i < 2^L and q < 2^L.

**Claim 7** (Line 2279): LP is in co-NP.

**Lemma 3** (Line 2210): If A' in Z^{n x n} then |det(A')| <= 2^{size(A')-n^2} - 1.

**Lemma 4** (Line 2216): L <= size(LP) <= mnL.

**Lemma 8** (Line 2307): Vol(E_{k+1})/Vol(E_k) < e^{-1/(2n+2)}.

## Lecture 12: Ellipsoid Algorithm

**Proposition 1** (Line 2389): Given E_k = E(a_k, A_k) and c_k, we can find E_{k+1} such that the half-ellipsoid containment is satisfied and Vol(E_{k+1})/Vol(E_k) < exp(-1/(2(n+1))).

**Claim 2** (Line 2395): Proposition 1 holds for the special case where E_k = E(0, I) and c_k = -e_1.

**Claim 3** (Line 2416): Proposition 1 holds when E_k = E(0, I), c_k = d and ||d|| = 1.

**Proposition 4** (Line 2527): Let P := {x : Ax <= b} and e be the vector of all ones. Assume that A has full column rank n. Then P is nonempty iff P' = {x : Ax <= b + (1/2^L)e, -2^L <= x_j <= 2^L for all j} is nonempty.

## Lecture 13: Ellipsoid Applications

**Lemma 1** (Line 2641): If there is no negative cost cycle in G then, for any s-t join J, there exists an s-t path P of no greater cost.

**Theorem 2** (Edmonds) (Line 2676): All vertices of the polytope defined by degree constraints, odd-set constraints, and box constraints are incidence vectors of perfect matchings.

**Lemma 3** (Line 2711): PSD (the set of positive semidefinite matrices) is a convex cone.

**Lemma 1** (SDP weak duality) (Line 2857): For any A, B >= 0 (positive semidefinite), we have A . B >= 0.

## Lecture 14: Interior Point Algorithms (LP)

*(No numbered theorems/lemmas beyond definitions in this lecture -- discussion of barrier programs and central paths)*

## Lecture 15: Interior Point Algorithms for Conic Programming

**Claim 1** (Line 3105): If x is optimum in BP_mu for K = R^n_+ (LP), then there exists y and s such that: (1) A^*y + s = c, (2) s - mu*x^{-1} = 0.

**Claim 2** (Line 3135): If X is optimum in BP_mu for K = PSD_p (SDP) then there exists y in R^m and S in PSD_p: (1) A^*y + S = C, (2) S - mu*X^{-1} = 0.

**Remark 1** (Line 3201): The canonical barrier functions defined in (1) and (2) are nu-logarithmically homogeneous.

**Lemma 3** (Line 3282): If d_mu(x,s) <= 1 then <x,s> <= 2*nu*mu.

**Theorem 4** (Line 3316): If d_{mu_k}(x_k, s_k) <= 0.1 and mu_{k+1} = mu_k / (1 + 0.1/sqrt(nu)) then d_{mu_{k+1}}(x_{k+1}, s_{k+1}) <= 0.1.

## Lecture 16: Approximation Algorithms

**Theorem 1** (Line 3385): The Christofides algorithm is a 3/2-approximation algorithm for the metric TSP.

**Theorem 2** (Line 3483): The LP rounding scheme is a 2-approximation algorithm for the Vertex Cover problem.

**Theorem 3** (Line 3515): The primal-dual algorithm achieves an approximation ratio of 2 for the vertex cover problem.

## Lecture 17: Facility Location

**Claim 1** (Line 3720): Let O and A be the opening-cost and assigning-cost of the (primal) solution constructed by the primal-dual algorithm. Then, 3O + A <= 3 * sum_{i in D} v_bar_i.

**Claim 2** (Line 3802): Consider a locally optimal solution v for the local search neighborhood N. Then, its opening cost O and assigning cost A satisfy: A <= A* + O* and O <= O* + 2A*.

## Lecture 18: MAX-CUT

**Lemma 1** (Line 3860): If (S:S_bar) is a local maximum for the MOVE neighborhood, then w(S:S_bar) >= (1/2)w(E) >= (1/2)OPT.

**Lemma 2** (Line 3892): The random cut algorithm gives a cut with expected weight that is >= (1/2)OPT.

**Theorem 3** (Line 4024): (Goemans-Williamson) For all w >= 0, we have that OPT/SDP >= 0.87856.

## Lecture 19: MAXCUT gamma-approximation, Sparsest Cut, Finite Metric Spaces

**Theorem 1** (Line 4115): The Goemans-Williamson algorithm is a randomized gamma-approximation algorithm for MAXCUT, where gamma = min_{-1 <= x <= 1} (2 cos^{-1}(x)) / (pi(1-x)) (approx 0.87856).

**Theorem 2** (Line 4193): beta*/alpha* = O(log k).

**Lemma 3** (Line 4221): Any finite metric space (V,d) is isometrically embeddable in l_infinity^{|V|}.

**Theorem 4** (Line 4253): alpha* = min_{l: (V,l) <= l_infinity} [sum_{e=(i,j)} u(e)l(i,j)] / [sum_{i=1}^k f_i l(s_i,t_i)], and beta* = min_{l: (V,l) <= l_1} [sum_{e=(i,j)} u(e)l(i,j)] / [sum_{i=1}^k f_i l(s_i,t_i)].

## Lecture 21: Convex Hull and Small-d LP

**Claim 1** (Line 4327): The MERGE algorithm terminates.

**Lemma 2** (Line 4329): At any time during the execution of the MERGE algorithm, the segment (a_i, b_j) intersects neither the interior of A nor the interior of B.

**Theorem 3** (Line 4403): Convex hull algorithms for n points in R^2 is as hard as sorting.

## Lecture 22: Seidel's Algorithm, Convex Hull

**Claim 1** (Line 4497): T(d,n) = O((sum_{1 <= i <= d} i^2/i!) * d! * n) = O(d! * n).

**Claim 2** (Line 4525): The expected running time of the improved algorithm is O(e^{2*sqrt(d*log(n/sqrt(d))) + O(sqrt(d)) + O(log n)}).

## Lecture 23: Voronoi Diagrams

**Lemma 1** (Line 4655): (1) A point q in R^2 is a vertex of a Voronoi Diagram iff there exists an empty circle centered at q having at least 3 points of P on its boundary. (2) Part of the bisector between p_i and p_j is an edge of the Voronoi diagram iff there exists an empty circle centered at a point q having precisely p_i and p_j (and no other point) on its boundary.

**Lemma 2** (Line 4660): For a Voronoi diagram with n points: the number of vertices is n_v <= 2n - 5, and the number of edges is n_e <= 3n - 6.

**Claim 3** (Line 4741): The only way for the beach line to change is through a site event or a circle event.
