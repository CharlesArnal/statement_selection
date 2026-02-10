# All Statements from Combinatorial Optimization (18.433)

## Statement 1: Claim 1
Any solution to the equations (1) $x_e \in \{0, 1\} \ \forall e \in E$ and (2) $\sum_{e \in \delta(v)} x_e \le 1 \ \forall v \in V$ is a matching.

## Statement 2: Theorem 2 (Minkowski-Weyl)
Every convex polytope is a polyhedron.

## Statement 3: Definitions (Polyhedral)
- A full-dimensional polyhedron is one that has an interior point (a point that satisfies all the half-spaces inequalities as strict inequalities rather than as equalities).
- The minimal set of half-spaces needed to describe a full-dimensional polytope are its essential inequalities. A facet is the subset of points of the polyhedron that satisfies an essential inequality as an equality.
- A vertex or extreme point of a polyhedron is any point that is not a convex combination of 2 other points in the set. It is the unique solution of n linearly independent half spaces.
- A face is a subset (of a polyhedron) of the form $\{x : x \text{ satisfies some subset of the essential inequalities as equalities}\}$. The dimension of a face is the dimension of the affine hull of the face.

## Statement 4: Euler's Formula
$$\sum_{i=0}^{n-1} (-1)^i f_i = 1 - (-1)^n$$
where $f_i$ is the number of faces of dimension $i$ of a polytope. For $n = 3$, $f_0 - f_1 + f_2 = 2$.

## Statement 5: Theorem 1 (Bipartite Matching Polytope)
If $G$ is bipartite, then $P = \mathcal{M}$, where $\mathcal{M} = conv\{x = \chi^M \mid M \text{ is a matching}\}$ and $P = \{x \mid x_e \ge 0 \ \forall e \in E, \sum_{e \in \delta(v)} x_e \le 1 \ \forall v \in V\}$.

## Statement 6: Observation 2
The vertex solution $y$ is integral if the numerator of the Cramer's rule expression is integral and $\det(A_1) = \pm 1$.

## Statement 7: Definition 3 (Totally Unimodular)
A matrix is said to be totally unimodular if every square submatrix has a determinant of 0, 1, or -1.

## Statement 8: Lemma 4
If $G$ is bipartite, then the constraint matrix (vertex-edge adjacency matrix plus negative identity) is totally unimodular.

## Statement 9: Theorem 1 (Edmonds, Perfect Matching Polytope)
$P = \{x \mid x \text{ satisfies Constraints 1, 2, and 3}\} = PM(G)$, where Constraint 1: $x_e \ge 0 \ \forall e \in E$, Constraint 2: $\sum_{e \in \delta(v)} x_e = 1 \ \forall v \in V$, Constraint 3: $\sum_{e \in \delta(S)} x_e \ge 1$ for any $S$ of odd size.

## Statement 10: Claim 2 (Edmonds Proof)
$$x = \sum_{e \in (W,\overline{W})} \sum_{M: e \in M} \left( \frac{\lambda_{M'} \alpha_{M''}}{x_e} \right) \chi^M$$
(That $x$ can be written as a convex combination of perfect matchings.)

## Statement 11: Lemma 1 (Randomized Min Cut)
Any particular minimum cut will be the output of the randomized contraction algorithm with probability at least $\frac{1}{\binom{n}{2}} \approx \frac{2}{n^2}$.

## Statement 12: Weak Duality Theorem
$$\max \{c^T x \mid Ax \le b, x \ge 0\} \le \min \{y^T b \mid A^T y \ge c, \ y \ge 0\}$$

## Statement 13: Theorem 1 (Complementary Slackness)
Suppose $x$ and $y$ are feasible solutions to (P) and (D). Then $x$ and $y$ are optimal if and only if the following conditions are satisfied: $\forall i \ (b_i - \sum_j a_{ij} x_j) y_i = 0$ and $\forall j \ (\sum_{i} a_{ij} y_i - c_j) x_j = 0$.

## Statement 14: Theorem 1 (Menger)
A graph $G=(V,E)$ has $k$ edge disjoint paths from $s$ to $t \iff k$ is the size of the minimum directed $s$-$t$ cut.

## Statement 15: Lemma 2 (Flow-Cut)
Let $(S, \bar{S})$ be any $s$-$t$ cut in the graph $G$. Then $f \leq c(S, \bar{S})$.

## Statement 16: Theorem 3 (Augmenting Path Characterization)
A flow $f$ is maximum $\iff$ there are no flow augmenting paths.

## Statement 17: Theorem 4 (Max Flow-Min Cut)
The maximum flow is equal to the minimum capacity cut.

## Statement 18: Claim 1 (Residual Graph)
An augmenting path in $G$ corresponds to a directed $s$-$t$ path in $\operatorname{Res}(G)$.

## Statement 19: Claim 2 (Flow Decomposition)
A flow $f$ can be decomposed into at most $m$ paths from $s$ to $t$, excluding cycles.

## Statement 20: Theorem 5 (Max Capacity Path)
There is a path $P$ with $c(P) \ge \frac{f^* - f}{m}$, where $f$ is the current flow value and $f^*$ is the optimal flow value.

## Statement 21: Observation (Shortest Path Non-decreasing)
The shortest path lengths are non-decreasing in the course of the shortest augmenting path algorithm.

## Statement 22: Lemma 6 (Bottleneck Edge Bound)
The total number of times an edge can be the minimum capacity edge is $O(n)$.

## Statement 23: Theorem 1 (Hall's Marriage Theorem)
A bipartite graph with sets of vertices $A$, $B$ has a perfect matching iff $|A| = |B|$ and $(\forall U \subseteq A)|N(U)| \ge |U|$.

## Statement 24: Lemma 2 (Augmenting Path Characterization for Matching)
A matching $M$ is maximum iff it has no augmenting paths.

## Statement 25: Lemma 3 (Bipartite Matching Optimality)
$M$ is maximum iff no vertex of $B^U$ is in the alternating forest $F$.

## Statement 26: Theorem 4 (Konig's Theorem)
The size of a maximum matching in a bipartite graph is equal to the size of a minimum vertex cover of the graph.

## Statement 27: Theorem 5 (Frobenius-Hall)
$A$ has a matching into $B$ iff for every subset $X$ of $A$, $|X| \leq |\Gamma(X)|$.

## Statement 28: Theorem 6 (Bipartite Matching Complexity)
A maximum matching can be found in a bipartite graph in $O(m\sqrt{n})$ time.

## Statement 29: Observation 7 (Augmenting Path Length)
The length of the shortest augmenting path increases in each phase.

## Statement 30: Lemma 8 (Cycle Shrinking / Blossom Lemma)
Let $M$ be a matching of $G$ and $B$ be a blossom. Further, assume that $B$ is vertex-disjoint from the rest of $M$. Consider the graph $G'$ obtained by contracting $B$ to a single vertex. Then the matching $M'$ of $G'$ induced by $M$ is maximum in $G'$ iff $M$ is maximum in $G$.

## Statement 31: Lemma 9 (Edmonds' Algorithm Progress)
At each step of the algorithm, we either increase the size of $F$, or decrease the size of $G$ or find an augmenting path or stop with a maximum matching.

## Statement 32: Theorem 10 (General Matching Complexity)
A maximum matching can be found in $O(n^4)$ time.

## Statement 33: Theorem 11 (Tutte's Theorem)
A graph $G$ has a perfect matching iff for any subset of vertices $X$, the number of odd-sized components of the graph $G \setminus X$ obtained by deleting $X$ from $G$ is at most $|X|$.

## Statement 34: Lemma 1 (Farkas' Lemma)
Let $A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$. Exactly one of the following conditions is true: (1) $\exists x \in \mathbb{R}^n : Ax = b$ and $x \ge 0$; (2) $\exists y \in \mathbb{R}^m : b^T y < 0$ and $A^T y \ge 0$.

## Statement 35: Theorem 2 (Weak Duality)
If (P) and (D) are feasible, then $\operatorname{opt}(P) \leq \operatorname{opt}(D)$ and finite. In particular, (P) is bounded.

## Statement 36: Corollary 3 (Duality Implications)
If (D) is feasible, then (P) is bounded or infeasible. If (P) is feasible, then (D) is bounded or infeasible.

## Statement 37: Theorem 4 (Strong Duality)
For a linear program (P) and its dual (D) there are only the following possibilities: (1) (P) BF and (D) BF, with $\operatorname{opt}(P) = \operatorname{opt}(D)$; (2) (P) I, (D) UF; (3) (P) UF, (D) I; (4) (P) I, (D) I.

## Statement 38: Problem 1 (Ellipsoid Feasibility)
Given a polyhedron $P$, written as $Ax \leq b$, find a point in $P$.

## Statement 39: Lemma 1 (Ellipsoid Volume Bound)
The minimum volume ellipsoid containing $\operatorname{Ell}(D, z) \cap \{x \mid a \cdot x \leq a \cdot z\}$ is exactly $E' = \operatorname{Ell}(D', z')$, where $z' = z - \frac{1}{n+1} \frac{Da}{\sqrt{a^T Da}}$ and $D' = \frac{n^2}{n^2 - 1} \left( D - \frac{2}{n+1} \frac{Daa^T D}{a^T Da} \right)$ and $\frac{\operatorname{vol}(E')}{\operatorname{vol}(E)} \le e^{\frac{-1}{2n+2}}$.
