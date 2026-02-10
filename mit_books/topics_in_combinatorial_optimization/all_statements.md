# All Mathematical Statements: Topics in Combinatorial Optimization

## Statement 1
**Proposition 1.** If M is a matching and C is a vertex cover then $|M| \leq |C|$.
(Line 10)

## Statement 2
**Theorem 2 (Tutte-Berge Formula).** Let G = (V, E) be a graph. Then
$$\nu(G) = \max_{M} |M| = \min_{U \subset V} (|V| + |U| - o(G - U))/2,$$
where the maximization is over all matchings M in G.
(Line 18)

## Statement 3
**Theorem 3.** The set U = A(G) gives equality in the Tutte-Berge Formula. The set D(G) contains all vertices in odd components of G-U, and C(G) contains all vertices in even components of G-U.
(Line 38)

## Statement 4
**Theorem 4 (Berge).** M is a maximum matching if and only if G contains no M-augmenting path.
(Line 44)

## Statement 5
**Theorem 1 (Lecture 2).** A matching M is of maximum size if and only if G contains no M-augmenting path.
(Line 73)

## Statement 6
**Lemma 2 (Lecture 2).** Let M be a matching in G, and let $P = (v_0, v_1, \ldots, v_t)$ be a shortest alternating walk from X to X. Then either P is an M-augmenting path, or $v_0, v_1, \ldots, v_j$ is an M-flower for some j < t.
(Line 93)

## Statement 7
**Theorem 3 (Lecture 2).** M is a maximum size matching in G if and only if M/B is a maximum size matching in G/B.
(Line 126)

## Statement 8
**Theorem 4 (Tutte-Berge Formula, Lecture 2).** For a graph G and a set of vertices $U \subseteq V(G)$, let $c_o(G \setminus U)$ denote the number of odd components of the graph $G \setminus U$, i.e. the number of components with an odd number of vertices. Then the cardinality of a maximum size matching, $\nu(G)$, satisfies:
$$\nu(G) = \min_{U \subseteq V} \frac{1}{2} [|V| + |U| - c_o(G \setminus U)].$$
(Line 166)

## Statement 9
**Theorem 5 (Edmonds-Gallai Decomposition, Lecture 2).** Given a graph G, let D(G) := {v : there exists a maximum size matching missing v}, A(G) := N(D(G)), C(G) := V(G) \ (D(G) union A(G)). Then U = A(G) achieves the minimum on the right side of the Tutte-Berge formula, D(G) is the union of the odd components of $G \setminus A(G)$, and C(G) is the union of the even components of $G \setminus A(G)$. Moreover, every odd component of $G \setminus A(G)$ is factor-critical.
(Line 170)

## Statement 10
**Claim 6 (Lecture 2).** If there is an edge from Even to v, then there is an alternating walk of odd length from X to v, and there is an alternating path from X to v.
(Line 198)

## Statement 11
**Corollary 7 (Lecture 2).** In G there is no edge between Even and Free.
(Line 202)

## Statement 12
**Claim 8 (Lecture 2).** In $G_0$, there is no edge between two vertices in Even.
(Line 206)

## Statement 13
**Claim 9 (Lecture 2).** Even = $D(G) = \{v : \exists$ a maximum-size matching missing $v\}$.
(Line 212)

## Statement 14
**Claim 10 (Lecture 2).** Odd = A(G) = N(D(G)).
(Line 216)

## Statement 15
**Claim 11 (Lecture 2).** Free = $C(G) = V(G) \setminus (D(G) \cup A(G))$.
(Line 220)

## Statement 16
**Claim 12 (Lecture 2).** In $G_0$, every free vertex is matched to another free vertex by M, and every odd vertex is matched to an even vertex by M.
(Line 224)

## Statement 17
**Claim 13 (Lecture 2).** Every component of $G \setminus A(G)$ is a subset of either D(G) or C(G). The even-cardinality components are subsets of C(G), while the odd-cardinality components are subsets of D(G). Moreover, if M is a maximum-size matching in G, then every component H of D(G) satisfies one of the following: (1) $|X \cap H| = 1$, and $M \cap \delta(H) = \emptyset$; or (2) $X \cap H = \emptyset$, $M \cap \delta(H)$ contains exactly one edge, and this edge joins H to A(G).
(Line 228)

## Statement 18
**Claim 14 (Lecture 2).** $|M| = \frac{1}{2} [|V| + |A(G)| - c_o(G \setminus A(G))].$
(Line 266)

## Statement 19
**Theorem 1 (Petersen, Lecture 3).** Any bridgeless cubic graph has a perfect matching.
(Line 316)

## Statement 20
**Theorem 2 (Vizing, 1964, Lecture 3).** For any graph, there is an edge coloring with at most $\Delta + 1$ colors, where $\Delta := \max_{v \in V} \deg(v)$ is the maximum degree of any vertex in G.
(Line 338)

## Statement 21
**Theorem 3 (Tait, 1878, Lecture 3).** Each planar cubic bridgeless can be decomposed into 3 matchings if and only if the 4-color conjecture holds.
(Line 344)

## Statement 22
**Conjecture 1 (Fulkerson, Lecture 3).** For any bridgeless cubic graph there exist 6 perfect matchings that cover each edge exactly twice.
(Line 348)

## Statement 23
**Claim 4 (Lecture 3).** Each odd connected component of G - A(G) is factor-critical.
(Line 360)

## Statement 24
**Theorem 5 (Robbins, 1939 (implicit), Lecture 3).** G is 2-connected if and only if G has a proper ear decomposition starting from a cycle.
(Line 374)

## Statement 25
**Theorem 6 (Lecture 3).** G is factor-critical if and only if G has an odd ear decomposition starting from an odd cycle.
(Line 382)

## Statement 26
**Theorem 7 (Lecture 3).** Let G be a 2-connected factor-critical graph. Then the number of near-perfect matchings is at least |E(G)|.
(Line 398)

## Statement 27
**Theorem 1 (Edmonds, 1965, Lecture 4).** The linear description $P^2$ is in fact the Matching polytope, i.e., $\mathcal{P} = P^2$.
(Line 461)

## Statement 28
**Theorem 2 (Edmonds-Giles, 1978, Lecture 4).** If the system $\{Ax \leq b\}$ is TDI, and b is integral, then the polytope $\{Ax \leq b\}$ is integral, i.e., all vertices are integral.
(Line 479)

## Statement 29
**Theorem 3 (Lecture 4).** For P a rational polyhedron, there exists a TDI system $\{Ax \leq b\}$ such that $P = \{x : Ax \leq b\}$. Furthermore, the polytope P is integral if and only if we can take b to be integral.
(Line 514)

## Statement 30
**Theorem 1 (Lecture 5).** If $Ax \leq b$ is TDI and b is integral then $P = \{x : Ax \leq b\}$ is integral.
(Line 552)

## Statement 31
**Proposition 2 (Lecture 5).** If A is totally unimodular then for all integral vectors b, $Ax \leq b$ is integral.
(Line 566)

## Statement 32
**Proposition 3 (Lecture 5).** If A is totally unimodular, $Ax \leq b$ is total dual integral for any integral vector b.
(Line 570)

## Statement 33
**Theorem 4 (Kronecker Approximation Theorem, 1884, Lecture 5).** Ax = b has an integral solution if and only if $y^{\top}b$ is an integer whenever $y^{\top}A$ is an integral vector.
(Line 584)

## Statement 34
**Corollary 5 (Lecture 5).** $P = \{x : Ax \leq b\}$ is integral if and only if each supporting hyperplane contains an integral vector.
(Line 609)

## Statement 35
**Theorem 6 (Cunningham-Marsh, Lecture 5).** For all $w \in \mathbb{Z}^{|E|}$, there exist integral vectors y and z such that the maximum weight of any matching is equal to
$$\min \sum_{v \in V} y_v + \sum_{S \in \mathcal{P}_{odd}} \lfloor \frac{S}{2} \rfloor z_s$$
subject to $\sum_{v \in V} y_v \chi^{\delta(v)} + \sum_{S \in \mathcal{P}_{odd}} z_s \chi^{E(S)} \ge w$, $y \ge 0$, $z \ge 0$.
(Line 642)

## Statement 36
**Theorem 7 (Tutte-Berge, Lecture 5).** $\nu(G) = \min_{U \subseteq V} \frac{1}{2} (|U| + |V| - o(G - U))$.
(Line 652)

## Statement 37
**Theorem 1 (Lecture 6).** $x(E(S)) \leq \lfloor \frac{|S|}{2} \rfloor$ is necessary in the description of the matching polytope iff G[S] is factor-critical and 2-connected.
(Line 695)

## Statement 38
**Theorem 2 (Lecture 6).** $\max_{C} |C| =$ minimum number of antichains $A'_i$s which partition S.
(Line 717)

## Statement 39
**Theorem 3 (Dilworth's theorem, Lecture 6).** $\max_A |A| =$ minimum number of chains $C'_i$s which partition S.
(Line 719)

## Statement 40
**Theorem 4 (Konig's theorem, Lecture 6).** $\nu(G) = \tau(G)$ in a bipartite graph G.
(Line 742)

## Statement 41
**Theorem 5 (Lecture 6).** $\max_C w(C) (= \sum_{s \in C} w_s)$ where the maximum is taken over the chains C is equal to the minimum number of antichains which cover each s w(s) times, $\forall s \in S$.
(Line 780)

## Statement 42
**Theorem 6 (Lecture 6).** $\max_A w(A) (= \sum_{s \in A} w_s)$ where the maximum is taken over the antichains A is equal to the minimum number of chains which cover each s w(s) times, $\forall s \in S$.
(Line 782)

## Statement 43
**Theorem 1 (Gallai-Milgram, Lecture 7).** In every directed graph D, the vertices can be partitioned into $\alpha(D)$ vertex-disjoint directed paths.
(Line 821)

## Statement 44
**Theorem 2 (Bessy-Thomasse, Lecture 7).** In every strongly connected digraph D, the vertices can be covered by at most $\alpha(D)$ directed cycles.
(Line 827)

## Statement 45
**Lemma 3 (Lecture 7).** Let $\pi$ be a partitioning of the vertices of D into directed paths $P_1, P_2, \dots P_l$, $l > \alpha(D)$. Let $S(\pi)$ denote the starting vertices, and $F(\pi)$ the ending vertices of $P_1, \dots P_l$. Then there is a partitioning $\pi'$ into l-1 directed paths such that $S(\pi') \subset S(\pi)$ and $F(\pi') \subset F(\pi)$.
(Line 840)

## Statement 46
**Theorem 4 (Lecture 7).** For every strongly connected directed graph, there exists a valid cyclic ordering.
(Line 860)

## Statement 47
**Corollary 5 (Lecture 7).** For a strongly connected tournament, there is a cyclic ordering $(v_1, v_2, \dots v_n)$ such that all the edges $(v_i, v_{i+1})$ are oriented clockwise, i.e. there is a hamiltonian cycle.
(Line 871)

## Statement 48
**Theorem 1 (Bessy-Thomasse, Lecture 8).** Given a strongly connected digraph D = (V, A), and a valid ordering $\mathcal{O}$, if $\alpha_{\mathcal{O}}$ denotes the size of the largest cardinality cyclic stable set, then
$$\alpha_{\mathcal{O}} = \min \sum_{\{C_1, \dots, C_p\}} i_{\mathcal{O}}(C_i),$$
where the cycles $\{C_1, \ldots, C_p\}$ cover the vertex set V.
(Line 911)

## Statement 49
**Lemma 2 (Lecture 8).** Given a valid ordering $\mathcal{O}$, fix an enumeration, $\{v_1, \ldots, v_n\}$. Let $S \subseteq V$ be a subset of the vertices. If there are no forward paths between any two vertices of S, then S is a cyclic stable set.
(Line 931)

## Statement 50
**Theorem 1 (Lecture 10).** If G and H are 2-connected, then M(G) = M(H) if and only if H can be obtained from G via a sequence of switching operations.
(Line 1162)

## Statement 51
**Theorem 2 (Lecture 10).** If G and H are 3-connected, then M(G) = M(H) if and only if G = H.
(Line 1166)

## Statement 52
**Theorem 3 (Tutte, Lecture 10).** The dual matroid of a graphic matroid M(G) corresponding to graph G is itself a graphic matroid if and only if G is planar.
(Line 1172)

## Statement 53
**Theorem 4 (Lecture 10).** If M is representable over F, then so is $M^*$.
(Line 1178)

## Statement 54
**Theorem 5 (Lecture 10).** A matroid is binary if and only if it excludes $U_4^2$ as a minor.
(Line 1192)

## Statement 55
**Theorem 6 (Lecture 10).** A binary matroid is regular if and only if it excludes the Fano matroid $F_7$ and its dual $F_7^*$ as minors.
(Line 1202)

## Statement 56
**Theorem 7 (Lecture 10).** The ternary matroids are the matroids which exclude $U_5^2$, $U_5^{2*} = U_5^3$, $F_7$, and $F_7^*$ as minors.
(Line 1206)

## Statement 57
**Lemma 8 (Lecture 10).** Let $M = \bigvee_{i=1}^k M_i$ for matroids $M_i = (S_i, \mathcal{I}_i)$. Then for any $U \subseteq S$, $r_M(U) = \min_{T \subseteq U} (|U - T| + \sum_{i=1}^k r_{M_i}(T \cap S_i))$ where $r_M(U)$ is the rank of set U in matroid M.
(Line 1228)

## Statement 58
**Theorem 9 (Lecture 10).** The greedy algorithm finds a maximum weight independent set.
(Line 1244)

## Statement 59
**Theorem 10 (Lecture 10).** The matroid polytope of Edmonds is integral.
(Line 1246)

## Statement 60
**Theorem 1 (Matroid Intersection, Lecture 11).** $\max_{I \in \mathcal{I}_1 \cap \mathcal{I}_2} |I| = \min_{U \in S} \left( r_1(U) + r_2(S \setminus U) \right).$
(Line 1297)

## Statement 61
**Lemma 2 (Lecture 11).** Let $M = (S, \mathcal{I})$ be a matroid. If $I \in \mathcal{I}, I + x \notin \mathcal{I}$, then I + x contains a unique minimal circuit.
(Line 1365)

## Statement 62
**Lemma 3 (Basis exchange, Lecture 11).** Suppose $B_1$ and $B_2$ are two bases of a matroid $\mathcal{M}$. For any $x \in B_1 \setminus B_2$, there exists $y \in B_2 \setminus B_1$ such that $B_1 - x + y \in \mathcal{I}$ and $B_2 - y + x \in \mathcal{I}$.
(Line 1367)

## Statement 63
**Lemma 4 (Lecture 11).** Let $I, J \in \mathcal{I}$ with |I| = |J|. Then A(I) contains a matching on $I\Delta J = (I \setminus J) \cup (J \setminus I)$.
(Line 1374)

## Statement 64
**Lemma 5 (Lecture 11).** Given matroid $\mathcal{M} = (S, \mathcal{I}), I \in \mathcal{I}$, and $J \subseteq S$ with |I| = |J|, if A(I) contains a unique matching on $I\Delta J$, then $J \in \mathcal{I}$.
(Line 1384)

## Statement 65
**Theorem 1 (Matroid Intersection, Lecture 12).** Let $\mathcal{M}_1 = (S, \mathcal{I}_1)$ and $\mathcal{M}_2 = (S, \mathcal{I}_2)$ be two matroids on common ground set S with rank functions $r_1$ and $r_2$, then $\max_{I \in \mathcal{I}_1 \cap \mathcal{I}_2} |I| = \min_{U \in S} (r_1(U) + r_2(S \setminus U)).$
(Line 1416)

## Statement 66
**Theorem 2 (Lecture 12).** In any step of Algorithm MIA, if there is no path from $X_1$ to $X_2$ then I is of maximum size. Otherwise, if P is a shortest path from $X_1$ to $X_2$ then $J = I\Delta V(P)$ is an independent set in $\mathcal{I}_1$ and $\mathcal{I}_2$.
(Line 1440)

## Statement 67
**Lemma 3 (Lecture 12).** Given matroid $\mathcal{M} = (S, \mathcal{I}), I \in \mathcal{I}$, and $J \subseteq S$ with |I| = |J|, if $A_{\mathcal{M}}(I)$ contains a unique matching on $I\Delta J$, then $J \in \mathcal{I}$.
(Line 1446)

## Statement 68
**Theorem 4 (Lecture 12).** Given three matroids $\mathcal{M}_1, \mathcal{M}_2, \mathcal{M}_3$ where $\mathcal{M}_i = (S, \mathcal{I}_i)$, it is NP-hard to find the independent set I with maximum size in $\mathcal{I}_1 \cap \mathcal{I}_2 \cap \mathcal{I}_3$.
(Line 1456)

## Statement 69
**Theorem 5 (Lecture 12).** Player 2 has a winning strategy if and only if S has two disjoint bases.
(Line 1496)

## Statement 70
**Theorem 1 (Matroid Intersection Polytope TDI, Lecture 13).** The polytope $\mathcal{P}$ defined by $x(U) \leq r_1(U)$ for all $U \subseteq S$, $x(U) \leq r_2(U)$ for all $U \subseteq S$, $x \geq 0$, is totally dual integrable (TDI).
(Line 1526)

## Statement 71
**Theorem 2 (Lecture 13).** If $\mathcal{F}$ is the union of two laminar families of subsets of a set X, then the $X \times \mathcal{F}$ incidence matrix of $\mathcal{F}$, is totally unimodular.
(Line 1568)

## Statement 72
**Theorem 3 (Lecture 13).** The union matroid $M = (S, \mathcal{I})$ as given above, is indeed a matroid.
(Line 1590)

## Statement 73
**Lemma 4 (Lecture 13).** Given any matroid $M' = (S', \mathcal{I}')$, and any function (not necessarily injective) $f: S' \to S$, then $M = (S, f(\mathcal{I}'))$ is a matroid, where $f(\mathcal{I}') = \{ f(I') : I' \in \mathcal{I}' \}$.
(Line 1594)

## Statement 74
**Lemma 5 (Lecture 13).** If the rank function of $M' = (S', \mathcal{I}')$ is r', then the rank function of the matroid $M = (S, f(\mathcal{I}'))$ is given by $r(U) = \min_{T \subseteq U} (|U \setminus T| + r'(f^{-1}(T)))$.
(Line 1608)

## Statement 75
**Theorem 1 (Lecture 14).** Let I be an independent set in the union. Then $I + s \in \mathcal{I}_1 \vee ... \vee \mathcal{I}_k$ iff there exists an F - s path in D.
(Line 1646)

## Statement 76
**Claim 2 (Lecture 14).** $|I_i \cap T|$ is a maximal independent subset of T in every matroid.
(Line 1650)

## Statement 77
**Corollary 3 (Lecture 14).** The maximum size of the union of k independent sets in M is $C = \min_{U \subseteq S} [|S \setminus U| + k \cdot r(U)]$.
(Line 1662)

## Statement 78
**Corollary 4 (Matroid base covering, Lecture 14).** S can be covered by k bases iff $\forall U : k \cdot r(U) \geq |U|$.
(Line 1668)

## Statement 79
**Corollary 5 (Matroid base packing, Lecture 14).** There exist k disjoint bases in M iff $\forall U : |S \setminus U| \ge k(r(S) - r(U))$.
(Line 1672)

## Statement 80
**Theorem 6 (Nash-Williams, Lecture 14).** G can be covered by k forests iff $\forall T \subseteq V : |E(T)| \leq k(|T|-1)$.
(Line 1678)

## Statement 81
**Theorem 7 (Tutte, Nash-Williams, Lecture 14).** G contains k edge-disjoint spanning trees iff for all partitions $\rho$ of V, with $\rho = (V_1, ..., V_l)$, we have $|\delta(\rho)| \ge (l-1)k$, where $|\delta(\rho)| = \{(u, v) : u \in V_i, v \in V_j, i \ne j\}$.
(Line 1688)

## Statement 82
**Lemma 8 (Lecture 14).** The rank function is submodular: $\forall A$ and $B \subseteq S$, $r(A) + r(B) \ge r(A \cap B) + r(A \cup B)$.
(Line 1692)

## Statement 83
**Lemma 9 (Lecture 14).** If $B_1$ and $B_2$ are bases of M, and $B_1$ is partitioned into $X_1 \cup Y_1$, then there exists a partition of $B_2$ into $X_2 \cup Y_2$ such that $X_1 \cup Y_2$ and $X_2 \cup Y_1$ are bases of M.
(Line 1740)

## Statement 84
**Theorem 1 (Lovasz, Lecture 15).** Let $M = (S, \mathcal{I})$ be a linear matroid (finite or infinite), let r be the rank function, and let E be a finite set of pairs in S. Then
$$\nu(M) = \min_{F} \left[ r(F) + \sum_{i=1}^{k} \lfloor \frac{1}{2} (r(F_i) - r(F)) \rfloor \right],$$
where the minimization is carried over the set $\{F: F \subseteq F_1 \cap F_2 \dots \cap F_k; F_1, F_2, \dots F_k$ are flats; $\forall (e \in E) \exists (F_i)$ such that $e \in F_i\}$.
(Line 1821)

## Statement 85
**Proposition 2 (Lecture 15).** If $M = (S, \mathcal{I})$ is a linear matroid, then it satisfies the condition given by (3).
(Line 1876)

## Statement 86
**Claim 1 (Lecture 16).** The set J (of characteristic functions for bases of a matroid M) is a jump system.
(Line 1955)

## Statement 87
**Claim 2 (Lecture 16).** J (the set of all degree sequences of subgraphs of G) is a jump system.
(Line 1970)

## Statement 88
**Claim 3 (Lecture 16).** $J_1 + J_2$ is a jump system.
(Line 1986)

## Statement 89
**Claim 4 (Lecture 16).** The greedy algorithm for optimizing over a jump system returns the desired maximum.
(Line 2023)

## Statement 90
**Theorem 1 (Lovasz, Lecture 16).** $J_B$ is a jump system.
(Line 2077)

## Statement 91
**Theorem 2 (Lecture 16).** If $V_B^+ \cap V_B^- = \emptyset$, then we have equality in Equation (1) (the min-max relation for distance from a jump system to a box).
(Line 2087)

## Statement 92
**Theorem 3 (Robbins, 1939, Lecture 18).** G is 2-edge-connected if and only if there exists an orientation D of G that is strongly connected.
(Line 2112)

## Statement 93
**Theorem 4 (Nash-Williams, 1960, Lecture 18).** G is 2k-edge-connected if and only if there exists an orientation D of G that is k-arc-connected.
(Line 2122)

## Statement 94
**Theorem 5 (Lecture 18).** Every 2k-edge-connected graph can be constructed as follows. Start from the multigraph $G_1$ consisting of two vertices u and v, with 2k parallel edges joining u and v. Repeatedly perform one of the following operations: (1) Add a new edge. (2) "Pinch" a set S of k edges. This means to add a new vertex z and to replace each edge $xy \in S$ with the two edges xz and zy.
(Line 2126)

## Statement 95
**Theorem 6 (Nash-Williams, 1960, Lecture 18).** For any graph G, there exists an orientation D such that $\lambda_D(u,v) \geq \lfloor\lambda_G(u,v)/2\rfloor$.
(Line 2141)

## Statement 96
**Theorem 9 (Lucchesi-Younger, 1978, Lecture 18).** For every weakly-connected digraph, the minimum size of a dijoin equals the maximum number of disjoint directed cuts.
(Line 2155)

## Statement 97
**Conjecture 10 (Woodall, 1978, Lecture 18).** For every digraph, the minimum size of a directed cut equals the maximum number of disjoint dijoins.
(Line 2163)

## Statement 98
**Proposition 11 (Lecture 18).** Let D = (V, A) be a weakly-connected digraph, let B be a subset of A, and let $B' = \{ (v, u) : (u, v) \in B \}$. Then B is a dijoin if and only if the digraph $D' = (V, A \cup B')$ is strongly connected.
(Line 2167)

## Statement 99
**Corollary 12 (Lecture 18).** For planar digraphs, the minimum size of a feedback arc set equals the maximum number of disjoint directed cuts.
(Line 2183)

## Statement 100
**Theorem 19 (Edmonds-Giles, 1977, Lecture 18).** The polyhedron (1) defined by submodular flow constraints is Box-TDI. That is, for any vectors $c, d \in \mathbb{R}^A$ and any crossing submodular function f, all vertices of (1) are integral.
(Line 2218)

## Statement 101
**Corollary 20 (Lecture 18).** G is 2k-edge-connected if and only if there exists an orientation of G that is k-arc-connected.
(Line 2222)

## Statement 102
**Corollary 21 (Lecture 18).** Let D = (V, A) be a weakly-connected digraph. The minimum size of a dijoin equals the maximum number of disjoint directed cuts in D.
(Line 2248)

## Statement 103
**Theorem 1 (Edmonds-Giles, Lecture 19).** Let C be a crossing family on V, let $f: C \to \mathbb{R}$ be crossing submodular, then the polytope defined by $x(\delta^{in}(U)) - x(\delta^{out}(U)) \le f(U)$ for all $U \in \mathcal{C}$, $d_a \le x_a \le c_a$ for all $a \in A$, is totally dual integral.
(Line 2376)

## Statement 104
**Theorem 2 (Lecture 19).** Let $\mathcal{F}$ be a cross-free family on $2^V$. Let M be an $|A| \times |\mathcal{F}|$ matrix such that column f is the vector $\chi^{\delta^{in}(U)} - \chi^{\delta^{out}(U)}$. Then M is totally unimodular.
(Line 2430)

## Statement 105
**Proposition 3 (Lecture 19).** $M_2$ is a matroid.
(Line 2466)

## Statement 106
**Proposition 4 (Lecture 19).** Testing independence in $M_2$ can be performed by network flows.
(Line 2468)

## Statement 107
**Lemma 1 (Lecture 20).** Let $C \subseteq 2^A$ be a crossing family and $f: C \to \mathbf{Z}$ a crossing submodular function. Then for any $k \in \mathbf{Z}_+$, $\mathcal{B} = \{ B \subset A : |B| = k$ and $\forall H \in \mathcal{C}; |B \cap H| \le f(H) \}$ are the bases of a matroid.
(Line 2506)

## Statement 108
**Theorem 2 (Splitting off, Lecture 20).** Let G = (V + s, E) be a graph, such that the degree of s is even, and $\forall U; \emptyset \subset U \subset V \Rightarrow |\delta(U)| \ge k$. Then there are edges (s, u), (s, t) such that $G' = (V+s, E \setminus \{(s,u),(s,t)\} \cup \{(t,u)\})$ satisfies the same condition.
(Line 2522)

## Statement 109
**Lemma 3 (Lecture 20).** Every edge-minimal k-edge connected graph has a vertex of degree k.
(Line 2534)

## Statement 110
**Theorem 4 (Lecture 20).** Let $M_{2k}$ denote a multigraph of 2k parallel edges between two vertices. Any 2k-edge-connected graph can be built from $M_{2k}$ by adding edges and pinching k edges.
(Line 2538)

## Statement 111
**Lemma 5 (Lecture 20).** Given G = (V, E), there exists a set of edges F such that $(V, E \cup F)$ is k-edge-connected and F has prescribed degrees $d_F(v) = x(v)$, if and only if x(V) is even, and $\forall U; \emptyset \subset U \subset V \Rightarrow d_E(U) + x(U) \geq k$.
(Line 2551)

## Statement 112
**Theorem 6 (Lecture 20).** G can be augmented to a k-edge-connected graph by adding $\gamma$ edges, if and only if for any collection of disjoint subsets of vertices $\mathcal{P}$: $\sum_{U \in \mathcal{P}} (k - d_E(U)) \le 2\gamma$.
(Line 2560)

## Statement 113
**Theorem 1 (Lovasz splitting-off, Lecture 21).** Let $G = (V \cup \{s\}, E)$ be a graph such that $\forall \emptyset \neq U \subseteq V: d(U) \ge k$, where d(U) denotes the number of edges between U and $\bar{U}$, and $k \geq 2$. Also, assume that d(s) (the degree of the vertex s) is even. Then for every $(s,t) \in E$, there exists $(s,u) \in E$ such that the graph $G' = (V \cup s, E \setminus \{(s,t),(s,u)\} \cup \{(t,u)\})$ also satisfies the condition.
(Line 2590)

## Statement 114
**Claim 2 (Lecture 21).** If we can find a set U and vector $x \in B_f$ satisfying properties (4)--(6), then U is the set that minimizes f(U).
(Line 2670)

## Statement 115
**Claim 3 (Lecture 21).** For every total order $\prec$ on $S, b^{\prec} \in B_f$.
(Line 2684)

## Statement 116
**Lemma 4 (Lecture 21).** Given $\prec$, s, and t, express the vector $b^{\prec} + \delta(\chi^t - \chi^s)$ for some $\delta \geq 0$ as a convex combination of $b^{\prec_{s,u}}$ for $u \in (s,t]_{\prec} = \{u : s \prec u \leq t\}$, where $\prec_{s,u}$ is the total order that is obtained from $\prec$ by moving u before s.
(Line 2703)

## Statement 117
**Theorem 1 (Rothschild and Whinston, Lecture 22).** G = (V, E) is an undirected graph such that $c(e) \in \mathcal{Z}^+$ for $e \in E$. Terminals $s_1, t_1, s_2, t_2$ are in V, and demands $d_1, d_2$ are positive integers. Additionally, the Euler condition is satisfied for G. Then G has an integer two-commodity flow if and only if the cut condition is satisfied.
(Line 2837)

## Statement 118
**Theorem 2 (Lecture 22).** The maximum biflow equals the minimum bicut.
(Line 2889)

## Statement 119
**Theorem 1 (Okamura-Seymour, Lecture 23).** Consider an undirected planar graph G = (V, E) and a set of terminal pairs $R = \{(s_i, t_i) : s_i \in V, t_i \in V, i = 1, \dots, k\}$ s.t. the following conditions are satisfied: (1) The terminals are on the boundary of the outside face of G. (2) The Euler condition: $(V, E \cup R)$ is Eulerian. (3) The cut condition: $|\delta_E(S)| \leq |\delta_R(S)|, \forall S \subseteq V$. Then there exist edge disjoint paths between $s_i$ and $t_i$, $i = 1, \dots, k$.
(Line 2909)

## Statement 120
**Lemma 2 (Lecture 23).** For any edge-disjoint path problem, $d_E(S) \ge d_R(S), \forall \emptyset \ne S \subsetneq V$ if and only if $d_E(S) \ge d_R(S), \forall \emptyset \ne S \subsetneq V$ s.t. G[S] and $G[V \setminus S]$ are connected.
(Line 2921)

## Statement 121
**Lemma 3 (Lecture 23).** We can assume w.l.o.g. that G is 2-connected.
(Line 2933)

## Statement 122
**Lemma 4 (Lecture 23).** The cut condition holds for the original instance I if and only if it holds for any re-paired instance $I_x$.
(Line 3031)
