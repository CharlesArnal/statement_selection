# All Mathematical Statements
## Probabilistic Methods in Combinatorics (Yufei Zhao, MIT 18.226, Fall 2022)

1. **Theorem 1.1.1** (Ramsey number lower bound; Erdos 1947). R(k,k) > 2^{k/2} for all k >= 2. A diagonal Ramsey number lower bound via the probabilistic method.

2. **Theorem 1.1.3** (Ramsey number lower bound via alteration). R(k,k) >= (1/(e*sqrt(2)) + o(1)) * k * 2^{k/2}. An improved diagonal Ramsey number lower bound using the alteration method.

3. **Theorem 1.1.4** (Ramsey number lower bound via Lovasz Local Lemma). R(k,k) >= (sqrt(2)/e + o(1)) * k * 2^{k/2}. A further improved lower bound via the LLL.

4. **Theorem 1.2.1** (Sperner's theorem). The maximum antichain in the Boolean lattice of subsets of [n] has size C(n, floor(n/2)).

5. **Theorem 1.2.3** (LYM inequality). For an antichain F of subsets of [n], sum of 1/C(n,|A|) over A in F is at most 1.

6. **Theorem 1.2.5** (Bollobas two-families theorem). If A_i are a_i-element sets and B_i are b_i-element sets with A_i cap B_j = empty iff i=j, then sum of 1/C(a_i+b_i, a_i) <= 1.

7. **Theorem 1.2.9** (Erdos-Ko-Rado 1961). If n >= 2k, then every intersecting family of k-element subsets of [n] has size at most C(n-1, k-1).

8. **Theorem 1.3.1** (Erdos 1964). m(k) >= 2^{k-1}; every k-uniform hypergraph with fewer than 2^{k-1} edges is 2-colorable.

9. **Theorem 1.3.3** (Erdos 1964). m(k) = O(k^2 * 2^k); there exists a non-2-colorable k-uniform hypergraph with O(k^2 * 2^k) edges.

10. **Theorem 1.4.2**. If n < 2^{k-1}, then K_{n,n} is k-choosable.

11. **Theorem 1.4.3**. If there exists a non-2-colorable k-uniform hypergraph with n edges, then K_{n,n} is not k-choosable.

12. **Corollary 1.4.4** (List chromatic number of complete bipartite graph). ch(K_{n,n}) = (1 + o(1)) log_2 n.

13. **Theorem 1.4.5** (Saxton and Thomason 2015). If a graph G has average degree d, then ch(G) > (1+o(1)) log_2 d.

14. **Theorem 2.1.2** (Szele 1943). There is a tournament on n vertices with at least n! * 2^{-(n-1)} Hamilton paths.

15. **Theorem 2.2.1** (Erdos 1965). Every set of n nonzero integers contains a sum-free subset of size >= n/3.

16. **Theorem 2.3.2** (Caro 1979, Wei 1981). Every graph G contains an independent set of size at least sum of 1/(d_v + 1) over all vertices v.

17. **Corollary 2.3.5**. Every n-vertex graph G contains a clique of size at least sum of 1/(n - d_v) over all vertices v.

18. **Theorem 2.3.6** (Turan's theorem 1941). The number of edges in an n-vertex K_{r+1}-free graph is at most (1 - 1/r) * n^2/2.

19. **Proposition 2.4.2** (Sampling bound for tetrahedron-free 3-graphs). Every tetrahedron-free 3-graph on n >= 4 vertices has at most (3/4)*C(n,3) edges.

20. **Lemma 2.4.3**. A 5-vertex tetrahedron-free 3-graph has at most 7 edges.

21. **Proposition 2.4.4**. Every tetrahedron-free 3-graph on n >= 4 vertices has at most (7/10)*C(n,3) edges.

22. **Theorem 2.5.1** (Unbalancing lights). For a_{ij} in {-1,1}, there exist x_i, y_j in {-1,1} such that sum a_{ij} x_i y_j >= (sqrt(2/pi) + o(1)) * n^{3/2}.

23. **Theorem 2.5.2** (Unbalancing k-uniform hypergraph colorings). For edges of K_V^{(k)} colored red/blue with all cross-edges blue, there exists S with |#red - #blue| > c_k * n^k.

24. **Lemma 2.5.3** (Polynomial lower bound via compactness). A compactness argument for polynomials of degree k with coefficient of p_1...p_k equal to 1.

25. **Theorem 2.6.2** (Crossing number inequality; ACNS 1982, Leighton 1984). If |E| >= 4|V|, then cr(G) >= c * |E|^3/|V|^2.

26. **Theorem 3.1.1** (Dominating sets). Every graph on n vertices with minimum degree delta > 1 has a dominating set of size <= ((log(delta+1)+1)/(delta+1)) * n.

27. **Theorem 3.2.3** (Heilbronn triangle problem lower bound). For every n, there exists n points in [0,1]^2 with every triangle area >= c/n^2.

28. **Theorem 3.3.1** (Markov's inequality). For X >= 0 and a > 0, P(X >= a) <= E[X]/a.

29. **Theorem 3.4.1** (Erdos 1959). For all k, l, there exists a graph with girth > l and chromatic number > k.

30. **Theorem 3.5.1** (Radhakrishnan and Srinivasan 2000). Every k-uniform hypergraph with at most c*sqrt(k/log k)*2^k edges is 2-colorable.

31. **Theorem 4.1.5** (Chebyshev's inequality). P(|X - mu| >= lambda*sigma) <= 1/lambda^2.

32. **Corollary 4.1.7** (Chebyshev bound on non-existence probability). P(X=0) <= Var(X)/(E[X])^2.

33. **Theorem 4.1.11** (Triangles in random graphs). If np -> infinity, then G(n,p) contains a triangle with probability 1 - o(1).

34. **Lemma 4.2.4** (Variance bound for few dependencies). If E[X] -> infinity and Delta* = o(E[X]), then X > 0 and X ~ E[X] whp.

35. **Theorem 4.2.10** (Threshold for containing a fixed graph; Bollobas 1981). p = n^{-1/m(H)} is a threshold for G(n,p) containing H as a subgraph, where m(H) is the maximum edge-vertex ratio of a subgraph.

36. **Theorem 4.3.5** (Monotonicity of satisfying probability). For a non-trivial monotone property F, p -> P(Omega_p in F) is strictly increasing.

37. **Lemma 4.3.7** (Multiple round exposure). P(Omega_p not in F) <= P(Omega_{p/m} not in F)^m for non-trivial monotone F.

38. **Theorem 4.3.6** (Existence of thresholds; Bollobas and Thomason 1987). Every sequence of nontrivial monotone properties has a threshold.

39. **Theorem 4.4.2** (Second moment bound for clique number). If f(n,k) -> infinity then omega(G(n,1/2)) >= k whp; if f(n,k) -> 0 then omega(G(n,1/2)) < k whp.

40. **Theorem 4.4.3** (Two-point concentration for clique number; Bollobas-Erdos 1976, Matula 1976). For each n, there exists k(n) such that omega(G(n,1/2)) in {k(n), k(n)+1} whp, with k(n) ~ 2 log_2 n.

41. **Theorem 4.5.1** (Hardy-Ramanujan 1917). The number of distinct prime divisors omega(n) satisfies omega(n) = (1+o(1)) log log n for almost all n.

42. **Theorem 4.6.1** (Erdos-Moser distinct subset sums). If S is a k-element subset of [n] with distinct subset sums, then n >= c * 2^k / sqrt(k).

43. **Theorem 4.6.4** (Harper's vertex-isoperimetric inequality on the hypercube, 1966). Every A in {0,1}^k with |A| = 2^{k-1} has |partial A| >= C(k, floor(k/2)).

44. **Theorem 4.7.1** (Weierstrass approximation theorem 1885). Every continuous f: [0,1] -> R can be uniformly approximated by polynomials (proved via Bernstein polynomials).

45. **Theorem 5.0.1** (Chernoff bound). For S_n = X_1 + ... + X_n with X_i in {-1,1} iid uniform, P(S_n >= lambda*sqrt(n)) <= e^{-lambda^2/2}.

46. **Theorem 5.1.1** (Chernoff bound for binomial). For X ~ Binomial(n,p), P(X >= (1+delta)*np) <= (e^delta/(1+delta)^{1+delta})^{np}.

47. **Theorem 5.2.1** (Discrepancy bound). For any n x n matrix with +/-1 entries, disc(A) <= c*sqrt(n*log n).

48. **Theorem 5.3.2** (Hajos conjecture counterexample). With probability 1-o(1), G(n,1/2) has no K_t-subdivision with t = ceil(10*sqrt(n)).

49. **Theorem 6.1.7** (Lovasz Local Lemma; symmetric form). If P[A_i] <= p and each A_i is independent from all but at most d others, and ep(d+1) <= 1, then P(none of A_i occur) > 0.

50. **Theorem 6.1.9** (Lovasz Local Lemma; general/asymmetric form). With appropriate x_i in [0,1), if P(A_i) <= x_i * prod_{j in N(i)} (1-x_j), then P(none of A_i) >= prod (1-x_i).

51. **Corollary 6.1.10** (LLL neighborhood bound). If P(A_i) < 1/2 and sum_{j in N(i)} P(A_j) <= 1/4 for all i, then P(none of A_i) > 0.

52. **Theorem 6.2.1** (LLL for hypergraph 2-coloring). A k-uniform hypergraph is 2-colorable if every edge intersects at most e^{-1}*2^{k-1} - 1 other edges.

53. **Corollary 6.2.2**. For k >= 9, every k-uniform k-regular hypergraph is 2-colorable.

54. **Theorem 6.2.4** (Non-uniform hypergraph 2-coloring via LLL). If every edge has size >= 3 and sum of 2^{-|f|} over intersecting edges f <= 1/8, then H is 2-colorable.

55. **Theorem 6.2.6** (LLL + compactness for infinite hypergraphs). If each edge is finite, has >= k vertices, intersects at most d others, and e*2^{-k+1}*(d+1) <= 1, then H is 2-colorable.

56. **Lemma 6.2.7** (Compactness argument). In the random variable model with finitely many choices per variable and finitely-dependent events, avoiding any finite subset implies avoiding all.

57. **Theorem 6.2.11** (Beck 1980). For every epsilon > 0, there exists k_0 and a 2-coloring of Z with no monochromatic k-AP with k >= k_0 and common difference < 2^{(1-epsilon)k}.

58. **Theorem 6.2.12** (Mani-Levitska and Pach 1986). Every k-fold nondecomposable covering of R^3 by open unit balls covers some point >= 2^{k/3} times.

59. **Theorem 6.3.1** (Independent transversal via LLL; Alon 1988). Let G have max degree Delta with partition V_1,...,V_r where |V_i| >= 2e*Delta. Then there is an independent transversal.

60. **Theorem 6.4.3** (Alon and Linial 1989). Every digraph with min out-degree delta and max in-degree Delta has a cycle of length divisible by k if k <= delta/(1 + log(1+delta*Delta)).

61. **Theorem 6.5.1** (Lopsided local lemma). Same conclusion as LLL but with weakened hypothesis: P(A_i | intersect_{j in S} bar{A_j}) <= P(A_i) for S disjoint from N(i) u {i}.

62. **Theorem 6.5.5** (Nonnegative dependence for random injections). In the random injection model, the canonical negative dependency graph is valid for the lopsided LLL.

63. **Corollary 6.5.6** (Derangement lower bound). The probability that a uniform random permutation of [n] has no fixed points is >= (1-1/n)^n.

64. **Theorem 6.6.1** (Moser and Tardos 2010). In the random variable model setup, if ep(d+1) <= 1 (symmetric LLL), there is a randomized algorithm finding an assignment avoiding all bad events in expected polynomial time.

65. **Theorem 6.6.5** (Moser 2009; algorithmic k-SAT). If every clause has >= k literals and each variable appears in <= 2^k/(8k) clauses, the formula is satisfiable and a satisfying assignment can be found in expected linear time.

66. **Theorem 7.1.1** (Harris inequality 1960). If A and B are increasing events of independent boolean random variables, then P(AB) >= P(A)*P(B).

67. **Theorem 7.1.5** (Harris inequality, functional form). If f and g are monotone increasing functions of independent random variables, then E[fg] >= E[f]*E[g].

68. **Corollary 7.1.6** (Harris for decreasing/mixed events). Decreasing events are positively correlated; an increasing and a decreasing event are negatively correlated.

69. **Theorem 7.2.2** (Triangle-free lower bound via Harris). P(G(n,p) is triangle-free) >= (1 - p^3)^{C(n,3)}.

70. **Theorem 8.1.2** (Janson inequality I). In the setup of dependent indicator sums, P(X=0) <= exp(-mu + Delta/2).

71. **Theorem 8.1.8** (Janson inequality II). If Delta >= mu, then P(X=0) <= exp(-mu^2/(2*Delta)).

72. **Theorem 8.1.10** (Triangle-free probability of G(n,p)). For p <= 0.99, the probability is exp(-Theta(n^2*p)) if p >= n^{-1/2} and exp(-Theta(n^3*p^3)) if p <= n^{-1/2}.

73. **Theorem 8.2.2** (Janson inequality III; lower tail). P(X <= mu - t) <= exp(-t^2/(2(mu+Delta))).

74. **Theorem 8.3.2** (Bollobas 1988; chromatic number of G(n,1/2)). chi(G(n,1/2)) ~ n/(2*log_2 n) with high probability.

75. **Theorem 9.1.1** (McDiarmid's inequality / bounded differences). For f of independent variables with bounded differences c, P(|Z - EZ| >= lambda) <= 2*exp(-2*lambda^2/(n*c^2)).

76. **Theorem 9.1.3** (Bounded differences inequality, general form). With coordinate-dependent bounds c_i, P(Z - EZ >= lambda) <= exp(-2*lambda^2/(c_1^2+...+c_n^2)).

77. **Theorem 9.2.7** (Azuma's inequality). For a martingale with |Z_i - Z_{i-1}| <= 1, P(Z_n - Z_0 >= lambda*sqrt(n)) <= e^{-lambda^2/2}.

78. **Theorem 9.2.8** (Azuma's inequality, general). For |Z_i - Z_{i-1}| <= c_i, P(Z_n - Z_0 >= lambda) <= exp(-lambda^2/(2*(c_1^2+...+c_n^2))).

79. **Theorem 9.2.9** (Azuma's inequality for Doob martingales). With conditional range c_i, P(Z_n - Z_0 >= lambda) <= exp(-2*lambda^2/(c_1^2+...+c_n^2)).

80. **Lemma 9.2.12** (Hoeffding's lemma). For X in an interval of length l with EX=0, E[e^X] <= e^{l^2/8}.

81. **Theorem 9.3.1** (Shamir and Spencer 1987). chi(G(n,p)) is concentrated: P(|Z-EZ| >= lambda*sqrt(n-1)) <= 2*e^{-2*lambda^2}.

82. **Theorem 9.3.4** (Shamir-Spencer; chromatic number concentration). For p >= n^{-1/2+epsilon}, chi(G(n,p)) is concentrated in an interval of width O(n/sqrt(log n)).

83. **Theorem 9.4.1** (Isoperimetric inequality in Euclidean space). Among all bodies with given volume, the ball minimizes the surface area.

84. **Theorem 9.4.3** (Harper's isoperimetric inequality on the hypercube). Among sets of given size in {0,1}^n, Hamming balls minimize the boundary.

85. **Theorem 9.4.10** (Levy's isoperimetric inequality on the sphere). For sets A on S^{n-1} with measure >= 1/2, the epsilon-neighborhood has measure >= 1 - e^{-n*epsilon^2/2}.

86. **Corollary 9.4.14** (Concentration of Lipschitz functions on the sphere). A 1-Lipschitz function on S^{n-1} satisfies P(|f - Ef| >= t) <= 2*e^{-nt^2/2}.

87. **Theorem 9.4.15** (Gaussian isoperimetric inequality). Half-spaces minimize the Gaussian boundary measure among all sets of given Gaussian measure.

88. **Theorem 9.4.22** (Johnson-Lindenstrauss lemma). For n points in R^d, there exists a map to R^k with k = O(log(n)/epsilon^2) preserving all pairwise distances up to (1+/-epsilon).

89. **Theorem 9.5.2** (Talagrand; distance to convex sets). For a convex set A in product space with P(A) >= 1/2, P(d_T(x,A) >= t) <= 2*e^{-t^2/4}.

90. **Theorem 9.5.3** (Talagrand; concentration for convex Lipschitz). For a 1-Lipschitz convex function f on [0,1]^n, P(|f-M| >= t) <= 4*e^{-t^2/4}, where M is the median.

91. **Theorem 9.5.11** (Talagrand's general inequality). For A in a product space, P(A)*P(d_T(x,A) >= t) <= e^{-t^2/4}.

92. **Theorem 9.5.14** (Talagrand; weighted certificates). A general concentration inequality using certificate structures.

93. **Theorem 9.5.17** (Eigenvalue concentration). The largest eigenvalue of a symmetric random +/-1 matrix is concentrated: concentrated around 2*sqrt(n).

94. **Theorem 9.5.21** (Talagrand; certifiable functions). For h-certifiable functions on product spaces, P(Z >= t) * P(Z <= s) <= exp(-(t-s)^2/(4ht)).

95. **Corollary 9.5.23** (LIS concentration). The longest increasing subsequence of a random permutation of [n] is concentrated around its mean.

96. **Theorem 9.6.1** (Rhee-Talagrand 1987; TSP concentration). The weight of the minimum TSP tour through n random points in [0,1]^2 is concentrated around its mean.

97. **Lemma 10.1.4** (Entropy upper bound). H(X) <= log|range(X)|, with equality iff X is uniform.

98. **Lemma 10.1.5** (Independence and entropy). For independent X,Y: H(X,Y) = H(X) + H(Y).

99. **Lemma 10.1.7** (Chain rule for entropy). H(X,Y) = H(X) + H(Y|X).

100. **Lemma 10.1.8** (Subadditivity of entropy). H(X,Y) <= H(X) + H(Y).

101. **Lemma 10.1.10** (Dropping conditioning increases entropy). H(X|Y) <= H(X).

102. **Theorem 10.1.12** (Binomial tail bound via entropy). n*h(k/n) >= log C(n,k), where h is the binary entropy function.

103. **Theorem 10.2.1** (Bregman-Minc inequality). The permanent of an n x n 0-1 matrix A satisfies perm(A) <= prod (r_i!)^{1/r_i}, where r_i are row sums.

104. **Corollary 10.2.2** (Kahn-Lovasz; perfect matchings in bipartite graphs). The number of perfect matchings in a bipartite graph with degree sequence (d_1,...,d_n) is at most prod (d_i!)^{1/d_i}.

105. **Theorem 10.2.4** (Alon; tournament Hamilton paths). The maximum number of Hamilton paths in an n-vertex tournament is at most c * n^{3/2} * (n!/2^{n-1}).

106. **Theorem 10.2.10** (Upper bound on Steiner triple systems). The number of STS(n) is at most ((1+o(1)) * n/(e^2))^{n^2/6}.

107. **Theorem 10.3.3** (Sidorenko for paths). The 3-edge path satisfies Sidorenko's conjecture: t(P_3, W) >= t(K_2, W)^3.

108. **Theorem 10.3.5** (Sidorenko for trees). Every tree satisfies Sidorenko's conjecture.

109. **Theorem 10.3.6** (Sidorenko for complete bipartite graphs). K_{a,b} satisfies Sidorenko's conjecture.

110. **Theorem 10.4.1** (Shearer's lemma, special case). H(X_1,...,X_n) <= sum H(X_i | X_{i-1}) under suitable conditions.

111. **Theorem 10.4.3** (Projection inequality / Loomis-Whitney type). |A|^{n-1} <= prod |pi_i(A)| for A in Z^n and coordinate projections pi_i.

112. **Corollary 10.4.4** (Volume from projection areas). vol(K)^{n-1} <= prod area(pi_i(K)) for a convex body K in R^n.

113. **Theorem 10.4.5** (Shearer's lemma, general form). H(X_1,...,X_n) <= sum H(X_{S_j})/k, where each index appears in at least k of the S_j.

114. **Corollary 10.4.6** (Loomis-Whitney inequality). For A in Z^n, |A|^{n-1} <= prod |pi_i(A)|.

115. **Theorem 10.4.9** (Triangle-intersecting families). If F is a family of graphs on [n] such that any G,H in F share a triangle, then |F| <= 2^{C(n,2) - 3}.

116. **Theorem 10.4.12** (Kahn-Zhao; independent sets in regular graphs). The number of independent sets in a d-regular bipartite graph on 2n vertices is at most (2^{d+1}-1)^{n/d}.

117. **Theorem 10.4.14** (Galvin-Tetali). For a d-regular bipartite graph G and any graph H, hom(G,H) <= hom(K_{d,d}, H)^{n/(2d)}.

118. **Theorem 10.4.15** (Sah-Sawhney-Stoner-Zhao; proper colorings of regular bipartite graphs). The number of proper q-colorings of a d-regular bipartite graph on 2n vertices is at most (q(q-1)^d * prod_{j=2}^{d}(q-j))^{n/d}.

119. **Theorem 11.0.2** (Erdos-Kleitman-Rothschild 1976). The number of n-vertex triangle-free graphs is 2^{(1+o(1))*n^2/4}. Almost all triangle-free graphs are bipartite.

120. **Theorem 11.1.1** (Containers for triangle-free graphs). There exists a collection C of O(2^{epsilon*n^2}) graphs, each with at most (1/4+epsilon)*n^2 edges, such that every triangle-free graph is a subgraph of some element of C.

121. **Theorem 11.1.2** (Erdos-Stone-Simonovits). The maximum number of edges in an n-vertex H-free graph is (1 - 1/(chi(H)-1) + o(1)) * C(n,2).

122. **Theorem 11.1.3** (H-free graph count). The number of n-vertex H-free graphs is 2^{(1+o(1)) * ex(n,H)}.

123. **Theorem 11.2.1** (Graph container theorem). For every epsilon > 0 and tau > 0, every independent set in the triangle-free hypergraph has a container with at most (1/4+epsilon)*n^2 edges, obtained via a fingerprint of size O(n^{2-tau}).

124. **Theorem 11.2.3** (Graph container with fingerprints). A refined version of graph containers with explicit fingerprint bounds.

125. **Theorem 11.3.1** (Hypergraph container theorem; Balogh-Morris-Samotij / Saxton-Thomason 2015). A general container theorem for hypergraphs: independent sets in uniform hypergraphs can be covered by a small collection of nearly independent containers.
