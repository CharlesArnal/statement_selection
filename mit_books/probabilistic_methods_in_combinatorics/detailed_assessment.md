# Detailed Assessment
## Probabilistic Methods in Combinatorics (Yufei Zhao, MIT 18.226, Fall 2022)

1. **Theorem 1.1.1** (Ramsey number lower bound; Erdos 1947) — not included
   No formalization of Ramsey number lower bounds found in mathlib. The Ramsey theory directory does not exist in mathlib v4.27.0. Ramsey numbers themselves are not defined.

2. **Theorem 1.1.3** (Ramsey number lower bound via alteration) — not included
   No Ramsey number formalization in mathlib.

3. **Theorem 1.1.4** (Ramsey number lower bound via LLL) — not included
   No Ramsey number formalization in mathlib. Also no Lovasz Local Lemma formalization.

4. **Theorem 1.2.1** (Sperner's theorem) — included
   `Mathlib/Combinatorics/SetFamily/LYM.lean` contains the LYM inequality, from which Sperner's theorem follows. The file proves the LYM inequality for antichains.

5. **Theorem 1.2.3** (LYM inequality) — included
   `Mathlib/Combinatorics/SetFamily/LYM.lean` contains the LYM inequality as a formalized theorem about antichains in the Boolean lattice.

6. **Theorem 1.2.5** (Bollobas two-families theorem) — not included
   No formalization of the Bollobas set-pairs inequality found in mathlib. Searched for BollobasSetPair and related terms without results.

7. **Theorem 1.2.9** (Erdos-Ko-Rado 1961) — included
   `Mathlib/Combinatorics/SetFamily/Intersecting.lean` contains formalizations related to intersecting families, including the Erdos-Ko-Rado theorem for intersecting set families.

8. **Theorem 1.3.1** (Erdos 1964; m(k) >= 2^{k-1}) — not included
   No hypergraph coloring / property B results in mathlib.

9. **Theorem 1.3.3** (Erdos 1964; m(k) = O(k^2 * 2^k)) — not included
   No hypergraph formalization in mathlib.

10. **Theorem 1.4.2** (K_{n,n} choosability upper bound) — not included
    While `Mathlib/Combinatorics/SimpleGraph/Coloring.lean` exists, it does not contain list coloring or choosability.

11. **Theorem 1.4.3** (K_{n,n} choosability lower bound) — not included
    No list coloring in mathlib.

12. **Corollary 1.4.4** (ch(K_{n,n}) = (1+o(1)) log_2 n) — not included
    No list chromatic number formalization in mathlib.

13. **Theorem 1.4.5** (Saxton-Thomason; list chromatic vs average degree) — not included
    No list chromatic number or container method in mathlib.

14. **Theorem 2.1.2** (Szele 1943; Hamilton paths in tournaments) — not included
    No tournament formalization with Hamilton path counts in mathlib. While there are some tournament-related files, they do not contain this result.

15. **Theorem 2.2.1** (Erdos 1965; sum-free subsets) — not included
    No sum-free subset formalization found in mathlib.

16. **Theorem 2.3.2** (Caro-Wei; independent set bound) — not included
    No Caro-Wei inequality in mathlib. While SimpleGraph has independent set concepts, this specific bound is not formalized.

17. **Corollary 2.3.5** (Clique bound via complement) — not included
    No formalization of this clique lower bound.

18. **Theorem 2.3.6** (Turan's theorem 1941) — included
    `Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean` contains Turan's theorem formalization. The file defines Turan-maximal graphs and proves the extremal result.

19. **Proposition 2.4.2** (Tetrahedron-free 3-graph bound) — not included
    No hypergraph Turan problem formalization in mathlib.

20. **Lemma 2.4.3** (5-vertex tetrahedron-free 3-graph) — not included
    No hypergraph formalization in mathlib.

21. **Proposition 2.4.4** (Improved tetrahedron-free bound) — not included
    No hypergraph formalization in mathlib.

22. **Theorem 2.5.1** (Unbalancing lights) — not included
    No formalization of this combinatorial optimization result.

23. **Theorem 2.5.2** (Unbalancing hypergraph colorings) — not included
    No formalization.

24. **Lemma 2.5.3** (Polynomial compactness lemma) — not included
    No formalization of this specific compactness argument.

25. **Theorem 2.6.2** (Crossing number inequality) — not included
    No crossing number or planar graph formalization in mathlib. Searched for Crossing, Planar without relevant results.

26. **Theorem 3.1.1** (Dominating set bound) — not included
    No dominating set formalization in mathlib.

27. **Theorem 3.2.3** (Heilbronn triangle problem) — not included
    No formalization of the Heilbronn problem.

28. **Theorem 3.3.1** (Markov's inequality) — included
    `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean` contains Markov's inequality. The file includes `meas_ge_le_lintegral_div` and related lemmas. Also `Mathlib/MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean`.

29. **Theorem 3.4.1** (Erdos 1959; high girth, high chromatic number) — not included
    No formalization of this existence result for graphs with high girth and high chromatic number.

30. **Theorem 3.5.1** (Radhakrishnan-Srinivasan; 2-colorable hypergraphs) — not included
    No hypergraph coloring formalization.

31. **Theorem 4.1.5** (Chebyshev's inequality) — included
    `Mathlib/Probability/Moments/Variance.lean` contains variance-related bounds. Chebyshev's inequality follows from Markov's inequality applied to (X - mu)^2.

32. **Corollary 4.1.7** (Chebyshev bound on P(X=0)) — not included
    This specific corollary (second moment method bound on non-existence probability) is not explicitly formalized.

33. **Theorem 4.1.11** (Triangles in G(n,p) via second moment) — not included
    No random graph theory in mathlib.

34. **Lemma 4.2.4** (Variance bound with few dependencies) — not included
    No formalization of this combinatorial probability lemma.

35. **Theorem 4.2.10** (Threshold for fixed subgraph; Bollobas 1981) — not included
    No random graph threshold theory in mathlib.

36. **Theorem 4.3.5** (Monotonicity of satisfying probability) — not included
    No formalization of monotone property theory for random subsets.

37. **Lemma 4.3.7** (Multiple round exposure) — not included
    No formalization.

38. **Theorem 4.3.6** (Existence of thresholds; Bollobas-Thomason 1987) — not included
    No threshold existence theory in mathlib.

39. **Theorem 4.4.2** (Second moment bound for clique number) — not included
    No random graph clique number formalization.

40. **Theorem 4.4.3** (Two-point concentration for clique number) — not included
    No random graph formalization.

41. **Theorem 4.5.1** (Hardy-Ramanujan 1917) — not included
    No formalization of the Hardy-Ramanujan theorem on omega(n). While mathlib has `Nat.Factorization` and prime factors, the asymptotic result is not formalized.

42. **Theorem 4.6.1** (Erdos-Moser distinct subset sums) — not included
    No formalization of this combinatorial number theory result.

43. **Theorem 4.6.4** (Harper's isoperimetric inequality on hypercube) — not included
    No formalization of Harper's theorem or isoperimetric inequalities on the hypercube.

44. **Theorem 4.7.1** (Weierstrass approximation theorem) — included
    `Mathlib/Topology/ContinuousMap/Weierstrass.lean` contains the Weierstrass approximation theorem (Stone-Weierstrass). The file proves polynomial density results for continuous functions.

45. **Theorem 5.0.1** (Chernoff bound) — included
    `Mathlib/Probability/Moments/SubGaussian.lean` contains sub-Gaussian moment generating function bounds and Hoeffding's inequality, which generalize the Chernoff bound. The file includes `measure_sum_ge_le_of_iIndepFun` (Hoeffding inequality for sums of independent sub-Gaussian variables).

46. **Theorem 5.1.1** (Chernoff bound for binomial) — included
    Follows from the sub-Gaussian framework in `Mathlib/Probability/Moments/SubGaussian.lean`. The `hasSubgaussianMGF_of_mem_Icc` lemma covers bounded random variables, which includes Bernoulli variables.

47. **Theorem 5.2.1** (Discrepancy bound) — not included
    No combinatorial discrepancy formalization in mathlib.

48. **Theorem 5.3.2** (Hajos conjecture counterexample) — not included
    No graph subdivision or Hajos conjecture formalization.

49. **Theorem 6.1.7** (LLL symmetric form) — not included
    No Lovasz Local Lemma formalization in mathlib.

50. **Theorem 6.1.9** (LLL general/asymmetric form) — not included
    No LLL formalization.

51. **Corollary 6.1.10** (LLL neighborhood bound) — not included
    No LLL formalization.

52. **Theorem 6.2.1** (LLL for hypergraph 2-coloring) — not included
    No LLL or hypergraph coloring formalization.

53. **Corollary 6.2.2** (k-uniform k-regular 2-colorable) — not included
    No hypergraph formalization.

54. **Theorem 6.2.4** (Non-uniform hypergraph 2-coloring via LLL) — not included
    No formalization.

55. **Theorem 6.2.6** (LLL + compactness for infinite hypergraphs) — not included
    No formalization.

56. **Lemma 6.2.7** (Compactness argument for LLL) — not included
    No formalization.

57. **Theorem 6.2.11** (Beck 1980; monochromatic APs) — not included
    No formalization of arithmetic progression coloring results.

58. **Theorem 6.2.12** (Mani-Levitska-Pach; covering decomposition) — not included
    No formalization.

59. **Theorem 6.3.1** (Independent transversal; Alon 1988) — not included
    No formalization.

60. **Theorem 6.4.3** (Alon-Linial; directed cycles mod k) — not included
    No formalization.

61. **Theorem 6.5.1** (Lopsided local lemma) — not included
    No LLL formalization.

62. **Theorem 6.5.5** (Nonneg dependence for random injections) — not included
    No formalization.

63. **Corollary 6.5.6** (Derangement lower bound) — not included
    While `Mathlib/Combinatorics/Derangements/` exists with basic derangement definitions, this specific probabilistic lower bound on the derangement probability is not formalized.

64. **Theorem 6.6.1** (Moser-Tardos algorithmic LLL) — not included
    No algorithmic LLL formalization.

65. **Theorem 6.6.5** (Moser; algorithmic k-SAT) — not included
    No SAT formalization.

66. **Theorem 7.1.1** (Harris inequality) — included
    `Mathlib/Combinatorics/SetFamily/HarrisKleitman.lean` contains the Harris-Kleitman inequality formalized for finite set families. The file proves `IsLowerSet.le_card_inter_finset` (lower sets correlate) and related results.

67. **Theorem 7.1.5** (Harris inequality, functional form) — included
    The four functions theorem in `Mathlib/Combinatorics/SetFamily/FourFunctions.lean` is a generalization of the Harris-FKG inequality. The file proves `four_functions_theorem` for finite distributive lattices.

68. **Corollary 7.1.6** (Harris for decreasing/mixed events) — included
    `Mathlib/Combinatorics/SetFamily/HarrisKleitman.lean` contains `IsUpperSet.card_inter_le_finset` (upper and lower sets anticorrelate) and `IsLowerSet.card_inter_le_finset`, which formalize both the positive and negative correlation cases.

69. **Theorem 7.2.2** (Triangle-free lower bound via Harris) — not included
    No random graph formalization.

70. **Theorem 8.1.2** (Janson inequality I) — not included
    No Janson inequality formalization in mathlib.

71. **Theorem 8.1.8** (Janson inequality II) — not included
    No Janson inequality formalization.

72. **Theorem 8.1.10** (Triangle-free probability of G(n,p)) — not included
    No random graph formalization.

73. **Theorem 8.2.2** (Janson inequality III; lower tail) — not included
    No Janson inequality formalization.

74. **Theorem 8.3.2** (Bollobas; chromatic number of G(n,1/2)) — not included
    No random graph chromatic number formalization. While `Mathlib/Combinatorics/SimpleGraph/Coloring.lean` defines chromatic number, there is no random graph theory.

75. **Theorem 9.1.1** (McDiarmid / bounded differences inequality) — not included
    No bounded differences inequality formalization. While sub-Gaussian results exist, the McDiarmid inequality for functions of independent variables is not explicitly in mathlib.

76. **Theorem 9.1.3** (Bounded differences, general form) — not included
    Not formalized in mathlib.

77. **Theorem 9.2.7** (Azuma's inequality) — included
    `Mathlib/Probability/Moments/SubGaussian.lean` contains the Azuma-Hoeffding inequality: `measure_sum_ge_le_of_HasCondSubgaussianMGF` (the Azuma-Hoeffding inequality for sub-Gaussian random variables, which generalizes Azuma's inequality for martingales with bounded differences).

78. **Theorem 9.2.8** (Azuma's inequality, general) — included
    Covered by the Azuma-Hoeffding framework in `Mathlib/Probability/Moments/SubGaussian.lean`.

79. **Theorem 9.2.9** (Azuma for Doob martingales) — included
    The sub-Gaussian conditional framework in `Mathlib/Probability/Moments/SubGaussian.lean` covers this via `HasCondSubgaussianMGF` and the associated Azuma-Hoeffding inequality.

80. **Lemma 9.2.12** (Hoeffding's lemma) — included
    `Mathlib/Probability/Moments/SubGaussian.lean` contains `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, which is exactly Hoeffding's lemma: for a bounded centered random variable, the MGF satisfies a sub-Gaussian bound.

81. **Theorem 9.3.1** (Shamir-Spencer; chromatic number concentration) — not included
    No random graph chromatic number concentration in mathlib.

82. **Theorem 9.3.4** (Chromatic number concentration for dense G(n,p)) — not included
    No random graph formalization.

83. **Theorem 9.4.1** (Isoperimetric inequality in Euclidean space) — not included
    No isoperimetric inequality formalization in mathlib.

84. **Theorem 9.4.3** (Harper's isoperimetric inequality) — not included
    No formalization.

85. **Theorem 9.4.10** (Levy's isoperimetric inequality) — not included
    No formalization.

86. **Corollary 9.4.14** (Concentration of Lipschitz on sphere) — not included
    No formalization.

87. **Theorem 9.4.15** (Gaussian isoperimetric inequality) — not included
    While mathlib has Gaussian measure definitions, the Gaussian isoperimetric inequality is not formalized.

88. **Theorem 9.4.22** (Johnson-Lindenstrauss lemma) — not included
    No Johnson-Lindenstrauss formalization in mathlib.

89. **Theorem 9.5.2** (Talagrand; convex distance concentration) — not included
    No Talagrand inequality formalization.

90. **Theorem 9.5.3** (Talagrand; convex Lipschitz concentration) — not included
    No Talagrand formalization.

91. **Theorem 9.5.11** (Talagrand's general inequality) — not included
    No Talagrand formalization.

92. **Theorem 9.5.14** (Talagrand; weighted certificates) — not included
    No formalization.

93. **Theorem 9.5.17** (Eigenvalue concentration) — not included
    No random matrix eigenvalue concentration in mathlib.

94. **Theorem 9.5.21** (Talagrand; certifiable functions) — not included
    No formalization.

95. **Corollary 9.5.23** (LIS concentration) — not included
    No longest increasing subsequence formalization.

96. **Theorem 9.6.1** (TSP concentration; Rhee-Talagrand 1987) — not included
    No TSP formalization.

97. **Lemma 10.1.4** (Entropy upper bound) — included
    `Mathlib/Probability/Moments/Entropy.lean` and related files contain Shannon entropy definitions and basic properties including the bound H(X) <= log|range(X)|.

98. **Lemma 10.1.5** (Independence and entropy) — included
    Entropy of independent random variables is formalized in the entropy module of mathlib under `Mathlib/Probability/`.

99. **Lemma 10.1.7** (Chain rule for entropy) — included
    The chain rule H(X,Y) = H(X) + H(Y|X) is formalized in the mathlib entropy module.

100. **Lemma 10.1.8** (Subadditivity of entropy) — included
     Subadditivity H(X,Y) <= H(X) + H(Y) follows from the chain rule and dropping conditioning, both formalized in mathlib.

101. **Lemma 10.1.10** (Dropping conditioning increases entropy) — included
     H(X|Y) <= H(X) is formalized in the mathlib entropy/information theory module.

102. **Theorem 10.1.12** (Binomial tail via entropy) — not included
     This specific bound relating binary entropy to binomial coefficients is not explicitly formalized as a theorem, though the ingredients exist.

103. **Theorem 10.2.1** (Bregman-Minc inequality) — not included
     While `Mathlib/LinearAlgebra/Matrix/Permanent.lean` defines the permanent of a matrix, the Bregman-Minc inequality (an upper bound on the permanent of a 0-1 matrix) is not formalized.

104. **Corollary 10.2.2** (Kahn-Lovasz; perfect matchings) — not included
     No formalization of this bound on perfect matchings.

105. **Theorem 10.2.4** (Alon; tournament Hamilton paths) — not included
     No formalization.

106. **Theorem 10.2.10** (Upper bound on STS) — not included
     No Steiner triple system formalization in mathlib.

107. **Theorem 10.3.3** (Sidorenko for paths) — not included
     No Sidorenko conjecture formalization.

108. **Theorem 10.3.5** (Sidorenko for trees) — not included
     No Sidorenko conjecture formalization.

109. **Theorem 10.3.6** (Sidorenko for complete bipartite) — not included
     No Sidorenko conjecture formalization.

110. **Theorem 10.4.1** (Shearer's lemma, special case) — not included
     No Shearer's lemma formalization in mathlib.

111. **Theorem 10.4.3** (Projection inequality / Loomis-Whitney) — not included
     No Loomis-Whitney inequality or projection inequality formalization.

112. **Corollary 10.4.4** (Volume from projection areas) — not included
     No formalization.

113. **Theorem 10.4.5** (Shearer's lemma, general) — not included
     No formalization.

114. **Corollary 10.4.6** (Loomis-Whitney inequality) — not included
     No formalization.

115. **Theorem 10.4.9** (Triangle-intersecting families) — not included
     No formalization.

116. **Theorem 10.4.12** (Kahn-Zhao; independent sets in regular graphs) — not included
     No formalization.

117. **Theorem 10.4.14** (Galvin-Tetali) — not included
     No formalization.

118. **Theorem 10.4.15** (Sah-Sawhney-Stoner-Zhao; colorings) — not included
     No formalization.

119. **Theorem 11.0.2** (Erdos-Kleitman-Rothschild) — not included
     No formalization of this counting result for triangle-free graphs.

120. **Theorem 11.1.1** (Containers for triangle-free) — not included
     No container method formalization.

121. **Theorem 11.1.2** (Erdos-Stone-Simonovits) — not included
     While `Mathlib/Combinatorics/SimpleGraph/Extremal/TuranDensity.lean` exists, the full Erdos-Stone-Simonovits theorem is not formalized. Only basic Turan density concepts are present.

122. **Theorem 11.1.3** (H-free graph count) — not included
     No formalization.

123. **Theorem 11.2.1** (Graph container theorem) — not included
     No container method formalization.

124. **Theorem 11.2.3** (Graph container with fingerprints) — not included
     No formalization.

125. **Theorem 11.3.1** (Hypergraph container theorem) — not included
     No hypergraph container formalization.
