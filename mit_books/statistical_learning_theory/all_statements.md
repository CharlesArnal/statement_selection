# All Mathematical Statements in Statistical Learning Theory Textbook

## Lecture 2: AdaBoost
1. **Theorem 2.1** (AdaBoost Training Error Bound): Let gamma_t = 1/2 - epsilon_t. Then the training error of AdaBoost satisfies (1/n) sum I(f(X_i) != Y_i) <= prod sqrt(1 - 4*gamma_t^2).

## Lecture 4: SVM Leave-One-Out
2. **Theorem 4.1** (SVM Leave-One-Out Error Bound): L.O.O.E. <= min(# support vectors, D^2/m^2) / (n+1), where D is the diameter of a ball containing all x_i and m is the margin of an optimal hyperplane.
3. **Lemma 4.1** (Support Vector Lower Bound): If x_i is a support vector and it is misclassified by leaving it out, then alpha_i^0 >= 1/D^2.

## Lecture 5: Concentration Inequalities
4. **Jensen's Inequality**: If phi is a convex function, then phi(E[Z]) <= E[phi(Z)].
5. **Chebyshev's Inequality** (Markov's Inequality for non-negative r.v.): If Z >= 0, then P(Z >= t) <= E[Z]/t.
6. **Markov's Inequality** (Exponential form): For any lambda > 0, P(Z >= t) <= inf_{lambda > 0} e^{-lambda t} E[e^{lambda Z}].
7. **Theorem 5.1** (Bennett's Inequality): Assume E[Z] = 0, E[Z^2] = sigma^2, |Z| < M, Z_1,...,Z_n independent copies of Z, and t >= 0. Then P(sum Z_i >= t) <= exp(-n*sigma^2/M^2 * phi(tM/(n*sigma^2))), where phi(x) = (1+x)log(1+x) - x.

## Lecture 6: Bernstein's Inequality
8. **Bernstein's Inequality**: P(sum X_i >= t) <= exp(-t^2 / (2*n*sigma^2 + (2/3)*t*M)).

## Lecture 7: Hoeffding's Inequality
9. **Theorem 7.1** (Hoeffding's Inequality for Rademacher sums): For t >= 0, P(sum epsilon_i a_i >= t) <= exp(-t^2 / (2 sum a_i^2)).
10. **Theorem 7.2** (Hoeffding-Chernoff Inequality): Assume 0 <= X_i <= 1 and mu = E[X]. Then P(sum X_i - mu >= t) <= e^{-n D(mu+t, mu)}, where D(p,q) = p log(p/q) + (1-p) log((1-p)/(1-q)).

## Lecture 8: VC Dimension and Sauer's Lemma
11. **Definition 8.1** (VC class and VC dimension): If V < infinity, then C is called a VC class. V is called VC dimension of C.
12. **Lemma 8.1** (Sauer's Lemma): For all {x_1,...,x_n}, Delta_n(C, x_1,...,x_n) <= (en/V)^V for n >= V.
13. **Lemma 8.2**: The number of subsets picked out by C is bounded by the number of subsets shattered by C.
14. **Corollary 8.1**: If V < infinity, then Delta_n(C) <= sum_{i=0}^V C(n,i) <= (en/V)^V.

## Lecture 9: VC Dimension Examples
15. **Theorem 9.1** (VC dimension of linear classifiers): VC(C) <= d for C = {{x : sum alpha_k f_k(x) > 0}}.
16. **Lemma 9.1** (Closure properties of VC classes): If C and D are VC classes of sets, then (1) C^c is VC, (2) C intersect D is VC, (3) C union D is VC.

## Lecture 10: Symmetrization and VC Inequality
17. **Lemma 10.1** (Symmetrization Lemma): If t >= sqrt(2/n), then P(sup_C |P_n(C) - P(C)| >= t) <= 2 P(sup_C |P_n(C) - P_n'(C)| >= t/2).
18. **Theorem 10.1** (Pessimistic VC Inequality): If VC(C) = V, then P(sup_C |P_n(C) - P(C)| >= t) <= 4(2en/V)^V e^{-nt^2/8}.

## Lecture 11: Optimistic VC Inequality
19. **Theorem 11.1** (Optimistic VC Inequality): P(sup_C (P(C) - P_n(C))/sqrt(P(C)) >= t) <= 4(2en/V)^V e^{-nt^2/4}.

## Lecture 12: VC-subgraph Classes, Packing and Covering Numbers
20. **Definition 12.1** (VC-subgraph class): If C is a VC class of sets, then F is VC-subgraph class of functions.
21. **Definition 12.2** (epsilon-separated set): f_1,...,f_N are epsilon-separated if d(f_i, f_j) > epsilon for any i != j.
22. **Definition 12.3** (epsilon-packing number): D(F, epsilon, d) is the maximal cardinality of an epsilon-separated set.
23. **Definition 12.4** (epsilon-cover): f_1,...,f_N is an epsilon-cover of F if for any f in F, there exists f_i such that d(f, f_i) <= epsilon.
24. **Definition 12.5** (epsilon-covering number): N(F, epsilon, d) is the minimal cardinality of an epsilon-cover of F.
25. **Lemma 12.1** (Packing-Covering Number Relationship): D(F, 2*epsilon, d) <= N(F, epsilon, d) <= D(F, epsilon, d).
26. **Definition 12.6** (Metric entropy): log N(F, epsilon, d) is called metric entropy.

## Lecture 13: Packing Number Bound for VC-subgraph Classes
27. **Theorem 13.1** (Packing Number Bound for VC-subgraph Classes): Assume F is a VC-subgraph class and VC(F) = V. Suppose -1 <= f(x) <= 1. Then D(F, epsilon, d) <= (8e/epsilon * log(7/epsilon))^V.

## Lecture 14: Dudley's Entropy Integral (Chaining)
28. **Theorem 14.1** (Dudley's Entropy Integral Bound): P(forall f in F, R(f) <= (2^{9/2}/sqrt(n)) int_0^{d(0,f)} log^{1/2} D(F, epsilon, d) d_epsilon + 2^{7/2} d(0,f) sqrt(u/n)) >= 1 - e^{-u}.

## Lecture 15: Symmetrization Lemmas
29. **Lemma 15.1** (Comparison Lemma): If P(nu >= t) <= Gamma e^{-gamma t} and E[phi(xi)] <= E[phi(nu)] for phi(x) = (x-a)_+, then P(xi > t) < Gamma * e * e^{-gamma t}.
30. **Lemma 15.2** (Averaging Lemma): If P(phi_1 >= phi_2 + sqrt(phi_3 * t)) <= Gamma e^{-gamma t}, then P(E_{x'} phi_1 >= E_{x'} phi_2 + sqrt(E_{x'} phi_3 * t)) <= Gamma * e * e^{-gamma t}.

## Lecture 16: Uniform Entropy and Generalized VC Inequality
31. **Definition 16.1** (Uniform Entropy Condition): F satisfies uniform entropy condition if for all n, for all (x_1,...,x_n), D(F, epsilon, d_x) <= D(F, epsilon).
32. **Lemma 16.1**: If F satisfies uniform entropy condition, then E_{x'} int_0^{d(0,f)} log^{1/2} D(F, epsilon, d) d_epsilon <= int_0^{sqrt(E_{x'} d(0,f)^2)} log^{1/2} D(F, epsilon/2) d_epsilon.
33. **Lemma 16.2**: If F = {f : X -> [0,1]}, then E_{x'} d(0,f)^2 <= 2 max(Ef, (1/n) sum f(x_i)).
34. **Theorem 16.1** (Generalized VC Inequality): If F satisfies Uniform Entropy Condition and F = {f : X -> [0,1]}, then P(forall f, Ef - (1/n) sum f(x_i) <= ...) >= 1 - e^{-t}.

## Lecture 17: Entropy of Convex Hulls
35. **Theorem 17.1** (Entropy of Convex Hulls): If log D(H, epsilon, d_x) <= KV log(2/epsilon), then log D(conv_d H, epsilon, d_x) <= KVd log(2/epsilon).

## Lecture 18-19: Margin Bounds for Voting Classifiers
36. **Lemma 18.1 / 19.1** (Margin Bound for Voting Classifiers): Let F_d = conv_d H. Then P(forall f in F_d, (E[phi_delta] - bar{phi_delta})/sqrt(E[phi_delta]) <= K(sqrt(dV log(n/delta)/n) + sqrt(t/n))) >= 1 - e^{-t}.

## Lecture 20: Boosting Bound
37. **Theorem 20.1** (Boosting Generalization Bound): With probability at least 1 - e^{-t}, for any T >= 1 and any f = sum lambda_i h_i, P(yf(x) <= 0) <= inf_{delta in (0,1)} (epsilon + sqrt(P_n(yf(x) <= delta) + epsilon^2))^2.

## Lecture 21: Margin-Sparsity Bound
38. **Theorem 21.1** (Margin-Sparsity Bound): For lambda_1 >= ... >= lambda_T >= 0, with probability at least 1 - e^{-t}, P(yf(x) <= 0) <= inf_{delta in (0,1)} (epsilon + sqrt(P_n(yf(x) <= delta) + epsilon^2))^2, where epsilon depends on effective dimension e(f, delta).

## Lecture 22: McDiarmid's Inequality
39. **Lemma 22.1**: For any lambda in R, E_{x_i} e^{lambda Z_i} <= e^{lambda^2 c_i^2/2}.
40. **Theorem 22.1** (McDiarmid's Inequality / Bounded Differences Inequality): If |Z(x_1,...,x_i',...,x_n) - Z(x_1,...,x_i,...,x_n)| <= c_i, then P(Z - E[Z] > t) <= e^{-t^2/(2 sum c_i^2)}.

## Lecture 23: Rademacher Complexity and Contraction Inequality
41. **Theorem 23.1** (Rademacher Complexity Bound): If -1 <= f <= 1, then P(Z(x) <= 2 E[R(x)] + 2 sqrt(2t/n)) >= 1 - e^{-t}.
42. **Theorem 23.2** (Comparison Inequality for Rademacher Processes / Contraction Inequality): E_epsilon G(sup_{f in F} sum epsilon_i phi_i(f_i)) <= E_epsilon G(sup_{f in F} sum epsilon_i f_i), where phi_i are contractions and G is convex non-decreasing.
43. **Lemma 23.1**: |x| = (x)^+ + (-x)^+.

## Lecture 24: Neural Network Bounds
44. **Theorem 24.1** (Neural Network Rademacher Complexity Bound): E sup_{h in H_k(A_1,...,A_k)} |(1/n) sum epsilon_i L(y_i, h(x_i))| <= 8 prod_{j=1}^k (2L*A_j) * E sup_{h in H} |(1/n) sum epsilon_i h(x_i)| + 8/sqrt(n).

## Lecture 26: Talagrand's Convex Distance Inequality
45. **Lemma 26.1**: For 0 <= r <= 1, inf_{0 <= lambda <= 1} e^{(1/4)(1-lambda)^2} r^{-lambda} <= 2 - r.
46. **Definition 26.1** (Convex hull distance): Defines V(A,x), U(A,x), and d(A,x).
47. **Theorem 26.1** (Talagrand's Convex Distance Inequality): E[e^{d(A,x)/4}] <= 1/P^n(A) and P^n(d(A,x) >= t) <= (1/P^n(A)) e^{-t/4}.

## Lecture 27: Concentration for Convex Lipschitz Functions
48. **Theorem 27.1** (Concentration for Convex Lipschitz Functions on Binary Cube): P(f(x_1,...,x_n) >= M + L sqrt(t)) <= 2 e^{-t/4} and P(f(x_1,...,x_n) <= M - L sqrt(t)) <= 2 e^{-t/4}, where M is the median.
49. **Theorem 27.2** (Concentration for Suprema of Linear Forms): Applied version of Theorem 27.1 for f(x) = sup_{h in H} |sum h_i x_i|.

## Lecture 28: Bousquet's Inequality
50. **Theorem 28.1** (Bousquet's Inequality): P(Z(x) >= E[Z(x)] + 2 sqrt(V(x) t)) <= 4e * e^{-t/4}.
51. **Lemma 28.1** (Symmetrization for Random Variance): If P(xi_1 >= xi_2 + sqrt(xi_3 t)) <= Gamma e^{-gamma t}, then P(xi_1' >= xi_2' + sqrt(xi_3' t)) <= Gamma e * e^{-gamma t}.

## Lecture 29: Control by Two Points
52. **Definition 29.1** (Two-point distance): d(A_1, A_2, x) = inf{card{i: x_i != y_i^1 and x_i != y_i^2}, y^1 in A_1, y^2 in A_2}.
53. **Theorem 29.1** (Control by Two Points): E[2^{d(A_1, A_2, x)}] <= 1/(P^n(A_1) P^n(A_2)).
54. **Lemma 29.1**: For 0 <= g_1, g_2 <= 1, integral min(2, 1/g_1, 1/g_2) dP * integral g_1 dP * integral g_2 dP <= 1.

## Lecture 30: Talagrand's Concentration for Empirical Processes
55. **Lemma 30.1** (Variance Concentration): P(V <= 4 E[V] + (b-a)^2 t) >= 1 - 4 * 2^{-t}.
56. **Lemma 30.2** (Variance-Expectation Bound): E[V] <= 8(b-a) E[Z] + 2n sigma^2.
57. **Corollary 30.1** (Talagrand's Concentration for Empirical Processes): P(Z <= E[Z] + 4 sqrt((8(b-a) E[Z] + 2n sigma^2) t) + 2(b-a)t) >= 1 - (4e) e^{-t/4} - 4 * 2^{-t}.
58. **Theorem 30.1** (Talagrand's Concentration Inequality): Assume a <= f <= b. Let Z = sup_f |sum f(x_i)| and V = sup_f sum (f(x_i) - f(x_i'))^2. Then P(Z <= E[Z] + 4 sqrt(E[V] t) + 2(b-a)t) >= 1 - (4e) e^{-t/4} - 4 * 2^{-t}.

## Lecture 31: Localization
59. **Theorem 31.1** (Localization / Fixed-Point Bound): Let 0 <= f <= 1 for all f in F. With probability at least 1 - e^{-t}, for any f_0 in F, Ef_0 <= x*, where x* is the largest solution of x* = (1/n) sum f_0(x_i) + Phi(x*).

## Lecture 32: Equivalence Theorem and Bin Packing
60. **Theorem 32.1** (Restatement of Talagrand's Convex Distance Inequality): P(d(A,x) >= t) <= (1/P(A)) e^{-t/4}.
61. **Theorem 32.2** (Equivalence of Convex Distance Conditions): d(A,x) < t if and only if for all alpha, there exists y in A such that sum alpha_i I(x_i != y_i) <= sqrt(sum alpha_i^2 * t).
62. **Lemma 32.1** (Bin Packing Upper Bound): B(x_1,...,x_n) <= 2 sum x_i + 1.
63. **Theorem 32.3** (Bin Packing Concentration): P(B(x_1,...,x_n) <= M + 2 sqrt(sum x_i^2 * t) + 1) >= 1 - 2 e^{-t/4}.

## Lecture 34: Kernel Methods and Random VC
64. **Theorem 34.1** (Covering Number Bound for Kernel Classes, Cucker-Smale): For all h >= d, log N(F, epsilon, d) <= (C_h/epsilon)^{2d/h}.
65. **Theorem 34.2** (VC Inequality for Random Collection of Sets): P(sup_{C in C(x)} (P(C) - P_n(C))/sqrt(P(C)) >= t) <= 4 G(2n) e^{-nt^2/4}.
