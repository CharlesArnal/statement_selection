# All Formal Statements in "High-Dimensional Statistics"

## Chapter 1: Sub-Gaussian Random Variables

1. **Proposition 1.1** (Mills inequality / Gaussian tail bound). Let X be a Gaussian random variable with mean mu and variance sigma^2. Then for any t > 0, P(X - mu > t) <= (1/sqrt(2*pi)) * exp(-t^2/(2*sigma^2)) / t.

2. **Lemma 1.3** (Sub-Gaussian tail bound). Let X ~ subG(sigma^2). Then for any t > 0, P(X > t) <= exp(-t^2/(2*sigma^2)) and P(X < -t) <= exp(-t^2/(2*sigma^2)).

3. **Lemma 1.5** (Tail bound implies MGF bound). If (1.3) holds, then for any s > 0, E[exp(sX)] <= exp(4*sigma^2*s^2).

4. **Theorem 1.6** (Sub-Gaussian vector). Let X = (X_1, ..., X_n) be a vector of independent sub-Gaussian random variables with variance proxy sigma^2. Then the random vector X is sub-Gaussian with variance proxy sigma^2.

5. **Corollary 1.7** (Sub-Gaussian linear combination). Let X_1, ..., X_n be n independent random variables with X_i ~ subG(sigma^2). Then for any a in R^n, P(sum a_i X_i > t) <= exp(-t^2/(2*sigma^2*|a|_2^2)).

6. **Lemma 1.8** (Hoeffding's lemma). Let X be a random variable with E(X) = 0 and X in [a, b] almost surely. Then for any s in R, E[exp(sX)] <= exp(s^2*(b-a)^2/8). In particular, X ~ subG((b-a)^2/4).

7. **Theorem 1.9** (Hoeffding's inequality). Let X_1, ..., X_n be n independent random variables with X_i in [a_i, b_i] a.s. Let X_bar = (1/n) sum X_i. Then for any t > 0, P(X_bar - E(X_bar) > t) <= exp(-2*n^2*t^2 / sum (b_i - a_i)^2).

8. **Lemma 1.10** (Sub-exponential moment bound). Let X be centered with P(|X| > t) <= 2*exp(-2t/lambda). Then for any k >= 1, E[|X|^k] <= lambda^k * k!.

9. **Lemma 1.12** (Square of sub-Gaussian is sub-exponential). Let X ~ subG(sigma^2). Then Z = X^2 - E[X^2] is sub-exponential: Z ~ subE(16*sigma^2).

10. **Theorem 1.13** (Bernstein's inequality). Let X_1, ..., X_n be independent with E(X_i) = 0 and X_i ~ subE(lambda). Then for any t > 0, P(X_bar > t) or P(X_bar < -t) <= exp(-n/2 * min(t^2/lambda^2, t/lambda)).

11. **Theorem 1.14** (Maximum of sub-Gaussians). Let X_1, ..., X_N be N random variables with X_i ~ subG(sigma^2). Then E[max X_i] <= sigma*sqrt(2*log(N)) and P(max X_i > t) <= N*exp(-t^2/(2*sigma^2)).

12. **Lemma 1.15** (Linear forms on polytopes). For a linear form x -> c^T x and convex polytope P, max_{x in P} c^T x = max_{x in V(P)} c^T x.

13. **Theorem 1.16** (Sub-Gaussian on polytope). Let P be a polytope with N vertices and X a random vector such that v^(i)^T X are sub-Gaussian with variance proxy sigma^2. Then E[max_{theta in P} theta^T X] <= sigma*sqrt(2*log(N)).

14. **Lemma 1.18** (Epsilon-net covering bound). Fix epsilon in (0,1). The unit Euclidean ball B_2 has an epsilon-net N with |N| <= (3/epsilon)^d.

15. **Theorem 1.19** (Sub-Gaussian random vector norm bound). Let X in R^d be a sub-Gaussian random vector with variance proxy sigma^2. Then E[max_{theta in B_2} theta^T X] <= 4*sigma*sqrt(d).

## Chapter 2: Linear Regression

16. **Proposition 2.1** (Least squares normal equations). The least squares estimator mu_hat^LS satisfies X^T mu_hat^LS = X^T Y. Moreover, theta_hat^LS = (X^T X)^dagger X^T Y.

17. **Theorem 2.2** (LS risk bound). Under the linear model with epsilon ~ subG_n(sigma^2), the LS estimator satisfies |X*theta_hat^LS - X*theta*|_2^2 / n <= 4*sigma^2*d/n + 2*sigma^2*t/n with probability 1 - delta.

18. **Theorem 2.4** (Constrained LS for l1 ball). Let K = B_1, assume theta* in B_1 and conditions of Theorem 2.2. Then the constrained LS estimator satisfies a bound involving sigma^2*log(2d)/n.

19. **Theorem 2.6** (Constrained LS for sparse vectors). Fix k <= d/2, K = B_0(k), theta* in B_0(k). Then with probability 1 - delta, the rate is of order k*log(ed/k)/n.

20. **Lemma 2.7** (Binomial coefficient bound). For any integers 1 <= k <= n, binom(n,k) <= (en/k)^k.

21. **Corollary 2.8** (Consequence of Theorem 2.6). Under assumptions of Theorem 2.6, explicit rate bound involving k*log(ed/k)/n.

22. **Theorem 2.11** (Hard thresholding). In the sub-Gaussian sequence model, the hard thresholding estimator with appropriate threshold achieves rate k*log(d)/n.

23. **Theorem 2.14** (BIC estimator). Under the linear model with sub-Gaussian noise, the BIC estimator achieves rate k*log(d)/n.

24. **Theorem 2.15** (Lasso rate). Under the linear model with sub-Gaussian noise and normalized columns, the Lasso estimator achieves rate k*log(d)/n.

25. **Proposition 2.16** (Incoherence of random matrices). Let X be a random matrix with i.i.d. Rademacher entries. Then X has incoherence k with high probability under certain conditions on n, d, k.

26. **Lemma 2.17** (Cone condition under incoherence). Fix k <= d and assume X satisfies INC(k). Then for |S| <= k and theta satisfying the cone condition, a restricted eigenvalue condition holds.

27. **Theorem 2.18** (Lasso under incoherence). Under INC(k) and sparsity, the Lasso achieves rate k*log(d)/n for both prediction and estimation.

## Chapter 3: Nonparametric Regression

28. **Theorem 3.3** (LS in general regression). Under the general regression model with sub-Gaussian noise, the LS estimator achieves rate d/n.

29. **Theorem 3.4** (BIC in general regression). Under the general regression model, the BIC estimator achieves rate d/n * log(M/d).

30. **Theorem 3.5** (Lasso in general regression). Under INC(k), the Lasso achieves rate k*log(M)/n.

31. **Theorem 3.6** (Dictionary approximation). For a dictionary normalized appropriately, approximation bounds hold.

32. **Corollary 3.7** (BIC with normalized dictionary). Under Theorem 3.4 assumptions with normalized dictionary.

33. **Theorem 3.11** (Trigonometric representation). A function f in Sobolev class W(beta, L) can be represented in the trigonometric basis with coefficient decay.

34. **Proposition 3.12** (Sobolev ellipsoid properties). Properties of Sobolev ellipsoids.

35. **Lemma 3.13** (Regular design orthogonality). For the regular design X_i = (i-1)/n, the design matrix Phi satisfies the ORT condition for M <= n-1.

36. **Lemma 3.14** (Bias bound for Sobolev functions). For f in Theta(beta, Q), beta > 1/2, the truncation bias is bounded.

37. **Theorem 3.15** (LS rate for Sobolev regression). The LS estimator with trigonometric basis achieves rate n^{-2*beta/(2*beta+1)} for Sobolev functions.

## Chapter 4: Matrix Estimation and PCA

38. **Lemma 4.2** (Sub-Gaussian matrix operator norm). Let A be a d x T random matrix with A ~ subG_{dxT}(sigma^2). Then E[||A||_op] <= C*sigma*(sqrt(d) + sqrt(T)).

39. **Theorem 4.3** (SVT estimator). The singular value thresholding estimator achieves rate rank(Theta*) * (d + T) / (d*T).

40. **Theorem 4.4** (Rank penalization estimator). The estimator by rank penalization achieves rate rank(Theta*) * (d + T) / (d*T).

41. **Theorem 4.6** (Covariance estimation). For n i.i.d. sub-Gaussian random vectors, ||hat{Sigma} - Sigma||_op is of order sigma^2 * sqrt(d/n).

42. **Theorem 4.8** (Davis-Kahan sin(theta) theorem). For the spiked covariance model, the angle between estimated and true eigenvectors is bounded by ||tilde{Sigma} - Sigma||_op / theta.

43. **Theorem 4.10** (Sparse PCA). For k-sparse eigenvectors, the k-sparse largest eigenvector of the empirical covariance achieves a bound involving k*log(d)/n.

## Chapter 5: Minimax Lower Bounds

44. **Lemma 5.3** (Neyman-Pearson). Let P_0 and P_1 be two probability measures. For any test psi, P_0(psi=1) + P_1(psi=0) >= integral min(p_0, p_1). Equality holds for the likelihood ratio test.

45. **Proposition 5.6** (KL divergence properties). (1) KL(P,Q) >= 0. (2) For product measures, KL(P,Q) = sum KL(P_i, Q_i).

46. **Lemma 5.8** (Pinsker's inequality). Let P and Q be probability measures with P << Q. Then TV(P,Q) <= sqrt(KL(P,Q)).

47. **Theorem 5.9** (Two-point testing lower bound). Under the Gaussian sequence model with two hypotheses separated by 8*alpha^2*sigma^2/n, the minimax risk is at least 1/2 - alpha.

48. **Theorem 5.10** (Fano's inequality). Let P_1, ..., P_M (M >= 2) be probability distributions with P_j << P_k. Then inf_psi max_j P_j[psi(X) != j] >= 1 - (avg KL + log 2) / log(M-1).

49. **Theorem 5.11** (Multiple testing lower bound). Under M >= 5 hypotheses with separation and KL conditions, the minimax probability of error is at least 1/2 - 2*alpha.

50. **Lemma 5.12** (Varshamov-Gilbert). For any gamma in (0, 1/2), there exist binary vectors omega_1, ..., omega_M in {0,1}^d with Hamming distance >= (1/2 - gamma)*d for j != k and M = floor(exp(gamma^2*d)).

51. **Corollary 5.13** (Minimax rate over R^d). The minimax rate of estimation over R^d in the GSM is phi(R^d) = sigma^2*d/n, attained by the LS estimator.

52. **Lemma 5.14** (Sparse Varshamov-Gilbert). For 1 <= k <= d/8, there exist k-sparse binary vectors omega_1, ..., omega_M in {0,1}^d with Hamming distance >= k/2 and log(M) >= (k/8)*log(1 + d/(2k)).

53. **Corollary 5.16** (Minimax rate over l1 ball). The minimax rate over B_1(R) in the GSM is phi(B_1(R)) = min(R^2, R*sigma*log(d)/n).
