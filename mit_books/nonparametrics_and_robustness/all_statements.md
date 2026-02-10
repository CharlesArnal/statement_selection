# All Mathematical Statements - Nonparametrics and Robustness

## Statement 1: Theorem 1.1 (Bretagnolle-Massart KMT Theorem)
The approximation of the empirical process by the Brownian bridge holds: P(sup_{0<=t<=1} |sqrt(n)(alpha_n(t) - B_n(t))| > x + c log n) < K e^{-lambda x} for all n and x, with c = 12, K = 2, and lambda = 1/6 for n >= 2.

## Statement 2: Lemma 1.2 (Tusnady's Lemma - Binomial-Normal Approximation)
Let Phi be the standard normal distribution function and Y a standard normal random variable. Let Phi_n be the distribution function of B(n,1/2) and set C_n := Phi_n^{-1}(Phi(Y)) - n/2. Then |C_n| <= 1 + (sqrt(n)/2)|Y| and |C_n - (sqrt(n)/2)Y| <= 1 + Y^2/8.

## Statement 3: Theorem 1.3 (Probability Integral Transform)
Let X be a real random variable with distribution function F. (a) If F is continuous then F(X) has a U[0,1] distribution. (b) For any F, if V has a U[0,1] distribution then F^{-1}(V) has distribution function F.

## Statement 4: Lemma 1.4 (Tusnady's Lemma - Binomial Tail Bounds)
Let Y be standard normal and beta_n be binomial B(n,1/2). For any integer j with 0 <= j <= n and n+j even: P(beta_n >= (n+j)/2) >= P(sqrt(n)Y/2 >= n(1 - sqrt(1-j/n))) and P(beta_n >= (n+j)/2) <= P(sqrt(n)Y/2 >= (j-2)/2).

## Statement 5: Lemma 1.5 (Stirling's Formula with Remainder)
Let n! = (n/e)^n sqrt(2 pi n) A_n where A_n = 1 + beta_n/(12n). Then beta_n decreases to 1 as n -> infinity.

## Statement 6: Lemma 1.6 (Normal Probability on Intervals)
For any 0 <= a < b and a standard normal variable Y, P(Y in [a,b]) >= sqrt(1/(2pi))(b-a) exp[-a^2/4 - b^2/4] phi(a,b) where phi(a,b) := [4/(b^2 - a^2)] sinh[(b^2 - a^2)/4] >= 1.

## Statement 7: Lemma 1.7 (Logarithm Lower Bounds)
log(1+x) >= lambda x for 0 <= x <= alpha for each of the pairs (alpha, lambda) = (0.207, 0.9), (0.195, 0.913), (0.14, 0.93), (0.04, 0.98).

## Statement 8: Lemma 1.8 (Log Interval Bound)
log(Delta_{k+1} - Delta_k) >= lambda d_k where lambda = 0.9 when n is even and n >= 20, lambda = 0.93 when n is odd and n >= 25, and lambda = 0.913 when k = 1 and n >= 10.

## Statement 9: Lemma 1.9 (Chernoff/Bennett-type Binomial Bounds)
Let xi be a binomial random variable with parameters n and p. For x >= 0 and m := np: P(xi - m >= x) <= inf_{s>0} e^{-sx} E e^{s(xi - m)}. If p <= 1/2 then P(xi >= m+x) <= exp(-m h(x/m)/(1-p)) and P(xi <= m-x) <= exp(-x^2/[2p(1-p)]).

## Statement 10: Lemma 1.10 (Empirical Process on Intervals)
For any b with 0 < b <= 1/2 and x > 0, P(sup_{0<=t<=b} |alpha_n(t)| > x/sqrt(n)) <= 2 exp(-nb(1-b)h(x/(nb))).

## Statement 11: Lemma 1.11 (Brownian Bridge Supremum Distribution)
Let B(t) be a Brownian bridge. For 0 < b < 1 and x > 0, the exact distribution of sup_{0<=t<=b} B(t) > x is given in terms of the normal CDF. If 0 < b <= 1/2, then P(sup_{0<=t<=b} B(t) > x) <= exp(-x^2/(2b(1-b))).

## Statement 12: Lemma 1.12 (Linearity of Isonormal Process)
For any Hilbert space H, an isonormal process L on H is linear: for any f, g in H and constant c, L(cf+g) = cL(f) + L(g) almost surely.

## Statement 13: Lemma 1.13 (Affine Functions and Schauder Coefficients)
If f is affine, that is f(t) = a + bt, then the Schauder coefficient f_{j,k} = 0 for all j and k.

## Statement 14: Lemma 1.14 (Schauder Expansion - Finite)
For any f: [0,1] -> R and r = 0, 1, ..., [f]_r(t) = f(0) + t[f(1) - f(0)] + sum_{j=0}^{r-1} sum_{k=1}^{2^j} f_{j,k} T_{j,k}(t).

## Statement 15: Lemma 1.15 (Schauder Expansion - Continuous Functions)
If f is continuous on [0,1] then [f]_r converges to f uniformly as r -> infinity. The Schauder expansion converges uniformly for continuous functions.

## Statement 16: Lemma 1.16 (Wiener and Bridge Schauder Coefficients)
W_{j,k}(B_.) = W_{j,k}(W_.) for all j = 0, 1, ... and k = 1, ..., 2^j, where B is the Brownian bridge and W is the Wiener process.

## Statement 17: Lemma 1.17 (Independence of Bridge Schauder Coefficients)
The random variables W_{j,k}(B_.) for j = 0, 1, ... and k = 1, ..., 2^j are independent with distribution N(0, 2^{-j-2}).

## Statement 18: Lemma 1.18 (Orthogonality of Haar Functions)
The functions g_{j,k} and g_{j',k'} are orthogonal in L^2([0,1]) unless (j,k) = (j',k').

## Statement 19: Theorem (Delta Method)
Let Y_n be a sequence of real-valued random variables such that sqrt(n)(Y_n - mu) converges in distribution to N(0, sigma^2). Let f have a derivative f'(mu) at mu. Then sqrt(n)[f(Y_n) - f(mu)] converges in distribution to N(0, f'(mu)^2 sigma^2).

## Statement 20: Theorem 1 (Affine Equivariance and Symmetry)
Let mu(.) be an affinely equivariant location functional and P be invariant under a set A of non-singular affine transformations. Then: (a) mu(P) is in the fixed-point set S_A; (b) if S_A is a singleton, mu(P) = x_A; (c) for reflection symmetry, mu(P) = v; (d) for n points in general position, mu(P) = centroid; (e) for vertices of a regular simplex, Sigma(P) = cI.

## Statement 21: Proposition 2 (Equivariant Functionals and Breakdown)
For d = 1, 2, ..., there is a sequence {Q_m} of laws with densities such that Q_m(K) = d/(d+1) for a compact K, and for every affinely equivariant location functional mu(.) defined at Q_m, |mu_m| -> infinity.

## Statement 22: Theorem 3 (Obenchain - Singularly Affine Equivariant Location)
(a) If mu(.) is a singularly affine equivariant location functional defined for all P_n on R^d for d >= 2, then mu(P_n) = sample mean. (b) If defined for all n, mu(.) is not weakly continuous. There is no affinely equivariant, weakly continuous location functional on all laws on R^d for d >= 2.

## Statement 23: Theorem 4 (Singularly Affine Equivariant Scatter)
(a) Let Sigma(.) be a singularly affine equivariant scatter functional on R^d for d >= 2 and fixed n >= 2. Then applied to centered data, Sigma is proportional to the sample covariance matrix. (b) If defined for all n and weakly continuous, then Sigma = 0.

## Statement 24: Theorem 5 (Breakdown-Collapse Tradeoff)
Let Sigma be any affinely equivariant scatter functional with values in N_d. Then delta_C^*(Sigma) + kappa(Sigma) <= 1, where delta_C^* is the breakdown point and kappa is the collapse point.

## Statement 25: Proposition 6 (Location Functional Continuity Obstruction)
Let mu(.) be an affinely equivariant location functional on R with delta_C^*(mu) = 1/2. Then the domain cannot be extended to contain (1/2)(delta_a + delta_b) with a != b and be weakly continuous there.

## Statement 26: Theorem 7 (Upper Bounds for Breakdown Points)
Let T be an affinely equivariant location or scatter functional on R^d. Under certain conditions involving a (1-gamma)-degenerate law P, epsilon_R^*(T,P) <= gamma. Under additional continuity and domain conditions, epsilon_C^*(T,F_0) <= gamma.

## Statement 27: Proposition 8 (MVE/Shorth Non-Uniqueness)
(a) For any law P on R with continuous density, for any epsilon > 0, there exists zeta in N_epsilon^C(P) for which the shorth is not defined, so delta_C^*(m_{Sh,1/2}, P) = 0. (b) For any alpha in (0,1), there exist symmetric laws P with center m not in K_alpha(P). (c) Analogous contamination result for unimodal symmetric laws.

## Statement 28: Theorem 1 (Breakdown Points - Order Statistics)
For sample size n, each j=1,...,n, the order statistic T = Z_{(j)} has breakdown point epsilon^*(T) = (1/n) min(j-1, n-j).

## Statement 29: Theorem 2 (Breakdown Point Upper Bound for Location Equivariant Statistics)
For any real-valued statistic T equivariant for location, the breakdown point is < 1/2 at any X.

## Statement 30: Proposition 3.3.4 (Adjustment Functions)
If a_1 is an adjustment function for h(.,.) and P, then a_2(.) is also an adjustment function if and only if a_1 - a_2 is integrable for P, and the set of theta where gamma(theta) is real does not depend on the choice.

## Statement 31: Lemma 3.3.8 (Adjustability and Adjustment Functions)
For any adjustable h(.,.) and adjustment function a(.), and any theta for which gamma_a(theta) is real, h(theta,.) is also an adjustment function.

## Statement 32: Lemma 3.3.9 (Lower Semicontinuity of gamma)
If (A-1), (A-2), and (A-3) hold, then for any theta, as a neighborhood U_k converges to {theta}, E(inf{h(phi,x) - a(x) : phi in U_k}) -> gamma(theta).

## Statement 33: Lemma 3.3.10 (Compactness of M-estimator Sequences)
If (A-1), (A-3), (A-4), and (A-5) hold, then there is a compact set C such that for every sequence T_n of approximate M-estimators, 1_{T_n in C} -> 1 almost uniformly.

## Statement 34: Theorem 3.3.13 (Consistency of Approximate M-estimators)
Let {T_n} be approximate M-estimators. If (A-1) through (A-5) hold, or (A-1), (A-2'), (A-3), (A-4) and compactness hold, then T_n -> theta_0 almost uniformly.

## Statement 35: Theorem 3.3.15 (Kullback-Leibler Divergence Nonnegativity)
Let P, Q be any two laws on a sample space. Then I(P,Q) >= 0 and I(P,Q) = 0 if and only if P = Q.

## Statement 36: Theorem 3.3.16 (Consistency of Approximate MLE)
Under (A-1) in the log likelihood case, with P = P_{theta_0} and identifiability, (A-3) and (A-4) hold. If additionally (A-2) and (A-5) hold, or (A-2') and compactness, then approximate MLEs are consistent.

## Statement 37: Theorem (Spatial Median Existence and Uniqueness)
For any probability measure P on R^d, a spatial median always exists. If P is not concentrated in any line, then its spatial median is unique.

## Statement 38: Theorem (Obenchain - Full Version)
Let d >= 2 and m be a singularly affine equivariant location functional defined on P_{n,d}. Then m(P_n) = sample mean for all P_n.

## Statement 39: Theorem (M-estimator Breakdown Point)
Let psi be odd, nondecreasing, nonconstant, and bounded. Then the M-estimator has breakdown point (1/2 - 1/n) if n is even and (1/2 - 1/(2n)) if n is odd. The same holds for the scale-adjusted M-estimator with MAD.
