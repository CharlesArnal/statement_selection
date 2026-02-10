# All Extracted Statements from Probabilistically Checkable Proofs (MIT 18.408)

## Statement 1: Theorem 1.1 (PCP Theorem -- gap-3-SAT formulation)
There exists epsilon > 0 such that gap-3-SAT[1, 1 - epsilon] is NP-hard. That is, it is NP-hard to distinguish between 3-CNF formulas that are satisfiable and those for which no assignment satisfies more than a (1 - epsilon) fraction of clauses.

## Statement 2: Theorem 1.2 (Hastad's Theorem for 3Lin_2)
For all epsilon > 0, gap-Max-3-Lin_2[1 - epsilon, 1/2 + epsilon] is NP-hard. In other words, it is NP-hard to do better than the trivial random assignment algorithm for systems of linear equations over F_2 with 3 variables per equation.

## Statement 3: Theorem 1.3 (Vertex Cover Hardness of Approximation)
For all epsilon > 0, approximating the minimum vertex cover in a graph within factor sqrt(2) - epsilon is NP-hard. Moreover, gap-Vertex-Cover[1 - epsilon, 1/sqrt(2) + epsilon] is NP-hard.

## Statement 4: Theorem 1.4 (Independent Set Hardness of Approximation)
For all epsilon > 0, gap-Independent-Set[1 - 1/sqrt(2) - epsilon, epsilon] is NP-hard. It is NP-hard to distinguish between graphs containing an independent set of fractional size 1 - 1/sqrt(2) - epsilon and those with no independent set of fractional size epsilon.

## Statement 5: Definition 1.1 (Linear Error Correcting Code)
A linear error correcting code is a subset C of F_q^n which is a subspace of F_q^n over F_q.

## Statement 6: Claim 1.2 (Distance of Linear Code)
For a linear error correcting code C in F_q^n, d(C) = min_{x in C \ {0}} |supp(x)|. The distance of a linear code equals the minimum Hamming weight of a non-zero codeword.

## Statement 7: Claim 1.4 (Polynomial Characterization via Linear Equations)
Let d, q be natural numbers. For all distinct a_0, ..., a_{d+1} in F_q there are nonzero alpha_0, ..., alpha_{d+1} such that: (1) if f: F_q -> F_q has degree at most d, then sum_{i=0}^{d+1} alpha_i f(a_i) = 0; (2) if f is not degree d, then for some choice of a_1, ..., a_{d+1} the sum is nonzero.

## Statement 8: Claim 1.5 (Polynomial Characterization via Arithmetic Progressions)
Let d, q be natural numbers. For x, h in F_q and alpha_i = C(d+1,i)(-1)^i: (1) if f: F_q -> F_q has degree at most d, then sum_{i=0}^{d+1} alpha_i f(x+ih) = 0; (2) if f is not degree d, then for some x, h the sum is nonzero.

## Statement 9: Theorem 1.6 (Local Testability of Reed-Solomon Code)
The local tester T (choose x, h uniformly, check sum_{i=0}^{d+1} alpha_i f(x+ih) = 0) is a (d+2, 2*delta, delta)-tester for RS_{d,n,q} for all delta < 1/(4(d+1)^2).

## Statement 10: Claim 1.7 (Plurality Agreement in RS Testing)
For all x in F_q, Pr_{h_1,h_2}[sum_{i=1}^{d+1} (alpha_i/alpha_0) f(x+ih_1) = sum_{i=1}^{d+1} (alpha_i/alpha_0) f(x+ih_2)] >= 1 - 2(d+1)*delta.

## Statement 11: Claim 1.8 (Degree Bound from Testing)
If delta < 1/(4(d+1)^2), then the plurality function g (constructed from the local tester) has degree at most d.

## Statement 12: Theorem 1.9 (Local Testability of Hadamard Code)
The Hadamard code H_n is (3, 2*epsilon, epsilon)-locally testable for epsilon < 1/8. The tester checks f(x+y) = f(x) + f(y) for random x, y in F_2^n.

## Statement 13: Claim 1.10 (Self-Correction Consistency for Hadamard)
For all x in F_2^n, Pr_{y_1,y_2}[f(x+y_1) - f(y_1) = f(x+y_2) - f(y_2)] >= 1 - 2*epsilon.

## Statement 14: Theorem (Schwartz-Zippel Lemma)
Let f: F_q^m -> F_q be a nonzero polynomial of total degree at most d. Then Pr_{x in F_q^m}[f(x) = 0] <= d/q.

## Statement 15: Theorem (Sum-Check Protocol Completeness and Soundness)
In the sum-check protocol for verifying sum_{x in {0,1}^m} f(x) = s where f has degree at most d in each variable: if s equals the true sum, the honest prover can make the verifier accept; if s does not equal the true sum, no cheating prover can make the verifier accept with probability more than md/q.

## Statement 16: Theorem (Label Cover NP-hardness -- basic PCP)
There exists epsilon_0 > 0 such that gap-Label-Cover[1, 1 - epsilon_0] is NP-hard. That is, it is NP-hard to distinguish between fully satisfiable label cover instances and those where no assignment satisfies more than (1 - epsilon_0) fraction of constraints.

## Statement 17: Theorem 1.2 (Label Cover with Vanishing Soundness)
For all epsilon > 0, gap-Label-Cover[1, epsilon] is NP-hard on instances with polynomial-sized alphabet.

## Statement 18: Theorem 1.3 (Parallel Repetition Theorem)
For all epsilon > 0, there exists delta > 0 such that for any projection 2-prover-1-round game Psi with val(Psi) <= 1 - epsilon, val(Psi^{otimes t}) <= (1 - delta)^t.

## Statement 19: Definition 2.1 (Shannon Entropy)
Let X be a discrete random variable taking values in X. The Shannon Entropy of X is H(X) = sum_{x in X} Pr[X = x] log(1/Pr[X = x]).

## Statement 20: Claim 2.2 (Near-Maximum Entropy Implies Near-Uniformity)
If X is a distribution over X satisfying H(X) >= log(|X|) - epsilon, then SD(X, U) <= sqrt(epsilon), where U is the uniform distribution over X.

## Statement 21: Definition 2.3 (Conditional Shannon Entropy given an Event)
Let X be a discrete random variable taking values in X, and let E be an event. The Shannon entropy of X|E is H(X|E) = sum_{x in X} Pr[X = x | E] log(1/Pr[X = x | E]).

## Statement 22: Definition 2.4 (Conditional Shannon Entropy given a Random Variable)
Let X, Y be discrete random variables. The Shannon Entropy of X|Y is H(X|Y) = E_{y ~ Y}[H(X | Y = y)].

## Statement 23: Claim 2.5 (Conditioning Reduces Entropy)
For jointly distributed discrete random variables (X, Y), H(X|Y) <= H(X).

## Statement 24: Claim 2.6 (Shannon Entropy Sub-additivity)
Let (X, Y) be jointly distributed discrete random variables. Then H(X, Y) <= H(X) + H(Y).

## Statement 25: Claim 2.7 (Entropy Decrease by Conditioning on an Event)
Let U be a discrete uniform random variable over U, and let E be some event. Then H(U | E) >= H(U) - log(1/Pr[E]).

## Statement 26: Theorem 1.1 (Greedy Set Cover Approximation)
Let (U, {S_i}_{i in I}) be a set cover instance whose smallest cover has size k. Then the greedy algorithm (pick the set covering the most uncovered elements) finds a set cover of size at most k ln(|U|).

## Statement 27: Definition 1.2 ((l,m,n) Set System)
An (l, m, n) set system consists of a universe U of size n and a collection of m sets A_1, ..., A_m and their complements B_1, ..., B_m. It is an (l, m, n) instance if any cover of U using subsets from {A_i} and {B_i} must contain some set and its complement.

## Statement 28: Lemma 1.3 (Existence of (l,m,n) Set Systems)
For all l in N, there is an (l, 2l, 2^l) set system, and this system can be constructed in time 2^{O(l)}.

## Statement 29: Theorem 2.1 (Label Cover Hardness with Bi-regularity)
For all epsilon > 0, there is k in N such that gap-Label-Cover[1, epsilon] is NP-hard on instances with alphabet size at most k and bi-regular constraint graphs.

## Statement 30: Theorem 2.2 (Hardness of Weighted Set Cover)
For all epsilon > 0, there is l in N such that gap-Weighted-set-cover[l, l/epsilon] is NP-hard.

## Statement 31: Claim 2.3 (Edge Satisfiability from Set Cover)
Let e in E be any edge with e = (u,v). Then there are pairs of labels sigma_u in Labels(u) and sigma_v in Labels(v) that satisfy the constraint Phi_e.

## Statement 32: Theorem 1.1 (3Lin_q Hardness of Approximation)
For all prime powers q, and for all epsilon, delta > 0, the problem gap-3Lin_q[1 - epsilon, 1/q + delta] is NP-hard.

## Statement 33: Theorem 1.2 (3SAT Hardness of Approximation)
For all epsilon > 0, the problem gap-3SAT[1, 7/8 + epsilon] is NP-hard. The random assignment algorithm achieving 7/8 satisfaction is optimal assuming P != NP.

## Statement 34: Definition 1.4 (The Long Code)
Let n in N and i in {1, ..., n}. The long code encoding of i is the truth table of f_i: {0,1}^n -> {0,1} defined by f_i(x) = x_i. The long code is LC = {(f_i(x))_{x in {0,1}^n} | i in [n]}.

## Statement 35: Definition 2.1 (Inner Product on Boolean Functions)
For functions F, G: {-1,1}^n -> R, define <F, G> = E_{z in {-1,1}^n}[F(z)G(z)]. This defines an inner product on L_2({-1,1}^n).

## Statement 36: Lemma 2.2 (Characters Form Orthonormal Basis)
The set {chi_alpha}_{alpha in F_2^n} is an orthonormal set in L_2({-1,1}^n), where chi_alpha(z) = prod_{i: alpha_i = 1} z_i. Since dim(L_2({-1,1}^n)) = 2^n = |F_2^n|, this is an orthonormal basis.

## Statement 37: Theorem 2.3 (Linearity Test in List Decoding Regime)
Suppose F: {-1,1}^n -> {-1,1} satisfies Pr_{x,y}[F(x)F(y) = F(xy)] >= 1/2 + delta. Then there exists alpha in F_2^n such that F-hat(alpha) >= 2*delta.

## Statement 38: Lemma 2.4 (Bound on Large Fourier Coefficients)
Suppose F: {-1,1}^n -> {-1,1} is any function, and let epsilon > 0. Then the number of alpha's such that F-hat(alpha) >= epsilon is at most 1/epsilon^2.

## Statement 39: Theorem 2.5 (Noisy Linearity Test)
Let F: {-1,1}^n -> {-1,1} and epsilon > 0. (1) If F is a long-code codeword F(x) = x_i, then the noisy linearity tester passes with probability 1 - epsilon. (2) If F passes the noisy linearity tester with probability 1/2 + delta, then there is alpha in F_2^n such that (1-2*epsilon)^{|alpha|} * F-hat(alpha) >= 2*delta. In particular, there is alpha of size at most ln(1/delta)/(2*epsilon) with F-hat(alpha) >= 2*delta.

## Statement 40: Theorem 3.1 (Combined Long-Code Test Analysis)
Suppose g_u: {-1,1}^{Sigma_L} -> {-1,1} and g_v: {-1,1}^{Sigma_R} -> {-1,1} are functions such that Pr[g_u(zya)g_u(z) = g_v(x)] >= 1/2 + delta. Then sum_{|alpha| <= ln(1/delta)/epsilon} g_u-hat(alpha)^2 * g_v-hat(phi_{u,v}^odd(alpha))^2 >= delta^2.

## Statement 41: Theorem 4.1 (Label Cover Hardness -- restated for 3Lin reduction)
For all eta > 0, there is k in N such that gap-Label-Cover[1, eta] is NP-hard on instances with alphabet size at most k and bi-regular constraint graphs.

## Statement 42: Lemma 4.2 (Completeness of 3Lin Reduction)
If the label cover instance Psi is satisfiable, then there is an assignment to the constructed 3Lin system (X, E, w) that satisfies at least 1 - epsilon fraction of the equations.

## Statement 43: Lemma 4.3 (Soundness of 3Lin Reduction)
For all epsilon, delta > 0, there is delta' > 0 such that if there is an assignment to (X, E, w) satisfying at least 1/2 + delta of the equations, then val(Psi) >= delta'.

## Statement 44: Definition 2.1 (d-to-1 Games)
An instance of d-to-1-Games is Psi = (G = (L union R, E), Sigma_L, Sigma_R, Phi) where G is bi-regular bipartite, |Sigma_L| = d|Sigma_R|, and each constraint Phi_e is defined by a d-to-1 map phi_e: Sigma_L -> Sigma_R.

## Statement 45: Definition 2.2 (Unique Games)
The Unique-Games problem is the d-to-1-Games problem for d = 1. Each constraint is a bijection (permutation) between alphabets of equal size.

## Statement 46: Conjecture 2.3 (d-to-1 Games Conjecture)
For all d >= 2 and for all epsilon > 0, there is k in N such that gap-d-to-1-Games[1, epsilon] is NP-hard on instances with alphabet sizes at most k.

## Statement 47: Conjecture 2.4 (Unique Games Conjecture)
For all epsilon, delta > 0, there is k in N such that gap-Unique-Games[1 - epsilon, delta] is NP-hard on instances with alphabet sizes at most k.

## Statement 48: Theorem 3.1 (1/2-Approximation for Max-Cut)
There is a polynomial time 1/2-approximation for Max-Cut. A random cut achieves expected size |E|/2, which is at least (1/2) * MC(G).

## Statement 49: Theorem 3.2 (Goemans-Williamson Algorithm for Max-Cut)
For alpha_GW approximately 0.878, there is a polynomial time alpha_GW-approximation for Max-Cut, using semi-definite programming relaxation and random hyperplane rounding.

## Statement 50: Theorem 3.3 (GW Algorithm for Almost Bipartite Graphs)
Suppose G = (V, E) has a cut of size (1 - epsilon)|E|. Then the expected size of the cut in the Goemans-Williamson algorithm is at least (1 - (2/pi)(1 + o(1))*sqrt(epsilon))|E|.

## Statement 51: Definition 1.1 (Influence of a Coordinate)
Let f: {-1,1}^n -> {-1,1} be a function and i in [n]. The influence of i is I_i[f] = Pr_{x}[f(x) != f(x * e_i)], where x * e_i flips the i-th coordinate.

## Statement 52: Definition 1.2 (tau-Small Influences)
A function f: {-1,1}^n -> {-1,1} has tau-small influences if for all i in [n], I_i[f] <= tau.

## Statement 53: Theorem 1.3 (Majority is Stablest -- Boolean version)
For all epsilon > 0 and eta > 0, there is tau > 0 such that if f: {-1,1}^n -> {-1,1} has E[f] = 0 and max_i I_i[f] <= tau, then Pr_{(x,y)~mu}[f(x) != f(y)] <= 1 - (1/pi) Arccos(1 - epsilon) + eta.

## Statement 54: Definition 1.4 (rho-Correlated Distribution)
Let rho in [0,1] and x in {-1,1}^n. The distribution T_rho x is defined by: for each i independently, y_i = x_i with probability rho, otherwise y_i is uniform in {-1,1}. For rho in [-1,0], T_rho x = -T_{-rho} x.

## Statement 55: Definition 1.5 (Stability of a Function)
Let rho in [-1,1] and f: {-1,1}^n -> [-1,1]. Define Stab_rho(f) = E_{x, y ~ T_rho x}[f(x)f(y)].

## Statement 56: Claim 1.6 (Fourier Formula for Influences)
For f: {-1,1}^n -> {-1,1} and i in [n], I_i[f] = sum_{alpha: alpha_i = 1} f-hat(alpha)^2.

## Statement 57: Definition 1.7 (Low-Degree Influence)
Let d in N, f: {-1,1}^n -> R and i in [n]. The degree-d influence of f is I_i^{<=d}[f] = sum_{alpha in F_2^n: |alpha| <= d, alpha_i = 1} f-hat(alpha)^2.

## Statement 58: Lemma 1.8 (Sum of Low-Degree Influences)
Let f: {-1,1}^n -> R and d in N. Then sum_{i=1}^n I_i^{<=d}[f] <= d * ||f||_2^2. Consequently, if f: {-1,1}^n -> [-1,1], then for all tau > 0, the number of coordinates with I_i^{<=d}[f] >= tau is at most d/tau.

## Statement 59: Theorem 1.9 (Majority is Stablest -- bounded functions, positive rho)
Let rho in [0,1] and fix eta > 0. There are d in N and tau > 0 such that if f: {-1,1}^n -> [-1,1] has E[f] = 0 and max_i I_i^{<=d}[f] <= tau, then Stab_rho(f) <= 1 - (2/pi) Arccos(rho) + eta.

## Statement 60: Theorem 1.10 (Majority is Stablest -- bounded functions, negative rho)
Let rho in [-1,0] and fix eta > 0. There are d in N and tau > 0 such that if f: {-1,1}^n -> [-1,1] has E[f] = 0 and max_i I_i^{<=d}[f] <= tau, then Stab_rho(f) >= (2/pi) Arccos(-rho) - 1 - eta.

## Statement 61: Definition 2.1 (Unique Games Instance -- restated for Max-Cut reduction)
An instance of Unique-Games is an instance of Label-Cover Psi = (G, Sigma_L, Sigma_R, Phi) where |Sigma_L| = |Sigma_R| and each constraint Phi_e is a permutation (1-to-1 map phi_e: Sigma_L -> Sigma_R).

## Statement 62: Conjecture 2.2 (Unique Games Conjecture -- restated for Max-Cut reduction)
For all epsilon, delta > 0 there is k in N such that gap-UniqueGames[1 - epsilon, delta] is NP-hard on instances with alphabet size at most k.

## Statement 63: Lemma 2.3 (Max-Cut Reduction Analysis)
For all rho in (0,1) and delta > 0, there is eta > 0 such that: (1) Completeness: if Psi is at least 1 - eta satisfiable, then there is a cut of weight at least (1+rho)/2 - delta. (2) Soundness: if Psi is at most eta satisfiable, then no cut has weight exceeding 1 - (1/pi) Arccos(rho) + delta.

## Statement 64: Claim 2.4 (Fourier Coefficients of Averaged Functions)
For all alpha in F_2^{Sigma_R}, g_v-hat(alpha) = E_{u:(u,v) in E}[g_u-hat(phi_{(v,u)} alpha)].

## Statement 65: Lemma 2.5 (Label Propagation via Low-Degree Influence)
Suppose v in L_good and i in List_tau(v). Then Pr_{u:(u,v) in E}[phi_{v,u}(i) in List_{tau/2}(u)] >= tau/2.

## Statement 66: Theorem (Hamming Bound for Error Correcting Codes)
For an error correcting code C in Sigma^n, R(C) + d(C)/2 + o(1) <= 1, where R is the rate and d is the relative distance. A code cannot simultaneously have both relative distance and rate close to 1.

## Statement 67: Theorem (Reed-Solomon Code Parameters)
The Reed-Solomon code RS_{d,a_1,...,a_n,q} with q >= n is an (n, 1 - d/n, (d+1)/n, q) code. The distance follows from the fundamental theorem of algebra: a nonzero univariate polynomial of degree at most d has at most d roots.

## Statement 68: Theorem (Composed Code Parameters)
If C_1 is an (n_1, d_1, r_1, q_1) code and C_2 is an (n_2, d_2, r_2, q_2) code with |C_2| >= q_1, then the composed code C_1 o C_2 is an (n_1*n_2, d_1*d_2, r_1*r_2, q_2) code. Rate and relative distance multiply, and the alphabet is inherited from C_2.

## Statement 69: Theorem (Parseval's Equality for Boolean Fourier Analysis)
For any real-valued function G: {-1,1}^n -> R with Fourier expansion G(z) = sum_alpha G-hat(alpha) chi_alpha(z), we have E_z[G(z)^2] = sum_alpha G-hat(alpha)^2.

## Statement 70: Theorem (Chain Rule for Shannon Entropy)
For jointly distributed discrete random variables (X, Y), H(X, Y) = H(X) + H(Y | X). This follows from writing p_{x,y} = p_x * p_{y|x} and expanding the entropy.

## Statement 71: Definition 1.3 (Local Tester for Error Correcting Code)
For a code C in F_q^n and parameters h in N, epsilon, delta > 0, an (h, epsilon, delta)-local tester T is a randomized algorithm with oracle access to w in F_q^n that: (1) makes at most h oracle accesses; (2) accepts w in C with probability 1; (3) rejects w with Delta(w, C) >= epsilon * n with probability at least delta.

## Statement 72: Theorem (Entropy Upper Bound)
For a discrete random variable X over X, H(X) <= log(|X|). Equality holds if and only if X is uniformly distributed over X. This follows from Jensen's inequality applied to the concave function log.

## Statement 73: Theorem (Fourier Coefficient Formula)
For any function G: {-1,1}^n -> R and alpha in F_2^n, G-hat(alpha) = <G, chi_alpha> = E_z[G(z) chi_alpha(z)].

## Statement 74: Theorem (Product of Characters)
For alpha, alpha' in F_2^n, chi_alpha(z) * chi_{alpha'}(z) = chi_{alpha + alpha'}(z), where addition is in F_2^n. In particular, if alpha != alpha', <chi_alpha, chi_{alpha'}> = 0.

## Statement 75: Theorem (Reed-Muller Code Parameters)
The Reed-Muller code RM_{m,d,q} with q >= d has rate binom(m+d, m)/q^m and relative distance at least 1 - d/q.

## Statement 76: Theorem (Cook-Levin Theorem)
3-SAT is NP-hard. For any language L in NP, there exists a polynomial-time reduction f such that z in L iff f(z) is satisfiable.

## Statement 77: Theorem (Stability of Majority Function)
The majority function h: {-1,1}^n -> {-1,1} satisfies Stab_rho(Majority) = 1 - (2/pi) Arccos(rho) + o(1) as n -> infinity. This equals the upper bound from the Majority is Stablest theorem for functions with small influences.

## Statement 78: Theorem (Influence of Majority Function)
For the majority function on n variables (n odd), the influence of each coordinate i is I_i[Maj] = binom(n-1, (n-1)/2) / 2^{n-1} ~ sqrt(2/(pi*n)).

## Statement 79: Theorem (Max-Cut as Constraint Satisfaction Problem)
Max-Cut can be formulated as an integer program: max (1/2) sum_{(u,v) in E} (1 - x_u * x_v) subject to x_v in {-1,1} for all v. The SDP relaxation replaces {-1,1} with unit vectors in R^r.

## Statement 80: Theorem (Goemans-Williamson Rounding Analysis)
For the random hyperplane rounding of the SDP relaxation: the expected cut size is sum_{(u,v) in E} Arccos(<x_u, x_v>)/pi >= alpha_GW * rho * |E|, where alpha_GW = min_{z in [-1,1]} (Arccos(z)/pi) / ((1-z)/2) ~ 0.878.

## Statement 81: Theorem (Pinsker's Inequality -- cited)
If the KL-divergence between distributions P and Q is at most epsilon, then SD(P, Q) <= sqrt(epsilon/2). This is used to derive Claim 2.2 about near-maximum entropy implying near-uniformity.

## Statement 82: Theorem (Arithmetic Expression for Stability via Cut)
For {-1,1}-valued functions f, Pr_{(x,y)~mu}[f(x) != f(y)] = (1/2) * E_{(x,y)~mu}[1 - f(x)f(y)] = (1/2)(1 - Stab_{-1+epsilon}(f)).

## Statement 83: Remark 2.6 (Dimension-Free Property of the Reduction)
The performance of the randomized assignment strategy for the Unique-Games instance depends on parameters of the reduction (noise rate rho) but not on the alphabet size of the Unique-Games instance. This dimension-free property is critical for the hardness reduction to work.
