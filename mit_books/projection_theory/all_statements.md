# All Mathematical Statements from Projection Theory (MIT 18.156, Spring 2025)

## Statement 1: Theorem (Szemeredi-Trotter, 1982)
If $X$ is a finite subset of $\mathbb{R}^2$, and $S < \frac{1}{2}|X|$, then $|E_S(X)| \le C S^2 |X|^{-1} + 1$, where $E_S(X)$ is the set of lines $L$ with $|\pi_L(X)| \le S$.

## Statement 2: Theorem (Marstrand, 1954)
If $X \subset \mathbb{R}^2$ is a compact set, then for almost every line $L$, $\text{HD}(\pi_L(X)) = \min(\text{HD}(X), 1)$.

## Statement 3: Theorem (Orponen-Shmerkin-Ren-Wang)
If $X \subset \mathbb{R}^2$ and $s < \text{HD}(X)$, then $\text{HD}(E_s(X)) \le \max(2s - \text{HD}(X), 0)$.

## Statement 4: Conjecture (Projection theory over $\mathbb{F}_p$)
Suppose $X \subset \mathbb{F}_p^2$, $D \subset \mathbb{F}_p$, and $S = \max_{\theta \in D} |\pi_\theta(X)|$. If $S \le p/2$, then $|D| \lesssim S^2/|X|$.

## Statement 5: Theorem (Double counting over $\mathbb{F}_q$)
Suppose $X \subset \mathbb{F}_q^2$, $D \subset \mathbb{F}_q$, and $S = \max_{\theta \in D}|\pi_\theta(X)|$. If $S \le |X|/2$, then $|D| \lesssim S$.

## Statement 6: Theorem (Orthogonality/Fourier method over $\mathbb{F}_q$)
Suppose $X \subset \mathbb{F}_q^2$, $D \subset \mathbb{F}_q$, and $S = \max_{\theta \in D}|\pi_\theta(X)|$. If $S \le q/2$, then $|D| \lesssim Sq/|X|$.

## Statement 7: Lemma (Orthogonality of line indicators)
If $L_1, L_2$ are two different lines in $\mathbb{F}_q^2$, then $\sum_{x \in \mathbb{F}_q^2} L_{1,h}(x) L_{2,h}(x) \le 0$.

## Statement 8: Theorem (Fourier inversion over $\mathbb{F}_q^d$)
If $f: \mathbb{F}_q^d \to \mathbb{C}$, then $f(x) = \frac{1}{q^d} \sum_{\xi \in \mathbb{F}_q^d} \hat{f}(\xi) e(x \cdot \xi)$.

## Statement 9: Theorem (Plancherel over $\mathbb{F}_q^d$)
If $f, g: \mathbb{F}_q^d \to \mathbb{C}$, then $\sum_{x \in \mathbb{F}_q^d} f(x) \overline{g(x)} = \frac{1}{q^d} \sum_{\xi \in \mathbb{F}_q^d} \hat{f}(\xi) \overline{\hat{g}(\xi)}$.

## Statement 10: Lemma (Fourier transform of affine plane indicator)
If $P(x)$ is the characteristic function of an affine $k$-plane in $\mathbb{F}_q^d$, then $|\hat{P}(\xi)| = q^k$ if $\xi \in P^\perp$ and $0$ otherwise.

## Statement 11: Theorem (Double Counting Real Version)
If SETUP (set of disjoint unit balls in $B_R \subset \mathbb{R}^2$, $D \subset S^1$ a set of $1/R$-separated directions), then $|D| \lesssim \frac{S}{|X|} \sum_{1 \le r \le R} N_X(r) N_D(1/r)$.

## Statement 12: Corollary (Double Counting Real with Hausdorff spacing)
If SETUP and $X$, $D$ have Hausdorff spacing, then $|D| \lesssim \log R (|S| + \frac{|S|}{|X|}|D|)$, which implies $S \sim X$ or $|D| \lesssim S$.

## Statement 13: Theorem (Double counting finite field restated)
If $X \subseteq \mathbb{F}_q^2$, $D \subseteq \mathbb{F}_q$, $S = \max_{\theta \in D}|\pi_\theta(X)|$, then $S \sim |X|$ or $|D| \lesssim S$.

## Statement 14: Theorem (Fourier Method Finite Field restated)
If $\mathbb{F}_q$-SETUP and $S \le q/2$, then $|D| \lesssim Sq/|X|$.

## Statement 15: Corollary (Fourier method real version)
If $\mathbb{R}$-SETUP and $X, D$ have Hausdorff spacing, then $|D| \lesssim SR/|X|$.

## Statement 16: Conjecture (Prime field projection)
If $p$ prime, $\mathbb{F}_p$-SETUP and $S \le \frac{1}{2}\min(q, |X|)$, then $|D| \lesssim S^2/|X|$.

## Statement 17: Conjecture (Furstenberg, discrete version)
If SETUP, $X$ and $D$ have Hausdorff spacing and $S \le R^{-\epsilon}\min(R, |X|)$, then $|D| \lessapprox S^2/R$.

## Statement 18: Lemma (Main lemma in finite field, $L^2$ decomposition)
If $\mathcal{L}$ is a set of lines in $\mathbb{F}_q^2$ and $f = \sum_{L \in \mathcal{L}} 1_L(x)$, then $f = f_0 + f_h$ with $\text{supp}(\hat{f}_0) = \{0\}$, $\text{supp}(\hat{f}_h) = \{0\}^c$, $\|f_0\|_2^2 = |\mathcal{L}|^2$, $\|f_h\|_2^2 = |\mathcal{L}|q$.

## Statement 19: Lemma (Main lemma in real, $L^2$ decomposition)
Let $\mathbb{T}$ be a set of $1 \times R$ rectangles in $\mathbb{R}^2$. Let $f = \sum_{T \in \mathbb{T}} \phi_T(x)$. Then $f = \sum_r f_r(x)$ with $\text{supp}(\hat{f}_r) \subseteq B(1/r)$ and $\|f_r\|_2^2 \lesssim N_{\mathbb{T}}(r)|\mathbb{T}|r^{-1}R$.

## Statement 20: Lemma (Orthogonality of tube functions)
If $T_1, T_2$ are $1 \times R$ tubes then $|\langle \phi_{T_1,r}, \phi_{T_2,r}\rangle| \lesssim R^{-1000}$ unless there exists a $R^\epsilon r \times R^{1+\epsilon}$ rectangle $\tilde{T}$ such that $T_1, T_2 \in \tilde{T}$.

## Statement 21: Lemma (Main Lemma 2F - Fourier method finite field bound)
If $\mathcal{L}$ is a set of lines in $\mathbb{F}_q^2$ covering each point of $X$ at least $D$ times, then the high-frequency part satisfies $\sum_{x \in \mathbb{F}_q^2}|f_h(x)|^2 \le |\mathcal{L}| q$.

## Statement 22: Lemma (Elementary $L^2$ bounds on $f$)
For $f = \sum_{T \in \mathbb{T}} \phi_T$, the decomposition $f = \sum f_r$ satisfies $\|f_r\|_2^2 \lesssim N_{\mathbb{T}}(r)|\mathbb{T}|r^{-1}R$ with Fourier support in $B(1/r)$.

## Statement 23: Lemma (Main Lemma 2R - Fourier method real version bound)
If $\mathbb{T}$ is a set of $1 \times R$ tubes in $B_R^2$ covering each ball of $X$ at least $D$ times, with Hausdorff spacing $\alpha$, then we get matching bounds to the finite field case.

## Statement 24: Lemma (Tube counting)
Given $X$ a set of $\delta$-balls and $D$ a set of directions, the number of $\delta$-tubes needed relates to the doubling number via $\sum_r N_X(r) N_D(1/r)$.

## Statement 25: Lemma (Frequency localization)
If $f_r$ is frequency-localized to scale $1/r$, then $|f_r(x)|$ is essentially constant on balls of radius $r$.

## Statement 26: Lemma (Tube incidence bound)
The number of incidences between a set of $\delta$-tubes and $\delta$-balls can be bounded using the $L^2$ method.

## Statement 27: Theorem (Szemeredi-Trotter incidence theorem)
Given $P$ points and $L$ lines in $\mathbb{R}^2$, the number of incidences satisfies $I(P, L) \lesssim |P|^{2/3}|L|^{2/3} + |P| + |L|$.

## Statement 28: Corollary (Projection bound from Szemeredi-Trotter)
For $X$ a finite set in $\mathbb{R}^2$, if $S$ lines each contain at least $R$ points of $X$, then $S \lesssim |X|^2/R^3 + |X|/R$.

## Statement 29: Theorem (Linnik's theorem on squares)
If $X \subset \{1, \ldots, N\}$ and $|\pi_p(X)| \le (p+1)/2$ for every prime $p$, then $|X| \lessapprox N^{1/2}$.

## Statement 30: Theorem (1S - Large sieve inequality version)
If $A \subset \{1, \ldots, N\}$ and for each prime $p$, $|\pi_p(A)| \le (p+1)/2$, then $|A| \le C \cdot N^{1/2}$ (with logarithmic losses).

## Statement 31: Theorem (Linnik, sieve formulation)
If $X \subset \{1, \ldots, N\}$ and $|\pi_p(X)| \le (p+1)/2$ for every prime $p \le N$, then $|X| \lessapprox N^{1/2}$.

## Statement 32: Corollary (Large sieve for general sets)
The large sieve inequality bounds the size of sets with restricted projections modulo primes.

## Statement 33: Corollary (Sieve bound)
If $X \subset \{1, \ldots, N\}$ with bounded projections mod $p$ for all primes $p \le z$, then $|X| \le N/L + z^2$ for appropriate $L$.

## Statement 34: Lemma (Character sum bound)
Character sums over $\mathbb{Z}/q\mathbb{Z}$ satisfy orthogonality relations that bound the number of elements with prescribed residue properties.

## Statement 35: Corollary (Bombieri-Vinogradov type)
The large sieve gives equidistribution of arithmetic sets modulo most moduli $q \le N^{1/2-\epsilon}$.

## Statement 36: Lemma (Dictionary: projection theory to sieve theory)
The double counting method in projection theory corresponds to the larger sieve in number theory; the Fourier method corresponds to the large sieve.

## Statement 37: Lemma (Previous projection estimates restated for sieve)
The double counting and Fourier bounds in projection theory translate to corresponding sieve bounds.

## Statement 38: Lemma (Sieve theory fundamental lemma)
If $A \subset \{1, \ldots, N\}$ and $|\pi_p(A)| \le c \cdot p$ for each prime $p$, then $|A| \lesssim N/(\log N)^{1-c}$.

## Statement 39: Theorem (Linnik, sieve version restated)
If $X \subset \{1, \ldots, N\}$ and for each prime $p$, $|\pi_p(X)| \le (p+1)/2$, then $|X| \lessapprox N^{1/2}$.

## Statement 40: Lemma (Dictionary: geometric to number-theoretic)
Projection theory translates: $\delta$-balls to integers, directions to primes, Hausdorff dimension to density in sieve theory.

## Statement 41: Theorem (Smoothing by projecting to typical direction)
For a set $X$ with Hausdorff spacing, projecting to a typical direction produces a set whose Fourier transform has good decay.

## Statement 42: Lemma (Dictionary: real projection to sieve)
The Fourier method in real projection theory is parallel to the large sieve inequality.

## Statement 43: Theorem (Dirichlet's theorem on primes in arithmetic progressions)
For $(a, q) = 1$, $\lim_{x \to \infty} \frac{|\{p \le x : p \equiv a \pmod{q}\}|}{|\{p \le x\}|} = \frac{1}{\phi(q)}$.

## Statement 44: Theorem (Siegel-Walfisz)
For every $A > 0$, $|\{p \le x : p \equiv a \pmod{q}\}| = \frac{\text{Li}(x)}{\phi(q)} + O(x/(\log x)^A)$ for $q \le (\log x)^A$.

## Statement 45: Theorem (Renyi, Bombieri-Vinogradov)
For every $A > 0$, $\sum_{q \le x^{1/2}/(\log x)^B} \max_{(a,q)=1} |\pi(x; q, a) - \text{Li}(x)/\phi(q)| \le C_A x/(\log x)^A$.

## Statement 46: Lemma (Large sieve inequality)
$\sum_{q \le Q} \sum_{\chi \pmod{q}} |\sum_{n \le N} a_n \chi(n)|^2 \le (N + Q^2) \sum_{n \le N} |a_n|^2$.

## Statement 47: Lemma (Lemma 1 - Orthogonality of characters)
The orthogonality relations for Dirichlet characters give $\sum_\chi \chi(a)\overline{\chi(b)} = \phi(q)\delta_{a \equiv b}$.

## Statement 48: Lemma (Lemma 2 - Dual large sieve)
The large sieve inequality has an equivalent dual formulation bounding exponential sums.

## Statement 49: Lemma (Lemma 3 - Exponential sum bound)
$\sum_{q \le Q} \sum_{a \pmod{q}, (a,q)=1} |S(a/q)|^2 \le (N + Q^2) \sum |a_n|^2$ where $S(\alpha) = \sum a_n e(n\alpha)$.

## Statement 50: Lemma (Lemma 4 - Well-spacing of fractions)
If $a_1/q_1 \neq a_2/q_2$ with $q_1, q_2 \le Q$ and $(a_i, q_i) = 1$, then $|a_1/q_1 - a_2/q_2| \ge 1/(q_1 q_2) \ge 1/Q^2$.

## Statement 51: Proposition (Large sieve from exponential sums)
The large sieve inequality follows from the exponential sum bound combined with the well-spacing of Farey fractions.

## Statement 52: Theorem (Fourier method for projection theory in Euclidean space)
Using the $L^2$ decomposition and Littlewood-Paley theory, one obtains bounds on projection sizes analogous to the finite field case.

## Statement 53: Theorem (Discrete Fourier restriction)
The Fourier restriction method gives bounds on the size of projections of sets with controlled spacing.

## Statement 54: Theorem (Real projection counting bound)
For $X$ a set of $\delta$-balls in $B_1 \subset \mathbb{R}^2$ with $(\delta, t, C)$ spacing and $D$ a set of $(\delta, s, C)$-separated directions, the projection sizes satisfy the double counting and Fourier bounds.

## Statement 55: Lemma (Tube intersection bound)
Two $1 \times R$ tubes $T_1, T_2$ with angle $\alpha$ between them satisfy $|T_1 \cap T_2| \lesssim R/\alpha$.

## Statement 56: Lemma (Cell decomposition lemma)
Given $n$ lines in $\mathbb{R}^2$, they partition $\mathbb{R}^2$ into $O(n^2)$ cells, each of which is a convex polygon. For any set of $r$ lines chosen from the $n$, each cell intersects at most $O(n/r)$ of the remaining lines.

## Statement 57: Theorem (Borsuk-Ulam Theorem)
If $f: S^n \to \mathbb{R}^n$ is continuous, then there exists $x \in S^n$ such that $f(x) = f(-x)$.

## Statement 58: Corollary (Ham Sandwich Theorem)
Given $n$ finite measures in $\mathbb{R}^n$, there exists a hyperplane that simultaneously bisects all $n$ measures.

## Statement 59: Theorem (Polynomial Ham Sandwich Theorem)
Given $\binom{d+n}{n} - 1$ finite measures in $\mathbb{R}^n$, there exists a polynomial of degree $d$ whose zero set simultaneously bisects all the measures.

## Statement 60: Lemma (Ham Sandwich theorem for finite sets)
Given $n$ finite sets in $\mathbb{R}^n$, there exists a hyperplane bisecting each set (up to $\pm 1$).

## Statement 61: Theorem (Szemeredi-Trotter via cell decomposition)
The Szemeredi-Trotter incidence bound $I(P, L) = O(|P|^{2/3}|L|^{2/3} + |P| + |L|)$ can be proved using the polynomial cell decomposition.

## Statement 62: Theorem (Bourgain-Katz-Tao projection theorem)
If $X \subset \mathbb{F}_p^2$, $D \subset \mathbb{F}_p$, $|X| = p^{s_X}$, $|D| = p^{s_D}$, $0 < s_X, s_D < 1$, and $S = \max_{\theta \in D}|\pi_\theta(X)|$, then $S \ge p^{s_X/2 + \epsilon}$ for some $\epsilon = \epsilon(s_X, s_D) > 0$.

## Statement 63: Lemma (Sum-product lower bound)
If $A \subset \mathbb{F}_p$ with $|A| = p^s$, $0 < s < 1$, then $\max(|A+A|, |A \cdot A|) \ge |A|^{1+\epsilon}$ for some $\epsilon > 0$.

## Statement 64: Theorem (Freiman-Ruzsa)
If $A \subset \mathbb{Z}$ and $|A + A| \le K|A|$, then $A$ is contained in a generalized arithmetic progression of dimension $O_K(1)$ and size $O_K(|A|)$.

## Statement 65: Conjecture (Polynomial Freiman-Ruzsa)
If $A \subset \mathbb{F}_p^n$ and $|A + A| \le K|A|$, then $A$ is covered by $\text{poly}(K)$ cosets of a subgroup of size at most $\text{poly}(K)|A|$.

## Statement 66: Theorem (Ruzsa's triangle inequality)
$|A - C| \le |A - B| \cdot |B - C| / |B|$ for finite subsets $A, B, C$ of an abelian group.

## Statement 67: Corollary (Ruzsa's covering lemma)
If $|A + B| \le K|A|$, then $B$ is covered by $K$ translates of $A - A$.

## Statement 68: Theorem (Plunnecke's inequality)
If $|A + B| \le K|A|$, then $|nB - mB| \le K^{n+m}|A|$.

## Statement 69: Corollary (Plunnecke-Ruzsa iterated sumset bound)
If $|A + A| \le K|A|$, then $|nA - mA| \le K^{n+m}|A|$.

## Statement 70: Corollary (Sumset chain bound)
If $|A + A| \le K|A|$, then for any $k$, $|kA| \le K^{2k}|A|$.

## Statement 71: Lemma (Contagious structure)
If $A \subset \mathbb{F}_p$ with $|A+A| \le K|A|$ and $B \subset A$ with $|B| \ge |A|/K$, then $|B+B| \le K^3|B|$.

## Statement 72: Theorem (Bourgain-Katz-Tao, full version)
If $A \subset \mathbb{F}_p$ with $p^{\delta} \le |A| \le p^{1-\delta}$, then $\max(|A+A|, |A \cdot A|) \ge c|A|^{1+\epsilon}$ for $\epsilon = \epsilon(\delta) > 0$.

## Statement 73: Corollary (BKT projection consequence)
Under BKT hypotheses, for most $\theta \in D$, $|\pi_\theta(X)| \ge |X|^{1/2+\epsilon}$.

## Statement 74: Lemma (Key step in BKT proof)
If $A + tA$ is small for many $t$, then $A$ has additive structure.

## Statement 75: Lemma (Double counting for sum-product)
$\sum_t |A + tA| \ge |A|^3 / |A \cdot A|$ by a counting argument.

## Statement 76: Lemma (Sum-product from Plunnecke-Ruzsa)
If $|A + A| \le K|A|$ and $|A \cdot A| \le K|A|$, then $|A| \lesssim K^C$ or $|A| \ge p^{1-\epsilon}$.

## Statement 77: Theorem (Main theorem - BKT projection, refined)
If $0 < s_X, s_D < 1$, $X \subset \mathbb{F}_p^2$ with $|X| = p^{s_X}$, $D \subset \mathbb{F}_p$ with $|D| = p^{s_D}$, then there exists $\theta \in D$ with $|\pi_\theta(X)| \ge p^{s_X/2+\epsilon}$ for $\epsilon(s_X, s_D) > 0$.

## Statement 78: Corollary (Projection lower bound)
Under BKT conditions, $S \ge p^{s_X/2 + \epsilon}$.

## Statement 79: Lemma (Double Counting for BKT)
The coincidence counting gives $|D| |X|^2 / S \le |X|^2$, hence $|D| \le S$.

## Statement 80: Lemma (Sum-product expansion)
If $A \subset \mathbb{F}_p$ with $|A| = p^s$, $0 < s < 1$, then there exists a polynomial $Q$ such that $|Q(A)| \ge |A|^{1+\epsilon}$.

## Statement 81: Theorem (BKT for general sets)
For $A \subset \mathbb{F}_p$ with $|A| = p^s$, $0 < s < 1$, and $X \subset A \times A$ with $|X| \ge |A|^{2-\eta}$, there exists $\theta$ such that $|\pi_\theta(X)| \ge |A|^{1/2+\epsilon}$.

## Statement 82: Theorem (BKT via BSG)
The Bourgain-Katz-Tao theorem can be proved using the Balog-Szemeredi-Gowers theorem to handle robust subsets of product sets.

## Statement 83: Theorem (Szemeredi-Trotter restated as incidence bound)
$I(P, L) \lesssim |P|^{2/3} |L|^{2/3} + |P| + |L|$.

## Statement 84: Proposition (BSG gives structured sumset)
If $E_+(A) \ge |A|^3/K$ (high additive energy), then there exist $A' \subset A$ with $|A'| \ge |A|/K$ and $|A' + A'| \le K^4|A'|$.

## Statement 85: Theorem (BKT refined statement)
If $X \subset \mathbb{F}_p^2$, $D \subset \mathbb{F}_p$, $|X| = p^{s_X}$, $|D| = p^{s_D}$, $0 < s_X, s_D < 1$, and $S = \max |\pi_\theta(X)|$, then $|D| \le C S^2/|X| \cdot p^\epsilon$.

## Statement 86: Theorem (BSG variant)
If $E_+(A, B) \ge |A||B|/K$, there exist $A' \subset A$, $B' \subset B$ with $|A'| \gtrsim |A|/K$ and $|A' + B'| \lesssim K^C |A'|$.

## Statement 87: Theorem (BKT 2 - robust version)
For $X \subset \mathbb{F}_p^2$, $D \subset \mathbb{F}_p$ with $|X| = p^{s_X}$, $|D| = p^{s_D}$, $0 < s_X, s_D < 1$, and $X'$ a large subset of $A_1 \times A_2$, there exists $\theta \in D$ with $|\pi_\theta(X')| \ge p^\epsilon |X'|^{1/2}$.

## Statement 88: Theorem (Balog-Szemeredi-Gowers)
If $A, B \subset G$ (abelian group) with $|A|, |B| \le N$ and $E_+(A, B) \ge N^2/K$, then there exist $A' \subset A$, $B' \subset B$ with $|A'|, |B'| \ge N/(2K)$ and $|A' + B'| \le (2K)^4 N$.

## Statement 89: Lemma (Graph lemma for BSG)
If $G$ is a bipartite graph between $A$ and $B$ with $|E(G)| \ge |A||B|/K$ edges, and the additive energy restricted to $G$ is large, then there exist dense subsets with small sumset.

## Statement 90: Lemma (Key Lemma for BSG)
If $x, y \in A$ are connected by many paths of length 2 in the graph $G$, then $x - y$ lies in a structured set.

## Statement 91: Lemma (Length 2 paths)
If the graph $G$ has many edges, then many pairs $(x, y)$ are connected by many paths of length 2.

## Statement 92: Lemma (P1 - Popularity argument)
In a bipartite graph with $M$ edges between sets of size $N$, there exist $\ge M/(2N)$ vertices each with $\ge M/(2N)$ neighbors.

## Statement 93: Lemma (P2 - Dependent random choice)
Given a graph $G$ with $|E| \ge |A||B|/K$, there exists $A' \subset A$ with $|A'| \ge |A|/(2K)$ such that most pairs in $A'$ share many common neighbors.

## Statement 94: Lemma (BSG counting argument)
For the BSG theorem, the number of representations of $a_1 - a_2$ as $b_1 - b_2$ with $(a_1, b_1), (a_2, b_2) \in G$ is at least $(M/N)^2/K^2$.

## Statement 95: Theorem (Bourgain-Katz-Tao, final version)
If $A \subset \mathbb{F}_p$ with $p^\delta \le |A| \le p^{1-\delta}$ for some $\delta > 0$, then $\max(|A+A|, |A \cdot A|) \ge |A|^{1+\epsilon}$ with $\epsilon = \epsilon(\delta) > 0$.

## Statement 96: Theorem (Bourgain projection theorem)
Given $0 < t < 2$, $0 < s \le 1$, there exist $\epsilon, \eta > 0$ such that if $X \subset B^2(0,1)$ is a $(\delta, t, \delta^{-\eta})_2$-set with $|X|_\delta = \delta^{-t}$ and $D \subset [0,1]$ is a $(\delta, s, \delta^{-\eta})_1$-set, then there exists $\theta \in D$ such that $|\pi_\theta(X')|_\delta \ge \delta^{-t/2-\epsilon}$ for every large subset $X' \subset X$.

## Statement 97: Lemma (Polynomial expansion, weak)
For each $s > 0$, there is a polynomial $Q$ and $\epsilon > 0$ such that if $A$ is a $(\delta, s, C)$-set, then $|Q(A)|_\delta \ge \delta^{-s-\epsilon}$.

## Statement 98: Lemma (Sum-product in continuous setting)
If $A$ is a $(\delta, s, C)$-set in $[0,1]$, then there exists $a \in A$ such that $|A + aA|_\delta \ge \delta^{-s-\epsilon}$.

## Statement 99: Theorem (Bourgain projection theorem, restated)
Given $0 < t < 2$, $0 < s \le 1$, there exist $\epsilon, \eta > 0$ such that the average projection of a $(\delta, t)$ set in the directions of a $(\delta, s)$ set has covering number at least $\delta^{-t/2-\epsilon}$.

## Statement 100: Lemma (Properties of non-concentrated sets)
If $X$ is a $(\delta, s, C)_d$-set then: (i) $|X|_\rho \ge C^{-1}\rho^{-s}$ for all $\rho \in [\delta, 1]$; (ii) if $Y \subset X$ and $|Y|_\delta \ge |X|_\delta / K$ then $Y$ is a $(\delta, s, CK)_1$-set.

## Statement 101: Lemma (Uniform set properties)
Let $X \subset [0,1]^d$ be a $(\Delta, m)$-uniform set and $\delta = \Delta^m$. (a) If $|X|_\rho \ge C^{-1}\rho^{-s}$ for $\rho \in \{1, \Delta, \ldots, \Delta^m\}$, then $X$ is a $(\delta, s, O_\Delta(C))$ set. (b) If $X$ is a $(\delta, s, C)$ set then $X$ is also $(\rho, s, O_\Delta(C))$ for all $\rho \in [\delta, 1]$.

## Statement 102: Lemma (Uniformization)
Let $\delta = \Delta^m$, $X \subset [0,1]^d$, $\mu$ a sub-additive set function. Then there exists $Y \subset X$ that is $(\Delta, m)$-uniform with $\mu(Y) \ge [2d\ln(1/\Delta)]^{-m}\mu(X)$.

## Statement 103: Lemma (Polynomial expansion, strong)
For each $s > 0$ and $\epsilon > 0$, there is a polynomial $P = P_{s,\epsilon}$ such that if $A$ is a $(\delta, s, C)$ set, then $|P(A)|_\delta \ge \delta^{-1+\epsilon}$.

## Statement 104: Lemma (Robust polynomial expansion)
There is a polynomial $Q: \mathbb{R}^k \to \mathbb{R}$ such that if $A$ is a $(\delta, s, C)$ set and $X \subset A^k$ with $|X|_\delta \gtrapprox |A^k|_\delta$, then $|Q(X)|_\delta \ge \delta^{-s-\epsilon}$.

## Statement 105: Lemma ($\|T_\mu f\|_{L^2} \le \|f\|_{L^2}$)
For a finite group $G$ and probability measure $\mu$ on $G$, $\|T_\mu f\|_{L^2} \le \|f\|_{L^2}$.

## Statement 106: Proposition ($L^2$ mixing bound)
$\|T_\mu^K \delta_{g_0} - 1/|G|\|_{L^2} \le |\sigma_1(T_\mu)|^K$ where $\sigma_1(T_\mu)$ is the largest singular value of $T_\mu$ on $L^2(G)_0$.

## Statement 107: Theorem (Selberg)
There exists a universal constant $c > 0$ such that for every prime $p$, $\sigma_1(T_{A_{\text{sel}}}) \le 1 - c$ for $A_{\text{sel}}$ the standard generators of $SL_2(\mathbb{F}_p)$.

## Statement 108: Proposition (Isoperimetric inequality from spectral gap)
If $S$ is a subset of $G$, then $|E(S, S^c)| \ge (1 - \sigma_1(T_A)) \frac{|A||S||S^c|}{|G|}$.

## Statement 109: Proposition (Minimal representation dimension of $SL_2(\mathbb{F}_p)$)
If $\rho: SL_2(\mathbb{F}_p) \to U(d)$ is a nontrivial representation, then $d \ge (p+1)/2$.

## Statement 110: Proposition ($\ell^2$ bound on $\sigma_1$)
Let $\mu$ be a measure on $SL_2(\mathbb{F}_p)$. Then $\sigma_1(T_\mu)^2 \cdot (p+1)/2 \le |SL_2(\mathbb{F}_p)| \cdot \|\mu\|_{L^2}^2$. In particular, $\sigma_1(T_\mu) \lesssim p\|\mu\|_{L^2}$.

## Statement 111: Corollary ($\sigma_1$ bound for uniform measures)
$\sigma_1(T_A)^2 \lesssim p^2/|A|$.

## Statement 112: Corollary (Proper subgroups of $SL_2(\mathbb{F}_p)$ are small)
If $H$ is a proper subgroup of $SL_2(\mathbb{F}_p)$, then $|H| \lesssim p^2$.

## Statement 113: Lemma ($T_\mu \mathbf{1} = \mathbf{1}$ and contraction)
$T_\mu \mathbf{1} = \mathbf{1}$, and $\|T_\mu f\|_{\ell^2(G)} \le \|f\|_{\ell^2(G)}$ for all $f \in \ell^2(G)$.

## Statement 114: Lemma (Mixing lemma, restated)
For any $K \in \mathbb{N}$, $\|T_\mu^K \delta_{g_0} - \frac{1}{|G|}\mathbf{1}\|_{\ell^2(G)} \le \sigma_1(T_\mu)^K$.

## Statement 115: Theorem (Selberg, restated)
There exists a universal constant $c > 0$ such that for every $p$, $\sigma_1(T_{A_{\text{sel}}}) \le 1 - c$.

## Statement 116: Lemma (Expansion from spectral gap, restated)
For any $S \subset G$, $|E(S, S^c)| \ge (1 - \sigma_1(T_A)) \frac{|A||S||S^c|}{|G|}$.

## Statement 117: Theorem ($\ell^2$-bound, restated)
There exists a universal constant $C > 0$ such that $\sigma_1(T_\mu)^2 \le Cp^2 \|\mu\|_{\ell^2(G)}^2$.

## Statement 118: Lemma (Representation dimension of $SL_2(\mathbb{F}_p)$, restated)
Let $\rho: G \to U(d)$ be a non-trivial representation of $G = SL_2(\mathbb{F}_p)$, then $d \ge (p-1)/2$.

## Statement 119: Lemma (Size of $B_T(\mathbb{Z})$)
For $T$ large, $|B_T(\mathbb{Z})| \approx T^2$ where $B_T$ is the ball of radius $T$ in $SL_2(\mathbb{R})$ and $B_T(\mathbb{Z}) = B_T \cap SL_2(\mathbb{Z})$.

## Statement 120: Lemma (Symmetric convolution and $L^2$ norm)
If $\mu$ is symmetric, then $\|\mu^{*K}\|_{\ell^2(G)}^2 = \mu^{*2K}(I)$.

## Statement 121: Lemma ($\Gamma_p \cap B_T(\mathbb{Z})$ counting)
For $T > p^2$, $|\Gamma_p \cap B_T(\mathbb{Z})| \lessapprox p^{-3} T^2$ where $\Gamma_p$ is the kernel of $\Pi_p: SL_2(\mathbb{Z}) \to SL_2(\mathbb{F}_p)$.

## Statement 122: Theorem (Hedlund, 1930s)
In $SL_2(\mathbb{R})/SL_2(\mathbb{Z})$, the orbit $U \cdot x$ of the unipotent group $U$ is either periodic or dense.

## Statement 123: Conjecture (Oppenheim)
If $n \ge 3$, the signature of $Q$ is mixed, and the coefficients of $Q$ are not contained in $\mathbb{Z}\alpha$ for any $\alpha$, then $Q(\mathbb{Z}^n)$ is dense in $\mathbb{R}$.

## Statement 124: Lemma (Projection estimate for orbits)
If $e^{2r} = \delta$, then $|X_{j+1}|_\delta \sim \delta^{-1} \text{Avg}_{0 \le t \le 1} |\pi_t X_j|_\delta$.

## Statement 125: Proposition (Average projection lower bound)
If $X \subset B_1^2$, then $\text{Avg}_{\theta \in S^1} |\pi_\theta X|_\delta \gtrsim |X|_\delta^{1/2}$.

## Statement 126: Corollary (Orbit spreading)
$|X_{j+1}|_\delta \gtrsim \delta^{-1} |X_j|_\delta^{1/2}$.

## Statement 127: Theorem (Gan-Guo-Guth-Harris-Maldague-Wang)
If $X \subseteq B^3$ is a $(\delta, 2, C)$ set and $\gamma$ is a non-degenerate curve in $S^2$, then $\text{Avg}_{\theta \in \gamma} |\pi_\theta(X)|_\delta \ge C_\epsilon \delta^{-2+\epsilon}$ for any $\epsilon > 0$.

## Statement 128: Theorem (Lindenstrauss-Mohammadi-Wang-Yang, vague)
There is a constant $c > 0$ such that if $G = SL(3, \mathbb{R})$, $\Gamma = SL(3, \mathbb{Z})$, $U$ as above and $U \cdot x$ is not close to a proper homogeneous subspace, then $U_{[0,T]}x$ is $T^{-c}$-dense in $G/\Gamma$.

## Statement 129: Theorem (Szemeredi-Trotter, 1982, restated for incidence bound)
Let $E$ be a set of points in $\mathbb{R}^2$. For every $x$ in $E$, let $L_x$ be a set of $S$ lines. Then $|L| \gtrsim \min(|E| \cdot S, |E|^{1/2} S^{3/2})$.

## Statement 130: Theorem (Furstenberg Conjecture, OSRW 2024)
Let $E \subset \mathbb{R}^2$ be a $(\delta, t, C)$ set. For every $x \in E$, let $\mathbb{T}_x$ be $\delta$-tubes with $\text{Dir}(\mathbb{T}_x)$ a $(\delta, s, C)$ subset of $S^1$. Then $|\mathbb{T}| \ge c_\epsilon C^{-O(1)} \delta^\epsilon \min(\delta^{-t-s}, \delta^{-t/2-3s/2}, \delta^{-1-s})$.

## Statement 131: Theorem (Orponen-Shmerkin, 2021)
Under the same hypotheses as the Furstenberg conjecture, for every $0 < s < t$ there is $\epsilon > 0$ such that $|\mathbb{T}| \gtrsim \delta^{-2s-\epsilon}$.

## Statement 132: Theorem (Beck's theorem)
Let $E$ be a set of points in $\mathbb{R}^2$ and for any line $\ell$, $|\ell \cap E| \le |E|/2$. Then for every $x \in E$, $|L_{x,E}| \gtrsim |E|$ where $L_{x,E}$ is the set of lines through $x$ hitting another point of $E$.

## Statement 133: Theorem (Continuum Beck's Theorem, OSW 2023)
Choose $\eta > 0$ and let $E$ be a $(\delta, u, C)$ set in the plane such that $|E \cap R|_\delta \le C\rho^\eta |E|_\delta$ for all $\rho \times 1$ rectangles $R$. Then for most $x \in E$, $|L_{x,E}|_\delta \gtrsim \delta^\epsilon \min(\delta^{-u}, \delta^{-1})$.

## Statement 134: Lemma (Epsilon improvement for continuum Beck)
If $0 < s < \min(u, 1)$ and a typical set $L_{x,E}$ is $(\delta, s, C)$, then $|L_{x,E}|_\delta \gtrsim \delta^{-s-\epsilon}$.

## Statement 135: Lemma (Bootstrap lemma)
If $0 < s < \min(u, 1)$ and a typical set $L_{x,E}$ is uniform and $(\delta, s, C)$, then a typical $L_{x,E}$ is $(\delta, s+\epsilon, C')$ where $\epsilon = \epsilon(s, u) > 0$.

## Statement 136: Theorem (OSRW, AD regular version restated)
If $E$ is $(\delta, t, C)$ and AD-regular, and $\mathbb{T}_x$ is $(\delta, s, C)$ uniform with $|\mathbb{T}_x| \sim \delta^{-s}$, then $|\mathbb{T}| \ge c_\epsilon \delta^\epsilon C^{-O(1)} \min(\delta^{-s-t}, \delta^{-t/2-3s/2}, \delta^{-1-s})$.

## Statement 137: Theorem (Orponen-Shmerkin, AD regular case)
$R_{AD}(s, t, \delta) \lessapprox \max(1, \delta^{-t/2}\delta^{s/2}, \delta^{1-t})$.

## Statement 138: Lemma (Submultiplicative Lemma)
If $\delta = \delta_1 \delta_2$ with $\delta_1, \delta_2 < 1$, then $R_{AD}(\delta) \lessapprox R_{AD}(\delta_1) R_{AD}(\delta_2)$.

## Statement 139: Lemma (Submultiplicative Lemma, projective version)
If $\delta = \delta_1 \delta_2$ with $\delta_1, \delta_2 < 1$, then $R_{AD,\text{proj}}(\delta) \lessapprox R_{AD,\text{proj}}(\delta_1) R_{AD,\text{proj}}(\delta_2)$.

## Statement 140: Lemma ($\epsilon$-improvement to submultiplicative lemma)
Fix $s, t$. For every $\alpha > 0$ there is $\epsilon > 0$ so that either $R_{AD,\text{proj}}(\delta^{1/2}) \lesssim \delta^{-\alpha} RHS$, or $R_{AD,\text{proj}}(\delta) \lesssim \delta^\epsilon R_{AD,\text{proj}}(\delta^{1/2})^2$.

## Statement 141: Theorem (ABC sum-product theorem, Orponen-Shmerkin)
Under the hypotheses that $A$ is $(\rho, a)$, $B$ is $(\rho, b)$, $C$ is $(\rho, c)$, and $|A + cB|_\rho \lessapprox |A|_\rho$ for all $c \in C$, then $a \ge b + c$.

## Statement 142: Theorem (Szemeredi-Trotter for $R$-rich lines)
If $E \subset \mathbb{R}^2$ is a set of $N$ points and $L_R(E)$ the set of $R$-rich lines, then $|L_R(E)| \lesssim N^2/R^3 + N/R$.

## Statement 143: Theorem (Guth-Solomon-Wang, well-spaced case)
Let $E \subset \mathbb{R}^2$ be $N$ well-spaced $\delta$-balls with $|E \cap B_{N^{-1/2}}|_\delta \lesssim 1$. Let $\mathbb{T}_R(E)$ be essentially distinct $\delta$-tubes with $|T \cap E|_\delta \ge R$ and $R > \delta^{-\epsilon}\delta|E|_\delta$. Then $|\mathbb{T}_R(E)| \lessapprox N^2/R^3$.

## Statement 144: Lemma (Two ends lemma)
Suppose $E$ is well-spaced, $T_\rho$ is a $\rho$-tube with $|T_\rho \cap E|_\rho \sim \tilde{R}$, and each $\delta$-tube obeys the two ends condition. Then $|\mathbb{T}_R(E, T_\rho)| \lesssim \tilde{R}^2/R^2$.

## Statement 145: Theorem (OSRW, full Furstenberg conjecture restated)
Let $E$ be a $(\delta, t)$ set, $\mathbb{T}_x$ a $(\delta, s)$ set of tubes. Then $R \lessapprox \max(1, \delta^{-s}\delta^{-t/2}, \delta^{1-t})$.

## Statement 146: Lemma (Branching function decomposition)
If $f: [0,1] \to \mathbb{R}$ is 2-Lipschitz, increasing with $f(1) = t$, $f(x) \ge tx$, and $s < t < 2-s$, then there is a decomposition $[0,1] = \bigsqcup I$ where on each interval $I$ either $f$ is almost linear with slope $t_I \in (s, 2-s)$, or $f$ is semi-well-spaced.
