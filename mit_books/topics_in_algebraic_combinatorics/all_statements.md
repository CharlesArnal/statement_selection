# All Mathematical Statements: Topics in Algebraic Combinatorics

## Statement 1
**Lemma 8.1.** Suppose $w = D^{s_k}U^{r_k} \cdots D^{s_2}U^{r_2}D^{s_1}U^{r_1}$, where $r_i \geq 0$ and $s_i \geq 0$. Let $\lambda \vdash n$. Then there exists a Hasse walk of type w from $\emptyset$ to $\lambda$ if and only if:

$$\sum_{i=1}^{k} (r_i - s_i) = n$$

$$\sum_{i=1}^{j} (r_i - s_i) \ge 0 \text{ for } 1 \le j \le k.$$

## Statement 2
**Lemma 8.2.** For any $i \ge 0$ we have

$$D_{i+1}U_i - U_{i-1}D_i = I_i,$$

the identity linear transformation on $\mathbb{R}Y_i$.

## Statement 3
**Theorem 8.3.** Let $\lambda$ be a partition and $w = A_n A_{n-1} \cdots A_1$ a valid $\lambda$-word. Let $S_w = \{i : A_i = D\}$. For each $i \in S_w$, let $a_i$ be the number of D's in w to the right of $A_i$, and let $b_i$ be the number of U's in w to the right of $A_i$. Then

$$\alpha(w,\lambda) = f^{\lambda} \prod_{i \in S_w} (b_i - a_i).$$

## Statement 4
**Corollary 8.4.** We have

$$\alpha(D^nU^n,\emptyset) = \sum_{\lambda \vdash n} (f^{\lambda})^2 = n!$$

## Statement 5
**Lemma 8.5.** We have $b_{ij}(\ell) = 0$ if $\ell - i - j$ is odd. If $\ell - i - j = 2m$ then

$$b_{ij}(\ell) = \frac{\ell!}{2^m i! j! m!}.$$

## Statement 6
**Theorem 8.6.** Let $\ell \geq n$ and $\lambda \vdash n$, with $\ell - n$ even. Then

$$\beta(\ell,\lambda) = \binom{\ell}{n} (1 \cdot 3 \cdot 5 \cdots (\ell-n-1)) f^{\lambda}.$$

## Statement 7
**Corollary 8.7.** The total number of Hasse walks in Y of length 2m from $\emptyset$ to $\emptyset$ is given by

$$\beta(2m, \emptyset) = 1 \cdot 3 \cdot 5 \cdots (2m - 1).$$

## Statement 8
**Theorem 8.8.** The eigenvalues of $Y_{j-1,j}$ are given as follows: 0 is an eigenvalue of multiplicity p(j) - p(j-1); and for $1 \le s \le j$, the numbers $\pm \sqrt{s}$ are eigenvalues of multiplicity p(j-s) - p(j-s-1).

## Statement 9
**Corollary 8.9.** Fix $j \geq 1$. The number of ways to choose a partition $\lambda$ of j, then delete a square from $\lambda$ (keeping it a partition), then insert a square, then delete a square, etc., for a total of m insertions and m deletions, ending back at $\lambda$, is given by

$$\sum_{s=1}^{j} [p(j-s) - p(j-s-1)]s^{m}, \ m > 0.$$

## Statement 10
**Proposition 4.4.** Let P be a graded poset of rank n. Suppose there exists an integer $0 \le j \le n$ and order-matchings

$$P_0 \to P_1 \to P_2 \to \cdots \to P_j \leftarrow P_{j+1} \leftarrow P_{j+2} \leftarrow \cdots \leftarrow P_n.$$

Then P is rank-unimodal and Sperner.

## Statement 11
**Lemma 4.5.** Suppose there exists a linear transformation $U : \mathbb{R}P_i \to \mathbb{R}P_{i+1}$ (U stands for "up") satisfying:

- U is one-to-one.
- For all $x \in P_i$, U(x) is a linear combination of elements $y \in P_{i+1}$ satisfying x < y. (We then call U an order-raising operator.)

Then there exists an order-matching $\mu: P_i \to P_{i+1}$.

Similarly, suppose there exists a linear transformation $U: \mathbb{R}P_i \to \mathbb{R}P_{i+1}$ satisfying:

- U is onto.
- U is an order-raising operator.

Then there exists an order-matching $\mu: P_{i+1} \to P_i$.

## Statement 12
**Lemma 4.6.** Let $0 \le i \le n$. Then

$$D_{i+1}U_i - U_{i-1}D_i = (n-2i)I_i.$$

## Statement 13
**Theorem 4.7.** The operator $U_i$ defined above is one-to-one if i < n/2 and is onto if $i \ge n/2$.

## Statement 14
**Corollary 4.8.** The boolean algebra $B_n$ has the Sperner property.

## Statement 15
**Proposition 5.6.** The quotient poset $B_n/G$ defined above is graded of rank n and rank-symmetric.

## Statement 16
**Lemma 5.7.** A basis for $\mathbb{R}(B_n)_i^G$ consists of the elements

$$v_{\mathcal{O}} := \sum_{x \in \mathcal{O}} x,$$

where $\mathcal{O} \in (B_n)_i/G$, the set of G-orbits for the action of G on $(B_n)_i$.

## Statement 17
**Lemma 5.8.** If $v \in \mathbb{R}(B_n)_i^G$, then $U_i(v) \in \mathbb{R}(B_n)_{i+1}^G$.

## Statement 18
**Theorem 5.9.** Let G be a subgroup of $\mathfrak{S}_n$. Then the quotient poset $B_n/G$ is graded of rank n, rank-symmetric, rank-unimodal, and Sperner.

## Statement 19
**Theorem 5.10.** (a) Fix $m \ge 1$. Let $p_i$ be the number of nonisomorphic simple graphs with m vertices and i edges. Then the sequence $p_0, p_1, \ldots, p_{\binom{m}{2}}$ is symmetric and unimodal.

(b) Let T be a collection of nonisomorphic simple graphs with m vertices such that no element of T is isomorphic to a subset of another element of T. Then |T| is maximized by taking T to consist of all nonisomorphic simple graphs with $\lfloor \frac{1}{2} {m \choose 2} \rfloor$ edges.

## Statement 20
**Conjecture (Circulant Hadamard).** Let H be an $n \times n$ circulant Hadamard matrix. Then n = 1 or n = 4.

## Statement 21
**Theorem 1.** There does not exist a circulant Hadamard matrix H of order $2^k$, k > 3.

## Statement 22
**Lemma 2.** The polynomial $p_k(x) = x^{2^{k-1}}+1$ is irreducible over $\mathbb{Q}$.

## Statement 23
**Lemma 3.** For $0 \le j \le n-1$ we have

$$|\gamma_j| = \sqrt{n}.$$

Thus all the factors appearing on the left-hand side of (3) have absolute value $\sqrt{n}$.

## Statement 24
**Lemma 4.** We have

$$2 = (1 - \zeta)^{n/2} u,$$

where u is a unit in $\mathbb{Z}[\zeta]$.

## Statement 25
**Lemma 5.** We have $\mathbb{Z}[\zeta]/(1-\zeta) \cong \mathbb{F}_2$.

## Statement 26
**Lemma 6.** For all $0 \le j \le n-1$ there is an integer $h_j \ge 0$ such that

$$a_0 + a_1 \zeta^j + a_2 \zeta^{2j} + \dots + a_{n-1} \zeta^{(n-1)j} = v_j (1 - \zeta)^{h_j},$$

where $v_j$ is a unit in $\mathbb{Z}[\zeta]$.

## Statement 27
**Corollary 7.** Either $\gamma_0/\gamma_1 \in \mathbb{Z}[\zeta]$ or $\gamma_1/\gamma_0 \in \mathbb{Z}[\zeta]$.

## Statement 28
**Lemma 8.** Let $\theta$ be an algebraic integer such that $\theta$ and all its conjugates have absolute value one. Then $\theta$ is a root of unity.

## Statement 29
**Theorem 9 (Kronecker).** Let $\tau$ be any root of unity and $\alpha \in \mathbb{Q}[\tau]$ with $|\alpha| = 1$. Then $\alpha$ is a root of unity.

## Statement 30
**Proposition 6.2.** L(m,n) is graded of rank mn and rank-symmetric. The rank of a partition $\lambda$ is just $|\lambda|$ (the sum of the parts of $\lambda$ or the number of squares in its Young diagram).

## Statement 31
**Proposition 6.3.** We have $|L(m,n)| = {m+n \choose m}$.

## Statement 32
**Lemma 6.5.** We have

$$\begin{bmatrix} k \\ j \end{bmatrix} = \begin{bmatrix} k-1 \\ j \end{bmatrix} + q^{k-j} \begin{bmatrix} k-1 \\ j-1 \end{bmatrix}$$

whenever $k \geq 1$, with the "initial conditions" $\begin{bmatrix} 0 \\ 0 \end{bmatrix} = 1$, $\begin{bmatrix} k \\ j \end{bmatrix} = 0$ if j < 0 or j > k.

## Statement 33
**Theorem 6.6.** Let $p_i(m, n)$ denote the number of elements of L(m, n) of rank i. Then

$$\sum_{i>0} p_i(m,n)q^i = \begin{bmatrix} m+n\\m \end{bmatrix}.$$

## Statement 34
**Lemma 6.8.** Every orbit $\mathcal{O}$ of the action of $G_{mn}$ on $B_R$ contains exactly one Young diagram D (i.e., exactly one subset $D \subseteq R$ such that D is left-justified, and if $\lambda_i$ is the number of elements of D in row i of R, then $\lambda_1 \geq \lambda_2 \geq \cdots \geq \lambda_m$).

## Statement 35
**Theorem 6.9.** The quotient poset $B_{R_{mn}}/G_{mn}$ is isomorphic to L(m,n).

## Statement 36
**Corollary 6.10.** The posets L(m, n) are rank-symmetric, rank-unimodal, and Sperner.

## Statement 37
**Theorem 6.11.** Let $S \in {\mathbb{R}^+ \choose n}$, $\alpha \in \mathbb{R}^+$, and $k \in \mathbb{P}$. Then $f_k(S, \alpha) \leq f_k([n], \lfloor k(n+1)/2 \rfloor)$.
