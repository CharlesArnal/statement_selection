# All Extracted Statements from Design and Analysis of Algorithms (MIT 6.046J)

## Statement 1: Definition (Complexity Class P)
P is the class of problems solvable in polynomial time O(n^k) for some constant k. Example: Shortest paths in a graph O(V^2).

## Statement 2: Definition (Complexity Class NP)
NP is the class of problems verifiable in polynomial time. Given a certificate, one can verify the answer in polynomial time.

## Statement 3: Definition (NP-complete)
A problem is NP-complete if it is in NP and is as hard as any problem in NP. If any NP-complete problem can be solved in polynomial time, then every problem in NP has a polynomial-time solution.

## Statement 4: Definition (Hamiltonian Cycle)
A Hamiltonian cycle in a directed graph G(V,E) is a simple cycle that contains each vertex in V exactly once.

## Statement 5: Definition (Compatible Requests)
Two requests i and j are compatible if they don't overlap, i.e., f(i) < s(j) or f(j) < s(i), where s(i) is the start time and f(i) is the finish time.

## Statement 6: Claim (Greedy Interval Scheduling Output)
The greedy algorithm (earliest finish time) outputs a list of intervals $\langle s(i_1), f(i_1) \rangle, \langle s(i_2), f(i_2) \rangle, \ldots, \langle s(i_k), f(i_k) \rangle$ such that $s(i_1) < f(i_1) < s(i_2) < f(i_2) < \ldots < s(i_k) < f(i_k)$.

## Statement 7: Claim (Optimality of Greedy Interval Scheduling)
Given a list of intervals L, the greedy algorithm with earliest finish time produces k* intervals, where k* is optimal (maximum number of compatible intervals).

## Statement 8: Claim (Convex Hull Upper Tangent)
Given two convex hulls CH(A) and CH(B) separated by a vertical line L, (a_i, b_j) is an upper tangent if and only if it maximizes y(i,j), where y(i,j) is the y-coordinate of the intersection between L and the segment (a_i, b_j).

## Statement 9: Theorem (Convex Hull Divide and Conquer Complexity)
The divide-and-conquer algorithm for convex hull runs in O(n log n) time: T(n) = 2T(n/2) + O(n), which by the Master Theorem gives O(n log n).

## Statement 10: Definition (Rank)
Given a set of n numbers, rank(x) is defined as the number of elements in the set that are less than or equal to x.

## Statement 11: Theorem (Median Finding in Linear Time)
The median-of-medians selection algorithm finds the element of rank i in O(n) time. The recurrence T(n) = T(n/5) + T(7n/10) + O(n) solves to T(n) = O(n).

## Statement 12: Definition (Polynomial Representation)
A polynomial $A(x) = a_0 + a_1 x + a_2 x^2 + \cdots + a_{n-1} x^{n-1} = \sum_{k=0}^{n-1} a_k x^k$ can be represented as coefficients $\langle a_0, a_1, \ldots, a_{n-1} \rangle$.

## Statement 13: Definition (Polynomial Multiplication via Convolution)
For polynomials A(x) and B(x), the product C(x) = A(x) * B(x) has coefficients $C_k = \sum_{j=0}^{k} a_j b_{k-j}$ for $0 \le k \le 2(n-1)$.

## Statement 14: Theorem (FFT Complexity)
The Fast Fourier Transform evaluates a polynomial of degree n at n points (roots of unity) in O(n log n) time: T(n) = 2T(n/2) + O(n) = O(n log n).

## Statement 15: Theorem (Inverse DFT)
For the Vandermonde matrix V with entries $V_{jk} = \omega^{jk}$ where $\omega = e^{2\pi i/n}$, the inverse is $V^{-1} = \overline{V}/n$, i.e., $V \cdot \overline{V} = nI$.

## Statement 16: Theorem (Fast Polynomial Multiplication)
Polynomial multiplication C(x) = A(x) * B(x) can be computed in O(n log n) time using FFT: compute $A^* = \text{FFT}(A)$, $B^* = \text{FFT}(B)$, pointwise multiply $c_k^* = a_k^* \cdot b_k^*$, then $C = \text{IFFT}(C^*)$.

## Statement 17: Theorem (van Emde Boas Operations)
The van Emde Boas data structure supports Insert, Delete, and Successor operations in O(lg lg u) time, where u is the universe size.

## Statement 18: Claim (Table Doubling Amortized Cost)
Table doubling has O(1) amortized cost per insertion. The total cost over n insertions is $\Theta(2^0 + 2^1 + 2^2 + \cdots + 2^{\lceil \lg n \rceil}) = \Theta(n)$.

## Statement 19: Claim (2-3 Tree Amortized Splits)
In a 2-3 tree, insertions cause only O(1) amortized splits. Using the potential function $\Phi$ = number of nodes with 3 children, the amortized number of splits per insertion is at most 1.

## Statement 20: Claim (Binary Counter Amortized Increment)
Incrementing a binary counter has O(1) amortized cost per increment, using the potential function $\Phi = c \cdot$ (number of 1-bits in counter).

## Statement 21: Claim (Matrix Product Checker Correctness)
If $AB \neq C$, then $\Pr[ABr \neq Cr] \geq 1/2$ for a random binary vector r, where each $r_i = 1$ with probability 1/2 independently.

## Statement 22: Theorem (Randomized Quicksort Expected Time)
Randomized quicksort has expected running time O(n log n) for all input arrays A.

## Statement 23: Theorem ("Paranoid" Quicksort Analysis)
The "paranoid" quicksort satisfies the recurrence $T(n) \leq T(n/4) + T(3n/4) + 2cn$, giving O(n log n) expected runtime.

## Statement 24: Lemma (Skip List Levels)
The number of levels in an n-element skip list is O(lg n) with high probability (w.h.p.). Specifically, $\Pr\{> c \lg n \text{ levels}\} \leq n \cdot (1/2)^{c \lg n} = 1/n^{c-1}$.

## Statement 25: Theorem (Skip List Search Time)
Search in a skip list takes O(lg n) time with high probability.

## Statement 26: Theorem (Chernoff Bound)
Let Y be a random variable representing the total number of heads in a series of m independent coin flips, where each flip has probability p of heads. Then for all $r > 0$, $\Pr[Y \geq E[Y] + r] < e^{-2r^2/m}$.

## Statement 27: Definition (Universal Hash Family)
A hash family H is universal if for any two distinct keys $k \neq k'$: $\Pr_{h \in H}\{h(k) = h(k')\} \leq 1/m$, where m is the table size.

## Statement 28: Theorem (Universal Hashing Expected Collisions)
For n arbitrary distinct keys and random h from a universal hash family H with table size m: $E[\text{number of keys colliding in a slot}] \leq 1 + n/m$.

## Statement 29: Theorem (Dot-Product Hash Family is Universal)
The dot-product hash family $h_a(k) = (a \cdot k) \mod m$ (where m is prime and keys/hash values are represented in base m) is universal. For any $k \neq k'$: $\Pr_a\{h_a(k) = h_a(k')\} = 1/m$.

## Statement 30: Theorem (Perfect Hashing)
Perfect hashing (Fredman, Komlos, Szemeredi, 1984) achieves O(1) worst-case search time with O(n) space using a two-level hashing scheme with universal hash families. Build time is O(n lg n) w.h.p.

## Statement 31: Definition (Longest Palindromic Subsequence Recurrence)
$L(i,j) = \begin{cases} 1 & \text{if } i = j \\ 2 & \text{if } i+1=j \text{ and } X[i]=X[j] \\ 2 + L(i+1, j-1) & \text{if } X[i]=X[j] \\ \max(L(i+1,j), L(i,j-1)) & \text{otherwise} \end{cases}$

## Statement 32: Theorem (Optimal BST Recurrence)
For the optimal binary search tree problem: $e(i,j) = \begin{cases} w_i & \text{if } i=j \\ \min_{i \leq r \leq j}(e(i,r-1) + e(r+1,j) + w(i,j)) & \text{otherwise} \end{cases}$ with complexity $\Theta(n^3)$.

## Statement 33: Theorem (Alternating Coin Game Value)
$V(i,j) = \max\{V_i + \min\{V(i+1,j-1), V(i+2,j)\}, V_j + \min\{V(i,j-2), V(i+1,j-1)\}\}$ with complexity $\Theta(n^2)$.

## Statement 34: Theorem (Bellman-Ford Shortest Paths)
Single-source shortest paths with general edge weights can be solved by Bellman-Ford in O(VE) time. If no negative-weight cycles exist, then the shortest path is simple, and $\delta(u,v) = d^{(|V|-1)}_{uv}$.

## Statement 35: Theorem (Floyd-Warshall All-Pairs Shortest Paths)
The Floyd-Warshall algorithm solves all-pairs shortest paths in O(V^3) time using the recurrence $c^{(k)}_{ij} = \min(c^{(k-1)}_{ij}, c^{(k-1)}_{ik} + c^{(k-1)}_{kj})$.

## Statement 36: Theorem (Johnson's Algorithm)
Johnson's algorithm solves all-pairs shortest paths in O(VE + V^2 lg V) time for general weights by reweighting edges using Bellman-Ford and then running Dijkstra from each vertex.

## Statement 37: Claim (Negative-Weight Cycle Detection)
If there exists a negative-weight cycle, then $d^{(n)}_{uv} < d^{(n-1)}_{uv}$ for some u, v.

## Statement 38: Theorem (LP Duality - Weak Duality)
For a linear program and its dual: the value of any feasible solution to the dual provides a bound on the optimal value of the primal. The feasible region is a convex polytope and the optimum is at a vertex.

## Statement 39: Theorem (LP Duality - Strong Duality)
If a linear program has an optimal solution, then so does its dual, and their optimal values are equal.

## Statement 40: Definition (NP-hardness via Reduction)
Problem X is NP-hard if every problem in NP can be reduced to X in polynomial time. If X is also in NP, then X is NP-complete.

## Statement 41: Definition (Polynomial-time Reduction)
A polynomial-time reduction from problem Y to problem X requires: (A) a poly-time conversion from Y inputs to X inputs, and (B) if Y's answer is YES then X's answer is YES, and vice versa.

## Statement 42: Theorem (3-Dimensional Matching is NP-complete)
3-Dimensional Matching (3DM) is NP-complete, by reduction from 3SAT.

## Statement 43: Theorem (Subset Sum is NP-complete)
Subset Sum is weakly NP-hard by reduction from 3DM. It has a pseudopolynomial algorithm via dynamic programming.

## Statement 44: Theorem (4-Partition is Strongly NP-hard)
4-Partition is strongly NP-hard by reduction from 3DM. It remains NP-hard even when number values are polynomial in n.

## Statement 45: Definition (Approximation Ratio)
An algorithm has approximation ratio $\rho(n)$ if for any input, it produces a solution of cost C such that $\max(C/C_{\text{opt}}, C_{\text{opt}}/C) \leq \rho(n)$.

## Statement 46: Definition (PTAS and FPTAS)
A polynomial-time approximation scheme (PTAS) is polynomial in n for any fixed $\varepsilon$. A fully PTAS (FPTAS) is polynomial in both n and $1/\varepsilon$.

## Statement 47: Theorem (2-Approximation for Vertex Cover)
The greedy algorithm that repeatedly picks both endpoints of an arbitrary edge is a 2-approximation algorithm for vertex cover. Proof: Let A be the edges picked. $|C_{\text{opt}}| \geq |A|$ and $|C| = 2|A|$, so $|C| \leq 2|C_{\text{opt}}|$.

## Statement 48: Theorem (Set Cover Approximation)
The greedy set cover algorithm (always pick the largest remaining set) is a $(\ln n + 1)$-approximation algorithm.

## Statement 49: Theorem (PTAS for Partition)
The Approx-Partition algorithm achieves approximation ratio $w(A)/L \leq 1 + 1/(m+1)$ where $m = \lceil 1/\varepsilon \rceil - 1$, giving a $(1+\varepsilon)$-approximation (PTAS).

## Statement 50: Definition (Fixed-Parameter Tractability)
A parameterized problem is fixed-parameter tractable (FPT) if there is an algorithm with running time $f(k) \cdot n^{O(1)}$, where k is the parameter and f is any computable function.

## Statement 51: Theorem (FPT Equivalence)
$f(k) \cdot n^{O(1)}$ algorithm exists if and only if $f(k) + n^c$ algorithm exists for some constant c.

## Statement 52: Theorem (Bounded Search Tree for Vertex Cover)
The bounded search tree algorithm solves k-vertex cover in $O(2^k \cdot V)$ time, which is FPT.

## Statement 53: Theorem (FPT implies Kernelization)
A parameterized problem is FPT if and only if it has a kernelization (polynomial-time reduction to an equivalent instance of size bounded by a function of k alone).

## Statement 54: Theorem (Optimization to Decision for EPTAS)
An optimization problem has an efficient PTAS (EPTAS, with $f(1/\varepsilon) \cdot n^{O(1)}$ time) if and only if the associated decision problem is FPT.

## Statement 55: Theorem (Fermat's Little Theorem)
For prime p and integer m with gcd(m,p) = 1: $m^{p-1} \equiv 1 \pmod{p}$.

## Statement 56: Theorem (RSA Correctness)
In RSA, if $ed \equiv 1 \pmod{(p-1)(q-1)}$ and $N = pq$, then $m^{ed} \equiv m \pmod{N}$ for all messages m. This follows from Fermat's Little Theorem applied modulo p and modulo q, combined via the Chinese Remainder Theorem.

## Statement 57: Definition (Cryptographic Hash Function Properties)
A cryptographic hash function $h: \{0,1\}^* \to \{0,1\}^d$ should satisfy: (1) One-wayness (OW): infeasible to find preimage, (2) Collision resistance (CR): infeasible to find $x \neq x'$ with $h(x) = h(x')$, (3) Target collision resistance (TCR): given x, infeasible to find $x' \neq x$ with $h(x) = h(x')$.

## Statement 58: Proposition (Collision Resistance Implies TCR)
If h is collision-resistant (CR), then h is target collision-resistant (TCR), but not conversely.

## Statement 59: Proposition (Birthday Attack Complexity)
Collisions in a hash function with d-bit output can be found in $O(2^{d/2})$ time (birthday attack). Inversion requires $O(2^d)$ time.

## Statement 60: Theorem (Diffie-Hellman Key Exchange)
In Diffie-Hellman, Alice computes $(g^b)^a \mod p = g^{ab} \mod p$ and Bob computes $(g^a)^b \mod p = g^{ab} \mod p$, so both obtain the same shared key $K = g^{ab} \mod p$. Security relies on the hardness of the Discrete Logarithm Problem.

## Statement 61: Definition (Graph Coloring)
Given a graph G, a k-coloring assigns one of k colors to each vertex such that no two adjacent vertices share the same color. The decision problem "Is G k-colorable?" is NP-complete for $k \geq 3$.

## Statement 62: Theorem (LRU Block Replacement Optimality)
LRU (Least Recently Used) with cache size M achieves at most twice the memory transfers of OPT (the optimal offline algorithm) with cache size M/2. This is proven via resource augmentation (Sleator, Tarjan, 1985).

## Statement 63: Theorem (B-tree Search Complexity in External Memory)
B-trees support search in $O(\log_B N)$ memory transfers, where B is the block size and N is the number of elements. Each node occupies O(1) blocks, and the height is $\Theta(\log_B N)$.

## Statement 64: Theorem (Cache-Oblivious Sorting)
Merge sort in the cache-oblivious model achieves $O(\frac{N}{B} \log_{M/B} \frac{N}{B})$ memory transfers, which is optimal.
