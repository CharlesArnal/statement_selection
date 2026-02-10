# All Mathematical Statements from Mathematics for Computer Science

## Statement 1: Proposition 1.1.1
2 + 3 = 5.

## Statement 2: Proposition 1.1.2
1 + 1 = 3.

## Statement 3: Proposition 1.1.3
For every nonnegative integer, n, the value of n^2 + n + 41 is prime.

## Statement 4: Proposition 1.1.4 (Euler's Conjecture)
The equation a^4 + b^4 + c^4 = d^4 has no solution when a, b, c, d are positive integers.

## Statement 5: Proposition 1.1.5
313(x^3 + y^3) = z^3 has no solution when x, y, z are positive integers.

## Statement 6: Proposition 1.1.6 (Four Color Theorem)
Every map can be colored with 4 colors so that adjacent regions have different colors.

## Statement 7: Proposition 1.1.7 (Fermat's Last Theorem)
There are no positive integers x, y, and z such that x^n + y^n = z^n for some integer n > 2.

## Statement 8: Proposition 1.1.8 (Goldbach's Conjecture)
Every even integer greater than 2 is the sum of two primes.

## Statement 9: Theorem 1.5.1
If 0 < x < 2, then -x^3 + 4x + 1 > 0.

## Statement 10: Theorem 1.5.2
If r is irrational, then sqrt(r) is also irrational.

## Statement 11: Theorem 1.6.1
The standard deviation of a sequence of values x_1, ..., x_n is zero iff all the values are equal to the mean.

## Statement 12: Theorem 1.8.1
sqrt(2) is irrational.

## Statement 13: Theorem 2.2.1
For any b in Z and any a in Z+, there exist unique integers q, r in N such that b = qa + r and 0 <= r < a.

## Statement 14: Theorem 2.3.1
Every positive integer greater than one can be factored as a product of primes.

## Statement 15: Theorem 2.4.1
For any nonnegative integer, n, the set of integers greater than or equal to -n is well ordered.

## Statement 16: Corollary 2.4.3
Any set of integers with a lower bound is well ordered.

## Statement 17: Corollary 2.4.4
Any nonempty set of integers with an upper bound has a maximum element.

## Statement 18: Lemma 2.4.5
N + F is well ordered (where F is a well ordered set under <=).

## Statement 19: Theorem 3.4.1 (Distributive Law of AND over OR)
P AND (Q OR R) = (P AND Q) OR (P AND R).

## Statement 20: Theorem 3.4.2 (Distributive Law of OR over AND)
P OR (Q AND R) = (P OR Q) AND (P OR R).

## Statement 21: Theorem 3.4.3
Every propositional formula is equivalent to both a disjunctive normal form and a conjunctive normal form.

## Statement 22: Theorem 4.1.1
For all nonnegative integers n: 1 + 2 + 3 + ... + n = n(n+1)/2.

## Statement 23: Theorem 4.1.2
For all n in N, 3 | (n^3 - n).

## Statement 24: Theorem 4.1.3 (Geometric Sum)
For all n in N and all z != 1: 1 + z + z^2 + ... + z^n = (z^(n+1) - 1)/(z - 1).

## Statement 25: Theorem 4.5.1
Every postage of n >= 8 cents can be made using 3-cent and 5-cent stamps.

## Statement 26: Theorem 4.5.2
All horses are the same color.

## Statement 27: Theorem 5.1.1 (Ordinary Induction)
Let P be a predicate on nonneg integers. If P(0) is true, and P(n) IMPLIES P(n+1) for all n in N, then P(m) is true for all m in N.

## Statement 28: Theorem 5.1.2 (Complete Induction or Strong Induction)
Let P be a predicate on nonneg integers. If for each n in N, P(0), P(1), ..., P(n) together imply P(n+1), then P(m) is true for all m in N.

## Statement 29: Theorem 5.3.1
Every positive integer is a product of a unique nondecreasing sequence of primes.

## Statement 30: Lemma 5.3.2
If p is a prime and p | ab, then p | a or p | b.

## Statement 31: Lemma 5.3.3
If p is a prime and p | a_1 * a_2 * ... * a_n, then p | a_i for some i.

## Statement 32: Theorem 7.2.1
If |A| <= |B| and |B| <= |A|, then |A| = |B|. (Schroeder-Bernstein)

## Statement 33: Theorem 7.2.2 (Cantor's Theorem)
For every set A (finite or infinite), |A| < |pow(A)|.

## Statement 34: Theorem 7.2.3
pow(N) is uncountable.

## Statement 35: Corollary 7.2.4
R is uncountable.

## Statement 36: Theorem 8.1.1 (GCD Linear Combination)
The greatest common divisor of a and b is a linear combination of a and b. That is, gcd(a,b) = sa + tb for some integers s and t.

## Statement 37: Lemma 8.1.2
gcd(a, b) = gcd(rem(a, b), b).

## Statement 38: Theorem 8.1.3
The Euclidean algorithm terminates on all valid inputs, and gcd(a,b) = gcd(rem(a,b), b).

## Statement 39: Corollary 8.1.4
An integer is a linear combination of a and b iff it is a multiple of gcd(a,b).

## Statement 40: Lemma 8.2.1 (Prime Divisibility)
If p is a prime and p | ab, then p | a or p | b.

## Statement 41: Theorem 8.2.2 (Fundamental Theorem of Arithmetic)
Every positive integer n can be written in a unique way as a product of primes: n = p_1 * p_2 * ... * p_j where p_1 <= p_2 <= ... <= p_j.

## Statement 42: Lemma 8.3.1
If a | bc and gcd(a, b) = 1, then a | c.

## Statement 43: Corollary 8.3.2
If p is prime and p does not divide a, then gcd(p, a) = 1.

## Statement 44: Theorem 8.3.3
If gcd(a, b) = 1 and gcd(a, c) = 1, then gcd(a, bc) = 1.

## Statement 45: Lemma 8.3.4
Let p be a prime. If p | a_1 * a_2 * ... * a_n, then p | a_i for some 1 <= i <= n.

## Statement 46: Theorem 8.4.1
For any prime p that does not divide n, n^(p-1) === 1 (mod p). (Fermat's Little Theorem)

## Statement 47: Corollary 8.4.2
phi(p) = p - 1 for prime p, where phi is Euler's totient function.

## Statement 48: Theorem 8.4.3 (Euler's Theorem)
If gcd(n, p) = 1, then n^(phi(p)) === 1 (mod p), where phi is Euler's totient function.

## Statement 49: Theorem 8.5.1 (Chinese Remainder Theorem)
If gcd(n_1, n_2) = 1, then for all m_1 and m_2, there exists a unique x in {0, 1, ..., n_1*n_2 - 1} such that x === m_1 (mod n_1) and x === m_2 (mod n_2).

## Statement 50: Corollary 8.5.2
phi(n_1 * n_2) = phi(n_1) * phi(n_2), when gcd(n_1, n_2) = 1.

## Statement 51: Lemma 8.5.3
phi(p^k) = p^k - p^(k-1) for prime p and k >= 1.

## Statement 52: Theorem 8.6.1 (RSA)
For all m in {0, 1, ..., p*q - 1}, m^(ed) === m (mod pq), where e*d === 1 (mod (p-1)(q-1)).

## Statement 53: Theorem 9.4.1
If a DAG has a positive number of vertices, then it has a source (a vertex with no incoming edges).

## Statement 54: Theorem 9.6.1
The largest antichain in a finite partially ordered set equals the minimum number of chains needed to partition the set. (Dilworth's Theorem)

## Statement 55: Theorem 10.7.1
The congestion of an N-input array is 2.

## Statement 56: Theorem 10.9.1
The congestion of the N-input Benes network is 1.

## Statement 57: Lemma 10.9.2
If the edges of a graph can be grouped into two sets such that every vertex has at most 1 edge from each set incident to it, then the graph is 2-colorable.

## Statement 58: Lemma 11.2.1 (Handshaking Lemma)
The sum of the degrees of the vertices in a graph equals twice the number of edges.

## Statement 59: Theorem 11.5.2 (Hall's Marriage Theorem)
A matching for a set M of men with a set W of women can be found if and only if the matching condition holds (every subset of men likes at least as large a set of women).

## Statement 60: Theorem 11.5.4 (Hall's Theorem)
Let G be a bipartite graph. There is a matching in G that covers L(G) iff no subset of L(G) is a bottleneck.

## Statement 61: Theorem 11.5.6
If G is a degree-constrained bipartite graph, then there is a matching that covers L(G).

## Statement 62: Theorem 11.5.8
Every regular bipartite graph has a perfect matching.

## Statement 63: Theorem 11.6.4
Everyone is married at the end of the Mating Ritual.

## Statement 64: Theorem 11.6.5
The Mating Ritual produces a stable matching.

## Statement 65: Lemma 11.6.8
Q is a preserved invariant for The Mating Ritual (where Q states: for every woman w and man m, if w is crossed off m's list, then w is not a feasible spouse for m).

## Statement 66: Theorem 11.6.10
The Mating Ritual marries every man to his optimal spouse and every woman to her pessimal spouse.

## Statement 67: Lemma 11.7.2
A graph G with at least one edge is bipartite iff chi(G) = 2.

## Statement 68: Theorem 11.7.3
A graph with maximum degree at most k is (k + 1)-colorable.

## Statement 69: Theorem 11.9.3
The following graph properties are equivalent: (1) The graph contains an odd length cycle. (2) The graph is not 2-colorable. (3) The graph contains an odd length closed walk.

## Statement 70: Lemma 11.9.6
An edge is a cut edge iff it is not on a cycle.

## Statement 71: Theorem 11.9.7
Every graph G has at least |V(G)| - |E(G)| connected components.

## Statement 72: Theorem 11.10.3
Every tree has the following properties: (1) Every connected subgraph is a tree. (2) There is a unique path between every pair of vertices. (3) Adding an edge between nonadjacent nodes creates a cycle. (4) Removing any edge disconnects the graph (every edge is a cut edge). (5) If the tree has at least two vertices, then it has at least two leaves. (6) The number of vertices in a tree is one larger than the number of edges.

## Statement 73: Lemma 11.10.4
A graph G is a tree iff G is a forest and |V(G)| = |E(G)| + 1.

## Statement 74: Theorem 11.10.6
Every connected graph contains a spanning tree.

## Statement 75: Lemma 11.10.11
An edge extends a pre-MST F if it is a minimum weight gray edge in some solid coloring of F.

## Statement 76: Corollary 11.10.12
If all edges in a weighted graph have distinct weights, then the graph has a unique MST.

## Statement 77: Theorem 12.3.1 (Euler's Formula)
If a connected graph has a planar embedding, then v - e + f = 2 where v is the number of vertices, e is the number of edges, and f is the number of faces.

## Statement 78: Lemma 12.4.1
In a planar embedding of a connected graph, each edge occurs once in each of two different faces, or occurs exactly twice in one face.

## Statement 79: Lemma 12.4.2
In a planar embedding of a connected graph with at least three vertices, each face is of length at least three.

## Statement 80: Theorem 12.4.3
Suppose a connected planar graph has v >= 3 vertices and e edges. Then e <= 3v - 6.

## Statement 81: Corollary 12.5.1
K_5 is not planar.

## Statement 82: Lemma 12.5.2
In a planar embedding of a connected bipartite graph with at least 3 vertices, each face has length at least 4.

## Statement 83: Theorem 12.5.3
Suppose a connected bipartite graph with v >= 3 vertices and e edges is planar. Then e <= 2v - 4.

## Statement 84: Corollary 12.5.4
K_{3,3} is not planar.

## Statement 85: Lemma 12.6.1
Any subgraph of a planar graph is planar.

## Statement 86: Lemma 12.6.2
Merging two adjacent vertices of a planar graph leaves another planar graph.

## Statement 87: Lemma 12.6.3
Every planar graph has a vertex of degree at most five.

## Statement 88: Theorem 12.6.4
Every planar graph is five-colorable.

## Statement 89: Theorem 13.1.1
If |x| < 1, then sum_{i=0}^{infinity} x^i = 1/(1-x).

## Statement 90: Theorem 13.1.2
If |x| < 1, then sum_{i=1}^{infinity} i*x^i = x/(1-x)^2.

## Statement 91: Theorem 13.3.2
Let f: R+ -> R+ be a weakly increasing function. Define S := sum_{i=1}^{n} f(i) and I := integral_1^n f(x) dx. Then I + f(1) <= S <= I + f(n). Similarly, if f is weakly decreasing, then I + f(n) <= S <= I + f(1).

## Statement 92: Theorem 13.5.1 (Stirling's Formula)
For all n >= 1, n! = sqrt(2*pi*n) * (n/e)^n * e^{epsilon(n)} where 1/(12n+1) <= epsilon(n) <= 1/(12n).

## Statement 93: Corollary 13.5.2
n! < sqrt(2*pi*n) * (n/e)^n * 1.09 for n >= 1; * 1.009 for n >= 10; * 1.0009 for n >= 100.

## Statement 94: Lemma 13.7.2
x^a = o(x^b) for all nonnegative constants a < b.

## Statement 95: Lemma 13.7.3
log x = o(x^epsilon) for all epsilon > 0.

## Statement 96: Corollary 13.7.4
x^b = o(a^x) for any a, b in R with a > 1.

## Statement 97: Lemma 13.7.6
If a function f: R -> R has a finite or infinite limit as its argument approaches infinity, then its limit and limit superior are the same.

## Statement 98: Lemma 13.7.7
If f = o(g) or f ~ g, then f = O(g).

## Statement 99: Lemma 13.7.8
If f = o(g), then it is not true that g = O(f).

## Statement 100: Lemma 14.1.1
The number of ways to select n donuts when k flavors are available is the same as the number of binary sequences with exactly n zeroes and k-1 ones.

## Statement 101: Lemma 14.10.1 (Pascal's Triangle Identity)
C(n, k) = C(n-1, k-1) + C(n-1, k).

## Statement 102: Theorem 14.10.2
sum_{r=0}^{n} C(n, r) * C(2n, n-r) = C(3n, n).

## Statement 103: Corollary 14.5.2
The number of n-bit sequences with exactly k ones is C(n, k).

## Statement 104: Corollary 14.5.3
The number of ways to select n donuts when k flavors are available is C(n+(k-1), n).

## Statement 105: Theorem 14.6.4 (Binomial Theorem)
For all n in N and a, b in R: (a+b)^n = sum_{k=0}^{n} C(n,k) * a^{n-k} * b^k.

## Statement 106: Theorem 14.6.5 (Multinomial Theorem)
For all n in N, (z_1 + z_2 + ... + z_m)^n = sum_{k_1+...+k_m=n} C(n; k_1,...,k_m) * z_1^{k_1} * ... * z_m^{k_m}.

## Statement 107: Lemma 15.3.1
Let p(x) be a polynomial of degree less than n and let alpha_1, ..., alpha_n be distinct, nonzero numbers. Then there are constants c_1, ..., c_n such that p(x)/((1-alpha_1*x)...(1-alpha_n*x)) = c_1/(1-alpha_1*x) + ... + c_n/(1-alpha_n*x).

## Statement 108: Theorem 17.4.1 (Bayes' Rule)
Pr[B | A] = Pr[A | B] * Pr[B] / Pr[A].

## Statement 109: Theorem 19.1.1 (Markov's Theorem)
If R is a nonnegative random variable, then for all x > 0, Pr[R >= x] <= Ex[R]/x.

## Statement 110: Corollary 19.1.2
If R is a nonnegative random variable, then for all c > 1, Pr[R >= c * Ex[R]] <= 1/c.

## Statement 111: Lemma 19.2.1
For any random variable R and positive real numbers x, z, Pr[|R| >= x] <= Ex[|R|^z] / x^z.

## Statement 112: Theorem 19.2.3 (Chebyshev's Theorem)
Let R be a random variable and x in R+. Then Pr[|R - Ex[R]| >= x] <= Var[R] / x^2.

## Statement 113: Theorem 19.3.7 (Pairwise Independent Additivity of Variance, two variables)
If R and S are independent random variables, then Var[R + S] = Var[R] + Var[S].

## Statement 114: Theorem 19.3.8 (Pairwise Independent Additivity of Variance)
If R_1, R_2, ..., R_n are pairwise independent random variables, then Var[R_1 + R_2 + ... + R_n] = Var[R_1] + Var[R_2] + ... + Var[R_n].

## Statement 115: Lemma 19.3.9 (Variance of the Binomial Distribution)
If J has the (n, p)-binomial distribution, then Var[J] = np(1-p).

## Statement 116: Theorem 19.6.1 (Chernoff Bound)
Let T_1, ..., T_n be mutually independent random variables such that 0 <= T_i <= 1 for all i. Let T = T_1 + ... + T_n. Then for c >= 1, Pr[T >= c * Ex[T]] <= e^{-(c*ln(c) - c + 1)*Ex[T]}.

## Statement 117: Lemma 19.6.2
Ex[c^T] <= e^{(c-1)*Ex[T]}.

## Statement 118: Theorem 20.1.1 (Gambler's Ruin)
In the Gambler's Ruin game with initial capital n, target T, and probability p of winning each bet, Pr[the gambler wins] = (r^n - 1)/(r^T - 1) if p != 1/2 (where r = q/p), and n/T if p = 1/2.

## Statement 119: Corollary 20.1.2
In the Gambler's Ruin game with initial capital n, target T, and probability p < 1/2 of winning each individual bet, Pr[the gambler wins] < (1/r)^{T-n} where r := q/p > 1.

## Statement 120: Theorem 20.1.3
In the Gambler's Ruin game with initial capital n, target T, and probability p of winning each bet, Ex[number of bets] = n(T-n) for p = 1/2, and (w_n * T - n)/(p - q) for p != 1/2, where w_n = Pr[the gambler wins].

## Statement 121: Lemma 20.1.4
If the gambler starts with one or more dollars and plays a fair unbounded game, then he will go broke with probability 1.

## Statement 122: Lemma 20.1.5
If the gambler starts with one or more dollars and plays a fair unbounded game, then his expected number of plays is infinite.
