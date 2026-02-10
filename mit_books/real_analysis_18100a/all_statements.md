# All Mathematical Statements - Real Analysis 18.100A

## Statement 1: Theorem (De Morgan's Laws)
If A, B, C are sets then (B union C)^c = B^c intersect C^c, (B intersect C)^c = B^c union C^c, A \ (B union C) = (A \ B) intersect (A \ C), and A \ (B intersect C) = (A \ B) union (A \ C).

## Statement 2: Theorem (Induction)
Let P(n) be a statement depending on n in N. If P(1) is true (base case) and if P(m) true implies P(m+1) true (inductive step), then P(n) is true for all n in N.

## Statement 3: Theorem (Geometric Sum Formula)
For all c != 1 in the reals and for all n in N, 1 + c + c^2 + ... + c^n = (1 - c^{n+1})/(1 - c).

## Statement 4: Theorem (Bernoulli's Inequality)
For all c >= -1, (1+c)^n >= 1 + nc for all n in N.

## Statement 5: Theorem (Cantor-Schroeder-Bernstein)
If |A| <= |B| and |B| <= |A| then |A| = |B|.

## Statement 6: Theorem (Cantor's Theorem)
If A is a set, then |A| < |P(A)| (the power set of A has strictly greater cardinality).

## Statement 7: Corollary (n < 2^n)
For all n in N union {0}, n < 2^n.

## Statement 8: Theorem (Existence and Uniqueness of Real Numbers)
There exists a unique ordered field containing Q with the least upper bound property, denoted R.

## Statement 9: Theorem (Sup of {q in Q : q > 0, q^2 < 2} implies x^2 = 2)
If x in Q and x = sup{q in Q : q > 0, q^2 < 2}, then x > 0 and x^2 = 2.

## Statement 10: Theorem (Q lacks LUB property)
The set E = {q in Q : q > 0 and q^2 < 2} does not have a supremum in Q.

## Statement 11: Theorem (0x = 0 in a field)
If x is in a field F, then 0x = 0.

## Statement 12: Theorem (Negative of positive is negative in ordered field)
If x > 0 in an ordered field, then -x < 0 (and vice versa).

## Statement 13: Theorem (Product of positive and negative is negative)
Let x, y in an ordered field F. If x > 0 and y < 0, or x < 0 and y > 0, then xy < 0.

## Statement 14: Theorem (Greatest Lower Bound Property)
Let F be an ordered field with the least upper bound property. If A subset F is nonempty and bounded below, then inf A exists in F.

## Statement 15: Theorem (Existence of R)
There exists a unique ordered field R such that Q subset R and R has the least upper bound property.

## Statement 16: Theorem (Existence and uniqueness of sqrt(2))
There exists a unique r in R such that r > 0 and r^2 = 2. In other words, sqrt(2) in R but sqrt(2) not in Q.

## Statement 17: Theorem (Archimedean Property and Density of Q)
(i) If x, y in R and x > 0, then there exists n in N such that nx > y. (ii) If x, y in R and x < y, then there exists r in Q such that x < r < y.

## Statement 18: Theorem (sup{1 - 1/n : n in N} = 1)
1 = sup{1 - 1/n : n in N}.

## Statement 19: Theorem (Characterization of Supremum)
Suppose S subset R is nonempty and bounded above. Then x = sup S if and only if (1) x is an upper bound for S and (2) for all epsilon > 0, there exists y in S such that x - epsilon < y <= x.

## Statement 20: Theorem (Supremum of translated and scaled sets)
(1) If x in R and A is bounded above, then sup(x + A) = x + sup A. (2) If x > 0 and A is bounded above, then sup(xA) = x sup A.

## Statement 21: Theorem (sup A <= inf B)
Let A, B subset R such that for all x in A, for all y in B, x <= y. Then sup A <= inf B.

## Statement 22: Theorem (Absolute Value Properties)
Properties of absolute value: |x| >= 0 with |x| = 0 iff x = 0; |-x| = |x|; |xy| = |x||y|; |x^2| = x^2 = |x|^2; |x| <= y iff -y <= x <= y; x <= |x|.

## Statement 23: Theorem (Triangle Inequality)
For all x, y in R, |x + y| <= |x| + |y|.

## Statement 24: Theorem (Decimal Representation)
For every x in (0,1], there exists a unique sequence of digits d_{-j} representing x. Furthermore, for every set of digits, there exists a unique x in [0,1] with that representation.

## Statement 25: Theorem (Cantor - (0,1] is uncountable)
The interval (0,1] is uncountable.

## Statement 26: Corollary (R is uncountable)
The set of real numbers R is uncountable.

## Statement 27: Theorem (Uniqueness of Limits)
If {x_n} converges to x and y, then x = y. Limits of convergent sequences of real numbers are unique.

## Statement 28: Theorem (Closeness Lemma)
Let x, y in R. If for all epsilon > 0, |x - y| < epsilon, then x = y.

## Statement 29: Theorem (Convergent implies Bounded)
If {x_n} is convergent, then {x_n} is bounded.

## Statement 30: Theorem (Monotone Convergence - Increasing)
Let {x_n} be a monotone increasing sequence. Then {x_n} is convergent if and only if {x_n} is bounded. Moreover, lim x_n = sup{x_n : n in N}.

## Statement 31: Theorem (Monotone Convergence - Decreasing)
Let {x_n} be a monotone decreasing sequence. Then {x_n} is convergent if and only if {x_n} is bounded. Moreover, lim x_n = inf{x_n : n in N}.

## Statement 32: Theorem (Subsequences of Convergent Sequences)
If {x_n} converges to x, then any subsequence of {x_n} also converges to x.

## Statement 33: Theorem (Squeeze Theorem)
Let {a_n}, {b_n}, {x_n} be sequences with a_n <= x_n <= b_n for all n. If lim a_n = x = lim b_n, then {x_n} converges and lim x_n = x.

## Statement 34: Theorem (Absolute Convergence Criterion)
lim x_n = x if and only if lim |x_n - x| = 0.

## Statement 35: Theorem (Limits Preserve Order)
(1) If {x_n} and {y_n} are convergent and x_n <= y_n for all n, then lim x_n <= lim y_n. (2) If {x_n} is convergent and a <= x_n <= b for all n, then a <= lim x_n <= b.

## Statement 36: Theorem (Algebraic Limit Theorem)
If lim x_n = x and lim y_n = y, then: (1) lim(x_n + y_n) = x + y, (2) lim(cx_n) = cx, (3) lim(x_n y_n) = xy, (4) if y_n != 0 and y != 0, then lim(x_n/y_n) = x/y.

## Statement 37: Theorem (Limit of Square Root)
If {x_n} is convergent with x_n >= 0 for all n, then lim sqrt(x_n) = sqrt(lim x_n).

## Statement 38: Theorem (Limit of Absolute Value)
If {x_n} is convergent and lim x_n = x, then lim |x_n| = |x|.

## Statement 39: Theorem (Geometric Sequence Limit)
If c in (0,1), then lim c^n = 0. If c > 1, then {c^n} is unbounded.

## Statement 40: Theorem (Special Sequences)
(1) If p > 0, then lim n^{-p} = 0. (2) If p > 0, then lim p^{1/n} = 1. (3) lim n^{1/n} = 1.

## Statement 41: Theorem (Limsup/Liminf Existence and Properties)
Let {x_n} be a bounded sequence, a_n = sup{x_k : k >= n}, b_n = inf{x_k : k >= n}. Then: (1) {a_n} is monotone decreasing and bounded, {b_n} is monotone increasing and bounded. (2) liminf x_n <= limsup x_n.

## Statement 42: Theorem (Subsequences Converging to Limsup/Liminf)
Let {x_n} be a bounded sequence. Then there exist subsequences converging to limsup x_n and liminf x_n respectively.

## Statement 43: Theorem (Bolzano-Weierstrass)
Every bounded sequence has a convergent subsequence.

## Statement 44: Theorem (Convergence iff Limsup equals Liminf)
Let {x_n} be a bounded sequence. Then {x_n} converges if and only if liminf x_n = limsup x_n.

## Statement 45: Theorem (Cauchy implies Bounded)
If {x_n} is Cauchy, then {x_n} is bounded.

## Statement 46: Theorem (Cauchy with Convergent Subsequence implies Convergent)
If {x_n} is Cauchy and a subsequence {x_{n_k}} converges, then {x_n} converges.

## Statement 47: Theorem (Cauchy iff Convergent in R)
A sequence of real numbers {x_n} is Cauchy if and only if {x_n} is convergent.

## Statement 48: Theorem (Geometric Series)
If |r| < 1 then sum_{n=0}^infty r^n converges and sum_{n=0}^infty r^n = 1/(1-r).

## Statement 49: Theorem (Tail Convergence of Series)
Let {x_n} be a sequence and M in N. Then sum_{n=1}^infty x_n converges if and only if sum_{n=M}^infty x_n converges.

## Statement 50: Theorem (Series Cauchy iff Convergent)
sum x_n is Cauchy if and only if sum x_n is convergent.

## Statement 51: Theorem (Cauchy Criterion for Series)
sum x_n is Cauchy if and only if for all epsilon > 0, there exists M in N such that for all m >= M and l > m, |sum_{n=m+1}^l x_n| < epsilon.

## Statement 52: Theorem (Divergence Test)
If sum x_n converges then lim x_n = 0.

## Statement 53: Theorem (Geometric Series Divergence)
If |r| >= 1, then sum_{n=0}^infty r^n diverges.

## Statement 54: Corollary (Geometric Series Convergence Criterion)
The series sum_{n=0}^infty alpha r^n converges if and only if |r| < 1.

## Statement 55: Theorem (Harmonic Series Diverges)
The series sum_{n=1}^infty 1/n does not converge.

## Statement 56: Theorem (Linearity of Series)
Let alpha in R and sum x_n, sum y_n be convergent series. Then sum(alpha x_n + y_n) converges and equals alpha sum x_n + sum y_n.

## Statement 57: Theorem (Nonneg Series Convergence iff Partial Sums Bounded)
If x_n >= 0 for all n, then sum x_n converges if and only if the partial sums are bounded.

## Statement 58: Theorem (Absolute Convergence implies Convergence)
If sum x_n converges absolutely (i.e., sum |x_n| converges), then sum x_n converges.

## Statement 59: Theorem (Comparison Test)
If 0 <= x_n <= y_n for all n, then: (1) if sum y_n converges, then sum x_n converges; (2) if sum x_n diverges, then sum y_n diverges.

## Statement 60: Theorem (p-Series Test)
For p in R, the series sum_{n=1}^infty 1/n^p converges if and only if p > 1.

## Statement 61: Theorem (Ratio Test)
Suppose x_n != 0 for all n and L = lim |x_{n+1}|/|x_n| exists. If L < 1, sum x_n converges absolutely. If L > 1, sum x_n diverges.

## Statement 62: Theorem (Root Test)
Let sum x_n be a series and L = lim |x_n|^{1/n} exist. If L < 1, sum x_n converges absolutely. If L > 1, sum x_n diverges.

## Statement 63: Theorem (Alternating Series Test)
Let {x_n} be a monotone decreasing sequence with x_n -> 0. Then sum (-1)^n x_n converges.

## Statement 64: Corollary (Alternating Harmonic Series Converges)
sum (-1)^n / n converges (but does not converge absolutely).

## Statement 65: Theorem (Rearrangement of Absolutely Convergent Series)
If sum x_n converges absolutely to x and sigma: N -> N is a bijection, then sum x_{sigma(n)} converges absolutely and equals x.

## Statement 66: Theorem (Cluster Point Characterization)
Let S subset R. Then x is a cluster point of S if and only if there exists a sequence {x_n} in S \ {x} with x_n -> x.

## Statement 67: Theorem (Uniqueness of Function Limits)
Let c be a cluster point of S subset R, and let f: S -> R. If f(x) -> L_1 and f(x) -> L_2 as x -> c, then L_1 = L_2.

## Statement 68: Theorem (Sequential Characterization of Function Limits)
Let S subset R, c a cluster point of S, and f: S -> R. Then lim_{x->c} f(x) = L iff for every sequence {x_n} in S \ {c} with x_n -> c, we have f(x_n) -> L.

## Statement 69: Theorem (lim x^2 = c^2)
For all c in R, lim_{x->c} x^2 = c^2.

## Statement 70: Theorem (sin(1/x) and x sin(1/x) limits)
(1) lim_{x->0} sin(1/x) does not exist. (2) lim_{x->0} x sin(1/x) = 0.

## Statement 71: Theorem (Limits of Functions Preserve Order)
Let S subset R, c a cluster point of S, and f,g: S -> R. If f(x) <= g(x) for all x in S and both limits at c exist, then lim_{x->c} f(x) <= lim_{x->c} g(x).

## Statement 72: Theorem (Two-sided Limits)
Let S subset R and c a cluster point of S intersect (-infty,c) and S intersect (c,infty). Then lim_{x->c} f(x) = L iff lim_{x->c^-} f(x) = lim_{x->c^+} f(x) = L.

## Statement 73: Theorem (Continuity Characterization)
Let S subset R, c in S, f: S -> R. (1) If c is not a cluster point, f is continuous at c. (2) If c is a cluster point, f is continuous at c iff lim_{x->c} f(x) = f(c). (3) f is continuous at c iff for every sequence x_n -> c with x_n in S, f(x_n) -> f(c).

## Statement 74: Theorem (sin and cos are continuous)
The functions f(x) = sin x and g(x) = cos x are continuous on R.

## Statement 75: Theorem (Polynomials are continuous)
If f is a polynomial, then f is continuous on all of R.

## Statement 76: Theorem (Arithmetic of Continuous Functions)
If f, g: S -> R are continuous at c, then f + g, f*g are continuous at c, and f/g is continuous at c when g(x) != 0.

## Statement 77: Theorem (Composition of Continuous Functions)
Let A, B subset R, f: B -> R, g: A -> B. If g is continuous at c and f is continuous at g(c), then f o g is continuous at c.

## Statement 78: Theorem (Dirichlet Function Nowhere Continuous)
The function f(x) = 1 if x in Q, 0 if x not in Q, is not continuous at any point of R.

## Statement 79: Theorem (Continuous Functions on Closed Intervals are Bounded)
If f: [a,b] -> R is continuous, then f is bounded.

## Statement 80: Theorem (Min-Max Theorem / Extreme Value Theorem)
Let f: [a,b] -> R be continuous. Then f achieves an absolute maximum and absolute minimum.

## Statement 81: Theorem (Bolzano's Intermediate Value Theorem - Zero Version)
Let f: [a,b] -> R be continuous. If f(a) < 0 and f(b) > 0, then there exists c in (a,b) such that f(c) = 0.

## Statement 82: Theorem (Bolzano IVT - General Version)
Let f: [a,b] -> R be continuous. If y is between f(a) and f(b), then there exists c in (a,b) such that f(c) = y.

## Statement 83: Theorem (Image of Continuous Function on Closed Interval)
Let f: [a,b] -> R be continuous, with absolute minimum at c and maximum at d. Then f([a,b]) = [f(c), f(d)].

## Statement 84: Theorem (Odd-Degree Polynomial Has a Real Root)
The polynomial f(x) = x^{2021} + x^{2020} + 9.03x + 1 has at least one real root.

## Statement 85: Theorem (Continuous on Closed Interval iff Uniformly Continuous)
Let f: [a,b] -> R. Then f is continuous if and only if f is uniformly continuous.

## Statement 86: Theorem (Differentiable implies Continuous)
If f: I -> R is differentiable at c in I, then f is continuous at c.

## Statement 87: Theorem (Derivative Rules: Linearity, Product, Quotient)
Let f, g: I -> R be differentiable at c. Then: (1) (alpha f + g)'(c) = alpha f'(c) + g'(c). (2) (fg)'(c) = f'(c)g(c) + f(c)g'(c). (3) If g(x) != 0, (f/g)'(c) = (f'(c)g(c) - f(c)g'(c))/(g(c))^2.

## Statement 88: Theorem (Chain Rule)
Let g: I_1 -> I_2 be differentiable at c, f: I_2 -> R differentiable at g(c). Then (f o g)'(c) = f'(g(c)) g'(c).

## Statement 89: Theorem (Interior Extremum Theorem / Fermat's Theorem)
If f: [a,b] -> R has a relative max or min at c in (a,b) and f is differentiable at c, then f'(c) = 0.

## Statement 90: Theorem (Rolle's Theorem)
Let f: [a,b] -> R be continuous and differentiable on (a,b). If f(a) = f(b), then there exists c in (a,b) such that f'(c) = 0.

## Statement 91: Theorem (Mean Value Theorem)
Let f: [a,b] -> R be continuous, differentiable on (a,b). Then there exists c in (a,b) such that f(b) - f(a) = f'(c)(b - a).

## Statement 92: Theorem (Zero Derivative implies Constant)
If f: I -> R is differentiable and f'(x) = 0 for all x in I, then f is constant.

## Statement 93: Theorem (Monotonicity and Derivative Sign)
Let f: I -> R be differentiable. (1) f is increasing iff f'(x) >= 0 for all x in I. (2) f is decreasing iff f'(x) <= 0 for all x in I.

## Statement 94: Theorem (Taylor's Theorem)
Suppose f: [a,b] -> R is continuous with n continuous derivatives and f^{(n+1)} exists on (a,b). Given x_0, x in [a,b], there exists c between x_0 and x such that f(x) = sum_{k=0}^n f^{(k)}(x_0)(x-x_0)^k / k! + f^{(n+1)}(c)(x-x_0)^{n+1}/(n+1)!.

## Statement 95: Theorem (Second Derivative Test)
If f: (a,b) -> R has two continuous derivatives, f'(x_0) = 0, and f''(x_0) > 0, then f has a strict relative minimum at x_0.

## Statement 96: Theorem (Weierstrass Cosine Bound)
(1) For all x, y in R, |cos x - cos y| <= |x - y|. (2) For all c in R and K in N, there exists y in (c + pi/K, c + 3pi/K) such that |cos(Kc) - cos(Ky)| >= 1.

## Statement 97: Theorem (Reverse Triangle Inequality for Three Terms)
For all a, b, c in R, |a + b + c| >= |a| - |b| - |c|.

## Statement 98: Theorem (Weierstrass Function Properties)
(1) For all x in R, sum_{k=0}^infty cos(160^k x)/4^k is absolutely convergent. (2) f(x) = sum_{k=0}^infty cos(160^k x)/4^k is bounded and continuous.

## Statement 99: Theorem (Weierstrass Nowhere Differentiable Function)
The function f(x) = sum_{k=0}^infty cos(160^k x)/4^k is nowhere differentiable.

## Statement 100: Theorem (Riemann Integral Existence)
Let f in C([a,b]). Then there exists a unique number int_a^b f(x) dx such that for all sequences of tagged partitions with norm -> 0, the Riemann sums converge to this number.

## Statement 101: Theorem (Modulus of Continuity Vanishes)
For all f in C([a,b]), lim_{eta->0} w_f(eta) = 0.

## Statement 102: Theorem (Refinement Bound for Riemann Sums)
If (x, xi) and (x', xi') are tagged partitions with x subset x', then |S_f(x,xi) - S_f(x',xi')| <= w_f(||x||)(b-a).

## Statement 103: Theorem (General Bound for Riemann Sums)
If (x,xi) and (x',xi') are any two tagged partitions, then |S_f(x,xi) - S_f(x',xi')| <= (w_f(||x||) + w_f(||x'||))(b-a).

## Statement 104: Theorem (Linearity of the Integral)
If f, g in C([a,b]) and alpha in R, then int_a^b (alpha f + g) = alpha int_a^b f + int_a^b g.

## Statement 105: Theorem (Additivity of the Integral)
If f in C([a,b]) and a < c < b, then int_a^b f = int_a^c f + int_c^b f.

## Statement 106: Theorem (Integral Bounds)
Let f in C([a,b]), m_f = inf f, M_f = sup f on [a,b]. Then m_f(b-a) <= int_a^b f <= M_f(b-a).

## Statement 107: Theorem (Monotonicity and Triangle Inequality for Integrals)
(1) If f(x) <= g(x) for all x in [a,b], then int_a^b f <= int_a^b g. (2) |int_a^b f| <= int_a^b |f|.

## Statement 108: Theorem (Fundamental Theorem of Calculus)
(1) If F is differentiable with F' = f, then int_a^b f = F(b) - F(a). (2) G(x) = int_a^x f is differentiable with G' = f and G(a) = 0.

## Statement 109: Theorem (Integration by Parts)
If f, g in C([a,b]) with f', g' in C([a,b]), then int_a^b f'g = f(b)g(b) - f(a)g(a) - int_a^b fg'.

## Statement 110: Lemma (Riemann-Lebesgue)
If f in C([-pi,pi]) with f' in C([-pi,pi]) and f 2pi-periodic, then the Fourier coefficients a_n and b_n tend to 0 as n -> infty.

## Statement 111: Theorem (Change of Variables)
Let phi: [a,b] -> [c,d] be continuously differentiable with phi' > 0, phi(a) = c, phi(b) = d. Then int_c^d f(u) du = int_a^b f(phi(x)) phi'(x) dx.

## Statement 112: Theorem (Power Series Radius of Convergence)
If R = lim |a_m|^{1/n} exists with p = 1/R (or infty if R = 0), then sum a_m(x-x_0)^m converges absolutely for |x-x_0| < p and diverges for |x-x_0| > p.

## Statement 113: Theorem (Uniform Convergence implies Pointwise Convergence)
If f_n -> f uniformly, then f_n -> f pointwise.

## Statement 114: Theorem (x^n Convergence on [0,b] vs [0,1])
(1) For all 0 < b < 1, x^n -> 0 uniformly on [0,b]. (2) x^n does not converge uniformly on [0,1].

## Statement 115: Theorem (Weierstrass M-test)
Let f_j: S -> R with |f_j(x)| <= M_j for all x in S and sum M_j convergent. Then sum f_j(x) converges absolutely for all x, and the partial sums converge uniformly to f on S.

## Statement 116: Theorem (Uniform Limit of Continuous Functions is Continuous)
If f_n: S -> R are continuous for all n and f_n -> f uniformly, then f is continuous.

## Statement 117: Theorem (Uniform Convergence and Integration)
If f_n: [a,b] -> R are continuous and f_n -> f uniformly, then int_a^b f_n -> int_a^b f.

## Statement 118: Theorem (Uniform Convergence of Derivatives and Differentiation)
If f_n: [a,b] -> R are continuously differentiable, f_n -> f pointwise, and f_n' -> g uniformly, then f is continuously differentiable and f' = g.

## Statement 119: Theorem (Uniform Convergence of Power Series on Compact Subsets)
Let sum a_j(x-x_0)^j have radius of convergence p in (0,infty]. Then for all r in (0,p), the series converges uniformly on [x_0-r, x_0+r].

## Statement 120: Theorem (Term-by-term Differentiation and Integration of Power Series)
Let sum a_j(x-x_0)^j have radius of convergence p. Then: (1) the series is differentiable with d/dx sum = sum j a_j(x-x_0)^{j-1}; (2) term-by-term integration is valid.

## Statement 121: Theorem (Weierstrass Approximation Theorem)
If f in C([a,b]), there exists a sequence of polynomials {P_n} such that P_n -> f uniformly on [a,b].

## Statement 122: Theorem (Properties of Approximating Kernels Q_n)
Let Q_n(x) = c_n(1-x^2)^n with c_n normalizing. Then: (1) int_{-1}^1 Q_n = 1, (2) Q_n(x) >= 0, (3) for all delta in (0,1), Q_n -> 0 uniformly on delta <= |x| <= 1.
