# All Mathematical Statements in 18.100C Real Analysis

## Lecture 1
1. **Fact 1.1.** Every nonempty subset of N has a least element.
2. **Theorem 1.2.** Any subset of N is either finite or countable.
3. **Theorem 1.3.** If S1 and S2 are countable, S1 union S2 is countable.
4. **Theorem 1.4.** N^2 is countable.
5. **Corollary 1.5.** If S1 and S2 are countable, S1 x S2 is countable.
6. **Corollary 1.6.** If S1, S2, ... are countable sets, their countable union is countable.

## Lecture 2
7. **Theorem 2.1.** In any field, x * 0 = 0 for all x.
8. **Theorem 2.2.** In any ordered field, 1 > 0.
9. **Theorem 2.3.** In any ordered field, x > 0 if and only if -x < 0.
10. **Corollary 2.4.** In any ordered field, x^2 >= 0, with equality if and only if x = 0.
11. **Theorem 2.5.** There is a unique real number x > 0 such that x^2 = 2.
12. **Corollary 2.6.** A real number is nonnegative if and only if it is a square.
13. **Theorem 2.7.** (Archimedean principle) For every real number x there is a natural number n such that n > x.

## Lecture 3
14. **Corollary 3.1.** For every real number x > 0 there is a natural number n such that 1/n < x.
15. **Corollary 3.2.** For every real number x there is an integer n such that x < n <= x + 1.
16. **Corollary 3.3.** For any real numbers x < y there is a rational number q such that x < q < y.
17. **Theorem 3.4.** 0.9999... = 1.
18. **Theorem 3.5.** Let I1 superset I2 superset I3 ... be nonempty closed intervals, Ik = [ak, bk]. Then their intersection is nonempty.
19. **Corollary 3.6.** R is uncountable.
20. **Theorem 3.7.** (Cauchy-Schwarz) For complex numbers z1,...,zk, w1,...,wk, |z1*conj(w1) + ... + zk*conj(wk)|^2 <= (|z1|^2 + ... + |zk|^2)(|w1|^2 + ... + |wk|^2).

## Lecture 4
21. **Theorem 4.1.** (Triangle inequality for Euclidean norm) On R^n, ||x + y|| <= ||x|| + ||y||.
22. **Theorem 4.2.** Every ball neighbourhood is an open subset.

## Lecture 5
23. **Theorem 5.1.** If E, F are open subsets, then so are E union F and E intersection F.
24. **Theorem 5.2.** If (Ei) is a collection of open subsets indexed by i in I, then their union is also open.
25. **Corollary 5.3.** Every open subset is a union of ball neighbourhoods.
26. **Theorem 5.4.** If x is a limit point of E, then B_r(x) intersection E is infinite for any r > 0.
27. **Corollary 5.5.** A finite subset of X has no limit points, hence is closed.
28. **Theorem 5.6.** If E, F are closed subsets, then so are E union F and E intersection F.
29. **Theorem 5.7.** If (Ei) is a collection of closed subsets indexed by i in I, then their intersection is also closed.
30. **Theorem 5.8.** A subset E of X is open if and only if its complement X \ E is closed.

## Lecture 6
31. **Theorem 6.2.** If K is a compact set and x is a point, then K is contained in B_r(x) for some r.
32. **Theorem 6.3.** If K is compact, it is also a closed subset.
33. **Theorem 6.4.** If K is compact and E is closed, K intersection E is again compact.
34. **Theorem 6.5.** If K1, K2 are compact, then so is K1 union K2.
35. **Theorem 6.6.** If K is compact and E is an infinite subset of K, then E has a limit point (in K).
36. **Theorem 6.7.** K is a compact subset of X if and only if K itself as a metric space is compact.

## Lecture 7
37. **Theorem 7.1.** Let (X,d) be a metric space with the property that every countably infinite subset has a limit point. Then X is compact.
38. **Theorem 7.2.** (Heine-Borel) Every finite closed interval [a,b] in R is compact.
39. **Theorem 7.3.** Every bounded closed subset of R is compact.
40. **Theorem 7.4.** Every finite closed cube in R^n is compact.
41. **Theorem 7.5.** Every bounded closed subset of R^n is compact.

## Lecture 8
42. **Theorem 8.1.** Let (xn) be a convergent sequence where all xn lie in E. Then the limit x lies in the closure of E.
43. **Theorem 8.2.** If x is in the closure of E, there is a sequence (xn), xn in E, which converges to x.
44. **Theorem 8.3.** Let (X,d) be a compact metric space. Then every sequence has a convergent subsequence.
45. **Corollary 8.4.** Every bounded sequence in R^d has a convergent subsequence.
46. **Lemma 8.5.** Let (xn) be a Cauchy sequence. If it has a convergent subsequence, then (xn) itself converges.
47. **Theorem 8.6.** Let (X,d) be a compact metric space. Then every Cauchy sequence converges.
48. **Corollary 8.7.** Every Cauchy sequence in R^n converges.

## Lecture 9
49. **Theorem 9.1.** The set of accumulation points of any sequence is a closed subset.
50. **Theorem 9.2.** Suppose that the metric space (X,d) is separable. Then for every closed nonempty subset E there is a sequence whose set of accumulation points is precisely E.
51. **Theorem 9.3.** Let (xn) be a nondecreasing sequence. Then (xn) converges if and only if it is bounded above.
52. **Theorem 9.4.** xn = (1 + 1/n)^n converges.
53. **Theorem 9.5.** A series of nonnegative numbers converges if and only if its partial sums are bounded above.
54. **Theorem 9.6.** sum_{k=0}^{infty} x^k = 1/(1-x) for all |x| < 1.
55. **Theorem 9.7.** sum_{k=1}^{infty} 1/k^p diverges if p <= 1, and converges if p > 1.

## Lecture 10
56. **Theorem 10.1.** (Euler) The series sum 1/p, where p ranges over all prime numbers, is divergent.
57. **Theorem 10.2.** Absolute convergence implies convergence.
58. **Theorem 10.3.** Suppose that sum ai is absolutely convergent, with value s. Then, for every epsilon > 0 there is an N such that for every finite subset I containing {1,...,N}, |sum_{i in I} ai - s| < epsilon.
59. **Corollary 10.4.** If sum ai is absolutely convergent and sum a_{sigma(i)} is a reordering, then it is again absolutely convergent with the same value.
60. **Theorem 10.5.** (Product theorem for series) Given absolutely convergent sum ai and convergent sum bj, the Cauchy product sum ck is convergent, and (sum ai)(sum bj) = sum ck.

## Lecture 11
61. **Theorem 11.1.** f(z) = sum a_k z^k is absolutely convergent for all |z| < rho (the radius of convergence).
62. **Theorem 11.2.** Take a series f(z) = sum a_k z^k where a_k in R and a0 >= a1 >= ..., lim ak = 0. Suppose radius of convergence is 1. Then the series converges for all z such that |z| = 1 and z != 1.
63. **Theorem 11.3.** (Abel) Take a series f(z) = sum a_k z^k with a_k in R. Suppose sum ak is convergent. Then its value is lim_{t->1} f(t), where the limit is taken over real t < 1.
64. **Theorem 11.4.** exp(z) exp(w) = exp(z + w).
65. **Theorem 11.5.** |exp(z)| = exp(Re(z)).
66. **Theorem 11.6.** cos^2(t) + sin^2(t) = 1.

## Lecture 12
67. **Theorem 12.5.** The four definitions of continuity are equivalent.
68. **Theorem 12.6.** If f: X -> Y and g: Y -> Z are continuous, then g circ f: X -> Z is continuous.
69. **Corollary 12.7.** If f, g: X -> R are continuous, then f(x) + g(x) and f(x)g(x) are continuous.
70. **Corollary 12.8.** If f: X -> R is continuous and everywhere nonzero, then 1/f is continuous.
71. **Theorem 12.9.** If f: X -> Y is continuous and K is compact, then f(K) is compact.
72. **Corollary 12.10.** If X is a compact metric space and f: X -> R is continuous, then f is bounded and has a minimum and maximum.
73. **Corollary 12.11.** Let X be a compact metric space, and f: X -> Y a continuous, one-to-one, onto map. Then f^{-1}: Y -> X is again continuous.
74. **Theorem 12.14.** The two definitions of continuity at a point are equivalent.
75. **Lemma 12.16.** If f: X -> Y satisfies lim_{x->p} f(x) = f(p), then it is continuous at p (and conversely).

## Lecture 13
76. **Theorem 13.3.** (Intermediate Value Theorem) Let f: [a,b] -> R be continuous with f(a) <= 0, f(b) >= 0. Then there is some x such that f(x) = 0.
77. **Corollary 13.4.** Let f: [a,b] -> R be continuous. Then its image is a closed interval [c,d].
78. **Corollary 13.5.** Let f: [a,b] -> R be continuous and strictly increasing. Then f is one-to-one onto a closed interval [c,d], and f^{-1}: [c,d] -> [a,b] is continuous.
79. **Theorem 13.8.** If X is compact, every continuous map f: X -> Y is uniformly continuous.

## Lecture 14
80. **Theorem 14.4.** The three definitions of differentiability are equivalent.
81. **Theorem 14.5.** If f is differentiable at p, it is also continuous at p.
82. **Theorem 14.7.** (Chain rule) If g is differentiable at p and f is differentiable at g(p), then f circ g is differentiable at p, and (f circ g)'(p) = f'(g(p))g'(p).
83. **Theorem 14.8.** (Rolle's theorem) Let f: [a,b] -> R be continuous on [a,b], differentiable on (a,b), and f(a) = f(b). Then there is some p in (a,b) such that f'(p) = 0.
84. **Theorem 14.9.** (Mean Value Theorem) Let f: [a,b] -> R be continuous on [a,b], differentiable on (a,b). Then there is some p in (a,b) such that (f(b) - f(a))/(b - a) = f'(p).
85. **Theorem 14.10.** (Generalized Mean Value Theorem) Let f, g: [a,b] -> R be continuous on [a,b], differentiable on (a,b). Then there is some p in (a,b) such that (f(b) - f(a))g'(p) = (g(b) - g(a))f'(p).

## Lecture 15
86. **Theorem 15.1.** (Inverse function theorem for derivatives) Suppose f(g(x)) = x. Under appropriate conditions, f is differentiable at g(p), and f'(g(p)) = 1/g'(p).
87. **Theorem 15.4.** (Taylor's theorem, Peano form) Suppose f is m times differentiable at p. Then f(x) = sum_{k=0}^{m} f^{(k)}(p)(x-p)^k/k! + r(x)(x-p)^m, where lim r(x) = 0.
88. **Theorem 15.5.** (Taylor's theorem, Peano form, epsilon-delta version) Equivalent reformulation with epsilon-delta.
89. **Theorem 15.6.** (Taylor's theorem with Lagrange remainder) Under appropriate differentiability conditions, f(b) = sum_{k=0}^{m} f^{(k)}(a)(b-a)^k/k! + f^{(m+1)}(x)(b-a)^{m+1}/(m+1)! for some interior point x.

## Lecture 16
90. **Theorem 16.1.** (Cauchy convergence criterion for uniform convergence) A sequence of functions fn is uniformly convergent if and only if it satisfies the uniform Cauchy condition.
91. **Corollary 16.2.** (Weierstrass M-test) Let sum fn be a series of functions with |fn(x)| <= Mn for all n, x, and sum Mn converges. Then sum fn converges uniformly.
92. **Corollary 16.3.** A power series sum an x^n with radius of convergence rho > 0 converges uniformly on any interval [-r, r] with r < rho.
93. **Theorem 16.4.** If (fn) are continuous functions converging uniformly towards f, then f is again continuous.
94. **Corollary 16.5.** Let f(x) = sum an x^n be a power series with radius of convergence rho > 0. Then f is continuous on (-rho, rho).

## Lecture 17
95. **Theorem 17.1.** Let (fn) be differentiable functions on [a,b]. If (fn') converges uniformly and (fn(x0)) converges for one point x0, then (fn) converges uniformly, the limit f is differentiable everywhere, and f' = lim fn'.
96. **Corollary 17.2.** If f(x) = sum an x^n has convergence radius rho > 0, then it is everywhere differentiable in (-rho, rho), and its derivative is f'(x) = sum an n x^{n-1} (same radius).
97. **Corollary 17.3.** If f(x) = sum an x^n has convergence radius rho > 0, then it is infinitely often differentiable in (-rho, rho).
98. **Theorem 17.4.** (Arzela-Ascoli type) Let (fn) be differentiable functions on [a,b] with |fn(x)| <= C, |fn'(x)| <= D. Then (fn) has a uniformly convergent subsequence.

## Lecture 18
99. **Theorem 18.1.** B(X) (the space of bounded functions) is a complete metric space.
100. **Theorem 18.2.** C(X) is a closed subspace of B(X), hence itself complete.
101. **Theorem 18.3.** The closure of a bounded subset of B^1(X) in C(X) is compact.
102. **Theorem 18.4.** (Lattice version of Stone-Weierstrass) If A subset C(X) is closed under max and min, and separates points, then A is dense in C(X).
103. **Theorem 18.5.** (Stone-Weierstrass) If A subset C(X) contains constants, is closed under addition and multiplication, and separates points, then A is dense in C(X).

## Lecture 19
104. **Proposition 19.2.** Properties of the integral of piecewise linear functions: constant functions, linearity, and positivity.
105. **Lemma 19.3.** Any continuous function f: [a,b] -> R is the uniform limit of piecewise linear functions.
106. **Theorem 19.4.** There is a unique way of assigning to each continuous f: [a,b] -> R a number (its integral) extending the integral of piecewise linear functions and preserved under uniform limits.

## Lecture 20
107. **Theorem 20.3.** Characterization of RS-integrability via partitions with S(f,alpha,P) - s(f,alpha,P) < epsilon.
108. **Theorem 20.4.** Continuous functions f are RS-integrable for any alpha.
109. **Theorem 20.5.** If (fn) are RS-integrable and fn -> f uniformly, then f is RS-integrable and the integrals converge.
110. **Theorem 20.6.** Linearity and positivity of the RS-integral: (i) integral of f+g, (ii) integral of cf, (iii) positivity.

## Lecture 21
111. **Theorem 21.1.** If f is RS-integrable and phi is continuous, then phi(f) is RS-integrable.
112. **Corollary 21.2.** If f and g are RS-integrable, then fg is RS-integrable.
113. **Corollary 21.3.** If f is RS-integrable, then |f| is RS-integrable, and |integral f| <= integral |f|.
114. **Theorem 21.4.** (Change of variables, easy version) If phi is strictly increasing, continuous, maps [A,B] to [a,b], and f is RS-integrable for alpha, then f(phi) is RS-integrable for alpha(phi).
115. **Theorem 21.5.** If alpha is differentiable with alpha' Riemann-integrable, and f is RS-integrable for alpha, then f(x)alpha'(x) is Riemann-integrable and the integrals agree.
116. **Corollary 21.6.** (Substitution rule) If phi is strictly increasing, differentiable with phi' Riemann integrable, and f is Riemann integrable, then f(phi(x))phi'(x) is Riemann integrable and integral equals integral.

## Lecture 22
117. **Lemma 22.1.** Additivity of the RS-integral over subintervals.
118. **Theorem 22.2.** (Fundamental Theorem of Calculus, Part 1) If f is Riemann integrable and F(x) = integral from a to x of f, then F is continuous; if f is continuous at x0, then F is differentiable there with F'(x0) = f(x0).
119. **Theorem 22.3.** (Fundamental Theorem of Calculus, Part 2) If f is differentiable and f' is Riemann integrable, then integral from a to b of f'(x) dx = f(b) - f(a).
120. **Lemma 22.4.** If f(x) = sum ak x^k has radius of convergence rho > 0, then f is differentiable at all x in (-rho, rho) with derivative sum ak k x^{k-1}, which has the same radius.

## Lecture 23
121. **Lemma 23.1.** There is a smallest number pi > 0 such that cos(pi/2) = 0. Moreover, sin(pi/2) = 1.
122. **Lemma 23.2.** exp(x + 2*pi*i) = exp(x) for all complex numbers x.
123. **Lemma 23.3.** log(x) is differentiable for all x > 0, and its derivative is 1/x.
124. **Theorem 23.4.** The series x - x^2/2 + x^3/3 - x^4/4 + ... converges to log(1+x) for |x| < 1.

## Lecture 24
125. **Lemma 24.1.** If sum |ak| and sum |tilde{a}_k| converge, the Fourier series is uniformly convergent.
126. **Lemma 24.2.** If sum k|ak| and sum k|tilde{a}_k| converge, the function defined by the Fourier series is differentiable, and its derivative is the term-by-term derivative.
127. **Theorem 24.3.** If h(x) is differentiable and h'(x) is continuous, then the Fourier series converges uniformly to h(x).
128. **Theorem 24.4.** (Parseval's theorem) For a 2*pi-periodic Riemann integrable function h(x), the Fourier partial sums converge to h in L^2: lim integral |h(x) - sN(h,x)|^2 dx = 0.
