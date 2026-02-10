# All Mathematical Statements in 18.100B Real Analysis

## Lecture 1
1. **Uniqueness of Zero in a Field** -- For any field, the additive identity ('zero') is unique.
2. **Ordered Field Multiplication Inequality** -- If x < y and z > 0 in an ordered field, then xz < yz.

## Lecture 2
3. **Irrationality of sqrt(2)** -- There does not exist a rational number x such that x^2 = 2.
4. **Existence of R** -- There exists a complete ordered field that contains Q.
5. **sqrt(2) is in R** -- There exists alpha > 0 in R such that alpha^2 = 2.
6. **Q is not complete** -- The rationals Q are not a complete ordered set.
7. **Archimedean Property** -- For all x in R, there exists a natural number n such that x < n.
8. **Density of Q in R** -- If x < y, then there exists a rational number m/n such that x < m/n < y.

## Lecture 3
9. **sqrt(2) in R (formal proof)** -- There exists alpha > 0 such that alpha^2 = 2.
10. **N is not bounded above (Archimedean property, formal)** -- The set of natural numbers is not bounded from above.
11. **Archimedean Corollary** -- For any epsilon > 0, there exists n in N such that 1/n < epsilon.

## Lecture 4
12. **Convergent Sequences are Bounded** -- If a_n is a convergent sequence, then the set {a_n} is a bounded subset of R.
13. **Algebraic Properties of Limits** -- If a_n -> a, b_n -> b, then (1) Ca_n -> Ca, (2) a_n + b_n -> a + b, (3) a_n * b_n -> ab, (4) a_n/b_n -> a/b (when b_n, b != 0).
14. **Subsequences of Convergent Sequences** -- A sequence a_n is convergent with limit a if and only if all subsequences of a_n are also convergent with limit a.

## Lecture 5
15. **Monotone Convergence Theorem (Increasing)** -- A bounded monotone increasing sequence converges with limit sup{a_n}.
16. **Monotone Convergence Theorem (Decreasing)** -- A bounded monotone decreasing sequence converges with limit inf{a_n}.

## Lecture 5-6
17. **Cauchy Convergence Theorem** -- A sequence is convergent if and only if it is a Cauchy sequence.
18. **Contraction Mapping Theorem** -- Any contracting map on R has a unique fixed point.

## Lecture 6
19. **Bolzano-Weierstrass Theorem** -- Any bounded sequence of real numbers has a convergent subsequence.
20. **Continuous Functions Preserve Limits** -- If f: R -> R is continuous and x_n -> x_0, then f(x_n) -> f(x_0).
21. **Extreme Value Theorem** -- If f:[a,b] -> R is continuous, then sup and inf of f are achieved.

## Lecture 7
22. **Geometric Series** -- The geometric series sum c^i converges to 1/(1-c) when |c| < 1 and diverges when |c| >= 1.
23. **Divergence of Harmonic Series** -- The harmonic series sum 1/n diverges.
24. **Absolute Convergence Implies Convergence** -- If sum |a_n| converges, then sum a_n converges.
25. **Non-negative Series Convergence** -- A series of non-negative numbers converges if and only if the partial sums are bounded.
26. **Comparison Test (Version 1)** -- If 0 <= a_n <= b_n and sum b_n converges, then sum a_n converges.
27. **Comparison Test (Version 2)** -- If a_n/b_n -> L != 0, then sum a_n converges iff sum b_n converges.
28. **Ratio Test** -- If a_n >= 0 and a_{n+1}/a_n -> a, then: a < 1 implies convergence, a > 1 implies divergence.
29. **Root Test** -- If a_n >= 0 and (a_n)^{1/n} -> r, then: r < 1 implies convergence, r > 1 implies divergence.

## Lecture 9-10
30. **Continuous Functions Agreeing on Q** -- If f and g are continuous functions on R that agree on all rationals, then f = g.
31. **E(x+y) = E(x)E(y)** -- The exponential power series satisfies E(x+y) = E(x)E(y).
32. **Cauchy Product of Series** -- If sum a_n and sum b_n are convergent series of non-negative numbers, then their Cauchy product sum c_n converges with limit (sum a_n)(sum b_n).
33. **Polynomials are Continuous** -- All polynomials are continuous functions.
34. **Algebraic Properties of Continuous Functions** -- Sums, scalar multiples, products, quotients, and compositions of continuous functions are continuous.

## Lecture 11
35. **Intermediate Value Theorem** -- If f:[a,b] -> R is continuous, then for all y between f(a) and f(b), there exists x in [a,b] such that f(x) = y.
36. **Convergent Sequence in Metric Space is Cauchy** -- In any metric space, a convergent sequence is also a Cauchy sequence.
37. **Cauchy Sequence in Metric Space is Bounded** -- In any metric space, any Cauchy sequence is bounded.

## Lecture 12
38. **Open Ball is Open** -- In a metric space, any ball B_r(x) is an open subset.
39. **Arbitrary Union of Open Sets is Open** -- In a metric space, the union of any family of open subsets is open.
40. **Finite Intersection of Open Sets is Open** -- In a metric space, the intersection of finitely many open subsets is open.
41. **De Morgan's Laws for Sets** -- (1) X \ (X \ A) = A; (2) X \ union A_alpha = intersection (X \ A_alpha); (3) X \ intersection A_alpha = union (X \ A_alpha).

## Lecture 13
42. **Closed Set Characterization by Sequences** -- A subset C of a metric space is closed if and only if for all convergent sequences in C, the limit is in C.
43. **Intersection of Closed Sets is Closed** -- Arbitrary intersection of closed sets is closed.
44. **Finite Union of Closed Sets is Closed** -- Finite union of closed sets is closed.
45. **Compact Implies Closed and Bounded** -- If A is a compact subset of a metric space, then A is closed and bounded.
46. **Closed Subset of Compact is Compact** -- If C is a closed subset of a compact set A, then C is compact.
47. **Bolzano-Weierstrass for Compact Metric Spaces** -- Any sequence in a compact subset of a metric space has a convergent subsequence.

## Lecture 14
48. **Heine-Borel Theorem** -- In R^n, a subset is compact if and only if it is closed and bounded.
49. **Nested Closed Sets in Compact Space** -- In a compact metric space, nested non-empty closed sets have non-empty intersection.
50. **Nested Balls Corollary** -- Nested closed balls with radii tending to 0 in a compact metric space intersect in exactly one point.

## Lecture 15
51. **Differentiable Implies Continuous** -- If f is differentiable at x_0, then f is continuous at x_0.
52. **Differentiation Rules (Sum, Product, Quotient)** -- If f, g are differentiable at x_0, then (f+g)'=f'+g', (fg)'=f'g+fg', (f/g)'=(f'g-fg')/g^2.
53. **Chain Rule** -- If f is differentiable at x_0 and g is differentiable at f(x_0), then (g o f)'(x_0) = g'(f(x_0)) * f'(x_0).
54. **Local Extremum Implies Zero Derivative** -- If f has a local max or min at interior point x_0, then f'(x_0) = 0.
55. **Rolle's Theorem** -- If f:[a,b] -> R is differentiable with f(a) = f(b), then there exists x_0 in (a,b) with f'(x_0) = 0.
56. **Mean Value Theorem** -- If f:[a,b] -> R is differentiable, then there exists x_0 in (a,b) with f'(x_0) = (f(b)-f(a))/(b-a).

## Lecture 16
57. **Cauchy Mean Value Theorem** -- If f,g:[a,b] -> R are differentiable, then there exists x_0 in (a,b) with f'(x_0)(g(b)-g(a)) = g'(x_0)(f(b)-f(a)).
58. **L'Hopital's Rule (0/0 form)** -- If f(x),g(x) -> 0 as x -> a and f'/g' -> L, then f/g -> L.
59. **L'Hopital's Rule (infinity/infinity form)** -- If f(x),g(x) -> infinity as x -> a and f'/g' -> L, then f/g -> L.
60. **Taylor's Theorem** -- If f has k continuous derivatives on [a,b] and f^(k) exists on (a,b), then there exists c between a and b giving the Lagrange remainder.

## Lecture 17
61. **Upper and Lower Sums Inequality** -- U(f,P) >= L(f,P) for any partition P.
62. **Refinement Inequality** -- If P_2 is a refinement of P_1, then L(f,P_1) <= L(f,P_2) <= U(f,P_2) <= U(f,P_1).
63. **Riemann Integrability Criterion** -- A bounded function f is Riemann integrable iff for all epsilon > 0, there exists a partition P with U(f,P) - L(f,P) < epsilon.
64. **Continuous Functions are Riemann Integrable** -- Any continuous function on [a,b] is Riemann integrable.

## Lecture 18
65. **Continuous on Compact Implies Uniformly Continuous** -- Any continuous function on [a,b] is uniformly continuous.
66. **Linearity of Riemann Integral** -- The Riemann integral is linear: integral(cf) = c*integral(f), integral(f+g) = integral(f) + integral(g).
67. **Monotonicity of Riemann Integral** -- If f <= g on [a,b], then integral(f) <= integral(g).
68. **Additivity of Riemann Integral** -- integral_a^b = integral_a^c + integral_c^b.
69. **Triangle Inequality for Integrals** -- |integral f| <= integral |f|.
70. **Fundamental Theorem of Calculus, Version 1** -- If f is continuous on [a,b] and F(x) = integral_a^x f(s) ds, then F is differentiable with F' = f.
71. **Fundamental Theorem of Calculus, Version 2** -- If F is differentiable on [a,b] and F' = f is Riemann integrable, then F(b) - F(a) = integral_a^b f(s) ds.

## Lecture 20-21
72. **Uniform Limit of Continuous Functions is Continuous** -- If f_n are continuous and f_n -> f uniformly, then f is continuous.
73. **Weierstrass M-test** -- If |f_n(x)| <= M_n for all x and sum M_n converges, then sum f_n converges uniformly.
74. **C([a,b]) is Cauchy Complete** -- The space of continuous functions with sup-norm metric is Cauchy complete.
75. **Uniform Convergence Preserves Integrability** -- If f_n are Riemann integrable and f_n -> f uniformly, then f is Riemann integrable and integral(f_n) -> integral(f).
76. **Uniform Convergence and Differentiation** -- If f_n(x_0) -> c, f'_n -> g uniformly, and f'_n are continuous, then f_n -> f uniformly and f' = g.
77. **Power Series Converges Uniformly on Compact Subsets** -- A power series with radius R converges uniformly on [-L,L] for L < R.

## Lecture 22
78. **Radius of Convergence of Derived Series** -- The power series and its term-by-term derivative have the same radius of convergence.
79. **Term-by-term Differentiation and Integration of Power Series** -- A power series can be differentiated and integrated term by term within its radius of convergence.

## Lecture 22-23
80. **Picard-Lindelof Theorem** -- For a first-order ODE y' = f(y) + g(x), y(0) = a, with f continuously differentiable and g continuous, there exists delta > 0 such that the ODE has a unique solution on (-delta, delta).
81. **Contraction Mapping Theorem (General Metric Space)** -- If (X,d) is a Cauchy complete metric space and T: X -> X is a contracting map, then T has a unique fixed point.
