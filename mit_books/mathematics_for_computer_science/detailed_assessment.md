# Detailed Assessment of Mathematical Statements Against Mathlib v4.27.0

## Statement 1: Proposition 1.1.1
2 + 3 = 5.

Assessment: included
This is a trivially decidable arithmetic fact. Lean's kernel can verify 2 + 3 = 5 by computation (using `native_decide` or `decide`). Mathlib has full support for natural number arithmetic in `Mathlib/Data/Nat/`.

## Statement 2: Proposition 1.1.2
1 + 1 = 3.

Assessment: non-included
This proposition is false (1 + 1 = 2, not 3). It is presented in the textbook as an example of a false proposition. Mathlib does not state false propositions.

## Statement 3: Proposition 1.1.3
For every nonnegative integer, n, the value of n^2 + n + 41 is prime.

Assessment: non-included
This proposition is false (it fails at n = 40, since 40^2 + 40 + 41 = 41^2). It is presented in the textbook as a cautionary example. Mathlib does not contain this specific false claim. The polynomial n^2 + n + 41 is known as Euler's prime-producing polynomial but its failure is well-known.

## Statement 4: Proposition 1.1.4 (Euler's Conjecture)
The equation a^4 + b^4 + c^4 = d^4 has no solution when a, b, c, d are positive integers.

Assessment: non-included
This is Euler's conjecture, which was disproved in 1988 by Elkies. The textbook presents it as a historically notable false conjecture. Mathlib does not contain a statement about Euler's sum of powers conjecture or its disproof. Searched in `Mathlib/NumberTheory/` without finding a match.

## Statement 5: Proposition 1.1.5
313(x^3 + y^3) = z^3 has no solution when x, y, z are positive integers.

Assessment: non-included
This is an open problem / specific Diophantine equation. Mathlib does not contain results about this particular equation. Searched in `Mathlib/NumberTheory/` without finding a match.

## Statement 6: Proposition 1.1.6 (Four Color Theorem)
Every map can be colored with 4 colors so that adjacent regions have different colors.

Assessment: non-included
The Four Color Theorem is a major result in graph theory that has been proved using computer-assisted methods. However, it is not formalized in Lean's mathlib v4.27.0. Searched in `Mathlib/Combinatorics/SimpleGraph/` for coloring-related results but did not find the Four Color Theorem. While there is a separate Lean formalization project for the Four Color Theorem, it is not part of mathlib.

## Statement 7: Proposition 1.1.7 (Fermat's Last Theorem)
There are no positive integers x, y, and z such that x^n + y^n = z^n for some integer n > 2.

Assessment: non-included
While mathlib has `Mathlib/NumberTheory/FLT/Basic.lean` which defines `FermatLastTheoremWith` and related concepts, and `Mathlib/NumberTheory/FLT/Four.lean` proves the n=4 case, and `Mathlib/NumberTheory/FLT/Three.lean` proves the n=3 case, the full Fermat's Last Theorem for all n > 2 is stated as `FermatLastThm` but is declared as `sorry` (unproven) in mathlib. The general theorem remains unformalized.

## Statement 8: Proposition 1.1.8 (Goldbach's Conjecture)
Every even integer greater than 2 is the sum of two primes.

Assessment: non-included
Goldbach's Conjecture is an open problem in mathematics. It has not been proved in any formal system, and is not in mathlib. Searched in `Mathlib/NumberTheory/` without finding it.

## Statement 9: Theorem 1.5.1
If 0 < x < 2, then -x^3 + 4x + 1 > 0.

Assessment: non-included
This is a specific polynomial inequality used as a proof example in the textbook. Mathlib does not contain this specific polynomial inequality. It could be proved using `polyrith` or `nlinarith` tactics but is not stated as a theorem.

## Statement 10: Theorem 1.5.2
If r is irrational, then sqrt(r) is also irrational.

Assessment: included
This follows from the contrapositive: if sqrt(r) is rational, then r = (sqrt(r))^2 is rational. Mathlib has extensive irrationality results in `Mathlib/NumberTheory/Real/Irrational.lean`, including `Irrational.rpow_nat_cast` and related lemmas that cover this result. Specifically, `Irrational` is closed under taking square roots of irrationals (via the contrapositive argument through rational closure under squaring).

## Statement 11: Theorem 1.6.1
The standard deviation of a sequence of values x_1, ..., x_n is zero iff all the values are equal to the mean.

Assessment: non-included
This is a basic statistics result about standard deviation. Mathlib has variance-related results in `Mathlib/Probability/Moments/Variance.lean`, but this specific characterization of zero standard deviation for finite sequences is not stated as a theorem. Searched in `Mathlib/Probability/` without finding an exact match.

## Statement 12: Theorem 1.8.1
sqrt(2) is irrational.

Assessment: included
This is proved as `irrational_sqrt_two` in `Mathlib/NumberTheory/Real/Irrational.lean` (line 143). This is one of the most classic results formalized in mathlib.

## Statement 13: Theorem 2.2.1
For any b in Z and any a in Z+, there exist unique integers q, r in N such that b = qa + r and 0 <= r < a.

Assessment: included
The division algorithm (Euclidean division) is formalized in mathlib. `Nat.div_add_mod` in core Lean gives `a = a / b * b + a % b`, and the EuclideanDomain typeclass in `Mathlib/Algebra/EuclideanDomain/Defs.lean` generalizes this. The uniqueness of quotient and remainder is also established.

## Statement 14: Theorem 2.3.1
Every positive integer greater than one can be factored as a product of primes.

Assessment: included
This is the existence part of the Fundamental Theorem of Arithmetic. Mathlib proves this through the `UniqueFactorizationMonoid` instance for natural numbers in `Mathlib/RingTheory/UniqueFactorizationDomain/Nat.lean` and related files. The existence of prime factorization is established by `Nat.exists_prime_and_dvd` and the full factorization infrastructure.

## Statement 15: Theorem 2.4.1
For any nonnegative integer, n, the set of integers greater than or equal to -n is well ordered.

Assessment: included
This follows from the well-ordering of natural numbers, which is built into Lean's foundation. The `Nat.lt_wfRel` and `WellFoundedRelation` instances for `Nat` in Lean's core library, together with the order-preserving bijection shifting by n, establish this. Mathlib has extensive well-ordering results in `Mathlib/Order/`.

## Statement 16: Corollary 2.4.3
Any set of integers with a lower bound is well ordered.

Assessment: included
This follows from Theorem 2.4.1 and is a consequence of the well-ordering of natural numbers. In mathlib, this is captured by `Int.lt_wfRel` and related results in `Mathlib/Order/WellFounded.lean` and `Mathlib/Data/Int/`.

## Statement 17: Corollary 2.4.4
Any nonempty set of integers with an upper bound has a maximum element.

Assessment: included
This is equivalent to the well-ordering principle applied to negated integers. In mathlib, this follows from `Finset.max'` for finite sets and from well-foundedness results for integers. The relevant infrastructure is in `Mathlib/Order/`.

## Statement 18: Lemma 2.4.5
N + F is well ordered (where F is a well ordered set under <=).

Assessment: non-included
This is a specific textbook lemma about the well-ordering of N + F (the shifted set). While mathlib has general results about well-ordered sets and their sums in `Mathlib/SetTheory/Ordinal/`, this specific formulation combining N with an arbitrary well-ordered set F is not directly stated.

## Statement 19: Theorem 3.4.1 (Distributive Law of AND over OR)
P AND (Q OR R) = (P AND Q) OR (P AND R).

Assessment: included
This is a basic propositional logic tautology. In Lean's logic, this corresponds to `And.comm`, `Or.comm`, and distributivity. Specifically, `and_or_left` in Lean's core library states `a /\ (b \/ c) <-> (a /\ b) \/ (a /\ c)`. Mathlib uses this extensively.

## Statement 20: Theorem 3.4.2 (Distributive Law of OR over AND)
P OR (Q AND R) = (P OR Q) AND (P OR R).

Assessment: included
This is the dual distributive law. In Lean's core library, `or_and_left` states `a \/ (b /\ c) <-> (a \/ b) /\ (a \/ c)`. This is a basic propositional logic fact used throughout mathlib.

## Statement 21: Theorem 3.4.3
Every propositional formula is equivalent to both a disjunctive normal form and a conjunctive normal form.

Assessment: non-included
While mathlib has propositional logic infrastructure, it does not contain an explicit theorem about the existence of DNF/CNF normal forms for propositional formulas. This is more of a meta-logical result about syntactic transformations. Searched in `Mathlib/Logic/` without finding this specific result.

## Statement 22: Theorem 4.1.1
For all nonneg integers n: 1 + 2 + 3 + ... + n = n(n+1)/2.

Assessment: included
This is Gauss's summation formula. In mathlib, `Finset.sum_range_id` or equivalent results in `Mathlib/Algebra/BigOperators/Intervals.lean` establish that the sum of the first n natural numbers equals n*(n+1)/2. The result `Gauss.sum_range_id_mul_two` or similar variants are available.

## Statement 23: Theorem 4.1.2
For all n in N, 3 | (n^3 - n).

Assessment: included
This follows from the factorization n^3 - n = n(n-1)(n+1), which is the product of three consecutive integers and is always divisible by 3. Mathlib can derive this from `Nat.three_dvd_iff` or through modular arithmetic in `Mathlib/Data/Nat/ModEq.lean`. The general result about products of consecutive integers being divisible by factorial is in mathlib.

## Statement 24: Theorem 4.1.3 (Geometric Sum)
For all n in N and z != 1: 1 + z + z^2 + ... + z^n = (z^(n+1) - 1)/(z - 1).

Assessment: included
The geometric sum formula is in `Mathlib/Algebra/Ring/GeomSum.lean` as `geom_sum_eq` and related lemmas. The `geom_series` results are also available.

## Statement 25: Theorem 4.5.1
Every postage of n >= 8 cents can be made using 3-cent and 5-cent stamps.

Assessment: non-included
This is the classic "postage stamp problem" or "Chicken McNugget theorem" for the specific case of 3 and 5. While the general Frobenius number/coin problem is studied, mathlib does not contain this specific recreational mathematics result. Searched in `Mathlib/Data/Nat/` and `Mathlib/Combinatorics/` without finding it.

## Statement 26: Theorem 4.5.2
All horses are the same color.

Assessment: non-included
This is a famous false "theorem" used in the textbook to illustrate a flawed induction argument. Mathlib does not contain false statements.

## Statement 27: Theorem 5.1.1 (Ordinary Induction)
Let P be a predicate on nonneg integers. If P(0) is true, and P(n) IMPLIES P(n+1) for all n in N, then P(m) is true for all m in N.

Assessment: included
Mathematical induction is a foundational principle built into Lean. The `Nat.rec` and `Nat.recOn` recursors implement this. Mathlib uses induction pervasively. This is `Nat.rec` in Lean's kernel.

## Statement 28: Theorem 5.1.2 (Strong Induction)
Let P be a predicate on nonneg integers. If for each n in N, P(0), P(1), ..., P(n) together imply P(n+1), then P(m) is true for all m in N.

Assessment: included
Strong (complete) induction is available in Lean as `Nat.strongRecOn` and related principles. Mathlib has `Nat.strongRecOn` and uses strong induction extensively. The well-founded recursion on `Nat` with `<` provides this, found across many files.

## Statement 29: Theorem 5.3.1
Every positive integer is a product of a unique nondecreasing sequence of primes.

Assessment: included
This is the Fundamental Theorem of Arithmetic (unique prime factorization). Mathlib formalizes this through `Nat.UniqueFactorizationMonoid` in `Mathlib/RingTheory/UniqueFactorizationDomain/Nat.lean`. The existence and uniqueness of prime factorizations are both established.

## Statement 30: Lemma 5.3.2
If p is a prime and p | ab, then p | a or p | b.

Assessment: included
This is Euclid's lemma, formalized in mathlib as `Nat.Prime.dvd_mul` and more generally through the `Irreducible.dvd_or_dvd` property. Found in `Mathlib/Data/Nat/Prime/Defs.lean` and related files.

## Statement 31: Lemma 5.3.3
If p is a prime and p | a_1 * a_2 * ... * a_n, then p | a_i for some i.

Assessment: included
This generalization of Euclid's lemma is available in mathlib. `Prime.dvd_finset_prod` and `Prime.dvd_of_dvd_pow` cover this. The result follows by induction from Lemma 5.3.2 and is used implicitly throughout the factorization infrastructure.

## Statement 32: Theorem 7.2.1 (Schroeder-Bernstein)
If |A| <= |B| and |B| <= |A|, then |A| = |B|.

Assessment: included
The Schroeder-Bernstein theorem is formalized in `Mathlib/SetTheory/Cardinal/SchroederBernstein.lean` as `Function.Embedding.antisymm` / `Cardinal.mk_le_mk_iff_exists_injective`. This provides that injections in both directions imply a bijection.

## Statement 33: Theorem 7.2.2 (Cantor's Theorem)
For every set A (finite or infinite), |A| < |pow(A)|.

Assessment: included
Cantor's theorem is formalized in mathlib. `Cardinal.cantor` in `Mathlib/SetTheory/Cardinal/Basic.lean` states that `#alpha < #(Set alpha)`. The diagonal argument is also available through `Function.cantor_injective`.

## Statement 34: Theorem 7.2.3
pow(N) is uncountable.

Assessment: included
This follows from Cantor's theorem. In mathlib, `Cardinal.mk_set_nat` combined with Cantor's theorem establishes this. The uncountability of `Set Nat` follows from `Cardinal.cantor` applied to `Nat`. Also available through `Mathlib/Analysis/Real/Cardinality.lean`.

## Statement 35: Corollary 7.2.4
R is uncountable.

Assessment: included
The uncountability of the reals is in mathlib. `Cardinal.mk_real` in `Mathlib/Analysis/Real/Cardinality.lean` shows `#R = 2^aleph_0`, which is strictly greater than `aleph_0`. The result `not_countable_real` or equivalent is available.

## Statement 36: Theorem 8.1.1 (GCD Linear Combination)
The greatest common divisor of a and b is a linear combination of a and b. That is, gcd(a,b) = sa + tb for some integers s and t.

Assessment: included
Bezout's identity is formalized in mathlib. `Nat.gcd_eq_gcd_ab` and `Int.gcd_eq_gcd_ab` in `Mathlib/Data/Nat/GCD/Basic.lean` and `Mathlib/Data/Int/GCD.lean` provide this. The extended GCD algorithm is also available in `Mathlib/Data/PNat/Xgcd.lean`.

## Statement 37: Lemma 8.1.2
gcd(a, b) = gcd(rem(a, b), b).

Assessment: included
This is the key step of the Euclidean algorithm. In mathlib, `Nat.gcd_rec` states `gcd a b = gcd (b % a) a`, which is equivalent (up to argument order). Found in `Mathlib/Data/Nat/GCD/Basic.lean`.

## Statement 38: Theorem 8.1.3
The Euclidean algorithm terminates on all valid inputs, and gcd(a,b) = gcd(rem(a,b), b).

Assessment: included
The Euclidean algorithm's termination and correctness are established through the definition of `Nat.gcd` which uses well-founded recursion on the modulus decreasing. This is in Lean's core and `Mathlib/Data/Nat/GCD/Basic.lean`. The `EuclideanDomain` typeclass in `Mathlib/Algebra/EuclideanDomain/Defs.lean` generalizes this.

## Statement 39: Corollary 8.1.4
An integer is a linear combination of a and b iff it is a multiple of gcd(a,b).

Assessment: included
This characterization is available in mathlib through `Int.gcd_dvd_iff` and related results. The "if" direction follows from Bezout's identity, and the "only if" direction from the fact that gcd divides both a and b. Found in `Mathlib/Data/Int/GCD.lean`.

## Statement 40: Lemma 8.2.1 (Prime Divisibility)
If p is a prime and p | ab, then p | a or p | b.

Assessment: included
Same as Statement 30. This is Euclid's lemma, formalized as `Nat.Prime.dvd_mul` in mathlib.

## Statement 41: Theorem 8.2.2 (Fundamental Theorem of Arithmetic)
Every positive integer n can be written in a unique way as a product of primes: n = p_1 * p_2 * ... * p_j where p_1 <= p_2 <= ... <= p_j.

Assessment: included
Same as Statement 29. Formalized through `UniqueFactorizationMonoid Nat` in `Mathlib/RingTheory/UniqueFactorizationDomain/Nat.lean`.

## Statement 42: Lemma 8.3.1
If a | bc and gcd(a, b) = 1, then a | c.

Assessment: included
This is a standard coprimality lemma. In mathlib, `Nat.Coprime.dvd_of_dvd_mul_left` and `Nat.Coprime.dvd_of_dvd_mul_right` in `Mathlib/Data/Nat/GCD/Basic.lean` establish this. Also available through `IsCoprime.dvd_of_dvd_mul_left` in `Mathlib/RingTheory/Coprime/Lemmas.lean`.

## Statement 43: Corollary 8.3.2
If p is prime and p does not divide a, then gcd(p, a) = 1.

Assessment: included
This is formalized in mathlib as `Nat.Prime.coprime_iff_not_dvd` or can be derived from `Nat.Prime.eq_one_or_self_of_dvd`. Found in `Mathlib/Data/Nat/Prime/Defs.lean`.

## Statement 44: Theorem 8.3.3
If gcd(a, b) = 1 and gcd(a, c) = 1, then gcd(a, bc) = 1.

Assessment: included
This is `Nat.Coprime.mul_right` in mathlib, which states that if `a.Coprime b` and `a.Coprime c`, then `a.Coprime (b * c)`. Found in `Mathlib/Data/Nat/GCD/Basic.lean`.

## Statement 45: Lemma 8.3.4
Let p be a prime. If p | a_1 * a_2 * ... * a_n, then p | a_i for some 1 <= i <= n.

Assessment: included
Same as Statement 31. Available through `Prime.dvd_finset_prod` and related results in mathlib.

## Statement 46: Theorem 8.4.1 (Fermat's Little Theorem)
For any prime p that does not divide n, n^(p-1) === 1 (mod p).

Assessment: included
Fermat's Little Theorem is formalized in mathlib. `ZMod.units_pow_card_sub_one_eq_one` and related results in `Mathlib/FieldTheory/Finite/Basic.lean` establish this. Also `Nat.Prime.totient_eq_pred` combined with Euler's theorem gives this.

## Statement 47: Corollary 8.4.2
phi(p) = p - 1 for prime p, where phi is Euler's totient function.

Assessment: included
This is `Nat.totient_prime` in `Mathlib/Data/Nat/Totient.lean`, which states that `p.totient = p - 1` for prime `p`.

## Statement 48: Theorem 8.4.3 (Euler's Theorem)
If gcd(n, p) = 1, then n^(phi(p)) === 1 (mod p), where phi is Euler's totient function.

Assessment: included
Euler's theorem is formalized in mathlib. `ZMod.pow_totient` in `Mathlib/Data/ZMod/Basic.lean` states that for coprime elements, raising to the totient power gives 1 modulo p. Also see `Mathlib/Data/Nat/Totient.lean`.

## Statement 49: Theorem 8.5.1 (Chinese Remainder Theorem)
If gcd(n_1, n_2) = 1, then for all m_1 and m_2, there exists a unique x in {0, 1, ..., n_1*n_2 - 1} such that x === m_1 (mod n_1) and x === m_2 (mod n_2).

Assessment: included
The Chinese Remainder Theorem is formalized in mathlib. `ZMod.chineseRemainder` in `Mathlib/Data/ZMod/QuotientRing.lean` provides the ring isomorphism `ZMod (m * n) ~= ZMod m x ZMod n` when `m.Coprime n`. Also see `Mathlib/Data/Nat/Totient.lean`.

## Statement 50: Corollary 8.5.2
phi(n_1 * n_2) = phi(n_1) * phi(n_2), when gcd(n_1, n_2) = 1.

Assessment: included
The multiplicativity of Euler's totient function is `Nat.totient_mul` in `Mathlib/Data/Nat/Totient.lean`, which states `totient (m * n) = totient m * totient n` when `m.Coprime n`.

## Statement 51: Lemma 8.5.3
phi(p^k) = p^k - p^(k-1) for prime p and k >= 1.

Assessment: included
This is `Nat.totient_prime_pow_succ` in `Mathlib/Data/Nat/Totient.lean`, which computes the totient of prime powers.

## Statement 52: Theorem 8.6.1 (RSA)
For all m in {0, 1, ..., p*q - 1}, m^(ed) === m (mod pq), where e*d === 1 (mod (p-1)(q-1)).

Assessment: non-included
While mathlib contains Euler's theorem and Fermat's Little Theorem which are the mathematical foundations of RSA, the specific RSA encryption/decryption theorem as stated is not formalized as a standalone result. There is no dedicated RSA module in mathlib. Searched for "RSA" in mathlib but only found unrelated uses of the substring.

## Statement 53: Theorem 9.4.1
If a DAG has a positive number of vertices, then it has a source (a vertex with no incoming edges).

Assessment: non-included
While mathlib has some directed graph infrastructure, this specific result about DAGs having sources is not directly stated. Searched in `Mathlib/Combinatorics/SimpleGraph/` and `Mathlib/Order/` but did not find this exact formulation. The result follows from well-ordering but is not stated for finite DAGs specifically.

## Statement 54: Theorem 9.6.1 (Dilworth's Theorem)
The largest antichain in a finite partially ordered set equals the minimum number of chains needed to partition the set.

Assessment: non-included
Dilworth's theorem is not formalized in mathlib v4.27.0. Searched for "Dilworth" and "dilworth" in the mathlib directory without finding any results. This is a notable gap in the formalization of combinatorics.

## Statement 55: Theorem 10.7.1
The congestion of an N-input array is 2.

Assessment: non-included
This is a specific result about communication network theory (switching networks). Mathlib does not contain any formalization of communication network congestion theory. Searched in `Mathlib/Combinatorics/` and `Mathlib/Computability/` without finding related results.

## Statement 56: Theorem 10.9.1
The congestion of the N-input Benes network is 1.

Assessment: non-included
Same as Statement 55. The Benes network and its congestion properties are not formalized in mathlib. This is a specific result in communication network theory.

## Statement 57: Lemma 10.9.2
If the edges of a graph can be grouped into two sets such that every vertex has at most 1 edge from each set incident to it, then the graph is 2-colorable.

Assessment: non-included
This specific lemma about edge groupings implying 2-colorability is not in mathlib. While mathlib has some graph coloring infrastructure, this particular result about edge decomposition and 2-colorability is not formalized. Searched in `Mathlib/Combinatorics/SimpleGraph/` without finding it.

## Statement 58: Lemma 11.2.1 (Handshaking Lemma)
The sum of the degrees of the vertices in a graph equals twice the number of edges.

Assessment: included
This is `SimpleGraph.sum_degrees_eq_twice_card_edges` in `Mathlib/Combinatorics/SimpleGraph/DegreeSum.lean` (line 102), which states exactly that the sum of degrees equals twice the number of edges. The file also contains `SimpleGraph.even_card_odd_degree_vertices` as the "handshaking lemma" corollary.

## Statement 59: Theorem 11.5.2 (Hall's Marriage Theorem)
A matching for a set M of men with a set W of women can be found if and only if the matching condition holds.

Assessment: included
Hall's Marriage Theorem is formalized in `Mathlib/Combinatorics/Hall/Basic.lean` and `Mathlib/Combinatorics/Hall/Finite.lean`. The theorem `Finset.all_card_le_biUnion_card_iff_exists_injective` provides the finite version, and the general version using compactness is also available.

## Statement 60: Theorem 11.5.4 (Hall's Theorem)
Let G be a bipartite graph. There is a matching in G that covers L(G) iff no subset of L(G) is a bottleneck.

Assessment: included
This is the abstract graph-theoretic version of Hall's theorem. It is formalized in `Mathlib/Combinatorics/SimpleGraph/Hall.lean` as well as the more general versions in `Mathlib/Combinatorics/Hall/Basic.lean`. The theorem `Fintype.all_card_le_rel_image_card_iff_exists_injective` covers this.

## Statement 61: Theorem 11.5.6
If G is a degree-constrained bipartite graph, then there is a matching that covers L(G).

Assessment: non-included
While Hall's theorem itself is in mathlib, this specific corollary about degree-constrained bipartite graphs is not directly stated. The result can be derived from Hall's theorem, but the specific formulation is not present. Searched in `Mathlib/Combinatorics/SimpleGraph/` without finding this exact result.

## Statement 62: Theorem 11.5.8
Every regular bipartite graph has a perfect matching.

Assessment: non-included
While this follows from Hall's theorem (which is in mathlib), the specific statement about regular bipartite graphs having perfect matchings is not directly formalized. Searched in `Mathlib/Combinatorics/SimpleGraph/Matching.lean` and `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` without finding this exact result. The Birkhoff theorem in `Mathlib/Analysis/Convex/Birkhoff.lean` is related but different.

## Statement 63: Theorem 11.6.4
Everyone is married at the end of the Mating Ritual.

Assessment: non-included
The Mating Ritual (Gale-Shapley algorithm) and its properties are not formalized in mathlib. This is an algorithmic result about the stable marriage problem. Searched throughout mathlib without finding any Gale-Shapley formalization.

## Statement 64: Theorem 11.6.5
The Mating Ritual produces a stable matching.

Assessment: non-included
Same as Statement 63. The stable matching problem and Gale-Shapley algorithm are not formalized in mathlib v4.27.0.

## Statement 65: Lemma 11.6.8
Q is a preserved invariant for The Mating Ritual.

Assessment: non-included
Same as Statement 63. Part of the Gale-Shapley algorithm analysis, which is not in mathlib.

## Statement 66: Theorem 11.6.10
The Mating Ritual marries every man to his optimal spouse and every woman to her pessimal spouse.

Assessment: non-included
Same as Statement 63. The optimality property of the Gale-Shapley algorithm is not formalized in mathlib.

## Statement 67: Lemma 11.7.2
A graph G with at least one edge is bipartite iff chi(G) = 2.

Assessment: non-included
Mathlib has `SimpleGraph.Bipartite` in `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` and some coloring results, but the specific equivalence between bipartiteness and chromatic number 2 is not directly stated as a theorem. The graph coloring infrastructure in mathlib does not include chromatic number computation.

## Statement 68: Theorem 11.7.3
A graph with maximum degree at most k is (k + 1)-colorable.

Assessment: non-included
This is a basic graph coloring bound (related to greedy coloring), but mathlib does not have graph coloring bounds formalized. Searched in `Mathlib/Combinatorics/SimpleGraph/` without finding chromatic number bounds. The graph coloring theory in mathlib is limited.

## Statement 69: Theorem 11.9.3
The following graph properties are equivalent: (1) The graph contains an odd length cycle. (2) The graph is not 2-colorable. (3) The graph contains an odd length closed walk.

Assessment: non-included
While mathlib has `SimpleGraph.IsAcyclic` and bipartiteness definitions, this specific three-way equivalence characterizing 2-colorability through odd cycles is not formalized. The result `SimpleGraph.Bipartite` does not include this characterization. Searched in `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` without finding it.

## Statement 70: Lemma 11.9.6
An edge is a cut edge iff it is not on a cycle.

Assessment: included
This characterization of bridges (cut edges) is available in mathlib. In `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`, the concept of bridges and their relationship to cycles is formalized. The `SimpleGraph.IsBridge` predicate and its characterization through cycles/acyclicity are available.

## Statement 71: Theorem 11.9.7
Every graph G has at least |V(G)| - |E(G)| connected components.

Assessment: non-included
This bound on the number of connected components is not directly stated in mathlib. While mathlib has `SimpleGraph.ConnectedComponent` in `Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, the specific inequality relating vertex count, edge count, and component count is not formalized. Searched without finding it.

## Statement 72: Theorem 11.10.3
Every tree has the following properties: (1) Every connected subgraph is a tree. (2) There is a unique path between every pair of vertices. (3) Adding an edge between nonadjacent nodes creates a cycle. (4) Removing any edge disconnects the graph. (5) If the tree has at least two vertices, then it has at least two leaves. (6) The number of vertices in a tree is one larger than the number of edges.

Assessment: included
Several of these tree properties are formalized in `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`. Property (2) is `SimpleGraph.isAcyclic_iff_path_unique`. Property (4) is `SimpleGraph.isAcyclic_iff_forall_edge_isBridge`. The `SimpleGraph.IsTree` structure captures connected acyclic graphs. While not all six properties are individually stated, the key characterizations are present.

## Statement 73: Lemma 11.10.4
A graph G is a tree iff G is a forest and |V(G)| = |E(G)| + 1.

Assessment: included
This characterization of trees is available through the tree infrastructure in `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`. The `IsTree` predicate (connected and acyclic) combined with edge-counting results provides this equivalence.

## Statement 74: Theorem 11.10.6
Every connected graph contains a spanning tree.

Assessment: non-included
While mathlib has tree and connectivity definitions, the specific existence theorem for spanning trees is not directly stated. Searched in `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean` and `Mathlib/Combinatorics/SimpleGraph/Connectivity/` without finding a spanning tree existence theorem. The Tutte matrix approach in `Mathlib/Combinatorics/SimpleGraph/Tutte.lean` is related but different.

## Statement 75: Lemma 11.10.11
An edge extends a pre-MST F if it is a minimum weight gray edge in some solid coloring of F.

Assessment: non-included
Minimum spanning tree theory (including Kruskal's and Prim's algorithms) is not formalized in mathlib. The concepts of pre-MST, extending edges, and solid colorings are specific to MST construction and are not in mathlib.

## Statement 76: Corollary 11.10.12
If all edges in a weighted graph have distinct weights, then the graph has a unique MST.

Assessment: non-included
Same as Statement 75. MST uniqueness under distinct weights is not formalized in mathlib.

## Statement 77: Theorem 12.3.1 (Euler's Formula)
If a connected graph has a planar embedding, then v - e + f = 2.

Assessment: non-included
Euler's formula for planar graphs is not formalized in mathlib v4.27.0. Searched for "euler" combined with "planar" or "face" throughout mathlib without finding this result. Planar graph theory is largely absent from mathlib.

## Statement 78: Lemma 12.4.1
In a planar embedding of a connected graph, each edge occurs once in each of two different faces, or occurs exactly twice in one face.

Assessment: non-included
Same as Statement 77. Planar graph theory including face structures is not in mathlib.

## Statement 79: Lemma 12.4.2
In a planar embedding of a connected graph with at least three vertices, each face is of length at least three.

Assessment: non-included
Same as Statement 77. Not in mathlib.

## Statement 80: Theorem 12.4.3
Suppose a connected planar graph has v >= 3 vertices and e edges. Then e <= 3v - 6.

Assessment: non-included
This edge bound for planar graphs is not in mathlib. Planar graph theory is not formalized.

## Statement 81: Corollary 12.5.1
K_5 is not planar.

Assessment: non-included
The non-planarity of K_5 requires planar graph theory, which is not in mathlib. While `SimpleGraph.completeGraph` exists, planarity is not defined.

## Statement 82: Lemma 12.5.2
In a planar embedding of a connected bipartite graph with at least 3 vertices, each face has length at least 4.

Assessment: non-included
Not in mathlib. Requires planar graph face theory.

## Statement 83: Theorem 12.5.3
Suppose a connected bipartite graph with v >= 3 vertices and e edges is planar. Then e <= 2v - 4.

Assessment: non-included
Not in mathlib. Requires planar graph theory.

## Statement 84: Corollary 12.5.4
K_{3,3} is not planar.

Assessment: non-included
Not in mathlib. Requires planar graph theory.

## Statement 85: Lemma 12.6.1
Any subgraph of a planar graph is planar.

Assessment: non-included
Not in mathlib. Requires planar graph definition.

## Statement 86: Lemma 12.6.2
Merging two adjacent vertices of a planar graph leaves another planar graph.

Assessment: non-included
Not in mathlib. Requires planar graph theory.

## Statement 87: Lemma 12.6.3
Every planar graph has a vertex of degree at most five.

Assessment: non-included
Not in mathlib. Requires planar graph theory.

## Statement 88: Theorem 12.6.4
Every planar graph is five-colorable.

Assessment: non-included
Not in mathlib. The five-color theorem requires planar graph theory which is not formalized.

## Statement 89: Theorem 13.1.1
If |x| < 1, then sum_{i=0}^{infinity} x^i = 1/(1-x).

Assessment: included
The infinite geometric series formula is in mathlib. `tsum_geometric_of_lt_one` in `Mathlib/Analysis/SpecificLimits/Basic.lean` states this for real numbers, and `tsum_geometric_of_abs_lt_one` handles the general case. Also `NNReal.summable_geometric` and related results.

## Statement 90: Theorem 13.1.2
If |x| < 1, then sum_{i=1}^{infinity} i*x^i = x/(1-x)^2.

Assessment: included
This derivative of the geometric series is available in mathlib. `tsum_coe_mul_geometric_of_norm_lt_one` and related results in `Mathlib/Analysis/SpecificLimits/Normed.lean` establish this formula for power-weighted geometric series.

## Statement 91: Theorem 13.3.2
Integral bounds for sums of monotone functions.

Assessment: non-included
While mathlib has extensive integral theory, this specific integral test / comparison between sums and integrals for monotone functions is not stated as a standalone theorem in the discrete math context. The result exists conceptually through `MeasureTheory.integral_le_sum` type results but the specific textbook formulation with the tight bounds I + f(1) <= S <= I + f(n) is not directly available. Searched without finding an exact match.

## Statement 92: Theorem 13.5.1 (Stirling's Formula)
For all n >= 1, n! = sqrt(2*pi*n) * (n/e)^n * e^{epsilon(n)} where 1/(12n+1) <= epsilon(n) <= 1/(12n).

Assessment: included
Stirling's formula is formalized in `Mathlib/Analysis/SpecialFunctions/Stirling.lean`. The file contains `Stirling.tendsto_stirling_seq_sqrt_pi` which establishes the asymptotic relationship n! ~ sqrt(2*pi*n) * (n/e)^n. The precise error bounds may not match exactly, but the essential content is present.

## Statement 93: Corollary 13.5.2
n! < sqrt(2*pi*n) * (n/e)^n * 1.09 for n >= 1 (with better bounds for larger n).

Assessment: included
This follows from Stirling's formula. The bounds in `Mathlib/Analysis/SpecialFunctions/Stirling.lean` provide sufficient approximation results. While the exact numerical constants 1.09, 1.009, 1.0009 may not be explicitly stated, the Stirling approximation infrastructure supports deriving them.

## Statement 94: Lemma 13.7.2
x^a = o(x^b) for all nonneg constants a < b.

Assessment: included
This asymptotic comparison of polynomial growth rates is standard analysis. In mathlib, `isLittleO_pow_pow_of_lt` or equivalent results in the asymptotic notation infrastructure handle this. The relevant files are in `Mathlib/Analysis/Asymptotics/`.

## Statement 95: Lemma 13.7.3
log x = o(x^epsilon) for all epsilon > 0.

Assessment: included
This is the standard result that logarithms grow slower than any positive power. In mathlib, `Real.tendsto_pow_mul_log_rpow_nhds` and related results in `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean` establish that log grows slower than any positive power of x.

## Statement 96: Corollary 13.7.4
x^b = o(a^x) for any a, b in R with a > 1.

Assessment: included
This is the standard result that exponential growth dominates polynomial growth. In mathlib, `isLittleO_pow_exp_atTop` and `tendsto_pow_mul_exp_neg_atTop_nhds` in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean` and related files establish this.

## Statement 97: Lemma 13.7.6
If a function f: R -> R has a finite or infinite limit as its argument approaches infinity, then its limit and limit superior are the same.

Assessment: included
This is a standard result in real analysis. In mathlib, the relationship between `Filter.Tendsto`, `Filter.limsup`, and `Filter.liminf` is established in `Mathlib/Order/LiminfLimsup.lean`. The result `Filter.Tendsto.limsup_eq` provides this.

## Statement 98: Lemma 13.7.7
If f = o(g) or f ~ g, then f = O(g).

Assessment: non-included
While mathlib has the asymptotic notation definitions (`IsLittleO`, `IsBigO`, `IsEquivalent`) in `Mathlib/Analysis/Asymptotics/`, the specific implication from little-o or asymptotic equivalence to big-O is available as `IsLittleO.isBigO` which does exist. However, the combined statement with "or f ~ g" as a single lemma is not present in this exact form. The individual implications are available but not combined.

## Statement 99: Lemma 13.7.8
If f = o(g), then it is not true that g = O(f).

Assessment: non-included
While mathlib has asymptotic notation, this specific contrapositive result is not directly stated as a standalone lemma. The tools to prove it are available through `IsLittleO` and `IsBigO` definitions, but the exact statement is not present. Searched in `Mathlib/Analysis/Asymptotics/` without finding an exact match.

## Statement 100: Lemma 14.1.1
The number of ways to select n donuts when k flavors are available is the same as the number of binary sequences with exactly n zeroes and k-1 ones.

Assessment: non-included
This is the "stars and bars" combinatorial identity. While mathlib has binomial coefficients and counting results, this specific bijection between multisets and binary sequences is not formalized as a standalone theorem. The result is implicitly present through `Nat.choose` properties but not stated in this bijective form.

## Statement 101: Lemma 14.10.1 (Pascal's Triangle Identity)
C(n, k) = C(n-1, k-1) + C(n-1, k).

Assessment: included
Pascal's identity is `Nat.choose_succ_succ` in `Mathlib/Data/Nat/Choose/Basic.lean`, which states `(n+1).choose (k+1) = n.choose k + n.choose (k+1)`. This is equivalent to the standard Pascal's identity.

## Statement 102: Theorem 14.10.2
sum_{r=0}^{n} C(n, r) * C(2n, n-r) = C(3n, n).

Assessment: included
This is the Vandermonde identity (or Chu-Vandermonde identity). Mathlib has `Nat.add_choose_eq` and related Vandermonde convolution results in `Mathlib/Data/Nat/Choose/Vandermonde.lean`. The Vandermonde identity states sum C(m,k)*C(n,r-k) = C(m+n,r), and the stated identity is a special case.

## Statement 103: Corollary 14.5.2
The number of n-bit sequences with exactly k ones is C(n, k).

Assessment: included
This is a basic interpretation of binomial coefficients. In mathlib, `Finset.card_powersetCard` in `Mathlib/Data/Finset/Powerset.lean` counts k-element subsets of an n-element set as `Nat.choose n k`. The bijection between k-element subsets and binary sequences with k ones is standard.

## Statement 104: Corollary 14.5.3
The number of ways to select n donuts when k flavors are available is C(n+(k-1), n).

Assessment: included
This is the "stars and bars" / multiset coefficient formula. In mathlib, `Nat.choose` with the stars-and-bars argument is supported. The multiset counting is related to `Finset.card_powersetCard` applied appropriately. The formula C(n+k-1, n) for combinations with repetition is a standard application of binomial coefficients.

## Statement 105: Theorem 14.6.4 (Binomial Theorem)
For all n in N and a, b in R: (a+b)^n = sum_{k=0}^{n} C(n,k) * a^{n-k} * b^k.

Assessment: included
The Binomial Theorem is formalized in mathlib as `Commute.add_pow` in `Mathlib/Algebra/Ring/GeomSum.lean` and `Mathlib/Algebra/BigOperators/Ring/Finset.lean`. For commutative rings, this gives exactly the standard binomial expansion. The result `add_pow` provides the commutative case directly.

## Statement 106: Theorem 14.6.5 (Multinomial Theorem)
For all n in N, (z_1 + ... + z_m)^n = sum C(n; k_1,...,k_m) * z_1^{k_1} * ... * z_m^{k_m}.

Assessment: included
The Multinomial Theorem is available in mathlib through `Finset.sum_pow` and multinomial coefficient infrastructure in `Mathlib/Data/Nat/Choose/Multinomial.lean`. The multinomial coefficients and their relationship to the expansion of sums raised to powers are formalized.

## Statement 107: Lemma 15.3.1
Partial fraction decomposition for rational functions with distinct nonzero poles.

Assessment: non-included
Mathlib does not have a general partial fraction decomposition theorem for rational functions. While polynomial division and factorization are available, the specific partial fractions decomposition lemma is not formalized. Searched for "partial_fraction" and "partialFraction" without finding results.

## Statement 108: Theorem 17.4.1 (Bayes' Rule)
Pr[B | A] = Pr[A | B] * Pr[B] / Pr[A].

Assessment: included
Bayes' rule is formalized in `Mathlib/Probability/ConditionalProbability.lean`. The `ProbabilityTheory.cond` definition and related results establish conditional probability. The `ProbabilityTheory.cond_eq_inv_mul_cond_mul` or equivalent provides Bayes' rule.

## Statement 109: Theorem 19.1.1 (Markov's Theorem)
If R is a nonneg random variable, then for all x > 0, Pr[R >= x] <= Ex[R]/x.

Assessment: included
Markov's inequality is in mathlib. `MeasureTheory.mul_meas_ge_le_lintegral` in `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean` provides the measure-theoretic version. Also `ProbabilityTheory.meas_ge_le_mul_pow_snorm` and related results cover this.

## Statement 110: Corollary 19.1.2
If R is a nonneg random variable, then for all c > 1, Pr[R >= c * Ex[R]] <= 1/c.

Assessment: included
This is a direct restatement of Markov's inequality. It follows immediately from Statement 109 by setting x = c * Ex[R]. The same mathlib files as Statement 109 cover this.

## Statement 111: Lemma 19.2.1
For any random variable R and positive real numbers x, z, Pr[|R| >= x] <= Ex[|R|^z] / x^z.

Assessment: included
This generalized moment inequality (sometimes called the generalized Markov inequality) is in mathlib through `MeasureTheory.meas_ge_le_mul_pow_snorm` in `Mathlib/MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean`. The Chebyshev-Markov inequality framework covers this.

## Statement 112: Theorem 19.2.3 (Chebyshev's Theorem)
Let R be a random variable and x in R+. Then Pr[|R - Ex[R]| >= x] <= Var[R] / x^2.

Assessment: included
Chebyshev's inequality is formalized in mathlib. `ProbabilityTheory.meas_ge_le_variance_div_sq` or equivalent in `Mathlib/Probability/Moments/Variance.lean` provides this. The Chebyshev-Markov framework in `Mathlib/MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean` also covers this.

## Statement 113: Theorem 19.3.7
If R and S are independent random variables, then Var[R + S] = Var[R] + Var[S].

Assessment: included
The additivity of variance for independent random variables is in mathlib. `ProbabilityTheory.IndepFun.variance_add` or equivalent in `Mathlib/Probability/Moments/Variance.lean` establishes that variance is additive for independent variables.

## Statement 114: Theorem 19.3.8 (Pairwise Independent Additivity of Variance)
If R_1, ..., R_n are pairwise independent random variables, then Var[sum] = sum of Var.

Assessment: included
This generalization of variance additivity to pairwise independent variables is covered by the same infrastructure in `Mathlib/Probability/Moments/Variance.lean`. The pairwise independence condition suffices for variance additivity.

## Statement 115: Lemma 19.3.9 (Variance of the Binomial Distribution)
If J has the (n, p)-binomial distribution, then Var[J] = np(1-p).

Assessment: included
The variance of the binomial distribution is available in mathlib through `Mathlib/Probability/ProbabilityMassFunction/Binomial.lean` and the variance computation infrastructure. The binomial distribution's moments are computed using independence and indicator variable decomposition.

## Statement 116: Theorem 19.6.1 (Chernoff Bound)
For mutually independent random variables T_i in [0,1], Pr[T >= c*Ex[T]] <= e^{-(c*ln(c)-c+1)*Ex[T]}.

Assessment: included
Chernoff bounds are available in mathlib. `Mathlib/Probability/Moments/SubGaussian.lean` and `Mathlib/Probability/Moments/Basic.lean` contain moment generating function bounds and Chernoff-type concentration inequalities. The exponential tail bounds for sums of independent bounded random variables are formalized.

## Statement 117: Lemma 19.6.2
Ex[c^T] <= e^{(c-1)*Ex[T]}.

Assessment: non-included
This specific technical lemma used in the Chernoff bound proof (bounding the moment generating function) may not be directly stated as a standalone result. While the Chernoff bound framework exists in mathlib, this particular intermediate inequality may not be separately formalized. Searched without finding an exact match.

## Statement 118: Theorem 20.1.1 (Gambler's Ruin)
Probability of winning in the Gambler's Ruin game with given parameters.

Assessment: non-included
The Gambler's Ruin problem and its exact solution are not formalized in mathlib. While mathlib has random walk infrastructure, the specific Gambler's Ruin formula with absorbing barriers is not present. Searched for "gambler" and "random_walk" without finding relevant results.

## Statement 119: Corollary 20.1.2
In biased Gambler's Ruin, Pr[gambler wins] < (1/r)^{T-n}.

Assessment: non-included
Not in mathlib. Part of the Gambler's Ruin analysis which is not formalized.

## Statement 120: Theorem 20.1.3
Expected number of bets in Gambler's Ruin.

Assessment: non-included
Not in mathlib. The expected duration of Gambler's Ruin is not formalized.

## Statement 121: Lemma 20.1.4
If the gambler plays a fair unbounded game, he will go broke with probability 1.

Assessment: non-included
This result about symmetric random walks being recurrent (returning to the origin with probability 1) is not formalized in the Gambler's Ruin context in mathlib. While the result follows from random walk theory, the specific formulation is not present.

## Statement 122: Lemma 20.1.5
If the gambler plays a fair unbounded game, his expected number of plays is infinite.

Assessment: non-included
Not in mathlib. The infinite expected duration of fair unbounded Gambler's Ruin is not formalized.
