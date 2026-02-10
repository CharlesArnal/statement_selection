# Detailed Assessment: Topics in Algebraic Combinatorics

## Statement 1: Lemma 8.1
**Assessment: non-included**
This lemma characterizes Hasse walks of a given type from the empty partition to a partition lambda in Young's lattice. Mathlib has basic Young diagram definitions in `Mathlib/Combinatorics/Young/YoungDiagram.lean` (including a distributive lattice structure, rows, columns, and an equivalence with weakly decreasing lists), but there is no formalization of Hasse walks, up/down steps in Young's lattice, or the walk-type characterization. Searched: `Combinatorics/Young/`, `Order/`, and broad mathlib searches for "Hasse walk", "HasseWalk", "hasse_walk" -- all yielded no results. The concept of Hasse walks on Young's lattice is entirely absent from mathlib v4.27.0.

## Statement 2: Lemma 8.2
**Assessment: non-included**
This lemma establishes the commutation relation D_{i+1}U_i - U_{i-1}D_i = I_i for up and down operators on the real vector space spanned by partitions of weight i (RY_i). Mathlib has no formalization of up/down operators on Young's lattice, the linear algebra of partition spaces RY_i, or the DU-UD commutation relation. Searched: `Combinatorics/Young/`, "order_raising", "orderRaising", "Young lattice" -- no matches. These operators are specific to the representation-theoretic approach to Young's lattice and are not present in mathlib.

## Statement 3: Theorem 8.3
**Assessment: non-included**
This theorem computes the coefficient alpha(w, lambda) of a Hasse walk in terms of f^lambda (the number of standard Young tableaux of shape lambda) and a product over down steps. Mathlib has semistandard Young tableaux in `Mathlib/Combinatorics/Young/SemistandardTableau.lean`, but no standard tableaux, no counting formula f^lambda (hook-length formula or otherwise), and no Hasse walk coefficients. Searched: "standardTableau", "hookLengthFormula", "numStandardTableaux", "f_lambda" -- no results.

## Statement 4: Corollary 8.4
**Assessment: non-included**
This corollary states the RSK-related identity sum_{lambda |- n} (f^lambda)^2 = n!. Mathlib has no formalization of f^lambda (number of standard Young tableaux), the RSK correspondence, or this identity. Searched: "RSK", "Robinson.Schensted", "hook.*length" -- no results.

## Statement 5: Lemma 8.5
**Assessment: non-included**
This lemma gives a closed form for b_{ij}(l), counting certain Hasse walk types. This is deeply embedded in the Hasse walk theory on Young's lattice, which is entirely absent from mathlib. Same reasoning as Statements 1-4.

## Statement 6: Theorem 8.6
**Assessment: non-included**
This theorem provides a formula for beta(l, lambda), the total number of Hasse walks of length l from empty to lambda. Again part of the Hasse walk theory, which is not formalized in mathlib.

## Statement 7: Corollary 8.7
**Assessment: non-included**
This corollary states that the total number of Hasse walks of length 2m from empty to empty equals the double factorial 1*3*5*...*(2m-1). While mathlib does have double factorials in `Mathlib/Data/Nat/Factorial/DoubleFactorial.lean`, the Hasse walk counting result that connects to this formula is not present. The combinatorial identity itself (as a statement about walks on Young's lattice) is not formalized.

## Statement 8: Theorem 8.8
**Assessment: non-included**
This theorem computes the eigenvalues of the transfer matrix Y_{j-1,j} in terms of p(j-s) - p(j-s-1), where p is the partition function. This spectral analysis of the Young's lattice transfer matrices is not formalized in mathlib. The partition function p(n) itself does not appear to have an explicit counting function in mathlib, and the eigenvalue analysis is entirely absent.

## Statement 9: Corollary 8.9
**Assessment: non-included**
This corollary counts round-trip insertion-deletion sequences on partitions using eigenvalues of transfer matrices. This depends on Statement 8 and the spectral theory of Young's lattice, none of which is in mathlib.

## Statement 10: Proposition 4.4
**Assessment: non-included**
This proposition states that a graded poset with a chain of order-matchings from P_0 to P_j and from P_n down to P_j is rank-unimodal and Sperner. Mathlib has no formalization of the concepts of "rank-unimodal", "Sperner property" for general graded posets, or "order-matchings" between levels of a graded poset. Searched: "order.matching", "orderMatching", "rank.unimodal", "rankUnimodal", "Sperner.*property" -- no results. The graded poset framework from the textbook is not present in mathlib.

## Statement 11: Lemma 4.5
**Assessment: non-included**
This lemma shows that an injective (resp. surjective) order-raising linear operator implies the existence of an order-matching. Same concepts as Statement 10 (order-raising operators, order-matchings) which are not in mathlib.

## Statement 12: Lemma 4.6
**Assessment: non-included**
This lemma establishes the commutation relation D_{i+1}U_i - U_{i-1}D_i = (n-2i)I_i for operators on the boolean algebra B_n. While mathlib has extensive boolean algebra infrastructure in `Mathlib/Order/BooleanAlgebra/`, the specific up/down operators and their commutation relations as linear transformations on the level spaces of B_n are not formalized.

## Statement 13: Theorem 4.7
**Assessment: non-included**
This theorem states that U_i is one-to-one if i < n/2 and onto if i >= n/2 for the boolean algebra B_n. This is the key technical result used to prove the Sperner property, but the operator-theoretic proof framework is not in mathlib (even though the conclusion -- the Sperner property -- is proved via a different method in LYM.lean).

## Statement 14: Corollary 4.8
**Assessment: included**
The boolean algebra B_n has the Sperner property. In mathlib, this is formalized as `IsAntichain.sperner` in `/Users/vivc/code/Lean/statement_selection/mathlib_coverage/mathlib/Mathlib/Combinatorics/SetFamily/LYM.lean`. The theorem states: the size of any antichain in `Finset alpha` is bounded by the size of the maximal layer `C(n, n/2)`, where n = Fintype.card alpha. Since `Finset alpha` ordered by inclusion is exactly the boolean algebra B_n, this is precisely the Sperner property of B_n. The proof in mathlib uses the LYM inequality rather than the operator-theoretic approach of the textbook, but the result is the same.

## Statement 15: Proposition 5.6
**Assessment: non-included**
This proposition states that the quotient poset B_n/G (under a group action) is graded of rank n and rank-symmetric. Mathlib has no formalization of quotient posets under group actions, nor the concepts of "rank-symmetric" for posets. Searched: "quotient.*poset", "Poset.*quotient", "rank_symmetric", "rankSymmetric" -- no results.

## Statement 16: Lemma 5.7
**Assessment: non-included**
This lemma describes a basis for the G-invariant subspace of R(B_n)_i. This depends on the quotient poset framework (Statement 15) which is not in mathlib.

## Statement 17: Lemma 5.8
**Assessment: non-included**
This lemma shows that the up operator U_i preserves G-invariant subspaces. Same framework as Statements 15-16, not in mathlib.

## Statement 18: Theorem 5.9
**Assessment: non-included**
This theorem states that B_n/G is rank-symmetric, rank-unimodal, and Sperner for any subgroup G of S_n. The quotient poset framework and these Sperner-theoretic properties for quotient posets are not in mathlib.

## Statement 19: Theorem 5.10
**Assessment: non-included**
Part (a) states that the sequence counting nonisomorphic simple graphs with m vertices by number of edges is symmetric and unimodal. Part (b) is a Sperner-type result. Mathlib has simple graphs in `Mathlib/Combinatorics/SimpleGraph/` but no counting of nonisomorphic graphs, nor unimodality/Sperner results in this context. Searched: "nonisomorphic.*graph", "graph.*isomorphism.*count" -- no results.

## Statement 20: Conjecture (Circulant Hadamard)
**Assessment: non-included**
The conjecture that an n x n circulant Hadamard matrix exists only for n = 1 or n = 4. Mathlib has circulant matrices in `Mathlib/LinearAlgebra/Matrix/Circulant.lean` and the Hadamard (entrywise) product in `Mathlib/LinearAlgebra/Matrix/Hadamard.lean`, but has no concept of a "Hadamard matrix" (a matrix with +/-1 entries satisfying HH^T = nI). The circulant Hadamard conjecture is not formalized. Searched: "circulant.*Hadamard", "Hadamard.*circulant" -- no results.

## Statement 21: Theorem 1
**Assessment: non-included**
This theorem states there is no circulant Hadamard matrix of order 2^k for k > 3. As noted for Statement 20, Hadamard matrices as a concept are not defined in mathlib. Searched: "Hadamard" found only `Matrix.hadamard` (entrywise product) and `Analysis.Complex.Hadamard` (three-lines lemma), neither of which relates to Hadamard matrices in the combinatorial sense.

## Statement 22: Lemma 2
**Assessment: included**
The polynomial p_k(x) = x^{2^{k-1}} + 1 is irreducible over Q. This polynomial is the cyclotomic polynomial cyclotomic(2^k). Mathlib proves that all cyclotomic polynomials are irreducible over Z (and Q) in `/Users/vivc/code/Lean/statement_selection/mathlib_coverage/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean`:
- `Polynomial.cyclotomic.irreducible`: `cyclotomic n Z` is irreducible for any n > 0.
- `Polynomial.cyclotomic.irreducible_rat`: `cyclotomic n Q` is irreducible for any n > 0.
The identification cyclotomic(2^k) = X^{2^{k-1}} + 1 follows from `cyclotomic_prime_pow_eq_geom_sum` in `Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean` applied with p = 2 (the geometric sum has only 2 terms: X^{2^{k-1}} + 1).

## Statement 23: Lemma 3
**Assessment: non-included**
This lemma states that the eigenvalues gamma_j of a circulant Hadamard matrix all have absolute value sqrt(n). This is specific to circulant Hadamard matrix theory, which is not formalized in mathlib. While mathlib has circulant matrices, it does not have Hadamard matrices or their eigenvalue properties.

## Statement 24: Lemma 4
**Assessment: included**
The statement that 2 = (1 - zeta)^{n/2} * u where u is a unit in Z[zeta], for zeta a primitive 2^k-th root of unity. This is formalized in mathlib in `/Users/vivc/code/Lean/statement_selection/mathlib_coverage/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`. The key result is `map_eq_span_zeta_sub_one_pow`, which shows that the ideal (p) in the ring of integers of the p^{k+1}-th cyclotomic field equals the ideal (zeta - 1)^{finrank Q K}. For p = 2, the finrank is phi(2^{k+1}) = 2^k = n/2 (where n = 2^{k+1} is the order of the root). Since (zeta - 1) generates a principal ideal, this ideal equality translates to the element-level statement 2 = (1 - zeta)^{n/2} * u. Additionally, `associated_norm_zeta_sub_one` establishes the associated norm result.

## Statement 25: Lemma 5
**Assessment: included**
The statement Z[zeta]/(1 - zeta) = F_2 for zeta a primitive 2^k-th root of unity. This is formalized in mathlib in `/Users/vivc/code/Lean/statement_selection/mathlib_coverage/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`. The result `absNorm_span_zeta_sub_one` states that the absolute norm of the ideal (zeta - 1) equals p. For p = 2, this means |O_K/(zeta - 1)| = 2, so the quotient is F_2. The result `inertiaDeg_span_zeta_sub_one` confirms the residual degree is 1, further establishing the quotient is F_p. The more general version holds for any prime p: Z[zeta]/(1 - zeta) = F_p.

## Statement 26: Lemma 6
**Assessment: non-included**
This lemma states that each eigenvalue of the circulant Hadamard matrix can be written as v_j * (1 - zeta)^{h_j} for a unit v_j and non-negative integer h_j. This is specific to the algebraic number theory analysis of circulant Hadamard matrices and is not in mathlib. While mathlib has the ideal theory of cyclotomic fields, the specific application to Hadamard matrix eigenvalues is absent.

## Statement 27: Corollary 7
**Assessment: non-included**
This corollary states that either gamma_0/gamma_1 or gamma_1/gamma_0 is in Z[zeta], a divisibility result for eigenvalue ratios of circulant Hadamard matrices. This is specific to the circulant Hadamard theory and is not in mathlib.

## Statement 28: Lemma 8
**Assessment: included**
The statement that an algebraic integer theta whose conjugates all have absolute value one is a root of unity. This is Kronecker's theorem, formalized in `/Users/vivc/code/Lean/statement_selection/mathlib_coverage/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean` as `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`: for an algebraic integer x in a number field K, if all embeddings phi : K -> A satisfy ||phi(x)|| = 1, then x^n = 1 for some positive n. Since any algebraic integer generates a number field Q(theta), this covers the general statement of Lemma 8. The file explicitly names this as Kronecker's Theorem in its docstring.

## Statement 29: Theorem 9 (Kronecker)
**Assessment: included**
The statement that if tau is a root of unity and alpha in Q[tau] with |alpha| = 1, then alpha is a root of unity. This is a special case of Statement 28, where the ambient number field is the cyclotomic field Q(tau). It is covered by the same mathlib result `NumberField.Embeddings.pow_eq_one_of_norm_eq_one` in `/Users/vivc/code/Lean/statement_selection/mathlib_coverage/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean`. The more general version `pow_eq_one_of_norm_le_one` (for conjugates inside the closed unit disk) is also available and is explicitly labeled as Kronecker's Theorem.

## Statement 30: Proposition 6.2
**Assessment: non-included**
This proposition states that L(m,n) (the poset of partitions fitting in an m x n rectangle) is graded of rank mn and rank-symmetric. While mathlib has Young diagrams with a distributive lattice structure in `Mathlib/Combinatorics/Young/YoungDiagram.lean`, there is no explicit formalization of L(m,n) as a bounded partition lattice, no concept of "graded poset" or "rank-symmetric" in this context. Searched: "partition.*lattice", "L.*m.*n.*partition", "graded.*poset", "GradedPoset", "rank_symmetric" -- no relevant results.

## Statement 31: Proposition 6.3
**Assessment: non-included**
This proposition states |L(m,n)| = C(m+n, m). Mathlib has no formalization of L(m,n) as a finite set with this cardinality. The counting of partitions fitting in a box is not present. Searched: "partition.*count.*binomial", "binom.*m+n", "lattice_path" -- no relevant results.

## Statement 32: Lemma 6.5
**Assessment: non-included**
This lemma gives the recurrence for the Gaussian (q-)binomial coefficient: [k choose j]_q = [k-1 choose j]_q + q^{k-j} * [k-1 choose j-1]_q. Mathlib does not have Gaussian/q-binomial coefficients. Searched: "GaussianBinomial", "gaussianBinomial", "qBinomial", "q_binomial", "q_analog", "qAnalog" -- no results in the relevant combinatorial/algebraic sense.

## Statement 33: Theorem 6.6
**Assessment: non-included**
This theorem states that the rank generating function of L(m,n) equals the q-binomial coefficient [m+n choose m]_q. Since neither L(m,n) nor q-binomial coefficients are formalized in mathlib, this result is absent.

## Statement 34: Lemma 6.8
**Assessment: non-included**
This lemma states that every orbit of G_{mn} acting on the boolean algebra B_R contains exactly one Young diagram. This concerns the group action on boolean algebras and the bijection with Young diagrams, which is not formalized. Searched: "quotient.*poset", "orbit.*Young", "Poset.*quotient" -- no relevant results.

## Statement 35: Theorem 6.9
**Assessment: non-included**
This theorem states that the quotient poset B_{R_{mn}}/G_{mn} is isomorphic to L(m,n). Neither quotient posets nor L(m,n) are formalized in mathlib.

## Statement 36: Corollary 6.10
**Assessment: non-included**
This corollary states that L(m,n) is rank-symmetric, rank-unimodal, and Sperner. Since L(m,n) is not formalized, and the Sperner/rank-unimodal framework for general posets is not present in mathlib, this is not included.

## Statement 37: Theorem 6.11
**Assessment: non-included**
This theorem states an optimization result about f_k(S, alpha), bounding it by the value at the initial segment f_k([n], floor(k(n+1)/2)). This appears to be a Kruskal-Katona-type extremal result. While mathlib has the Kruskal-Katona theorem in `Mathlib/Combinatorics/SetFamily/KruskalKatona.lean`, that theorem concerns shadow sizes of set families in the colex order, which is a different (though related) extremal result. The specific function f_k and the optimization claim of Theorem 6.11 are not formalized. Searched: "f_k", "RSK", "numberOfPartitions", broader combinatorics directories -- no matches for this specific result.
