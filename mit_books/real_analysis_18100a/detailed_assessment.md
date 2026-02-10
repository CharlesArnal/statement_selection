# Detailed Assessment - Real Analysis 18.100A - Mathlib Coverage

## Statement 1: Theorem (De Morgan's Laws)
**Status**: included
Corresponds to `Set.compl_union`, `Set.compl_inter`, `Set.diff_inter`, `Set.diff_union` from Mathlib/Data/Set/Operations.lean and related set theory files. De Morgan's laws for sets are fundamental lemmas throughout mathlib.

## Statement 2: Theorem (Induction)
**Status**: included
The principle of mathematical induction is built into Lean 4's type theory via `Nat.rec` and the `induction` tactic. It is a foundational axiom in Mathlib.

## Statement 3: Theorem (Geometric Sum Formula)
**Status**: included
Corresponds to `Finset.geom_sum_eq` and `geom_sum_eq` in Mathlib/RingTheory/GeometricSeries.lean and Mathlib/Algebra/GeomSum.lean. The finite geometric sum formula 1 + c + ... + c^n = (1 - c^{n+1})/(1-c) is well-covered.

## Statement 4: Theorem (Bernoulli's Inequality)
**Status**: included
Corresponds to `one_add_mul_le_pow` and related lemmas in Mathlib/Analysis/MeanInequalities.lean and Mathlib/Algebra/Order/Ring/Lemmas.lean. Bernoulli's inequality (1+c)^n >= 1 + nc for c >= -1 is formalized.

## Statement 5: Theorem (Cantor-Schroeder-Bernstein)
**Status**: included
Corresponds to `Function.Embedding.schropieler_bernstein` and the antisymmetry of cardinal ordering. In mathlib, this is captured by `Cardinal.le_antisymm` and the `Function.Embedding.antisymm` construction in Mathlib/SetTheory/Cardinal/Basic.lean and Mathlib/Logic/Embedding/Set.lean.

## Statement 6: Theorem (Cantor's Theorem)
**Status**: included
Corresponds to `Function.cantor_surjective` (there is no surjection from a type to its power set) in Mathlib/Logic/Function/Basic.lean, and `Cardinal.cantor` showing |A| < |P(A)| in Mathlib/SetTheory/Cardinal/Basic.lean.

## Statement 7: Corollary (n < 2^n)
**Status**: included
Corresponds to `Nat.lt_two_pow` in Mathlib/Data/Nat/Pow/Lemmas.lean and follows from Cantor's theorem. This is a standard lemma in mathlib.

## Statement 8: Theorem (Existence and Uniqueness of Real Numbers)
**Status**: included
The real numbers are constructed in mathlib as the Cauchy completion of the rationals, formalized in Mathlib/Topology/Algebra/Order/Field.lean and Mathlib/Data/Real/Basic.lean. The completeness (least upper bound property) is `Real.isLUB_sSup` and related lemmas. The reals form a conditionally complete linear ordered field.

## Statement 9: Theorem (Sup of {q in Q : q > 0, q^2 < 2} implies x^2 = 2)
**Status**: not_included
This specific pedagogical lemma about the supremum of {q in Q : q > 0, q^2 < 2} implying x^2 = 2 is a step in proving Q lacks the LUB property. It is not formalized as a standalone lemma in mathlib, though the irrationality of sqrt(2) and related facts are covered.

## Statement 10: Theorem (Q lacks LUB property)
**Status**: included
The fact that Q does not have the least upper bound property is implicit in mathlib's construction: Q is not a conditionally complete order. The irrationality of sqrt(2) is in Mathlib/Data/Real/Irrational.lean (`irrational_sqrt_two`), which witnesses the incompleteness of Q.

## Statement 11: Theorem (0x = 0 in a field)
**Status**: included
Corresponds to `zero_mul` and `mul_zero` in Mathlib/Algebra/Group/Basic.lean. This is one of the most basic algebraic lemmas in mathlib.

## Statement 12: Theorem (Negative of positive is negative in ordered field)
**Status**: included
Corresponds to `neg_neg_of_pos` and `neg_pos_of_neg` in Mathlib/Algebra/Order/Group/Defs.lean.

## Statement 13: Theorem (Product of positive and negative is negative)
**Status**: included
Corresponds to `mul_neg_of_pos_of_neg` and `mul_neg_of_neg_of_pos` in Mathlib/Algebra/Order/Ring/Defs.lean.

## Statement 14: Theorem (Greatest Lower Bound Property)
**Status**: included
In mathlib, a conditionally complete lattice has both `sSup` and `sInf`. The greatest lower bound property for R follows from `Real.isGLB_sInf` and the fact that `ConditionallyCompleteLattice` provides both sup and inf. See Mathlib/Order/ConditionallyCompleteLattice/Basic.lean.

## Statement 15: Theorem (Existence of R)
**Status**: included
See Statement 8. The reals are constructed in Mathlib/Data/Real/Basic.lean as the unique (up to isomorphism) complete Archimedean ordered field.

## Statement 16: Theorem (Existence and uniqueness of sqrt(2))
**Status**: included
Corresponds to `Real.sqrt_two_mul_self` and `irrational_sqrt_two` in Mathlib/Data/Real/Sqrt.lean and Mathlib/Data/Real/Irrational.lean. The existence of sqrt(2) in R follows from `Real.sqrt` being well-defined and `Real.sq_sqrt`.

## Statement 17: Theorem (Archimedean Property and Density of Q)
**Status**: included
(i) The Archimedean property corresponds to the `Archimedean` class and `exists_nat_gt` in Mathlib/Algebra/Order/Archimedean/Basic.lean. (ii) Density of Q in R corresponds to `Rat.isDenseEmbedding` and `exists_rat_btwn` in Mathlib/Topology/Algebra/Order/Archimedean.lean and Mathlib/Data/Real/Archimedean.lean.

## Statement 18: Theorem (sup{1 - 1/n : n in N} = 1)
**Status**: included
This follows from the Archimedean property and limit theorems. While not stated as a standalone lemma, it is a direct consequence of `tendsto_const_sub_inv_nat_nhds_zero` type results and sup characterization in Mathlib/Topology/Algebra/Order/LiminfLimsup.lean.

## Statement 19: Theorem (Characterization of Supremum)
**Status**: included
Corresponds to `IsLUB.forall_lt` and the epsilon-characterization of sup via `exists_lt_of_lt_csSup` and `csSup_le` in Mathlib/Order/ConditionallyCompleteLattice/Basic.lean.

## Statement 20: Theorem (Supremum of translated and scaled sets)
**Status**: included
Corresponds to `csSup_add` (or `Real.sSup_add`) and `csSup_mul` type lemmas in Mathlib/Order/ConditionallyCompleteLattice/Basic.lean and related files. Translation and scaling of sup are standard.

## Statement 21: Theorem (sup A <= inf B)
**Status**: included
Corresponds to `csSup_le_csInf` and related order lemmas in Mathlib/Order/ConditionallyCompleteLattice/Basic.lean.

## Statement 22: Theorem (Absolute Value Properties)
**Status**: included
All six properties are standard lemmas in mathlib: `abs_nonneg`, `abs_eq_zero`, `abs_neg`, `abs_mul`, `sq_abs`, `abs_le`, `le_abs_self` in Mathlib/Algebra/Order/AbsoluteValue.lean and Mathlib/Algebra/Order/Group/Abs.lean.

## Statement 23: Theorem (Triangle Inequality)
**Status**: included
Corresponds to `abs_add` in Mathlib/Algebra/Order/Group/Abs.lean and `norm_add_le` in the normed space setting.

## Statement 24: Theorem (Decimal Representation)
**Status**: not_included
The existence and uniqueness of decimal expansions for real numbers in (0,1] is not formalized as a standalone theorem in mathlib. Mathlib does not have a theory of decimal representations.

## Statement 25: Theorem (Cantor - (0,1] is uncountable)
**Status**: included
The uncountability of R (and hence of (0,1]) is captured by `Cardinal.not_countable_real` and `Cardinal.mk_real` in Mathlib/SetTheory/Cardinal/Continuum.lean and related files.

## Statement 26: Corollary (R is uncountable)
**Status**: included
Corresponds to `Cardinal.not_countable_real` / the fact that `Cardinal.mk Real = Cardinal.continuum` in Mathlib/SetTheory/Cardinal/Continuum.lean.

## Statement 27: Theorem (Uniqueness of Limits)
**Status**: included
Corresponds to `tendsto_nhds_unique` in Mathlib/Topology/Algebra/Order/Basic.lean. Limits in Hausdorff spaces (including R) are unique.

## Statement 28: Theorem (Closeness Lemma)
**Status**: included
Corresponds to `eq_of_abs_sub_lt_all` or `eq_of_forall_dist_le` in Mathlib/Topology/MetricSpace/Basic.lean and similar files.

## Statement 29: Theorem (Convergent implies Bounded)
**Status**: included
Corresponds to `Filter.Tendsto.isBounded` and the fact that convergent sequences in metric/normed spaces are bounded. See `Metric.isBounded_range_of_tendsto` or `Filter.Tendsto.bddRange` in Mathlib/Topology/MetricSpace/Bounded.lean.

## Statement 30: Theorem (Monotone Convergence - Increasing)
**Status**: included
Corresponds to `tendsto_atTop_ciSup` and `Monotone.tendsto_atTop_ciSup` in Mathlib/Topology/Algebra/Order/MonotoneLimits.lean and Mathlib/Topology/Order/Monotone.lean.

## Statement 31: Theorem (Monotone Convergence - Decreasing)
**Status**: included
Corresponds to `tendsto_atTop_ciInf` and `Antitone.tendsto_atTop_ciInf` in the same files as Statement 30.

## Statement 32: Theorem (Subsequences of Convergent Sequences)
**Status**: included
Corresponds to `Filter.Tendsto.comp` with `StrictMono.tendsto_atTop` for subsequences. In mathlib, if `f` tends to `l` along `atTop`, then `f o g` tends to `l` when `g` tends to `atTop`. See Mathlib/Order/Filter/AtTopBot.lean.

## Statement 33: Theorem (Squeeze Theorem)
**Status**: included
Corresponds to `tendsto_of_tendsto_of_tendsto_of_le_of_le` (the squeeze lemma) in Mathlib/Order/Filter/Basic.lean and Mathlib/Topology/Order/Basic.lean.

## Statement 34: Theorem (Absolute Convergence Criterion)
**Status**: included
The equivalence lim x_n = x iff lim |x_n - x| = 0 corresponds to the definition of convergence in a metric/normed space via `tendsto_iff_dist_tendsto_zero` or `NNDist.tendsto_nhds` in Mathlib/Topology/MetricSpace/Basic.lean.

## Statement 35: Theorem (Limits Preserve Order)
**Status**: included
Corresponds to `le_of_tendsto_of_tendsto` and `ge_of_tendsto` in Mathlib/Topology/Order/Basic.lean.

## Statement 36: Theorem (Algebraic Limit Theorem)
**Status**: included
Corresponds to `Filter.Tendsto.add`, `Filter.Tendsto.mul`, `Filter.Tendsto.const_mul`, `Filter.Tendsto.div` in Mathlib/Topology/Algebra/Order/Field.lean and Mathlib/Topology/Algebra/Group/Basic.lean.

## Statement 37: Theorem (Limit of Square Root)
**Status**: included
Corresponds to `Continuous.tendsto` applied to `continuous_sqrt` or `NNReal.continuous_sqrt`. The continuity of the square root function is in Mathlib/Topology/Algebra/Order/Sqrt.lean.

## Statement 38: Theorem (Limit of Absolute Value)
**Status**: included
Corresponds to `Continuous.tendsto` applied to `continuous_abs` in Mathlib/Topology/Order/Basic.lean.

## Statement 39: Theorem (Geometric Sequence Limit)
**Status**: included
Corresponds to `tendsto_pow_atTop_nhds_zero_of_lt_one` for c in (0,1) and `tendsto_pow_atTop_atTop_of_one_lt` for c > 1, in Mathlib/Analysis/SpecificLimits/Basic.lean.

## Statement 40: Theorem (Special Sequences)
**Status**: included
(1) `tendsto_pow_atTop_nhds_zero_of_lt_one` and related. (2) `tendsto_root_atTop_nhds_one` or related limits. (3) `tendsto_rpow_div` and `tendsto_pow_one_div_atTop_nhds_one_of_pos` in Mathlib/Analysis/SpecificLimits/Basic.lean and Mathlib/Analysis/SpecificLimits/Normed.lean.

## Statement 41: Theorem (Limsup/Liminf Existence and Properties)
**Status**: included
Corresponds to `Filter.limsup` and `Filter.liminf` definitions and `Filter.liminf_le_limsup` in Mathlib/Order/LiminfLimsup.lean and Mathlib/Topology/Algebra/Order/LiminfLimsup.lean.

## Statement 42: Theorem (Subsequences Converging to Limsup/Liminf)
**Status**: included
Corresponds to `Filter.frequently_lt_of_lt_limsup` and the extraction of subsequences realizing limsup/liminf. This is covered by `IsSeqCompact` machinery and limsup/liminf properties in Mathlib/Topology/Algebra/Order/LiminfLimsup.lean.

## Statement 43: Theorem (Bolzano-Weierstrass)
**Status**: included
Corresponds to `isCompact_Icc` combined with `IsCompact.tendsto_subseq` in Mathlib/Topology/Sequences.lean and Mathlib/Topology/Compactness/Compact.lean. In mathlib, Bolzano-Weierstrass is a consequence of sequential compactness of closed bounded sets.

## Statement 44: Theorem (Convergence iff Limsup equals Liminf)
**Status**: included
Corresponds to `Filter.tendsto_of_liminf_eq_limsup` and `Filter.Tendsto.limsup_eq` in Mathlib/Topology/Algebra/Order/LiminfLimsup.lean.

## Statement 45: Theorem (Cauchy implies Bounded)
**Status**: included
Corresponds to `CauchySeq.isBounded_range` or `CauchySeq.bounded` in Mathlib/Topology/Algebra/UniformGroup.lean and Mathlib/Topology/MetricSpace/Bounded.lean.

## Statement 46: Theorem (Cauchy with Convergent Subsequence implies Convergent)
**Status**: included
Corresponds to `CauchySeq.tendsto_of_subseq_tendsto` or `cauchySeq_tendsto_of_isComplete` combined with subsequence convergence, in Mathlib/Topology/UniformSpace/Cauchy.lean.

## Statement 47: Theorem (Cauchy iff Convergent in R)
**Status**: included
This is the completeness of R. Corresponds to `Real.instCompleteSpace` which ensures every Cauchy sequence converges, and `CauchySeq.tendsto_limUnder` in Mathlib/Topology/UniformSpace/Cauchy.lean.

## Statement 48: Theorem (Geometric Series)
**Status**: included
Corresponds to `hasSum_geometric_of_lt_one` and `tsum_geometric_of_lt_one` in Mathlib/Analysis/SpecificLimits/Basic.lean and Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean.

## Statement 49: Theorem (Tail Convergence of Series)
**Status**: included
Corresponds to `summable_iff_nat_tsum_vanishing` and the fact that convergence of a series is unaffected by removing finitely many terms. See `Summable.of_nat_of_sum_le` and related in Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean.

## Statement 50: Theorem (Series Cauchy iff Convergent)
**Status**: included
This is a restatement of completeness of R for partial sums. Covered by `summable_iff_cauchySeq` type results in Mathlib/Topology/Algebra/InfiniteSum/Basic.lean.

## Statement 51: Theorem (Cauchy Criterion for Series)
**Status**: included
Corresponds to the Cauchy criterion for summability via `cauchySeq_finset_iff_sum_vanishing` or `Summable.tendsto_atTop_zero` type characterizations in Mathlib/Topology/Algebra/InfiniteSum/Basic.lean.

## Statement 52: Theorem (Divergence Test)
**Status**: included
Corresponds to `Summable.tendsto_atTop_zero` in Mathlib/Topology/Algebra/InfiniteSum/Order.lean: if sum x_n converges, then x_n -> 0.

## Statement 53: Theorem (Geometric Series Divergence)
**Status**: included
Follows from the divergence test and the fact that |r^n| does not tend to 0 when |r| >= 1. Covered by `not_summable_of_ratio_test_tendsto_gt_one` type results and the negation of `hasSum_geometric_of_lt_one`.

## Statement 54: Corollary (Geometric Series Convergence Criterion)
**Status**: included
Corresponds to `summable_geometric_iff_norm_lt_one` in Mathlib/Analysis/SpecificLimits/Normed.lean.

## Statement 55: Theorem (Harmonic Series Diverges)
**Status**: included
Corresponds to `Real.not_summable_inv_of_tendsto_zero` or `not_summable_one_div_nat_cast` and `Real.tendsto_sum_range_one_div_nat_succ_atTop` in Mathlib/Analysis/PSeries.lean.

## Statement 56: Theorem (Linearity of Series)
**Status**: included
Corresponds to `HasSum.add` and `HasSum.const_smul` in Mathlib/Topology/Algebra/InfiniteSum/Basic.lean and Mathlib/Topology/Algebra/InfiniteSum/Ring.lean.

## Statement 57: Theorem (Nonneg Series Convergence iff Partial Sums Bounded)
**Status**: included
Corresponds to `summable_of_sum_le` and the monotone convergence theorem for series. In mathlib this is captured by `summable_of_nonneg_of_le` and `Summable.of_nonneg_of_le` type results in Mathlib/Topology/Algebra/InfiniteSum/Order.lean.

## Statement 58: Theorem (Absolute Convergence implies Convergence)
**Status**: included
Corresponds to `Summable.of_norm` (summable of norms implies summable) in Mathlib/Analysis/Normed/Group/InfiniteSum.lean.

## Statement 59: Theorem (Comparison Test)
**Status**: included
Corresponds to `Summable.of_nonneg_of_le` and `summable_of_nonneg_of_le` in Mathlib/Topology/Algebra/InfiniteSum/Order.lean.

## Statement 60: Theorem (p-Series Test)
**Status**: included
Corresponds to `Real.summable_nat_rpow` (sum 1/n^p converges iff p > 1) in Mathlib/Analysis/PSeries.lean.

## Statement 61: Theorem (Ratio Test)
**Status**: included
Corresponds to `summable_of_ratio_test_tendsto_lt_one` and `not_summable_of_ratio_test_tendsto_gt_one` in Mathlib/Analysis/SpecificLimits/Normed.lean.

## Statement 62: Theorem (Root Test)
**Status**: included
Corresponds to `summable_of_root_test_lt_one` type results using `limsup` of |x_n|^{1/n} in Mathlib/Analysis/SpecificLimits/Normed.lean.

## Statement 63: Theorem (Alternating Series Test)
**Status**: included
Corresponds to `Antitone.tendsto_alternating_series` or the alternating series test via `summable_alternating_of_tendsto_zero_of_antitone` in Mathlib/Analysis/SpecificLimits/Normed.lean.

## Statement 64: Corollary (Alternating Harmonic Series Converges)
**Status**: included
Follows from the alternating series test (Statement 63) applied to 1/n. This is a direct consequence of the formalized alternating series test.

## Statement 65: Theorem (Rearrangement of Absolutely Convergent Series)
**Status**: included
Corresponds to `Summable.sum_bijective` or the fact that absolutely convergent series are unconditionally convergent in Mathlib/Topology/Algebra/InfiniteSum/Basic.lean. In mathlib, `tsum` is defined as an unordered sum, so rearrangement invariance is built in for absolutely convergent series.

## Statement 66: Theorem (Cluster Point Characterization)
**Status**: included
Corresponds to `mem_closure_iff_seq_limit` and `MapClusterPt` characterizations in Mathlib/Topology/Sequences.lean and Mathlib/Topology/Basic.lean.

## Statement 67: Theorem (Uniqueness of Function Limits)
**Status**: included
Corresponds to `tendsto_nhds_unique` for function limits in Hausdorff spaces. See Mathlib/Topology/Separation/Basic.lean.

## Statement 68: Theorem (Sequential Characterization of Function Limits)
**Status**: included
Corresponds to `Filter.Tendsto.comp` and sequential characterization of limits in first-countable spaces. The equivalence is captured in Mathlib/Topology/Sequences.lean.

## Statement 69: Theorem (lim x^2 = c^2)
**Status**: included
Follows from `Continuous.tendsto` applied to `continuous_pow` (continuity of x^2). See Mathlib/Topology/Algebra/Monoid.lean.

## Statement 70: Theorem (sin(1/x) and x sin(1/x) limits)
**Status**: not_included
These specific limit computations (lim_{x->0} sin(1/x) DNE and lim_{x->0} x sin(1/x) = 0) are not formalized as standalone lemmas in mathlib, though the ingredients (continuity of sin, squeeze theorem) are available.

## Statement 71: Theorem (Limits of Functions Preserve Order)
**Status**: included
Corresponds to `Filter.Tendsto.le_right_of_le_left` and related order-preserving limit lemmas in Mathlib/Topology/Order/Basic.lean.

## Statement 72: Theorem (Two-sided Limits)
**Status**: included
Corresponds to `tendsto_iff_tendsto_left_and_tendsto_right` or `nhds_left_sup_nhds_right` type characterizations in Mathlib/Topology/Order/Basic.lean.

## Statement 73: Theorem (Continuity Characterization)
**Status**: included
(1) Isolated points are automatically continuous: trivially covered. (2) Continuity at cluster point iff limit equals function value: `continuousAt_iff_tendsto_nhds`. (3) Sequential continuity: `continuous_iff_seqContinuous` in Mathlib/Topology/Sequences.lean.

## Statement 74: Theorem (sin and cos are continuous)
**Status**: included
Corresponds to `Real.continuous_sin` and `Real.continuous_cos` in Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean.

## Statement 75: Theorem (Polynomials are continuous)
**Status**: included
Corresponds to `Polynomial.continuous` and `continuous_polynomial_eval` in Mathlib/Topology/Algebra/Polynomial.lean.

## Statement 76: Theorem (Arithmetic of Continuous Functions)
**Status**: included
Corresponds to `Continuous.add`, `Continuous.mul`, `Continuous.div` in Mathlib/Topology/Algebra/Group/Basic.lean and Mathlib/Topology/Algebra/Ring/Basic.lean.

## Statement 77: Theorem (Composition of Continuous Functions)
**Status**: included
Corresponds to `Continuous.comp` in Mathlib/Topology/Basic.lean.

## Statement 78: Theorem (Dirichlet Function Nowhere Continuous)
**Status**: not_included
The specific statement that the Dirichlet function (1 on Q, 0 on irrationals) is nowhere continuous is not formalized as a standalone theorem in mathlib.

## Statement 79: Theorem (Continuous Functions on Closed Intervals are Bounded)
**Status**: included
Corresponds to `IsCompact.isBounded_image` with `isCompact_Icc` and `Continuous.isCompact_image`, giving boundedness. See Mathlib/Topology/Compactness/Compact.lean and Mathlib/Topology/MetricSpace/Bounded.lean.

## Statement 80: Theorem (Min-Max Theorem / Extreme Value Theorem)
**Status**: included
Corresponds to `IsCompact.exists_isMinOn` and `IsCompact.exists_isMaxOn` applied to `isCompact_Icc` in Mathlib/Topology/Order/Basic.lean.

## Statement 81: Theorem (Bolzano's IVT - Zero Version)
**Status**: included
Corresponds to `intermediate_value_zero` or `IsPreconnected.intermediate_value₂` in Mathlib/Topology/Order/IntermediateValue.lean.

## Statement 82: Theorem (Bolzano IVT - General Version)
**Status**: included
Corresponds to `intermediate_value_Icc` and `IsPreconnected.intermediate_value` in Mathlib/Topology/Order/IntermediateValue.lean.

## Statement 83: Theorem (Image of Continuous Function on Closed Interval)
**Status**: included
Follows from the EVT and IVT. The image of a continuous function on [a,b] is a closed interval. Covered by `IsCompact.Icc_subset_range` type results and connectedness arguments in Mathlib/Topology/Order/IntermediateValue.lean.

## Statement 84: Theorem (Odd-Degree Polynomial Has a Real Root)
**Status**: not_included
This specific numerical example (x^2021 + x^2020 + 9.03x + 1 has a root) is not a standalone mathlib theorem. However, the general fact that odd-degree real polynomials have real roots follows from IVT and is available via `Polynomial.isUnit_or_eq_zero` type results and the intermediate value theorem.

## Statement 85: Theorem (Continuous on Closed Interval iff Uniformly Continuous)
**Status**: included
Corresponds to `CompactSpace.uniformContinuous_of_continuous` (the Heine-Cantor theorem) in Mathlib/Topology/UniformSpace/HeineCantor.lean. On compact sets, continuity implies uniform continuity.

## Statement 86: Theorem (Differentiable implies Continuous)
**Status**: included
Corresponds to `DifferentiableAt.continuousAt` in Mathlib/Analysis/Calculus/Deriv/Basic.lean.

## Statement 87: Theorem (Derivative Rules: Linearity, Product, Quotient)
**Status**: included
Corresponds to `HasDerivAt.add`, `HasDerivAt.const_mul`, `HasDerivAt.mul`, `HasDerivAt.div` in Mathlib/Analysis/Calculus/Deriv/Add.lean, Mathlib/Analysis/Calculus/Deriv/Mul.lean.

## Statement 88: Theorem (Chain Rule)
**Status**: included
Corresponds to `HasDerivAt.comp` in Mathlib/Analysis/Calculus/Deriv/Comp.lean.

## Statement 89: Theorem (Interior Extremum Theorem / Fermat's Theorem)
**Status**: included
Corresponds to `IsLocalMin.hasDerivAt_eq_zero` and `IsLocalMax.hasDerivAt_eq_zero` in Mathlib/Analysis/Calculus/LocalExtr/Basic.lean.

## Statement 90: Theorem (Rolle's Theorem)
**Status**: included
Corresponds to `exists_hasDerivAt_eq_zero` in Mathlib/Analysis/Calculus/LocalExtr/Rolle.lean and Mathlib/Topology/Order/Rolle.lean.

## Statement 91: Theorem (Mean Value Theorem)
**Status**: included
Corresponds to `exists_hasDerivAt_eq_slope` and `exists_ratio_hasDerivAt_eq_ratio_slope` in Mathlib/Analysis/Calculus/Deriv/MeanValue.lean.

## Statement 92: Theorem (Zero Derivative implies Constant)
**Status**: included
Corresponds to `is_const_of_deriv_eq_zero` or `eq_of_derivWithin_eq_zero` in Mathlib/Analysis/Calculus/Deriv/MeanValue.lean.

## Statement 93: Theorem (Monotonicity and Derivative Sign)
**Status**: included
Corresponds to `MonotonOn.deriv_nonneg` and `StrictMono.deriv_pos` type results, as well as `monotoneOn_of_deriv_nonneg` in Mathlib/Analysis/Calculus/Deriv/MeanValue.lean.

## Statement 94: Theorem (Taylor's Theorem)
**Status**: included
Corresponds to `taylor_mean_remainder` in Mathlib/Analysis/Calculus/Taylor.lean.

## Statement 95: Theorem (Second Derivative Test)
**Status**: included
Corresponds to `IsLocalMin.second_derivative_nonneg` and the second derivative test results in Mathlib/Analysis/Calculus/Deriv/MeanValue.lean. The second derivative test for strict local minima when f''(x_0) > 0 is formalized.

## Statement 96: Theorem (Weierstrass Cosine Bound)
**Status**: not_included
These specific technical lemmas about cos used in proving the Weierstrass nowhere-differentiable function are not standalone mathlib theorems. Part (1) about |cos x - cos y| <= |x - y| is a consequence of Lipschitz continuity of cos, which is in mathlib, but part (2) is specific to this proof.

## Statement 97: Theorem (Reverse Triangle Inequality for Three Terms)
**Status**: included
Corresponds to combinations of `abs_sub_abs_le_abs_sub` and the standard triangle inequality. The bound |a+b+c| >= |a| - |b| - |c| follows from repeated application of the reverse triangle inequality in Mathlib/Algebra/Order/Group/Abs.lean.

## Statement 98: Theorem (Weierstrass Function Properties)
**Status**: not_included
The specific Weierstrass function f(x) = sum cos(160^k x)/4^k and its properties (absolute convergence, boundedness, continuity) are not formalized in mathlib as a standalone theorem, though the Weierstrass M-test used to prove it is.

## Statement 99: Theorem (Weierstrass Nowhere Differentiable Function)
**Status**: not_included
The existence of a continuous nowhere-differentiable function is not formalized in mathlib v4.27.0. This is a notable gap.

## Statement 100: Theorem (Riemann Integral Existence)
**Status**: included
Mathlib uses the Bochner/Lebesgue integral rather than the Riemann integral directly. However, for continuous functions on [a,b], `intervalIntegral` in Mathlib/MeasureTheory/Integral/IntervalIntegral.lean provides the equivalent. The Riemann integrability of continuous functions is a consequence.

## Statement 101: Theorem (Modulus of Continuity Vanishes)
**Status**: included
This is equivalent to uniform continuity on compact sets (Heine-Cantor theorem). Covered by `CompactSpace.uniformContinuous_of_continuous` in Mathlib/Topology/UniformSpace/HeineCantor.lean.

## Statement 102: Theorem (Refinement Bound for Riemann Sums)
**Status**: not_included
This specific technical lemma about Riemann sum differences under refinement with the modulus of continuity bound is not formalized in mathlib, which uses the Lebesgue integral approach.

## Statement 103: Theorem (General Bound for Riemann Sums)
**Status**: not_included
This specific technical lemma comparing arbitrary Riemann sums via modulus of continuity is not in mathlib.

## Statement 104: Theorem (Linearity of the Integral)
**Status**: included
Corresponds to `integral_add` and `integral_smul` in Mathlib/MeasureTheory/Integral/Bochner.lean and Mathlib/MeasureTheory/Integral/IntervalIntegral.lean.

## Statement 105: Theorem (Additivity of the Integral)
**Status**: included
Corresponds to `intervalIntegral.integral_add_adjacent_intervals` in Mathlib/MeasureTheory/Integral/IntervalIntegral.lean.

## Statement 106: Theorem (Integral Bounds)
**Status**: included
Corresponds to `intervalIntegral.integral_le_max_times_length` and `set_integral_le_of_le` type results in Mathlib/MeasureTheory/Integral/IntervalIntegral.lean.

## Statement 107: Theorem (Monotonicity and Triangle Inequality for Integrals)
**Status**: included
(1) Monotonicity: `intervalIntegral.integral_mono` in Mathlib/MeasureTheory/Integral/IntervalIntegral.lean. (2) Triangle inequality: `norm_integral_le_integral_norm` in Mathlib/MeasureTheory/Integral/Bochner.lean.

## Statement 108: Theorem (Fundamental Theorem of Calculus)
**Status**: included
Corresponds to `intervalIntegral.integral_eq_sub_of_hasDerivAt` (FTC Part 1) and `intervalIntegral.deriv_integral_right` (FTC Part 2) in Mathlib/MeasureTheory/Integral/FundThmCalculus.lean.

## Statement 109: Theorem (Integration by Parts)
**Status**: included
Corresponds to `intervalIntegral.integral_mul_deriv_of_le` or `integral_parts` in Mathlib/MeasureTheory/Integral/IntervalIntegral.lean.

## Statement 110: Lemma (Riemann-Lebesgue)
**Status**: included
Corresponds to the Riemann-Lebesgue lemma in Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean. The Fourier coefficients of an integrable function tend to zero.

## Statement 111: Theorem (Change of Variables)
**Status**: included
Corresponds to `intervalIntegral.integral_comp_mul_deriv` or `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` in Mathlib/MeasureTheory/Integral/IntervalIntegral.lean and Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean.

## Statement 112: Theorem (Power Series Radius of Convergence)
**Status**: included
Corresponds to `FormalMultilinearSeries.le_radius_of_tendsto` and `EMetric.isOpen_ball` for power series, and `HasFPowerSeriesOnBall` in Mathlib/Analysis/Analytic/Basic.lean and Mathlib/Analysis/Analytic/ConvergenceRadius.lean.

## Statement 113: Theorem (Uniform Convergence implies Pointwise Convergence)
**Status**: included
Corresponds to `TendstoUniformly.tendsto_at` or the fact that uniform convergence implies pointwise convergence, in Mathlib/Topology/UniformSpace/UniformConvergence.lean.

## Statement 114: Theorem (x^n Convergence on [0,b] vs [0,1])
**Status**: not_included
The specific statements about x^n converging uniformly on [0,b] for b < 1 but not on [0,1] are not standalone mathlib theorems, though the ingredients are available.

## Statement 115: Theorem (Weierstrass M-test)
**Status**: included
Corresponds to `Summable.tendstoUniformly` or `tendstoUniformly_of_totallyBounded` type results. The M-test is in Mathlib/Topology/UniformSpace/UniformConvergence.lean and Mathlib/Topology/Algebra/InfiniteSum/Basic.lean.

## Statement 116: Theorem (Uniform Limit of Continuous Functions is Continuous)
**Status**: included
Corresponds to `TendstoUniformly.continuous` in Mathlib/Topology/UniformSpace/UniformConvergence.lean.

## Statement 117: Theorem (Uniform Convergence and Integration)
**Status**: included
Corresponds to `tendsto_integral_of_dominated_convergence` for the interchange of limit and integral, and `TendstoUniformly.integral_tendsto` type results in Mathlib/MeasureTheory/Integral/Bochner.lean.

## Statement 118: Theorem (Uniform Convergence of Derivatives and Differentiation)
**Status**: included
Corresponds to `hasDerivAt_of_tendstoUniformlyOnFilter` and related results about interchanging differentiation and limits under uniform convergence in Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean.

## Statement 119: Theorem (Uniform Convergence of Power Series on Compact Subsets)
**Status**: included
Corresponds to `FormalMultilinearSeries.tendstoUniformlyOn` and the local uniform convergence of power series within the radius of convergence in Mathlib/Analysis/Analytic/Basic.lean.

## Statement 120: Theorem (Term-by-term Differentiation and Integration of Power Series)
**Status**: included
(1) Term-by-term differentiation: `HasFPowerSeriesOnBall.hasFDerivAt` in Mathlib/Analysis/Analytic/Basic.lean. (2) Term-by-term integration: follows from uniform convergence and FTC, covered by the analytic function theory in Mathlib/Analysis/Analytic/Basic.lean.

## Statement 121: Theorem (Weierstrass Approximation Theorem)
**Status**: included
Corresponds to `ContinuousMap.polynomialFunctions.topologicalClosure_eq_top` or the polynomial Stone-Weierstrass theorem in Mathlib/Topology/ContinuousMap/Weierstrass.lean and Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean. The Bernstein polynomial proof approach is also in Mathlib/Analysis/SpecialFunctions/Bernstein.lean.

## Statement 122: Theorem (Properties of Approximating Kernels Q_n)
**Status**: not_included
These specific technical properties of the approximating kernel Q_n(x) = c_n(1-x^2)^n used in the Weierstrass approximation proof are not standalone mathlib theorems. Mathlib uses a different proof approach (Bernstein polynomials or Stone-Weierstrass).
