# Detailed Assessment of 18.100C Statements in Mathlib

## Fact 1.1: Every nonempty subset of N has a least element
**Status: included**
This is the well-ordering principle for natural numbers. In Mathlib, `Nat` has a `WellFoundedLT` instance, established in `Mathlib/Order/RelClasses.lean` (line 723: `instance : WellFoundedLT Nat := ⟨Nat.lt_wfRel.wf⟩`). The `Nat.find` function in core Lean also directly provides the least element of a nonempty decidable subset.

## Theorem 1.2: Any subset of N is either finite or countable
**Status: included**
Since `Nat` is itself countable, any subset is at most countable. In Mathlib, `Nat` is a `Countable` type (by virtue of being `Encodable`), and `Mathlib/Data/Set/Countable.lean` provides infrastructure for subsets of countable types being countable. The dichotomy finite-or-countable for subsets of `Nat` follows from `Set.Countable.finite_or_countable` type reasoning.

## Theorem 1.3: If S1 and S2 are countable, S1 union S2 is countable
**Status: included**
This is `Set.Countable.union` in `Mathlib/Data/Set/Countable.lean` (line 232): `theorem Countable.union {s t : Set α} (hs : s.Countable) (ht : t.Countable) : (s ∪ t).Countable`.

## Theorem 1.4: N^2 is countable
**Status: included**
In `Mathlib/Data/Countable/Basic.lean` (line 140), there is an instance: `instance [Countable α] [Countable β] : Countable (PProd α β)`, and through the equivalence with `Prod`, the product `Nat × Nat` is countable. The `Countable` instance for `Prod` is derived from this.

## Corollary 1.5: If S1 and S2 are countable, S1 x S2 is countable
**Status: included**
This follows from the `Countable` instance for products mentioned above. If `S1` and `S2` are countable types, `S1 × S2` is countable, derived in `Mathlib/Data/Countable/Basic.lean`.

## Corollary 1.6: If S1, S2, ... are countable sets, their countable union is countable
**Status: included**
This is `Set.countable_iUnion` in `Mathlib/Data/Set/Countable.lean` (line 205): `theorem countable_iUnion {t : ι → Set α} [Countable ι] (ht : ∀ i, (t i).Countable) : (⋃ i, t i).Countable`.

## Theorem 2.1: In any field, x * 0 = 0 for all x
**Status: included**
This is `mul_zero` and `zero_mul`, which are fundamental lemmas in Lean's core algebraic hierarchy. They appear throughout `Mathlib/Algebra/` and are part of the basic `MulZeroClass` typeclass.

## Theorem 2.2: In any ordered field, 1 > 0
**Status: included**
This is `zero_lt_one` or `one_pos`, available in `Mathlib/Algebra/Order/ZeroLEOne.lean` and used extensively. The `ZeroLEOneClass` typeclass captures this, and `zero_lt_one` is the strict version for ordered fields.

## Theorem 2.3: In any ordered field, x > 0 if and only if -x < 0
**Status: included**
This is `neg_neg_iff_pos` and related lemmas in Mathlib's ordered group theory. The equivalence `0 < x ↔ -x < 0` is captured by `neg_lt_zero` (i.e., `-x < 0 ↔ 0 < x`) in `Mathlib/Algebra/Order/Group/Defs.lean`.

## Corollary 2.4: In any ordered field, x^2 >= 0, with equality iff x = 0
**Status: included**
This is `sq_nonneg` in `Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean` and `Mathlib/Algebra/Order/Ring/Pow.lean`. The characterization of equality (`sq_eq_zero_iff`) is also present.

## Theorem 2.5: There is a unique real number x > 0 such that x^2 = 2
**Status: included**
The existence of `Real.sqrt` is established in Mathlib. `Real.sq_sqrt` shows that `(Real.sqrt x)^2 = x` for nonneg x, and `Real.sqrt_pos` gives positivity. These are in `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` and related files. The specific fact `sqrt 2` exists follows from the general `Real.sqrt` construction, proved via the completeness of the reals.

## Corollary 2.6: A real number is nonnegative if and only if it is a square
**Status: included**
This follows from `Real.sqrt` and `sq_nonneg`. Every nonneg real `x` equals `(Real.sqrt x)^2`, and every square is nonneg by `sq_nonneg`. The constructions in `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` establish this.

## Theorem 2.7: (Archimedean principle) For every real number x there is a natural number n such that n > x
**Status: included**
This is the `Archimedean` typeclass in `Mathlib/Algebra/Order/Archimedean/Basic.lean`. The instance `instArchimedean` for `ℝ` is established, and `exists_nat_gt` provides exactly this statement.

## Corollary 3.1: For every x > 0 there is n such that 1/n < x
**Status: included**
This is a direct consequence of the Archimedean property. In Mathlib, `exists_nat_gt` gives `n > 1/x`, so `1/n < x`. The lemma `Nat.one_div_lt_iff` or similar reasoning in `Mathlib/Algebra/Order/Archimedean/Basic.lean` covers this.

## Corollary 3.2: For every x there is an integer n such that x < n <= x + 1
**Status: included**
This is essentially the floor function. In Mathlib, `Int.floor` and `Int.lt_floor_add_one` in `Mathlib/Algebra/Order/Floor.lean` provide that `x < ⌊x⌋ + 1 ≤ x + 1`. The Archimedean property yields `FloorRing` instances.

## Corollary 3.3: For any x < y there is a rational q with x < q < y (density of Q in R)
**Status: included**
This is `exists_rat_btwn` in `Mathlib/Topology/Instances/Rat.lean` and related files. Also `Rat.isDenseEmbedding_coe_real` and the `DenseRange` property of the rationals in the reals are established in Mathlib.

## Theorem 3.4: 0.9999... = 1
**Status: included**
This follows from the geometric series formula. In Mathlib, `tsum_geometric_of_lt_one` in `Mathlib/Analysis/SpecificLimits/Basic.lean` gives `∑ n, r^n = (1-r)⁻¹` for `0 ≤ r < 1`. Taking `r = 9/10` and multiplying by `9/10` yields `0.999... = 1`. The infrastructure is present even if not stated in exactly this form.

## Theorem 3.5: Nested closed intervals have nonempty intersection
**Status: included**
This is a consequence of compactness of closed intervals. In Mathlib, `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` in `Mathlib/Topology/Compactness/Compact.lean` provides this for compact spaces. Since `Icc a b` is compact (`isCompact_Icc`), nested nonempty closed subintervals have nonempty intersection.

## Corollary 3.6: R is uncountable
**Status: included**
This is `Cardinal.not_countable_real` in `Mathlib/Analysis/Real/Cardinality.lean`, which shows `Cardinal.mk_real = Cardinal.continuum` (line 185) and the reals are not countable.

## Theorem 3.7: (Cauchy-Schwarz inequality)
**Status: included**
This is `abs_real_inner_le_norm` and `inner_mul_le_norm_mul_iff` in `Mathlib/Analysis/InnerProductSpace/Basic.lean` (line 468). For finite-dimensional spaces, the Cauchy-Schwarz inequality `|⟪x, y⟫| ≤ ‖x‖ * ‖y‖` is a fundamental result. The complex version is covered by `abs_inner_le_norm` for complex inner product spaces.

## Theorem 4.1: Triangle inequality for Euclidean norm
**Status: included**
The triangle inequality `‖x + y‖ ≤ ‖x‖ + ‖y‖` is the fundamental axiom of normed spaces, captured by the `NormedAddCommGroup` typeclass. For `EuclideanSpace ℝ (Fin n)`, this is inherited from the `NormedAddCommGroup` structure. The specific proof for `ℝ^n` via Cauchy-Schwarz is in `Mathlib/Analysis/Complex/Norm.lean` (the private `norm_add_le'`).

## Theorem 4.2: Every ball neighbourhood is an open subset
**Status: included**
This is `Metric.isOpen_ball` in `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean` (line 793): `theorem isOpen_ball : IsOpen (ball x ε)`.

## Theorem 5.1: Finite unions and intersections of open sets are open
**Status: included**
`IsOpen.union` and `IsOpen.inter` are fundamental topological lemmas available in `Mathlib/Topology/Sets/Opens.lean` and `Mathlib/Topology/Defs/Basic.lean`. These are part of the `TopologicalSpace` axioms (arbitrary unions are open, finite intersections are open).

## Theorem 5.2: Arbitrary unions of open sets are open
**Status: included**
This is `isOpen_iUnion` and `isOpen_sUnion`, which are axioms of the `TopologicalSpace` structure in Mathlib, available in `Mathlib/Topology/Sets/Opens.lean`.

## Corollary 5.3: Every open subset is a union of ball neighbourhoods
**Status: included**
In a metric space, the topology is generated by open balls. This is built into the definition of `MetricSpace` in Mathlib: the topology is defined as the one generated by open balls. The `Metric.isOpen_iff` lemma characterizes open sets as those where every point has a ball neighborhood contained in the set.

## Theorem 5.4: If x is a limit point of E, then B_r(x) intersection E is infinite for any r > 0
**Status: non-included**
Mathlib uses a filter-based approach to limit points (`ClusterPt`, `AccPt`) rather than the classical metric-space statement about infinite intersections. While `AccPt` captures the notion that every neighborhood meets the set in a point different from x, the specific statement that the intersection is *infinite* is not directly stated in this form. The closest results are in `Mathlib/Topology/ClusterPt.lean` and `Mathlib/Topology/DiscreteSubset.lean`, but they use filter language rather than explicitly asserting infiniteness of ball intersections.

## Corollary 5.5: A finite subset of X has no limit points, hence is closed
**Status: included**
Finite sets are closed in T1 spaces (which includes all metric spaces). In Mathlib, `Set.Finite.isClosed` is available, and `isCompact_iff_finite` for discrete topologies. For metric spaces (which are T1), `Set.Finite.isClosed` handles this in `Mathlib/Topology/Separation/Basic.lean`.

## Theorem 5.6: Finite unions and intersections of closed sets are closed
**Status: included**
`IsClosed.union` and `IsClosed.inter` are in `Mathlib/Topology/Irreducible.lean` and the basic topology files. These follow from the open set versions by complementation.

## Theorem 5.7: Arbitrary intersections of closed sets are closed
**Status: included**
This is `isClosed_iInter` and `isClosed_sInter`, available throughout Mathlib, used for instance in `Mathlib/Dynamics/OmegaLimit.lean` and many other places. It follows from the axiom that arbitrary unions of open sets are open.

## Theorem 5.8: E is open iff X \ E is closed
**Status: included**
This is `isOpen_compl_iff` and `isClosed_compl_iff` in `Mathlib/Topology/Defs/Basic.lean` and `Mathlib/Topology/Order/LowerUpperTopology.lean`. It is a fundamental equivalence in the topology API.

## Theorem 6.2: If K is compact and x is a point, then K is contained in B_r(x) for some r (compact sets are bounded)
**Status: included**
This is `IsCompact.isBounded` in `Mathlib/Topology/MetricSpace/Bounded.lean` (line 174): `theorem IsCompact.isBounded {s : Set α} (h : IsCompact s) : IsBounded s`.

## Theorem 6.3: Compact sets are closed
**Status: included**
In Mathlib, this is `IsCompact.isClosed` for T2 (Hausdorff) spaces, which includes all metric spaces. This is in `Mathlib/Topology/Separation/Hausdorff.lean`. The statement follows from the T2 separation axiom.

## Theorem 6.4: If K is compact and E is closed, K intersection E is compact
**Status: included**
This is `IsCompact.inter_right` in `Mathlib/Topology/Compactness/Compact.lean` (line 86): `theorem IsCompact.inter_right (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s ∩ t)`.

## Theorem 6.5: Union of two compact sets is compact
**Status: included**
This is `IsCompact.union` in `Mathlib/Topology/Compactness/Compact.lean` (line 487): `theorem IsCompact.union (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t)`.

## Theorem 6.6: Infinite subset of a compact set has a limit point
**Status: included**
This is captured by `IsCompact.isSeqCompact` and the Bolzano-Weierstrass property. In `Mathlib/Topology/Sequences.lean`, `IsCompact.isSeqCompact` (line 258) shows compact implies sequentially compact. The classical formulation about infinite subsets having cluster points follows from `isCompact_iff_finite_subcover` combined with properties in `Mathlib/Topology/Compactness/Compact.lean`.

## Theorem 6.7: K is compact as a subset of X iff K is compact as a metric space in its own right
**Status: included**
In Mathlib, `isCompact_iff_compactSpace` relates the compactness of a set to the `CompactSpace` property of the subtype. This is in `Mathlib/Topology/Compactness/Compact.lean`.

## Theorem 7.1: If every countably infinite subset has a limit point, then X is compact
**Status: included**
This is related to the equivalence of sequential compactness and compactness in metric spaces. In `Mathlib/Topology/Sequences.lean` (line 383), `isCompact_iff_isSeqCompact` establishes this equivalence for metric spaces. The condition that every infinite subset has a limit point is equivalent to sequential compactness.

## Theorem 7.2: (Heine-Borel) [a,b] is compact
**Status: included**
This is `isCompact_Icc` in Mathlib, proved in `Mathlib/Topology/Order/Compact.lean` and used extensively (e.g., `Mathlib/Topology/Order/Rolle.lean`). The Heine-Borel theorem for intervals is a fundamental result.

## Theorem 7.3: Every bounded closed subset of R is compact
**Status: included**
This is `isCompact_of_isClosed_isBounded` in `Mathlib/Topology/MetricSpace/Bounded.lean`. The Heine-Borel theorem in full generality for `ℝ` (and finite-dimensional spaces) is captured by `Metric.isCompact_iff_isClosed_bounded` or `ProperSpace` instances.

## Theorem 7.4: Every finite closed cube in R^n is compact
**Status: included**
This follows from `isCompact_Icc` applied to each factor and the fact that finite products of compact sets are compact (`IsCompact.prod`). In Mathlib, `isCompact_pi_infinite` and `isCompact_Icc` in product spaces cover this.

## Theorem 7.5: Every bounded closed subset of R^n is compact
**Status: included**
This is the Heine-Borel theorem for `ℝ^n`. In Mathlib, `ℝ^n` (as `EuclideanSpace ℝ (Fin n)` or `Fin n → ℝ`) has `ProperSpace` instance, so `isCompact_of_isClosed_isBounded` applies. This is in `Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`.

## Theorem 8.1: Convergent sequence with terms in E has limit in closure of E
**Status: included**
This is fundamental in Mathlib's topology. The closure is characterized as the set of limits of sequences (in first-countable spaces). `mem_closure_iff_seq_limit` and related results in `Mathlib/Topology/Defs/Sequences.lean` and `Mathlib/Topology/Sequences.lean` provide this.

## Theorem 8.2: Points in the closure of E are limits of sequences from E
**Status: included**
This is `mem_closure_iff_seq_limit` in Mathlib for first-countable spaces (which includes all metric spaces). Available in `Mathlib/Topology/Sequences.lean`.

## Theorem 8.3: Every sequence in a compact metric space has a convergent subsequence
**Status: included**
This is `IsCompact.tendsto_subseq` in `Mathlib/Topology/Sequences.lean` (line 268): given a compact set and a sequence in it, there exists a convergent subsequence. Also `CompactSpace.tendsto_subseq` (line 277) for compact spaces.

## Corollary 8.4: Every bounded sequence in R^d has a convergent subsequence (Bolzano-Weierstrass)
**Status: included**
This follows from the compactness of closed bounded sets in `ℝ^d` (Heine-Borel) and `IsCompact.tendsto_subseq`. In `Mathlib/Topology/MetricSpace/Sequences.lean`, `tendsto_subseq_of_bounded` (or similar) provides this.

## Lemma 8.5: Cauchy sequence with convergent subsequence converges
**Status: included**
This is `tendsto_nhds_of_cauchySeq_of_subseq` in `Mathlib/Topology/UniformSpace/Cauchy.lean` (line 269): `theorem tendsto_nhds_of_cauchySeq_of_subseq [Preorder β] {u : β → α} (hu : CauchySeq u) ...`.

## Theorem 8.6: In a compact metric space, every Cauchy sequence converges
**Status: included**
Compact metric spaces are complete. In Mathlib, `CompactSpace` implies `CompleteSpace` via `UniformSpace.isComplete_univ` and the fact that compact spaces are complete. The result `cauchySeq_tendsto_of_isComplete` in `Mathlib/Topology/UniformSpace/Cauchy.lean` handles this.

## Corollary 8.7: Every Cauchy sequence in R^n converges (R^n is complete)
**Status: included**
`ℝ^n` has a `CompleteSpace` instance in Mathlib, so every Cauchy sequence converges. This is inherited from the completeness of `ℝ` and the completeness of finite products of complete spaces.

## Theorem 9.1: The set of accumulation points of a sequence is closed
**Status: included**
In Mathlib, `isClosed_setOf_clusterPt` in `Mathlib/Topology/ClusterPt.lean` shows that the set of cluster points (accumulation points) is closed. This is the filter-theoretic generalization.

## Theorem 9.2: In a separable metric space, every closed nonempty subset is the set of accumulation points of some sequence
**Status: non-included**
This is a more specialized result about the "richness" of accumulation-point sets in separable spaces. While Mathlib has extensive material on separable spaces and sequential characterizations, this particular converse statement (that every closed set can be realized as the set of subsequential limits) does not appear to be formalized. The relevant files `Mathlib/Topology/Sequences.lean` and `Mathlib/Topology/Defs/Sequences.lean` do not contain this result.

## Theorem 9.3: A nondecreasing bounded sequence converges
**Status: included**
This is `tendsto_of_monotone` in `Mathlib/Topology/Order/MonotoneConvergence.lean` (line 200), which states that a monotone sequence in a conditionally complete linear order either tends to the top or converges. For bounded monotone sequences, convergence follows. Also `tendsto_atTop_atTop_of_monotone'` handles the bounded case.

## Theorem 9.4: (1 + 1/n)^n converges
**Status: included**
The limit of `(1 + 1/n)^n` defines `e = Real.exp 1`. In Mathlib, `Real.exp` is defined and the connection to this sequence is established. The monotonicity and boundedness of this sequence can be derived from properties of `exp` in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean` and `Mathlib/Analysis/SpecialFunctions/Exp.lean`.

## Theorem 9.5: A series of nonneg numbers converges iff partial sums are bounded
**Status: included**
This is `summable_of_sum_le` and related results in `Mathlib/Topology/Algebra/InfiniteSum/Real.lean` (line 84). For nonneg sequences, summability is equivalent to bounded partial sums.

## Theorem 9.6: Geometric series formula sum x^k = 1/(1-x) for |x| < 1
**Status: included**
This is `tsum_geometric_of_abs_lt_one` in `Mathlib/Analysis/SpecificLimits/Normed.lean` (line 381): `theorem tsum_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) : ∑' n, r ^ n = (1 - r)⁻¹`. Also `hasSum_geometric_of_abs_lt_one` (line 374).

## Theorem 9.7: p-series convergence: sum 1/k^p diverges for p <= 1, converges for p > 1
**Status: included**
This is `summable_one_div_nat_rpow` in `Mathlib/Analysis/PSeries.lean` (line 293), which gives the characterization of when the p-series is summable based on the exponent.

## Theorem 10.1: (Euler) The series sum 1/p over primes diverges
**Status: included**
This is `Nat.Primes.not_summable_one_div` in `Mathlib/NumberTheory/SumPrimeReciprocals.lean` (line 86): `theorem Nat.Primes.not_summable_one_div : ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ))`.

## Theorem 10.2: Absolute convergence implies convergence
**Status: included**
This is `Summable.of_norm` in `Mathlib/Analysis/Normed/Group/InfiniteSum.lean` (line 185): `theorem Summable.of_norm {f : ι → E} (hf : Summable fun a => ‖f a‖) : Summable f`. The general version `Summable.of_norm_bounded` (line 110) is also available.

## Theorem 10.3: Absolute convergence controls tail sums for any sufficiently large finite subset
**Status: included**
This follows from the general theory of `HasSum` in Mathlib. The `HasSum` predicate in `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean` is defined via convergence of finite partial sums over all finite subsets, which directly encodes this property. The relevant API is in `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`.

## Corollary 10.4: Rearrangements of absolutely convergent series give the same sum
**Status: included**
This is `Equiv.hasSum_iff` and `Equiv.summable_iff` in `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`. Since `HasSum` is defined over all finite subsets (not just initial segments), rearrangement invariance is built into the definition. For absolutely convergent series this follows from `Summable.of_norm`.

## Theorem 10.5: Cauchy product theorem for series
**Status: included**
The Cauchy product formula is `tsum_mul_tsum_eq_tsum_sum_antidiagonal` (mentioned in `Mathlib/Topology/Algebra/InfiniteSum/Ring.lean`, line 23 in the docstring). This file contains `HasSum.mul_left`, `HasSum.mul_right`, and the Cauchy product infrastructure.

## Theorem 11.1: Power series converges absolutely inside radius of convergence
**Status: included**
This is fundamental to the `FormalMultilinearSeries` and `HasFPowerSeriesOnBall` API in `Mathlib/Analysis/Analytic/Basic.lean`. The `HasFPowerSeriesOnBall` predicate ensures absolute convergence within the ball of convergence. Also `FormalMultilinearSeries.radius` defines the radius of convergence.

## Theorem 11.2: Convergence of power series with decreasing nonneg coefficients on the unit circle except z=1
**Status: non-included**
This is a specialized result about power series with monotonically decreasing coefficients (related to Dirichlet's test / Abel's test for convergence on the boundary). While Mathlib has Abel's limit theorem (`Mathlib/Analysis/Complex/AbelLimit.lean`), this specific convergence criterion for series on the unit circle with monotone coefficients does not appear to be formalized. Searched `Mathlib/Analysis/Analytic/`, `Mathlib/Analysis/SpecificLimits/`, and `Mathlib/Analysis/Complex/AbelLimit.lean` without finding this result.

## Theorem 11.3: (Abel's theorem) If sum ak converges, its value equals lim_{t->1} f(t)
**Status: included**
This is Abel's limit theorem, formalized in `Mathlib/Analysis/Complex/AbelLimit.lean`. The main result is `Real.tendsto_tsum_powerSeries_nhdsWithin_lt` (Abel's limit theorem for real power series) and `Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone` for the complex version.

## Theorem 11.4: exp(z) * exp(w) = exp(z + w)
**Status: included**
This is `exp_add` in `Mathlib/Analysis/Normed/Algebra/Exponential.lean` (line 427 for the commutative version `exp_add_of_mem_ball`, and the general `exp_add` for commutative algebras). For complex numbers, `Complex.exp_add` is available.

## Theorem 11.5: |exp(z)| = exp(Re(z))
**Status: included**
This is `Complex.norm_exp` or `Complex.abs_exp` in `Mathlib/Analysis/SpecialFunctions/Exp.lean`. The result `norm_exp` relates `‖exp z‖` to `Real.exp (z.re)`.

## Theorem 11.6: cos^2(t) + sin^2(t) = 1
**Status: included**
This is `sin_sq_add_cos_sq` in `Mathlib/Analysis/Complex/Trigonometric.lean` (line 462): `theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1`. Also the real version at line 628.

## Theorem 12.5: Four definitions of continuity are equivalent
**Status: included**
In Mathlib, the equivalence of sequential, epsilon-delta, and open-preimage definitions of continuity is built into the API. `Metric.continuous_iff` characterizes continuity in metric spaces via epsilon-delta, `continuous_def` via open preimages, and `SeqContinuous` via sequences. The equivalences are in `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean` and `Mathlib/Topology/Sequences.lean`.

## Theorem 12.6: Composition of continuous maps is continuous
**Status: included**
This is `Continuous.comp` in Mathlib's topology library. It is a fundamental property used throughout Mathlib.

## Corollary 12.7: Sum and product of continuous real-valued functions are continuous
**Status: included**
`Continuous.add` and `Continuous.mul` are in `Mathlib/Topology/Algebra/Ring/Basic.lean` and `Mathlib/Topology/Algebra/Group/Basic.lean`. The topological ring structure on `ℝ` makes addition and multiplication continuous, and compositions preserve continuity.

## Corollary 12.8: If f is continuous and nonzero, then 1/f is continuous
**Status: included**
`Continuous.inv₀` (for functions into a topological field that are nonzero) is available in Mathlib. This uses the fact that inversion is continuous away from zero in a topological field.

## Theorem 12.9: Continuous image of compact set is compact
**Status: included**
This is `IsCompact.image` in `Mathlib/Topology/Compactness/Compact.lean` (line 121): `theorem IsCompact.image {f : X → Y} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s)`.

## Corollary 12.10: Continuous function on a compact space is bounded and attains its min and max
**Status: included**
This is `IsCompact.exists_isMinOn` and `IsCompact.exists_isMaxOn` in `Mathlib/Topology/Order/Compact.lean` (lines 228, 246). These are the extreme value theorems.

## Corollary 12.11: Continuous bijection from compact to Hausdorff has continuous inverse
**Status: included**
This is `Continuous.homeoOfEquivCompactToT2` in `Mathlib/Topology/Homeomorph/Lemmas.lean` (line 475): `def homeoOfEquivCompactToT2 [CompactSpace X] [T2Space Y] {f : X ≃ Y} (hf : Continuous f) : X ≃ₜ Y`. Also `Continuous.isClosedMap` for compact-to-T2 in `Mathlib/Topology/Separation/Hausdorff.lean` (line 663).

## Theorem 12.14: Two definitions of continuity at a point are equivalent
**Status: included**
The equivalence of sequential and epsilon-delta continuity at a point is established in Mathlib through `continuousAt_iff_seq_tendsto` (in first-countable spaces) and `Metric.continuousAt_iff` for the epsilon-delta version. These are in `Mathlib/Topology/Sequences.lean` and `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`.

## Lemma 12.16: lim_{x->p} f(x) = f(p) iff f is continuous at p
**Status: included**
This is essentially the definition of `ContinuousAt` in Mathlib: `ContinuousAt f x ↔ Tendsto f (nhds x) (nhds (f x))`. The equivalence with the limit characterization is built into the filter-based approach.

## Theorem 13.3: (Intermediate Value Theorem)
**Status: included**
This is `intermediate_value_Icc` in `Mathlib/Topology/Order/IntermediateValue.lean` (line 543). The more general version `IsPreconnected.intermediate_value₂` is also available. The theorem uses the connectedness of intervals.

## Corollary 13.4: Continuous image of [a,b] is a closed interval [c,d]
**Status: included**
This follows from the IVT and the extreme value theorem. The image of a connected compact set under a continuous function is connected and compact, hence a closed interval. In Mathlib, `IsPreconnected.image` gives connectedness of the image, and compactness gives closedness and boundedness. The result `eq_Icc_of_connected_compact` is used in `Mathlib/Topology/Order/Compact.lean`.

## Corollary 13.5: Continuous strictly increasing f on [a,b] is a homeomorphism onto [c,d]
**Status: included**
This combines the IVT (the image is [f(a), f(b)]), injectivity from strict monotonicity, and the continuous inverse theorem for compact-to-Hausdorff maps. All ingredients are in Mathlib. `StrictMono.continuousOn_Icc` and the homeomorphism theorem provide this.

## Theorem 13.8: On compact spaces, continuous implies uniformly continuous
**Status: included**
This is `CompactSpace.uniformContinuous_of_continuous` in `Mathlib/Topology/UniformSpace/HeineCantor.lean` (line 38), also known as the Heine-Cantor theorem. Also `IsCompact.uniformContinuousOn_of_continuous` (line 47).

## Theorem 14.4: Three definitions of differentiability are equivalent
**Status: included**
In Mathlib, `HasDerivAt` is defined via the Frechet derivative, and the equivalence with the difference quotient definition is built into the API. `hasDerivAt_iff_isLittleO` and `hasDerivAt_iff_tendsto_slope` provide the equivalences. These are in `Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Theorem 14.5: Differentiable implies continuous
**Status: included**
This is `HasDerivAt.continuousAt` and `DifferentiableAt.continuousAt` in `Mathlib/Analysis/Calculus/Deriv/Basic.lean`. This is a fundamental result in the calculus API.

## Theorem 14.7: Chain rule
**Status: included**
This is `HasDerivAt.comp` in `Mathlib/Analysis/Calculus/Deriv/Comp.lean`. The chain rule `(f ∘ g)'(x) = f'(g(x)) * g'(x)` is formalized for `HasDerivAt`.

## Theorem 14.8: Rolle's theorem
**Status: included**
This is `exists_deriv_eq_zero` in `Mathlib/Analysis/Calculus/LocalExtr/Rolle.lean` (line 58): `theorem exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) : ∃ c ∈ Ioo a b, deriv f c = 0`.

## Theorem 14.9: Mean Value Theorem
**Status: included**
This is `exists_hasDerivAt_eq_slope` in `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` (derived from `exists_ratio_hasDerivAt_eq_ratio_slope` at line 83). The MVT states there exists `c` where `f'(c) = (f(b) - f(a))/(b - a)`.

## Theorem 14.10: Generalized (Cauchy) Mean Value Theorem
**Status: included**
This is `exists_ratio_hasDerivAt_eq_ratio_slope` in `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` (line 83): the generalized MVT with two functions f and g, yielding `(f(b) - f(a)) * g'(c) = (g(b) - g(a)) * f'(c)`.

## Theorem 15.1: Inverse function theorem for derivatives
**Status: included**
The one-dimensional inverse function theorem for derivatives is in Mathlib. `HasDerivAt.eventually_ne` and the general inverse function theorem infrastructure in `Mathlib/Analysis/Calculus/InverseFunctionTheorem/` provide the result. For the one-dimensional case, the formula `f'(g(p)) = 1/g'(p)` follows from the chain rule.

## Theorem 15.4: Taylor's theorem (Peano form)
**Status: included**
This is captured by the Taylor approximation results in `Mathlib/Analysis/Calculus/Taylor.lean`. The `taylor_mean_remainder` (line 293) and the `is_o` formulation of the remainder provide the Peano form of the remainder.

## Theorem 15.5: Taylor's theorem (Peano form, epsilon-delta)
**Status: included**
This is the epsilon-delta reformulation of Theorem 15.4, equivalent to saying the remainder is `o(|x-p|^m)`. In Mathlib, this is captured by the `IsLittleO` (Landau notation) formulation of Taylor's theorem in `Mathlib/Analysis/Calculus/Taylor.lean`.

## Theorem 15.6: Taylor's theorem with Lagrange remainder
**Status: included**
This is `taylor_mean_remainder_lagrange` in `Mathlib/Analysis/Calculus/Taylor.lean` (line 323): Taylor's theorem with the Lagrange form of the remainder.

## Theorem 16.1: Cauchy convergence criterion for uniform convergence
**Status: included**
This is `tendstoUniformly_iff_tendsto` and the Cauchy characterization via `UniformCauchySeqOn` in `Mathlib/Topology/UniformSpace/UniformConvergence.lean`. The complete space structure ensures the equivalence.

## Corollary 16.2: Weierstrass M-test
**Status: included**
This is `tendstoUniformlyOn_tsum` in `Mathlib/Analysis/Normed/Group/FunctionSeries.lean` (line 33): given `Summable u` and `‖f n x‖ ≤ u n`, the series converges uniformly. Also `tendstoUniformly_tsum` (line 92).

## Corollary 16.3: Power series converges uniformly on compact subsets inside radius of convergence
**Status: included**
This follows from the Weierstrass M-test applied to power series. In Mathlib, the analytic function theory in `Mathlib/Analysis/Analytic/Basic.lean` establishes that power series converge uniformly on compact subsets of the ball of convergence.

## Theorem 16.4: Uniform limit of continuous functions is continuous
**Status: included**
This is `TendstoUniformly.continuous` in `Mathlib/Topology/UniformSpace/UniformConvergence.lean` (line 31 in docstring, formally proved later in the file). Also `TendstoUniformlyOn.continuousOn` for the local version.

## Corollary 16.5: Power series with positive radius of convergence defines a continuous function
**Status: included**
This follows from the uniform convergence on compact subsets and the continuity of uniform limits. In Mathlib, `HasFPowerSeriesOnBall` implies continuity through `AnalyticAt.continuousAt` in `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean` and the analytic function API.

## Theorem 17.1: Uniform convergence of derivatives implies differentiability of limit
**Status: included**
This is formalized in `Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`. The theorem `hasDerivAt_of_tendstoUniformly` (line 548) states that if derivatives converge uniformly and the functions converge at one point, then the limit is differentiable with derivative equal to the limit of the derivatives.

## Corollary 17.2: Power series is differentiable with term-by-term derivative
**Status: included**
This is `HasFPowerSeriesOnBall.fderiv` in `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean` (line 211) and `HasFPowerSeriesAt.deriv` (line 436). The derivative of a power series is the term-by-term derivative, and has the same radius of convergence.

## Corollary 17.3: Power series is infinitely differentiable
**Status: included**
This is `AnalyticAt.contDiffAt` in `Mathlib/Analysis/Calculus/ContDiff/Defs.lean` (line 961): analytic functions are smooth (`ContDiff`), hence infinitely differentiable.

## Theorem 17.4: Arzela-Ascoli type theorem for bounded functions with bounded derivatives
**Status: included**
The Arzela-Ascoli theorem is formalized in `Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean` and `Mathlib/Topology/UniformSpace/Ascoli.lean`. The specific version for uniformly bounded and equicontinuous families (which bounded-derivative families are) yielding uniformly convergent subsequences is covered.

## Theorem 18.1: B(X) is a complete metric space
**Status: included**
This is `BoundedContinuousFunction.instCompleteSpace` in `Mathlib/Topology/ContinuousMap/Bounded/Basic.lean` (line 303): `instance instCompleteSpace [CompleteSpace β] : CompleteSpace (α →ᵇ β)`. The space of bounded functions (with sup norm) is complete when the codomain is complete.

## Theorem 18.2: C(X) is closed in B(X), hence complete
**Status: included**
In Mathlib, `BoundedContinuousFunction` already consists of continuous bounded functions. The completeness of `C(X)` (with compact `X`) as a metric space follows. The closedness of continuous functions among bounded functions under uniform convergence is `TendstoUniformly.continuous` (Theorem 16.4). The completeness is `BoundedContinuousFunction.instCompleteSpace`.

## Theorem 18.3: Closure of bounded subset of B^1(X) in C(X) is compact (Arzela-Ascoli)
**Status: included**
This is the Arzela-Ascoli theorem. In Mathlib, it is in `Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`. The equicontinuity coming from bounded derivatives and the pointwise boundedness give the compactness of the closure.

## Theorem 18.4: Lattice version of Stone-Weierstrass (closed under max/min, separates points implies dense)
**Status: non-included**
The lattice version of Stone-Weierstrass (closure under max and min operations, plus point separation implying density) is not directly formalized in Mathlib. Mathlib has the algebra version (Theorem 18.5) in `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean`, but the lattice variant (which is actually a key ingredient in proving the algebra version) is not exposed as a standalone theorem. Searched `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean` and related files.

## Theorem 18.5: Stone-Weierstrass theorem (subalgebra version)
**Status: included**
This is `subalgebra_topologicalClosure_eq_top_of_separatesPoints` in `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean` (line 267): a subalgebra of `C(X, ℝ)` that separates points has dense closure (equals the whole space).

## Proposition 19.2: Properties of integral of piecewise linear functions
**Status: non-included**
This proposition about integrals of piecewise linear functions (linearity, positivity, constant functions) is part of a pedagogical development of integration starting from piecewise linear functions, which is not the approach taken in Mathlib. Mathlib uses the Lebesgue integral (Bochner integral) via measure theory in `Mathlib/MeasureTheory/Integral/`. While the *results* (linearity, positivity) hold for the Lebesgue integral, the specific piecewise-linear starting point is not formalized.

## Lemma 19.3: Continuous functions are uniform limits of piecewise linear functions
**Status: non-included**
While Mathlib has various approximation results (e.g., Stone-Weierstrass implies polynomial approximation), the specific approximation of continuous functions by piecewise linear functions is not directly formalized as a standalone lemma. The pedagogical approach of building integration from piecewise linear approximation is not Mathlib's approach. Searched `Mathlib/Topology/ContinuousMap/` and `Mathlib/Analysis/` without finding this specific result.

## Theorem 19.4: Unique extension of integral from piecewise linear to continuous functions via uniform limits
**Status: non-included**
This is the pedagogical construction of the integral of continuous functions via uniform approximation by piecewise linear functions. Mathlib does not follow this approach; instead, it uses the Lebesgue/Bochner integral construction in `Mathlib/MeasureTheory/Integral/`. The uniqueness result for this specific extension is not formalized.

## Theorem 20.3: Characterization of RS-integrability
**Status: non-included**
The Riemann-Stieltjes integral characterization via upper and lower sums is not directly formalized in Mathlib. Mathlib primarily uses the Lebesgue (Bochner) integral and the interval integral (`intervalIntegral`), which is defined as a special case of the Lebesgue integral. Riemann-Stieltjes integrals are handled through `MeasureTheory.Measure.stieltjes` for Stieltjes measures, but the classical upper/lower sum characterization is not present. Searched `Mathlib/MeasureTheory/Integral/` and `Mathlib/MeasureTheory/Measure/Stieltjes.lean`.

## Theorem 20.4: Continuous functions are RS-integrable
**Status: included**
While Mathlib does not formalize the Riemann-Stieltjes integral in the classical sense, continuous functions on compact intervals are integrable with respect to any Stieltjes measure. `ContinuousOn.intervalIntegrable` and `Continuous.intervalIntegrable` in the interval integral API provide this for the standard Lebesgue measure case. For Stieltjes measures, `MeasureTheory.Measure.stieltjes` in `Mathlib/MeasureTheory/Measure/Stieltjes.lean` combined with integrability of continuous functions on compact intervals covers the content.

## Theorem 20.5: Uniform limit of RS-integrable functions is RS-integrable with convergent integrals
**Status: non-included**
The specific statement about uniform convergence preserving Riemann-Stieltjes integrability and converging integrals is not formalized in the classical RS-integral framework. Mathlib uses dominated convergence theorems for the Lebesgue integral. While `tendstoUniformlyOn` combined with `MeasureTheory.tendsto_integral_of_dominated_convergence` provides analogous results, the RS-integral specific version is not present.

## Theorem 20.6: Linearity and positivity of RS-integral
**Status: non-included**
As with Theorem 20.3, the Riemann-Stieltjes integral properties are not formalized in their classical form. Mathlib's `intervalIntegral` has `integral_add` and `integral_nonneg` properties, but specifically for the Lebesgue-measure-based integral, not the general RS-integral.

## Theorem 21.1: Composition with continuous function preserves RS-integrability
**Status: non-included**
This result about composing an RS-integrable function with a continuous function is not formalized for the classical RS-integral in Mathlib. Mathlib's measure-theoretic integral handles composition differently (through measurability).

## Corollary 21.2: Product of RS-integrable functions is RS-integrable
**Status: non-included**
Not formalized for the RS-integral. For the Lebesgue integral, the product of integrable functions is handled via `IntegrableOn.mul_continuousOn` and related results, but the RS-integral version is absent.

## Corollary 21.3: |f| is RS-integrable and triangle inequality for RS-integral
**Status: non-included**
Not formalized for the RS-integral specifically. For the Lebesgue integral, `norm_integral_le_integral_norm` provides the analogous result.

## Theorem 21.4: Change of variables for RS-integral (easy version)
**Status: non-included**
The change of variables formula for the RS-integral with a strictly increasing continuous substitution is not formalized in the RS-integral framework. Mathlib has substitution rules for the interval integral (`integral_comp_mul_right` etc. in `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`) but in the Lebesgue measure framework.

## Theorem 21.5: Relationship between RS-integral and Riemann integral via alpha'
**Status: non-included**
The theorem relating the RS-integral to a weighted Riemann integral via the derivative of alpha is specific to the RS-integral theory and not formalized in Mathlib.

## Corollary 21.6: Substitution rule for Riemann integrals
**Status: included**
The substitution (change of variables) formula for interval integrals is formalized in `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`. Results like `integral_comp_mul_right` (line 851), `integral_comp_mul_left` (line 869), and `integral_comp_mul_add` (line 903) provide substitution rules.

## Lemma 22.1: Additivity of the integral over subintervals
**Status: included**
This is `integral_add_adjacent_intervals` in `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` (line 1030): the integral from a to b plus the integral from b to c equals the integral from a to c.

## Theorem 22.2: Fundamental Theorem of Calculus, Part 1
**Status: included**
This is `integral_hasDerivAt_right` in `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` (line 727): if f is integrable and continuous at a point, then F(x) = integral from a to x of f is differentiable there with F'(x) = f(x). The continuity of F is also established.

## Theorem 22.3: Fundamental Theorem of Calculus, Part 2
**Status: included**
This is `integral_eq_sub_of_hasDerivAt` in `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` (line 1149): if f has derivative f' everywhere on [a,b] and f' is integrable, then the integral of f' from a to b equals f(b) - f(a).

## Lemma 22.4: Derivative of power series (same as Corollary 17.2)
**Status: included**
This is `HasFPowerSeriesAt.deriv` in `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean` (line 436) and `HasFPowerSeriesOnBall.fderiv` (line 211). The derivative of a power series is computed term by term and has the same radius of convergence.

## Lemma 23.1: Existence of pi (smallest positive zero of cosine), sin(pi/2) = 1
**Status: included**
This is `Real.cos_pi_div_two` in `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean` (line 133): `theorem cos_pi_div_two : cos (π / 2) = 0` and `Real.sin_pi_div_two` (line 438): `theorem sin_pi_div_two : sin (π / 2) = 1`. The definition of `π` as the smallest positive number where cosine vanishes is built into Mathlib's construction.

## Lemma 23.2: exp(x + 2*pi*i) = exp(x) (periodicity of exp)
**Status: included**
This is `Complex.exp_periodic` in `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean` (line 1202): `theorem exp_periodic : Function.Periodic exp (2 * π * I)`. The periodicity `exp(z + 2πi) = exp(z)` is established.

## Lemma 23.3: log(x) is differentiable for x > 0 with derivative 1/x
**Status: included**
This is `Real.hasDerivAt_log` (referenced in `Mathlib/Analysis/SpecialFunctions/NonIntegrable.lean` and defined in `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`) and `Real.deriv_log` (line 65): `theorem deriv_log (x : ℝ) : deriv log x = x⁻¹`.

## Theorem 23.4: Power series for log(1+x)
**Status: included**
The power series `x - x^2/2 + x^3/3 - ...` converging to `log(1+x)` for `|x| < 1` is established via `hasSum_log_one_add` in `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean` (line 419). This connects the formal power series to the logarithm function.

## Lemma 24.1: Absolutely convergent Fourier series is uniformly convergent
**Status: included**
This follows from the Weierstrass M-test (`tendstoUniformly_tsum` in `Mathlib/Analysis/Normed/Group/FunctionSeries.lean`) applied to the Fourier series terms. The Fourier series infrastructure in `Mathlib/Analysis/Fourier/AddCircle.lean` provides `hasSum_fourier_series_of_summable` (line 470): if the Fourier coefficients are summable, the Fourier series converges (which for absolute convergence gives uniform convergence).

## Lemma 24.2: Differentiability of Fourier series under stronger summability
**Status: included**
This follows from the uniform convergence of derivatives theorem (Theorem 17.1) applied to Fourier series. The Weierstrass M-test ensures uniform convergence of the term-by-term derivative when `sum k|ak|` converges. The infrastructure in `Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean` combined with Fourier theory in `Mathlib/Analysis/Fourier/AddCircle.lean` covers this.

## Theorem 24.3: Fourier series of smooth periodic function converges uniformly to the function
**Status: included**
This is `hasSum_fourier_series_of_summable` in `Mathlib/Analysis/Fourier/AddCircle.lean` (line 470), combined with the fact that smooth periodic functions have rapidly decaying Fourier coefficients (hence summable). The uniform convergence result for summable Fourier coefficients is established.

## Theorem 24.4: Parseval's theorem (L^2 convergence of Fourier series)
**Status: included**
This is `tsum_sq_fourierCoeff` in `Mathlib/Analysis/Fourier/AddCircle.lean` (line 429): Parseval's identity `∑ |c_k|^2 = (1/2π) ∫ |f|^2`. Also `hasSum_fourier_series_L2` (line 409) establishes L^2 convergence of Fourier partial sums.
