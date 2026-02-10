# Detailed Assessment: Analysis II Statements in Mathlib

## Statement 1: Definition 1.1
**Status**: included
**Explanation**: The Cartesian product is a basic set-theoretic construction available throughout Lean/Mathlib as the `Prod` type.
**Mathlib references**: `Init.Prelude` (Prod type), used ubiquitously throughout Mathlib.

## Statement 2: Definition 1.2
**Status**: included
**Explanation**: Metric spaces are extensively formalized in Mathlib via `MetricSpace` and `PseudoMetricSpace` type classes.
**Mathlib references**: `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean` (`PseudoMetricSpace`), `Mathlib/Topology/MetricSpace/Defs.lean` (`MetricSpace`).

## Statement 3: Definition 1.3
**Status**: included
**Explanation**: Open balls are defined as `Metric.ball` in Mathlib.
**Mathlib references**: `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean` (`Metric.ball`).

## Statement 4: Definition 1.4
**Status**: included
**Explanation**: Open sets in metric spaces are part of the induced topology in Mathlib. The `IsOpen` predicate is fundamental.
**Mathlib references**: `Mathlib/Topology/Basic.lean` (`IsOpen`), `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`.

## Statement 5: Proposition 1.5
**Status**: included
**Explanation**: Arbitrary unions of open sets are open. This is an axiom of `TopologicalSpace` in Mathlib.
**Mathlib references**: `Mathlib/Topology/Basic.lean` (`isOpen_sUnion`, `isOpen_iUnion`).

## Statement 6: Corollary 1
**Status**: included
**Explanation**: This is the characterization of the subspace topology: open sets in a subspace are intersections with open sets of the ambient space.
**Mathlib references**: `Mathlib/Topology/Constructions.lean` (`isOpen_induced_iff`).

## Statement 7: Proposition 1.6
**Status**: included
**Explanation**: Finite intersections of open sets are open. This is an axiom of `TopologicalSpace`.
**Mathlib references**: `Mathlib/Topology/Basic.lean` (`IsOpen.inter`).

## Statement 8: Definition 1.7
**Status**: included
**Explanation**: Set complement is a basic operation in Lean (`Set.compl`).
**Mathlib references**: `Mathlib/Order/SetPartition/Basic.lean`, standard set operations throughout Mathlib.

## Statement 9: Definition 1.8
**Status**: included
**Explanation**: Closed sets are defined as complements of open sets via `IsClosed`.
**Mathlib references**: `Mathlib/Topology/Basic.lean` (`IsClosed`).

## Statement 10: Definition 1.9
**Status**: included
**Explanation**: The Euclidean norm on $\mathbb{R}^n$ is formalized via the inner product space structure.
**Mathlib references**: `Mathlib/Analysis/InnerProductSpace/Basic.lean`, `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.

## Statement 11: Proposition 1.10
**Status**: included
**Explanation**: The equivalence of the $\ell^2$ and $\ell^\infty$ norms on finite-dimensional spaces is captured by the fact that all norms on a finite-dimensional space induce the same topology.
**Mathlib references**: `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` (topology uniqueness for finite-dimensional normed spaces).

## Statement 12: Definition 1.11
**Status**: included
**Explanation**: Continuity at a point is defined via filters and `ContinuousAt` in Mathlib.
**Mathlib references**: `Mathlib/Topology/ContinuousOn.lean` (`ContinuousAt`).

## Statement 13: Definition 1.12
**Status**: included
**Explanation**: Continuous functions are defined via `Continuous` in Mathlib.
**Mathlib references**: `Mathlib/Topology/Continuous.lean` (`Continuous`).

## Statement 14: Theorem 1.13
**Status**: included
**Explanation**: The equivalence between the epsilon-delta definition and the preimage definition of continuity is fundamental in Mathlib.
**Mathlib references**: `Mathlib/Topology/Continuous.lean` (`continuous_def`).

## Statement 15: Definition 1.14
**Status**: included
**Explanation**: Homeomorphisms are formalized via `Homeomorph`.
**Mathlib references**: `Mathlib/Topology/Homeomorph.lean` (`Homeomorph`).

## Statement 16: Definition 1.15
**Status**: included
**Explanation**: Convergence of sequences is a special case of filter convergence via `Filter.Tendsto`.
**Mathlib references**: `Mathlib/Topology/Sequences.lean`, `Mathlib/Order/Filter/Basic.lean` (`Filter.Tendsto`).

## Statement 17: Theorem 1.16
**Status**: included
**Explanation**: Sequential characterization of continuity. In first-countable spaces (which include metric spaces), continuity is equivalent to sequential continuity.
**Mathlib references**: `Mathlib/Topology/Sequences.lean` (`continuous_iff_sequentiallyContinuous` for first-countable spaces).

## Statement 18: Definition 1.17
**Status**: included
**Explanation**: Bounded sets in metric spaces are formalized via `Bornology.IsBounded` (formerly `Metric.Bounded`).
**Mathlib references**: `Mathlib/Topology/MetricSpace/Bounded.lean` (`Bornology.IsBounded`).

## Statement 19: Proposition 1.18
**Status**: included
**Explanation**: The closure of a set is formalized via `closure`.
**Mathlib references**: `Mathlib/Topology/Closure.lean` (`closure`).

## Statement 20: Definition 1.19
**Status**: included
**Explanation**: Compactness is formalized via `IsCompact` in Mathlib, using the open cover definition (equivalent to sequential compactness in metric spaces).
**Mathlib references**: `Mathlib/Topology/Compactness/Compact.lean` (`IsCompact`), `Mathlib/Topology/Sequences.lean` (`isCompact_iff_isSeqCompact`).

## Statement 21: Theorem 1.20 (Heine-Borel)
**Status**: included
**Explanation**: The Heine-Borel theorem for $\mathbb{R}^n$ is formalized: compact iff closed and bounded.
**Mathlib references**: `Mathlib/Topology/MetricSpace/Bounded.lean` (`isCompact_iff_isClosed_bounded` for proper spaces).

## Statement 22: Theorem 1.21
**Status**: included
**Explanation**: The continuous image of a compact set is compact.
**Mathlib references**: `Mathlib/Topology/Compactness/Compact.lean` (`IsCompact.image`).

## Statement 23: Corollary 2
**Status**: included
**Explanation**: A continuous function on a compact set attains its maximum and minimum.
**Mathlib references**: `Mathlib/Topology/Compactness/Compact.lean` (`IsCompact.exists_isMinOn`, `IsCompact.exists_isMaxOn`).

## Statement 24: Theorem 1.22
**Status**: included
**Explanation**: A continuous bijection from a compact space to a Hausdorff space is a homeomorphism.
**Mathlib references**: `Mathlib/Topology/Compactness/Compact.lean` (`Continuous.isClosedMap` for compact domain, yielding homeomorphism).

## Statement 25: Definition 1.23
**Status**: included
**Explanation**: Open coverings are used implicitly in the definition of compactness.
**Mathlib references**: `Mathlib/Topology/Compactness/Compact.lean`.

## Statement 26: Theorem 1.24 (Heine-Borel, open cover version)
**Status**: included
**Explanation**: Compactness is defined via the finite subcover property in Mathlib.
**Mathlib references**: `Mathlib/Topology/Compactness/Compact.lean` (`isCompact_iff_finite_subcover`).

## Statement 27: Proposition 1.25
**Status**: included
**Explanation**: A closed subset of a compact set is compact.
**Mathlib references**: `Mathlib/Topology/Compactness/Compact.lean` (`IsClosed.isCompact` or `IsCompact.of_isClosed_subset`).

## Statement 28: Theorem 1.26
**Status**: included
**Explanation**: A continuous function on a compact metric space is uniformly continuous.
**Mathlib references**: `Mathlib/Topology/UniformSpace/CompactConvergence.lean`, `Mathlib/Topology/UniformSpace/Cauchy.lean` (`IsCompact.uniformContinuousOn_of_continuous`).

## Statement 29: Definition 1.27
**Status**: included
**Explanation**: Connected spaces and sets are defined via `IsConnected` and `ConnectedSpace`.
**Mathlib references**: `Mathlib/Topology/Connected/Basic.lean` (`ConnectedSpace`, `IsConnected`).

## Statement 30: Theorem 1.28
**Status**: included
**Explanation**: The continuous image of a connected set is connected.
**Mathlib references**: `Mathlib/Topology/Connected/Basic.lean` (`IsConnected.image`).

## Statement 31: Theorem 1.29 (Intermediate Value Theorem)
**Status**: included
**Explanation**: The intermediate value theorem is formalized in Mathlib.
**Mathlib references**: `Mathlib/Topology/Order/IntermediateValue.lean` (`intermediate_value_uIcc`).

## Statement 32: Definition 2.1
**Status**: included
**Explanation**: The Frechet derivative (total derivative) is formalized via `HasFDerivAt`.
**Mathlib references**: `Mathlib/Analysis/Calculus/FDeriv/Basic.lean` (`HasFDerivAt`).

## Statement 33: Definition 2.2
**Status**: included
**Explanation**: The derivative as a continuous linear map is `fderiv`.
**Mathlib references**: `Mathlib/Analysis/Calculus/FDeriv/Basic.lean` (`fderiv`).

## Statement 34: Proposition 2.3
**Status**: included
**Explanation**: Uniqueness of the Frechet derivative is built into the formalization.
**Mathlib references**: `Mathlib/Analysis/Calculus/FDeriv/Basic.lean` (`HasFDerivAt.unique`).

## Statement 35: Theorem 2.4
**Status**: included
**Explanation**: Differentiability implies continuity.
**Mathlib references**: `Mathlib/Analysis/Calculus/FDeriv/Basic.lean` (`HasFDerivAt.continuousAt`).

## Statement 36: Theorem 2.5 (Chain Rule)
**Status**: included
**Explanation**: The chain rule for Frechet derivatives is formalized.
**Mathlib references**: `Mathlib/Analysis/Calculus/FDeriv/Comp.lean` (`HasFDerivAt.comp`).

## Statement 37: Definition 2.6
**Status**: included
**Explanation**: Partial derivatives are available via `fderiv` composed with basis vectors or via `HasFDerivAt` restricted to coordinate directions.
**Mathlib references**: `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`, `Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Statement 38: Theorem 2.7
**Status**: included
**Explanation**: The Frechet derivative, when it exists, determines and is determined by the partial derivatives (the Jacobian matrix).
**Mathlib references**: `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

## Statement 39: Theorem 2.8
**Status**: included
**Explanation**: If all partial derivatives exist and are continuous, then the function is differentiable. This is captured by `ContDiff` implying `Differentiable`.
**Mathlib references**: `Mathlib/Analysis/Calculus/ContDiff/Basic.lean` (`ContDiff.differentiable`).

## Statement 40: Definition 2.9
**Status**: included
**Explanation**: $\mathcal{C}^k$ smoothness is formalized via `ContDiff`.
**Mathlib references**: `Mathlib/Analysis/Calculus/ContDiff/Defs.lean` (`ContDiff`).

## Statement 41: Definition 2.10
**Status**: included
**Explanation**: $\mathcal{C}^\infty$ smoothness is `ContDiff` with $k = \infty$ (i.e., `⊤`).
**Mathlib references**: `Mathlib/Analysis/Calculus/ContDiff/Defs.lean` (`ContDiff ℝ ⊤ f`).

## Statement 42: Theorem 2.11 (Inverse Function Theorem)
**Status**: included
**Explanation**: The inverse function theorem is formalized in Mathlib.
**Mathlib references**: `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`.

## Statement 43: Definition 2.12
**Status**: included
**Explanation**: Diffeomorphisms are not a single type class but the concept is captured by combining `Homeomorph` with `ContDiff` conditions, or using local diffeomorphisms.
**Mathlib references**: `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`, `Mathlib/Geometry/Manifold/Diffeomorph.lean`.

## Statement 44: Theorem 2.13 (Implicit Function Theorem)
**Status**: included
**Explanation**: The implicit function theorem is formalized in Mathlib.
**Mathlib references**: `Mathlib/Analysis/Calculus/Implicit.lean`, `Mathlib/Analysis/Calculus/ImplicitContDiff.lean`.

## Statement 45: Definition 3.1
**Status**: included
**Explanation**: Bump functions are formalized in Mathlib, including the construction of smooth bump functions.
**Mathlib references**: `Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`, `Mathlib/Topology/MetricSpace/PartitionOfUnity.lean`.

## Statement 46: Definition 3.2
**Status**: included
**Explanation**: Convolution is formalized in Mathlib.
**Mathlib references**: `Mathlib/Analysis/Convolution.lean`.

## Statement 47: Theorem 3.3
**Status**: included
**Explanation**: The smoothness of convolution of a smooth compactly supported function with an integrable function is covered.
**Mathlib references**: `Mathlib/Analysis/Convolution.lean` (smoothness results for convolutions).

## Statement 48: Definition 3.4
**Status**: included
**Explanation**: The support of a function is defined as `Function.support` or `tsupport` (closure of support).
**Mathlib references**: `Mathlib/Topology/Support.lean` (`tsupport`, `HasCompactSupport`).

## Statement 49: Theorem 3.5 (Partitions of Unity)
**Status**: included
**Explanation**: Existence of smooth partitions of unity is formalized in Mathlib for metric spaces and manifolds.
**Mathlib references**: `Mathlib/Topology/PartitionOfUnity.lean`, `Mathlib/Topology/MetricSpace/PartitionOfUnity.lean`.

## Statement 50: Definition 3.6
**Status**: included
**Explanation**: Partitions of unity are formalized in Mathlib.
**Mathlib references**: `Mathlib/Topology/PartitionOfUnity.lean` (`PartitionOfUnity`).

## Statement 51: Definition 4.1
**Status**: included
**Explanation**: The dual space is formalized as `Module.Dual` or the space of continuous linear maps.
**Mathlib references**: `Mathlib/LinearAlgebra/Dual.lean` (`Module.Dual`).

## Statement 52: Definition 4.2
**Status**: included
**Explanation**: Dual bases are formalized in Mathlib.
**Mathlib references**: `Mathlib/LinearAlgebra/Dual.lean` (`Basis.dualBasis`).

## Statement 53: Definition 4.3
**Status**: included
**Explanation**: Multilinear maps are formalized via `MultilinearMap`.
**Mathlib references**: `Mathlib/LinearAlgebra/Multilinear/Basic.lean` (`MultilinearMap`).

## Statement 54: Definition 4.4
**Status**: included
**Explanation**: Tensor products of multilinear maps are available.
**Mathlib references**: `Mathlib/LinearAlgebra/Multilinear/Basic.lean`, `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`.

## Statement 55: Definition 4.5
**Status**: included
**Explanation**: Alternating multilinear maps are formalized via `AlternatingMap`.
**Mathlib references**: `Mathlib/LinearAlgebra/Alternating/Basic.lean` (`AlternatingMap`).

## Statement 56: Definition 4.6
**Status**: included
**Explanation**: The exterior power $\Lambda^k(V^*)$ is formalized via `ExteriorAlgebra` and `ExteriorPower`.
**Mathlib references**: `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`, `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean`.

## Statement 57: Definition 4.7
**Status**: included
**Explanation**: The alternation operator is part of the theory of alternating maps.
**Mathlib references**: `Mathlib/LinearAlgebra/Alternating/Basic.lean` (`MultilinearMap.alternatization`).

## Statement 58: Theorem 4.8
**Status**: included
**Explanation**: The dimension of $\Lambda^k(V^*)$ equals $\binom{n}{k}$ is formalized.
**Mathlib references**: `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean` (finiteness and rank results).

## Statement 59: Definition 4.9
**Status**: included
**Explanation**: The wedge product is defined in the exterior algebra.
**Mathlib references**: `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean` (`ExteriorAlgebra.ι`, multiplication in the exterior algebra).

## Statement 60: Theorem 4.10
**Status**: included
**Explanation**: Associativity of the wedge product follows from the algebra structure of the exterior algebra.
**Mathlib references**: `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean` (algebra multiplication is associative).

## Statement 61: Theorem 4.11
**Status**: included
**Explanation**: The graded-commutativity $\omega \wedge \mu = (-1)^{k\ell} \mu \wedge \omega$ is part of the exterior algebra theory.
**Mathlib references**: `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean` (`ExteriorAlgebra.ι_mul_ι`).

## Statement 62: Theorem 4.12
**Status**: included
**Explanation**: The basis theorem for exterior powers: wedge products of dual basis elements form a basis of $\Lambda^k(V^*)$.
**Mathlib references**: `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean`.

## Statement 63: Theorem 4.13
**Status**: included
**Explanation**: The wedge product of 1-forms evaluated on vectors gives the determinant: $\omega_1 \wedge \cdots \wedge \omega_k(v_1, \ldots, v_k) = \det[\omega_i(v_j)]$.
**Mathlib references**: `Mathlib/LinearAlgebra/Alternating/Basic.lean` (`AlternatingMap.apply_eq_det`).

## Statement 64: Definition 4.14
**Status**: included
**Explanation**: The pullback of alternating maps by a linear map is formalized.
**Mathlib references**: `Mathlib/LinearAlgebra/Alternating/Basic.lean` (`AlternatingMap.compLinearMap`).

## Statement 65: Theorem 4.15
**Status**: included
**Explanation**: Pullback preserves the wedge product. This is captured in the exterior algebra.
**Mathlib references**: `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`.

## Statement 66: Definition 4.16
**Status**: included
**Explanation**: The determinant of a linear endomorphism is defined in Mathlib.
**Mathlib references**: `Mathlib/LinearAlgebra/Determinant.lean` (`LinearMap.det`).

## Statement 67: Theorem 4.17
**Status**: included
**Explanation**: The multiplicativity of the determinant: $\det(AB) = \det(A)\det(B)$.
**Mathlib references**: `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` (`Matrix.det_mul`).

## Statement 68: Theorem 4.18
**Status**: included
**Explanation**: The determinant of a matrix equals the determinant of its transpose.
**Mathlib references**: `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` (`Matrix.det_transpose`).

## Statement 69: Definition 4.33
**Status**: included
**Explanation**: Orientation of a one-dimensional vector space is formalized as part of the orientation theory.
**Mathlib references**: `Mathlib/LinearAlgebra/Orientation.lean` (`Orientation`).

## Statement 70: Definition 4.34
**Status**: included
**Explanation**: Orientation of an n-dimensional vector space via $\Lambda^n(V^*)$ is formalized.
**Mathlib references**: `Mathlib/LinearAlgebra/Orientation.lean` (`Orientation`).

## Statement 71: Definition 4.35
**Status**: included
**Explanation**: Positively oriented bases are part of the orientation theory.
**Mathlib references**: `Mathlib/LinearAlgebra/Orientation.lean`.

## Statement 72: Definition 4.36
**Status**: included
**Explanation**: Tangent spaces of $\mathbb{R}^n$ (identified with $\mathbb{R}^n$ itself) are trivially included. In Mathlib's manifold library, tangent spaces are formalized more generally.
**Mathlib references**: `Mathlib/Geometry/Manifold/MFDeriv/Basic.lean` (`TangentSpace`).

## Statement 73: Definition 4.37
**Status**: included
**Explanation**: The cotangent space (dual of the tangent space) is available as the dual. In Mathlib, cotangent spaces are related to Kahler differentials in algebraic settings, and the dual of the tangent space in the differential geometry setting.
**Mathlib references**: `Mathlib/LinearAlgebra/Dual.lean`, `Mathlib/RingTheory/Kaehler/Basic.lean`.

## Statement 74: Definition 4.38
**Status**: non-included
**Explanation**: Differential k-forms on open subsets of $\mathbb{R}^n$ (as sections of exterior powers of the cotangent bundle) are only partially formalized in Mathlib. Mathlib has `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` which is a very recent and limited development. The general theory of differential forms as presented in this textbook is not fully formalized.
**Mathlib references**: `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` (partial, limited).

## Statement 75: Definition 4.39
**Status**: non-included
**Explanation**: The notion of a $\mathcal{C}^r$ k-form (smoothness class of differential forms) is not formalized in this generality in Mathlib.
**Mathlib references**: None directly applicable.

## Statement 76: Definition 4.40
**Status**: non-included
**Explanation**: The space $\Omega^k(U)$ of smooth k-forms is not formalized as a standalone object in Mathlib.
**Mathlib references**: `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` (partial).

## Statement 77: Definition 4.41
**Status**: included
**Explanation**: The convention $\Lambda^0(V^*) = \mathbb{R}$ is standard and follows from the exterior algebra construction.
**Mathlib references**: `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`.

## Statement 78: Definition 4.42
**Status**: non-included
**Explanation**: Decomposable differential forms are not a formalized concept in Mathlib.
**Mathlib references**: None.

## Statement 79: Theorem 4.43
**Status**: non-included
**Explanation**: The formula for the exterior derivative of a decomposable form is not formalized in Mathlib. The exterior derivative d on differential forms is not fully formalized.
**Mathlib references**: None.

## Statement 80: Definition 4.44
**Status**: non-included
**Explanation**: The pullback operation on differential forms (as opposed to the algebraic pullback on alternating maps) is not formalized in the differential forms context in Mathlib.
**Mathlib references**: None directly (algebraic pullback exists in `Mathlib/LinearAlgebra/Alternating/Basic.lean`).

## Statement 81: Theorem 4.45
**Status**: non-included
**Explanation**: The commutativity of pullback and exterior derivative ($df^*\omega = f^*d\omega$) is not formalized in Mathlib. This requires a full theory of differential forms which is not yet developed.
**Mathlib references**: None.

## Statement 82: Definition 5.1
**Status**: non-included
**Explanation**: The support of a differential form is not formalized as such. While `tsupport` exists for functions, the extension to k-forms on open sets is not present.
**Mathlib references**: `Mathlib/Topology/Support.lean` (for functions only).

## Statement 83: Definition 5.2
**Status**: non-included
**Explanation**: Compactly supported k-forms $\Omega_c^k(U)$ are not formalized in Mathlib.
**Mathlib references**: None.

## Statement 84: Definition 5.3
**Status**: non-included
**Explanation**: Integration of n-forms over open sets is not formalized in this differential forms framework. Mathlib uses measure-theoretic integration (Lebesgue/Bochner integral) rather than integration of differential forms.
**Mathlib references**: None in the differential forms sense. Measure-theoretic integration is in `Mathlib/MeasureTheory/Integral/`.

## Statement 85: Definition 5.4
**Status**: non-included
**Explanation**: Orientation preserving/reversing maps in the context of differential forms and sign of the Jacobian determinant is not directly formalized in this form in Mathlib.
**Mathlib references**: `Mathlib/LinearAlgebra/Orientation.lean` has orientation-related concepts but not this specific definition.

## Statement 86: Theorem 5.5 (Change of Variables)
**Status**: included
**Explanation**: The change of variables formula for integrals is formalized in Mathlib in the measure-theoretic setting via the Jacobian determinant.
**Mathlib references**: `Mathlib/MeasureTheory/Function/Jacobian.lean` (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`).

## Statement 87: Theorem 5.6
**Status**: included
**Explanation**: This is the coordinate version of the change of variables formula, which is equivalent to the measure-theoretic version in Mathlib.
**Mathlib references**: `Mathlib/MeasureTheory/Function/Jacobian.lean`.

## Statement 88: Sard's Theorem
**Status**: non-included
**Explanation**: Sard's theorem (the image of the critical set has measure zero) is not formalized in Mathlib.
**Mathlib references**: None.

## Statement 89: Lemma 5.7
**Status**: non-included
**Explanation**: This technical lemma used in the proof of Sard's theorem for one-dimensional maps is not formalized.
**Mathlib references**: None.

## Statement 90: Lemma 5.8
**Status**: non-included
**Explanation**: This inductive lemma used in the proof of the Poincare Lemma is not formalized.
**Mathlib references**: None.

## Statement 91: Poincare Lemma
**Status**: non-included
**Explanation**: The Poincare Lemma (for compactly supported top-degree forms on connected open sets) is not formalized in Mathlib. While there is a file `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`, it deals with a different aspect (Poincare inequality for curve integrals), not the de Rham cohomological Poincare Lemma.
**Mathlib references**: None directly applicable.

## Statement 92: Definition 5.9
**Status**: non-included
**Explanation**: Exact differential forms ($\omega = d\mu$) are not formally defined in Mathlib since the exterior derivative on forms is not fully developed.
**Mathlib references**: None.

## Statement 93: Definition 5.10
**Status**: non-included
**Explanation**: Closed differential forms ($d\omega = 0$) are not formally defined in Mathlib for the same reason.
**Mathlib references**: None.

## Statement 94: Lemma 5.11
**Status**: non-included
**Explanation**: This connectivity lemma about chaining rectangles in a connected open set is not formalized.
**Mathlib references**: None.

## Statement 95: Definition 5.12
**Status**: included
**Explanation**: Proper maps are formalized in Mathlib via `IsProperMap`.
**Mathlib references**: `Mathlib/Topology/Maps/Basic.lean` (`IsProperMap`).

## Statement 96: Theorem 5.13
**Status**: non-included
**Explanation**: The degree theorem (integral formula $\int f^*\omega = \deg(f) \int \omega$) is not formalized in Mathlib. There is no theory of topological degree via differential forms.
**Mathlib references**: None.

## Statement 97: Theorem 5.14
**Status**: non-included
**Explanation**: Same as Statement 96. The existence of the degree constant is not formalized.
**Mathlib references**: None.

## Statement 98: Definition 5.15
**Status**: non-included
**Explanation**: The degree of a proper smooth map is not defined in Mathlib.
**Mathlib references**: None.

## Statement 99: Theorem 5.16
**Status**: non-included
**Explanation**: The theorem relating degree to orientation (deg = +1 for orientation preserving, -1 for reversing diffeomorphisms) is not formalized.
**Mathlib references**: None.

## Statement 100: Lemma 5.17
**Status**: non-included
**Explanation**: This technical lemma about bounding $|g(x)|$ near a fixed point is not formalized as a standalone result.
**Mathlib references**: None.

## Statement 101: Definition 5.18
**Status**: non-included
**Explanation**: Regular values of smooth maps are not formalized in Mathlib (related to absent Sard theory).
**Mathlib references**: None.

## Statement 102: Lemma 5.19
**Status**: non-included
**Explanation**: The finiteness of preimages at regular values for proper maps is not formalized.
**Mathlib references**: None.

## Statement 103: Theorem 5.20
**Status**: non-included
**Explanation**: The formula computing degree as a signed count of preimages is not formalized.
**Mathlib references**: None.

## Statement 104: Theorem 5.21
**Status**: non-included
**Explanation**: The surjectivity theorem (nonzero degree implies surjectivity) is not formalized.
**Mathlib references**: None.

## Statement 105: Definition 5.22
**Status**: included
**Explanation**: Homotopies between continuous maps are formalized in Mathlib.
**Mathlib references**: `Mathlib/Topology/Homotopy/Basic.lean` (`ContinuousMap.Homotopy`).

## Statement 106: Definition 5.23
**Status**: non-included
**Explanation**: Proper homotopies (where the homotopy map itself is proper) are not formalized in Mathlib.
**Mathlib references**: None.

## Statement 107: Theorem 5.24
**Status**: non-included
**Explanation**: Homotopy invariance of degree is not formalized since degree theory is not developed.
**Mathlib references**: None.

## Statement 108: Definition 6.1
**Status**: included
**Explanation**: Canonical projections and inclusions of $\mathbb{R}^n$ are available as basic linear maps.
**Mathlib references**: `Mathlib/LinearAlgebra/Basic.lean`, `Mathlib/Analysis/NormedSpace/Basic.lean` (projections and inclusions as continuous linear maps).

## Statement 109: Canonical Submersion Theorem (Linear)
**Status**: included
**Explanation**: For a surjective linear map, the existence of a right inverse (and hence a change of basis making it a projection) follows from basic linear algebra in Mathlib.
**Mathlib references**: `Mathlib/LinearAlgebra/Basic.lean` (surjective linear maps split).

## Statement 110: Canonical Immersion Theorem (Linear)
**Status**: included
**Explanation**: For an injective linear map, the existence of a left inverse (and hence a change of basis making it an inclusion) follows from basic linear algebra.
**Mathlib references**: `Mathlib/LinearAlgebra/Basic.lean`.

## Statement 111: Definition 6.2
**Status**: non-included
**Explanation**: The concept of a submersion at a point (surjectivity of the derivative) is not formalized as a dedicated definition in Mathlib, though the condition $Df(p)$ surjective can be expressed.
**Mathlib references**: None as a specific definition.

## Statement 112: Canonical Submersion Theorem (Nonlinear)
**Status**: non-included
**Explanation**: The nonlinear canonical submersion theorem (local normal form for submersions) is not formalized in Mathlib. The inverse function theorem is available but the submersion theorem as stated is not.
**Mathlib references**: None directly. Related: `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`.

## Statement 113: Definition 6.3
**Status**: included
**Explanation**: Immersions are formalized in the manifold library.
**Mathlib references**: `Mathlib/Geometry/Manifold/Immersion.lean`.

## Statement 114: Canonical Immersion Theorem (Nonlinear)
**Status**: non-included
**Explanation**: The local normal form for immersions between Euclidean spaces is not directly formalized in Mathlib, though the manifold library has immersion-related results.
**Mathlib references**: `Mathlib/Geometry/Manifold/Immersion.lean` (partial, for manifolds).

## Statement 115: Definition 6.4
**Status**: included
**Explanation**: Diffeomorphisms between subsets of Euclidean space. In Mathlib, diffeomorphisms are formalized via `Diffeomorph` in the manifold context.
**Mathlib references**: `Mathlib/Geometry/Manifold/Diffeomorph.lean` (`Diffeomorph`).

## Statement 116: Definition 6.5
**Status**: included
**Explanation**: Manifolds are formalized in Mathlib via `ChartedSpace` and `IsManifold` (formerly `SmoothManifoldWithCorners`).
**Mathlib references**: `Mathlib/Geometry/Manifold/ChartedSpace.lean`, `Mathlib/Geometry/Manifold/IsManifold/`.

## Statement 117: Definition 6.6
**Status**: included
**Explanation**: Smooth maps between subsets of Euclidean spaces are handled via the general theory of smooth maps between manifolds.
**Mathlib references**: `Mathlib/Geometry/Manifold/ContMDiff/Defs.lean` (`ContMDiff`).

## Statement 118: Definition 6.7
**Status**: included
**Explanation**: Same as Definition 6.4 / Statement 115.
**Mathlib references**: `Mathlib/Geometry/Manifold/Diffeomorph.lean`.

## Statement 119: Definition 6.8
**Status**: included
**Explanation**: Same as Definition 6.5. Manifolds as subsets of $\mathbb{R}^N$ with local parameterizations.
**Mathlib references**: `Mathlib/Geometry/Manifold/ChartedSpace.lean`.

## Statement 120: Theorem 6.9
**Status**: non-included
**Explanation**: The regular value theorem (preimage of a regular value is a manifold) is not directly formalized in Mathlib. While the inverse function theorem exists, the specific statement about regular level sets being manifolds is not present.
**Mathlib references**: None directly.

## Statement 121: Definition 6.10
**Status**: included
**Explanation**: The tangent space of a manifold is formalized in Mathlib.
**Mathlib references**: `Mathlib/Geometry/Manifold/MFDeriv/Basic.lean` (`TangentSpace`).

## Statement 122: Definition 6.11
**Status**: non-included
**Explanation**: The alternate definition of tangent space as the kernel of df (for manifolds defined as level sets) is not a separate definition in Mathlib.
**Mathlib references**: None as a specific definition.

## Statement 123: Lemma 6.12
**Status**: non-included
**Explanation**: This specific lemma about images of smooth maps into manifolds landing in the tangent space is not formalized as a standalone result.
**Mathlib references**: Implicitly covered by `Mathlib/Geometry/Manifold/MFDeriv/Basic.lean`.

## Statement 124: Definition 6.13
**Status**: included
**Explanation**: The derivative of a smooth map between manifolds is formalized via `mfderiv`.
**Mathlib references**: `Mathlib/Geometry/Manifold/MFDeriv/Basic.lean` (`mfderiv`).

## Statement 125: Definition 6.14
**Status**: non-included
**Explanation**: k-forms on manifolds (sections of exterior powers of the cotangent bundle) are not formalized in Mathlib. The manifold library does not include a theory of differential forms on manifolds.
**Mathlib references**: None.

## Statement 126: Definition 6.15
**Status**: non-included
**Explanation**: Smooth k-forms on manifolds (via pullback by inclusion) are not formalized.
**Mathlib references**: None.

## Statement 127: Definition 6.16
**Status**: non-included
**Explanation**: Smooth k-forms (via pullback by parameterization) are not formalized.
**Mathlib references**: None.

## Statement 128: Definition 6.17
**Status**: non-included
**Explanation**: The space $\Omega^k(X)$ of smooth k-forms on a manifold is not formalized.
**Mathlib references**: None.

## Statement 129: Theorem 6.18
**Status**: non-included
**Explanation**: The extension theorem for smooth forms (every smooth form on X extends to a neighborhood) is not formalized.
**Mathlib references**: None.

## Statement 130: Theorem 6.19
**Status**: non-included
**Explanation**: The pullback of smooth forms by smooth maps between manifolds is not formalized in the differential forms context.
**Mathlib references**: None.

## Statement 131: Definition 6.20
**Status**: non-included
**Explanation**: The exterior derivative on manifolds is not formalized.
**Mathlib references**: None.

## Statement 132: Definition 6.21
**Status**: included
**Explanation**: Support of a function on a manifold. The general notion of support (`tsupport`) is available.
**Mathlib references**: `Mathlib/Topology/Support.lean` (`tsupport`, `HasCompactSupport`).

## Statement 133: Definition 6.22
**Status**: included
**Explanation**: Partitions of unity on manifolds are formalized.
**Mathlib references**: `Mathlib/Geometry/Manifold/PartitionOfUnity.lean`, `Mathlib/Topology/PartitionOfUnity.lean`.

## Statement 134: Definition 6.23
**Status**: included
**Explanation**: Subordinate partitions of unity are part of the partition of unity formalization.
**Mathlib references**: `Mathlib/Topology/PartitionOfUnity.lean` (`IsSubordinate`).

## Statement 135: Definition 6.24
**Status**: included
**Explanation**: Same as Definition 4.33. Orientation of a one-dimensional vector space.
**Mathlib references**: `Mathlib/LinearAlgebra/Orientation.lean`.

## Statement 136: Definition 6.25
**Status**: included
**Explanation**: Same as Definition 4.34. Orientation of an n-dimensional vector space.
**Mathlib references**: `Mathlib/LinearAlgebra/Orientation.lean` (`Orientation`).

## Statement 137: Definition 6.26
**Status**: included
**Explanation**: Orientation preserving linear maps.
**Mathlib references**: `Mathlib/LinearAlgebra/Orientation.lean`.

## Statement 138: Definition 6.27
**Status**: included
**Explanation**: Orientation of a manifold is partially formalized in Mathlib. The concept exists but the full smooth orientation theory is limited.
**Mathlib references**: `Mathlib/LinearAlgebra/Orientation.lean` (at the linear algebra level).

## Statement 139: Definition 6.28
**Status**: non-included
**Explanation**: The $\mathcal{C}^\infty$ orientation of a manifold (smooth orientation) is not fully formalized as a standalone concept in Mathlib's manifold library.
**Mathlib references**: None directly.

## Statement 140: Theorem 6.29
**Status**: non-included
**Explanation**: The existence of a global nowhere-vanishing n-form on an oriented manifold (volume form) is not formalized in this generality.
**Mathlib references**: None.

## Statement 141: Definition 6.30
**Status**: non-included
**Explanation**: Volume forms on manifolds are not formalized in this differential-geometric sense.
**Mathlib references**: None (Mathlib has measure-theoretic volume but not differential form volume).

## Statement 142: Definition 6.31
**Status**: included
**Explanation**: Orientation preserving diffeomorphisms between oriented manifolds. The concept is available at the linear algebra level.
**Mathlib references**: `Mathlib/LinearAlgebra/Orientation.lean`, `Mathlib/Geometry/Manifold/Diffeomorph.lean`.

## Statement 143: Definition 6.32
**Status**: non-included
**Explanation**: Oriented parameterizations of manifolds are not formalized.
**Mathlib references**: None.

## Statement 144: Definition 6.33
**Status**: non-included
**Explanation**: Integration of n-forms on manifolds using partitions of unity is not formalized. Mathlib uses measure-theoretic integration, not integration of differential forms.
**Mathlib references**: None in this form.

## Statement 145: Theorem 6.34
**Status**: non-included
**Explanation**: The Poincare Lemma for manifolds (equivalence of zero integral and exactness for compactly supported top-forms) is not formalized.
**Mathlib references**: None.

## Statement 146: Lemma 6.35 (Connectivity Lemma)
**Status**: non-included
**Explanation**: This connectivity lemma about chaining chart domains in a connected manifold is not formalized.
**Mathlib references**: None.

## Statement 147: Lemma 6.36
**Status**: non-included
**Explanation**: This technical lemma (the Poincare-type result within a single chart) is not formalized.
**Mathlib references**: None.

## Statement 148: Theorem 6.37
**Status**: non-included
**Explanation**: The degree theorem for proper maps between manifolds is not formalized.
**Mathlib references**: None.

## Statement 149: Theorem 6.38 (Change of Variables for Manifolds)
**Status**: non-included
**Explanation**: The change of variables theorem for integration of forms on manifolds is not formalized. While the measure-theoretic change of variables exists, the differential forms version does not.
**Mathlib references**: None in this form.

## Statement 150: Theorem 6.39 (Inverse Function Theorem for Manifolds)
**Status**: non-included
**Explanation**: While the IFT for Euclidean spaces is formalized, the specific manifold version (bijective tangent map implies local diffeomorphism between manifolds) is not directly available as a theorem in this form. The manifold library has `LocalDiffeomorph` but the specific IFT statement for abstract manifolds is not present.
**Mathlib references**: `Mathlib/Geometry/Manifold/LocalDiffeomorph.lean` (partial).

## Statement 151: Lemma 6.40
**Status**: non-included
**Explanation**: Finiteness of preimages at non-critical values for proper maps between manifolds is not formalized.
**Mathlib references**: None.

## Statement 152: Theorem 6.41
**Status**: non-included
**Explanation**: The degree formula for manifolds (degree as signed count of preimages) is not formalized.
**Mathlib references**: None.

## Statement 153: Theorem 6.42 (Volume Theorem / Sard for Manifolds)
**Status**: non-included
**Explanation**: Sard's theorem for manifolds is not formalized.
**Mathlib references**: None.

## Statement 154: Definition 6.43
**Status**: non-included
**Explanation**: Smooth domains (manifolds with boundary in the sense of half-space parameterizations) are partially available but not in this exact formulation. Mathlib has `ModelWithCorners` which handles boundaries.
**Mathlib references**: `Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean` (partial).

## Statement 155: Definition 6.44
**Status**: non-included
**Explanation**: Parameterizations of smooth domains are not formalized in this form.
**Mathlib references**: None.

## Statement 156: Definition 6.45
**Status**: non-included
**Explanation**: Oriented parameterizations of smooth domains are not formalized.
**Mathlib references**: None.

## Statement 157: Definition 6.46
**Status**: non-included
**Explanation**: Integration over smooth domains using partitions of unity is not formalized.
**Mathlib references**: None.

## Statement 158: Stokes' Theorem
**Status**: non-included
**Explanation**: Stokes' theorem ($\int_D d\omega = \int_{\mathrm{Bd}(D)} \omega$) in the differential forms sense is not formalized in Mathlib. There is a divergence theorem for box integrals (`Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean`), but the general Stokes' theorem for manifolds with boundary is not present.
**Mathlib references**: `Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean` (a special case only).

## Statement 159: Theorem 6.47
**Status**: non-included
**Explanation**: The theorem that a map from a boundary that extends to the interior has degree zero is not formalized.
**Mathlib references**: None.

## Statement 160: Corollary 9 (Brouwer Fixed Point Theorem)
**Status**: non-included
**Explanation**: The Brouwer fixed point theorem is not formalized in Mathlib. There is no `BrouwerFixedPoint` theorem in Mathlib.
**Mathlib references**: None.

## Statement 161: Hopf Theorem
**Status**: non-included
**Explanation**: The Hopf theorem (every smooth map $f: S^n \to \mathbb{R}^{n+1}$ for even n has an eigenvector) is not formalized in Mathlib.
**Mathlib references**: None.
