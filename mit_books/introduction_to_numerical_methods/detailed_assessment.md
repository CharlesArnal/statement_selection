# Detailed Assessment of Mathematical Statements

Note: This textbook (MIT 18.335J, Introduction to Numerical Methods) is primarily a computational/algorithmic course. It does not contain formally named or labeled theorems, lemmas, propositions, or corollaries in the traditional mathematical textbook style. The statements below are mathematical facts referenced or used informally within the text. Many are well-known classical results from analysis, linear algebra, and number theory.

## Statement 1: Monotone Convergence Theorem for Sequences
A monotonic-decreasing sequence that is bounded below converges.

Assessment: included
This is the monotone convergence theorem for real sequences, a fundamental result in real analysis. In mathlib, this is formalized in `Mathlib/Topology/Order/MonotoneConvergence.lean`. The key result is `tendsto_atTop_ciSup`, which states that a monotone function with a bounded above range converges to the supremum: if `f` is monotone and `BddAbove (range f)`, then `Tendsto f atTop (nhds (iSup f))`. The dual version handles monotone-decreasing sequences bounded below. The file also contains `tendsto_atTop_atTop_of_monotone'` for the unbounded case. Additional related results appear in `Mathlib/Topology/Order/IsLUB.lean`.

## Statement 2: Equivalence of Norms on Finite-Dimensional Vector Spaces
If we are given two norms $\|\cdot\|_a$ and $\|\cdot\|_b$ on some finite-dimensional vector space $V$ over $\mathbb{C}$, there exists a pair of real numbers $0 < C_1 \le C_2$ such that, for all $x \in V$:
$$C_1 \|x\|_b \le \|x\|_a \le C_2 \|x\|_b.$$

Assessment: included
The equivalence of norms on finite-dimensional spaces is formalized in mathlib, though not as a single explicit inequality statement. Instead, it is established through the more general result that all Hausdorff topologies on a finite-dimensional vector space over a complete nontrivially normed field coincide. The key files are `Mathlib/Topology/Algebra/Module/FiniteDimension.lean` (which proves `unique_topology_of_t2` and that all linear maps on finite-dimensional T2 spaces are continuous, yielding topological equivalence of all norms) and `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` (which notes that "Over a complete nontrivially normed field, in finite dimension, all norms are equivalent" and provides consequences such as `LinearMap.continuous_of_finiteDimensional`). The norm equivalence follows from these results: any two norms induce the same topology, and hence are equivalent with finite constants.

## Statement 3: Extreme Value Theorem
A continuous function on a compact set must achieve a maximum and minimum value on the set.

Assessment: included
The extreme value theorem is formalized in mathlib at `Mathlib/Topology/Order/Compact.lean`. The file header states: "We prove the extreme value theorem (`IsCompact.exists_isMinOn`, `IsCompact.exists_isMaxOn`)." Specifically, `IsCompact.exists_isMinOn` proves that if `s` is compact, nonempty, and `f` is continuous on `s`, then `f` attains its minimum on `s`. Similarly, `IsCompact.exists_isMaxOn` proves the corresponding result for the maximum.

## Statement 4: Convex Optimization -- Local Optima are Global Optima
For a convex problem (convex objective and constraints), any local optimum must be a global optimum.

Assessment: included
This result is formalized in mathlib at `Mathlib/Analysis/Convex/Extrema.lean`. The file contains `IsLocalMinOn.isMinOn_of_convexOn`, which states: "A local minimum of a convex function is a global minimum, restricted to a set `s`." Specifically, if `f` is a convex function on a convex set `s` and `a` is a local minimum of `f` on `s`, then `a` is a global minimum of `f` on `s`. There is also a version for unconstrained local minima being global minima.

## Statement 5: Cauchy-Schwarz Inequality
For any inner product $\langle x, y \rangle$, it is always true that $\langle x, x \rangle \langle \delta, \delta \rangle \geq |\langle x, \delta \rangle|^2$.

Assessment: included
The Cauchy-Schwarz inequality is formalized in mathlib at `Mathlib/Analysis/InnerProductSpace/Defs.lean`. The key result is `norm_inner_le_norm`, which states `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖` for elements of an inner product space. This is the normed version of Cauchy-Schwarz (since `‖x‖^2 = ⟪x, x⟫` in a real inner product space, this is equivalent to the classical inequality). The internal proof uses `InnerProductSpace.Core.cauchy_schwarz_aux` from `Mathlib/Analysis/InnerProductSpace/Basic.lean`. Discrete versions for sums also appear in `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean` (the `inner_mul_le_norm_mul_sq` / Cauchy-Schwarz for finite sums).

## Statement 6: Hellmann-Feynman Theorem
For a real-symmetric matrix $A(\mathbf{p})$ with eigenvector $\mathbf{x}$ and eigenvalue $\alpha$, the derivative of the eigenvalue with respect to parameters is $\alpha_{\mathbf{p}} = \mathbf{x}^T A_p \mathbf{x}$.

Assessment: non-included
The Hellmann-Feynman theorem is a result from quantum mechanics / perturbation theory relating the derivative of an eigenvalue to the expectation value of the derivative of the operator. Searched mathlib for "Hellmann", "Feynman", "HellmanFeynman", "eigenvalue_deriv", and "perturbation" and found no formalization. Mathlib contains extensive eigenvalue theory (`Mathlib/LinearAlgebra/Eigenspace/`) but does not include perturbation theory or sensitivity analysis of eigenvalues with respect to matrix parameters.

## Statement 7: Abel's Theorem (Abel-Ruffini Theorem)
There is no general algebraic solution to polynomial equations of degree five or higher.

Assessment: included
The Abel-Ruffini theorem is formalized in mathlib at `Mathlib/FieldTheory/AbelRuffini.lean`. The file proves one direction: if an element is solvable by radicals, then its minimal polynomial has a solvable Galois group. The key result is `solvableByRad.isSolvable'`: an irreducible polynomial with a root that is solvable by radicals has a solvable Galois group. Since the symmetric group $S_5$ is not solvable, this implies no general radical solution exists for degree 5 or higher.

## Statement 8: Euler's Identity
$e^{i\phi} = \cos\phi + i\sin\phi$.

Assessment: included
Euler's formula is formalized in mathlib at `Mathlib/Analysis/Complex/Trigonometric.lean`. The key result is `cos_add_sin_I`, which states `cos x + sin x * I = exp (x * I)`, which is precisely Euler's formula $e^{ix} = \cos x + i\sin x$. Related results include `exp_mul_I` used throughout `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` for working with the unit circle in $\mathbb{C}$.

## Statement 9: Chinese Remainder Theorem
If $\gcd(N_1, N_2) = 1$, one can re-index using the Chinese Remainder Theorem.

Assessment: included
The Chinese Remainder Theorem is formalized in multiple places in mathlib. For natural numbers, it appears in `Mathlib/Data/Nat/ChineseRemainder.lean`. For rings and ideals, the general version is in `Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean`. For $\mathbb{Z}/n\mathbb{Z}$, relevant results are in `Mathlib/Data/ZMod/Basic.lean`. These formalizations cover the algebraic isomorphism underlying the re-indexing used in FFT prime-factor algorithms.

## Statement 10: Sherman-Morrison Formula
$(A + uv^T)^{-1} = A^{-1} - \frac{A^{-1}uv^TA^{-1}}{1 + v^TA^{-1}u}$.

Assessment: non-included
The Sherman-Morrison formula (and its generalization, the Woodbury matrix identity) gives a closed form for the inverse of a rank-1 perturbation of a matrix. Searched mathlib for "Sherman", "Morrison", "Woodbury", "rank_one_update", and "smul_update" and found no formalization. While mathlib has extensive linear algebra including matrix inverses and determinants, it does not contain these specific matrix perturbation identities.

## Statement 11: Backward Stability of Householder Hessenberg Reduction
The Householder Hessenberg reduction algorithm is backward stable: $\tilde{Q}\tilde{H}\tilde{Q}^* = A + \delta A$, where $\frac{\|\delta A\|}{\|A\|} = O(\epsilon_{\text{machine}})$.

Assessment: non-included
This is a numerical analysis result about the backward stability of a specific algorithm (Householder reduction to Hessenberg form). Searched mathlib for "Householder", "Hessenberg", "backward_stable", "QR", and "qr_factorization" and found no formalization. Mathlib does not contain numerical analysis results about floating-point arithmetic, rounding errors, or algorithmic stability. These are fundamentally computational results that do not fit the current scope of mathlib's pure mathematics formalization.

## Statement 12: DFT Inverse Formula
The DFT defined by $y_k = \sum_{n=0}^{N-1} x_n e^{-\frac{2\pi i}{N}nk}$ has inverse $x_n = \frac{1}{N} \sum_{k=0}^{N-1} y_k e^{+\frac{2\pi i}{N} nk}$.

Assessment: non-included
Mathlib contains continuous Fourier transform theory in `Mathlib/Analysis/Fourier/FourierTransform.lean`, but not the discrete Fourier transform (DFT). The DFT inverse formula is a finite-dimensional linear algebra identity involving roots of unity. Searched for "DFT", "discrete.*fourier", "FourierTransform" and found only continuous Fourier transforms and their applications to number theory (e.g., `Mathlib/NumberTheory/LSeries/ZMod.lean`). The discrete Fourier transform as a finite matrix operation and its inverse are not formalized in mathlib.

## Statement 13: Convolution Theorem
Cyclic convolution $c_n = \sum_{m=0}^{N-1} a_m b_{n-m}$ can be evaluated in $O(N \log N)$ time via: $c_n = \text{inverse FFT}(\text{FFT}(a_n) \cdot \text{FFT}(b_n))$.

Assessment: non-included
The convolution theorem states that pointwise multiplication in the frequency domain corresponds to convolution in the time domain (and vice versa). For the continuous case, mathlib has some convolution theory in `Mathlib/Analysis/Fourier/FourierTransform.lean`, but the discrete cyclic convolution theorem (relating DFT, pointwise multiplication, and inverse DFT) is not formalized. Moreover, the computational complexity claim ($O(N \log N)$) is an algorithmic result outside the scope of mathlib's mathematical formalization.
