# Detailed Assessment: Statements vs. Mathlib (v4.27.0)

## Source: Matrix Calculus (for Machine Learning and Beyond)
### Lecturers: Alan Edelman and Steven G. Johnson, MIT 18.S096 (IAP 2023)

---

## Textbook Character

This textbook consists of course notes for an applied mathematics class on matrix calculus. It is primarily expository, emphasizing intuition, computation, and applications (machine learning, optimization, automatic differentiation, ODE sensitivity analysis) over formal theorem-proof structure. The text contains 7 formally labeled theorems/propositions and numerous definitions. Most mathematical results are presented informally through worked examples and derivations rather than as formal theorem statements. The chapters on automatic differentiation (Ch. 8), ODE sensitivity (Ch. 9), stochastic derivatives (Ch. 11), and much of the optimization material (Ch. 6) contain no formal theorems at all, being entirely algorithmic/computational in nature.

---

## Detailed Statement-by-Statement Assessment

---

### Statement 1: Theorem 2 (Differential Product Rule)

**Full text:** Let A, B be two matrices. Then, $d(AB) = (dA)B + A(dB)$.

**Assessment: INCLUDED in mathlib**

**Mathlib evidence:**
The Frechet derivative of a bilinear map is formalized in `Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean`. Specifically, `ContinuousLinearMap.HasFDerivAt.of_bilinear` states that if `B` is a continuous bilinear map and `f`, `g` are differentiable functions, then the derivative of `y -> B(f(y), g(y))` is `B.precompR (f x) g' + B.precompL f' (g x)`. Applied to matrix multiplication (which is a continuous bilinear map), this yields exactly the product rule $d(AB) = (dA)B + A(dB)$.

Additionally, `HasFDerivAt.mul` in `Mathlib/Analysis/Calculus/FDeriv/Mul.lean` gives the product rule for multiplication in a normed algebra, which covers the matrix case.

The key mathlib declarations:
- `ContinuousLinearMap.HasFDerivAt.of_bilinear` (Bilinear.lean, line ~121)
- `HasFDerivAt.mul` (Mul.lean, line ~205)

---

### Statement 2: Proposition 27 (Key Kronecker-Product Identity)

**Full text:** Given (compatibly sized) matrices A, B, C, we have $(A \otimes B) \operatorname{vec}(C) = \operatorname{vec}(BCA^T)$.

**Assessment: NOT INCLUDED in mathlib**

**Mathlib evidence:**
Mathlib has extensive Kronecker product support in `Mathlib/LinearAlgebra/Matrix/Kronecker.lean`, including the definition of `kroneckerMap`, the mixed-product property (`mul_kronecker_mul`), transpose (`kroneckerMap_transpose`), determinant (`det_kronecker`), and trace (`trace_kronecker`).

However, the vectorization operation `vec` (stacking columns of a matrix into a column vector) is not formalized anywhere in mathlib. Without vectorization, this identity cannot be stated. While the isomorphism between `Matrix m n R` and `(m x n -> R)` exists implicitly via the function representation of matrices, the specific column-stacking operation and this Kronecker-vec identity are not present.

The closest related result is `mul_kronecker_mul`: $(A * B) \otimes_k (A' * B') = (A \otimes_k A') * (B \otimes_k B')$, which is the mixed-product property but operates in the Kronecker product space rather than relating Kronecker products to vectorized matrix operations.

---

### Statement 3: Problem 26 -- Kronecker Product Properties

These are stated as exercises but contain concrete mathematical identities.

#### 3a. $(A \otimes B)^T = A^T \otimes B^T$

**Assessment: INCLUDED in mathlib**

**Mathlib evidence:** `Matrix.kroneckerMap_transpose` in `Mathlib/LinearAlgebra/Matrix/Kronecker.lean` (line 68):
```
theorem kroneckerMap_transpose (f : a -> b -> g) (A : Matrix l m a) (B : Matrix n p b) :
    kroneckerMap f A^T B^T = (kroneckerMap f A B)^T
```
This is stated for the general `kroneckerMap`, which specializes to the Kronecker product when `f = (*)`.

#### 3b. $(A \otimes B)(C \otimes D) = (AC) \otimes (BD)$

**Assessment: INCLUDED in mathlib**

**Mathlib evidence:** `Matrix.mul_kronecker_mul` in `Mathlib/LinearAlgebra/Matrix/Kronecker.lean` (line 367):
```
theorem mul_kronecker_mul [Fintype m] [Fintype m'] [CommSemiring a]
    (A : Matrix l m a) (B : Matrix m n a) (A' : Matrix l' m' a) (B' : Matrix m' n' a) :
    (A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B'
```
Note: mathlib requires commutativity of the base ring, while the textbook states it without this restriction. The identity does hold for commutative rings; for non-commutative rings, a more careful statement is needed.

#### 3c. $(A \otimes B)^{-1} = A^{-1} \otimes B^{-1}$

**Assessment: NOT INCLUDED in mathlib**

**Mathlib evidence:** The Kronecker product file does not contain any results about inverses of Kronecker products. A search for "inv" patterns in `Kronecker.lean` yields no matches. This could be derived from `mul_kronecker_mul` combined with `kronecker_one`, but the explicit statement is absent.

#### 3d. $A \otimes B$ is orthogonal if A and B are orthogonal.

**Assessment: NOT INCLUDED in mathlib**

**Mathlib evidence:** This follows from 3a and 3b (and the fact that $1 \otimes 1 = 1$), but is not stated explicitly. Mathlib's orthogonal group (`LinearAlgebra/UnitaryGroup.lean`) does not discuss Kronecker products.

#### 3e. $\det(A \otimes B) = \det(A)^m \det(B)^n$

**Assessment: INCLUDED in mathlib**

**Mathlib evidence:** `Matrix.det_kronecker` in `Mathlib/LinearAlgebra/Matrix/Kronecker.lean` (line 387):
```
theorem det_kronecker [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : Matrix m m R) (B : Matrix n n R) :
    det (A ⊗ₖ B) = det A ^ Fintype.card n * det B ^ Fintype.card m
```
This matches the textbook's statement exactly (with $m$ = card of the index type of B, $n$ = card of the index type of A).

#### 3f. $\operatorname{tr}(A \otimes B) = (\operatorname{tr} A)(\operatorname{tr} B)$

**Assessment: INCLUDED in mathlib**

**Mathlib evidence:** `Matrix.trace_kronecker` in `Mathlib/LinearAlgebra/Matrix/Kronecker.lean` (line 383):
```
theorem trace_kronecker [Fintype m] [Fintype n] [Semiring a]
    (A : Matrix m m a) (B : Matrix n n a) :
    trace (A ⊗ₖ B) = trace A * trace B
```

#### 3g. Eigenvalues of $A \otimes B$ are products of eigenvalues of A and B.

**Assessment: NOT INCLUDED in mathlib**

**Mathlib evidence:** Mathlib does not have a comprehensive eigenvalue theory for finite-dimensional matrices in the linear algebra sense needed here. While there are definitions of eigenvalues and eigenvectors (`LinearAlgebra/Eigenspace/Basic.lean`), the specific statement about eigenvalues of Kronecker products is not formalized. This would require establishing that if $Au = \lambda u$ and $Bv = \mu v$, then $(A \otimes B)(u \otimes v) = \lambda\mu (u \otimes v)$, where $u \otimes v$ is interpreted appropriately.

---

### Statement 4: Theorem 39 (Derivative of the Determinant)

**Full text:**
$\nabla(\det A) = \operatorname{cofactor}(A) = (\det A)A^{-T}$, and
$d(\det A) = \operatorname{tr}(\det(A)A^{-1}dA) = \operatorname{tr}(\operatorname{adj}(A)dA)$.

**Assessment: PARTIALLY INCLUDED in mathlib**

**Mathlib evidence:**

*What IS in mathlib:*
- The adjugate matrix and its key algebraic properties are thoroughly formalized in `Mathlib/LinearAlgebra/Matrix/Adjugate.lean`:
  - `Matrix.adjugate_mul`: $\operatorname{adj}(A) \cdot A = \det(A) \cdot I$
  - `Matrix.mul_adjugate`: $A \cdot \operatorname{adj}(A) = \det(A) \cdot I$
  - `Matrix.det_adjugate`: $\det(\operatorname{adj}(A)) = \det(A)^{n-1}$
  - `Matrix.det_eq_sum_mul_adjugate_row`: cofactor expansion of the determinant
- The relationship $\operatorname{adj}(A) = \det(A) \cdot A^{-1}$ is implicit from `mul_adjugate` combined with `nonsing_inv` properties.

*What is NOT in mathlib:*
- The Frechet derivative of the determinant function. There is no `hasFDerivAt_det` or `fderiv_det` theorem. The calculus-level statement that $d(\det A) = \operatorname{tr}(\operatorname{adj}(A) dA)$ as a Frechet derivative is not formalized.
- While the algebraic identity connecting det, adjugate, and cofactors is present, the analytic/calculus formulation (gradient of det) is missing.

This is a significant gap: the algebraic ingredients are all there, but the synthesis into a calculus statement about the Frechet derivative of the determinant map has not been done.

---

### Statement 5: Derivative of the Matrix Inverse

**Full text:** $d(A^{-1}) = -A^{-1} dA A^{-1}$

**Assessment: INCLUDED in mathlib**

**Mathlib evidence:**
In `Mathlib/Analysis/Calculus/FDeriv/Mul.lean` (lines 645-670):

```
HasFDerivAt Ring.inverse (-mulLeftRight K R x_inv x_inv) x
```

and

```
theorem fderiv_inverse (x : R_units) :
    fderiv K (@Ring.inverse R _) x = -mulLeftRight K R x_inv x_inv
```

Here `mulLeftRight K R a b` is the continuous linear map $h \mapsto a \cdot h \cdot b$. So `fderiv_inverse` states that the Frechet derivative of the ring inverse at a unit $x$ is $h \mapsto -x^{-1} h x^{-1}$, which is exactly the textbook's formula $d(A^{-1}) = -A^{-1} dA A^{-1}$.

This is stated for general normed rings (which include matrix algebras), so the matrix case is a special instance.

---

### Statement 6: Theorem 60 (Gradient on the Unit Sphere)

**Full text:** Given $f: \mathbb{S}^n \to \mathbb{R}$, the gradient of f on the sphere is obtained by projecting the ambient gradient onto the tangent space: $\nabla_{\mathbb{S}^n} f = (I - xx^T)\nabla f$.

**Assessment: NOT INCLUDED in mathlib**

**Mathlib evidence:**
Mathlib has extensive machinery for:
- Spheres and their topology (`Topology/MetricSpace/Sphere.lean`)
- Smooth manifold structure on spheres (`Geometry/Manifold/Instances/Sphere.lean`)
- General tangent vectors and derivatives on manifolds (`Geometry/Manifold/MFDeriv/`)

However, the specific formula for the Riemannian gradient on the sphere as a projection of the ambient Euclidean gradient is not present. Mathlib's manifold library works with abstract charts and tangent bundles rather than with explicit projection formulas in ambient Euclidean space. The projection operator $(I - xx^T)$ for the sphere is not formalized as a gradient computation tool.

---

### Statement 7: Theorem 62 ($Q^T dQ$ is Anti-symmetric for Orthogonal Q)

**Full text:** Given Q is an orthogonal matrix, $Q^T dQ$ is anti-symmetric. Proof: $Q^TQ = I$ implies $Q^T dQ + (Q^T dQ)^T = 0$.

**Assessment: PARTIALLY INCLUDED in mathlib**

**Mathlib evidence:**
- The orthogonal/unitary group is defined in `Mathlib/LinearAlgebra/UnitaryGroup.lean` with the constraint $Q^* Q = 1$.
- The Lie algebra of the unitary group (skew-adjoint operators) is characterized in `Mathlib/Algebra/Lie/SkewAdjoint.lean`, which establishes that the tangent space at the identity of the unitary group consists of skew-adjoint operators. This is the infinitesimal version of the same statement.
- However, the specific differential-form statement "if $Q^TQ = I$ then $Q^T dQ + dQ^T Q = 0$" is not stated as a theorem in this explicit form. The Lie algebra characterization captures the same mathematical content at the level of the Lie algebra, but the differential notation used in the textbook is not present.

---

## Informal Claims Assessment

### Chain Rule: $f'(x) = g'(h(x)) \circ h'(x)$

**Assessment: INCLUDED in mathlib**

**Mathlib evidence:** `HasFDerivAt.comp` in `Mathlib/Analysis/Calculus/FDeriv/Comp.lean` (line 100):
```
theorem HasFDerivAt.comp {g : F -> G} {g' : F ->L[K] G}
    (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (g . f) (g'.comp f') x
```
This is exactly the chain rule: the Frechet derivative of a composition is the composition of the Frechet derivatives.

---

### Symmetry of Second Derivatives: $f''[dx', dx] = f''[dx, dx']$

**Assessment: INCLUDED in mathlib**

**Mathlib evidence:** `second_derivative_symmetric` in `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean` (line ~493):
```
theorem second_derivative_symmetric [IsRCLikeNormedField K]
    {f : E -> F} {f' : E -> E ->L[K] F} {f'' : E ->L[K] E ->L[K] F}
    (hf : Differentiable K f') (hf'' : HasFDerivAt f' f'' x) (v w : E) :
    f'' v w = f'' w v
```
This confirms that the second Frechet derivative is symmetric as a bilinear map, matching the textbook's claim.

---

### Quadratic Approximation / Taylor's Theorem to Second Order

**Assessment: INCLUDED in mathlib**

**Mathlib evidence:** Taylor's theorem and related results are in `Mathlib/Analysis/Calculus/Taylor.lean`. The second-order Taylor expansion $f(x + h) = f(x) + f'(x)[h] + \frac{1}{2}f''(x)[h,h] + o(\|h\|^2)$ is captured by the general Taylor remainder estimates.

---

### Euler-Lagrange Equations

**Assessment: NOT INCLUDED in mathlib**

**Mathlib evidence:** A thorough search for "EulerLagrange", "euler_lagrange", "calculus of variations", and related terms yields no results in mathlib. The calculus of variations is not formalized. This is a significant area of classical analysis that remains outside mathlib's scope as of v4.27.0.

---

### Eigenvalue Perturbation Theory (Hellmann-Feynman Theorem)

**Assessment: NOT INCLUDED in mathlib**

**Mathlib evidence:** The statement $d\lambda_i = q_i^T dS q_i$ for eigenvalues of a symmetric matrix $S = Q\Lambda Q^T$ under perturbation $dS$ is not in mathlib. While mathlib has eigenvalue/eigenvector definitions (`LinearAlgebra/Eigenspace/`), perturbation theory for eigenvalues is not formalized. The second-order perturbation formula $\lambda_i(\epsilon) = \lambda_i + \epsilon E_{ii} + \epsilon^2 \sum_{k \neq i} E_{ik}^2/(\lambda_i - \lambda_k) + \ldots$ is likewise absent.

---

## Summary

**Total formally labeled statements:** 7 (Theorems 2, 39, 60, 62; Proposition 27; Problem 26 with 7 sub-identities; derivative of inverse from Section 7.3)

**Breakdown (counting Problem 26 sub-identities individually):**
- **Fully included in mathlib:** 8 (Theorem 2, Problem 26 parts a/b/e/f, derivative of inverse, chain rule, symmetry of second derivatives)
- **Partially included:** 2 (Theorem 39 -- algebraic but not analytic part; Theorem 62 -- Lie algebra but not differential form)
- **Not included:** 7 (Proposition 27, Problem 26 parts c/d/g, Theorem 60, Euler-Lagrange, eigenvalue perturbation)

The textbook's content is heavily computational and algorithmic (automatic differentiation, finite differences, ODE sensitivity analysis, stochastic derivatives). These topics are fundamentally about numerical methods and computer science rather than pure mathematics, and are entirely outside the scope of a formal mathematics library like mathlib.
