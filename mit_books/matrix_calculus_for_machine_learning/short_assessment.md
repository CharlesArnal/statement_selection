# Short Assessment: Statements vs. Mathlib (v4.27.0)

## Source: Matrix Calculus (for Machine Learning and Beyond)
### MIT 18.S096 (IAP 2023)

---

## Note on the Textbook

This textbook is primarily expository course notes. It contains 7 formally labeled statements (Theorems, Propositions) and several substantive Definitions. Most mathematical content is presented informally through examples and derivations. Below we assess each formally labeled theorem/proposition, the Kronecker product identities from Problem 26, and the key informal claims.

---

## Formally Labeled Theorems and Propositions

### Statement 1: Theorem 2 (Differential Product Rule)
$d(AB) = (dA)B + A(dB)$

**Assessment: INCLUDED in mathlib.**
Mathlib has the Frechet derivative product rule for bilinear maps (`ContinuousLinearMap.HasFDerivAt.of_bilinear` in `Analysis/Calculus/FDeriv/Bilinear.lean`) and for multiplication (`HasFDerivAt.mul` in `Analysis/Calculus/FDeriv/Mul.lean`), which subsume this result.

---

### Statement 2: Proposition 27 (Key Kronecker-Product Identity)
$(A \otimes B) \operatorname{vec}(C) = \operatorname{vec}(BCA^T)$

**Assessment: NOT INCLUDED in mathlib.**
Mathlib has extensive Kronecker product support in `LinearAlgebra/Matrix/Kronecker.lean` (definition, transpose, mixed-product property, determinant, trace), but does not formalize the vectorization operation `vec` or this specific Kronecker-vec identity.

---

### Statement 3: Problem 26 -- Kronecker Product Properties

**3a.** $(A \otimes B)^T = A^T \otimes B^T$
**Assessment: INCLUDED.** `Matrix.kroneckerMap_transpose` in `LinearAlgebra/Matrix/Kronecker.lean`.

**3b.** $(A \otimes B)(C \otimes D) = (AC) \otimes (BD)$
**Assessment: INCLUDED.** `Matrix.mul_kronecker_mul` in `LinearAlgebra/Matrix/Kronecker.lean`.

**3c.** $(A \otimes B)^{-1} = A^{-1} \otimes B^{-1}$
**Assessment: NOT INCLUDED.** Not formalized in mathlib's Kronecker product file.

**3d.** $A \otimes B$ is orthogonal if A and B are orthogonal.
**Assessment: NOT INCLUDED.** Not directly formalized.

**3e.** $\det(A \otimes B) = \det(A)^m \det(B)^n$
**Assessment: INCLUDED.** `Matrix.det_kronecker` in `LinearAlgebra/Matrix/Kronecker.lean`.

**3f.** $\operatorname{tr}(A \otimes B) = (\operatorname{tr} A)(\operatorname{tr} B)$
**Assessment: INCLUDED.** `Matrix.trace_kronecker` in `LinearAlgebra/Matrix/Kronecker.lean`.

**3g.** Eigenvalues of $A \otimes B$ are products of eigenvalues of A and B.
**Assessment: NOT INCLUDED.** No formalization of eigenvalue properties of Kronecker products in mathlib.

---

### Statement 4: Theorem 39 (Derivative of the Determinant)
$\nabla(\det A) = \operatorname{cofactor}(A)$, $d(\det A) = \operatorname{tr}(\operatorname{adj}(A)dA)$

**Assessment: PARTIALLY INCLUDED.**
- The algebraic identity `adjugate A * A = det A . 1` is in mathlib (`Matrix.adjugate_mul`, `Matrix.mul_adjugate` in `LinearAlgebra/Matrix/Adjugate.lean`).
- The Frechet derivative of the determinant is NOT formalized in mathlib. There is no `hasFDerivAt_det` or similar theorem.
- The cofactor expansion for det is present (`Matrix.det_eq_sum_mul_adjugate_row`).

---

### Statement 5: Derivative of the Matrix Inverse
$d(A^{-1}) = -A^{-1} dA A^{-1}$

**Assessment: INCLUDED in mathlib.**
`hasFDerivAt_ring_inverse` and `fderiv_inverse` in `Analysis/Calculus/FDeriv/Mul.lean` express the Frechet derivative of the ring inverse as $-\text{mulLeftRight}(x^{-1}, x^{-1})$, which is exactly $h \mapsto -x^{-1} h x^{-1}$.

---

### Statement 6: Theorem 60 (Gradient on the Unit Sphere)
The gradient on the sphere is the ambient gradient projected by $(I - xx^T)$.

**Assessment: NOT INCLUDED in mathlib.**
Mathlib has general manifold/tangent space machinery but not this specific formula for gradients on the sphere.

---

### Statement 7: Theorem 62 ($Q^T dQ$ is Anti-symmetric for Orthogonal Q)
**Assessment: PARTIALLY INCLUDED.**
- Mathlib defines orthogonal groups (`LinearAlgebra/UnitaryGroup.lean`) and has the constraint $Q^T Q = I$.
- The Lie algebra characterization (tangent space at identity is skew-symmetric matrices) is present in `Algebra/Lie/SkewAdjoint.lean`.
- The specific differential statement is not directly present in this form.

---

## Informal Claims

### Chain Rule: $f'(x) = g'(h(x))h'(x)$
**Assessment: INCLUDED.** `HasFDerivAt.comp` in `Analysis/Calculus/FDeriv/Comp.lean`.

### Symmetry of Second Derivatives: $f''[dx', dx] = f''[dx, dx']$
**Assessment: INCLUDED.** `second_derivative_symmetric` in `Analysis/Calculus/FDeriv/Symmetric.lean`.

### Quadratic Approximation (Taylor's theorem to second order)
**Assessment: INCLUDED.** Taylor's theorem results in `Analysis/Calculus/Taylor.lean`.

### Euler-Lagrange Equations
**Assessment: NOT INCLUDED.** Mathlib does not formalize the Euler-Lagrange equations or the calculus of variations.

### Eigenvalue Perturbation (Hellmann-Feynman)
**Assessment: NOT INCLUDED.** No formalization of eigenvalue perturbation theory in mathlib.

---

## Summary Table

| # | Statement | Included in Mathlib? |
|---|-----------|---------------------|
| 1 | Differential Product Rule | Yes |
| 2 | Kronecker-vec identity | No |
| 3a | $(A \otimes B)^T = A^T \otimes B^T$ | Yes |
| 3b | $(A \otimes B)(C \otimes D) = (AC) \otimes (BD)$ | Yes |
| 3c | $(A \otimes B)^{-1} = A^{-1} \otimes B^{-1}$ | No |
| 3d | Orthogonality of Kronecker product | No |
| 3e | $\det(A \otimes B)$ formula | Yes |
| 3f | $\operatorname{tr}(A \otimes B)$ formula | Yes |
| 3g | Eigenvalues of Kronecker product | No |
| 4 | Derivative of determinant | Partially (algebraic identity yes, Frechet derivative no) |
| 5 | Derivative of matrix inverse | Yes |
| 6 | Gradient on unit sphere | No |
| 7 | $Q^T dQ$ anti-symmetric | Partially |
| - | Chain Rule | Yes |
| - | Symmetry of second derivatives | Yes |
| - | Quadratic approximation | Yes |
| - | Euler-Lagrange equations | No |
| - | Eigenvalue perturbation | No |
