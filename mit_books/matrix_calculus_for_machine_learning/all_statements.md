# All Formal Mathematical Statements

## Source: Matrix Calculus (for Machine Learning and Beyond)
### Lecturers: Alan Edelman and Steven G. Johnson, MIT 18.S096 (IAP 2023)

---

## Overview

This textbook is primarily expository, functioning as course notes for an applied mathematics course. It contains relatively few formally labeled theorems, lemmas, propositions, or corollaries compared to a pure mathematics textbook. Most mathematical content is presented as definitions, examples, remarks, and problems. The statements below are every instance of a formally labeled Theorem, Proposition, Definition (with substantive mathematical content), or similar formal marker found in the text.

---

## Formally Labeled Statements

### Statement 1: Theorem 2 (Differential Product Rule)
**Type:** Theorem
**Location:** Section 1.3

**Full text:**
Let A, B be two matrices. Then, we have the differential product rule for AB:
$$d(AB) = (dA)B + A(dB).$$

---

### Statement 2: Proposition 27 (Key Kronecker-Product Identity)
**Type:** Proposition
**Location:** Section 3.3.1

**Full text:**
Given (compatibly sized) matrices A, B, C, we have
$$(A \otimes B) \operatorname{vec}(C) = \operatorname{vec}(BCA^T).$$

---

### Statement 3: Problem 26 -- Kronecker Product Properties (stated as identities to derive)
**Type:** Problem (contains formal mathematical identities)
**Location:** Section 3.3

**Full text (identities):**
From the definition of the Kronecker product, derive the following identities:
1. $(A \otimes B)^T = A^T \otimes B^T$.
2. $(A \otimes B)(C \otimes D) = (AC) \otimes (BD)$.
3. $(A \otimes B)^{-1} = A^{-1} \otimes B^{-1}$.
4. $A \otimes B$ is orthogonal if A and B are orthogonal.
5. $\det(A \otimes B) = \det(A)^m \det(B)^n$, where $A \in \mathbb{R}^{n,n}$ and $B \in \mathbb{R}^{m,m}$.
6. $\operatorname{tr}(A \otimes B) = (\operatorname{tr} A)(\operatorname{tr} B)$.
7. Given eigenvectors/values $Au = \lambda u$ and $Bv = \mu v$, then $\lambda \mu$ is an eigenvalue of $A \otimes B$ with eigenvector $u \otimes v$.

---

### Statement 4: Theorem 39 (Derivative of the Determinant)
**Type:** Theorem
**Location:** Section 7.1

**Full text:**
Given A is a square matrix, we have
$$\nabla(\det A) = \operatorname{cofactor}(A) = (\det A)A^{-T} := \operatorname{adj}(A^T) = \operatorname{adj}(A)^T$$
where adj is the "adjugate". Furthermore,
$$d(\det A) = \operatorname{tr}(\det(A)A^{-1}dA) = \operatorname{tr}(\operatorname{adj}(A)dA) = \operatorname{tr}(\operatorname{cofactor}(A)^T dA).$$

---

### Statement 5: Derivative of the Matrix Inverse (from Section 7.3)
**Type:** Derived result (presented as a boxed formula)
**Location:** Section 7.3

**Full text:**
From the property $A^{-1}A = I$, by the product rule:
$$d(A^{-1}A) = d(I) = 0 = d(A^{-1})A + A^{-1}dA$$
$$\implies d(A^{-1}) = (A^{-1})'[dA] = -A^{-1} dA A^{-1}.$$
In Kronecker-product notation:
$$\operatorname{vec}(d(A^{-1})) = -(A^{-T} \otimes A^{-1}) \operatorname{vec}(dA).$$

---

### Statement 6: Theorem 60 (Gradient on the Unit Sphere)
**Type:** Theorem
**Location:** Section 13.1

**Full text:**
Given $f: \mathbb{S}^n \to \mathbb{R}$, we have
$$df = g(x)^T dx = ((I - xx^T)g(x))^T dx.$$
That is, the gradient of f on the sphere is obtained by projecting the ambient gradient g(x) onto the tangent space via $(I - xx^T)$.

---

### Statement 7: Theorem 62 (Differential of Orthogonal Matrices is Anti-symmetric)
**Type:** Theorem (with proof)
**Location:** Section 13.2

**Full text:**
Given Q is an orthogonal matrix, we have that $Q^T dQ$ is anti-symmetric.

*Proof.* The constraint of being orthogonal implies that $Q^T Q = I$. Differentiating this equation, we obtain
$$Q^T dQ + dQ^T Q = 0 \implies Q^T dQ = -(Q^T dQ)^T.$$
This is precisely the definition of being anti-symmetric.

---

## Additional Substantive Definitions

### Definition 22 (Vectorization)
**Location:** Section 3.2

The vectorization $\operatorname{vec} A \in \mathbb{R}^{mn}$ of any $m \times n$ matrix $A$ is defined by stacking the columns of A, from left to right, into a column vector.

---

### Definition 25 (Kronecker Product)
**Location:** Section 3.3

If A is an $m \times n$ matrix and B is a $p \times q$ matrix, then their Kronecker product $A \otimes B$ is the $mp \times nq$ matrix formed by replacing each entry $a_{ij}$ of A with the block $a_{ij}B$.

---

### Definition 30 (Frobenius Norm)
**Location:** Section 4.3

$$\|A\| := \sqrt{\sum_{i,j} |A_{ij}|^2} = \sqrt{\operatorname{tr}(A^T A)}.$$

---

### Definition 31 (Hilbert Space)
**Location:** Section 5.1

A (complete) vector space with an inner product is called a Hilbert space.

---

### Definition 34 (Frobenius Inner Product)
**Location:** Section 5.1

The Frobenius inner product of two $m \times n$ matrices A and B is:
$$\langle A, B \rangle_F = \sum_{ij} A_{ij} B_{ij} = \operatorname{vec}(A)^T \operatorname{vec}(B) = \operatorname{tr}(A^T B).$$

---

### Definition 37 (Banach Space)
**Location:** Section 5.2

A (complete) vector space with a norm is called a Banach space.

---

### Definition 56 (Bilinear Map)
**Location:** Section 12.2

Let U, V, W be vector spaces. A bilinear map is a function $B: U \times V \to W$ such that:
$$B[u, \alpha v_1 + \beta v_2] = \alpha B[u, v_1] + \beta B[u, v_2]$$
$$B[\alpha u_1 + \beta u_2, v] = \alpha B[u_1, v] + \beta B[u_2, v]$$

---

### Definition 61 (Anti-symmetric Matrix)
**Location:** Section 13.2

A matrix M is anti-symmetric if $M = -M^T$.

---

## Informal Mathematical Claims Functioning as Theorems

The following are important mathematical claims stated in the text without formal "Theorem" labels but which have substantive mathematical content:

1. **Chain Rule for Linear Operators** (Section 2.5): $f'(x) = g'(h(x))h'(x)$ for $f = g \circ h$.
2. **Symmetry of Second Derivatives** (Section 12.2): $f''(x)[dx', dx] = f''(x)[dx, dx']$ -- the second derivative is a symmetric bilinear map.
3. **Quadratic Approximation** (Section 12.3): $f(x + \delta x) = f(x) + f'(x)[\delta x] + \frac{1}{2}f''(x)[\delta x, \delta x] + o(\|\delta x\|^2)$.
4. **Euler-Lagrange Equations** (Section 10.4): For $f(u) = \int_a^b F(u, u', x) dx$ with fixed endpoints, $\nabla f = \frac{\partial F}{\partial u} - \left(\frac{\partial F}{\partial u'}\right)' = 0$ at extremum.
5. **Eigenvalue Perturbation / Hellmann-Feynman** (Section 13.2.1): For $S = Q\Lambda Q^T$ symmetric, $d\lambda_i = q_i^T dS q_i$.
