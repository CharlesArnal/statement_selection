# MIT Books → Mathlib Undergrad TODO: Candidate Analysis

## Overview

The [Mathlib undergrad TODO](https://leanprover-community.github.io/undergrad_todo.html) lists ~15 categories of missing undergraduate mathematics. Below is a ranking of MIT OCW books by how well they cover those gaps, based on the "not included" statements in each book's `detailed_assessment.md`.

---

## Tier 1: Strong Candidates (high overlap with undergrad TODO)

### 1. `algebra_i_student_notes` — Linear Algebra, Quadratic Forms, Euclidean Geometry
Covers **4 TODO categories** with concrete not-in-Mathlib statements:
- **Jordan normal form** (Theorems 32–33)
- **Sylvester's law of inertia** (Claim 88)
- **SO(n) / O(2,ℝ) / O(3,ℝ) classification** (Theorems 38, 43–46)
- **Isometry classification in ℝ²** (Theorems 39–41: decomposition f(x)=Ax+b, fixing-origin linearity, 4-type classification)
- **Finite subgroups of SO₂ are cyclic** (Theorem 43)
- **Discrete subgroups of ℝ²** (Theorem 47)

### 2. `algebra_ii_student_notes` — Representation & Character Theory
Covers **group theory / representation** TODO items:
- **Irreducible representations** of Sₙ (Propositions 1–2)
- **Character formula for regular representation** (Proposition 7)
- **Class functions and convolution** (Lemma 24, class-function equivariance lemma)
- **Orthonormal basis of irreducible characters** (related infrastructure)

### 3. `theory_of_probability` — Probability Theory
Covers nearly the entire **probability** section of the TODO:
- **Weak law of large numbers** (Statement 20)
- **Central limit theorem** (Statement 39)
- **Lévy's continuity theorem** (Statement 21)
- **Characteristic function inversion** (Statement 36)
- **Bochner's theorem** (Statement 37)
- **Lindeberg-Feller CLT** (Statement 40)
- **Berry-Esseen theorem** (Statement 41)
- **Poisson convergence** (Statement 43)

### 4. `fourier_analysis` — Fourier Analysis & Distribution Calculus
Covers **measures/integrals** and **distribution calculus** TODO items:
- **Fejér's theorem** (Theorem 1) — uniform convergence of Cesàro means
- **Density of trig polynomials in C(𝕋)** (Corollary 1)
- **Approximate identity lemma** for periodic functions
- **Young's inequality for convolution on 𝕋** (Proposition 1)
- **Uniqueness of Fourier series** (Corollary 1)
- **Fourier inversion** on L² and S'(ℝ) (multiple propositions)
- **Lévy continuity / weak convergence via Fourier transforms** (Proposition 2)
- **Central limit theorem** (Theorem 2 — independent derivation)
- **Weyl equidistribution theorem** (Theorem 2)

### 5. `complex_variables_with_applications` + `functions_of_a_complex_variable` — Complex Analysis
Together they cover most of the **complex analysis** TODO:
- **Residue theorem** (multiple formulations)
- **Argument principle** and **Rouché's theorem**
- **Winding numbers** of closed curves
- **Laurent series** and **isolated singularities**
- **Casorati-Weierstrass theorem**
- **Mittag-Leffler's theorem**
- **Montel's theorem**
- **Möbius transformation geometry** (circles → circles)
- **Poisson integral formula**
- Orthogonality of harmonic conjugate level curves

---

## Tier 2: Moderate Candidates (partial overlap)

### 6. `introduction_to_partial_differential_equations` — PDE / Distribution Calculus
20+ not-in-Mathlib statements matching the TODO:
- **Laplacian fundamental solutions** (Statements 21–22)
- **Heat/wave equation solutions** — d'Alembert, Kirchhoff (Statements 38–42)
- **Maximum principles** for harmonic functions (Statements 18–19)
- **Harnack's inequality** (Statement 28)
- **Poisson formula for the ball** (Statement 27)
- **PDE classification** (elliptic/hyperbolic/parabolic) (Statement 50)
- **Duhamel's principle** (Statement 14)

### 7. `measure_and_integration` — Measures & Integrals
Key missing items:
- **Young's inequality** for general exponents (Statement 67)
- **Hardy-Littlewood maximal inequality** (Statement 74)
- **Marcinkiewicz interpolation** (Statement 79)
- **Lebesgue criterion for Riemann integrability** (Statement 9)
- **Absolute continuity and FTOC** (Statement 72)
- Mollifier convergence in Lᵖ (Statement 71)

### 8. `real_analysis_18100a` / `real_analysis_18100c` — Real Analysis
Some relevant gaps despite high overall Mathlib coverage:
- **Weierstrass nowhere-differentiable function** (Statements 98–99)
- **Riemann-Stieltjes integral** theory (18100c, Statements 20.3–21.5)
- **Stone-Weierstrass lattice version** (18100c, Statement 18.4)
- **Uniform convergence of derivatives** theorem (18100b, Statement 76)

### 9. `topics_in_fourier_analysis` — Distribution Calculus (advanced)
- **Hermite functions** as orthogonal basis / Fourier eigenfunctions (Statements 12–15)
- **Riesz-Thorin interpolation** (Statement 44)
- **Bochner's theorem** (Statement 41)
- **Lévy-Khintchine representation** (Statements 29–30)

### 10. `introduction_to_functional_analysis` — Topology / Hilbert Spaces
- **Dirichlet problem** for Sturm-Liouville (Statements 129–135)
- **Green's functions** for boundary value problems
- Equivalent norms on finite-dim spaces already in Mathlib

---

## Tier 3: Low Overlap with Undergrad TODO

These books cover **graduate-level** or **applied** topics that mostly fall outside the undergrad TODO scope:

- `linear_partial_differential_equations` — numerical PDE (Lax equivalence, von Neumann stability)
- `differential_geometry` — Riemannian geometry (not on TODO)
- `geometry_and_topology_in_the_plane` — combinatorial geometry
- `introduction_to_numerical_methods` — numerical methods (DFT, Sherman-Morrison)
- `advanced_calculus_for_engineers` — applied/distribution theory
- All other books (algebraic geometry, number theory, combinatorics, etc.)

---

## Coverage Matrix

| Undergrad TODO Category | Best Book(s) | # Not-in-Mathlib Statements |
|---|---|---|
| **Linear Algebra** (Jordan, diagonalization, Gaussian elim) | `algebra_i_student_notes` | ~6 |
| **Group Theory** (SO(n), characters, representations) | `algebra_i_student_notes`, `algebra_ii_student_notes` | ~12 |
| **Ring Theory** (partial fractions) | `algebra_ii_student_notes` | ~2 |
| **Bilinear/Quadratic Forms** (Sylvester, polar decomp) | `algebra_i_student_notes` | ~3 |
| **Affine/Euclidean Geometry** (isometries, conics) | `algebra_i_student_notes` | ~6 |
| **Single Variable Real Analysis** (series, Taylor, improper integrals) | `real_analysis_18100a/b/c` | ~10 |
| **Complex Analysis** (residues, Laurent, winding numbers) | `complex_variables_with_applications`, `functions_of_a_complex_variable` | ~15 |
| **Topology** (norms, Hilbert spaces) | `introduction_to_functional_analysis` | ~7 |
| **Multivariable Calculus** (Jacobian, Lagrange, ODEs) | `introduction_to_partial_differential_equations` | ~10 |
| **Measures/Integrals** (convolution, Fejér, Dirichlet) | `measure_and_integration`, `fourier_analysis` | ~15 |
| **Probability** (CLT, LLN, char functions, distributions) | `theory_of_probability` | ~12 |
| **Distribution Calculus** (Fourier, Dirac, PDE weak solutions) | `fourier_analysis`, `topics_in_fourier_analysis` | ~15 |
| **Numerical Analysis** (LU, SVD, gradient descent, FFT) | `introduction_to_numerical_methods` | ~5 |

---

## Recommended Top 8 Books (ranked)

1. **`algebra_i_student_notes`** — broadest coverage: linear algebra, quadratic forms, Euclidean geometry, SO(n)
2. **`theory_of_probability`** — nearly complete coverage of the probability TODO section
3. **`fourier_analysis`** — Fejér, convolution, Fourier inversion, CLT, distributions
4. **`algebra_ii_student_notes`** — representation theory, character theory, class functions
5. **`complex_variables_with_applications`** — residue theorem, Laurent series, winding numbers
6. **`functions_of_a_complex_variable`** — complementary complex analysis (Mittag-Leffler, Montel, Rouché)
7. **`measure_and_integration`** — Young's inequality, Hardy-Littlewood, absolute continuity
8. **`introduction_to_partial_differential_equations`** — Laplacian, heat/wave equations, maximum principles
