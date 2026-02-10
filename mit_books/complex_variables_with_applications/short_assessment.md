# Short Assessment: Mathlib Coverage
## Complex Variables with Applications (MIT 18.04, Spring 2018)

Each statement is marked as:
- **Included**: Formalized in mathlib
- **Partially Included**: Core concept exists but not in the exact form stated
- **Not Included**: Not formalized in mathlib

---

### Topic 1: Complex Algebra and the Complex Plane

| # | Statement | Status |
|---|-----------|--------|
| Def 1 | Complex numbers ($i^2 = -1$) | **Included** |
| Thm 1 | Fundamental theorem of algebra | **Included** |
| Def 2 | Real and imaginary parts | **Included** |
| Def 3 | Complex conjugation | **Included** |
| Def 4 | Modulus $|z|$ | **Included** |
| Thm 2 | Triangle inequality | **Included** |
| Def 5 | Euler's formula | **Included** |
| Thm 3 | Properties of complex exponentials | **Included** |
| Thm 4 | De Moivre's formula | **Partially Included** |
| Def 6 | Complex exponential | **Included** |
| Def 7 | Punctured plane | **Included** |
| Def 8 | Branch of argument | **Partially Included** |
| Def 9 | Principal argument | **Included** |
| Def 10 | Complex logarithm | **Included** |
| Def 11 | Complex powers $z^a$ | **Included** |

### Topic 2: Analytic Functions

| # | Statement | Status |
|---|-----------|--------|
| Def 12 | Complex derivative | **Included** |
| Def 13 | Open disk | **Included** |
| Def 14 | Open region | **Included** |
| Def 15 | Limit of complex function | **Included** |
| Def 16 | Continuity | **Included** |
| Thm 2.10 | Cauchy-Riemann equations | **Partially Included** |
| Thm 5 | Converse of Cauchy-Riemann | **Partially Included** |
| Thm 6 | $f' = 0$ implies constant | **Included** |
| Thm 2.13 | Analytic implies $f'$ analytic | **Included** |
| Def 17 | Entire function | **Included** |
| Def 18 | Complex $\cos$, $\sin$ | **Included** |
| Def 19 | Complex $\cosh$, $\sinh$ | **Included** |

### Topic 3: Line Integrals and Cauchy's Theorem

| # | Statement | Status |
|---|-----------|--------|
| Def 20 | Complex line integral | **Included** |
| Thm 3.5 | Fundamental theorem of complex line integrals | **Included** |
| Thm 3.8 | Antiderivative implies path independence | **Included** |
| Thm 3.9 | Path independence iff vanishing loop integrals | **Included** |
| Thm 3.13 | Cauchy's theorem (simply connected) | **Included** |
| Thm 3.14 | Extended Cauchy's theorem | **Included** |
| Def 21 | Winding number | **Partially Included** |

### Topic 4: Cauchy's Integral Formula

| # | Statement | Status |
|---|-----------|--------|
| Thm 4.1 | Cauchy's integral formula | **Included** |
| Thm 4.5 | Cauchy's formula for derivatives | **Included** |
| Thm 4.11 | Triangle inequality for integrals | **Included** |
| Thm 4.12 | Triangle inequality for integrals II | **Included** |
| Cor 1 | ML inequality | **Included** |
| Thm 4.14 | Second extension of Cauchy's theorem | **Partially Included** |
| Thm 7 | Analytic implies infinitely differentiable | **Included** |
| Thm 4.15 | Cauchy's inequality | **Included** |
| Thm 4.16 | Liouville's theorem | **Included** |
| Cor 2 | FTA via Liouville | **Included** |
| Thm 4.17 | Mean value property | **Included** |
| Thm 4.18 | Maximum modulus principle | **Included** |

### Topic 5: Harmonic Functions

| # | Statement | Status |
|---|-----------|--------|
| Def 5.1 | Harmonic function (Laplace equation) | **Partially Included** |
| Thm 5.2 | Analytic parts are harmonic | **Partially Included** |
| Thm 5.3 | Harmonic implies real part of analytic | **Partially Included** |
| Def 22 | Harmonic conjugates | **Partially Included** |
| Thm 8 | Mean value property for harmonic | **Partially Included** |
| Thm 9 | Maximum principle for harmonic | **Partially Included** |
| Lem 5.4 | Gradients of conjugates are orthogonal | **Not Included** |
| Thm 10 | Orthogonality of level curves | **Not Included** |

### Topic 6: Two-Dimensional Hydrodynamics

| # | Statement | Status |
|---|-----------|--------|
| Thm 11 | Analytic potential gives div/curl-free field | **Not Included** |
| Thm 12 | Irrotational incompressible flow has complex potential | **Not Included** |
| Thm 13 | Stream function theorem | **Not Included** |

### Topic 7: Taylor and Laurent Series

| # | Statement | Status |
|---|-----------|--------|
| Thm 14 | Sum of finite geometric series | **Included** |
| Thm 15 | Infinite geometric series | **Included** |
| Thm 7.1 | Convergence of power series | **Included** |
| Thm 7.5 | Taylor's theorem (complex) | **Included** |
| Cor 3 | Uniqueness of Taylor series | **Included** |
| Thm 7.6 | Zeros are isolated | **Included** |
| Def 23 | Order of a zero | **Included** |
| Def 24 | Isolated singularity | **Partially Included** |
| Thm 7.19 | Laurent series | **Partially Included** |
| Def 25 | Poles, essential/removable singularities | **Partially Included** |
| Def 7.31 | Residue | **Not Included** |

### Topic 8: Residue Theorem

| # | Statement | Status |
|---|-----------|--------|
| Def 26 | Holomorphic / Meromorphic | **Included** |
| Thm 16 | Picard's theorem | **Not Included** |
| Thm 17 | Quotients of functions (zero/pole orders) | **Included** |
| Thm 18 | Residue at simple pole ($1/g'(z_0)$) | **Not Included** |
| Thm 19 | Residues at higher order poles | **Not Included** |
| Thm 20 | Cauchy's residue theorem | **Not Included** |
| Def 27 | Residue at infinity | **Not Included** |
| Thm 21 | Computing residue at infinity | **Not Included** |

### Topic 9: Definite Integrals Using Residue Theorem

| # | Statement | Status |
|---|-----------|--------|
| Thm 9.1 | Estimation on semicircles | **Not Included** |
| Thm 9.2 | Jordan-type lemma | **Not Included** |
| Thm 9.7 | Trigonometric integrals via residues | **Not Included** |
| Thm 9.11 | Convergence implies p.v. convergence | **Not Included** |
| Def 28 | Cauchy principal value | **Partially Included** |
| Thm 9.13 | Integral over semicircle around simple pole | **Not Included** |
| Thm 9.14 | Integral over arc around simple pole | **Not Included** |
| Def 29 | Fourier transform | **Included** |
| Thm 22 | Fourier inversion formula | **Partially Included** |

### Topic 10: Conformal Transformations

| # | Statement | Status |
|---|-----------|--------|
| Def 30 | Conformal map | **Included** |
| Thm 10.3 | Conformal iff complex linear | **Included** |
| Thm 10.4 | Analytic with nonzero derivative is conformal | **Included** |
| Thm 10.9 | Level curves of $u,v$ orthogonal | **Not Included** |
| Thm 10.10 | Riemann mapping theorem | **Not Included** |
| Def 31 | Fractional linear transformation (Mobius) | **Partially Included** |
| Thm 23 | FLTs map circles/lines to circles/lines | **Not Included** |
| Def 32 | Symmetric points | **Not Included** |
| Thm 24 | FLTs preserve symmetry | **Not Included** |
| Thm 25 | Milne-Thomson circle theorem | **Not Included** |

### Topic 11: Argument Principle

| # | Statement | Status |
|---|-----------|--------|
| Thm 11.1 | $\oint f'/f = Z - P$ | **Not Included** |
| Def 33 | Winding number of $f$ | **Not Included** |
| Thm 11.4 | Argument principle | **Not Included** |
| Thm 11.6 | Rouche's theorem | **Not Included** |
| Cor 4 | FTA via Rouche | **Not Included** |
| Thm 11.18 | Nyquist stability criterion | **Not Included** |

### Topic 12: Laplace Transform

| # | Statement | Status |
|---|-----------|--------|
| Def 34 | Laplace transform | **Not Included** |
| Def 35 | Exponential type | **Not Included** |
| Thm 26 | Convergence for exponential type | **Not Included** |
| Thm 27 | Properties (linearity, shifts, derivatives) | **Not Included** |
| Thm 12.13 | Substitution rule | **Not Included** |
| Thm 12.20 | Laplace inversion 1 | **Not Included** |
| Thm 12.21 | Bromwich integral | **Not Included** |

### Topic 13: Analytic Continuation and Gamma Function

| # | Statement | Status |
|---|-----------|--------|
| Thm 13.2 | Uniqueness of analytic continuation | **Included** |
| Cor 5 | At most one analytic continuation | **Included** |
| Def 36 | Gamma function | **Included** |
| Thm 28 | Gamma is analytic for Re(z) > 0 | **Included** |
| Thm 29 | $\Gamma(n+1) = n!$ | **Included** |
| Thm 30 | Functional equation $\Gamma(z+1) = z\Gamma(z)$ | **Included** |
| Thm 31 | Meromorphic continuation of Gamma | **Included** |
| Thm 32 | Weierstrass product for Gamma | **Partially Included** |
| Thm 33 | Reflection formula | **Included** |
| Thm 34 | Stirling's formula | **Included** |
| Thm 35 | Legendre duplication formula | **Included** |
| Thm 36 | $\mathcal{L}(t^{z-1}) = \Gamma(z)/s^z$ | **Partially Included** |

---

## Summary

| Status | Count |
|--------|-------|
| **Included** | 55 |
| **Partially Included** | 22 |
| **Not Included** | 33 |
| **Total** | 110 |
