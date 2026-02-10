# All Sources and Selected Statements for Legal Review

## Overview

This document lists all mathematical sources and proposed statements for the autoformalization annotation project, organized for legal review. Each entry includes source metadata, copyright information, and the specific statement(s) we propose to formalize.

**Totals:**
- **63 sources** (23 MIT OCW courses + 40 external textbooks)
- **~110 statements** (52 previously selected + 18 from additional MIT OCW + ~40 from external textbooks)

**License categories:**
- CC BY-NC-SA 4.0 (MIT OCW): 23 sources
- CC BY 3.0 / CC BY 4.0: 2 sources
- CC BY-NC 4.0 / CC BY-NC-ND 4.0 / Open Access: 6 sources
- All Rights Reserved: 32 sources

---

## Part A: MIT OCW — Previously Selected (5 books, 52 statements)

All MIT OCW materials are licensed under **CC BY-NC-SA 4.0** (Creative Commons Attribution-NonCommercial-ShareAlike).

---

### A1. High Dimensional Statistics

- **OCW Course**: 18.S997 — High-Dimensional Statistics
- **OCW URL**: https://ocw.mit.edu/courses/18-s997-high-dimensional-statistics-spring-2015/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/high_dimensional_statistics/`

| # | Statement | Description |
|---|-----------|-------------|
| 1 | Proposition 1.1 | **Gaussian tail bound (Mills inequality)**: For X ~ N(0,1), P(X >= t) satisfies (1/t - 1/t³)(2π)^{-1/2}e^{-t²/2} ≤ P(X ≥ t) ≤ (1/t)(2π)^{-1/2}e^{-t²/2} |
| 2 | Theorem 1.13 | **Bernstein's inequality**: For independent zero-mean r.v.s with |X_i| ≤ M, P(|∑ X_i| ≥ t) ≤ 2 exp(-t²/(2(∑ Var(X_i) + Mt/3))) |
| 3 | Theorem 1.14 | **Maximum of sub-Gaussians**: E[max_{1≤i≤n} X_i] ≤ σ · √(2 log n) for sub-Gaussian X_i with parameter σ |
| 4 | Lemma 1.18 | **Epsilon-net covering bound**: The unit ball in ℝ^d has an ε-net of size at most (3/ε)^d |
| 5 | Theorem 4.8 | **Davis-Kahan sin(θ) theorem**: Perturbation bound for eigenvectors: if A, A+E are symmetric and λ is a simple eigenvalue of A, then sin(angle between eigenvectors) ≤ ‖E‖_op / gap |
| 6 | Lemma 5.3 | **Neyman-Pearson lemma**: The likelihood ratio test is the most powerful test for simple vs simple hypothesis testing at any given significance level |
| 7 | Proposition 5.6 | **KL divergence properties**: Non-negativity (Gibbs' inequality), additivity for product measures, and data processing inequality |
| 8 | Lemma 5.8 | **Pinsker's inequality**: TV(P,Q) ≤ √(KL(P‖Q)/2) |
| 9 | Theorem 5.10 | **Fano's inequality**: For any estimator of θ ∈ {1,…,M}, P(θ̂ ≠ θ) ≥ 1 - (I(θ;X) + log 2) / log M |
| 10 | Lemma 5.12 | **Varshamov-Gilbert lemma**: There exists a subset of {0,1}^d of size ≥ 2^{d/8} such that any two elements differ in at least d/4 coordinates |

---

### A2. Graph Theory and Additive Combinatorics

- **OCW Course**: 18.225 — Graph Theory and Additive Combinatorics
- **OCW URL**: https://ocw.mit.edu/courses/18-225-graph-theory-and-additive-combinatorics-fall-2023/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/graph_theory_and_additive_combinatorics/`

| # | Statement | Description |
|---|-----------|-------------|
| 11 | Theorem 0.1.1 | **Schur's theorem**: If the positive integers are finitely colored, there exists a monochromatic solution to x + y = z |
| 12 | Theorem 0.2.4 | **Szemerédi's theorem**: Every subset of the integers with positive upper density contains arithmetic progressions of any length |
| 13 | Theorem 1.4.2 | **Kővári-Sós-Turán theorem**: ex(n, K_{s,t}) ≤ (1/2)(t-1)^{1/s} n^{2-1/s} + (s-1)n/2 for s ≤ t |
| 14 | Theorem 1.5.1 | **Erdős-Stone-Simonovits theorem**: For any graph H with χ(H) ≥ 2, ex(n,H) = (1 - 1/(χ(H)-1) + o(1)) n²/2 |
| 15 | Theorem 3.2.4 | **Expander mixing lemma**: In a d-regular graph, |e(S,T) - d|S||T|/n| ≤ λ₂√(|S||T|) |
| 16 | Theorem 3.2.13 | **Cheeger's inequality**: h(G)²/(2d) ≤ d - λ₂ ≤ 2h(G) |
| 17 | Theorem 7.1.10 | **Freiman's theorem**: If |A+A| ≤ K|A| then A is contained in a GAP of bounded rank and size |
| 18 | Theorem 7.13.6 | **Balog-Szemerédi-Gowers theorem**: Large additive energy implies structured subsets with small sumset |
| 19 | Theorem 8.2.5 | **Szemerédi-Trotter theorem**: Incidences between n points and m lines in ℝ² is O(n^{2/3}m^{2/3} + n + m) |
| 20 | Theorem 8.2.3 | **Crossing number inequality**: cr(G) ≥ e(G)³/(64 v(G)²) when e(G) ≥ 4v(G) |
| 21 | Theorem 5.5.17 | **Shearer's entropy inequality**: Generalized subadditivity of entropy |
| 22 | Theorem 0.2.9 | **Green-Tao theorem**: The primes contain arbitrarily long arithmetic progressions |

---

### A3. Number Theory II: Class Field Theory

- **OCW Course**: 18.786 — Number Theory II: Class Field Theory
- **OCW URL**: https://ocw.mit.edu/courses/18-786-number-theory-ii-class-field-theory-spring-2016/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/number_theory_ii_class_field_theory/`

| # | Statement | Description |
|---|-----------|-------------|
| 23 | Theorem 1.1 | **Kronecker-Weber theorem**: Every abelian extension of ℚ is contained in a cyclotomic field |
| 24 | Theorem 1.2 | **Hasse-Minkowski theorem**: A quadratic form over ℚ has a nontrivial solution iff it has one over ℚ_p for all p and over ℝ |
| 25 | Theorem 9.2 | **Additive Hilbert 90**: H¹(Gal(L/K), L) = 0 for any Galois extension L/K |
| 26 | Claim 13.4 | **H₁(G,ℤ) = G^{ab}**: First group homology with ℤ coefficients is the abelianization |
| 27 | Theorem 1.5 | **Main theorem of Local Class Field Theory**: Canonical isomorphism Gal(K^{ab}/K) ≅ K̂ˣ |
| 28 | Theorem 21.6 | **Artin reciprocity**: The Artin map induces C_K / N_{L/K}(C_L) → Gal(L/K) |
| 29 | Corollary 19.5 | **Brauer group of local fields**: Br(K) ≅ ℚ/ℤ for nonarchimedean local fields |
| 30 | Theorem 19.16 | **Cohomological = CSA Brauer group**: The two definitions of Brauer group are canonically isomorphic |
| 31 | Theorem 4.1 | **Quadratic Hilbert reciprocity**: ∏_v (a,b)_v = 1 for all a,b ∈ ℚˣ |
| 32 | Theorem 3.1 | **Norm groups for tamely ramified extensions** |

---

### A4. Introduction to Partial Differential Equations

- **OCW Course**: 18.152 — Introduction to Partial Differential Equations
- **OCW URL**: https://ocw.mit.edu/courses/18-152-introduction-to-partial-differential-equations-fall-2011/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/introduction_to_partial_differential_equations/`

| # | Statement | Description |
|---|-----------|-------------|
| 33 | Theorem 1.1 (heat) | **Weak maximum principle for heat equation**: max u is attained on the parabolic boundary |
| 34 | Theorem 4.1 (Laplace) | **Mean value property**: Harmonic functions equal their spherical/ball averages |
| 35 | Theorem 5.1 | **Strong maximum principle**: Harmonic function attaining its max on a connected domain is constant |
| 36 | Theorem 4.1 (Harnack) | **Harnack's inequality**: For non-negative harmonic u on B(x₀, R), sup ≤ C(n) inf on B(x₀, R/2) |
| 37 | Theorem 3.1 (Poisson) | **Poisson's formula**: Solution to Δu = 0 on the ball with boundary data |
| 38 | Theorem 4.1 (wave) | **d'Alembert's formula**: Solution to 1D wave equation u_tt - c²u_xx = 0 |
| 39 | Theorem 1.1 (Kirchhoff) | **Kirchhoff's formula**: Solution to 3D wave equation as a surface integral |
| 40 | Theorem 2.1 (energy) | **Energy conservation for wave equation**: E(t) = (1/2)∫(u_t² + c²|∇u|²) is conserved |
| 41 | Theorem 1.1 (E-L) | **Euler-Lagrange equation**: Critical points of I[u] = ∫L(x,u,Du) satisfy div(D_p L) - D_u L = 0 |
| 42 | Theorem 4.1 (Burger) | **Singularity formation for Burger's equation**: Blowup iff min u₀' < 0, time = -1/min u₀' |

---

### A5. Algebraic Topology I

- **OCW Course**: 18.905 — Algebraic Topology I
- **OCW URL**: https://ocw.mit.edu/courses/18-905-algebraic-topology-i-fall-2016/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/algebraic_topology_i/`

| # | Statement | Description |
|---|-----------|-------------|
| 43 | Theorem 5.2 | **Homotopy invariance of singular homology**: Homotopic maps induce equal maps on homology |
| 44 | Theorem 6.2 | **Excision theorem**: H_n(X∖U, A∖U) ≅ H_n(X, A) under closure/interior conditions |
| 45 | Theorem 9.4 | **Mayer-Vietoris sequence**: Long exact sequence for X = A ∪ B |
| 46 | Theorem 17.1 | **Brouwer fixed point theorem**: Every continuous f: Dⁿ → Dⁿ has a fixed point |
| 47 | Theorem 24.1 | **Universal Coefficient Theorem**: Short exact sequence relating H_n(C) ⊗ G, H_n(C;G), and Tor |
| 48 | Theorem 25.13 | **Eilenberg-Zilber theorem**: S_*(X × Y) ≃ S_*(X) ⊗ S_*(Y) |
| 49 | Theorem 25.15 | **Künneth theorem**: H_n(X × Y; k) = ⨁_{p+q=n} H_p(X;k) ⊗ H_q(Y;k) for fields k |
| 50 | Theorem 34.2 | **Poincaré duality**: For closed oriented n-manifold M, H^k(M) ≅ H_{n-k}(M) |
| 51 | Theorem 38.4 | **Alexander duality**: H̃^k(K) ≅ H̃_{n-k-1}(Sⁿ∖K) for compact K ⊂ Sⁿ |
| 52 | Theorem 38.11 | **Borsuk-Ulam theorem**: For continuous f: Sⁿ → ℝⁿ, ∃x with f(x) = f(-x) |

---

## Part B: MIT OCW — Additional Books (18 books, 1 statement each)

All MIT OCW materials are licensed under **CC BY-NC-SA 4.0**.

For each book below, the statement was verified in the course's `all_statements.md`.

---

### B1. Elliptic Curves

- **OCW Course**: 18.783 — Elliptic Curves
- **OCW URL**: https://ocw.mit.edu/courses/18-783-elliptic-curves-spring-2021/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/elliptic_curves/`

| # | Statement | Description |
|---|-----------|-------------|
| 53 | Theorem 7.3 [Hasse] | **Hasse bound**: For an elliptic curve E/𝔽_q, #E(𝔽_q) = q+1-t where t = tr(π_E) is the trace of the Frobenius endomorphism and |t| ≤ 2√q. |

---

### B2. Differential Geometry

- **OCW Course**: 18.950 — Differential Geometry
- **OCW URL**: https://ocw.mit.edu/courses/18-950-differential-geometry-fall-2008/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/differential_geometry/`

| # | Statement | Description |
|---|-----------|-------------|
| 54 | Corollary 34.5 | **Gauss-Bonnet theorem**: For any compact surface M in ℝ³, κ_gauss^{tot} = 2π · χ(M). |

---

### B3. Algebraic Topology II

- **OCW Course**: 18.906 — Algebraic Topology II
- **OCW URL**: https://ocw.mit.edu/courses/18-906-algebraic-topology-ii-spring-2020/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/algebraic_topology_ii/`

| # | Statement | Description |
|---|-----------|-------------|
| 55 | Corollary 11.2 | **Freudenthal suspension theorem**: For a (k-1)-connected CW complex X with k ≥ 1, the suspension map σ: π_q(X) → π_{q+1}(ΣX) is an isomorphism for q < 2k-1 and a surjection for q = 2k-1. |

---

### B4. Lie Groups and Lie Algebras I

- **OCW Course**: 18.745 — Lie Groups and Lie Algebras I
- **OCW URL**: https://ocw.mit.edu/courses/18-745-lie-groups-and-lie-algebras-i-fall-2020/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/lie_groups_and_lie_algebras_i/`

| # | Statement | Description |
|---|-----------|-------------|
| 56 | Theorem 4.1 | **Quotient manifold theorem**: Let G be a Lie group of dimension n and H ⊂ G a closed Lie subgroup of dimension k. Then G/H has a natural (n-k)-dimensional manifold structure, and p: G → G/H is a locally trivial fibration with fiber H. If H is normal then G/H is a Lie group. |

---

### B5. Fourier Analysis

- **OCW Course**: 18.103 — Fourier Analysis
- **OCW URL**: https://ocw.mit.edu/courses/18-103-fourier-analysis-fall-2013/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/fourier_analysis/`

| # | Statement | Description |
|---|-----------|-------------|
| 57 | Theorem 2 | **Weyl equidistribution theorem**: If α is irrational and 0 ≤ a < b ≤ 1, then lim_{N→∞} #{m : 0 ≤ m ≤ N-1, a ≤ {mα} ≤ b}/N = b-a. |

---

### B6. Probabilistic Methods in Combinatorics

- **OCW Course**: 18.226 — Probabilistic Methods in Combinatorics
- **OCW URL**: https://ocw.mit.edu/courses/18-226-probabilistic-methods-in-combinatorics-fall-2022/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/probabilistic_methods_in_combinatorics/`

| # | Statement | Description |
|---|-----------|-------------|
| 58 | Theorem 6.1.7 | **Lovász Local Lemma (symmetric form)**: If P[A_i] ≤ p and each A_i is independent from all but at most d others, and ep(d+1) ≤ 1, then P(none of A_i occur) > 0. |

---

### B7. Theory of Computation

- **OCW Course**: 18.404J — Theory of Computation
- **OCW URL**: https://ocw.mit.edu/courses/18-404j-theory-of-computation-fall-2020/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/theory_of_computation/`

| # | Statement | Description |
|---|-----------|-------------|
| 59 | Theorem (Hilbert's 10th, 1971) | **Undecidability of Diophantine equations**: D = {⟨p⟩ | polynomial p(x₁,…,x_k) = 0 has integer solution} is not decidable. |

---

### B8. Theory of Probability

- **OCW Course**: 18.175 — Theory of Probability
- **OCW URL**: https://ocw.mit.edu/courses/18-175-theory-of-probability-spring-2014/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/theory_of_probability/`

| # | Statement | Description |
|---|-----------|-------------|
| 60 | Theorem (Birkhoff) | **Birkhoff's ergodic theorem**: Let φ be a measure preserving transformation of (Ω,ℱ,P). For any X ∈ L¹, (1/n)∑_{m=0}^{n-1} X(φ^m ω) → E(X|ℐ) a.s. and in L¹. |

---

### B9. Combinatorial Optimization

- **OCW Course**: 18.433 — Combinatorial Optimization
- **OCW URL**: https://ocw.mit.edu/courses/18-433-combinatorial-optimization-fall-2003/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/combinatorial_optimization/`

| # | Statement | Description |
|---|-----------|-------------|
| 61 | Theorem 4 | **Max Flow-Min Cut theorem**: The maximum flow is equal to the minimum capacity cut. |

---

### B10. The Polynomial Method

- **OCW Course**: 18.S997 — The Polynomial Method
- **OCW URL**: https://ocw.mit.edu/courses/18-s997-the-polynomial-method-fall-2012/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/the_polynomial_method/`

| # | Statement | Description |
|---|-----------|-------------|
| 62 | Theorem 0.2 | **Finite field Kakeya conjecture**: A Kakeya set K in 𝔽ⁿ has at least c_n qⁿ elements. |

---

### B11. Noncommutative Algebra

- **OCW Course**: 18.706 — Noncommutative Algebra
- **OCW URL**: https://ocw.mit.edu/courses/18-706-noncommutative-algebra-spring-2023/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/noncommutative_algebra/`

| # | Statement | Description |
|---|-----------|-------------|
| 63 | Theorem 7.1 | **Morita equivalence**: Let R be a ring and P a finitely generated projective right R-module. Then End_R(P)-mod is equivalent to R-mod iff P is a projective generator. |

---

### B12. Tensor Categories

- **OCW Course**: 18.769 — Topics in Lie Theory: Tensor Categories
- **OCW URL**: https://ocw.mit.edu/courses/18-769-topics-in-lie-theory-tensor-categories-spring-2009/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/tensor_categories/`

| # | Statement | Description |
|---|-----------|-------------|
| 64 | Theorem 1.8.5 | **MacLane's Strictness theorem**: Any monoidal category is monoidally equivalent to a strict monoidal category. |

---

### B13. Algebraic Geometry II

- **OCW Course**: 18.726 — Algebraic Geometry
- **OCW URL**: https://ocw.mit.edu/courses/18-726-algebraic-geometry-spring-2009/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/algebraic_geometry_ii/`

| # | Statement | Description |
|---|-----------|-------------|
| 65 | Statement 56 | **Riemann-Roch for curves**: There exists a nonneg integer g = g(X) such that for any divisor D and canonical divisor K, l(D) - l(K - D) = deg(D) + 1 - g. |

---

### B14. Statistical Learning Theory

- **OCW Course**: 18.465 — Topics in Statistics: Statistical Learning Theory
- **OCW URL**: https://ocw.mit.edu/courses/18-465-topics-in-statistics-statistical-learning-theory-spring-2007/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/statistical_learning_theory/`

| # | Statement | Description |
|---|-----------|-------------|
| 66 | Theorem 22.1 | **McDiarmid's inequality**: If |Z(x₁,…,x_i',…,x_n) - Z(x₁,…,x_i,…,x_n)| ≤ c_i, then P(Z - E[Z] > t) ≤ exp(-t²/(2∑c_i²)). |

---

### B15. Analysis of Boolean Functions

- **OCW Course**: 18.218 — Topics in Combinatorics: Analysis of Boolean Functions
- **OCW URL**: https://ocw.mit.edu/courses/18-218-topics-in-combinatorics-analysis-of-boolean-functions-spring-2021/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/analysis_of_boolean_functions/`

| # | Statement | Description |
|---|-----------|-------------|
| 67 | Theorem 5.5 | **KKL theorem (Kahn-Kalai-Linial)**: There is an absolute constant c > 0 such that for any f: {-1,1}ⁿ → {-1,1}, there is i ∈ [n] such that I_i[f] ≥ c(log n / n)Var(f). |

---

### B16. Geometry of Manifolds I

- **OCW Course**: 18.965 — Geometry of Manifolds
- **OCW URL**: https://ocw.mit.edu/courses/18-965-geometry-of-manifolds-fall-2004/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/geometry_of_manifolds_i/`

| # | Statement | Description |
|---|-----------|-------------|
| 68 | Theorem 21.4 | **Frobenius theorem**: An involutive subbundle of the tangent bundle is integrable. |

---

### B17. Introduction to Arithmetic Geometry

- **OCW Course**: 18.782 — Introduction to Arithmetic Geometry
- **OCW URL**: https://ocw.mit.edu/courses/18-782-introduction-to-arithmetic-geometry-fall-2013/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/introduction_to_arithmetic_geometry/`

| # | Statement | Description |
|---|-----------|-------------|
| 69 | Theorem (Faltings 1983) | **Faltings' theorem (Mordell conjecture)**: Let C/ℚ be an irreducible curve of genus greater than 1. Then |C(ℚ)| is finite. |

---

### B18. Number Theory I

- **OCW Course**: 18.785 — Number Theory I
- **OCW URL**: https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/
- **License**: CC BY-NC-SA 4.0
- **Directory**: `mit_books/number_theory_i/`

| # | Statement | Description |
|---|-----------|-------------|
| 70 | Theorem 18.1 | **Dirichlet's theorem on primes in arithmetic progressions**: For all coprime integers a and m there are infinitely many primes p ≡ a mod m. |

---

## Part C: External Textbooks (40 books, 1 statement each)

For each book, we propose one landmark theorem. These are best-effort assessments — the external books have not been processed through our full pipeline.

### Open Access / CC-Licensed Sources

---

#### C1. Linear Algebra Done Right

- **Author**: Sheldon Axler
- **Copyright**: © 1996–2024 Sheldon Axler. Released as Open Access under **CC BY-NC 4.0**.
- **URL**: https://linear.axler.net/LADR4e.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 71 | Ch. 7 | **Spectral theorem for normal operators**: A linear operator on a finite-dimensional complex inner product space is normal iff it has an orthonormal basis of eigenvectors. |

---

#### C2. Learning Theory from First Principles

- **Author**: Francis Bach
- **Copyright**: © 2024 Francis Bach. MIT Press, **CC BY-NC-ND 4.0**.
- **URL**: https://www.di.ens.fr/~fbach/ltfp_book.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 72 | Ch. 12 | **Minimax lower bound via Fano's method**: The minimax risk over a parameter class is bounded below by a function of the KL divergence between distributions indexed by a packing set. |

---

#### C3. Convex Optimization: Algorithms and Complexity

- **Author**: Sébastien Bubeck
- **Copyright**: © 2015 Sébastien Bubeck (Now Publishers). arXiv preprint (nonexclusive distribution license).
- **URL**: https://arxiv.org/pdf/1405.4980

| # | Statement | Description |
|---|-----------|-------------|
| 73 | §3.7 | **Nesterov's accelerated gradient convergence**: For L-smooth convex f, Nesterov's method achieves f(x_t) - f(x*) ≤ O(L‖x₀ - x*‖²/t²). |

---

#### C4. Algebraic Topology

- **Author**: Allen Hatcher
- **Copyright**: © 2002 Cambridge Univ. Press — free to download for personal use by author's arrangement.
- **URL**: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 74 | Theorem 1.20 | **Seifert-van Kampen theorem**: For a space X = U₁ ∪ U₂ with U₁, U₂, U₁∩U₂ path-connected and open, π₁(X) ≅ π₁(U₁) *_{π₁(U₁∩U₂)} π₁(U₂). |

---

#### C5. Foundations of Machine Learning

- **Author**: Mohri, Rostamizadeh & Talwalkar
- **Copyright**: © 2018 Mehryar Mohri et al. MIT Press, **CC BY-NC-ND 4.0** (Open Access).
- **URL**: https://www.dropbox.com/s/38p0j6ds5q9c8oe/10290.pdf?dl=1

| # | Statement | Description |
|---|-----------|-------------|
| 75 | Ch. 6 | **PAC-Bayes bound**: For any prior P over hypotheses and any δ > 0, with probability ≥ 1-δ over S ~ D^m, for all posteriors Q: E_Q[R(h)] ≤ E_Q[R̂_S(h)] + √(KL(Q‖P) + ln(m/δ))/(2m). |

---

#### C6. An Introduction to Measure Theory

- **Author**: Terence Tao
- **Copyright**: © 2011 Terence Tao (AMS). Free author-provided PDF (preliminary version).
- **URL**: https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-126-tao5-measure-book.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 76 | §1.6 | **Lebesgue differentiation theorem**: For f ∈ L¹(ℝⁿ), lim_{r→0} (1/|B(x,r)|)∫_{B(x,r)} f = f(x) for a.e. x. |

---

### All Rights Reserved Sources

---

#### C7. Complex Analysis

- **Author**: Lars Ahlfors
- **Copyright**: © 1953, 1966, 1979 McGraw-Hill, Inc. All rights reserved.
- **URL**: https://mccuan.math.gatech.edu/courses/6321/lars-ahlfors-complex-analysis-third-edition-mcgraw-hill-science_engineering_math-1979.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 77 | Ch. 6 | **Riemann Mapping Theorem**: Any simply connected proper open subset of ℂ is biholomorphic to the open unit disk. |

---

#### C8. Mathematical Analysis

- **Author**: Tom Apostol
- **Copyright**: © 1974 Addison-Wesley (Pearson Education). All rights reserved.
- **URL**: https://invent.ilmkidunya.com/images/Section/mathematical-analysis-css-book.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 78 | Ch. 13 | **Implicit Function Theorem (C^k form)**: If F: ℝⁿ⁺ᵐ → ℝⁿ is C^k with F(a,b) = 0 and D_x F(a,b) invertible, then there exists a C^k function g with F(g(y),y) = 0 near (a,b). |

---

#### C9. Analysis and Geometry of Markov Diffusion Operators

- **Author**: Dominique Bakry, Ivan Gentil, Michel Ledoux
- **Copyright**: © 2014 Springer-Verlag. All rights reserved.
- **URL**: https://www.hse.ru/data/2016/11/24/1113029204/bok%253A978-3-319-00227-9.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 79 | Ch. 4 | **Bakry-Émery criterion (Γ₂ criterion)**: If Γ₂(f) ≥ ρΓ(f) for some ρ > 0, then the operator satisfies a logarithmic Sobolev inequality with constant 2/ρ. |

---

#### C10. Convex Analysis and Monotone Operator Theory in Hilbert Spaces

- **Author**: Heinz Bauschke & Patrick Combettes
- **Copyright**: © 2011 Springer. All rights reserved.
- **URL**: https://pcombet.math.ncsu.edu/livre1.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 80 | Ch. 22 | **Minty's theorem**: A monotone operator A on a Hilbert space is maximally monotone iff Range(Id + A) = H. |

---

#### C11. Lectures on the Nearest Neighbor Method

- **Author**: Gérard Biau & Luc Devroye
- **Copyright**: © 2015 Springer International Publishing. All rights reserved.
- **URL**: https://luc.devroye.org/Biau+Devroye-LecturesontheNearestNeighborMethod-2015.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 81 | Ch. 6 | **Stone's universal consistency theorem**: The k-nearest neighbor classifier is universally consistent (its risk converges to the Bayes risk) for any distribution, provided k → ∞ and k/n → 0. |

---

#### C12. Éléments de Mathématique

- **Author**: Nicolas Bourbaki
- **Copyright**: Published 1939–1983 by multiple publishers (Hermann, Addison-Wesley). All volumes remain in copyright (no open license).
- **URL**: No publicly available URL. ISBN series: see `books/list.md`.

| # | Statement | Description |
|---|-----------|-------------|
| 82 | Ch. III (Set Theory) | **Bourbaki-Witt fixed point theorem**: Every increasing self-map on a chain-complete poset with a least element has a fixed point. |

---

#### C13. The Structure and Stability of Persistence Diagrams

- **Author**: Frédéric Chazal et al.
- **Copyright**: © 2013 F. Chazal et al. All rights reserved (author preprint, nonexclusive arXiv distribution).
- **URL**: https://arxiv.org/pdf/1207.3674

| # | Statement | Description |
|---|-----------|-------------|
| 83 | Theorem 4.11 | **Stability theorem for persistence diagrams**: The bottleneck distance between persistence diagrams is bounded by the L^∞ distance between the defining functions: d_B(Dgm(f), Dgm(g)) ≤ ‖f - g‖_∞. |

---

#### C14. Discriminants, Resultants, and Multidimensional Determinants

- **Author**: Gelfand, Kapranov, Zelevinsky
- **Copyright**: © 1994 Birkhäuser (Springer). All rights reserved.
- **URL**: https://webhomes.maths.ed.ac.uk/~v1ranick/papers/gelkapzel.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 84 | Ch. 9 | **A-discriminant formula / Kapranov's theorem**: Characterization of the A-discriminant variety via secondary polytopes and tropical geometry. |

---

#### C15. Commutative Algebra

- **Author**: David Eisenbud
- **Copyright**: © 1995 Springer-Verlag. All rights reserved.
- **URL**: https://www.math.ens.psl.eu/~benoist/refs/Eisenbud.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 85 | Theorem 3.10 | **Primary decomposition theorem**: Every ideal in a Noetherian ring has a primary decomposition: I = Q₁ ∩ … ∩ Q_r where each Q_i is primary, and the associated primes are uniquely determined. |

---

#### C16. Partial Differential Equations

- **Author**: Lawrence Evans
- **Copyright**: © 1998, 2010 American Mathematical Society. All rights reserved.
- **URL**: https://math24.wordpress.com/wp-content/uploads/2013/02/partial-differential-equations-by-evans.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 86 | §6.2 | **Lax-Milgram theorem**: If B is a bounded coercive bilinear form on a Hilbert space H and f ∈ H*, then there exists a unique u ∈ H with B(u,v) = ⟨f,v⟩ for all v. |

---

#### C17. An Introduction to Probability Theory and Its Applications

- **Author**: William Feller
- **Copyright**: © 1950, 1957, 1968 John Wiley & Sons, Inc. All rights reserved.
- **URL**: https://bitcoinwords.github.io/assets/papers/an-introduction-to-probability-theory-and-its-applications.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 87 | Ch. III | **Arc-sine law for random walks**: For a symmetric random walk S_n, the fraction of time spent positive converges to the arc-sine distribution: P(S₁ > 0,…,S_{2k} > 0 for exactly j of 2n steps) → (2/π)arcsin(√p). |

---

#### C18. Real Analysis

- **Author**: Gerald Folland
- **Copyright**: © 1984, 1999 John Wiley & Sons, Inc. All rights reserved.
- **URL**: https://apachepersonal.miun.se/~andrli/Bok.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 88 | §7.1 | **Riesz representation theorem (positive linear functionals)**: Every positive linear functional on C_c(X) for a locally compact Hausdorff space X is given by integration against a unique Radon measure. |

---

#### C19. Algebraic Geometry

- **Author**: Robin Hartshorne
- **Copyright**: © 1977 Springer-Verlag. All rights reserved.
- **URL**: https://www.math.stonybrook.edu/~kamenova/homepage_files/Hartshorne_engl.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 89 | Ch. III, §7 | **Serre duality**: For a smooth projective variety X of dimension n over a field k, H^i(X, ℱ) ≅ H^{n-i}(X, ωX ⊗ ℱ∨)∨ where ωX is the canonical sheaf. |

---

#### C20. Tropical Algebraic Geometry

- **Author**: Itenberg, Mikhalkin, Shustin
- **Copyright**: © 2007 Birkhäuser Basel (Springer). All rights reserved.
- **URL**: No publicly available URL. ISBN: 9783034600477.

| # | Statement | Description |
|---|-----------|-------------|
| 90 | Ch. 3 | **Kapranov's theorem (tropical)**: The tropicalization of a hypersurface {f = 0} ⊂ (K*)ⁿ coincides with the non-Archimedean amoeba, which is a polyhedral complex dual to the Newton subdivision of f. |

---

#### C21. Introductory Functional Analysis with Applications

- **Author**: Erwin Kreyszig
- **Copyright**: © 1978 John Wiley & Sons, Inc. All rights reserved.
- **URL**: https://physics.bme.hu/sites/physics.bme.hu/files/users/BMETE15AF53_kov/Kreyszig%20-%20Introductory%20Functional%20Analysis%20with%20Applications%20(1).pdf

| # | Statement | Description |
|---|-----------|-------------|
| 91 | §4.9 | **Banach-Steinhaus uniform boundedness principle**: If {T_α} is a family of bounded linear operators on a Banach space X such that sup_α ‖T_α x‖ < ∞ for each x, then sup_α ‖T_α‖ < ∞. |

---

#### C22. Algebra

- **Author**: Serge Lang
- **Copyright**: © 2002 Springer Science+Business Media. All rights reserved.
- **URL**: No publicly available URL. ISBN: 9780387953854.

| # | Statement | Description |
|---|-----------|-------------|
| 92 | Ch. III, §7 | **Structure theorem for finitely generated modules over a PID**: Every finitely generated module over a PID is isomorphic to a direct sum of cyclic modules R/(d₁) ⊕ … ⊕ R/(d_r) ⊕ R^s where d₁ | d₂ | … | d_r. |

---

#### C23. Introduction to Smooth Manifolds

- **Author**: John Lee
- **Copyright**: © 2003, 2013 Springer-Verlag. All rights reserved.
- **URL**: https://julianchaidez.net/materials/reu/lee_smooth_manifolds.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 93 | Ch. 16 | **Stokes' theorem on manifolds**: For a compact oriented smooth n-manifold M with boundary and ω an (n-1)-form, ∫_M dω = ∫_{∂M} ω. |

---

#### C24. A Wavelet Tour of Signal Processing

- **Author**: Stéphane Mallat
- **Copyright**: © 2009 Elsevier Inc. (Academic Press). All rights reserved.
- **URL**: https://www.di.ens.fr/~mallat/papiers/WaveletTourChap1-2-3.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 94 | Ch. 7 | **Multiresolution analysis characterization**: An orthogonal wavelet basis of L²(ℝ) arises from a multiresolution analysis iff the scaling function φ satisfies φ̂(ξ) = m₀(ξ/2)φ̂(ξ/2) with |m₀|² + |m₀(· + π)|² = 1. |

---

#### C25. Model Theory: An Introduction

- **Author**: David Marker
- **Copyright**: © 2002 Springer-Verlag. All rights reserved.
- **URL**: https://www.nzdr.ru/data/media/biblio/kolxoz/M/MA/MAml/Marker%20D.%20Model%20theory..%20an%20introduction%20(GTM217,%20Springer,%202002)(ISBN%200387987606)(O)(351s)_MAml_.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 95 | §2.1 | **Compactness theorem for first-order logic**: A set of first-order sentences has a model iff every finite subset has a model. |

---

#### C26. Topology

- **Author**: James Munkres
- **Copyright**: © 2000 Pearson Education, Inc. All rights reserved.
- **URL**: https://eclass.uoa.gr/modules/document/file.php/MATH707/James%20R.%20Munkres%20Topology%20%20Prentice%20Hall%2C%20Incorporated%2C%202000%20by%20James%20R.%20Munkres%20%28z-lib.org%29.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 96 | §34 | **Urysohn metrization theorem**: Every regular second-countable T₁ space is metrizable. |

---

#### C27. Methods of Modern Mathematical Physics, Vol. 1

- **Author**: Michael Reed, Barry Simon
- **Copyright**: © 1972, 1980 Academic Press, Inc. All rights reserved.
- **URL**: https://www.astrosen.unam.mx/~aceves/Metodos/ebooks/reed_simon1.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 97 | §XI | **RAGE theorem**: For a self-adjoint operator H on a Hilbert space, the time-averaged probability of finding a state in any compact region vanishes for the continuous spectral subspace. |

---

#### C28. Convex Analysis

- **Author**: R. Tyrrell Rockafellar
- **Copyright**: © 1970 Princeton University Press. All rights reserved.
- **URL**: No publicly available URL. ISBN: 9780691015866.

| # | Statement | Description |
|---|-----------|-------------|
| 98 | §31 | **Fenchel duality theorem**: For proper convex functions f and g and a linear map A, under constraint qualification, inf_x {f(x) + g(Ax)} = sup_y {-f*(A*y) - g*(-y)}. |

---

#### C29. Variational Analysis

- **Author**: R. Tyrrell Rockafellar, Roger Wets
- **Copyright**: © 1998 Springer-Verlag. All rights reserved.
- **URL**: https://sites.math.washington.edu/~rtr/papers/rtr169-VarAnalysis-RockWets.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 99 | §1.G | **Moreau-Yosida regularization**: For a proper lsc convex function f on a Hilbert space, the Moreau envelope e_λ f(x) = inf_y {f(y) + ‖x-y‖²/(2λ)} is C^{1,1} with gradient (x - prox_λf(x))/λ. |

---

#### C30. Functional Analysis

- **Author**: Walter Rudin
- **Copyright**: © 1973, 1991 McGraw-Hill, Inc. All rights reserved.
- **URL**: https://59clc.wordpress.com/wp-content/uploads/2012/08/functional-analysis-_-rudin-2th.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 100 | §3.4 | **Hahn-Banach theorem (geometric form)**: If A and B are disjoint nonempty convex sets in a locally convex space, with A open, then there exists a continuous linear functional separating them. |

---

#### C31. Principles of Mathematical Analysis

- **Author**: Walter Rudin
- **Copyright**: © 1964, 1976 McGraw-Hill, Inc. All rights reserved.
- **URL**: https://david92jackson.neocities.org/images/Principles_of_Mathematical_Analysis-Rudin.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 101 | §7.25 | **Arzelà-Ascoli theorem**: A subset of C(X, ℝⁿ) for compact X is relatively compact iff it is equicontinuous and pointwise bounded. |

---

#### C32. Real and Complex Analysis

- **Author**: Walter Rudin
- **Copyright**: © 1966, 1974, 1987 McGraw-Hill. All rights reserved.
- **URL**: https://perso.telecom-paristech.fr/decreuse/_downloads/c22155fef582344beb326c1f44f437d2/rudin.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 102 | §13 | **Runge's approximation theorem**: If K ⊂ ℂ is compact and ℂ∖K is connected, then every holomorphic function on a neighborhood of K can be uniformly approximated on K by polynomials. |

---

#### C33. Calculus

- **Author**: Michael Spivak
- **Copyright**: © 1967, 1980, 1994 Michael Spivak (Publish-or-Perish Press). All rights reserved.
- **URL**: No publicly available URL. ISBN: 9780914098911.

| # | Statement | Description |
|---|-----------|-------------|
| 103 | Ch. 13 | **Fundamental Theorem of Calculus (Darboux integrability form)**: If f is integrable on [a,b] and F(x) = ∫_a^x f, then F is continuous; if f is continuous at c then F is differentiable at c with F'(c) = f(c). |

---

#### C34. Multidimensional Diffusion Processes

- **Author**: Daniel Stroock, Srinivasa Varadhan
- **Copyright**: © 1979 Springer-Verlag. All rights reserved.
- **URL**: No publicly available URL. ISBN: 9780387903538.

| # | Statement | Description |
|---|-----------|-------------|
| 104 | Ch. 6 | **Martingale problem existence/uniqueness**: Under suitable regularity conditions on the coefficients a and b, the martingale problem for L = (1/2)∑a_{ij}∂²/∂x_i∂x_j + ∑b_i∂/∂x_i has a unique solution. |

---

#### C35. Analysis II

- **Author**: Terence Tao
- **Copyright**: © 2006 Terence Tao (Hindustan Book Agency). All rights reserved.
- **URL**: https://cjhb.site/Files.php/books/(Uncategorized)/%E9%99%B6%E5%93%B2%E8%BD%A9%E5%AE%9E%E5%88%86%E6%9E%902%E5%86%8C%EF%BC%8C%E7%AC%AC%E4%B8%89%E7%89%88.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 105 | §10.5 | **Picard's existence and uniqueness theorem for ODEs**: If f: [t₀-ε, t₀+ε] × B(x₀,r) → ℝⁿ is Lipschitz in x, then the IVP x' = f(t,x), x(t₀) = x₀ has a unique solution on some interval. |

---

#### C36. Introduction to Nonparametric Estimation

- **Author**: Alexandre Tsybakov
- **Copyright**: © 2009 Springer Science+Business Media. All rights reserved.
- **URL**: https://www.personal.soton.ac.uk/cz1y20/Reading_Group/mlts-2023w/Tsybakov_Nonparametric_Estimation.pdf

| # | Statement | Description |
|---|-----------|-------------|
| 106 | §2.7 | **Assouad's lemma**: The minimax risk over a parameter class Θ containing a 2^d-element hypercube is bounded below by (d/2) · τ² · (1 - TV), where τ is the minimum separation and TV is the max total variation between adjacent vertices. |

---

#### C37. Topics in Optimal Transportation

- **Author**: Cédric Villani
- **Copyright**: © 2003 American Mathematical Society. All rights reserved.
- **URL**: https://libgen.la/edition.php?id=43701006

| # | Statement | Description |
|---|-----------|-------------|
| 107 | Ch. 2 | **Brenier's theorem**: For absolutely continuous probability measures μ and ν on ℝⁿ with finite second moments, the optimal transport map for quadratic cost is the gradient of a convex function: T = ∇φ. |

---

#### C38. Hodge Theory and Complex Algebraic Geometry, Vol. 1

- **Author**: Claire Voisin
- **Copyright**: © 2002 Cambridge University Press. All rights reserved.
- **URL**: https://libgen.la/edition.php?id=136114971

| # | Statement | Description |
|---|-----------|-------------|
| 108 | Ch. 6 | **Hodge decomposition theorem**: For a compact Kähler manifold X, H^k(X, ℂ) = ⨁_{p+q=k} H^{p,q}(X) where H^{p,q} = H^{q,p} (conjugate). |

---

### Additional Books from `books/` Directory

---

#### C39. Buildings (book.pdf)

- **Author**: Paul Garrett
- **Copyright**: © Paul Garrett. Licensed under **CC BY 3.0**.
- **URL**: Local file `books/buildings/book.pdf`

| # | Statement | Description |
|---|-----------|-------------|
| 109 | TBD | **Tits' theorem / Building axioms**: Classification or structural result for buildings, e.g., that a thick irreducible spherical building of rank ≥ 3 is associated to a simple algebraic group over a field. |

---

#### C40. Spectral Methods for Data Science

- **Author**: Yuxin Chen et al.
- **Copyright**: © Yuxin Chen et al. Licensed under **CC BY 4.0**.
- **URL**: Local TeX source `books/spectral_methods_data_science/`

| # | Statement | Description |
|---|-----------|-------------|
| 110 | TBD | **Spectral clustering guarantee**: Under a planted partition / stochastic block model, spectral methods (based on eigenvectors of the adjacency or Laplacian matrix) achieve exact or near-exact community recovery above the information-theoretic threshold. |

---

## Summary Table

### Source Counts by License Category

| License Category | # Sources | # Statements |
|-----------------|-----------|-------------|
| CC BY-NC-SA 4.0 (MIT OCW) | 23 | 70 |
| CC BY 3.0 / CC BY 4.0 | 2 | 2 |
| CC BY-NC 4.0 | 1 | 1 |
| CC BY-NC-ND 4.0 / Open Access | 3 | 3 |
| Free author PDF / arXiv preprint | 2 | 2 |
| All Rights Reserved | 32 | 32 |
| **Total** | **63** | **110** |

### Master Source Table

| # | Source | Author(s) | License | Part | Statements |
|---|--------|-----------|---------|------|------------|
| 1 | High Dimensional Statistics (MIT OCW 18.S997) | — | CC BY-NC-SA | A | 10 |
| 2 | Graph Theory & Additive Combinatorics (MIT OCW 18.225) | — | CC BY-NC-SA | A | 12 |
| 3 | Number Theory II: Class Field Theory (MIT OCW 18.786) | — | CC BY-NC-SA | A | 10 |
| 4 | Introduction to PDE (MIT OCW 18.152) | — | CC BY-NC-SA | A | 10 |
| 5 | Algebraic Topology I (MIT OCW 18.905) | — | CC BY-NC-SA | A | 10 |
| 6 | Elliptic Curves (MIT OCW 18.783) | — | CC BY-NC-SA | B | 1 |
| 7 | Differential Geometry (MIT OCW 18.950) | — | CC BY-NC-SA | B | 1 |
| 8 | Algebraic Topology II (MIT OCW 18.906) | — | CC BY-NC-SA | B | 1 |
| 9 | Lie Groups and Lie Algebras I (MIT OCW 18.745) | — | CC BY-NC-SA | B | 1 |
| 10 | Fourier Analysis (MIT OCW 18.103) | — | CC BY-NC-SA | B | 1 |
| 11 | Probabilistic Methods in Combinatorics (MIT OCW 18.226) | — | CC BY-NC-SA | B | 1 |
| 12 | Theory of Computation (MIT OCW 18.404J) | — | CC BY-NC-SA | B | 1 |
| 13 | Theory of Probability (MIT OCW 18.175) | — | CC BY-NC-SA | B | 1 |
| 14 | Combinatorial Optimization (MIT OCW 18.433) | — | CC BY-NC-SA | B | 1 |
| 15 | The Polynomial Method (MIT OCW 18.S997) | — | CC BY-NC-SA | B | 1 |
| 16 | Noncommutative Algebra (MIT OCW 18.706) | — | CC BY-NC-SA | B | 1 |
| 17 | Tensor Categories (MIT OCW 18.769) | — | CC BY-NC-SA | B | 1 |
| 18 | Algebraic Geometry II (MIT OCW 18.726) | — | CC BY-NC-SA | B | 1 |
| 19 | Statistical Learning Theory (MIT OCW 18.465) | — | CC BY-NC-SA | B | 1 |
| 20 | Analysis of Boolean Functions (MIT OCW 18.218) | — | CC BY-NC-SA | B | 1 |
| 21 | Geometry of Manifolds I (MIT OCW 18.965) | — | CC BY-NC-SA | B | 1 |
| 22 | Introduction to Arithmetic Geometry (MIT OCW 18.782) | — | CC BY-NC-SA | B | 1 |
| 23 | Number Theory I (MIT OCW 18.785) | — | CC BY-NC-SA | B | 1 |
| 24 | Linear Algebra Done Right | Axler | CC BY-NC 4.0 | C | 1 |
| 25 | Learning Theory from First Principles | Bach | CC BY-NC-ND 4.0 | C | 1 |
| 26 | Convex Optimization: Algorithms and Complexity | Bubeck | arXiv preprint | C | 1 |
| 27 | Algebraic Topology | Hatcher | Free author PDF | C | 1 |
| 28 | Foundations of Machine Learning | Mohri et al. | CC BY-NC-ND 4.0 | C | 1 |
| 29 | An Introduction to Measure Theory | Tao | Free author PDF | C | 1 |
| 30 | Complex Analysis | Ahlfors | All Rights Reserved | C | 1 |
| 31 | Mathematical Analysis | Apostol | All Rights Reserved | C | 1 |
| 32 | Analysis & Geometry of Markov Diffusion Operators | Bakry/Gentil/Ledoux | All Rights Reserved | C | 1 |
| 33 | Convex Analysis and Monotone Operator Theory | Bauschke/Combettes | All Rights Reserved | C | 1 |
| 34 | Lectures on the Nearest Neighbor Method | Biau/Devroye | All Rights Reserved | C | 1 |
| 35 | Éléments de Mathématique | Bourbaki | All Rights Reserved | C | 1 |
| 36 | Structure and Stability of Persistence Diagrams | Chazal et al. | All Rights Reserved | C | 1 |
| 37 | Discriminants, Resultants, and Multidimensional Determinants | GKZ | All Rights Reserved | C | 1 |
| 38 | Commutative Algebra | Eisenbud | All Rights Reserved | C | 1 |
| 39 | Partial Differential Equations | Evans | All Rights Reserved | C | 1 |
| 40 | Intro to Probability Theory and Its Applications | Feller | All Rights Reserved | C | 1 |
| 41 | Real Analysis | Folland | All Rights Reserved | C | 1 |
| 42 | Algebraic Geometry | Hartshorne | All Rights Reserved | C | 1 |
| 43 | Tropical Algebraic Geometry | Itenberg/Mikhalkin/Shustin | All Rights Reserved | C | 1 |
| 44 | Introductory Functional Analysis | Kreyszig | All Rights Reserved | C | 1 |
| 45 | Algebra | Lang | All Rights Reserved | C | 1 |
| 46 | Introduction to Smooth Manifolds | Lee | All Rights Reserved | C | 1 |
| 47 | A Wavelet Tour of Signal Processing | Mallat | All Rights Reserved | C | 1 |
| 48 | Model Theory: An Introduction | Marker | All Rights Reserved | C | 1 |
| 49 | Topology | Munkres | All Rights Reserved | C | 1 |
| 50 | Methods of Modern Mathematical Physics, Vol. 1 | Reed/Simon | All Rights Reserved | C | 1 |
| 51 | Convex Analysis | Rockafellar | All Rights Reserved | C | 1 |
| 52 | Variational Analysis | Rockafellar/Wets | All Rights Reserved | C | 1 |
| 53 | Functional Analysis | Rudin | All Rights Reserved | C | 1 |
| 54 | Principles of Mathematical Analysis | Rudin | All Rights Reserved | C | 1 |
| 55 | Real and Complex Analysis | Rudin | All Rights Reserved | C | 1 |
| 56 | Calculus | Spivak | All Rights Reserved | C | 1 |
| 57 | Multidimensional Diffusion Processes | Stroock/Varadhan | All Rights Reserved | C | 1 |
| 58 | Analysis II | Tao | All Rights Reserved | C | 1 |
| 59 | Introduction to Nonparametric Estimation | Tsybakov | All Rights Reserved | C | 1 |
| 60 | Topics in Optimal Transportation | Villani | All Rights Reserved | C | 1 |
| 61 | Hodge Theory and Complex Algebraic Geometry | Voisin | All Rights Reserved | C | 1 |
| 62 | Buildings | Garrett | CC BY 3.0 | C | 1 |
| 63 | Spectral Methods for Data Science | Chen et al. | CC BY 4.0 | C | 1 |

### Notes for Legal Review

1. **MIT OCW sources (Part A & B)**: All 23 sources are CC BY-NC-SA 4.0. Our use (extracting mathematical statements for formalization) should be compatible, but legal should confirm whether derivative works in Lean 4 fall under "ShareAlike" obligations.

2. **Open Access / CC sources (Part C, #24–29)**: Six sources with permissive licenses. CC BY-NC-ND sources (#25, #28) prohibit derivatives — legal should assess whether a formal statement in Lean constitutes a "derivative work" of the informal statement.

3. **All Rights Reserved sources (Part C, #30–61)**: 32 sources with traditional copyright. Mathematical theorems themselves are not copyrightable, but the specific textual formulations may be. Legal should assess whether our use (paraphrasing theorem statements for formalization) constitutes fair use.

4. **Sources without URLs** (#35 Bourbaki, #45 Lang, #51 Rockafellar, #56 Spivak, #57 Stroock/Varadhan, #43 Itenberg): ISBNs are provided in `books/list.md`.

5. **Local-only sources** (#62, #63): Licensed under CC BY 3.0 (Garrett) and CC BY 4.0 (Chen et al.) respectively.
