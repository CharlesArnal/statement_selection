# Book Selection for Autoformalization Annotation

## Overview

We selected 5 MIT OCW textbooks covering diverse areas of mathematics. From each book, we chose ~10 statements (theorems, lemmas, propositions) that are:
- **Not in mathlib** (v4.27.0)
- **Fundamental**: important, well-known results rather than technical auxiliaries
- **Formalizable**: clean statements with clear hypotheses that can build on existing mathlib infrastructure

The goal is to provide annotators with ~50 statements to formalize in Lean 4. The informal context from the textbook should provide enough background for annotators to write formal statements and, ideally, proofs.

---

## Book 1: High Dimensional Statistics

**Directory**: `mit_books/high_dimensional_statistics/`
**Coverage**: 49/54 statements not in mathlib (91%)
**Area**: Probability & Statistics
**Formalizability**: Good -- mathlib has measure theory, probability spaces, random variables, expectation, L^p spaces

### Selected Statements (10)

| # | Statement | Description |
|---|-----------|-------------|
| 1 | Proposition 1.1 | **Gaussian tail bound (Mills inequality)**: For X ~ N(0,1), P(X >= t) satisfies (1/t - 1/t^3)(2pi)^{-1/2}e^{-t^2/2} <= P(X >= t) <= (1/t)(2pi)^{-1/2}e^{-t^2/2} |
| 2 | Theorem 1.13 | **Bernstein's inequality**: For independent zero-mean r.v.s with |X_i| <= M, P(|sum X_i| >= t) <= 2 exp(-t^2/(2(sum Var(X_i) + Mt/3))) |
| 3 | Theorem 1.14 | **Maximum of sub-Gaussians**: E[max_{1<=i<=n} X_i] <= sigma * sqrt(2 log n) for sub-Gaussian X_i with parameter sigma |
| 4 | Lemma 1.18 | **Epsilon-net covering bound**: The unit ball in R^d has an epsilon-net of size at most (3/epsilon)^d |
| 5 | Theorem 4.8 | **Davis-Kahan sin(theta) theorem**: Perturbation bound for eigenvectors: if A, A+E are symmetric and lambda is a simple eigenvalue of A, then sin(angle between eigenvectors) <= ||E||_op / gap |
| 6 | Lemma 5.3 | **Neyman-Pearson lemma**: The likelihood ratio test is the most powerful test for simple vs simple hypothesis testing at any given significance level |
| 7 | Proposition 5.6 | **KL divergence properties**: Non-negativity (Gibbs' inequality), additivity for product measures, and data processing inequality |
| 8 | Lemma 5.8 | **Pinsker's inequality**: TV(P,Q) <= sqrt(KL(P||Q)/2) |
| 9 | Theorem 5.10 | **Fano's inequality**: For any estimator of a parameter theta in {1,...,M}, P(theta_hat != theta) >= 1 - (I(theta;X) + log 2) / log M |
| 10 | Lemma 5.12 | **Varshamov-Gilbert lemma**: There exists a subset of {0,1}^d of size >= 2^{d/8} such that any two elements differ in at least d/4 coordinates |

---

## Book 2: Graph Theory and Additive Combinatorics

**Directory**: `mit_books/graph_theory_and_additive_combinatorics/`
**Coverage**: 265/291 statements not in mathlib (91%)
**Area**: Combinatorics & Graph Theory
**Formalizability**: Good -- mathlib has SimpleGraph, Finset, Fintype, basic combinatorics

### Selected Statements (12)

| # | Statement | Description |
|---|-----------|-------------|
| 11 | Theorem 0.1.1 | **Schur's theorem**: If the positive integers are finitely colored, there exists a monochromatic solution to x + y = z |
| 12 | Theorem 0.2.4 | **Szemeredi's theorem**: Every subset of the integers with positive upper density contains arithmetic progressions of any length |
| 13 | Theorem 1.4.2 | **Kovari-Sos-Turan theorem**: ex(n, K_{s,t}) <= (1/2)(t-1)^{1/s} n^{2-1/s} + (s-1)n/2 for s <= t |
| 14 | Theorem 1.5.1 | **Erdos-Stone-Simonovits theorem**: For any graph H with chi(H) >= 2, ex(n,H) = (1 - 1/(chi(H)-1) + o(1)) n^2/2 |
| 15 | Theorem 3.2.4 | **Expander mixing lemma**: In a d-regular graph, |e(S,T) - d|S||T|/n| <= lambda_2 sqrt(|S||T|) where lambda_2 is the second eigenvalue |
| 16 | Theorem 3.2.13 | **Cheeger's inequality**: h(G)^2/(2d) <= d - lambda_2 <= 2h(G) where h(G) is the edge expansion |
| 17 | Theorem 7.1.10 | **Freiman's theorem**: If |A+A| <= K|A| for a finite set A in Z, then A is contained in a generalized arithmetic progression of rank <= r(K) and size <= C(K)|A| |
| 18 | Theorem 7.13.6 | **Balog-Szemeredi-Gowers theorem**: If E(A,B) >= |A||B|K/|A+B| and certain density conditions hold, then there exist A' subset A, B' subset B with |A'+B'| small |
| 19 | Theorem 8.2.5 | **Szemeredi-Trotter theorem**: The number of incidences between n points and m lines in R^2 is O(n^{2/3}m^{2/3} + n + m) |
| 20 | Theorem 8.2.3 | **Crossing number inequality**: cr(G) >= e(G)^3/(64 v(G)^2) when e(G) >= 4v(G) |
| 21 | Theorem 5.5.17 | **Shearer's entropy inequality**: H(X_{A_1},...,X_{A_k}) <= sum H(X_{A_i}) / (covering number), generalized subadditivity of entropy |
| 22 | Theorem 0.2.9 | **Green-Tao theorem**: The primes contain arbitrarily long arithmetic progressions |

---

## Book 3: Number Theory II -- Class Field Theory

**Directory**: `mit_books/number_theory_ii_class_field_theory/`
**Coverage**: 108/141 statements not in mathlib (77%)
**Area**: Algebra & Number Theory
**Formalizability**: Moderate -- mathlib has Galois theory, p-adic numbers, class groups, Dedekind domains

### Selected Statements (10)

| # | Statement | Description |
|---|-----------|-------------|
| 23 | Theorem 1.1 | **Kronecker-Weber theorem**: Every abelian extension of Q is contained in a cyclotomic field Q(zeta_n) for some n |
| 24 | Theorem 1.2 | **Hasse-Minkowski theorem**: A quadratic form over Q has a nontrivial solution iff it has a nontrivial solution over Q_p for all primes p and over R |
| 25 | Theorem 9.2 | **Additive Hilbert 90**: H^1(Gal(L/K), L) = 0 for any Galois extension L/K |
| 26 | Claim 13.4 | **H_1(G,Z) = G^{ab}**: The first group homology of G with Z coefficients is the abelianization of G |
| 27 | Theorem 1.5 | **Main theorem of Local Class Field Theory**: For a local field K, there is a canonical isomorphism Gal(K^{ab}/K) = K_hat^x (profinite completion of K^x) |
| 28 | Theorem 21.6 | **Artin reciprocity**: For a number field K and an abelian extension L/K, the Artin map induces an isomorphism C_K / N_{L/K}(C_L) -> Gal(L/K) |
| 29 | Corollary 19.5 | **Brauer group of local fields**: Br(K) = Q/Z for any nonarchimedean local field K |
| 30 | Theorem 19.16 | **Cohomological Brauer group = CSA Brauer group**: The Brauer group defined via H^2(Gal, K_sep^x) is canonically isomorphic to the Brauer group defined via central simple algebras |
| 31 | Theorem 4.1 | **Quadratic Hilbert reciprocity**: The product of Hilbert symbols prod_v (a,b)_v = 1 for all a,b in Q^x |
| 32 | Theorem 3.1 | **Norm groups for tamely ramified extensions**: For a tamely ramified extension L/K of local fields, N_{L/K}(L^x) = K^x_{>= f} * (pi_K)^Z where f is the residue degree |

---

## Book 4: Introduction to Partial Differential Equations

**Directory**: `mit_books/introduction_to_partial_differential_equations/`
**Coverage**: 61/73 statements not in mathlib (84%)
**Area**: Analysis & PDE
**Formalizability**: Moderate-Hard -- mathlib has L^p spaces, Fourier analysis, smooth functions

### Selected Statements (10)

| # | Statement | Description |
|---|-----------|-------------|
| 33 | Theorem 1.1 (Ch. heat) | **Weak maximum principle for heat equation**: If u solves u_t - D*u_{xx} = 0 on [0,L]x[0,T], then max u is attained on the parabolic boundary |
| 34 | Theorem 4.1 (Ch. Laplace) | **Mean value property**: If u is harmonic on a ball B(x,r), then u(x) = average of u over the sphere S(x,r) = average of u over the ball B(x,r) |
| 35 | Theorem 5.1 | **Strong maximum principle**: If u is harmonic on a connected open set Omega and attains its maximum in Omega, then u is constant |
| 36 | Theorem 4.1 (Ch. Harnack) | **Harnack's inequality**: For a non-negative harmonic function u on B(x_0, R), sup_{B(x_0,R/2)} u <= C(n) inf_{B(x_0,R/2)} u |
| 37 | Theorem 3.1 (Ch. Poisson) | **Poisson's formula**: The solution to Delta u = 0 on the ball B(0,R) with boundary data g is u(x) = (R^2-|x|^2)/(n*omega_n*R) int_{S(0,R)} g(y)/|x-y|^n dS(y) |
| 38 | Theorem 4.1 (Ch. wave) | **d'Alembert's formula**: The solution to u_tt - c^2 u_{xx} = 0 with u(x,0)=f(x), u_t(x,0)=g(x) is u(x,t) = (f(x+ct)+f(x-ct))/2 + (1/2c) int_{x-ct}^{x+ct} g(s) ds |
| 39 | Theorem 1.1 (Ch. Kirchhoff) | **Kirchhoff's formula**: Solution to 3D wave equation u_tt - c^2 Delta u = 0 expressed as a surface integral over an expanding sphere |
| 40 | Theorem 2.1 (Ch. energy) | **Energy estimates for wave equation**: E(t) := (1/2) int (u_t^2 + c^2 |nabla u|^2) dx is conserved for solutions to the wave equation |
| 41 | Theorem 1.1 (Ch. Euler-Lagrange) | **Euler-Lagrange equation**: Critical points of the functional I[u] = int L(x, u, Du) dx satisfy div(D_p L) - D_u L = 0 |
| 42 | Theorem 4.1 (Ch. Burger) | **Singularity formation for Burger's equation**: The solution to u_t + u u_x = 0 with smooth initial data u_0 develops a singularity in finite time iff min u_0'(x) < 0, and blowup time = -1/min u_0'(x) |

---

## Book 5: Algebraic Topology I

**Directory**: `mit_books/algebraic_topology_i/`
**Coverage**: 72/80 statements not in mathlib (90%)
**Area**: Topology
**Formalizability**: Moderate -- mathlib has chain complexes, exact sequences, homological algebra, simplicial sets

### Selected Statements (10)

| # | Statement | Description |
|---|-----------|-------------|
| 43 | Theorem 5.2 | **Homotopy invariance of singular homology**: If f,g: X -> Y are homotopic, then f_* = g_*: H_n(X) -> H_n(Y) |
| 44 | Theorem 6.2 | **Excision theorem**: If U subset A subset X with closure(U) subset interior(A), then inclusion induces isomorphism H_n(X\U, A\U) -> H_n(X,A) |
| 45 | Theorem 9.4 | **Mayer-Vietoris sequence**: For X = A union B with A,B open, there is a long exact sequence ... -> H_n(A cap B) -> H_n(A) + H_n(B) -> H_n(X) -> H_{n-1}(A cap B) -> ... |
| 46 | Theorem 17.1 | **Brouwer fixed point theorem**: Every continuous map f: D^n -> D^n has a fixed point |
| 47 | Theorem 24.1 | **Universal Coefficient Theorem**: For a chain complex C of free abelian groups, 0 -> H_n(C) tensor G -> H_n(C;G) -> Tor_1(H_{n-1}(C), G) -> 0 is exact and splits |
| 48 | Theorem 25.13 | **Eilenberg-Zilber theorem**: There is a natural chain homotopy equivalence S_*(X x Y) ~ S_*(X) tensor S_*(Y) |
| 49 | Theorem 25.15 | **Kunneth theorem (for spaces)**: H_n(X x Y; k) = bigoplus_{p+q=n} H_p(X;k) tensor H_q(Y;k) when k is a field |
| 50 | Theorem 34.2 | **Poincare duality**: For a closed oriented n-manifold M, H^k(M; Z) = H_{n-k}(M; Z) (up to torsion / with appropriate coefficients) |
| 51 | Theorem 38.4 | **Alexander duality**: For a compact subspace K of S^n, H_tilde^k(K) = H_tilde_{n-k-1}(S^n \ K) |
| 52 | Theorem 38.11 | **Borsuk-Ulam theorem**: For every continuous map f: S^n -> R^n, there exists x in S^n with f(x) = f(-x) |

---

## Summary

| Book | Area | Statements Selected | Total Non-Included |
|------|------|--------------------|--------------------|
| High Dimensional Statistics | Probability & Statistics | 10 | 49 |
| Graph Theory and Additive Combinatorics | Combinatorics | 12 | 265 |
| Number Theory II: Class Field Theory | Algebra & Number Theory | 10 | 108 |
| Introduction to PDE | Analysis & PDE | 10 | 61 |
| Algebraic Topology I | Topology | 10 | 72 |
| **Total** | | **52** | **555** |

## Selection Criteria

1. **Importance**: Prioritized landmark theorems and widely-known results over technical lemmas
2. **Diversity**: Within each book, selected from different chapters/topics
3. **Formalizability**: Preferred statements with clean hypotheses that can be expressed using existing mathlib types (even if the proof requires new definitions)
4. **Independence**: Avoided selecting many results that depend on each other in a chain (annotators should be able to work on statements somewhat independently)
5. **Range of difficulty**: Mix of "should be formalizable now" (e.g., Bernstein's inequality, Brouwer fixed point) and "requires significant new definitions" (e.g., Poincare duality, Green-Tao)
