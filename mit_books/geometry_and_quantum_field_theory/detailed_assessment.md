Lemma 2.1 (Gaussian integral):
included
Mathlib contains Gaussian integral results in Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean and related files (FourierTransform.lean). These files establish the integral of exp(-b*x^2) over the reals and its multidimensional generalizations, including complex Gaussian integrals. The core identity for the Gaussian integral with a linear term in the exponent is covered by these results. Additionally, Mathlib/Probability/Distributions/Gaussian/CharFun.lean treats Gaussian distributions. The statement in the book, giving the value of the oscillatory Gaussian integral with a linear term, is a standard form that is covered (or can be derived from) the results in mathlib's Gaussian integral files.

Theorem 2.2:
non-included
This theorem states that the function I_g(hbar) satisfies I_g'(hbar) = I_{(1/2)Delta_B g}(hbar) and is smooth on [0, infinity). This is a specific result about the smoothness of oscillatory integrals as a function of the semiclassical parameter hbar. Searched in Mathlib/Analysis/SpecialFunctions/Gaussian/, Mathlib/Analysis/Fourier/, and Mathlib/Analysis/Distribution/ but found no equivalent statement. This is a specialized result in semiclassical analysis not formalized in mathlib.

Lemma 2.3:
non-included
This lemma states the continuity of the function I_g(hbar) defined as a normalized oscillatory integral. This is a technical lemma used in the proof of Theorem 2.2, specific to the semiclassical analysis context. Searched in Mathlib/Analysis/SpecialFunctions/Gaussian/ and Mathlib/MeasureTheory/Integral/ but found no equivalent. This is too specialized for current mathlib coverage.

Lemma 2.4:
non-included
This lemma states that multiplying the integrand by a linear function ell produces a factor of i*hbar times a directional derivative. This is a specific identity for oscillatory integrals related to integration by parts in the Gaussian measure context. Searched in Mathlib/Analysis/SpecialFunctions/Gaussian/ and Mathlib/MeasureTheory/Integral/ but found no such result. Not in mathlib.

Theorem 2.6 (Steepest descent formula):
non-included
The steepest descent (Laplace) method gives asymptotic expansions of integrals of the form int g(x) e^{-f(x)/hbar} dx as hbar -> 0. Searched for "steepestDescent", "steepest_descent", "laplace_method", "LaplaceMethod" in the entire mathlib directory and found no results. Asymptotic analysis of this type is not yet formalized in mathlib.

Theorem 2.8 (Stationary phase formula):
non-included
The stationary phase formula gives asymptotic expansions of oscillatory integrals int g(x) e^{if(x)/hbar} dx. Searched for "stationaryPhase", "stationary_phase", "StationaryPhase" throughout mathlib and found no results. This is a fundamental result in semiclassical/microlocal analysis that has not been formalized in mathlib.

Lemma 2.10 (Riemann lemma):
non-included
This is a version of the Riemann-Lebesgue lemma for oscillatory integrals, stating rapid decay of such integrals when the phase has no critical points. While mathlib has some Fourier analysis results in Mathlib/Analysis/Fourier/, the specific form of the Riemann-Lebesgue lemma with quantitative bounds in terms of the number of derivatives (as stated here) was not found. Searched for "RiemannLebesgue", "riemann_lebesgue" and found no exact match for this oscillatory integral version.

Theorem 2.16 (Multidimensional steepest descent formula):
non-included
This is the multidimensional generalization of the steepest descent formula. As noted above, no steepest descent or Laplace method results exist in mathlib. Searched the same terms and confirmed absence.

Theorem 2.17 (Multidimensional stationary phase formula):
non-included
The multidimensional stationary phase formula. As with the one-dimensional case, no stationary phase results are formalized in mathlib.

Theorem 2.18 (Separation of variables):
non-included
This states that near a non-degenerate critical point, a smooth function can be written in coordinates where it separates into a quadratic form plus higher order terms in some variables. This is closely related to the Morse lemma. Searched for "Morse", "morse_lemma", "MorseLemma" and found only unrelated files (Snowflaking.lean, ContDiffHolder). The Morse lemma and its generalizations are not in mathlib.

Corollary 2.19 (Morse lemma):
non-included
The Morse lemma states that near a non-degenerate critical point, a smooth function can be written as a sum of squares in appropriate coordinates. This is a fundamental result in differential topology. Searched for "Morse", "morse_lemma" and confirmed it is not in mathlib. The files found (Snowflaking.lean, ContDiffHolder) are unrelated to the Morse lemma.

Lemma 2.21:
non-included
This lemma states that oscillatory integrals are O(hbar^infinity) when the phase function has no critical points on the support of the amplitude. This is a non-stationary phase estimate. As with the stationary phase formula itself, this is not in mathlib.

Theorem 3.1 (Wick's theorem):
non-included
Wick's theorem expresses the moments of a Gaussian distribution as a sum over matchings (pairings). Searched for "wick", "Wick" throughout mathlib and found only unrelated files (Condensed/Basic.lean, LinearMapCompletion.lean, GelfandNaimarkSegal.lean). While mathlib has Gaussian integral computations, the combinatorial Wick theorem (expressing higher moments via pairings) is not formalized.

Theorem 3.11:
non-included
This theorem states that the logarithm of the partition function is given by a sum over connected Feynman diagrams. This is a fundamental result in perturbative quantum field theory relating the partition function to connected graphs. Searched for "Feynman", "feynman", "connected.*diagram" and found no relevant results. This is a physics/combinatorics result not in mathlib.

Corollary 3.14 (Cayley's formula):
non-included
Cayley's formula states that the number of labeled trees on n vertices is n^{n-2}. Searched for "Cayley.*tree", "cayleyTree", "labeled.*tree", "numLabeled" and found no results. While mathlib has Cayley-Hamilton theorem (Mathlib/LinearAlgebra/Matrix/Charpoly/), Cayley's tree formula is not formalized. Also searched in Mathlib/Combinatorics/ but found no tree-counting results.

Theorem 3.20:
non-included
This theorem gives the effective action as a sum over 1-particle irreducible (1PI) Feynman diagrams. This is a standard result in perturbative QFT. No Feynman diagram or effective action formalism exists in mathlib.

Lemma 3.21:
non-included
This graph-theoretic lemma states that any connected graph can be uniquely decomposed as a tree of 1-particle irreducible subgraphs connected by bridges. Searched for "bridge" and "1PI" in mathlib's graph theory files but found no such decomposition result. This is a specialized graph theory result used in QFT.

Theorem 4.4:
non-included
This theorem establishes the existence of a large-N limit for the logarithm of the partition function of a random matrix model, expressed via ballot numbers and Catalan-type combinatorics. While mathlib has Catalan numbers (Mathlib/Combinatorics/Enumerative/Catalan.lean), it does not contain random matrix theory or large-N limits. Searched for "matrixIntegral", "random_matrix", "largeN" and found nothing relevant.

Theorem 4.8:
non-included
Similar to Theorem 4.4 but for a more general matrix model. The same assessment applies: random matrix theory is not in mathlib.

Theorem 4.10 (Harer-Zagier):
non-included
The Harer-Zagier theorem gives a formula for the orbifold Euler characteristic of the moduli space of curves of genus g, relating it to Bernoulli numbers and values of the Riemann zeta function. While mathlib has Bernoulli numbers (Mathlib/NumberTheory/Bernoulli.lean) and the Riemann zeta function (Mathlib/NumberTheory/LSeries/RiemannZeta.lean), the moduli space of curves and its Euler characteristic are not formalized. Searched for "EulerCharacteristic", "Harer", "Zagier", "moduliSpace" and found nothing.

Theorem 4.12 (Wigner's semicircle law):
non-included
Wigner's semicircle law states that the empirical eigenvalue distribution of a random symmetric matrix converges to the semicircle distribution. Searched for "Wigner", "semicircle_law", "SemicircleLaw" and found no results. Random matrix theory is not covered in mathlib.

Theorem 4.13 (Properties of Hermite polynomials):
non-included
This theorem states several properties of Hermite polynomials: exponential generating function, differential equation, orthogonality, completeness in L^2(R), and integral formulas. Mathlib defines Hermite polynomials in Mathlib/RingTheory/Polynomial/Hermite/Basic.lean with basic algebraic properties (recursion, coefficients, degree, monicity) and Mathlib/RingTheory/Polynomial/Hermite/Gaussian.lean connects them to derivatives of Gaussians. However, the analytic properties stated in Theorem 4.13 -- the exponential generating function identity, the orthogonality with respect to the Gaussian weight, completeness in L^2, and the specific integral formulas -- are not established in mathlib. The mathlib treatment is purely algebraic/polynomial-theoretic and does not include the measure-theoretic orthogonality or L^2 completeness.

Theorem 5.8 (Mumford):
non-included
Mumford's theorem on the proper discontinuity of the mapping class group action on the space of filling arc systems. This is a result in the topology of moduli spaces of Riemann surfaces. Searched for "moduliSpace", "mappingClassGroup", "arcSystem", "Mumford" and found nothing. This area of geometric topology is not in mathlib.

Lemma 5.12:
non-included
A technical lemma about refining systems of curves to obtain filling arc systems on surfaces. This belongs to the combinatorial topology of surfaces, which is not formalized in mathlib.

Lemma 5.15:
non-included
A lemma about sequences satisfying recurrences related to the Euler characteristic of moduli spaces of curves. This is specific to the combinatorial study of moduli spaces and is not in mathlib.

Theorem 6.2 (BIPZ, 1978):
non-included
The BIPZ theorem gives a matrix integral representation for the generating function of planar diagrams. This is a foundational result in random matrix theory. No matrix model or planar diagram results exist in mathlib.

Proposition 6.3 (Steepest descent principle for matrix integrals):
non-included
This states that the leading asymptotics of a matrix integral as N -> infinity is determined by the saddle point. This is the matrix analog of the steepest descent method, which is not in mathlib (neither the scalar nor the matrix version).

Proposition 6.4:
non-included
This states the convergence of the empirical eigenvalue distribution to a continuous density supported on a finite interval. This is a result in random matrix theory not covered by mathlib.

Proposition 7.8 (Wick's theorem for quantum mechanics):
non-included
This is Wick's theorem for the correlation functions of the quantum harmonic oscillator, expressing n-point functions as sums over pairings of 2-point functions. As noted for Theorem 3.1, Wick's theorem is not in mathlib.

Proposition 7.14:
non-included
This states that Minkowskian correlation functions are obtained from Euclidean ones by Wick rotation t_j -> it_j. This is a foundational result in quantum mechanics/QFT relating Euclidean and Lorentzian formulations. No Wick rotation or related concepts exist in mathlib.

Proposition 7.20:
non-included
This identifies the generating function W(J) of connected Green's functions as the Legendre transform of the effective action. Searched for "Legendre.*transform", "legendreTransform" and found no results in mathlib. The Legendre transform as used in physics/convex analysis is not formalized in mathlib in this context.

Proposition 7.23:
non-included
This proposition relates the Fourier transform of position-space Feynman amplitudes to momentum-space amplitudes. This is a standard result in perturbative quantum field theory not covered by mathlib.

Proposition 8.3:
non-included
This states the equivalence between the Euler-Lagrange equations of motion and Hamilton's equations dq_i/dt = dH/dp_i, dp_i/dt = -dH/dq_i. Searched for "Hamilton.*equation", "hamiltonian" (case-insensitive) and found only Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, which is about Hamiltonian paths in graphs, not Hamiltonian mechanics. Also checked Mathlib/LinearAlgebra/SymplecticGroup.lean which defines the symplectic group but not Hamiltonian mechanics. Hamilton's equations of classical mechanics are not in mathlib.

Theorem 8.4 (von Neumann spectral theorem):
non-included
The spectral theorem for bounded self-adjoint operators, stating realization as multiplication operators on L^2. Mathlib has extensive work on the continuous functional calculus in Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/ (52+ files) and matrix spectral theory in Mathlib/Analysis/Matrix/Spectrum.lean. However, the specific form of the spectral theorem stated here -- the existence of a measure space realization where a self-adjoint operator becomes multiplication by a measurable function -- requires the spectral measure construction, which is not yet fully formalized in mathlib. The continuous functional calculus provides a partial version but does not give the full measure-space realization.

Theorem 8.5 (Spectral theorem for unbounded operators):
non-included
Extension of the spectral theorem to unbounded self-adjoint operators. Since even the bounded version is not fully in mathlib in the measure-theoretic form, the unbounded extension is certainly not present. Searched in Mathlib/Analysis/CStarAlgebra/ and found no treatment of unbounded operators.

Corollary 8.6:
non-included
This corollary constructs the strongly continuous 1-parameter unitary group U(t) = e^{iAt} from a self-adjoint operator, which is essentially Stone's theorem. Searched for "Stone", "unitaryGroup", "one_parameter" and found no formalization of Stone's theorem in mathlib. The theory of strongly continuous semigroups/groups of operators is not in mathlib.

Lemma 8.19:
non-included
This lemma states the existence and uniqueness of a positive ground state eigenvector for a Schrodinger operator with a potential growing at infinity. This is a result from spectral theory of Schrodinger operators (related to the Perron-Frobenius theorem for positivity-preserving semigroups). No Schrodinger operator theory exists in mathlib.

Theorem 8.22 (Feynman-Kac formula):
non-included
The Feynman-Kac formula relates Hamiltonian correlation functions to path integral correlation functions. Searched for "FeynmanKac", "feynman_kac" and found no results. This is a deep result connecting operator theory and stochastic processes that is not in mathlib.

Theorem 8.23 (Feynman-Kac formula on the circle):
non-included
The periodic version of the Feynman-Kac formula. As with Theorem 8.22, this is not in mathlib.

Theorem 8.30 (WKB formal solutions):
non-included
This theorem establishes the existence and uniqueness of WKB-type formal solutions to a system of ODEs involving the semiclassical parameter hbar. Searched for "WKB", "wkb" and found no results. WKB approximation theory is not in mathlib.

Theorem 8.31 (Local WKB approximation):
non-included
This gives the WKB approximation for the Schrodinger equation. As noted above, WKB theory is not in mathlib.

Proposition 8.32 (Weyl law):
non-included
The Weyl law gives the asymptotic counting function for eigenvalues of a Schrodinger operator: nu(E) ~ A(E)/hbar as hbar -> 0. Searched for "WeylLaw", "weyl_law" and found no results. Spectral asymptotics are not covered in mathlib.

Proposition 9.2 (Classification of supermanifolds):
non-included
This states that the functors S and S_* between vector bundles on manifolds and supermanifolds are inverse to each other (on isomorphism classes). Searched for "supermanifold", "Supermanifold" and found no results. Mathlib has no theory of supermanifolds. The only "superalgebra" reference found was in Mathlib/LinearAlgebra/CliffordAlgebra/Grading.lean, which defines a Z/2-grading on the Clifford algebra but not supermanifolds.

Proposition 9.5 (Properties of Berezinian):
non-included
Properties of the Berezinian (superdeterminant): multiplicativity, derivative formula, and exponential formula. Searched for "Berezinian", "berezinian", "superdeterminant" and found no results. The Berezinian is not defined in mathlib.

Theorem 9.7 (Berezin's change of variable formula):
non-included
The change of variables formula for integration on supermanifolds, involving the Berezinian of the Jacobian. As supermanifolds and the Berezinian are not in mathlib, this result is certainly not present.

Proposition 9.9:
non-included
The Gaussian integral in an odd (fermionic) vector space equals the Pfaffian. Searched for "Pfaffian", "pfaffian" and found no results. The Pfaffian is not defined in mathlib, nor is integration over odd/fermionic spaces.

Proposition 9.10:
non-included
The fermionic Gaussian integral equals (-1)^{n(n-1)/2} det A. As the Pfaffian and Berezin integration are not in mathlib, this is not present.

Theorem 9.11 (Wick formula in the odd case):
non-included
The fermionic Wick theorem expressing moments of the fermionic Gaussian in terms of Pfaffians. Neither the Pfaffian nor fermionic integration is in mathlib.

Theorem 10.6 (Feynman-Kac formula for free fermionic theory):
non-included
The Feynman-Kac formula adapted to free fermionic field theory, using the supertrace. No Feynman-Kac formula or fermionic field theory exists in mathlib.

Lemma 11.6:
non-included
For dim V >= 2, a unitary representation of the Poincare group is positive energy iff its spectrum lies in the forward light cone. This is a result in relativistic quantum field theory. Searched for "Wightman", "wightman", "Poincare.*group", "lightCone" and found no results. Representation theory of the Poincare group is not in mathlib.

Theorem 11.8 (Spin-statistics theorem):
non-included
The spin-statistics theorem relating the spin of a quantum field to its bosonic/fermionic nature. This is a deep result in axiomatic quantum field theory. Not in mathlib.

Proposition 11.10:
non-included
Existence and uniqueness of Wightman functions (tempered distributions) encoding the correlation functions of a Wightman QFT. Wightman axioms and distributions are not formalized in mathlib.

Proposition 11.12:
non-included
Properties of Wightman functions: Poincare invariance, positive energy spectral condition, hermiticity, space locality, and positivity. Not in mathlib.

Theorem 11.13 (Wightman reconstruction theorem):
non-included
States that a set of distributions satisfying the Wightman axioms determines a Wightman QFT. This is a fundamental result in axiomatic QFT not formalized in mathlib.

Proposition 11.17 (Operator product expansion):
non-included
Existence of the operator product expansion for composite operators in the free scalar boson theory. This is a result in quantum field theory not in mathlib.

Lemma 12.1 (Feynman's famous formula):
non-included
The identity for the simplex integral: int_{Delta_n} dy / (a_1 y_1 + ... + a_n y_n)^n = 1/(a_1 ... a_n). While this is a purely analytic/combinatorial identity, it was not found in mathlib. Searched in Mathlib/MeasureTheory/Integral/, Mathlib/Analysis/SpecialFunctions/ and found no equivalent. This specific identity involving integration over the simplex is not formalized.

Proposition 12.6:
non-included
Classification of superficially divergent Feynman diagrams by renormalizability type. This is a result in perturbative renormalization theory, which is entirely absent from mathlib.

Proposition 12.7:
non-included
Classification of the most general renormalizable Lagrangian for a scalar bosonic field by spacetime dimension. This is a standard result in quantum field theory / renormalization theory, not in mathlib.

Proposition 13.2:
non-included
Wick's formula for the correlation functions of the holomorphic current a(z) in the free scalar conformal field theory. Conformal field theory is not formalized in mathlib.

Theorem 13.6 (Virasoro action on Fock space):
non-included
Construction of an action of the Virasoro algebra on the Fock space via Sugawara-type formulas. Searched for "Virasoro", "virasoro", "WittAlgebra" and found no results. The Virasoro algebra and its representations are not in mathlib. While mathlib has Lie algebras (Mathlib/Algebra/Lie/) and Kac-Moody structures, the Virasoro algebra specifically is not defined.

Theorem 13.9 (Operator product expansion in CFT):
non-included
Existence and uniqueness of the operator product expansion for local operators in the free scalar conformal field theory. As conformal field theory and vertex algebras are not in mathlib, this result is not present.
