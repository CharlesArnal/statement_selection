# Detailed Assessment of Mathlib Coverage for Projection Theory

## Statement 1: Theorem (Szemeredi-Trotter, 1982)
**Status**: not included
The Szemeredi-Trotter incidence theorem is a combinatorial geometry result. Mathlib does not contain incidence geometry results of this type. The closest area is Mathlib/Combinatorics/ but it lacks discrete geometry incidence bounds.

## Statement 2: Theorem (Marstrand, 1954)
**Status**: not included
Marstrand's projection theorem relates Hausdorff dimension to projections. While mathlib has Hausdorff dimension (Mathlib/Topology/MetricSpace/HausdorffDimension.lean) including Lipschitz and Holder maps preserving dimension bounds, it does not have Marstrand's projection theorem or any results about orthogonal projections and Hausdorff dimension.

## Statement 3: Theorem (Orponen-Shmerkin-Ren-Wang)
**Status**: not included
This is a very recent (2024) research result solving the exceptional set problem. Far beyond current mathlib scope.

## Statement 4: Conjecture (Projection theory over F_p)
**Status**: not included
An open conjecture in combinatorial geometry over finite fields. Not formalized.

## Statement 5: Theorem (Double counting over F_q)
**Status**: not included
A projection bound over finite fields using double counting. This is a combinatorial geometry result specific to projection theory. Not in mathlib.

## Statement 6: Theorem (Orthogonality/Fourier method over F_q)
**Status**: not included
A projection bound over finite fields using Fourier methods. While mathlib has some Fourier analysis on finite abelian groups (Mathlib/Analysis/Fourier/FiniteAbelian/), it does not have this projection-theoretic application.

## Statement 7: Lemma (Orthogonality of line indicators)
**Status**: not included
This is a specific computation about characteristic functions of lines in F_q^2. Not in mathlib.

## Statement 8: Theorem (Fourier inversion over F_q^d)
**Status**: not included
While mathlib has Fourier inversion for real-valued functions (Mathlib/Analysis/Fourier/Inversion.lean) and Pontryagin duality for finite abelian groups (Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean), the specific statement for F_q^d with the character $e(x \cdot \xi)$ formulation is not directly present. The abstract Pontryagin duality framework could be specialized to obtain this, but the specific finite field vector space version is not stated.

## Statement 9: Theorem (Plancherel over F_q^d)
**Status**: not included
While mathlib has the Plancherel theorem for L^2 functions on locally compact abelian groups (Mathlib/Analysis/Fourier/LpSpace.lean), the specific finite field version with the explicit character sum formulation is not present. The general framework could be specialized, but the specific statement is missing.

## Statement 10: Lemma (Fourier transform of affine plane indicator)
**Status**: not included
A specific computation about the Fourier transform of characteristic functions of affine planes in F_q^d. Not in mathlib.

## Statement 11: Theorem (Double Counting Real Version)
**Status**: not included
A projection counting bound for sets of unit balls in Euclidean space. Not in mathlib.

## Statement 12: Corollary (Double Counting Real with Hausdorff spacing)
**Status**: not included
Specialization of the double counting bound to Hausdorff-spaced sets. Not in mathlib.

## Statement 13: Theorem (Double counting finite field restated)
**Status**: not included
Restatement of Statement 5. Not in mathlib.

## Statement 14: Theorem (Fourier Method Finite Field restated)
**Status**: not included
Restatement of Statement 6. Not in mathlib.

## Statement 15: Corollary (Fourier method real version)
**Status**: not included
Real version of the Fourier projection bound. Not in mathlib.

## Statement 16: Conjecture (Prime field projection)
**Status**: not included
Open conjecture. Not in mathlib.

## Statement 17: Conjecture (Furstenberg, discrete version)
**Status**: not included
The Furstenberg set conjecture in discrete form. Proven in 2024 by OSRW but not in mathlib.

## Statement 18: Lemma (Main lemma in finite field, L^2 decomposition)
**Status**: not included
Specific L^2 decomposition for sums of line indicators. Not in mathlib.

## Statement 19: Lemma (Main lemma in real, L^2 decomposition)
**Status**: not included
Littlewood-Paley decomposition applied to tube functions. While mathlib has some Fourier analysis infrastructure, this specific Littlewood-Paley type estimate is not present.

## Statement 20: Lemma (Orthogonality of tube functions)
**Status**: not included
A technical orthogonality estimate for tube bump functions. Not in mathlib.

## Statement 21: Lemma (Main Lemma 2F)
**Status**: not included
L^2 bound for high-frequency part of line indicator sums. Not in mathlib.

## Statement 22: Lemma (Elementary L^2 bounds on f)
**Status**: not included
Specific L^2 estimate for Littlewood-Paley pieces of tube sums. Not in mathlib.

## Statement 23: Lemma (Main Lemma 2R)
**Status**: not included
Real analogue of the L^2 Fourier method bound. Not in mathlib.

## Statement 24: Lemma (Tube counting)
**Status**: not included
A combinatorial counting argument for tubes. Not in mathlib.

## Statement 25: Lemma (Frequency localization)
**Status**: not included
Statement about frequency-localized functions being essentially constant on appropriate balls. Not in mathlib as stated.

## Statement 26: Lemma (Tube incidence bound)
**Status**: not included
Incidence bound between tubes and balls. Not in mathlib.

## Statement 27: Theorem (Szemeredi-Trotter incidence theorem)
**Status**: not included
The Szemeredi-Trotter theorem stated as an incidence bound. Not in mathlib.

## Statement 28: Corollary (Projection bound from Szemeredi-Trotter)
**Status**: not included
Consequence of Szemeredi-Trotter for rich lines. Not in mathlib.

## Statement 29: Theorem (Linnik's theorem on squares)
**Status**: not included
Linnik's sieve-theoretic result about sets with restricted projections mod primes. Not in mathlib.

## Statement 30: Theorem (1S - Large sieve inequality version)
**Status**: not included
The large sieve inequality applied to characterize sets with small projections. Not in mathlib. Mathlib has Mathlib/NumberTheory/SelbergSieve.lean but not the large sieve inequality.

## Statement 31: Theorem (Linnik, sieve formulation)
**Status**: not included
Restatement of Linnik's theorem. Not in mathlib.

## Statement 32: Corollary (Large sieve for general sets)
**Status**: not included
General corollary of the large sieve. Not in mathlib.

## Statement 33: Corollary (Sieve bound)
**Status**: not included
A sieve-theoretic bound. Not in mathlib.

## Statement 34: Lemma (Character sum bound)
**Status**: not included
Bound using character orthogonality. While mathlib has character orthogonality (Mathlib/NumberTheory/DirichletCharacter/), this specific application is not present.

## Statement 35: Corollary (Bombieri-Vinogradov type)
**Status**: not included
The Bombieri-Vinogradov theorem or its consequences. Not in mathlib.

## Statement 36: Lemma (Dictionary: projection theory to sieve theory)
**Status**: not included
This is a conceptual correspondence, not a formal mathematical statement.

## Statement 37: Lemma (Previous projection estimates restated for sieve)
**Status**: not included
Translation of projection bounds to sieve theory language. Not in mathlib.

## Statement 38: Lemma (Sieve theory fundamental lemma)
**Status**: not included
A fundamental sieve lemma. Not in mathlib.

## Statement 39: Theorem (Linnik, sieve version restated)
**Status**: not included
Restatement of Linnik's theorem. Not in mathlib.

## Statement 40: Lemma (Dictionary: geometric to number-theoretic)
**Status**: not included
Conceptual dictionary. Not a formal statement suitable for mathlib.

## Statement 41: Theorem (Smoothing by projecting to typical direction)
**Status**: not included
A projection theorem about Fourier decay. Not in mathlib.

## Statement 42: Lemma (Dictionary: real projection to sieve)
**Status**: not included
Conceptual correspondence. Not a formal statement.

## Statement 43: Theorem (Dirichlet's theorem on primes in arithmetic progressions)
**Status**: included
Corresponds to results in mathlib_coverage/mathlib/Mathlib/NumberTheory/LSeries/PrimesInAP.lean and mathlib_coverage/mathlib/Mathlib/NumberTheory/LSeries/Dirichlet.lean. Mathlib proves that for coprime $a, q$, there are infinitely many primes congruent to $a$ mod $q$, using Dirichlet L-series methods.

## Statement 44: Theorem (Siegel-Walfisz)
**Status**: not included
The Siegel-Walfisz theorem gives quantitative error terms for primes in arithmetic progressions. Not in mathlib.

## Statement 45: Theorem (Renyi, Bombieri-Vinogradov)
**Status**: not included
The Bombieri-Vinogradov theorem on the distribution of primes in arithmetic progressions on average. Not in mathlib.

## Statement 46: Lemma (Large sieve inequality)
**Status**: not included
The large sieve inequality for Dirichlet characters. Not in mathlib.

## Statement 47: Lemma (Orthogonality of characters)
**Status**: included
The orthogonality of Dirichlet characters is available in mathlib. Corresponds to results in mathlib_coverage/mathlib/Mathlib/NumberTheory/DirichletCharacter/ and mathlib_coverage/mathlib/Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean, which establish orthogonality relations for characters of finite abelian groups.

## Statement 48: Lemma (Dual large sieve)
**Status**: not included
The dual formulation of the large sieve. Not in mathlib.

## Statement 49: Lemma (Exponential sum bound)
**Status**: not included
A bound on exponential sums over Farey fractions. Not in mathlib.

## Statement 50: Lemma (Well-spacing of fractions)
**Status**: not included
The well-spacing property of reduced fractions. While elementary, this specific statement about Farey fractions is not in mathlib.

## Statement 51: Proposition (Large sieve from exponential sums)
**Status**: not included
The derivation of the large sieve from exponential sum bounds. Not in mathlib.

## Statement 52: Theorem (Fourier method for projection theory in Euclidean space)
**Status**: not included
Application of Fourier analysis to projection bounds. Not in mathlib.

## Statement 53: Theorem (Discrete Fourier restriction)
**Status**: not included
A discrete restriction estimate. Not in mathlib.

## Statement 54: Theorem (Real projection counting bound)
**Status**: not included
Projection counting for delta-balls with controlled spacing. Not in mathlib.

## Statement 55: Lemma (Tube intersection bound)
**Status**: not included
A geometric estimate on tube intersections. Not in mathlib.

## Statement 56: Lemma (Cell decomposition lemma)
**Status**: not included
The polynomial cell decomposition lemma for line arrangements. Not in mathlib.

## Statement 57: Theorem (Borsuk-Ulam Theorem)
**Status**: not included
The Borsuk-Ulam theorem is a fundamental result in algebraic topology. Mathlib does not currently contain it.

## Statement 58: Corollary (Ham Sandwich Theorem)
**Status**: not included
The Ham Sandwich theorem, a consequence of Borsuk-Ulam. Not in mathlib.

## Statement 59: Theorem (Polynomial Ham Sandwich Theorem)
**Status**: not included
A polynomial generalization of the Ham Sandwich theorem. Not in mathlib.

## Statement 60: Lemma (Ham Sandwich theorem for finite sets)
**Status**: not included
Discrete version of the Ham Sandwich theorem. Not in mathlib.

## Statement 61: Theorem (Szemeredi-Trotter via cell decomposition)
**Status**: not included
The proof of Szemeredi-Trotter using polynomial partitioning. Not in mathlib.

## Statement 62: Theorem (Bourgain-Katz-Tao projection theorem)
**Status**: not included
A fundamental result in additive combinatorics over finite fields. Not in mathlib.

## Statement 63: Lemma (Sum-product lower bound)
**Status**: not included
The sum-product phenomenon over finite fields. Not in mathlib.

## Statement 64: Theorem (Freiman-Ruzsa)
**Status**: not included
Freiman's theorem characterizing sets with small doubling. While mathlib has Freiman homomorphisms (Mathlib/Combinatorics/Additive/FreimanHom.lean), the full Freiman-Ruzsa theorem is not present.

## Statement 65: Conjecture (Polynomial Freiman-Ruzsa)
**Status**: not included
An open conjecture (recently proved by Gowers-Green-Manners-Tao for F_2^n). Not in mathlib.

## Statement 66: Theorem (Ruzsa's triangle inequality)
**Status**: included
Corresponds to `Finset.ruzsa_triangle_inequality_div_div_div` and its variants in mathlib_coverage/mathlib/Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean. Multiple versions (multiplicative, additive, with different sign patterns) are available.

## Statement 67: Corollary (Ruzsa's covering lemma)
**Status**: included
Corresponds to the Ruzsa covering lemma in mathlib_coverage/mathlib/Mathlib/Combinatorics/Additive/RuzsaCovering.lean.

## Statement 68: Theorem (Plunnecke's inequality)
**Status**: included
Corresponds to `Finset.pluennecke_petridis_inequality_mul` and related results in mathlib_coverage/mathlib/Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean.

## Statement 69: Corollary (Plunnecke-Ruzsa iterated sumset bound)
**Status**: included
Corresponds to `Finset.pluennecke_ruzsa_inequality_pow_div_pow_mul` and variants in mathlib_coverage/mathlib/Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean.

## Statement 70: Corollary (Sumset chain bound)
**Status**: included
Follows from the Plunnecke-Ruzsa inequality in mathlib_coverage/mathlib/Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean, specifically `pluennecke_ruzsa_inequality_pow_mul`.

## Statement 71: Lemma (Contagious structure)
**Status**: not included
A structure propagation lemma for sets with small doubling. Not directly available in mathlib.

## Statement 72: Theorem (Bourgain-Katz-Tao, full version)
**Status**: not included
The full BKT sum-product theorem over prime fields. Not in mathlib.

## Statement 73: Corollary (BKT projection consequence)
**Status**: not included
Consequence of BKT for projections. Not in mathlib.

## Statement 74: Lemma (Key step in BKT proof)
**Status**: not included
Technical lemma in the BKT proof. Not in mathlib.

## Statement 75: Lemma (Double counting for sum-product)
**Status**: not included
A counting argument relating sumsets to product sets. Not in mathlib.

## Statement 76: Lemma (Sum-product from Plunnecke-Ruzsa)
**Status**: not included
Application of Plunnecke-Ruzsa to sum-product. Not in mathlib.

## Statement 77: Theorem (Main theorem - BKT projection, refined)
**Status**: not included
Refined BKT projection theorem. Not in mathlib.

## Statement 78: Corollary (Projection lower bound)
**Status**: not included
A lower bound on projection sizes. Not in mathlib.

## Statement 79: Lemma (Double Counting for BKT)
**Status**: not included
Double counting in the BKT context. Not in mathlib.

## Statement 80: Lemma (Sum-product expansion)
**Status**: not included
Polynomial sum-product expansion lemma. Not in mathlib.

## Statement 81: Theorem (BKT for general sets)
**Status**: not included
Extension of BKT to general subsets of products. Not in mathlib.

## Statement 82: Theorem (BKT via BSG)
**Status**: not included
BKT proved through the Balog-Szemeredi-Gowers route. Not in mathlib.

## Statement 83: Theorem (Szemeredi-Trotter restated as incidence bound)
**Status**: not included
Restatement of ST as point-line incidence bound. Not in mathlib.

## Statement 84: Proposition (BSG gives structured sumset)
**Status**: not included
The BSG theorem extracting structure from high additive energy. While mathlib has additive energy (Mathlib/Combinatorics/Additive/Energy.lean), the BSG theorem itself is not present.

## Statement 85: Theorem (BKT refined statement)
**Status**: not included
Refined BKT bound. Not in mathlib.

## Statement 86: Theorem (BSG variant)
**Status**: not included
A variant of BSG for asymmetric energy bounds. Not in mathlib.

## Statement 87: Theorem (BKT 2 - robust version)
**Status**: not included
Robust version of BKT for large subsets. Not in mathlib.

## Statement 88: Theorem (Balog-Szemeredi-Gowers)
**Status**: not included
The BSG theorem. Mathlib has the energy definition but not the BSG theorem itself.

## Statement 89: Lemma (Graph lemma for BSG)
**Status**: not included
Graph-theoretic lemma used in BSG proof. Not in mathlib.

## Statement 90: Lemma (Key Lemma for BSG)
**Status**: not included
Key combinatorial lemma in BSG proof. Not in mathlib.

## Statement 91: Lemma (Length 2 paths)
**Status**: not included
A graph theory lemma about paths of length 2. Not in mathlib in this context.

## Statement 92: Lemma (P1 - Popularity argument)
**Status**: not included
A popularity/pigeonhole argument for bipartite graphs. Not in mathlib.

## Statement 93: Lemma (P2 - Dependent random choice)
**Status**: not included
The dependent random choice lemma. Not in mathlib.

## Statement 94: Lemma (BSG counting argument)
**Status**: not included
A counting argument in the BSG proof. Not in mathlib.

## Statement 95: Theorem (Bourgain-Katz-Tao, final version)
**Status**: not included
Final statement of BKT. Not in mathlib.

## Statement 96: Theorem (Bourgain projection theorem)
**Status**: not included
Bourgain's projection theorem for delta-discretized sets. Far beyond current mathlib scope.

## Statement 97: Lemma (Polynomial expansion, weak)
**Status**: not included
A sum-product type expansion for continuous sets. Not in mathlib.

## Statement 98: Lemma (Sum-product in continuous setting)
**Status**: not included
Sum-product phenomenon for delta-discretized sets. Not in mathlib.

## Statement 99: Theorem (Bourgain projection theorem, restated)
**Status**: not included
Restatement of Bourgain's projection theorem. Not in mathlib.

## Statement 100: Lemma (Properties of non-concentrated sets)
**Status**: not included
Properties of (delta, s, C)-sets. Not in mathlib. This is a specific concept in delta-discretized analysis.

## Statement 101: Lemma (Uniform set properties)
**Status**: not included
Properties of uniform sets at multiple scales. Not in mathlib.

## Statement 102: Lemma (Uniformization)
**Status**: not included
The uniformization lemma for extracting uniform subsets. Not in mathlib.

## Statement 103: Lemma (Polynomial expansion, strong)
**Status**: not included
Strong polynomial expansion result. Not in mathlib.

## Statement 104: Lemma (Robust polynomial expansion)
**Status**: not included
Robust expansion using BSG ideas. Not in mathlib.

## Statement 105: Lemma (||T_mu f||_L2 <= ||f||_L2)
**Status**: not included
Contraction of the convolution operator on a finite group. While mathlib has convolution on groups (Mathlib/MeasureTheory/Group/Convolution.lean), this specific operator norm bound for finite groups with probability measures is not stated.

## Statement 106: Proposition (L^2 mixing bound)
**Status**: not included
The mixing bound in terms of the spectral gap. Not in mathlib. Mathlib has some ergodic theory (Mathlib/Dynamics/Ergodic/) but not this specific finite group mixing result.

## Statement 107: Theorem (Selberg)
**Status**: not included
Selberg's spectral gap theorem for SL_2(F_p). While mathlib has SL_2 defined (Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean) and some representation theory (Mathlib/RepresentationTheory/), it does not have Selberg's theorem.

## Statement 108: Proposition (Isoperimetric inequality from spectral gap)
**Status**: not included
The Cheeger-type isoperimetric inequality for Cayley graphs. Not in mathlib.

## Statement 109: Proposition (Minimal representation dimension of SL_2(F_p))
**Status**: not included
The lower bound on non-trivial representations of SL_2(F_p). Mathlib has representation theory basics but not this specific result.

## Statement 110: Proposition (ell^2 bound on sigma_1)
**Status**: not included
The l^2 bound on the spectral gap using representation dimension. Not in mathlib.

## Statement 111: Corollary (sigma_1 bound for uniform measures)
**Status**: not included
Spectral gap bound for uniform measures on subsets. Not in mathlib.

## Statement 112: Corollary (Proper subgroups of SL_2(F_p) are small)
**Status**: not included
Size bound on proper subgroups of SL_2(F_p). Not in mathlib.

## Statement 113: Lemma (T_mu 1 = 1 and contraction)
**Status**: not included
Restatement of Statement 105 with T_mu 1 = 1 added. Not in mathlib.

## Statement 114: Lemma (Mixing lemma, restated)
**Status**: not included
Restatement of Statement 106. Not in mathlib.

## Statement 115: Theorem (Selberg, restated)
**Status**: not included
Restatement of Statement 107. Not in mathlib.

## Statement 116: Lemma (Expansion from spectral gap, restated)
**Status**: not included
Restatement of Statement 108. Not in mathlib.

## Statement 117: Theorem (ell^2-bound, restated)
**Status**: not included
Restatement of Statement 110. Not in mathlib.

## Statement 118: Lemma (Representation dimension of SL_2(F_p), restated)
**Status**: not included
Restatement of Statement 109 with slightly different bound (p-1)/2. Not in mathlib.

## Statement 119: Lemma (Size of B_T(Z))
**Status**: not included
Counting lattice points in balls in SL_2(R). Not in mathlib.

## Statement 120: Lemma (Symmetric convolution and L^2 norm)
**Status**: not included
Identity for symmetric measures: ||mu^K||_2^2 = mu^{2K}(I). Not in mathlib.

## Statement 121: Lemma (Gamma_p cap B_T(Z) counting)
**Status**: not included
Counting elements of the congruence subgroup in a ball. Not in mathlib.

## Statement 122: Theorem (Hedlund, 1930s)
**Status**: not included
Hedlund's theorem on unipotent orbits in SL_2(R)/SL_2(Z). Not in mathlib.

## Statement 123: Conjecture (Oppenheim)
**Status**: not included
The Oppenheim conjecture (proved by Margulis). Not in mathlib.

## Statement 124: Lemma (Projection estimate for orbits)
**Status**: not included
A specific estimate relating orbit spreading to projections. Not in mathlib.

## Statement 125: Proposition (Average projection lower bound)
**Status**: not included
Average projection of a planar set is at least sqrt of covering number. Not in mathlib.

## Statement 126: Corollary (Orbit spreading)
**Status**: not included
Iterative orbit size growth estimate. Not in mathlib.

## Statement 127: Theorem (Gan-Guo-Guth-Harris-Maldague-Wang)
**Status**: not included
A restricted projection theorem for non-degenerate curves. Very recent research result; not in mathlib.

## Statement 128: Theorem (Lindenstrauss-Mohammadi-Wang-Yang, vague)
**Status**: not included
Quantitative Ratner-type equidistribution. Very recent research; not in mathlib.

## Statement 129: Theorem (Szemeredi-Trotter, 1982, restated)
**Status**: not included
Restatement of Statement 1. Not in mathlib.

## Statement 130: Theorem (Furstenberg Conjecture, OSRW 2024)
**Status**: not included
The full Furstenberg set conjecture. Very recent (2024) result; not in mathlib.

## Statement 131: Theorem (Orponen-Shmerkin, 2021)
**Status**: not included
The epsilon-improvement theorem for projections. Not in mathlib.

## Statement 132: Theorem (Beck's theorem)
**Status**: not included
Beck's theorem in combinatorial geometry. Not in mathlib.

## Statement 133: Theorem (Continuum Beck's Theorem, OSW 2023)
**Status**: not included
The continuum analogue of Beck's theorem. Very recent result; not in mathlib.

## Statement 134: Lemma (Epsilon improvement for continuum Beck)
**Status**: not included
An epsilon improvement step in the proof of continuum Beck. Not in mathlib.

## Statement 135: Lemma (Bootstrap lemma)
**Status**: not included
A bootstrapping lemma for improving dimension bounds. Not in mathlib.

## Statement 136: Theorem (OSRW, AD regular version restated)
**Status**: not included
Restatement of the OSRW theorem for AD regular sets. Not in mathlib.

## Statement 137: Theorem (Orponen-Shmerkin, AD regular case)
**Status**: not included
The AD regular case of the Furstenberg conjecture. Not in mathlib.

## Statement 138: Lemma (Submultiplicative Lemma)
**Status**: not included
Submultiplicativity of the richness function across scales. Not in mathlib.

## Statement 139: Lemma (Submultiplicative Lemma, projective version)
**Status**: not included
Projective version of the submultiplicative lemma. Not in mathlib.

## Statement 140: Lemma (Epsilon-improvement to submultiplicative lemma)
**Status**: not included
A key technical lemma in the AD regular case proof. Not in mathlib.

## Statement 141: Theorem (ABC sum-product theorem, Orponen-Shmerkin)
**Status**: not included
A sharp sum-product estimate. Very recent research; not in mathlib.

## Statement 142: Theorem (Szemeredi-Trotter for R-rich lines)
**Status**: not included
Restatement of Szemeredi-Trotter for rich lines. Not in mathlib.

## Statement 143: Theorem (Guth-Solomon-Wang, well-spaced case)
**Status**: not included
The well-spaced case of the Furstenberg conjecture. Not in mathlib.

## Statement 144: Lemma (Two ends lemma)
**Status**: not included
A geometric lemma about tubes satisfying the two ends condition. Not in mathlib.

## Statement 145: Theorem (OSRW, full Furstenberg conjecture restated)
**Status**: not included
Restatement of the full Furstenberg conjecture. Not in mathlib.

## Statement 146: Lemma (Branching function decomposition)
**Status**: not included
A decomposition lemma for branching functions of uniform sets. Not in mathlib.
