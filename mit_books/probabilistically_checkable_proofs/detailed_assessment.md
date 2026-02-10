# Detailed Assessment: Mathlib Coverage for Probabilistically Checkable Proofs (MIT 18.408)

## Statement 1: Theorem 1.1 (PCP Theorem -- gap-3-SAT formulation)
**Status**: non-included
Searched in Mathlib/Computability/. The PCP theorem is a fundamental result in computational complexity theory. Mathlib's computability library covers Turing machines, DFAs, NFAs, and basic computability concepts but has no formalization of complexity classes like NP, promise problems, or gap problems. No equivalent found.

## Statement 2: Theorem 1.2 (Hastad's Theorem for 3Lin_2)
**Status**: non-included
Searched in Mathlib/Computability/ and Mathlib/Combinatorics/Optimization/. Hastad's inapproximability result for 3Lin_2 requires the PCP theorem and Fourier analysis on Boolean functions. While Mathlib has a ValuedCSP framework in Mathlib/Combinatorics/Optimization/ValuedCSP.lean, it defines VCSP templates but does not formalize NP-hardness of approximation results. No equivalent found.

## Statement 3: Theorem 1.3 (Vertex Cover Hardness of Approximation)
**Status**: non-included
Searched in Mathlib/Combinatorics/SimpleGraph/VertexCover.lean. Mathlib defines IsVertexCover and vertexCoverNum for simple graphs, providing the combinatorial definition. However, no computational complexity or hardness of approximation results are formalized. No equivalent found.

## Statement 4: Theorem 1.4 (Independent Set Hardness of Approximation)
**Status**: non-included
Searched in Mathlib/Combinatorics/SimpleGraph/. Mathlib has clique definitions (Clique.lean) and some graph partition concepts but no formalization of independent set hardness results or gap problems. No equivalent found.

## Statement 5: Definition 1.1 (Linear Error Correcting Code)
**Status**: non-included
Searched across Mathlib for error correcting code formalizations. Found no dedicated coding theory library. Mathlib has general subspace and linear algebra concepts but no specific formalization of error correcting codes as subspaces of F_q^n with distance/rate parameters. No equivalent found.

## Statement 6: Claim 1.2 (Distance of Linear Code)
**Status**: non-included
No coding theory formalization in Mathlib. The claim that d(C) = min_{x != 0} |supp(x)| for linear codes is a basic coding theory fact not present. No equivalent found.

## Statement 7: Claim 1.4 (Polynomial Characterization via Linear Equations)
**Status**: non-included
Searched in Mathlib for polynomial interpolation results. While Mathlib has polynomial algebra (Mathlib/Algebra/Polynomial/), the specific characterization of degree-d polynomials via linear equations on d+2 evaluation points is not formalized in this form. No equivalent found.

## Statement 8: Claim 1.5 (Polynomial Characterization via Arithmetic Progressions)
**Status**: non-included
A specific result about finite differences of polynomials evaluated on arithmetic progressions. Not formalized in Mathlib. No equivalent found.

## Statement 9: Theorem 1.6 (Local Testability of Reed-Solomon Code)
**Status**: non-included
No coding theory or local testing formalization in Mathlib. No equivalent found.

## Statement 10: Claim 1.7 (Plurality Agreement in RS Testing)
**Status**: non-included
Part of the proof of local testability of Reed-Solomon codes. No equivalent in Mathlib. No equivalent found.

## Statement 11: Claim 1.8 (Degree Bound from Testing)
**Status**: non-included
Part of the proof of local testability of Reed-Solomon codes. No equivalent in Mathlib. No equivalent found.

## Statement 12: Theorem 1.9 (Local Testability of Hadamard Code)
**Status**: non-included
Searched for Hadamard-related content. Found Mathlib/LinearAlgebra/Matrix/Hadamard.lean (Hadamard product of matrices) and Mathlib/Analysis/Complex/Hadamard.lean (Hadamard three-circles theorem). Neither relates to the Hadamard code or its local testability. No equivalent found.

## Statement 13: Claim 1.10 (Self-Correction Consistency for Hadamard)
**Status**: non-included
Part of the local testability proof for Hadamard codes. No equivalent in Mathlib. No equivalent found.

## Statement 14: Theorem (Schwartz-Zippel Lemma)
**Status**: non-included
Searched across Mathlib for polynomial identity testing results. While Mathlib has extensive polynomial algebra, the Schwartz-Zippel lemma (bounding Pr[f(x)=0] for random x over a finite field) is not formalized. No equivalent found.

## Statement 15: Theorem (Sum-Check Protocol Completeness and Soundness)
**Status**: non-included
The sum-check protocol is an interactive proof system. Mathlib has no formalization of interactive proofs, protocols, or verifier-prover interactions. No equivalent found.

## Statement 16: Theorem (Label Cover NP-hardness -- basic PCP)
**Status**: non-included
No formalization of label cover problems or their NP-hardness in Mathlib. No equivalent found.

## Statement 17: Theorem 1.2 (Label Cover with Vanishing Soundness)
**Status**: non-included
Requires the PCP theorem and parallel repetition. No formalization in Mathlib. No equivalent found.

## Statement 18: Theorem 1.3 (Parallel Repetition Theorem)
**Status**: non-included
A deep result in theoretical computer science (Raz's theorem). No formalization of 2-prover games or parallel repetition in Mathlib. No equivalent found.

## Statement 19: Definition 2.1 (Shannon Entropy)
**Status**: non-included
Searched in Mathlib/Probability/ and Mathlib/Analysis/SpecialFunctions/. Found Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean which deals with the binary entropy function h(p) = -p*log(p) - (1-p)*log(1-p), and Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean. However, the general Shannon entropy H(X) for discrete random variables is not formalized as a standalone definition. No equivalent found.

## Statement 20: Claim 2.2 (Near-Maximum Entropy Implies Near-Uniformity)
**Status**: non-included
Uses Pinsker's inequality to relate entropy deficit to statistical distance. Neither Pinsker's inequality nor this consequence is formalized in Mathlib. No equivalent found.

## Statement 21: Definition 2.3 (Conditional Shannon Entropy given an Event)
**Status**: non-included
No formalization of conditional Shannon entropy in Mathlib. No equivalent found.

## Statement 22: Definition 2.4 (Conditional Shannon Entropy given a Random Variable)
**Status**: non-included
No formalization of conditional Shannon entropy in Mathlib. No equivalent found.

## Statement 23: Claim 2.5 (Conditioning Reduces Entropy)
**Status**: non-included
A basic information theory inequality. Not formalized in Mathlib. No equivalent found.

## Statement 24: Claim 2.6 (Shannon Entropy Sub-additivity)
**Status**: non-included
H(X,Y) <= H(X) + H(Y) is a fundamental property of Shannon entropy. Not formalized in Mathlib. No equivalent found.

## Statement 25: Claim 2.7 (Entropy Decrease by Conditioning on an Event)
**Status**: non-included
Bounds entropy loss when conditioning on an event. Not formalized in Mathlib. No equivalent found.

## Statement 26: Theorem 1.1 (Greedy Set Cover Approximation)
**Status**: non-included
A classic algorithmic result. Mathlib has no formalization of approximation algorithms or their guarantees. No equivalent found.

## Statement 27: Definition 1.2 ((l,m,n) Set System)
**Status**: non-included
A combinatorial gadget definition specific to hardness of approximation for set cover. Not formalized in Mathlib. No equivalent found.

## Statement 28: Lemma 1.3 (Existence of (l,m,n) Set Systems)
**Status**: non-included
Construction of set systems using the Boolean hypercube. Not formalized in Mathlib. No equivalent found.

## Statement 29: Theorem 2.1 (Label Cover Hardness with Bi-regularity)
**Status**: non-included
A strengthening of the PCP theorem. No equivalent in Mathlib. No equivalent found.

## Statement 30: Theorem 2.2 (Hardness of Weighted Set Cover)
**Status**: non-included
NP-hardness result for weighted set cover approximation. No equivalent in Mathlib. No equivalent found.

## Statement 31: Claim 2.3 (Edge Satisfiability from Set Cover)
**Status**: non-included
A structural claim used in the reduction from label cover to set cover. No equivalent in Mathlib. No equivalent found.

## Statement 32: Theorem 1.1 (3Lin_q Hardness of Approximation)
**Status**: non-included
Generalization of Hastad's theorem to arbitrary finite fields. No equivalent in Mathlib. No equivalent found.

## Statement 33: Theorem 1.2 (3SAT Hardness of Approximation)
**Status**: non-included
Optimal inapproximability of 3SAT (the 7/8 threshold). No equivalent in Mathlib. No equivalent found.

## Statement 34: Definition 1.4 (The Long Code)
**Status**: non-included
A specific error correcting code used in PCP constructions. Not formalized in Mathlib. No equivalent found.

## Statement 35: Definition 2.1 (Inner Product on Boolean Functions)
**Status**: non-included
Searched in Mathlib/Analysis/InnerProductSpace/. Mathlib has extensive inner product space theory but not the specific L_2({-1,1}^n) inner product for Boolean Fourier analysis. No equivalent found.

## Statement 36: Lemma 2.2 (Characters Form Orthonormal Basis)
**Status**: non-included
Searched in Mathlib/Analysis/InnerProductSpace/Orthonormal.lean and Mathlib/Analysis/Fourier/. Mathlib has Fourier analysis on additive circles (AddCircle) but not discrete Fourier analysis on the Boolean hypercube {-1,1}^n. The orthonormality of characters chi_alpha is not formalized in this combinatorial setting. No equivalent found.

## Statement 37: Theorem 2.3 (Linearity Test in List Decoding Regime)
**Status**: non-included
A result connecting the BLR linearity test to Fourier coefficients. No equivalent in Mathlib. No equivalent found.

## Statement 38: Lemma 2.4 (Bound on Large Fourier Coefficients)
**Status**: non-included
A corollary of Parseval's equality for Boolean functions. Not formalized in the Boolean hypercube setting in Mathlib. No equivalent found.

## Statement 39: Theorem 2.5 (Noisy Linearity Test)
**Status**: non-included
Analysis of the noisy linearity test incorporating noise sensitivity. No equivalent in Mathlib. No equivalent found.

## Statement 40: Theorem 3.1 (Combined Long-Code Test Analysis)
**Status**: non-included
Core technical result in the long-code framework for hardness of approximation. No equivalent in Mathlib. No equivalent found.

## Statement 41: Theorem 4.1 (Label Cover Hardness -- restated for 3Lin reduction)
**Status**: non-included
Restatement of the PCP theorem for the 3Lin reduction. No equivalent in Mathlib. No equivalent found.

## Statement 42: Lemma 4.2 (Completeness of 3Lin Reduction)
**Status**: non-included
Part of the proof of Theorem 1.1 (3Lin hardness). No equivalent in Mathlib. No equivalent found.

## Statement 43: Lemma 4.3 (Soundness of 3Lin Reduction)
**Status**: non-included
Part of the proof of Theorem 1.1 (3Lin hardness). No equivalent in Mathlib. No equivalent found.

## Statement 44: Definition 2.1 (d-to-1 Games)
**Status**: non-included
A specialization of label cover with d-to-1 constraints. No equivalent in Mathlib. No equivalent found.

## Statement 45: Definition 2.2 (Unique Games)
**Status**: non-included
The 1-to-1 games (unique games) problem. No equivalent in Mathlib. No equivalent found.

## Statement 46: Conjecture 2.3 (d-to-1 Games Conjecture)
**Status**: non-included
An open conjecture in complexity theory. No equivalent in Mathlib. No equivalent found.

## Statement 47: Conjecture 2.4 (Unique Games Conjecture)
**Status**: non-included
A major open conjecture in TCS. No equivalent in Mathlib. No equivalent found.

## Statement 48: Theorem 3.1 (1/2-Approximation for Max-Cut)
**Status**: non-included
Searched in Mathlib/Combinatorics/Optimization/ValuedCSP.lean. The file defines HasMaxCutProperty for binary functions but does not prove approximation guarantees. No equivalent found.

## Statement 49: Theorem 3.2 (Goemans-Williamson Algorithm for Max-Cut)
**Status**: non-included
Requires semi-definite programming and random hyperplane rounding. Mathlib has no SDP formalization. No equivalent found.

## Statement 50: Theorem 3.3 (GW Algorithm for Almost Bipartite Graphs)
**Status**: non-included
A refined analysis of the Goemans-Williamson algorithm. No equivalent in Mathlib. No equivalent found.

## Statement 51: Definition 1.1 (Influence of a Coordinate)
**Status**: non-included
A key definition from analysis of Boolean functions. Not formalized in Mathlib. No equivalent found.

## Statement 52: Definition 1.2 (tau-Small Influences)
**Status**: non-included
A notion from analysis of Boolean functions. Not formalized in Mathlib. No equivalent found.

## Statement 53: Theorem 1.3 (Majority is Stablest -- Boolean version)
**Status**: non-included
A deep result in analysis of Boolean functions (Mossel-O'Donnell-Oleszkiewicz). Not formalized in Mathlib. No equivalent found.

## Statement 54: Definition 1.4 (rho-Correlated Distribution)
**Status**: non-included
The noise operator on the Boolean hypercube. Not formalized in Mathlib. No equivalent found.

## Statement 55: Definition 1.5 (Stability of a Function)
**Status**: non-included
Noise stability of Boolean functions. Not formalized in Mathlib. No equivalent found.

## Statement 56: Claim 1.6 (Fourier Formula for Influences)
**Status**: non-included
Relates influences to Fourier coefficients: I_i[f] = sum_{alpha: alpha_i=1} f-hat(alpha)^2. Not formalized in Mathlib for the Boolean hypercube setting. No equivalent found.

## Statement 57: Definition 1.7 (Low-Degree Influence)
**Status**: non-included
A refinement of the influence notion restricting to low-degree Fourier coefficients. Not formalized in Mathlib. No equivalent found.

## Statement 58: Lemma 1.8 (Sum of Low-Degree Influences)
**Status**: non-included
Bounds the total low-degree influence and the number of influential coordinates. Not formalized in Mathlib. No equivalent found.

## Statement 59: Theorem 1.9 (Majority is Stablest -- bounded functions, positive rho)
**Status**: non-included
Extension of the Majority is Stablest theorem to bounded (non-Boolean) functions with low-degree influences. Not formalized in Mathlib. No equivalent found.

## Statement 60: Theorem 1.10 (Majority is Stablest -- bounded functions, negative rho)
**Status**: non-included
The negative correlation version of Majority is Stablest. Not formalized in Mathlib. No equivalent found.

## Statement 61: Definition 2.1 (Unique Games Instance -- restated for Max-Cut reduction)
**Status**: non-included
Restatement of the Unique Games definition. No equivalent in Mathlib. No equivalent found.

## Statement 62: Conjecture 2.2 (Unique Games Conjecture -- restated for Max-Cut reduction)
**Status**: non-included
Restatement of UGC. No equivalent in Mathlib. No equivalent found.

## Statement 63: Lemma 2.3 (Max-Cut Reduction Analysis)
**Status**: non-included
The completeness and soundness analysis of the UG-to-Max-Cut reduction. No equivalent in Mathlib. No equivalent found.

## Statement 64: Claim 2.4 (Fourier Coefficients of Averaged Functions)
**Status**: non-included
A technical claim relating Fourier coefficients of averaged functions to those of component functions via constraint maps. No equivalent in Mathlib. No equivalent found.

## Statement 65: Lemma 2.5 (Label Propagation via Low-Degree Influence)
**Status**: non-included
Shows that high low-degree influence propagates through constraint edges with constant probability. No equivalent in Mathlib. No equivalent found.

## Statement 66: Theorem (Hamming Bound for Error Correcting Codes)
**Status**: non-included
R + d/2 + o(1) <= 1 for codes. A basic coding theory bound not formalized in Mathlib. No equivalent found.

## Statement 67: Theorem (Reed-Solomon Code Parameters)
**Status**: non-included
Searched in Mathlib for Reed-Solomon or polynomial code formalizations. Found no coding theory library. The fundamental theorem of algebra (roots bound) is in Mathlib (Mathlib/Algebra/Polynomial/) but not applied to Reed-Solomon code parameters. No equivalent found.

## Statement 68: Theorem (Composed Code Parameters)
**Status**: non-included
Code concatenation/composition preserving rate and distance. Not formalized in Mathlib. No equivalent found.

## Statement 69: Theorem (Parseval's Equality for Boolean Fourier Analysis)
**Status**: non-included
Searched in Mathlib/Analysis/Fourier/. Mathlib has Fourier transform theory for AddCircle and related structures, but not Parseval's equality in the specific Boolean hypercube {-1,1}^n setting used in analysis of Boolean functions. No equivalent found.

## Statement 70: Theorem (Chain Rule for Shannon Entropy)
**Status**: non-included
H(X,Y) = H(X) + H(Y|X). No Shannon entropy formalization in Mathlib. No equivalent found.

## Statement 71: Definition 1.3 (Local Tester for Error Correcting Code)
**Status**: non-included
Defines local testability (h queries, completeness 1, soundness delta for epsilon-far words). No equivalent in Mathlib. No equivalent found.

## Statement 72: Theorem (Entropy Upper Bound)
**Status**: non-included
H(X) <= log(|X|) with equality iff X is uniform. Follows from Jensen's inequality. While Jensen's inequality is formalized in Mathlib (Mathlib/Analysis/Normed/Module/Convex.lean area), the entropy application is not. No equivalent found.

## Statement 73: Theorem (Fourier Coefficient Formula)
**Status**: non-included
G-hat(alpha) = <G, chi_alpha>. Part of basic discrete Fourier analysis on {-1,1}^n, not formalized in Mathlib. No equivalent found.

## Statement 74: Theorem (Product of Characters)
**Status**: non-included
chi_alpha * chi_{alpha'} = chi_{alpha + alpha'} on the Boolean hypercube. While character theory exists in Mathlib for groups, this specific Boolean hypercube version is not formalized. No equivalent found.

## Statement 75: Theorem (Reed-Muller Code Parameters)
**Status**: non-included
No coding theory formalization in Mathlib for Reed-Muller codes. No equivalent found.

## Statement 76: Theorem (Cook-Levin Theorem)
**Status**: non-included
Searched in Mathlib/Computability/. While Mathlib has Turing machine definitions (TuringMachine.lean, Halting.lean, Reduce.lean), the Cook-Levin theorem itself (NP-hardness of SAT) is not formalized. The Reduce.lean file has general reducibility concepts but not the specific Cook-Levin reduction. No equivalent found.

## Statement 77: Theorem (Stability of Majority Function)
**Status**: non-included
The noise stability of majority being 1 - (2/pi)Arccos(rho) + o(1). Not formalized in Mathlib. No equivalent found.

## Statement 78: Theorem (Influence of Majority Function)
**Status**: non-included
The influence of each coordinate in majority being ~ sqrt(2/(pi*n)). Not formalized in Mathlib. No equivalent found.

## Statement 79: Theorem (Max-Cut as Constraint Satisfaction Problem)
**Status**: non-included
The integer program formulation of Max-Cut. Mathlib/Combinatorics/Optimization/ValuedCSP.lean has a general VCSP framework and mentions Max-Cut property, but does not formalize the integer program or SDP relaxation. No equivalent found.

## Statement 80: Theorem (Goemans-Williamson Rounding Analysis)
**Status**: non-included
The alpha_GW ~ 0.878 approximation ratio analysis. Requires SDP theory not present in Mathlib. No equivalent found.

## Statement 81: Theorem (Pinsker's Inequality -- cited)
**Status**: non-included
SD(P,Q) <= sqrt(KL(P||Q)/2). While Mathlib has statistical distance concepts in probability, Pinsker's inequality is not formalized. No equivalent found.

## Statement 82: Theorem (Arithmetic Expression for Stability via Cut)
**Status**: non-included
Pr[f(x) != f(y)] = (1/2)(1 - Stab_{-1+epsilon}(f)). Not formalized in Mathlib. No equivalent found.

## Statement 83: Remark 2.6 (Dimension-Free Property of the Reduction)
**Status**: non-included
A methodological observation about the UG-to-Max-Cut reduction. Not a formalizable mathematical statement in the traditional sense; it is a meta-observation about the reduction's parameters. No equivalent found.
