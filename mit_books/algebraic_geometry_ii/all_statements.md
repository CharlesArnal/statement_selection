# All Mathematical Statements from 18.726 Algebraic Geometry II (MIT, Spring 2009)

## Statement 1 (Basis Lemma)
Any sheaf on X specified on a basis B extends uniquely to a sheaf on X. Similarly, any morphism between two sheaves on X specified on B extends to a morphism of sheaves on X. In other words, the restriction functor from sheaves on X to sheaves on X specified on B is an equivalence of categories.

## Statement 2 (Gluing Corollary)
Let I be an index set and let {U_i} be an open cover of X. Suppose we are given sheaves F_i on U_i and isomorphisms theta_{ij}: F_i|_{U_i cap U_j} -> F_j|_{U_i cap U_j} satisfying the cocycle condition. Then there exist a sheaf F on X and isomorphisms theta_i: F|_{U_i} -> F_i compatible with the theta_{ij}. Moreover, F is unique up to unique isomorphism.

## Statement 3 (Stalks and Morphisms Lemma)
Let phi: F_1 -> F_2 be a morphism of sheaves. Consider: (a) For each x in X, phi_x is injective/surjective/bijective. (b) For each open U, phi(U) is injective/surjective/bijective. Then (b) implies (a) in all cases, while (a) implies (b) in the injective and bijective cases.

## Statement 4 (Sheafification Proposition)
The functor F -> F^+ from presheaves on X to sheaves on X, and the forgetful functor from sheaves on X to presheaves on X, form an adjoint pair.

## Statement 5 (Inverse and Direct Image Adjunction)
The functors f^{-1} and f_* form an adjoint pair.

## Statement 6 (Five Lemma)
Let a commuting diagram with exact rows A_0 -> A_1 -> A_2 -> A_3 -> A_4 and B_0 -> B_1 -> B_2 -> B_3 -> B_4 with vertical maps f_0,...,f_4 be given. (a) If f_1 and f_3 are monomorphisms and f_0 is an epimorphism, then f_2 is a monomorphism. (b) If f_1 and f_3 are epimorphisms and f_4 is a monomorphism, then f_2 is an epimorphism.

## Statement 7 (Snake Lemma)
Given a commuting diagram with exact rows 0 -> A_1 -> A_2 -> A_3 -> 0 and 0 -> B_1 -> B_2 -> B_3 -> 0 with vertical maps f_1, f_2, f_3, there exists a canonical connecting homomorphism delta: ker(f_3) -> coker(f_1) such that 0 -> ker(f_1) -> ker(f_2) -> ker(f_3) -> coker(f_1) -> coker(f_2) -> coker(f_3) -> 0 is exact.

## Statement 8 (Short Five Lemma)
In a commuting diagram with short exact rows, f_2 is a monomorphism/epimorphism if and only if f_1 and f_3 both are.

## Statement 9 (Adjoint Functors and Exactness)
If the covariant functors f^*: C_1 -> C_2 and f_*: C_2 -> C_1 form an adjoint pair, then f^* is right exact and f_* is left exact.

## Statement 10 (Stalks of Kernel/Image/Cokernel)
For x in X, ker(phi)_x = ker(phi_x), im(phi)_x = im(phi_x), and coker(phi)_x = coker(phi_x).

## Statement 11 (Global Sections Left Exact)
The global sections functor Gamma(., X) is left exact.

## Statement 12 (Quasicompactness of Distinguished Opens)
Any distinguished open D(f) of Spec(R) is quasicompact for the Zariski topology. In particular, Spec(R) = D(1) itself is quasicompact.

## Statement 13 (Distinguished Open Inclusion Lemma)
For f, g in R, D(f) is contained in D(g) if and only if some power of f is a multiple of g.

## Statement 14 (Fundamental Theorem of Affine Schemes, Part 1)
The presheaf O_X on X = Spec R specified on D satisfies the sheaf axiom for coverings of distinguished opens by other distinguished opens. Consequently, it extends uniquely to a sheaf of rings on Spec R.

## Statement 15 (Fundamental Theorem of Affine Schemes, Part 2)
Let M be an R-module. Define a presheaf tilde{M} on X specified on D by D(f) -> M tensor_R R_f. Then tilde{M} satisfies the sheaf axiom for coverings of distinguished opens by other distinguished opens. Consequently, it extends uniquely to a sheaf on Spec R.

## Statement 16 (Morphisms of Affine Schemes)
For A and B two rings, the set of morphisms Spec(A) -> Spec(B) of locally ringed spaces corresponds bijectively to the set of ring homomorphisms B -> A.

## Statement 17 (Gamma-Spec Adjunction)
For any locally ringed space (X, O_X) and any ring A, there is a natural bijection Hom_{LocRingSp}((X,O_X), Spec(A)) -> Hom_{Ring}(A, Gamma(X, O_X)). In other words, the functors Spec and Gamma form an adjoint pair.

## Statement 18 (Fibre Product Open Subscheme Lemma)
Suppose f: Y -> X and g: Z -> X are morphisms such that the fibre product Y x_X Z exists. Let T, U, V be open subsets with f(U), g(V) contained in T. Then pi_1^{-1}(U) cap pi_2^{-1}(V), viewed as a subscheme of Y x_X Z, is a fibre product of U -> T and V -> T.

## Statement 19 (Existence of Fibre Products)
All fibre products exist in the category of schemes.

## Statement 20 (Quasicoherent Sheaves on Affine Schemes)
Let F be a quasicoherent sheaf of O_X-modules for X = Spec(R), and put M = Gamma(X, F). Then the natural homomorphism tilde{M} -> F of O_X-modules is an isomorphism. In other words, the category of quasicoherent O_X-modules on Spec(R) is equivalent to the category of R-modules.

## Statement 21 (Separatedness and Diagonal)
A morphism f: Y -> X is separated if and only if the image of the diagonal Delta: Y -> Y x_X Y is a closed subset of Y x_X Y.

## Statement 22 (Affine Intersection Theorem)
Let X be a separated scheme. Then the intersection of any two open affine subschemes of X is again affine.

## Statement 23 (Separatedness Stable under Base Change)
Separatedness is stable under base change.

## Statement 24 (Composition of Closed Immersions)
The composition of closed immersions is a closed immersion.

## Statement 25 (Closed Immersion is Separated)
Any closed immersion is separated.

## Statement 26 (Varieties and Schemes Equivalence)
The category of abstract algebraic varieties over the algebraically closed field k is equivalent to the category of schemes which are reduced and locally of finite type over Spec(k).

## Statement 27 (Properness of Projective Space)
The morphism f: P^n_Z -> Spec Z is proper.

## Statement 28 (Closed Immersion is Proper)
Any closed immersion is proper.

## Statement 29 (Projective Morphism is Proper Corollary)
Any morphism f: X -> Y that factors as a closed immersion of X into P^n_Y followed by the projection P^n_Y -> Y is proper.

## Statement 30 (Twisting Sheaves on Proj)
Suppose S is generated by S_1 as an S_0-algebra. Then O_X(n) on Proj S are locally free of rank 1, and O_X(m) tensor O_X(n) is canonically isomorphic to O_X(m+n).

## Statement 31 (Quasicoherent Sheaves on Proj)
Suppose S is finitely generated by S_1 as an S_0-algebra. Then each quasi-coherent sheaf on Proj S can be written as tilde{M} for a canonical choice of M.

## Statement 32 (Proj and Projective Space Isomorphism)
For S = A[x_0,...,x_n] with the usual grading, Proj S is canonically isomorphic to P^n_A.

## Statement 33 (Closed Immersions into Projective Space)
For n >= 1, any closed immersion into P^n_A is defined by some homogeneous ideal of A[x_0,...,x_n].

## Statement 34 (Equivalent Conditions for Projective Closed Subscheme)
For n >= 1, let I be a homogeneous ideal of S = A[x_0,...,x_n]. Several conditions characterizing when the associated closed subscheme of Proj S is empty are equivalent (related to the irrelevant ideal).

## Statement 35 (Projective iff Proper plus Very Ample)
The morphism f: Y -> X is projective if and only if f is proper and there exists a very ample sheaf relative to f.

## Statement 36 (Blowup and Locally Principal Ideal)
If f: Y -> X is the blowup defined by a finitely generated ideal sheaf I on X, then the inverse image ideal sheaf of I on Y is locally principal.

## Statement 37 (Chow's Lemma)
Let f: X -> S be a morphism of finite type. Assume S is noetherian or S is quasicompact and X has finitely many irreducible components. Then there exists a quasiprojective S-scheme X' and a projective surjective morphism X' -> X which restricts to an isomorphism over some dense open U.

## Statement 38 (Reduced Scheme Characterization)
Let X be a scheme. The following are equivalent: (a) X is reduced, (b) For every open affine Spec(R), R is reduced, (c) For each x in X, O_{X,x} is reduced.

## Statement 39 (Connected Scheme Characterization)
The scheme X is connected if and only if the idempotent elements of Gamma(X, O_X) are 0 and 1.

## Statement 40 (Irreducible Affine Scheme Characterization)
The nonempty affine scheme X = Spec(A) is irreducible if and only if the nilradical of A is a prime ideal.

## Statement 41 (Unique Generic Point)
If X is irreducible, then X has a unique generic point.

## Statement 42 (Integral Scheme Characterization)
Put X = Spec(A). The following are equivalent: (a) X is integral, (b) A is an integral domain, (c) X is connected and each local ring O_{X,x} is an integral domain.

## Statement 43 (Normal Affine Scheme Characterization)
Suppose X = Spec(A) is connected. Then X is normal if and only if A is an integral domain which is integrally closed in its field of fractions.

## Statement 44 (Existence of Normalization)
Let X be an integral scheme. Then the category of dominant morphisms tilde{X} -> X with tilde{X} normal has a final element.

## Statement 45 (Flat Module on Affine Scheme)
Let X = Spec(R) be an affine scheme, and let M be an R-module. Then M is a flat O_X-module if and only if M is a flat R-module.

## Statement 46 (Flat Morphism of Affine Schemes)
Let A -> B be a homomorphism of rings. Then Spec(B) -> Spec(A) is flat if and only if B is flat as an A-module.

## Statement 47 (Flat Locally of Finite Presentation is Universally Open)
Let f: X -> Y be a morphism which is flat and locally of finite presentation. Then f is universally open, i.e., any base change of f is an open map on topological spaces.

## Statement 48 (Generic Flatness)
Let f: Y -> X be a morphism of finite type, with X locally noetherian, and let F be a quasicoherent O_Y-module. The set of y in Y at which F is flat relative to f is an open subset.

## Statement 49 (Faithfully Flat Descent)
Let f: Y -> X be a faithfully flat, quasicompact morphism. Then the natural functor from quasicoherent O_X-modules to descent data for quasicoherent sheaves defined by f is an equivalence of categories.

## Statement 50 (Descent of Finite Type)
Let f: Y -> X be a morphism, and let g: Z -> X be a faithfully flat quasicompact morphism. Then f is of finite type if and only if the base change of f by g is of finite type.

## Statement 51 (Formally Unramified iff Omega Zero)
The morphism f is formally unramified if and only if Omega_{Y/X} = 0.

## Statement 52 (Etale iff Flat and Unramified)
If f is locally of finite presentation, then f is etale if and only if f is flat and unramified.

## Statement 53 (Smooth iff Flat and Geometrically Regular Fibres)
If f is locally of finite presentation, then f is smooth if and only if f is flat and for each x in X, the fibre f^{-1}(x) is geometrically regular over kappa(x).

## Statement 54 (DVR Characterization)
Let A be a noetherian local ring of dimension 1. Then the following are equivalent: (a) A is regular, (b) A is normal, (c) A is a discrete valuation ring.

## Statement 55 (Cartier and Weil Divisors for Locally Factorial Schemes)
Suppose X is locally factorial. Then the map from Cartier divisors to Weil divisors is an isomorphism. In particular, this holds if X is regular.

## Statement 56 (Riemann-Roch for Curves)
There exists a nonnegative integer g = g(X) with the following property. For any divisor D and any canonical divisor K, l(D) - l(K - D) = deg(D) + 1 - g.

## Statement 57 (Closed Immersion from High Degree Divisors)
For g >= 2, for any divisor D of degree at least 2g-1, the complete linear system associated to D defines a closed immersion into a projective space.

## Statement 58 (l(D) Bounds)
For any point P and any divisor D, l(D) <= l(D+P) <= l(D) + 1. Consequently, l(D) <= deg(D) + 1.

## Statement 59 (Canonical Embedding and Hyperelliptic Curves)
The canonical embedding is a closed immersion if and only if X is not hyperelliptic.

## Statement 60 (Riemann-Hurwitz Formula, Divisor Form)
For f: X -> Y a finite separable morphism of curves, K_X ~ f^* K_Y + R where R is the ramification divisor.

## Statement 61 (Riemann-Hurwitz Formula, Genus Form)
2g(X) - 2 = (deg(f))(2g(Y) - 2) + deg(R).

## Statement 62 (Finite Generation of Canonical Ring, BCHM)
Let X be a smooth projective irreducible variety over C. Then the ring direct_sum Gamma(X, omega_{X/k}^{tensor n}) is finitely generated as a C-algebra.

## Statement 63 (Universality of Effaceable Cohomological Functors)
Let T^i: C_1 -> C_2 be a cohomological functor such that T^i is effaceable for each i > 0. Then T is universal.

## Statement 64 (Acyclic Resolution Theorem)
Let T: C_1 -> C_2 be a universal cohomological functor. Given J in C_1, suppose 0 -> A^0 -> A^1 -> ... is an acyclic resolution of J. Then for each i >= 0, there is an isomorphism T^i(h^0(A)) = h^i(T^0(A)) which is functorial.

## Statement 65 (Injectives are Acyclic for Universal Functors)
Let T^i be a cohomological functor that is effaceable for i > 0. Then for any injective object I, T^i(I) = 0 for i > 0.

## Statement 66 (Derived Functors from Enough Injectives)
Assume C has enough injectives. Then the derived functor construction gives a well-defined cohomological functor, which is effaceable and hence universal.

## Statement 67 (Flat Module Characterization)
For X in Mod_R, the following are equivalent: (a) X is flat, (b) Tor_1(M, X) = 0 for all M, (c) for any injection N -> P, the map N tensor X -> P tensor X is injective.

## Statement 68 (Short Exact Sequence with Flat Term)
Let 0 -> A_1 -> A_2 -> A_3 -> 0 be exact with A_3 flat. Then for any R-module M, 0 -> M tensor A_1 -> M tensor A_2 -> M tensor A_3 -> 0 is exact.

## Statement 69 (Ab Has Enough Injectives)
The category Ab has enough injectives.

## Statement 70 (Sheaves of Modules Have Enough Injectives)
Let (X, O_X) be a ringed space. Then the category of sheaves of O_X-modules has enough injectives.

## Statement 71 (Grothendieck's Theorem on Enough Injectives)
Let C be an abelian category satisfying: (a) C has a generator, (b) C has exact filtered colimits, (c) C has arbitrary products. Then C has enough injectives.

## Statement 72 (Injective Iff Extension Property from Generator)
Under the conditions of Statement 71, an object M in C is injective if and only if for any monomorphism V -> U into the generator, every morphism V -> M extends to U -> M.

## Statement 73 (Injective Implies Flasque)
For any ringed space (X, O_X), any injective O_X-module is flasque.

## Statement 74 (Flasque Sheaves Acyclic)
Let F be a flasque sheaf of abelian groups on a topological space X. Then H^i(X, F) = 0 for all i > 0.

## Statement 75 (Singular and Sheaf Cohomology Agree)
For a locally contractible topological space X, the sheaf cohomology of X with coefficients in the constant sheaf Z_X is canonically isomorphic to the singular cohomology of X.

## Statement 76 (Homotopy Equivalence Lemma for Singular Cochains)
The restriction C^.(X) -> D^.(X) (from singular cochains to those defined on simplices in some U_i) is a homotopy equivalence.

## Statement 77 (Cech Cohomology Vanishes for Flasque Sheaves)
If F is flasque, then check{H}^i(U, F) = 0 for i > 0.

## Statement 78 (Cech Cohomology on Paracompact Spaces)
Suppose X is paracompact. Then the check{H}^i(X, F) form a cohomological functor which is effaceable, hence universal, hence canonically isomorphic to H^i(X, F).

## Statement 79 (Leray's Theorem)
If the cover U is good for F (i.e., higher cohomology vanishes on finite intersections), then check{H}^.(U, F) -> H^.(X, F) are isomorphisms.

## Statement 80 (Vanishing of Quasicoherent Cohomology on Affine Schemes)
Let X be an affine scheme and F a quasicoherent sheaf on X. Then H^i(X, F) = 0 for i > 0.

## Statement 81 (Global Sections Exact for Quasicoherent Sheaves on Affines)
Let X = Spec A be an affine scheme. Let 0 -> F_1 -> F -> F_2 -> 0 be exact with F_1 quasicoherent. Then 0 -> Gamma(X, F_1) -> Gamma(X, F) -> Gamma(X, F_2) -> 0 is exact.

## Statement 82 (Cech Cohomology for Affine Covers)
Let X be a scheme and U = {U_i} an open cover with all finite intersections affine. Then for any quasicoherent sheaf F, H^i(X, F) = check{H}^i(U, F).

## Statement 83 (Cech Cohomology on Distinguished Open Covers)
Let A be a ring, f_1,...,f_n generating the unit ideal, U the cover of Spec A by D(f_i). Then for any A-module M, check{H}^0(U, tilde{M}) = M and check{H}^i(U, tilde{M}) = 0 for i > 0.

## Statement 84 (Cartan's Theorem)
Let X be a topological space, B a basis closed under pairwise intersections, F a sheaf with check{H}^i(U, F) = 0 for all U in B and i > 0. Then check{H}^i(X, F) is naturally isomorphic to H^i(X, F).

## Statement 85 (Cech^1 Vanishing Implies Surjectivity)
Let F be a sheaf with check{H}^1(X, F) = 0. Then for any short exact sequence 0 -> F -> G -> H -> 0, the sequence 0 -> Gamma(X, F) -> Gamma(X, G) -> Gamma(X, H) -> 0 is exact.

## Statement 86 (Finitely Generated Module iff Finitely Generated Sheaf)
Let A be a ring and M an A-module. Then M is finite as an A-module if and only if the quasicoherent sheaf tilde{M} is finitely generated.

## Statement 87 (Cohomology of Closed Immersion)
Let f: Z -> X be a closed immersion and F a sheaf on Z. Then H^i(Z, F) -> H^i(X, f_*F) are canonical isomorphisms for i >= 0.

## Statement 88 (Cohomology Commutes with Direct Limits on Noetherian Spaces)
Let X be a noetherian topological space and (F_j) a direct system of abelian sheaves. Then the natural maps lim H^.(X, F_j) -> H^.(X, lim F_j) are isomorphisms.

## Statement 89 (Serre's Computation of Cohomology of Projective Space)
Let A be any ring, r >= 1, X = P^r_A, S = A[x_0,...,x_r]. (a) S -> direct_sum H^0(X, O_X(n)) is an isomorphism. (b) For 0 < i < r, H^i(X, O_X(n)) = 0. (c) H^r(X, O_X(-r-1)) = A. (d) The natural pairing H^0(X, O_X(n)) x H^r(X, O_X(-n-r-1)) -> A is a perfect pairing. (e) For i > r, H^i(X, O_X(n)) = 0.

## Statement 90 (Serre's Generation by Global Sections)
Let A be a ring, X -> P^r_A a closed immersion, F a finitely generated quasicoherent sheaf on X. Then there exists n_0 such that for all n >= n_0, F(n) is generated by finitely many global sections.

## Statement 91 (Serre's Surjection Corollary)
With notation as above, there exists a surjection from a direct sum of O(n) onto F for some n.

## Statement 92 (Serre's Finiteness Theorem)
Let A be a noetherian ring, X -> P^r_A a closed immersion, F a finitely generated quasicoherent sheaf. (a) H^i(X, F) are finitely generated A-modules. (b) There exists n_0 such that for i > 0 and n >= n_0, H^i(X, F(n)) = 0.

## Statement 93 (Euler Characteristic Additivity)
The Euler characteristic chi(X, .) is additive in short exact sequences.

## Statement 94 (Existence of Hilbert Polynomial)
There exists a polynomial P(z) in Q[z] such that chi(X, F(n)) = P(n) for all n in Z.

## Statement 95 (Flatness and Constancy of Hilbert Polynomials)
Let T be an integral noetherian scheme, X a closed subscheme of P^r_T, F a coherent sheaf. Then F is flat over T if and only if the Hilbert polynomial P_t is constant as a function of t.

## Statement 96 (Existence of Hilbert Scheme)
Fix a field k, integer r, polynomial P(z). There exists a noetherian scheme H and a closed subscheme X of P^r_H, flat with Hilbert polynomial P, universal for the Hilbert functor.

## Statement 97 (Hilbert Polynomial and Dimension/Degree)
Let P(z) be the Hilbert polynomial of a closed subscheme X of P^n_k. (a) deg(P) = dim(X). (b) For any d-dimensional plane L with dim(X cap L) = 0, the length of X cap L is d! times the leading coefficient of P.

## Statement 98 (Spectral Sequence Convergence)
If for each q the induced filtration on C_q has finitely many distinct steps, then the spectral sequence converges.

## Statement 99 (Cartan's Theorem via Spectral Sequences)
Let X be a topological space with a nice basis B, F a sheaf with check{H}^i(U, F) = 0 for all i > 0 and U in B. Then there are natural isomorphisms check{H}^i(X, F) -> H^i(X, F).

## Statement 100 (Coherent Sheaves on Noetherian Affine Schemes)
Let A be a noetherian ring, X = Spec A, V an open subset, F an O_X|_V-module. The following are equivalent: (a) F is coherent, (b) F is finitely generated and quasicoherent, (c) F = tilde{M} for some finitely generated A-module M.

## Statement 101 (Cartan's Lemma on Coherence of Analytification Pullback)
For any coherent sheaf F on P^r_C, the pullback h^*F under the analytification map is coherent.

## Statement 102 (Flatness of Analytification)
For any z in tilde{P}^r_C, the morphism O_{P^r_C, z} -> O_{tilde{P}^r_C, z} is flat. That is, the analytification map h is flat.

## Statement 103 (GAGA, Part 1: Cohomology Comparison)
For any coherent sheaf F on P^r_C, the natural morphism H^i(P^r_C, F) -> H^i(tilde{P}^r_C, h^*F) is an isomorphism for each i >= 0.

## Statement 104 (Cartan's Theorem B for Stein Manifolds)
For any nonempty subset J of {0,...,r} and any coherent sheaf F on U = intersection of tilde{X}_j, H^i(U, F) = 0 for i > 0.

## Statement 105 (Cech Computation on Analytic Projective Space)
For any coherent sheaf F on tilde{P}^r_C, sheaf cohomology can be computed using the Cech complex for the standard cover. In particular, H^i vanishes for i > r.

## Statement 106 (GAGA, Part 2: Morphism Comparison)
For F, G coherent sheaves on P^r_C, Hom(F, G) -> Hom(h^*F, h^*G) is an isomorphism.

## Statement 107 (Hom Base Change for Flat Algebras)
Let R be a noetherian ring, S a flat R-algebra. Then for any R-modules M, N, the natural map Hom_R(M,N) tensor S -> Hom_S(M tensor S, N tensor S) is a bijection.

## Statement 108 (Cartan-Serre Finiteness)
For F a coherent sheaf on tilde{P}^r_C, the spaces H^i(tilde{P}^r_C, F) are finite dimensional over C.

## Statement 109 (GAGA, Part 3: Essential Surjectivity)
Every coherent sheaf on tilde{P}^r_C is the pullback under h of a unique coherent sheaf on P^r_C.

## Statement 110 (GAGA Lemma on Local Generation)
Assume the third GAGA theorem in dimensions up to r-1. For any coherent sheaf F on tilde{P}^r_C and any z, there exists n_0 such that for n >= n_0, F(n)_z is generated by global sections.

## Statement 111 (GAGA Corollary on Uniform Generation)
Assume the third GAGA theorem in dimensions up to r-1. For any coherent sheaf F on tilde{P}^r_C, there exists n_0 such that for all n >= n_0 and all z, F(n)_z is generated by global sections.

## Statement 112 (Analytification Functor Theorem)
Let X be a scheme locally of finite type over C. The functor Y -> Hom_{LocRingSp}(Y, X) from AnSp to Set is represented by an analytic space X^{an}.

## Statement 113 (GAGA for Projective Schemes)
Let X be a closed subscheme of P^r_C. (a) H^i(X, F) -> H^i(X^{an}, h^*F) is an isomorphism. (b) Hom(F, G) -> Hom(h^*F, h^*G) is an isomorphism. (c) Every coherent sheaf on X^{an} is h^*F for a unique coherent F.

## Statement 114 (GAGA for Hodge Cohomology)
Let X be a smooth proper scheme over C. Then H^p(X, Omega^q_{X/C}) = H^p(X^{an}, Omega^q_{X^{an}}).

## Statement 115 (Grothendieck's Theorem on Finite Covers)
Let X be a smooth proper scheme over C. Then any finite covering space Y -> X^{an} corresponds to a finite etale cover of X in the category of schemes.

## Statement 116 (Profinite Completion Independence)
Let K be a number field, X a smooth proper scheme over K. Then the profinite completion of pi_1((X x_K C)^{an}) does not depend on the embedding K -> C.

## Statement 117 (Separatedness and Analytification)
Let f: X -> Y be a morphism of schemes locally of finite type over C. Then f is separated iff f^{an} is separated. In particular, X is separated iff X^{an} is Hausdorff.

## Statement 118 (Injective Restriction to Opens)
Let I be an injective O_X-module. Then for any open subset U of X, I|_U is an injective O_U-module.

## Statement 119 (Ext as Cohomological Functor)
For F an O_X-module, Ext^i(., F) and sheaf-Ext^i(., F) are cohomological functors on Mod_X^{op}.

## Statement 120 (Ext via Locally Free Resolutions)
If L_. -> F -> 0 is a locally free resolution, then sheaf-Ext^i(F, G) = h^i(Hom(L_., G)).

## Statement 121 (Coherence of Ext on Projective Space)
For coherent sheaves F, G on P^n_k, sheaf-Ext^i(F, G) is again coherent.

## Statement 122 (Ext Tensor Adjunction)
For L locally free of finite rank: Ext^i(F tensor L, G) = Ext^i(F, L^v tensor G) and sheaf-Ext^i(F tensor L, G) = sheaf-Ext^i(F, G) tensor L^v.

## Statement 123 (Serre Duality on Projective Space)
Put X = P^n_k, F coherent. (a) Hom(F, O_X(-n-1)) x H^n(X, F) -> H^n(X, O_X(-n-1)) is a perfect pairing. (b) For each i >= 0, Ext^i(F, O_X(-n-1)) -> H^{n-i}(X, F)' is a natural isomorphism.

## Statement 124 (Canonical Sheaf of Projective Space)
For X = P^n_k, the canonical sheaf omega_X is isomorphic to O_X(-n-1).

## Statement 125 (Existence of Dualizing Sheaf)
There exists a dualizing sheaf omega_X^o for X (a projective scheme over a field).

## Statement 126 (Canonical Sheaf is Dualizing for Smooth Schemes)
If X is smooth and irreducible over k, then the canonical sheaf omega_X is a dualizing sheaf.

## Statement 127 (Ext Proposition for Sheaves)
For coherent sheaves F, G on X, for q >= q_0, Ext^i_X(F, G(q)) = Gamma(X, sheaf-Ext^i_X(F, G)(q)).

## Statement 128 (Grothendieck Vanishing)
For any sheaf F of abelian groups on X, H^i(X, F) = 0 for i > dim(X).

## Statement 129 (Dualizing Sheaf for Local Complete Intersections)
Suppose X is a local complete intersection in P. Let I be the ideal sheaf. Then Ext^r_P(j_*O_X, omega_P) = omega_P tensor j_*O_X tensor (I/I^2)^v.

## Statement 130 (Cohen-Macaulay Duality Equivalence)
The following are equivalent: (a) X is equidimensional and Cohen-Macaulay. (b) theta^i: Ext^i_X(F, omega_X^o) -> H^{n-i}(X, F)' are isomorphisms for all i >= 0 and all coherent F.

## Statement 131 (Smooth Implies Full Duality)
If X is smooth over k, then theta^i is an isomorphism for all i >= 0 and all coherent F.

## Statement 132 (Cohen-Macaulay via Cohomological Vanishing)
The following are equivalent to (b): (c) For q large, H^i(X, F(-q)) = 0 for i < n, (c') For q large, H^i(X, O_X(-q)) = 0 for i < n.

## Statement 133 (Cohen-Macaulay via Ext Vanishing)
The following is equivalent to (b): (d) For all i < n, Ext^{N-i}_P(j_*O_X, omega_P) = 0.

## Statement 134 (Cohen-Macaulay via Local Ext Vanishing)
The following is equivalent to (b): (e) For each x in X, Ext^{N-i}_A(A/I, A) = 0 for all i < n where A = O_{P,x}.

## Statement 135 (Projective Dimension and Ext Vanishing)
Let A be a regular local ring, M a finitely generated A-module. The following are equivalent: (a) Ext^i(M, A) = 0 for i > n, (b) Ext^i(M, N) = 0 for all N and i > n, (c) There exists a projective resolution of M of length at most n.

## Statement 136 (Auslander-Buchsbaum Formula)
For A a regular local ring and M an A-module, pd_A(M) + depth_A(M) = dim(A).

## Statement 137 (Cohen-Macaulay via Depth)
The following is equivalent to (b): (f) For each x in X, depth_{O_{X,x}}(O_{X,x}) >= n.

## Statement 138 (Hodge Index Theorem)
Fix a projective embedding of X (smooth projective surface) with hyperplane divisor H. For any divisor D with D . H = 0, D^2 <= 0.

## Statement 139 (Nakai-Moishezon Criterion)
A divisor D on a smooth projective surface X is ample iff D^2 > 0 and D . C > 0 for all irreducible curves C.

## Statement 140 (Hirzebruch-Riemann-Roch)
Let X be a smooth proper scheme over k, F a locally free coherent sheaf. Then chi(X, F) = integral_X ch(F) . td(T_X).

## Statement 141 (Grothendieck-Riemann-Roch)
Let f: X -> Y be a proper morphism of smooth schemes over k. Then ch(f_*F) . td(T_Y) = f_*(ch(F) . td(T_X)).

## Statement 142 (Etale Cohomology Computes Betti Numbers)
Let X be a smooth proper scheme over C. Then for any prime l, the cohomology of the etale locally constant sheaf associated to Z_l computes the topological Betti numbers of X.

## Statement 143 (Riemann-Roch for Surfaces)
For X a smooth projective surface, D a divisor, K a canonical divisor: chi(X, L(D)) = (1/2)D.(D-K) + chi(X, O_X).
