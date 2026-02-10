# All Mathematical Statements in "Tensor Categories" (Etingof et al.)

## Chapter 1: Monoidal Categories and Tensor Categories

### 1.1-1.2 Monoidal Categories

1. **Definition 1.1.1.** A monoidal category is a quintuple (C, tensor, a, 1, iota) where C is a category, tensor is a bifunctor (tensor product), a is the associativity constraint (natural isomorphism), 1 is the unit object, and iota is the unit isomorphism, satisfying the pentagon axiom.

2. **Definition 1.1.2.** A monoidal subcategory of a monoidal category is a subcategory closed under tensor product and containing the unit object.

3. **Definition 1.1.3.** The opposite monoidal category C^op is C with reversed order of tensor product and inverted associativity isomorphism.

4. **Proposition 1.2.2.** The unit constraint diagrams commute: l_{1 tensor X} composed with appropriate associators equals Id tensor l_X, and similarly for r.

5. **Proposition 1.2.3.** For any object X in C, l_{1 tensor X} = Id tensor l_X and r_{X tensor 1} = r_X tensor Id.

6. **Proposition 1.2.4.** The unit object in a monoidal category is unique up to a unique isomorphism.

7. **Proposition 1.2.7.** The monoid End(1) of endomorphisms of the unit object of a monoidal category is commutative.

8. **Definition 1.2.6.** A monoidal category (equivalent definition) is a sextuple (C, tensor, a, 1, l, r) satisfying the pentagon axiom and triangle axiom.

### 1.4-1.5 Monoidal Functors

9. **Definition 1.4.1.** A monoidal functor from C to C' is a pair (F, J) where F is a functor and J is a natural isomorphism F(X) tensor' F(Y) -> F(X tensor Y) satisfying the monoidal structure axiom.

10. **Proposition 1.4.3.** For any monoidal functor (F, J), the unit constraint diagrams commute.

11. **Definition 1.4.5.** A monoidal functor (complete definition) is a triple (F, J, phi) satisfying the monoidal structure axiom and the unit constraints.

12. **Definition 1.5.1.** A morphism of monoidal functors eta: (F1, J1) -> (F2, J2) is a natural transformation compatible with J.

### 1.6-1.7 Examples and Classification

13. **Proposition 1.6.4.** The functor F: A-bimod -> End(C) defines an equivalence between monoidal categories A-bimod and End_re(C) (right exact endofunctors).

14. **Proposition 1.7.1.** (i) Monoidal isomorphisms between monoidal functors on C_G^omega form a torsor over H^1(G, k*). (ii) Monoidal functors C_{G1}^{omega1} -> C_{G2}^{omega2} correspond to pairs (f, mu) where f is a group homomorphism and mu is a cochain. (iii) Monoidal equivalence classes of C_G^omega are parametrized by H^3(G, k*)/Out(G).

### 1.8-1.9 Strictness and Coherence

15. **Theorem 1.8.5.** (MacLane's Strictness Theorem) Any monoidal category is monoidally equivalent to a strict monoidal category.

16. **Theorem 1.9.1.** (MacLane's Coherence Theorem) Let X_1,...,X_n be objects in C. Any two isomorphisms P_1 -> P_2 between parenthesized products, obtained by composing associativity and unit isomorphisms, are equal.

### 1.10-1.11 Duals and Rigidity

17. **Definition 1.10.1.** A right dual of an object X is an object X* with evaluation ev: X* tensor X -> 1 and coevaluation coev: 1 -> X tensor X* satisfying the zig-zag identities.

18. **Definition 1.10.2.** A left dual of X is an object *X with evaluation ev': X tensor *X -> 1 and coevaluation coev': 1 -> *X tensor X satisfying dual zig-zag identities.

19. **Proposition 1.10.4.** If X has a right (resp. left) dual, then it is unique up to a unique isomorphism.

20. **Proposition 1.10.7.** (i) Taking right duals defines a contravariant functor. (ii) (X tensor Y)* = Y* tensor X*. (iii) Similar for left duals.

21. **Proposition 1.10.9.** (i) If V has a right dual V* then Hom(U tensor V, W) = Hom(U, W tensor V*) (adjunction). (ii) If V has a left dual *V then Hom(V tensor U, W) = Hom(U, *V tensor W).

22. **Definition 1.10.11.** A monoidal category C is rigid if every object has a right dual and a left dual.

23. **Definition 1.11.1.** An object X in C is invertible if ev_X and coev_X are isomorphisms.

24. **Proposition 1.11.3.** Let X be invertible. Then (i) X* = *X; (ii) ev and coev for left duals are also isomorphisms; (iii) V tensor X is a monoidal autoequivalence of C.

### 1.12-1.13 Tensor Categories

25. **Definition 1.12.1.** A k-linear abelian category is locally finite if Hom spaces are finite dimensional, every object has finite length, and there are finitely many simples.

26. **Proposition 1.12.2.** (Schur's Lemma) In a locally finite abelian category, Hom(X,Y) = 0 for non-isomorphic simples, and Hom(X,X) = k for any simple X.

27. **Definition 1.12.3.** A multitensor category is a locally finite k-linear abelian rigid monoidal category with bilinear tensor product. A tensor category additionally requires End(1) = k.

28. **Proposition 1.13.1.** In a multitensor category, the tensor product bifunctor is exact in both variables.

29. **Definition 1.13.3.** A multiring category is a locally finite k-linear abelian monoidal category with biexact tensor product. A ring category additionally requires End(1) = k.

30. **Corollary 1.13.4.** In a multiring category, Im(f1 tensor f2) = Im(f1) tensor Im(f2).

31. **Proposition 1.13.5.** In a multiring category with right duals, the right dualization functor is exact.

32. **Proposition 1.13.6.** If P is projective in a multiring category and X has a right dual, then P tensor X is projective.

33. **Corollary 1.13.7.** In a multiring category with right duals, 1 is projective if and only if C is semisimple.

### 1.14-1.16 Quasi-tensor Functors and Grothendieck Rings

34. **Definition 1.14.1.** A quasi-tensor functor is an exact faithful functor F: C -> D with a natural isomorphism J: F(.) tensor F(.) -> F(. tensor .) (not necessarily satisfying the monoidal axiom). A tensor functor is one where J is a monoidal structure.

35. **Theorem 1.15.1.** In any multiring category, End(1) is a semisimple algebra, isomorphic to a direct sum of copies of k.

36. **Proposition 1.15.5.** A multiring category decomposes as C = direct sum of C_ij where C_ij = 1_i tensor C tensor 1_j, and tensor product maps C_ij x C_jk -> C_ik.

37. **Theorem 1.15.8.** (i) In a ring category with right duals, the unit object 1 is simple. (ii) In a multiring category with right duals, the unit object is a direct sum of pairwise non-isomorphic simple objects.

38. **Lemma 1.16.1.** The multiplication on Gr(C) (Grothendieck ring) is associative.

39. **Proposition 1.16.2.** A quasi-tensor functor F: C -> D defines a homomorphism of unital rings [F]: Gr(C) -> Gr(D).

### 1.18-1.19 Finite Categories and Fiber Functors

40. **Definition 1.18.1.** A k-linear abelian category C is finite if it is equivalent to A-mod for some finite dimensional k-algebra A.

41. **Definition 1.18.2.** Equivalent characterization: C is finite if (i) it has finite dimensional Hom spaces, (ii) every object has finite length, (iii) C has enough projectives, (iv) there are finitely many simples.

42. **Proposition 1.18.3.** There is a canonical isomorphism End(F1) tensor End(F2) = End(F1 tensor F2) for exact functors on a finite abelian category.

43. **Definition 1.19.1.** A quasi-fiber functor on C is an exact faithful functor F: C -> Vec with F(1) = k equipped with an isomorphism J. A fiber functor additionally requires J to be monoidal.

### 1.20-1.22 Coalgebras, Bialgebras, Hopf Algebras

44. **Definition 1.20.1.** A coalgebra over k is a vector space C with comultiplication Delta: C -> C tensor C and counit epsilon: C -> k satisfying coassociativity and counit axioms.

45. **Definition 1.20.2.** A left comodule over C is a vector space M with a coaction map pi: M -> C tensor M satisfying the comodule axioms.

46. **Theorem 1.21.1.** If C is a finite abelian monoidal category with fiber functor F, then H = End(F) is a coalgebra with comultiplication and counit, and it is a bialgebra.

47. **Definition 1.21.2.** A bialgebra is an algebra H with comultiplication Delta and counit epsilon such that Delta and epsilon are algebra homomorphisms.

48. **Theorem 1.21.3.** (Reconstruction for bialgebras) The assignments (C,F) -> H = End(F) and H -> (Rep(H), Forget) are mutually inverse bijections between finite tensor categories with fiber functors and finite dimensional bialgebras.

49. **Proposition 1.22.1.** (Antipode axiom) mu(S tensor Id) Delta = mu(Id tensor S) Delta = i epsilon.

50. **Definition 1.22.2.** An antipode on a bialgebra H is a linear map S: H -> H satisfying the antipode axiom.

51. **Proposition 1.22.4.** An antipode on a bialgebra is unique if it exists.

52. **Proposition 1.22.5.** If S is an antipode on H, then S is an antihomomorphism of algebras and coalgebras.

53. **Corollary 1.22.6.** If H is a bialgebra with antipode, then Rep(H) has right duals. If S is invertible, Rep(H) also has left duals.

54. **Definition 1.22.9.** A Hopf algebra is a bialgebra with an invertible antipode.

55. **Theorem 1.22.11.** (Reconstruction for Hopf algebras) Mutually inverse bijections between finite tensor categories with fiber functor (up to monoidal equivalence) and finite dimensional Hopf algebras (up to isomorphism).

56. **Proposition 1.22.15.** If H is a finite dimensional bialgebra with antipode S, then S is invertible, so H is a Hopf algebra.

### 1.23 Reconstruction Theory (General)

57. **Theorem 1.23.1.** (General reconstruction) If C is a k-linear abelian category with exact faithful functor F to Vec, then F defines an equivalence between C and finite dimensional right comodules over Coend(F).

58. **Theorem 1.23.2.** Mutually inverse bijections between k-linear abelian categories with exact faithful functor to Vec and coalgebras over k.

### 1.24-1.26 Quantum Groups

59. **Definition 1.24.2.** An element x of a bialgebra is primitive if Delta(x) = x tensor 1 + 1 tensor x.

60. **Definition 1.24.6.** A skew-primitive element of type (h,g) satisfies Delta(x) = h tensor x + x tensor g.

61. **Definition 1.25.1.** The quantum group U_q(sl_2) is generated by E, F, K with relations KEK^{-1} = q^2 E, KFK^{-1} = q^{-2} F, [E,F] = (K - K^{-1})/(q - q^{-1}).

62. **Theorem 1.25.2.** U_q(sl_2) has a unique Hopf algebra structure with Delta(E) = E tensor 1 + K tensor E, etc.

63. **Definition 1.26.2.** The quantum group U_q(g) for a semisimple Lie algebra g, with generators E_i, F_i, K_i and q-Serre relations.

64. **Theorem 1.26.3.** U_q(g) has a unique Hopf algebra structure.

### 1.27 Extensions and the Ext Group

65. **Proposition 1.27.1.** The space Prim_{h,g}(C)/k(h-g) is naturally isomorphic to Ext^1(g,h) for 1-dimensional comodules.

66. **Theorem 1.27.4.** (Ext^1(1,1) = 0 in char 0) If k has characteristic 0 and C is a finite ring category with simple unit, then Ext^1(1,1) = 0.

67. **Corollary 1.27.8.** If H is a finite dimensional commutative Hopf algebra over an algebraically closed field of characteristic 0, then H = Fun(G,k) for a unique finite group G.

### 1.28-1.29 Pointed Categories and Coradical Filtration

68. **Definition 1.28.1.** A coalgebra C is pointed if all simple comodules are 1-dimensional.

69. **Definition 1.28.3.** A tensor category C is pointed if every simple object is invertible.

70. **Definition 1.29.1.** The coradical filtration C_0 subset C_1 subset ... of a coalgebra.

71. **Proposition 1.29.4.** C is cosemisimple iff C_0 = C_1.

72. **Proposition 1.29.6.** If f: C -> D is a coalgebra homomorphism injective on C_1, then f is injective.

### 1.30-1.31 Chevalley Property

73. **Theorem 1.30.1.** (Chevalley's Theorem) Over a field of characteristic zero, the tensor product of two simple finite dimensional representations of any group or Lie algebra is semisimple.

74. **Lemma 1.30.2.** If V is a completely reducible representation of an algebraic group G, then G is reductive.

75. **Definition 1.31.1.** A tensor category C has the Chevalley property if its semisimple subcategory C_0 is a tensor subcategory.

76. **Proposition 1.31.2.** A pointed tensor category has the Chevalley property.

77. **Proposition 1.31.3.** In a tensor category with the Chevalley property, the coradical filtration is a filtration of tensor categories.

78. **Corollary 1.31.5.** In a pointed Hopf algebra, the coradical filtration is a Hopf algebra filtration.

### 1.32-1.33 Cartier-Kostant Theorem

79. **Proposition 1.32.3.** A pointed Hopf algebra is generated by grouplike and skew-primitive elements iff H-comod is tensor-generated by objects of length 2.

80. **Theorem 1.33.1.** (Cartier-Kostant Theorem) Any cocommutative Hopf algebra over an algebraically closed field of characteristic zero is of the form k[G] semidirect U(g).

81. **Lemma 1.33.2.** If u in SV tensor SV is symmetric and satisfies the cocycle equation, then u is a coboundary.

### 1.34-1.36 Quasi-Bialgebras, Twisting, Reconstruction

82. **Definition 1.34.1.** A normalized quasi-fiber functor satisfies J_{1X} = J_{X1} = Id.

83. **Proposition 1.34.4.** The associator Phi of a quasi-bialgebra satisfies the 3-cocycle condition and normalization conditions.

84. **Definition 1.34.5.** A quasi-bialgebra is an algebra H with coproduct, counit, and invertible associator Phi satisfying the identities of Proposition 1.34.4.

85. **Definition 1.34.6.** A twist J for a quasi-bialgebra defines a new quasi-bialgebra H^J.

86. **Proposition 1.34.7.** If a finite k-linear abelian monoidal category admits a quasi-fiber functor, then this functor is unique up to twisting.

87. **Theorem 1.34.8.** (Reconstruction for quasi-bialgebras) Mutually inverse bijections between finite abelian monoidal categories with quasi-fiber functor and finite dimensional quasi-bialgebras.

88. **Definition 1.35.2.** An antipode on a quasi-bialgebra is a triple (S, alpha, beta).

89. **Theorem 1.35.6.** (Reconstruction for quasi-Hopf) Mutually inverse bijections between finite tensor categories with quasi-fiber functor and finite dimensional quasi-Hopf algebras.

90. **Definition 1.36.1.** A bialgebra twist J satisfies Phi^J = 1.

91. **Proposition 1.36.4.** For a finite dimensional bialgebra H, gauge equivalence classes of bialgebra twists biject with fiber functors on Rep(H) up to isomorphism.

92. **Proposition 1.36.5.** Fiber functors on Vec_G up to isomorphism biject with H^2(G, k*).

### 1.37-1.39 Quantum Traces, Pivotal and Spherical Categories

93. **Proposition 1.37.1.** Properties of quantum traces: (1) Tr^L_V(a) = Tr^R_{V*}(a*); (2) additivity; (3) multiplicativity; (4) cyclicity.

94. **Proposition 1.37.3.** Quantum trace is additive on exact sequences.

95. **Definition 1.38.1.** A pivotal structure on a rigid monoidal category is an isomorphism of monoidal functors a: Id -> ?**.

96. **Definition 1.38.4.** The dimension of X with respect to a pivotal structure a is dim_a(X) = Tr(a_X).

97. **Proposition 1.38.5.** In a tensor category, the function X -> dim_a(X) is a character of the Grothendieck ring.

98. **Corollary 1.38.6.** Dimensions of objects in a pivotal finite tensor category are algebraic integers.

99. **Definition 1.39.1.** A spherical structure is a pivotal structure with dim_a(V) = dim_a(V*) for all V.

100. **Theorem 1.39.2.** In a spherical category, Tr^L_V(a_V x) = Tr^R_V(x a_V^{-1}) for all x in End(V).

### 1.41-1.42 Semisimple Categories and Grothendieck Rings

101. **Proposition 1.41.1.** In a semisimple multitensor category, *V = V*, hence V = V**.

102. **Proposition 1.41.5.** In a semisimple tensor category, for a simple V and isomorphism a: V -> V**, Tr(a) != 0.

103. **Definition 1.42.1.** Z_+-basis, Z_+-ring definitions.

104. **Definition 1.42.2.** Based ring, unital based ring, multifusion ring, fusion ring.

105. **Proposition 1.42.4.** Gr(C) is a based ring for semisimple multitensor categories, a fusion ring for fusion categories.

106. **Proposition 1.42.9.** Categorifications of Z[G] are Vec_G^omega, parametrized by H^3(G, k*)/Out(G).

### 1.43-1.45 Semisimplicity and Frobenius-Perron

107. **Proposition 1.43.2.** Any finite dimensional *-algebra is semisimple.

108. **Proposition 1.43.4.** If A is a based ring, then A tensor_Z C is canonically a *-algebra.

109. **Corollary 1.43.5.** If A is a multifusion ring, then A tensor_Z C is semisimple.

110. **Theorem 1.44.1.** (Frobenius-Perron Theorem) A square matrix B with nonneg entries has a nonneg real eigenvalue lambda(B) dominating all other eigenvalues. If B has strictly positive entries, lambda(B) is a simple positive eigenvalue.

111. **Proposition 1.45.2.** If C is a ring category with right duals, then Gr(C) is a transitive unital Z_+-ring.

112. **Definition 1.45.3.** The Frobenius-Perron dimension FPdim(X) is the largest nonneg eigenvalue of the matrix of left multiplication by X.

113. **Proposition 1.45.4.** (i) FPdim(X) is an algebraic integer dominating its conjugates. (ii) FPdim(X) >= 1.

114. **Proposition 1.45.5.** (1) FPdim is a ring homomorphism. (2) There exists a unique regular element R. (3) FPdim is the unique character taking nonneg values on the basis. (4) FPdim(X) = lambda(N_X) for nonneg X.

115. **Proposition 1.45.8.** FPdim is invariant under the duality involution *.

116. **Corollary 1.45.9.** If FPdim(X) = 1 then X is invertible.

117. **Proposition 1.45.10.** (1) A unital Z_+-ring homomorphism with nonneg matrix preserves FPdim. (2) It preserves regular elements.

118. **Corollary 1.45.11.** A quasi-tensor functor preserves FPdim.

119. **Proposition 1.45.15.** (Kronecker) If B is nonneg integer matrix with lambda(BB^T) = lambda(B)^2, and lambda(B) < 2, then lambda(B) = 2cos(pi/n).

120. **Corollary 1.45.16.** In a fusion ring, if FPdim(X) < 2 then FPdim(X) = 2cos(pi/n) for some n >= 3.

### 1.46-1.48 Deligne Tensor Product, Finite Tensor Categories

121. **Definition 1.46.1.** Deligne's tensor product C boxtimes D is universal for bilinear right exact bifunctors.

122. **Proposition 1.46.2.** Deligne's tensor product exists, is unique, and for module categories C-mod boxtimes D-mod = (C tensor D)-mod.

123. **Proposition 1.46.3.** If C, D are multitensor categories, then C boxtimes D is a multitensor category.

124. **Proposition 1.47.1.** K_0(C) is a Gr(C)-bimodule for finite multitensor categories.

125. **Proposition 1.47.2.** Explicit formulas for tensor product of projective covers with objects.

126. **Proposition 1.47.3.** In a multitensor category, dual of a projective is projective, and any projective is also injective.

127. **Definition 1.47.4.** The regular object R_C = sum FPdim(X_i) P_i.

128. **Definition 1.47.5.** The Frobenius-Perron dimension of C is FPdim(C) = FPdim(R_C).

129. **Proposition 1.47.7.** Z tensor R_C = R_C tensor Z = FPdim(Z) R_C; the image of R_C in Gr(C) is regular.

130. **Definition 1.48.1.** A tensor category is integral if FPdim takes integer values.

131. **Proposition 1.48.2.** A finite tensor category is integral iff it is Rep(H) for a finite dimensional quasi-Hopf algebra.

132. **Corollary 1.48.3.** Integral finite tensor categories biject with finite dimensional quasi-Hopf algebras up to twist equivalence.

### 1.49-1.50 Surjective Functors and Categorical Freeness

133. **Definition 1.49.1.** A functor F is surjective if any object of D is a subquotient of F(X).

134. **Theorem 1.49.3.** A surjective quasi-tensor functor maps projective objects to projectives.

135. **Theorem 1.50.1.** F(R_C) = (FPdim(C)/FPdim(D)) R_D.

136. **Corollary 1.50.2.** FPdim(C) >= FPdim(D), and FPdim(D) divides FPdim(C) in algebraic integers.

137. **Corollary 1.50.3.** If C is integral and F surjective, D is integral and F(R_C) is free of rank FPdim(C)/FPdim(D).

138. **Corollary 1.50.4.** A finite dimensional quasi-Hopf algebra is a free module over its quasi-Hopf subalgebra.

### 1.51-1.53 Distinguished Invertible Object, Integrals

139. **Lemma 1.51.1.** L_rho (the distinguished invertible object) is invertible.

140. **Lemma 1.51.2.** P_{D(i)} = P_i tensor L_rho; L_{D(i)} = L_i tensor L_rho.

141. **Corollary 1.51.3.** P_{i**} = L_rho* tensor P_{i**} tensor L_rho.

142. **Definition 1.51.4.** L_rho is the distinguished invertible object of C.

143. **Corollary 1.51.5.** Any finite dimensional quasi-Hopf algebra is a Frobenius algebra.

144. **Definition 1.52.1.** A left integral in H is I such that xI = epsilon(x)I for all x.

145. **Proposition 1.52.3.** Any finite dimensional quasi-Hopf algebra admits unique (up to scaling) nonzero left and right integrals.

146. **Proposition 1.52.4.** L_rho coincides with the distinguished character chi of H.

147. **Proposition 1.52.5.** Equivalence: H semisimple iff epsilon(I) != 0 iff I^2 != 0 iff I is an idempotent.

148. **Definition 1.52.6.** A finite tensor category is unimodular if L_rho = 1.

149. **Theorem 1.53.1.** If C is not semisimple and admits u: Id -> **, then the Cartan matrix is degenerate over k.

## Chapter 2: Module Categories

### 2.1-2.5 Module Categories: Definitions and Examples

150. **Definition 2.1.1.** A left module category over C is a category M with action bifunctor, associativity constraint satisfying the pentagon relation.

151. **Definition 2.1.2.** Equivalent definition with explicit unit constraint.

152. **Proposition 2.1.3.** C-module category structures on M biject with monoidal functors F: C -> End(M).

153. **Definition 2.1.6.** A module subcategory is a full subcategory closed under the action.

154. **Definition 2.2.1.** A module functor (F, s) is a functor with natural isomorphism s compatible with the module structure.

155. **Definition 2.3.1.** An abelian module category over a multitensor category C is a locally finite abelian category with exact-in-first-variable action.

156. **Proposition 2.4.1.** Direct sum of module categories is a module category.

157. **Definition 2.4.3.** A module category is indecomposable if it is not a nontrivial direct sum.

158. **Definition 2.5.4.** A (C,D)-bimodule category is a module category over C boxtimes D^op.

### 2.6-2.8 Exact Module Categories

159. **Definition 2.6.1.** A module category M is exact if P tensor M is projective in M for any projective P in C and any M in M.

160. **Lemma 2.7.1.** An exact module category over a finite multitensor category has enough projectives.

161. **Corollary 2.7.2.** An exact module category with finitely many simples is finite.

162. **Lemma 2.7.3.** In an exact module category, P tensor X is injective for projective P in C.

163. **Corollary 2.7.4.** In an exact module category, projective = injective.

164. **Lemma 2.7.6.** The relation "Y appears as subquotient of L tensor X" is an equivalence relation on simples.

165. **Proposition 2.7.7.** An exact module category decomposes as direct sum of indecomposable exact subcategories.

166. **Proposition 2.7.8.** Any additive module functor from an exact module category is exact.

167. **Definition 2.8.1.** A Z_+-module over a Z_+-ring K.

168. **Definition 2.8.3.** An irreducible Z_+-module has no proper Z_+-submodules.

169. **Lemma 2.8.5.** Gr(M) is irreducible over Gr(C) for indecomposable exact M.

170. **Proposition 2.8.7.** There are only finitely many irreducible Z_+-modules over a based ring of finite rank.

### 2.9-2.10 Algebras in Categories and Internal Hom

171. **Definition 2.9.1.** An algebra in a multitensor category C is (A, m, u) with multiplication and unit morphisms satisfying associativity and unit axioms.

172. **Definition 2.9.5.** A right module over an algebra (A, m, u) in C.

173. **Definition 2.9.6.** Homomorphisms of A-modules.

174. **Proposition 2.9.10.** Mod_C(A) is a left module category over C.

175. **Lemma 2.9.12.** Hom_A(X tensor A, M) = Hom(X, M).

176. **Definition 2.9.18.** Two algebras A, B in C are Morita equivalent if Mod_C(A) and Mod_C(B) are module equivalent.

177. **Definition 2.9.21.** An algebra A is exact if Mod_C(A) is exact.

178. **Definition 2.9.22.** Tensor product M tensor_A N over an algebra A.

179. **Definition 2.9.24.** An A-B-bimodule in C.

180. **Definition 2.10.2.** The internal Hom Hom(M1, M2) is the object of C representing Hom(. tensor M1, M2).

181. **Lemma 2.10.4.** Canonical isomorphisms for internal Hom: (1) adjunction, (2) via tensor with dual, (3) Hom(X tensor M1, M2) = Hom(M1, M2) tensor X*, (4) Hom(M1, X tensor M2) = X tensor Hom(M1, M2).

182. **Corollary 2.10.6.** For exact module categories, internal Hom is exact in each variable.

183. **Proposition 2.10.7.** If internal Hom is right exact in second variable then M is exact. If all module functors M1 -> M2 are exact then M1 is exact.

### 2.11-2.14 Main Theorem, Dual Categories

184. **Theorem 2.11.2.** If M in M satisfies (1) Hom(M, .) is right exact and (2) every N is a quotient of X tensor M, then Hom(M, .): M -> Mod_C(A) is an equivalence, where A = Hom(M,M).

185. **Theorem 2.11.6.** (i) Every finite module category over C is equivalent to Mod_C(A). (ii) Every exact module category with a generator is Mod_C(Hom(M,M)).

186. **Proposition 2.12.2.** Fun_C(M1, M2) is equivalent to the category of A-B-bimodules (when M_i = Mod_C(A_i)).

187. **Corollary 2.12.3.** Fun_C(M1, M2) of right exact module functors is abelian.

188. **Lemma 2.13.2.** Composition of module functors between exact module categories is biexact.

189. **Lemma 2.13.3.** Any module functor between exact module categories has right and left adjoints.

190. **Corollary 2.13.4.** Module functors between exact categories map projectives to projectives.

191. **Proposition 2.13.5.** Fun_C(M1, M2) is finite.

192. **Definition 2.14.1.** The dual category C*_M = Fun_C(M, M) is a finite multitensor category.

193. **Lemma 2.14.3.** The unit object in C*_M is a direct sum of projectors; each is simple.

194. **Lemma 2.14.4.** M is an exact module category over C*_M.

195. **Theorem 2.14.6.** (Double centralizer theorem) The functor can: C -> (C*_M)*_M is an equivalence.

196. **Lemma 2.14.7.** Any left B-module is of the form *A tensor X.

197. **Corollary 2.14.9.** An exact module category over a finite tensor category is indecomposable over C*_M.

198. **Lemma 2.14.10.** Fun_C(M1, M) is an exact module category over C*_M.

199. **Theorem 2.14.11.** The maps M1 -> Fun_C(M1, M) and M2 -> Fun_{C*_M}(M2, M) are mutually inverse bijections of exact module categories over C and C*_M.

200. **Proposition 2.14.14.** (Basic identity) Hom_C(X,Y) tensor Z = *Hom_{C*_M}(Z,X) tensor Y.

201. **Definition 2.14.13.** The Drinfeld center Z(C) = C*_{C boxtimes C^op}.
