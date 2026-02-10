# All Statements from "An Invitation to Applied Category Theory: Seven Sketches in Compositionality"

## Statement 1: Definition 1.12
Let X and Y be sets. A *relation between* X and Y is a subset R ⊆ X × Y. A *binary relation on* X is a relation between X and X, i.e. a subset R ⊆ X × X.

## Statement 2: Definition 1.14
If A is a set, a *partition* of A consists of a set P and, for each p ∈ P, a nonempty subset A_p ⊆ A, such that A = ⋃_{p ∈ P} A_p and if p ≠ q then A_p ∩ A_q = ∅.

## Statement 3: Definition 1.18
Let A be a set. An *equivalence relation* on A is a binary relation, denoted ~, satisfying: (a) a ~ a for all a ∈ A (reflexivity), (b) a ~ b iff b ~ a for all a, b ∈ A (symmetry), and (c) if a ~ b and b ~ c then a ~ c for all a, b, c ∈ A (transitivity).

## Statement 4: Proposition 1.19
Let A be a set. There is a one-to-one correspondence between the ways to partition A and the equivalence relations on A.

## Statement 5: Definition 1.21
Given a set A and an equivalence relation ~ on A, we say that the *quotient* A/~ of A under ~ is the set of parts of the corresponding partition.

## Statement 6: Definition 1.22
Let S and T be sets. A *function from S to T* is a subset F ⊆ S × T such that for all s ∈ S there exists a unique t ∈ T with (s, t) ∈ F.

## Statement 7: Definition 1.28
If F: X → Y is a function and G: Y → Z is a function, their *composite* is the function X → Z defined to be G(F(x)) for any x ∈ X.

## Statement 8: Definition 1.30
A *preorder relation* on a set X is a binary relation on X, denoted ≤, such that (a) x ≤ x (reflexivity); and (b) if x ≤ y and y ≤ z, then x ≤ z (transitivity). A pair (X, ≤) is called a *preorder*.

## Statement 9: Definition 1.36
A graph G = (V, A, s, t) consists of a set V whose elements are called *vertices*, a set A whose elements are called *arrows*, and two functions s, t: A → V known as the *source* and *target* functions respectively.

## Statement 10: Definition 1.59
A *monotone map* between preorders (A, ≤_A) and (B, ≤_B) is a function f: A → B such that, for all elements x, y ∈ A, if x ≤_A y then f(x) ≤_B f(y).

## Statement 11: Proposition 1.70
For any preorder (P, ≤_P), the identity function is monotone. If (Q, ≤_Q) and (R, ≤_R) are preorders and f: P → Q and g: Q → R are monotone, then (f ; g): P → R is also monotone.

## Statement 12: Definition 1.75
Let (P, ≤_P) and (Q, ≤_Q) be preorders. A monotone function f: P → Q is called an *isomorphism* if there exists a monotone function g: Q → P such that f ∘ g = id_P and g ∘ f = id_Q.

## Statement 13: Proposition 1.78
Let P be a preorder. Monotone maps P → 𝔹 are in one-to-one correspondence with upper sets of P.

## Statement 14: Definition 1.81
Let (P, ≤) be a preorder, and let A ⊆ P be a subset. An element p ∈ P is a *meet* of A if (a) for all a ∈ A, p ≤ a, and (b) for all q such that q ≤ a for all a ∈ A, q ≤ p. Similarly for *join*.

## Statement 15: Proposition 1.91
Suppose (P, ≤) is a preorder and A ⊆ B ⊆ P are subsets that have meets. Then ⋀B ≤ ⋀A. Similarly, if A and B have joins, then ⋁A ≤ ⋁B.

## Statement 16: Definition 1.92
We say that a monotone map f: P → Q preserves meets if f(a ∧ b) ≅ f(a) ∧ f(b) for all a, b ∈ P. We similarly say f preserves joins if f(a ∨ b) ≅ f(a) ∨ f(b) for all a, b ∈ P.

## Statement 17: Definition 1.93
We say that a monotone map f: P → Q has a generative effect if there exist elements a, b ∈ P such that f(a) ∨ f(b) ≇ f(a ∨ b).

## Statement 18: Definition 1.95
A *Galois connection* between preorders P and Q is a pair of monotone maps f: P → Q and g: Q → P such that f(p) ≤ q if and only if p ≤ g(q). We say that f is the *left adjoint* and g is the *right adjoint*.

## Statement 19: Proposition 1.107
Suppose that f: P → Q and g: Q → P are monotone maps. The following are equivalent: (a) f and g form a Galois connection where f is left adjoint to g, (b) for every p ∈ P and q ∈ Q we have p ≤ g(f(p)) and f(g(q)) ≤ q.

## Statement 20: Proposition 1.111
(Right adjoints preserve meets). Let f: P → Q be left adjoint to g: Q → P. Suppose A ⊆ Q any subset, and let g(A) := {g(a) | a ∈ A} be its image. Then if A has a meet ⋀A ∈ Q then g(A) has a meet ⋀g(A) in P, and g(⋀A) ≅ ⋀g(A). Similarly, left adjoints preserve joins.

## Statement 21: Theorem 1.115
(Adjoint functor theorem for preorders). Suppose Q is a preorder that has all meets and let P be any preorder. A monotone map g: Q → P preserves meets if and only if it is a right adjoint. Similarly, if P has all joins, a monotone map f: P → Q preserves joins if and only if it is a left adjoint.

## Statement 22: Definition 1.120
A *closure operator* j: P → P on a preorder P is a monotone map such that for all p ∈ P we have (a) p ≤ j(p); (b) j(j(p)) ≅ j(p).

## Statement 23: Definition 2.2
A *symmetric monoidal structure* on a preorder (X, ≤) consists of: (i) an element I ∈ X (monoidal unit), and (ii) a function ⊗: X × X → X (monoidal product), satisfying: (a) monotonicity, (b) unitality, (c) associativity, and (d) symmetry.

## Statement 24: Proposition 2.38
If (X, ≤, I, ⊗) is a symmetric monoidal preorder then so is its opposite, (X, ≥, I, ⊗).

## Statement 25: Definition 2.41
Let P and Q be monoidal preorders. A *monoidal monotone* from P to Q is a monotone map f satisfying: (a) I_Q ≤ f(I_P), and (b) f(p₁) ⊗ f(p₂) ≤ f(p₁ ⊗ p₂).

## Statement 26: Definition 2.46
Let V = (V, ≤, I, ⊗) be a symmetric monoidal preorder. A V-category X consists of: (i) a set Ob(X) of objects; (ii) for every two objects x, y, an element X(x,y) ∈ V (hom-object), satisfying: (a) I ≤ X(x,x), and (b) X(x,y) ⊗ X(y,z) ≤ X(x,z).

## Statement 27: Theorem 2.49
There is a one-to-one correspondence between preorders and Bool-categories.

## Statement 28: Definition 2.51
A metric space (X, d) consists of: (i) a set X of points, and (ii) a function d: X × X → ℝ_{≥0}, satisfying: (a) d(x,x) = 0, (b) d(x,y) = 0 implies x = y, (c) d(x,y) = d(y,x), and (d) d(x,y) + d(y,z) ≥ d(x,z) (triangle inequality).

## Statement 29: Definition 2.53
A *Lawvere metric space* is a Cost-category.

## Statement 30: Definition 2.69
Let X and Y be V-categories. A V-functor from X to Y, denoted F: X → Y, is a function F: Ob(X) → Ob(Y) such that X(x₁, x₂) ≤ Y(F(x₁), F(x₂)).

## Statement 31: Definition 2.74
Let X and Y be V-categories. Their V-product X × Y has Ob(X × Y) := Ob(X) × Ob(Y) and (X × Y)((x,y),(x',y')) := X(x,x') ⊗ Y(y,y').

## Statement 32: Definition 2.79
A symmetric monoidal preorder V is *symmetric monoidal closed* if, for every v, w ∈ V, there is an element v ⊸ w with (a ⊗ v) ≤ w iff a ≤ (v ⊸ w).

## Statement 33: Proposition 2.87
Suppose V is a symmetric monoidal preorder that is closed. Then: (a) (- ⊗ v) is left adjoint to (v ⊸ -); (b) v ⊗ distributes over joins; (c) v ⊗ (v ⊸ w) ≤ w; (d) v ≅ (I ⊸ v); (e) (u ⊸ v) ⊗ (v ⊸ w) ≤ (u ⊸ w).

## Statement 34: Definition 2.90
A *unital commutative quantale* is a symmetric monoidal closed preorder V that has all joins.

## Statement 35: Proposition 2.96
Let P = (P, ≤) be a preorder. It has all joins iff it has all meets.

## Statement 36: Proposition 2.98
Suppose V = (V, ≤, I, ⊗) is any symmetric monoidal preorder that has all joins. Then V is closed if and only if ⊗ distributes over joins.

## Statement 37: Definition 2.100
Let V be a quantale. Given sets X and Y, a V-matrix is a function M: X × Y → V.

## Statement 38: Definition 3.6
A category C consists of: (i) objects Ob(C); (ii) for every two objects c, d, a set C(c,d) of morphisms; (iii) identity morphisms id_c; (iv) a composition rule, satisfying: (a) unitality and (b) associativity.

## Statement 39: Definition 3.7
For any graph G = (V, A, s, t), the *free category* Free(G) has vertices as objects and paths as morphisms, with composition given by concatenation.

## Statement 40: Definition 3.24
The *category of sets*, denoted Set, has all sets as objects and functions as morphisms.

## Statement 41: Definition 3.28
An *isomorphism* is a morphism f: A → B such that there exists a morphism g: B → A satisfying f ∘ g = id_A and g ∘ f = id_B.

## Statement 42: Definition 3.35
A *functor* F: C → D assigns to each object c ∈ C an object F(c) ∈ D and to each morphism f: c₁ → c₂ a morphism F(f): F(c₁) → F(c₂), preserving identities and composition.

## Statement 43: Definition 3.44
Let C be a schema (finitely-presented category). A C-instance is a functor I: C → Set.

## Statement 44: Definition 3.49
A *natural transformation* α: F ⇒ G between functors F, G: C → D specifies, for each c ∈ C, a morphism α_c: F(c) → G(c) satisfying the naturality condition: F(f) ∘ α_d = α_c ∘ G(f).

## Statement 45: Definition 3.51
A *diagram* D in C is a functor D: J → C from an indexing category J. It *commutes* if D(f) = D(f') for every parallel pair of morphisms.

## Statement 46: Definition 3.54
The *functor category* D^C has functors F: C → D as objects and natural transformations as morphisms.

## Statement 47: Definition 3.60
An *instance homomorphism* between database instances I, J: C → Set is a natural transformation α: I → J.

## Statement 48: Definition 3.68
The *pullback of I along F* is the composite functor F ∘ I: C → Set, where F: C → D is a functor and I: D → Set is a set-valued functor.

## Statement 49: Definition 3.70
L: C → D is left adjoint to R: D → C if, for any C ∈ C and D ∈ D, there is a natural isomorphism of hom-sets α_{c,d}: C(c, R(d)) ≅ D(L(c), d).

## Statement 50: Definition 3.79
An object Z in C is a *terminal object* if, for each object C of C, there exists a unique morphism !: C → Z.

## Statement 51: Proposition 3.84
All terminal objects in a category C are isomorphic.

## Statement 52: Definition 3.86
A *product* of X and Y is an object X × Y, together with projection morphisms p_X and p_Y, satisfying the universal property: for all objects C with morphisms f: C → X and g: C → Y, there exists a unique morphism ⟨f, g⟩: C → X × Y making the diagram commute.

## Statement 53: Definition 3.92
A *cone* (C, c_*) over a diagram D: J → C consists of an object C and morphisms c_j: C → D(j) satisfying compatibility. The *limit* of D is the terminal object in Cone(D).

## Statement 54: Theorem 3.95
(Finite limits in Set). Given J presented by a finite graph and D: J → Set, the limit is the set of tuples (d₁,...,d_n) with d_i ∈ D(v_i) satisfying D(a)(d_i) = d_j for all arrows a: v_i → v_j.

## Statement 55: Definition 3.102
A *cocone* in C is a cone in C^op. The *colimit* of D is the limit of D^op: J^op → C^op, viewed as a cocone in C.

## Statement 56: Definition 4.2
A *feasibility relation* for preorders X and Y is a monotone map Φ: X^op × Y → Bool.

## Statement 57: Definition 4.8
Let V be a quantale, X and Y be V-categories. A V-profunctor from X to Y, denoted Φ: X ⇸ Y, is a V-functor Φ: X^op × Y → V.

## Statement 58: Definition 4.21
Let Φ: X ⇸ Y and Ψ: Y ⇸ Z be V-profunctors. Their composite is defined by (Φ ; Ψ)(p,r) = ⋁_{q ∈ Q} (Φ(p,q) ⊗ Ψ(q,r)).

## Statement 59: Theorem 4.23
For any skeletal quantale V, there is a category Prof_V whose objects are V-categories, whose morphisms are V-profunctors, and with composition as in Definition 4.21.

## Statement 60: Definition 4.24
We define Feas := Prof_{Bool}.

## Statement 61: Lemma 4.27
Composing any profunctor Φ: P ⇸ Q with either unit profunctor U_P or U_Q returns Φ: U_P ; Φ = Φ = Φ ; U_Q.

## Statement 62: Lemma 4.31
Serial composition of profunctors is associative.

## Statement 63: Definition 4.34
Let F: P → Q be a V-functor. The *companion* of F is F̂(p,q) := Q(F(p),q) and the *conjoint* is F̌(q,p) := Q(q,F(p)).

## Statement 64: Definition 4.42
The *collage* of a V-profunctor Φ: X ⇸ Y is a V-category Col(Φ) defined on Ob(X) ⊔ Ob(Y).

## Statement 65: Definition 4.58
A *dual for c* in a symmetric monoidal category (C, I, ⊗) consists of: an object c*, a unit η_c: I → c* ⊗ c, and a counit ε_c: c ⊗ c* → I, satisfying the snake equations. If every object has a dual, C is *compact closed*.

## Statement 66: Proposition 4.60
If C is a compact closed category, then it is monoidal closed with c ⊸ d := c* ⊗ d.

## Statement 67: Theorem 4.63
Let V be a skeletal quantale. The category Prof_V can be given the structure of a compact closed category, with monoidal product given by the product of V-categories.

## Statement 68: Definition 5.2
A *prop* is a symmetric strict monoidal category (C, 0, +) for which Ob(C) = ℕ, the monoidal unit is 0 ∈ ℕ, and the monoidal product on objects is given by addition.

## Statement 69: Definition 5.11
A *prop functor* F: C → D is identity-on-objects and strictly preserves the monoidal structure.

## Statement 70: Definition 5.13
An (m, n)-port graph (V, in, out, ι) consists of a finite set V of vertices, functions in: m → V, out: n → V, and wires ι connecting ports.

## Statement 71: Definition 5.25
A prop signature is a tuple (G, s, t), where G is a set of generators and s, t: G → ℕ give in-arity and out-arity.

## Statement 72: Proposition 5.29
The free prop Free(G) on a signature (G, s, t) has the property that prop functors Free(G) → C are in one-to-one correspondence with functions G → C sending each g to a morphism s(g) → t(g).

## Statement 73: Definition 5.30
A G-generated prop expression e: m → n is defined inductively from generators, identities, composition, and monoidal product.

## Statement 74: Definition 5.36
A *rig* is a tuple (R, 0, +, 1, *) where (R, 0, +) is a commutative monoid, (R, 1, *) is a monoid, * distributes over +, and 0 * r = r * 0 = 0.

## Statement 75: Definition 5.45
Matrices with entries in a rig R, with rows indexed by m and columns by n.

## Statement 76: Definition 5.50
The *prop of R-matrices*, Mat(R), has morphisms m → n given by (m × n)-matrices with values in R. Composition is matrix multiplication and monoidal product is direct sum.

## Statement 77: Theorem 5.53
There is a prop functor S: SFG_R → Mat(R) that sends signal flow graph generators to matrices.

## Statement 78: Proposition 5.54
The matrix S(g) of a signal flow graph g with m inputs and n outputs is the (m × n)-matrix whose (i,j)-entry describes the amplification of the ith input to the jth output.

## Statement 79: Proposition 5.56
Given any matrix M ∈ Mat(R), there exists a signal flow graph g ∈ SFG_R such that S(g) = M.

## Statement 80: Theorem 5.60
The prop Mat(R) is isomorphic to the prop with a certain explicit presentation by generators and relations.

## Statement 81: Definition 5.65
A monoid object (M, μ, η) in a symmetric monoidal category (C, I, ⊗) is an object M with morphisms μ: M ⊗ M → M and η: I → M satisfying associativity and unitality.

## Statement 82: Definition 5.79
The prop Rel_R of R-relations has subsets B ⊆ R^m × R^n as morphisms, composed by the relational composition rule.

## Statement 83: Theorem 5.87
The prop Rel_R is a compact closed category in which every object n ∈ ℕ is dual to itself, n = n*.

## Statement 84: Definition 6.1
An *initial object* in C is an object ∅ such that for each object T in C there exists a unique morphism !_T: ∅ → T.

## Statement 85: Definition 6.11
A *coproduct* of A and B is an object A + B with morphisms ι_A and ι_B, satisfying the universal property: for all objects T with f: A → T and g: B → T, there exists a unique [f,g]: A + B → T.

## Statement 86: Definition 6.19
The *pushout* X +_A Y is the colimit of X ← A → Y, with the universal property for commutative squares.

## Statement 87: Definition 6.30
A category C *has finite colimits* if a colimit exists whenever J is a finite category and D: J → C is a diagram.

## Statement 88: Proposition 6.32
The following are equivalent: (1) C has all finite colimits; (2) C has an initial object and all pushouts; (3) C has all coequalizers and all finite coproducts.

## Statement 89: Corollary 6.36
The categories FinSet and Set have (all) finite colimits.

## Statement 90: Theorem 6.37
(Finite colimits in Set). Given J presented by a finite graph and D: J → Set, the colimit is the set {(v,d) | v ∈ V and d ∈ D(v)}/~ where (v,d) ~ (w,e) if there is an arrow a: v → w with D(a)(d) = e.

## Statement 91: Definition 6.43
A *cospan* in C is a pair of morphisms to a common object A → N ← B.

## Statement 92: Definition 6.45
For C with finite colimits, the category Cospan_C has same objects as C, with cospans as morphisms and composition via pushouts.

## Statement 93: Definition 6.52
A *Frobenius structure* on X in a symmetric monoidal category consists of (μ, η, δ, ε) where (X, μ, η) is a commutative monoid and (X, δ, ε) is a cocommutative comonoid, satisfying the Frobenius equations.

## Statement 94: Definition 6.54
The *spider* s_{m,n}: X^{⊗m} → X^{⊗n} is defined as (m-1) multiplications followed by (n-1) comultiplications.

## Statement 95: Theorem 6.55
(Spider theorem). Let (X, μ, η, δ, ε) be a Frobenius monoid. If f: X^{⊗m} → X^{⊗n} is constructed from spiders and symmetry maps with one connected component, then f = s_{m,n}.

## Statement 96: Theorem 6.58
The hypergraph category structure can be presented by generators {μ, η, δ, ε} with specified arities.

## Statement 97: Definition 6.60
A *hypergraph category* is a symmetric monoidal category in which each object X is equipped with a Frobenius structure, compatible with the monoidal product.

## Statement 98: Definition 6.75
An F-decorated cospan consists of a cospan A → N ← B in C together with an element s ∈ F(N), where (F, φ): (C, +) → (Set, ×) is a symmetric monoidal functor.

## Statement 99: Theorem 6.77
Given a category C with finite colimits and a symmetric monoidal functor (F, φ): (C, +) → (Set, ×), there is a hypergraph category Cospan_F whose morphisms are equivalence classes of F-decorated cospans.

## Statement 100: Definition 6.97
For any symmetric monoidal category (C, I, ⊗), there is an operad O_C having Ob(C) as types and morphisms C₁ ⊗ ⋯ ⊗ C_n → D as operations.

## Statement 101: Definition 6.99
An *algebra* for an operad O is an operad functor F: O → Set.

## Statement 102: Proposition 6.101
There is an equivalence between Cospan-algebras and hypergraph props.

## Statement 103: Proposition 7.3
(Pullback pasting lemma). In a commutative diagram, if the right square is a pullback, then the left square is a pullback iff the whole rectangle is a pullback.

## Statement 104: Definition 7.5
A morphism f: A → B is a *monomorphism* if the square with id_A is a pullback; it is an *epimorphism* if the corresponding square is a pushout.

## Statement 105: Definition 7.12
A *subobject classifier* in a category E with finite limits consists of an object Ω together with a monomorphism true: 1 → Ω such that for any monomorphism m: X → Y, there is a unique characteristic map ⌈m⌉: Y → Ω making the diagram a pullback.

## Statement 106: Definition 7.22
A *presheaf* P on a small category C is a functor P: C^op → Set.

## Statement 107: Definition 7.25
A *topology* on X is a subset Op ⊆ P(X) of open sets satisfying: (a) X ∈ Op; (b) binary intersections are open; (c) arbitrary unions are open. The pair (X, Op) is a *topological space*.

## Statement 108: Definition 7.35
A *sheaf* on a topological space (X, Op) is a presheaf P: Op^op → Set satisfying the sheaf condition: for every matching family of sections over an open cover, there exists a unique gluing.

## Statement 109: Definition 7.69
A *modality* in Shv(X) is a sheaf morphism j: Ω → Ω satisfying: (a) p ≤ j(p); (b) j(j(p)) ≤ j(p); and (c) j(p ∧ q) = j(p) ∧ j(q).

## Statement 110: Proposition 7.71
Fix a proposition p ∈ |Ω|. Then (a) q ↦ (p ⇒ q) is a modality; (b) q ↦ (p ∨ q) is a modality; (c) q ↦ ((q ⇒ p) ⇒ p) is a modality.

## Statement 111: Example 5.6
The prop Bij has the symmetric group as morphisms n → n and only identity morphisms otherwise.

## Statement 112: Example 5.7
The prop Corel has corelations as morphisms.

## Statement 113: Example 5.8
The prop Rel has relations as morphisms.
