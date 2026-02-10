MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Introduction

In this lecture, I'll give a bit of an overview of what we will be doing this semester, and in particular how it will differ from 18.725. We will start in earnest (with the rudiments of category theory) in the next lecture.

## 1 Where we were, and where we need to go

In 18.725, we studied the notion of an abstract algebraic variety over an algebraically closed field. This combines a lot of the commutative algebra developed in the early 20th century (largely to explain the geometric reasoning of the masters of the Italian school) with Weil's fundamental idea to glue affine algebraic varieties in the same way that one glues local charts together to build manifolds. So what's left?

• We would like to deal with phenomena of nonreducedness, for instance as it emerges under degenerations. One of the key ideas of the Italian school for understanding things like the geometry of the moduli space of curves was to notice that if you have a family of algebro-geometric objects defined in terms of a parameter t, then the behavior of a particular member of the family is sometimes much simpler than that of a general member. For instance, for a general t, the elliptic curve  $y^2 = x^3 + tx + t$  does not have a rational parametrization, but it does in the special case t = 0. One can often understand something about the general member of the family by first analyzing a special member, then figuring out how the information you are looking for gets transmitted back to the general member via the degeneration.

However, degenerations of algebraic varieties are not always best viewed as algebraic varieties. For example, if  $t \neq 0$ , then the homogeneous polynomial  $y^2 - tx^2$  in x, y, z (over, say, the complex numbers) defines a pair of lines. The degeneration at t = 0, however, is the *single* line y = 0, because the equations  $y^2 = 0$  and y = 0 define the same variety. In order for the degeneration to preserve the degree of the curve, we need to remember that it is  $y^2$  rather than y which defines this line. That is, the function y on the variety should be *nilpotent*, a possibility that is not afforded by the category of algebraic varieties.

• We would like to work over fields which are not algebraically closed. The restriction to algebraically closed fields was originally needed to make things like Bézout's theorem work. However, at the end of the day, we are sometimes interested in solving polynomials over non-algebraically closed fields. For instance, the elliptic curves  $y^2 = x^3 + tx$  defined by rational numbers t are all isomorphic as algebraic varieties over the complex numbers. However, they have rather different arithmetic behaviors; for instance, the curve for t = 1 has only finitely many rational points, whereas the curve for t = 73 has infinitely many.

Weil had an answer for this point: he suggested embedding one's given base field in a large algebraically closed field, called a *universal domain*. However, Weil's answer looks like a mistake in hindsight, because it is not sufficiently *functorial*; see below.

• We would also like to work over (commutative, unital) rings, not just fields. For instance, already in Weil's work the question of reduction mod p arises, but cannot be addressed while working over fields.

Even in the context of varieties, one often wants to work over a base which is not a field. For instance, the theory of *elliptic surfaces* is largely thought of by viewing these surfaces as (relative) elliptic curves over a base curve.

There's more, but enough for now.

## 2 Paradigm shift 1: sheaves

At the time, one might have expected that the future development of algebraic geometry would proceed as a natural descent from Weil's 1946 Foundations, with more bells and whistles attached to extend generality. However, just as the theory of epicycles to explain the motion of planets was thrown into disrepute by two paradigm shifts (Galileo's heliocentricity and Kepler's elliptic orbits), two paradigm shifts rendered Weil's foundations a dead end in the development of algebraic geometry. (Most material written in that language has since appeared in modern terminology; what remains untranslated is as intelligible to the modern reader as Chaucer's Middle English.)

The first of these shifts can be attributed to Serre, who introduced the notion of sheaves into algebraic geometry. These are the sort of objects defined by descriptions like "take all continuous functions on all open subsets of a topological space", or "take all differentiable functions on all open subsets of a smooth manifold". The latter example is particularly helpful to keep in mind: it is possible to have two different smooth manifolds which are isomorphic as topological spaces (e.g., to  $\mathbb{R}^4$ , or to a seven-dimensional sphere), but not as smooth manifolds. That is, the underlying topological space does not carry enough information to detect nonisomorphism of smooth manifolds. However, the sheaf of differentiable functions does carry enough information.

Sheaves were originally introduced by Cartan in order to simplify and extend the theory of complex analytic geometry. It is Serre who recognized their place in modern algebraic geometry, by observing (among other things) that they give you a natural way to add nilpotents. In my example of the lines y = 0 versus  $y^2 = 0$  in the (x, y)-plane, it will turn out that (in the category of schemes) the underlying sets of these two objects will be the same, but the sheaves of regular functions will differ.

However, it will take us some time before we can relate sheaves to algebraic geometry. We will first have to take some time to discuss topological spaces equipped with rings of "interesting" functions, giving rise to the notion of a *locally ringed space*. This notion includes many familiar things: topological spaces, topological manifolds, smooth manifolds, and even abstract algebraic varieties.

But what we really want to include into this category is the prime spectrum of an arbitrary (commutative) ring. Recall that over an algebraically closed field, by the Nullstellensatz there is a bijection between the points of an affine algebraic variety and the *maximal* ideals of its ring of regular functions. For a general ring, Zariski suggested to instead look at the set of *prime* ideals, i.e., the *prime spectrum* of the ring; that way, any map of rings would correspond to a map (contraction) on prime ideals in the opposite direction.

The "fundamental theorem of schemes" is that this set carries the natural structure of a *sheaf* of rings. In other words, the prime spectrum of a ring can be viewed as a locally ringed space. With that (nontrivial) fact in hand, we will be ready to glue prime spectra together to manufacture arbitrary schemes.

## 3 Paradigm shift 2: functors

The second paradigm shift that stood between Weil and modern algebraic geometry is mostly due to Grothendieck, though it is of a piece with the formalist view of mathematics propounded by the Bourbaki school of French mathematicians in the middle of the 20th century. It is to conceive of algebraic geometry in the language of *categories* and *functors*. Roughly speaking, a *category* is the collection of all mathematical objects of a given type, equipped with the maps between those objects that preserve the distinguishing structures. The key example to keep in mind is the category of all rings, together with all homomorphisms between rings.

At first, it may seem rather a bad idea to deal with categories; for one thing, they cannot be viewed as sets due to some annoying paradoxes in set theory (such as Russell's paradox). But once you get past such considerations, dealing with categories is not so hard, and in fact they appear everywhere around you.

Here is where categories appear naturally in algebraic geometry. Say  $P_1, \ldots, P_m$  are polynomials in the variables  $x_1, \ldots, x_n$  over a ring R. Then for any ring S equipped with a homomorphism  $R \to S$ , it makes sense to consider the set

$$\{(x_1,\ldots,x_n)\in S^n: P_1(x_1,\ldots,x_n)=\cdots=P_m(x_1,\ldots,x_n)=0\}$$

of S-valued solutions to the system of equations  $P_1 = \cdots = P_m = 0$ . One should thus avoid linking these polynomials to a single set of "points", but instead view them as a *scheme* for converting rings into sets of solutions. This gives a natural example of a *functor* between two categories, i.e., a rule for converting objects of one category into objects of the other, and for converting morphisms between two objects of the first category into morphisms between the image objects of the second category. (In our example, we are converting R-algebras into sets.)

One benefit of this point of view is that it naturally distinguishes, for instance, the zero loci of y and  $y^2$ : they give the same sets when we plug in an algebraically closed field k, but not when we plug in a ring such as  $k[\epsilon]/(\epsilon^2)$ .

That benefit by itself is not so significant, as it still doesn't really prove that category theory is good for anything other than formulating simple statements in complicated lan-

guage. What makes category theory so useful, and how we will exploit it in our work, is that it lets you formalize certain types of "reasoning by analogy" that mathematicians would like to engage in all the time, but which is sometimes difficult. One key example in the context of schemes is the notion of a *product*. Given two mathematical objects X and Y, how should one define their product  $X \times Y$ ? When X and Y are given as sets carrying some extra structure (e.g., groups, rings, etc.), the correct answer is to take the Cartesian product of the underlying sets and then somehow cook up a good structure on that.

From the point of view of category theory, though, the right way to answer this question is to specify a *universal property* that should be satisfied by the product. Namely, the product  $X \times Y$  should have the following properties.

- (a) It should come with projection maps  $\pi_1: X \times Y \to X$  and  $\pi_2: X \times Y \to Y$ .
- (b) Given any object Z, the function taking a map  $f:Z\to X\times Y$  to the pair of compositions  $\pi_1\circ f:Z\to X$  and  $\pi_2\circ g:Z\to Y$  should be a bijection.

This does not by itself actually construct products; indeed, some categories may not always admit product objects according to this definition. However, it does give a characterization of how a "correct" definition of a product object should behave. In fact, it's okay to come up with two different definitions as long as they both satisfy the universal property; the effect is that there will be *canonical identifications* between the two types of projects.

We will use this particular example to construct products in the category of schemes. There, we will discover that the product of two schemes does *not* have underlying set equal to the Cartesian products of the underlying sets!

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Category theory (updated 8 Feb 09)

We're going to use the language of category theory freely. Fortunately, it's easy to learn because it corresponds naturally to the way you (hopefully) already think about mathematical objects. (I could give a reference, but in fact you should be fine just looking these things up in Wikipedia.)

## 1 Warning: set-theoretic difficulties

Category theory is a bit tricky because it tries to deal with objects like "the ??? of all sets", or all rings, or whatnot. Russell's paradox shows that there is in fact no *set* of all sets. Namely, if there were, it would have a subset consisting of those sets U for which  $U \notin U$ . But that would then be a set V, and if  $V \in V$  then  $V \notin V$  and vice versa.

The way around this is to tamper with the axioms of set theory slightly, by introducing the notion of a *class*. A class is something which behaves just like a set whose members are sets, except that there is no power axiom; there is not guaranteed to be a class consisting of all subclasses of a given class. Unless, that is, your class consists just of the elements of some actual set. (You might then ask what kind of object is the ??? of all classes. Never mind that for now.) We also assume there is a class of all sets, called the *universe*.

Except for the power axiom, you may perform operations on classes like you do with sets. For instance, given a class C and a logical statement P depending on a single set, you can form the subclass of C consisting of all elements for which P is true. You can also form Cartesian products indexed by sets, although I'll hardly ever do this except for *finite* products. (There is also an axiom of choice at the class level.)

A class is *small* if its elements are in bijection with some set.

### 2 Categories, and examples

A category  $\mathcal{C}$  consists of the following data.

- A class of *objects*, denoted  $Obj(\mathcal{C})$ .
- For each ordered pair of objects (X, Y), a set of *morphisms*, denoted Hom(X, Y). (You may think of this as an element of the Cartesian product of two copies of  $\mathcal{C}$  and one copy of the universe.)
- For each ordered triple of objects (X, Y, Z), a function  $\circ$ :  $\operatorname{Hom}(Y, Z) \times \operatorname{Hom}(X, Y) \to \operatorname{Hom}(X, Z)$ , called *composition*, which satisfies the following properties.
  - The associative law: given an ordered quadruple of objects (X, Y, Z, W), the two ways to compose  $\operatorname{Hom}(Z, W) \times \operatorname{Hom}(Y, Z) \times \operatorname{Hom}(X, Y)$  to  $\operatorname{Hom}(X, W)$  give the same answer.

- The *identity law*: for each object X, there must exist a morphism  $\mathrm{id}_X \in \mathrm{Hom}(X,X)$  which is an identity under composition on either side. Note that  $\mathrm{id}_X$  is forced to be unique by this condition.

(I have a habit of calling morphisms "arrows" because they are usually pictorially represented as such.)

This definition is meant to capture many, if not all, basic types of structured mathematical objects. Examples:

- The category of sets, denoted Set, where Hom(X,Y) is all functions from X to Y.
- The category of topological spaces, denoted Top, where Hom(X,Y) is all *continuous* functions from X to Y.
- The category of (commutative, unital) rings, denoted Ring, where Hom(X, Y) is all ring homomorphisms from X to Y.
- The category of topological rings, denoted TopRing, where Hom(X, Y) is all *continuous* ring homomorphisms from X to Y.
- The category of modules over a fixed ring R, denoted  $Mod_R$ , where Hom(X,Y) is all R-module homomorphisms from X to Y.

And so forth. I'll leave to your imagination the definitions of some more categories for which I might need names later: Ab (abelian groups), Grp (groups), TopGp (topological groups).

However, there are other things that can be viewed as categories. An important example: given any partially ordered set S, make a category in which the objects are the elements of S, and there is exactly one morphism from X to Y if  $X \leq Y$  and none otherwise.

Important special case of the previous one: given a topological space S, we can make a category in which the objects are the open subsets of S, and the morphisms are the inclusions of one open subset into another.

Another example comes from algebra. Given a group, we can make a category with only one object X, in which Hom(X,X) is the group and the composition law is the group operation.

Here's a more interesting example along the lines of the previous one. Given a topological space S, make a category in which the objects are the *points* of S, and the morphisms from X to Y are the continuous functions  $f:[0,1]\to S$  with f(0)=X and f(1)=Y. Define the composition  $g\circ f$  for  $g\in \operatorname{Hom}(Y,Z)$  and  $f\in \operatorname{Hom}(X,Y)$  to be the function  $h:[0,1]\to S$  with

$$h(x) = \begin{cases} f(2x) & x \in [0, 1/2] \\ g(2x - 1) & x \in [1/2, 1]. \end{cases}$$

This is a special case of turning a *groupoid* (something which is like a group except that objects can only be composed if they satisfy a matching condition) into a category. This example comes from the *fundamental groupoid* of a topological space.

#### 3 Interlude: "is" versus "does"

The rigorous formulation of category theory exposes a dark secret of mathematics: objects in a category are rarely ever *equal*. For instance, we all think we agree on what the ring  $\mathbb{Z}$  is, but if we all sat down and wrote down set-theoretic definitions, probably no two of them would exactly match. The point is that we conceive of  $\mathbb{Z}$ , and of most mathematical objects in general, not in terms of what they literally *are* as sets, but by how they *work*, and in particular how they relate to other mathematical objects.

The solution for this suggested by category theory is to characterize interesting mathematical objects using universal properties. For instance, the ring  $\mathbb{Z}$  is characterized by the fact that it is an *initial object* in the category of rings: for every ring Y, there is a unique morphism from  $\mathbb{Z}$  to Y. Any two objects with this property are uniquely isomorphic.

Here are a few other "arrow-theoretic" properties that can be used for this purposes. I'll talk more about universal properties later.

- $Y \in \text{Obj}(\mathcal{C})$  is a *final object* in  $\mathcal{C}$  if for any  $X \in \text{Obj}(\mathcal{C})$ , there is a unique morphism from X to Y. An object which is both initial and final is a *terminal object*.
- A morphism  $f \in \text{Hom}(X,Y)$  is a monomorphism if for any  $g,h \in \text{Hom}(W,X)$ , if  $f \circ g = f \circ h$ , then g = h. In the category of sets (and many other examples), f is a monomorphism if and only if f is injective.
- A morphism  $f \in \text{Hom}(X,Y)$  is an *epimorphism* if for any  $g,h \in \text{Hom}(Y,Z)$ , if  $g \circ f = h \circ f$ , then g = h. In the category of sets (and many other examples), f is an epimorphism if and only if f is surjective. But beware of surprises: for example, the morphism  $\mathbb{Z} \to \mathbb{Q}$  of rings is an epimorphism (and also a monomorphism).
- A morphism  $f \in \text{Hom}(X, Y)$  is an *isomorphism* if it has a two-sided inverse. This implies that it is a monomorphism and an epimorphism, but not conversely (see previous example).

### 4 Functors and natural transformations

Functors can be thought of as "functions between categories". A covariant functor from a category  $C_1$  to a category  $C_2$  consists of:

- A function F from  $Obj(\mathcal{C}_1)$  to  $Obj(\mathcal{C}_2)$ .
- For each pair (X, Y) of  $\mathrm{Obj}(\mathcal{C}_1)$ , a function  $F_{X,Y} : \mathrm{Hom}(X, Y) \to \mathrm{Hom}(F(X), F(Y))$ , such that F commutes with composition and F carries  $\mathrm{id}_X$  to  $\mathrm{id}_{F(X)}$ .

A contravariant functor works the same way except that  $F_{X,Y}$  carries Hom(X,Y) to Hom(F(Y),F(X)), that is, it reverses the sense of the morphisms. You can turn it into a covariant functor by replacing one of the two categories with its *opposite category*, in which all morphisms are reversed; for simplicity, let us just talk about covariant functors for the moment.

This point is actualized by the notion of a natural transformation. Given two functors  $F_1, F_2$  from  $C_1$  to  $C_2$ , a natural transformation of  $F_1$  to  $F_2$  consists of, for each  $X \in \text{Obj}(C_1)$ , a morphism  $\phi_X : F_1(X) \to F_2(X)$  such that for every morphism  $f \in \text{Hom}(X, Y)$ , the diagram

$$F_1(X) \xrightarrow{F_1(f)} F_1(Y)$$

$$\downarrow^{\phi_X} \qquad \downarrow^{\phi_Y}$$

$$F_2(X) \xrightarrow{F_2(f)} F_2(Y)$$

is commutative (that is, if you trace around both ways you get the same answer). Natural transformations can be composed; one with an inverse (equivalently, in which the morphisms  $\phi_X$  are all isomorphisms) is called a *natural isomorphism*. For instance, the functors taking ordered triples  $(M_1, M_2, M_3)$  of modules over a ring R to

$$(M_1 \otimes_R M_2) \otimes_R M_3$$
 and  $M_1 \otimes_R (M_2 \otimes_R M_3)$ 

are naturally isomorphic.

### 5 Other properties of functors

A functor is faithful if the maps  $F_{X,Y}$  are injective. Typical examples of these are "forgetful" functors, in which you start with a category of objects carrying a lot of structure, and the functor strips off some structure. E.g., take groups to their underlying sets, or take rings to their additive groups, or take topological groups to their underlying topological spaces.

The analogues of injectivity and surjectivity for functors are:

- A functor is fully faithful if the maps  $F_{X,Y}$  are bijective. A typical example is the inclusion of a full subcategory (i.e., take some of the objects, and all of the morphisms between the chosen objects).
- A functor is essentially surjective if every object in  $C_2$  is isomorphic to an object of the form F(X) for some  $X \in \text{Obj}(C_1)$ .
- A functor is an *equivalence of categories* if it is fully faithful and essentially surjective. This is equivalent to the existence of a *quasi-inverse* functor, i.e., one for which the compositions in both directions are naturally isomorphic to the relevant identities.

A typical example from last semester: take the category of affine algebraic varieties over an algebraically closed field k. The functor  $\Omega$  computing regular functions is an equivalence between this category and (the opposite category of) finitely generated k-algebras which are reduced (have no nilpotent elements). One of the goals of schemes is to set up a similar equivalence between some sort of geometric objects and the category of all commutative unital rings.

# 6 Representable functors, Yoneda's lemma, and universal properties

An individual object in a category casts a sort of shadow on the entire category, via the notion of representable functors. For a fixed object X in a category C, let  $h_X$  be the functor from C to Set such that  $h_X(Y) = \text{Hom}(X,Y)$ , and the image of  $f \in \text{Hom}(Y,Z)$  under  $h_X$  carries Hom(X,Y) to Hom(Y,Z) via postcomposition with f.

It turns out that any natural transformation from  $h_X$  to any other functor  $F: \mathcal{C} \to \operatorname{Set}$  is determined by specifying the image of the special element  $\operatorname{id}_X$  of  $\operatorname{Hom}(X,X) = h_X(X)$ , and conversely any such choice induces a natural transformation from  $h_X$  to F. This is *Yoneda's lemma*; proof is left as an (easy) homework problem.

An arbitrary functor  $F: \mathcal{C} \to \text{Set}$  is representable if it is naturally isomorphic to  $h_X$  for some X. By Yoneda's lemma, if X and Y represent the same functor, then they are isomorphic in a "natural" way (i.e., one compatible with the action of the functor).

In practice, this is usually interpreted as saying that an object of a category determined by a universal mapping property is unique up to unique isomorphism (or up to natural isomorphism). Here is an example of this which will help explain why categorical thinking is so helpful when dealing with schemes. For objects X, Y in a category C, an (absolute) product of X and Y is an object Z equipped with maps  $Z \to X$  and  $Z \to Y$ , with the following universal mapping property. Given any object W and morphisms  $W \to X$  and  $W \to Y$ , there must be a unique morphism  $W \to Z$  such that the diagram

commutes. The product is unique in the sense that if Z' is an other object equipped with morphisms  $Z' \to X$  and  $Z' \to Y$  satisfying the mapping property, there is a unique isomorphism  $Z \to Z'$  making everything commute.

In any "normal" category, in which objects are sets equipped with some extra structure (e.g., groups, topological groups), products exist and can be written as Cartesian products with some appropriate extra structure. But in general, products need not exists, and even if they do they might look weird. Case in point: suppose we tried to make a theory of abstract algebraic varieties over the non-algebraically closed field  $\mathbb{Q}$ , in which the points are Galois orbits of points over  $\overline{\mathbb{Q}}$ . (This is close to what will happen with schemes, except that there will be some more points.) Then in the affine line, we have a variety consisting of the single orbit  $\{i, -i\}$ . The product of this with itself will then consist of the *two* orbits  $\{(i, i), (-i, -i)\}$  and  $\{(i, -i), (-i, i)\}$ .

#### 7 Limits and colimits

The universal mapping properties we will consider can all be wrapped into the following framework. Let  $\mathcal{C}, \mathcal{D}$  be two categories. A *diagram* on  $\mathcal{C}$  of type  $\mathcal{D}$  is just a functor from  $\mathcal{D}$  to  $\mathcal{C}$ .

Fix a diagram  $F: \mathcal{D} \to \mathcal{C}$ . Let  $\mathcal{D}'$  be the category formed from  $\mathcal{D}$  by adding one extra object I with a unique morphism to every object in  $\mathcal{D}'$  (and the obvious composition law). Now look at extensions of F to functors  $\mathcal{D}' \to \mathcal{C}$ ; that is, you have to add one object X of  $\mathcal{C}$  and maps  $X \to F(Y)$  for each  $Y \in \mathcal{D}$  which commute with the maps coming from the diagram. A *limit* of F is a universal set of such data, i.e., any other extension factors uniquely through this one. My example of a product is the case where  $\mathcal{D}$  consists of two objects and no morphisms.

Define *colimits* as limits in the opposite category. For example, the co-analogue of the product is the *coproduct*. In Set, the product is the Cartesian product, while the coproduct is the disjoint union.

Important special case: a directed set is a partially ordered set in which any two elements have a common upper bound. (I.e., for any x, y, there is some z with  $x \leq z, y \leq z$ . A diagram from a directed set into some category  $\mathcal{C}$  is called a direct system; a colimit of a direct system is called a direct limit, or an inductive limit, in  $\mathcal{C}$ . (It should be called a direct/inductive colimit. Sorry about that.) For example, take the natural numbers under divisibility; then the direct limit of the abelian groups  $\frac{1}{n}\mathbb{Z}$  is the group  $\mathbb{Q}$ .

A diagram from the opposite of a directed set into some category C is called an *inverse* system; a colimit of an inverse system is called an *inverse limit* (or *projective limit*). For example, view the nonnegative integers as a partially ordered set using the reverse of the usual ordering. Then for any ring R, the inverse limit of the rings  $R[x]/(x^n)$  is the ring R[x] of formal power series. (A similar example is the p-adic numbers.)

### 8 Adjoint functors

One other notion that comes up a lot is that of an *adjoint pair of functors*, which you might like to think of as category-theoretic analogues of a linear operator and its transpose.

Let  $\mathcal{C}, \mathcal{D}$  be categories. A pair of functors  $F^* : \mathcal{C} \to \mathcal{D}$  and  $F_* : \mathcal{D} \to \mathcal{C}$  form an adjoint pair if we can form bijections

$$\operatorname{Hom}_{\mathcal{C}}(F^*X,Y) \to \operatorname{Hom}_{\mathcal{D}}(X,F_*Y)$$

which are functorial in X and Y (imagine the diagrams yourself). In this relationship,  $F^*$  is the *left adjoint* and  $F_*$  is the *right adjoint*.

The notation was chosen because the adjoint pairs we will use correspond to operations of promotion and demotion between two categories, one of which has more structured objects than the other. Here is a typical example. Let  $F_*: Ab \to Set$  be the forgetful functor on abelian groups. Let  $F^*: Set \to Ab$  be the functor carrying a set S to the free abelian group generated by S. Then  $F^*$  and  $F_*$  form an adjoint pair.

Another important example for us: let  $R \to S$  be a homomorphism of rings. Let  $F^*$ :  $\operatorname{Mod}_R \to \operatorname{Mod}_S$  be the functor  $M \mapsto M \otimes_R S$ . Let  $F_*$ :  $\operatorname{Mod}_S \to \operatorname{Mod}_R$  be the functor given by restriction of scalars from S to R. Then  $F^*$  and  $F_*$  form an adjoint pair.

We can of course compose  $F^*$  and  $F_*$  both ways, and we don't in general get the identity, or even something naturally isomorphic to the identity. We do get something interesting, though. The identity map on  $F^*X$  corresponds to a morphism  $X \to F_*F^*X$ , while the identity map on  $F_*Y$  corresponds to a morphism  $F^*F_*Y \to Y$ . These morphisms are called adjunction morphisms. For example, in the previous example, for X an R-module,  $X \to F_*F^*X = X \otimes_R S$  is the map  $X \mapsto X \otimes Y$  is the map  $X \mapsto X \otimes Y \otimes Y \otimes Y \otimes Y \otimes Y \otimes Y \otimes Y \otimes Y \otimes Y \otimes$

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Sheaves (updated 12 Feb 09)

We are now ready to introduce the basic building block in the theory of schemes, the notion of a *sheaf*. See also: Hartshorne II.1, EGA 1 0.3. (The latter means: look in the "Chapitre 0" section of EGA volume 1.) The base reference for this bit of EGA is Godement, *Théorie des Faisceaux*.

Note that Hartshorne assumes all sheaves take values in the category of abelian groups, that being the case of most interest in algebraic geometry. I will only impose that restriction in the next lecture.

#### 1 Presheaves

Fix a category  $\mathcal{C}$ , e.g., sets or abelian groups. Given a topological space X, let  $\underline{X}$  be the category of open sets of X. A *presheaf* on X with values in  $\mathcal{C}$  is a contravariant functor  $\mathcal{F}: \underline{X} \to \mathcal{C}$ . the category of open sets of X to  $\mathcal{C}$ . In other words, to specify a sheaf  $\mathcal{F}$  on X, you must specify:

- (a) for each open subset U of X an element  $\mathcal{F}(U) \in \mathcal{C}$ ;
- (b) for each inclusion  $V \subseteq U$  of open subsets of X a morphism  $\operatorname{Res}_{U,V} = \operatorname{Res}_{U,V}(\mathcal{F})$ :  $\mathcal{F}(U) \to \mathcal{F}(V)$  (called restriction), such that:
  - (i) for each open subset U of X,  $Res_{U,U} = id_{\mathcal{F}(U)}$ ;
  - (ii) for each series of inclusions  $W \subseteq V \subseteq U$  of open subsets of X, we have  $\operatorname{Res}_{V,W} \circ \operatorname{Res}_{U,V} = \operatorname{Res}_{U,W}$  within  $\operatorname{Hom}(U,W)$ .

There seems to be some confusion over whether it is required that  $\mathcal{F}(\emptyset)$  is required to be a final object of  $\mathcal{C}$ ; Hartshorne's two characterizations of presheaves disagree on this point (because the definition of a functor doesn't include this condition). Fortunately, this doesn't have any serious consequences; the definition of a sheaf will stamp out this ambiguity. (EGA avoids this issue by omitting the definition of a presheaf entirely!)

We will typically use this definition in cases where  $\mathcal{C}$  carries a forgetful functor to <u>Set</u>. In that case, it makes sense to speak of the elements of  $\mathcal{F}(U)$  for U an open subset of X; we call these elements the *sections* of  $\mathcal{F}$  on U. For  $V \subseteq U$  an inclusion of open sets, and  $s \in \mathcal{F}(U)$ , we often write  $s|_V$  instead of  $\text{Res}_{U,V}(s)$ .

The restriction of a presheaf  $\mathcal{F}$  on X to an open subset U of X is defined in the obvious fashion. It is denoted  $\mathcal{F}|_{U}$ . It is also called the *induced presheaf* of  $\mathcal{F}$  on U.

If  $\mathcal{F}_1, \mathcal{F}_2 : \underline{X} \to \mathcal{C}$  are both presheaves on a topological space X with values in a category  $\mathcal{C}$ , a morphism  $\mathcal{F}_1 \to \mathcal{F}_2$  of presheaves is a natural transformation of functors from  $\mathcal{F}_1$  to  $\mathcal{F}_2$ , i.e., a collection of maps  $\mathcal{F}_1(U) \to \mathcal{F}_2(U)$  compatible with restrictions.

## 2 Sheaves

Here is an example of a set-valued presheaf  $\mathcal{F}$ : take another topological space Y, and put  $\mathcal{F}(U) = \operatorname{Hom}_{\operatorname{Top}}(U,Y)$  (the continuous functions from U to Y) with restriction being the usual restriction of functions. This example has a special feature not implied by the definition of a presheaf: a continuous function can be specified *locally*. In other words, for any index set I, if  $\{V_i\}_{i\in I}$  is a family of open sets with union U, then on one hand, each element of  $\mathcal{F}(U)$  is uniquely determined by its restrictions to all of the  $V_i$ ; and on the other hand, any family of elements of  $\mathcal{F}(V_i)$  which agree on the overlaps of the  $V_i$  gives a section over U.

This is formalized by the notion of a *sheaf*. A sheaf on X with values in C is a presheaf with the following property (called the *sheaf axiom*).

**Axiom** (Sheaf axiom). For any index set I, for any family of open sets  $\{V_i\}_{i\in I}$  which form a cover of the open set U, the object  $\mathcal{F}(U)$  is the limit of the diagram formed by the  $\mathcal{F}(V_i)$  for  $i \in I$ , the  $\mathcal{F}(V_i \cap V_j)$  for  $i, j \in I$ , and the arrows  $\text{Res}_{V_i, V_i \cap V_j}$  for  $i, j \in I$ .

Let us make this explicit in case  $\mathcal{C} = \underline{\text{Set}}$ . Define  $I, U, V_i$  as in the sheaf axiom.

- (i) If  $s_1, s_2 \in \mathcal{F}(U)$  is such that  $s_1|_{V_i} = s_2|_{V_i}$  for all i, then  $s_1 = s_2$ . (If  $\mathcal{C} = \underline{Ab}$ , we can just check this for  $s_2 = 0$ .)
- (ii) Suppose we are given for each  $i \in I$ , an element  $s_i \in \mathcal{F}(V_i)$  such that for each  $i, j \in I$ ,  $s_i|_{V_i \cap V_j} = s_j|_{V_i \cap V_j}$ . Then there exists an element  $s \in \mathcal{F}(U)$  such that  $s|_{V_i} = s_i$  for each i. (The element s is unique by (i).)

We define restriction of sheaves, and morphisms of sheaves, by copying the definitions from presheaves.

Some examples of sheaves:

- On a manifold, the continuous functions to some fixed topological space. Special example: if you take a target space C equipped with the discrete topology, you get what's called the *locally constant sheaf* associated to C.
- On a differentiable manifold, the differentiable functions.
- On a complex manifold, the holomorphic functions.
- On an abstract algebraic variety over an algebraically closed field, the regular functions, or the differential forms.

These all come from a class of objects called *locally ringed spaces*, which we will discuss later. Although sheaves can be defined to take values in an arbitrary category, we will only be interested in cases where the category consists of objects with well-defined elements, and all the glueing is determined by the elements. So to keep things simple, let me drop in a hypothesis that I would like to keep in place from now on. (With only limits, Grothendieck calls this hypothesis (E). However, we'll want the colimits in order to talk about stalks later.)

**Hypothesis** (E). Assume hereafter that all sheaves under discussion take values in a fixed category  $\mathcal{C}$  which admits a forgetful functor to <u>Set</u> that *reflects small limits and colimits*. That is, all small (indexed by sets) limits exist, and their formation commutes with passage to <u>Set</u>.

For example,  $\mathcal{C}$  could be <u>Set</u> itself. It could also be any one of the usual "algebraic" categories: <u>Ab</u>, <u>Grp</u>, <u>Ring</u>, <u>Mod</u><sub>R</sub> for a ring R, etc. Under this hypothesis, the sheaf axiom for  $\mathcal{C}$  is exactly as for <u>Set</u>, so a presheaf is a sheaf if and only if it becomes a sheaf after composing with the forgetful functor. We can thus forget the extra structure of  $\mathcal{C}$  when checking basic facts about sheaves.

A typical bad example is <u>Top</u>; the basic problem is that the image of a morphism under the forgetful functor can be an isomorphism even if the original morphism is not. That is, a continuous bijection of topological spaces need not be a homeomorphism.

Here is a trick for dealing with bad cases: given a presheaf  $\mathcal{F}$  on X, for each object  $Y \in \mathcal{C}$ , let  $\mathcal{F}_Y$  be the presheaf on X with values in <u>Set</u> defined by  $U \mapsto \operatorname{Hom}(Y, \mathcal{F}(U))$ . Then  $\mathcal{F}$  is a sheaf if and only if each  $\mathcal{F}_Y$  is a sheaf.

# 3 Defining sheaves on a basis

It is very often convenient not to have to explicitly specify the sections of a sheaf on every open subset, but simply on a basis of open sets. Recall that a *basis* (of open sets) in a topological space X is a collection of open sets such that every open set can be written as a union of elements of the basis.

Let X be a topological space, and let  $\underline{X}$  be the category of open sets of X. Let B be a basis of X, and let  $\underline{B}$  be the full subcategory of  $\underline{X}$  with  $\mathrm{Obj}(\underline{B}) = B$ . (That is, keep all of the morphisms.) A presheaf on X specified on B is a contravariant functor from  $\underline{B}$  to  $\mathcal{C}$ . A sheaf on X specified on B is a presheaf  $\mathcal{F}$  on X specified on B, such that  $\mathcal{F}$  satisfies the following modified sheaf axiom.

**Axiom** (Sheaf axiom for a basis). For any index set I, for any  $U \in B$  and any family of open sets  $\{V_i\}_{i\in I}$  in B which form a cover of U, we can choose a covering  $\{W_{ijk}\}_{k\in J_{i,j}}$  of each  $V_i \cap V_j$  such that the object  $\mathcal{F}(U)$  is the limit of the diagram formed by the  $\mathcal{F}(V_i)$  for  $i \in I$ , the  $\mathcal{F}(W_{ijk})$  for  $i, j \in I$  and  $k \in J_{i,j}$ , and the arrows  $\operatorname{Res}_{V_i,W_{ijk}}$  for  $i, j \in I$  and  $k \in J_{i,j}$ .

For example, suppose B is a basis in which the intersection of any two basic opens is a basic open; Ravi Vakil calls this a *nice* basis, so I will too. For a nice basis, this follows from the sheaf axiom applied to coverings of basic opens by other basic opens, because you just take the trivial covering of  $V_i \cap V_j$  by itself. (The niceness condition is satisfied in most of our examples.)

**Lemma** (Basis lemma). Any sheaf on X specified on B extends uniquely to a sheaf on X. Similarly, any morphism between two sheaves on X specified on B extends to a morphism of sheaves on X.

In other words, the restriction functor from sheaves on X to sheaves on X specified on B is an equivalence of categories.

Proof. Let  $\mathcal{F}'$  be the presheaf defined by taking  $\mathcal{F}(U)$  to be the limit of the diagram formed by the  $\mathcal{F}(V)$  (and the restriction maps) for all basic opens V contained in U. If U is a basic open, then the construction comes with a map  $\mathcal{F}'(U) \to \mathcal{F}(U)$  which defines a morphism of presheaves specified on B. Also, the limit property also defines the restriction maps  $\operatorname{Res}_{U,V}: \mathcal{F}'(U) \to \mathcal{F}'(V)$  whenever  $V \subseteq U$  are arbitrary opens, since  $\mathcal{F}'(U)$  maps to  $\mathcal{F}(W)$  for any basic open W contained in V. By a similar argument, any morphism  $\mathcal{F} \to \mathcal{G}$  of presheaves induces a morphism  $\mathcal{F}' \to \mathcal{G}'$ .

What is left to check that on one hand the map  $\mathcal{F}'(U) \to \mathcal{F}(U)$  is an isomorphism, and on the other hand  $\mathcal{F}'$  satisfies the sheaf axiom. We leave these as exercises.

As a corollary, we learn how to glue sheaves together.

**Corollary.** Let I be an index set and let  $\{U_i\}_{i\in I}$  be an open cover of X. Suppose we are given the following data.

- (a) For each  $i \in I$ , a sheaf  $\mathcal{F}_i$  on  $U_i$  with values in  $\mathcal{C}$ .
- (b) For each  $i, j \in I$ , an isomorphism  $\theta_{ij} : \mathcal{F}_i|_{U_i \cap U_j} \cong \mathcal{F}_j|_{U_i \cap U_j}$ , satisfying the following conditions.
  - (i) For each  $i \in I$ ,  $\theta_{ii}$  is the identity morphism on  $\mathcal{F}_i$ .
  - (ii) For each  $i, j, k \in I$ , we have  $\theta_{jk} \circ \theta_{ij} = \theta_{ik}$  as morphisms of sheaves on  $U_i \cap U_j \cap U_k$ . (This is called the cocycle condition, for reasons to be discussed later.)

Then there exist a sheaf  $\mathcal{F}$  on X and isomorphisms  $\theta_i : \mathcal{F}|_{U_i} \cong \mathcal{F}_i$  for each  $i \in I$ , such that for each  $i, j \in I$ ,  $\theta_{ij} \circ \theta_i = \theta_j$ . Moreover,  $\mathcal{F}$  is unique up to unique isomorphism (in a sense to be interpreted by the reader).

You might describe this by saying that "a sheaf of sheaves is a sheaf." In fact, this is the same sort of data needed to glue, say, topological spaces.

*Proof.* Suppose we are in the happy situation where whenever an open set U of X belongs to both  $V_i$  and  $V_j$ , we have a literal equality  $\mathcal{F}_i(U) = \mathcal{F}_j(U)$  and the map  $\theta_{ij}$  between these two is the identity morphism. (Note that the cocycle condition is automatically valid here.) Then we can apply the basis lemma, where B is the (nice) basis consisting of those open sets U contained in  $U_i$  for at least one index i.

The trouble is that as usual, objects in a category are usually not equal. However, using the cocycle condition we can force them to become equal as follows. Define a functor  $\mathcal{F}: \underline{B} \to \mathcal{C}$  as follows. For  $U \in B$ , pick an index i = i(U) such that  $U \subseteq U_i$ , and put  $\mathcal{F}(U) = \mathcal{F}_i(U)$ . For an inclusion  $V \subseteq U$  of elements of B, put i = i(U) and j = i(V), so that V is contained in both  $U_i$  and  $U_j$ . Define  $\text{Res}_{U,V}(\mathcal{F})$  as the composition of the restriction map  $\text{Res}_{U,V}(\mathcal{F}_i): \mathcal{F}_i(U) \to \mathcal{F}_i(V)$  with the map  $\theta_{ij}: \mathcal{F}_i(V) \to \mathcal{F}_j(V)$ . The cocycle condition

then implies that these restriction maps are associative, so they define a presheaf  $\mathcal{F}$  specified on B. The fact that each  $\mathcal{F}_i$  is a sheaf implies that  $\mathcal{F}$  is a sheaf specified on B, so it extends to a sheaf.

#### 4 Stalks

An important source of information about sheaves is given by looking at their behavior "in the neighborhood of a point", as follows.

First let us recall something about direct limits. (Warning: I had the terminology slightly wrong when I introduced this in the category theory lecture. The notes have been corrected.) A directed set is a partially ordered set in which any two elements have an upper bound (but not necessarily a least upper bound). A direct system in a category  $\mathcal{C}$  is a covariant functor  $F: P \to \mathcal{C}$  with P a directed set. If the colimit exists, it is called the direct limit of the system.

Before using this notion for much, it might be helpful to make it explicit in the case of sets. (The case of abelian groups, which we also use, works the same way.) In this case, the direct limit is formed by starting with the union of F(S) over all  $S \in P$ , then identifying the elements  $x \in F(S)$  and  $y \in F(T)$  if there exist arrows  $f: S \to U$  and  $g: T \to U$  in P such that F(f)(x) = F(g)(y). A typical example is the formation of the fraction field Frac(R) of an integral domain R, as the direct limit of the rings R[x]/(xf-1) over all nonzero  $f \in R$ . Here the poset is the nonzero elements of R ordered under divisibily, and the map from R[x]/(xf-1) to R[x]/(xfg-1) takes x to xg.

Now let  $\mathcal{F}$  be a presheaf on the topological space X, and let  $x \in X$  be any point. View the open subsets of X containing x as a partially ordered set  $P_x$  under *reverse* inclusion. They then form a directed set, and the direct limit of the functor  $\mathcal{F}: P_x \to \mathcal{C}$  is called the *stalk* of  $\mathcal{F}$ , denoted  $\mathcal{F}_x$ .

The elements of a stalk (which exist because we assumed (E)) are typically called *germs*. If s is a section of a sheaf on an open set containing x, we write  $s_x$  for the germ of s at x.

Example: the stalk of the sheaf of real-valued continuous functions consists of germs of real-valued continuous functions. Two continuous functions defined on open subsets of X containing a point x determine the same germ at x if and only if they coincide on some open subset containing x.

We can make a similar construction for the other "functions on manifolds" examples above. Beware that in these examples, the germ of a function at a point carries much more information than the *value* at that point. Extreme example: two holomorphic functions defined on a *connected* complex manifold have the same germ at a single point if and only if they coincide (because of analytic continuation!).

One variant we'll need a bit later: given any subset Z of X, not necessarily a single point, we can similarly take the direct limit of  $\mathcal{F}(U)$  over all open subsets U of X containing Z. We call this the stalk of X at Z.

# 5 Stalks and morphisms

Stalks can be used to detect lots of interesting properties of sheaves, particularly in relation to morphisms. Throughout this section, let  $\phi : \mathcal{F}_1 \to \mathcal{F}_2$  be a morphism of sheaves on a topological space X.

**Lemma.** Consider the following conditions.

- (a) For each  $x \in X$ , the map  $\phi_x : \mathcal{F}_{1,x} \to \mathcal{F}_{2,x}$  is injective/surjective/bijective.
- (b) For each open subset U of X, the map  $\phi(U): \mathcal{F}_1(U) \to \mathcal{F}_2(U)$  is injective/surjective/bijective.

Then (b) implies (a) in all cases, while (a) implies (b) in the injective and bijective cases.

*Proof.* Suppose (a). Let  $Y_i$  be the product of  $\mathcal{F}_{i,x}$  over all  $x \in U$ . Then the sheaf axiom implies that the map  $\mathcal{F}_i(U) \to Y_i$  carrying s to  $\prod_x s_x$  is injective. This gives injectivity in (b). (This is a toy example of the construction of the *espace étale* of a sheaf; I asked more about it on Problem Set 1.)

If  $\phi_x$  is bijective for all x, then for any section  $t \in \mathcal{F}_2(U)$  and any  $x \in U$ , there is an open neigborhood  $V = V_x$  of x on which t coincides with the image under  $\phi$  of some section  $s_x \in \mathcal{F}_1(V_x)$ . For  $y \in U$  also, the restrictions of  $s_x$  and  $s_y$  to  $\mathcal{F}_1(V_x \cap V_y)$  have the same image under  $\phi$  (namely the restriction of t to  $\mathcal{F}_2(V_x \cap V_y)$ ), so they coincide by what we proved in the previous paragraph. We can thus invoke the sheaf axiom to assemble  $s \in \mathcal{F}_1(U)$  with  $\phi(s) = t$ . so surjectivity/bijectivity in (b) is an easy consequence.

Suppose (b). The surjectivity aspect is more or less obvious, so we only check the injectivity aspect. Suppose we are given two elements of  $\mathcal{F}_{1,x}$  with the same image in  $\mathcal{F}_{2,x}$ . We can represent these by sections  $s_1, s_2$  of  $\mathcal{F}_1$  on some open neighborhood of x. In fact, we can take them on the same open neighborhood U. Their images are sections of  $\mathcal{F}_2$  which have the same image in  $\mathcal{F}_{2,x}$ . That means that we can replace U by some smaller open neighborhood V so that  $\phi(s_1)$  and  $\phi(s_2)$  coincide in  $\mathcal{F}_2(V)$ . But then  $s_1 = s_2$  in  $\mathcal{F}_1(V)$ , so (a) holds.

We define a morphism of sheaves to be *injective/surjective/bijective* if it has the corresponding property on stalks. By the previous lemma, bijective is the same as being an isomorphism (in the sense of having an inverse).

The disturbing thing is of course the failure of the implication from (a) to (b) in the surjectivity case. Yes, a morphism of sheaves can be surjective without being surjective on sections! What is true is: if  $\phi$  is surjective and U is an open in X, then for each  $s \in \mathcal{F}_2(U)$ , we can cover U with open subsets  $V_i$  such that  $\text{Res}_{U,V_i}(s)$  is in the image of  $\phi(V_i)$  for each i. The trouble is that you may not be able to choose elements of the  $\mathcal{F}_1(V_i)$  which can be glued.

Here is a familiar example. Put  $X = \mathbb{C} \setminus \{0\}$ . Let  $\mathcal{F}_1$  be the sheaf of holomorphic functions on X. Let  $\mathcal{F}_2$  be the sheaf of nowhere vanishing holomorphic functions on X. Let  $\phi: \mathcal{F}_1 \to \mathcal{F}_2$  be the map taking  $f: U \to \mathbb{C}$  to  $\exp \circ f$ . Then  $\phi$  is surjective because the logarithm of a nonzero holomorphic function exists locally, but not globally: the function  $z \in \mathcal{F}_2(X)$  is not in the image of  $\phi(X)$ .

## 6 Sheafification

If we fix a topological space X and a category C, there is an obvious forgetful functor from sheaves on X with values in C to presheaves on X with values in C. If you properly digested the notion of an adjoint functor, you should be asking whether this forgetful functor occurs as the right adjoint in an adjoint pair. It does!

Let  $\mathcal{F}: \underline{X} \to \mathcal{C}$  be a presheaf on X with values in  $\mathcal{C}$ . Define another presheaf  $\mathcal{F}^+$  on X as follows. For  $U \subseteq X$  open, take  $\mathcal{F}^+(U)$  to be the subset of  $\prod_{x \in U} \mathcal{F}_x$  consisting of elements  $s = \prod_x s_x$  with the following property: for each  $x \in U$ , there exists an open neighborhood V of x in U and a section  $t \in \mathcal{F}(V)$  such that  $s_y = t_y$  for all  $y \in V$ . From the definition, it is easy to check that  $\mathcal{F}^+$  is a sheaf and that its stalk  $\mathcal{F}^+_x$  is canonically isomorphic to  $\mathcal{F}_x$ . We call  $\mathcal{F}^+$  the sheafification of  $\mathcal{F}$ ; its construction is functorial in  $\mathcal{F}$ .

**Proposition.** The functor  $\mathcal{F} \mapsto \mathcal{F}^+$  from presheaves on X to sheaves on X, and the forgetful functor from sheaves on X to presheaves on X, form an adjoint pair.

Proof. Exercise.  $\Box$ 

# 7 Direct and inverse image

Let  $f: X \to Y$  be a continuous map. For  $\mathcal{F}$  a sheaf on X, the formula

$$(f_*\mathcal{F})(V) = \mathcal{F}(f^{-1}(V))$$

obviously defines a sheaf  $f_*\mathcal{F}$  on Y. It is called the *direct image* of  $\mathcal{F}$ .

Now let  $\mathcal{G}$  be a sheaf on Y. Define a presheaf  $f_{-}^{-1}\mathcal{G}$  on X as follows: for U open in X, let  $(f_{-}^{-1}\mathcal{G})(U)$  be the stalk of  $\mathcal{G}$  at f(U), i.e., the direct limit of  $\mathcal{G}(V)$  over open sets  $V \subseteq X$  containing f(U). This is general not a sheaf; its sheafification is called the *inverse image* of  $\mathcal{G}$ , denoted  $f^{-1}\mathcal{G}$ .

**Proposition.** The functors  $f^{-1}$  and  $f_*$  form an adjoint pair.

Proof. Exercise.  $\Box$ 

You might wonder why I didn't use the notation  $f^*$  for the inverse image. That is because I will need that notation later for a different functor, defined for a morphism of ringed spaces.

Using the inverse image, we can define the restriction of  $\mathcal{F}$  to an arbitrary subset Z of X, as the sheaf  $i^{-1}\mathcal{F}$  for  $i:Z\to X$  the inclusion map (with Z given the subspace topology). If  $Z=\{x\}$ , this coincides with the stalk  $\mathcal{F}_x$  (exercise).

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) More on abelian sheaves

We now specialize the discussion of sheaves to the situation where the target category consists of abelian groups. At the end, I'll explain how to generalize to the case of a target which is an *abelian category*.

#### 1 Abelian groups

Assume until I say otherwise that  $C = \underline{Ab}$ . (At the end, we'll generalize to the case where C can be any abelian category.) Let me first set some notation and terminology about morphisms of abelian groups themselves.

For  $f: A \to B$  a morphism of abelian groups,

$$\ker(f) = \{x \in A : f(x) = 0\}$$
$$\operatorname{im}(f) = \{f(x) : x \in A\}$$
$$\operatorname{coker}(f) = A/\operatorname{im}(f) = \{y + \operatorname{im}(f) : y \in B\}.$$

A (finite or infinite) sequence

$$\cdots \to A_{i-1} \to A_i \to A_{i+1} \to \cdots$$

in Ab is exact if for each i,

$$\operatorname{im}(A_{i-1} \to A_i) = \ker(A_{i+1} \to A_i).$$

If we only have the weaker assertion that

$$\operatorname{im}(A_{i-1} \to A_i) \subseteq \ker(A_{i+1} \to A_i)$$

(i.e., the composition  $A_{i-1} \to A_i \to A_{i+1}$  is zero) for each i, we say that the sequence is a *complex*.

Here are some useful facts about exact sequences; their proofs are fun exercises in what is sometimes called *diagram chasing*. Remember that in <u>Ab</u>, monomorphism equals injective and epimorphism equals surjective (so mono plus epi equals iso, which is not true in an arbitrary category).

**Lemma** (Five lemma). Let

$$A_0 \longrightarrow A_1 \longrightarrow A_2 \longrightarrow A_3 \longrightarrow A_4$$

$$\downarrow f_0 \qquad \qquad \downarrow f_1 \qquad \qquad \downarrow f_2 \qquad \qquad \downarrow f_3 \qquad \qquad \downarrow f_4$$

$$B_0 \longrightarrow B_1 \longrightarrow B_2 \longrightarrow B_3 \longrightarrow B_4$$

be a commuting diagram in C with exact rows.

- (a) If  $f_1$  and  $f_3$  are monomorphisms and  $f_0$  is an epimorphism, then  $f_2$  is a monomorphism.
- (b) If  $f_1$  and  $f_3$  are epimorphisms and  $f_4$  is a monomorphism, then  $f_2$  is an epimorphism.

Proof. Exercise. 
$$\Box$$

Lemma (Snake lemma). Let

$$0 \longrightarrow A_1 \longrightarrow A_2 \longrightarrow A_3 \longrightarrow 0$$

$$\downarrow f_1 \qquad \downarrow f_2 \qquad \downarrow f_3$$

$$0 \longrightarrow B_1 \longrightarrow B_2 \longrightarrow B_3 \longrightarrow 0$$

be a short exact sequence. Then there exists a canonical homomorphism  $\delta : \ker(f_3) \to \operatorname{coker}(f_1)$  (the connecting homomorphism) such that

$$0 \to \ker(f_1) \to \ker(f_2) \to \ker(f_3) \xrightarrow{\delta} \operatorname{coker}(f_1) \to \operatorname{coker}(f_2) \to \operatorname{coker}(f_3) \to 0$$

is exact, where all the maps other than  $\delta$  are the obvious ones induced by the diagram.

*Proof.* Here is what  $\delta$  is supposed to be: given  $a_3 \in \ker(f_3)$ , lift it to  $a_2 \in A_2$ , then apply  $f_2$  to get  $b_2 \in B_2$ . Since the diagram commutes,  $b_2$  must map to zero in  $B_3$ , so it lifts to  $b_1$  in  $B_1$ . Declare  $\delta(a_3) = b_1$ .

It remains to show that  $\delta$  is well-defined and is a homomorphism, and that the claimed sequence is exact. These are left as exercises.

Corollary (Short five lemma). Let

$$0 \longrightarrow A_1 \longrightarrow A_2 \longrightarrow A_3 \longrightarrow 0$$

$$\downarrow^{f_1} \qquad \downarrow^{f_2} \qquad \downarrow^{f_3}$$

$$0 \longrightarrow B_1 \longrightarrow B_2 \longrightarrow B_3 \longrightarrow 0$$

be a commuting diagram in C with exact rows. Then  $f_2$  is a monomorphism/epimorphism if and only if  $f_1$  and  $f_3$  both are.

## 2 Exact functors

For  $C_1 = C_2 = \underline{Ab}$ , a covariant functor  $F : C_1 \to C_2$  is additive if it commutes with addition of morphisms. Any additive functor sends complexes to complexes (because the property of the composition of two maps being zero is preserved), but not necessarily exact sequences to exact sequences. Hence the following definitions.

We say F is *left exact* if for any exact sequence

$$0 \to A_1 \to A_2 \to A_3$$

the sequence

$$0 \to F(A_1) \to F(A_2) \to F(A_3)$$

is exact. We say F is right exact if for any exact sequence

$$A_1 \rightarrow A_2 \rightarrow A_3 \rightarrow 0$$

the sequence

$$F(A_1) \to F(A_2) \to F(A_3) \to 0$$

is exact. We say F is exact if it is both left exact and right exact; equivalently, for any exact sequence

$$0 \to A_1 \to A_2 \to A_3 \to 0$$

the sequence

$$0 \to F(A_1) \to F(A_2) \to F(A_3) \to 0$$

It in turn implies that any exact sequence of any length goes into another exact sequence under F. (I'll try avoid using these notions for contravariant functors, since there is a left/right ambiguity.)

Examples:

- For any given  $X \in \mathcal{C}$ , the covariant functor  $\operatorname{Hom}(X,\cdot)$  is left exact.
- For any given  $X \in \mathcal{C}$ , the covariant functor  $X \otimes \cdot$  is right exact.

Many left/right exact functors arise from the following proposition.

**Proposition.** Suppose the covariant functors  $f^*: \mathcal{C}_1 \to \mathcal{C}_2$  and  $f_*: \mathcal{C}_2 \to \mathcal{C}_1$  form an adjoint pair. Then  $f^*$  is right exact and  $f_*$  is left exact.

Proof. Exercise. 
$$\Box$$

### 3 Abelian sheaves

Let  $\mathcal{F}$  be a sheaf on a topological space X with values in  $\mathcal{C} = \underline{\mathrm{Ab}}$ . A subsheaf of  $\mathcal{F}$  is what you think: take a subset of the sections on each open so that you still have a sheaf. The quotient of  $\mathcal{F}$  by a subsheaf  $\mathcal{G}$  is a bit trickier: take the presheaf  $U \mapsto \mathcal{F}(U)/\mathcal{G}(U)$ , then sheafify. Note that the stalk at x is indeed  $\mathcal{F}_x/\mathcal{G}_x$ .

Given a morphism  $\phi : \mathcal{F} \to \mathcal{G}$  of sheaves, the presheaf  $U \mapsto \ker(\phi(U))$  is a sheaf; we call it the *kernel* of  $\phi$ . The presheaves  $U \mapsto \operatorname{im}(\phi(U))$  and  $U \mapsto \operatorname{coker}(\phi(U))$  are not in general sheaves; their sheafifications are called the *image* and *cokernel* of  $\phi$ .

**Proposition.** For  $x \in X$ , we have  $\ker(\phi)_x = \ker(\phi_x)$ ,  $\operatorname{im}(\phi)_x = \operatorname{im}(\phi_x)$ , and  $\operatorname{coker}(\phi)_x = \operatorname{coker}(\phi_x)$ . Consequently,

$$\operatorname{im}(\phi) \cong \mathcal{F}/\ker(\phi), \qquad \operatorname{coker}(\phi) \cong \mathcal{G}/\operatorname{im}(\phi).$$

*Proof.* Exercise.

Using these, we extend the notion of exactness to a sequence of sheaves; it's equivalent to define it using sheaves or stalks, but *not* using sections.

Let  $\underline{\operatorname{Sh}}_{\mathcal{C}}(X)$  be the category of sheaves on X with values in  $\mathcal{C}$ . We define the global sections functor  $\Gamma(\cdot,X):\underline{\operatorname{Sh}}_{\mathcal{C}}(X)\to\mathcal{C}$  by the formula

$$\Gamma(\mathcal{F}, X) = \mathcal{F}(X).$$

(No set-theoretic difficulties here:  $\underline{X}$  is a small category, so sheaves on X with values in  $\mathcal{C}$  do form a class.)

**Proposition.** The global sections functor is left exact.

Proof. Exercise. 
$$\Box$$

The failure of the global sections functor to be right exact will give rise to the notion of sheaf cohomology later.

## 4 Abelian categories

Everything I defined above can be generalized to the case where C is what is called an *abelian* category, i.e., a category which captures the useful properties of abelian groups.

First, let me give an *ad hoc* definition which will suffice for our purposes. A *nice abelian* category is an additive category in which all limits and colimits exist, together with a forgetful functor to <u>Ab</u> which preserves limits and colimits.

Next, let's figure out what the correct abstract definition shoul be. We first write down the definition of an *preadditive category* (which I called an *additive category* by mistake on Problem Set 1). That is a category  $\mathcal{C}$  equipped with the structure of an abelian group on each set Hom(X,Y), over which composition is distributive.

We next define an additive category. The key notion is that direct sum and direct product coincide for a finite collection of abelian groups. We should thus require the existence of biproducts: that is, for any  $X_1, \ldots, X_n \in \text{Obj}(\mathcal{C})$ , there must exist an object X equipped with maps  $\pi_i: X \to X_i$  and  $\iota_i: X_i \to X$ , such that X is both a product (using the  $\pi_i$ ) and a coproduct (using the  $\iota_i$ ), and the sum  $\iota_1 \circ \pi_1 + \cdots + \iota_n \circ \pi_n$  is the identity on X. (Exercise: this exists as soon as you have finite products.)

Since the empty biproduct exists, an additive category has a terminal (initial and final) object, which we call the zero object and label 0. In an additive category, we can define a kernel of the morphism  $f: X \to Y$  to be a limit of the diagram

i.e., an object W plus a morphism  $g: W \to X$  such that  $f \circ g = 0$ , and any other morphism  $h: V \to X$  for which  $f \circ h = 0$  factors uniquely through g. Similarly, a cokernel of f is a colimit of

To get a *preabelian category*, we insist that every morphism admit a kernel and cokernel (which as usual are only unique up to unique isomorphism). To get an *abelian category*, we insist that every monomorphism be the kernel of its cokernel, and every epimorphism be the cokernel of its kernel.

The Freyd-Mitchell embedding theorem asserts that at least for every small abelian category  $\mathcal{C}$ , we can construct an exact and fully faithful functor  $F:\mathcal{C}\to \operatorname{\underline{Mod}}_R$  for a not necessarily commutative ring R (where  $\operatorname{\underline{Mod}}_R$  now means left modules). This lets you prove theorems about abelian categories by reducing to situations where objects really do have elements.

The main difference between my nice abelian categories and true abelian categories is that I want *all* limits and colimits to exist. This is a bit strong for some purposes, but since I need limits anyway to work with sheaves, it's not so strange.

Anyway, the point here is that if you start with a (nice) abelian category  $\mathcal{C}$ , for any topological space X, the category  $\underline{\operatorname{Sh}}_{\mathcal{C}}(X)$  is again a (nice) abelian category. This follows by assembling various homework exercises.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Schemes

We next introduce locally ringed spaces, affine schemes, and general schemes. References: Hartshorne II.2, Eisenbud-Harris I.1, EGA 1.1.

## 1 Ringed and locally ringed spaces

A ringed space is a topological space X equipped with a sheaf  $\mathcal{O}_X$  on X with values in Ring (called the *structure sheaf*). This definition isn't so useful because it doesn't force the topology to have much to do with the ring structure; for instance, any ring can be viewed as a ringed space on a one-element topological space.

A more useful notion is that of a locally ringed space. This is a ringed space in which for each  $x \in X$ , the stalk  $\mathcal{O}_{X,x}$  of  $\mathcal{O}_X$  at x is a local ring, i.e., a ring with a unique maximal ideal  $\mathfrak{m}_{X,x}$ . (The zero ring is not a local ring!)

For example, suppose X is a manifold and let  $\mathcal{O}_X$  be the sheaf of real-valued continuous functions. We check that  $(X, \mathcal{O}_X)$  forms a locally ringed space. Given  $x \in X$ , let  $\mathfrak{m}_{X,x}$  be the ideal of  $\mathcal{O}_{X,x}$  consisting of germs of functions taking the value 0 at x. This is clearly an ideal, and the quotient  $\mathcal{O}_{X,x}/\mathfrak{m}_{X,x}$  is certainly contained in  $\mathbb{R}$ . Since X is a manifold, the quotient is nonzero, so  $\mathfrak{m}_{X,x}$  is indeed a maximal ideal of  $\mathcal{O}_{X,x}$ . To check that it is the unique maximal ideal, it suffices to check that any  $f \in \mathcal{O}_{X,x}$  not contained in  $\mathfrak{m}_{X,x}$  is a unit in  $\mathcal{O}_{X,x}$ . For such an f, f(x) is some nonzero real number, so we can find an open subinterval  $I \subseteq \mathbb{R}$  such that f(x) belongs to I but 0 does not. Represent f by a continuous function on some open subset U of X containing x, which I'll also call f. The key point is that by continuity,  $V = f^{-1}(I)$  is again an open subset of X containing x, and f takes nonzero values everywhere on V. Hence there exists a multiplicative inverse g of f on V, which is necessarily continuous.

Similarly, a smooth manifold, complex manifold, or abstract algebraic variety equipped with the obvious sheaf is a locally ringed space.

For any  $x \in X$ , the quotient  $\mathcal{O}_{X,x}/\mathfrak{m}_{X,x}$  is a field. We denote it by  $\kappa(x)$  and call it the residue field of x. In the aforementioned examples, the residue fields of all of the points of x are the same (either  $\mathbb{R}$ ,  $\mathbb{C}$ , or a prescribed algebraically closed field), but that will not be the case for schemes!

I'll talk about morphisms of (locally) ringed spaces later. For the moment, let me at least point out that an *isomorphism* of (locally) ringed spaces is what you think: a homeomorphism of topological spaces and corresponding bijections of sections which commute with restriction.

## 2 The prime spectrum of a ring

The notion of a locally ringed space is a sufficiently broad generalization of manifolds that it admits a meaningful functor from the category of *arbitrary* (commutative unital) rings.

This gives rise to the concept of an affine scheme; to define this, we must first recall the construction of the prime spectrum of a ring. See the exercises for lots of examples.

Let R be an arbitrary ring. Following Zariski, we define the *prime spectrum* of R, denoted  $\operatorname{Spec}(R)$ , to be the set of prime ideals of R. (An ideal  $\mathfrak p$  of R is *prime* if  $R/\mathfrak p$  is an integral domain. The zero ring is not an integral domain, so the trivial ideal is not prime.) For a general ring, this is a better idea than using only maximal ideals because a ring homomorphism  $\phi: R \to S$  induces a map  $\operatorname{Spec}(S) \to \operatorname{Spec}(R)$  taking  $\mathfrak p \subseteq S$  to  $\phi^{-1}(\mathfrak p)$ . (The latter is prime because  $\phi$  induces an *injective* map  $R/\phi^{-1}(\mathfrak p) \to S/\mathfrak p$ , so the source is an integral domain.) By contrast,  $\phi$  may not carry maximal ideals of S to maximal ideals of S; for instance, consider  $\phi: \mathbb Z \to \mathbb Q$ .

Again following Zariski, we equip the set Spec(R) with the Zariski topology, in which the closed sets have the form

$$V(I) = {\mathfrak{p} \in \operatorname{Spec}(R) : I \subseteq \mathfrak{p}}$$

for I an ideal of R. This is indeed a topology because

$$V(I) \cup V(J) = V(I \cap J) = V(IJ)$$
$$\bigcap_{i} V(I_i) = V\left(\sum_{i} I_i\right).$$

We will use a special basis of open sets for this topology: the *distinguished open sets*, of the form

$$D(f) = \{ \mathfrak{p} \in \operatorname{Spec}(R) : f \notin \mathfrak{p} \}$$

for f an element of R. Note that this basis is *nice* in the sense that the intersection of any two distinguished opens D(f) and D(g) is again a distinguished open, namely D(fg). Note also that for  $\phi: R \to S$  a homomorphism, the induced map  $\operatorname{Spec}(S) \to \operatorname{Spec}(R)$  is continuous because the inverse image of D(f) is  $D(\phi(f))$ .

**Lemma.** Any distinguished open D(f) of Spec(R) is quasicompact for the Zariski topology. In particular, Spec(R) = D(1) itself is quasicompact.

*Proof.* It is enough to prove that any covering of D(f) by distinguished open subsets admits a finite subcover. If the sets  $D(f_i)$  cover D(f) (for i running over some arbitrary index set), then the radical of (f) is contained in the radical of the ideal generated by the  $f_i$ . In particular, some power of f is in the ideal generated by the  $f_i$ . But that means that we can write f as a *finite* R-linear combination of the  $f_i$ , so those  $D(f_i)$  already cover D(f).  $\square$ 

For example, if k is an algebraically closed field, then  $\operatorname{Spec} k[x]$  consists of one point of the form (x-a) for each  $a \in k$ , plus a point corresponding to the prime ideal (0). The latter is an example of a *generic point*, a point whose closure is equal to the entire space in question. For the analogous picture of  $\operatorname{Spec} k[x,y]$ , see Hartshorne Example 2.3.4.

## 3 A presheaf of rings

We now specify a presheaf of rings on  $X = \operatorname{Spec}(R)$ , but only on the distinguished open subsets. To do this, we must do a bit of work to clean up their description, to account for the fact that prime ideals don't see the difference between an element of a ring and a power of that element.

**Lemma.** For  $f, g \in R$ , we have  $D(f) \subseteq D(g)$  if and only if some power of f is a multiple of g.

Proof. Note that  $D(f) = D(f^n)$  for any positive integer n. Hence if  $f^n$  is a multiple of g for some n, then  $D(f) = D(f^n)$  is contained in D(g). Conversely, suppose  $D(f) \subseteq D(g)$ , or in other words,  $V(g) \subseteq V(f)$ . Recall that the radical of the ideal (g) is the intersection of the prime ideals containing (g). Since  $V(g) \subseteq V(f)$ , it follows that the radical of (g) is contained in the radical of (g), so in particular f belongs to the radical of (g). That is, some power of f is a multiple of g, as desired.

A multiplicative subset of R is a subset closed under multiplication. For example,  $S_f = \{1, f, f^2, f^3, \ldots\}$  is a multiplicative subset. A multiplicative subset S is saturated if for any  $x \in R$  such that some power of x equals an element of S times a unit, we have in fact  $x \in S$ . For any multiplicative subset S of R, there is a unique saturated multiplicative subset S containing it, formed in the obvious fashon. By the previous lemma, we now have the following.

Corollary. For  $f, g \in R$ , we have D(f) = D(g) if and only if  $\tilde{S}_f = \tilde{S}_g$ .

Given any multiplicative subset S of R, there is a unique initial object among the Ralgebras in which each element of S has a multiplicative inverse. It is called the *localization*of R at S, denoted  $S^{-1}R$ . We can construct it as the polynomial ring in one variable  $x_f$ for each  $f \in S$ , modulo the relations  $x_f f - 1$ . Note that there is a canonical isomorphism  $\tilde{S}^{-1}R \cong S^{-1}R$  since they both satisfy the same universal property. In particular, we can
write

$$\tilde{S}_f^{-1}R \cong R[x]/(xf-1).$$

From now on, write  $R_f$  instead of  $\tilde{S}_f^{-1}R$ .

Let D be the set of distinguished open subsets of  $X = \operatorname{Spec} R$ . Define a presheaf of rings  $\mathcal{O}_X$  on X specified on D as follows. First put

$$\mathcal{O}_X(D(f)) = R_f;$$

this is well-defined by the previous corollary. Then note that given an inclusion  $D(g) \subseteq D(f)$ , we have  $R_f \subseteq R_g$ , so the universal property of localization gives a canonical homomorphism  $R_f \to R_g$ . If you want to write this more concretely (but less canonically), apply the lemma above to write  $f^n = gh$  for some positive integer n, identify  $\mathcal{O}_X(D(f)) = R[x]/(xf-1)$  and  $\mathcal{O}_X(D(g)) = R[y]/(yg-1)$ , and take the R-algebra homomorphism

$$R[x]/(xf-1) \to R[y]/(yg-1), \qquad x \mapsto f^{n-1}hy.$$

#### 4 The fundamental theorem of affine schemes

We are now ready to prove what I call the fundamental theorem of affine schemes. I don't know whether its appearance in EGA 1 is its first.

**Theorem 1.** The presheaf  $\mathcal{O}_X$  on  $X = \operatorname{Spec} R$  specified on D satisfies the sheaf axiom for coverings of distinguished opens by other distinguished opens. Consequently, it extends uniquely to a sheaf of rings on  $\operatorname{Spec} R$ .

While we're at it, though, we may as well prove something stronger which we will need later. This proof is basically the same one used to compute the regular functions on an affine algebraic variety. It may also be thought of as an enhancement of the Chinese remainder theorem; indeed, the latter is an immediate corollary (exercise).

**Theorem 2.** Let M be an R-module. Define a presheaf  $\tilde{M}$  of abelian groups on X specified on D by the formula  $D(f) \mapsto M \otimes_R R_f$ . Then  $\tilde{M}$  satisfies the sheaf axiom for coverings of distinguished opens by other distinguished opens. Consequently, it extends uniquely to a sheaf on Spec R.

*Proof.* By replacing R with  $R_f$ , we may reduce to checking the sheaf axiom for a cover of X itself by some distinguished open subsets  $D(f_i)$ . We first verify that the map  $M \to \prod_i M \otimes_R R_{f_i}$  is injective, as follows. Suppose  $m \in M$  belongs to the kernel of this map. Then the annihilator of m is an ideal of R which cannot be contained in any prime ideal  $\mathfrak{p}$  of R, or else we would have  $\mathfrak{p} \in D(f_i)$  for some i, and the image of m in  $M \otimes_R R_{f_i}$  would be nonzero. Thus  $1 \cdot m = 0$ , so m = 0.

This proves the first half of the sheaf axiom; we must now check the glueing property. For this, we remember that X is quasicompact, so we may reduce to checking for a finite cover. Say  $D(f_1), \ldots, D(f_n)$  cover X. Suppose that some  $D(f_i)$  cover D(f), and that we are given elements  $m_i/f_i^{h_i} \in M \otimes_R R_{f_i}$  such that  $m_i/f_i^{h_i}$  and  $m_j/f_j^{h_j}$  have the same image in  $R_{f_if_j}$ . Since there are only finitely many  $f_i$ , we may take the nonnegative integers  $h_i$  to be equal to a common value h. For each i, j, we then have

$$(f_i f_j)^{g_{ij}} (f_i^h m_j - f_j^h m_i) = 0$$

for some nonnegative integers  $g_{ij}$ . By rechoosing the  $m_i$ , we can force  $g_{ij} = 0$  for all i, j, that is, we now have literal equalities

$$f_i^h m_j = f_i^h m_i.$$

Since  $D(f_i^h) = D(f_i)$ , the  $D(f_i^h)$  again cover X, so the  $f_i^h$  generate the unit ideal. We may now pick  $g_1, \ldots, g_n \in R$  such that  $g_1 f_1^h + \cdots + g_n f_n^h = 1$ . Put

$$m = g_1 m_1 + \dots + g_n m_n.$$

We then have

$$f_i^h m = \sum_j f_i^h g_j m_j = \sum_j f_j^h g_j m_i = m_i,$$

so m is an element of M restricting to  $m_i/f_i^h$  for each i. This completes the proof of the glueing property, so we are done.

#### 5 Schemes

From now on, we view  $X = \operatorname{Spec}(R)$  as a ringed space with structure sheaf  $\mathcal{O}_X$  as defined above. Note that for any prime ideal  $\mathfrak{p}$  of R, the stalk  $\mathcal{O}_{X,\mathfrak{p}}$  is canonically isomorphic to the local ring  $R_{\mathfrak{p}}$  (the localization of R at the multiplicative set  $R \setminus \mathfrak{p}$ ). Hence  $\operatorname{Spec}(R)$  is in fact a locally ringed space.

At this point, we make schemes out of prime spectra by glueing, just as we would make manifolds out of open subspaces of  $\mathbb{R}^n$ . We define an *affine scheme* to be any locally ringed space X isomorphic to  $\operatorname{Spec}(R)$  for some ring R; note that the ring R is uniquely determined by the fact that

$$\Gamma(\operatorname{Spec}(R), \mathcal{O}_{\operatorname{Spec}(R)}) = R$$

(from the previous theorem). A *scheme* is a locally ringed space in which each point has an open neighborhood isomorphic to an affine scheme.

Warning: if  $X = \operatorname{Spec}(R)$  is an affine scheme, each distinguished open subset D(f) is an affine scheme, namely  $\operatorname{Spec}(R_f)$  (exercise). By construction, these form a basis of open sets. However, it is possible for there to be an open subset U of X such that  $(U, \mathcal{O}_X|_U)$  is isomorphic to an affine scheme but U is not distinguished. (Counterexample to appear as an exercise.)

# 6 Schemes by glueing

We often specify nonaffine schemes using glueing data. For instance, if  $X_1$  and  $X_2$  are two schemes admitting open subsets  $U_1, U_2$  which are isomorphic as locally ringed spaces, we can glue along this isomorphism to get a third scheme X. For more than two schemes, though, we must add a cocycle condition to keep the glueing maps consistent. Here is how that works.

Let us first specify glueing data for sets. Let  $(X_i)_{i\in I}$  be a collection of sets. For each pair  $(i,j)\in I\times I$ , let  $U_{ij}$  be an open subset of  $X_i$ , and suppose that  $U_{ii}=X_i$ . Let  $\phi_{ij}:U_{ij}\to U_{ji}$  be an isomorphism, and suppose that  $\phi_{ii}=\mathrm{id}_{X_i}$ . Suppose also that for  $i,j,k\in I$ ,  $\phi_{ij}$  restricts to an isomorphism of  $U_{ij}\cap U_{ik}$  with  $U_{ji}\cap U_{jk}$ , and the cocycle condition

$$\phi_{ik} = \phi_{jk} \circ \phi_{ij}$$

holds on  $U_{ij} \cap U_{ik}$ . (In particular,  $\phi_{ji} = \phi_{ij}^{-1}$ .)

We would like to identify the  $X_i$  with subsets of a single set X in such a way that  $U_{ij}$  identifies with  $X_i \cap X_j$  and  $\phi_{ij}$  identifies with the identity map on  $X_i \cap X_j$ . To do this, first form the disjoint union  $X' = \coprod_{i \in I} X_i$ . Then define a binary relation on X' as follows: for  $x_i \in X_i$  and  $x_j \in X_j$ , we say that  $x_i \sim x_j$  if  $x_i \in U_{ij}$ ,  $x_j \in U_{ji}$ , and  $\phi_{ij}(x_i) = x_j$ . The glueing conditions guarantee that this is an equivalence relation, so we may form the quotient X of X' by  $\sim$ ; this gives the desired glueing. (Exercise: reformulate this definition in terms of a limit construction.)

We next specify glueing data for topological spaces. Set notation as above, except that each  $U_{ij}$  must be an open subset of  $X_i$ , and each  $\phi_{ij}$  must be a homeomorphism. Using the

glueing construction for sets, identify the  $X_i$  with subsets of a single set X. We may then use the topologies on the  $X_i$  as a basis for a topology on X; in particular,  $X_i$  is open in X.

We must still check, however, that the given topology on  $X_i$  coincides with the subspace topology from X (it is only obvious that the subspace topology is finer). Suppose  $x_i \in X_i$  and V is an open neighborhood of  $x_i$  in X. There then exists some j such that  $x_i \in X_j$  and V contains an open neighborhood of  $x_i$  for the topology on  $X_j$ . Since  $x_i \in X_i \cap X_j = U_{ji}$  and the latter is open in  $X_j$ ,  $V \cap U_{ji}$  also contains an open neighborhood of  $x_i$  for the topology on  $X_j$ . Since  $\phi_{ij}$  is a homeomorphism,  $V \cap U_{ji} = V \cap U_{ij}$  contains an open neighborhood of  $x_i$  for the topology on  $X_i$ . This proves the claim.

We next specify glueing data for (locally) ringed spaces. Set notation as above, except that each  $X_i$  now carries a structure sheaf  $\mathcal{O}_{X_i}$ , and each  $\phi_{ij}$  is an isomorphism of (locally) ringed spaces. Using the glueing construction for topological spaces, identify the  $X_i$  with open subsets of a single topological space X. By the glueing property for sheaves, we now obtain a sheaf of rings  $\mathcal{O}_X$ , so X may be viewed as a ringed space. Moreover, for  $x \in X_i$ , we have a canonical identification of  $\mathcal{O}_{X,x}$  with  $\mathcal{O}_{X_i,x}$ ; hence if each  $X_i$  is a locally ringed space, so is X.

We finally specify glueing data for schemes. This is the easy part: set notation as above, except that each  $X_i$  is a scheme. Then it is evident that X is also locally isomorphic to an affine scheme, so X is a scheme! (This part also works for manifolds and the like.)

# 7 Examples of glueing

Glueing can be a force for both good and evil. Let's start with good. Start with any ring R. For i = 0, ..., n, put

$$X_i = \operatorname{Spec} R[x_0/x_i, \dots, x_{i-1}/x_i, x_{i+1}/x_i, \dots, x_n/x_i].$$

Define the distinguished open subset

$$U_{ij} = D(x_j/x_i) \subset X_i$$
.

Then there is an obvious isomorphism of  $U_{ij}$  with  $U_{ji}$  given by identifying  $x_k/x_i$  with  $(x_k/x_j)(x_j/x_i)$ . It is easy to check that the cocycle condition is satisfied, so we get a scheme  $\mathbb{P}_R^n$ , the *projective space* over R. (An alternate construction of projective space uses graded rings. More on this later.)

Now for the evil. Let k be an algebraically closed field. Let  $X_1$  and  $X_2$  be two copies of Spec k[x]. We may glue these on the open sets obtained by removing the point x = 0 (i.e., the distinguished opens D(x)) to get a rather unpleasant object; it is a *line with a doubled point*.

We would like to formulate a condition that rules out such pathologies. In topology, the Hausdorff condition does the job, but that won't work for schemes. We need a more category-theoretical notion, which will be provided once we define *separatedness*.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Morphisms of schemes (updated 20 Feb 09)

We next introduce morphisms of locally ringed spaces and schemes. Same references as the previous handout.

Missing remark from last time: when EGA was written, what we now call a scheme was called a *prescheme*. EGA's "scheme" is what we will call a *separated scheme*.

### 1 Direct and inverse image

To define morphisms of ringed spaces, I need the direct and inverse image functors for sheaves. I had these on a previous handout, but didn't discuss them in class, so let me review.

Let  $f: X \to Y$  be a continuous map. For  $\mathcal{F}$  a sheaf on X, the formula

$$(f_*\mathcal{F})(V) = \mathcal{F}(f^{-1}(V))$$

obviously defines a sheaf  $f_*\mathcal{F}$  on Y. It is called the *direct image* of  $\mathcal{F}$ .

Now let  $\mathcal{G}$  be a sheaf on Y. Define a presheaf  $f_{-}^{-1}\mathcal{G}$  on X as follows: for U open in X, let  $(f_{-}^{-1}\mathcal{G})(U)$  be the stalk of  $\mathcal{G}$  at f(U), i.e., the direct limit of  $\mathcal{G}(V)$  over open sets  $V \subseteq X$  containing f(U). This is general not a sheaf; its sheafification is called the *inverse image* of  $\mathcal{G}$ , denoted  $f^{-1}\mathcal{G}$ . (The notation  $f^*$  is reserved for something else; see below.)

**Proposition.** The functors  $f^{-1}$  and  $f_*$  form an adjoint pair.

Proof. Exercise. 
$$\Box$$

Using the inverse image, we can define the restriction of  $\mathcal{F}$  to an arbitrary subset Z of X, as the sheaf  $i^{-1}\mathcal{F}$  for  $i:Z\to X$  the inclusion map (with Z given the subspace topology). If  $Z=\{x\}$ , this coincides with the stalk  $\mathcal{F}_x$  (exercise).

## 2 Morphisms of (locally) ringed spaces

Let  $(X, \mathcal{O}_X)$  and  $(Y, \mathcal{O}_Y)$  be ringed spaces. A morphism of ringed spaces from X to Y consists of a continuous map  $f: X \to Y$  plus a homomorphism  $f^{\sharp}: \mathcal{O}_Y \to f_*(\mathcal{O}_X)$  of sheaves of rings on Y.

For example, if X and Y are manifolds, then  $f^{\sharp}$  acts as follows. Given an open subset U of Y, we must specify a homomorphism from  $\mathcal{O}_Y(U)$  to  $f_*(\mathcal{O}_X)(U) = \mathcal{O}_X(f^{-1}(U))$ . This homomorphism is pullback by f; that is, it takes a continuous function  $g: U \to \mathbb{R}$  to the continuous function  $g \circ f: f^{-1}(U) \to \mathbb{R}$ .

In this example, both X and Y are locally ringed spaces. Moreover, the homomorphism  $f^{\sharp}$  has an important property not implied by the definition of a morphism of ringed spaces: if  $g: U \to \mathbb{R}$  vanishes at some point  $y \in Y$ , then  $g \circ f$  vanishes at any point  $x \in X$  for which f(x) = y. More generally, the value of g at y equals the value of  $g \circ f$  at x.

This is such an important property that we build it into the definition of a morphism of locally ringed spaces. If  $(X, \mathcal{O}_X)$  and  $(Y, \mathcal{O}_Y)$  are locally ringed spaces, a morphism of locally ringed spaces is a morphism of the underlying ringed spaces such that for each point  $x \in X$  mapping to  $y \in Y$ , the induced homomorphism  $\mathcal{O}_{Y,y} \to \mathcal{O}_{X,x}$  of local rings is a local homomorphism, that is, the inverse image of  $\mathfrak{m}_{X,x}$  is  $\mathfrak{m}_{Y,y}$ .

### 3 Morphisms of schemes

A morphism between two schemes is simply a morphism between the underlying locally ringed spaces. E.g., for  $U \subseteq X$  open, restricting X to U gives a locally ringed space which is again a scheme, and the inclusion is a morphism of schemes. Such a U is called an *open subscheme* of X.

It may be a surprise that merely requiring morphisms of schemes to preserve the locally ringed space structure has the expected effect.

**Theorem 1.** For A and B two rings, the set of morphisms  $(f, f^{\sharp})$ : Spec $(A) \to \text{Spec}(B)$  of locally ringed spaces corresponds bijectively to the set of ring homomorphisms  $f^*: B \to A$ , where  $(f, f^{\sharp})$  goes to the map

$$f^{\sharp}(\operatorname{Spec}(A)): \Gamma(\operatorname{Spec}(B), \mathcal{O}_{\operatorname{Spec}(B)}) = B \to \Gamma(\operatorname{Spec}(B), f_{*}(\mathcal{O}_{\operatorname{Spec}(A)})) = A.$$

In fact, something more general is true.

**Theorem 2.** Let LocRingSp be the category of locally ringed spaces. For any locally ringed space  $(X, \mathcal{O}_X)$  and any ring A, there is a natural bijection

$$\operatorname{Hom}_{\operatorname{LocRingSp}}((X,\mathcal{O}_X),\operatorname{Spec}(A)) \to \operatorname{Hom}_{\operatorname{Ring}}(A,\Gamma(X,\mathcal{O}_X))$$

obtained by taking global sections. In other words, the functors Spec and  $\Gamma(\cdot, \mathcal{O})$  from the category of rings to the opposite category of locally ringed spaces form an adjoint pair.

*Proof.* We first define the inverse map. Given a map  $f^*: A \to \Gamma(X, \mathcal{O}_X)$  and a point  $x \in X$ , let f(x) be the point of  $\operatorname{Spec}(A)$  corresponding to the inverse image of  $\mathfrak{m}_{X,x}$  under the composition  $A \to \Gamma(X, \mathcal{O}_X) \to \mathcal{O}_{X,x}$ .

To see that f is continuous, it is enough to check that the inverse image of a distinguished open subset D(g) is open. But this inverse image consists of the points  $x \in X$  where  $f^*(g) \in \Gamma(X, \mathcal{O}_X)$  has a nonzero value, and this is indeed open. Better yet, if  $x \in X$  is a point where  $f^*(g)$  has a nonzero value, then (since  $\mathcal{O}_{X,x}$  is a local ring) g has a multiplicative inverse in  $\mathcal{O}_{X,x}$ , and so has a multiplicative inverse everywhere in some open neighborhood of X. As a corollary, we observe that g has a multiplicative inverse everywhere on  $f^{-1}(D(g))$  (since the local inverses are unique, and hence must glue).

Now that f is known to be continuous, we can define  $f^{\sharp}$ . It is sufficient to define it on distinguished opens, that is, we must specify

$$f^{\sharp}(D(g)):\Gamma(D(g),\mathcal{O}_{\operatorname{Spec}(A)})=A_g\to\Gamma(D(g),f_*(\mathcal{O}_X))=\Gamma(f^{-1}(D(g)),\mathcal{O}_X).$$

To do this, write any  $h \in A_g$  as  $a/g^i$  with  $a \in A$  and  $i \in \mathbb{Z}_{\geq 0}$ . We can then map a to  $\Gamma(X, \mathcal{O}_X)$  and then by restriction to  $\Gamma(f^{-1}(D(g)), \mathcal{O}_X)$ . By the previous paragraph, g maps to a unit in  $\Gamma(f^{-1}(D(g)), \mathcal{O}_X)$ , so we can compute (unambiguously) the image of  $a/g^i$ .

It is clear that if we start with a ring homomorphism, then pass to locally ringed spaces, then return, we get back the original ring homomorphism. The hard part is to check that if we start with a morphism of locally ringed spaces on the left, then go to the right and come back, we get back the morphism we started with. What we need the extra condition for is to see that the underlying map on topological spaces is reproduced; once that holds, we get the equality of homomorphisms of ring sheaves by comparing them on stalks.

Here is a simple example to illustrate why we need morphisms of locally ringed spaces, rather than ringed spaces. Let R be a discrete valuation ring with fraction field K, e.g.,  $R = \mathbb{Z}_p$  and  $K = \mathbb{Q}_p$ . Then  $\operatorname{Spec}(K)$  consists of a single point (0), while  $\operatorname{Spec}(R)$  consists of two points (0) and  $\mathfrak{m}_R$  (the maximal ideal) with the first being closed and the second not. The inclusion  $R \to K$  of rings corresponds to a map of locally ringed spaces sending the unique point of  $\operatorname{Spec}(K)$  to the point (0). However, there is also a map of ringed spaces sending  $\operatorname{Spec}(K)$  to the point  $\mathfrak{m}_R$  and again using  $R \to K$  to define the map on structure sheaves. This is not a morphism of locally ringed spaces because the map  $R \to K$  on stalks is not a local homomorphism. (For the good morphism, the map on stalks is just the identity map  $K \to K$ .)

### 4 Some strange morphisms to schemes

Given any locally ringed space  $(X, \mathcal{O}_X)$ , we can use the previous theorem to construct a canonical morphism

$$(X, \mathcal{O}_X) \to \operatorname{Spec}(\Gamma(X, \mathcal{O}_X))$$

(this is basically an adjunction morphism). This in itself may not be so useful, because X may have very few global functions (e.g., the Riemann sphere with the sheaf of holomorphic functions). On the other hand, if X contains enough global functions to separate points (i.e., if for any  $x, y \in X$  we can find  $f \in \Gamma(X, \mathcal{O}_X)$  with  $f \in \mathfrak{m}_{X,x}$  but  $f \notin \mathfrak{m}_{X,y}$ ), then the canonical homomorphism is injective.

For instance, if X is an affine algebraic variety, this gives a map from X to a scheme. It turns out that this map is a bijection from X to the closed point to the resulting scheme, and in fact gives an embedding of the category of varieties into the category of schemes; see Hartshorne Proposition II.2.6 and the related exercise.

Another example occurs when X is a sufficiently small complex analytic manifold (e.g., a  $Stein\ space$ ). Such examples will occur when we talk about analytification of complex algebraic varieties and Serre's  $GAGA\ principle$ .

One other funny but useful example: for X any scheme and  $x \in X$ , we can construct a morphism  $\operatorname{Spec}(\mathcal{O}_{X,x}) \to X$  by taking any open affine neighborhood U of x in X and performing adjunction on the ring map  $\Gamma(U, \mathcal{O}_X) \to \mathcal{O}_{X,x}$ . The result does not depend on

U; it carries the closed point of  $\mathcal{O}_{X,x}$  (the point corresponding to the maximal ideal of the local ring) to x.

### 5 Fibre products

Recall that a fibre product of the morphisms  $Y \to X$  and  $Z \to X$  in any category is a limit of the diagram

i.e., a final object among objects mapping to Y and Z making the diagram commute.

We'll construct fibre products of schemes in a moment. First, we observe how fibre products interact with passage to open subschemes.

**Lemma.** Suppose  $f: Y \to X$  and  $g: Z \to X$  are morphisms of schemes such that the fibre product  $Y \times_X Z$  exists. Let  $\pi_1: Y \times_X Z \to Y$ ,  $\pi_2: Y \times_X Z \to Z$  be the induced maps. Let  $T \subseteq X, U \subseteq Y, V \subseteq Z$  be open subsets such that  $f(U), g(V) \subseteq T$ , viewed as subschemes. Then

$$\pi_1^{-1}(U) \cap \pi_2^{-1}(V),$$

viewed as a subscheme of  $Y \times_X Z$ , is a fibre product of  $U \to T$  and  $V \to T$ . (In particular, the construction does not depend on T.)

Proof. Suppose  $S \to U$  and  $S \to V$  are morphisms such that  $S \to U \to T$  and  $S \to V \to T$  agree. Then  $S \to U \hookrightarrow Y \xrightarrow{f} X$  and  $S \to V \hookrightarrow Z \xrightarrow{g} X$  agree, so S factors uniquely through  $Y \times_X Z$ . Now writing  $S \to U \to T \hookrightarrow X$  as  $S \to Y \times_X Z \xrightarrow{\pi_1} Y \xrightarrow{f} X$  shows that the image of S in  $Y \times_X Z$  lands in  $\pi_1^{-1}(U)$ ; similarly, it lands in  $\pi_2^{-1}(V)$ . So we get a map  $S \to \pi_1^{-1}(U) \cap \pi_2^{-1}(V)$ ; conversely, any such map can be composed with the inclusion  $\pi_1^{-1}(U) \cap \pi_2^{-1}(V) \hookrightarrow X$ , so the above argument shows that the map is unique.

With this, it is easy to check the existence of fibre products.

**Theorem 3.** All fibre products exist in the category of schemes.

*Proof.* The easy part is when  $X = \operatorname{Spec}(A)$ ,  $Y = \operatorname{Spec}(B)$ ,  $Z = \operatorname{Spec}(C)$  are all affine. In that case, the tensor product  $B \otimes_A C$  is a fibre coproduct in the category of rings, using the maps  $\cdot \otimes 1 : B \to B \otimes_A C$  and  $1 \otimes \cdot : C \to B \otimes_A C$ .

To get the general case, we apply the previous lemma twice. First, if X is affine, then we can cover Y and Z with open affines and use the previous lemma to glue the fibre products. Second, once we know fibre products exist when X is affine, we can cover X itself with open affines (and cover Y and Z with the inverse images of these) and use the lemma again.  $\square$ 

As noted earlier, this notion of product behaves a bit strangely on the level of sets. For instance, Spec  $\mathbb{R}$  and Spec  $\mathbb{C}$  both contain a single point, but Spec  $\mathbb{C} \times_{\operatorname{Spec} \mathbb{R}} \operatorname{Spec} \mathbb{C}$  consists of two points!

### 6 The functor of points

The previous example illustrates that the set of points of a scheme does not really reflect our geometric intuition, derived largely from our experience with varieties, about the behavior of "points" on geometric objects. A good conceptual workaround for this is the *functor of points*.

Given two schemes S and X, the set of S-valued points of X, denoted X(S), is simply the set Hom(S,X) of morphisms of schemes. If S = Spec R, we may write X(R) instead of X(S). For instance, for any ring R, define the affine space  $\mathbb{A}_R^n = \text{Spec } R[x_1, \ldots, x_n]$ . Then for any ring R,

$$\mathbb{A}^n_{\mathbb{Z}}(R) = \mathbb{A}^n_R(R) = R^n.$$

A more telling example is the fibre product. If  $Y \to X$  and  $Z \to X$  are morphisms, then

$$\operatorname{Hom}(S, Y \times_X Z) = \operatorname{Hom}(S, Y) \times_{\operatorname{Hom}(S, X)} \operatorname{Hom}(S, Z),$$

where the right side denotes the usual fibre product in the category of sets, i.e., you take pairs of morphisms from S, one to Y and one to Z, which agree when you pass to morphisms from S to X.

If we fix X, we may view  $X(\cdot)$  as a functor on the category of schemes. There is an appropriate sense in which it is a *sheaf* on that category, but never mind that for now. The one thing you might want to take away from this is that if X is covered by open affines  $U_i$ , a morphism  $S \to X$  may not land in any one of the  $U_i$ . For instance,  $\mathbb{P}^n_{\mathbb{Z}}(S)$  is not just obtained by taking the union of the R-valued points of the distinguished open subsets. For instance, the identity morphism  $\mathbb{P}^n_{\mathbb{Z}} \to \mathbb{P}^n_{\mathbb{Z}}$  doesn't occur this way. You can even have this problem for ring-valued points: there is a natural map  $\operatorname{Spec} \mathbb{Z}[x_0, \ldots, x_n] \to \mathbb{P}^n_{\mathbb{Z}}$  which does not factor through a distinguished open. (See exercises.)

The functor of points doesn't by itself prove much of anything; for instance, it doesn't tell you how to construct the fibre product. However, it can be used to *suggest* certain natural definitions, e.g., the definition of a *group scheme*. See exercises.

### 7 Zen and the art of base change

Although the fibre product is a symmetric construction in the two factors, in algebraic geometry we will often use it in an asymmetric fashion. Namely, for  $f: Y \to X$  a morphism and  $g: Z \to X$  another morphism, we refer to  $f \times g: Y \times_X Z \to Z$  as the base change of f by g. Geometrically, if you imagine f as giving a family of geometric objects parametrized by X,  $f \times g$  describes the pullback of this family to Z.

When we start defining properties of morphisms (next lecture), we will be particularly concerned with their behavior under base change. Typical questions:

(a) Is the property stable under arbitrary base change? If not, how about base changes where the base change morphism is itself restricted in some way?

(b) Does the property descend down a suitable base change? E.g., if g is surjective, does  $f \times g$  having the property imply the same for f?

In particular, if (b) is true whenever  $g: \coprod_i U_i \to X$  is a covering of X by open subschemes, we say that the property is *local on the target*. For instance, by our lemma about base change, the property of being injective/surjective on points is local on the target.

We'll give many examples of properties of morphisms later. Here are two to use as a mental model. For  $f: Y \to X$  a morphism of schemes with  $X = \operatorname{Spec}(A)$  affine, we say that f is affine if  $Y = \operatorname{Spec}(B)$  is also affine. I claim that this property satisfies the following condition.

(i) Let  $f: Y \to X$  be a morphism with X affine. Let  $D(g_1), \ldots, D(g_n)$  be a finite covering of X by distinguished open subsets. Then f is affine if and only if the induced morphisms  $Y \times_X D(g_i) \to D(g_i)$  are all affine.

This follows from the assigned Hartshorne exercise II.2.17, since the  $g_i$  generate the unit ideal in  $\Gamma(Y, \mathcal{O}_Y)$ . (We'll prove something much stronger in the next lecture.)

It can be deduced from this (exercise) that for  $f: Y \to X$  an arbitrary morphism, the following are equivalent.

- (a) For a *single* open affine cover  $\{U_i\}_{i\in I}$  of X, each induced morphism  $Y\times_X U_i\to U_i$  is affine.
- (b) For each open affine cover  $\{U_i\}_{i\in I}$  of X, each induced morphism  $Y\times_X U_i\to U_i$  is affine. (In other words, for every open affine  $U\subseteq X$ , the induced morphism  $Y\times_X U\to U$  is affine.)

If these hold, we say that f itself is affine.

In this case, we have an extra condition that is evidently satisfied.

(ii) Let  $f: Y \to X$  be a morphism with X affine, which is affine. Then for any morphism  $g: Z \to X$  with Z also affine,  $f \times g: Y \times_X Z \to Z$  is also affine.

In this case, (a) and (b) are equivalent to this condition (exercise again).

(c) For every morphism  $g: Z \to X$  with Z affine,  $f \times g: Y \times_X Z \to Z$  is finite.

Moreover, these equivalent conditions are stable under *arbitrary* base change.

Here is another important example. For  $f: Y \to X$  a morphism of schemes with  $X = \operatorname{Spec}(A)$  affine, we say that f is finite if  $Y = \operatorname{Spec}(B)$  is also affine and B is finite as an A-module. I claim this satisfies (i) and (ii). For (i), we already know that  $Y = \operatorname{Spec}(B)$  is affine. Suppose  $B \otimes_A A_{g_i}$  is generated as an  $A_{g_i}$ -module by some finite set of elements. Since each element is an element of B divided by a power of  $g_i$ , we can generate  $B \otimes_A A_{g_i}$  as an  $A_{g_i}$ -module with a finite subset of B itself. These subsets together generate a finite A-submodule B' such that  $(B/B') \otimes_A A_{g_i} = 0$  for each i. That is, the sheaf corresponding to the A-module B/B' is zero; but by a theorem from last time, this forces B/B' = 0.

For (ii), note that if  $Z = \operatorname{Spec}(C)$ , then  $Y \times_X Z = \operatorname{Spec}(B \otimes_A C)$  and  $B \otimes_A C$  is finite as a C-module: use a set of generators of B as an A-module.

#### 8 Back to schemes for a moment

The strategy I just introduced can be used to establish properties of schemes, not just morphisms, using a trick: to define a property P of schemes, say that a morphism  $f: Y \to X$  has property P if and only if f is an isomorphism and X has property P.

For instance, an affine scheme is reduced if its corresponding ring A has no nilpotent elements. This holds if each local ring of A is reduced (exercise), so in particular (i) holds. This allows us to extend the definition of reducedness to arbitrary schemes, and the resulting condition holds if and only if each local ring of the scheme is reduced.

Another approach is to recall that each scheme admits a unique morphism to  $\operatorname{Spec}(\mathbb{Z})$ , and extract properties of schemes from properties of this morphism. Trivial example: X is affine if and only if  $X \to \operatorname{Spec}(\mathbb{Z})$  is affine.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Sheaves of modules (updated 27 Feb 09)

Having discussed sheaves of sets, abelian groups, and rings, we now consider sheaves of modules over a locally ringed space, with an emphasis on the situation for schemes. We'll then use what we know to talk about closed immersions and separated morphisms. (Many more properties of morphisms to follow in the next lectures!) References: Hartshorne II.4, II.5; EGA I 0.4, I 0.5, I 1.1.

### 1 Sheaves of modules

Let  $(X, \mathcal{O}_X)$  be a ringed space. A sheaf of  $\mathcal{O}_X$ -modules is a sheaf of sets  $\mathcal{F}$  such that for each  $U \subseteq X$  open, the group of sections  $\mathcal{F}(U)$  is equipped with a structure of a  $\mathcal{O}_X(U)$ -module, in a fashion compatible with restriction. We sometimes call such a thing simply an  $\mathcal{O}_X$ -module. A morphism of two  $\mathcal{O}_X$ -modules  $\mathcal{F} \to \mathcal{G}$  is a morphism of sheaves which gives a  $\mathcal{O}_X(U)$ -module homomorphism  $\mathcal{F}(U) \to \mathcal{G}(U)$  for each  $U \subseteq X$  open.

Fun fact: for  $\mathcal{F}$  a sheaf of  $\mathcal{O}_X$ -modules, there is a natural bijection between

$$\operatorname{Hom}(\mathcal{O}_X, \mathcal{F}) \to \mathcal{F}(X).$$

If  $\mathcal{F}$  is a sheaf of  $\mathcal{O}_X$ -modules, then for each  $x \in X$ , the stalk  $\mathcal{F}_x$  inherits a structure of a  $\mathcal{O}_{X,x}$ -module. Using that, we can talk about submodules, quotient modules, kernels, cokernels, images, and the like; in fact, these agree with the corresponding notions in the category of sheaves of abelian groups.

An  $\mathcal{O}_X$ -module is *free* if it is isomorphic to a direct sum  $\mathcal{O}_X^I$  of copies of  $\mathcal{O}_X$ . This property cannot be checked locally; if  $\mathcal{O}_X$  is only locally isomorphic to a free  $\mathcal{O}_X$ -module, we say it is *locally free*. More on locally free sheaves later.

One new operation is the tensor product, but it requires some care. If  $\mathcal{F}, \mathcal{G}$  are two  $\mathcal{O}_X$ -modules, the presheaf

$$U \mapsto \mathcal{F}(U) \otimes_{\mathcal{O}_X} \mathcal{G}(U)$$

may not be a sheaf. Form its sheafification, and call that  $\mathcal{F} \otimes_{\mathcal{O}_X} \mathcal{G}$ ; it has the expected arrow-theoretic behavior. (I might forget the  $\mathcal{O}_X$  sometimes when it is not ambiguous.)

## 2 Direct and inverse image

If  $f:(X,\mathcal{O}_X)\to (Y,\mathcal{O}_Y)$  is a morphism of ringed spaces, and  $\mathcal{F}$  is a  $\mathcal{O}_X$ -module, then  $f_*\mathcal{F}$  may naturally be viewed as a  $f_*\mathcal{O}_X$ -module. Using the map  $f^{\sharp}:\mathcal{O}_Y\to f_*\mathcal{O}_X$ , we may also give  $f_*\mathcal{F}$  the structure of an  $\mathcal{O}_Y$ -module. We call this again the *direct image* of  $\mathcal{F}$ .

On the other hand, if  $\mathcal{G}$  is a sheaf of  $\mathcal{O}_Y$ -modules, then  $f^{-1}\mathcal{G}$  is an  $f^{-1}\mathcal{O}_Y$ -module. Adjointness turns  $f^{\sharp}$  into a homomorphism  $f^{-1}\mathcal{O}_Y \to \mathcal{O}_X$ , so we can form the tensor product

$$\mathcal{G} \otimes_{f^{-1}\mathcal{O}_Y} \mathcal{O}_X$$

and get a  $\mathcal{O}_X$ -module. We notate this  $f^*\mathcal{G}$  and call it the *(module-theoretic) inverse image* of  $\mathcal{G}$  under f.

Again,  $f^*$  and  $f_*$  are adjoint in the obvious fashion. Statement and proof left to the reader.

## 3 Quasicoherent sheaves of modules

Since thinking about affine schemes is supposed to be equivalent to thinking about rings (after all, the two categories are equivalent!), we would like our thinking about sheaves of modules on affine schemes to be equivalent to thinking about modules over rings. We even know what the functors realizing this equivalence should be: on an affine scheme  $X = \operatorname{Spec}(R)$ , we should go from R-modules to  $\mathcal{O}_X$ -modules via  $M \mapsto \tilde{M}$  (which we already proved is a sheaf!), and back via  $\mathcal{F} \mapsto \Gamma(X, \mathcal{F})$ .

While it is clear that the composition one way is naturally isomorphic to the identity functor on R-modules, the other way fails because there are "too many"  $\mathcal{O}_X$ -modules. For instance, for R = k[x] with k an algebraically closed field, we can make an  $\mathcal{O}_X$ -module  $\mathcal{F}$  by declaring

$$\mathcal{F}(U) = \begin{cases} 0 & (0) \notin U \\ k[x] & (0) \in U \end{cases}$$

and putting in the obvious restriction maps. This sheaf has the same global sections as  $\mathcal{O}_X$  itself but is clearly not the same!

The fix for this is a bit heavy-handed: we simply declare that we only want sheaves which locally come from a module over a ring. For schemes, it is clear what this means: we want  $\mathcal{F}$  to have the property that for each  $x \in X$ , there is an open affine neighborhood  $U = \operatorname{Spec}(A)$  of x in X such that  $\mathcal{F}|_U = \tilde{M}$  for some A-module M. For locally ringed spaces, we must be a bit more careful: we want  $\mathcal{F}$  to locally be given as the cokernel of some module homomorphism  $\mathcal{O}_X^I|_U \to \mathcal{O}_X^J|_U$  between free  $\mathcal{O}_X$ -modules.

It still remains to check that this gives what we expect for affine schemes. I call this the third fundamental theorem of affine schemes.

**Theorem 1.** Let  $\mathcal{F}$  be a quasicoherent sheaf of  $\mathcal{O}_X$ -modules for  $X = \operatorname{Spec}(R)$ , and put  $M = \Gamma(X, \mathcal{F})$ . Then the natural homomorphism  $\tilde{M} \cong \mathcal{F}$  of  $\mathcal{O}_X$ -modules is in fact an isomorphism. In other words, the category of quasicoherent  $\mathcal{O}_X$ -modules on  $\operatorname{Spec}(R)$  is equivalent to the category of modules on R.

Proof. The claim is equivalent to the fact that for each prime ideal  $\mathfrak{p}$  of R, the natural map  $M_{\mathfrak{p}} \cong \tilde{M}_{\mathfrak{p}} \to \mathcal{F}_{\mathfrak{p}}$  is a bijection. Since  $\mathcal{F}$  is quasicompact, we can find a distinguished open D(f) of X on which  $\mathcal{F} \cong \tilde{N}$  for some  $R_f$ -module N. The map  $\tilde{M} \to \mathcal{F}$  induces a map  $\tilde{M}_f \cong \tilde{M}|_{D(f)} \to \mathcal{F}|_{D(f)} \cong \tilde{N}$ . Taking global sections gives a homomorphism  $M_f \cong N$  of  $R_f$ -modules.

We check injectivity of  $M_f \to N$ . Suppose  $m/f^h \in M_f$  maps to zero in N. For each prime ideal  $\mathfrak{q}$  of R, we can find a distinguished open neighborhood D(g) of  $\mathfrak{q}$  in X such that

 $\mathcal{F}|_{D(g)}\cong \tilde{P}$  for some  $R_g$ -module P. Now  $P_f\cong N_g\cong M_{fg}$  as  $R_{fg}$ -modules since they all give rise to the same sheaf. Hence the image of  $m/f^h$  in  $P_f$  is zero, so the image of m in  $P=\Gamma(D(g),\mathcal{F})$  is killed by some power of f. We conclude that for some nonnegative integer j,  $f^jm$  restricts to the zero section of  $\mathcal{F}$  on D(g). Since this holds for each  $\mathfrak{q}$ , and we only need finitely many D(g) to cover X (since X is quasicompact), there exists a nonnegative integer j such that  $f^jm=0$  in  $\Gamma(X,\mathcal{F})=M$ . Hence  $m/f^h$  represents the zero element in  $M_f$ .

We check surjectivity of  $M_f \to N$ . Let  $n \in N$  be any class. Cover X with finitely many  $D(g_i)$  on each of which  $\mathcal{F}|_{D(g_i)}$  is represented by a module  $P_i$  over  $R_{g_i}$ . Then  $\mathcal{F}_{D(fg_i)}$  is represented by  $(P_i)_{g_i}$ . Hence for some j,  $f^j n$  is the restriction to  $D(fg_i)$  of a section  $s_i$  of  $\mathcal{F}$  over  $D(g_i)$ . We may enlarge j so that it works for all i; then  $s_i - s_j$  represents the zero section of  $\mathcal{F}$  over  $D(fg_ig_j)$ . By the previous paragraph, we can find some k such that  $f^k(s_i - s_j)$  is the zero section of  $\mathcal{F}$  over  $D(g_ig_j)$ . Ergo, for some very large j, the  $f^j n$  give sections  $s_i$  of  $\mathcal{F}$  over  $D(g_i)$  which glue to give a section of  $\mathcal{F}$  on X itself.

We now have  $M_f \cong N$ , so  $M_{\mathfrak{p}} \cong N_{\mathfrak{p}} \cong \mathcal{F}_{\mathfrak{p}}$ . Since  $\mathfrak{p} \in X$  was arbitrary, this proves  $\tilde{M} \cong \mathcal{F}$ .

## 4 Relative Spec, ideal sheaves, and closed immersions

Let X be a scheme, and let  $\mathcal{F}$  be a quasicoherent sheaf of  $\mathcal{O}_X$ -modules which also carries an  $\mathcal{O}_X$ -algebra structure (or for short, a quasicoherent  $\mathcal{O}_X$ -algebra). Then for each open affine subscheme U of X, we can form the scheme  $\operatorname{Spec}\Gamma(U,\mathcal{F})$ , and these glue. We thus obtain a scheme  $Y = \operatorname{Spec}\mathcal{F}$  which comes with a morphism  $Y \to X$ . This is called the relative spectrum of  $\mathcal{F}$ .

One important class of examples of relative spectra are closed immersions. (For more examples, see exercises.) An *ideal sheaf* on a locally ringed space X is a quasicoherent subsheaf of  $\mathcal{O}_X$ . For  $\mathcal{I}$  an ideal sheaf, the quotient  $\mathcal{O}_X/\mathcal{I}$  is a quasicoherent  $\mathcal{O}_X$ -algebra. Let Z be its relative Spec; any map arising as such a map  $f: Z \to X$  is called a *closed immersion*.

Let us see why this name is fitting in the case of schemes. Say  $X = \operatorname{Spec} R$ . Then an ideal sheaf corresponds to an ideal I of R, and  $Z = \operatorname{Spec}(R/I)$ . (Notice that this means that any closed immersion is an affine and finite morphism!) The points of Z are in bijection with the points  $\mathfrak{p} \in X$  where the stalks  $R_{\mathfrak{p}}$  and  $I_{\mathfrak{p}}$  differ, which is precisely the vanishing set V(I). But there can be many different closed immersions with the same underlying set! For instance, in  $\operatorname{Spec} k[x,y]$ , the ideals (x) and  $(x^2)$  define the same closed set but not the same closed immersion.

Beware that algebraic geometers have the habit of calling the source of a closed immersion a closed subscheme of X even though it's not really a subscheme of X in any precise sense. But this isn't so misleading because the map  $Z \to X$  is indeed a monomorphism. And there is something comforting in the thought that (looking at our previous example) the x, y-plane "contains" a doubled line defined by  $x^2 = 0$ , which in turn "contains" the undoubled line defined by x = 0.

Finally, note that if  $f: Z \to X$  is a closed immersion, the defining ideal sheaf can be recovered as the kernel of  $f^{\sharp}: \mathcal{O}_X \to f_*\mathcal{O}_Z$ . In fact, following Hartshorne, you may define a closed immersion as a map of schemes  $f: Z \to X$  which induces a homeomorphism of Z with a closed subset of X, such that  $f^{\sharp}: \mathcal{O}_X \to f_*\mathcal{O}_Z$  is surjective. This has the advantage that it is clear that the property of being a closed immersion is local on the target (though you can check it the other way too, since the ideal sheaf is uniquely determined).

## 5 Separated schemes and morphisms

We are now ready to introduce the analogue of the Hausdorff property for schemes. However, it is more natural to introduce it for morphisms of schemes.

A morphism  $f: Y \to X$  is separated if the diagonal morphism  $\Delta: Y \to Y \times_X Y$  is a closed immersion. Since the formation of  $\Delta$ , and the property of it being a closed immersion, are local on the target, so is the notion of being separated.

For instance, if  $X = \operatorname{Spec} k$  for k a field, and Y consists of two copies of  $\operatorname{Spec} k[x]$  glued along  $\operatorname{Spec} k[x,x^{-1}]$ , then  $Y\times_X Y$  is the affine plane with two copies of each axis, and four copies of the origin. The image of  $\Delta$  contains two copies of the origin, but its closure contains all four. Hence  $Y \to X$  is not separated.

**Lemma.** A morphism  $f: Y \to X$  is separated if and only if the image of the diagonal  $\Delta: Y \to Y \times_X Y$  is a closed subset of  $Y \times_X Y$ .

*Proof.* See Hartshorne, Corollary II.4.2. It relies on another useful (but easy) fact: any *affine* morphism is separated.  $\Box$ 

We say a scheme itself is *separated* if its unique morphism to  $\operatorname{Spec}(\mathbb{Z})$  is separated. This means that by fiat  $\operatorname{Spec}(\mathbb{Z})$  is itself separated, but this seems reasonable enough, especially in light of the following.

**Theorem 2.** Let X be a separated scheme. Then the intersection of any two open affine subschemes of X is again affine.

*Proof.* Exercise. (Beware that the converse is false. The nonseparated example above also satisfies this condition.)  $\Box$ 

There is a valuative criterion for separatedness, but it is hardly ever useful (because it involves arbitrary valuation rings, which can be rather nasty); see Hartshorne Theorem II.4.3.

## 6 Separatedness and base change

**Theorem 3.** Separatedness is stable under base change.

*Proof.* Let  $f: Y \to X$  be a separated morphism, and let  $Z \to X$  be an arbitrary morphism. We are supposed to check that the diagonal

$$Y \times_X Z \to (Y \times_X Z) \times_Z (Y \times_X Z)$$

is a closed immersion. On the other hand, since closed immersions are stable under base change, we already know that

$$Y \times_X Z \to (Y \times_X Y) \times_X Z$$

is a closed immersion. It thus suffices to identify the two right sides in a way commuting with the arrows.

The way to see this is to use the functor of points: given  $W \to X$ , we must identify the maps into the two right hand sides in a natural way. The maps to  $(Y \times_X Y) \times_X Z$  give pairs of maps  $W \to Y \times_X Y$  and  $W \to Z$  which agree on X, then (by splitting the first fibre product) gives triples of maps  $W \to Y$ ,  $W \to Y$ , and  $W \to Z$  which all agree on X.

The maps to  $(Y \times_X Z) \times_Z (Y \times_X Z)$  similarly give pairs of maps  $W \to (Y \times_X Z)$ ,  $W \to Y \times_X Z$  which agree on Z. Splitting again, we get quadruples  $W \to Y$ ,  $W \to Z$ ,  $W \to Y$ ,  $W \to Z$  which agree on X, but moreover the two maps  $W \to Z$  must be the same map. We thus identify with the previous description.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) More properties of morphisms (updated 5 Mar 09)

Note that finite presentation is not discussed in EGA 1; see EGA 4.1 instead.

#### 1 More about separated morphisms

**Lemma.** The composition of closed immersions is a closed immersion.

*Proof.* Let  $f: X \to Y$  and  $g: Y \to Z$  be closed immersions. Since the property of being a closed immersion is local on the base, we may assume  $Z = \operatorname{Spec}(A)$  is affine. Then  $Y = \operatorname{Spec}(B)$  for B a quotient of A, so  $X = \operatorname{Spec}(C)$  for C a quotient of B. Hence C is a quotient of A, proving the claim. (A similar argument shows that a composition of finite morphisms is finite.)

**Lemma.** (a) Any closed immersion is separated.

- (b) A composition of separated morphisms is separated.
- (c) Separatedness is stable under base change.
- (d) A product of separated morphisms is separated.
- (e) If  $f: X \to Y$  and  $g: Y \to Z$  are morphisms,  $g \circ f$  is separated, and g is separated, then f is separated.
- (f) If  $f: X \to Y$  is separated, then  $f_{red}: X_{red} \to Y_{red}$  is separated.

*Proof.* We know (a) because closed immersions are affine and affine morphisms are separated. We know (c) from the previous handout. Parts (d)-(f) follow once we also have (b); see exercises.

It remains to prove (b). Let  $f: X \to Y$  and  $g: Y \to Z$  be separated morphisms. Then  $X \times_Y X$  maps to  $X \times_Z X$ ; in fact, this morphism is the base change of the closed immersion  $\Delta: Y \to Y \times_Z Y$  by  $f \times f: X \times_Z X \to Y \times_Z Y$ . (To check this: use functor-of-points to reduce to the analogous assertion for sets. This can be checked with Z equal to a singleton set, so we just want to know that for a morphism of sets  $X \to Y$ , the fibre product of Y and  $X \times X$  over  $Y \times Y$  equals  $X \times_Y X$ . This is obvious.) Hence  $X \times_Y X \to X \times_Z X$  is a closed immersion. Since the composition of closed immersions is a closed immersion (previous lemma), we find that  $X \to X \times_Y X \to X \times_Z X$  is a closed immersion.

### 2 Quasicompact morphisms

A morphism  $f: Y \to X$  with X affine is *quasicompact* if Y is quasicompact as a topological space. This definition satisfies the strong collater (exercise), so we get a notion which is local on the base and stable under base change.

**Exercise.** Any affine morphism is quasicompact.

#### 3 Finite type and finite presentation

Let A be a ring. Recall that an A-algebra B is finitely generated if it is of the form  $A[x_1, \ldots, x_n]/I$  for some nonnegative integer n and some ideal I of  $A[x_1, \ldots, x_n]$ . If I can be chosen to be a finitely generated ideal, we say that B is finitely presented; this is of course automatic if A is noetherian (as it will be in most of our examples).

Let  $f: Y \to X$  be a morphism of schemes with  $X = \operatorname{Spec}(A)$  affine. We say f is locally of finite type/presentation if Y is a union of open subschemes, each of the form  $\operatorname{Spec}(B)$  with B a finitely generated/presented A-algebra. If only finitely many such open subschemes are needed, we say f is of finite type/presentation. These satisfy the strong collater (exercise).

If  $f: Y \to X$  is of finite type, we sometimes say that Y is of finite type over X. Similarly for the other definitions.

Obvious: any finite morphism, including any closed immersion, is of finite type.

**Exercise.** A morphism  $f: Y \to X$  is of finite type/presentation if and only if it is quasi-compact and locally of finite type/presentation.

## 4 Algebraic varieties

We can now give a scheme-theoretic rendition of the theory of abstract algebraic varieties, in the sense of 18.725. (But see below.)

Let k be an algebraically closed field. An affine variety is a locally ringed space defined by some data of the following form. Pick a nonnegative integer n and an ideal I of  $k[x_1, \ldots, x_n]$ , and put X = V(I). Equip X with the Zariski topology, i.e., take a basis of open sets of the form  $D(g) = \{x \in X : g(x) \neq 0\}$  for  $g \in k[x_1, \ldots, x_n]$ . Define a regular function on an open subset U of X to be a function  $h: U \to k$  such that for each  $x \in U$ , there exist  $f, g \in k[x_1, \ldots, x_n]$  and a nonnegative integer m such that g vanishes nowhere on U while  $g^m h - f$  vanishes identically on U. Then the regular functions on U form a sheaf.

In the context of schemes, we interpret X to be the set of maximal ideals in  $\operatorname{Spec}(A)$  for  $A = (k[x_1, \ldots, x_n]/I)^{\operatorname{red}}$ , equipped with the structure of a locally ringed space given by restriction from  $\operatorname{Spec}(A)$ .

Now recall that an *abstract algebraic variety* is a locally ringed space covered by affine varieties.

**Theorem 1.** The category of abstract algebraic varieties over the algebraically closed field k is equivalent to the category of schemes which are reduced and locally of finite type over  $\operatorname{Spec}(k)$ .

*Proof.* Exercise. The key point is to check that if  $X = \operatorname{Spec}(A)$  and  $Y = \operatorname{Spec}(B)$  for A, B two reduced finitely generated k-algebras, then the morphisms from X to Y are the same as the morphisms of the corresponding algebraic varieties. But that is because they both correspond to ring homomorphisms  $B \to A$ .

Beware that there is no universal definition of *algebraic varieties*, because everyone seems to prefer to add additional hypotheses. For instance, Hartshorne (see Chapter I) forces his varieties to be separated (as often do I). Some authors also force their varieties to be *irreducible*, i.e., not admitting two disjoint open subschemes. And so on.

#### 5 Proper morphisms

We would like to have an algebraic analogue of the notion of a *compact* algebraic variety over the complex numbers. For this, we introduce the notion of properness.

A morphism  $f: Y \to X$  of schemes is *proper* if it is separated, of finite type, and universally closed. The latter means that any base change of f is a closed map of topological spaces (i.e., carries closed sets to closed sets); this condition comes from the notion of a proper map of topological spaces (see exercises). Since these properties are all local on the base and stable under base change (the last one by fiat), properness is also.

The definition of properness is rather hard to check. One easy case: a closed immersion is separated (because it's affine), of finite type (obvious), and universally closed (because any base change is still a closed immersion, so has closed image), so is proper. Besides this example, and the following slightly fancier example...

Exercise. Any finite morphism (including any closed immersion) is proper.

... all examples of properness will ultimately be extracted from the following theorem.

**Theorem 2.** The morphism  $f: \mathbb{P}^n_{\mathbb{Z}} \to \operatorname{Spec} \mathbb{Z}$  is proper.

Hartshorne proves this using the valuative criterion for properness (under a somewhat mysterious noetherian hypothesis). I'll ultimately prove this following EGA, but I need to wait until the next lecture so I can say more about projective spaces in the interim. I will point out now that the fact that f is of finite type is evident from the glueing construction, and the separatedness may be obtained by describing the diagonal  $\Delta : \mathbb{P}^n_{\mathbb{Z}} \to \mathbb{P}^n_{\mathbb{Z}} \times_{\operatorname{Spec} \mathbb{Z}} \mathbb{P}^n_{\mathbb{Z}}$  explicitly (exercise).

As for separated morphisms, we have some properties.

**Lemma.** (a) Any closed immersion is proper.

- (b) A composition of proper morphisms is proper.
- (c) Properness is stable under base change.
- (d) A product of proper morphisms is proper.
- (e) If  $f: X \to Y$  and  $g: Y \to Z$  are morphisms,  $g \circ f$  is proper, and g is separated, then f is proper.
- (f) If  $f: X \to Y$  is proper, then  $f_{red}: X_{red} \to Y_{red}$  is proper.

*Proof.* Again, (d)-(f) follow from (a)-(c). We already observed (a) and (c). To check (b), we already checked that separatedness composes. Finite type composes by an argument similar to the proof that closed immersions compose. Universal closedness composes because a composition of closed maps of topological spaces is again closed.  $\Box$ 

**Corollary.** Any morphism  $f: X \to Y$  that factors as a closed immersion of X into  $\mathbb{P}^n_Y = \mathbb{P}^n_{\mathbb{Z}} \times_{\operatorname{Spec} \mathbb{Z}} Y$  followed by the projection  $\mathbb{P}^n_Y \to Y$  is proper.

The converse is not true even over  $\mathbb{C}$ , as there are compact algebraic varieties which are not closed subvarieties of any projective space. See the appendices to Hartshorne for an example. One can often deal with these using Chow's lemma, about which more later.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Projective morphisms, part 1 (updated 3 Mar 08)

We now describe projective morphisms, starting over an affine base.

### 1 Proj of a graded ring

The construction of Proj of a graded ring was assigned as an exercise; let me now recall the result of that exercise.

Let  $S = \bigoplus_{n=0}^{\infty} S_n$  be a graded ring, i.e., a ring such that each  $S_n$  is closed under addition, and  $S_m S_n \subseteq S_{m+n}$ . An element of  $S_n$  is said to be homogeneous of degree n; the elements of  $S_0$  form a subring of S, and each  $S_n$  is an  $S_0$ -module. (One could also define a graded ring to allow negative degrees; on the few occasions where I'll need that construction, I'll call it a graded ring with negative degrees.) Let  $S^+$  denote the ideal  $\bigoplus_{n=1}^{\infty} S_n$ .

Let Proj S be the set of all homogeneous prime ideals of S not containing  $S_+$ . For each positive integer n and each  $f \in S_n$ , we may view the localization  $S_f$  as a graded ring with negative degrees, by placing  $g/f^k$  in degree m-kn whenever  $g \in S_m$ . We may then identify the set

$$D(f) = \{ \mathfrak{p} \in \operatorname{Proj} S : f \notin \mathfrak{p} \}$$

with Spec  $S_{f,0}$ , where  $S_{f,0}$  is the degree zero subring of  $S_f$ . These glue to equip Proj S with the structure of a scheme (note that  $D(f) \cap D(g) = D(fg)$ ). In the case  $S = A[x_0, \ldots, x_n]$  where each of  $x_0, \ldots, x_n$  is homogeneous of degree 1, this simply produces the projective space  $\mathbb{P}^n_A$ .

Any morphism  $S \to T$  of graded rings induces a morphism  $\operatorname{Proj} T \to \operatorname{Proj} S$  of schemes. For example, we say an ideal I of S is homogeneous if as abelian groups we have

$$I = \bigoplus_{n=0}^{\infty} (I \cap S_n).$$

In other words, if we split each element of I into homogeneous components, the components themselves belong to I. Then S/I may also be viewed as a graded ring, the projection  $S \to S/I$  induces a morphism  $\operatorname{Proj} S/I \to \operatorname{Proj} S$ , and this morphism is a closed immersion (as we see immediately by checking on a D(f)).

Beware that the scheme  $\operatorname{Proj} S$  does not by itself determine the graded ring S. For instance, omitting  $S_1$  gives another graded ring with the same  $\operatorname{Proj}$ . We'll come back to this point later.

More generally, if  $M = \bigoplus_{n=-\infty}^{\infty}$  is a graded S-module, i.e.,  $S_m M_n \subseteq M_{m+n}$  for all m, n, we can convert M into a quasicoherent sheaf  $\tilde{M}$  on Proj S by doing so on each D(f) (using the degree-zero subset of  $M_f$ ) and then glueing. For a converse, see below.

# 2 The sheaf $\mathcal{O}(1)$

For S a graded ring, n a nonnegative integer, and M a graded S-module, let M(n) denote the shifted module

$$M(n)_i = M_{n+i}.$$

Let  $\mathcal{O}_X(n)$  be the quasicoherent sheaf on  $X = \operatorname{Proj} S$  defined by the graded module S(n). In particular,  $\mathcal{O}_X(0) = \mathcal{O}_X$ . More generally, for any quasicoherent sheaf  $\mathcal{F}$  of  $\mathcal{O}_X$ -modules, put  $\mathcal{F}(n) = \mathcal{F} \otimes_{\mathcal{O}_X} \mathcal{O}_X(n)$ .

**Lemma.** Suppose that S is generated by  $S_1$  as an  $S_0$ -algebra. Then the sheaves  $\mathcal{O}_X(n)$  on Proj S are locally free of rank 1, and  $\mathcal{O}_X(m) \otimes_{\mathcal{O}_X} \mathcal{O}_X(n)$  is canonically isomorphic to  $\mathcal{O}_X(m+n)$ .

*Proof.* See Hartshorne, Proposition II.5.12.

Note: a quasicoherent sheaf  $\mathcal{F}$  on a locally ringed space X which is locally free of rank 1 is also called an *invertible sheaf*. That is because there is a unique sheaf  $\mathcal{F}^{\vee}$  such that  $\mathcal{F} \otimes_{\mathcal{O}_X} \mathcal{F}^{\vee} \cong \mathcal{O}_X$ , the dual of X (exercise). In this case, the dual of  $\mathcal{O}_X(n)$  is in fact  $\mathcal{O}_X(-n)$ .

This gives us an explanation for what  $x_0, \ldots, x_n$  are on the projective space  $\operatorname{Proj} A[x_0, \ldots, x_n]$ : they are global sections not of the sheaf  $\mathcal{O}_X$ , but rather of the sheaf  $\mathcal{O}_X(1)$ .

**Theorem 1.** Suppose that S is finitely generated by  $S_1$  as an  $S_0$ -algebra. Then each quasi-coherent sheaf on Proj S can be written as  $\tilde{M}$  for a canonical choice of M.

The finitely generated hypothesis is needed to ensure that  $\operatorname{Proj} S$  is quasicompact; we will impose it pretty consistently hereafter.

*Proof.* Let  $\mathcal{F}$  be a quasicoherent sheaf on M. Then the module we want is

$$\Gamma_*(\mathcal{F}) = \bigoplus_{n \in \mathbb{Z}} \Gamma(X, \mathcal{F}(n)),$$

where

$$\mathcal{F}(n) = \mathcal{F} \otimes_{\mathcal{O}_X} \mathcal{O}_X(n).$$

For the rest of the proof, see Hartshorne, Proposition II.5.15.

Beware that this does not imply that  $S = \bigoplus_{n=0}^{\infty} \Gamma(X, \mathcal{O}_X(n))$  in general. For a stupid example, take S = A[x], in which case the sheaves  $\mathcal{O}_X(n)$  are all free and so  $\Gamma(X, \mathcal{O}_X(n)) \neq 0$  even when n < 0. For less stupid examples, see Hartshorne exercise II.5.14. However, the following is true.

**Lemma.** Let  $n \geq 1$  be an integer. For  $S = A[x_0, \ldots, x_n]$  with the usual grading (by total degree), we have

$$S = \bigoplus_{n=0}^{\infty} \Gamma(X, \mathcal{O}_X(n)).$$

*Proof.* Exercise, or see Hartshorne Proposition II.5.13.

### 3 Closed subschemes of projective spaces

**Proposition.** For  $n \geq 1$ , any closed immersion into  $\mathbb{P}_A^n$  is defined by some homogeneous ideal of  $A[x_0, \ldots, x_n]$ .

Proof. In fact, there is a canonical way to pick out the ideal. Let  $\mathcal{I}$  be the ideal sheaf defining the closed immersion; then  $\Gamma_*(\mathcal{I})$  is an ideal of  $\Gamma_*(\mathcal{O}_X)$ , but we already identified the latter with  $S = A[x_0, \ldots, x_n]$ . (This identification uses the fact that S is finitely generated by  $S_1$  as an  $S_0$ -algebra, in order to invoke the previous theorem. In fact, it is part of the proof of that theorem; see Hartshorne Proposition II.5.13.)

In general, there may be multiple homogeneous ideals defining the same closed subscheme of  $\mathbb{P}^n_A$ . If we start with an ideal I, pass to the closed subscheme, then use the previous proposition to get back, we get the *saturation* of I, namely, the set of all elements  $f \in A[x_0, \ldots, x_n]$  such that  $x_0^j f, \ldots, x_n^j f \in I$  for some nonnegative integer j. We thus obtain a one-to-one correspondence between closed subschemes of  $\mathbb{P}^n_A$  and *saturated* (equal to their saturation) homogeneous ideals.

**Corollary.** For  $n \geq 1$ , let I be a homogeneous ideal of  $S = A[x_0, \ldots, x_n]$ . The following conditions are equivalent.

- (a) The subscheme of  $\mathbb{P}_A^n$  defined by I is empty.
- (b) The saturation of I equals  $S^+$ .
- (c) For some  $n_0$ , we have  $S_n \subseteq I$  for all  $n \ge n_0$ .

*Proof.* We just proved the equivalence of (a) and (b). It is clear that (c) implies (b). Let us check that (b) implies (c). Given (b), each  $f \in \{x_0, \ldots, x_n\}$  has the property that  $x_0^j f, \ldots, x_n^j f \in I$  for some j. In particular, we have  $x_0^j, \ldots, x_n^j \in I$  for some j. This in turn implies  $S_{(n+1)(j-1)+1} \subseteq I$  since each monomial of degree (n+1)(j-1)+1 is divisible by one of  $x_0^j, \ldots, x_n^j$  (pigeonhole principle!).

## 4 Projective implies proper

We are now ready to complete the proof that  $f: \mathbb{P}^n_{\mathbb{Z}} \to \operatorname{Spec} \mathbb{Z}$  is proper. Recall that the missing step was to show that f is universally closed, i.e., for any scheme X, the map  $\mathbb{P}^n_X \to X$  is closed. It is enough to do this in case  $X = \operatorname{Spec} A$  is affine. Moreover, we may assume  $n \geq 1$ , as the case n = 0 is stupid (because f is an isomorphism).

Let Z be a closed subset of  $\mathbb{P}^n_X$ , suppose  $z \in X$  is not in the image of Z, and put  $k = \kappa(z)$ . We must exhibit an open neighborhood U of x in X such that  $Z \cap \mathbb{P}^n_U = \emptyset$ . Let  $I = \bigoplus_{n=0}^{\infty} I_n$  be the saturated homogeneous ideal in  $S = A[x_0, \ldots, x_n]$  defining Z. Then  $I \otimes_A k$  defines the empty subscheme of Proj  $k[x_0, \ldots, x_n]$ , but may not be saturated. Nonetheless, for some m, we have that  $I_n \otimes_A k = S_n \otimes_A k$ , and so  $(S_n/I_n) \otimes_A k = 0$ .

Since  $S_n/I_n$  is a finitely generated A-module, by Nakayama's lemma,  $(S_n/I_n) \otimes_A A_{\mathfrak{p}} = 0$  for  $\mathfrak{p}$  the prime ideal of A defining z. Again since  $S_n/I_n$  is finitely generated, we have  $(S_n/I_n) \otimes_A A_g = 0$  for some  $g \in A \setminus \mathfrak{p}$ . Then  $z \in D(g)$  and D(g) is disjoint from the image of Z, proving the claim.

## 5 What is a projective morphism?

Several authors (Hartshorne, Eisenbud-Harris) define a morphism  $f: Y \to X$  to be projective if it is the composition of a closed immersion  $Y \to \mathbb{P}^n_X$  with the projection  $\mathbb{P}^n_X$  for some nonnegative integer n. This definition is evidently stable under base change, but it is not local on the base! Better to say that such a morphism is globally projective, and to say that f is locally projective if each  $x \in X$  admits an open neighborhood U such that  $f: Y \times_X U \to U$  is globally projective.

This is not such a serious distinction in practice, as globally projective equals locally projective if X is "not too large". For instance, this occurs if X is itself globally quasiprojective over an affine scheme. (A morphism is globally quasiprojective if it factors as an open immersion followed by a globally projective morphism. Again, this is stable under base change but not local on the base; the version where we force locality on the base is a quasiprojective morphism.)

The definition of *projective* given in EGA is in fact somewhere between locally and globally projective. More on that later. (Warning: Eisenbud-Harris claim that locally projective and projective are the same. They aren't, but counterexamples are rather pathological.)

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Projective morphisms, part 2 (updated 7 Mar 09)

I particularly recommend Eisenbud-Harris for the material in this section; they give a complete description of the relationship between the two descriptions of a blowup (using charts versus relative Proj).

### 1 Relative Proj

Let X be a scheme. Let  $S = \bigoplus_{n=0}^{\infty} S_n$  be a graded quasicoherent  $\mathcal{O}_X$ -algebra. For each open affine U in X, we can form the morphism  $\operatorname{Proj} S(U) \to U$ ; these glue to give a morphism  $\operatorname{Proj} S \to X$ . The object  $\operatorname{Proj} S$  is called the *relative Proj* of S.

We will hereafter assume that  $S_1$  is finitely generated (remember that this is a local notion), and that S is (locally) generated by  $S_1$  as a  $S_0$ -algebra. We also assume that  $S_0$  is a quotient of  $\mathcal{O}_X$ ; Hartshorne assumes that in fact  $S_0 = \mathcal{O}_X$ , but I'd rather not do that. Pick an open affine subset U of X and a surjection  $\mathcal{O}_U^{\oplus (m+1)} \to \mathcal{S}_1|_U$ ; we then obtain a surjection  $\mathrm{Sym}\,\mathcal{O}_U^{\oplus (m+1)} \to \mathcal{S}|_U$ , where

$$\operatorname{Sym} \mathcal{O}_{U}^{\oplus (m+1)} = \bigoplus_{n=0}^{\infty} \operatorname{Sym}^{n} \mathcal{O}_{U}^{\oplus (m+1)}.$$

This in turn gives a closed immersion  $\operatorname{\mathbf{Proj}} \mathcal{S} \to \operatorname{\mathbf{Proj}} \operatorname{Sym} \mathcal{O}_U^{\oplus (m+1)}$ , and the latter is nothing but the projective space  $\mathbb{P}_U^n$ . Consequently,  $\operatorname{\mathbf{Proj}} \mathcal{S} \to X$  is locally projective.

We say that a morphism  $f: Y \to X$  is *projective* if and only if it occurs as a relative Proj. This implies locally projective and is implied by globally projective, but does not coincide with either.

Following EGA, we write  $\mathbb{P}(\mathcal{F})$  for **Proj** Sym  $\mathcal{F}$  whenever  $\mathcal{F}$  is a finitely generated quasicoherent  $\mathcal{O}_X$ -module.

#### 2 Very ample sheaves

An immersion is a morphism  $f: Y \to X$  of schemes which on topological spaces is an isomorphism of Y with a locally closed subset (i.e., a closed subset of an open subset) of X, such that for each  $y \in Y$  mapping to  $x \in X$ , the map  $f^{\sharp}: \mathcal{O}_{X,x} \to \mathcal{O}_{Y,y}$  is surjective. Any composition of closed immersions and open immersions is an immersion; conversely, if f is an immersion, then it can be written as a closed immersion followed by an open immersion. (Let U be an open subset of X in which Y is closed; then f factors uniquely through the open immersion  $U \to X$ , and the resulting map  $Y \to U$  satisfies Hartshorne's definition of a closed immersion.)

Let  $f: Y \to X$  be a morphism. A quasicoherent sheaf  $\mathcal{F}$  on Y is *very ample* relative to f if there exists an immersion  $Y \to \mathbb{P}(\mathcal{S}_1)$  for some finitely generated quasicoherent  $\mathcal{O}_X$ -module  $\mathcal{S}_1$ , under which  $\mathcal{F}$  occurs as the pullback of  $\mathcal{O}(1)$ . Unlike the definition of projectivity, this notion is indeed local on the base.

**Lemma.** The morphism  $f: Y \to X$  is projective if and only if f is proper and there exists a very ample sheaf relative to f.

*Proof.* See Hartshorne, Remark II.5.16.1.

The very ample sheaf pulled back from  $\mathcal{O}(1)$  can be used to retrieve the morphism to  $\mathbb{P}(\mathcal{S}_1)$ . Namely, if  $\mathcal{S}_1$  is globally finitely generated, any set of generators pull back to sections of the pullback of  $\mathcal{O}(1)$ , and those define a morphism to projective space. See Hartshorne Theorem II.7.1.

#### 3 Blowups

Here is a neat class of examples of relative Proj. Let  $\mathcal{I}$  be a finitely generated ideal sheaf on the scheme X, and put  $Y = \mathbb{P}(\mathcal{I})$ . We call Y the blowup of X along  $\mathcal{I}$ .

For example, say  $X = \operatorname{Spec} k[x, y]$  for k a field, and let  $\mathcal{I}$  be the ideal sheaf defined by (x, y). Over  $U = D(x) \cup D(y)$ , we have an isomorphism  $\mathcal{I}|_{U} \cong \mathcal{O}_{U}$ , so  $Y \times_{X} U \to U$  is an isomorphism. But the fibre over the origin looks like a projective line with homogeneous coordinates x, y.

The blowup defined by  $\mathcal{I}$  carries less information than  $\mathcal{I}$  itself. For instance, for any locally principal ideal sheaf, the blowup defined by  $\mathcal{I}$  is the identity.

Here is a special property of the blowup. For  $f: Y \to X$  a morphism and  $\mathcal{I}$  an ideal sheaf on X, we may compose the inclusion  $\mathcal{I} \to \mathcal{O}_X$  with  $f^{\sharp}: \mathcal{O}_X \to f_*(\mathcal{O}_Y)$  and then perform adjunction to get  $f^*\mathcal{I} \to \mathcal{O}_Y$ . The image is an ideal sheaf on Y, called the *inverse image* ideal sheaf of  $\mathcal{I}$  under f.

**Theorem 1.** If  $f: Y \to X$  is the blowup defined by the finitely generated ideal sheaf  $\mathcal{I}$  on X, then the inverse image ideal sheaf of  $\mathcal{I}$  on Y is locally principal.

*Proof.* Recall that  $Y = \operatorname{\mathbf{Proj}} \mathcal{S}$  for  $\mathcal{S}_n = \operatorname{Sym}^n \mathcal{I}$ . In this notation, the inverse image ideal sheaf of  $\mathcal{I}$  on Y is simply  $\mathcal{O}_Y(1)$ , which is locally free. This proves the claim.

In fact, f is universal for this property: any morphism  $Z \to X$  such that the inverse image ideal sheaf of  $\mathcal{I}$  on Z is locally principal factors uniquely through f (Hartshorne, Proposition II.7.14).

More concrete description of the standard example: the blowup of Spec k[x, y] at (x, y) is covered by the two charts

$$\operatorname{Spec} k[x, y/x]$$
  $\operatorname{Spec} k[y, x/y]$ 

glued along Spec k[x, y, x/y, y/x]. In fact, any blowup can be described analogously: the blowup of Spec A along  $I = (r_0, \ldots, r_m)$  is covered by m+1 charts, a typical one of which is

Spec 
$$A[t_1, ..., t_m](t_1r_0 - r_1, ..., t_mr_0 - r_m).$$

The point is that the inverse image ideal sheaf is supposed to become locally principal, so you must force one of the generators  $r_0, \ldots, r_m$  to divide into the other ones, and the different

choices for which generator will divide into the others produces the different charts. (Explicit description of the other charts and the glueing is left to the reader.)

A blowup is a special example of a modification. The latter is a morphism  $f: Y \to X$  of schemes which is proper, surjective, and birational (i.e., its restriction to an open dense subset of X is an isomorphism). In the case of a blowup defined by an ideal sheaf, we get an isomorphism over the complement of the closed set defined by the ideal. In fact, under certain circumstances, every modification can be written as a blowup; see Hartshorne Theorem II.7.17. The catch is that the ideal sheaf is not unique; for example, on Spec k[x, y], the ideals (x, y) and  $(x^2, xy, y^2)$  define the same blowup.

## 4 Chow's lemma

One use of modifications is to turn proper schemes (over some base) into projective schemes.

**Theorem 2** (Chow's lemma). Let  $f: X \to S$  be a morphism of finite type. Assume that either S is noetherian, or S is quasicompact and X has finitely many irreducible components. Then there exists a quasiprojective S-scheme X' and a projective surjective morphism  $f: X' \to X$  which restricts to an isomorphism over some open  $U \subseteq X$  such that  $f^{-1}(U) \cong U$  is dense in X'. Moreover, if X is reduced/irreducible/integral, we can ensure that X' is also.

See EGA 2, Lemme 5.6.1, or for a weaker result, Hartshorne exercise II.4.10.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) More properties of schemes (updated 9 Mar 09)

I've now spent a fair bit of time discussing properties of morphisms of schemes. How-ever, there are a few properties of individual schemes themselves that merit some discussion (especially for those of you interested in arithmetic applications); here are some of them.

#### 1 Reduced schemes

I already mentioned the notion of a reduced scheme. An affine scheme  $X = \operatorname{Spec}(A)$  is reduced if A is a reduced ring (i.e., A has no nonzero nilpotent elements). This occurs if and only if each stalk  $A_{\mathfrak{p}}$  is reduced. We say X is reduced if it is covered by reduced affine schemes.

**Lemma.** Let X be a scheme. The following are equivalent.

- (a) X is reduced.
- (b) For every open affine subsheme  $U = \operatorname{Spec}(R)$  of X, R is reduced.
- (c) For each  $x \in X$ ,  $\mathcal{O}_{X,x}$  is reduced.

*Proof.* A previous exercise.

Recall that any closed subset Z of a scheme X supports a unique reduced closed subscheme, defined by the ideal sheaf  $\mathcal{I}$  which on an open affine  $U = \operatorname{Spec}(A)$  is defined by the intersection of the prime ideals  $\mathfrak{p} \in Z \cap U$ . See Hartshorne, Example 3.2.6.

## 2 Connected schemes

A nonempty scheme is *connected* if its underlying topological space is connected, i.e., cannot be written as a disjoint union of two open sets. (The empty scheme is not connected.)

**Lemma.** The scheme X is connected if and only if the idempotent elements of  $\Gamma(X, \mathcal{O}_X)$  (i.e., the solutions of  $e = e^2$ ) are 0 and 1.

*Proof.* If X is a disjoint union of open sets U and V, then we can construct an idempotent  $e \neq 0, 1$  by taking the pullback of 0 along  $U \to \operatorname{Spec} \mathbb{Z}$  and the pullback of 1 along  $V \to \operatorname{Spec} \mathbb{Z}$ . Conversely, if  $e \in \Gamma(X, \mathcal{O}_X)$  is an idempotent, then its value at each  $x \in X$  is either 0 or 1; the sets where the two values occur are closed and form a partition of X, so X is disconnected.

In many reasonable cases, X can be written as a disjoint union of connected open subschemes; these are then called the *connected components* of X.

#### 3 Irreducible schemes

A nonempty scheme is *irreducible* if its underlying topological space is irreducible, i.e., cannot be written as a union of two proper closed subsets, i.e., does not contain two disjoint nonempty open subsets. (The empty scheme is not irreducible.) Note that a nonempty open subscheme of an irreducible scheme is still irreducible.

**Lemma.** The nonempty affine scheme  $X = \operatorname{Spec}(A)$  is irreducible if and only if the nilradical of A is a prime ideal (i.e., every zero divisor of A is nilpotent).

*Proof.* Note that X is irreducible if and only if the intersection of any two nonempty open subsets is nonempty. It is of course enough to check the intersection of two distinguished opens D(f), D(g). They are nonempty if and only if f and g are not nilpotent; the intersection D(fg) is nonempty if and only if fg is not nilpotent. Hence X is irreducible if and only if the nilradical of A is prime.

Handy fact: the spectrum of a local ring is irreducible, because the maximal ideal belongs to every closed subset.

A generic point of a topological space is a point belonging to every nonempty open subset.

**Lemma.** If X is irreducible, then X has a unique generic point.

Proof. If  $X = \operatorname{Spec}(A)$ , then the nilradical of A is the unique generic point. In general, if X is irreducible and  $U = \operatorname{Spec}(A)$  is a nonempty open affine, then any generic point of X is also a generic point of U. Conversely, if  $\eta \in U$  is the unique generic point of U (which exists because U is forced to be irreducible), then there cannot be an open affine subset V of X omitting  $\eta$ , as then  $V \cap U$  would have to be empty (since it is an open subset U missing the generic point of U), a contradiction.

# 4 Integral schemes

A nonempty scheme is *integral* if it is irreducible and reduced. (The empty scheme is not irreducible.)

**Lemma.** Put  $X = \operatorname{Spec}(A)$ . Then the following are equivalent.

- (a) X is integral.
- (b) A is an integral domain. (The zero ring is not an integral domain.)
- (c) X is connected and each local ring  $\mathcal{O}_{X,x}$  is an integral domain.

*Proof.* The only nontrivial implication is  $(c) \Longrightarrow (a)$ . Suppose (c); note that it implies that X is reduced. Choose  $f \in A$ . Let U be the set of  $x \in X$  such that f has nonzero image in  $\mathcal{O}_{X,x}$ ; then U is open (previously assigned exercise).

We claim that  $X \setminus U$  is also open. To see this, pick  $x \in X \setminus U$  corresponding to a prime ideal  $\mathfrak{p}$  of A. Since f maps to zero in  $A_{\mathfrak{p}}$ , there must exist  $g \in A \setminus \mathfrak{p}$  for which fg = 0. That equality in turn implies that D(g), which contains  $\mathfrak{p}$ , is in fact contained in  $X \setminus U$ . Since each point of  $X \setminus U$  has an open neighborhood contained in  $X \setminus U$ , we conclude that  $X \setminus U$  is open.

Since X is connected, it follows that U equals either X or the empty set. In the latter case, f belongs to the nilradical of A, and so equal 0 because X is reduced.

We conclude that if  $f, g \in A$  are nonzero, their images in each  $A_{\mathfrak{p}}$  are nonzero. Hence fg also has nonzero image in each  $A_{\mathfrak{p}}$ , and so must be nonzero. This proves (a).

#### 5 Normal schemes

A scheme X is normal if for each  $x \in X$ , the local ring  $\mathcal{O}_{X,x}$  is an integral domain and is integrally closed in its field of fractions.

**Lemma.** Suppose  $X = \operatorname{Spec}(A)$  is connected. Then X is normal if and only if A is an integral domain which is integrally closed in its field of fractions.

*Proof.* If A is an integral domain which is integrally closed in its field of fractions, then so is each localization of A (see Atiyah-Macdonald, Proposition 5.12), so X is normal. Conversely, suppose X is connected and normal. By the previous lemma, A is an integral domain.

It remains to check that an integral domain is integrally closed (in its field of fractions) if and only if its localization at each prime ideal has this property. This follows from the easy fact that A is the intersection of the  $A_p$ .

The construction of the integral closure of a domain can be sheafified. (Note: a *dominant* morphism is one with dense image.)

**Theorem 1.** Let X be an integral scheme. Then the category of dominant morphisms  $\tilde{X} \to X$  with  $\tilde{X}$  normal has a final element.

Proof. Exercise.  $\Box$ 

The final element is called the *normalization* of X. Under "normal" circumstances, the morphism  $\tilde{X} \to X$  is finite, but there are pathological counterexamples unless one imposes some hypotheses.

One attempt is the notion of a Nagata ring. We say an integral domain R is N-1 if the integral closure of R in Frac(R) is finite as an R-module. We say R is N-2 if for any finite extension L of Frac(R), the integral closure of R in L is finite as an R-module. We say a general ring R is a Nagata ring if R is noetherian and  $R/\mathfrak{p}$  is N-2 for any prime ideal  $\mathfrak{p}$  of R. (Without the noetherian hypothesis, I think this is what is called a universally Japanese ring in EGA. My definition is from Matsumura, Commutative Algebra, §31.) The point is that the Nagata property is stable under many natural operations: localizations, quotients, passing to a finitely generated ring extension, certain types of completion, etc.

## 6 Dimension and codimension

The dimension of a scheme X is the length of the longest chain  $Z_0 \subset Z_1 \subset \cdots \subset Z_n$  of distinct irreducible closed subsets of X (keeping in mind that the numbering starts at 0). The dimension of an affine scheme  $X = \operatorname{Spec}(A)$  is the same as the Krull dimension, since irreducible closed sets of X correspond to prime ideals of A.

The codimension of an irreducible closed subset Z of X is the length of the longest chain  $Z_0 \subset Z_1 \subset \cdots \subset Z_n$  of distinct irreducible closed subsets of X for which  $Z_0 = Z$ . We can similarly define the codimension of one irreducible closed subset inside another.

These notions can behave badly even for the spectrum of a noetherian ring (Hartshorne, Caution 3.2.8). Again, we need to impose more hypotheses before working with these in any detail; the best way to do this is work with the class of *excellent schemes*. More on those later.

# 7 Regular schemes

Let A be a local ring with maximal ideal  $\mathfrak{m}$  and residue field  $k = A/\mathfrak{m}$ . The cotangent space of A is the k-vector space  $\mathfrak{m}/\mathfrak{m}^2$ ; its dual is called the tangent space of A.

Suppose A is noetherian. Then it is a nontrivial theorem from commutative algebra (e.g., Matsumura  $\S12$ ) that

$$\dim_k(\mathfrak{m}/\mathfrak{m}^2) \ge \dim A.$$

If equality holds, we say that A is regular.

We say that a scheme X is regular at a point x if  $\mathcal{O}_{X,x}$  is a regular local ring, and simply regular if it is regular everywhere. For instance, if X is a scheme of finite type over a field k, then X is regular if and only if the corresponding variety is nonsingular everywhere. For another example, Spec  $\mathbb{Z}$  and Spec  $\mathbb{Z}[x]$  are both regular. We will give a relative version of nonsingularity later (the notion of a smooth morphism).

# 8 Excellent rings and schemes

A quasiexcellent ring is a noetherian ring R with the following properties.

- (a) For any prime ideal  $\mathfrak{p}$  of R and any homomorphism  $R \to K$  with K a field, the ring  $\hat{R}_{\mathfrak{p}} \otimes_A K$  is regular.
- (b) Any integral domain A which is finite as an R-algebra is generically regular, i.e., there exists  $a \in A$  nonzero such that  $A_a$  is regular.

An excellent ring is a quasiexcellent ring R with the following additional property.

(c) The ring R is universally catenary. That is, for any nonnegative integer n and any two prime ideals  $\mathfrak{p}_1 \subseteq \mathfrak{p}_2$  of  $R[x_1, \ldots, x_n]$ , any two maximal chains of prime ideals of  $R[x_1, \ldots, x_n]$  starting with  $\mathfrak{p}_1$  and  $\mathfrak{p}_2$  have the same length.

The class of excellent rings is introduced by Grothendieck in EGA IV part 3 (see §7.8). It includes some natural examples (fields,  $\mathbb{Z}$ , complete local rings, and the series in  $\mathbb{C}[x_1,\ldots,x_n]$  convergent in a neighborhood of the origin) and is stable under nice operations (localization, completion, quotient, polynomial ring). These rings have lots of useful properties: for instance, they are Nagata rings.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Flat morphisms and descent (updated 11 Mar 09)

Hartshorne only treats flatness after cohomology (so see III.9) and doesn't talk about descent at all. The EGA reference for flatness is EGA IV, part 2, §2. I'm not sure if descent is discussed at all in EGA, so I gave references to SGA 1 instead.

## 1 Flat sheaves and flat morphisms

Let  $f: Y \to X$  be a morphism and let  $\mathcal{F}$  be a quasicoherent  $\mathcal{O}_Y$ -module. We say  $\mathcal{F}$  is flat relative to f if for each point  $y \in Y$  with f(y) = x, if we use the map  $f^{\sharp}: \mathcal{O}_{X,x} \to \mathcal{O}_{Y,y}$  to view  $\mathcal{F}$  as a  $\mathcal{O}_{X,x}$ -module, then that module is flat in the usual sense. (The usual sense is that an R-module M is flat if tensoring with it is exact, not just right exact.) If this holds at a particular y, we say  $\mathcal{F}$  is flat at y relative to f.

Two special cases:

- If Y = X, we say that  $\mathcal{F}$  is a flat  $\mathcal{O}_X$ -module; it is equivalent to saying that tensoring with  $\mathcal{F}$  is an exact functor on quasicoherent  $\mathcal{O}_X$ -modules. For instance, any locally free  $\mathcal{O}_X$ -module is flat.
- If  $\mathcal{F} = \mathcal{O}_Y$ , we say that f is a flat morphism. For example, any open immersion is flat.

Note that if  $\mathcal{F}$  is a flat  $\mathcal{O}_Y$ -module and f is a flat morphism, then  $\mathcal{F}$  is flat relative to f. Note that also that flatness is *local on the source*, not just on the target, and stable under base change.

**Lemma.** Let  $X = \operatorname{Spec}(R)$  be an affine scheme, and let M be an R-module. Then M is a flat  $\mathcal{O}_X$ -module if and only if M is a flat R-module.

*Proof.* This should be a familiar fact from commutative algebra: M is flat over R if and only if  $M_{\mathfrak{p}}$  is flat over  $R_{\mathfrak{p}}$  for each prime ideal  $\mathfrak{p}$ . For completeness, I include the proof here.

Suppose first that M is flat. Let  $\mathfrak{p}$  be an ideal and let  $N \to P$  be an injection of  $R_{\mathfrak{p}}$ -modules. We may then view N, P as R-modules and identify

$$M_{\mathfrak{p}} \otimes_R N = M_{\mathfrak{p}} \otimes_{R_{\mathfrak{p}}} N$$

and similarly for P. Since localization is flat,  $R_{\mathfrak{p}}$  is a flat R-algebra, so  $M_{\mathfrak{p}}$  is flat not just over  $R_{\mathfrak{p}}$  but also over R. Hence  $M_{\mathfrak{p}} \otimes N \to M_{\mathfrak{p}} \otimes P$  is injective, so  $M_{\mathfrak{p}}$  is flat over  $R_{\mathfrak{p}}$ .

Suppose next that  $M_{\mathfrak{p}}$  is flat over  $R_{\mathfrak{p}}$  for each  $\mathfrak{p}$ . If  $N \to P$  is an injection of R-modules, we must check that  $M \otimes N \to M \otimes P$  is still injective. Localizing gives  $M_{\mathfrak{p}} \otimes N_{\mathfrak{p}} \to M_{\mathfrak{p}} \otimes P_{\mathfrak{p}}$  (since localization commutes with tensor product), which is injective because  $M_{\mathfrak{p}}$  is flat.  $\square$ 

**Corollary.** Let  $A \to B$  be a homomorphism of rings. Then  $\operatorname{Spec}(B) \to \operatorname{Spec}(A)$  is flat if and only if B is flat as an A-module.

Proof. The statement that  $\operatorname{Spec}(B) \to \operatorname{Spec}(A)$  is flat says that for each  $\mathfrak{q} \in \operatorname{Spec}(B)$  mapping to  $\mathfrak{p} \in \operatorname{Spec}(A)$ , the morphism  $A_{\mathfrak{p}} \to B_{\mathfrak{q}}$  is flat. This follows from  $A \to B$  being flat because the localization  $B_{\mathfrak{p}} \to B_{\mathfrak{q}}$  is flat. Conversely, suppose that this holds. Let  $N \hookrightarrow P$  be an injection of A-modules. Then for each prime ideal  $\mathfrak{p}$  of A, we may view  $B_{\mathfrak{p}} \otimes_A N \to B_{\mathfrak{p}} \otimes_A P$  as a morphism of  $B_{\mathfrak{p}}$ -modules. For each prime ideal  $\mathfrak{q}$  of B over  $\mathfrak{p}$ , tensoring with  $B_{\mathfrak{q}}$  over  $B_{\mathfrak{p}}$  simply gives  $B_{\mathfrak{q}} \otimes_A N \to B_{\mathfrak{q}} \otimes_A P$ . This is injective because  $A \to A_{\mathfrak{p}}$  is flat always and  $A_{\mathfrak{p}} \to B_{\mathfrak{q}}$  is flat by hypothesis.

Applying the previous lemma over  $B_{\mathfrak{p}}$ , we may now deduce that  $B_{\mathfrak{p}} \otimes_A N \to B_{\mathfrak{p}} \otimes_A P$  is injective. That is,  $B_{\mathfrak{p}}$  is flat over A, or equivalently over  $A_{\mathfrak{p}}$ . Applying the previous lemma over A, we deduce that B is flat over A.

The notion of flatness, while useful (especially when we study cohomology), is geometrically somewhat mysterious. For projective morphisms, one can give a geometric interpretation in terms of *Hilbert polynomials*; more on that later. In the interim, you may wish to chew on the following examples. (See Eisenbud-Harris II.3.4 for more examples.)

Let k be an algebraically closed field. The morphism

$$\operatorname{Spec} k[x,t]/(x^2-t) \to \operatorname{Spec} k[t]$$

is flat. If the characteristic of k is not 2, then the fibres above points  $t \neq 0$  are pairs of distinct points whereas the fibre above t = 0 is the doubled origin in Spec k[x].

The morphism

$$\operatorname{Spec} k[x,t]/(x^2-t^2) \to \operatorname{Spec} k[t]$$

is also flat, but the source is not normal. If we replace the source by its normalization, we get two copies of the affine line mapping to one affine line, and this is *also* flat.

Hartshorne gives the example of the family of cubic curves in  $\mathbb{A}^3$  given as parametric equations in u by

$$x = u^2 - 1, y = u^3 - u, z = tu.$$

If we eliminate u and make sure the result is flat over Spec k[t], we get

Spec 
$$k[x, y, z, t]/(t^2(x+1) - z^2, tx(x+1) - yz, xz - ty, y^2 - x^2(x+1)) \to \text{Spec } k[t].$$

The fibre over t = 0 is supported on the plane curve  $y^2 = x^2(x+1), z = 0$  but is not a subscheme of the plane z = 0 in Spec k[x, y, z]: the local ring at the origin contains the nonzero nilpotent element z.

Here are some deep results about flatness. For this one, see EGA 4, part 2, Théoreme 2.4.6

**Theorem 1.** Let  $f: X \to Y$  be a morphism which is flat and locally of finite presentation. Then f is universally open, i.e., any base change of f is an open map (the image of any open set is open) on topological spaces.

For this one, see SGA 1, Exposé IV, Théorème 6.10 or EGA 4, part 3, 11.1.1.

**Theorem 2.** Let  $f: Y \to X$  be a morphism of finite type, with X locally noetherian, and let  $\mathcal{F}$  be a quasicoherent  $\mathcal{O}_Y$ -module. The set of  $y \in Y$  at which  $\mathcal{F}$  is flat relative to f is an open subset of U.

## 2 Faithfully flat morphisms and descent

A morphism which is both flat and surjective is faithfully flat. For instance, if  $\operatorname{Spec}(B) \to \operatorname{Spec}(A)$  is a morphism of affine schemes, then this morphism is faithfully flat if and only if B is faithfully flat in the usual sense, i.e., B is flat over A, and for any A-module M, the map  $M \to M \otimes_A B$  of A-modules is injective.

Faithfully flat morphisms are important because of their role in *descent*, the process of "undoing" a base change. Here is a typical example.

Let  $f: Y \to X$  be a morphism. Let  $\pi_1, \pi_2: Y \times_X Y \to Y$  be the canonical projections. The category of descent data for quasicoherent sheaves relative to f is defined as follows. A descent datum is a quasicoherent  $\mathcal{O}_Y$ -module  $\mathcal{F}$  equipped with an isomorphism  $\psi: \pi_1^*\mathcal{F} \to \pi_2^*\mathcal{F}$ , satisfying the following cocycle condition. Let  $\pi_1, \pi_2, \pi_3: Y \times_X Y \times_X Y \to Y$  be the canonical projections. Use  $\psi$  first to identify  $\pi_1^*\mathcal{F}$  with  $\pi_2^*\mathcal{F}$ , then  $\pi_2^*\mathcal{F}$  with  $\pi_3^*\mathcal{F}$ . The resulting isomorphism  $\pi_1^*\mathcal{F} \to \pi_3^*\mathcal{F}$  must coincide with the one obtained directly by applying  $\psi$  to the first and third factors.

A morphism of two descent data is a morphism  $\mathcal{F} \to \mathcal{G}$  of the underlying  $\mathcal{O}_Y$ -modules, such that the induced morphisms  $\pi_1^*\mathcal{F} \to \pi_1^*\mathcal{G}$  and  $\pi_2^*\mathcal{F} \to \pi_2^*\mathcal{G}$  commute with the isomorphisms  $\psi$ . There is no extra cocycle condition.

In general, there is a functor from quasicoherent  $\mathcal{O}_X$ -modules to descent data taking  $\mathcal{E}$  to  $f^*\mathcal{E}$ , and defining  $\psi$  in the obvious manner.

**Theorem 3** (Faithfully flat descent). Let  $f: Y \to X$  be a faithfully flat, quasicompact morphism. Then the natural functor from quasicoherent  $\mathcal{O}_X$ -modules to descent data for quasicoherent sheaves defined by f is an equivalence of categories.

The reference for this is SGA 1, Exposé VIII, section 1. However, the proof there is written in a somewhat cryptic manner; we will see a somewhat simplified proof in the exercises.

Note that faithfully flat descent for quasicoherent sheaves includes as a special case Galois descent: if L/K is a finite Galois extension of fields, and V is an L-vector space equipped with a semilinear action of Gal(L/K), then V has a basis of invariant elements. (The usual proof uses Noether's nonabelian generalization of Hilbert's Theorem 90, i.e., the fact that the first Galois cohomology set of Gal(L/K) acting on  $GL_n(L)$  is trivial.)

Armed with faithfully flat descent for quasicoherent sheaves, one can now establish descent for various properties of morphisms. (Some of these can be found in EGA 4, part 2.) For example:

**Theorem 4.** Let  $f: Y \to X$  be a morphism, and let  $g: Z \to X$  be a faithfully flat quasicompact morphism. Then f is of finite type if and only if the base change of f by g is of finite type.

*Proof.* Suppose first that  $X = \operatorname{Spec}(A)$ ,  $Y = \operatorname{Spec}(B)$ ,  $Z = \operatorname{Spec}(C)$  are all affine, and that the base change of f by g is of finite type. Then B is the direct limit of its finitely generated A-subalgebras  $B_i$ , and so  $B \otimes_A C$  is the direct limit of the finitely generated C-subalgebras

 $B_i \otimes_A C$ . By hypothesis,  $B \otimes_A C$  is finitely generated as a C-algebra; each generator can itself be written in terms of finitely many elements of B and C. Hence  $B \otimes_A C$  can be generated over C by finitely many elements of B, and so must occur as one of the  $B_i \otimes_A C$ . For that index i, the fact that the inclusion  $B_i \to B$  is an isomorphism follows from the fact that  $B_i \otimes_A C \to B \otimes_A C$  is an isomorphism because C was assumed to be faithfully flat over A.

To finish, we must show that if the base change of f by g is quasicompact, then f is quasicompact. We may assume X is affine, as then is Z because g was required to be quasicompact, as then is  $Y \times_X Z$  by hypothesis. Let  $\{U_i\}$  be an open affine cover of Y. By hypothesis, the open cover  $\{U_i \times_X Z\}$  of  $Y \times_X Z$  admits a finite subcover. Since those  $Z \to X$  is surjective, the corresponding  $U_i$  must then cover Y. Hence Y is a union of finitely many affines, hence quasicompact.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Differentials

See Hartshorne II.8.

## 1 The module of Kähler differentials

Let  $A \to B$  be a homomorphism of rings. The module of Kähler differentials of B over A is a B-module  $\Omega_{B/A}$  equipped with an A-linear derivation  $d: B \to \Omega_{B/A}$  (an A-linear homomorphism satisfying the Leibniz rule  $d(xy) = x \, dy + y \, dx$  for  $x, y \in B$ ; note that this forces d(a) = 0 for  $a \in A$ ), with the following universal property: for any B-module M and any A-linear derivation  $\partial: B \to M$ ,  $\partial$  factors uniquely through d via a B-linear homomorphism  $\Omega_{B/A} \to M$ .

There are two standard ways to construct  $\Omega_{B/A}$ . One is to form the B-module generated by symbols db for  $b \in B$ , modulo the necessary relations:

- (a)  $d(b_1b_2) b_1 db_2 b_2 db_1$  for  $b_1, b_2 \in B$ ;
- (b)  $d(b_1 + b_2) = d(b_1) + d(b_2)$  for  $b_1, b_2 \in B$ ;
- (c) d(a) = 0 for  $a \in A$ .

This obviously has the desired universal property. The other is to let I be the kernel of the multiplication map  $B \otimes_A B \to B$ , and put  $\Omega_{B/A} = I/I^2$  equipped with the map  $d(b) = b \otimes 1 - 1 \otimes b$ . This evidently gives an A-linear derivation. Given a derivation  $\partial : B \to M$ , view  $B \oplus M$  as a B-algebra in by setting  $m_1 m_2 = 0$  for all  $m_1, m_2 \in M$ . Then the formula

$$b_1 \otimes b_2 \rightarrow (b_1b_2, b_1\partial(b_2))$$

induces a ring homomorphism  $B \otimes_A B \to B \oplus M$  under which I maps to M, so  $I^2$  maps to 0 and we get a B-linear map  $I/I^2 \to M$ . Composing with d easily gives back  $\partial$ . The uniqueness of the factorization follows by observing that

$$x \otimes y = xy \otimes 1 - x(y \otimes 1 - 1 \otimes y)$$

so the image of d generates I (and hence  $I/I^2$ ) as a B-module.

For instance, if  $B = A[x_1, \ldots, x_n]$ , then  $\Omega_{B/A}$  is freely generated by  $dx_1, \ldots, dx_n$ . Also, if k is an algebraically closed field and A is a reduced quotient of  $k[x_1, \ldots, x_n]$ , then the Jacobian criterion can be interpreted as saying that A corresponds to a nonsingular variety over k if and only if  $\Omega_{A/k}$  is locally free as an A-module.

For another example, if A is a field and B is a finite field extension, then  $\Omega_{B/A} = 0$  if and only if B is separable over A.

## 2 The sheaf of Kähler differentials

Let  $f: Y \to X$  be a morphism. For each open affine subset  $U = \operatorname{Spec}(A)$  of X and each open affine subset  $V = \operatorname{Spec}(B)$  of  $f^{-1}(U)$ , form the module  $\Omega_{B/A}$ . We would like these to form the sections of a sheaf  $\Omega_{Y/X}$ , but checking the glueing property directly from this definition is a bit awkward.

Fortunately, our second construction of the module of Kähler differentials suggests a global definition of the sheaf  $\Omega_{Y/X}$ . We'll explain this first in case f is separated. In that case,  $\Delta: Y \to Y \times_X Y$  is a closed immersion; let  $\mathcal{I}$  be the corresponding ideal sheaf on  $Y \times_X Y$ . We then put

$$\Omega_{Y/X} = \Delta^*(\mathcal{I}/\mathcal{I}^2).$$

But what if f is not separated? In that case, we still claim that  $\Delta$  is an *immersion*; this follows from the proof of Hartshorne Corollary II.4.2. Then  $\Delta$  gives rise to an ideal sheaf not on  $Y \times_X Y$ , but on some open subscheme containing the image of  $\Delta$ ; we may then proceed as in the separated case.

Useful properties of  $\Omega$ :

- The formation of  $\Omega_{Y/X}$  commutes with base change as follows. If  $g: Z \to X$  is another morphism, then  $\Omega_{Y \times_X Z/Z}$  can be identified canonically with the pullback of  $\Omega_{Y/X}$  along the projection  $Y \times_X Z \to Y$  (Hartshorne, Proposition II.8.10).
- If  $f: Z \to Y$  and  $g: Y \to X$  are morphisms, then there is a natural exact sequence

$$f^*\Omega_{Y/X} \to \Omega_{Z/X} \to \Omega_{Z/Y} \to 0$$

(Hartshorne, Proposition II.8.11).

• If  $f: Y \to X$  is a morphism, and  $j: Z \to Y$  is the closed immersion defined by the ideal sheaf  $\mathcal{I}$  on Y, then there is a natural exact sequence of sheaves on Z:

$$j^*(\mathcal{I}/\mathcal{I}^2) \to j^*(\Omega_{Y/X}) \to \Omega_{Z/X} \to 0$$

(Hartshorne, Proposition II.8.12).

• Let A be a ring, and let  $f: Y = \mathbb{P}_A^n \to X = \operatorname{Spec} A$  be the natural morphism. We then have a short exact sequence

$$0 \to \Omega_{Y/X} \to \mathcal{O}_X(-1)^{\oplus (n+1)} \to \mathcal{O}_Y \to 0$$

(Hartshorne, Theorem II.8.13).

As in the affine case, a variety X over a field k is nonsingular if and only if  $\Omega_{X/k}$  is locally free. Since  $\Omega_{X/k}$  is necessarily finitely generated (deduce this from the case of affine space), there is always an open dense subset U of X which is nonsingular over k.

Suppose X is nonsingular of dimension n (on each component). Then we call the sheaf  $\omega_{X/k} = \wedge^n \Omega_{X/k}$  the canonical sheaf on X; it is locally free of rank 1. As the name suggests,

the canonical sheaf is an omnipresent object in the study of the geometry of varieties; we will see it in the Riemann-Roch theorem, and more generally in Serre duality, but it is also a central player in modern birational geometry, as in the following *very hard* theorem.

**Theorem** (Bircar-Cascini-Hacon-McKernan, Siu). Let X be a smooth projective irreducible variety over  $\mathbb{C}$ . Then the ring

$$\bigoplus_{n=0}^{\infty} \Gamma(X, \omega_{X/k}^{\otimes n})$$

is finitely generated as a  $\mathbb{C}$ -algebra.

## 3 Smooth, unramified, and étale morphisms

Let  $f: Y \to X$  be a morphism of schemes. For each morphism  $g: X' \to X$  with X' affine, and each closed subscheme Z of X' defined by a nilpotent ideal of  $\mathcal{O}(X')$ , we have a canonical map

$$\operatorname{Hom}_X(X',Y) \to \operatorname{Hom}_X(Z,Y).$$

If this map is always injective/surjective/bijective, we say that f is  $formally unramified/smooth/\acute{e}tale$ . We drop the "formally" if f is also locally of finite presentation. These properties have all the expected behaviors (local on the base, stable under base change, descendable down faithfully flat quasicompact morphisms).

The definition above is given in terms of an *infinitesimal lifting property*. There are more practical characterizations in terms of differentials; some of these will be exercises. (See EGA IV, part 4, section 17.)

**Proposition.** The morphism f is formally unramified if and only if  $\Omega_{Y/X} = 0$ .

**Proposition.** If f is locally of finite presentation, then f is étale if and only if f is flat and unramified.

**Proposition.** If f is locally of finite presentation, then f is smooth if and only if f is flat and for each  $x \in X$ , the fibre  $f^{-1}(x)$  is geometrically regular over  $\kappa(x)$ . (That is, for k an algebraic closure of  $\kappa(x)$ ,  $f^{-1}(x) \times_{\operatorname{Spec} \kappa(x)} k$  is regular.)

For example, the projective space  $\mathbb{P}^n_X$  is smooth over X.

The difference between regular and geometrically regular shows up only when the field  $\kappa(x)$  is imperfect. For instance, put  $\kappa = \mathbb{F}_p(x)$ ,  $X = \operatorname{Spec} \kappa$  and  $Y = \operatorname{Spec} \mathbb{F}_p(x^{1/p}) = \operatorname{Spec} \kappa[y]/(y^p - x)$ . Then Y is a regular scheme, but its base change to an algebraic closure k of  $\kappa$  is

Spec 
$$k[y]/(y^p - x) = \text{Spec } k[y]/((y - x^{1/p})^p),$$

which is not regular. For a slightly less trivial example, see Hartshorne exercise III.10.1.

The notion of an étale morphism is an algebro-geometric analogue of the concept of a covering space in topology. As such, it forms the basis for one of the most successful notions of cohomology in algebraic geometry, that of étale cohomology. I probably won't have time to say more than a few words about that at the end of the course.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Divisors, linear systems, and projective embeddings (updated 1 Apr 09)

We conclude the first half of the course by translating into the language of schemes some classical notions related to the concept of a *divisor*. This will serve to explain (in part) why we will be interested in the cohomology of quasicoherent sheaves.

In order to facilitate giving examples, I will mostly restrict to *locally noetherian* schemes. See Hartshorne II.6 for divisors, and IV.1 for Riemann-Roch.

#### 1 Weil divisors

Introduce Hartshorne's hypothesis (\*): let X be a scheme which is noetherian, integral, separated, and regular in codimension 1. The latter means that for each point  $x \in X$  whose local ring  $\mathcal{O}_{X,x}$  has Krull dimension 1, that local ring must be regular.

**Lemma.** Let A be a noetherian local ring of dimension 1. Then the following are equivalent.

- (a) A is regular.
- (b) A is normal.
- (c) A is a discrete valuation ring.

(This is why normalizing a one-dimensional noetherian ring produces a regular ring.)

Warning: for a noetherian integral domain, normal implies regular in codimension 1 but not conversely. You have to add Serre's condition S2: for  $a \in A$ , every associated prime of the principal ideal (a) has codimension 1 when a is not a zerodivisor, and has codimension 0 when a = 0.

A prime (Weil) divisor on X is a closed integral (irreducible and reduced) subscheme of codimension 1. A formal  $\mathbb{Z}$ -linear combination of prime divisors is called a Weil divisor. If only nonnegative coefficients are used, we say the divisor is effective.

For example, let K(X) be the function field of X, i.e., the local ring of X at its generic point. (This equals  $\operatorname{Frac}(\mathcal{O}(U))$  for any nonempty open affine subscheme U of X.) For  $f \in K(X)$  nonzero, we can define a principal divisor associated to f as follows. For each prime divisor Z on X, let  $\eta_Z$  be the generic point of Z. Then  $\mathcal{O}_{X,\eta_Z}$  is a discrete valuation ring; let  $v_Z$  be the valuation. Now define the divisor

$$(f) = \sum_{Z} v_{Z}(f)Z;$$

this makes sense because only finitely many  $v_Z(f)$  are nonzero. (That's because f restricts to an invertible regular function on some nonempty open subscheme U of X, and  $v_Z(f) = 0$  whenever  $Z \not\subseteq X - U$ .)

Let Div X be the group of Weil divisors of X. The principal divisors form a subgroup (since (f) + (g) = (fg)); the quotient by this subgroup is called the *divisor class group* of

X, denoted Cl X. For example, if  $X = \operatorname{Spec}(A)$  with A a Dedekind domain, then  $\operatorname{Div} X$  is the group of fractional ideals, and  $\operatorname{Cl} X$  is the ideal class group. We say two divisors which differ by a principal divisor are *linearly equivalent*.

There are a number of examples in Hartshorne. One of my favorites is that of an *elliptic curve*; here is a summary. Let k be an algebraically closed field (for starters). Let  $P(x,y,z) \in k[x,y,z]$  be a homogeneous polynomial of degree 3 defining a nonsingular subvariety C of  $\mathbb{P}^2_k$ . Pick a point  $O \in C(k)$ . There is a surjective map  $\operatorname{Div} X \to \mathbb{Z}$  mapping each prime divisor P to 1, called the *degree*. This map factors through  $\operatorname{Cl} X$  because each principal divisor has degree 0. The kernel of the degree map  $\operatorname{Cl} X \to \mathbb{Z}$  is generated by (P) - (O) for  $P \in C(k)$ . In fact it is *equal* to the set of such elements: given  $P, Q \in C$ , we first draw the line through P, Q in  $\mathbb{P}^2_k$  and find its third intersection point P with P. We then draw the line through P and P and P in different intersection point P with P. Then

$$(P) + (Q) + (R) \sim (R) + (S) + (O),$$

SO

$$(P) - (O) + (Q) - (O) \sim (S) - (O).$$

#### 2 Cartier divisors

When the scheme X is not regular, there is a more restrictive notion of divisors that turns out to be more useful in many cases.

Let K be the locally constant sheaf associated to the function field K(X). A Cartier divisor on X is a section of the sheaf  $K(X)/\mathcal{O}^{\times}$ . Using the construction of principal divisors, we obtain a map from Cartier divisors to Weil divisors: if the Cartier divisor is represented on some open subset U of X by the rational function  $f \in K(X)$ , then the Weil divisor we get should agree with (f) when restricted to U (i.e., only keep the components of those prime divisors meeting U). This map is injective if X is normal, because an integrally closed noetherian domain is the intersections of its localizations at minimal prime ideals.

**Proposition** (Hartshorne, Proposition II.6.11). Suppose X is locally factorial (i.e., each local ring  $\mathcal{O}_{X,x}$  is a unique factorization domain). Then the previous map is an isomorphism. (In particular, this holds if X is regular, because a regular local ring is factorial by a not-so-easy theorem of commutative algebra.)

Example: if  $X = \operatorname{Spec} k[x, y, z]/(xy - z^2)$ , the ideal (x, z) defines a Weil divisor which is not a Cartier divisor.

Again, there is an obvious notion of a *principal Cartier divisor*, namely one defined by a single element of K(X). The group of Cartier divisors modulo principal divisors is called the *Cartier class group* of X, denoted  $\operatorname{CaCl} X$ .

### 3 The Picard group

The Cartier class group is "usually" the same as the *Picard group*, namely the group of invertible sheaves on X under the tensor product. Namely, if D is a Cartier divisor on X, let  $\mathcal{L}(D)$  be the subsheaf of  $\mathcal{K}$  such that

$$\mathcal{L}(D)(U) = \{ f \in K(X) : ((f) + (D))|_{U} \ge 0 \}.$$

Assuming that X is normal, this is locally free of rank 1, hence an invertible sheaf. This gives a homomorphism from Cartier divisors to the Picard group, which we see kills the principal divisors. The resulting homomorphism is always injective, even without any hypotheses on X (Hartshorne, Corollary II.6.14) but may not be surjective; however, it is surjective if X is integral (Hartshorne, Proposition II.6.15).

Note that if D is effective, then the function 1 defines a global section of  $\mathcal{L}(D)$ . Since  $\mathcal{L}$  is locally principal, we can locally identify  $\mathcal{L}$  with  $\mathcal{O}_X$ ; when we do so, the subsheaf of  $\mathcal{L}(D)$  generated by 1 goes into correspondence with an ideal sheaf of  $\mathcal{O}_X$ , which doesn't depend on any choices. This ideal sheaf defines D as a closed subscheme. In other words, D is the zero locus of a certain section of  $\mathcal{L}(D)$ . More generally, even if D is effective, we can view D as the zero locus of a meromorphic section of  $\mathcal{L}(D)$  (meaning a zero locus of  $\mathcal{L}(D) \otimes_{\mathcal{O}_X} \mathcal{K}_X$ ), and indeed the zero locus of any meromorphic section of  $\mathcal{L}(D)$  is linearly equivalent to D.

## 4 Linear systems

Suppose X is an integral separated scheme of finite type over a field k (which need not be algebraically closed). Let  $\mathcal{L}$  be an invertible sheaf on X. A linear system defined by  $\mathcal{L}$  is the set of zero loci of some k-linear subspace H of  $H^0(X, \mathcal{L})$ . If we take the entire space, that is called the complete linear system defined by  $\mathcal{L}$ .

We can attempt to use the elements of H to define a map  $X \to \mathbb{P}^n_k$ , where  $n = \dim_k(H) - 1$ . This might fail to give a morphism because H may have a base point, i.e., a point in the intersection of all of the divisors in the linear system. In fact, we get a morphism  $X \to \mathbb{P}^n_k$  if and only if H has no base points.

Suppose now that k is algebraically closed, and that X is one-dimensional, projective, irreducible, and nonsingular (i.e., a "curve"). Consider the complete linear system associated to  $\mathcal{L}(D)$  for some divisor D.

- (a) We get a map  $X \to \mathbb{P}_k^n$  if and only if for each closed point  $x \in X$ , we have  $\dim_k H^0(X, \mathcal{L}(D-x)) = \dim_k H^0(X, \mathcal{L}(D)) 1$ . (In other words, there must be a section of  $\mathcal{L}(D)$  not vanishing at x.)
- (b) The map in (a) is injective as a map of sets if and only if for each pair of distinct closed points  $x, y \in X$ , we have  $\dim_k H^0(X, \mathcal{L}(D-x-y)) = \dim_k H^0(X, \mathcal{L}(D)) 2$ . (In other words, there must be a section of  $\mathcal{L}(D)$  vanishing at x but not at y, and vice versa.)

(c) The map in (b) is a closed immersion if and only if for each closed point  $x \in X$ , we have dim  $H^0(X, \mathcal{L}(D-2x)) = \dim_k H^0(X, \mathcal{L}(D)) - 2$ . (In other words, there must be a section of  $\mathcal{L}(D)$  not vanishing at x, and a section vanishing to exact order 1 at x.)

(Condition (c) is needed to ensure that the tangent space at x embeds into the tangent space at the image of x. See Remark 7.8.2.)

Since we would like to know under what circumstances X embeds into a projective space, we would like to be able to compute at least the dimension of  $H^0(X, \mathcal{L}(D))$  for each divisor D. This quest is greatly abetted by the Riemann-Roch theorem, more on which next time.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Divisors on curves and Riemann-Roch (updated 31 Mar 09)

We continue the discussion of divisors but now restricted to curves. Again, see IV.1 for Riemann-Roch and IV.2 for Riemann-Hurwitz.

#### 1 The Riemann-Roch theorem

Again, let X be a (projective, irreducible, nonsingular) curve over an algebraically closed field k. Since X is one-dimensional, the canonical sheaf  $\omega_{X/k}$  coincides with the sheaf of Kähler differentials  $\Omega_{X/k}$ . By a canonical divisor, I mean a divisor K defined by any meromorphic section of  $\omega_{X/k}$ . (This means that a canonical divisor is in fact not canonical in any sense. Sorry about that.)

As in the elliptic curve example, there is a homomorphism Div  $X \to \mathbb{Z}$  sending (P) to 1 for each  $P \in X(k)$ , and this factors through Cl X because any principal divisor has degree 0 (Hartshorne, Corollary II.6.10).

Write l(D) as shorthand for  $\dim_k \Gamma(X, \mathcal{L}(D))$ . The following theorem will be proved later using properties of sheaf cohomology (particularly Serre duality), but in the meantime we will see (in this lecture and in the next problem set) how it tells us many useful things that have no overt relationship to cohomology.

**Theorem** (Riemann-Roch). There exists a nonnegative integer g = g(X) with the following property. For any divisor D and any canonical divisor K,

$$l(D) - l(K - D) = \deg(D) + 1 - g.$$

Corollary. The integer q in Riemann-Roch can be identified as

$$g = l(K) = \dim_k \Gamma(X, \Omega_{X/k}).$$

*Proof.* Take D=0. Then l(D)=1 because any global regular function on a curve (or indeed on any projective variety) is constant. This forces l(K)=g.

The quantity l(K) is called the *genus* of K, or more precisely the *geometric genus*. In case  $k = \mathbb{C}$ , this will end up matching the topological genus of the Riemann surface associated to X.

Corollary. The integer g in Riemann-Roch can also be identified by the formula

$$\deg(K) = 2g - 2.$$

*Proof.* Apply Riemann-Roch with D = K to obtain (by the previous corollary)

$$g-1 = l(K) - l(0) = \deg(K) + 1 - g.$$

Corollary. If deg(D) > 2g - 2, or deg(D) = 2g - 2 and  $D \nsim K$ , then

$$l(D) = \deg(D) + 1 - g \ge g - 1.$$

*Proof.* If  $\deg(D) = 2g - 2$ , then  $\deg(K - D) = 0$ . If  $f \in K(X)$  nonzero satisfies  $(f) + K - D \ge 0$ , we must have equality because the left side has degree 0. Thus l(K - D) is only nonzero if  $K \sim D$ .

If deg(D) > 2g - 2, then deg(K - D) < 0. In this case, (f) + K - D has negative degree and so cannot be effective, so l(K - D) = 0 no matter what.

**Corollary.** For  $g \ge 2$ , for any divisor D of degree at least 2g-1, the complete linear system associated to D defines a closed immersion of D into a projective space.

## 2 The canonical (almost) embedding

The canonical embedding is the map to projective space defined by the complete linear system associated to a canonical divisor K. The name suggests that it is always a closed immersion, but this is only almost true; there are a few exceptions in low genus (for which see the exercises).

**Lemma.** For any point P and any divisor D, we have

$$l(D) \le l(D+P) \le l(D) + 1.$$

Consequently,  $l(D) \leq \deg(D) + 1$ .

*Proof.* We have an exact sequence of sheaves

$$0 \to \mathcal{L}(D) \to \mathcal{L}(D + (P)) \to \mathcal{E} \to 0$$

where  $\mathcal{E}$  is the quotient of  $\mathcal{O}_X$  by the ideal sheaf defining P. So clearly  $l(D) \leq l(D+P)$ . On the other hand, taking global sections yields a short exact sequence

$$0 \to \Gamma(X, \mathcal{L}(D)) \to \Gamma(X, \mathcal{L}(D+(P))) \to \Gamma(X, \mathcal{E})$$

and the last term is one-dimensional over k, so we get  $l(D+P) \leq l(D)+1$ .

**Proposition.** The canonical embedding is a closed immersion if and only if X is not hyperelliptic.

*Proof.* The special cases g=2,3 are discussed in the problem set, so I'll only sketch the general argument. Put D=(P)+(Q) for  $P,Q\in X(k)$  not necessarily distinct. We need to check whether we always have

$$l(K - D) = l(K) - 2 = g - 2.$$

By Riemann-Roch,

$$l(K-D) = l(D) + g - 3$$

so we have an embedding if and only if l(D) = 0 for any effective D of degree 2; but a failure of that defines a two-to-one map to  $\mathbb{P}^1$ , in which case X is hyperelliptic. (Strictly speaking, we should also check for D of degree 1, but it's esay to see that if such D has l(D) > 0, then there exists a rational function on X with a single pole, which gives a degree 1 map to  $\mathbb{P}^1$ . That is,  $X \cong \mathbb{P}^1$ .)

The canonical embedding, and variants of it (e.g., using higher multiples of a canonical divisor) are key tools for studying the moduli space of curves of a given genus. This is "almost" a scheme  $M_g$  which represents the functor taking schemes to families of curves of genus g, except that this functor is not quite representable. It becomes representable in the category of Deligne-Mumford stacks, which extend schemes in much the same way that orbifolds extend manifolds (by allowing quotients by finite group actions).

### 3 The Riemann-Hurwitz formula

Let  $f: X \to Y$  be a finite separable morphism of curves (i.e., the induced field extension k(X)/k(Y) is separable). The ramification divisor of f is defined as

$$R = \sum_{P \in X(k)} \operatorname{length}(\Omega_{X/Y})_P(P),$$

where as usual  $\Omega_{X/Y}$  is the module of Kähler differentials.

Proposition. We have

$$K_{\rm X} \sim f^* K_{\rm Y} + R$$
.

*Proof.* (Compare Hartshorne Proposition IV.2.3.) Note that

$$0 \to f^*\Omega_{Y/k} \to \Omega_{X/k} \to \Omega_{X/Y} \to 0$$

is exact; this follows from properties of Kähler differentials except for the injectivity on the left. But that we can check at generic points, where it follows because k(X) is separable over k(Y).

We can then tensor with  $\Omega_{X/k}^{\vee}$  to obtain another exact sequence

$$0 \to (f^*\Omega_{Y/k}) \otimes \Omega_{X/k}^{\vee} \to \mathcal{O}_X \to \Omega_{X/Y} \otimes \Omega_{X/k}^{\vee} \to 0.$$

However,  $\Omega_{X/Y}$  is supported on finitely many points, so it is isomorphic to its twist by  $\Omega_{X/k}^{\vee}$ . So we really have an isomorphism

$$(f^*\Omega_{Y/k})\otimes\Omega_{X/k}^\vee\cong\mathcal{O}_X/\Omega_{X/Y}.$$

We thus get an equality of associated divisors; these are  $f^*K_Y - K_X$  on the left and -R on the right.

Using Riemann-Roch, we deduce the Riemann-Hurwitz formula.

#### Proposition. We have

$$2g(X) - 2 = (\deg(f))(2g(Y) - 2) + \deg(R),$$

where deg(f) is the degree of f (i.e., the degree of the field extension k(X)/k(Y)).

Moreover, the contribution of  $P \in X(k)$  can sometimes be computed very simply. Namely, put Q = f(P), and pick  $t \in k(Y)$  which generates  $\mathfrak{m}_{Y,Q}$ ; then  $f^*(t)$  generates  $\mathfrak{m}_{X,P}^e$  for some nonnegative integer e. We call  $e = e_P$  the ramification index of P. Then

$$\operatorname{length}(\Omega_{X/Y})_P \ge e_P - 1,$$

with equality if and only if f is tamely ramified, i.e.,  $e_P$  is not divisible by the characteristic of k.

In case  $k = \mathbb{C}$ , the Riemann-Hurwitz formula has a topological meaning: the quantity 2-2g(X) turns out to compute the *Euler characteristic* of the associated Riemann surface. The Euler characteristic (computed using homology, or compactly supported cohomology) is an *additive* invariant of a topological space. If the map f were unramified, then we would have  $\deg(R) = 0$  and the space X would have Euler characteristic equal to  $\deg(f)$  times that of Y. Otherwise, one must subtract  $e_P - 1$  for each point P with  $e_P > 1$ , because you get X from an unramified cover of Y by removing  $e_P$  different points from the fibre (each of which has Euler characteristic 1) and adding one point back in.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Homological algebra (updated 8 Apr 09)

We now enter the second part of the course, in which we use cohomological methods to gain further insight into the theory of schemes. To start with, let us recall some of the basics of homological algebra. The original reference for derived functors is the book *Homological Algebra* of Cartan and Eilenberg, and for cohomological functors is Grothendieck's article *Sur quelques points d'algèbre homologique*; however, any good modern book on homological algebra (e.g., Weibel, *An Introduction to Homological Algebra*) should suffice. (It is worth keeping in mind Lang's suggested exercise in homological algebra: take any book on homological algebra, read the statements of the theorems, and prove them all yourself.)

# 1 Abelian categories

We saw once before the notion of an abelian category. This is a category  $\mathcal{C}$  in which each homset has the structure of an abelian group in a manner compatible with composition, with some additional restrictions designed to make things well-behaved. Let's recall some of these. First of all, there must exist biproducts, i.e., for any nonnegative integer n and any objects  $X_1, \ldots, X_n$  in  $\mathcal{C}$ , there must exist an object Y and morphisms  $\iota_i : X_i \to Y$  and  $\pi_i : Y \to X_i$  for  $i = 1, \ldots, n$  such that Y is the product of the  $X_i$  (using the  $\pi_i$ ) and the coproduct of the  $X_i$  (using the  $\iota_i$ ), and  $\sum_{i=1}^n \iota_i \circ \pi_i = 1$ .

Also, each morphism must have a kernel and a cokernel. A kernel of the morphism  $f: X \to Y$  to be a limit of the diagram

We write Ker(f) for the domain of a kernel. Similarly, a cokernel of f is a colimit of

We write Coker(f) for the codomain of a cokernel.

Finally, we insist that every monomorphsm be the kernel of its cokernel, and every epimorphism be the cokernel of its kernel.

Examples:

- 1. Ab, the category of abelian groups.
- 2.  $\underline{\text{Mod}}_R$ , the category of modules over a ring. We can drop our running commutativity hypothesis if we choose to work with, say, left modules.

3. The category of sheaves on a fixed topological space with values in another abelian category.

I recommend just thinking about the case of abelian groups. The *Freyd-Mitchell embedding* theorem implies that most things you prove about an abelian category can be deduced from the case of abelian groups, where you can use "diagram-chasing" arguments.

## 2 Complexes and exact sequences

Throughout this section, all objects are in a particular abelian category C. A sequence of morphisms

$$\cdots \to C^{i-1} \stackrel{d^{i-1}}{\to} C^i \stackrel{d^i}{\to} C^{i+1} \to \cdots$$

is a complex if the composition of any two of the arrows is zero, i.e.,  $d^i \circ d^{i-1} = 0$  for all i. Note that I number the objects so that the arrows point in the increasing direction; this is called a cohomological grading. If I numbered things the other way, I would have a homological grading. I will mostly talk about the cohomological grading because that is what is most convenient for algebraic geometry. (In a homological grading, you usually write with subscripts instead of superscripts, i.e.,  $d_i: C_i \to C_{i-1}$ .)

The *i-th cohomology* of a complex C, denoted  $h^i(C)$ , is defined as

$$h^{i}(C^{\cdot}) = \frac{\ker(d^{i})}{\operatorname{im}(d^{i-1})}.$$

We say that C is exact if  $h^i(C) = 0$  for all i.

A morphism of complexes  $f: C \to D$  is a commutative diagram

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

With this definition, we obtain a category of complexes with values in C; this is again an abelian category (exercise).

Any morphism  $f^{\cdot}: C^{\cdot} \to D^{\cdot}$  induces maps

$$f^i: h^i(C^{\cdot}) \to h^i(D^{\cdot})$$

for each *i*. We say f is a quasi-isomorphism (or quasiisomorphism, but I'll spare you the doubled vowel) if each  $f^i$  is an isomorphism; for example, this occurs if f is homotopic to the zero map in the following sense. Given two maps  $f^{\cdot}, g^{\cdot}: C^{\cdot} \to D^{\cdot}$ , we say that f and g are homotopic if there exist a sequence of maps

$$k^i \cdot C^i \rightarrow D^{i-1}$$

such that

$$k^{i+1} \circ d^i + d^{i-1} \circ k^i = f - g;$$

this is obviously an equivalence relation. It is an exercise to show that this implies that f and g induce the same maps  $h^i(C^{\cdot}) \to h^i(D^{\cdot})$ . (The collection of maps  $k^i$  are called a *chain homotopy* between f and g.) Important: the fact that a morphism is a quasi-isomorphism is *not* stable under applying functors, but the fact that two morphisms are homotopic is stable under applying functors because it is arrow-theoretic. (This should remind you of the fact that a sequence being exact is not stable under applying functors, but it being a complex is stable.)

The homology functors don't quite capture as much information as possible, just as passing from a filtered object to its associated graded object loses information. A better construction is that of the *derived category* of complexes with values in  $\mathcal{C}$ ; in this construction, one formally inverts all quasi-isomorphisms. This is not completely straightforward, and I won't talk about it more just now.

# 3 The long exact sequence in cohomology

Let

$$0 \rightarrow C^{\cdot} \rightarrow D^{\cdot} \rightarrow E^{\cdot} \rightarrow 0$$

be a short exact sequence of complexes, i.e., a diagram

in which the rows are exact, and the columns are complexes. As was shown in a previous exercise, this leads to a long exact sequence

$$\cdots \to h^{i-1}(C^{\cdot}) \to h^{i-1}(D^{\cdot}) \to h^{i-1}(E^{\cdot}) \stackrel{\delta^{i-1}}{\to} h^{i}(C^{\cdot}) \to h^{i}(D^{\cdot}) \to h^{i}(E^{\cdot}) \to \cdots$$

in which the maps  $h^{\cdot}(C^{\cdot}) \to h^{\cdot}(D^{\cdot})$  and  $h^{\cdot}(D^{\cdot}) \to h^{i-1}(E^{\cdot})$  are the obvious induced ones, and the maps  $\delta^{i}$  are the connecting homomorphisms. (Recall the definition of  $\delta^{i}$ : given an

element x in  $E^{i-1}$  representing a class in  $h^{i-1}(E^{\cdot})$ , use exactness in the row to lift x to  $y \in D^{i-1}$ . Then the image of  $d^{i-1}(y)$  in  $E^{i}$  equals  $d^{i-1}(x) = 0$ , so  $d^{i-1}(y)$  lifts to  $z \in C^{i}$ . The image of  $d^{i}(z)$  in  $D^{i+1}$  equals  $d^{i}(d^{i-1}(y)) = 0$ , so z represents a class in  $h^{i}(C^{\cdot})$ . The fact that this class is well-defined independent of choices, and that the resulting map  $\delta^{i}$  makes the long sequence exact, were part of the earlier exercise.)

## 4 Cohomological functors

Let  $F: \mathcal{C}_1 \to \mathcal{C}_2$  be an additive covariant functor between abelian categories. Recall that F is *left exact* if for any exact sequence

$$0 \rightarrow A_1 \rightarrow A_2 \rightarrow A_3$$

the sequence

$$0 \to F(A_1) \to F(A_2) \to F(A_3)$$

is exact. The functor is right exact if for any exact sequence

$$A_1 \rightarrow A_2 \rightarrow A_3 \rightarrow 0$$

the sequence

$$F(A_1) \to F(A_2) \to F(A_3) \to 0$$

is exact. The functor is exact if it is both left exact and right exact; equivalently, for any exact sequence

$$0 \to A_1 \to A_2 \to A_3 \to 0$$

the sequence

$$0 \to F(A_1) \to F(A_2) \to F(A_3) \to 0$$

is exact. This implies that F preserves exact sequences of any length.

Many interesting functors in mathematics are left or right exact but not exact. For example, for  $\mathcal{C}$  an abelian category and X an object, the functor  $\operatorname{Hom}(X,\cdot)$  carrying Y to  $\operatorname{Hom}(X,Y)$  is left exact. (We saw this previously for  $\operatorname{\underline{Mod}}_R$  but it holds in general.) We would like to be able to quantify the failure of a functor to be exact; our ability to do this is aided by the presence of objects on which the functor behaves well. For instance, in  $\operatorname{\underline{Mod}}_R$ , the functor  $X \otimes_R \cdot$  behaves badly on a general exact sequence. However, if

$$0 \rightarrow Y_1 \rightarrow Y_2 \rightarrow Y_3 \rightarrow 0$$

is a short exact sequence in which  $Y_3$  is a flat R-module, then it can be shown that

$$0 \to X \otimes Y_1 \to X \otimes Y_2 \to X \otimes Y_3 \to 0$$

is again exact. For instance, this holds if  $Y_3$  is a *free* R-module.

Assume now that F is a left exact functor. The idea now is to replace the single bad object X first with the complex  $0 \to X \to 0 \to \cdots$ , then with a quasi-isomorphic complex

$$0 \to X^0 \to X^1 \to \cdots$$

of good objects. If we can lift short exact sequences of maps to short exact sequences of these resolving complexes, we can then use the long exact sequence in cohomology to quantify the failure of right exactness. Namely, our short exact sequence

$$0 \to A \to B \to C \to 0$$

will be replaced by a short exact sequence of complexes

$$0 \to A^{\cdot} \to B^{\cdot} \to C^{\cdot} \to 0.$$

If we have chosen the good objects well, then

$$0 \to F(A^{\cdot}) \to F(B^{\cdot}) \to F(C^{\cdot}) \to 0$$

will still form a short exact sequence of complexes, and its long exact sequence in homology

$$0 \to h^0(F(A^{\cdot})) \to h^0(F(B^{\cdot})) \to h^0(F(C^{\cdot})) \xrightarrow{\delta^0} h^1(F(A^{\cdot})) \cdots$$

will tell us something useful. What we really want is that  $h^0(F(A^{\cdot})) = A$  and so forth, so that this long exact sequence fills in the gap left at the right end of the exact sequence

$$0 \to F(A) \to F(B) \to F(C)$$
.

To quantify this notion, we define a cohomological functor (or  $\delta$ -functor) between abelian categories  $C_1$  and  $C_2$  to be a sequence of functors

$$T^i: \mathcal{C}_1 \to \mathcal{C}_2 \qquad (i=0,1,\dots)$$

plus for each short exact sequence  $0 \to A \to B \to C \to 0$  in  $C_1$  a morphism  $\delta^i : T^i(C) \to T^{i+1}(A)$  functorial in the sequence (I'll let you draw the diagram), such that the sequence

$$0 \to T^0(A) \to T^0(B) \to T^0(C) \xrightarrow{\delta^0} T^1(A) \to T^1(B) \to T^1(C) \xrightarrow{\delta^1} T^2(A) \to \cdots$$

is exact. A cohomological functor is universal if given any other cohomological functor U and a natural transformation  $f^0: T^0 \to U^0$ , there is a unique sequence of natural transformations  $f^i: T^i \to U^i$  starting with  $f^0$  which commute with the  $\delta^i$ . Given  $T^0$ , any two extensions of it to a universal cohomological functor are naturally isomorphic.

This notion does not become useful without a criterion for checking whether a cohomological functor is universal. Here is one. A functor  $F: \mathcal{C}_1 \to \mathcal{C}_2$  between abelian categories is effaceable if for any  $A \in \mathcal{C}_1$ , there is a monomorphism  $u: A \to B$  with F(u) = 0. I like to think of this in the following way. Most of the time, we deal with functors which are kind of "monotonic", in the sense that under some appropriate hypothesis, the bigger the input object into the functor, the bigger the output object. Effaceable functors are quite the opposite!

**Theorem** (Grothendieck). Let  $T^i: \mathcal{C}_1 \to \mathcal{C}_2$  be a cohomological functor such that  $T^i$  is effaceable for each i > 0. Then T is universal.

*Proof.* Here's how to construct the natural transformation from  $T^i$  to  $U^i$ . Given an object A and an index i>0 such that we know the existence and uniqueness of the natural transformation for indices less than i, choose a monomorphism  $u:A\to B$  with  $T^i(u)=0$ . Then form the long exact sequence  $0\to A\to B\to C\to 0$ , apply both cohomological functors, and use the equality u=0 to truncate the upper one:

$$T^{i-1}(A) \longrightarrow T^{i-1}(B) \longrightarrow T^{i-1}(C) \xrightarrow{\delta^{i-1}} T^{i}(A) \longrightarrow 0$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \uparrow \qquad \qquad \uparrow \qquad \qquad \uparrow \qquad \qquad \uparrow \qquad \qquad \uparrow \qquad \qquad \uparrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \uparrow \qquad \qquad \uparrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \uparrow \qquad \qquad \uparrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \uparrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

An easy diagram chase shows that there is a unique arrow  $T^i(A) \to U^i(A)$  making the diagram commute. It remains to check that:

- the arrow  $T^i(A) \to U^i(A)$  does not depend on the choice of u;
- these arrows form a natural transformation.

We leave these verifications as an exercise.

A typical case is when each object  $A \in \mathcal{C}_1$  admits a monomorphism  $u : A \to B$  in which B is *acyclic* for T, that is,  $T^i(B) = 0$  for i > 0. These objects are good in the sense considered above.

**Theorem** (Acyclic resolution theorem). Let  $T: \mathcal{C}_1 \to \mathcal{C}_2$  be a universal cohomological functor. Given  $J \in \mathcal{C}_1$ , suppose  $0 \to A^0 \to A^1 \to \cdots$  is a complex in  $\mathcal{C}_1$  with each A acyclic,  $h^0(A) \cong J$ , and  $h^i(A) = 0$  for i > 0. (That is, this complex is an acyclic resolution of J.) Then for each  $i \geq 0$ , there is an isomorphism  $T^i(h^0(A)) \cong h^i(T^0(A))$  which is functorial in the input data.

#### 5 Derived functors

We are now ready to make some universal cohomological functors. Unfortunately, we are in a bit of a jam: we would like to define them using acyclic resolutions, but the definition of an acyclic object depends on the definition of the cohomological functor. We get out of this vicious circle by identifying some objects which are *always* acyclic.

An object X in an abelian category  $\mathcal{C}$  is *injective* if the functor  $\operatorname{Hom}(\cdot,X):\mathcal{C}^{\operatorname{op}}\to \operatorname{\underline{Ab}}$  is exact. Since this functor is already left exact, it is enough to require something weaker: if  $0\to Y\to Z$  is a monomorphism, then for any morphism  $Y\to X$  we can find some morphism  $Z\to X$  fitting into the diagram:

For instance, in <u>Ab</u>, an object X is injective if and only if it is *divisible*, i.e., the multiplicationby-n maps for each positive integer n are all surjective. You might be more familiar with the dual notion: an object X in an abelian category C is *projective* if the functor  $\text{Hom}(X, \cdot)$ :  $C \to \underline{Ab}$  is exact. In  $\underline{\text{Mod}}_R$ , any *free* module is projective; in fact, a module is projective if and only if it is a direct summand of a free module.

Lemma. Any short exact sequence

$$0 \to I \to B \to C \to 0$$

with I injective is split, i.e., there exists an arrow  $C \to B$  such that  $C \to B \to C$  is an isomorphism.

*Proof.* Apply the definition of injectivity to the monomorphism  $I \to B$  and the arrow  $I \to I$  to get a map  $B \to I$  such that  $I \to B \to I$  is the identity. Then the kernel of  $B \to I$  will be isomorphic to C.

We once again hit a distinction between non-arrow-theoretic and arrow-theoretic conditions; while the property of being a short exact sequence is not preserved under an arbitrary additive functor, the property of being *split* short exact is. That is because a splitting of  $0 \to A \to B \to C \to 0$  specifies a pair of endomorphisms  $e_1, e_2 : B \to B$  whose sum is B, namely  $B \to A \to B$  and  $B \to C \to B$ , and conversely these endomorphisms determine the sequence.

**Proposition.** Let  $T^i$  be a cohomological functor such that  $T^i$  is effaceable for i > 0 (so in particular it is universal). Then for any injective object I,  $T^i(I) = 0$  for i > 0.

*Proof.* Choose a monomorphism  $u: I \to B$  with  $T^i(u) = 0$ , then form the short exact sequence

$$0 \to I \to B \to C \to 0$$
.

Since this sequence splits, the resulting sequences

$$0 \to T^j(I) \to T^j(B) \to T^j(C) \to 0$$

are exact for all j. Consequently, the connecting homomorphism  $\delta^{i-1}: T^{i-1}(C) \to T^i(I)$  is zero. On the other hand, the morphism  $T^j(I) \to T^j(B)$  is just  $T^j(u)$ , which is also zero. So the exactness of the sequence  $T^{i-1}(C) \stackrel{\delta^{i-1}}{\to} T^i(I) \stackrel{T^i(u)}{\to} T^i(B)$  forces  $T^i(I) = 0$ .

This more or less forces us into the following definition. We say that the category C has enough injectives if for any object X there exists a monomorphism  $X \to I$  with I injective. Then any universal cohomological functor can be computed using injective resolutions. On the other hand, given an object X, we can always find an injective resolution; better yet, given any morphism  $X \to Y$  and an injective resolution of X, we can find an injective resolution of Y and a morphism inducing  $X \to Y$  on cohomology. This suggests that we define the right derived functors of a left exact functor F by saying for any object X, if F is an injective resolution of X, put

$$R^i F(X) = h^i(F(I^{\cdot})).$$

**Theorem.** Assume that C has enough injectives. Then the previous definition gives a well-defined cohomological functor, which is effaceable and hence universal.

The effaceability is obvious from the fact that injectives are acyclic under this definition (if X is injective, use  $0 \to X \to 0 \to \cdots$  as the injective resolution). The hard part, or rather the easy but tedious part, is to check that what you are writing down is really a well-defined cohomological functor in the first place. This is so tedious I won't even make you do it as an exercise; rather, I've just asked you to list which compatibilities need to be checked in the first place, which is already a nontrivial effort.

## 6 Examples

Here are some possibly familiar examples of derived functors. Some of these admit reasonable explicit computations; see exercises.

For  $X \in \underline{\mathrm{Mod}}_R$ ,  $X \otimes \cdot$  is a right exact covariant functor from  $\underline{\mathrm{Mod}}_R$  to  $\underline{\mathrm{Mod}}_R$ , hence a left exact covariant functor from  $\underline{\mathrm{Mod}}_R^{\mathrm{op}}$  to  $\underline{\mathrm{Mod}}_R^{\mathrm{op}}$ . The derived functors are called  $\mathrm{Tor}^i(X,\cdot)$ .

**Proposition.** For  $X \in \underline{\mathrm{Mod}}_R$ , the following are equivalent.

- (a) X is flat.
- (b)  $\operatorname{Tor}^{i}(X,Y) = 0$  for any i > 0 and any  $Y \in \operatorname{\underline{Mod}}_{R}$ .
- (c)  $\operatorname{Tor}^1(X, Y) = 0$  for any  $Y \in \operatorname{\underline{Mod}}_R$ .

*Proof.* Given (a), the functor  $X \otimes \cdot$  is exact, so its derived functors are zero, proving (b). Given (b), (c) is trivial. Given (c), for any short exact sequence  $0 \to A \to B \to C \to 0$ , we get a long exact sequence

$$0 \to X \otimes A \to X \otimes B \to X \otimes C \to \operatorname{Tor}^1(X,A) = 0$$

so  $X \otimes A$  is exact, proving (a).

This is of course a totally general argument: if F is a left exact covariant functor, then F is exact iff  $R^iF = 0$  identically for all i > 0 iff  $R^1F = 0$  identically.

Given that the tensor product is symmetric, one would like to identify  $\operatorname{Tor}^{i}(X,Y)$  with  $\operatorname{Tor}^{i}(Y,X)$ . However, the definition of Tor is asymmetric, so this takes a bit of thinking (which I'll do using the dual language of *projective resolutions* and *homology* and lower indices, but you can switch back if you like). Before starting, note that at least the fact that  $\operatorname{Tor}^{i}(X,Y)$  is functorial in X (not just in Y) is clear from the universal property of universal cohomological functors.

Let P and Q be projective resolutions of X and Y, respectively. Then we have a double complex

in which the homology of the bottom row computes  $Tor^{i}(X,Y)$ , the homology of the right column computes  $Tor^{j}(Y,X)$ , and the other rows and columns are exact.

It is now a diagram chase to check that we have canonical isomorphisms  $\operatorname{Tor}^i(Y,X) \cong \operatorname{Tor}^i(X,Y)$ . For instance, say I start with a class in  $\operatorname{Tor}^1(X,Y)$  represented by  $x \in X \otimes Q_1$ . Lift x to  $P_0 \otimes Q_1$ , then push to  $P_0 \otimes Q_0$ . The result maps to 0 in  $X \otimes Q_0$ , so lifts to  $P_1 \otimes Q_0$ ; push to  $P_1 \otimes Y$  to get a class in  $\operatorname{Tor}^1(Y,X)$ . (This is really an example of a *spectral sequence*; more on those a bit later.)

**Corollary.** Let  $0 \to A_1 \to A_2 \to A_3 \to 0$  be an exact sequence of R-modules with  $A_3$  flat. Then for any R-module M,  $0 \to M \otimes A_1 \to M \otimes A_2 \to M \otimes A_3 \to 0$  is again exact.

*Proof.* We have a long exact sequence

$$\operatorname{Tor}^1(M, A_1) \to M \otimes A_1 \to M \otimes A_2 \to M \otimes A_3 \to 0$$

but the left term can be identified with  $\operatorname{Tor}^1(A_1, M)$ , which vanishes because  $A_1$  is flat.  $\square$ 

The example of Tor is particularly important in algebraic geometry because of Serre's intersection multiplicity formula. Let X be a regular excellent scheme, let Y, Z be two integral closed subschemes defined by the ideal sheaves  $\mathcal{I}, \mathcal{J}$ , and let x be the generic point of a component of  $Y \cap Z$ . The naïve intersection multiplicity of Y and Z at x is

$$\mathcal{O}_{Y\cap Z,x} = \mathcal{O}_{X,x}/(\mathcal{I}\mathcal{J})_x,$$

and this gives the correct answer when  $\dim(X) = 2$ ,  $\dim(Y) = \dim(Z) = 1$  (meaning the answer that makes Bézout's theorem work) but not in general. Serre found that the "right" multiplicity is

$$\sum_{i} (-1)^{i} \operatorname{length}_{\mathcal{O}_{X,x}} \operatorname{Tor}_{\mathcal{O}_{Z,x}}^{i} (\mathcal{O}_{X,x}/\mathcal{I}_{x}, \mathcal{O}_{X,x}/\mathcal{J}_{x}).$$

It was an open question for a long time to give a "geometric" interpretation of the Tor contributions in this formula; such an interpretation was recently provided by Jacob Lurie using *derived algebraic geometry*. (Roughly speaking, one replaces rings by certain topological rings before applying Spec; the intersection multiplicity then appears as the Euler characteristic of the "derived schematic intersection".)

A similar example occurs using the bifunctor Hom, except that it is really a bifunctor from  $\mathcal{C}^{\text{op}} \to \mathcal{C}$ . (Here  $\mathcal{C}$  can be *any* abelian category, not just  $\underline{\text{Mod}}_R$ .) Anyway, the right derived functors of  $\text{Hom}(X,\cdot)$  are called  $\text{Ext}^i(X,\cdot)$ , and they also occur as derived functors of  $\text{Hom}(\cdot,Y)$  by the double complex argument (with arrows appropriately reversed).

One more important example: if G is a group (considered with the discrete topology, if you must), let  $\mathbb{Z}[G]$  be the *group algebra* of G with coefficients in  $\mathbb{Z}$ , i.e., additively the direct sum  $\bigoplus_{g \in G} \mathbb{Z}[g]$  with  $\mathbb{Z}$ -linear multiplication characterized by [g][h] = [gh]. Then the covariant functor  $\cdot^G : \underline{\mathrm{Mod}}_{\mathbb{Z}[G]} \to \underline{\mathrm{Mod}}_{\mathbb{Z}}$  computing G-invariants is left exact; its derived functors are called *group cohomology* and denoted  $H^{\cdot}(G, M)$ . The covariant functor  $\cdot_G : \underline{\mathrm{Mod}}_{\mathbb{Z}[G]} \to \underline{\mathrm{Mod}}_{\mathbb{Z}}$  computing G-coinvariants (i.e., M maps to the quotient of M by g(m) - m for all  $g \in G$  and  $m \in M$ ) is right exact; its derived functors are called *group homology* and denoted  $H^{\cdot}(G, M)$ . These are actually special cases of the previous example, namely

$$H^{\boldsymbol{\cdot}}(G,M)=\operatorname{Ext}^i_{\operatorname{\underline{Mod}}_{\mathbb{Z}[G]}}(\mathbb{Z},M), \qquad H_{\boldsymbol{\cdot}}(G,M)=\operatorname{Tor}^{\operatorname{\underline{Mod}}_{\mathbb{Z}[G]}}_i(\mathbb{Z},M).$$

(More generally, one could replace  $\mathbb{Z}$  with an arbitrary ring.)

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Sheaf cohomology (updated 13 Apr 09)

In the previous lecture, we discussed the construction of derived functors for left exact additive functors out of on an abelian category that has enough injectives. In this lecture, we specialize to the case of the global sections functor for sheaves on a locally ringed space, and thus obtain the definition of sheaf cohomology.

#### 1 Having enough injectives

I thought I assigned this as homework, but apparently not, so here is the proof.

**Lemma.** The category Ab has enough injectives.

*Proof.* It has been assigned as an exercise that an abelian group G is injective if and only if it is divisible, i.e., if the multiplication by n maps are surjective for all positive integers n.

It remains to show that every group G is isomorphic to a subgroup of a divisible abelian group. For instance, write G = F/H where F is a *free* abelian group, then embed G into  $(F \otimes_{\mathbb{Z}} \mathbb{Q})/H$ . If you want something more canonical, take F to be the free abelian group generated by the elements of G, with the map  $G \to F$  taking each  $g \in G$  to the generator of F indexed by g (a/k/a the adjunction morphism for the forgetful functor  $Ab \to Set$ ).  $\Box$ 

There isn't quite as nice an argument for  $\underline{\text{Mod}}_R$  because we don't have as simple a description of the injective modules. One proof that  $\underline{\text{Mod}}_R$  has enough injectives is assigned as an exercise; another will be given using Grothendieck's criterion later in this lecture.

#### 2 Categories of sheaves have enough injectives

Let X be a locally ringed space, let  $\mathcal{C}$  be an abelian category, and let  $\mathcal{D}$  be the category of sheaves on X with values in  $\mathcal{C}$ ; then  $\mathcal{D}$  is again an abelian category. However, in order to use the definition of derived functors, we need to know that  $\mathcal{D}$  has enough injectives, i.e., that for any object  $A \in \mathcal{D}$ , there exists a monomorphism  $A \to I$  with I injective. I should certainly assume that  $\mathcal{C}$  itself has enough injectives; but then how can we go about constructing injective objects in  $\mathcal{D}$ ?

One method is to try to identify the injective objects in  $\mathcal{D}$ , but that is a bit difficult, even for  $\mathcal{C} = \underline{\mathrm{Ab}}$ . Another method is to construct a large enough class of injective objects using skyscraper sheaves. Let  $x \in X$  be a point and let G be an object of  $\mathcal{C}$ . We may then view G as a sheaf on the one-point topological space  $\{x\}$ ; the skyscraper sheaf at x with values in G, denoted  $i_x(G)$  is the direct image of G along  $\{x\} \to X$ . Its sections are G on any open set containing x and 0 otherwise; its stalks are G at all points in the closure of x and 0 elsewhere.

If we assume that C has colimits, then we can use the adjointness property between direct and inverse image to assert that

$$\operatorname{Hom}_{\operatorname{\underline{Sh}}_{\mathcal{C}}(X)}(\mathcal{F}, i_x(G)) = \operatorname{Hom}_{\mathcal{C}}(\mathcal{F}_x, G).$$

In particular, if G is injective in  $\mathcal{C}$ , then  $i_x(G)$  is injective in  $\underline{\operatorname{Sh}}_{\mathcal{C}}(X)$ . (Remember that this means that  $\operatorname{Hom}(\cdot, i_x(G))$  is an exact functor.)

If we assume that  $\mathcal{C}$  also has arbitrary products, it becomes easy to guess how to embed an arbitrary sheaf  $\mathcal{F}$  into an injective: for each  $x \in X$ , use the hypothesis that  $\mathcal{C}$  has enough injectives to construct a monomorphism  $\mathcal{F}_x \to G_x$ , and then  $\mathcal{F}$  embeds into  $\prod_{x \in X} i_x(G_x)$ . Namely, for  $U \subseteq X$  open, the map

$$\mathcal{F}(U) \to \left(\prod_{x \in X} i_x(G_x)\right)(U) = \prod_{x \in U} G_x = \prod_{x \in U} \mathcal{F}_x$$

takes a section s to the tuple  $(s_x)$  of its germs. This is a monomorphism by the sheaf axiom. Moreover, an arbitrary product of injective objects is injective.

In fact, something even stronger is true, and the proof is similar; see Hartshorne, Proposition III.3.2. (This reproduces the previous statement by taking the sheaf of rings to be a constant sheaf.)

**Proposition.** Let  $(X, \mathcal{O}_X)$  be a ringed space. Then the category of sheaves of  $\mathcal{O}_X$ -modules has enough injectives.

Beware that if X is a locally ringed space, it does not follow that the category of *quasicoherent* sheaves of  $\mathcal{O}_X$ -modules has enough injectives. (However, this is true for affine schemes because  $\underline{\mathrm{Mod}}_R$  has enough injectives.)

#### 3 More on having enough injectives

One can also establish that the category of sheaves has enough injectives using a very general criterion introduced by Grothendieck in *Sur quelques points...* 

**Theorem.** Let C be an abelian category satisfying the following conditions.

- (a) C admits arbitrary (small) direct sums.
- (b) Suppose we are given a monomorphism  $X \to Y$  in C, a totally ordered set I, and an increasing family of subobjects  $Y_i$  of Y indexed by  $i \in I$ . (This last means that we are given a monomorphism  $Y_i \to Y$  for each  $i \in I$ , and a monomorphism  $Y_i \to Y_j$  for each i, j in I with  $i \leq j$ , such that  $Y_i \to Y_j \to Y$  agrees with  $Y_i \to Y$ .) Then inside Y,

$$\left(\sum_{i} Y_{i}\right) \cap X = \left(\sum_{i} (Y_{i} \cap X)\right).$$

In other words, forming the direct limit of the  $Y_i$  commutes with taking the fibred product with X over Y. (The direct limits on both sides exist by (a).)

(c) There exists an object  $U \in \mathcal{C}$  such that for any monomorphism  $X \to Y$  which is not an epimorphism, the map  $\operatorname{Hom}(U,X) \to \operatorname{Hom}(U,Y)$  is also not an epimorphism. (That is, there is a map  $U \to Y$  not factoring through X. Grothendieck calls U a generator of  $\mathcal{C}$ .) Also, the class of isomorphism classes of monomorphisms into U is small (this is automatic if  $\mathcal{C}$  admits a forgetful additive functor to  $\operatorname{Ab}$ ).

Then C has enough injectives.

Before proving this, I should point out that these conditions are sufficiently weak that they are satisfied by  $\underline{\mathrm{Mod}}_R$ . Namely, (a) and (b) are obvious, while (c) holds by taking U=R because then  $\mathrm{Hom}(U,\cdot)$  coincides with the forgetful functor to abelian groups. (It is also possible to prove more directly that  $\underline{\mathrm{Mod}}_R$  has enough injectives, but never mind.)

I should also check a bit more carefully that these conditions are satisfied by the category of sheaves of abelian groups on a locally ringed space. To check (a), note that if  $\mathcal{F}_i$  is a family of sheaves on X, then we may construct the direct sum by taking the sheafification of the presheaf  $U \mapsto \bigoplus_i \mathcal{F}_i(U)$ . We may check (b) stalkwise. To check (c), we take U to be the direct sum over open subsets  $V \subseteq X$  of the pushforward  $j_{V*}(\underline{\mathbb{Z}}_V)$  of the constant sheaf on V with values in  $\mathbb{Z}$ . The point is that for any sheaf  $\mathcal{G}$ ,

$$\operatorname{Hom}\left(\bigoplus_{V} j_{V*}(\underline{\mathbb{Z}}_{V}), \mathcal{G}\right) = \bigoplus_{V} \operatorname{Hom}(j_{V*}(\underline{\mathbb{Z}}_{V}), \mathcal{G})$$
$$= \bigoplus_{V} \operatorname{Hom}(\underline{\mathbb{Z}}_{V}, \mathcal{G}|_{V})$$
$$= \bigoplus_{V} \Gamma(V, \mathcal{G}).$$

You can also use a direct sum over points, as in the previous section.

**Lemma.** Under the conditions of the theorem, an object  $M \in \mathcal{C}$  is injective if and only if for any monomorphism  $V \to U$  into the generator, every morphism  $V \to M$  extends to a morphism  $U \to M$ .

Proof of the theorem. We make a first approximation to the desired construction as follows. Let  $M \in \mathcal{C}$  be any object. Let I(M) be the set of isomorphism classes of pairs (T,t), where  $T \to U$  is a monomorphism and  $t: T \to M$  is a morphism. Consider the map

$$\bigoplus_{(T,t)\in I(M)} T \to M \times U^{I(M)}$$

in which the factor of T coming from a pair (T,t) maps to M via T, maps to the (T,t)-th factor of  $U^{I(M)}$  via the monomorphism  $T \to U$ , and maps to the other factors of  $U^{I(M)}$  via the zero map. Let  $M \times U^{I(M)} \to C(M)$  be the cokernel of that map, and let  $f(M): M \to C(M)$  be the composition of this with the injection of M into the first factor of  $M \times U^{I(M)}$ . One checks using (b) that this is a monomorphism.

By construction, we have a monomorphism  $f(M): M \to I(M)$  such that for any monomorphism  $T \to U$  and any morphism  $T \to M$ , we can extend  $T \to M \to I(M)$  to a morphism  $T \to I(M)$ . This doesn't quite solve our problem because  $M \neq I(M)$ . The trick is to repeat this construction using transfinite induction. Namely, start with  $M_0 = 0$ . For any nonlimit ordinal i, put  $M_{i+1} = f(M_i)$ ; for any limit ordinal, let  $M_i$  be the direct limit of  $M_j$  over j < i. There must then be a least ordinal k such that the cardinality of k is strictly greater than the cardinality of the number of isomorphism classes of monomorphisms into U. Then for any morphism  $T \to M_k$ , the sequence of inverse images of the  $M_j$  in T for j < k must stabilize; that is, T maps into  $M_j$  for some  $M_j$ . Then this extends to a map of U into  $M_{j+1}$ , so  $M_k$  satisfies the condition of the previous lemma.

# 4 Sheaf cohomology for topological spaces and ringed spaces

Let  $\mathcal{C}$  be an abelian category admitting arbitrary products and colimits, and having enough injectives. We have just shown that for any topological space X,  $\underline{\operatorname{Sh}}_{\mathcal{C}}(X)$  also has enough injectives. We may now define the *sheaf cohomology functors*  $H^i:\underline{\operatorname{Sh}}_{\mathcal{C}}(X)\to\mathcal{C}$  to be the right derived functors of the left exact functor  $\Gamma(X,\cdot):\underline{\operatorname{Sh}}_{\mathcal{C}}(X)\to\mathcal{C}$ . In particular,  $H^0(X,\mathcal{F})$  is just another notation for  $\mathcal{F}(X)$  or  $\Gamma(X,\mathcal{F})$ .

If  $(X, \mathcal{O}_X)$  is a ringed space, we can also define derived functors of  $\Gamma(X, \cdot)$  directly on the category of sheaves of  $\mathcal{O}_X$ -modules. The fact that these coincide with the  $H^i$  requires some justification, but it's not hard. One way to see it is to note that the  $H^i$ , when restricted to the category of  $\mathcal{O}_X$ -modules, return  $\mathcal{O}(X)$ -modules, then argue that these are an effaceable cohomological functor and so coincide with the derived functors.

Another argument is to use some acyclic objects which are not injective, remembering that we may use resolutions with these objects to compute derived functors. Here is a cheap supply of acyclic objects. A sheaf  $\mathcal{F}$  on X is flasque (or flabby) if for any inclusion  $V \subseteq U$  of open sets, the restriction map  $\mathcal{F}(U) \to \mathcal{F}(V)$  is surjective. For instance, if X is an irreducible topological space, then any constant sheaf is flasque. (Reminder: for  $C \in \mathcal{C}$ , the constant sheaf  $C_X$  on any space X is the sheafification of the constant presheaf  $U \mapsto C$ .) However, if  $X = \mathbb{R}$  with the usual topology then the sections of  $C_X$  on  $C_X$  are  $C_X$  but on  $C_X$  or  $C_X$  is not flasque unless  $C_X$  on  $C_X$  is not flasque unless  $C_X$  is not flasque unless  $C_X$  on  $C_X$  is not flasque unless  $C_X$  on  $C_X$  is not flasque unless  $C_X$  is

**Lemma.** For any ringed space  $(X, \mathcal{O}_X)$ , any injective  $\mathcal{O}_X$ -module is flasque. In particular (by taking  $\mathcal{O}_X = \underline{\mathbb{Z}}_X$ ), any injective sheaf of abelian groups on X is flasque.

*Proof.* (Compare Hartshorne, Lemma III.2.4.) Let  $\mathcal{I}$  be an injective  $\mathcal{O}_X$ -module. For any open subset U of X, let  $\mathcal{O}_U$  denote the extension by zero of  $\mathcal{O}_X|_U$  to X, i.e., the sheafification of the presheaf assigning V to  $\mathcal{O}_X(V)$  if  $V \subseteq U$  and 0 otherwise. Note that it has stalks  $\mathcal{O}_{X,x}$  for  $x \in U$  and 0 otherwise. (This differs from the direct image under the inclusion  $U \hookrightarrow X$ , which has nonzero sections on any open set meeting V.)

For  $V \subseteq U$  an inclusion of open sets, we get a monomorphism  $\mathcal{O}_V \to \mathcal{O}_U$  of sheaves of  $\mathcal{O}_X$ -modules. Since  $\mathcal{I}$  is injective, this gives a surjection  $\operatorname{Hom}(\mathcal{O}_U, \mathcal{I}) \to \operatorname{Hom}(\mathcal{O}_V, I)$ . But  $\operatorname{Hom}(\mathcal{O}_U, \mathcal{I}) = \mathcal{I}(U)$  and  $\operatorname{Hom}(\mathcal{O}_V, \mathcal{I}) = \mathcal{I}(V)$ , so  $\mathcal{I}$  is flasque.

**Proposition.** Let  $\mathcal{F}$  be a flasque sheaf of abelian groups on a topological space X. Then  $H^i(X,\mathcal{F})=0$  for all i>0.

*Proof.* The argument is a classic example of dimension shifting. Embed  $\mathcal{F}$  into an injective sheaf  $\mathcal{I}$ , and put  $\mathcal{G} = \mathcal{I}/\mathcal{F}$ . Using the fact that  $\mathcal{F}$  is flasque, we find (exercise)

$$0 \to H^0(X, \mathcal{F}) \to H^0(X, \mathcal{I}) \to H^0(X, \mathcal{G}) \to 0$$

is exact. Using this, the long exact sequence in cohomology associated to

$$0 \to \mathcal{F} \to \mathcal{I} \to \mathcal{G} \to 0$$
.

and the fact that  $\mathcal{I}$  is acyclic, we find that  $H^1(X,\mathcal{F})=0$  and

$$H^{i}(X, \mathcal{F}) \cong H^{i-1}(X, \mathcal{G}) \qquad (i > 1).$$

Since  $\mathcal{F}$  is flasque, and  $\mathcal{I}$  is injective and hence flasque by the previous lemma, it follows that  $\mathcal{G}$  is flasque (exercise). Hence by the induction hypothesis, we may deduce  $H^i(X,\mathcal{F}) \cong H^{i-1}(X,\mathcal{G}) = 0$  for i > 1.

#### 5 Sheaf cohomology and topological cohomology

If you know some topology, you might appreciate the following relationship between sheaf cohomology and the usual cohomology of topological spaces. (If not, pretend that the cohomology of the constant sheaf  $\underline{\mathbb{Z}}_X$  is the definition of topological cohomology of a space X, then skip directly to the next section.)

**Theorem.** Let X be a locally contractible topological space. Then the sheaf cohomology of X with coefficients in the constant sheaf  $\underline{\mathbb{Z}}_X$  is canonically isomorphic to the singular cohomology of X.

Recall that X is *contractible* if there is a continuous map  $f: X \times [0,1] \to X$  with f(x,0) = x for all  $x \in X$ , and f(x,1) = f(y,1) for all  $x,y \in X$ ; it is *locally contractible* if each point has a basis of contractible neighborhoods. For instance, all manifolds and CW-complexes are locally contractible.

The singular n-chains in X, collectively denoted  $C_n(X)$ , are formal finite  $\mathbb{Z}$ -linear combinations of continuous maps  $\Delta: T_n \to X$ , where  $T_n$  denotes the standard n-simplex. The boundary map  $\delta: C_n(X) \to C_{n-1}(X)$  takes each simplex  $\Delta$  to its signed boundary, i.e., if  $T_n$  has vertices  $e_0, \ldots, e_n$ , then for  $i = 0, \ldots, n$ , you take  $(-1)^i$  times the restriction to the subsimplex omitting  $e_i$ . These form a homologically graded complex; putting

 $C^n(X) = \operatorname{Hom}_{\mathbb{Z}}(C_n(X), \mathbb{Z})$  gives the *singular n-cochains*, which form a cohomologically graded complex.

Let  $C^n(X)$  be the sheafification of the presheaf  $U \mapsto C^n(U)$ ; it is straightforward to check that in fact  $C^n(X)$  is flasque. Using the hypothesis that X is locally contractible (so that we can check exactness on stalks by running over a basis of contractible neighborhoods), one checks that

$$0 \to \mathcal{C}^0(X) \to \mathcal{C}^1(X) \to \cdots$$

is a resolution of  $\underline{\mathbb{Z}}_X$ . We may thus compute  $H^i(\underline{\mathbb{Z}}_X)$  by computing global sections of this complex.

It remains to check that the natural map

$$C^{\cdot}(X) \to \Gamma(X, \mathcal{C}^{\cdot}(X))$$

is a quasi-isomorphism of complexes. To see this, let us fix an open cover  $\{U_i\}$  of X, and let  $D^{\cdot}(X)$  be the set of singular cochains only defined on simplices contained in some  $U_i$ . One then reduces to the following assertion.

**Lemma.** The restriction  $C^{\cdot}(X) \to D^{\cdot}(X)$  is a homotopy equivalence, with a quasi-inverse defined as follows. Given a cochain in  $D^{\cdot}(X)$ , extend to a cochain on X by mapping each simplex not contained in some  $U_i$  to 0.

This is a standard if tedious calculation; see Spanier's Algebraic Topology.

### 6 Čech cohomology

From the previous section, we know that if X is a contractible topological space, then  $\underline{\mathbb{Z}}_X$  is an acyclic sheaf (because the singular cohomology of X vanishes). This can be used to compute the cohomology of X in terms of the combinatorics of a *good cover*, i.e., an open cover  $\{U_i\}$  of X in which each finite intersection is contractible. (You may have read about this in Bott and Tu, *Differential Forms in Algebraic Topology*.) We will use the same idea later in order to compute the cohomology of quasicoherent sheaves on schemes.

Let X be a topological space, and let  $\mathfrak{U} = \{U_i\}_{i \in I}$  be an open cover of X (i.e., each  $x \in X$  appears in only finitely many  $U_i$ ). For convenience, let us assume the set I is equipped with a total ordering (this helps straighten out some sign conventions). For each finite subset J of I, put  $U_J = \bigcap_{i \in J} U_i$ , with the convention that  $U_\emptyset = X$ .

Let  $\mathcal{F}$  be a sheaf of abelian groups on X. We define the  $\check{C}ech$  complex of  $\mathcal{F}$  defined by the open cover  $\{U_i\}$  as follows. For  $j \geq 0$ , let  $\check{C}^j(\mathfrak{U}, \mathcal{F})$  be the direct product of  $\Gamma(\mathcal{F}, U_J)$ over all (j+1)-element subsets J of I. The differential  $d^j: \check{C}^j(\mathfrak{U}, \mathcal{F}) \to \check{C}^{j+1}(\mathfrak{U}, \mathcal{F})$  is defined as follows: for  $\alpha = (\alpha_J) \in \check{C}^j(\mathfrak{U}, \mathcal{F})$ , we have

$$d^{j}(\alpha)_{J} = \sum_{k=0}^{j+1} (-1)^{k} \operatorname{Res}_{U_{J-\{i_{k}\},J}}(\alpha_{J-\{i_{k}\}}) \qquad J = \{i_{0} \leq \dots \leq i_{j+1}\}.$$

For instance, if there are only two open sets  $U_1$  and  $U_2$ , then you have

$$0 \to \Gamma(\mathcal{F}, U_1) \oplus \Gamma(\mathcal{F}, U_2) \to \Gamma(\mathcal{F}, U_1 \cap U_2) \to 0$$

where the nontrivial map is the difference between the two restrictions. The signs were rigged up to make sure that this is indeed a complex: the point is that if you pull  $i_j$  and  $i_k$  out of a set J in on order and multiply the two resulting signs, you get the opposite sign as if you pulled them out in the opposite order.

It is an easy exercise to check that this gives a complex, and continues to do so if you insert  $\Gamma(X, \mathcal{F})$  in front (with the individual restriction maps to  $\check{C}^0(\mathfrak{U}, \mathcal{F})$ .

It is convenient to also work with a sheafier analogue of this construction. Let  $\check{\mathcal{C}}^j(\mathfrak{U},\mathcal{F})$  be the direct product of  $j_{J*}\mathcal{F}|_{U_J}$  over all (j+1)-element subsets J of I, where  $j_J:U_J\to X$  is the inclusion. The global sections of this are just  $\check{\mathcal{C}}^j(\mathfrak{U},\mathcal{F})$ .

Lemma. The complex

$$0 \to \mathcal{F} \to \check{\mathcal{C}}^0(\mathfrak{U}, \mathcal{F}) \to \check{\mathcal{C}}^1(\mathfrak{U}, \mathcal{F}) \to \cdots$$

 $is\ exact.$ 

*Proof.* (Compare Hartshorne Lemma III.4.2.) It suffices to check exactness on stalks. Pick a point  $x \in X$ ; we may then replace X by some  $U_i$  containing x. In this case, we can construct an explicit chain homotopy k between the identity map and the zero map. Its action can be described as follows: given a j-cochain  $\alpha = (\alpha_J)$ , you make a (j-1)-cochain by identifying  $\alpha_J$  with a section of  $U_{J\setminus\{i\}}$  whenever  $i \in J$ , and discarding the  $\alpha_J$  whenever  $i \notin J$ . To do this correctly, you need to add some signs; I'll leave this to the Hartshorne reference.

We write  $\check{H}^{\cdot}(\mathfrak{U},\mathcal{F}) = h^{\cdot}(\check{C}^{\cdot}(\mathfrak{U},\mathcal{F}))$ . These do *not* form a cohomological functor if we fix the choice of  $\mathfrak{U}$ . As noted in Hartshorne Caution 4.0.2, this is clear for the trivial cover of X by itself because the global sections functor is not exact. However, they do at least give the right answer in the flasque case. (They also give the correct answer in degree 0 no matter what the cover, by the sheaf axiom!)

**Lemma.** If  $\mathcal{F}$  is flasque, then  $\check{H}^i(\mathfrak{U}, \mathcal{F}) = 0$  for i > 0.

*Proof.* In the resolution

$$0 \to \check{\mathcal{C}}^0(\mathfrak{U},\mathcal{F}) \to \check{\mathcal{C}}^1(\mathfrak{U},\mathcal{F}) \to \cdots$$

of  $\mathcal{F}$ , each term is again flasque and hence acyclic for sheaf cohomology. If we then take global sections and compute cohomology of the resulting complex, on one hand we just get  $\check{H}^i(\mathfrak{U},\mathcal{F})$ . On the other hand, by the acyclic resolution theorem, we are also computing  $H^i(X,\mathcal{F})$ , which vanishes for i > 0.

On the other hand, suppose  $\mathfrak{V}$  is a refinement of  $\mathfrak{U}$ , i.e., a new covering  $\{V_j\}_{j\in J}$  equipped with a map  $\lambda: J \to I$  of index sets such that  $V_j \subseteq U_{\lambda(j)}$  for all  $j \in J$ . Then we get a restriction morphism

$$\check{H}^{\cdot}(\mathfrak{U},\mathcal{F}) \to \check{H}^{\cdot}(\mathfrak{V},\mathcal{F})$$

Using refinements, the coverings of X form a direct system, so (since we are working with abelian groups, which admit colimits) we can form the direct limit

$$\check{H}^{\cdot}(X,\mathcal{F}) = \varinjlim_{\mathfrak{U}} \check{H}^{\cdot}(\mathfrak{U},\mathcal{F}).$$

Under certain circumstances, we can show that this computes sheaf cohomology. This won't cover the case of schemes, but we'll deal with that separately later.

**Theorem.** Suppose that X is paracompact, i.e., X is Hausdorff and every open covering refines to a locally finite subcovering. Then the  $\check{H}^i(X,\mathcal{F})$  form a cohomological functor which is effaceable, hence universal, hence canonically isomorphic to  $H^i(X,\mathcal{F})$ . In particular, for any particular covering  $\mathfrak{U}$ , we obtain a morphism  $\check{H}^i(\mathfrak{U},\mathcal{F}) \to H^i(X,\mathcal{F})$  functorial in  $\mathcal{F}$ .

*Proof.* Since X is paracompact, we need only take the direct limit over locally finite coverings. In that case, the functors

$$\mathcal{F}\mapsto \varinjlim_{\mathfrak{U}}\check{C}^{\cdot}(\mathfrak{U},\mathcal{F})$$

are exact (exercise). Given that, we may apply them to a short exact sequence and then take the long exact sequence in cohomology to get the connecting homomorphisms. Effaceability holds because each  $\mathcal{F}$  embeds into a sheaf which is injective, hence flasque, hence acyclic for  $\check{H}^{\cdot}(X,\cdot)$  by an earlier lemma.

All well and good, but what we really want to know is, when can we use the Čech complex associated to a particular complex  $\mathfrak U$  to compute the cohomology of  $\mathcal F$ ? Here is a useful answer in practice. We say the cover  $\mathfrak U$  is good for  $\mathcal F$  if for each J,  $\mathcal F|_{U_J}$  is acyclic. (No hypothesis on X needed.)

**Theorem** (Leray). If  $\mathfrak{U}$  is good for  $\mathcal{F}$ , then the morphisms  $\check{H}^{\cdot}(\mathfrak{U},\mathcal{F}) \to H^{\cdot}(X,\mathcal{F})$  are isomorphisms. That is, the Čech complex  $\check{C}^{\cdot}(\mathfrak{U},\mathcal{F})$  computes the sheaf cohomology of  $\mathcal{F}$ .

*Proof.* As in the proof that Čech cohomology vanishes for flasque sheaves, it would suffice to show that the resolution

$$0 \to \check{\mathcal{C}}^0(\mathfrak{U},\mathcal{F}) \to \check{\mathcal{C}}^1(\mathfrak{U},\mathcal{F}) \to \cdots$$

is acyclic. Unfortunately, we can't directly conclude this from the fact that each  $\mathcal{F}|_{U_J}$  is acyclic, because the direct image  $j_{J*}$  functor need not be exact.

So instead, we argue by dimension-shifting. The claim is evident for i = 0 by the sheaf axiom. Given the claim for all indices less than i, embed  $\mathcal{F}$  into an injective sheaf  $\mathcal{I}$ , and let  $\mathcal{G}$  be the quotient:

$$0 \to \mathcal{F} \to \mathcal{I} \to \mathcal{G} \to 0.$$

On each  $U_J$ ,  $\mathcal{F}$  and  $\mathcal{I}$  are acyclic, so  $\mathcal{G}$  is as well by the long exact sequence in cohomology. Moreover, we have short exact sequences

$$0 \to \Gamma(U_J, \mathcal{F}) \to \Gamma(U_J, \mathcal{I}) \to \Gamma(U_J, \mathcal{G}) \to H^1(U_J, \mathcal{F}) = 0.$$

This means that not only does this short exact sequence of sheaves give rise to a long exact sequence for the  $H^i(X,\cdot)$ , it also gives rise to a long exact sequence for the  $\check{H}^i(\mathfrak{U},\cdot)$  (because we get a short exact sequence of Čech complexes). We thus have a commuting diagram with exact rows:

$$\check{H}^{i-1}(\mathfrak{U},\mathcal{I}) \longrightarrow \check{H}^{i-1}(\mathfrak{U},\mathcal{G}) \longrightarrow \check{H}^{i}(\mathfrak{U},\mathcal{F}) \longrightarrow \check{H}^{i}(\mathfrak{U},\mathcal{I})$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$H^{i-1}(X,\mathcal{I}) \longrightarrow H^{i-1}(X,\mathcal{G}) \longrightarrow H^{i}(X,\mathcal{F}) \longrightarrow H^{i}(X,\mathcal{I})$$

in which the corners are zero (because injective implies flasque, which implies both the ordinary and Čech cohomologies vanish). So we transfer our question about  $\mathcal{F}$  at index i to a question about  $\mathcal{G}$  at index i-1, which we know by the induction hypothesis.

This has practical applications outside of algebraic geometry: you can now use good covers to compute the singular cohomology of ordinary topological spaces! The analogue of this in algebraic geometry will appear next, when we start computing the cohomology of quasicoherent sheaves; the analogue of contractible open subsets in the topological case will turn out to be the *affine* schemes, on which quasicoherent sheaves will be acyclic.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Cohomology of quasicoherent sheaves (updated 25 Apr 09)

There is one more fundamental theorem about affine schemes! Here it is.

### 1 The theorem, and a bogus proof

Let's start with the statement of the fourth fundamental theorem of affine schemes.

**Theorem.** Let X be an affine scheme and let  $\mathcal{F}$  be a quasicoherent sheaf on X. Then  $H^i(X,\mathcal{F}) = 0$  for i > 0, that is,  $\mathcal{F}$  is acyclic for sheaf cohomology.

Here is how *not* to prove this theorem.

Bogus proof of the theorem. Put  $X = \operatorname{Spec} A$ . From the earlier fundamental theorems of affine schemes, we know we can write  $\mathcal{F} = \tilde{M}$  for some A-module M. Since  $\operatorname{\underline{Mod}}_A$  has enough injectives, we can find a monomorphism  $M \to I$  with I an injective A-module. Put N = I/M. Again by the earlier fundamental theorems of affine schemes, we know that the exact sequence

$$0 \to M \to I \to I/M \to 0$$

of A-modules is precisely what you get by taking global sections of the exact sequence

$$0 \to \tilde{M} \to \tilde{I} \to \tilde{I/M} \to 0.$$

So in the long exact sequence in cohomology, the connecting homomorphism into  $H^1(X, \tilde{M})$  is zero. On the other hand,  $H^i(X, \tilde{I}) = 0$  for all i > 0 since  $\tilde{I}$  is injective, so  $H^1(X, \tilde{M})$  is forced to be zero. Moreover, for i > 1,  $H^i(X, \tilde{M}) \cong H^{i-1}(X, \tilde{I/M})$ , so we may prove the higher vanishing by dimension shifting.

What's wrong with this proof? The problem is that while the injectivity of I in  $\underline{\text{Mod}}_A$  implies the injectivity of I in the category of quasicoherent  $\mathcal{O}_X$ -modules, it does not imply injectivity in the category of arbitrary  $\mathcal{O}_X$ -modules, or of sheaves of abelian groups on X. In particular, it is unclear whether injectivity of I implies that I is flasque. One can at least show that I is "basically flasque", in that the restriction from  $\Gamma(X, I) = I$  to  $\Gamma(D(f), I) = I_f$  is surjective, but this isn't really enough to do anything useful.

There are two ways to fix this. One way (used in Hartshorne, and also in the book by Ueno that I recommended earlier) is to restrict attention to noetherian rings, and then prove that an injective module does indeed give rise to a flasque sheaf. The other way (used in EGA) is to compute with Čech cohomology instead of sheaf cohomology, so that you can deal only with finite covers by distinguished opens. That's what I'll do here.

First, however, I should mention that there is an easy argument to show that  $H^1$  vanishes. The following is close to the *third* fundamental theorem of affine schemes; see Hartshorne Proposition II.5.6 for the proof. (Since I won't use this to prove the theorem, you may instead view it as a corollary of the theorem.)

**Lemma.** Let  $X = \operatorname{Spec} A$  be an affine scheme. Let

$$0 \to \mathcal{F}_1 \to \mathcal{F} \to \mathcal{F}_2 \to 0$$

be an exact sequence of  $\mathcal{O}_X$ -modules such that  $\mathcal{F}_1$  is quasicoherent (but don't assume anything about the other two). Then the sequence

$$0 \to \Gamma(X, \mathcal{F}_1) \to \Gamma(X, \mathcal{F}) \to \Gamma(X, \mathcal{F}_2) \to 0$$

is exact.

This implies that the connecting homomorphism  $H^0(X, \mathcal{F}_2) \to H^1(X, \mathcal{F}_1)$  is zero, so  $H^1(X, \mathcal{F}_1)$  injects into  $H^1(X, \mathcal{F})$ . If we then choose  $\mathcal{F}$  to be injective, we deduce  $H^1(X, \mathcal{F}_1) = 0$ .

## 2 Applications

Before proving the theorem, let me mention some corollaries. First, from the Čech cohomology discussion, we deduce the following.

**Corollary.** Let X be a scheme and let  $\mathfrak{U} = \{U_i\}_{i \in I}$  be an open cover of X. Suppose that for each finite subset  $J \subseteq I$ , the intersection  $U_J = \cap_{j \in J} U_j$  is affine. Then for any quasicoherent sheaf  $\mathcal{F}$  on X, the sheaf cohomology of  $\mathcal{F}$  is computed by the Čech cohomology for the cover  $\mathfrak{U}$ ; that is,

$$H^i(X, \mathcal{F}) = \check{H}^i(\mathfrak{U}, \mathcal{F}).$$

Recall that inside a *separated* scheme, the intersection of any two open affines is again affine. We thus have the following; I'll illustrate next time by using this to compute the cohomology of the sheaves  $\mathcal{O}(n)$  on projective space.

Corollary. Let X be a separated scheme and let  $\mathfrak{U} = \{U_i\}_{i \in I}$  be an open affine cover of X. Then for any quasicoherent sheaf  $\mathcal{F}$  on X,

$$H^i(X,\mathcal{F}) = \check{H}^i(\mathfrak{U},\mathcal{F}).$$

Here is an even more specialized corollary, which in itself is not so useful. I mention it because I will prove this directly and use it as a lemma to prove the whole theorem.

**Corollary.** Let A be a ring and choose  $f_1, \ldots, f_n \in A$  which generate the unit ideal. Let  $\mathfrak{U}$  be the open cover of  $X = \operatorname{Spec} A$  by  $D(f_i)$  for  $i = 1, \ldots, n$ . Then for any A-module M,  $\check{H}^0(\mathfrak{U}, \tilde{M}) = M$  and  $\check{H}^i(\mathfrak{U}, \tilde{M}) = 0$  for i > 0.

### 3 A correct proof of the theorem

Following Grothendieck (and I think Serre before him, in the context of varieties), we will prove the last corollary first, and then use that to prove the theorem. So our first order of business is to show that the complex

$$0 \to M \to \check{C}^0(\mathfrak{U}, \tilde{M}) \to \check{C}^1(\mathfrak{U}, \tilde{M}) \to \cdots$$

is exact. Remember that this complex came from the complex of sheaves

$$0 \to \tilde{M} \to \check{\mathcal{C}}^0(\mathfrak{U}, \tilde{M}) \to \check{\mathcal{C}}^1(\mathfrak{U}, \tilde{M}) \to \cdots$$

by taking global sections. We proved in the Čech cohomology lecture that this sequence of sheaves is exact (by computing at stalks). Moreover, each of the constituent sheaves is quasicoherent, for the following reason. Each sheaf in the sequence equals a direct sum of sheaves each of the form  $j_{U*}(\tilde{M}|_U)$  for U an intersection of some of the  $U_j$ . In particular, each such intersection has the form D(g) for some  $g \in A$ . But this sheaf is simply the quasicoherent sheaf associated to the A-module  $M_g$ .

Since we have an exact sequence of quasicoherent sheaves, taking global sections gives us an exact sequence of A-modules. This proves the corollary. So now we know that for any finite cover  $\mathfrak{U}$  of Spec A by distinguished opens,

$$\check{H}^0(\mathfrak{U}, \tilde{M}) = M, \qquad \check{H}^i(\mathfrak{U}, \tilde{M}) = 0 \quad (i > 0).$$

The same holds if we take the direct limit over finite covers by distinguished opens. However, this gives the same result as taking the direct limit over *all* open covers because any cover can be refined to a finite cover by distinguished opens. We conclude that

$$\check{H}^{0}(X, \tilde{M}) = M, \qquad \check{H}^{i}(X, \tilde{M}) = 0 \quad (i > 0);$$

although the theorem that says that the direct limit Čech cohomology also computes sheaf cohomology doesn't apply (because X is not Hausdorff), one can still show that this implies

$$H^{0}(X, \tilde{M}) = M, \qquad H^{i}(X, \tilde{M}) = 0 \quad (i > 0)$$

using the following theorem of Cartan, applied with B being the collection of distinguished open affines.

**Theorem** (Cartan). Let X be a topological space. Let B be a basis of X closed under pairwise intersections. Let  $\mathcal{F}$  be a sheaf of abelian groups on X such that  $\check{H}^i(U,\mathcal{F}) = 0$  for all  $U \in B$ . Then  $\check{H}^i(X,\mathcal{F})$  is naturally isomorphic to  $H^i(X,\mathcal{F})$  for all  $i \geq 0$ .

We will prove this in the next section. It can also be proved using spectral sequences; see the optional handout.

# 4 Comparison of Čech and sheaf cohomology

Before proving Cartan's theorem, here is a lemma which generalizes a fact we already know about flasque sheaves.

**Lemma.** Let X be a topological space. Let  $\mathcal{F}$  be a sheaf of abelian groups on X such that  $\check{H}^1(X,\mathcal{F})=0$ . Then for any short exact sequence

$$0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H} \to 0$$

of sheaves,

$$0 \to \Gamma(X, \mathcal{F}) \to \Gamma(X, \mathcal{G}) \to \Gamma(X, \mathcal{H}) \to 0$$

is exact.

*Proof.* (proof suggested by Fucheng Tan) We need only check surjectivity on the right. Let  $s \in \Gamma(X, \mathcal{H})$  be any section; let  $\mathfrak{U} = \{U_i\}_{i \in I}$  be an open cover of X such that for each  $i \in I$ ,  $s|_{U_i}$  lifts to a section  $t_i \in \Gamma(U_i, \mathcal{G})$ . For  $i, j \in I$ , put

$$u_{ij} = t_i|_{U_i \cap U_j} - t_j|_{U_i \cap U_j} \in \Gamma(U_i \cap U_j, \mathcal{G}).$$

Since  $u_{ij}$  has zero image in  $\Gamma(U_i \cap U_j, \mathcal{G})$ , we may also view as an element of  $\Gamma(U_i \cap U_j, \mathcal{F})$ . With this convention, we see that the  $u_{ij}$  form a Čech 1-cocycle of  $\mathcal{F}$  for the open cover  $\mathfrak{U}$ .

Before proceeding, note that there is a natural way to replace the above data for one cover  $\mathfrak{U}$  with a refinement  $\mathfrak{V} = \{V_j\}_{j \in J}$ . Namely, the refinement comes by definition with a map  $\lambda : J \to I$  such that  $V_j \subseteq U_{\lambda(j)}$  for each j. To pass from  $\mathfrak{U}$  to  $\mathfrak{V}$ :

- replace the collection of the  $t_i$  for  $i \in I$  with the collection of the  $t_{\lambda(j)}|_{V_i}$  for  $j \in I$ ;
- replace the collection of the  $t_{ij}$  for  $i, j \in I$  with the collection of the  $u_{\lambda(k)\lambda(l)}|_{V_k \cap V_j}$  for  $k, l \in I$ .

To avoid excess notation, we will speak of "replacing  $\mathfrak U$  by a refinement" which will also be labeled  $\mathfrak U$ .

Since  $\check{H}^1(X,\mathcal{F}) = 0$  by hypothesis, we can replace  $\mathfrak{U}$  by a refinement in such a way that  $u_{ij}$  become a Čech 1-coboundary. This means that there are sections  $v_i \in \Gamma(U_i,\mathcal{F})$  such that

$$v_i|_{U_i \cap U_j} - v_j|_{U_i \cap U_j} = u_{ij} \qquad (i, j \in I).$$

For  $i \in I$ , we now form

$$w_i = t_i - v_i \in \Gamma(U_i, \mathcal{G}).$$

These sections have the property that on one hand, the image of  $w_i$  in  $\Gamma(U_i, \mathcal{H})$  equals  $s|_{U_i}$  (since  $v_i$ , having come from  $\mathcal{F}$ , maps to zero in  $\mathcal{H}$ ), and on the other hand,

$$w_{i}|_{U_{i}\cap U_{j}} - w_{j}|_{U_{i}\cap U_{j}} = (t_{i}|_{U_{i}\cap U_{j}} - v_{i}|_{U_{i}\cap U_{j}}) - (t_{j}|_{U_{i}\cap U_{j}} - v_{j}|_{U_{i}\cap U_{j}})$$

$$= (t_{i}|_{U_{i}\cap U_{j}} - t_{j}|_{U_{i}\cap U_{j}}) - (v_{i}|_{U_{i}\cap U_{j}} - v_{j}|_{U_{i}\cap U_{j}})$$

$$= u_{ij} - u_{ij} = 0.$$

Hence the  $w_i$  glue to a section  $w \in \Gamma(X, \mathcal{G})$  lifting s, as desired.

*Proof of Cartan's theorem.* The claim is true for i = 0 because of the sheaf axiom. We use this as a basis for induction on i, using dimension shifting. Assume that for some i > 0, the claim is true for every value less than i. Choose a short exact sequence

$$0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H} \to 0$$

with  $\mathcal{G}$  flasque. By the previous lemma, for any  $U \in B$ ,

$$0 \to \Gamma(U, \mathcal{F}) \to \Gamma(U, \mathcal{G}) \to \Gamma(U, \mathcal{H}) \to 0$$

is exact. Let  $\mathfrak{U} = \{U_i\}_{i \in I}$  be an open cover of X by basic open sets. Since B is closed under pairwise intersections, it follows that

$$0 \to \check{C}^{\cdot}(\mathfrak{U}, \mathcal{F}) \to \check{C}^{\cdot}(\mathfrak{U}, \mathcal{G}) \to \check{C}^{\cdot}(\mathfrak{U}, \mathcal{H}) \to 0$$

is an exact sequence of complexes. Since every open cover can be refined to an open cover by basic opens, taking direct limits over all covers is the same as taking direct limits over basic open covers, which means that

$$0 \to \check{C}^{\cdot}(X, \mathcal{F}) \to \check{C}^{\cdot}(X, \mathcal{G}) \to \check{C}^{\cdot}(X, \mathcal{H}) \to 0$$

is again an exact sequence of complexes. The same holds if we replace X by any basic open set U, by the same reasoning.

We now take the long exact sequence in cohomology associated to this short exact sequence of complexes, and compare it to the long exact sequence in sheaf cohomology. We get the diagram

We first notice that  $\check{H}^i(X,\mathcal{G}) = H^i(X,\mathcal{G}) = 0$  because  $\mathcal{G}$  is flasque. If we replace X by a basic open set U and then look at the top sequence, we see that for i > 1,  $\check{H}^{i-1}(U,\mathcal{H})$  is sandwiched between two zero groups, so it is also zero. That is,  $\mathcal{H}$  also satisfies the hypothesis of the theorem.

We may now argue by dimension shifting as follows. The first vertical arrow is an isomorphism (for i=1 this holds by the sheaf axiom, otherwise both groups vanish), the second vertical arrows is an isomorphism by the induction hypothesis, and the fourth vertical arrow is the zero map between zero groups. The five lemma thus implies that the third arrow is an isomorphism.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Cohomology of projective space (updated April 14)

Using Čech cohomology, we now give Serre's computation of the cohomology of the twisting sheaves on projective space, and deduce from it Serre's finiteness theorem. See also Hartshorne III.5 (except that you can ignore the last paragraph at the bottom of page 227, which is irrelevant).

### 1 Finitely generated sheaves

Let  $(X, \mathcal{O}_X)$  be a locally ringed space. An  $\mathcal{O}_X$ -module  $\mathcal{F}$  is finitely generated if for each point  $x \in X$ , there exist an open subset U of X containing x, a nonnegative integer n, and a surjection  $\mathcal{O}_X^{\oplus n}|_U \to \mathcal{F}|_U$  of  $\mathcal{O}_X$ -modules. (In other words,  $\mathcal{F}$  is locally generated by finite collections of sections.)

**Lemma.** Let A be a ring and let M be an A-module. Then M is finite as an A-module if and only if the quasicoherent sheaf  $\tilde{M}$  is finitely generated.

Proof. It is clear that finiteness of M implies that  $\tilde{M}$  is finitely generated. Conversely, suppose  $\tilde{M}$  is finitely generated. We can then cover X with distinguished opens  $X_i = D(f_i)$  on each of which  $\tilde{M}|_{X_i} = \tilde{M}_{f_i}$  is generated by finitely many sections  $m_{ij}/f_i^{h_j}$ . Since X is quasicompact, we need only finitely many i, and the resulting  $m_{ij}$  generate M because they do so stalkwise.

Beware that Hartshorne says a sheaf is *coherent* if it is quasicoherent and finitely generated. This is not the correct definition, but it does agree with the correct definition on a *locally noetherian* scheme, which is the only place he ever uses it. I'll give the proper definition of a coherent sheaf later.

### 2 Odds and ends

We will make frequent use of the following fact.

**Lemma.** Let  $f: Z \to X$  be a closed immersion of locally ringed spaces, and let  $\mathcal{F}$  be a sheaf of abelian groups on Z. Then there are canonical isomorphisms

$$H^i(Z, \mathcal{F}) \to H^i(X, f_* \mathcal{F}) \qquad (i \ge 0).$$

*Proof.* We already know that  $f_*$  preserves flasqueness (previous exercise). We can also see that  $f_*$  is exact by its behavior on stalks:

$$(f_*\mathcal{F})_x = \begin{cases} \mathcal{F}_x & x \in Z\\ 0 & x \notin Z. \end{cases}$$

Finally, we note that we have a canonical isomorphism at the level of  $H^0$ . If we then start with a flasque resolution of  $\mathcal{F}$ , we can either push forward (obtaining another flasque resolution) and then take global sections, or take global sections directly, to obtain the *same* complexes, and in particular the same cohomology.

This will very often allow us to carry out induction arguments on dimension, by setting up a short exact sequence of sheaves on X in which one member is the direct image of a sheaf on Z.

**Lemma.** Let X be a noetherian topological space, and let  $(\mathcal{F}_j)$  be a direct system of abelian sheaves. Then the natural functoriality maps

$$\underline{\lim} H^{\cdot}(X, \mathcal{F}_j) \to H^{\cdot}(X, \underline{\lim} \mathcal{F}_j)$$

(coming from the maps  $\mathcal{F}_j \to \varinjlim \mathcal{F}_j$ ) are isomorphisms.

*Proof.* Fix the index set for the direct system. Then both sides are cohomological functors on the category of direct systems of abelian sheaves for that index set, and the noetherian hypothesis forces the  $H^0$  terms to match (earlier exercise), so it suffices to check that they are both effaceable. For that, it suffices to observe that there is a *functorial* way to embed any sheaf of abelian groups on X into a flasque sheaf; for instance, see Hartshorne exercise II.1.16(e).

#### 3 The result

Before stating the theorem, I need to make one general observation. Let  $\mathcal{F}, \mathcal{G}$  be sheaves of  $\mathcal{O}_X$ -modules on a scheme X, with  $\mathcal{F}$  quasicoherent and flat. I claim there is a natural homomorphism

$$H^0(X,\mathcal{F}) \otimes_{\mathcal{O}_X} H^r(X,\mathcal{G}) \to H^r(X,\mathcal{F} \otimes_{\mathcal{O}_X} \mathcal{G})$$

of  $\Gamma(X, \mathcal{O}_X)$ -modules for any nonnegative integer r. It comes from the facts that:

- both sides are cohomological functors in  $\mathcal{G}$  (using the fact that  $\mathcal{F}$  is flat on the right side, and the fact that  $H^0(X,\mathcal{F})$  is flat over  $\mathcal{O}(X)$  on the left side);
- the left side is effaceable and hence universal;
- there is a natural map for r = 0.

We can also compute this map using Čech complexes.

**Theorem** (Serre). Let A be any ring, fix an integer  $r \geq 1$ , and put  $X = \mathbb{P}_A^r$  and  $S = A[x_0, \ldots, x_n]$ .

(a) The natural map

$$S \to \bigoplus_{n \in \mathbb{Z}} H^0(X, \mathcal{O}_X(n))$$

is an isomorphism of graded S-modules.

- (b) For 0 < i < r and  $n \in \mathbb{Z}$ , we have  $H^i(X, \mathcal{O}_X(n)) = 0$ .
- (c) We have  $H^r(X, \mathcal{O}_X(-r-1)) \cong A$ .
- (d) The natural A-bilinear map

$$H^0(X, \mathcal{O}_X(n)) \times H^r(X, \mathcal{O}_X(-n-r-1)) \to H^r(X, \mathcal{O}_X(-r-1)) \cong A$$

is a perfect pairing of finitely generated free A-modules, for each  $n \in \mathbb{Z}$ . (That is, each side is isomorphic to Hom of the other side into A; in particular, they have the same rank.)

(e) For i > r, we have  $H^i(X, \mathcal{O}_X(n)) = 0$ .

Proof of the theorem. It is enough to compute the cohomology of the sheaf  $\mathcal{F} = \bigoplus_{n \in \mathbb{Z}} \mathcal{O}_X(n)$  and keep track of the grading by n. (This can be seen by applying the previous lemma, but this forces a noetherian hypothesis. But it is also clear without such a hypothesis, because the Čech cohomology computation we are about to do commutes with the direct sums.) For starters, recall that we checked part (a) earlier; see for instance Hartshorne Proposition II.5.13.

We use the obvious Čech resolution by the  $D_+(x_i)$  for i = 0, ..., r. Since the complex vanishes above degree r, we immediately get (e). (This also follows from a general theorem of Grothendieck; see Hartshorne Theorem III.2.7.) To compute  $H^r(X, \mathcal{F})$ , we need the cokernel of

$$d^{r-1}: \prod_{k=0}^{r} S_{x_0 \cdots x_{k-1} x_{k+1} \cdots x_r} \to S_{x_0 \cdots x_r}.$$

View  $S_{x_0\cdots x_r}=A[x_0^\pm,\ldots,x_r^\pm]$  as the free A-module generated by the monomials  $x_0^{e_0}\cdots x_r^{e_r}$  with  $e_0,\ldots,e_r\in\mathbb{Z}$ . The image under  $d^{r-1}$  of the k-th factor of the product is precisely the span of the monomials with  $e_k\geq 0$ . Hence  $H^r(X,\mathcal{F})$  is the free A-module generated by the  $x_0^{e_0}\cdots x_r^{e_r}$  with  $e_0,\ldots,e_r<0$ , graded by degree. In particular, in degree -r-1, we see exactly one monomial  $x_0^{-1}\cdots x_r^{-1}$ , proving (c).

To see (d), we must make the pairing explicit. First, note that there is nothing to check if n < 0, since then  $H^0(X, \mathcal{O}_X(n)) = S_{-n} = 0$  obviously, and  $H^0(X, \mathcal{O}_X(-n-r-1)) = 0$  because there are no monomials of degree greater than -r-1 with all exponents negative. So assume hereafter  $n \geq 0$ . If we identify  $H^0(X, \mathcal{O}_X(n))$  with the A-span of the monomials in  $x_0, \ldots, x_r$  (with nonnegative powers) of degree n, then the pairing with  $H^r(X, \mathcal{F})$  (the A-span of the monomials of degree -n-r-1 in  $x_0^{-1}, \ldots, x_r^{-1}$ ) is to simply multiply together and throw away everything except the term  $x_0^{-1} \cdots x_r^{-1}$ . This implies (c).

It remains to prove (b), which we do by induction on r. The base case is r = 1, for which there is nothing to check because 0 < i < r is impossible. Before running the induction, we note that if we localize the Čech complex by inverting  $x_r$ , we get the corresponding Čech complex on the open set  $D_+(x_r)$ , which is affine. So the localized Čech complex must be acyclic since it computes the cohomology of a quasicoherent sheaf on an affine scheme. On the other hand, localizing in  $x_r$  is exact, so it commutes with taking cohomology; that is,

the localization  $H^i(X, \mathcal{F})_{x_r} = 0$  for i > 0. In other words, every element of  $H^i(X, \mathcal{F})$  is annihilated by some power of  $x_r$ .

It thus suffices to show that for 0 < i < r, multiplication by any power of  $x_r$  is injective on  $H^i(X, \mathcal{F})$ ; it also suffices to check multiplication by  $x_r$  itself. Look at the exact sequence

$$0 \to S(-1) \stackrel{\times x_r}{\to} S \to S/(x_r) \to 0$$

of graded S-modules. Writing  $H \cong \mathbb{P}_A^{r-1}$  for the hyperplane  $x_r = 0$  and  $j: H \to X$  for the inclusion, this sheafifies to

$$0 \to \mathcal{F}(-1) \to \mathcal{F} \to \bigoplus_{n \in \mathbb{Z}} (j_* \mathcal{O}_H)(n) \to 0.$$

Let's take the long exact sequence in homology. In degree 0 we get back our original sequence, so the connecting homomorphism into  $H^1(X, \mathcal{F}(-1))$  is zero. That (which holds even in the base case) plus the induction hypothesis, which implies that  $H^i(X, \bigoplus_n (j_*\mathcal{O}_H)(n)) = H^i(H, \bigoplus_n \mathcal{O}_H(n)) = 0$  for 0 < i < r - 1, gives us the bijectivity of multiplication by  $x_r$  on  $H^i(X, \mathcal{F})$  for  $i = 0, \ldots, r-2$  and injectivity for i = r-1. This is enough to get  $H^i(X, \mathcal{F}) = 0$  for 0 < i < r.

## 4 Finiteness of cohomology on projective schemes

Using the previous calculation, Serre was able to derive a powerful finiteness and vanishing theorem for cohomology on projective schemes. First, we need another result of Serre (Hartshorne II.5.17 except without the noetherian hypothesis).

**Theorem.** Let A be a ring, let  $X \to \mathbb{P}_A^r$  be a closed immersion for some  $r \geq 1$ , and let  $\mathcal{O}_X(1)$  be the pullback of the twisting sheaf. Let  $\mathcal{F}$  be a finitely generated quasicoherent sheaf on X. Then there exists an integer  $n_0$  such that for all  $n \geq n_0$ ,  $\mathcal{F}(n)$  is generated by a finite number of global sections.

Proof. By replacing  $\mathcal{F}$  by its direct image, we reduce to the case  $X = \mathbb{P}_A^r$  itself. For  $i = 0, \ldots, r$ , we have  $\mathcal{F}|_{D_+(x_i)} = \tilde{M}_i$  for some finitely generated module  $M_i$  over  $B_i = A[x_0/x_i, \ldots, x_r/x_i]$ . For any  $s \in M_i$ , for  $n \geq n_0$  for some  $n_0$  depending on  $s, x_i^n s$  is a section of  $\mathcal{F}(n)$ . For  $n_0$  large enough, we can lift a set of generators of each  $M_i$  to sections of  $\mathcal{F}(n)$  whenever  $n \geq n_0$ ; this proves the claim.

**Corollary.** With notation as in the previous theorem, we obtain a surjection  $\bigoplus_{i=1}^{m} \mathcal{O}(n) \to \mathcal{F}$  for some  $n \in \mathbb{Z}$ .

For this I need a noetherian hypothesis, but only until we define coherent sheaves.

**Theorem** (Serre). Let A be a noetherian ring, let  $X \to \mathbb{P}_A^r$  be a closed immersion for some  $r \geq 1$ , and let  $\mathcal{O}_X(1)$  be the pullback of the twisting sheaf. Let  $\mathcal{F}$  be a finitely generated quasicoherent sheaf on X.

- (a) The A-modules  $H^i(X, \mathcal{F})$  are finitely generated for  $i \geq 0$ .
- (b) There exists an integer  $n_0$  (depending on  $\mathcal{F}$ ) such that for each i > 0 and  $n \geq n_0$ ,  $H^i(X, \mathcal{F}(n)) = 0$ .

*Proof.* We proceed by descending induction on i. For i > r, we have  $H^i(X, \mathcal{F}) = 0$  because X admits a good over by at most r + 1 open affines.

By the previous corollary, we can write  $\mathcal{F}$  as a quotient of some sheaf  $\mathcal{E}$  which is a direct sum of twisting sheaves. Let  $\mathcal{G}$  be the kernel:

$$0 \to \mathcal{G} \to \mathcal{E} \to \mathcal{F} \to 0$$

Thanks to the noetherian hypothesis, we may conclude that  $\mathcal{G}$  is also finitely generated. The long exact sequence in cohomology gives:

$$\cdots \to H^i(X,\mathcal{E}) \to H^i(X,\mathcal{F}) \to H^{i+1}(X,\mathcal{G}) \to \cdots$$

Given the claim for i + 1, we know that the right term is finitely generated as an A-module. The left term is a sum of things of the form  $H^i(X, \mathcal{O}_X(n))$  for various  $n \in \mathbb{Z}$ , and we already computed those and saw that they were finitely generated as A-modules. Again since A is noetherian, we can conclude that the middle module is finitely generated. This proves (a).

To get (b), twist by n and then again take the long exact sequence in cohomology:

$$\cdots \to H^i(X, \mathcal{E}(n)) \to H^i(X, \mathcal{F}(n)) \to H^{i+1}(X, \mathcal{G}(n)) \to \cdots$$

For n large, the right module vanishes by the induction hypothesis, while the left module vanishes by the explicit calculation, so the middle group vanishes.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Hilbert polynomials and flatness (revised 17 Apr 09)

See Hartshorne III.9 again.

#### 1 Hilbert polynomials

Let k be a field (not necessarily algebraically closed). Let  $j: X \to \mathbb{P}_k^r$  be a closed immersion for some  $r \geq 1$ . Write  $\mathcal{O}_X(1)$  for the inverse image by j of the twisting sheaf  $\mathcal{O}(1)$ . Let  $\mathcal{F}$  be a finitely generated quasicoherent sheaf on X.

The Euler characteristic of  $\mathcal{F}$  is defined as

$$\chi(X,\mathcal{F}) = \sum_{i=0}^{\infty} (-1)^i \dim_k H^i(X,\mathcal{F});$$

we know from Serre's finiteness theorem that each summand is finite, and we also know that there are no terms in dimension greater than r. So this is indeed a well-defined integer.

**Lemma.** The Euler characteristic is additive in short exact sequences; that is, if

$$0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H} \to 0$$

is exact, then

$$\chi(X,\mathcal{G}) = \chi(X,\mathcal{F}) + \chi(X,\mathcal{H}).$$

*Proof.* Exercise in the long exact sequence in cohomology.

Corollary. If

$$0 \to \mathcal{F}_1 \to \cdots \to \mathcal{F}_n \to 0$$

is an exact sequence of finitely generated quasicoherent sheaves, then

$$\sum_{i=1}^{n} (-1)^i \chi(X, \mathcal{F}_i) = 0.$$

**Theorem.** There exists a polynomial  $P(z) \in \mathbb{Q}[z]$  such that

$$\chi(X, \mathcal{F}(n)) = P(n) \qquad (n \in \mathbb{Z}).$$

Moreover, the degree of P is at most the dimension of X.

*Proof.* By replacing  $\mathcal{F}$  by  $j_*\mathcal{F}$ , we may reduce to the case  $X = \mathbb{P}_k^r$ . Also, changing the base field doesn't change any of the dimensions (e.g., by looking at Čech cohomology; this is a special case of the *flat base change theorem*), so we may assume k is algebraically closed.

We proceed by induction on the dimension of the support of  $\mathcal{F}$ . If that support is empty (i.e.,  $\mathcal{F}$  is the zero sheaf), then obviously P(z) = 0 works.

Otherwise, form an exact sequence

$$0 \to \mathcal{G} \to \mathcal{F}(-1) \stackrel{\times x_r}{\to} \mathcal{F} \to \mathcal{H} \to 0$$

and note that  $\mathcal{G}$  and  $\mathcal{H}$  have support of lower dimension than  $\mathcal{F}$  provided that we ensure that the hyperplane  $x_r = 0$  does not contain any component of the support of  $\mathcal{F}$ . (We can arrange this given that k is algebraically closed; see exercises. In fact, k infinite would be sufficient.) By the induction hypothesis, we know that  $\chi(\mathbb{P}_k^r, \mathcal{F}(n)) - \chi(\mathbb{P}_k^r, \mathcal{F}(n-1))$  is a polynomial in n of degree at most dim( $\operatorname{Supp} \mathcal{F}$ ) – 1. It is an elementary exercise in algebra to then see that  $\chi(\mathbb{P}_k^r, \mathcal{F}(n))$  is a polynomial in n of degree at most dim( $\operatorname{Supp} \mathcal{F}$ ).

The polynomial P(n) is called the *Hilbert polynomial* of the sheaf  $\mathcal{F}$ ; in case  $\mathcal{F} = \mathcal{O}_X$ , we call it the *Hilbert polynomial* of the scheme X itself. Note that by Serre's vanishing theorem, for some  $n_0$ , we have

$$P(n) = \dim_k H^0(X, \mathcal{F}) \qquad (n \ge n_0);$$

this was the original definition of the Hilbert polynomial.

For example, the Hilbert polynomial of  $\mathbb{P}_k^r$  itself is  $P(n) = \binom{n+r}{n}$ . For another example, the Hilbert polynomial of the subscheme  $\operatorname{Spec} k[x]/(x^2)$  of  $\mathbb{P}_k^1$  is P(n) = 2, which is the same as the Hilbert polynomial of a scheme consisting of two distinct reduced points. This is suggestive, because this scheme can indeed be written as a flat limit of pairs of distinct points.

#### 2 Flatness and Hilbert polynomials

The Hilbert polynomial can be used to give the following numerical criterion for flatness. (The locally noetherian hypothesis is important; I think one can replace "integral" by "connected and reduced".)

**Theorem.** Let T be an integral (locally) noetherian scheme. Let  $X \subseteq \mathbb{P}_T^r$  be a closed subscheme. Let  $\mathcal{F}$  be a coherent sheaf on X. For each  $t \in T$ , let  $P_t \in \mathbb{Q}[z]$  be the Hilbert polynomial of the pullback of  $\mathcal{F}$  to the fibre  $X_t$  viewed as a subscheme of  $\mathbb{P}_{\kappa(t)}^r$  (where  $\kappa(t) = \mathcal{O}_{T,t}/\mathfrak{m}_{T,t}$  is the residue field of the point t). Then  $\mathcal{F}$  is flat relative to  $X \to T$  if and only if  $P_t$  is constant as a function of t.

In particular, X itself is flat over T if and only if the Hilbert polynomial of  $X_t$  is constant as t varies. This gives us a way to check whether a morphism is flat which we were sorely lacking before.

*Proof.* (Compare Hartshorne Theorem III.9.9, or EGA III §7.9.) We first note that we can reduce to the case  $X = \mathbb{P}_T^r$  by replacing  $\mathcal{F}$  with its direct image. We next note that it suffices to consider the case where  $T = \operatorname{Spec} A$  for A a local integral noetherian ring.

We then show that  $\mathcal{F}$  is flat over T if and only if  $H^0(X, \mathcal{F}(m))$  is finite free over A for m sufficiently large. On one hand, if  $\mathcal{F}$  is flat over T, then so are all the terms in the sheafy

Čech resolution of  $\mathcal{F}(m)$  for the usual open cover  $\mathfrak{U}$  (since open immersions are flat). Taking global sections, we see that the terms of the exact sequence

$$0 \to H^0(X, \mathcal{F}(m)) \to \check{C}^0(\mathfrak{U}, \mathcal{F}(m)) \to \cdots \to \check{C}^r(\mathfrak{U}, \mathcal{F}(m)) \to 0$$

are all flat except possibly for the first term. This then implies flatness of  $H^0(X, \mathcal{F}(m))$  (exercise). Since it's also finitely generated over A by Serre's finiteness theorem, it is free.

On the other hand, if we pick  $m_0$  such that  $H^0(X, \mathcal{F}(m))$  is finite free over A for  $m \geq m_0$ , then we can recover  $\mathcal{F}$  as  $\tilde{M}$  for

$$M = \bigoplus_{m > m_0} H^0(X, \mathcal{F}(m)).$$

Since M is flat, so is  $\mathcal{F}$ .

We now need to show that  $H^0(X, \mathcal{F}(m))$  is finite free for m large if and only if  $P_t$  is constant. I claim that this follows by checking

$$H^0(X_t, \mathcal{F}_t(m)) = H^0(X, \mathcal{F}(m)) \otimes_A \kappa(t)$$

for m large (even if I don't prove this uniformly in t). Namely, if  $H^0(X, \mathcal{F}(m))$  is finite free over A for  $m \geq m_0$ , then for each t, for m large, I find that  $P_t$  equals  $P_{\eta}$  for  $\eta$  the generic point of T. On the other hand, if  $P_t$  is the same for the generic point and the closed point, then I can make m large enough to work for both, and obtain finite freeness of  $H^0(X, \mathcal{F}(m))$ .

To check

$$H^0(X_t, \mathcal{F}_t(m)) = H^0(X, \mathcal{F}(m)) \otimes_A \kappa(t),$$

we may reduce to the case where t is the closed point by replacing A with  $\mathcal{O}_{T,t}$ . Since A is noetherian, we can find a short exact sequence

$$A^{\oplus n} \to A \to \kappa(t) \to 0$$

of A-modules. We can then tensor with  $\mathcal{F}$  to get an exact sequence; it follows (exercise) that

$$H^0(X, \mathcal{F}(m)^{\oplus n}) \to H^0(X, \mathcal{F}(m)) \to H^0(X, \mathcal{F}_t(m)) \to 0$$

is exact for m large. I can pull out the direct sum, and then we read off what we want.  $\square$ 

## 3 Hilbert schemes

It turns out that there is a universal family of closed subschemes of projective space with a fixed Hilbert polynomial.

**Theorem** (Grothendieck). Fix a field k and an integer r. Let  $P(z) \in \mathbb{Q}[z]$  be a polynomial. There exists a noetherian scheme H over Spec k and a closed subscheme X of  $\mathbb{P}^r_H$  which is flat with Hilbert polynomial P(z), such that for any noetherian scheme T and any closed subscheme Y of  $\mathbb{P}^r_T$  which is flat with Hilbert polynomial P(z), there is a unique morphism  $T \to H$  such that  $Y = X \times_H T$  as closed subschemes of  $\mathbb{P}^r_T \cong \mathbb{P}^r_H \times_H T$ .

For instance, one can show that a closed subscheme of  $\mathbb{P}_k^r$  is a d-dimensional plane if and only if it has Hilbert polynomial  $P(n) = \binom{n+d-1}{n}$ . The parameter scheme in this case is the *Grassmannian* of d-dimensional planes in  $\mathbb{P}_k^r$ .

### 4 Hilbert polynomials, degree, and dimension

Some of the basic information contained in the Hilbert polynomial of a scheme is the following.

**Lemma.** Let P(z) be the Hilbert polynomial of a closed subscheme X of  $\mathbb{P}^n_k$ .

- (a) We have deg(P) = dim(X).
- (b) Put  $d = \dim(X)$ . For any d-dimensional plane  $P \subseteq \mathbb{P}^n_k$  such that  $\dim(X \cap P) = 0$ , the length of  $X \cap P$  is d! times the leading coefficient of P. (This length is called the degree of X.)

*Proof.* We may assume k is algebraically closed. We first need to know that for a *generic d*-dimensional plane P (i.e., one chosen outside some closed subscheme of the Grassmannian), we have  $\dim(X \cap P) = 0$ . This follows from the fact that as long as  $X \neq \emptyset$ , for a generic hyperplane H, we have  $\dim(X \cap H) < \dim(X)$  (exercise).

Put  $\mathcal{F} = j_* \mathcal{O}_X$  for  $j: X \to \mathbb{P}^n_k$  the given closed immersion. For H a hyperplane with  $\dim(X \cap H) < \dim(X)$ , we have an exact sequence

$$0 \to \mathcal{F}(-1) \to \mathcal{F} \to \mathcal{G} \to 0$$

where  $\mathcal{G}$  is the direct image of the structure sheaf of  $X \cap H$ . If P(z) is the Hilbert polynomial of X, it follows that the Hilbert polynomial of  $X \cap H$  is P(z) - P(z-1). From this, both claims follows.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Spectral sequences and Čech cohomology

We explain the construction (or rather, one particular construction) of spectral sequences, enough to explain how they are used as part of the computation of the sheaf cohomology of quasicoherent sheaves on affine schemes using Čech cohomology.

I continue to recommend Bott and Tu, Differential Forms in Algebraic Topology as a good reference for spectral sequences.

#### 1 Exact couples

It is handy to start with the following bit of homological algebra. An exact couple is a circular exact sequence

For instance, given an exact sequence  $0 \to A \xrightarrow{i} A \xrightarrow{j} B \to 0$ , we get an exact couple by taking k = 0. A more typical example: given an exact sequence of complexes

$$0 \to A^{\cdot} \to A^{\cdot} \to B^{\cdot} \to 0$$
,

we get an exact couple involving the total cohomologies  $\bigoplus_i h^i(A^{\cdot})$  and  $\bigoplus_i h^i(B^{\cdot})$  using the long exact sequence in cohomology.

From an exact couple we obtain a derived exact couple

as follows.

- Define  $d: B \to B$  as  $d = j \circ k$ . Then  $d \circ d = j \circ k \circ j \circ k = 0$  because  $k \circ j = 0$ , so I can define the cohomology  $B' = h(B) = \ker(d)/\operatorname{im}(d)$ .
- Put  $A' = \operatorname{im}(i)$ .
- We now have an obvious map  $i': A' \to A'$  induced by i.
- We now claim that there is a well-defined map  $j': A' \to B'$  sending i(a) to the class of j(a) for any  $a \in A$ . To make sense of this, we first note that  $j(a) \in \ker(d)$  because  $j \circ k \circ j = 0$ . We next note that if i(a) = 0, then a = k(b) for some  $b \in B$  by exactness, so j(a) = k(j(b)) = d(b).

• We now claim there is a well-defined map  $k': B' \to A'$  induced by k. That is, if  $b \in \ker(d)$ , k' should carry the class of k' to k(b); this belongs to  $\operatorname{im}(a)$  because  $(j \circ k)(b) = 0$ , so k(b) = i(a) for some  $a \in A$  by exactness. This is well-defined:

It is a routine exercise in diagram chasing to verify that this is again exact.

## 2 Filtered complexes and double complexes

Let C be a cohomologically graded complex in nonnegative degrees. A filtration on C is a decreasing sequence of subcomplexes

$$C^{\cdot} = \operatorname{Fil}^{0} C^{\cdot} \supset \operatorname{Fil}^{1} C^{\cdot} \supset \cdots$$

The associated graded complex is

$$\operatorname{Gr}^{i} C^{\cdot} = \operatorname{Fil}^{i} C^{\cdot} / \operatorname{Fil}^{i+1} C^{\cdot}.$$

For instance, suppose  $D^{p,q}$  is a double complex, with differentials  $d_p$  in the p-direction and  $d_q$  in the q-direction. We form a single complex

$$C^k = \bigoplus_{p+q=k} D^{p,q}$$

with derivation  $d_p + (-1)^p d_q$ . (The alternating sign is needed to ensure that this is actually a complex.) We then obtain a filtration on C by setting

$$\operatorname{Fil}^{i} C^{k} = \bigoplus_{p+q=k, p > i} D^{p,q}.$$

## 3 The spectral sequence of a filtered complex

Given a filtered complex C, there are two interesting invariants one can consider. Perhaps the most natural one is the cohomology h(C), equipped with the decreasing filtration

$$\operatorname{Fil}^{i} h^{\cdot}(C^{\cdot}) = \operatorname{im}(h^{\cdot}(\operatorname{Fil}^{i} C^{\cdot})).$$

However, in practice this will usually be something complicated. A less complicated invariant will be the cohomology of the graded complex  $h^{\cdot}(\operatorname{Gr}^{p}C^{\cdot})$ . This is a rather crude approximation to the cohomology of the total complex; it turns out that there is a sequence of refinements that give closer and closer approximations. These constitute the *spectral sequence* associated to the filtered complex.

To start with, take the exact sequence of complexes

$$0 \to \bigoplus_{p \in \mathbb{Z}} \operatorname{Fil}^{p+1} C^{\cdot} \to \bigoplus_{p \in \mathbb{Z}} \operatorname{Fil}^{p} C^{\cdot} \to \bigoplus_{p \in \mathbb{Z}} \operatorname{Gr}^{p} C^{\cdot} \to 0.$$

Identifying the first two members by shifting indices, then taking the long exact sequence in cohomology, we get an exact couple

in which  $E_1 = \bigoplus_{p \in \mathbb{Z}} h^{\cdot}(\operatorname{Gr}^p C^{\cdot})$ . By repeatedly extracting derived exact couples, we get a sequence of exact couples

for h = 1, 2, ... The spectral sequence here is specifically the sequence of groups  $E_h$  equipped with the square-zero endomorphisms  $d_h = j_h \circ k_h$ . Note that  $E_{h+1}$  is just the cohomology of  $E_h$  for  $d_h$ ; the mysterious part is where the next map  $d_{h+1}$  comes from. (The terms in this sequence are often called the *sheets*, or *pages*, of the spectral sequence. The visual significance of these metaphors may become more clear in the next section.)

Without any additional hypotheses, the spectral sequence does not say much. But under certain circumstances, the  $E_h$  "converge" to something useful. Namely, suppose that the complex C comes not only with a filtration but with a grading  $C = \bigoplus_q C_q$ .

**Theorem.** Suppose that for each q, the induced filtration on  $C_q$  has only finitely many distinct steps. Then the spectral sequence converges, in the sense that for each q, the q-th graded piece of  $E_h$  stabilizes for h large. If we let  $E_{\infty}$  denote the sum of the stable graded pieces, then  $E_{\infty}$  is canonically isomorphic to the associated graded group of the filtered cohomology  $\operatorname{Fil}^i h(C)$ .

Note that we still don't quite manage to compute the filtered cohomology, but but only its graded pieces. Still, that information itself is often very very useful. (It is sometimes said that the spectral sequence *abuts* to the filtered cohomology.)

*Proof.* See Bott and Tu, Theorem 14.6.

#### 4 The spectral sequence of a double complex

Let us see how this works in the specific example of a double complex. (I'm just going to state the result; see Bott and Tu for the derivation.) Let  $D^{p,q}$  be a double complex, and let C be the associated filtered single complex. It is customary to draw pictures in this

orientation:

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

without any arrows (at least for now).

Let me redraw this picture writing  $E_0^{p,q}$  for  $D^{p,q}$ , and drawing in the vertical arrows standing for  $(-1)^p d_q$ :

Taking cohomology here gives you exactly  $E_1$ . A quick diagram chase shows that the next differential is precisely the one induced by  $d_p$ :

$$\vdots \qquad \vdots \qquad \vdots$$

$$E_1^{0,2} \longrightarrow E_1^{1,2} \longrightarrow E_1^{2,2} \longrightarrow \cdots$$

$$E_1^{0,1} \longrightarrow E_1^{1,1} \longrightarrow E_1^{2,1} \longrightarrow \cdots$$

$$E_1^{0,0} \longrightarrow E_1^{1,0} \longrightarrow E_1^{2,0} \longrightarrow \cdots$$

Taking cohomology gives the next sheet  $E_2$ . But what is the next differential? Again, I'll just state the answer. Each element of  $E_2$  is represented by an element of  $e_2$  for which for some  $e_3$ ,

$$d_q(b) = 0,$$
  $d_p(b) = (-1)^{p+1} d_q(c).$ 

The next differential carries this class to  $d_p(c)$ , which turns out to be well-defined.

That is, our next page should be drawn like this:

The pattern continues: we have

$$d_r: E_r^{p,q} \to E_r^{p+r,q-r+1}$$

and we can explicitly see the stabilization, since we get an increasingly large bottom left corner with no arrows to or from anyplace other than 0. Let  $E_{\infty}^{p,q}$  denote the stable values; then the associated graded complex of the filtered total cohomology has k-th step given by

$$\bigoplus_{p+q=k} E_{\infty}^{p,q}.$$

# 5 Spectral sequences and Čech cohomology

Here is how spectral sequences make quick work of the comparison theorem between Čech and sheaf cohomology, in the form needed for algebraic geometry. Let X be a topological space, and let  $\mathcal{F}$  be a sheaf of abelian groups on X. Let  $\mathcal{I}$  be a flasque resolution of  $\mathcal{F}$ . Take the double complex

$$D^{p,q} = \check{C}^p(X, \mathcal{I}^q) = \varinjlim_{\mathfrak{U}} \check{C}^p(\mathfrak{U}, \mathcal{I}^q).$$

The trick here is that there are *two* different ways to run the spectral sequence construction from a double complex, depending on how you orient the diagram. As written, we first take Čech cohomology, and then take cohomology of whatever that yields:

$$E_{1a}^{p,q} = \check{H}^p(X, \mathcal{I}^q)$$
  

$$E_{2a}^{p,q} = h^q(\check{H}^p(X, \mathcal{I}^\cdot)).$$

Note that  $E_{1a}^{p,q} = 0$  for p > 0 because the Čech cohomology of a flasque sheaf is zero, whereas  $E_{1a}^{p,0} = \Gamma(X,\mathcal{F})$ . Thus  $E_{2a}^{p,q} = 0$  for p > 0, and in fact  $E_{2a}^{p,q} = E_{\infty a}^{p,q}$  for all p,q. Since we only have one term along each antidiagonal, we actually get much more than usual: we really have computed the cohomology of the total complex, and it is the  $E_{2a}^{0,q} = H^q(X,\mathcal{F})$ .

Now let's run the spectral sequence with the roles of p and q reversed. This time, I take cohomology in the q-direction first, so I start with

$$E_{1h}^{q,p} = h^q(\check{C}^p(X,\mathcal{I}^{\cdot})).$$

This is a rather strange object, but we can repackage it in a useful way by noting that the functor  $\mathcal{I} \to \check{C}^p(X,\mathcal{I})$  preserves exact sequences of presheaves, i.e., sequences of presheaves where the sections over any open give an exact sequence. That means that working with presheaves, I can commute the cohomology computation across the  $\check{C}^p$ . I'll take advantage of this by defining the presheaf  $\mathcal{H}^q$  by

$$\mathcal{H}^q(U) = H^q(\mathcal{I}^{\cdot}(U)) = H^q(U, \mathcal{F}),$$

so that

$$E_{1b}^{q,p} = \check{C}^p(X, \mathcal{H}^q)$$
  
$$E_{2b}^{q,p} = \check{H}^p(X, \mathcal{H}^q)$$

interpreted as the Čech complex associated to a presheaf (defined using the same formula as for sheaves). This spectral sequence must converge to some term  $E_{\infty b}^{q,p}$  giving graded pieces of the total cohomology, which we already identified as the sheaf cohomology of  $\mathcal{F}$  itself.

This isn't useful as an abstract method for dealing with Čech cohomology. However, it is just the thing I need to prove the theorem that I need to finish the argument that quasicoherent sheaves on affine schemes are acyclic.

**Theorem.** Let X be a topological space equipped with a nice basis B (i.e., a basis closed under pairwise intersections; we need not assume  $X \in B$ ). Let  $\mathcal{F}$  be a sheaf of abelian groups on X such that  $\check{H}^i(U,\mathcal{F}) = 0$  for all i > 0 and all  $U \in B$ . Then there are natural isomorphisms  $\check{H}^i(X,\mathcal{F}) \to H^i(X,\mathcal{F})$  for all  $i \geq 0$ .

*Proof.* The natural maps come from the fact that if  $\mathcal{T}$  is an injective resolution of  $\mathcal{F}$ , then the Čech resolution  $\check{\mathcal{C}}(X,\mathcal{F})$  admits a map into  $\mathcal{T}$  which is a quasi-isomorphism, and is well-determined up to a chain homotopy. (This is similar to the homework problem about injective resolutions of complexes; see PS 8, problem 7.)

To prove the theorem, it suffices to check for X equal to an open in B, as then the Leray theorem asserts that we can compute sheaf cohomology using any cover by elements of B, and any open cover refines to such. So assume hereafter  $X \in B$ .

We induct on i, the case i=0 being an easy consequence of the sheaf axiom. Say we know that

$$H^{j}(U, \mathcal{F}) = 0 \qquad (0 < j < i, U \in B).$$

Then the spectral sequence  $E_{\cdot b}$  from above has  $E_{2b}^{q,p}=0$  for 0 < q < i. By staring at the spectral sequence, we see that the terms with q+p=i must already be stable, so the total i-th cohomology must just be

$$E_{2b}^{0,i} = \check{H}^i(X, \mathcal{H}^0) = \check{H}^i(X, \mathcal{F}).$$

Since we also know that the total cohomology is  $H^i(X, \mathcal{F})$ , we obtain the desired isomorphism.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) GAGA (updated 30 Apr 2009)

We now discuss a classic theorem of algebraic geometry, Serre's GAGA, which exposes a tight relationship between algebraic geometry over the complex numbers and complex analytic geometry. By far the best reference for this is Serre's original paper Géométrie algébrique et géométrie analytique. (Thanks to Bjorn Poonen for reporting some errors, which have now been corrected.)

#### 1 Coherent sheaves

In order to discuss GAGA, I need to talk about coherent sheaves not just on schemes, but on analytic spaces. In fact, the notion is well-defined on any locally ringed space.

Let  $(X, \mathcal{O}_X)$  be a locally ringed space. We say a sheaf  $\mathcal{F}$  is coherent if  $\mathcal{F}$  is finitely generated, and for any open subset U of X, any nonnegative integer n, and any homomorphism  $h: \mathcal{O}_X^{\oplus n}|_U \to \mathcal{F}|_U$ , the kernel of h is itself finitely generated. Warning! I originally only required this for h surjective, but I don't think that is enough. (Important note: we don't require the kernel to be generated by finitely many sections over all of U.) This is stronger than saying that  $\mathcal{F}$  is finitely presented, in which case we only require that one such surjection h must have this property. In particular,  $\mathcal{O}_X$  itself need not be coherent.

However, if X is locally noetherian, then all finitely generated quasicoherent sheaves are in fact coherent. This follows from the following result.

**Theorem.** Let A be a noetherian ring, put  $X = \operatorname{Spec} A$ , let V be an open subset of X, and let  $\mathcal{F}$  be an  $\mathcal{O}_X|_V$ -module. Then the following are equivalent.

- (a)  $\mathcal{F}$  is coherent.
- (b)  $\mathcal{F}$  is finitely generated and quasicoherent.
- (c) We have  $\mathcal{F} = \tilde{M}$  for some finitely generated A-module M.

I'm only going to show this for V = X, as this is the only case I need. For the general case, see EGA 1, Théorème 1.5.1.

*Proof.* Even without a noetherian hypothesis, it is obvious that (a) implies (b), and we checked (b) implies (c) in a previous lecture.

To check that (c) implies (a) under the noetherian hypothesis, note that the claim is local, so it suffices to check that the kernel of a homomorphism  $\mathcal{O}_X^{\oplus n}|_{D(f)} \to \mathcal{F}|_{D(f)}$  is finitely generated. It is represented by a homomorphism  $A_f^n \to M_f$  of  $A_f$ -modules, but  $A_f$  is noetherian since A is. Hence the kernel of the homomorphism, being a submodule of a finitely generated  $A_f$ -module, is itself a finitely generated  $A_f$ -module (because A is noetherian).  $\square$ 

Lemma. Let

$$0 \to \mathcal{F}_1 \to \mathcal{F} \to \mathcal{F}_2 \to 0$$

be a short exact sequence of quasicoherent sheaves on a locally ringed space X. Then if any two of  $\mathcal{F}, \mathcal{F}_1, \mathcal{F}_2$  are coherent, so is the third.

Proof. Exercise. 
$$\Box$$

Beware that it is not obvious that the inverse image of a coherent sheaf is coherent, since the defining condition involves looking at all open subsets.

## 2 Analytification of coherent sheaves

In order to state the GAGA theorems, we use the fact that there is a morphism of locally ringed spaces

$$h: \tilde{\mathbb{P}}^r_{\mathbb{C}} \to \mathbb{P}^r_{\mathbb{C}},$$

where the left side is the projective r-space over  $\mathbb{C}$  viewed as a complex manifold (or a complex analytic variety, on which more later). Where does this morphism come from? We'll give a functorial answer later, but for now I'll do something more direct.

For each i = 0, ..., r, put  $X_i = D_+(x_i) \subseteq \mathbb{P}^r_{\mathbb{C}}$ . This space is an affine *n*-space over  $\mathbb{C}$  with coordinates  $x_j/x_i$  for  $j \neq i$ ; let  $\tilde{X}_i$  be the complex analytic affine *r*-space with the same coordinates. There is an obvious map

$$\Gamma(X_i, \mathcal{O}_{X_i}) = \mathbb{C}[x_0/x_i, \dots, x_r/x_i] \to \Gamma(\tilde{X}_i, \mathcal{O}_{\tilde{X}_i});$$

by adjunction, this gives us a morphism

$$\tilde{X}_i \to X_i$$

of locally ringed spaces. These glue to give the morphism I described. Note that  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$  includes only some of the points of  $\mathbb{P}^r_{\mathbb{C}}$  (namely the closed points), but gives them a finer topology (the analytic topology rather than the Zariski topology). This is consistent with the fact that the map  $\tilde{\mathbb{P}}^r_{\mathbb{C}} \to \mathbb{P}^r_{\mathbb{C}}$  is continuous.

What is nice about viewing the analytification process this way is that we can apply operations defined on locally ringed spaces uniformly to both  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$  to  $\mathbb{P}^r_{\mathbb{C}}$ . For instance, for any quasicoherent sheaf  $\mathcal{F}$  on  $\mathbb{P}^r_{\mathbb{C}}$ , the pullback  $h^*\mathcal{F}$  is a quasicoherent sheaf on  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$ .

**Lemma** (Cartan). For any coherent sheaf  $\mathcal{F}$  on  $\mathbb{P}^r_{\mathbb{C}}$ ,  $h^*\mathcal{F}$  is coherent.

*Proof.* Recall that there exists a surjection  $\mathcal{O}(n)^{\oplus m} \to \mathcal{F}$  for some integers m, n. It thus suffices to show that  $h^*\mathcal{O}(n)$  is coherent. Since coherence is a local property, it is enough to show that the structure sheaf on complex analytic affine n-space is coherent (as a module over itself). This follows from the fact that each local ring of this space is *noetherian*.

I won't give a complete proof of this here, but the basic idea is as follows. Let  $\mathbb{C}\{x_1,\ldots,x_r\}$  be the ring of formal power series which converge in some neighborhood of the origin; this is

the ring we are trying to prove is noetherian. We proceed by induction on r, the case r=0 being trivial. The key to the induction step is the Weierstrass preparation theorem, which implies that any element of  $\mathbb{C}\{x_1,\ldots,x_r\}$  equals a unit times an element of  $\mathbb{C}\{x_1,\ldots,x_{r-1}\}[x_r]$ . Since that ring is noetherian by the induction hypothesis plus the Hilbert basis theorem, we deduce that  $\mathbb{C}\{x_1,\ldots,x_r\}$  is too. For a proof of the Weierstrass preparation theorem, see for example the first few pages of Griffiths and Harris, Principles of Algebraic Geometry.

We also need the following relationship between analytic and algebraic stalks.

**Lemma.** For any  $z \in \tilde{\mathbb{P}}^r_{\mathbb{C}}$ , the morphism  $f: \mathcal{O}_{\mathbb{P}^r_{\mathbb{C}}, z} \to \mathcal{O}_{\tilde{\mathbb{P}}^r_{\mathbb{C}}, z}$  is flat. That is, the morphism  $h: \tilde{\mathbb{P}}^r_{\mathbb{C}} \to \mathbb{P}^r_{\mathbb{C}}$  is flat.

Proof. Let  $t_1, \ldots, t_n$  be local (algebraic) coordinates at z. Then we have a completion morphism  $g: \mathcal{O}_{\tilde{\mathbb{P}}_{\mathbb{C}}^r, z} \to \mathbb{C}[\![t_1, \ldots, t_n]\!]$ . Both g and  $g \circ f$  are faithfully flat because they are maps from noetherian local rings into their completions for their maximal ideals. This easily yields flatness of f.

Corollary. The functor  $h^*$  from quasicoherent sheaves on  $\mathbb{P}^r_{\mathbb{C}}$  to quasicoherent sheaves on  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$  is exact.

#### 3 The first GAGA theorem

Note that for any quasicoherent sheaf  $\mathcal{F}$  on  $\mathbb{P}^r_{\mathbb{C}}$ , there is always a natural morphism

$$H^i(\mathbb{P}^r_{\mathbb{C}},\mathcal{F}) \to H^i(\tilde{\mathbb{P}}^r_{\mathbb{C}},h^*\mathcal{F})$$

by pulling back along h. More concretely, you may view an algebraic Čech cocycle as an analytic one.

**Theorem** (GAGA, part 1). For any coherent sheaf  $\mathcal{F}$  on  $\mathbb{P}^r_{\mathbb{C}}$ , the natural morphism

$$H^i(\mathbb{P}^r_{\mathbb{C}},\mathcal{F}) \to H^i(\tilde{\mathbb{P}}^r_{\mathbb{C}},h^*\mathcal{F})$$

is an isomorphism for each i > 0.

In order to prove this, we need a mechanism for computing sheaf cohomology on analytic spaces. Here it is, presented as a black box.

**Theorem** (Cartan). For any nonempty subset J of  $\{0, ..., r\}$  and any coherent sheaf  $\mathcal{F}$  on  $U = \bigcap_{j \in J} \tilde{X}_j$ ,  $H^i(U, \mathcal{F}) = 0$  for i > 0.

The key point is that U is a *Stein manifold*. This also holds if U is the analytification of any affine scheme of finite type over  $\mathbb{C}$  (which I'll leave to you to define). By Leray's theorem, this gives the following corollary.

**Corollary.** For any coherent sheaf  $\mathcal{F}$  on  $\tilde{\mathbb{P}}_{\mathbb{C}}^r$ , we may compute sheaf cohomology using the Čech complex associated to the cover  $\mathfrak{U} = \{X_0, \ldots, X_r\}$ . In particular, the *i*-th cohomology vanishes for i > r.

With this, the proof is parallel to that of Serre's finiteness theorem.

Proof of GAGA (part 1). We first prove the claim for  $\mathcal{F} = \mathcal{O}$  by an explicit Čech cohomology calculation (exercise); note that the computation  $H^0(\tilde{\mathbb{P}}^r_{\mathbb{C}}, \mathcal{O}) = \mathbb{C}$  comes down to the fact that any bounded entire function on  $\mathbb{C}^n$  is constant, which reduces to Liouville's theorem. (By the way, this makes it clear that the theorem is completely false if we replace  $\mathbb{P}^r_{\mathbb{C}}$  with, say, the affine space  $\mathbb{A}^r_{\mathbb{C}}$ . More on this later.)

We next deal with the cases  $\mathcal{F} = \mathcal{O}(n)$  for  $n \in \mathbb{Z}$ , using the exact sequence

$$0 \to \mathcal{O}(n-1) \stackrel{\times x_r}{\to} \mathcal{O}(n) \to \mathcal{O}_H(n) \to 0$$

for  $H \cong \mathbb{P}^{r-1}_{\mathbb{C}}$  the hyperplane  $x_r = 0$ . By induction on r, and comparing long exact sequences in cohomology, we can infer all of the cases from the case n = 0.

Finally, we treat the general case by descending induction on i (as in the proof that Čech cohomology for a good cover computes sheaf cohomology). Build an exact sequence

$$0 \to \mathcal{G} \to \mathcal{E} \to \mathcal{F} \to 0$$

in which  $\mathcal{E}$  is a direct sum of twisting sheaves. Note that applying  $h^*$  is exact, so we get an exact sequence on the analytic side. Then twist and compare long exact sequences in cohomology after twisting:

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

Using the five lemma, we get the desired result.

## 4 The second GAGA theorem

We now know that algebraic coherent sheaves preserve their cohomology under pullback to the analytic side. We next show that they also preserve their morphisms.

**Theorem** (GAGA, part 2). Let  $\mathcal{F}, \mathcal{G}$  be coherent sheaves on  $\mathbb{P}^r_{\mathbb{C}}$ . Then the natural map

$$\operatorname{Hom}_{\mathcal{O}_{\mathbb{P}^r_{\mathbb{C}}}}(\mathcal{F},\mathcal{G}) \to \operatorname{Hom}_{\mathcal{O}_{\mathbb{P}^r_{\mathbb{C}}}}(h^*\mathcal{F},h^*\mathcal{G})$$

is an isomorphism.

*Proof.* In general, for sheaves of  $\mathcal{O}_X$ -modules  $\mathcal{F}$  and  $\mathcal{G}$ , let  $\mathscr{H}om(\mathcal{F},\mathcal{G})$  be the presheaf

$$\mathscr{H}om(\mathcal{F},\mathcal{G})(U) = \operatorname{Hom}_{O_U}(\mathcal{F}|_U,\mathcal{G}_U).$$

This is in fact a sheaf, called the *sheaf Hom* from  $\mathcal{F}$  to  $\mathcal{G}$ . Its global sections are just  $\operatorname{Hom}_{\mathcal{O}_X}(\mathcal{F},\mathcal{G})$ . (I should really write  $\mathscr{H}om_{\mathcal{O}_X}(\mathcal{F},\mathcal{G})$  with the subscript  $\mathcal{O}_X$ , but never mind for now.)

Note that there is a natural map

$$h^* \mathcal{H} om(\mathcal{F}, \mathcal{G}) \to \mathcal{H} om(h^* \mathcal{F}, h^* \mathcal{G})$$

of sheaves on  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$ , given by viewing an algebraic morphism over a Zariski open subset of  $\mathbb{P}^r_{\mathbb{C}}$  as an analytic morphism over the corresponding subset of  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$ . We claim this map is an isomorphism; this will imply the theorem by taking global sections of this isomorphism, then applying the first GAGA theorem.

We check the isomorphism on stalks. Using coherence, we have for each  $z \in \tilde{\mathbb{P}}^r_{\mathbb{C}}$  a natural identification

$$\mathcal{H}om(\mathcal{F},\mathcal{G})_z = \operatorname{Hom}(\mathcal{F}_z,\mathcal{G}_z)$$

and similarly on the analytic side. Put

$$R = \mathcal{O}_{\mathbb{P}^r_{\mathbb{C}}, z}, \qquad \tilde{R} = \mathcal{O}_{\tilde{\mathbb{P}}^r_{\mathbb{C}}, z};$$

a lemma from earlier states that  $\tilde{R}$  is flat over R. By that flatness plus the lemma below (and the fact that R is noetherian), we have a natural identification

$$\operatorname{Hom}(\mathcal{F}_z, \mathcal{G}_z) \otimes_R \tilde{R} = \operatorname{Hom}(\mathcal{F}_z \otimes_R \tilde{R}, \mathcal{G}_z \otimes_R \tilde{R}).$$

This yields the claim.

**Lemma.** Let R be a noetherian ring. Let S be a flat R-algebra. Then for any R-modules M, N, the natural map

$$\operatorname{Hom}_R(M,N) \otimes_R S \to \operatorname{Hom}_S(M \otimes_R S, N \otimes_R S)$$

is a bijection.

*Proof.* Since R is noetherian, I can find an exact sequence

$$F_1 \to F_0 \to M \to 0$$

where  $F_0, F_1$  are finite free R-modules. Then we get a diagram

$$0 \longrightarrow \operatorname{Hom}_{R}(F_{1}, N) \otimes_{R} S \longrightarrow \operatorname{Hom}_{R}(F_{0}, N) \otimes_{R} S \longrightarrow \operatorname{Hom}_{R}(M, N) \otimes_{R} S$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$0 \longrightarrow \operatorname{Hom}_{S}(F_{1} \otimes_{R} S, N \otimes_{R} S) \longrightarrow \operatorname{Hom}_{S}(F_{0} \otimes_{R} S, N \otimes_{R} S) \longrightarrow \operatorname{Hom}_{S}(M \otimes_{R} S, N \otimes_{R} S)$$

with exact rows (the exactness in the first row requiring the flatness of S over R). Since the second and third vertical arrows are isomorphisms, so is the first by the five lemma.

#### 5 The third GAGA theorem

We next try to classify the coherent sheaves on the analytic projective space. We need one more black box.

**Theorem** (Cartan, Serre). For  $\mathcal{F}$  a coherent sheaf on  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$ , the spaces  $H^i(\tilde{\mathbb{P}}^r_{\mathbb{C}}, \mathcal{F})$  are finite dimensional over  $\mathbb{C}$  for all  $i \geq 0$ .

Sketch of proof. Equip the Čech cocycles for the usual open cover with the topology of uniform convergence on compact subsets. Then restrict to a cover in which each  $\tilde{X}_i$  is replaced by an open subset with closure inside  $\tilde{X}_i$ . Using this, one sees that for the induced topology on  $H^i(\tilde{\mathbb{P}}^r_{\mathbb{C}}, \mathcal{F})$ , the identity map is *compact*, which is only possible if this vector space is finite dimensional over  $\mathbb{C}$ .

**Theorem** (GAGA, part 3). Every coherent sheaf on  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$  is the pullback under h of a unique coherent sheaf on  $\mathbb{P}^r_{\mathbb{C}}$ .

The uniqueness follows from the second GAGA theorem. To prove existence, we induct on r, the case r=0 being trivial. For  $\mathcal{F}$  a coherent sheaf on  $\widetilde{\mathbb{P}}^r_{\mathbb{C}}$ , we extend the twisting notation from the algebraic case by writing

$$\mathcal{F}(n) = \mathcal{F} \otimes h^* \mathcal{O}(n).$$

**Lemma.** Assume the third GAGA theorem in dimensions up to r-1. For any coherent sheaf  $\mathcal{F}$  on  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$  and any  $z \in \tilde{\mathbb{P}}^r_{\mathbb{C}}$ , there exists an integer  $n_0$  (depending on  $\mathcal{F}$  and z) such that for  $n \geq n_0$ ,  $\mathcal{F}(n)_z$  is generated by global sections of  $\mathcal{F}(n)$ .

*Proof.* Choose  $x_r \in H^0(\mathbb{P}^r_{\mathbb{C}}, \mathcal{O}(1))$  vanishing at z, and let E be the hyperplane  $x_r = 0$ . We then have the usual exact sequence

$$0 \to \mathcal{O}(-1) \stackrel{\times x_r}{\to} \mathcal{O} \to \mathcal{O}_E \to 0$$

of algebraic coherent sheaves. Tensoring with  $\mathcal{F}$ , we have an exact sequence

$$\mathcal{F}(-1) \to \mathcal{F} \to \mathcal{F}_E \to 0$$

where  $\mathcal{F}_E$  denotes the pushforward of the restriction to E. Let  $\mathcal{G}$  be the kernel on the left side. Twisting, we get

$$0 \to \mathcal{G}(n) \to \mathcal{F}(n-1) \to \mathcal{F}(n) \to \mathcal{F}_E(n) \to 0.$$

Split this into short exact sequences:

$$0 \to \mathcal{G}(n) \to \mathcal{F}(n-1) \to \mathcal{H} \to 0$$
$$0 \to \mathcal{H} \to \mathcal{F}(n) \to \mathcal{F}_E(n) \to 0$$

and then take long exact sequences in cohomology:

$$H^{1}(\tilde{\mathbb{P}}_{\mathbb{C}}^{r}, \mathcal{F}(n-1)) \to H^{1}(\tilde{\mathbb{P}}_{\mathbb{C}}^{r}, \mathcal{H}) \to H^{2}(\tilde{\mathbb{P}}_{\mathbb{C}}^{r}, \mathcal{G}(n))$$
$$H^{1}(\tilde{\mathbb{P}}_{\mathbb{C}}^{r}, \mathcal{H}) \to H^{1}(\tilde{\mathbb{P}}_{\mathbb{C}}^{r}, \mathcal{F}(n)) \to H^{1}(\tilde{\mathbb{P}}_{\mathbb{C}}^{r}, \mathcal{F}_{E}(n)).$$

Note that  $\mathcal{G}$  and  $\mathcal{F}_E$  are supported on E, so by the induction hypothesis, they both come from algebraic coherent sheaves. It follows that for n large enough, the terms  $H^2(\tilde{\mathbb{P}}^r_{\mathbb{C}}, \mathcal{G}(n))$  and  $H^1(\tilde{\mathbb{P}}^r_{\mathbb{C}}, \mathcal{F}_E(n))$  both vanish. We thus obtain inequalities

$$\dim_{\mathbb{C}} H^{1}(\tilde{\mathbb{P}}_{\mathbb{C}}^{r}, \mathcal{F}(n-1)) \geq \dim_{\mathbb{C}} H^{1}(\tilde{\mathbb{P}}_{\mathbb{C}}^{r}, \mathcal{H}) \geq \dim_{\mathbb{C}} H^{1}(\tilde{\mathbb{P}}_{\mathbb{C}}^{r}, \mathcal{F}(n))$$

for n large. By the previous Cartan theorem, the terms of the sequence  $\dim_{\mathbb{C}} H^1(\tilde{\mathbb{P}}^r_{\mathbb{C}}, \mathcal{F}(n))$  are all finite; we just showed that they are nonincreasing for n large enough. They thus eventually reach a *constant value* for n large enough!

In particular, for n large, the previous inequalities all become equalities. Backing up the second of the two long exact sequences, we see that

$$H^0(\tilde{\mathbb{P}}^r_{\mathbb{C}}, \mathcal{F}(n)) \to H^0(\tilde{\mathbb{P}}^r_{\mathbb{C}}, \mathcal{F}_E(n))$$

must be surjective for n large.

Again since  $\mathcal{F}_E$  is known to be algebraic, for n large,  $H^0(\tilde{\mathbb{P}}_{\mathbb{C}}^r, \mathcal{F}_E(n))$  generates  $(\mathcal{F}_E)_z$ . By a quick Nakayama's lemma argument, for such n,  $H^0(\tilde{\mathbb{P}}_{\mathbb{C}}^r, \mathcal{F}(n))$  also generates  $\mathcal{F}(n)_z$ .

**Corollary.** Assume the third GAGA theorem in dimensions up to r-1. For any coherent sheaf  $\mathcal{F}$  on  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$ , there exists an integer  $n_0$  (depending only on  $\mathcal{F}$ ) such that for any  $n \geq n_0$  and any  $z \in \tilde{\mathbb{P}}^r_{\mathbb{C}}$ ,  $\mathcal{F}(n)_z$  is generated by global sections of  $\mathcal{F}(n)$ .

Proof. For a single n, if the claim holds for a single z, it holds in a neighborhood of that z; moreover, by multiplying these sections by monomials in  $x_0, \ldots, x_r$ , we infer the claim for all larger n in the same neighborhood. Since  $\tilde{\mathbb{P}}_{\mathbb{C}}^r$  is compact, we may find a single  $n_0$  such that  $\mathcal{F}(n)_z$  is generated by global sections of  $\mathcal{F}(n)$  for each  $z \in \tilde{\mathbb{P}}_{\mathbb{C}}^r$  and each  $n \geq n_0$ .

Proof of the theorem. Let  $\mathcal{F}$  be a coherent sheaf on  $\tilde{\mathbb{P}}_{\mathbb{C}}^r$ . By the previous corollary, for some n, each stalk of  $\mathcal{F}(n)$  is generated by the space of sections  $H^0(\tilde{\mathbb{P}}_{\mathbb{C}}^r, \mathcal{F}(n))$ , which by Cartan's theorem is finite dimensional over  $\mathbb{C}$ . We thus obtain a surjection  $h^*\mathcal{O}(-n)^{\oplus m} \to \mathcal{F}$  for some m, n. Applying the same argument to the kernel of this map (which is again coherent), we get an exact sequence

$$\mathcal{F}_1 \to \mathcal{F}_2 \to \mathcal{F} \to 0$$

in which each  $\mathcal{F}_i$  is a direct sum of pullbacks of twisting sheaves. In particular, the  $\mathcal{F}_i$  are algebraic; by the second GAGA theorem, the morphism between them is also algebraic. We may then form the algebraic cokernel, whose analytification is isomorphic to  $\mathcal{F}$ , as desired.

## 6 More analytification

One can state the GAGA theorems more generally, but first we need to discuss analytification of spaces other than projective space. We first specify the target category: a locally ringed space  $(X, \mathcal{O}_X)$  is a *complex analytic space* if each point x admits a neighborhood U and an immersion  $\phi: U \to \mathbb{C}^n$  for some n. This is not the same as a *complex manifold* because we allow singularities, and for that matter nonreducedness (so these shouldn't be called *complex analytic varieties* either). Let AnSp denote the category of complex analytic spaces.

We would like a process for turning schemes locally of finite type over  $\mathbb{C}$  into complex analytic spaces in a natural way. It is easy to say what we want to have happen in local coordinates: if  $X = \operatorname{Spec} \mathbb{C}[z_1, \ldots, z_n]/(f_1, \ldots, f_m)$ , we want to take the subspace Z of  $\mathbb{C}^n$  on which  $f_1 = \cdots = f_m = 0$ , equipped with the quotient of  $\mathcal{O}_{\mathbb{C}^n}$  by the coherent ideal sheaf generated by  $f_1, \ldots, f_m$  (or rather, its inverse image on Z).

However, if one works this way, one has to check independence from coordinates. This is doable but annoying (it's like Hartshorne's Proposition II.2.14 comparing certain schemes to varieties). There is a more functorial description of analytification introduced by Grothendieck; see SGA I, exposé XII, Théorème-Définition 1.1.

**Theorem.** Let X be a scheme locally of finite type over  $\mathbb{C}$ . The functor

$$Y \mapsto \operatorname{Hom}_{\operatorname{LocRingSp}}(Y, X)$$

from  $\underline{\operatorname{AnSp}}$  to  $\underline{\operatorname{Set}}$  is represented by an analytic space  $X^{\operatorname{an}}$ ; that is, there are natural isomorphisms

$$\operatorname{Hom}_{\operatorname{LocRingSp}}(Y,X) \to \operatorname{Hom}_{\operatorname{AnSp}}(Y,X^{\operatorname{an}}).$$

Moreover,  $X^{\mathrm{an}}$  has underlying set  $X(\mathbb{C})$ , and the morphism  $X^{\mathrm{an}} \to X$  induces isomorphisms of completed local rings, and so is flat.

You could interpret this as saying that the inclusion functor from analytic spaces to locally ringed spaces has a "partial right adjoint".

Sketch of proof. One first shows that the class of schemes for which the theorem holds is closed under forming open subschemes, closed subschemes, and products, by mirroring these constructions on the analytic side. It then suffices to check the theorem for  $X = \mathbb{A}^1_{\mathbb{C}}$ ; this amounts to observing that giving a map  $Y \to X$  is the same (by the adjunction property of affine schemes) as specifying a map  $\mathbb{C}[t] \to \Gamma(Y, \mathcal{O}_Y)$ , which in turn is the same as specifying the image of t. That is,  $\operatorname{Hom}(Y,X)$  is naturally isomorphic to  $\Gamma(Y,\mathcal{O}_Y)$ . On the other hand, if we view  $\mathbb{C}$  as an analytic space in the obvious fashion, then we may again identify  $\operatorname{Hom}(Y,\mathbb{C})$  naturally with holomorphic functions on Y, i.e., with  $\Gamma(Y,\mathcal{O}_Y)$ . This proves the claim for affine space.

This paradigm extends to other categories derived from schemes. For instance, for k an algebraically closed field, separated reduced schemes of finite type over k admit "varietifications", thus reproducing the class of abstract algebraic varieties and giving a stronger version of Hartshorne Proposition II.2.14.

## 7 Extension to projective and proper schemes

In terms of the analytification functor, we can now extend the GAGA theorems as follows.

**Theorem** (GAGA for projective schemes). Let X be a closed subscheme of  $\mathbb{P}^r_{\mathbb{C}}$  for some  $r \geq 1$ . Let  $h: X^{\mathrm{an}} \to X$  be the analytification morphism.

(a) For any coherent sheaf  $\mathcal{F}$  on X, the natural morphism

$$H^i(X,\mathcal{F}) \to H^i(X^{\mathrm{an}},h^*\mathcal{F})$$

is an isomorphism.

(b) For any coherent sheaves  $\mathcal{F}, \mathcal{G}$  on X, the natural morphism

$$\operatorname{Hom}_{\mathcal{O}_{Y}}(\mathcal{F},\mathcal{G}) \to \operatorname{Hom}_{\mathcal{O}_{Yan}}(h^{*}\mathcal{F},h^{*}\mathcal{G})$$

is an isomorphism.

(c) Every coherent sheaf on  $X^{\mathrm{an}}$  is isomorphic to  $h^*\mathcal{F}$  for a unique coherent sheaf  $\mathcal{F}$  on X.

We saw earlier that already (a) is totally false for  $X = \mathbb{A}^r_{\mathbb{C}}$ , so some sort of completeness is necessary. Grothendieck noticed that it suffices to assume X is *proper* over  $\mathbb{C}$ ; this reduces to the projective case using Chow's lemma (exercise).

## 8 Applications

The GAGA theorem has applications too numerous to count, so I'll just mention a few (see SGA 1, exposé XII for more). The following was proved before GAGA by Chow, but is an immediate corollary.

Corollary (Chow). Any closed analytic subvariety of  $\tilde{\mathbb{P}}^r_{\mathbb{C}}$  is the analytification of a closed algebraic subvariety.

Another application is the following.

**Theorem.** Let X be a smooth proper scheme over  $\mathbb{C}$ . Then

$$H^p(X, \Omega^q_{X/\mathbb{C}}) = H^p(X^{\mathrm{an}}, \Omega^q_{X^{\mathrm{an}}}) \qquad (p, q \ge 0).$$

This can be used to show that the hypercohomology of the algebraic de Rham complex  $\Omega_{X/\mathbb{C}}$  coincides with the hypercohomology of the analytic de Rham complex. (If  $F: \mathcal{C}_1 \to \mathcal{C}_2$  is a left exact additive functor of abelian categories with  $\mathcal{C}_1$  having enough injectives, the hypercohomology of a complex C is defined by forming a quasi-isomorphism  $C \to I$  with the I all injective, and taking  $h^i(F(I))$ . More on this construction a bit later.) This in turn can be combined with some more results on the analytic/topological side (the Dolbeault and de Rham theorems, respectively) to show that algebraic de Rham cohomology computes the usual topological Betti numbers of a smooth variety over  $\mathbb{C}$ .

Here is another application by Grothendieck. See SGA 1, exposé XII again.

**Theorem** (Grothendieck). Let X be a smooth proper scheme over  $\mathbb{C}$ . Then any finite covering space map  $Y \to X^{\mathrm{an}}$  (of topological spaces) corresponds to a finite étale cover of X in the category of schemes.

One can define the étale fundamental group of a scheme X as, roughly speaking, the automorphism group of a maximal inverse system of connected finite étale covers of X. For instance, if  $X = \operatorname{Spec} F$  with F a field, this gives the absolute Galois group of F. (To make this more precise, one must fix a choice of a basepoint just as in the topological case.) The previous theorem implies that for a smooth proper scheme over  $\mathbb{C}$ , the étale fundamental group is the profinite completion of the usual topological fundamental group, i.e., the inverse limit of its finite quotients. For instance, for an elliptic curve, the topological fundamental group is  $\mathbb{Z} \times \mathbb{Z}$ , while the profinite completion is

$$\widehat{\mathbb{Z}} \times \widehat{\mathbb{Z}} \cong \prod_{p} (\mathbb{Z}_p \times \mathbb{Z}_p),$$

where  $\mathbb{Z}_p$  denotes the *p*-adic integers.

**Corollary.** Let K be a number field and let X be a smooth proper scheme over K. Then the profinite completion of the fundamental group of  $(X \times_K \mathbb{C})^{an}$  does not depend on the choice of the embedding  $K \hookrightarrow \mathbb{C}$ .

This might not be so surprising until I tell you that Serre exhibited examples in which the topological fundamental group *does* depend on the choice of the embedding! (Serre's example is a rather artificial construction using elliptic curves with complex multiplications. There are some more natural examples due to one of our postdocs, Junecue Suh.)

The following is an example of a rather large class of results from SGA 1. See the exercises for an example involving properness.

**Theorem.** Let  $f: X \to Y$  be a morphism of schemes locally of finite type over  $\mathbb{C}$ . Then f is separated if and only if  $f^{\mathrm{an}}: X^{\mathrm{an}} \to Y^{\mathrm{an}}$  is separated. In particular, X is separated if and only if  $X^{\mathrm{an}}$  is Hausdorff.

## 9 Analogues

I know of at least two analogues of GAGA, though there may be more.

- One is *formal GAGA*, in which one passes from a scheme to its formal completion along a closed subscheme.
- The other is rigid GAGA, which is like ordinary GAGA except that one works over a complete nonarchimedean field, and uses Tate's notion of rigid analytic geometry (or Berkovich's notion of nonarchimedean analytic geometry instead of complex analytic geometry.

| • I suppose there is also an instance of GAGA for passing from of finite type over an algebraically closed field to abstract one is neither surprising nor useful. | - |
|--------------------------------------------------------------------------------------------------------------------------------------------------------------------|---|
|                                                                                                                                                                    |   |
|                                                                                                                                                                    |   |

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Serre duality for projective space

## 1 Ext groups

For R a ring and  $M, N \in \underline{\mathrm{Mod}}_R$ , I defined  $\mathrm{Ext}^i(M, N)$  as the image of N under the i-th right derived functor of  $\mathrm{Hom}_R(M, \cdot)$ . This makes sense because  $\mathrm{Hom}_R(M, \cdot)$  is a left exact covariant functor from  $\underline{\mathrm{Mod}}_R$  to  $\underline{\mathrm{Ab}}$  (it actually goes to  $\underline{\mathrm{Mod}}_R$  but never mind that). I also remarked that it can be viewed as the image of M under the i-th right derived functor of  $\mathrm{Hom}_R(\cdot, N)$ , provided we view this as a functor on  $\underline{\mathrm{Mod}}_R^{\mathrm{op}}$ .

For the category  $\underline{\mathrm{Mod}}_X$  of sheaves of  $\mathcal{O}_X$ -modules on a ringed space X, we can imitate the first construction pretty directly, except that we have to choose between the normal Hom and the sheaf Hom. Let  $\mathrm{Ext}^i(\mathcal{F},\cdot)$  be the right derived functors of  $\mathrm{Hom}(\mathcal{F},\cdot)$ , and let  $\mathscr{E}xt^i(\mathcal{F},\cdot)$  be the right derived functors of  $\mathscr{H}om(\mathcal{F},\cdot)$ .

For example, there is a natural isomorphism

$$\operatorname{Ext}^{i}(\mathcal{O}_{X},\mathcal{F})\cong H^{i}(X,\mathcal{F})$$

because these are derived functors of the naturally isomorphic functors  $\operatorname{Hom}(\mathcal{O}_X, \mathcal{F}) \cong H^0(X, \mathcal{F})$ . On the other hand,  $\mathscr{H}om(\mathcal{O}_X, \mathcal{F})$  is the identity functor, so

$$\mathscr{E}xt^0(\mathcal{O}_X,\mathcal{F})\cong\mathcal{F},\qquad \mathscr{E}xt^i(\mathcal{O}_X,\mathcal{F})=0\quad (i>0).$$

**Lemma.** Let  $\mathcal{I}$  be an injective  $\mathcal{O}_X$ -module. Then for any open subset U of X,  $\mathcal{I}|_U$  is an injective  $\mathcal{O}_U$ -module.

Proof. Let  $j: U \to X$  be the inclusion. We must show that given a monomorphism  $\mathcal{F} \to \mathcal{G}$ , any map  $\mathcal{F} \to \mathcal{I}|_U$  extends to  $\mathcal{G}$ . Let  $j_*$  denote extension by zero, so that  $j_*\mathcal{F}$  has the same stalks as  $\mathcal{F}$  over U and zero stalks elsewhere. (Sections are the same as  $\mathcal{F}$  over opens contained in U and zero elsewhere.) By looking at stalks,  $j_*\mathcal{F} \to j_*\mathcal{G}$  is still a monomorphism. Moreover, we have a map  $j_*\mathcal{I}|_U \to \mathcal{I}$  by adjunction, and the resulting composition  $j_*\mathcal{F} \to j_*\mathcal{I}|_U \to \mathcal{I}$  extends to  $j_*\mathcal{G} \to \mathcal{I}$ . Restricting back to U gives the desired map  $\mathcal{G} \to \mathcal{I}|_U$ .

Corollary. For any open subset U of X, there are natural isomorphisms

$$\mathscr{E}xt^{i}(\mathcal{F},\mathcal{G})|_{U}\cong \mathscr{E}xt^{i}(\mathcal{F}|_{U},\mathcal{G}|_{U}).$$

In particular, the right side is a sheaf; e.g.,  $\mathcal{E}xt^i(\mathcal{F},\mathcal{G}) = 0$  for i > 0 whenever  $\mathcal{F}$  is locally free of finite rank.

*Proof.* Both sides are cohomological functors in  $\mathcal{G}$  whose higher terms vanish on injectives (by the previous lemma in the case of the right side), hence are effaceable and thus universal.  $\square$ 

Corollary. For  $\mathcal{I}$  an injective  $\mathcal{O}_X$ -module, the functors

$$\operatorname{Hom}(\cdot, \mathcal{I}), \quad \mathscr{H}om(\cdot, \mathcal{I})$$

are exact.

*Proof.* This is true for Hom by the definition of injectivity. For  $\mathscr{H}om$ , use the lemma.  $\square$ 

**Proposition.** For  $\mathcal{F}$  an  $\mathcal{O}_X$ -module,  $\operatorname{Ext}^i(\cdot,\mathcal{F})$  and  $\operatorname{\mathscr{E}\!\mathit{xt}}^i(\cdot,\mathcal{F})$  are cohomological functors on  $\operatorname{\underline{Mod}}^{\operatorname{op}}_X$ .

*Proof.* Let  $\mathcal{I}$  be an injective resolution of  $\mathcal{F}$ . Given a short exact sequence

$$0 \to \mathcal{E} \to \mathcal{G} \to \mathcal{H} \to 0$$

in  $\underline{\mathrm{Mod}}_X$ , we obtain the long exact sequence by taking Hom or  $\mathscr{H}\!om$  into  $\mathcal{T}$ , yielding a short exact sequence of complexes (by the previous corollary), and then taking the long exact sequence of cohomology groups. One does need to check independence from the choice of the resolution, but this is similar to other arguments we've done before, so I won't bore you with it. (The summary: by a pushout construction, it suffices to compare  $\mathcal{T}$  and  $\mathcal{T}$  when there is a quasi-isomorphism  $\mathcal{T} \to \mathcal{T}$ . You then get a morphisms of short exact sequences which is a quasi-isomorphism on each term, etc.)

Unfortunately, we can't check that  $\operatorname{Ext}^{i}(\cdot, \mathcal{F})$  and  $\operatorname{\mathcal{E}\!\mathit{xt}}^{i}(\cdot, \mathcal{F})$  are effaceable, or construct them as derived functors, because  $\operatorname{\underline{Mod}}_{X}$  need not have enough *projectives* (exercise). However, we can still use certain "acyclic resolutions" to compute.

**Proposition.** Suppose that

$$\cdots \to \mathcal{L}_1 \to \mathcal{L}_0 \to \mathcal{F} \to 0$$

is an exact sequence in  $\underline{\mathrm{Mod}}_X$ , where each  $\mathcal{L}_i$  is locally free of finite rank. (We say the  $\mathcal{L}$ . form a locally free resolution of  $\mathcal{F}$ .) Then there is a isomorphism

$$\operatorname{Ext}^i(\mathcal{F},\mathcal{G}) \cong h^i(\operatorname{Hom}(\mathcal{L}_\cdot,\mathcal{G}))$$

which is functorial both in  $\mathcal{G}$  and in the resolution of  $\mathcal{F}$ .

*Proof.* Since  $\mathcal{L}_i$  is locally free of finite rank,  $\mathscr{E}xt^1(\mathcal{I},\cdot)$  always vanishes, so  $\mathscr{H}om(\mathcal{L}_i,\cdot)$  is an exact functor (even though  $\operatorname{Hom}(\mathcal{L}_i|_U,\cdot)$  is not exact on any open U). From this we see that the right side is a cohomological functor: given a short exact sequence  $0 \to \mathcal{G}_1 \to \mathcal{G} \to \mathcal{G}_2 \to 0$ , the sequence

$$0 \to \mathscr{H}\!\mathit{om}(\mathcal{L}_{\cdot},\mathcal{G}_{1}) \to \mathscr{H}\!\mathit{om}(\mathcal{L}_{\cdot},\mathcal{G}) \to \mathscr{H}\!\mathit{om}(\mathcal{L}_{\cdot},\mathcal{G}_{2}) \to 0$$

is again exact, so admits a long exact sequence in cohomology.

We now have that both sides of the desired isomorphism are cohomological functors in  $\mathcal{G}$  whose higher terms vanish on injectives, so are effaceable. Hence they are both universal.  $\square$ 

Note that locally free resolutions are much easier to write down in practice than injective resolutions. For instance, if  $X = \mathbb{P}^n_k$  for k a field, and  $\mathcal{F}$  is coherent, then Serre's theorem gives a surjection  $\mathcal{E} \to \mathcal{F}$  where  $\mathcal{E}$  is a direct sum of twisting sheaves. Repeated application gives not just a locally free resolution but a free resolution!

**Proposition.** For any coherent sheaves  $\mathcal{F}, \mathcal{G}$  on  $\mathbb{P}^n_k$  for k a field,  $\mathcal{E}xt^i(\mathcal{F}, \mathcal{G})$  is again coherent.

*Proof.* We just argued that a free resolution  $\mathcal{L}$ . of  $\mathcal{F}$  exists. By the previous proposition, we need only check that the  $h^i(\mathcal{H}om(\mathcal{L},\mathcal{G}))$  are coherent. This is true because the  $\mathcal{L}$ . and  $\mathcal{G}$  are coherent, so the  $\mathcal{H}om(\mathcal{L},\mathcal{G})$  are too.

**Lemma.** For  $\mathcal{F}, \mathcal{G}, \mathcal{L} \in \underline{\mathrm{Mod}}_X$  with  $\mathcal{L}$  locally free of finite rank, there are canonical isomorphisms

$$\operatorname{Ext}^{i}(\mathcal{F} \otimes \mathcal{L}, \mathcal{G}) \cong \operatorname{Ext}^{i}(\mathcal{F}, \mathcal{L}^{\vee} \otimes \mathcal{G})$$

and

$$\mathscr{E}xt^{i}(\mathcal{F}\otimes\mathcal{L},\mathcal{G})\cong\mathscr{E}xt^{i}(\mathcal{F},\mathcal{L}^{\vee}\otimes\mathcal{G})\cong\mathscr{E}xt^{i}(\mathcal{F},\mathcal{G})\otimes\mathcal{L}^{\vee}.$$

*Proof.* Again, check that everything is an effaceable cohomological functor of  $\mathcal{G}$  and that things match at i = 0. (See Hartshorne Proposition III.6.7.)

Final note: you may be wondering what the relationship is between Ext and  $\mathscr{E}xt$ . It comes from the following general fact: if F and G are left exact functors such that  $F \circ G$  makes sense, then there is a spectral sequence relating the derived functors of F, the derived functors of G, and the derived functors of  $F \circ G$ . (See Godement's book for details.) In our case, given a sheaf  $\mathcal{F}$ , take

$$F = H^0(X, \cdot), G = \mathcal{H}om_X(\mathcal{F}, \cdot), F \circ G = \operatorname{Hom}_X(\mathcal{F}, \cdot).$$

## 2 Duality on projective space

For the rest of this lecture, we work over a field k, but it need not be algebraically closed.

**Theorem** (Duality on projective space). Put  $X = \mathbb{P}_k^n$ . Let  $\mathcal{F}$  be a coherent sheaf on X. Recall that  $H^n(X, \mathcal{O}_X(-n-1))$  is one-dimensional over k.

(a) The map

$$\operatorname{Hom}_X(\mathcal{F}, \mathcal{O}_X(-n-1)) \times H^n(X, \mathcal{F}) \to H^n(X, \mathcal{O}_X(-n-1))$$

is a perfect pairing of finite dimensional k-vector spaces (i.e., it identifies each space with the Hom of the other into the target).

(b) For V a k-vector space, put

$$V' = \operatorname{Hom}_k(V, H^n(X, \mathcal{O}_X(-n-1)).$$

For each  $i \geq 0$ , there is a natural isomorphism

$$\operatorname{Ext}^{i}(\mathcal{F}, \mathcal{O}_{X}(-n-1)) \to H^{n-i}(X, \mathcal{F})'$$

which for i = 0 reproduces (a), and which is compatible with short exact sequences.

*Proof.* For (a), we have a natural morphism

$$\operatorname{Hom}(\mathcal{F}, \mathcal{O}_X(-n-1)) \to H^n(X, \mathcal{F})'$$

of left exact covariant functors on  $\underline{\mathrm{Mod}}_X^{\mathrm{op}}$ , which we claim is an isomorphism. In case  $\mathcal{F} = \mathcal{O}_X(m)$ , we want a natural isomorphism

$$H^0(X, \mathcal{O}_X(-m-n-1)) \cong \operatorname{Hom}(H^n(X, \mathcal{O}_X(m)), H^n(X, \mathcal{O}_X(-n-1)))$$

and this is exactly what we got from Serre's calculation. Likewise, we already have the isomorphism when  $\mathcal{F}$  is a direct sum of twisting sheaves.

In general, we can write an exact sequence

$$\mathcal{E}_1 \to \mathcal{E}_0 \to \mathcal{F} \to 0$$

in  $\underline{\mathrm{Mod}}_X$  with  $\mathcal{E}_0$ ,  $\mathcal{E}_1$  both direct sums of twisting sheaves. Since the things we are computing are left exact on  $\underline{\mathrm{Mod}}_X^{\mathrm{op}}$ , this exact sequence turns into a diagram with exact rows:

$$0 \longrightarrow 0 \longrightarrow \operatorname{Hom}(\mathcal{F}, \mathcal{O}_X(-n-1)) \longrightarrow \operatorname{Hom}(\mathcal{E}_0, \mathcal{O}_X(-n-1)) \longrightarrow \operatorname{Hom}(\mathcal{E}_1, \mathcal{O}_X(-n-1))$$

$$\downarrow \qquad \qquad \downarrow \sim \qquad \qquad \downarrow \sim \qquad \qquad \downarrow \sim$$

$$0 \longrightarrow 0 \longrightarrow H^n(X, \mathcal{F})' \longrightarrow H^n(X, \mathcal{E}_0)' \longrightarrow H^n(X, \mathcal{E}_1)'$$

The five lemma gives the desired isomorphism.

For (b), we have two cohomological functors on the category of coherent  $\mathcal{O}_X$ -modules which agree at index 0. We need only check that they are both effaceable. For this, given  $\mathcal{F}$  coherent, we can write it as a quotient of  $\mathcal{E} = \mathcal{O}_X(-q)^{\oplus m}$  for any sufficiently large q. So all we need to do is check that for any given i > 0, both  $\operatorname{Ext}^i(\mathcal{O}_X(-q), \mathcal{O}_X(-n-1))$  and  $H^{n-i}(X, \mathcal{O}_X(-q))$  vanish for q large. The second statement is true by Serre's calculation; so is the first because  $\operatorname{Ext}^i(\mathcal{O}_X(-q), \mathcal{O}_X(-n-1)) \cong H^i(X, \mathcal{O}_X(q-n-1))$ .

## 3 Differentials and duality

This is not really the right way to view the duality theorem, because it does not generalize well. To fix this, we reintroduce the sheaf  $\Omega_{X/k}$  of Kähler differentials on  $X = \mathbb{P}_k^n$ , and its top exterior power  $\omega_X$ , the *canonical sheaf*.

**Lemma.** For  $X = \mathbb{P}_k^n$ , the sheaf  $\omega_X$  is isomorphic to  $\mathcal{O}_X(-n-1)$ .

*Proof.* This can be seen using the exact sequence

$$0 \to \Omega_{X/k} \to \mathcal{O}_X(-1)^{\oplus n+1} \to \mathcal{O}_X \to 0$$

of sheaves on X, where the middle term corresponds to the sheaf  $\bigoplus_{i=0}^{n} S(-1)e_i$ , the right term corresponds to  $S = k[x_0, \ldots, x_n]$ , and the map  $S(-1)^{n+1} \to S$  takes  $e_i$  to  $x_i$  (Hartshorne, Theorem 8.13). This gives exact sequences

$$0 \to \Omega^i_{X/k} \to \wedge^i_k \mathcal{O}_X(-1)^{\oplus n+1} \to \Omega^{i-1}_{X/k} \to 0$$

for all i. For i=n+1, this becomes an isomorphism  $\mathcal{O}_X(-n-1) \to \Omega^n_{X/k}$  because  $\Omega^{n+1}_{X/k} = 0$ . One can also see this more directly by writing down a global generator of  $\omega_X(n+1)$ . For instance, define  $\alpha \in H^0(D_+(x_0 \cdots x_n), \omega_X)$  by the formula

$$\alpha = \frac{x_0^{n+1}}{x_0 \cdots x_n} d(x_1/x_0) \wedge \cdots \wedge d(x_n/x_0)$$

$$= \frac{1}{x_0 \cdots x_n} \sum_{i=0}^{n} (-1)^i x_i dx_0 \wedge \cdots \wedge \widehat{dx_i} \wedge \cdots \wedge dx_n.$$

The first line shows that  $x_0 \cdots x_n \alpha$  generates  $\omega_X(n+1)$  over  $D_+(x_0)$ ; it also shows that performing an automorphism of X which swaps two of  $x_1, \ldots, x_n$  only changes  $\alpha$  by a sign. The second line shows that the same is true of the automorphism of X which swaps  $x_0$  and  $x_n$ . Hence  $x_0 \cdots x_n \alpha$  generates  $\omega_X(n+1)$  over  $D_+(x_i)$  for  $i=1,\ldots,n$ .

Warning: Hartshorne Remark 7.1.1 claims that  $\alpha$ , viewed as a Čech n-cocycle, is invariant under coordinate changes. However, we just contradicted this by showing that  $\alpha$  itself changes sign when you swap two coordinates. What is really happening is that if  $T: \mathbb{P}^n_k \to \mathbb{P}^n_k$  is the linear automorphism defined by the matrix A, in the sense that

$$T^*(x_j) = \sum_{i} A_{ij} x_i$$
  $(i, j = 0, ..., n),$ 

then

$$T^*(x_0\cdots x_n\alpha) = \det(A)x_0\cdots x_n\alpha.$$

In any case, we can use  $\omega_X$  in place of  $\mathcal{O}_X(-n-1)$  in the statement of the duality theorem on projective space. Next time, I'll talk about how this can be generalized to other schemes over k.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Dualizing sheaves and Riemann-Roch (updated 6 May 09)

In this lecture, we introduce dualizing sheaves for projective schemes over a field, then use them to derive the Riemann-Roch theorem for curves. Throughout, let k be a field (not necessarily algebraically closed), let  $j: X \to P = \mathbb{P}^N_k$  be a closed immersion with X of dimension n, and let  $\mathcal{O}_X(1)$  be the corresponding twisting sheaf.

### 1 Dualizing sheaves

For V a k-vector space, let  $V^{\vee}$  denote the dual space  $\operatorname{Hom}_k(V,k)$ . A dualizing sheaf for X is a coherent sheaf  $\omega_X^{\circ}$  equipped with a trace morphism  $t: H^n(X,\omega_X^{\circ}) \to k$ , such that for all coherent sheaves  $\mathcal{F}$  on X, the composition

$$\operatorname{Hom}_X(\mathcal{F},\omega_X^{\circ}) \times H^n(X,\mathcal{F}) \to H^n(X,\omega_X^{\circ}) \xrightarrow{t} k$$

of the natural pairing with the trace morphism induces an isomorphism

$$\operatorname{Hom}_X(\mathcal{F},\omega_X^{\circ}) \cong H^n(X,\mathcal{F})^{\vee}.$$

By interpreting this in terms of representing a certain functor, we see that a dualizing sheaf is unique up to unique isomorphism if it exists.

**Theorem.** There exists a dualizing sheaf for X.

This also holds when X is proper, but I won't give the proof in this course (see the references at the end of Hartshorne III.7).

The previous theorem is not so useful unless one can identify the dualizing sheaf explicitly. This is tricky in general, but can be done well in the smooth case.

**Theorem.** Suppose that X is smooth and irreducible over k. Then the canonical sheaf  $\omega_X$  is a dualizing sheaf.

### 2 Application to Riemann-Roch

Modulo the previous two theorems, we can already deduce Riemann-Roch for curves. Suppose in this section that k is algebraically closed, and that X is smooth over k, irreducible, and of dimension 1.

For any divisor D on X, the identification of the canonical sheaf  $\omega_X \cong \Omega_{X/k}$  with the dualizing sheaf  $\omega_X^{\circ}$  gives us an isomorphism

$$H^0(X, \omega_X \otimes \mathcal{L}(-D)) \cong \operatorname{Hom}_X(\mathcal{L}(D), \omega_X)$$
  
 $\cong \operatorname{Hom}_X(\mathcal{L}(D), \omega_X^{\circ})$   
 $\cong H^1(X, \mathcal{L}(D))^{\vee}.$ 

This tells us several useful things. First, the genus g = g(X), which is typically defined as  $\dim_k H^0(X, \omega_X)$ , is also equal to  $\dim_K H^1(X, \mathcal{O})$ . Second, the desired statement of Riemann-Roch is now

$$\deg(D) + 1 - g \stackrel{?}{=} \dim_k H^0(X, \mathcal{L}(D)) - \dim_k H^0(X, \omega_X \otimes \mathcal{L}(-D))$$
$$= \dim_k H^0(X, \mathcal{L}(D)) - \dim_k H^1(X, \mathcal{L}(D))$$
$$= \chi(X, \mathcal{L}(D)).$$

Third, Riemann-Roch does indeed hold for D = 0 (by the previous two assertions).

To finish the proof, it is enough to show that the Riemann-Roch equality for a given divisor D is equivalent to its truth for the divisor D + (Q) for any closed point  $Q \in X(k)$ . (With that in hand, we can walk from 0 to any other divisor by adding or subtracting points.) So let us see how much both sides of the Riemann-Roch equality change when we add the point Q. On one hand, obviously

$$(\deg(D+(Q))+1-g)-(\deg(D)+1-g)=1.$$

On the other hand, we have a short exact sequence

$$0 \to \mathcal{L}(D) \to \mathcal{L}(D + (Q)) \to \mathcal{O}_Q \to 0$$

where  $\mathcal{O}_Q$  denotes the skyscraper sheaf k at the point Q. Since Euler characteristics add in short exact sequences,

$$\chi(X, \mathcal{L}(D+(Q))) - \chi(X, \mathcal{L}(D)) = \chi(X, \mathcal{O}_Q) = 1.$$

Hence Riemann-Roch for D is equivalent to Riemann-Roch for D + (Q).

## 3 Construction of the dualizing sheaf

We now go back and construct dualizing sheaves following the argument in Hartshorne (but fleshing out some details which he leaves opaque). Recall that we already know the duality theorem for X = P, with the dualizing sheaf being the canonical sheaf  $\omega_P$ . The plan is to manufacture a dualizing sheaf on X out of  $\omega_P$ , using Serre duality for P. That tells us that if we fix an isomorphism  $H^N(P, \omega_P) \cong k$  of k-vector spaces, then for any coherent sheaf  $\mathcal{F}$  on X,

$$H^n(X, \mathcal{F}) = H^n(P, j_*\mathcal{F}) \cong \operatorname{Ext}_P^{N-n}(j_*\mathcal{F}, \omega_P)^{\vee}.$$

So we are reduced to finding a sheaf  $\omega_X^{\circ}$  on X for which there is a functorial isomorphism

$$\operatorname{Hom}_X(\mathcal{F},\omega_X^{\circ}) \cong \operatorname{Ext}_P^{N-n}(j_*\mathcal{F},\omega_P).$$

(We then get the required trace map  $H^n(X,\omega_X^\circ) \to k$  by tracing the identity element of  $\operatorname{Hom}_X(\omega_X^\circ,\omega_X^\circ)$  through the identifications.)

One might imagine that this isomorphism comes from an isomorphism of sheaves

$$\mathscr{H}om_X(\mathcal{F},\omega_X^{\circ})\stackrel{?}{\cong}\mathscr{E}xt_P^{N-n}(j_*\mathcal{F},\omega_P)$$

by taking global sections. Taking  $\mathcal{F} = \mathcal{O}_X$  in this hypothetical isomorphism suggests the right definition:

$$\omega_X^{\circ} = j^* \mathscr{E}xt_P^{N-n}(j_*\mathcal{O}_X, \omega_P).$$

We would like to get back from this to the claimed isomorphism

$$\operatorname{Hom}_X(\mathcal{F}, \omega_X^{\circ}) \cong \operatorname{Ext}_P^{N-n}(j_*\mathcal{F}, \omega_P).$$

by first forming the canonical identification

$$\mathscr{H}om_X(\mathcal{F}, j^*\mathscr{H}om_P(j_*\mathcal{O}_X, \cdot)) \cong \mathscr{H}om_P(j_*\mathcal{F}, \cdot)$$

(local version: for A a ring, I an ideal,  $M \in \operatorname{\underline{Mod}}_{A/I}$ ,  $N \in \operatorname{\underline{Mod}}_A$ , we identify  $\operatorname{Hom}_A(M,N) \cong \operatorname{Hom}_{A/I}(M,\operatorname{Hom}_A(A/I,N))$ ), then evaluating the resulting derived functors at  $\omega_P$ , then taking global sections. This is complicated by the fact that in the second step,  $\mathscr{H}om_X(\mathcal{F},\cdot)$  is not exact, and in the third step, taking global sections is not exact.

To straighten these things out, we need to know more about the relationship between the sheaf  $\mathcal{E}xt$  and the global Ext. For starters, here is one thing I can say using Serre vanishing. (See Hartshorne Proposition III.6.9.)

**Proposition.** Let  $\mathcal{F}$  and  $\mathcal{G}$  be coherent sheaves on X. Then there exists an integer  $q_0$  depending on  $\mathcal{F}$  and  $\mathcal{G}$ , such that for every  $q \geq q_0$ , we have

$$\operatorname{Ext}_X^i(\mathcal{F},\mathcal{G}(q)) \cong \Gamma(X,\mathscr{E}xt_X^i(\mathcal{F},\mathcal{G})(q)).$$

*Proof.* This holds for i=0 without any restriction on q. For  $\mathcal{F}$  locally free, the right side is zero for i>0, whereas the left side vanishes for n large enough by Serre's vanishing theorem. The general case then follows by a dimension shifting argument; see Hartshorne Proposition III.6.9.

Next, I must recall a theorem which I skipped over earlier.

**Theorem** (Grothendieck). For any  $\mathcal{F} \in \underline{\operatorname{Sh}}_{\operatorname{Ab}}(X)$ ,  $H^i(X, \mathcal{F}) = 0$  for i > n.

*Proof.* This holds with X replaced by any noetherian topological space of dimension n. The argument is a rather elaborate dimension-shifting argument; see Hartshorne Theorem III.2.7. (See also Hartshorne exercise III.4.8(d), which is enough for this discussion.)

Corollary. For any coherent sheaf  $\mathcal{F}$  on X, we have  $\mathscr{E}xt_P^i(j_*\mathcal{F},\omega_P) = 0$  for i < N - n.

*Proof.* Put  $\mathcal{F}_i = \mathcal{E}xt_P^i(j_*\mathcal{F}, \omega_P)$ . On one hand, for q large,

$$\Gamma(P, \mathcal{F}_i(q)) = \operatorname{Ext}_P^i(j_*\mathcal{F}, \omega_P(q)) \cong H^{N-i}(P, j_*\mathcal{F}(-q))^{\vee}$$

by Serre duality for P. For i < N - n,  $H^{N-i}(P, j_*\mathcal{F}(-q)) = 0$  by the theorem. Hence  $\Gamma(P, \mathcal{F}_i(q)) = 0$  for q large. On the other hand, since  $\mathcal{F}_i$  is coherent, for q large,  $\mathcal{F}_i(q)$  is generated by global sections. This forces  $\mathcal{F}_i(q) = 0$  for q large, whence  $\mathcal{F}_i = 0$ .

At this point, we can finish with the following argument; compare Hartshorne Lemma III.7.4. (Once again, there is a spectral sequence hiding behind this, but never mind.) Take an injective resolution  $\mathcal{I}$  of  $\omega_P$ , so we can compute  $\mathscr{E}xt^*(j_*\mathcal{F},\omega_P)$  as the cohomology of  $\mathscr{H}om_P(j_*\mathcal{F},\mathcal{I}^*)$ , and similarly for Ext and Hom. But using the canonical identification from earlier, if we write  $\mathcal{J}^{\cdot} = j^*\mathscr{H}om_P(j_*\mathcal{O}_X,\mathcal{I}^{\cdot})$ , we can also compute  $\mathscr{E}xt^{\cdot}(j_*\mathcal{F},\omega_P)$  as the cohomology of  $\mathscr{H}om_X(\mathcal{F},\mathcal{J}^{\cdot})$ , and similarly for Ext and Hom. So now what we need to know is that

$$\mathscr{H}\!om_X(\mathcal{F},\omega_X^\circ)\stackrel{?}{\cong} h^{N-n}(\mathscr{H}\!om_X(\mathcal{F},\mathcal{J}^\cdot))$$

and similarly with straight Homs.

However, the sheaves  $\mathcal{J}$  are injective  $\mathcal{O}_X$ -modules. (Local version: if A is a ring, I an ideal, and  $I \in \underline{\mathrm{Mod}}_A$  is injective, then  $\mathrm{Hom}_A(A/I,M)$  is an injective A/I-module; this uses the previous local identification.) By the previous corollary, the complex  $\mathcal{J}$  (whose cohomology computes  $\mathscr{E}xt^*(j_*\mathcal{O}_X,\omega_P)$ ) is acyclic in degrees up to N-n-1. We can then split it into two complexes of injectives  $\mathcal{J}_1$ ,  $\mathcal{J}_2$ , where  $\mathcal{J}_1$  is exact and only has terms in degrees up to N-n, and  $\mathcal{J}_2$  only has terms in degrees at least N-n (exercise).

Since  $\mathcal{J}_1$  is a bounded complex of injectives, it splits into a series of split short exact sequences; thus it stays exact no matter what left exact functors you apply to it. So we can replace  $\mathcal{J}$  by  $\mathcal{J}_2$  for the purposes of computing derived functors, i.e., what we need to prove is reduced to

$$\mathscr{H}om_X(\mathcal{F},\omega_X^\circ)\stackrel{?}{\cong} h^{N-n}(\mathscr{H}om_X(\mathcal{F},\mathcal{J}_2^\cdot))$$

and similarly for straight Hom. But  $\mathcal{J}_2$  only starts in degree N-n, and Hom and  $\mathscr{H}om$  are left exact, so we have

$$\mathscr{E}xt_P^{N-n}(j_*\mathcal{F},\omega_P) \cong h^{N-n}(\mathscr{H}om_X(\mathcal{F},\mathcal{J}_2))$$

$$\cong \mathscr{H}om_X(\mathcal{F},h^{N-n}(\mathcal{J}_2))$$

$$\cong \mathscr{H}om_X(\mathcal{F},h^{N-n}(\mathscr{H}om_X(\mathcal{O}_X,\mathcal{J}_2)))$$

$$\cong \mathscr{H}om_X(\mathcal{F},\mathscr{E}xt^{N-n}(j_*\mathcal{O}_X,\omega_P))$$

$$\cong \mathscr{H}om_X(\mathcal{F},\omega_X^\circ)$$

and similarly

$$\operatorname{Ext}_{P}^{N-n}(j_*\mathcal{F},\omega_P) \cong h^{N-n}(\operatorname{Hom}_X(\mathcal{F},\mathcal{J}_2)) \cong \operatorname{Hom}_X(\mathcal{F},\omega_X^\circ).$$

That completes the proof that

$$\omega_X^{\circ} = \mathscr{E}xt_P^{N-n}(j_*\mathcal{O}_X, \omega_P)$$

is a dualizing sheaf for X.

### 4 Calculation of the dualizing sheaf for smooth schemes

To finish the proof of Riemann-Roch, we must still show that we can take  $\omega_X^{\circ} = \omega_X$  when X is smooth over k. Fortunately, this is a local problem.

**Theorem.** Suppose that X is a local complete intersection in P. Let  $\mathcal{I}$  be the ideal sheaf of X. Then there is a canonical isomorphism

$$\mathscr{E}xt_P^r(j_*\mathcal{O}_X,\omega_P)\cong\omega_P\otimes j_*\mathcal{O}_X\otimes\wedge^r(\mathcal{I}/\mathcal{I}^2)^\vee.$$

The local complete intersection condition asserts that  $\mathcal{I}$  is locally generated by N-n elements; this is true for X smooth basically by the Jacobian criterion. See Hartshorne Theorem II.8.17. The fact that the right side gives  $\omega_X$  comes from the exact sequence

$$0 \to \mathcal{I}/\mathcal{I}^2 \to \Omega_{P/k} \otimes j_* \mathcal{O}_Y \to j_* \Omega_{Y/k}$$

by taking exterior powers; see Hartshorne Proposition II.8.20. The stated theorem itself is proved by computing in local coordinates; see Hartshorne Theorem III.7.11

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Cohen-Macaulay schemes and Serre duality

In this lecture, we extend Serre duality to Cohen-Macaulay schemes over a field. As in the previous lecture, let k be a field (not necessarily algebraically closed), let  $j: X \to P = \mathbb{P}_k^N$  be a closed immersion with X of dimension n, and let  $\mathcal{O}_X(1)$  be the corresponding twisting sheaf.

## 1 Cohen-Macaulay schemes and duality

Let  $\omega_X^{\circ}$  denote a dualizing sheaf on X; remember that this choice includes a trace map  $H^n(X,\omega_X^{\circ}) \to k$ . We then obtain natural functorial maps

$$\theta^i : \operatorname{Ext}_X^i(\mathcal{F}, \omega_X^{\circ}) \to H^{n-i}(X, \mathcal{F})^{\vee}$$

because both sides are cohomological functors on the opposite category of coherent sheaves on X, and the one on the left is effaceable because it vanishes on direct sums of twisting sheaves. By the definition of a dualizing sheaf,  $\theta^0$  is always an isomorphism.

**Theorem.** The following conditions are equivalent.

- (a) The scheme X is equidimensional (each irreducible component has dimension n) and Cohen-Macaulau.
- (b) The maps  $\theta^i$  are isomorphisms for all  $i \geq 0$  and all coherent sheaves  $\mathcal{F}$  on X.

This is of course meaningless if I don't tell you what a Cohen-Macaulay scheme is. For the moment, suffice to say that a scheme is Cohen-Macaulay if and only if each of its local rings is a Cohen-Macaulay ring. That already has content, because then the theorem says that (b) is equivalent to a local condition on X, which is far from obvious.

I'll also point out that a regular local ring is always Cohen-Macaulay. This implies the following.

**Corollary.** If X is smooth over k, then  $\theta^i$  is an isomorphism for all  $i \geq 0$  and all coherent sheaves  $\mathcal{F}$  on X.

## 2 Proof of the duality theorem, part 1

Even without knowing what a Cohen-Macaulay scheme is, we can at least start working to prove that condition (b) is equivalent to a *local* condition on X. Let us start by relating (b) to two global vanishing assertions.

**Lemma.** The following conditions are equivalent to (b).

- (c) For any locally free coherent sheaf  $\mathcal{F}$  on X, for q sufficiently large, we have  $H^i(X, \mathcal{F}(-q)) = 0$  for all i < n.
- (c') For q sufficiently large, we have  $H^i(X, \mathcal{O}_X(-q)) = 0$  for all i < n.

Note that condition (c) is a sort of opposite to Serre's vanishing theorem, which gives the vanishing of  $H^i(X, \mathcal{F}(q))$  for i > 0 and q sufficiently large.

*Proof.* Given (b), for any locally free coherent sheaf  $\mathcal{F}$  on X, we have

$$H^{i}(X, \mathcal{F}(-q)) = \operatorname{Ext}_{X}^{n-i}(\mathcal{F}(-q), \omega_{X}^{\circ})^{\vee}$$

$$= \operatorname{Ext}_{X}^{n-i}(\mathcal{O}_{X}, \mathcal{F}^{\vee} \otimes \omega_{X}^{\circ}(q))^{\vee}$$

$$= H^{n-i}(X, \mathcal{F}^{\vee} \otimes \omega_{X}^{\circ}(q))^{\vee}$$

and this vanishes for n-i>0 and q large by Serre's vanishing theorem. Thus (b) implies (c).

It is clear that (c) implies (c'). Given (c'), it follows that  $H^{n-i}(X,\cdot)^{\vee}$  is effaceable for all i>0 since we can cover  $\mathcal{F}$  with a direct sum of twisting sheaves. Hence  $\theta^i$  is the natural map between two universal cohomological functors, hence is an isomorphism. Thus (c') implies (b).

We next reformulate this in local terms, using Serre duality on P.

**Lemma.** The following condition is equivalent to (b).

(d) For all 
$$i < n$$
,  $\mathcal{E}xt_P^{N-i}(j_*\mathcal{O}_X, \omega_P) = 0$ .

Remember that no matter what X is, we have  $\mathscr{E}xt_P^{N-i}(j_*\mathcal{O}_X,\omega_P)=0$  for i>n: we proved this in the course of constructing the dualizing sheaf  $\omega_X^{\circ}$ .

*Proof.* By Serre duality on P (and choosing an isomorphism  $H^n(P,\omega_P)\cong k$ ), we may identify

$$H^i(X, \mathcal{O}_X(-q)) \cong H^i(P, j_*\mathcal{O}_X(-q)) \cong \operatorname{Ext}_P^{N-i}(j_*\mathcal{O}_X, \omega_P(q))^{\vee}.$$

So (c) is equivalent to the condition that for q sufficiently large,  $\operatorname{Ext}_P^{N-i}(j_*\mathcal{O}_X, \omega_P(q)) = 0$  for all i < n. Recall from earlier that for q large,

$$\operatorname{Ext}_P^{N-i}(j_*\mathcal{O}_X,\omega_P(q)) = \Gamma(P,\mathscr{E}xt_P^{N-i}(j_*\mathcal{O}_X,\omega_P(q))) = \Gamma(P,\mathscr{E}xt_P^{N-i}(j_*\mathcal{O}_X,\omega_P)(q)).$$

Since  $\mathscr{E}xt_P^{N-i}(j_*\mathcal{O}_X,\omega_P)$  is coherent,  $\Gamma(P,\mathscr{E}xt_P^{N-i}(j_*\mathcal{O}_X,\omega_P)(q))$  vanishes for q sufficiently large if and only if  $\mathscr{E}xt_P^{N-i}(j_*\mathcal{O}_X,\omega_P)=0$ .

Condition (d) can be rewritten as follows.

**Lemma.** The following condition is equivalent to (b).

(e) For each point  $x \in X$ , if  $A = \mathcal{O}_{P,x}$  and I is the ideal of A defining X at x, then for all i < n,  $\operatorname{Ext}_A^{N-i}(A/I, A) = 0$ .

*Proof.* This translates directly from (d) once we remember that  $\omega_P$  is locally free of rank 1 on P.

This is almost the local condition we are seeking, except that it still refers to the position of X within P.

## 3 The Cohen-Macaulay condition

To get rid of the dependence of our duality condition on the relative geometry of X within P, we need some more sophisticated commutative algebra.

**Proposition.** Let A be a regular local ring and let M be a finitely generated A-module. Then for any nonnegative integer n, the following are equivalent.

- (a) We have  $\operatorname{Ext}^{i}(M, A) = 0$  for all i > n.
- (b) For any A-module N, we have  $\operatorname{Ext}^i(M,N)=0$  for all i>n.
- (c) There exists a projective resolution  $0 \to L_n \to \cdots \to L_1 \to L_0 \to M \to 0$  of M at length at most n.

*Proof.* See Hartshorne Proposition III.6.10A (and associated Matsumura reference) and exercise III.6.6.  $\Box$ 

The smallest integer for which this holds is called the *projective dimension* of M (if it exists), denoted  $pd_A(M)$ . For instance, M is projective if and only if  $pd_A(M) = 0$ .

For M a module over a ring A, a regular sequence is a sequence  $x_1, \ldots, x_n$  of elements of A such that for  $i = 1, \ldots, n$ ,  $x_i$  is not a zerodivisor on  $M/(x_1, \ldots, x_{i-1})M$ . For A a local ring, the depth of M is the maximal length of a regular sequence with all  $x_i$  in the maximal ideal of A.

**Proposition.** For A a regular local ring and M an A-module,

$$\operatorname{pd}_A(M) + \operatorname{depth}_A(M) = \dim(A).$$

*Proof.* See Hartshorne Proposition III.6.12A (and associated Matsumura reference).  $\Box$ 

We can finally give a local equivalent to condition (b) from the duality theorem. Recall that our last equivalent (e) said that for each  $x \in X$ , for  $A = \mathcal{O}_{P,x}$  and I the ideal of A defining X at x,  $\operatorname{Ext}_A^{N-i}(A/I,A) = 0$  for all i < n. This is equivalent to  $\operatorname{pd}_A(A/I) \leq N - n$ , and hence to  $\operatorname{depth}_A(A/I) \geq n$ . The trick is that if M is an A/I-module, then  $\operatorname{depth}_A(M) = \operatorname{depth}_{A/I}(M)$ . Thus we have the following.

**Lemma.** The following condition is equivalent to (b).

(f) For each point  $x \in X$ , if  $B = \mathcal{O}_{X,x}$ , then  $\operatorname{depth}_B(B) \geq n$ .

On the other hand, we always have  $\operatorname{depth}_{B}(B) \leq \dim(B) \leq n$ , so it is equivalent to require  $\operatorname{depth}_{B}(B) = \dim(B) = n$ .

This condition  $\operatorname{depth}_B(B) = \dim(B)$  is in fact the definition of a *Cohen-Macaulay* local ring B. Any regular local ring is Cohen-Macaulay, since we can use generators of the cotangent space as a regular sequence. But the Cohen-Macaulay condition is much more permissive; for instance, any *local complete intersection* is Cohen-Macaulay.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Higher Riemann-Roch

In this lecture, we discuss some higher-dimensional versions of the Riemann-Roch theorem: the Riemann-Roch theorem for surfaces, the Hirzebruch-Riemann-Roch theorem, and the Grothendieck-Riemann-Roch theorem. For the first, see Hartshorne V.1; for the others, see Chapter 15 of Fulton's *Intersection Theory* (a well-deserved winner of the Steele Prize for mathematical exposition).

## 1 Surfaces

Let X be a smooth irreducible projective surface over an algebraically closed field k. Let K be a canonical divisor on X. As in the case of curves, the Riemann-Roch theorem combines an input from Serre duality with an Euler characteristic calculation.

The input from Serre duality is that for any divisor D,

$$H^0(X, \mathcal{L}(D)^{\vee} \otimes \omega_X) \cong H^2(X, \mathcal{L}(D))^{\vee}.$$

We can thus write the Euler characteristic  $\chi(X, \mathcal{L}(D))$  as

$$\dim_k H^0(X, \mathcal{L}(D)) - \dim_k H^1(X, \mathcal{L}(D)) + \dim_k H^0(X, \mathcal{L}(K-D)).$$

Unfortunately, we can't do much with the term  $\dim_k H^1(X, \mathcal{L}(D))$  other than give it a name: it's called the *superabundance* of D. However, we do at least know that it is nonnegative, and this turns out to be surprisingly useful.

The Euler characteristic calculation is made as follows. Write D as the difference between two effective divisors C - E with no common components. We then have exact sequences

$$0 \to \mathcal{L}(C - E) \to \mathcal{L}(C) \to \mathcal{L}(C) \otimes \mathcal{O}_E \to 0, \qquad 0 \to \mathcal{O}_X \to \mathcal{L}(C) \to \mathcal{L}(C) \otimes \mathcal{O}_C \to 0.$$

By additivity of  $\chi$ , we get

$$\chi(X, \mathcal{L}(C-E)) = \chi(X, \mathcal{O}_X) + \chi(C, \mathcal{L}(C)) - \chi(E, \mathcal{L}(C)).$$

The first term we are happy to leave alone since it depends only on X. The other two are calculated using *intersection theory* on the surface X. For instance, the term  $\chi(E, \mathcal{L}(C))$  equals  $C \cdot E + 1 - g_E$ , where  $g_E$  is the genus and  $C \cdot E$  is the length of the scheme-theoretic intersection  $C \times_X E$  (this amounts to Riemann-Roch on the curve E).

The term  $\chi(C, \mathcal{L}(C))$  is a bit trickier: it is  $C \cdot C + 1 - G_C$  where  $C \cdot C = C^2$  is the self-intersection of C. That can be defined as  $C \cdot C'$  if C is linearly equivalent to a divisor C' having no common components with C, but that is not always possible. In fact, the correct definition is to force the intersection pairing to be bilinear, and this sometimes involves letting  $C^2$  take negative values. For instance, if you blow up  $P^2$  at a point, the exceptional divisor has self-intersection -1. (This is a general pattern; one can in fact blow down any curve isomorphic to  $\mathbb{P}^1$  with self-intersection -1.)

Moreover, one can write the genera of C and E in terms of the canonical divisor K, basically using Riemann-Roch again:

$$C \cdot (C + K) = 2g_C - 2,$$
  $E \cdot (E + K) = 2g_E - 2.$ 

So

$$\chi(X, \mathcal{L}(D)) = \frac{1}{2}D \cdot (D - K) + \chi(X, \mathcal{O}_X).$$

As in the case of curves, this is useful for many calculations involving the geometry of surfaces, such as the Hodge index theorem and the Nakai-Moishezon criterion. These in turn figure in the classification of surfaces (which you should read about in Hartshorne if you are interested in Abhinav's work).

**Theorem** (Hodge index theorem). Fix a projective embedding of X, and let H be a divisor with  $\mathcal{L}(H) \cong \mathcal{O}_X(1)$ . Then for any divisor D such that  $D \cdot H = 0$ , we have  $D^2 \leq 0$ . (This also holds if H is ample, i.e., some positive multiple of H comes from an  $\mathcal{O}_X(1)$ .)

**Theorem** (Nakai-Moishezon criterion). A divisor D on X is ample if and only if  $D^2 > 0$  and  $D \cdot C > 0$  for all irreducible curves C on X.

## 2 Hirzebruch's generalization

Hirzebruch noticed that the Euler characteristic aspect of Riemann-Roch could be generalized to handle arbitrary vector bundles on arbitrary smooth varieties over an algebraically closed field k. Let me state his result and then explain what it means.

**Theorem** (Hirzebruch). Let X be a smooth proper scheme over k. Let  $\mathcal{F}$  be a locally free coherent sheaf on X. Then

$$\chi(X, \mathcal{F}) = \int_X \operatorname{ch}(\mathcal{F}) \cdot \operatorname{td}(T_X).$$

Here  $T_X$  is the tangent bundle of X, i.e., the dual to the bundle  $\omega_X$  of Kähler differentials (which is also called the cotangent bundle).

The Chern character ch is a certain map from coherent sheaves on X to a certain group of cycles on X. The latter are formal  $\mathbb{Q}$ -linear combinations of subschemes of X modulo a relation of rational equivalence. You should imagine this as generalizing the function taking a line bundle  $\mathcal{L}$  on a curve C to (the equivalence class of) the divisor of a nonzero rational section of  $\mathcal{L}$ .

The group of cycles is graded by codimension, and forms a commutative ring under the (appropriately defined) intersection pairing with the identity being the class of X itself in codimension 0. The Chern character is usually split up as  $\sum_d c_d(\cdot)$  with  $c_d$  being the bit in codimension d; for  $\mathcal{F}$  locally free of rank 1, we always have

$$c_d(\mathcal{F}) = \frac{1}{d!}c_1(\mathcal{F})^d.$$

The Todd class td is another such map on coherent sheaves, which I won't try to construct here, except to give the characterizing identity: for  $\mathcal{F}$  locally free of rank d,

$$\operatorname{td}(\mathcal{F}) \cdot \sum_{p=0}^{d} (-1)^{p} \operatorname{ch}(\wedge^{p} \mathcal{F}^{\vee}) = c_{d}(\mathcal{F}).$$

. The point is that it depends only on X, not on  $\mathcal{F}$ .

The Chern character and the Todd class are both examples of *characteristic classes* of vector bundles, which originally appeared in algebraic topology as tools for classifying manifolds. For instance, Milnor uses them to construct differentiable manifolds which are homeomorphic but not diffeomorphic to the 7-sphere, the so-called *exotic 7-spheres*. See Milnor and Stasheff, *Characteristic Classes* for an introduction.

Oh, and  $\int_X$  means use intersection theory (which is a pretty complicated thing to define, as evidenced by the length of Fulton's book), keep only the zero-dimensional part, and count points.

## 3 Grothendieck's generalization

In characteristic fashion, Grothendieck noticed that one can make a relative version of the Hirzebruch-Riemann-Roch theorem. Also, one can drop the locally free condition.

**Theorem** (Grothendieck). Let  $f: X \to Y$  be a proper morphism of smooth schemes over an algebraically closed field k. Then for any coherent sheaf  $\mathcal{F}$  on X,

$$\operatorname{ch}(f_*\mathcal{F})\cdot\operatorname{td}(T_Y)=f_*(\operatorname{ch}(\mathcal{F})\cdot\operatorname{td}(T_X)).$$

One has to define direct image for cycles; I won't try here.

It should be noted that already our formulation of Hirzebruch's statement is Grothendieck's; the original statement was made in the language of topology. One byproduct of this work is the development of K-theory, which is now a frequently occurring construction in both algebraic topology and algebraic geometry.

---

MIT OpenCourseWare http://ocw.mit.edu

18.726 Algebraic Geometry Spring 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# 18.726: Algebraic Geometry (K.S. Kedlaya, MIT, Spring 2009) Étale cohomology (updated 13 May 09)

In this lecture, we give a hint of the theory of *étale cohomology*. Standard references: Milne, *Étale Cohomology* (he also has some more accessible lecture notes online at jmilne.org); Tamme, *Introduction to Étale Cohomology*; Freitag-Kiehl, *Étale Cohomology and the Weil Conjectures*. You might want to read Hartshorne Appendix C first for an overview. Also, note that there is a "rogue" volume of SGA called  $SGA \neq 1/2$ , written mostly by Deligne after the fact, which gives a surprisingly legible (albeit in French) account of this stuff.

Since this is the last lecture of the course, I would like to take the opportunity to thank you, the participants, for all the hard work you put in on the problem sets, and especially for all your feedback on the notes. If you have further questions about algebraic geometry, from the general to the specific, I would be happy to discuss them!

### 1 Motivation: the Weil conjectures

Let X be a variety over a finite field  $\mathbb{F}_q$ . Weil predicted that the zeta function of X, defined as an Euler product

$$\zeta_X(T) = \prod_x (1 - T^{\deg(x \to \mathbb{F}_q)})^{-1}$$

over the closed points of X, could always be interpreted as the power series expansion of a rational function of T; this analogizes the analytic continuation of the Riemann zeta function. For instance, for  $X = \mathbb{P}^1$ ,

$$\zeta_X(T) = \frac{1}{(1-T)(1-qT)}.$$

Weil also predicted analogues of the functional equation of the zeta function, and the Riemann hypothesis. For instance, for X an elliptic curve, Hasse proved that

$$\zeta_X(T) = \frac{1 - aT + qT^2}{(1 - T)(1 - qT)}$$

for some  $a \in \mathbb{Z}$ . This expression has the symmetry property that

$$\zeta_X(q^{-1}/T) = \zeta_X(T).$$

(This example is a bit lucky; more generally, you might be off by a factor of  $q^a T^b$  for some  $a, b \in \mathbb{Z}$ . For X of pure dimension n, you should compare  $\zeta_X(T)$  with  $\zeta_X(q^{-n}/T)$ .) Hasse also proved that

$$|a| \le 2\sqrt{q},$$

or equivalently, the numerator polynomial  $1 - aT + qT^2$  has complex roots of norm  $q^{-1/2}$ .

Weil also noticed that the degrees of the factors in the zeta function appeared to have topological meaning. Namely, if X is obtained from a smooth proper scheme over some

arithmetic ring (i.e., a localization of the ring of integers in a number field) by reduction modulo a prime, then the degrees of the factors in  $\zeta_X(T)$  correspond to the Betti numbers of  $(X \times \mathbb{C})^{\mathrm{an}}$ . For example, the degrees of the factors  $1 - T, 1 - aT + qT^2, 1 - qT$  in the elliptic curve case match the Betti numbers 1, 2, 1 of a genus 1 Riemann surface.

Weil proved analogues of all these assertions for arbitrary curves, and (based on some evidence from Fermat hypersurfaces) conjectured analogues for higher dimensional varieties. More precisely, he predicted the existence of a cohomology theory  $H^i(\cdot)$  for varieties over  $\mathbb{F}_q$ , taking values in finite dimensional vector spaces over a field K of characteristic zero, in which the number of  $\mathbb{F}_q$ -rational points (i.e., the fixed points of the q-power Frobenius map) could be computed using an analogue of the Lefschetz fixed point formula in topology:

$$\#X(\mathbb{F}_{q^n}) = \sum_{i=0}^{2\dim(X)} (-1)^i \operatorname{Trace}(F_q^n, H^i(X)).$$

This immediately implies rationality of  $\zeta_X(T)$ . Symmetry should follow from a form of Poincaré duality, i.e., a perfect pairing

$$H^i(X) \times H^{2\dim(X)-i}(X) \to H^{2\dim(X)}(X) \to K.$$

The Riemann hypothesis is not quite as purely formal a consequence, since it is basically a nonnegativity condition, whereas K need not have anything to do with  $\mathbb{R}$ . But never mind that for now.

#### 2 Curves

For curves, Weil proved his conjectures by constructing an algebraic group associated to a curve C, called the *Jacobian variety* J(C). Over  $\mathbb{C}$ , this gives a complex torus which had been constructed by Abel-Jacobi using abelian integrals.

For a prime  $\ell$  not equal to the characteristic of  $\mathbb{F}_q$ , and a positive integer n, the group  $J(C)(\overline{\mathbb{F}_q})[\ell^n]$  of geometric  $\ell^n$ -torsion points is abstractly isomorphic to  $(\mathbb{Z}/\ell^n\mathbb{Z})^{2g}$ , for g the genus of C. The absolute Galois group of  $\mathbb{F}_q$  acts by  $(\mathbb{Z}/\ell^n\mathbb{Z})$ -module endomorphisms. If we take the inverse limit over n, we get a  $\mathbb{Z}_\ell$ -module  $T_\ell(J(C))$  equipped with an action of the absolute Galois group; it is nowadays called the *Tate module* of C. (For instance, if C is an elliptic curve, then J(C) = C.)

This gives the  $H^1$  (or really its dual) in a good cohomology theory. The symmetry comes from the Tate pairing. The Riemann hypothesis can be deduced using the Hodge index theorem, which gives a nonnegativity (or really a nonpositivity) assertion for the intersection pairing on  $C \times_{\mathbb{F}_q} C$ .

Aside: a noncohomological proof, using only Riemann-Roch and some clever estimates, was found later by Stepanov (and simplified by Bombieri). Good reference: Lorenzini's *Invitation to Arithmetic Geometry*.

### 3 Why étale?

One might think that coherent sheaf cohomology, as we have developed in this course, might be useful against the Weil conjectures. However, it has several problems: it lives in characteristic p rather than characteristic 0 (so it can only aspire to prove rationality mod p, rather than integrally), and its dimensions do not match Betti numbers. For instance, sheaf cohomology on a scheme of dimension n only goes up to index n, rather than 2n.

Grothendieck realized that one might get around this by trying to make an analogue of topological cohomology in which étale maps play the role of local homeomorphisms. For instance, recall one of the consequences of GAGA: for a smooth proper variety X over  $\mathbb{C}$ , every finite covering space map comes from a unique finite étale cover of X. Thus the profinite completion of the topological fundamental group can be recovered as an inverse limit of Galois groups of these étale covers.

Perhaps a better justification for considering étale covers is the following. For X a complex analytic variety and  $x \in X$ , the local ring  $\mathcal{O}_{X,x}$ , while not complete, is henselian: the conclusion of Hensel's lemma still holds. (That is, given a polynomial over  $\mathcal{O}_{X,x}$ , any simple root of the reduction modulo the maximal ideal lifts uniquely to a root.) This is not true for schemes, though. A related geometric statement is that if  $f: Y \to X$  is an étale morphism of schemes, and  $x \in X$  is a point, then there is no way to draw disjoint open neighborhoods of the points of  $f^{-1}(x)$ , so you cannot view the étale map as a local homeomorphism.

### 4 Topology revisited

In order to combine the ideas about étale covers with sheaf cohomology, Grothendieck had to take the apparently drastic step of modifying the notion of a topology on a space. But in retrospect, this isn't such a strange modification to make. After all, presheaves on a topological space X are nothing more than contravariant functors on the category  $\underline{X}$  of open sets. Why not state all the sheaf axioms in terms of the structure of that category?

Grothendieck realized that stating the sheaf axiom really only requires knowing what an open cover is, leading to the following definition. Let  $\mathcal{C}$  be a category admitting fibre products. A *Grothendieck topology* consists of the following data. For each  $X \in \mathcal{C}$ , you must tell me which collections of morphisms  $\{U_i \to X\}_{i \in I}$  are *coverings* of X. This prescription must satisfy some hypotheses.

- Any isomorphism  $X \to Y$  is by itself a cover of Y.
- For any  $Y \to X$ , if  $\{U_i \to X\}$  is a cover, then  $\{U_i \times_X Y \to Y\}$  is a cover. That is, open covers can be restricted to open subsets.
- If  $\{U_i \to X\}$  is a cover, and for each  $i \{V_{ij} \to U_i\}$  is a cover, then  $\{V_{ij} \to X\}$  is also a cover. That is, covering each open in a cover gives a cover.

(Strictly speaking, this is a *Grothendieck pretopology* because it only gives you the analogue of a *basis* for a topology. You should really throw in all coverings "generated" by these too.)

A category equipped with a Grothendieck topology is called a *site*. For instance, the *big* étale site of a scheme S is the category of all S-schemes, in which coverings are collections of étale morphisms which form a set-theoretic cover. That is,  $\{U_i \to X\}$  is a cover if and only if each  $U_i$  is étale and the union of their images is X. (If you only bother keeping objects which are themselves étale over S, you get the *small étale site*.)

There are many other useful Grothendieck topologies that occur frequently in algebraic geometry. These include the fppf topology (fidèlement plat de présentation finie = faithfully flat of finite presentation), the fpqc topology (fidèlement plat et quasicompact = faithfully flat quasicompact), the smooth topology, the flat topology, the syntomic topology (flat and locally of finite presentation), the Nisnevich topology (étale, but each point must be covered by a point with the same residue field), etc. There are also useful examples where you start with a usual topological space but use only some of the available open covers; this occurs in the definition of rigid analytic spaces (i.e., analytic spaces over a nonarchimedean complete field like  $\mathbb{Q}_p$ ).

Anyway, once you know what a Grothendieck topology is, you can define a *sheaf* of abelian groups (say) on it. Namely, you want a contravariant functor F from your category to Ab, such that for any cover  $\{U_i \to X\}$ , we have an exact sequence

$$0 \to F(X) \to \prod_i F(U_i) \to \prod_{i,j} F(U_i \times_X U_j)$$

where the last map computes a section on  $F(U_i \times_X U_j)$  as the restriction from  $U_i$  minus the restriction from  $U_j$ . For instance, in most reasonable cases, the *structure sheaf*  $F(X) = \mathcal{O}_X$  is a sheaf.

There is also a notion of *sheafification* but this is complicated by the fact that we don't have points with with to define stalks. No matter: what are points anyway but decreasing families of open sets? One can make an artificial definition of "points" in that fashion; this brings one dangerously close to the notion of a *topos*, which I will skip over entirely. (Roughly speaking, a topos is the category of sheaves on a site with values in a given category, like sets or abelian groups.)

## 5 Étale cohomology in practice

We can now define sheaf cohomology on any site with a final object as the derived functors of global sections, meaning sections over the final object. (One can fix this even if there is no final object, by taking a compatible family of sections over *every* element of the site. Yeesh.)

However, it's not so straightforward to compute étale cohomology of a scheme X with coefficients in a sheaf  $\mathcal{F}$ . On one hand, writing down étale cochains is not a problem: you specify an étale cover of X and then some sections on each element of the cover. Writing down cocycles isn't that much harder: you have to write down another étale cover on which

you can check that the differential of your cochain vanishes. The hard part is, given a cochain, how do you tell whether it is zero or not?

Despite this complication, one can prove quite a lot. For instance, if you start with a quasicoherent sheaf  $\mathcal{F}$  on a scheme X, you get a sheaf on its big and small étale sites by setting the sections over an open  $i: U \to X$  to be  $i^*\mathcal{F}$ . But this is a boring example, because the resulting sheaf cohomology turns out to agree with usual sheaf cohomology on the "Zariski site" (i.e., what we already know).

What makes the étale site fun is that you get strange new sheaves, much more akin to the locally constant sheaves in topology, and their cohomology is quite interesting. For instance, you can make a locally constant sheaf associated to any (pro)finite abelian group (by sheafifying the constant presheaf), and this gives you something with topological meaning.

**Theorem.** Let X be a smooth proper scheme over  $\mathbb{C}$ . Then for any prime  $\ell$ , the cohomology of the étale locally constant sheaf associated to the  $\ell$ -adic integers  $\mathbb{Z}_{\ell}$  computes the topological Betti numbers of X.

The fun comes when you start with a scheme over an arithmetic base, like  $\mathbb{Q}$ . If you extend the base to  $\overline{\mathbb{Q}}$  and then take étale cohomology with coefficients in  $\mathbb{Z}_{\ell}$ , the result carries an action of the absolute Galois group of  $\mathbb{Q}$ . E.g., for an elliptic curve, the first étale cohomology is (dual to) the  $\ell$ -adic Tate module, i.e., the inverse limit of the  $\ell$ -power torsion groups viewed as a Galois representation.

### 6 Back to the Weil conjectures

Let X be a smooth proper scheme over the finite field  $\mathbb{F}_q$ . Pick any prime  $\ell \neq q$ . For each positive integer n, we can consider the locally constant étale sheaf  $\mathbb{Z}/\ell^n\mathbb{Z}_X$  on X. Let  $\mathbb{Z}_{\ell_X}$  be the inverse limit of these; this is *not* the same as the locally constant étale sheaf generated by  $\mathbb{Z}_{\ell}$ . (E.g., in the example of the elliptic curve, that is because the  $\ell^{\infty}$ -power torsion is not defined over a *finite* extension of the base field.)

Nonetheless,  $\underline{\mathbb{Z}_{\ell}}$  is a good sheaf to work with. (It is an example of a sheaf which is *lisse*, or *smooth* if you prefer to translate from the French.) We will be interested in working with the

$$H^{i}(X) = H^{i}_{\mathrm{et}}(X \times_{\mathbb{F}_{q}} \overline{\mathbb{F}_{q}}, \underline{\mathbb{Z}_{\ell}}) \otimes_{\mathbb{Z}_{\ell}} \mathbb{Q}_{\ell},$$

which is a collection of  $\mathbb{Q}_{\ell}$ -vector spaces. These turn out (with some effort) to be finite dimensional over  $\mathbb{Q}_{\ell}$ , and carry a Lefschetz trace formula. This proves rationality of the zeta function.

Aside: rationality had already been proved by Dwork around 1960 using p-adic analytic methods, but not using cohomology. Nowadays, though, Dwork's proof has been reinterpreted in terms of a different Weil cohomology, called rigid cohomology, taking values in a p-adic field. (Remember that  $\ell = p$  is excluded in étale cohomology, because this case behaves badly. For instance, an elliptic curve over an algebraically closed field of characteristic p has at most p points killed by p, not  $p^2$ .)

Returning to étale cohomology, there is also a Poincaré duality which implies symmetry. The Riemann hypothesis, of course, is more subtle; Grothendieck had predicted it would follow from a suitable analogue of the Hodge index theorem, which was one of his *standard conjectures*. This analogue is still open; instead, Deligne proved the Riemann hypothesis by a rather clever combination of ideas, including an algebro-geometric variant of the "Rankin squaring" argument from classical modular forms. Laumon later gave a similar but technically simpler proof by adding the use of a *cohomological Fourier transform*. (These proofs are largely independent of which Weil cohomology you are using. In particular, with some effort they can be transposed into rigid cohomology.)
