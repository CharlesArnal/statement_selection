## **Massachusetts Institute of Technology**

Department of Mathematics 18.965 Fall 04 Lecture Notes Tomasz S. Mrowka

Lecture 1.

## 1 Manifolds: definitions and examples

Loosely manifolds are topological spaces that look locally like Euclidean space. A little more precisely it is a space *together with* a way of identifying it locally with a Euclidean space which is compatible on overlaps. To formalize this we need the following notions. Let *X* be a Hausdorff, second countable, topological space.

**Definition 1.1.** A chart is a pair  $(U, \phi)$  where U is an open set in X and  $\phi : U \to \mathbb{R}^n$  is homeomorphism onto it image. The components of  $\phi = (x^1, x^2, \dots, x^n)$  are called coordinates.

Given two charts  $(U_1, \phi_1)$  and  $(U_2, \phi_2)$  then we get overlap or transition maps

$$\phi_2 \circ \phi_1^{-1} : \phi_1(U_1 \cap U_2) \to \phi_2(U_1 \cap U_2)$$

and

$$\phi_1 \circ \phi_2^{-1} : \phi_2(U_1 \cap U_2) \to \phi_1(U_1 \cap U_2)$$

**Definition 1.2.** Two charts  $(U_1, \phi_1)$  and  $(U_2, \phi_2)$  are called compatible if the overlap maps are smooth.

In practice it is useful to consider manifolds with other kinds of regularity. One many consider  $C^k$ -manifolds where the overlaps are  $C^k$ -maps with  $C^k$  inverses. If we only require the overlap maps to be homeomorphisms we arrive at the notion of a topological manifold. In some very important work of Sullivan one consider Lipschitz, or Quasi-conformal manifolds.

An *atlas* for X is a (non-redundant) collection  $\mathcal{A} = \{(U_\alpha, \phi_\alpha) | \alpha \in A\}$  of pair wise compatible charts. Two atlases are *equivalent* if there their union is an atlas. An atlas  $\mathcal{A}$  is called *maximal* if any other atlas compatible with it is contained in it.

Exercise 1. Using Zorn's lemma, show that any atlas is contained in a unique maximal atlas.

**Definition 1.3.** A smooth n-dimensional manifold is a Hausdorff, second countable, topological space X together with an atlas, A.

## 1.1 examples

 $\mathbb{R}^n$  or any open subset of  $\mathbb{R}^n$  is a smooth manifold with an atlas consisting of one chart. The unit sphere

$$S^n = \{(x^0, x^1, \dots, x^n) | \sum_{i=0}^n (x^i)^2 = 1\}$$

has an atlas consisting of two charts  $(U_{\pm}, \phi_{\pm})$  where  $U_{\pm} = S^n \setminus \{(\pm 1, 0, 0, \dots, 0)\}$  and

$$\phi_{\pm}(x^0, x^1, \dots, x^n) = \frac{1}{\pm 1 - x_0}(x^1, \dots, x^n)$$

Real projective space,  $\mathbb{RP}^n$ , is space of all lines through the origin in  $\mathbb{R}^{n+1}$  which we can identify with nonzero vectors up to the action of non-zero scalars so  $\mathbb{RP}^n = (\mathbb{R}^{n+1} \setminus \{\vec{0}\})/\mathbb{R}^*$ . The equivalence class of  $(x_0, \ldots, x_n)$  is denoted  $[x_0 : x_1 : \ldots : x_n]$ .  $\mathbb{RP}^n$  has an atlas consisting of n+1 charts. The open sets are

$$U_i = \{ [x_0 : x_1 : \dots : x_n] | x_j \in \mathbb{R}, \text{ and } x_i \neq 0 \}$$

and the corresponding coordinates are

$$\phi_i([x_0:x_1:\ldots:x_n])=(x_1/x_i,\ldots,\widehat{x_i/x_i},\ldots,x_n/x_i).$$

Similarly we have complex projective space,  $\mathbb{CP}^n$ , the space of a line through the origin in  $\mathbb{C}^{n+1}$ . So just as above we have  $\mathbb{CP}^n = (\mathbb{C}^{n+1} \setminus \{\vec{0}\})/\mathbb{C}^*$ . A typical point of  $\mathbb{CP}^n$  is written  $[z_0:z_1:\ldots:z_n]$ .  $\mathbb{CP}^n$  has a atlas consisting of n+1 charts. The open sets are

$$U_i = \{[z_0 : z_1 : \ldots : z_n] | z_i \neq 0\}$$

and the corresponding coordinates are

$$\phi_i([z_0:z_1:\ldots:z_n])=(z_1/z_i,\ldots,\widehat{z_i/z_i},z_n/z_i).$$

.

*Exercise* 2. Show that in fact the above construction yield charts.

Notice that in the case of  $\mathbb{CP}^n$  the coordinates have values in  $\mathbb{C}^n$  and so the overlap maps map an open subset of  $\mathbb{C}^n$  to  $\mathbb{C}^n$ . We can ask that they are holomorphic. We make the following definition.

**Definition 1.4.** A complex manifold is a Hausdorff second countable topological space X, with an atlas  $\mathcal{A} = \{(U_{\alpha}, \phi_{\alpha}) | \alpha \in A \text{ the coordinate functions } \phi_{\alpha} \text{ take values in } \mathbb{C}^n \text{ and so all the overlap maps are holomorphic.}$ 

Let  $Gr_k(\mathbb{R}^n)$  be the space of k-planes through the origin in  $\mathbb{R}^n$ .

*Exercise* 3. Show that  $Gr_k(\mathbb{R}^n)$  has an atlas with  $\binom{n}{k}$  charts each homeomorphic with  $\mathbb{R}^{k(n-k)}$ .

Similarly we have  $\operatorname{Gr}_k(\mathbb{C}^n)$  the space of all complex k-plane through the origin in  $\mathbb{C}^n$ .

*Exercise* 4. Show that  $Gr_k(\mathbb{C}^n)$  has an atlas with  $\binom{n}{k}$  charts each homeomorphic with  $\mathbb{C}^{k(n-k)}$ . Show that we can give  $Gr_k(\mathbb{C}^n)$  the structure of a complex manifold.

---

## Lecture 2.

## 2 Smooth maps and the notion of equivalence

Let X and Y be smooth manifolds. A continuous map  $f: X \to Y$  is called smooth if for all charts  $(U, \phi)$  for and X and  $(V, \psi)$  for Y we have that the composition

$$\psi \circ f \circ \phi^{-1} : \phi(U \cap f^{-1}(V)) \to \psi(V)$$

is smooth.

Two manifolds X and Y are called *diffeomorphic* if there is a homeomorphism  $h: X \to Y$  so that h and  $h^{-1}$  are smooth.

## 3 Standard pathologies.

The condition that *X* be Hausdorff and second countable does not follow from the existence of an atlas.

The line with two origins. Let X be the quotient space of  $\mathbb{R} \times \{0, 1\}$  by the equivalence relation  $(t, 1) \equiv (t, 0)$  unless t = 0. Then X is not Hausdorff, however X admits an atlas with two charts. Let  $U_i$  be the image of  $\mathbb{R} \times \{i\}$  in X. These maps invert to give coordinates.

*Remark* 1. Actually non-Hausdorff spaces which satisfy all the other properties arise in real life for example in the theory of foliations or when taking quotients by non- compact group actions. More work is required to come up with a useful notions to replace that of manifolds in this context.

The long line. Let  $S_{\Omega}$  denote the smallest uncountable totally ordered set. Consider the product  $X = S_{\Omega} \times (0, 1]$  with dictionary order topology. Then give X charts as follows. For  $(\omega, t) \in X$  if  $t \neq 1$  let  $U_{(\omega, t)} = \{\omega\} \times (0, 1)$  and  $\phi_{(\omega, t)} \colon U \to \mathbb{R}$  be given by  $\phi_{(\omega, t)}(\omega, t) = t$ . If t = 1 let  $S(\omega)$  denote the successor of  $\omega$ . Set  $U_{(\omega, 1)} = \{\omega\} \times (0, 1] \sup\{S(\omega)\} \times (0, 1)$  and

$$\phi_{(\omega,t)}(\eta,t) = \begin{cases} t & \text{if } \eta = \omega \\ t+1 & \text{if } \eta = S(\omega). \end{cases}$$

Exercise 5. Check that overlaps are smooth.

The collection  $\{U_{(\omega,1/2)}\}_{\omega\in S_{\omega}}$  is uncountable and consists of disjoint open sets, so X is not second countable.

Different charts

Consider  $\mathbb{R}_1$  denote  $\mathbb{R}$  with the following charts  $(\mathbb{R}, x)$  and  $\mathbb{R}_2$  with the chart  $(\mathbb{R}, x^3)$ . Identity map  $\mathbb{R}_1 \to \mathbb{R}_2$  is smooth but not  $\mathbb{R}_2 \to \mathbb{R}_1$ .  $\mathbb{R}_1$  and  $\mathbb{R}_2$  are diffeomorphic by the map  $x \mapsto x^3$  thought of as a map from  $\mathbb{R}_1 \to \mathbb{R}_2$ .

These pathologies are simple problems to keep in mind when thinking about the definitions. There are far more subtle issues that arise. Given a topological manifold we can ask can carry an atlas, and if it carries an atlas how many non-diffeomorphic atlases does it carry. The first observation of this phenomenon is due to John Milnor who showed that the seven-sphere admits an atlas (with two charts!) which is not diffeomorphic to the standard differentiable structure. We'll examine this example later in the course.

---

## Lecture 3.

## 4 The derivative of a map between vector spaces

Let  $f: V \to W$  be a smooth map between real vector spaces.

**Definition 4.1.** Given  $x \in V$  we say that f is differentiable at x if there is a linear map  $L_x \colon V \to W$  so that for all  $v \in V$  we have:

$$|| f(x) - f(x') - L_x(x - x') || = o(||x - x'||).$$

Here we using the Landau symbol o to mean a function  $o: \mathbb{R}_+ \to \mathbb{R}$  continuous at zero and o(0) = 0.

Really this is an improper definition. We really need V and W to be normed vector spaces and it is natural to require that L is a continuous linear map. One can try to develop differential calculus on manifolds modelled on general topological vector spaces. A sufficiently general context to work in is that of manifolds modelled on Banach spaces, that is complete normed linear spaces. Essentially of the basic results in differential topology work in this context with the same proofs (as long as proof don't use coordinates)

Notice that map L in the above definition is unique. If L' is another such map then

$$o(\|x - x'\|) \ge \|f(x) - f(x') - L(x - x') - (f(x) - f(x') - L'(x - x'))\|$$

$$= \|(L - L')(x - x')\|$$

So 
$$(L - L')(x - x') = 0$$
.

The map L is called the *differential* of f at x and is denoted

$$d_x f$$
 or  $D_x f$ .

We say f is differentiable if f is differentiable at each  $x \in U$  and is continuously differentiable if

$$df: U \to \text{hom}(V, W).$$

is continuous. The second derivative is the derivative of the first derivative and thus is a map

$$d^2 f: U \to \text{hom}(V, \text{hom}(V, W)).$$

In the finite dimensional case hom(V, hom(V, W)) with a subspace of  $hom(V \otimes V, W)$ . In the infinite dimensional case we need to be more careful but we can identify hom(V, hom(V, W)) with bilinear maps from

$$V \rightarrow W$$
.

You can read all about this in gory detail in [?]

**Definition 4.2.** A smooth map  $f: X \to Y$  is called an immersion its differential is everywhere injective. It is called a submersion if it differential is everywhere surjective.

There obvious examples of such maps. Suppose m < n are positive integers

$$i: \mathbb{R}^m \to \mathbb{R}^n$$

given by

$$i(x^1, \ldots, x_m) = (x^1, \ldots, x_m, 0, \ldots, 0)$$

is an immersion while

$$s: \mathbb{R}^n \to \mathbb{R}^m$$

given by

$$s(x^1, \ldots, x_m, x_{m+1}, \ldots, x_n) = (x^1, \ldots, x_m)$$

is a submersion. We will see in the next section that locally these simple examples are completely general.

---

## Lecture 4.

## 5 Inverse, and implicit function theorems.

Among the basic tools of the trade are the inverse and implicit function theorems. We will first state them in a coordinate dependent fashion. When we develop some of the basic terminology we will have available a coordinate free version.

**Theorem 5.1.** Let U be a neighborhood let  $f: U \subset V \to W$  be a smooth map. Suppose  $d_x f: \mathbb{R}^n \to \mathbb{R}^n$  is invertible for some  $x \in U$ . Then there is a neighborhood  $U' \subset U$  of x so that

$$f|U' \to f(U')$$

is a diffeomorphism. Furthermore

$$d_0(f^{-1}) = (d_0 f)^{-1}.$$

*Proof.* We will construct an inverse for f using the contraction mapping theorem. It is enough to prove the result in the case that x = 0 and f(0) = 0 and  $D_0 f = Id$ . (For the last condition replace f by  $(D_0 f)^{-1} \circ f$ .. Set g(x) = f(x) - x (so g is the "nonlinear" part of f.) The equation f(x) = y can be rewritten as

$$x + g(x) = y$$

or as the fixed point equation

$$y - g(x) = x$$
.

We claim that if f is  $C^1$  then for y in a small enough neighborhood of  $0 x \mapsto y - g(x) = h_y(x)$  is a contraction mapping on a small enough ball.

Since  $D_0h_y(x)=0$  and  $h_y$  is  $C^1$  there is a neighborhood  $B_r(0)$  so that  $\|D_0h_y\|\leq \frac{1}{2}$ . By the mean value theorem for  $x,x'\in B_r(0)$  we have

$$||h_y(x) - h_y(x')|| \le \frac{1}{2}||x - x'||.$$

Furthermore if  $x \in B_r(0)$  and  $y \in B_{r/2}(0)$  we have

$$\begin{split} \|h_y(x)\| &\leq \|h_y(x) - h_y(0)\| + \|h_y(0)\| \\ &\leq \frac{1}{2} \|x\| + \|y\| \\ &\leq \frac{r}{2} + \frac{r}{2} \\ &\leq r. \end{split}$$

Thus for  $y \in B_{r/2}$  we have  $h_y(B_r) \subset B_r$  and  $h_y$  is a contraction there. The contraction mapping theorem implies for each y the existence of a unique fixed point  $\phi(y)$  which is a least a set wise inverse for f.

We check that  $\phi(y)$  is continuous.

$$\|\phi(y) - \phi(y')\| = \|h_y(\phi(y)) - h_{y'}(\phi(y'))\|$$

$$\leq \|g(\phi(y)) - g(\phi(y'))\| + \|y' - y\|$$

$$\leq \frac{1}{2} \|\phi(y) - \phi(y')\| + \|y' - y\|$$

SO

$$\|\phi(y) - \phi(y')\| \le 2\|y' - y\| \tag{1}$$

Now we check that  $\phi$  is differentiable. Let  $x = \phi(y)$  and  $x' = \phi(y')$ 

$$\|\phi(y) - \phi(y') - (d_x f)^{-1} (y - y')\| = \|x - x' - (d_x f)^{-1} (f(x) - f(x'))\|$$

$$\leq \|d_x f\|^{-1} \|(d_x f)(x - x') - (f(x) - f(x'))\|$$

$$\leq o(\|x - x'\|)$$

$$\leq o(\|y - y'\|).$$

where we use the differentiability of f to go from the second to third lines and and inequality 1 to go from the third to the fourth.

Notice that if f is continuously differentiable then so is  $\phi$ .

An important corollary of the inverse function theorem is the implicit function theorem. The implicit function theorem can be stated in various, each useful in some situation. We will use repeatedly the *Open Mapping Theorem* which say that a surjective bounded linear map between Banach spaces is an open mapping in particular an bounded linear map which is an algebraic isomorphism is an isomorphism.

**Theorem 5.2.** Let  $f: U \subset V \to W$  be a smooth map with f(0) = 0. Suppose that for some x in U we have that  $D_x f$  is surjective and  $\ker(D_x f)$  admits a closed complement C. Then there are neighborhoods  $U_1$  of  $0 \in \ker(D_x f)$ ,  $U_2$  of  $0 \in W$  and diffeomorphisms  $\phi: U_1 \times U_2 \to U$  and  $\psi: U_2 \to W$  so that the following diagram commutes:

$$\begin{array}{ccc} U & \stackrel{f}{\longrightarrow} & W \\ \uparrow \phi & & \uparrow \psi \\ U_1 \times U_2 & \stackrel{p_2}{\longrightarrow} & U_2 \end{array}$$

where  $p_2$  denotes the projection on the second factor.

*Proof.* Write a typical element of U as a pair (k, c) with  $k \in ker(D_x f)$  and  $c \in C$ . The fact that C is closed means in implies that C is a C a Banach space in its own right. Then the map  $K \times C \to V$  given by  $(k, c) \mapsto k + c$  is an isomorphism by the Open Mapping Theorem. The Open Mapping Theorem also implies that  $d_{0,0}f|_C: C \to W$  is an isomorphism. Let  $L: W \to C$  denote its inverse. Consider the map

$$F(k, c) = (k, Lf(k, c)).$$

We have that

$$d_{(0,0)}F = \begin{bmatrix} \operatorname{Id}_K & * \\ 0 & \operatorname{Id}_C \end{bmatrix}$$

and again by the Open Mapping Theorem the differential of F at (0,0) is an isomorphism. The inverse function theorem implies F has an inverse,  $\phi$ , in a neighborhood of (0,0). Setting  $\psi = d_{0,0}f|_C$  we have

$$f(\phi(k,c)) = \psi(p_2(k,c))$$

on a sufficiently small neighborhood of (0,0) since

$$Lf(\phi(k,c)) = c$$

on such a neighborhood.

We call a point x where  $D_x f$  is not a surjective a critical point. A point in the range of f which is not the image of a critical point is called a regular value.

**Definition 5.3.** A subset Y of a manifold X is called submanifold if for all  $y \in Y$  there is a neighborhood U of Y and a chart  $\phi : V \to B$  so that  $\phi(Y \cap U)$  is an open subset of a closed linear subspace admitting a complement.

Having made these definition we have a corollary of the implicit function theorem.

**Corollary 5.4.** *The preimage of a regular value is a submanifold.*

---

## Lecture 5.

## 6 More examples.

The orthogonal group. Let

$$O(n) = \{ A \in \mathbf{M}_{n \times n}(\mathbb{R}) | AA^T = I \}.$$

be the group of orthogonal transformations of  $\mathbb{R}^n$ . We claim that the orthogonal group is a smooth manifold. To see this consider the map

$$f: \mathbf{M}_{n \times n}(\mathbb{R}) \to \mathbf{S}ym_n(\mathbb{R})$$

given by

$$f(A) = AA^T$$

where  $\operatorname{Sym}_n(\mathbb{R})$  denotes the space of symmetric  $n \times n$  matrices. Then  $O(n) = f^{-1}(I)$  so it suffices to show that I is a regular value. The differential of f is

$$D_A f(B) = AB^T + BA^T.$$

and we must show that it is surjective. Fix  $A \in O(n)$  and choose  $C \in Sym_n(\mathbb{R})$ . If we take  $B = \frac{1}{2}CA$  then

$$D_A f(B) = \frac{1}{2} (AA^T C^T + CAA^T) = C$$

as required.

Let prove existence and uniqueness theorem for ODEs using the inverse function theorem. Let  $X: B \to B$  be a smooth map of Banach spaces. We would like so see that the differential equation

$$\frac{dx}{dt} = X(x)x(0) = x_0$$

has a unique solution for all  $x_0 \in B$ . Define a map

$$F: C^1([0,\epsilon],B) \to C^0([0,\epsilon],B) \times B$$

by

$$F(x) = \left(\frac{dx}{dt} - X(x), x(0)\right)$$

**Lemma 6.1.** If X is K-Lipschitz so is  $F: C^0 \to C^0$ . If X is  $C^1$  with uniformly bounded

*Proof.* 
$$|X(x)-X(x')|_{C^0} \le K|x-x'|_{C^0}$$
 if  $X$  is  $K$ -Lipschitz. We also have that 
$$|X(x)-X(x')-D_xX(x-x')| \le o_x(x-x')$$

---

## Lecture 6.

## 7 Vector bundles and the differential

Consider the Grassman manifold say  $Gr_2(\mathbb{R}^4)$  of two planes in  $\mathbb{R}^4$ . Let

$$\gamma = \{(\Pi, x) \in \operatorname{Gr}_2(\mathbb{R}^4) \times \mathbb{R}^4 | x \in \Pi\}.$$

Let  $p: \gamma \to \operatorname{Gr}_2(\mathbb{R}^4)$  be the natural projection. The fibers of  $p, p^{-1}(\Pi)$  are vector spaces (in this case over the reals).

This is an example of a vector bundle. We'll give the definition appropriate for the world of smooth manifolds. There is an obvious version of the definition for more general topological spaces.

**Definition 7.1.** Let V be a vector space (over the reals, complexes or quaternions.) A vector bundle with fiber V is a triple (E, B, p) where E and B are smooth manifolds and  $\pi : E \to B$  is a smooth map. For each  $b \in B$ ,  $p^{-1}(b)$  has the structure of a vector space over the same field as V and for each  $b \in B$  there is an open set U and a smooth map  $\phi : p^{-1}(U) \to V$  which is linear isomorphism on each fiber. In addition the map  $\tau_{\phi} : p^{-1}(U) \to U \times V$  given by  $\tau_{\phi}(e) = (p(e), \phi(e))$  is a diffeomorphism.

The map  $\tau_{\phi}$  is called a *local trivialization*.

## Example 7.2. Let

$$\gamma = \{(\Pi, v) \subset \operatorname{Gr}_k(\mathbb{R}^n) \times \mathbb{R}^n | v \in \Pi\}.$$

We claim as the natural projection  $p: \gamma \to \operatorname{Gr}_k(\mathbb{R}^n)$  has the structure of a vector bundle with fiber  $\mathbb{R}^k$ . Let  $\phi: U_\Pi \to \operatorname{hom}(\Pi, \Pi^\perp)$  be one of our charts. Then  $\phi^{-1}$  is given by  $A \to \Gamma_A \subset \mathbb{R}^n = \Pi \oplus \Pi^\perp$  where  $\Gamma_A$  denotes the graph of A. The map  $\phi: p^{-1}(U_\Pi) \to \Pi$  is simply the orthogonal projection.

A very important notion is the transition function. Suppose we are given two trivializations  $\tau_{\alpha}$ :  $p^{-1}(U_{\alpha}) \to U_{\alpha} \times V$  and  $\tau_{\beta}$ :  $p^{-1}(U_{\beta}) \to U_{\beta} \times V$ . Then get a map

$$g_{\alpha\beta}\colon U_{\alpha}\cap U_{\beta}\to \mathrm{Gl}(V).$$

defined as follows. If

$$\tau_{\alpha}(v) = (p(v), \phi_{\alpha}(v)) \text{ and } \tau_{\beta}(v) = (p(v), \phi_{\beta}(v))$$

then

$$g_{\alpha\beta}(p(v))\phi_{\beta}(v) = \phi_{\alpha}(v).$$

The transition function satisfy the *cocycle condition*: If we have three trivializations  $\tau_{\alpha}$ ,  $\tau_{\beta}$ ,  $\tau_{\gamma}$  over open sets  $U_{\alpha}$ ,  $U_{\beta}$ ,  $U_{\gamma}$  then for all  $x \in U_{\alpha} \cap U_{\beta} \cap U_{\gamma}$ 

$$g_{\alpha\beta}g_{\beta\gamma}g_{\gamma\alpha}=1$$

A vector bundle is determined its transition functions and give an open cover  $\{U_{\alpha}\}$  and a collection of functions

$$g_{\alpha\beta}\colon U_{\alpha}\cap U_{\beta}\to \mathrm{Gl}(V).$$

satisfying the cocycle condition we can construct a vector bundle.

## 7.1 New vector bundles from old

We can get new vector bundles from old bundles in a number of ways. Given  $p_1: V_1 \to X$  and  $p_2: V_2 \to X$  we can take direct (or Whitney) sum to get a bundle  $V_1 \oplus V_2 \to X$  whose fiber above x is  $p_1^{-1}(x) \oplus p_2^{-1}(x)$ . Another important operation is the pullback. Suppose we have  $p: V \to X$  and  $f: Y \to X$  a smooth map. Then we can form a vector bundle over Y as follows. The total space denoted  $f^*(V)$  is:

$$f^*(V) = \{(y, v) | f(y) = p(v)\}$$

and projection

$$f^*(p)(y, v) = y.$$

---

## Lecture 7.

## 7.2 The tangent bundle

Let M be a smooth manifold. We will associate to M a bundle TM. We will do this concretely but there are many ways of doing this. You should read about them all!!!

We know what a tangent vector in  $\mathbb{R}^n$ .

**Definition 7.3.** A tangent vector to M at x is the equivalence class of all pairs v,  $(U, \phi)$  where  $(U, \phi)$  is a chart about x and v is a tangent vector to  $\mathbb{R}^n$  at  $\phi(x)$ . We say that v',  $(U', \phi')$  is equivalent to v,  $(U, \phi)$  if

$$v' = d_{\phi(x)}(\phi' \circ \phi^{-1})(v).$$

The tangent bundle TM to M is the set of all tangent vectors.

In other words the tangent bundle to M is bundle determined by choosing an atlas  $\{(U_{\alpha}, \phi_{\alpha}) | \alpha \in X\}$  and taking as transition functions

$$g_{\alpha\beta}(x) = d_{\phi_{\beta}(x)}(\phi_{\alpha} \circ \phi_{\beta}^{-1})(v).$$

Given a chart  $(U, \phi)$  we get coordinates  $x^1, x^2, \ldots, x^n$  on U. A typical tangent X vector is written as

$$X = a^{1} \frac{\partial}{\partial x^{1}} + a^{2} \frac{\partial}{\partial x^{2}} + \dots + a^{n} \frac{\partial}{\partial x^{n}}.$$

reminding us that we can differentiate function using tangent vectors. Given  $f: M \to \mathbb{R}$  and a tangent vector at x inM we define

$$Xf(x) = a^{1} \frac{\partial f \circ \phi^{-1}}{\partial x^{1}}(\phi(x)) + a^{2} \frac{\partial f \circ \phi^{-1}}{\partial x^{2}}(\phi(x)) + \dots + a^{n} \frac{\partial f \circ \phi^{-1}}{\partial x^{n}}(\phi(x)).$$
(2)

in other word the usual directional derivative of  $f \circ \phi^{-1}$ .

Given a smooth map  $f: M \to N$  we can define the differential of f as a map

$$Df:TM \to TN$$
.

Given x in M and  $X = (v, (U, \phi))$  a tangent vector and a chart  $(V, \psi)$  about f(x) set  $D_x f(X)$  to be the equivalence class of the vector

$$D_{\phi(x)}(\psi \circ f \circ \phi^{-1})(v)$$

and the chart,  $(V, \psi)$  or in terms of coordinates if we write

$$\psi \circ f \circ \phi^{-1}(x^1, x^2, \dots, x^n) = (f^1(x^1, \dots, x^n), \dots, f^m(x^1, \dots, x^n))$$

then the matrix of Df is

$$\left[\frac{\partial f^i}{\partial x^j}\right].$$

---

## Lecture 8.

## 8 Connections

We motivate the introduction of connections in a vector bundle as a generalization of the usual directional derivative of functions on a manifold. Given a vector field X and a function f on a manifold M, its directional derivative is a new function as in equation (2). Thus we have a map

$$C^{\infty}(M; TM) \times C^{\infty}(M) \to C^{\infty}(M).$$

This map has the following properties.

$$X(fg) = fXg + gXf \tag{3}$$

$$(\alpha X + \beta Y)f = \alpha Xf + \beta Yf \tag{4}$$

where X and Y are smooth vector fields and  $\alpha$ ,  $\beta$ , f and g are smooth functions.

If we try to generalize this to a directional derivative on sections of a vector bundle we would like a map

$$C^{\infty}(M; TM) \times C^{\infty}(M; E) \to C^{\infty}(M; E).$$

This map is using denoted

$$(X,s)\mapsto \nabla_X s$$

We can no longer multiply sections of a vector bundle but we can multiply sections of a vector bundle by functions. The appropriate generalization of the two rules about are

$$\nabla_X f s = f \nabla_X s + (Xf) s \tag{5}$$

$$\nabla_{\alpha X + \beta Y} s = \alpha \nabla_X s + \beta \nabla_Y f \tag{6}$$

## 9 Partitions of unity

Given an open cover,  $\{U_{\alpha} | \alpha \in A\}$  of a topological space X we say that a collection of function  $\beta_{\alpha} : X \to \mathbb{R}_{>0}$  is a *partition of unity* if

- 1. For all  $\alpha \in A$  Support $(\beta_{\alpha}) \subset U_{\alpha}$
- 2. The collection {Support( $\beta_{\alpha}$ )| $\alpha \in A$ } is locally finite, that is to say for all  $x \in X$  there is a neighborhood of x meeting only finitely many of members of the collection.
- 3. For all  $x \in X$  we have

$$\sum_{\alpha \in A} \beta_{\alpha}(x) = 1.$$

Smooth manifolds have smooth partitions of unity.

## 10 The Grassmanian is universal

We say that bundle is of *finite type* if there is a finite set of trivializations whose open sets cover. In this section we will prove the following theorem.

**Theorem 10.1.** Let  $E \to M$  be a vector bundle of finite type. Then for some N large enough there is a map

$$f: M \to \operatorname{Gr}_k(\mathbb{R}^N).$$

*Proof.* Let  $\{(U_i, \tau_i) | i = 1, \dots m\}$  be a collection of trivializations so that the  $U_i$  cover. Write the trivializations as  $\tau_i(e) = (p(e), \phi_i(e))$  as before. Choose a partition of unity  $\{\beta_i | i = 1, \dots, m\}$  subordinate to the  $U_i$ . Then define

$$\Phi: E \to \mathbb{R}^{mk}$$

by the formula

$$\Phi(e) = (\beta_1(p(e))\phi_1(e), \beta_2(p(e))\phi_2(e), \dots, \beta_m(p(e))\phi_m(e)).$$

 $\Phi$  is well defined by the support condition on the partition of unity.  $\Phi$  is linear on each fiber of E as the  $\phi_i$  are.  $\Phi$  is injective on each fiber since for each  $b \in B$ 

there is a  $\beta_i$  with  $\beta_i(b) \neq 0$ . Thus for each point  $b \in B$  we have that  $\Phi^{-1}(p^{-1}(b))$  is a k-plane in  $\mathbb{R}^{mk}$ . So we can now define

$$f: B \to \operatorname{Gr}_k(\mathbb{R}^{mk})$$

by

$$f(b) = \Phi(p^{-1}(b)).$$

*Exercise* 6. Check that this map is smooth. In other words write the map down in charts on the domain and range.

We claim that  $f^*(\gamma_k)$  is isomorphic to E. Consider the map

$$\tilde{\Phi}: E \to B \times \gamma_k$$

given by

$$\tilde{\Phi}(e) = (p(e), (\Phi(p^{-1}(p(e))), \Phi(e))).$$

From the definition of f this maps E to  $f^*(\gamma_k)$ .

Exercise 7. Check that this is an isomorphism.

---

## 11 The embedding manifolds in $\mathbb{R}^N$

**Theorem 11.1.** (The Whitney Embedding Theorem, Easiest Version). Let X be a compact n-manifold. Then X admits a embedding in  $\mathbb{R}^N$ .

*Proof.* First we construct an embedding  $\Phi: X \to \mathbb{R}^N$  for some large N. Let  $\{f_i\}_{i=1}^k$  be a partition of unity so that the support of each  $f_i$  is contained in some coordinate chart  $(U_i, \phi_i)$  so that  $\phi_i(U_i)$  is bounded. Then we can construction smooth functions  $\tilde{\phi}_i: X \to \mathbb{R}^n$  by

$$\tilde{\phi}_i(x) = \begin{cases} f_i(x)\phi_i(x) & \text{if} \quad x \in U_i \\ 0 & \text{if} \quad x \in U_i \end{cases}.$$

Then we can define  $\Phi$  by the equation

$$\Phi(x) = (\tilde{\phi}_1(x), \tilde{\phi}_2(x), \dots, \tilde{\phi}_k(x), f_1(x), f_2(x), \dots, f_k(x)).$$

Then  $\Phi(x) = \Phi(x')$  implies that for some i,  $f_i(x) = f_i(x') \neq 0$  so that  $x, x \in U_i$ . Then for the same i we have

$$\phi_i(x) = \phi_i(x')$$

and hence x = x' since  $\phi_i$  is a diffeomorphism on  $U_i$  and so  $\Phi$  is injective.

Next we need to check that the differential of  $\Phi$  is injective. The differential of  $\Phi$  at x send  $v \in T_x X$  to

$$(D_x f_1(v)\phi_1(x)+f_1(x)D_x\phi_1(v),\ldots,D_x f_k(v)\phi_k(x)+f_k(x)D_x\phi_k(v),D_x f_1(v),\ldots,D_x f_k(v))$$

and the result follows.

---

## Lectures 10 and 11

## 12 Sard's Theorem

An extremely important notion in differential topology is that that of general position or genercity. A particular map may have some horrible pathologies but often a nearby map has much nicer properties.

For example the map

$$f(\theta) = ((\cos(2\theta)\cos(\theta), \cos(2\theta)\sin(\theta), 0).$$

maps the unit circle in the plain to the a figure 8 lying in a plane in  $\mathbb{R}^3$  while the near by map

$$f_{\epsilon}(\theta) = (\cos(2\theta)\cos(\theta), \cos(2\theta)\sin(\theta), \epsilon\cos(\theta)).$$

is an embedding. We will develop a general setting in which we can decide when a nearby map will have some nice property. These ideas have been central in topology since early days of Lagrange, Poincaré and where put into a modern efficient setting by Thom and Smale.

The most basic result we will need is Sard's Theorem. A subset of a manifold is said to have measure zero if its intersection with every chart has measure zero with respect to the Lebesque measure on  $\mathbb{R}^n$ . We will need an easy version of Fubini's theorem.

**Theorem 12.1.** Suppose a measureable  $C \subset \mathbb{R}^n$  has the property that for all  $t \in \mathbb{R}$   $C \cap \{t\} \times \mathbb{R}^{n-1}$  has measure zero. Then C has measure zero.

We will also use the following lemma.

**Lemma 12.2.** If  $C \subset \mathbb{R}^m$  is measureable and  $f : \mathbb{R}^m \to \mathbb{R}^n$  is continuous then f(C) is measureable.

**Theorem 12.3.** Let  $f: M \to N$  be a smooth map of finite dimensional manifolds. Then the set of critical values has measure zero in N.

*Proof.* (Copied from Milnor's little blue book *Topology from the differentiable viewpoint*, this proof does not give the sharp result that a  $C^k$  map with  $k \ge \max\{1, m-n+1\}$  also satisifies the conclusion.) The definition of measure zero is local so it suffices to prove the result in case  $M \subset \mathbb{R}^m$  and  $N \subset \mathbb{R}^n$  are open subsets.

The proof is by induction on m the dimension of the domain. The case m=0 is trivial. Let C=Crit(f) denote the critical set of f. It suffices to prove that for every point  $y \in f(C)$  there is neighborhood of y whose intersection with f(C) has measure zero. Now set

$$C_s = \{x \in M | d_x^j f = 0, \text{ for all } 1 \le j \le k\}$$

Then  $C \supset C_1 \supset C_2 \supset \dots$  is a desceding sequence of closed sets and hence measureable sets. Futhermore the sets  $f(C_s \setminus C_{s+1})$  are all measureable.

The proof has three steps. If  $m \le n$  then you can skip directly to step 3.

Step 1.  $f(C \setminus C_1)$  has measure zero. If  $x \in C \subset C_1$  then there is some first partial which doesn't vanish so assume that

$$\frac{\partial f^1}{\partial x_1}(x) \neq 0.$$

Then we consider the map  $g: \mathbb{R}^m \to \mathbb{R}^m$ .

$$g(x^1, \dots, x^m) = (f^1(x^1, \dots, x^m), x^2, \dots, x^m)$$

Notice that from our assumption

$$d_x g = \begin{bmatrix} \frac{\partial f^1}{\partial x_1}(x) & \frac{\partial f^1}{\partial x_2}(x) & \dots & \frac{\partial f^1}{\partial x_m}(x) \\ 0 & 1 & 0 & \dots & 0 \\ 0 & 0 & 1 & \dots & 0 \\ \vdots & & \ddots & \vdots \\ 0 & 0 & 0 & \dots & 1 \end{bmatrix}$$

which is clearly invertible. The inverse function theorem then provides an inverse,  $h: V \to \mathbb{R}^m$ , on small neighborhood of x Then consider the map  $f \circ h$  we have

$$f \circ h(x^1, \dots, x^m) = (x^1, f^2 \circ h(x^1, \dots, x^m), \dots, f^n \circ h(x^1, \dots, x^m)).$$

So  $f(C \cap h(V)) = f \circ h(h^{-1}(C) \cap V)$ . The inverse image of the set critical  $h^{-1}(C) \cap V$  are simply the critical points of  $f \circ h$ . If we set

$$k_t(x^2, x^3, \dots, x^m) = (f^2 \circ h(t, \dots, x^m), \dots, f^n \circ h(t, \dots, x^m))$$

then

$$h^{-1}(C) \cap V = \bigcup_t \{t\} \times Crit(k_t).$$

By the induction hypothesis we have

$$k_t(Crit(k_t))$$

has measure zero in  $\mathbb{R}^{m-1}$  and hence by Fubini

$$f(C \cap h(V)) = \bigcup_t \{t\} \times k_t(Crit(k_t))$$

has measure zero in  $\mathbb{R}^m$ .

Step 2. Suppose  $x \in C_s \setminus C_{s+1}$ . Then without loss of generality we can assume that there is some s-th order mixed partial derivative so that if we set

$$w = \frac{\partial^{i_1 + \dots + i_m} f}{\partial (x^1)^{i_1} \dots \partial (x^m)^{i_m}}$$

so that

$$\frac{\partial w}{\partial x^1}(x) \neq 0.$$

Define

$$g(x^1, ..., x^m) = (w(x^1, ..., x^m), x^2, ..., x^m).$$

Again this map is a diffeomorphism with inverse  $h: V \to \mathbb{R}^m$  for some neighborhood V of g(x). Let

$$k = f \circ h$$

and let

$$\bar{k} = k|_{\{0\} \times \mathbb{R}^{m-1} \cap V}.$$

Clearly  $g(C_k \cap h(V)) \subset \{0\} \times \mathbb{R}^{m-1} \cap V$  and the critical set of  $\bar{k}$  contains  $g(C_k \cap h(V))$  since it contains  $g(C \cap h(V))$ . Thus

$$f(C_k \cap h(V)) \subset \bar{k}(Crit(\bar{k}))$$

which has measure zero by the induction hypothesis.

Step 3. Suppose that  $x \in C_k$  where  $k+1 > \frac{m}{n}$ . Choose a little cube I of side length  $\delta$ . We have from Taylors theorem and the compactness of I that there is a constant M > 0 so that for all  $y \in I$  and all  $x \in C_k \cap I$ 

$$|| f(x) - f(y) || \le M ||x - y||^{k+1}$$

Subdivide I into  $l^m$  subcubes of side length  $\delta/l$ . By the above estimate if I' is such a subcube containing a point of  $C_k$  then f(I') is contained in a cube of side length at most

$$2M\sqrt{m}(\delta/l)^{k+1}$$

Thus the  $f(C_k \cap I)$  is contained in set of total volume bounded above

$$(2M\sqrt{m}(\delta/l)^{k+1})^n l^m = Cl^{m-n(k+1)}.$$

By our assumption this goes to zero as *l* goes to infinity.

---

## Lecture 12.

## 13 Stratified Spaces

.

**Definition 13.1.** A stratification of a topological space X is a filtraion is a decomposition  $X = \bigcup_{i=0}^{n} S_i$  where each of the  $S_i$  are smooth manifolds (possibily empty) of dimension i and so that

$$\overline{S_k} \setminus S_k \subset \bigcup_{i=0}^{k-1} S_i.$$

The closure  $\overline{S_k}$  is called the stratum of dimension k.

Note that any stratum of a strafied space is a stratified space in its own right. Stratified spaces are useful because many results about smooth manifolds can be extended to stratified spaces. A good example is the space of matrices  $M_{k \times n} l$ . The strata are the matrices of rank bounded above by a fixed number. (assume that  $k \le n$ )

As an application of this result we will compute the low homotopy groups for the Stiefel manifolds,  $\operatorname{St}_k(\mathbb{R}^n)$ . Recall that the Stiefel manifold is the space of k-frames in  $\mathbb{R}^n$ . Given a k-frame  $(v_1, v_2, \ldots, v_k)$  we get an injective linear map  $A: \mathbb{R}^k \to \mathbb{R}^n$  by sending the standard basis vectors  $e_i \to v_i$ . In other words we can identify the Stiefel manifold,  $V_k(\mathbb{R}^n)$ , with the open subset of  $\operatorname{hom}(\mathbb{R}^k, \mathbb{R}^n)$  consisting of injective maps. The compliment of  $V_k(\mathbb{R}^n)$  has a decomposition according to the dimension of the kernel of the map. To codify this set

$$R_l = \{A \in \text{hom}(\mathbb{R}^k, \mathbb{R}^n) | \text{Rank}(A)) = l\}.$$

We claim that in fact these  $R_l$  are submanifolds.

**Proposition 13.2.**  $R_l \subset \text{hom}(\mathbb{R}^k, \mathbb{R}^n)$  is a smooth submanifold of codimension

$$(k-l)(n-l)$$
.

*Proof.* Fix  $A \in S_l$ . Write  $\mathbb{R}^k = \ker(A) \oplus \operatorname{Ran}(A^*)$  and  $\mathbb{R}^n = \ker(A^*) + \operatorname{Ran}(A)$ . Then with respect to this decomposition we can write

$$A = \begin{bmatrix} \bar{A} & 0 \\ 0 & 0 \end{bmatrix}$$

and a nearby matrix as

$$B = A + \begin{bmatrix} \alpha & \beta \\ \gamma & \delta \end{bmatrix}$$

**Lemma 13.3.** If  $\bar{A} + \alpha$  is invertible then a vector (v, w) is in the kernel of B if and only if  $v = -(\bar{A} + \alpha)^{-1}\beta w$  and  $(\delta - \gamma(\bar{A} + \alpha)^{-1}\beta)v = 0$ 

*Proof.* If (v, w) is the kernel of B then

$$(\bar{A} + \alpha)v + \beta w = 0$$

so the first equation is clear. The second equation follows by substituting the first into

$$\gamma v + \delta w = 0$$

The lemma implies that the kernel of *B* is *l*-dimensional if and only if

$$\delta - \gamma (\bar{A} + \alpha)^{-1} \beta = 0$$

The map

$$\begin{bmatrix} \alpha & \beta \\ \gamma & \delta \end{bmatrix} \mapsto \delta - \gamma (\bar{A} + \alpha)^{-1} \beta$$

is clearly a submersion so the preimage of 0, our local model of  $R_l$  is a submanifold of codimension

$$\dim(\ker(A))\dim(\operatorname{Coker}(A)) = (k-l)(n-l).$$

We'll use this to do a simple calculation of homotopy groups.

$$\pi_i(\operatorname{St}_k(\mathbb{R}^n)=0$$

for i < n - k. From its definition  $\operatorname{St}_k(\mathbb{R}^n)$  can be identified with the space of matrices of maximal rank in  $M_{k \times n}$  and so

$$\operatorname{St}_k(\mathbb{R}^n) = M_{k \times n} \setminus (\bigcup_{l=0}^{k-1} R_l)$$

so the problem is to show that a map

$$f: S^i \to \operatorname{St}_k(\mathbb{R}^n)$$

from a sphere of dimension i < n - k is null homotopic. We know that there is a null-homotopy in the larger contractible space of matrices that is to say there is a map

$$h: D^{i+1} \to M_{k \times n}$$
.

so that

$$h|_{S}^{i} = f.$$

If we can find a homotopy  $k: I \times D^{i+1} \to M_{k \times n}$  so that during the homotopy the following two conditions hold.

- 1.  $k|I \times S^i \subset \operatorname{St}_k(\mathbb{R}^n)$
- 2.  $k(\{1\} \times D^{i+1}) \subset \operatorname{St}_k(\mathbb{R}^n)$ .

To see that we can do this we will appeal to Sard's theorem. Lets consider the larger family of maps

$$H: M_{k\times n} \times D^{i+1} \to M_{k\times n}$$

given by

$$H(A, x) = A + h(x).$$

If A is small enough then

$$k(t, x) = H(tA, x) = tA + f(x)$$

satisfies the first condition. To see that we can arrange that the second condition is satisfied we note that H is a submersion. Thus the preimages of the  $R_l$ 's are all submanifolds. Set

$$\tilde{R}_l = H^{-1}(R_l)$$

these are submanifolds of codimension (k-l)(n-l). so they have dimension

$$i + 1 + nk - (k - l)(n - l)$$

Consider the projection  $\tilde{R}_l \to M_{k \times n}$ . Provided that for all  $l \le k-1$ 

$$i + 1 + nk - (k - l)(n - l) < nk$$

then image of the projection has measure zero. The worst case is l=k-1 when the right hand side is

$$i + nk + k - n$$

so that the inequality holds if i < n - k. If  $(A, x) \ni \tilde{R}_l$  that for all  $x f(x) \ni R_l$  completing the proof.

---

## Lecture 13.

## 14 Fiber bundles

The notion of a vector bundle has a natural and useful generalization, that of a fiber bundle. Here is a basic example.

**Example 14.1.** A *k*-frame for  $\mathbb{R}^n$  is a *k*-tuple  $(e_1, \ldots, e_k)$  of linearly independent vectors.

Let  $\operatorname{St}_k(\mathbb{R}^n)$  be the space of all k-frames for  $\mathbb{R}^n$ . This the Stiefel manifold. There is a natural map

$$p: \operatorname{St}_k(\mathbb{R}^n) \to \operatorname{Gr}_k(\mathbb{R}^n)$$

given by sending the k-tuple to  $(v_1, v_2, \ldots, v_k)$  to its span. This map is a submersion and the preimage of small open sets can be given a product structure.

**Definition 14.2.** A (locally trivial) fiber bundle with fiber F is triple (E, B, p) where  $p: E \to B$  is a smooth map so that for all  $b \in B$  in B there is a neighborhood U of b and a diffeomorphism:

$$\tau \colon p^{-1}(U) \to U \times F$$

so that  $p_1 \circ \tau = p$  where  $p_1 \colon U \times F \to U$  is the projection.

In our example let  $U_{\Pi}$  be one of our standard charts and let  $F = \operatorname{Inj}(\mathbb{R}^k, \mathbb{R}^n)$  be the space of injective linear maps. This an open subset of  $\operatorname{hom}(\mathbb{R}^k, \mathbb{R}^n)$  so it is a manifold. We'll define the inverse of the trivialization

$$\tau^{-1}: U_{\Pi} \times F \to p^{-1}(U_{\Pi}).$$

To do this we need to fix an identification of  $\iota \colon \Pi \to \mathbb{R}^k$ . Then

$$\tau^{-1}(\Gamma_A, j) = (A \circ \iota \circ je_1), A \circ \iota \circ j(e_2), \dots, A \circ \iota \circ j(e_k)).$$

where as usual  $A: \Pi \to \Pi^{\perp}$  is a linear transformation and  $\Gamma_A$  is its graph.

For another example consider a real vector bundle  $p: E \to B$ . The projectivization of E, denoted  $\mathbb{P}(E)$  is space of lines in E and has natural projection  $p': \mathbb{P}(E) \to B$  which is a fiber bundle with fiber  $\mathbb{RP}^{n-1}$ .

---

## Lecture 14.

## 15 Whitney's embedding theorem, medium version.

**Theorem 15.1.** (Whitney). Let X be a compact n-manifold. Then M admits a embedding in  $\mathbb{R}^{2n+1}$ .

*Proof.* From Theorem [?] we can assume that M is embedded in  $\mathbb{R}^N$  for some N. To state the next result for a hyperplane  $\Pi \subset \mathbb{R}^N$  let  $p_\Pi \colon \mathbb{R}^N \to \Pi$  denote the orthogonal projection. Note that the set of hyperplanes in  $\mathbb{R}^N$  is a copy of  $\mathbb{RP}^{N-1}$  by associating to each hyperplane the orthogonal line. The desired result follows from:

**Lemma 15.2.** If N > 2n + 1 then for a full measure set of hyperplanes  $\Pi \subset \mathbb{R}^N$  the composition  $p_{\Pi} \circ \Phi$  is a differentiable embedding of M into  $\Pi$ .

*Proof.* Let  $\Delta \subset M \times M$  be the diagonal,  $\Delta = \{(x, x) | x \in M\}$ . Define the map

$$a: M \times M \setminus \Delta \to \mathbb{RP}^{N-1}$$
.

which sends distinct points x and x' to the line through the origin parallel to the line passing through x and x' or equivalently the line through 0 and x - x'. Notice that  $p_{\Pi} \circ \Phi$  is injective if and only if a misses the line orthogonal to  $\Pi$ . If  $2n < \infty$ 

N-1 then any point in the image of a is a critical value and hence by Sard's theorem the image of has measure zero. Thus the set of then the image of a has measure zero and so the set of hyperplane for which the composition is injective is a Baire set.

Next consider the projectivization of the tangent bundle of M,  $\mathbb{P}(TM)$ . This is a fiber bundle over M with fiber  $\mathbb{RP}^{n-1}$ . The total space of the bundle is a smooth manifold of dimension 2n-1. Define the map

$$b: \mathbb{P}(TM) \to \mathbb{RP}^{N-1}$$

which sends a line  $\ell \in T_x M$  to the line  $D_x \Phi(\ell)$  in  $\mathbb{R}^N$ . Notice that the differential of  $p_{\Pi} \circ \Phi$  is injective precisely when the line orthogonal to  $\Pi$  is not in the image of b. If 2n - 1 < N - 1 then as above the image of b has full measure.

Thus the set of good planes is the intersection of two sets of full measure and hence had full measure itself.  $\Box$ 

Notice that the condition on the map b was weaker then the condition on the map a so the proof also proves:

**Proposition 15.3.** *If M is a closed smooth n-manifold then M immerses into*  $\mathbb{R}^{2n}$ .

Proof.

We'll use this theorem to prove the hard version of Whitney's theorem.

---

#### Lecture 15.

# 16 A brief introduction to linear analysis

In a number of place we've talked about the so called infinite dimensional context. In this section we'll introduce briefly the basic notions necessary to discuss this story rigorously. The main application we have in mind is to the

### 16.1 Basic definitions

**Definition 16.1.** A normed vector space is a vector space X (over the real or complex numbers) with a function  $\|\cdot\|: X \to \mathbb{R}_+$  satisfying the usual properties of a norm. A Banach space is a complete normed vector space that is all sequences which are Cauchy with respect to the converge.

Examples.  $C^0(X)$ , the space of continuous functions on a compact metric space is a Banach space with its natural norm. Completeness is the statement that a uniform limit of continuous functions is continuous.

 $C^k(X)$ , the space of k-times continuously differentiable functions on a compact manifold when given the norm

$$||f||_{C^k} = \sup_{x \in X, I \text{ with } \ell(I) \le k} ||\frac{\partial^I f}{\partial x^I}||.$$

where  $I = (i_1, i_2, ..., i_n)$  is a multi-index and  $\ell(I) = \sum_{j=1}^n i_j$ . Completeness follows form the same theorem applied to the derivatives of f.

 $L^p$ -spaces.

Spaces of Hölder continuous functions.

Next we wish to consider functions on normed vector spaces. It turns out that continuity of maps on a normed vector space is equivalent to boundedness. More precisely we have:

**Definition 16.2.** A linear map  $T: X \to Y$  is called bounded if there is a constant  $C \ge 0$  so that for all  $x \in X$  we have

$$||Tx||_Y \leq C||x||_X.$$

Furthermore the smallest such constant C is called the operator norm of T and is denoted ||T||.

**Exercise:**  $T: X \to Y$  is continuous if and only T is bounded.

A basic fact of life is that every normed vector space sits in canonical fashion in a Banach space.

**Theorem 16.3.** To each normed vector space X there corresponds a unique Banach space  $\overline{X}$  called the completion of X and a unique injective map continuous linear map  $X \to \overline{X}$  satisfying the following universal property. If  $T: X \to Y$  is a continuous linear map then there is a unique continuous linear map  $\overline{T}: \overline{X} \to \overline{Y}$  so that the operator norm of T and  $\overline{T}$  agree.

For proof see for example Royden's text. In practice the significance of this theorem is that we will consider various norms on  $C_0^{\infty}(\mathbb{R}^n)$  and take the completions with respect to these norms. To check if maps between these completions are continuous it suffices to check that the map is bounded on  $C_0^{\infty}$  with respect to the norms in question.

**Definition 16.4.** Let  $\mathcal{B}(X, Y)$  denote the space of bounded linear operators from X to Y.

 $\mathcal{B}(X,Y)$  is Banach space in its own right. In fact it is a Banach algebra (i.e. a Banach space with the structure of an algebra so that for  $x, y \in X$  we have  $||xy|| \le ||x|| ||y||$ .

#### 16.1.1 The three pillar's of linear analysis

You can look in any book on Functional analysis for this material. Its also in Abraham-Marsden and Ratiu.

**Theorem 16.5.** The Hahn-Banach theorem Let X be a linear space over  $\mathbb{F} = \mathbb{R}$  or  $\mathbb{C}$  and  $p: X \to \mathbb{R}$  be a map satisfying

- 1. For all  $x, y \in X \ p(x + y) \le p(x) + p(y)$
- 2. For all  $\lambda \in \mathbb{F}$  and all  $x \in X$  we have  $p(\lambda x) = |\lambda| p(x)$ .

Let  $Z \subset X$  be a linear subspace and  $\rho : Z \to \mathbb{F}$  be a linear functional. If for all  $z \in Z$  we have  $|\rho(z)| \le p(z)$  then there is a linear functional  $\tilde{\rho} : X \to \mathbb{F}$  which extends  $\rho$  and satisfies  $|\tilde{\rho}(x)| \le p(x)$  for all  $x \in X$ .

The proof goes by a Zorn's lemma argument considering all possible extensions with the given property. One shows that this is a partially ordered set and any extension which is not defined on the whole space has a nontrivial extension.

This has one corollary that we will need later.

**Corollary 16.6.** Let X be a Banach space and  $F \subset B$  a finite dimensional subspace. Then F has closed complementary subspace. (i.e., there is a closed subspace  $C \subset B$  so that  $F \cap C = \{0\}$  and F + C = B.

Proof. Take a basis  $\{f_1, \ldots, f\}n\}$  for F. Let  $\phi_1, \ldots, \phi_n$  be the corresponding dual basis of  $F^*$ . Clearly the  $\phi_i$  satisfy the hypothesis of the Hahn-Banach theorem with p being a multiple of the norm. So there are linear functionals  $\tilde{\phi}_1, \ldots, \tilde{\phi}_n$  extending these. Set  $C = \bigcap_{i=1}^n \ker(\tilde{\phi}_i)$ .

**Theorem 16.7. The Open mapping theorem** Any surjective bounded linear mapping  $T: X \to Y$  is an open mapping, that is it takes open sets to open sets.

The proof of this theorem is an application of the Baire category theorem. An important corollary is the Banach isomorphism theorem.

**Theorem 16.8. The Banach isomorphism theorem** A bounded linear map  $T: X \rightarrow Y$  which is an isomorphism of vector spaces is a topological isomorphism.

*Proof.* At issue is show that  $T^{-1}$  which exists as a map of sets is continuous. So we must show for all  $U \subset X$  open that  $(T^{-1})^{-1}(U) = T(U)$  is open. T is surjective so this following from the open mapping theorem.

**Theorem 16.9. The closed graph theorem** A linear operator  $T: X \to Y$  is bounded if and only if its graph  $\Gamma_T = \{(x, Tx) | x \in X \| \subset X \times Y \text{ is closed.} \}$ 

## 16.2 Compact operators

In this subsubsection *X* and *Y* will denote Banach spaces.

**Definition 16.10.** A linear operator  $T: X \to Y$  is called a compact operator the image under T of the unit ball in X has compact closure in Y.

*Remark* 2. Compact operators are sometime called completely continuous.

The prototypical compact operator is the following Let X and Y be the space  $\ell^2$  of all sequences  $a=(a_1,a_2,\ldots)$  so that  $\sum_{i=1}^{\infty}(a_i)^2\leq\infty$  and define

$$T(a_1, a_2, \ldots) = (a_1, a_2/2, a_3/3, \ldots, a_n/n, \ldots)$$

To see that T is compact choose a sequence  $a^i$  in  $B_1$  the ball of radius one. By a diagonal argument we can pass to a subsequence where components of  $a^i$  converge to some  $a^{\infty}$ . Then we claim that  $T(a^i)$  converges in  $\ell^2$ . Choose  $\epsilon > 0$ . Then choose  $i_0 > 0$  so that the following hold.

1. 
$$\frac{1}{i_0} < \epsilon/2$$

2. 
$$(\sum_{n=1}^{i_0-1} |a_n^i - a_n^{\infty}|^2)^{\frac{1}{2}} \le \epsilon/2$$
.

The last follows from the component-wise convergence. Then we have for  $i \ge i_0$ 

$$||T(a^{i}) - T(a^{\infty})||^{2} \leq \sum_{n=1}^{i_{0}-1} \frac{1}{i^{2}} |a_{n}^{i} - a_{n}^{\infty}|^{2} + (\sum_{n=i_{0}}^{\infty} \frac{1}{i^{2}} |a_{n}^{i} - (a_{n}^{\infty})^{2}|)^{\frac{1}{2}}$$

$$\leq \epsilon^{2}/4 + \frac{1}{i_{0}^{2}} \sum_{n=i_{0}}^{\infty} |a_{n}^{i} - a_{n}^{\infty}|^{2}$$

$$\leq \epsilon^{2}/4 + \epsilon^{2}/4 = \epsilon^{2}/2.$$

The basic result that we will need is Arzela-Ascoli theorem. Let B be a ball in  $\mathbb{R}^n$ . Recall we call a subset  $A \in C^0(B)$  equicontinuous if for all  $\epsilon > 0$  there is a  $\delta > 0$  so that if  $|x - y| < \delta$  then  $|f(x) - f(y)| < \epsilon$  for all  $f \in A$ .

**Theorem 16.11.** (Arzela-Ascoli). A subset  $A \in C^0(B)$  has compact closure in  $C^0(B)$  if and only if A is bounded and equicontinuous.

This has an immediate corollary:

**Corollary 16.12.** The embedding  $C^1(B) \to C^0(B)$  is compact.

*Proof.* The unit ball in  $C^{0,\alpha}(B)$  is certainly bounded in  $C^0(B)$ . If  $||f||_{C^{0,\alpha}} \le 1$  then  $|f(x) - f(y)| \le |x - y|$  we can take  $\delta = \epsilon$ .

---

## 16.3 Fredholm Operators

A nice way to think about compact operators is to show that set of compact operators is the closure of the set of finite rank operator in operator norm. In this sense compact operator are similar to the finite dimensional case. One property of finite rank operators that does not generalize to this setting is theorem from linear algebra that if  $T: X \to Y$  is a linear transformation of finite dimensional vector spaces then

$$\dim(\ker(T)) - \dim(\operatorname{Coker}(T)) = \dim(X) - \dim(Y).$$

Of course if *X* or *Y* is infinite dimensional then the right hand side of equality does not make sense however the stability property that the equality implies could be generalized. This brings us to the study of Fredholm operators. It turns out that many of the operators arising naturally in geometry, the Laplacian, the Dirac operator etc give rise to Fredholm operators. The following is mainly from Hörmander

**Definition 16.13.** Let X and Y be Banach spaces and let  $T: X \to Y$  be a bounded linear operator. T is said to be *Fredholm* if the following hold.

- 1. ker(T) is finite dimensional.
- 2. Ran(T) is closed.
- 3. Coker(T) is finite dimensional.

If *T* is Fredholm define the *index* of *T* denoted Ind(T) to be the number dim(ker(T)) - dim(Coker(T))

First let us show that the closed range condition is redundant.

**Lemma 16.14.** Let  $T: X \to Y$  be a operator so that the range admits a closed complementary subspace. Then the range of T is closed.

Proof: C be a closed complement for the range. We can assume that T is injective since  $\ker(T)$  is a closed subspace and hence  $X/\ker(T)$  is a Banach space so we can replace T by the induced map from this quotient. Now consider the map  $S: X \oplus C \to Y$  defined by

$$S(x,c) = T(x) + c.$$

S is bounded linear isomorphism and hence by the open mapping theorem S is a topological isomorphism. Thus  $Ran(T) = S(X \oplus \{0\})$  is closed.

An important result that will be used over and over again is the openness of invertibility in the operator norm.

**Theorem 16.15.** If  $T: X \to Y$  is a bounded invertible operator then for all  $p: X \to Y$  with sufficiently small norm T + p is also invertible.

*Proof.* Without loss of generality we can assume X = Y and T = I. Then if the norm of p is sufficiently small the Neumann series

$$\sum_{i=1}^{\infty} (-p)^i$$

converges to the inverse of I + p.

We begin with some lemma's

**Lemma 16.16.** (F. Riesz) *The unit ball B in a Banach space X is compact if and only if B is finite dimensional.* 

*Proof.* See Kerszig Lemma 2.5-4. This is easy for Hilbert spaces but takes a little care for Banach spaces.  $\Box$ 

## **Lemma 16.17.** *The following are equivalent:*

- 1. ker(T)) is finite dimensional and Ran(T) is closed.
- 2. Every bounded sequence  $\{x_i\} \subset X$  with  $Tx_i$  convergent has a convergent subsequence.

Proof: Suppose that 1 holds. Since  $\ker(T)$  is finite dimensional it admits a closed compliment C. Since  $\operatorname{Ran}(T)$  is closed it is a Banach space so the Banach isomorphism theorem implies  $T|_C \colon C \to \operatorname{Ran}(T)$  is an isomorphism and the result follows. Now suppose that 2 holds. Then a bounded sequence in the kernel has a convergent subsequence so the kernel is finite dimensional. That  $\operatorname{Ran}(T)$  is closed follows immediately from 2.

Let Fred(X, Y) denote the space of Fredholm operators between X and Y. Also let Fred(X) be the set of Fredholm operators on X

**Lemma 16.18.** Fred(X, Y) is a open subset of  $\mathcal{B}(X, Y)$  and the index is a locally constant function on Fred(X, Y).

*Proof.* Let  $T: X \to Y$  be a Fredholm operator and let  $p: X \to Y$  be an operator with small norm. We can write  $X = C + \ker(T)$  and  $Y = \operatorname{Ran}(T) + D$ . With respect to this decomposition we can write T as a matrix

$$T = \left[ \begin{array}{cc} T' & 0 \\ 0 & 0 \end{array} \right].$$

and p as the matrix

$$p = \begin{bmatrix} a & b \\ c & d \end{bmatrix}.$$

We prove the result by reduction to the finite dimensional situation. In fact we'll prove

**Lemma 16.19.** For p sufficiently small there is a linear transformation  $A : \ker(T) \to \operatorname{Coker}(T)$  so that

$$\ker(T + p) \equiv \ker(A)$$
 and  $\operatorname{Coker}(T + p) \equiv \operatorname{Coker}(A)$ .

In fact the norm of p is small enough then T + a will be invertible and if we set

$$G = \begin{bmatrix} I & -(T'+a)^{-1}b \\ 0 & I \end{bmatrix} \text{ and } H = \begin{bmatrix} I & 0 \\ -c(T'+a)^{-1} & I \end{bmatrix}$$
 (7)

then

$$H(T+p)G = \begin{bmatrix} T'+a & 0\\ 0 & -c(T'+a)^{-1}b+d \end{bmatrix}.$$

The lemma follows immediately from this taking  $A = -c(T+a)^{-1}b + d$ .  $\Box$ 

The proof of the lemma proved the following conceptually useful result

**Lemma 16.20.** Let  $T: X \to Y$  be a Fredholm map and  $p: X \to Y$  a linear map. If p has sufficiently small norm then there are isomorphisms  $i: X' \oplus K \to X$  and  $j: Y \to X' \oplus C$  so that

$$j \circ (T+p) \circ i = \begin{bmatrix} I & 0 \\ 0 & q \end{bmatrix}.$$

for some linear map  $q: K \to C$ .

We'll also need the notion of the adjoint of an operator. If X is a Banach space the dual space of X is the space of all bounded linear functionals on X and is denoted  $X^*$ . Given a bounded linear operator  $T: X \to Y$  we have get a linear operator

$$T^* \colon Y^* \to X^*$$

by declaring that for  $\rho \in Y^*$ ,  $T^*(\rho)$  is the linear functional so which send x to

$$\rho(T(x)).$$

First we give the dual characterization of the norm.

## **Lemma 16.21.** For all $x \in X$

$$||x|| = \sup_{\|\rho\|=1} (|\rho(x)|)$$

*Proof.* Fix  $x_0 \in X$  Certainly  $|\rho(x_0)| \le ||\rho|| ||x_0||$  so

$$||x_0|| \ge \sup_{\|\rho\|=1} (|\rho(x_0)|)$$

Define a linear functional  $\lambda$ : span $(x_0) \to \mathbb{R}$  by  $\lambda(x_0) = \|x_0\|$  and extending by linearity to the span. Applying the Hahn-Banach theorem to  $\lambda$  and the subadditive function  $p(x) = \|x\|$  implies the existence of an extension of  $\lambda$  to the whole of X with

$$|\lambda(x)| \le ||x||$$

**Lemma 16.22.** If T is bounded then  $T^*$  is bounded with the same norm

Proof.

$$||T|| = \sup_{\substack{x \mid ||x|| \le 1}} ||Tx||$$

$$= \sup_{\substack{x \mid ||x|| \le 1}} ||\sup_{\rho \mid ||\rho|| \le 1} \rho(Tx)|$$

$$= \sup_{\substack{\rho \mid ||\rho|| \le 1}} \sup_{x \mid ||x|| \le 1} ||\rho(Tx)||$$

$$= \sup_{\substack{\rho \mid ||\rho|| \le 1}} ||T^*(\rho)||$$

$$= ||T^*||.$$

We'll need the relationship between the cokernel of T and the kernel of  $T^*$ .

**Lemma 16.23.** *If T has closed range then* 

$$\operatorname{Coker}(T)^* \equiv \ker(T^*).$$

*Proof.* There is a natural map  $\ker(T^*) \to \operatorname{Coker}(T)^*$  by sending  $\rho \in \ker(T^*)$  to the linear functional  $\lambda \in \operatorname{Coker}(T)^*$  where  $\lambda(y+TX)=\rho(y)$ . This well defined since for all  $x \in X$  we have  $\rho(Tx)=T^*(\rho)(x)=0$ . Since  $\operatorname{Ran}(T)$  is closed,  $\operatorname{Coker}(T)=Y/\operatorname{Ran}(T)$  is a Banach space. Given a linear functional  $\lambda \in \operatorname{Coker}(T)^*$  so  $\lambda \colon Y/\operatorname{Ran}(T) \to \mathbb{R}$  and hence defines a bounded linear functional

$$\rho: Y \to Y/\text{Ran}(T) \to \mathbb{R}$$
.

Now  $(T^*\rho)(x) = \rho(T(x)) = 0$ . It is easy to check that this inverts the previous construction.

Next we observe that compactness is preserved under taking adjoints.

**Lemma 16.24.** Let  $K: X \to Y$  be compact then  $K^*: Y^* \to X^*$  is compact.

*Proof.* This takes a little work. See for example Kreszig *Introductory functional* analysis with applications Theorem 8.2-5.  $\Box$ 

**Lemma 16.25.** Let  $K: X \to X$  be a compact operator. Then I + K is Fredholm.

Proof: First we coincide the kernel of I + K. Let B be the unit ball in  $\ker(I + K)$ . Then B = K(B) so B is image of a bounded set under a compact operator hence is precompact. But B is closed so B is compact. By Riesz's lemma  $\ker(I + K)$  is finite dimensional. Next we show that  $\operatorname{Ran}(I + K)$  is closed. By lemma 16.17 it suffices to show that if  $x_i$  is a bounded sequence so that  $x_i + K_i x_i$  converges to  $y \in Y$  then there is  $x \in X$  so that x + Kx = y. Since  $\{x_i\}$  is bounded there is a subsequence  $x_{i_j}$  so that  $\{Kx_{i_j}\}$  converges. But then  $\{x_{i_j}\}$  converges. Thus the operator I + K is a semi-Fredholm. Applying the same argument to the adjoint  $I + K^*$  completes the proof.

Next we give a useful characterization of Fredholm operators.

**Theorem 16.26.**  $T: X \to Y$  is Fredholm if and only this a bounded linear operator  $R: Y \to X$  so that

$$RT - I$$
 and  $TR - I$ 

are compact operators.

*Proof.* If T is Fredholm then as before we can write

$$X = X' \oplus \ker(T)$$
 and  $Y = \operatorname{Ran}(T) \oplus C$ 

for closed subspaces  $X' \subset X$  and  $C \subset Y$ .  $T|_{X'} \colon X' \to \operatorname{Ran}(T)$  is an isomorphism so it has and inverse  $\tilde{R}$ . Extending  $\tilde{R}$  to a map  $Y \to X$  using the direct sum decomposition gives the required map.

If R exists  $\ker(T)$  is finite dimensional from the equation RT = I + K.  $\operatorname{Ran}(T)$  is finite dimensional from the equation TR = I + K' and the operator is Fredholm.

Next we consider the composition of Fredholm operators.

**Lemma 16.27.** Let  $T: X \to Y$  and  $S: Y \to Z$  be Fredholm operators. Then  $ST: X \to Z$  is Fredholm. Furthermore  $\operatorname{Ind}(ST) = \operatorname{Ind}(T) + \operatorname{Ind}(S)$ .

Proof: Since  $(ST)^{-1}(0) = T^{-1}(S^{-1}(0))$  we have  $\dim(\ker(ST)) \le \dim(\ker(S)) + \dim(\ker(T))$ . Similarly  $\dim(\operatorname{Coker}(ST)) \le \dim(\operatorname{Coker}(S)) + \dim(\operatorname{Coker}(T))$  so the composition is Fredholm.

Next we consider the index assertion. To this end consider the family of operators  $A_t: Y \oplus X \to Z \oplus X$  defined by the equation

$$A_{t} = \begin{bmatrix} cos(t)S & -sin(t)ST \\ sin(t)I & cos(t)T \end{bmatrix}$$

for  $0 \le t \le 1$ . We claim that  $A_t$  is a continuous family of Fredholm operators. But

$$A_t = \begin{bmatrix} S & 0 \\ 0 & I \end{bmatrix} \begin{bmatrix} cos(t)I & -sin(t)I \\ sin(t)I & cos(t)I \end{bmatrix} \begin{bmatrix} I & 0 \\ 0 & T \end{bmatrix}.$$

So  $A_t$  is the composition of Fredholm operators and hence is Fredholm. Clearly  $Ind(A_0) = Ind(T) + Ind(S)$  and  $Ind(A_{\pi}) = Ind(ST)$ .

---

## Lecture 18 and 19

## 17 Smale's Sard theorem

In the early sixties Smales realized that many of the ideas of differential topology can be applied to aid in the study of PDEs and as part of this program he showed how to generalize Sard's theorem to the infinite dimensional case. First we need to introduce the correct kind of mappings of Banach manifolds.

**Definition 17.1.** Let X and Y be Banach manifolds and  $f: X \to Y$  a smooth map. We say that f is a Fredholm mapping if for all  $x \in X$  the differential

$$d_x f: T_x X \to T_{f(x)} Y$$

is a Fredholm map

The first problem we run into with trying generalize Sard's theorem is that the notion of measure zero isn't easy to make sense of in an infinite dimensional space however the the complement of a (closed) set of measure zero is an open dense set. The critical set of a map is closed so the image is at worst a countable union of closed sets of measure zero. The complement is a countable intersection of open dense sets. This notion makes sense in an arbitrary topological space. In particular Banach manifold which satisfies the Baire category theorem so such a set is non-empty.

**Definition 17.2.** Let X be topological space. A set  $A \subset X$  is called residual it is a countable intersection of open dense sets.

Thus the Baire category theorem says that a residual subset of a metric space is dense.

Smale's generalization of Sard's theorem is

**Theorem 17.3.** Let  $f: X \to Y$  be a smooth mapping of second countable Banach manifolds. Then the set of regular values of f is residual in Y.

To prove this result we prove a result of independent interest which says that after a change of coordinates a nonlinear Fredholm mapping differs from an linear isomorphism by a nonlinear map between finite dimensional manifolds. We have a kind of analogue of Lemma ??

**Lemma 17.4.** Let  $f: X \to Y$  be a Fredholm map. Then for any  $x \in X$  there are coordinate charts  $\phi: U \subset X \to B \oplus K \to \text{and } \psi: V \subset Y \to B \oplus C$  so that

$$\psi \circ f \circ \phi^{-1}(x,k) = (x,g(x,k)).$$

*Proof.* This is a local result so we may assume without loss of generality that x is the origin in  $\bar{U} \subset X \to B \oplus K$  and that f(x) is the origin in  $\bar{V} \subset Y \to B \oplus C$  where B is a Banach space,  $K = \ker(d_x f)$ , and  $C = \operatorname{Coker}(d_x f)$ . We can also

arrange that  $0 \oplus K$  is the kernel of  $d_{(0,0)}f$  and that  $B \oplus \{0\}$  is complement for the range of  $d_{(0,0)}f$  and finally that

$$d_{(0,0)}f = \begin{bmatrix} I & 0 \\ 0 & 0 \end{bmatrix}$$

Write

$$f(x,k) = (a(x,k), b(x,k)).$$

As in the proof of the implicit function theorem consider the map

$$h:U\to B\oplus K$$

given by

$$h(x,k) = (a(x,k),k).$$

Then the differential of h at (0,0) is the identity so there is a map q inverting h near the origin. Notice that

$$f \circ q(x, k) = (x, g(x, k))$$

as required.  $\Box$ 

*Remark* 3. This lemma has a very important consequence. Point preimages of Fredholm mappings are locally homeomorphic to the point preimage of a smooth map between finite dimensional manifolds. This the beginning of Kuranishi's work in deformation theory for complex manifolds. Kuranshi and Smale where contemporaries at Columbia in the early sixties.

We need one more technical lemma.

**Definition 17.5.** A map  $f: X \to Y$  is said to be locally closed if for all  $x \in X$  there is a neighborhood U of x so that  $f|\bar{U}: \bar{U}toY$  is a closed map.

Any continuous map from a locally compact space is locally closed. Banach spaces a locally compact if and only if they are finite dimensional.

**Lemma 17.6.** A Fredholm map  $f: X \to Y$  is locally closed.

*Proof.* Choose charts as guaranteed by Lemma 17.4 so that we can assume our map has the form

$$f(x,k) = (x, g(x,k))$$

If  $A \subset U \subset B \times K$  is closed we must show that f(A) is closed. Let  $(x_i, c_i)$  be a sequence in f(A) converging to (x, c). Then  $c_i = g(x_i, y_i)$  for some sequence  $y_i$ . Since the  $y_i$  are bounded in finite dimensional vector space we can assume that  $y_i$  converge. Then clearly (x, c) will be in f(A).

We are now ready to prove Smale's Sard theorem.

*Proof.* Let  $f: X \to Y$  be our Fredholm map. Since X is second countable it is enough to show that there is a covering of X by open sets U so that the regular values of  $f|_U$  are residual. In fact we will show that we can find U so that the regular values of  $f|_U$  are open and dense. Since f is locally closed and the since the critical point set of f is closed there in no problem in choosing U the regular values of  $f|_U$  is an open set. Now choose charts about the point in question so that the local representative of f has the form guaranteed by Lemma 17.4. The differential of local representative of f has the form

$$\begin{bmatrix} I & 0 \\ * & d_{(x,k)}g|_K \end{bmatrix}$$

so that  $d_{(x,k)}f$  is surjective if and only if  $d_{(x,k)}g|_K$  is surjective in other words (x,c) is a regular value for  $f|_U$  if and only if c is a regular value of  $k\mapsto g(x,k)$  for k in a suitable neighborhood. Thus the intersection of  $\mathcal{R}(f|_U)$  with each slice  $\{x\}\times C\cap V$  is dense and hence  $\mathcal{R}(f|_U)$  is dense.

---

## Lecture 20.

## 18 Parametric transversality

An important tool in differential topology is the notion of transversality.

**Definition 18.1.**  $f: M \to N$  is said to be transversal to  $Z \subset N$  if for all  $m \in M$  we have

$$d_m f(T_m M) + T_{f(m)} Z = T_{f(m)} N.$$

This is sometimes written  $f \square Z$ .

**Lemma 18.2.** If  $f: M \to N$  is transverse to Z then the preimage  $f^{-1}(Z)$  is a smooth submanifold of dimension

$$\dim(M) - \dim(N) + \dim(Z)$$
.

*Proof.* Let  $x \in f^{-1}(Z)$  and choose charts  $(U, \phi)$  about x and  $(V, \phi)$  about  $f(x) \in Z$ . We can choose  $(V, \phi)$  so that  $\psi(f(x)) = 0$  and  $\psi(V \cap Z) \subset \mathbb{R}^z \times \{0\} \subset \mathbb{R}^n$ . Let  $p \colon \mathbb{R}^n \to \mathbb{R}^{n-z}$  be the projection. Define  $g \colon U \to \mathbb{R}^{n-z}$  by  $g(x) = p \circ \psi \circ f|_{U}(x)$ . Then the condition that f is travsversal to Z implies that the origin a regular value of g and hence  $g^{-1}(0) = Z \cap U$  is a submanifold.  $\square$ 

Remark 4. Often one can make cleaner statements by introducing the notion of codimension. If  $Z \subset N$  is a submanifold we define  $\operatorname{codim}(Z) = \dim(N) - \dim(Z)$ . It is the number of equations required to cut out Z locally. In the above theorem the codimension of Z and  $f^{-1}(Z)$  are the same. (They are each cut out by the same number of equations!)

Our aim is to show that the condition of being transversal is generic in the sense of Sard's theorem. As a model for what we wish to prove consider the following situation.

Let

$$F: P \times M \rightarrow N$$

be a smooth map.

**Theorem 18.3.** Suppose that F is a submersion, i.e. the differential of F is surjective everywhere. Suppose further that P, M and N are finite dimensional. Then for each  $p \in P$  we get a map  $f_p \colon M \to N$ . Given a submanifold Z of N t for a generic  $p \in P$  we have  $f_p$  is transversal to Z.

*Proof.* Since F is a submersion F is transversal to Z so that  $S = F^{-1}(Z) \subset P \times M$  is a submanifold. Consider the projection

$$p_1: S \to P$$
.

Fix  $(p, m) \in S$  and set n = F(p, m) The tangent space of S at (p, m) is  $(v, w) \in T_{(p,m)}M$  so that  $d_{(p,m)}F(v, w) \in T_nZ$  or equivalently

$$d_m f_p(w) + d_{(p,m)} F(v,0) \in T_n Z.$$

We claim that p is a regular value of the projection if and only if  $f_p$  is transverse to Z. This follows from

**Lemma 18.4.**  $S = F^{-1}(Z)$  is transverse to  $\{p\} \times M$  if and only if  $f_p$  is transverse to Z.

*Proof.* The first condition is

$$0 \oplus T_m M + (d_{n,m} F)^{-1} (T_n Z) = T_n P \oplus T_m M$$

The second condition is

$$d_{p,m}F(0 \oplus T_mM) + T_nZ = T_nN.$$

Since F is surjective these condition are equivalent.

Next we observe that the condition S is transverse to  $\{p\} \times M$  is equivalent to the condition that p is regular value of the projection  $p_1|_S: S \to P$ . The first condition is

$$0 \oplus T_m M + (d_{p,m} F)^{-1} (T_n Z) = T_p P \oplus T_m M$$

while the second is

$$d_{p,m}p_1:(d_{p,m}F)^{-1}(T_nZ)=T_pP.$$

Since  $0 \oplus T_m M$  is the kernel of  $d_{p,m} p_1$  is  $0 \oplus T_m M$  these conditions are equivalent. Thus we can appeal to Sard's theorem applied to the projection  $p_1 \colon S \to P$  to say that a generic  $p \in P$  is a regular value and by the lemma for generic  $p \in P$ ,  $f_p$  is transverse to Z.

**Theorem 18.5.** Suppose that F is a submersion, i.e. the differential of F is surjective everywhere. Suppose further that P, M and N are Banach manifolds for each  $p \in P$  we get the map  $f_p \colon M \to N$  is Fredholm. Given a finite dimensional submanifold Z of N then for a residual set of  $p \in P$  we have  $f_p$  is transversal to Z.

*Proof.* We simply need to check the map  $p_1|_S: S \to P$  is Fredholm. To this end we need to inspect the proofs of the two lemmas above. We can sharpen them to the following.

**Lemma 18.6.** There an isomorphism

$$T_p P \oplus T_m M / (0 \oplus T_m M + (d_{p,m} F)^{-1} (T_n Z) \to T_n N / d_{p,m} F (0 \oplus T_m M) + T_n Z$$

*Proof.* Differential of F induces a map which is easily seen to be an isomorphism using the fact that F is a submersion.

$$d_{p,m}p_1:(d_{p,m}F)^{-1}(T_nZ)=T_pP.$$

Lemma 18.7. There an isomorphism

$$T_p P \oplus T_m M/(0 \oplus T_m M + (d_{p,m} F)^{-1} (T_n Z) \to T_p P/d_{p,m} p_1 : (d_{p,m} F)^{-1} (T_n Z)$$

*Proof.* Now the differential of  $p_1$  induces the desired map which is easily seen to be an isomorphism using the fact that  $p_1$  is a submersion.

These two lemmas tell us that the cokernel of  $p_1|_S$  is finite dimensional.

The kernel of the projection  $p_1|S$  is the intersection  $(0 \oplus T_m M \cap (d_{p,m}F)^{-1}(T_nZ)$ . This intersection Fits into a short exact sequence

$$0 \to \ker(d_m f_p) \to (0 \oplus T_m M \cap (d_{p,m} F)^{-1}(T_n Z) \to T_n Z \to 0.$$

and hence is finite dimensional.

The main application we will have of this result is the following result.

**Theorem 18.8.** Let M, N, and Z be smooth manifolds with  $Z \subset N$  a submanifold. The set of maps  $f: M \to N$  in  $C^k(M, N)$  which are transverse to Z is residual in  $C^k(M, N)$ .

A little later in the course we will deal with giving  $C^k(M, N)$  the structure of a Banach manifold.

---

## Lectures 21 and 22.

## 19 The Strong Whitney Embedding Theorem

Whitney proved a stronger version of this theorem.

**Theorem 19.1.** (Whitney 1944) Any compact n-manifold admits an embedding into  $\mathbb{R}^{2n}$ .

*Proof.* (Sketch). We will work out the case n is even and n > 2 and M orientable first. Consider the space Imm of  $C^k$ -immersions of  $M \to \mathbb{R}^{2n}$ . The condition of being an immersion is an open condition in the  $C^k$ -topology on the space of maps so that Imm is a Banach manifold. By Proposition 15.3 proposition this space is non-empty. First we will show that for a Baire set of immersions the there are only finitely many double points and that the two sheets of image are transverse at the double points.

To this end consider the map

$$F: Imm \times (M \times M \setminus \Delta) \to Gr_n(\mathbb{R}^{2n}) \times Gr_n(\mathbb{R}^{2n}) \times \mathbb{R}^{2n}$$
.

given by  $F(f, x, y) = (\operatorname{Im}(D_x f), \operatorname{Im}(D_y f), f(x) - f(x')$ . One checks that F is a submersion. Let  $Z_i \subset \operatorname{Gr}_n(\mathbb{R}^{2n}) \times \operatorname{Gr}_n(\mathbb{R}^{2n})$  be the set of pairs  $(\Pi_1, \Pi_2)$  so that  $\dim(\Pi_1 \cap \Pi_2) = i$ .

**Lemma 19.2.**  $Z_i$  is a smooth submanifold of dimension  $2n^2 - i^2$ .

*Proof.* Write  $\mathbb{R}^{2n}$  as

$$\Pi_1 \cap \Pi_2 \oplus \Pi_1 \cap \Pi_2^{\perp} \oplus \Pi_1^{\perp} \cap \Pi_2 \oplus \Pi_1 \cap \Pi_2^{\perp}$$

The standard coordinate chart about  $\Pi_1$  represents a plane near  $\Pi_1$  as the graph of a linear map  $A_1:\Pi_1\to\Pi_1^\perp$  decomposing this matrix according the to the above deomposition we can write

$$A_1 = \begin{bmatrix} \alpha_1 & \beta_1 \\ \gamma_1 & \delta_1 \end{bmatrix}$$

viewed as a map

$$\Pi_1 \cap \Pi_2 \oplus \Pi_1 \cap \Pi_2^{\perp} \to \Pi_1^{\perp} \cap \Pi_2^{\perp} \oplus \Pi_1^{\perp} \cap \Pi_2$$

Doing the same of a chart about  $\Pi_2$  we get

$$A_2 = \begin{bmatrix} \alpha_2 & \beta_2 \\ \gamma_2 & \delta_2 \end{bmatrix}$$

now viewed as a map

$$\Pi_1 \cap \Pi_2 \oplus \Pi_1^{\perp} \cap \Pi_2 \rightarrow \Pi_1^{\perp} \cap \Pi_2^{\perp} \oplus \Pi_1 \cap \Pi_2^{\perp}$$

The condition that the planes represented by  $(A_1, A_2)$  also intersect in an *i*-dimensional subspace is the condition that  $\alpha_1 = \alpha_2$  so the total dimension is  $2n^2 - i^2$ 

We seek a map f so that for all distinct  $x, y \in M$   $F(f, x, y) \notin Z_i \times \{0\}$  for any i. The parametric transversality theorem implies that for a Baire set of f the map  $(x, y) \mapsto F(f, x, y)$  is transverse to  $Z_i \times \{0\}$ . But the codimension of  $Z_i \times \{0\}$  is  $2n^2 + 2n - (2n^2 - i^2) = i^2 + 2n$  which is larger than the dimension of the domain 2n.

Exercise 8. Show that we can in addition assume that f has no triple points.

Thus whenever f(x) = f(y) we have that the differentials have transverse images at those points. We assume that in the remainder of the discussion that f has been chosen satisfy these conditions.

**Lemma 19.3.** At each pair (x, x') with f(x) = f(x') = y there are charts  $(U, \phi)$ ,  $(U', \phi')$  near x, x' and  $(V, \psi)$  near y so that

$$\psi^{-1} \circ f \circ \phi(x_1, x_2, \dots, x_n) = (x_1, x_2, \dots, x_n, 0, 0, \dots, 0)$$

and

$$\psi^{-1} \circ f \circ \phi'(x_1', x_2', \dots, x_n') = (0, 0, \dots, 0, x_1', x_2', \dots, x_n')$$

*Proof.* Since f is an immersion there are coordinates  $\phi = (x_1, \dots, x_n)$  about x and  $\psi_1(y_1, \dots, y_{2n})$  about y so that

$$\psi_1^{-1} \circ f \circ \phi(x_1, x_2, \dots, x_n) = (x_1, x_2, \dots, x_n, 0, 0, \dots, 0)$$

and coordinates  $\phi' = (x_1', \dots, x_n')$  about x' and  $\psi_2 = (y_1', \dots, y_{2n}')$  about y so that

$$\psi_2^{-1} \circ f \circ \phi(x_1', x_2', \dots, x_n') = (0, 0, \dots, 0, x_1', x_2', \dots, x_n')$$

Then set  $\psi = (y_1, \dots, y_n, y'_{n+1}, \dots, y'_{2n})$  We claim that this gives the desired coordinate system.

Thus the double points are isolated and hence by compactness there are finitely many.

Next we define the sign of a double point. Recall now that are assuming that n is even and that M is orientable. Choose an orientation of M and of  $\mathbb{R}^{2n}$ . If f(x) = f(x') = y then transversality tells us that we can write

$$T_{\mathbf{y}}\mathbb{R}^{2n} = D_{\mathbf{x}}f(T_{\mathbf{x}}M) \oplus D_{\mathbf{x}'}f(T_{\mathbf{x}'}M).$$

As both sides of this equations are oriented vector spaces we can assign a sign to the double point according to whether or not the orientations agree. Notice that since n is even the order of the factors on the right hand side is immaterial. Also notice that the sign is independent of the choice of orientation of M.

We will now prove the following key proposition.

**Proposition 19.4.** If a pair of double points  $y_1$  and  $y_2$  of opposite sign with preimages  $(x_1, x'_1)$  and  $(x_2, x'_2)$  respectively. Then we can modify f so as to eliminate the double point without introducing any others.

*Proof.* Then choose  $\gamma$  and  $\gamma'$  embedded smooth curves in M with endpoints  $x_1, x_2$  and  $x_1', x_2'$  respectively. Since n > 2 we can assume that the curves are disjoint and that their images are disjoint except at the endpoints. Let  $\Gamma = f(\gamma) \cup f(\gamma')$  denote the union of these images.  $\Gamma$  is an embedded closed curve in  $\mathbb{R}^{2n}$  and hence bounds a disk  $\sigma: D^2 \to \mathbb{R}^{2n}$ . We can assume that  $\sigma$  is transverse to f and to itself. This implies that  $\sigma$  has no double points and that  $\sigma$  misses f except along  $\Gamma$ .

Let N be the normal bundle of  $\sigma$ . Since  $\sigma$  is contractible N is trivial so that there is a bundle isomorphism

$$N \equiv D^2 \times \mathbb{R}^{2n-2}.$$

Let  $\nu$  and  $\nu'$  denote the normal bundles of  $\gamma$  and  $\gamma'$  in M. These are again trivial bundles. Note that along  $f(\gamma)$ ,  $Df(\nu)$  defines a distinguished subbundle similarly along  $f(\gamma')$ ,  $Df(\nu')$ .

Notice that the tubular neighborhood of By the tubular neighborhood theorem there is a diffeomorphism

$$\psi: D^2 \times D^{2n-2} \to \mathbb{R}^{2n}$$

Suppose that we can write  $N = \xi_1 \oplus \xi_2$  so that

$$\xi|_{f(\gamma)} = Df(\nu)$$
 and  $\xi|_{f(\gamma')} = Df(\nu')$ 

Then we can write the tubular neighborhood of  $\sigma$  in a standard way and we see since we can push the two dimensional picture till the two arcs don't intersect we can also push the higher dimensional picture till they don't intersect.

We must return to the issue of extending the splitting. The splitting gives rise to a map  $\upsilon:\Gamma\to \mathrm{Gr}_{n-1}(\mathbb{R}^{2n-2})$  and we must understand when this map is null homotopic. Form algebraic topology we know that  $\mathrm{Gr}_{n-1}(\mathbb{R}^{2n-2})$  fundamental group  $\mathbb{Z}/2\mathbb{Z}$  and is generated by the family of subspaces

$$\Pi_t = \text{span}\{\cos(t)e^1 + \sin(t)e^n, e^2, \dots, e^{n-1}\}.$$

as t varies between 0 and  $\pi$ . In other words the identification of  $\Pi_0$  with  $\Pi_{\pi}$  is orientation reversing. Thus the orientation of  $\xi_1 \oplus \xi_2$  must be the same at the two end if the splitting is to extend. On the other hand the normal vectors in the two disk reverse orientation.

To prove the theorem we need to see that we first modify f so that the signed number of double points is zero. To this end consider the map

$$(x_1,\ldots,x_n)\mapsto (x_1-2x_1/u,x_2,\ldots,x_n,1/u,x_1x_2/u,\ldots,x_1x_n/u)$$

where  $u(x_1, ..., x_n) = (1+x_1^2)(1+x_2^2)...(1+x_n^2)$ . It is straightfoward if tedious to check that this map has exactly one double point and also notice that at very large distance from the origin this map is quite close to the linear embedding

$$(x_1, \ldots, x_n, 0, \ldots, 0)$$

in other words we can shrink the map down a lot and use it to modify a given map to have another double point and we can choose the sign of this double points as well.

Now we consider the case that n is odd (it doesn't matter now if M is orientable). Then the sign of a point of intersection is not well defined. In this case however the relative sign of a pair of intersection points given the pair of curves  $\gamma$  and  $\gamma'$  is still well defined. If the curves  $\gamma$  joining  $x_1$  and  $x_2$  and  $\gamma'$  joining  $x_1'$  to  $x_2'$  lead to intersection with the same sign choose different curves now joining  $x_1$  to  $x_2'$  and joining  $x_1'$  to  $x_2$ .

If M is nonorientable and we have curves  $\gamma$  and  $\gamma'$  leading to a pair of intersection point with the same sign add to  $\gamma'$  a curve running around a loop that reverses orientation.

---

## **Lecture 23-28**

## 20 Morse Theory

**Definition 20.1.** A function on a manifold is called a *Morse function* if all of it critical points are non-degenerate.

Sorry, no notes.

---

## Lecture 29.

## 21 Canonical forms

## 21.1 The Lie Derivative

Let M be a vector field on a manifold M. As we say the vector field generates a flow  $F_t: M \to M$  at least locally in M characterized by the condition that for all  $x \in M$  we have

$$\frac{d}{dt}F_t(x) = X(F_t(x))$$

Remark 5. Or in words the tangent vector to the curve defined by  $t \to F_t(x)$  at t = 0 is X(x).

Using the flow we can differentiate objects on M. For example given a function  $f: M \to \mathbb{R}$  we can compute

$$\frac{d}{dt}f\circ F_t(x).$$

**Lemma 21.1.**  $\frac{d}{dt} f \circ F_t(x)|_{t=0} = D_x f(X(x)).$ 

*Proof.* This follows from remark 5.

We will often write Xf(x) for any of these expressions.

For vector field we can do the same. Here we need to be a little careful about conventions. Suppose that X, Y are vector fields on X. Then we can form their bracket [X, Y]. Here it is easiest to think in terms of the action on functions. If f is a  $C^2$  function then we define.

$$[X, Y](f) = X(Yf) - Y(Xf)$$

If in terms of local coordinates  $X = a^i \frac{\partial}{\partial x^i}$  and  $Y = b^j \frac{\partial}{\partial x^j}$  then

$$[X, Y] = \left(a^i \frac{\partial b^j}{\partial x^i} - b^i \frac{\partial a^j}{\partial x^i}\right) \frac{\partial}{\partial x^j}.$$

The remaining terms dropping out since mixed partials commute.

A little more invariantly in term of a patch we have can represent X and Y by maps

$$X. Y: U \rightarrow B$$

and then

$$X(Yf)(x) = D^2 f(X, Y) + D_x Y(X) f$$

and hence

$$[X, Y]f(x) = (D_x Y(X) - D_x X(Y))f$$

We can also get a path of vector fields at x by considering

$$D_{F_t(x)}F_{-t}(Y(F_t(x)))$$

and we define the Lie Derivative to be

$$\mathcal{L}_X Y = \frac{d}{dt} D_{F_t(x)} F_{-t}(Y(F_t(x)))$$

Fortunately we have

## **Proposition 21.2.**

$$\mathcal{L}_X Y = [X, Y]$$

*Proof.* Let  $G_s$  denote the time s flow for the vector field Y. Then

$$D_{F_t(x)}F_{-t}(Y(F_t(x)))f = \frac{d}{ds}f \circ F_{-t} \circ G_s \circ F_t(x)|_{s=0}$$

so that

$$\frac{d}{dt}D_{F_{t}(x)}F_{-t}(Y(F_{t}(x)))f|_{t=0} = \frac{d}{dt}\frac{d}{ds}f \circ F_{-t} \circ G_{s} \circ F_{t}(x)|_{s=0,t=0} 
= \frac{d}{ds}\frac{d}{dt}f \circ F_{-t} \circ G_{s} \circ F_{t}(x)|_{s=0,t=0} 
= \frac{d}{ds}(-Xf)(G_{s}(x) + X(f \circ G_{s})(x) 
= -Y(Xf) + X(Yf).$$

As advertised.

Recall that every square matrix A with complex entries is conjugate to one in Jordan canonical form and many theorems about matrices are obvious once we use this fact. So it is in geometry. We already saw one baby example of canonical forms.

**Theorem 21.3.** Let X be a vector field on the Banach manifold M modeled on B. Suppose for some  $m \in M$  we have  $X(m) \neq 0$  Then there is a chart  $\phi$ :  $U \times (-\epsilon, \epsilon) \to M$  about m so that  $\phi^*(X) = (0, \frac{d}{dt})$ .

In other words any two vector fields non-zero at a point in M are equivalent in small enough neighborhoods under the action of diffeomorphisms of M fixing the point.

---

### Lecture 30.

### 21.2 The Frobenious Integrability Theorem

Next we consider when can a subbundle  $\xi$  of the tangent bundle TM of M can be brought into a canonical form. In generality this is a very complicated problem and we need to isolate manageable cases. The example that comes to mind is the case where  $\Xi_0|_{(x,y)} = T_x \mathbb{R}^n \times \{0\} \subset T_x \mathbb{R}^n \times T_x \mathbb{R}^{m-n}$ , the tangent bundle along a product. A subbundle which is locally diffeomorphic to  $\Xi_0$  is called *integrable*.

Notice that  $\Xi_0$  is has following property. If

$$X_1 = \sum_{i=1}^n a^i(x^1, \dots, x^m) \frac{\partial}{\partial x^i},$$
 and  $X_2 = \sum_{i=1}^n b^i(x^1, \dots, x^m) \frac{\partial}{\partial x^i}$ 

is a pair of local sections of  $\Xi_0$  then the bracket

$$[X_1, X_2] = \sum_{i,j=1}^{n} \left( a^i \frac{\partial b^j}{\partial x^i} - b^i \frac{\partial a^j}{\partial x^i} \right) \frac{\partial}{\partial x^j}$$

is also a local section of  $\Xi$ . A subbundle with this property is called *involutive*. Clearly any integrable subbundle is involutive. Examples:

$$\Xi_1 = \operatorname{span}\left\{\frac{\partial}{\partial x} + \frac{2zx}{1 + x^2 + v^2} \frac{\partial}{\partial z}, \frac{\partial}{\partial y} + \frac{2zy}{1 + x^2 + v^2} \frac{\partial}{\partial z}\right\}$$

is involutive indeed it field of tangent planes to the family of paraboloids

$$z = \lambda(1 + x^2 + y^2)$$

On the other hand

$$\Xi_2 = \operatorname{span}\{\frac{\partial}{\partial x} + y \frac{\partial}{\partial z}, \frac{\partial}{\partial y}\}\$$

is not involutive. In fact in has the interesting property that given any two points and any path connected neighborhood there is a path tangent to  $\Xi_2$  joining the two points contained in the neighborhood. Clearly then  $\Xi_2$  is not integrable.

The following provides a converse.

**Theorem 21.4.** (*Frobenius*). *If*  $\Xi$  *is involutive then it is integrable.* 

*Proof.* Choose first a coordinate patch about of the from  $\phi: U \to \mathbb{R}^n \times \mathbb{R}^{m-n}$  so that at  $\phi(m) = 0$  and  $\phi_*(\xi_m) = T_0\mathbb{R}^n \times \{0\}$ . Set  $\Xi_1 = \phi_*(\Xi)$ .

Then in some neighborhood  $V \times W$  of  $\phi(m) = 0$  we can find a function  $f: V \times W \times \mathbb{R}^n \to \mathbb{R}^{m-n}$ , linear in the last factor with  $f(0, 0, \cdot) = 0$  and so that any  $\xi \in \Xi$  can uniquely be written as

$$\xi = (e, f(x, y, e).$$

There is a natural homotopy of  $\Xi_0$  to  $\Xi_1$  given by

$$\Xi_t = \{(e, t f(tx, y, e) | e \in \mathbb{R}^n\}.$$

We will show that there is a one parameter family of diffeomorphisms  $F_t$  so that

- 1.  $F_t(0) = 0$  and
- 2.  $(F_t)_*(X_t) = \Xi_0$ .

Thus  $F_1$  is the desired change of coordinates. For  $x \in V$  let

$$X_{r}(v, w) = (x, f(v, w, x))$$

Then the fact the  $\Xi_1$  is involutive implies that  $[X_x, X_y] \in \Xi_1$  but  $[X_x, X_y]$  is certainly of the form (O, \*) since the constant vectors fields x and y commute so  $[X_x, X_y] = 0$ . More explicitly

$$[X_x, X_y] = (0, D_{(v,w,x)} f(y, f(v, w, y), 0) - D_{(v,w,y)} f(x, f(v, w, x), 0)) = 0$$

Let  $X_t(v, w) = (0, f(tv, w, v))$ . A typical section of  $\Xi_t$  is  $X_{t,x}(u, v) = (x, tf(tv, w, x))$ . We can work out the bracket  $[X_t, X_{t,x}]$ 

$$[X_{t}, X_{t,x}] = (0, tD_{(tv,w,x)} f(0, f(tv, w, v), 0) -tD_{(tv,w,v)} f(x, f(tv, w, x), 0) - f(tv, w, x))$$
$$= -tD_{(tv,w,x)} f(v, 0, 0) - f(tv, w, x)$$
$$= -\frac{d}{dt} X_{t,x}$$

Thus the Lie derivative of  $[(X_t, \frac{d}{dt}), X_{t,x}] = 0$  or equivalently if  $F_t$  is the flow of the time dependent vector field then we have  $(F_t)_*(X_{s,x}) = X_{s+t,x}$  as required.

Here is a more intuitive proof by induction on the dimension.

*Proof.* Induction on the dimension of the subbundle. The case of dimension one follows from the standard form for an non-vanishing vector field. The question is also local so we assume that we are given a subbundle of the tangent bundle of  $\mathbb{R}^n$  defined in a neighborhood of  $0 \in \mathbb{R}^n$ . Suppose we have proved the result for all subbundles of dimension d. Let E be an involutive subbundle of  $T\mathbb{R}^n$  of dimension d+1. Choose a nowhere vanishing local section, X, of E. Next choose a coordinate system  $z^1, \ldots, z^n$ , centered at 0, so that  $\frac{\partial}{\partial z^n} = X$ .  $T\mathbb{R}^{n-1} \times \{0\}$  is an integrable hence involutive subbundle.  $E' = E \cap T\mathbb{R}^{n-1} \times \{0\}$  defines a subbundle in a neighborhood of 0 of dimension d. Since E' is the intersection of two involutive subbundles it is involutive and so the induction hypothesis applies. We can find a coordinate system  $y^1, \ldots, y^n$  centered at 0 so that E' is given in a neighborhood of 0 as the span of  $y^1, \ldots, y^d$  In this new coordinate system X may not be straight but we have that

$$\frac{\partial}{\partial y^1}, \dots, \frac{\partial}{\partial y^d}, X$$

forms a basis for E. We can write

$$X = \sum_{i=1}^{d} a^{i} \frac{\partial}{\partial y^{i}} + X_{0}$$

where  $X_0$  is section of TW. Then

$$\frac{\partial}{\partial y^1}, \ldots, \frac{\partial}{\partial y^d}, X_0$$

is also a basis for E. Since  $X_0$  is a section of TW so is  $[\frac{\partial}{\partial y^i}, X_0]$ . By involutivity it is parallel to  $X_0$  so there is a smooth function  $f_1$  defined in a neighborhood of 0 with

$$\left[\frac{\partial}{\partial y^i}, X_0\right] = f_1 X_0.$$

Set

$$g_1 = -int_0^{y^1} f_i(\mathbf{w}, s, y^2, \dots, y^d) ds.$$

Then set

$$X_1 = \exp(g_1)X_0.$$

It is now easy to check that

$$\left[\frac{\partial}{\partial y^i}, X_1\right] = 0.$$

 $X_1$  is still a section of TW so  $\left[\frac{\partial}{\partial y^i}, X_0\right]$  is parallel to  $X_1$  and we can find a smooth function  $f_2$  so that

$$\left[\frac{\partial}{\partial y^i}, X_1\right] = f_2 X_1$$

We claim that

$$\frac{\partial f_2}{\partial v^1} = 0.$$

To see this notice that

$$\left[\frac{\partial}{\partial y^1}, \left[\frac{\partial}{\partial y^2}, X_1\right] = \frac{\partial f_2}{\partial y^1} X_1 = 0.\right]$$

Using Jacobi's identity we also have

$$\begin{bmatrix} \frac{\partial}{\partial y^1}, [\frac{\partial}{\partial y^2}, X_1] &= [[\frac{\partial}{\partial y^1}, \frac{\partial}{\partial y^2}]X_1] + [\frac{\partial}{\partial y^2}, [\frac{\partial}{\partial y^1}, X_1] \\ &= 0. \end{bmatrix}$$

So if we set

$$g_2 = -\int_0^{y^2} f_i(\mathbf{w}, y^1, s, y^3, \dots, y^d) ds.$$

and

$$X_2 = e^{g_2} X_1$$

we have

$$\left[\frac{\partial}{\partial y^i}, X_2\right] = 0$$

for i = 1, 2. Continuing in this fashion we eventually find  $X_d$  commuting with  $y^1, \ldots, y^d$  and we can construct the desired coordinate system as we did in class.

#### 21.3 Foliations

The local structure of the previous subsection has as its global counterpart the notion of a foliation. Here is the precise definition.

**Definition 21.5.** A foliation  $\mathcal{F}$  of M is a decomposition of M as a disjoint union of connected immersed submanifolds  $M = \coprod_{\alpha \in A} \mathcal{L}_{\alpha}$  called the leaves of  $\mathcal{F}$  so that each point has a chart  $(U, \phi)$  so that under  $\phi$  the decomposition obtained from the decomposition  $\coprod_{\alpha \in A} \mathcal{L}_{\alpha} \cap U$  by taking components goes over to the decomposition of  $\mathbb{R}^n = \coprod_{x \in \mathbb{R}^{n-k}} \mathbb{R}^k \times x$ .

It is important to realize that in the above definition we do not require the leaves to have the subspace topology. For example Consider the 2-torus

$$T^2 = \mathbb{R}^2/\mathbb{Z}^2$$

Fix a pair of real numbers  $(\zeta_1, \zeta_2)$  so that  $\zeta_1/\zeta_2$  is irrational. The cosets of the subgroup  $\Gamma$  generated by  $\{[t\zeta_1, t\zeta_2]|t \in \mathbb{R}\}$  give rise to a foliation with leaves that are not locally closed subsets.

*Remark* 6. The space of leaves of a foliation is one setting where one runs into non-Hausdorff manifolds. The space of leaves has a natural covering by charts (These may not be injective so be careful).

# 22 Characterizing a codimension one foliation in terms of its normal vector.

Let  $\mathcal{F}$  be a two dimensional foliation of  $\mathbb{R}^3$ .

**Proposition 22.1.** Let **n** be a local normal vector field to  $\mathcal{F}$ . Then

$$\mathbf{n} \cdot (\nabla \times \mathbf{n}) = 0$$

Proof. Write

$$\mathbf{n} = a\frac{\partial}{\partial x} + b\frac{\partial}{\partial y} + c\frac{\partial}{\partial z}.$$

By rotating the coordinates we can assume that none of a, b or c are zero. Then  $\mathcal{F}$  is locally spanned by the local sections

$$-b\frac{\partial}{\partial x} + a\frac{\partial}{\partial y}, c\frac{\partial}{\partial x} - a\frac{\partial}{\partial z}, c\frac{\partial}{\partial y} - b\frac{\partial}{\partial z}$$

and we have

$$\begin{split} [-b\frac{\partial}{\partial x} + a\frac{\partial}{\partial y}, c\frac{\partial}{\partial x} - a\frac{\partial}{\partial z}] &= [-b\frac{\partial}{\partial x}, -a\frac{\partial}{\partial z}] + [a\frac{\partial}{\partial y}, c\frac{\partial}{\partial x}] + [a\frac{\partial}{\partial y}, -a\frac{\partial}{\partial z}] \\ &= b\frac{\partial a}{\partial x}\frac{\partial}{\partial z} - a\frac{\partial b}{\partial z}\frac{\partial}{\partial x} + a\frac{\partial c}{\partial y}\frac{\partial}{\partial x} - c\frac{\partial a}{\partial x}\frac{\partial}{\partial y} + -a\frac{\partial a}{\partial y}\frac{\partial}{\partial z} + a\frac{\partial a}{\partial z}\frac{\partial}{\partial y} \\ &= a\big((\frac{\partial c}{\partial y} - \frac{\partial b}{\partial z})\frac{\partial}{\partial x} + \frac{\partial a}{\partial z}\frac{\partial}{\partial y} - \frac{\partial a}{\partial y}\frac{\partial}{\partial z}\big) + b\frac{\partial a}{\partial x}\frac{\partial}{\partial z} + -c\frac{\partial a}{\partial x}\frac{\partial}{\partial y}. \end{split}$$

Since we are assuming that  $\mathcal{F}$  is involutive we have

$$a\left(\left(\frac{\partial c}{\partial y} - \frac{\partial b}{\partial z}\right)a + \frac{\partial a}{\partial z}b - \frac{\partial a}{\partial y}c\right) = 0.$$

Since  $a \neq 0$  we have:

$$\left( \left( \frac{\partial c}{\partial y} - \frac{\partial b}{\partial z} \right) a + \frac{\partial a}{\partial z} b - \frac{\partial a}{\partial y} c \right) = 0.$$

This same equation hold for any cyclic permutation of a, b, c and simultaneous permutation of x, y, z. Adding the resulting three equations gives

$$2\left(\left(\frac{\partial c}{\partial y} - \frac{\partial b}{\partial z}\right)a + \left(\frac{\partial a}{\partial z} - \frac{\partial c}{\partial x}\right)b + \left(\frac{\partial b}{\partial x} - \frac{\partial a}{\partial y}c\right)\right) = 0.$$

as required.

## 23 The holonomy of closed loop in a leaf

**Definition 23.1.** Let  $\mathcal{F}$  be a foliation of a manifold M. A transversal to  $\mathcal{F}$  is smooth locally closed submanifold of M which meets all leaves transversally. A local transversal is a transversal which is diffeomorphic to a disk.

To discuss the holonomy we will use the terminology of a germs.

**Definition 23.2.** Let X, Y be smooth manifolds. Fix a point  $x \in X$ . A germ of smooth mappings at x is the equivalence class of functions  $f: U \to Y$  where  $U \subset X$  is an open neighborhood of x under the equivalence relation of agreement upon restriction. That is  $f: U \to Y$  is equivalent to  $g: V \to Y$  if there is a neighborhood W of x so that  $f|_{W} = g|_{W}$ .

Let  $\tau_1$  and  $\tau_2$  be local transversals hitting the same leaf  $\mathcal{L}$  of  $\mathcal{F}$ .  $\tau_1$  and  $\tau_2$  are both contained in the same foliation chart U. Then the chart defines the germ of a diffeomorphism from  $\tau_1$  at  $\tau_1 \cap \mathcal{L}$  to  $\tau_2$  at  $\tau_2 \cap \mathcal{L}$ 

Let  $\gamma: S^1 \to \mathcal{L}$  be a  $C^1$  closed loop based at x in a leaf  $\mathcal{L}$  of foliation  $\mathcal{F}$ . Let  $\tau$  be a transversal to  $\mathcal{F}$  passing through x.

### 24 Reeb's stability theorem

**Definition 24.1.** A codimension one foliation is called transversally orientable if the normal bundle  $\nu = TM/T\mathcal{F}$  is orientable.

**Theorem 24.2.** Let  $\mathcal{F}$  be a normally oriented two dimensional foliation of a compact oriented three manifold. If  $\mathcal{F}$  contains  $S^2$  as a closed leave then the pair M,  $\mathcal{F}$  is diffeomorphic to  $S^2 \times S^1$  with the product foliation by two-spheres.

Remark 7. To see that the normally oriented condition is important in the statement of the result note the following.  $S^2 \times S^1$  has an orientation preserving involution  $\tau: S^2 \times S^1 \to S^2 \times S^1$  given by

$$\tau(x, e^{i\theta}) = (-x, e^{-i\theta}).$$

This is a fixed point free involution so the quotient  $X = S^2 \times S^1/(x, e^{i\theta}) \sim (-x, e^{-i\theta})$  has the structure of manifold as well. The product foliation is of  $S^2 \times S^1$  is carried to itself by  $\tau$  and descends to a foliation of X. The induced foliation is not normally oriented (can you see this). Most of the leaves are two sphere but there are two leaves which are real projective planes.

**Lemma 24.3.** Let  $\phi: D^2 \to M$  be an smooth embedding of  $D^2$  into  $M^3$  with image contained in a leaf L of  $\mathcal{F}$ . Then there is a foliating coordinate patch  $\tilde{\phi}: D^2 \times (-\epsilon, \epsilon) \to M^3$  extending  $\phi$ .

*Proof.* First of all it is straightforward to construct a coordinate patch  $\psi: D^2 \times (-a,a) \to M$  extending  $\phi$  so that  $\mathcal{F}$  is transverse to all the  $\psi(\{x\} \times (-a,a))$  and so  $T\mathcal{F}$  agrees with  $D_{(0,t)}\psi(T_0D^2\times\{0\})$ . Transfer  $\mathcal{F}$  to a foliation of  $D^2\times(-a,a)$  still called  $\mathcal{F}$ . Let  $(r,\theta)$  be polar coordinates in the disk.

Define G on  $(D^2 \setminus \{0\}) \times (-a, a)$  to be the span of  $\frac{\partial}{\partial r}$  and  $\frac{\partial}{\partial t}$ . By construction G is transverse to  $\mathcal{F}$  and so the intersection  $T\mathcal{F} \cap G$  defines a line field on  $(D^2 \setminus \{0\}) \times (-a, a)$ . This line field is spanned by a vector field of the form  $v(r, \theta, t) = \frac{\partial}{\partial r} + a(r, \theta, t) \frac{\partial}{\partial t}$ . We have  $a(r, \theta, 0) = 0$  and  $a(0, \theta, t) = 0$ . and let  $F_s$  denote the time s flow of v.  $F_s(r, \theta, t) = (r + s, \theta, T_s(r, \theta, t))$  when it is defined. Choose b small enough so that the time 1-flow of v with initial conditions  $(0, \theta, t)$  for |t| < b is defined. Define a map  $\tilde{\phi} : D^2 \times (-b, b) \to D^2 \setminus \{0\} \times (-a, a)$  by sending  $(r, \theta, t)$  to the point  $(r, \theta, T_r(0, \theta, t))$  or in words the time r flow of  $(0, \theta, t)$  under v. This map takes the line segment  $\{(r, \theta, t) | 0 \le r < 1\}$  to a leaf. Since for any  $\theta$   $v(0, \theta, t) = \frac{\partial}{\partial r}$  is tangent to  $\mathcal{F}$ ,  $\tilde{\phi}$  carries  $D^2 \times \{t\}$  onto a leaf. Thus  $\tilde{\phi}$  is the required map.

Next we prove that in a neighborhood of a two-sphere leaf the foliation has a product structure.

**Lemma 24.4.** Suppose that  $\mathcal{L}$  is a leaf of  $\mathcal{F}$  which diffeomorphic to  $S^2$  The is a saturated neighborhood N of  $\mathcal{L}$  which diffeomorphic to  $S^2 \times (-a, a)$  with the product foliation.

*Proof.* Decompose  $S^2 = D_+^2 \cup D_-^2$ . By the previous lemma we can find standard neighborhoods and glue them together to get the result.

Next we will show that the set of points on a leaf diffeomorphic to  $S^2$  is both open and closed.

**Theorem 24.5.** Let  $\mathcal{F}$  be a transversally oriented foliation. Then there is a embedding  $\gamma: S^1 \to M$  transverse to the leaves. In fact  $\gamma$  can be chosen to pass through any point of M

Remark 8. This is not to say that the image of  $\gamma$  hits all the leaves. This is a much stronger condition. A foliation with this addition property is called taut. The Reeb foliation of  $S^3$  is an example of a non-taut foliation. Any flow line can only touch the torus leaf once but a closed circle transverse to a torus in  $S^3$  must meet the torus in an even number of points.

*Proof.* Fix a point  $x_0 \in M$ . Since  $\mathcal{F}$  is transversally oriented there is a nowhere vanishing vector field, v, which is transverse to the leaves. Let  $F_t$  denote the time-t flow for this vector field and consider a particular flow line,  $\gamma$ , of this vector field. If this flow line is a periodic orbit we are done so suppose it is not. Then we claim that there is leaf that is hit infinitely often by the flowline. We can find  $x \in X$  and sequence  $t_i \to \infty$  so that  $\lim_{i \to \infty} F_{t_i}(x_0) = x$ . Let U be a foliation chart in M about x. We can construct a smaller chart, V, about x by using the vector field v to flow away from the leaf  $\mathcal L$  containing v. In v if a point is on a connected component of the part of the flow line in v it hits v. Since infinitely many points of v in different components of  $v \cap V$  are contained in v the claim follows.

Thus we can find a piece of orbit which contains  $x_0$  and hits some leaf twice and the points of intersection are contained in the patch V. It is straightforward to modify the piece of flow line in this patch to close it up.

Now consider our transversally oriented foliation of  $M^3$  containing a leaf  $\mathcal{L}$  diffeomorphic to  $S^2$ . Let  $\gamma$  be a closed transverse curve passing through  $\mathcal{L}$ . Let  $\Gamma$  denote the union of all the leaves which pass through  $\Gamma$ . We claim that  $\Gamma$  is all of M and that  $\gamma$  hits each leaf the same number of times.

By Lemma 24.4  $\Gamma$  is open. Also by this lemma there for each point y of  $\gamma$  there is a compact foliated neighborhood diffeomorphic to  $S^2 \times [0, 1]$ . By the compactness of  $\gamma$  finitely many such neighborhoods cover  $\gamma$  but then  $\Gamma$  is the union of finitely many closed sets and hence closed. Finally consider the function which associates to each point y of  $\gamma$  the of points of  $\gamma$  contained in the same leaf as  $\gamma$ . By Lemma 24.4 this is a continuous function and hence is constant.

Finally choose a new  $\gamma$  which hits  $\mathcal{L}$  once and hence all leaves once. Then

$$h: \mathcal{L} \times \gamma \to M$$

given by taking  $y \in \mathcal{L}$  and  $t \in \gamma$  to the unique point in the leaf through t hit by the flow line of v through y is the required diffeomorphism.

---

## 25 Differential forms and de Rham's Theorem

## 25.1 The exterior algebra

Let V be a finite dimensional vector space over the reals. The tensor algebra of V is direct sum

$$\mathbf{Ten}(V) = \mathbb{R} \oplus V \oplus V^{\otimes 2} \dots \oplus V^{\otimes k} \dots$$

It is made into an algebra by declaring that the product of  $a \in V^{\otimes k}$  and  $b \in V^{\otimes l}$  is  $a \otimes b \in V^{\otimes (k+l)}$ . It is characterized by the universal mapping property that any linear map  $V \to A$  where A is an algebra over  $\mathbb R$  extends to a unique map of algebras  $\mathbf{Ten}(V) \to A$ .

The exterior algebra algebra is the quotient of exterior algebra by the relation

$$v \otimes v = 0$$
.

The exterior algebra is denoted  $\Lambda^*(V)$  or  $\Lambda(V)$ . It is customary to denote the multiplication in the exterior algebra by  $(a,) \mapsto a \wedge b$  If  $v_1 \dots v_k$  is a basis for V then this relation is equivalent to the relations

$$v_i \wedge v_j = -v_j \wedge v_i \text{ for } i \neq j,$$
  
 $v_i \wedge v_i = 0$ 

Thus  $\Lambda^*(V)$  has basis the products

$$v_{i_1} \wedge v_{i_2} \dots v_{i_k}$$

where the indices run over all strictly increasing sequences of numbers between 1 and n.

$$1 < i_i < i_2 < \ldots < i_k < n.$$

Since for each k there are  $\binom{n}{k}$  such sequences of length k we have

$$\dim(\Lambda^*(V)) = 2^n$$
.

 $\Lambda^*(V)$  since the relation is homogenous the grading of the tensor algebra descends to a grading on the exterior algebra (hence the \*).

We can apply this construction fiberwise to a vector bundle. The most important example is the cotangent bundle of a manifold  $T^*X$  in which case we get the bundle of differential forms

$$\Lambda^*(T^*X)$$
 or  $\Lambda^*(X)$ .

We will denote the space of smooth sections of  $\Lambda^*(X)$  by  $\Omega^*(X)$ . In local coordinates a typical element of  $\Omega^*(X)$  looks like

$$\omega = \sum_{1 \leq i_1 < i_2 < \dots < i_k \leq n} \omega_{i_1 i_2 \dots < i_k} dx^{i_1} \wedge dx^{i_2} \wedge \dots dx^{i_k}.$$

Since the construction of  $\Lambda^*(X)$  was functorial in the cotangent bundle these bundles naturally pull back under diffeomorphism and if  $f: X \to Y$  is any smooth map there is natural map

$$f^*: \Omega^*(Y) \to \Omega^*(X)$$

The most important thing about differential forms is the existence of a natural differential operator the exterior differential defined locally by the following rules

$$df = \sum_{i=1}^{n} \frac{\partial f}{\partial x^{i}} dx^{i}$$

$$d\omega = \sum_{1 < i_{1} < i_{2} < \dots < i_{k} < n} d\omega_{i_{1}i_{2}\dots < i_{k}} \wedge dx^{i_{1}} \wedge dx^{i_{2}} \wedge \dots dx^{i_{k}}.$$

Notice that we can't invariantly define a similar operator on the tensor algebra. If we have a one form

$$\theta = \sum_{i=1}^{\infty} f_i dx^i$$

and try to define

$$D\theta = \sum_{i=1}^{\infty} \frac{\partial f_i}{\partial x^j} dx^j \otimes dx^i$$

then when if we have new coordinates  $y^1 \dots y^n$  we have

$$dx^{i} = \sum_{i=1}^{n} \frac{\partial x^{i}}{\partial y^{j}} dy^{j}$$

and

$$\theta = \sum_{m=1}^{n} g_m dy^m$$

where

$$g_m = f_i \frac{\partial x^i}{\partial y^m}$$

$$D\theta = \sum_{i=1}^{\infty} \frac{\partial f_i}{\partial x^j} dx^j \otimes dx^i$$

$$= \frac{\partial f_i}{\partial x^j} \frac{\partial x^i}{\partial y^l} \frac{\partial x^j}{\partial y^m} dy^m \otimes dy^l$$

$$= \frac{\partial f_i}{\partial y^k} \frac{\partial y^k}{\partial x^j} \frac{\partial x^i}{\partial y^l} \frac{\partial x^j}{\partial y^m} dy^m \otimes dy^l$$

$$= \frac{\partial f_i}{\partial y^m} \frac{\partial x^i}{\partial y^l} dy^m \otimes dy^l$$

$$= \frac{\partial f_i}{\partial y^m} \frac{\partial x^i}{\partial y^l} dy^m \otimes dy^l$$

$$= (\frac{\partial}{\partial y^m} (f_i \frac{\partial x^i}{\partial y^l}) - f_i \frac{\partial^2 x^i}{\partial y^m \partial y^l}) dy^m \otimes dy^l$$

$$= \sum_{m=1}^{\infty} \frac{\partial g_l}{\partial y^m} dy^m \otimes dy^l - f_i \frac{\partial^2 x^i}{\partial y^m \partial y^l} dy^m \otimes dy^l.$$

Thus our definition depends on the choice of coordinates. Notice that when we pass to the exterior algebra this last expression vanishes that exterior derivative is well defined.

## **Theorem 25.1.** $d^2 = 0$ .

*Proof.* From the definition in local coordinates it suffices to check that  $d^2=0$  on functions.

$$d^{2}(f) = \sum_{i,j=1}^{n} \frac{\partial^{2} f}{\partial x^{i} \partial x^{j}} dx^{i} \wedge dx^{j} = 0$$

since the f smooth so the matrix of second derivatives is symmetric.  $\Box$ 

## **Proposition 25.2.**

$$d(a \wedge b) = da \wedge b + (-1)^{\deg(a)} \wedge db.$$

*Proof.* The bilinearity of the wedge product implies that it suffices to check the result when

$$a = f dx^{i_1} \wedge dx^{i_2} \wedge \ldots \wedge dx^{i_k}.$$

**Definition 25.3.** A cochain complex is a graded vector space  $C = \sum_{i=0}^{\infty} C_i$  together with a map  $d: C \to C$  so that  $dC_i \subset C_{i+1}$  and  $d^2 = 0$ . The cohomology groups of a cochain complex are defined to be

$$H^i(C, d) = \ker(d : C^i \to C^{i+1}) / \operatorname{Ran}(d : C^{i-1} \to C^i)$$

---

## Lecture 32.

## 25.2 The Poincaré lemma and homotopy invariance of the DeRham cohomology

There are a bunch of basic forumlas in dealing with forms, the exterior derivative and contraction and the Lie derivative.

Recall that the Lie derivative is defined as follow. Given a vector field v let  $F_t$  be its time t flow. By pull back this acts on forms on the manifold. Fixing a point  $x \in X$  we can watch what happens to the a form at the point x under the flow, i.e consider the path

$$F_t^*(\omega_{F_t(x)}) \in \Lambda_x^k(X)$$

The derivative at t = 0 is called the Lie derivative

$$\mathcal{L}_v \omega = \frac{d}{dt} F_t^*(\omega_{F_t(x)})|_{t=0} \in \Lambda_x^k(X)$$

More generally there is a Lie derivative on tensors. Note that if f is a function then this definition amounts to nothing more that

$$\mathcal{L}_{v}f = \frac{d}{dt}f \circ F_{t}(x)_{t=0} = vf(x) = \iota_{v}df$$

Since the exterior derivative is natural under diffeomorphisms it follows that Lie derivative commutes with d. Hence

$$\mathcal{L}_v df = d\mathcal{L}_v f = d\iota_v df.$$

More generally we have Cartan's formula or the homotopy formula.

$$\mathcal{L}_v\omega = d\iota_v\omega + \iota_v d\omega.$$

We prove this by induction on the degree of the form. We have checked the case of functions. Furthermore it is enough to check that that both sides satisfy the Leibniz rule.

$$\mathcal{L}_{v}(\omega \wedge \eta) = \mathcal{L}_{v}(\omega \wedge \eta) = d\iota_{v}\omega + \iota_{v}d\omega.$$

Let  $i: M \to \mathbb{R} \times M$  be the inclusion i(x) = (0, x) and let  $\pi: \mathbb{R} \times M \to M$  be the projection. We claim that the induced maps on cohomology are inverses of each other. Thus we have

**Proposition 25.4.** The groups  $H^*(M)$  and  $H^*(\mathbb{R} \times M)$  are isomorphic.

To prove this we will construct a map *K* 

## 26 Čech cohomology

Let  $\mathfrak{U} = \{U_{\alpha} | \alpha \in A\}$  be a open cover of a topological space. Using the combinatorics of the cover when can define a complex as follows. Let  $C^p(\mathfrak{U})$  be the space of all locally constant functions on p+1 fold intersections

$$U_{\alpha_0}\cap\ldots\cap U_{\alpha_p}$$

with the symmetry property that if  $\sigma$  is a permutation of  $0, \ldots, p$  then

$$f|U_{\alpha_0}\cap\ldots\cap U_{\alpha_p}=\operatorname{sign}(\sigma)f|U_{\alpha_{\sigma(0)}}\cap\ldots\cap U_{\alpha_{\sigma(p)}}.$$

We write  $f_{\alpha_0...\alpha_p}$  for  $f|U_{\alpha_0}\cap\ldots\cap U_{\alpha_p}$ 

There is a natural codifferential on such functions

$$\delta: C^p(\mathfrak{U}) \to C^{p+1}(\mathfrak{U})$$

defined by the formula

$$(\delta f)_{\alpha_0...\alpha_{p+1}} = \sum_{i=0}^{p+1} (-1)^i f_{\alpha_0...\hat{\alpha}_i \alpha_{p+1}} |_{U_{\alpha_0} \cap ... \cap U_{\alpha_{p+1}}}$$

If we order A then we can consider only ordered intersections and define a similary complex which has isomorphic cohomology. In practice this is how one work but the first definition is choice free so a bit prefereable.

Example. Think of  $S^2$  as the boundary of tetrahedron. Cover  $S^2$  by the four open which are the complements of the four closed two dimensional faces. If we label these sets  $U_1$ ,  $U_2$ ,  $U_3$ ,  $U_4$  then the non empty two fold intersections are

$$U_1 \cap U_2$$
,  $U_1 \cap U_3$ ,  $U_1$ ,  $\cap U_4$ ,  $U_2 \cap U_3$ ,  $U_2 \cap U_4$ ,  $U_3 \cap U_4$ .

and the non-empty three fold intersections are

$$U_1 \cap U_2 \cap U_3$$
,  $U_1 \cap U_2 \cap U_4$ ,  $U_1 \cap U_3 \cap U_4$ ,  $U_2 \cap U_3 \cap U_4$ 

the four-fold intersection is empty.

Then all interections are connected and the complex is

$$\mathbb{R}^4 \mapsto \mathbb{R}^6 \mapsto \mathbb{R}^4$$

with the maps

$$\delta_0(f_1, f_2, f_3, f_4) = (f_1 - f_2, f_1 - f_3, f_1 - f_4, f_2 - f_3, f_2 - f_4, f_3 - f_4)$$
 (8)

and

$$\delta_1(f_{12}, f_{13}, f_{14}, f_{23}, f_{24}, f_{34}) = (f_{23} - f_{13} + f_{12}, f_{24} - f_{14} + f_{12}, f_{34} - f_{14} + f_{13}, f_{34} - f_{24} + f_{23})$$
(9)

The kernel of  $\delta_0$  is clearly the constant functions. Cokernel of  $\delta_1$  is one dimensional and hence we have  $\check{H}^*(\mathfrak{U}) = \mathbb{R}, 0, \mathbb{R}$ .

---

## 26.1 refinement

By a refinement  $\mathfrak{V}$  of an open cover  $\mathfrak{U}$  we mean a  $\mathfrak{V} = \{V_{\beta} | \beta \in B\}$  and a map  $r: B \to A$  so that for all  $\beta \in B$  we have  $V_{\beta} \subset U_{r(\beta)}$ . If we have a refinement then there is a chain map of the Čeck complexes.

$$\tilde{r}: \check{\mathbf{C}}^p(\mathfrak{U}) \to \check{\mathbf{C}}^p(\mathfrak{V})$$

given by the formula

$$\tilde{r}(\{f_{\beta_0\beta_1...\beta_p}\}) = \{f_{\beta_{r(0)}\beta_{r(1)}...\beta_{r(p)}}|_{V_{\beta_{r(0)}\beta_{r(1)}...\beta_{r(p)}}}\}$$

Thus there is a map

$$\tilde{r}^* : \check{H}^*(\mathfrak{U}) \to \check{H}^*(\mathfrak{V}).$$

Thus we have an directed system (well really need to check that if we have two refinements  $\mathfrak{V}$ , r and  $\mathfrak{V}$ , r' then the induced maps  $\tilde{r}$  and  $\tilde{r}'$  are the same.) The direct limit of this system is called the Čech cohomology of X.

## 27 The acyclicity of the sheaf of p-forms.

Then we can consider another version of the of the Čech complex. That is we define  $\check{\mathbf{C}}^p(\mathfrak{U},\Omega^q)$  to be all colletions of q-forms  $\omega_{\alpha_0...\alpha_p}$  defined on  $U_{\alpha_0...\alpha_p}$  with the symmetry properties above. The same formula above defines a differential mapping

$$\check{\mathbf{C}}^p(\mathfrak{U}, \Omega^q) \to \check{\mathbf{C}}^{p+1}(\mathfrak{U}, \Omega^q)$$

Given an open cover \$\mathcal{U}\$ consider the Čech complex

$$\dots \check{\mathsf{C}}^{k-1}(\mathfrak{U};\Omega^p) \xrightarrow{\delta} \check{\mathsf{C}}^k(\mathfrak{U};\Omega^p) \xrightarrow{\delta} \check{\mathsf{C}}^{k+1}(\mathfrak{U};\Omega^p) \xrightarrow{\delta}$$

**Lemma 27.1.** This sequence is exact so long as k > 0.

*Proof.* Fix a partition of unity  $\{\phi_{\beta}|\beta\in B\}$  subordinate to  $\mathfrak{U}=\{U_{\alpha}\}_{\alpha\in A}$ . The supports of the  $\phi_{\beta}$  are a refinement of the  $U_{\alpha}$  and we choose a refinement function  $r:B\to A$  so that  $supp(\phi_{\beta})\subset r(\beta)$ . Define

$$K: \check{\mathsf{C}}^{k+1}(\mathfrak{U};\mathcal{S}_{\Omega^p}) \to \check{\mathsf{C}}^k(\mathfrak{U};\mathcal{S}_{\Omega^p})$$

by

$$K(\omega)|_{U_{\alpha_0\alpha_1...\alpha_{k-1}}} = \sum_{\beta \in B} \phi_{\beta}\omega|_{U_{r(\beta)\alpha_0\alpha_1...\alpha_{k-1}}}$$

Since the supports of the  $\phi_{\beta}$ s are locally finite by definition of partition of unity this is well defined. Now consider where  $k \ge 1$ 

$$\begin{split} (\delta K + K\delta)\omega|_{U_{\alpha_0\alpha_1...\alpha_k}} &= \sum_{i=0}^k (-1)^i K(\omega)|_{U_{\alpha_0...\hat{\alpha}_i...\alpha_k}} + \sum_{\beta \in B} \phi_\beta(\delta\omega)|_{U_{r(\beta)\alpha_0\alpha_1...\alpha_k}} \\ &= \sum_{i=0}^k (-1)^i \sum_{\beta \in B} \phi_\beta\omega|_{U_{r(\beta)\alpha_0...\hat{\alpha}_i...\alpha_k}} \\ &+ \sum_{\beta \in B} \phi_\beta\omega|_{U_{\alpha_0\alpha_1...\alpha_k}} - \sum_{\beta \in B} \sum_{j=0}^k (-1)^j \phi_\beta\omega|_{U_{r(\beta)\alpha_0...\hat{\alpha}_j...\alpha_k}} \big) \\ &= \omega|_{U_{\alpha_0\alpha_1...\alpha_k}}. \end{split}$$

We have used that the sum if locally finite to rearrange the order summation. Thus we have proved the identity is cochain homotopic to zero and so the cohomology groups are zero. Note that if k = 0 then we simple get zero and the argument proves nothing.

**Definition 27.2.** A sheaf that admits partitions of unity is called fine.

---

## 28 The Poincaré Lemma implies the equality of Čech cohomology and de Rham cohomology

The proof here is modelled on the presentation of Weil's proof (see Weil, Andr "Sur les thormes de de Rham." Comment. Math. Helv. 26, (1952). 119–145.) in <u>Principles of Algerbraic Geometry</u> by Griffiths and Harris published by John Wiley and Sons, Inc.

The scheme of the proof is to first restrict attention to countable good covers which we assume to be cofinal in the set of countable covers.

The Poincaré lemma tells us that that for a contractible open set U

$$\mathbb{R} \hookrightarrow \Omega^0(U) \xrightarrow{d} \Omega^1(U) \xrightarrow{d} \Omega^2(U) \xrightarrow{d} \dots$$

is a long exact sequence. We introduce the notation  $\mathbb{Z}^p$  for the closed p-forms so that  $\mathbb{Z}^p(U) = \{\theta \in \Omega^p(U) | d\theta = 0\}$ 

then we can break up this long exact sequence into short exact sequences.

$$0 \to \mathcal{Z}^p(U) \hookrightarrow \Omega^p(U) \stackrel{d}{\to} \mathcal{Z}^{p+1}(U) \to 0.$$

Note that  $\mathcal{Z}^0(U)$  is the constant function so a copy of  $\mathbb{R}$ . These induce long exact sequences in cohomology.

$$\check{H}^{i-1}(M;\Omega^p) \to \check{H}^{i-1}(M;\mathcal{Z}^{p+1}) \to \check{H}^i(M;\mathcal{Z}^p) \to \check{H}^i(M;\Omega^p) \to$$

We have seen that  $\check{H}^i(M; \Omega^p) = \{0\}$  for i > 0 and hence

$$\check{H}^{i}(M;\mathcal{Z}^{p}) \equiv \check{H}^{i-1}(M;\mathcal{Z}^{p+1})$$

for  $i \geq 2$ . Now by definition we the p-th Čech cohomology group of M is

$$\check{H}^p(M;\mathbb{R})=H^p(M;\mathcal{Z}^0).$$

Repeated applying the isomorphism above we have

$$\check{H}^p(M;\mathbb{R}) \approx H^1(M;\mathcal{Z}^{p-1}).$$

Now consider the beginning of the long exact sequence

which becomes

$$0 \to \mathcal{Z}^{p-1}(M) \to \Omega^{p-1}(M) \xrightarrow{d} \mathcal{Z}^{p}(M) \to H^{1}(M; \mathcal{Z}^{p-1}) \to 0$$

Thus

$$H^1(M; \mathcal{Z}^{p-1}) \approx \mathcal{Z}^p(M)/d\Omega^{p-1}(M) = H^p_{deR}(M; \mathbb{R}).$$

Thus we have proved that there is a natural isomorphism

$$\check{H}^p(M;\mathbb{R}) \approx H^p_{deR}(M;\mathbb{R}).$$

---

## Lecture 35.

## 29 The immersion theorem of Smale

Let  $\mathbf{Imm}(X, Y)$  denote the space of immersion of X into Y. Fixing base points  $x \in X$  and  $y \in Y$  and an injection  $\xi : T_x X \to T_y Y$ . let  $\mathbf{Imm}_*(X, Y)$  be the space of base point preserving immersions in the sense that

$$f(x) = y,$$
  $d_x f = \xi.$ 

Let  $\mathbf{Imm}^1(X,Y)$  denote the space of pair (f,f') where  $f:X\to Y$  is an immersion and f' is a section of  $f^*(TY)\to X$  with the property that  $f^{'}(x)\ni \mathrm{Ran}(d_xf)$  and let  $\mathbf{Imm}^1_*(X,Y)$  denote the based version. Here is the proof of the covering homotopy property of the natural map

$$\pi: \mathbf{Imm}(D^k, \mathbb{R}^n) \to \mathbf{Imm}^1(S^{k-1}, \mathbb{R}^n)$$

where 
$$\pi(f) = (f|_{S^{k-1}}, \frac{\partial f}{\partial n}|_{S^{k-1}}).$$

The idea of the proof is the following. The condition of being an immersion is open and there is certainly a section of  $\pi$  (indeed linear) if we disregard the immersion condition so we can alway lift a given a homotopy for a short time where the time depends on how close to failing to be an immersion the time zero lift is and on how big the derviatives of the section are. Smale's trick is morally to essentially homotope the time zero lift to be very much inside the space of immersion. Then he can lift the homotopy a fixed amount along the time parameter in the homotopy See "The classification of immersions of spheres in Euclidean Spaces" by Stephen Smale in the Annals of Mathematics Vol. 69, No. 2, March 1959, pg 327.
