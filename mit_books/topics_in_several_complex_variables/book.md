## 18.117 Lecture Notes

Victor Guillemin and Jonathan Campbell August 19, 2005

## Chapter 1

# Several Complex Variables

#### Lecture 1

Lectures with Victor Guillemin, Texts:

Hormander: Complex Analysis in Several Variables

Griffiths: Principles in Algebraic Geometry

Notes on Elliptic Operators

No exams, 5 or 6 HW's.

Syllabus (5 segments to course, 6-8 lectures each)

- 1. Complex variable theory on open subsets of  $\mathbb{C}^n$ . Hartog, simply pseudoconvex domains, inhomogeneous C.R.
- 2. Theory of complex manifolds, Kaehler manifolds
- 3. Basic theorems about elliptic operators, pseudo-differential operators
- 4. Hodge Theory on Kaehler manifolds
- 5. Geometry Invariant Theory.

#### 1 Complex Variable and Holomorphic Functions

U an open set in  $\mathbb{R}^n$ , let  $C^{\infty}(U)$  denote the  $C^{\infty}$  function on U. Another notation for continuous function: Let A be any subset of  $\mathbb{R}^n$ ,  $f \in C^{\infty}(A)$  if and only  $f \in C^{\infty}(U)$  with  $U \supset A$ , U open. That is, f is  $C^{\infty}$  on A if it can be extended to an open set around it.

As usual, we will identify  $\mathbb{C}$  with  $\mathbb{R}^2$  by  $z\mapsto (x,y)$  when z=x+iy. On  $\mathbb{R}^2$  the standard de Rham differentials are dx,dy. On  $\mathbb{C}$  we introduce the de Rham differentials

$$dz = dx + idy$$
  $d\bar{z} = dx - idy$ 

Let U be open in  $\mathbb{C}$ ,  $f \in C^{\infty}(U)$  then the differential is given as follows

$$df = \frac{\partial f}{\partial x}dx + \frac{\partial f}{\partial y}dy = \frac{\partial f}{\partial x}\left(\frac{dz + d\bar{z}}{2}\right) + \frac{\partial f}{\partial y}\left(\frac{dz - d\bar{z}}{2i}\right)$$
$$= \frac{1}{2}\left(\frac{\partial f}{\partial x} - i\frac{\partial f}{\partial y}\right)dz + \frac{1}{2}\left(\frac{\partial f}{\partial x} + i\frac{\partial f}{\partial y}\right)d\bar{z}$$

If we make the following definitions, the differential has a succinct form

$$\frac{\partial f}{\partial z} = \frac{1}{2} \left( \frac{\partial f}{\partial x} - i \frac{\partial f}{\partial y} \right) \qquad \frac{\partial f}{\partial \bar{z}} = \frac{1}{2} \left( \frac{\partial f}{\partial x} + i \frac{\partial f}{\partial y} \right)$$

SO

$$df = \frac{\partial f}{\partial z}dz + \frac{\partial f}{\partial \bar{z}}d\bar{z}.$$

We take this to be the definition of the differential operator.

**Definition.**  $f \in \mathcal{O}(U)$  (the holomorphic functions) iff  $\partial f/\partial \bar{z} = 0$ . So if  $f \in \mathcal{O}(U)$  then  $df = \frac{\partial f}{\partial z}dz$ .

#### Examples

1.  $z \in \mathcal{O}(U)$ 

2.  $f, g \in C^{\infty}(U)$  then

$$\frac{\partial f}{\partial \bar{z}} f g = \frac{\partial f}{\partial \bar{z}} g + f \frac{\partial g}{\partial \bar{z}}$$

so if  $f, g \in \mathcal{O}(U)$  then  $fg \in \mathcal{O}(U)$ .

- 3. By the above two, we can say  $z, z^2, \ldots$  and any polynomial in z is in  $\mathcal{O}(U)$
- 4. Consider a formal power series  $f(z) \sim \sum_{i=1}^{\infty} a_i z^i$  where  $|a_i| \leq (\text{const}) R^{-i}$ . Then if  $D = \{|z| < R\}$  the power series converges uniformly on any compact set in D, so  $f \in C(D)$ . And by term-by-term differentiation we see that the differentiated power series converges, so  $f \in C^{\infty}(D)$ , and the differential w/ respect to  $\bar{z}$  goes to 0, so  $f \in \mathcal{O}(D)$ .
- 5.  $a \in C$ ,  $f(z) = \frac{1}{z-a} \in C^{\infty}(C \{a\})$ .

#### Cauchy Integral Formula

Let U be an open bounded set in  $\mathbb{C}$ ,  $\partial U$  is smooth,  $f \in C^{\infty}(\overline{U})$ . Let u = fdz by Stokes

$$\int_{\partial U} f dz = \int_{U} du \qquad du = \frac{\partial f}{\partial z} dz \wedge dz + \frac{\partial f}{\partial \bar{z}} d\bar{z} \wedge dz$$

so

$$\int_{\partial U} f dz = \int_{U} du = \int_{U} \frac{\partial f}{\partial \bar{z}} d\bar{z} \wedge dz.$$

Now, take  $a \in U$  and remove  $D_{\epsilon} = \{|z - a| < \epsilon\}$ , and let the resulting region be  $U_{\epsilon} = U - \overline{D}_{\epsilon}$ . Replace f in the above by  $\frac{f}{z-a}$ . Note that  $(z-a)^{-1}$  is holomorphic. We get

$$\int_{\partial U_{\epsilon}} \frac{f}{z - a} dz = \int_{U_{\epsilon}} \frac{\partial f}{\partial \overline{z}} \frac{1}{z - a} d\overline{z} \wedge dz$$

Note: The boundary of U is oriented counter-clockwise, and the inner boundary  $D_{\epsilon}$  is oriented clockwise. When orientations are taken into account the above becomes

$$\int_{\partial U} \frac{f}{z - a} dz - \int_{\partial D_{\epsilon}} \frac{f(z)}{z - a} dz = \int_{U_{\epsilon}} \frac{\partial f}{\partial \bar{z}} \frac{1}{z - a} d\bar{z} \wedge dz$$
 (1.1)

The second integral, with the change of coordinates  $z = a + \epsilon e^{i\theta}$ ,  $dz = i\epsilon e^{i\theta}$ ,  $\frac{dz}{z-a} = id\theta$ . This gives

$$\int_{\partial D_{\epsilon}} \frac{f(z)}{z - a} dz = i \int_{0}^{2\pi} f(a + e^{i\theta}) d\theta.$$

Now we look at what happens when  $\epsilon \to 0$ . Well,  $\frac{1}{z-a} \in \mathcal{L}^1(U)$ , so by Lebesgue dominated convergence if we let  $U_{\epsilon} \to U$ , and the integral remians unchanged. On the left hand side we get  $-if(a)2\pi$ , and altogether we have

$$2\pi i f(a) = \int_{U} \frac{f}{z - a} dz + \int_{U} \frac{\partial f}{\partial \bar{z}} \frac{1}{z - a} dz \wedge d\bar{z}$$

In particular, if  $f \in \mathcal{O}(U)$  then

$$2\pi i f(a) = \int_{\partial U} \frac{f}{z - a} dz$$

Applications:

 $f \in C^{\infty}(\overline{U}) \cap \mathcal{O}(U)$ , take  $a \rightsquigarrow z, z \rightsquigarrow \eta$  then just rewriting

$$2\pi i f(z) = \int_{\partial U} \frac{f(\eta)}{\eta - z} d\eta$$

If we let  $U = \{D : |z| < R\}$ . Then

$$\frac{1}{\eta - z} = \frac{1}{\eta \left(1 - \frac{z}{\eta}\right)} = \frac{1}{\eta} \sum_{k=0}^{\infty} \frac{z^k}{\eta^k}$$

and since on boundary  $|\eta| = R$ , |z| < R so the series converges uniformly on compact sets, we get

$$\int_{\partial U} \frac{f(\eta)}{\zeta - z} d\eta = \sum_{k=0}^{\infty} a_k z^k \qquad a_k = \int_{|\eta| = R} \frac{f(\eta)}{\eta^{k+1}} d\eta$$

or  $a_k = \frac{1}{k!} \frac{\partial^k}{\partial z^k} f(0)$ . This is the holomorphic Taylor expansion. Now if we take  $z \leadsto z - a$ , D: |z - a| < R,  $f \in \mathcal{O}(U) \cap C^{\infty}(\overline{U})$  then

$$f(z) = \sum a_k (z - a)^k$$
  $a_k = \frac{1}{k!} \frac{\partial^k}{\partial z^k} f(a)$ 

We can apply this a prove a few theorems.

**Theorem.** U a connected open set in  $\mathbb{C}$ .  $f,g \in \mathcal{O}(U)$ , suppose there exists an open subset V of U on which f = g. We can conclude  $f \equiv g$ , this is unique analytic continuation.

*Proof.* W set of all points  $a \in U$  where

$$\frac{\partial^k f}{\partial z^k}(a) = \frac{\partial^k g}{\partial z^k}$$
  $k = 0, 1, \dots$ 

holds. Then W is closed, and we see that W is also open, so W = U.

#### Lecture 2

Cauchy integral formula again. U an open bounded set in  $\mathbb{C}$ ,  $\partial U$  smooth,  $f \in C^{\infty}(\overline{U}), z \in U$ 

$$f(z) = \frac{1}{2\pi i} \int_{\partial U} \frac{f(\eta)}{\eta - z} d\eta + \frac{1}{2\pi i} \int_{U} \frac{\partial f}{\partial \bar{\eta}}(\eta) \frac{1}{\eta - z} d\eta \wedge d\bar{\eta}$$

the second term becomes 0 when f is holomorphic, i.e. the area integral vanishes, and we get

$$f(z) = \frac{1}{2\pi i} \int_{\partial U} \frac{f(\eta)}{\eta - z} d\eta$$

Now take  $D: |z-a| < \epsilon, f \in \mathcal{O}(D) \cap C^{\infty}(\overline{D})$ , then

$$f(a) = \frac{1}{2\pi} \int_0^{2\pi} f(a + \epsilon e^{i\theta}) d\theta$$

More applications:

**Theorem (Maximum Modulus Principle).** U any open connected set in  $\mathbb{C}$ ,  $f \in \mathcal{O}(U)$  then if |f| has a local maximum value at some point  $a \in U$  then f has to be constant.

First, a little lemma.

**Lemma.** If  $f \in \mathcal{O}(U)$  and  $Ref \equiv 0$ , then f is constant.

*Proof.* Trivial consequence of the definition of holomorphic.

Proof of Maximum Modulus Principle. Assume f(a) is positive (we can do this by a trivial normalization operation). Let u(z) = Re f. Now from above

$$f(a) = \frac{1}{2\pi} \int_0^{2\pi} f(a + \epsilon e^{i\theta}) d\theta$$

The LHS is real valued and trivially

$$f(a) = \frac{1}{2\pi} \int_0^{2\pi} f(a)d\theta$$

we subtract the above 2 and we get

$$0 = \int_0^{2\pi} f(a) - u(a + \epsilon e^{\theta}) d\theta.$$

When  $\epsilon$  is sufficiently small, since a is a local maximum, the integral is greater than 0,  $f(a) = u(a + \epsilon e^{i\theta})$  so Re f is constant in a neighborhood of a and we can normalize and assume Re f = 0 near a, so by analytic continuation f is constant on U.

#### Inhomogeneous CR Equation

Consider U an open bounded subset of  $\mathbb{C}$ ,  $\partial U$  a smooth boundary,  $g \in C^{\infty}(\overline{U})$ . The Inhomogeneous CR equation is the following PDE: find  $f \in C^{\infty}(U)$  such that

$$\frac{\partial f}{\partial \bar{z}} = g$$

The question is, does there exists a solution for arbitrary g?

First, consider another, simpler version of CR with  $g \in C_0^{\infty}(\mathbb{C})$ . Does there exists  $f \in C^{\infty}(\mathbb{C})$  such that  $\partial f/\partial \bar{z} = g$ ?

**Lemma.** We claim the function f defined by the integral

$$f(z) = \frac{1}{2\pi i} \int \frac{g(\eta)}{\eta - z} d\eta \wedge d\bar{\eta}$$

is in  $C^{\infty}(\mathbb{C})$  and satisfies  $\partial f/\partial \bar{z} = g$ .

*Proof.* Perform the change of variables  $w=z-\eta$ ,  $dw=-d\eta$ ,  $d\bar{w}=-d\bar{\eta}$  and  $\eta=z-w$  then the integral above becomes

$$-\int \frac{g(z-w)}{w} dw \wedge d\bar{w} = f(z)$$

Now it is clear that  $f \in C^{\infty}(\mathbb{C})$ , because if we take  $\partial/\partial z$ , we can just keep differentiating under the integral. And now

$$\frac{\partial f}{\partial z} = -\frac{1}{2\pi i} \int \frac{\left(\frac{\partial g}{\partial \bar{z}}\right)(z-w)}{w} dw \wedge d\bar{w} = \frac{1}{2\pi i} \int \frac{\left(\frac{\partial g}{\partial \bar{\eta}}\right)(\eta)}{\eta - z} d\eta \wedge d\bar{\eta}$$

Let A = supp g, so A is compact, then there exists U open and bounded such that  $\partial U$  is smooth and  $A \subset U$ . For  $g \in C^{\infty}(\overline{U})$  write down using the Cauchy integral formula

$$g(z) = \frac{1}{2\pi i} \int_{\partial U} \frac{g(\eta)}{\eta - z} d\eta + \frac{1}{2\pi i} \int_{U} \frac{\partial g}{\partial \bar{\eta}}(\eta) \frac{d\eta \wedge d\bar{\eta}}{\eta - z}$$

On  $\partial U$ , g is identically 0, so the first integral is 0. For the second integral we replace A by the entire complex plane, so

$$g(z) = \frac{1}{2\pi i} \int_{\mathbb{C}} \frac{\partial g}{\partial \bar{\eta}}(\eta) \frac{d\eta \wedge d\bar{\eta}}{\eta - z}$$

which is the expression for  $\frac{\partial f}{\partial \bar{z}}$ 

Now, we want to get rid of our compactly supported criterion. Let U be bounded,  $\partial U$  smooth and  $g \in C^{\infty}(\overline{U}), \ \frac{\partial f}{\partial \overline{z}} = g.$ 

Make the following definition

$$f(z) := \frac{1}{2\pi i} \int_{U} \frac{g(\eta)}{\eta - z} d\eta \wedge d\bar{\eta}$$

Take  $a \in U$ , D an open disk about  $a, \overline{D} \subset U$ . Check that  $f \in C^{\infty}$  on D and that  $\partial f/\partial \overline{z} = g$  on D. Since ais arbitrary, if we can prove this we are done. Take  $\rho \in C_0^{\infty}(U)$  so that  $\rho \equiv 1$  on a neighborhood of  $\overline{D}$ , then

$$f(z) = \underbrace{\frac{1}{2\pi i} \int \frac{\rho(\eta)g(\eta)}{\eta - z} d\eta \wedge d\bar{\eta}}_{I} + \underbrace{\frac{1}{2\pi i} \int (1 - \rho) \frac{g(\eta)}{\eta - z} d\eta \wedge d\bar{\eta}}_{II}$$

The first term, I, is in  $C_0^{\infty}(\mathbb{C})$ , so I is  $C^{\infty}$  on  $\mathbb{C}$  and  $\partial I/\partial \bar{z} = \rho g$  on  $\mathbb{C}$  and so is equal to  $g|_{D}$ . We claim that  $II|_D$  is in  $\mathcal{O}(D)$ . The Integrand is 0 on an open set containing D, so  $\partial II/\partial \bar{z} = 0$  on D.

We conclude that  $\partial f(z)/\partial \bar{z} = g(z)$  on D. (The same result could have just been obtained by taking a partition of unity)

#### Transition to Several Complex Variables

We are now dealing with  $\mathbb{C}^n$ , coordinatized by  $z=(z_1,\ldots,z_n)$ , and  $z_k=x_k+iy_k$  and  $dz_k=dx_k+idy_k$ . Given U open in  $\mathbb{C}^n$ ,  $f\in C^\infty(U)$  we define

$$\frac{\partial f}{\partial z_k} = \frac{1}{2} \left( \frac{\partial f}{\partial x_k} - i \frac{\partial f}{\partial y_k} \right) \qquad \frac{\partial f}{\partial \bar{z}_k} = \frac{1}{2} \left( \frac{\partial f}{\partial x_k} + i \frac{\partial f}{\partial y_k} \right)$$

So the de Rham differential is defined by

$$df = \sum \left( \frac{\partial f}{\partial x_i} dx_i + \frac{\partial y}{\partial y_i} dy_i \right) = \sum \frac{\partial f}{\partial z_k} dz_k + \sum \frac{\partial f}{\partial \bar{z}_k} d\bar{z}_k := \partial f + \bar{\partial} f$$

so  $df = \partial f + \overline{\partial} f$ .

Let  $\Omega^{1}(U)$  be the space of  $C^{\infty}$  de Rham 1-forms, and  $u \in \Omega^{1}(U)$  then

$$u = u' + u'' = \sum a_i dz_i + \sum b_i d\bar{z}_i$$
  $a_i, b_i \in C^{\infty}(U)$ 

we introduce the following notation

$$\Omega^{1,0} = \left\{ \sum a_k dz_k, a_k \in C^{\infty}(U) \right\}$$
  
$$\Omega^{0,1} = \left\{ \sum b_k d\bar{z}_k, b_k \in C^{\infty}(U) \right\}$$

and therefore there is a decomposition  $\Omega^1(U) = \Omega^{1,0}(U) \oplus \Omega^{0,1}(U)$ . We can rephrase a couple of the lines above in the following way:  $df = \partial f + \overline{\partial} f$ ,  $\partial f \in \Omega^{1,0}$ ,  $\overline{\partial} f \in \Omega^{0,1}$ .

**Definition.**  $f \in \mathcal{O}(U)$  if  $\overline{\partial} f = 0$ , i.e. if  $\partial f/\partial \bar{z}_k = 0$ ,  $\forall k$ .

**Lemma.** For  $f, g \in C^{\infty}(U)$ ,  $\overline{\partial} f g = f \overline{\partial} g + g \overline{\partial} f$ , thus  $f g \in \mathcal{O}(U)$ .

Obviously,  $z_1, \ldots, z_n \in \mathcal{O}(U)$ .

If  $\alpha=(\alpha_1,\ldots,\alpha_n)$ ,  $\alpha_i\in \bar{\mathbb{N}}$ , then  $z^\alpha=z_1^{\alpha_1}\ldots z_n^{\alpha_n}$  and  $z^\alpha\in \mathcal{O}(\mathbb{C})$ . Then

$$p(z) = \sum_{|\alpha| \le N} a_{\alpha} z^{\alpha} \in \mathcal{O}(\mathbb{C}^n)$$

Even more generally, suppose we have the formal power series

$$f(z) = \sum_{\alpha} a_{\alpha} z^{\alpha}$$

and  $|a_{\alpha}| \leq CR_1^{-\alpha_1} \dots R_n^{-\alpha_n}$ . Then let  $D_k : |z_k| < R_k$  and  $D = D_1 \times \dots \times D_n$  then f(z) converges on D and uniformly on compact sets in D, and by differentiation we see that  $f \in \mathcal{O}(D)$ .

**Definition.** Let  $D_i : |z - a_i| < R_n$ , then open set  $D_1 \times \cdots \times D_n$  is called a **polydisk**.

#### Lecture 3

#### Generalizations of the Cauchy Integral Formula

There are many, many ways to generalize this, but we will start with the most obvious

**Theorem.** Let  $D \subseteq \mathbb{C}^n$  be the polydisk  $D = D_1 \times \cdots \times D_n$  where  $D_i : |z_i| < R_i$  and let  $f \in \mathcal{O}(D) \cap C^{\infty}(\overline{D})$  then for any point  $a = (a_1, \ldots, a_n)$ 

$$f(a) = \left(\frac{1}{2\pi i}\right)^n \int_{\partial D_1 \times \dots \times \partial D_n} \frac{f(z_1, \dots, z_n)}{(z_1 - a_1) \dots (z_n - a_n)} dz_1 \wedge \dots \wedge dz_n$$

*Proof.* We will prove by induction, but only for the case n=2, the rest follow easily. We do the Cauchy Integral formula in each variable separately

$$f(z_1, a_2) = \frac{1}{2\pi i} \int_{\partial D_2} \frac{f(z_1, z_2)}{z_2 - z_2} dz_1 \qquad f(a_1, z_n) = \frac{1}{2\pi i} \int_{\partial D_2} \frac{f(z_1, z_2)}{(z_1 - a_1)} dz_2$$

Then just plug the first into the second.

Applications: First make the following changes  $a_i \rightsquigarrow z_i, z_i \rightsquigarrow \eta_i$ , then

$$f(z_1, \dots, z_n) = \left(\frac{1}{2\pi i}\right)^n \int_{\partial D_1 \times \dots \times \partial D_n} \frac{f(\eta)}{(\eta_1 - z_1) \dots (\eta_n - z_n)} d\eta_1 \wedge \dots \wedge d\eta_n$$

As before in the single variable case we make the following replacements

$$\frac{1}{\prod(\eta_i - z_i)} = \frac{1}{\eta_1 \dots \eta_n} \prod \frac{1}{1 - \frac{z_i}{\eta_i}} = \frac{1}{\eta_1 \dots \eta_n} \sum_{\alpha} \frac{z^{\alpha}}{\eta^{\alpha}}$$

for  $\eta \in \partial D_1 \times \cdots \times \partial D_n$  we have uniform converge for z on compact subsets of D. So by the Lebesgue dominated convergence theorem

$$f(z) = \sum_{\alpha} a_{\alpha} z^{\alpha} \qquad a_{\alpha} = \left(\frac{1}{2\pi i}\right)^{n} \int \frac{f(\eta)}{\eta_{1}^{\alpha_{1}+1} \dots \eta_{n}^{\alpha_{n}+1}} d\eta_{1} \wedge \dots \wedge d\eta_{n}$$

**Theorem.** U open in  $\mathbb{C}^n$ ,  $f \in \mathcal{O}(U)$ ,  $a \in U$  and D a polydisk centered at a with  $\overline{D} \subseteq U$  then on D we have

$$f(z) = \sum_{\alpha} a_{\alpha} (z_1 - a_1)^{\alpha_1} \dots (z_n - a_n)^{\alpha_n}$$

(we will call this (\*) from now on)

*Proof.* Apply the previous little theorem to f(z-a).

Note we can check by differentiation that the coefficients are  $a_{\alpha} = \frac{1}{\alpha!} \partial f / \partial z^{\alpha}(a)$ .

**Theorem.** U is a connected open set in  $\mathbb{C}^n$  with  $f, g \in \mathcal{O}(U)$ . If f = g on an open subset  $V \subset U$  then f = g on all of U.

*Proof.* As in one dimension.  $\Box$ 

**Theorem (Maximum Modulus Principle).** U is a connected open set in  $\mathbb{C}^n$ ,  $f \in \mathcal{O}(U)$ . If |f| achieves a local maximum at some point  $a \in U$  then f is constant

*Proof.* Left as exercise. 
$$\Box$$

As a reminder:

**Theorem.** Let  $g \in C_0^{\infty}(\mathbb{C})$  then if f is the function

$$f(z) = \frac{1}{2\pi i} \int_{\mathbb{C}} \frac{g(\eta)}{\eta - z} d\eta \wedge d\bar{\eta}$$

then  $f \in C^{\infty}(\mathbb{C})$  and  $\partial f/\partial \bar{z} = g$ .

What about the *n*-dimensional case? That is, given  $h_i \in C_0^{\infty}(\mathbb{C}^n)$ , i = 1, ..., n does there exist  $f \in C^{\infty}(\mathbb{C}^n)$  such that  $\frac{\partial f}{\partial \bar{z}_i} = h_i$ , i = 1, ..., n?

There clearly can't always be a solution because we have the integrability conditions

$$\frac{\partial h_i}{\partial \bar{z}_j} = \frac{\partial h_j}{\partial \bar{z}_i}$$

Theorem (Multidimensional Inhomogeneous CR equation). If the  $h_i$ 's satisfy these integrability conditions then there exists an  $f \in C^{\infty}(\mathbb{C}^n)$  with  $\partial f/\partial \bar{z}_i = h_i$ . And in fact such a solution is given by

$$f(z_1, \dots, z_n) = \frac{1}{2\pi i} \int_{\mathbb{C}} \frac{h_1(\eta_1, z_2, \dots, z_n)}{(\eta_1 - z_1)} d\eta_1 \wedge d\bar{\eta}_1$$

*Proof.* This just says for get about everything except the first variable.

Clearly  $f \in C^{\infty}(\mathbb{C}^n)$  and  $\partial f/\partial \bar{z}_1 = h_1$ . Now  $\partial f/\partial \bar{z}_i$  we compute under the integral sign and we get

$$\frac{\partial}{\partial \bar{z}_i} h_1(\eta_1, z_2, \dots, z_n) \frac{1}{\eta_i - z_i} \in L'(\eta_1)$$

(so it is legitimate to differentiate under the integral sign). Now

$$\frac{\partial f}{\partial \bar{z}_i} = \frac{1}{2\pi i} \int \frac{\partial h_1}{\partial \bar{z}_j} (\eta_1, z_2, \dots, z_n) \frac{d\eta_1 \wedge d\bar{\eta}_1}{\eta_1 - z_1}$$

$$= \frac{1}{2\pi i} \int \frac{\partial h_j}{\partial \eta_1} (\eta_1, z_2, \dots, z_n) \frac{d\eta_1 \wedge d\bar{\eta}_1}{\eta_1 - z_1}$$

$$= h_j(z_1, \dots, z_n)$$

The second set is by integrability conditions, and the lat is by the previous lemma. QED.

Let  $K \in \mathbb{C}^n$  be a compact st. Suppose  $\mathbb{C}^n - K$  is connected. Suppose  $h_i \in C_0^{\infty}(\mathbb{C}^n)$  are supported in K. **Theorem.** If f is the function (\*) then supp  $f \subseteq K$  (unique to higher dimension). So not only do we have a solution to the ICR eqn, it is compactly supported.

*Proof.* By (\*)  $f(z_1, \ldots, z_n)$  is identically 0 when  $(z_i) \gg 0$ , i > 1, because  $h_i$  is compactly supported. Also, since supp  $h_i \subseteq K$  and  $\partial f/\partial \bar{z}_i = h_i$  we have that  $\partial f/\partial \bar{z}_i = 0$  on  $\mathbb{C}^n - K$ , so  $f \in \mathcal{O}(\mathbb{C}^n - K)$ . The uniqueness of analytic continuation we have  $f \equiv 0$  on  $\mathbb{C}^n - K$  (used that  $\mathbb{C}^n - K$  is connected)

**Theorem (Hartog's Theorem).** Let  $K \subseteq U$ ,  $U \subset \mathbb{C}^n$  is open and connected. Suppose that U - K is connected. Let  $f \in \mathcal{O}(U - K)$  then f extends holomorphically to all of U. THIS IS A PROPERTY SPECIFIC TO HIGHER DIMENSIONAL SPACES.

*Proof.* Let  $K_1 \subseteq U$  so that  $K \subset \operatorname{Int} K_1$ ,  $U - K_1$  is connected. Choose  $\varphi \in C^{\infty}(\mathbb{C}^n)$  such that  $\varphi \equiv 1$  on K and supp  $\varphi \subset \operatorname{Int} K_1$ . Let

$$v = \begin{cases} (1 - \varphi)f & \text{on } U - K \\ 0 & \text{on } K \end{cases}$$

then  $v \in C^{\infty}(U)$ . And  $v \equiv f$  on U - K.  $h_i = \frac{\partial}{\partial \bar{z}_i} v$ , i = 1, ..., n. One  $U - K_1$ ,  $v = f \in \mathcal{O}(U - K_1)$  so  $h_i = \frac{\partial}{\partial \bar{z}_i} f$  on  $U - K_1$  and f is holomorphic, so this is 0, thus  $h_i \in C_0^{\infty}(\mathbb{C}^n)$ , supp  $h_i \subseteq K_1$  and  $\frac{\partial h_i}{\partial \bar{z}_j} = \frac{\partial h_j}{\partial \bar{z}_j}$ , so  $\exists w \in C_0^{\infty}(\mathbb{C}^n)$  such that  $\frac{\partial w}{\partial \bar{z}_i} = h_i$  and supp  $w \subseteq K_1$ . Take g = v - w so  $w \equiv 0$  on  $\mathbb{C}^n - K$ , v = f on  $\mathbb{C}^n - K_1$ , so g = f on  $\mathbb{C}^n - K$  and by construction

$$\frac{\partial g}{\partial \bar{z}_i} = \frac{\partial v}{\partial \bar{z}_i} - \frac{\partial w}{\partial \bar{z}_i} = h_i - \frac{\partial}{\partial \bar{z}_i} w = 0$$

so  $g \in \mathcal{O}(U)$  and g = f on  $U - K_1$ ,  $f \in C^{\infty}(U - K)$ , since U - K connected, by uniqueness of analytic continuation g = f on U - K, so g is holomorphic continuation of f onto all of U.

#### Lecture 4

#### Applying Hartog's Theorem

Let  $X \subset \mathbb{C}^n$  be an algebraic variety,  $\operatorname{cod}_{\mathbb{C}} X = 2$ . And suppose  $f \in \mathcal{O}(\mathbb{C}^n - X)$ . Then f extends holomorphically to  $f \in \mathcal{O}(\mathbb{C}^n)$ .

Sketch of Proof: Cut X by a complex plane  $(P = \mathbb{C}^2)$  transversally. Then  $f \mid_{P} \in \mathcal{O}(P - \{p\})$  so by hartog,  $f|_{P} \in \mathcal{O}(P)$ . Do this argument for all points, so f has to be holomorphic on  $f \in \mathcal{O}(\mathbb{C}^n)$ .

We have to be a little more careful to actually prove it, but this is just an example of how algebraic geometers use this.

#### Dolbeault Complex and the ICR Equation

Let U be an open subset of  $\mathbb{C}^n$ ,  $\omega \in \Omega^1(U)$ , then we discussed how  $\Omega^1(U) = \Omega^{1,0} \oplus \Omega^{0,1}$ .

There is a similar story for higher degree forms.

Take r > 1, p + q = r. Then  $\omega \in \Omega^{p,q}(U)$  if  $\omega$  is in the following form

$$\omega = \sum f_{I,J} dz_I \wedge d\bar{z}_J \qquad f_{I,J} \in C^{\infty}(U)$$

and  $dz_I = dz_{i_1} \wedge \cdots \wedge dz_{i_p}$ ,  $d\bar{z}_J = d\bar{z}_{j_1} \wedge \cdots \wedge d\bar{z}_{j_q}$  are standard multi-indices. Then

$$\Omega^r = \bigoplus_{p+q=r} \Omega^{p,q}(U)$$

Now suppose we have  $\omega \in \Omega^{p,q}(U)$ ,  $\omega = \sum_i f_{I,J} dz_I \wedge d\bar{z}_J$  then the de Rham differential is written as follows

$$dw = \sum df_{IJ} \wedge dz_I \wedge dz_J = \sum \frac{\partial f_{I,J}}{\partial z_i} dz_i \wedge dz_I \wedge dz_J + \sum \frac{\partial f}{\partial \bar{z}_i} d\bar{z}_j \wedge dz_I \wedge d\bar{z}_J$$

The first term we define to be  $\partial \omega$  and the second to be  $\bar{\partial} \omega$ , i.e.

$$\partial \omega = \sum \frac{\partial f_{I,J}}{\partial z_i} dz_i \wedge dz_I \wedge dz_J$$
$$\overline{\partial} \omega = \sum \frac{\partial f_{I,J}}{\partial \overline{z}_i} d\overline{z}_j \wedge dz_I \wedge d\overline{z}_J$$

Now we may write  $d\omega = \partial\omega + \overline{\partial}\omega$ , and note that  $\partial\omega \in \Omega^{p+1,q}(U)$  and  $\overline{\partial}\omega \in \Omega^{p,q+1}(U)$ .

$$d^2 = 0 = \partial^2 \omega + \partial \overline{\partial} \omega + \overline{\partial} \overline{\partial} \omega + \overline{\partial}^2 \omega$$

and the terms in the above expression are of bidegree

$$(p+2,q)+(p+1,q+1)+(p+1,q+1+(p,q+2)$$

so  $\overline{\partial}^2 = \partial^2 = 0$  and  $\partial \overline{\partial} + \overline{\partial} \partial = 0$ , so  $\partial$ ,  $\overline{\partial}$  are anti-commutative. We now have that the de Rham complex  $(\Omega^*(U), d)$  is a bicomplex, i.e. d splits into two different coboundary operators that anticommute.

The rows of the bicomplex are given by

$$\Omega^{0,q} \xrightarrow{\quad \partial \quad} \Omega^{1,q} \xrightarrow{\quad \partial \quad} \Omega^{2,q} \xrightarrow{\quad \partial \quad} \cdots$$

and the columns are given by

$$\Omega^{p,0} \xrightarrow{\overline{\partial}} \Omega^{p,1} \xrightarrow{\overline{\partial}} \Omega^{p,2} \xrightarrow{\overline{\partial}} \cdots$$

For the moment, we focus on the columns, more specifically the extreme left column.

**Definition.** The **Dolbeault Complex** is the following complex

$$C^{\infty}(U) = \Omega^{0} = \Omega^{0,0}(U) \xrightarrow{\overline{\partial}} \Omega^{0,1}(U) \xrightarrow{\overline{\partial}} \Omega^{0,2}(U) \xrightarrow{\overline{\partial}} \cdots$$

A basic problem in several complex variables is to answer the question: For what open sets U in  $\mathbb{C}^n$  is this complex exact?

Today we will show that the Dolbeault complex is locally exact (actually, we will prove something a little stronger)

**Theorem (1).** Let U and V be polydisks with  $\overline{V} \subset U$ . Then if  $\omega \in \Omega^{0,q}(U)$  and  $\overline{\partial}\omega = 0$  then there exists  $\mu \in \Omega^{0,q-1}(V)$  with  $\overline{\partial}\mu = \omega$  on V.

This just says that if we shrink the domain a little, the exactness holds.

To prove this theorem we will use a trick similar to showing that the real de Rham complex is locally exact.

First, we define a new set

**Definition.**  $\Omega^{0,q}(U)_k$ ,  $0 \le k \le n$  is given by the following rule:  $\omega \in \Omega^{0,q}(U)_k$  if and only if

$$\omega = \sum f_I d\bar{z}_I \qquad d\bar{z}_I = d\bar{z}_{i_1} \wedge \dots \wedge d\bar{z}_{i_q}, \quad 1 \le i_1 \le \dots \le i_q \le k$$

This is just a restriction on the  $\bar{z}_j$ 's that may be present. For example  $\Omega^{0,q}(U)_0 = \{0\}$  and  $\Omega^{0,q}(U)_n = \Omega^{0,q}(U)$ .

An important property of this space follows. If  $\omega \in \Omega^{0,q}(U)_k$  then

$$\overline{\partial}\omega = \sum_{l>k} \frac{\partial f_I}{\partial \bar{z}_l} d\bar{z}_l \wedge d\bar{z}_I + \Omega^{0,q+1}(U)_k$$

so if  $\overline{\partial}\omega = 0$  then  $\partial f_I/\partial \bar{z}_l = 0$ , for l > k i.e.  $f_I$  is holomorphic.

Let V, U be polydisks,  $\overline{V} \subset U$ . Choose a polydisk W so that  $\overline{V} \subset W$  and  $\overline{W} \subset U$ .

**Theorem (2).** If  $\omega \in \Omega^{0,q}(U)_k$  and  $\overline{\partial}\omega = 0$  then there exists  $\beta \in \Omega^{0,q-1}(W)_{k-1}$  such that  $\omega - \overline{\partial}\beta \in \Omega^{0,q}(W)_{k-1}$ .

We claim that Theorem 2 implies Theorem 1 (left as exercise) Before we prove theorem 2, we need a lemma

**Lemma.** (ICR in 1D) If  $g \in C^{\infty}(U)$  with  $\frac{\partial g}{\partial \bar{z}_l} = 0$ , l > k then there exists  $f \in C^{\infty}(W)$  such that  $\frac{\partial f}{\partial \bar{z}_l} = 0$  for l > k and  $\frac{\partial f}{\partial \bar{z}_k} = g$ .

*Proof.*  $U = U_1 \times \cdots \times U_n$  where  $U_i$  are disks and  $W = W_1 \times \cdots \times W_n$  where  $W_i$  are disks. Let  $\rho \in C_0^{\infty}(U_k)$  so that  $\rho \equiv 1$  on a neighborhood of  $\overline{W}_k$ . Replacing g by  $\rho(z_k)g$  we can assume that g is compactly supported in  $z_k$ .

Choose f to be

$$f = \frac{1}{2\pi i} \int_{\mathbb{C}} \frac{g(z_1, \dots, z_{k-1}, \eta, z_{k+1}, \dots, z_n) d\eta \wedge d\bar{\eta}}{\eta - z_k}$$

We showed before that  $\frac{\partial f}{\partial \bar{z}_k} = g$ . By a change of variable we see that

$$f = -\frac{1}{2\pi i} \int_{\mathbb{C}} \frac{g(z_1, \dots, z_{k-1} z_k - \eta, z_{k+1}, \dots, z_n)}{\eta} d\eta \wedge d\bar{\eta}$$

so  $f \in C^{\infty}(W)$  and clearly  $\frac{\partial f}{\partial \overline{z}_l} = 0, l > k$ . QED.

We may now prove Theorem 2

Proof of Theorem 2.  $\omega \in \Omega^{0,q}(U)_k$ , and  $\overline{\partial}\omega = 0$ . Write

$$\omega = \mu + d\bar{z}_k \wedge \nu \qquad \mu \in \Omega^{0,q}(U)_{k-1}, \nu \in \Omega^{0,q-1}(U)_{k-1}$$

(just decompose  $\omega$ ) and say

$$\nu = \sum g_I d\bar{z}_I, \quad g_I \in C^{\infty}(U), \quad I = (i_1, \dots, i_{q-1}), \quad i_s \le k-1$$

 $\overline{\partial}\omega=0$  tells use that  $\frac{\partial g_I}{\partial \bar{z}_I}=0,\ l>k.$  By the lemma above, there exists  $f_I\in C_0^\infty(W)$  so that

$$\frac{\partial f_I}{\bar{z}_k} = g_I$$
 and  $\frac{\partial f_I}{\partial \bar{z}_l} = 0, \ l > k$ 

Take  $\beta = \sum f_I dz_I$ , then

$$\overline{\partial}\beta = \sum d\bar{z}_k \wedge \frac{\partial f_I}{\partial \bar{z}_k} dz_i + \Omega^{0,q}(W)_{k-1} = dz_k \wedge \nu$$

so  $\omega - \overline{\partial}\beta \in \Omega^{0,q}(W)_{k-1}$ .

**Theorem (3).** Let U be a polydisk then the Dolbeault complex

$$\Omega^{0,0}(U) \xrightarrow{\overline{\partial}} \Omega^{0,1}(U) \xrightarrow{\overline{\partial}} \Omega^{0,2}(U) \xrightarrow{\overline{\partial}} \cdots$$

is exact. That is, you don't have to pass to sub-polydisks.

The above theorem is **EXERCISE 1** 

#### Lecture 5

#### Notes about Exercise 1

**Lemma.** Let U and V be as in Theorem 1 above.  $\beta \in \Omega^{0,q}(U)$ ,  $\overline{\partial}\beta = 0$  then there exists  $\alpha \in \Omega^{0,q-1}(U)$  such that  $\overline{\partial}\alpha = \beta$  on V.

*Proof.* Choose a polydisk W so that  $\overline{V} \subset W$ ,  $\overline{W} \subset U$ . Choose  $\rho \in C_0^{\infty}(W)$  with  $\rho \equiv 1$  on a neighborhood of V. By theorem 1 there exists  $\alpha_0 \in \Omega^{0,q-1}(W)$  so that  $\overline{\partial}\alpha_0 = \beta$  on W. If we take

$$\alpha = \begin{cases} \rho \alpha_0 & \text{on } W \\ 0 & \text{on } U - W \end{cases}$$

then we have a solution.

We claim that the Dolbealt complex is exact on all degrees  $q \geq 2$ .

**Lemma.** Let  $V_0, V_1, V_2, \ldots$  be a sequence of polydisks so that  $\overline{V}_r \subset V_{r+1}$  and  $\bigcup V_1 = U$ . (exhaustion on U by compact polydisk). There exists  $\alpha_i \in \Omega^{0,q+1}(U)$  such that  $\overline{\partial}\alpha_r = \beta$  on  $V_r$  and such that  $\alpha_{r+1} = \alpha_r$  on  $V_{r-1}$ .

Proof. By the previous lemma there exists  $\alpha_r \in \Omega^{0,q-1}(U)$  with  $\overline{\partial}\alpha_r = \beta$  on  $V_r$ . And for  $\alpha_{r+1}, \alpha_r$  on  $V_r$ ,  $\overline{\partial}\alpha_{r+1} = \overline{\partial}\alpha_r = \beta$  on  $V_r$ , so  $\overline{\partial}(\alpha_{r+1} - \alpha_r) = 0$  on  $V_r$ . Now  $q \ge 2$  so we can find  $\gamma \in \Omega^{0,q-1}(U)$  such that  $\overline{\partial}\gamma = \alpha_{r+1} - \alpha_r$  on  $V_{r-1}$ . Then set  $\alpha_{r+1}^{\text{new}} := \alpha_{r+1}^{\text{old}} + \overline{\partial}\gamma$ . So  $\overline{\partial}\alpha_{r+1}^{\text{new}} = \beta$  on  $V_{r+1}$ ,  $\alpha_{r+1}^{\text{new}} = \alpha_r$  on  $V_{r-1}$ .

We get a global solution when we set  $\alpha = \alpha_r$  on  $V_{r-1}$  for all r.

(**EXERCISE** Prove exactness at q = 1, i.e. make this argument work for q = 1.)

What does exactness mean for degree 1? Well

$$\beta \in \Omega^{0,1}(U)$$
  $\beta = \sum f_i d\bar{z}_i$   $f_i \in C^{\infty}(U)$ 

We need to show that there exists  $g \in \Omega^{0,0}(U) = C^{\infty}(U)$  so that  $\overline{\partial}g = \beta$ , i.e.

$$\frac{\partial g}{\partial \bar{z}_i} = f_i \qquad i = 1, \dots, n$$

So the condition that  $\overline{\partial}\beta = 0$  is just the integrability conditions.

So we have to show the following. That there exists a sequence of functions  $g_r \in C^{\infty}(U)$ .  $V_0 \subset V_1 \subset \cdots \subset U$  such that  $\frac{\partial g_r}{\partial \bar{z}_i} = f_i$ ,  $i = 1, \ldots, n$  on  $V_r$  (easy consequence of lemma)

We can no longer say  $g_{r+1} - g_r$  on  $V_{r-1}$ . But we can pick  $g_r$  such that  $|g_{r+1} - g_r| < \frac{1}{2^r}$  on  $V_{r-1}$ .

Hint Choose  $g_r \in C^{\infty}(U)$  such that  $\frac{\partial g_r}{\partial \bar{z}_i} = f_i$  on  $V_r$ . Look at  $g_{r+1} - g_r$  on  $V_r$ . Note that  $\frac{\partial}{\partial \bar{z}_i} (g_{r+1} - g_r) = 0$  on  $V_r$ , so  $g_{r+1} - g_r \in \mathcal{O}(V_r)$ . On  $V_{r-1}$  we can expand by power series to get  $g_{r+1} - g_r = \sum_{\alpha} a_{\alpha} z^{\alpha}$ , and this series is actually uniformly convergent on  $V_{r-1}$ . We try to modify  $g_{r+1}^{\text{old}}$  by setting  $g_{r+1}^{\text{new}} + P_N(z)$ , where  $P_N(z) = \sum_{|\alpha| \leq N} a_{\alpha} z^{\alpha}$ 

(The exercise is due Feb 25th)

#### More on Dolbealt Complex

For polydisks the Dolbealt complex is acyclic (exact). But what about other kinds of open sets? The solution was obtained by Kohn in 1963.

Let U be open in  $\mathbb{C}$ ,  $\varphi: U \to \mathbb{R}$  be such that  $\varphi \in C^{\infty}(U)$ .

**Definition.**  $\varphi$  is strictly pluri-subharmonic if for all  $p \in U$  the hermitian form

$$a \in \mathbb{C}^n \mapsto \sum_{i,j} \frac{\partial^2 \varphi}{\partial z_i \partial \bar{z}_j}(p) a_i \overline{a}_j$$

is positive definite.

(This definition will be important later for Kaehler manifolds)

**Definition.** A  $C^{\infty}$  function  $\varphi: U \to \mathbb{R}$  is an exhaustion function if it is bounded from below and if for all  $c \in \mathbb{C}$ 

$$K_c = \{ p \in U | \varphi(p) < c \}$$

is compact.

**Definition.** U is **pseudoconvex** if it possesses a strictly pluri-subharmonic exhaustion function.

#### Examples

- 1.  $U=\mathbb{C}$ . If we take  $\varphi=|z|^2=z\bar{z}, \frac{\partial \varphi}{\partial z\partial\bar{z}}=1$ .
- 2.  $U = D \subset \mathbb{C}$

$$\varphi = \frac{1}{1 - |z|^2} \qquad \frac{\partial \varphi}{\partial z \partial \bar{z}} = \frac{1 + |z|^2}{(1 - |z|^2)^3} > 0$$

3.  $U \subset \mathbb{C}$ ,  $U = D - \{0\} = D^o$ , i.e. the punctured disk

$$\varphi^o = \frac{1}{1 - |z|^2} + \operatorname{Log} \frac{1}{|z|^2} \qquad \frac{\partial \varphi^o}{\partial z \partial \overline{z}} = \frac{\partial \varphi}{\partial z \partial \overline{z}}$$

because Log is harmonic. Note the extra term in  $\varphi^o$  is so the function will blow up at its point of discontinuity.

4.  $\mathbb{C}^n \supset U = D_1 \times \cdots \times D_n$ , where  $D_i = |z_i|^2 < 1$ . Take

$$\varphi = \sum \frac{1}{1 - |z_i|^2}$$

5.  $\mathbb{C}^n \supset U, D_1^o \times \cdots \times D_k^o \times D_{k+1} \times \cdots \times D_n$ 

$$\varphi^o = \varphi + \sum_{i=1}^k \operatorname{Log} \frac{1}{|z_i|^2}$$

6.  $U \subset \mathbb{C}^n$ ,  $U = B^n$ ,  $|z|^2 = |z_1|^2 + \cdots + |z_n|^2$ .

$$\varphi = \frac{1}{1 - |z|^2} \qquad \frac{\partial^2 \varphi}{\partial z_i \partial \bar{z}_j} = \frac{\delta_{ij}}{(1 + |z|^2)} + \frac{2z_i \bar{z}_j}{(1 - |z|^2)^3}$$

**Theorem.** If  $U_i \subset \mathbb{C}^n$ , i = 1, 2 is pseudo-convex then  $U_1 \cap U_2$  is pseudo-convex

*Proof.* Take  $\varphi_i$  to be strictly pluri-subharmonic exhaustion functions for  $U_i$ . Then set  $\varphi = \varphi_1 + \varphi_2$  on  $U_1 \cap U_w$ .

Punchline:

**Theorem.** The Dolbealt complex is exact on U if and only if U is pseudo-convex.

This takes 150 pages to prove, so we'll just take it as fact.

The Dolbealt complex is the left side of the bi-graded de Rham complex.

There is another interesting complex. For example if we let  $A^0 = \ker \overline{\partial}: \Omega^{p,0} \to \Omega^{p,1}, \ \partial \overline{\partial} + \overline{\partial} \partial = 0$  and  $\omega \in A^r$  then  $\partial \omega \in A^{r+1}$  and we get a complex

$$A^0 \xrightarrow{\partial} A^1 \xrightarrow{\partial} A^2 \xrightarrow{\partial} \cdots$$

#### Lecture 6

#### Review

U open  $\mathbb{C}^n$ . Make the convention that  $\Omega^r(U) = \Omega^r$ . We showed that  $\Omega^r = \bigoplus_{p+q=r} \Omega^{p,q}$ , i.e. its bigraded. And we also saw that  $d = \partial + \overline{\partial}$ , so the coboundary operator breaks up into bigraded pieces.

$$\partial:\Omega^{p,q}\to\Omega^{p+1,q} \qquad \overline{\partial}:\Omega^{p,q}\to\Omega^{p,q+1}$$

 $\omega \in \Omega^r, \mu \in \Omega^s$ . Then

$$d(\omega \wedge \mu) = d\omega \wedge \mu + (-1)^r \omega \wedge d\mu$$

there are analogous formulas for  $\partial$ ,  $\overline{\partial}$ 

$$\overline{\partial}(\omega \wedge \mu) = \overline{\partial}\omega \wedge \mu + (-1)^r \omega \wedge \overline{\partial}\mu$$

Because of bi-grading the de Rham complex breaks into subcomplexes

$$(1)_q: \Omega^{0,q} \xrightarrow{\partial} \Omega^{1,q} \xrightarrow{\partial} \Omega^{2,q} \xrightarrow{\partial} \cdots$$

$$(2)_p: \Omega^{p,0} \xrightarrow{\overline{\partial}} \Omega^{p,1} \xrightarrow{\overline{\partial}} \Omega^{0,2} \xrightarrow{\overline{\partial}} \cdots$$

The Dolbeault complex is  $(2)_0: \Omega^{0,0} \xrightarrow{\overline{\partial}} \Omega^{0,1}$ . Last week we showed that if U is a polydisk then the Dolbeault complex is acyclic.

**Theorem.** If U is a polydisk then complex  $(1)_q$  and  $(2)_p$  are exact for all p,q.

*Proof.* Take  $I=(i_1,\ldots,i_p)$ , define  $\Omega_I^{p,q}:=\Omega^{0,q}\wedge dz_I$ . And  $\omega\in\Omega_I^{p,q}$  if and only if  $\omega=\mu\wedge dz_I$ ,  $\mu\in\Omega^{0,q}$ . And

 $\overline{\partial}(\omega) = \overline{\partial}(\mu \wedge dz_I) = \overline{\partial}\mu \wedge dz_I$ 

Therefore, if  $\omega \in \Omega_I^{p,q}$ , then  $\overline{\partial}\omega \in \Omega_I^{p,q+1}$ . We can get another complex, define  $(2)p_I: \Omega^{p,0} \xrightarrow{\overline{\partial}} \Omega_I^{p,1} \xrightarrow{\overline{\partial}} \dots$ Now the map  $\mu \in \Omega^{0,q} \mapsto \mu \wedge dz_I$ . This maps  $(2)_0$  bijectively onto  $(2)_I$ . So (2) is acyclic. And  $\Omega^{p,q} = \bigoplus_I \Omega_I^{p,q}$  implies that  $(2)_p$  is acyclic.

What about complex with  $\partial$ ?

Take  $\omega \in \Omega^{p,q}$ , then

$$\omega = \sum f_{I,J} dz_I \wedge d\bar{z}_J \qquad f_{I,J} \in C^{\infty}(U), \quad |I| = p, |J| = q$$

Take complex conjugates

$$\bar{\omega} = \sum \bar{f}_{I,J} d\bar{z}_I \wedge dz_J \in \Omega^{q,p} \qquad \overline{\partial \omega} = \bar{\partial} \bar{\omega}$$

This map  $\omega \mapsto \bar{\omega}$  maps  $(1)_p$  to  $(2)_p$  so  $(2)_p$  acyclic implies that  $(1)_p$  is acyclic.

#### The Subcomplex $(A, \partial$

Another complex to consider. We look at the map  $\Omega^{p,0} \xrightarrow{\bar{\partial}} \Omega^{p,1}$ . Denote by  $A^p$  the kernel of this map,  $\ker\{\Omega^{p,0} \xrightarrow{\bar{\partial}} \Omega^{p,1}\}$ . Suppose  $\mu \in A^p$ ,  $\partial \mu \in \Omega^{p+1,0}$ , and we know that  $\bar{\partial}\partial \mu = -\partial \bar{\partial}\mu = 0$ , so  $\partial \mu \in A^{p+1}$ . Moreover,  $d\mu = \partial \mu + \bar{\partial}\mu = \partial \mu$ , so we have a subcomplex (A, d) of  $(\Omega, d)$ , the de Rham complex

$$A^0 \xrightarrow{d} A^1 \xrightarrow{d} A^2 \xrightarrow{d} \cdots$$

This complex has a fairly simple description. Suppose  $\mu \in \Omega^{p,0}$ ,  $\mu = \sum_{|I|=p} f_I dz_I$ , and suppose further that  $\overline{\partial} \mu = 0$ , i.e.  $\mu \in A^p$ . Then

$$\overline{\partial}\mu = \sum \frac{\partial f_I}{\partial \bar{z}_i} d\bar{z}_i \wedge dz_I = 0$$
  $\frac{\partial f_I}{\partial \bar{z}_i} = 0$   $i = 1, \dots, n$ 

so the  $f_i$  are holomorphic. Because of this we have the following definition

**Definition.** The complex  $(A^*, d)$  is called the **Holomorphic de Rham complex**.

When is this complex acyclic? To answer this, we go back to the real de Rham complex.

#### Reminder of Real de Rham Complex

Consider the usual (real) de Rham complex. Let U be an open set in  $\mathbb{R}^n$ . Then we know

Theorem (Poincare Lemma). If U is convex then  $(\Omega^*(U), d)$  is exact.

*Proof.* U convex, and to make things simpler, let  $0 \in U$ . Let  $\rho: U \to U$ ,  $\rho \equiv 0$ . Construct a homotopy operator  $Q: \Omega^k(U) \to \Omega^{k-1}(U)$ , satisfying

$$dQ\omega + Qd\omega = \omega - \rho^*\omega$$

for all  $\omega \in \Omega^*(U)$ . The exactness follows trivially if we have this operator. Now, what is the operator? We define it the following way.

If  $\omega = \sum f_I(x) dx_I$ ,  $f_I \in C^{\infty}(U)$ . Then

$$Q\omega = \sum_{r,I} (-1)^r x_{i_r} \left( \int_0^1 t^{k-1} f_I(tx) dt \right) dx_{i_1} \wedge \dots \wedge \widehat{dx_{i_r}} \wedge \dots \wedge dx_{i_k}$$

<u>2nd Homework Problem</u> The holomorphic version of this works. Let  $U \subseteq \mathbb{R}^{2n} \subseteq \mathbb{C}^n$ , convex with  $0 \in U$ . Take  $\omega = \sum_{|I|=k} f_I dz_I$ ,  $f_I \in \mathcal{O}(U)$ . Let Q be the same operator (but holomorphic version)

$$Q\omega = \sum_{r,I} (-1)^r z_{i_r} \left( \int_0^1 t^{k-1} f_I(tz) dt \right) dz_{i_1} \wedge \dots \wedge \widehat{dz_{i_r}} \wedge \dots \wedge dz_{i_k}$$

Show  $Q: A^k \to A^{k-1}$  and  $(dQ + Qd)\omega = \omega - \rho^*\omega$ . Homework is to check that this all works.

**Theorem.** U a polydisk. Then if  $\omega \in \Omega^{1,1}(U)$  and is closed then there exists a  $C^{\infty}$  function f so that  $\omega = \partial \overline{\partial} f$ . (f is called the potential function of  $\omega$ ).

This is an important lemma in Kaehler geometry, which we will use later.

*Proof.* Just diagram chasing:

$$\overline{A}^{1} \xrightarrow{i} \Omega^{0,1} \xrightarrow{\partial} \Omega^{1,1} \xrightarrow{\partial} \Omega^{2,1} \xrightarrow{\cdots}$$

$$\uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial} \qquad \uparrow \overline{\partial}$$

let  $\omega = \omega^{1,1} \in \Omega^{1,1}$ ,  $d\omega = 0$ , so  $\partial \omega = \overline{\partial} \omega = 0$ .  $\overline{\partial} \omega = 0$  implies there is an a so that  $\omega = \overline{\partial} a, a \in \Omega^{1,0}$ . We can find  $b \in A^1$  so that  $\partial a = \partial b$ . So  $\partial (a - b) = 0$ , and  $a - b = \partial c$ , where  $c \in \Omega^{0,0} = C^{\infty}$ . Then  $\overline{\partial} (a - b) = \overline{\partial} \partial c$ .

Exercise (not to be handed in)  $\omega \in \Omega^{p,q}(U)$ . And  $d\omega = 0$  then  $\omega = \overline{\partial}\partial u$ ,  $u \in \Omega^{p-1,q-1}$ .

#### **Functoriality**

U open in  $\mathbb{C}^n$ , V open in  $\mathbb{C}^k$ . Coordinatized by  $(z_1, \ldots, z_n)$ ,  $(w_1, \ldots, w_k)$ . Let  $f: U \to V$  be a mapping,  $f = (f_1, \ldots, f_k)$ ,  $f_i: U \to \mathbb{C}$ . f is holomorphic if each  $f_i$  is holomorphic.

**Theorem.** f is holomorphic iff  $f^*(\Omega^{1,0}(V) \subseteq \Omega^{1,0}(U)$ , i.e. for every  $\omega \in \Omega^{1,0}(V)$ ,  $f^*\omega \in \Omega^{1,0}(U)$ .

*Proof.* Necessity.  $\omega = d\omega_i$ , then

$$f^*\omega = df_i = \partial f_i + \overline{\partial} f_i \in \Omega^{1,0}(U)$$

then  $\overline{\partial} f_i = 0$ , so  $f_i \in \mathcal{O}(U)$ . Sufficiency. Check this.

**Corollary.** f holomorphic. Then  $f^*\Omega^{p,q}(V) \subseteq \Omega^{p,q}(U)$ , also  $\omega \in \Omega^{p,q}(V)$ , then  $f^*d\omega = df^*\omega$ , which implies that  $f^*\partial\omega = \partial f^*\omega$ ,  $f^*\overline{\partial}\omega = \overline{\partial} f^*\omega$ .

## Chapter 2

# Complex Manifolds

#### Lecture 7

#### Complex manifolds

First, lets prove a holomorphic version of the inverse and implicit function theorem.

For real space the inverse function theorem is as follows: Let U be open in  $\mathbb{R}^n$  and  $f: U \to \mathbb{R}^n$  a  $C^{\infty}$  map. For  $p \in U$  and for  $x \in B_{\epsilon}(p)$  we have that

$$f(x) = \underbrace{f(p) + \frac{\partial f}{\partial x}(p)(x-p)}_{II} + \underbrace{O(|x-p|^2)}_{II}$$

I is the linear approximation to f at p.

**Theorem (Real Inverse Function Theorem).** If I is a bijective map  $\mathbb{R}^n \to \mathbb{R}^n$  then f maps a neighborhood  $U_1$  of p in U diffeomorphically onto a neighborhood V of f(p) in  $\mathbb{R}^n$ .

Now suppose U is open in  $\mathbb{C}^n$ , and  $f:U\to\mathbb{C}^n$  is holomorphic, i.e. if  $f=(f_1,\ldots,f_n)$  then each of the  $f_i$  are holomorphic. For z close to p use the Taylor series to write

$$f(z) = \underbrace{f(p) + \frac{\partial f}{\partial z}(p)(z-p)}_{I} + \underbrace{O(|z-p|^2)}_{II}$$

I is the linear approximation of f at p.

**Theorem (Holomorphic Inverse Function Theorem).** If I is a bijective map  $\mathbb{C}^n \to \mathbb{C}^n$  then f maps a neighborhood  $U_1$  of p in U biholomorphically onto a neighborhood V of f(p) in  $\mathbb{C}^n$ .

(biholomorphic: inverse mapping exists and is holomorphic)

Proof. By usual inverse function theorem f maps a neighborhood  $U_1$  of p is U diffeomorphically onto a neighborhood V of f(p) in  $\mathbb{C}^n$ , i.e.  $g=f^{-1}$  exists and is  $C^{\infty}$  on V. Then  $f^*:\Omega^1(V)\to\Omega^1(U_1)$  is bijective and f is holomorphic, so  $f^*:\Omega^1(V)\to\Omega^1(U_1)$  preserves the splitting  $\Omega^1=\Omega^{1,0}\oplus\Omega^{0,1}$ . However, if  $g=f^{-1}$  then  $g^*:\Omega^1(U_1)\to\Omega^1(V)$  is just  $(f^*)^{-1}$  so it preserves the splitting. By a theorem we proved last lecture g has to be holomorphic.

Now, the implicit function theorem. Let U be open in  $\mathbb{C}^n$  and  $f_1, \ldots, f_k \in \mathcal{O}(U), p \in U$ .

**Theorem.** If  $df_1, \ldots, df_k$  are linearly independent at p, there exists a neighborhood  $U_1$  of p in U and a neighborhood V of 0 in  $\mathbb{C}^n$  and a biholomorphism  $\varphi: (V,0) \to (U_1,p)$  so that

$$\varphi^* f_i = z_i \qquad i = 1, \dots, k$$

Proof. We can assume p=0 and assume  $f_i=z_i+O(|z|^2)$   $i=1,\ldots,k$  near 0. Take  $\psi:(U,0)\to(\mathbb{C}^n,0)$  given by  $\psi(f_1,\ldots,f_kz_{k+1},\ldots,z_n)$ . By definition  $\partial\psi/\partial z(0)=Id=[\delta_{ij}]$ .  $\psi$  maps a neighborhood  $U_1$  of 0 in U biholomorphically onto a neighborhood V of 0 in  $\mathbb{C}^n$  and for  $1\leq i\leq k, \ \psi^*z_i=f_i$ . Define  $\varphi=\psi^{-1}$ , then  $\varphi^*f_i=z_i$ .

#### Manifolds

X a Hausdorff topological space and 2nd countable (there is a countable collection of open sets that defines the topology).

**Definition.** A chart on X is a triple  $(\varphi, U, V)$ , U open in X, V an open set in  $\mathbb{C}^n$  and  $\varphi : U \to V$  homeomorphic.

Suppose we are given a pair of charts  $(\varphi_i, U_i, V_i)$ , i = 1, 2. Then we have the overlap chart

where  $\varphi_1(U_1 \cap U_2) = V_{1,2}$  and  $\varphi_2(U_1 \cap U_2) = V_{2,1}$ .

**Definition.** Two charts are **compatible** if  $\varphi_{1,2}$  is biholomorphic.

**Definition.** An atlas A on X is a collection of mutually compatible charts such that the domains of these charts cover X.

**Definition.** An atlas is **complete** if every chart which is compatible with the members of  $\mathcal{A}$  is in  $\mathcal{A}$ .

The completion operation is as follows: Take  $A_0$  to be any atlas then we take  $A_0 \rightsquigarrow A$  by adding all charts compatible with  $A_0$  to this atlas.

**Definition.** A complex n-dimensional manifold is a pair  $(X, \mathcal{A})$ , where X is a second countable Hausdorff topological space,  $\mathcal{A}$  is a complete atlas.

From now on if we mention a chart, we assume it belongs to some atlas A.

**Definition.**  $(\varphi, U, V)$  a chart,  $p \in U$  and  $\varphi(p) = 0 \in \mathbb{C}^n$ , then " $\varphi$  is centered at p".

**Definition.**  $(\varphi, U, V)$  a chart and  $z_1, \ldots, z_n$  the standard coordinates on  $\mathbb{C}^n$ . Then

$$\varphi_i = \varphi^* z_i$$

 $\varphi_1, \ldots, \varphi_n$  are coordinate functions on U. We call  $(U, \varphi_1, \ldots, \varphi_n)$  is a **coordinate patch** 

Suppose X is an n-dimensional complex manifold, Y an m-dimensional complex manifold and  $f: X \to Y$  continuous.

**Definition.** f is holomorphic at  $p \in X$  if there exists a chart  $(\varphi, U, V)$  centered at p and a chart  $(\varphi', U', V')$  centered at f(p) such that  $f(U) \subset U'$  and such that in the diagram below the bottom horizontal arrow is holomorphic

$$U \xrightarrow{f} U'$$

$$\varphi \bowtie \cong \varphi'$$

$$V \xrightarrow{g} V'$$

(Check that this is an intrinsic definition, i.e. doesn't depend on choice of coordinates). From now on  $f: X \to \mathbb{C}$  is holomorphic iff  $f \in \mathcal{O}(X)$  (just by definition)

 $(\varphi, U, V)$  is a chart on X, V is by definition open in  $\mathbb{C}^n = \mathbb{R}^{2n}$ . So  $(\varphi, U, V)$  is a 2n-dimensional chart in the real sense. If two charts  $(\varphi_i, U_i, V_i)$ , i = 1, 2 are 18.117 compatible then they are compatible in the 18.965 sense (because biholomorphisms are diffeomorphisms)

So every n-dimensional complex manifold is automatically a 2n-dimensional  $C^{\infty}$  manifold. One application of this observation:

Let X be an  $\mathbb{C}$ -manifold, X is then a 2n-dimensional  $C^{\infty}$  manifold. If  $p \in X$ , then  $T_pX$  the tangent

space to X (as a  $C^{\infty}$  2n-dimensional manifold).  $T_0X$  is a 2n-dimensional vector space over  $\mathbb{R}$ . We claim:  $T_pZ$  has the structure of a complex n-dimensional vector space. Take a chart  $(\varphi, U, V)$  centered at p, so  $\varphi: U \to V$  is a  $C^{\infty}$  diffeomorphism.

Take  $(d\varphi)_p: T_p \to T_0\mathbb{C}^n = \mathbb{C}^n$ . Define a complex structure on  $T_pX$  by requiring  $d\varphi_p$  to be  $\mathbb{C}$ -linear. (check that this in independent of the choice of  $\varphi$ ).

From the overlap diagram we get something like

 $X, Y, f: X \to Y$  holomorphic, f(p) = q. By 18.965,  $df_p: T_p \to T_q$  check that  $df_p$  is  $\mathbb{C}$ -linear.

## Lecture 8

We'll just list a bunch of definitions. X a topological Hausdorff space, second countable.

**Definition.** A chart is a trip  $(\varphi, U, V)$ , U open in X, V open in  $\mathbb{C}$  and  $\varphi: U \to V$  a homeomorphism.

If you consider two charts  $(\varphi_i, U_i, V_i)$ , i = 1, 2 we get an overlap diagram. Charts are compatible if and only if the transition maps in the overlap diagram (see above) are biholomorphic.

**Definition.** A atlas is a collection  $\mathcal{A}$  of charts such that

- 1. The domains are a cover of X
- 2. All members of  $\mathcal{A}$  are compatible.

**Definition.** An atlas  $\mathcal{A}$  is a maximal atlas then  $(X, \mathcal{A})$  is a complex *n*-dimensional manifold.

Remark: If every open subset of X is a complex n-dimensional manifold we say  $\mathcal{A}_U$  is a member of  $\mathcal{A}$ with domain contained in U.

If X is a complex n-dimensional manifold it is automatically a real  $C^{\infty}$  2n-dimensional manifold.

**Definition.** X, Y are complex manifolds,  $f: X \to Y$  is holomorphic if locally its holomorphic.

 $f \in \mathcal{O}(X), \ f: X \to \mathbb{C}$ . Note if  $f: X \to Y, \ g: Y \to Z$  holomorphic, then  $f \circ g: X \to Z$  is as well. Take X to be an n-dimensional complex manifolds, if we think of X as a  $C^{\infty}$  2n-dimensional then  $T_pX$ is well defined. But we showed that  $T_pX$  has a complex structure.  $f:X\to Y$  holomorphic,  $p\in X, q=f(p)$ in the real case  $df_p: T_p \to T_q$ , but we check that this is also C-linear.

Notion of Charts Revisited A chart (from now on) is a triple  $(\varphi, U, V)$ , U open in X, V open in  $\mathbb{C}^n$ ,  $\varphi: U \to V$  a biholomorphic map.

**Definition.** A coordinate patch in X is an n-tuple  $(U, w_1, \ldots, w_n)$  where U is open in X and  $w_i \in \mathcal{O}(U)$ such that the map  $\varphi: U \to \hat{\mathbb{C}}^n$ 

$$p \mapsto (w_1(p), \dots, w_n(p))$$

is a biholomorphic map onto an open set V of  $\mathbb{C}^n$ .

Charts and coordinate patches are equivalent.

**Theorem (Implicit Function Theorem in Manifold Setting).**  $X^n$  a manifold.  $U_0 \subseteq X$  is an open set,  $f_1, \ldots, f_k \in \mathcal{O}(U_0)$ ,  $p \in U_0$ . Assume  $df_1, \ldots, df_k$  are linearly independent at p. Then there exists a coordinate patch  $(U, w_1, \ldots, w_n)$ ,  $p \in U$ ,  $U \subset U_0$  such that  $w_i = f_i$  for  $i = 1, \ldots, k$ .

*Proof.* We can assume  $U_0$  is the domain of the chart  $(U_0, V, \varphi)$ , V an open set in  $\mathbb{C}^n$ ,  $\varphi : U_0 \to V$  a biholomorphism. Then just apply last lecture version of implicity function theorem to  $f_i \circ (\varphi^{-1})$ .

#### Submanifolds

X a complex n-dimensional manifolds.  $Y \subset X$  a subset.

**Definition.** Y is a k-dimensional submanifold of X if for every  $p \in Y$  there exists a coordinate patch  $(U, z_1, \ldots, z_n)$  with  $p \in U$  such that  $Y \cap U$  is defined by the equation  $z_{k+1} = \cdots = z_n = 0$ .

Remarks: A k dimensional submanifold of X is a k-dimensional complex manifold in its own right. Call a coordinate patch with the property above an **adapted** coordinated for X. The collection of (n+1)-tuples  $(U', z'_1, \ldots, z'_k)$ ,  $(U, z_1, \ldots, z_n)$ ,  $U' = U \cap Y$ ,  $z'_i = z_i \mid_{U'}$  gives an atlas for X. By the implicit function theorem this definition is equivalent to the following weaker definition.

**Definition.** Y is a k-dimensional submanifold X if for every  $p \in Y$  there exists an open set U of p in X and  $f_i \in \mathcal{O}(U)$  where  $i = 1, \ldots, l, l = n - k$  such that  $df_1, \ldots, df_l$  are linearly independent at p and  $Y \cap U$ ,  $f_1 = \cdots = f_l = 0$ , i.e. locally Y is cut-out by l independent equation.

#### Examples

Affine non-singular algebraic varieties in  $\mathbb{C}^n$ . These are X-dimensional submanifolds, Y of  $\mathbb{C}^n$  such that for every  $p \in Y$  the  $f_i$ 's figuring into the equation above (the ones that cut-out the manifold) are

**Projective counterparts** We start by constructing the projective space  $\mathbb{C}P^n$ . Start with  $\mathbb{C}^{n+1} - \{0\}$ . Given 2(n+1)-tuples we say

$$(z_0, z_1, \ldots, z_n) \sim (z'_0, z'_1, \ldots, z'_n)$$

in  $\mathbb{C}^n - \{0\}$  if there exists  $\lambda \in \mathbb{C} - \{0\}$  with  $z_i' = \lambda z_i$ ,  $i = 0, \ldots, n$ .  $[z_0, z_1, \ldots, z_n]$  are equivalence classes. We define  $\mathbb{C}P^n$  to be these equivalence classes  $\mathbb{C}^{n+1} - \{0\}/\sim$ . We make this into a topological space by  $\pi: \mathbb{C}^{n+1} - \{0\} \to \mathbb{C}P^n$ , which is given by

$$(z_0, z_1, \ldots, z_n) \sim [z_0, z_1, \ldots, z_n]$$

We topologize  $\mathbb{C}P^n$  by giving it the weakest topology that makes  $\pi$  continuous, i.e.  $U\subseteq\mathbb{C}P^n$  is open if  $\pi^{-1}(U)$  is open.

**Lemma.** With this topology  $\mathbb{C}P^n$  is compact.

Proof. Take

$$\mathbb{S}^{2n+1} = \{(z_0, \dots, z_n) | |z_0|^2 + \dots + |z_n|^2 = 1\}$$

and we note

$$\pi(\mathbb{S}^{2n+1}) = \mathbb{C}P^n$$

so its the image of a compact set under a continuous map, so its compact.

**Lemma.**  $\mathbb{C}P^n$  is a complex n-manifold.

*Proof.* Define the standard atlas for  $\mathbb{C}P^n$ . For  $i=0,\ldots,n$  take

$$U_i = \{ [z_0, \dots, z_n] \in \mathbb{C}P^n, z_i \neq 0 \}$$

Take  $V_i = \mathbb{C}^n$  and define a map  $\varphi_i : U_i \to V_i$  by

$$[z_0,\ldots,z_n]\mapsto\left(\frac{z_0}{z_i},\ldots,\frac{\widehat{z_i}}{z_i},\ldots,\frac{z_n}{z_i}\right)$$

$$\varphi_i^{-1}:\mathbb{C}^n\to U_i$$
 is given by

$$(w_1,\ldots,w_n)\mapsto [w_1,\ldots,1,\ldots,w_n]$$

where  $w_1$  is in the 0th place, and 1 is in the ith place. The overlap diagrams for  $U_0$  and  $U_1$  are given by

$$V_{0,1} \xrightarrow{\varphi_{0}} V_{1,0}$$

We can check that  $V_{0,1} = V_{1,0} = \{(z_1, \ldots, z_n), z_i \neq 0\}$ . Also check that

$$\varphi_{0,1}: V_{0,1} \to V_{1,0} \qquad (z_1, \dots, z_n) \mapsto \left(\frac{1}{z_1}, \frac{z_2}{z_1}, \dots, \frac{z_n}{z_1}\right)$$

This standard atlas gives a complex structure for  $\mathbb{C}P^n$ .

### Lecture 9

We have a manifold  $\mathbb{C}P^n$ . Take

$$P(z_0, \dots, Pz_n) = \sum_{|\alpha|=m} c_{\alpha} z^{\alpha}$$

a homogenous polynomial. Then

- 1.  $P(\lambda z) = \lambda^m P(z)$ , so if P(z) = 0 then  $P(\lambda z) = 0$
- 2. Euler's identity holds

$$\sum_{i=0}^{n} z_i \frac{\partial P}{\partial z_i} = mP$$

**Lemma.** The following are equivalent

- 1. For all  $z \in \mathbb{C}^{n+1} \{0\}, dP_z \neq 0$
- 2. For all  $z \in \mathbb{C}^{n+1} \{0\}$ , P(z) = 0,  $dP_z \neq 0$ .

we call P non-singular if one of these holds.

If  $X = \{[z_0, \ldots, z_n], P(z) = 0\}$ . Note that this is a well-defined property of homogeneous polynomials.

**Theorem.** If P is non-singular, X s an n-1 dimensional submanifold of  $\mathbb{C}P^n$ .

*Proof.* Let  $U_0, \ldots, U_n$  be the standard atlas for  $\mathbb{C}P^n$ . It is enough to check that  $X \cap U_i$  is a submanifold of  $U_i$ . WE'll check this for i = 0.

Consider the map  $\gamma \mathbb{C}^n \xrightarrow{\cong} U_0$  given by

$$\gamma(z_1,\ldots,z_n)=[1,z_1,\ldots,z_n]$$

It is enough to show that  $X_0 = \gamma^{-1}(X)$  is a complex n-1 dimensional submanifold of  $\mathbb{C}^n$ . Let  $p(z_1, \ldots, z_n) = P(1, z_1, \ldots, z_n)$ .  $X_0$  is the set of all points such that p = 0. It is enough to show that p(z) = 0 implies  $dp_z \neq 0$  (showed last time that this would then define a submanifold) Suppose dp(z) = p(z) = 0. Then

$$p(1, z_1, \dots, z_n) = 0 = \frac{\partial P}{\partial z_i}(1, z_1, \dots, z_n) = 0$$
  $i = 1, \dots, n$ 

By the Euler Identity

$$0 = P(1, z_1, \dots, z_n) = \sum_{i=0}^n z_i \frac{\partial P}{\partial z_i} (1, z_1, \dots, z_n) + \sum_{i=0}^n \frac{\partial P}{\partial z_i} (1, z_1, \dots, z_n)$$

So  $\frac{\partial P}{\partial z_i}(1, z_1, \dots, z_n) = 0$ , which is a contradiction because we assumed  $p \neq 0$ .

Theorem (Uniqueness of Analytic Continuation). X a connected complex manifold,  $V \subseteq X$  is an open set,  $f,g \in \mathcal{O}(X)$ . If f = g on V then f = g on all of X.

Sketch. Local version of UAC plus the following connectedness lemma

**Lemma.** For  $p, q \in X$  there exists open sets  $U_i$ , i = 1, ..., n such that

- 1.  $U_i$  is biholomorphic to a connected open subset of  $\mathbb{C}^n$
- $2. p \in U_1$
- $3. q \in U_n$
- 4.  $U_i \cap U_{i+1} \neq \emptyset$ .

**Theorem.** If X is a connected complex manifold and  $f \in \mathcal{O}(X)$  then if for some  $p \in X$ ,  $|f|: X \to \mathbb{R}$  takes a local maximum then f is constant.

Corollary. If X is compact and connected  $\mathcal{O}(X) = \mathbb{C}$ .

This implies that the Whitney embedding theorem does not hold for holomorphic manifolds.

Let X be a complex n-dimensional manifold, X a real 2n dimensional manifold. Then if  $p \in X$  then  $T_pX$ is a real 2n-dimensional vector space and  $T_pX$  is a complex n-dimensional vector space.

Think for the moment of  $T_p\dot{X}$  as being a 2n-dimensional  $\mathbb{R}$ -linear vector space. Define

$$J_p: T_pX \to T_pX$$
  $J_pv = \sqrt{-1}v$ 

 $J_p$  is  $\mathbb{R}$ -linear map with the property that  $J_p^2 = -I$ . We want to find the eigenvectors. First take  $T_p \otimes \mathbb{C}$ and extend  $J_p$  to this by

$$J_p(v\otimes c)=J_pv\otimes c$$

Now,  $J_p$  is  $\mathbb{C}$ -linear,  $J_p: T_p \otimes \mathbb{C} \to T_p \otimes \mathbb{C}$ . Also, we can introduce a complex conjugation operator

$$: T_p \otimes \mathbb{C} \to T_p \otimes \mathbb{C} \qquad v \otimes c \mapsto v \otimes \bar{c}$$

We can split the tangent space by

$$T_p \otimes \mathbb{C} = T_p^{1,0} \oplus T_p^{0,1}$$

where  $v \in T_p^{1,0}$  if  $J_p v = +\sqrt{-1}v$  and  $v \in T_p^{0,1}$  if  $J_p v = -\sqrt{-1}v$ . i.e. we break  $T_p \otimes \mathbb{C}$  into eigenspaces. If  $v \in T_p^{1,0}$  iff  $\bar{v} \in T_p^{0,1}$  and so the dimension of the two parts of the tangent spaces are equal. We can also take  $T_p^* \otimes \mathbb{C} = (T_p^*)^{1,0} \oplus (T_p^*)^{0,1}$  and  $l \in (T_p^*)^{1,0}$  if and only if  $J_p^* l = \sqrt{-1}l$ ,  $l \in (T_p^*)^{0,1}$  if  $J_p^* l = -\sqrt{-1}l.$ 

Check that  $l \in (T_p^*)^{1,0}$  if and only if  $l: T_p \to \mathbb{C}$  is actually  $\mathbb{C}$ -linear. To do this  $J^*l = \sqrt{-1}l$  implies  $J_p^*l(v) = l(J_pv) = \sqrt{-1}l(v)$  which implies that l is C-linear.

**Corollary.** U is open in X and  $p \in U$ . Then if  $f \in \mathcal{O}(U \text{ then } df_p \in (T_p^*)^{1,0}$ .

Corollary.  $(U, z_1, \ldots, z_n)$  a coordinate patch then  $(dz_1)_p, \ldots, (dz_n)_p$  is a basis of  $(T_p^*)^{1,0}$  and  $(d\bar{z}_1)_p, \ldots, (d\bar{z}_n)_p$ is a basis of  $(T_n^*)^{0,1}$ .

From the splitting above we get a splitting of the exterior product

$$\Lambda^{k}(T_{p}^{*}\otimes\mathbb{C})=\bigoplus_{l+m=k}\Lambda^{l,m}(T_{p}^{*}\otimes\mathbb{C})$$

for  $\nu_1, \ldots, \nu_n$  a basis of  $T_p^* \otimes \mathbb{C}$  then

$$\omega \in \Lambda^{l,m}(T_p^* \otimes \mathbb{C}) \Leftrightarrow \omega = \sum c_{I,J} \nu_I \wedge \bar{\nu}_J$$

We also get a splitting in the tangent bundle

$$\Lambda^k(T^*\otimes\mathbb{C})=\bigoplus_{l+m=k}\Lambda^{k,l}(T^*\otimes\mathbb{C})$$

since  $\Omega^k(X)$  is sections of  $\Lambda^k(T^* \otimes \mathbb{C})$ . Then

$$\Omega^k(X) = \bigoplus_{l+m=k} \Lambda^{l,m}(X)$$

Locally when  $(U, z_1, \dots, z_n)$  is a coordinate patch,  $\omega \in \Omega^{l,m}(U)$  iff

$$\omega = \sum a_{I,J} dz_I \wedge d\bar{z}_J$$

so we've extended the Dolbeault complex to arbitrary manifolds.

#### Lecture 10

IF  $(U, z_1, \ldots, z_n)$  is a coordinate patch, then this splitting agrees with our old splitting. Son on a complex manifold we have the bicomplex  $(\Omega^{*,*}, \partial, \overline{\partial})$ . Again, we have lots of interesting subcomplexes.

$$A^p(X) = A^p = \ker \overline{\partial} : \Omega^{p,0} \longrightarrow \Omega^{p,1}$$

the complex of holomorphic p-forms on X, i.e. on a coordinate patch  $\omega \in A^p(U)$ 

$$\omega = \sum f_I dz_I \qquad f_I \in \mathcal{O}(U)$$

Now, for the complex  $A^p(X)$  we can compute its cohomology. There are two approaches to this

- 1. Hodge Theory
- 2. Sheaf Theory

We'll talk about sheaves for bit.

Let X be a topological space. Top(X) is the category whose objects are open subsets of X and morphisms are the inclusion maps.

**Definition.** A **pre-sheaf** of abelian groups is a contravariant functor  $\mathcal{F}$  from Top(X) to the category of abelian groups.

In english:  $\mathcal{F}$  attached to every open set  $U \subset X$  an abelian group  $\mathcal{F}(U)$  and to every pair of open sets  $U \supset V$  a restriction map  $r_{U,V} : \mathcal{F}(U) \to \mathcal{F}(V)$ . The functorality of this is that if  $U \supset V \supset W$  then  $r_{U,W} = r_{V,W} \cdot r_{U,V}$ .

#### Examples

1. The pre-sheaf  $C, U \to C(U) =$  the continuous function on U. Then the restrictions are given by

$$r_{U,V}: C(U) \to C(V)$$
  $C(U) \ni f \mapsto f \mid_{V} \in C(V)$ 

- 2. X a  $C^{\infty}$  manifold. The pre-sheaf of  $C^{\infty}$  functions,  $U \to C^{\infty}(U)$ .  $r_{U,V}$  are as in 1.
- 3.  $\Omega^r$  is a pre-sheaf,  $U \to \Omega^r(U)$ . Restriction is the usual restriction.
- 4. X a complex manifold, then  $\Omega^{p,q}$ ,  $U \to \Omega^{p,q}(U)$  is a pre-sheave.
- 5. X a complex manifold, then you have the sheaf  $U \to \mathcal{O}(U)$ .

Consider the pre-sheaf of  $C^{\infty}$ -functions. Let  $\{U_i\}$  be a collection of open set n X and  $U=\bigcup U_i$ . We claim that  $C^1$  has the following "gluing property":

Given  $f_i \in C^{\infty}(U_i)$  suppose

$$r_{U_i,U_i\cap U_j}f_i=r_{U_i,U_i\cap U_j}f_j$$

i.e.  $f_i = f_j$  on  $U_i \cap U_j$ . Then there is a unique  $f \in C^{\infty}(U)$  such that

$$r_{U,U_i}f = f_i$$

**Definition.** A pre-sheaf  $\mathcal{F}$  is a **sheaf** if it has the gluing property.

(Note that all of all pre-sheaves in the examples are sheaves)

#### **Sheaf Cohomology**

Let  $U = \{U_i, i \in I\}$ , I an index set,  $U_i$  an open cover of X. Let  $J = (j_0, \dots, j_k) \in I^{k+1}$ , then define

$$U_J = U_{j_0} \cap \cdots \cap U_{j_k}$$

Take  $N^k \subseteq I^{k+1}$  and let us say that  $J \subset N^k$  if and only if  $U_J \neq \emptyset$  and take

$$N = | N^k$$

then this is a graded set called the **nerve** of the cover  $U_i$ .  $N^k$  is called the **k-skeleton** of N. Let  $\mathcal{F}$  be the sheaf of abelian groups in X

**Definition.** A Cech cochain, c of degree k, with values in  $\mathcal{F}$  is a map that assigns to every  $J \in \mathbb{N}^k$  an element  $c(J) \in \mathcal{F}(U_J)$ .

**Notation.**  $J \in \mathbb{N}^k$ ,  $J = (j_0, \dots, j_k)$  and  $j_i \in I$  for all  $0 \le i \le k$ . Then define

$$J_i = (j_0, \dots, \widehat{j_i}, \dots, j_k)$$

then  $J_i \in N^{k-1}$  and let  $r_i = r_{U_{J_i}, U_J}$ .

We can define an coboundary operator

$$\delta: C^{k-1}(U,\mathcal{F}) \to C^k(U,\mathcal{F})$$

For  $J \in \mathbb{N}^k$  and  $c \in \mathbb{C}^{k-1}$  define

$$\delta c(J) = \sum_{i} (-1)^{i} r_{i} c(J_{i})$$

(note that this makes sense, because  $c(J_i) \in \mathcal{F}(U_{J_i})$ .

**Lemma.**  $\delta^2 = 0$ , i.e.  $\delta$  is in fact a coboundary operator.

Proof.  $J \in N^{k+1}$  then

$$(\delta \delta c)(J) = \sum_{i} (-1)^{i} r_{i} \delta c(J_{i})$$

$$= \sum_{i} (-1)^{i} r_{i} r_{j} \sum_{j < i} (-1)^{j} c(J_{i,j}) +$$

$$\sum_{i} (-1)^{i} r_{i} r_{j} \sum_{j > i} (-1)^{j-1} c(J_{i,j})$$

this is symmetric in i and j, so its 0.

Because  $\delta$  is a coboundary operator we can consider  $H^k(\mathcal{U}, \mathcal{F})$ , the cohomology groups of this complex. What is  $H^0(U, \mathcal{F})$ ? Consider  $c \in C^0(U, \mathcal{F})$  then every  $i \in I$ ,  $c(i) = f_i \in \mathcal{F}(U_i)$ . If  $\delta c = 0$  then  $r_i f_j = r_j f_i$  for all i, j. Then the gluing property of  $\mathcal{F}$  tells us that there exists an  $f \in \mathcal{F}(X)$  with  $r_i f = f_i$ , so we have proved that  $H^0(X, \mathcal{F}) = \mathcal{F}(X)$ , the global sections of the sheaf.

For today, we'll just compute  $H^k(U, C^{\infty}) = 0$  for all  $k \geq 1$ . The proof is a bit sketchy.

Let  $\{\rho_r\}_{r\in I}$  be a partition of unity subordinate to  $\{U_i, i\in I\}$ . Then  $\rho_r\in C_0^\infty(U_r)$  and  $\sum \rho_r=1$  by definition. Given  $J\in N^{k-1}$  let  $(r,J)=(r,j_0,\ldots,j_{k-1})$  and define a coboundary operator

$$Q: C^k(U, \mathcal{F}) \to C^{k-1}(U, \mathcal{F})$$

Take  $c \in C^k$ ,  $J \in N^{k-1}$  then

$$Qc(J) = \sum \rho_r c(r, J) \qquad \in C^{\infty}(U_J)$$

Explanation: First notice that (r, J) may not be in  $N^k$ . But in this case  $U_r$  and  $U_J$  are disjoint, so  $\rho_r \equiv 0$  on  $U_J$ , so we just make these terms 0. What if  $(r, J) \in N^k$  then  $c(r, J) \in C^{\infty}(U_r \cap U_J)$  (but we want Qc(J) to be  $C^{\infty}(U_J)$ .

But.

$$\rho_r c(r,J) = \begin{cases} \rho_r c(r,J) & \text{on } U_r \cap U_J \\ 0 & \text{on } U_J - (U_r \cap U_J) \end{cases}$$

and  $\rho_r \in C^{\infty}(U_r)$ .

**Proposition.**  $\delta Q + Q\delta = id$ .

Corollary.  $H^k(U, C^{\infty}) = 0$ .

The same argument works for the sheaves  $\Omega^*$ ,  $\Omega^{p,q}$ , but NOT however for  $\mathcal{O}$ .

#### Lecture 11

U open in  $\mathbb{C}^n$ ,  $\rho \in C^{\infty}(U)$ ,  $\rho: U \to \mathbb{R}$  ten  $\rho$  is strictly plurisubharmonic if for all  $p \in U$  the matrix

$$\left[\frac{\partial^2 \rho}{\partial z_i \partial \bar{z}_j}(p)\right]$$

is positive definite.

If U, V open in  $\mathbb{C}^n$  then  $\varphi: U \to V$  is biholomorphic then for  $\rho \in C^{\infty}(V)$  strictly plurisubharmonic  $\varphi^* \rho$  is also strictly plurisubharmonic. If  $q = \varphi(p)$ 

$$\frac{\partial^2}{\partial z_i \bar{z}_j} \varphi^* \rho(q) = \sum_{k,l} \frac{\partial^2 \rho}{\partial z_i \partial \bar{z}_l} \frac{\partial \varphi_k}{\partial z_l} \frac{\partial \bar{\varphi}_l}{\partial \bar{z}_j}$$

the RHS being s.p.s.h implies the right hand side is also.

**Definition.** U open in  $\mathbb{C}^n$  is **pseudo-convex** if it admits a s.p.s.h exhaustion function. We discussed the examples before (in particular if  $U_1$ ,  $U_2$  pseudo-convex,  $U_1 \cap U_2$  is pseudo-convex)

The observation above gives that pseudoconvexity is invariant under biholomorphism.

**Theorem (Hormander).** U pseudo-convex then the Dolbeault complex on U is exact.

#### Back to Cech Cohomology

X a complex n-dimensional manifold and  $\mathcal{U} = \{U_i, i \in I\}$  and  $\mathcal{F}$  a sheaf of abelian groups. We get the Cech complex

$$C^0(\mathcal{U},\mathcal{F}) \xrightarrow{\delta} C^1(\mathcal{U},\mathcal{F}) \xrightarrow{\delta} \cdots$$

and  $H^p(\mathcal{U}, \mathcal{F})$  is the cohomology group of the Cech complex. We proved earlier that  $H^0(\mathcal{U}, \mathcal{F}) = \mathcal{F}(X)$ . Also, we showed that if  $\mathcal{F}$  is one of the sheaves that we discussed  $H^p(\mathcal{U}, \mathcal{F}) = 0, p > 0$  i.e.  $\mathcal{F} = C^{\infty}, \Omega^p, \Omega^{p,q}$ . But what we're really interested in is  $\mathcal{F} = \mathcal{O}$ .

**Definition.**  $\mathcal{U} = \{U_i, i \in I\}$  is a pseudoconvex cover if for each  $i, U_i$  is biholomorphic to a pseudoconvex open set of  $\mathbb{C}^n$ .

**Theorem.** If  $\mathcal{U}$  is a pseudoconvex cover then the Cech cohomology groups  $H^p(\mathcal{U}, \mathcal{O})$  are identified with the cohomology groups of the Dolbeault complex

$$\Omega^{0,0}(X) \xrightarrow{\overline{\partial}} \Omega^{0,1}(X) \xrightarrow{\overline{\partial}} \Omega^{0,2}(X) \xrightarrow{\overline{\partial}} \cdots$$

This is pretty nice, because its a comparison of very different objects. We do a proof by diagram chasing. The rows of this diagram are

$$0 \xrightarrow{\quad \delta \quad} \Omega^{0,q}(X) \xrightarrow{\quad \delta \quad} C^0(\mathcal{U},\Omega^{0,q}) \xrightarrow{\quad \delta \quad} C^1(\mathcal{U},\Omega^{0,q}) \xrightarrow{\delta \quad} \cdots$$

To figure out the columns we have to create another way looking at the Cech complex.

Let N be the nerve of  $U, J \in N^p, c \in C^p(U, \Omega^{0,q})$  iff c assigns to J an element  $c(J) \in \Omega^{0,q}(U_J)$ . Define  $\overline{\partial} c \in C^p(\mathcal{U}, \Omega^{0,q+1})$  by

$$\overline{\partial}c(J) = \overline{\partial}(c(J))$$

now  $\overline{\partial}: C^p(\mathcal{U}, \Omega^{0,q}) \to C^p(\mathcal{U}, \Omega^{0,q+1})$  and we can show that  $\overline{\partial}^2 = 0$ . Its not hard to show that the diagram below commutes.

$$C^{p}(\mathcal{U}, \Omega^{0,q}) \xrightarrow{\delta} C^{p+1}(\mathcal{U}, \Omega^{0,q})$$

$$\overline{\partial} \downarrow \qquad \qquad \overline{\partial} \downarrow$$

$$C^{p}(\mathcal{U}, \Omega^{0,q+1}) \xrightarrow{\delta} C^{p+1}(\mathcal{U}, \Omega^{0,q+1})$$

Consider the map  $C^p(\mathcal{U},\Omega^{0,0}) \xrightarrow{\overline{\partial}} C^p(\mathcal{U},\Omega^{0,1})$ , what is the kernel of  $\overline{\partial}$ .  $c \in C^p(\mathcal{U},\Omega^{0,0})$ ,  $J \in N^p$ ,  $c(J) \in C^p(\mathcal{U},\Omega^{0,0})$  $C^{\infty}(U_J)$  and  $\overline{\partial}c(J)=0$  then  $c(J)\in\mathcal{O}(U_J)$ . So we can extend the arrow that we are considering as follows

$$C^p(\mathcal{U}, \mathcal{O}) \xrightarrow{i} C^p(\mathcal{U}, \Omega^{0,0}) \xrightarrow{\overline{\partial}} C^p(\mathcal{U}, \Omega^{0,1}) \xrightarrow{\longrightarrow} \cdots$$

**Theorem.** The following sequence is exact

$$C^p(\mathcal{U}, \Omega^{0,0}) \xrightarrow{\overline{\partial}} C^p(\mathcal{U}, \Omega^{0,1}) \xrightarrow{\overline{\partial}} \cdots$$

Observation:  $J \in \mathbb{N}^p$ . The set  $U_J$  is biholomorphic to a pseudoconvex open set in  $\mathbb{C}^n$ . Why?  $U_J$  is non-empty and it is the intersection of pseudoconvex sets, and so it is also pseudoconvex.

Suppose we have  $c \in C^p(\mathcal{U}, \Omega^{0,q})$  and  $\overline{\partial} c = 0$ . For  $J \in N^p$ ,  $c(J) \in C^\infty(U_J)$  and  $\overline{\partial} c(J) = 0$ . So there is an  $f_J \in \Omega^{0,q+1}$  such that  $\overline{\partial} f_I = c(J)$ . Now define  $c' \in C^p(\mathcal{U}, \Omega^{0,q-1})$  by  $c'(J) = f_I$ . Then  $\overline{\partial} c' = c$ . Now, for the diagram. Set  $C^{p,q} = C^p(\mathcal{U}, \Omega^{0,q})$ , and  $A^q = \Omega^{0,q}(X)$ ,  $B^p = C^p(\mathcal{U}, \mathcal{O})$ . We get the following

diagram

All rows except the bottom row are exact, all columns except the the left are exact. The bottom row computes  $H^p(\mathcal{U}, \mathcal{O})$  and the left hand column computes  $H^q(X, \text{Dolbeault})$ . We need to prove that the cohomology of the bottom row is the cohomology of the left.

the bottom row is the cohomology of the left. Hint: Take  $[a] \in H^k(X, \text{Dolbeault})$ ,  $a \in A^k = \Omega^{0,k}(X)$ . The we just diagram chase down and to the right, eventually we get down to a  $[b] \in H^k(\mathcal{U}, \mathcal{O})$ . We have to prove that this case  $[a] \leadsto [b]$  is in fact a mapping (we do this by showing that the chasing does not change cohomology class) and we have to show that the map created is bijective, which is not too hard.

## Chapter 3

# Symplectic and Kaehler Geometry

#### Lecture 12

Today: Symplectic geometry and Kaehler geometry, the linear aspects anyway.

#### Symplectic Geometry

Let V be an n dimensional vector space over  $\mathbb{R}$ ,  $B: V \times V \to \mathbb{R}$  a bilinear form on V.

**Definition.** B is alternating if B(v, w) = -B(w, v). Denote by  $Alt^2(V)$  the space of all alternating bilinear forms on V.

**Definition.** Take any  $B \in Alt(V)$ , U a subspace of V. Then we can define the orthogonal complement by

$$U^{\perp} = \{ v \in V, B(u, v) = 0, \forall u \in U \}$$

**Definition.** B is non-degenerate if  $V^{\perp} = \{0\}$ .

**Theorem.** If B is non-degenerate then dim V is even. Moeover, there exists a basis  $e_1, \ldots, e_n, f_1, \ldots, f_n$  of V such that  $B(e_i, e_n) = B(f_i, f_j) = 0$  and  $B(e_i, f_j) = \delta_{ij}$ 

**Definition.** B is non-degenerate if and only if the pair (V, B) is a symplectic vector space. Then  $e_i$ 's and  $f_i$ 's are called a Darboux basis of V.

Let B be non-degenerate and U a vector subspace of V

 $\dim U^{\perp} = 2n - \dim V$  and we have the following 3 scenarios.

- 1. U isotropic  $\Leftrightarrow U^{\perp} \supset U$ . This implies that dim  $U \leq n$
- 2. U Lagrangian  $\Leftrightarrow U^{\perp} = U$ . This implies dim U = n.
- 3. U symplectic  $\Leftrightarrow U^{\perp} \cap U = \emptyset$ . This implies that  $U^{\perp}$  is symplectic and  $B|_{U}$  and  $B|_{U^{\perp}}$  are non-degenerate. Let  $V = V^{m}$  be a vector space over  $\mathbb{R}$  we have

$$\operatorname{Alt}^2(V) \cong \Lambda^2(V^*)$$

is a canonical identification. Let  $v_1, \ldots, v_m$  be a basis of v, then

$$\operatorname{Alt}^{2}(V)\ni B\mapsto \frac{1}{2}\sum B(v_{i},v_{j})v_{i}^{*}\wedge v_{j}^{*}$$

and the inverse  $\Lambda^2(V^*) \ni \omega \mapsto B_\omega \in \mathrm{Alt}^2(V)$  is given by

$$B(v, w) = i_W(i_V\omega)$$

Suppose m=2n.

**Theorem.**  $B \in Alt^2(V)$  is non-degenerate if  $\omega_B \in \Lambda^2(V)$  satisfies  $\omega_B^n \neq 0$ 

1/2 of Proof. B non-degenerate, let  $e_1, \ldots, f_n$  be a Darboux basis of V then

$$\omega_B = \sum e_i^* \wedge f_j^*$$

and we can show

$$\omega_B^n = n! e_1^* \wedge f_1^* \wedge \dots \wedge e_n^* \wedge f_n^* \neq 0$$

**Notation.**  $\omega \in \Lambda^2(V^*)$ , symplectic geometers just say " $B_{\omega}(v, w) = \omega(v, w)$ ".

#### Kaehler spaces

 $V=V^{2n}, V$  a vector space over  $R, B \in \text{Alt}^2(V)$  is non-generate. Assume we have another piece of structure a map  $J:V \to V$  that is  $\mathbb{R}$ -linear and  $J^2=-I$ .

**Definition.** B and J are compatible if B(v, w) = B(Jv, Jw).

Exercise(not to be handed in) Let Q(v, w) = B(v, Jw) show that B and J are compatible if and only if Q is symmetric.

From J we can make V a vector space over  $\mathbb{C}$  by setting  $\sqrt{-1}v = Jv$ . So this gives V a structure of complex n-dimensional vector space.

**Definition.** Take the bilinear form  $H: V \times V \to \mathbb{C}$  by

$$H(v, w) = \frac{1}{\sqrt{-1}}(B(v, w) + \sqrt{-1}Q(v, w))$$

B and J are compatible if and only if H is hermitian on the complex vector space V. Note that H(v,v) = Q(v,v).

**Definition.** V, J, B is Kahler if either H is positive definite or Q is positive definite (these two are equivalent).

Consider  $V^* \otimes \mathbb{C} = \operatorname{Hom}_{\mathbb{R}}(V, \mathbb{C})$ , so if  $l \in V^* \otimes \mathbb{C}$  then  $l : V \to \mathbb{C}$ .

**Definition.**  $l \in (V^*)^{1,0}$  if it is  $\mathbb{C}$ -linear, i.e.  $l(Jv) = \sqrt{-1}l(v)$ . And  $l \in (V^*)^{0,1}$  if it is  $\mathbb{C}$ -antilinear, i.e.  $l(Jv) = -\sqrt{-1}l(v).$ 

**Definition.**  $\bar{l}v = \overline{l(v)}$ .  $J^*l(v) = lJ(v)$ .

Then if  $l \in (V^*)^{1,0}$  then  $\bar{l} \in (V^*)^{0,1}$ . If  $l \in (V^*)^{1,0}$  then  $J^*l = \sqrt{-1}l$ ,  $l \in (V^*)^{0,1}$ ,  $J^*l = -\sqrt{-1}l$ . So we can decompose  $V^* \otimes \mathbb{C} = (V^*)^{1,0} \oplus (V^*)^{0,1}$  i.e. decomposing into  $\pm \sqrt{-1}$  eigenspace of  $J^*$  and

 $(V^*)^{0,1} = \overline{(V^*)^{0,1}}.$ 

This decomposition gives a decomposition of the exterior algebra,  $\Lambda^r(V^* \otimes \mathbb{C}) = \Lambda^r(V^*) \otimes \mathbb{C}$ . Now, this decomposes into bigraded pieces

$$\Lambda^r(V^*\otimes \mathbb{C}) = \bigoplus_{k+l=r} \Lambda^{k,l}(V^*)$$

 $\Lambda^{k,l}(V^*)$  is the linear span of k,l forms of the form

$$\mu_1 \wedge \cdots \wedge \mu_k \wedge \bar{\nu}_1 \wedge \cdots \wedge \bar{\nu}_l \qquad \mu_i \nu_i \in (V^*)^{1,0}$$

Note that  $J^*: V^* \otimes \mathbb{C} \to V^* \otimes \mathbb{C}$  can be extended to a map  $J^*: \Lambda^r(V^* \otimes \mathbb{C}) \to \Lambda^r(V^* \otimes \mathbb{C})$  by setting

$$J^*(l_1 \wedge \cdots \wedge l_r) = J^*l_1 \wedge \cdots \wedge J^*l_r$$

on decomposable elements  $l_1 \wedge \cdots \wedge l_r \in \Lambda^r$ . We can define complex conjugation on  $\Lambda^r(V^* \otimes \mathbb{C})$  on decomposable elements  $\omega = l_1 \wedge \cdots \wedge l_r$  by  $\bar{\omega} = \bar{l}_1 \wedge \cdots \wedge \bar{l}_r$ .  $\Lambda^r(V^* \otimes \mathbb{C}) = \Lambda^r(V) \otimes \mathbb{C}$ , then  $\bar{\omega} = \omega$  if and only if  $\omega \in \Lambda^r(V^*)$ . And if  $\omega \in \Lambda^{k,l}(V^*)$  then  $\bar{\omega} \in \Lambda^{l,k}(V^*)$ 

**Proposition.** On  $\Lambda^{k,l}(V^*)$  we have  $J^* = (\sqrt{-1})^{k-l} \operatorname{Id}$ .

*Proof.* Take  $\omega = \mu_1 \wedge \cdots \wedge \mu_k \wedge \bar{\nu}_1 \wedge \cdots \wedge \bar{\nu}_l, \ \mu_i, \nu_i \in (V^*)^{1,0}$  then

$$J^*\omega = J^*\mu_1 \wedge \dots \wedge J^*\mu_k \wedge J^*\bar{\nu}_1 \wedge \dots \wedge J^*\bar{\nu}_l = (-1)^k (-\sqrt{-1})^l \omega$$

Notice that for the following decomposition of  $\Lambda^2(V \otimes \mathbb{C})$  the eigenvalues of  $J^*$  are given below

$$\underbrace{\Lambda^2(V\otimes\mathbb{C})}_{I^*} = \underbrace{\Lambda^{2,0}}_{1} \oplus \underbrace{\Lambda^{1,1}}_{-1} \oplus \underbrace{\Lambda^{0,2}}_{-1}$$

So if  $\omega \in \Lambda^*(V^* \otimes \mathbb{C})$  then if  $J\omega = \omega$ .

Now, back to serious Kahler stuff.

Let V, B, J be Kahler.  $B \mapsto \omega_B \in \Lambda^2(V^*) \subset \Lambda^2(V^*) \otimes \mathbb{C}$ .

B is J invariant, so  $\omega_B$  is J-invariant, which happens if and only if  $\omega_B \in \Lambda^{1,1}(V^*)$  and  $\omega_B$  is real if and only if  $\bar{\omega}_B = \omega_B$ .

So there is a -1 correspondence between J invariant elements of  $\Lambda^2(V)$  and elements  $\omega \in \Lambda^{1,1}(V^*)$  which are real.

Observe:  $(V^*)^{1,0} \otimes V^*)^{0,1} \xrightarrow{\rho} \Lambda^{1,1}(V^*)$  by  $\mu \otimes \nu \mapsto \mu \wedge \nu$ . Let  $\mu_1, \ldots, \mu_n$  be a basis of  $(V^*)^{1,0}$ . Take

$$\alpha = \sum a_{ij}\mu_i \otimes \bar{\mu}_j \in (V^*)^{1,0} \otimes (V^*)^{0,1}$$

Take

$$\rho(\alpha) = \sum a_{ij}\mu_i \wedge \bar{\mu}_j$$

is it true that  $\overline{\rho(\alpha)} = \rho(\alpha)$ . No, not always. This happens if  $a_{ij} = -\overline{a_{ij}}$ , equivalently  $\frac{1}{\sqrt{-1}}[a_{ij}]$  is Hermitian. We have

$$\operatorname{Alt}^2(V) \ni B \mapsto \omega = \omega_B \in \Lambda^{1,1}(V^*)$$

Take  $\alpha = \rho^{-1}(\omega)$ ,  $H = \frac{1}{\sqrt{-1}}\alpha$ . Then H is Hermitian.

Check that  $H = \frac{1}{\sqrt{-1}}(B + \sqrt{-1}Q)$ , B Kahler iff and only if H is positive definite.

#### Lecture 13

 $X^{2n}$  a real  $C^{\infty}$  manifold. Have  $\omega \in \Omega^2(X)$ , with  $\omega$  closed.

For  $p \in X$  we saw last time that  $\Lambda^2(T_p^*) \cong \operatorname{Alt}^2(T_p)$ , so  $\omega_p \leftrightarrow B_p$ .

**Definition.**  $\omega$  is symplectic if for every point p,  $B_p$  is non-degenerate.

Remark: Alternatively  $\omega$  is symplectic if and only if  $\omega^n$  is a volume form. i.e.  $\omega_p^n \neq 0$  for all p.

**Theorem (Darboux Theorem).** If  $\omega$  is symplectic then for every  $p \in X$  there exists a coordinate patch  $(U, x_1, \ldots, x_n, y_1, \ldots, y_n)$  centered at p such that on U

$$\omega = \sum dx_i \wedge dy_i$$

(in Anna Cannas notes)

Suppose  $X^{2n}$  is a complex *n*-dimensional manifold. Then for  $p \in X$ ,  $T_pX$  is a complex *n*-dimensional vector space. So there exists an  $\mathbb{R}$ -linear map  $J_p: T_p \to T_p$ ,  $J_pv = \sqrt{-1}v$  with  $J_p^2 = -I$ .

**Definition.**  $\omega$  symplectic is Kahler if for every  $p \in X$ ,  $B_p$  and  $J_p$  are compatible and the quadratic form

$$Q_p(v, w) = B_p(v, J_p w)$$

is positive definite.

This  $Q_p$  is a positive definite symmetric bilinear form on  $T_p$  for all p, so X is a Riemannian manifold as well.

We saw earlier that  $J_p$  and  $B_p$  are compatible is equivalent to the assumption that  $\omega \in \Lambda^{1,1}(T_p^*)$ . Last time we say there was a mapping

$$\rho: (T^*)^{1,0} \otimes (T^*)^{0,1} \xrightarrow{\cong} \Lambda^{1,1}(T_p^*) \qquad H_p \leftrightarrow \omega_p$$

The condition  $\bar{\omega}_p = \omega_p$  tells us that  $H_p$  is a hermitian bilinear form on  $T_p$ . The condition that  $Q_p$  is positive definite implies that  $H_p$  is positive definite.

Let  $(U, z_1, \ldots, z_n)$  be a coordinate patch on X

$$\omega = \sqrt{-1} \sum h_{ij} dz_i \wedge d\bar{z}_j \qquad h_{i,j} \in C^{\infty}(U)$$

SO

$$H_p = \sum h_{ij}(p)(dz_i)_p \otimes (d\bar{z}_j)_p$$

the condition that  $H_p \gg 0$  ( $\gg$  means positive definite) implies that  $h_{ij}(p) \gg 0$ . What about the Riemannian structure? The Riemannian arc-length on U is given by

$$ds^2 = \sum h_{ij} dz_i d\bar{z}_j$$

#### Darboux Theorem for Kahler Manifolds

Let  $(U, z_1, \ldots, z_n)$  be a coordinate patch on X, let U be biholomorphic to a polydisk  $|z_1| < \epsilon_1, \ldots, |z_n| < \epsilon_n$ . Let  $\omega \in \Omega^{1,1}(U)$ ,  $d\omega = 0$  be a Kaehler form.  $d\omega = 0$  implies that  $\overline{\partial}\omega = \partial\omega = 0$ , which implies (by a theorem we proved earlier) that for some F

$$\omega = \sqrt{-1}\partial \overline{\partial} F \qquad F \in C^{\infty}(U)$$

(it followed from the exactness of the Dolbeault complex). Also, since  $\overline{\omega} = \omega$  we get that

$$\omega = \overline{\omega} = -\sqrt{-1}\partial \overline{\partial} F = \sqrt{-1}\partial \overline{\partial} \overline{F}$$

So replacing F by  $\frac{1}{2}(F+\overline{F})$  we can assume that F is real-valued. Moreover

$$\omega = \sqrt{-1}\partial \overline{\partial} F = \sqrt{-1} \sum_{i} \frac{\partial^{2} F}{\partial z_{i} \partial \overline{z}_{j}} dz_{i} \wedge d\overline{z}_{j}$$

so we conclude that

$$\frac{\partial^2 F}{\partial z_i \partial \bar{z}_i}(p) \gg 0$$

for all  $p \in U$ , i.e.  $F \in C^{\infty}(U)$  is a strictly plurisubharmonic function. So we've proved

**Theorem (Darboux).** If  $\omega$  is a Kahler form then for every point  $p \in X$  there exists a coordinate patch  $(U, z_1, \ldots, z_n)$  cenetered at p and a strictly plurisubharmonic function F on U such that on  $U, \omega = \sqrt{-1}\partial \bar{\partial} F$ .

All of the local structure is locally encoded in F, the symplectic form, the Kahler form etc.

#### **Definition.** F is called the **potential function**

This function is not unique, but how not-unique is it?

Let U be a simply connected open subset of X and let  $F_1, F_2 \in C^{\infty}(U)$  be potential functions for the <u>K</u>ahler metric. Let  $G = F_1 - F_2$ . If  $\partial \overline{\partial} F_1 = \partial \overline{\partial} F_2$  then  $\partial \overline{\partial} G = 0$ . Now,  $\partial \overline{\partial} G = 0$  implies that  $\overline{d} \overline{\partial} G = 0$ , so  $\overline{\partial}G$  is a closed 1-form. U simply connected implies that there exists an  $H\in C^{\infty}(U)$  so that  $\overline{\partial}G=dH$ , so  $\overline{\partial}G = \overline{\partial}H$ , and  $\partial H = 0$ .

Let  $K_1 = G - H$ ,  $K_2 = \overline{H}$ ,  $K_1, K_2 \in \mathcal{O}$ . Ten  $G = K_1 + \overline{K_2}$ . But G is real-valued, so  $\overline{G} = G$  so  $K_1 + \overline{K_2} = \overline{K_1} + K_2$  which implies  $K_1 - K_2 = \overline{K_1} - \overline{K_2}$  so  $K_1 - K_2$  is a real-valued holomorphic function on U. But real valued and holomorphic implies that the function is constant. Thus  $K_1 - K_2$  is a constant. Adjusting this constant we get that  $K_{\underline{1}} = K_2$ .

Let 
$$K = K_1 = K_2$$
, then  $G = K + \frac{\overline{K}}{K}$ .

**Theorem.** If  $F_1$  and  $F_2$  are potential functions for the Kahler metric  $\omega$  on U then  $F_1 = F_2 + (K + \overline{K})$  where  $K \in \mathcal{O}(U)$ .

**Definition.** Let X be a complex manifold, U any open subset of X.  $F \in C^{\infty}(U)$ , F is strictly plurisubharmonic if  $\sqrt{-1}\partial \overline{\partial} F = \omega$  is a Kahler form on U. This is the **coordinate free definition of s.p.s.h** 

**Definition.** An open set U of X is pseudoconvex if it admits a s.p.s.h. exhaustion function.

Remarks: U is pseudoconvex if the Dolbeault complex is exact.

**Definition.** X is a stein manifold if it is pseudoconvex

#### **Examples of Kaehler Manifolds**

1.  $\mathbb{C}^n$ . Let  $F = |z|^2 = |z_1|^2 + \cdots + |z_n|^2$  and then

$$\sqrt{-1}\partial \overline{\partial} f = \sqrt{-1} \sum dz_i \wedge d\overline{z}_j = \omega$$

and if we say  $z_i = x_i + \sqrt{-1}y$  then

$$\omega = 2\sum dx_i \wedge dy_i$$

then standard Darboux form.

- 2. Stein manifolds.
- 3. Complex submanifolds of Kaehler manifolds. We claim that if  $X^n$  is a complex manifold,  $Y^k$  a complex submanifold in X if  $\iota: Y \to X$  is an inclusion. Then
  - (a) If  $\omega$  is a Kaehler form on X,  $\iota^*\omega$  is a Kaehler form.
  - (b) If U is an open subset of X and  $F \in C^{\infty}(U)$  is a potential function for  $\omega$  on U the  $\iota^*F$  is a potential function for the form  $\iota^*\omega$  on  $U \cap Y$ .
  - b) implies a), so it suffices to prove b). Let  $(U, z_1, \ldots, z_n)$  be a coordinate chart adapted for Y, i.e  $Y \cap U$  is defined by  $z_{k+1} = \cdots = z_n = 0$ .  $\omega = \sqrt{-1}\partial\overline{\partial}F$  on U, so since  $\iota$  is holomorphic it commutes with  $\partial$ ,  $\overline{\partial}$ . Then

$$\iota^* \omega = \sqrt{-1} \partial \overline{\partial} \iota^* F$$
  $\iota^* F = F(z_1, \dots, z_k, 0, \dots, 0)$ 

To see this is Kaehler we need only check that  $\iota^*F$  is s.p.s.h. Take  $p \in U \cap Y$ . We consider the matrix

$$\left\lceil \frac{\partial^2 F}{\partial z_i \partial \bar{z}_j}(p) \right\rceil \qquad 1 \leq i, j \leq k$$

But this is the principle  $k \times k$  minor of

$$\left[\frac{\partial^2 F}{\partial z_i \partial \bar{z}_j}(p)\right] \qquad 1 \le i, j \le n$$

and the last matrix is positive definite, by definition (and since its a hermitian matrix its principle  $k \times k$  minors are positive definite)

4. All non-singular affine algebraic varieties.

#### Lecture 14

We discussed the Kaehler metric corresponding to the potential function  $F(z) = |z|^2 = |z_1|^2 + \cdots + |z_n|^2$ . Another interesting case is to take the potential function  $F = \text{Log}\,|z|^2$  on  $\mathbb{C}^{n+1} - \{0\}$ . This is not s.p.s.h. But recall we have a mapping

$$\mathbb{C}^{n+1} - \{0\} \xrightarrow{\pi} \mathbb{C}P^n \qquad \pi(z_0, \dots, z_n) = [z_0, \dots, z_n]$$

**Theorem.** There exists a unique Kaehler form  $\omega$  on  $\mathbb{C}P^b$  such that  $\pi^*\omega = \sqrt{-1}\partial\overline{\partial} \operatorname{Log}|z^2|$ . This is called the **Fubini-Study** symplectic form.

We'll prove this over the next few paragraphs. Let  $U_i = \{[z_0, \ldots, z_n], z_i \neq 0\}$  and let  $O_i = \pi^{-1}(U_i) = \{(z_0, \ldots, z_n), z_i \neq 0\}$ . Define  $\gamma_i : U_i \to O_i$  by mapping  $\gamma_i([z_0, \ldots, z_n]) = (z_0, \ldots, z_n)/z_i$ . Notice that  $\pi \circ \gamma_i = \mathrm{id}_{U_i}$  and  $\gamma_i \circ \pi(z_0, \ldots, z_n) = (z_0, \ldots, z_n)/z_i$ .

**Lemma.** Let  $\mu = \sqrt{-1}\partial \overline{\partial} \operatorname{Log} |z|^2$  on  $\mathbb{C}^{n+1} - \{0\}$ . Then on  $O_i$  we have  $\pi^* \gamma_i^* \mu = \mu$ .

$$\pi^* \gamma_i^* \operatorname{Log} |z|^2 = (\gamma_i \pi)^* \operatorname{Log} |z|^2 = \operatorname{Log} \left( \frac{|z|^2}{|z_i|^2} \right) = \operatorname{Log} |z|^2 - \operatorname{Log} |z_i|^2$$

$$\pi^* \gamma_i^* \mu = \sqrt{-1} \pi^* \gamma_i^* \partial \overline{\partial} \operatorname{Log} |z|^2 = \sqrt{-1} \partial \overline{\partial} (\operatorname{Log} |z|^2 - \operatorname{Log} |z_i|^2)$$

$$= \sqrt{-1} \partial \overline{\partial} (\operatorname{Log} |z|^2 - \operatorname{Log} z_i - \operatorname{Log} \overline{z}_i) = \sqrt{-1} \partial \overline{\partial} \operatorname{Log} |z|^2 = \mu$$

Corollary. We have local existence and uniqueness of  $\omega$  on each  $U_i$ , which implies global existence and uniqueness.

So we know there exists  $\omega$  on  $\mathbb{C}P^n$  such that  $\pi^*\omega = \sqrt{-1}\partial\overline{\partial}\operatorname{Log}|z|^2$ . We want to show that Kaehlerity of  $\omega$ . Define

$$\rho_i: \mathbb{C}^n \to O_i \qquad \rho_i(z_1, \dots, z_n) = (z_1, \dots, 1, \dots, z_n)$$

Then  $\pi \circ \rho_i : \mathbb{C}^n \to U_i$  is a biholomorphism. It suffices to check that

$$(\pi \circ \rho_i)^* \omega = \rho_i^* \pi^* \omega = \rho^* \mu = \rho_i^* (\sqrt{-1} \partial \overline{\partial} \operatorname{Log} |z|^2)$$
$$= \sqrt{-1} \partial \overline{\partial} \operatorname{Log} (1 + |z_i|^2 + \dots + |z_n|^2) = \sqrt{-1} \partial \overline{\partial} \operatorname{Log} (1 + |z|^2)$$

We must check that  $Log(1 + |z|^2)$  is s.p.s.h.

$$\frac{\partial}{\partial \bar{z}_{j}} \operatorname{Log}(1+|z|^{2}) = \frac{z_{j}}{1+|z|^{2}}$$

$$\frac{\partial}{\partial z_{i}} \partial \partial \bar{z}_{j} \operatorname{Log}(1+|z|^{2}) = \frac{\delta_{ij}}{1+|z|^{2}} - \frac{\bar{z}_{i}z_{j}}{(1+|z|^{2})^{2}} = \frac{1}{1+|z|^{2}} ((1+|z|^{2}\delta_{ij} - z_{j}\bar{z}_{i}))$$

We have to check that the term in parentheses is positive, but thats not too hard.

Corollary. All complex submanifolds of  $\mathbb{C}P^n$  are Kaehler.

Suppose we have  $(X, \omega)$  a Kaehler manifold. We can associate to  $\omega \in \Omega^{1,1}(X)$  another closed 2-form  $\mu \in \Omega^{1,1}(X)$  called the **Ricci form** 

Let  $(U, z_1, \ldots, z_n)$  be a coordinate patch. Let  $F \in C^{\infty}(U)$  be a potential function for  $\omega$  on U, i.e.  $\omega = \sqrt{-1}\partial \overline{\partial} F$ . Let

$$G = \det\left(\frac{\partial F}{\partial z_i \partial \bar{z}_j}\right)$$

This is real and positive, so the log is well defined. Define

$$\mu = \sqrt{-1}\partial \overline{\partial} \operatorname{Log} G$$

**Lemma.**  $\mu$  is intrinsically defined, i.e. it is independent of F and the coordinate system

*Proof.* Independent of F Take  $F_1, F_2$  to be potential functions of  $\omega$  on U. Then  $\partial \overline{\partial} F_1 = \partial \overline{\partial} F_2$ , which, in coordinates means that

$$\left[\frac{\partial F_1}{\partial z_i \partial \bar{z}_j}\right] = \left[\frac{\partial F_2}{\partial z_i \partial \bar{z}_j}\right]$$

**Independent of Coordinates** On  $U \cap U'$  the formula's look like

$$\frac{\partial F}{\partial z_i \partial \bar{z}_j} = \sum_{k,l} \frac{\partial^2 F}{\partial z_k' \partial \bar{z}_l'} \frac{\partial z_k'}{\partial z_i} \frac{\partial \bar{z}_l}{\partial z_j'}$$

or in matrix notation

$$\left[\frac{\partial F}{\partial z_i \partial \bar{z}_j}\right] = \left[\frac{\partial z_k'}{\partial z_i}\right] \cdot \left[\frac{\partial^2 F}{\partial z_k' \partial \bar{z}_l'}\right] \cdot \left[\frac{\partial \bar{z}_l'}{\partial \bar{z}_j}\right]$$

taking determinants we get

$$\det\left[\frac{\partial F}{\partial z_i\partial\bar{z}_j}\right] = \left[\frac{\partial^2 F}{\partial z_k'\partial\bar{z}_l'}\right]H\bar{H}$$

where

$$H = \det\left[\frac{z_k'}{z_l}\right]$$

SO

$$\operatorname{Log} \det \left[ \frac{\partial F}{\partial z_i \partial \bar{z}_j} \right] = \operatorname{Log} \det \left[ \frac{\partial^2 F}{\partial z_i' \partial \bar{z}_j'} \right] + \operatorname{Log} \det H + \operatorname{Log} \det \bar{H}$$

 $\text{Log } H \in \mathcal{O}(U)$  (at least on a branch). Apply  $\partial \overline{\partial}$  to both sides of the above. That finishes it.

**Definition.**  $X, \omega$  a Kaehler manifold and  $\mu$  is the Ricci form. Then X is called **Kaehler-Einstein** if there exists a constant such that  $\mu = \lambda \omega$ .

Take  $\mu = \lambda \omega$ ,  $\lambda \neq 0$ . Let  $(U, z_1, \dots, z_n)$  be a coordinate patch. For  $F \in C^{\infty}(U)$  a potential function for  $\omega$  on U

$$\mu = \sqrt{-1}\partial \overline{\partial} \operatorname{Log} \det \left( \frac{\partial^2 F}{\partial z_i \partial \overline{z}_i} \right) = \lambda \omega = \lambda \sqrt{-1}\partial \overline{\partial} F$$

By a theorem we proved last time

$$\operatorname{Log} \det \left( \frac{\partial^2 F}{\partial z_i \partial \bar{z}_j} \right) = \lambda F = G + \overline{G} \qquad G \in \mathcal{O}(U)$$

Take F and replace it by

$$F \leadsto F + \frac{1}{\lambda}(G + \overline{G})$$

then

$$\operatorname{Log} \det \left( \frac{\partial^2 F}{\partial z_i \partial \bar{z}_j} \right) = \lambda F \qquad \overline{\det \left( \frac{\partial^2 F}{\partial z_i \partial \bar{z}_j} \right)} = e^{\lambda F}$$

The boxed formula is the Monge-Ampere equation. This is essential an equation for constructing Einstein-Kahler metrics.

**Exercise** Check that the Fubini-Study potential is Kaehler-Einstein with  $\lambda = -(n+1)$ .  $F = \text{Log}(1+|z|^2)$  locally on each  $U_i$ . So we need to check that  $F = \text{Log}(1+|z|^2)$  satisfies the Monge-Ampere equations.

#### Lecture 15

Homework problem number 2. X a complex manifold. We know we have the splitting

$$\Omega^r(X) = \bigoplus_{p+q} \Omega^{p,q}(X) \qquad d = \partial + \overline{\partial}$$

We get the Dolbeault complex  $\Omega^{0,0}(X) \xrightarrow{\bar{\partial}} \Omega^{0,1}(X) \xrightarrow{\bar{\partial}} \dots$  and for every p we get a generalized Dolbeault complex

$$\Omega^{p,0}(X) \xrightarrow{\overline{\partial}} \Omega^{p,1}(X) \xrightarrow{\overline{\partial}} \Omega^{p,2}(X) \xrightarrow{\overline{\partial}} \cdots$$

this is the p-Dolbeault complex. Take  $\ker \overline{\partial}: \Omega^{0,0}(X) \to \Omega^{0,1}(X)$  this is  $\mathcal{O}(X)$  and in general  $\ker \overline{\partial}: \Omega^{0,0}(X) \to \Omega^{0,1}(X)$  $\Omega^{p,0}(X) \to \Omega^{p,1}(X)$ . Call this  $A^p(X)$ . For  $\mu \in A^p(X)$  pick a coordinate patch  $(U, z_1, \dots, z_n)$  then

$$\mu = \sum f_I(z)dz_{i_1} \wedge \dots \wedge dz_{i_p}$$

and  $\overline{\partial}\mu = 0$  implies that  $\overline{\partial}f_I = 0$ , so  $f_I \in \mathcal{O}(U)$ . These  $A^p$  are called the holomorphic de Rham complex. More general, take U open in X. Then  $\mathcal{A}^p(X)$  defines a sheaf  $\mathcal{A}^p$  on X. Exercise Let  $U = \{U_i, i \in I\}$  be a cover of X by pseudoconvex open sets. Show that the Cech cohomology group  $H^q(U, \mathcal{A}^p)$  coincide with the cohomology groups of

$$\Omega^{p,0}(X) \xrightarrow{\overline{\partial}} \Omega^{p,1}(X) \xrightarrow{\overline{\partial}} \Omega^{p,2}(X) \xrightarrow{\overline{\partial}} \cdots$$

We did the special case p=0, i.e. we showed  $H^q(U,\mathcal{O})\cong$  the Dolbeault complex.

The idea is to reduce this to the following exercise in diagram chasing. Let  $C = \bigoplus C^{i,j}$  be a bigraded vector space with commuting coboundary operators  $\delta: C^{i,j} \to C^{i+1,j}$  and  $d: C^{i,j} \to C^{i,j+1}$ .

Let  $V_i = \ker d_i : C^{i,0} \to \check{C}^{i,1}$ . Note that since  $d\delta = \delta d$  that  $\delta V_i \subset V_{i+1}$ . Also let  $W = \ker \delta_i : C^{0,i} \to C^{1,i}$ and  $dW_i \subset W_{i+1}$ .

Theorem. Suppose that the sequence

$$C^{0,i} \xrightarrow{\delta} C^{1,i} \xrightarrow{\delta} C^{2,i} \xrightarrow{\delta} \cdots$$

and the sequence

$$C^{i,0} \xrightarrow{d} C^{i,1} \xrightarrow{d} C^{i,2} \xrightarrow{d} \cdots$$

are exact for all i. Prove that the cohomology groups of

$$0 \longrightarrow V_0 \xrightarrow{\delta} V_1 \xrightarrow{\delta} V_2 7 \xrightarrow{\delta} \cdots$$

and

$$0 \longrightarrow W_0 \xrightarrow{d} W_1 \xrightarrow{d} W_2 \xrightarrow{d} \cdots$$

are isomorphic.

## Chapter 4

# Elliptic Operators

### Lecture 16

This chapter by Victor Guillemin

## 4.1 Differential operators on $\mathbb{R}^n$

Let U be an open subset of  $\mathbb{R}^n$  and let  $D_k$  be the differential operator,

$$\frac{1}{\sqrt{-1}} \frac{\partial}{\partial x_k}.$$

For every multi-index,  $\alpha = \alpha_1, \dots, \alpha_n$ , we define

$$D^{\alpha} = D_1^{\alpha_1} \cdots D_n^{\alpha_n} .$$

A differential operator of order r:

$$P: \mathcal{C}^{\infty}(U) \to \mathcal{C}^{\infty}(U)$$
,

is an operator of the form

$$Pu = \sum_{|\alpha| < r} a_{\alpha} D^{\alpha} u, \quad a_{\alpha} \in \mathcal{C}^{\infty}(U).$$

Here  $|\alpha| = \alpha_1 + \cdots + \alpha_n$ .

The symbol of P is roughly speaking its "r<sup>th</sup> order part". More explicitly it is the function on  $U \times \mathbb{R}^n$  defined by

$$(x,\xi) \to \sum_{|\alpha|=r} a_{\alpha}(x)\xi^{\alpha} =: p(x,\xi).$$

The following property of symbols will be used to define the notion of "symbol" for differential operators on manifolds. Let  $f: U \to \mathbb{R}$  be a  $\mathcal{C}^{\infty}$  function.

Theorem. The operator

$$u \in \mathcal{C}^{\infty}(U) \to e^{-itf} P e^{itf} u$$

 $is \ a \ sum$ 

$$\sum_{i=0}^{r} t^{r-i} P_i u \tag{4.1.1}$$

 $P_i$  being a differential operator of order i which doesn't depend on t. Moreover,  $P_0$  is multiplication by the function

$$p_0(x) =: P(x, \xi)$$

with  $\xi_i = \frac{\partial f}{\partial x_i}$ ,  $i = 1, \dots n$ .

*Proof.* It suffices to check this for the operators  $D^{\alpha}$ . Consider first  $D_k$ :

$$e^{-itf}D_k e^{itf}u = D_k u + t \frac{\partial f}{\partial x_k}.$$

Next consider  $D^{\alpha}$ 

$$e^{-itf}D^{\alpha}e^{itf}u = e^{-itf}(D_1^{\alpha_1} \cdots D_n^{\alpha_n})e^{itf}u$$
$$= (e^{-itf}D_1e^{itf})^{\alpha_1} \cdots (e^{-itf}D_ne^{itf})^{\alpha_n}u$$

which is by the above

$$(D_1 + t \frac{\partial f}{\partial x_1})^{\alpha_1} \cdots (D_n + t \frac{\partial f}{\partial x_n})^{\alpha_n}$$

and is clearly of the form (4.1.1). Moreover the  $t^r$  term of this operator is just multiplication by

$$\left(\frac{\partial}{\partial x_1}f\right)^{\alpha_1}\cdots\left(\frac{\partial}{\partial x_n}\right)^{\alpha_n}.$$
 (4.1.2)

**Corollary.** If P and Q are differential operators and  $p(x,\xi)$  and  $q(x,\xi)$  their symbols, the symbol of PQ is  $p(x,\xi) q(x,s)$ .

*Proof.* Suppose P is of the order r and Q of the order s. Then

$$e^{-itf}PQe^{itf}u = (e^{-itf}Pe^{itf})(e^{-itf}Qe^{itf})u$$
$$= (p(x, df)t^r + \cdots)(q(x, df)t^s + \cdots)u$$
$$= (p(x, df)q(x, df)t^{r+s} + \cdots)u.$$

Given a differential operator

$$P = \sum_{|\alpha| \le r} a_{\alpha} D^{\alpha}$$

we define its *transpose* to be the operator

$$u \in \mathcal{C}^{\infty}(U) \to \sum_{|\alpha| \le r} D^{\alpha} \overline{a}_{\alpha} u =: P^{t} u.$$

**Theorem.** For  $u, v \in \mathcal{C}_0^{\infty}(U)$ 

$$\langle Pu, v \rangle =: \int Pu\overline{v} \, dx = \langle u, P^t \rangle.$$

*Proof.* By integration by parts

$$\langle D_k u, v \rangle = \int D_k u \overline{v} \, dx = \frac{1}{\sqrt{-1}} \int \frac{\partial}{\partial x_k} u \overline{v} \, dk$$
$$= -\frac{1}{\sqrt{-1}} \int u \frac{\partial}{\partial x_k} \overline{v} \, dx = \int u \overline{D_k v} \, dx$$
$$= \langle u, d_k v \rangle.$$

Thus

$$\langle D^{\alpha}u, v \rangle = \langle u, D^{\alpha}v \rangle$$

and

$$\langle a_{\alpha}D^{\alpha}u, v \rangle = \langle D^{\alpha}u, \overline{a}_{\alpha}v \rangle = \langle u, D^{\alpha}\overline{a}_{\alpha}v \rangle,$$

#### Exercises.

If  $p(x,\xi)$  is the symbol of  $P, \overline{p}(x,\xi)$  is the symbol of  $p^t$ .

#### Ellipticity.

P is elliptic if  $p(x,\xi) \notin 0$  for all  $x \in U$  and  $\xi \in \mathbb{R}^n - 0$ .

## 4.2 Differential operators on manifolds.

Let U and V be open subsets of  $\mathbb{R}^n$  and  $\varphi: U \to V$  a diffeomorphism. Claim. If P is a differential operator of order m on U the operator

$$u \in \mathcal{C}^{\infty}(V) \to (\varphi^{-1})^* P \varphi^* u$$

is a differential operator of order m on V.

*Proof.*  $(\varphi^{-1})^*D^{\alpha}\varphi^* = ((\varphi^{-1})^*D_1\varphi^*)^{\alpha_1}\cdots((\alpha^{-1})^*D_n\varphi^*)^{\alpha_n}$  so it suffices to check this for  $D_k$  and for  $D_k$  this follows from the chain rule

$$D_k \varphi^* f = \sum \frac{\partial \varphi_i}{\partial x_k} \varphi^* D_i f.$$

This invariance under coordinate changes means we can define differential operators on manifolds.

**Definition.** Let  $X = X^n$  be a real  $\mathcal{C}^{\infty}$  manifold. An operator,  $P : \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$ , is an  $m^{\text{th}}$  order differential operator if, for every coordinate patch,  $(U, x_1, \dots, x_n)$  the restriction map

$$u \in \mathcal{C}^{\infty}(X) \to Pu1U$$

is given by an  $m^{\text{th}}$  order differential operator, i.e., restricted to U,

$$Pu = \sum_{|\alpha| \le m} a_{\alpha} D^{\alpha} u, \quad a_{\alpha} \in \mathcal{C}^{\infty}(U).$$

**Remark.** Note that this is a non-vacuous definition. More explicitly let  $(U, x_1, \ldots, x_n)$  and  $(U', x'_1, \ldots, x'_n)$  be coordinate patches. Then the map

$$u \to Pu1U \cap U'$$

is a differential operator of order m in the x-coordinates if and only if it's a differential operator in the x'-coordinates.

#### The symbol of a differential operator

**Theorem.** Let  $f: X \to \mathbb{R}$  be  $C^{\infty}$  function. Then the operator

$$u \in \mathcal{C}^{\infty}(X) \to e^{-itf} P e^{-itf} u$$

can be written as a sum

$$\sum_{i=0}^{m} t^{m-i} P_i$$

 $P_i$  being a differential operator of order i which doesn't depend on t.

*Proof.* We have to check that for every coordinate patch  $(U, x_1, \ldots, x_n)$  the operator

$$u \in \mathcal{C}^{\infty}(X) \to e^{-itf} P e^{itf} 1U$$

has this property. This, however, follows from Theorem 4.1.

In particular, the operator,  $P_0$ , is a zero<sup>th</sup> order operator, i.e., multiplication by a  $\mathcal{C}^{\infty}$  function,  $p_0$ .

**Theorem.** There exists  $C^{\infty}$  function

$$\sigma(P): T^*X \to \mathbb{C}$$

not depending on f such that

$$p_0(x) = \sigma(P)(x,\xi) \tag{4.2.1}$$

with  $\xi = df_x$ .

*Proof.* It's clear that the function,  $\sigma(P)$ , is uniquely determined at the points,  $\xi \in T_x^*$  by the property (4.2.1), so it suffices to prove the local existence of such a function on a neighborhood of x. Let  $(U, x_1, \ldots, x_n)$  be a coordinate patch centered at x and let  $\xi_1, \ldots, \xi_n$  be the cotangent coordinates on  $T^*U$  defined by

$$\xi \to \xi_1 dx_1 + \cdots + \xi_n dk_n$$
.

Then if

$$P = \sum a_{\alpha} D^{\alpha}$$

on U the function,  $\sigma(P)$ , is given in these coordinates by  $p(x,\xi) = \sum a_{\alpha}(x)\xi^{\alpha}$ . (See (4.1.2).)

#### Composition and transposes

If P and Q are differential operators of degree r and s, PQ is a differential operator of degree r + s, and  $\sigma(PQ) = \sigma(P)\sigma(Q)$ .

Let  $\mathcal{F}_X$  be the sigma field of Borel subsets of X. A measure, dx, on X is a measure on this sigma field. A measure, dx, is smooth if for every coordinate patch

$$(U, x_1, \ldots, x_n)$$
.

The restriction of dx to U is of the form

$$\varphi \, dx_1 \dots dx_n \tag{4.2.2}$$

 $\varphi$  being a non-negative  $\mathcal{C}^{\infty}$  function and  $dx_1 \dots dx_n$  being Lebesgue measure on U. dx is non-vanishing if the  $\varphi$  in (4.2.2) is strictly positive.

Assume dx is such a measure. Given u and  $v \in \mathcal{C}_0^{\infty}(X)$  one defines the  $L^2$  inner product

$$\langle u, v \rangle$$

of u and v to be the integral

$$\langle u, v \rangle = \int u \overline{v} \, dx$$
.

**Theorem.** If  $P: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$  is an  $m^{th}$  order differential operator there is a unique  $m^{th}$  order differential operator,  $P^t$ , having the property

$$\langle Pu, v \rangle = \langle u, P^t v \rangle$$

for all  $u, v \in \mathcal{C}_0^{\infty}(X)$ .

*Proof.* Let's assume that the support of u is contained in a coordinate patch,  $(U, x_1, \ldots, x_n)$ . Suppose that on U

$$P = \sum a_{\alpha} D^{\alpha}$$

and

$$dx = \varphi dx_1 \dots dx_n$$
.

Then

$$\langle Pu, v \rangle = \sum_{\alpha} \int a_{\alpha} D^{\alpha} u \overline{v} \varphi dx_{1} \dots dx_{n}$$

$$= \sum_{\alpha} \int a_{\alpha} \varphi D^{\alpha} u \overline{v} dx_{1} \dots dx_{n}$$

$$= \sum_{\alpha} \int u \overline{D^{\alpha}} \overline{a_{\alpha}} \varphi v dx_{1} \dots dx_{n}$$

$$= \sum_{\alpha} \int u \overline{\frac{1}{\varphi}} D^{\alpha} \varphi v \varphi dx_{1} \dots dx_{n}$$

$$= \langle u, P^{t} v \rangle$$

where

$$P^t v = \frac{1}{\varphi} \sum D^{\alpha} \overline{a}_{\alpha} \varphi v.$$

This proves the local existence and local uniqueness of  $P^t$  (and hence the global existence of  $P^t$ !).

#### Exercise.

$$\sigma(P^t)(x,\xi) = \overline{\sigma(P)(x,\xi)}.$$

#### Ellipticity.

P is elliptic if  $\sigma(P)(x,\xi) \neq 0$  for all  $x \in X$  and  $\xi \in T_x^* - 0$ .

The main goal of these notes will be to prove:

Theorem (Fredholm theorem for elliptic operators.). If X is compact and

$$P: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$$

is an elliptic differential operator, the kernel of P is finite dimensional and  $u \in C^{\infty}(X)$  is in the range of P if and only if

$$\langle u, v \rangle = 0$$

for all v in the kernel of  $P^t$ .

**Remark.** Since  $P^t$  is also elliptic its kernel is finite dimensional.

#### Lecture 17

## 4.3 Smoothing operators

Let X be an n-dimensional manifold equipped with a smooth non-vanishing measure, dx. Given  $K \in \mathcal{C}^{\infty}(X \times X)$ , one can define an operator

$$T_K: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$$

by setting

$$T_K f(x) = \int K(x, y) f(y) dy. \qquad (4.3.1)$$

Operators of this type are called *smoothing* operators. The definition (4.3.1) involves the cho ice of the measure, dx, however, it's easy to see that the notion of "smoothing operator" doesn't depend on this choice. Any other smooth measure will be of the form,  $\varphi(x) dx$ , where  $\varphi$  is an everywhere-positive  $\mathcal{C}^{\infty}$  function, and if we replace dy by  $\varphi(y) dy$  in (4.3.1) we get the smoothing operator,  $T_{K_1}$ , where  $K_1(x,y) = K(x,y) \varphi(y)$ .

A couple of elementary remarks about smoothing operators:

1. Let  $L(x,y) = \overline{K(y,x)}$ . Then  $T_L$  is the transpose of  $T_K$ . For f and g in  $\mathcal{C}_0^{\infty}(X)$ ,

$$\langle T_K f, g \rangle = \int \overline{g}(x) \left( \int K(x, y) f(y) \, dy \right) dx$$
  
=  $\int f(y) \overline{(T_L g)(y) \, dy} = \langle f, T_L g \rangle$ .

2. If X is compact, the composition of two smoothing operators is a smoothing operator. Explicitly:

$$T_{K_1}T_{K_2} = T_{K_3}$$

where

$$K_3(x,y) = \int K_1(x,z)K_2(z,y) dz$$
.

We will now give a rough outline of how our proof of Theorem 4.2 will go. Let  $I: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$  be the identity operator. We will prove in the next few sections the following two results.

**Theorem.** The elliptic operator, P is right-invertible modulo smoothing operators, i.e., there exists an operator,  $Q: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\hat{\infty}}(X)$  and a smoothing operator,  $T_K$ , such that

$$PQ = I - T_K \tag{4.3.2}$$

and

**Theorem.** The Fredholm theorem is true for the operator,  $I - T_K$ , i.e., the kernel of this operator is finite dimensional, and  $f \in C^{\infty}(X)$  is in the image of this operator if and only if it is orthogonal to kernel of the operator,  $I - T_L$ , where L(x, y) = K(y, x).

**Remark.** In particular since  $T_K$  is the transpose of  $T_L$ , the kernel of  $I - T_L$  is finite dimensional. The proof of Theorem 4.3 is very easy, and in fact we'll leave it as a series of exercises. (See §??.) The proof of Theorem 4.3, however, is a lot harder and will involve the theory of pseudodifferential operators on

We will conclude this section by showing how to deduce Theorem 4.2 from Theorems 4.3 and 4.3. Let V be the kernel of  $I-T_L$ . By Theorem 4.3, V is a finite dimensional space, so every element, f, of  $\mathcal{C}^{\infty}(X)$ can be written uniquely as a sum

$$f = g + h \tag{4.3.3}$$

where g is in V and h is orthogonal to V. Indeed, if  $f_1, \ldots, f_m$  is an orthonormal basis of V with respect to the  $L^2$  norm

$$g = \sum \langle f, f_i \rangle f_i$$

and h = f - g. Now let U be the orthocomplement of  $V \cap \text{Image } P$  in V.

**Proposition.** Every  $f \in C^{\infty}(M)$  can be written uniquely as a sum

$$f = f_1 + f_2 \tag{4.3.4}$$

where  $f_1 \in U$ ,  $f_2 \in \text{Image } P$  and  $f_1$  is orthogonal to  $f_2$ .

Proof. By Theorem 4.3

Image 
$$P \subset \text{Image}(I - T_K)$$
. (4.3.5)

Let g and h be the "g" and "h" in (4.3.3). Then since h is orthogonal to V, it is in Image  $(I - T_K)$  by Theorem 4.3 and hence in Image P by (4.3.5). Now let  $g = f_1 + g_2$  where  $f_1$  is in U and  $g_2$  is in the orthocomplement of U in V (i.e., in  $V \cap \text{Image } P$ ). Then

$$f = f_1 + f_2$$

where  $f_2 = g_2 + h$  is in Image P. Since  $f_1$  is orthogonal to  $g_2$  and h it is orthogonal to  $f_2$ .

Next we'll show that

$$U = \operatorname{Ker} P^t. \tag{4.3.6}$$

Indeed  $f \in U \Leftrightarrow f \perp \text{Image } P \Leftrightarrow \langle f, Pu \rangle = 0$  for all  $u \Leftrightarrow \langle P^t f, u \rangle = 0$  for all  $u \leftrightarrow P^t f = 0$ . This proves that all the assertions of Theorem 4.3 are true except for the finite dimensionality of Ker P. However, (4.3.6) tells us that Ker  $P^t$  is finite dimensional and so, with P and  $P^t$  interchanged, Ker P is finite dimensional.

## 4.4 Fourier analysis on the *n*-torus

In these notes the "n-torus" will be, by definition, the manifold:  $T^n = \mathbb{R}^n/2\pi\mathbb{Z}^n$ . A  $\mathcal{C}^{\infty}$  function, f, on  $T^n$  can be viewed as a  $\mathcal{C}^{\infty}$  function on  $\mathbb{R}^n$  which is *periodic* of period  $2\pi$ : For all  $k \in \mathbb{Z}^n$ 

$$f(x + 2\pi k) = f(x). (4.4.1)$$

Basic examples of such functions are the functions

$$e^{ikx}$$
,  $k \in \mathbb{Z}^n$ ,  $kx = k_1x_1 + \cdots k_nx_n$ .

Let  $\mathcal{P} = \mathcal{C}^{\infty}(T^n) = \mathcal{C}^{\infty}$  functions on  $\mathbb{R}^n$  satisfying (4.4.1), and let  $Q \subseteq \mathbb{R}^n$  be the open cube

$$0 < x_i < 2\pi$$
.  $i = 1, \ldots, n$ .

Given  $f \in \mathcal{P}$  we'll define

$$\int_{T^n} f \, dx = \left(\frac{1}{2\pi}\right)^n \int_Q f \, dx$$

and given  $f, g \in \mathcal{P}$  we'll define their  $L^2$  inner product by

$$\langle f, g \rangle = \int_{T^n} f \overline{g} \, dx \,.$$

I'll leave you to check that

$$\langle e^{ikx}, e^{i\ell x} \rangle$$

is zero if  $k \neq \ell$  and 1 if  $k = \ell$ . Given  $f \in \mathcal{P}$  we'll define the  $k^{\text{th}}$  Fourier coefficient of f to be the  $L^2$  inner product

$$c_k = c_k(f) = \langle f, e^{ikx} \rangle = \int_{T^n} f e^{-ikx} dx.$$

The Fourier series of f is the formal sum

$$\sum c_k e^{ikx} \,, \quad k \in \mathbb{Z}^n \,. \tag{4.4.2}$$

In this section I'll review (very quickly) standard facts about Fourier series. It's clear that  $f \in \mathcal{P} \Rightarrow D^{\alpha} f \in \mathcal{P}$  for all multi-indices,  $\alpha$ .

Proposition. If  $g = S^{\alpha f}$ 

$$c_k(q) = k^{\alpha} c_k(f)$$
.

Proof.

$$\int_{T^n} D^{\alpha} f e^{-ikx} dx = \int_{T^n} f \overline{D^{\alpha} e^{ikx}} dx.$$

Now check

$$D^{\alpha}e^{ikx} = k^{\alpha}e^{ikx}.$$

Corollary. For every integer r > 0 there exists a constant  $C_r$  such that

$$|c_k(f)| \le C_r (1+|k|^2)^{-r/2}$$
. (4.4.3)

Proof. Clearly

$$|c_k(f)| \le \frac{1}{(2\pi)^n} \int_{T^n} |f| \, dx = C_0 \, .$$

Moreover, by the result above, with  $g = D^{\alpha} f$ 

$$k^{\alpha}|C_K(f)| = |C_K(g)| \le C_{\alpha}$$

and from this it's easy to deduce an estimate of the form (4.4.3).

**Proposition.** The Fourier series (4.4.2) converges and this sum is a  $C^{\infty}$  function.

To prove this we'll need

**Lemma.** If m > n the sum

$$\sum \left(\frac{1}{1+|k|^2}\right)^{m/2}, \quad k \in \mathbb{Z}^n, \tag{4.4.4}$$

converges.

*Proof.* By the "integral test" it suffices to show that the integral

$$\int_{\mathbb{R}^n} \left( \frac{1}{1+|x|^2} \right)^{m/2} dx$$

converges. However in polar coordinates this integral is equal to

$$\gamma_{n-1} \int_0^\infty \left(\frac{1}{1+|r|^2}\right)^{m/2} r^{n-1} dr$$

 $(\gamma_{n-1})$  being the volume of the unit n-1 sphere) and this converges if m>n.

Combining this lemma with the estimate (4.4.3) one sees that (4.4.2) converges absolutely, i.e.,

$$\sum |c_k(f)|$$

converges, and hence (4.4.2) converges uniformly to a continuous limit. Moreover if we differentiate (4.4.2) term by term we get

$$D^{\alpha} \sum c_k e^{ikx} = \sum k^{\alpha} c_k e^{ikx}$$

and by the estimate (4.4.3) this converges absolutely and uniformly. Thus the sum (4.4.2) exists, and so do its derivatives of all orders.

Let's now prove the fundamental theorem in this subject, the identity

$$\sum c_k(f)e^{ikx} = f(x). \tag{4.4.5}$$

*Proof.* Let  $A \subseteq \mathcal{P}$  be the algebra of trigonometric polynomials:

$$f \in \mathcal{A} \Leftrightarrow f = \sum_{|k| \le m} a_k e^{ikx}$$

for some m.

Claim. This is an algebra of continuous functions on  $T^n$  having the Stone-Weierstrass properties

- 1) Reality: If  $f \in \mathcal{A}$ ,  $\overline{f} \in \mathcal{A}$ .
- 2)  $1 \in \mathcal{A}$ .
- 3) If x and y are points on  $T^n$  with  $x \neq y$ , there exists an  $f \in \mathcal{A}$  with  $f(x) \neq f(y)$ .

*Proof.* Item 2 is obvious and item 1 follows from the fact that  $\overline{e^{ikx}} = e^{-ikx}$ . Finally to verify item 3 we note that the finite set,  $\{e^{ix_1}, \dots, e^{ix_n}\}$ , already separates points. Indeed, the map

$$T^n \to (S^1)^n$$

mapping x to  $e^{ix_1}, \ldots, e^{ix_n}$  is bijective.

Therefore by the Stone–Weierstrass theorem  $\mathcal{A}$  is dense in  $C^0(T^n)$ . Now let  $f \in \mathcal{P}$  and let g be the Fourier series (4.4.2). Is f equal to g? Let h = f - g. Then

$$\langle h, e^{ikx} \rangle = \langle f, e^{ikx} \rangle - \langle g, e^{ikx} \rangle$$
  
=  $c_k(f) - c_k(f) = 0$ 

so  $\langle h, e^{ikx} \rangle = 0$  for all  $e^{ikx}$ , hence  $\langle h, \varphi \rangle = 0$  for all  $\varphi \in \mathcal{A}$ . Therefore since  $\mathcal{A}$  is dense in  $\mathcal{P}$ ,  $\langle h, \varphi \rangle = 0$  for all  $\varphi \in \mathcal{P}$ . In particular,  $\langle h, h \rangle = 0$ , so h = 0.

I'll conclude this review of the Fourier analysis on the n-torus by making a few comments about the  $L^2$  theory.

The space,  $\mathcal{A}$ , is dense in the space of continuous functions on  $T^n$  and this space is dense in the space of  $L^2$  functions on  $T^n$ . Hence if  $h \in L^2(T^n)$  and  $\langle h, e^{ikx} \rangle = 0$  for all k the same argument as that I sketched above shows that h = 0. Thus

 $\{e^{ikx}, k \in \mathbb{Z}^n\}$ 

is an orthonormal basis of  $L^2(T^n)$ . In particular, for every  $f \in L^2(T^n)$  let

$$c_k(f) = \langle f, e^{ikx} \rangle$$
.

Then the Fourier series of f

$$\sum c_k(f)e^{ikx}$$

converges in the  $L^2$  sense to f and one has the Plancherel formula

$$\langle f, f \rangle = \sum |c_k(f)|^2, \quad k \in \mathbb{Z}^n.$$

#### Lecture 18

## 4.5 Pseudodifferential operators on $T^n$

In this section we will prove Theorem 4.2 for elliptic operators on  $T^n$ . Here's a road map to help you navigate this section. §4.5.1 is a succinct summary of the material in §4. Sections 4.5.2, 4.5.3 and 4.5.4 are a brief account of the theory of pseudodifferential operators on  $T^n$  and the symbolic calculus that's involved in this theory. In §4.5.5 and 4.5.6 we prove that an elliptic operator on  $T^n$  is right invertible modulo smoothing operators (and that its inverse is a pseudodifferential operator). Finally, in §4.5.7, we prove that pseudodifferential operators have a property called "pseudolocality" which makes them behave in some ways like differential operators (and which will enable us to extend the results of this section from  $T^n$  to arbitrary compact manifolds).

Some notation which will be useful below: for  $a \in \mathbb{R}^n$  let

$$\langle a \rangle = (|a|^2 + 1)^{\frac{1}{2}}.$$

Thus

 $|a| \le \langle a \rangle$ 

and for  $|a| \ge 1$ 

 $\langle a \rangle \leq 2|a|$ .

#### 4.5.1 The Fourier inversion formula

Given  $f \in \mathcal{C}^{\infty}(T^n)$ , let  $c_k(f) = \langle f, e^{ikx} \rangle$ . Then:

- 1)  $c_k(D^{\alpha f}) = k^{\alpha} c_k(f)$ .
- 2)  $|c_k(f)| \le C_r \langle k \rangle^{-r}$  for all r.
- 3)  $\sum c_k(f)e^{ikx} = f$ .

Let S be the space of functions,

$$g: \mathbb{Z}^n \to \mathbb{C}$$

satisfying

$$|g(k)| \le C_r \langle k \rangle^{-r}$$

for all r. Then the map

$$F: \mathcal{C}^{\infty}(T^n) \to S, \quad Ff(k) = c_k(f)$$

is bijective and its inverse is the map,

$$g \in S \to \sum g(k)e^{ikx}$$
.

#### 4.5.2 Symbols

A function  $a: T^n \times \mathbb{R}^n \to \mathbb{C}$  is an  $\mathcal{S}^m$  if, for all multi-indices,  $\alpha$  and  $\beta$ ,

$$|D_x^{\alpha} D_{\varepsilon}^{\beta}| \le C_{\alpha,\beta} \langle \xi \rangle^{m-|\beta|} \,. \tag{5.2.1}$$

#### Examples

- 1)  $a(x,\xi) = \sum_{|\alpha| \le m} a_{\alpha}(x)\xi^{\alpha}, \ a_{\alpha} \in \mathcal{C}^{\infty}(T^n).$
- $(\xi)^m$
- 3)  $a \in \mathcal{S}^{\ell}$  and  $b \in \mathcal{S}^m \Rightarrow ab \in \mathcal{S}^{\ell+m}$ .
- 4)  $a \in \mathcal{S}^m \Rightarrow D_x^{\alpha} D_{\varepsilon}^{\beta} a \in \mathcal{S}^{m-|\beta|}$ .

#### The asymptotic summation theorem

Given  $b_i \in \mathcal{S}^{m-i}$ ,  $i = 0, 1, \ldots$ , there exists a  $b \in \mathcal{S}^m$  such that

$$b - \sum_{j < i} b_j \in \mathcal{S}^{m-i}. \tag{5.2.2}$$

*Proof. Step 1.* Let  $\ell = m + \epsilon$ ,  $\epsilon > 0$ . Then

$$|b_i(x,\xi)| < C_i \langle \xi \rangle^{m-i} = \frac{c_i \langle \xi \rangle^{\ell-i}}{\langle \xi \rangle^{\epsilon}}.$$

Thus, for some  $\lambda_i$ .

$$|b_i(x,\xi)| < \frac{1}{2^i} \langle \xi \rangle^{\ell-i}$$

for  $|\xi| > \lambda_i$ . We can assume that  $\lambda_i \to +\infty$  as  $i \to +\infty$ . Let  $\rho \in \mathcal{C}^{\infty}(\mathbb{R})$  be bounded between 0 and 1 and satisfy  $\rho(t) = 0$  for t < 1 and  $\rho(t) = 1$  for t > 2. Let

$$b = \sum \rho \left(\frac{|\xi|}{\lambda_i}\right) b_i(x,\xi). \tag{5.2.3}$$

Then b is in  $C^{\infty}(T^n \times \mathbb{R}^n)$  since, on any compact subset, only a finite number of summands are non-zero. Moreover,  $b - \sum_{j < i} b_j$  is equal to:

$$\sum_{j < i} \left( \rho \left( \frac{|\xi|}{\lambda_j} \right) - 1 \right) b_j + b_i + \sum_{j > i} \rho \left( \frac{|\xi|}{\lambda_j} \right) b_j.$$

The first summand is compactly supported, the second summand is in  $S^{m-1}$  and the third summand is bounded from above by

$$\sum_{k>i} \frac{1}{2^k} \langle \xi \rangle^{\ell-k}$$

which is less than  $\langle \xi \rangle^{\ell-(i+1)}$  and hence, for  $\epsilon < 1$ , less than  $\langle \xi \rangle^{m-i}$ .

Step 2. For  $|\alpha| + |\beta| \leq N$  choose  $\lambda_i$  so that

$$|D_x^{\alpha} D_{\xi}^{\beta} b_i(x,\xi)| \le \frac{1}{2^i} \langle \xi \rangle^{\ell - i - |\beta|}$$

for  $\lambda_i < |\xi|$ . Then the same argument as above implies that

$$D_x^{\alpha} D_{\xi}^{\beta} (b - \sum_{j,i} b_j) \le C_N \langle \xi \rangle^{m-i-|\beta|}$$

$$(5.2.4)$$

for  $|\alpha| + |\beta| \le N$ .

Step 3. The sequence of  $\lambda_i$ 's in step 2 depends on N. To indicate this dependence let's denote this sequence by  $\lambda_{i,N}$ ,  $i=0,1,\ldots$  We can, by induction, assume that for all i,  $\lambda_{i,N} \leq \lambda_{i,N+1}$ . Now apply the Cantor diagonal process to this collection of sequences, i.e., let  $\lambda_i = \lambda_{i,i}$ . Then b has the property (5.2.4) for all N. We will denote the fact that b has the property (5.2.2) by writing

$$b \sim \sum b_i \,. \tag{5.2.5}$$

The symbol, b, is not unique, however, if  $b \sim \sum b_i$  and  $b' \sim \sum b_i$ , b - b' is in the intersection,  $\bigcap S^{\ell}$ ,  $-\infty < \ell < \infty$ .

#### 4.5.3 Pseudodifferential operators

Given  $a \in \mathcal{S}^m$  let

$$T_a^0: S \to \mathcal{C}^\infty(T^n)$$

be the operator

$$T_a^0 g = \sum a(x,k)g(k)e^{ikx}.$$

Since

$$|D^{\alpha}a(x,k)e^{ikx}| \le C_{\alpha}\langle k\rangle^{m+\langle \alpha\rangle}$$

and

$$|g(k)| \le C_{\alpha} \langle k \rangle^{-(m+n+|\alpha|+1)}$$

this operator is well-defined, i.e., the right hand side is in  $\mathcal{C}^{\infty}(T^n)$ . Composing  $T_a^0$  with F we get an operator

$$T_a: \mathcal{C}^{\infty}(T^n) \to \mathcal{C}^{\infty}(T^n)$$
.

We call  $T_a$  the pseudodifferential operator with symbol a.

Note that

$$T_a e^{ikx} = a(x,k)e^{ikx}$$
.

Also note that if

$$P = \sum_{|\alpha| \le m} a_{\alpha}(x) D^{\alpha} \tag{5.3.1}$$

and

$$p(x,\xi) = \sum_{|\alpha| \le m} a_{\alpha}(x)\xi^{\alpha}. \tag{5.3.2}$$

Then

$$P = T_p$$
.

#### 4.5.4 The composition formula

Let P be the differential operator (5.3.1). If a is in  $S^r$  we will show that  $PT_a$  is a pseudodifferential operator of order m+r. In fact we will show that

$$PT_a = T_{p \circ a} \tag{5.4.1}$$

where

$$p \circ a(x,\xi) = \sum_{|\alpha| \le m} \frac{1}{\beta!} \partial_{\xi}^{\beta} p(x,\xi) D_x^{\beta} a(x,\xi)$$
 (5.4.2)

and  $p(x, \xi)$  is the function (5.3.2).

*Proof.* By definition

$$PT_a e^{ikx} = Pa(x,k)e^{ikx}$$
$$= e^{ikx}(e^{-ikx}Pe^{ikx})a(x,k).$$

Thus  $PT_a$  is the pseudodifferential operator with symbol

$$e^{-ix\xi}Pe^{ix\xi}a(x,\xi). \tag{5.4.3}$$

However, by (5.3.1):

$$e^{-ix\xi}Pe^{ix\xi}u(x) = \sum a_{\alpha}(x)e^{-ix\xi}D^{\alpha}e^{ix\xi}u(x)$$
$$= \sum a_{\alpha}(x)(D+\xi)^{\alpha}u(x)$$
$$= P(x,D+\xi)u(x).$$

Moreover,

$$p(x, \eta + \xi) = \sum \frac{1}{\beta!} \frac{\partial}{\partial \xi^{\beta}} p(x, \xi) \eta^{\beta},$$

so

$$p(x,D+\xi)u(x) = \sum \frac{1}{\beta!} \frac{\partial}{\partial \xi^{\beta}} p(x,\xi) D^{\beta} u(x)$$

and if we plug in  $a(x,\xi)$  for u(x) we get, by (5.4.3), the formula (5.4.2) for the symbol of  $PT_a$ .

#### 4.5.5 The inversion formula

Suppose now that the operator (5.3.1) is elliptic. We will prove below the following inversion theorem.

**Theorem.** There exists an  $a \in \mathcal{S}^{-m}$  and an  $r \in \bigcap S^{\ell}$ ,  $-\infty < \ell < \infty$ , such that

$$PT_a = I - T_r$$
.

Proof. Let

$$p_m(x,\xi) = \sum_{|\alpha|=m} a_{\alpha}(x)\xi^{\alpha}.$$

By ellipticity  $p_m(x,\xi) \neq 0$  for  $\xi \notin 0$ . Let  $\rho \in \mathcal{C}^{\infty}(\mathbb{R})$  be a function satisfying  $\rho(t) = 0$  for t < 1 and  $\rho(t) = 1$  for t > 2. Then the function

$$a_0(x,\xi) = \rho(|\xi|) \frac{1}{p_m(x,\xi)}$$
(5.5.1)

is well-defined and belongs to  $S^{-m}$ . To prove the theorem we must prove that there exist symbols  $a \in S^{-m}$  and  $r \in \bigcap S^{\ell}$ ,  $-\infty < \ell < \infty$ , such that

$$p \circ q = 1 - r$$
.

We will deduce this from the following two lemmas.

**Lemma.** If  $b \in S^i$  then

$$b - p \circ a_0 b$$

is in  $S^{i-1}$ .

*Proof.* Let  $q = p - p_m$ . Then  $q \in \mathcal{S}^{m-1}$  so  $q \circ a_0 b$  is in  $\mathcal{S}^{i-1}$  and by (5.4.2)

$$p \circ a_0 b = p_m \circ a_0 b + q \circ a_0 b$$
$$= p_m a_0 b + \dots = b + \dots$$

where the dots are terms of order i-1.

**Lemma.** There exists a sequence of symbols  $a_i \in \mathcal{S}^{-m-i}$ , i = 0, 1, ..., and a sequence of symbols  $r_i \in \mathcal{S}^{-i}$ , i = 0, ..., such that  $a_0$  is the symbol (5.5.1),  $r_0 = 1$  and

$$p \circ a_i = r_i - r_{i+1}$$

for all i.

Proof. Given  $a_0, \ldots, a_{i-1}$  and  $r_0, \ldots r_i$ , let  $a_i = r_i a_0$  and  $r_{i+1} = r_i - p \circ a_i$ . By Lemma 4.5.5,  $r_{i+1} \in \mathcal{S}^{-i-1}$ 

Now let  $a \in \mathcal{S}^{-m}$  be the "asymptotic sum" of the  $a_i$ 's

$$a \sim \sum a_i$$
.

Then

$$p \circ a \sim \sum p \circ a_i = \sum_{i=1}^{\infty} r_i - r_{i-1} = r_0 = 1,$$

so  $1 - p \circ a \sim 0$ , i.e.,  $r = 1 - p \circ q$  is in  $\bigcap S^{\ell}$ ,  $-\infty < \ell < \infty$ .

#### 4.5.6 Smoothing properties of $\Psi DO$ 's

Let  $a \in \mathcal{S}^{\ell}$ ,  $\ell < -m - n$ . We will prove in this section that the sum

$$K_a(x,y) = \sum a(x,k)e^{ik(x-y)}$$
 (5.6.1)

is in  $C^m(T^{\beta} \times T^n)$  and that  $T_a$  is the integral operator associated with  $K_a$ , i.e.,

$$T_a u(x) = \int K_a(x, y) u(y) dy$$
.

*Proof.* For  $|\alpha| + |\beta| \le m$ 

$$D_x^{\alpha} D_y^{\beta} a(x,k) e^{ik(x-y)}$$

is bounded by  $\langle k \rangle^{\ell+|\alpha|+|\beta|}$  and hence by  $\langle k \rangle^{\ell+m}$ . But  $\ell+m<-n$ , so the sum

$$\sum D_x^{\alpha} D_y^{\beta} a(x,k) e^{ik(x-y)}$$

converges absolutely. Now notice that

$$\int K_a(x,y)e^{iky} dy = a(x,k)e^{ikx} = T_\alpha e^{ikx}.$$

Hence  $T_a$  is the integral operators defined by  $K_a$ . Let

$$S^{-\infty} = \bigcap S^{\ell}, \quad -\infty < \ell \infty. \tag{5.6.2}$$

If a is in  $S^{-\infty}$ , then by (5.6.1),  $T_a$  is a smoothing operator.

#### 4.5.7 Pseudolocality

We will prove in this section that if f and g are  $\mathcal{C}^{\infty}$  functions on  $T^n$  with non-overlapping supports and a is in  $\mathcal{S}^m$ , then the operator

$$u \in \mathcal{C}^{\infty}(T^n) \to fT_a gu$$
 (5.7.1)

is a smoothing operator. (This property of pseudodifferential operators is called *pseudolocality*.) We will first prove:

**Lemma.** If  $a(x,\xi)$  is in  $S^m$  and  $w \in \mathbb{R}^n$ , the function,

$$a_w(x,\xi) = a(x,\xi+w) - a(x,\xi)$$
 (5.7.2)

is in  $S^{m-1}$ .

*Proof.* Recall that  $a \in \mathcal{S}^m$  if and only if

$$|D_x^{\alpha} D_{\xi}^{\beta} a(x,\xi)| \le C_{\alpha,\beta} \langle \xi \rangle^{m-|\beta|}.$$

From this estimate is is clear that if a is in  $\mathcal{S}^m$ ,  $a(x,\xi+w)$  is in  $\mathcal{S}^m$  and  $\frac{\partial a}{\partial \xi_i}(x,\xi)$  is in  $\mathcal{S}^{m-1}$ , and hence that the integral

$$a_w(x,\xi) = \int_0^1 \sum_i \frac{\partial a}{\partial \xi_i}(x,\xi + tw) dt$$

in  $S^{m-1}$ .

Now let  $\ell$  be a large positive integer and let a be in  $S^m$ ,  $m < -n - \ell$ . Then

$$K_a(x,y) = \sum a(x,k)e^{ik(x-y)}$$

is in  $C^{\ell}(T^n \times T^n)$ , and  $T_a$  is the integral operator defined by  $K_a$ . Now notice that for  $w \in \mathbb{Z}^n$ 

$$(e^{-i(x-y)w} - 1)K_a(x,y) = \sum a_w(x,k)e^{ik(x-y)}, \qquad (5.7.3)$$

so by the lemma the left hand side of (5.7.3) is in  $C^{\ell+1}(T^n \times T^n)$ . More generally,

$$(e^{-i(x-y)w} - 1)^N K_{\sigma}(x,y) \tag{5.7.4}$$

is in  $C^{\ell+N}(T^n \times T^n)$ . In particular, if  $x \neq y$ , then for some  $1 \leq i \leq n$ ,  $x_i - y_i \not\equiv 0 \mod 2\pi Z$ , so if

$$w = (0, 0, \dots, 1, 0, \dots, 0),$$

(a "1" in the i<sup>th</sup>-slot),  $e^{i(x-y)w} \neq 1$  and, by (5.7.4),  $K_a(x,y)$  is  $C^{\ell+N}$  is a neighborhood of (x,y). Since N can be arbitrarily large we conclude

**Lemma.**  $K_a(x,y)$  is a  $\mathcal{C}^{\infty}$  function on the complement of the diagonal in  $T^n \times T^n$ .

Thus if f and g are  $\mathcal{C}^{\infty}$  functions with non-overlapping support,  $fT_ag$  is the smoothing operator,  $T_K$ , where

$$K(x,y) = f(x)K_a(x,y)g(y)$$
. (5.7.5)

We have proved that  $T_a$  is pseudolocal if  $a \in \mathcal{S}^m$ ,  $m < -n - \ell$ ,  $\ell$  a large positive integer. To get rid of this assumption let  $\langle D \rangle^N$  be the operator with symbol  $\langle \xi \rangle^N$ . If N is an even positive integer

$$\langle D \rangle^N = (\sum D_i^2 + I)^{\frac{N}{2}}$$

is a differential operator and hence is a local operator: if f and g have non-overlapping supports,  $f\langle D\rangle^N g$  is identically zero. Now let  $a_N(x,\xi)=a(x,\xi)\langle \xi\rangle^{-N}$ . Since  $a_N\in\mathcal{S}^{m-N}$ ,  $T_{a_N}$  is pseudolocal for N large. But  $T_a=T_{a_N}\langle D\rangle^N$ , so  $T_a$  is the composition of an operator which is pseudolocal with an operator which is local, and therefore  $T_a$  itself is pseudolocal.

## 4.6 Elliptic operators on open subsets of $T^n$

Let U be an open subset of  $T^n$ . We will denote by  $\iota_U: U \to T^n$  the inclusion map and by  $\iota_U^*: \mathcal{C}^{\infty}(T^n) \to \mathcal{C}^{\infty}(U)$  the restriction map: let V be an open subset of  $T^n$  containing  $\overline{U}$  and

$$P = \sum_{|\alpha| \le m} a_{\alpha}(x) D^{\alpha} , \quad a_{\alpha}(x) \in \mathcal{C}^{\infty}(V)$$

an elliptic  $m^{\rm th}$  order differential operator. Let

$$P^t = \sum_{|\alpha| \le m} D^{\alpha} \overline{a}_{\alpha}(x)$$

be the transpose operator and

$$P_m(x,\xi) = \sum_{|\alpha|=m} a_{\alpha}(x)\xi^{\alpha}$$

the symbol at P. We will prove below the following localized version of the inversion formula of  $\S$  4.5.5.

**Theorem.** There exist symbols,  $a \in S^{-m}$  and  $r \in S^{-\infty}$  such that

$$P\iota_{II}^* T_a = \iota_{II}^* (I - T_r). \tag{4.6.1}$$

*Proof.* Let  $\gamma \in C_0^{\infty}(V)$  be a function which is bounded between 0 and 1 and is identically 1 in a neighborhood of  $\overline{U}$ . Let

$$Q = PP^{t}\gamma + (1 - \gamma)(\sum D_{\iota}^{2})^{n}.$$

This is a globally defined  $2m^{th}$  order differential operator in  $T^n$  with symbol,

$$\gamma(x)|P_m(x,\xi)|^2 + (1-\gamma(x))|\xi|^{2m} \tag{4.6.2}$$

and since (4.6.2) is non-vanishing on  $T^n \times (\mathbb{R}^n - 0)$ , this operator is elliptic. Hence, by Theorem 4.5.5, there exist symbols  $b \in \mathcal{S}^{-2m}$  and  $r \in \mathcal{S}^{-\infty}$  such that

$$QT_b = I - T_r$$

Let  $T_a = P^t \gamma T_b$ . Then since  $\gamma \equiv 1$  on a neighborhood of  $\overline{U}$ ,

$$\iota_U^*(I - T_r) = \iota_U^*QT_b$$

$$= \iota_U^*(PP^t\gamma T_b + (1 - \gamma)\sum D_i^2 T_b)$$

$$= \iota_U^*PP^t\gamma T_b$$

$$= P\iota_U^*P^t\gamma T_b = P\iota_U^*T_a.$$

## 4.7 Elliptic operators on compact manifolds

Let X be a compact n dimensional manifold and

$$P: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$$

an elliptic  $m^{\text{th}}$  order differential operator. We will show in this section how to construct a parametrix for P: an operator

$$Q: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$$

such that I - PQ is smoothing.

Let  $V_i$ ,  $i=1,\ldots,N$  be a covering of X by coordinate patches and let  $U_i$ ,  $i=1,\ldots,N$ ,  $\overline{U}_i\subset V_i$  be an open covering which refines this covering. We can, without loss of generality, assume that  $V_i$  is an open subset of the hypercube

$$\{x \in \mathbb{R}^n \mid 0 < x_i < 2\pi \quad i = 1, \dots, n\}$$

and hence an open subset of  $T^n$ . Let

$$\{\rho_i \in \mathcal{C}_0^{\infty}(U_i), \quad i = 1, \dots, N\}$$

be a partition of unity and let  $\gamma_i \in \mathcal{C}_0^{\infty}(U_i)$  be a function which is identically one on a neighborhood of the support of  $\rho_i$ . By Theorem 4.6, there exist symbols  $a_i \in \mathcal{S}^{-m}$  and  $r_i \in \mathcal{S}^{-\infty}$  such that on  $T^n$ :

$$P\iota_{U_i}^* T_{a_i} = \iota_{U_i}^* (I - T_{r_i}). \tag{4.7.1}$$

Moreover, by pseudolocality  $(1 - \gamma_i)T_{a_i}\rho_i$  is smoothing, so

$$\gamma_i T_{a_i} \rho_i - \iota_{U_i}^* T_{a_i} \rho_i$$

and

$$P\gamma_i T_{a_i} \rho_i - P\iota_{U_i}^* T_{a_i} \rho_i$$

are smoothing. But by (4.7.1)

$$P\iota_{U_i}^* T_{a_i} \rho_i - \rho_i I$$

is smoothing. Hence

$$P\gamma_i T_{a_i} \rho_i - \rho_i I \tag{4.7.2}$$

is smoothing as an operator on  $T^n$ . However,  $P\gamma_i T_{a_i}\rho_i$  and  $\rho_i I$  are globally defined as operators on X and hence (4.7.2) is a globally defined smoothing operator. Now let  $Q = \sum \gamma_i T_{a_i}\rho_i$  and note that by (4.7.2)

$$PQ - I$$

is a smoothing operator.

This concludes the proof of Theorem 4.3, and hence, modulo proving Theorem 4.3. This concludes the proof of our main result: Theorem 4.2. The proof of Theorem 4.3 will be outlined, as a series of exercises, in the next section.

## 4.8 The Fredholm theorem for smoothing operators

Let X be a compact n-dimensional manifold equipped with a smooth non-vanishing measure, dx. Given  $K \in \mathcal{C}^{\infty}(X \times X)$  let

$$T_K: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$$

be the smoothing operator 3.1.

**Exercise 1.** Let V be the volume of X (i.e., the integral of the constant function, 1, over X). Show that if

$$\max |K(x,y)| < \frac{\epsilon}{V}, \quad 0 < \epsilon < 1$$

then  $I - T_K$  is invertible and its inverse is of the form,  $I - T_L$ ,  $L \in \mathcal{C}^{\infty}(X \times X)$ .

Hint 1. Let  $K_i = K \circ \cdots \circ K$  (i products). Show that  $\sup |K_i(x,y)| < C\epsilon^i$  and conclude that the series

$$\sum K_i(x,y) \tag{4.8.1}$$

converges uniformly.

Hint 2. Let U and V be coordinate patches on X. Show that on  $U \times V$ 

$$D_x^{\alpha} D_y^{\beta} K_i(x, y) = K^{\alpha} \circ K_{i-2} \circ K^{\beta}(x, y)$$

where  $K^{\alpha}(x,z) = D_x^{\alpha}K(x,z)$  and  $K^{\beta}(z,y) = D_y^{\beta}K(z,y)$ . Conclude that not only does (8.1) converge on  $U \times V$  but so do its partial derivatives of all orders with respect to x and y.

Exercise 2. (finite rank operators.)  $T_K$  is a finite rank smoothing operator if K is of the form:

$$K(x,y) = \sum_{i=1}^{N} f_i(x)g_i(y).$$
 (4.8.2)

- (a) Show that if  $T_K$  is a finite rank smoothing operator and  $T_L$  is any smoothing operator,  $T_K T_L$  and  $T_L T_K$  are finite rank smoothing operators.
- (b) Show that if  $T_K$  is a finite rank smoothing operator, the operator,  $I T_K$ , has finite dimensional kernel and co-kernel.

Hint. Show that if f is in the kernel of this operator, it is in the linear span of the  $f_i$ 's and that f is in the image of this operator if

$$\int f(y)g_i(y)\,dy=0\,,\quad i=1,\ldots,N\,.$$

**Exercise 3.** Show that for every  $K \in \mathcal{C}^{\infty}(X \times X)$  and every  $\epsilon > 0$  there exists a function,  $K_1 \in \mathcal{C}^{\infty}(X \times X)$  of the form (4.8.2) such that

$$\sup |K - K_1|(x, y) < \epsilon.$$

Hint. Let  $\mathcal{A}$  be the set of all functions of the form (4.8.2). Show that  $\mathcal{A}$  is a *subalgebra* of  $C(X \times X)$  and that this subalgebra separates points. Now apply the Stone–Weierstrass theorem to conclude that  $\mathcal{A}$  is dense in  $C(X \times X)$ .

**Exercise** 4. Prove that if  $T_K$  is a smoothing operator the operator

$$I - T_K : \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$$

has finite dimensional kernel and co-kernel.

Hint. Show that  $K = K_1 + K_2$  where  $K_1$  is of the form (4.8.2) and  $K_2$  satisfies the hypotheses of exercise 1. Let  $I - T_L$  be the inverse of  $I - T_{K_2}$ . Show that the operators

$$(I - T_K) \circ (I - T_L)$$
$$(I - T_L) \circ (I - T_K)$$

are both of the form: identity minus a finite rank smoothing operator. Conclude that  $I-T_K$  has finite dimensional kernel and co-kernel.

Exercise 5. Prove Theorem 4.3.

## Chapter 5

# Hodge Theory

## Lecture 19

(First see notes on Elliptic operators)

Let X be a compact manifold. We will show that Section 7 of the notes on Elliptic operators works for elliptic operators on vector bundles.

We'll be working with the basic vector bundles  $TX \otimes \mathbb{C}$ ,  $T^*X \otimes \mathbb{C}$ ,  $\Lambda^1(T^*X) \otimes \mathbb{C}$  etc. Let review the basic facts about vector bundle theory.  $E \to X$  is a rank k (complex) vector bundle then given U open in X we define  $E_U = E \mid_U$ . Given  $p \in U$  there exists an open set  $U \ni p$  and a vector bundle isomorphism such that

**Notation.**  $C^{\infty}(E)$  denotes the  $C^{\infty}$  sections of E.

Suppose we have  $E^i \to X$ , i = 1, 2 vector bundles of rank  $k_i$  and suppose we have an operator P:  $C^{\infty}(E^1) \to C^{\infty}(E^2)$ .

#### **Definition.** P is an mth order differential operator if

- (a) P is local. That is for every open set  $U \subseteq X$  there exists a linear operator  $P_U: C^{\infty}(E_U^1) \to C^{\infty}(E_U^2)$ such that  $i_U^*P = P_U i_U^*$ .
- (b) If  $\gamma_U^i$ , i=1,2 are local trivializations of the vector bundle  $E^i$  over U then the operator  $P_U^{\sharp}$  in the diagram below is an mth order differential operator

$$C^{\infty}(E_{U}^{1}) \xrightarrow{P_{U}} C^{\infty}(E_{U}^{2})$$

$$\gamma_{U}^{1} \downarrow \cong \qquad \cong \downarrow \gamma_{U}^{2}$$

$$C^{\infty}(U, \mathbb{C}^{k_{1}}) \xrightarrow{P_{U}^{\sharp}} C^{\infty}(U, \mathbb{C}^{k_{2}})$$

Check: This is independent of choices of trivializations.

Let  $p \in U$ . From  $\gamma_U^i$ , i = 1, 2 we get a diagram (with  $\xi \in T_p^*$ )

$$E_p^1 \xrightarrow{\sigma_{\xi}} E_p^2 \qquad \sigma_{\xi}^{\sharp} = \sigma(P_U^{\sharp})(p, \xi)$$

$$\cong \bigvee_{\sigma_{\xi}^{k_1}} \xrightarrow{\sigma_{\xi}^{\sharp}} \mathbb{C}^{k_2}$$

**Definition.**  $\sigma_{\xi} = \sigma(P)(p, \xi)$ 

Check that this is independent of trivialization.  $f \in C^{\infty}(U), s \in C^{\infty}(E_U)$ . Then

$$(e^{-itf}Pe^{itf})(p) = t^m \sigma(P)(p,\xi)s(p) + O(t^{m-1})$$

where  $\xi = df_p$ .

**Definition.** P is elliptic if  $k_1 = k_2$  and for every p and  $\xi \neq 0$  in  $T_pX$ , then  $\sigma(P)(p,\xi) : E_p^1 \to E_p^2$  is bijective.

#### 5.0.1 Smoothing Operators on Vector Bundles

We have bundles  $E^i \to X$ . Form a bundle  $\text{Hom}(E^1, E^2) \to X \times X$  by defining that at (x, y) the fiber of this bundle is  $\text{Hom}(E_x^1, E_y^2)$ . In addition lets let dx be the volume form on X.

Let  $K \in C^{\infty}(Hom(E^1, E^2))$  and define  $T_K : C^{\infty}(E^1) \to C^{\infty}(E^2)$ , with  $f \in C^{\infty}(E^1)$  by

$$T_K f(y) = \int K(x, y) f(x) dx$$

What does this mean? By definition  $f(x) \in E_x^1$  and  $K(x,y) : E_x^1 \to E_y^2$ , so  $(K(x,y)f(x)) \in E_y^2$ . Thus it makes perfect sense to do the integration in the definition.

**Theorem.**  $P: C^{\infty}(E^1) \to C^{\infty}(E^2)$  is an mth order elliptic differential operator, then there exists an "mth order  $\Psi DO$ ",  $Q: C^{\infty}(E^2) \to C^{\infty}(E^1)$  such that

$$PQ-I$$

is smoothing.

*Proof.* Just as proof outlined in notes with  $U_i, \rho_i, \gamma_i$ . But make sure that  $E^1, E^2$  are locally trivial over  $U_i$ , i.e. on  $U_i, P_{U_i} \cong P_{U_i}^{\sharp}$ , so  $P_{U_i}^{\sharp}$  is an elliptic system.

#### 5.0.2 Fredholm Theory in the Vector Bundle Setting

Let  $E \to X$  be a complex vector bundle. Then a hermitian inner product on E is a smooth function  $X \ni p \to (,)_p$  where  $(,)_p$  is a Hermitian inner product on  $E_p$ .

If X is compact with  $s_1, s_2 \in C^{\infty}(E)$  then we can make this into a compact pre-Hilbert space by defining an  $L^2$  inner product

$$\langle s_1, s_2 \rangle = \int (s_1(x), s_2(x)) dx$$

**Lemma.** Given  $p \in X$ , there exists a neighborhood U of p and a Hermitian trivialization of  $E_U$ 

for  $p \in U$ ,  $E_p \cong \mathbb{C}^k$  and  $\gamma_U$  hermitian if  $E_p \cong \mathbb{C}^k$  is an isomorphism of hermitian vector spaces.

*Proof.* This is just Graham-Schmidt

**Theorem.**  $E^i \to X$ , i = 1, 2 Hermitian vector bundles and  $P: C^{\infty}(E^1) \to C^{\infty}(E^2)$  an mth order DO, then there exists a unique mth order DO,  $P^t: C^{\infty}(E^2) \to C^{\infty}(E^1)$  such that for  $f \in C^{\infty}(E^1)$ ,  $g \in C^{\infty}(E^2)$ 

$$\langle Pf, g \rangle_{L^2} = \langle f, P^t g \rangle_{L^2}$$

Proof. (Using the usual mantra: local existence, local uniqueness implies global existence global uniqueness). So we'll first prove local existence. Let U be open and  $\gamma_U^1$ ,  $\gamma_U^2$  hermitian trivialization of  $E_U^1$ ,  $E_U^2$ .  $P \leftrightsquigarrow P_U^\sharp$ ,  $P_U^\sharp : C^\infty(U, \mathbb{C}^{k_1}) \to C^\infty(U, \mathbb{C}^{k_2})$ . Then  $P_U^\sharp = [P_{ij}], \ P_{ij} : C^\infty(U) \to C^\infty(U), \ 1 \le i \le k_2, \ 1 \le j \le k_1$ . Set  $(P_U^t)^\sharp = [P_{ji}^t], \ (P_U^t)^\sharp \leadsto P_U^t$ . Then  $P_U^t : C^\infty(E_U^2) \to C^\infty(E_U^1)$ .

We leave the read to check that if  $f \in C_0^{\infty}(E_U^1)$ ,  $g \in C_0^{\infty}(E_U^2)$  then

$$\langle P_U f, g \rangle = \langle f, P_U^t g \rangle$$

This is local existence. Local uniqueness is trivial. This all implies global existence.

**Theorem (Main Theorem).** X compact,  $E^i \to X$ , i=1,2 hermitian bundles of rank k. And  $P: C^{\infty}(E^1) \to C^{\infty}(E^2)$  an m order elliptic DO then

- (a) ker P is finite dimensional
- (b)  $f \in \text{Im } P \text{ if and only if } \langle f, g \rangle = 0 \text{ for all } g \in \ker P^t.$

*Proof.* The proof is implied by existence of right inverses for P modulo smoothing and the Fredholm Theorem for I-T when  $T:C^{\infty}(E^1)\to C^{\infty}(E^2)$ .

### Lecture 20

X a compact manifold,  $E^k \to X$ ,  $k=1,\ldots,N$  complex vector bundles,  $D: C^\infty(E^k) \to C^\infty(E^{k+1})$  first order differential operator. Consider the following complex, hereafter referred to as (\*).

$$\cdots \longrightarrow C^{\infty}(E^k) \xrightarrow{D} C^{\infty}(E^{k+1}) \xrightarrow{D} \cdots$$

(\*) is a differential complex if  $D^2 = DD = 0$ .

For  $x \in X$ ,  $\xi \in T_x^*$ , we have  $\sigma_{\xi} : E_x^k \to E_x^{k+1}$  then we have the symbol  $\sigma_{\xi}(D)(x,\xi)$ . And

$$0 = \sigma(D^2)(x,\xi) = \sigma(D)(x,\xi)\sigma(D)(x,\xi)$$

so we conclude that  $\sigma_{\xi}^2 = 0$ . So at every point we get a finite dimensional complex

$$0 \longrightarrow E_x^1 \xrightarrow{\sigma_{\xi}} E_x^2 \xrightarrow{\sigma_{\xi}} \cdots$$

the symbol complex

**Definition.** (\*) is elliptic if the symbol complex is exact for all x and  $\xi \in T_x^* - \{0\}$ .

#### Examples

(a) The De Rham complex. For this complex the bundle is

$$E^k: \Lambda^k \otimes \mathbb{C} = \Lambda^k(T^*X) \otimes \mathbb{C}$$

then  $C^{\infty}(E^k) = \Omega^k(X)$ . The first order operation is the usual exterior derivative  $d: C^{\infty}(E^k) \to C^{\infty}(E^{k+1})$ .  $\sigma_{\xi} = \sigma(d)(x,\xi)$ , where  $\sigma_{\xi}: \Lambda^k(T_x^*) \otimes \mathbb{C} \to \Lambda^{k+1}(T_x^*) \otimes \mathbb{C}$ 

**Theorem.** For  $\mu \in \Lambda^k(T_x^*) \otimes \mathbb{C}$ ,  $\sigma_{\xi}\mu = \sqrt{-1}\xi \wedge \mu$ .

Proof.  $\omega \in \Omega^k(X)$ ,  $\omega_x = \mu$ ,  $f \in C^{\infty}(X)$ ,  $df_x = \xi$  then

$$(e^{-itf}de^{ift}\omega)_x = (idf \wedge \omega)_x + (d\omega)_x = (i\xi_x \wedge \mu)t + (d\omega)_x$$

**Theorem.** The de Rham complex is elliptic

*Proof.* To do this we have to prove the exactness of the symbol complex:

$$\cdots \longrightarrow \Lambda^k(T_x^*) \xrightarrow{\text{``} \wedge \xi^{\text{"}}} \Lambda^{k+1}(T_x^*) \xrightarrow{\text{``} \wedge \xi^{\text{"}}} \cdots$$

To do this let  $e_1, \ldots, e_n$  be a basis of  $T_x^*$  with  $e_1 = \xi$ . Then for  $\mu \in \Lambda^k(T_x^*)$ ,  $\mu = e_1 \wedge \alpha + \beta$  where  $\alpha$  and  $\beta$  are products just involving  $e_2, \ldots, e_n$  (this is not hard to prove).

(b) Let X be complex and let us define a vector bundle

$$E^k = \Lambda^{0,k}(T^*) \qquad C^{\infty}(E^k) = \Omega^{0,k}(X)$$

Take  $D = \overline{\partial}$ . This is a first order DO,  $\overline{\partial}: C^{\infty}(E^k) \to C^{\infty}(E^{k+1})$ ,  $\sigma_x i = \sigma(D)(x, \xi)$ , now what is this symbol?

Take  $\xi \in T_x^*$ , then  $\xi = \xi^{1,0} + \xi^{0,1}$  where  $\xi^{1,0} \in (T^a s t_x)^{1,0}, \xi^{0,1} \in (T_x^*)^{0,1}$  and  $\xi^{1,0} = \overline{\xi}^{0,1}, \xi \neq 0$  then  $\xi^{0,1} \neq 0$ .

**Theorem.** For  $\mu \in \Lambda^{0,ki}(T_x^*)$ ,  $\sigma_{\xi}(\mu) = \sqrt{-1}\xi^{0,1} \wedge \mu$ .

Proof.  $\omega \in \Omega^{0,k}(X)$ ,  $\omega_x = \mu$ ,  $f \in C^{\infty}(X)$ ,  $df_x = \xi$  then

$$(e^{-itf}\overline{\partial}e^{itf}\omega)_x = (it\overline{\partial}f\wedge\omega)_x t + (\overline{\partial}\omega)_x = it\xi^{0,1}\wedge\mu + \overline{\partial}\omega_x$$

Check: For  $\xi \neq 0$  the sequence

$$\cdots \longrightarrow \Lambda^{0,k}(T_x^*) \xrightarrow{\text{``} \wedge \xi^{0,1}} \Lambda^{0,k+1}(T_x^*)^{\xi^{0,1}} \longrightarrow \cdots$$

is exact. This is basically the same as the earlier proof, when we note that  $\Lambda^{0,k}(T_x^*) = \Lambda^k((T_x^*)^{0,1})$ . we conclude that the Dolbeault complex is elliptic.

(c) The above argument forks for higher dimensional Dolbeault complexes. If we set

$$E^k = \Lambda^{p,k}(T^*X), \qquad D = \overline{\partial}, \qquad C^{\infty}(E^k) = \Omega^{p,k}(X)$$

it is easy to show that  $\sigma(\overline{\partial})(x,\xi) = " \wedge \xi^{0,1}"$ 

#### The Hodge Theorem

Given a general elliptic complex

$$\cdots \xrightarrow{\quad D \quad} C^{\infty}(E^k) \xrightarrow{\quad D \quad} C^{\infty}(E^{k+1}) \xrightarrow{\quad D \quad} \cdots$$

with dx a volume form on X, equip each vector bundle  $E^k$  with a Hermitian structure. We then get an  $L^2$  inner product  $\langle,\rangle_{L^2}$  on  $C^\infty(E^k)$ . And for each  $D:C^\infty(E^k)\to C^\infty(E^{k+1})$  we get a transpose operator

$$D^t: C^{\infty}(E^{k+1}) \to C^{\infty}(E^k)$$

If for  $x \in X$ ,  $\xi \in T_x^*$ ,  $\sigma_{\xi} = \sigma(D)(x, \xi)$  then

$$\sigma(D^t)(x,\xi) = \sigma_x^t$$

So we can get a complex in the other direction, call it  $(*)^t$ 

$$\cdots \xrightarrow{D^t} C^{\infty}(E^k) \xrightarrow{D^t} C^{\infty}(E^{k-1}) \xrightarrow{D^t} \cdots$$

and since  $0 = (D^r)^t = (DD)^t = D^tD^t = (D^t)^2$  we have that  $(*)^t$  is a differential complex. Also,  $\sigma(D^t)(x,\xi) = \sigma_{\xi} = \sigma(D)(x,\xi)^t$ . For x and  $\xi \in T_x^* - \{0\}$  the symbol complex of  $D^t$  is

$$0 \longrightarrow E_x^N \xrightarrow{\sigma_\xi^t} E_x^{N-1} \xrightarrow{\sigma_\xi^t} \cdots$$

The transpose of the symbol complex for D. So (\*) elliptic implies that  $(*)^t$  is elliptic.

**Definition.** The harmonic space for (\*) is

$$\mathcal{H}^k = \{ s \in C^{\infty}(E^k), Ds = D^t s = 0 \}$$

Theorem (Hodge Decomposition Theorem). We have two propositions

- (a) For all k,  $\mathcal{H}^k$  is finite dimensional.
- (b) Every element u of  $C^{\infty}(E^k)$  can be written uniquely as a sum  $u_1 + u_2 + u_3$  where  $u_1 \in \text{Im}(D)$ ,  $u_2 \in \text{Im}(D^t)$ ,  $u_3 \in \mathcal{H}^k$

Before we prove this we'll do a little preliminary work. Let

$$E = \bigoplus_{k=1}^{N} E^k$$

Then consider the operator

$$D + D^t : C^{\infty}(E) \to C^{\infty}(E)$$

**Check**: This is elliptic.

*Proof.* Consider  $Q = (D + D^t)^2$ . It suffices to show that Q is elliptic.

$$Q = D^2 + DD^t + D^tD + (D^t)^2$$

but the two end terms are 0. So

$$Q = DD^t + D^tD$$

Note that Q sends  $C^{\infty}(E^k)$  to  $C^{\infty}(E^k)$ , so Q behaves nicer than  $D+D^t$ . So now we want to show that Q is elliptic.

Let  $x, \xi \in T_x^* - \{0\}$ . Then

$$\sigma(Q)(x,\xi) = \sigma(DD^t)(x,\xi) + \sigma(D^tD)(x,\xi) = \sigma_x^t \xi_{\xi} + \sigma_{\xi} \sigma_{\xi}^t$$

(where  $\sigma_{\xi} = \sigma(D)(x, \xi)$ .

Suppose  $v \in E_x^k$  and  $\sigma(Q)(x,\xi)v = 0$  (i.e. it fails to be bijective). Then

$$((\sigma_{\xi}^t \sigma_{\xi} + \sigma_{\xi} \sigma_{\xi}^t)v, v) = 0 = (\sigma_{\xi} v, \sigma_{\xi} v)_x + (\sigma_{\xi}^t v, \sigma_{\xi}^t v) = 0$$

which implies that  $\sigma_{\xi}v = 0$  and  $\sigma_{\xi}^t v = 0$ . Now  $\sigma_{\xi} = 0$  implies that  $v \in \text{Im } \sigma_{\xi} : E_x^{k-1} \to E_x^k$  by exactness. We know that  $\text{Im } \sigma_{\xi} \perp \ker \sigma_{\xi}^t$ , but  $v \in \ker \sigma_{\xi}^t$ , so  $v \perp v$  implies that v = 0.

So Q is elliptic and thus 
$$(D + D^t)$$
 is elliptic.

**Lemma.**  $\mathcal{H}^k = \ker Q$ .

*Proof.* We want to show  $\mathcal{H}^k \subseteq \ker Q$ . The other direction is easy. Let  $u \in \ker Q$ . Then

$$\langle DD^t u + D^t Du, u \rangle = 0 = \langle D^t u, D^t u \rangle + \langle Du, Du \rangle = 0$$

This implies that  $D^t u = Du = 0$ , so  $u \in \mathcal{H}^k$ .

Proof of Hodge Decomposition. By the Fredholm theorem every element  $u \in C^{\infty}(E^k)$  is of the form  $u = v_1 + v_2$  where  $v_1 \in \operatorname{Im}(Q)$  and  $v_2 \in \ker Q$ .  $v_2 \in \ker Q$  implies that  $v_2 \in \mathcal{H}^k$ ,  $v_1 \in \operatorname{Im} Q$  implies that  $v_1 = Qw = D(D^tw) + D^t(Dw)$ . Choose  $u_1 = DD^tw$ ,  $u_2 = D^tDw$  and  $v_2 = u_3$ .

Left as an exercise: Check that  $u = u_1 + u_2 + u_3$  is unique. Hint:  $\ker D \perp \operatorname{Im} D^t$  and  $\ker D^t \perp \operatorname{Im} D$ . Then the space  $\operatorname{Im}(D)$ ,  $\operatorname{Im}(D^t)$  and  $\mathcal{H}$  are all mutually perpendicular.

#### Lecture 21

#### The Hodge \*-operator

Let  $V = V^n$  be an *n*-dimensional  $\mathbb{R}$ -vector space. Let  $B: V \times V \to \mathbb{R}$  be a non-degenerate bilinear form on V (Note that for the momentum we are not assuming anything about this form).

From B one gets a non-degenerate bilinear form  $B: \Lambda^k(V) \times \lambda^k(V) \to \mathbb{R}$ . If  $\alpha = v_1 \wedge \cdots \wedge v_k, \beta = w_1 \wedge \cdots \wedge w_k$  then

$$B(\alpha, \beta) = \det(B(v_i, v_i))$$

Alternate definition:

Define a pairing (non-degenerate and bilinear)  $\Lambda^k(V) \times \Lambda^k(V^*) \to \mathbb{R}$  with  $\alpha = v_1 \wedge \cdots \wedge v_k$ ,  $\beta = f_1 \wedge \cdots \wedge f_k$ ,  $v_i \in V$ ,  $f_i \in V^*$ . Then

$$\langle \alpha, \beta \rangle = d \langle v_i, f_i \rangle$$

This gives rise to the identification  $\Lambda^k(V^*) \cong \Lambda^k(V)^*$ .

So  $B: V \times V \to \mathbb{R}$  gives to  $L_B: V \xrightarrow{\cong} V^*$  by  $B(u,v) = \langle u, L_B v \rangle$ . This can be extended to a map of k-th exterior powers,  $L_B: \Lambda^k(V) \to \Lambda^k(V^*)$ , defined by

$$L_B(v_1 \wedge \cdots \wedge v_k) = L_B v_1 \wedge \cdots \wedge L_B v_k$$

and if we have  $\alpha, \beta \in \Lambda^k(V)$  then  $B(\alpha, \beta) = \langle \alpha, L_B \beta \rangle$ .

Let us now look at the top dimensional piece of the exterior algebra. dim  $\Lambda^n(V) = 1$ , orient V so that we are dealing with  $\Lambda^k(V)_+$ . Then there is a unique  $\Omega \in \Lambda^n(V)$  such that  $B(\Omega, \Omega) = 1$ .

**Theorem.** There exists a bijective map  $*: \Lambda^k(V) \to \Lambda^{n-k}(V)$  such that for  $\alpha, \beta \in \Lambda^k(V)$  we have

$$\alpha \wedge *\beta = B(\alpha, \beta)\Omega$$

*Proof.* From  $\Omega$  we get a map  $\Lambda^n(V) \xrightarrow{\cong} \mathbb{R}$ ,  $\lambda \Omega \mapsto \lambda$ . So we get a non-degenerate pairing

$$\Lambda^k(V) \times \Lambda^k(V) \to \Lambda^n(V) \to \mathbb{R}$$

Now we have a mapping  $\Lambda^k(V^*) \xrightarrow{k} \Lambda^{n-k}(V)$ . Define the \*-operator to be  $k \circ L_B$ .

There is a clear dependence of \* on the orientation of V. If we exchange  $\Omega$  for  $-\Omega$  then \* turns to -\*. Lets say something about the dependence on B.

Suppose we have  $B_1$ , another non-degenerate bilinear form on V. Then there exists a unique  $J:V \xrightarrow{cong} V$  so that  $B_1(u,v)=B(u,Jv)$ . In fact we define J by requiring that  $L_{B_1}:V\to V^*$  is given by setting  $L_{B_1}=L_B\circ J$ .

Extend J to a map  $J: \Lambda^k(V) \to \Lambda^k(V)$  by setting  $J(v_1 \wedge \cdots \wedge v_k) = Jv_1 \wedge \cdots \wedge Jv_k$ . Then on  $\Lambda^k(V)$ ,  $L_{B_1} = L_B \circ J$ ,  $*_1 = k \circ L_{B_1} = k \circ L_B \circ J = *_0 \circ J$ . So the star operator for  $B_1$  and B are relation b  $*_1 = *_0 \circ J$ .

#### Multiplicative Properties of \*

There are actually almost no multiplicative properties of the \*-operator, but there are a few things to be said.

Suppose we have a vector space  $V^n = V_1^{n_1} \oplus V_2^{n_2}$  and suppose we have the bilinear form  $B = B_1 \oplus B_2$ . From this decomposition we can split the exterior powers

$$\Lambda^k(V) = \bigoplus_{r+s=k} \Lambda^r(V_1) \otimes \Lambda^s(V_2)$$

If  $\alpha_1, \beta_1 \in \Lambda^r(V_1)$  and  $\alpha_2, \beta_2 \in \Lambda^r(V_2)$  then

$$B(\alpha_1 \wedge \alpha_2, \beta_1 \wedge \beta_2) = B_1(\alpha_1, \beta_1)B_2(\alpha_2, \beta_2)$$

**Theorem.** With  $\beta_1 \in \Lambda^r(V_1)$  and  $\beta_2 \in \Lambda^s(V_2)$  we have

$$*(\beta_1 \wedge \beta_2) = (-1)^{(n_1 - r)s} *_1 \beta_1 \wedge *_2 \beta_2$$

*Proof.*  $\alpha_1 \in \Lambda^r(V_1)$ ,  $\alpha_2 \in \Lambda^s(V_2)$  with  $\Omega_1, \Omega_2$  the volume forms on the vector spaces. Then let  $\Omega = \Omega_1 \wedge \Omega_2$  be the volume form for  $\Lambda^n(V)$ . Then

$$(\alpha_1 \wedge \alpha_2) * (\beta_1 \wedge \beta_2) = B(\alpha_1 \wedge \alpha_2, \beta_1 \wedge \beta_2) \Omega = B_1(\alpha_1, \beta_1) \Omega_1 \wedge B(\alpha_2, \beta_2) \Omega_2$$
$$= (\alpha_1 \wedge *_1\beta_1) \wedge (\alpha_2 \wedge *_2\beta_2)$$
$$= (-1)^{(n_1 - r)s} \alpha_1 \wedge \alpha_2 \wedge (*_1\beta_1 \wedge *_2\beta_2)$$

## Lecture 22

Again,  $V = V^n$  and  $B: V \times V \to \mathbb{R}$  a non-degenerate bilinear form. A few properties of \* we have not mentioned yet:

$$*1 = \Omega$$
  $*\Omega = 1$ 

#### Computing the \*-operator

We now present a couple of applications to computation

(a) B symmetric and positive definite. Let  $v_1, \ldots, v_n$  be an oriented orthonormal basis of V. If  $I = (i_1, \ldots, i_k)$  where  $i_1 < \cdots < i_k$  then  $v_I = v_{i_1} \wedge \cdots \wedge v_{i_k}$ . Let  $J = I^C$ . Then

$$*v_I = \pm v_J$$

where this is postive if  $v_I \wedge v_J = \Omega$  and negative if  $v_I \wedge v_J = -\Omega$ .

(b) Let B be symplectic and  $V = V^{2n}$ . Then there is a Darboux basis  $e_1, f_1, \ldots, e_n, f_n$ . Give V the symplectic orientation

$$\Omega = e_1 \wedge f_1 \wedge \cdots \wedge e_n f_n$$

What does the \*-operator look like? For n=1, i.e.  $V=V^2$  we have  $*1=e \wedge f, *(e \wedge f)=1 *e=e$  and \*f=f.

What about n arbitrary? Suppose we have

$$V = V_1 \oplus \cdots \oplus V_n$$
  $V_i = span\{e_i, f_i\}$ 

then  $\Lambda(V)$  is spanned by  $\beta_1 \wedge \cdots \wedge \beta_n$  where  $\beta_i \in \Lambda^{p_i}(V_i), 0 \leq p_i \leq 2$ . Then

$$*(\beta_1 \wedge \cdots \wedge \beta_n) = *_n \beta_n \wedge \cdots \wedge *_1 \beta_1$$

and we already know that \* operator on 2 dimensional space.

#### Other Operations

For  $u \in V$  we can define an operation  $L_u : \Lambda^k \to \Lambda^{k+1}$  by  $\alpha \mapsto u \wedge \alpha$ . We can also define this operations dual: for  $v^* \in V^*$ ,  $i_{v^*} : \Lambda^k \to \Lambda^{k-1}$  the usual interior product. But because we have a bilinear form we can find  $L^t_u$  and  $i^t_{v^*}$  and since we have \* we have other interesting

things to do, like conjugate with the \*-operator:

$$*^{-1}L_u * *^{-1}(i_{v^*})*$$

**Theorem.** For  $\alpha \in \Lambda^{p-1}$ ,  $\beta \in \Lambda^p$ 

$$B(L_u\alpha,\beta) = B(\alpha, L_u^t\beta)$$

where  $L_u^t = (-1)^{p-1} *^{-1} L_u * := \widetilde{L}_u$ .

*Proof.* Begin by noting  $L_u \alpha \wedge *\beta = B(L_u \alpha, \beta)\Omega$ . Now

$$u \wedge \alpha \wedge *\beta = (-1)^{p-1} \alpha \wedge u \wedge *\beta = (-1)^p \alpha \wedge *(*^{-1}u \wedge *\beta)$$
$$= \alpha \wedge *\widetilde{L}_u \beta = B(\alpha, \widetilde{L}_u \beta)\Omega$$

which implies that  $\widetilde{L}_u = L_u^t$ .

What is this transpose really doing? We know we have a bilinear form B that gives rise to an map  $L_u: V \to V^*$ . Since B is not symmetric, define  $B^{\sharp}(u,v) = B(v,u)$ , and we get a new map  $L_{B^{\sharp}}: V \to V^*$ . Then:

**Theorem.** If  $v^* = L_{B\sharp}u$ , then  $L_u^t = i_{v^*}$ .

*Proof.* Let  $u_1, \ldots, u_n$  be a basis of V and let  $v_1, \ldots, v_n$  be a complementary basis of V determined by

$$B(u_i, v_j) = \delta_{ij}$$

and let  $v_1^*, \ldots, v_n^*$  be a dual basis of  $V^*$ . Check that  $v_1^* = L_{B^\sharp} u_1$ . Let  $I = (i_1, \ldots, i_{k-1})$  and  $J = (j_1, \ldots, j_k)$  be multi-indices. We claim that

$$B(L_{u_1}u_I, v_J) = B(u_I, i_{v_*^*}v_J)$$

and that if  $j_1, \ldots, j_k = 1$  and  $i_1, \ldots, i_{k-1} = 1$  then both sides are 1. Otherwise they are 0. 

**Theorem.** On  $\Lambda^{p+1}$ ,  $(i_{v^*})^t = (-1)^p *^{-1} (i_{v^*})^*$  and  $v^* = L_B u$ .

#### Lecture 23

For the next few days we're assuming that B is symplectic and  $V = V^{2n}$ . Choose a Darboux basis  $e_1, f_1, \ldots, e_n, f_n$ . Check that  $L_B: V \to V^*$  is the map

$$\{e_i \rightarrow -f_i^*, f_i \rightarrow e_i^*\}$$

where  $e_i^*, f_i^*$  are the dual vectors. In the symplectic case  $B^{\sharp} = -B$  and  $L_{B^{\sharp}} = -L$ . Say that  $\omega \in \Lambda^2 V$ ,

$$\omega = \sum e_i \wedge f_i$$

Then we have the operation  $L: \Lambda^p \to \Lambda^{p+2}$ , given by  $\alpha \mapsto \omega \wedge \alpha$  and also its transpose  $L^t: \Lambda^{p+2} \to \Lambda^p$ . Lets look at the commutator  $[L, L^t]: \Lambda^p \to \Lambda^p$ .

Theorem (Kaehler, Weil).  $[L, L^t] = (p - n) \operatorname{Id}$ 

*Proof.*  $L = \sum_{i} L_{e_i} L_{f_i}$ , so

$$L^{t} = \sum_{i} L_{f_{i}}^{t} L_{e_{i}}^{t} = \sum \iota_{f_{i}^{*}} \iota_{e_{i}^{*}}$$

Its easy to see that Kaehler-Weil holds when n=2. For n-dimensions

$$L = \sum_{i} L_i \qquad L_i = L_{e_i} L_{f_i} \qquad L^t = \sum_{i} L_i^t \qquad L_i^t = \iota_{f_i^*} \iota_{e_i^*}$$

 $V_i = span\{e_i, f_i\}, \text{ then } \Lambda^p = span\beta_1 \wedge \cdots \wedge \beta_n \text{ where } \beta_i \in \Lambda^{p_i}(V_i).$ 

$$L_i\beta_1 \wedge \cdots \wedge \beta_n = \beta_1 \wedge \cdots \wedge (L_i\beta_i) \wedge \cdots \wedge \beta_n$$

and

$$L_i^t(\beta_1 \wedge \cdots \wedge \beta_n) = \beta_1 \wedge \cdots \wedge (L_j \beta_j) \wedge \cdots \wedge \beta_n$$

If  $n \neq j$ , then  $L_i L_i^t = L_i^t L_i$ . So

$$[L, L^t]\beta_1 \wedge \dots \wedge \beta_n = \sum_i \beta_1 \wedge \dots \wedge [L_i, L_i^t]\beta_i \wedge \dots \wedge \beta_n$$
$$= \sum_i (p_i - 1)\beta_1 \wedge \dots \wedge \beta_n = (p - n)\beta_1 \wedge \dots \wedge \beta_n$$

### Lecture 24

Proposition.  $L^t = *^{-1}L*$ 

**Proposition.**  $u \in V$  then  $[L_u^t, L] = -L_u$ .

Proof. Proof omitted.

Let  $(X^{2n}, \omega)$  be a compact symplectic manifold. Let  $x \in X$  and  $V = T_x^*$ . Notice

- (a) From  $\omega_x$  we get a symplectic bilinear form on  $T_x$ .
- (b) From this form we get an identification  $T_x \to T_x^*$ .
- (c) Hence from 1,2 we get a symplectic bilinear from  $B_x$  on V.
- (d) From  $B_x$  we get a \*-operator

$$*_x: \Lambda^p(T_x^*) \to \Lambda^{2n-p}(T_x^*)$$

(e) This gives us a \*-operator on forms

$$*: \Omega^p(X) \to \Omega^{2n-p}(X)$$

We can define a symplectic version of the  $L^2$  inner product on  $\Omega^p$  as follows. Take  $\alpha, \beta \in \Omega^p$  and define

$$\langle \alpha, \beta \rangle = \int_X \alpha \wedge *\beta$$

(Note: This is not positive definite or anything, its just a pairing) Take  $\alpha \in \Omega^{p-1}$ ,  $\beta \in \Omega^p$ . Then look at

$$d(\alpha \wedge *\beta) = d\alpha \wedge *\beta + (-1)^{p-1}\alpha \wedge d * \beta$$
$$= d\alpha \wedge *\beta + (-1)^{p-1}\alpha \wedge *(*^{-1}d*)\beta$$

Since  $\int_X d(\alpha \wedge *\beta) = 0$ , we integrate both sides of the above and get

$$\int_{X} d\alpha \wedge *\beta = (-1)^{p} \int \alpha \wedge *(*^{-1}d*)\beta$$

If we introduce the notation  $\delta = (-1)^p *^{-1} d*$  on  $\Omega^p$  then

$$\langle d\alpha, \beta \rangle = \langle \alpha, \delta\beta \rangle$$

Now, given the mapping  $L: \Omega^p \to \Omega^{p+2}$ ,  $L\alpha = \omega \wedge \alpha$  we have the following theorem

Theorem.  $[\delta, L] = d$ .

This identity has no analogue in ordinary Hodge Theory. This is very important.

*Proof.*  $x \in X, \xi \in T_x^*$ , then  $\sigma(d)(x,\xi) = iL_{\xi}$ . On  $\Lambda^p$ ,  $\delta = (-1)^p *^{-1} d *$ , so  $\sigma(d)(x,\xi) = (-1)^p i *^{-1} L_{\xi} * = -iL_{\xi}^t$ . Then

$$\sigma([\delta, L]) = i[L_{\varepsilon}^t, L] = iL_{\varepsilon} = \sigma(d)(x, \xi)$$

so  $[\delta, L]$  and d have the same symbol.

Now,  $d [\delta, L]$  are first order DO's mapping  $\Omega^p \to \Omega^{p+1}$ , so  $d - [\delta, L] : \Omega^p \to \Omega^{p+1}$  is a first order DO. We want to show that this is 0.

Let  $(U, x_1, \ldots, x_n, y_1, \ldots, y_n)$  be a Darboux coordinate patch. Consider  $u = \beta_1 \wedge \cdots \wedge \beta_n$  where  $\beta_i = 1, dx_i, dy_i$  or  $dx_i \wedge dy_i$ .

These de Rham forms are a basis at each point of  $\Lambda(T_x^*)$ .

 $Lu = \omega \wedge u$  is again a form of this type since  $\omega = \sum dx_i \wedge dy_i$  is of this form. Also \*u is of this from.

Note that d=0 on a form of this type, hence  $\delta=*^{-1}d*$  is 0 on a form of this type. Thus  $[\delta,L]-d$  is 9 on a form of this type.

#### Lecture 25

#### Symplectic Hodge Theory

 $(X^{2n}, \omega)$  be a compact symplectic manifold. From  $x \in X$  we get  $\omega_x \to B_x$  a non-degenerate bilinear form on  $T_x^*$ , and so induces a non-degenerate bilinear from on  $\Lambda^p(T_x^*)$ .

Define  $\langle , \rangle_{L^2}$  on  $\Omega^p$  as follows. Take  $\Omega = \omega^n/n!$ , a symplectic volume form,  $\alpha, \beta \in \Omega^p$ 

$$\langle \alpha, \beta \rangle = \int_X B_x(\alpha, \beta) \Omega = \int_X \alpha \wedge *\beta$$

Remarks:

- (a) In symplectic geometry  $*^2 = id$ ,  $* = *^{-1}$ .
- (b)  $\langle , \rangle$  is anti-symmetric on  $\Omega^p$ , p odd and symmetric on  $\Omega^p$ , p even.
- (c)  $[L^t, \delta^t] = d^t = \delta$ . And  $\delta^t = (d^t)^t = -d$ , so  $[d, L^t] = \delta$ .

Consider the Laplace operator  $d\delta + \delta d = dd^t + d^t d$ . Now, in the symplectic world,  $\Delta = 0$ . We'll prove this:  $\delta = [d, L^t] = dL^t - L^t d$ , so  $d\delta = -dL^t d$  and  $\delta d = dL^t d$ , so  $\Delta = 0$ .

So for symplectic geometry we work with the bicomplex  $(\Omega, d, \delta)$ . We're going to use symplectic geometry to prove the Hard Lefshetz theorem for Kaehler manifolds.

Let  $(X^{2n}, \omega)$  be a compact Kaehler manifold. Then we have the following operation in cohomology

$$\gamma: H^p(X, \mathbb{C}) \to H^{p+2}(X) \qquad c \mapsto [\omega] \smile c$$

Theorem (Hard Lefshetz).  $\gamma^p$  is bijective.

Question: Is Hard Lefshetz true for compact symplectic manifolds. If not, when is it true. Define  $[L^t, L] = A$ , by Kaehler-Weil says that  $A\alpha = (n - p)\alpha$ .

**Lemma.**  $[A, L^t] = 2L^t$ .

Proof. 
$$AL^t\alpha - L^tA\alpha = (n - (p - 2))L^t\alpha - (n - p)L^t\alpha = 2L^t\alpha$$

**Lemma.** [A, L] = -2L.

There is another place in the world where you encounter these: Lie Groups.

#### Lie Groups

Take  $G = SL(2, \mathbb{R})$ , then consider the lie algebra  $\mathbf{g} = sl(2, \mathbb{R})$ . This is the algebra  $\{A \in M_{22}(\mathbb{R}), tr \ A = 0\}$ . Generated by

$$X = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix} \qquad Y = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \qquad H = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$$

Check that [X,Y]=H, [H,X]=2X and [H,Y]=-2Y, and  $sl(2,\mathbb{R})=span\{X,Y,Z\}$ , and the above describes the Lie Algebra structure.

 $\rho: \mathbf{g} \to End(\Omega)$  be given by  $X \mapsto L^t$ ,  $Y \mapsto L$  and  $H \mapsto A$  is a representation of the Lie algebra  $\mathbf{g}$  on  $\Omega$ . So  $\Omega$  is a  $\mathbf{g}$ -module.

**Lemma.**  $\Omega_{harm}$  is a **g**-module of  $\Omega$ .

Proof. First note that Ld = dL, i.e.  $dL\alpha = d(\omega \wedge \alpha) = \omega \wedge d\alpha = Ld\alpha$ . Taking transposes we get  $L^t\delta = \delta L^t$ . Then take  $\alpha \in \Omega_{harm}$ . We already know that  $[d, L^t] = \delta$ , so  $dL^t\alpha - L^td\alpha = \delta\alpha$ , which implies that  $dL^t\alpha = 0$ . Similarly  $dL\alpha$ ,  $\delta L\alpha = 0$ , so  $L\alpha$ ,  $L^t\alpha$  are in  $\Omega_{harm}$ .

So since  $A = [L, L^t]$ ,  $A\alpha \in \Omega_{harm}$  and  $\Omega$  is a g-module.

Note that  $\Omega_{harm}$  is not finite dimensional. So these representations are not necessarily easy to deal with.

**Definition.** Let V be a **g**-module. V is of **finite** H-type if

$$V = \bigoplus_{i=1}^{N} V_i$$

and  $H = \lambda_i Id$  on  $V_i$ .

In other words, H is in diagonal form with respect to this decomposition.

**Example.**  $\Omega = \bigoplus_{p=0}^{2n} \Omega^p$ , H = (n-p)Id on  $\Omega^p$  and  $\Omega_{harm} = \bigoplus_{p=0}^{2n} \Omega_{harm}^p$ , H = (n-p)Id on  $\Omega_{harm}^p$ .

**Theorem.** If V is a g-module of finite type, then every sub and quotient module is of finite type.

*Proof.*  $V = \bigoplus_{i=1}^{N} V_i$ ,  $H = \lambda_i Id$  on  $V_i$ . Let  $\pi_i : V \to V_i$  be a projection onto  $V_i$ . Check that

$$\pi_i = \frac{1}{\prod (\lambda_i - \lambda_j)} \prod_{i \neq i} (H - \lambda_j)$$

i.e.,  $\pi_i v = v$  on  $v_i$ . So  $\pi_i$  takes sub/quotient objects onto themselves.

### Lecture 26

**Lemma.** Take  $v \in V$ ,  $Hv = \lambda v$ . We claim that  $H(Xv) = (\lambda + 2)Xv$ .

*Proof.* 
$$(HX - XH)v = 2Xv$$
, so  $HXv = \lambda Xv + 2Xv = (\lambda + 2)Xv$ .

**Lemma.** If  $Hv = \lambda v$ , then

$$[X, Y^k]v = k(\lambda - (k-1))Y^{k-1}v$$

*Proof.* We proceed by induction. If k=1 this is just  $[X,Y]v=Hv=\lambda v$ . This is true. Now we show that if this is true for k, its true for k+1.

$$\begin{split} [X,Y^{k+1}]v &= XY^{k+1}v - Y^{k+1}Xv \\ &= (XY)Y^kv - (YX)Y^kv + Y(XY^k)v - Y(Y^kXv) \\ &= HY^kv + Y([X,Y^k])v \\ &= (\lambda - 2k)Y^kv + Y(k(\lambda - (k-1))Y^{k-1}v \\ &= ((\lambda - 2k) + k(\lambda - k - 1))Y^kv = (k+1)(\lambda - k)Y^kv \end{split}$$

**Definition.** V is a cyclic module with generator v if every submodule of V containing v is equal to V itself.

**Theorem.** If V is a cyclic module of finite H type then  $\dim V < \infty$ .

*Proof.* Let v generate V. Then  $v = \sum_{i=0}^{N} v_i$  where  $v_i \in V_i$ . It is enough to prove the theorem for cyclic modules generated by  $v_i$ . We can assume without loss of generality that  $Hv = \lambda v$ .

Now, note that only a finite number of expression  $Y^k X^l v$  are non-zero (since X shifts into a different eigenspace, and there are only a finite number of eigenspaces).

By the formula that we just proved,  $span\{Y^kX^lv\}$  is a submodule of V containing v.

Fact: Every finite dimensional g-module is a direct sum of irreducibles.

In particular, every cyclic submodule of V is a direct sum of irreducibles.

**Theorem.** Every irreducible **g**-module of finite H type is of the form  $V = V_0 \oplus \cdots \oplus V_k$  where dim  $V_i = 1$ . Moreover, there exists  $v_i \in V_i - \{0\}$  such that

$$Hv_{i} = (k-2i)v_{i}$$

$$Yv_{i} = v_{i+1} i \le k-1$$

$$Xv_{i} = i(k-(i-1))v_{i-1} i \ge 1$$

$$Xv_{0} = 0, Yv_{k} = 0$$

*Proof.* Let  $V = V_0 \oplus \cdots \oplus V_n$ , and  $H = \lambda_i Id$  on  $V_i$  and assume that  $\lambda_0 > \lambda_1 > \cdots > \lambda_n$ . Take  $v \in V_0 - \{0\}$ . Note that Xv = 0, because  $HXv = (\lambda_0 + 2)Xv$  and  $\lambda_0 + 2 > \lambda_0$ .

Consider  $Yv, \ldots, Y^kv \neq 0, Y^{k+1}v = 0$ , so  $HY^iv = (\lambda_0 - 2i)Y^iv$ . and

$$XY^{i}v = Y^{i}Xv + i(\lambda - (i-1))Y^{i-1}v = i(\lambda - (i-1))Y^{i-1}v$$

When i = k + 1 we have

$$XY^{k+1}v = 0 = (k+1)(\lambda - k)Y^kv$$

but  $Y^k v \neq 0$ , so it must be that  $\lambda = k$ . Now just set  $v_i = Y^i v$ .

**Lemma.** Let V be a k+1 dimensional vector space with basis  $v_0, \ldots, v_k$ . Then the relations in the above theorem define an irreducible representation of  $\mathbf{g}$  on V

**Definition.** V a g-module,  $V = \bigoplus_{i=0}^{N} V_i$  of finite H-type. Then  $v \in V$  is **primitive** if

- (a) v is homogenous, (i.e.  $v \in V_i$ )
- (b) Xv = 0.

**Theorem.** If v is primitive then the cyclic submodule generated by v is irreducible and Hv = k where k is the dimension of this module.

*Proof.* 
$$v, Yv, \ldots, Y^kv \neq 0, Y^{k+1} = 0$$
. Take  $v_i = Y^iv$ . Check that  $v_i$  satisfies the conditions.

**Theorem.** Every vector  $v \in V$  can be written as a finite sum

$$v = \sum Y^l v_l$$

where  $v_l$  is primitive.

*Proof.* This is clearly true if V is irreducible (by the relations). Hence this is true for cyclic modules, because they are direct sums of irreducibles, hence this is true in general.

Corollary. The eigenvalues of H are integers.

*Proof.* We need to check this for eigenvectors of the form  $Y^lv$  where v is primitive. But for v primitive we know the theorem is true, i.e. Hv = kv,  $HY^lv = (k-2l)Y^lv$ . So write  $V = \bigoplus V_r$ , H = rId on  $V_r$ 

### Lecture 27

**Theorem.** We can repage ate the sum so that

$$V = \bigoplus_{i=-N}^{N} V_i$$

where

 $H = iId \ on \ V_i$ 

- (a)  $X: V_i \rightarrow V_{i+2}$  and  $Y: V_{i+2} \rightarrow V_i$ .
- (b)  $Y^iV_i \xrightarrow{cong} V_{-i}$  is bijective.

Now, recall that we are going to apply this stuff to Hodge Theory. In particular, let  $(X^{2n}, \omega)$  be a symplectic, compact manifold. Then we define  $L: \Omega^k(X) \to \Omega^{k+2}(X)$  given by  $\alpha \mapsto \omega \wedge \alpha$ ,  $*: \Omega^k \to \Omega^{2n-k}$ ,  $L^t: \Omega^{k+2} \to \Omega^k$  given by  $L^t = *L*$  and we defined  $A: \Omega \to \omega$ , A = iId on  $\Omega^{n-i}$ . The Kaehler-Weil identities said that

$$[L^t, L] = A$$
  $[A, L^t] = 2L^t$   $[A, L] = -2L$ 

So  $\Omega$  is a **g**-module of finite H-type with  $X=L^t,\,Y=L$  and H=A.

Corollary. The map  $L^k: \Omega^{n-k} \to \Omega^{n+k}$  is an isomorphism.

We can apply this to symplectic hodge theory as follows. We know in this case that

$$[d, L^t] = \delta \qquad [\delta, L] = d$$

Let  $\Omega_{harm} = \{ u \in \Omega du = \delta = 0 \}.$ 

**Theorem.**  $\Omega_{harm}$  is a **g**-module of  $\Omega$ .

Corollary. The map  $L^k: \Omega_{harm}^{n-k} \to \Omega_{harm}^{n+k}$  is bijective.

#### Hard Lefshetz Theorem

 $\omega \in \Omega^2$ ,  $d\omega = 0$ . Then  $[\omega]$  defines a cohomology class  $[\omega] \in H^2_{DR}(X) = H^2(X)$ . And in turn we can define a mapping  $\gamma : H^k(X) \to H^{k+2}(X)$  by  $c \mapsto [\omega] \frown c$ .

**Theorem.** Let X be Kaehler then  $\gamma^k: H^{n-k}(X) \to H^{n+k}(X)$  is bijective.

What about the symplectic case? Let  $u \in \Omega_{harm}^k$  with du = 0. Define a mapping  $P_k : \Omega_{harm}^k \to H^k(X)$  by  $u \mapsto [u]$ 

**Theorem.** (Matthieu) Hard Lefshetz holds for X if and only if  $P_x$  is onto for all k.

*Proof.* The "only if" part is covered in the supplementary notes. Now the for the "if" part, we use the following diagram

$$\Omega_{harm}^{n-k} \xrightarrow{L^k} \Omega_{harm}^{n+k}$$

$$\downarrow \qquad \qquad \downarrow$$

$$H^{n-k}(X) \xrightarrow{\gamma^k} H^{n+k}(X)$$

 $L^k$  is bijective, the vertical arrows are surjective, so  $\gamma^k$  is surjective. Poincare duality tells us that dim  $H^{n-k} = \dim H^{n+k}$  so  $\gamma^k$  is bijective.

Remarks:

(a) "if" condition is automatic for Kaehler manifolds

(b) A consequence of Hard Lefshetz. We know that  $H^{2n}(X) \xrightarrow{\cong} \mathbb{R}$  given by  $[u] \mapsto \int_X u$  is (by stokes theorem) bijective. Hence one can define a bilinear form on  $H^{n-k}(X)$  via

$$c_1, c_2 \to \gamma^k c_1 \frown c_2 \in H^{2n}(X) \xrightarrow{\cong} \mathbb{R}$$

By poincare and hard lefshetz this form is non-degenerate, i.e.  $\gamma^k c_1 \frown c_2 = 0$  for all  $c_2$ , then by Poincare  $\gamma^k c_1 = 0$  which implies that  $c_1 = 0$ .

A consequence is that for k odd  $H^k(X)$  is even dimensional.

- (c) Thurston showed that there exists lots of compact symplectic manifolds with  $\dim H^1(X)$  odd, i.e. it doesn't satisfy strong lefshetz.
- (d) For any symplectic manifold X, let  $H^k_{symp}(X) = \operatorname{Im}(\Omega^k_{harm} \to H^k(X))$ . For symplectic cohomology you **do** have Hard Lefshetz.

#### Riemannian Hodge Theory

Let  $V = V^n$  be a vector space over  $\mathbb{R}$ . B is a positive definite inner product on V. Assume V is oriented, then you get  $*: \Lambda^k(V) \to \Lambda^{n-k}(V)$ . Take  $v_1, \ldots, v_n$  to be an oriented orthonormal basis of V.  $I = (i_1, \ldots, i_k)$ ,  $i_1 < \cdots < i_k$ .  $I^c$  the complementary multi-index. Then  $*v_I = \epsilon v_{I^c}$  where  $\epsilon v_I \wedge v_{I^c} = v_1 \wedge \cdots \wedge v_n$  (where  $\epsilon$  is some sign).

Let  $X = X^n$  be a compact Riemannian manifold. From the Riemannian metric we get  $B_p$  a positive definite inner product on  $T_p^*$  so  $B_p$  induces a positive definite inner product on  $\Lambda^k(T_p^*)$ .

From these inner products we get the star operator  $*_p: \Lambda_p^k \to \Lambda_p^{n-k}$  satisfying  $\alpha, \beta \in \Lambda_p^k$ ,  $\alpha \wedge *\beta = B_p(\alpha, \beta)v_p$  where  $v_p$  is the Riemannian volume form.

Its clear that  $B_p$  extends  $\mathbb{C}$ -linearly to a  $\mathbb{C}$ -blinear form on  $\Lambda_p^k \otimes \mathbb{C}$  and  $*_p$  extends  $\mathbb{C}$ -linearly to  $\Lambda_p^k \otimes \mathbb{C}$ .

A hermitian inner product on  $\Lambda^k(T_p^*)\otimes \mathbb{C}$  by  $(\alpha,\beta)_p=B_p(\alpha^{\bar{\beta}})$  and  $\alpha\wedge *\bar{\beta}:=(\alpha,\beta)_pv_p$ .

Globally,  $\Omega^k(X) = C^{\infty}(\Lambda^k(T^*X) \otimes \mathbb{C})$ . Define an  $L^2$  inner-product by  $\alpha, \beta \in \Omega^k(X)$ 

$$\langle \alpha, \beta \rangle = \int_X (\alpha, \beta)_p v = \int_X \alpha \wedge *\bar{\beta}$$

From  $\Omega^0(X) \xrightarrow{d} \Omega^1(X) \xrightarrow{d} \dots$  we get an elliptic complex

$$C^{\infty}(X) \longrightarrow C^{\infty}(\Lambda^1(T^*X) \otimes \mathbb{C}) \longrightarrow \cdots$$

We have a hermitian inner product on the vector bundles  $\Lambda^k(T^*X) \otimes \mathbb{C}$ , so we can get a transpose

$$d^t: C^{\infty}(\Lambda^k(T^*X) \otimes \mathbb{C}) \to C^{\infty}(\Lambda^{k-1}(T^*X) \otimes \mathbb{C})$$

and write  $d^t = \delta$  and think of  $\delta$  as  $\delta : \Omega^k \to \Omega^{k-1}$ .

Form the corresponding Laplacian operator  $\Delta = d\delta + \delta d$ .

Apply the general theory of Elliptic complexes to this case. We conclude that

- (a)  $\mathcal{H}^k = \{u \in \Omega^k, \Delta u = 0\}$  is finite dimensional.
- (b)  $\mathcal{H}^k = \{ u \in \Omega^k, du = \delta u = 0 \}.$
- (c) Hodge Decomposition

$$\Omega^k = \{ (\operatorname{Im} d) \oplus (\operatorname{Im} \delta) \oplus \mathcal{H}^k \}$$

(d) The map  $\mathcal{H}^k \to H_{DR}^k$  is bijective, i.e. every cohomology class has a unquie harmonic representation.

#### Lecture 28

The  $H_{DR}^k$  are finite-dimensional.

#### Poincare Duality

Make a pairing  $P: \Omega^k \times \Omega^{n-k} \to \mathbb{C}$  given by

$$P(\alpha, \beta) = \int_X \alpha \wedge \beta$$

If  $\alpha$  is exact and  $\beta$  closed then  $P(\alpha, \beta) = 0$ , since  $\alpha = d\omega$ ,  $d\beta = 0$  and  $\alpha \wedge \beta = du \wedge \beta = d(u \wedge \beta)$ . By stokes  $\int \alpha \wedge \beta$  is thus 0. P induces a pairing in cohomology,  $P^{\sharp}: H^k_{DR} \times H^{n-k}_{DR} \to \mathbb{C}$ .

Theorem (Poincare). This is a non-degenerate pairing.

We give a Hodge Theoretic Proof. First,

**Lemma.**  $\delta: \Omega^k \to \Omega^{k-1}$  is given by  $\delta = (-1)^k *^{-1} d*$ 

*Proof.* Let  $\delta_1 = (-1)^k *^{-1} d*$ , we want to show that  $\delta = \delta_1$ . Let  $\alpha \in \Omega^{k-1}$  and  $\beta \in \Omega^{n-k}$  then

$$d(\alpha \wedge \bar{\beta}) = d\alpha \wedge \bar{\beta} + (-1)^{k-1}\alpha \wedge d * \bar{\beta}$$
  
=  $d\alpha \wedge *\bar{\beta} + (-1)^{k-1}\alpha \wedge *(*^{-1}d * \bar{\beta})$   
=  $d\alpha \wedge *\bar{\beta} - \alpha \wedge *(\bar{\delta_1}\bar{\beta})$ 

Now integrate and apply stokes

$$\int d\alpha \wedge *\bar{\beta} = \int \alpha \wedge *\delta_1 \beta$$

so  $\langle d\alpha, \beta \rangle = \langle \alpha, \delta_1 \beta \rangle$  and  $\delta_1 = d^t = \delta$ .

Corollary.  $*\mathcal{H}^k = \mathcal{H}^{n-k}$ 

*Proof.* Take  $\alpha \in \mathcal{H}^k$ . We'll show that  $d * \alpha = 0$ . This happens iff  $*^{-1}d * \alpha = \pm \delta \alpha$ . Since  $\delta \alpha = 0$ ,  $d * \alpha = 0$ . It is similarly easy to check that  $\delta * \alpha = 0$ .

*Proof of Poincare Duality*. If suffices to check that the pairing  $P: \mathcal{H}^k \times \mathcal{H}^{n-k} \to \mathbb{C}$  given by  $\alpha, \beta \mapsto \int_X \alpha \wedge \beta$  is non-degenerate.

Suppose  $P(\alpha, \beta) = 0$  for all  $\beta$ . Take  $\beta = *\bar{\alpha}$ . Then

$$P(\alpha, \beta) = \int_{X} \alpha \wedge *\bar{\alpha} = \langle \alpha, \alpha \rangle = 0$$

so this would imply that  $\alpha = 0$ .

## A Review of Kaehlerian Linear Algebra

**Definition.**  $V = V^{2n}$  a vector space over  $\mathbb{R}$ ,  $B_s$  a non-degenerate alternating bilinear form on V,  $J: V \to V$  a linear map such that  $J^2 = -I$ .  $B_s$  and J are compatible if  $B_s(Jv, Jw) = B_s(v, w)$ .

**Lemma.** If  $B_s$  and J are compatible if and only if the bilinear form  $B_r(v, w) = B_s(v, Jw)$  is symmetric. (Here  $B_r$  is a Riemannian metric)

 $J, B_s$  Kaehler implies that  $B_r$  is positive definite.

Notice that  $B_r(Jv, Jw) = B_s(Jv, J^2w) = B_s(v, Jw) = B_r(v, w)$  so that  $B_r$  and J are compatible. And also notice that  $B_r(Jv, w) = B_s(Jv, Jw) = B_s(v, w)$ . Let  $J^t$  be the transpose of J with respect to  $B_r$ . Then

$$B_r(Jv, Jw) = B_r(v, J^tJw) = B_r(v, w)$$

so  $J^t J = I$  and  $J^t = -J$ .

#### $B_r$ , $B_s$ , J in Coordinates

Let  $e \in V$  such that  $B_r(e,e) = 1$ , and set f = Je, and e = -Jf. Then

$$B_r(e,e) = 1 \qquad B_s(e,f) = 1$$

Take  $V_1 = span\{e, f\}$ . This is a *J*-invariant subspace. If we then take

$$V_1^{\perp}$$
 = orthocomplement of  $V_1$  w.r.t  $B_r$ 

then for  $v \in V_1, w \in V_1^{\perp}$ ,  $0 = B_r(Jv, w) = B_s(v, w)$ , so  $V_1^{\perp}$  is the symplectic orthocomplement of  $V_1$  with respect to  $B_s$ .

Applying induction we get a decomposition

$$V = V_1 \oplus V_2 \oplus \cdots \oplus V_n$$

where  $V_i = span\{e_i, f_i\}$  such that  $e_1, f_1, \ldots, e_n, f_n$  is an oriented orthonormal basis of V with respect to  $B_r$  and a Darboux basis with respect to  $B_s$ . Note that  $Je_i = f_i$  and  $Jf_i = -e_i$ 

## **5.0.3** $B_r$ , $B_s$ and J on $\Lambda^k(V)$

 $\omega = \sum e_i \wedge f_i$  is the symplectic element in  $\Lambda^2(V)$  and  $\Omega = \omega^n/n! = e_1 \wedge f_1 \wedge \cdots \wedge e_n \wedge f_n$  is the symplectic volume for and Riemannian volume form.

On decomposable elements,  $\alpha = v_1 \wedge \cdots \wedge v_k$  and  $\beta = w_1 \wedge \cdots \wedge w_k$  and

$$B_r(\alpha, \beta) = \det(B_r(v_i, w_j))$$
  $B_s(\alpha, \beta) = \det(B_s(v_i, w_j))$ 

and we can define

$$J\alpha = Jv_1 \wedge \cdots \wedge Jv_k$$

Notice that

$$B_r(\alpha, \beta) = \det(B_r(v_i, w_j)) = \det B_s(v_i, Jw_j) = B_s(\alpha, J\beta)$$

and furthermore, it is easy to check that  $B_r(J\alpha, J\beta) = B_r(\alpha, \beta)$ ,  $B_s(J\alpha, J\beta) = B_s(\alpha, \beta)$ ,  $J^2 = (-1)^k Id$  and if  $J^t : \Lambda^k \to \Lambda^k$  is the  $B_r$ -transpose of J, then  $J^t = (-1)^k J$ .

#### The Star Operators

These are  $*_r$  and  $*_s$ , the Riemannian and symplectic star operators, respectively. Let  $\Omega$  be the symplectic (and Riemannian) volume form. For  $\alpha, \beta \in \Lambda^k$  we have

$$\alpha \wedge *_r \beta = B_r(\alpha, \beta)\Omega = B_s(\alpha, J\beta) = \alpha \wedge *_s J\beta$$

so

$$*_r = *_s J$$

Also, notice that

$$J\alpha \wedge *_r J\beta = B_r(J\alpha, J\beta)\Omega = B_r(\alpha, \beta)\Omega = \alpha \wedge *_r\beta$$

on the other hand  $J\Omega = \Omega$ , so

$$\alpha \wedge *_r \beta = B_r(\alpha, \beta)\Omega = J\alpha \wedge *_r J *_r \beta$$

so  $*_r J = J *_r$  and since  $*_r = *_s J$  we have  $J *_s = *_s J$ .

## Structure of $\Lambda(V)$

We have a symplectic element  $\omega = \sum e_i \wedge f_i \in \Omega^2$ . From this, we can define a mapping  $L : \Lambda^k \to \Lambda^{k+2}$  given by  $\alpha \mapsto \omega \wedge \alpha$ . Note that

$$LJ\alpha = \omega \wedge J\alpha = J(\omega \wedge \alpha) = JL\alpha$$

so that [J, L] = 0.

Similarly for  $L^t: \Lambda^{k+2} \to \Lambda^k$ , the symplectic transpose given by  $L^t = *_s L *_s$ . Since  $*_s, L$  commute with the J map, so does  $L^t$ , so  $[J, L^t] = 0$ . Notice that

$$B_r(L\alpha,\beta) = B_s(L\alpha,J\beta) = B_s(\alpha,L^tJ\beta) = B_s(\alpha,JL^t\beta) = B_r(\alpha,L^t\beta)$$

so  $L^t$  is also the Riemannian transpose.

From  $L, L^t$  we get a representation of  $SL(2,\mathbb{R})$  on  $\Lambda(V)$  and this representation is J-invariant.

### Lecture 29

We now extend  $*_r, *_s, J, L, L^t$ ,  $\mathbb{C}$ -linearly to  $\Lambda^* \otimes \mathbb{C}$ . And extend  $B_r, B_s$  to  $\mathbb{C}$ -linear forms on  $\Lambda^k \otimes \mathbb{C}$ . We can now take  $\Lambda^1 \otimes \mathbb{C} = \Lambda^{1,0} \oplus \Lambda^{0,1}$ , where as usual the two elements of the splitting are the eigenspaces

If we now let  $e_1, f_1, \ldots, e_n, f_n$  be a Kaehlerian Darboux basis of V and set

$$u_i = \frac{1}{2\sqrt{-1}}(e_i - \sqrt{-1}f_i)$$

then  $u_1, \ldots, u_n$  is an orthonormal basis of  $\Lambda^{1,0}$  with respect to the Hermitian form  $(u,v) = B_r(u,\bar{v})$  and  $\bar{u}_1, \ldots, \bar{u}_n$  is an orthonormal basis of  $\Lambda^{0,1}$ .

We know from earlier that \* gives rise to a splitting

$$\Lambda^k \otimes \mathbb{C} = \bigoplus_{p+q=k} \Lambda^{p,q}$$

and if I and J are multi-indices of length p and q, then the  $u_I \wedge \bar{u}_J$  forms form an orthonormal basis of  $\Lambda^{p,q}$ with respect to the Riemannian bilinear form  $(\alpha, \beta) = B_r(\alpha, \bar{\beta})$ .

In particular  $\Lambda^k \otimes \mathbb{C} = \bigoplus_{p+q} \Lambda^{p+q}$  is an orthonormal decomposition of  $\Lambda^k \otimes \mathbb{C}$  with respect to the inner product  $(\alpha, \beta) = B_r(\alpha, \bar{\beta})$ .

In terms of  $u_1, \ldots, u_n \in \Lambda^{1,0}$ , the symplectic form is

$$\omega = \frac{1}{2\sqrt{-1}} \sum u_i \wedge \bar{u}_i \in \Lambda^{1,1}$$

Consequences:

- (a)  $L: \Lambda^{p,q} \to \Lambda^{p+1,q+1}, \alpha \in \Lambda^{p,q}$
- (b)  $J = (\sqrt{-1})^{p-q} Id$  on  $\Lambda^{p,q}$ .
- (c) The star operators behave nicely,  $*_s : \Lambda^{p,q} \to \Lambda^{n-p,n-q}$ .
- (d)  $*_r: \Lambda^{p,q} \to \Lambda^{n-p,n-q}, *_r = *_s J.$
- (e)  $L^t: \Lambda^{p,q} \to \Lambda^{p-1,q-1}$  because  $L^t = *_s L *_s$ .

So all the operators behave well as far as bi-degrees are concerned.

#### Kaehlerian Hodge Theory

Let  $(X^{2n}, \omega)$  be a compact Kaehler manifold, with  $\omega \in \Omega^{1,1}$  a Kaehler form.

From the complex structure we get a mapping  $J_p: \Lambda^k(T_p^*) \otimes \mathbb{C} \to \Lambda^k(T_p^*) \otimes \mathbb{C}$ . This induces a mapping  $J:\Omega^k(X)\to\Omega^k(X)$  by defining  $(J\alpha)_p=J_p\alpha_p$  and we have as before the \*-operators,  $*_r,*_s:\Omega^k(X)\to \Omega^k(X)$  $\Omega^{2n-k}$  related by  $*_r = *_s \otimes J$ .

We also have  $\langle , \rangle_r, \langle , \rangle_s$  bilinear forms on  $\Omega^k$  defined by

$$\langle \alpha, \beta \rangle_r = \int_X \alpha \wedge *_r \bar{\beta} \qquad \langle \alpha, \beta_S = \int_X \alpha \wedge *_s \beta$$

 $L:\Omega^k\to\Omega^{k+2}$  is given by  $\alpha\mapsto\omega\wedge\alpha$  and  $L^t=*_sL*_s=*_r^{-1}L*_r$ , the transpose of L with respect to  $\langle,\rangle_r$ 

Finally, we have  $d:\Omega^k\to\Omega^{k+1}$  and its transpose  $\delta=\delta_r$  the transpose w.r.t.  $\langle,\rangle_r$  and  $\delta_s$  the transpose w.r.t.  $\langle , \rangle_s$ . On  $\Omega^k$ ,  $\delta_r = (-1)^k *_r^{-1} d *_r$  and  $\delta_s = (-1)^k *_s d *_s$ . But from  $*_r = *_s \circ J$  we get

$$\delta_r = (-1)^k J^{-1} *_{s}^{-1} d *_{s} \circ J = J^{-1} \delta_s J$$

We proved a little while ago that  $d = [\delta_s, L]$ . What happens upon conjugation by J?

$$JdJ^{-1} = [J^{-1}\delta_s J, L] = [\delta, L]$$

We make the following definition

**Definition.**  $d_{\mathbb{C}} = JdJ^{-1}$ 

So now we have

$$d_{\mathbb{C}} = [\delta, L]$$

**Theorem.** d and  $d_{\mathbb{C}}$  anti-commute

We'll prove this later. But for now, we'll prove an important corollary

Corollary. Let  $\Delta = d\delta + \delta d$ . Then L and L<sup>t</sup> commute with  $\Delta$ 

*Proof.*  $[d\delta, L] = [d, L]\delta + d[\delta, L]$ , and we showed before that [d, L] = 0 and  $d[\delta, L] = dd_{\mathbb{C}}$ . Similarly  $[\delta d, L] = d\mathbb{C}d$ , so  $[\Delta, L] = 0$ .

 $L^t$  is the Riemannian transpose of L, and in this setting  $\Delta^t = \Delta$ , so  $[\Delta, L^t] = 0$ .

We will now use the above to prove Hard Lefshetz

Takef

$$\mathcal{H} = \bigoplus_k \mathcal{H}^k \qquad \mathcal{H}^k = \ker \Delta : \Omega^k \to \Omega^k$$

By the results above  $\mathcal{H}$  is invariant under  $L, L^t$  and  $A = [L, L^t]$ . So  $\mathcal{H}$  is a finite-dimensional  $SL(2, \mathbb{R})$  module.

We prove for  $SL(2,\mathbb{R})$  modules that  $L^k:\mathcal{H}^{n-k}\to\mathcal{H}^{n+k}$  is bijective.

In the Kaehler case we get the following diagram

$$\mathcal{H}^{n-k} \xrightarrow{L_k} \mathcal{H}^{n+k}$$

$$\cong \bigvee_{Y} \bigvee_{Y} \cong \bigoplus_{P} H^{n-k}_{DR}(X) \xrightarrow{\gamma^k} H^{n+k}_{DR}(X)$$

where  $\gamma^k c = [\omega^k] \wedge c$ .

Unlike the diagram in the symplectic case, in this case the vertical arrows are bijections. So  $\gamma^k$  is bijective, which is strong Lefshetz.

#### Lecture 30

**Lemma.**  $d, d^{\mathbb{C}}$  anti-commute

*Proof.* Write  $d = \partial + \overline{\partial}$ , where  $\partial : \Omega^{p,q} \to \Omega^{p+1,q}$ ,  $\overline{\partial} : \Omega^{p,q} \to \Omega^{p,q+1}$ . Now,  $d^{\mathbb{C}} = J^{-1}dJ = J^{-1}\partial J + J^{-1}\overline{\partial}J$ . Take  $\alpha \in \Omega^{p,q}$  then

$$J^{-1}\partial J\alpha = i^{p-q}J^{-1}\partial\alpha = -\frac{i^{p-q}}{i^{p+1-q}}\partial\alpha = -i\partial\alpha$$
$$J^{-1}\overline{\partial}J\alpha = \frac{i^{p-q}}{i^{p-(q+1)}}\overline{\partial}\alpha = i\overline{\partial}\alpha$$

So  $d^{\mathbb{C}} = -i(\partial - \overline{\partial})$ , so  $d^{\mathbb{C}}$ , d anti-commute because  $\partial + \overline{\partial}$  and  $\partial = \overline{\partial}$  anti-commute.

Now, some more Hodge Theory.

Take the identity  $d^{\mathbb{C}} = [\delta, L]$  and decompose into its homogeneous components, by using  $d^{\mathbb{C}} = -i(\partial - \overline{\partial})$ . Then  $\partial^t : \Omega^{p,q} \to \Omega^{p-1,q}$ ,  $\overline{\partial}^t : \Omega^{p,q} \to \Omega^{p,q-1}$  then  $\delta = d^t = \partial^t + \overline{\partial}^t$ . So  $d^{\mathbb{C}} = [\delta, L]$  because

$$-i(\partial - \overline{\partial}) = [\partial^t, L] + [\overline{\partial}^t, L]$$

and by matching degrees we get

$$i\overline{\partial} = [\partial^t, L] \qquad -\partial = [\overline{\partial}^t, L]$$

We'll play around with these identities for a little while.

We already know that  $\partial^2 = \overline{\partial}^2 = \partial \overline{\partial} + \overline{\partial} \partial = 0$ . And so  $(\partial^t)^2 = (\overline{\partial}^t)^2 = \overline{\partial}^t \partial^t + \partial^t \overline{\partial}^t = 0$ . Bracket these with L and we get

$$0 = [(\partial^t)^2, L] = [\partial^t, L]\partial^t + \partial^t[\partial^t, L] = i\overline{\partial}\partial^t + \partial^t(i\overline{\partial})$$

so

$$\overline{\partial}\partial^t + \partial^t \overline{\partial} = 0$$

Similarly, from  $0 = [(\overline{\partial}^t)^2, L]$  we get

$$\overline{\partial}^t \partial + \partial \overline{\partial}^t = 0$$

Lemma. The above identities imply the following

$$\Delta = \Delta_{\partial} + \Delta_{\overline{\partial}}$$

Proof.

$$\begin{split} \Delta &= dd^t + d^t d \\ &= (\partial + \overline{\partial})(\partial^t + \overline{\partial}^t) + (\partial^t + \overline{\partial}^t)(\partial + \overline{\partial}) \\ &= \Delta_{\partial} + \Delta_{\overline{\partial}} + (\overline{\partial}\partial^t + \partial \overline{\partial}^t) + (\partial^t \overline{\partial} + \overline{\partial}^t \partial) \end{split}$$

Now since  $\partial^t \overline{\partial}^t + \overline{\partial}^t \partial^t = 0$  and we get

$$\begin{split} 0 &= [\overline{\partial}^t \partial^t + \partial^t \overline{\partial}^t, L] \\ &= [\partial^t \overline{\partial}^t, L] + [\overline{\partial}^t \partial^t, L] \\ &= \partial^t [\overline{\partial}^t, L] + [\partial^t, L] \overline{\partial}^t + \overline{\partial}^t [\partial^t, L] + [\overline{\partial}^t, L] \partial^t \\ &= -i(\partial^t \partial - \overline{\partial} \overline{\partial}^t) - i(\partial \partial^t - \overline{\partial}^t \overline{\partial}) \end{split}$$

And we get  $\partial^t \partial + \partial \partial^t - \overline{\partial}^t \overline{\partial} - \overline{\partial} \overline{\partial}^t = 0$ , i.e.

$$\Delta_{\partial} - \Delta_{\overline{\partial}} = 0$$

But since  $\Delta = \Delta_{\partial} + \Delta_{\overline{\partial}}$ ,  $\Delta_{\partial} = \Delta_{\overline{\partial}} = \frac{1}{2}\Delta$ . "This has some really neat applications"

#### Neat Applications

 $\Delta_{\overline{\partial}}$  is the Laplace operator for the  $\overline{\partial}$  complex

$$\Omega^{1,0} \xrightarrow{\overline{\partial}} \Omega^{i,1} \xrightarrow{\overline{\partial}} \cdots$$

so it maps  $\Omega^{i,j}$  to  $\Omega^{i,j}$  which implies  $\Delta: \Omega^{i,j} \to \Omega^{i,j}$ . So  $\mathcal{H}^k = \ker \Delta: \Omega^k \to \Omega^k$  is a direct such

$$\mathcal{H}^k = \bigoplus_{i+j=k} \mathcal{H}^{i,j}$$

where  $\mathcal{H}^{i,j} = \mathcal{H}^k \cap \Omega^{i,j}$ .

We get a similar decomposition in cohomology

$$H^k(X,\mathbb{C}) = \bigoplus_{i+j=k} H^{i,j}(X) = \operatorname{Im} \mathcal{H}^{i,j}$$

where  $\mathcal{H}^{i,j} = \ker \Delta_{\overline{\partial}} : \Omega^{i,j} \to \Omega^{i,j}$ , so  $\mathcal{H}^{i,j}$  is the jth harmonic space for the Dolbeault complex. So  $H^k(X,\mathbb{C}) = \bigoplus H^{i,j}_{\overline{\partial}}(X)$ .

## Chapter 6

# Geometric Invariant Theory

#### Lecture 31

#### Lie Groups

Goof references for this material: Abraham-Marsden, Foundations of Mechanics (2nd edition) and Ana Canas p. 128

Let G be a lie group. Denote by  $\mathfrak{g}$  the Lie algebra of G which is  $T_eG$ , with the lie bracket operation.

**Definition.** The exponential is a map  $\exp : \mathfrak{g} \to G$  with the following properties

(a)  $\mathbb{R} \to G$ ,  $t \mapsto \exp tv$  is a lie group homomorphism.

(b)

$$\frac{d}{dt} \exp tv \bigg|_{t=0} = v \in T_e G = \mathfrak{g}$$

**Example.**  $G = GL(n, \mathbb{R}) = \{A \in M_{n \times n}(\mathbb{R}) \mid \det(A) \neq 0\}$ . Then  $\mathfrak{g} = \mathfrak{gl}(n, \mathbb{R}) = M_{n \times n}(\mathbb{R})$  and [A, B] = AB - BA and

$$\exp A = \sum \frac{A^i}{i!}$$

**Example.** G a compact connected abelian Lie group. Then the lie algebra is  $\mathfrak{g}$  with  $[,] \equiv 0$ .  $\mathfrak{g}$  is a vector space, i.e. an abelian lie group in its own right. Then the exponential map  $\exp: \mathfrak{g} \to G$  is a surjective lie group homomorphism.

Let  $\mathbb{Z}_G = \ker \exp$  be called the Group lattice of G, then  $G = \mathfrak{g}/\mathbb{Z}_G$ , by the first isomorphism theorem. For instance, take  $G = (S^1)^n = T^n$ , then  $\mathfrak{g} = \mathbb{R}^n$ ,  $\exp : \mathbb{R}^n \to T^n$  is given by  $(t_1, \ldots, t_n) \mapsto (e^{it_1}, \ldots, e^{it_n})$ . Then  $\mathbb{Z}_G = 2\pi\mathbb{Z}^n$  and  $G \cong \mathbb{R}^n/2\pi\mathbb{Z}^n$ .

#### Group actions

Let M be a manifold.

**Definition.** An action of G on M is a group homomorphism

$$\tau: G \to Diff(M)$$

where  $\tau$  is smooth if  $ev: G \times M \to M$ ,  $(g, m) \to \tau_q(m)$  is smooth.

**Definition.** Then infinitesimal action of  $\mathfrak{g}$  on M

$$d\tau: \mathfrak{g} \to Vect(M)$$
  $v \in \mathfrak{g} \mapsto v_M$ 

is given by

$$\tau(\exp tv) = \exp(-tv_M)$$

**Theorem.**  $d\tau$  is a morphism of lie algebras.

Given  $p \in M$  denote

$$G_p = \{g \in G, \tau_g(p) = p\}$$

This is the **isotropy group of** p of the **stabilizer of** p. Then

$$\operatorname{Lie} G_p = \{ v \in \mathfrak{g} \mid v_m(p) = 0 \}$$

**Definition.** The orbit of G through p is

$$G \circ p = \{ \tau_q(p) \mid g \in G \}$$

This is an immersed submanifold of M, and its tangent space is given by  $T_p(G \circ p) = \mathfrak{g}/\mathfrak{g}_p$ .

The orbit space of  $\tau$  is M/G = the set of all orbits, or equivalently  $M/\sim$  where  $p,q\in M$  and  $p\sim q$  iff  $p = \tau_g(q)$  for some  $g \in G$ .

We can topologize this space, by the projection

$$\pi: M \to M/G \qquad p \mapsto G \circ p$$

and define the topology of M/G by  $U \subset M/G$  is open if and only if  $\pi^{-1}(U)$  is open (i.e. assign M/G the weakest topology that makes  $\pi$  continuous). This, however, can be a nasty topological space.

**Example.**  $M = \mathbb{R}$ ,  $G = (\mathbb{R}^+, \times)$ . And  $\tau$  maps t to multiplication by t. Then M/G is composed of 3 points,  $\pi(0), \pi(1)$  and  $\pi(-1)$ , but the set  $\{\pi(1), \pi(-1)\}$  is not closed.

**Definition.** The action  $\tau$  is **free** if  $G_p = \{e\}$  for all p (e the identity).

**Definition.** The action  $\tau$  is locally free if  $\mathfrak{g} = \{0\}$  for all p (this happens if and only if  $G_p$  is discrete).

**Definition.**  $\tau$  is a proper action if the map  $G \times M \to M \times M$  given by  $(g,m) \mapsto (m,\tau_q(m))$  is a proper

**Theorem.** If  $\tau$  is free and proper then M/G is a differentiable manifold and  $\pi: M \to M/G$  is a smooth fibration.

*Proof.* (Sketch) S a slice of a G-orbit through pi.e, S is a submanifold of M of codim =  $\dim G$ , with  $S \cap G \circ p = \{p\}, T_pS \oplus T_pG \circ p = T_pM$ . Its not hard to construct such slices.

Then look at the map  $G \times S \to M$ ,  $(g,s) \to \tau_g(s)$ . This is locally a diffeomorphism at (e,p) and group invariance implies that it is locally a diffeomorphism on  $G \times \{p\}$ . So it maps a neighborhood W of  $G \times \{p\}$ diffeomorphically onto an open set U of U of U of U of U of U diffeomorphically onto an open set that  $U = G \times U$  where U of U is a coordinate patch on U centered at U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of U of

**Definition.** G is a **complex Lie group** if G is a complex manifold and the group operations  $(g,h) \mapsto gh$ and  $g \mapsto g^{-1}$  are holomorphic.

**Example.** (a)  $G = GL(n, \mathbb{C}) = \{A \in M_n(\mathbb{C}) \mid \det A \neq 0\}$ . And the lie algebra is  $M_n(\mathbb{C}) = \mathfrak{gl}(n, \mathbb{C})$ .

- (b)  $\mathbb{C}^* = \mathbb{C} \{0\}.$
- (c) Complex Tori. For instance  $T^n_{\mathbb{C}} = (\mathbb{C}^*)^n$ .

**Definition.** An action  $\tau$  of G on M is holomorphic if

$$ev: G \times M \to M$$

is holomorphic.

In particular for  $g \in G$ ,  $\tau_g : M \to M$  is a biholomorphism and the G-orbits

$$G \circ p$$

are complex submanifolds of G.

**Theorem.** If  $\tau$  is free and proper the orbit space M/G is a complex manifold and the fibration  $\pi: M \to M/G$ is a holomorphic fiber mapping.

*Proof.* Imitate the proof above with S being a holomorphic slice of  $G \circ p$  at p.

#### Symplectic Manifolds and Hamiltonian G-actions

Let G be a connected Lie group and  $M, \omega$  a symplectic manifold. An action,  $\tau$  of G on M is symplectic if  $\tau_g^*\omega = \omega$  for all g,i.e. the  $\tau_g$  are symplectomorphisms.

Thus if  $v \in \mathfrak{g}$ 

$$\tau(\exp tv)^*\omega = \omega = \exp(-tv_M)^*\omega$$

Then

$$\frac{d}{dt}\exp(-tv_M)^*\omega\bigg|_{t=0} = L_{v_M}\omega = 0.$$

This implies that

$$\iota(v_M)d\omega + d\iota(v_M)\omega = d\iota(v_M)\omega = 0$$

so  $\iota_{v_M}\omega$  is closed.

**Definition.**  $\tau$  is a **Hamiltonian action** if for all  $v \in \mathfrak{g}$ ,  $\iota(v_M)\omega$  is exact.

#### The Moment Map

Choose a basis  $v^1, \ldots, v^n$  of  $\mathfrak{g}$  and let  $v_1^*, \ldots, v_n^*$  be a dual basis of  $\mathfrak{g}^*$ . If  $\tau$  is hamiltonian then  $\iota(v_M^i)\omega = d\phi^i$ , where  $\phi^i \in C^\infty(M)$ .

**Definition.** The map  $\Phi: M \to \mathfrak{g}^*$  defined by

$$\Phi = \sum \phi^i v_i^*$$

is called the moment map

Remarks

(a) Note that for every  $v \in \mathfrak{g}$ ,

$$\iota(v_M)\omega = d\phi^v$$
 where  $\phi^v = \langle \Phi, v \rangle$ 

- (b)  $\Phi$  is only well defined up to an additive constant  $c \in \mathfrak{g}^*$ .
- (c) If M is compact one can normalize this constant by requiring that

$$\int_{M} \phi^{i} \frac{\omega^{n}}{n!} = 0$$

(d) Another normalization: If  $p \in M^G$ , i.e. if  $G_p = G$ , then one can require that  $phi^i(p) = 0$  for  $i = 1, \ldots, n$ , then  $\Phi(p) = 0$ .

#### Lecture 32

Properties of the moment map.

For  $v, w \in \mathfrak{g}$ , we have

$$L_{v_M} d\phi^w = L_{v_M}(\iota(w_M)\omega) = \iota([v_M, w_M])\omega + \iota(w_M)L_{v_M}\omega = \iota([v_M, w_m])\omega = d\phi^{[v, w]}$$

so

$$L_{v_M} \phi^W = \phi^{[v,w]} + \text{constant}$$

**Definition.**  $\Phi$  is **equivariant** if and only if

$$L_{v_M}\phi^w = \phi^{[v,w]}$$

Remark: For G abelian, i.e. [,] = 0 we have that equivarience implies G invariance, i.e.

$$\Phi(\tau_q(p)) = \Phi(p) \quad \forall p$$

Also, there is a derivative of the moment map  $d\Phi_p: T_pM \to \mathfrak{g}^*$ .

**Theorem.** (a)  $\operatorname{Im}(d\Phi_p) = \mathfrak{g}_p^{\perp}$ 

(b)  $\ker d\Phi_p = (T_p G \circ p)^{\perp}$ .

Two parts:

**Notation.** The " $\perp$ " in a) is the set of all  $v \in \mathfrak{g}$  with  $\langle v, l \rangle = 0$  for  $l \in \operatorname{Im} d\Phi_p$ . The " $\perp$ " in b) is the symplectic  $\perp$ : The set of all  $w \in T_pM$  with  $\omega_p(w, u) = 0$  for  $u \in T_pG \circ p$ .

*Proof.* Recall that  $T_pG \circ p = \{v_M(p), v \in \mathfrak{g}\}$ . For every  $v \in \mathfrak{g}$  and  $w \in T_pM$  we have

(\*) 
$$\langle d\Phi_p(w), v \rangle = d\Phi_p^v(w) = \omega_p(v_M, w)$$

Hence if (\*) = 0 for all w, then  $\iota(v_M)\omega_p = 0$ , so  $v_M(p) = 0$ . Similarly if (\*) = 0 for all v, then  $w \perp T_p G \circ p$ .

#### De Rham Theory on Quotient Spaces

Let G be a connected Lie group, and  $\tau$  an action of G on M. Suppose  $\tau$  is free and proper. Then M/G is a manifold and

$$\pi: M \to M/G = B$$

is a fibration, whose fibers are the G-orbits.

**Definition.** A k-form  $\omega \in \Omega^k(M)$  is **basic** if

- (a) It is G-invariant, i.e.  $\tau_q^*\omega = \omega$  for all  $g \in G$ .
- (b)  $\iota(v_M)\omega = 0$  for all  $v \in \mathfrak{q}$ .

**Theorem.**  $\omega$  is basic if and only if there exists a  $\nu \in \Omega^k(B)$  with  $\omega = \pi^* \nu$ .

The proof will be given in a series of lemmas:

**Lemma.** For  $p \in M$  and  $q = \pi(p)$  then sequence

$$0 \longrightarrow T_p G \circ p \xrightarrow{i} T_p Z \xrightarrow{d\pi_p} T_q B$$

is exact.

*Proof.*  $\pi$  is a fibration and  $G \circ p$  is the fiber through p. N.B.  $T_pG \circ p = \{v_M(p), v \in \mathfrak{g}\}.$ 

**Lemma.** If  $\iota(v_M)\mu_p=0$  for all  $v\in\mathfrak{g}$  there exists a  $\nu_q\in\Lambda^k(T^*B)$  with  $(d\pi_p)^*\nu_q=\mu_p$ 

#### Symplectic Reduction

Assume G is compact, connected and  $(M, \omega)$  is a symplectic manifold. Let  $\tau$  be a Hamiltonian action of G with moment map  $\Phi: M \to \mathfrak{g}^*$ . Assume  $0 \in \mathfrak{g}^*$  is a regular value of  $\Phi$ , i.e. for all  $p \in \Phi^{-1}(0)$ ,  $d\Phi_p$  is surjective. Then  $Z = \Phi^{-1}(0)$  is a submanifold of M.

**Proposition.** Two things

- (a) Z is G-invariant.
- (b) The action of G on Z is locally free.

Proof. Z is G-invariant if and only if  $\exp tv_M : Z \to Z$  for all  $v \in \mathfrak{g}$  if and only if  $v_m(p) \in T_p Z$ , for all  $p \in Z$ . But  $v_M(p) \in T_p Z$  if and only if  $d\Phi_p(v_M(p)) = 0$  if and only if  $d\varphi_p^w(v_M(p)) = 0$  for all w if and only if  $L_{v_M} \varphi^w(p) = 0$  on Z if and only if  $\varphi_p^{[v,w]}(p) = 0$  at p. But  $p \in \Phi^{-1}(0)$ .

To prove that the G action is locally free: At  $p \in Z$ ,  $d\Phi_p : T_p \to \mathfrak{g}^*$  is onto. So  $(\operatorname{Im} d\Phi_p)^{\perp} = \mathfrak{g}_p = 0$  if and only if the G action is locally free at p.

Assume G acts free on Z. Since G is compact it acts properly. And  $Z/G = M_{red}$  is a  $C^{\infty}$  manifold.

**Proposition.** Let  $i: Z \to M$  be inclusion and  $\pi: Z \to Z/G = M_{red}$ . There exists a unique symplectic form  $\omega_{red}$  on  $M_{red}$  with the property that  $\iota^*\omega = \pi^*\omega_{red}$ . So the orbit space has a god-given symplectic form.

Proof.  $\mu = i^*\omega$ ,  $v \in \mathfrak{g}$ , then  $\iota(v_Z)\mu = \iota^*(\iota(v_M)\omega) = \iota d\phi^v = 0$ , since  $\phi^v = 0$  on Z. Moreover,  $\omega$  G-invariant implies that  $\mu$  is G-invariant. So we conclude that  $\mu$  is basic, i.e.  $\mu = \pi^*\omega_{red}$ , with  $\omega_{red} \in \Omega^2(M_{red})$ .

Check that this form is symplectic at  $p \in M_{red}$ ,  $q = \pi(p)$ ,  $p \in Z$ . Then

$$TG \circ p \subset T_p Z = \ker(d\Phi_p) : T_p \to \mathfrak{g}^* = (T_p G \circ p)^{\perp}$$

But  $T_q M_{red} = T_p Z / T_p G \circ p = (T_p G \circ p)^{\perp} / (T_p G \circ p)$  and we conclude that this is a symplectic vector space.  $\square$ 

### Lecture 33

First, some general Lie theory things. G a compact, connected Lie group. Let  $G_{\mathbb{C}} \supset G$  a complex Lie group.

**Definition.**  $G_{\mathbb{C}}$  is the complexification of G if

- (a)  $\mathfrak{g}_{\mathbb{C}} = Lie \ G_{\mathbb{C}} = \mathfrak{g} \otimes \mathbb{C}$
- (b) The complex structure on  $T_eG_{\mathbb{C}}$  is the standard complex structure on  $\mathfrak{g}\otimes\mathbb{C}$ .
- (c)  $\exp: \mathfrak{g}_{\mathbb{C}} \to G_{\mathbb{C}}$  maps  $\mathfrak{g}$  into G.
- (d) The map  $\sqrt{-1}\mathfrak{g}\times G\to G_{\mathbb{C}}$  defined by  $(\omega,g)\mapsto (\exp\omega)g$  is a diffeomorphism.

Take G = U(n). What is  $\mathfrak{g}$ ? Let  $H_n$  be the Hermitian matrices. If  $A \in H_n$ , then  $\exp \sqrt{-1}tA \subset U(n)$ , so  $\mathfrak{g} = \sqrt{-1}H_n$ .

Exercise Show  $G_{\mathbb{C}} = GL(n, \mathbb{C})$ 

(a)  $M_n(\mathbb{C}) = Lie\ GL(n,\mathbb{C}) = H_n \oplus \sqrt{-1}H_n$  given by the decomposition

$$A \mapsto \frac{A + \bar{A}^t}{2} + \frac{A - \bar{A}^t}{2}$$

- (b) Polar decomposition theorem: For  $A \in GL(n,\mathbb{C})$  then A = BC where B is positive definite,  $B \in H^n$  and  $C \in U(n)$ .
- (c) exp:  $H_n^* \to H_n^{*\text{pos. def}}$  is an isomorphism. This maps a matrix with eigenvalues  $\lambda_i$  to a matrix with eigenvalues  $e^{\lambda_i}$ .

**Example.** Take G a compact, connected abelian Lie group. Then  $G = \mathfrak{g}/\mathbb{Z}_G$  and  $G_{\mathbb{C}} = \mathfrak{g}_{\mathbb{C}}/\mathbb{Z}_G$ .

Let M be a Kaehler manifold,  $\omega$  a Kaehler form, and  $\tau$  a holomorphic action of  $G_{\mathbb{C}}$  on M.

**Definition.**  $\tau$  is a Kaehler action if  $\tau \mid_G$  is hamiltonian.

So we have a moment map  $\Phi: M \to \mathfrak{g}^*$  and for  $v \in \mathfrak{g}$  we have  $v_M$  a vector field on M, and

$$\iota(v_M)\omega = d\phi^v \qquad \phi^v = \langle \Phi, v \rangle$$

For  $p \in M$  note that because M is Kaehler we have the addition bits of structure  $(B_r)_p, (B_s)_p, J_p$  on  $T_pM$ .

Now take  $v \in \mathfrak{g}$ ,  $\sqrt{-1}v = w \in \mathfrak{g}_{\mathbb{C}}$ . From these we get corresponding vector fields  $v_M, w_M$ .

**Lemma.** At every  $p \in M$ 

$$w_M(p) = J_p v_M(p)$$

*Proof.* Consider  $\epsilon: G_{\mathbb{C}} \to M$ ,  $g \mapsto \tau_{g^{-1}}(p)$ . This is a holomorphic map and  $(d\epsilon)_p: \mathfrak{g}_{\mathbb{C}} \to T_pM$  is  $\mathbb{C}$ -linear and maps v, w into  $v_M(p), w_M(p)$ .

**Proposition.** If  $v \in \mathfrak{g}$ ,  $w = \sqrt{-1}v$ , ten the vector field  $w_M$  is the <u>Riemannian</u> gradient of  $\phi^v$ .

*Proof.* Take  $p \in M$ ,  $v \in T_pM$ . Then

$$(B_r)_p(v, w_M(p)) = B_s(v, J_p w_M(p)) = -B_s(v, v_M(p)) = \iota(v_M(p))\omega_p(v) = d\phi_p^v(v)$$

QED  $\square$ 

Assume  $\Phi: M \to \mathfrak{g}^*$  is proper. Let  $Z = \Phi^{-1}(0)$ . Assume that G acts freely on Z. Then Z is a compact submanifold of M. Then we can form the reduction  $M_{red} = Z/G$ .

Consider  $G_{\mathbb{C}} \times Z \to M$  given by  $(g, z) \mapsto \tau_g(z)$ . Let  $M_{st}$  be the image of this map. Note that  $G_{\mathbb{C}}$  is a subset of M.

**Theorem (Main Theorem).** (a)  $M_{st}$  is an open  $G_{\mathbb{C}}$ -invariant subset of M.

- (b)  $G_{\mathbb{C}}$  acts freely and properly on  $M_{st}$ .
- (c) Every  $G_{\mathbb{C}}$  orbit in  $M_{st}$  intersects Z in a unique G-orbit.
- (d) Hence  $M_{st}/G_{\mathbb{C}} = Z/G = M_{red}$ .
- (e)  $\omega_{red}$  is Kaehler.

*Proof.* (a) Since  $M_{st}$  is  $G_{\mathbb{C}}$ -invariant it suffices to show that  $M_{st}$  contains an open neighborhood of Z. Note that since  $G_{\mathbb{C}} = (\exp \sqrt{-1}g)G$  implies that  $M_{st}$  is the image of

$$\psi: \sqrt{-1}g \times Z \to M \qquad (\omega, p) \mapsto (\exp w_m)(p)$$

Hence it suffices to show that  $\psi$  is a local diffeomorphism at all points (0,p). Hence it suffices to show that  $(d\psi)_{0,p}$  is bijective.

But  $(d\pi)_{0,p}: T_pZ \to T_pZ$ . So it suffices to finally prove that

**Lemma.**  $(d\psi)_{0,p}$  maps  $\sqrt{-1}\mathfrak{g}$  bijectively onto  $(T_pZ)_p^{\perp}$  in  $T_pM$ .

*Proof.* Let  $w = \sqrt{-1}v$  in  $\sqrt{-1}\mathfrak{g}$ ,  $v \in T_pZ$ . Then

$$B_r(v, w_M(p)) = d\varphi_n^v(v) = 0$$

so  $w_M(p) \perp T_p Z$ .

(b)  $G_{\mathcal{C}}$  acts freely on  $M_{st}$ .

**Lemma.** If  $p \in Z$  and  $w \in \sqrt{-1}\mathfrak{g} - \{0\}$ . Then  $(\exp w_M)(p) \in Z$ .

*Proof.* Let  $w = \sqrt{-1}v, v \in \mathfrak{g}$ , then  $(\exp tw_M)(p)$  is an integral curve of a gradient vector field of  $\varphi^v$ . Now  $\varphi^v(p) = 0$  so  $\varphi^v(\exp tw_M)(p) > 0$  for t > 0 (since gradient vector fields are increasing. So  $\varphi^v(\exp w_M)(p) > 0$  and so  $\exp w_M(p) \notin Z$ .

To show that  $G_{\mathbb{C}}$  acts freely on  $M_{st}$  it suffices to show that  $G_{\mathbb{C}}$  acts freely at  $p \in Z$ . Let  $a \in G_{\mathbb{C}}$ ,  $a = (\exp - w)_g$ , where  $w \in \sqrt{-1}\mathfrak{g}, g \in G$ . Suppose  $a \in (G_{\mathbb{C}})_p$  then  $(\exp w_M)(\tau_g(p)) = p$ . But  $\tau_g(p) = q \in Z$ . So  $(\exp w_M)(q) = p \in Z$  which implies w = 0, a = G. So  $(G_{\mathbb{C}}) = G_p = \{e\}$ . We will skip proving that  $G_{\mathbb{C}}$  acts properly on  $M_{st}$ .

(c) This will be an exercise

**Exercise** Every  $G_{\mathbb{C}}$ -orbit in  $M_{st}$  intersects Z in a unique G orbit. Hint: Every  $G_{\mathbb{C}}$  orbit in  $M_{st}$  is of the form  $G_{\mathbb{C}} \circ p$  with  $p \in Z$ .  $a \in (G_{\mathbb{C}} \circ p) \cap Z$ . Then  $a = (\exp w_M)\tau_g(p), g \in G, w \in -sqrt-1\mathfrak{g}$ . Argue as before and force w = 0.

- (d) So  $M_{red} = Z/G = M_{st}/G_{\mathbb{C}}$ .
- (e) All that remains to show is that  $\omega_{red}$  is Kaehler.

*Proof.*  $p \in Z$ ,  $\pi: Z \to M_{red}$ ,  $q = \pi(p)$ . Let V be the  $B_r$ -orthocomplement in  $T_pM$  to  $T_p(G_{\mathbb{C}} \circ p)$  implies that  $V \subseteq T_pZ$  and its perpendicular to  $T_pG \circ p$ .

Remember we have  $d\pi: M_{st} \to M_{red} = M_{st}/G_{\mathbb{C}}$  is a holomorphic action.

So  $d\pi_p: V \to T_q M_{red}$  is  $\mathbb{C}$ -linear and  $\omega_p \mid V = (d\pi_p)^* \omega_{red} \mid_V$ , where V a complementary subspace of  $T_pM$  so  $\omega_p$  | is Kaehler implies that  $(\omega_{red})_q$  is Kaehler.

#### Lecture 34

Let G be an n-dimensional compact connected abelian Lie group. Let  $\mathfrak{g}$  be the Lie algebra of G.

For an abelian Lie group  $\exp: \mathfrak{g} \to G$  is a group epi-morphism and  $\mathbb{Z}_G = \ker \operatorname{exp}$  is called the **group** lattice of G. Since  $\exp$  is an epi-morphisms,  $G = \mathfrak{g}/\mathbb{Z}_G$ . So we can think of  $\exp: \mathfrak{g} \to G$  as a projection  $\mathfrak{g} \to \mathfrak{g}/\mathbb{Z}_G$ .

#### Representations of G

We introduce the dual lattice  $\mathbb{Z}_G^* \subseteq \mathfrak{g}^*$  a weight lattice, with  $\alpha \in \mathfrak{g}^*$  in  $\mathbb{Z}_G^*$  if and only if  $\alpha(v) \in 2\pi\mathbb{Z}$  for all  $v \in \mathbb{Z}_G$ . Suppose we're given  $\alpha_i \in \mathbb{Z}^a st_G$ , i = 1, ..., d. We can define a homomorphism  $\tau : G \to GL(d, \mathbb{C})$  by

(I) 
$$\tau(\exp v)z = (e^{\sqrt{-1}\alpha_1(v)}z_1, \dots, e^{\sqrt{-1}\alpha_d(v)}z_d)$$

and this is well-defined, because if  $v \in \mathbb{Z}_G$ ,  $\tau(\exp v) = 1$ . But think of  $\tau$  as an action of G on  $\mathbb{C}^d$ . We get a corresponding infinitesimal actions

$$d\tau: \mathfrak{g} \to \mathcal{X}(G)$$
  $v \mapsto v_{\mathbb{C}^d}$   $d\tau(\exp -tv) = \exp tv_{\mathbb{C}^d}.$ 

We want a formula for this. We introduce the coordinates  $z_i = x_i + \sqrt{-1}y_i$ . We claim

$$(II) v_{\mathbb{C}}d = -\sum_{i} \alpha_{i}(v) \left( x_{i} \frac{\partial}{\partial y_{i}} - y_{i} \frac{\partial}{\partial x_{i}} \right).$$

We must check that for each coordinate  $z_i$ 

$$\frac{d}{dt}(\tau_{\exp -tv})^* z_i \bigg|_{t=0} = L_{v_{\mathbb{C}^d}} z_i.$$

The LHS is

$$\frac{d}{dt}e^{-\sqrt{-1}t\alpha_i(V)}z_i = -\alpha_i(v)z_i$$

and the RHS is

$$\left(x_i \frac{\partial}{\partial y_i} - y_i \frac{\partial}{\partial x_i}\right) (x_i + \sqrt{-1}y_i) = \sqrt{-1}z_i$$

SO

$$L_{v_{\mathbb{C}^d}} z_i = \sqrt{-1}\alpha_i(v)z_i$$

Take  $\omega$  to be the standard kaehler form on  $\mathbb{C}^d$ 

$$\omega = \sqrt{-1} \sum dz_i \wedge d\bar{z}_i = 2 \sum dx_i \wedge dy_j$$

**Theorem.**  $\tau$  is a Hamiltonian action with moment map

$$\Phi:\mathbb{C}^d\to\mathfrak{g}^*$$

where

$$\Phi(z) = \sum |z_i|^2 dz_i$$

Proof.

$$\iota(v_{\mathbb{C}^d})\omega = \left(-\sum \alpha_i(v)\left(x_i\frac{\partial}{\partial y_i} - y_i\frac{\partial}{\partial x_i}\right)\right) - \sum dx_i \wedge dy_i$$

$$= 2\sum \alpha_i(v)x_idx_i + y_idy_i = \sum \alpha_i(v)d(x_i^2 + y_i^2)$$

$$= d\sum \alpha_i(v)|z_i|^2 = d\langle\Phi,v\rangle$$

N.B.  $\Phi(0) = 0$ ,  $0 \in (\mathbb{C}^d)^G$  implies that  $\Phi$  is an equivariant moment map.

**Definition.**  $\alpha_1, \ldots, \alpha_d$  are said to be polarized if for all  $v \in \mathfrak{g}$  we have  $\alpha_i(v) > 0$ .

**Theorem.** If  $\alpha_1, \ldots, \alpha_d$  are polarized then  $\Phi : \mathbb{C}^d \to \mathfrak{g}^*$  is proper.

*Proof.* The map  $\langle \Phi, v \rangle : \mathbb{C}^d \to \mathbb{R}$  is already proper if  $\alpha_i(v) > 0$ , so the moment map itself is proper.

Now, given  $z \in \mathbb{C}^d$ , what can be said about  $G_z$  and  $\mathfrak{g}_z$ ?

Notation.  $I_z = \{i, z_i \neq 0\}$ 

**Theorem.** (a)  $G_z = \{ \exp v \mid \alpha_i(v) \in 2\pi \mathbb{Z} \text{ for all } i \in I_z \}$ 

(b) 
$$\mathfrak{g}_z = \{ v \mid \alpha_i(v) = 0 \text{ for all } i \in I \}$$

Corollary.  $\tau$  is locally free at z if and only if  $span_{\mathbb{R}}\{\alpha_i, i \in I_z\} = \mathfrak{g}^*$ .  $\tau$  is free at z if and only if  $span_{\mathbb{Z}}\{\alpha_i, i \in I_z\} = \mathbb{Z}_G^*$ .

Let  $a \in \mathfrak{q}^*$ . Is a a regular value of  $\Phi$ .

Notation.

$$\mathbb{R}_{+}^{d} = \{ (t_{1}, \dots, t_{d}) \in \mathbb{R}^{d}, t_{i} \geq 0 \}$$

$$I \subset \{1, \dots, d\} \qquad (\mathbb{R}_{+}^{d})_{I} = \{ t \in \mathbb{R}_{+}^{d}, t_{i} > 0 \Leftrightarrow i \in I \}$$

Consider  $L: \mathbb{R}^d_+ \to \mathfrak{g}^*$ 

$$L(t) = \sum t_i \alpha_i$$

Assume  $\alpha_i$ 's are polarized. L is proper. Take  $a \in \mathfrak{g}^*$ . Let  $\Delta_a = L^{-1}(a)$ , then  $\Delta_a$  is a convex polytope. Denote  $\mathcal{I}_{\Delta_a} = \{I, (\mathbb{R}^d_+)_I \cap \Delta_a \neq \emptyset\}$ . For  $I \in \mathcal{I}_{\Delta}$  we have that  $(\mathbb{R}^d_+)_I \cap \Delta =$  the faces of  $\Delta$ .

**Theorem.**  $a \in \mathfrak{g}^*$  is a regular value of  $\Phi$  if and only if for all  $I \in \mathcal{I}_{\Delta_a}$  we have  $span_{\mathbb{R}}\{a_i, i \in I\} = \mathfrak{g}^*$  and G acts freely on  $\Phi^{-1}(a)$  if and only if  $span_{\mathbb{Z}}\{a_i, i \in I\} = \mathbb{Z}_G^*$ .

*Proof.*  $\Phi$  is the composite of  $L: \mathbb{R}^d_+ \to \mathfrak{g}^*$  and the map  $\gamma: \mathbb{C}^d \to \mathbb{R}^d_+$  which maps  $z \mapsto (|z_1|^2, \dots, |z_d|^2)$  so  $z \in \Phi^{-1}(a)$  if an only if  $\gamma(z) \in \Delta_a$ . How just apply above.

#### Symplectic Reduction

Take  $a \in \mathfrak{g}^*$ . Suppose a is a regular value of  $\Phi$ , i.e.  $\mathfrak{g}_z = \{0\}$  for all  $z \in \Phi^{-1}(a)$ . Then  $\mathbb{Z}_a = \Phi^{-1}(a)$  is a compact submanifold of  $\mathbb{C}^d$ .

Suppose G acts freely on  $Z_a$ . Then  $M_a = Z_a/G$ . Consider  $i: Z_a \to \mathbb{C}, \pi: Z_a \to M_a$ .

**Theorem.** There exists a unique symplectic form  $\omega_a$  on  $M_a$  such that  $\pi^*\omega_a = i^*\omega_a$ .

*Proof.* Apply the symplectic quotient procedure to  $\Phi^{-1}(a)$ .

Let  $G_{\mathbb{C}} = \mathfrak{g}_{\mathbb{C}}/\mathbb{Z}_G = \mathfrak{g} \otimes \mathbb{C}/\mathbb{Z}_g$ . By (I),  $\tau$  extends to a holomorphic action of  $G_{\mathbb{C}}$  on  $\mathbb{C}^d$ . Then

$$G_{\mathbb{C}} \cdot \Phi^{-1}(a) = \{ \tau_q(z) \mid g \in G_{\mathbb{C}}, z \in Z_a \} = \mathbb{C}_{\text{stable}}^d(a)$$

then  $M_a = \mathbb{C}^d_{\mathrm{stable}}(a)/G_{\mathbb{C}}$  = the holomorphic description of  $M_a$ .  $\omega_a$  is Kaehler. This  $M_a$  is a toric variety.

Theorem.

$$\mathbb{C}^d_{stable}(a) = \bigcup_{I \in \mathcal{I}_{\Delta}} \mathbb{C}^d_I$$

where

$$\mathbb{C}_I^d = \{ z \in \mathbb{C}^d \mid I_z = I \}$$

#### Lecture 35

Let G be a compact connected Lie group and  $n=\dim G$ , with Lie algebra  $\mathfrak{g}$ . We have a group lattice  $\mathbb{Z}_G\subset\mathfrak{g}$ , and the dual  $\mathbb{Z}_G^*\subset\mathfrak{g}^*$  the weight lattice. Then  $G=\mathfrak{g}/\mathbb{Z}_G$ . We can define  $\exp:\mathfrak{g}\to\mathfrak{g}/\mathbb{Z}_G$ . Take elements  $\alpha_i\in\mathbb{Z}_G^*$ ,  $i=1,\ldots,d$  then we get a representation  $\tau:G\to GL(d,\mathbb{C})$  given by

$$\tau(\exp v)z = (e^{\sqrt{-1}\alpha_1(v)}z_1, \dots, e^{\sqrt{-1}\alpha_d}z_d).$$

We can think of  $\tau$  as an action. As such it preserves the Kaehler form

$$\omega = \sqrt{-1} \sum dz_i \wedge d\bar{z}_i$$

In fact,  $\tau$  is Hamiltonian with momen t map

$$\Phi: \mathbb{C}^d \to \mathfrak{g}^*, \qquad \Phi(z) = \sum |z_i|^2 \alpha_i$$

Note that  $\alpha_1, \ldots, \alpha_d$  are polarized if and only if there exists a  $v \in \mathfrak{g}$  such that  $\alpha_i(v) > 0$  for all i.

**Theorem.**  $\alpha_i s$  are polarized if and only if  $\Phi$ , the moment map, is proper.

What are the regular values of  $\Phi$ ?

Let

$$\mathbb{R}_{+}^{d} = \{(t_1, \dots, t_d) \in \mathbb{R}^d, t_i \ge 0\}$$

and take  $I \subseteq \{1, \ldots, d\}$ .

Notation.  $\mathbb{R}^d_I = \{t \in \mathbb{R}^d, t_i \neq 0 \Leftrightarrow i \in I\}$ 

Consider the following maps:  $L: \mathbb{R}^d \to \mathfrak{g}^*$  given by

$$t \mapsto \sum t_i \alpha_i$$

and  $\gamma: \mathbb{C}^d \to \mathbb{R}^d_+$  given by

$$z \mapsto (|z_1|^2, \dots, |z_n|^2).$$

Then for any  $a \in \mathfrak{g}^*$ , let  $\Delta_a = L^{-1}(a) \cap \mathbb{R}^d_+$ . Then  $\Phi = L \circ \gamma$ , so  $z \in \Phi^{-1}(a)$  if and only if  $\gamma(z) \in \Delta_a$ . Suppose that the  $\alpha_i$ s are polarized. Then  $\Delta_a$  is a compact convex set, and in fact it is a **convex polytope** 

**Definition.** The index set of a polytope is defined to be

$$\mathcal{I}_{\Delta_a} = \{ I \mid \mathbb{R}^d_I \cap \Delta_a \neq 0 \}$$

The faces of the polytope  $\Delta_a$  are the sets

$$\Delta_I = \Delta_a \cap \mathbb{R}^d_I, \qquad I \in \mathcal{I}_\Delta$$

Theorem (1). Let  $a \in \mathfrak{g}^*$ . Then

(a) a is a regular value of  $\Phi$  if and only if for every  $I \in \mathcal{I}_{\Delta_a}$ 

$$span_{\mathbb{R}}\{a_i, i \in I\} = \mathfrak{g}^*$$

(b) G acts freely on  $\Phi^{-1}(a)$  if and only if for all  $I \in \mathcal{I}_{\Delta_a}$ 

$$span_{\mathbb{Z}}\{a_i, i \in I\} = \mathbb{Z}_G^*$$

 $\mathcal{I}_{\Delta}$  is partially order by inclusion, i.e.  $I_1 < I_2$  if  $I_1 \subseteq I_2$ .  $I \in \mathcal{I}_{\Delta}$  is minimal iff the corresponding face  $\Delta_I$  is a vertex of  $\Delta_a$ , i.e.  $\Delta_I = \{v_I\}$  where  $v_I$  is a vertex of  $\Delta_a$ .

**Theorem (2).** (a) a is a regular value of the moment map  $\Phi$  if and only if for every vertex  $v_I$  of  $\Delta_a$ ,  $\alpha_i, i \in I$  are a basis of  $\mathfrak{g}^*$ .

(b) G acts freely on  $\Phi^{-1}(a)$  if and only if for every vertex  $v_I$  of  $\Delta_a$ ,  $\alpha_i, i \in I$  are a lattice basis for  $\mathbb{Z}_G^*$ .

*Proof.* In **Theorem 1** it suffices to check a) and b) for the minimal elements I of  $\mathcal{I}_{\Delta}$ .

Check that a) of Thm. 1 implies b) of Thm 2. So we just have to check a) of Thm. 2. Let  $\Delta_I = \{v_I\}$ , where I is a minimal element of  $\mathcal{I}_{\Delta}$ . By Thm 1., span $\{\alpha_i, i \in I\} = \mathfrak{g}^*$ . Suppose  $\alpha_i$ s are not a basis, then there exist  $c_i$  so that

$$\sum_{i \in I} c_i \alpha_i = 0$$

Now,  $v_I = (t_1, \ldots, t_d), t_i > 0$  for  $i \in I$  and  $t_i = 0$  for  $i \notin I$ . Define  $(s_1, \ldots, s_d) \in \Delta_a$  by

$$s_i = \begin{cases} t_i + \epsilon c_i & i \in I \\ 0 & i \notin I \end{cases}$$

Then  $L(s) = a, s \in \Delta_I$ , so this contradicts that  $\Delta_I$  is a singular point.

**Notation.**  $\Delta \in \mathbb{R}^d$  a convex polytope,  $v, v' \in Vert(\Delta)$ . Then v and v' are adjacent if they lie on a common edge of  $\Delta$ .

**Definition.** An m-dimensional polytope  $\Delta$  is simple if for every vertex v there are exactly m vertices adjacent to it.

[Next time we'll show that a is a regular value of  $\Phi$  iff  $\Delta_a$  is simple]

**Example.** A tetrahedron or a cube in  $\mathbb{R}^3$ . A pyramid is not simple.

 $\Phi: \mathbb{C}^d \to \mathfrak{g}^*$ , and a regular value. G acts freely on  $Z_a = \Phi^{-1}(a)$ . Then we can form the symplectic quotient  $M_a = \Phi^{-1}(a)/G$ , which is a compact Kaehler manifold. We want to compute the de Rham and Dolbeault cohomology groups,  $H_{DR}^*(M_a)$ ,  $H_{Do}^*(M_a)$ . To compute the de Rham cohomology we're going to use Morse Theory.

#### A Digression on Morse Theory

Let  $M^m$  be a compact  $C^{\infty}$  manifold and let  $f: M \to \mathbb{R}$  be a smooth function.

 $p \in \mathbf{Crit}(f)$  if and only if  $df_p = 0$  (by definition). For any  $p \in \mathbf{Crit}(f)$  we have the Hessian  $d^2f_p$  a quadratic form on  $T_p$ . Let  $(U, x_1, \ldots, x_n)$  be a coordinate patch centered at p. Then

$$f(x) = c + \sum a_{ij}x_ix_j + O(x^3) = d^2f_p + O(x^3)$$

and p is called non-degenerate if  $d^2f_p$  is non-degenerate. If p is a non-degenerate critical point, then p is

**Definition.** f is Morse if all  $p \in Crit(f)$  are non-degenerate, which implies that

$$\#\operatorname{Crit}(f) < \infty$$

**Definition.**  $p \in \operatorname{Crit}(f)$  then  $\operatorname{ind} p = \operatorname{ind} d^2 f_p$ , i.e. if

$$d^2 f_p = -(x_1^2 + \dots + x_k^2) + x_{k+1}^2 + \dots + x_m^2$$

then ind  $d^2 f_p = k$ .

**Theorem.** Let  $f: M \to \mathbb{R}$  be a Morse function with the property tat ind p is even for all  $p \in Crit(f)$ . Then

$$H^{2k+1}(M) = 0$$
  $H^{2k}(M) = \{ p \in Crit(f), \text{ ind } p = 2k \}$ 

#### **Back to Symplectic Reduction**

Again, we're talking about the moment map  $\Phi: \mathbb{C}^d \to \mathfrak{g}^*$ , with a a regular value of  $\Phi$ . G acts freely on  $Z_a$  and let  $M_a = Z_a/G$ . Then we have the following diagram:

$$Z_a \xrightarrow{i} \mathbb{C}^n$$

$$\downarrow^{\pi}$$

$$M_a$$

and the mapping  $\gamma: \mathbb{C}^d \to \mathbb{R}^d_+, z \mapsto (|z_1|^2, \dots, |z_d|^2)$ .  $\gamma$  is G-invariant.

This implies that there exists  $\psi: M_a \to \mathbb{R}^d_+$  with the property that  $\psi \circ \pi = \gamma \circ i$ . Moreover  $\gamma: Z_a \to \Delta_a$ . So  $\psi: M_a \to \Delta_a$ ,  $\Delta_a$  is called the moment polytope.

Now take  $\xi \in \mathbb{R}^d$  and let  $f: M_a \to \mathbb{R}$  be  $f(p) = \langle \psi(p), \xi \rangle$ , i.e.  $\pi^* f = i^* f_0$  where

$$f_0(z) = \sum \xi_i |z_i|^2$$

Theorem (Main Theorem). Assume for  $v, v' \in Vert(\Delta_a)$ , v, v' adjacent that

$$\langle v - v', \xi \rangle \neq 0$$

then

- (a)  $f: M_a \to \mathbb{R}$  is Morse
- (b)  $\psi: M_a \to \Delta_a \ maps \ Crit(f) \ bijectively \ onto \ Vert(\Delta_a)$ .
- (c) For  $p \in Crit(f)$  and v the corresponding vertex let  $v_1, \ldots, v_m$  be the vertices adjacent to v. Then

$$\frac{ind_p}{2} = \#\{v_i \mid \langle v_i - v, \xi \rangle < 0\} := ind_v \xi$$

Corollary.  $H^{2k+1}(M_a) = 0$  then

$$b_k = H^{2k}(M_a) = \#\{v \in Vert(\Delta_a), ind_v \xi = k\}$$

that is,  $b_k$  is independent of  $\xi$ .

#### Lecture 36

Let G be an n-torus, and  $\alpha_1, \ldots, \alpha_d \in \mathbb{Z}_G^*$ . Define a Hamiltonian action  $\tau$  of G on  $\mathbb{C}^d$  as follows. First we have

$$L: \mathbb{R}^d \to \mathfrak{g}^*$$
  $L(t) = \sum t_i \alpha_i$ 

and

$$\gamma: \mathbb{C}^d \to \mathbb{R}^d \qquad \gamma(z) = (|z_1|^2, \dots, |z_d|^2)$$

then  $\Phi = L \circ \gamma$  is the moment map of  $\tau$ . As before, we're interested in the regular values of  $\Phi$ . Define  $\Delta_a = L^{-1}(a) \cap \mathbb{R}^d_+$  a convex polytope.

**Theorem (1).** a is a regular value if  $\Delta_a$  is a simple n-dimensional.

For a regular call  $Z_a = \Phi^{-1}(a)$ . Assume G acts freely on  $Z_a$ . we have  $M_a = Z_a/G$ .

$$Z_a \xrightarrow{i} \mathbb{C}^a$$

$$\downarrow^{\psi}$$

$$M_a$$

$$\psi: M_a \to \mathbb{R}^d$$
 and  $\psi \circ \pi = \gamma \circ i$ .  
 $Z_a = \gamma^{-1}(\Delta_a)$  implies that  $\psi(M_a) = \Delta_a$ .

#### **Definition.** $\Delta_a$ is called the moment polytope

For  $\xi \in \mathbb{R}^d$ , let  $f = \langle \psi, \xi \rangle$  and  $\pi^* f = i^* f_0$  where

$$f_0(z) = \sum_{i=1}^d \xi_i |z_j|^2$$

**Theorem (2).** Suppose that for all adjacent v, v' of  $\Delta_a$  we have  $\langle v - v', \xi \rangle \neq 0$ . Then

- (a) f is Morse
- (b)  $\psi$  maps Crit(f) bijectively onto  $Vert(\Delta_a)$ .
- (c) For  $q \in Crit(f)$  ind<sub>q</sub> = ind<sub>\xi</sub> v where  $v = \psi(a)$  and the index ind<sub>v</sub>\xi is given by

$$ind_v xi = \{v_k \mid \langle v_k - v, \xi \rangle < 0\}$$

where the  $v_k$ 's are vertices adjacent to v.

 $I \subseteq \{1, \ldots, d\}$  then  $t \in \mathbb{R}^d_I$  if and only if  $t_i \neq 0$  if and only if  $i \in I$ . For  $\Delta = \Delta_a$ 

$$\mathcal{I}_{\Delta} = \{I, \mathbb{R}^d_I \cap \Delta \neq \emptyset\}$$

For  $I \in \mathcal{I}_{\Delta}$ ,  $\Delta_I = \mathbb{R}^d_I \cap \Delta =$  faces of the polytope  $\Delta$ . Recall also that there is a partial ordering  $I_1 \leq I_2$  if and only if  $I_1 \subseteq I_2$ . For I minimal  $\Delta_I = \{v_I\}$ 

**Theorem.** a is a regular value if and only if for every vertex  $v_I$  of  $\Delta_a$ ,  $\alpha_i$ ,  $i \in I$  form a basis of  $\mathfrak{g}^*$ .

Let  $v_I \in Vert(\Delta_a)$ . Relabel I = (1, 2, ..., n) so that  $\alpha_1, ..., \alpha_n$  are a basis for  $\mathfrak{g}^*$ ,  $a = \sum_{i=1}^n a_i \alpha_i, L(v_I) = \sum_{i=1}^n a_i \alpha_i$  $a. \ v_I = (a_1, \dots, a_n, 0, \dots, 0) \text{ and for } k > n,$ 

$$\alpha_k = \sum a_{k,i} \alpha_i$$

Rewrite

$$L(t) = \sum_{i=1}^{n} \left( t_i - \sum_{k>n} a_{k,i} t_k \right) \alpha_i = \sum_{k>n} a_i \alpha_i = a$$

From this we conclude that  $\Delta_a$  is defined by

$$(I) \begin{cases} t_i = a_i = \sum a_{k,i} t_k \\ t_1, \dots, t_d \ge 0 \end{cases} .$$

We see immediately tat  $\Delta_a$  is m-dimensional, m=d-n. The edges of  $\Delta_a$  at  $v_I$  lie along the rays  $v_I+se_k$ ,  $k = n + 1, \dots, d \text{ for } s \ge 0.$ 

**Exercise** Check that  $e_k = (-a_{k,1}, \ldots, a_{k,n}, 0, \ldots, 1, \ldots, 0)$  where the 1 is in the kth slot. The conclusion is that  $\Delta_a$  is simple at  $v_I$  so  $\Delta_a$  is simple.

Let  $v = v_I$  be a vertex of  $\Delta_a$ . Write

$$\mathcal{O}_v = \{t \in \Delta_a, t_i > 0 \text{ if } i \in \} = \bigcup J \ge I\Delta_I.$$

Consider  $\gamma^{-1}(\mathcal{O}_v)$ . These are open G-invariant sets in  $Z_a$ 

Take  $\mathcal{U}_v = \pi(\gamma^{-1}(\mathcal{O}_v))$  an open cover of  $M_a$ . Let  $f: M_a \to \mathbb{R}$ . What does f look like on  $f|_{\mathcal{U}_v}$ . Take  $I = (1, \ldots, n)$  by relabeling. Then

$$a = \sum_{i=1}^{n} a_i \alpha_i$$
  $v_I = (a_1, \dots, a_n, 0, \dots, 0)$ 

then

$$z \in \gamma^{-1}(v_I) \iff \begin{cases} |z_i|^2 = a_i & i = 1, \dots, n \\ z_k = 0 & k > n \end{cases}$$

**Proposition.**  $\gamma^{-1}(v_I)$  is a single G-orbit.

*Proof.* dim  $\gamma^{-1}(v) = n$ , dim G = n and G acts freely on  $\gamma^{-1}(v)$ . More generally,  $z \in Z_a$  if and only if  $\gamma(z) \in \Delta_a$ . Hence by (I)  $\mathcal{O}_v$  is defined by

$$|z_i|^2 = a_i - \sum a_{k,i} |z_k|^2$$

and  $z_i \neq 0$ ,  $i = 1, \dots, n$ . Take  $f_0 = \sum \xi_j |z_j|^2$  then (\*)

$$i^*f_0 = c + \sum_{k>n} \left(\xi_k - \sum a_{k,i}\xi_i\right) |z_k|^2$$
 
$$= c + \sum_{k>n} \langle e_k, \xi \rangle |z_k|^2 = \pi^*f$$

where  $e_k$  is defined as before.

Proof of Theorem 2. From (\*) the only critical point of f on  $\mathcal{U}_v$  is  $a = \pi(\gamma^{-1}(v))$ .(Recall  $\gamma^{-1}(v)$  is a single G-orbit).

Moreover  $\psi(a) = v_I$ . Finally if  $p \in \gamma^{-1}(v)$ , then

$$(d\pi)_p^*(d^2f_a) = \sum_{k>n} \langle e_k, \xi \rangle |z_k|^2 = \sum_{k>n} \langle e_k, \xi \rangle (x_k^2 + y_k^2)$$

It follows that  $(d^2f_a)$  is (...), and the index is  $2\operatorname{ind}_{\xi}v$ .

Also a consequence

$$H^{2k+1}(M_a) = 0$$

SO

$$b_k = \dim H^{2k}(M_a) = \#\{Vert(\Delta_a), \operatorname{ind}_{\xi} v = k\}$$

and  $b_k = \#\{ \inf_x iv = v \}$  doesn't depend on  $\xi$ . If  $f_k$  is the number of k-dimensional faces of  $\Delta_a$  for  $k = 0, \ldots, m$  then

$$f_{m-k} = {m \choose k} b_0 + {m-1 \choose k-1} b_1 + \dots + b_k$$

**Exercise** Prove this.

Let  $\Delta$  be a simple *m*-dimensional convex polytope and  $f_k$  be the number of *k*-dimensional faces of  $\Delta$ . Define  $b_0, \ldots, b_n$  by the solutions to the equations

$$f_{m-k} = \binom{m}{k} b_0 + \dots b_k$$

Then

Theorem (McMullen, Stanley). (a) The  $b_k s$  are integers.

- $(b) b_{m-k} = b_k$
- (c)  $b_0 \leq b_1 \leq \cdots \leq b_k$  where  $k = \left\lceil \frac{m}{2} \right\rceil$ .

*Proof.* Exhibit  $\Delta$  as the moment polytope of a toric variety of M.

- (a) The  $b_k$ s are Betti numbers of M (so integers)
- (b) Poincare duality
- (c) Hard Lefschetz.