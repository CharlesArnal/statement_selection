MIT OpenCourseWare <http://ocw.mit.edu>

18.950 Differential Geometry Fall 2008

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

# CHAPTER 2

# Local geometry of hypersurfaces

Background from linear algebra: A symmetric bilinear form on  $\mathbb{R}^n$  is a map  $I: \mathbb{R}^n \times \mathbb{R}^n \to \mathbb{R}$  of the form  $I(x,y) = \sum_{ij} x_i a_{ij} y_j$ , where  $a_{ij} = a_{ji}$ . Equivalently,  $I(x,y) = \langle x, Ay \rangle$ , where A is a symmetric matrix. We say that I is an inner product if I(x,x) > 0 for all nonzero x, or equivalently if A is positive definite.

Suppose from now on that I is an inner product. A basis  $(e_1, \ldots, e_n)$  is called orthogonal with respect to I if

$$I(e_i, e_i) = 1$$
,  $I(e_i, e_i) = 0$  for  $i \neq j$ .

Such bases always exist. In particular, by passing from the standard basis to the basis given by such vectors, one reduces standard about I to ones about the standard inner product  $\langle \cdot, \cdot \rangle$ . A linear map  $L : \mathbb{R}^n \to \mathbb{R}^n$  is called selfadjoint with respect to I if I(x, Ly) is a symmetric bilinear form. Equivalently, this is the case iff AL is symmetric, which means that

$$AL = L^{tr}A$$
.

Such a matrix L always has a basis of eigenvectors, which is an orthogonal basis with respect to I.

Background from multivariable calculus: the derivative or Jacobian of a smooth map  $f: \mathbb{R}^m \to \mathbb{R}^n$  at a point x is a linear map  $Df_x: \mathbb{R}^m \to \mathbb{R}^n$ . In terms of partial derivatives,

$$Df_x(X) = (\sum_j \partial_{x_j} f_1 \cdot X_j, \sum_j \partial_{x_j} f_2 \cdot X_j, \dots).$$

The chain rule is  $D(f \circ g)_x = Df_{g(x)} \cdot Dg_x$ , where the right hand side is matrix multiplication. The second derivative is a symmetric bilinear map  $D^2 f_x : \mathbb{R}^m \times \mathbb{R}^m \to \mathbb{R}^n$  (for n = 1, this is a symmetric bilinear form, called the Hessian of the function f). Again explicitly,

$$D^{2}f_{x}(X,Y) = (\sum_{i,j} \partial_{x_{i}x_{j}}^{2} f_{1} \cdot X_{i}Y_{j}, \sum_{i,j} \partial_{x_{i}x_{j}}^{2} f_{2} \cdot X_{i}Y_{j}, \dots).$$

DEFINITION 12.1. A hypersurface patch is a smooth map  $f: U \to \mathbb{R}^{n+1}$ , where  $U \subset \mathbb{R}^n$  is an open subset, such that the derivatives  $\partial_{x_1} f, \ldots, \partial_{x_n} f \in \mathbb{R}^{n+1}$  are linearly independent at each point x. Equivalently, the Jacobian  $Df_x: \mathbb{R}^n \to \mathbb{R}^{n+1}$  is injective (one-to-one).

DEFINITION 12.2. Let f be a hypersurface patch. There is a unique  $\nu: U \to \mathbb{R}^{n+1}$  such that  $\nu(x)$  is of length one, is orthogonal to  $\partial_{x_1} f, \ldots, \partial_{x_n} f$ , and satisfies  $\det(\partial_{x_1} f, \ldots, \partial_{x_n} f, \nu(x)) > 0$ . It is automatically smooth. We call  $\nu(x)$  the Gauss normal vector of f at the point x.

Like in Frenet theory, we have an explicit formula. First, define N by

$$N_i = \det(\partial_{x_1} f, \dots, \partial_{x_n} f, \underbrace{(0, \dots, 1, \dots, 0)}_{i-\text{th unit vector}}).$$

Then  $\nu = N/\|N\|$ . For a curve in  $\mathbb{R}^2$ , this simplifies to  $\nu = Jf'/\|f'\|$ . For a surface in  $\mathbb{R}^3$ ,  $N = \partial_{x_1} f \times \partial_{x_2} f$ , hence

$$\nu = \partial_{x_1} f \times \partial_{x_2} f / \|\partial_{x_1} f \times \partial_{x_2} f\|.$$

DEFINITION 12.3. Define  $G_{ij}(x) = \langle \partial_{x_i} f, \partial_{x_j} f \rangle$ . Equivalently, the matrix with entries  $G_{ij}(x)$  is  $G_x = Df_x^{tr} \cdot Df_x$ . The associated inner product,  $I_x(X,Y) = \langle X, G_x Y \rangle = \langle Df_x(X), Df_x(Y) \rangle$ , is called the *first fundamental form*.

DEFINITION 12.4. Define  $H_{ij}(x) = -\langle \partial_{x_i} \nu, \partial_{x_j} f \rangle = \langle \partial_{x_i} \partial_{x_j} f, \nu(x) \rangle$ . Equivalently, the matrix with entries  $H_{ij}(x)$  is  $H_x = -D\nu_x^{tr} \cdot Df_x$ . The associated symmetric bilinear form,  $H_x(X,Y) = \langle X, H_xY \rangle = -\langle D\nu_x(X), Df_x(Y) \rangle = \langle \nu(x), D^2 f_x(X,Y) \rangle$ , is called the second fundamental form.

DEFINITION 12.5. Define a matrix  $L_x$  by  $L_x = G_x^{-1}H_x = (H_xG_x^{-1})^{tr}$ . We call this the *shape operator*. Equivalently, this is characterized by the property that

$$II_x(X,Y) = I_x(L_xX,Y).$$

LEMMA 12.6.  $D\nu = -Df \cdot L$  (matrix multiplication). More explicitly, each partial derivative  $\partial_{x_i}\nu$  lies in the linear span of  $\{\partial_{x_1}f,\ldots,\partial_{x_n}f\}$ , and the shape operator allows us to express it as a linear combination of these vectors:

$$\partial_{x_i} \nu = -\sum_j L_{ji}(x) \partial_{x_j} f.$$

EXAMPLE 12.7. Suppose that f(x) = (x, h(x)), where h is a smooth function of n variables. Let  $p \in U$  be a point where h and Dh both vanish. At that point,  $G = \mathbf{1}$  is the identity matrix, and H (as well as L) is the Hessian  $D^2h$ .

Here's a summary. Let  $f: U \to \mathbb{R}^{n+1}$  be a hypersurface patch, and  $\nu: U \to \mathbb{R}^{n+1}$  its Gauss map. We then get:

| coefficients | matrix                                           | bilinear form                                                                                                           |
|--------------|--------------------------------------------------|-------------------------------------------------------------------------------------------------------------------------|
|              | $G = Df^{tr} \cdot Df$ $H = -D\nu^{tr} \cdot Df$ | $I(X,Y) = \langle Df(X), Df(Y) \rangle$ $II(X,Y) = -\langle D\nu(X), Df(Y) \rangle$ $= \langle \nu, D^2 f(X,Y) \rangle$ |
| $L_{ij}$     | $L = G^{-1}H = (HG^{-1})^{tr}$                   |                                                                                                                         |

Let  $U, \tilde{U}$  be open subsets of  $\mathbb{R}^n$ , and  $\phi: \tilde{U} \to U$  a smooth map such that  $\det(D\phi) > 0$  everywhere. If  $f: U \to \mathbb{R}^{n+1}$  is a regular hypersurface, then so is  $\tilde{f} = f \circ \phi: \tilde{U} \to \mathbb{R}^{n+1}$ , which we call a partial reparametrization of f.

Proposition 13.1. The coordinate changes for the main associated data are

$$\begin{split} \tilde{\nu}(x) &= \nu(\phi(x)), \\ \tilde{G}(x) &= D\phi(x)^{tr} \cdot G(\phi(x)) \cdot D\phi(x), \\ \tilde{H}(x) &= D\phi(x)^{tr} \cdot H(\phi(x)) \cdot D\phi(x), \\ \tilde{L}(x) &= D\phi(x)^{-1} \cdot L(\phi(x)) \cdot D\phi(x). \end{split}$$

All the structures above are obtained by differentiating f. It is interesting to ask to what extent they can be integrated back to determine the hypersurface itself.

EXAMPLE 13.2. Let  $f: U \to \mathbb{R}^{n+1}$  be a hypersurface patch such that L is 1/R times the identity matrix, for some  $R \neq 0$ . Then  $f + R\nu$  is constant, and therefore, the image f(U) is contained in a radius |R| sphere in  $\mathbb{R}^{n+1}$ .

PROPOSITION 13.3. Let  $f, \tilde{f}: U \to \mathbb{R}^{n+1}$  be two hypersurface patches, defined on the same *connected* set  $U \subset \mathbb{R}^n$ . Suppose that their first and second fundamental forms coincide. Then  $\tilde{f}(x) = Af(x) + c$ , where A is an orthogonal matrix with determinant +1, and c some constant.

By definition  $L_x$  is selfadjoint with respect to the inner product  $I_x$ . Hence, it has a basis of eigenvectors which are orthonormal with respect to  $I_x$ . Note that X is an eigenvector of  $L_x$  iff  $H_xX = \lambda G_xX$ . Hence, the eigenvalues  $\lambda$  are the solutions of  $\det(G - \lambda H) = 0$ .

DEFINITION 14.1. The eigenvalues  $(\lambda_1, \ldots, \lambda_n)$  of  $L_x$  are called the *principal* curvatures of the hypersurface patch f at x. The corresponding eigenvectors  $(X_1, \ldots, X_n)$  are called the *principal* curvature directions.

If  $\tilde{f} = f(\phi)$  is a partial reparametrization of f, then the principal curvatures of  $\tilde{f}$  at x are equal to the principal curvatures of f at  $\phi(x)$ .

EXAMPLE 14.2. Suppose that f is such that  $f_1$  achieves its maximum at the point p. Then  $\nu(p) = (\pm 1, 0, \dots, 0)$ . In the + case, all principal curvatures at p are  $\leq 0$ . In the - case, all principal curvatures at p are  $\geq 0$ .

EXAMPLE 14.3. Suppose that f is such that ||f|| achieves its maximum at the point p, where ||f(p)|| = R. Then  $\nu(p) = \pm f(p)/||f(p)||$ . In the + case, all principal curvatures at p are  $\leq -1/R < 0$ . In the - case, all principal curvatures at p are  $\geq 1/R > 0$ .

DEFINITION 14.4. Let  $\lambda_1, \ldots, \lambda_n$  be the principal curvatures of f at x. The mean curvature is

$$\kappa_{mean} = \lambda_1 + \dots + \lambda_n = \text{trace}(L).$$

The Gauss curvature is

$$\kappa_{qauss} = \lambda_1 \cdots \lambda_n = \det(L) = \det(H) / \det(G).$$

The scalar curvature is

$$\kappa_{scalar} = \sum_{i < j} \lambda_i \lambda_j = \frac{1}{2} (\operatorname{trace}(L)^2 - \operatorname{trace}(L^2)).$$

Lemma 14.5. The Gauss curvature is

$$\kappa_{gauss} = (-1)^n \frac{\det(\partial_{x_1} \nu, \dots, \partial_{x_n} \nu, \nu)}{\sqrt{\det G}}.$$

EXAMPLE 15.1. Let c be a Frenet curve in  $\mathbb{R}^3$ , parametrized with unit speed. Consider the surface patch  $f(x_1, x_2) = c(x_1) + x_2 c'(x_1)$ , where  $x_2 > 0$ . Then  $\kappa_{aauss} = 0$  and

$$\kappa_{mean} = -\frac{1}{x_2} \cdot \frac{\tau(x_1)}{\kappa(x_1)},$$

where  $\tau$  and  $\kappa$  are the torsion and curvature of c as a Frenet curve.

EXAMPLE 15.2. Let  $c: I \to \mathbb{R}^2$  be a curve, parametrized with unit speed, whose first component  $c_1$  is always positive. The associated surface of rotation is  $f: I \times \mathbb{R} \to \mathbb{R}^3$ ,

$$f(x_1, x_2) = (c_1(x_1)\cos x_2, c_1(x_1)\sin x_2, c_2(x_1)).$$

The first and second fundamental forms of f are given by

$$G = \begin{pmatrix} 1 & \\ & c_1^2 \end{pmatrix}, \quad H = \begin{pmatrix} -c_1''c_2' + c_1'c_2'' \\ & c_1c_2' \end{pmatrix};$$

In particular,  $\kappa_{gauss} = -c_1''/c_1$ .

This can be used to construct surfaces with constant Gauss curvature, by solving the corresponding equation. For instance, the pseudo-sphere with Gauss curvature -1 is obtained by setting

$$c_1(t) = e^t, \ c_2(t) = \int_0^t \sqrt{1 - e^{2\tau}} d\tau,$$

where  $t \in (-\infty, 0)$ .

Definition 16.1. Write

$$\frac{\partial^2 f}{\partial x_i \partial x_j} = \sum_k \Gamma^k_{ij} \frac{\partial f}{\partial x_k} + H_{ij} \nu.$$

The functions  $\Gamma_{ij}^k(x)$  are called *Christoffel symbols*.

From the definition, it follows that

$$\sum_{l} \Gamma_{ij}^{l} G_{kl} = \langle \frac{\partial^{2} f}{\partial x_{i} \partial x_{j}}, \frac{\partial f}{\partial x_{k}} \rangle.$$

Theorem 16.2. Let  $g^{ij}$  be the coefficients of the inverse matrix  $G^{-1}$ . Then

$$\Gamma_{ij}^{l} = \frac{1}{2} \sum_{k} g^{kl} \Big( \partial_{x_j} G_{ik} - \partial_{x_k} G_{ij} + \partial_{x_i} G_{jk} \Big).$$

The expression above shows that the Christoffel symbols only depend on the first fundamental form. By taking the definition of  $\Gamma^l_{ij}$  and applying  $\partial/\partial x_k$ , we get

$$\sum_{l} \left\langle \frac{\partial^{3} f}{\partial x_{i} \partial x_{j} \partial x_{k}}, \frac{\partial f}{\partial x_{l}} \right\rangle G^{ls} = \partial_{k} \Gamma^{s}_{ij} + \sum_{t} \Gamma^{t}_{ij} \Gamma^{s}_{kt} - H_{ij} L_{sk}.$$

Using cancellation properties on the left hand side, one sees that

Theorem 16.3. The Gauss equation holds:

$$H_{ij}L_{sk} - H_{ik}L_{sj} = \partial_k \Gamma_{ij}^s - \partial_j \Gamma_{ik}^s + \sum_t \Gamma_{ij}^t \Gamma_{kt}^s - \Gamma_{ik}^t \Gamma_{jt}^s.$$

The expression on the right hand side of the Gauss equation is usually written as  $R_{ikj}^s$ . Denote by  $\Gamma_i$  the matrices whose entries are the Christoffel symbols, more precisely

$$(\Gamma_j)_{si} = \Gamma_{ij}^s$$
.

Similarly, write  $R_{ij}$  for the matrices whose entries are the Riemann curvatures, more precisely

$$(R_{kj})_{si} = R^s_{ikj}.$$

Then, the definition of the  $R_{ikj}^s$  can be rewritten in matrix notation as

$$R_{kj} = \partial_k \Gamma_j - \partial_j \Gamma_k + \Gamma_k \Gamma_j - \Gamma_j \Gamma_k.$$

Since H = GL, we can also write the Gauss equation in one of the two following forms:

$$H_{ij}H_{sk} - H_{ik}H_{sj} = \sum_{u} G_{su}R_{ikj}^{u},$$
  
$$L_{ij}L_{sk} - L_{ik}L_{sj} = \sum_{u} G^{iu}R_{ukj}^{s}.$$

For a surface in  $\mathbb{R}^3$ , one sets (i, j, k, s) = (1, 1, 2, 2) in the first equation to get  $\det(H)$ , hence:

COROLLARY 17.1. (Theorema egregium for surfaces) The Gauss curvature of a surface patch is given in terms of the first fundamental form by

$$\kappa_{gauss} = \frac{\sum_{u} G_{2u} R_{121}^{u}}{\det(G)}.$$

EXAMPLE 17.2 (Isothermal or conformal coordinates). Suppose that the first fundamental form satisfies

$$G(x_1, x_2) = e^{h(x_1, x_2)} \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}.$$

Then  $\kappa_{gauss} = -\frac{1}{2e^h} \Delta h$ , where  $\Delta$  is the Laplace operator. There is a (hard) theorem which says that for an arbitrary surface patch and any given point, one can find a local reparametrization which brings the metric into this form.

EXAMPLE 17.3 (Parallel geodesic coordinates). Suppose that the first fundamental form satisfies

$$G(x_1, x_2) = \begin{pmatrix} 1 & 0 \\ 0 & h^2(x_1, x_2) \end{pmatrix}.$$

Then  $\kappa_{gauss} = -\frac{\partial_{x_1}^2 h}{h}$ . There is a (not so hard)which says that for an arbitrary surface patch and any given point, one can find a local reparametrization which brings the metric into this form.

We now introduce a generalization of our usual formalism, where the partial derivatives  $\partial_{x_i} f$  are replaced by some more flexible auxiliary choice of basis at any point.

DEFINITION 18.1. Let  $f: U \to \mathbb{R}^{n+1}$  be a hypersurface patch. A moving basis for f is a collection  $(X_1, \ldots, X_n)$  of vector-valued functions  $X_i: U \to \mathbb{R}^n$  which are linearly independent at each point. If the  $X_i$  are orthonormal with respect to the first fundamental form, we call  $(X_1, \ldots, X_n)$  a moving frame.

Let X be the matrix whose columns are  $(X_1, \ldots, X_n)$ , and define the *connection matrices* and their *curvature matrices* to be, respectively,

$$A_j = X^{-1}(\partial_{x_j}X) + X^{-1}\Gamma_jX,$$
  

$$F_{kj} = \partial_k A_j - \partial_j A_k + A_k A_j - A_j A_k.$$

LEMMA 18.2. For any moving basis,  $F_{kj} = X^{-1}R_{kj}X$ .

LEMMA 18.3. If the moving basis is a frame, the  $A_j$  and  $F_{kj}$  are skew-symmetric matrices.

Let's specialize to the case of surfaces, n=2, and take X to be a moving frame. Then,  $F_{12}$  is necessarily a multiple of J. From the Gauss equation, we have

$$\kappa_{gauss} = \det(L) = (R_{21}G^{-1})_{12}$$

$$= (XF_{21}X^{-1}G^{-1})_{12} = (XF_{21}X^{tr})_{12}$$

$$= (F_{21})_{12}\det(X) = (F_{21})_{12}\det(G)^{-1/2}.$$

This gives rise to a curvature expression in curl form:

Proposition 18.4. If  $\alpha_i = (A_i)_{12}$ , then

$$\kappa_{gauss} \sqrt{\det(G)} = (F_{21})_{12} = \partial_2 \alpha_1 - \partial_1 \alpha_2.$$

COROLLARY 18.5 (Gauss-Bonnet for tori). Let  $f: \mathbb{R}^2 \to \mathbb{R}^3$  be a doubly-periodic surface patch, which means that  $f(x_1 + T_1, x_2) = f(x_1, x_2) = f(x_1, x_2 + T_2)$  for some  $T_1, T_2 > 0$ . Then

$$\kappa_{gauss}^{tot} \stackrel{\text{def}}{=} \int_{[0,T_1]\times[0,T_2]} \kappa_{gauss} \sqrt{\det(G)} \, dx_1 dx_2 = 0.$$

From this and Example 14.3, we get:

COROLLARY 18.6. If f is a doubly-periodic surface patch, then the Gauss curvature must be > 0 at some point, and < 0 at some other point.

Before continuing, we need more linear algebra preliminaries: write Λ2(Rn) for the space of skewsymmetric matrices of size n. This is a linear subspace of Rn<sup>2</sup> of dimension n(n − 1)/2. Given v, w ∈ Rn, we denote by v ∧ w the skewsymmetric matrix with entries

$$(v \wedge w)_{ij} = \frac{1}{2}(v_i w_j - w_i v_j).$$

This satisfies the rules

$$w \wedge v = -v \wedge w,$$
  
 $w \wedge (u+v) = w \wedge u + w \wedge v.$ 

Lemma 19.1. If (vi)1≤i≤<sup>n</sup> is any basis of Rn, then (v<sup>i</sup> ∧v<sup>j</sup> )1≤i<j≤<sup>n</sup> is a basis of the space of antisymmetric matrices.

Given any linear map L : R<sup>n</sup> R<sup>n</sup> → , there is an associated map

$$\Lambda^2 L : \Lambda^2 \mathbb{R}^n \longrightarrow \Lambda^2 \mathbb{R}^n, \quad (\Lambda^2 L)(S) = LSL^{tr}.$$

This satisfies (and is characterized by)

$$\Lambda^2 L(v \wedge w) = Lv \wedge Lw.$$

Example 19.2. If n = 2, then Λ2R<sup>2</sup> is one-dimensional, and Λ2L is just multiplication with det(L).

Lemma 19.3. We have

$$\operatorname{trace}(\Lambda^2 L) = \frac{1}{2}(\operatorname{trace}(L)^2 - \operatorname{trace}(L^2)),$$
$$\det(\Lambda^2 L) = \det(L)^{n-1}.$$

Lemma 19.4. Suppose that L,L˜ : R<sup>n</sup> R<sup>n</sup> → are two linear maps, with rank(L) ≥ 3. Then, if Λ2L = Λ2L˜, it also follows that L = ±L˜.

This is easiest to see if L is a diagonal matrix with entries (1, . . . , 1, 0, . . . , 0), and the general case follows from that.

An expression is called *intrinsic* if it depends only on the first fundamental form and its derivatives. For instance, G is intrinsic, but H is not intrinsic. Less obviously, the Christoffel symbols are intrinsic, and so are the  $R^s_{ikj}$ . The last-mentioned observation deserves to be formulated in a more conceptual way.

Let  $\Lambda^2 L : \Lambda^2 \mathbb{R}^n \to \Lambda^2 \mathbb{R}^n$  be the second exterior product of the shape operator. We call this the *Riemann curvature operator*, and denote it by  $\mathcal{R}$ . By definition

$$\mathcal{R}(e_j \wedge e_k) = Le_j \wedge Le_k = \sum_{is} L_{ij} L_{sk} e_i \wedge e_s = \sum_{i \leq s} (L_{ij} L_{sk} - L_{sj} L_{ik}) e_i \wedge e_s = \sum_{i \leq s} (\sum_{u} g^{iu} R^s_{ukj}) e_i \wedge e_s.$$

Under reparametrization  $\tilde{f} = f \circ \phi$ , the Riemann curvature operators satisfy  $\tilde{\mathcal{R}}(x) = (\Lambda^2 D\psi(x))^{-1} \cdot \mathcal{R}(\psi(x)) \cdot (\Lambda^2 D\psi(x)).$ 

Theorem 20.1. (Generalized theorems egregium)  $\mathcal{R}$  is intrinsic.

COROLLARY 20.2. The unordered collection of n(n-1)/2 numbers  $\lambda_i \lambda_j$  is intrinsic.

COROLLARY 20.3.  $\kappa_{scalar}$  and  $\kappa_{gauss}^{n-1}$  are intrinsic. In particular,  $\kappa_{gauss}$  is intrinsic for n even, and  $|\kappa_{gauss}|$  is intrinsic for  $n \geq 3$  odd.

COROLLARY 20.4. Let  $f: U \to \mathbb{R}^{n+1}$  be a hypersurface patch, defined on a connected set. Suppose that for each point in U, the matrix  $H_x$  has rank  $\geq 3$ . In that case, the intrinsic geometry of f determines the extrinsic one. This means that if  $\tilde{f}: U \to \mathbb{R}^{n+1}$  is another hypersurface patch with the same first fundamental form as f, then necessarily  $\tilde{f}(x) = Af(x) + c$  with f an orthogonal matrix, and f a constant.

To get some intuition for the intrinsic viewpoint, let's look at the problem of simplifying the first fundamental form by a local change of coordinates. More precisely, let  $f: U \to \mathbb{R}^{n+1}$  be a hypersurface patch, and p a point of U. A local reparametrization near p is a partial reparametrization  $\tilde{f} = f \circ \phi$ :  $\tilde{U} \to \mathbb{R}^{n+1}$ , where  $p \in \tilde{U}$  and  $\psi(p) = p$ . Such local reparametrizations are easy to find, because  $\det(D\phi(p)) > 0$  implies positivity of that determinant for points close to p.

LEMMA 21.1. For any point p, there is always a local reparametrization such that in the new coordinates,  $\tilde{G}_p = \mathbf{1}$  is the identity matrix.

LEMMA 21.2. Suppose that we have numbers  $S_{ijk}$  (the indices i,j,k run from 1 to n) such that  $S_{ijk} = S_{jik}$ . Then there are numbers  $T_{ijk}$  with  $T_{ijk} = T_{kji}$  such that

$$S_{ijk} = T_{ijk} + T_{jik}.$$

COROLLARY 21.3. For any point p, there is always a local reparametrization such that in the new coordinates,  $\tilde{G}_p = \mathbf{1}$  and  $\partial_{x_k} \tilde{G}_p = 0$  for all k.

Our first generalization is to hypersurfaces in Minkowski space. Take  $\mathbb{R}^{n+1}$  with the Minkowski form  $\langle X, Y \rangle_{Min} = X_1Y_1 + X_2Y_2 + \cdots + X_nY_n - X_{n+1}Y_{n+1}$ .

DEFINITION 22.1. A spacelike hypersurface in Minkowski space is a smooth map  $f: U \to \mathbb{R}^{n+1}$ , where  $U \subset \mathbb{R}^n$  is an open subset, such that at every point  $x \in U$ , the derivatives  $(\partial_{x_1} f, \ldots, \partial_{x_n} f)$  are linearly independent and span a subspace of  $\mathbb{R}^{n+1}$  on which  $\langle \cdot, \cdot \rangle_{Min}$  is positive definite.

More concretely, f is spacelike if the matrices G(x) with entries  $G_{ij}(x) = \langle \partial_{x_i} f, \partial_{x_j} f \rangle_{Min}$  are positive definite for all x. We define this to be the first fundamental form of the hypersurface. Using the usual intrinsic formulae, we can now define the Christoffel symbols  $\Gamma_{ij}^k$  and the  $R_{ujk}^s$ , hence the Riemann curvature operator  $\mathcal{R}$ .

DEFINITION 22.2. The Gauss normal vector of a spacelike hypersurface is the unique  $\nu = \nu(x)$  such that  $\langle \nu, \nu \rangle_{Min} = -1$ ,  $\langle \nu, \partial_{x_i} f \rangle_{Min} = 0$ , and  $\det(\partial_{x_1} f, \dots, \partial_{x_n} f, \nu) > 0$ .

Given that, we now define H by  $H_{ij} = -\langle \partial_{x_i} \nu, \partial_{x_j} f \rangle_{Min} = \langle \nu, \partial^2_{x_i x_j} f \rangle_{Min}$  and  $L = G^{-1}H$ . Some of the usual equations pick up additional signs, for instance:

$$\frac{\partial^2 f}{\partial x_i \partial x_j} = \sum_k \Gamma_{ij}^k \, \partial_{x_k} f - H_{ij} \nu.$$

Similarly, the theorema egregium says that  $\mathcal{R} = -\Lambda^2(L)$ . In particular, for spacelike surfaces, the Gauss curvature is  $\kappa_{gauss} = -\det(H)/\det(G) = -\det(L)$ .

LEMMA 22.3 (no proof). If  $X \in \mathbb{R}^{n+1}$  has  $\langle X, X \rangle_{Min} < 0$ , then its Minkowski orthogonal complement  $X^{\perp} = \{Y \in \mathbb{R}^{n+1} : \langle X, Y \rangle_{Min} = 0\}$  has the property that  $\langle \cdot, \cdot \rangle_{Min}$  restricted to  $X^{\perp}$  is positive definite.

EXAMPLE 22.4. Hyperbolic n-space is defined to be  $H^n = \{X \in \mathbb{R}^{n+1} : X_{n+1} > 0, \langle X, X \rangle_{Min} = -1\}$ . Suppose that  $f: U \to \mathbb{R}^{n+1}$  is some parametrization of  $H^n$ . Since  $\langle f, \partial_{x_i} f \rangle = 0$ , it follows from the Lemma that f is spacelike. It has Gauss normal vector  $\nu = \pm f$ . Hence  $H = \mp G$  and  $L = \mp 1$ . Hence,  $\kappa_{qauss} = -1$ .

Two explicit parametrizations of hyperbolic n-space: the first is the  $Poincar\acute{e}$  or  $conformal\ ball\ model$ 

$$f: U = \{x \in \mathbb{R}^n : ||x|| < 1\} \longrightarrow \mathbb{R}^{n+1},$$
  
 $f(x) = \frac{1}{1 - ||x||^2} (2x_1, \dots, 2x_n, 1 + ||x||^2).$ 

Geometrically, this corresponds to taking a disc in  $\mathbb{R}^n \times \{0\}$ , and then projecting radially from the point  $(0, \ldots, -1)$ . In this model,

$$G_{ij} = \begin{cases} \frac{4}{(1 - \|x\|^2)^2} & i = j, \\ 0 & i \neq j. \end{cases}$$

The second is the Klein or projective ball model

$$\tilde{f}: U = \{x \in \mathbb{R}^n : ||x|| < 1\} \longrightarrow \mathbb{R}^{n+1},$$
  
 $\tilde{f}(x) = \frac{1}{\sqrt{1 - ||x||^2}} (x_1, \dots, x_n, 1).$ 

Geometrically, one takes the disc tangent to  $H^n$  at the point  $(0, \ldots, 0, 1)$ , and then projects radially from the origin. The resulting first fundamental form is

$$\tilde{G}_{ij} = \begin{cases} \frac{1}{1 - ||x||^2} + \frac{x_i^2}{(1 - ||x||^2)^2} & i = j, \\ \frac{x_i x_j}{(1 - ||x||^2)^2} & i \neq j. \end{cases}$$

Our second generalization is to submanifolds which are not hypersurfaces. Let  $U \subset \mathbb{R}^n$  be an open subset. A regular map (or *immersion*)  $f: U \to \mathbb{R}^{n+m}$  is a smooth map such that the partial derivatives  $\partial_{x_1} f, \ldots, \partial_{x_n} f$  are linearly independent at each point. The first fundamental form is then defined as usual by

$$G = Df^{tr} \cdot Df$$
.

DEFINITION 23.1. A set of Gauss normal vectors for f consists of maps  $\nu^1, \ldots, \nu^m : U \to \mathbb{R}^{n+m}$  satisfying

$$\langle \nu^{w}, \nu^{w} \rangle = 1,$$
  

$$\langle \nu^{v}, \nu^{w} \rangle = 0 \text{ for } u \neq w,$$
  

$$\langle \nu^{w}, \partial_{x_{i}} f \rangle = 0,$$
  

$$\det(\partial_{x_{1}} f, \dots, \partial_{x_{n}} f, \nu^{1}, \dots, \nu^{m}) > 0.$$

Such maps may not necessarily exist over all of U, but they can be defined locally near any given  $x \in U$  by the Gram-Schmidt method. Moreover, any two choices defined on the same subset are related by

$$\tilde{\nu}^w = \sum_v a_{vw} \nu^v,$$

where  $a_{vw}$  are the coefficients of an orthogonal matrix A = A(x) with det(A) = 1.

DEFINITION 23.2. Given a set of Gauss normal vectors, we define the second fundamental forms  $H^w$ , w = 1, ..., m, by

$$H_{ij}^w = -\langle \partial_i \nu^w, \partial_j f \rangle = \langle \nu^w, \partial^2 f / \partial x_i \partial x_j \rangle.$$

The corresponding shape operators are  $L^w = G^{-1}H^w$ .

One then has

$$\frac{\partial^2 f}{\partial x_i \partial x_j} = \sum_k \Gamma^k_{ij} \, \partial_{x_k} f + \sum_w H^w_{ij} \nu,$$

where the Christoffel symbols  $\Gamma^k_{ij}$  are given by the usual intrinsic formulae. The Gauss equation says that

$$\sum_{w} H_{ij}^{w} L_{sk}^{w} - H_{ik}^{w} L_{sj}^{w} = \partial_{k} \Gamma_{ij}^{s} - \partial_{j} \Gamma_{ik}^{s} + \sum_{t} \Gamma_{ij}^{t} \Gamma_{kt}^{s} - \Gamma_{ik}^{t} \Gamma_{jt}^{s}.$$

It is easy to check explicitly that the left hand side is independent of the choice of  $\nu^w$ . The Riemann curvature operator, given by the usual intrinsic formulae, now reads

$$\mathcal{R} = \sum_{w} \Lambda^2(L^w).$$

Its eigenvalues are now less constrained than in the hypersurface case, hence the connection between intrinsic and extrinsic geometry is somewhat weaker.

Our final generalization is to a completely intrinsic viewpoint. A Riemannian metric on  $U \subset \mathbb{R}^n$  is a family  $G_x$  of positively definite symmetric nxn matrices, depending smoothly on  $x \in U$ . For any such metric, and independently of any embedding of U into another space, one can define Christoffel symbols, the Riemann curvature operator, and all its dependent quantities (scalar curvature, for instance). The proof of Corollary 18.6, for instance, is purely intrinsic and shows the following:

COROLLARY 23.3. Take any Riemannian metric on  $\mathbb{R}^2$  which is doubly-periodic,  $G_{(x_1+T_1,x_2)}=G_{(x_1,x_2)}=G_{(x_1,x_2+T_2)}$ . Then

$$\kappa_{gauss}^{tot} = \int_{[0,T_1]\times[0,T_2]} \kappa_{gauss} \sqrt{\det(G)} dx_1 dx_2 = 0.$$