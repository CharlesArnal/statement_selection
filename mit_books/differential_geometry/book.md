MIT OpenCourseWare <http://ocw.mit.edu>

18.950 Differential Geometry Fall 2008

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

# CHAPTER 1

# Local and global geometry of plane curves

Terminology from linear algebra: the scalar product of  $X, Y \in \mathbb{R}^2$  is

$$\langle X, Y \rangle = X_1 Y_1 + X_2 Y_2.$$

The length of a vector is

$$||X|| = \langle X, X \rangle^{1/2}.$$

The rotation by any angle  $\alpha$  is the linear transformation of  $\mathbb{R}^2$  with matrix

$$A = \begin{pmatrix} \cos(\alpha) & -\sin(\alpha) \\ \sin(\alpha) & \cos(\alpha) \end{pmatrix}.$$

In particular,  $J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$  is anticlockwise rotation by 90 degrees. We write  $\det(X, Y)$  for the determinant of the matrix with column vectors  $X, Y \in \mathbb{R}^2$ . Equivalently,

$$det(X, Y) = \langle JX, Y \rangle$$
 or  $\langle X, Y \rangle = det(X, JY)$ .

Finally, suppose that  $X \in \mathbb{R}^2$  is any vector, and  $Y \in \mathbb{R}^2$  is a vector of length one. Then

$$X = \langle Y, X \rangle Y + \det(Y, X) J Y.$$

Terminology from calculus: a map is called smooth if it is infinitely differentiable.

LEMMA 1.1. Let  $I \subset \mathbb{R}$  be an interval, and  $f: I \to \mathbb{R}^2$  a smooth map such that ||f(t)|| = 1 for all t. Then

$$f'(t) = \det(f(t), f'(t))Jf(t).$$

DEFINITION 1.2. A regular curve is a smooth map  $c: I \to \mathbb{R}^2$ , where  $I \subset \mathbb{R}$  is an interval, satisfying  $c'(t) \neq 0$  for all t. The curvature of c at t is

$$\kappa(t) = \frac{\det(c'(t), c''(t))}{\|c'(t)\|^3}.$$

In physics terminology, if distance in  $\mathbb{R}^2$  is measured in meters m, and time on I in seconds s, then  $\kappa$  is of type 1/m. For instance, a circle of radius R has curvature 1/R if it is parametrized in an anticlockwise way, and -1/R if it is parametrized in a clockwise way.

PROPOSITION 1.3 (Frenet equation of motion). For a regular curve c,

$$\frac{d}{dt} \left( \frac{c'(t)}{\|c'(t)\|} \right) = \|c'(t)\| \kappa(t) J \frac{c'(t)}{\|c'(t)\|} = \kappa(t) J c'(t).$$

COROLLARY 1.4. If  $\kappa(t) = 0$  for all t, then  $c(I) \subset \mathbb{R}^2$  is part of a straight line.

COROLLARY 1.5. Suppose that  $\kappa(t) = 1/R$  is a nonzero constant. Then  $c + RJ \frac{c'}{\|c'\|}$  is constant, and therefore c is part of a circle of radius |R|.

A graph is a curve of the form c(t) = (t, f(t)).

LEMMA 2.1. The curvature of a graph is

$$\kappa(t) = \frac{f''(t)}{(1 + f'(t)^2)^{3/2}}.$$

A unit speed curve is a curve c such that ||c'(t)|| = 1.

LEMMA 2.2. The curvature of a unit speed curve is

$$\kappa(t) = \det(c'(t), c''(t)).$$

Moreover, we have

$$c''(t) = \kappa(t) Jc'(t),$$

and in particular  $|\kappa(t)| = ||c''(t)||$ .

One can think of this as the motion of a charged particle in a magnetic field pointing "out of the plane", with strength  $\kappa(t)$ .

PROPOSITION 2.3. For every  $\kappa: I \to \mathbb{R}$  there is a unit speed curve  $c: I \to \mathbb{R}$  whose curvature is  $\kappa$ . Moreover, c is unique up to translations and rotations.

It is often useful to change the way in which a curve is parametrized. Let  $c: I \to \mathbb{R}^2$  be a regular curve, and  $\psi: \tilde{I} \to I$  a smooth function such that  $\psi'(t) > 0$  for all t. Then  $\tilde{c}(t) = c(\psi(t))$  is again a regular curve, called a partial reparametrization of c.

PROPOSITION 2.4. If  $\tilde{c}(t) = c(\psi(t))$  is a partial reparametrization, their curvatures are related by  $\kappa_{\tilde{c}}(t) = \kappa_c(\psi(t))$ .

If  $\psi: \tilde{I} \to I$  is onto, we call  $\tilde{c}$  a reparametrization of c. Such changes of parameter can be inverted, as the following well-known statement shows.

LEMMA 2.5 (from calculus). Let  $\tilde{I} \subset \mathbb{R}$  be an interval, and  $\psi : \tilde{I} \to \mathbb{R}$  a smooth function such that  $\psi'(t) > 0$  for all t. Then  $\psi(\tilde{I}) = I$  is an interval, and  $\psi$  is a one-to-one map from I to  $\tilde{I}$ . Moreover, its inverse map  $\phi = \psi^{-1}$  is again smooth, and by the chain rule  $\phi'(t) = 1/\psi'(\phi(t))$ .

LEMMA 2.6. Let  $d = (d_1, d_2)$  be a curve such that  $d'_1(t) > 0$  for all t. One can then reparametrize it to a graph.

Lemma 2.7. Every curve d admits a reparametrization which is a unit speed curve.

Let c, d be two unit speed curves. We say that c and d osculate at  $t_0$  if they are both defined at that point and satisfy

$$c(t_0) = d(t_0), \quad c'(t_0) = d'(t_0), \quad c''(t_0) = d''(t_0).$$

Because the curves are unit speed,  $c''(t_0) = d''(t_0)$  is equivalent to saying that  $\kappa_c(t_0) = \kappa_d(t_0)$ .

PROPOSITION 3.1. Let c be a unit speed curve, and  $t_0$  a point where  $\kappa(t_0) \neq 0$ . Then there is a unique circle which osculates c at  $t_0$  (the osculating circle).

The curvature  $|\kappa(t_0)|$  is then the inverse radius of the osculating circle at that point. If the curvature is zero, there is no osculating circle, and instead the curve osculates its tangent line.

PROPOSITION 3.2. Let  $f: U \to \mathbb{R}$  be a smooth function, defined on an open subset  $U \subset \mathbb{R}^2$ . Let  $c: I \to U$  be a regular curve, which is contained in its level set  $\{f(x) = a\}$ . Then, at every point t such that x = c(t) satisfies  $\nabla f(x) \neq 0$ , we have

$$\pm \kappa(t) = \frac{\langle J \nabla f(x), D^2 f(x) J \nabla f(x) \rangle}{\|\nabla f(x)\|^3}.$$

Here,  $D^2f(x)$  is the Hessian (the matrix of second derivatives).

The sign is determined as follows. If  $\det(\nabla f(x), c'(t)) > 0$ , then  $\kappa(t)$  is the right hand side of the equation above. Otherwise,  $-\kappa(t)$  is the right hand side.

EXAMPLE 3.3. Let  $f: \mathbb{R}^2 \to \mathbb{R}$  be a function with f(0) = 0, Df(0) = 0, and  $D^2f(0)$  positive definite (so that the origin is a local minimum). Then as one gets closer and closer to the origin, the curvature of the level sets goes to infinity.

As the first of our two generalizations, we look at the Minkowski plane, which is  $\mathbb{R}^2$  with the indefinite bilinear form  $\langle X, Y \rangle_{Min} = X_1Y_1 - X_2Y_2$ . The role of J is played by the matrix

$$K = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}.$$

In particular  $\langle X, KX \rangle_{Min} = 0$ , which is the analogue of  $\det(X, X) = 0$  in the Minkowski context. Take two vectors X, Y where  $\langle Y, Y \rangle_{Min} = 1$ . One can then write

$$X = \langle Y, X \rangle_{Min} Y - \langle KY, X \rangle_{Min} KY.$$

A regular curve  $c: I \to \mathbb{R}^2$  is called *spacelike* if  $\langle c'(t), c'(t) \rangle_{Min} > 0$  for all t. We define the curvature of c to be

$$\kappa = \frac{\langle c'(t), Kc''(t) \rangle_{Min}}{\|c'(t)\|^3}.$$

The equation of motion is then

$$\frac{d}{dt} \left( \frac{c'}{\langle c', c' \rangle_{Min}^{1/2}} \right) = -\kappa(t) K c'.$$

The curvature is reparametrization invariant. Every spacelike curve admits a reparametrization  $\tilde{c} = c(\psi)$  such that  $\langle \tilde{c}'(t), \tilde{c}'(t) \rangle_{Min} = 1$  (for the opposite case of timelike curves, this would be called proper time parametrization). For curves with this property, the equation of motion simplifies to

$$c''(t) = -\kappa(t)Kc'(t).$$

EXAMPLE 4.1.  $c(t) = (\cosh(t), \sinh(t))$  is the analogue of a circle. It is parametrized with unit speed, and its curvature is constant equal to -1.

Our second generalization is to curves in higher-dimensional Euclidean space. A regular curve in  $\mathbb{R}^n$  is a smooth map  $c:I\to\mathbb{R}^n$ , where  $I\subset\mathbb{R}$  is an interval, such that  $c'(t)\neq 0$  for all t. The naive generalization of our two-dimensional definition would be

$$\frac{\det(c', c'', \dots, c^{(n)})}{\|c'(t)\|^{n(n+1)/2}},$$

where det is the determinant of the matrix with given column vectors. This is reparametrization invariant. Physically it's of type  $m^{-n(n-1)/2}$ , where m is the unit of distance in  $\mathbb{R}^n$ . Frenet theory decomposes this as a product of curvatures, each carrying different information.

LEMMA 5.1 (Gram-Schmidt orthogonalization). Let  $(v_1, \ldots, v_k)$  be linearly independent vectors. There are unique orthonormal vectors  $(e_1, \ldots, e_k)$  of the form

$$e_i = \sum_{j \le i} f_{ij} v_j$$

where  $f_{ii} > 0$ . Note that in particular, each  $(e_1, \ldots, e_i)$  spans the same subspace as  $(v_1, \ldots, v_i)$ . An explicit inductive formula is

$$e_i = \frac{v_i - \langle v_i, e_1 \rangle e_1 - \dots - \langle v_i, e_{i-1} \rangle e_{i-1}}{\|v_i - \langle v_i, e_1 \rangle e_1 - \dots - \langle v_i, e_{i-1} \rangle e_{i-1}\|}$$

LEMMA 5.2. Let E(t) be a family of orthogonal matrices, depending differentiably on t. Write

$$\frac{d}{dt}E(t) = E(t)A(t).$$

Then the matrices A(t) are skewsymmetric,  $A(t)^{tr} = -A(t)$ .

DEFINITION 5.3.  $c: I \to \mathbb{R}^n$  is a *Frenet curve* if for all t, the vectors  $(c'(t), c''(t), \ldots, c^{(n-1)}(t))$  are linearly independent.

One then defines the Frenet frame  $(e_1(t), \ldots, e_n(t))$  as follows. First, apply Gram-Schmidt to  $(v_1(t) = c'(t), \ldots, v_{n-1}(t) = c^{(n-1)}(t))$ , which yields  $(e_1(t), \ldots, e_{n-1}(t))$ . Then, take the unique vector  $e_n(t)$  which is orthogonal to  $(e_1(t), \ldots, e_{n-1}(t))$  and satisfies  $\det(e_1(t), \ldots, e_n(t)) = 1$ .

The components of the last vector are

$$e_{n,j} = \det(e_1, \dots, e_{n-1}, \overbrace{(0, \dots, 1, \dots, 0)}^{j\text{-th unit vector}}).$$

LEMMA 5.4. Frenet frames are reparametrization invariant. Explicitly, if c is a Frenet curve and  $d(t) = c(\phi(t))$  a reparametrization, then d is again Frenet, and its Frenet frame is related to that of c by

$$f_i(t) = e_i(\phi(t)).$$

Take a Frenet curve c in  $\mathbb{R}^n$ . Let E(t) be the matrix with columns  $e_1(t), \ldots, e_n(t)$ .

THEOREM 6.1. We have

$$\frac{d}{dt}E(t) = \|c'(t)\| E(t) \begin{pmatrix} 0 & -\kappa_1(t) & 0 & \cdots \\ \kappa_1(t) & 0 & -\kappa_2(t) & \cdots \\ 0 & \kappa_2(t) & 0 & -\kappa_3(t) \cdots \\ \cdots \end{pmatrix}.$$

Here  $\kappa_1(t), \ldots, \kappa_{n-2}(t) > 0$ , and  $\kappa_{n-1}(t) \in \mathbb{R}$ . Concretely,

$$\kappa_i(t) = \frac{\langle e_{i+1}(t), e_i'(t) \rangle}{\|c'(t)\|}.$$

The functions  $\kappa_i(t)$  are called the *Frenet curvatures* of c. Physically, they are again of type 1/m. As usual they are reparametrization invariant.

PROPOSITION 6.2. Let c be a Frenet curve in  $\mathbb{R}^n$ . Then

$$\frac{\det(c',c'',\ldots,c^{(n)})}{\|c'\|^{n(n+1)/2}} = \prod_{i=1}^{n-1} \kappa_i^{n-i}.$$

EXAMPLE 6.3. A regular plane curve is always Frenet. The Frenet basis is  $e_1(t) = c'(t)/\|c'(t)\|$ ,  $e_2(t) = Jc'(t)/\|c'(t)\|$ .  $\kappa = \kappa_1$  is the ordinary curvature, and the Frenet equations of motion reduce to Proposition 1.3.

EXAMPLE 6.4. Let  $c: I \to \mathbb{R}^3$  be a space curve, parametrized with unit speed. This is Frenet if and only if  $c''(t) \neq 0$ . The Frenet basis is

$$e_1(t) = c'(t), \quad e_2(t) = \frac{c''(t)}{\|c''(t)\|},$$
  
 $e_3(t) = \frac{c'(t) \times c''(t)}{\|c''(t)\|}.$ 

 $\kappa = \kappa_1$  is called the *curvature* and  $\tau = \kappa_2$  the *torsion*. Concretely

$$\kappa = \langle e_2(t), e_1'(t) \rangle = ||c''(t)||,$$

$$\tau = \langle e_3(t), e_2'(t) \rangle = \frac{\langle c'(t) \times c''(t), c'''(t) \rangle}{||c''(t)||^2} = \frac{\det(c', c'', c''')}{||c''||^2}.$$

The Frenet equations are

$$e'_1 = \kappa e_2, \quad e'_2 = \tau e_3 - \kappa e_1, \quad e'_3 = -\tau e_2.$$

Throughout the following discussion,  $f: \mathbb{R} \to \mathbb{R}^2$  is a T-periodic smooth function (f(t+T)=f(t)) for all t, such that ||f(t)||=1 for all t.

LEMMA 7.1. One can write  $f(t) = (\cos \theta(t), \sin \theta(t))$ , where  $\theta : \mathbb{R} \to \mathbb{R}$  is a smooth function, unique up to adding constant integer multiples of  $2\pi$ . Specifically, all such functions are of the form

$$\theta(t) = \theta_0 + \int_{t_0}^t \det(f(\tau), f'(\tau)) d\tau.$$

where  $(\cos \theta_0, \sin \theta_0) = f(t_0)$ .

Definition 7.2. The degree of f is

$$\deg(f) = \frac{1}{2\pi} (\theta(T) - \theta(0)) = \frac{1}{2\pi} \int_0^T \det(f(\tau), f'(\tau)) d\tau \in \mathbb{Z}.$$

Instead of [0, T], one can take any other interval  $[t_0, t_0 + T]$ .

LEMMA 7.3. If  $deg(f) \neq 0$ , f is a surjective (onto) map to the unit circle.

PROPOSITION 7.4. Let ||p|| = 1 be a point on the circle with the following properties: (i) There are only finitely many  $0 \le t_1 < t_2 < \cdots < t_m < T$  for which  $f(t_k) = p$ ; (ii) each such  $t_k$  satisfies  $f'(t_k) \ne 0$ . In that case,

$$\deg(f) = \sum_{k=1}^{m} \operatorname{sign} \det(p, f'(t_k)).$$

Here is a popular application of degrees. Let f be more generally a T-periodic function  $\mathbb{R} \to \mathbb{R}^2$ , and  $q \in \mathbb{R}^2$  a point not on its image. The winding number of f around p is the degree of the map f(t) - q/||f(t) - q||.

DEFINITION 8.1. A closed curve of period T is a regular curve  $c : \mathbb{R} \to \mathbb{R}^2$  such that c(t+T) = c(t) for all t. We say that c is simple if it has no selfintersections. This means that for all  $0 \le s < t < T$ , we have  $c(s) \ne c(t)$ .

Theorem 8.2 (Jordan curve theorem; very sketchy proof). Let c be a simple closed curve. Then, the complement of the image of c is the disjoint union of two connected open subsets, one bounded (the inside) and one unbounded (the outside)

The hard step in the proof is to show that the inside and outside are not connected to each other. For that, one uses winding numbers. Points in the inside have winding number  $\neq 0$ , and points in the outside have winding number 0. On the other hand, the winding number is locally constant.

DEFINITION 8.3. The total curvature of a closed curve is defined to be

$$\kappa^{tot}(c) = \int_0^T \kappa(t) \|c'(t)\| dt.$$

Physically,  $\kappa^{tot}$  is a dimensionless quantity.

LEMMA 8.4 (partial proof). Let c be a closed curve of period T, and set  $L = \int_0^T \|c'(t)\| dt$ . Let d be the unit speed reparametrization of c. Then d is again a closed curve, of period L. Moreover, the total curvature of d is the same as that of c.

PROPOSITION 8.5.  $\kappa^{tot}(c)/2\pi$  is the degree of  $f(t) = c'(t)/\|c'(t)\|$ . In particular, it is always an integer. We call it the *rotation number* of the curve (not to be confused with the winding number: the rotation number is the winding number of c'(t) around 0).

COROLLARY 8.6. Let c be a closed curve of period T. Suppose that there are only finitely many points  $0 \le t_1 < t_2 < \cdots < t_m < T$  where  $c'_2(t_k) = 0$ ,  $c'_1(t_k) > 0$ , and that any such point satisfies  $\kappa(t_k) \ne 0$ . Then, the rotation number is

$$\kappa^{tot}(c)/2\pi = \sum_{k=1}^{m} \operatorname{sign}(\kappa(t_k)).$$

Theorem 9.1 (Hopf Umlaufsatz; sketch proof). Let c be a simple closed curve. Then  $\kappa^{tot}(c)=\pm 2\pi$ .

The sign here can be determined as follows. Let t be a point where  $c_2(t)$  reaches its (global) minimum. Then the sign of  $\kappa^{tot}(c)$  equals that of  $c'_1(t)$ .

DEFINITION 9.2. Let c be a simple closed curve. We say that c is convex if the following holds. Whenever c is tangent to some line  $\{a_1x_1 + a_2x_2 = b\}$  in the plane, it is entirely contained in one of the two half-planes  $\{a_1x_1 + a_2x_2 \leq b\}$ ,  $\{a_1x_1 + a_2x_2 \geq b\}$ .

PROPOSITION 9.3 (partial proof). A simple closed curve is convex if and only if its curvature never changes sign.

COROLLARY 9.4 (sketch proof). Let c be a closed curve of period T. Then

$$\int_0^T |\kappa(t)| \, \|c'(t)\| \, dt \ge 2\pi.$$

Here is a useful generalization of the Umlaufsatz. Take a closed curve c of period T. Suppose that c takes on the same value at most twice in [0,T). Moreover, for any  $0 \le s < t < T$  such that c(s) = c(t), we also require c'(s) and c'(t) to be linearly independent. In that case, we say that c has normal self-intersections.

THEOREM 9.5 (Whitney; no proof). Let c be a closed curve with normal self-intersections. Assume that it is parametrized in such a way that  $c_2(t)$  reaches a global minimum at t = 0. Then

$$\kappa^{tot}(c)/2\pi = \operatorname{sign} c_1'(0) - \sum_{(s,t)} \operatorname{sign} \det(c'(s), c'(t)),$$

where the sum is over all  $0 \le s < t < T$  with c(s) = c(t).

LEMMA 10.1 (Sturm-Hurwitz). Let  $f: \mathbb{R} \to \mathbb{R}$  be a continuous  $2\pi$ -periodic function such that

$$\int_0^{2\pi} f(t) dt = 0, \quad \int_0^{2\pi} f(t) \cos(t) dt = 0, \quad \int_0^{2\pi} f(t) \sin(t) dt = 0.$$

Then f has at least four zeros in the region  $[0, 2\pi)$ .

LEMMA 10.2. Let h be a smooth  $2\pi$ -periodic function. Then h(t) + h''(t) has at least four critical points (points where its derivative vanishes) in the region  $[0, 2\pi)$ .

LEMMA 10.3. Take a simple closed curve whose curvature is everywhere positive. By reparametrizing in a suitable way, one can achieve that the curve has period  $2\pi$  and satisfies

$$\frac{c'(t)}{\|c'(t)\|} = (\cos(t), \sin(t)).$$

In that case,

$$\kappa(t) = \frac{1}{\|c'(t)\|}.$$

Theorem 10.4 (Four Vertex theorem, strictly convex version). Take a simple closed curve whose curvature is everywhere positive. Then there are at least four points where  $\kappa'(t) = 0$ .

---

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

---

MIT OpenCourseWare <http://ocw.mit.edu>

18.950 Differential Geometry Fall 2008

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

# CHAPTER 3

# Global geometry of hypersurfaces

DEFINITION 24.1. A hypersurface is a subset  $M \subset \mathbb{R}^{n+1}$  with the following property. For every  $y \in M$  there is an open subset  $V \subset \mathbb{R}^{n+1}$  containing y, and a function  $\psi : V \to \mathbb{R}$  whose zero set  $\psi^{-1}(0)$  is precisely  $M \cap V$ , and whose derivative is nonzero at any point of  $M \cap V$ .

Example 24.2.  $M = \{x_1x_2x_3 = 0\} \subset \mathbb{R}^{n+1}$  is not a hypersurface.

We call  $\psi$  a local defining function for M near y. We are looking for properties of M that are independent of how it is presented as a zero set. The following is useful:

PROPOSITION 24.3 (L'Hopital's rule; proof postponed). Let  $\psi: V \to \mathbb{R}$  be a local defining function for M, and  $\phi: V \to \mathbb{R}$  another smooth function which vanishes along  $V \cap M$ . Then there a unique smooth function  $q: V \to \mathbb{R}$  such that  $\phi = q\psi$ .

COROLLARY 24.4. Let  $\psi, \tilde{\psi}: V \to \mathbb{R}$  be two local defining functions for M. Then there is a unique smooth nowhere vanishing function  $q: V \to \mathbb{R}$  such that  $\tilde{\psi} = q\psi$ .

Let M be a hypersurface,  $\psi:V\to\mathbb{R}$  a local defining function, and  $y\in V\cap M$  any point. The derivative  $D\psi_y$  is independent of the choice of  $\psi$  up to multiplication with a nonzero real number. Hence, its nullspace

$$TM_y = \ker D\psi_y = \{Y \in \mathbb{R}^{n+1} \mid D\psi_y \cdot Y = \langle \nabla \psi_y, Y \rangle = 0\}$$

is independent of  $\psi$ . We call it the tangent space of M at y.

Example 24.5. The unit sphere  $S^n=\{\|y\|^2=1\}\subset\mathbb{R}^{n+1}$  is a hypersurface, and  $TS^n_y=y^\perp$ .

Let  $M \subset \mathbb{R}^{n+1}$  be a hypersurface. If  $\psi$  is a local defining function for M, then the map  $\nabla \psi / \|\nabla \psi\| : M \cap V \to S^n$  is independent of the choice of  $\psi$  up to sign. This ambiguity will be further discussed later. Similarly, for all  $y \in M \cap V$ , the linear map

$$L_y: TM_y \longrightarrow TM_y, \ L_y(Y) = -D(\nabla \psi / \|\nabla \psi\|)_y \cdot Y$$

is independent of the choice of  $\psi$  up to sign. We call it the *shape operator* of M at y.

EXAMPLE 25.1. Take the hyperboloid  $M = \{y_1^2 = y_2^2 + y_3^2 + 1\}$  in  $\mathbb{R}^3$  (this is Euclidean space, and not to be confused with curvature computations in Minkowski space). The tangent space at any point y is spanned by  $Y_1 = (y_2, y_1, 0)$  and  $Y_2 = (y_3, 0, y_1)$ . The matrix of  $D(\nabla \psi / \|\nabla \psi\|)_y : TM_y \to TM_y$  with respect to this basis is

$$\frac{1}{\|y\|^3}\begin{pmatrix} y_1^2-y_2^2+y_3^2 & -2y_2y_3 \\ -2y_2y_3 & y_1^2-y_3^2+y_2^2 \end{pmatrix}$$

LEMMA 25.2. For  $X, Y \in TM_{u}$ ,

$$\langle X, L_y \cdot Y \rangle = -\frac{1}{\|\nabla_y \psi\|} \langle X, D^2 \psi_y \cdot Y \rangle.$$

This proves that  $L_y$  is selfadjoint with respect to the standard inner product  $\langle \cdot, \cdot \rangle$  on  $TM_y$ . In particular, it has real eigenvalues, which we call the principal curvatures. The mean, Gauss, and scalar curvature are then defined as usual. Finally, the Riemann curvature operator is defined to be

$$\mathcal{R}_y = \Lambda^2(L_y) : \Lambda^2(TM_y) \longrightarrow \Lambda^2(TM_y).$$

Note that  $\Lambda^2(L_y) = \Lambda^2(-L_y)$ , so the Riemann curvature operator does not suffer from sign ambiguities. The same applies to the Gauss curvature if n is even.

EXAMPLE 25.3. The Gauss curvature of the hyperboloid discussed above is the determinant of  $L_y$ , which is  $(2y_1^2 - 1)/||y||^6$ .

PROPOSITION 25.4. Let  $M \subset \mathbb{R}^{n+1}$  be a hypersurface. Take a point  $y \in M$ , a local defining function  $\psi$  for M near y, and an orthonormal basis  $Y_1, \ldots, Y_n$  of the tangent space  $TM_y$ .

$$\kappa_{mean} = \pm \frac{1}{\|\nabla \psi_y\|} \sum_{i=1}^n \langle Y_i, D^2 \psi_y \cdot Y_i \rangle,$$
  
$$\kappa_{gauss} = \pm \frac{\det(D^2 \psi_y \cdot Y_1, \dots, D^2 \psi_y \cdot Y_n, \nabla \psi_y)}{\|\nabla \psi_y\|^{n+1}}.$$

Let  $M \subset \mathbb{R}^{n+1}$  be a hypersurface.

DEFINITION 26.1. A function  $f: M \to \mathbb{R}$  if smooth if for every point  $y \in M$  there is an open subset  $V \subset \mathbb{R}^{n+1}$  containing y, and a smooth function  $\tilde{f}: V \to \mathbb{R}$ , such that  $f|M \cap V = \tilde{f}|M \cap V$ . We call  $\tilde{f}$  a local extension of f.

The derivative  $Df_y$  is the linear map  $TM_y \to \mathbb{R}$  defined by  $Df_y = D\tilde{f}_y \mid TM_y$ . This is independent of the choice of local extension.

This generalizes to several functions, which means to maps  $f: M \to \mathbb{R}^{k+1}$ . If  $M \subset \mathbb{R}^{n+1}$  and  $N \subset \mathbb{R}^{k+1}$  are hypersurfaces, and  $f: M \to \mathbb{R}^{k+1}$  a smooth map whose image lies in N, then the image of the derivative  $Df_y$  lies in the tangent space to N at f(y). Hence,  $Df_y$  is a linear map  $TM_y \to TN_{f(y)}$ .

DEFINITION 26.2. A Gauss map for M is a smooth map  $\nu: M \to \mathbb{R}^{n+1}$  such that for all  $y, \nu(y)$  is of unit length and orthogonal to  $TM_y$ .

We also call a Gauss map a choice of orientation. Suppose that such a  $\nu$  is given. If  $\psi$  is a local defining function for M, we have  $\nu = \pm \nabla \psi / \|\nabla \psi\|$  on  $M \cap V$ , where the sign is locally constant. If the sign is positive everywhere, we say that  $\psi$  is compatible with the choice of orientation.

Consider the derivative of the Gauss map, which is

$$D\nu_y: TM_y \longrightarrow T(S^n)_{\nu(y)} = \nu(y)^{\perp} = TM_y.$$

We re-define the shape operator to be  $L_y = -D\nu_y$ . This agrees with the previous definition, except that the sign ambiguity has been removed by the choice of orientation.

REMARK 26.3. In Proposition 25.4, assume that M is oriented, and  $\psi$  compatible with the choice of orientation. Then the sign in  $\kappa_{mean}$  is -1. Assume in addition that the basis is chosen in such a way that  $\det(Y_1, \ldots, Y_n, \nabla \psi_y) > 0$ . Then the sign in  $\kappa_{gauss}$  is  $(-1)^n$ .

DEFINITION 27.1. Let U, V be open subsets of  $\mathbb{R}^{n+1}$ . A smooth map  $\phi: V \to U$  is a diffeomorphism if it is one-to-one and the inverse  $\phi^{-1}$  is also smooth (it is in fact enough to check that  $\phi$  is one-to-one and that  $D\phi_y$  is invertible for all y, since that ensures smoothness of the inverse).

One can think of diffeomorphisms as curvilinear coordinate changes.

Theorem 27.2 (Inverse function theorem; no proof). Let  $\tilde{V} \subset \mathbb{R}^{n+1}$  be an open subset,  $y \in \tilde{V}$  a point, and  $\phi: \tilde{V} \to \mathbb{R}^{n+1}$  a smooth map such that  $D\phi_y$  is invertible. Then there is an open subset  $V \subset \tilde{V}$ , still containing y, such that:  $U = \phi(V)$  is open, and  $\phi|V: V \to U$  is a diffeomorphism.

COROLLARY 27.3 (Implicit function theorem, special case). Let  $\tilde{V} \subset \mathbb{R}^{n+1}$  be an open subset,  $\psi : \tilde{V} \to \mathbb{R}$  a smooth function, and  $y \in V$  a point such that  $\psi(y) = 0$ ,  $D\psi(y) \neq 0$ . Then there are: an open subset  $V \subset \tilde{V}$ , still containing y; an open subset  $U \subset \mathbb{R}^{n+1}$  containing 0; and a diffeomorphism  $\phi: U \to V$  such that  $\phi(0) = y$ , and  $\psi(\phi(x)) = x_{n+1}$  for all x.

The informal meaning is that in the curvilinear local coordinate system  $\phi$ ,  $\psi$  looks like a linear function.

Let  $M \subset \mathbb{R}^{n+1}$  be a hypersurface. Take a local defining function  $\psi : V \to \mathbb{R}$ , defined near some point  $y \in V$ . The derivative  $D\psi_y : \mathbb{R}^{n+1} \to \mathbb{R}$  depends on  $\psi$ , but its nullspace

$$\ker(D\psi_y) = \{ X \in \mathbb{R}^{n+1} \mid D\psi_y \cdot X = \langle \nabla \psi_y, X \rangle = 0 \}$$

does not, since it is the tangent space  $TM_y$ . Now assume that M comes with a Gauss vector, which on  $V \cap M$  agrees with  $\nabla \psi / \|\nabla \psi\|$ . The Hessian  $\mathbb{R}^{n+1} \times \mathbb{R}^{n+1} \to \mathbb{R}$ ,  $(X,Y) \mapsto \langle X, D^2 \psi_y Y \rangle$  depends on Y, but the map

$$TM_y \times TM_y \longrightarrow \mathbb{R}, \ (X,Y) \longmapsto \frac{1}{\|\nabla \psi\|} \langle X, D^2 \psi_y Y \rangle$$

is independent of  $\psi$ , since it can be written as  $-\langle X, LY \rangle$  where  $L: TM_y \to TM_y$  is the shape operator.

EXAMPLE 28.1. Take the hyperboloid  $M = \{y_1^2 = y_2^2 + y_3^2 + 1\}$  in  $\mathbb{R}^3$  (this is Euclidean space, and not to be confused with curvature computations in Minkowski space). A Gauss normal is

$$\nu(y) = \frac{1}{\|y\|} (-y_1, y_2, y_3).$$

The tangent space at any point y is spanned by  $Y_1 = (y_2, y_1, 0)$  and  $Y_2 = (y_3, 0, y_1)$ . The matrix of  $D\nu_y : TM_y \to TM_y$  with respect to this basis is

$$\frac{1}{\|y\|^3} \begin{pmatrix} y_1^2 - y_2^2 + y_3^2 & -2y_2y_3 \\ -2y_2y_3 & y_1^2 - y_3^2 + y_2^2 \end{pmatrix}$$

The Gauss curvature is its determinant, which is  $(2y_1^2 - 1)/||y||^6$ . In particular, it's always positive.

Let U, V be open subsets of  $\mathbb{R}^{n+1}$ . A smooth map  $\phi: V \to U$  is a diffeomorphism if it is one-to-one and the inverse  $\phi^{-1}$  is also smooth (it is in fact enough to check that  $\phi$  is one-to-one and that  $D\phi_y$  is invertible for all y, since that ensures smoothness of the inverse). One can think of diffeomorphisms as curvilinear coordinate changes.

THEOREM 28.2 (Inverse function theorem; no proof). Let  $\tilde{V} \subset \mathbb{R}^{n+1}$  be an open subset,  $y \in \tilde{V}$  a point, and  $\phi : \tilde{V} \to \mathbb{R}^{n+1}$  a smooth map such that  $D\phi_y$  is invertible. Then there is an open subset  $V \subset \tilde{V}$ , still containing y, such that:  $U = \phi(V)$  is open, and  $\phi|V: V \to U$  is a diffeomorphism.

COROLLARY 29.1 (Implicit function theorem, special case). Let  $\tilde{V} \subset \mathbb{R}^{n+1}$  be an open subset,  $\psi: \tilde{V} \to \mathbb{R}$  a smooth function, and  $y \in \tilde{V}$  a point such that  $\psi(y) = 0$ ,  $D\psi(y) \neq 0$ . Then there are: an open subset  $V \subset \tilde{V}$ , still containing y; an open subset  $U \subset \mathbb{R}^{n+1}$  containing 0; and a diffeomorphism  $\phi: U \to V$  such that  $\phi(0) = y$ , and  $\psi(\phi(x)) = x_{n+1}$  for all x.

The informal meaning is that in the curvilinear local coordinate system  $\phi$ ,  $\psi$  looks like a linear function.

LEMMA 29.2. Let  $U \subset \mathbb{R}^{n+1}$  be an open subset containing the origin, and  $\psi: U \to \mathbb{R}$  a smooth function which vanishes at all points  $x \in U$  whose last coordinate  $x_{n+1}$  is zero. Then there is a unique smooth function q such that  $\psi = qx_{n+1}$ .

This and the previous Corollary together imply our version of l'Hopital's theorem (Lemma 20.2).

DEFINITION 29.3. Let M be a hypersurface. A partial parametrization of M consists of an open subset  $V \subset \mathbb{R}^{n+1}$ , an open subset  $U \subset \mathbb{R}^n$ , and a hypersurface patch  $f: U \to \mathbb{R}^{n+1}$  which is one-to-one (injective), and whose image is precisely  $M \cap V$ .

COROLLARY 29.4. For every point  $y \in M$ , there is a partial parametrization such that  $y \in f(U) = M \cap V$ .

If f is a partial parametrization, the  $\partial_{x_i} f$  form a basis of  $TM_{f(x)}$  for all x. Equivalently,  $Df_x: \mathbb{R}^n \to TM_{f(x)}$  is an isomorphism (an invertible linear map). In the case where M comes with a Gauss vector field  $\nu: M \to \mathbb{R}^{n+1}$ , one can always choose these partial parametrizations to be compatible with it, which means that  $\det(\partial_{x_1} f, \ldots, \partial_{x_n} f, \nu(f(x))) > 0$ .

PROPOSITION 29.5. Let f be a partial parametrization. Denote by  $I^f$  its first fundamental form, and by  $S^f$  its shape operator. Under the identification  $Df: \mathbb{R}^n \to TM_{f(x)}, I^f$  turns into the ordinary scalar product, and  $S^f$  into the shape operator S of M.

Explicitly, the second part of this says that  $S:TM_{f(x)}\to TM_{f(x)}$  and  $S^f:\mathbb{R}^n\to\mathbb{R}^n$  are related by

$$S^f = Df^{-1} \cdot S \circ Df.$$

PROPOSITION 30.1. Let  $M \subset \mathbb{R}^{n+1}$  be a hypersurface. Take a point  $y \in M$ , a local defining function  $\psi$  for M near y, and an orthonormal basis  $Y_1, \ldots, Y_n$  of the tangent space  $TM_y$ .

$$\kappa_{mean} = \pm \frac{1}{\|\nabla \psi_y\|} \sum_{i=1}^n \langle Y_i, D^2 \psi_y \cdot Y_i \rangle,$$
  
$$\kappa_{gauss} = \pm \frac{\det(D^2 \psi_y \cdot Y_1, \dots, D^2 \psi_y \cdot Y_n, \nabla \psi_y)}{\|\nabla \psi_y\|^{n+1}}.$$

Assume that  $\nu(y) = \nabla \psi_y / \|\nabla \psi_y\|$ . Then the sign in  $\kappa_{mean}$  is -1. Assume in addition that the basis is chosen in such a way that  $\det(Y_1, \ldots, Y_n, \nabla \psi_y) > 0$ . Then the sign in  $\kappa_{gauss}$  is  $(-1)^n$ .

DEFINITION 30.2. A hypersurface  $M \subset \mathbb{R}^{n+1}$  is compact if it is bounded and closed (closedness means that if a sequence  $y_n \in M$  converges to some point  $y_\infty \in \mathbb{R}^{n+1}$ , then that point must also lie in M).

DEFINITION 30.3. A hypersurface  $M \subset \mathbb{R}^{n+1}$  is connected if every smooth function  $\phi: M \to \mathbb{R}$  whose derivative is identically zero is actually constant.

THEOREM 30.4 (from topology; no proof). A connected compact hypersurface is always orientable (in fact, there are precisely two choices of Gauss vectors, differing by a sign).

Take a connected compact hypersurface, oriented inwards. Then there is a point where all principal curvatures are > 0. Similarly, for the outwards orientation, there is a point where all principal curvatures are < 0. This follows from Example 14.3.

THEOREM 30.5 (from topology; no proof). Let  $M \subset \mathbb{R}^{n+1}$  be a connected compact hypersurface, with  $n \geq 2$ , and  $\phi: M \to S^n$  a smooth map such that  $D\phi_y: TM_y \to TS^n_{\phi(y)}$  is an isomorphism for all y. Then  $\phi$  is bijective (one-to-one and onto).

DEFINITION 30.6. A hypersurface M is convex if for all  $y \in M$ , the whole of M lies on one side of the hyperplane  $y + TM_y$ .

We already know from Example 14.2 that if M is compact connected and convex, its principal curvatures any any point are either  $\geq 0$  (for the orientation pointing inwards) or  $\leq 0$  (for the orientation pointing outwards).

THEOREM 30.7 (Hadamard). Let  $M \subset \mathbb{R}^{n+1}$ ,  $n \geq 2$ , be a compact connected hypersurface, whose Gauss curvature is everywhere nonzero. Then M is convex.

Remark 30.8. For a compact connected hypersurface M ⊂ Rn+1, n ≥ 2, the following are equivalent: (i) the Gauss curvature is everywhere nonzero; (ii) the Riemann curvature operator has only positive eigenvalues everywhere; (ii) the principal curvatures are either everywhere > 0 or everywhere < 0.

Let  $M \subset \mathbb{R}^{n+1}$  be a compact hypersurface, and  $\phi: M \to \mathbb{R}$  a smooth function. We want to quickly sketch the definition of the integral of  $\phi$ . Recall that the  $support \operatorname{supp}(\phi) \subset M$  is the closure of the set of points where  $\phi$  is nonzero. First suppose that  $\phi$  has  $small\ support$ , which means that  $supp(\phi)$  is contained in the image of a partial parametrization  $f: U \to M$ , and write  $\phi^f = \phi \circ f: U \to \mathbb{R}$ . In that case,

$$\int_{M} \phi(y) \, d\mathrm{vol}_{y} \stackrel{\mathrm{def}}{=} \int_{U} \phi^{f} \sqrt{\det(G^{f})} \, dx,$$

This makes sense because it's invariant under diffeomorphisms. For general  $\phi$ , there are two equivalent ways: either write it as  $\phi = \phi_1 + \cdots + \phi_m$  where each  $\phi_i$  has small support. Then,

$$\int_{M} \phi(y) \, d\mathrm{vol}_{y} \stackrel{\mathrm{def}}{=} \sum_{i=1}^{m} \int_{M} \phi_{i}(y) \, d\mathrm{vol}_{y}.$$

Alternatively, suppose that M is decomposed into polytopes in the following sense. There is a collection of partial parametrizations  $f_i: U_i \to M$  and polytopes  $P_i \subset U_i$   $(1 \le i \le m)$ , such that  $M = f_1(P_1) \cup \cdots \cup f_m(P_m)$ , and with the interiors  $f_i(P_i \setminus \partial P_i)$  pairwise disjoint. Then

$$\int_{M} \phi(y) \, d\text{vol}_{y} \stackrel{\text{def}}{=} \sum_{i=1}^{m} \int_{P_{i}} \phi^{f_{i}} \sqrt{\det(G^{f_{i}})} \, dx,$$

where  $\phi^{f_i}$  and  $G^{f_i}$  are defined as before.

LEMMA 31.1. Let f be a partial parametrization, and  $\nu^f$  the associated Gauss normal. Then  $\det(G^f) = \det(\partial_{x_1} f, \dots, \partial_{x_n} f, \nu^f)^2$ . In particular, in the case of a surface,

$$\sqrt{\det(G^f)} = \|\partial_{x_1} f \times \partial_{x_2} f\|.$$

Example 31.2. The volume of M is defined as  $\operatorname{vol}(M) = \int_M 1 d\operatorname{vol}$ .

Let  $M, \tilde{M}$  be hypersurfaces in  $\mathbb{R}^{n+1}$ , and  $\phi: M \to \tilde{M}$  a smooth map. Suppose that both our hypersurfaces come with Gauss normal vectors  $\nu, \tilde{\nu}$ . We then define  $\det(D\phi_y)$  by writing  $D\phi_y: TM_y \to T\tilde{M}_{\phi(y)}$  in terms of orthonormal bases of those vector spaces which are compatible with the orientation. This means:

DEFINITION 31.3. In the situation above, let  $(X_1, \ldots, X_n)$  be a basis of  $TM_y$  such that  $\det(X_1, \ldots, X_n, \nu(y)) > 0$ , and  $(Y_1, \ldots, Y_n)$  a basis of  $T\tilde{M}_{\phi(y)}$  such that  $\det(Y_1, \ldots, Y_n, \tilde{\nu}(\phi(y))) > 0$ . Take the matrix A such that  $D\phi_y(X_i) = \sum_j A_{ji}Y_j$ , and define  $\det(D\phi_y) = \det(A)$ . This is independent of the choices of bases

Example 31.4. Consider the Gauss map ν : M M˜ = Sn, where S → <sup>n</sup> carries a Gauss normal vector ν(y) = y. Then det(Dνy) is (−1)<sup>n</sup> times the Gauss curvature of M at y.

LEMMA 32.1. Let  $M, \tilde{M}$  be hypersurfaces, with Gauss maps  $\nu, \tilde{\nu}$ , and  $\phi: M \to \tilde{M}$  be a smooth map. Suppose that we have a parametrization  $f: U \to M$  compatible with the orientation. Set  $\phi^f = \phi \circ f: U \to \tilde{M} \subset \mathbb{R}^{n+1}$ , and let  $G^f$  be the first fundamental form. Then for y = f(x),

$$\det(D\phi)_y = \frac{\det(\partial_{x_1}\phi^f, \dots, \partial_{x_n}\phi^f, \tilde{\nu}(\phi^f(x)))}{\sqrt{\det(G^f(x))}}.$$

DEFINITION 32.2. Let  $M, \tilde{M}$  be compact hypersurfaces equipped with Gauss maps. Assume that  $\tilde{M}$  is connected. Let  $\phi: M \to \tilde{M}$  be a smooth map. The degree of  $\phi$  is defined as

$$\deg(\phi) = \frac{1}{\operatorname{vol}(\tilde{M})} \int_{M} \det(D\phi_y) \, d\operatorname{vol}_y.$$

PROPOSITION 32.3. Suppose that  $\tilde{M}$  is decomposed into  $f_i(P_i)$  as in the previous lecture, where  $f_i: U_i \to M$  are partial parametrization, and  $P_i \subset U_i$  polytopes. Then

$$\deg(\phi) = \frac{1}{\operatorname{vol}(\tilde{M})} \left( \sum_{i} \int_{P_i} \det(\partial_{x_1} \phi^{f_i}, \dots, \partial_{x_n} \phi^{f_i}, \tilde{\nu}(\phi(f_i(x)))) \, dx \right).$$

where  $\phi^{f_i} = \phi \circ f_i$ .

LEMMA 32.4 (Sketch proof). Suppose that  $\phi$  is bijective (one-to-one and onto), and that  $\det(D\phi)$  is everywhere positive (or everywhere negative). Then  $\deg(\phi) = 1$  (or -1).

THEOREM 32.5 (No proof). The degree is always an integer.

Example 33.1. Let  $M \subset \mathbb{R}^3$  be a torus, parametrized by

$$f(x_1, x_2) = ((\cos x_1)(2 + \cos x_2), (\sin x_1)(2 + \cos x_2), \sin x_2)$$

In this parametrization, the first fundamental form is

$$G = \begin{pmatrix} (2 + \cos x_2)^2 & 0\\ 0 & 1 \end{pmatrix},$$

hence  $\sqrt{\det G} = 2 + \cos x_2$  and

$$\operatorname{vol}(M) = 8\pi^2$$
.

Take the map  $\phi: M \to M$  which wraps the torus twice around itself, sending  $f(x_1, x_2)$  to  $f(2x_1, x_2)$ . Then  $\det(D\phi) = 2$  everywhere, hence  $\deg(\phi) = 2$ .

Now consider the map  $\tilde{\phi}: M \to M$  wrapping the other way, which means that it sends  $f(x_1, x_2)$  to  $f(x_1, 2x_2)$ . With respect to the orthonormal basis  $(\partial_{x_1} f/(2 + \cos x_2), \partial_{x_2} f)$ , we have

$$D\tilde{\phi}_{f(x_1,x_2)} = \begin{pmatrix} \frac{2+\cos 2x_2}{2+\cos x_2} & 0\\ 0 & 2 \end{pmatrix},$$

hence  $\det(D\tilde{\phi})_{f(x_1,x_2)} = 4\frac{1+\cos x_2}{2+\cos x_2}$ , and

$$\int_{M} \det(D\tilde{\phi}) \, d\text{vol} = \int_{[0,2\pi] \times [0,2\pi]} 4(1 + \cos x_2) = 16\pi^2,$$

which means that again  $\deg(\tilde{\phi}) = 2$ . One can get the same integral formula a little more easily by using Proposition 26.3.

Since the degree is an integer, it is constant under smooth deformations of a map. By applying this idea (called the *homotopy method*), we get:

LEMMA 33.2. Let  $M \subset \mathbb{R}^{n+1}$  be a compact hypersurface with a Gauss map, and  $\phi: M \to S^n$  a smooth map. If  $\deg(\phi) \neq 0$ , then  $\phi$  is necessarily onto.

The result generalizes to targets other than  $S^n$ , and there is an even more general formula:

THEOREM 33.3 (no proof). Let  $M, \tilde{M} \subset \mathbb{R}^{n+1}$  be compact connected hypersurfaces with orientations, and  $\phi: M \to \tilde{M}$  a smooth map. Suppose that  $p \in \tilde{M}$  is a point with the following properties: (i) there are only finitely many  $y_1, \ldots, y_k \in M$  such that  $\phi(y_i) = p$ ; (ii) at each  $y_i$ , we have  $\det(D\phi_{y_i}) \neq 0$ . Then

$$\deg(\phi) = \sum_{i=1}^{k} \operatorname{sign}(\det(D\phi_{y_i})).$$

Definition 33.4. Let M be a compact hypersurface with an orientation. The  $total\ Gauss\ curvature$  is

$$\kappa_{gauss}^{tot} = \int_{M} \kappa_{gauss} \, d\text{vol}.$$

For even-dimensional hypersurfaces, the choice of orientation is actually irrelevant. If we take  $\phi = \nu : M \to S^n$  to be the Gauss map, and orient  $S^n$  pointing outwards, then  $\det(D\phi_y) = \det(-L_y) = (-1)^n \kappa_{gauss}$ , hence:

COROLLARY 33.5. Let M be a compact hypersurface with an orientation. Then

$$\kappa_{gauss}^{tot} = (-1)^n \operatorname{vol}(S^n) \operatorname{deg}(\nu).$$

In particular, the total Gauss curvature is always an integer multiple of  $vol(S^n)$ .

We already saw that if  $M \subset \mathbb{R}^3$  is a torus, then  $\kappa_{gauss}^{tot} = 0$ , irrespective of how it's embedded. To generalize this to other surfaces, we need to return to our discussion of moving frames.

DEFINITION 34.1. Let  $f: U \to \mathbb{R}^3$  be a surface patch, whose domain contains the origin. Let  $(X_1, X_2)$  be a moving frame defined on  $U \setminus \{0\}$ . We say that the frame has a *singularity of multiplicity*  $m \in \mathbb{Z}$  at 0 if it can be written as

$$X_1 = \cos(m\theta)\tilde{X}_1 - \sin(m\theta)\tilde{X}_2,$$
  

$$X_2 = \sin(m\theta)\tilde{X}_1 + \cos(m\theta)\tilde{X}_2,$$

where  $\theta$  is the angular coordinate, and  $(\tilde{X}_1, \tilde{X}_2)$  is a moving frame which extends smoothly over x = 0. Passing to the matrices whose column vectors are the  $X_k$  and  $\tilde{X}_k$ , one can write the relation as

$$X = \tilde{X} \exp(m\theta J),$$

where  $J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$  as usual.

Let X be a moving frame with a singularity of order m. Last time we considered the vector field

$$\alpha = ((A_1)_{12}, (A_2)_{12}) : U \setminus \{0\} \to \mathbb{R}^2,$$

which was such that  $\operatorname{curl}(\alpha) = \kappa_{gauss} \sqrt{\det(G)}$ . A computation shows that

$$\alpha = m(x_2, -x_1)/||x||^2 + something bounded in x,$$

and therefore:

Lemma 34.2.

$$\lim_{\rho \to 0} \oint_{|x|=\rho} \alpha = -2\pi m.$$

DEFINITION 34.3. Let  $M \subset \mathbb{R}^3$  be a compact surface. A moving frame with singularities is given by a finite set of points  $\{p_1, \ldots, p_k\}$  on M, together with maps  $Y_1, Y_2 : M \setminus \{p_1, \ldots, p_k\} \to \mathbb{R}^3$  which at each point y form a positively oriented orthonormal basis of TM, and such that around each  $p_k$  there is a partial parametrization in which  $Y_j = Df(X_j)$  for some frame with singularity of order  $m(p_i)$  at p.

THEOREM 34.4 (no proof). Moving frames with singularities always exist. Moreover, for any choice of such frame, the sum  $\sum_i m(p_i)$  is the same. It agrees with a topological invariant of M, called the Euler characteristic  $\chi(M)$ .

The torus has Euler characteristic 0. More interestingly, the sphere has Euler characteristic 2.

COROLLARY 34.5 (Gauss-Bonnet theorem; sketch proof). For any compact surface  $M \subset \mathbb{R}^3$ ,  $\kappa_{gauss}^{tot} = 2\pi \cdot \chi(M)$ .

COROLLARY 34.6. The Gauss map  $\nu$  of a compact surface  $M \subset \mathbb{R}^3$  satisfies  $\chi(M) = 2 \operatorname{deg}(\nu)$ . In particular,  $\chi(M)$  is always even.

There is also a direct topological proof of this, avoiding curvature. Note that there exist abstract compact surfaces (compact topological spaces locally homeomorphic to  $\mathbb{R}^2$ ) with odd Euler characteristic, but those do not admit orientations, hence cannot be realized inside  $\mathbb{R}^3$ .

COROLLARY 34.7 (sketch proof). For any compact surface  $M \subset \mathbb{R}^3$ ,  $\int_M \|\kappa\| dvol_M \ge 4\pi$ .

The Euler characteristic  $\chi(M)$  is defined for all sufficiently nice topological spaces, and in particular for compact hypersurfaces M of any dimension. It is an intrinsic quantity (a homeomorphism invariant). We do not give the definition here, except to mention that if M admits a moving frame without any singularities, then the Euler characteristic is zero.

THEOREM 35.1 (Hopf; no proof). Let  $M \subset \mathbb{R}^{n+1}$  be a closed hypersurface of even dimension n, and  $\nu: M \to S^n$  a Gauss map. Then  $\deg(\nu) = \chi(M)/2$ .

COROLLARY 35.2 (Generalized Gauss-Bonnet). In the same situation as above,  $\kappa_{qauss}^{tot} = \chi(M) \text{vol}(S^n)/2$ .

No such result exists for odd n, which means that  $\kappa_{gauss}^{tot}$  is not intrinsic in those dimensions (it depends on how the hypersurface sits in  $\mathbb{R}^{n+1}$ ).

DEFINITION 35.3. A compact combinatorial surface consists of a finite collection  $\{P_i\}$  of flat convex polygons in  $\mathbb{R}^3$ , with the following properties: any two  $P_i$  are either disjoint or share a common edge; (ii) any edge of any given  $P_i$  belongs to precisely one other  $P_j$ ,  $j \neq i$ .

We usually think of  $M = \bigcup_i P_i$  as the surface. Write  $\{E_j\}$  for the set of edges, and  $\{V_k\}$  for the set of vertices. The combinatorial Gauss map assigns to each  $P_i$  a normal vector  $\nu(P_i) \in S^2$ , uniquely determined by the requirement that it should point outwards (if M is connected, this means pointing into the component of  $\mathbb{R}^3 \setminus M$  which is not bounded). For each edge  $E_j$  we then get a great circle segment  $\nu(E_j) \subset S^2$  connecting the normal vectors associated to its endpoints. Similarly, for each vertex  $V_k$  we get a "region"  $\nu(V_k) \subset S^2$  whose boundaries are the great circle segments associated to the edges adjacent to each vertex. The combinatorial Gauss curvature is the spherical area

$$\kappa_{gauss}^{comb}(V_k) = \text{``area}(\nu(V_k))\text{''}.$$

This has to be approached with some care, since the "region" can have self-overlaps, and the area should be counted with sign. In the case of a convex vertex, one really gets the ordinary positive area. More generally, one can use some spherical trigonometry to get

$$\kappa_{gauss}^{comb}(V_k) = 2\pi - \sum \text{angles of corners adjacent to our vertex},$$

where the angles are counted with signs. Define the Euler characteristic to be  $\chi(M) = \#\text{polygons} - \#\text{edges} + \#\text{vertices}$  (for a polygonal approximation of a smooth surface, this agrees with our previous definition). By applying spherical trigonometry, one obtains

THEOREM 35.4 (combinatorial Gauss-Bonnet; sketch proof).  $\sum_k \kappa_{gauss}^{comb}(V_k) = 2\pi\chi(M)$ .

---

MIT OpenCourseWare <http://ocw.mit.edu>

18.950 Differential Geometry Fall 2008

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

## CHAPTER 4

# Geometry of lengths and distances

Let's start by looking at standard  $\mathbb{R}^n$ . Straight lines are distinguished by being the shortest lines joining two points. More precisely,

LEMMA 36.1. Let  $\gamma:[a,b]\to\mathbb{R}^n$  be a smooth path, with  $\gamma(a)=p$  and  $\gamma(b)=q$ . Its length  $L(\gamma)=\int_a^b\|\gamma'(t)\|\,dt$  is  $\geq \|q-p\|$ , and equality holds iff  $\gamma'(t)$  is always a nonnegative multiple of q-p.

Straight lines also appear in mechanics, from three equivalent viewpoints:

- From a Newtonian point of view, a unit mass particle moves according to x''(t) = F. If the force F vanishes, the solution  $\gamma(t)$  is a constant speed straight line.
- From a Lagrangian point of view, the straight line comes about because we are trying to minimize the Lagrange functional  $\int_a^b \mathcal{L}(x, x') dt$ . For free motion  $\mathcal{L}(x, x') = \frac{1}{2} ||x'||^2$ , which produces the same equations of motion as before (this viewpoint is closely related to length minimization).
- From the Hamiltonian (conjugate variable) point of view, the particle position and momentum (x(t), p(t)) satisfy  $x_i'(t) = \partial_{p_i} H(x, p)$ ,  $p_i'(t) = -\partial_{x_i} H(x, p)$ . In the free case the Hamiltonian is  $H(x, p) = \frac{1}{2} ||p||^2$ .

DEFINITION 36.2. Let  $M \subset \mathbb{R}^{n+1}$  be a hypersurface. A smooth map  $\gamma: I \to M$ , where  $I \subset \mathbb{R}$  is an interval, is called a *geodesic* if  $\gamma''(t)$  is perpendicular to  $TM_{\gamma(t)}$  for all t.

Remember that  $\gamma'(t) \in TM_{\gamma(t)}$ , essentially by definition of tangent space. Geodesics are curves held to M by a constraint force.

LEMMA 36.3. If  $\gamma$  is a geodesic, the speed  $\|\gamma'(t)\|$  is constant.

PROPOSITION 36.4. Let  $f: U \to \mathbb{R}^{n+1}$  be a partial parametrization of M, and  $c: I \to U$  a smooth curve on its domain. Then  $\gamma = f(c)$  is a geodesic iff c itself satisfies the *geodesic equation* 

$$\frac{d^2c_k}{dt^2} + \sum_{ij} \Gamma_{ij}^k \frac{dc_i}{dt} \frac{dc_j}{dt} = 0.$$

Importantly, this equation contains only intrinsic quantities.

COROLLARY 36.5 (proof sketched). Two geodesics  $\gamma, \tilde{\gamma}: I \to M$  with  $\gamma(0) = \tilde{\gamma}(0)$  and  $\gamma'(0) = \tilde{\gamma}'(0)$  agree.

COROLLARY 36.6 (proof sketched). Given any point  $y \in M$  and any tangent vector  $Y \in TM_y$ , there is an interval  $I \subset \mathbb{R}$  containing 0 and a geodesic

 $\gamma: I \to \mathbb{R}$  such that  $\gamma(0) = y$ ,  $\gamma'(0) = Y$ . If M is a closed subset of  $\mathbb{R}^{n+1}$ , one can take  $I = \mathbb{R}$ , which means that geodesics are defined for all times.

EXAMPLES 36.7. (i) The nontrivial geodesics on  $S^n$  are just the great circles, parametrized with arbitrary constant speed. More explicitly, take  $u, v \in S^n$  which are orthogonal to each other, and write  $\gamma(t) = \cos(\alpha t)u + \sin(\alpha t)v$ , where  $\alpha \in \mathbb{R}$  is any constant.

- (ii) Take the infinite cylinder  $M=\{x\in\mathbb{R}^3: x_2^2+x_3^2=1\}$ . Geodesics on this are just spirals,  $\gamma(t)=(a_1t+b_1,\cos(a_2t+b_2),\sin(a_2t+b_2))$ .
- (iii) If the hypersurface M contains a straight line, that straight line is a geodesic.

EXAMPLE 37.1. Let  $M \subset \mathbb{R}^3$  be a surface which is invariant under the reflection  $x \mapsto (x_1, x_2, -x_3)$ , and is not contained in the plane  $x_3 = 0$ . Then any path in M which is contained in the plane  $x_3 = 0$  and parametrized with constant speed, is a geodesic.

EXAMPLE 37.2. Let  $M \subset \mathbb{R}^3$  be a surface of rotation, parametrized by  $f(x_1, x_2) = (l_1(x_1) \cos x_2, l_1(x_1) \sin x_2, l_2(x_1))$ , where l is a unit speed curve in the plane. Then the geodesic equation is

$$c_1''(t) - l_1(c_1)l_1'(c_1)c_2'(t)^2 = 0,$$
  

$$c_2''(t) + 2\frac{l_1'(c_1)}{l_1(x_1)}c_1'(t)c_2'(t) = 0.$$

Particular solutions are where  $x_2$  is constant, or where  $x_1$  is constant at a value where  $l'_1(x_1) = 0$ .

Consider a hypersurface  $M \subset \mathbb{R}^{n+1}$ , but where now  $\mathbb{R}^{n+1}$  carries the Minkowski inner product. We assume that M is space-like, which means that the restriction of  $\langle \cdot, \cdot \rangle_{Min}$  to  $TM_y$  is positive definite for all y. A geodesic is then a curve  $\gamma(t)$  such that  $\gamma''(t)$  is Minkowski-orthogonal to  $TM_{\gamma(t)}$  for all t. In a local parametrization, this satisfies the same geodesic equation as before.

Consider the hyperbolic plane  $H^2 = \{x_1 > 0, \langle x, x \rangle_{Min} = -x_1^2 + x_2^2 + x_3^2 = -1\}$ . Take two vectors  $u, v \in \mathbb{R}^3$  which satisfy  $u_1 > 0$ ,  $\langle u, u \rangle_{Min} = -1$ ,  $\langle v, v \rangle_{Min} = +1$ ,  $\langle u, v \rangle_{Min} = 0$ . Then

$$\gamma(t) = \cosh(\alpha t)u + \sinh(\alpha t)v$$

for any  $\alpha \in \mathbb{R}$ , is a geodesic, and these are all the geodesic on the hyperbolic plane. If  $\alpha \neq 0$ , the image of  $\gamma$  is just the intersection of  $H^n$  with the plane spanned by u,v. Note that unlike the sphere, non-constant geodesic go to infinity as  $t \to \infty$ .

If we parametrize projective space as in the Klein or projective ball model, the geodesics become straight line segments (their speed, obviously, is not constant). In the parametrization by the Poincaré ball model, they become circle segments which intersect the boundary of ball perpendicularly (on, in the limiting case, a line segment through the center of our ball).

This lecture covers the "Lagrangian" and "Hamiltonian" viewpoints on geodesics, each of which is important in its own right. Let  $M \subset \mathbb{R}^{n+1}$  be a hypersurface, and  $\gamma : [a, b] \to M$  a path. We define its energy to be

$$E(\gamma) = \frac{1}{2} \int_{a}^{b} \|\gamma'(t)\|^{2} dt.$$

Then the following variational principle holds:

THEOREM 38.1 (proof sketched). A curve  $\gamma:[a,b]\to M$  is a geodesic if and only if the following holds. For any smooth family of paths  $(\gamma_s)$ ,  $-\epsilon < s < \epsilon$ , with the same endpoints  $\gamma_s(a) = p$ ,  $\gamma_s(b) = q$  and with  $\gamma_0 = \gamma$ , we have

$$\left. \frac{\partial}{\partial s} E(\gamma_s) \right|_{s=0} = 0.$$

COROLLARY 38.2. A path which is an absolute minimizer of the energy (over all paths  $\gamma:[a,b]\to M$  with fixed endpoints  $\gamma(a)=p,\ \gamma(b)=q)$ , is necessarily a geodesic.

Note that the converse to the Corollary does not hold. There are geodesics (on the sphere, for instance) which are not absolute energy minimizers.

THEOREM 38.3 (no proof). Suppose that M is closed and connected. Then, for any given p,q and any interval [a,b], there is a geodesic  $\gamma:[a,b]\to M$  which is an absolute minimizer of the energy.

This provides a practical way of finding geodesics *numerically*, by applying some minimization method to the energy functional.

Now consider a partial parametrization  $f: U \to \mathbb{R}^{n+1}$  of M, and its associated first fundamental form  $G = (g_{ij})$ . In this local coordinate system, the geodesic equations (using the intrinsic formula for Christoffel symbols) can be written as

$$\sum_{k} g_{kl} x_l'' = \frac{1}{2} \sum_{ij} x_i' x_j' \partial_{x_l} g_{ij} - \sum_{ij} x_i' x_j' \partial_{x_i} g_{jl}.$$

Decoupling them by introducing new variables  $v_1, \ldots, v_n$  yields

$$x'_k = v_k,$$

$$\sum_k g_{kl} v'_l = \frac{1}{2} \sum_{ij} v_i v_j \partial_{x_l} g_{ij} - \sum_{ij} v_i v_j \partial_{x_i} g_{jl}.$$

PROPOSITION 38.4. Write the equations above in conjugate variables  $x_k$  (position) and  $p_k = \sum_l g_{kl}(x)v_l$  (momentum). Then they take on the Hamiltonian for

tonian for 
$$\begin{cases} x_k' = \frac{\partial H}{\partial p_k}, \\ p_k' = -\frac{\partial H}{\partial x_k}, \end{cases}$$
 where  $H = \frac{1}{2}I(v,v) \quad \frac{1}{2}\langle p, G^{-1}(x) \cdot p \rangle = \frac{1}{2}\sum_{ij}p_ig^{ij}(x)p_j.$ 

This allows one to apply general methods from mechanics, such as Noether's theorem (any continuous symmetry implies the existence of a conserved quantity).

Let  $M \subset \mathbb{R}^{n+1}$  be a hypersurface. The length of a path  $\gamma: [a,b] \to M$  is

$$L(\gamma) = \int_a^b \|\gamma'(t)\| dt.$$

Define the distance  $\operatorname{dist}(p,q) = \inf_{\gamma} L(\gamma)$ , where the infimum is taken over all paths from p to q.

LEMMA 39.1. If M is a connected hypersurface, then (M, dist) is a metric space. By this we mean that it satisfies the following axioms:

 $dist(p,q) \ge 0$ , with equality if and only if p = q.

dist(p,q) = dist(q,p),

 $dist(p,q) \le dist(p,r) + dist(r,q).$ 

PROPOSITION 39.2 (part of the Cauchy-Schwarz inequality; no proof). Let  $f:[a,b]\to\mathbb{R}$  be a function. Then

$$\int_{a}^{b} f(t) dt \le \sqrt{b - a} \sqrt{\int_{a}^{b} f(t)^{2} dt},$$

with equality if and only if f is constant.

COROLLARY 39.3. For any path  $\gamma:[a,b]\to M$ , we have  $L(\gamma)\leq 2^{1/2}(b-a)^{1/2}E(\gamma)^{1/2}$ , with equality if and only if  $\gamma$  has constant speed.

COROLLARY 39.4. If we fix the endpoints  $\gamma(a) = p$ ,  $\gamma(b) = q$ , a path is an absolute energy-minimizer if and only if it is an absolute length-minimizer and is parametrized with constant speed.

COROLLARY 39.5. Let M be a closed connected hypersurface. Then, for any two points p, q there is a path  $\gamma$  connecting them, such that  $L(\gamma) = \text{dist}(p, q)$ . In other words, the infimum in the definition of distance is always attained.

Given a parametrization  $f: U \to M$  with first fundamental form I, one can define the lengths of paths  $c: [a,b] \to U$  to be equal to the length of their image  $\gamma = f(c)$ . Concretely,

$$L(c) = \int_{a}^{b} \sqrt{I_{c(t)}(c'(t), c'(t))} dt.$$

As before, there is an associated notion of distance. As an example, consider the Poincaré parametrization of the hyperbolic plane. We identify  $\mathbb{R}^2 = \mathbb{C}$ , with one complex coordinate  $z = x_1 + ix_2$ , so that  $U = \{z \in \mathbb{C} \ , \ |z| < 1\}$ . Then

$$G(z) = \frac{4}{(1-|z|^2)^2} \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}.$$

Lemma 39.6 (partial proof). For z, w ∈ U, the distance in the hyperbolic metric is

$$\operatorname{dist}(z, w) = 2\operatorname{arctanh} \frac{|z - w|}{|\bar{w}z - 1|}.$$

There is an interesting connection with complex geometry.

Theorem 39.7. (Schwarz-Pick) Let h : U → U be a holomorphic (complex differentiable) function. Then at every point z ∈ U,

$$|h'(z)| \le \frac{1 - |h(z)|^2}{1 - |z|^2}.$$

Corollary 39.8. For h as before,

$$I_{h(z)}(Dh(z)X, Dh(z)X) \le I_z(X, X).$$

Corollary 39.9. Any holomorphic function h : U U is distance-nonincreasing for the hyperbolic metric: dist(h(p), h(q)) ≤ → dist(p, q).

Let (X, d) be a metric space. This means that X is a set, and d : X ×X → R a function satisfying the three axioms from the last lecture. In particular, this allows one to define continuous functions, maps, etc.

Definition 40.1. A continuous path γ : [a, b] X is called a metric geodesic if d(γ(s), γ(t)) = |s − t| for all s,t ∈ [a, b]. →

Example 40.2. In the traditional case of hypersurfaces, metric geodesics are precisely unit speed geodesics which are absolute distance-minimizers.

A metric space is called geodesic if any two points can be joined by a metric geodesic.

Definition 40.3. Let X be a geodesic metric space. X is called nonpositively curved in the sense of Busemann (or a Busemann space) if it has the following property. Whenever γ1, γ<sup>2</sup> : [0, l] → X are metric geodesics starting at the same point γ1(l) = γ2(l), then we have

$$d(\gamma_1(t), \gamma_2(t)) \le (t/l) d(\gamma_1(l), \gamma_2(l)).$$

Example 40.4. Euclidean space Rn, as well as hyperbolic space Hn, are nonnegatively curved in the sense of Busemann. For the latter, the distance function along two geodesics with the same starting point is

$$d(\gamma_1(t), \gamma_2(t)) = \alpha \operatorname{arctanh}(1/\tanh(t)).$$

for some constant α, which is a convex function.

Example 40.5. Any metrized tree is nonnegatively curved in the sense of Busemann.

Example 40.6. A combinatorial surface in R<sup>3</sup> is Busemann if and only if it is topologically simply-connected (any continuous loop can be filled in by a continuous disc), and the total angle at any vertex is ≥ 2π.

Lemma 40.7. Any two points in a Busemann space are joined by a unique metric geodesic.

There is also a stronger and more useful notion, due to Alexandrov. For any geodesic triangle Δ in X with corners p, q, r, consider the comparison triangle Δ� in R<sup>2</sup> with corners p� , q� , r� , characterized by having sides of the same length: d(p, q) = �p� − q� �, d(p, r) = �p� − r� �, d(q, r) = �q� − r� �. For any point on any of the sides of Δ, there is a unique corresponding point of Δ� , characterized by having the same distance from the two adjacent corners.

Definition 40.8. Let X be a geodesic metric space. X is called nonpositively curved in the sense of Cartan-Alexandrov-Topogonov (or an CAT space) if for all Δ, Δ� and all points x, y on the boundary of Δ, with comparison points x� , y� , we have dist(x, y) ≤ dist(x� , y� ).

All examples listed above are in fact CAT (which implies Busemann). There are also important local versions of all the notions in this lecture, where the conditions are assumed to hold only locally ("for every point x ∈ X there exists an open subset U ⊂ X containing x, such that...").

References: Burago-Burago-Ivanov, A course in metric geometry; Bridson-Haefliger, Metric spaces of non-positive curvature; Papadopoulos, Metric spaces, convexity, and nonpositive curvature.

Let  $M \subset \mathbb{R}^3$  be a surface, with a Gauss map  $\nu : M \to S^2$ . Suppose that  $\gamma : I \to M$  is a regular curve, which as usual means  $\gamma'(t) \neq 0$  for all  $t \in I$ .

DEFINITION 41.1. The geodesic curvature of  $\gamma$  is defined by

$$\kappa_{geod}(t) = \frac{\det(\gamma'(t), \gamma''(t), \nu(\gamma(t)))}{\|\gamma'(t)\|^3}.$$

The geodesic curvature is reparametrization invariant. If  $M = \mathbb{R}^2 \times \{0\}$  with  $\nu(x_1, x_2, 0) = (0, 0, 1)$ , it specializes to the ordinary curvature of a plane curve. On the other hand, if we only look at curves which are parametrized with constant speed. Then  $\kappa_{qeod}$  vanishes identically iff  $\gamma$  is a geodesic.

Suppose that we have, at each point of M, a positively oriented orthonormal basis  $(Y_1(y), Y_2(y), Y_3(y))$  such that  $Y_3 = \nu$  everywhere, and  $Y_1(\gamma(t)) = \gamma'(t)/\|\gamma'(t)\|$ . Then

$$\kappa_{geod}(t) = \frac{\langle Y_2(\gamma(t)), (d/dt)Y_1(\gamma(t))\rangle}{\|\gamma'(t)\|}.$$

LEMMA 41.2. Take a partial parametrization  $f: U \to M \subset \mathbb{R}^3$  which is compatible with our choice of orientation, and let  $\gamma = f(c)$ . Suppose that we have a moving frame  $(X_1(x), X_2(x))$  which is positively oriented, and such that  $X_1(c(t)) = c'(t)/I_{c(t)}(c'(t), c'(t))^{1/2}$ . Then, in terms of the associated connection matrices,

$$\kappa_{geod}(t) = \frac{(A_1)_{12}c_1'(t) + (A_2)_{12}c_2'(t)}{I_{c(t)}(c'(t),c'(t))^{1/2}}.$$

Theorem 41.3 (Gauss-Bonnet with boundary, for discs; proof sketched). Let  $M \subset \mathbb{R}^3$  be a surface, and  $f: U \to M$  a partial parametrization, and  $D \subset U$  a curvilinear disc. Take the simple closed curve c which parametrizes the boundary of D, and consider the total geodesic curvature of  $\gamma = f(c)$ . This satisfies

$$\kappa_{geod}^{tot} = \int \kappa_{geod}(t) I_{c(t)}(c'(t), c'(t))^{1/2} dt = 2\pi - \int_D \kappa_{gauss} \sqrt{\det G} dx,$$

where G is the first fundamental form.

For a more general domain with boundary  $S \subset M$ , one gets an equality

$$\kappa_{geod}^{tot} = 2\pi \chi(S) - \int_{S} \kappa_{gauss} \, dvol.$$

More classical is the case of a geodesic triangle with corners:

Corollary 41.4 (proof sketched). Let M ⊂ R<sup>3</sup> be a surface, f : U → M a partial parametrization, and T ⊂ U a curvilinear triangle, whose sides map to geodesics in M. Let α1, α2, α<sup>3</sup> be the angles at the corners of the triangle, measured with respect to the first fundamental form. Then

$$\alpha_1 + \alpha_2 + \alpha_3 = \pi + \int_T \kappa_{gauss} \sqrt{\det G} \, dx.$$
