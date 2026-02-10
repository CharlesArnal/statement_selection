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