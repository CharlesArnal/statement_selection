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