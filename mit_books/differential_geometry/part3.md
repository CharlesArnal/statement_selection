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