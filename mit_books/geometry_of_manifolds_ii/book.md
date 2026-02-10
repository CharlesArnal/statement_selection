# SYMPLECTIC GEOMETRY, LECTURE 1

Prof. Denis Auroux

## 1. Differential forms

Given M a smooth manifold, one has two natural bundles: the tangent bundle  $TM = \{v = \sum v_i \frac{\partial}{\partial x_i}\}$  and the cotangent bundle  $T^*M = \{\alpha = \sum \alpha_i dx_i\}$ . Under  $C^{\infty}$  maps, tangent vectors pushforward:

$$f: M \to N \implies f_*(v) = df(v) \in T_{f(v)}N$$

Similarly, differential forms pull back:  $f^*(\alpha) = \alpha \circ df \in T_p^*M$ .

**Definition 1.** A differential p-form is a section of  $\bigwedge^p T^*M$ . We denote the set of such sections as

(2) 
$$\Omega^p(M) = \Omega^p(M, \mathbb{R}) = C^{\infty}(\bigwedge^p T^*M)$$

Recall that, for E a vector space,  $\bigwedge^* E = \bigotimes^* E/\{e_i \wedge e_j + e_j \wedge e_i = 0\}$ . Furthermore,  $\bigwedge^* E$  has a basis  $e_{i_1} \wedge \cdots \wedge e_{i_p}$ ,  $i_1 < \cdots < i_p$ . In coordinates, a p-form is locally

(3) 
$$\alpha = \sum_{i_1 < \dots < i_p} \alpha_{i_1, \dots, i_p} dx_{i_1} \wedge \dots \wedge dx_{i_p}$$

where the  $\alpha_{i_1,\dots,i_p}$  are  $C^{\infty}$  functions. (Under coordinate changes,  $x_i = f_i(y_1,\dots,y_n)$ , one replaces  $dx_i$  by  $df_i = \sum_j \frac{\partial f_i}{\partial y_j} dy_j.$ 

**Definition 2.** The exterior differential is the map  $d: \Omega^p \to \Omega^{p+1}$  which maps:

- For f a function,  $df = \sum \frac{\partial f}{\partial x_i} dx_i$ .  $d(f dx_{i_1} \wedge \cdots \wedge dx_{i_p}) = df \wedge dx_{i_1} \wedge \cdots \wedge dx_{i_p}$ .

d is obtained by extending  $\mathbb{R}$ -linearly to all of  $\Omega^p$ .

Note that d satisfies  $d(f\alpha) = f d\alpha + df \wedge \alpha$ . The exterior derivative has the following properties:

- $d(\alpha \wedge \beta) = (d\alpha) \wedge \beta + (-1)^{\text{deg } \alpha} \alpha \wedge d\beta$ . In coordinates,
- $d((fdx_{i_1} \wedge \cdots \wedge dx_{i_p}) \wedge (gdx_{j_1} \wedge \cdots \wedge dx_{j_q})) = (fdg + gdf) \wedge dx_{i_1} \wedge \cdots \wedge dx_{i_p} \wedge dx_{j_1} \wedge \cdots \wedge dx_{j_q})$ 
  - $d^2 = 0$ . For any function f,

(5) 
$$d^2 f = \sum_{i,j} \frac{\partial^2 f}{\partial x_j \partial x_i} dx_i \wedge dx_j = 0$$

because terms with switched i, j cancel.

These two properties give us the structure of a differential graded algebra on  $\Omega^*(M) = \bigoplus_n \Omega^p(M)$ .

•  $\forall \phi \in C^{\infty}(M, N), \alpha \in \Omega^p(N), \phi^*(d\alpha) = d(\phi^*\alpha).$ 

Other operations:

- For  $v \in C^{\infty}(TM)$  a vector field,  $\alpha \in \Omega^p(M)$  a form, we have the interior product  $i_v\alpha = \alpha(v, \cdots) \in$
- For  $X \in C^{\infty}(TM)$  a vector field,  $f \in C^{\infty}(M)$ , we have the Lie derivative  $X \cdot f = L_X f = i_X df = df(X)$ . If X generates diffeomorphisms  $\phi^t$  on M with  $\phi^0(x) = x$  and  $\frac{d}{dt}\phi^t(x) = X(\phi^t(x))$ , then

(6) 
$$\frac{d}{dt}((\phi^t)^*f) = \frac{d}{dt}(f \circ \phi^t) = \phi^{t*}(X \cdot f)$$

We can extend this construction to forms: given  $\alpha \in \Omega^p(M)$ ,  $X \in C^{\infty}(TM)$  a vector field,  $L_X \alpha \in \Omega^p$  is defined s.t.

(7) 
$$\frac{d}{dt}((\phi^t)^*\alpha) = \phi_t^*(L_X\alpha)$$

Note that the Lie derivative satisfies

(8) 
$$L_X(\alpha \wedge \beta) = L_X \alpha \wedge \beta + \alpha \wedge L_X \beta$$

and  $L_X(d\alpha) = d(L_X\alpha)$ .

Combining these two properties, we find that:

**Proposition 1.**  $L_X \alpha = di_X \alpha + i_X d\alpha$ .

*Proof.* By induction: base case is trivial, so assume statement for p-forms. Locally, a (p+1) form is the sum of  $fd\alpha$  for  $f \in C^{\infty}(M)$ ,  $\alpha \in \Omega^p$ . Thus,

(9) 
$$L_X(fd\alpha) = (L_X f) d\alpha + f dL_X \alpha$$
$$= (i_X df) d\alpha + f (ddi_X \alpha + di_X d\alpha)$$
$$= (i_X df) d\alpha + f di_X d\alpha$$

Now,

(10) 
$$di_X(fd\alpha) + i_X d(fd\alpha) = d(fi_X d\alpha) + i_X (df \wedge d\alpha)$$
$$= df \wedge i_X d\alpha + f di_X d\alpha + (i_X df) d\alpha - df \wedge i_X d\alpha$$
$$= (i_X df) d\alpha + f di_X d\alpha$$

giving us the desired equality.

#### 2. DE RHAM COHOMOLOGY

**Definition 3.** We say that  $\alpha \in \Omega^p$  is closed if  $d\alpha = 0$ , exact if  $\alpha = d\beta$  for some  $\beta$ . The de Rham cohomology of M is the collection of groups

(11) 
$$H^{p}(M,\mathbb{R}) = \frac{\ker(d:\Omega^{p} \to \Omega^{p+1})}{\operatorname{Im} (d:\Omega^{p-1} \to \Omega^{p})}$$

Example. For M connected,  $df = 0 \Leftrightarrow f$  is constant, so  $H^0(M, \mathbb{R}) = \mathbb{R}$ .

**Proposition 2** (Poincaré Lemma).  $H^p(\mathbb{R}^n) = 0 \ \forall p \geq 1$ .

*Proof.* By induction on n. The case n=1 is obvious, as  $f=\int \alpha dx \implies df=\alpha$ . For general n, write

(12) 
$$\alpha = \sum_{1 \le i_1 < \dots < i_p \le n} \alpha_{i_1 \dots i_p} dx_{i_1} \wedge \dots \wedge dx_{i_p}$$

on  $\mathbb{R}^n$  and assume  $\alpha$  is closed. Let

(13) 
$$\beta = \sum_{2 < j_1 < \dots < j_{p-1} < n} \beta_{j_1 \dots j_{p-1}} dx_{j_1} \wedge \dots \wedge dx_{j_{p-1}}$$

where  $\frac{\partial \beta_{j_1\cdots j_{p-1}}}{\partial x_1} = \alpha_{1j_1\cdots j_{p-1}}$  (i.e.  $\beta_{j_1\cdots j_p} = \int \alpha_{1j_1\cdots j_{p-1}} dx_1$ ). Then  $i_{\frac{\partial}{\partial x_1}} d\beta = i_{\frac{\partial}{\partial x_1}} \alpha$  by construction. Let  $\alpha' = \alpha - d\beta$ . Then  $\alpha' = \sum_{2 \leq i_1 < \cdots < i_p \leq n} \alpha'_{i_1\cdots i_p} dx_{i_1} \wedge \cdots \wedge dx_{i_p}$  with no  $dx_1$  by construction and  $d\alpha' = d\alpha - d(d\beta) = 0$ , showing that  $\alpha'$  is pulled back from  $\mathbb{R}^{n-1}$  by  $(x_1, \ldots, x_n) \stackrel{\pi}{\mapsto} (x_2, \ldots, x_n)$ . Writing  $\alpha' = \pi^* \eta, \eta \in \Omega(\mathbb{R}^{n-1})$ , we have that  $d\eta = 0$  and  $\eta = d\gamma$  by our inductive hypothesis. Thus,  $\alpha = \alpha' + d\beta = d(\pi^* \gamma + \beta)$  as desired.

# 2.1. Variants of de Rham Cohomology.

- If M is noncompact, we can also consider the space of compactly supported differential forms  $\Omega_c^p(M,\mathbb{R})$  and get the associated compactly supported de Rham cohomology  $H_c^p(M,\mathbb{R})$ .
- If  $U \subset M$  is a submanifold (e.g. an open subset), we can define relative differential forms  $\Omega^p(M, U; \mathbb{R}) = \{\alpha \in \Omega^p(M, \mathbb{R}) | \alpha|_U = 0\}$  and obtain the relative de Rham cohomology  $H^p(M, U; \mathbb{R})$ .

#### 3. Exact sequences of complexes

If  $M = U \cup V$ ,  $U, V \subset M$  open, we have an exact sequence on forms

$$(14) 0 \to \Omega^p(M) \to \Omega^p(U) \oplus \Omega^p(V) \to \Omega^p(U \cap V) \to 0$$

where the first map sends  $\alpha \mapsto (\alpha|_U, \alpha|_V)$  and the second  $(\alpha, \beta) \to \alpha|_{U \cap V} - \beta|_{U \cap V}$ . Both these maps commute with d, and exactness is clear: for the surjectivity of the last map, use a partition of unity 1 = u + v, where  $\text{supp}(u) \subset U$ ,  $\text{supp}(v) \subset V$ , so  $\gamma \in \Omega^p(U \cap V)$  is the image of  $(v\gamma, -u\gamma)$ . This short exact sequence then gives a long exact sequence (called the *Mayer-Vietoris* sequence)

$$(15) \qquad \cdots \to H^p(M) \to H^p(U) \oplus H^p(V) \to H^p(U \cap V) \xrightarrow{\delta} H^{p+1}(M) \to \cdots$$

The map  $\delta$  is obtained as follows:

- (1) Choose a splitting  $\sigma: \Omega^p(U \cap V) \to \Omega^p(U) \oplus \Omega^p(V)$ .
- (2) Given  $\gamma \in \Omega^p(U \cap V)$  closed,  $d\sigma(\gamma)$  lands in the image of  $i^* : \Omega^{p+1}(M) \to \Omega^{p+1}(U) \oplus \Omega^{p+1}(V)$ , and its preimage gives the desired element of  $\Omega^{p+1}(M)$ .

Similarly, for  $U \subset M$ , we get a sequence  $0 \to \Omega^p(M,U) \to \Omega^p(M) \to \Omega^p(U) \to 0$ , with the maps given by inclusion and restriction respectively, and thus a long exact sequence of relative cohomology. Using these properties along with Poincaré duality and functoriality under diffeomorphisms, we get

**Theorem 1.** The de Rham and singular (simplicial) cohomologies are equivalent.

### 3.1. Operations on de Rham cohomology.

- Cup product:  $[\alpha] \cup [\beta] = [\alpha \wedge \beta]$ . This is well defined:  $d\alpha = d\beta = 0 \implies d(\alpha \wedge \beta) = 0$ , and  $(\alpha + d\eta) \wedge \beta = \alpha \wedge \beta + d(\eta \wedge \beta)$ .
- Pairing with homology: for  $\Sigma \subset M$  a p-dimensional submanifold which is oriented and closed, we have an element  $[\Sigma] \in H_p(M)$  and thus a pairing  $\langle [\alpha], [\Sigma] \rangle = \int_{\Sigma} \alpha$ . More generally, given a p-cycle  $[\Sigma]$  represented by  $\sum n_i C_i$ , with  $C_i$  p-dimensional submanifolds with  $\partial$ , we get the same pairing extended linearly. That this is well-defined is a consequence of Stokes' theorem  $\int_{\Sigma} d\alpha = \int_{\partial \Sigma} \alpha$ .
- Poincaré duality: For  $M^n$  compact,  $[\alpha] \in H^p(M), [\beta] \in H^{n-p}(M) \mapsto \int_M \alpha \wedge \beta = ([\alpha] \cup [\beta]) \cdot [M]$  is a nondegenerate linear pairing and gives an isomorphism  $H^{n-p} \cong H_p$ . In the noncompact case, we have  $[\alpha] \in H^p(M), [\beta] \in H^{n-p}_c(M) \mapsto \int_M \alpha \wedge \beta$  giving  $H^{n-p}_c \cong H_p$ .

---

## SYMPLECTIC GEOMETRY, LECTURE 2

Prof. Denis Auroux

## 1. Homology and Cohomology

Recall from last time that, for M a smooth manifold, we produced a graded differential algebra  $(\Omega^*(M), \wedge, d)$  giving us a cohomology  $H^*(M)$  with cup product  $[\alpha] \cup [\beta] = [\alpha \wedge \beta]$  (which is well-defined since  $d(\alpha \wedge \beta) = d\alpha \wedge \beta + (-1)^{\text{deg }\alpha} \alpha \wedge d\beta$  and  $(\alpha + d\eta) \wedge \beta = \alpha \wedge \beta + d\eta \wedge \beta$ ). Furthermore, we obtain a pairing with homology: for  $\Sigma \subset M$  a p-dimensional, oriented, closed submanifold with associated class  $[\Sigma] \in H_p(M)$ , we define

(1) 
$$\langle [\alpha], [\Sigma] \rangle = \int_{\Sigma} \alpha$$

for  $[\alpha] \in H^p(M,\mathbb{R})$ , and extend this by linearity to give a pairing with all of  $H_p(M)$ . That this is well-defined is a consequence of Stokes' theorem:

(2) 
$$\int_{\Sigma} d\alpha = \int_{\partial \Sigma} \alpha$$

Remark. A form is closed  $\Leftrightarrow$  its integral on submanifolds depends only the homology class of the submanifold.

Furthermore, if  $M^n$  is compact, closed, and oriented, we have a nondegenerate pairing

(3) 
$$H^{p}(M,\mathbb{R}) \otimes H^{n-p}(M,\mathbb{R}) \to \mathbb{R}, [\alpha] \otimes [\beta] \mapsto \int_{M} \alpha \wedge \beta$$

which induces the Poincaré duality  $H^{n-p}(M,\mathbb{R}) \to H_p(M,\mathbb{R})$ . In the noncompact case, we have the same statement using cohomology with compact support  $H_C^{n-p}(M,\mathbb{R})$ .

## 2. Symplectic Vector Spaces

Let V be a f.d. vector space  $\mathbb{R}$ .

**Definition 1.** A symplectic structure on V is a bilinear, non-degenerate, skew-symmetric pairing  $\Omega: V \times V \to \mathbb{R}$ . That is, as a matrix, it is invertible and skew-symmetric.

Example. For  $\mathbb{R}^{2n}$  with basis  $\{e_i\}_{i=1}^n, \{f_i\}_{i=1}^n$ , we have a standard symplectic form given by  $\Omega_0(e_i, e_j) = \Omega_0(f_i, f_j) = 0 \ \forall i, j, \Omega_0(e_i, f_j) = \delta_{i,j} = -\Omega_0(f_j, e_i)$ . As a matrix, it is given by  $\begin{pmatrix} 0 & I_n \\ -I_n & 0 \end{pmatrix}$ .

**Definition 2.** For  $E \subset V$  a linear subspace,  $\Omega$  a bilinear form, the orthogonal complement of E is  $E^{\Omega} = E^{\perp} = \{v \in V | \Omega(u, v) = 0 \ \forall u \in E\}.$ 

Note that  $\Omega$  is non-degenerate  $\Leftrightarrow V^{\Omega} = \{0\}.$ 

Example. In  $\mathbb{R}^{2n}$  with basis as above,

$$\operatorname{Span}\{e_1\}^{\Omega} = \operatorname{Span}\{e_1, \dots, e_n, f_2, \dots, f_n\}$$

$$\operatorname{Span}\{e_1, f_1\}^{\Omega} = \operatorname{Span}\{e_2, \dots, e_n, f_2, \dots, f_n\}$$

$$\operatorname{Span}\{e_1, \dots, e_n\}^{\Omega} = \operatorname{Span}\{e_1, \dots, e_n\}$$

**Definition 3.** A standard (symplectic) basis of  $(V^{2n}, \Omega)$  is a basis  $(\{e_i\}, \{f_i\})$  satisfying the above.

**Theorem 1.** For  $(V^n, \Omega)$  a symplectic vector space,  $\exists$  a standard basis.

Proof. We induce on n: the base case is trivial. Choose some vector  $e_1 \in V \setminus \{0\}$ . By nondegeneracy,  $\Omega(e_i, \cdot) \neq 0 \implies \exists f_1 \text{ s.t. } \Omega(e_1, f_1) = 1$ . Let  $W = \operatorname{Span}\{e_1, f_1\}^{\Omega}$ : then  $\Omega|_W$  is symplectic since  $u \in W, \Omega(u, q) = 0 \ \forall w \in W \implies \Omega(u, e_1) = 0, \Omega(u, f_1) = 0 \implies u = 0$ . Furthermore,  $V = \operatorname{Span}\{e_1, f_1\} \oplus W$ . To see this, note first that, if  $v = ae_1 + bf_1 \in W, \Omega(e_1, v) = b = 0$  and  $\Omega(f_1, v) = a = 0$ , so  $W \cap \operatorname{Span}\{e_1, f_1\} = \emptyset$ . Secondly, for  $v \in V$ , we can write  $v = w + ae_1 + bf_1$ , where  $w = v - \Omega(e_1, v)f_1 + \Omega(f_1, v)e_1 \in W$ . Since W has dimension n - 2, we are done.

Corollary 1. V symplectic  $\implies$  V is even-dimensional and symplectomorphic to  $(\mathbb{R}^{2n}, \Omega_0)$ .

We denote the symplectic automorphisms of  $(V,\Omega)$  by  $\mathrm{Sp}(V,\Omega)=\mathrm{Sp}(2n,\mathbb{R})$ .

Remark. dim  $E^{\Omega} = \dim V - \dim E$  because  $V \stackrel{\cong}{\to} V^* \to E^*, v \mapsto \Omega(v, \cdot) \mapsto \Omega(v, \cdot)|_E$  is surjective with kernel  $E^{\Omega}$ .

**Definition 4.**  $E \subset V$  is a symplectic subspace if  $\Omega|_E$  is nondegenerate, e.g. in a standard basis E is the span of

$$(5) (e_1, f_1, \dots, e_k, f_k)$$

*Problem.* Prove that E is a symplectic subspace  $\Leftrightarrow E \cap E^{\Omega} = \{0\} \Leftrightarrow V = E \oplus E^{\Omega}$ .

**Definition 5.**  $E \subset V$  is an isotopic (resp. coisotopic, lagrangian) subspace if  $E \subset E^{\Omega}$  (resp.  $E^{\Omega} \subset E, E^{\Omega} = E$ ), e.g. in a standard basis E is the span of  $(e_1, \ldots, e_k)$  (resp.  $(e_1, f_1, \ldots, e_k, f_k, e_{k+1}, \ldots e_n)$ ,  $(e_1, \ldots, e_n)$ ).

Example. For  $E \subset V$  Lagrangian with basis  $(e_1, \ldots, e_n)$ , we can complete this to a symplectic basis

$$(6) (e_1, \ldots, e_n, f_1, \ldots, f_n)$$

of V.

**Definition 6.** The symplectic volume form is  $\frac{1}{n!}\Omega^{\wedge n}$  (where  $\Omega$  is considered as an element of  $\bigwedge^2(V^*)$ ).

Note that, since  $\Omega$  is nondegenerate, we can write  $\Omega = \sum_i e^i \wedge f^i$ , so  $\Omega^{\wedge n} = n!e^1 \wedge f^1 \wedge \cdots \wedge e^n \wedge f^n$  is a non-zero top form, and our volume form is well-defined. In fact,  $\Omega^{\wedge n} \neq 0 \Leftrightarrow \Omega$  is nondegenerate.

## 3. Symplectic Manifolds

Let M be a smooth manifold.

**Definition 7.** A symplectic form on M is a 2-form  $\omega$  (i.e. a skew-symmetric pairing  $\omega_p: T_pM \times T_pM \to \mathbb{R}$  for all  $p \in M$ ) which is nondegenerate (i.e.  $\frac{1}{n!}\omega^n$  is a volume form) and closed (i.e.  $d\omega = 0$ ).

Remark. M symplectic  $\implies$  it is even-dimensional and naturally oriented. Moreover,  $[\omega] \in H^2(M, \mathbb{R})$  plays an important role, especially if M is compact, as in this case  $\int_M \frac{\omega^n}{n!} = \text{vol}(M) > 0 \implies [\omega] \neq 0$ .

Example. For  $\mathbb{R}^{2n}$ ,  $\omega_0 = \sum dx_i \wedge dy_i$  is the standard symplectic structure: for  $\mathbb{C}^n$ , we write this as  $\omega = \frac{i}{2} \sum dz_j \wedge d\overline{z_j}$  instead. Furthermore, for an orientable surface  $\Sigma$ , any area form is a symplectic form.

*Problem.* For which values of n does  $S^{2n}$  (resp.  $T^{2n}$ ) have a symplectic structure?

**Definition 8.** A symplectomorphism is a diffeomorphism  $\phi:(M,\omega)\to (M',\omega')$  s.t.  $\phi^*\omega'=\omega$ .

We denote the group of symplectomorphisms of M by  $\operatorname{Symp}(M,\omega)$ .

Example. For  $S^2 \subset \mathbb{R}^3$ ,  $\operatorname{Symp}(S^2)$  is the group of area and orientation preserving diffeomorphisms, which is much larger than the group of isometries.

**Theorem 2** (Darboux). Every symplectic manifold is locally symplectomorphic to  $(\mathbb{R}^{2n}, \omega)$ , i.e. it has local coordinates in which  $\omega = \sum dx_i \wedge dy_i$ .

---

## SYMPLECTIC GEOMETRY, LECTURE 3

Prof. Denis Auroux

## 1. Symplectic Manifolds

Let  $(M,\omega)$  be a symplectic manifold, i.e. a smooth manifold with nondegenerate closed 2-form  $\omega$ .

Example. For X a smooth manifold, the cotangent bundle  $M = T^*X$  is a symplectic manifold. Specifically, given a chart  $U \subset X$  with coordinates  $x_1, \ldots, x_n$ , we have a basis of  $T_p^*X$  given by  $dx_1, \ldots, dx_n$  and every  $\xi \in T^*X$  can be written as  $\sum \xi_i dx_i$ . This gives us a map

(1) 
$$T^*X|_U \to \mathbb{R}^{2n}, (x,\xi) \mapsto (x_1, \dots, x_n, \xi_1, \dots, \xi_n)$$

Let  $\alpha$  be the Liouville form defined by  $\sum \xi_i dx_i$  on each coordinate patch. It is well-defined as a 1-form on M, and  $\omega = d\alpha = \sum d\xi_i \wedge dx_i$  is the desired symplectic form. Furthermore, given a diffeomorphism  $X_1 \to X_2$ , we have an induced map

(2) 
$$F: T^*X_1 \to T^*X_2, (x, \xi) \mapsto (f(x), (d_x f)^{-1*}\xi)$$

which is a symplectomorphism (because  $\exists$  local coordinates in which f is the identity). Also, given  $h \in C^{\infty}(X,\mathbb{R})$ , we have an associated symplectomorphism  $\tau_h: M \to M, (x,\xi) \mapsto (x,\xi+d_xh)$  since

(3) 
$$\tau_h^* \alpha = \alpha + dh \implies \tau_h^* \omega = \tau_h^* (d\alpha) = d\alpha + ddh = \omega$$

as desired.

## 1.1. Submanifolds.

**Definition 1.** A submanifold  $W \subset (M, \omega)$  is symplectic if  $\omega|_W$  is symplectic (specifically, nondegenerate). This implies that  $T_pW \subset T_pM$  is a symplectic subspace  $\forall p.\ L \subset (M, \omega)$  is Lagrangian if  $\omega|_L = 0$  and dim  $L = \frac{1}{2}\dim M$ .

Example. By our above construction, the 0-section  $X \hookrightarrow T^*X = M$  is a Lagrangian submanifold. Furthermore, sections of  $T^*X$  are graphs  $X_{\mu} = \{(x, \mu(x)) | x \in X\} \subset T^*X$  of 1-forms  $\mu \in \Omega^1(X, \mathbb{R})$ : such a graph is Lagrangian iff  $d\mu = 0$ , since denoting  $i_{\mu}(x) = (x, \mu(x))$ ,  $i_{\mu}^*\alpha = \mu \implies i_{\mu}^*(\omega) = i_{\mu}^*(d\alpha) = di_{\mu}^*\alpha = d\mu$ .

Example. For  $\Sigma^k \subset X^n$  a submanifold, define the conormal space to  $x \in \Sigma$  by

(4) 
$$N_x^* \Sigma = \{ \xi \in T_x^* X | \xi |_{T_x \Sigma} = 0 \}$$

This gives us subbundle  $N^*\Sigma \subset T^*X|_{\Sigma}$  and a submanifold  $N^*\Sigma \subset T^*X$ . For  $\Sigma = X$ , we get the 0-section: for  $\Sigma = \{p\}$ , we get the fiber  $T_p^*X$ . By definition,  $\alpha|_{N^*\Sigma} = 0$ , so  $N^*\Sigma$  is Lagrangian.

1.2. Symplectomorphisms and Lagrangian Submanifolds. Let  $\phi:(M_1,\omega_1)\to (M_2,\omega_2)$  be a diffeomorphism: we want to know whether  $\phi$  is a symplectomorphism as well, i.e. whether  $\phi^*\omega_2=\omega_1$ . Consider the graph  $\Gamma_\phi\subset M=M_1\times M_2$ . The latter space has one symplectic structure via  $\omega=\omega_1\oplus\omega_2=\pi_1^*\omega_1+\pi_2^*\omega_2$ , which is nondegenerate since

(5) 
$$\omega^{n_1+n_2} = \binom{n_1+n_2}{n_1} \pi_1^* \omega_1^{n_1} \wedge \pi_2^* \omega_2^{n_2}$$

However, here we will consider the alternate symplectic structure given by  $\hat{\omega} = \pi_1^* \omega_1 - \pi_2^* \omega_2$ .

**Proposition 1.**  $\phi$  is a symplectomorphism  $\Leftrightarrow \Gamma_{\phi}$  is Lagrangian.

*Proof.*  $\Gamma_{\phi}$  is the image of the embedding  $\gamma: M_1 \to M_1 \times M_2, p \mapsto (p, \phi(p))$ , and  $\gamma^* \hat{\omega} = \gamma^* \pi_1^* \omega_1 - \gamma^* \pi_2^* \omega_2 = \omega_1 - \phi^* \omega_2$  is  $0 \Leftrightarrow \Gamma_{\phi}$  is Lagrangian.

## 2. Hamiltonian Vector Fields

Let M be a manifold.

**Definition 2.** An isotopy on M is a  $C^{\infty}$  map  $\rho: M \times \mathbb{R} \to M$  s.t.  $\rho_0 = \operatorname{id}$  and  $\forall t, \rho_t$  is a diffeomorphism.

Given an isotopy, we obtain a time-dependent vector field  $v_t: p \mapsto \frac{d}{ds}\rho_s(q)|_{s=t}$  where  $q = \rho_t^{-1}(p)$ . We say that  $\rho_t$  is the flow of  $v_t$ . Conversely, if M is compact or  $v_t$  is sufficiently "good", we can integrate to obtain the flow from the vector field. If v is time-independent, we obtain a 1-parameter group  $\rho_t = \exp(tv)$ , with associated vector field v. Recall the Lie derivative  $L_v \alpha = \frac{d}{dt} (\exp(tv)^* \alpha)|_{t=0}$ .

**Proposition 2** (Cartan's Formula).  $L_v\alpha = di_v\alpha + i_v d\alpha$ .

If  $(\rho_t)$  is generated by  $(v_t)$  then  $\frac{d}{dt}(\rho_t^*\alpha) = \rho_t^*(L_{v_t}\alpha)$ .

Now, let  $(M, \omega)$  be a symplectic manifold,  $H: M \to \mathbb{R}$  a  $C^{\infty}$  map. Then  $dH \in \Omega^1(M) \Longrightarrow \exists$  a unique vector field  $X_H$  s.t.  $i_{X_H}\omega = dH$ , called the *Hamiltonian vector field* generated by H (H itself is called the *Hamiltonian function*). Now, assume that M is compact, or that the flow of  $X_H$  is well-defined. Then we obtain an isotopy  $\rho_t: M \to M$  of diffeomorphisms generated by  $X_H$ .

**Proposition 3.**  $\rho_t$  are symplectomorphisms.

*Proof.* Note that 
$$\frac{d}{dt}(\rho_t^*\omega) = \rho_t^*(L_{X_H}\omega)$$
 but  $L_{X_H}\omega = di_{X_H}\omega + i_{X_H}d\omega = d^2H = 0$ . Since  $\rho_0$  is the identity,  $\rho_t^*\omega = \omega$  for all  $t$ .

Example. For  $\mathbb{R}^{2n}$  with coordinates  $x_1, \ldots, x_n, p_1, \ldots, p_n$ , the function  $H(x, p) = \frac{1}{2} |p|^2 + V(x)$  has derivative  $dH = \sum p_i dp_i + \frac{\partial V}{\partial x_i} dx_i$ . Thus, the associated vector field is  $X_H = \sum -p_i \frac{\partial}{\partial x_i} + \frac{\partial V}{\partial x_i} \frac{\partial}{\partial p_i}$ , giving us Hamilton's equations

(6) 
$$\frac{dx_i}{dt} = -p_i = -\frac{\partial H}{\partial p_i}, \quad \frac{dp_i}{dt} = \frac{\partial V}{\partial x_i} = \frac{\partial H}{\partial x_i}$$

---

## SYMPLECTIC GEOMETRY, LECTURE 4

## Prof. Denis Auroux

## 1. Hamiltonian Vector Fields

Recall from last time that, for  $(M, \omega)$  a symplectic manifold,  $H: M \to \mathbb{R}$  a  $C^{\infty}$  function, there exists a vector field  $X_H$  s.t.  $i_{X_H}\omega = dH$ . Furthermore, the associated flow  $\rho_t$  of this vector field is an isotopy of symplectomorphisms.

Example. Consider  $S^2 \subset \mathbb{R}^3$  with cylindrical coordinates  $(r, \theta, z)$  and symplectic form  $\omega = d\theta \wedge dz$  ( $\omega$  is the usual area form). Then setting H = z gives the vector field  $\frac{\partial}{\partial \theta}$ : the associated flow is precisely rotation by angle t.

Note also that the critical points of H are the fixed points of  $\rho_t$ , and  $\rho_t$  preserves the level sets of H, i.e.

(1) 
$$\frac{d}{dt}(H \circ \rho_t) = \frac{d}{dt}(\rho_t^* H) = \rho_t^*(L_{X_H} H) = \rho_t^*(i_{X_H} \omega(X_H)) = \rho_t^*(\omega(X_H, X_H)) = 0$$

One can apply this to obtain the ordinary formula for conservation of energy.

**Definition 1.** X is a symplectic vector field if  $L_X\omega = 0$ , i.e.  $i_X\omega$  is closed. X is Hamiltonian if  $i_X\omega$  is exact.

By Poincaré, we see that, locally, symplectic vector fields are Hamiltonian. Globally, we obtain a class  $[i_X\omega]\in H^1(M,\mathbb{R})$ .

Example. On  $T^2$ ,  $\frac{\partial}{\partial x}$  and  $\frac{\partial}{\partial y}$  are symplectic vector fields: since dy and dx are not exact,  $\frac{\partial}{\partial x}$  and  $\frac{\partial}{\partial y}$  are not Hamiltonian

Now consider time-dependent Hamiltonian functions, i.e.  $C^{\infty}$  maps  $\mathbb{R} \times M \to \mathbb{R}$ ,  $(t,x) \mapsto H_t(x)$ . Let  $\operatorname{Ham}(M,\omega)$  denote the space of Hamiltonian diffeomorphisms on  $\omega$ , i.e. the set of diffeomorphisms  $\rho$  s.t.  $\exists H_t$  with corresponding flow  $\rho_t$  satisfying  $\rho_1 = \rho$ .

Remark. The Arnold conjecture states that for M compact,  $\phi \in \text{Ham}(M, \omega)$  with nondegenerate  $\text{Fix}(\phi)$  (i.e. at a fixed point p,  $d\phi(p)$  – id is invertible),

(2) 
$$\#\operatorname{Fix}\phi \ge \sum \dim H^i(M)$$

This statement is false for non-Hamiltonian vector fields, as seen in the case of  $\frac{\partial}{\partial x}$  on a torus.

We can measure the difference between symplectomorphisms and Hamiltonian symplectomorphisms via the flux function

(3) 
$$\operatorname{Flux}(\rho_t) = \int_0^1 [i_{X_t} \omega] dt \in H^1(M, \mathbb{R})$$

In general, the flux depends on the homotopy class of the path from the identity to  $\rho_1$ .

Remark. The Flux conjecture concerns the integral of the flux on  $\pi_1 \operatorname{Symp}(M,\omega)$ , i.e. the nature of

(4) 
$$\langle \operatorname{Flux}, \pi_1 \operatorname{Symp}(M, \omega) \rangle \subset H^1(M, \mathbb{R})$$

Geometrically, for  $\gamma: S^1 \to M$  a loop, let  $\gamma_t = \rho_t \circ \gamma: S^1 \to M$  be the image of  $\gamma$  under  $\rho$  and define  $\Gamma: [0,1] \times S^1 \to M$  by  $(t,s) \mapsto \gamma_t(s)$ .

Problem.  $\langle \operatorname{Flux}(\rho_t), [\gamma] \rangle = \operatorname{Area}(\Gamma) = \int_{[0,1] \times S^1} \Gamma^* \omega.$ 

## 2. Moser's Theorem

One can ask whether, for a given manifold M, two symplectic structures  $\omega_0, \omega_1$  are equivalent, i.e. whether there is a symplectomorphism  $M \to M$  which pulls back one to the other. In general,  $[\omega_0] = [\omega_1]$  does not imply that the two structures are symplectomorphic. To study this question further, we give other notions of equivalence.

**Definition 2.** Two forms  $\omega_0, \omega_1$  are deformation equivalent if  $\exists (\omega_t)_{t \in [0,1]}$  a continuous family of symplectic forms, and isotopic if there is such a family with  $[\omega_t]$  constant in  $H^2(M, \mathbb{R})$ .

*Remark.* There exist pairs of symplectic forms with the same cohomology class which are not deformation equivalent, as well as pairs which are deformation equivalent but not isotopic (in dimension  $\geq 6$ ).

Let M be a compact manifold with  $\omega_0, \omega_1$  isotopic symplectic forms (i.e.  $\exists \omega_t$  as above with each  $\omega_t$  nondegenerate).

**Theorem 1** (Moser).  $\exists$  an isotopy  $\rho_t : M \to M$  s.t.  $\rho_t^* \omega_t = \omega_0$ .

That is,  $(M, \omega_0)$  and  $(M, \omega_1)$  are symplectomorphic.

Proof. (This technique is known as Moser's trick.) By assumption,  $[\omega_t]$  is independent of t, i.e.  $[\frac{d\omega_t}{dt}] = 0$ . Thus,  $\exists \alpha_t$  a 1-form s.t.  $\frac{d\omega_t}{dt} = -d\alpha_t$ : moreover, we can choose this  $\alpha_t$  smoothly w.r.t. to t (via the Poincaré lemma). Since  $\omega_t$  is nondegenerate,  $\exists X_t$  s.t.  $i_{X_t}\omega_t = \alpha_t$ . Moreover, since M is compact, we have a well-defined flow  $\rho_t$  of  $X_t$ . Now,

(5) 
$$\frac{d}{dt}(\rho_t^*\omega_t) = \rho_t^*(L_{X_t}\omega_t) + \rho_t^*\left(\frac{d\omega_t}{dt}\right) = \rho_t^*(di_{X_t}\omega_t + \frac{d\omega_t}{dt}) = 0$$

Since  $\rho_0$  is the identity, we have our desired isotopy.

Example. For symplectic forms  $\omega_0, \omega_1$  with  $[\omega_0] = [\omega_1]$ , consider the family  $\omega_t = t\omega_0 + (1-t)\omega_1$ . By the above, if this family is nondegenerate, the two forms are symplectomorphic. In general, there is no reason for this to be true: in dimension 2, it always is. More generally, this follows from compatibility with almost-complex structures.

**Theorem 2** (Darboux). For  $(M, \omega)$  symplectic,  $p \in M$ ,  $\exists U \ni p$  with a coordinate system  $(x_1, y_1, \dots, x_n, y_n)$  s.t.  $\omega|_U = \sum dx_i \wedge dy_i$ .

Proof.  $(T_pM,\omega_p)$  has a standard basis  $(e_1,\ldots,e_n,f_1,\ldots,f_n)$ , so there exist local coordinates  $(x_1,y_1,\ldots,x_n,y_n)$  s.t.  $\omega_p = \sum dx_i \wedge dy_i$ . On a neighborhood U of p, we obtain two symplectic forms:  $\omega$  and the standard form. The family  $\omega_t = (1-t)\omega_0 + t\omega_1$  is one of closed forms: since nondegeneracy is an open condition, we can shrink our neighborhood to assure that  $\omega_t$  is nondegenerate for each t on some  $U' \ni p$ . Thus,  $\exists \alpha \in \Omega^1(U)$  s.t.  $\omega_1 - \omega_0 = -d\alpha$ . Subtracting a constant, we can assume  $\alpha_p = 0$ . Let  $v_t$  be the vector field on U s.t.  $i_{v_t}\omega_t = \alpha$ . Then  $\exists U'' \ni p$  s.t. its flow  $\rho_t$  is defined  $\forall t$ . By the Moser's trick, we find that  $\rho_1^*\omega_1 = \omega_0$ , implying that the symplectic form is indeed standard after composing our chosen coordinates with  $\rho_1$ .

---

## SYMPLECTIC GEOMETRY, LECTURE 5

Prof. Denis Auroux

Last time we proved:

**Theorem 1** (Moser). Let M be a compact manifold,  $(\omega_t)$  symplectic forms,  $[\omega_t]$  constant  $\implies (M, \omega_0) \cong (M, \omega_1)$ .

**Theorem 2** (Darboux). Locally, any symplectic manifold is locally isomorphic to  $(\mathbb{R}^{2n}, \omega_0)$ .

## 1. Tubular Neighborhoods

Let  $M^n \supset X^k$  be a submanifold with inclusion map i. Then we get a map  $d_x i: T_x X \hookrightarrow T_x M$ , with associated normal space  $N_x X = T_x M/T_x X$ . Note that if there is a metric, one can identify this with the orthogonal space to X at x. Putting all these spaces together, we get a normal bundle  $NX = \{(x, v) | x \in X, v \in N_x X\}$  with zero section  $i_0: X \to NX, x \mapsto (x, 0)$ .

**Theorem 3.**  $\exists U_0$  a neighborhood of X in NX (via the 0-section) and  $U_1$  a neighborhood of X in M s.t.  $\exists \phi: U_0 \xrightarrow{\sim} U_1$  a diffeomorphism.

Proof. (Idea) Equip M with a Riemannian metric g, so  $N_x X \xrightarrow{\sim} T_x X^{\perp} \subset T_x M$ . Then, given  $x \in X, v \in N_x X$  for |v| sufficiently small  $(|v| = \sqrt{g(v,v)} < \epsilon)$ , we obtain an exponential function  $\exp_x(v)$  (defined by considering a small geodesic segment with origin x and tangent vector v). We obtain a map  $U_0 \to M$ ,  $(x,v) \mapsto \exp_x(v)$ . For  $x \in X, T_{(x,0)}(NX) = T_x X \oplus N_x X$  and

(1) 
$$d_{(x,0)}\exp(u,v) = u + v \in T_x X \oplus T_x X^{\perp}$$

this giving us a local diffeomorphism near the 0-section. Thus, locally on some neighborhood of the 0-section in NX, exp induces a diffeomorphism onto  $\exp(U_0) = \text{neighborhood}$  of X in M.

Let  $U_1 = \{\exp_x(v) | |v| < \epsilon'(x)\} \subset M$  be a tubular neighborhood of X in M as constructed above, with  $U_0 \subset NX$  the corresponding neighborhood of the zero section. Via the projection  $\pi: U_0 \to X$ , whose fibers are balls in  $\mathbb{R}^{n-k}$ , we see that  $U_1$  retracts onto X, i.e. we have a null-homotopic map  $U_1 \xrightarrow{\pi} X \xrightarrow{i} U_1$ .

Corollary 1.  $i^*: H^*(U_1, \mathbb{R}) \to H^*(X, \mathbb{R})$  is an isomorphism.

**Proposition 1.**  $\beta \in \Omega^{\ell}(U), d\beta = 0, i^*\beta = \beta|_X = 0 \implies \exists \mu \in \Omega^{\ell-1}(U), \beta = d\mu \text{ and } \mu_x = 0 \ \forall x \in X.$ 

*Proof.* Identify  $U \cong U_0 \subset NX$ , set  $\rho_t : (x, v) \mapsto (x, tv)$ , and let

(2) 
$$\mu_{(x,v)} = \int_0^1 \rho_t^*(i_{(0,v)}\beta)dt$$

Then  $\mu = 0$  on the zero section, and

(3) 
$$d\mu = \int_0^1 \rho_t^*(di_{X_t}\beta)dt$$

where  $X_t(x,tv) = (0,v)$ . Since  $\beta$  is closed,  $di_{X_t}\beta = L_{X_t}\beta$ , so

(4) 
$$d\mu = \int_0^1 \frac{d}{dt} (\rho_t^* \beta) dt = \rho_1^* \beta - \rho_0^* \beta = \beta - \pi^* i^* \beta = \beta$$

**Theorem 4** (Local Moser). Let  $X \hookrightarrow M$  be a submanifold,  $\omega_0, \omega_1$  symplectic forms on M s.t.  $(\omega_0)_p = (\omega_1)_p \forall p \in X$ . Then  $\exists$  neighborhoods  $U_0, U_1 \supset X$  and  $\phi: U_0 \overset{\sim}{\to} U_1$  s.t.  $\phi^*\omega_1 = \omega_0$  and  $\phi|_X = \mathrm{id}$ .

That is, we have a symplectomorphism  $(U_0, \omega_0) \stackrel{\sim}{\to} (U_1, \omega_1)$  commuting with the inclusion of X.

Proof. Let  $U_0$  be a tubular neighborhood of X. Since  $\omega_1 - \omega_0$  is closed and is 0 on X, by the above proposition we have a form  $\mu \in \Omega^1(U_0)$  s.t.  $\omega_1 - \omega_0 = d\mu$  and  $\mu$  is 0 along X. Now, let  $\omega_t = (1-t)\omega_0 + t\omega_1$ : these form a family of closed two-forms which are  $\omega_0$  along X and thus nondegenerate at X. Since nondegeneracy is an open condition,  $\exists U_0' \subset U_0$  on which  $\omega_t$  is symplectic  $\forall t$ .  $\exists v_t$  a vector field on  $U_0'$  s.t.  $i_{v_t}\omega_t = -\mu$  with  $v_t = 0$  along X. Letting  $\rho_t$  be the flow of  $v_t$ , we find that  $\rho_t$  is the identity along X, and  $\exists$  a neighborhood  $U_0''$  on which the flow is well defined. Finally,

(5) 
$$\frac{d}{dt}(\rho_t^*\omega_t) = \rho_t^* \left( L_{v_t}\omega_t + \frac{d\omega_t}{dt} \right) = \rho_t^* (-d\mu + (\omega_1 - \omega_0)) = 0$$

**Proposition 2.** Let  $X \hookrightarrow (M, \omega)$  be a Lagrangian submanifold. Then  $NX \xrightarrow{\sim} T^*X$ .

*Proof.*  $E \subset (V,\Omega)$  a Lagrangian subspace  $\implies \Omega: V \xrightarrow{\sim} V^* \twoheadrightarrow E^*, v \mapsto \Omega(v,\cdot)$  is onto with kernel  $\cong E^{\perp\Omega} = E$ , so  $V/E \cong E^*$ .

**Theorem 5** (Weinstein's Lagrangian Neighborhood). Let  $(M, \omega)$  be a symplectic manifold,  $i: X \hookrightarrow M$  a closed Lagrangian submanifold,  $i_0: X \to (T^*X, \omega_0)$  the zero-section. Then  $\exists U_0$  a neighborhood of X in  $T^*X$  and U a neighborhood of X in M s.t. we have a symplectomorphism  $(U_0, \omega_0) \xrightarrow{\sim} (U, \omega)$  which is the identity on X.

*Proof.*  $NX \cong T^*X$ , so  $\exists N_0 \supset X$  in  $T^*X, N \supset X$  in M, and a diffeomorphism  $\psi : N_0 \xrightarrow{\sim} N$  which preserves X. Now, let  $\omega_0$  be the canonical form on  $T^*X$  and  $\omega_1 = \psi^*\omega$ . These are both sympectic forms on  $N_0 \subset T^*X$  s.t. the zero section X is Lagrangian for both.

We claim that we can build (canonically) a family of isomorphisms  $L_p: T_pN_0 \to T_pN_0$  for  $p \in X$  s.t.  $L_{p|T_pX} = \text{id}$  and  $(L_p^*\omega_1)_p = (\omega_0)_p$ . By Whitney's extension theorem,  $\exists$  a neighborhood  $N' \supset X$  and an embedding  $h: N' \hookrightarrow N_0$  s.t.

(6) 
$$h|_{X} = \mathrm{id}, dh_{p} = L_{p} \forall p \in X$$

(Idea: use a Riemannian metric, and set  $h(p,\xi) = \exp_{p,0} L_p(0,\xi)$ ). Then  $\forall p \in X, (h^*\omega_1)_p = (\omega_0)_p$ , so we can use local Moser for  $h^*\omega_1$  and  $\omega_0$ . We therefore obtain  $U_0, U_1 \supset X$  and a local symplectomorphism  $f: (U_0, \omega_0) \xrightarrow{\sim} (U_1, h^*\omega_1)$ . Setting  $\phi = \psi \circ h \circ f$  gives us the desired result.

To prove the claim, decompose  $T_{(p,0)}N_0 = T_pX \oplus T_p^*X$ , with a chosen basis for  $T_pX$  and the dual basis for  $T_p^*X$ . We have two symplectic forms on this space, namely  $\omega_0 = \begin{pmatrix} 0 & -I \\ I & 0 \end{pmatrix}$ ,  $\omega = \begin{pmatrix} 0 & -B^t \\ B & C \end{pmatrix}$ . That is, we know that

(7) 
$$\omega_0((v_1, \xi_1), (v_2, \xi_2)) = \xi_1(v_2) - \xi_2(v_1)$$

and  $\omega|_{T_pX}=0$ . We want to find a matrix  $L=\begin{pmatrix}I&*\\0&*\end{pmatrix}$  s.t.  $L^t\omega L=\omega_0$ . Setting

(8) 
$$L = \begin{pmatrix} I & -\frac{1}{2}B^{-1}CB^{-t} \\ 0 & B^{-t} \end{pmatrix}$$

gives the desired matrix: furthermore, the construction doesn't depend on the choice of basis.

---

## SYMPLECTIC GEOMETRY, LECTURE 6

Prof. Denis Auroux

## 1. Applications

(1) The work done last time gives us a new way to look at  $T_{\rm id} \operatorname{Symp}(M,\omega)$  (using  $C^1$ -topology, wherein  $f_i: X \to Y$  converges to f iff  $f_i \to f$  uniformly on compact sets and same for  $df_i: TX \to TY$ . Now,  $f \in \operatorname{Symp}(M,\omega)$  gives a graph  $\operatorname{graph}(f) = \{(x,f(x))\} \subset (M \times M,\operatorname{pr}_1^*\omega - \operatorname{pr}_2^*\omega)$  which is a Lagrangian submanifold. If f is  $C^1$ -close to the identity map, then  $\operatorname{graph}(f)$  is  $C^1$ -close to the diagonal  $\Delta = \{(x,x)\} \subset (M \times M,\operatorname{pr}_1^*\omega - \operatorname{pr}_2^*\omega)$  (i.e. the graph of the identity map). By Weinstein, a tubular neighborhood of  $\Delta$  is diffeomorphic to  $U_0 \subset (T^*M,\omega_{T^*M})$ , and the graph of f gives a section ( $C^1$ -close to the zero section), i.e. the graph of a  $C^1$ -small  $\mu \in \Omega^1(M)$ . The fact that its graph is Lagrangian implies that  $\mu$  is closed, i.e.  $d\mu = 0$ . Thus, we have an identification  $T_{\rm id}(\operatorname{Symp}(M,\omega)) \cong \{\mu \in \Omega^1 | d\mu = 0\}$  with  $C^1$  topologies.

(2)

**Theorem 1.** For  $(M, \omega)$  compact, if  $H^1(M, \mathbb{R}) = 0$ , then every symplectomorphism of M which is  $C^1$  close to the identity has  $\geq 2$  fixed points.

**Theorem 2.** For  $(M, \omega)$  symplectic,  $X \subset (M, \omega)$  compact and Lagrangian, if  $H^1(X, \mathbb{R}) = 0$ , then every Lagrangian submanifold of M which is  $C^1$  close to X intersects X in  $\geq 2$  points.

The first theorem follows from the second, using the diagonal embedding  $\Delta \subset M \times M$ . To see the second theorem, note that  $H^1(X) = 0$  implies that, given any graph  $Y = \text{graph}(\mu)$   $C^1$ -close to X with  $d\mu = 0$ , we have  $\mu = dh$  for some  $h: X \to \mathbb{R}$ . Since such an h must have at least 2 critical points,  $\exists$  at least 2 points at which  $\mu = 0$ , i.e. points at which Y intersects X.

## 2. Arnold Conjecture

**Arnold's conjecture:** Let  $(M,\omega)$  be compact,  $f \in \operatorname{Ham}(M,\omega)$  the time 1 flow of  $X_{H_t}$  for  $H_t: M \to \mathbb{R}$  a 1-periodic Hamiltonian  $(H: M \times \mathbb{R} \to \mathbb{R} \text{ smooth with } H_{t+1} = H_t)$ . Then the number of fixed points of f is at least the minimal number of critical points of a smooth function on M. Moreover, assume the fixed points of f are nondegenerate, i.e. if f(x) = x then  $\det (d_x f - \operatorname{id}) \neq 0$ . Then  $\#\operatorname{Fix}(f)$  is at least the minimal number of critical points of a Morse function on M, which in turn is  $\geq \sum_i \dim H^i(M)$ .

Remark. The last inequality follows from classical Morse theory. Given a Morse function f on a manifold M (equipped with a Riemannian metric satisfying the Morse-Smale condition), we have the Morse complex  $C^i$  generated by critical points of index i, and the Morse differential  $d: C^i \to C^{i+1}$  which counts gradient trajectories between critical points. Then  $H^*(C^*, d) \simeq H^*(M)$ , so  $\#\text{Fix}(f) = \sum \dim C^i \ge \sum \dim H^i$ .

The case where  $H_t = H$  is independent of t is easy: if p is a critical point of H then  $X_H(p) = 0$  so the flow f fixes p. The general case was proved by Conley-Zehnder, Floer, Hofer-Salamon, Ono, Fukaya-Ono, Li-Tian, ... using Floer homology. Floer homology is formally the  $\infty$ -dimensional Morse theory of a functional on a covering of the loop space,  $\widehat{\Omega M} = \{\gamma: S^1 \to M \text{ contractible} + \text{homotopy class of disc with } \partial D = \gamma\}$ :

(1) 
$$\mathcal{A}_H: \widetilde{\Omega M} \to \mathbb{R}, \quad \mathcal{A}_H(\gamma) = -\int_{D^2} u^* \omega - \int_{S^1} H(t, \gamma(t)) dt$$

where the first term involves  $u: D^2 \to M$  with  $u(\partial D) = \gamma$  in the given homotopy class.

Given  $v: S^1 \to \gamma^*TM$  (a vector field along  $\gamma$ ), the differential of  $\mathcal{A}_H$  is given by

$$D\mathcal{A}_{H(\gamma)}(v) = -\int_{S^1} \omega(v(t), \dot{\gamma}(t)) dt - \int_{S^1} dH_{t(\gamma(t))}(v(t)) dt = \int_{S^1} (i_{\dot{\gamma}(t)}\omega - dH_t)(v(t)) dt.$$

Since  $dH_t = i_{X_t}\omega$ , this vanishes  $\forall v$  if and only if  $\dot{\gamma}(t) = X_t(\gamma(t))$ , i.e.  $\gamma$  is a periodic orbit of the flow. Hence critical points of  $\mathcal{A}_H$  correspond to fixed points of f. Moreover, formally gradient trajectories of  $\mathcal{A}_H$  correspond to solutions  $u : \mathbb{R} \times S^1 \times M$ ,  $(s,t) \mapsto u(s,t)$  of the PDE

(2) 
$$\frac{\partial u}{\partial s} + J(u) \left( \frac{\partial u}{\partial t} - \nabla H_t(u) \right) = 0.$$

---

## SYMPLECTIC GEOMETRY, LECTURE 7

Prof. Denis Auroux

## 1. Floer homology

For a Hamiltonian diffeomorphism  $f:(M,\omega)\to (M,\omega), f=\phi_H^1, H_t:M\to\mathbb{R}$  1-periodic in t, we want to look for fixed points of f, i.e. 1-periodic orbits of  $X_H$ ,  $x'(t)=X_{H_t}(x(t))$ . We consider the Floer complex  $CF^*(f)$ , whose basis are 1-periodic orbits; these correspond to critical points of the action functional  $\mathcal{A}_H$  on a covering of the free loop space  $\Omega(M)$ . The differential 'counts' solutions of Floer's equations

(1) 
$$u: \mathbb{R} \times S^1 \to M, \ \frac{\partial u}{\partial s} + J(u(s,t))(\frac{\partial u}{\partial t} - X_{H_t}(u)) = 0$$

such that  $\lim_{s\to\pm\infty} u(s,\cdot) = x_{\pm}$  (1-periodic orbits). The solutions are formal gradient flow lines of  $\mathcal{A}_H$  between the critical points  $x_{\pm}$ .

**Theorem 1** (Arnold's conjecture). If the fixed points of f are nondegenerate, then  $\#\text{Fix}(f) \ge \sum_i \dim H^i(M)$ , i.e.  $\#\text{Fix}(f) = \text{rk } CF^* \ge \text{rk } HF^* = \text{rk } H^*(CF^*, \partial) = \text{rk}H^*(M)$ .

1.1. Lagrangian intersections. There is a notion of Lagrangian Floer homology, which is not always defined (in fact, there are explicit obstructions to its existence). The idea is to count intersections of Lagrangian submanifolds  $L, L' \subset M$  in a manner which is invariant under Hamiltonian deformations (isotopies). Assume that L and L' are transverse (if not, e.g. when L = L', replace the submanifold L by the graph  $L_t$  of an exact 1-form in  $T^*L$ ). To define Floer homology, one defines a complex  $CF^*(L, L')$  whose basis is the set of intersection points, and whose differential is given by  $\partial p = \sum_q n_{p,q} q$ , where  $n_{p,q}$  counts solutions to

(2) 
$$u: \mathbb{R} \times [0,1] \to M, u(\mathbb{R} \times 0) \subset L, u(\mathbb{R} \times 1) \subset L', \frac{\partial u}{\partial s} + J \frac{\partial u}{\partial t} = 0$$

Under suitable assumptions, one finds that  $\partial^2 = 0$ , giving us a Floer homology

(3) 
$$HF^*(L, L') = H^*(CF^*(L, L'), \partial)$$

which is invariant under Hamiltonian deformations of L, L'. Moreover,  $\operatorname{rk} HF^* \leq \operatorname{rk} CF^* = |L \cap L'|$ .

**Theorem 2** (Floer, Oh, Fukaya-Oh-Ohta-Ono). Given a compact Lagrangian submanifold  $L \subset M$  which is "relatively spin" (i.e.  $w_2(TL) \in \text{Im}\{i^* : H^2(M, \mathbb{Z}/2\mathbb{Z}) \to H^2(L, \mathbb{Z}/2\mathbb{Z})\}$ ) s.t.  $i_* : H_1(L, \mathbb{Q}) \to H_1(M, \mathbb{Q})$  is injective, then  $\forall \psi \in \text{Ham}(M, \omega)$  s.t.  $\psi(L)$  intersects L transversely,  $\#(L \cap \psi(L)) \geq \sum \dim H_i(L, \mathbb{Q})$ .

Remark. Applying this theorem to the diagonal  $\Delta = \Delta(M) \subset M \times M$  and the graph of a Hamiltonian diffeomorphism f on M, one recovers Arnold's conjecture.

## 2. Almost-Complex Structures

To begin, we will study complex structures on vector spaces.

**Definition 1.** A complex structure on a vector space V is an endomorphism  $J: V \to V$  s.t.  $J^2 = -I$ . Thinking of this J as multiplication by i turns V into a complex vector space, (x+iy)v = xv + yJv. If V is a symplectic vector space with symplectic form  $\Omega$ , a complex structure is compatible if  $G(u,v) = \Omega(u,Jv)$  is a positive symmetric inner product. Note that being symmetric is equivalent to  $\Omega(Ju,Jv) = \Omega(u,v)$ , and being positive is precisely  $\Omega(u,Ju) > 0 \ \forall u \neq 0$ .

Example. Let  $V = (\mathbb{R}^{2n}, \Omega_0)$  be the standard symplectic vector space, with standard basis  $e_1, \ldots, e_n, f_1, \ldots, f_n$ , and define  $J_0$  by  $e_i \mapsto f_i, f_i \mapsto -e_i$ . Then

(4) 
$$J_0^2 = -\mathrm{id} , G_0(u, v) = \Omega_0(u, J_0 v) \implies G_0(e_i, e_i) = 1, G_0(f_i, f_i) = 1$$

and all other pairings are 0. In matrix terms,  $\Omega_0 = \begin{pmatrix} 0 & I \\ -I & 0 \end{pmatrix}$ , and  $J_0 = \begin{pmatrix} 0 & -I \\ I & 0 \end{pmatrix}$ , so  $G_0 = \Omega_0 J_0 = I$ . This gives us a natural isomorphism with  $\mathbb{C}^n$ .

**Proposition 1.** If  $(V,\Omega)$  is a symplectic vector space,  $\exists$  a compatible J. Moreover, given any positive inner product  $\langle \cdot, \cdot \rangle$  on V, we can build an  $\Omega$ -compatible complex structure on V canonically (though it has no direct relation to the given inner product).

Proof. For the first part, taking  $J=J_0$  in a standard basis gives the desired endomorphism. For the second part, by the nondegeneracy of  $\Omega$ , we have isomorphisms  $u\mapsto\Omega(u,\cdot)$  and  $u\mapsto\langle u,\cdot\rangle$  from V to  $V^*$ . We thus obtain an endomorphism  $A=\langle\rangle^{-1}\circ\Omega$  s.t.  $\Omega(u,v)=\langle Au,v\rangle$ . A is invertible and skew-symmetric w.r.t.  $\langle\rangle$ , i.e.  $A^*=-A$  (since  $\Omega(v,u)=\langle Av,u\rangle=\langle V,A^*u\rangle=\langle A^*v,v\rangle=-\Omega(u,v)=-\langle Au,v\rangle$ ). Thus,  $AA^*=-A^2$  is symmetric and positive definite, therefore diagonalizable with real, strictly positive eigenvalues. This implies the existence of a square root  $\sqrt{AA^*}(=\operatorname{diag}(\sqrt{\lambda_i}))$ , so define  $J=(\sqrt{AA^*})^{-1}A$ . (Note that the decomposition  $A=\sqrt{AA^*}J$  gives a "polar decomposition" of A.) A commutes with  $\sqrt{AA^*}$ : letting  $V_i$  be the eigenspace of  $AA^*$  with eigenvalue  $\lambda_i$ , or similarly that of  $\sqrt{AA^*}$  with eigenvalue  $\sqrt{\lambda_i}$ , we find that,

(5) 
$$\forall v \in V_i, (AA^*)Av = -A^3v = A(AA^*)v = \lambda_i Av \implies Av \in V_i$$

So J also commutes with A and with  $\sqrt{AA^*}$ , and thus is skew-symmetric

(6) 
$$J^* = A^* (\sqrt{AA^*})^{-1} = -A(\sqrt{AA^*})^{-1} = -J$$

and orthogonal

(7) 
$$J^*J = A^*(\sqrt{AA^*})^{-1}(\sqrt{AA^*})^{-1}A = id$$

In particular,  $J^2 = -J^*J = -id$ . For compatibility, note that

$$\Omega(Ju, Jv) = \langle AJu, Jv \rangle = \langle JAu, Jv \rangle = \langle Au, v \rangle = \Omega(u, v)$$

(8) 
$$\Omega(u, Ju) = \langle Au, Ju \rangle = \langle -JAu, u \rangle = \langle -(\sqrt{AA^*})^{-1}AAu, u \rangle$$
$$= \langle (\sqrt{AA^*})^{-1}(AA^*)u, u \rangle = \langle (\sqrt{AA^*})u, u \rangle > 0$$

thus completing the proof.

Remark. Note that  $G(u,v) = \Omega(u,Jv) = \langle \sqrt{AA^*}u,v \rangle$ , so if  $\langle \cdot,\cdot \rangle$  was already compatible with  $\Omega$ , then  $AA^* = I, J = A, G = \langle \cdot,\cdot \rangle$ .

**Definition 2.** An almost-complex structure on a manifold M is  $J \in \text{End}(TM)$  s.t.  $J^2 = -I$  (i.e.  $\forall x \in M, J_x$  is a complex structure on  $T_xM$ ). If  $M = (M, \omega)$  is a symplectic manifold, J is compatible if  $\forall x \in M, J_x$  is  $\omega_x$ -compatible, with associated Riemannian metric  $g_x(u, v) = \omega_x(u, J_xv)$ . We say that  $(\omega, g, J)$  is a compatible triple, with any two determining the third.

---

## SYMPLECTIC GEOMETRY, LECTURE 8

## Prof. Denis Auroux

## 1. Almost-complex Structures

Recall compatible triples  $(\omega, g, J)$ , wherein two of the three determine the third  $(g(u, v) = \omega(u, Jv), \omega(u, v) = g(Ju, v), J(u) = \tilde{g}^{-1}(\tilde{\omega}(u))$  where  $\tilde{g}, \tilde{\omega}$  are the induced isomorphisms  $TM \to T^*M$ ).

**Proposition 1.** For  $(M, \omega)$  a symplectic manifold with Riemannian metric  $g, \exists a$  canonical almost complex structure J compatible with  $\omega$ .

*Idea*. Do polar decomposition on every tangent space.

**Corollary 1.** Any symplectic manifold has compatible almost-complex structures, and the space of such structures is path connected.

*Proof.* For the first part, using a partition of unity gives a Riemannian metric, so the rest follows from the proposition. For the second part, given  $J_0, J_1$ , let  $g_i = \omega(\cdot, J_i \cdot)$  for i = 0, 1 and set  $g_t = (1 - t)g_0 + tg_1$ . Each of these (for  $t \in [0,1]$ ) is a metric, and gives an  $\omega$ -compatible  $\tilde{J}_t$  by polar decomposition, with  $\tilde{J}_0 = J_0$  and  $\tilde{J}_1 = J_1$ .

The mechanism of the proof also gives

**Proposition 2.** The set  $\mathcal{J}(T_xM,\omega_x)$  of  $\omega_x$ -compatible complex structures on  $T_xM$  is contractible, i.e.  $\exists h_t : \mathcal{J}(T_xM,\omega_x) \to \mathcal{J}(T_xM,\omega_x)$  for  $t \in [0,1], h_0 = \mathrm{id}, h_1 = \mathcal{J} \to J_0, h_t(J_0) = J_0 \forall t$ .

Corollary 2. The space of compatible almost-complex structures on  $(M, \omega)$  is contractible. It is the space of sections of a bundle whose fibers are contractible by the previous proposition.

More generally, let  $E \to M$  be a vector bundle.

**Definition 1.** A metric on E is a family of positive-definite scalar products  $\langle \cdot, \cdot \rangle_x : E_x \times E_x \to \mathbb{R}$ . E is symplectic (resp. complex) if there is a family of nondegenerate skew-symmetric forms  $\omega_x : E_x \times E_x \to \mathbb{R}$  (resp. complex structures  $J_x : E_x \to E_x$ ,  $J_x^2 = -1$ ).

Then metrics always exist, and every sympletic vector bundle is a complex vector bundle and vice versa.

**Proposition 3.** For (M, J) an almost-complex manifold,  $\omega_0, \omega_1$  two symplectic forms compatible with J,  $\omega_t = (1-t)\omega_0 + t\omega_1$  is symplectic and J-compatible  $\forall t \in [0,1]$  (i.e. the space of J-compatible  $\omega$  is convex).

Note that

- The space of such  $\omega$  might be empty, as there are almost complex manifolds (like  $S^6$ ) which have no symplectic structures.
- Not every manifold has an almost-complex structure (e.g.  $S^4$ , by the Ehresman-Hopf theorem).

*Problem.*  $\exists$  an almost-complex structure  $\Leftrightarrow \exists$  a nondegenerate 2-form.

• The proposition works if we put *tame* instead of compatible, i.e. require  $\omega(u, Ju) > 0 \ \forall u \neq 0$  but not symmetry.

*Proof.*  $\omega_t$  is closed and  $\omega_t(u, Ju) = (1 - t)\omega_0(u, Ju) + t\omega_1(u, Ju) > 0 \ \forall u \neq 0$ , so  $\omega_t$  is nondegenerate and thus symplectic. Moreover,  $g_t(u, v) = \omega_t(u, Jv) = (1 - t)g_0(u, v) + tg_1(u, v)$  is a metric.

**Definition 2.**  $X \subset (M,J)$  is an almost-complex submanifold if J(TX) = TX, i.e.  $\forall x \in X, v \in T_xX$ ,  $Jv \in T_xX$ .

**Proposition 4.** If X is an almost-complex submanifold in compatible  $(M, \omega, J)$ , then X is symplectic (i.e.  $\omega|_X$  is nondegenerate).

Proof.  $\forall u \in T_x X, u \neq 0, Ju \in T_x X$  and  $\omega(u, Ju) > 0$ , so  $\forall u \in T_x X \setminus \{0\}, \omega(u, \cdot)|_{T_x X} \in T_x^* X$  is nonzero, giving us an isomorphism  $TX \to T^* X$  as desired.

Let  $(\mathbb{R}^{2n}, \Omega_0, J_0, g_0)$  be the standard symplectic structure, complex structure, and metric on  $\mathbb{R}^{2n}$ .

- Sp $(2n, \mathbb{R})$  is the group of linear symplectomorphisms of  $(\mathbb{R}^{2n}, \Omega_0)$ , i.e.  $\{A \in GL(2n, \mathbb{R}) | \Omega_0(Au, Av) = \Omega(u, v) \ \forall u, v \}$ .
- $GL(n,\mathbb{C})$  is the group of  $\mathbb{C}$ -linear automorphisms of  $(\mathbb{R}^{2n},J_0)$ , i.e.  $\{A|AJ_0=J_0A\}$ .
- O(2n) is the group of isometries of  $(\mathbb{R}^{2n}, g_0)$ , i.e.  $\{A|A^tA=1\}$ .
- $U(n) = GL(n, \mathbb{C}) \cap O(2n)$ .

**Proposition 5.**  $\operatorname{Sp}(2n) \cap O(2n) = \operatorname{Sp}(2n) \cap \operatorname{GL}(n,\mathbb{C}) = O(2n) \cap \operatorname{GL}(n,\mathbb{C}) = U(n)$ .

*Proof.* The intersection of any two of these sets is the set of automorphisms preserving two of the three in a compatible triple, and thus must preserve all of them.  $\Box$ 

- For  $(V, \Omega, J)$  a symplectic vector space with compatible almost-complex structure,  $\exists$  an isomorphism  $(V, \Omega, J) \xrightarrow{\sim} (\mathbb{R}^{2n}, \Omega_0, J_0)$ .
- The space  $\Omega(V)$  of all symplectic structures on V is  $\cong \operatorname{GL}(V)/\operatorname{Sp}(V,\Omega_0) \cong \operatorname{GL}(2n,\mathbb{R})/\operatorname{Sp}(2n)$ , as GL(V) acts transitively on  $\Omega(V)$  by  $\phi \mapsto \phi^*\Omega_0$  with stabilizer  $\operatorname{Sp}(V,\Omega)$ .
- The space  $\mathcal{J}(V)$  of almost-complex structures on V is  $\cong \mathrm{GL}(V)/\mathrm{GL}(V,J) \cong \mathrm{GL}(2n,\mathbb{R})/\mathrm{GL}(n,\mathbb{C})$ .
- The space  $\mathcal{J}(V,\Omega)$  of  $\Omega$ -compatible J's on V is  $\cong \operatorname{Sp}(V,\Omega)/\operatorname{Sp}(V,\Omega) \cap GL(V,J) \cong \operatorname{Sp}(2n,\mathbb{R})/U(n)$ .
- The constractibility of  $\mathcal{J}(V,\Omega)$  is now the fact that  $\operatorname{Sp}(2n,\mathbb{R})$  retracts onto its subgroup U(n).

## 2. Vector Bundles and Connections

For  $E \to M$  a real or complex vector bundle, we have an exact sequence

$$(1) 0 \to E_x \to T_p E \stackrel{d\pi}{\to} T_x M \to 0$$

for each  $p \in E, x = \pi(p)$ . Here,  $E_x \subset T_p E$  gives the set of vertical directions: we would like a splitting  $T_p E = E_x \oplus (T_p E)^{horiz}$ , i.e. a way to transport from one fiber to another. The data required to do this is a connection.

**Definition 3.** A connection  $\nabla$  on E is an  $\mathbb{R}$  or  $\mathbb{C}$ -linear mapping  $C^{\infty}(M, E) \to C^{\infty}(M, T^*M \otimes E) = \Omega^1(M, E)$  s.t.  $\nabla (f\sigma) = df \cdot \sigma + f \nabla \sigma$ . For  $v \in T_xM$ , we let  $\nabla_v$  denote the mapping  $\sigma \mapsto \nabla \sigma(v)$ .

Choose a local trivialization of E, i.e. a frame of sections  $e_i$  s.t.  $\mathbb{R}^r$  (or  $\mathbb{C}^r$ )× $U \cong E|_U$ ,  $(\xi_1, \ldots, \xi_r) \mapsto \sum \xi_i e_i$ . Then  $\nabla \sigma = \nabla(\sum \xi_i e_i) = \sum (d\xi_i)e_i + \xi_i \nabla e_i$ , i.e. locally  $\nabla = d + A$ , where  $A = (a_{ij}) \in \Omega^1(M, \operatorname{End}(E))$  is a matrix-valued 1-form (the *connection* 1-form) with  $a_{ij}$  the component of  $\nabla e_j$  along  $e_i$ . Globally, given  $\nabla, \nabla', \nabla(fs) - \nabla'(fs) = f(\nabla s - \nabla's)$ , so  $\nabla - \nabla'$  is  $C^{\infty}(M, E)$ -linear and the space of connections is an affine space modeled on  $\Omega^1(M, \operatorname{End}(E))$ .

2.1. **Horizontal Distribution.** Let  $\sigma: M \to E$  be a section,  $d_x \sigma: T_x M \to T_{\sigma(x)} E$  the induced map. Then  $\nabla \sigma(x) \in T_x^* M \otimes E_x$  depends only on  $d\sigma(x)$ . Thus, we can also think of  $\nabla$  as a projection  $\pi^{\nabla}: T_{\sigma(x)} E \to E_x$ , with  $\nabla_v \sigma = \pi^{\nabla} (d\sigma(v))$ . Then  $\mathcal{H}^{\nabla} = \text{Ker } \pi^{\nabla}$  is the horizontal subspace at p(x).

**Definition 4.** For  $\langle \cdot, \cdot \rangle$  a Euclidean or Hermitian metric on E,  $\nabla$  is compatible with the metric if  $d\langle \sigma, \sigma' \rangle = \langle \nabla \sigma, \sigma' \rangle + \langle \sigma, \nabla \sigma' \rangle$ .

As above, locally one can find an orthonormal frame of sections  $(e_i)$ ,  $\langle e_i, e_j \rangle = \delta_{i,j}$ . Writing  $\nabla = d + A$  in this trivialization, the compatibility becomes

(2) 
$$\langle \nabla \xi, \eta \rangle + \langle \xi, \nabla \eta \rangle = \langle d\xi, \eta \rangle + \langle A\xi, \eta \rangle + \langle \xi, d\eta \rangle + \langle \xi, A\eta \rangle$$

Since  $d\langle \xi, \eta \rangle = \langle d\xi, \eta \rangle + \langle \xi, d\eta \rangle$ , this means that the connection 1-form A must be skew-symmetric (or anti-Hermitian).

Also note that  $\nabla$  on E induces a  $\nabla^*$  on  $E^*$  by  $d(\phi(\sigma)) = \langle \nabla^* \phi, \sigma \rangle + \langle \phi, \nabla \sigma \rangle$ , and similarly for  $E \otimes F$ , etc.

---

## SYMPLECTIC GEOMETRY, LECTURE 9

Prof. Denis Auroux

## 1. Curvature

Let  $\nabla$  be a connection as before: then we get a curvature tensor  $R^{\nabla} \in \Omega^2(M, \operatorname{End}(E))$ , i.e. a matrix of 2-forms (in local coordinates).

**Definition 1.** Given a local section  $\sigma$  and vector fields U, V,

(1) 
$$R^{\nabla}(U, V)\sigma = \nabla_{U}\nabla_{V}\sigma - \nabla_{V}\nabla_{U}\sigma - \nabla_{[U, V]}\sigma$$

**Proposition 1.**  $R^{\nabla}$  is a tensor (i.e. it is defined pointwise, depending only on  $\sigma(x)$  and not on its derivatives).

Remark. Use local coordinates, let  $f_i = \frac{\partial}{\partial x_i}$ : then  $R^{\nabla} = \sum_{i < j} (\nabla_{f_i} \nabla_{f_j} \sigma - \nabla_{f_j} \nabla_{f_i} \sigma) dx_i \wedge dx_j$ .

In a local trivialization  $(e_i)$ ,  $\nabla = d + A$ ,  $A \in \Omega^1(\text{End } E)$ , i.e.  $\nabla e_j = \sum_i a_{ij} e_i$ . Then

(2)

$$R^{\nabla}(U, V)e_{j} = \nabla_{U}(\sum_{i} a_{ij}(V)e_{i}) - \nabla_{V}(\sum_{i} a_{ij}(U)e_{i}) - \sum_{i} a_{ij}([U, V])e_{i}$$

$$= \sum_{i} (U \cdot a_{ij}(V))e_{i} + \sum_{i} a_{ki}(U)a_{ij}(V)e_{k} - \sum_{i} (V \cdot a_{ij}(U))e_{i} - \sum_{i} a_{ki}(V)a_{ij}(U)e_{k} - \sum_{i} a_{ij}([U, V])e_{i}$$

The component along  $e_i$  is

(3) 
$$R_{ij}^{\nabla}(U,V) = U \cdot a_{ij}(V) - V \cdot a_{ij}(U) - a_{ij}([U,V]) + \sum_{\ell} a_{i\ell}(U) a_{\ell j}(V) - a_{i\ell}(V) a_{\ell j}(U)$$

That is,  $R_{ij}^{\nabla} = da_{ij} + \sum_{\ell} a_{i\ell} \wedge a_{\ell j}$ .

Remark. We can take this as the definition of  $R^{\nabla}$ , i.e. write  $R^{\nabla} = dA + A \wedge A$ .

If we change trivializations  $(e_1, \ldots, e_n) \mapsto (e'_1, \ldots e'_n)$  via  $e'_j = \sum g_{ij}e_i$  s.t. g is a matrix-valued function, then we can write  $s = \sum \xi'_j e'_j = \sum g_{ij} \xi'_j e_i$ . In other words, if s corresponds to a vector  $\xi$  in the trivialization  $(e_i)$  and  $\xi'$  in the trivialization  $e'_i$ , then  $\xi = g\xi'$ , i.e.  $\xi_i = \sum g_{ij}\xi'_j$ . Now we write  $\nabla s$  in the trivialization:  $\nabla(\xi)_e = (d\xi + A\xi)_e$  for A the connection 1-form in the trivialization  $(e_i)$ . Changing trivializations gives  $\nabla(g^{-1}\xi)_{e'} = g^{-1}(d\xi + A\xi)|_{e'}$ , (???)

i.e.  $\nabla(\xi')_{e'} = (g^{-1}(d(g\xi') + Ag\xi'))_{e'} = d\xi' + (g^{-1}Ag + g^{-1}d(g))\xi'$ . Thus, the connection 1-form in the new trivialization is  $A' = g^{-1}Ag + g^{-1}dg$  (as matrix-valued form).

**Proposition 2.**  $dA' + A' \wedge A' = g^{-1}(dA + A \wedge A)g$ , i.e.  $R^{\nabla} = dA + A \wedge A$  is a well-defined element of  $\Omega^2(M, \operatorname{End} E)$  independently of trivialization.

Recall that the product here is matrix multiplication, with the entries 1-forms multiplied under  $\wedge$ .

*Proof.* First, gA' = Ag + dg: taking exterior derivatives, we get  $dg \wedge A' + gdA' = dA \cdot g - A \wedge dg + 0$ . Thus,

(4) 
$$g(dA' + A' \wedge A') = (dA \cdot g - A \wedge dg - dg \wedge A') + gA' \wedge A'$$
$$= dA \cdot g - A \wedge dg - dg \wedge A' + (Ag + dg) \wedge A'$$
$$= dA \cdot g - A \wedge dg + Ag \wedge A'$$
$$= dA \cdot g - A \wedge dg + A \wedge (dg + Ag) = (dA + A \wedge A)g$$

---

## SYMPLECTIC GEOMETRY, LECTURE 10

Prof. Denis Auroux

## 1. Curvature and the Covariant Derivative

Let  $\nabla$  be a connection,  $R^{\nabla} \in \Omega^2(M, \text{End } E)$  its curvature, where

(1) 
$$R^{\nabla}(u,v)s = \nabla_u \nabla_v s - \nabla_v \nabla_u s - \nabla_{[u,v]} s$$

Last time, we saw that in a local trivialization,  $\nabla = d + A$ , where A is a 1-form with values in  $\operatorname{End}(E)$ , and  $R^{\nabla} = dA + A \wedge A$ . Moreover, a change of basis given by  $g \in C^{\infty}(U, \operatorname{End}(E))$  acts by

(2) 
$$A \mapsto g^{-1}Ag + g^{-1}dg, R^{\nabla} \mapsto g^{-1}R^{\nabla}g$$

We can extend the covariant derivative  $\nabla: C^{\infty}(M, E) \to \Omega^{1}(M, E)$  to an operator  $d^{\nabla}: \Omega^{p}(M, E) \to \Omega^{p+1}(M, E)$ . Locally,  $\Omega^{p}(M, E)$  is given by sums  $\sum \alpha_{i} s_{i}$ , where  $\alpha_{i} = dx_{i_{1}} \wedge \cdots \wedge dx_{i_{p}}$  are p-forms and  $e_{i} = s_{i_{1} \cdots i_{p}}$  are sections of E, and  $d^{\nabla}$  maps this to  $\sum (\nabla s_{i}) \wedge \alpha_{i} + s_{i} d\alpha_{i}$ . In a trivialization  $\nabla = d + A$ , we have

(3) 
$$d^{\nabla} \begin{pmatrix} \alpha_1 \\ \vdots \\ \alpha_r \end{pmatrix} = d \begin{pmatrix} \alpha_1 \\ \vdots \\ \alpha_r \end{pmatrix} + A \wedge \begin{pmatrix} \alpha_1 \\ \vdots \\ \alpha_r \end{pmatrix}$$

That is,  $d^{\nabla} = d + A \wedge (\cdot)$ .

**Proposition 1.**  $R^{\nabla} = (d^{\nabla})^2 : \Omega^0(M, E) \to^{d^{\nabla}} \Omega^1(M, E) \to^{d^{\nabla}} \Omega^2(M, E)$ . More generally,

$$(4) R^{\nabla} \wedge \cdot = (d^{\nabla})^2 : \Omega^p(M, E) \to^{d^{\nabla}} \Omega^{p+1}(M, E) \to^{d^{\nabla}} \Omega^{p+2}(M, E)$$

*Proof.* In a local trivialization,

(5) 
$$d^{\nabla}(d^{\nabla}\alpha) = d^{\nabla}(d\alpha + A \wedge \alpha) = d(d\alpha + A \wedge \alpha) + A \wedge (d\alpha + A \wedge \alpha) = (dA) \wedge \alpha - A \wedge d\alpha + A \wedge d\alpha + A \wedge A \wedge \alpha = (dA + A \wedge A) \wedge \alpha$$

as desired.

Remark.  $R^{\nabla}$  can be thought of as an obstruction for  $0 \to C^{\infty}(E) \xrightarrow{d^{\nabla}} \Omega^{1}(E) \xrightarrow{d^{\nabla}} \cdots$  being a complex. If the manifold is flat, i.e.  $R^{\nabla} = 0$ , then we obtain a twisted de Rham cohomology with coefficients in E.  $R^{\nabla}$  is also an obstruction to the integrability of the horizontal distribution  $\mathcal{H}^{\nabla}$ , i.e. homotopy invariance of parallel transport.

When E = TM for (M,g) a Riemannian manifold, there is a unique metric  $(X \cdot g(u,v) = g(\nabla_X u,v) + g(u,\nabla_X v))$  connection on TM s.t.  $\nabla_X Y - \nabla_Y X = [X,Y]$ , called the *Levi-Cevita* connection. Now, let  $(M,\omega,g,J)$  be a symplectic manifold with a compatible almost complex structure. Then TM is a complex vector bundle, but  $\nabla^{LC}$  is not  $\mathbb{C}$ -linear in general. Indeed, it is  $\mathbb{C}$ -linear  $\Leftrightarrow \nabla J = 0$  for the induced connection  $\nabla$  on  $\mathrm{End}(TM) \Leftrightarrow J$  is integrable (i.e. an actual complex structure).

## 2. Complex Vector Bundles and Chern Classes

Let  $L \to M$  be a complex line bundle,  $\nabla$  a connection (possibly Hermitian w.r.t. a Hermitian metric  $\langle \cdot, \cdot \rangle$ ). In a local trivialization,  $R^{\nabla} = dA \in \Omega^2(M, \mathbb{C})$  (resp.  $\Omega^2(M, i\mathbb{R})$ ) since  $A \in \Omega^1(U, \mathbb{C})$  (resp.  $\Omega^1(M, i\mathbb{R})$ ) has  $A \wedge A = 0$ . Thus,  $R^{\nabla}$  is a closed 2-form, and has a corresponding class  $c = [R^{\nabla}] \in H^2(M, \mathbb{C})$  (resp.  $\Omega^2(M, i\mathbb{R})$ ). For  $\nabla'$  another connection, we have a global decomposition  $\nabla' = \nabla + a$  for  $a \in \Omega^1(M, \mathbb{C})$ , so  $R^{\nabla'} = R^{\nabla} + da$  and  $[R^{\nabla}] = [R^{\nabla'}]$ . Thus, c is an invariant of L independent of  $\nabla$  in  $H^2(M, \mathbb{C})$  (resp.  $H^2(M, i\mathbb{R})$ ). Since we can always choose a connection compatible with a given Hermitian form, we have

**Definition 1.** The first Chern class of L is  $c_1(L) = \left[\frac{1}{2\pi}R^{\nabla}\right] \in H^2(M,\mathbb{R})$ .

Remark. From algebraic topology, we can obtain an associated integer class  $c_1(L) \in H^2(M,\mathbb{Z})$  corresponding to this form.

Now, let  $E \to M$  be a complex vector bundle with connection  $\nabla$ .

**Definition 2.** The total Chern form is

(6) 
$$c(E, \nabla) = \det \left( I + \frac{i}{2\pi} R^{\nabla} \right) \in \bigoplus_{p \ even} \Omega^{p}(M, \mathbb{C})$$

Decomposing this element, we obtain projections  $c_j(E, \nabla) \in \Omega^{2j}(M, \mathbb{C})$ . Here  $I + \frac{i}{2\pi}R^{\nabla}$  is a matrix with entries (const + 2-forms) in a local trivialization, and det is the usual determinant under the  $\wedge$  product. As before, this is independent of change of basis.

*Remark.* By the formula for det  $(I + tM) = 1 + t \cdot \text{Tr}(M) + \cdots$ , we find that  $c_1(E, \nabla) = \frac{i}{2\pi} \text{Tr}(R^{\nabla})$ , and

(7) 
$$c_r(E, \nabla) = \left(\frac{i}{2\pi}\right)^r \det R^{\nabla}$$

We can do the same for any ad-invariant polynomial in  $R^{\nabla}$ , giving Chern-Weil theory (for complex vector bundles, simply get functions of  $c_1, \ldots, c_r$ ).

**Theorem 1.**  $c_j(E,\nabla)$  is closed, and  $c_j(E) = [c_j(E,\nabla)] \in H^{2j}(M,\mathbb{R})$  is independent of  $\nabla$ .

*Proof.* Closedness follows from the Bianchi identity for  $d^{\nabla}(R^{\nabla})$ , and independence follows from showing that  $c_j(E, \nabla') - c_j(E, \nabla)$  is a sum of exact terms.

Remark. Another approach involves the Euler class of an oriented rank k real vector bundle  $E \to M$  over a compact, oriented manifold M. Let s be a section of E, chosen so s is transverse to the zero section and  $Z = s^{-1}(0)$  is a smooth, oriented submanifold of codimension k. Then, at a point of Z,  $\nabla s : NZ \to E|_Z$  is an isomorphism. We define  $e(E) = [Z] \in H_{n-k}(M,\mathbb{Z}) \cong H^k(M,\mathbb{Z})$  by Poincaré duality. If E was a rank r  $\mathbb{C}$ -vector bundle, then  $c_r(E) = e(E)$ .

Remark. For  $TM \to M$ ,  $e(TM) \in H^n(M, \mathbb{Z}) = \mathbb{Z} \Leftrightarrow \chi(M) = e(TM) \cdot [M]$ . Moreover, for  $E, \nabla$  a flat connection,  $c_i(E) = 0 \in H^{2j}(M, \mathbb{R})$ .

---

## SYMPLECTIC GEOMETRY, LECTURE 11

Prof. Denis Auroux

## 1. Chern Classes

Let  $E \to M$  be a complex vector bundle,  $\nabla$  a connection on E. Recall that we obtain the Chern classes of E via  $c(E) = \sum c_i(E) = \det \left(I + \frac{i}{2\pi}R^{\nabla}\right)$ .

**Proposition 1.** M compact and oriented  $\implies c_r(E) = e(E) \in H^{2r}(M, \mathbb{Z}).$ 

Let s be a section transverse to the zero section. Let  $Z = s^{-1}(0)$  be its zero set: then

$$[Z] \in H_{2n-2r}(M) \implies PD([Z]) \in H^{2r}(M)$$

is the Euler class of E.

1.1. Chern Classes of Line bundles. We now restrict to understanding the first Chern class of a line bundle. If M is compact, this is precisely the Euler class. Now, consider a closed, oriented surface  $\Sigma$ : any section vanishes at finitely many points, giving us a well-defined degree by counting these points (with sign). Moreover, we have that  $c_1(L) \in H^2(L, \mathbb{Z}) \cong \mathbb{Z}$  is precisely the class s.t.  $c_1(L)[\Sigma] = \deg L$ . Cut  $\Sigma$  into two parts  $U \cup D^2$ , where  $U = \bigvee S^1$  holds all the non-trivial loops. Any complex bundle over  $S^1$  is trivial, so L is trivial over both U and  $D^2$ . To obtain L from  $L|_U$  and  $L_{D^2}$ , we need to identify  $L|_{\partial U} \cong \mathbb{C} \times S^1 \to L|_{\partial D^2} \cong \mathbb{C} \times S^1$ . This corresponds to a map  $S^1 \to \mathbb{C}^*$  modulo homotopy, i.e. an element of  $\pi_1(S^1) \cong \mathbb{Z}$ . This is again deg L.

Remark. Alternatively, since L is trivial over  $D^2$  and U, we have a non-vanishing section s of  $L|_U$ . The Chern class of L measures why this section cannot be extended to all of  $\Sigma$ . Specifically, the Chern class corresponds to the boundary map  $\frac{s}{|s|}: \partial D^2 = S^1 \to S^1$ .

- 1.2. Properties of Chern Classes. Let  $c(E) = \sum c_i(E)$  denote the total Chern class of E (with  $c_0(E) = 1$ ).
  - (1)  $c(E \oplus F) = c(E) \cup c(F)$ .
  - (2) For  $f: X \to M$  a smooth map giving a commutative square

$$\begin{array}{ccc}
f^*E & \longrightarrow E \\
\downarrow & & \downarrow \\
X & \longrightarrow M
\end{array}$$

where  $f^*E = \{(x, v) \in X \times E | f(x) = \pi(v)\}$ , we have  $c(f^*(E)) = f^*(c(E))$ . By the splitting principle, for any  $E \to M$ ,  $\exists f: X \to M$  s.t. in the above square,  $f^*$  is injective on cohomology, and  $f^*E$  splits as a sum of line bundles.

One can define the Chern classes via these properties along with the definition of the first Chern class of a line bundle. Our definition of Chern classes (i.e. via the curvature  $R^{\nabla}$ ) also satisfies these properties.

- (1) Given bundles E, F with connections  $\nabla^E, \nabla^F$ , the connection on the direct sum is precisely  $\nabla^{E \oplus F}(s, t) = (\nabla^E(s), \nabla^F(t))$ , implying that the curvature is  $R^{E \oplus F} = R^E \oplus R^F$  as desired.
- (2) Note that, if s is a local section of E near f(x), then  $s \circ f$  is a local section of  $f^*E$  near x. By the definition of the pullback connection,  $\nabla^{f^*E}(f^*(s)) = f^*(\nabla^E s)$ . Via the definition of curvature, we see that  $f^*(R^{\nabla}) = R^{f^*\nabla}$  as well, implying the desired pullback property.

Remark.  $c_1(L) \in H^2(M,\mathbb{Z})$  completely classifies  $\mathbb{C}$ -line bundles. Moreover, it defines a group isomorphism between the set of line bundles over M under  $\otimes$  with  $H^2(M,\mathbb{Z})$ . To see this, recall that a line bundle is precisely


a collection of local trivializations  $\{f_{\alpha}: L|_{U_{\alpha}} \stackrel{\cong}{\to} U_{\alpha} \times \mathbb{C}\}$  with attaching maps  $g_{\alpha,\beta} \in C^{\infty}(U_{\alpha} \cap U_{\beta}, \mathbb{C}^{*})$  satisfying the cocycle condition

$$g_{\alpha,\beta}g_{\beta,\gamma}g_{\gamma\alpha} = 1$$

on  $U_{\alpha} \cap U_{\beta} \cap U_{\gamma}$ . This corresponds precisely with the Cech cohomology on M, where  $\{g_{\alpha,\beta}\}$  is a 1-cocycle. In this description,  $c_1$  is the connecting map in the long exact sequence

$$(4) \qquad \cdots \to 0 = H^1(M,\underline{\mathbb{C}}) \to H^1(M,\underline{\mathbb{C}}^*) \to^{c_1} H^2(M,\mathbb{Z}) \to H^2(M,\underline{\mathbb{C}}) = 0 \to \cdots$$

associated to the short exact sequence of sheaves  $0 \to \mathbb{Z} \to \underline{\mathbb{C}} \xrightarrow{\exp} \underline{\mathbb{C}}^* \to 0$  where  $\underline{\mathbb{C}}, \underline{\mathbb{C}}^*$  are the sheaves of  $\mathbb{C}^{\infty}$  functions with values in  $\mathbb{C}, \mathbb{C}^*$ . One can also see directly the fact that  $c_1(L \otimes L') = c_1(L) + c_1(L')$  using the definition of the tensor product connection  $\nabla^{L \otimes L'} = \nabla^L \otimes \operatorname{id} + \operatorname{id} \otimes \nabla^{L'}$ .

Now, for  $(M, \omega)$  a symplectic manifold, J a compatible almost-complex structure, (TM, J) is a complex vector bundle, with  $c_j(TM) \in H^{2j}(M, \mathbb{Z})$ . Since the RHS is discrete, we get an invariant of the almost-complex structure up to deformation, and since the space of compatible J's is connected, the complex isomorphism class of (TM, J) is uniquely determined. Explicitly, if  $J_t$  is a family of complex structures on E, the map  $\phi: v \mapsto \frac{1}{2}(v - J_t J_{t_0} v)$  is a complex isomorphism from  $(E, J_{t_0})$  to  $(E, J_t)$  since

(5) 
$$\phi(J_{t_0}v) = \frac{1}{2}(J_{t_0}v + J_tv) = J_t(\frac{1}{2}(v - J_tJ_{t_0}v)) = J_t\phi(v)$$

Thus,  $c_j(TM, J)$  is independent of the choice of almost-complex structure (it is even an invariant of the deformation class of M): for instance,  $c_n(TM) \in H^{2n}(M, \mathbb{Z}) \cong \mathbb{Z}$  is an invariant of the manifold (the *Euler characteristic*).

Remark. For  $1 \leq j \leq n-1$ ,  $c_j$  does depend on the choice of symplectic structure, however: there exists a 4-manifold M with symplectic forms  $\omega_1, \omega_2$  s.t.  $c_1(TM, \omega_1) \neq c_1(TM, \omega_2)$ .

---

## SYMPLECTIC GEOMETRY, LECTURE 12

Prof. Denis Auroux

## 1. Existence of Almost-Complex Structures

Let  $(M, \omega)$  be a symplectic manifold. If J is a compatible almost-complex structure, we obtain invariants  $c_j(TM, J) \in H^{2j}(M, \mathbb{Z})$  of the deformation equivalence class of  $(M, \omega)$ .

Remark. There exist 4-manifolds  $(M^4, \omega_1)$ ,  $(M^4, \omega_2)$  s.t.  $c_1(TM, \omega_1) \neq c_1(TM, \omega_2)$ .

We can use this to obtain an obstruction to the existence of an almost-complex structure on a 4-manifold: note that we have two Chern classes  $c_1(TM, J) \in H^2(M, \mathbb{Z})$  and  $c_2(TM, J) = e(TM) \in H^4(M, \mathbb{Z}) \cong \mathbb{Z}$  if  $M^4$  is closed, compact. Then the class

$$(1) (1+c_1+c_2)(1-c_1+c_2)-1=-c_1^2+2c_2=c_2(TM\oplus \overline{TM},J\oplus \overline{J})=c_2(TM\otimes_{\mathbb{R}}\mathbb{C},i)$$

is independent of J.

More generally, for E a real vector space with complex structure J, we have an equivalence  $(E \otimes_{\mathbb{R}} \mathbb{C}, i) \cong E \oplus \overline{E} = (E, J) \oplus (E, -J)$ . Indeed, J extends  $\mathbb{C}$ -linearly to an almost complex structure  $J_{\mathbb{C}}$  which is diagonalizable with eigenvalues  $\pm i$ . Applying this to vector bundles, we obtain the *Pontrjagin classes* 

(2) 
$$p_1(TM) = -c_2(TM \otimes_{\mathbb{R}} \mathbb{C}) \in H^4(M, \mathbb{Z}) \cong \mathbb{Z}$$

for a 4-manifold M.

**Theorem 1.**  $p_1(TM) \cdot [M] = 3\sigma(M)$ , where  $\sigma(M)$  is the signature of M (the difference between the number of positive and negative eigenvalues of the intersection product  $Q: H_2(M) \otimes H_2(M) \to \mathbb{Z}, [A] \otimes [B] \mapsto [A \cap B]$  dual to the cup product on  $H^2$ ).

Corollary 1.  $c_1^2 \cdot [M] = 2\chi(M) + 3\sigma(M)$ .

Remark. Under the map  $H^2(M, \mathbb{Z}) \to H^2(M, \mathbb{Z}/2\mathbb{Z})$ , the Chern class  $c_1(TM, J)$  gets sent to the Stiefel-Whitney class  $w_2(TM)$ . This means that

(3) 
$$c_1(TM) \cdot [A] \equiv Q([A], [A]) \mod 2 \ \forall [A] \in H_2(M, \mathbb{Z})$$

**Theorem 2.**  $\exists$  an almost complex structure J on  $M^k$  s.t.  $\alpha = c_1(TM, J) \in H^2(M, \mathbb{Z})$  iff  $\alpha$  satisfies

(4) 
$$\alpha^2 \cdot [M] = 2\chi + 3\sigma \text{ and } \alpha \cdot [A] \equiv Q([A], [A]) \mod 2 \ \forall [A] \in H_2(M, \mathbb{Z})$$

Examples:

- On  $S^4$ , if J were an almost complex structure, then  $c_1(TS^4, J) \in H^2(S^4) = 0$ .. However,  $\chi(S^4) = 2$  and  $\sigma(S^4) = 0$ , so  $2 \cdot 2 + 3 \cdot 0$  cannot be  $c_1^2$ , and thus there is no almost complex structure.
- On  $\mathbb{CP}^2$ , we have  $H_2(\mathbb{CP}^2, \mathbb{Z}) = \mathbb{Z}$  generated by  $[\mathbb{CP}^1]$  with intersection product  $Q([\mathbb{CP}^1], [\mathbb{CP}^1]) = 1$  (the number of lines in the intersection of two planes in  $\mathbb{C}^3$ . By Mayer-Vietoris,  $H_2(\mathbb{CP}^2 \# \mathbb{CP}^2, \mathbb{Z}) \cong \mathbb{Z}^2$  has intersection product  $Q = I_{2\times 2} \implies \sigma = 2$  and Euler characteristic  $\chi = 4$ . Now, assume  $c_1(TM, J) = (a, b) \in H_2(M, \mathbb{Z})$ : if there were an almost complex structure,

(5) 
$$a^2 + b^2 = c_1^2 = 2\chi + 3\sigma = 14$$

which is impossible.

## 2. Types and Splittings

Let (M,J) be an almost complex structure, J extended  $\mathbb{C}$ -linearly to  $TM\otimes\mathbb{C}=TM^{1,0}\oplus TM^{0,1}$  (with the decomposition being into +i and -i eigenspaces). Here,  $TM^{1,0}=\{v-iJv|v\in TM\}$  is the set of holomorphic tangent vectors and  $TM^{0,1}=\{v+iJv,v\in TM\}$  is the set of anti-holomorphic tangent vectors. For instance, on  $\mathbb{C}^n$ , this gives

(6) 
$$\frac{1}{2} \left( \frac{\partial}{\partial x_j} - i \frac{\partial}{\partial y_j} \right) = \frac{\partial}{\partial z_j}, \ \frac{1}{2} \left( \frac{\partial}{\partial x_j} + i \frac{\partial}{\partial y_j} \right) = \frac{\partial}{\partial \overline{z}_j}$$

respectively. More generally, we have induced real isomorphisms

(7) 
$$\pi^{1,0}: TM \to TM^{1,0}, v \mapsto v^{1,0} = \frac{1}{2}(v - iJv), \pi^{0,1}: TM \to TM^{0,1}, v \mapsto v^{0,1} = \frac{1}{2}(v + iJv)$$

Then  $(Jv)^{1,0}=i(v^{1,0}),(Jv)^{0,1}=-i(v^{0,1}),$  so  $(TM,J)\cong TM^{1,0}\cong \overline{TM^{0,1}}$  as almost-complex bundles. Similarly, the complexified cotangent bundle decomposes as  $T^*M^{1,0}=\{\eta\in T^*M\otimes\mathbb{C}|\eta(Jv)=i\eta(v)\},T^*M^{0,1}=\{\eta\in T^*M\otimes\mathbb{C}|\eta(Jv)=-i\eta(v)\},$  with maps from the original cotangent bundle given by

$$(8) \hspace{1cm} \eta \mapsto \eta^{1,0} = \frac{1}{2}(\eta - i(\eta \circ J)) = \frac{1}{2}(\eta + iJ^*\eta), \\ \eta \mapsto \eta^{0,1} = \frac{1}{2}(\eta + i(\eta \circ J)) = \frac{1}{2}(\eta - iJ^*\eta)$$

For  $\mathbb{C}^n$ , we find that

$$(9) J^* dx_i = dy_i, J^* dy_i = -dx_i \implies dx_j + i dy_j = dz_j \in (T^* \mathbb{C}^n)^{1,0}, dx_j - i dy_j = d\overline{z_j} \in (T^* \mathbb{C}^n)^{0,1}$$

More generally, on a complex manifold, in holomorphic local coordinates, we have  $T^*M^{1,0} = \text{Span}(dz_j)$ . Note also that  $T^*M^{1,0}$  pairs with  $TM^{0,1}$  trivially.

2.1. **Differential forms.**  $\Omega^k$  splits into forms of type (p,q), p+q=k, with

(10) 
$$\wedge^{p,q} T^* M = (\wedge^p T^* M^{1,0}) \otimes (\wedge^q T^* M^{0,1}) = \bigoplus_{p+q=k} \wedge^{p,q} T^* M$$

**Definition 1.** For  $\alpha \in \Omega^{p,q}(M)$ ,  $\partial \alpha = (d\alpha)^{p+1,q} \in \Omega^{p+1,q}$  and  $\overline{\partial} \alpha = (d\alpha)^{p,q+1} \in \Omega^{p,q+1}$ .

In general,

(11) 
$$d\alpha = (d\alpha)^{p+q+1,0} + (d\alpha)^{p+q,1} + \dots + (d\alpha)^{0,p+q+1}$$

For a function, we have  $df = \partial f + \overline{\partial} f$ . Now, say  $f: M \to \mathbb{C}$  is J-holomorphic if  $\overline{\partial} f = 0 \Leftrightarrow df \in \Omega^{1,0} \Leftrightarrow df(Jv) = idf(v)$ .

2.2. **Dolbeault cohomology.** Assume d maps  $\Omega^{p,q} \to \Omega^{p+1,q} \oplus \Omega^{p,q+1}$ , i.e.  $d = \partial + \overline{\partial}$ . On  $\mathbb{C}^n$ , for instance, we have

$$\partial(\alpha_{I,J}dz_{i_1}\wedge\cdots\wedge dz_{i_p}\wedge d\overline{z}_{j_1}\wedge\cdots\wedge d\overline{z}_{j_q}) = \sum_{k} \frac{\partial\alpha_{IJ}}{\partial z_k}dz_k\wedge dz_{i_1}\wedge\cdots\wedge dz_{i_p}\wedge d\overline{z}_{j_1}\wedge\cdots\wedge d\overline{z}_{j_q}$$
(12)
$$\overline{\partial}(\alpha_{I,J}dz_{i_1}\wedge\cdots\wedge dz_{i_p}\wedge d\overline{z}_{j_1}\wedge\cdots\wedge d\overline{z}_{j_q}) = \sum_{k} \frac{\partial\alpha_{IJ}}{\partial\overline{z}_k}d\overline{z}_k\wedge dz_{i_1}\wedge\cdots\wedge dz_{i_p}\wedge d\overline{z}_{j_1}\wedge\cdots\wedge d\overline{z}_{j_q}$$

Then,  $\forall \beta \in \Omega^{p,q}, 0 = d^2\beta = \partial \partial \beta + \partial \overline{\partial} \beta + \overline{\partial} \partial \beta + \overline{\partial} \overline{\partial} \beta \implies \partial^2 = 0, \overline{\partial}^2 = 0, \partial \overline{\partial} + \overline{\partial} \partial = 0.$  Since  $\overline{\partial}^2 = 0$ , we obtain a complex  $0 \to \Omega^{p,0} \xrightarrow{\overline{\partial}} \Omega^{p,1} \cdots$ .

**Definition 2.** The Dolbeault cohomology of M is

(13) 
$$H^{p,q}(M) = \frac{\operatorname{Ker}(\overline{\partial}: \Omega^{p,q} \to \Omega^{p,q+1})}{\operatorname{Im}(\overline{\partial}: \Omega^{p,q-1} \to \Omega^{p,q})}$$

In general, this is not finite-dimensional. We'll see that on a compact Kähler manifold, i.e. a manifold with compatible symplectic and complex structures,  $H^k(M,\mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}(M)$ .

2.3. Integrability. Let (M, J) be a manifold with almost-complex structure.

**Definition 3.** The Nijenhuis tensor is the map N(u, v) = [Ju, Jv] - J[u, Jv] - J[Ju, v] - [u, v] for u, v vector fields on M.

In fact, 
$$N(u, v) = -8\text{Re}([u^{1,0}, v^{1,0}])^{0,1}$$
.

---

## SYMPLECTIC GEOMETRY, LECTURE 13

Prof. Denis Auroux

## 1. Integrability of Almost-Complex Structures

Recall the following:

**Definition 1.** The Nijenhuis tensor is the form

(1) 
$$N_J(u,v) = [Ju, Jv] - J[u, Jv] - J[Ju, v] - [u, v]$$

**Proposition 1.**  $N(u, v) = -8\text{Re}([u^{1,0}, v^{1,0}]^{0,1}).$ 

*Proof.*  $[u^{1,0},v^{1,0}]=\frac{1}{4}[u-iJu,v-iJv]=\frac{1}{4}([u,v]-i[Ju,v]-i[u,Jv]-[Ju,Jv])$ . Taking the real part of the (0,1) component gives the desired expression.

**Corollary 1.** N=0 globally  $\Leftrightarrow [T^{1,0},T^{1,0}] \subset T^{1,0}$ , i.e. the Lie bracket preserves the splitting  $T^{1,0} \oplus T^{0,1}$ .

**Proposition 2.** N is a tensor, i.e. in depends only on the values of u, v.

Note also that N is by definition skew-symmetric an J-antilinear. In fact, N can be taken as a complex map  $\bigwedge^2(TM,J) \to (TM,-J)$ . Thus, if dim  $\mathbb{R}M=2, N=0$ , since N(u,Ju)=-JN(u,u)=0.

**Definition 2.** An almost-complex structure J is a complex structure if it is integrable, i.e. if  $\exists$  local holomorphic coordinates s.t.  $(M,J) \cong (\mathbb{C}^n,i)$  locally.

**Proposition 3.** If J is a complex structure, N = 0.

*Proof.* This follows from the fact that, on  $T^{1,0}\mathbb{C}^n$ ,  $\left[\frac{\partial}{\partial z_i}, \frac{\partial}{\partial z_i}\right] = 0$ .

**Theorem 1** (Newlander-Nirenberg).  $N \equiv 0 \Leftrightarrow J$  is integrable.

*Proof.* Sketch: producing holomorphic coordinates is equivalent to giving a frame on the tangent bundle of the form  $\{\frac{\partial}{\partial z_i}\}$ , which is the same as finding a basis  $\{e_i\}$  of  $T^{1,0}$  s.t.  $[e_i,e_j]=0$ .

This does not make the problem of determining whether a manifold has some complex structure trivial: for instance, it is currently unknown whether  $S^6$  has an integrable complex structure.

We can extend our tensor to differential forms to obtain alternate ways to determine integrability.

**Proposition 4.** The dual map  $N^*: \bigwedge^{0,1} T^*M \to \bigwedge^{2,0} T^*M$  is precisely the map  $N^*\alpha = (d\alpha)^{(2,0)}$ .

*Proof.* For  $\alpha \in \Omega^{0,1}$ , we have a decomposition  $d\alpha = \partial \alpha + \overline{\partial} \alpha + (d\alpha)^{(2,0)} \in \Omega^{1,1} \oplus \Omega^{0,2} \oplus \Omega^{2,0}$ . Moreover,

(2) 
$$d\alpha^{(2,0)}(u,v) = d\alpha^{(2,0)}(u^{1,0}, v^{1,0}) = d\alpha(u^{1,0}, v^{1,0}) = u^{1,0} \cdot \alpha(v^{1,0}) - v^{1,0} \cdot \alpha(u^{1,0}) - \alpha([u^{1,0}, v^{1,0}])$$

The first two terms of the latter expression vanish, implying that  $d\alpha(u^{1,0}, v^{1,0}) = 8\alpha(N(u, v))$ .

Similarly, for  $\beta \in \Omega^{1,0}$ , we have  $\overline{N}^*\beta = (d\beta)^{(0,2)}$ . Note that, for f a function,  $df = \partial f + \overline{\partial} f$ , so

(3) 
$$ddf = d(\partial f) + d(\overline{\partial} f) = (\partial \partial f + \overline{\partial} \partial f + \overline{N}^* \partial f) + (N^* \overline{\partial} f + \partial \overline{\partial} f + \overline{\partial} \overline{\partial} f)$$

so  $\overline{\partial}^2 f = -\overline{N}^* \partial f$ . If f is holomorphic,  $\overline{\partial} f = 0 \implies \overline{\partial} \overline{\partial} f = 0 \implies \overline{N}^* \partial f = 0$ . Therefore, if there exist  $z_i : M \to \mathbb{C}$  holomorphic functions s.t.  $\partial z_i$  generate  $T^*M^{1,0}$ , then N = 0 and  $\overline{\partial}^2 = 0$ .

**Theorem 2** (Newlander-Nirenberg). J is integrable  $\Leftrightarrow N \equiv 0 \Leftrightarrow [T^{1,0}, T^{1,0}] \subset T^{1,0} \Leftrightarrow d = \partial + \overline{\partial} \Leftrightarrow \overline{\partial}^2 = 0$  on forms.

Finally, we return to the case of M a symplectic manifold with compatible a.c.s. J and induced metric g. Denote by  $\nabla$  the Levi-Civita connection given by g. In this case, J is integrable  $\Leftrightarrow \nabla(Jv) = J\nabla(v) \Leftrightarrow \nabla J = 0 \Leftrightarrow \nabla(T^{1,0}) \subset T^{1,0}$ .

**Definition 3.** A symplectic manifold  $(M, \omega, J)$  is Kähler if J is integrable and compatible with  $\omega$ . That is, (M, J) is a complex manifold,  $\omega$  is a closed, positive, real, nondegenerate (1, 1)-form (i.e.  $\omega(Ju, Ju) = \omega(u, v)$ ).

Example.  $(\mathbb{C}^n, \omega_0, i)$  is Kähler.

Example. Any Riemann surface (oriented with area form) is Kähler.

*Example.* The complex projective space  $\mathbb{C}P^n = \mathbb{C}^{n+1} \setminus \{0\}/(z_0,\ldots,z_n) \sim (\lambda z_0,\ldots,\lambda z_n)$  is Kähler. The points are given as homogeneous coordinates  $[z_0:\cdots:z_n]$ , with coordinate charts

(4) 
$$\mathbb{C}^n \cong U_i = \{ z_i \neq 0 \} = \{ [\frac{z_0}{z_i} : \dots : 1 : \dots : \frac{z_n}{z_i}] \}$$

and coordinate changes (WLOG on  $U_0 \cap U_1$ ) given by  $[1:z_1:\dots:z_n] \mapsto [\frac{1}{z_1}:1:\frac{z_2}{z_1}:\dots:\frac{z_n}{z_1}]$ . Note that  $\mathbb{C}P^1 = \mathbb{C} \cup \{\infty\} \cong S^2$ : more generally,

(5) 
$$\mathbb{C}P^n = \{[1:z_1:\dots z_n]\} \sqcup \{[0:z_1:\dots z_n]|z_i \neq 0 \text{ for some } i\} = \mathbb{C}^n \cup \mathbb{C}P^{n-1}$$

so we can construct the spaces inductively from cells in dimension  $2i, i \in \{0, \dots, n\}$ .

We claim that  $\mathbb{C}P^n$  has a symplectic structure compatible with the complex structure given above.

---

## SYMPLECTIC GEOMETRY, LECTURE 14

Prof. Denis Auroux

## 1. Kähler Geometry

Let  $(M, \omega, J)$  be a Kähler manifold, with  $\omega$  a symplectic form and J an integrable complex structure compatible with  $\omega$ .

- Compatibility  $\omega(Ju, Jv) = \omega(u, v)$ : note that, for a (2,0)-form  $\gamma = \sum a_{i,j} dz_i \wedge dz_j$ , we have  $\gamma(Ju, Jv) = -\gamma(u, v)$ , and similarly for a (0,2)-form. For a (1,1)-form  $\gamma = \sum a_{i,j} dz_i \wedge d\overline{z}_j$ , we have  $\gamma(Ju, Jv) = \gamma(u, v)$ , implying that  $\omega \in \Omega^{1,1}$ .
- Closedness  $d\omega = 0 \Leftrightarrow \partial \omega = 0, \overline{\partial} \omega = 0$ : in particular,  $[\omega] \in H^{1,1}_{\overline{\partial}}(M)$  lives in the Dolbeault cohomology of M. Moreover  $\omega$  is real (i.e.  $\overline{\omega} = \omega$ ). Writing  $\omega$  locally as  $\frac{i}{2} \sum_{j,k=1}^{n} h_{jk} dz_j \wedge d\overline{z}_k$ , so

(1) 
$$\overline{\omega} = \frac{i}{2} \sum_{j,k=1}^{n} \overline{h_{jk}} dz_k \wedge d\overline{z}_j$$

we have that  $h_{jk} = \overline{h_{kj}}$ , and  $(h_{jk})$  must be a Hermitian matrix.

• Nondegeneracy  $\omega^n \neq 0 \Leftrightarrow (h_{jk})$  is invertible, since

(2) 
$$\omega^n = \pm (\frac{i}{2})^n n! (\det(h_{jk})) dz_1 \wedge \dots \wedge dz_n \wedge d\overline{z}_1 \wedge \dots \wedge d\overline{z}_n$$

• Positivity  $\omega(v,Jv) > 0 \Leftrightarrow \text{positivity of } g(\cdot,\cdot) = \omega(\cdot,J\cdot) = \sum h_{jk}dz_jd\overline{z}_k \Leftrightarrow (h_{jk}) \text{ is a positive definite Hermitian matrix.}$ 

Thus, we find that, given a complex manifold (M, J),  $\omega$  is a Kähler form  $\Leftrightarrow \omega \in \Omega_{\mathbb{R}}^{1,1}, \overline{\partial}\omega = 0$ , and locally  $\omega = \frac{1}{2} \sum h_{jk} dz_j \wedge d\overline{z}_k$  for  $(h_{jk})$  a positive definite Hermitian matrix. Moreover, since these properties are preserved by convex linear combinations, any two Kähler forms for the same complex structure J are deformation equivalent and isotopic if  $[\omega]$  is fixed.

## 1.1. Kähler potential.

**Definition 1.** For M a complex manifold,  $\phi \in C^{\infty}(M,\mathbb{R})$  is strictly plurisubharmonic (spsh) if on each complex chart  $(U, z_j)$ , the matrix  $(\frac{\partial \phi}{\partial z_j \partial \overline{z}_k})$  is positive definite at every point.

Recall that J integrable,  $d^2 = 0 \implies \partial^2 = 0, \partial \overline{\partial} + \overline{\partial} \partial = 0, \overline{\partial}^2 = 0$ .

**Proposition 1.**  $\phi$  spsh  $\Leftrightarrow \frac{i}{2}\partial \overline{\partial} \phi$  is Kähler.

Example. On  $\mathbb{C}^n$ ,  $\phi = \sum |z_j|^2 = \sum z_j \overline{z_j}$  is strictly plurisubharmonic since  $(\frac{\partial \phi}{\partial z_j \partial \overline{z_k}})$  is the identity matrix, and the corresponding symplectic form  $\omega = \frac{i}{2} \sum dz_j \wedge d\overline{z_j}$  is the standard one.

We have the following converse.

**Theorem 1.** For  $\omega$  a closed, real-valued (1,1)-form on  $p \in M$ ,  $\exists$  a neighborhood  $U \ni p$ ,  $\phi \in C^{\infty}(U,\mathbb{R})$  s.t.  $\omega = \frac{i}{2}\partial \overline{\partial} \phi$ . This  $\phi$  is called a local Kähler potential for  $\omega$ .

## 1.2. Examples of Kähler Manifolds.

Example. Any complex submanifold of  $(\mathbb{C}^n, \omega)$  is Kähler, with the inherited complex and symplectic structures.

Example. Complex projective space  $\mathbb{CP}^n = \mathbb{C}^{n+1} \setminus \{0\}/\mathbb{C}^*$  is Kähler: letting

(3) 
$$U_i = \{(z_0 : \dots : z_{i-1} : 1 : z_{i+1} : \dots : z_n)\}$$

be the standard charts  $\cong \mathbb{C}^n$ , we have the Fubini-Study Kähler form

(4) 
$$\omega_{FS} = \frac{i}{2} \partial \overline{\partial} \log(1 + |z|^2)$$

(since  $f(z) = \log(1 + |z|)^2$  is spsh). Explicitly,

(5) 
$$\partial \overline{\partial} f = \partial \frac{\sum z_j d\overline{z}_j}{1 + |z|^2} = \frac{(1 + |z|^2) \sum dz_j \wedge d\overline{z}_j - (\sum \overline{z}_j dz_j) \wedge (\sum z_j d\overline{z}_j)}{(1 + |z|^2)^2}$$

Applying this to  $v \in T^{1,0}, \overline{v} \in T^{0,1}$ , we obtain

(6) 
$$\frac{(1+|z|^2)|v|^2-|\langle z,v\rangle|^2}{(1+|z|^2)^2} \ge \frac{|v|^2}{(1+|z|^2)^2}$$

Since  $\frac{i}{2}\partial\overline{\partial}f(u,iu) = \partial\overline{\partial}f(u^{1,0},\overline{u^{1,0}})$ , we have the desired positivity. Moreover, for  $\phi$  a transition map (WLOG between  $U_0$  and  $U_1$ ), we have that  $\phi^*f = \log(1+|z|^2) - \log|z_1|^2 \implies \partial\overline{\partial}(\phi^*f) = \partial\overline{\partial}f$  since

(7) 
$$\partial \overline{\partial} \log |z_1|^2 = \partial \frac{z_1 d\overline{z}_1}{|z_1|^2} = \partial \frac{d\overline{z}_1}{\overline{z}_1} = 0$$

Finally, recall that  $H^2(\mathbb{CP}^n, \mathbb{R}) = \mathbb{R}$ , and  $H_2(\mathbb{CP}^n)$  is generated by  $[\mathbb{CP}^1]$ . The class of  $[\omega]$  is thus defined by the value of

(8) 
$$[\omega] \cdot [\mathbb{CP}^1] = \int_{\mathbb{CP}^1} \omega_{FS} = \text{Area}(\mathbb{CP}^1, \omega_{FS})$$

*Example.* Any complex submanifold of  $\mathbb{CP}^n$  (i.e. complex projective variety) is Kähler.

**Theorem 2** (Kodaira Embedding). Let  $(X, \omega, J)$  be a compact Kähler manifold, with  $[\omega] \in H^2(X, \mathbb{R})$  an integral class. Then  $\exists$  a holomorphic embedding  $X \hookrightarrow \mathbb{CP}^n$  making it a complex projective variety, with  $\omega$  differing from  $\omega_{ES}$  by a scaling factor.

**Theorem 3** (Hodge). For  $(M, \omega)$  a compact Kähler manifold, the Dolbeault cohomology groups  $H^{p,q}_{\overline{\partial}}(M)$  satisfy  $H^k(M, \mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}_{\overline{\partial}}(M)$  and  $H^{p,q} \cong \overline{H^{q,p}}$ .

Corollary 1. dim  $H^k(M)$  is even for odd k.

Example. In the 70's, Kodaira and Thurston independently studied a closed 4-manifold which carries both a complex structure and a symplectic structure but which is not Kähler.

---

## SYMPLECTIC GEOMETRY, LECTURE 15

Prof. Denis Auroux

## 1. Hodge Theory

**Theorem 1** (Hodge). For M a compact Kähler manifold, the deRham and Dolbeault cohomologies are related by  $H^k_{dR}(M,\mathbb{C}) = \bigoplus_{p,q} H^{p,q}_{\overline{\partial}}(M)$ , with  $H^{p,q} \cong \overline{H^{q,p}}$ .

Before we discuss this theorem, we need to go over Hodge theory for a compact, oriented Riemannian manifold (M, g).

**Definition 1.** For V an oriented Euclidean vector space, the Hodge \* operator is the linear map  $\bigwedge^k V \to \bigwedge^{n-k} V$  which, for any oriented orthonormal basis  $e_1, \ldots, e_n$ , maps  $e_1 \wedge \cdots \wedge e_k \mapsto e_{k+1} \wedge \cdots \wedge e_n$ .

Example. For any V,  $*(1) = e_1 \wedge \cdots \wedge e_n$ , and  $** = (-1)^{k(n-k)}$ .

Applying this to  $T_x^*M$ , we obtain a map on forms.

Remark. Note that,

(1) 
$$\forall \alpha, \beta \in \Omega^k, \alpha \wedge *\beta = \langle \alpha, \beta \rangle. \text{vol}$$

**Definition 2.** The codifferential is the map

(2) 
$$d^* = (-1)^{n(k-1)+1} * d^* : \Omega^k(M) \to \Omega^{k-1}(M)$$

**Proposition 1.**  $d^*$  is the  $L^2$  formal adjoint to the deRham operator d, i.e. on a compact closed Riemannian manifold,  $\forall \alpha \in \Omega^k, \beta \in \Omega^{k+1}$ , we have

(3) 
$$\langle d\alpha, \beta \rangle_{L^2} = \int_M \langle d\alpha, \beta \rangle d\text{vol} = \langle \alpha, d^*\beta \rangle_{L^2}$$

*Proof.* This follows from

$$\int_{M} \langle d\alpha, \beta \rangle d\text{vol} = \int_{M} d\alpha \wedge *\beta = \int_{M} d(\alpha \wedge *\beta) - (-1)^{k} \int_{M} \alpha \wedge d * \beta$$

$$= (-1)^{k+1} \int_{M} \alpha \wedge d * \beta = (-1)^{k+1} \int_{M} \alpha \wedge *(*d * \beta)(-1)^{k(n-k)}$$

$$= (-1)^{kn+1} \int_{M} \langle \alpha, *d * \beta \rangle d\text{vol}$$

Example. For  $\mathbb{R}^n$  with the standard metric,

(5) 
$$\alpha = \sum_{I \subset \{1, \dots, n\}} \alpha_I dx_I \implies d\alpha = \sum_j dx_j \wedge \frac{\partial \alpha}{\partial x_j} \text{ and } d^*\alpha = -\sum_j i_{\frac{\partial}{\partial x_j}} \frac{\partial \alpha}{\partial x_j}$$

**Definition 3.** The Laplacian is  $\Delta = dd^* + d^*d : \Omega^k \to \Omega^k$ .

Note that, on  $\Omega^*(M) = \bigoplus_{k=0}^n \Omega^k(M)$ ,  $\Delta = (d+d^*)^2$ . By the adjointness of d and  $d^*$ , we see that  $\Delta$  is a self-adjoint, second order differential operator, i.e.  $\langle \Delta \alpha, \beta \rangle_{L^2} = \langle \alpha, \Delta \beta \rangle_{L^2}$ . Moreover,

(6) 
$$\langle \Delta \alpha, \alpha \rangle_{L^2} = \langle dd^* \alpha, \alpha \rangle_{L^2} + \langle d^* d\alpha, \alpha \rangle_{L^2} = ||d^* \alpha||^2 + ||d\alpha||^2 \ge 0$$

so  $\Delta \alpha = 0 \Leftrightarrow \alpha$  is closed and co-closed.


**Definition 4.** The space of harmonic forms is the set  $\mathcal{H}^k = \{\alpha \in \Omega^k | \Delta \alpha = 0\}$ .

We have a natural map  $\mathcal{H}^k \to H^k, \alpha \mapsto [\alpha]$ .

**Theorem 2** (Hodge). For M a compact, oriented Riemannian manifold, every cohomology class has a unique harmonic representative, i.e.  $\mathcal{H}^k \cong H^k$ , and  $\Omega^k(M) = \mathcal{H}^k \oplus_{L^2} d(\Omega^{k-1}) \oplus_{L^2} d^*(\Omega^{k+1})$ .

Remark. Clearly  $\mathcal{H}^k + d(\Omega^{k-1}) \subset \text{Ker } d = (\text{Im } d^*)^{\perp}$  and  $\mathcal{H}^k + d^*(\Omega^{k+1}) \subset \text{Ker } d^* = (\text{Im } d)^{\perp}$ , implying that the map  $\mathcal{H}^k \to H^k$  is injective. Surjectivity (i.e. existence of harmonic representatives) is more difficult and requires elliptic theory.

**Definition 5.** A differential operator of order k is a linear map  $L: \Gamma(E) \to \Gamma(F)$  s.t., locally in coordinates,

(7) 
$$L(s) = \sum_{|\alpha| \le k} A_{\alpha} \frac{\partial^{|\alpha|} s}{\partial x^{\alpha}}$$

where each  $A_{\alpha}$  is a  $C^{\infty}$  function with values in matrices, i.e. a local section of Hom(E,F). The symbol of L is the map

(8) 
$$\sigma_k: T_x^* M \ni \xi \mapsto \sum_{|\alpha|=k} A_{\alpha}(x) \xi_1^{\alpha_1} \cdots \xi_n^{\alpha_n} \in \text{Hom}(E_x, F_x)$$

L is elliptic if for every nonzero  $\xi$ ,  $\sigma(\xi)$  is an isomorphism.

*Example.* For instance, in local coordinates, the symbol of the Laplacian is given by  $\sigma(\xi) = -|\sigma|^2 \cdot id$ .

Now, let L be a differential operator of order k: it extends from  $L: C^{\infty}(E) \to C^{\infty}(F)$  to  $L_s: W^s(E) \to W^{s-k}(F)$ .

**Definition 6.** For  $L: \Gamma(E) \to \Gamma(F)$  a differential operator,  $P: \Gamma(F) \to \Gamma(E)$  is called a parametrix (or pseudoinverse) if  $L \circ P - \mathrm{id}_E$  and  $P \circ L - \mathrm{id}_F$  are smoothing operators, i.e. they extend continuously to  $W^s(E) \to W^{s+1}(E)$ .

Using Rellich's lemma on embedding of Sobolev spaces, we find that

**Theorem 3.** Every elliptic operator has a pseudoinverse.

Corollary 1.  $\xi \in W^s(E)$ , L is elliptic, and  $L\xi \in C^{\infty}(F) \implies \xi \in C^{\infty}(E)$ .

*Proof.* Let P be a parametrix. Let  $S = P \circ L - I$ , so

$$\xi = P \circ L\xi - S\xi$$

Since the former part lies in  $C^{\infty}(E)$  and the latter in  $W^{s+1}(E)$ , we have that  $\xi \in W^{s+1}(E)$ . Iterating,  $\xi \in C^{\infty}(E)$ .

---

## SYMPLECTIC GEOMETRY, LECTURE 16

## Prof. Denis Auroux

Recall that we were in the midst of elliptic operator analysis of the Laplace-deRham operator  $\Delta = (d+d^*)^2$ . We claimed that  $\Delta$  was an elliptic operator, i.e. it has an invertible symbol  $\sigma(\xi) = -|\xi|^2$  id. We stated that a differential operator  $L: C^{\infty}(E) \to C^{\infty}(F)$  of order k extends to a map  $L_s: W^s(E) \to W^{s-k}(F)$ .

**Definition 1.** For  $L: \Gamma(E) \to \Gamma(F)$  a differential operator,  $P: \Gamma(F) \to \Gamma(E)$  is called a parametrix (or pseudoinverse) if  $L \circ P - \mathrm{id}_E$  and  $P \circ L - \mathrm{id}_F$  are smoothing operators, i.e. they extend continuously to  $W^s(E) \to W^{s+1}(E)$ .

The following results can be found in Wells' book.

**Theorem 1.** Every elliptic operator has a pseudoinverse.

Corollary 1.  $\xi \in W^s(E)$ , L elliptic,  $L\xi \in C^{\infty}(F) \implies \xi C^{\infty}(E)$ .

**Theorem 2.** L elliptic  $\Longrightarrow L_s$  is Fredholm, i.e. Ker  $L_s$ , Coker  $L_s$  are finite dimensional, Im  $L_s$  is closed, and Ker  $L_s = \text{Ker } L \subset C^{\infty}(E)$ .

**Theorem 3.** L elliptic,  $\tau \in (\text{Ker } L^*)^{\perp} = \text{Im } L \subset C^{\infty}(F) \implies \exists ! \xi \in C^{\infty}(E) \text{ s.t. } L\xi = \tau \text{ and } \xi \perp \text{Ker } L.$ 

**Theorem 4.** L elliptic, self-adjoint  $\implies \exists H_L, G_L : C^{\infty}(E) \to C^{\infty}(E)$  s.t.

- (1)  $H_L \ maps \ C^{\infty}(E) \to \operatorname{Ker} (L),$
- (2)  $L \circ G_L = G_L \circ L = \mathrm{id} H_L$ ,
- (3)  $G_L, H_L$  extend to bounded operators  $W^s \to W^s$ , and
- (4)  $C^{\infty}(E) = \operatorname{Ker} L \oplus_{\perp L^2} \operatorname{Im} (L \circ G_L).$

We now return to the case of  $\Delta = (d + d^*)^2$  on a compact manifold.

Corollary 2.  $\exists G: \Omega^k \to \Omega^k \text{ and } H: \Omega^k \to \mathcal{H}^k = \text{Ker } \Delta \text{ s.t. } G\Delta = \Delta G = \text{id} - H \text{ and } \text{Im } (G\Delta) = (\mathcal{H}^k)^{\perp}.$ 

Corollary 3.  $\Omega^k = \mathcal{H}^k \oplus_{\perp L^2} \operatorname{Im} d \oplus_{\perp L^2} \operatorname{Im} d^*$ .

Remark. Every  $\alpha \in \Omega^k$  decomposes as  $\alpha = H\alpha + d(d^*G\alpha) + d^*(dG\alpha)$ .

Using this decomposition, we immediately obtain the theorem

**Theorem 5** (Hodge). For M a compact, oriented Riemannian manifold, every cohomology class has a unique harmonic representative.

From now on, M is a compact, Kähler manifold, with the Hodge \* operator on  $\Omega^*(M)$  extended  $\mathbb{C}$ -linearly to  $\mathbb{C}$ -valued forms.

**Proposition 1.** \* maps  $\bigwedge^{p,q} \to \bigwedge^{n-q,n-p}$ .

*Proof.* Consider the standard orthonormal basis of  $V = T_x^*M$  given by  $\{x_1, y_1, \dots, x_n, y_n\}$  with  $Jx_j = y_j$  and  $z_j = x_j + iy_j$  giving the basis for  $\bigwedge^{1,0}$ . Now, write any form  $\alpha$  as a linear combination of

(1) 
$$\alpha_{A,B,C} = \prod_{j \in A} z_j \wedge \prod_{j \in B} \overline{z_j} \wedge \prod_{j \in C} z_j \wedge \overline{z_j}$$

where  $A, B, C \subset \{1, ..., n\}$  are disjoint subsets. That is, A is the set of indices which contribute purely holomorphic terms of  $\alpha$ , B is the set of indices which contribute purely anti-holomorphic terms to  $\alpha$ , and C is the set of indices which contribute both. One can show that

(2) 
$$*(\alpha_{A,B,C}) = i^{a-b}(-1)^{\frac{1}{2}k(k+1)+c}(-2i)^{k-n}\alpha_{A,B,C'}$$

where  $C' = \{1, ..., n\} \setminus (A \cup B \cup C), a = |A|, b = |B|, c = |C|, \text{ and } k = \deg \alpha = a + b + 2c.$  By this, (p,q) = (a+c,b+c)-forms map to (a+(n-a-b-c),b+(n-a-b-c)) = (n-q,n-p)-forms as desired.  $\Box$ 

Let  $L: \Omega^{p,q} \to \Omega^{p+1,q+1}$  be the map  $\alpha \mapsto \omega \wedge \alpha, L^*: \Omega^{p,q} \to \Omega^{p-1,q-1}$  the adjoint map  $\alpha \mapsto (-1)^{p+q} * L^*$ . Furthermore, set  $d_C = J^{-1}dJ = (-1)^{k+1}JdJ$ , with adjoint  $d_C^* = J^{-1}d^*J = (-1)^{k+1}Jd^*J$ . On functions, we have that

(3) 
$$d_c f = -Jdf = -J(\partial f + \overline{\partial} f) = -i\partial f + i\overline{\partial} f = -i(\partial - \overline{\partial})f$$

which extends to higher forms as well. Thus,  $dd_C = -i(\partial + \overline{\partial})(\partial - \overline{\partial}) = 2i\partial \overline{\partial}$ .

**Lemma 1.** For X Kähler, [L, d] = 0,  $[L^*, d^*] = 0$ ,  $[L, d^*] = d_C$ ,  $[L^*, d] = -d_C^*$ .

*Proof.* The first part follows from  $d(\alpha \wedge \omega) = d\alpha \wedge \omega$ . For the second, see Wells, theorem 4.8.

Proposition 2.  $\Delta_C = J^{-1}\Delta J = d_C d_C^* + d_C^* d_C = \Delta$ 

*Proof.* By J-invariance of  $\omega$ , we have that  $[L,J]=[L^*,J]=0$ . Using the above identities, we have that  $[L^*,d_C]=d^*$ , so

(4) 
$$\Delta = dd^* + d^*d = d[L^*, d_C] + [L^*, d_C]d = dL^*d_C - dd_CL^* + L^*d_Cd - d_CL^*d$$

Conjugating by J simply swaps terms, since  $dd_C = -d_C d$ .

Let

(5) 
$$\overline{\partial^*} = - * \partial * : \Omega^{p,q} \to \Omega^{p,q-1}$$
$$\partial^* = - * \overline{\partial} * : \Omega^{p,q} \to \Omega^{p-1,q}$$

so  $d^* = \partial^* + \overline{\partial}^*$ .

**Lemma 2.**  $\overline{\partial^*}$  is  $L^2$ -adjoint to  $\overline{\partial}$ , and  $\partial^*$  is  $L^2$ -adjoint to  $\partial$ .

For  $\phi, \psi \in \Omega^k(M, \mathbb{C})$ , we have the natural scalar product

$$\langle \phi, \psi \rangle_{L^2} = \int_M \phi \wedge *\overline{\psi}$$

Under this, the various  $\Omega^{p,q}$  are orthogonal because if  $\phi \in \Omega^{p,q}$ ,  $\psi \in \Omega^{p',q'}$ ,  $(p,q) \neq (p',q')$ , then  $\phi \wedge *\overline{\psi}$  is of type

$$(7) (n + (p - p'), n + (q - q')) \neq (n, n)$$

Finally, define the operators

(8) 
$$\Box = \partial \partial^* + \partial^* \partial, \overline{\Box} = \overline{\partial \partial^*} + \overline{\partial^* \partial} : \Omega^{p,q} \to \Omega^{p,q}$$

**Theorem 6.** For M compact, Kähler,

(9) 
$$H^{p,q}_{\overline{\partial}}(M) = \mathcal{H}^{p,q}_{\overline{\square}} = \operatorname{Ker} \overline{\square}$$

The proof that each  $\bar{\partial}$ -cohomology class contains a unique  $\bar{\Box}$ -harmonic form is similar to that of the Hodge theorem in the Riemannian case.

Theorem 7.  $\Delta = 2\Box = 2\overline{\Box}$ .

*Proof.* By the first lemma,  $d^*d_c = d^*[L, d^*] = d^*Ld^* = -[L, d^*]d^* = -d_Cd^*$ . Moreover,  $d_c = -i(\partial - \overline{\partial})$ , so  $\overline{\partial} = \frac{1}{2}(d - \mathrm{id}_c)$  and  $\overline{\partial}^* = \frac{1}{2}(d^* + id_c^*)$ . Thus,

(10) 
$$4\overline{\square} = (d - \mathrm{id}_c)(d^* + \mathrm{id}_c^*) + (d^* + \mathrm{id}_c^*)(d - \mathrm{id}_c)$$
$$= (dd^* + d^*d) + (d_cd_c^* + d_c^*d_c) + i(dd_c^* + d_c^*d) - i(d_cd^* + d^*d_c)$$
$$= \Delta + \Delta_c + 0 + 0 = 2\Delta$$

Corollary 4.  $\Delta$  maps  $\Omega^{p,q}$  to itself and

(11) 
$$H_{dR}^{k}(M,\mathbb{C}) = \mathcal{H}_{\Delta}^{k} = \bigoplus_{p+q=k} \mathcal{H}^{p,q} = \bigoplus_{p,q} H_{\overline{\partial}}^{p,q}(M)$$

---

## SYMPLECTIC GEOMETRY, LECTURE 17

## Prof. Denis Auroux

The Hodge decomposition stated last time places strong constraints on  $H^*$  of Kähler manifolds, e.g. dim  $H^k$  is even for k odd because  $\mathbb{C}$  conjugation gives isomorphisms  $\overline{\mathcal{H}^{p,q}} \cong \mathcal{H}^{q,p}$  (note that this is false for symplectic manifolds in general). The Hodge star \* gives isomorphisms  $\mathcal{H}^{p,q} \xrightarrow{\sim} \mathcal{H}^{n-q,n-p}$  and the Hodge diamond structure on the the ranks of the Dolbeault cohomology groups, i.e.

(1) 
$$\begin{array}{ccccccccccccccccccccccccccccccccccc$$

is symmetric across the two diagonal axes. Moreover, note that  $[\omega^{\wedge p}] \in \mathcal{H}^{p,p}$  is nonzero, since  $[\omega^{\wedge n}]$  is the volume class.

We have even stronger constraints, namely the "hard Lefschetz theorem".

**Theorem 1.** 
$$L^{n-k} = (\cdot \wedge \omega^{n-k}) : H^k(X,\mathbb{R}) \to H^{2n-k}(X,\mathbb{R})$$
 is an isomorphism.

This is false for many symplectic manifolds. Moreover, combining this with Poincaré duality gives that, for  $k \leq n, \ H^k \times H^k \to \mathbb{R}, \ \alpha, \beta \mapsto \int \alpha \cup \beta \cup \omega^{n-k}$  is a nondegenerate bilinear pairing (skew-symmetric if k is odd). We also have the *Kodaira embedding theorem*:

**Theorem 2.** For  $(X, \omega)$  a compact Kähler manifold,  $[\omega] \in H^2(X, \mathbb{Z})$ ,  $\exists$  a projective embedding  $X \to \mathbb{CP}^N$  realizing X as a projective algebraic variety.

We will see a symplectic geometry proof due to Donaldson.

## 1. Holomorphic vector bundles

Let (M,J) be a complex manifold,  $E \to M$  a complex vector bundle. Then we can cover M by  $U_{\alpha}$  s.t. the restrictions  $U_{\alpha} \times \mathbb{C}^n \cong E|_{U_{\alpha}} \to U_{\alpha}$  are trivial.

**Definition 1.** E is a holomorphic vector bundle if the transition functions  $\phi_{\alpha,\beta}: U_{\alpha} \cap U_{\beta} \to \mathrm{GL}(r,\mathbb{C})$  are holomorphic.

Note that this only makes sense on a complex manifold. Now,  $\exists$  a natural  $\overline{\partial}$  operator on sections given in a local trivialization by  $\overline{\partial}$  (given a section s which looks like  $\xi_{\alpha}$  in the local trivialization  $\alpha$ , on an intersection we have that  $\overline{\partial}\xi_{\alpha} = \phi_{\alpha,\beta}\overline{\partial}\xi_{\beta}$  since  $\overline{\partial}\phi_{\alpha,\beta} = 0$ ). This extends to  $\overline{\partial}: \Omega^{p,q}(E) \to \Omega^{p,q+1}(E)$  similarly.

$$\textbf{Definition 2.} \ \ H^q_{\overline{\partial}}(E) = \frac{\operatorname{Ker} \ (\overline{\partial}: \Omega^{0,q}(E) \to \Omega^{0,q+1}(E))}{\operatorname{Im}(\overline{\partial}: \Omega^{0,q-1}(E) \to \Omega^{0,q}(E))}. \ \ In \ \ particular, \ H^0(E) \ \ is \ the \ space \ of \ holomorphic \ sections.$$

Specifying the holomorphic structure on a complex vector bundle E is equivalent to specifying a  $\overline{\partial}$  operator with  $\overline{\partial}^2 = 0$ . The  $\overline{\partial}$  operator is half of a connection: in fact,  $\nabla$  a connection on E decomposes into  $\nabla = \nabla^{1,0} + \nabla^{0,1}$ .

**Proposition 1.** For  $(E, \overline{\partial}, |\cdot|)$  a holomorphic bundle with a Hermitian metric,  $\exists !$  Hermitian connection s.t.  $\nabla^{0,1} = \overline{\partial}$ .

Proof. We work in local coordinates on M, and local trivializations of E by orthonormal sections  $\sigma_j$  (but not necessarily holomorphic trivializations;  $\overline{\partial}\sigma_j$  may be nonzero).  $\nabla = d + A$  for  $A = (a_{ij})$  a matrix-valued 1-form  $(a_{ij} = \langle \nabla \sigma_j, \sigma_i \rangle)$ .  $\nabla$  is Hermitian iff  $a_{ij} = -\overline{a_{ij}}$ , i.e. A is antihermitian, and  $\nabla$  is holomorphic, i.e.  $\nabla^{0,1}s = \overline{\partial}s$  iff  $A^{0,1}$  is given by  $a_{ij}^{0,1} = \langle \overline{\partial}\sigma_j, \sigma_i \rangle$ . Then  $A^* = -A \Leftrightarrow A^{1,0} = -(A^{0,1})^*$ , i.e.  $a_{ij}^{1,0} = -\overline{a_{ij}^{0,1}}$ .

Equivalently, in a holomorphic trivialization, when  $\overline{\partial}$  is the usual  $\overline{\partial}$  operator,  $\langle \cdot, \cdot \rangle$  given by  $h = C^{\infty}$  function with values in positive definite Hermitian matrices,  $\nabla = d + A$  again and  $\nabla$  is Hermitian  $\Leftrightarrow d\langle s, s' \rangle = \langle \nabla s, s' \rangle + \langle s, \nabla s' \rangle \Leftrightarrow d(s^*hs') = (ds^* + s^*A^*)hs' + s^*h(ds' + As') \Leftrightarrow dh = A^*h + hA$ . On the other hand, now  $\nabla^{0,1} = \overline{\partial} \Leftrightarrow A^{0,1} = 0$ . Hence  $dh = A^*h + hA \Leftrightarrow A = h^{-1}\partial h$  (and  $A^* = \overline{\partial}h \cdot h^{-1}$ ).

**Proposition 2.** In a holomorphic frame, the connection 1-form A is of type (1,0), and  $\partial A = -A \wedge A$ ,  $R^{\nabla} = \overline{\partial} A$  is of type (1,1), and  $\overline{\partial} R = 0$  and  $\partial R = [R,A]$ .

In fact, we have

**Theorem 3.**  $(E, \nabla^{0,1} = \overline{\partial}^{\nabla})$  is holomorphic  $\Leftrightarrow (\overline{\partial}^{\nabla})^2 = 0 \Leftrightarrow R^{0,2} = 0$ .

*Proof.* First,  $A = h^{-1}\partial h$  has type (1,0) by the above, and

(2) 
$$\partial A = \partial (h^{-1}) \wedge \partial h = (-h^{-1}(\partial h)h^{-1}) \wedge \partial h = -(h^{-1}\partial h) \wedge (h^{-1}\partial h) = -A \wedge A$$

by the formula for derivatives of inverses in a noncommutative setting. Second,  $R^{\nabla} = dA + A \wedge A = dA - \partial A = \overline{\partial} A$ , hence it has type (1, 1). Finally,  $\overline{\partial} R = \overline{\partial} \overline{\partial} A = 0$ ,  $\partial R = \partial \overline{\partial} A = -\overline{\partial} \partial A = \overline{\partial} A \wedge A - A \wedge \overline{\partial} A = [R, A]$ .

---

## SYMPLECTIC GEOMETRY, LECTURE 18

Prof. Denis Auroux

Let  $(M, \omega, J)$  be a compact Kähler manifold,  $[\omega] \in H^{1,1}(M) \cap H^2(M, \mathbb{Z})$ . Then we can find a line bundle  $L \to M$  with first Chern class  $c_1(L) = [\omega]$ . Choose a Hermitian metric on L along with a Hermitian connection  $\nabla$  with  $R^{\nabla} = -2\pi i\omega$ . More explicitly, starting with any hermitian connection  $\nabla$ ,  $R^{\nabla}$  is a closed imaginary 2-form: in a trivialization,  $\nabla = d + A$ , so  $R^{\nabla} = dA + [A, A] = dA$ . Thus,

(1) 
$$[R^{\nabla}] = -2\pi i c_1(L) = -2\pi i [\omega] \implies \exists a \in \Omega^1(M) \text{ s.t. } R^{\nabla} = -2\pi i \omega + i da$$

Letting  $\nabla' = \nabla - ia$ , we find that  $R' = R - ida = -2\pi i\omega$ .

Next, recall that  $\nabla^{0,1}$  defines a holomorphic structure on L iff  $(R^{\nabla})^{0,2}=0$ . Since  $\omega$  is a (1,1)-form and  $R^{\nabla}=-2\pi i\omega$ , we get a holomorphic line bundle structure for L. We will furthermore see that  $L^{\otimes k}$  has "enough holomorphic sections", i.e. the number of such sections  $\to \infty$ . Given this, consider a basis of holomorphic sections  $s_0,\ldots,s_N\in H^0(L)$  (or  $H^0(L^{\otimes k})$ ). Assume that,  $\forall p\in M, \exists s\in H^0(L)$  s.t.  $s(p)\neq 0$ . Then we can define a map

$$(2) f: M \to \mathbb{CP}^n, p \to [s_0(x): \dots : s_N(x)]$$

More intrinsically, we obtain a map

(3) 
$$M \to \mathbb{P}(H^0(L)^*), p \mapsto H_p = \{s \in H^0(L) | s(p) = 0\} \subset H^0(L)$$

Here,  $H_p$  is the kernel of the linear form given by evaluation at p, well-defined up to scaling.

**Definition 1.** L is very ample if  $f: M \to \mathbb{P}(H^0(L)^*)$  is a well-defined embedding, and ample if  $L^{\otimes k}$  is very ample for some k.

We can reformulate this using the Kodaira embedding theorem:

**Theorem 1** (Kodaira). A holomorphic line bundle is ample  $\Leftrightarrow$  it has a holomorphic connection whose curvature is a Kähler form.

The traditional proof of the Kodaira embedding theorem requires the Kodaira vanishing theorem. Instead, we will prove this using Donaldson's argument. For simplicity, replace  $\omega$  by  $\frac{\omega}{2\pi}$ , so  $\left[\frac{\omega}{2\pi}\right] = c_1(L)$ . We will explicitly construct holomorphic sections of  $L^{\otimes k}$  for all k >> 0.

- First, fix  $p \in M$ , and choose local Darboux coordinates s.t.  $\omega = \frac{i}{2} \sum dz_j \wedge d\overline{z_j}$  and  $J = J_0 + \mathcal{O}(|z|)$  (we can't assume that J is the natural complex structure, because that would imply the Kähler metric was flat).
- Next, choose a unitary trivialization of  $L^{\otimes k}$ , so that  $\nabla$  corresponds to

(4) 
$$d + iA_0 = d + \frac{k}{4} \sum z_j d\overline{z_j} - \overline{z_j} dz_j$$

To see that we can choose A in this way, note that, in any trivialization,  $\nabla = d + iA$ , so  $-ik\omega = R = idA$ . We have

$$idA_0 = \frac{k}{4} \sum dz_j \wedge d\overline{z_j} = -ik\omega_0 = idA$$

Thus,  $A-A_0$  is closed and locally exact. Moreover, changing the trivialization by  $f=e^{i\phi}\in C^\infty(U,U(1))$  changes the connection 1-form to  $A'=A+d\phi$ . Thus a suitable change of trivialization ensures that the connection form becomes  $iA_0$ .

Remark. Baby model: assume  $J = J_0$  in our coordinates (so that the Kähler metric is flat), and consider  $s(z) = \exp(-\frac{k}{4}|z|^2)$ : this function arises from considering the curvature

(6) 
$$R^{1,1} = \partial^{\nabla} \overline{\partial}^{\nabla} + \overline{\partial}^{\nabla} \partial^{\nabla} = \overline{\partial} \partial \log |\sigma|^2$$

for  $\sigma$  a holomorphic section. We claim that s is holomorphic w.r.t.  $\nabla$ . To see this, note that

(7) 
$$\nabla s = ds + iA_0 s = \left(-\frac{k}{4} \sum z_j d\overline{z_j} + \overline{z_j} dz_j\right) s + \left(\frac{k}{4} \sum z_j d\overline{z_j} - \overline{z_j} dz_j\right) s = \frac{-k}{2} \left(\sum \overline{z_j} dz_j\right) s$$
 so  $\overline{\partial}^{\nabla} s = 0$  as desired.

• In our case,

(8) 
$$J = J_0 + \mathcal{O}(|z|) \implies \left| \nabla s^{0,1} \right| = \mathcal{O}(|z| \cdot |\nabla s|) = \mathcal{O}(k |z|^2 \cdot |s|)$$

while

(9) 
$$|\nabla s| = \mathcal{O}(k|z||s|) \implies \frac{\sup |\nabla s^{0,1}|}{\sup |\nabla s|} = \mathcal{O}(\frac{1}{\sqrt{k}})$$

We say that s is "approximately holomorphic".

**Definition 2.** A family of sections  $s_k \in C^{\infty}(L^{\otimes k})$  is uniformly bounded if it satisfies the uniform bounds

(10) 
$$\sup_{x \in M} |\nabla^r s_k|_g \le C_r k^{\frac{r}{2}}$$

and approximately holomorphic if

(11) 
$$\sup_{r \in M} \left| \nabla^{r-1} \overline{\partial} s_k \right|_g \le C_r k^{\frac{r-1}{2}}$$

for all r. Furthermore,  $s_k$  is uniformly concentrated at p if  $\exists$  a polynomial P and a constant  $\lambda > 0$  s.t.

(12) 
$$\forall x \in M, \left| \frac{1}{k^{t/2}} \nabla^t s(x) \right| \le P(\sqrt{k} d(p, x)) \exp(-\lambda k \operatorname{dist}(p, x)^2)$$

for  $t \in \{0, ..., r\}$ .

**Proposition 1.** If  $(M, \omega)$  is a compact symplectic manifold with a compatible almost complex structure, then  $\exists$  a family of sections  $(\sigma_{k,p})_{k>>0,p\in M}$  which are uniformly bounded, approximately holomorphic, uniformly concentrated, and  $|\sigma_{k,p}| \geq c > 0$  over  $B(p, \frac{1}{\sqrt{k}})$ .

In the Kähler case, we also have the following approximation theorem.

**Proposition 2.** Given a family of sections  $\{\sigma_{k,n}\}$  as above,  $\exists \{\tilde{\sigma}_{k,n}\}$  holomorphic s.t.

(13) 
$$\sup(k^{r/2} |\nabla^r \sigma_{k,p} - \nabla^r \tilde{\sigma}_{k,p}|) \le Ce^{-\lambda k/3}$$

That is, any estimate you make via  $\sigma$  can also be applied to  $\tilde{\sigma}$ , so you can assume that your approximately holomorphic sections are holomorphic and obtain the desired embedding. To use these sections to prove Kodaira embedding, note that  $\forall p \in M, \exists s \in H^0(L^{\otimes k})$  s.t.  $s(p) \neq 0$  since  $|\tilde{\sigma}_{k,p}(p)| \approx 1$  (that is,  $L^{\otimes k}$  is base point free). Moreover, given  $p \neq q \in M, \exists s, s' \in H^0(L^{\otimes k})$  s.t. |s(p)| > |s(q)| and |s'(p)| < |s'(q)|: e.g., if p, q are distant by more than  $k^{-\frac{1}{2}}$  we can take  $s = \tilde{\sigma}_{k,p}$  and  $s' = \tilde{\sigma}_{k,q}$  (that is, our sections separate points). Finally, at every point  $p, \forall v \in T_pM, \exists \sigma_1, \sigma_2 \in H^0(L^{\otimes k})$  s.t.  $d_v(\frac{\sigma_1}{\sigma_2}) \neq 0$  (that is, our sections separate tangent vectors). This is done by choosing a local holomorphic coordinate so that  $v = \operatorname{Re} \frac{\partial}{\partial z_1}$  and perturbing  $z_1 \sigma_{k,p}$  to a holomorphic section; setting  $\sigma_2 = \tilde{\sigma}_{k,p}$  gives the desired nonzero derivative.

---

## SYMPLECTIC GEOMETRY, LECTURE 19

## Prof. Denis Auroux

We now return to the complex Kähler case. Let  $(M, \omega, J)$  be a complex Kähler manifold.

**Proposition 1** (Donaldson).  $\exists$  a family of sections  $(\sigma_{k,p})_{k>k_0,p\in M}$  which is uniformly bounded and almost-holomorphic, uniformly concentrated, and satisfies  $|\sigma_{k,p}| \geq c > 0$  on  $B(p,k^{-1/2})$ . Furthermore,  $\exists$  a family of holomorphic sections  $(\tilde{\sigma}_{k,p})$  with  $\sup |\sigma_{k,p} - \tilde{\sigma}_{k,p}|$ ,  $\sup (k^{1/2} |\nabla \sigma_{k,p} - \nabla \tilde{\sigma}_{k,p}|) \leq O(\exp(-\lambda k^{1/3}))$ . That is, the  $\tilde{\sigma}_{k,p}$  are so close to  $\sigma_{k,p}$  that they're interchangeable in practice.

*Proof.* Fix  $p \in M$  and holomorphic coordinates  $(M, p) \to (\mathbb{C}^n, 0)$  (not necessarily Darboux). We can choose the coordinates to be isometric at the origin.

(1) Let u be a local section of L near p which is holomorphic and s.t. |u(x)| = 1 (e.g.  $u \equiv 1$  in a holomorphic trivialization). Then

(1) 
$$\overline{\partial}\partial \log |u|^2 = \overline{\partial}(u^{-1}\partial^{\nabla}u) = u^{-1}\overline{\partial}^{\nabla}\partial^{\nabla}u = R^{1,1} = -i\omega$$

with the third equality coming from  $(R^{\nabla})^{1,1} = \overline{\partial}^{\nabla} \partial^{\nabla} + \partial^{\nabla} \overline{\partial}^{\nabla} = (R^{\nabla})^{1,1}$  and  $\overline{\partial}^{\nabla} u = 0$ . In local coordinates, we can write

(2) 
$$\log|u|^2 = \sum_{j} (f_j z_j + \overline{f}_j \overline{z}_j) + \sum_{ij} (g_{ij} z_i \overline{z}_j + h_{ij} z_i z_j + \overline{h}_{jk} \overline{z}_i \overline{z}_j) + O(|z|^3)$$

Replacing u by  $\exp(\sum -f_jz_j - \sum h_{ij}z_iz_j)u$  (which preserves holomorphicity), we can assume  $\log |u|^2 = \sum g_{ij}z_i\overline{z_j} + O(|z|^3)$ .  $\overline{\partial}\partial \log |u|^2 = -i\omega \implies (g_{ij}) = -\frac{1}{2} (\text{metric tensor on } T_x M) \implies \log |u|^2 = -\frac{1}{2} |z|^2 + O(|z|^3)$ . Hence  $u^k$  is a local holomorphic section of  $L^{\otimes k}$ ,  $|u^k| = \exp(-\frac{k}{4}|z|^2 + kO(|z|^3))$ . Estimating the growth of derivatives of  $\log |u|^2$  gives us uniform concentratedness estimates as long as |z| << 1 (which is fine since the "support" of  $u^k \sim$  a ball of radius  $\frac{1}{\sqrt{k}}$ ). Then let  $\sigma_{k,p}(q) = \chi_k(\operatorname{dist}(p,q))u(q)^k$ , where  $\chi_k$  is a smooth cut-off function at distance  $\sim k^{-1/3}$  (i.e.  $\chi_k \equiv 1$  inside the ball of radius  $k^{-1/3}$  and 0 outside a larger ball).

Note that the cutoff occurs in the region where  $|z| \sim k^{-1/3}$  i.e.  $|u^k| \sim \exp(-k\frac{|z|^2}{4}) \sim \exp(-k^{1/3})$ . Thus we get  $\sup |\overline{\partial}\sigma_{k,p}| = \sup |u^k\overline{\partial}(\chi_k)| \leq O(\exp(-\lambda k^{1/3}))$  since  $\overline{\partial}\chi_k \equiv 0$  except for  $|z| \sim k^{-1/3}$  and  $|\overline{\partial}\chi_k| \leq k^{1/3}$ .

(2) To obtain the  $\tilde{\sigma}_{k,p}$ , we use the following lemma:

**Lemma 1.**  $\forall s \in \Gamma(L^{\otimes k}), \exists \xi \in \Gamma(L^{\otimes k}) \text{ s.t. } ||\xi||_{L^2} \leq \frac{c}{\sqrt{k}} \left|\left|\overline{\partial} s\right|\right|_{L^2} \text{ and } s + \xi \text{ is holomorphic.}$ 

We apply this lemma to  $\sigma_{k,p}$  and obtain  $||\xi||_{L^2} \leq \frac{c}{\sqrt{k}} \left| \left| \overline{\partial} \sigma_{k,p} \right| \right|_{L^2} \leq O(k^{-2n/3-1/2} \exp(-\lambda k^{-1/3}))$ , where the  $L^2$  estimate on  $\overline{\partial} \sigma_{k,p}$  follows from the pointwise bound and the observation that it is supported in a ball of volume  $\sim k^{-2n/3}$ . To get a pointwise  $C^r$ -estimate on  $\xi$ , we use a Cauchy estimate expressing values of holomorphic functions at q by integrals over balls containing q. At points inside  $B(p, k^{-1/3})$ ,  $\chi = 1$  so  $\sigma_{k,p}$  is holomorphic there, as is  $\xi$ , and  $||\xi||_{C^r}$  is controlled by  $||\xi||_{L^2} \sim \exp(-\lambda k^{1/3})$  on  $B(k^{-1/3})$ . Finally, the Cauchy estimates for  $\sigma_{k,p} + \xi$  imply that  $||\sigma_{k,p} + \xi||_{C^r}$  is also controlled by the local  $L^2$  norm and thus also bounded by  $\exp(-\lambda k^{1/3})$  outside of  $B(p, k^{-1/3})$  as desired.

Proof of Lemma. We use the operator  $\Delta_k = \overline{\partial}_{L^k}^* \overline{\partial}_{L^k} + \overline{\partial}_{L^k} \overline{\partial}_{L^k}^* : \Omega^{0,1}(L^{\otimes k}) \to \Omega^{0,1}(L^{\otimes k})$ . We estimate via a Weitzenböck formula: fixing a tangent frame  $e_i$  of  $T^{1,0}$ ,  $e^i$  the dual frame, we have

(3) 
$$\overline{\partial}^{\alpha} = \sum_{i} \overline{e^{i}} \wedge \nabla_{\overline{e_{i}}} \alpha$$

$$\overline{\partial}^{*} \alpha = -\sum_{i} g(e^{i}, \overline{e^{j}}) i_{\overline{e_{j}}} (\nabla_{e_{i}} \alpha)$$

Take a frame that's orthonormal at the origin, and radially parallel transport so  $\nabla_{e_i}e_j=0$  at the origin; this preserves type (1,0) forms since J is integrable. Then

(4) 
$$\Delta_{k}\alpha = -\sum_{ij} i_{\overline{e_{i}}} (\overline{e_{j}} \wedge \nabla_{e_{i}} \nabla_{\overline{e_{j}}} \alpha) - \sum_{ij} \overline{e^{j}} \wedge (i_{\overline{e_{i}}} \nabla_{\overline{e_{j}}} \nabla_{e_{i}} \alpha)$$

$$= \sum_{i} -\nabla_{e_{i}} \nabla_{\overline{e_{i}}} \alpha + \sum_{ij} \overline{e^{j}} \wedge i_{\overline{e_{i}}} (R^{T^{*}M \otimes L^{k}} (e_{i}, \overline{e_{k}}) \alpha)$$

$$= D\alpha + R\alpha + k\alpha$$

because at the origin  $R^{L^k}(e_i, \overline{e_j}) = -ik\omega(e_i, \overline{e_j}) = k\delta_{ij}$ . D is semipositive, since  $\langle D\alpha, \alpha \rangle = \sum ||\nabla_{\overline{e_i}}\alpha||^2 + d(\text{something}) \implies \int_M \langle D\alpha, \alpha \rangle \geq 0$ . Therefore, for k large enough,  $\Delta_k$  is invertible and  $\exists$  an inverse G of norm  $O(\frac{1}{k})$ .

Given  $s \in \Gamma(L^k)$ , set  $\xi = -\overline{\partial}^* G \overline{\partial} s$ . Then

(1)  $(s + \xi)$  is holomorphic since

$$\overline{\partial}(s+\xi) = \overline{\partial}s - \overline{\partial}\overline{\partial}^*G\overline{\partial}s = \overline{\partial}s - (\Delta_k - \overline{\partial}^*\overline{\partial})G\overline{\partial}s = \overline{\partial}^*\overline{\partial}G\overline{\partial}s$$

but  $\operatorname{Im}\overline{\partial} \cap \operatorname{Im}\overline{\partial}^* = 0$  by Hodge theory, so  $\overline{\partial}(s+\xi) = 0$ .

(2) 
$$||\xi||_{L^{2}}^{2} = \langle \overline{\partial}^{*}G\overline{\partial}s, \overline{\partial}^{*}G\overline{\partial}s \rangle = \langle \overline{\partial}\overline{\partial}^{*}G\overline{\partial}s, G\overline{\partial}s \rangle = \langle \overline{\partial}s, G\overline{\partial}s \rangle \leq ||G|| \left|\left|\overline{\partial}s\right|\right|_{L^{2}}^{2} \leq ck^{-1} \left|\left|\overline{\partial}s\right|\right|_{L^{2}}^{2}$$
. This completes the proof.

Going from these collections of sections to the Kodaira embedding is straightforward:

• Well-definedness: we need that  $\forall p, \exists s \in H^0(L^k)$  s.t.  $s(p) \neq 0$ , which comes from the fact that  $|\tilde{\sigma}_{k,p}(p)| \simeq$ 

- Immersion: need that  $\forall p \in M, v \in T_pM, \ \exists \sigma_1, \sigma_2 \in H^0(L^k) \text{ s.t. } d_v(\frac{\sigma_1}{\sigma_2}) \neq 0.$  This would give us a projection to a certain  $\mathbb{CP}^1$  factor of  $\mathbb{CP}^n$  which has nonzero derivative in the direction of v. We could do this by looking at  $\tilde{\sigma}_{k,q_{\pm}}, q_{\pm} = \exp_p(\pm k^{-1/2}v)$ . More simply, we set  $\sigma_2 = \tilde{\sigma}_{k,p}, \sigma_1$  obtained by a similar process starting from  $z_1\sigma_{k,p}$  (rotating the coordinates so v is along the  $z_1$ -axis) and adding  $\xi$  perturbation to make it holomorphic. Then  $\frac{\sigma_1}{\sigma_2} = z_1 + \cdots \implies d_v(\frac{\sigma_1}{\sigma_2}) \neq 0$ .

  • Injectivity: If p,q are at a distance  $<< k^{-1/3}$  then (using the above argument for immersiveness) the
- sections are different at p and q. If the distance is greater,  $[\tilde{\sigma}_{k,p}:\tilde{\sigma}_{k,p}]\sim[1:0]$  and [0:1] respectively.

---

## SYMPLECTIC GEOMETRY, LECTURE 20

Prof. Denis Auroux

Recall from last time the statement of the following lemma: given L a holomorphic line bundle with curvature  $-i\omega$ ,

**Lemma 1.**  $\forall s \in C^{\infty}(L^{\otimes k}), \ \exists \xi \in C^{\infty}(L^{\otimes k}) \ st. \ ||\xi||_{L^2} \leq \frac{C}{\sqrt{k}} \left|\left|\overline{\partial} s\right|\right|_{L^2} \ and \ s+\xi \ is \ holomorphic.$ 

*Proof.* For this, we use the Weitzenbock formula for

$$\overline{\Box}_k = \overline{\partial}\overline{\partial}^* + \overline{\partial}^*\overline{\partial}: \Omega^{0,1}(L^{\otimes k}) \circlearrowleft$$

where  $\overline{\partial}$  is induced by  $\nabla$  on  $L^{\otimes k}$ . We fix  $p \in M$  and work in a neighborhood with p identified with the origin, choosing a standard frame for  $T_pM \cong \mathbb{C}^n$  with  $e_i = \frac{\partial}{\partial z_i}$  an orthonormal frame of  $T^{1,0}$ ,  $e^i = dz_i$  the dual frame. Using parallel transport w.r.t. the Levi-Cevita connection in the radial directions, we still have these frames (though they are no longer given by coordinates). At the origin, moreover, we have  $\nabla_{e_i}e_j = 0$ . Now,

(2) 
$$\overline{\partial}\alpha = \sum_{i} \overline{e^{i}} \wedge \nabla_{\overline{e_{i}}}\alpha, \ \overline{\partial}^{*}\alpha = -\sum_{i} i_{\overline{e_{i}}}(\nabla_{e_{i}}\alpha)$$

so at the origin

$$\overline{\Box}_{k}\alpha = -\sum_{i,j} i_{\overline{e_{i}}}(\overline{e^{j}} \wedge \nabla_{e_{i}} \nabla_{\overline{e_{j}}} \alpha) - \sum_{i,j} \overline{e^{j}} \wedge (i_{\overline{e_{i}}} \nabla_{\overline{e_{j}}} \nabla_{e_{i}} \alpha)$$

Note that  $\nabla_{\overline{e_j}} \nabla_{e_i} \alpha = \nabla_{e_i} \nabla_{\overline{e_j}} \alpha - R(e_i, \overline{e_j}) \alpha$ , where

$$(4) R = R^{T^*M} \otimes \operatorname{id}_{L^k} + \operatorname{id}_{T^*M} \otimes R^{L^k}$$

is the curvature on  $T^*M \otimes L^k$ . Now,  $i_{\overline{e^i}}\overline{e^j} \wedge \cdot$  maps  $\overline{e^i} \mapsto 0$  and is the identity on other terms when i=j and, when  $i \neq j$ , sends  $\overline{e^i}$  to  $-\overline{e^j}$  and other terms to 0. Similarly,  $\overline{e^j} \wedge (i_{\overline{e_i}} \cdot)$  sends  $\overline{e^i}$  to  $\overline{e^j}$  and maps the other terms to zero. Thus,

(5) 
$$\overline{\Box}_{k}\alpha = -\sum_{i} \nabla_{e_{i}} \nabla_{\overline{e_{i}}}\alpha + \sum_{i,j} \overline{e^{j}} \wedge i_{\overline{e_{i}}} (R(e_{i}, \overline{e_{j}})\alpha)$$

$$= D\alpha + R\alpha + \sum_{i} \overline{e^{i}} \wedge i_{\overline{e_{i}}} (k\alpha) = D\alpha + R\alpha + k\alpha$$

Here, D is a semipositive operator, as  $\int_M \langle D\alpha, \alpha \rangle = \int_M \left| \overline{\partial} \alpha \right|^2 \ge 0$ , while R has order 0 and is independent of k. Thus,

(6) 
$$\int \langle \overline{\square}_{k} \alpha, \alpha \rangle \operatorname{vol}_{0} = \int \langle D\alpha, \alpha \rangle + \int \langle R\alpha, \alpha \rangle + \int k |\alpha|^{2} \ge 0 - C ||\alpha||_{L^{2}}^{2} + k ||\alpha||_{L^{2}}^{2}$$

for some constant C. If k > C, then Ker  $\overline{\square}_k = 0$  and (by self-adjointness under  $L^2$ ) Coker  $\overline{\square}_k = 0$ , so  $\overline{\square}_k$  is invertible. Furthermore, the smallest eigenvalue of  $\overline{\square}_k$  is  $\geq k - C$ , so  $\overline{\square}_k$  admits an inverse G with norm  $\leq \frac{1}{k-C} \leq \mathcal{O}(\frac{1}{k})$ .

Finally, given  $s \in C^{\infty}(L^k)$ , let  $\xi = -\overline{\partial}^* G \overline{\partial} s$ .

(1)  $s + \xi$  is holomorphic:

(7) 
$$\overline{\partial}^{\nabla}(s+\xi) = \overline{\partial}s - \overline{\partial}\overline{\partial}^*G\overline{\partial}s = (\overline{\Box}_k - \overline{\partial}\overline{\partial}^*)G\overline{\partial}s = \overline{\partial}^*\overline{\partial}G\overline{\partial}s$$

But Im  $\overline{\partial} \cap \text{Im } \overline{\partial}^* = \{0\}$ , since  $\overline{\partial} a = \overline{\partial}^* b \implies ||\overline{\partial} a||_{L^2}^2 = \langle \overline{\partial} a, \overline{\partial}^* b \rangle_{L^2} = \langle \overline{\partial} \overline{\partial} a, b \rangle_{L^2} = 0$ . Thus,  $\overline{\partial} (s + \xi) = 0$  as desired.

Prof. Denis Auroux

$$(2) ||\xi||_{L^{2}}^{2} = \leq \mathcal{O}(\frac{1}{k}) \left| \left| \overline{\partial} s \right| \right|_{L^{2}}^{2}:$$

(8) 
$$\left\| \overline{\partial}^* G \overline{\partial} s \right\|_{L^2}^2 = \langle \overline{\partial}^* G \overline{\partial} s, \overline{\partial}^* G \overline{\partial} s \rangle_{L^2} = \langle \overline{\partial} \overline{\partial}^* G \overline{\partial} s, G \overline{\partial} s \rangle_{L^2}$$

$$= \langle \overline{\partial} s, G \overline{\partial} s \rangle_{L^2} \le ||G|| \left| \left| \overline{\partial} s \right| \right|_{L^2}^2 \le \mathcal{O}(\frac{1}{k}) \left| \left| \overline{\partial} s \right| \right|_{L^2}^2$$

## 1. Counterexamples

We know now that K ahler  $\implies$  complex and symplectic, while both imply the existence of an almost-complex structure, and the latter implies that the manifold is even-dimensional and orientable. In dimension 2, these are all the same: in dimension 4, all these inclusions are strict (even when restricting to compact manifolds).

Example. •  $S^4$  is even-dimensional and orientable, but not almost-complex: if it were,  $c_1(TS^4, J) \in H^2(S^4, \mathbb{Z}) = 0$  would satisfy  $c_1^2 \cdot [S^4] = 2c_2 - p_1 = 2\chi + 3\sigma$  (with  $\chi$  the Euler characteristic and  $\sigma$  the signature), which is impossible. Similarly,  $\mathbb{CP}^2 \# \mathbb{CP}^2$  is not almost-complex:

(9) 
$$c_1 = (a, b) \in H^2 \cong \mathbb{Z}^2 \implies c_1^2 \cdot [\mathbb{CP}^2 \# \mathbb{CP}^2] = a^2 + b^2 \neq 2\chi + 3\sigma = 14$$

which is again impossible.

- $\mathbb{CP}^2 \# \mathbb{CP}^2 \# \mathbb{CP}^2$  is almost-complex, but not symplectic or complex: Ehresman-Wu implies that  $\exists J$  with  $c_1 = c \in H^2(M, \mathbb{Z}) \Leftrightarrow c^2 \cdot [M] = 2\chi + 3\sigma$  and  $\forall x \in H_2, \langle c, x \rangle \equiv Q(x, x) \mod 2$ . In our case,  $\chi = 5$  and  $\sigma = 3$ , so the calculation works out. By the Kodaira classification of surfaces, if it were complex it would be Kähler; by Taubes' (1995) theorem on Seiberg-Witten invariants, it is not symplectic.
- The Hopf surface  $S^3 \times S^1 \cong (\mathbb{C}^2 \setminus \{0\})/\mathbb{Z}$  is complex ( $\mathbb{Z}$ -action  $(z_1, z_2) \mapsto (\lambda^n z_1, \lambda^n z_2)$  is holomorphic) but not symplectic  $(H^2 = 0)$ .
- Not all symplectic manifolds have complex structure (compatible or otherwise). For the former case, we have examples of torus bundles over tori; for the latter case, we have the following theorem.

**Theorem 1** (Gompf 1994).  $\forall G$  finitely presented group,  $\exists M^4$  compact, symplectic, but not complex with  $\pi_1(M^4) \cong F$ .

This construction is obtained by performing symplectic sums along codimension 2 symplectic submanifolds. Since

(10) 
$$H_1(M, \mathbb{Z}) = \text{Ab}(\pi_1(M)) = \text{Ab}(G) = G/[G, G]$$

M is not K ahler if this has odd rank (since  $H^1 \cong H^{1,0} \oplus H^{0,1}$ , with the two parts having the same rank). Using the Kodaira classification, one can arrange to obtain non-complex manifolds as well.

• The Kodaira-Thurston manifold  $M = \mathbb{R}^4/\Gamma$ , where  $\Gamma$  is the discrete group generated by

(11) 
$$g_{1}: (x_{1}, x_{2}, x_{3}, x_{4}) \mapsto (x_{1} + 1, x_{2}, x_{3}, x_{4})$$
$$g_{2}: (x_{1}, x_{2}, x_{3}, x_{4}) \mapsto (x_{1}, x_{2} + 1, x_{3} + x_{4}, x_{4})$$
$$g_{3}: (x_{1}, x_{2}, x_{3}, x_{4}) \mapsto (x_{1}, x_{2}, x_{3} + 1, x_{4})$$
$$g_{4}: (x_{1}, x_{2}, x_{3}, x_{4}) \mapsto (x_{1}, x_{2}, x_{3}, x_{4} + 1)$$

is complex and symplectic, but not Kähler. Note that  $\Gamma \subset \operatorname{Symp}(\mathbb{R}^4, \omega_0)$  (obvious for the three translations, while  $g_2^*\omega_0 = dx_1 \wedge d(x_2+1) + d(x_3+x_4) \wedge dx_4 = dx_1 \wedge dx_2 + dx_3 \wedge dx_4$  as desired), so M is symplectic. M is also a symplectic  $T^2$  bundle over  $T^2$ , with the base given by  $x_1, x_2$  and the fiber by  $x_3, x_4$  (with the bundle trivial along the  $x_1$  direction, nontrivial along the  $x_2$  direction with monodromy  $(x_3, x_4) \mapsto (x_3 + x_4, x_4)$ ).

---

## SYMPLECTIC GEOMETRY, LECTURE 21

#### Prof. Denis Auroux

### 1. Counterexamples contd.

We continue our discussion of the Thurston manifold introduced last time. Recall that  $M = \mathbb{R}^4/\Gamma$ , where  $\Gamma$  is generated by the four maps

(1) 
$$g_1: (x_1, x_2, x_3, x_4) \mapsto (x_1 + 1, x_2, x_3, x_4)$$
$$g_2: (x_1, x_2, x_3, x_4) \mapsto (x_1, x_2 + 1, x_3 + x_4, x_4)$$
$$g_3: (x_1, x_2, x_3, x_4) \mapsto (x_1, x_2, x_3 + 1, x_4)$$
$$g_4: (x_1, x_2, x_3, x_4) \mapsto (x_1, x_2, x_3, x_4 + 1)$$

We showed last time that M was symplectic.

Lemma 1.  $H_1(M,\mathbb{Z}) = \mathbb{Z}^3$ .

*Proof.* One way to see this is to note that  $g_3 = [g_4, g_2]$ , so  $Ab(\Gamma) = \Gamma/[\Gamma, \Gamma] = \Gamma/\langle g_3 \rangle \cong \mathbb{Z}^3$ . To see this another way, note that  $\pi_1(M) = \Gamma$  is generated by the four loops  $\gamma_1, \gamma_2, \gamma_3, \gamma_4$  given by the coordinate axes in  $\mathbb{R}^4$ . Look at  $\gamma_4$ : this can be described as

$$(2) \gamma_4 \sim \{(a_1, a_2, a_3, t), t \in [0, 1]\} \sim \{(a_1, a_2 - 1, a_3, t), t \in [0, 1]\} \sim \{(a_1, a_2, a_3 + t, t), t \in [0, 1]\}$$

implying that  $[\gamma_4] = [\gamma_3] + [\gamma_4]$  and  $[\gamma_3] = 0$  in  $H_1(M)$  (so the space is generated by the images of the other three loops).

#### 2. Symplectic Fibrations

Let  $f: M \to B$  be a locally trivial fibration, with generic fiber  $(F, \omega_F)$  a symplectic manifold.

**Definition 1.** f is symplectic if the structure group reduces to  $\operatorname{Symp}(F, \omega_F)$ , i.e.  $\exists$  local trivializations f:  $f^{-1}(U_i) \cong U_i \times F \to U_i$  s.t., over  $U_i \cap U_j$ , the change of trivialization is a symplectomorphism.

Now, let  $f: M \to B$  be a compact, locally trivial symplectic fibration with symplectic fiber  $(F, \omega_F)$  and symplectic base  $(B, \omega_B)$ .

**Theorem 1** (Thurston). If  $\exists c \in H^2(M,\mathbb{R})$  s.t.  $c|_F = [\omega_F] = H^2(F,\mathbb{R})$ . Then  $\forall k >> 0, \exists$  a symplectic form on M in the class  $c + k.f^*[\omega_B]$  for which the fibers of f are symplectic submanifolds.

*Proof.* Choose a closed 2-form  $\eta$  on M s.t.  $[\eta] = c$ , and a cover  $\{U_i\}$  of B by contractible subsets with trivializations  $\phi_i : f^{-1}(U_i) \to F \times U_i$  s.t.  $\phi_i \circ \phi_j^{-1}$  are symplectomorphisms over  $U_i \cap U_j$ . Let  $p_i = \operatorname{pr}_2 \circ \phi_i : f^{-1}(U_i) \to F$ . Then, on  $U_i \times F$ ,  $\eta$  and  $p_i^* \omega_F$  are closed 2-forms, and

(3) 
$$[\eta|_{f^{-1}(U_i)}] = [p_i^* \omega_F] \in H^2(f^{-1}(U_i), \mathbb{R}) \cong H^2(F, \mathbb{R})$$

since  $c|_F = [\omega_F]$ . Thus,  $\exists$  a 1-form  $\alpha_i$  on  $f^{-1}(U_i)$  s.t.  $p_i^*\omega_F = \eta + d\alpha_i$ . Now, let  $\rho_i$  be a partition of unity on B by smooth functions  $\rho_i : B \to [0,1]$ ,  $\operatorname{Supp}(\rho_i) \subset U_i$ , and set  $\tilde{\eta} = \eta + \sum d((\rho_i \circ f)\alpha_i)$ . Then  $\tilde{\eta}$  is closed, with  $[\tilde{\eta}] = [\eta] = c$ : moreover,

(4) 
$$\tilde{\eta}|_{F_p = f^{-1}(p)} = \eta|_{F_p} + \sum_i (\rho_i \circ f) d\alpha_i|_{F_p} = \sum_i \rho_i(f(p))(\eta|_{F_p} + d\alpha_i|_{F_p}) = \omega_F$$

in the trivializations  $\phi_i$ .

We have obtained a closed 2-form  $\tilde{\eta}$  on M s.t.  $[\tilde{\eta}] = c$  which is symplectic on the fibers.  $\forall x \in M$ , split  $T_xM = V_x \oplus H_x$ , where  $V_x = \text{Ker } df_x$  is the tangent space to the fiber and  $H_x = \{v \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM | \tilde{\eta}(v,v') = 0 \forall v' \in T_xM$ 

 $V_x$ . These two spaces are in direct sum since  $\tilde{\eta}|_{V_x}$  is nondegenerate.  $f^*\omega_B$  is nondegenerate on  $H_x$  because  $df_x: H_x \stackrel{\sim}{\to} T_{f(x)}B$ , so  $\tilde{\eta} + kf^*\omega_B$  is nondegenerate on  $H_x$  for k >> 0 since nondegeneracy is an open condition (consider  $f^*\omega_B + \frac{1}{k}\tilde{\eta}$ ). It is also nondegenerate on  $V_x$  since  $(\tilde{\eta} + kf^*\omega_B)|_{V_x} = \tilde{\eta}|_{V_x}$ . Thus, we obtain our desired symplectic form on M.

Remark. Assume dim F=2: then if F is orientable and the fibration is oriented, we always have a symplectic form  $\omega_F$ , and the structure group always reduces to  $\operatorname{Symp}(F,\omega_F)=\operatorname{Diff}^+_{\operatorname{vol}}(F)$ . The cohomological assumption in the theorem is equivalent to the statement that  $[f^{-1}(\operatorname{pt})] \neq 0 \in H_2(M,\mathbb{R})$  (for instance, it is true on the Kodaira-Thurston manifold).

We can generalize this to other settings.

**Definition 2.** A Lefschetz fibration is a map  $M^4 \to \Sigma^2$  between oriented manifolds with isolated critical points modeled in oriented coordinates on  $\mathbb{C}^2 \to \mathbb{C}$ ,  $(z_1, z_2) \to z_1^2 + z_2^2$  (so the central fibers is the union of two lines, and nearby fibers are smooth conics).

**Theorem 2** (Gompf, 1998). If  $f: M^4 \to \Sigma^2$  is a Lefschetz fibration with  $[F] \neq 0 \in H_2(M, \mathbb{R})$ , then M carries a symplectic form s.t. the fibers are symplectic.

**Theorem 3** (Donaldson). For  $(M^4, \omega)$  symplectic, after blowing up points in M, we get  $\hat{M}$  which admits a Lefschetz fibration to  $S^2$ . Here, the blowup is locally given by  $\hat{\mathbb{C}}^2 = \{(x, \ell) \in \mathbb{C}^2 \times \mathbb{CP}^1 | x \in \ell\}$ .

The idea of this theorem is to look at approximately holomorphic sections  $s, s' \in C^{\infty}(L^{\otimes k})$  s.t. s/s' is an "approximately meromorphic" function and has nondegenerate critical points.

# 3. Symplectic Sums (Gompf 1994)

**Definition 3.** A symplectic sum is a connected sum along a codimension 2 symplectic submanifold.

Explicitly, for  $Q^{2n-2} \subset (M^{2n}, \omega)$  a compact, symplectic submanifold,  $NQ = (TQ)^{\perp}$  is a rank 2 symplectic vector bundle over Q. Putting a compactible complex structure on it gives  $c_1(NQ) \in H^2(Q, \mathbb{Z})$ . Assume NQ is trivial, so  $c_1(NQ) = 0$  (i.e. it has a nonvanishing section).

Example. For n = 2,  $c_1$  is precisely the degree of the line bundle, and deg  $(NQ) = [Q] \cdot [Q]$  because the zeroes of a section of NQ are obtained by deforming Q to Q' and intersecting them.

Now, by the symplectic tubular neighborhood theorem, we have a neighborhood of Q in M symplectomorphic to  $(Q \times D^2(\epsilon), \omega|_Q \oplus \omega_0)$ . Idea: use exponential maps to identify  $\phi : v(Q) \stackrel{\sim}{\to} Q \times D^2(\epsilon)$  s.t.  $\phi_*\omega$  and  $(\omega|_Q \oplus \omega_0)$  agree on  $Q \times \{0\}$ , and use local Moser to produce a local symplectomorphism to identify to two forms.

---

## SYMPLECTIC GEOMETRY, LECTURE 22

Prof. Denis Auroux

## 1. Symplectic Sum

Let  $(M_1^{2n}, \omega_1), (M_2^{2n}, \omega_2)$  be symplectic manifolds,  $(Q^{2n-2}, \omega_Q)$  a compact symplectic manifold with symplectic embeddings  $\iota_1: Q \to M_1, \iota_2: Q \to M_2$  and trivial normal bundles. Then  $v(Q_i)$  is symplectomorphic to  $(Q \times D^2(\epsilon), \omega_Q \oplus \omega_0)$ . Let

$$(1) M = M_1 \#_Q M_2 = \left( M_1 \setminus \left( Q_1 \times D^2 \left( \frac{\epsilon}{2} \right) \right) \right) \cup_{\phi} \left( M_2 \setminus \left( Q_2 \times D^2 \left( \frac{\epsilon}{2} \right) \right) \right)$$

where  $\phi$  is given in local coordinates by

(2) 
$$Q \times \left(D^2(\epsilon) - D^2\left(\frac{\epsilon}{2}\right)\right) \to Q \times \left(D^2(\epsilon) - D^2\left(\frac{\epsilon}{2}\right)\right), \ (q, z) \mapsto (q, \psi(z))$$

and  $\psi$  is an orientation- and area-preserving diffeomorphism that exchanges the boundaries. Then  $\psi^*\omega_0 = \omega_0, \phi^*\omega_2 = \omega_1 \implies$  we get a natural symplectic structure on  $M_1 \#_Q M_2$ .

Remark. In this gluing, we "lost" an amount of volume depending on  $\epsilon$ . If one instead forms the manifold as

$$(M_1 \smallsetminus (Q_1 \times D^2(\frac{\epsilon}{2}))) \cup (Q \times \text{ cylinder}) \cup (M_2 \smallsetminus (Q_2 \times D^2(\frac{\epsilon}{2})))$$

one can force  $\operatorname{vol}(M) = \operatorname{vol} M_1 + \operatorname{vol} M_2$ . Moreover,  $M_1 \#_Q M_2$  depends on the isotopy class of  $i_2 \circ i_1^{-1} : Q_1 \to Q \to Q_2$ .

Remark. In dimension 4, it is enough to have  $\Sigma_1 \subset M_1^4, \Sigma_2 \subset M_2^4$  symplectic submanifolds with the self-intersection 0 and identical genus and symplectic area.

We can generalize this construction to the case when the normal bundles are no longer trivial, but dual to each other, i.e.  $c_1(NQ_1)+c_1(NQ_2)=0$ : this implies that we can do the gluing fiberwise since  $(NQ_2)\cong (NQ_1)^*$ . Letting  $L=NQ_1$ , we consider a manifold X which is the total space of  $L\oplus L^*\to Q$ , on which we can put a symplectic structure compatible with the symplectic structures on  $L, L^*$ . By local Moser,  $\exists$  a local description

(4) 
$$M_1 \cong \{(g, s_1, 0) \in Q \times L_q \times L_q^*\}, M_2 \cong \{(g, 0, s_2) \in Q \times L_q \times L_q^*\}$$

 $M_1, M_2$  intersect along the zero section, and

(5) 
$$M_1 \cup_O M_2 = \{(q, s_1, s_2) | s_1 s_2 = 0\}$$

Let  $M = \{(q, s_1, s_2) | s_1 s_2 = \delta \chi(|s_1|, |s_2|)\}$  for  $\delta \neq 0$  small (can consider it to be a complex number fixing  $L \otimes L^* \cong \underline{\mathbb{C}}$  or a nonvanishing section of  $L \otimes L^*$ ) and  $\chi$  a cutoff function which makes M look like  $M_1$  or  $M_2$  away from Q. We claim without proof that we can choose  $\delta$  small enough that we get a symplectic structure on M.

Remark. In dimension 4, the above assumption implies that  $[\Sigma_1] \cdot [\Sigma_1] + [\Sigma_2] \cdot [\Sigma_2] = 0$ . We can do the same construction assuming only that  $[\Sigma_1] \cdot [\Sigma_1] + [\Sigma_2] \cdot [\Sigma_2] \ge 0$ . Consider,  $L_1 = N\Sigma_1, L_2 = N\Sigma_2, X = L_1 \oplus L_2 \to \Sigma$ , and set

(6) 
$$M = \{(q, s_1, s_2) | s_1 s_2 = \delta \sigma(q) \chi(|s_1|, |s_2|) \}$$

where  $\sigma$  is a section of  $L_1 \otimes L_2$ . To ensure that M is smooth, we need  $\sigma$  to vanish transversally, i.e. its zeroes  $\sim \sigma(z) = z$  or  $\sigma(z) = \overline{z}$ . To ensure that M is symplectic, we require all the zeros of  $\sigma$  to have complex orientation, which requires  $\sim \sigma(z) = z$  and deg  $(L_1 \otimes L_2) \geq 0$ .

An application of the symplectic sum construction is the following result:

**Theorem 1** (Gompf 1994). Every finitely presented group G is  $\pi_1$  of a compact symplectic 4 manifold.

Write  $G = \langle g_1, \dots, g_k | r_1, \dots, r_k \rangle$  where  $g_i$  are generators and  $r_i$  are relations. Let F be a compact genus k surface with standard generators  $(\alpha_1, \beta_1, \dots, \alpha_k, \beta_k)$  of  $\pi_1$  s.t.

(7) 
$$\pi_1(F) = \langle \alpha_1, \beta_1, \dots, \alpha_k, \beta_k | \prod_{i=1}^k [\alpha_i, \beta_i] = 1 \rangle$$

That is,  $F = F^0 \cup D^2$ , where  $F^0 = \bigvee^{2g} S^1$  is the 1-skeleton and  $D^2$  is attached along  $\prod \alpha_i \beta_i \alpha_i^{-1} \beta_i^{-1}$ . Now, for  $i = 1, ..., \ell$ , choose  $\gamma_i$  an immersed closed curve in F representing  $\sigma_i(\alpha_1 \cdots \alpha_k)$ . Let  $\gamma_{\ell+j} = \beta_j$  for j = 1, ..., k. Then

(8) 
$$G = \pi_1(F)/\langle \gamma_1 \cdots \gamma_{k+\ell} \rangle$$

Assume  $\exists \rho \in \Omega^1(F)$  a closed 1-form s.t.  $\rho|_{\gamma_i}$  is a positive form at every point of every  $\gamma_i$  (there exists a procedure to do this, at the expense of increasing the genus and the number of  $\gamma_i$ 's). Set  $X = F \times T^2$ ,  $\omega = \omega_1 + \omega_2$ . From before we have  $\gamma_i \subset F$ ,  $\rho \in \Omega^1(F)$  closed s.t.  $\rho|_{\gamma_i} > 0$ , and we can similarly find  $\alpha_i \subset T^2$  disjoint nontrivial simple closed curves and  $\theta \in \Omega^1(T^2)$  closed with  $\theta|_{\alpha_i} > 0$  (for instance,  $\theta = dx$  for  $\alpha_i = S^1 \times \{p_i\}$ ). Then  $T_i = \gamma_i \times \alpha_i$  are Lagrangian w.r.t  $\omega$ , symplectic w.r.t.  $\omega' = \omega + \rho \wedge \theta$ . Now do a symplectic sum construction, attaching  $(\mathbb{CP}^2, E = \{(x_0 : x_1 : x_2) | x_0^3 + x_1^3 + x_2^3 = 0\})$ .

Remark (Adjunction Formula). For a connected, embedded compact symplectic  $\Sigma^2 \subset (M^4, \omega)$ ,  $TM|_{\Sigma} = T\Sigma \oplus N\Sigma$  as symplectic vector bundles, so

(9) 
$$c_1(TM|_{\Sigma}) = c_1(T\Sigma) + c_1(N\Sigma) \in H^2(\Sigma) = \mathbb{Z}$$
$$c_1(TM) \cdot [\Sigma] = 2 - 2g(\Sigma) + [\Sigma] \cdot [\Sigma]$$

In our case, this implies that the genus is 1, i.e. we have a torus on both sides that can be glued. The tori  $T_i$  are disjoint, and  $[T_i] \cdot [T_i] = 0$ : since  $[E] \cdot [E] = 9$ , we can do the symplectic sum. Doing the sums along the  $T_i$  as well as  $\{z\} \times T^2, z \in F \setminus (\bigcup \gamma_i)$ , we kill  $\gamma_i$  and the generators of the  $T^2$ . Indeed, using Van Kampen, we can show that  $\#_E \mathbb{CP}^2$  just kills  $\mathrm{Im}(\pi_1(\Sigma) \to \pi_1(M))$ , giving us the desired manifold.

Now we will study further the topology of 4-manifolds.

*Problem.* Let M be the connected sum of 9 copies of  $\mathbb{CP}^2$  and 44 copies of  $\overline{\mathbb{CP}}^2$ . Then M is homeomorphic but not diffeomorphic to  $\{x_0^5+x_1^5+x_2^5+x_3^5=0\}\subset\mathbb{CP}^3$ .

---

## SYMPLECTIC GEOMETRY, LECTURE 23

Prof. Denis Auroux

## 1. Branched Covers

**Definition 1.** For  $(M, \omega)$  a symplectic manifold,  $p \in M$ , a local diffeomorphism  $\phi : U \to \mathbb{C}^n$  for  $U \ni p$  is  $\omega$ -tame if  $(\phi_*\omega)(v, iv) > 0 \ \forall v \neq 0 \in \mathbb{C}^n$ . This is,  $\phi^*J_0$  is  $\omega$ -tame, i.e. complex lines in  $\mathbb{C}^n$  give symplectic submanifolds in M.

**Definition 2.** A map  $f: X^4 \to (Y^4, \omega_Y)$  from a compact, oriented manifold to a compact, symplectic manifold is a symplectic branched covering if  $\forall p \in X, \exists U \ni p, V \ni f(p)$  coordinate neighborhoods (with  $\phi: U \to \mathbb{C}^2$  an oriented diffeomorphism,  $\psi: V \to \mathbb{C}^2$  an  $\omega_Y$ -tame diffeomorphism) s.t. the right vertical map of the commutative diagram

(1) 
$$X \supset U \xrightarrow{\phi} \mathbb{C}^{2}$$

$$f \downarrow \qquad \qquad \downarrow \psi f \phi^{-1}$$

$$Y \supset V \xrightarrow{g_{1}} \mathbb{C}^{2}$$

is one of

- (1)  $(u,v) \mapsto (z_1,z_2) = (u,v)$  (local diffeomorphism),
- (2)  $(u,v) \mapsto (z_1,z_2) = (u^2,v)$  (simple branching),
- (3)  $(u, v) \mapsto (z_1, z_2) = (u^3 uv, v)$  (cusp)

Remark. Simple branching also makes sense in higher dimensions as  $(x_1, \ldots, x_n) \mapsto (x_1^2, x_2, \ldots, x_n)$ . Moreover, we could allow higher order branching, i.e.  $(u, v) \mapsto (u^p, v)$  for p > 2, but this isn't generic.

*Remark.* The three models given above correspond to the 3 generic local models for holomorphic maps  $\mathbb{C}^2 \to \mathbb{C}^2$ .

**Definition 3.** The ramification curve is the set  $R \subset X$  s.t.  $R = \{p \in X | df(p) \text{ not onto}\}$ . The branch (discriminant) curve is  $D = f(R) \subset Y$ , i.e.  $D = \{q \in Y | \#f^{-1}(q) < \deg f\}$ .

We can calculate these curves explicitly in local coordinates. For instance, in the case of simple branching, we have that  $\operatorname{Jac}(f) = \det (df) = \left| \begin{pmatrix} 2u & 0 \\ 0 & 1 \end{pmatrix} \right| = 2u$ , so  $R = \{u = 0\}, D = \{z_1 = 0\}$ . In the case of a cusp, we have

(2) 
$$\operatorname{Jac}(f) = \det (df) = \left| \begin{pmatrix} 3u^2 - v & -u \\ 0 & 1 \end{pmatrix} \right| = 3u^2 - v$$

so  $R = \{v = 3u^2\}$  and  $D = \{27z_1^2 = 4z_2^3\}$ . What happens at the cusp:  $\forall p \in R$ , Ker  $df = \mathbb{C} \times \{0\} \subset T_p\mathbb{C}^2$ , so Ker df is transverse to TR at most points, but not at the cusp.

**Lemma 1.**  $R \subset X$  is a smooth, 2-dimensional submanifold, and  $D \subset Y$  is a symplectic submanifold of Y immersed except at isolated points (corresponding to cusps). In local coordinates, D is a complex curve, so TD consists of complex lines and  $\omega_Y|_{TD} > 0$ .

Note that the generic singularities of D consist of two types: complex cusps and transverse double points (with either orientation, i.e.  $T_qY = T_1 \oplus T_2$  with agreeing or disagreeing orientations).

**Proposition 1.** If  $f: X^4 \to (Y^4, \omega_Y)$  is a symplectic branched covering, then X carries a symplectic form  $\omega_X$  (canonical up to isotopy) s.t.  $[\omega_X] = f^*[\omega_Y]$ .

*Proof.* Note that  $f^*\omega_Y$  is a closed 2-form which is nondegenerate outside of R.  $\forall p \in R, K_p = \text{Ker } df_p \subset T_pX$  is the kernel of  $f^*\omega_Y$ , and is a complex line in local coordinates (so it carries a natural orientation). We claim that  $\exists \alpha$  an exact 2-form on X s.t.  $\forall p \in R, \alpha|_{K_p} > 0$  is positive nondegenerate. Assuming this, we have that  $\omega_X = f^*\omega_Y + \epsilon \alpha$  for  $\epsilon > 0$  sufficient small is closed and nondegenerate, since

(3) 
$$\omega_X \wedge \omega_X = f^* \omega_Y \wedge f^* \omega_Y + 2\epsilon f^* \omega \wedge \alpha + \epsilon^2 \alpha \wedge \alpha$$

with the first term  $\geq 0$  everywhere and nondegenerate outside R, the second term positive on R (in local coordinates,  $f^*\omega_Y=\frac{i\lambda}{2}(dv\wedge d\overline{v})$  for some  $\lambda>0$ , and  $\alpha|_{\mathbb{C}\times\{0\}}>0$ ), and the third term negligible for small  $\epsilon$ .

We are left to prove our claim. Fix  $p \in R$ , and choose local coordinates (u, v) on X of our model. Set x = Re(u), y = Im(u), and  $\alpha_p = d(\chi_1(|u|)\chi_2(|v|)xdy)$ , where  $\chi_1, \chi_2$  are cutoff functions chosen s.t.  $\forall q \in R \cap \text{Supp}(\chi_2), \chi_1 \equiv 1$ . In local coordinates, we have that

$$(4) \qquad \forall (u,v) \in R \cap \operatorname{Supp}(\chi_2), \alpha_p|_{K=\mathbb{C} \times \{0\}} = \chi_2(|v|) dx \wedge dy > 0$$

and 0 outside Supp( $\chi_2$ ). Covering R by small neighborhoods, and taking  $\alpha$  to be the sum of these  $\alpha_p$  gives the desired exact form.

Finally, to see that the choice of  $\omega_X$  is canonical up to isotopy, note that the set of  $\alpha$ 's satisfying our claim (i.e. exact 2-forms s.t.  $\alpha|_K > 0$  along R) is convex. That is, we can find an  $\epsilon$  sufficiently small s.t., for two such forms  $\alpha_1, \alpha_2$ ,

(5) 
$$f^*\omega_Y + \epsilon\alpha_1, \ f^*\omega_Y + \epsilon\alpha_2, \ f^*\omega_Y + \epsilon(t\alpha_1 + (1-t)\alpha_2)$$

are all symplectic.  $\Box$ 

There is a converse to this result. Let  $(X^4, \omega)$  be a complex symplectic,  $\frac{1}{2\pi}[\omega] \in H^2(X, \mathbb{Z})$ ,  $L \to X$  a line bundle s.t.  $c_1(L) = \frac{1}{2\pi}[\omega]$ , J a compatible almost-complex structure, etc. Recall that  $L^{\otimes k}$  has many approximately-holomorphic sections: choosing three "good" sections, we obtain a map  $f: X \to \mathbb{CP}^2$  which locally looks like one of our models. That is,

**Theorem 1.** Every compact symplectic 4-manifold with integral  $\frac{1}{2\pi}[\omega]$  can be realized as a symplectic branched cover of  $\mathbb{C}P^2$ .

This  $f_k$  will look like the local models in coordinates which are  $\omega$ -tame on X and  $\omega_0$ -tame on  $\mathbb{C}P^2$ , and applying the proposition to  $f_k$  gives  $[f_k^*\omega_0] = k[\omega]$  with  $\omega_X$  isotopic to  $k\omega$ . Moreover, if k is large enough, then  $\exists$  a preferred choice of  $f_k: X \to \mathbb{C}P^2$  up to homotopy among symplectic branched covers.

Remark. If D is holomorphic, then we can lift  $J_0$  to X, i.e. X is a Kähler manifold and f is holomorphic. Conversely, if X is not Kähler, then the singular symplectic curve  $D \subset \mathbb{CP}^2$  is not isotopic to any holomorphic curve.

---

## SYMPLECTIC GEOMETRY, LECTURE 24

Prof. Denis Auroux

## 1. Homeomorphism Classification of Simply Connected Compact 4-Manifolds

**Theorem 1** (Freedman).  $M_1, M_2$  compact, simply connected, oriented smooth 4-manifolds are homeomorphic  $\Leftrightarrow$  the intersection pairings  $Q_i: H_2(M_i, \mathbb{Z}) \times H_2(M_i, \mathbb{Z}) \to \mathbb{Z}$  are isomorphic as integer quadratic forms (of  $|\det| = 1$ ). It suffices to check that the following invariants coincide:  $b_2 = \operatorname{rk} H_2(M), \sigma = b_2^+ - b_2^-$  (the signature), and  $Q(x, x) \mod 2 \forall x$  (the parity).

Example. For  $M=\mathbb{CP}^2$ , we have  $Q_{\mathbb{CP}^2}=(1)$  on  $H_2(\mathbb{CP}^2,\mathbb{Z})=\mathbb{Z}[\mathbb{CP}^2]$ , while  $N=\overline{\mathbb{CP}^2}$  (with reversed orientation) has  $Q_{\overline{\mathbb{CP}^2}}=(-1)$ . By Mayer-Vietoris, one can see that  $H_2(M\#N)=H_2(M)\oplus H_2(N)$  and  $Q_{M\#N}=Q_M\oplus Q_N$ . Applying this to m copies of  $\mathbb{CP}^2$  and n copies of  $\overline{\mathbb{CP}^2}$  gives the matrix  $\begin{pmatrix} I_{m\times m} \\ -I_{n\times n} \end{pmatrix}$  which gives all the unimodular odd quadratic forms ( $|\det|=1$ ).

Example.  $Q_{S^2 \times S^2} = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$  has  $b_2^+ = b_2^- = 1$  like  $\mathbb{CP}^2 \# \overline{\mathbb{CP}^2}$ , but different parity.

Example. A K3 is a surface of degree 4 in  $\mathbb{CP}^3$  (given, for instance, by  $\{x_0^4 + x_1^4 + x_2^4 + x_3^4 = 0\}$ ). We have  $b_2 = 22, b_2^+ = 3, b_2^- = 19$ , and  $Q = 2.(-E_8) \oplus 3.\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ , where  $(-E_8)$  is the matrix

$$\begin{pmatrix}
-2 & 1 & & & & & \\
1 & -2 & 1 & & & & & \\
& 1 & -2 & 1 & & & & \\
& & 1 & -2 & 1 & & & \\
& & & 1 & -2 & 1 & 0 & 1 \\
& & & & 1 & -2 & 1 & 0 \\
& & & & 0 & 1 & -2 & 0 \\
& & & & 1 & 0 & 0 & -2
\end{pmatrix}$$

**Theorem 2** (Donaldson). In the even case,  $Q = (2k).(\pm E_8) \oplus m \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ .

Remark. The Rokhlin signature theorem (16| $\sigma$  in the even case) implies that the number of  $\pm E_8$  summands is even.

Remark. The  $\frac{11}{8}$  conjecture claims that the m in the theorem above satisfies  $m \ge 3k$ : it has been shown (Furuta, 1995) that  $m \ge 2k$ .

Remark. Smooth compact 4-manifolds may have infinitely many exotic smooth structures: K3 surfaces are known to have infinitely many smooth structures, as do the manifolds  $\mathbb{CP}^2 \# n.\overline{\mathbb{CP}^2}$  for  $n \geq 3$ .

## 2. Seiberg-Witten Invariants [J. Morgan], [Witten '94]

Let  $X^4$  be a compact manifold, with Riemannian metric g and spin<sup>c</sup> structure s. The goal of Seiberg-Witten theory is to assign a number to the pair (g, s) giving the number of "abelian supersymmetric magnetic monopoles" on the manifold.

**Definition 1.** A spin<sup>c</sup> structure is a rank 4 Hermitian complex vector bundle  $S \to X$  along with a Clifford multiplication (unitary representation of a Clifford algebra)  $\gamma : T^*X \times S \to S$  (i.e.  $\gamma(u)\gamma(v) + \gamma(v)\gamma(u) = -2\langle u, v \rangle$  id and  $\gamma(u)^* = -\gamma(u)$ ).


Example. For  $\{e_i\}$  an orthonormal basis,  $\gamma(e^i) \in U(S)$ , since  $\gamma(e^i)^2 = -1$ , and  $\gamma(e^i)\gamma(e^j) + \gamma(e^j)\gamma(e^i) = 0$ .

We extend our Clifford multiplication to

(2) 
$$\gamma: \bigwedge^*(T^*X) \times S \to S, \gamma(e^{i_1} \wedge \dots \wedge e^{i_p}) = \gamma(e^{i_1}) \dots \gamma(e^{i_p})$$

for  $(e^i)$  orthonormal. Applying this to the volume form gives  $\gamma(\text{vol})^2 = (\gamma(e^1)\gamma(e^2)\gamma(e^3)\gamma(e^4))^2 = \text{id}$  and thus a decomposition  $S = S^+ \oplus S^-$ , with the former having  $\gamma(\text{vol}) = -1$  and the latter  $\gamma(\text{vol}) = 1$ . Moreover,  $\gamma(e^i)$  maps  $S^{\pm}$  to  $S^{\mp}$ .

**Lemma 1.** We can represent complexified forms via  $\gamma: \wedge^* \otimes \mathbb{C} \xrightarrow{\sim} \operatorname{End}(S^+ \oplus S^-)$ . More specifically, we have decompositions

$$\wedge^{even} \otimes \mathbb{C} \cong \operatorname{End}(S^+) \oplus \operatorname{End}(S^-)$$

$$\wedge^{odd} \otimes \mathbb{C} \cong \operatorname{Hom}(S^+, S^-) \oplus \operatorname{Hom}(S^-, S^+)$$

with  $\gamma(*\alpha) = \gamma(\alpha)$  on  $S^+$  and  $-\gamma(\alpha)$  on  $S^-$  for any  $\alpha \in \wedge^2$ , so

(4) 
$$\operatorname{End}(S^{+}) = \mathbb{C} \oplus (\wedge_{+}^{2} \otimes \mathbb{C}), \operatorname{End}(S^{-}) = \mathbb{C} \oplus (\wedge_{-}^{2} \otimes \mathbb{C})$$

**Theorem 3.** Every compact 4-manifold admits  $\operatorname{spin}^c$  structures classified up to 2-torsion by  $c = c_1(S^+) = c_1(S^-) = c_1(L) \in H^2(X,\mathbb{Z})$ , where  $L = \det(S^+) = \wedge^2 S^+ = \wedge^2 S^-$ . Moreover, c is a characteristic element, i.e.  $\langle c_1(L), \alpha \rangle \equiv Q(\alpha, \alpha) \mod 2$ .

In particular, if  $E \to X$  is a line bundle, the mapping  $(S^+, S^-) \mapsto (S^+ \otimes E, S^- \otimes E)$  gives a twisting of the spin<sup>c</sup> structure by any line bundle.

**Proposition 1.** If X admits a g-orthogonal almost-complex structure J, then  $\exists$  a canonical spin<sup>c</sup> structure given by  $S^+ = \wedge^{0,0} \oplus \wedge^{0,2}$ ,  $S^- = \wedge^{(0,1)}$  with

(5) 
$$\forall u \in T^*X, \gamma(u) = \sqrt{2}[(u^{0,1} \wedge \cdot) - \iota_{(u^{1,0})^{\#}}(\cdot)]$$

Note that  $L = \wedge^2 S^- = \wedge^2 S^+ = \wedge^{0,2}$  is the anti-canonical bundle. All other spin structures are given by  $S^+ = E \oplus (\wedge^{0,2} \otimes E), S^- = \wedge^{0,1} \otimes E, \forall E \to X$  a line bundle.

## 3. Dirac Operator

**Definition 2.** A spin<sup>c</sup> connection on  $S^{\pm}$  is a Hermitian connection  $\nabla^A$  s.t.

(6) 
$$\nabla_v^A(\gamma(u)\phi) = \gamma(\nabla_v^{LC}u)\phi + \gamma(u)\nabla_v^A\phi$$

**Proposition 2.** Any two spin<sup>c</sup> connections differ by a 1-form on X of the type  $ia \otimes id_{S^{\pm}}$ , and the induced connection A on  $L = \wedge^2 S^{\pm}$  defines the spin<sup>c</sup> connection uniquely.

**Definition 3.** Given a spin<sup>c</sup> structure and a connection, the Dirac operator is

(7) 
$$D_A: \Gamma(S^{\pm}) \to \Gamma(S^{\pm}), \ D_A \psi = \sum_i \gamma(e^i) \nabla_{e_i}^A \psi$$

for  $\{e_i\}$  an orthonormal basis (though it is independent of choice of basis).

Example. On a Kähler manifold,  $S^+ = E \oplus \wedge^{0,2} \otimes E, S^- = \wedge^{0,1} \otimes E, \nabla^A$  corresponds to a unitary connection  $\nabla^a$  on E, i.e. via  $\nabla^A = \nabla^{LC} \otimes 1 + 1 \otimes \nabla^a$ . Then  $D_A = \sqrt{2}(\overline{\partial}_a + \overline{\partial}_a^*)$  and  $D_A^2 = 2\overline{\square}_a$ .

**Definition 4.** The Seiberg-Witten equations are the equations

(8) 
$$D_A \psi = 0 \in \Gamma(S^-)$$
$$\gamma(F_A^+) = (\psi^* \otimes \psi)_0 \in \Gamma(\operatorname{End}(S^+))$$

where A is a Hermitian connection on  $L = \wedge^2 S^{\pm}$  (corresponding to a spin<sup>c</sup> connection on  $S^{\pm}$ ),  $\psi \in \Gamma(S^+)$  is a section,  $F_A^+ = \frac{1}{2}(F_A + *F_A) \in i\Omega_+^2$  for  $F_A \in i\Omega^2$  the curvature of A, and  $(\psi^* \otimes \psi)_0 = \psi^* \otimes \psi - \frac{1}{2} |\psi|^2$  is the traceless part of  $\psi^* \otimes \psi$ .

---

## SYMPLECTIC GEOMETRY, LECTURE 25

Prof. Denis Auroux

## 1. Spin Structures

Let  $(X^4, g)$  be an oriented Riemannian manifold,  $S = S_+ \oplus S_- \to X$  a spin<sup>c</sup> structure with Clifford multiplication  $\gamma : T^*X \otimes S \to S$ .

Example. If X is almost-complex,  $S_+ = (\bigwedge^{0,0} \otimes E) \oplus (\bigwedge^{0,2} \otimes E), S_- = (\bigwedge^{0,1} \otimes E), \gamma(u) = \sqrt{2}[u^{0,1} \wedge \cdot - \iota_{(u^{1,0})^{\#}}\cdot]$ . As defined last time,  $L = \det(S_+) = \det(S_-) = K_X^{-1} \otimes E^2$ .

As we stated last time, the Clifford multiplication extends to differential forms with  $\bigwedge_{+}^{2} \cong \operatorname{End}_{TLAH}(S^{+})$  (where the latter group is the space of traceless, anti-hermitian endomorphisms). We also have the Dirac operator associated to a spin<sup>c</sup> connection  $\nabla^{A}$  on S:

(1) 
$$D_A: \Gamma(S^{\pm}) \to \Gamma(S^{\mp}), D_A \psi = \sum_i \gamma(e^i)(\nabla_{e_i}^A \psi)$$

Example. If X is Kähler, the spin<sup>c</sup> connection is induced by  $\nabla_a$  connection on E, and  $D_A = \sqrt{2}(\overline{\partial}_a + \overline{\partial}_a^*)$ .

Example.  $\nabla^A = \nabla^{A_0} + ia \otimes id$  on  $S_{\pm}$  for  $a \in \Omega^1$  corresponding to  $A = A_0 + 2ia$  on L. The associated decomposition of the Dirac operator is  $D_A = D_{A_0} + \gamma(a)$ .

## 2. Seiberg-Witten Equations

**Definition 1.** The Seiberg-Witten equations are the equations

(2) 
$$D_A \psi = 0 \in \Gamma(S^-)$$
$$\gamma(F_A^+) = (\psi^* \otimes \psi)_0 [+\gamma(\mu)] \in \Gamma(\text{End}(S^+))$$

where A is a Hermitian connection on  $L = \bigwedge^2 S^{\pm}$  (corresponding to a spin<sup>c</sup> connection  $\nabla^A$ ),  $\psi \in \Gamma(S+)$  is a section,  $F_A^+ = \frac{1}{2}(F_A + *F_A) \in i\Omega_+^2$  for  $F_A \in i\Omega^2$  the curvature of A,  $(\psi^* \otimes \psi)_0$  is the traceless part of  $\psi^* \otimes \psi$ , and  $\mu$  is an imaginary self-dual form fixed in advance.

Now, there exists an  $\infty$ -dimensional group of symmetries preserving solutions, called the gauge group  $\mathcal{G} = C^{\infty}(X, S^1)$  where  $f \in C^{\infty}(X, S^1)$  acts by

$$(3) (A, \psi) \mapsto (A - 2df \cdot f^{-1}, f\psi)$$

**Proposition 1.** This preserves the solution space, and the action of  $\mathcal{G}$  is free unless  $\psi \equiv 0$  (reducible solutions), where  $\operatorname{Stab}((A,0)) \cong S^1$  is the space of constant maps.

Reducible solutions can happen  $\Leftrightarrow F_A^+ = \mu$  has a solution  $\Leftrightarrow (g,\mu)$  lie in a codimension  $b_2^+$  subspace. Thus, we want to assume  $b_2^+(X) \ge 1$ , and  $(g,\mu)$  generic. Note that, for  $\mu = 0$ ,  $F_A^+ = 0 \Leftrightarrow \frac{i}{2\pi}F_A$  is closed and antiselfdual in the class  $c_1(L) \in \mathcal{H}^2_- \subset \mathcal{H}^2_- \oplus \mathcal{H}^2_+ = H^2$ .

**Definition 2.** The moduli space of solutions  $\mathcal{M}(S, g, \mu)$  is the set of solutions modulo  $\mathcal{G}$ .

**Theorem 1.** For  $(g, \mu)$  generic,  $\mathcal{M}$  (if nonempty) is a smooth, compact, orientable manifold of dimension

(4) 
$$d(S) = \frac{1}{4}(c_1(L)^2 \cdot [X] - (2\chi + 3\sigma))$$

Idea: We want to understand, given a solution  $(A_0, \psi_0)$  to the SW equations, the nearby solutions to the same equations. We linearize the SW equations, and let  $(a, \phi) \in \Omega^1(X, i\mathbb{R}) \times C^{\infty}(S^+)$  be a small change in the solution, obtaining

(5) 
$$P_1: (a,\phi) \mapsto D_{A_0}\phi + \gamma(a)\psi_0$$

as the linearization of the first equation and

(6) 
$$P_2: (a,\phi) \mapsto \gamma((da)^+) - (\phi \otimes \psi_0^* + \psi_0 \otimes \phi^*)_0$$

as the linearization of the second equation. We restrict  $P = P_1 \oplus P_2$  to a slice transverse to the  $\mathcal{G}$ -action  $A \mapsto A - 2df \cdot f^{-1}, \psi \mapsto f\psi$ , i.e. to  $\mathcal{S} = \{(a,\phi)|d^*a = 0 \text{ and } \operatorname{Im}(\langle \phi, \psi_0 \rangle_{L^2}) = 0\}$  (which is transverse to the  $\mathcal{G}$ -orbit at  $(A_0, \psi_0)$ ). Then  $P|_{\operatorname{Ker}\ d^* \times L^2_1(S^+)}$  is a differential operator of order 1, and is Fredholm (f.d. kernel and cokernel) since

(7) 
$$(P \oplus d^*): L_2^2(X, i \wedge^1) \times L_1^2(S^+) \to L^2(S^-) \times L_1^2(X, i \wedge^2) \times L_1^2(X, i \mathbb{R})$$

 $(=D_{A_0} \oplus (d^+ \oplus d^*) + \text{order } 0)$  is elliptic. Elliptic regularity implies that both Ker, Coker lie in  $C^{\infty}$ . For generic  $(g,\mu)$ , P is surjective (specifically, consider  $\{(A,\psi,\mu)|\cdots\}/\mathcal{G}$  and apply Sard's theorem to project to  $\mu$  and find a good choice). We expect that Ker P is the tangent space to  $\mathcal{M}$ : this is only ok if Coker P=0, so we can use the implicit function theorem to show that  $\mathcal{M}$  is smooth with  $T\mathcal{M}=\text{Ker }P|_{\mathcal{S}}$ . The statement about the dimension follows from the Atiyah-Singer index theorem, which gives a formula for  $d(S)=\text{ind}(P|_{\mathcal{S}})=\text{dim Ker }-\text{dim Coker}$ . Compactness of  $\mathcal{M}$  follows from the a priori bounds on the solutions: the key point is that we get a bound on  $\sup |\psi|$ , so elliptic regularity and "bootstrapping" give us bounds in all norms.

Consider a solution  $(A, \psi)$  of the SW equations (for simplicity assume  $\mu = 0$ ). We have the following Weitzenbock formula for the Dirac operator:

(8) 
$$D_A^2 \psi = \nabla_A^* \nabla_A \psi + \frac{s}{4} \psi + \frac{1}{2} \gamma(F_A^+) \psi$$

where  $\nabla_A^*$  is the  $L^2$ -adjoint of  $\nabla_A$ , s is the scalar curvature of the metric g (this can be shown by calculation in a local frame). Now,

(9) 
$$D_A \psi = 0 \implies 0 = \langle D_A^2 \psi, \psi \rangle = \langle \nabla_A^* \nabla_A \psi, \psi \rangle + \frac{s}{4} |\psi|^2 + \frac{1}{2} \langle \gamma(F_A^+) \psi, \psi \rangle$$

where  $\gamma(F_A^+) = (\psi^* \otimes \psi)_0 = \psi^* \otimes \psi - \frac{1}{2} |\psi|^2$ . Then

(10) 
$$0 = \frac{1}{2} d^* d |\psi|^2 + |\nabla_A \psi|^2 + \frac{s}{4} |\psi|^2 + \frac{1}{4} |\psi|^4$$

Take a point where  $|\psi|$  is maximal. Then

(11) 
$$\frac{1}{2}d^*d|\psi|^2 \ge 0 \implies \frac{s}{4}|\psi|^2 + \frac{1}{4}|\psi|^4 \le 0 \implies |\psi|^2 \le \max(-s,0)$$

**Theorem 2.** If g has scalar curvature > 0, then the SW-invariants  $\equiv 0$ .

*Proof.* A small generic perturbation ensures that there are no reducible solutions. The above estimate on  $\sup |\psi|$  ensures that there are no irreducible solutions either.
