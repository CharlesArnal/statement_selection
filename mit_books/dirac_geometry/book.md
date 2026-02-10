# 18.969: Topics in Geometry

## Contents

| 1         | 1.2 Geometry of Foliations                                                                                                    | 3 3 4          |
|-----------|-------------------------------------------------------------------------------------------------------------------------------|----------------|
| 2         | 2.2 Symplectic Manifolds                                                                                                      | 5 5 6          |
| 3         | 3.4 Forms on a Complex Manifold                                                                                               |                |
| 4         | Lecture 4 (Notes: J. Pascaleff)1 $4.1$ Geometry of $V \oplus V^*$ 1 $4.2$ Linear Dirac structures1 $4.3$ Generalized metrics1 | 13             |
| 5         | 5.1       Spinors       1         5.2       The Spin Group       1         5.3       A Bilinear Pairing on Spinors       1    | 16<br>17<br>18 |
| 6         | 6.1 Generalized Hodge star                                                                                                    | 20<br>21       |
| 7         | 7.1 Exact Courant Algebroids                                                                                                  | 22<br>22<br>23 |
| 8         | 8.1 Dirac Structures                                                                                                          | 25<br>25<br>27 |
| 9         | Lecture 9 (Notes: K. Venkatram)                                                                                               | <b>27</b>      |
|           | 9.1 Bilinar forms on groups                                                                                                   | 28             |
|           | 9.1.1 Key calculation                                                                                                         | 28             |
| 10        | Lecture 10 (Notes: K. Venkatram)                                                                                              | 29             |
|           | 10.1 Integrability                                                                                                            | 29             |
|           | 10.2 Dirac Maps                                                                                                               |                |
|           | 10.3 Manifolds with Courant Structure                                                                                         | 30             |
| 11        | Lecture 11(Notes: K. Venkatram)                                                                                               | 31             |
|           | 11.1 Integrability and spinors                                                                                                | 31             |
|           | 11.2 Lie Bialgebroids and deformations                                                                                        |                |
| 12        | Lecture 12-17(Notes: K. Venkatram)                                                                                            | 33             |
|           | 12.1 Generalized Complex Structures and Topological Obstructions                                                              | 33             |
|           | 12.1.1 Z-grading on spinors                                                                                                   | 35             |
|           | 12.1.2 Complex Case                                                                                                           | 36             |
|           | 12.1.3 Symplectic Case                                                                                                        | 37             |
|           | 12.2 Intermediate Cases                                                                                                       | 38             |
|           | 12.2.1 Complex and Symplectic Decompositions                                                                                  | 38             |
|           | 12.2.2 General case                                                                                                           | 38             |
|           | 12.2.3 Weinstein Splitting                                                                                                    | 39             |
|           | 12.2.4 Examples of type jumping                                                                                               | 40             |
|           | 12.3 Spinorial Description                                                                                                    | 40             |
|           | 12.3.1 More Examples of Type Jumping                                                                                          | 42             |
|           | 12.3.2 Interpolation                                                                                                          | 42             |
|           | 12.3.3 Intermediate Types                                                                                                     | 43             |
|           | 12.3.4 Generalized K ahler Geometry                                                                                           | 44             |
|           | 12.3.4 Generalized Kamer Geometry                                                                                             | $44 \\ 45$     |
|           |                                                                                                                               |                |
|           | 12.4.1 Condition on Types                                                                                                     | 45             |
|           | 12.4.2 Integrability                                                                                                          | 46             |
| <b>13</b> | Lecture 18 (Notes: K. Venkatram)                                                                                              | 47             |
|           | 13.1 Generalized K ahler Geometry                                                                                             |                |
|           | 13.1.1 Integrability                                                                                                          | 47             |
| 14        | Lecture 19 (Notes: K. Venkatram)                                                                                              | <b>49</b>      |
|           | 14.1 Generalized K ahler Geometry                                                                                             |                |
|           | 14.2 Hodge Theory on Generalized K ahler Manifolds                                                                            | 50             |
| <b>15</b> | Lecture 20 (Notes: K. Venkatram)                                                                                              | 51             |
|           | 15.1 Generalized Complex Branes (of rank 1)                                                                                   | 51             |
|           | 15.1.1 General Properties of Generalized Complex Branes                                                                       | 52             |
|           | 15.1.2 Branes for Other Generalized Complex Manifolds                                                                         | 53             |
| 16        | Lecture 21-23 (Notes: K. Venkatram)                                                                                           | 53             |
|           | 16.1 Linear Algebra                                                                                                           | 53             |
|           | 16.1.1 Doubling Functor                                                                                                       | 54             |
|           | 16.1.2 Maps Induced by Morphisms                                                                                              | 54             |
|           | 16.1.3 Factorization of Morphisms $L: \mathcal{D}V \to \mathcal{D}(W)$                                                        | 54             |
|           | 16.9 T-duality                                                                                                                | 5/             |

## 1 Lecture 1 (Notes: K. Venkatram)

#### 1.1 Smooth Manifolds

Let M be a f.d.  $C^{\infty}$  manifold, and  $C^{\infty}(M)$  the algebra of smooth  $\mathbb{R}$ -valued functions. Let T = TM be the tangent bundle of M: then  $C^{\infty}(T)$  is the set of derivations  $\operatorname{Der}(C^{\infty}(M))$ , i.e. the set of morphisms  $X \in \operatorname{End}(C^{\infty}(M))$  s.t. X(fg) = (Xf)g + f(Xg). Then  $C^{\infty}(T)$  is equilled with a Lie bracket [,] via the commutator [X,Y]f = XYf - YXf.

**Note.** Explicitly, [X, Y] can be obtained as  $\lim_{t\to 0} \frac{Y-\operatorname{Fl}_X^t Y}{t}$ , where  $\operatorname{Fl}_X^t \in \operatorname{Diff}(M)$  is the flow of the vector field on M.

**Definition 1.** The exterior derivative is the mapping

$$d: C^{\infty}\left(\bigwedge^{k} T^{*}\right) \to C^{\infty}\left(\bigwedge^{k+1} T^{*}\right)$$

$$p \mapsto \left[ (X_{0}, \dots, X_{k}) \mapsto \sum_{i} (-1)^{i} X_{i} p(X_{0}, \dots, \hat{X}_{i}, \dots, X_{k}) + \sum_{i < j} (-1)^{i+j} p([X_{i}, X_{j}], X_{0}, \dots, \hat{X}_{i}, \dots, \hat{X}_{j}, \dots, X_{k}) \right]$$

$$(1)$$

Since [,] satisfies the Jacobi identity,  $d^2 = 0$ , i.e.

$$\cdots \to C^{\infty} \left( \bigwedge^{k-1} T^* \right) \xrightarrow{d} C^{\infty} \left( \bigwedge^k T^* \right) \xrightarrow{d} C^{\infty} \left( \bigwedge^{k+1} T^* \right) \to \cdots$$
 (2)

is a differential complex of first-order differential operators. Set  $\Omega^k(M) = C^{\infty}(\bigwedge^k T^*)$ . Letting  $m_f = \{g \mapsto fg\}$  denote multiplication by f, one finds that  $[d, m_f]\rho = df \wedge \rho$ , thus obtaining a sequence of symbols

$$\bigwedge^{k-1} T^* \xrightarrow{\eta \wedge \cdot} \bigwedge^k T^* \xrightarrow{\eta \wedge \cdot} \bigwedge^{k+1} T^* \tag{3}$$

which is exact for any nonzero 1-form  $\eta \in C^{\infty}(T^*)$ . Thus,  $\Omega^*$  is an *elliptic complex*. In particular, if M is compact,  $H^*(M) = \frac{\text{Ker } d|_{\Omega^*}}{\text{Im } d|_{\Omega^{*-1}}}$  is finite dimensional.

**Remark.** d has the property  $d(\alpha \wedge \beta) = d\alpha \wedge d\beta + (-1)^{\text{deg }\alpha} \alpha \wedge d\beta$ . Thus,  $(\Omega^{\bullet}(M), d, \wedge)$  is a differential graded algebra, and  $H^{\bullet}(M) = \bigoplus H^k(M)$  has a ring structure (called the *de Rham cohomology ring*).

We would like to express [X,Y] in terms of d. Now, a vector field  $X \in C^{\infty}(T)$  determines a derivation

$$i_X: \Omega^k(M) \to \Omega^{k-1}(M), \rho \mapsto [(Y_1, \dots, Y_k) \mapsto \rho(X, Y_1, \dots, Y_k)]$$
 (4)

of  $\Omega^*(M)$ .  $i_X$  has degree -1 and order 0.

**Definition 2.** The Lie derivative of a vector field X is  $L_X = [i_X, d]$ .

Note that this map has order 1 and degree 0.

**Theorem 1** (Cartan's formula).  $i_{[X,Y]} = [[i_X,d],i_Y]$ 

One thus obtains [,] as the *derived bracket of d*. See Kosmann-Schwarzbach's "Derived Brackets" for more information.

**Problem.** Classify all derivations of  $\Omega^{\bullet}(M)$ , and show that the set of such derivations has the structure of a  $\mathbb{Z}$ -graded Lie algebra.

One can extend the Lie bracket [,] on vector fields to an operator on all  $C^{\infty}(\bigwedge^k T)$ .

**Definition 3.** The Shouten bracket is the mapping

$$[,]: C^{\infty}\left(\bigwedge^{p} T\right) \times C^{\infty}\left(\bigwedge^{q} T\right) \to C^{\infty}\left(\bigwedge^{p+q-1} T\right)$$

$$(X_{1} \wedge \dots \wedge X_{p}, Y_{1} \wedge \dots \wedge Y_{q}) \mapsto \sum_{i} (-1)^{i+j} [X_{i}, Y_{i}] \wedge X_{1} \wedge \dots \wedge \hat{X}_{i} \wedge \dots \wedge X_{p} \wedge Y_{1} \wedge \dots \wedge \hat{Y}_{j} \wedge \dots \wedge Y_{q}$$

$$(5)$$

with the additional properties [X,f]=-[f,X]=X(f) and  $[f,g]=0 \forall f,g\in C^{\infty}(M)$ .

Note the following properties:

- $[P,Q] = -(-1)^{(\text{deg }P-1)(\text{deg }Q-1)}[Q,P]$
- $[P, Q \wedge R] = [P, Q] \wedge R + (-1)^{(\text{deg } P-1)\text{deg } Q} Q \wedge [P, R]$
- $[P, [Q, R]] = [[P, Q], R] + (-1)^{(\text{deg } P-1)(\text{deg } Q-1)}[Q, [P, R]]$

Thus, we find that  $C^{\infty}(\bigwedge T)$  has two operations: a wedge product  $\wedge$ , giving it the structure of a graded commutative algebra, and a bracket [,], giving it the structure of the Lie algebra. The above properties imply that it is a *Gerstenhaber algebra*.

Finally, for  $P = X_1 \wedge \cdots \wedge X_p$ , define  $i_p = i_{X_1} \circ \cdots \circ i_{X_p}$ . Note that it is a map of degree -p

**Problem.** Show that  $[[i_P,d]i_Q]=(-1)^{(\deg P-1)(\deg Q-1)}i_{[P,O]}$ .

#### 1.2 Geometry of Foliations

Let  $\Delta \subset T$  be subbundle of the tangent bundle (distribution) with constant rank k.

**Definition 4.** An integrating foliation is a decomposition  $M = \bigsqcup S$  of M into "leaves" which are locally embedded submanifolds with  $TS = \Delta$ .

Note that such leaves all have dimension k.

**Theorem 2** (Frobenius). An integrating foliation exists  $\Leftrightarrow \Delta$  is involutive, i.e.  $[\Delta, \Delta] \subset [\Delta]$ .

A distribution is equivallently determined by Ann  $\Delta \subset T^*$  or the line det Ann  $\Delta \subset \Omega^{n-k}(M)$ . That is, for locally-defined 1-forms  $(\theta_1, \dots, \theta_{n-k})$  s.t.  $\Delta = \bigcap_i \operatorname{Ker} \theta_i$ ,  $\Omega = \theta_1 \wedge \dots \wedge \theta_k$  generates a line bundle. If  $\Delta$  is involutive,  $i_X i_Y d\Omega = [[i_X, d], i_Y]\Omega = i_{[X,Y]}\Omega = 0$  for all X, Y s.t.  $i_X \Omega = i_Y \Omega = 0$ . That is,  $d\Omega = \eta \wedge \Omega$  for some 1-form  $\eta \in \Omega$ .

**Remark.** More generally, let  $\Delta \subset T$  be a distribution on non-constant rank spanned by an nvolutive  $C^{\infty}(M)$  module  $\mathcal{D} \subset C^{\infty}(T)$  at each point. Sussmann showed that such a  $\mathcal{D}$  gives M as a disjoint union of locally embedding leaves S with  $TS = \Delta$  everywhere.

### 1.3 Symplectic Structure

**Definition 5.** An symplectic structure on M is a closed, non-degenerate two-form  $\omega: T \to T^*$ .

Let  $(M, \omega)$  be a symplectic manifold: note that det  $\omega \in \det T^* \otimes \det T^*$ .

**Problem.** Show that det  $\omega = \operatorname{Pf} \omega \otimes \operatorname{Pf} \omega$ , where Pf is the *Pfaffian*.

**Theorem 3** (Darboux). Locally,  $\exists C^{\infty}$  functions  $p_1, \ldots, p_n, q_1, \ldots, q_n$  s.t.  $\{dp_i, dq_i\}$  span  $T^*$  and  $\omega = \sum dp_i \wedge dq_i$ . That is,  $(M, \omega)$  is locally diffeomorphic to  $(\mathbb{R}^{2n}, \sum dx_i \wedge dy_i)$ .

Moreover, by Stokes' theorem, one finds that  $\int_M \omega \wedge \cdots \wedge \omega \neq 0 \implies [\omega]^i \neq 0$  for all i.

Corollary 1. Neither  $S^4$  nor  $S^1 \times S^3$  have a symplectic structure.

## 2 Lecture 2 (Notes: A. Rita)

### 2.1 Comments on previous lecture

(0) The Poincaré lemma implies that the sequence

$$\ldots \longrightarrow C^{\infty}(\wedge^{k-1}T^*) \xrightarrow{d} C^{\infty}(\wedge^kT^*) \xrightarrow{d} C^{\infty}(\wedge^{k+1}T^*) \longrightarrow \ldots$$

is an exact sequence of sheaves, even though it is not an exact sequence of vector spaces.

(1) We defined the Lie derivative of a vector field X to be  $L_X = [\iota_X, d]$ . Since  $\iota_X \in \mathrm{Der}^{-1}(\Omega^{\cdot}(M))$  and  $d \in \mathrm{Der}^{+1}(\Omega^{\cdot}(M))$ , we have

$$[\iota_X, d] = \iota_X d - (-1)^{(1)\cdot(-1)} d\iota_X = \iota_X d + d\iota_X$$

(2)  $\omega: V \longrightarrow V^*$ ,  $\omega^* = -\omega$  If  $\omega$  is an isomorphism, then for any  $X \in V$  we have  $\omega(X, X) = 0$ , so that

$$X \in X^{\omega} = \operatorname{Ker} \omega(X) = \omega^{-1} \operatorname{Ann} X$$

Thus, we have an isomorphism  $\omega^*:X^\omega/\left\langle X\right\rangle\stackrel{\cong}{\longrightarrow} \operatorname{Ann}\,X/\left\langle \omega X\right\rangle$  and

$$\frac{\operatorname{Ann} X}{\langle \omega X \rangle} = \frac{\langle X \rangle^*}{(X^{\omega})^*} = \left(\frac{X^{\omega}}{\langle X \rangle}\right)^*$$

Then using induction, we can prove that V must be even dimensional.

### 2.2 Symplectic Manifolds

(continues the previous lecture)

For a manifold M, consider its cotangent bundle  $T^*M$  equipped with the 2-form  $\omega = d\theta$ , where  $\theta \in \Omega^1(T^*M)$  is such that  $\theta_\alpha(v) = \alpha(\pi_*(v))$ . In coordinates  $(x^1, \dots, x^n, a_1, \dots, a_n)$ , we have  $\theta = \sum_i a_i dx^i$  and therefore  $d\theta = \sum_i da_i \wedge dx^i$ , as in the Darboux theorem. Thus,  $T^*M$  is symplectic.

**Definition 6.** A subspace W of a symplectic 2n-dimensional vector space  $(V, \omega)$  is called isotropic if  $\omega|_W = 0$ 

W is called coisotropic if its  $\omega$ -perpendicular subspace  $W^{\omega}$  is isotropic.

W is called Lagrangian if it is both isotropic and coisotropic.

There exist isotropic subspaces of any dimension  $0, 1, \ldots, n$ , and coisotropic subspaces of any dimension  $n, n+1, \ldots, 2n$ . Hence, Lagragian subspaces must be of dimension n.

We have analogous definitions for submanifolds of a symplectic manifold  $(M, \omega)$ :

**Definition 7.**  $L \stackrel{f}{\hookrightarrow} (M, \omega)$  is called isotropic if  $f^*\omega = 0$ . When dim(L) = n it is called Lagrangian.

The graph of  $0 \in C^{\infty}(M, T^*M)$ , which is the zero section of  $T^*M$ , is Lagrangian.

More generally,  $\Gamma_{\xi}$ , the graph of  $\xi \in C^{\infty}(M, T^*M)$  is a Lagrangian submanifold of  $T^*M$  if and only if  $d\xi = 0$ . It is in this sense that we say that Lagrangian submanifolds of  $T^*M$  are like generalized functions:  $f \in C^{\infty}(M)$  gives rise to df, which is a closed 1-form, so  $\Gamma_{df} \subset T^*M$  is Lagrangian.

**Proposition 1.** Suppose we have a diffeomorphism between two symplectic manifolds,  $\varphi:(M_0,\omega_0)\to (M_1,\omega_1)$  and let  $\pi_i:M_0\times M_1\to M_i,\ i=0,1$  be the projection maps.

Then,  $Graph(\varphi) \subset (M_0 \times M_1, \pi_0^* \omega_0 - \pi_1^* \omega_1)$  is Lagrangian if and only if  $\varphi$  is a symplectomorphism.

### 2.3 Poisson geometry

**Definition 8.** A Poisson structure on a manifold M is a section  $\pi \in C^{\infty}(\wedge^2(TM))$  such that  $[\pi, \pi] = 0$ , where  $[\cdot, \cdot]$  is the Shouten bracket.

**Remark.**  $[\pi,\pi] \in C^{\infty}(\wedge^3(TM))$ , so for a surface  $\Sigma^{(2)}$ , all  $\pi \in C^{\infty}(\wedge^2(TM))$  are Poisson.

This defines a bracket on functions, called the Poisson bracket:

**Definition 9.** The Poisson bracket of two functions  $f, g \in C^{\infty}(\wedge^{0}(TM))$  is

$$\{f,g\} = \pi(df,dg) = \iota(df \wedge dg) = [[\pi,f],g]$$

**Proposition 2.** The triple  $(C^{\infty}(M), \cdot, \{,\})$  is a Poisson algebra, i.e., it satisfies the properties below. For  $f, g, h \in C^{\infty}(\wedge^0(TM))$ ,

- Leibniz rule  $\{f, gh\} = \{f, g\} h + g \{f, h\}$
- Jacobi identity:  $\{f, \{g, h\}\} + \{g, \{h, f\}\} + \{h, \{f, g\}\} = 0$

**Problem.** Write  $\{f,g\}$  in coordinates for  $\pi=\pi^{ij}\frac{\partial}{\partial x^i}\wedge\frac{\partial}{\partial x^j}$ .

A basic example of a Poisson structure is given by  $\omega^{-1}$ , where  $\omega$  is a symplectic form on M, since

$$\left[\omega^{-1}, \omega^{-1}\right] = 0 \Leftrightarrow d\omega = 0 \tag{6}$$

**Problem.** Prove (6) by testing  $d\omega(X_f, X_g, X_h)$ , for  $f, g, h \in C^{\infty}(M)$ .

Poisson manifolds are of interest in physics: given a function  $H \in C^{\infty}(M)$  on a Poisson manifold  $(M, \pi)$ , we get a unique vector field  $X_H = \pi(dH)$  and its flow  $Fl_{X_H}^t$ . H is called Hamiltonian, and we usually think about it as energy.

We have  $X_H(H) = \pi(dH, dH) = 0$ , so H is preserved by the flow. What other functions  $f \in C^{\infty}(M)$  are preserved by the flow? A function  $f \in C^{\infty}(M)$  is conserved by the flow if and only if  $X_H(f) = 0$ , equivalently  $\{H, f\} = 0$ , f commutes with the Hamiltonian.

If we can find k conserved quantities,  $H_0 = H, H_1, H_2, \ldots, H_k$  such that  $\{H_0, H_i\} = 0$ , then the system must remain on a level surface  $Z = \{x : (H_0, \ldots, H_k) = \vec{c}\}$  for all time. Moreover, if  $\{H_i, H_j\}$  for all i, j then we get commutative flows  $Fl_{X_{H_i}}^t$ . If Z is compact, connected, and k = n, then Z is a torus  $\mathbb{T}^n$ , and the trajectory is a straight line in these coordinates. Also,  $\mathbb{T}^n$  is Lagrangian.

**Problem.** Describe the Hamiltonian flow on  $T^*M$  for  $H = \pi^*f$ , with  $f \in C^{\infty}(M)$  and  $\pi : T^*M \to M$ . Show that a coordinate patch for M gives a natural system of n commuting Hamiltonians.

Let us now think about a Poisson structure,  $\pi: T^* \to T$  and consider  $\Delta = \text{Im}\pi$ .  $\Delta$  is spanned at each point x by  $\pi(df) = X_f$ , Hamiltonian vector fields. The Poisson tensor is always preserved:

$$L_{X_f}\pi = [\pi, X_f] = [\pi, [\pi, f]] = [[\pi, \pi], f] + (-1)^{1 \cdot 1} [\pi, [\pi, f]] = -[\pi, [\pi, f]]$$

$$\Longrightarrow L_{X_f}\pi = 0$$

If  $\Delta_{x_0} = \langle X_{f_1}, \dots, X_{f_k} \rangle$ , then  $Fl_{X_1}^{t_1} \circ \dots \circ Fl_{X_k}^{t_k}(x_0)$  sweeps out  $S \ni x_0$  submanifold of M such that  $TS = \Delta$ .

**Example** (of a generalized Poisson structure). Let  $M = \mathfrak{g}^*$ , for  $\mathfrak{g}$  a Lie algebra,  $[\cdot, \cdot] \in \wedge^2 \mathfrak{g}^* \otimes \mathfrak{g}$ . Then  $TM = M \times \mathfrak{g}^*$  and  $T^*M = M \times \mathfrak{g}$ , and also  $\wedge^2(TM) = M \times \wedge^2 \mathfrak{g}$ , so  $[\cdot, \cdot] \in C^{\infty}(\wedge^2 T\mathfrak{g}^*)$ .

Given  $f_1, f_2 \in C^{\infty}(M)$ , their Poisson bracket is given by  $\{f_1, f_2\}(x) = \langle [df_1, df_2], x \rangle$ .

For  $f, g \in \mathfrak{g}$  linear functions on M, we have

$$X_f(g) = \langle [f, g], x \rangle = \langle \operatorname{ad}_f g, x \rangle = \langle g, -\operatorname{ad}_f^* x \rangle$$

Thus  $X_f = -\mathrm{ad}_f^*$ , so the the leaves of  $\Delta = \mathrm{Im}\pi$  are coadjoint orbits. If S is a leaf, then

$$0 \longrightarrow N_S^* \longrightarrow T^*|_S \stackrel{\pi}{\longrightarrow} T|_S \longrightarrow 0$$

is a short exact sequence and we have an isomorphism  $\pi_*: T^*S = \frac{T^*|_S}{N^*S} \xrightarrow{\cong} TS$ , which implies that the leaf S is symplectic.

Given  $f, g \in C^{\infty}(S)$ , we can extend them to  $\tilde{f}, \tilde{g} \in C^{\infty}(M)$ . The Poisson bracket  $\left\{\tilde{f}, \tilde{g}\right\}_{\pi}$  is independent of choice of  $\tilde{f}, \tilde{g}$ , so  $\{f, g\}_{\pi_*} = \left\{\tilde{f}, \tilde{g}\right\}_{\pi}$  is well defined.

Therefore, giving a Poisson structure on a manifold is the same as giving a "generalized" folliation with symplectic leaves.

When  $\pi$  is Poisson,  $[\pi, \pi] = 0$ , we can define

$$d_{\pi} = [\pi, \cdot] : C^{\infty}(\wedge^k T) \to C^{\infty}(\wedge^{k+1} T)$$

Note that  $[\pi,\cdot]$  is of degree (2-1), so it makes sense to cal it  $d_{\pi}$ . Also,

$$d_{\pi}^{2}(A) = [\pi, [\pi, A]] = [[\pi, \pi], A] - [\pi, [\pi, A]] = -[\pi, [\pi, A]]$$

$$\implies d_{\pi}^{2} = 0$$

Thus, we have a chain complex

$$\ldots \longrightarrow C^{\infty}(\wedge^{k-1}T) \xrightarrow{d_{\pi}} C^{\infty}(\wedge^{k}T) \xrightarrow{d_{\pi}} C^{\infty}(\wedge^{k+1}T) \longrightarrow \ldots$$

Moreover, if  $m_f$  denotes multiplication by  $f \in C^{\infty}(M)$ ,

$$[d_{\pi}, m_f] \psi = d_{\pi}(f\psi) - f d_{\pi}\psi = [\pi, f\psi] - f[\pi, \psi] = [\pi, f] \wedge \psi = \iota_{df}\pi \wedge \psi$$

But for any  $\xi \in T^*$ ,  $\xi \neq 0$ ,  $(\iota_{\xi}\pi) \wedge : \wedge^k T \to \wedge^{k+1} T$  is exact only for  $\iota_{\xi}\pi \neq 0$ . So, if  $\pi$  is not invertible,  $d_{\pi}$  is not an elliptic complex, and the Poisson cohomology groups,  $H_{\pi}^k(M) = \text{Ker } d_{\pi}|_{\wedge^k T}/\text{Im } d_{\pi}|_{\wedge^{k-1} T}$  could be infinite dimensional on a compact M.

Let us look at the first such groups:

$$H_{\pi}^0(M)=\{f:d_{\pi}f=0\}=\{f:X_f=0\}=\{\text{Casimir functions, i.e. functions s.t.}\ \{f,g\}=0 \text{ for all } g\}$$

$$H_{\pi}^{1}(M) = \{X : d_{\pi}X = 0\} / \text{Im } d_{\pi} = \{\text{infinitesimal symmetries of Poisson vector fields} \} / \text{Hamiltonians}$$

$$H_{\pi}^2(M) = \{P \in C^{\infty}(\wedge^2 T) : [\pi, P] = 0\} = \text{tangent space to the moduli space of Poisson structures}$$

## 3 Lecture 3 (Notes: J. Bernstein)

## 3.1 Almost Complex Structure

Let  $J \in \mathbb{C}^{\infty}(\operatorname{End}(T))$  be such that  $J^2 = -1$ . Such a J is called an almost complex structure and makes the real tangent bundle into a complex vector bundle via declaring iv = J(v). In particular dim  $\mathbb{R}M = 2n$ . This also tells us that the structure group of the tangent bundle reduces from  $Gl(2n, \mathbb{R})$  to  $Gl(n, \mathbb{C})$ . Thus T is an associated bundle to a principal  $Gl(n, \mathbb{C})$  bundle. In particular we have map on the cohomology,

$$H^{2i}(M,\mathbb{Z}) \rightarrow H^{2i}(M,\mathbb{Z}/2\mathbb{Z})$$
  
 $c(T,J) \mapsto w(T)$ 

Where c(T, J) are the *Chern classes* of T (with complex structure given by J) and w(T) are the *Stiefel-Whitney classes*. Here the map is reduction mod 2. In particular  $w_{2i+1} = 0$  and  $c_1 \mapsto w_2$ , the later fact implies that M is  $Spin^c$ .

Recall that the *Pontryagin classes* of a vector bundle are  $p_i \in H^{4i}$  such that  $p_i(E) = (-1)^i c_{2i}(E \otimes \mathbb{C})$ . We study  $p_i(T) = (-1)^i c_{2i}(T \otimes \mathbb{C})$ . Since the eigenvalues of  $J: T \to T$  are  $\pm i$  we have the natural decomposition

$$T \otimes \mathbb{C} = (\text{Ker } (J-i)) \oplus (\text{Ker } (J+i)) = T_{1,0} \oplus T_{0,1}$$

Here  $T_{1,0}$  and  $T_{0,1}$  are complex subbundles of  $T \otimes \mathbb{C}$  and on has the identifications  $(T_{1,0},i) \cong (T,J)$  and  $(T_{0,1},i) \cong (T,-J)$ . Hence if we choose a hermitian metric h on T we get a non degenerate pairing,

$$T_{1,0} \times T_{0,1} \to \mathbb{C}$$

and hence  $T_{1,0} \cong (T_{0,1})^*$ . We now compute

$$\sum_{k} (-1)^{k} p_{k}(T) = \sum_{k} c_{2k}(T_{1,0} \oplus T_{0,1}) = \sum_{k} \sum_{i} c_{i}(T_{1,0}) \cup c_{2k-i}(T_{0,1}) = (\sum_{i} c_{i}(T_{1,0})) \cup (\sum_{i} c_{j}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{i}(T_{0,1})) \cup (\sum_{i} c_{$$

where the last equality comes from rearranging the sum. Now we have  $c_i(T_{0,1}) = (-1)^i c_i(T_{1,0})$  and since we can identity  $T_{1,0}$  with (T,J) we have

$$\sum_{k} (-1)^{k} p_{k}(T) = (\sum_{i} c_{i}(T, J)) \cup (\sum_{j} (-1)^{j} c_{j}(T, J))$$

Thus the existence of an almost complex structure implies that one can find classes  $c_i \in H^{2i}(M,\mathbb{Z})$  that when taken mod 2 give the Stiefel-Whitney class and that satisfy the above Pontryagin relation.

**Problem.** Show that  $S^{4k}$  does not admit an almost complex structure.

Remark. Topological obstructions to the existence of an almost complex structure in general are not known.

#### 3.2 Hermitian Structure

**Definition 10.** A hermitian structure or a real vector space V consists of a triple

- J an almost complex structure
- $\omega: V \to V^* \ \omega \ symplectic \ (i.e. \ \omega^* = -\omega)$
- $g: V \to V^*$  g a metric (i.e.  $g^* = g$  and if we write  $x \mapsto g(x, \cdot)$  then g(x, x) > 0 for  $x \neq 0$ )

with the compatibility

$$g \circ J = \omega$$

Now pick (J,g) this determines a hermitian structure if and only if

$$-(gJ) = (gJ)^* = J^*g^* = J^*g$$

. On the other hand  $(J,\omega)$  determines a hermitian structure if and only if

$$-(\omega J) = (\omega J^{-1})^* = -J^* \omega^* = J^* \omega$$

that is if and only if  $J^*\omega + \omega J = 0$ . Then we have  $(J^*\omega + \omega J)(v)(w) = \omega(Jx,y) + \omega(x,Jy) = 0$  which is equivalent to  $\omega$  of type (1,1). We get three structure groups

$$g \mapsto O(V,g) = \{A : A^*gA = g\}$$
  
$$\omega \mapsto Sp(V,\omega) = \{A^*\omega A = \omega\}$$
  
$$J \mapsto Gl(V,J) = \{A : AJ = JA\}$$

Now if we form  $h = g + i\omega$  we obtain a hermitian metric on V. And we have structure group

$$\mathrm{Stab}(h) = U(V,h) = O(v,h) \cap Sp(V,\omega) = Gl(V,J) \cap O(V,g) = Sp(V,\omega) \cap Gl(V,J)$$

we note U(V, h) is the maximal compact subgroup of Gl(V, J).

**Problem.** 1. Show Explicitly that given J one can always find a compatible  $\omega$  (or g) 2. Show similarly that given  $\omega$  can find compatible g.

#### 3.3 Integrability of J

Since we have a Lie bracket on T we can tensor it with  $\mathbb C$  and obtain a Lie bracket on  $T\otimes \mathbb C$ . The since  $T\otimes \mathbb C=T_{1,0}\oplus T_{0,1}$ , integrability conditions are thus that the complex distribution  $T_{1,0}$  is involutive i.e.  $[T_{1,0},T_{1,0}]\subseteq T_{1,0}$ . How far is this geometry from usual complex structure on  $\mathbb C^n$ ? Idea is if one can form  $M^{\mathbb C}$  the complexification of M (think of  $\mathbb RP^n\subset \mathbb CP^n$  or  $\mathbb R^n\subset \mathbb C^n$ , indeed if M is real analytic it is always possible to do this. Then  $M^{\mathbb C}$  has two transverse foliations by the integrability condition (from  $T_{1,0}$  and  $T_{0,1}$ ). Say functions  $z^i:M^{\mathbb C}\to \mathbb C$  cut out the leaves of  $T_{1,0}$  (i.e. the leaves are given by  $z^1=z^2=\ldots=z^n=c$ ). Then when one restricts the  $z^ii$  to a neighborhood  $U\subseteq M$ , obtains maps  $z^1,\ldots,z^n:U\to \mathbb C$  such that  $< dz^1,\ldots,dz^n>=T_{1,0}^*=Ann(T_{0,1})$ . That is one obtains a holomorphic coordinate chart. Moreover in this chart one has

$$J = \sum_{k} i(dz^{k} \otimes \frac{\partial}{\partial z^{k}} + d\overline{z}^{k} \otimes \frac{\partial}{\partial \overline{z}^{k}})$$

**Remark.** This is similar to the Darboux theorem of symplectic geometry

More generally we have

**Theorem 4.** (Newlander-Nirenberg) If M is a smooth manifold with smooth almost complex structure J that is integrable then M is actually complex.

**Note.** This was most recently treated by Malgrange.

Now  $T_{1,0}$  closed under [,] happens if and only if for  $X \in T, X - iJX \in T_{1,0}$  one has [X - iJX, Y - iJY] = Z - iJZ. That is [X, Y] - [JX, JY] + J[X, JY] + J[JX, Y] = 0

**Definition 11.** We define the Nijenhuis tensor as  $N_J(X,Y) = [X,Y] - [JX,JY] + J[X,JY] + J[JX,Y]$ 

**Problem.** Show that  $N_J$  is a tensor in  $C^{\infty}(\bigwedge^2 T^* \otimes T)$ .

Thus one has J integrable if and only if  $N_J = 0$ .

**Remark.**  $N_J=0$  is the analog of  $d\omega \in C^{\infty}(\bigwedge^3 T^*)$ 

Now if we view  $J \in \text{End}(T) = \Omega^1(T) = \sum \xi^i \otimes \nu_i$  then J acts on differential forms,  $\rho \in \Omega^{\cdot}(M)$  by  $i_J(\rho) = \sum \xi^i \wedge i_{v_i} \rho = \sum (e_{\xi^i} \cdot i_{v_i}) \rho$ . And one computes

$$i_J(\alpha \wedge \beta) = i_J(\alpha) \wedge \beta + (-1)^{\alpha} \alpha \wedge i_J \beta$$

thus  $i_J \in \operatorname{Der}^0(\Omega^{\cdot}(M))$  and we may form  $L_J = [i_J, d] \in \operatorname{Der}^1(\Omega^{\cdot}(M))$ .

**Note.**  $L_J$  is denoted  $d^c$ 

**Definition 12.** We define the Nijenhuis bracket  $[,]: \Omega^k \times \Omega^l \to \Omega^{k+l}$  by  $L_{[J,K]} = [L_J, L_K]$ 

One checks  $[L_J, L_J] = L_{N_J}$  hence  $N_J = [J, J]$ .

## 3.4 Forms on a Complex Manifold

In a manner similar with our treatment of foliations, we wish to express integrability in terms of differentiable forms. Let  $T_{0,1}$  (or  $T_{1,0}$ ) be closed under the complexified Lie bracket. Since Ann  $T_{0,1} = T_{1,0}^* = \langle \theta^1, \dots, \theta^n \rangle$  (Ann  $T_{1,0} = T_{1,0}^*$ ),  $\Omega = \theta^1 \wedge \dots \theta^n$  is a generator for det  $T_{1,0}^* = K$ . Where here K is a complex line bundle. The condition for integrability is then  $d\Omega^{n,0} = \xi^{0,1} \wedge \Omega^{n,0}$  for some  $\xi$ . Taking d again one obtains  $0 = d\xi \wedge \Omega^{n,0} - \xi \wedge d\Omega = d\xi \wedge \Omega$ , hence  $\overline{\partial} \xi = 0$ . We call  $K = \bigwedge^n T_{1,0}^*$  the canonical bundle.

**Note.** This definition is deserved since  $K \subset \bigwedge T^* \otimes \mathbb{C}$  and  $T_{0,1} = AnnK = \{X \imath_X \Omega = 0\}$ , i.e. we can recover the complex structure from K

More fully, there is a decomposition of forms

$$\bigwedge^{\cdot} T^* \otimes \mathbb{C} = \bigoplus_{p,q} \left( \bigwedge^{p} T_{1,0}^* \bigotimes \bigwedge^{q} T_{0,1}^* \right)$$

$$\Omega^{\cdot} = \bigoplus_{p,q} \Omega^{p,q}(M)$$

that is a  $\mathbb{Z} \times \mathbb{Z}$  grading.

Since  $d\Omega^{n,0} = \xi \wedge \Omega$  we have integrability if and only if  $d = \partial + \overline{\partial}$ , where here  $\partial = \pi_{p,q+1} \circ d$  and  $\overline{\partial} = \pi_{p+1,q} \circ d$ .

**Problem.** Show that without integrability

$$d = \partial + \overline{\partial} + d^N$$

where  $N_J \in \wedge^2 T^* \otimes T$  and  $d^N = i_{N_J}$ . Also determine the p, q decomposition of  $d^N$ .

#### 3.5 Dolbeault Cohomology

Assuming  $N_J = 0$  one has  $\partial^2 = \overline{\partial}^2 = \partial \overline{\partial} + \overline{\partial} \partial = 0$ . Thus one gets a complex

$$\overline{\partial}: \Omega^{p,q}(M) \to \Omega^{p,q+1}(M).$$

The cohomology of this complex is called the *Dolbeault cohomology* and is denoted

$$\frac{\operatorname{Ker} \, \overline{\partial}|_{\Omega^{p,q}}}{\operatorname{Im} \, \overline{\partial}|_{\Omega^{p,q-1}}} = H^{p,q}_{\overline{\partial}}(M).$$

This is a  $\mathbb{Z} \times \mathbb{Z}$  graded ring. The symbol of  $\overline{\partial}$  can be determined from the computation  $[\overline{\partial}, m_f] = e_{\overline{\partial}f}$ . Now given a real form  $\xi \in T^* - \{0\}$  then

$$\bigwedge^{p,q} T^* \to \bigwedge^{p,q+1} T^*$$

$$\rho \mapsto \xi^{0,1} \wedge \rho$$

is elliptic, since  $\xi = \xi^{1,0} + \xi^{0,1} = \xi^{1,0} + \overline{\xi^{0,1}}$  (as  $\xi$  real) and so  $\xi^{0,1} \neq 0$ . Hence dim  $H^{p,q}_{\overline{\partial}} < \infty$  on M compact. Now suppose  $E \to M$  is a complex vector bundle, how does pone make E compatible with the complex structure J on M?

**Definition 13.**  $E \to M$  a complex vector bundle is a holomorphic if there exists a connection  $\overline{\partial}_E : C^{\infty}(E) \to C^{\infty}(T_{0,1}^* \otimes E)$  which is flat (i.e.  $\overline{\partial}_E^2 = 0$ ).

This gives us a complex

$$C^{\infty}(T_{0,1}^* \otimes E) \to \ldots \to \Omega^{0,q}(E) = C^{\infty}(\wedge^{0,q}T^* \otimes E) \to \ldots$$

The cohomology of this complex is called *Dolbeault cohomology with values in E* and is denoted  $H^q_{\overline{\partial}_E}(M, E)$ . Elliptic theory tells us that M compact implies  $H^q_{\overline{\partial}_E}(M, E)$  is finite dimensional. We note that  $\overline{\partial}|_{\Omega^{n,0}}$  is a holomorphic structure on K and hence K is a holomorphic line bundle.

**Problem.** Find explicitly the  $\overline{\partial}_E$  operator on  $E = T_{1,0}$ 

## 4 Lecture 4 (Notes: J. Pascaleff)

## 4.1 Geometry of $V \oplus V^*$

Let V be an n-dimensional real vector space, and consider the direct sum  $V \oplus V^*$ . This space has a natural symmetric bilinear form, given by

$$\langle X + \xi, Y + \eta \rangle = \frac{1}{2} (\xi(Y) + \eta(X))$$

for  $X, Y \in V$ ,  $\xi, \eta \in V^*$ . Note that the subspaces V and  $V^*$  are null under this pairing. Choose a basis  $e_1, e_2, \ldots, e_n$  of V, and let  $e^1, e^2, \ldots, e^n$  be the dual basis for  $V^*$ . Then the collection

$$e_1 + e^1, e_2 + e^2, \dots, e_n + e^n, \quad e_1 - e^1, e_2 - e^2, \dots, e_n - e^n$$

is a basis for  $V \oplus V^*$ , and we have

$$\langle e_i + e^i, e_i + e^i \rangle = 1$$
  
 $\langle e_i - e^i, e_i - e^i \rangle = -1,$ 

whereas for  $i \neq j$ ,

$$\langle e_i \pm e^i, e_j \pm e^j \rangle = 0$$

Thus the pairing  $\langle \cdot, \cdot \rangle$  is non-degenerate with signature (n, n), a so-called "split signature." The symmetry group of the structure consisting of  $V \oplus V^*$  with the pairing  $\langle \cdot, \cdot \rangle$  is therefore

$$O(V \oplus V^*) = \{A \in GL(V \oplus V^*) : \langle A \cdot, A \cdot \rangle = \langle \cdot, \cdot \rangle\} \cong O(n, n).$$

Note that O(n, n) is not a compact group.

We have a natural orientation on  $V \oplus V^*$  coming from the canonical isomorphisms

$$\det (V \oplus V^*) = \det V \otimes \det V^* = \mathbf{R}.$$

The symmetry group of  $V \oplus V^*$  therefore naturally reduces to SO(n, n).

The Lie algebra of  $SO(V \oplus V^*)$  is

$$\mathfrak{so}(V \oplus V^*) = \{Q : \langle Q \cdot, \cdot \rangle + \langle \cdot, Q \cdot \rangle \}.$$

By way of the non-degenerate bilinear form on  $V \oplus V^*$ , we may identify  $V \oplus V^*$  with its dual, and so we may write

$$\mathfrak{so}(V \oplus V^*) = \{Q : Q + Q^* = 0\}.$$

We may decompose  $Q \in \mathfrak{so}(V \oplus V^*)$  in view of the splitting  $V \oplus V^*$ :

$$Q = \begin{pmatrix} A & \beta \\ B & D \end{pmatrix},$$

where

$$\begin{array}{ll} A:V\to V & \beta:V^*\to V \\ B:V\to V^* & D:V^*\to V^* \end{array}$$

The condition that  $Q + Q^* = 0$  means now

$$Q^* = \begin{pmatrix} D^* & \beta^* \\ B^* & A^* \end{pmatrix} = -Q,$$

or  $D^* = -A$ ,  $\beta^* = -\beta$ , and  $B^* = -B$ . The necessary and sufficient conditions that  $A, \beta, B, D$  give an element of  $\mathfrak{so}(V \oplus V^*)$  are therefore

$$A \in \text{End}V$$
,  $\beta \in \wedge^2 V$ ,  $B \in \wedge^2 V^*$ ,  $D = -A^*$ .

Thus we may identify  $\mathfrak{so}(V \oplus V^*)$  with

$$\operatorname{End}(V) \oplus \wedge^2 V \oplus \wedge^2 V^*$$
.

This decomposition is consistent with the fact that, for any vector space E with a non-degenerate symmetric bilinear form  $\langle \cdot, \cdot \rangle$ , we have

$$\mathfrak{so}(E) = \wedge^2 E$$
.

In the case of  $E = V \oplus V^*$  this gives

$$\mathfrak{so}(V \oplus V^*) = \wedge^2(V \oplus V^*) = \wedge^2V \oplus (V \otimes V^*) \oplus \wedge^2V^*,$$

and the term  $V \otimes V^*$  is just  $\operatorname{End}(V)$ .

Of particular note is the fact that the "usual" symmetries  $\operatorname{End}(V)$  of V are contained in the symmetries of  $V \oplus V^*$ . (Since V is merely a vector space with no additional structure, its symmetry group is  $\operatorname{GL}(V)$ , with Lie algebra  $\mathfrak{gl}(V) = \operatorname{End}(V)$ .)

Now we examine how the different parts of the decomposition

$$\mathfrak{so}(V \oplus V^*) = \operatorname{End}(V) \oplus \wedge^2 V \oplus \wedge^2 V^*$$

act on  $V \oplus V^*$ .

Any  $A \in \text{End}(V)$  corresponds to the element

$$Q_A = \begin{pmatrix} A & 0 \\ 0 & -A^* \end{pmatrix} \in \mathfrak{so}(V \oplus V^*).$$

Which acts on  $V \oplus V^*$  as the linear transformation

$$e^{Q_A} = \begin{pmatrix} e^A & 0 \\ 0 & ((e^A)^*)^{-1} \end{pmatrix} \in \operatorname{SO}(V \oplus V^*)$$

Since any transformation  $T \in GL^+(V)$  of positive determinant is  $e^A$  for some  $A \in End(V)$ . We can regard  $GL^+(V)$  as a subgroup of  $SO(V \oplus V^*)$ . In fact the map

$$P \mapsto \begin{pmatrix} P & 0 \\ 0 & (P^*)^{-1} \end{pmatrix}$$

gives an injection of GL(V) into  $SO(V \oplus V^*)$ .

Thus, once again, the usual symmetries GL(V) may be regarded as part of a larger group of symmetries, namely  $SO(V \oplus V^*)$ . This is the direct analog of the same fact at the level of Lie algebras.

Now consider a 2-form  $B \in \wedge^2 V^*$ . This element corresponds to

$$Q_B = \begin{pmatrix} 0 & 0 \\ B & 0 \end{pmatrix} \in \mathfrak{so}(V \oplus V^*),$$

which acts  $V \oplus V^*$  as the linear transformation

$$e^B = e^{Q_B} = \exp\begin{pmatrix} 0 & 0 \\ B & 0 \end{pmatrix} = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix} + \begin{pmatrix} 0 & 0 \\ B & 0 \end{pmatrix} + 0 = \begin{pmatrix} 1 & 0 \\ B & 1 \end{pmatrix},$$

since  $Q_B^2 = 0$ . More explicitly,  $e_B^Q$  is the map

$$\begin{pmatrix} X \\ \xi \end{pmatrix} \mapsto \begin{pmatrix} X \\ \xi + B(X) \end{pmatrix} = \begin{pmatrix} X \\ \xi + i_X B \end{pmatrix}.$$

Thus B gives rise to a shear transformation which preserves the projection onto V. These transformations are called B-fields.

The case of a bivector  $\beta \in \wedge^2 V$  is analogous to that of a 2-form:  $\beta$  corresponds to

$$Q_{\beta} = \begin{pmatrix} 0 & \beta \\ 0 & 0 \end{pmatrix}$$

which acts on  $V \oplus V^*$  as

$$e^{\beta} = e^{Q_{\beta}} = \begin{pmatrix} 1 & \beta \\ 0 & 1 \end{pmatrix} : \begin{pmatrix} X \\ \xi \end{pmatrix} \mapsto \begin{pmatrix} X + i_{\xi}\beta \\ \xi \end{pmatrix},$$

or in other words a shear transformation preserving projection onto  $V^*$ . These are called  $\beta$ -field transformations.

In summary, the natural structure of  $V \oplus V^*$  is such that we may regard three classes of objects defined on V, namely, endomorphisms, 2-forms, and bivectors, as orthogonal symmetries of  $V \oplus V^*$ .

#### 4.2 Linear Dirac structures

A subspace  $L \subset V \oplus V^*$  is called *isotropic* if

$$\langle x, y \rangle = 0$$
 for all  $x, y \in L$ .

If V has dimension n, then the maximal dimension of an isotropic subspace in  $V \oplus V^*$  is n. Isotropic subspaces of the maximal dimension are called *linear Dirac structures* on V.

Examples of linear Dirac structures on V are

- 1. *V*
- 2.  $V^*$ .
- 3.  $e^BV = \{X + i_X B : X \in V\}$ , which is simply the graph  $\Gamma_B$  of the map  $B : V \to V^*$ .
- 4.  $e^{\beta} \cdot V^* = \{i_{\xi}\beta + \xi : \xi \in V^*\}.$
- 5. In general,  $A \cdot V$ , where  $A \in O(V \oplus V^*)$ .

Exercise. If D is a linear Dirac structure on V, such that the projection onto to V,  $\pi_V(D) = V$ , then there is a unique  $B: V \to V^*$  such that  $D = e^B V$ . Specifically  $B = \pi_{V^*} \circ (\pi_V | D)^{-1}$ .

A further example of a linear Dirac structure is given as follows: let  $\Delta \subset V$  be any subspace of dimension d. Then the annihilator of  $\Delta$ ,  $\operatorname{Ann}(\Delta)$ , consisting of all 1-forms which vanish on  $\Delta$  is a subspace of  $V^*$  of dimension n-d. The space

$$D = \Delta \oplus \operatorname{Ann}(\Delta) \subset V \oplus V^*$$

is then isotropic of dimension n, and is hence a linear Dirac structure.

When we apply a B-field to a Dirac structure of this kind, we get

$$e^{B}(\Delta \oplus \text{Ann}(\Delta)) = \{X + \xi + i_{X}B : X \in \Delta, \xi \in \text{Ann}(\Delta)\}$$
$$= e^{B}(\Delta) \oplus \text{Ann}(\Delta).$$

We define the *type* of a Dirac structure D to be  $\operatorname{codim}(\pi_V(D))$ . The computation above shows that a B-field transformation cannot change the type of a Dirac structure.

What matters in this computation is not so much B itself as it is the pullback  $f^*B$  of B under the inclusion  $f: \Delta \to V$ . Indeed, if  $f^*B = f^*B'$ , then

$$0 = i_X(f^*B - f^*B') = f^*(i_XB - i_XB').$$

This means that  $i_X B - i_X B' \in \text{Ann}(\Delta)$ , and so

$$e^{B}(\Delta) \oplus \operatorname{Ann}(\Delta) = e^{B'}(\Delta) \oplus \operatorname{Ann}(\Delta).$$

Generalizing this observation, let  $f: E \to V$  be the inclusion of a subspace E of V, and let  $\epsilon \in \wedge^2 E^*$ . Then define

$$L(E,\epsilon) = \{X + \xi \in E \oplus V^* : f^*\xi = i_X \epsilon\},\$$

which is a linear Dirac structure. Note that when  $\epsilon = 0$ ,

$$L(E,0) = E \oplus \operatorname{Ann}(E).$$

Otherwise,  $L(E, \epsilon)$  is a general Dirac structure.

Conversely, the subspace E and 2-form  $\epsilon$  may be reconstructed from a given Dirac structure L. Set

$$E = \pi_V(L) \subset V$$
.

Then

$$L \cap V^* = \{\xi : \langle \xi, L \rangle = 0\}$$
$$= \{\xi : \xi(\pi_V(L)) = 0\}$$
$$= \operatorname{Ann}(E).$$

We can define a map from E to  $V^*/L \cap V^*$  by taking  $e \in E$  first to  $(\pi_V|L)^{-1}(e) \in L$ , and then projecting onto  $V^*/L \cap V^*$ ; this yields

$$\epsilon: E \to V^*/L \cap V^* = V^*/\mathrm{Ann}(E) = E^*.$$

Then we have  $\epsilon \in \wedge^2 E^*$ , and  $L = L(E, \epsilon)$ .

In an analogous way, we could consider Dirac structures  $L = L(F, \gamma)$ , where  $F = \pi_{V^*}(L)$ , and  $\gamma : F \to F^*$ .

Exercise. Let  $\operatorname{Dir}_k(V)$  be the space of Dirac structures of type k. Determine dim  $\operatorname{Dir}_k(V)$ . Compare this to the usual stratification of the Grassmannian  $\operatorname{Gr}_k(V)$ .

A B-field transformation cannot change the type of a Dirac structure, since

$$e^B L(E, \epsilon) = L(E, \epsilon + f^*B).$$

However, a  $\beta$ -field transform can. Express a given Dirac structure L as  $L(F,\gamma)$ , with  $g: F \to V^*$  an inclusion, and  $\gamma \in \wedge^2 F^*$ . Let  $E = \pi_V(L)$ , which contains  $L \cap V = \operatorname{Ann}(F)$ . Thus

$$E/L \cap V = E/\mathrm{Ann}(F) = \mathrm{Im} \ \gamma$$

and so

$$\dim E = \dim L \cap V + \operatorname{rank} \gamma.$$

Since rank  $\gamma$  is always even, if we change  $\gamma$  to  $\gamma + g^*\beta$ , we can change dim E by an even amount.

The space Dir(V) of Dirac structures has two connected components, one consisting of those of even type, and one consisting of those of odd type.

#### 4.3 Generalized metrics

There is another way to see the structure of Dir(V). Let  $C_+ \subset V \oplus V^*$  be a maximal subspace on which the pairing  $\langle \cdot, \cdot \rangle$  is positive definite, e.g., the space spanned by  $e_i + e^i$ , i = 1, ..., n. Let  $C_- = C_+^{\perp}$  be the orthogonal complement. Then  $\langle \cdot, \cdot \rangle$  is negative definite on  $C_-$ .

If L is a linear Dirac structure, then  $L \cap C_{\pm} = \{0\}$ , since L is isotropic. Thus L defines an isomorphism.

$$L: C_+ \to C_-$$

such that  $-\langle Lx, Ly \rangle = \langle x, y \rangle$ , since  $\langle x + Lx, y + Ly \rangle = 0$ . By choosing isomorphism between  $C_{\pm}$  and  $\mathbf{R}^n$  with the standard inner product, any  $L \in \mathrm{Dir}(V)$  may be regarded as an orthogonal transformation of  $\mathbf{R}^n$ , and conversely. Thus  $\mathrm{Dir}(V)$  is isomorphic to  $\mathrm{O}(n)$  as a space. The two connected components of  $\mathrm{O}(n)$  correspond in some way to the two components of  $\mathrm{Dir}(V)$  consisting of Dirac structures of even and odd type.

Observe that because  $C_+$  is transverse to V and  $V^*$ , the choice of  $C_+$  is equivalent to the choice of a map  $\gamma: V \to V^*$  such that the graph  $\Gamma_{\gamma}$  is a positive definite subspace, i.e., for  $0 \neq x \in V$ ,

$$\langle x + \gamma(x), x + \gamma(x) \rangle = \gamma(x, x) > 0.$$

Thus if we decompose  $\gamma$  into g+b, where g is the symmetric and b the anitsymmetric part, then g must be a positive definite metric on V. The form g+b is called a *generalized metric* on V. A generalized metric defines a positive definite metric on  $V \oplus V^*$ , given by

$$\langle \cdot, \cdot \rangle|_{C_{+}} - \langle \cdot, \cdot \rangle|_{C_{-}}$$

Exercise. Given  $A \in \mathcal{O}(n)$ , determine explicitly the Dirac structure  $L_A$  determined by the map  $\mathcal{O}(n) \to \mathrm{Dir}(V)$ .

## 5 Lecture 5 (Notes: C. Kottke)

## 5.1 Spinors

We have a natural action of  $V \oplus V^*$  on  $\bigwedge^{\cdot} V^*$ . Indeed, if  $X + \xi \in V \oplus V^*$  and  $\rho \in \bigwedge^{\cdot} V^*$ , let

$$(X + \xi) \cdot \rho = i_X \rho + \xi \wedge \rho.$$

Then

$$(X + \xi)^{2} \cdot \rho = i_{X}(i_{X}\rho + \xi \wedge \rho) + \xi \wedge (i_{X}\rho + \xi \wedge \rho)$$
$$= (i_{X}\xi)\rho - \xi \wedge i_{X}\rho + \xi \wedge i_{X}\rho$$
$$= \langle X + \xi, X + \xi \rangle \rho$$

where  $\langle , \rangle$  is the natural symmetric bilinear form on  $V \oplus V^*$ :

$$\langle X + \xi, Y + \eta \rangle = \frac{1}{2} (\xi(Y) + \eta(X)).$$

Thus we have an action of  $v \in V \oplus V^*$  with  $v^2 \rho = \langle v, v \rangle \rho$ . This is the defining relation for the Clifford Algebra  $CL(V \oplus V^*)$ .

For a general vector space E,  $CL(E, \langle, \rangle)$  is defined by

$$CL(E,\langle,\rangle) = \bigotimes E/\langle v \otimes v - \langle v,v \rangle 1 \rangle$$

That is,  $CL(E, \langle, \rangle)$  is the quotient of the graded tensor product of E by the free abelian group generated by all elements of the form  $v \otimes v - \langle v, v \rangle 1$  for  $v \in E$ . Note in particular that if  $\langle, \rangle \equiv 0$  then  $CL(E, \langle, \rangle) = \bigwedge E$ .

We therefore have representation  $CL(V \oplus V^*) \xrightarrow{\cong} \operatorname{End}(\bigwedge^{\cdot} V^*) \cong \operatorname{End}(\mathbb{R}^{2^n})$  where  $n = \dim V$ . This is called the "spin" representation for  $CL(V \oplus V^*)$ .

Choose an orthonormal basis for  $V \oplus V^*$ , i.e.  $\{e_1 \pm e^1, \dots, e_n \pm e^n\}$ . The clifford algebra has a natural volume element in terms of this basis given by

$$\omega \equiv (-1)^{\frac{n(n-1)}{2}} (e_1 - e^1) \cdots (e_n - e^n) (e_1 + e^1) \cdots (e_n + e^n).$$

**Problem.** Show  $\omega^1 = 1$ ,  $\omega e_i = -e_i \omega$ ,  $\omega e^i = -e^i \omega$ , and  $\omega \cdot 1 = 1$ , considering 1 as the element in  $\bigwedge^0 V^*$  acted on by the clifford algebra.

The eigenspace of  $\omega$  is naturally split, and we have

$$S^{+} \equiv \operatorname{Ker}(\omega - 1) = \bigwedge^{\operatorname{ev}} V^{*}$$
  
$$S^{-} \equiv \operatorname{Ker}(\omega + 1) = \bigwedge^{\operatorname{od}} V^{*}$$

The  $e^i$  are known as "creation operators" and the  $e_i$  as "annihilation operators". We define the "spinors" S by

$$S = \Lambda^{\cdot} V^* = S^+ \oplus S^-$$

Here is another view. V is naturally embedded in  $V \oplus V^*$ , so we have

$$CL(V) = \bigwedge V \subset CL(V \oplus V^*)$$

since  $\langle V, V \rangle = 0$ . Note in particular that  $\det V \subset CL(V \oplus V^*)$ , where  $\det V$  is generated by  $e_1 \cdots e_n$  in terms of our basis elements.  $\det V$  is a minimal ideal in  $CL(V \oplus V^*)$ , so  $CL(V \oplus V^*) \cdot \det V \subset CL(V \oplus V^*)$ . Elements of  $CL(V \oplus V^*) \cdot \det V$  are generated by elements which look like

$$\underbrace{(1, e^i, e^i e^j, \ldots)}_{\text{no } e_i} \quad \underbrace{e_1 \cdots e_n}_{\equiv f \in \det V}$$

For  $x \in CL(V \oplus V^*)$  and  $\rho \in S$ , the action  $x \cdot \rho$  satisfies  $x \rho f = (x \cdot \rho) f$ .

**Problem.** Show that this action coincides with the Cartan action.

## 5.2 The Spin Group

The spin group  $\mathrm{Spin}(V \oplus V^*) \subset CL(V \oplus V^*)$  is defined by

$$Spin(V \oplus V^*) = \{v_1 \cdots v_r : v_i \in V \oplus V^*, \langle v_i, v_i \rangle = \pm, r \text{ even.}\}$$

 $Spin(V \oplus V^*)$  is a double cover of the special orthogonal group  $SO(V \oplus V^*)$ ; there is a map

$$\rho: \operatorname{Spin}(V \oplus V^*) \xrightarrow{2:1} \operatorname{SO}(V \oplus V^*)$$

where the action  $\rho(x) \cdot v = xvx^{-1}$  in  $CL(V \oplus V^*)$ .

The adjoint action in the Lie algebra  $\mathfrak{so}(V \oplus V^*)$  is given by

$$d\rho_x: v \longmapsto [x,v]$$

where [,] is the commutator in  $CL(V \oplus V^*)$ , so

$$\mathfrak{so}(V \oplus V^*) = \operatorname{span}\{[x,y] : x,y \in V \oplus V^*\} \cong \bigwedge^2 (V \oplus V^*).$$

Recall that  $\bigwedge^2(V \oplus V^*) = \bigwedge^2 V^* \oplus \bigwedge^2 V \oplus \text{End}(V)$ , so a generic element in  $\bigwedge^2(V \oplus V^*)$  looks like

$$B + \beta + A \in \bigwedge^2 V^* \oplus \bigwedge^2 V \oplus \operatorname{End}(V)$$

In terms of the basis, say  $B = B_{ij}e^i \wedge e^j$ ,  $\beta^{ij}e_i \wedge e_j$ , and  $A = A_i^j e^i \otimes e_j$ . In  $CL(V \oplus V^*)$ , these become  $B_{ij}e^i e^j$ ,  $\beta^{ij}e_j e_i$  and  $\frac{1}{2}A_i^j(e_j e^i - e^i e_j)$ , respectively. Consider the action of each type of element on the spinors.

$$(B_{ij}e^ie^j)\cdot\rho=B_{ij}e^i\wedge e_i\wedge\rho=-B\wedge\rho$$

$$(\beta^{ij}e_ie_i) \cdot \rho = \beta^{ij}i_{e_i}i_{e_i}\rho = i_{\beta}\rho$$

$$\left(\frac{1}{2}A_i^j(e_je^i - e^ie_j)\right) \cdot \rho = \frac{1}{2}A_i^j(i_{e_j}(e^i \wedge \rho) - e^i \wedge i_{e_j}\rho) = \left(\frac{1}{2}A_i^j\delta_j^i\right)\rho - A_i^je^i \wedge e_j\rho = \left(\frac{1}{2}\mathrm{Tr}A\right)\rho - A^*\rho$$

Given  $B \in \bigwedge^2 V^*$ , recall the B field transform  $e^{-B}$ . This acts on the spinors via

$$e^{-B} \cdot \rho = \rho + B \wedge \rho + \frac{1}{2!} B \wedge B \wedge \rho + \cdots$$

Note that there are only finitely many terms in the above.

Similarly, given  $\beta \in \bigwedge^2 V$ , we have

$$e^{\beta} \cdot \rho = \rho + i_{\beta}\rho + \frac{1}{2}i_{\beta}i_{\beta}\rho + \cdots$$

For  $A \in \text{End}(V)$ ,  $e^A \equiv g \in \text{GL}^+(V)$ , we have

$$g \cdot \rho = \sqrt{\det(g)} \left(g^{*-1}\right) \cdot \rho$$

so that, as a  $\operatorname{GL}^+(V)$  representation,  $S \cong \bigwedge V^* \otimes (\det V)^{1/2}$ .

## 5.3 A Bilinear Pairing on Spinors

Let  $\rho, \phi \in \bigwedge^{\cdot} V^*$  and consider the reversal map  $\alpha : \bigwedge^{\cdot} V^* \to \bigwedge^{\cdot} V^*$  where

$$\xi_1 \wedge \cdots \wedge \xi_k \stackrel{\alpha}{\longmapsto} \xi_k \wedge \cdots \wedge \xi_1$$

Define

$$(\rho, \phi) = [\alpha(\rho) \wedge \phi]_n \in \det V^*$$

where  $n = \dim V$ , and the subscript n on the bracket indicates that we take only the degree n parts of the resulting form.

**Proposition 3.** For  $x \in CL(V \oplus V^*)$ ,  $(x \cdot \rho, \phi) = (\phi, \alpha(x) \cdot \phi)$ 

*Proof.* Recall that  $(x \cdot \rho)f = x\rho f$  and

$$(\rho, \phi) = i_f(\rho, \phi)f$$

$$= i_f(\alpha(\rho) \wedge \phi)f$$

$$= \alpha(f)\alpha(\rho)\phi f$$

$$= \alpha(\rho f)\phi f$$

so  $(x \cdot \rho, \phi) = \alpha(x\rho f)\phi f = \alpha(\rho f)\alpha(x)\phi f = (\rho, \alpha(x)\phi).$ 

Corollary 2. We have

$$(v \cdot \rho, v \cdot \phi) = (\rho, \alpha(v)v \cdot \phi) = \langle v, v \rangle (\rho, \phi)$$

Also, for  $g \in Spin(V \oplus V^*)$ ,

$$(g \cdot \rho, g \cdot \phi) = \pm 1(\rho, \phi)$$

**Example.** Suppose n = 4, and  $\rho, \phi \in \bigwedge^{ev} V^*$ , so that

$$\rho = \rho_0 + \rho_2 + \rho_4$$

and similarly for  $\phi$ , where the subscripts indicate forms of degree 0, 2, and 4. Then  $\alpha(\rho) = \rho_0 - \rho_2 + \rho_4$  and

$$(\rho, \phi) = [(\rho_0 - \rho_2 + \rho_4) \wedge (\phi_0 + \phi_2 + \phi_4)]_4 = \rho_0 \phi_4 + \phi_0 \rho_4 - \rho_2 \wedge \phi_2$$

If n = 4 and  $\rho, \phi \in \bigwedge^{\text{od}} V^*$ , then

$$(\rho, \phi) = [(\rho_1 - \rho_3) \wedge (\phi_1 + \phi_3)]_4 = \rho_1 \wedge \phi_3 - \rho_3 \wedge \phi_1.$$

**Proposition 4.** In general,  $(\rho, \phi) = (-1)^{\frac{n(n-1)}{2}}(\phi, \rho)$ 

**Problem.** • What is the signature of (, ) when symmetric?

- Show that (, ) is non-degenerate on  $S^{\pm}$ .
- Show that in dimension 4, the 16 dimensional space  $\bigwedge^{\cdot}V^*$  has a non degenerate symmetric form

### 5.4 Pure Spinors

Let  $\phi \in \Lambda^{\cdot} V^*$  be any nonzero spinor, and define the null space of  $\phi$  as

$$L_{\phi} = \{X + \xi \in V \oplus V^* : (X + \xi) \cdot \phi = 0\}.$$

It is clear then that  $L_{\phi}$  depends equivariantly on  $\phi$  under the spin representation. If

$$\phi \mapsto g \cdot \phi, \qquad g \in \operatorname{Spin}(V \oplus V^*)$$

then

$$L_{\phi} \mapsto \rho(g)L_{\phi}$$

where  $\rho: \mathrm{Spin}(V \oplus V^*) \to \mathfrak{so}(V \oplus V^*)$  as before. The key property of the null space is that it is isotropic. Indeed, if  $x, y \in L_{\phi}$  we have

$$2\langle x, y \rangle \phi = (xy + yx)\phi = 0.$$

Thus  $L_{\phi} \subset L_{\phi}^{\perp}$ .

If  $L_{\phi} = L_{\phi}^{\perp}$ , that is, if  $L_{\phi}$  is maximal, then  $\phi$  is called "pure". We have therefore that  $\phi$  is pure if and only if  $L_{\phi}$  is Dirac.

**Example.** • Take  $\phi = e^1 \wedge \cdots \wedge e^n$ . Then  $L_{\phi} = V^*$ .

- Take  $1 \in \bigwedge^0 V^*$ . Then  $L_1 = V$ . For  $B \in \bigwedge^2 V^*$ , then  $e^{-B} \cdot 1 = 1 B + 1/2B \wedge B + \cdots$ . So  $L_{e^B} = e^B(L_1) = e^B(V) = \Gamma_B$ .
- For  $\theta \in V^*$ ,  $\theta$  is pure since  $L_{\theta} = \{X + \xi : i_X \theta + \xi \wedge \theta = 0\} = \text{Ker } \theta \oplus \langle \theta \rangle$  which is Dirac; indeed this is what we called  $L(\text{Ker } \theta, 0)$ .
- Similarly, considering  $e^B \theta$ , we have  $L_{e^B \theta} = L(\text{Ker } \theta, f^*B)$ .
- Given a Dirac structure  $L(E, \epsilon)$ , choose  $\theta_1, \ldots, \theta_k$  such that  $\langle \theta_1, \ldots, \theta_k \rangle = \text{Ann } E$ . Choose  $B \in \bigwedge^2 V^*$  such that  $f_{\epsilon}^* B = \epsilon$ . Then  $\phi = e^{-B} \theta_1 \wedge \cdots \wedge \theta_k$  is pure and  $L_{\phi} = L(E, \epsilon)$ .

**Problem.** • Show  $L_{\phi} \cap L_{\phi'} = \{\emptyset\} \Leftrightarrow (\phi, \phi') \neq 0$ .

• Let dim V=4, and  $\rho=\rho_0+\rho_2+\rho_4\neq 0$ . Show that  $\rho$  is pure iff  $2\rho_0\rho_4=\rho_2\wedge\rho_2$ .

## 6 Lecture 6 (Notes: Y. Lekili)

Recall from last lecture :

$$S = \Lambda^{\bullet}V^*, (X + \xi) \cdot \rho = \iota_X \rho + \xi \wedge \rho. \text{ Mukai pairing } (\rho, \phi) = [\rho \wedge \alpha(\phi)]_n \text{ Spin}_0\text{-invariant.}$$

$$Dir(V) \longleftrightarrow Pure spinors$$
  
 $L_{\phi} \longleftrightarrow \phi = ce^{B}\theta_{1} \wedge ... \wedge \theta_{k}, k = type$ 

**Problem.** 1. Prove that  $L_{\phi} \cap L'_{\phi} = \{0\} \Leftrightarrow (\phi, \phi') \neq 0$ 

2. Let  $\dim V = 4$ . Show that  $0 \neq \rho = \rho_0 + \rho_2 + \rho_4$  is pure iff  $2\rho_0\rho_4 = \rho_2 \wedge \rho_2$ . Show in general dimension that  $\text{Pur} = \text{Pure spinors} \subset S^{\pm}$  are defined by a quadratic cone. Indentify the space  $\mathbb{P}(Pur) \subset \mathbb{P}(S^{\pm})$ .

### 6.1 Generalized Hodge star

 $C_+$  positive definite.  $C_+:V\to V^*$ ,  $C_+(X)(X)>0$  for  $X\neq 0$ .  $C_+=\Gamma_{g+b},$   $g\in S^2V^*$  and  $b\in \Lambda^2V^*$ . Note that  $C_+$  determines an operator

$$G:V\oplus V^*\to V\oplus V^*$$

 $\langle Gx, Gy \rangle = \langle x, y \rangle, G^2 = 1$ . So  $G^* = G$ . G is called a generalized metric since  $\langle Gx, y \rangle$  is positive definite.

Note that if 
$$C_+ = \Gamma_g : \{v + g(v)\}$$
 and  $C_- = \{v - g(v)\}$  then  $G = \begin{pmatrix} 0 & g^{-1} \\ g & 0 \end{pmatrix}$ . In general

$$C_+ = \Gamma_{g+b} = e^b \Gamma_g$$
 so

$$G = e^{b} \begin{pmatrix} 0 & g^{-1} \\ g & 0 \end{pmatrix} e^{-b} = \begin{pmatrix} 1 & 0 \\ b & 1 \end{pmatrix} \begin{pmatrix} 0 & g^{-1} \\ g & 0 \end{pmatrix} \begin{pmatrix} 1 & 0 \\ -b & 1 \end{pmatrix} = \begin{pmatrix} -g^{-1}b & g^{-1} \\ g - bg^{-1}b & bg^{-1} \end{pmatrix}$$

**Problem.** Note that restriction of G to T is  $g - bg^{-1}b$ . Verify that it is indeed positive definite.

Comment about the volume form of  $g - bg^{-1}b = g^b$ :

Note: 
$$g - bg^{-1}b = (g - b)g^{-1}(g + b)$$
. So  $\det(g - bg^{-1}b) = \det(g - b)\det(g^{-1})\det(g + b)$ , and  $\det(g + b) = \det(g + b)^* = \det(g - b)$ . Hence  $vol_{g^b} = \det(g - bg^{-1}b)^{1/2} = \frac{\det(g + b)}{\det(g)^{1/2}}$ .

**Problem.** What is  $vol_{q^b}/vol_q$ ?

Aside:  $\det V^*$ , choose orientation.  $\det V^* \otimes V^*$ , natural orientation since square.  $\det g(v \otimes v) > 0$  so  $\det g$  has square roots. After choice of orientation on V, there exists a unique positive square root  $vol_g$ .

A generalized metric is given by  $G: V \oplus V^* \to V \oplus V^*$  such that  $G^2 = 1, G^* = G, \langle G(x), x \rangle > 0$ .  $C_+ = ker(G \mp 1)$ .

Consider  $* = a_1 \dots a_n$  where  $(a_1, \dots, a_n)$  is an oriented basis for  $C_+$ .  $* \in CL(C_+) \subset CL(V \oplus V^*)$ .

- \* is the volume element of  $CL(C_+)$
- \* is the lift of -G to  $Pin(V \oplus V^*) = \{v_1 \dots v_r : ||v_i|| = \pm 1\}$  (Spin if n is even)
- \* acts on forms via \*  $\cdot \rho = a_1 \dots a_n \cdot \rho$ .

Consider b=0 and  $e_i, e^i$  orthonormal basis. Then  $*=(e_1+e^1)\dots(e_n+e^n)$ . Consider  $\alpha(*)=(e_n+e^n)\dots(e_1+e^1)$ .  $\alpha(*)1=e^n\wedge\dots\wedge e^1, \alpha(*)e^1=e^n\wedge\dots\wedge e^2,\dots e^2$ .

$$\alpha(\alpha(*)\rho) = \star \rho$$
, Hodge star.

So  $\alpha(\alpha(*)\rho)$  is generalized Hodge star. Note that  $*^2 = (-1)^{\frac{n(n-1)}{2}}$  and  $(\rho,\phi) = (-1)^{\frac{n(n-1)}{2}}(\phi,\rho)$ . So consider  $(*\rho,\phi)$  is symmetric pairing of  $\rho,\phi$  into  $\det V^*$ . And note that if b=0,

$$(*\rho,\phi) = (\rho,\alpha(*)\phi) = [\rho \land \alpha(\alpha(*)\phi)]_{top} = [\rho \land \star \phi]_{top} = g(\rho,\phi)vol_g$$

When  $b \neq 0, G = e^b \begin{pmatrix} 0 & g^{-1} \\ g & 0 \end{pmatrix} e^{-b}$ . So  $* = e^b *_g e^{-b}$ , and  $(*\rho, \phi) = (e^b *_g e^{-b}\rho, \phi) = (*_g (e^{-b}\rho)e^{-b}\phi)$ . So

always nondegenerate for all b. Hence  $(*\rho, \phi) = G(\rho, \phi)(*1, 1)$  with G(1, 1) = 1 where G is the natural symmetric pairing on forms.

**Problem.** Let  $e_1, \ldots, e_n$  be g-orthonormal basis of V.

- Show  $(e_i + (g+b)(e_i))$  form orthonormal basis of  $C_+$ .
- Show  $(*1,1) = det(g+b)(e_1 \wedge ... \wedge e_n) = \frac{\det(g+b)}{\det(g)^{1/2}} = vol_{g^b}$
- As a result, show  $\frac{vol_{g^b}}{vol_g} = ||e^{-b}||_g^2$

## **6.2** Spinors for $TM \oplus T^*M$ and the Courant algebroid

On a manifold  $M, T = TM, T^* = T^*M$ .  $T \oplus T^*$  is a bundle with  $\langle , \rangle$  structure O(n, n).  $S = \Lambda^{\bullet}T^*$ .

Diff forms 
$$\longleftrightarrow$$
 Spinors for  $T \oplus T^*$ .

New element:  $d: \Omega^k \to \Omega^{k+1}$ . Recall [X,Y] is defined by  $\iota_{[X,Y]} = [L_X, \iota_Y] = [[d, \iota_X], \iota_Y]$ . We now use same strategy to define a bracket on  $T \oplus T^*$ .

$$(X + \xi) \cdot \rho = (\iota_X + \xi \wedge) \rho$$

So for  $e_1, e_2 \in C^{\infty}(T \oplus T^*)$ , define

$$[[d, e_1 \cdot], e_2 \cdot] \rho = [e_1, e_2]_{\mathcal{C}} \cdot \rho$$

the Courant bracket on  $C^{\infty}(T \oplus T^*)$ . Note  $[d, \iota_X + (\xi \wedge)] = L_X + (d\xi \wedge)$  and

$$[L_X + (d\xi \wedge), \iota_Y + (\eta \wedge)] = \iota_{[X,Y]} + ((L_X \eta) \wedge) - ((\iota_Y d)\xi \wedge).$$

Hence

$$[[d, e_1 \cdot], e_2 \cdot] \rho = \iota_{[X,Y]} \rho + (L_X \eta - \iota_Y d\xi) \wedge \rho$$

defines a bracket, Courant bracket:

$$[X + \xi, Y + \eta] = [X, Y] + L_X \eta - \iota_Y d\xi.$$

Note bracket is not skew-symmetric:  $[X + \xi, X + \xi] = L_X \xi - \iota_X d\xi = d\iota_X \xi = d\langle X + \xi, X + \xi \rangle$ . It is skew "up to exact terms" or "up to homotopy". However, it does satisfy Jacobi identity:

$$[[a,b].c] = [a,[b,c]] - [b,[a,c]].$$

Proof:  $[d, \cdot] = D$  an inner graded derivation on End $\Omega$ .  $D^2 = 0$ .  $[a, b]_{\mathcal{C}} \cdot \phi = [[d, a], b] \cdot \phi = [Da, b]$  Then  $[[a, b]_{\mathcal{C}}, c]_{\mathcal{C}} \cdot \phi = [D[Da, b], c]\phi = [[Da, Db], c]\phi = [Da, [Db, c]] - [Db, [Da, c]] = [a, [b, c]_{\mathcal{C}}]_{\mathcal{C}} - [b, [a, c]_{\mathcal{C}}]_{\mathcal{C}}$ .

It is also obviously compatible with Lie bracket.

$$T \oplus T^* \stackrel{\pi}{\longrightarrow} T$$
$$[\ ,\ ]_{\mathcal{C}} \longrightarrow [\ ,\ ]$$

that is,  $[\pi a, \pi b] = \pi [a, b]_{\mathcal{C}}$ .

Two main key properties:

•  $[a, fb] = f[a, b] + ((\pi a)(f))b$ .

Let 
$$a = X + \xi, b = Y + \eta$$
,  $[X + \xi, f(Y + \eta)] = [X, fY] + L_X(f\eta) - f\iota_Y d\xi = f[a, b] + (Xf)Y + (Xf)\eta = f[X + \xi, Y + \eta] + (Xf)(Y + \eta)$ .

• How does it interact with  $\langle , \rangle$ ?  $\pi a \langle b, b \rangle = 2 \langle [a, b], b \rangle$ 

$$\langle [a,b],b\rangle = \iota_{[X|Y]}\eta + \iota_{Y}(L_{X}\eta - \iota_{Y}d\xi) = L_{X}\iota_{Y}\eta = \frac{1}{2}L_{X}\langle b,b\rangle = \pi a\langle b,b\rangle$$

Usually written :  $\pi a \langle b, c \rangle = \langle [a, b], c \rangle + \langle b, [a, c] \rangle$ .

This defines the notion of Courant Algebroid:

 $(E, \langle, \rangle, [,], \pi)$  where E is a real vector bundle,  $\pi : E \to T$  is called anchor,  $\langle, \rangle$  is nondegenerate symmetric bilinear form,  $[,]: C^{\infty}(E) \times C^{\infty}(E) \to C^{\infty}(E)$  such that :

- $[[e_1, e_2], e_3] = [e_1, [e_2, e_3] [e_2, [e_1, e_3]]$
- $[\pi e_1, \pi e_2] = \pi[e_1, e_2]$
- $[e_1, fe_2] = f[e_1, e_2] + (\pi e_1)f)e_2$
- $\pi e_1 \langle e_2, e_3 \rangle = \langle [e_1, e_2], e_3 \rangle + \langle e_2, [e_1, e_3] \rangle$
- $\bullet \ [e_1, e_1] = \pi^* d\langle e_1, e_1 \rangle$

E is exact when

$$0 \to T^* \xrightarrow{\pi^*} E \xrightarrow{\pi} T \to 0$$

So  $T \oplus T^*$  is exact Courant algebroid.

This motivates Lie Algebroid:  $A \xrightarrow{\pi} T$ ,  $[,]: C^{\infty}(A) \times C^{\infty}(A) \to C^{\infty}(A)$  Lie alg. such that

- $\pi[a,b] = [\pi a, \pi b]$
- $[a, fb] = f[a, b] + ((\pi a)f)b$

## 7 Lecture 7 (Notes: N. Rosenblyum)

## 7.1 Exact Courant Algebroids

Recall that a Courant algebroid is given by the diagram of bundles

where  $\pi$  is called the "anchor" along with a bracket [, ] and a nondegenerate bilinear form  $\langle , \rangle$  such that

- $\pi[a,b] = [\pi a, \pi b]$
- The Jacobi identity is zero
- $[a, fb] = f[a, b] + ((\pi a)f)b$
- $[a,b] = \frac{1}{2}\pi^*d\langle a,a\rangle$
- $\pi a \langle b, c \rangle = \langle [a, b], c \rangle + \langle b, [a, c] \rangle$

A Courant algebroid is exact if the sequence

$$0 \longrightarrow T^* \stackrel{\pi}{\longrightarrow} E \stackrel{\pi^*}{\longrightarrow} T \longrightarrow 0$$

is exact (note that  $\pi \circ \pi^*$  is always 0).

Remarks: For an exact Courant algebroid, we have:

1. The inclusion  $T^* \subset E$  is automatically isotropic because for  $\xi, \eta \in T^*$ ,

$$\langle \pi^* \xi, \pi^* \eta \rangle = \xi(\pi^* \pi \eta) = 0$$

since  $\langle \pi^* \xi, a \rangle = \xi(\pi a)$ .

2. The bracket  $[ , ]|_{T^*} = 0$ : for  $s, t \in C^{\infty}(E), f \in C^{\infty}(M),$ 

$$\mathcal{D} = \pi^* d : C^{\infty}(M) \to C^{\infty}(E)$$

Now.

$$\langle [s, \mathcal{D}f], t \rangle = \pi s \langle \mathcal{D}f, t \rangle - \langle \mathcal{D}f, [s, t] \rangle = \pi s (\pi t(f)) - \pi [s, t](f) = \pi t (\pi s(f)) = \langle \mathcal{D}\langle \mathcal{D}f, s \rangle, f \rangle$$

Thus,  $[s, \mathcal{D}f] = \mathcal{D}\langle s, \mathcal{D}f \rangle$ . We also have,  $[\mathcal{D}f, s] + [s, \mathcal{D}f] = \mathcal{D}\langle \mathcal{D}f, s \rangle$  and therefore [Df, s] = 0. We need to show that  $[fdx^i, gdx^j] = 0$ . But have  $[dx^i, dx^j] = 0$  and

$$[a, fb] = f[a, b] + ((\pi a)f)b, \quad [ga, b] = g[a, b] - ((\pi b)g)a + 2\langle a, b\rangle dg.$$

## 7.2 Ševera's Classification of Exact Courant Algebroids

We can choose an isotropic splitting

$$0 \longrightarrow T^* \stackrel{\pi^*}{\underset{s^*}{\longleftarrow}} E \stackrel{\pi}{\underset{s}{\longleftarrow}} T \longrightarrow 0$$

i.e.  $\langle sX, sY \rangle = 0$  for all  $X, Y \in T$ . We then have  $E \cong T \oplus T^*$  and we can transport the Courant structure to  $T \oplus T^*$ : for  $X, Y \in T$  and  $\xi, \eta \in T^*$ ,

$$\langle X + \xi, Y + \eta \rangle = \langle sX + \pi^* \xi, sY + \pi^* \eta \rangle = \xi(\pi sY) + \eta(\pi sX) = \xi(Y) + \eta(X)$$

since  $\langle sX, sY \rangle = 0$ . Also,

$$[X + \xi, Y + \eta] = [sX + \pi^* \xi, sY + \pi^* \eta] = [sX, sY] + [sX, \pi^* \eta] + [\pi^* \xi, sY]$$

We have that the second term is given by

$$\pi[sX, \pi^*\eta] = [\pi sX, \pi \pi^*\eta] = 0$$

and therefore,  $[sX, \pi^*\eta] \in \Omega^1$ . Further,

$$[sX, \pi^*\eta](Z) = \langle [sX, \pi^*\eta], sZ \rangle = X\langle \pi^*\eta, sZ \rangle - \langle \pi^*\eta, [sX, sZ] \rangle = X\eta(Z) - \eta([X, Z]) = i_Z L_X \eta$$

and so  $[sX, \pi^*\eta] = L_X\eta$ .

Now, the third term is given by

$$\langle [\pi^*\xi, sY], sZ \rangle = \langle -[sY, \pi^*\xi] + \mathcal{D}\langle sY, \pi^*\xi \rangle, sZ \rangle = -(L_Y\xi)(Z) + i_Z di_Y \xi = (-i_Y d\xi)(Z)$$

and so  $[\pi^*\xi, sY] = -i_Y d\xi$ .

For the first term, we have no reason to believe that [sX, sY] = [X, Y] We do have that  $\pi[sX, sY] = [X, Y]_{Lie}$ . Now, let  $H(X, Y) = s^*[sX, sY]$ . We then have,

1. H is  $C^{\infty}$ -linear and skew in X, Y:

$$H(X,fY)=fs^*[sX,sY]+s^*(X(f)sY)=fs^*[sX,sY], \text{ and}$$
 
$$H(fX,Y)=s^*[fsX,sY]=fH(X,Y)-s^*((Yf)sX)+2\langle sX,sY\rangle df=fH(X,Y). \text{ Furthermore,}$$
 
$$[sX,sY]+[sY,sX]=\pi^*d\langle sX,sY\rangle.$$

2. H(X,Y)(Z) is totally symmetric in X,Y,Z:

$$H(X,Y)(Z) = \langle [sX,sY], sZ \rangle_E = X \langle sY, sZ \rangle - \langle sY, [sX,sZ] \rangle$$

So, we have  $[sX, sY] = [X, Y] - i_Y i_X H$  for  $H \in \Omega^3(M)$ .

**Problem.** Show that  $[[a,b],c]=[a,[b,c]]-[b,[a,c]]+i_{\pi c}i_{\pi b}i_{\pi a}dH$  and so Jac=0 if and only if dH=0.

Thus, we have that the only parameter specifying the Courant bracket is a closed three form  $H \in \Omega^3(M)$ . We will see that when  $[H]/2\pi \in H^3(M,\mathbb{Z})$ , E is associated to an  $S^1$ -gerbe.

Now, let's consider how H changes when we change the splitting. Suppose that we have two section  $s_1, s_2 : T \to E$ . We then have that  $\pi(s_1 - s_2) = 0$ . So consider  $B = s_1 - s_2 : T \to T^*$ . In the  $s_1$  splitting, we have for  $x \in T$ ,  $s_2(x) = (x + (s_2 - s_1)x)$ . Since the  $s_i$  are isotropic splittings, we have that  $(s_2 - s_1)(x)(x) = 0$ . Thus we have,  $B \in C^{\infty}(\Lambda^2 T^*)$ . Now, in the  $s_1$  splitting we have,

$$[X + i_x B, Y + i_Y B]_H = [X, Y] + L_X i_Y B - i_Y di_X B + i_Y i_X H = [X, Y] + i_{[X, Y]} B - i_Y L_X B + i_Y di_X B + i_Y i_X H = [X, Y] + i_{[X, Y]} B + i_Y i_X (H + dB)$$

In particular, in the  $s_2$  splitting H changes by dB. Thus, we have that  $[H] \in H^3(M,\mathbb{R})$  classifies the exact Courant algebroid up to isomorphis.

The above bracket is also a derived bracket. Before, we had that

$$[a,b]_{\mathcal{C}} \cdot \varphi = [[d,a],b]\varphi.$$

Now, replace d with  $d_H = d + H \wedge$ . We clearly have that  $d_H^2 = (dH) \wedge = 0$  since dH = 0. Note that  $d_H$  is not of degree one and is not a derivation but it is odd. The cohomology of  $d_H$  is called H-twisted deRham cohomology. In simple cases (e.g. when M is formal in the sense of rational homotopy theory,), we have

$$H^*(H^{ev/od}(M), e_{[H]}) = H_{d_H}^{ev/od}(M)$$

where  $e_H = H \wedge$ .

Now,  $[a,b]_H \cdot \varphi = [[d_H,a],b]\varphi$ . Indeed, for  $B \in \Omega^2$ , we have  $\varphi \mapsto e^B \varphi$  and  $e^{-B}(d+H\wedge)e^B = e^{-B}de^B + e^{-B}He^B = d_{H+dB}$ , and so  $e^B[e^{-B}\cdot,e^B\cdot]_H = [\ ,\ ]_{H+dB}$  In particular, if  $B \in \Omega^2_{\circ}l$ , then  $e^B$  is a symmetry of the Courant bracket.

This phenomena is somewhat unusual because for the ordinary Lie bracket, the only symmetries are given by diffeomorphisms of the underlying manifold. More specifically, a symmetry of the Lie bracket on  $C^{\infty}(T)$  is a diagram

$$T \xrightarrow{\Phi} T$$

$$\downarrow \qquad \qquad \downarrow$$

$$M \xrightarrow{\phi} M$$

such that  $\phi$  is a diffeomorphism and  $[\Phi, \Phi] = \Phi[\cdot, \cdot]$ .

Claim 1.  $Sym[\ ,\ ]_{Lie} = \{(\phi_*, \phi), \ \phi \in Diff(M)\}.$ 

Proof. Given  $(\Phi, \phi) \in Sym[\ ,\ ]_{Lie}$ , consider  $G : \Phi\phi_*^{-1}$ . Then G covers the identity map on M and we have fG[X,Y] - ((Yf)GX = G[fX,Y] = f[GX,GY] - (GY)fGX and so Yf = (GY)(f) for all Y, f and so G = 1.

Let's now consider the question of what all the symmetries of the Courant bracket  $[\ ,\ ]_{\mathcal{C}}$  are. Once again, we have a diagram

$$\begin{array}{ccc} E & \stackrel{\Phi}{\longrightarrow} E \\ \downarrow & & \downarrow \\ M & \stackrel{\phi}{\longrightarrow} M \end{array}$$

where  $E \simeq T \oplus T^*$  such that

- 1.  $\phi^* \langle \Phi \cdot, \Phi \cdot \rangle = \langle \cdot, \cdot \rangle$
- 2.  $[\Phi \cdot, \Phi \cdot] = \Phi[\cdot, \cdot]$
- 3.  $\pi \circ \Phi = \phi_* \circ \pi$ .

Suppose that  $\phi \in Diff(M)$ . Then on  $T \oplus T^*, \phi_*$  is given by

$$\phi_* = \left( \begin{array}{cc} \phi_* & \\ & (\phi^*)^{-1} \end{array} \right)$$

and so we have  $\phi_*(X + \xi) = \phi_* X + (\phi^*)^{-1} \xi$  and

$$\phi_*^{-1}[\phi_*X + (\phi^*)^{-1}\xi, \phi_*Y + (\phi^*)^{-1}\eta]_H = [X + \xi, Y + \eta]_{\phi^*H}$$

since  $\phi_*^{-1}(i_{\phi_*Y}i_{\phi_*X}H)(Z) = i_{\phi_*Z}i_{\phi_*Y}i_{\phi_*X}H = \phi^*H(X,Y,Z)$ . In particular, this does not give a symmetry unless  $\phi^*H = H$ .

Now, consider a *B*-field transform. Since  $e^B[e^{-B}\cdot,e^{-B}\cdot]_H=[\cdot,\cdot]_{H+dB}$ , this is not a symmetry unless dB=0. Now we can combine these to generate the symmetries:

$$[\phi_*e^B\cdot,\phi_*e^B\cdot]=\phi_*e^B[\cdot,\cdot]_{\phi^*H+dB}$$

and so  $\phi_*e^B \in SymE$  iff  $H - \phi^*H = dB$ . It turns out that these are all the symmetries.

**Theorem 5.** The above are all the symmetries of an exact Courant algebroid. In particular, we have a short exact sequence

$$0 \to \Omega^2_{cl} \to Sym(E) \to Diff_{[H]} \to 0$$

where  $Diff_{[H]}$  is the subgroup of diffeomorphisms of M preserving the cohomology class [H].

## 8 Lecture 8 (Notes: J. Bernstein)

#### 8.1 Dirac Structures

So far we understand the exact Courant Algebroids

$$0 \to T^* \to E \to T \to 0$$

Which are classified up to isomorphism by  $[H] \in H^3(M, \mathbb{R}^3)$  and upon a choice of splitting is isomorphic to  $(T \oplus T^*, <, >, [,]_H, \pi : E \to T)$ . For  $H \in \Omega^3_{cl}$ . Always consider (M, E) or (M, H). Geometry in exact Courant Algebroids consists of studying special subbundles  $L \subseteq E$ .

**Theorem 6.** Suppose that  $L \subseteq E$  a subbundle which is closed under [,] (involutive), i.e.  $[C^{\infty}(L), C^{\infty}(L)] \subseteq C^{\infty}(L)$ . then L must be isotropic or  $L = \pi^{-1}(\Delta)$  for  $\Delta \subseteq T$  integrable distribution. Note, for  $\Delta^k \subseteq T$ ,  $\pi^{-1}(\delta)$  is of dimension n + k and contains  $T^*$  (so is not isotropic).

Proof. Suppose L is involutive, but not isotropic, then there exists  $v \in C^{\infty}(L)$  with  $\langle v, v \rangle_m \neq 0$ . Now recall property  $[fv, v] = f[v, v] - (\pi(v)f)v + 2 \langle v, v \rangle df \Rightarrow 2 \langle v, v \rangle df \in C^{\infty}(L)$  for all f, as  $[fv, v], f[v, v] \in C^{\infty}(L)$ . This implies that  $df_m \in L_m$  for all m which tells us that  $T_m^* \subseteq L_m$  but  $T^*$  is isotropic so  $L_m = \pi^{-1}(\Delta_m)$  for  $\Delta \neq 0$ . Thus  $\mathrm{rk} L > n$  evertywhere and so L not isotropic at all points  $p \in M$  thus  $T_p^* \subseteq L_p$  for all p and so  $L = \pi^{-1}(\Delta)$  where  $\Delta$  is an integrable distribution.

So interesting involutive subbundles are isotropic subbundles  $L \subseteq E$ . Recall that the axioms of a Courant Algebroid imply that  $[a,a] = \frac{1}{2}\pi^*d < a,a>$ . Thus on L,  $[,]_{\mathcal{C}_{\infty}(L)}$  defines a Lie Algebroid when L is involutive and isotropic. So  $L \subseteq E$  with  $[L,L] \subseteq L$  and (L,L) = 0 implies that  $(L,[,],\pi)$  is a Lie Algebroid which implies  $(C^{\infty}(\wedge^*L^*),d_L)$  gives rise the  $H_{d_L}(M)$  the Lie Algebroid Cohomology.

**Definition 14.** When an isotropic, involutive  $L \subset E$  is maximal it is called a Dirac Structure

Examples of Dirac structures in  $0 \to T^* \to E \to T \to 0$ 

- $T^* \subset E$  as  $[T^*, T^*] \subseteq [T^*, T^*]$
- If we split  $(T \oplus T^*, [,]_H)$  then  $[X,Y]_H \in C^{\infty}(T)$  if and only if H = 0 so  $T \in T \oplus T^*$  is a Dirac structure if and only if H = 0
- Any maximal isotropic transverse L (that is such that  $L \cap T^* = \{0\}$  is of the form  $L = \Gamma_B$ . Since  $e^B[e^{-B}\cdot,e^{-B}\cdot]_H = [\cdot,\cdot]_{H+dB}$  so  $e^B[T,T]_{H-dB} = e^B[e^{-B}\Gamma_B,e^{-B}\Gamma_B]_{H-dB} = [\Gamma_B,\Gamma_B]_H$ . Thus  $[\Gamma_B,\Gamma_B] \subset \Gamma_B$  if and only if  $[T,T]_{H-dB} \subseteq T$  and this occurs if and only if H-dB=0 so  $\Gamma_B$  is Dirac when and only when [H]=0. In particular when  $[H]\neq 0$  there is no Dirac complement to  $T^*$ .
- When  $\Delta \subset T$  is an integral distribution then  $f : \Delta \oplus \text{Ann } \Delta \hookrightarrow T \oplus T^*$  is involutive for  $[,]_H$  when and only when  $f^*H = 0$ .
- For  $(T \oplus T^*, [,]_H)$  and  $\beta \in \wedge^2 T$  we consider  $\Gamma_{\beta}$ . This is Dirac if and only if  $[\beta, \beta] = -\beta^* H$  where we think of  $\beta : T^* \to T$ .

**Problem.** Verify the condition for  $\Gamma_{\beta}$  to be Dirac by first showing that  $[\xi + \beta(\xi), \eta + \beta(\eta)] = \zeta + \beta(\zeta)$  if and only if  $\langle [\xi + \beta(\xi), \eta + \beta(\eta)], \zeta + \beta(\zeta) \rangle = 0$ . And then showing that  $\langle [df + \beta(df), dg + \beta(dg)], dh + \beta(dh) \rangle = \{f, \{g, h\}\} + \{g, \{h, f\}\} + \{h, \{f, g\}\} + H(\beta(df), \beta(dg), \beta(dh)) = (Jac\{, \} + \beta^*H)(df, dg, dh).$ 

**Definition 15.** if  $[\beta, \beta] = -\beta^* H$  then  $\beta$  is called a twisted Poisson Structure.

Suppose that  $\beta$  is a twisted Poisson structure, then  $e^B\Gamma_{\beta}$  is not necessarily  $\Gamma_{\beta'}$ , in particular if  $\beta$  is invertible (as a map  $T^* \to T$ ) and  $\beta^{-1} = B$  then  $e^{-B}\Gamma_{\beta} = T$ . However if B is "small enough" then  $e^B\Gamma_{\beta} = \Gamma_{\beta'}$ . To quantify this we note that  $e^B : \xi + \beta(\xi) \mapsto \beta(\xi) + \xi + B\beta(\xi)$  which we want equal to  $\eta + \beta'(\eta)$ . This happens if and only if  $\eta = (1 + B\beta)\xi$  and also  $\beta(\xi) = \beta'(\eta) = \beta'(1 + B\beta)\xi$ . Thus  $\beta' = \beta(1 + B\beta)^{-1}$  and so smallness just means that the map is invertible (i.e. what is written makes sense).

**Definition 16.** The transformation from  $\beta \mapsto \beta(1+B\beta)^{-1}$  is called a gauge transform of  $\beta$ .

**Problem.** (Ševera-Weinstein) Show that if  $\beta$  is Poisson and  $d\beta = 0$  then  $\beta'$  is Poisson. Also show that  $H_{\beta}(M) \cong H_{\beta'}(M)$ , (i.e. one has a isomorphsm of Poisson cohomology. (Hint:  $e^B : \Gamma_{\beta} \to \Gamma_{\beta'}$  is an isomorphism of Lie Algebras).

#### 8.2 Geometry of Lie Groups

Recall that for a Lie group G one has a natural action of  $G \times G$  on G, given by  $(g,h) \cdot x = gxh = L_gR_hx$  (here one has a left action and a right action). These actions commute in that (gx)h = g(xh). Now for  $\mathfrak{g} = T_eG$  the lie algebra of G one has two identifications of  $\mathfrak{g} \to T_gG$  namely  $a \mapsto a^L|_g = (L_g)_*a$  and  $a \mapsto a^R|_g = (R_g)_*a$  where  $a^L$ ,  $a^R$  are left and right invariant vector fields respectively. We have by definition  $[a^L, b^L]_{Lie} = [a, b]^L$ . Now if  $j: G \to G$  is given by  $x \mapsto x^{-1}$ , then  $jL_g = R_{g^{-1}}j$  so  $j_*(L_g)_* = (R_{g^{-1}})_*j_*$ . In particular since  $(j_*)_e = -Id$ , one has  $(j_*a^L)_{g^{-1}} = j_*(L_g)_*a = (R_{g^{-1}})_*j_*a = -(R_{g^{-1}})_*a = -a^R|_{g^{-1}}$ . Thus  $j_*a^L = -a^R$ . Thus  $[a^R, b^R] = [j_*a^L, j_*b^L] = j_*[a^L, b^L] = j_*[a, b]^L = -[a, b]^R$ . One also has  $[a^L, b^R] = 0$ . To see this we note that the map  $\mathfrak{g} \to C^\infty(TG)$  given by  $a \mapsto a^L|_g = \frac{d}{dt}(g\gamma(t))$  exponentiates to a right action  $R_{\gamma(t)}$  similarly  $a^R$  exponentiates to a left action and so  $[a^L, b^R] = 0$ . We now define  $Ad_g: \mathfrak{g} \to \mathfrak{g}$  by  $Ad_g(X) = (R_{g^{-1}})_*(L_g)_*$ . Equivalently  $a^R|_g = (Ad_{g^{-1}}a)^L|_g$ . We define  $ad_X = d(Ad_g)_0 = [X, \cdot]$ .

**Lemma 1.** If  $\rho \in \Omega^k(G)$  is bi-invariant then  $d\rho = 0$ 

*Proof.* If  $\rho$  is left invariant then  $\rho \in \wedge^k \mathfrak{g}^*$  and so

$$d\rho(X_0,\ldots,X_k) = \sum_i (-1)^i X_i \rho(X_0,\ldots,\hat{X}_i,\ldots,X_k) + \sum_{i,j} (-1)^{i+j} \rho([X_i,X_j],X_0,\ldots,X_k)$$

, where we have chosen  $X_0, \dots X_k$  to be left invariant so the first sum is zero . On the other hand right invariance tells us that for all  $X, \sum \rho(X_1, \dots, [X, X_i], \dots, X_k) = 0$ .

**Problem.** Show how the statement above implies that  $d\rho = 0$ .

We define  $Cartan\ one-forms$  to be forms  $\theta^L, \theta^R \in \Omega^1(G,\mathfrak{g})$  by  $\theta^L_g(v) = (L_{g^{-1}})_*v \in \mathfrak{g}$ . and  $\theta^R_g(v) = (R_{g^{-1}})_*v \in \mathfrak{g}$ . So  $\theta^L_x \circ (L_{g^{-1}})_* = \theta^L_{gx}$ . Thus  $\theta^L$  is left invariant as  $\theta^R$  is right invariant. For  $G = Gl_n$ ,  $\mathfrak{g} = M_n$  one has  $\theta^L = g^{-1}dg$  and  $\theta^R = dgg^{-1}$ . Now if  $g = [g_{ij}]$  that is  $g_{ij}$  are coordinates one gets matrix of one-forms  $[g_{ij}]^{-1}[dg_{ij}]$ . Then  $(\sigma g)^{-1}d(\sigma g) = g^{-1}\sigma^{-1}\sigma dg = g^{-1}dg$ , and so it is left invariant (similarly one can check that the obvious definition is indeed right invariant). At  $1 \in GL_n$  one has  $\mathfrak{g}$  consisting of  $n \times n$  matrices  $\{[a_{ij}]\}$  here we make think of  $[a_{ij}] = \sum_{i,j} a_{ij} \frac{\partial}{\partial g_{ij}}$ . so  $g^{-1}dg(\sum_{i,j} a_{ij} \frac{\partial}{\partial g_{ij}}) = a_i j$ , so  $g^{-1}dg|_e = Id : \mathfrak{g} \to \mathfrak{g}$ . This is also true for  $\theta^L$  and  $\theta^R$ .

## 9 Lecture 9 (Notes: K. Venkatram)

Last time, we talked about the geometry of a connected lie group G. Specifically, for any a in the corresponding Lie algebra  $\mathfrak{g}$ , one can define  $a^L|_g = L_{g*}a$  and choose  $\theta^L \in \Omega^1(G,\mathfrak{g})$  s.t.  $\theta^L(a^L) = a$ . For instance, for  $\mathrm{GL}_n$ , with coordinates  $g = [g_{ij}]$ , one has  $\theta^L = g^{-1}dg$ , and similarly  $\theta^R = dgg^{-1}$ . This implies that  $dg \wedge \theta^L + gd\theta^L = 0 \implies d\theta^L + \theta^L \wedge \theta^L = 0 \implies d\theta^L + \frac{1}{2}[\theta^L, \theta^L] = 0$ , the latter of which is the Maurer-Cartan equation.

**Problem.** 1. Extend this proof so that it works in the general case.

- 2. Show  $j^*\theta^R = -\theta^L$ .
- 3. Show  $d\theta^R \frac{1}{2}[\theta^R, \theta^R] = 0$ .
- 4. Show  $\theta^R(a^L)|_q = \text{Ad }_q a \forall a \in \mathfrak{g}, g \in G$ .

#### 9.1 Bilinar forms on groups

Let G be a connected real Lie group, B a symmetric nondegenerate bilinear form on  $\mathfrak{g}$ . This extends to a left-invariant metric on G, and B is invariant under right translation

 $\Leftrightarrow B([X,Y],Z) + B(Y,[X,Z]) = 0 \forall X,Y,Z.$  If this is true, we obtain a bi-invariant (pseudo-Riemannian) metric on G.

**Remark.** Geodesics through e are one-parameter subgroups  $\Leftrightarrow B$  is bi-invariant. See Helgason for Riemannian geometry of Lie groups and homogeneous spaces.

**Example.** Let B be the Killing form on a semisimple Lie group, i.e.  $B(a,b) = \text{Tr}_g(\text{ad}_a \text{ad}_b)$  for  $\mathfrak{s}|_m, \mathfrak{s} \circ m, \mathfrak{s}p_m$  a constant multiple of Tr(X,Y). Now, we can form the Cartan 3-form

$$H = \frac{1}{12} B(\theta^L, [\theta^L, \theta^L]) = \frac{1}{12} B(\theta^R, [\theta^R, \theta^R])$$
 (7)

This H is bi-invariant, and thus closed. When G is simple, compact, and simply connected, the Killing form gives  $\lambda[H]$  as a generator for  $H^3(G,\mathbb{Z})=\mathbb{Z}$ . (See Brylinski.) For instance, given  $\mathfrak{g}=\mathfrak{s}|_n, \theta^L=g^{-1}dg$ , one has  $H=\mathrm{Tr}(\theta^L\wedge\theta^L\wedge\theta^L)$  i.e.  $H=\mathrm{Tr}(g^{-1}dg)^3$ .

#### 9.1.1 Key calculation

Let  $m, p_1, p_2: G \times G \to G$  be the multiplication and projection maps respectively. Then

$$m^*H = \text{Tr}((gh)^{-1}d(gh))^3 = \text{Tr}(h^{-1}g^{-1}(gdh + dgh))^3$$
  
= \text{Tr}(h^{-1}gh)^3 + \text{Tr}(g^{-1}dg)^3 + \text{Tr}((dhh^{-1})^2g^{-1}dg) + \text{Tr}(dhh^{-1}(g^{-1}dg)^2) (8)

Now, define  $\theta = dhh^{-1}$ ,  $\Omega = g^{-1}dg$ , so  $d\theta = \theta \wedge \theta$  and  $d\Omega = -\Omega \wedge \Omega$ . Then

$$d\operatorname{Tr}(dhh^{-1}g^{-1}dg) = d\operatorname{Tr}(\theta \wedge \Omega) = \operatorname{Tr}(d\theta \wedge \Omega - \theta \wedge d\Omega)$$
  
=  $\operatorname{Tr}(\theta \wedge \theta \wedge \Omega + \theta \wedge \Omega \wedge \Omega)$  (9)

So,  $m^*H - p_1^*H - p_2^*H = d\tau$ , where  $\tau = \text{Tr}(dhh^{-1}g^{-1}dg) = B(p_1^*\theta^L, p_2^*\theta^R) \in \Omega^2(G \times G)$ . Now, recall that given a metric  $g: V \to V^*$ , we have a decomposition  $V \oplus V^* = C_+ \oplus C_-$  for  $C_\pm = \Gamma_\pm$ . Moreover, any Dirac structure  $L \subset V \oplus V^*$  can be written as the graph of  $A \in O(V, \mathfrak{g})$  thought of as  $A: C_+ \to C_-$ . NOw, for  $X \in V$ , let  $X^\pm = X \pm gX \in C_\pm$ . Then  $L_\pm^A = \{X^+ \pm (AX)^- | X \in V\}$  are the Dirac structures. Note that

$$\langle X^{+} \pm (AX)^{-}, X^{+} \pm (AX)^{-} \rangle = g(X, X) - g(AX, AX) = 0$$
 (10)

Let B be a bi-invariant metric on G. Then the map  $A_x = L_{x^{-1}*}R_{x*}: T_xG \to T_xG, a^L \mapsto a^R$  is orthogonal for B and  $\mathrm{ad}(G)$ -invariant, since

$$T_{x}G \xrightarrow{A_{x}} T_{x}G$$

$$\underset{\text{ad}_{g_{*}}}{\text{ad}_{g_{*}}} \bigvee_{\text{ad}_{g_{*}}} T_{gxg^{-1}}G$$

$$(11)$$

where  $ad_{g*} = L_{g*}R_{g^{-1}*}$ . Thus, we find that

$$\operatorname{ad}_{g*} A_x \operatorname{ad}_{g*}^{-1} = L_g R_{g^{-1}} R_x L_{x^{-1}} R_g L_{g^{-1}} = L_{g^{-1} x^{-1} g} R_{g x g^{-1}} = A_{g x g^{-1}}$$
(12)

Overall,  $L_{\pm}(A)$  are  $\mathrm{ad}(G)$ -invariant almost Dirac structures in  $(T \oplus T^*)(G)$ .  $T_xG$  is spanned by the  $a^L$ , so  $L_+$  is spanned by  $(a^L)^+ + (a^L)^- = a^L + B(a^L) + a^r - B(a^R)$  and  $L_+ = \langle a^L + a^R + B(a^L - a^R) \rangle$ . Recall that  $\theta^L(a^L) = a$  so  $\langle a^L + a^R + B(a^L - a^R) \rangle = \langle a^L + a^R + B(\theta^L - \theta^R, a) \rangle$ . Similarly,  $L_- = \langle a^L - a^R + B(\theta^L + \theta^R, a) \rangle$ .

**Remark.** Since  $a^L - a^R$  generates the adjoint action,  $[a^L - a^R, b^L - b^R] = [a, b]^L - [a, b]^R$ . But  $[a^L + a^R, b^L + b^R] = [a, b]^L + [a, b]^R$  is not integrable.  $L_-(A)$  is integrable, however, w.r.t. the Courant bracket twisted by  $H = B(\theta^L, [\theta^L, \theta^L])$ .

## 10 Lecture 10 (Notes: K. Venkatram)

Last time, we defined an almost Dirac structure on any Lie group G with a bi-invariant metric B by

$$L_C = \langle a^L - a^R + B(a^L + a^R) | a \in \mathfrak{g} \rangle \tag{13}$$

#### 10.1 Integrability

**Lemma 2.**  $d(B(a^L))(x^L, y^L) = x^L B(a^L, y^L) - y^L B(a^L, x^L) - B(a^L, [x^L, y^L]) = -i_{a^L} H(x^L, y^L)$ , where  $H(a, b, c) = B(a^L, [b^L, c^L])$ .

**Problem.** Show that  $B(\theta^L, [\theta^L, \theta^L])(a^L, b^L, c^L) = 6B(a^L, [b^L, c^L])$ .

Note also that

$$dB(a^R)(x^R, y^R) = -B(a^R, [x^R, y^R]) = i_{a^R}H(x^R, y^R)$$
(14)

Now,

$$[a^{L} - a^{R} + B(a^{L} + a^{R}), b^{L} - b^{R} + B(b^{L} + b^{R})]_{0} = [a, b]^{L} - [a, b]^{R} - i_{b^{L} - b^{R}} dB(a^{L} + a^{R}) + L_{a^{L} - a^{R}} B(b^{L} + b^{R})$$

$$= [a, b]^{L} - [a, b]^{R} + i_{b^{L} - b^{R}} i_{a^{L} - a^{R}} H + B([a, b]^{L} + [a, b]^{R})$$

$$(15)$$

Corollary 3.  $L_C$  is involutive under  $[,]_H$ .

Comments about the Cartan-Dirac structure:

- 1.  $a^L a^R$  generates the adjoint action so generalized, and  $\pi L_C = \Delta$  is a foliation by the conjugacy classes.
- 2.  $T^*$  component is  $B(a^L + a^R)$ , which spans  $T^*$  whenever  $\mathfrak{g} \to T_g^*$ ,  $a \mapsto a^L + a^R$  is surjective  $\Leftrightarrow$  (ad<sub>g</sub> + 1 is invertible. This is true, in particular, for an open set containing  $e \in G$ .

In this region,  $L_c = \Gamma_{\beta}$  for an *H*-twisted Poisson structure.

- 1. Determine explicitly the bivector  $\beta$  when it is defined.
- 2. For  $G = SU(2) = S^3$ , describe the conjugacy classes and the locus where  $ad_g + 1$  is invertible, rank 2, rank 1, and rank 0.
- 3. Determine the Lie algebroid cohomology  $H^*(L_c)$ . Hint:  $\mathfrak{g} \to L_c, a \mapsto a^L a^R + B(a^L + a^R)$  is bracket-preserving.

#### 10.2 Dirac Maps

A linear map  $f: V \to W$  of vector spaces induces a map  $f_*: \text{Dir}(V) \to \text{Dir}(W)$  (the forward Dirac map) given by  $f_*L_V = \{f_*v + \eta \in W \oplus W^* | v + f^*\eta \in L_V\}$  and a map  $f^*: \text{Dir}(W) \to \text{Dir}(V)$  (the backward Dirac map) given by  $f^*L_W = \{v + f^*\eta \in V \oplus V^* | f_*v + \eta \in L_W\}$ .

#### Example.

 $\beta \in \bigwedge^2 V$ . Then

$$f_*\Gamma_\beta = \{f_*v + \eta | v + f^*\eta = \beta(\xi) + \xi \forall \xi \in V^*\} = \{f_*\beta f^*\eta + \eta | \eta \in W^*\}$$

$$= \{(f_*\beta)(\eta) + \eta\} = \Gamma_{f_*\beta}$$
(16)

so  $f_*$  coincides with the usual pushforward.

 $L = L(E, \epsilon), f : E \hookrightarrow V, \epsilon \in \bigwedge^2 E^*$ . Then L is precisely  $f_*\Gamma_\epsilon$  via the pushforward  $E \oplus E^* \to V \oplus V^*$ .

In general, 
$$L = L(F, \gamma), F \subset V^*, \gamma \in \bigwedge^2 F^*$$
 is equivalent to specifying  $(C = \text{Ann } F = L \cap V, \gamma \iota \bigwedge^2 F^* = \bigwedge^2 (V/L \cap V) = \bigwedge^2 (V/C))$ . Note that  $(f_*L_V) \cap W = f_*(L_V \cap V)$ .

**Problem.**  $f_*L(C,\gamma) = L(f_*C, f_*\gamma)$ .

This proves that pushforward commutes properly with composition.

#### 10.3 Manifolds with Courant Structure

Let  $(M, H_M)$ ,  $(N, H_N)$  be manifolds equipped with  $H \in \Omega^3$ )cl-structure.

**Definition 17.** A morphism  $\Phi:(M,H_M)\to (N,H_N)$  is a pair  $(\phi,B)$  for  $\phi:M\to N$  a smooth map and  $B \in \Omega^2(M)$  s.t.  $\phi^*H_N - H_M = dB$ , i.e. B gives an isomorphism  $\phi^*G_N \to G_M$ .

Now, suppose that  $L_M \subset TM \oplus T^*M, L_N \subset TN \oplus T^*N$  are Dirac structures.

**Definition 18.**  $\Phi$  is a Dirac morphism  $\Leftrightarrow \phi_* e^B L_M = L_N$ .

If  $L_M$  is transverse to  $T^*M$ , then a Dirac morphism to  $(N, H_N, L_N)$  is called a *Dirac brane* for N: this object is important because  $\phi^*G_N$  is trivial.

**Example.** Let  $L_N$  be a Dirac structure, and let  $M \subset N$  be a leaf of  $\Delta = \pi L_N$ . Then  $L_N = L(\Delta, \epsilon \in \bigwedge^2 \Delta^*)$  and so  $\epsilon \in \Omega^2(M)$ . Furthermore, integrability means that  $d\epsilon = H|_M$ , hence  $(M,\epsilon) \to (N,H,L)$  is a Dirac brane. So any Dirac manifold is foliated by Dirac branes, and for G, is foliated by conjugacy classes C and 2-forms  $\epsilon \in \Omega^2(C)$  called GHJW (Guruprasad-Huebschmann-Jeffrey-Weinstein) 2-forms.

**Theorem 7.**  $(m,\tau): (G\times G, p_1^*H + p_2^*H) \to (G,H)$  is a Dirac morphism from  $L_C\times L_C\to L_C$ , i.e.  $m_*e^{\tau}(L_C\times L_C)=L_C.$ 

*Proof.* Set  $\rho(a) = a^L - a^R$ ,  $\sigma(a) = B(a^L + a^R)$ , so  $[\rho(a), \rho(b)] = \rho([a, b])$ ,  $[\rho(a), \sigma(b)] = \sigma([a, b])$ , and  $d\sigma(a) = -i_{\rho(a)}H$ . Then

$$e^{\tau}(L_C \times L_C) = \langle (\rho(a), \rho(b)), (\sigma(a), \sigma(b)) + i_{\rho(a), \rho(b)} \tau \rangle$$
(17)

We want to show that this object contains  $L_C$ , so choose  $(X,\xi) \in L_C|_{gh}$ ,  $X = \rho(x)$ ,  $\xi = \sigma(x)$ . Want to find  $a, b \text{ s.t. } X = m_*(\rho(a), \rho(b)) \text{ and } m^*\sigma(x) = (\sigma(a), \sigma(b)) + i_{\rho(a), \rho(b)}\tau.$ 

I  $m_*|_{(a,h)} = [R_{h*}, L_{a*}]$  and

$$m_* \begin{pmatrix} \rho(x)_g \\ \rho(x)_h \end{pmatrix} = \begin{pmatrix} R_{h^*} & L_{g^*} \end{pmatrix} \begin{pmatrix} (L_{g^*} - R_{g^*})x \\ (L_{h^*} - R_{h^*})x \end{pmatrix}$$

$$= (R_{h^*}(L_{g^*} - R_{g^*}) + L_{g^*}(L_{h^*} - R_{h^*}))x = \rho(x)_{gh}$$
(18)

II Want to show  $m^*\sigma(x)_{gh} = (\sigma(a)_g, \sigma(b)_h) + i_{\rho(a)_g, \rho(b)_h}\tau$ . At gh, we have that

$$m^* \sigma(x) \begin{pmatrix} a^R \\ b^L \end{pmatrix} = \sigma(x) (R_{h*} a^R + L_{g*} b^L) = \sigma(x) (a^R + b^L) = B(x^L - x^R, a^R + b^L)$$
 (19)

Then

$$(\sigma(x), \sigma(x)) \begin{pmatrix} a^R \\ b^L \end{pmatrix} = \sigma(x)_g(a^R) + \sigma(x)_h(b^L)$$
(20)

and the rest follows.

This leads to a fusion operation on Dirac morphisms: given  $\Phi_1: M_1 \to G, \Phi_2: M_2 \to G$ , composing the product with  $(m, \tau)$  gives  $\Phi_1 \circledast \Phi_2: M_1 \times M_2 \to G$ .

**Example.** Given two copies of the map  $m: G \times G \to G$ , obtain  $m \circledast m: G^4 \to G$ : more generally, get Dirac morphisms  $M^{\circledast h}: G^{2h} \to G$ . This is used by AMM to get a symplectic structure on the moduli space of flat G-connections on a genus h Riemann surface.

By Freed-Hopkins, fusion on branes implies a form of fusion on  $K_G^{\tau}(G)$ .

## 11 Lecture 11(Notes: K. Venkatram)

## 11.1 Integrability and spinors

Given  $L \subset T \oplus T^*$  maximal isotropic, we get a filtration  $0 \subset K_L = F^0 \subset F^1 \subset \cdots \subset F^n = \Omega^*(M)$  via  $F^k = \{\psi : \bigwedge^{k+1} L \cdot \psi = 0\}$ . Furthermore, for  $\phi \in K_L$ , we have

$$X_1 X_2 d\phi = [[d, X_1], X_2]\phi = [X_1, X_2]\phi$$
(21)

for all  $X_1, X_2 \in L$  (where  $d = d_H$ ). Thus, in general,  $d\phi \in F^3$ , and L is involutive  $\Leftrightarrow d\phi \in F^1$ . Now, assume  $d(F^i) \subset F^{i+3}$  (and in  $F^{i+1}$  if L is integrable)  $\forall i < k$  and  $\psi \in F^k$ . Then

$$[X_1, X_2]\psi = [[d, X_1], X_2]\psi = dX_1X_2\psi + X_1dX_2\psi - X_2dX_1\psi - X_2X_1d\psi X_1X_2d\psi = -dX_1X_2\psi - X_1dX_2\psi + X_2dX_1\psi + [X_1, X_2]\psi$$
(22)

Note that, in the latter expression, each of the parts on the RHS have degree (k-1)+2=k+1, so  $d\psi \in F^{k+1}$  if L is integrable and  $F^{k+3}$  otherwise.

Next, suppose that the Courant algebroid E has a decomposition  $L \oplus L'$  into transverse Dirac structures.

- 1. Linear algebra:
  - $L' \cong L^* \text{ via } \langle \cdot, \cdot \rangle$ .
  - The filtration  $K_L = F^0 \subset F^1 \subset \cdots \subset F^n$  of spinors becomes a  $\mathbb{Z}$ -grading  $K_L \oplus (L' \cdot K_L) \oplus \cdots \oplus (\bigwedge^k L' \cdot K_L) \oplus \cdots \oplus (\det L' \cdot K_L)$ , i.e.  $\bigoplus (\bigwedge^k L^*)K_L$ .

**Remark.** Note that  $L' \cdot (\det L' \cdot K_L) = 0$ , so  $\det L' \cdot K_L = \det L^* \otimes K_L = K_{L'}$ .

Thus, we have a  $\mathbb{Z}$  grading  $S = \bigoplus_{k=0}^{n} \mathcal{U}_k$ .

• If the Mukai pairing is nondegenerate on pure spinors, then  $K_L \otimes K_{L'} = \det T^*$ .

2. Differential structure: via the above grading, we have  $F^k(L) = \bigoplus_{i=0}^k \mathcal{U}_i, F^k(L') = \bigoplus_{i=0}^k \mathcal{U}_{n-i}$ , so  $d(\mathcal{U}_k) = d(F^k(L) \cap F^{n-k}(L')$ . By parity,  $d\mathcal{U}_k \cap \mathcal{U}_k = 0$ , so a priori

$$d = (\pi_{k-3} + \pi_{k-1} + \pi_{k+1} + \pi_{k+3}) \circ d = T' + \partial' + \partial + T$$
(23)

**Problem.** Show that  $T': \mathcal{U}_k \to \mathcal{U}_{k-3}, T: \mathcal{U}_k \to \mathcal{U}_{k+3}$  are given by the Clifford action of tensors  $T' \in \bigwedge^3 L, T \in \bigwedge^3 L^*$ .

**Remark.** This splitting of  $d = d_H$  can be used to understand the splitting of the Courant structure on  $L \oplus L^*$ . Specifically,  $d^2 = 0 \Longrightarrow$ 

$$-4 T'\partial' + \partial'T' = 0$$

$$-2 (\partial')^2 + T'\partial + \partial T'$$

$$0 \partial\partial' + \partial'\partial + TT' + T'T$$

$$2 \partial^2 + T\partial' + \partial'T$$

$$4 T\partial + \partial T = 0$$

$$(24)$$

### 11.2 Lie Bialgebroids and deformations

We can express the whole Courant structure in terms of  $(L, L^*)$ . Assume for simplicity that  $L, L^*$  are both integrable, so T = T' = 0. Then

- 1. Anchor  $\pi \to \text{a pair of anchors } \pi: L \to T, \pi': L' \to T$ .
- 2. An inner product  $\rightarrow$  a pairing  $L' = L^*, \langle X + \xi, X + \xi \rangle = \xi(X)$ .
- 3. A bracket  $\rightarrow$  a bracket [,] on L, [,], on L\*. Specifically, for  $x, y \in L, \phi \in \mathcal{U}_0$ ,

$$[x,y]\phi = [[d,x],y]\phi = xyd\phi = xy(\partial + T)\phi = xyT\phi = (i_x i_y T)\phi$$
(25)

The induced action on S is  $d_L\alpha = [\partial, \alpha]$ , giving us an action of L on  $L^*$  as  $\pi_{L^*}[x, \xi]$  for  $x \in L, \xi \in L^*$ . Expanding, we have

$$[x,\xi]\phi = [[\partial,x],\xi]\phi = \partial x\xi\phi + x\partial\xi\phi - \xi x\partial\phi - (i_x\xi)\partial\phi$$
  
=  $\partial(i_x\xi)\phi + x(d_L\xi)\phi - (i_x\xi)\partial\phi = (d_Li_x\xi + i_xd_L\xi)\phi = (L_x\xi)\phi$  (26)

If T = 0, then  $x \to L_x$  is an action (guaranteed by the Jacobi identity of the Courant algebroid). If L, L' are integrable,

$$L_x[\xi,\eta]_* = \pi_{L^*}[x,[\xi,\eta]] = \pi_{L^*}([[x,\xi],\eta] + [\xi,[x,\eta]])$$
(27)

**Problem.** This implies that  $d[\cdot,\cdot]_* = [d\cdot,\cdot]_* + [\cdot,d\cdot]_*$ .

As a result of these computations, we find that, for  $X, Y \in L, \xi, \eta \in L^*$ ,

$$[X + \xi, Y + \eta] = [X, Y] + [X, \eta]_L + [\xi, Y]_L + [\xi, \eta] + [\xi, Y]_{L^*} + [X, \eta]_{L^*}$$

$$= [X, Y] + L_{\xi}Y - i_{\eta}d_*X + [\xi, \eta] + L_X\eta - i_Yd\xi$$
(28)

There are no H terms since we assumed T = T' = 0. Overall, we have obtained a correspondence between transverse Dirac structures (L, L') and Lie bialgebroids  $(L, L^*)$  with actions and brackets  $L \to T, L^* \to T$  s.t. d is a derivation of  $[,]_*$ .

Finally, we can deform the Dirac structure in pairs. Specifically, for  $\epsilon \in C^{\infty}(\bigwedge^2 L^*)$  a small *B*-transform,  $e^{\epsilon}(L) = L_{\epsilon}$ , one can ask when  $L_{\epsilon}$  is integrable. We claim that this happens  $\Leftrightarrow d_L \epsilon + \frac{1}{2} [\epsilon, \epsilon]_* = 0$ . To see this, note that

$$\langle [e^{\epsilon}x, e^{\epsilon}y], e^{\epsilon}z \rangle = \langle [e^{\epsilon}x, e^{\epsilon}y]_{L}, e^{\epsilon}z \rangle + \langle [e^{\epsilon}x, e^{\epsilon}y]_{L^{*}}, e^{\epsilon}z \rangle$$

$$= (d_{L}\epsilon)(x, y, z) + \frac{1}{2}[\epsilon, \epsilon]_{*}(x, y, z)$$
(29)

via an analogous computation to that of  $e^BT$  and  $e^{\pi}T^*$  from before.

## 12 Lecture 12-17(Notes: K. Venkatram)

## 12.1 Generalized Complex Structures and Topological Obstructions

Let  $E \cong (T \oplus T^*, H)$  be an exact Courant algebroid.

**Definition 19.** A generalized complex structure (GCS) on E is an integrable orthogonal complex structure  $\mathbb{J}: E \to E$ , i.e. a map s.t.

- $\langle \mathbb{J}A, \mathbb{J}B \rangle = \langle A, B \rangle$
- $L = \text{Ker} (\mathbb{J} i1)$

**Note.** 1.  $\langle \mathbb{J}A, B \rangle = \langle \mathbb{J}^2A, \mathbb{J}B \rangle = -\langle A, \mathbb{J}B \rangle$ , and thus  $\langle \mathbb{J}\cdot, \cdot \rangle$  is a symplectic struction on E compatible with  $\langle, \rangle$ .

- 2. L is maximal isotropic and so is  $\overline{L}$ , and thus  $E = L \oplus \overline{L} = L \oplus L^*$  and we get a Lie bialgebroid.
- 3. V must be even dimensional: letting  $x \in V \oplus V^*$  be a null vector then  $\langle \mathbb{J}x, x \rangle = 0$  and  $\langle \mathbb{J}x, \mathbb{J}x \rangle = 0$ , so we can always enlarge a null set by 2 vectors; thus the maximal null set is even.

At the level of structure groups,  $(T \oplus T^*, \langle, \rangle)$ ,  $\mathbb{J}$  corresponds to  $O(2n, 2n) \to U(n, n) = O(2n, 2n) \cap GL(2n, \mathbb{C})$ .

**Problem.** Show that  $O(V \oplus V^*)$  acts transitively by conjugation on a set of GCS

$$S_{\mathbb{J}} \cong \frac{O(2n, 2n)}{U(n, n)} \tag{30}$$

**Example.** 1.  $\mathbb{J}=\left(\begin{array}{cc} J & \\ & -J^* \end{array}\right)$  acting on  $V\oplus V^*.$ 

- 2.  $\mathbb{J} = \begin{pmatrix} & -\omega^{-1} \\ \omega & \end{pmatrix}$  acting on  $V \oplus V^*$ .
- 3. Any conjugation  $A\mathbb{J}A^{-1}$ ,  $A \in O(2n, 2n)$ , e.g.  $e\mathbb{J}e^{-1}$ ,

$$\begin{pmatrix} 1 \\ B & 1 \end{pmatrix} \begin{pmatrix} J \\ -J^* \end{pmatrix} \begin{pmatrix} 1 \\ -B & 1 \end{pmatrix} = \begin{pmatrix} 1 \\ B & 1 \end{pmatrix} \begin{pmatrix} J & 0 \\ J^*B & -J^* \end{pmatrix} = \begin{pmatrix} J & 0 \\ J^*B + BJ & -J^* \end{pmatrix}$$

$$\begin{pmatrix} 1 \\ B & 1 \end{pmatrix} \begin{pmatrix} -\omega^{-1} \\ \omega \end{pmatrix} \begin{pmatrix} 1 \\ -B & 1 \end{pmatrix} = \begin{pmatrix} 1 \\ B & 1 \end{pmatrix} \begin{pmatrix} \omega^{-1}B & -\omega^{-1} \\ \omega & 0 \end{pmatrix} = \begin{pmatrix} \omega^{-1}B \\ -\omega^{-1} \\ \omega + B\omega^{-1}B & -B\omega^{-1} \end{pmatrix}$$

$$(31)$$

**Lemma 3.**  $O(n.n) \simeq O(n) \times O(n)$ .

Proof. Let  $C_+ \subset V \oplus V^*$  be positive definite and  $C_- = C_+^{\perp}$ . Then O(n,n) acts transitively on the space of all  $C_+$ , with stabilizer  $\operatorname{Stab}(C_+) = O(n) \times O(n)$ . Question: what is  $\frac{O(n,n)}{O(n) \times O(n)}$ ?  $C'_+$  (see diagram below) is given by  $A : \mathbb{R}^n \to \mathbb{R}^n, ||Ax|| < ||x|| \forall x$ , i.e.  $||A||_{op} < 1$ . Thus, it is the unit ball under the operator norm.

**Lemma 4.**  $U(n,n) \simeq U(n) \times U(n)$ 

Proof. We can enlarge  $\tilde{C}_+$  to  $C_+$  by adding  $V \perp \tilde{C}_+$  and  $\mathbb{J}V$ , and get complex decomposition  $E = C_+ \oplus C_+^{\perp} = C_+ + C_-$ . U(n,n) acts transitively on these spaces with stabilizer  $\operatorname{Stab}(C_+) = U(n) \times U(n)$ . As above, we obtain the unit ball in  $\mathbb{C}^n$ .

Thus, the existence of  $\mathbb{J}$  is topologically equivalent to the reduction to  $U(n) \times U(n)$ , i.e. complex structures  $\mathbb{J}_{\pm} := \mathbb{J}|_{C_{\pm}}$  on  $C_{+}$  and  $C_{-} = C_{+}^{\perp}$  (since the bundle of positive-definite subspaces is contractible).

**Note.** The projection  $\pi: C_{\pm} \to T$  is an isomorphism, so we obtain almost complex structure  $J_{\pm}: T \to T$ .

Thus M must be almost complex, and  $\mathbb{J}$  has two sets of Chern classes  $c_i^{\pm} \in H^{2i}(M,\mathbb{Z})$  associated to  $J_{\pm}$  (i.e.  $c_i^{\pm} = c_i(c_{\pm})$ ) and  $c(T \oplus T^*, \mathbb{J}) = c(C_+) \cup c(C_-)$ .

**Remark.** Topologically, E has structure group  $U(n,n) \simeq U(n) \times U(n)$ , so the bundle is classified by  $\psi: X \to B(U(n) \times U(n)) = BU(n) \times BU(n) = C^+ \times C^-$  with Chern classes  $\psi^*C^+, \psi^*C^-$ .

Now, spaces  $L \subset T \oplus T^*$  correspond to canonical bundes  $K_L \subset \Omega^*(M)$ .

**Proposition 5.** A generalized complex structure is equivalent to a complex Dirac structure of real index 0, i.e. to a Dirac structure  $L \subset (T \oplus T^*) \otimes \mathbb{C}$  s.t.  $\overline{L} \cap L = \{0\}$ .

*Proof.*  $\Leftarrow$ : given L, set  $\mathbb{J} = i|_L + (-i)|_{\overline{L}}$ , and obtain

$$\langle \mathbb{J}(\alpha + \overline{\beta}), \mathbb{J}(\alpha + \overline{\beta}) \rangle = \langle i\alpha - i\overline{\beta}, i\alpha - i\overline{\beta} \rangle = \langle \alpha, \overline{\beta} \rangle + \langle \overline{\beta}, \alpha \rangle = \langle \alpha + \overline{\beta}, \alpha + \overline{\beta} \rangle \tag{32}$$

 $\rightarrow$ : given  $\mathbb{J}$ , set  $L = \text{Ker } (\mathbb{J} - i1)$ , so

$$\langle \alpha, \beta \rangle = \langle \mathbb{J}\alpha, \mathbb{J}\beta \rangle = -\langle \alpha, \beta \rangle = 0 \tag{33}$$

Therefore,  $(T \oplus T^*) \otimes \mathbb{C} = L \oplus \overline{L}$ , and we obtain a transverse complex Dirac structure. This gives us a  $\mathbb{Z}$ -grading on  $S \otimes \mathbb{C} = \Omega^*(M, \mathbb{C})$  as

$$(K_L = \mathcal{U}_n) \oplus \mathcal{U}_{n-1} \oplus \cdots \oplus \mathcal{U}_{-n+1} \oplus (\mathcal{U}_{-n} = K_{\overline{L}})$$
(34)

with conjugation exchanging  $\mathcal{U}_k$  and  $\mathcal{U}_{-k}$ .

**Definition 20.**  $K_L = \mathcal{U}_{-n}$  is the canonical line bundle of the generalized complex structure.

Furthermore, the decomposition  $d_H = \partial + \overline{\partial}$  gives the general Dolbeault complex via  $\partial : \mathcal{U}_k \leftrightarrow \mathcal{U}_{k-1} : \overline{\partial}$ .

**Problem.** Use the Mukai pairing between  $K_L$  and  $\overline{K}_L$  to show that  $2c_1(K_L) = c_1^* + c_1^-$ .

#### 12.1.1 $\mathbb{Z}$ -grading on spinors

Let  $\mathbb{J}$  be a generalized complex structure: then  $\mathbb{J} \in \mathfrak{so}(T \oplus T^*)$ . The transformtation  $e^{\theta \mathbb{J}}$  behaves like  $e^{i\theta}$  and thus defines an  $S^1$  action on  $T \oplus T^*$  and thus, by the spin representation, on on  $\Omega^*(M)$  (in fact, we can imagine this as  $\cos \theta \cdot 1 + \mathbb{J} \cdot \sin \theta$ ). Just as  $(T \oplus T^*) \otimes \mathbb{C}$  decomposes as  $L \oplus \overline{L}$ , we have  $\mathbb{J}(x,\phi) = [\mathbb{J},x] \cdot \phi + x \cdot \mathbb{J}\phi$ , where  $[\mathbb{J},x]$  is the  $\mathfrak{so}$ -action. Thus, for an eigenvector  $x \in L$ ,  $\mathbb{J}x = ix$ , then  $\mathbb{J}x\phi = x\mathbb{J}\phi + i\phi$ . That is, the action of L increases by i, while  $\overline{L}$  decreases by i, giving us a diagram

$$K_{\overline{L}} = \mathcal{U}_{-n} \underbrace{\overset{L}{\smile}}_{\overline{L}} \mathcal{U}_{-n+1} \qquad \cdots \qquad \mathcal{U}_{n-1} \underbrace{\overset{L}{\smile}}_{\overline{L}} \mathcal{U}_{n} = K_{L}$$
 (35)

Since the eigenvalues are symmetric, they must be  $\{-ni, (-n+1)i, \dots, ni\}$ , with  $\mathcal{U}_k$  the ik-eigenspace of  $\mathbb{J}$ . Now, via the decomposition  $d_H = \partial + \overline{\partial}$ , we can form another real differential operator  $d^{\mathbb{J}} = [d, \mathbb{J}] = [\partial + \overline{\partial}, \mathbb{J}]$ . Applying this to  $\phi^k$  gives

$$[d, \mathbb{J}]\phi^k = ik(\partial + \overline{\partial})\phi - i(k+1)\partial\phi - i(k-1)\overline{\partial}\phi = i(\overline{\partial} - \partial)\phi$$
(36)

Thus,  $d^{\mathbb{J}} = i(\overline{\partial} - \partial)$ , and  $(d^{\mathbb{J}})^2 = 0$  as desired.

For each GCS, we obtain three complexes:  $(C^{\infty}(\bigwedge^* L^*), d_L)$  and the pair  $(\mathcal{U}^*, \overline{\partial}), (\mathcal{U}^*, \partial)$ .

**Proposition 6.**  $(C^{\infty}(\bigwedge^* L^*), d_L)$  is elliptic.

Recall that in general, this is not true. In particular, in the case of Poisson structures, the complex is infinite dimensional.

*Proof.* Since L is a Lie algebra, we obtain a symbol sequence

$$\bigwedge^{k-1} L^* \to^{S_{\xi}} \bigwedge^k L^* \to^{S_{\xi}} \bigwedge^{k+1} L^* \tag{37}$$

where  $S_{\xi}(\phi) = \pi^* \xi \wedge \phi$  for a given  $\xi \in T^*$  real. If  $\xi \neq 0$ , it can be decomposed as  $\alpha + \overline{\alpha} \in L \oplus \overline{L}$  with  $\alpha \neq 0$ . Moreover, for  $x \in L$ , we have

$$(\pi^*\xi)(x) = \xi(\pi x) = \langle \xi, x \rangle = \langle \alpha + \overline{\alpha}, x \rangle = \langle \overline{\alpha}, x \rangle \tag{38}$$

so  $\pi^* \xi = \overline{\alpha}$  is nonzero.

Corollary 4.  $H^*(L)$ ,  $H^*(\overline{L})$  are finite dimensional on compact generalized complex manifolds.

For the other complex, we have that  $d_H(f\phi) = df \wedge \phi + f d_H \phi = (d_L f + d_{\overline{L}} f) \phi + f d_H \phi$ , so that  $\overline{\partial}(f\phi) = (d_L f) \phi + f \overline{\partial} \phi$ .

**Problem.** Using the right derived bracket, show that  $(d_L x) = [\overline{\partial}, x]$  for  $x \in C^{\infty}(\bigwedge^k L^*)$ .

By the above, we have a symbol sequence  $\mathcal{U}^{k-1} \leftarrow^{S_{\xi}} \mathcal{U}^k \leftarrow^{S_{\xi}} \mathcal{U}^{k+1}$  given by the anihilation operator  $S_{\xi}(\phi) = \overline{\alpha}\phi$  which is also an exact sequence. Doing a similar procedure for  $\partial$ , and following the above logic (replacing the Clifford action with the wedge product), we obtain:

Corollary 5.  $H^*_{\overline{\partial}}(M), H^*_{\partial}(M)$  are finite dimensional for compact generalized complex manifolds.

**Remark.** One has a spectral sequence  $H_{\partial,\overline{\partial}}^*(M) \Longrightarrow H_{d_H}^*(M)$ . Moreover, this spectral sequence is trivial (i.e.  $H_{d_H}^* = \bigoplus H_{\overline{\partial}}^*(M)$  if the  $\partial \overline{\partial}$ -lemma holds for M: if  $\overline{\partial}\alpha = 0$  and  $\alpha = \partial\beta$ , then  $\alpha = \overline{\partial}\partial\gamma$  for some  $\gamma$ . In other words,

$$\operatorname{Im} \partial \cap \operatorname{Ker} \overline{\partial} = \operatorname{Ker} \partial \cap \operatorname{Im} \overline{\partial} = \operatorname{Im} \partial \overline{\partial}$$
 (39)

Finally, we obtain actions of  $H^*(L), H^*(\overline{L})$  on  $H^*_{\overline{\partial}}(M), H^*_{\partial}(M)$  respectively via

$$\overline{\partial}(x \cdot \phi) = (d_L x) \cdot \phi + (-1)^x x \cdot \overline{\partial}\phi, x \in \bigwedge^k L$$
(40)

**Problem.** Show the above statement.

This statement implies  $d_L x = [\overline{\partial}, x]$ , so  $d_L x = 0, \overline{\partial} \phi = 0 \implies \overline{\partial}(x \cdot \phi) = 0$ , making the action well-defined.

#### 12.1.2 Complex Case

Given an almost-complex structure J, we obtain a generalized complex structure  $\mathbb{J}_J = \begin{pmatrix} -J \\ J^* \end{pmatrix}$ . We claim that  $\mathbb{J}_J$  is integrable w.r.t.  $[,] \Leftrightarrow J$  is integrable. To see this, decompose  $L = T_{0,1} \oplus T_{1,0}^*$ , and choose elements  $x, y \in T_{0,1}, \xi, \eta \in T_{1,0}^*$ . One obtains

$$[x,y] + L_x \eta - i_y d\xi = [x,y] + i_x \overline{\partial} \eta - i_y \overline{\partial} \xi \tag{41}$$

where  $[x,y] \in T_{0,1} \Leftrightarrow J$  is integrable, and  $L_x \eta = i_x d\eta = i_x (\partial \eta + \overline{\partial} \eta) = i_x \overline{\partial} \eta$  because  $\partial \eta \in \bigwedge^2 T_{0,1}^*$  and thus does not survive  $i_x$ .

**Remark.** Adding a term  $i_x i_y H$  to the above expression, where  $H \neq 0$ , we find that  $i_x i_y H \in T_{1,0} \forall x,y \in T_{0,1} \Leftrightarrow H^{(0,3)} = 0$ , i.e. the gerbe is homogeneous. This is similar to the fact that  $F^{(2,0)} = 0$  for  $(L, \nabla)$  holomorphic.

We have two different complexes:

1. First, the complex  $(C^{\infty}(\bigwedge^* L^*), d_L)$ , where

$$\bigwedge^{k} L^{*} = \bigoplus_{p+q=k} (\bigwedge^{p} T_{1,0}) \otimes (\bigwedge^{p} T_{0,1}^{*})$$

$$\tag{42}$$

and the differential map is given by the individual partials

$$\overline{\partial}: C^{\infty}(\bigwedge^{p} T_{1,0} \otimes \bigwedge^{p} T_{0,1}^{*}) \to C^{\infty}(\bigwedge^{p} T_{1,0} \otimes \bigwedge^{p+1} T_{0,1}^{*})$$

$$\tag{43}$$

That is, each of the bundles  $\bigwedge^p T_{1,0}$  has a  $\overline{\partial}$  operator and  $d_L$  is their sum. This implies that

$$H^{k}(L) = \bigoplus_{p+q=k} H^{q}(\bigwedge^{p} T_{1,0}) = H^{0}(\wedge^{k} T_{1,0}) \oplus H^{1}(\bigwedge^{k-1} T_{1,0}) \oplus \cdots \oplus H^{k}(\emptyset)$$
(44)

2. Second, we have the complex  $(\mathcal{U}^k, \overline{\partial})$  as defined above. Note first that, being the canonical bundles, we have that  $K_L = \mathcal{U}^n = \bigwedge^n T_{1,0}^* = \Omega^{n,0}$  (similarly,  $K_{\overline{L}} = \mathcal{U}^{-n} = \Omega^{n,0}$ . By the decomposition  $L = T_{0,1} + T_{1,0}^*$ , we find that L acts on each  $\Omega^{k,l}$  by either increasing k or decreasing l, giving us our sequence as the decomposed Hodge diamond

$$K_{\overline{L}} = \Omega^{0,n} \begin{vmatrix} \Omega^{0,n-1} \\ \Omega^{1,n} \end{vmatrix} \cdots \begin{vmatrix} \Omega^{0,0} \\ \vdots \\ \Omega^{n,n} \end{vmatrix} \cdots \begin{vmatrix} \Omega^{n-1,0} \\ \Omega^{n,1} \end{vmatrix} \Omega^{n,0} = K_L$$
 (45)

That is,  $\mathcal{U}^k = \bigoplus_{p-q=k} \Omega^{p,q}$ , with the boundary maps given by the usual ones on  $\Omega$  and  $H^k_{\overline{\partial}}(M) = \bigoplus_{p-q=k} H^k_{\nabla d_{\overline{\partial}}}(M)$ .

#### 12.1.3 Symplectic Case

Given a symplectic form  $\omega$ , we obtain a generalized complex structure  $\mathbb{J}_{\omega} = \begin{pmatrix} -\omega^{-1} \\ \omega \end{pmatrix}$ . Given an i-eigenvector  $\begin{pmatrix} x \\ \xi \end{pmatrix}$ , we have

$$\omega(x) - \omega^{-1}(\xi) = ix + i\xi \implies i\eta = \omega(x) \tag{46}$$

Thus,  $L = \{x - i\omega(x) : x \in T \otimes \mathbb{C}\} = \Gamma_{-i\omega}$ , where  $\Gamma_{-i\omega}$  denotes the graph of  $-i\omega : T \otimes \mathbb{C} \to T^* \otimes \mathbb{C}$ , is a simple Dirac structure. Moreover,  $\Omega_{\sigma}$  is integrable w.r.t.  $[,]_H \Leftrightarrow d_H \sigma = 0$ . In our case, we have  $d(-\omega) = -H \wedge (-i\omega)$ , so  $d\omega$  and H must be 0 (i.e.  $\omega$  is symplectic). We again get two complexes

- 1.  $(C^{\infty}(\bigwedge^* L^*)d_L) \cong (C^{\infty}(\bigwedge^* T^* \otimes \mathbb{C}), d)$  is trivial, and  $H^k(L) \cong H^k_{dR}(M)$ . However, one does have a nontrivial Gerstenhaber structure  $(C^{\infty}(\bigwedge^* L^*), d_L, [,]_*)$ , and one has an equivalence between  $(L, \overline{L})$  and  $(T \otimes \mathbb{C}, \Gamma_{(\partial i\omega)^{-1}})$  (the Lie bialgebroid of a complex Poisson structure).
- 2. The ends of the complex  $(\mathcal{U}^k, \overline{\partial})$  can be simply exhibited as  $K_L = \langle e^{i\omega} \rangle, K_{\overline{L}} = \langle e^{-i\omega} \rangle$ . The next term can be computed via

$$\mathcal{U}^{-n+1} = (X - i\omega X)e^{-i\omega} = -i\omega(x) \wedge e^{-i\omega} - i\omega(x) \wedge e^{-i\omega} = e^{i\omega} \cdot \Omega^{1}$$
(47)

The higher terms are more complicated: given general invertible  $\sigma$ , the transformation  $e^{-\sigma}e^{\frac{\sigma^{-1}}{2}}$  on  $T \oplus T^*$  sends  $T^* \to \Gamma_{\sigma}$  (i.e.  $1 \to e^{\sigma}$ ) and  $T \to \Gamma_{-\sigma}$  (i.e.  $\Omega^n \to e^{-\sigma}$ ). Thus, we find that

$$\mathcal{U}^k = e^{i\omega} e^{\frac{\omega^{-1}}{2i}} \Omega^{n-k} \tag{48}$$

Letting  $L, \Lambda$  denote the maps  $\phi \mapsto \omega \wedge \phi, \phi \mapsto = -i_{\omega^{-1}} \phi$ , we obtain the expression  $\mathcal{U}^k = e^{iL} e^{-\frac{\Lambda}{2i}} \Omega^{n-k}$ . These maps arise via the decomposition of  $\mathbb{J}$  as  $\begin{pmatrix} & & \\ & -\omega & \end{pmatrix} + \begin{pmatrix} & \omega^{-1} & \\ & & \end{pmatrix}$ . Setting

$$H = [L, \Lambda] = \begin{pmatrix} 0 & 0 \\ 0 & -1 \end{pmatrix} - \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix} = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$$
 (49)

we find that [H, L] = -2L and  $[H, \Lambda] = 2\Lambda$ . These are precisely the  $\mathfrak{sl}_2\mathbb{R}$  commutator relations, giving us associated actions on the symplectic manifold. In particular, H acts as

$$H\phi = \frac{1}{2}\operatorname{tr}(\mathrm{id}) - (\mathrm{id}^*)\phi = \operatorname{sum}(n-k)\pi_k\phi$$
(50)

where  $\pi_k: \Omega \to \Omega^k$  is the projection. Via our decomposition of  $\mathbb{J}$ , we find that  $d^{\mathbb{J}} = [d, L + \Lambda] = [d, \Lambda] = \delta$  is a degree -1 operator with  $\delta^2 = 0$  (called the *symplectic adjoint of d*) and  $\overline{\partial} = d - i\delta : \mathcal{U}^k \to \mathcal{U}^{k-1}$ . Using an analogous  $d\delta$  (or  $\partial\overline{\partial}$ ) lemma for symplectic manifolds, we find that any cohomology class  $\alpha \in H^*_{dR}$  has a  $\delta$ -closed representation (since  $\delta\alpha = \delta d\gamma$  and  $d(\alpha - \gamma) = 0$ , implying that  $\delta(\alpha - d\gamma) = 0$ ). Thus, setting  $\tilde{\alpha} = \alpha - \gamma$ , we find that  $[d, \mathbb{J}] a l \tilde{p} h a = 0 \Leftrightarrow [d, \Lambda] \tilde{\alpha} = 0 \Rightarrow d(\Lambda \tilde{\alpha}) = 0$ . These statements combine to give an action of  $(L, \Lambda)$  on cohomology, i.e. an  $\mathfrak{sl}_2\mathbb{R}$  action on  $H^*(M)$ . Furthermore,  $L^{n-k}: H^k \to H^{2n-k}$  is an isomorphism, implying an equivalence between the  $d\delta$ -lemma and the *Lefshetz properlty* (see Cavalcanti thesis for  $\Leftarrow$ ).

### 12.2 Intermediate Cases

We have studied

$$\mathbb{J}_{J} = \begin{pmatrix} J & & \\ & -J^{*} \end{pmatrix}, \mathbb{J}_{\omega} = \begin{pmatrix} & -\omega^{-1} & \\ & \omega & \end{pmatrix}$$
 (51)

What about the intermediate cases?

- intermediate types and spinors
- Poisson structure
- Local form
- Examples of type jumping by deformation
- interpolation

Given a complex bundle  $T^* \to E \to^{\pi} T$ , let  $\mathbb{J} \circlearrowleft E$  with  $\mathbb{J}T^* = T^*$ . Then  $T^* \subset E$  is a complex subspace, and  $E/T^* = T$  obtains an almost complex structure J which is integrable. Furthermore,

$$(\mathbb{J}\xi)(X) = \langle \mathbb{J}\xi, \tilde{X} \rangle = -\langle \xi, \mathbb{J}\tilde{x} \rangle = \xi(Jx) = -J^*\xi(X)$$
(52)

i.e.  $\mathbb{J}|_{T^*} = -J^*$ .

#### 12.2.1 Complex and Symplectic Decompositions

Let  $S: T \to E$  be any splitting, i.e.  $\pi \circ s = id|_T$ . Then we can produce a complex splitting by averaging

$$\frac{1}{2}(S - \mathbb{J}sJ) = S' \tag{53}$$

Note.  $\pi(-\mathbb{J}sJ)(X) = \pi(-\mathbb{J}(s(JX))) = -J^2X = X$ , so  $-\mathbb{J}xJ$  is a splitting.

Observe that, in splitting  $S': E \to T \oplus T^*$ , we obtain  $\mathbb{J} = \begin{pmatrix} J & \\ & -J^* \end{pmatrix}$ .

**Problem.** Write  $\mathbb{J}$  is a non-complex splitting using S. Hint: what is the difference between the splittings S and  $-\mathbb{J}SJ$ ?

Finally, assume that  $\mathbb{J}T^* \cap T^* = \{0\}$ . Then  $E = T^* \oplus \mathbb{J}T^*$  and, in this splitting,

$$\mathbb{J} = \begin{pmatrix} & -\omega^{-1} \\ \omega & \end{pmatrix}$$
(54)

where  $\omega(X,Y) = \langle \mathbb{J}xX, xY \rangle$ .

#### 12.2.2 General case

In general,  $T^* + \mathbb{J}T^*$  is a complex subspace of E, as is  $T^* \cap \mathbb{J}^*T^* \subset T^* + \mathbb{J}T^* \subset E$ .

**Definition 21.**  $\Delta = \pi(T^* + \mathbb{J}T^*) = \pi \mathbb{J}T^*$ 

Note that

Ann 
$$\Delta = (T^* + \mathbb{J}T^*)^{\perp} \cap T^* = T^* \cap \mathbb{J}T^* \cap T^* = T^* \cap \mathbb{J}T^*$$
 (55)

is complex, and  $\frac{T^* + \mathbb{J}T^*}{\mathrm{Ann}\ \Delta} \cong \Delta^* \oplus_{\circlearrowleft \mathbb{J}} \Delta$  has symplectic structure. Also,  $E/(T^* + \mathbb{J}T^*) = T/\Delta$  has a complex structure, with complex dimension k (called the type).

**Theorem 8.** M is generally foliated by symplectic leaves with transverse complex structure.

Lemma 5.  $\mathbb{J}T^*$  is Dirac.

*Proof.* Observe first that the +i eigenspace is closed, i.e.

$$z - i \mathbb{J} z = [x - i \mathbb{J} x, y - i \mathbb{J} y]$$

$$= [x, y] - [\mathbb{J} x, \mathbb{J} y] - i([x, \mathbb{J} y] + [\mathbb{J} x, y])$$

$$[x, \mathbb{J} y] + [\mathbb{J} x, y] = \mathbb{J} [x, y] - \mathbb{J} [\mathbb{J} x, \mathbb{J} y]$$

$$[\mathbb{J} x, \mathbb{J} y] = [x, y] + \mathbb{J} ([x, \mathbb{J} y] + [\mathbb{J} x, y])$$
(56)

Thus,  $[\mathbb{J}\xi, \mathbb{J}\eta] = [\xi, \eta] + \mathbb{J}([\xi, \mathbb{J}\eta] + [\mathbb{J}\xi, \eta]) = \mathbb{J}\alpha$  (note that  $\pi\alpha = 0 \implies \alpha \in T^*$ ).

**Problem.** Show that  $N_{\mathbb{J}}(x,y) = [\mathbb{J}x,\mathbb{J}y] - \mathbb{J}[x,\mathbb{J}y] - \mathbb{J}[x,y] - [x,y]$  is tensorial and express it in terms of T,T'.

**Problem.**  $e^{\theta \mathbb{J}}T^*$  is Dirac  $\forall \theta$ . Hint:  $e^{\theta \mathbb{J}}T^* = ((\cos \theta \cdot 1) + (\sin \theta)\mathbb{J})(T^*) = (1 + \tan \theta \mathbb{J})T^*$ , and

$$[\xi + t \mathbb{J}\xi, \eta + t \mathbb{J}\eta] = t([\xi, \mathbb{J}\eta] + [J\xi, \eta]) + t^2 \mathbb{J}([\xi, \mathbb{J}\eta] + [\mathbb{J}\xi, \eta]) = (1 + t \mathbb{J})(t([\xi, \mathbb{J}\eta] + [\mathbb{J}\xi, \eta]))$$

$$(57)$$

**Lemma 6.** For small  $\theta$ ,  $e^{\theta J}T^*$  is a twisted Poisson structure in a splitting satisfying  $[\pi, \pi] = \bigwedge^3 \pi^* H$ .

Taking the derivative  $\frac{d}{d\theta}(e^{\theta \mathbb{J}}T^*)$  at  $\theta = 0$ , we obtain a tangent vector to  $\mathrm{Dir}(T \oplus T^*)$  at  $T^*$ : this is a skew map  $T^* \to T$ , i.e. an element  $\pi \in C^{\infty}(\bigwedge^2 T)$  s.t.  $[\theta \pi, \theta \pi] = \theta^3 \pi^* H \implies [\pi, \pi] = 0$ . Thus,  $\frac{d}{d\theta}(e^{\theta \mathbb{J}}T^*) = \pi$ , and  $\pi : \xi \mapsto \pi_T \mathbb{J} \xi$  is a Poisson structure, and we can split

$$\mathbb{J} = \begin{pmatrix} A & \pi \\ \sigma & -A^* \end{pmatrix}$$
(58)

The proof of the theorem follows from the following two observations:

- 1.  $\Delta = \text{Im}(\pi)$  is the image of a Poisson structure and thus a generalized distribution.
- 2. The symplectic structure on  $\Delta$  agrees with  $\pi$ , i.e. for  $\xi, \eta \in \Delta^*, \omega^{-1}(\xi, \eta) = \langle \mathbb{J}\xi, \eta \rangle = \pi(\xi, \eta)$ .

#### 12.2.3 Weinstein Splitting

Now, assume that the foliation is of locally constant rank near  $p \in M$ .

**Theorem 9** (Weinstein Splitting). For any  $p \in (M, \pi)$  Poisson, there exist coordinates  $(q_1, \ldots, q_r, p_1, \ldots, p_r, y_1, \ldots, y_\ell)$  s.t.

$$\pi = \sum_{i=1}^{r} \frac{\partial}{\partial q_i} \wedge \frac{\partial}{\partial p_i} + \sum_{i,j=1}^{\ell} \phi(y) \frac{\partial}{\partial y_i} \wedge \frac{\partial}{\partial y_j}$$
 (59)

with  $\phi(0) = 0$ .

**Note.** • When  $\ell = 0$ , this is the Darboux theorem.

• When the rank at p is locally constant,  $\phi = 0$  in a neighborhood of p. (Lie's Theorem)

If the rank is locally constant, then  $\mathbb{J}$  induces a complex structure J on  $\langle y_1, \dots, y_{2k} \rangle$  which is integrable since  $(\pi x, \pi y) = \pi(x, y)$ . Moreover, it is independent of the  $\{p_i, q_i\}$ , as

$$[\mathbb{J}dp_i, \mathbb{J}dy_j] = \mathbb{J}(d\{p_i, y_j\}) = 0 \tag{60}$$

and similarly for q. This gives us a local coordinate system  $\mathbb{R}^{2(n-k)} \times \mathbb{C}^k$ .

#### 12.2.4 Examples of type jumping

Given a complex structure  $\mathbb{J}_J=\left(\begin{array}{cc}-J&\\&J^*\end{array}\right)$  and spaces

$$L = T_{0,1} \oplus T_{1,0}^*, \bigwedge^2 L^* = \bigwedge^2 T_{1,0} \oplus (T_{1,0} \otimes T_{0,1}^*) \oplus \bigwedge^2 T_{0,1}^*$$
(61)

we can examine deformations  $\epsilon \in \bigwedge^2 L^*$  s.t.  $d\epsilon + \frac{1}{2}[\epsilon, \epsilon] = 0$ .

**Example.** For  $\epsilon \in \bigwedge^2 T_{1,0}$ ,

$$\left(\bigwedge^{2} T_{1,0} \otimes T_{0,1}^{*}\right) \oplus \bigwedge^{3} T_{1,0} \ni \overline{\partial} \epsilon + \frac{1}{2} [\epsilon, \epsilon] = 0 \implies \overline{\partial} \epsilon = 0, [\epsilon, \epsilon] = 0$$

$$(62)$$

i.e.  $\epsilon$  is a holomorphic Poisson structure.

By construction,

$$\begin{pmatrix} 1 & \overline{\epsilon} \\ \epsilon & 1 \end{pmatrix} \begin{pmatrix} L \\ \overline{L} \end{pmatrix} = 1 + \epsilon + \overline{\epsilon} \tag{63}$$

Letting  $P = \epsilon + \overline{\epsilon}$ , we obtain a transformation  $\mathbb{J}_J \mapsto e^p \mathbb{J} e^{-P}$ ,

$$\begin{pmatrix} 1 & P \\ & 1 \end{pmatrix} \begin{pmatrix} J & & \\ & -J^* \end{pmatrix} \begin{pmatrix} 1 & -P \\ & 1 \end{pmatrix} = \begin{pmatrix} 1 & P \\ & 1 \end{pmatrix} \begin{pmatrix} J & -JP \\ 0 & -J^* \end{pmatrix} = \begin{pmatrix} J & -JP - PJ^* \\ 0 & -J^* \end{pmatrix} = \begin{pmatrix} PJ & 2Q \\ & -J^* \end{pmatrix}$$
 (64)

for  $Q = i(\bar{\epsilon} - \epsilon)$ . Thus, the type is given by n - rkQ.

**Example.** On  $\mathbb{C}P^2$ ,  $\bigwedge^2 T_{1,0} = \mathcal{O}(3)$ , and  $\epsilon \in H^0(\mathcal{O}(3))$ .

#### 12.3 Spinorial Description

Recall that  $\mathbb{J}$  determines as is determined by the +i-eigenbundle L. Set  $pi: L \to T \otimes \mathbb{C}$  to be the map  $\pi(L) = E \subset T \otimes \mathbb{C}$ . Since  $L = L(E, \epsilon), k_L = \langle e^{\epsilon} \Omega \rangle$ , i.e.  $k_L$  is generated by products  $\phi = e^{B+i\omega}\theta_1 \wedge \cdots \wedge \theta_k$  when  $\langle \theta_1, \dots, \theta_k \rangle = \text{Ann } E$ .

Note. However,

- 1. Let  $\xi \in T^*$  be real: then  $\xi = \alpha + \overline{\alpha} \in L \oplus \overline{L} \implies \mathbb{J}\xi = i(\alpha + \overline{\alpha})$  and  $\pi(\alpha) + \pi(\overline{\alpha}) = 0 \implies \pi(\mathbb{J}\xi) = i\pi(\alpha \overline{\alpha}) = 2i\pi(\alpha) = -2i\pi(\overline{\alpha})$ . Therefore  $E \cap \overline{E} = \Delta \otimes \mathbb{C}$ , with Ann  $\Delta = \langle \Omega \wedge \overline{\Omega} \rangle$ , and k is the type of  $\mathbb{J}$ .
- 2.  $f^*\omega$  is nondegenerate on  $\Delta$ , as  $\langle \phi, \overline{\phi} \rangle \neq 0 \Leftrightarrow \langle e^{B+i\omega}\Omega, e^{B-i\omega}\overline{\Omega} \rangle \neq 0 \Leftrightarrow \langle e^{2i\omega}\Omega, \overline{\Omega} \rangle \neq 0 \Leftrightarrow \omega^{n-k} \wedge \Omega \wedge \overline{\Omega} \neq 0$ .

**Problem.** Show that  $\omega^{-1} = \pi|_{\Delta}$ .

Given coordinates  $(x_1, \ldots, x_{n-k}, p_1, \ldots, p_{n-k}, z_1, \ldots, z_k)$  for  $\mathbb{R}^{2(n-k)}_{\omega_0} \times \mathbb{C}^k$ ,  $\omega_0 = \omega|_{\Delta}$ ,  $\mathbb{J}$  has a general spinor  $\phi = e^{B+i\omega}dz_1 \wedge \cdots \wedge dz_k$  around each regular point. Here, we are fixing the splitting so that H = 0. Now,  $d\phi = \alpha \cdot \phi = (X + \xi) \cdot \phi = d(B + i\omega) \wedge \phi$ : by degree considerations,  $i_X\Omega = 0$  and  $i_X(B + i\omega) + \xi = 0$ , so  $d\phi = 0$  and  $d(B + i\omega) \wedge \Omega = 0$ , giving us  $\infty$ -integrability.

**Theorem 10.**  $\phi = e^{B' + i\omega_0} \Omega$  with B' closed, i.e.  $\mathbb{J}$  is equivalent to  $\mathbb{R}^{2(n-k)}_{\omega_0} \times \mathbb{C}^k$ .

*Proof.* The general strategy is to transfer to some  $e^{B+i\omega}\Omega$  and use the freedom available to make B closed. Using the splitting on  $\mathbb{R}^{2(n-k)}_{\omega_0} \times \mathbb{C}^k$ , we have a decomposition  $d = d_f + \partial + \overline{\partial}$ . Set  $A = B + i\omega$ : then A breaks up into a triangle

$$\begin{pmatrix}
A^{200} \\
A^{110} & A^{101} \\
A^{020} & A^{011} & A^{002}
\end{pmatrix}$$
(65)

which acts effectively via exponentiation on  $\Omega^{0k0}$ . Note that, via averaging, we have  $\omega_0 = \omega|_{\Delta} = \frac{i}{2}(A^{200} - \overline{A^{200}})$ . Our goal is to modify the triangle  $(A^{110}, A^{020}, A^{011})$  so that  $A^{101}, A^{002}$  enter only in the real part of A. To this end, let  $C^{011}$  be any real form, and set

$$A' = A^{200} + (A^{101} + \overline{A^{101}}) + (A^{002} + \overline{A^{002}}) + C^{011}$$

$$= \left(\frac{1}{2}(A^{200} + \overline{A^{200}}) + A^{101} + \overline{A^{101}} + A^{002} + \overline{A^{002}} + C^{011}\right) + \frac{1}{2}(A^{200} + \overline{A^{200}}) = B' + i\omega_0$$
(66)

The condition that  $dA \wedge \Omega = 0$  gives four constraints on the  $A^{ijk}$ :

$$(a)d_f A^{200} = 0$$

$$(b)\overline{\partial} A^{200} + d_f A^{101} = 0$$

$$(c)\overline{\partial} A^{101} + d_f A^{002} 0$$

$$(d)\overline{\partial} A^{002} = 0$$
(67)

The desire for B' to be closed requires  $(dB')^{012} = (dB')^{111} = 0$ , which gives the following two constraints:

$$\partial A^{002} + \overline{\partial}C = 0$$

$$\partial A^{101} + d_f C + \overline{\partial}A^{101} = 0$$
(68)

We obtain the desired C via the Dolbeault lemma. For the first constraint, note that (d)  $\implies A^{002} = \overline{\partial} \alpha^{001}$ . Thus

$$(1) \Leftrightarrow \overline{\partial}C + \partial\overline{\partial}\alpha = 0 \Leftrightarrow \overline{\partial}(C - \partial\alpha) = 0 \Leftrightarrow \overline{\partial}(C - \partial\alpha - \overline{\partial}\overline{\alpha}) = 0$$

$$\Leftrightarrow C - \partial\alpha - \overline{\partial}\overline{\alpha} = \overline{\partial}\psi \Leftrightarrow C = \partial\alpha + \overline{\partial}\overline{\alpha} + i\partial\overline{\partial}\chi$$

$$(69)$$

for  $\chi$  a real function. For the second constraint, note that (c) is true  $\Leftrightarrow 0 = \overline{\partial} A^{101} + d_f A^{002} = \overline{\partial} (A^{101} - d_f \alpha) \implies A^{101} = d_f \alpha + \overline{\partial} \beta^{100}$  for  $\beta$  a 100-form. This implies that

$$(2) \Leftrightarrow \partial(d_f \alpha + \overline{\partial}\beta) + \overline{\partial}(d_f \overline{\alpha} + \partial \overline{\beta}) + d_f(\partial \alpha + \overline{\partial}\overline{\alpha} + i\partial \overline{\partial}\chi) = 0 \Leftrightarrow \overline{\partial}\partial(\beta - \overline{\beta}) = \mathrm{id}_f \partial \overline{\partial}\chi$$
 (70)

Moreover, (b) is true  $\Leftrightarrow \overline{\partial}A^{200} + d_fA^{101} = 0 \Leftrightarrow d_f\overline{\partial}\beta = -\overline{\partial}A^{200}$ . Thus,  $d_f\overline{\partial}\partial(\beta - \overline{\beta}) = \overline{\partial}\partial(A^{200} - \overline{A^{200}}) = 0$ , so we can choose the desired  $\chi$ .

**Corollary 6.** A GCS on an exact Courant algebroid is locally equivalent, near a regular point, to  $\mathbb{R}^{2(n-k)}_{\omega_0} \times \mathbb{C}^k$ .

### 12.3.1 More Examples of Type Jumping

Recall that we say type jumping via the operator  $e^{\beta+\overline{\beta}}\mathbb{J}_J e^{-(\beta+\overline{\beta})}$ . We can see this behavior more explicitly using forms. Recall that a complex structure on  $\mathbb{C}^2$  a representation by a spinor  $\phi=dz_1\wedge dz_2$ . Let  $\beta\in H^0(\bigwedge^2T)$  be a holomorphic section, e.g.  $\beta=z_1\partial_1\wedge\partial_2$  (obviously holomorphic). Then

$$e^{\beta}\phi = e^{\beta + \overline{\beta}}\phi = dz_1 \wedge dz_2 + i_{z_1\partial_1 \wedge \partial_2}dz_1 \wedge dz_2 = z_1 + dz_1 \wedge dz_2 \tag{71}$$

At  $z_1 = 0$ , this gives the complex structure  $dz_1 \wedge dz_2$ . Outside  $z_1 = 0$ , we have  $z_1(1 + \frac{dz_1 + dz_2}{z_1}) \sim e^{B+i\omega}$ , where  $B + i\omega = \frac{dz_1 + dz_2}{z_1}$ .

#### 12.3.2 Interpolation

Suppose (g, I, J) is a Hyperk ahler structure, i.e. (I, g), (J, g) are K ahler and IJ = -JI. Then (K = IJ, g) is another integrable K ahler structure, and one obtains a family of complex structures  $\{aI + bJ + cK | a^2 + b^2 + c^2 = 1\}$  parameterized by  $S^2$ , all of which are K ahler w.r.t. g.

**Remark.** This places a strong constraint on g (reduction of holonomy, Ricci-flat metric, i.e. Einstein) but does not imply that the Riemann curvature is 0. The only known compact examples known are

- K3 surface
- Flat  $T^4$
- $Hilb^n(K3)$
- $\operatorname{Hilb}^n(T^4)$
- Two examples in dimensions 12 and 20 (O'Grady).

Setting  $\omega_J I = gJ, \omega_K = gK$ , one obtains

$$w_J I = gJI = -gIJ = I^*gJ = I^*\omega_J \tag{72}$$

Moreover, considering the GCSs

$$\mathbb{J}_{I} = \begin{pmatrix} I \\ -I^{*} \end{pmatrix}, \mathbb{J}_{\omega_{J}} = \begin{pmatrix} -\omega_{J}^{-1} \\ \omega_{J} \end{pmatrix}, \mathbb{J}_{\omega_{K}} = \begin{pmatrix} -\omega_{k}^{-1} \\ \omega_{k} \end{pmatrix}$$
(73)

one obtains the relations

$$\mathbb{J}_{I}\mathbb{J}_{\omega_{J}} = \begin{pmatrix} & -I\omega_{J}^{-1} \\ -I^{*}\omega_{J} \end{pmatrix} = \begin{pmatrix} & -\omega_{J}^{-1}I^{*} \\ -\omega_{J}I \end{pmatrix} = -\mathbb{J}_{\omega_{J}}\mathbb{J}_{I}$$
 (74)

Similarly,  $\mathbb{J}_I \mathbb{J}_{\omega_K} = -\mathbb{J}_{\omega_K} \mathbb{J}_I$  and  $\mathbb{J}_{\omega_J} \mathbb{J}_{\omega_K} = -\mathbb{J}_{\omega_K} \mathbb{J}_{\omega_J}$ , whereas  $\mathbb{J}_I \mathbb{J}_{\omega_I} = \mathbb{J}_{\omega_I} \mathbb{J}_I$ . Thus,  $(a\mathbb{J}_I + b\mathbb{J}_{\omega_K} + c\mathbb{J}_{\omega_J})^2 = -(a^2 + b^2 + c^2)$ , giving a 2-sphere of GCSs interpolating  $I \to \omega_J$ .

**Problem.** Show that the intermediate structures are all B-field transforms of symplectic forms.

**Note.** On  $\mathbb{C}P^2$ , for the complex case  $\mathbb{J}_J$ ,  $K = \Omega^n$ , so  $K = \emptyset(3)$  and  $c_1(K) = -3$ . For  $\mathbb{J}_{\omega}$ , on the other hand,  $K = \langle e^{i\omega} \rangle$  and  $c_1(K) = 0$ . So we see that we can never interpolate complex to symmetric. In fact, for any even general complex structure,

$$K_{\mathbb{J}} \subset \bigwedge^{ev} T^* \otimes \mathbb{C} = \bigwedge^0 \oplus \bigwedge^2 \oplus \bigwedge^4 \tag{75}$$

there is a canonical projection  $s: K_{\mathbb{J}} \to \bigwedge^0 = \mathbb{C}$  (i.e.  $s \in C^{\infty}(K_{\mathbb{J}}^*)$ ) which vanishes when type jumps off of zero. Hence, we see that for a generic GCS in four dimensions, the type change locus is PD to  $c_1(K)$ .

**Example.** In dimension 4, one has types  $\{0, 1, 2\}$ , so an odd GCS corresponds to a four-manifold foliated by 2-d symplectic leaves and transverse complex structure, e.g.  $\Sigma_{\omega} \times \Sigma_{J}$  or a symplectec surface bundle over a complex Riemann surface.

**Example.** In dimension 6, one has types  $\{0,1,2,3\}$ , and one can construct an odd GCS by deforming the complex structure by a holomorphic Poisson structure (here, the Poisson condition is nontrivial). 0-2 structures?

**Problem.** Construct an interesting even GCS on a compact 6-manifold.

We now consider examples on Hyperk ahler manifolds. Recall that, for a K ahler manifold one has maps

$$T \xrightarrow{g} T^* \tag{76}$$

s.t.  $J, \omega$  are integrable,  $g = -\omega J$ , and  $g^* = g \Leftrightarrow J^*\omega = -\omega J$ . Thus,

$$G = \mathbb{J}_{J}\mathbb{J}_{\omega} = \begin{pmatrix} -J & \\ J^{*} \end{pmatrix} \begin{pmatrix} -\omega^{-1} \\ \omega \end{pmatrix} = \begin{pmatrix} 0 & J\omega^{-1} \\ J^{*}\omega & 0 \end{pmatrix}$$
$$= \begin{pmatrix} g^{-1} \\ g \end{pmatrix} = \begin{pmatrix} -\omega^{-1} \\ \omega \end{pmatrix} \begin{pmatrix} -J & \\ J^{*} \end{pmatrix} = \mathbb{J}_{\omega}\mathbb{J}_{J}$$
(77)

is a generalized Riemannian metric. The integrability condition can be rephrased as  $\nabla I = 0$  or  $\nabla \omega = 0$ . As above, for a Hyperk ahler manifold, we have almost complex structures (I, J, K) which are K ahler w.r.t. g and satisfy quaternion relations, thereby giving us a 2-sphere of complex structures  $\{aI + bJ + cK\}$ . This gives us an integrable complex structure which is K ahler w.r.t. g for  $\{(a, b, c) \in S^2\}$ .

Now, the relations  $\nabla I = 0$ ,  $\nabla J = 0$ ,  $\nabla K = 0$  reduce the holonomy of our manifold: the first reduces it U(n), while the second reduces it to the quaternionic unitary group  $U(n)_I \cap U(n)_J = \operatorname{Sp}(n)$ . This is modeled as follows: set (V, I) to be a complex vector space, with dual  $V^*$  and anti-complex space  $\overline{V} \cong_{\mathbb{R}}$  with action  $i \cdot x = -ix$ . Then, in the category of vector spaces with  $\mathbb{C}$ -linear maps, one has a diagram

$$\overline{V} \xrightarrow{h} V^*$$

$$V$$
(78)

with Q a complex symplectic form and  $h = g + ig(J, \cdot)$  the induced hermitian metric. Note that J is "anti-linear", in the sense that  $Ji = -iJ \implies JI - iIJ$ . One thus finds that the holonomy reduction forces the Ricci flow to be trivial, though the whole Riemann tensor need not vanish.

Finally, recall that the only known compact examples are the K3 and  $T^4$  surfaces, the Hilbert schemes of both, and the two examples of O'Grady in dimensions 12 and 20. Except for the  $T^4$  and Hilb<sup>n</sup> $(T^4)$ , the metrics on these manifolds are not explicit, as they rely on Yau's existence theorem of Ricci flat metrics on K ahler manifolds with holomorphic trivial canonical bundle  $(Q \wedge \cdots \wedge Q \neq 0)$ .

#### 12.3.3 Intermediate Types

As earlier, given a Hyperk ahler structure (g, I, J, K = IJ) and setting  $\omega_I = gI, \omega_J = gJ, \omega_K = gK$ , we have an  $S^2$ -parameterized family of structures  $a\mathbb{J}_I + b\mathbb{J}_{\omega_J} + c\mathbb{J}_{\omega_K}$ . Moreover, observe that  $\mathbb{J}_I\mathbb{J}_{\omega_J} = -\mathbb{J}_{\omega_J}\mathbb{J}_I$ , so

$$\mathbb{J} = a\mathbb{J}_I + b\mathbb{J}_{\omega_J} = \begin{pmatrix} -aI & -b\omega_J^{-1} \\ b\omega_J & aI^* \end{pmatrix}$$
 (79)

is generalized almost-complex for  $a^2+b^2=1$ . It has Poisson structure  $-b\omega_J^{-1}=-\omega^{-1}$ , so  $\mathbb J$  could be a B-field transform

$$\begin{pmatrix} 1 \\ B & 1 \end{pmatrix} \begin{pmatrix} -\omega^{-1} \\ \omega \end{pmatrix} \begin{pmatrix} 1 \\ -B & 1 \end{pmatrix} = \begin{pmatrix} \omega^{-1}B & -\omega^{-1} \\ \omega + B\omega^{-1}B & -B\omega^{-1} \end{pmatrix}$$
(80)

of  $\mathbb{J}_{\frac{1}{\hbar}\omega_J}$ . This holds if  $b\omega_J^{-1}B = -aI$ , i.e.  $B = -\frac{a}{b}w_JI = \frac{a}{b}\omega_K$ .

**Problem.** Check that

$$\frac{1}{b}\omega_J + \left(\frac{a}{b}\right)^2 b\omega_K \omega_J^{-1} \omega_K = \frac{1 - a^2}{b^2} \omega_J = b\omega_J \tag{81}$$

Thus, we find that  $\mathbb{J}=e^{\frac{a}{b}\omega_k}\mathbb{J}_{\frac{1}{b}\omega_I}e^{-\frac{a}{b}\omega_K}$  is integrable.

In another direction, a small deformation of  $\mathbb{J}_I$  by a holomorphic Poisson structure is a *B*-symplectic structure, e.g. take  $\beta = (\omega_J + i\omega_K)^{-1}, \overline{\partial}\beta = 0, [\beta, \beta] = 0.$ 

**Problem.** Show that  $\omega_J + i\omega_K$  is a holomorphic, nondegenerate (2,0)-form and therefore  $\beta = (\omega_J + i\omega_K)^{-1}$  is a holomorphic, Poisson, nowhere-vanishing bivector field. Thus, the  $\beta$ -transform is of symplectic type: determine it explicitly.

### 12.3.4 Generalized K ahler Geometry

Starting with  $(I, \omega_I)$  in a Hyperk ahler manifold, one can do an infinitesimal deformation by a bivector  $t\omega_J^{-1}$  (the real part of the holomorphic Poisson structure  $(\omega_J + i\omega_K)^{-1}$ ). (...)

Thus, the generalized K ahler structure  $(\mathbb{J}_A, \mathbb{J}_B)$  induces a  $\mathbb{Z} \times \mathbb{Z}$ -grading on complex differential forms

$$S^{\cdot} \otimes \mathbb{C} = \bigoplus_{\substack{p+q \cong n \mod 2 \\ p+q \leq n}} \mathcal{U}^{p,q}$$
(82)

and that

$$d_H = \delta_+ + \delta_- + \overline{\delta}_- + \overline{\delta}_+ \tag{83}$$

maps  $\mathcal{U}^{p,q}$  to  $\mathcal{U}^{p+1,q+1} \oplus \mathcal{U}^{p+1,q+1} \oplus \mathcal{U}^{p+1,q-1} \oplus \mathcal{U}^{p-1,q+1} \oplus \mathcal{U}^{p-1,q-1}$ . Since  $\Delta_{d_H} = \frac{1}{4}\Delta_{\delta_{\pm}}(-)$ , we obtain the Hodge decomposition

$$H_H^*(M,\mathbb{C}) = \bigoplus \mathcal{H}^{p,q} \tag{84}$$

Now, recall that the key observation leading to the K ahler identities was  $*|_{\mathcal{U}^{p,q}} = i^{p+q}$ 

**Example.** Define the twisted Betti numbers to be the values  $b^{ev/od} = \dim H_H^{ev/od}(M)$ , where, if [H] = 0,  $b^{ev} = \sum_k b^{2k}$ ,  $b^{od} = \sum_k b^{2k+1}$ . Consider the four-dimensional case as given before: then, if the generalized K ahler form is of type (ev, ev), one finds that  $b^{od}$  must be even as well, since the action of complex conjugation is reflected through  $\mathcal{U}^{0,0}$ . Opposingly, if the generalized K ahler form is of type (od, od),  $b^{ev}$  must be even. In particular, this implies that on  $\mathbb{C}P^2$ , there are no (od, od) generalized K ahler structures (since  $b^{ev} = 1 + 1 + 1 = 3$ ).

Now, recall that  $*=(i)^{p+q}$  satisfies the identity  $\alpha(\alpha(*)\phi)=\star\phi$ : in four dimensions, this implies that  $\alpha(*)=(-1)^{4*3/2}*=*$  and  $\alpha(\phi)=\phi$  is degrees  $0,1,4,-\phi$  in degrees 2,3. Applying this to the (ev,ev) case, we find that  $\mathcal{U}^{0,0}=(\Omega^0+\Omega^4)_++\Omega^2_-$ , while  $\mathcal{U}^{-2,0}+\mathcal{U}^{0,2}+\mathcal{U}^{2,0}+\mathcal{U}^{0,-2}=(\Omega^0+\Omega^4)_-+\Omega^2_+$ . Opposingly, in the (od,od) case, we find that  $\mathcal{U}^{0,0}=(\Omega^{1,3})_-$ , while  $\mathcal{U}^{-1,1}\oplus\mathcal{U}^{1,-1}=\Omega^2_-+(\Omega^0+\Omega^4)_+$  and  $\mathcal{U}^{1,1}\oplus\mathcal{U}^{-1,-1}=\Omega^2_++(\Omega^0+\Omega^4)_-$ .

Finally, if [H] = 0, \* induces a splitting on  $H^2 = b_+^2 + b_-^2$ . Thus, in the (ev, ev) case,  $b_+^2$  is odd and  $b_1 = b_3$  is even, while in the (od, od) case, both  $b_\pm^2$  are odd, and just  $b_1$  is necessarily even. In particular, for the space  $\mathbb{C}P^2\#\mathbb{C}P^2\#\mathbb{C}P^2\#\mathbb{C}P^2$ , one has twisted Betti numbers 1, 0, 4, 0, 1.

### 12.4 Introduction to Hermitian Geometry

Let  $G = -\mathbb{J}_A \mathbb{J}_B$ : decomposing  $E = C_+ \oplus C_-$  into  $\pm$ -definite spaces, ones finds that  $C_\pm = \operatorname{Ker}\ (G \mp 1)$ , i.e.  $P_\pm = \frac{1 \pm G}{2}$  are the projection operators to  $C_\pm$ , so that  $P_\pm^2 = P_\pm$ . Recall that, given  $X \in T$ , one has a unique pair of lifts  $X^\pm$  to  $C_\pm$ . We previously obtained  $C_\pm = \operatorname{Gr}(b \pm g)$  in an isotropic splitting, so

$$g(X,Y) = \langle X^+, Y^+ \rangle = \langle X^-, Y^- \rangle \tag{85}$$

independent of the isotropy choice. Now, since G commutes with  $\mathbb{J}_A$  and  $\mathbb{J}_B$ , the  $C_{\pm}$  are complex sub-bundles, with  $\mathbb{J}_A = \mathbb{J}_B$  on  $C_+$  and  $\mathbb{J}_A = -\mathbb{J}_B$  on  $C_-$ . Via the isomorphism  $\pi: C_{\pm} \to T$ , any structure on  $C_{\pm}$  can be transported to T. In particular, the complex structure on  $C_{\pm}$  gives two almost complex structures  $J_+, J_-$  on T, both of which are g-orthogonal (since  $\mathbb{J}_A$  preserves  $\langle \rangle$  on  $C_{\pm}$ ). That is, we obtain almost-Hermitian structures  $(g, J_+), (g, J_-)$  on T.

**Proposition 7.** Choose the unique splitting for E where b = 0, i.e.  $E = (GT^*) \oplus T^* = T \oplus T^*$ . Then  $(\mathbb{J}_A, \mathbb{J}_B)$  can be reconstructed from  $(g, J_+, J_-)$  as follows:

- $\mathbb{J}_A$  is  $J_+$  on  $C_+$ ,  $J_-$  on  $C_-$
- $\mathbb{J}_B$  is  $J_-$  on  $C_+$ ,  $J_+$  on  $C_-$

That is,

$$\mathbb{J}_{A/B} = \pi|_{C_{+}}^{-1} J_{+} \pi P_{+} \pm \pi|_{C_{-}}^{-1} J_{-} \pi P_{-} 
= \frac{1}{2} \begin{pmatrix} 1 \\ g \end{pmatrix} J_{+} \begin{pmatrix} 1 & 0 \end{pmatrix} \begin{pmatrix} 1 & g^{-1} \\ g & 1 \end{pmatrix} \pm \frac{1}{2} \begin{pmatrix} 1 \\ -g \end{pmatrix} J_{-} \begin{pmatrix} 1 & 0 \end{pmatrix} \begin{pmatrix} 1 & -g^{-1} \\ -g & 1 \end{pmatrix} 
= \frac{1}{2} \begin{pmatrix} 1 \\ g \end{pmatrix} \begin{pmatrix} J_{+} & J_{+} g^{-1} \end{pmatrix} \pm \begin{pmatrix} 1 \\ -g \end{pmatrix} \begin{pmatrix} J_{-} & -J_{-} g^{-1} \end{pmatrix} \right)$$
(86)

Setting  $\omega_{\pm} = gJ_{\pm}, w_{+}^{-1} = -J_{\pm}g^{-1}$ , one obtains

$$\mathbb{J}_{A/B} = \frac{1}{2} \begin{pmatrix} J_{+} & -\omega_{+}^{-1} \\ \omega_{+} & -J_{+}^{*} \end{pmatrix} \pm \begin{pmatrix} J_{-} & \omega_{-}^{-1} \\ -\omega_{-} & -J_{-}^{*} \end{pmatrix} \\
= \frac{1}{2} \begin{pmatrix} J_{+} \pm J_{-} & -\omega_{+}^{-1} \pm \omega_{-}^{-1} \\ \omega_{+} \mp \omega_{-} & -J_{+}^{*} \mp J_{-}^{*} \end{pmatrix}$$
(87)

#### 12.4.1 Condition on Types

The above expression implies that  $\pi_{A/B} = \omega_+^{-1} \mp \omega_-^{-1}$  are real Poisson structures and  $\omega_+^{-1} = -J_+g^{-1}$ , with types

$$\operatorname{type}(\mathbb{J}_{A}) = \frac{1}{2} \dim_{\mathbb{R}}(\operatorname{Ker} \pi_{A} = \operatorname{Ker} (J_{+} - J_{-}))$$

$$\operatorname{type}(\mathbb{J}_{B}) = \frac{1}{2} \dim_{\mathbb{R}}(\operatorname{Ker} \pi_{B} = \operatorname{Ker} (J_{+} + J_{-}))$$
(88)

Note that

$$(\star)[J_+, J_-] = (J_+ + J_-)(J_+ - J_-) \tag{89}$$

Thus,

1.  $(J_+ - J_-), (J_+ + J_-)$  have linearly independent kernels.

2.  $\star \implies \operatorname{Ker} (J_{+} - J_{-}) \oplus \operatorname{Ker} (J_{+} + J_{-}) \subset \operatorname{Ker} [J_{+}, J_{-}]$ 

3. If  $[J_+, J_-]x = 0$ , then

$$x = \frac{x + J_{+}J_{-}x}{2} + \frac{x - J_{+}J_{-}x}{2} \tag{90}$$

and  $(J_+ + J_-)(x + J_+ J_- x) = 0$ . Thus, Ker  $(J_+ + J_-) \oplus \text{Ker } (J_+ - J_-) = \text{Ker } [J_+, J_-]$ , and  $\text{type}(\mathbb{J}_A) + \text{type}(\mathbb{J}_B) = \frac{1}{2} \dim_{\mathbb{R}} \text{Ker } [J_+, J_-]$ .

Corollary 7.  $type(A) + type(B) \le n \text{ on } M^{2n}$ .

It immediatly follows from this that, since type(A) + type(B) = n everywhere  $\Leftrightarrow [J_+, J_-] = 0$ , then the pair (type(A), type(B)) is constant on a connected manifold.

#### 12.4.2 Integrability

As above, we have a map with structure actions  $\mathbb{J}_A \circlearrowleft C_{\pm} \to T \circlearrowleft J_{\pm}$  from our decomposed bundle to T. Note that the complexifications of these bundles are given by

$$C_{+} \otimes \mathbb{C} = L_{+} \oplus \overline{L}_{+}, C_{-} \otimes \mathbb{C} = L_{-} \oplus \overline{L}_{-}$$

$$\tag{91}$$

, where  $L_{+} = L_{A} \cap L_{B}, L_{-} = L_{A} \cap \overline{L}_{B}$ . Now,  $L_{A}, L_{B}$  are integrable  $\Longrightarrow L_{\pm}$  are Courant integrable  $\Longrightarrow \pi(L_{\pm}) = T_{\pm}^{1,0}$  are Lie integrable  $\Longrightarrow J_{\pm}$  are integrable  $\Longrightarrow (J_{\pm},g)$  are both Hermitian. With the chosen splitting, we have

$$L_{+} = \{X + gX : X \in T_{+}^{1,0}\} = \{X - i\omega_{+}X : X \in T_{+}^{1,0}\}$$
(92)

 $L_{+}$  is closed under H-Courant  $\Leftrightarrow$ 

$$\forall X, Y \in T_{+}^{1,0}, i_X i_Y (H - id\omega_{+}) = 0 \tag{93}$$

Similarly,

$$L_{-} = \{X - gX : X \in T_{-}^{1,0}\} = \{X + i\omega_{-}X : X \in T_{-}^{1,0}\}$$
(94)

and  $L_{-}$  is closed under H-Courant  $\Leftrightarrow$ 

$$\forall X, Y \in T_{-}^{1,0}, i_X i_Y (H + id\omega_{-}) = 0 \tag{95}$$

We can rewrite this as

$$i_X i_Y (H \mp i d\omega_{\pm}) = 0$$

$$i_X i_Y (H \mp i (\partial \overline{\partial}) \omega_{\pm}) = 0 \text{(since } i_X i_Y \overline{\partial} \omega_{\pm} = 0)$$

$$i_X i_Y (H \pm d_{\pm}^c \omega_{\pm}) = 0$$

$$H \pm d_{\pm}^c \omega_{\pm} = 0$$
(96)

That is, for a generalized K ahler manifold, we must have  $H = d_+^c \omega_+ = -d_-^c \omega_-$  in order that  $J_{\pm}$  is integrable.

**Theorem 11.** An abstracted defined  $\mathbb{J}_{A/B}$  on  $T \oplus T^*$ , H defines a generalized K aher structure  $\Leftrightarrow H = d_+^c \omega_+ = -d_-^c \omega_-$ . That is, a generalized K ahler structure over a b-field is a triple  $(g, J_+, J_-)$  s.t.  $d_+^c \omega_+ = -d_-^c \omega_-$ .

## 13 Lecture 18 (Notes: K. Venkatram)

## 13.1 Generalized K ahler Geometry

Let  $(\mathbb{J}_A, \mathbb{J}_B)$  be a generalized K ahler structure: then  $G = -\mathbb{J}_A\mathbb{J}_B$  is a generalized metric, and taking the decomposition  $T \oplus T^* = C_+ \oplus C_-$ ,  $C_{\pm} = \Gamma_{\pm g}$  gives  $\mathbb{J}_A|_{C_+} = \mathbb{J}_B|_{C_+}$ ,  $\mathbb{J}_A|_{C_-} = -\mathbb{J}_B|_{C_-}$ . Thus, we obtain two complex structures  $J_+, J_-$  on T by transport, i.e.  $J_+X = \pi \mathbb{J}_AX^+$  and  $J_-X = \pi \mathbb{J}_AX^-$ . Since  $\mathbb{J}_A$  is compatible with G, this implies that  $(J_+, g), (J_-, g)$  are almost Hermitian. Further, given the splitting of the Courant algebroid,  $\mathbb{J}_A, \mathbb{J}_B$  can be reconstructed from  $(g, J_+, J_-)$  by

$$\mathbb{J}_A = J_+|_{C_+} + J_-|_{C_-} 
\mathbb{J}_B = J_+|_{C_+} - J_-|_{C_-}$$
(97)

thus giving the formula

$$\mathbb{J}_{A/B} = \frac{1}{2} \begin{pmatrix} J_{+} \pm J_{-} & -(\omega_{+}^{-1} \mp \omega_{-}^{-1}) \\ \omega_{+} \mp \omega_{-} & -(J_{+}^{*} \pm J_{-}^{*}) \end{pmatrix}$$
(98)

#### 13.1.1 Integrability

As shown earlier, the integrability of  $(\mathbb{J}_A, \mathbb{J}_B)$  is equivalent to the Courant involutivity of  $L_A, L_B$ . Specifically, note that

$$(T \oplus T^*) \otimes \mathbb{C} = L_A \oplus \overline{L}_A = L_B \oplus \overline{L}_B = (L_A \cap L_B) \oplus (L_A \cap \overline{L}_B) \oplus (\overline{L}_A \cap L_B) \oplus (\overline{L}_A \cap \overline{L}_B)$$

$$= L_+ \oplus L_- \oplus \overline{L}_- \oplus \overline{L}_+$$

$$(99)$$

Thus, the complex structures on  $C_{\pm}$ , and thus on T, are described by the decompositions  $C_{+} \otimes \mathbb{C} = L_{+} \oplus \overline{L}_{+}, C_{-} \otimes \mathbb{C} = L_{-} \oplus \overline{L}_{-}$ , and the dimensions of the four spaces on the rhs are the same. Finally, since  $T_{1,0}^{+} = +i$  for  $J_{+} = L_{+}$  (and similarly,  $T_{1,0}^{-} = L_{-}$ ), we have integrability  $\Leftrightarrow L_{A}, L_{B}$  are involutive  $\implies L_{\pm}$  is involutive. The latter impliciation is in fact an iff:

**Proposition 8.**  $L_{\pm}$  involutive  $\implies L_{+} \oplus L_{-}, L_{+} \oplus \overline{L_{-}}$  involutive.

*Proof.* Using the fact that

$$\langle [a,b],c\rangle \cdot \phi = [[[d_H,a],b],c] \cdot \phi = a \cdot b \cdot c \cdot d_H \phi \tag{100}$$

for any  $\phi$  pure,  $a, b, c \in L_{\phi}$ , we find that  $\langle [a, b], c \rangle$  defined a tensor in  $\bigwedge L_{\phi}^*$ . Let  $a \in L_+, b \in L_-$  be elements. Then, for any  $x \in L_+$ ,  $\langle [a, b], x \rangle = \langle [x, a], b \rangle = 0$ . Similarly, for any  $x \in L_-$ ,  $\langle [a, b], x \rangle = \langle [b, x], a \rangle = 0$ . Thus,  $[a, b] \in L_+ \oplus L_-$ .

However, as we saw last time,

$$L_{\pm} = \{ X \pm gX | X \in T_{\pm}^{1,0} \} = \{ X \mp i\omega_{\pm} X | X \in T_{\pm}^{1,0} \}$$
 (101)

and so  $L_{\pm}$  are integrable  $\Leftrightarrow T_{\pm}^{1,0}$  are integrable and  $i_X i_Y (H \mp i d\omega_{\pm}) = 0 \forall X, Y \in T_{\pm}^{1,0}$ . Using the integrability of  $J_{\pm}$ , we can write the latter expression as  $i_X i_Y (H \mp i (\partial_{\pm} + \overline{\partial}_{\pm}) \omega_{\pm}) = 0 \forall X, Y \in T_{\pm}^{1,0}$ . Since  $\overline{\partial}_{\pm} \omega_{\pm}$  is of type 1, 2, it is killed, and

$$i_X I_Y (H \pm d_{\pm}^c \omega_{\pm}) = 0 \Leftrightarrow H \pm d_{\pm}^c \omega_{\pm} = 0 \Leftrightarrow \begin{cases} d_+^c \omega_+ + d_-^c \omega_- = 0 \\ d_+^c \omega_+ = -H \end{cases}$$
 (102)

Finally, we obtain the following result.

**Theorem 12.** Generalized K ahler structures on the exact Courant algebroid  $E \to M$ , modulo non-closed B-field transforms (choice of splitting) are equivalent to bi-Hermitian structures  $(g, J_+, J_-)$  s.t.  $d_+^c \omega_+ + d_-^c \omega_- = 0$ ,  $dd_+^c \omega_+ = 0$ , and  $[d_+^c \omega_+] = [E] \in H^3(M, \mathbb{R})$ .

**Remark.** This geometry was first described by Gates, Hull, Roček as the most general geomtry on the target of a 2-dimensional sigma model constrained to have N=(2,2) supersymmetry. Note that the special identities giving a (p,q) decomposition of  $H_H^*(M,\mathbb{C})$  are a consequence of the special identities required by SUSY. However, they are only clear when viewed in terms of  $(\mathbb{J}_A,\mathbb{J}_B)$  rather than  $J_{\pm}$ .

We can use this theorem to construct several new examples of generalized K ahler and generalized complex structures.

**Example.** Let G be an even-dimensional, compact, semisimple group, and choose an even-dimensional Cartan subalgebra  $\mathfrak{h} \subset \mathfrak{g} \otimes \mathbb{C}$ . The root system splits into  $\pm re$  roots, giving a decomposition  $\mathfrak{g} \otimes \mathbb{C} = \tau \oplus \overline{\tau}$  which is closed onder the Lie bracket. Thus, by left or right translating, we get an integrable complex structure on G, and since the root spaces are killing-orthogonal, we have a bi-Hermitian structure  $(g, J_L, J_R)$ , with g the killing form. Now, recall the Cartan 3-form H(X, Y, Z) = g([X, Y], Z) and notice that

$$A = d_L^c \omega_L(X, Y, Z) = d\omega_L(J_L X, J_L Y, J_L Z) = -\omega_L([J_L X, J_L Y], J_L Z) + \text{c.p.}$$

$$= -g(J_L[J_L X, Y] + J_L[X, J_L Y] + [X, Y], Z) + \text{c.p.}$$

$$= (2q([J_L X, J_L Y], Z) + \text{c.p.}) - 3H(X, Y, Z) = -2A - 3H$$
(103)

Thus,  $d_L^c \omega_L = -H$ ; since the right Lie algebra is anti-isomorphic to the left,  $d_R^c \omega_R = H$ , and  $(G, g, J_L, J_R)$  is a generalized K ahler structure unique w.r.t.  $H_{cartan}$ . Finally, we obtain the generalized complex structures

$$\mathbb{J}_{A/B} = \begin{pmatrix} J_L \pm J_R & -(\omega_L^{-1} \mp \omega_R^{-1}) \\ \omega_L \mp \omega_R & -(J_L^* \pm J_R^*) \end{pmatrix}$$
 (104)

on G.

What are their types? Since  $\omega_L = gJ_L, \omega_R = gJ_R$ ,

$$-(\omega_L^{-1} \mp \omega_R^{-1}) = (J_L \mp J_R)g^{-1}$$

$$J_L \pm J_R = R_{g*}(R_{q^{-1}*}L_{g*}J \pm JR_{q^{-1}*}L_{g*})L_{q^{-1}*}$$
(105)

Thus, the rank of  $(\mathbb{J}_A, \mathbb{J}_B)$  at g is simply  $(\operatorname{rk}[J, \operatorname{Ad}_a], \operatorname{rk}\{J, \operatorname{Ad}_a\})$ .

**Problem.** Describe the symplectic leaves of  $(\mathbb{J}_A, \mathbb{J}_B)$  for G = SU(3).

In the simplest case,  $Q = [J_+, J_-]g^{-1} = 0$ , so that type  $A + \text{type } B = n \implies \text{constant types.}$  As earlier, since  $[J_+, J_-] = 0$ , we have a decomposition  $T \otimes \mathbb{C} = A \oplus B \oplus \overline{A} \oplus \overline{B}$ , with  $A = T_{1,0}^+ \cap T_{1,0}^-$ ,  $B = T_{1,0}^+ \cap T_{0,1}^-$ . Note that A, B are integrable since  $T_{1,0}^+, T_{1,0}^-$  are. Also, note that  $A \oplus \overline{A} = \text{Ker } (J_+ - J_-) = \text{Im } (J_+ + J_-) = \text{Im } \pi_A$  is integrable, as is  $B \oplus \overline{B}$ .

**Proposition 9.** A, B are holomorphic subbundles of  $T_{1.0}^+$ .

*Proof.* Define  $\overline{\partial}_{X^{0,1}}Z^{1,0} = [X,Z]^{1,0}$ . For  $Z \in C^{\infty}(A)$ ,  $X = X_{\overline{A}} + X_{\overline{B}}$ ,  $[X,Z]^{1,0} = [X,Z]^A + [X,Z]^B$ , with the latter term being zero since  $[X_{\overline{A}},Z]$  is still in  $A \oplus \overline{A}$  and  $[X_{\overline{B}},Z]$  is in the integrable space  $A \oplus \overline{B}$ . Thus, A (and similarly B) give  $J_{\pm}$  holomorphic splittings of TM.

## 14 Lecture 19 (Notes: K. Venkatram)

## 14.1 Generalized K ahler Geometry

Recall from earlier that a K ahler structure is a pair  $\mathbb{J}_J = \begin{pmatrix} J & \\ & -J^* \end{pmatrix}$ ,  $\mathbb{J}_\omega = \begin{pmatrix} & -\omega^{-1} \\ \omega & \end{pmatrix}$  s.t.  $\mathbb{J}_J \mathbb{J}_\omega = \mathbb{J}_\omega \mathbb{J}_J = -\begin{pmatrix} & g^{-1} \\ g & \end{pmatrix} = -G$ .

**Definition 22.** A generalized K ahler structure is a pair  $(\mathbb{J}_A, \mathbb{J}_B)$  of generalized complex structures s.t.  $-\mathbb{J}_A\mathbb{J}_B = G$  is a generalized Riemannian metric.

The usual example has type (0, n) for  $\mathbb{J}_A, \mathbb{J}_B$ . In fact, as we will show later type  $\mathbb{J}_A$  + type  $\mathbb{J}_B \leq n$  and  $\equiv n \mod 2$ .

**Example.** 1. Can certainly apply *B*-field  $(e^B \mathbb{J}_A e^{-B}, e^B \mathbb{J}_B e^{-B})$  and obtain the generalized metric  $e^B G e^{-B}$ .

2. Going back to hyperk ahler structures, recall that

$$(\omega_J + i\omega_K)I = g(J + iK)I = -gI(J + iK) = I^*(\omega_J + i\omega_K)$$
(106)

so  $\frac{1}{2}(\omega_J + i\omega_k) = \sigma$  is a holomorphic (2,0)-form with  $\sigma^n \neq 0$ . Note that  $\beta = \frac{1}{2}(\omega_J^{-1} - i\omega_k^{-1})$  satisfies  $\beta\sigma = \frac{1}{2}(1 - iI) = P_{1,0}$ , i.e. it is the projection to the (1,0)-form  $\beta|_{T_{1,0}^*} = \sigma^{-1}|_{T^{1,0}}$ .

Recall that, for  $\beta$  a holomorphic (2,0)-bivector field s.t.  $[\beta,\beta] = 0$ ,  $e^{\beta+\overline{\beta}}\mathbb{J}_I e^{-\beta-\overline{\beta}}$  is a generalized complex structure. Thus, we have

$$\begin{pmatrix} 1 & t\omega_{J}^{-1} \\ 1 & 1 \end{pmatrix} \begin{pmatrix} I \\ -I^{*} \end{pmatrix} \begin{pmatrix} 1 & -t\omega_{J}^{-1} \\ 1 & 1 \end{pmatrix} = \begin{pmatrix} I & -t\omega_{J}^{-1}I^{*} \\ -I^{*} \end{pmatrix} \begin{pmatrix} 1 & -t\omega_{J}^{-1}I^{*} \\ 1 & 1 \end{pmatrix} = \begin{pmatrix} I & -tI\omega_{J}^{-1} - t\omega_{J}^{-1}I^{*} \\ 0 & -I^{*} \end{pmatrix}$$

$$= \begin{pmatrix} I & 2tKg^{-1} \\ -I^{*} \end{pmatrix} = \begin{pmatrix} I & -2t\omega_{K}^{-1} \\ -I^{*} \end{pmatrix}$$

$$(107)$$

Now, note that

$$\begin{pmatrix} 1 & t\omega_{J}^{-1} \\ 1 & 1 \end{pmatrix} \begin{pmatrix} & -\omega_{I}^{-1} \\ \omega_{I} & & 1 \end{pmatrix} = \begin{pmatrix} t\omega_{J}^{-1}\omega_{I} & -\omega_{I}^{-1} \\ \omega_{I} & & \end{pmatrix} \begin{pmatrix} 1 & -t\omega_{J}^{-1} \\ 1 & & 1 \end{pmatrix}$$

$$= \begin{pmatrix} t\omega_{J}^{-1}\omega_{I} & -\omega_{I}^{-1} - t^{2}\omega_{J}^{-1}\omega_{I}\omega_{J}^{-1} \\ \omega_{I} & & -t\omega_{I}\omega_{J}^{-1} \end{pmatrix}$$

$$= \begin{pmatrix} tK & (-1+t^{2})\omega_{I}^{-1} \\ \omega_{I} & & -tK^{*} \end{pmatrix}$$

$$= \sqrt{1-t^{2}}\mathbb{J}_{\frac{1}{\sqrt{1-t^{2}}}\omega_{I}} + t\mathbb{J}_{K}$$

$$(108)$$

By a previous calculation, this is integrable, and  $\mathbb{J}_A = \begin{pmatrix} I & -2t\omega_K^{-1} \\ -I^* \end{pmatrix}$ ,  $\mathbb{J}_B = \begin{pmatrix} tK & (-1+t^2)\omega_I^{-1} \\ \omega_I & -tK^* \end{pmatrix}$  is a generalized K ahler structure of type (0,0).

**Problem.** Let  $(J, \omega)$  be a K ahler structure,  $\beta$  a holomorphic Poisson structure. For  $Q = \beta + \overline{\beta}$ , when is  $e^{tQ} \mathbb{J}_{\omega} e^{-tQ}$  integrable for small t?

What is the analog of the Hodge decomposition  $H^k(M,\mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}(M)$  for generalized K ahler manifolds. The key element of this decomposition in the case of ordinary K ahler structures is to show that  $\Delta_d = \partial \Delta_{\partial} = \partial \Delta_{\overline{\partial}}$ , where  $\Delta_d = dd^* + d^*d = (d+d^*)^2$ , and  $d^*$  is the adjoint of d in an appropriate metric define on forms. The equality of the above decomposition then follows from Hodge theory (that every cohomology class has a unique harmonic representative).

### 14.2 Hodge Theory on Generalized K ahler Manifolds

Recall the Born-Infeld volume: letting  $(a_i)$  be an orthonormal basis for  $C_+$  in  $Pin(T \oplus T^*)$ , we have an associated element  $-G \in O(n,n)$ ; letting  $\star \psi = \alpha(\alpha(*)\psi)$  denote the generalized Hodge star and  $(*\phi, \psi) \in \det T^*$  the symmetric volume form, the Born-Infeld inner product on  $S \otimes \mathbb{C} = \Omega^*(M, \mathbb{C})$  is

$$(\phi, \psi) = \int_{M} \langle *\phi, \overline{\psi} \rangle \tag{109}$$

This is a Hermitian inner product. Recall also that, if we split  $T \oplus T^*$  and  $G = \begin{pmatrix} g^{-1} \\ g \end{pmatrix}$ , then  $\langle *\phi, \psi \rangle = \phi \wedge \star \psi = (\phi, \psi) \text{vol}_q$  via the usual Hodge inner product. What is the adjoint of  $d_H$ ?

**Lemma 7.**  $\langle d\phi, \psi \rangle = (-1)^{\dim M} \langle \phi, \partial \psi \rangle$ .

*Proof.* First, note that  $\alpha(\phi^{(k)}) = (-1)^{\frac{1}{2}k(k-1)}\phi^{(k)}$ . then

$$d(\phi \wedge \alpha(\psi)) = d\phi \wedge \alpha(\psi) + (-1)^k \phi \wedge d\alpha(\psi) d(\alpha(\psi^p)) = (-1)^{\frac{1}{2}p(p-1)} d\psi^p = (-1)^{\frac{1}{2}p(p-1) + \frac{1}{2}p(p+1)} \alpha(d\psi^p) = -\alpha(d\psi^p)$$
(110)

Thus,  $d(\phi \wedge \alpha(\psi)) = \langle d\phi, \psi \rangle + (-1)^n \langle \phi, d\psi \rangle.$ 

**Lemma 8.** We have the same for  $H \wedge \cdot$ .

Corollary 8. On an even-dimensional manifold,  $\int_M \langle d_H \phi, \psi \rangle = \int_M \langle \phi, d_H \psi \rangle$ .

Now

$$h(d_H\phi,\psi) = \int \langle *d_H\phi,\psi\rangle = \int \langle d_H\phi,\sigma(ast)\psi\rangle = \int \langle \phi,d_H\sigma(*)\psi\rangle = \int \langle *\phi,*d_H\sigma(*)\psi\rangle$$
(111)

so  $d_H^* = *d_H *^{-1}$ . As in the classical case,  $d_H + d_H^*$  is elliptic, as is  $D^2 = \Delta_{d_H}$ . By Hodge theory, every twisted deRham cohomology class has a unique harmonic representative.

To perform Hodge decomposition on generalized K ahler manifolds, note that we have two commuting actions on spinors. For  $\mathbb{J}_A$ , we have the maps  $\partial_A:\mathcal{U}_k\to\mathcal{U}_{k+1}$  and  $\overline{\partial}_A:\mathcal{U}_k\to\mathcal{U}_{k-1}$ , with the associated differential  $d_H=\partial_A+\overline{\partial}_A$ . Each  $\mathcal{U}_k$  must decompose as eigenspaces for  $\mathbb{J}_B$ , i.e. we can obtain a set of spaces  $\mathcal{U}_{r,s}$  which has the pair of eigenvalues (ir,is) for  $(\mathbb{J}_A,\mathbb{J}_B)$ . Between these spaces, we have horizontal maps given by  $L_A,\overline{L_A}$  and vertical maps given by  $L_B,\overline{L_B}$ , with the associated decompositions

$$(T \oplus T^*) \otimes \mathbb{C} = L_A \cap L_B \oplus L_A \cap \overline{L_B} \oplus \cap L_A \cap L_B \oplus \overline{L_A} \cap \overline{L_B}$$
$$d_H = \delta_+ + \delta_- + \overline{\delta_+} + \overline{\delta_-}$$
(112)

**Proposition 10.**  $\delta_+^* = -\overline{\delta}_+$  and  $\delta_-^* = \overline{\delta}_-$ .

*Proof.* The identity  $\mathbb{J}_A \mathbb{J}_B = -G$  corresponds to the spin decomposition  $e^{\frac{\pi}{2}\mathbb{J}_A} \times e^{\frac{\pi}{2}\mathbb{J}_B} = *$ . Thus, for  $\phi \in \mathcal{U}^{p,q}$ ,  $*\phi = e^{\frac{\pi}{2}\mathbb{J}_A} \times e^{\frac{\pi}{2}\mathbb{J}_B} \phi = i^{p+q}\phi$  and

$$\delta_{\perp}^{*} = (*d_{H} *^{-1} \phi) = (i^{p+q-2} \overline{\delta}_{+} i^{-p-q} \phi) = -\overline{\delta}_{+}$$
(113)

The other identity follows similarly.

Corollary 9. If  $\phi \in \mathcal{U}^{p,q}$  is closed (i.e.  $d_H \phi = 0$ ) then it is  $\Delta$  closed as well.

By our above decomposition of  $d_H$  and the implied decomposition of  $d_H^*$ , we find that  $\frac{1}{2}(d_H + d_H^*) = \delta_- + \delta_-^*$  and  $\frac{1}{2}(d_H - d_H^*) = \delta_+ + \delta_+^*$ , so that  $\frac{1}{4}\Delta_{d_H} = \Delta_{\delta_-} = \Delta_{\delta_+}$ . This finally gives us our desired decomposition

$$H_H^*(M, \mathbb{C}) = \bigoplus_{|p+q| \le n, p+q \equiv n \mod 2} \mathcal{H}_{\Delta_{d_H}}^{p,q} \tag{114}$$

## 15 Lecture 20 (Notes: K. Venkatram)

## 15.1 Generalized Complex Branes (of rank 1)

In complex geometry, we have special submanifolds, i.e. complex submanifolds  $\phi: S \to M$  s.t.  $J(TS) \subset TS$ , i.e.  $TS \subset TM$  is a complex subspace (for examplex, points in a manifold, or algebraic subvarieties). In symplectic geometry, there are several kinds of special submanifolds: isotropic  $(TS \subset TS^{\omega})$ , coisotropic  $(TS^{\omega} \subset TS)$ , and Lagrangian  $(TS = TS^{\omega} \Leftrightarrow \phi^* \omega = 0)$ .

**Example.** 1. If  $f:(M,\omega)\to (M,\omega)$  is a diffeomorphism with  $f^*\omega=\omega$  (i.e. a symplectomorphism), then  $\phi:\Gamma_f\to M\times \overline{M}$  satisfies  $\phi^*(\pi_1^*\omega-\pi_2^*\omega)=0$ , i.e.  $\Gamma_f$  is Lagrangian.

2. For any manfold M,  $T^*M$  is symplectic, with  $\omega = \sum dp_i \wedge dx_i$ , for  $\{x_i\}$  a coordinate chart on M and  $\{p_i\}$  coordinates for the 1-form. Then the fibers  $(x_i = 0)$  are Lagrangian, as are the zero sections  $(p_i = 0)$ . Aimilarly, the graph of any 1-form  $\alpha = \sum \alpha_i dx^i \in \Omega^1(M)$  is Lagrangian  $\Leftrightarrow f^*\omega = \sum d\alpha_i \wedge dx^i = 0 \Leftrightarrow d\alpha = 0$ .

Lagrangians and complex submanifolds are important in physics since they are the D-branes in A- and B-models. However, for a generalized complex manifold, we don't yet have such a good notion of subobject. Now, associated to any submanifold  $S \to M$ , we can form

$$0 \to TS \to TM \to NS \to 0 \tag{115}$$

and hence

$$0 \to N^*S \to T^*M \to T^*S \to 0 \tag{116}$$

where  $N^*S = \{\xi \in T^*M | \xi(TS) = 0\}$  is the conormal bundle. Therefore, we have a natural maximal isotropic subbundle  $TS \oplus N^*S \subset TM \oplus T^*M$ . If there is ambient flux, i.e. (M, H), then as we defined before,  $(f: S \to M, F \in \Omega^2(S))$  gives us a topological brane when  $f^*H = dF$ . In this case, we similarly have  $\tau_{S,F} = f_*\Gamma_F \subset TM \oplus T^*M$  s.t.

$$f_*\Omega_F = \{ f_*v + \xi \in TS \oplus T^*M | v + f^*\xi \in \Gamma_F \}$$

$$\tag{117}$$

This gives us an exact sequence

$$0 \to N^*S \to \tau_{S,F} \to TS \to 0 \tag{118}$$

, and we call it a generalized complex brane when  $\mathbb{J}\tau_{S,F}\subset\tau_{S,F}$ .

#### 15.1.1 General Properties of Generalized Complex Branes

•  $(f: S \to (M, H), F \in \Omega^2(S))$  has generalized pullback map  $e^F f^* : \Omega^*(M) \ni \rho \mapsto e^F f^* \rho \in \Omega^*(S)$  s.t.

$$de^F f^* \rho = dF \wedge e^F f^* \rho + e^F f^* d\rho = e^F f^* (d\rho + H \wedge \rho) = e^F f^* d_H \rho \tag{119}$$

Thus, we obtain a map on cohomology  $H_H^*(M,\mathbb{R}) \to H_H^*(S,\mathbb{R})$ .

• Let  $\psi$  be the pure spinor line in  $\bigwedge^* T^*M|_S$  defining  $\tau_{M,S}$ . Then  $\psi = \langle e^{-F} \det(N^*) \rangle$  and  $\mathbb{J}\tau \subset \tau$  implies that

$$0 = (\mathbb{J}x)\psi = [\mathbb{J}, x] \cdot \psi = \mathbb{J}(x \cdot \psi) + x \cdot \mathbb{J} \cdot \psi \forall x \in \tau$$
(120)

Thus,  $\mathbb{J}\psi = (ik)\psi$ : since  $\psi$  is real, k = 0, and  $\psi \in \mathcal{U}^0$ .

- Gerbe interpretation: for  $G = (L_{ij}, m_{ij}, \theta_{ijk})$  a gerbe,  $(\nabla_{ij}, B_i)$  a connection, if we can find  $(L_i, \nabla_i)$  on S s.t.  $F(\nabla_i) F(\nabla_i) = F(\nabla_{ij})$ , then  $F(\nabla_i) B_i = F$  is the gloabl 2-form on S we described.
- Action by B-fields:  $e^B \circlearrowright T \oplus T^*, (S, F + B)$ .

#### Example. Examples of generalized complex branes:

1. Complex Case:  $f:(S,F)\to (M,J)(H=0)$ . Then

$$\tau_{S,F} = \{v + \xi \in TS \oplus T^*M | i_V F = f^* \xi\}$$

$$\mathbb{J}\tau_{S,F} = \tau_{S,F} \Leftrightarrow J(TS) \subset TS \text{ and } -J^*Fv = FJv \Leftrightarrow S \text{ is a complex submanifold and } F \text{ has type } (1,1)$$
(121)

Thus, we interpret  $F = F(\nabla)$  as the curvature of a unitary connection on a holomorphic line bundle  $\mathcal{L}$ , giving us the complex brane  $(S, \mathcal{L}, \nabla)$ .

2. Symplectic Case: For H = 0, F = 0, we have

$$\mathbb{J}' = \begin{pmatrix} & -\omega^{-1} \\ \omega & \end{pmatrix} \begin{pmatrix} TS \\ N^*S \end{pmatrix} = \begin{pmatrix} TS \\ N^*S \end{pmatrix} \Leftrightarrow \omega(TS) = N^*S \text{ and } \omega^{-1}(N^*S) = TS \Leftrightarrow TS \subset TS^{\omega} \text{ and } TS^{\omega} \subset TS$$
(122)

i.e. iff S is Lagrangian. For  $F \neq 0$ , things are more interesting. Choose locally an extension of F to  $\Omega^2(M)$ . Then  $\mathbb{J}_{\omega}$  fixes  $\tau_{S,F} \Leftrightarrow e^F \mathbb{J}_{\omega} e^{-F}$  fixed  $\tau_{S,0} \Leftrightarrow$ 

$$\begin{pmatrix} -\omega^{-1}F & -\omega^{-1} \\ \omega + F\omega^{-1}F & F\omega^{-1} \end{pmatrix} \begin{pmatrix} TS \\ N^*S \end{pmatrix} = \begin{pmatrix} TS \\ N^*S \end{pmatrix}$$
 (123)

That is, we must have

- $\omega^{-1}N^*S \subset TS$ , i.e. S is coisotropic
- $F(TS^{\omega}) \subset N^*S$ , i.e. F vanishes on the characteristic foliation C, i.e. locally  $F = \pi^* \{ , \pi : S \to S/C .$
- $\omega^{-1}F \circlearrowleft TS$  s.t.  $(\omega + F\omega^{-1}F)TS \subset N^*S)$ , i.e. on  $TS/TS^{\omega}$ ,  $(1 + \omega^{-1}F\omega^{-1}F) = 0$ , i.e.  $(\omega^{-1}F)^2 = -1$ . Thus,  $TS/TS^{\omega}$  inherits a complex structure.

Note that  $F + i\omega$  defines a form of type (2,0) on  $TS/TS^{\omega}$  w.r.t.  $I = \omega^{-1}F$  since

$$I^*(F+i\omega) = F\omega^{-1}(F+i\omega) = -\omega + iF = i(F+i\omega) = (F+i\omega)I$$
(124)

and  $F + i\omega$  is closed. Thus,  $F + i\omega$  defines a holomorphic symplectic structure on SC, which therefore must be 4k-dimensional. This is precisely the geometry discovered by Kapustin and Orlov as the most general rank 1 A-brane in a symplectic manifold.

**Example.** Let (g, I, J) be a hyper-K ahler manifold, and consider the complex structure  $\omega_I$ .

**Example.** If S=M, then the conditions are  $(\omega^{-1}F)^2=-1$ , i.e.  $F+i\omega$  is a holomorphic symplectic structure. For example, (M,g,I,J) hyperk ahler with  $\omega=\omega_k, F=\omega_J, \omega^{-1}F=\omega_J^{-1}\omega_k=(gJ)^{-1}gk=-I$ . This is an example of a space-filling rank 1 A-brane used by Kapustin-Witten in their study of the geometric Langlands program.

#### 15.1.2 Branes for Other Generalized Complex Manifolds

Consider a complex structure I, deformed by a holomorphic bivector  $\beta$ :  $Q = \beta + \overline{\beta}$ ,  $\mathbb{J} = \begin{pmatrix} I & Q \\ & -I^* \end{pmatrix}$  is a generalized complex structure, e.g.  $\mathbb{C}P^2$ .

0-Branes: Before deformation, all the points were branes. Now, only the points on  $\beta = 0$  are.

2-Branes: Branes must be complex curves where  $\beta = 0$  or  $(\beta + i\omega)$ -Langrangian where  $\beta \neq 0$ . That is,  $\beta = 0$  is a brane, as is any curve on which  $\beta + i\omega = \beta^{-1}$  vanishes. In particular, any previous complex curve is still a brane

**Problem.** Are there 2-branes in  $\mathbb{C}P^2_{\beta}$  which are not complex curves in  $\mathbb{C}P^2$ ? What are the space-filling branes on  $\mathbb{C}P^2_{\beta}$ ?

## 16 Lecture 21-23 (Notes: K. Venkatram)

### 16.1 Linear Algebra

We define a category  $\mathcal{H}$  whose objects are pairs (E,g) (sometimes denoted E for brevity), where E is a finite dimensional vector space  $/\mathbb{R}$  and g is a nondegenerate symmetric bilinear form on E with signature 0, and whose morphisms are maximal isotropies  $L \subset \overline{E} \times F$ . Here,  $E \mapsto \overline{E} = (E, -g)$  is the natural involution, and  $E \times F = (E \times F, g_E + g_F)$  is the natural product structure. Composition is done by composition of relations, i.e.  $E \to^L F \to^M G, M \circ L = \{(e,g) \in E \times G | \exists f \in Fs.t.(e,f) \in L, (f,g) \in M\}$ .

**Proposition 11.**  $M \circ L$  is a morphism in  $\mathcal{H}$ .

*Proof.*  $\mathcal{L}: L \times M \subset \overline{E} \times F \times \overline{F} \times G = W$  is maximally isotropic.  $\mathcal{C} = E \times \Delta_F \times G$ , where  $\Delta_F = \{(f, f) | f \in F\}$ , is coisotropic, i.e.  $\mathcal{C}^{\perp} = \Delta_F \subset \mathcal{C}$ . Thus, we get an induced bilinear form on  $\mathcal{C}^{\perp}/\mathcal{C} = \overline{E} \times G$ .  $\mathcal{C} \cap \mathcal{L} + \mathcal{C}^{\perp}$  is maximaly isotropic in W, so

$$(\mathcal{C} \cap \mathcal{L} + \mathcal{C}^{\perp})^{\perp} = (\mathcal{C}^{\perp} + \mathcal{L}^{\perp}) \cap \mathcal{C} = \mathcal{C}^{\perp} + \mathcal{L} \cap \mathcal{C}$$
(125)

Thus,  $\mathcal{C} \cap \mathcal{L} + \mathcal{C}^{\perp}/\mathcal{C}^{\perp} = M \circ L \subset \mathcal{C}/\mathcal{C}^{\perp} = \overline{E} \times G$  is maximally isotropic.

**Remark.** This cateogory is the symmetric version of the Weinstein's symplectic category  $\zeta$  where  $\mathrm{Ob}(\zeta) = (E, \omega)$  and morphisms are given by Lagrangians. Thus, is the the "odd" version or parity reversal of  $\zeta$ .

A particular case of a morphism  $E \to F$  is the graph of an orthogonal morphism.

**Problem.** Show that  $L: E \to F$  is epi  $\Leftrightarrow \pi_F(L) = F$ , mono  $\Leftrightarrow \pi_E(L) = E$ , and iso  $\Leftrightarrow L$  is orthogonal iso  $E \to F$ .

So for dim E = 2n,  $O(n, n) \subset \text{Hom}(E, E)$  are isos. But  $\text{Hom}(E, E) \cong O(2n)$  as a space since we can choose a positive definite  $C_+$  and then any  $L \in O(2n)$ . This implies that Hom(E, E) is a monoid compactifying the group O(E).

#### 16.1.1 Doubling Functor

Now, there is a nature "Double" functor  $\mathcal{D}$ : Vect  $\to \mathcal{H}$  which maps  $V \mapsto V \oplus V^*$  and  $\{f: V \to M\} \mapsto \{\mathcal{D}f = \{(v + F^*\eta, f_*v + \eta) \in V \oplus V^* \times W \oplus W^* | v \in V, \eta \in W^*\}\}$ . Note that  $\mathcal{D}f \subset \overline{\mathcal{D}V} \times \mathcal{D}W$  and dim  $\mathcal{D}f = \dim V + \dim W$ .

$$\langle (v + f^* \eta, f_* v + \eta), (v + f^* \eta, f_* v + \eta) \rangle = -f^* \eta(v) + \eta(f_* v) = 0$$
(126)

**Problem.** Prove that  $\mathcal{D}$  is a functor, i.e.  $\mathcal{D}(f \circ g) = \mathcal{D}f \circ \mathcal{D}g$ .

Note that  $\mathcal{H}$  has a duality functor  $L \in \text{Hom}(E, F) \implies L^* \in \text{Hom}(F, E)$ , where  $L^* = \{(f, e) | (e, f) \in L\}$ .

**Problem.** Show that  $\mathcal{D}(f^*) = (\mathcal{D}f)^*$ .

**Problem.** Prove that  $\mathcal{D}$  preserves epis and monos.

#### 16.1.2 Maps Induced by Morphisms

A morphism  $L \in \operatorname{Hom}(E,F)$  induces maps  $L \circ - : \operatorname{Hom}(X,E) \rightleftarrows \operatorname{Hom}(X,F) : L^* \circ -$ . A special case is  $X = \{0\}$ , in which  $\operatorname{Hom}(0,E) = \operatorname{Dir}(E)$ , so  $L \in \operatorname{Hom}(E,F)$  induces maps  $L_* : \operatorname{Dir}(E) \rightleftarrows \operatorname{Dir}(F) : L^*$ . If L is mono or epi, so is  $L_*$ . This recovers the pushforward and pullback of Dirac structures: for  $f : V \to W$  a linear map,  $\mathcal{D}f : \mathcal{D}V \to \mathcal{D}W$  a morphism we obtain maps  $\mathcal{D}f_* : \operatorname{Dir}(V) \rightleftarrows \operatorname{Dir}(W) : \mathcal{D}f^*$ . As observed earlier, any Dirac  $L \subset V \oplus V^*$  with  $\pi_V(L) = M \subset V$  can be written as  $L(M,B), B \in \bigwedge^2 M^*$ , i.e.  $L = j_*\Gamma_B$  for  $j : M \hookrightarrow V$  the embedding and a unique B. That is,  $L = j_*e^BM$ .

**Example.** Given  $f: V \to W$  a linear map,  $\mathcal{D}f \subset \overline{\mathcal{D}V} \times \mathcal{D}W = \mathcal{D}(V \oplus W^*)$ . and  $\mathcal{D}f = ((v, f^*\eta), (f_*v, \eta) \cdots)$ , hence  $\pi_{V \oplus W^*} \mathcal{D}f = V \oplus W^*$  is onto. Therefore,  $\mathcal{D}f = e^B(V \oplus W^*)$ , and in fact  $B = f \in V^* \otimes W \subset \bigwedge^2 (V \oplus W^*)^*$ .

#### **16.1.3** Factorization of Morphisms $L: \mathcal{D}V \to \mathcal{D}(W)$

Let  $L \in \text{Hom}(\mathcal{D}V, \mathcal{D}W), L \subset \overline{\mathcal{D}V} \times \mathcal{D}W \cong \mathcal{D}(V \oplus W)$ . Then  $L = j_*e^FM$ , for  $M = \pi_{V \oplus W}L \subset V \oplus W$ . Let  $\phi : M \to V, \psi : M \to W$  be the natural projections.

Theorem 13.  $L = \mathcal{D}\psi_* \circ e^F \circ \mathcal{D}\phi^*$ .

$$Proof.$$
 (Exercise)

**Corollary 10.** L is an isomorphism  $\Leftrightarrow \phi, \psi$  are surjective and F determines a nondegenerate pairing Ker  $\phi \times \text{Ker } \psi \to \mathbb{R}$ .

Therefore, an orthogonal map  $V \oplus V^* \to W \oplus W^*$  can be viewed as a subspace  $M \subset V \times W, F \in \bigwedge^2 M^*$ .

#### **16.2** *T*-duality

The basic idea of T-duality is as follows: let  $S^1 \to P \to^{\pi} B$  be a principal  $S^1$  bundle, i.e. a spacetime with geometry, with an invariant 3-form flux  $H \in \Omega^3_{cl}(P)^{S^1}$  and an integral  $[H] \in H^3(P,\mathbb{Z})$ , i.e. coming from a gerbe with connection. Then we are going to produce a new "dual" spacetime with "isomorphic quantized field theory" (in this case, a sigma model). Specifically, let  $\tilde{P}$  be a new  $S^1$ -bundle over B so that  $c_1(\tilde{P}) = \pi_*(H) \in H^2(B,\mathbb{Z})$ , and choose  $\tilde{H} \in H^3(\tilde{P},Z)$  s.t.  $\tilde{\pi}_*\tilde{H} = c_1(P)$ . More specifically, choose a connection  $\theta \in \Omega^1(P)$  (i.e.  $L_{\partial_{\theta}}\theta = 0, i_{\partial_{\theta}} = 1/2\pi$ ) so  $d\theta = F \in \Omega^2(B)$  is integral and  $[F] = c_1(P)$ . Then  $H = \tilde{F} \wedge \theta + h$  for some  $\tilde{F} \in \Omega^2(B)$  integral and  $H \in \Omega^3(B)$ . Now,  $[\tilde{F}] \in H^2(B,\mathbb{Z})$  defines a new principal  $S^1$ -bundle  $\tilde{P}$ . Choose a connection  $\tilde{\theta}$  on  $\tilde{P}$  so that  $d\tilde{\theta} = \tilde{F}$ . Then define  $\tilde{H} = F \wedge \tilde{\theta} + h$ , so tat  $\int \tilde{H} = F$  and  $\int H = \tilde{F}$ .

**Example.** Let  $S^1 \times S^2 \to S^2$  be the trivial  $S^1$ -bundle, with  $H = v_1 \wedge v_2$ . Then  $v_2 = \int_{S^1} H = c_1(S^3 \to S^2)$ , so the T-dual is the pair  $S^3$ , 0. Our original space has trivial topology and nontrivial flux, while the new space has nontrivial topology and trivial flux.

**Remark.** In physics, T-dual spaces have the same quantum physics, hence the same D-branes and twisted K-theory.

**Theorem 14** (BHM). We have an isomorphism  $K_H^*(P) \cong K_{\tilde{\mu}}^{*+1}(\tilde{P})$ .

Next, let  $P \times_B \tilde{P} = \{(p, \tilde{p}) | \pi(p) = \tilde{\pi}(\tilde{p})\} \subset P \times \tilde{P}$  be the correspondence space,  $\phi, \psi$  the two projections. Then  $\phi^* H - \psi^* \tilde{H} = \tilde{F} \wedge \theta - F \wedge \tilde{\theta} = -d(\phi^* \theta \wedge \psi^* \tilde{\theta})$ .

**Definition 23.** A T-duality between  $S^1$ -bundles (P, H) and  $(\tilde{P}, \tilde{H})$  over B is a 2-form  $F \in \Omega^2(P \times_B \tilde{P})^{S^1 \times S^1}$  s.t.  $\phi^*H - \psi^*\tilde{H} = dF$  and F deterines a nondegenerate pairing Ker  $\phi_* \times \text{Ker } \psi_* \to \mathbb{R}$ .

In fact, T-duality can be expressed, therefore, as an orthogonal isomorphism

$$(T_p \oplus T_p^*, H)/S^1 \to^{L(P \times_B \tilde{P}, F)} (T_{\tilde{P}} \oplus T_{\tilde{P}}^*, \tilde{H})/S^1$$

$$(127)$$

though of as bundles over B (or just  $S^1$ -invariant sections on  $P, \tilde{P}$ ). This map sends H-twisted bracket to  $\tilde{H}$ -twisted bracket, via

$$\Omega^*(P)^{S^1} \ni \rho \mapsto \tau(\rho) = \psi_* e^F \wedge \phi^* \rho = \int_{\tilde{S}^1} e^F \wedge \phi^* \rho \in \Omega^*(\tilde{P})^{S^1}$$
(128)

Since  $d(e^F\rho)=e^F(d\rho+(H-\tilde{H})\rho)$ , we find that  $d_{\tilde{H}}(e^F\rho)=e^Fd_H\rho$  and  $\tau(d_H\rho)=d_{\tilde{H}}\tau(\rho)$  as desired. Overall, a T-duality  $F:(P,H)\to (\tilde{P},\tilde{H})$  implies an isomorphism  $(T_p\oplus T_p^*,H)/S^1\to^{L(P\times_B\tilde{P},F)}(T_{\tilde{P}}\oplus T_{\tilde{P}}^*,\tilde{H})/S^1$  as Courant algebroid, and thus any  $S^1$ -invariant generalized structure may be transported from (P,H) to  $(\tilde{P},\tilde{H})$ .

**Example.** 1.  $T_P^* \subset (T_p \oplus T_p^*, H)$  is a Dirac structure  $\implies T$ -dual is

$$\tau(\xi + \theta) = \xi - \tilde{\partial}_{\theta} = T^*B + \langle \partial_{\tilde{\theta}} \rangle = \Delta \oplus \text{Ann } \Delta$$
 (129)

for  $\delta = \langle \partial_{\tilde{\theta}} \rangle$ 

- 2. The induced map on twisted cohomology  $H^*_H(P) \rightleftarrows H^{*+1}_{\tilde{H}}(\tilde{P})$  is an isomorphism.
- 3. Where does  $\tau$  take the subspace  $C_+ = \Gamma_{g+b} \subset T^* \oplus T$ ? In  $TP = TB \oplus 1$ , decompose  $g = g_0\theta \odot \theta + g_1 \odot \theta + g_2, b = b_1 \wedge \theta + b_2$  for  $g_i, b_i$  basic. Then

$$C_{+} = \Gamma_{a+b} = \langle x + f \partial_{\theta} + (i_x q_2 + f q_1 + i_x b_2 - f b_1) + (q_1(x) + f q_0 + b_1(x))\theta \rangle$$
 (130)

which is mapped via  $\tau$  to

$$\Gamma_{\tilde{q}+\tilde{b}} = \langle x + (g_1(x) + fg_0 + b_1(x))\partial_{\tilde{\theta}} + (i_x g_1 + fg_1 + i_x b_2 - fb_1) + f\tilde{\theta} \rangle$$
(131)

where

$$\begin{cases}
\tilde{g} = \frac{1}{g_0}\tilde{\theta}\odot\tilde{\theta} - \frac{b_1}{g_0}\odot\tilde{\theta} + g_2 + \frac{1}{g_0}(b_1\odot b_1 - g_1\odot g_1) \\
\tilde{b} = \frac{-g_1}{g_0}\wedge\tilde{\theta} + b_2 + \frac{g_1\wedge b_1}{g_0}
\end{cases}$$
(132)

These are called "Buscher rules".

4. Elliptic Curves: