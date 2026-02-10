# All Mathematical Statements: Topics in Several Complex Variables

## Statement 1
**Theorem.** U a connected open set in $\mathbb{C}$. $f,g \in \mathcal{O}(U)$, suppose there exists an open subset V of U on which f = g. We can conclude $f \equiv g$, this is unique analytic continuation.
(Line 121)

## Statement 2
**Theorem (Maximum Modulus Principle).** U any open connected set in $\mathbb{C}$, $f \in \mathcal{O}(U)$ then if |f| has a local maximum value at some point $a \in U$ then f has to be constant.
(Line 146)

## Statement 3
**Lemma.** If $f \in \mathcal{O}(U)$ and $Ref \equiv 0$, then f is constant.
(Line 150)

## Statement 4
**Lemma.** We claim the function f defined by the integral
$$f(z) = \frac{1}{2\pi i} \int \frac{g(\eta)}{\eta - z} d\eta \wedge d\bar{\eta}$$
is in $C^{\infty}(\mathbb{C})$ and satisfies $\partial f/\partial \bar{z} = g$.
(Line 178)

## Statement 5
**Lemma.** For $f, g \in C^{\infty}(U)$, $\overline{\partial} f g = f \overline{\partial} g + g \overline{\partial} f$, thus $f g \in \mathcal{O}(U)$.
(Line 243)

## Statement 6
**Theorem.** Let $D \subseteq \mathbb{C}^n$ be the polydisk $D = D_1 \times \cdots \times D_n$ where $D_i : |z_i| < R_i$ and let $f \in \mathcal{O}(D) \cap C^{\infty}(\overline{D})$ then for any point $a = (a_1, \ldots, a_n)$
$$f(a) = \left(\frac{1}{2\pi i}\right)^n \int_{\partial D_1 \times \dots \times \partial D_n} \frac{f(z_1, \dots, z_n)}{(z_1 - a_1) \dots (z_n - a_n)} dz_1 \wedge \dots \wedge dz_n$$
(Line 265)

## Statement 7
**Theorem.** U open in $\mathbb{C}^n$, $f \in \mathcal{O}(U)$, $a \in U$ and D a polydisk centered at a with $\overline{D} \subseteq U$ then on D we have
$$f(z) = \sum_{\alpha} a_{\alpha} (z_1 - a_1)^{\alpha_1} \dots (z_n - a_n)^{\alpha_n}$$
(Line 287)

## Statement 8
**Theorem.** U is a connected open set in $\mathbb{C}^n$ with $f, g \in \mathcal{O}(U)$. If f = g on an open subset $V \subset U$ then f = g on all of U.
(Line 297)

## Statement 9
**Theorem (Maximum Modulus Principle).** U is a connected open set in $\mathbb{C}^n$, $f \in \mathcal{O}(U)$. If |f| achieves a local maximum at some point $a \in U$ then f is constant.
(Line 301)

## Statement 10
**Theorem.** Let $g \in C_0^{\infty}(\mathbb{C})$ then if f is the function
$$f(z) = \frac{1}{2\pi i} \int_{\mathbb{C}} \frac{g(\eta)}{\eta - z} d\eta \wedge d\bar{\eta}$$
then $f \in C^{\infty}(\mathbb{C})$ and $\partial f/\partial \bar{z} = g$.
(Line 308)

## Statement 11
**Theorem (Multidimensional Inhomogeneous CR equation).** If the $h_i$'s satisfy these integrability conditions then there exists an $f \in C^{\infty}(\mathbb{C}^n)$ with $\partial f/\partial \bar{z}_i = h_i$. And in fact such a solution is given by
$$f(z_1, \dots, z_n) = \frac{1}{2\pi i} \int_{\mathbb{C}} \frac{h_1(\eta_1, z_2, \dots, z_n)}{(\eta_1 - z_1)} d\eta_1 \wedge d\bar{\eta}_1$$
(Line 320)

## Statement 12
**Theorem.** Let $K \in \mathbb{C}^n$ be a compact set. Suppose $\mathbb{C}^n - K$ is connected. Suppose $h_i \in C_0^{\infty}(\mathbb{C}^n)$ are supported in K. If f is the function (*) then supp $f \subseteq K$ (unique to higher dimension). So not only do we have a solution to the ICR eqn, it is compactly supported.
(Line 340)

## Statement 13
**Theorem (Hartog's Theorem).** Let $K \subseteq U$, $U \subset \mathbb{C}^n$ is open and connected. Suppose that U - K is connected. Let $f \in \mathcal{O}(U - K)$ then f extends holomorphically to all of U. THIS IS A PROPERTY SPECIFIC TO HIGHER DIMENSIONAL SPACES.
(Line 344)

## Statement 14
**Theorem (1).** Let U and V be polydisks with $\overline{V} \subset U$. Then if $\omega \in \Omega^{0,q}(U)$ and $\overline{\partial}\omega = 0$ then there exists $\mu \in \Omega^{0,q-1}(V)$ with $\overline{\partial}\mu = \omega$ on V.
(Line 417)

## Statement 15
**Theorem (2).** If $\omega \in \Omega^{0,q}(U)_k$ and $\overline{\partial}\omega = 0$ then there exists $\beta \in \Omega^{0,q-1}(W)_{k-1}$ such that $\omega - \overline{\partial}\beta \in \Omega^{0,q}(W)_{k-1}$.
(Line 439)

## Statement 16
**Lemma.** (ICR in 1D) If $g \in C^{\infty}(U)$ with $\frac{\partial g}{\partial \bar{z}_l} = 0$, l > k then there exists $f \in C^{\infty}(W)$ such that $\frac{\partial f}{\partial \bar{z}_l} = 0$ for l > k and $\frac{\partial f}{\partial \bar{z}_k} = g$.
(Line 443)

## Statement 17
**Theorem (3).** Let U be a polydisk then the Dolbeault complex
$$\Omega^{0,0}(U) \xrightarrow{\overline{\partial}} \Omega^{0,1}(U) \xrightarrow{\overline{\partial}} \Omega^{0,2}(U) \xrightarrow{\overline{\partial}} \cdots$$
is exact. That is, you don't have to pass to sub-polydisks.
(Line 478)

## Statement 18
**Lemma.** Let U and V be as in Theorem 1 above. $\beta \in \Omega^{0,q}(U)$, $\overline{\partial}\beta = 0$ then there exists $\alpha \in \Omega^{0,q-1}(U)$ such that $\overline{\partial}\alpha = \beta$ on V.
(Line 490)

## Statement 19
**Lemma.** Let $V_0, V_1, V_2, \ldots$ be a sequence of polydisks so that $\overline{V}_r \subset V_{r+1}$ and $\bigcup V_1 = U$. (exhaustion on U by compact polydisk). There exists $\alpha_i \in \Omega^{0,q+1}(U)$ such that $\overline{\partial}\alpha_r = \beta$ on $V_r$ and such that $\alpha_{r+1} = \alpha_r$ on $V_{r-1}$.
(Line 500)

## Statement 20
**Theorem.** If $U_i \subset \mathbb{C}^n$, i = 1, 2 is pseudo-convex then $U_1 \cap U_2$ is pseudo-convex.
(Line 574)

## Statement 21
**Theorem.** The Dolbealt complex is exact on U if and only if U is pseudo-convex.
(Line 580)

## Statement 22
**Theorem.** If U is a polydisk then complex $(1)_q$ and $(2)_p$ are exact for all p,q.
(Line 614)

## Statement 23
**Theorem (Poincare Lemma).** If U is convex then $(\Omega^*(U), d)$ is exact.
(Line 655)

## Statement 24
**Theorem.** U a polydisk. Then if $\omega \in \Omega^{1,1}(U)$ and is closed then there exists a $C^{\infty}$ function f so that $\omega = \partial \overline{\partial} f$. (f is called the potential function of $\omega$).
(Line 673)

## Statement 25
**Theorem.** f is holomorphic iff $f^*(\Omega^{1,0}(V) \subseteq \Omega^{1,0}(U)$, i.e. for every $\omega \in \Omega^{1,0}(V)$, $f^*\omega \in \Omega^{1,0}(U)$.
(Line 691)

## Statement 26
**Corollary.** f holomorphic. Then $f^*\Omega^{p,q}(V) \subseteq \Omega^{p,q}(U)$, also $\omega \in \Omega^{p,q}(V)$, then $f^*d\omega = df^*\omega$, which implies that $f^*\partial\omega = \partial f^*\omega$, $f^*\overline{\partial}\omega = \overline{\partial} f^*\omega$.
(Line 699)

## Statement 27
**Theorem (Real Inverse Function Theorem).** If I is a bijective map $\mathbb{R}^n \to \mathbb{R}^n$ then f maps a neighborhood $U_1$ of p in U diffeomorphically onto a neighborhood V of f(p) in $\mathbb{R}^n$.
(Line 717)

## Statement 28
**Theorem (Holomorphic Inverse Function Theorem).** If I is a bijective map $\mathbb{C}^n \to \mathbb{C}^n$ then f maps a neighborhood $U_1$ of p in U biholomorphically onto a neighborhood V of f(p) in $\mathbb{C}^n$.
(Line 725)

## Statement 29
**Theorem.** If $df_1, \ldots, df_k$ are linearly independent at p, there exists a neighborhood $U_1$ of p in U and a neighborhood V of 0 in $\mathbb{C}^n$ and a biholomorphism $\varphi: (V,0) \to (U_1,p)$ so that
$$\varphi^* f_i = z_i \qquad i = 1, \dots, k$$
(Line 733)

## Statement 30
**Lemma.** With this topology $\mathbb{C}P^n$ is compact.
(Line 856)

## Statement 31
**Lemma.** $\mathbb{C}P^n$ is a complex n-manifold.
(Line 868)

## Statement 32
**Lemma.** The following are equivalent: (1) For all $z \in \mathbb{C}^{n+1} \setminus \{0\}$, $dP_z \neq 0$. (2) For all $z \in \mathbb{C}^{n+1} \setminus \{0\}$, P(z) = 0, $dP_z \neq 0$. We call P non-singular if one of these holds.
(Line 906)

## Statement 33
**Theorem.** If P is non-singular, X is an n-1 dimensional submanifold of $\mathbb{C}P^n$.
(Line 915)

## Statement 34
**Theorem (Uniqueness of Analytic Continuation).** X a connected complex manifold, $V \subseteq X$ is an open set, $f,g \in \mathcal{O}(X)$. If f = g on V then f = g on all of X.
(Line 934)

## Statement 35
**Lemma.** For $p, q \in X$ there exists open sets $U_i$, i = 1, ..., n such that (1) $U_i$ is biholomorphic to a connected open subset of $\mathbb{C}^n$, (2) $p \in U_1$, (3) $q \in U_n$, (4) $U_i \cap U_{i+1} \neq \emptyset$.
(Line 938)

## Statement 36
**Theorem.** If X is a connected complex manifold and $f \in \mathcal{O}(X)$ then if for some $p \in X$, $|f|: X \to \mathbb{R}$ takes a local maximum then f is constant.
(Line 945)

## Statement 37
**Corollary.** If X is compact and connected $\mathcal{O}(X) = \mathbb{C}$.
(Line 947)

## Statement 38
**Corollary.** U is open in X and $p \in U$. Then if $f \in \mathcal{O}(U)$ then $df_p \in (T_p^*)^{1,0}$.
(Line 974)

## Statement 39
**Corollary.** $(U, z_1, \ldots, z_n)$ a coordinate patch then $(dz_1)_p, \ldots, (dz_n)_p$ is a basis of $(T_p^*)^{1,0}$ and $(d\bar{z}_1)_p, \ldots, (d\bar{z}_n)_p$ is a basis of $(T_n^*)^{0,1}$.
(Line 976)

## Statement 40
**Theorem (Implicit Function Theorem in Manifold Setting).** $X^n$ a manifold. $U_0 \subseteq X$ is an open set, $f_1, \ldots, f_k \in \mathcal{O}(U_0)$, $p \in U_0$. Assume $df_1, \ldots, df_k$ are linearly independent at p. Then there exists a coordinate patch $(U, w_1, \ldots, w_n)$, $p \in U$, $U \subset U_0$ such that $w_i = f_i$ for $i = 1, \ldots, k$.
(Line 828)

## Statement 41
**Lemma.** $\delta^2 = 0$, i.e. $\delta$ is in fact a coboundary operator.
(Line 1079)

## Statement 42
**Proposition.** $\delta Q + Q\delta = id$.
(Line 1111)

## Statement 43
**Corollary.** $H^k(U, C^{\infty}) = 0$.
(Line 1113)

## Statement 44
**Theorem (Hormander).** U pseudo-convex then the Dolbeault complex on U is exact.
(Line 1135)

## Statement 45
**Theorem.** If $\mathcal{U}$ is a pseudoconvex cover then the Cech cohomology groups $H^p(\mathcal{U}, \mathcal{O})$ are identified with the cohomology groups of the Dolbeault complex
$$\Omega^{0,0}(X) \xrightarrow{\overline{\partial}} \Omega^{0,1}(X) \xrightarrow{\overline{\partial}} \Omega^{0,2}(X) \xrightarrow{\overline{\partial}} \cdots$$
(Line 1147)

## Statement 46
**Theorem.** The following sequence is exact
$$C^p(\mathcal{U}, \Omega^{0,0}) \xrightarrow{\overline{\partial}} C^p(\mathcal{U}, \Omega^{0,1}) \xrightarrow{\overline{\partial}} \cdots$$
(Line 1173)

## Statement 47
**Theorem.** If B is non-degenerate then dim V is even. Moreover, there exists a basis $e_1, \ldots, e_n, f_1, \ldots, f_n$ of V such that $B(e_i, e_n) = B(f_i, f_j) = 0$ and $B(e_i, f_j) = \delta_{ij}$.
(Line 1207)

## Statement 48
**Theorem.** $B \in Alt^2(V)$ is non-degenerate if $\omega_B \in \Lambda^2(V)$ satisfies $\omega_B^n \neq 0$.
(Line 1231)

## Statement 49
**Proposition.** On $\Lambda^{k,l}(V^*)$ we have $J^* = (\sqrt{-1})^{k-l} \operatorname{Id}$.
(Line 1285)

## Statement 50
**Theorem (Darboux Theorem).** If $\omega$ is symplectic then for every $p \in X$ there exists a coordinate patch $(U, x_1, \ldots, x_n, y_1, \ldots, y_n)$ centered at p such that on U
$$\omega = \sum dx_i \wedge dy_i$$
(Line 1331)

## Statement 51
**Theorem (Darboux).** If $\omega$ is a Kahler form then for every point $p \in X$ there exists a coordinate patch $(U, z_1, \ldots, z_n)$ centered at p and a strictly plurisubharmonic function F on U such that on $U, \omega = \sqrt{-1}\partial \bar{\partial} F$.
(Line 1385)

## Statement 52
**Theorem.** If $F_1$ and $F_2$ are potential functions for the Kahler metric $\omega$ on U then $F_1 = F_2 + (K + \overline{K})$ where $K \in \mathcal{O}(U)$.
(Line 1401)

## Statement 53
**Theorem.** There exists a unique Kaehler form $\omega$ on $\mathbb{C}P^n$ such that $\pi^*\omega = \sqrt{-1}\partial\overline{\partial} \operatorname{Log}|z^2|$. This is called the Fubini-Study symplectic form.
(Line 1450)

## Statement 54
**Lemma.** Let $\mu = \sqrt{-1}\partial \overline{\partial} \operatorname{Log} |z|^2$ on $\mathbb{C}^{n+1} - \{0\}$. Then on $O_i$ we have $\pi^* \gamma_i^* \mu = \mu$.
(Line 1454)

## Statement 55
**Corollary.** We have local existence and uniqueness of $\omega$ on each $U_i$, which implies global existence and uniqueness.
(Line 1462)

## Statement 56
**Corollary.** All complex submanifolds of $\mathbb{C}P^n$ are Kaehler.
(Line 1481)

## Statement 57
**Lemma.** $\mu$ is intrinsically defined, i.e. it is independent of F and the coordinate system.
(Line 1493)

## Statement 58
**Theorem.** Suppose that the sequence $C^{0,i} \xrightarrow{\delta} C^{1,i} \xrightarrow{\delta} C^{2,i} \xrightarrow{\delta} \cdots$ and the sequence $C^{i,0} \xrightarrow{d} C^{i,1} \xrightarrow{d} C^{i,2} \xrightarrow{d} \cdots$ are exact for all i. Then the cohomology groups of $0 \longrightarrow V_0 \xrightarrow{\delta} V_1 \xrightarrow{\delta} V_2 \xrightarrow{\delta} \cdots$ and $0 \longrightarrow W_0 \xrightarrow{d} W_1 \xrightarrow{d} W_2 \xrightarrow{d} \cdots$ are isomorphic.
(Line 1567)

## Statement 59
**Theorem.** The operator $u \in \mathcal{C}^{\infty}(U) \to e^{-itf} P e^{itf} u$ is a sum $\sum_{i=0}^{r} t^{r-i} P_i u$, $P_i$ being a differential operator of order i which doesn't depend on t. Moreover, $P_0$ is multiplication by the function $p_0(x) =: P(x, \xi)$ with $\xi_i = \frac{\partial f}{\partial x_i}$, $i = 1, \dots n$.
(Line 1620)

## Statement 60
**Corollary.** If P and Q are differential operators and $p(x,\xi)$ and $q(x,\xi)$ their symbols, the symbol of PQ is $p(x,\xi) q(x,\xi)$.
(Line 1652)

## Statement 61
**Theorem.** For $u, v \in \mathcal{C}_0^{\infty}(U)$
$$\langle Pu, v \rangle =: \int Pu\overline{v} \, dx = \langle u, P^t v \rangle.$$
(Line 1668)

## Statement 62
**Theorem.** Let $f: X \to \mathbb{R}$ be $C^{\infty}$ function. Then the operator $u \in \mathcal{C}^{\infty}(X) \to e^{-itf} P e^{-itf} u$ can be written as a sum $\sum_{i=0}^{m} t^{m-i} P_i$, $P_i$ being a differential operator of order i which doesn't depend on t.
(Line 1724)

## Statement 63
**Theorem.** There exists $C^{\infty}$ function $\sigma(P): T^*X \to \mathbb{C}$ not depending on f such that $p_0(x) = \sigma(P)(x,\xi)$ with $\xi = df_x$.
(Line 1742)

## Statement 64
**Theorem.** If $P: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$ is an $m^{th}$ order differential operator there is a unique $m^{th}$ order differential operator, $P^t$, having the property $\langle Pu, v \rangle = \langle u, P^t v \rangle$ for all $u, v \in \mathcal{C}_0^{\infty}(X)$.
(Line 1787)

## Statement 65
**Theorem (Fredholm theorem for elliptic operators).** If X is compact and $P: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$ is an elliptic differential operator, the kernel of P is finite dimensional and $u \in C^{\infty}(X)$ is in the range of P if and only if $\langle u, v \rangle = 0$ for all v in the kernel of $P^t$.
(Line 1830)

## Statement 66
**Theorem.** The elliptic operator, P is right-invertible modulo smoothing operators, i.e., there exists an operator, $Q: \mathcal{C}^{\infty}(X) \to \mathcal{C}^{\infty}(X)$ and a smoothing operator, $T_K$, such that $PQ = I - T_K$.
(Line 1875)

## Statement 67
**Theorem.** The Fredholm theorem is true for the operator, $I - T_K$, i.e., the kernel of this operator is finite dimensional, and $f \in C^{\infty}(X)$ is in the image of this operator if and only if it is orthogonal to kernel of the operator, $I - T_L$, where L(x, y) = K(y, x).
(Line 1881)

## Statement 68
**Proposition.** Every $f \in C^{\infty}(M)$ can be written uniquely as a sum $f = f_1 + f_2$ where $f_1 \in U$, $f_2 \in \text{Image } P$ and $f_1$ is orthogonal to $f_2$.
(Line 1895)

## Statement 69
**Proposition.** If $g = D^{\alpha} f$ then $c_k(g) = k^{\alpha} c_k(f)$.
(Line 1957)

## Statement 70
**Corollary.** For every integer r > 0 there exists a constant $C_r$ such that $|c_k(f)| \le C_r (1+|k|^2)^{-r/2}$.
(Line 1970)

## Statement 71
**Proposition.** The Fourier series (4.4.2) converges and this sum is a $C^{\infty}$ function.
(Line 1985)

## Statement 72
**Lemma.** If m > n the sum $\sum \left(\frac{1}{1+|k|^2}\right)^{m/2}$, $k \in \mathbb{Z}^n$, converges.
(Line 1989)

## Statement 73
**Theorem.** There exists an $a \in \mathcal{S}^{-m}$ and an $r \in \bigcap S^{\ell}$, $-\infty < \ell < \infty$, such that $PT_a = I - T_r$.
(Line 2251)

## Statement 74
**Lemma.** If $b \in S^i$ then $b - p \circ a_0 b$ is in $S^{i-1}$.
(Line 2272)

## Statement 75
**Lemma.** There exists a sequence of symbols $a_i \in \mathcal{S}^{-m-i}$, i = 0, 1, ..., and a sequence of symbols $r_i \in \mathcal{S}^{-i}$, i = 0, ..., such that $a_0$ is the symbol (5.5.1), $r_0 = 1$ and $p \circ a_i = r_i - r_{i+1}$ for all i.
(Line 2285)

## Statement 76
**Lemma.** If $a(x,\xi)$ is in $S^m$ and $w \in \mathbb{R}^n$, the function, $a_w(x,\xi) = a(x,\xi+w) - a(x,\xi)$ is in $S^{m-1}$.
(Line 2343)

## Statement 77
**Lemma.** $K_a(x,y)$ is a $\mathcal{C}^{\infty}$ function on the complement of the diagonal in $T^n \times T^n$.
(Line 2378)

## Statement 78
**Theorem.** There exist symbols, $a \in S^{-m}$ and $r \in S^{-\infty}$ such that $P\iota_{U}^* T_a = \iota_{U}^* (I - T_r)$.
(Line 2407)

## Statement 79
**Theorem.** $P: C^{\infty}(E^1) \to C^{\infty}(E^2)$ is an mth order elliptic differential operator, then there exists an "mth order $\Psi DO$", $Q: C^{\infty}(E^2) \to C^{\infty}(E^1)$ such that $PQ-I$ is smoothing.
(Line 2595)

## Statement 80
**Lemma.** Given $p \in X$, there exists a neighborhood U of p and a Hermitian trivialization of $E_U$: for $p \in U$, $E_p \cong \mathbb{C}^k$ and $\gamma_U$ hermitian if $E_p \cong \mathbb{C}^k$ is an isomorphism of hermitian vector spaces.
(Line 2611)

## Statement 81
**Theorem.** $E^i \to X$, i = 1, 2 Hermitian vector bundles and $P: C^{\infty}(E^1) \to C^{\infty}(E^2)$ an mth order DO, then there exists a unique mth order DO, $P^t: C^{\infty}(E^2) \to C^{\infty}(E^1)$ such that for $f \in C^{\infty}(E^1)$, $g \in C^{\infty}(E^2)$, $\langle Pf, g \rangle_{L^2} = \langle f, P^t g \rangle_{L^2}$.
(Line 2617)

## Statement 82
**Theorem (Main Theorem).** X compact, $E^i \to X$, i=1,2 hermitian bundles of rank k. And $P: C^{\infty}(E^1) \to C^{\infty}(E^2)$ an m order elliptic DO then (a) ker P is finite dimensional, (b) $f \in \text{Im } P$ if and only if $\langle f, g \rangle = 0$ for all $g \in \ker P^t$.
(Line 2629)

## Statement 83
**Theorem.** For $\mu \in \Lambda^k(T_x^*) \otimes \mathbb{C}$, $\sigma_{\xi}\mu = \sqrt{-1}\xi \wedge \mu$.
(Line 2664)

## Statement 84
**Theorem.** The de Rham complex is elliptic.
(Line 2670)

## Statement 85
**Theorem.** For $\mu \in \Lambda^{0,k}(T_x^*)$, $\sigma_{\xi}(\mu) = \sqrt{-1}\xi^{0,1} \wedge \mu$.
(Line 2686)

## Statement 86
**Theorem (Hodge Decomposition Theorem).** (a) For all k, $\mathcal{H}^k$ is finite dimensional. (b) Every element u of $C^{\infty}(E^k)$ can be written uniquely as a sum $u_1 + u_2 + u_3$ where $u_1 \in \text{Im}(D)$, $u_2 \in \text{Im}(D^t)$, $u_3 \in \mathcal{H}^k$.
(Line 2732)

## Statement 87
**Lemma.** $\mathcal{H}^k = \ker Q$.
(Line 2773)

## Statement 88
**Theorem.** There exists a bijective map $*: \Lambda^k(V) \to \Lambda^{n-k}(V)$ such that for $\alpha, \beta \in \Lambda^k(V)$ we have $\alpha \wedge *\beta = B(\alpha, \beta)\Omega$.
(Line 2811)

## Statement 89
**Theorem.** With $\beta_1 \in \Lambda^r(V_1)$ and $\beta_2 \in \Lambda^s(V_2)$ we have $*(\beta_1 \wedge \beta_2) = (-1)^{(n_1 - r)s} *_1 \beta_1 \wedge *_2 \beta_2$.
(Line 2839)

## Statement 90
**Theorem.** For $\alpha \in \Lambda^{p-1}$, $\beta \in \Lambda^p$, $B(L_u\alpha,\beta) = B(\alpha, L_u^t\beta)$ where $L_u^t = (-1)^{p-1} *^{-1} L_u * := \widetilde{L}_u$.
(Line 2891)

## Statement 91
**Theorem.** If $v^* = L_{B^\sharp}u$, then $L_u^t = i_{v^*}$.
(Line 2906)

## Statement 92
**Theorem.** On $\Lambda^{p+1}$, $(i_{v^*})^t = (-1)^p *^{-1} (i_{v^*})^*$ and $v^* = L_B u$.
(Line 2918)

## Statement 93
**Theorem (Kaehler, Weil).** $[L, L^t] = (p - n) \operatorname{Id}$.
(Line 2932)

## Statement 94
**Proposition.** $L^t = *^{-1}L*$.
(Line 2957)

## Statement 95
**Proposition.** $u \in V$ then $[L_u^t, L] = -L_u$.
(Line 2959)

## Statement 96
**Theorem.** $[\delta, L] = d$.
(Line 2995)

## Statement 97
**Theorem (Hard Lefshetz).** $\gamma^p: H^{n-p}(X, \mathbb{C}) \to H^{n+p}(X)$ is bijective.
(Line 3039)

## Statement 98
**Lemma.** $[A, L^t] = 2L^t$.
(Line 3043)

## Statement 99
**Lemma.** $[A, L] = -2L$.
(Line 3048)

## Statement 100
**Lemma.** $\Omega_{harm}$ is a g-module of $\Omega$.
(Line 3062)

## Statement 101
**Theorem.** If V is a g-module of finite type, then every sub and quotient module is of finite type.
(Line 3080)

## Statement 102
**Lemma.** Take $v \in V$, $Hv = \lambda v$. We claim that $H(Xv) = (\lambda + 2)Xv$.
(Line 3090)

## Statement 103
**Lemma.** If $Hv = \lambda v$, then $[X, Y^k]v = k(\lambda - (k-1))Y^{k-1}v$.
(Line 3096)

## Statement 104
**Theorem.** If V is a cyclic module of finite H type then $\dim V < \infty$.
(Line 3106)

## Statement 105
**Theorem.** Every irreducible g-module of finite H type is of the form $V = V_0 \oplus \cdots \oplus V_k$ where dim $V_i = 1$. Moreover, there exists $v_i \in V_i - \{0\}$ such that $Hv_{i} = (k-2i)v_{i}$, $Yv_{i} = v_{i+1}$ for $i \le k-1$, $Xv_{i} = i(k-(i-1))v_{i-1}$ for $i \ge 1$, $Xv_{0} = 0, Yv_{k} = 0$.
(Line 3118)

## Statement 106
**Lemma.** Let V be a k+1 dimensional vector space with basis $v_0, \ldots, v_k$. Then the relations in the above theorem define an irreducible representation of g on V.
(Line 3140)

## Statement 107
**Theorem.** If v is primitive then the cyclic submodule generated by v is irreducible and Hv = k where k is the dimension of this module.
(Line 3147)

## Statement 108
**Theorem.** Every vector $v \in V$ can be written as a finite sum $v = \sum Y^l v_l$ where $v_l$ is primitive.
(Line 3153)

## Statement 109
**Corollary.** The eigenvalues of H are integers.
(Line 3161)

## Statement 110
**Theorem.** We can repage the sum so that $V = \bigoplus_{i=-N}^{N} V_i$ where $H = iId$ on $V_i$. (a) $X: V_i \rightarrow V_{i+2}$ and $Y: V_{i+2} \rightarrow V_i$. (b) $Y^iV_i \xrightarrow{\cong} V_{-i}$ is bijective.
(Line 3167)

## Statement 111
**Corollary.** The map $L^k: \Omega^{n-k} \to \Omega^{n+k}$ is an isomorphism.
(Line 3185)

## Statement 112
**Theorem.** $\Omega_{harm}$ is a g-module of $\Omega$.
(Line 3193)

## Statement 113
**Corollary.** The map $L^k: \Omega_{harm}^{n-k} \to \Omega_{harm}^{n+k}$ is bijective.
(Line 3195)

## Statement 114
**Theorem.** Let X be Kaehler then $\gamma^k: H^{n-k}(X) \to H^{n+k}(X)$ is bijective.
(Line 3201)

## Statement 115
**Theorem.** (Matthieu) Hard Lefshetz holds for X if and only if $P_k$ is onto for all k.
(Line 3205)

## Statement 116
**Theorem (Poincare).** The pairing $P^{\sharp}: H^k_{DR} \times H^{n-k}_{DR} \to \mathbb{C}$ is a non-degenerate pairing.
(Line 3282)

## Statement 117
**Lemma.** $\delta: \Omega^k \to \Omega^{k-1}$ is given by $\delta = (-1)^k *^{-1} d*$.
(Line 3286)

## Statement 118
**Corollary.** $*\mathcal{H}^k = \mathcal{H}^{n-k}$.
(Line 3301)

## Statement 119
**Lemma.** If $B_s$ and J are compatible if and only if the bilinear form $B_r(v, w) = B_s(v, Jw)$ is symmetric. (Here $B_r$ is a Riemannian metric).
(Line 3317)

## Statement 120
**Lemma.** $d, d^{\mathbb{C}}$ anti-commute.
(Line 3493)

## Statement 121
**Theorem.** d and $d_{\mathbb{C}}$ anti-commute.
(Line 3461)

## Statement 122
**Corollary.** Let $\Delta = d\delta + \delta d$. Then L and $L^t$ commute with $\Delta$.
(Line 3465)

## Statement 123
**Lemma.** The identities $\overline{\partial}\partial^t + \partial^t \overline{\partial} = 0$ and $\overline{\partial}^t \partial + \partial \overline{\partial}^t = 0$ imply $\Delta = \Delta_{\partial} + \Delta_{\overline{\partial}}$.
(Line 3526)

## Statement 124
**Theorem.** $d\tau$ is a morphism of lie algebras.
(Line 3609)

## Statement 125
**Theorem.** If $\tau$ is free and proper then M/G is a differentiable manifold and $\pi: M \to M/G$ is a smooth fibration.
(Line 3641)

## Statement 126
**Theorem.** If $\tau$ is free and proper the orbit space M/G is a complex manifold and the fibration $\pi: M \to M/G$ is a holomorphic fiber mapping.
(Line 3666)

## Statement 127
**Theorem.** $\omega$ is basic if and only if there exists a $\nu \in \Omega^k(B)$ with $\omega = \pi^* \nu$.
(Line 3764)

## Statement 128
**Lemma.** For $p \in M$ and $q = \pi(p)$ then the sequence $0 \longrightarrow T_p G \circ p \xrightarrow{i} T_p M \xrightarrow{d\pi_p} T_q B$ is exact.
(Line 3768)

## Statement 129
**Lemma.** If $\iota(v_M)\mu_p=0$ for all $v\in\mathfrak{g}$ there exists a $\nu_q\in\Lambda^k(T^*B)$ with $(d\pi_p)^*\nu_q=\mu_p$.
(Line 3776)

## Statement 130
**Proposition.** (a) Z is G-invariant. (b) The action of G on Z is locally free.
(Line 3782)

## Statement 131
**Proposition.** Let $i: Z \to M$ be inclusion and $\pi: Z \to Z/G = M_{red}$. There exists a unique symplectic form $\omega_{red}$ on $M_{red}$ with the property that $\iota^*\omega = \pi^*\omega_{red}$. So the orbit space has a god-given symplectic form.
(Line 3793)

## Statement 132
**Theorem.** (a) $\operatorname{Im}(d\Phi_p) = \mathfrak{g}_p^{\perp}$. (b) $\ker d\Phi_p = (T_p G \circ p)^{\perp}$.
(Line 3736)

## Statement 133
**Lemma.** At every $p \in M$, $w_M(p) = J_p v_M(p)$.
(Line 3839)

## Statement 134
**Proposition.** If $v \in \mathfrak{g}$, $w = \sqrt{-1}v$, then the vector field $w_M$ is the Riemannian gradient of $\phi^v$.
(Line 3845)

## Statement 135
**Theorem (Main Theorem).** (a) $M_{st}$ is an open $G_{\mathbb{C}}$-invariant subset of M. (b) $G_{\mathbb{C}}$ acts freely and properly on $M_{st}$. (c) Every $G_{\mathbb{C}}$ orbit in $M_{st}$ intersects Z in a unique G-orbit. (d) Hence $M_{st}/G_{\mathbb{C}} = Z/G = M_{red}$. (e) $\omega_{red}$ is Kaehler.
(Line 3857)

## Statement 136
**Lemma.** $(d\psi)_{0,p}$ maps $\sqrt{-1}\mathfrak{g}$ bijectively onto $(T_pZ)_p^{\perp}$ in $T_pM$.
(Line 3872)

## Statement 137
**Lemma.** If $p \in Z$ and $w \in \sqrt{-1}\mathfrak{g} - \{0\}$. Then $(\exp w_M)(p) \notin Z$.
(Line 3882)

## Statement 138
**Theorem.** $\tau$ is a Hamiltonian action with moment map $\Phi:\mathbb{C}^d\to\mathfrak{g}^*$ where $\Phi(z) = \sum |z_i|^2 \alpha_i$.
(Line 3943)

## Statement 139
**Theorem.** If $\alpha_1, \ldots, \alpha_d$ are polarized then $\Phi : \mathbb{C}^d \to \mathfrak{g}^*$ is proper.
(Line 3963)

## Statement 140
**Theorem.** (a) $G_z = \{ \exp v \mid \alpha_i(v) \in 2\pi \mathbb{Z} \text{ for all } i \in I_z \}$. (b) $\mathfrak{g}_z = \{ v \mid \alpha_i(v) = 0 \text{ for all } i \in I_z \}$.
(Line 3971)

## Statement 141
**Corollary.** $\tau$ is locally free at z if and only if $span_{\mathbb{R}}\{\alpha_i, i \in I_z\} = \mathfrak{g}^*$. $\tau$ is free at z if and only if $span_{\mathbb{Z}}\{\alpha_i, i \in I_z\} = \mathbb{Z}_G^*$.
(Line 3976)

## Statement 142
**Theorem.** $a \in \mathfrak{g}^*$ is a regular value of $\Phi$ if and only if for all $I \in \mathcal{I}_{\Delta_a}$ we have $span_{\mathbb{R}}\{\alpha_i, i \in I\} = \mathfrak{g}^*$ and G acts freely on $\Phi^{-1}(a)$ if and only if $span_{\mathbb{Z}}\{\alpha_i, i \in I\} = \mathbb{Z}_G^*$.
(Line 3992)

## Statement 143
**Theorem.** There exists a unique symplectic form $\omega_a$ on $M_a$ such that $\pi^*\omega_a = i^*\omega$.
(Line 4002)

## Statement 144
**Theorem.** $\mathbb{C}^d_{stable}(a) = \bigcup_{I \in \mathcal{I}_{\Delta}} \mathbb{C}^d_I$ where $\mathbb{C}_I^d = \{ z \in \mathbb{C}^d \mid I_z = I \}$.
(Line 4012)

## Statement 145
**Theorem.** $\alpha_i$'s are polarized if and only if $\Phi$, the moment map, is proper.
(Line 4036)

## Statement 146
**Theorem (1).** a is a regular value of $\Phi$ if and only if for every vertex $v_I$ of $\Delta_a$, $\alpha_i, i \in I$ are a basis of $\mathfrak{g}^*$.
(Line 4066)

## Statement 147
**Theorem (2).** (a) a is a regular value of the moment map $\Phi$ if and only if for every vertex $v_I$ of $\Delta_a$, $\alpha_i, i \in I$ are a basis of $\mathfrak{g}^*$. (b) G acts freely on $\Phi^{-1}(a)$ if and only if for every vertex $v_I$ of $\Delta_a$, $\alpha_i, i \in I$ are a lattice basis for $\mathbb{Z}_G^*$.
(Line 4078)

## Statement 148
**Theorem.** Let $f: M \to \mathbb{R}$ be a Morse function with the property that ind p is even for all $p \in Crit(f)$. Then $H^{2k+1}(M) = 0$ and $H^{2k}(M) = \{ p \in Crit(f), \text{ ind } p = 2k \}$.
(Line 4124)

## Statement 149
**Theorem (Main Theorem).** Assume for $v, v' \in Vert(\Delta_a)$, v, v' adjacent that $\langle v - v', \xi \rangle \neq 0$. Then (a) $f: M_a \to \mathbb{R}$ is Morse, (b) $\psi: M_a \to \Delta_a$ maps Crit(f) bijectively onto $Vert(\Delta_a)$, (c) For $p \in Crit(f)$ and v the corresponding vertex let $v_1, \ldots, v_m$ be the vertices adjacent to v. Then $\frac{ind_p}{2} = \#\{v_i \mid \langle v_i - v, \xi \rangle < 0\} := ind_v \xi$.
(Line 4147)

## Statement 150
**Corollary.** $H^{2k+1}(M_a) = 0$ and $b_k = \dim H^{2k}(M_a) = \#\{v \in Vert(\Delta_a), ind_v \xi = k\}$, that is, $b_k$ is independent of $\xi$.
(Line 4159)

## Statement 151
**Theorem (1).** a is a regular value if $\Delta_a$ is a simple n-dimensional polytope.
(Line 4178)

## Statement 152
**Theorem (2).** Suppose that for all adjacent v, v' of $\Delta_a$ we have $\langle v - v', \xi \rangle \neq 0$. Then (a) f is Morse, (b) $\psi$ maps Crit(f) bijectively onto $Vert(\Delta_a)$, (c) For $q \in Crit(f)$, $ind_q = ind_{\xi} v$ where $v = \psi(q)$.
(Line 4198)

## Statement 153
**Theorem.** a is a regular value if and only if for every vertex $v_I$ of $\Delta_a$, $\alpha_i$, $i \in I$ form a basis of $\mathfrak{g}^*$.
(Line 4214)

## Statement 154
**Proposition.** $\gamma^{-1}(v_I)$ is a single G-orbit.
(Line 4247)

## Statement 155
**Theorem (McMullen, Stanley).** (a) The $b_k$'s are integers. (b) $b_{m-k} = b_k$. (c) $b_0 \leq b_1 \leq \cdots \leq b_k$ where $k = \lceil \frac{m}{2} \rceil$.
(Line 4289)
