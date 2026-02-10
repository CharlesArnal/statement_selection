# All Statements from Analysis II

## Statement 1: Definition 1.1
Let X be a set. Define the Cartesian product $X \times X = \{(x, y) : x, y \in X\}$.

## Statement 2: Definition 1.2
Let $d: X \times X \to \mathbb{R}$ be a mapping. The mapping d is a *metric on* X if the following four conditions hold for all $x, y, z \in X$: (1) $d(x, y) \ge 0$; (2) $d(x, y) = 0$ iff $x = y$; (3) $d(x, y) = d(y, x)$; (4) $d(x, z) \le d(x, y) + d(y, z)$ (triangle inequality).

## Statement 3: Definition 1.3
Given a point $x_o \in X$, and a real number $\epsilon > 0$, we define $U(x_o, \epsilon) = \{x \in X : d(x, x_o) < \epsilon\}$, the open ball of radius $\epsilon$ centered at $x_o$.

## Statement 4: Definition 1.4
A subset U of X is open if for every $x_o \in U$ there exists a real number $\epsilon > 0$ such that $U(x_o, \epsilon) \subseteq U$.

## Statement 5: Proposition 1.5
Let $\{U_{\alpha}, \alpha \in I\}$ be a collection of open sets in X, where I is just a labeling set that can be finite or infinite. Then, the set $U = \bigcup_{\alpha \in I} U_{\alpha}$ is open.

## Statement 6: Corollary 1
If $Y \subset X$ and A is open in Y (w.r.t. $d_Y$), then there exists an open set U in X such that $U \cap Y = A$.

## Statement 7: Proposition 1.6
Let $\{U_i, i = 1, ..., N\}$ be a finite collection of open sets in X. Then the set $U = \bigcap_{i=1}^{N} U_i$ is open.

## Statement 8: Definition 1.7
Define the *complement of* A *in* X to be $A^c = X - A = \{x \in X : x \notin A\}$.

## Statement 9: Definition 1.8
The set A is closed in X if $A^c$ is open in X.

## Statement 10: Definition 1.9
Let $x \in \mathbb{R}^n$, written out in component form as $x = (x_1, x_2, \dots, x_n)$. The *Euclidean norm* of x is $\|x\| = \sqrt{x_1^2 + x_2^2 + \dots + x_n^2}$.

## Statement 11: Proposition 1.10
A subset U of $\mathbb{R}^n$ is open w.r.t. the $\| \|$ distance function if and only if it is open w.r.t. the $\| \|_\infty$ distance function.

## Statement 12: Definition 1.11
The function f is *continuous at* $x_o$ if for every $\epsilon > 0$ there exists a $\delta > 0$ such that $d(x, x_o) < \delta$ implies $d(f(x), f(x_o)) < \epsilon$.

## Statement 13: Definition 1.12
The function f is *continuous* if f is continuous at every point $x_o \in X$.

## Statement 14: Theorem 1.13
The function f is continuous if and only if for every open subset U of Y, the pre-image $f^{-1}(U)$ is open in X.

## Statement 15: Definition 1.14
The map f is a *homeomorphism* if f is bijective and both f and $f^{-1}$ are continuous.

## Statement 16: Definition 1.15
A sequence of points $x_1, x_2, \ldots$ in X converges to $x \in X$ if for every $\epsilon > 0$ there exists an $N > 0$ such that $d(x_n, x) < \epsilon$ for all $n > N$.

## Statement 17: Theorem 1.16
The function $f: X \to Y$ is continuous at $x_0 \in X$ if and only if for every sequence $(x_n)$ converging to $x_0$, the sequence $(f(x_n))$ converges to $f(x_0)$.

## Statement 18: Definition 1.17
A subset A of X is *bounded* if A is contained in some ball $U(x_0, r)$.

## Statement 19: Proposition 1.18
Let X be a metric space and A a subset. The closure $\bar{A}$ is the set of all points $x \in X$ such that for every $\epsilon > 0$, $U(x, \epsilon) \cap A \neq \emptyset$. Equivalently, $\bar{A}$ is the smallest closed set containing A.

## Statement 20: Definition 1.19
A set A in a metric space X is *compact* if every sequence in A has a convergent subsequence whose limit is in A.

## Statement 21: Theorem 1.20 (Heine-Borel)
A subset A of $\mathbb{R}^n$ is compact if and only if it is closed and bounded.

## Statement 22: Theorem 1.21
Let X be a compact metric space and let $f: X \to Y$ be a continuous map. Then $f(X)$ is compact.

## Statement 23: Corollary 2
If $f: X \to \mathbb{R}$ is continuous and X is compact, then f achieves its maximum and minimum values.

## Statement 24: Theorem 1.22
Let $f: X \to Y$ be a continuous bijective map where X is compact. Then $f^{-1}$ is also continuous (f is a homeomorphism).

## Statement 25: Definition 1.23
A collection of open sets $\{U_\alpha\}$ is an *open covering* of A if $A \subseteq \bigcup U_\alpha$.

## Statement 26: Theorem 1.24 (Heine-Borel, open cover version)
A metric space X is compact if and only if every open covering of X has a finite subcovering.

## Statement 27: Proposition 1.25
A closed subset of a compact set is compact.

## Statement 28: Theorem 1.26
A continuous function on a compact metric space is uniformly continuous.

## Statement 29: Definition 1.27
A set X is *connected* if it cannot be written as $X = U_1 \cup U_2$ where $U_1, U_2$ are non-empty disjoint open sets.

## Statement 30: Theorem 1.28
The continuous image of a connected set is connected.

## Statement 31: Theorem 1.29 (Intermediate Value Theorem)
If $f: [a,b] \to \mathbb{R}$ is continuous and $f(a) < c < f(b)$, then there exists $x \in (a,b)$ such that $f(x) = c$.

## Statement 32: Definition 2.1
Let U be an open set in $\mathbb{R}^n$. A map $f: U \to \mathbb{R}^m$ is differentiable at $p \in U$ if there exists a linear map $A: \mathbb{R}^n \to \mathbb{R}^m$ such that $\lim_{h \to 0} \frac{|f(p+h) - f(p) - Ah|}{|h|} = 0$.

## Statement 33: Definition 2.2
The linear map A in Definition 2.1 is called the *derivative* (or *total derivative*) of f at p, denoted $Df(p) = A$.

## Statement 34: Proposition 2.3
If f is differentiable at p, then $Df(p)$ is unique.

## Statement 35: Theorem 2.4
If f is differentiable at p, then f is continuous at p.

## Statement 36: Theorem 2.5 (Chain Rule)
Let $f: U \to V$ and $g: V \to \mathbb{R}^k$, where U is open in $\mathbb{R}^n$ and V is open in $\mathbb{R}^m$. If f is differentiable at p and g is differentiable at $f(p)$, then $g \circ f$ is differentiable at p and $D(g \circ f)(p) = Dg(f(p)) \circ Df(p)$.

## Statement 37: Definition 2.6
The partial derivative of $f$ with respect to $x_i$ at $p$ is $\frac{\partial f}{\partial x_i}(p) = \lim_{t \to 0} \frac{f(p + te_i) - f(p)}{t}$.

## Statement 38: Theorem 2.7
If f is differentiable at p, then all partial derivatives exist and $Df(p)$ is the matrix $\left[\frac{\partial f_i}{\partial x_j}(p)\right]$.

## Statement 39: Theorem 2.8
If all partial derivatives $\frac{\partial f_i}{\partial x_j}$ exist and are continuous in a neighborhood of p, then f is differentiable at p.

## Statement 40: Definition 2.9
A map f is $\mathcal{C}^1$ on U if all partial derivatives exist and are continuous on U. More generally, f is $\mathcal{C}^k$ if all partial derivatives up to order k exist and are continuous.

## Statement 41: Definition 2.10
A map f is $\mathcal{C}^\infty$ (smooth) if it is $\mathcal{C}^k$ for all $k \ge 0$.

## Statement 42: Theorem 2.11 (Inverse Function Theorem)
Let U be open in $\mathbb{R}^n$ and $f: U \to \mathbb{R}^n$ be $\mathcal{C}^r$ with $r \ge 1$. If $Df(p)$ is invertible at some $p \in U$, then there exist neighborhoods $U_0$ of p and $V_0$ of $f(p)$ such that $f: U_0 \to V_0$ is a $\mathcal{C}^r$ diffeomorphism.

## Statement 43: Definition 2.12
A map $f: U \to V$ is a $\mathcal{C}^r$ *diffeomorphism* if f is bijective, $\mathcal{C}^r$, and $f^{-1}$ is $\mathcal{C}^r$.

## Statement 44: Theorem 2.13 (Implicit Function Theorem)
Let U be open in $\mathbb{R}^n \times \mathbb{R}^m$ and $F: U \to \mathbb{R}^m$ be $\mathcal{C}^r$, $r \ge 1$. Suppose $F(a, b) = 0$ and the partial derivative $D_y F(a, b)$ is invertible. Then there exist neighborhoods $U_0$ of a and $V_0$ of b and a $\mathcal{C}^r$ map $g: U_0 \to V_0$ such that $F(x, g(x)) = 0$ for all $x \in U_0$.

## Statement 45: Definition 3.1
A $\mathcal{C}^{\infty}$ bump function $\rho$ supported in a ball $B(0, \delta)$ satisfies: (i) $\rho \ge 0$, (ii) $\rho(x) = 0$ for $|x| \ge \delta$, (iii) $\int \rho = 1$.

## Statement 46: Definition 3.2
The *convolution* of $f$ and $g$ is $(f * g)(x) = \int f(x - y)g(y) dy$.

## Statement 47: Theorem 3.3
Let $f \in \mathcal{C}_0^{\infty}(\mathbb{R}^n)$ and $g \in L^1(\mathbb{R}^n)$. Then $f * g \in \mathcal{C}^{\infty}(\mathbb{R}^n)$.

## Statement 48: Definition 3.4
The *support* of a function $f$ is $\text{supp } f = \overline{\{x : f(x) \neq 0\}}$.

## Statement 49: Theorem 3.5 (Existence of Partitions of Unity)
Given an open cover $\{U_\alpha\}$ of an open set $U \subseteq \mathbb{R}^n$, there exists a partition of unity $\{\rho_i\}$ subordinate to $\{U_\alpha\}$.

## Statement 50: Definition 3.6
A *partition of unity subordinate to* $\{U_\alpha\}$ is a collection of $\mathcal{C}^\infty$ functions $\rho_i$ such that (i) $0 \le \rho_i$, (ii) supp $\rho_i$ is compact and contained in some $U_\alpha$, (iii) $\sum \rho_i = 1$, and (iv) the collection is locally finite.

## Statement 51: Definition 4.1
Let V be a vector space over $\mathbb{R}$. The *dual space* $V^*$ is the set of all linear maps $\ell: V \to \mathbb{R}$.

## Statement 52: Definition 4.2
Let $V$ be an $n$-dimensional vector space with basis $e_1, \ldots, e_n$. The *dual basis* $e_1^*, \ldots, e_n^*$ of $V^*$ is defined by $e_i^*(e_j) = \delta_{ij}$.

## Statement 53: Definition 4.3
A *$k$-tensor on V* is a function $T: V^k \to \mathbb{R}$ that is multilinear (linear in each argument).

## Statement 54: Definition 4.4
The *tensor product* $T_1 \otimes T_2$ of a $k$-tensor $T_1$ and an $\ell$-tensor $T_2$ is the $(k+\ell)$-tensor defined by $T_1 \otimes T_2(v_1, \ldots, v_k, v_{k+1}, \ldots, v_{k+\ell}) = T_1(v_1, \ldots, v_k) T_2(v_{k+1}, \ldots, v_{k+\ell})$.

## Statement 55: Definition 4.5
A $k$-tensor T on V is *alternating* if for any permutation $\sigma \in S_k$, $T(v_{\sigma(1)}, \ldots, v_{\sigma(k)}) = (-1)^\sigma T(v_1, \ldots, v_k)$.

## Statement 56: Definition 4.6
The space $\Lambda^k(V^*)$ is the space of all alternating $k$-tensors on $V$.

## Statement 57: Definition 4.7
The *alternation operator* $\text{Alt}: \mathcal{L}^k(V^*) \to \Lambda^k(V^*)$ is defined by $\text{Alt}(T)(v_1, \ldots, v_k) = \frac{1}{k!} \sum_{\sigma \in S_k} (-1)^\sigma T(v_{\sigma(1)}, \ldots, v_{\sigma(k)})$.

## Statement 58: Theorem 4.8
$\dim \Lambda^k(V^*) = \binom{n}{k}$ for an $n$-dimensional vector space $V$.

## Statement 59: Definition 4.9
The *wedge product* $\omega \wedge \mu$ of $\omega \in \Lambda^k(V^*)$ and $\mu \in \Lambda^\ell(V^*)$ is defined by $\omega \wedge \mu = \frac{(k+\ell)!}{k!\ell!} \text{Alt}(\omega \otimes \mu)$.

## Statement 60: Theorem 4.10
The wedge product is associative: $(\omega \wedge \mu) \wedge \nu = \omega \wedge (\mu \wedge \nu)$.

## Statement 61: Theorem 4.11
If $\omega \in \Lambda^k(V^*)$ and $\mu \in \Lambda^\ell(V^*)$, then $\omega \wedge \mu = (-1)^{k\ell} \mu \wedge \omega$.

## Statement 62: Theorem 4.12
If $e_1^*, \ldots, e_n^*$ is the dual basis, then $\{e_{i_1}^* \wedge \cdots \wedge e_{i_k}^* : 1 \le i_1 < \cdots < i_k \le n\}$ is a basis for $\Lambda^k(V^*)$.

## Statement 63: Theorem 4.13
If $\omega_1, \ldots, \omega_k \in V^*$ and $v_1, \ldots, v_k \in V$, then $\omega_1 \wedge \cdots \wedge \omega_k(v_1, \ldots, v_k) = \det[\omega_i(v_j)]$.

## Statement 64: Definition 4.14
Let $A: V \to W$ be a linear map. The *pullback* $A^*: \Lambda^k(W^*) \to \Lambda^k(V^*)$ is defined by $(A^*\omega)(v_1, \ldots, v_k) = \omega(Av_1, \ldots, Av_k)$.

## Statement 65: Theorem 4.15
If $A: V \to W$ is linear and $\omega \in \Lambda^k(W^*)$, $\mu \in \Lambda^\ell(W^*)$, then $A^*(\omega \wedge \mu) = A^*\omega \wedge A^*\mu$.

## Statement 66: Definition 4.16
Let $V$ be $n$-dimensional. Define $\det(A)$ for $A: V \to V$ by $A^*\omega = \det(A)\omega$ for any $\omega \in \Lambda^n(V^*)$.

## Statement 67: Theorem 4.17
$\det(AB) = \det(A)\det(B)$.

## Statement 68: Theorem 4.18
$\det(A) = \det(A^t)$.

## Statement 69: Definition 4.33
An *orientation of* $\mathbb{L}$ (a one-dimensional vector space) is a choice of one of the two connected components of $\mathbb{L} - \{0\}$.

## Statement 70: Definition 4.34
An orientation of V is an orientation of $\Lambda^n(V^*)$. That is, a choice of $\Lambda^n(V^*)_+$.

## Statement 71: Definition 4.35
The basis $e_1, \ldots, e_n$ is positively oriented if $\omega = e_1^* \wedge \cdots \wedge e_n^* \in \Lambda^n(V^*)_+$.

## Statement 72: Definition 4.36
The tangent space of p in $\mathbb{R}^n$ is $T_p \mathbb{R}^n = \{ (p, v) : v \in \mathbb{R}^n \}$.

## Statement 73: Definition 4.37
The cotangent space of $\mathbb{R}^n$ at p is the space $T_p^* \mathbb{R}^n \equiv (T_p \mathbb{R}^n)^*$, the dual of the tangent space.

## Statement 74: Definition 4.38
Let U be an open subset of $\mathbb{R}^n$. A k-form on U is a function $\omega$ which assigns to every point $p \in U$ an element $\omega_p$ of $\Lambda^k(T_p^*\mathbb{R}^n)$.

## Statement 75: Definition 4.39
The k-form $\omega$ is $\mathcal{C}^r(U)$ if each coefficient function $a_I \in \mathcal{C}^r(U)$.

## Statement 76: Definition 4.40
$\Omega^k(U)$ = the set of all $\mathcal{C}^{\infty}$ k-forms on U.

## Statement 77: Definition 4.41
We define $\Lambda^0(T_p^*\mathbb{R}^n) = \mathbb{R}$.

## Statement 78: Definition 4.42
A k-form $\omega \in \Omega^k(U)$ is decomposable if $\omega = \mu_1 \wedge \cdots \wedge \mu_k$, where each $\mu_i \in \Omega^1(U)$.

## Statement 79: Theorem 4.43
If $\omega$ is decomposable, i.e. $\omega = \mu_1 \wedge \cdots \wedge \mu_k$, then $d\omega = \sum_{i=1}^{k} (-1)^{i-1} \mu_1 \wedge \dots \wedge \mu_{i-1} \wedge d\mu_i \wedge \mu_{i+1} \wedge \dots \wedge \mu_k$.

## Statement 80: Definition 4.44
$f^*\omega$ is the k-form whose value at $p \in U$ is $(df_p)^*\omega_q$, where $q = f(p)$.

## Statement 81: Theorem 4.45
Let $\omega \in \Omega^k(V)$. Then $df^*\omega = f^*d\omega$.

## Statement 82: Definition 5.1
The support of $\omega$ is $\operatorname{supp} \omega = \overline{\{p \in U : \omega_p \neq 0\}}$.

## Statement 83: Definition 5.2
The k-form $\omega$ is compactly supported if supp $\omega$ is compact. We define $\Omega_c^k(U)$ = the space of all compactly supported k-forms.

## Statement 84: Definition 5.3
$\int_{U} \omega \equiv \int_{U} \phi = \int_{U} \phi(x) dx_{1} \dots dx_{n}$ where $\omega = \phi(x)dx_1 \wedge \dots \wedge dx_n$.

## Statement 85: Definition 5.4
The map f is orientation preserving if $\det\left[\frac{\partial f_i}{\partial x_j}(p)\right] > 0$ everywhere. The map f is orientation reversing if $\det < 0$ everywhere.

## Statement 86: Theorem 5.5 (Change of Variables)
If $\omega \in \Omega_c^n(V)$, then $\int_{U} f^* \omega = \int_{V} \omega$ if f is orientation preserving, and $\int_{U} f^* \omega = -\int_{V} \omega$ if f is orientation reversing.

## Statement 87: Theorem 5.6
If f is orientation preserving, then $\int_{V} \phi = \int_{U} \phi \circ f \det \left[ \frac{\partial f_{i}}{\partial x_{j}} \right]$.

## Statement 88: Sard's Theorem
Let U be open in $\mathbb{R}^n$, and let $f: U \to \mathbb{R}^n$ be a $\mathcal{C}^1(U)$ map. The image $f(C_f)$ of the critical set is of measure zero.

## Statement 89: Lemma 5.7
If $x, y \in I_r$ (a subinterval intersecting $C_f$), then $|f(x) - f(y)| < \epsilon \ell/N$.

## Statement 90: Lemma 5.8
For all $0 \le k \le n+1$, there exists $\mu \in \Omega_c^{n-1}(U)$ and $f \in \mathcal{C}_0^{\infty}(U)$ such that $\omega = d\mu + f dx_1 \wedge \dots \wedge dx_n$ and $\int f(x_1, \dots, x_n) dx_k \dots dx_n = 0$.

## Statement 91: Poincare Lemma
Let U be a connected open subset of $\mathbb{R}^n$, and let $\omega \in \Omega_c^n(U)$. The following conditions are equivalent: (1) $\int_U \omega = 0$, (2) $\omega = d\mu$, for some $\mu \in \Omega_c^{n-1}(U)$.

## Statement 92: Definition 5.9
Whenever $\omega \in \Omega^k(U)$ and $\omega = d\mu$ for some $\mu \in \Omega^{k-1}(U)$, we say that $\omega$ is *exact*.

## Statement 93: Definition 5.10
Whenever $\omega \in \Omega^k(U)$ such that $d\omega = 0$, we say that $\omega$ is closed.

## Statement 94: Lemma 5.11
Let U be connected. Given rectangles $R_i$ such that supp $\phi_i\omega \subset \operatorname{Int} R_i$, and given a fixed rectangle $Q_0$ and any point $x \in U$, there exists a finite sequence of rectangles $R_0, \ldots, R_N$ with the properties: $Q_0 = R_0$, $x \in \operatorname{Int} R_N$, and $(\operatorname{Int} R_i) \cap (\operatorname{Int} R_{i+1})$ is non-empty.

## Statement 95: Definition 5.12
Let $f: U \to V$ be a continuous map. The map f is *proper* if for all compact subsets $K \subseteq V$, the set $f^{-1}(K)$ is compact.

## Statement 96: Theorem 5.13
Let U, V be connected open subsets of $\mathbb{R}^n$, and let $f: U \to V$ be a $\mathcal{C}^{\infty}$ proper map. For all $\omega \in \Omega^n_c(V)$, $\int_{U} f^* \omega = (\deg f) \int_{V} \omega$.

## Statement 97: Theorem 5.14
There exists a constant $\gamma_f$ (the degree of f) with the property that for all $\omega \in \Omega_c^n(V)$, $\int_{U} f^* \omega = \gamma_f \int_{V} \omega$.

## Statement 98: Definition 5.15
$\deg(f) = \gamma_f$.

## Statement 99: Theorem 5.16
If f is orientation preserving, then deg(f) = 1; if f is orientation reversing, then deg(f) = -1.

## Statement 100: Lemma 5.17
There exists $\delta > 0$ such that for all $|x| < \delta$, $|g(x)| \le \frac{|x|}{2}$.

## Statement 101: Definition 5.18
A point $q \in V$ is a regular value of f if $q \in V - f(C_f)$.

## Statement 102: Lemma 5.19
If q is a regular value, then $f^{-1}(q)$ is a finite set.

## Statement 103: Theorem 5.20
The degree of f is $\deg(f) = \sum_{i=1}^{N} \sigma_{p_i}$, where $\sigma_{p_i} = +1$ if $Df(p_i)$ is orientation preserving and $-1$ if orientation reversing.

## Statement 104: Theorem 5.21
If $\deg(f) \neq 0$, then $f: U \to V$ is onto.

## Statement 105: Definition 5.22
Let $f_0, f_1 : U \to V$ be $\mathcal{C}^{\infty}$ maps. The maps $f_0$ and $f_1$ are homotopic if there is a $\mathcal{C}^{\infty}$ map $F : U \times [0,1] \to V$ such that $F(p,0) = f_0(p)$ and $F(p,1) = f_1(p)$.

## Statement 106: Definition 5.23
The map F is a proper homotopy if for all compact sets $A \subseteq V$, the pre-image $F^{-1}(A)$ is compact.

## Statement 107: Theorem 5.24
If $f_0$ and $f_1$ are homotopic by a proper homotopy, then $\deg(f_0) = \deg(f_1)$.

## Statement 108: Definition 6.1
Define the *canonical submersion* map $\pi: \mathbb{R}^n \to \mathbb{R}^k$, $(x_1, \dots, x_n) \to (x_1, \dots, x_k)$ and the *canonical immersion* map $\iota: \mathbb{R}^k \to \mathbb{R}^n$, $(x_1, \dots, x_k) \to (x_1, \dots, x_k, 0, \dots, 0)$.

## Statement 109: Canonical Submersion Theorem (Linear)
Let $A : \mathbb{R}^n \to \mathbb{R}^k$ be a linear map, and suppose that A is onto. Then there exists a bijective linear map $B : \mathbb{R}^n \to \mathbb{R}^n$ such that $A \circ B = \pi$.

## Statement 110: Canonical Immersion Theorem (Linear)
Let $A : \mathbb{R}^k \to \mathbb{R}^n$ be a one-to-one linear map. Then there exists a bijective linear map $B : \mathbb{R}^n \to \mathbb{R}^n$ such that $B \circ A = \iota$.

## Statement 111: Definition 6.2
The map f is a submersion at p if $Df(p) : \mathbb{R}^n \to \mathbb{R}^k$ is onto.

## Statement 112: Canonical Submersion Theorem (Nonlinear)
Assume that f is a submersion at p and that f(p) = 0. Then there exists a neighborhood $U_0$ of p in U, a neighborhood V of 0 in $\mathbb{R}^n$, and a diffeomorphism $g: V \to U_0$ such that $f \circ g = \pi$.

## Statement 113: Definition 6.3
Let $f: U \to \mathbb{R}^n$ be a $\mathcal{C}^{\infty}$ map. The map f is an *immersion at* p if $(Df)(p): \mathbb{R}^k \to \mathbb{R}^n$ is injective.

## Statement 114: Canonical Immersion Theorem (Nonlinear)
Let $f: U \to \mathbb{R}^n$ be a $C^{\infty}$ map that is an immersion at 0. Then there exists a neighborhood V of f(0) = p in $\mathbb{R}^n$, a neighborhood W of 0 in $\mathbb{R}^k$, and a diffeomorphism $g: V \to W$ such that $\iota^{-1}(W) \subseteq U$ and $g \circ f = \iota$.

## Statement 115: Definition 6.4
A map $f: X \to Y$ is a diffeomorphism if it is one-to-one, onto, a $\mathcal{C}^{\infty}$ map, and $f^{-1}: Y \to X$ is $\mathcal{C}^{\infty}$.

## Statement 116: Definition 6.5
The set X is an n-dimensional manifold if for every point $p \in X$ there exists a neighborhood V of p in $\mathbb{R}^N$, an open set U in $\mathbb{R}^n$, and a diffeomorphism $f: U \to V \cap X$.

## Statement 117: Definition 6.6
The map $f: X \to Y$ (between subsets of Euclidean spaces) is $\mathcal{C}^{\infty}$ if for every $p \in X$, there exists a neighborhood $U_p$ and a $\mathcal{C}^{\infty}$ extension $g_p: U_p \to \mathbb{R}^m$ such that $g_p = f$ on $U_p \cap X$.

## Statement 118: Definition 6.7
The map $f: X \to Y$ is a diffeomorphism if it is one-to-one, onto, and both f and $f^{-1}$ are $\mathcal{C}^{\infty}$ maps.

## Statement 119: Definition 6.8
A subset X of $\mathbb{R}^N$ is an n-dimensional manifold if for every $p \in X$, there exists a neighborhood V of p in $\mathbb{R}^N$, an open set U in $\mathbb{R}^n$, and a diffeomorphism $\phi: U \to X \cap V$.

## Statement 120: Theorem 6.9
If 0 is a regular value of $f: U \to \mathbb{R}^k$ (where $U$ is open in $\mathbb{R}^N$), then $X = f^{-1}(0)$ is an $n$-dimensional manifold, where $n = N - k$.

## Statement 121: Definition 6.10
The tangent space of a manifold X at p is $T_p X = \operatorname{Im} (d\phi)_q$, where $\phi$ is a parameterization with $\phi(q) = p$.

## Statement 122: Definition 6.11
An alternate definition for the tangent space: $T_p X = \ker df_p$, where f defines X locally as $f^{-1}(0)$.

## Statement 123: Lemma 6.12
Let $g: W \to \mathbb{R}^n$ be $\mathcal{C}^{\infty}$ with $g(W) \subseteq X$ and $g(w) = p$. Then $(dg)_w \subseteq T_pX$.

## Statement 124: Definition 6.13
$df_p = dg_p | T_p X$, where $g: V \to \mathbb{R}^\ell$ extends $f: X \to Y$ to a neighborhood of $p$.

## Statement 125: Definition 6.14
A k-form $\omega$ on X is a function on X which assigns to each point $p \in X$ an element $\omega_p \in \Lambda^k((T_pX)^*)$.

## Statement 126: Definition 6.15
The k-form $\omega$ is $\mathcal{C}^{\infty}$ at p if there exists a k-form $\tilde{\omega} \in \Omega^k(V)$ such that $\iota_X^* \tilde{\omega} = \omega$.

## Statement 127: Definition 6.16
The k-form $\omega$ is $\mathcal{C}^{\infty}$ at p if there exists a diffeomorphism $\phi: U \to V \cap X$ such that $\phi^*\omega \in \Omega^k(U)$.

## Statement 128: Definition 6.17
The k-form $\omega$ is $\mathcal{C}^{\infty}$ if $\omega$ is $\mathcal{C}^{\infty}$ at p for every point $p \in X$. Notation: $\omega \in \Omega^k(X)$.

## Statement 129: Theorem 6.18
If $\omega \in \Omega^k(X)$, then there exists a neighborhood W of X in $\mathbb{R}^N$ and a k-form $\tilde{\omega} \in \Omega^k(W)$ such that $\iota_X^* \tilde{\omega} = \omega$.

## Statement 130: Theorem 6.19
Let $X \subseteq \mathbb{R}^N$ and $Y \subseteq \mathbb{R}^\ell$ be manifolds, and let $f: X \to Y$ be a $C^{\infty}$ map. If $\omega \in \Omega^k(Y)$, then $f^*\omega \in \Omega^k(X)$.

## Statement 131: Definition 6.20
$d\omega = \iota_X^* d\tilde{\omega}$, where $\tilde{\omega}$ extends $\omega$ to a neighborhood.

## Statement 132: Definition 6.21
The support of f is supp $f = \overline{\{x \in X : f(x) \neq 0\}}$.

## Statement 133: Definition 6.22
A collection of functions $\{\rho_i \in \mathcal{C}_0^{\infty}(X)\}$ is a partition of unity if (1) $0 \le \rho_i$, (2) for every compact $A \subseteq X$, there exists N such that supp $\rho_i \cap A = \emptyset$ for all i > N, (3) $\sum \rho_i = 1$.

## Statement 134: Definition 6.23
The partition of unity $\rho_i$ is subordinate to $\mathcal{U}$ if for every i, there exists $\alpha$ such that supp $\rho_i \subseteq U_\alpha$.

## Statement 135: Definition 6.24
An *orientation of* $\mathbb{L}$ (a one-dimensional vector space) is a choice of one of the two components of $\mathbb{L} - \{0\}$.

## Statement 136: Definition 6.25
An orientation of V is an orientation of the one-dimensional vector space $\Lambda^n(V^*)$.

## Statement 137: Definition 6.26
A bijective linear map $A: V_1 \to V_2$ is orientation preserving if $\omega \in \Lambda^n(V_2)_+ \implies A^*\omega \in \Lambda^n(V_1)_+$.

## Statement 138: Definition 6.27
An orientation of X (an n-dimensional manifold) is a function on X which assigns to each point $p \in X$ an orientation of $T_pX$.

## Statement 139: Definition 6.28
An orientation of X is a $\mathcal{C}^{\infty}$ orientation if for every point $p \in X$, there exists a neighborhood U and an n-form $\omega \in \Omega^n(U)$ such that for all $q \in U$, $\omega_q \in \Lambda^n(T_q^*X)_+$.

## Statement 140: Theorem 6.29
If X is oriented, then there exists $\omega \in \Omega^n(X)$ such that for all $p \in X$, $\omega_p \in \Lambda^n(T_p^*X)_+$.

## Statement 141: Definition 6.30
An n-form $\omega \in \Omega^n(X)$ that is nowhere vanishing and positively oriented is called a *volume form*.

## Statement 142: Definition 6.31
A diffeomorphism $f: X_1 \to X_2$ between oriented manifolds is orientation preserving if for every $p \in X_1$, $df_p: T_p X_1 \to T_q X_2$ is orientation preserving.

## Statement 143: Definition 6.32
The parameterization $\phi$ is an *oriented parameterization* if it is orientation preserving.

## Statement 144: Definition 6.33
Let $\omega \in \Omega_c^n(X)$. We define $\int_{X} \omega = \sum_{i=1}^{\infty} \int_{V_{i}} \rho_{i} \omega$, using a partition of unity $\rho_i$ subordinate to an atlas.

## Statement 145: Theorem 6.34
For any $\omega \in \Omega_c^n(X)$ (X oriented connected manifold), the following are equivalent: (1) $\int_{X} \omega = 0$, (2) $\omega \in d\Omega_c^{n-1}(X)$.

## Statement 146: Lemma 6.35 (Connectivity Lemma)
Given $p, q \in X$ (X connected manifold), there exist open sets $W_j$, $j = 0, ..., N+1$, each diffeomorphic to an open set in $\mathbb{R}^n$, such that $p \in W_0$, $q \in W_{N+1}$, and $W_i \cap W_{i+1} \neq \emptyset$.

## Statement 147: Lemma 6.36
The theorem (6.34) is true if V = V' (i.e. the forms are supported in the same chart).

## Statement 148: Theorem 6.37
If $X_1, X_2$ are connected oriented n-dimensional manifolds and $f: X_1 \to X_2$ is a proper $C^{\infty}$ map, then there exists a topological invariant $\deg(f)$ such that $\int_{X_1} f^* \omega = \deg(f) \int_{X_2} \omega$.

## Statement 149: Theorem 6.38 (Change of Variables for Manifolds)
Let $X_1, X_2$ be connected oriented n-dimensional manifolds, and let $f: X_1 \to X_2$ be an orientation preserving diffeomorphism. Then, for all $\omega \in \Omega_c^n(X_2)$, $\int_{X_1} f^* \omega = \int_{X_2} \omega$.

## Statement 150: Theorem 6.39 (Inverse Function Theorem for Manifolds)
If $df_p: T_pX \to T_{p_1}Y$ is bijective, then f maps a neighborhood V of p diffeomorphically onto a neighborhood $V_1$ of $p_1$.

## Statement 151: Lemma 6.40
Suppose that $q \in Y - f(C_f)$. Then $f^{-1}(q)$ is a finite set.

## Statement 152: Theorem 6.41
$\deg(f) = \sum_{i=1}^{N} \sigma_{p_i}$, where $\sigma_{p_i} = +1$ if $df_{p_i}$ is orientation preserving, $-1$ if orientation reversing.

## Statement 153: Theorem 6.42 (Volume Theorem / Sard for Manifolds)
If $q_0 \in Y$ and W is a neighborhood of $q_0$ in Y, then $W - f(C_f)$ is non-empty.

## Statement 154: Definition 6.43
A closed subset $D \subseteq X$ is a *smooth domain* if for every point $p \in \text{Bd}(D)$, there exists a parameterization $\phi: U \to V$ of X at p such that $\phi(U \cap \mathbb{H}^n) = V \cap D$.

## Statement 155: Definition 6.44
The map $\phi$ is a parameterization of D at p.

## Statement 156: Definition 6.45
The map $\phi$ is an oriented parameterization of D if it is an oriented parameterization of X.

## Statement 157: Definition 6.46
For $\omega \in \Omega_c^n(X)$ we define $\int_{D} \omega = \sum_{i} \int_{D} \rho_{i} \omega$.

## Statement 158: Stokes' Theorem
For all $\omega \in \Omega^{n-1}_c(X)$, $\int_{D} d\omega = \int_{\mathrm{Bd}(D)} \omega$.

## Statement 159: Theorem 6.47
If $f: Y \to Z$ extends to a $C^{\infty}$ map $F: D \to Z$ (where Y = Bd(D), D is compact), then $\deg(f) = 0$.

## Statement 160: Corollary 9 (Brouwer Fixed Point Theorem)
The Brouwer fixed point theorem follows from Theorem 6.47.

## Statement 161: Hopf Theorem
Let n be even. Let $f: S^n \to \mathbb{R}^{n+1}$ be a $C^{\infty}$ map. Then, for some $v \in S^n$, $f(v) = \lambda v$ for some scalar $\lambda \in \mathbb{R}$.
