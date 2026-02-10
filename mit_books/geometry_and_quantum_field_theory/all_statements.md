# All Mathematical Statements in "Geometry and Quantum Field Theory"

## Lemma 2.1 (Gaussian integral)
For any $B \in \mathbf{M}(V)$ we have
$$\int_V e^{\frac{i}{2\hbar}B(v,v)+\frac{i}{\hbar}\ell(v)}dv = (2\pi\hbar)^{d/2}\frac{e^{i\pi\sigma/4}}{\sqrt{|\det B|}}e^{-\frac{i}{2\hbar}B^{-1}(\ell,\ell)},$$
where $\sigma$ is the signature of $B$ and $\ell \in V^*$.

## Theorem 2.2
We have $I_g'(\hbar) = I_{\frac{1}{2}\Delta_B g}(\hbar), \ \hbar \ge 0$. Thus $I_g \in C^{\infty}[0,\infty)$. In particular, if $g$ vanishes at the origin to order $2n+1$ then $I_g(0)=\ldots=I_g^{(n)}(0)=0$.

## Lemma 2.3
$I_g$ is a continuous function.

## Lemma 2.4
If $\ell \in V^*$ and $f \in \mathcal{S}(V)$ then
$$I_{\ell \cdot f}(\hbar) = i\hbar I_{\partial_{B^{-1}\ell}f}(\hbar).$$

## Theorem 2.6 (Steepest descent formula)
Assume that $f$ attains a global minimum at a unique point $c \in [a, b]$, such that $a < c < b$ and $f''(c) > 0$. Then one has
$$\int_a^b g(x) e^{-f(x)/\hbar} dx \sim e^{-f(c)/\hbar} \sum_{n=0}^{\infty} A_n \hbar^{n+\frac{1}{2}},$$
where $A_n$ are some constants depending on $f$ and $g$ and $A_0 = g(c)\sqrt{\frac{2\pi}{f''(c)}}$.

## Theorem 2.8 (Stationary phase formula)
Let $f, g : [a,b] \to \mathbb{R}$ be smooth functions. Assume that $f$ has a unique critical point $c \in [a,b]$, such that $a < c < b$ and $f''(c) \neq 0$, and $g$ has vanishing derivatives of all orders at $a$ and $b$. Then
$$\int_a^b g(x) e^{if(x)/\hbar} dx \sim e^{if(c)/\hbar} \sum_{n=0}^{\infty} A_n \hbar^{n+\frac{1}{2}},$$
where $A_0 = g(c)\sqrt{\frac{2\pi}{|f''(c)|}} e^{i\pi\mathrm{sgn}(f''(c))/4}$ and $A_n$ are some constants depending on $f$ and $g$.

## Lemma 2.10 (Riemann lemma)
(i) Let $f : [a,b] \to \mathbb{R}$ be a smooth function such that $f'(x) > 0$ for all $x \in [a,b]$ and $g : [a,b] \to \mathbb{R}$ a $C^n$-function such that $g^{(k)}(a) = g^{(k)}(b) = 0$ for $0 \le k \le n-1$. Then
$$\int_a^b g(x) e^{if(x)/\hbar} dx = O(\hbar^n), \ \hbar \to 0.$$
(ii) If g is smooth and has vanishing derivatives of all orders at a and b then this integral is $O(\hbar^{\infty})$.

## Theorem 2.16 (Multidimensional steepest descent formula)
Let $f, g: D \to \mathbb{R}$ be continuous functions which are smooth in the interior of $D$. Assume that $f$ achieves global minimum on $D$ at a unique point $c$, such that $c$ is an interior point and $f''(c) > 0$. Then
$$\int_D g(x) e^{-f(x)/\hbar} dx \sim e^{-f(c)/\hbar} \sum_{n=0}^{\infty} A_n \hbar^{n+\frac{d}{2}}.$$

## Theorem 2.17 (Multidimensional stationary phase formula)
Let $f, g: D \to \mathbb{R}$ be smooth functions. Assume that $f$ has a unique critical point $c$ in $D$, such that $c$ is an interior point and $\det f''(c) \neq 0$, and $g$ has vanishing derivatives of all orders on $\partial D$. Then
$$\int_D g(x) e^{if(x)/\hbar} dx \sim e^{if(c)/\hbar} \sum_{n=0}^{\infty} A_n \hbar^{n+\frac{d}{2}}.$$

## Theorem 2.18 (Separation of variables)
Let $f$ be a smooth function on an open ball $0 \in B \subset \mathbb{R}^d$ which has a non-degenerate critical point at 0, and suppose $f(0) = 0$. Then there is a local coordinate system near 0 in which $f = \frac{1}{2}(x_1^2 + ... + x_k^2 - x_{k+1}^2 - ... - x_d^2) + O_3(x_1,...,x_k)$, where $O_3$ denotes cubic terms.

## Corollary 2.19 (Morse lemma)
Let $f$ be a smooth function on an open ball $0 \in B \subset \mathbb{R}^d$ which has a non-degenerate critical point at 0, and suppose $f(0) = 0$. Then there is a local coordinate system $(x_1, ..., x_d)$ near 0 in which $f = \frac{1}{2}(x_1^2 + ... + x_k^2 - x_{k+1}^2 - ... - x_d^2)$.

## Lemma 2.21
Let $f, g: D \to \mathbb{R}$ be smooth functions such that all derivatives of $g$ vanish on $\partial D$ and $df$ does not vanish anywhere on the support of $g$. Then the function
$$I(\hbar) = \int_D g(x) e^{\frac{i}{\hbar}f(x)} dx$$
is $O(\hbar^{\infty})$ as $\hbar \to 0^+$.

## Theorem 3.1 (Wick's theorem)
Let $B^{-1}$ denote the inverse form to $B$ on $V^*$, and $\ell_1, \ldots, \ell_N \in V^*$. Then, if $N$ is even, we have
$$\frac{\int_V \ell_1(v) \ldots \ell_N(v) e^{-\frac{1}{2}B(v,v)} dv}{\int_V e^{-\frac{1}{2}B(v,v)} dv} = \sum_{\sigma \in \Pi_N} \prod_{i < \sigma(i)} B^{-1}(\ell_i, \ell_{\sigma(i)}),$$
where $\Pi_N$ denotes the set of perfect matchings. If $N$ is odd, the integral is zero.

## Theorem 3.11
Let $Z_0 = \frac{(2\pi)^{\frac{d}{2}}}{\sqrt{\det B}}$. Then one has
$$\log \frac{Z}{Z_0} = \sum_{\mathbf{n}} \prod_{i} (g_i \hbar^{\frac{i}{2}-1})^{n_i} \sum_{\Gamma \in G_c(\mathbf{n})} \frac{\mathbb{F}_{\Gamma}}{|\operatorname{Aut}(\Gamma)|}$$
where $G_c(\mathbf{n})$ is the set of connected graphs in $G(\mathbf{n})$.

## Corollary 3.14 (A. Cayley)
The number of labeled trees with $n$ vertices is $n^{n-2}$.

## Theorem 3.20
The effective action $S_{\text{eff}}$ is given by the formula
$$S_{\text{eff}}(x) = \frac{B(x, x)}{2} - \sum_{i>0} \frac{\mathcal{B}_i(x, ..., x)}{i!},$$
where
$$\mathcal{B}_N(x,\ldots,x) = \hbar \sum_{\mathbf{n}} \prod_i (g_i \hbar^{\frac{i}{2}-1})^{n_i} \sum_{\Gamma \in G_{\mathrm{1PI}}(\mathbf{n},N)} \frac{\mathbb{F}_{\Gamma}(Bx,\ldots,Bx)}{|\mathrm{Aut}(\Gamma)|}.$$

## Lemma 3.21
Any connected graph $\Gamma$ can be uniquely represented as a tree whose vertices are 1-particle irreducible subgraphs (with external edges), and edges are the bridges of $\Gamma$.

## Theorem 4.4
(1) There exists a limit $W_{\infty} := \lim_{N \to \infty} \frac{\log \widehat{Z}_N}{N^2}$. This limit is given by the formula
$$W_\infty = -\frac{1}{2}(\log \frac{z}{2\pi} + 1) + \frac{1}{z}\sum_{k \ge 1}\frac{1}{2k}\sum_{j \ge 0}g_j\frac{C_k(j)}{z^{k-1}}$$
where $C_k(j) = \frac{1}{k}\binom{2k}{k-j}$ are the ballot numbers.

## Theorem 4.8
(1) There exists a limit $W_{\infty} := \lim_{N \to \infty} \frac{\log \widehat{Z}_N}{N^2}$. This limit is given by the formula involving the spectral density.

## Theorem 4.10 (Harer-Zagier, 1986)
$$e_{g}(\Sigma_g) = \sum_{g \ge 0} e_g t^{2g} = \sum_{g \ge 0} \frac{(-1)^g B_{2g}}{2g \cdot (2g-2)!} t^{2g} = \frac{t/2}{\sin(t/2)},$$
where the second equation can be reformulated as $e_g = \zeta(1-2g)/(2-2g)$ for $g > 0$, and $e_0 = 1$.

## Theorem 4.12 (Wigner's semicircle law)
Let $f$ be a continuous function on $\mathbb{R}$ of at most polynomial growth at infinity. Then
$$\lim_{N\to\infty}\frac{1}{N}E\left(\sum_{i=1}^{N}f(\lambda_i/\sqrt{N})\right) = \frac{1}{2\pi}\int_{-2}^{2}f(x)\sqrt{4-x^2}dx.$$

## Theorem 4.13 (Properties of Hermite polynomials)
(i) The exponential generating function of $H_n(x)$ is $f(x,t) = \sum_{n>0} H_n(x) \frac{t^n}{n!} = e^{2xt-t^2}$.
(ii) $H_n(x)$ satisfy the differential equation $f'' - 2xf' + 2nf = 0$.
(iii) $H_n(x)$ are orthogonal: $\frac{1}{\sqrt{\pi}} \int_{-\infty}^{\infty} e^{-x^2} H_m(x) H_n(x) dx = 2^n n! \delta_{mn}$. Moreover, the functions $H_n(x)e^{-\frac{x^2}{2}}$ form an orthogonal basis of $L^2(\mathbb{R})$.
(iv) $\frac{1}{\sqrt{\pi}} \int_{-\infty}^{\infty} e^{-x^2} x^{2m} H_{2k}(x) dx = \frac{(2m)!}{(m-k)!} 2^{2(k-m)}$.
(v) $\frac{H_r^2(x)}{2^r r!} = \sum_{k=0}^r \frac{r!}{2^k k!^2 (r-k)!} H_{2k}(x)$.

## Theorem 5.8 (Mumford)
(a) The action of $\Gamma_g^1$ on $A \setminus A_{\infty}$ is properly discontinuous.

## Lemma 5.12
Let $(\alpha_1, ..., \alpha_n)$ be a system of curves, satisfying the axioms of a filling arc system, except maybe conditions (A) and (B). Then one can refine $(\alpha_1, ..., \alpha_n)$ by adding finitely many curves to obtain a filling arc system satisfying all conditions.

## Lemma 5.15
Let $\varepsilon(n)$, $\mu(n)$, $\lambda(n)$, $n \geq 0$, be sequences satisfying the equations described in the theorem, relating them via recurrences involving the Euler characteristic of moduli spaces of curves.

## Theorem 6.2 (Brezin, Itzykson, Parisi, Zuber, 1978)
One has the matrix integral representation
$$W_\infty = \lim_{N\to\infty}\frac{1}{N^2}\log\frac{\int e^{-\frac{N}{2g}\mathrm{Tr}(A^2)}e^{-\frac{N}{g}\sum_j g_j\mathrm{Tr}(A^j)/j}dA}{\int e^{-\frac{N}{2g}\mathrm{Tr}(A^2)}dA}.$$

## Proposition 6.3 (Steepest descent principle for matrix integrals)
$E(g)$ equals the leading coefficient of the asymptotics as $N \to \infty$ of the maximal value of the logarithm of the integrand.

## Proposition 6.4
The normalized counting measures $\frac{1}{N}\sum_{i}\delta(x-\lambda_{i})$ converge weakly to a measure $\mu(x)=f(x,g)dx$, where $f(x,g)$ is a continuous function supported on a finite interval $[-2a,2a]$ and differentiable on the interior of this interval.

## Proposition 7.8 (Wick's theorem for quantum mechanics)
One has $G_n(t_1,...,t_n) = 0$ if $n$ is odd, and
$$G_n(t_1,...,t_n) = \sum_{\sigma \in \Pi_n} \prod_{(i,j) \in \sigma} G_2(t_i, t_j)$$
if $n$ is even.

## Proposition 7.14
One has $\mathcal{G}_n^M(t_1,...,t_n) = \mathcal{G}_n^E(t_1,...,t_n)|_{t_j \to it_j}$, relating Minkowskian and Euclidean correlation functions via Wick rotation.

## Proposition 7.20
The function $W(J) = \log(Z(J)/Z(0))$ is the Legendre transform of $S_{\text{eff}}(q)$, i.e. it equals $-S_{\text{eff}}(\widetilde{q}_J) + (J, \widetilde{q}_J)$, where $\widetilde{q}_J$ is the extremal of $-S_{\text{eff}}(q) + (J, q)$ decaying at infinity.

## Proposition 7.23
The Fourier transform of the function $F_{\Gamma}(\delta_{t_1},...,\delta_{t_n})$ is $\widehat{F}_{\Gamma}(E_1,...,E_n)$. Hence, the Fourier transform of the connected Green's function is the sum of Feynman amplitudes of connected diagrams in momentum space.

## Proposition 8.3
The equations of motion are equivalent to the Hamilton equations $\dot{q}_i = \frac{\partial H}{\partial p_i}, \dot{p}_i = -\frac{\partial H}{\partial q_i}$.

## Theorem 8.4 (von Neumann spectral theorem)
Let $A$ be a bounded self-adjoint operator. There exists a measure space $(X, \mu)$, an essentially bounded measurable function $h: X \to \mathbb{R}$, and an isometry $\mathcal{H} \to L^2(X, \mu)$ under which $A$ maps to the operator of multiplication by $h$. Moreover, the spectrum $\sigma(A)$ is the set of $\lambda \in \mathbb{R}$ for which $h^{-1}(\lambda - \varepsilon, \lambda + \varepsilon)$ has positive measure for each $\varepsilon > 0$.

## Theorem 8.5 (Spectral theorem for unbounded self-adjoint operators)
Theorem 8.4 except for the statement that $h$ is essentially bounded holds for not necessarily bounded self-adjoint operators. Moreover, the domain $V$ of $A$ in its spectral theorem realization is the space of $g \in L^2(X, \mu)$ such that $hg \in L^2(X, \mu)$.

## Corollary 8.6
Let $(A, V)$ be a self-adjoint operator. Then there exists a unique 1-parameter group of unitary operators $U(t) = e^{iAt} : \mathcal{H} \to \mathcal{H}$ strongly continuous in $t$ which preserve $V$ and commute with $A$, such that for all $v \in V$ the function $t \mapsto U(t)v$ is differentiable and $\frac{d}{dt}U(t)v = iAU(t)v$.

## Lemma 8.19
There is a unique eigenvector $\Omega$ of $\widehat{H}$ with smallest eigenvalue given by a positive function with norm 1.

## Theorem 8.22 (Feynman-Kac formula)
If $t_1 \geq ... \geq t_n$ then the function $\mathcal{G}_n^{\text{Ham}}$ admits an asymptotic expansion in $\hbar$ (near $\hbar = 0$), which coincides with the path integral correlation function $\mathcal{G}_n^M$ constructed above. Equivalently, the Wick rotated function $\mathcal{G}_n^{\text{Ham}}(-it_1,...,-it_n)$ equals $\mathcal{G}_n^E(t_1,...,t_n)$.

## Theorem 8.23 (Feynman-Kac formula on the circle)
The functions $Z_L^{\text{Ham}}$, $\mathcal{G}_{n,L}^{\text{Ham}}$ admit asymptotic expansions in $\hbar$, which coincide with the functions $Z_L$ and $\mathcal{G}_{n,L}$ computed from path integrals.

## Theorem 8.30 (WKB formal solutions)
There is a unique, up to scaling, basis of formal solutions of equation $\hbar\frac{dF}{dx} = AF$ of the form $F_{\pm}(x, \hbar) = e^{\pm \frac{1}{\hbar}\int_0^x p(y)dy}(1 + \sum_{k \ge 1} \psi_k^{\pm}(x)\hbar^k)$, where $p(x) = \sqrt{U(x) - E}$ for $U(x) > E$.

## Theorem 8.31 (Local WKB approximation)
Equation $-\hbar^2 \psi'' + (U(x) - E)\psi = 0$ has a basis of formal solutions of the form $\psi_{\pm}(x, \hbar) = p(x)^{-1/2}e^{\pm\frac{i}{\hbar}\int_0^x p(y)dy}(1 + \sum_{k \ge 1} \phi_k^{\pm}(x)\hbar^k)$, where $p(x) = \sqrt{E - U(x)}$ for $U(x) < E$.

## Proposition 8.32 (Weyl law)
$\nu(E) \sim \frac{A(E)}{\hbar}, \ \hbar \to 0$, where $A(E) := \frac{1}{\pi} \int_{0}^{2\pi} \sqrt{2(E - U(x))} dx$.

## Proposition 9.2 (Classification of supermanifolds)
(i) $S_* \circ S = \mathrm{Id}$; (ii) $S \circ S_* = \text{Id}$ on isomorphism classes of objects.

## Proposition 9.5 (Properties of Berezinian)
(i) For any $A, B \in \operatorname{Mat}_{n|m}(R)$ with $A_{11}, B_{11}$ invertible, we have $\operatorname{Ber}(AB) = \operatorname{Ber}(A)\operatorname{Ber}(B)$.
(ii) $\frac{d}{dt}|_{t=0} \operatorname{Ber}(1+tC) = \operatorname{sTr}(C)$.
(iii) $\operatorname{Ber}(e^C) = e^{\operatorname{sTr}(C)}$.

## Theorem 9.7 (Berezin's change of variable formula)
Let $g$ be a smooth function with compact support on $U'$, and $F: U \to U'$ be an isomorphism. Let $dv, dv'$ be supervolume elements on $U, U'$. Then
$$\int_{U'} g(dv')^{-1} = \int_{U} (g \circ F)\operatorname{Ber}(dF)(dv)^{-1}.$$

## Proposition 9.9
$\int_{V} e^{\frac{1}{2}B(\xi,\xi)} (d\xi)^{-1} = Pf(B)$, where the integral is over an odd vector space $V$ of dimension $2m$ with volume element $d\xi$ and $B$ is a symmetric bilinear form on $V$.

## Proposition 9.10
$\int_{V} e^{S} (dv)^{-1} = (-1)^{\frac{n(n-1)}{2}} \det A$, where $S(y, y^*) = (Ay, y^*)$ for a linear operator $A: Y \to Y$ and $V = Y \oplus Y^*$ is an odd space.

## Theorem 9.11 (Wick formula in the odd case)
$$\int_{V} \lambda_{1}(\xi) ... \lambda_{n}(\xi) e^{-\frac{1}{2}B(\xi,\xi)} (d\xi)^{-1} = \text{Pf}(-B) \text{Pf}(B^{-1}(\lambda_{i},\lambda_{j})).$$

## Theorem 10.6 (Feynman-Kac formula for free fermionic theory)
(i) For the free theory on the line we have $\langle \psi(t_1)...\psi(t_n)\rangle = \langle \Omega, \psi(t_1)...\psi(t_n)\Omega \rangle$.
(ii) For the free theory on the circle of length $L$ we have $\langle \psi(t_1)...\psi(t_n)\rangle = \frac{\operatorname{sTr}(\psi(t_1)...\psi(t_n)e^{-L\widehat{H}})}{\operatorname{sTr}(e^{-L\widehat{H}})}$.

## Lemma 11.6
Suppose $\dim V \geq 2$. Then $\pi$ is positive energy if and only if $\sigma(\pi)$ is contained in the positive part of the solid light cone, $\overline{V}_+$.

## Theorem 11.8 (The spin-statistics theorem)
If $E \subset R_j^*$ is a subrepresentation then $\zeta|_E = (-1)^j$.

## Proposition 11.10
In a Wightman QFT on a Minkowski space $V$, for every $n \geq 1$ there exists a unique tempered distribution $W_n$ on $V^n$ valued in $R^{*\otimes n}$ such that $W_n(f_1 \boxtimes ... \boxtimes f_n) = \langle \Omega, \phi(f_1)...\phi(f_n)\Omega \rangle$.

## Proposition 11.12
The Wightman functions $W_n$ of a Wightman QFT satisfy: (1) $\widetilde{\mathbf{P}}$-invariance, (2) positive energy: Fourier transform supported appropriately, (3) $W_n(f^*) = \overline{W_n(f)}$, (4) space locality, (5) positivity: $W(f^* \otimes f) \geq 0$.

## Theorem 11.13 (Wightman reconstruction theorem)
If a collection of distributions $W_n$ satisfies conditions (1)-(5) of Proposition 11.12 then they define a Wightman QFT.

## Proposition 11.17 (Operator product expansion)
Let $A, B$ be two composite operators in the theory of scalar boson. Then there exist a unique collection of functions $F_j(y)$ and composite operators $C_j(y)$ such that we have an asymptotic expansion $A(x)B(y) \sim \sum_{j} F_{j}(x-y)C_{j}(y), \ x \to y$, such that for every $N$ we have $|F_j(z)| = O(|z|^N)$, $z \to 0$, for all but finitely many $j$.

## Lemma 12.1 (Feynman's famous formula)
Let $\Delta_n$ be the $n-1$-dimensional simplex defined in $\mathbb{R}^n$ by the equation $y_1 + ... + y_n = 1$, and $dy$ be the Lebesgue measure on $\Delta_n$ of volume 1. Then for positive numbers $a_1, ..., a_n$ we have
$$\int_{\Delta_n} \frac{dy}{(a_1 y_1 + \dots + a_n y_n)^n} = \frac{1}{a_1 \dots a_n}.$$

## Proposition 12.6
(i) If a Lagrangian is super-renormalizable then the degree of superficial divergence of the corresponding Feynman diagrams is bounded above, and there are finitely many superficially divergent diagrams with any given number of external edges; moreover, if $d > 2$ then there are finitely many superficially divergent diagrams altogether.
(ii) If a Lagrangian is renormalizable, then there are infinitely many superficially divergent diagrams with a fixed number of external edges, but the degree of superficial divergence is still bounded above.
(iii) If a Lagrangian is non-renormalizable, then the degree of superficial divergence of diagrams with a fixed number of external edges is unbounded above.

## Proposition 12.7
For the scalar bosonic field $\phi$, the most general (super-)renormalizable non-quadratic Poincare-invariant Lagrangian is (up to scaling): $d > 6$: none; $d = 5, 6$: $\mathcal{L} = \frac{1}{2}(d\phi)^2 + P_3(\phi)$; $d = 4$: $\mathcal{L} = \frac{1}{2}(d\phi)^2 + P_4(\phi)$; $d = 3$: $\mathcal{L} = \frac{1}{2}(d\phi)^2 + P_6(\phi)$; $d = 2$: $\mathcal{L} = \frac{1}{2}g(\phi)(d\phi)^2 + U(\phi)$.

## Proposition 13.2 (Wick's formula for conformal field theory)
We have $\langle \Omega, a(z_1)...a(z_{2k})\Omega \rangle = \sum_{\sigma \in \Pi_{2k}} \frac{1}{\prod_{j \in [1,2k]/\sigma} (z_j - z_{\sigma(j)})^2}$, and the $2k + 1$-point correlation functions are zero.

## Theorem 13.6 (Virasoro action on Fock space)
The formulas $L_0 = \sum_{k>1} a_{-k} a_k$, $L_n = \frac{1}{2} \sum_{k \in \mathbb{Z}} a_{-k} a_{k+n}$ for $n \neq 0$, define an action of $\operatorname{Vir}$ on $\mathcal{F}$ with $C$ acting by 1.

## Theorem 13.9 (Operator product expansion in CFT)
For any local operators $P, Q \in \mathcal{V}$, there exist a unique finite sequence of local operators $R_1, ..., R_N \in \mathcal{V}$ such that $P(a)(z)Q(a)(w) = \sum_{j=1}^{N} R_j(a)(w)(z-w)^{-j} + \text{regular terms}$.
