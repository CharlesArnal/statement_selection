# All Mathematical Statements: Topics in Fourier Analysis

## Statement 1
**Theorem 1.1.** If $\varphi \in L^p(\lambda_{[0,1]}; \mathbb{C})$ for some $p \in [1,\infty)$, then

$$\lim_{r \nearrow 1} \left\| \varphi - \sum_{m \in \mathbb{Z}} r^{|m|} (\varphi, \mathfrak{e}_m)_{L^2(\lambda_{[0,1)}; \mathbb{C})} \mathfrak{e}_m \right\|_{L^p(\lambda_{[0,1]}; \mathbb{C})} = 0,$$

and, if $\varphi \in C([0,1];\mathbb{C})$ satisfies $\varphi(0) = \varphi(1)$, then

$$\lim_{r \nearrow 1} \left\| \varphi - \sum_{m \in \mathbb{Z}} r^{|m|} (\varphi, \mathfrak{e}_m)_{L^2(\lambda_{[0,1)}; \mathbb{C})} \mathfrak{e}_m \right\|_{\mathfrak{U}} = 0.$$

## Statement 2
**Theorem 1.2.** $\{\mathfrak{e}_m : m \in \mathbb{Z}\}$ is an orthonormal basis in $L^2(\lambda_{[0,1)}; \mathbb{C})$, and so, for each $\varphi \in L^2(\lambda_{[0,1)}; \mathbb{C})$,

$$\sum_{m \in \mathbb{Z}} (\varphi, \mathfrak{e}_m)_{L^2(\lambda_{[0,1)}; \mathbb{C})} \mathfrak{e}_m \equiv \lim_{n \to \infty} \sum_{|m| < n} (\varphi, \mathfrak{e}_m)_{L^2(\lambda_{[0,1)}; \mathbb{C})} = \varphi,$$

where the convergence is in $L^2(\lambda_{[0,1)};\mathbb{C})$. In addition, for all $\varphi, \psi \in L^2(\lambda_{[0,1)};\mathbb{C})$,

$$(\varphi,\psi)_{L^2(\lambda_{[0,1)};\mathbb{C})} = \sum_{m \in \mathbb{Z}} (\varphi,\mathfrak{e}_m)_{L^2(\lambda_{[0,1)};\mathbb{C})} \overline{(\psi,\mathfrak{e}_m)}_{L^2(\lambda_{[0,1)};\mathbb{C})}.$$

## Statement 3
**Corollary 1.3.** If $\varphi \in C([0,1];\mathbb{C})$ and

$$\sum_{m\neq 0} \left| (\varphi, \mathfrak{e}_m)_{L^2(\lambda_{[0,1)};\mathbb{C})} \right| < \infty,$$

then the series

$$\sum_{m\in\mathbb{Z}} (\varphi, \mathfrak{e}_m)_{L^2(\lambda_{[0,1)};\mathbb{C})} \mathfrak{e}_m(x)$$

is uniformly absolutely convergent to $\varphi$. In fact,

$$||S_n(\varphi) - \varphi||_{\mathbf{u}} \le \sum_{|m| > n} |(\varphi, \mathfrak{e}_m)_{L^2(\lambda_{[0,1)};\mathbb{C})}|.$$

## Statement 4
**Lemma 1.4.** Let $\ell \geq 1$ and assume that $\varphi \in C^{\ell}([0,1];\mathbb{C})$ satisfies $\varphi^{(k)}(0) = \varphi^{(k)}(1)$ for $0 \leq k \leq \ell - 1$. Then

$$(\varphi, \mathfrak{e}_m)_{L^2(\lambda_{[0,1)};\mathbb{C})} = \left(\frac{\imath}{2\pi m}\right)^{\ell} \left(\varphi^{(\ell)}, \mathfrak{e}_m\right)_{L^2(\lambda_{[0,1)};\mathbb{C})} \text{ for } m \neq 0.$$

## Statement 5
**Theorem 3.1.** Define $\{b_{\ell} : \ell \geq 0\} \subseteq \mathbb{R}$ inductively by

$$b_0 = 1$$
and $b_{\ell+1} = \sum_{k=0}^{\ell} \frac{(-1)^k b_{\ell-k}}{(k+2)!}$,

and set

$$B_{\ell}(x) = \sum_{k=0}^{\ell} \frac{(-1)^k b_{\ell-k}}{k!} x^k \text{ for } \ell \ge 0.$$

Then $\{B_{\ell}: \ell \geq 0\}$ are the one and only functions satisfying

$$B_0 = 1$$, $B'_{\ell+1} = -B_{\ell}$ for $\ell \ge 0$, and $B_{\ell}(1) = B_{\ell}(0)$ for $\ell \ge 2$.

## Statement 6
**Theorem 3.2.** For $\ell \geq 2$ and $x \in [0, 1]$,

$$B_{\ell}(x) = \frac{-i^{\ell}}{(2\pi)^{\ell}} \sum_{n \neq 0} \frac{\mathfrak{e}_n(x)}{n^{\ell}}.$$

In particular, $b_{2\ell+1} = 0$ and

$$\zeta(2\ell) \equiv \sum_{m=1}^{\infty} \frac{1}{m^{2\ell}} = (-1)^{\ell+1} 2^{2\ell-1} \pi^{2\ell} b_{2\ell}$$

for $\ell \geq 1$.

## Statement 7
**Theorem 3.3.** If $\ell \geq 1$ and $\varphi \in C^{\ell}([0,1];\mathbb{C})$, then

$$\int_{0}^{1} \varphi(x) - \frac{1}{n} \sum_{m=1}^{n} \varphi\left(\frac{m}{n}\right)$$

$$= -\sum_{k=1}^{\ell} \frac{b_{k}}{n^{k}} \left(\varphi^{(k-1)}(1) - \varphi^{(k-1)}(0)\right) + \frac{1}{n^{\ell}} \int_{0}^{1} \tilde{B}_{\ell}(nx) \varphi^{(\ell)}(x) dx.$$

## Statement 8
**Theorem 5.1.** Let $\varphi: [-\frac{1}{2}, \frac{1}{2}] \longrightarrow \mathbb{C}$ be a measurable function, let $x \in [-\frac{1}{2}, \frac{1}{2}]$, and assume that there is a $C \in (0, \infty)$ and $\alpha \in (0, 1]$ such that $|\tilde{\varphi}(x+y) - \varphi(x)| \leq C|y|^{\alpha}$ for $y \in [-\frac{1}{2}, \frac{1}{2}]$. For $n \geq 5$

$$|F_n * \varphi(x) - \varphi(x)| \le C \begin{cases} \frac{2}{(1+\alpha)n^{\alpha}} + \frac{4(n^{1-\alpha}-4^{1-\alpha})}{\pi^2(1-\alpha)n} + \frac{1-2^{-(1+\alpha)}}{2^{\alpha}(1+\alpha)n} & \text{if } \alpha \in (0,1) \\ \frac{19}{16n} + \frac{4\log\frac{n}{4}}{\pi^2n(1-\alpha)} & \text{if } \alpha = 1. \end{cases}$$

Hence

$$\overline{\lim}_{n \to \infty} n^{\alpha} |F_n * \varphi(x) - \varphi(x)| \le \frac{2}{1+\alpha} + \frac{4}{\pi^2 (1-\alpha)} \quad \text{if } \alpha \in (0,1)$$

and

$$\overline{\lim}_{n \to \infty} \frac{n}{\log n} |F_n * \varphi(x) - \varphi(x)| \le \frac{4}{\pi^2} \quad \text{if } \alpha = 1.$$

## Statement 9
**Theorem 5.2.** If $\varphi \in L^1(\lambda_{[-\frac{1}{2},\frac{1}{2}]};\mathbb{C})$, then

$$\lim_{n\to\infty} F_n * \varphi(x) = \varphi(x) \text{ for } \lambda_{\left[-\frac{1}{2},\frac{1}{2}\right]} \text{-almost every } x \in [0,1].$$

## Statement 10
**Lemma 7.1.** If $f \in C^1(\mathbb{R}, \mathbb{C}) \cap L^1(\lambda_{\mathbb{R}}; \mathbb{C})$ and $f' \in L^1(\lambda_{\mathbb{R}}; \mathbb{C})$, then

$$\widehat{f'}(\xi) = -i\xi \widehat{f}(\xi).$$

## Statement 11
**Theorem 7.2.** (Poisson Sum) Let $f \in L^1(\lambda_{\mathbb{R}}; \mathbb{C}) \cap C(\mathbb{R}; \mathbb{C})$, and assume that

$$\sum_{n\in\mathbb{Z}} \left( \sup_{x\in[0,1]} |f(x+n)| + |\hat{f}(2\pi n)| \right) < \infty.$$

Then

$$\sum_{n \in \mathbb{Z}} f(n) = \sum_{n \in \mathbb{Z}} \hat{f}(2\pi n).$$

## Statement 12
**Theorem 10.1.** $||H_m||_{L^2(\gamma;\mathbb{C})} = (m!)^{\frac{1}{2}}$ and $\{H_m : m \geq 0\}$ is an orthogonal basis in $L^2(\gamma;\mathbb{C})$. Equivalently, if $\tilde{H}_m = \frac{H_m}{\sqrt{m!}}$, then $\{\tilde{H}_m : m \geq 0\}$ is an orthonormal basis in $L^2(\gamma;\mathbb{C})$.

## Statement 13
**Theorem 11.1.** For all $m \ge 0$, $\widehat{h_m} = (2\pi)^{\frac{1}{2}} i^m h_m$.

## Statement 14
**Corollary 11.2.** For all $m \geq 0$,

$$\|\tilde{h}_m\|_{L^1(\lambda_{\mathbb{R}};\mathbb{C})} \leq (2\pi)^{\frac{1}{2}} (m+1)^{\frac{1}{2}}, \|\tilde{h}_m\|_{\mathbf{u}} \leq (m+1)^{\frac{1}{2}} \text{ and } \|\tilde{h}_m\|_{\mathbf{u}} \leq 2m + \frac{3}{2}.$$

## Statement 15
**Theorem 11.3.** If $f \in L^1(\lambda_{\mathbb{R}}; \mathbb{C}) \cup L^2(\lambda_{\mathbb{R}}; \mathbb{C})$, then

$$\int q(t, x, y) f(y) \, dy = e^{-\frac{1}{2}} \sum_{m=0}^{\infty} e^{-mt} (f, \tilde{h}_m)_{L^2(\lambda_{\mathbb{R}}; \mathbb{C})} \tilde{h}_m \text{ for } t > 0,$$

where the convergence of the series is absolute uniformly for $x \in \mathbb{R}$.

## Statement 16
**Lemma 12.1.** If $f \in L^1(\mathbb{R}; \mathbb{C})$, then

$$\frac{e^{-\frac{\xi^2 \tanh t}{2}}}{(2\pi \cosh t)^{\frac{1}{2}}} \int e^{\frac{i\xi x}{\cosh t}} e^{-\frac{x^2 \tanh t}{2}} f(x) dx$$
$$= e^{-\frac{t}{2}} \sum_{m=0}^{\infty} (ie^{-t})^m (f, \tilde{h}_m)_{L^2(\lambda_{\mathbb{R}}; \mathbb{C})} \tilde{h}_m(\xi)$$

for $(t,\xi) \in (0,\infty) \times \mathbb{R}$.

## Statement 17
**Theorem 12.2.** If $f \in L^1(\mathbb{R}; \mathbb{C}) \cap L^2(\mathbb{R}; \mathbb{C})$, then

$$\hat{f} = (2\pi)^{\frac{1}{2}} \sum_{m=0}^{\infty} i^m (f, \tilde{h}_m)_{L^2(\lambda_{\mathbb{R}}; \mathbb{C})} \tilde{h}_m$$

almost everywhere.

## Statement 18
**Lemma 13.1.** For each $m \geq 0$,

$$||x\varphi||_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})} \vee ||\partial\varphi||_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})} \leq 3^m ||\varphi||_{\mathscr{S}^{(m+1)}(\mathbb{R};\mathbb{C})}.$$

## Statement 19
**Theorem 13.2.** For each $m \in \mathbb{N}$, $\mathscr{S}(\mathbb{R}; \mathbb{C})$ is a dense subset of $\mathscr{S}^{(m)}(\mathbb{R}; \mathbb{C})$. In addition, for each $m \geq 0$, there exists a $K_m \in (0, \infty)$ such that

$$\|\varphi\|_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})} \le K_m \|\varphi\|_{\mathbf{u}}^{(m+1)}$$

and

$$\|\varphi\|_{\mathbf{u}}^{(m)} \le K_m \|\varphi\|_{\mathscr{S}^{(m+3)}(\mathbb{R};\mathbb{C})}.$$

for all $\varphi \in \mathscr{S}(\mathbb{R};\mathbb{C})$. Thus $\varphi_n \longrightarrow \varphi$ in $\mathscr{S}(\mathbb{R};\mathbb{C})$ if and only if

$$\lim_{n \to \infty} \|\varphi_n - \varphi\|_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})} = 0$$

for all $m \in \mathbb{N}$. In particular, for each $\varphi \in \mathscr{S}(\mathbb{R}; \mathbb{C})$,

$$\sum_{k=0}^{n} (\varphi, \tilde{h}_{k})_{L^{2}(\lambda_{\mathbb{R}}; \mathbb{C})} \tilde{h}_{k} \longrightarrow \varphi \ in \ \mathscr{S}(\mathbb{R}; \mathbb{C}) \ as \ n \to \infty.$$

## Statement 20
**Corollary 13.3.** Define the map $S: L^2(\lambda_{\mathbb{R}}; \mathbb{C}) \longrightarrow \ell^2(\mathbb{N}; \mathbb{C})$ by

$$[S(\varphi)](k) = (\varphi, \tilde{h}_k)_{L^2(\lambda_{\mathbb{R}};\mathbb{C})}.$$

Then, for each $m \geq 0$, $S \upharpoonright \mathscr{S}^{(m)}(\mathbb{R}; \mathbb{C})$ is an isometric isomorphism from $\mathscr{S}^{(m)}(\mathbb{R}; \mathbb{C})$ onto $\mathfrak{s}^{(m)}(\mathbb{N}; \mathbb{C})$, and so $S \upharpoonright \mathscr{S}(\mathbb{R}; \mathbb{C})$ is isometric homeomorphism from $\mathscr{S}(\mathbb{R}; \mathbb{C})$ onto $\mathfrak{s}(\mathbb{N}; \mathbb{C})$.

## Statement 21
**Lemma 13.4.** Let $\{\alpha_k : k \geq 0\} \subseteq (0, \infty)$, and define the measure $\nu$ on $\mathbb{N}$ by $\nu(\{k\}) = \alpha_k$. Then $L^2(\nu; \mathbb{C})$ is a separable Hilbert space. In addition, a set $B \subseteq L^2(\nu; \mathbb{C})$ is relatively compact if and only if B is bounded and tight in the sense that

$$\lim_{K \to \infty} \sup_{s \in B} \sum_{k > K} \alpha_k |s(k)|^2 = 0.$$

## Statement 22
**Theorem 13.5.** $\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})$ is a separable Hilbert space for each $m \geq 0$, and $\mathscr{S}(\mathbb{R};\mathbb{C})$ is a complete separable metric space. Moreover, a subset $B \subseteq \mathscr{S}(\mathbb{R};\mathbb{C})$ is relatively compact if and only if it is bounded in $\mathscr{S}(\mathbb{R};\mathbb{C})$.

## Statement 23
**Theorem 13.6.** The map $\varphi \leadsto \hat{\varphi}$ is an isomorphism from $\mathscr{S}(\mathbb{R};\mathbb{C})$ onto itself, and, for each $m \geq 0$, $\|\hat{\varphi}\|_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})} = (2\pi)^{\frac{1}{2}} \|\varphi\|_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})}$.

## Statement 24
**Lemma 14.1.** For each $u \in \mathscr{S}(\mathbb{R}; \mathbb{C})^*$ there is an $m \geq 0$ and a $C \in (0, \infty)$ such that

$$|\langle \varphi, u \rangle| \leq C \|\varphi\|_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})} \text{ for all } \varphi \in \mathscr{S}(\mathbb{R};\mathbb{C}).$$

## Statement 25
**Theorem 14.2.** For each $m \geq 0$, $\mathscr{S}^{(-m)}(\mathbb{R};\mathbb{C})$ is a separable Hilbert space in which $\mathscr{S}(\mathbb{R};\mathbb{C})$ is a dense subset, and

$$u \in \mathscr{S}^{(-m)}(\mathbb{R}; \mathbb{C}) \iff \mathcal{H}^{-\frac{m}{2}} u \in L^{2}(\lambda_{\mathbb{R}}; \mathbb{C}) \& |\mathcal{H}^{-\frac{m}{2}} u|_{L^{2}(\lambda_{\mathbb{R}}; \mathbb{C})} = ||u||_{\mathscr{S}^{(-m)}(\mathbb{R}; \mathbb{C})}$$
$$\iff u \in \mathscr{S}^{(m)}(\mathbb{R}; \mathbb{C})^{*}.$$

Moreover, if $u \in \mathscr{S}^{(-m)}(\mathbb{R};\mathbb{C})$, then $\|u\|_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})^*} = \|u\|_{\mathscr{S}^{(-m)}(\mathbb{R};\mathbb{C})}$ and therefore $|\langle \varphi, u \rangle| \leq \|\varphi\|_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})} \|u\|_{\mathscr{S}^{(-m)}(\mathbb{R};\mathbb{C})}$.

## Statement 26
**Theorem 14.3.** If $u \in \mathscr{S}^{(-m)}(\mathbb{R}; \mathbb{C})$ is non-negative in the sense that $\langle \varphi, u \rangle \geq 0$ whenever $\varphi \in \mathscr{S}(\mathbb{R}; \mathbb{C})$ is non-negative, then there exists a Borel measure $\mu$ on $\mathbb{R}$ such that

$$\int (1+x^2)^{-\frac{m+2}{2}} \, \mu(dx) < \infty \ \ and \ \langle \varphi, \mu \rangle = \int \varphi \, d\mu.$$

Conversely, if $\mu$ is a Borel measure on $\mathbb{R}$ satisfying

$$\int (1+x^2)^{-\frac{m}{2}} \,\mu(dx) < \infty$$

and $u \in \mathscr{S}(\mathbb{R}; \mathbb{C})^*$ is defined by $\langle \varphi, u \rangle = \int \varphi \, d\mu$, then $u \in \mathscr{S}^{(-m-3)}(\mathbb{R}; \mathbb{C})$.

## Statement 27
**Theorem 14.4.** Let $\mu$ be a Borel measure on $\mathbb{R}$, and assume that

$$M_{\mu} \equiv \int (1+x^2)^{-\frac{m}{2}} \, \mu(dx) < \infty.$$

If $f \in L^p(\mu; \mathbb{C})$, then there is a distribution $f\mu$ given by

$$\varphi \in \mathscr{S}(\mathbb{R}; \mathbb{C}) \longmapsto \int \varphi \bar{f} \, d\mu \in \mathbb{C}.$$

Moreover, if $m_p = \min\{n : m \leq 2p'n\}$, where $p'$ is the Holder conjugate of $p$, then $f\mu \in \mathcal{S}^{(-m_p-3)}(\mathbb{R};\mathbb{C})$ and

$$||f\mu||_{\mathscr{S}^{(-m_p-3)}(\mathbb{R};\mathbb{C})} \le K_{m_p} M_{\mu}^{\frac{1}{p'}} ||f||_{L^p(\mu;\mathbb{C})}.$$

## Statement 28
**Theorem 14.5.** If $u \in \mathscr{S}^{(-n+1)}(\mathbb{R};\mathbb{C})$, then $u$ is supported on $\{0\}$ if and only if there exist $\{a_0,\ldots,a_n\}\subseteq\mathbb{C}$ for which

$$\langle \varphi, u \rangle = \sum_{m=0}^{n} a_m \partial^m \varphi(0)$$

for all $\varphi \in \mathscr{S}(\mathbb{R}; \mathbb{C})$.

## Statement 29
**Lemma 14.6.** If $u \in \mathscr{S}(\mathbb{R}; \mathbb{R})$ satisfies (14.4) and (14.5), then there exists a unique Borel measure $M$ on $\mathbb{R}$ such that $M(\{0\}) = 0$, $\int \frac{y^2}{1+y^2} M(dy) < \infty$, and

$$\langle \varphi, u \rangle = \int \varphi(y) M(dy)$$

if $\varphi$, $\varphi'$, and $\varphi''$ vanish at 0.

## Statement 30
**Theorem 14.7.** If $u \in \mathscr{S}(\mathbb{R}; \mathbb{R})$ satisfies (14.4) and (14.5), then there exist an $a \geq 0$, $b \in \mathbb{R}$, and Borel measure $M$ on $\mathbb{R}$ such that $M(\{0\}) = 0$, $\int \frac{y^2}{1+y^2} M(dy) < \infty$, and

$$\langle \varphi, u \rangle = \frac{a}{2}\varphi''(0) + b\varphi'(0) + \int (\varphi(y) - \varphi(0) - \mathbf{1}_{[0,1]}(y)\varphi'(0)y) M(dy).$$

In fact, $M$ is determined by

$$\langle \varphi, u \rangle = \int \varphi(y) \, M(dy) \, \text{ if } \varphi \in C_{\rm c}^{\infty} \big( \mathbb{R} \setminus \{0\} \big),$$

and, for any $\eta \in C^{\infty}(\mathbb{R}; [0,1])$ which is 1 on $[-1,1]$ and 0 off $(-2,2)$

$$a = \langle y^2 \eta^2, u \rangle - \int y^2 \eta(y)^2 M(dy)$$

and

$$b = \langle y\eta, u \rangle - \int y \big( \eta(y) - \mathbf{1}_{[0,1]}(y) \big) M(dy).$$

## Statement 31
**Theorem 15.1.** Let $A$ be a continuous map of $\mathscr{S}(\mathbb{R};\mathbb{C})$ into $\mathscr{S}(\mathbb{R};\mathbb{C})^*$, and assume that there is a continuous operator $A^*$ on $\mathscr{S}(\mathbb{R};\mathbb{C})$ such that

$$\left(A^*\varphi,\psi\right)_{L^2(\lambda_{\mathbb{R}};\mathbb{C})} = \left(\varphi,A\psi\right)_{L^2(\lambda_{\mathbb{R}};\mathbb{C})} \text{ for all } \varphi,\psi \in \mathscr{S}(\mathbb{R};\mathbb{C}).$$

If $Au$ is defined for $u \in \mathscr{S}(\mathbb{R}; \mathbb{C})^*$ by

$$\langle \varphi, Au \rangle = \langle A^* \varphi, u \rangle \text{ for } \varphi \in \mathscr{S}(\mathbb{R}; \mathbb{C}),$$

then $u \rightsquigarrow Au$ is the unique extension of $A$ as a continuous operator on $\mathscr{S}(\mathbb{R};\mathbb{C})^*$.

## Statement 32
**Lemma 15.2.** Let $f \in C^{\infty}(\mathbb{R}; \mathbb{R})$, and assume that for each $m \geq 0$ there exists an $k_m \geq 0$ such that

$$F_m \equiv \max_{1 \le j \le m} \sup_{x \in \mathbb{R}} \frac{|\partial^j f(x)|}{|x|^{k_m} \vee 1} < \infty.$$

Then, for each $m \geq 0$, there is a $C_m < \infty$ such that

$$\|\varphi f\|_{\mathscr{S}^{(m)}(\mathbb{R};\mathbb{C})} \le C_m F_m \|\varphi\|_{\mathscr{S}^{(m+k_m)}(\mathbb{R};\mathbb{C})}.$$

## Statement 33
**Theorem 15.3.** For $\psi \in \mathscr{S}(\mathbb{R}; \mathbb{C})$ and $u \in \mathscr{S}(\mathbb{R}; \mathbb{C})^*$, $\psi * u$ is a continuous function with at most polynomial growth, and $C_{\psi}u = \psi * u$. In addition, $\widehat{\psi * u} = \widehat{\psi}\widehat{u}$, and $\psi * u = (2\pi)^{-1}(\widehat{\psi}\widehat{u})^{\vee}$.

## Statement 34
**Lemma 17.1.** The sets $S(\mu, r; \varphi_1, \ldots, \varphi_n)$ with $\varphi_1, \ldots, \varphi_n \in C_c^{\infty}(\mathbb{R}^N; \mathbb{R})$ are a neighborhood basis at $\mu$ for the weak topology.

## Statement 35
**Theorem 17.2.** The weak topology on $\mathbf{M}_1(\mathbb{R}^N)$ is a separable, metric topology.

## Statement 36
**Theorem 17.3.** Given $\{\mu_n : n \geq 1\} \cup \{\mu\} \subseteq \mathbf{M}_1(\mathbb{R}^N)$, the following are equivalent:

- (i) $\mu_n \xrightarrow{\mathbf{w}} \mu$.
- (ii) $|\langle \varphi, \mu_n - \mu \rangle| \longrightarrow 0$ for all $\varphi \in C_c^{\infty}(\mathbb{R}^N; \mathbb{R})$.
- (iii) For all closed sets $F \subseteq \mathbb{R}^N$, $\overline{\lim}_{n \to \infty} \mu_n(F) \le \mu(F)$.
- (iv) For all open sets $G \subseteq \mathbb{R}^N$, $\underline{\lim}_{n \to \infty} \mu_n(G) \ge \mu(G)$.
- (v) For all upper continuous functions $f: \mathbb{R}^N \longrightarrow \mathbb{R}$ that are bounded above, $\overline{\lim}_{n\to\infty} \langle f, \mu_n \rangle \leq \langle f, \mu \rangle$.
- (vi) For all lower continuous functions $f: \mathbb{R}^N \longrightarrow \mathbb{R}$ that are bounded below, $\underline{\lim}_{n\to\infty} \langle f, \mu_n \rangle \geq \langle f, \mu \rangle$.

Finally, if $\Gamma \in \mathcal{B}$ and its boundary $\partial \Gamma$ has $\mu$-measure 0, then $\mu_n \xrightarrow{\mathbf{w}} \mu \implies \mu(\Gamma) = \lim_{n \to \infty} \mu_n(\Gamma)$.

## Statement 37
**Theorem 17.4.** Assume that $\mu_n \xrightarrow{\mathbf{w}} \mu$, let $\psi \in C(\mathbb{R}^N; [0, \infty))$ be an element of $L^1(\mu; \mathbb{R})$ as well as of $\bigcap_{n=1}^{\infty} L^1(\mu_n; \mathbb{R})$. Then $\langle \psi, \mu \rangle \leq \underline{\lim}_{n \to \infty} \langle \psi, \mu_n \rangle$. In addition, if $\{\varphi_n : n \geq 1\} \subseteq C(\mathbb{R}^N; \mathbb{R})$, $|\varphi_n| \leq \psi$ for all $n \geq 1$, and $\langle \psi, \mu_n \rangle \longrightarrow \langle \psi, \mu \rangle$, then $\langle \varphi_n, \mu_n \rangle \longrightarrow \langle \varphi, \mu \rangle$ if $\varphi_n \longrightarrow \varphi$ uniformly on compact subsets.

## Statement 38
**Theorem 17.5.** A subset $A \subseteq \mathbf{M}_1(\mathbb{R}^N)$ is relatively compact in the weak topology if and only if it is tight.

## Statement 39
**Theorem 18.1.** Given $\{\mu_n : n \geq 1\} \cup \{\mu\} \subseteq \mathbf{M}_1(\mathbb{R}^N)$, $\mu_n \xrightarrow{\mathbf{w}} \mu$ if and only if $\hat{\mu}_n(\boldsymbol{\xi}) \longrightarrow \hat{\mu}(\boldsymbol{\xi})$ for each $\boldsymbol{\xi} \in \mathbb{R}^N$. In fact, if $\mu_n \xrightarrow{\mathbf{w}} \mu$, then $\hat{\mu}_n \longrightarrow \hat{\mu}$ uniformly on compact subsets.

## Statement 40
**Theorem 18.2.** (Levy's Continuity Theorem) If $A \subseteq \mathbf{M}_1(\mathbb{R}^N)$, then $A$ is tight if and only if for each $\epsilon > 0$ there exists an $r > 0$ such that

$$\sup_{\substack{\mu \in A \\ |\xi| \le r}} \left| 1 - \hat{\mu}(\xi) \right| \le \epsilon.$$

Hence, $\{\mu_n : n \geq 1\} \subseteq \mathbf{M}_1(\mathbb{R}^N)$ is weakly convergent in $\mathbf{M}_1(\mathbb{R}^N)$ if and only if $\hat{\mu}_n$ converges uniformly in a neighborhood of $\mathbf{0}$, in which case there is a $\mu \in \mathbf{M}_1(\mathbb{R}^N)$ to which $\{\mu_n : n \geq 1\}$ is converging weakly.

## Statement 41
**Theorem 18.3.** A function $f: \mathbb{R}^N \longrightarrow \mathbb{C}$ is a characteristic function if and only if $f$ is continuous, $f(0) = 1$, and $f$ is non-negative definite.

## Statement 42
**Theorem 19.1.** If either $A$ is non-degenerate or $M(G) > 0$ for all non-empty open sets $G \subseteq \mathbb{R}^N \setminus \{\mathbf{0}\}$, then $\mu_{(\mathbf{b},A,M)}(G) > 0$ for all non-empty open sets $G \subseteq \mathbb{R}^N$.

## Statement 43
**Theorem 19.2.** If $N=1$, then $\mu_{(b,A,M)}((-\infty,0))=0$ if and only if

$$A = 0, \ M\big((-\infty, 0)\big) = 0, \ and \ \int_{|y| < 1} y \ M(dy) \le b.$$

## Statement 44
**Theorem 22.1.** (Riesz-Thorin) Given a $\sigma$-finite measure space $(E, \mathcal{F}, \mu)$ and numbers

$$1 \leq p_0, p_1, q_0, q_1 \leq \infty \text{ with } p_0 \wedge p_1 < \infty,$$

assume that $T$ is a linear operator on $L^{p_0}(\mu;\mathbb{C}) \cap L^{p_1}(\mu;\mathbb{C})$ into $L^{q_0}(\mu;\mathbb{C}) \cap L^{q_1}(\mu;\mathbb{C})$ satisfying

$$||Tf||_{L^{q_j}(\mu;\mathbb{C})} \le M_j ||f||_{L^{p_j}(\mu;\mathbb{C})} \text{ for } j \in \{0,1\},$$

where $M_0 \vee M_1 < \infty$. Then, for each $\theta \in [0, 1]$

$$||Tf||_{L^{q_{\theta}}(\mu;\mathbb{C})} \le M_1^{1-\theta} M_2^{\theta} ||f||_{L^{p_{\theta}}(\mu;\mathbb{C})},$$

where $\frac{1}{p_{\theta}} = \frac{1-\theta}{p_0} + \frac{\theta}{p_1}$.

## Statement 45
**Lemma 22.2.** Suppose that $F$ is a bounded continuous function on the closed strip $S = \{z \in \mathbb{C} : \mathfrak{Re}z \in [0,1]\}$ which is analytic on the interior of $S$. If $|F(\imath y)| \leq m_0$ and $|F(1+\imath y)| \leq m_1$ for all $y \in \mathbb{R}$, then $|F(z)| \leq m_0^{1-x} m_1^x$ for $z = x + \imath y \in S$.
