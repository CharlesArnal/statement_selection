In this lecture we consider the classification problem, i.e.  $\mathcal{Y} = \{-1, +1\}$ . Consider a family of weak classifiers

$$\mathcal{H} = \{h \colon \mathcal{X} \to \{-1, +1\}\}.$$

Let the empirical minimizer be

$$h_0 = \operatorname{argmin} \frac{1}{n} \sum_{i=1}^{n} I(h(X_i) \neq Y_i)$$

and assume its expected error,

$$\frac{1}{2} > \varepsilon = Error(h_0), \ \varepsilon > 0$$

Examples:

- $\mathcal{X} = \mathbb{R}^d$ ,  $\mathcal{H} = \{ \operatorname{sign}(wx + b) \colon w \in \mathbb{R}^d, b \in \mathbb{R} \}$
- Decision trees: restrict depth.
- Combination of simple classifiers:

$$f = \sum_{t=1}^{T} \alpha_t h_t(x),$$

where  $h_t \in \mathcal{H}$ ,  $\sum_{t=1}^{T} \alpha_t = 1$ . For example,

$$h_1 = \begin{array}{|c|c|c|}\hline 1 & -1 \\ \hline 1 & -1 \\ \hline \end{array}, \qquad h_2 = \begin{array}{|c|c|c|}\hline 1 & 1 \\ \hline -1 & -1 \\ \hline \end{array}, \qquad h_3 = \begin{array}{|c|c|c|}\hline 1 & 1 \\ \hline 1 & 1 \\ \hline \end{array}$$

$$f = \frac{1}{7}(h_1 + 3h_2 + 3h_3) = \boxed{\begin{array}{c|c} 7 & 5 \\ \hline 1 & -1 \end{array}}, \quad \text{sign}(f) = \boxed{\begin{array}{c|c} 1 & 1 \\ \hline 1 & -1 \end{array}}$$

## AdaBoost

Assign weight to training examples  $w_1(i) = 1/n$ .

for t = 1..T

1) find "good" classifier 
$$h_t \in \mathcal{H}$$
; Error  $\varepsilon_t = \sum_{i=1}^n w_t(i) I(h(X_i) \neq Y_i)$ 

2) update weight for each i:

$$w_{t+1}(i) = \frac{w_t(i)e^{-\alpha_t Y_i h_t(X_i)}}{Z_t}$$
$$Z_t = \sum_{i=1}^n w_t(i)e^{-\alpha_t Y_i h_t(X_i)}$$
$$\alpha_t = \frac{1}{2} \ln \frac{1 - \varepsilon_t}{\varepsilon_t} > 0$$

3) 
$$t = t+1$$

end

Output the final classifier:  $f = sign(\sum \alpha_t h_t(x))$ .

**Theorem 2.1.** Let  $\gamma_t = 1/2 - \varepsilon_t$  (how much better  $h_t$  is than tossing a coin). Then

$$\frac{1}{n} \sum_{i=1}^{n} I(f(X_i) \neq Y_i) \le \prod_{t=1}^{T} \sqrt{1 - 4\gamma_t^2}$$

Proof.

$$I(f(X_i) \neq Y_i) = I(Y_i f(X_i) = -1) = I(Y_i \sum_{t=1}^{T} \alpha_t h_t(X_i) \leq 0) \leq e^{-Y_i \sum_{t=1}^{T} \alpha_t h_t(X_i)}$$

Consider how weight of example i changes:

$$w_{T+1}(i) = \frac{w_T(i)e^{-Y_i\alpha_T h_T(X_i)}}{Z_t}$$
$$= \frac{e^{-Y_i\alpha_T h_T(X_i)}}{Z_t} \frac{w_{T-1}(i)e^{-Y_i\alpha_{T-1} h_{T-1}(X_i)}}{Z_{T-1}}$$

. . .

$$= \frac{e^{-Y_i \sum_{t=1}^{T} \alpha_t h_t(X_i)}}{\prod_{t=1}^{t} Z_t} \frac{1}{n}$$

Hence,

$$w_{T+1}(i) \prod Z_t = \frac{1}{n} e^{-Y_i \sum_{t=1}^T \alpha_t h_t(X_i)}$$

and therefore

$$\frac{1}{n} \sum_{i=1}^{n} I(f(X_i) \neq Y_i) \leq \frac{1}{n} \sum_{i=1}^{n} e^{-Y_i \sum_{t=1}^{T} \alpha_t h_t(X_i)} = \prod_{t=1}^{T} Z_t \sum_{i=1}^{n} w_{T+1}(i) = \prod_{t=1}^{T} Z_t$$

$$Z_{t} = \sum_{i=1}^{n} w_{t}(i)e^{-\alpha_{t}Y_{i}h_{t}(X_{i})}$$

$$= \sum_{i=1}^{n} w_{t}(i)e^{-\alpha_{t}}I(h_{t}(X_{i}) = Y_{i}) + \sum_{i=1}^{n} w_{t}(i)e^{+\alpha_{t}}I(h_{t}(X_{i}) \neq Y_{i})$$

$$= e^{+\alpha_{t}}\sum_{i=1}^{n} w_{t}(i)I(h_{t}(X_{i}) \neq Y_{i}) + e^{-\alpha_{t}}\sum_{i=1}^{n} w_{t}(i)(1 - I(h_{t}(X_{i}) \neq Y_{i}))$$

$$= e^{\alpha_{t}}\varepsilon_{t} + e^{-\alpha_{t}}(1 - \varepsilon_{t})$$

Minimize over  $\alpha_t$  to get

$$\alpha_t = \frac{1}{2} \ln \frac{1 - \varepsilon_t}{\varepsilon_t}$$

and

$$e^{\alpha_t} = \left(\frac{1 - \varepsilon_t}{\varepsilon_t}\right)^{1/2}.$$

Finally,

$$Z_t = \left(\frac{1 - \varepsilon_t}{\varepsilon_t}\right)^{1/2} \varepsilon_t + \left(\frac{\varepsilon_t}{1 - \varepsilon_t}\right)^{1/2} (1 - \varepsilon_t)$$
$$= 2(\varepsilon_t (1 - \varepsilon_t))^{1/2} = 2\sqrt{(1/2 - \gamma_t)(1/2 + \gamma_t)}$$
$$= \sqrt{1 - 4\gamma_t^2}$$

---

As in the previous lecture, consider the classification setting. Let  $\mathcal{X} = \mathbb{R}^d$ ,  $\mathcal{Y} = \{+1, -1\}$ , and

$$\mathcal{H} = \{ \psi x + b, \ \psi \in \mathbb{R}^d, \ b \in \mathbb{R} \}$$

where  $|\psi| = 1$ .

We would like to maximize over the choice of hyperplanes the minimal distance from the data to the hyperplane:

$$\max_{H} \min_{i} d(x_{i}, H),$$

where

$$d(x_i, H) = y_i(\psi x_i + b).$$

Hence, the problem is formulated as maximizing the margin:

$$\max_{\psi,b} \underbrace{\min_{i} y_i(\psi x_i + b)}_{m \text{ (margin)}}.$$

Rewriting,

$$y_i(\psi'x_i + b') = \frac{y_i(\psi x_i + b)}{m} \ge 1,$$

 $\psi' = \psi/m$ , b' = b/m,  $|\psi'| = |\psi|/m = 1/m$ . Maximizing m is therefore minimizing  $|\psi'|$ . Rename  $\psi' \to \psi$ , we have the following formulation:

$$\min |\psi|$$
 such that  $y_i(\psi x_i + b) \ge 1$ 

Equivalently,

$$\min \frac{1}{2} \psi \cdot \psi$$
 such that  $y_i(\psi x_i + b) \ge 1$ 

Introducing Lagrange multipliers:

$$\phi = \frac{1}{2}\psi \cdot \psi - \sum \alpha_i (y_i(\psi x_i + b) - 1), \ \alpha_i \ge 0$$

Take derivatives:

$$\frac{\partial \phi}{\partial \psi} = \psi - \sum_{i} \alpha_i y_i x_i = 0$$
$$\frac{\partial \phi}{\partial h} = -\sum_{i} \alpha_i y_i = 0$$

Hence,

$$\psi = \sum \alpha_i y_i x_i$$

and

$$\sum \alpha_i y_i = 0.$$

Substituting these into  $\phi$ ,

$$\phi = \frac{1}{2} \left( \sum \alpha_i y_i x_i \right)^2 - \sum_{i=1}^n \alpha_i \left( y_i \left( \sum_{j=1}^n \alpha_j y_j x_j x_i + b \right) - 1 \right)$$

$$= \frac{1}{2} \sum_{i,j} \alpha_i \alpha_j y_i y_j x_i x_j - \sum_{i,j} \alpha_i \alpha_j y_i y_j x_i x_j - b \sum \alpha_i y_i + \sum \alpha_i$$

$$= \sum \alpha_i - \frac{1}{2} \sum \alpha_i \alpha_j y_i y_j x_i x_j$$

The above expression has to be maximized this with respect to  $\alpha_i$ ,  $\alpha_i \geq 0$ , which is a Quadratic Programming problem.

Hence, we have  $\psi = \sum_{i=1}^{n} \alpha_i y_i x_i$ .

Kuhn-Tucker condition:

$$\alpha_i \neq 0 \Leftrightarrow y_i(\psi x_i + b) - 1 = 0.$$

Throwing out non-support vectors  $x_i$  does not affect hyperplane  $\Rightarrow \alpha_i = 0$ .

The mapping  $\phi$  is a feature mapping:

$$x \in \mathbb{R}^d \longrightarrow \phi(x) = (\phi_1(x), \phi_2(x), ...) \in \mathcal{X}'$$

where  $\mathcal{X}'$  is called feature space

Support Vector Machines find optimal separating hyperplane in a very high-dimensional space. Let  $K(x_i, x_j) = \sum_{k=1}^{\infty} \phi_k(x_i) \phi_k(x_j)$  be a scalar product in  $\mathcal{X}'$ . Notice that we don't need to know mapping  $x \to \phi(x)$ . We only need to know  $K(x_i, x_j) = \sum_{k=1}^{\infty} \phi_k(x_i) \phi_k(x_j)$ , a symmetric positive definite kernel.

Examples:

- (1) Polynomial:  $K(x_1, x_2) = (x_1x_2 + 1)^{\ell}, \ \ell \ge 1.$
- (2) Radial Basis:  $K(x_1, x_2) = e^{-\gamma |x_1 x_2|^2}$ .

(3) Neural (two-layer):  $K(x_1, x_2) = \frac{1}{1 + e^{\alpha x_1 x_2 + \beta}}$  for some  $\alpha, \beta$  (for some it's not positive definite).

Once  $\alpha_i$  are known, the decision function becomes

$$\operatorname{sign}\left(\sum \alpha_i y_i x_x \cdot x + b\right) = \operatorname{sign}\left(\sum \alpha_i y_i K(x_i, x) + b\right)$$

---

Assume we have samples  $z_1 = (x_1, y_1), \ldots, z_n = (x_n, y_n)$  as well as a new sample  $z_{n+1}$ . The classifier trained on the data  $z_1, \ldots, z_n$  is  $f_{z_1, \ldots, z_n}$ .

The error of this classifier is

$$\operatorname{Error}(z_1, \dots, z_n) = \mathbb{E}_{z_{n+1}} I(f_{z_1, \dots, z_n}(x_{n+1}) \neq y_{n+1}) = \mathbb{P}_{z_{n+1}} (f_{z_1, \dots, z_n}(x_{n+1}) \neq y_{n+1})$$

and the Average Generalization Error

A.G.E. = 
$$\mathbb{E} \operatorname{Error}(z_1, \dots, z_n) = \mathbb{E}\mathbb{E}_{z_{n+1}} I(f_{z_1, \dots, z_n}(x_{n+1}) \neq y_{n+1}).$$

Since  $z_1, \ldots, z_n, z_{n+1}$  are i.i.d., in expectation training on  $z_1, \ldots, z_i, \ldots, z_n$  and evaluating on  $z_{n+1}$  is the same as training on  $z_1, \ldots, z_{n+1}, \ldots, z_n$  and evaluating on  $z_i$ . Hence, for any i,

A.G.E. = 
$$\mathbb{EE}_{z_i} I(f_{z_1,...,z_{n+1},...,z_n}(x_i) \neq y_i)$$

and

A.G.E. = 
$$\mathbb{E}\left[\underbrace{\frac{1}{n+1}\sum_{i=1}^{n+1}I(f_{z_1,\dots,z_{n+1},\dots,z_n}(x_i)\neq y_i)}_{\text{leave-one-out error}}\right].$$

Therefore, to obtain a bound on the generalization ability of an algorithm, it's enough to obtain a bound on its leave-one-out error. We now prove such a bound for SVMs. Recall that the solution of SVM is  $\varphi = \sum_{i=1}^{n+1} \alpha_i^0 y_i x_i$ .

## Theorem 4.1.

$$L.O.O.E. \le \frac{\min(\# support \ vect., D^2/m^2)}{n+1}$$

where D is the diameter of a ball containing all  $x_i$ ,  $i \leq n+1$  and m is the margin of an optimal hyperplane.

## Remarks:

- $\bullet$  dependence on sample size is  $\frac{1}{n}$
- dependence on margin is  $\frac{1}{m^2}$
- number of support vectors (sparse solution)

**Lemma** 4.1. If  $x_i$  is a support vector and it is misclassified by leaving it out, then  $\alpha_i^0 \geq \frac{1}{D^2}$ .

Given Lemma 4.1, we prove Theorem 4.1 as follows.

Proof. Clearly,

L.O.O.E. 
$$\leq \frac{\text{\# support vect.}}{n+1}$$
.

Indeed, if  $x_i$  is not a support vector, then removing it does not affect the solution. Using Lemma 4.1 above,

$$\sum_{i \in \text{supp.vect}} I(x_i \text{ is misclassified}) \leq \sum_{i \in \text{supp.vect}} \alpha_i^0 D^2 = D^2 \sum \alpha_i^0 = \frac{D^2}{m^2}.$$

In the last step we use the fact that  $\sum \alpha_i^0 = \frac{1}{m^2}$ . Indeed, since  $|\varphi| = \frac{1}{m}$ ,

$$\frac{1}{m^2} = |\varphi|^2 = \varphi \cdot \varphi = \varphi \cdot \sum_i \alpha_i^0 y_i x_i$$

$$= \sum_i \alpha_i^0 (y_i \varphi \cdot x_i)$$

$$= \sum_i \alpha_i^0 (y_i (\varphi \cdot x_i + b) - 1) + \sum_i \alpha_i^0 - b \sum_i \alpha_i^0 y_i$$

$$= \sum_i \alpha_i^0$$

We now prove Lemma 4.1.

*Proof.* Define

$$w(\alpha) = \sum \alpha_i - \frac{1}{2} \left( \sum \alpha_i y_i x_i \right)^2,$$

which we maximize under constraints

(1) 
$$\alpha_i \ge 0 \quad \text{and} \quad \sum y_i \alpha_i = 0.$$


Assume the following ordering on the support vectors when trained on  $z_1, \ldots, z_n, z_{n+1}$ :

$$\underbrace{\alpha_1^0, \dots, \alpha_k^0, 0, \dots, 0}_{-} = \alpha^0$$

where the first k points are the support vectors. Now, assume we leave out  $x_1$  and make a mistake on it, and

$$\alpha_1 = 0.$$

Now we have

$$\underbrace{0,\ldots,0}_{+},\underbrace{\alpha_{1}^{\prime},\ldots,\alpha_{\ell}^{\prime}},\underbrace{0,\ldots,0}_{-}=\alpha^{\prime}$$

where  $\beta \in \{0,1\}^n$ .

Let t > 0 and suppose  $\alpha' + t\beta$  satisfies optimization conditions (1). We know that

$$w(\alpha' + t\beta) \le w(\alpha^0).$$

Hence,

$$w(\alpha^0) - w(\alpha') \ge w(\alpha + t\beta) - w(\alpha').$$

Moreover,

$$w(\alpha') = \sum \alpha'_i - \frac{1}{2} \left( \sum \alpha'_i y_i x_i \right)^2$$

and

$$w(\alpha' + t\beta) = \sum \alpha_i' + t \sum \beta_i - \frac{1}{2} \left( \sum \alpha_i' y_i x_i + t \sum \beta_i y_i x_i \right)^2$$
$$= \sum \alpha_i' + t \sum \beta_i - \frac{1}{2} \left( \sum \alpha_i' y_i x_i \right)^2 - t \sum \alpha_i' y_i x_i \cdot \sum \beta_i y_i x_i - \frac{t^2}{2} \left( \sum \beta_i y_i x_i \right)^2.$$

Hence,

$$w(\alpha' + t\beta) - w(\alpha') = t \sum_{\varphi} \beta_i - t \underbrace{\sum_{\varphi'} \alpha'_i y_i x_i}_{\varphi'} \cdot \sum_{\varphi} \beta_i y_i x_i - \frac{t^2}{2} \left( \sum_{\varphi} \beta_i y_i x_i \right)^2$$

$$= t \sum_{\varphi} \beta_i (1 - y_i \varphi' \cdot x_i) - \frac{t^2}{2} \left( \sum_{\varphi} \beta_i y_i x_i \right)^2$$

$$= t \sum_{\varphi} \beta_i (1 - y_i (\varphi' \cdot x_i + b)) + tb \underbrace{\sum_{\varphi} \beta_i y_i}_{0} - \frac{t^2}{2} \left( \sum_{\varphi} \beta_i y_i x_i \right)^2$$

$$= t(1 - y_1 (\varphi' \cdot x_1 + b)) - \frac{t^2}{2} \left( \sum_{\varphi} \beta_i y_i x_i \right)^2$$

Maximizing the above expression over t, we find

$$t = \frac{1 - y_1(\varphi' \cdot x_1 + b)}{\left(\sum \beta_i y_i x_i\right)^2} \ge 0.$$

Substituting this t back into the expression.

$$w(\alpha' + t\beta) - w(\alpha') = \frac{\left(1 - y_1(\varphi' \cdot x_1 + b)\right)^2}{2\left(\sum \beta_i y_i x_i\right)^2}$$

Since  $x_1$  is misclassified,  $y_1(\varphi' \cdot x_1 + b) \leq 0$ . Hence,

$$w(\alpha' + t\beta) - w(\alpha') \ge \frac{1}{2\left(\sum \beta_i y_i x_i\right)^2} \ge \frac{1}{2D^2}$$

because  $|x_1 - x_2| \le D$ .

Now define  $\gamma$  as  $\gamma(1) = \alpha_1^0$ ,  $\gamma(i) = \alpha_i^0$  for  $p \le i \le k$ , and  $\gamma(i) = 0$  otherwise, where

$$\underbrace{\alpha_1^0,\ldots}_{\perp},\underbrace{\alpha_p^0,\ldots,\alpha_k^0,0,\ldots,0}_{\perp}.$$

We have

$$w(\alpha^0) - w(\alpha') \ge \frac{1}{2D^2}$$

and  $\alpha^0 - \gamma$  satisfies constraint (2) and

$$w(\alpha^0 - \gamma) \le w(\alpha').$$

$$w(\alpha^{0}) - w(\alpha') \leq w(\alpha^{0}) - w(\alpha^{0} - \gamma) = \dots \text{ similarly to the previous proof}$$

$$= \frac{1}{2} \left( \sum \gamma_{i} y_{i} x_{i} \right)^{2} = \frac{(\alpha_{1}^{0})^{2}}{2} \left( \sum \frac{\gamma_{i}}{\alpha_{1}^{0}} y_{i} x_{i} \right)^{2}$$

$$= x_{1} - \sum_{i=p}^{k} \frac{\gamma_{i}}{\alpha_{1}^{0}} x_{i} \leq \frac{(\alpha_{1}^{0})^{2}}{2} \cdot D^{2}$$

$$\text{convex combination}$$

Hence,

$$\frac{1}{2D^2} \le w(\alpha^0) - w(\alpha') \le \frac{(\alpha_1^0)^2}{2} \cdot D^2$$

and so

$$\alpha_1^0 \ge \frac{1}{D^2}.$$

---

Bennett's inequality.

For a fixed  $f \in \mathcal{F}$ , if we observe  $\frac{1}{n} \sum_{i=1}^{n} I\left(f(X_i) \neq Y_i\right)$  is small, can we say that  $\mathbb{P}\left(f(X) \neq Y\right)$  is small? By the Law of Large Numbers,

$$\frac{1}{n} \sum_{i=1}^{n} I\left(f(X_i) \neq Y_i\right) \to \mathbb{E}I(f(X) \neq Y) = \mathbb{P}\left(f(X) \neq Y\right).$$

The Central Limit Theorem says

$$\frac{\sqrt{n}\left(\frac{1}{n}\sum_{i=1}^{n}I\left(f(X_{i})\neq Y_{i}\right)-\mathbb{E}I(f(X)\neq Y)\right)}{\sqrt{\operatorname{Var}I}}\to\mathcal{N}(0,1).$$

Thus,

$$\frac{1}{n} \sum_{i=1}^{n} I\left(f(X_i) \neq Y_i\right) - \mathbb{E}I(f(X) \neq Y) \sim \frac{k}{\sqrt{n}}.$$

Let  $Z_1, \dots, Z_n \in \mathbb{R}$  be i.i.d. random variables. We're interested in bounds on  $\frac{1}{n} \sum Z_i - \mathbb{E}Z_i$ 

- (1) Jensen's inequality: If  $\phi$  is a convex function, then  $\phi(\mathbb{E}Z) \leq \mathbb{E}\phi(X)$ .
- (2) Chebyshev's inequality: If  $Z \ge 0$ , then  $\mathbb{P}(Z \ge t) \le \frac{\mathbb{E}Z}{t}$ Proof:

$$\mathbb{E}Z = \mathbb{E}ZI(Z < t) + \mathbb{E}ZI(Z \ge t) \ge \mathbb{E}ZI(Z \ge t)$$
$$> \mathbb{E}tI(Z > t) = t\mathbb{P}(Z > t).$$

(3) Markov's inequality: Let Z be a signed r.v. Then for any  $\lambda > 0$ 

$$\mathbb{P}\left(Z \geq t\right) = \mathbb{P}\left(e^{\lambda Z} \geq e^{\lambda t}\right) \leq \frac{\mathbb{E}e^{\lambda Z}}{e^{\lambda t}}$$

and therefore

$$\mathbb{P}\left(Z \geq t\right) \leq \inf_{\lambda > 0} e^{-\lambda t} \mathbb{E} e^{\lambda Z}.$$

**Theorem 5.1** (Bennett). Assume  $\mathbb{E}Z = 0$ ,  $\mathbb{E}Z^2 = \sigma^2$ , |Z| < M = const,  $Z_1, \dots, Z_n$  independent copies of Z, and  $t \geq 0$ . Then

$$\mathbb{P}\left(\sum_{i=1}^{n} Z_i \ge t\right) \le \exp\left(-\frac{n\sigma^2}{M^2}\phi\left(\frac{tM}{n\sigma^2}\right)\right),\,$$

where  $\phi(x) = (1+x)\log(1+x) - x$ .

*Proof.* Since  $Z_i$  are i.i.d.,

$$\mathbb{P}\left(\sum_{i=1}^{n} Z_{i} \geq t\right) \leq e^{-\lambda t} \mathbb{E}e^{\lambda \sum_{i=1}^{n} Z_{i}} = e^{-\lambda t} \prod_{i=1}^{n} \mathbb{E}e^{\lambda Z_{i}} = e^{-\lambda t} \left(\mathbb{E}e^{\lambda Z}\right)^{n}.$$

Expanding,

$$\mathbb{E}e^{\lambda Z} = \mathbb{E}\sum_{k=0}^{\infty} \frac{(\lambda Z)^k}{k!} = \sum_{k=0}^{\infty} \lambda^k \frac{\mathbb{E}Z^k}{k!}$$

$$= 1 + \sum_{k=2}^{\infty} \frac{\lambda^k}{k!} \mathbb{E}Z^2 Z^{k-2} \le 1 + \sum_{k=2}^{\infty} \frac{\lambda^k}{k!} M^{k-2} \sigma^2$$

$$= 1 + \frac{\sigma^2}{M^2} \sum_{k=2}^{\infty} \frac{\lambda^k M^k}{k!} = 1 + \frac{\sigma^2}{M^2} \left( e^{\lambda M} - 1 - \lambda M \right)$$

$$\le \exp\left(\frac{\sigma^2}{M^2} \left( e^{\lambda M} - 1 - \lambda M \right) \right)$$

where the last inequality follows because  $1 + x \le e^x$ .

Combining the results,

$$\mathbb{P}\left(\sum_{i=1}^{n} Z_{i} \geq t\right) \leq e^{-\lambda t} \exp\left(\frac{n\sigma^{2}}{M^{2}}\left(e^{\lambda M} - 1 - \lambda M\right)\right)$$
$$= \exp\left(-\lambda t + \frac{n\sigma^{2}}{M^{2}}\left(e^{\lambda M} - 1 - \lambda M\right)\right)$$

Now, minimize the above bound with respect to  $\lambda$ . Taking derivative w.r.t.  $\lambda$  and setting it to zero:

$$-t + \frac{n\sigma^2}{M^2} \left( M e^{\lambda M} - M \right) = 0$$
$$e^{\lambda M} = \frac{tM}{n\sigma^2} + 1$$
$$\lambda = \frac{1}{M} \log \left( 1 + \frac{tM}{n\sigma^2} \right).$$

The bound becomes

$$\mathbb{P}\left(\sum_{i=1}^{n} Z_{i} \geq t\right) \leq \exp\left(-\frac{t}{M}\log\left(1 + \frac{tM}{n\sigma^{2}}\right) + \frac{n\sigma^{2}}{M^{2}}\left(\frac{tM}{n\sigma^{2}} + 1 - \log\left(1 + \frac{tM}{n\sigma^{2}}\right)\right)\right) \\
= \exp\left(\frac{n\sigma^{2}}{M^{2}}\left(\frac{tM}{n\sigma^{2}} - \log\left(1 + \frac{tM}{n\sigma^{2}}\right) - \frac{tM}{n\sigma^{2}}\log\left(1 + \frac{tM}{n\sigma^{2}}\right)\right)\right) \\
= \exp\left(\frac{n\sigma^{2}}{M^{2}}\left(\frac{tM}{n\sigma^{2}} - \left(1 + \frac{tM}{n\sigma^{2}}\right)\log\left(1 + \frac{tM}{n\sigma^{2}}\right)\right)\right) \\
= \exp\left(-\frac{n\sigma^{2}}{M^{2}}\phi\left(\frac{tM}{n\sigma^{2}}\right)\right)$$

---

Last time we proved Bennett's inequality:  $\mathbb{E}X = 0$ ,  $\mathbb{E}X^2 = \sigma^2$ , |X| < M = const,  $X_1, \dots, X_n$  independent copies of X, and  $t \geq 0$ . Then

$$\mathbb{P}\left(\sum_{i=1}^{n} X_i \ge t\right) \le \exp\left(-\frac{n\sigma^2}{M^2}\phi\left(\frac{tM}{n\sigma^2}\right)\right),\,$$

where  $\phi(x) = (1+x)\log(1+x) - x$ .

If X is small,  $\phi(x) = (1+x)(x - \frac{x^2}{2} + \cdots) - x = x + x^2 - \frac{x^2}{2} - x + \cdots = \frac{x^2}{2} + \cdots$ 

If X is large,  $\phi(x) \sim x \log x$ .

We can weaken the bound by decreasing  $\phi(x)$ . Take<sup>1</sup>  $\phi(x) = \frac{x^2}{2 + \frac{2}{3}x}$  to obtain **Bernstein's** inequality:

$$\mathbb{P}\left(\sum_{i=1}^{n} X_{i} \ge t\right) \le \exp\left(-\frac{n\sigma^{2}}{M^{2}} \left(\frac{\left(\frac{tM}{n\sigma^{2}}\right)^{2}}{2 + \frac{2}{3}\frac{tM}{n\sigma^{2}}}\right)\right)$$

$$= \exp\left(-\frac{t^{2}}{2n\sigma^{2} + \frac{2}{3}tM}\right)$$

$$= e^{-u}$$

where  $u = \frac{t^2}{2n\sigma^2 + \frac{2}{3}tM}$ . Solve for t:

$$t^2 - \frac{2}{3}uMt - 2n\sigma^2u = 0$$

$$t = \frac{1}{3}uM + \sqrt{\frac{u^2M^2}{9} + 2n\sigma^2u}.$$

Substituting,

$$\mathbb{P}\left(\sum_{i=1}^{n} X_i \ge \sqrt{\frac{u^2 M^2}{9} + 2n\sigma^2 u} + \frac{uM}{3}\right) \le e^{-u}$$

or

$$\mathbb{P}\left(\sum_{i=1}^{n} X_{i} \le \sqrt{\frac{u^{2}M^{2}}{9} + 2n\sigma^{2}u} + \frac{uM}{3}\right) \ge 1 - e^{-u}$$

Using inequality  $\sqrt{a+b} \le \sqrt{a} + \sqrt{b}$ ,

$$\mathbb{P}\left(\sum_{i=1}^{n} X_i \le \sqrt{2n\sigma^2 u} + \frac{2uM}{3}\right) \ge 1 - e^{-u}$$

<sup>&</sup>lt;sup>1</sup>exercise: show that this is the best approximation

For non-centered  $X_i$ , replace  $X_i$  with  $X_i - \mathbb{E}X$  or  $\mathbb{E}X - X_i$ . Then  $|X_i - \mathbb{E}X| \leq 2M$  and so with high probability

$$\sum (X_i - \mathbb{E}X) \le \sqrt{2n\sigma^2 u} + \frac{4uM}{3}.$$

Normalizing by n,

$$\frac{1}{n}\sum X_i - \mathbb{E}X \le \sqrt{\frac{2\sigma^2 u}{n}} + \frac{4uM}{3n}$$

and

$$\mathbb{E}X - \frac{1}{n} \sum X_i \le \sqrt{\frac{2\sigma^2 u}{n}} + \frac{4uM}{3n}.$$

Whenever  $\sqrt{\frac{2\sigma^2 u}{n}} \geq \frac{4uM}{3n}$ , we have  $u \leq \frac{n\sigma^2}{8M^2}$ . So,  $\left|\frac{1}{n}\sum X_i - \mathbb{E}X\right| \lesssim \sqrt{\frac{2\sigma^2 u}{n}}$  for  $u \lesssim n\sigma^2$  (range of normal deviations). This is predicted by the Central Limit Theorem (condition for CLT is  $n\sigma^2 \to \infty$ ). If  $n\sigma^2$  does not go to infinity, we get Poisson behavior.

Recall from the last lecture that the we're interested in concentration inequalities because we want to know  $\mathbb{P}(f(X) \neq Y)$  while we only observe  $\frac{1}{n} \sum_{i=1}^{n} I(f(X_i) \neq Y_i)$ . In Bernstein's inequality take "X" to be  $I(f(X_i) \neq Y_i)$ . Then, since 2M = 1, we get

$$\mathbb{E}I(f(X_i) \neq Y_i) - \frac{1}{n} \sum_{i=1}^{n} I\left(f(X_i) \neq Y_i\right) \leq \sqrt{\frac{2\mathbb{P}\left(f(X_i) \neq Y_i\right)\left(1 - \mathbb{P}\left(f(X_i) \neq Y_i\right)\right)u}{n}} + \frac{2u}{3n}$$

because  $\mathbb{E}I(f(X_i) \neq Y_i) = \mathbb{P}(f(X_i) \neq Y_i) = \mathbb{E}I^2$  and therefore  $\text{Var}(I) = \sigma^2 = \mathbb{E}I^2 - (\mathbb{E}I)^2$ . Thus,

$$\mathbb{P}\left(f(X_i) \neq Y_i\right) \leq \frac{1}{n} \sum_{i=1}^n I\left(f(X_i) \neq Y_i\right) + \sqrt{\frac{2\mathbb{P}\left(f(X_i) \neq Y_i\right)u}{n}} + \frac{2u}{3n}$$

with probability at least  $1 - e^{-u}$ . When the training error is zero,

$$\mathbb{P}\left(f(X_i) \neq Y_i\right) \leq \sqrt{\frac{2\mathbb{P}\left(f(X_i) \neq Y_i\right)u}{n}} + \frac{2u}{3n}.$$

If we forget about 2u/3n for a second, we obtain  $\mathbb{P}(f(X_i) \neq Y_i)^2 \leq 2\mathbb{P}(f(X_i) \neq Y_i) u/n$  and hence

$$\mathbb{P}\left(f(X_i) \neq Y_i\right) \le \frac{2u}{n}.$$

The above zero-error rate is better than  $n^{-1/2}$  predicted by CLT.

---

Let  $a_1, \ldots, a_n \in \mathbb{R}$  and let  $\varepsilon_1, \ldots, \varepsilon_n$  be i.i.d. Rademacher random variables:  $\mathbb{P}(\varepsilon_i = 1) = \mathbb{P}(\varepsilon_i = -1) = 0.5$ .

**Theorem 7.1** (Hoeffding). For  $t \geq 0$ ,

$$\mathbb{P}\left(\sum_{i=1}^{n} \varepsilon_{i} a_{i} \geq t\right) \leq \exp\left(-\frac{t^{2}}{2\sum_{i=1}^{n} a_{i}^{2}}\right).$$

*Proof.* Similarly to the proof of Bennett's inequality (Lecture 5),

$$\mathbb{P}\left(\sum_{i=1}^{n} \varepsilon_{i} a_{i} \geq t\right) \leq e^{-\lambda t} \mathbb{E} \exp\left(\lambda \sum_{i=1}^{n} \varepsilon_{i} a_{i}\right) = e^{-\lambda t} \prod_{i=1}^{n} \mathbb{E} \exp\left(\lambda \varepsilon_{i} a_{i}\right).$$

Using inequality  $\frac{e^x+e^{-x}}{2} \leq e^{x^2/2}$  (from Taylor expansion), we get

$$\mathbb{E}\exp\left(\lambda\varepsilon_{i}a_{i}\right) = \frac{1}{2}e^{\lambda a_{i}} + \frac{1}{2}e^{-\lambda a_{i}} \leq e^{\frac{\lambda^{2}a_{i}^{2}}{2}}.$$

Hence, we need to minimize the bound with respect to  $\lambda > 0$ :

$$\mathbb{P}\left(\sum_{i=1}^{n} \varepsilon_{i} a_{i} \geq t\right) \leq e^{-\lambda t} e^{\frac{\lambda^{2}}{2} \sum_{i=1}^{n} a_{i}^{2}}.$$

Setting derivative to zero, we obtain the result.

Now we change variable:  $u = \frac{t^2}{2\sum_{i=1}^n a_i^2}$ . Then  $t = \sqrt{2u\sum_{i=1}^n a_i^2}$ .

$$\mathbb{P}\left(\sum_{i=1}^{n} \varepsilon_{i} a_{i} \geq \sqrt{2u \sum_{i=1}^{n} a_{i}^{2}}\right) \leq e^{-u}$$

and

$$\mathbb{P}\left(\sum_{i=1}^{n} \varepsilon_{i} a_{i} \leq \sqrt{2u \sum_{i=1}^{n} a_{i}^{2}}\right) \geq 1 - e^{-u}.$$

Here  $\sum_{i=1}^{n} a_i^2 = \operatorname{Var}(\sum_{i=1}^{n} \varepsilon_i a_i)$ .

Rademacher sums will play important role in future. Consider again the problem of estimating  $\frac{1}{n}\sum_{i=1}^{n} f(X_i) - \mathbb{E}f$ . We will see that by the Symmetrization technique,

$$\frac{1}{n}\sum_{i=1}^{n} f(X_i) - \mathbb{E}f \sim \frac{1}{n}\sum_{i=1}^{n} f(X_i) - \frac{1}{n}\sum_{i=1}^{n} f(X_i').$$

In fact,

$$\mathbb{E}\left|\frac{1}{n}\sum_{i=1}^n f(X_i) - \mathbb{E}f\right| \le \mathbb{E}\left|\frac{1}{n}\sum_{i=1}^n f(X_i) - \frac{1}{n}\sum_{i=1}^n f(X_i')\right| \le 2\mathbb{E}\left|\frac{1}{n}\sum_{i=1}^n f(X_i) - \mathbb{E}f\right|.$$

The second inequality above follows by adding and subtracting  $\mathbb{E}f$ :

$$\mathbb{E}\left|\frac{1}{n}\sum_{i=1}^{n}f(X_{i})-\frac{1}{n}\sum_{i=1}^{n}f(X_{i}')\right| \leq \mathbb{E}\left|\frac{1}{n}\sum_{i=1}^{n}f(X_{i})-\mathbb{E}f\right|+\mathbb{E}\left|\frac{1}{n}\sum_{i=1}^{n}f(X_{i}')-\mathbb{E}f\right|$$

$$= 2\mathbb{E}\left|\frac{1}{n}\sum_{i=1}^{n}f(X_{i})-\mathbb{E}f\right|$$

while for the first inequality we use Jensen's inequality:

$$\mathbb{E}\left|\frac{1}{n}\sum_{i=1}^{n}f(X_{i})-\mathbb{E}f\right| = \mathbb{E}\left|\frac{1}{n}\sum_{i=1}^{n}f(X_{i})-\frac{1}{n}\sum_{i=1}^{n}\mathbb{E}f(X_{i}')\right|$$

$$\leq \mathbb{E}_{X}\mathbb{E}_{X'}\left|\frac{1}{n}\sum_{i=1}^{n}f(X_{i})-\frac{1}{n}\sum_{i=1}^{n}\mathbb{E}f(X_{i}')\right|.$$

Note that  $\frac{1}{n} \sum_{i=1}^{n} f(X_i) - \frac{1}{n} \sum_{i=1}^{n} \mathbb{E}f(X_i')$  is equal in distribution to  $\frac{1}{n} \sum_{i=1}^{n} \varepsilon_i(f(X_i) - f(X_i'))$ . We now prove Hoeffding-Chernoff Inequality:

**Theorem 7.2.** Assume  $0 \le X_i \le 1$  and  $\mu = \mathbb{E}X$ . Then

$$\mathbb{P}\left(\sum_{i=1}^{n} X_i - \mu \ge t\right) \le e^{-n\mathcal{D}(\mu + t, \mu)}$$

where the KL-divergence  $\mathcal{D}(p,q) = p \log \frac{p}{q} + (1-p) \log \frac{1-p}{1-q}$ 

*Proof.* Note that  $\phi(x) = e^{\lambda x}$  is convex and so  $e^{\lambda x} = e^{\lambda(x\cdot 1 + (1-x)\cdot 0)} \le xe^{\lambda} + (1-x)e^{\lambda \cdot 0} = 1 - x + xe^{\lambda}$ . Hence,

$$\mathbb{E}e^{\lambda X} = 1 - \mathbb{E}X + \mathbb{E}Xe^{\lambda} = 1 - \mu + \mu e^{\lambda}.$$

Again, we minimize the following bound with respect to  $\lambda > 0$ :

$$\mathbb{P}\left(\sum_{i=1}^{n} X_{i} \geq n(\mu+t)\right) \leq e^{-\lambda n(\mu+t)} \mathbb{E}e^{\lambda \sum X_{i}}$$

$$= e^{-\lambda n(\mu+t)} \left(\mathbb{E}e^{\lambda X}\right)^{n}$$

$$\leq e^{-\lambda n(\mu+t)} \left(1 - \mu + \mu e^{\lambda}\right)^{n}$$

Take derivative w.r.t.  $\lambda$ :

$$-n(\mu+t)e^{-\lambda n(\mu+t)}(1-\mu+\mu e^{\lambda})^n + n(1-\mu+\mu e^{\lambda})^{n-1}\mu e^{\lambda}e^{-\lambda n(\mu+t)} = 0$$
$$-(\mu+t)(1-\mu+\mu e^{\lambda}) + \mu e^{\lambda} = 0$$
$$e^{\lambda} = \frac{(1-\mu)(\mu+t)}{\mu(1-\mu-t)}.$$

Substituting,

$$\mathbb{P}\left(\sum_{i=1}^{n} X_{i} \ge n(\mu+t)\right) \le \left(\left(\frac{\mu(1-\mu-t)}{(1-\mu)(\mu+t)}\right)^{\mu+t} \left(1-\mu+\frac{(1-\mu)(\mu+t)}{1-\mu-t}\right)\right)^{n} \\
= \left(\left(\frac{\mu}{\mu+t}\right)^{\mu+t} \left(\frac{1-\mu}{1-\mu-t}\right)^{1-\mu-t}\right)^{n} \\
= \exp\left(-n\left((\mu+t)\log\frac{\mu+t}{\mu} + (1-\mu-t)\log\frac{1-\mu-t}{1-\mu}\right)\right),$$

completing the proof. Moreover,

$$\mathbb{P}\left(\mu - \sum_{i=1}^{n} X_i \ge t\right) = \mathbb{P}\left(\sum_{i=1}^{n} Z_i - \mu_Z \ge t\right) \le e^{-n\mathcal{D}(\mu_z + t, \mu_Z)} = e^{-n\mathcal{D}(1 - \mu_X + t, 1 - \mu_X)}$$

where  $Z_i = 1 - X_i$  (and thus  $\mu_Z = 1 - \mu_X$ ).

If  $0 < \mu \le 1/2$ ,

$$\mathcal{D}(1 - \mu + t, 1 - \mu) \ge \frac{t^2}{2\mu(1 - \mu)}.$$

Hence, we get

$$\mathbb{P}\left(\mu - \sum_{i=1}^{n} X_i \ge t\right) \le e^{-\frac{nt^2}{2\mu(1-\mu)}} = e^{-u}.$$

Solving for t,

$$\mathbb{P}\left(\mu - \sum_{i=1}^{n} X_i \ge \sqrt{\frac{2\mu(1-\mu)u}{n}}\right) \le e^{-u}.$$

If  $X_i = 0, 1$ , then  $\mu = \mathbb{E}X = \mathbb{P}(X = 1)$  and  $Var(X) = \mu(1 - \mu)$ .

---

Assume  $f \in \mathcal{F} = \{f : \mathcal{X} \mapsto \mathbb{R}\}$  and  $x_1, \dots, x_n$  are i.i.d. Denote  $\mathbb{P}_n f = \frac{1}{n} \sum_{i=1}^n f(x_i)$  and  $\mathbb{P}f = \int f dP = \mathbb{E}f$ . We are interested in bounding  $\frac{1}{n} \sum_{i=1}^n f(x_i) - \mathbb{E}f$ .

Worst-case scenario is the value

$$\sup_{f\in\mathcal{F}}|\mathbb{P}_nf-\mathbb{P}f|.$$

The Glivenko-Cantelli property  $GC(\mathcal{F}, P)$  says that

$$\mathbb{E}\sup_{f\in\mathcal{F}}|\mathbb{P}_nf-\mathbb{P}f|\to 0$$

as  $n \to \infty$ .

- Algorithm can output any  $f \in \mathcal{F}$
- Objective is determined by  $\mathbb{P}_n f$  (on the data)
- Goal is  $\mathbb{P}f$
- $\bullet$  Distribution P is unknown

The most pessimistic requirement is

$$\sup_{P} \mathbb{E} \sup_{f \in \mathcal{F}} |\mathbb{P}_n f - \mathbb{P} f| \to 0$$

which we denote

uniform
$$GC(\mathcal{F})$$
.

## VC classes of sets

Let  $C = \{C \subseteq X\}$ ,  $f_C(x) = I(x \in C)$ . The most pessimistic value is

$$\sup_{P} \mathbb{E} \sup_{C \in \mathcal{C}} |\mathbb{P}_{n}(C) - \mathbb{P}(C)| \to 0.$$

For any sample  $\{x_1, \ldots, x_n\}$ , we can look at the ways that  $\mathcal{C}$  intersects with the sample:

$${C \cap \{x_1,\ldots,x_n\} : C \in \mathcal{C}\}.$$

Let

$$\Delta_n(\mathcal{C}, x_1, \dots, x_n) = \operatorname{card} \{C \cap \{x_1, \dots, x_n\} : C \in \mathcal{C}\},\$$

the number of different subsets picked out by  $C \in \mathcal{C}$ . Note that this number is at most  $2^n$ . Denote

$$\triangle_n(\mathcal{C}) = \sup_{\{x_1,\dots,x_n\}} \triangle_n(\mathcal{C},x_1,\dots,x_n) \le 2^n.$$

We will see that for some classes,  $\triangle_n(\mathcal{C}) = 2^n$  for  $n \leq V$  and  $\triangle_n(\mathcal{C}) < 2^n$  for n > V for some constant V.

What if  $\Delta_n(\mathcal{C}) = 2^n$  for all  $n \geq 1$ ? That means we can always find  $\{x_1, \ldots, x_n\}$  such that  $C \in \mathcal{C}$  can pick out any subset of it: " $\mathcal{C}$  shatters  $\{x_1, \ldots, x_n\}$ ". In some sense, we do not learn anything.

**Definition 8.1.** If  $V < \infty$ , then  $\mathcal{C}$  is called a VC class. V is called VC dimension of  $\mathcal{C}$ .

Sauer's lemma states the following:

## Lemma 8.1.

$$\forall \{x_1, \ldots, x_n\}, \quad \triangle_n(\mathcal{C}, x_1, \ldots, x_n) \leq \left(\frac{en}{V}\right)^V \text{ for } n \geq V.$$

Hence, C will pick out only very few subsets out of  $2^n$  (because  $\left(\frac{e^n}{V}\right)^V \sim n^V$ ).

**Lemma 8.2.** The number  $\triangle_n(\mathcal{C}, x_1, \dots, x_n)$  of subsets picked out by  $\mathcal{C}$  is bounded by the number of subsets shattered by  $\mathcal{C}$ .

Identify

$$\mathcal{C} := \{ C \cap \{x_1, \dots, x_n\} : C \in \mathcal{C} \}$$

i.e. restrict C on  $\{x_1, \ldots, x_n\}$ .

We will say that  $\mathcal{C}$  is hereditary if and only if whenever  $C \in \mathcal{C}$ , then any  $B \subseteq C$  is in  $\mathcal{C}$ . If  $\mathcal{C}$  is hereditary, Lemma is obvious. Otherwise, we will transform  $\mathcal{C} \to \mathcal{C}'$ , hereditary, in such a way that card  $\mathcal{C} = \operatorname{card} \mathcal{C}'$ , i.e. the number of shattered subsets can only decrease.

card 
$$C = \text{card } C' = \#(\text{shattered by } C') \leq \#(\text{shattered by } C)$$

Define

$$T_i(C) = \begin{cases} C - \{x_i\} & \text{if } C - \{x_i\} \text{ is not in } C \\ C & \text{otherwise} \end{cases}$$

Define

$$T_i(\mathcal{C}) = \{T_i(C) : C \in \mathcal{C}\}.$$

Note that card  $T_i(\mathcal{C}) = \text{card } \mathcal{C}$ . Moreover, if C is shattered by  $T_i(\mathcal{C})$ , it is shattered by  $\mathcal{C}$ . Indeed, if  $x_i \notin C$ , then obvious. Otherwise, let  $B \in T_i(\mathcal{C})$ , but  $B \in \mathcal{C}$ . Since  $x_i \in B$ ,  $x_i$  was not removed from B. This means that  $B - \{x_i\} \in \mathcal{C}$ . This proves that  $\mathcal{C}$  shatters C. Let

$$T = T_1 \circ \ldots \circ T_n$$

and consider  $T^k(\mathcal{C})$  until  $T^{k+1}(\mathcal{C}) = T^k(\mathcal{C})$ . This will happen because if  $T^{k+1}(\mathcal{C}) \neq T^k(\mathcal{C})$ , it means that for some C and some i, point  $x_i$  was removed from C,  $T_i(C) = C - \{x_i\}$ ,  $k \leq 2^n \cdot n$ .

 $T(T^k(\mathcal{C})) = T^k(\mathcal{C})$  implies that  $T^k(\mathcal{C})$  is hereditary because for any  $C \in T^k(\mathcal{C})$  and any  $x_i \in C$ ,  $C - \{x_i\}$  is also in  $T^k(\mathcal{C})$ . This is our  $\mathcal{C}' = T^k(\mathcal{C})$ .

Corollary 8.1. If  $V < \infty$ , then

$$\triangle_n(\mathcal{C}) \le \sum_{i=0}^{V} \binom{n}{i} \le \left(\frac{en}{V}\right)^V$$

Indeed, for arbitrary  $\{x_1, \ldots, x_n\}$ ,

$$\triangle_n(\mathcal{C}, x_1, \dots, x_n) \le \text{card (shattered subsets of } \{x_1, \dots, x_n\})$$

$$\le \text{card (subsets of size } \le V)$$

$$= \sum_{i=1}^{V} \binom{n}{i}.$$

---

Recall the definition of VC-dimension. Consider some examples:

- $\mathcal{C} = \{(-\infty, a) \text{ and } (a, \infty) : a \in \mathbb{R}\}. \ VC(\mathcal{C}) = 2.$
- $C = \{(a, b) \cup (c, d)\}. \ VC(C) = 4.$
- $f_1, \ldots, f_d : \mathcal{X} \to \mathbb{R}, \ \mathcal{C} = \{ \{x : \sum_{k=1}^d \alpha_k f_k(x) > 0 \} : \alpha_1, \ldots, \alpha_d \in \mathbb{R} \}$

**Theorem 9.1.** VC(C) in the last example above is at most d.

*Proof.* Observation: For any  $\{x_1, \ldots, x_{d+1}\}$  if we cannot shatter  $\{x_1, \ldots, x_{d+1}\} \longleftrightarrow \exists I \subseteq \{1 \ldots d+1\}$  s.t. we cannot pick out  $\{x_i, i \in I\}$ . If we can pick out  $\{x_i, i \in I\}$ , then for some  $C \in \mathcal{C}$  there are  $\alpha_1, \ldots, \alpha_d$  s.t.  $\sum_{k=1}^d \alpha_k f_k(x) > 0$  for  $i \in I$  and  $\sum_{k=1}^d \alpha_k f_k(x) \le 0$  for  $i \notin I$ . Denote

$$\left(\sum_{k=1}^d \alpha_k f_k(x_1), \dots, \sum_{k=1}^d \alpha_k f_k(x_{d+1})\right) = F(\alpha) \in \mathbb{R}^{d+1}.$$

By linearity,

$$F(\alpha) = \sum_{k=1}^{d} \alpha_k \left( f_k(x_1), \dots, f(x_{d+1}) \right) = \sum_{k=1}^{d} \alpha_k F_k \subseteq H \subset \mathbb{R}^{d+1}$$

and H is a d-dim subspace. Hence,  $\exists \phi \neq 0, \ \phi \cdot h = 0, \forall h \in H \ (\phi \text{ orthogonal to } H)$ . Let  $I = \{i : \phi_i > 0\}$ , where  $\phi = (\phi_1, \dots, \phi_{d+1})$ . If  $I = \emptyset$  then take  $-\phi$  instead of  $\phi$  so that  $\phi$  has positive coordinates.

Claim: We cannot pick out  $\{x_i, i \in I\}$ . Suppose we can: then  $\exists \alpha_1, \ldots, \alpha_d$  s.t.  $\sum_{k=1}^d \alpha_k f_k(x_i) > 0$  for  $i \in I$  and  $\sum_{k=1}^d \alpha_k f_k(x_i) \leq 0$  for  $i \notin I$ . But  $\phi \cdot F(\alpha) = 0$  and so

$$\phi_1 \sum_{k=1}^d \alpha_k f_k(x_1) + \ldots + \phi_{d+1} \sum_{k=1}^d \alpha_k f_k(x_{d+1}) = 0.$$

Hence,

$$\sum_{i \in I} \phi_i \left( \sum_{k=1}^d \alpha_k f_k(x_i) \right) = \sum_{i \notin I} \underbrace{(-\phi_i)}_{\geq 0} \underbrace{\left( \sum_{k=1}^d \alpha_k f_k(x_i) \right)}_{<0}.$$

Contradiction.

• Half-spaces in 
$$\mathbb{R}^d$$
:  $\{\{\alpha_1 x_1 + \ldots + \alpha_d x_d + \alpha_{d+1} > 0\} : \alpha_1, \ldots, \alpha_{d+1} \in \mathbb{R}\}.$ 

By setting  $f_1 = x_1, \ldots, f_d = x_d, f_{d+1} = 1$ , we can use the previous result and therefore  $VC(\mathcal{C}) \leq d+1$  for half-spaces.

Reminder:  $\triangle_n(\mathcal{C}, x_1, \dots, x_n) = \operatorname{card}\{\{x_1, \dots, x_n\} \cap C : C \in \mathcal{C}\}.$ 

**Lemma 9.1.** If C and D are VC classes of sets,

- (1)  $C = \{C^c : C \in C\}$  is VC
- (2)  $C \cap D = \{C \cap D : C \in C, D \in D\}$  is VC
- (3)  $C \cup D = \{C \cup D : C \in C, D \in D\}$  is VC

*Proof.* (1) obvious - we can shatter  $x_1, \ldots, x_n$  by  $\mathcal{C}$  iff we can do the same by  $\mathcal{C}^c$ .

(2) By Sauer's Lemma,

$$\triangle_n(\mathcal{C} \cap \mathcal{D}, x_1, \dots, x_n) \le \triangle_n(\mathcal{C}, x_1, \dots, x_n) \triangle_n(\mathcal{C} \cap \mathcal{D}, x_1, \dots, x_n)$$

$$\le \left(\frac{en}{V_{\mathcal{C}}}\right)_{\mathcal{C}}^V \left(\frac{en}{V_{\mathcal{D}}}\right)_{\mathcal{D}}^V \le 2^n$$

for large enough n.

(3)  $(C \cup D) = (C^c \cap D^c)^c$ , and the result follows from (1) and (2).

**Example 1.** Decision trees on  $\mathbb{R}^d$  with linear decision rules:  $\{C_1 \cap \ldots C_\ell\}$  is VC and  $\bigcup_{\text{leaves}} \{C_1 \cap \ldots C_\ell\}$  is VC.

**Example 2.** Neural networks with depth  $\ell$  and binary leaves.

---

We are interested in bounding

$$\mathbb{P}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\mathbb{P}\left(C\right)\right|\geq t\right)$$

In Lecture 7 we hinted at Symmetrization as a way to deal with the unknown  $\mathbb{P}(C)$ .

**Lemma 10.1**(Symmetrization). If  $t \ge \sqrt{\frac{2}{n}}$ , then

$$\mathbb{P}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\mathbb{P}\left(C\right)\right|\geq t\right)\leq 2\mathbb{P}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\frac{1}{n}\sum_{i=1}^{n}I(X_{i}'\in C)\right|\geq t/2\right).$$

*Proof.* Suppose the event

$$\sup_{C \in \mathcal{C}} \left| \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C) - \mathbb{P}(C) \right| \ge t$$

occurs. Let  $X = (X_1, \dots, X_n) \in \{\sup_{C \in \mathcal{C}} \left| \frac{1}{n} \sum_{i=1}^n I(X_i \in C) - \mathbb{P}(C) \right| \ge t \}$ . Then

$$\exists C_X \text{ such that } \left| \frac{1}{n} \sum_{i=1}^n I(X_i \in C_X) - \mathbb{P}(C_X) \right| \ge t.$$

For a fixed C,

$$\mathbb{P}_{X'}\left(\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}'\in C)-\mathbb{P}\left(C\right)\right|\geq t/2\right) = \mathbb{P}\left(\left(\frac{1}{n}\sum_{i=1}^{n}I(X_{i}'\in C)-\mathbb{P}\left(C\right)\right)^{2}\geq t^{2}/4\right) \\
\leq \text{(by Chebyshev's Ineq)} \frac{4\mathbb{E}\left(\frac{1}{n}\sum_{i=1}^{n}I(X_{i}'\in C)-\mathbb{P}\left(C\right)\right)^{2}}{t^{2}} \\
= \frac{4}{n^{2}t^{2}}\sum_{i,j}\mathbb{E}\left(I(X_{i}'\in C)-\mathbb{P}\left(C\right)\right)\left(I(X_{j}'\in C)-\mathbb{P}\left(C\right)\right) \\
= \frac{4}{n^{2}t^{2}}\sum_{i=1}^{n}\mathbb{E}\left(I(X_{i}'\in C)-\mathbb{P}\left(C\right)\right)^{2} = \frac{4n\mathbb{P}\left(C\right)\left(1-\mathbb{P}\left(C\right)\right)}{n^{2}t^{2}}\leq \frac{1}{nt^{2}}\leq \frac{1}{2}$$

since we chose  $t \ge \sqrt{\frac{2}{n}}$ .

So,

$$\mathbb{P}_{X'}\left(\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}'\in C_{X})-\mathbb{P}\left(C_{X}\right)\right|\leq t/2\right)\geq 1/2$$

because  $C_X$  does not depend on X'. Assume that the event

$$\left| \frac{1}{n} \sum_{i=1}^{n} I(X_i' \in C_X) - \mathbb{P}(C_X) \right| \le t/2$$

occurs. Recall that

$$\left| \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C_X) - \mathbb{P}(C_X) \right| \ge t.$$

Hence, it must be that

$$\left| \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C_X) - \frac{1}{n} \sum_{i=1}^{n} I(X_i' \in C_X) \right| \ge t/2.$$

We conclude

$$\frac{1}{2} \leq \mathbb{P}_{X'} \left( \left| \frac{1}{n} \sum_{i=1}^{n} I(X_i' \in C_X) - \mathbb{P}(C_X) \right| \leq t/2 \right)$$

$$\leq \mathbb{P}_{X'} \left( \left| \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C_X) - \frac{1}{n} \sum_{i=1}^{n} I(X_i' \in C_X) \right| \geq t/2 \right).$$

Clearly,

$$\mathbb{P}_{X'}\left(\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C_{X})-\frac{1}{n}\sum_{i=1}^{n}I(X'_{i}\in C_{X})\right|\geq t/2\right)$$

$$\leq \mathbb{P}_{X'}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\frac{1}{n}\sum_{i=1}^{n}I(X'_{i}\in C)\right|\geq t/2\right).$$

Since indicators are 0, 1-valued,

$$\frac{1}{2}I\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\mathbb{P}\left(C\right)\right|\geq t\right)$$

$$\leq \mathbb{P}_{X'}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\frac{1}{n}\sum_{i=1}^{n}I(X'_{i}\in C)\right|\geq t/2\right).$$

Now, take expectation with respect to  $X_i$ 's to obtain

$$\mathbb{P}_{X}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\mathbb{P}\left(C\right)\right|\geq t\right)$$

$$\leq \mathbb{P}_{X,X'}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\frac{1}{n}\sum_{i=1}^{n}I(X'_{i}\in C)\right|\geq t/2\right).$$

**Theorem 10.1.** If  $VC(\mathcal{C}) = V$ , then

$$\mathbb{P}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\mathbb{P}\left(C\right)\right|\geq t\right)\leq 4\left(\frac{2en}{V}\right)^{V}e^{-\frac{nt^{2}}{8}}.$$

Proof.

$$2\mathbb{P}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C)-\frac{1}{n}\sum_{i=1}^{n}I(X_{i}'\in C)\right|\geq t/2\right)$$

$$=2\mathbb{P}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}\left(I(X_{i}\in C)-I(X_{i}'\in C)\right)\right|\geq t/2\right)$$

$$=2\mathbb{E}_{X,X'}\mathbb{P}_{\varepsilon}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}\left(I(X_{i}\in C)-I(X_{i}'\in C)\right)\right|\geq t/2\right).$$

The first equality is due to the fact that  $X_i$  and  $X_i'$  are i.i.d., and so switching their names (i.e. introducing random signs  $\varepsilon_i$ ,  $\mathbb{P}(\varepsilon_i = \pm 1) = 1/2$ ) does not have any effect. In the last line, it's important to see that the probability is taken with respect to  $\varepsilon_i$ 's, while  $X_i$  and  $X_i'$ 's are fixed.

Let

$$a(C) = (I(X_1 \in C) - I(X_1' \in C), \dots, I(X_n \in C) - I(X_n' \in C)).$$

By Sauer's lemma,

$$\triangle_{2n}\left(\mathcal{C},X_1,\ldots,X_n,X_1',\ldots,X_n'\right) \leq \left(\frac{2en}{V}\right)^V.$$

In other words, any class will be equivalent to one of  $C_1, \ldots, C_N$  on the data, where  $N \leq \left(\frac{2en}{V}\right)^V$ . Hence,

$$2\mathbb{E}_{X,X'}\mathbb{P}_{\varepsilon}\left(\sup_{C\in\mathcal{C}}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}\left(I(X_{i}\in C)-I(X_{i}'\in C)\right)\right|\geq t/2\right)$$

$$=2\mathbb{E}_{X,X'}\mathbb{P}_{\varepsilon}\left(\sup_{1\leq k\leq N}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}\left(I(X_{i}\in C_{k})-I(X_{i}'\in C_{k})\right)\right|\geq t/2\right)$$

$$=2\mathbb{E}_{X,X'}\mathbb{P}_{\varepsilon}\left(\bigcup_{k=1}^{N}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}\left(I(X_{i}\in C_{k})-I(X_{i}'\in C_{k})\right)\right|\geq t/2\right)$$

$$\leq 2\mathbb{E}\sum_{k=1}^{n}\mathbb{P}_{\varepsilon}\left(\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}\left(I(X_{i}\in C_{k})-I(X_{i}'\in C_{k})\right)\right|\geq t/2\right)$$

$$\leq 2\mathbb{E}\sum_{k=1}^{n}2\exp\left(-\frac{-n^{2}t^{2}}{8\sum_{i=1}^{n}\left(I(X_{i}\in C)-I(X_{i}'\in C)\right)^{2}}\right)$$

$$\leq 2\mathbb{E}\sum_{k=1}^{n}2\exp\left(-\frac{-n^{2}t^{2}}{8n}\right)\leq 2\left(\frac{2en}{V}\right)^{V}2e^{-\frac{nt^{2}}{8}},$$

where the first inequality above follows from the Hoeffding's inequality (see Lecture 7).

---

Last time we proved the Pessimistic VC inequality:

$$\mathbb{P}\left(\sup_{C} \left| \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C) - \mathbb{P}(C) \right| \ge t \right) \le 4 \left( \frac{2en}{V} \right)^{V} e^{-\frac{nt^2}{8}},$$

which can be rewritten with

$$t = \sqrt{\frac{8}{n} \left( \log 4 + V \log \frac{2en}{V} + u \right)}$$

as

$$\mathbb{P}\left(\sup_{C} \left| \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C) - \mathbb{P}(C) \right| \le \sqrt{\frac{8}{n} \left(\log 4 + V \log \frac{2en}{V} + u\right)} \right) \ge 1 - e^{-u}.$$

Hence, the rate is  $\sqrt{\frac{V \log n}{n}}$ . In this lecture we will prove Optimistic VC inequality, which will improve on this rate when  $\mathbb{P}(C)$  is small.

As before, we have pairs  $(X_i, Y_i)$ ,  $Y_i = \pm 1$ . These examples are labeled according to some unknown  $C_0$  such that Y = 1 if  $X = C_0$  and Y = 0 if  $X \notin C_0$ .

Let  $C = \{C : C \subseteq \mathcal{X}\}$ , a set of classifiers. C makes a mistake if

$$X \in C \setminus C_0 \cup C_0 \setminus C = C \triangle C_0.$$

Similarly to last lecture, we can derive bounds on

$$\sup_{C} \left| \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C \triangle C_0) - \mathbb{P}(C \triangle C_0) \right|,$$

where  $\mathbb{P}(C\triangle C_0)$  is the generalization error.

Let  $C' = \{C \triangle C_0 : C \in C\}$ . One can prove that  $VC(C') \leq VC(C)$  and  $\Delta_n(C', X_1, \dots, X_n) \leq \Delta_n(C, X_1, \dots, X_n)$ .

By Hoeffding-Chernoff, if  $\mathbb{P}\left(C\right) \leq \frac{1}{2}$ ,

$$\mathbb{P}\left(\mathbb{P}\left(C\right) - \frac{1}{n}\sum_{i=1}^{n}I(X_{i} \in C) \leq \sqrt{\frac{2\mathbb{P}\left(C\right)t}{n}}\right) \geq 1 - e^{-t}.$$

**Theorem 11.1** (Optimistic VC inequality).

$$\mathbb{P}\left(\sup_{C} \frac{\mathbb{P}\left(C\right) - \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C)}{\sqrt{\mathbb{P}\left(C\right)}} \ge t\right) \le 4\left(\frac{2en}{V}\right)^{V} e^{-\frac{nt^2}{4}}.$$

*Proof.* Let C be fixed. Then

$$\mathbb{P}_{(X_i')}\left(\frac{1}{n}\sum_{i=1}^n I(X_i' \in C) \ge \mathbb{P}(C)\right) \ge \frac{1}{4}$$

whenever  $\mathbb{P}(C) \geq \frac{1}{n}$ . Indeed,  $\mathbb{P}(C) \geq \frac{1}{n}$  since  $\sum_{i=1}^{n} I(X_i' \in C) \geq n \mathbb{P}(C) \geq 1$ . Otherwise  $\mathbb{P}(\sum_{i=1}^{n} I(X_i' \in C) = 0) = \prod_{i=1}^{n} \mathbb{P}(X_i' \notin C) = (1 - \mathbb{P}(C))^n$  can be as close to 0 as we want. Similarly to the proof of the previous lecture, let

$$(X_i) \in \left\{ \sup_{C} \frac{\mathbb{P}(C) - \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C)}{\sqrt{\mathbb{P}(C)}} \ge t \right\}.$$

Hence, there exists  $C_X$  such that

$$\frac{\mathbb{P}(C) - \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C)}{\sqrt{\mathbb{P}(C)}} \ge t.$$

Exercise 1. Show that if

$$\frac{\mathbb{P}(C_X) - \frac{1}{n} \sum_{i=1}^{n} I(X_i \in C_X)}{\sqrt{\mathbb{P}(C_X)}} \ge t$$

and

$$\frac{1}{n}\sum_{i=1}^{n}I(X_{i}'\in C_{X})\geq\mathbb{P}\left(C_{X}\right),$$

then

$$\frac{\frac{1}{n}\sum_{i=1}^{n}I(X_{i}'\in C_{X})-\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C_{X})}{\sqrt{\frac{1}{n}\sum_{i=1}^{n}I(X_{i}\in C_{X})+\frac{1}{n}\sum_{i=1}^{n}I(X_{i}'\in C_{X})}}\geq \frac{t}{\sqrt{2}}.$$

Hint: use the fact that  $\phi(s) = \frac{s-a}{\sqrt{s}} = \sqrt{s} - \frac{s}{\sqrt{s}}$  is increasing in s.

From the above exercise it follows that

$$\frac{1}{4} \leq \mathbb{P}_{(X_i')} \left( \frac{1}{n} \sum_{i=1}^n I(X_i' \in C_X) \geq \mathbb{P}(C_X) \right) 
\leq \mathbb{P}_{(X_i')} \left( \frac{\frac{1}{n} \sum_{i=1}^n I(X_i' \in C_X) - \frac{1}{n} \sum_{i=1}^n I(X_i \in C_X)}{\sqrt{\frac{1}{n} \sum_{i=1}^n I(X_i \in C_X) + \frac{1}{n} \sum_{i=1}^n I(X_i' \in C_X)}} \geq t \right)$$

Since indicator is 0, 1-valued,

$$\frac{1}{4}I\left(\sup_{C} \frac{\mathbb{P}(C_{X}) - \frac{1}{n}\sum_{i=1}^{n}I(X_{i} \in C_{X})}{\sqrt{\mathbb{P}(C_{X})}} \ge t\right) 
\le \mathbb{P}_{(X'_{i})}\left(\frac{\frac{1}{n}\sum_{i=1}^{n}I(X'_{i} \in C_{X}) - \frac{1}{n}\sum_{i=1}^{n}I(X_{i} \in C_{X})}{\sqrt{\frac{1}{n}\sum_{i=1}^{n}I(X_{i} \in C_{X}) + \frac{1}{n}\sum_{i=1}^{n}I(X'_{i} \in C_{X})}} \ge t\right) 
\le \mathbb{P}_{(X'_{i})}\left(\sup_{C} \frac{\frac{1}{n}\sum_{i=1}^{n}I(X'_{i} \in C) - \frac{1}{n}\sum_{i=1}^{n}I(X_{i} \in C)}{\sqrt{\frac{1}{n}\sum_{i=1}^{n}I(X_{i} \in C) + \frac{1}{n}\sum_{i=1}^{n}I(X'_{i} \in C)}} \ge t\right).$$

Hence,

$$\frac{1}{4}\mathbb{P}\left(\sup_{C} \frac{\mathbb{P}(C_X) - \frac{1}{n}\sum_{i=1}^{n}I(X_i \in C_X)}{\sqrt{\mathbb{P}(C_X)}} \ge t\right)$$

$$\le \mathbb{P}\left(\sup_{C} \frac{\frac{1}{n}\sum_{i=1}^{n}I(X_i' \in C) - \frac{1}{n}\sum_{i=1}^{n}I(X_i \in C)}{\sqrt{\frac{1}{n}\sum_{i=1}^{n}I(X_i \in C) + \frac{1}{n}\sum_{i=1}^{n}I(X_i' \in C)}} \ge t\right)$$

$$= \mathbb{EP}_{\varepsilon}\left(\sup_{C} \frac{\frac{1}{n}\sum_{i=1}^{n}\varepsilon_i\left(I(X_i' \in C) - I(X_i \in C)\right)}{\sqrt{\frac{1}{n}\sum_{i=1}^{n}I(X_i \in C) + \frac{1}{n}\sum_{i=1}^{n}I(X_i' \in C)}} \ge t\right)$$

There exist  $C_1, \ldots, C_N$ , with  $N \leq \triangle_{2n}(\mathcal{C}, X_1, \ldots, X_n, X_1', \ldots, X_n')$ . Therefore,

$$\mathbb{EP}_{\varepsilon}\left(\sup_{C} \frac{\frac{1}{n}\sum_{i=1}^{n} \varepsilon_{i} \left(I(X_{i}' \in C) - I(X_{i} \in C)\right)}{\sqrt{\frac{1}{n}\sum_{i=1}^{n} I(X_{i} \in C) + \frac{1}{n}\sum_{i=1}^{n} I(X_{i}' \in C)}} \ge t\right)$$

$$= \mathbb{EP}_{\varepsilon}\left(\bigcup_{k \le N} \left\{\frac{\frac{1}{n}\sum_{i=1}^{n} \varepsilon_{i} \left(I(X_{i}' \in C_{k}) - I(X_{i} \in C_{k})\right)}{\sqrt{\frac{1}{n}\sum_{i=1}^{n} I(X_{i} \in C_{k}) + \frac{1}{n}\sum_{i=1}^{n} I(X_{i}' \in C_{k})}} \ge t\right\}\right)$$

$$\leq \mathbb{E}\sum_{k=1}^{N} \mathbb{P}_{\varepsilon}\left(\frac{\frac{1}{n}\sum_{i=1}^{n} \varepsilon_{i} \left(I(X_{i}' \in C_{k}) - I(X_{i} \in C_{k})\right)}{\sqrt{\frac{1}{n}\sum_{i=1}^{n} I(X_{i} \in C_{k}) + \frac{1}{n}\sum_{i=1}^{n} I(X_{i}' \in C_{k})}} \ge t\right)$$

$$\leq \mathbb{E}\sum_{k=1}^{N} \mathbb{P}_{\varepsilon}\left(\frac{1}{n}\sum_{i=1}^{n} \varepsilon_{i} \left(I(X_{i}' \in C_{k}) - I(X_{i} \in C_{k})\right) \ge t\sqrt{\frac{1}{n}\sum_{i=1}^{n} I(X_{i} \in C_{k}) + \frac{1}{n}\sum_{i=1}^{n} I(X_{i}' \in C_{k})}\right)$$

The last expression can be upper-bounded by Hoeffding's inequality as follows:

$$\mathbb{E} \sum_{k=1}^{N} \mathbb{P}_{\varepsilon} \left( \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} \left( I(X_{i}' \in C_{k}) - I(X_{i} \in C_{k}) \right) \ge t \sqrt{\frac{1}{n} \sum_{i=1}^{n} \left( I(X_{i} \in C_{k}) + I(X_{i}' \in C_{k}) \right)} \right)$$

$$\leq \mathbb{E} \sum_{k=1}^{N} \exp \left( -\frac{t^{2} \frac{1}{n} \sum_{i=1}^{n} \left( I(X_{i} \in C_{k}) + I(X_{i}' \in C_{k}) \right)}{\frac{1}{n^{2}} 2 \sum \left( I(X_{i}' \in C_{k}) - I(X_{i} \in C_{k}) \right)^{2}} \right)$$

since upper sum in the exponent is bigger than the lower sum (compare term-by-term)

$$\leq \mathbb{E} \sum_{k=1}^{N} e^{-\frac{nt^2}{2}} \leq \left(\frac{2en}{V}\right)^{V} e^{-\frac{nt^2}{2}}.$$

---

## VC-subgraph classes of functions

Let  $\mathcal{F} = \{f : \mathcal{X} \mapsto \mathbb{R}\}$  and

$$C_f = \{(x,t) \in \mathcal{X} \times \mathbb{R} : 0 \le t \le f(x) \text{ or } f(x) \le t \le 0\}.$$

Define class of sets  $C = \{C_f : f \in \mathcal{F}\}.$ 

**Definition 12.1.** If C is a VC class of sets, then F is VC-subgraph class of functions and, by definition, VC(F) = VC(C).

Note that equivalent definition of  $C_f$  is

$$C'_f = \{(x, t) \in \mathcal{X} \times \mathbb{R} : f(x) \ge t\}.$$

**Example 1.**  $C = \{C \subseteq \mathcal{X}\}, \ \mathcal{F}(C) = \{I(X \in C) : C \in C\}.$  Then  $\mathcal{F}(C)$  is VC-subgraph class if and only if C is a VC class of sets.

**Example 2.** Assume d functions are fixed:  $\{f_1, \ldots, f_d\} : \mathcal{X} \mapsto \mathbb{R}$ . Let

$$\mathcal{F} = \left\{ \sum_{i=1}^{d} \alpha_i f_i(x) : \alpha_1, \dots, \alpha_d \in \mathbb{R} \right\}.$$

Then  $VC(\mathcal{F}) \leq d+1$ . To prove this, it's easier to use the second definition.

## Packing and covering numbers

Let  $f, g \in \mathcal{F}$  and assume we have a distance function d(f, g).

**Example 3.** If  $X_1, \ldots, X_n$  are data points, then

$$d_1(f,g) = \frac{1}{n} \sum_{i=1}^{n} |f(X_i) - g(X_i)|$$

and

$$d_2(f,g) = \left(\frac{1}{n}\sum_{i=1}^n (f(X_i) - g(X_i))^2\right)^{1/2}.$$

**Definition 12.2.** Given  $\varepsilon > 0$  and  $f_1, \ldots, f_N \in \mathcal{F}$ , we say that  $f_1, \ldots, f_N$  are  $\varepsilon$ -separated if  $d(f_i, f_j) > \varepsilon$  for any  $i \neq j$ .

**Definition 12.3.** The  $\varepsilon$ -packing number,  $\mathcal{D}(\mathcal{F}, \varepsilon, d)$ , is the maximal cardinality of an  $\varepsilon$ -separated set.

Note that  $\mathcal{D}(\mathcal{F}, \varepsilon, d)$  is decreasing in  $\varepsilon$ .

**Definition 12.4.** Given  $\varepsilon > 0$  and  $f_1, \ldots, f_N \in \mathcal{F}$ , we say that the set  $f_1, \ldots, f_N$  is an  $\varepsilon$ -cover of  $\mathcal{F}$  if for any  $f \in \mathcal{F}$ , there exists  $1 \leq i \leq N$  such that  $d(f, f_i) \leq \varepsilon$ .

**Definition 12.5.** The  $\varepsilon$ -covering number,  $\mathcal{N}(\mathcal{F}, \varepsilon, d)$ , is the minimal cardinality of an  $\varepsilon$ -cover of  $\mathcal{F}$ .

## Lemma 12.1.

$$\mathcal{D}(\mathcal{F}, 2\varepsilon, d) \leq \mathcal{N}(\mathcal{F}, \varepsilon, d) \leq \mathcal{D}(\mathcal{F}, \varepsilon, d).$$

*Proof.* To prove the first inequality, assume that  $\mathcal{D}(\mathcal{F}, 2\varepsilon, d) > \mathcal{N}(\mathcal{F}, \varepsilon, d)$ . Let the packing corresponding to the packing number  $\mathcal{D}(\mathcal{F}, 2\varepsilon, d) = D$  be  $f_1, \ldots, f_D$ . Let the covering corresponding to the covering number  $\mathcal{N}(\mathcal{F}, \varepsilon, d) = N$  be  $f'_1, \ldots, f'_N$ . Since D > N, there exist  $f_i$  and  $f_j$  such that for some  $f'_k$ 

$$d(f_i, f_k') \le \varepsilon$$
 and  $d(f_j, f_k') \le \varepsilon$ .

Therefore, by triangle inequality,  $d(f_i, f_j) \leq 2\varepsilon$ , which is a contradiction.

To prove the second inequality, assume  $f_1, \ldots, f_D$  is an optimal packing. For any  $f \in \mathcal{F}$ ,  $f_1, \ldots, f_D$ , f would also be  $\varepsilon$ -packing if  $d(f, f_i) > \varepsilon$  for all i. Since  $f_1, \ldots, f_D$  is optimal, this cannot be true, and, therefore, for any  $f \in \mathcal{F}$  there exists  $f_i$  such that  $d(f, f_i) \leq \varepsilon$ . Hence  $f_1, \ldots, f_D$  is also a cover. Hence,  $\mathcal{N}(\mathcal{F}, \varepsilon, d) \leq \mathcal{D}(\mathcal{F}, \varepsilon, d)$ .

**Example 4.** Consider the  $L_1$ -ball  $\{x \in \mathbb{R}^d, |x| \leq 1\} = B_1(0)$  and  $d(x,y) = |x-y|_1$ . Then

$$\mathcal{D}(B_1(0), \varepsilon, d) \le \left(\frac{2+\varepsilon}{\varepsilon}\right)^d \le \left(\frac{3}{\varepsilon}\right)^d$$
,

where  $\varepsilon \leq 1$ . Indeed, let  $f_1, \ldots, f_D$  be optimal  $\varepsilon$ -packing. Then the volume of the ball with  $\varepsilon/2$ -fattening (so that the center of small balls fall within the boundary) is

$$Vol\left(1+\frac{\varepsilon}{2}\right) = C_d\left(1+\frac{\varepsilon}{2}\right)^d.$$

Moreover, the volume of each of the small balls

$$Vol\left(\frac{\varepsilon}{2}\right) = C_d\left(\frac{\varepsilon}{2}\right)^d$$

and the volume of all the small balls is

$$DC_d\left(\frac{\varepsilon}{2}\right)^d$$
.

Therefore,

$$D \le \left(\frac{2+\varepsilon}{\varepsilon}\right)^d.$$

**Definition 12.6.**  $\log \mathcal{N}(\mathcal{F}, \varepsilon, d)$  is called metric entropy.

For example,  $\log \mathcal{N}(B_1(0), \varepsilon, d) \leq d \log \frac{3}{\varepsilon}$ .

---

**Theorem 13.1.** Assume  $\mathcal{F}$  is a VC-subgraph class and  $VC(\mathcal{F}) = V$ . Suppose  $-1 \leq f(x) \leq 1$  for all  $f \in \mathcal{F}$  and  $x \in \mathcal{X}$ . Let  $x_1, \ldots, x_n \in \mathcal{X}$  and define  $d(f, g) = \frac{1}{n} \sum_{i=1}^{n} |f(x_i) - g(x_i)|$ . Then

$$\mathcal{D}(\mathcal{F}, \varepsilon, d) \le \left(\frac{8e}{\varepsilon} \log \frac{7}{\varepsilon}\right)^V.$$

(which is  $\leq \left(\frac{K}{\varepsilon}\right)^{V+\delta}$  for some  $\delta$ .)

*Proof.* Let  $m = \mathcal{D}(\mathcal{F}, \varepsilon, d)$  and  $f_1, \ldots, f_m$  be  $\varepsilon$ -separated, i.e.

$$\frac{1}{n}\sum_{i=1}^{n}|f_r(x_i)-f_\ell(x_i)|>\varepsilon.$$

Let  $(z_1, t_1), \ldots, (z_k, t_k)$  be constructed in the following way:  $z_i$  is chosen uniformly from  $x_1, \ldots, x_n$  and  $t_i$  is uniform on [-1, 1].

Consider  $f_r$  and  $f_\ell$  from the  $\varepsilon$ -packing. Let  $C_{f_r}$  and  $C_{f_\ell}$  be subgraphs of  $f_r$  and  $f_\ell$ . Then

 $\mathbb{P}\left(C_{f_r} \text{ and } C_{f_\ell} \text{ pick out different subsets of } (z_1, t_1), \ldots, (z_k, t_k)\right)$ 

- $= \mathbb{P} \left( \text{At least one point } (z_i, t_i) \text{ is picked by } C_{f_r} \text{ or } C_{f_\ell} \text{ but not picked by the other} \right)$
- $=1-\mathbb{P}\left(\text{All points }(z_{i},t_{i})\text{ are picked either by both or by none}\right)$
- $= 1 \mathbb{P}((z_i, t_i) \text{ is picked either by both or by none})^k$

Since  $z_i$  is drawn uniformly from  $x_1, \ldots, x_n$ ,

 $\mathbb{P}\left((z_1,t_1) \text{ is picked by both } C_{f_r},C_{f_\ell} \text{ or by neither}\right)$ 

$$= \frac{1}{n} \sum_{i=1}^{n} \mathbb{P}\left((x_i, t_1) \text{ is picked by both } C_{f_r}, C_{f_\ell} \text{ or by neither}\right)$$

$$= \frac{1}{n} \sum_{i=1}^{n} \left(1 - \frac{1}{2} |f_r(x_i) - f_\ell(x_i)|\right)$$

$$=1-\frac{1}{2}\frac{1}{n}\sum_{i=1}^{n}|f_r(x_i)-f_{\ell}(x_i)|$$

$$=1-\frac{1}{2}d(f_r,f_{\ell}) \le 1-\varepsilon/2 \le e^{-\varepsilon/2}$$


Substituting,

 $\mathbb{P}(C_{f_r} \text{ and } C_{f_\ell} \text{ pick out different subsets of } (z_1, t_1), \dots, (z_k, t_k))$   $= 1 - \mathbb{P}((z_1, t_1) \text{ is picked by both } C_{f_r}, C_{f_\ell} \text{ or by neither})^k$   $\geq 1 - (e^{-\varepsilon/2})^k$   $= 1 - e^{-k\varepsilon/2}$ 

There are  $\binom{m}{2}$  ways to choose  $f_r$  and  $f_\ell$ , so

 $\mathbb{P}\left(\text{All pairs } C_{f_r} \text{ and } C_{f_\ell} \text{ pick out different subsets of } (z_1, t_1), \dots, (z_k, t_k)\right) \geq 1 - \binom{m}{2} e^{-k\varepsilon/2}.$ 

What k should we choose so that  $1 - {m \choose 2} e^{-k\varepsilon/2} > 0$ ? Choose

$$k > \frac{2}{\varepsilon} \log \binom{m}{2}.$$

Then there exist  $(z_1, t_1), \ldots, (z_k, t_k)$  such that all  $C_{f_\ell}$  pick out different subsets. But  $\{C_f : f \in \mathcal{F}\}$  is VC, so by Sauer's lemma, we can pick out at most  $\left(\frac{ek}{V}\right)^V$  out of these k points. Hence,  $m \leq \left(\frac{ek}{V}\right)^V$  as long as  $k > \frac{2}{\varepsilon} \log {m \choose 2}$ . The latter holds for  $k = \frac{2}{\varepsilon} \log m^2$ . Therefore,

$$m \le \left(\frac{e}{V}\frac{2}{\varepsilon}\log m^2\right)^V = \left(\frac{4e}{V\varepsilon}\log m\right)^V,$$

where  $m = \mathcal{D}(\mathcal{F}, \varepsilon, d)$ . Hence, we get

$$m^{1/V} \le \frac{4e}{\varepsilon} \log m^{1/V}$$

and defining  $m^{1/V} = s$ ,

$$s \le \frac{4e}{\varepsilon} \log s$$
.

Note that  $\frac{s}{\log s}$  is increasing for  $s \geq e$  and so for large enough s, the inequality will be violated. We now check that the inequality is violated for  $s' = \frac{8e}{\varepsilon} \log \frac{7}{\varepsilon}$ . Indeed, one can show that

$$\frac{4e}{\varepsilon}\log\left(\frac{7}{\varepsilon}\right)^2 > \frac{4e}{\varepsilon}\log\left(\frac{8e}{\varepsilon}\log\frac{7}{\varepsilon}\right)$$

since

$$\frac{49}{8e\varepsilon} > \log \frac{7}{\epsilon}$$
.

Hence,  $m^{1/V} = s \le s'$  and, thus,

$$\mathcal{D}(\mathcal{F}, \varepsilon, d) \le \left(\frac{8e}{\varepsilon} \log \frac{7}{\varepsilon}\right)^V.$$

---

For  $f \in F \subseteq [-1,1]^n$ , define  $R(f) = \frac{1}{n} \sum_{i=1}^n \varepsilon_i f_i$ . Let  $d(f,g) := \left(\frac{1}{n} \sum_{i=1}^n (f_i - g_i)^2\right)^{1/2}$ .

Theorem 14.1.

$$\mathbb{P}\left(\forall f \in F, R(f) \leq \frac{2^{9/2}}{\sqrt{n}} \int_0^{d(0,f)} \log^{1/2} \mathcal{D}(F,\varepsilon,d) d\varepsilon + 2^{7/2} d(0,f) \sqrt{\frac{u}{n}}\right) \geq 1 - e^{-u}$$

for anyu > 0.

*Proof.* Without loss of generality, assume  $0 \in F$ .

Kolmogorov's chaining techniquedefine a sequence of subsets

$$\{0\} = F_0 \subseteq F_1 \ldots \subseteq F_j \subseteq \ldots \subseteq F$$

where  $F_j$  is defined such that

- (1)  $\forall f, g \in F_i, d(f, g) > 2^{-j}$
- (2)  $\forall f \in F$ , we can find  $g \in F_j$  such that  $d(f,g) \leq 2^{-j}$

How to construct  $F_{j+1}$  if we have  $F_j$ :

- $F_{j+1} := F_j$
- Find  $f \in F$ ,  $d(f,g) > 2^{-(j+1)}$  for all  $g \in F_{j+1}$
- Repeat until you cannot find such f

Define projection  $\pi_j: F \mapsto F_j$  as follows: for  $f \in F$  find  $g \in F_j$  with  $d(f,g) \leq 2^{-j}$  and set  $\pi_j(f) = g$ .

For any  $f \in F$ ,

$$f = \pi_0(f) + (\pi_1(f) - \pi_0(f)) + (\pi_2(f) - \pi_1(f)) \dots$$
$$= \sum_{j=1}^{\infty} (\pi_j(f) - \pi_{j-1}(f))$$

Moreover,

$$d(\pi_{j-1}(f), \pi_j(f)) \le d(\pi_{j-1}(f), f) + d(f, \pi_j(f))$$
  
$$\le 2^{-(j-1)} + 2^{-j} = 3 \cdot 2^{-j} \le 2^{-j+2}$$

Define the links

$$L_{j-1,j} = \{ f - g : f \in F_j, g \in F_{j-1}, d(f,g) \le 2^{-j+2} \}.$$

Since R is linear,  $R(f) = \sum_{j=1}^{\infty} R(\pi_j(f) - \pi_{j-1}(f))$ . We first show how to control R on the links. Assume  $\ell \in L_{j-1,j}$ . Then by Hoeffding's inequality

$$\mathbb{P}\left(\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}\ell_{i} \geq t\right) \leq \exp\left(-\frac{t^{2}}{2\sum\frac{1}{n^{2}}\ell_{i}^{2}}\right)$$
$$= \exp\left(-\frac{nt^{2}}{2\frac{1}{n}\sum_{i=1}^{n}\ell_{i}^{2}}\right)$$
$$\leq \exp\left(-\frac{nt^{2}}{2\cdot 2^{-2j+4}}\right)$$

Note that

$$\operatorname{card} L_{j-1,j} \le \operatorname{card} F_{j-1} \cdot \operatorname{card} F_j \le (\operatorname{card} F_j)^2.$$

$$\mathbb{P}\left(\forall \ell \in L_{j-1,j}, R(\ell) = \frac{1}{n} \sum_{i=1}^{n} \varepsilon_i \ell_i \le t\right) \ge 1 - (\operatorname{card} F_j)^2 e^{-\frac{nt^2}{2 \cdot 2^{-2j+5}}}$$
$$= 1 - \frac{1}{(\operatorname{card} F_j)^2} e^{-u}$$

after changing the variable such that

$$t = \sqrt{\frac{2^{-2j+5}}{n} \left( 4 \log(\text{card}F_j) + u \right)} \le \sqrt{\frac{2^{-2j+5}}{n}} 4 \log(\text{card}F_j) + \sqrt{\frac{2^{-2j+5}}{n}} u.$$

Hence.

$$\mathbb{P}\left(\forall \ell \in L_{j-1,j}, R(\ell) \le \frac{2^{7/2}2^{-j}}{\sqrt{n}} \log^{1/2}(\operatorname{card}F_j) + 2^{5/2}2^{-j}\sqrt{\frac{u}{n}}\right) \ge 1 - \frac{1}{(\operatorname{card}F_j)^2}e^{-u}.$$

If  $F_{j-1} = F_j$  then by definition  $\pi_{j-1}(f) = \pi_f$  and  $L_{j-1,j} = \{0\}$ .

By union bound for all steps,

$$\mathbb{P}\left(\forall j \ge 1, \forall \ell \in L_{j-1,j}, R(\ell) \le \frac{2^{7/2}2^{-j}}{\sqrt{n}} \log^{1/2}(\operatorname{card}F_j) + 2^{5/2}2^{-j}\sqrt{\frac{u}{n}}\right) \\
\ge 1 - \sum_{j=1}^{\infty} \frac{1}{(\operatorname{card}F_j)^2} e^{-u} \\
\ge 1 - \left(\frac{1}{2^2} + \frac{1}{3^2} + \frac{1}{4^2}\right) e^{-u} \\
= 1 - (\pi^2/6 - 1)e^{-u} \ge 1 - e^{-u}$$

Recall that  $R(f) = \sum_{j=1}^{\infty} R(\pi_j(f) - \pi_{j-1}(f))$ . If f is close to  $0, -2^{k+1} < d(0, f) \le 2^{-k}$ . Find such a k. Then  $\pi_0(f) = \ldots = \pi_k(f) = 0$  and so

$$R(f) = \sum_{j=k+1}^{\infty} R(\pi_j(f) - \pi_{j-1}(f))$$

$$\leq \sum_{j=k+1}^{\infty} \left(\frac{2^{7/2}}{\sqrt{n}} 2^{-j} \log^{1/2}(\operatorname{card} F_j) + 2^{5/2} 2^{-j} \sqrt{\frac{u}{n}}\right)$$

$$\leq \sum_{j=k+1}^{\infty} \left(\frac{2^{7/2}}{\sqrt{n}} 2^{-j} \log^{1/2} \mathcal{D}(F, 2^{-j}, d)\right) + 2^{5/2} 2^{-k} \sqrt{\frac{u}{n}}$$

Note that  $2^{-k} < 2d(f, 0)$ , so

$$2^{5/2}2^{-k} < 2^{7/2}d(f,0).$$

Furthermore,

$$\frac{2^{9/2}}{\sqrt{n}} \sum_{j=k+1}^{\infty} \left( 2^{-(j+1)} \log^{1/2} \mathcal{D}(F, 2^{-j}, d) \right) \leq \frac{2^{9/2}}{\sqrt{n}} \int_{0}^{2^{-(k+1)}} \log^{1/2} \mathcal{D}(F, \varepsilon, d) d\varepsilon$$

$$\leq \frac{2^{9/2}}{\sqrt{n}} \underbrace{\int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(F, \varepsilon, d) d\varepsilon}_{\text{Dudley's entropy integral}}$$

since  $2^{-(k+1)} < d(0, f)$ .

---

**Lemma 15.1.** Let  $\xi, \nu$  - random variables. Assume that

$$\mathbb{P}\left(\nu \ge t\right) \le \Gamma e^{-\gamma t}$$

where  $\Gamma \geq 1$ ,  $t \geq 0$ , and  $\gamma > 0$ . Furthermore, for all a > 0 assume that

$$\mathbb{E}\phi(\xi) \leq \mathbb{E}\phi(\nu)$$

where  $\phi(x) = (x - a)_+$ . Then

$$\mathbb{P}\left(\xi > t\right) < \Gamma \cdot e \cdot e^{-\gamma t}.$$

*Proof.* Since  $\phi(x) = (x - a)_+$ , we have  $\phi(\xi) \ge \phi(t)$  whenever  $\xi \ge t$ .

$$\mathbb{P}\left(\xi \ge t\right) \le \mathbb{P}\left(\phi(\xi) \ge \phi(t)\right)$$
$$\le \frac{\mathbb{E}\phi(\xi)}{\phi(t)} \le \frac{\mathbb{E}\phi(\nu)}{\phi(t)} = \frac{\mathbb{E}(\nu - a)_{+}}{(t - a)_{+}}$$

Furthermore,

$$\mathbb{E}(\nu - a)_{+} = \mathbb{E} \int_{0}^{(\nu - a)_{+}} 1 dx$$

$$= \mathbb{E} \int_{0}^{\infty} I(x \le (\nu - a)_{+}) dx$$

$$= \int_{0}^{\infty} \mathbb{E}I(x \le (\nu - a)_{+}) dx$$

$$= \int_{0}^{\infty} \mathbb{P}((\nu - a)_{+} \ge x) dx$$

$$= \int_{0}^{\infty} \mathbb{P}(\nu \ge a + x) dx$$

$$\le \int_{0}^{\infty} \Gamma e^{-\gamma a - \gamma x} dx = \frac{\Gamma e^{-\gamma a}}{\gamma}.$$

Hence,

$$\mathbb{P}\left(\xi \geq t\right) \leq \frac{\Gamma e^{-\gamma a}}{\gamma(t-a)_{+}} = \frac{\Gamma \cdot e \cdot e^{-\gamma t}}{1} = \Gamma \cdot e \cdot e^{-\gamma t}$$

where we chose optimal  $a = t - \frac{1}{\gamma}$  to minimize  $\frac{\Gamma e^{-\gamma a}}{\gamma}$ .

**Lemma 15.2.** Let  $x = (x_1, ..., x_n)$ ,  $x' = (x'_1, ..., x'_n)$ . If for functions  $\varphi_1(x, x')$ ,  $\varphi_2(x, x')$ ,  $\varphi_3(x, x')$ 

$$\mathbb{P}\left(\varphi_1(x, x') \ge \varphi_2(x, x') + \sqrt{\varphi_3(x, x') \cdot t}\right) \le \Gamma e^{-\gamma t}$$

then

$$\mathbb{P}\left(\mathbb{E}_{x'}\varphi_1(x,x') \ge \mathbb{E}_{x'}\varphi_2(x,x') + \sqrt{\mathbb{E}_{x'}\varphi_3(x,x') \cdot t}\right) \le \Gamma \cdot e \cdot e^{-\gamma t}.$$

(i.e. if the inequality holds, then it holds with averaging over one of the copies)

*Proof.* First, note that  $\sqrt{ab} = \inf_{\delta>0} (\delta a + \frac{b}{4\delta})$  with  $\delta_* = \sqrt{\frac{b}{4a}}$  achieving the infima. Hence,

$$\{\varphi_1 \ge \varphi_2 + \sqrt{\varphi_3 t}\} = \{\exists \delta > 0, \varphi_1 \ge \varphi_2 + \delta \varphi_3 + \frac{t}{4\delta}\}$$

$$= \{\exists \delta > 0, (\varphi_1 - \varphi_2 - \delta \varphi_3) \cdot 4\delta \ge t\}$$

$$= \{\sup_{\delta > 0} (\varphi_1 - \varphi_2 - \delta \varphi_3) \cdot 4\delta \ge t\}$$

and similarly

$$\{\mathbb{E}_{x'}\varphi_1 \ge \mathbb{E}_{x'}\varphi_2 + \sqrt{\mathbb{E}_{x'}\varphi_3 t}\} = \{\underbrace{\sup_{\delta > 0} (\mathbb{E}_{x'}\varphi_1 - \mathbb{E}_{x'}\varphi_2 - \delta\mathbb{E}_{x'}\varphi_3) 4\delta}_{\mathcal{E}} \ge t\}.$$

By assumption,  $\mathbb{P}(\nu \geq t) \leq \Gamma e^{-\gamma t}$ . We want to prove  $\mathbb{P}(\xi \geq t) \leq \Gamma \cdot e \cdot e^{-\gamma t}$ . By the previous lemma, we only need to check whether  $\mathbb{E}\phi(\xi) \leq \mathbb{E}\phi(\nu)$ .

$$\xi = \sup_{\delta>0} \mathbb{E}_{x'} (\varphi_1 - \varphi_2 - \delta \varphi_3) 4\delta$$

$$\leq \mathbb{E}_{x'} \sup_{\delta>0} (\varphi_1 - \varphi_2 - \delta \varphi_3) 4\delta$$

$$= \mathbb{E}_{x'} \nu$$

Thus,

$$\phi(\xi) \le \phi(\mathbb{E}_{x'}\nu) \le \mathbb{E}_{x'}\phi(\nu)$$

by Jensen's inequality ( $\phi$  is convex). Hence,

$$\mathbb{E}\phi(\xi) \leq \mathbb{E}\mathbb{E}_{x'}\phi(\nu) = \mathbb{E}\phi(\nu).$$

We will now use Lemma 15.2. Let  $\mathcal{F} = \{f : \mathcal{X} \mapsto [c, c+1]\}$ . Let  $x_1, \ldots, x_n, x'_1, \ldots, x'_n$  be i.i.d. random variables. Define

$$F = \{ (f(x_1) - f(x_1'), \dots, f(x_n) - f(x_n')) : f \in \mathcal{F} \} \subseteq [-1, 1]^n.$$

Define

$$d(f,g) = \left(\frac{1}{n}\sum_{i=1}^{n} \left( \left( f(x_i) - f(x_i') \right) - \left( g(x_i) - g(x_i') \right) \right)^2 \right)^{1/2}.$$

In Lecture 14, we proved

$$\mathbb{P}_{\varepsilon}\left(\forall f \in \mathcal{F}, \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i}(f(x_{i}) - f(x_{i}')) \leq \frac{2^{9/2}}{\sqrt{n}} \int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon, d) d\varepsilon + 2^{7/2} d(0, f) \sqrt{\frac{t}{n}}\right) \geq 1 - e^{-t}.$$

Complement of the above is

$$\mathbb{P}_{\varepsilon}\left(\exists f \in \mathcal{F}, \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i}(f(x_{i}) - f(x_{i}')) \geq \frac{2^{9/2}}{\sqrt{n}} \int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon, d) d\varepsilon + 2^{7/2} d(0, f) \sqrt{\frac{t}{n}}\right) \leq e^{-t}.$$

Taking expectation with respect to x, x', we get

$$\mathbb{P}\left(\exists f \in \mathcal{F}, \ \frac{1}{n} \sum_{i=1}^{n} \varepsilon_i (f(x_i) - f(x_i')) \ge \frac{2^{9/2}}{\sqrt{n}} \int_0^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon, d) d\varepsilon + 2^{7/2} d(0, f) \sqrt{\frac{t}{n}}\right) \le e^{-t}.$$

Hence (see below)

$$\mathbb{P}\left(\exists f \in \mathcal{F}, \ \frac{1}{n} \sum_{i=1}^{n} (f(x_i) - f(x_i')) \ge \frac{2^{9/2}}{\sqrt{n}} \int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon, d) d\varepsilon + 2^{7/2} d(0, f) \sqrt{\frac{t}{n}}\right) \le e^{-t}.$$

To see why the above step holds, notice that d(f,g) is invariant under permutations  $x_i \leftrightarrow x_i'$ . We can remove  $\varepsilon_i$  since x and x' are i.i.d and we can switch  $x_i$  and  $x_i'$ . To the right of " $\geq$ " sign, only distance d(f,g) depends on x,x', but it's invariant to the permutations.

By Lemma 15.2 (minus technical detail " $\exists f$ "),

$$\mathbb{P}\left(\exists f \in \mathcal{F}, \ \mathbb{E}_{x'} \frac{1}{n} \sum_{i=1}^{n} (f(x_i) - f(x_i')) \ge \mathbb{E}_{x'} \frac{2^{9/2}}{\sqrt{n}} \int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon, d) d\varepsilon + 2^{7/2} \sqrt{\frac{\mathbb{E}_{x'} d(0, f)^2 t}{n}}\right) \le e \cdot e^{-t},$$

where

$$\mathbb{E}_{x'} \frac{1}{n} \sum_{i=1}^{n} (f(x_i) - f(x_i')) = \frac{1}{n} \sum_{i=1}^{n} f(x_i) - \mathbb{E}f$$

and

$$\mathbb{E}_{x'}d(0,f)^2 = \mathbb{E}_{x'}\frac{1}{n}\sum_{i=1}^n (f(x_i) - f(x_i'))^2.$$

The Dudley integral above will be bounded by something non-random in the later lectures.

---

In Lecture 15, we proved the following Generalized VC inequality

$$\mathbb{P}\left(\forall f \in \mathcal{F}, \ \mathbb{E}f - \frac{1}{n} \sum_{i=1}^{n} f(x_i) \leq \frac{2^{9/2}}{\sqrt{n}} \mathbb{E}_{x'} \int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon, d) d\varepsilon + 2^{7/2} \sqrt{\frac{\mathbb{E}_{x'} d(0, f)^{2} t}{n}}\right) \geq 1 - e^{-t}$$
$$d(f, g) = \left(\frac{1}{n} \sum_{i=1}^{n} \left(f(x_i) - f(x'_i) - g(x_i) + g(x'_i)\right)^{2}\right)^{1/2}$$

**Definition 16.1.** We say that  $\mathcal{F}$  satisfies uniform entropy condition if

$$\forall n, \ \forall (x_1, \dots, x_n), \ \mathcal{D}(\mathcal{F}, \varepsilon, d_x) \leq \mathcal{D}(\mathcal{F}, \varepsilon)$$

where 
$$d_x(f,g) = \left(\frac{1}{n} \sum_{i=1}^n (f(x_i) - g(x_i))^2\right)^{1/2}$$

**Lemma 16.1.** If  $\mathcal{F}$  satisfies uniform entropy condition, then

$$\mathbb{E}_{x'} \int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon, d) d\varepsilon \leq \int_{0}^{\sqrt{\mathbb{E}_{x'} d(0,f)^{2}}} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon/2) d\varepsilon$$

*Proof.* Using inequality  $(a+b)^2 \le 2(a^2+b^2)$ ,

$$d(f,g) = \left(\frac{1}{n}\sum_{i=1}^{n} (f(x_i) - g(x_i) + g(x_i') - f(x_i'))^2\right)^{1/2}$$

$$\leq \left(\frac{2}{n}\sum_{i=1}^{n} \left((f(x_i) - g(x_i))^2 + (g(x_i') - f(x_i'))^2\right)\right)^{1/2}$$

$$= 2\left(\frac{1}{2n}\sum_{i=1}^{n} \left((f(x_i) - g(x_i))^2 + (g(x_i') - f(x_i'))^2\right)\right)^{1/2}$$

$$= 2d_{x,x'}(f,g)$$

Since  $d(f,g) \leq 2d_{x,x'}(f,g)$ , we also have

$$\mathcal{D}(\mathcal{F}, \varepsilon, d) \leq \mathcal{D}(\mathcal{F}, \varepsilon/2, d_{x,x'}).$$

Indeed, let  $f_1, ..., f_N$  be optimal  $\varepsilon$ -packing w.r.t. distance d. Then

$$\varepsilon \le d(f_i, f_j) \le 2d_{x,x'}(f_i, f_j)$$

and, hence,

$$\varepsilon/2 \le d_{x,x'}(f_i, f_j).$$

So,  $f_1, ..., f_N$  is  $\varepsilon/2$ -packing w.r.t.  $d_{x,x'}$ . Therefore, can pack at least N and so  $\mathcal{D}(\mathcal{F}, \varepsilon, d) \leq \mathcal{D}(\mathcal{F}, \varepsilon/2, d_{x,x'})$ .

$$\mathbb{E}_{x'} \int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon, d) d\varepsilon \leq \mathbb{E}_{x'} \int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon/2, d_{x,x'}) d\varepsilon$$
$$\leq \int_{0}^{d(0,f)} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon/2) d\varepsilon$$

Let  $\phi(x) = \int_0^x \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon) d\varepsilon$ . It is concave because  $\phi'(x) = \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon/2)$  is decreasing when x is increasing (can pack less with larger balls). Hence, by Jensen's inequality,

$$\mathbb{E}_{x'}\phi(d(0,f)) \le \phi(\mathbb{E}_{x'}d(0,f)) = \phi(\mathbb{E}_{x'}\sqrt{d(0,f)^2}) \le \phi(\sqrt{\mathbb{E}_{x'}d(0,f)^2}).$$

**Lemma 16.2.** If  $\mathcal{F} = \{f : \mathcal{X} \to [0, 1]\}$ , then

$$\mathbb{E}_{x'}d(0,f)^2 \le 2\max\left(\mathbb{E}f, \frac{1}{n}\sum_{i=1}^n f(x_i)\right)$$

Proof.

$$\mathbb{E}_{x'}d(0,f)^{2} = \mathbb{E}_{x'}\frac{1}{n}\sum_{i=1}^{n}(f(x_{i}) - f(x'_{i}))^{2}$$

$$= \frac{1}{n}\sum_{i=1}^{n}(f^{2}(x_{i}) - 2f(x_{i})\mathbb{E}f + \mathbb{E}f^{2})$$

$$\leq \frac{1}{n}\sum_{i=1}^{n}(f^{2}(x_{i}) + \mathbb{E}f^{2}) \leq \frac{1}{n}\sum_{i=1}^{n}f(x_{i}) + \mathbb{E}f$$

$$\leq 2\max\left(\mathbb{E}f, \frac{1}{n}\sum_{i=1}^{n}f(x_{i})\right)$$

**Theorem 16.1.** If  $\mathcal{F}$  satisfies Uniform Entropy Condition and  $\mathcal{F} = \{f : \mathcal{X} \to [0,1]\}$ . Then

$$\mathbb{P}\left(\forall f \in \mathcal{F}, \ \mathbb{E}f - \frac{1}{n} \sum_{i=1}^{n} f(x_i) \leq \frac{2^{9/2}}{\sqrt{n}} \int_{0}^{\sqrt{2\mathbb{E}f}} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon/2) d\varepsilon + 2^{7/2} \sqrt{\frac{2\mathbb{E}f \cdot t}{n}}\right) \geq 1 - e^{-t}.$$


*Proof.* If  $\mathbb{E}f \geq \frac{1}{n} \sum_{i=1}^{n} f(x_i)$ , then

$$2\max\left(\mathbb{E}f, \frac{1}{n}\sum_{i=1}^{n}f(x_i)\right) = 2\mathbb{E}f.$$

If  $\mathbb{E}f \leq \frac{1}{n} \sum_{i=1}^{n} f(x_i)$ ,

$$\mathbb{E}f - \frac{1}{n} \sum_{i=1}^{n} f(x_i) \le 0$$

and the bound trivially holds.

Another result:

$$\mathbb{P}\left(\forall f \in \mathcal{F}, \ \frac{1}{n} \sum_{i=1}^{n} f(x_i) - \mathbb{E}f \leq \frac{2^{9/2}}{\sqrt{n}} \int_{0}^{\sqrt{2\frac{1}{n} \sum_{i=1}^{n} f(x_i)}} \log^{1/2} \mathcal{D}(\mathcal{F}, \varepsilon/2) d\varepsilon + 2^{7/2} \sqrt{\frac{2(\frac{1}{n} \sum_{i=1}^{n} f(x_i))t}{n}}\right) \geq 1 - e^{-t}.$$

**Example 1** (VC-type entropy condition).

$$\log \mathcal{D}(\mathcal{F}, \varepsilon) \le \alpha \log \frac{2}{\varepsilon}.$$

For VC-subgraph classes, entropy condition is satisfied. Indeed, in Lecture 13, we proved that  $\mathcal{D}(\mathcal{F}, \varepsilon, d) \leq \left(\frac{8e}{\varepsilon} \log \frac{7}{\varepsilon}\right)^V$  for a VC-subgraph class  $\mathcal{F}$  with  $VC(\mathcal{F}) = V$ , where  $d(f, g) = d_1(f, g) = \frac{1}{n} \sum_{i=1}^n |f(x_i) - g(x_i)|$ . Note that if  $f, g: \mathcal{X} \mapsto [0, 1]$ , then

$$d_2(f,g) = \left(\frac{1}{n}\sum_{i=1}^n (f(x_i) - g(x_i))^2\right)^{1/2} \le \left(\frac{1}{n}\sum_{i=1}^n |f(x_i) - g(x_i)|\right)^{1/2}.$$

Hence,  $\varepsilon < d_2(f,g) \le \sqrt{d_1(f,g)}$  implies

$$\mathcal{D}(\mathcal{F}, \varepsilon, d_2) \leq \mathcal{D}(\mathcal{F}, \varepsilon^2, d_1) \leq \left(\frac{8e}{\varepsilon^2} \log \frac{7}{\varepsilon^2}\right)^V = \mathcal{D}(\mathcal{F}, \varepsilon).$$

The entropy is

$$\log \mathcal{D}(\mathcal{F}, \varepsilon) \le \log \left(\frac{8e}{\varepsilon^2} \log \frac{7}{\varepsilon^2}\right)^V = V \log \left(\frac{8e}{\varepsilon^2} \log \frac{7}{\varepsilon^2}\right) \le K \cdot V \log \frac{2}{\varepsilon},$$

where K is an absolute constant.

We now give an upper bound on the Dudley integral for VC-type entropy condition.

$$\int_0^x \sqrt{\log \frac{1}{\varepsilon}} d\varepsilon \le \begin{cases} 2x \log^{1/2} \frac{1}{x} &, & x \le \frac{1}{e} \\ 2x &, & x \ge \frac{1}{e} \end{cases}.$$

*Proof.* First, check the inequality for  $x \leq 1/e$ . Taking derivatives,

$$\sqrt{\log \frac{1}{x}} \le 2\sqrt{\log \frac{1}{x}} + \frac{x}{\sqrt{\log \frac{1}{x}}} \left(-\frac{1}{x}\right)$$
$$\log \frac{1}{x} \le 2\log \frac{1}{x} - 1$$
$$1 \le \log \frac{1}{x}$$
$$x \le 1/e$$

Now, check for  $x \ge 1/e$ .

$$\int_0^x \sqrt{\log \frac{1}{\varepsilon}} d\varepsilon = \int_0^{\frac{1}{e}} \sqrt{\log \frac{1}{\varepsilon}} d\varepsilon + \int_{\frac{1}{e}}^x \sqrt{\log \frac{1}{\varepsilon}} d\varepsilon$$

$$\leq \frac{2}{e} + \int_{\frac{1}{e}}^x 1 dx$$

$$= \frac{2}{e} + x - \frac{1}{e} = x + \frac{1}{e} \leq 2x$$

Using the above result, we get

$$\mathbb{P}\left(\forall f \in \mathcal{F}, \ \mathbb{E}f - \frac{1}{n} \sum_{i=1}^{n} f(x_i) \leq K \sqrt{\frac{\alpha}{n}} \mathbb{E}f \log \frac{1}{\mathbb{E}f} + K \sqrt{\frac{t\mathbb{E}f}{n}}\right) \geq 1 - e^{-t}.$$


Without loss of generality, we can assume  $\mathbb{E}f \geq \frac{1}{n}$ , and, therefore,  $\log \frac{1}{\mathbb{E}f} \leq \log n$ . Hence,

$$\mathbb{P}\left(\forall f \in \mathcal{F}, \ \frac{\mathbb{E}f - \frac{1}{n} \sum_{i=1}^{n} f(x_i)}{\sqrt{\mathbb{E}f}} \le K \sqrt{\frac{\alpha \log n}{n}} + K \sqrt{\frac{t}{n}}\right) \ge 1 - e^{-t}.$$

---

Consider the classification setting, i.e.  $\mathcal{Y} = \{-1, +1\}$ . Denote the set of weak classifiers

$$\mathcal{H} = \{h : \mathcal{X} \mapsto [-1, +1]\}$$

and assume  $\mathcal{H}$  is a VC-subgraph. Hence,  $\mathcal{D}(\mathcal{H}, \varepsilon, d_x) \leq K \cdot V \log 2/\varepsilon$ . A voting algorithm outputs

$$f = \sum_{i=1}^{T} \lambda_i h_i$$
, where  $h_i \in \mathcal{H}$ ,  $\sum_{i=1}^{T} \lambda_i \leq 1$ ,  $\lambda_i > 0$ .

Let

$$\mathcal{F} = \text{conv } \mathcal{H} = \left\{ \sum_{i=1}^{T} \lambda_i h_i, \ h_i \in \mathcal{H}, \ \sum_{i=1}^{T} \lambda_i \leq 1, \ \lambda_i \geq 0, \ T \geq 1 \right\}.$$

Then sign(f(x)) is the prediction of the label y. Let

$$\mathcal{F}_d = \operatorname{conv}_d \mathcal{H} = \left\{ \sum_{i=1}^d \lambda_i h_i, \ h_i \in \mathcal{H}, \ \sum_{i=1}^T \lambda_i \le 1, \ \lambda_i \ge 0 \right\}.$$

**Theorem 17.1.** For  $anyx = (x_1, ..., x_n)$ , if

$$\log \mathcal{D}(\mathcal{H}, \varepsilon, d_x) \leq KV \log 2/\varepsilon$$

then

$$\log \mathcal{D}(conv_d \mathcal{H}, \varepsilon, d_x) \leq KVd \log 2/\varepsilon.$$

*Proof.* Let  $h^1, \ldots, h^D$  be  $\varepsilon$ -packing of  $\mathcal{H}$  with respect to  $d_x$ ,  $D = \mathcal{D}(\mathcal{H}, \varepsilon, d_x)$ . Note that  $d_x$  is a norm.

$$d_x(f,g) = \left(\frac{1}{n}\sum_{i=1}^n (f(x_i) - g(x_i))^2\right)^{1/2} = ||f - g||_x.$$

If  $f = \sum_{i=1}^{d} \lambda_i h_i$ , for all  $h_i$  we can find  $h^{k_i}$  such that  $d(h_i, h^{k_i}) \leq \varepsilon$ . Let  $f' = \sum_{i=1}^{d} \lambda_i h^{k_i}$ . Then

$$d(f, f') = \|f - f'\|_{x} = \left\| \sum_{i=1}^{d} \lambda_{i} (h_{i} - h^{k_{i}}) \right\|_{x} \le \sum_{i=1}^{d} \lambda_{i} \|h_{i} - h^{k_{i}}\|_{x} \le \varepsilon.$$

Define

$$\mathcal{F}_{D,d} = \left\{ \sum_{i=1}^{d} \lambda_i h_i, \ h_i \in \{h^1, \dots, h^D\}, \ \sum_{i=1}^{d} \lambda_i \le 1, \ \lambda_i \ge 0 \right\}.$$

Hence, we can approximate any  $f \in \mathcal{F}_d$  by  $f' \in \mathcal{F}_{D,d}$  within  $\varepsilon$ .

Now, let  $f = \sum_{i=1}^{d} \lambda_i h_i \in \mathcal{F}_{D,d}$  and consider the following construction. We will choose  $Y_1(x), \ldots, Y_k(x)$  from  $h_1, \ldots, h_d$  according to  $\lambda_1, \ldots, \lambda_d$ :

$$\mathbb{P}(Y_j(x) = h_i(x)) = \lambda_i \text{ and } \mathbb{P}(Y_j(x) = 0) = 1 - \sum_{i=1}^d \lambda_i.$$

Note that with this construction

$$\mathbb{E}Y_j(x) = \sum_{i=1}^d \lambda_i h_i(x) = f(x).$$

Furthermore,

$$\mathbb{E} \left\| \frac{1}{k} \sum_{j=1}^{k} Y_j - f \right\|_x^2 = \mathbb{E} \frac{1}{n} \sum_{i=1}^{n} \left( \frac{1}{k} \sum_{j=1}^{k} Y_j(x_i) - f(x_i) \right)^2$$

$$= \frac{1}{n} \sum_{i=1}^{n} \mathbb{E} \left( \frac{1}{k} \sum_{j=1}^{k} (Y_j(x_i) - \mathbb{E} Y_j(x_i)) \right)^2$$

$$= \frac{1}{n} \sum_{i=1}^{n} \frac{1}{k^2} \sum_{j=1}^{k} \mathbb{E} (Y_j(x_i) - \mathbb{E} Y_j(x_i))^2$$

$$\leq \frac{4}{k}$$

because  $|Y_j(x_i) - \mathbb{E}Y_j(x_i)| \le 2$ . Choose  $k = 4/\varepsilon^2$ . Then

$$\mathbb{E} \left\| \frac{1}{k} \sum_{j=1}^{k} Y_j - f \right\|_x^2 = \mathbb{E} d_x \left( \frac{1}{k} \sum_{j=1}^{k} Y_j, f \right)^2 \le \varepsilon^2.$$

So, there exists a deterministic combination  $\frac{1}{k} \sum_{j=1}^{k} Y_j$  such that  $d_x(\frac{1}{k} \sum_{j=1}^{k} Y_j, f) \leq \varepsilon$ . Define

$$\mathcal{F}'_{D,d} = \left\{ \frac{1}{k} \sum_{j=1}^{k} Y_j : \ k = 4/\varepsilon^2, \ Y_j \in \{h_1, \dots, h_d\} \subseteq \{h^1, \dots, h^D\} \right\}$$

Hence, we can approximate any  $f = \sum_{i=1}^{d} \lambda_i h_i \in \mathcal{F}_{D,d}$ ,  $h_i \in \{h^1, \ldots, h^D\}$ , by  $f' \in \mathcal{F}'_{D,d}$  within  $\varepsilon$ .

Let us now bound the cardinality of  $\mathcal{F}'_{D,d}$ . To calculate the number of ways to choose k functions out of  $h_1, \ldots, h_d$ , assume each of  $h_i$  is chosen  $k_d$  times such that  $k = k_1 + \ldots + k_d$ .

We can formulate the problem as finding the number of strings of the form

$$\underbrace{00\ldots0}_{k_1}1\underbrace{00\ldots0}_{k_2}1\ldots1\underbrace{00\ldots0}_{k_d}.$$

In this string, there are d-1 "1"s and k "0"s, and total length is k+d-1. The number of such strings is  $\binom{k+d-1}{k}$ . Hence,

$$\operatorname{card} \mathcal{F}'_{D,d} \leq \binom{D}{d} \times \binom{k+d}{k}$$

$$\leq \frac{D^{D-d}D^d}{d^d(D-d)^{D-d}} \frac{(k+d)^{k+d}}{k^k d^d}$$

$$= \left(\frac{D(k+d)}{d^2}\right)^d \left(\frac{D}{D-d}\right)^{D-d} \left(\frac{k+d}{k}\right)^k$$

$$= \left(\frac{D(k+d)}{d^2}\right)^d \left(1 + \frac{d}{D-d}\right)^{D-d} \left(1 + \frac{d}{k}\right)^k$$
\nusing inequality  $1 + x \leq e^x$ 

$$\leq \left(\frac{D(k+d)e^2}{d^2}\right)^d$$

where  $k = 4/\varepsilon^2$  and  $D = \mathcal{D}(\mathcal{F}, \varepsilon, d_x)$ .

Therefore, we can approximate any  $f \in \mathcal{F}_d$  by  $f'' \in \mathcal{F}_{D,d}$  within  $\varepsilon$  and  $f'' \in \mathcal{F}_{D,d}$  by  $f' \in \mathcal{F}'_{D,d}$  within  $\varepsilon$ . Hence, we can approximate any  $f \in \mathcal{F}_d$  by  $f' \in \mathcal{F}'_{D,d}$  within  $2\varepsilon$ . Moreover,

$$\log \mathcal{N}(\mathcal{F}_d = \operatorname{conv}_d \mathcal{H}, 2\varepsilon, d_x) \leq d \log \frac{e^2 D(k+d)}{d^2}$$

$$= d \left( 2 + \log D + \log \frac{k+d}{d^2} \right)$$

$$\leq d \left( 2 + KV \log \frac{2}{\varepsilon} + \log \left( 1 + \frac{4}{\varepsilon^2} \right) \right)$$

$$\leq KV d \log \frac{2}{\varepsilon}$$

since  $\frac{k+d}{d^2} \le 1 + k$  and  $d \ge 1$ ,  $V \ge 1$ .

---

As in the previous lecture, let  $\mathcal{H} = \{h : \mathcal{X} \mapsto [-1, 1]\}$  be a VC-subgraph class and  $f \in \mathcal{F} = \text{conv } \mathcal{H}$ . The classifier is sign(f(x)). The set

$$\{y \neq \operatorname{sign}(f(x))\} = \{yf(x) \le 0\}$$

is the set of misclassified examples and  $\mathbb{P}(yf(x) \leq 0)$  is the misclassification error.

Assume the examples are labeled according to  $C_0 = \{x \in \mathcal{X} : y = 1\}$ . Let  $C = \{\text{sign}(f(x)) > 0\}$ . Then  $C_0 \triangle C$  are misclassified examples.

$$\mathbb{P}(C\triangle C_0) = \frac{1}{n} \sum_{i=1}^n I(x_i \in C\triangle C_0) + \underbrace{\mathbb{P}(C\triangle C_0) - \frac{1}{n} \sum_{i=1}^n I(x_i \in C\triangle C_0)}_{\text{small estimate uniformly over sets } C}.$$

For voting classifiers, the collection of sets  $\mathcal{C}$  can be "very large".

**Example 1.** Let  $\mathcal{H}$  be the class of simple step-up and step-down functions on the [0,1] interval, parametrized by a and b. Then  $VC(\mathcal{H}) = 2$ . Let  $\mathcal{F} = conv \mathcal{H}$ . First, rescale the

functions:  $f = \sum_{i=1}^{T} \lambda_i h_i = 2 \sum_{i=1}^{T} \lambda_i \left(\frac{h_i+1}{2}\right) - 1 = 2f' - 1$  where  $f' = \sum_{i=1}^{T} \lambda_i h_i'$ ,  $h_i' = \frac{h_i+1}{2}$ . We can generate any non-decreasing function f' such that f'(0) = 0 and f'(1) = 1. Similarly, we can generate any non-increasing f' such that f'(0) = 1 and f'(1) = 0. Rescaling back to f, we can get any non-increasing and non-decreasing functions of the form

Any function with sum of jumps less than 1 can be written as  $f = \frac{1}{2}(f_1 + f_2)$ . Hence, we can generate basically all sets by  $\{f(x) > 0\}$ , i.e. conv  $\mathcal{H}$  is bad.

Recall that  $\mathbb{P}(yf(x) \leq 0) = \mathbb{E}I(yf(x) \leq 0)$ . Define function  $\varphi_{\delta}(s)$  as follows:

Then,

$$I(s \le 0) \le \varphi_{\delta}(s) \le I(s \le \delta).$$

Hence,

$$\mathbb{P}(yf(x) \leq 0) \leq \mathbb{E}\varphi_{\delta}(yf(x))$$

$$= \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}(y_{i}f(x_{i})) + \left(\mathbb{E}\varphi_{\delta}(yf(x)) - \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}(y_{i}f(x_{i}))\right)$$

$$\leq \frac{1}{n} \sum_{i=1}^{n} I(y_{i}f(x_{i}) \leq \delta) + \left(\mathbb{E}\varphi_{\delta}(yf(x)) - \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}(y_{i}f(x_{i}))\right)$$

By going from  $\frac{1}{n} \sum_{i=1}^{n} I(y_i f(x_i) \leq 0)$  to  $\frac{1}{n} \sum_{i=1}^{n} I(y_i f(x_i) \leq \delta)$ , we are penalizing small confidence predictions. The margin yf(x) is a measure of the confidence of the prediction. For the sake of simplicity, denote  $\mathbb{E}\varphi_{\delta} = \mathbb{E}\varphi_{\delta}(yf(x))$  and  $\bar{\varphi}_{\delta} = \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}(y_i f(x_i))$ .

**Lemma 18.1.** Let  $\mathcal{F}_d = conv_d \ \mathcal{H} = \{\sum_{i=1}^d \lambda_i h_i, h_i \in \mathcal{H}\}$  and fix  $\delta \in (0,1]$ . Then

$$\mathbb{P}\left(\forall f \in \mathcal{F}_d, \ \frac{\mathbb{E}\varphi_\delta - \bar{\varphi_\delta}}{\sqrt{\mathbb{E}\varphi_\delta}} \le K\left(\sqrt{\frac{dV\log\frac{n}{\delta}}{n}} + \sqrt{\frac{t}{n}}\right)\right) \ge 1 - e^{-t}.$$

*Proof.* Denote

$$\varphi_{\delta}\left(y\mathcal{F}_{d}(x)\right) = \{\varphi_{\delta}\left(yf(x)\right), f \in \mathcal{F}_{d}\}.$$

Note that  $\varphi_{\delta}(yf(x)): \mathcal{X} \times \mathcal{Y} \mapsto [0,1].$ 

For any n, take any possible points  $(x_1, y_1), \ldots, (x_n, y_n)$ . Since

$$|\varphi_{\delta}(s) - \varphi_{\delta}(t)| \leq \frac{1}{\delta}|s - t|,$$

we have

$$d_{x,y}(\varphi_{\delta}(yf(x)), \varphi_{\delta}(yg(x))) = \left(\frac{1}{n} \sum_{i=1}^{n} (\varphi_{\delta}(y_{i}f(x_{i})) - \varphi_{\delta}(y_{i}g(x_{i})))^{2}\right)^{1/2}$$

$$\leq \left(\frac{1}{\delta^{2}} \frac{1}{n} \sum_{i=1}^{n} (y_{i}f(x_{i}) - y_{i}g(x_{i}))^{2}\right)^{1/2}$$

$$= \frac{1}{\delta} \left(\frac{1}{n} \sum_{i=1}^{n} (f(x_{i}) - g(x_{i}))^{2}\right)^{1/2}$$

$$= \frac{1}{\delta} d_{x}(f, g)$$

where  $f, g \in \mathcal{F}_d$ .

Choose  $\varepsilon \cdot \delta$ -packing of  $\mathcal{F}_d$  so that

$$d_{x,y}\left(\varphi_{\delta}\left(yf(x)\right),\varphi_{\delta}\left(yg(x)\right)\right) \leq \frac{1}{\delta}d_{x}(f,g) \leq \varepsilon.$$

Hence,

$$\mathcal{N}(\varphi_{\delta}(y\mathcal{F}_{d}(x)), \varepsilon, d_{x,y}) \leq \mathcal{D}(\mathcal{F}_{d}, \varepsilon\delta, d_{x})$$

and

$$\log \mathcal{N}(\varphi_{\delta}(y\mathcal{F}_{d}(x)), \varepsilon, d_{x,y}) \leq \log \mathcal{D}(\mathcal{F}_{d}, \varepsilon \delta, d_{x}) \leq KdV \log \frac{2}{\varepsilon \delta}.$$

We get

$$\log \mathcal{D}(\varphi_{\delta}(y\mathcal{F}_{d}), \varepsilon/2, d_{x,y}) \leq KdV \log \frac{2}{\varepsilon \delta}.$$

So, we can choose  $f_1, \ldots, f_D$ ,  $D = \mathcal{D}(\mathcal{F}_d, \varepsilon \delta, d_x)$  such that for any  $f \in \mathcal{F}_d$  there exists  $f_i$ ,  $d_x(f, f_i) \leq \varepsilon \delta$ . Hence,

$$d_{x,y}(\varphi_{\delta}(yf(x)), \varphi_{\delta}(yf_{i}(x))) \leq \varepsilon$$

and  $\varphi_{\delta}(yf_1(x)), \ldots, \varphi_{\delta}(yf_D(x))$  is an  $\varepsilon$ -cover of  $\varphi_{\delta}(y\mathcal{F}_d(x))$ .

---

We continue to prove the lemma from Lecture 18:

**Lemma 19.1.** Let  $\mathcal{F}_d = conv_d$   $\mathcal{H} = \{\sum_{i=1}^d \lambda_i h_i, h_i \in \mathcal{H}\}$  and fix  $\delta \in (0,1]$ . Then

$$\mathbb{P}\left(\forall f \in \mathcal{F}_d, \ \frac{\mathbb{E}\varphi_\delta - \bar{\varphi_\delta}}{\sqrt{\mathbb{E}\varphi_\delta}} \le K\left(\sqrt{\frac{dV\log\frac{n}{\delta}}{n}} + \sqrt{\frac{t}{n}}\right)\right) \ge 1 - e^{-t}.$$

*Proof.* We showed that

$$\log \mathcal{D}(\varphi_{\delta}(y\mathcal{F}_{d}), \varepsilon/2, d_{x,y}) \leq KdV \log \frac{2}{\varepsilon\delta}.$$

By the result of Lecture 16,

$$\mathbb{E}\varphi_{\delta}\left(yf(x)\right) - \frac{1}{n}\sum_{i=1}^{n}\varphi_{\delta}\left(y_{i}f(x_{i})\right) \leq \frac{k}{\sqrt{n}}\int_{0}^{\sqrt{\mathbb{E}\varphi_{\delta}}}\log^{1/2}\mathcal{D}(\varphi_{\delta}\left(y\mathcal{F}_{d}(x)\right),\varepsilon)d\varepsilon + \sqrt{\frac{t\mathbb{E}\varphi_{\delta}}{n}}$$

with probability at least  $1 - e^{-t}$ . We have

$$\frac{k}{\sqrt{n}} \int_{0}^{\sqrt{\mathbb{E}\varphi_{\delta}}} \log^{1/2} \mathcal{D}(\varphi_{\delta}(y\mathcal{F}_{d}(x)), \varepsilon) d\varepsilon \leq \frac{k}{\sqrt{n}} \int_{0}^{\sqrt{\mathbb{E}\varphi_{\delta}}} \sqrt{dV \log \frac{2}{\varepsilon \delta}} d\varepsilon$$

$$= \frac{k}{\sqrt{n}} \frac{2}{\delta} \int_{0}^{\delta\sqrt{\mathbb{E}\varphi_{\delta}}/2} \sqrt{dV} \sqrt{\log \frac{1}{x}} dx$$

$$\leq \frac{k}{\sqrt{n}} \frac{2}{\delta} \sqrt{dV} 2 \frac{\delta}{2} \sqrt{\mathbb{E}\varphi_{\delta}} \sqrt{\log \frac{2}{\delta\sqrt{\mathbb{E}\varphi_{\delta}}}}$$

where we have made a change of variables  $\frac{2}{\varepsilon \delta} = x$ ,  $\varepsilon = \frac{2x}{\delta}$ . Without loss of generality, assume  $\mathbb{E}\varphi_{\delta} \geq 1/n$ . Otherwise, we're doing better than in Lemma:  $\frac{\mathbb{E}}{\sqrt{\mathbb{E}}} \leq \sqrt{\frac{\log n}{n}} \Rightarrow \mathbb{E} \leq \frac{\log n}{n}$ . Hence,

$$\frac{k}{\sqrt{n}} \int_{0}^{\sqrt{\mathbb{E}\varphi_{\delta}}} \log^{1/2} \mathcal{D}(\varphi_{\delta}(y\mathcal{F}_{d}(x)), \varepsilon) d\varepsilon \leq K \sqrt{\frac{dV \mathbb{E}\varphi_{\delta}}{n}} \log \frac{2\sqrt{n}}{\delta} \\
\leq K \sqrt{\frac{dV \mathbb{E}\varphi_{\delta}}{n}} \log \frac{n}{\delta}$$

So, with probability at least  $1 - e^{-t}$ ,

$$\mathbb{E}\varphi_{\delta}\left(yf(x)\right) - \frac{1}{n}\sum_{i=1}^{n}\varphi_{\delta}\left(y_{i}f(x_{i})\right) \leq K\sqrt{\frac{dV\mathbb{E}\varphi_{\delta}\left(yf(x)\right)}{n}\log\frac{n}{\delta}} + \sqrt{\frac{t\mathbb{E}\varphi_{\delta}\left(yf(x)\right)}{n}}$$

which concludes the proof.

The above lemma gives a result for a fixed  $d \ge 1$  and  $\delta \in (0,1]$ . To obtain a uniform result, it's enough to consider  $\delta \in \Delta = \{2^{-k}, k \ge 1\}$  and  $d \in \{1, 2, ...\}$ . For a fixed  $\delta$  and d, use the Lemma above with  $t_{\delta,d}$  defined by  $e^{-t_{\delta,d}} = e^{-t} \frac{6\delta}{d^2\pi^2}$ . Then

$$\mathbb{P}\left(\forall f \in \mathcal{F}_d, \ldots + \sqrt{\frac{t_{\delta,d}}{n}}\right) \ge 1 - e^{-t_{\delta,d}} = 1 - e^{-t} \frac{6\delta}{d^2 \pi^2}$$

and

$$\mathbb{P}\left(\bigcup_{d,\delta} \left\{ \forall f \in \mathcal{F}_d, \ \ldots + \sqrt{\frac{t_{\delta,d}}{n}} \right\} \right) \ge 1 - \sum_{\delta,d} e^{-t} \frac{6\delta}{d^2 \pi^2} = 1 - e^{-t}.$$

Since  $t_{\delta,d} = t + \log \frac{d^2 \pi^2}{6\delta}$ .

$$\forall f \in \mathcal{F}_d, \ \frac{\mathbb{E}\varphi_{\delta} - \bar{\varphi}_{\delta}}{\sqrt{\mathbb{E}\varphi_{\delta}}} \leq K \left( \sqrt{\frac{dV \log \frac{n}{\delta}}{n}} + \sqrt{\frac{t + \log \frac{d^2 \pi^2}{6\delta}}{n}} \right)$$
$$\leq K \left( \sqrt{\frac{dV \log \frac{n}{\delta}}{n}} + \sqrt{\log \frac{d^2 \pi^2}{6\delta}} + \sqrt{\frac{t}{n}} \right)$$
$$\leq K' \left( \sqrt{\frac{dV \log \frac{n}{\delta}}{n}} + \sqrt{\frac{t}{n}} \right)$$

since  $\log \frac{d^2\pi^2}{6\delta}$ , the penalty for union-bound, is much smaller than  $\sqrt{\frac{dV\log\frac{n}{\delta}}{n}}$ .

Recall the bound on the misclassification error

$$\mathbb{P}\left(yf(x) \leq 0\right) \leq \frac{1}{n} \sum_{i=1}^{n} I(y_i f(x_i) \leq \delta) + \left(\mathbb{E}\varphi_\delta\left(yf(x)\right) - \frac{1}{n} \sum_{i=1}^{n} \varphi_\delta\left(y_i f(x_i)\right)\right).$$

If

$$\frac{\mathbb{E}\varphi_{\delta} - \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}}{\sqrt{\mathbb{E}\varphi_{\delta}}} \le \varepsilon,$$

then

$$\mathbb{E}\varphi_{\delta} - \varepsilon\sqrt{\mathbb{E}\varphi_{\delta}} - \frac{1}{n}\sum_{i=1}^{n}\varphi_{\delta} \le 0.$$

Lecture 19

Hence,

$$\sqrt{\mathbb{E}\varphi_{\delta}} \leq \frac{\varepsilon}{2} + \sqrt{\left(\frac{\varepsilon}{2}\right)^{2} + \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}}$$
$$\mathbb{E}\varphi_{\delta} \leq 2\left(\frac{\varepsilon}{2}\right)^{2} + 2\frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}.$$

The bound becomes

$$\mathbb{P}(yf(x) \le 0) \le K \left(\frac{1}{n} \sum_{i=1}^{n} I(y_i f(x_i) \le \delta) + \underbrace{\frac{dV}{n} \log \frac{n}{\delta}}_{(*)} + \frac{t}{n}\right)$$

where K is a rough constant.

(\*) not satisfactory because in boosting the bound should get better when the number of functions grows. We prove a better bound in the next lecture.

---

**Theorem 20.1.** With probability at least  $1 - e^{-t}$ , for any  $T \ge 1$  and any  $f = \sum_{i=1}^{T} \lambda_i h_i$ ,

$$\mathbb{P}\left(yf(x) \leq 0\right) \leq \inf_{\delta \in (0,1)} \left(\varepsilon + \sqrt{\mathbb{P}_n\left(yf(x) \leq \delta\right) + \varepsilon^2}\right)^2$$
where  $\varepsilon = \varepsilon(\delta) = K\left(\sqrt{\frac{V\min(T,(\log n)/\delta^2)\log\frac{n}{\delta}}{n}} + \sqrt{\frac{t}{n}}\right)$ .

Here we used the notation  $\mathbb{P}_n(C) = \frac{1}{n} \sum_{i=1}^n I(x_i \in C)$ .

Remark:

$$\mathbb{P}\left(yf(x) \leq 0\right) \leq \inf_{\delta \in (0,1)} K\left(\underbrace{\mathbb{P}_n\left(yf(x) \leq \delta\right)}_{\text{inc. with } \delta} + \underbrace{\frac{V\min(T, (\log n)/\delta^2)\log\frac{n}{\delta}}{n}}_{\text{dec. with } \delta} + \frac{t}{n}\right).$$

*Proof.* Let  $f = \sum_{i=1}^{T} \lambda_i h_i$ ,  $g = \frac{1}{k} \sum_{j=1}^{k} Y_j$ , where

$$\mathbb{P}(Y_j = h_i) = \lambda_i \text{ and } \mathbb{P}(Y_j = 0) = 1 - \sum_{i=1}^{T} \lambda_i$$

as in Lecture 17. Then  $\mathbb{E}Y_j(x) = f(x)$ .

$$\mathbb{P}(yf(x) \le 0) = \mathbb{P}(yf(x) \le 0, yg(x) \le \delta) + \mathbb{P}(yf(x) \le 0, yg(x) > \delta)$$
$$\le \mathbb{P}(yg(x) \le \delta) + \mathbb{P}(yg(x) > \delta \mid yf(x) \le 0)$$

$$\mathbb{P}\left(yg(x) > \delta \mid yf(x) \le 0\right) = \mathbb{E}_x \mathbb{P}_Y\left(y\frac{1}{k}\sum_{j=1}^k Y_j(x) > \delta \mid y\mathbb{E}_Y Y_j(x) \le 0\right)$$

Shift Y's to [0,1] by defining  $Y'_j = \frac{yY_j+1}{2}$ . Then

$$\mathbb{P}(yg(x) > \delta | yf(x) \leq 0) = \mathbb{E}_x \mathbb{P}_Y \left( \frac{1}{k} \sum_{j=1}^k Y_j' \geq \frac{1}{2} + \frac{\delta}{2} \mid \mathbb{E}Y_j' \leq \frac{1}{2} \right)$$

$$\leq \mathbb{E}_x \mathbb{P}_Y \left( \frac{1}{k} \sum_{j=1}^k Y_j' \geq \mathbb{E}Y_1' + \frac{\delta}{2} \mid \mathbb{E}Y_j' \leq \frac{1}{2} \right)$$

$$\leq \text{(by Hoeffding's ineq.) } \mathbb{E}_x e^{-kD\left(\mathbb{E}Y_1' + \frac{\delta}{2}, \mathbb{E}Y_1'\right)}$$

$$\leq \mathbb{E}_x e^{-k\delta^2/2} = e^{-k\delta^2/2}$$

because  $D(p,q) \ge 2(p-q)^2$  (KL-divergence for binomial variables, Homework 1) and, hence,

$$D\left(\mathbb{E}Y_1' + \frac{\delta}{2}, \mathbb{E}Y_1'\right) \ge 2\left(\frac{\delta}{2}\right)^2 = \delta^2/2.$$

We therefore obtain

(1) 
$$\mathbb{P}(yf(x) \le 0) \le \mathbb{P}(yg(x) \le \delta) + e^{-k\delta^2/2}$$

and the second term in the bound will be chosen to be equal to 1/n.

Similarly, we can show

$$\mathbb{P}_n(yg(x) \le 2\delta) \le \mathbb{P}_n(yf(x) \le 3\delta) + e^{-k\delta^2/2}.$$

Choose k such that  $e^{-k\delta^2/2} = 1/n$ , i.e.  $k = \frac{2}{\delta^2} \log n$ .

Now define  $\varphi_{\delta}$  as follows:

Observe that

(2) 
$$I(s \le \delta) \le \varphi_{\delta}(s) \le I(s \le 2\delta).$$

By the result of Lecture 19, with probability at least  $1 - e^{-t}$ , for all  $k, \delta$  and any  $g \in \mathcal{F}_k = \text{conv }_k(\mathcal{H})$ ,

$$\Phi\left(\mathbb{E}\varphi_{\delta}, \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}\right) = \frac{\mathbb{E}\varphi_{\delta}\left(yg(x)\right) - \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}\left(y_{i}g(x_{i})\right)}{\sqrt{\mathbb{E}\varphi_{\delta}\left(yg(x)\right)}}$$

$$\leq K\left(\sqrt{\frac{Vk \log \frac{n}{\delta}}{n}} + \sqrt{\frac{t}{n}}\right)$$

$$= \varepsilon/2.$$

Note that  $\Phi(x,y) = \frac{x-y}{\sqrt{x}}$  is increasing with x and decreasing with y.

By inequalities (1) and (2),

$$\mathbb{E}\varphi_{\delta}\left(yg(x)\right) \geq \mathbb{P}\left(yg(x) \leq \delta\right) \geq \mathbb{P}\left(yf(x) \leq 0\right) - \frac{1}{n}$$

and

$$\frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta} (y_i g(x_i)) \leq \mathbb{P}_n (y g(x) \leq 2\delta) \leq \mathbb{P}_n (y f(x) \leq 3\delta) + \frac{1}{n}.$$

By decreasing x and increasing y in  $\Phi(x,y)$ , we decrease  $\Phi(x,y)$ . Hence,

$$\Phi\left(\underbrace{\mathbb{P}\left(yf(x) \leq 0\right) - \frac{1}{n}}_{x}, \underbrace{\mathbb{P}_{n}\left(yf(x) \leq 3\delta\right) + \frac{1}{n}}_{y}\right) \leq K\left(\sqrt{\frac{Vk\log\frac{n}{\delta}}{n}} + \sqrt{\frac{t}{n}}\right)$$

where  $k = \frac{2}{\delta^2} \log n$ .

If  $\frac{x-y}{\sqrt{x}} \leq \varepsilon$ , we have

$$x \le \left(\frac{\varepsilon}{2} + \sqrt{\left(\frac{\varepsilon}{2}\right)^2 + y}\right)^2$$

So,

$$\mathbb{P}\left(yf(x) \le 0\right) - \frac{1}{n} \le \left(\frac{\varepsilon}{2} + \sqrt{\left(\frac{\varepsilon}{2}\right)^2 + \mathbb{P}_n\left(yf(x) \le 3\delta\right) + \frac{1}{n}}\right)^2.$$

---

Let  $f = \sum_{i=1}^{T} \lambda_i h_i$ , where  $\lambda_1 \geq \lambda_2 \geq \ldots \geq \lambda_T \geq 0$ . Rewrite f as

$$f = \sum_{i=1}^{d} \lambda_i h_i + \sum_{i=d+1}^{T} \lambda_i h_i = \sum_{i=1}^{d} \lambda_i h_i + \gamma(d) \sum_{i=d+1}^{T} \lambda'_i h_i$$

where  $\gamma(d) = \sum_{i=d+1}^{T} \lambda_i$  and  $\lambda'_i = \lambda_i / \gamma(d)$ .

Consider the following random approximation of f,

$$g = \sum_{i=1}^{d} \lambda_i h_i + \gamma(d) \frac{1}{k} \sum_{j=1}^{k} Y_j$$

where, as in the previous lectures,

$$\mathbb{P}(Y_i = h_i) = \lambda_i', \quad i = d + 1, \dots, T$$

for any j = 1, ..., k. Recall that  $\mathbb{E}Y_j = \sum_{i=d+1}^T \lambda_i' h_i$ .

Then

$$\mathbb{P}(yf(x) \le 0) = \mathbb{P}(yf(x) \le 0, yg(x) \le \delta) + \mathbb{P}(yf(x) \le 0, yg(x) > \delta)$$
$$\le \mathbb{P}(yg(x) \le \delta) + \mathbb{E}\left[\mathbb{P}_Y\left(yf(x) \le 0, yg(x) \ge \delta \mid (x, y)\right)\right]$$

Furthermore,

$$\mathbb{P}_{Y}\left(yf(x) \leq 0, yg(x) \geq \delta \mid (x,y)\right) \leq \mathbb{P}_{Y}\left(yg(x) - yf(x) > \delta \mid (x,y)\right)$$
$$= \mathbb{P}_{Y}\left(\gamma(d)y\left(\frac{1}{k}\sum_{j=1}^{k}Y_{j}(x) - \mathbb{E}Y_{1}\right) \geq \delta \mid (x,y)\right).$$

By renaming  $Y_j' = \frac{yY_j+1}{2} \in [0,1]$  and applying Hoeffding's inequality, we get

$$\mathbb{P}_{Y}\left(\gamma(d)y\left(\frac{1}{k}\sum_{j=1}^{k}Y_{j}(x)-\mathbb{E}Y\right)\geq\delta\mid(x,y)\right)=\mathbb{P}_{Y}\left(\frac{1}{k}\sum_{j=1}^{k}Y_{j}'(x)-\mathbb{E}Y_{1}'\geq\frac{\delta}{2\gamma(d)}\mid(x,y)\right)$$

$$< e^{-\frac{k\delta^{2}}{2\gamma(d)^{2}}}.$$

Hence,

$$\mathbb{P}\left(yf(x) \le 0\right) \le \mathbb{P}\left(yg(x) \le \delta\right) + e^{-\frac{k\delta^2}{2\gamma^2(d)}}$$

If we set  $e^{-\frac{k\delta^2}{2\gamma(d)^2}} = \frac{1}{n}$ , then  $k = \frac{2\gamma^2(d)}{\delta^2} \log n$ .

We have

$$g = \sum_{i=1}^{d} \lambda_i h_i + \gamma(d) \frac{1}{k} \sum_{j=1}^{k} Y_j \in \text{conv}_{d+k} \mathcal{H},$$

 $d + k = d + \frac{2\gamma^2(d)}{\delta^2} \log n.$ 

Define the effective dimension of f as

$$e(f, \delta) = \min_{0 \le d \le T} \left( d + \frac{2\gamma^2(d)}{\delta^2} \log n \right).$$

Recall from the previous lectures that

$$\mathbb{P}_n\left(yg(x) \le 2\delta\right) \le \mathbb{P}_n\left(yf(x) \le 3\delta\right) + \frac{1}{n}.$$

Hence, we have the following margin-sparsity bound

**Theorem 21.1.** For  $\lambda_1 \geq \ldots \lambda_T \geq 0$ , we define  $\gamma(d, f) = \sum_{i=d+1}^T \lambda_i$ . Then with probability at least  $1 - e^{-t}$ ,

$$\mathbb{P}\left(yf(x) \le 0\right) \le \inf_{\delta \in (0,1)} \left(\varepsilon + \sqrt{\mathbb{P}_n\left(yf(x) \le \delta\right) + \varepsilon^2}\right)^2$$

where

$$\varepsilon = K\left(\sqrt{\frac{V \cdot e(f, \delta)}{n} \log \frac{n}{\delta}} + \sqrt{\frac{t}{n}}\right)$$

**Example 1.** Consider the zero-error case. Define

$$\delta^* = \sup\{\delta > 0, \mathbb{P}_n (yf(x) \le \delta) = 0\}.$$

Hence,  $\mathbb{P}_n(yf(x) \leq \delta^*) = 0$  for confidence  $\delta^*$ . Then

$$\mathbb{P}(yf(x) \le 0) \le 4\varepsilon^2 = K\left(\frac{V \cdot e(f, \delta^*)}{n} \log \frac{n}{\delta^*} + \frac{t}{n}\right)$$
$$\le K\left(\frac{V \log n}{(\delta^*)^2 n} \log \frac{n}{\delta^*} + \frac{t}{n}\right)$$

because  $e(f, \delta) \leq \frac{2}{\delta^2} \log n$  always.

**Example 2.** Consider the polynomial weight decay:  $\lambda_i \leq Ki^{-\alpha}$ , for some  $\alpha > 1$ . Then

$$\gamma(d) = \sum_{i=d+1}^{T} \lambda_i \le K \sum_{i=d+1}^{T} i^{-\alpha} \le K \int_{d}^{\infty} x^{-\alpha} dx = K \frac{1}{(\alpha - 1)d^{\alpha - 1}} = \frac{K_{\alpha}}{d^{\alpha - 1}}$$

Then

$$e(f, \delta) = \min_{d} \left( d + \frac{2\gamma^{2}(d)}{\delta^{2}} \log n \right)$$

$$\leq \min_{d} \left( d + \frac{K'_{\alpha}}{\delta^{2} d^{2(\alpha - 1)}} \log n \right)$$

Taking derivative with respect to d and setting it to zero,

$$1 - \frac{K_{\alpha} \log n}{\delta^2 d^{2\alpha - 1}} = 0$$

we get

$$d = K_{\alpha} \cdot \frac{\log^{1/(2\alpha - 1)} n}{\delta^{2/(2\alpha - 1)}} \le K \frac{\log n}{\delta^{2/(2\alpha - 1)}}.$$

Hence,

$$e(f, \delta) \le K \frac{\log n}{\delta^{2/(2\alpha - 1)}}$$

Plugging in,

$$\mathbb{P}\left(yf(x) \le 0\right) \le K\left(\frac{V\log n}{n(\delta^*)^{2/(2\alpha-1)}}\log\frac{n}{\delta^*} + \frac{t}{n}\right).$$

As  $\alpha \to \infty$ , the bound behaves like

$$\frac{V\log n}{n}\log\frac{n}{\delta^*}.$$

---

Let  $Z(x_1, ..., x_n) : \mathcal{X}^n \to \mathbb{R}$ . We would like to bound  $Z - \mathbb{E}Z$ . We will be able to answer this question if for any  $x_1, ..., x_n, x'_1, ..., x'_n$ ,

(1) 
$$|Z(x_1,\ldots,x_n) - Z(x_1,\ldots,x_{i-1},x_i',x_{i+1},\ldots,x_n)| \le c_i.$$

Decompose  $Z - \mathbb{E}Z$  as follows

$$Z(x_{1},...,x_{n}) - \mathbb{E}_{x'}Z(x'_{1},...,x'_{n}) = (Z(x_{1},...,x_{n}) - \mathbb{E}_{x'}Z(x'_{1},x_{2},...,x_{n}))$$

$$+ (\mathbb{E}_{x'}Z(x'_{1},x_{2},...,x_{n}) - \mathbb{E}_{x'}Z(x'_{1},x'_{2},x_{3},...,x_{n}))$$

$$...$$

$$+ (\mathbb{E}_{x'}Z(x'_{1},...,x'_{n-1},x_{n}) - \mathbb{E}_{x'}Z(x'_{1},...,x'_{n}))$$

$$= Z_{1} + Z_{2} + ... + Z_{n}$$

where

$$Z_i = \mathbb{E}_{x'} Z(x'_1, \dots, x'_{i-1}, x_i, \dots, x_n) - \mathbb{E}_{x'} Z(x'_1, \dots, x'_i, x_{i+1}, \dots, x_n).$$

Assume

- $(1) |Z_i| \le c_i$
- (2)  $\mathbb{E}_{X_i} Z_i = 0$
- $(3) Z_i = Z_i(x_i, \dots, x_n)$

**Lemma 22.1.** For any  $\lambda \in \mathbb{R}$ ,

$$\mathbb{E}_{x_i} e^{\lambda Z_i} \le e^{\lambda^2 c_i^2/2}.$$

*Proof.* Take any  $-1 \leq s \leq 1$ . With respect to  $\lambda$ , function  $e^{\lambda s}$  is convex and

$$e^{\lambda s} = e^{\lambda \left(\frac{1+s}{2}\right) + (-\lambda)\left(\frac{1-s}{2}\right)}.$$

Then  $0 \le \frac{1+s}{2}, \frac{1-s}{2} \le 1$  and  $\frac{1+s}{2} + \frac{1-s}{2} = 1$  and therefore

$$e^{\lambda s} \le \frac{1+s}{2}e^{\lambda} + \frac{1-s}{2}e^{-\lambda} = \frac{e^{\lambda} + e^{-\lambda}}{2} + s\frac{e^{\lambda} - e^{-\lambda}}{2} \le e^{\lambda^2/2} + s \cdot \operatorname{sh}(x)$$

using Taylor expansion. Now use  $\frac{Z_i}{c_i} = s$ , where, by assumption,  $-1 \le \frac{Z_i}{c_i} \le 1$ . Then

$$e^{\lambda Z_i} = e^{\lambda c_i \cdot \frac{Z_i}{c_i}} \le e^{\lambda^2 c_i^2/2} + \frac{Z_i}{c_i} \operatorname{sh}(\lambda c_i).$$

Since  $\mathbb{E}_{x_i} Z_i = 0$ ,

$$\mathbb{E}_{x_i} e^{\lambda Z_i} \le e^{\lambda^2 c_i^2/2}.$$

We now prove McDiarmid's inequality

**Theorem 22.1.** If condition (1) is satisfied,

$$\mathbb{P}(Z - \mathbb{E}Z > t) \le e^{-\frac{t^2}{2\sum_{i=1}^n c_i^2}}.$$

*Proof.* For any  $\lambda > 0$ 

$$\mathbb{P}\left(Z - \mathbb{E}Z > t\right) = \mathbb{P}\left(e^{\lambda(Z - \mathbb{E}Z)} > e^{\lambda t}\right) \le \frac{\mathbb{E}e^{\lambda(Z - \mathbb{E}Z)}}{e^{\lambda t}}.$$

Furthermore,

$$\mathbb{E}e^{\lambda(Z-\mathbb{E}Z)} = \mathbb{E}e^{\lambda(Z_{1}+...+Z_{n})}$$

$$= \mathbb{E}\mathbb{E}_{x_{1}}e^{\lambda(Z_{1}+...+Z_{n})}$$

$$= \mathbb{E}\left[e^{\lambda(Z_{2}+...+Z_{n})}\mathbb{E}_{x_{1}}e^{\lambda Z_{1}}\right]$$

$$\leq \mathbb{E}\left[e^{\lambda(Z_{2}+...+Z_{n})}e^{\lambda^{2}c_{1}^{2}/2}\right]$$

$$= e^{\lambda^{2}c_{1}^{2}/2}\mathbb{E}\mathbb{E}_{x_{2}}\left[e^{\lambda(Z_{2}+...+Z_{n})}\right]$$

$$= e^{\lambda^{2}c_{1}^{2}/2}\mathbb{E}\left[e^{\lambda(Z_{3}+...+Z_{n})}\mathbb{E}_{x_{2}}e^{\lambda Z_{2}}\right]$$

$$\leq e^{\lambda^{2}(c_{1}^{2}+c_{2}^{2})/2}\mathbb{E}e^{\lambda(Z_{3}+...+Z_{n})}$$

$$\leq e^{\lambda^{2}\sum_{i=1}^{n}c_{i}^{2}/2}$$

Hence,

$$\mathbb{P}\left(Z - \mathbb{E}Z > t\right) \le e^{-\lambda t + \lambda^2 \sum_{i=1}^{n} c_i^2/2}$$

and we minimize over  $\lambda > 0$  to get the result of the theorem.

**Example** 1.Let  $\mathcal{F}$  be a class of functions:  $\mathcal{X} \mapsto [a,b]$ . Define the empirical process

$$Z(x_1,\ldots,x_n) = \sup_{f\in\mathcal{F}} \left| \mathbb{E}f - \frac{1}{n} \sum_{i=1}^n f(x_i) \right|.$$

Then, for any i,

$$|Z(x_1, \dots, x_i', \dots, x_n) - Z(x_1, \dots, x_i, \dots, x_n)|$$

$$= \left| \sup_{f} \left| \mathbb{E}f - \frac{1}{n} \left( f(x_1) + \dots + f(x_i') + \dots + f(x_n) \right) \right| \right|$$

$$- \sup_{f} \left| \mathbb{E}f - \frac{1}{n} \left( f(x_1) + \dots + f(x_i) + \dots + f(x_n) \right) \right| \right|$$

$$\leq \sup_{f \in \mathcal{F}} \frac{1}{n} |f(x_i) - f(x_i')| \leq \frac{b - a}{n} = c_i$$

because

$$\sup_{t} f(t) - \sup_{t} g(t) \le \sup_{t} (f(t) - g(t))$$

and

$$|c| - |d| \le |c - d|.$$

Thus, if  $a \leq f(x) \leq b$  for all f and x, then, setting  $c_i = \frac{b-a}{n}$  for all i,

$$\mathbb{P}(Z - \mathbb{E}Z > t) \le \exp\left(-\frac{t^2}{2\sum_{i=1}^n \frac{(b-a)^2}{n^2}}\right) = e^{-\frac{nt^2}{2(b-a)^2}}.$$

By setting  $t = \sqrt{\frac{2u}{n}}(b-a)$ , we get

$$\mathbb{P}\left(Z - \mathbb{E}Z > \sqrt{\frac{2u}{n}}(b - a)\right) \le e^{-u}.$$

**Example 2.**Let  $\varepsilon_1, \ldots, \varepsilon_n$  be i.i.d. such that  $\mathbb{P}(\varepsilon = \pm 1) = \frac{1}{2}$ . Define

$$Z((\varepsilon_1, x_1), \dots, (\varepsilon_n, x_n)) = \sup_{f \in \mathcal{F}} \left| \frac{1}{n} \sum_{i=1}^n \varepsilon_i f(x_i) \right|.$$

Then, for any i,

$$|Z((\varepsilon_1, x_1), \dots, (\varepsilon'_i, x'_i), \dots, (\varepsilon_n, x_n)) - Z((\varepsilon_1, x_1), \dots, (\varepsilon_i, x_i), \dots, (\varepsilon_n, x_n))|$$

$$\leq \sup_{f \in \mathcal{F}} \left| \frac{1}{n} (\varepsilon'_i f(x'_i) - \varepsilon_i f(x_i)) \right| \leq \frac{2M}{n} = c_i$$

where  $-M \le f(x) \le M$  for all f and x.

Hence,

$$\mathbb{P}(Z - \mathbb{E}Z > t) \le \exp\left(-\frac{t^2}{2\sum_{i=1}^n \frac{(2M)^2}{n^2}}\right) = e^{-\frac{nt^2}{8M^2}}.$$

By setting  $t = \sqrt{\frac{8u}{n}}M$ , we get

$$\mathbb{P}\left(Z - \mathbb{E}Z > \sqrt{\frac{8u}{n}}M\right) \le e^{-u}.$$

Similarly,

$$\mathbb{P}\left(\mathbb{E}Z - Z > \sqrt{\frac{8u}{n}}M\right) \le e^{-u}.$$

---

Define the following processes:

$$Z(x) = \sup_{f \in \mathcal{F}} \left( \mathbb{E}f - \frac{1}{n} \sum_{i=1}^{n} f(x_i) \right)$$

and

$$R(x) = \sup_{f \in \mathcal{F}} \frac{1}{n} \sum_{i=1}^{n} \varepsilon_i f(x_i).$$

Assume  $a \leq f(x) \leq b$  for all f, x. In the last lecture we proved Z is concentrated around its expectation: with probability at least  $1 - e^{-t}$ ,

$$Z < \mathbb{E}Z + (b-a)\sqrt{\frac{2t}{n}}.$$

Furthermore,

$$\mathbb{E}Z(x) = \mathbb{E}\sup_{f\in\mathcal{F}} \left( \mathbb{E}f - \frac{1}{n}\sum_{i=1}^{n} f(x_i) \right)$$

$$= \mathbb{E}\sup_{f\in\mathcal{F}} \left( \mathbb{E}\left[\frac{1}{n}\sum_{i=1}^{n} f(x_i')\right] - \frac{1}{n}\sum_{i=1}^{n} f(x_i) \right)$$

$$\leq \mathbb{E}\sup_{f\in\mathcal{F}} \frac{1}{n}\sum_{i=1}^{n} (f(x_i') - f(x_i))$$

$$= \mathbb{E}\sup_{f\in\mathcal{F}} \frac{1}{n}\sum_{i=1}^{n} \varepsilon_i (f(x_i') - f(x_i))$$

$$\leq \mathbb{E}\sup_{f\in\mathcal{F}} \frac{1}{n}\sum_{i=1}^{n} \varepsilon_i f(x_i') + \sup_{f\in\mathcal{F}} \left( -\frac{1}{n}\sum_{i=1}^{n} \varepsilon_i f(x_i) \right)$$

$$\leq 2\mathbb{E}R(x).$$

Hence, with probability at least  $1 - e^{-t}$ ,

$$Z < 2\mathbb{E}R + (b-a)\sqrt{\frac{2t}{n}}.$$

It can be shown that R is also concentrated around its expectation: if  $-M \le f(x) \le M$  for all f, x, then with probability at least  $1 - e^{-t}$ ,

$$\mathbb{E}R \le R + M\sqrt{\frac{2t}{n}}.$$

Hence, with high probability,

$$Z(x) \le 2R(x) + 4M\sqrt{\frac{2t}{n}}.$$

**Theorem 23.1.** *If*  $-1 \le f \le 1$ , *then* 

$$\mathbb{P}\left(Z(x) \le 2\mathbb{E}R(x) + 2\sqrt{\frac{2t}{n}}\right) \ge 1 - e^{-t}.$$

If  $0 \le f \le 1$ , then

$$\mathbb{P}\left(Z(x) \le 2\mathbb{E}R(x) + \sqrt{\frac{2t}{n}}\right) \ge 1 - e^{-t}.$$

Consider  $\mathbb{E}_{\varepsilon}R(x) = \mathbb{E}_{\varepsilon}\sup_{f\in\mathcal{F}}\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}f(x_{i})$ . Since  $x_{i}$  are fixed,  $f(x_{i})$  are just vectors. Let  $F\subseteq\mathbb{R}^{n}, f\in F$ , where  $f=(f_{1},\ldots,f_{n})$ .

Define contraction  $\varphi_i : \mathbb{R} \to \mathbb{R}$  for i = 1, ..., n such that  $\varphi_i(0) = 0$  and  $|\varphi_i(s) - \varphi_i(t)| \le |s - t|$ . Let  $G : \mathbb{R} \to \mathbb{R}$  be convex and non-decreasing.

The following theorem is called Comparison inequality for Rademacher process.

## Theorem 23.2.

$$\mathbb{E}_{\varepsilon}G\left(\sup_{f\in F}\sum \varepsilon_{i}\varphi_{i}(f_{i})\right) \leq \mathbb{E}_{\varepsilon}G\left(\sup_{f\in F}\sum \varepsilon_{i}f_{i}\right).$$

*Proof.* It is enough to show that for  $T \subseteq \mathbb{R}^2$ ,  $t = (t_1, t_2) \in T$ 

$$\mathbb{E}_{\varepsilon}G\left(\sup_{t\in T}t_1+\varepsilon\varphi(t_2)\right)\leq \mathbb{E}_{\varepsilon}G\left(\sup_{t\in T}t_1+\varepsilon t_2\right),\,$$

i.e. enough to show that we can erase contraction for 1 coordinate while fixing all others. Since  $\mathbb{P}(\varepsilon = \pm 1) = 1/2$ , we need to prove

$$\frac{1}{2}G\left(\sup_{t\in T}t_1+\varphi(t_2)\right)+\frac{1}{2}G\left(\sup_{t\in T}t_1-\varphi(t_2)\right)\leq \frac{1}{2}G\left(\sup_{t\in T}t_1+t_2\right)+\frac{1}{2}G\left(\sup_{t\in T}t_1-t_2\right).$$

Assume  $\sup_{t \in T} t_1 + \varphi(t_2)$  is attained on  $(t_1, t_2)$  and  $\sup_{t \in T} t_1 - \varphi(t_2)$  is attained on  $(s_1, s_2)$ . Then

$$t_1 + \varphi(t_2) \ge s_1 + \varphi(s_2)$$

and

$$s_1 - \varphi(s_2) \ge t_1 - \varphi(t_2).$$

Again, we want to show

$$\Sigma = G(t_1 + \varphi(t_2)) + G(s_1 - \varphi(s_2)) \le G(t_1 + t_2) + G(t_1 - t_2).$$

Case 1:  $t_2 \le 0, s_2 \ge 0$ 

Since  $\varphi$  is a contraction,  $\varphi(t_2) \leq |t_2| \leq -t_2$ ,  $-\varphi(s_2) \leq s_2$ .

$$\Sigma = G(t_1 + \varphi(t_2)) + G(s_1 - \varphi(s_2)) \le G(t_1 - t_2) + G(s_1 + s_2)$$

$$\le G\left(\sup_{t \in T} t_1 - t_2\right) + G\left(\sup_{t \in T} t_1 + t_2\right).$$

Case  $2: t_2 \ge 0, s_2 \le 0$ 

Then  $\varphi(t_2) \leq t_2$  and  $-\varphi(s_2) \leq -s_2$ . Hence

$$\Sigma \le G(t_1 + t_2) + G(s_1 - s_2) \le G\left(\sup_{t \in T} t_1 + t_2\right) + G\left(\sup_{t \in T} t_1 - t_2\right).$$

Case  $3: t_2 \ge 0, s_2 \ge 0$ 

Case 3a:  $s_2 \le t_2$ 

It is enough to prove

$$G(t_1 + \varphi(t_2)) + G(s_1 - \varphi(s_2)) \le G(t_1 + t_2) + G(s_1 - s_2).$$

Note that  $s_2 - \varphi(s_2) \ge 0$  since  $s_2 \ge 0$  and  $\varphi$  – contraction. Since  $|\varphi(s)| \le |s|$ ,

$$s_1 - s_2 \le s_1 + \varphi(s_2) \le t_1 + \varphi(t_2),$$

where we use the fact that  $t_1, t_2$  attain maximum.

Furthermore,

$$G\left(\underbrace{(s_1 - s_2)}_{x} + \underbrace{(s_2 - \varphi(s_2))}_{x}\right) - G\left(s_1 - s_2\right) \le G\left((t_1 + \varphi(t_2)) + (s_2 - \varphi(s_2))\right) - G\left(t_1 + \varphi(t_2)\right)$$

Indeed,  $\Psi(u) = G(u+x) - G(u)$  is non-decreasing for  $x \ge 0$  since  $\Psi'(u) = G'(u+x) - G'(u) > 0$  by convexity of G.

Now,

$$(t_1 + \varphi(t_2)) + (s_2 - \varphi(s_2)) \le t_1 + t_2$$

since

$$\varphi(t_2) - \varphi(s_2) \le |t_2 - s_2| = t_2 - s_2.$$

Hence,

$$G(s_1 - \varphi(s_2)) - G(s_1 - s_2) = G((s_1 - s_2) + (s_2 - \varphi(s_2))) - G(s_1 - s_2)$$

$$\leq G(t_1 + t_2) - G(t_1 + \varphi(t_2)).$$

Case 3a:  $t_2 \le s_2$ 

$$\Sigma \le G(s_1 + s_2) + G(t_1 - t_2)$$

Again, it's enough to show

$$G(t_1 + \varphi(t_2)) - G(t_1 - t_2) \le G(s_1 + s_2) - G(s_1 - \varphi(s_2))$$

We have

$$t_1 - t_2 \le t_1 - \varphi(t_2) \le s_1 - \varphi(s_2)$$

since  $s_1, s_2$  achieves maximum and since  $t_2 + \varphi(t_2) \ge 0$  ( $\varphi$  is a contraction and  $t_2 \ge 0$ ). Hence,

$$G\left(\underbrace{(t_1 - t_2)}_{u} + \underbrace{(t_2 + \varphi(t_2))}_{x}\right) - G\left(t_1 - t_2\right) \le G\left((s_1 - \varphi(s_2)) + (t_2 + \varphi(t_2))\right) - G\left(s_1 - \varphi(s_2)\right)$$

Since

$$\varphi(t_2) - \varphi(s_2) \le |t_2 - s_2| = s_2 - t_2,$$

we get

$$\varphi(t_2) - \varphi(s_2) \le s_2 - t_2.$$

Therefore,

$$s_1 - \varphi(s_2) + (t_2 + \varphi(t_2) \le s_1 + s_2$$

and so

$$G(t_1 + \varphi(t_2)) - G(t_1 - t_2) \le G(s_1 + s_2) - G(s_1 - \varphi(s_2))$$

Case 4:  $t_2 \le 0, s_2 \le 0$ 

Proved in the same way as Case 3.

We now apply the theorem with  $G(s) = (s)^+$ .

*Proof.* Note that

Lemma 23.1.

$$|x| = (x)^{+} + (x)^{-} = (x)^{+} + (-x)^{+}.$$

We apply the Contraction Inequality for Rademacher processes with  $G(s) = (s)^+$ .

$$\mathbb{E}\sup_{t\in T} \left| \sum_{i=1}^{n} \varepsilon_{i} \varphi_{i}(t_{i}) \right| = \mathbb{E}\sup_{t\in T} \left( \left( \sum_{i=1}^{n} \varepsilon_{i} \varphi_{i}(t_{i}) \right)^{+} + \left( \sum_{i=1}^{n} (-\varepsilon_{i}) \varphi_{i}(t_{i}) \right)^{+} \right)$$

$$\leq 2\mathbb{E}\sup_{t\in T} \left( \sum_{i=1}^{n} \varepsilon_{i} \varphi_{i}(t_{i}) \right)^{+}$$

$$\leq 2\mathbb{E}\sup_{t\in T} \left( \sum_{i=1}^{n} \varepsilon_{i} t_{i} \right)^{+} \leq 2\mathbb{E}\sup_{t\in T} \left| \sum_{i=1}^{n} \varepsilon_{i} t_{i} \right|.$$

---

Let  $\mathcal{H}$  be a class of "simple" functions (VC-subgraph, perceptrons). Define recursively

$$\mathcal{H}_{i+1} = \left\{ \sigma \left( \sum \alpha_j h_j \right) : h_j \in \mathcal{H}_i, \ \alpha_j \in \mathbb{R} \right\}$$

where  $\sigma$  is sigmoid function such that  $\sigma(0) = 0$  and  $|\sigma(s) - \sigma(t)| \le L|s - t|, -1 \le \sigma \le 1$ . Example:

$$\sigma(x) = \frac{e^x - e^{-x}}{e^x + e^{-x}}.$$

Assume we have data  $(x_1, y_1), \ldots, (x_n, y_n), -1 \leq y_i \leq 1$ . We can minimize

$$\frac{1}{n} \sum_{i=1}^{n} (y_i - h(x_i))^2$$

over  $\mathcal{H}_k$ , where k is the number of layers.

Define  $\mathcal{L}(y, h(x)) = (y - h(x))^2$ ,  $0 \le \mathcal{L}(y, h(x)) \le 4$ . We want to bound  $\mathbb{E}\mathcal{L}(y, h(x))$ . From the previous lectures,

$$\sup \left| \mathbb{E} \mathcal{L}(y, h(x)) - \frac{1}{n} \sum_{i=1}^{n} \mathcal{L}(y_i, h(x_i)) \right| \le 2\mathbb{E} \sup \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_i \mathcal{L}(y_i, h(x_i)) \right| + 4\sqrt{\frac{2t}{n}}$$

with probability at least  $1 - e^{-t}$ .

Define

$$\mathcal{H}_{i+1}(A_1,\ldots,A_{i+1}) = \left\{ \sigma\left(\sum \alpha_j h_j\right) : \sum |\alpha_j| \le A_{i+1}, \ h_j \in \mathcal{H}_i \right\}.$$

For now, assume bounds  $A_i$  on sum of weights (although this is not true in practice, so we will take union bound later).

## Theorem 24.1.

$$\mathbb{E}\sup_{h\in\mathcal{H}_k(A_1,\ldots,A_k)}\left|\frac{1}{n}\sum_{i=1}^n\varepsilon_i\mathcal{L}(y_i,h(x_i))\right|\leq 8\prod_{j=1}^k(2L\cdot A_j)\cdot\mathbb{E}\sup_{h\in\mathcal{H}}\left|\frac{1}{n}\sum_{i=1}^n\varepsilon_ih(x_i)\right|+\frac{8}{\sqrt{n}}.$$

*Proof.* Since  $-2 \le y - h(x) \le 2$ ,  $\frac{(y-h(x))^2}{4} : [-2,2] \mapsto \mathbb{R}$  is a contraction because largest derivative of  $s^2$  on [-2,2] is 4. Hence,

$$\mathbb{E} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} (y_{i} - h(x_{i}))^{2} \right| = \mathbb{E} \mathbb{E}_{\varepsilon} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} (y_{i} - h(x_{i}))^{2} \right| \\
= 4 \mathbb{E} \mathbb{E}_{\varepsilon} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} \frac{(y_{i} - h(x_{i}))^{2}}{4} \right| \\
\leq 8 \mathbb{E} \mathbb{E}_{\varepsilon} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} (y_{i} - h(x_{i})) \right| \\
\leq 8 \mathbb{E} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} y_{i} \right| + 8 \mathbb{E} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h(x_{i}) \right| \\
\leq 8 \mathbb{E} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} y_{i} \right| + 8 \mathbb{E} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h(x_{i}) \right| \\
\leq 8 \mathbb{E} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} y_{i} \right| + 8 \mathbb{E} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h(x_{i}) \right| \\
\leq 8 \mathbb{E} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} y_{i} \right| + 8 \mathbb{E} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h(x_{i}) \right| \\
\leq 8 \mathbb{E} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} y_{i} \right| + 8 \mathbb{E} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h(x_{i}) \right|$$

Furthermore,

$$\mathbb{E}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}y_{i}\right| \leq \left(\mathbb{E}\left(\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}y_{i}\right)^{2}\right)^{1/2}$$

$$= \left(\mathbb{E}\sum_{i=1}^{n}\frac{1}{n^{2}}\varepsilon_{i}^{2}y_{i}^{2}\right)^{1/2}$$

$$= \left(\frac{1}{n}\mathbb{E}y_{1}^{2}\right)^{1/2} \leq \sqrt{\frac{1}{n}}$$

Using the fact that  $\sigma/L$  is a contraction,

$$\mathbb{E}_{\varepsilon} \sup_{h \in \mathcal{H}_{k}(A_{1}, \dots, A_{k})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} \sigma \left( \sum \alpha_{j} h_{j}(x_{i}) \right) \right| = L \mathbb{E}_{\varepsilon} \sup_{h} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} \frac{\sigma}{L} \left( \sum \alpha_{j} h_{j}(x_{i}) \right) \right| \\
\leq 2L \mathbb{E}_{\varepsilon} \sup_{h} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} \left( \sum \alpha_{j} h_{j}(x_{i}) \right) \right| \\
= 2L \mathbb{E}_{\varepsilon} \sup_{h} \left| \frac{1}{n} \sum_{j} \alpha_{j} \left( \sum_{i=1}^{n} \varepsilon_{i} h_{j}(x_{i}) \right) \right| \\
= 2L \mathbb{E}_{\varepsilon} \sup_{h} \left| \frac{\sum |\alpha_{j}|}{n} \sum_{i} \alpha'_{j} \left( \sum_{i=1}^{n} \varepsilon_{i} h_{j}(x_{i}) \right) \right| \\
= 2L \mathbb{E}_{\varepsilon} \sup_{h} \left| \frac{\sum |\alpha_{j}|}{n} \sum_{i} \alpha'_{j} \left( \sum_{i=1}^{n} \varepsilon_{i} h_{j}(x_{i}) \right) \right| \\
= 2L \mathbb{E}_{\varepsilon} \sup_{h} \left| \frac{\sum |\alpha_{j}|}{n} \sum_{i} \alpha'_{j} \left( \sum_{i=1}^{n} \varepsilon_{i} h_{j}(x_{i}) \right) \right| \\
= 2L \mathbb{E}_{\varepsilon} \sup_{h} \left| \frac{\sum |\alpha_{j}|}{n} \sum_{i} \alpha'_{j} \left( \sum_{i=1}^{n} \varepsilon_{i} h_{j}(x_{i}) \right) \right| \\
= 2L \mathbb{E}_{\varepsilon} \sup_{h} \left| \frac{\sum |\alpha_{j}|}{n} \sum_{i} \alpha'_{j} \left( \sum_{i=1}^{n} \varepsilon_{i} h_{j}(x_{i}) \right) \right|$$

where  $\alpha'_j = \frac{\alpha_j}{\sum_j |\alpha_j|}$ . Since  $\sum_j |\alpha_j| \le A_k$  for the layer k,

$$2L\mathbb{E}_{\varepsilon} \sup_{h \in \mathcal{H}_{k}(A_{1},\dots,A_{k})} \left| \frac{\sum |\alpha_{j}|}{n} \sum_{j} \alpha_{j}' \left( \sum_{i=1}^{n} \varepsilon_{i} h_{j}(x_{i}) \right) \right|$$

$$\leq 2LA_{k} \mathbb{E}_{\varepsilon} \sup_{h \in \mathcal{H}_{k}(A_{1},\dots,A_{k})} \left| \frac{1}{n} \sum_{j} \alpha_{j}' \left( \sum_{i=1}^{n} \varepsilon_{i} h_{j}(x_{i}) \right) \right|$$

$$= 2LA_{k} \mathbb{E}_{\varepsilon} \sup_{h \in \mathcal{H}_{k-1}(A_{1},\dots,A_{k-1})} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h_{j}(x_{i}) \right|$$

The last equality holds because  $\sup |\sum \lambda_j s_j| = \max_j |s_j|$ , i.e. max is attained at one of the vertices.

By induction,

$$\mathbb{E}\sup_{h\in\mathcal{H}_k(A_1,\ldots,A_k)}\left|\frac{1}{n}\sum_{i=1}^n\varepsilon_i(y_i-h(x_i))^2\right|\leq 8\prod_{j=1}^k(2LA_j)\cdot\mathbb{E}\sup_{h\in\mathcal{H}}\left|\frac{1}{n}\sum_{i=1}^n\varepsilon_ih(x_i)\right|+\frac{8}{\sqrt{n}},$$

where  $\mathcal{H}$  is the class of simple classifiers.

---

In Lecture 24 we proved

$$\mathbb{E}\sup_{h\in\mathcal{H}_k(A_1,\dots,A_k)}\left|\frac{1}{n}\sum_{i=1}^n\varepsilon_i(y_i-h(x_i))^2\right|\leq 8\prod_{i=1}^k(2LA_i)\cdot\mathbb{E}\sup_{h\in\mathcal{H}}\left|\frac{1}{n}\sum_{i=1}^n\varepsilon_ih(x_i)\right|+\frac{8}{\sqrt{n}}$$

Hence,

$$Z(\mathcal{H}_k(A_1, \dots, A_k)) := \sup_{h \in \mathcal{H}_k(A_1, \dots, A_k)} \left| \mathbb{E}\mathcal{L}(y, h(x)) - \frac{1}{n} \sum_{i=1}^n \mathcal{L}(y_i, h(x_i)) \right|$$
$$\leq 8 \prod_{j=1}^k (2LA_j) \cdot \mathbb{E} \sup_{h \in \mathcal{H}} \left| \frac{1}{n} \sum_{i=1}^n \varepsilon_i h(x_i) \right| + \frac{8}{\sqrt{n}} + 8\sqrt{\frac{t}{n}}$$

with probability at least  $1 - e^{-t}$ .

Assume  $\mathcal{H}$  is a VC-subgraph class,  $-1 \leq h \leq 1$ .

We had the following result:

$$\mathbb{P}_{\varepsilon}\left(\forall h \in \mathcal{H}, \ \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h(x_{i}) \leq \frac{K}{\sqrt{n}} \int_{0}^{\sqrt{\frac{1}{n} \sum_{i=1}^{n} h^{2}(x_{i})}} \log^{1/2} \mathcal{D}(\mathcal{H}, \varepsilon, d_{x}) d\varepsilon + K \sqrt{\frac{t}{n} \left(\frac{1}{n} \sum_{i=1}^{n} h^{2}(x_{i})\right)}\right) \geq 1 - e^{-t},$$

where

$$d_x(f,g) = \left(\frac{1}{n} \sum_{i=1}^n (f(x_i) - g(x_i))^2\right)^{1/2}.$$

Furthermore,

$$\mathbb{P}_{\varepsilon}\left(\forall h \in \mathcal{H}, \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h(x_{i}) \right| \leq \frac{K}{\sqrt{n}} \int_{0}^{\sqrt{\frac{1}{n} \sum_{i=1}^{n} h^{2}(x_{i})}} \log^{1/2} \mathcal{D}(\mathcal{H}, \varepsilon, d_{x}) d\varepsilon + K \sqrt{\frac{t}{n} \left(\frac{1}{n} \sum_{i=1}^{n} h^{2}(x_{i})\right)} \right) \geq 1 - 2e^{-t},$$

Since  $-1 \le h \le 1$  for all  $h \in \mathcal{H}$ ,

$$\mathbb{P}_{\varepsilon} \left( \sup_{h \in \mathcal{H}} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h(x_{i}) \right| \leq \frac{K}{\sqrt{n}} \int_{0}^{1} \log^{1/2} \mathcal{D}(\mathcal{H}, \varepsilon, d_{x}) d\varepsilon + K \sqrt{\frac{t}{n}} \right) \geq 1 - 2e^{-t},$$

Since  $\mathcal{H}$  is a VC-subgraph class with  $VC(\mathcal{H}) = V$ ,

$$\log \mathcal{D}(\mathcal{H}, \varepsilon, d_x) \le KV \log \frac{2}{\varepsilon}.$$

Hence,

$$\int_{0}^{1} \log^{1/2} \mathcal{D}(\mathcal{H}, \varepsilon, d_{x}) d\varepsilon \leq \int_{0}^{1} \sqrt{KV \log \frac{2}{\varepsilon}} d\varepsilon$$
$$\leq K\sqrt{V} \int_{0}^{1} \sqrt{\log \frac{2}{\varepsilon}} d\varepsilon \leq K\sqrt{V}$$

Let  $\xi \geq 0$  be a random variable. Then

$$\mathbb{E}\xi = \int_0^\infty \mathbb{P}\left(\xi \ge t\right) dt = \int_0^a \mathbb{P}\left(\xi \ge t\right) dt + \int_a^\infty \mathbb{P}\left(\xi \ge t\right) dt$$
$$\le a + \int_a^\infty \mathbb{P}\left(\xi \ge t\right) dt = a + \int_0^\infty \mathbb{P}\left(\xi \ge a + u\right) du$$

Let  $K\sqrt{\frac{V}{n}} = a$  and  $K\sqrt{\frac{t}{n}} = u$ . Then  $e^{-t} = e^{-\frac{nu^2}{K^2}}$ . Hence, we have

$$\mathbb{E}_{\varepsilon} \sup_{h \in \mathcal{H}} \left| \frac{1}{n} \sum_{i=1}^{n} \varepsilon_{i} h(x_{i}) \right| \leq K \sqrt{\frac{V}{n}} + \int_{0}^{\infty} 2e^{-\frac{nu^{2}}{K^{2}}} du$$

$$= K \sqrt{\frac{V}{n}} + \int_{0}^{\infty} \frac{K}{\sqrt{n}} e^{-x^{2}} dx$$

$$\leq K \sqrt{\frac{V}{n}} + \frac{K}{\sqrt{n}} \leq K \sqrt{\frac{V}{n}}$$

for  $V \ge 2$ . We made a change of variable so that  $x^2 = \frac{nu^2}{K^2}$ . Constants K change their values from line to line.

We obtain,

$$Z\left(\mathcal{H}_k(A_1,\ldots,A_k)\right) \le K \prod_{j=1}^k (2LA_j) \cdot \sqrt{\frac{V}{n}} + \frac{8}{\sqrt{n}} + 8\sqrt{\frac{t}{n}}$$

with probability at least  $1 - e^{-t}$ .

Assume that for any  $j, A_j \in (2^{-\ell_j-1}, 2^{-\ell_j}]$ . This defines  $\ell_j$ . Let

$$\mathcal{H}_k(\ell_1,\ldots,\ell_k) = \bigcup \{\mathcal{H}_k(A_1,\ldots,A_k) : A_j \in (2^{-\ell_j-1},2^{-\ell_j})\}.$$

Then the empirical process

$$Z\left(\mathcal{H}_k(\ell_1,\ldots,\ell_k)\right) \le K \prod_{j=1}^k (2L \cdot 2^{-\ell_j}) \cdot \sqrt{\frac{V}{n}} + \frac{8}{\sqrt{n}} + 8\sqrt{\frac{t}{n}}$$

with probability at least  $1 - e^{-t}$ .

For a given sequence  $(\ell_1, \ldots, \ell_k)$ , redefine t as  $t + 2 \sum_{j=1}^k \log |w_j|$  where  $w_j = \ell_j$  if  $\ell_j \neq 0$  and  $w_j = 1$  if  $\ell_j = 0$ .

With this t,

$$Z(\mathcal{H}_k(\ell_1,\ldots,\ell_k)) \le K \prod_{j=1}^k (2L \cdot 2^{-\ell_j}) \cdot \sqrt{\frac{V}{n}} + \frac{8}{\sqrt{n}} + 8\sqrt{\frac{t + 2\sum_{j=1}^k \log|w_j|}{n}}$$

with probability at least

$$1 - e^{-t - 2\sum_{j=1}^{k} \log|w_j|} = 1 - \prod_{j=1}^{k} \frac{1}{|w_j|^2} e^{-t}.$$

By union bound, the above holds for all  $\ell_1, \ldots, \ell_k \in \mathcal{Z}$  with probability at least

$$1 - \sum_{\ell_1, \dots, \ell_k \in \mathcal{Z}} \prod_{j=1}^k \frac{1}{|w_j|^2} e^{-t} = 1 - \left( \sum_{\ell_1 \in \mathcal{Z}} \frac{1}{|w_1|^2} \right)^k e^{-t}$$
$$= 1 - \left( 1 + 2\frac{\pi^2}{6} \right)^k e^{-t} \ge 1 - 5^k e^{-t} = 1 - e^{-u}$$

for  $t = u + k \log 5$ .

Hence, with probability at least  $1 - e^{-u}$ ,

$$\forall (\ell_1, \dots, \ell_k), \ Z(\mathcal{H}_k(\ell_1, \dots, \ell_k)) \le K \prod_{j=1}^k (2L \cdot 2^{-\ell_j}) \cdot \sqrt{\frac{V}{n}} + \frac{8}{\sqrt{n}} + 8\sqrt{\frac{2\sum_{j=1}^k \log|w_j| + k \log 5 + u}{n}}.$$

If  $A_j \in (2^{-\ell_j-1}, 2^{-\ell_j}]$ , then  $-\ell_j - 1 \le \log A_j \le \ell_j$  and  $|\ell_j| \le |\log A_j| + 1$ . Hence,  $|w_j| \le |\log A_j| + 1$ . Therefore, with probability at least  $1 - e^{-u}$ ,

$$\forall (A_1, \dots, A_k), \ Z(\mathcal{H}_k(A_1, \dots, A_k)) \le K \prod_{j=1}^k (4L \cdot A_j) \cdot \sqrt{\frac{V}{n}} + \frac{8}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} + \frac{1}{\sqrt{n}} +$$

Notice that  $\log(|\log A_j| + 1)$  is large when  $A_j$  is very large or very small. This is penalty and we want the product term to be dominating. But  $\log\log A_j \leq 5$  for most practical applications.

---

**Lemma 26.1.** *For*  $0 \le r \le 1$ ,

$$\inf_{0 \le \lambda \le 1} e^{\frac{1}{4}(1-\lambda)^2} r^{-\lambda} \le 2 - r.$$

*Proof.* Taking log, we need to show

$$\inf_{0 \le \lambda \le 1} \left( \frac{1}{4} (1 - \lambda)^2 - \lambda \log r - \log(2 - r) \right) \le 0.$$

Taking derivative with respect to  $\lambda$ ,

$$-\frac{1}{2}(1-\lambda) - \log r = 0$$
$$\lambda = 1 + 2\log r \le 1$$
$$0 \le \lambda = 1 + 2\log r$$

Hence,

$$e^{-1/2} < r$$
.

Take

$$\lambda = \begin{cases} 1 + 2\log r & e^{-1/2} \le r \\ 0 & e^{-1/2} \ge r \end{cases}$$

Case a):  $r \le e^{-1/2}$ ,  $\lambda = 0$ 

$$\frac{1}{4} - \log(2 - r) \le 0 \iff r \le 2 - e^{\frac{1}{4}}. \quad e^{-1/2} \le 2 - e^{\frac{1}{4}}.$$

Case a):  $r \ge e^{-1/2}$ ,  $\lambda = 1 + 2 \log r$ 

$$(\log r)^2 - \log r - 2(\log r)^2 - \log(2 - r) \le 0$$

Let

$$f(r) = \log(2 - r) + \log r + (\log r)^{2}.$$

Is  $f(r) \ge 0$ ? Enough to prove  $f'(r) \le 0$ . Is

$$f'(r) = -\frac{1}{2-r} + \frac{1}{r} + 2\log r \cdot \frac{1}{r} \le 0.$$

$$rf'(r) = -\frac{r}{2-r} + 1 + 2\log r \le 0.$$

Enough to show  $(rf'(r))' \geq 0$ :

$$(rf'(r))' = \frac{2}{r} - \frac{2-r+r}{(2-r)^2} = \frac{2}{r} - \frac{2}{(2-r)^2}.$$

Let  $\mathcal{X}$  be a set (space of examples) and P a probability measure on  $\mathcal{X}$ . Let  $x_1, \ldots, x_n$  be i.i.d.,  $(x_1, \ldots, x_n) \in \mathcal{X}^n$ ,  $P^n = P \times \ldots \times P$ .

Consider a subset  $A \in \mathcal{X}^n$ . How can we define a distance from  $x \in \mathcal{X}^n$  to A? Example: hamming distance between two points  $d(x,y) = \sum I(x_i \neq y_1)$ .

We now define convex hull distance.

**Definition 26.1.** Define V(A, x), U(A, x), and d(A, x) as follows:

(1) 
$$V(A, x) = \{(s_1, \dots, s_n) : s_i \in \{0, 1\}, \exists y \in A \text{ s.t. } if s_i = 0 \text{ then } x_i = y_i\}$$

$$x = (x_1, x_2, \dots, x_n)$$

$$= \neq \dots =$$

$$y = (y_1, y_2, \dots, y_n)$$

$$s = (0, 1, \dots, 0)$$

Note that it can happen that  $x_i = y_i$  but  $s_i \neq 0$ .

(2) 
$$U(A,x) = conv \ V(A,x) = \{ \sum \lambda_i u^i, \ u^i = (u_1^i, \dots, u_n^i) \in V(A,x), \ \lambda_i \ge 0, \ \sum \lambda_i = 1 \}$$

(3) 
$$d(A, x) = \min_{u \in U(A, x)} |u|^2 = \min_{u \in U(A, x)} \sum_{i=1}^{n} u_i^2$$

Theorem 26.1.

$$\mathbb{E}e^{\frac{1}{4}d(A,x)} = \int e^{\frac{1}{4}d(A,x)} dP^{n}(x) \le \frac{1}{P^{n}(A)}$$

and

$$P^{n}(d(A,x) \ge t) \le \frac{1}{P^{n}(A)}e^{-t/4}.$$

*Proof.* Proof is by induction on n.

n = 1:

$$d(A, x) = \begin{cases} 0, & x \in A \\ 1, & x \notin A \end{cases}$$

Hence,

$$\int e^{\frac{1}{4}d(A,x)}dP^n(x) = P(A) \cdot 1 + (1 - P(A))e^{\frac{1}{4}} \le \frac{1}{P(A)}$$

because

$$e^{\frac{1}{4}} \le \frac{1 + P(A)}{P(A)}.$$

 $\mathbf{n} \rightarrow \mathbf{n+1}:$ 

Let  $x = (x_1, \dots, x_n, x_{n+1}) = (z, x_{n+1})$ . Define

$$A(x_{n+1}) = \{(y_1, \dots, y_n) : (y_1, \dots, y_n, x_{n+1}) \in A\}$$

and

$$B = \{(y_1, \dots, y_n) : \exists y_{n+1}, (y_1, \dots, y_n, y_{n+1}) \in A\}$$

One can verify that

$$s \in U(A(x_{n+1}, z)) \Rightarrow (s, 0) \in U(A, (z, x_{n+1}))$$

and

$$t \in U(B, z) \Rightarrow (t, 1) \in U(A, (z, x_{n+1})).$$

Take  $0 \le \lambda \le 1$ . Then

$$\lambda(s,0) + (1-\lambda)(t,1) \in U(A,(z,x_{n+1}))$$

since  $U(A,(z,x_{n+1}))$  is convex. Hence,

$$d(A, (z, x_{n+1})) = d(A, x) \le |\lambda(s, 0) + (1 - \lambda)(t, 1)|^2$$

$$= \sum_{i=1}^{n} (\lambda s_i + (1 - \lambda)t_i)^2 + (1 - \lambda)^2$$

$$\le \lambda \sum_{i=1}^{n} s_i^2 + (1 - \lambda) \sum_{i=1}^{n} t_i^2 + (1 - \lambda)^2$$

So,

$$d(A, x) \le \lambda d(A(x_{n+1}), z) + (1 - \lambda)d(B, z) + (1 - \lambda)^{2}.$$

Now we can use induction:

$$\int e^{\frac{1}{4}d(A,x)}dP^{n+1}(x) = \int_{\mathcal{X}} \int_{\mathcal{X}^n} e^{\frac{1}{4}d(A,(z,x_{n+1}))}dP^n(z)dP(x_{n+1}).$$

Then inner integral is

$$\int_{\mathcal{X}^n} e^{\frac{1}{4}d(A,(z,x_{n+1}))} dP^n(z) \le \int_{\mathcal{X}^n} e^{\frac{1}{4}\left(\lambda d(A(x_{n+1}),z) + (1-\lambda)d(B,z) + (1-\lambda)^2\right)} dP^n(z) 
= e^{\frac{1}{4}(1-\lambda)^2} \int e^{\left(\frac{1}{4}d(A(x_{n+1}),z)\right)\lambda + \left(\frac{1}{4}d(B,z)\right)(1-\lambda)} dP^n(z)$$

We now use  $H\ddot{o}lder$ 's inequality:

$$\int fgdP \leq \left(\int f^p dP\right)^{1/p} \left(\int g^q dP\right)^{1/q} \text{ where } \frac{1}{p} + \frac{1}{q} = 1$$

$$e^{\frac{1}{4}(1-\lambda)^{2}} \int e^{\left(\frac{1}{4}d(A(x_{n+1}),z)\right)\lambda + \left(\frac{1}{4}d(B,z)\right)(1-\lambda)} dP^{n}(z)$$

$$\leq e^{\frac{1}{4}(1-\lambda)^{2}} \left(\int e^{\frac{1}{4}d(A(x_{n+1}),z)} dP^{n}(z)\right)^{\lambda} \left(e^{\frac{1}{4}d(B,z)} dP^{n}(z)\right)^{1-\lambda}$$

$$\leq \text{(by ind. hypoth.)} \quad e^{\frac{1}{4}(1-\lambda)^{2}} \left(\frac{1}{P^{n}(A(x_{n+1}))}\right)^{\lambda} \left(\frac{1}{P^{n}(B)}\right)^{1-\lambda}$$

$$= \frac{1}{P^{n}(B)} e^{\frac{1}{4}(1-\lambda)^{2}} \left(\frac{P^{n}(A(x_{n+1}))}{P^{n}(B)}\right)^{-\lambda}$$

Optimizing over  $\lambda \in [0,1]$ , we use the Lemma proved in the beginning of the lecture with

$$0 \le r = \frac{P^n(A(x_{n+1}))}{P^n(B)} \le 1.$$

Thus,

$$\frac{1}{P^n(B)}e^{\frac{1}{4}(1-\lambda)^2}\left(\frac{P^n(A(x_{n+1}))}{P^n(B)}\right)^{-\lambda} \le \frac{1}{P^n(B)}\left(2 - \frac{P^n(A(x_{n+1}))}{P^n(B)}\right).$$

Now, integrate over the last coordinate. When averaging over  $x_{n+1}$ , we get measure of A.

$$\int e^{\frac{1}{4}d(A,x)} dP^{n+1}(x) = \int_{\mathcal{X}} \int_{\mathcal{X}^n} e^{\frac{1}{4}d(A,(z,x_{n+1}))} dP^n(z) dP(x_{n+1})$$

$$\leq \int_{\mathcal{X}} \frac{1}{P^n(B)} \left( 2 - \frac{P^n(A(x_{n+1}))}{P^n(B)} \right) dP(x_{n+1})$$

$$= \frac{1}{P^n(B)} \left( 2 - \frac{P^{n+1}(A)}{P^n(B)} \right)$$

$$= \frac{1}{P^{n+1}(A)} \frac{P^{n+1}(A)}{P^n(B)} \left( 2 - \frac{P^{n+1}(A)}{P^n(B)} \right)$$

$$\leq \frac{1}{P^{n+1}(A)}$$

because  $x(2-x) \le 1$  for  $0 \le x \le 1$ .

---

Let  $\mathcal{X} = \{0, 1\}, (x_1, \dots, x_n) \in \{0, 1\}^n, \mathbb{P}(x_i = 1) = p, \text{ and } \mathbb{P}(x_i = 0) = 1 - p.$  Suppose  $A \subseteq \{0, 1\}^n$ . What is d(A, x) in this case?

For a given x, take all  $y \in A$  and compute s:

$$x = ( x_1, x_2, \dots, x_n )$$
  
 $= \neq \dots =$   
 $y = ( y_1, y_2, \dots, y_n )$   
 $s = ( 0, 1, \dots, 0 )$ 

Build conv V(A, x) = U(A, x). Finally,  $d(A, x) = \min\{|x - u|^2; u \in \text{conv } A\}$ 

**Theorem 27.1.** Consider a convex and Lipschitz  $f : \mathbb{R}^n \to \mathbb{R}$ ,  $|f(x) - f(y)| \leq L|x - y|$ ,  $\forall x, y \in \mathbb{R}^n$ . Then

$$\mathbb{P}\left(f(x_1,\ldots,x_n) \ge M + L\sqrt{t}\right) \le 2e^{-t/4}$$

and

$$\mathbb{P}\left(f(x_1,\ldots,x_n) \le M - L\sqrt{t}\right) \le 2e^{-t/4}$$

where M is median of  $f \colon \mathbb{P}\left(f \geq M\right) \geq 1/2$  and  $\mathbb{P}\left(f \leq M\right) \geq 1/2$ .

*Proof.* Fix  $a \in \mathbb{R}$  and consider  $A = \{(x_1, \dots, x_n) \in \{0, 1\}^n, f(x_1, \dots, x_n) \leq a\}$ . We proved that

$$\mathbb{P}\left(\underbrace{d(A,x) \ge t}_{\text{event } E}\right) \le \frac{1}{\mathbb{P}(A)}e^{-t/4} = \frac{1}{\mathbb{P}(f \le a)}e^{-t/4}$$

$$d(A, x) = \min\{|x - u|^2; u \in \text{conv } A\} = |x - u_0|^2$$

for some  $u_0 \in \text{conv } A$ . Note that  $|f(x) - f(u_0)| \le L|x - u_0|$ .

Now, assume that x is such that  $d(A, x) \leq t$ , i.e. complement of event E. Then  $|x - u_0| = \sqrt{d(A, x)} \leq \sqrt{t}$ . Hence,

$$|f(x) - f(u_0)| \le L|x - u_0| \le L\sqrt{t}.$$

So,  $f(x) \leq f(u_0) + L\sqrt{t}$ . What is  $f(u_0)$ ? We know that  $u_0 \in \text{conv } A$ , so  $u_0 = \sum \lambda_i a_i$ ,  $a_i \in A$ , and  $\lambda_i \geq 0$ ,  $\sum \lambda_i = 1$ . Since f is convex,

$$f(u_0) = f\left(\sum \lambda_i a_i\right) \le \sum \lambda_i f(a_i) \le \sum \lambda_i a = a.$$

This implies  $f(x) \leq a + L\sqrt{t}$ . We proved

$${d(A, x) \le t} \subseteq {f(x) \le a + L\sqrt{t}}.$$

Hence,

$$1 - \frac{1}{\mathbb{P}(f \ge a)} e^{-t/4} \le \mathbb{P}(d(A, x) \le t) \le \mathbb{P}\left(f(x) \le a + L\sqrt{t}\right).$$

Therefore,

$$\mathbb{P}\left(f(x) \ge a + L\sqrt{t}\right) \le \frac{1}{\mathbb{P}\left(f \ge a\right)}e^{-t/4}.$$

To prove the first inequality take a = M. Since  $\mathbb{P}(f \leq M) \geq 1/2$ ,

$$\mathbb{P}\left(f(x) \ge M + L\sqrt{t}\right) \le 2e^{-t/4}.$$

To prove the second inequality, take  $a = M - L\sqrt{t}$ . Then

$$\mathbb{P}\left(f \ge M\right) \le \frac{1}{\mathbb{P}\left(f \le M - L\sqrt{t}\right)}e^{-t/4},$$

which means

$$\mathbb{P}\left(f(x) \le M - L\sqrt{t}\right) \le 2e^{-t/4}.$$

**Example 1.** Let  $H \subseteq \mathbb{R}^n$  be a bounded set. Let

$$f(x_1,\ldots,x_n) = \sup_{h\in\mathcal{H}} \left| \sum_{i=1}^n h_i x_i \right|.$$

Let's check:

(1) convexity:

$$f(\lambda x + (1 - \lambda)y) = \sup_{h \in \mathcal{H}} \left| \sum_{i=1}^{n} h_i (\lambda x_i + (1 - \lambda)y_i) \right|$$

$$= \sup_{h \in \mathcal{H}} \left| \lambda \sum_{i=1}^{n} h_i x_i + (1 - \lambda) \sum_{i=1}^{n} h_i y_i \right|$$

$$\leq \lambda \sup_{h \in \mathcal{H}} \left| \sum_{i=1}^{n} h_i x_i \right| + (1 - \lambda) \sup_{h \in \mathcal{H}} \left| \sum_{i=1}^{n} h_i y_i \right|$$

$$= \lambda f(x) + (1 - \lambda) f(y)$$

(2) Lipschitz:

$$|f(x) - f(y)| = \left| \sup_{h \in \mathcal{H}} \left| \sum_{i=1}^{n} h_{i} x_{i} \right| - \sup_{h \in \mathcal{H}} \left| \sum_{i=1}^{n} h_{i} y_{i} \right| \right|$$

$$\leq \sup_{h \in \mathcal{H}} \left| \sum_{i=1}^{n} h_{i} (x_{i} - y_{i}) \right|$$

$$\leq (by \ Cauchy\text{-}Schwartz) \quad \sup_{h \in \mathcal{H}} \sqrt{\sum_{i=1}^{n} h_{i}^{2}} \sqrt{\sum_{i=1}^{n} (x_{i} - y_{i})^{2}}$$

$$= |x - y| \quad \sup_{h \in \mathcal{H}} \sqrt{\sum_{i=1}^{n} h_{i}^{2}}$$

$$L = Lipschitz \ constant$$

We proved the following

**Theorem 27.2.** If M is the median of  $f(x_1, ..., x_n)$ , and  $x_1, ..., x_n$  are i.i.d with  $\mathbb{P}(x_i = 1) = p$  and  $\mathbb{P}(x_i = 0) = 1 - p$ , then

$$\mathbb{P}\left(\sup_{h\in\mathcal{H}}\left|\sum_{i=1}^n h_i x_i\right| \ge M + \sup_{h\in\mathcal{H}} \sqrt{\sum_{i=1}^n h_i^2} \cdot \sqrt{t}\right) \le 2e^{-t/4}$$

and

$$\mathbb{P}\left(\sup_{h\in\mathcal{H}}\left|\sum_{i=1}^n h_i x_i\right| \le M - \sup_{h\in\mathcal{H}} \sqrt{\sum_{i=1}^n h_i^2} \cdot \sqrt{t}\right) \le 2e^{-t/4}$$

---

Assume we have space  $\mathcal{X}$  and a class of functions  $\mathcal{F} = \{f : \mathcal{X} \mapsto \mathbb{R}\}$ , not necessarily bounded. Define

$$Z(x) = Z(x_1, \dots, x_n) = \sup_{f \in \mathcal{F}} \sum f(x_i)$$

(or  $\sup_{f \in \mathcal{F}} |\sum f(x_i)|$ ).

**Example 1.**  $f \to \frac{1}{n}(f - \mathbb{E}f)$ .  $Z(x) = \sup_{f \in \mathcal{F}} \frac{1}{n} \sum_{i=1}^{n} f(x_i) - \mathbb{E}f$ .

Consider  $x' = (x'_1, \dots, x'_n)$ , an independent copy of x. Let

$$V(x) = \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(x_i) - f(x'_i))^2$$

be "random uniform variance" (unofficial name)

## Theorem 28.1.

$$\mathbb{P}\left(Z(x) \ge \mathbb{E}Z(x) + 2\sqrt{V(x)t}\right) \le 4e \cdot e^{-t/4}$$
$$\mathbb{P}\left(Z(x) \le \mathbb{E}Z(x) - 2\sqrt{V(x)t}\right) \le 4e \cdot e^{-t/4}$$

Recall the Symmetrization lemma:

**Lemma 28.1.** $\xi_1, \xi_2, \xi_3(x, x') : \mathcal{X} \times \mathcal{X} \mapsto \mathbb{R}, \ \xi_i' = \mathbb{E}_{x'} \xi_i$ . If

$$\mathbb{P}\left(\xi_1 \ge \xi_2 + \sqrt{\xi_3 t}\right) \le \Gamma e^{-\gamma t},$$

then

$$\mathbb{P}\left(\xi_1' \ge \xi_2' + \sqrt{\xi_3't}\right) \le \Gamma e \cdot e^{-\gamma t}.$$

We have

$$\mathbb{E}Z(x) = \mathbb{E}_{x'}Z(x') = \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} f(x'_i)$$

and

$$V(x) = \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(x_i) - f(x'_i))^2.$$

Use the Symmetrization Lemma with  $\xi_1 = Z(x)$ ,  $\xi_2 = Z(x')$ , and

$$\xi_3 = \sup_{f \in \mathcal{F}} \sum_{i=1}^n (f(x_i) - f(x_i'))^2.$$

It is enough to prove that

$$\mathbb{P}\left(Z(x) \ge Z(x') + 2\sqrt{t \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(x_i) - f(x_i'))^2}\right) \le 4e^{-t/4},$$

i.e.

$$\mathbb{P}\left(\sup_{f \in \mathcal{F}} \sum_{i=1}^{n} f(x_i) \ge \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} f(x_i') + 2\sqrt{t \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(x_i) - f(x_i'))^2}\right) \le 4e^{-t/4}.$$

If we switch  $x_i \leftrightarrow x_i'$ , nothing changes, so we can switch randomly. Implement the permutation  $x_i \leftrightarrow x_i'$ :

$$I = f(x_i') + \varepsilon_i (f(x_i) - f(x_i'))$$

$$II = f(x_i) - \varepsilon_i (f(x_i) - f(x_i'))$$

where  $\varepsilon_i = 0, 1$ . Hence,

(1) If 
$$\varepsilon_i = 1$$
, then  $I = f(x_i)$  and  $II = f(x'_i)$ .

(2) If 
$$\varepsilon_i = 0$$
, then  $I = f(x_i')$  and  $II = f(x_i)$ .

Take  $\varepsilon_1 \dots \varepsilon_n$  i.i.d. with  $\mathbb{P}(\varepsilon_i = 0) = \mathbb{P}(\varepsilon_i = 1) = 1/2$ .

$$\mathbb{P}_{x,x'}\left(\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}f(x_i)\geq\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}f(x_i')+2\sqrt{t\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}(f(x_i)-f(x_i'))^2}\right)$$

$$=\mathbb{P}_{x,x',\varepsilon}\left(\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}(f(x_i')+\varepsilon_i(f(x_i)-f(x_i')))\geq\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}(f(x_i)-\varepsilon_i(f(x_i)-f(x_i')))\right)$$

$$+2\sqrt{t\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}(f(x_i)-f(x_i'))^2}$$

$$=\mathbb{E}_{x,x'}\mathbb{P}_{\varepsilon}\left(\sup_{f\in\mathcal{F}}\ldots\geq\sup_{f\in\mathcal{F}}\ldots+2\sqrt{\ldots}\text{ for fixed }x,x'\right)$$

Define

$$\Phi_1(\varepsilon) = \sup_{f \in \mathcal{F}} \sum_{i=1}^n (f(x_i') + \varepsilon_i (f(x_i) - f(x_i')))$$

and

$$\Phi_2(\varepsilon) = \sup_{f \in \mathcal{F}} \sum_{i=1}^n (f(x_i) - \varepsilon_i (f(x_i) - f(x_i'))).$$

 $\Phi_1(\varepsilon), \Phi_2(\varepsilon)$  are convex and Lipschitz with  $L = \sup_{f \in \mathcal{F}} \sqrt{\sum_{i=1}^n (f(x_i) - f(x_i'))^2}$ . Moreover,  $Median(\Phi_1) = Median(\Phi_2)$  and  $\Phi_1(\varepsilon_1, \dots, \varepsilon_n) = \Phi_2(1 - \varepsilon_1, \dots, 1 - \varepsilon_n)$ . Hence,

$$\mathbb{P}_{\varepsilon}\left(\Phi_{1} \leq M(\Phi_{1}) + L\sqrt{t}\right) \geq 1 - 2e^{-t/4}$$

and

$$\mathbb{P}_{\varepsilon}\left(\Phi_2 \le M(\Phi_2) - L\sqrt{t}\right) \ge 1 - 2e^{-t/4}.$$

With probability at least  $1 - 4e^{-t/4}$  both above inequalities hold:

$$\Phi_1 \le M(\Phi_1) + L\sqrt{t} = M(\Phi_2) + L\sqrt{t} \le \Phi_2 + 2L\sqrt{t}.$$

Thus,

$$\mathbb{P}_{\varepsilon}\left(\Phi_1 \ge \Phi_2 + 2L\sqrt{t}\right) \le 4e^{-t/4}$$

and

$$\mathbb{P}_{x,x',\varepsilon}\left(\Phi_1 \ge \Phi_2 + 2L\sqrt{t}\right) \le 4e^{-t/4}.$$

The "random uniform variance" is

$$V(x) = \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(x_i) - f(x'_i))^2.$$

For example, if  $\mathcal{F} = \{f\}$ , then

$$\frac{1}{n}V(x) = \frac{1}{n}\mathbb{E}_{x'}\sum_{i=1}^{n}(f(x_i) - f(x'_i))^2$$

$$\frac{1}{n}\sum_{i=1}^{n}\left(f(x_i)^2 - 2f(x_i)\mathbb{E}f + \mathbb{E}f^2\right)$$

$$= \bar{f}^2 - 2\bar{f}\mathbb{E}f + \mathbb{E}f^2$$

$$= \underbrace{\bar{f}^2 - (\bar{f})^2}_{\text{sample variance}} + \underbrace{(\bar{f})^2 - 2\bar{f}\mathbb{E}f + (\mathbb{E}f)^2}_{\text{(}\bar{f} - \mathbb{E}f)^2} + \underbrace{\mathbb{E}f^2 - (\mathbb{E}f)^2}_{\text{variance}}$$

---

Let  $x \in \mathcal{X}^n$ . Suppose  $A_1, A_2 \subseteq \mathcal{X}^n$ . We want to define  $d(A_1, A_2, x)$ .

## Definition 29.1.

$$d(A_1, A_2, x) = \inf\{card \{i \leq n : x_i \neq y_i^1 \text{ and } x_i \neq y_i^2\}, y^1 \in A_1, y^2 \in A_2\}$$

## Theorem 29.1.

$$\mathbb{E}2^{d(A_1, A_2, x)} = \int 2^{d(A_1, A_2, x)} dP^n(x) \le \frac{1}{P^n(A_1)P^n(A_2)}$$

and

$$\mathbb{P}(d(A_1, A_2, x) \ge t) \le \frac{1}{P^n(A_1)P^n(A_2)} \cdot 2^{-t}$$

We first prove the following lemma:

**Lemma 29.1.** Let  $0 \le g_1, g_2 \le 1, g_i : \mathcal{X} \mapsto [0, 1]$ . Then

$$\int \min\left(2, \frac{1}{g_1(x)}, \frac{1}{g_2(x)}\right) dP(x) \cdot \int g_1(x) dP(x) \cdot \int g_2(x) dP(x) \le 1$$

*Proof.* Notice that  $\log x \le x - 1$ .

So enough to show

$$\int \min\left(2, \frac{1}{g_1}, \frac{1}{g_2}\right) dP + \int g_1 dP + \int g_2 dP \le 3$$

which is the same as

$$\int \left[ \min\left(2, \frac{1}{g_1}, \frac{1}{g_2}\right) + g_1 + g_2 \right] dP \le 3$$

It's enough to show

$$\min\left(2, \frac{1}{g_1}, \frac{1}{g_2}\right) + g_1 + g_2 \le 3.$$

If min is equal to 2, then  $g_1, g_2 \leq \frac{1}{2}$  and the sum is less than 3.

If min is equal to  $\frac{1}{g_1}$ , then  $g_1 \ge \frac{1}{2}$  and  $g_1 \ge g_2$ , so  $\min + g_1 + g_2 \le \frac{1}{g_1} + 2g_1 \le 3$ .

We now prove the Theorem:

*Proof.* Proof by induction on n.

n = 1:

$$d(A_1, A_2, x) = 0$$
 if  $x \in A_1 \cup A_2$  and  $d(A_1, A_2, x) = 1$  otherwise

$$\int 2^{d(A_1, A_2, x)} dP(x) = \int \min\left(2, \frac{1}{I(x \in A_1)}, \frac{1}{I(x \in A_2)}\right) dP(x)$$

$$\leq \frac{1}{\int I(x \in A_1) dP(x) \cdot \int I(x \in A_2) dP(x)}$$

$$= \frac{1}{P(A_1)P(A_2)}$$

 $\mathbf{n} \rightarrow \mathbf{n} + \mathbf{1}$ :

Let  $x \in \mathcal{X}^{n+1}$ ,  $A_1, A_2 \subseteq \mathcal{X}^{n+1}$ . Denote  $x = (x_1, \dots, x_n, x_{n+1}) = (z, x_{n+1})$ .

Define

$$A_1(x_{n+1}) = \{ z \in \mathcal{X}^n : (z, x_{n+1}) \in A_1 \}$$

$$A_2(x_{n+1}) = \{ z \in \mathcal{X}^n : (z, x_{n+1}) \in A_2 \}$$

and

$$B_1 = \bigcup_{x_{n+1}} A_1(x_{n+1}), \quad B_2 = \bigcup_{x_{n+1}} A_2(x_{n+1})$$

Then

$$d(A_1, A_2, x) = d(A_1, A_2, (z, x_{n+1})) \le 1 + d(B_1, B_2, z),$$
  
$$d(A_1, A_2, (z, x_{n+1})) \le d(A_1(x_{n+1}), B_2, z),$$

and

$$d(A_1, A_2, (z, x_{n+1})) \le d(B_1, A_2(x_{n+1}), z).$$

Now,

$$\int 2^{d(A_1, A_2, x)} dP^{n+1}(z, x_{n+1}) = \int \underbrace{\int 2^{d(A_1, A_2, (z, x_{n+1}))} dP^n(z)}_{I(x_{n+1})} dP^n(z) dP(x_{n+1})$$

The inner integral can e bounded by induction as follows

$$I(x_{n+1}) \le \int 2^{1+d(B_1, B_2, z)} dP^n(z)$$

$$= 2 \int 2^{d(B_1, B_2, z)} dP^n(z)$$

$$\le 2 \cdot \frac{1}{P^n(B_1)P^n(B_2)}$$

Moreover, by induction,

$$I(x_{n+1}) \le \int 2^{d(A_1(x_{n+1}),B_2,z)} dP^n(z) \le \frac{1}{P^n(A_1(x_{n+1}))P^n(B_2)}$$

and

$$I(x_{n+1}) \le \int 2^{d(B_1, A_2(x_{n+1}), z)} dP^n(z) \le \frac{1}{P^n(B_1)P^n(A_2(x_{n+1}))}$$

Hence,

$$I(x_{n+1}) \leq \min\left(\frac{2}{P^n(B_1)P^n(B_2)}, \frac{1}{P^n(A_1(x_{n+1}))P^n(B_2)}, \frac{1}{P^n(B_1)P^n(A_2(x_{n+1}))}\right)$$

$$= \frac{1}{P^n(B_1)P^n(B_2)} \min\left(2, \underbrace{\frac{1}{P^n(A_1(x_{n+1})/P^n(B_1)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)}, \underbrace{\frac{1}{P^n(A_2(x_{n+1})/P^n(B_2)$$

So,

$$\int I(x_{n+1})dP(x_{n+1}) \le \frac{1}{P^n(B_1)P^n(B_2)} \int \min\left(2, \frac{1}{g_1}, \frac{1}{g_2}\right) dP$$

$$\le \frac{1}{P^n(B_1)P^n(B_2)} \cdot \frac{1}{\int g_1 dP \cdot \int g_2 dP}$$

$$= \frac{1}{P^n(B_1)P^n(B_2)} \cdot \frac{1}{P^{n+1}(A_1)/P^n(B_1) \cdot P^{n+1}(A_2)/P^n(B_2)}$$

$$= \frac{1}{P^{n+1}(A_1)P^{n+1}(A_2)}$$

because  $\int P^n(A_1(x_{n+1}))dP(x_{n+1}) = P^{n+1}(A_1)$ .

---

**Lemma 30.1.** *Let* 

$$V(x) = \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(x_i) - f(x'_i))^2$$

and  $a \leq f \leq b$  for all  $f \in \mathcal{F}$ . Then

$$\mathbb{P}\left(V \le 4\mathbb{E}V + (b-a)^2t\right) \ge 1 - 4 \cdot 2^{-t}$$

*Proof.* Consider M-median of V, i.e.  $\mathbb{P}(V \ge M) \ge 1/2$ ,  $\mathbb{P}(V \le M) \ge 1/2$ . Let  $A = \{y \in \mathcal{X}^n, V(y) \le M\} \subseteq \mathcal{X}^n$ . Hence, A consists of points with typical behavior. We will use control by 2 points to show that any other point is close to these two points. By control by 2 points,

$$\mathbb{P}\left(d(A, A, x) \ge t\right) \le \frac{1}{\mathbb{P}(A)\mathbb{P}(A)} \cdot 2^{-t} \le 4 \cdot 2^{-t}$$

Take any  $x \in \mathcal{X}^n$ . With probability at least  $1 - 4 \cdot 2^{-t}$ ,  $d(A, A, x) \leq t$ . Hence, we can find  $y^1 \in A, y^2 \in A$  such that card  $\{i \leq n, x_i \neq y_i^1, x_i \neq y_i^2\} \leq t$ .

Let

$$I_1 = \{i \le n : x_i = y_i^1\}, I_2 = \{i \le n : x_i \ne y_i^1, x_i = y_i^2\},$$

and

$$I_3 = \{i \le n : x_i \ne y_i^1, x_i \ne y_i^2\}$$

Then we can decompose V as follows

$$\begin{split} V(x) &= \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(x_i) - f(x_i'))^2 \\ &= \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \left[ \sum_{i \in I_1} (f(x_i) - f(x_i'))^2 + \sum_{i \in I_2} (f(x_i) - f(x_i'))^2 + \sum_{i \in I_3} (f(x_i) - f(x_i'))^2 \right] \\ &\leq \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i \in I_1} (f(x_i) - f(x_i'))^2 + \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i \in I_2} (f(x_i) - f(x_i'))^2 + \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i \in I_3} (f(x_i) - f(x_i'))^2 \\ &\leq \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(y_i^1) - f(x_i'))^2 + \mathbb{E}_{x'} \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(y_i^2) - f(x_i'))^2 + (b - a)^2 t \\ &= V(y^1) + V(y^2) + (b - a)^2 t \\ &\leq M + M + (b - a)^2 t \end{split}$$

because  $y^1, y^2 \in A$ . Hence,

$$\mathbb{P}\left(V(x) \le 2M + (b-a)^2 t\right) \ge 1 - 4 \cdot 2^{-t}.$$

Finally,  $M \leq 2\mathbb{E}V$  because

$$\mathbb{P}(V \ge 2\mathbb{E}V) \le \frac{\mathbb{E}V}{2\mathbb{E}V} = \frac{1}{2}$$
 while  $\mathbb{P}(V \ge M) \ge \frac{1}{2}$ .

Now, let  $Z(x) = \sup_{f \in \mathcal{F}} |\sum_{i=1}^n f(x_i)|$ . Then

$$Z(x) \underbrace{\leq}_{\text{with prob. } \geq 1-(4e)e^{-t/4}} \mathbb{E}Z + 2\sqrt{V(x)t} \underbrace{\leq}_{\text{with prob. } \geq 1-4\cdot 2^{-t}} \mathbb{E}Z + 2\sqrt{(4\mathbb{E}V + (b-a)^2t)t}.$$

Using inequality  $\sqrt{c+d} \le \sqrt{c} + \sqrt{d}$ ,

$$Z(x) \le \mathbb{E}Z + 4\sqrt{\mathbb{E}Vt} + 2(b-a)t$$

with high probability.

We proved Talagrand's concentration inequality for empirical processes:

**Theorem 30.1.** Assume  $a \leq f \leq b$  for all  $f \in \mathcal{F}$ . Let  $Z = \sup_{f \in \mathcal{F}} |\sum_{i=1}^n f(x_i)|$  and  $V = \sup_{f \in \mathcal{F}} \sum_{i=1}^n (f(x_i) - f(x_i'))^2$ . Then

$$\mathbb{P}\left(Z \le \mathbb{E}Z + 4\sqrt{\mathbb{E}Vt} + 2(b-a)t\right) \ge 1 - (4e)e^{-t/4} - 4 \cdot 2^{-t}.$$

This is an analog of Bernstein's inequality:

$$4\sqrt{\mathbb{E}Vt} \longrightarrow \text{Gaussian behavior}$$

$$2(b-a)t \longrightarrow$$
 Poisson behavior

Now, consider the following lower bound on V.

$$V = \mathbb{E} \sup_{f \in \mathcal{F}} \sum_{i=1}^{n} (f(x_i) - f(x_i'))^2$$

$$> \sup_{f \in \mathcal{F}} \mathbb{E} \sum_{i=1}^{n} (f(x_i) - f(x_i'))^2$$

$$= \sup_{f \in \mathcal{F}} n \mathbb{E} (f(x_1) - f(x_1'))^2$$

$$= \sup_{f \in \mathcal{F}} 2n \operatorname{Var}(f) = 2n \sup_{f \in \mathcal{F}} \operatorname{Var}(f) = 2n\sigma^2$$

As for the upper bound,

$$\mathbb{E}\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}(f(x_{i})-f(x'_{i}))^{2} = \mathbb{E}\sup_{f\in\mathcal{F}}\left(\sum_{i=1}^{n}(f(x_{i})-f(x'_{i}))^{2}-2n\mathrm{Var}(f)+2n\mathrm{Var}(f)\right)$$

$$\leq \mathbb{E}\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}\left[(f(x_{i})-f(x'_{i}))^{2}-\mathbb{E}(f(x_{i})-f(x'_{i}))^{2}\right]+2n\sup_{f\in\mathcal{F}}\mathrm{Var}(f)$$
(by symmetrization)
$$\leq 2\mathbb{E}\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}\varepsilon_{i}(f(x_{i})-f(x'_{i}))^{2}+2n\sigma^{2}$$

$$\leq 2\mathbb{E}\left(\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}\varepsilon_{i}(f(x_{i})-f(x'_{i}))^{2}\right)_{+}+2n\sigma^{2}$$

Note that the square function  $[-(b-a),(b-a)] \mapsto \mathbb{R}$  is a contraction. Its largest derivative on [-(b-a),(b-a)] is at most 2(b-a). Note that  $|f(x_i)-f(x_i')| \leq b-a$ . Hence,

$$2\mathbb{E}\left(\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}\varepsilon_{i}(f(x_{i})-f(x_{i}'))^{2}\right)_{+} + 2n\sigma^{2} \leq 2\cdot2(b-a)\mathbb{E}\left(\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}\varepsilon_{i}(f(x_{i})-f(x_{i}'))\right)_{+} + 2n\sigma^{2}$$

$$\leq 4(b-a)\mathbb{E}\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}\varepsilon_{i}|f(x_{i})-f(x_{i}')| + 2n\sigma^{2}$$

$$\leq 4(b-a)\cdot2\mathbb{E}\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}\varepsilon_{i}|f(x_{i})| + 2n\sigma^{2}$$

$$= 8(b-a)\mathbb{E}Z + 2n\sigma^{2}$$

We have proved the following

## Lemma 30.2.

$$\mathbb{E}V \le 8(b-a)\mathbb{E}Z + 2n\sigma^2,$$

where  $\sigma^2 = \sup_{f \in \mathcal{F}} \operatorname{Var}(f)$ .

Corollary 30.1. Assume  $a \leq f \leq b$  for all  $f \in \mathcal{F}$ . Let  $Z = \sup_{f \in \mathcal{F}} |\sum_{i=1}^n f(x_i)|$  and  $\sigma^2 = \sup_{f \in \mathcal{F}} \operatorname{Var}(f)$ . Then

$$\mathbb{P}\left(Z \le \mathbb{E}Z + 4\sqrt{(8(b-a)\mathbb{E}Z + 2n\sigma^2)t} + 2(b-a)t\right) \ge 1 - (4e)e^{-t/4} - 4 \cdot 2^{-t}.$$

Using other approaches, one can get better constants:

$$\mathbb{P}\left(Z \le \mathbb{E}Z + \sqrt{(4(b-a)\mathbb{E}Z + 2n\sigma^2)t} + (b-a)\frac{t}{3}\right) \ge 1 - e^{-t}.$$

---

If we substitute  $f - \mathbb{E}f$  instead of f, the result of Lecture 30 becomes:

$$\sup_{f \in \mathcal{F}} \left| \sum_{i=1}^{n} (f(x_i) - \mathbb{E}f) \right| \leq \mathbb{E} \sup_{f \in \mathcal{F}} \left| \sum_{i=1}^{n} (f(x_i) - \mathbb{E}f) \right| + \sqrt{\left( 4(b-a)\mathbb{E} \sup_{f \in \mathcal{F}} \left| \sum_{i=1}^{n} (f(x_i) - \mathbb{E}f) \right| + 2n\sigma^2 \right) t + (b-a)\frac{t}{3}}$$

with probability at least  $\geq 1 - e^{-t}$ . Here,  $a \leq f \leq b$  for all  $f \in \mathcal{F}$  and  $\sigma^2 = \sup_{f \in \mathcal{F}} \operatorname{Var}(f)$ . Now divide by n to get

$$\sup_{f \in \mathcal{F}} \left| \frac{1}{n} \sum_{i=1}^{n} f(x_i) - \mathbb{E}f \right| \leq \mathbb{E} \sup_{f \in \mathcal{F}} |\ldots| + \sqrt{\left(4(b-a)\mathbb{E} \sup_{f \in \mathcal{F}} |\ldots| + 2\sigma^2\right) \frac{t}{n}} + (b-a) \frac{t}{3n}$$

Compare this result to the Martingale-difference method (McDiarmid):

$$\sup_{f \in \mathcal{F}} \left| \frac{1}{n} \sum_{i=1}^{n} f(x_i) - \mathbb{E}f \right| \le \mathbb{E} \sup_{f \in \mathcal{F}} |\ldots| + \sqrt{\frac{2(b-a)^2 t}{n}}$$

The term  $2(b-a)^2$  is worse than  $4(b-a)\mathbb{E}\sup_{f\in\mathcal{F}}|\ldots|+2\sigma^2$ .

An algorithm outputs  $f_0 \in \mathcal{F}$ ,  $f_0$  depends on data  $x_1, \ldots, x_n$ . What is  $\mathbb{E}f_0$ ? Assume  $0 \le f \le 1$  (loss function). Then

$$\left| \mathbb{E} f_0 - \frac{1}{n} \sum_{i=1}^n f_0(x_i) \right| \le \sup_{f \in \mathcal{F}} \left| \mathbb{E} f - \frac{1}{n} \sum_{i=1}^n f(x_i) \right| \le \text{ use Talagrand's inequality }.$$

What if we knew that  $\mathbb{E}f_0 \leq \varepsilon$  and the family  $\mathcal{F}_{\varepsilon} = \{f \in \mathcal{F}, \mathbb{E}f \leq \varepsilon\}$  is much smaller than  $\mathcal{F}$ . Then looking at  $\sup_{f \in \mathcal{F}} \left| \mathbb{E}f - \frac{1}{n} \sum_{i=1}^{n} f(x_i) \right|$  is too conservative.

Pin down location of  $f_0$ . Pretend we know  $\mathbb{E}f_0 \leq \varepsilon$ ,  $f_0 \in \mathcal{F}_{\varepsilon}$ . Then with probability at least  $1 - e^{-t}$ ,

$$\left| \mathbb{E} f_0 - \frac{1}{n} \sum_{i=1}^n f_0(x_i) \right| \le \sup_{f \in \mathcal{F}_{\varepsilon}} \left| \mathbb{E} f - \frac{1}{n} \sum_{i=1}^n f(x_i) \right|$$

$$\le \mathbb{E} \sup_{f \in \mathcal{F}_{\varepsilon}} \left| \mathbb{E} f - \frac{1}{n} \sum_{i=1}^n f(x_i) \right| + \sqrt{\left( 4\mathbb{E} \sup_{f \in \mathcal{F}_{\varepsilon}} |\ldots| + 2\sigma_{\varepsilon}^2 \right) \frac{t}{n}} + \frac{t}{3n}$$

where  $\sigma_{\varepsilon}^2 = \sup_{f \in \mathcal{F}_{\varepsilon}} \text{Var}(f)$ . Note that for  $f \in \mathcal{F}_{\varepsilon}$ 

$$Var(f) = \mathbb{E}f^2 - (\mathbb{E}f)^2 \le \mathbb{E}f^2 \le \mathbb{E}f \le \varepsilon$$

since  $0 \le f \le 1$ .

Denote  $\varphi(\varepsilon) = \mathbb{E} \sup_{f \in \mathcal{F}_{\varepsilon}} \left| \mathbb{E} f - \frac{1}{n} \sum_{i=1}^{n} f(x_i) \right|$ . Then

$$\left| \mathbb{E} f_0 - \frac{1}{n} \sum_{i=1}^n f_0(x_i) \right| \le \varphi(\varepsilon) + \sqrt{(4\varphi(\varepsilon) + 2\varepsilon) \frac{t}{n}} + \frac{t}{3n}$$

with probability at least  $1 - e^{-t}$ .

Take  $\varepsilon=2^{-k},\ k=0,1,2,\ldots$  Change  $t\to t+2\log(k+2)$ . Then, for a fixed k, with probability at least  $1-e^{-t}\frac{1}{(k+2)^2}$ ,

$$\left| \mathbb{E} f_0 - \frac{1}{n} \sum_{i=1}^n f_0(x_i) \right| \le \varphi(\varepsilon) + \sqrt{(4\varphi(\varepsilon) + 2\varepsilon) \frac{t + 2\log(k+2)}{n}} + \frac{t + 2\log(k+2)}{3n}$$

For all  $k \geq 0$ , the statement holds with probability at least

$$1 - \underbrace{\sum_{k=1}^{\infty} \frac{1}{(k+2)^2}}_{\frac{\pi^2}{6} - 1} e^{-t} \ge 1 - e^{-t}$$

For  $f_0$ , find k such that  $2^{-k-1} \leq \mathbb{E} f_0 < 2^{-k}$  (hence,  $2^{-k} \leq 2\mathbb{E} f_0$ ). Use the statement for  $\varepsilon_k = 2^{-k}$ ,  $k \leq \log_2 \frac{1}{\mathbb{E} f_0}$ .

$$\left| \mathbb{E} f_0 - \frac{1}{n} \sum_{i=1}^n f_0(x_i) \right| \le \varphi(\varepsilon_k) + \sqrt{\left(4\varphi(\varepsilon_k) + 2\varepsilon_k\right) \frac{t + 2\log(k+2)}{n}} + \frac{t + 2\log(k+2)}{3n}$$

$$\le \varphi(2\mathbb{E} f_0) + \sqrt{\left(4\varphi(2\mathbb{E} f_0) + 4\mathbb{E} f_0\right) \frac{t + 2\log(\log_2 \frac{1}{\mathbb{E} f_0} + 2)}{n}} + \frac{t + 2\log(\log_2 \frac{1}{\mathbb{E} f_0} + 2)}{2n} = \Phi(\mathbb{E} f_0)$$

Hence,  $\mathbb{E}f_0 \leq \frac{1}{n} \sum_{i=1}^n f_0(x_i) + \Phi(\mathbb{E}f_0)$ . Denote  $x = \mathbb{E}f_0$ . Then  $x \leq \bar{f} + \Phi(x)$ .

**Theorem 31.1.** Let  $0 \leq f \leq 1$  for all  $f \in \mathcal{F}$ . Define  $\mathcal{F}_{\varepsilon} = \{f \in \mathcal{F}, \mathbb{E}f \leq \varepsilon\}$  and  $\varphi(\varepsilon) = \mathbb{E} \sup_{f \in \mathcal{F}_{\varepsilon}} \left| \mathbb{E}f - \frac{1}{n} \sum_{i=1}^{n} f(x_i) \right|$ . Then, with probability at least  $1 - e^{-t}$ , for any  $f_0 \in \mathcal{F}$ ,  $\mathbb{E}f_0 \leq x^*$ , where  $x^*$  is the largest solution of

$$x^* = \frac{1}{n} \sum_{i=1}^{n} f_0(x_i) + \Phi(x^*).$$

Main work is to find  $\varphi(\varepsilon)$ . Consider the following example.

## Example 1. If

$$\sup_{x_1,\dots,x_n} \log \mathcal{D}(\mathcal{F}, u, d_x) \le \mathcal{D}(\mathcal{F}, u),$$

then

$$\mathbb{E}\sup_{f\in\mathcal{F}_{\varepsilon}}\left|\mathbb{E}f-\frac{1}{n}\sum_{i=1}^{n}f(x_{i})\right|\leq\frac{k}{\sqrt{n}}\int_{0}^{\sqrt{\varepsilon}}\log^{1/2}\mathcal{D}(\mathcal{F},\varepsilon)d\varepsilon.$$

---

Let  $x \in \mathcal{X}^n$ ,  $x = (x_1, \dots, x_n)$ . Suppose  $A \subseteq \mathcal{X}^n$ . Define

$$V(A, x) = \{ (I(x_1 \neq y_1), \dots, I(x_n \neq y_n)) : y = (y_1, \dots, y_n) \in A \},\$$

$$U(A, x) = \text{conv } V(A, x)$$

and

$$d(A, x) = \min\{|s|^2 = \sum_{i=1}^n s_i^2, \ s \in U(A, x)\}$$

In the previous lectures, we proved

## Theorem 32.1.

$$\mathbb{P}\left(d(A,x) \ge t\right) \le \frac{1}{\mathbb{P}(A)}e^{-t/4}.$$

Today, we prove

**Theorem 32.2.** The following are equivalent:

(1) 
$$d(A, x) < t$$

(2) 
$$\forall \alpha = (\alpha_1, \dots, \alpha_n), \exists y \in A, \text{ s.t. } \sum_{i=1}^n \alpha_i I(x_i \neq y_i) \leq \sqrt{\sum_{i=1}^n \alpha_i^2 \cdot t}$$

Proof.  $(1)\Rightarrow(2)$ :

Choose any  $\alpha = (\alpha_1, \dots, \alpha_n)$ .

(1) 
$$\min_{y \in A} \sum_{i=1}^{n} \alpha_i I(x_i \neq y_i) = \min_{s \in U(A,x)} \sum_{i=1}^{n} \alpha_i s_i \leq \sum_{i=1}^{n} \alpha_i s_i^0$$

(2) 
$$\leq \sqrt{\sum_{i=1}^{n} \alpha_i^2} \sqrt{\sum_{i=1}^{n} (s_i^0)^2} \leq \sqrt{\sum_{i=1}^{n} \alpha_i^2 \cdot t}$$

where in the last inequality we used assumption (1). In the above, min is achieved at  $s^0$ .

 $(2) \Rightarrow (1)$ :

Let  $\alpha = (s_1^0, \dots, s_n^0)$ . There exists  $y \in A$  such that

$$\sum_{i=1}^{n} \alpha_i I(x_i \neq y_i) \leq \sqrt{\sum_{i=1}^{n} \alpha_i^2 \cdot t}$$

Note that  $\sum \alpha_i s_i^0$  is constant on L because  $s^0$  is perpendicular to the face.

$$\sum \alpha_i s_i^0 \le \sum \alpha_i I(x_i \ne y_i) \le \sqrt{\sum \alpha_i^2 t}$$

Hence, 
$$\sum (s_i^0)^2 \leq \sqrt{\sum (s_i^0)^2 t}$$
 and  $\sqrt{\sum (s_i^0)^2} \leq \sqrt{t}$ . Therefore,  $d(A,x) \leq \sum (s_i^0)^2 \leq t$ .

We now turn to an application of the above results: Bin Packing.

**Example 1.** Assume we have  $x_1, \ldots, x_n$ ,  $0 \le x_i \le 1$ , and let  $B(x_1, \ldots, x_n)$  be the smallest number of bins of size 1 needed to pack all  $(x_1, \ldots, x_n)$ . Let  $S_1, \ldots, S_B \subseteq \{1, \ldots, n\}$  such that all  $x_i$  with  $i \in S_k$  are packed into one bin,  $\bigcup S_k = \{1, \ldots, n\}$ ,  $\sum_{i \in S_k} x_i \le 1$ .

**Lemma 32.1.**  $B(x_1, ..., x_n) \le 2 \sum x_i + 1$ .

*Proof.* For all but one  $k, \frac{1}{2} \leq \sum_{i \in S_k} x_i$ . Otherwise we can combine two bins into one. Hence,  $B-1 \leq 2 \sum_k \sum_{i \in S_k} x_i = 2 \sum_i x_i$ 

Theorem 32.3.

$$\mathbb{P}\left(B(x_1,\ldots,x_n) \le M + 2\sqrt{\sum x_i^2 \cdot t} + 1\right) \ge 1 - 2e^{-t/4}.$$

*Proof.* Let  $A = \{y : B(y_1, \dots, y_n) \leq M\}$ , where  $\mathbb{P}(B \geq M) \geq 1/2$ ,  $\mathbb{P}(B \leq M) \geq 1/2$ . We proved that

$$\mathbb{P}\left(d(A,x) \ge t\right) \le \frac{1}{\mathbb{P}\left(A\right)} e^{-t/4}.$$

Take x such that  $d(A, x) \leq t$ . Take  $\alpha = (x_1, \dots, x_n)$ . Since  $d(A, x) \leq t$ , there exists  $y \in A$  such that  $\sum x_i I(x_i \neq y_i) \leq \sqrt{\sum x_i^2 \cdot t}$ .

To pack the set  $\{i: x_i = y_i\}$  we need  $\leq B(y_1, \ldots, y_n) \leq M$  bins.

To pack  $\{i: x_i \neq y_i\}$ :

$$B(x_1I(x_1 \neq y_1), \dots, x_nI(x_n \neq y_n)) \le 2\sum x_iI(x_i \neq y_i) + 1$$
  
  $\le 2\sqrt{\sum x_i^2 \cdot t} + 1$ 

by Lemma.

Hence,

$$B(x_1, \dots, x_n) \le M + 2\sqrt{\sum x_i^2 \cdot t} + 1$$

with probability at least  $1 - 2e^{-t/4}$ .

By Bernstein's inequality we get

$$\mathbb{P}\left(\sum x_i^2 \le n\mathbb{E}x_1^2 + \sqrt{n\mathbb{E}x_1^2 \cdot t} + \frac{2}{3}t\right) \ge 1 - e^{-t}.$$

Hence,

$$B(x_1,\ldots,x_n) \lesssim M + 2\sqrt{n\mathbb{E}x_1^2 \cdot t}$$

---

Let  $\mathcal{X} \subset \mathbb{R}^d$  be a compact subset. Assume  $x_1, \ldots, x_n$  are i.i.d. and  $y_1, \ldots, y_n = \pm 1$  for classification and [-1, 1] for regression. Assume we have a kernel  $K(x, y) = \sum_{i=1}^{\infty} \lambda_i \phi_i(x) \phi_i(y)$ ,  $\lambda_i > 0$ .

Consider a map

$$x \in \mathcal{X} \mapsto \phi(x) = (\sqrt{\lambda_1}\phi_1(x), \dots, \sqrt{\lambda_k}\phi_k(x), \dots) = (\sqrt{\lambda_k}\phi_k(x))_{k \ge 1} \in \mathcal{H}$$

where  $\mathcal{H}$  is a Hilbert space.

Consider the scalar product in  $\mathcal{H}$ :  $(u, v)_{\mathcal{H}} = \sum_{i=1}^{\infty} u_i v_i$  and  $||u||_{\mathcal{H}} = \sqrt{(u, v)_{\mathcal{H}}}$ . For  $x, y \in \mathcal{X}$ ,

$$(\phi(x), \phi(y))_{\mathcal{H}} = \sum_{i=1}^{\infty} \lambda_i \phi_i(x) \phi_i(y) = K(x, y).$$

Function  $\phi$  is called feature map

Family of classifiers:

$$\mathcal{F}_{\mathcal{H}} = \{ (w, z)_{\mathcal{H}} : ||w||_{\mathcal{H}} \le 1 \}.$$

$$\mathcal{F} = \{(w, \phi(x))_{\mathcal{H}} : ||w||_{\mathcal{H}} \le 1\} \ni f : \mathcal{X} \mapsto \mathbb{R}.$$

Algorithms:

(1) **SVMs** 

$$f(x) = \sum_{i=1}^{n} \alpha_i K(x_i, x) = (\underbrace{\sum_{i=1}^{n} \alpha_i \phi(x_i), \phi(x)}_{w})_{\mathcal{H}}$$

Here, instead of taking any w, we only take w as a linear combination of images of data points. We have a choice of Loss function  $\mathcal{L}$ :

- $\mathcal{L}(y, f(x)) = I(yf(x) \le 0)$  classification
- $\mathcal{L}(y, f(x)) = (y f(x))^2$  regression
- (2) Square-loss regularization

Assume an algorithm outputs a classifier from  $\mathcal{F}$  (or  $\mathcal{F}_{\mathcal{H}}$ ),  $f(x) = (w, \phi(x))_{\mathcal{H}}$ . Then, as in Lecture 18,

$$\mathbb{P}\left(yf(x) \leq 0\right) \leq \mathbb{E}\varphi_{\delta}\left(yf(x)\right) = \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}\left(y_{i}f(x_{i})\right) + \left(\mathbb{E}\varphi_{\delta}\left(yf(x)\right) - \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}\left(y_{i}f(x_{i})\right)\right)$$
$$\leq \frac{1}{n} \sum_{i=1}^{n} I(y_{i}f(x_{i}) \leq \delta) + \sup_{f \in \mathcal{F}} \left(\mathbb{E}\varphi_{\delta}\left(yf(x)\right) - \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta}\left(y_{i}f(x_{i})\right)\right)$$

By McDiarmid's inequality, with probability at least  $1 - e^{-t}$ 

$$\sup_{f \in \mathcal{F}} \left( \mathbb{E} \varphi_{\delta} \left( y f(x) \right) - \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta} \left( y_{i} f(x_{i}) \right) \right) \leq \mathbb{E} \sup_{f \in \mathcal{F}} \left( \mathbb{E} \varphi_{\delta} \left( y f(x) \right) - \frac{1}{n} \sum_{i=1}^{n} \varphi_{\delta} \left( y_{i} f(x_{i}) \right) \right) + \sqrt{\frac{2t}{n}}$$

Using the symmetrization technique,

$$\mathbb{E}\sup_{f\in\mathcal{F}}\left(\mathbb{E}(\varphi_{\delta}\left(yf(x)\right)-1\right)-\frac{1}{n}\sum_{i=1}^{n}(\varphi_{\delta}\left(y_{i}f(x_{i})\right)-1\right)\right)\leq2\mathbb{E}\sup_{f\in\mathcal{F}}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}\left(\varphi_{\delta}\left(y_{i}f(x_{i})\right)-1\right)\right|.$$

Since  $\delta \cdot (\varphi_{\delta} - 1)$  is a contraction,

$$\begin{split} &2\mathbb{E}\sup_{f\in\mathcal{F}}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}\left(\varphi_{\delta}\left(y_{i}f(x_{i})\right)-1\right)\right|\leq\frac{2}{\delta}2\mathbb{E}\sup_{f\in\mathcal{F}}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}y_{i}f(x_{i})\right|\\ &=\frac{4}{\delta}\mathbb{E}\sup_{f\in\mathcal{F}}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}f(x_{i})\right|=\frac{4}{\delta}\mathbb{E}\sup_{\|w\|\leq1}\left|\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}(w,\phi(x_{i}))_{\mathcal{H}}\right|\\ &=\frac{4}{\delta n}\mathbb{E}\sup_{\|w\|\leq1}\left|(w,\sum_{i=1}^{n}\varepsilon_{i}\phi(x_{i}))_{\mathcal{H}}\right|=\frac{4}{\delta n}\mathbb{E}\sup_{\|w\|\leq1}\left\|\sum_{i=1}^{n}\varepsilon_{i}\phi(x_{i})\right\|_{\mathcal{H}}\\ &=\frac{4}{\delta n}\mathbb{E}\sqrt{\left(\sum_{i=1}^{n}\varepsilon_{i}\phi(x_{i}),\sum_{i=1}^{n}\varepsilon_{i}\phi(x_{i})\right)_{\mathcal{H}}}=\frac{4}{\delta n}\mathbb{E}\sqrt{\sum_{i,j}\varepsilon_{i}\varepsilon_{j}(\phi(x_{i}),\phi(x_{i}))_{\mathcal{H}}}\\ &=\frac{4}{\delta n}\mathbb{E}\sqrt{\sum_{i,j}\varepsilon_{i}\varepsilon_{j}K(x_{i},x_{j})}\leq\frac{4}{\delta n}\sqrt{\mathbb{E}\sum_{i,j}\varepsilon_{i}\varepsilon_{j}K(x_{i},x_{j})}\\ &=\frac{4}{\delta n}\sqrt{\sum_{i=1}^{n}\mathbb{E}K(x_{i},x_{i})}=\frac{4}{\delta}\sqrt{\frac{\mathbb{E}K(x_{1},x_{1})}{n}} \end{split}$$

Putting everything together, with probability at least  $1 - e^{-t}$ ,

$$\mathbb{P}\left(yf(x) \le 0\right) \le \frac{1}{n} \sum_{i=1}^{n} I(y_i f(x_i) \le \delta) + \frac{4}{\delta} \sqrt{\frac{\mathbb{E}K(x_1, x_1)}{n}} + \sqrt{\frac{2t}{n}}.$$

Before the contraction step, we could have used Martingale method again to have  $\mathbb{E}_{\varepsilon}$  only. Then  $\mathbb{E}K(x_1, x_1)$  in the above bound will become  $\frac{1}{n} \sum_{i=1}^{n} K(x_i, x_i)$ .

---

As in the previous lecture, let  $\mathcal{F} = \{(w, \phi(x))_{\mathcal{H}}, ||w|| \leq 1\}$ , where  $\phi(x) = (\sqrt{\lambda_i}\phi_i(x))_{i\geq 1}$ ,  $\mathcal{X} \subset \mathbb{R}^d$ .

Define  $d(f, g) = ||f - g||_{\infty} = \sup_{x \in \mathcal{X}} |f(x) - g(x)|.$ 

The following theorem appears in Cucker & Smale:

Theorem 34.1.  $\forall h \geq d$ ,

$$\log \mathcal{N}(\mathcal{F}, \varepsilon, d) \le \left(\frac{C_h}{\varepsilon}\right)^{\frac{2d}{h}}$$

where  $C_h$  is a constant.

Note that for any  $x_1, \ldots, x_n$ ,

$$d_x(f,g) = \left(\frac{1}{n}\sum_{i=1}^n (f(x_i) - g(x_i))^2\right)^{1/2} \le d(f,g) = \sup_x |f(x) - g(x)| \le \varepsilon.$$

Hence,

$$\mathcal{N}(\mathcal{F}, \varepsilon, d_x) \leq \mathcal{N}(\mathcal{F}, \varepsilon, d).$$

Assume the loss function  $\mathcal{L}(y, f(x)) = (y - f(x))^2$ . The loss classis defined as

$$\mathcal{L}(y,F) = \{(y - f(x))^2, f \in \mathcal{F}\}.$$

Suppose  $|y - f(x)| \le M$ . Then

$$|(y - f(x))^2 - (y - g(x))^2| \le 2M|f(x) - g(x)| \le \varepsilon.$$

So,

$$\mathcal{N}(\mathcal{L}(y,\mathcal{F}), \varepsilon, d_x) \leq \mathcal{N}\left(\mathcal{F}, \frac{\varepsilon}{2M}, d_x\right)$$

and

$$\log \mathcal{N}(\mathcal{L}(y,\mathcal{F}),\varepsilon,d_x) \le \left(\frac{2MC_h}{\varepsilon}\right)^{\frac{2d}{h}} = \left(\frac{2MC_h}{\varepsilon}\right)^{\alpha}$$

 $\alpha = \frac{2d}{h} < 2$  (see Homework 2, problem 4).

Now, we would like to use specific form of solution for SVM:  $f(x) = \sum_{i=1}^{n} \alpha_i K(x_i, x)$ , i.e. f belongs to a random subclass. We now prove a VC inequality for random collection of sets. Let's consider  $C(x_1, \ldots, x_n) = \{C : C \subseteq \mathcal{X}\}$  - random collection of sets. Assume that  $C(x_1, \ldots, x_n)$  satisfies:

(1) 
$$C(x_1, \ldots, x_n) \subseteq C(x_1, \ldots, x_n, x_{n+1})$$

(2)  $C(\pi(x_1,\ldots,x_n)) = C(x_1,\ldots,x_n)$  for any permutation  $\pi$ .

Let

$$\triangle_{\mathcal{C}}(x_1,\ldots,x_n) = \operatorname{card} \{C \cap \{x_1,\ldots,x_n\}; C \in \mathcal{C}\}\$$

and

$$G(n) = \mathbb{E} \triangle_{\mathcal{C}(x_1,\dots,x_n)}(x_1,\dots,x_n).$$

Theorem 34.2.

$$\mathbb{P}\left(\sup_{C\in\mathcal{C}(x_1,\dots,x_n)}\frac{\mathbb{P}\left(C\right)-\frac{1}{n}\sum_{i=1}^nI(x_i\in C)}{\sqrt{\mathbb{P}\left(C\right)}}\geq t\right)\leq 4G(2n)e^{-\frac{nt^2}{4}}$$

Proof.

Consider event

$$A_x = \left\{ x = (x_1, \dots, x_n) : \sup_{C \in \mathcal{C}(x_1, \dots, x_n)} \frac{\mathbb{P}(C) - \frac{1}{n} \sum_{i=1}^n I(x_i \in C)}{\sqrt{\mathbb{P}(C)}} \ge t \right\}$$

So, there exists  $C_x \in \mathcal{C}(x_1, \ldots, x_n)$  such that

$$\frac{\mathbb{P}(C_x) - \frac{1}{n} \sum_{i=1}^{n} I(x_i \in C_x)}{\sqrt{\mathbb{P}(C_x)}} \ge t.$$

For  $x'_1, \ldots, x'_n$ , an independent copy of x,

$$\mathbb{P}_{x'}\left(\mathbb{P}\left(C_x\right) \le \frac{1}{n} \sum_{i=1}^n I(x_i' \in C_x)\right) \ge \frac{1}{4}$$

if  $\mathbb{P}(C_x) \geq \frac{1}{n}$  (which we can assume without loss of generality).

Together,

$$\mathbb{P}\left(C_{x}\right) \leq \frac{1}{n} \sum_{i=1}^{n} I(x_{i}' \in C_{x})$$

and

$$\frac{\mathbb{P}(C_x) - \frac{1}{n} \sum_{i=1}^{n} I(x_i \in C_x)}{\sqrt{\mathbb{P}(C_x)}} \ge t$$

imply

$$\frac{\frac{1}{n} \sum_{i=1}^{n} I(x_i' \in C_x) - \frac{1}{n} \sum_{i=1}^{n} I(x_i \in C_x)}{\sqrt{\frac{1}{2n} \sum_{i=1}^{n} (I(x_i' \in C_x) + I(x_i \in C_x))}} \ge t.$$

Indeed,

$$0 < t \le \frac{\mathbb{P}(C_x) - \frac{1}{n} \sum_{i=1}^n I(x_i \in C_x)}{\sqrt{\mathbb{P}(C_x)}}$$

$$\le \frac{\mathbb{P}(C_x) - \frac{1}{n} \sum_{i=1}^n I(x_i \in C_x)}{\sqrt{\frac{1}{2} \left(\mathbb{P}(C_x) + \frac{1}{n} \sum_{i=1}^n I(x_i \in C_x)\right)}}$$

$$\le \frac{\frac{1}{n} \sum_{i=1}^n I(x_i' \in C_x) - \frac{1}{n} \sum_{i=1}^n I(x_i \in C_x)}{\sqrt{\frac{1}{2} \left(\frac{1}{n} \sum_{i=1}^n I(x_i' \in C_x) + \frac{1}{n} \sum_{i=1}^n I(x_i \in C_x)\right)}}$$

Hence, multiplying by an indicator,

$$\frac{1}{4} \cdot I(x \in A_x) \leq \mathbb{P}_{x'} \left( \mathbb{P}(C_x) \leq \frac{1}{n} \sum_{i=1}^n I(x_i' \in C_x) \right) \cdot I(x \in A_x) 
\leq \mathbb{P}_{x'} \left( \frac{\frac{1}{n} \sum_{i=1}^n I(x_i' \in C_x) - \frac{1}{n} \sum_{i=1}^n I(x_i \in C_x)}{\sqrt{\frac{1}{2} \left(\frac{1}{n} \sum_{i=1}^n I(x_i' \in C_x) + \frac{1}{n} \sum_{i=1}^n I(x_i \in C_x)\right)}} \geq t \right) 
\leq \mathbb{P}_{x'} \left( \sup_{C \in \mathcal{C}(x_1, \dots, x_n)} \frac{\frac{1}{n} \sum_{i=1}^n I(x_i' \in C_x) - \frac{1}{n} \sum_{i=1}^n I(x_i \in C_x)}{\sqrt{\frac{1}{2} \left(\frac{1}{n} \sum_{i=1}^n I(x_i' \in C_x) + \frac{1}{n} \sum_{i=1}^n I(x_i \in C_x)\right)}} \geq t \right)$$

Taking expectation with respect to x on both sides,

$$\mathbb{P}\left(\sup_{C \in \mathcal{C}(x_{1},...,x_{n})} \frac{\mathbb{P}(C) - \frac{1}{n} \sum_{i=1}^{n} I(x_{i} \in C)}{\sqrt{\mathbb{P}(C)}} \ge t\right) \\
\leq 4\mathbb{P}\left(\sup_{C \in \mathcal{C}(x_{1},...,x_{n})} \frac{\frac{1}{n} \sum_{i=1}^{n} I(x'_{i} \in C_{x}) - \frac{1}{n} \sum_{i=1}^{n} I(x_{i} \in C_{x})}{\sqrt{\frac{1}{2} \left(\frac{1}{n} \sum_{i=1}^{n} I(x'_{i} \in C_{x}) + \frac{1}{n} \sum_{i=1}^{n} I(x_{i} \in C_{x})\right)}} \ge t\right) \\
\leq 4\mathbb{P}\left(\sup_{C \in \mathcal{C}(x_{1},...,x_{n},x'_{1},...,x'_{n})} \frac{\frac{1}{n} \sum_{i=1}^{n} I(x'_{i} \in C_{x}) - \frac{1}{n} \sum_{i=1}^{n} I(x_{i} \in C_{x})}{\sqrt{\frac{1}{2} \left(\frac{1}{n} \sum_{i=1}^{n} I(x'_{i} \in C_{x}) + \frac{1}{n} \sum_{i=1}^{n} I(x_{i} \in C_{x})\right)}} \ge t\right) \\
= 4\mathbb{P}\left(\sup_{C \in \mathcal{C}(x_{1},...,x_{n},x'_{1},...,x'_{n})} \frac{\frac{1}{n} \sum_{i=1}^{n} E_{i}(I(x'_{i} \in C_{x}) - I(x_{i} \in C_{x}))}{\sqrt{\frac{1}{2} \left(\frac{1}{n} \sum_{i=1}^{n} I(x'_{i} \in C_{x}) + \frac{1}{n} \sum_{i=1}^{n} I(x_{i} \in C_{x})\right)}} \ge t\right) \\
= 4\mathbb{E}\mathbb{P}_{\varepsilon}\left(\sup_{C \in \mathcal{C}(x_{1},...,x_{n},x'_{1},...,x'_{n})} \frac{\frac{1}{n} \sum_{i=1}^{n} E_{i}(I(x'_{i} \in C_{x}) - I(x_{i} \in C_{x}))}{\sqrt{\frac{1}{2} \left(\frac{1}{n} \sum_{i=1}^{n} E_{i}(I(x'_{i} \in C_{x}) + \frac{1}{n} \sum_{i=1}^{n} I(x_{i} \in C_{x})\right)}} \ge t\right)$$

By Hoeffding,

$$4\mathbb{E}P_{\varepsilon}\left(\sup_{C\in\mathcal{C}(x_{1},\ldots,x_{n},x'_{1},\ldots,x'_{n})}\frac{\frac{1}{n}\sum_{i=1}^{n}\varepsilon_{i}(I(x'_{i}\in C_{x})-I(x_{i}\in C_{x}))}{\sqrt{\frac{1}{2}\left(\frac{1}{n}\sum_{i=1}^{n}I(x'_{i}\in C_{x})+\frac{1}{n}\sum_{i=1}^{n}I(x_{i}\in C_{x})\right)}}\geq t\right)$$

$$\leq 4\mathbb{E}\Delta_{\mathcal{C}(x_{1},\ldots,x_{n},x'_{1},\ldots,x'_{n})}(x_{1},\ldots,x_{n},x'_{1},\ldots,x'_{n})\cdot\exp\left(-\frac{t^{2}}{2\sum\left(\frac{\frac{1}{n}(I(x'_{i}\in C_{x})-I(x_{i}\in C_{x}))}{\sqrt{\frac{1}{2n}\sum_{i=1}^{n}(I(x'_{i}\in C_{x})+I(x_{i}\in C_{x}))}}\right)^{2}}\right)$$

$$\leq 4\mathbb{E}\Delta_{\mathcal{C}(x_{1},\ldots,x_{n},x'_{1},\ldots,x'_{n})}(x_{1},\ldots,x_{n},x'_{1},\ldots,x'_{n})\cdot e^{-\frac{nt^{2}}{4}}$$

$$= 4G(2n)e^{-\frac{nt^{2}}{4}}$$

---

Recall that the solution of SVM is  $f(x) = \sum_{i=1}^{n} \alpha_i K(x_i, x)$ , where  $(x_1, y_1), \dots, (x_n, y_n)$  – data, with  $y_i \in \{-1, 1\}$ . The label is predicted by  $\operatorname{sign}(f(x))$  and  $\mathbb{P}(yf(x) \leq 0)$  is misclassification error.

Let  $\mathcal{H} = \mathcal{H}((x_1, y_1), \dots, (x_n, y_n))$  be random collection of functions, with card  $\mathcal{H} \leq \mathcal{N}(n)$ . Also, assume that for any  $h \in \mathcal{H}$ ,  $-h \in \mathcal{H}$  so that  $\alpha$  can be positive.

Define

$$\mathcal{F} = \left\{ \sum_{i=1}^{T} \lambda_i h_i, \ T \ge 1, \ \lambda_i \ge 0, \ \sum_{i=1}^{T} \lambda_i = 1, \ h_i \in \mathcal{H} \right\}.$$

For SVM,  $\mathcal{H} = \{\pm K(x_i, x) : i = 1, ..., n\}$  and card  $\mathcal{H} \leq 2n$ .

Recall margin-sparsity bound (voting classifiers): algorithm outputs  $f = \sum_{i=1}^{T} \lambda_i h_i$ . Take random approximation  $g(x) = \frac{1}{k} \sum_{j=1}^{k} Y_j(x)$ , where  $Y_1, \dots, Y_k$  i.i.d with  $\mathbb{P}(Y_j = h_i) = \lambda_i$ ,  $\mathbb{E}Y_j(x) = f(x)$ .

Fix  $\delta > 0$ .

$$\mathbb{P}(yf(x) \leq 0) = \mathbb{P}(yf(x) \leq 0, yg(x) \leq \delta) + \mathbb{P}(yf(x) \leq 0, yg(x) > \delta)$$

$$\leq \mathbb{P}(yg(x) \leq \delta) + \mathbb{E}_{x,y}\mathbb{P}_{Y}\left(y\frac{1}{k}\sum_{j=1}^{k}Y_{j}(x) > \delta, \ y\mathbb{E}_{Y}Y_{1}(x) \leq 0\right)$$

$$\leq \mathbb{P}(yg(x) \leq \delta) + \mathbb{E}_{x,y}\mathbb{P}_{Y}\left(\frac{1}{k}\sum_{j=1}^{k}(yY_{j}(x) - \mathbb{E}(yY_{j}(x))) \geq \delta\right)$$

$$\leq (\text{by Hoeffding}) \ \mathbb{P}(yg(x) \leq \delta) + \mathbb{E}_{x,y}e^{-k\delta^{2}/2}$$

$$= \mathbb{P}(yg(x) \leq \delta) + e^{-k\delta^{2}/2}$$

$$= \mathbb{E}_{Y}\mathbb{P}_{x,y}(yg(x) \leq \delta) + e^{-k\delta^{2}/2}$$

Similarly to what we did before, on the data

$$\mathbb{E}_{Y} \left[ \frac{1}{n} \sum_{i=1}^{n} I(y_{i}g(x_{i}) \leq \delta) \right] \leq \frac{1}{n} \sum_{i=1}^{n} I(y_{i}f(x_{i}) \leq 2\delta) + e^{-k\delta^{2}/2}$$

Can we bound

$$\mathbb{P}_{x,y}\left(yg(x) \le \delta\right) - \frac{1}{n} \sum_{i=1}^{n} I(y_i g(x_i) \le \delta)$$

for any q?

Define

$$\mathcal{C} = \{ \{ yg(x) \le \delta \}, \ g \in \mathcal{F}_k, \ \delta \in [-1, 1] \}$$

where

$$\mathcal{F}_k = \left\{ \frac{1}{k} \sum_{j=1}^k h_j(x) : h_j \in \mathcal{H} \right\}$$

Note that  $\mathcal{H}(x_1,\ldots,x_n)\subseteq\mathcal{H}(x_1,\ldots,x_n,x_{n+1})$  and  $\mathcal{H}(\pi(x_1,\ldots,x_n))=\mathcal{H}(x_1,\ldots,x_n)$ .

In the last lecture, we proved

$$\mathbb{P}_{x,y}\left(\sup_{C\in\mathcal{C}}\frac{\mathbb{P}\left(C\right)-\frac{1}{n}\sum_{i=1}^{n}I(x_{i}\in C)}{\sqrt{\mathbb{P}\left(C\right)}}\geq t\right)\leq 4G(2n)e^{-\frac{nt^{2}}{2}}$$

where

$$G(n) = \mathbb{E} \triangle_{\mathcal{C}(x_1,\dots,x_n)}(x_1,\dots,x_n).$$

How many different g's are there? At most card  $\mathcal{F}_k \leq \mathcal{N}(n)^k$ . For a fixed g,

card 
$$\{\{yg(x) \leq \delta\} \cap \{x_1, \dots, x_n\}, \delta \in [-1, 1]\} \leq (n+1).$$

Indeed, we can order  $y_1g(x_1), \ldots, y_ng(x_n) \to y_{i_1}g(x_{i_1}) \leq \ldots \leq y_{i_n}g(x_{i_n})$  and level  $\delta$  can be anywhere along this chain.

Hence.

$$\triangle_{\mathcal{C}(x_1,\dots,x_n)}(x_1,\dots,x_n) \leq \mathcal{N}(n)^k(n+1).$$

$$\mathbb{P}_{x,y}\left(\sup_{C\in\mathcal{C}}\frac{\mathbb{P}\left(C\right)-\frac{1}{n}\sum_{i=1}^{n}I(x_{i}\in C)}{\sqrt{\mathbb{P}\left(C\right)}}\geq t\right)\leq 4G(2n)e^{-\frac{nt^{2}}{2}}$$

$$\leq 4\mathcal{N}(2n)^{k}(2n+1)e^{-\frac{nt^{2}}{2}}$$

Setting the above bound to  $e^{-u}$  and solving for t, we get

$$t = \sqrt{\frac{2}{n}(u + k \log \mathcal{N}(2n) + \log(8n + 4))}$$

So, with probability at least  $1 - e^{-u}$ , for all C

$$\frac{\left(\mathbb{P}\left(C\right) - \frac{1}{n}\sum_{i=1}^{n}I(x_{i} \in C)\right)^{2}}{\mathbb{P}\left(C\right)} \leq \frac{2}{n}\left(u + k\log\mathcal{N}(2n) + \log(8n + 4)\right).$$

In particular,

$$\frac{\left(\mathbb{P}\left(yg(x) \leq \delta\right) - \frac{1}{n}\sum_{i=1}^{n}I(y_{i}g(x_{i}) \leq \delta)\right)^{2}}{\mathbb{P}\left(yg(x) \leq \delta\right)} \leq \frac{2}{n}\left(u + k\log\mathcal{N}(2n) + \log(8n + 4)\right).$$

Since  $\frac{(x-y)^2}{x}$  is convex with respect to (x,y),

$$\frac{\left(\mathbb{E}_{Y}\mathbb{P}_{x,y}\left(yg(x) \leq \delta\right) - \mathbb{E}_{Y}\frac{1}{n}\sum_{i=1}^{n}I(y_{i}g(x_{i}) \leq \delta)\right)^{2}}{\mathbb{E}_{Y}\mathbb{P}_{x,y}\left(yg(x) \leq \delta\right)}$$

$$\leq \mathbb{E}_{Y}\frac{\left(\mathbb{P}\left(yg(x) \leq \delta\right) - \frac{1}{n}\sum_{i=1}^{n}I(y_{i}g(x_{i}) \leq \delta)\right)^{2}}{\mathbb{P}\left(yg(x) \leq \delta\right)}$$

$$\leq \frac{2}{n}\left(u + k\log\mathcal{N}(2n) + \log(8n + 4)\right).$$

Recall that

(2) 
$$\mathbb{P}(yf(x) \le 0) \le \mathbb{E}_Y \mathbb{P}(yg(x) \le \delta) + e^{-k\delta^2/2}$$

and

(3) 
$$\mathbb{E}_{Y} \frac{1}{n} \sum_{i=1}^{n} I(y_{i}g(x_{i}) \leq \delta) \leq \frac{1}{n} \sum_{i=1}^{n} I(y_{i}f(x_{i}) \leq 2\delta) + e^{-k\delta^{2}/2}.$$

Choose k such that  $e^{-k\delta^2/2} = \frac{1}{n}$ , i.e.  $k = \frac{2 \log n}{\delta^2}$ . Plug (2) and (3) into (1) (look at  $\frac{(a-b)^2}{a}$ ). Hence,

$$\frac{\left(\mathbb{P}\left(yf(x) \le 0\right) - \frac{2}{n} - \frac{1}{n}\sum_{i=1}^{n}I(y_{i}f(x_{i}) \le 2\delta)\right)^{2}}{\mathbb{P}\left(yf(x) \le 0\right) - \frac{2}{n}} \le \frac{2}{n}\left(u + \frac{2\log n}{\delta^{2}}\log\mathcal{N}(2n) + \log(8n + 4)\right)$$

with probability at least  $1 - e^{-u}$ .

Recall that for SVM,  $\mathcal{N}(n) = \text{card } \{\pm K(x_i, x)\} \leq 2n$ .
