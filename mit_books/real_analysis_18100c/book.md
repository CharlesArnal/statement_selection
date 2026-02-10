## 18.100C Lecture 1 Summary

Sets. Ordered sets. Examples. Ordering pairs of numbers. Largest element (maximum) and smallest element (minimum) of a subset of an ordered set.

**Fact 1.1.** Every nonempty subset of  $\mathbb{N}$  has a least element.

Finite sets. Countable sets.

**Theorem 1.2.** Any subset of  $\mathbb{N}$  is either finite or countable.

Hence, any subset of a countable set is finite or countable.

**Theorem 1.3.** If  $S_1$  and  $S_2$  are countable,  $S_1 \cup S_2$  is countable.

Hence,  $\mathbb{Z}$  is countable.

**Theorem 1.4.**  $\mathbb{N}^2$  is countable.

Corollary 1.5. If  $S_1$  and  $S_2$  are countable,  $S_1 \times S_2$  is countable.

Corollary 1.6. If  $S_1, S_2, \ldots$  are countable sets,  $\bigcup_{k=1}^{\infty} S_k$  is countable.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 2 Summary

Axioms of a field.

**Theorem 2.1.** In any field,  $x \cdot 0 = 0$  for all x.

Examples. Field with two elements.

Axioms of an ordered field.

**Theorem 2.2.** In any ordered field, 1 > 0.

**Theorem 2.3.** In any ordered field, x > 0 if and only if -x < 0.

**Corollary 2.4.** In any ordered field,  $x^2 \ge 0$ , with equality if and only if x = 0.

Least upper bounds. Axiom of the least upper bound. The real numbers.

**Theorem 2.5.** There is a unique real number x > 0 such that  $x^2 = 2$ .

Similarly, existence of square roots for all positive real numbers:

Corollary 2.6. A real number is nonnegative if and only if it is a square.

**Theorem 2.7.** (Archimedean principle) For every real number x there is a natural number n such that n > x.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 3 Summary

**Corollary 3.1.** For every real number x > 0 there is a natural number n such that  $\frac{1}{n} < x$ .

**Corollary 3.2.** For every real number x there is an integer n such that  $x < n \le x + 1$ .

**Corollary 3.3.** For any real numbers x < y there is a rational number q such that x < q < y.

Definition of decimal expansion

$$0.9999...\sup\{0,0.9,0.99,0.999,...\}$$

**Theorem 3.4.**  $0.9999 \cdots = 1$ .

**Theorem 3.5.** Let  $I_1 \supset I_2 \supset I_3 \cdots$  be nonempty closed intervals,  $I_k = [a_k, b_k]$ . Then

$$\bigcap_{k=1}^{\infty} I_k \neq \emptyset.$$

Corollary 3.6.  $\mathbb{R}$  is uncountable.

Definition of complex numbers and their usual operations.

**Theorem 3.7.** (Cauchy-Schwarz) For complex numbers  $z_1, \ldots, z_k, w_1, \ldots, w_k$ ,

$$|z_1\bar{w}_1 + \dots + z_k\bar{w}_k|^2 \le (|z_1|^2 + \dots + |z_k|^2)(|w_1|^2 + \dots + |w_k|^2).$$

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 4 Summary

Definition of metric space. Various example (including French railroad metric, Hamming distance).

**Theorem 4.1.** (Triangle inequality for the Euclidean norm) On  $\mathbb{R}^n$ , define  $\|x\| = \sqrt{x_1^2 + \dots + x_n^2}$ . Then  $\|x + y\| \le \|x\| + \|y\|$ .

For general metric spaces: ball neighbourhoods. Open subsets.

**Theorem 4.2.** Every ball neighbourhood is an open subset.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100 C Lecture 5 Summary

Throughout, (X, d) is an arbitrary metric space.

**Theorem 5.1.** If  $E, F \subset X$  are open subsets, then so are  $E \cup F$  and  $E \cap F$ .

**Theorem 5.2.** If  $(E_i)$  is a collection of open subsets of X indexed by  $i \in I$  for some set I, then their union  $\bigcup_{i \in I} E_i$  is also open.

Corollary 5.3. Every open subset is a union of ball neighbourhoods.

Definition of limit point, closed subset.

**Theorem 5.4.** If x is a limit point of E, then  $B_r(x) \cap E$  is infinite for any r > 0.

**Corollary 5.5.** A finite subset of X has no limit points, hence is closed.

**Theorem 5.6.** If  $E, F \subset X$  are closed subsets, then so are  $E \cup F$  and  $E \cap F$ .

**Theorem 5.7.** If  $(E_i)$  is a collection of closed subsets of X indexed by  $i \in I$  for some set I, then their intersection  $\bigcap_{i \in I} E_i$  is also closed.

**Theorem 5.8.** A subset  $E \subset X$  is open if and only if its complement  $X \setminus E$  is closed.

Definition of closure  $\bar{E}$ .

**Definition 5.9.** A subset  $E \subset X$  is called dense if  $\overline{E} = X$ .

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 6 Summary

Throughout, (X, d) is an arbitrary metric space. Definition of a compact subset  $K \subset X$ .

Example 6.1. A finite set K is always compact.

**Theorem 6.2.** If  $K \subset X$  is a compact set and  $x \in X$  is a point, then  $K \subset B_r(x)$  for some r.

**Theorem 6.3.** If  $K \subset X$  is compact, it is also a closed subset.

**Theorem 6.4.** If  $K \subset X$  is compact and  $E \subset X$  is closed,  $K \cap E$  is again compact.

**Theorem 6.5.** If  $K_1, K_2 \subset X$  are compact, then so is  $K_1 \cup K_2$ .

**Theorem 6.6** ("you can run but you can't hide"). If  $K \subset X$  is compact and  $E \subset K$  is an infinite subset, then E has a limit point (in K).

**Theorem 6.7.**  $K \subset X$  is a compact subset of X if and only if K itself as a metric space is compact.

"K itself as a metric space is compact" means this: given any cover of K by subsets which are open (as subsets of K), there are finitely many of those subsets which already cover K.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 7 Summary

**Theorem 7.1.** Let (X,d) be a metric space with the following property: every countably infinite subset  $E \subset X$  has a limit point. Then X is compact.

Step 1: show that X has an at most countable dense subset (homework).

Step 2: show that if  $(U_i)_{i\in I}$  is an open cover of X, then at most countably many  $U_i$  already cover X.

Step 3: show that if  $(U_i)_{i\in I}$  is a countable open cover of X, then finitely many  $U_i$  already cover X.

**Theorem 7.2** (Heine-Borel). Every finite closed interval  $[a,b] \subset \mathbb{R}$  is compact (for the standard metric).

**Theorem 7.3.** Every bounded closed subset of  $\mathbb{R}$  is compact.

**Theorem 7.4.** Every finite closed cube  $[a_1, b_1] \times \cdots \times [a_n, b_n] \subset \mathbb{R}^n$  is compact.

**Theorem 7.5.** Every bounded closed subset of  $\mathbb{R}^n$  is compact.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 8 Summary

Convergent sequences in metric spaces. Examples.

**Theorem 8.1.** Let  $(x_n)$  be a convergent sequence, where all the  $x_n$  lie in a subset  $E \subset X$ . Then the limit x lies in  $\bar{E}$ .

**Theorem 8.2.** If  $x \in \overline{E}$ , there is a sequence  $(x_n)$ ,  $x_n \in E$ , which converges to x

Subsequence of a convergent sequence is convergent (same limit).

**Theorem 8.3.** Let (X, d) be a compact metric space. Then every sequence  $(x_n)$  in X has a convergent subsequence.

Corollary 8.4. Every bounded sequence in  $\mathbb{R}^d$  has a convergent subsequence.

Definition of Cauchy sequence. Every convergent sequence is a Cauchy sequence.

**Lemma 8.5.** Let  $(x_n)$  be a Cauchy sequence. If it has a convergent subsequence, then  $(x_n)$  itself converges (to the same point).

**Theorem 8.6.** Let (X, d) be a compact metric space. Then every Cauchy sequence converges.

Corollary 8.7. Every Cauchy sequence in  $\mathbb{R}^n$  converges.

A metric space where this happens (every Cauchy sequence converges) is called complete. So, we just showed that compact metric spaces as well as  $\mathbb{R}^n$  are complete.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 9 Summary

Subsequential limits (accumulation points) of a sequence in a metric space.

**Theorem 9.1.** The set of accumulation points of any sequence is a closed subset.

**Theorem 9.2.** Suppose that the metric space (X,d) is separable (has a countable dense subset). Then for every closed nonempty subset  $E \subset X$  there is a sequence  $(x_n)$  whose set of accumulation points is precisely E. [No proof in class]

Convergence of sequences in  $\mathbb{R}$ .

**Theorem 9.3.** Let  $(x_n)$  be a sequence which is nondecreasing,  $x_1 \le x_2 \le x_3 \cdots$ . Then  $(x_n)$  converges if and only if it is bounded above.

**Theorem 9.4.**  $x_n = (1 + 1/n)^n$  converges.

Definition of  $\limsup$  and  $\liminf$ . Improper  $\limsup$   $\pm \infty$ . Convergence of series. Series of nonnegative numbers.

**Theorem 9.5.** A series of nonnegative numbers converges if and only if its partial sums are bounded above.

**Theorem 9.6.**  $\sum_{k=0}^{\infty} x^p = 1/(1-x)$  for all |x| < 1.

**Theorem 9.7.**  $\sum_{k=1}^{\infty} 1/k^p$  diverges if  $p \leq 1$ , and converges if p > 1.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 10 Summary

**Theorem 10.1** (Euler). The series  $\sum_{p} \frac{1}{p}$ , where p ranges over all prime numbers, is divergent.

Absolute convergence of series (of real or complex numbers).

**Theorem 10.2.** Absolute convergence implies convergence.

**Theorem 10.3.** Suppose that  $\sum_i a_i$  is absolutely convergent, with value s. Then, for every  $\epsilon > 0$  there is an N such that the following holds. For every finite subset  $I \subset \mathbb{N}$  such that  $\{1, \ldots, N\} \subset I$ , we have

$$\left|\sum_{i\in I} a_i - s\right| < \epsilon.$$

**Corollary 10.4.** If  $\sum_i a_i$  is absolutely convergent, and  $\sum_i a_{\sigma(i)}$  is a reordering (which means that  $\sigma: \mathbb{N} \to \mathbb{N}$  is one-to-one and onto), then  $\sum_i a_{\sigma(i)}$  is again absolutely convergent, and has the same value.

This allows us to define absolute convergence for series  $\sum_{i \in I} a_i$ , where I is any countable set.

**Theorem 10.5** (Product theorem for series). Given series  $\sum_{i=0}^{\infty} a_i$  and  $\sum_{j=0}^{\infty} b_j$ , define their product  $\sum_{k=0}^{\infty} c_k$  by setting  $c_k = \sum_{i=0}^{k} a_i b_{k-i}$ . Suppose that  $\sum_j a_i$  is absolutely convergent, and  $\sum_j b_j$  convergent. Then  $\sum_k c_j$  is again convergent, and

$$\left(\sum_{i} a_{i}\right) \cdot \left(\sum_{j} b_{j}\right) = \sum_{k} c_{k}.$$

Root criterion for absolute convergence.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 11 Summary

Definition of power series. Convergence radius  $\rho$  of a power series.

**Theorem 11.1.**  $f(z) = \sum_{k=0}^{\infty} a_k z^k$  is absolutely convergent for all complex numbers  $|z| < \rho$ .

The series never converges for  $|z| > \rho$ . However, for  $|z| = \rho$  several types of behaviour are possible.

**Theorem 11.2.** Take a series  $f(z) = \sum_{k=0}^{\infty} a_k z^k$ , where  $a_k \in \mathbb{R}$  and  $a_0 \ge a_1 \ge a_2 \ge \cdots$ ,  $\lim_{k\to\infty} a_k = 0$ . Suppose that the convergence radius is 1. Then the series converges for all z such that |z| = 1 and  $z \ne 1$ .

**Theorem 11.3** (Abel; not proved in class). Take a series  $f(z) = \sum_{k=0}^{\infty} a_k z^k$  with  $a_k \in \mathbb{R}$ . Suppose that  $\sum_k a_k$  is convergent. Then its value is  $\lim_{t\to 1} f(t)$ , where the limit is taken over real t<1.

The exponential series  $\exp(z)$ . It has infinite convergence radius (converges absolutely for all  $z \in \mathbb{C}$ ).

**Theorem 11.4.**  $\exp(z) \exp(w) = \exp(z + w)$ .

**Theorem 11.5.**  $|\exp(z)| = \exp(Re(z))$ .

Definition of sin and cos by  $\exp(it) = \cos(t) + i\sin(t)$ . Power series for cos and sin.

**Theorem 11.6.**  $\cos^2(t) + \sin^2(t) = 1$ .

The trigonometric addition formulae.

Short discussion of Fourier series.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis
Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 12 Summary

Let  $(X, d_X)$  and  $(Y, d_Y)$  be metric spaces, and  $f: X \to Y$  a map.

**Definition 12.1.** f is continuous (everywhere) if: whenever  $(x_n)$  is a sequence in X converging to some point  $p \in X$ , then  $(f(x_n))$  converges to f(p) in Y.

**Definition 12.2.** f is continuous (everywhere) if: for any open subset  $V \subset Y$ , the preimage  $f^{-1}(V) = \{x \in X : f(x) \in V\}$  is an open subset of X.

**Definition 12.3.** f is continuous (everywhere) if: for all  $p \in X$  and all  $\epsilon > 0$ , there is a  $\delta > 0$  such that if  $d_X(x, p) < \delta$  then  $d_Y(f(x), f(p)) < \epsilon$ .

The "such that..." part can be reformulated as follows: " $f(B_{\delta}(x)) \subset B_{\epsilon}(f(x))$ ". Or as follows: " $B_{\delta}(x) \subset f^{-1}(B_{\epsilon}(f(x)))$ ".

**Definition 12.4.** f is continuous (everywhere) if: for any closed subset  $W \subset Y$ , the preimage  $f^{-1}(W)$  is a closed subset of X.

**Theorem 12.5.** The four definitions above are equivalent.

**Theorem 12.6.** If  $f: X \to Y$  and  $g: Y \to Z$  are continuous, then the composition  $g \circ f: X \to Z$  is continuous.

**Corollary 12.7.** If  $f, g: X \to \mathbb{R}$  (with the usual metric on the real numbers) are continuous, then f(x) + g(x) and f(x)g(x) are continuous.

Corollary 12.8. If  $f: X \to \mathbb{R}$  is continuous and everywhere nonzero, then 1/f is continuous.

**Theorem 12.9.** If  $f: X \to Y$  is continuous and  $K \subset X$  is compact, then  $f(K) \subset Y$  is compact.

**Corollary 12.10.** If X is a compact metric space and  $f: X \to \mathbb{R}$  a continuous function, then f is bounded and has a minimum and maximum.

**Corollary 12.11.** Let X be a compact metric space, and  $f: X \to Y$  a map which is continuous, one-to-one, and onto. Then the inverse map  $f^{-1}: Y \to X$  (defined by  $f(x) = y \Leftrightarrow x = f^{-1}(y)$ ) is again continuous.

We return to basic definitions. Let  $f: X \to Y$  be a map between metric spaces. Fix a point  $p \in X$ .

**Definition 12.12.** f is continuous at p if: whenever  $(x_n)$  is a sequence in X converging to (our particular point) p, then  $(f(x_n))$  converges to f(p).

**Definition 12.13.** f is continuous at p if: for all  $\epsilon > 0$ , there is a  $\delta > 0$  such that if  $d_X(x,p) < \delta$  then  $d_Y(f(x),f(p)) < \epsilon$ .

**Theorem 12.14.** The two definitions above are equivalent.

**Definition 12.15.** Let X,Y be metric spaces,  $f:X\to Y$  a map, and  $p\in X$  a point. We write

$$\lim_{x \to p} f(x) = q \in Y$$

if the following holds: for all  $\epsilon > 0$ , there is a  $\delta > 0$  such that if  $x \neq p$  and  $d_X(x,p) < \delta$ , then  $d_Y(f(x),f(p)) < \epsilon$ .

The advantage of this is that it makes sense even if f is defined only on  $X \setminus \{p\}$ .

**Lemma 12.16.** If  $f: X \to Y$  satisfies  $\lim_{x \to p} f(x) = f(p)$ , then it is continuous at p (the converse also holds).

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 13 Summary

**Example 13.1.** The map  $f: \mathbb{R}^2 \to \mathbb{R}$ , f(x,y) = xy, is continuous.

**Example 13.2.** The map  $\exp : \mathbb{R} \to \mathbb{R}$  is continuous (the same holds for  $\exp$  of a complex number, hence also for  $\cos$  and  $\sin$ ).

**Theorem 13.3.** (Intermediate Value Theorem) Let  $f : [a,b] \to \mathbb{R}$  be a continuous map, such that  $f(a) \leq 0$ ,  $f(b) \geq 0$ . Then there is some x such that f(x) = 0.

**Corollary 13.4.** Let  $f:[a,b] \to \mathbb{R}$  be a continuous map. Then its image is a closed interval [c,d].

**Corollary 13.5.** Let  $f:[a,b] \to \mathbb{R}$  be a continuous map which is strictly increasing (x < y implies f(x) < f(y)). Then f is one-to-one onto a closed interval [c,d]. Moreover, the inverse map  $f^{-1}:[c,d] \to [a,b]$  is continuous.

**Example 13.6.** The map exp, from the real numbers to the positive real numbers, is strictly increasing and onto. We call its inverse the natural logarithm  $\log:(0,\infty)\to\mathbb{R}$ . This automatically satisfies  $\log(ab)=\log(a)+\log(b)$ , and is continuous.

Let  $(X, d_X)$  and  $(Y, d_Y)$  be metric spaces, and  $f: X \to Y$  a map.

**Definition 13.7.** f is uniformly continuous if: for any  $\epsilon > 0$  there is a  $\delta > 0$  such that if  $d_X(x,y) < \delta$ , then  $d_Y(f(x),f(y)) < \epsilon$ .

Every absolutely continuous map is continuous.

**Theorem 13.8.** If X is compact, every continuous map  $f: X \to Y$  is uniformly continuous.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis
Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 14 Summary

Take a function  $f:U\to\mathbb{R}$  defined on a subset  $U\subset\mathbb{R}$ . Let p be an interior point of U.

**Definition 14.1.** f is differentiable at p, with derivative  $f'(p) \in \mathbb{R}$ , if

$$\lim_{x \to p} \frac{f(x) - f(p)}{x - p} = f'(p).$$

(Occasionally we will also use derivatives f'(a), f'(b) for a function  $f:[a,b] \to \mathbb{R}$ ; those are defined in the same way).

**Definition 14.2.** f is differentiable at p, with derivative  $f'(p) \in \mathbb{R}$ , if one can write

$$f(x) = f(p) + f'(p)(x - p) + r(x)(x - p),$$

and the function r satisfies  $\lim_{x\to p} r(x) = 0$ .

**Definition 14.3.** f is differentiable at p, with derivative  $f'(p) \in \mathbb{R}$ , if the following holds. For every  $\epsilon > 0$  there is a  $\delta > 0$  such that if  $|x - p| < \delta$ , then

$$|f(x) - f(p) - f'(p)(x - p)| \le \epsilon |x - p|.$$

Theorem 14.4. The three definitions above are equivalent.

**Theorem 14.5.** If f is differentiable at p, it is also continuous at p.

**Example 14.6.**  $f(x) = \exp(x)$  is differentiable, and its derivative is  $f'(x) = \exp(x)$ . (The same argument can be used to prove the familiar formulae for derivatives of  $\sin$  and  $\cos$ ).

Sum, product, and quotient rule (not discussed in class). Here's the chain rule:

**Theorem 14.7.** Let  $g: U \to \mathbb{R}$  and  $f: V \to \mathbb{R}$  be functions, and p an interior point of U, such that g(u) is an interior point of V. Suppose that g is differentiable and p, and f is differentiable at g(p). Then p is an interior point of the domain of definition of  $f \circ g$ ;  $f \circ g$  is differentiable at p; and

$$(f \circ g)'(p) = f'(g(p))g'(p).$$

**Theorem 14.8** (Rolle's theorem). Let  $f : [a,b] \to \mathbb{R}$  be continuous on all of [a,b], differentiable on (a,b), and such that f(a) = f(b). Then there is some  $p \in (a,b)$  such that f'(p) = 0.

**Theorem 14.9** (Mean Value Theorem). Let  $f : [a, b] \to \mathbb{R}$  be continuous on all of [a, b], and differentiable on (a, b). Then there is some  $p \in (a, b)$  such that

$$\frac{f(b) - f(a)}{b - a} = f'(p).$$

**Theorem 14.10** (Generalized Mean Value Theorem). Let  $f, g : [a, b] \to \mathbb{R}$  be two functions which are continuous on all of [a, b], and differentiable on (a, b). Then there is some  $p \in (a, b)$  such that

$$(f(b) - f(a))g'(p) = (g(b) - g(a))f'(p).$$

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 15 Summary

**Theorem 15.1.** Suppose that f and g are functions satisfying f(g(x)) = x. Take a point p in the interior of the domain of definition of g, and such that f(x) lies in the interior of the domain of definition of f. Suppose that there is some  $\delta > 0$  such that g is increasing on the interval  $(p - \delta, p + \delta)$ , and that g'(p) exists and is positive (alternatively, g could be strictly decreasing and g'(p) could be negative). Then f' is differentiable at g(p), and

$$f'(g(p)) = \frac{1}{g'(p)}.$$

Only differentiability needs to be proved; the formula for the derivative then follows from the chain rule.

**Example 15.2.**  $f(x) = \log(x)$  is differentiable for all x > 0, and f'(x) = 1/x.

**Example 15.3.** For any natural number n, the function  $f(x) = x^{1/n}$  is differentiable for all x > 0, and  $f'(x) = (1/n)x^{1/n-1}$ .

Definition of higher differentiability. The rest of this lecture is about forms of Taylor's theorem.

**Theorem 15.4.** Suppose that f is m times differentiable at p. Then one can write

$$f(x) = f(p) + (x-p)f'(p) + \frac{(x-p)^2}{2}f''(p) + \dots + \frac{(x-p)^m}{m!}f^{(m)}(p) + r(x)(x-p)^m,$$
where  $\lim_{x\to p} r(x) = 0$ .

Equivalently:

**Theorem 15.5.** Suppose that f is m times differentiable at p. Then for each  $\epsilon > 0$  there exists a  $\delta > 0$  such that if  $|x - p| < \delta$ , then

$$\left| f(x) - f(p) - (x - p)f'(p) - \frac{(x - p)^2}{2}f''(p) - \dots - \frac{(x - p)^m}{m!}f^{(m)}(p) \right| \le \epsilon |x - p|^m.$$

**Theorem 15.6.** Suppose that f is m times differentiable in the (closed) interval bounded by a and b; that  $f^{(m)}$  is continuous in the same interval; and that  $f^{(m+1)}$  exists at all interior points of that interval. Then

$$f(b) = f(a) + (b-a)f'(a) + \frac{(b-a)^2}{2}f''(a) + \dots + \frac{(b-a)^m}{m!}f^{(m)}(a) + \frac{(b-a)^{m+1}}{(m+1)!}f^{(m+1)}(x)$$

for some point x in the interior of the interval bounded by a and b.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 16 Summary

Pointwise convergence. Examples. Uniform convergence.

**Theorem 16.1** (Cauchy convergence criterion). A sequence of functions  $f_n: X \to \mathbb{R}$  is uniformly convergent if and only if the following holds. For every  $\epsilon > 0$  there is an N such that if  $m, n \geq N$  then  $|f_n(x) - f_m(x)| < \epsilon$  for all x.

Uniform convergence of series of functions.

Corollary 16.2. (Weierstrass criterion) Let  $\sum_{n=0}^{\infty} f_n$  be a series of functions. Suppose that there are constants  $M_n$  such that  $|f_n(x)| \leq M_n$  for all n, x, and such that  $\sum_{n=0}^{\infty} M_n$  converges. Then  $\sum_{n=0}^{\infty} f_n$  converges uniformly.

Corollary 16.3. Let  $\sum_{n=0}^{\infty} a_n x^n$  be a power series with radius of convergence  $\rho > 0$ . Then that series converges uniformly on any interval [-r, r] with  $r < \rho$ .

**Theorem 16.4.** If  $(f_n)$  are continuous functions converging uniformly towards f, then f is again continuous.

**Corollary 16.5.** Let  $f(x) = \sum_{n=0}^{\infty} a_n x^n$  be a power series with radius of convergence  $\rho > 0$ . Then f is continuous on  $(-\rho, \rho)$ .

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis
Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 17 Summary

Weierstrass' example of a nowhere differentiable continuous function.

**Theorem 17.1.** Let  $(f_n)$  be a sequence of functions  $[a,b] \to \mathbb{R}$  which are everywhere differentiable. Suppose that  $(f'_n)$  is uniformly convergent. Suppose also that  $(f_n(x_0))$  is convergent for just one point  $x_0 \in [a,b]$ . Then  $(f_n)$  itself is uniformly convergent, the limit f is differentiable everywhere, and

$$f' = \lim_{n \to \infty} f'_n.$$

**Corollary 17.2.** If  $f(x) = \sum_{n=0}^{\infty} a_n x^n$  has convergence radius  $\rho > 0$ , then it is everywhere differentiable in  $(-\rho, \rho)$ , and its derivative is  $f'(x) = \sum_{n=1}^{\infty} a_n n x^{n-1}$  (which has the same convergence radius).

**Corollary 17.3.** If  $f(x) = \sum_{n=0}^{\infty} a_n x^n$  has convergence radius  $\rho > 0$ , then it is infinitely often differentiable in  $(-\rho, \rho)$ .

**Theorem 17.4.** Let  $(f_n)$  be a sequence of functions  $[a,b] \to \mathbb{R}$  which are everywhere differentiable. Suppose that there are constants C, D such that  $|f_n(x)| \le C$ ,  $|f'_n(x)| \le D$  for all n and x. Then  $(f_n)$  has a uniformly convergent subsequence.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis
Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 18 Summary

Definitions of  $\mathcal{B}(X)$  (the space of bounded functions),  $\mathcal{C}(X)$  (the space of continuous functions) as metric spaces. Also, for X = [a, b], definition of  $\mathcal{B}^1(X)$  (the space of functions with bounded derivative) as a metric space.

**Theorem 18.1.**  $\mathcal{B}(X)$  is a complete metric space.

**Theorem 18.2.** C(X) is a closed subspace of B(X), hence itself complete.

**Theorem 18.3.** Take a bounded subset of  $\mathcal{B}^1(X)$ , consider it as a subset of  $\mathcal{C}(X)$ , and take its closure with respect to the metric of  $\mathcal{C}(X)$ . Then that closure is a compact subset of  $\mathcal{C}(X)$ .

Uniform approximation by step functions and by piecewise linear functions.

**Theorem 18.4.** Let X be a compact metric space. Suppose that  $A \subset C(X)$  is a subset with the following properties: (i) if  $f, g \in A$ , then  $\max(f, g) \in A$  and  $\min(f, g) \in A$ ; (ii) for any two points  $x \neq y$  and any real numbers a, b, there is an  $f \in A$  such that f(x) = a, f(y) = b. Then A is dense in C(X).

**Theorem 18.5** (Stone-Weierstrass). Let X be a compact metric space. Suppose that  $A \subset C(X)$  is a subset with the following properties: (i) all constant functions are in A; (ii) if  $f, g \in A$ , then  $f + g \in A$ ; (iii) if  $f, g \in A$ , then  $f \cdot g \in A$ ; (iv) for any two points  $x \neq y$ , there is an  $f \in A$  such that  $f(x) \neq f(y)$ . Then A is dense in C(X).

Application: polynomials, trigonometric polynomials.

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis
Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 19 Summary

A partition P of [a, b] is given by  $a = x_0 < x_1 < \cdots < x_n = b$ , for some n.

**Definition 19.1.** A function  $f:[a,b] \to \mathbb{R}$  is called piecewise linear if there is a partition P such that f is linear (of the form  $c_i x + d_i$ ) on each interval  $[x_{i-1}, x_i]$ .

To get integration theory started, one defines the integral of a piecewise linear function to be

$$\int_{a}^{b} f(x) \, dx \stackrel{\text{def}}{=} \sum_{i=1}^{n} \frac{1}{2} (f(x_{i-1}) + f(x_{i})) \Delta x_{i}$$

where  $\Delta x_i = x_i - x_{i-1}$ . This is the geometric formula for the area of a trapezoid (with sign), added up over *i*. Again by elementary geometric arguments, the integral of a piecewise linear function is independent of the choice of partition.

**Proposition 19.2.** (i) If f(x) = c is constant,  $\int_a^b f(x)dx = c(b-a)$ . (ii) Suppose that f, g are piecewise linear functions. Then

$$\int_{a}^{b} f(x) + g(x) \, dx = \int_{a}^{b} f(x) \, dx + \int_{a}^{b} g(x) \, dx.$$

(iii) Suppose that f is a piecewise linear function and c is a constant. Then

$$\int_a^b c f(x) dx = c \int_a^b f(x) dx.$$

(iv) If a piecewise linear function f satisfies  $f(x) \ge 0$  for all  $x \in [a,b]$ , then  $\int_a^b f(x) dx \ge 0$ .

We extend this notion of integral to all continuous functions by uniform convergence.

**Lemma 19.3.** Any continuous function  $f : [a, b] \to \mathbb{R}$  is the uniform limit of a sequence of piecewise linear functions.

**Theorem 19.4.** There is a unique way of assigning to each continuous  $f:[a,b] \to \mathbb{R}$  a number  $\int_a^b f(x) \ dx \in \mathbb{R}$  such that: if f is piecewise linear, then we get back the integral as defined before; and if  $f_n \to f$  uniformly, then  $\int_a^b f_n(x) \ dx \to \int_a^b f(x) \ dx$ .

The integral of continuous functions defined in this way has the same properties as that for piecewise linear functions stated in the Proposition above.

**Definition 19.5.** A function  $f:[a,b] \to \mathbb{R}$  is a step function if there is a partition P such that f is constant on each open interval  $(x_{i-1},x_i)$ .

One can use the geometric formula for the integral of a step function (sum of areas of rectangles) as a starting point, and then extend that by uniform convergence. This yields a notion of integral which covers all continuous functions as well as some others (but still not as much as the Riemann integral).

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis
Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 20 Summary

Definition of Riemann-Stielties (RS) integral (of a bounded function, with respect to a nondecreasing function  $\alpha$ ).

Example 20.1. Constant functions are always RS integrable, and

$$\int_{a}^{b} c \, d\alpha = c \left( \alpha(b) - \alpha(a) \right).$$

**Example 20.2.** Take some  $x_* \in (a,b)$ , and define  $\alpha$  to be the jump function

$$\alpha(x) = \begin{cases} 0 & x < x_*, \\ 1 & x \ge x_*. \end{cases}$$

f is RS-integrable with respect to  $\alpha$  if  $\lim_{x\to x_*-} f(x) = f(x_*)$  holds (in particular, this is true if f is continuous at  $x_*$ ). In that case,

$$\int_a^b f(x) \ d\alpha = f(x_*).$$

**Theorem 20.3.** (i) f is RS-integrable if and only if: for every  $\epsilon > 0$ , there is a partition P such that

$$S(f, \alpha, P) - s(f, \alpha, P) < \epsilon$$
.

(ii) Suppose that P is a partition as in (i). For each i, take a point  $x_i^* \in$  $[x_{i-1}, x_i]$ . Then

$$\left| \sum_{i} f(x_i^*) \Delta \alpha_i - \int_a^b f \ d\alpha \right| < \epsilon.$$

**Theorem 20.4.** Continuous functions f are RS-integrable for any  $\alpha$ .

**Theorem 20.5.** If  $(f_n)$  are RS-integrable with respect to  $\alpha$ , and  $f_n \to f$  uniformly, then f is RS-integrable for the same  $\alpha$ , and

$$\int_{a}^{b} f \ d\alpha = \lim_{n \to \infty} \int_{a}^{b} f_n \ d\alpha.$$

**Theorem 20.6.** (i) If f and g are RS-integrable, then f+g is RS-integrable, and  $\int_a^b f + g \ d\alpha = \int_a^b f \ d\alpha + \int_a^b g \ d\alpha$ .

(ii) If f is RS-integrable and c is a constant, then c f is RS-integrable, and  $\int_a^b c f \ d\alpha = c \int_a^b f \ d\alpha$ .

(iii) If f is RS-integrable and  $f(x) \geq 0$  for all x, then  $\int_a^b f \ d\alpha \geq 0$ .

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis
Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 21 Summary

**Theorem 21.1.** If f is RS-integrable and  $\phi$  is continuous (on some closed interval containing all values f(x),  $x \in [a,b]$ ), then  $\phi(f)$  is RS-integrable (for the same  $\alpha$ ).

**Corollary 21.2.** If f and g are RS-integrable, then fg is RS-integrable (for the same  $\alpha$ ).

Corollary 21.3. If f is RS-integrable, then |f| is RS-integrable, and  $|\int_a^b f \ d\alpha| \le \int_a^b |f| \ d\alpha$ .

The following is easy:

**Theorem 21.4.** Suppose that  $\phi$  is strictly increasing and continuous, and maps [A,B] to [a,b]. Then if  $f:[a,b] \to \mathbb{R}$  is RS-integrable for some  $\alpha$ ,  $g=f(\phi):[A,B] \to \mathbb{R}$  is RS-integrable for  $\beta=\alpha(\phi)$ , and

$$\int_{a}^{b} f \, d\alpha = \int_{A}^{B} g \, d\beta.$$

But this is hard:

**Theorem 21.5.** Suppose that  $\alpha$  is everywhere differentiable, and  $\alpha'$  is Riemann-integrable. Let f be a function which is R-S integrable for  $\alpha$ . Then  $f(x)\alpha'(x)$  is Riemann-integrable, and

$$\int_{a}^{b} f(x)\alpha'(x) \ dx = \int_{a}^{b} f \ d\alpha.$$

Together they yield the following form of the substitution rule:

**Corollary 21.6.** Suppose that  $\phi$  is strictly increasing, differentiable, maps [A,B] to [a,b], and that  $\phi'$  is Riemann integrable. Let  $f:[a,b] \to \mathbb{R}$  be a Riemann integrable function. Then  $f(\phi(x))\phi'(x):[A,B] \to \mathbb{R}$  is again Riemann integrable, and

$$\int_A^B f(\phi(x))\phi'(x) \ dx = \int_a^b f(x) \ dx.$$

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis
Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 22 Summary

**Lemma 22.1.** If f is Riemann-Stjeltjes integrable on [a,b], then the same holds for any smaller closed interval. Moreover, for any  $c \in (a,b)$ ,

$$\int_{a}^{c} f \, d\alpha + \int_{c}^{b} f \, d\alpha = \int_{a}^{b} f \, d\alpha.$$

Here are two different versions of the Fundamental Theorem of Calculus:

**Theorem 22.2.** Suppose that  $f:[a,b] \to \mathbb{R}$  is Riemann integrable, and define

$$F(x) = \int_{a}^{t} f(t) dt.$$

Then F is continuous. Moreover, if f is continuous at some point  $x_0$ , then F is differentiable there, and  $F'(x_0) = f(x_0)$ .

**Theorem 22.3.** Suppose that  $f:[a,b] \to \mathbb{R}$  is differentiable, and f' is Riemann integrable. Then

$$\int_a^b f'(x) \, dx = f(b) - f(a).$$

Reminder: radius of convergence of a power series.

**Lemma 22.4.** Suppose that  $f(x) = \sum_{k=0}^{\infty} a_k x^k$  has radius of convergence  $\rho > 0$ . Then f is differentiable at all points  $x \in (-\rho, \rho)$ , and its derivative is

$$f'(x) = \sum_{k=1}^{\infty} a_k k x^{k-1},$$

which is a power series with the same radius of convergence  $\rho$ .

**Example 22.5.** The function  $f(x) = x + x^2/2 + x^3/x + \cdots$ , with radius of convergence 1, satisfies f'(x) = 1/(1-x).

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis
Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 23 Summary

General discussion of the Taylor series of an (arbitrarily differentiable) function. This can be quite badly behaved - it may not converge; and even if it does, it may not converge to the original function.

Reminder: definition of  $\exp(x)$ ,  $\sin(x)$ ,  $\cos(x)$ . How to derive their derivatives. Euler's formula  $\exp(it) = \cos(t) + i\sin(t)$ .

**Lemma 23.1.** There is a smallest number  $\pi > 0$  such that  $\cos(\pi/2) = 0$ . Moreover, for that number  $\sin(\pi/2) = 1$ .

**Lemma 23.2.**  $\exp(x+2\pi i)=\exp(x)$ , for all complex numbers x.

Definition of log as inverse function of exp.

**Lemma 23.3.**  $\log(x)$  is differentiable for all x > 0, and its derivative is 1/x.

**Theorem 23.4.** The series  $x - x^2/2 + x^3/3 - x^4/4 + \cdots$  converges to  $\log(1+x)$  inside its radius of convergence (which means for |x| < 1).

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.100C Lecture 24 Summary

Consider Fourier series

$$a_0 + \sum_{k=1}^{\infty} a_k \sin(kx) + \sum_{k=1}^{\infty} \tilde{a}_k \cos(kx).$$

**Lemma 24.1.** If  $\sum_{k} |a_k|$  and  $\sum_{k} |\tilde{a}_k|$  converge, the Fourier series is uniformly convergent for  $x \in \mathbb{R}$ .

In that situation, the Fourier series defines a continuous  $2\pi$ -periodic function f(x).

**Lemma 24.2.** If  $\sum_k k|a_k|$  and  $\sum_k k|\tilde{a}_k|$  converge, the function f(x) defined by the Fourier series is differentiable, and its derivative is

$$\sum_{k=1}^{\infty} a_k k \cos(kx) - \sum_{k=1}^{\infty} \tilde{a}_k k \sin(kx).$$

It's more convenient to think in terms of complex-valued functions, where Fourier series are

$$\sum_{k\in\mathbb{Z}} c_k \exp(ikt).$$

(convergence here means, say, convergence of the sum from k=-N to k=N, as  $N\to\infty$ ). Given any  $2\pi$ -periodic Riemann integrable function h(x), one defines its Fourier coefficients

$$c_k = \frac{1}{2\pi} \int_{-\pi}^{\pi} h(x)e^{-ikx}dx.$$

**Theorem 24.3.** Suppose that h(x) is differentiable and h'(x) is continuous. Then the Fourier series  $\sum_k c_k \exp(ikx)$  converges uniformly to the original function h(x).

**Theorem 24.4** (Parseval's theorem). Let h(x) be a  $2\pi$ -periodic Riemann integrable function. Define its Fourier sums as

$$s_N(h,x) = \sum_{k=-N}^{N} c_k e^{ikx}.$$

Then we have "average convergence"

$$\lim_{N \to \infty} \int_{-\pi}^{\pi} |h(x) - s_N(h, x)|^2 dx = 0$$

MIT OpenCourseWare http://ocw.mit.edu

18.100C Real Analysis Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.
