## 18.103. Lecture 1: Introduction.

One of the main goals this course is to establish rules for the limiting behavior of functions so that we can deal with functions with as much confidence as we do real or complex numbers. Today we give a preview, without any proofs.

Part 2. Fourier Analysis (starting about week 7). A complex-valued, periodic function f(x) of period  $2\pi$  is represented by the Fourier series

$$f(x) = \sum_{n = -\infty}^{\infty} c_n e^{inx}, \quad c_n \in \mathbb{C}$$
 (1)

The family

$$e^{inx}$$
,  $n \in \mathbb{Z} = \{0, \pm 1, \pm 2, \dots\}$ 

should be viewed as a basis for the infinite-dimensional vector space of periodic functions. The remarkably simple and practical formula of Fourier (from the early 1800s) for the coefficients  $c_n$  is

$$c_n = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x)e^{-inx} dx$$
 (2)

Formula (2) giving the correspondence  $f \mapsto c_n$  is the companion to Formula (1) which computes  $c_n \mapsto f$ .

Consider the partial sum

$$S_N(x) = \sum_{|n| \le N} c_n e^{inx}$$

The main question in the second half of the course is whether and in what sense

$$\lim_{N\to\infty} S_N = f ?$$

The cleanest answer (among many) is that convergence works in the following average sense. Assume that

$$\sum_{n=-\infty}^{\infty} |c_n|^2 < \infty$$

then

$$\lim_{N \to \infty} \int_{-\pi}^{\pi} |f(x) - S_N(x)|^2 dx = 0$$

This conclusion is based on remarkably simple formulas based on the Pythagorean theorem. Define the length of a function in terms of its Fourier coefficients as

$$||f|| = \sqrt{\cdots + |c_{-1}|^2 + |c_0|^2 + |c_1|^2 + \cdots}$$

This gives a definition of the length of f because the correspondence given by (2) and (1) between f and the sequence of coefficients  $c_n$  is one-to-one. This length can also be expressed directly in terms of f as follows.

Theorem (Parseval's formula) 
$$|c_n|^2 = \frac{1}{2\pi} \int_{-\pi}^{\pi} |f(x)|^2 dx$$

Because the series has a finite sum, its tail  $|c_n|^2$  tends to zero. Hence

$$f - S_N = c_n e^{inx} \implies f - S_N^2 = |c_n|^2 \longrightarrow 0 \text{ as } N \to \infty$$

In other words, by Parseval's formula, the square mean distance from f to  $S_N$  tends to zero:

$$\int_{-\pi}^{\pi} |f(x) - S_N(x)|^2 dx = 2\pi |c_n|^2 \longrightarrow 0, \text{ as } N \to \infty$$

Part 1. Lebesgue measure and integrals. The task in the first half of the course is to introduce Lebesgue measure and establish properties of the Lebesgue integral. Our textbook (Adams and Guillemin) introduces Lebesgue measure using motivation and examples from probability theory. An equally important motivation (that will only become clear in the second half) is that the systematic study of Fourier series requires the Lebesgue integral. The square mean convergence of Fourier series and Parseval's formula cannot be stated accurately in proper generality without the Lebesgue integral and Lebesgue integrable functions f(x).

Probability theory. A Bernoulli sequence is an infinite sequence of outcomes

$$HTTHTTTH \cdots$$

of coin tosses with H representing heads and T representing tails. Assume that heads and tails are equally likely and that the tosses are independent of each other. Then the 8-letter initial sequence displayed has probability  $2^{-8}$  as does each of the  $2^{8}$  possible words of length 8 in the letters H and T. The first paradox we face is that the probability of any single infinite string is zero (the limit of  $2^{-n}$  as  $n \to \infty$ ), whereas if we add up all possibilities we get

$$0 = 1$$
 ??

It turns out that this paradox is a real contradiction that has to be avoided. The collection of outcomes is uncountably infinite. (This is proved by the Cantor diagonal argument and is the subject of our first homework exercise.) We will have to give up on sums of probabilities with uncountably many terms.

Given that some operations are illegal, our job will be to figure out what operations are legal and give meaningful probability values. Fortunately there are many meaningful questions we can answer. For  $n \geq 0$ , consider

 $S_n$  = number of heads minus number of tails in first n tosses

The trajectory of  $S_n$  is known as a random walk (in one dimension, that is, on the integers  $\mathbb{Z}$ ). I graphed this for the example HTTHTTTH:  $S_0 = 0$ ,  $S_1 = 1$ ,  $S_2 = 0$ ,  $S_3 = -1$ , etc. A statement referring to full, infinite strings can only make sense using a correct formulation

of probability on the uncountable collection of Bernoulli sequences. Here is an example that does make sense and has a coherent answer.

## Strong Law of Large Numbers.

With probability 1, 
$$\lim_{n\to\infty} \frac{S_n}{n} = 0$$

Combining probability and Fourier analysis. After we have developed probability theory on Bernoulli sequences, using a correspondence with Lebesgue measure on the unit interval, we will discuss the Lebesgue integral and some Fourier analysis. Then we will use some Fourier analysis to prove more theorems in probability. By the end of the semester we will have all the tools to discuss the continuum limit of a (suitably scaled) random walk, namely *Brownian motion*.

The first rigorous formulation of Brownian motion was given by Norbert Wiener (in the math department at MIT in the 1920s) before probability theory itself was on a fully rigorous footing! Brownian motion starting from B(0) = 0 is given on  $0 \le t \le \pi$  by

$$B(t) = a_0 t + \sum_{k=1}^{\infty} a_k \frac{\sin kt}{k}$$

where the  $a_k$ , k = 1, 2, ... are independent, standard (mean 0, variance 1) normal random variables. (The coefficient  $a_0$  is also a normal random variable, but with a different variance, which we will figure out later. In lecture, for simplicity, I omitted  $a_0$  initially. Without the  $a_0t$  term, B(t) returns to 0 at  $t = \pi$  and is known as a Brownian bridge.)

Wiener showed that with probability 1, B(t) is continuous but not differentiable. Curiously, with the help of Fourier series representations, even non-differentiable functions can be differentiated. The catch is that the answer is not a function. The derivative

$$dB/dt = \int_{k=0}^{\infty} a_k \cos kt$$

is known as "white noise." With probability 1 the series on the right is not convergent. Although with probability 1 this series does not represent a function (much less a continuous function), it nevertheless has a good interpretation as a so-called "generalized function." You have already seen one such generalized function in 18.03, namely the delta function. We will discuss generalized functions much later in the course.

In Lecture 2, we will begin the systematic theory of Lebesgue measure, starting with the case of the unit interval, in tandem with probability theory for Bernoulli sequences, following the Adams-Guillemin text.

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.103 Fall 2013

## 1. Fourier Series, Part 1.

We will consider several function spaces during our study of Fourier series. When we talk about  $L^p((-\pi,\pi))$ , it will be convenient to include the factor  $1/2\pi$  in the norm:

$$||f||_p = \left(\frac{1}{2\pi} \int_{-\pi}^{\pi} |f(x)|^p dx\right)^{1/p}.$$

In particular, the Lebesgue space  $L^2((-\pi,\pi))$  is a Hilbert space with inner product

$$\langle f, g \rangle = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x) \overline{g(x)} \, dx \,.$$

The starting place for the theory of Fourier series is that the family of functions  $\{e^{inx}\}_{n=-\infty}^{\infty}$  is orthonormal, that is

$$\langle e^{inx}, e^{imx} \rangle = 0, \ n \neq m; \quad \langle e^{inx}, e^{inx} \rangle = 1, \quad n, \ m \in \mathbf{Z}.$$

The Fourier coefficients of f are defined by

$$\hat{f}(n) = \langle f, e^{inx} \rangle = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x)e^{-inx} dx, \quad n \in \mathbf{Z}.$$

 $(\mathbf{Z} = \{0, \pm 1, \pm 2, \dots\})$  represents the integers.) The definition of Fourier the coefficients  $\hat{f}(n)$  also makes sense for  $f \in L^1((-\pi, \pi))$ . The main issue is to find the ways in which the Fourier series

$$\sum \hat{f}(n)e^{inx}$$

represents the function f.

The first basic remark is that for all  $f \in L^1((-\pi, \pi))$ ,

$$|\hat{f}(n)| \le ||f||_1$$

This is proved by putting the absolute value inside the integral:

$$|\hat{f}(n)| = \left| \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x)e^{-inx} dx \right| \le \frac{1}{2\pi} \int_{-\pi}^{\pi} |f(x)| dx = ||f||_1.$$

Let  $C^k(\mathbf{R})$ , k = 0, 1, 2, ..., denote the complex-valued functions that are k times continuously differentiable on  $\mathbf{R}$ .  $C(\mathbf{R}) = C^0(\mathbf{R})$  denotes continuous functions on  $\mathbf{R}$ , and  $f \in C^k(\mathbf{R})$  if and only if  $f' \in C^{k-1}(\mathbf{R})$ . Denote by  $C^{\infty}(\mathbf{R})$  the infinitely differentiable functions on  $\mathbf{R}$ .

If the function f is periodic of period  $2\pi$   $(f(x+2\pi)=f(x))$ , then f defines a function on  $\mathbf{T}=\mathbf{R}/2\pi\mathbf{Z}$ , the quotient space of  $\mathbf{R}$  under the equivalence relation  $x\sim x'$  if  $x-x'\in 2\pi\mathbf{Z}$ . We will use the notation  $C^k(\mathbf{T})$  for  $C^k$  functions on  $\mathbf{T}$ , which are identified with  $2\pi$ -periodic functions in  $C^k(\mathbf{R})$ . We will identify functions in  $L^p((-\pi,\pi))$  with  $2\pi$  periodic functions on  $\mathbf{R}$  and write  $L^p(\mathbf{T})$ .

The proof in the preceding set of lecture notes that  $C_0^{\infty}(\mathbf{R})$  is dense in  $L^p(\mathbf{R})$ ,  $1 \leq p < \infty$ , can be modified in a routine way to show that  $C^{\infty}(\mathbf{T})$  is dense in  $L^p(\mathbf{T})$ ,  $1 \leq p < \infty$ . Indeed, the density can be proved using  $C^{\infty}$  functions that are truncated to be zero in a small neighborhood of  $\pi$  (equivalent to  $-\pi$ ).

Proposition 1. If  $f \in C^1(\mathbf{T})$ , then

$$|\hat{f}(n)| \le C/|n|$$

*Proof.* For  $n \neq 0$ ,

$$\int_{-\pi}^{\pi} f(x)e^{-inx} dx = \int_{-\pi}^{\pi} f(x)\frac{d}{dx} \left(\frac{e^{-inx}}{-in}\right) dx = -\int_{-\pi}^{\pi} f'(x)\frac{e^{-inx}}{-in} dx$$

Hence,

$$|\hat{f}(n)| \le \frac{1}{2\pi |n|} \int_{-\pi}^{\pi} |f'(x)| \, dx = ||f'||_1/|n|$$

**Exercise.** Show that if  $f \in C^k(\mathbf{T})$ , then

$$|\hat{f}(n)| < C/(1+|n|)^k$$

**Lemma 1.** (Riemann-Lebesque Lemma) Suppose that  $h \in L^1(\mathbf{T})$ . Then

$$\hat{h}(n) \to 0$$
 as  $|n| \to \infty$ 

*Proof.* Let  $\epsilon > 0$ , and choose  $g \in C^1(\mathbf{T})$  so that

$$||h-g||_{L^1(\mathbf{T})} \le \epsilon.$$

By Proposition 1  $\hat{g}(n) \to 0$  as  $|n| \to \infty$ . Therefore,

$$\limsup_{n\to\infty}|\hat{h}(n)|\leq \limsup_{n\to\infty}(|\hat{h}(n)-\hat{g}(n)|+|\hat{g}(n)|)=\limsup_{n\to\infty}|\hat{h}(n)-\hat{g}(n)|.$$

Next note that using (1),

$$|\hat{h}(n) - \hat{g}(n)| \le \|h - g\|_{L^1(\mathbf{T})} \le \epsilon.$$

Thus we have shown

$$\limsup_{n \to \infty} |\hat{h}(n)| \le \epsilon.$$

And taking the limit as  $\epsilon \to 0$  finishes the proof.

For any  $f \in L^1(\mathbf{T})$ , we define the partial sum of the Fourier series by

$$s_N(x) = \sum_{n=-N}^{N} \hat{f}(n)e^{inx}.$$

Substituting the formula for  $\hat{f}(n)$  into this formula, we find

$$s_N(x) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(y) \sum_{n=-N}^{N} e^{in(x-y)} dy,$$

which we also write

$$s_N(x) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(y) D_N(x - y) dy$$
 with  $D_N(t) = \sum_{n = -N}^{N} e^{int}$ .

The formula for  $s_N$  can be written in more compact form using an important operation \* known as convolution.

$$(2) s_N(x) = f * D_N(x)$$

Convolution. In general, for f and g in  $L^1(\mathbf{T})$ , we define the operation of convolution by

$$f * g(x) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(y)g(x-y) \, dy = \frac{1}{2\pi} \int_{a}^{a+2\pi} f(y)g(x-y) \, dy$$

For such f and g Fubini's theorem implies that f \* g defines an integrable function. In particular, f \* g(x) is defined and finite for almost every x (and periodic of period  $2\pi$ ). It's easy to see that convolution satisfies the distributive law, f \* (g+h) = f \* g + f \* h. One can also confirm, using a change of variable, that the operation is commutative. In other words,

$$f * g(x) = g * f(x) = \frac{1}{2\pi} \int_{-\pi}^{\pi} g(y)f(x-y) dy$$

There will be more about convolution later.

**Theorem 1.** (Dini Test) If  $f \in L^1(\mathbf{T})$ , and for some fixed x

$$\int_{-\pi}^{\pi} \frac{|f(x+y) - f(x)|}{|y|} dy < \infty,$$

then  $s_N(x) \to f(x)$  as  $N \to \infty$ .

*Proof.* (Note that although f is merely an  $L^1$  function, the hypothesis specifies the value of f(x) uniquely.) To prove the theorem observe first that

$$\int_{-\pi}^{\pi} D_N(y) \, dy = \int_{-\pi}^{\pi} \left( \sum_{n=-N}^{N} e^{iny} \right) \, dy = \int_{-\pi}^{\pi} \, dy = 2\pi$$

Therefore,

$$s_N(x) - f(x) = D_N * f(x) - f(x) = \frac{1}{2\pi} \int_{-\pi}^{\pi} D_N(y) f(x - y) \, dy - \frac{1}{2\pi} \int_{-\pi}^{\pi} D_N(y) f(x) \, dy$$
$$= \frac{1}{2\pi} \int_{-\pi}^{\pi} (f(x - y) - f(x)) D_N(y) \, dy$$

Furthermore,

$$D_N(y) = \sum_{n=-N}^{N} e^{iny} = \frac{e^{i(N+1)y} - e^{-iNy}}{e^{iy} - 1}$$

Thus

$$s_N(x) - f(x) = \hat{h}_x(N+1) - \hat{h}_x(-N)$$

with

$$h_x(y) = \frac{f(x-y) - f(x)}{e^{iy} - 1}.$$

Since  $|e^{iy}-1| \ge 2|y|/\pi$  for all  $|y| \le \pi$ , the hypothesis implies

$$\int_{-\pi}^{\pi} |h_x(y)| \, dy \le \frac{\pi}{2} \int_{-\pi}^{\pi} \frac{|f(x-y) - f(x)|}{|y|} dy < \infty$$

Therefore, by the Riemann-Lebesgue lemma (Lemma 1)

$$\lim_{N \to \infty} \hat{h}_x(N+1) - \hat{h}_x(-N) = 0$$

and the theorem is proved.

Corollary 1. If  $f \in C^1(\mathbf{T})$ , then

a) 
$$s_N(x) \to f(x)$$
 as  $N \to \infty$  for all  $x \in \mathbf{T}$ .

b) 
$$||s_N - f||_p \to 0$$
 as  $N \to \infty$ ,  $1 \le p < \infty$ .

*Proof.* Let  $M = \max |f'|$ . Then  $|f(x-y) - f(x)| \le M|y|$  so that

$$|h_x(y)| \le \left| \frac{f(x-y) - f(x)}{e^{iy} - 1} \right| \le \pi M/2$$

In particular, by the Dini test (Theorem 1),  $s_N(x) \to f(x)$ . Furthermore, by (1), we have

$$|s_N(x)| \le |\hat{h}_x(N+1)| + |\hat{h}_x(-N)| \le 2||h_x||_1 \le M\pi$$

so that  $|s_N(x) - f(x)|^p \le (M\pi + |f(x)|)^p$  is a majorant. By the dominated convergence theorem,

$$\lim_{N \to \infty} \int_{-\pi}^{\pi} |s_N(x) - f(x)|^p \, dx = 0$$

**Exercise.** For each  $\alpha$ ,  $0 < \alpha < 1$ , define  $C^{\alpha}(\mathbf{T})$  as the collection of  $2\pi$  periodic functions on  $\mathbf{R}$  satisfying

$$|f(x) - f(y)| \le C|x - y|^{\alpha}$$
, for all  $x, y \in \mathbf{R}$ 

Show that the conclusion of Corollary 1 holds for all  $f \in C^{\alpha}(\mathbf{T})$ .

Corollary 2. The functions  $e^{inx}$ ,  $n \in \mathbb{Z}$  form an orthonormal basis for  $L^2(\mathbb{T})$ . In particular, for all  $f \in L^2(\mathbb{T})$ ,

$$\lim_{N \to \infty} ||s_N - f||_2 = 0, \quad and \quad ||f||_2^2 = \sum_{n \in \mathbf{Z}} |\hat{f}(n)|^2.$$

*Proof.* Corollary 1 shows that the closure of V in the  $L^2(\mathbf{T})$  distance includes all functions in  $C^1(\mathbf{T})$ . Our density theorem says, in particular, that  $C^1(\mathbf{T})$  is dense in  $L^2(\mathbf{T})$ . Thus V is dense in  $L^2(\mathbf{T})$ , and this is condition (a) of our theorem characterizing orthonormal bases.

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.103 Fall 2013

## FOURIER SERIES 2

Recall that if  $f \in L^1(\mathbb{T})$ , and we define the partial sum

$$s_N(x) = \sum_{n=-N}^{N} \hat{f}(n)e^{inx}$$

then

$$s_N(x) = f * D_N(x) = \frac{1}{2\pi} \int_{\mathbb{T}} f(y) D_N(x - y) \, dy$$

where the Dirichlet kernel  $D_N(x)$  is defined by

$$D_N(x) = \sum_{n=-N}^{N} e^{inx}$$

Recall that if you sum the geometric series, you find the following closed formula.

(1) 
$$D_N(x) = \frac{e^{i(N+1)x} - e^{-iNx}}{e^{ix} - 1}$$

Multiplying numerator and denominator by  $e^{-ix/2}$ , we obtain a second closed form formula for  $D_N$ , namely

(2) 
$$D_N(x) = \frac{e^{i(2N+1)x/2} - e^{-i(2N+1)x/2}}{e^{ix/2} - e^{-ix/2}} = \frac{\sin[(2N+1)x/2]}{\sin(x/2)}$$

Taking the limit of the very last expression as  $x \to 0$ , we find  $D_N(0) = 2N + 1$  — a good double check, consistent with series for  $D_N$  with 2N + 1 terms, all equal to 1 at x = 0.

It took nearly a century from the time Fourier invented the series in the early 1800s to the proof of a general theorem about convergence. People got stuck because  $s_N$  and  $D_N$  are hard to work with.

The problem was (and is) that there are "bad" functions  $f \in C(\mathbb{T})$  such that  $s_N$  diverges at some points. There are even uglier functions  $f \in L^1(\mathbb{T})$  for which  $s_N(x)$  diverges for every x. Today we won't discuss these pathologies. We will focus instead on the positive side.

The breakthrough took place in 1904, when L. Fejér showed that trigometric polynomials approximate all continuous periodic functions uniformly. The idea is to give up, temporarily, on trying to approximate functions using  $s_N(x)$  and instead look at the Cesáro means

$$\sigma_N(x) = [s_0(x) + \dots + s_{N-1}(x)]/N$$

This new sequence converges more readily, smoothing out some of the oscillations in the sequence  $s_N(x)$ .

**Theorem 1.** (Fejér) Let f be continuous on  $\mathbb{R}$  and periodic of period  $2\pi$ . Then

$$\max_{x} |\sigma_N(x) - f(x)| \to 0 \quad as \ N \to \infty$$

where

$$\sigma_N(x) = (s_0(x) + \dots + s_{N-1}(x))/N$$

An immediate corollary is the density of the finite linear span of the functions  $e^{inx}$  in continuous periodic functions.

Corollary 1. Trigonometric polyonomials are dense in continuous, periodic of  $2\pi$  functions in the uniform norm.

To prove Fejér's theorem, we first compute

$$\sigma_N = \frac{1}{N}[s_0 + \dots + s_{N-1}] = f * \frac{1}{N} \sum_{0}^{N-1} D_N = f * F_N$$

where

$$F_N(x) = \frac{1}{N}(D_0 + D_1 + \dots + D_{N-1})$$

 $F_N$  is known as Fejér's kernel. We claim that

(3) 
$$F_N(x) = \frac{\sin^2(Nx/2)}{N\sin^2(x/2)}$$

To prove this, we use the representation (1).

$$(e^{ix} - 1)^{2} N F_{N}(x) = (e^{ix} - 1)^{2} \sum_{0}^{N-1} D_{n}(x)$$

$$= (e^{ix} - 1) \left[ \sum_{n=0}^{N-1} e^{i(n+1)x} - \sum_{n=0}^{N-1} e^{-inx} \right]$$

$$= e^{i(N+1)x} - e^{ix} - e^{ix} + e^{-i(N-1)x}$$

$$= e^{ix} [e^{iNx} - 2 + e^{-iNx}] = e^{ix} (e^{iNx/2} - e^{-iNx/2})^{2}$$

Therefore

$$F_N(x) = \frac{e^{ix}(e^{iNx/2} - e^{-iNx/2})^2}{N(e^{ix} - 1)^2} = \frac{(e^{iNx/2} - e^{-iNx/2})^2}{N(e^{ix/2} - e^{-ix/2})^2} = \frac{2i\sin^2(Nx/2)}{2iN\sin^2(x/2)}$$

**Lemma 1.** Approximate Identity Lemma. Let  $f \in C(\mathbb{R}/2\pi\mathbb{Z})$ , that is, f is a continuous function on  $\mathbb{R}$  such that  $f(x+2\pi) = f(x)$ . Let  $K_N(x)$  satisfy

i) 
$$\frac{1}{2\pi} \int_{-\pi}^{\pi} K_N(x) dx = 1$$

$$ii) \sup_{N} \int_{-\pi}^{\pi} |K_N(x)| dx \le M$$

iii) For any 
$$\delta > 0$$
,  $\int_{\delta \le |x| \le \pi} |K_N(x)| dx \to 0$  as  $N \to \infty$ .

Then

$$\max_{x} |f(x) - f * K_N(x)| \to 0 \quad as \ N \to \infty$$

Proof. By property (i),

$$2\pi [f * K_N(x) - f(x)] = \int_{-\pi}^{\pi} K_N(y) (f(x - y) - f(x)) dy$$
$$= \int_{\delta \le |y| \le \pi} K_N(y) (f(x - y) - f(x)) dy$$
$$+ \int_{|y| < \delta} K_N(y) (f(x - y) - f(x)) dy$$

For any  $\epsilon > 0$  choose  $\delta > 0$  so that  $|f(x - y) - f(x)| \le \epsilon$  for all  $|y| \le \delta$ . Note that there is such a  $\delta > 0$  that works for all x simultaneously because a continuous function on a compact set is uniformly continuous.<sup>1</sup> Next, by property (iii),

$$\left| \int_{\delta \le |y| \le \pi} K_N(y) (f(x-y) - f(x)) dy \right| \le 2 \max |f| \int_{\delta \le |y| \le \pi} |K_N(y)| dy \to 0$$

as  $N \to \infty$ . (The right side is independent of x, so the left side tends to zero uniformly in x.) Finally, using property (ii)

$$\left| \int_{|y| < \delta} K_N(y) (f(x - y) - f(x)) dy \right| \le \int_{|y| < \delta} |K_N(y)| \epsilon dy \le M \epsilon$$

It follows that

$$\limsup_{N \to \infty} \max_{x} |f * K_N(x) - f(x)| \le M\epsilon/2\pi$$

<sup>&</sup>lt;sup>1</sup>We need this uniform continuity on a larger compact interval than  $-\pi \le x - y \le \pi$ . It is this step that uses the property  $f(-\pi) = f(\pi)$ , or, equivalently, that f can be extended to a continuous periodic function on  $\mathbb{R}$ .

Since  $\epsilon > 0$  is arbitrary, this concludes the proof of the lemma.

Fejér's theorem follows once we confirm that  $F_N$  satisfies the hypotheses of the lemma. Indeed,

$$\frac{1}{2\pi} \int_{-\pi}^{\pi} D_N(x) \, dx = 1$$

and

$$\frac{1}{2\pi} \int_{-\pi}^{\pi} F_N(x) \, dx = \frac{1}{N} \sum_{0}^{N-1} \frac{1}{2\pi} \int_{-\pi}^{\pi} D_N(x) \, dx = 1,$$

which confirms (i). Formula (3) shows that  $F_N \geq 0$ , so

$$\int_{-\pi}^{\pi} |F_N(x)| \, dx = \int_{-\pi}^{\pi} F_N(x) \, dx = 2\pi < \infty$$

To prove (iii), fix  $\delta > 0$ . For  $\delta \leq |x| \leq \pi$ ,

$$|F_N(x)| \le \frac{1}{N\sin^2(x/2)} \le \frac{1}{N\sin^2(\delta/2)} \le C/N$$

for a constant C depending on  $\delta$ . Thus the integral in (iii) tends to zero.

Final Remark. Later on, we be able to recognize the way in which  $F_N$  is better than  $D_N$  by looking at their Fourier series,

$$D_N(x) = \sum_{n=-N}^{N} e^{inx}, \quad F_N(x) = \sum_{n=-N}^{N} \left(1 - \frac{|n|}{N}\right) e^{inx}$$

Let

$$h_1(s) = 1_{[-1,1]}, \quad h_2(s) = (1 - |s|)^+$$

The function  $h_1$  is discontinuous, but  $h_2$  has a bounded first derivative. The Dirichlet and Fejér kernels are

$$D_N(x) = \sum_{n=-\infty}^{\infty} h_1(n/N)e^{inx}, \quad F_N(x) = \sum_{n=-\infty}^{\infty} h_2(n/N)e^{inx},$$

and the fact that  $h_2$  is smoother than  $h_1$  accounts for the improved properties (ii) and (iii) of  $F_N$  that fail for  $D_N$ .

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

#### 18.103 Fall 2013

#### Fourier Series, Continued (part 3)

**Proposition 1.** If f and g belong to  $L^1(\mathbf{T})$ , then  $f * g \in L^1(\mathbf{T})$  and

$$||f * g||_p \le ||f||_p ||g||_1.$$

*Proof.* Fubini's theorem implies

$$\int_{\mathbf{T}} \left( \int_{\mathbf{T}} |f(x-y)g(y)| dy \right) dx = \int_{\mathbf{T}} \left( \int_{\mathbf{T}} |f(x-y)|g(y)| dx \right) dy$$
$$= \int_{T} 2\pi ||f||_{1} |g(y)| dy = (2\pi)^{2} ||f||_{1} ||g||_{1} < \infty$$

It follows that

$$\int_{\mathbb{T}} |f(x-y)g(y)| dy < \infty \quad \text{a. e.}$$

For these values of x, f(x-y)g(y) is integrable, and we may define

$$f * g(x) = \frac{1}{2\pi} \int_{\mathbf{T}} f(x - y)g(y)dy.$$

Moreover,

$$||f * g||_1 = \frac{1}{2\pi} \int_{\mathbf{T}} |f * g(x)| dx = \frac{1}{2\pi} \int_{T} \left| \frac{1}{2\pi} \int_{\mathbf{T}} f(x - y) g(y) dy \right| dx$$

$$\leq \frac{1}{(2\pi)^2} \int_{T} \int_{\mathbf{T}} |f(x - y) g(y)| dy dx = ||f||_1 ||g||_1.$$

**Exercise.** Show that for  $f \in L^{\infty}(\mathbf{T})$  and  $g \in L^{1}(\mathbf{T})$ , f \* g(x) is defined for every x and

$$||f * g||_{\infty} \le ||f||_{\infty} ||g||_{1}.$$

Deduce, using a density argument, that f \* g is continuous. <sup>1</sup>

$$||f||_{\infty} := \operatorname{esssup}_{x \in X} |f(x)|$$

<sup>&</sup>lt;sup>1</sup>Recall that the space  $L^{\infty}(X,\mu)$  is defined as the set of measurable functions for which the norm

Next, we introduce an operator notation for the Cesáro means of the Fourier series:

$$\sigma_N f(x) = \sum_{n=-N}^{N} \left( 1 - \frac{|n|}{N} \right) \hat{f}(n) e^{inx} = f * F_N(x),$$

with  $F_N$  the Fejér kernel. Notice that this is a linear operation,  $\sigma_N(af + bg) = a\sigma_N f + b\sigma_N g$  for complex numbers a and b.

Theorem 1. Let  $f \in L^1(\mathbf{T})$ . Then

$$\lim_{N\to\infty} \|f - \sigma_N f\|_1 = 0$$

In particular, trigonometric polynomials are dense in  $L^1(\mathbf{T})$ .

*Proof.* Take  $\epsilon > 0$  and choose  $g \in C(\mathbf{T})$  such that

$$||f - g||_1 \le \epsilon$$

Then

$$\|\sigma_N f - f\|_1 \le \|\sigma_N f - \sigma_N g\|_1 + \|\sigma_N g - g\|_1 + \|g - f\|_1,\tag{1}$$

and Proposition 1 implies

$$\|\sigma_N f - \sigma_N g\|_1 = \|\sigma_N (f - g)\|_1 = \|(f - g) * F_N\|_1 \le \|f - g\|_1 \|F_N\|_1 = \|f - g\|_1 \le \epsilon$$

Therefore, implies

$$\|\sigma_N f - f\|_1 \le 2\epsilon + \|\sigma_N g - g\|_1$$

The main theorem from the preceding lecture was

$$\max_{x} |g(x) - \sigma_N g(x)| \to 0 \quad \text{as} \quad N \to \infty$$

This is the same as saying  $||g - \sigma_N g||_{\infty} \to 0$ . For any function h,

$$||h||_1 = \frac{1}{2\pi} \int_{-\pi}^{\pi} |h(x)| dx \le \frac{1}{2\pi} \int_{-\pi}^{\pi} \operatorname{esssup}_x |h| dx = ||h||_{\infty}$$

is finite. The essential supremum is defined by

$$\operatorname{esssup}_{x \in X} f(x) = \inf \{ \sup_{E} f : \mu(X \setminus E) = 0 \}$$

As with the other  $L^p$  spaces, we consider two functions in  $L^{\infty}(X,\mu)$  to be equivalent if they are equal except on a set of measure zero.

It follows that as  $N \to \infty$ ,

$$||g - \sigma_N g||_1 \le ||g - \sigma_N g||_{\infty} \to 0$$

Thus,

$$\lim_{N \to \infty} \|\sigma_N f - f\|_1 \le 2\epsilon$$

and since  $\epsilon > 0$  was arbitrary, we have proved the theorem.

Corollary 1. (Uniqueness of Fourier Series) If  $f \in L^1(\mathbf{T})$  and  $\hat{f}(n) = 0$  for all n, then f(x) = 0 for almost every x.

*Proof.* By the theorem,  $\|\sigma_N f - f\|_1 \to 0$  as  $N \to \infty$ . But the fact that  $\hat{f}(n) = 0$  for all n implies  $\sigma_N f \equiv 0$  for all N, so we have  $\|f\|_1 = 0$ .

**Further Results.** We mention without proof several negative and positive results about convergence that we won't have time to prove in this class. To state these, we will also use operator notation for the partial sums  $s_N(x)$  as follows.

$$S_N f(x) := \sum_{n=-N}^{N} \hat{f}(n) e^{inx} = f * D_N(x)$$

where  $D_N$  is the Dirichlet kernel.

- 1. There exists  $f \in C(\mathbf{T})$  such that  $S_N f(0) \to \infty$  as  $N \to \infty$ . (Pointwise convergence of  $S_N f$  can fail for continuous functions.)
- 2. There exists  $f \in L^1(\mathbf{T})$  such that  $||S_N f||_1 \to \infty$  as  $N \to \infty$ . (Norm convergence of  $S_N f$  can fail for  $L^1$  functions.)
  - 3. On the other hand, if  $f \in L^p(\mathbf{T})$  for some p, 1 , then

$$||S_N f - f||_p \to 0, \qquad N \to \infty.$$

(Norm convergence of  $S_N f$  succeeds for  $L^p$  functions,  $1 . The main step in the proof is a theorem of Marcel Riesz that <math>||S_N f||_p \le C_p ||f||_p$ , independent of N. In this class, we will only prove the weaker statement that this works for  $\sigma_N f$ . This depends on the inequality  $||\sigma_N f||_p \le ||f||_p$  which is relatively easy.)

4. If  $f \in L^p(\mathbf{T})$  for some  $p, p \geq 1$ , then

$$\lim_{N \to \infty} \sigma_N f(x) = f(x), \quad \text{a. e. } x.$$

(Pointwise convergence of  $\sigma_N f$  succeeds for  $L^p$  functions, for all  $p \geq 1$ . This follows from what are known as maximal function estimates. This type of estimate also plays the central in what is known as the Lebesgue differentiation theorem, which says that the fundamental theorem of calculus works for integrals of  $L^1$  functions.)

5. If  $f \in L^p(\mathbf{T})$  for some p, 1 , then

$$\lim_{N \to \infty} S_N f(x) = f(x), \quad \text{a. e. } x.$$

This last result is due to Lennart Carleson (1965) for  $p \ge 2$  and to Richard Hunt (1967) for 1 , and the proof is difficult.

Rather than prove these more detailed results about ordinary and Cesáro convergence, we prefer to talk about applications. The text by Stein and Shakarchi features two lovely, illustrative applications of Fourier analysis, which we now present. They are a proof of the isoperimetric inequality and a proof of Weyl's equidistribution theorem.

# **Applications**

The fundamental idea motivating Fourier is that differentiation can be understood using the Fourier basis. The linear operator d/dx can be diagonalized in the basis  $e^{inx}$ . Formally

$$\frac{d}{dx}\sum_{n}a_{n}e^{inx} = \sum_{n}ina_{n}e^{inx}$$

In analogy with finite dimensions, we say that that d/dx is represented by the matrix with diagonal entries  $0, \pm i, \pm 2i, \pm 3i,$  etc.<sup>2</sup>

If one assumes that  $\sum |na_n| < \infty$ , then one can justify this formula pointwise for each x. Here is a Fourier coefficient version of the differentiation formula above.

**Proposition 2.** If  $f \in C^1(\mathbf{R}/2\pi \mathbf{Z})$ , then (proved in class by integration by parts)

$$\widehat{f'}(n) = in\widehat{f}(n)$$

<sup>&</sup>lt;sup>2</sup>Mathematicians have found that this important formula gives a consistent way to **define** d/dx even when differentiation in the ordinary sense does not work and the sums don't converge in any ordinary sense. As we will explain later in the class, this formula for d/dx is true in the sense of distributions.

The formula  $\hat{f}'(n) = in\hat{f}(n)$  is of central importance, just like its counterpart in summation form above

It follows from Proposition 2, that if  $f \in C^1(\mathbf{R}/2\pi \mathbf{Z})$ , then continuous function  $f' \in C(\mathbf{T}) \subset L^2(\mathbf{T})$ . Hence by our result showing that  $e^{inx}$  is an orthormal basis of  $L^2(\mathbf{T})$ , f' is represented by its series, and the Parseval formula says

$$\frac{1}{2\pi} \int_{-\pi}^{\pi} |f'(x)|^2 dx = \sum_{n \in \mathbf{Z}} |in\hat{f}(n)|^2.$$

(In particular, the series on the right side is finite.)

# Application 1. The Isoperimetric Inequality.

Let D be a region of the plane enclosed by a simple  $C^1$  curve  $\Gamma:(x(t),y(t))$ . The isoperimetric inequality

$$A(D) \le \ell(\Gamma)^2 / 4\pi$$

where A(D) denotes the area of D and  $\ell(\Gamma)$  denotes the length of  $\Gamma$ . Moreover, the case of equality occurs if and only if  $\Gamma$  is a circle.

The idea is to convert this inequality into one concerning Fourier coefficients of x(t) and y(t).

We begin with a standard 18.02 formula for area,

$$A(D) = \frac{1}{2} \int_{\Gamma} x dy - y dx,$$

which follows from Green's theorem,

$$\int_{\Gamma} M dx + N dy = \int \int_{D} \left[ (\partial N / \partial x) - (\partial M / \partial y) \right] dx dy$$

with M = -y/2, N = x/2. Thus

$$A(D) = \frac{1}{2} \int_{a}^{b} [x(t)y'(t) - x'(t)y(t)]dt$$

<sup>&</sup>lt;sup>3</sup> "Simple" means that the curve does not cross itself.

 $<sup>^4</sup>$ We follow Stein-Shakarchi, although we treat the  $C^1$  case, a bit more general a hypothesis than in that text.

Moreover, the length of  $\Gamma$  is given by

$$\ell(\Gamma) = \int_a^b \sqrt{x'(t)^2 + y'(t)^2} dt.$$

Step 1. By rescaling, we may assume  $\ell(\Gamma) = 2\pi$ . Then our goal is to prove that

$$A(D) \le (2\pi)^2/4\pi = \pi$$

We can also change variables so that the parametrization has unit speed:

$$x'(t)^2 + y'(t)^2 = 1$$

which implies  $b-a=\ell(\Gamma)=2\pi$ . Thus, we may suppose  $a=-\pi$ ,  $b=\pi$  and that x(t) and y(t) are in  $C^1(\mathbf{R}/2\pi\mathbf{Z})$ .

Step 2. Next we relax the constraint from the unit speed condition to the constraint.

$$\frac{1}{2\pi} \int_{-\pi}^{\pi} [x'(t)^2 + y'(t)^2] dt = 1$$
 (2)

In the case  $x'(t)^2 + y'(t)^2 = 1$ , this constraint is obviously true, so if we succeed in proving  $A(D) \le \pi$  under the constraint (2), then we have proved the isoperimetric inequality.

What is less obvious, is why we did this and why we can get away with it. We will answer these questions before proceeding further. The reason why we did this is that the constraint on the integral of  $\sqrt{x'(t)^2 + y'(t)^2}$  can't be written in any useful way in terms of Fourier coefficients. Neither can the constraint  $x'(t)^2 + y'(t)^2 = 1$ . On the other hand, the constraint (2) can be rewritten using Parseval's formula (see Step 3).

There remains the question why we can get away with this relaxation of the constraint. The answer is that the Cauchy-Schwarz inequality implies

$$\frac{1}{2\pi} \int_{-\pi}^{\pi} \sqrt{x'(t)^2 + y'(t)^2} dt \le \left(\frac{1}{2\pi} \int_{-\pi}^{\pi} (x'(t)^2 + y'(t)^2) dt\right)^{1/2} \left(\frac{1}{2\pi} \int_{-\pi}^{\pi} 1^2 dt\right)^{1/2} = 1$$

In other words, all curves (x(t), y(t)) satisfying (2) also have length less than or equal to  $2\pi$ .

It looks peculiar the first time you see it, but replacing  $L^1$  norm of the speed |(x'(t), y'(t))| by the  $L^2$  norm is a standard device in the theory of geodesics (curves that minimize the distance between points in Riemannian manifolds). The curves minimizing the quadratic integral have constant speed, which has the further advantage of eliminating the non-uniqueness in the parametric representation of a shortest length curve.

Step 3. Reformulation in terms of Fourier series.

The Fourier series of x and y are given by

$$x(t) = \sum_{n=-\infty}^{\infty} a_n e^{int}; \quad y(t) = \sum_{n=-\infty}^{\infty} b_n e^{int}$$

Since x and y are real-valued,  $a_{-n} = \overline{a_n}$  and  $b_{-n} = \overline{b_n}$ . Moreover, Proposition 2 says that

$$x'(t) = \sum_{n=-\infty}^{\infty} ina_n e^{int}; \quad y'(t) = \sum_{n=-\infty}^{\infty} inb_n e^{int}$$

with convergence in  $L^2$  norm. Parseval's formula implies that (2) can be written

$$1 = ||x'||^2 + ||y'||^2 = \sum_{n = -\infty}^{\infty} |ina_n|^2 + |inb_n|^2 = \sum_{n = -\infty}^{\infty} n^2 [|a_n|^2 + |b_n|^2]$$

Next, the scalar product formula (polarization of the Parseval formula) implies

$$\langle f, g \rangle = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(t) \overline{g(t)} dt = \sum_{n=-\infty}^{\infty} \hat{f}(n) \overline{\hat{g}(n)}$$

Thus,

$$A(D) = \frac{1}{2} \int_{-\pi}^{\pi} [x(t)y'(t) - x'(t)y(t)]dt = \pi[\langle x, y' \rangle - \langle y, x' \rangle] = \pi \sum_{n=-\infty}^{\infty} [a_n \overline{inb_n} - b_n \overline{ina_n}]$$

Step 4. Recall that we want to prove that  $A(D) \leq \pi$ . Note that for real numbers a and b,  $2ab \leq a^2 + b^2$ . Thus

$$|a_n\overline{b_n} - b_n\overline{a_n}| \le 2|a_n||b_n| \le |a_n|^2 + |b_n|^2$$

and hence

$$A(D) \le \pi \sum_{n = -\infty}^{\infty} |a_n \overline{inb_n} - b_n \overline{ina_n}| \le \pi \sum_{n = -\infty}^{\infty} |n| [|a_n|^2 + |b_n|^2] \le \pi \sum_{n = -\infty}^{\infty} n^2 [|a_n|^2 + |b_n|^2] = \pi$$

This ends the proof of the isoperimetric inequality.

Step 5. It remains to prove that in the case of equality in the isoperimetric inequality,  $\Gamma$  is a circle. To prove this note that if equality holds, each of the inequalities in the proof is an equation. The last one says

$$\sum_{n=-\infty}^{\infty} |n|[|a_n|^2 + |b_n|^2] = \sum_{n=-\infty}^{\infty} n^2[|a_n|^2 + |b_n|^2]$$

Since  $|n| < n^2$  for all  $|n| \ge 2$ , we have  $|a_n|^2 + |b_n|^2 = 0$  for all  $|n| \ge 2$ . Thus

$$x(t) = a_0 + a_1 e^{it} + \overline{a}_1 e^{-it}; \quad y(t) = b_0 + b_1 e^{it} + \overline{b}_1 e^{-it};$$

Moreover,

$$1 = \sum_{n=-1}^{1} n^{2} [|a_{n}|^{2} + |b_{n}|^{2}] = 2|a_{1}|^{2} + 2|b_{1}|^{2}$$

Furthermore,  $a \ge 0$ ,  $b \ge 0$ ,

$$2ab = a^2 + b^2 \implies (a-b)^2 = 0 \implies a = b$$

From this and the equality  $2|a_1b_1| = |a_1|^2 + |b_1|^2$ , we conclude that  $|a_1| = |b_1|$ . Thus,

$$|a_1|^2 = |b_1|^2 = 1/4$$

Therefore we may write

$$a_1 = e^{i\alpha}/2; \quad b_1 = e^{i\beta}/2$$

and

$$x(t) = a_0 + \cos(\alpha + t); \quad y(t) = b_0 + \cos(\beta + t)$$

Finally, substitute into the equality

$$|a_1\overline{b}_1 - \overline{a}_1b_1| = 2|a_1||b_1| = 1/2$$

to find

$$(1/4)|e^{i(\alpha-\beta)} - e^{i(\beta-\alpha)}| = (1/2)|\sin(\alpha-\beta)| = 1/2$$

Finally, this yields  $\alpha - \beta = \pm \pi/2 \mod 2\pi$ , so that

$$\cos(\beta + t) = \pm \sin(\alpha + t)$$

This finishes the proof that  $\Gamma$  is a unit circle (parametrized counterclockwise or clockwise) centered at  $(a_0, b_0)$ .

### Application 2. Weyl Equidistribution Theorem

For  $x \in \mathbf{R}$ , let  $\{x\}$  denote the fractional part, that is,  $x - \{x\}$  is the largest integer that is less than or equal to x.

**Theorem 2.** (Weyl equidistribution theorem) If  $\alpha$  is irrational, and  $0 \le a < b \le 1$ , then

$$\lim_{N \to \infty} \frac{\#\{m: 0 \le m \le N-1, \quad a \le \{m\alpha\} \le b\}}{N} = b-a$$

*Proof.* The conclusion can be rewritten

$$\lim_{N \to \infty} \frac{1}{N} \sum_{m=0}^{N-1} f(\{m\alpha\}) = \int_0^1 f(x) dx \tag{3}$$

with  $f = 1_{[a,b]}$ . Extend f to be periodic of period 1. For any  $\epsilon > 0$  there are functions  $f_1$  and  $f_2$  continuous and periodic of period 1 such that  $f_1 \leq f \leq f_2$  and

$$\int_{0}^{1} f_{1}(x) \ge (b-a) - \epsilon; \quad \int_{0}^{1} f_{2}(x) dx \le (b-a) - \epsilon$$

Thus if we can prove (3) for  $f_1$  and  $f_2$  we have

$$\limsup_{N \to \infty} \frac{1}{N} \sum_{m=0}^{N-1} 1_{[a,b]}(\{m\alpha\}) \le \lim_{N \to \infty} \frac{1}{N} \sum_{m=0}^{N-1} f_2(\{m\alpha\}) = \int_0^1 f_2(x) dx \le (b-1) + \epsilon$$

and similarly the liminf is greater than  $(b-a)-\epsilon$ . Since  $\epsilon>0$  is arbitrary, Theorem 2 follows.

To prove (3) for continuous functions with period 1, recall that they can be uniformly approximated by trigonometric polynomials with period 1. In other words, for  $\epsilon > 0$ , and any continuous periodic f, we can find a trigonometric polynomial g such that

$$\left| \frac{1}{N} \sum_{m=0}^{N-1} f(\{m\alpha\}) - \frac{1}{N} \sum_{m=0}^{N-1} g(\{m\alpha\}) \right| \le \max|f - g| \le \epsilon.$$

So it suffices to confirm (3) for trigonometric polynomials, and hence for single exponentials,  $f = \varphi_n(x)$ , with

$$\varphi_n(x) = e^{2\pi i n x}, \quad n = 0, \pm 1, \pm 2, \dots$$

The case n = 0 is immediate since

$$\frac{1}{N} \sum_{m=0}^{N-1} \varphi_0(\{m\alpha\}) = \frac{1}{N} \sum_{m=0}^{N-1} 1 = 1 = \int_0^1 \varphi_0(x) \, dx.$$

For  $n \in \mathbf{Z}$ ,  $n \neq 0$ , we have

$$\varphi_n(\{m\alpha\}) = e^{2\pi i \{m\alpha\}} = e^{2\pi i m\alpha} = \varphi_n(m\alpha),$$

and

$$\frac{1}{N} \sum_{m=0}^{N-1} \varphi_n(\{m\alpha\}) = \frac{1}{N} \sum_{m=0}^{N-1} e^{2\pi i n m \alpha} = \frac{e^{2\pi i n N \alpha} - 1}{N(e^{2\pi i n \alpha} - 1)}$$

Here, we used the fact that  $\alpha$  is irrational in order to know that  $e^{2\pi i n \alpha} - 1 \neq 0$ . Letting N tend to infinity we see that

$$\lim_{N \to \infty} \frac{1}{N} \sum_{m=0}^{N-1} \varphi_n(\{m\alpha\}) = 0 = \int_0^1 e^{2\pi i nx} dx = \int_0^1 \varphi_n(x) dx$$

Exercise. For  $x \in \mathbb{R}^n$ , denote the fractional parts of its components by

$$\{x\} = (\{x_1\}, \dots, \{x_n\}),\$$

(Put another way,  $\{\cdot\}: \mathbf{R}^n \to \mathbf{R}^n/\mathbf{Z}^n$  is the quotient mapping.) Let R be a rectangle (multi-interval) in  $[0,1]^n$ . Let

$$\alpha = (\alpha_1, \ldots, \alpha_n)$$

be such that 1,  $\alpha_1, \ldots, \alpha_n$  are linearly independent over  $\mathbf{Q}$ , the rational numbers. Show that

$$\lim_{N \to \infty} \frac{\#\{m : 0 \le m \le N - 1, \{m\alpha\} \in R\}}{N} = \operatorname{vol}(R)$$

(Hint: Formulate and prove the appropriate density theorem for trigonometric polynomials on  $\mathbf{R}^n/\mathbf{Z}^n$ .)

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.103 Fall 2013

## 1 Fourier Integrals on $L^2(\mathbb{R})$ and $L^1(\mathbb{R})$ .

The first part of these notes cover §3.5 of AG, without proofs. When we get to things not covered in the book, we will start giving proofs.

The Fourier transform is defined for  $f \in L^1(\mathbb{R})$  by

$$\mathcal{F}(f) = \hat{f}(\xi) = \int_{-\infty}^{\infty} f(x)e^{-ix\xi} dx \tag{1}$$

The Fourier inversion formula on the Schwartz class  $\mathcal{S}(\mathbb{R})$ .

**Theorem 1** If  $f \in \mathcal{S}(\mathbb{R})$ , then  $\hat{f} \in \mathcal{S}(\mathbb{R})$  and

$$f(x) = \frac{1}{2\pi} \int_{-\infty}^{\infty} \hat{f}(\xi) e^{ix\xi} d\xi$$

Thus the inverse operator to the Fourier transform is given by

$$\check{g}(x) = \frac{1}{2\pi} \int_{-\infty}^{\infty} g(\xi) e^{ix\xi} d\xi = \frac{1}{2\pi} \hat{g}(-x)$$

A function  $f \in L^2(\mathbb{R})$  need not be in  $L^1(\mathbb{R})$  and the integral defining  $\hat{f}$  may be divergent. Nevertheless, one can define the Fourier transform  $\hat{f}$  as a limit in two ways. The first way uses the Plancherel theorem.

Corollary 1 If  $f \in \mathcal{S}(\mathbb{R})$ , then

$$2\pi \int_{\mathbb{R}} |f(x)|^2 dx = \int_{\mathbb{R}} |\hat{f}(\xi)|^2 d\xi$$

Corollary 1 leads to a definition of the Fourier transform for  $f \in L^2(\mathbb{R})$  by continuity in the  $L^2$  distance as follows.

Corollary 2 Let  $f \in L^2(\mathbb{R})$  and let  $f_j \in \mathcal{S}(\mathbb{R})$  be such that  $||f - f_j||_2 \to 0$  as  $j \to \infty$ . Then  $\hat{f}_j$  is a Cauchy sequence in  $L^2(\mathbb{R})$  and the limit (in the  $L^2$  metric) is independent of the choice of sequence approximating f. Thus there is a unique function denoted  $\hat{f} \in L^2(\mathbb{R})$  for which

$$\lim_{j \to \infty} \|\hat{f} - \hat{f}_j\|_2 = 0$$

Furthermore,

$$\|\hat{f}\|_2^2 = 2\pi \|f\|_2^2$$

Corollary 3 If  $f \in L^2(\mathbb{R})$ , and  $\hat{f} = 0$  almost everywhere, then f = 0.

Fourier inversion formula on the Schwartz class extends by continuity to Fourier inversion on  $L^2(\mathbb{R})$ .

Corollary 4 (Fourier inversion on  $L^2$ ) Let

$$\mathcal{G}(f)(x) = \frac{1}{2\pi}\hat{f}(-x)$$

then for all  $f \in L^2(\mathbb{R})$ ,

$$\mathcal{G} \circ \mathcal{F}(f) = \mathcal{F} \circ \mathcal{G}(f) = f$$

Thus, up to the factor  $2\pi$ , the Fourier transform is an isometry (distance preserving) from  $L^2(\mathbb{R})$  to itself.

We need to make sure that our two definitions of the Fourier transform for  $L^1$  and  $L^2$  are consistent. This is taken care of by the following proposition.

**Proposition 1** If  $f \in L^2(\mathbb{R}) \cap L^1(\mathbb{R})$ , then the definition by continuity in Corollary 2 for  $\hat{f}$  coincides with the definition (1) above.

(See PS9, Exercise AG §3.5/3, p. 153. The starting point of the proof of the proposition is that one can choose  $f_j \in \mathcal{S}$  so that  $||f - f_j||_1 + ||f - f_j||_2 \to 0$ ).

As a consequence of the proposition, we find a second way to define the Fourier transform on  $L^2$  using a more straightforward truncation Indeed, in the very next exercise (PS9, AG §3.5/4, p. 153) you were asked to show that if  $f \in L^2(\mathbb{R})$ , then

$$\hat{f}(\xi) = \lim_{N \to \infty} \int_{-N}^{N} f(x)e^{-ix\xi}dx,$$
 (limit in  $L^2$  sense)

To prove this, note that if  $f_N(x) = f(x)1_{[-N,N]}$ , then  $f_N \in L^2(\mathbb{R}) \cap L^1(\mathbb{R})$ , and by Exercise §3.5/3,  $\hat{f}_N(\xi)$  is the integral on the right. On the other hand, it follows from Corollary 2 applied to  $f - f_N$  that

$$\|\hat{f} - \hat{f}_N\|_2^2 = 2\pi \|f - f_N\|_2^2 = 2\pi \int_{|x| > N} |f(x)|^2 dx$$

which tends to zero by the dominated convergence theorem (with majorant  $|f(x)|^2$ ).

We now deduce a more explicit version of Fourier inversion on  $L^2$ , which can be stated as follows.

**Theorem 2** Suppose that  $f \in L^2(\mathbb{R})$ . Then  $\hat{f}(\xi)1_{[-N,N]}(\xi)$  is in  $L^2(\mathbb{R}) \cap L^1(\mathbb{R})$  and

$$s_N(x) = \frac{1}{2\pi} \int_{-N}^{N} \hat{f}(\xi) e^{ix\xi} d\xi$$

satisfies

$$\lim_{N \to \infty} \|f - s_N\|_{L^2} = 0$$

To begin the proof of Theorem 2, consider  $f \in L^2(\mathbb{R})$ . Then by Corollary 2,  $\hat{f} \in L^2(\mathbb{R})$  and hence, by the Cauchy-Schwarz inequality,  $\hat{f} 1_{[-N,N]} \in L^1(\mathbb{R}) \cap L^2(\mathbb{R})$ . We will apply a proposition analogous to Proposition 1 (with exactly the same proof).

**Proposition 2** If  $h \in L^1(\mathbb{R}) \cap L^2(\mathbb{R})$ , then the inverse Fourier transform obtained by continuity in the  $L^2$  norm coincides with the  $L^1$  definition:

$$\mathcal{G}(h)(x) = \frac{1}{2\pi} \int_{-\infty}^{\infty} h(\xi) e^{ix\xi} d\xi$$

Let  $h = \hat{f} 1_{[-N,N]}$ . Then  $h \in L^1(\mathbb{R}) \cap L^2(\mathbb{R})$  and Proposition 2 implies

$$s_N(x) = \mathcal{G}(h)(x)$$

Since  $h \in L^2(\mathbb{R})$ , we also have  $s_N \in L^2(\mathbb{R})$ , and we may take the Fourier transform and apply Theorem 4 to obtain

$$\hat{s}_N(\xi) = h(\xi) = \hat{f}(\xi) 1_{[-N,N]}(\xi)$$

Finally, applying the formula in Corollary 2

$$2\pi \|f - s_N\|_2^2 = \|\hat{f} - \hat{s}_N\|_2^2 = \int_{|\xi| > N} |\hat{f}(\xi)|^2 d\xi \to 0 \text{ as } N \to \infty$$

(The last step uses the dominated convergence theorem with majorant  $|\hat{f}(\xi)|^2$ .) This ends the proof of Theorem 2.

Our last task is to find a Fourier inversion formula on  $L^1(\mathbb{R})$ .

**Theorem 3** Let  $f \in L^1(\mathbb{R})$  and denote

$$\sigma_N(x) = \frac{1}{2\pi} \int_{-N}^{N} (1 - |\xi/N|)^+ \hat{f}(\xi) e^{ix\xi} d\xi$$

Then

$$\lim_{N\to\infty} \|f - \sigma_N\|_{L^1} = 0$$

Corollary 5 If  $f \in L^1(\mathbb{R})$ , and  $\hat{f} = 0$ , then f = 0.

The idea of the proof of Theorem 3 is parallel to the case of Fourier series. Note that Fubini's theorem implies that for f and g in  $L^1(\mathbb{R})$ ,

$$\widehat{(f * g)}(\xi) = \widehat{f}(\xi)\widehat{g}(\xi) \tag{2}$$

We will show that

$$\sigma_N(x) = f * F_N(x) \tag{3}$$

for a function  $F_N$ , known (as in the case of the circle group) as the Fejér kernel.

**Theorem 4** (Approximate identity) If  $K \in L^1(\mathbb{R})$ ,  $K_{\epsilon}(x) = (1/\epsilon)K_{\epsilon}(x)$ , and

$$\int_{-\infty}^{\infty} K(x) \, dx = 1$$

then  $||K_{\epsilon} * f - f||_1 \to 0$  for all  $f \in L^1(\mathbb{R})$ .

Consider  $K(x) = F_1(x)$ ,  $K_{\epsilon} = F_{1/\epsilon}$  with  $\epsilon = 1/N$ . It will suffice to show that  $K = F_1$  is integrable with integral 1. In fact, we will find that  $F_1(x) > 0$  and

$$\int_{\mathbb{R}} |F_1(x)| dx = \int_{\mathbb{R}} F_1(x) dx = \hat{F}_1(0) = 1 \tag{4}$$

Thus the approximate identity theorem implies that  $\|\sigma_N - f\|_1 \to 0$  as  $N \to \infty$  for all  $f \in L^1(\mathbb{R})$ .

We will find the formula for  $F_N$  using the identity

$$\hat{F}_N(\xi) = (1 - |\xi/N|)^+$$

This function has the shape of a triangle. It has a very simple relationship with change of scale, namely,  $\hat{F}_N(\xi) = \hat{F}_1(\xi/N)$  and by change of variables,  $F_N(x) = NF_1(Nx)$ . One can easily compute  $F_1$  and hence  $F_N$  using the inverse Fourier transform formula and integration by parts, but we prefer to derive its fomula by a more circuitous route that will enable us to see why  $F_N(x)$  is essentially the square of  $D_N(x)$ , the Dirichlet kernel.

Define

$$\hat{D}_N(\xi) = 1_{[-N,N]}(\xi)$$

Then Proposition 2 gives

$$D_N(x) = \frac{1}{2\pi} \int_{-N}^{N} e^{ix\xi} d\xi = \frac{e^{ix\xi}}{2\pi ix} \Big|_{-N}^{N} = \frac{\sin Nx}{\pi x}$$

 $D_N$  is known as the Dirichlet kernel (analogous to the one for Fourier series).

$$s_N(x) = f * D_N(x); \quad \hat{s}_N(\xi) = \hat{f}(\xi) 1_{[-N,N]}(\xi)$$

(Note that  $D_N(x)^2 \leq 1/|x|^2$  as  $|x| \to \infty$  so that  $D_N \in L^2(\mathbb{R})$ . Thus  $f * D_N(x)$  is a convergent integral for every x, provided  $f \in L^2(\mathbb{R})$ .) We also remark that  $D_N$  has the following scaling properties.

$$D_N(x) = ND_1(Nx); \quad \hat{D}_N(\xi) = \hat{D}_1(\xi/N)$$

As in the case of Fourier series, it does not work to approximate f by  $s_N(x)$  for  $f \in L^1(\mathbb{R})$ . By inspection, we see that  $|D_N(x)|$  has the size of 1/|x| as  $|x| \to \infty$  so that  $D_N \notin L^1(\mathbb{R})$ . Even figuring out exactly what  $f * D_N(x)$  means for  $f \in L^1(\mathbb{R})$  is delicate and beyond the scope of this course.

So instead of  $D_N$ , we work out the formula for the Fejér kernel  $F_N$ . Since  $\hat{D}_{1/2}(\xi) = 1_{[-1/2,1/2]}$ , we have the convolution formula

$$\hat{D}_{1/2} * \hat{D}_{1/2}(\xi) = (1 - |\xi|)^{+} = \hat{F}_{1}(\xi)$$

Because the inverse Fourier transform is  $1/2\pi$  times the Fourier transform (with a sign change) a formula equivalent to (2) says

$$\mathcal{G}(f * g) = 2\pi \mathcal{G}(f)\mathcal{G}(g)$$

Apply this with  $f = g = 1_{[-1/2,1/2]} = \hat{D}_{1/2}$ , then

$$F_1 = \mathcal{G}(f * g) = 2\pi \mathcal{G}(f)\mathcal{G}(g) = 2\pi D_{1/2}^2$$

In other words,

$$F_1(x) = 2\pi \frac{\sin^2(x/2)}{(\pi x)^2} = \frac{2\sin^2(x/2)}{\pi x^2}$$

Next we rescale. Since  $\hat{F}_N(\xi) = \hat{F}_1(\xi/N)$ , we have

$$F_N(x) = NF_1(Nx) = \frac{2N\sin^2(Nx/2)}{\pi(Nx)^2} = \frac{2\sin^2(Nx/2)}{\pi Nx^2}$$

The only feature of the explicit formula for  $F_N(x)$  that we need is  $F_N(x) > 0$ . Since  $\hat{F}_N(0) = 1$ , (4) follows.

The last step in the proof is to confirm (3). If  $f \in L^1(\mathbb{R})$ , then  $\hat{f}$  is continuous and by definition,

$$\sigma_N(x) = \frac{1}{2\pi} \int_{-N}^{N} \hat{f}(\xi) (1 - |\xi/N|) e^{ix\xi} d\xi = \frac{1}{2\pi} \int_{\mathbb{R}} \int_{\mathbb{R}} f(y) e^{-iy\xi} dy (1 - |\xi/N|) e^{ix\xi} d\xi$$

The majorant  $|f(y)|(1-|\xi/N|)^+$  is integrable with respect to  $dyd\xi$  so Fubini's theorem and Theorem 2 applied to  $F_N$  imply

$$\sigma_N(x) = \int_{\mathbb{R}} f(y) \frac{1}{2\pi} \int_{\mathbb{R}} (1 - |\xi/N|)^+ e^{i(x-y)\xi} d\xi \, dy = f * F_N(x)$$

As a final remark, we double check our arithmetic in the computation of  $F_N$  as follows.

$$F_N(0) = \frac{1}{2\pi} \int_{-N}^{N} (1 - |\xi/N|) d\xi$$

The integral on the right is  $1/2\pi$  times the area of the triangle of base 2N and height 1, so the total is  $N/2\pi$ . The left side is

$$F_N(0) = \lim_{x \to 0} \frac{2\sin^2(Nx/2)}{\pi Nx^2} = \lim_{x \to 0} \frac{2(Nx/2)^2}{\pi Nx^2} = N/2\pi$$

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### 18.103 Fall 2013

## 1 Fourier Integrals of finite measures.

Denote the space of finite, positive, measures on  $\mathbb{R}$  by

$$M_{+}(\mathbb{R}) = \{ \mu : \mu \text{ is a positive measure on } \mathbb{R}; \quad \mu(\mathbb{R}) < \infty \}$$

**Proposition 1** For  $\mu \in M_+(\mathbb{R})$ , we define the Fourier transform by

$$\mathcal{F}(\mu) = \hat{\mu}(\xi) = \int_{\mathbb{R}} e^{-ix\xi} \, d\mu(x)$$

Then

$$\mathcal{F}: M_+(\mathbb{R}) \to C_b(\mathbb{R})$$

where  $C_b(\mathbb{R})$  is the space of bounded continuous functions.

*Proof.* We have

$$|\hat{\mu}(\xi)| \le \left| \int_{\mathbb{R}} e^{-ix\xi} d\mu(x) \right| \le \int_{\mathbb{R}} |e^{-ix\xi}| d\mu(x) = \mu(\mathbb{R}) < \infty$$

Furthermore, since  $\mu(\mathbb{R}) < \infty$ , the function  $g(x) \equiv 1$  is integrable, and serves as a majorant,  $|e^{-ix\xi}| \leq 1 = g(x)$ . By the dominated convergence theorem,  $\hat{\mu}(\xi)$  is continuous.

**Theorem 1** (Uniqueness) Let  $\mu \in M_+(\mathbb{R})$ . Then  $\mu$  is uniquely determined by  $\hat{\mu}$ .

*Proof.* We show that if  $\hat{\mu}_1 = \hat{\mu}_2$ , then  $\mu_1 = \mu_2$ . Let  $\varphi \in \mathcal{S}$ . Then

$$\int_{\mathbb{R}} \hat{\varphi}(y) d\mu(y) = \int_{\mathbb{R}} \varphi(x) \hat{\mu}(x) dx \tag{1}$$

Indeed, by Fubini's theorem

$$\int_{\mathbb{R}} \hat{\varphi}(y) d\mu(y) = \int_{\mathbb{R}} \int_{\mathbb{R}} e^{-ixy} \varphi(x) \, dx d\mu(y) = \int_{\mathbb{R}} \int_{\mathbb{R}} e^{-ixy} d\mu(y) \varphi(x) \, dx = \int_{\mathbb{R}} \hat{\mu}(y) \varphi(x) \, dx$$

If  $\hat{\mu}_1(y) = \hat{\mu}_2(y)$ , then by (1),

$$\int_{\mathbb{R}} \hat{\varphi}(y) d\mu_1(y) = \int_{\mathbb{R}} \hat{\varphi}(y) d\mu_2(y)$$

for every  $\varphi \in \mathcal{S}$ . Since the Fourier transform is invertible on  $\mathcal{S}$ , we can also write this as

$$\int_{\mathbb{R}} \varphi(y) d\mu_1(y) = \int_{\mathbb{R}} \varphi(y) d\mu_2(y) \quad \text{for all} \quad \varphi \in \mathcal{S}$$

Choose  $\varphi_{\epsilon} \in \mathcal{S}(\mathbb{R})$  such that

$$1_{[a,b]} \le \varphi_{\epsilon} \le 1_{[a-\epsilon,b+\epsilon]}$$

By the dominated convergence theorem

$$\mu_1([a,b]) = \lim_{\epsilon \to 0} \int_{\mathbb{R}} \varphi_{\epsilon} d\mu_1 = \lim_{\epsilon \to 0} \int_{\mathbb{R}} \varphi_{\epsilon} d\mu_2 = \mu_2([a,b])$$

This shows that  $\mu_1$  and  $\mu_2$  are the same.

Weak convergence of measures. Let  $\mu_j$  and  $\mu$  denote positive measures with finite total mass on  $\mathbb{R}$ . We say that  $\mu_j$  tends weakly to  $\mu$  if

$$\lim_{j \to \infty} \int_{\mathbb{R}} \varphi d\mu_j = \int_{\mathbb{R}} \varphi d\mu$$

for all  $\varphi \in C_0(\mathbb{R})$ .

Exercise. Show that if

$$\lim_{j\to\infty}\int_{\mathbb{R}}\varphi d\mu_j=\int_{\mathbb{R}}\varphi d\mu$$

for all  $\varphi \in C_0^{\infty}(\mathbb{R})$ , then  $\mu_j \to \mu$  weakly. (The reason is that  $C_0^{\infty}(\mathbb{R})$  is dense in  $C_0(\mathbb{R})$  in the uniform norm, i. e. the  $L^{\infty}(\mathbb{R})$  norm. In particular, functions  $\varphi \in \mathcal{S}(\mathbb{R})$  suffice.)

We will establish weak convergence by finding a sufficient condition for it in terms of Fourier transforms. (Note that we established the analogous lemma for Fourier series when we proved Weyl's equidistribution theorem.)

**Proposition 2** If  $\mu_j$  and  $\mu$  belong to  $M^+(\mathbb{R})$ , and for each  $\xi \in \mathbb{R}$ ,

$$\lim_{j\to\infty}\hat{\mu}_j(\xi)=\hat{\mu}(\xi)$$

then

$$\lim_{j \to \infty} \int_{\mathbb{D}} f d\mu_j = \int_{\mathbb{D}} f d\mu$$

for all  $f \in \mathcal{S}(\mathbb{R})$ .

*Proof.* We have in particular,  $\mu_j(\mathbb{R}) = \hat{\mu}_j(0) \to \hat{\mu}(0)$  so that the sequence  $\mu_j(\mathbb{R})$  is bounded. (In all of our applications we have probability measures,  $\mu_j(\mathbb{R}) = 1$ , so this step is not needed.) Thus

$$\sup_{j} |\hat{\mu}_{j}(\xi)| = \sup_{j} \mu_{j}(\mathbb{R}) \le C < \infty$$

For  $\varphi \in \mathcal{S}$ ,  $|\varphi(\xi)\hat{\mu}_j(\xi)| \leq C|\varphi(\xi)|$  is an integrable majorant, so the dominated convergence theorem gives

$$\lim_{j \to \infty} \int_{\mathbb{R}} \varphi(\xi) \hat{\mu}_j(\xi) d\xi = \int_{\mathbb{R}} \varphi(\xi) \hat{\mu}(\xi) d\xi$$

But by Fubini's theorem this is the same as

$$\lim_{j \to \infty} \int_{\mathbb{R}} \hat{\varphi}(y) d\mu_j(y) = \int_{\mathbb{R}} \hat{\varphi}(y) d\mu(y)$$

But the set of all  $\hat{\varphi}$  such that  $\varphi \in \mathcal{S}$  is all of  $\mathcal{S}$ , so we have the desired weak convergence of  $\mu_j$  to  $\mu$ .

In the applications we want more explicit kind of convergence, namely convergence of  $\mu_j(I)$  for intervals I. This nearly works. What can go wrong is illustrated using sequences of point masses,

$$\delta_a(x) = \delta(x - a)$$

This measure is defined by  $\delta_a(E) = 1$  if  $a \in E$  and 0 if  $a \notin E$ . The sequence  $\delta_{1/n}$  tends weakly to  $\delta_0$  as  $n \to \infty$ , but

$$\lim_{i \to \infty} \delta_{1/n}(I) = 1 \neq 0 = \delta_0(I), \qquad I = (0, 1).$$

A continuous measure is a measure  $\mu$  such that  $\mu(a) = 0$  for any single point a. A measure that has only point masses is called atomic, and a continuous measure is sometimes called non-atomic. On your homework you show how to split a measure into atomic and continuous parts. The discontinuities arise at at most countably many points. A continuous measure is characterized by the fact that  $\mu((a,b))$  is continuous as a function of a and b. Equivalently,  $\mu((a,b)) = \mu([a,b])$  for any  $a \leq b$ .

### Proposition 3 If

$$\lim_{j \to \infty} \int_{\mathbb{D}} f d\mu_j = \int_{\mathbb{D}} f d\mu$$

for all  $f \in C_0^{\infty}(\mathbb{R})$ , then

$$\limsup_{j \to \infty} \mu_j((a, b)) \le \mu([a, b])$$

and

$$\liminf_{j \to \infty} \mu_j((a, b)) \ge \mu((a, b))$$

In particular if  $\mu$  is continuous then

$$\mu_i((a,b)) \to \mu((a,b)) = \mu([a,b])$$

*Proof.* Let  $\varphi \in \mathcal{S}$  be such that  $1_{(a,b)} \leq \varphi \leq 1_{(a-\epsilon,b+\epsilon)}$ , then

$$\limsup_{j \to \infty} \mu_j((a, b)) \le \limsup_{j \to \infty} \int_{\mathbb{R}} \varphi \, d\mu_j = \int_{\mathbb{R}} \varphi \, d\mu \le \mu((a - \epsilon, b + \epsilon))$$

Taking the limit as  $\epsilon \to 0$  gives the upper bound. The lower bound is similar using  $\varphi \in C_0^{\infty}(\mathbb{R})$  such that  $1_{(a+\epsilon,b-\epsilon)} \leq \varphi \leq 1_{(a,b)}$ . It is important to note that the sequence  $\mu_j$  can have all the atomic parts it wants. Only the target measure  $\mu$  needs to be continuous at the endpoints. This is crucial to the applications.

## 2 An application to the central limit theorem.

Recall that in probability theory, we are concerned with measures  $\mu_X$  on  $\mathbb{R}$  that represent the probability distribution of a random variable X satisfying

$$P(a < X < b) = \mu_X((a, b)) = \mathbb{E}(1_{(a,b)}(X)) = \int_{\mathbb{R}} 1_{(a,b)} d\mu_X$$

and, more generally, for any Borel function  $\varphi$  on  $\mathbb{R}$  that is  $\mu_f$ -integrable,

$$\int_{\mathbb{R}} \varphi(x) d\mu_f(x) = \mathbb{E}(\varphi(X)) = \int_{M} \varphi(X) d\nu$$

For example, all the Rademacher functions  $R_n$  all have the same distribution, value 1 with probability 1/2 and value -1 with probability 1/2. The corresponding measure is denoted

$$\mu = \frac{1}{2}\delta_1 + \frac{1}{2}\delta_{-1}$$

$$\mathbb{E}(\varphi(R_n)) = \int_{\mathbb{R}} \varphi(x)d\mu(x) = \frac{1}{2}\varphi(1) + \frac{1}{2}\varphi(-1)$$

The mean and variance of X is defined by

$$\mathbb{E}(X) = \int_{-\infty}^{\infty} x \, d\mu_X(x); \quad \text{Var}(X) = \mathbb{E}((X - \mathbb{E}(X))^2) = \int_{-\infty}^{\infty} (x - \mathbb{E}(X))^2 \, d\mu_X(x)$$

For  $X = R_n$  the mean is 0 and the variance is

$$\frac{1}{2}(1-0)^2 + \frac{1}{2}(1-0)^2 = 1$$

The characteristic function  $\chi_X$  of a random variable X is defined by

$$\chi_X(t) = \mathbb{E}(e^{itX}) = \int_{-\infty}^{\infty} e^{itx} d\mu_X(x)$$

For example, the characteristic function of each  $R_n$  is

$$\chi(t) = (1/2)e^{it} + (1/2)e^{-it} = \cos(t)$$

In general, up to a sign, the characteristic function is the Fourier transform of the distribution of a random variable X,

$$\chi_X(t) = \widehat{\mu_X}(-t)$$

The notion of weak convergence is central to probability theory. Weak convergence of the distributional measures is the same as

$$\mathbb{E}(\varphi(X_i)) \to \mathbb{E}(\varphi(X))$$

for all  $\varphi \in C_0(\mathbb{R})$  (or equivalently for all  $\varphi \in C_0^{\infty}(\mathbb{R})$ ). In probability theory it's also convenient to know (and not hard to show) that one can broaden the class of test functions from  $\varphi \in C_0(\mathbb{R})$  to  $\varphi \in C_b(\mathbb{R})$ , the space of bounded continuous functions.

The word used by probabilists for weak convergence is *convergence in law*. They often prefer an equivalent, but more concrete, formulation using test functions of the form  $\varphi = 1_I$ , where  $I \subset \mathbb{R}$  is an interval. We have

$$\mathbb{E}(X \in I) = \mathbb{E}(1_I(X)) = \int_I d\mu_X = \mu_X(I)$$

The discontinuity of  $1_I$  at its endpoints requires us to change the statement slightly, as we explained earlier and now express using notations from probability theory.

The (cumulative) distribution function  $F_X$  of a random variable X (with probability distribution  $\mu_X$ ) is defined as

$$F_X(a) = \mathbb{E}(X \le a) = \mu_X((-\infty, a])$$

We say that  $X_j$  converges in law to X if

$$\lim_{i \to \infty} F_{X_j}(a) = F_X(a)$$

for every a at which F(x) is continuous. It follows that if  $X_j$  tends to X in law

$$\lim_{i \to \infty} \mathbb{E}(a < X_j < b) = \mathbb{E}(a < X < b)$$

provided  $F_X$  is continuous at a and b. Proposition 3 says that weak convergence of  $\mu_{X_j}$  to  $\mu_X$  implies convergence in law of  $X_j$  to X. The converse is left as an exercise; we won't use it. (To prove this, first figure out how convergence in law identifies the jumps of the increasing function  $F_X$ .)

A gaussian random variable X with mean zero and variance 1 is a variable whose distribution is given by

$$\mathbb{E}(a < X < b) = \int_{a}^{b} g(x) dx;$$

in which

$$d\mu_X = g(x)dx, \qquad g(x) = \frac{1}{\sqrt{2\pi}}e^{-x^2/2}$$

Thus

$$\mathbb{E}(\varphi(X)) = \int_{-\infty}^{\infty} \varphi(x)g(x) \, dx$$

The characteristic function is

$$\chi(t) = \chi_X(t) = \mathbb{E}(e^{itX}) = \int_{-\infty}^{\infty} e^{ixt} g(x) \, dx = \hat{g}(-t) = e^{-t^2/2}$$
 (2)

In particular,

$$\mathbb{E}(1) = \int_{-\infty}^{\infty} g(x) \, dx = 1$$

(This is just the required normalization of a probability measure: total mass 1.) Differentiating (2) with respect to t, we get

$$\mathbb{E}(X) = \int_{-\infty}^{\infty} x \, g(x) \, dx = 0 \quad \text{(mean zero)}$$

Differentiating again, we get

$$\mathbb{E}(X^2) = \int_{-\infty}^{\infty} x^2 g(x) dx = 1 \quad \text{(variance 1)}$$

We can rescale to get any variance. Let

$$g_{\sigma}(x) = (1/\sigma)g(x/\sigma), \quad g(x) = g_1(x) = \frac{1}{\sqrt{2\pi}}e^{-x^2/2}$$

The parameter  $\sigma$  is known as the standard deviation and the variance is the square of the standard deviation.

$$\int_{-\infty}^{\infty} x^2 g_{\sigma}(x) dx = \sigma^2$$

We can also change the mean by translation: If X has distribution  $g_{\sigma}(x-x_0)dx$ , then it has mean  $x_0$  and variance  $\sigma^2$ .

To clarify the meaning of the scale factor  $\sigma$ , consider  $X_{\sigma}$  a gaussian random variable with standard deviation  $\sigma$ , and  $X_1$ , a gaussian random variable with standard deviation 1. Then

$$P(a\sigma < X_{\sigma} - \mathbb{E}(X_{\sigma}) < b\sigma) = P(a < X_1 - \mathbb{E}X_1 < b)$$

**Theorem 2** (Central Limit Theorem) Let  $X_1, X_2, \ldots$  be independent, identically distributed random variables such that

$$\mathbb{E}(X_1) = M; \quad \mathbb{E}[(X_1 - M)^2] = \sigma^2; \quad \mathbb{E}(|X_1|^{2+\alpha}) = A < \infty$$

for some  $\alpha > 0$ . Then

$$\mathbb{E}\left(a < \frac{X_1 + \dots + X_n - nM}{\sqrt{n}} < b\right) \longrightarrow \int_a^b g_\sigma(x) \, dx$$

### Lemma 1

$$e^{ix} = 1 + ix + (ix)^2/2 + R(x)$$

with

$$|R(x)| \le 4\min(|x|^2, |x|^3) \le 4|x|^{2+\alpha}$$

for all  $\alpha$ ,  $0 < \alpha < 1$ .

*Proof.* The fundamental theorem of calculus implies

$$f(1) = f(0) + f'(0) + \frac{1}{2!}f''(0) + \frac{1}{2!}\int_0^1 f'''(t)(1-t)^2 dt$$

Let  $f(t) = e^{itx}$ . Then

$$R(x) = \frac{1}{2} \int_0^1 (ix)^3 e^{itx} (1-t)^2 dt$$

Therefore,

$$|R(x)| \le \frac{|x|^3}{2} \int_0^1 (1-t)^2 dt = |x|^3/6$$

for all  $|x| \leq 1$ . On the other hand, for  $|x| \geq 1$ ,

$$|R(x)| = |1 + ix + (ix)^2/2 - e^{ix}| \le 2 + |x| + x^2/2 \le 4|x|^2$$

Replacing  $X_j$  with  $X_j - M$  we may assume without loss of generality that M = 0. We compute the Fourier transform of the measure  $\mu_n$  defined by

$$\mu_n((a,b)) = P\left(a < \frac{X_1 + \dots + X_n}{\sqrt{n}} < b\right)$$

$$\hat{\mu}_n(\xi) = \mathbb{E}\left(e^{-i\xi(X_1 + \dots + X_n)/\sqrt{n}}\right) = \prod_{i=1}^n \mathbb{E}(e^{-i\xi X_j/\sqrt{n}}) = \left(\mathbb{E}(e^{-i\xi X_1/\sqrt{n}})\right)^n$$

and since M=0,

$$\mathbb{E}(e^{-i\xi X_1/\sqrt{n}}) = \int_{\mathbb{R}} e^{-ix\xi} d\mu_1(x) = \int_{\mathbb{R}} [1 - ix\xi/\sqrt{n} + (-ix\xi)^2/2n + R(-x\xi/\sqrt{n})] d\mu_1(x)$$
$$= 1 - \sigma^2 \xi^2/2n + O(|\xi|^{2+\alpha}/n^{1+\alpha/2})$$

For each fixed  $\xi$  we therefore get

$$\lim_{n \to \infty} [1 - \sigma^2 \xi^2 / 2n + O(1/n^{1+\alpha/2})]^n = e^{-\sigma^2 \xi^2 / 2}$$

In other words, for all  $\xi$ 

$$\lim_{n\to\infty}\hat{\mu}_n(\xi)=\hat{g}_{\sigma}(\xi)$$

Then we apply Proposition 2 and 3 to finish the proof.

### Sums of random variables and convolution.

We can rephrase the central limit theorem in terms of convolution. For independent  $X_1$  and  $X_2$ , suppose that  $\nu_j = \mu_{X_j}$ , then

$$\mathbb{E}(\varphi(X_1 + X_2)) = \int_{\mathbb{R}} \int_{\mathbb{R}} \varphi(x_1 + x_2) d\nu_1(x_1) d\nu_2(x_2)$$

In particular, if we define a measure by

$$\nu(I) = \int_{\mathbb{R}} \int_{\mathbb{R}} 1_I(x_1 + x_2) d\nu_1(x_1) d\nu_2(x_2)$$
 (3)

for all intervals I, the  $\nu = \mu_{X_1 + X_2}$ , the distribution of the sum  $X_1 + X_2$ .

Exercise. Show that if  $d\nu_j = f_j(x)dx$ , with  $f_j \in L^1(\mathbb{R})$ , then

$$d\nu = g(x)dx$$
, with  $g = f_1 * f_2$ 

This justifies turning (3) into the definition of  $\nu = \nu_1 * \nu_2$ .

Exercise. Show that under this definition.

$$\widehat{\nu_1 * \nu_2}(\xi) = \hat{\nu}_1 \hat{\nu}_2 \tag{4}$$

For a sequence of independent random variables,  $X_i$ ,

$$\mu_{X_1+\cdots+X_n} = \mu_{X_1} * \mu_{X_2} * \cdots * \mu_{X_n}$$

For instance, if  $\mu_{X_1} = (1/2)(\delta_{-1} + \delta_1)$ , and the variables are i. i. d., then

$$\mu_{X_1+\dots+X_n} = 2^{-n} \sum_{k=0}^n \binom{n}{k} \delta_{-n+2k}$$

Exercise. Express the central limit theorem (in this special case) in terms of this measure, and find the scaling under which this measure tends weakly to the gaussian distribution  $g_1(x)dx$ .

We can also consider the class of signed measures Borel measures  $M(\mathbb{R})$ , real-valued functions  $\mu$  on Borel sets of  $\mathbb{R}$  such that

$$\|\mu\| = \sup\{\sum_{j=1}^{\infty} |\mu(I_j)| : \bigcup I_j = \mathbb{R}, \text{ (disjoint intervals)}\} < \infty$$

The norm  $\|\mu\|$  represents the total mass of  $\mu$  (also called the total variation). A signed measure can always be written as

$$\mu = \mu_{+} - \mu_{-}$$

for two finite, positive measures  $\mu_{\pm}$  such that, in addition, there are Borel sets  $E_{\pm}$  such that  $\mu_{\pm}(E_{\pm}) = \mu_{\pm}(\mathbb{R})$  and  $\mu_{+}(E_{-}) = \mu_{-}(E_{+}) = 0$ . (In this case we say  $\mu_{+}$  and  $\mu_{-}$  are mutually singular, and write  $\mu_{+} \perp \mu_{-}$ . This specifies the measures uniquely.) Using this decomposition, we can define  $\mu * \nu$  for signed measures using linearity and (4), and it remains the case that Fourier transform of the convolution is the product of the Fourier transforms.

# 3 $\mathcal{S}'(\mathbb{R})$ , the class of tempered distributions

Define a metric on the Schwartz class

$$\mathcal{S}(\mathbb{R}) = \{ \varphi \in C^{\infty}(\mathbb{R}) : \|\varphi\|_{j,k} < \infty, \ j, \ k = 0, \ 1, \ 2, \dots \}$$

with seminorms<sup>1</sup>

$$\|\varphi\|_{j,k} = \sup_{x \in \mathbb{R}} |x^j \varphi^{(k)}(x)|$$

by

$$dist(f,g) = \sum_{j,k=0}^{\infty} 2^{-j-k} \min(\|f - g\|_{j,k}, 1)$$

We take the minimum with 1 so that the sum is finite. The seminorm property is used to confirm the triangle inequality so that this is a metric.

The dual space to  $\mathcal{S}(\mathbb{R})$ , denoted  $\mathcal{S}'(\mathbb{R})$  is the set of continuous, linear functions  $T: \mathcal{S} \to \mathbb{C}$ . (The point of defining the metric was to say in what sense T is continuous.) This class is also known as the space of tempered distributions. (More generally, the class of distributions, are dual to the smaller function space  $C_0^{\infty}(\mathbb{R})$ . Because the tempered distributions have to act on Schwartz class functions, they have better behavior at infinity than general distributions. The more general distributions don't have well defined Fourier transforms because they can grow too fast at infinity.)

The most useful notion of convergence in S' is the same weak convergence we already discussed. We say that  $T_j$  tends to T if

$$\lim_{j \to \infty} T_j(\varphi) = T(\varphi)$$

<sup>&</sup>lt;sup>1</sup>A seminorm satisfies  $||f|| \ge 0$ ,  $||f + g|| \le ||f|| + ||g||$  and ||cf|| = |c|||f||, but not necessarily the last axiom: ||f|| = 0 need not imply that f = 0.

for all  $\varphi \in \mathcal{S}$ . (The technical reason why this is a useful kind of limit is that the existence of the limit point by point for each  $\varphi \in \mathcal{S}(\mathbb{R})$  suffices in order that the limiting linear operator T be continuous in the  $\mathcal{S}(\mathbb{R})$  metric.)

If u(x) is a bounded measurable function or  $u \in L^p(\mathbb{R})$ , then we define

$$T_u(\varphi) = \int_{\mathbb{R}} u(x)\varphi(x) dx$$

for any  $\varphi \in \mathcal{S}$ . In this way we identify every such function u with a distribution. Measures are also identified with

$$T_{\mu}(\varphi) = \int_{\mathbb{R}} \varphi \, d\mu$$

Any linear continuous operation on  $\mathcal{S}$  defines a corresponding (dual) operation on  $\mathcal{S}'$ . For example, we have calculated for  $u \in \mathcal{S}$  and for  $\varphi \in \mathcal{S}$  that

$$\int_{R} u\hat{\varphi} \, dx = \int_{\mathbb{R}} \hat{u}\varphi \, dx$$

This explains the definition of the Fourier transform of any  $T \in \mathcal{S}'(\mathbb{R})$ , namely

$$\hat{T}(\varphi) = T(\hat{\varphi})$$

For a measure,  $\mu \in M^+(\mathbb{R})$  we could also define the Fourier transform by

$$\hat{\mu}(\xi) = \int_{\mathbb{R}} e^{-ix\xi} \, d\mu(x)$$

The two definitions are consistent. The proof is left as an exercise. But let's illustrate it by comparing the two definitions in one case, namely  $\mu_0 = \delta$ , the delta function (unit mass at 0). The corresponding tempered distribution  $T_0 \in \mathcal{S}'(\mathbb{R})$  is given by  $T_0(\varphi) = \varphi(0)$ . Then

$$\hat{\mu}_0(\xi) = \int_{\mathbb{R}} e^{-ix\xi} d\mu_0(x) = e^{-i0\xi} = 1$$

On the other hand,

$$\hat{T}_0(\varphi) = T_0(\hat{\varphi}) = \hat{\varphi}(0) = \int_{\mathbb{R}} \varphi(x) \, dx = \int_{\mathbb{R}} \varphi(x) u_0(x) \, dx$$

with  $u_0(x) = 1$ . In other words, the definitions are consistent, yielding  $\hat{\mu}_0 \equiv 1$ .

The idea of duality also leads to the definition of the derivative of a tempered distribution, namely,

$$T'(\varphi) = -T(\varphi')$$

This is motivated by the formula (in the special case  $u \in \mathcal{S}$ ,  $\varphi \in \mathcal{S}$ ,

$$\int_{\mathbb{R}} u'\varphi \, dx = -\int_{\mathbb{R}} u\varphi' \, dx,$$

which follows from integration by parts (or the product rule  $(u\varphi)' = u'\varphi + u\varphi'$ ).

Exercise. Find  $\widehat{T}'(\xi)$  directly from the definition in the case  $T = \delta$ . More examples and formulas are on PS11.

Fourier inversion on  $\mathcal{S}'(\mathbb{R})$ . The Fourier transform is a continuous linear mapping from  $\mathcal{S}(\mathbb{R})$  to  $\mathcal{S}(\mathbb{R})$  and it inverse is also a continuous mapping from  $\mathcal{S}(\mathbb{R})$  to  $\mathcal{S}(\mathbb{R})$  with the formula

$$\check{\varphi}(x) = \frac{1}{2\pi} \int_{\mathbb{R}} \varphi(\xi) e^{ix\xi} d\xi$$

**Proposition 4** If  $T \in \mathcal{S}'(\mathbb{R})$ , and define S by

$$S(\varphi) = T(\check{\varphi})$$

Then  $S \in \mathcal{S}'(\mathbb{R})$  and  $\hat{S} = T$ . In other words, the mapping  $T \mapsto \check{T}$  defined by

$$\check{T}(\varphi) = T(\check{\varphi})$$

inverts the Fourier transform on  $\mathcal{S}'(\mathbb{R})$ .

This proposition is a corollary of Fourier inversion on  $\mathcal{S}(\mathbb{R})$  and the definition of Fourier transform on  $\mathcal{S}'(\mathbb{R})$ . Let  $T \in \mathcal{S}'(\mathbb{R})$ . The inverse Fourier transform mapping  $\varphi \mapsto \check{\varphi}$  is a continuous linear mapping from  $\mathcal{S}(\mathbb{R}) \to \mathcal{S}(\mathbb{R})$ , so S defined by

$$S(\varphi) = T(\check{\varphi})$$

is a continuous linear mapping from  $\mathcal{S}(\mathbb{R}) \to \mathbb{C}$ . In order to show that  $\hat{S} = T$ , recall that the Fourier inversion formula on  $\mathcal{S}(\mathbb{R})$  says that for all  $\eta \in \mathcal{S}(\mathbb{R})$ , if  $\varphi = \hat{\eta}$ , then  $\check{\varphi} = \eta$ . Thus for all  $\eta \in \mathcal{S}(\mathbb{R})$  (and denoting  $\varphi = \hat{\eta}$ )

$$\hat{S}(\eta) = S(\hat{\eta}) = S(\varphi) = T(\check{\varphi}) = T(\eta)$$

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.103 Fall 2013

## **Orthonormal Bases**

Consider an inner product space V with inner product  $\langle f, g \rangle$  and norm

$$||f||^2 = \langle f, f \rangle$$

**Proposition 1** (Continuity) If  $||u_n - u|| \to 0$  and  $||v_n - v|| \to 0$  as  $n \to \infty$ , then

$$||u_n|| \to ||u||; \quad \langle u_n, v_n \rangle \to \langle u, v \rangle.$$

*Proof.* Note first that since  $||v_n - v|| \to 0$ ,

$$||v_n|| \le ||v_n - v|| + ||v|| \le M < \infty$$

for a constant M independent of n. Therefore, as  $n \to \infty$ ,

$$|\langle u_n, v_n \rangle - \langle u, v \rangle| = |\langle u_n - u, v_n \rangle + \langle u, v_n - v \rangle| \le M ||u_n - u|| + ||u|| ||v_n - v|| \to 0$$

In particular, if  $u_n = v_n$ , then  $||u_n||^2 = \langle u_n, u_n \rangle \to \langle u, u \rangle = ||u||^2$ .  $\square$ 

For u and v in V we say that u is perpendicular to v and write  $u \perp v$  if  $\langle u, v \rangle = 0$ . The Pythogorean theorem says that if  $u \perp v$ , then

$$||u+v||^2 = ||u||^2 + ||v||^2$$
(1)

**Definition 1**  $\varphi_n$  is called an orthonormal sequence,  $n = 1, 2, ..., if \langle \varphi_n, \varphi_m \rangle = 0$  for  $n \neq m$  and  $\langle \varphi_n, \varphi_n \rangle = ||\varphi_n||^2 = 1$ .

Suppose that  $\varphi_n$  is an orthonormal sequence in an inner product space V. The following four consequences of the Pythagorean theorem (1) were proved in class (and are also in the text):

If 
$$h = \sum_{n=1}^{N} a_n \varphi_n$$
, then

$$||h||^2 = \sum_{1}^{N} |a_n|^2.$$
 (2)

If  $f \in V$  and  $s_N = \sum_{n=1}^N \langle f, \varphi_n \rangle \varphi_n$ , then

$$||f||^2 = ||f - s_N||^2 + ||s_N||^2$$
(3)

If  $V_N = \text{span} \{\varphi_1, \varphi_2, \dots, \varphi_N\}$ , then

$$||f - s_N|| = \min_{g \in V_N} ||f - g||$$
 (best approximation property) (4)

If  $c_n = \langle f, \varphi_n \rangle$ , then

$$||f||^2 \ge \sum_{n=1}^{\infty} |c_n|^2$$
 (Bessel's inequality). (5)

**Definition 2** A Hilbert space is defined as a complete inner product space (under the distance d(u, v) = ||u - v||).

**Theorem 1** Suppose that  $\varphi_n$  is an orthonormal sequence in a Hilbert space H. Let

$$V_N = span\{\varphi_1, \varphi_2, \dots, \varphi_N\}, \quad V = \bigcup_{N=1}^{\infty} V_N$$

(V is the vector space of finite linear combinations of  $\varphi_n$ .) The following are equivalent.

- a) V is dense in H (with respect to the distance d(f,g) = ||f g||),
- b) If  $f \in H$  and  $\langle f, \varphi_n \rangle = 0$  for all n, then f = 0.

c) If 
$$f \in H$$
 and  $s_N = \sum_{n=1}^N \langle f, \varphi_n \rangle \varphi_n$ , then  $||s_N - f|| \to 0$  as  $N \to \infty$ .

d) If  $f \in H$ , then

$$||f||^2 = \sum_{n=1}^{\infty} |\langle f, \varphi_n \rangle|^2$$

If the properties of the theorem hold, then  $\{\varphi_n\}_{n=1}^{\infty}$  is called an *orthonormal basis* or *complete* orthonormal system for H. (Note that the word "complete" used here does not mean the same thing as completeness of a metric space.)

*Proof.* (a)  $\Longrightarrow$  (b). Let f satisfy  $\langle f, \varphi_n \rangle = 0$ , then by taking finite linear combinations,  $\langle f, v \rangle = 0$  for all  $v \in V$ . Choose a sequence  $v_j \in V$  so that  $||v_j - f|| \to 0$  as  $j \to \infty$ . Then by Proposition 1 above

$$0 = \langle f, v_j \rangle \to \langle f, f \rangle \implies ||f||^2 = 0 \implies f = 0$$

(b)  $\implies$  (c). Let  $f \in H$  and denote  $c_n = \langle f, \varphi_n \rangle$ ,  $s_N = \sum_{1}^{N} c_n \varphi_n$ . By Bessel's inequality (5),

$$\sum_{1}^{\infty} |c_n|^2 \le ||f||^2 < \infty.$$

Hence, for M < N (using (2))

$$||s_N - s_M||^2 = \left\| \sum_{M+1}^N c_n \varphi_n \right\|^2 = \sum_{M+1}^N |c_n|^2 \to 0 \text{ as } M, N \to \infty.$$

In other words,  $s_N$  is a Cauchy sequence in H. By completeness of H, there is  $u \in H$  such that  $||s_N - u|| \to 0$  as  $N \to \infty$ . Moreover,

$$\langle f - s_N, \varphi_n \rangle = 0$$
 for all  $N \ge n$ .

Taking the limit as  $N \to \infty$  with n fixed yields

$$\langle f - u, \varphi_n \rangle = 0$$
 for all  $n$ .

Therefore by (b), f - u = 0.

(c) 
$$\implies$$
 (d). Using (3) and (2),

$$||f||^2 = ||f - s_N||^2 + ||s_N||^2 = ||f - s_N||^2 + \sum_{n=1}^{N} |c_n|^2, \qquad (c_n = \langle f, \varphi_n \rangle)$$

Take the limit as  $N \to \infty$ . By (c),  $||f - s_N||^2 \to 0$ . Therefore,

$$||f||^2 = \sum_{1}^{\infty} |c_n|^2$$

Finally, for  $(d) \implies (a)$ ,

$$||f||^2 = ||f - s_N||^2 + \sum_{1}^{N} |c_n|^2$$

Take the limit as  $N \to \infty$ , then by (d) the rightmost term tends to  $||f||^2$  so that  $||f - s_N||^2 \to 0$ . Since  $s_N \in V_N \subset V$ , V is dense in H.  $\square$ 

**Proposition 2** Let  $\varphi_n$  be an orthonormal sequence in a Hilbert space H, and

$$\sum |a_n|^2 < \infty, \quad \sum |b_n|^2 < \infty$$

then

$$u = \sum_{n=1}^{\infty} a_n \varphi_n, \quad v = \sum_{n=1}^{\infty} b_n \varphi_n$$

are convergent series in H norm and

$$\langle u, v \rangle = \sum_{n=1}^{\infty} a_n \overline{b_n} \tag{6}$$

*Proof.* Let

$$u_N = \sum_{1}^{N} a_n \varphi_n; \quad v_N = \sum_{1}^{N} b_n \varphi_n.$$

Then for M < N,

$$||u_N - u_M||^2 = \sum_{M}^{N} |a_n|^2 \to 0 \text{ as } M \to \infty$$

so that  $u_N$  is a Cauchy sequence converging to some  $u \in H$ . Similarly,  $v_N \to v$  in H norm. Finally,

$$\langle u_N, v_N \rangle = \sum_{j,k=1}^N \langle a_j \varphi_j, b_k \varphi_k \rangle = \sum_{j,k=1}^N a_j \overline{b_k} \langle \varphi_j, \varphi_k \rangle = \sum_{j=1}^N a_j \overline{b_j}$$

since  $\langle \varphi_j, f_k \rangle = 0$  for  $j \neq k$  and  $\langle f_j, f_j \rangle = 1$ . Taking the limit as  $N \to \infty$  and using the continuity property (1),  $\langle u_N, v_N \rangle \to \langle u, v \rangle$ , gives (6).  $\square$ 

If H is a Hilbert space and  $\{\varphi_n\}_{n=1}^{\infty}$  is an orthonormal basis, then every element can be written

$$f = \sum_{n=1}^{\infty} a_n \varphi_n \quad \text{(series converges in norm)}$$

The mapping

$$\{a_n\} \mapsto \sum_n a_n \varphi_n$$

is a linear isometry from  $\ell^2(\mathbb{N})$  to H that preserves the inner product. The inverse mapping is

$$f \mapsto \{a_n\} = \{\langle f, \varphi_n \rangle\}$$

It is also useful to know that as soon as a linear mapping between Hilbert spaces is an isometry (preserves norms of vectors) it must also preserve the inner product. Indeed, the inner product function (of two variables u and v) can be written as a function of the norm function (of linear combinations of u and v). This is known as polarization:

## Polarization Formula.

$$\langle u, v \rangle = a_1 \|u + iv\|^2 + a_2 \|u + v\|^2 + a_3 \|u\|^2 + a_4 \|v\|^2 \tag{7}$$

with

$$a_1 = i/2$$
,  $a_2 = 1/2$ ,  $a_3 = -(1+i)/2$ ,  $a_4 = -(i+1)/2$ 

Proof.

$$||u+iv||^2 = \langle u+iv, u+iv \rangle$$

$$= ||u||^2 + \langle iv, u \rangle + \langle u, iv \rangle + ||v||^2$$

$$= ||u||^2 + i(\langle v, u \rangle - \langle u, v \rangle) + ||v||^2$$

Similarly,

$$||u + v||^2 = ||u||^2 + (\langle v, u \rangle + \langle u, v \rangle) + ||v||^2$$

Multiplying the first equation by i and adding to the second, we find that

$$i||u + iv||^2 + ||u + v||^2 = (i+1)||u||^2 + 2\langle u, v \rangle + (i+1)||v||^2$$

Solving for  $\langle u, v \rangle$  yields (7).  $\square$ 

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.103 Fall 2013

## 1. Completeness of $L^p$ .

For  $1 \leq p < \infty$ , we define

$$L^p(X,\mu) = \{ f : X \to \mathbf{C} : f \text{ is measurable and } \int_X |f(x)|^p d\mu(x) < \infty \},$$

but we identify two functions as equal if the differ on a set of zero measure. The norm on  $L^p$  is given by

$$||f||_p = \left(\int_X |f(x)|^p d\mu(x)\right)^{1/p}.$$

One case of interest is the case in which X is the natural numbers  $\mathbf{N} = \{1, 2, ...\}$  and  $\mu$  is the counting measure. Then

$$||f||_p = \left(\sum_{k=1}^{\infty} |f(k)|^p\right)^{1/p}.$$

Note that if f and g belong to  $L^p(X, \mu)$ ,

$$\int_X |f(x) + g(x)|^p d\mu \le \int_X \max(|2f(x)|^p, |2g(x)|^p) d\mu \le 2^p \int_X (|f(x)|^p + |g(x)|^p) d\mu < \infty,$$

so that  $f + g \in L^p(X, \mu)$ , and we have

(1) 
$$||f + g||_p^p \le 2^p ||f||_p^p + 2^p ||g||_p^p.$$

Let 1 and let <math>q be the so-called dual exponent, defined by  $\frac{1}{p} + \frac{1}{q} = 1$ . Hölder's inequality (Exercise 7, §3.1, p. 123) says that for every  $f \in L^p(X,\mu)$  and  $g \in L^q(X,\mu)$ ,  $fg \in L^1(X,\mu)$  and

$$||fg||_1 \le ||f||_p ||g||_q$$
.

In particular, if  $\mu$  is the counting measure on N, we have

(2) 
$$\sum_{k=1}^{\infty} |a_k b_k| \le \left(\sum_{k=1}^{\infty} |a_k|^p\right)^{1/p} \left(\sum_{k=1}^{\infty} |b_k|^q\right)^{1/q}$$

In the exercise that followed (Exercise 8) you deduced the triangle inequality

$$||f + g||_p \le ||f||_p + ||g||_p.$$

Thus  $L^p(X,\mu)$  is a normed vector space.

**Theorem 1.** For  $1 \leq p < \infty$ ,  $L^p(X, \mu)$  is a Banach space.

The fact that  $\|\cdot\|_p$  is a norm follows from Exercise 8. Here we show that the space is complete. Consider a Cauchy sequence  $f_n$ , i. e.,

$$||f_n - f_m||_p \to 0$$
 as  $m, n \to \infty$ 

Choose  $n_1 < n_2 < \cdots$  such that

$$||f_n - f_m||_p \le 2^{-2j}$$
, for all  $m, n \ge n_j$ 

Let  $g_j = f_{n_j}$  and  $h_k = g_{k+1} - g_k$ . Note that

$$\int_{X} |h_k|^p \, d\mu = ||h_k||_p^p \le 2^{-2pk}$$

The only difference between this proof of completeness and the one in the text is the way we show that

$$\sum_{k=1}^{\infty} h_k(x)$$

converges almost everywhere. By (2) applied to  $a_k = |h_k(x)| 2^{k/p}$ ,  $b_k = 2^{k/p}$ ,

$$\sum_{k=1}^{\infty} |h_k(x)| = \sum_{k=1}^{\infty} a_k b_k \le \left(\sum_{k=1}^{\infty} 2^k |h_k(x)|^p\right)^{1/p} \left(\sum_{k=1}^{\infty} 2^{-kq/p}\right)^{1/q}$$

Let

$$C = \left(\sum_{k=1}^{\infty} 2^{-kq/p}\right)^{1/q} < \infty$$

It follows from the monotone convergence theorem that

$$\int_{X} \left( \sum_{k=1}^{\infty} |h_k(x)| \right)^p d\mu \le C^p \int_{X} \sum_{k=1}^{\infty} 2^k |h_k(x)|^p d\mu \le C^p \sum_{k=1}^{\infty} 2^k 2^{-2kp} < \infty$$

Therefore,

$$\left(\sum_{k=1}^{\infty} |h_k(x)|\right)^p < \infty$$

for almost every x. For such x, the series  $\sum h_k(x)$  is absolutely convergent, and we can define

$$f(x) = g_1(x) + \sum_{k=1}^{\infty} h_k(x) = \lim_{n \to \infty} g_n(x)$$

Set f(x) = 0 on the exceptional set of measure 0 where the limit does not exist.

The remaining parts of the argument are nearly the same as in the case of  $L^1$ . By Fatou's lemma, for k fixed,

$$2^{-2kp} \ge \liminf_{j \to \infty} \int_X |g_j(x) - g_k(x)|^p \, d\mu \ge \int_X \liminf_{j \to \infty} |g_j(x) - g_k(x)|^p \, d\mu = \int_X |f(x) - g_k(x)|^p \, d\mu$$

In other words,

$$||f - q_k||_p < 2^{-2k}$$

In particular, for k = 1 we have  $f - g_1 \in L^p(X, \mu)$  and hence  $f = (f - g_1) + g_1 \in L^p(X, \mu)$ . Finally, for all  $n \ge n_k$ ,

$$||f_n - f||_p \le ||f_n - g_k||_p + ||g_k - f||_p \le 2^{-2k+1}$$

The space  $L^{\infty}(X,\mu)$  is defined (with the usual equivalence) as the set of measurable functions such that

$$||f||_{\infty} = \operatorname{ess sup}_{X}|f(x)| = \inf_{E} \sup_{x \in (X - E)} |f(x)| < \infty$$

where the infimum is taken over all sets E of measure zero. The expression on the right is known as the essential supremum (supremum ignoring sets of measure zero).

**Exercise.** Show that  $L^{\infty}(X,\mu)$  is a Banach space. (This does not require an accelerated Cauchy sequence. The main issue is to identify the exceptional set of measure zero on which the convergence may fail.)

## 2 Density in $L^p$

The space  $C_0^{\infty}(\mathbf{R}^n)$  denotes all infinitely differentiable functions on  $\mathbf{R}^n$  that are zero outside a compact set.

**Theorem 2.**  $C_0^{\infty}(\mathbf{R}^n)$  is dense in  $L^p(\mathbf{R}^n)$  for  $1 \leq p < \infty$ .

*Proof.* Step 1. Approximation of  $1_{[0,1]}$ . To accomplish this we will find for each  $\epsilon$ ,  $0 < \epsilon < 1/2$ , a function  $h_{\epsilon} \in C_0^{\infty}(\mathbf{R})$  satisfying  $0 \le h(x) \le 1$  for all x,  $h_{\epsilon}(x) = 1$  for  $\epsilon \le x \le 1 - \epsilon$ , and  $h_{\epsilon}(x) = 0$  for all  $x \notin [0,1]$ . It follows that

$$||1_{[0,1]} - h_{\epsilon}||_p^p = \int_{\mathbf{R}} |1_{[0,1]} - h_{\epsilon}(x)|^p dx \le 2\epsilon$$

Start by defining

$$f(x) = \begin{cases} e^{-1/x} & x > 0\\ 0 & x \le 0 \end{cases}$$

Then f is infinitely differentiable and  $f(x) \to 1$  as  $x \to \infty$ . The function g(x) = f(x)f(1-x) belongs to  $C_0^{\infty}(\mathbf{R})$  is zero outside [0,1] and satisfies 0 < g(x) < 1 in 0 < x < 1. Denote

$$c = \int_0^1 g(x) \, dx$$

and define

$$G(x) = \frac{1}{c} \int_0^x g(t) dt.$$

Then  $G \in C^{\infty}(\mathbf{R})$ ,  $0 \le G(x) \le 1$  for all x, G(x) = 0 for all  $x \le 0$ , G(x) = 1 for all  $x \ge 1$ . Finally, let

$$h_{\epsilon}(x) = G(x/\epsilon)G((1-x)/\epsilon).$$

Then  $1_{[\epsilon,1-\epsilon]} \leq h_{\epsilon} \leq 1_{[0,1]}$ , and hence  $||1_{[0,1]} - h_{\epsilon}||_p \leq (2\epsilon)^{1/p} \to 0$  as  $\epsilon \to 0$ .

Step 2. Approximate  $1_R$  for rectangles  $R = I_1 \times I_2 \times \cdots \times I_n$ ,  $I_j = [a_j, b_j]$  by

$$\prod_{j=1}^{n} h_{\epsilon}((x-a_j)/(b_j-a_j))$$

Step 3. Approximate  $1_E$  in case E is a measurable subset of  $\mathbb{R}^n$  of finite measure.

Taking sums of functions from Step 2, one can approximate  $1_R$  by functions in  $C_0^{\infty}(\mathbf{R}^n)$  for any R in the rectangle ring (finite union of rectangles). By Theorem 20 (§1.3, p. 34 of the textbook),  $\mu(E) < \infty$  implies  $E \in \mathcal{M}_F$ . Hence there is a sequence  $R_k$  in the rectangle ring such that

$$\mu(S(E,R_k)) \to 0 \text{ as } k \to \infty$$

where  $S(A, B) = (A - B) \cup (B - A)$ , the set-theoretical symmetric difference. Moreover,  $\|1_E - 1_{R_k}\|_p^p = \mu(S(E, R_k))$ , so  $1_{R_k}$  tends to  $1_E$  in  $L^p(\mathbf{R}^n)$  for any  $p, 1 \le p < \infty$ .

Step 4. From Step 3, we can approximate any finite linear combination of functions of the form  $1_E$  with  $\mu(E) < \infty$  in  $L^p(\mathbf{R}^n)$  norm by functions in  $C_0^{\infty}(\mathbf{R}^n)$ . Finally, consider any measurable  $f: \mathbf{R}^n \to \mathbf{C}$ . Then  $f = u + iv = (u^+ - u^-) + i(v^+ - v^-)$ , and we may apply Theorem 6 (§2.2, page 62) to each of the functions  $u^{\pm}$  and  $v^{\pm}$  to find a sequence of simple functions  $s_k$  such that

$$\lim_{k \to \infty} s_k(x) = f(x), \quad |s_k(x)| \le |f(x)|.$$

Note that if  $0 \le s \le u^+$  and s is simple, then for any c > 0,

$$\mu(\{x \in \mathbf{R}^n : s(x) = c\}) \le \mu(\{x \in \mathbf{R}^n : |f(x)| \ge c\}) \le \frac{1}{c^p} \int_{\mathbf{R}^n} |f|^p \, d\mu < \infty.$$

for  $f \in L^p(\mathbf{R}^n)$ . Thus  $s_k$  is a linear combination of indicator functions  $1_E$  with  $\mu(E) < \infty$ , and hence each  $s_k$  can be approximated, (Thanks to S. M. for pointing out the gap in

the preceding version in which we forgot to check this finiteness property of  $s_k$ .) Finally,  $|s_k(x) - f(x)|^p \le (2|f(x)|)^p$  is a majorant, and the dominated convergence theorem implies

$$\lim_{k \to \infty} \int_{R^n} |f(x) - s_k(x)|^p dx = 0.$$

This concludes the proof that  $C_0^{\infty}(\mathbf{R}^n)$  is dense in  $L^p(\mathbf{R}^n)$ .

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Boolean rings and Boolean algebra

The word ring as it is used measure theory corresponds to the notion of ring used elsewhere in mathematics, but I didn't give the correct correspondence in lecture. I will do so now.

A (commutative) ring is, by definition, a set with two commutative operations, addition and multiplication. The ring is a group under addition (has an additive identity, usually denoted 0, and additive inverses, namely elements -x such that x + (-x) = 0). The multiplication satisfies the associative law and distributes over addition: x(y+z) = xy + xz. If there is a multiplicative identity it is usually denoted by 1, but it need not exist. Even if it does, there is no requirement that multiplicative inverses exist.

If S is a set, then consider the set  $2^S$  of all functions  $x: S \to \{0,1\}$ . We can identify  $2^S$  with the set of all subsets of S as follows. A subset  $A \subset S$  corresponds to the indicator function

$$1_A(s) = \begin{cases} 1 & s \in A \\ 0 & s \notin A \end{cases}$$

Give the set  $\{0,1\}$  the group law of  $\mathbb{Z}/(2\mathbb{Z})$ , namely,

$$1+1=0$$
;  $1+0=0+1=1$ ;  $0+0=0$ ,

and use ordinary multiplication  $(1 \cdot 1 = 1, 0 \cdot 1 = 0 \cdot 0 = 0)$ . Then  $2^S$  is a ring with

$$1_A + 1_B = 1_{S(A,B)}; \quad 1_A 1_B = 1_{A \cap B},$$

where  $S(A, B) = (A - B) \cup (B - A)$ , the symmetric difference. Thus addition is identified with symmetric difference of sets and multiplication with intersection of sets.

A Boolean ring is a ring with the additional property that  $x^2 = x$  for all elements x. Indeed, in the situation above,

$$1_A 1_A = 1_A$$

so that the ring structure on sets described above is Boolean. The formulas for the operations we used in lecture to define rings, namely union and set difference, can be expressed in terms of the Boolean operations as follows.

$$1_{A \cup B} = 1_A + 1_B + 1_A 1_B; \quad 1_{A-B} = 1_A + 1_A 1_B$$

The additive identity is  $1_{\emptyset}$  and  $1_A$  is its own additive inverse. The multiplicative identity is  $1_S$ . Note that we proved that the empty set is always an element of a ring of sets, but the total space S need not be. Likewise, a ring must have an additive identity, but is not required to have a multiplicative identity.

The algebraic structure that encodes the union and intersection (or, equivalently, the "or" and "and" operations) as well as complementation (or, equivalently, negation) is usually called a Boolean algebra. Any Boolean algebra gives rise to a Boolean ring as follows. Define the operation  $\vee$  (same as "or" or "union") on  $\{0,1\}$  as the ones used in a truth table in logic:

$$1 \lor 1 = 1 \lor 0 = 0 \lor 1 = 1; \quad 0 \lor 0 = 0.$$

Similarly, the operation  $\wedge$  has the same rules as the truth table for "and" (or "intersection"):

$$1 \land 1 = 1$$
;  $1 \land 0 = 0 \land 1 = 0 \land 0 = 0$ .

Thus  $\wedge$  is the same as ordinary multiplication of 0 and 1.

Identify  $1_A$  with the set A as above. Then

$$1_{A \cup B} = 1_A \vee 1_B; \quad 1_{A \cap B} = 1_A \wedge 1_B = 1_A 1_B.$$

Multiplication is distributive over the operation  $\vee$ :

$$1_{A \cap (B \cup C)} = 1_A (1_B \vee 1_C) = (1_A 1_B) \vee (1_A 1_C) = 1_{(A \cap B) \cup (A \cap C)}$$

The additive identity for the operation  $\vee$  is  $1_{\emptyset}$  as it was for addition modulo 2 above. But one cannot find additive inverses, and  $2^S$  is not a group under the operation  $\vee$ . In other words, the Boolean algebra is not a ring under the operations  $\wedge$  for multiplication and  $\vee$  for addition. On the other hand, it is a ring under the operations  $\wedge$  for multiplication and symmetric difference for addition. The symmetric difference  $S(A, B) = (A - B) \cup (B - A)$  is expressed in terms of  $\wedge$ ,  $\vee$ , and complementation by

$$1_A + 1_B = 1_{S(A,B)} = (1_A \wedge 1_{B^c}) \vee (1_B \wedge 1_{A^c}),$$

since 
$$S(A, B) = (A \cap B^c) \cup (B \cap A^c)$$
.

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 1 Brownian Motion

**Random Walks**. Let  $S_0 = 0$ ,  $S_n = R_1 + R_2 + \cdots + R_n$ , with  $R_k$  the Rademacher functions. We consider  $S_n$  to be a path with time parameter the discrete variable n. At each step the value of S goes up or down by 1 with equal probability, independent of the other steps.  $S_n$  is known as a  $random\ walk$ .

To find the rescaled, continuum limit of a random walk, define

$$f_n(k/n) = S_k/\sqrt{n}, \quad k \in \mathbb{Z}$$

and for  $k/n \le t \le (k+1)/n$ , define f(t) to be linear. For t = k/n, the variance is

$$\operatorname{Var}(f_n(t)) = \mathbb{E}(S_k^2/n) = \mathbb{E}((R_1 + \dots + R_k)^2/n) = k/n = t$$

The central limit theorem implies that  $f_n(t)$  tends in probability law to a gaussian random variable. In other words,

$$\lim_{n \to \infty} P(a < f_n(t) < b) = \int_a^b \frac{e^{-x^2/2t}}{\sqrt{2\pi t}} \, dx$$

For each n, there is a unique k = k(n,t) such that  $k/n \le t \le (k+1)/n$ , so that  $S_k/\sqrt{n} \le f_n(t) \le S_{k+1}/\sqrt{n}$ . Since both  $S_k/\sqrt{n}$  and  $S_{k+1}/\sqrt{n}$  tend in law to the gaussian with variance t as  $n \to \infty$ , it's not hard to show that  $f_n(t)$  does so as well. More generally, we can describe the probability distribution of the entire path, that is, what happens at many different times.

**Theorem 1** Let  $0 \le t_0 < t_1 < t_2 < \dots < t_m$  and let  $I_1 \times I_2 \times \dots I_m \subset \mathbb{R}^m$  be a rectangle (product of intervals). Let  $\sigma_j > 0$  be such that  $\sigma_j^2 = t_j - t_{j-1}$ . Then

$$\lim_{n \to \infty} P[(f_n(t_1) - f_n(t_0), f_n(t_2) - f_n(t_1), \dots, f_n(t_m) - f_n(t_{m-1})) \in I_1 \times \dots \setminus I_m]$$

$$= \int_{I_1 \times \dots \times I_m} \prod_{j=1}^m g_{\sigma_j}(x_j) \, dx_1 \cdots dx_m$$

*Proof.* If  $k_j = k_j(n)$  is the integer such that  $k_j/n \le t_j < (k_j + 1)/n$ , then

$$f(t_j) - f(t_{j-1}) = X_j + O(1/\sqrt{n})$$
 with  $X_j = (S_{k_j} - S_{k_{j-1}})/\sqrt{n}$ 

For each  $j=1,\ldots,m$ , the central limit theorem implies  $X_j$  tends to a gaussian with mean zero, variance  $\sigma_j^2$ . Moreover, because for different  $j, X_j$  depends on the Rademacher functions  $R_\ell$ ,  $k_{j-1}+1 \leq \ell \leq k_j$ , which do not overlap with the Rademacher functions used to define the other  $X_j$ , these m random variables are independent. Hence the limit of the joint distribution is the product of the individual limits, the appropriate product distribution of gaussians. Therefore, the m variables  $f_n(t_j) - f_n(t_{j-1}) = X_j + O(1/\sqrt{n})$  converge jointly as  $n \to \infty$  to the same limit. This proves Theorem 1.

The rest of this section is devoted to explaining how to describe the limiting paths of the random walk, a continuum stochastic process called *Brownian motion*. Brownian motion is a function

$$B: \Omega \times \mathbb{R}_+ \to \mathbb{R}, \quad (\omega, t) \in \Omega \times \mathbb{R}_+$$

First, a few words about notation. When we display the dependence on  $\omega \in \Omega$ , we will put it into a subscript,  $B_{\omega}(t)$ . The main focus is on  $B_{\omega}$ , as a random function of t. The sample space  $\Omega$  is rarely mentioned in probability theory, and the dependence of B on  $\omega$  is omitted, so that one usually usually writes

$$B(t) = B_{\omega}(t).$$

The idea of trying to define B(t) as a function of a continuous variable t, as opposed to just a discrete time variable n, is in the same spirit as the overall motivation for differential and integral calculus. Continuum formulas are more transparent and capture better the essence of the phenomenon. For example, we will show that for almost every  $\omega$ ,  $B_{\omega}(t)$  is continuous in t. (Although we won't prove anything this precise, it turns out that the Brownian paths are almost surely of the Hölder class  $C^{\alpha}$  for all  $\alpha < 1/2$ , almost surely nowhere differentiable, and almost never  $C^{\alpha}$  for  $\alpha \geq 1/2$ . In higher level courses, one goes on to study so-called stochastic differential equations, in which dB(t) the differential of B(t) plays a role.)

The sample space  $\Omega$  is barely mentioned because we can identify  $\omega \in \Omega$  with  $B_{\omega}$  a continuous function. But there is one remark we need to make about the sigma field  $\mathcal{F}$ .  $\mathcal{F}$  will be defined as the sigma field generated by sets of the form

$$\{\omega \in \Omega : (B_{\omega}(t_1), \dots, B_{\omega}(t_m)) \in I_1 \times \dots \times I_m\}$$

Let  $0 \le t_0 < t_1 < \cdots t_m$ , and let  $R = I_1 \times I_2 \times \cdots \times I_m$ . Our goal is to find  $B_{\omega}(t)$  so that

$$\lim_{n \to \infty} P[(f_n(t_1), \dots, f_n(t_m)) \in R] = P[(B(t_1), \dots, B(t_m)) \in R]$$
 (1)

This uniquely specifies the probability law of B(t) on  $\mathcal{F}$ .

To get a picture of what (1) means, imagine we can simulate as many trials of B(t) as we like on an  $m \times m$  pixel video screen. (This turns out to be easy to carry out using the Fourier series formula for B(t) due to Wiener and any fast Fourier transform package, such

as the ones contained in Maple, Matlab, or Mathematica.) Suppose that  $t_j = j/m$  (pixel width 1/m) and  $I_j$  are chosen from intervals of the form [Ck/m, C(k+1)/m), corresponding to pixel height. The event  $(B(t_1), \ldots, B(t_m)) \in I_1 \times \cdots \times I_m$  specifies the graph to accuracy 1/m, which we can think of as the level of resolution of the pixels. Thus (1) says that the collection of graphs obtained by simulating B(t) look exactly the same as the collection of graphs simulating the functions  $f_n(t)$  (up to some negligible probability for n sufficiently large).

Since B(0) = 0, the knowledge of the increments  $B(t_j) - B(t_{j-1})$  is the same as the knowledge of the values of  $B(t_j)$ . Let  $\sigma_j > 0$ ,  $\sigma_j^2 = t_j - t_{j-1}$ , We can always let  $t_0 = 0$ , so Theorem 1 implies (1) is equivalent to

$$P[(B(t_1) - B(t_0), \dots, B(t_m) - B(t_{m-1})) \in R] = \int_R \prod_{j=1}^m g_{\sigma_j}(x_j) \, dx_1 \cdots dx_m \tag{2}$$

for all  $R = I_1 \times \cdots \times I_m$ 

The main issue is to show that B(t) exists. In around 1920, Norbert Wiener gave a formula for Brownian motion as a random Fourier series. Let  $a_k$ ,  $k = 0, 1, \ldots$ , be independent mean 0, variance 1 Gaussians. Let

$$W(t) = c_0 a_0 t + c_1 \sum_{k=1}^{\infty} a_k \frac{\sin kt}{k}, \quad 0 \le t \le \pi.$$
 (3)

with  $c_0 = \sqrt{1/\pi}$  and  $c_1 = \sqrt{2/\pi}$ . The rest of this section is devoted to proving Wiener's theorem.

**Theorem 2** Let W be given by (3). Then W(0) = 0 and

- a) B(t) = W(t) satisfies (2) (or equivalently (1)) on  $0 \le t \le \pi$ .
- b) W is almost surely continuous in t.

To obtain Brownian motion on all  $t \geq 0$ , take a countable number of independent copies of  $W_n(t)$  and let

$$B(t) = \begin{cases} W_1(t), & 0 \le t \le \pi \\ W_1(\pi) + W_2(t - \pi), & \pi \le t \le 2\pi \\ W_1(\pi) + W_2(\pi) + W_2(t - 2\pi), & 2\pi \le t \le 3\pi \\ \text{etc.} \end{cases}$$

We begin the proof of Theorem 2 with a lemma about gaussian random variables.

**Proposition 1** If  $X_k$ , are independent gaussians with mean 0 and variance  $\sigma_k^2$  with

$$\sum_k \sigma_k^2 < \infty$$

then  $X_1 + X_2 + \cdots$  converges in  $L^2(\Omega)$  to a gaussian random variable with mean zero and variance  $\sigma^2 = \sum_k \sigma_k^2$ .

*Proof.* For finite sums we have

$$\mathbb{E}(e^{-i\xi(X_1+X_2+\dots+X_n)}) = \prod_{k=1}^n \mathbb{E}(e^{-i\xi X_k})$$
$$= \prod_{k=1}^n e^{-\sigma_k^2 \xi^2/2} = e^{-\sum_{k=1}^n \sigma_k^2 \xi^2/2}$$

By the uniqueness of the Fourier transform of measures,  $S = X_1 + \cdots + X_n$  is gaussian with variance  $\sum_{k=1}^{n} \sigma_k^2$ .

For the infinite sum, consider first the partial sums

$$S_n = X_1 + \cdots + X_n$$

For n > m,

$$\mathbb{E}(|S_n - S_m|^2) = \sum_{k=m+1}^n \mathbb{E}(X_k^2) = \sum_{k=m+1}^n \sigma_k^2$$

which tends to zero as  $m \to \infty$ . Therefore,  $S_n$  converges in  $L^2(\Omega)$  to a random variable S.

Denote by  $\rho_n^2 = \sum_{1}^n \sigma_k^2$ . Fix  $\epsilon > 0$ .

$$P(a < S < b) \le P(a - \epsilon < S_n < b + \epsilon) + P(|S - S_n| \ge \epsilon)$$

and

$$P(|S - S_n| \ge \epsilon) = P(|S - S_n|^2 \ge \epsilon^2) \le \frac{1}{\epsilon^2} ||S - S_n||_{L^2(\Omega)}^2 \to 0$$

as  $n \to \infty$ . Therefore, since  $\rho_n \to \sigma$ ,

$$P(a < S < b) \le \lim_{n \to \infty} \int_{a-\epsilon}^{b+\epsilon} g_{\rho_n}(x) dx = \int_{a-\epsilon}^{b+\epsilon} g_{\sigma}(x) dx$$

Since  $\epsilon > 0$  was arbitrary, we have

$$P(a < S < b) \le \int_a^b g_{\sigma}(x) dx$$

A similar argument gives the same lower bound, proving the proposition.

Covariance. The *covariance* of two random variables X and Y is defined as

$$Cov(X, Y) = \mathbb{E}((X - \mathbb{E}X)(Y - \mathbb{E}Y))$$

Note that

$$\operatorname{Cov}\left(\sum_{j} X_{j}, \sum_{k} X_{k}\right) = \sum_{j,k} \operatorname{Cov}\left(X_{j}, X_{k}\right)$$

The polarization method says that to determine the covariance, of a family  $X_1, X_2, \ldots, X_n$  of random variables is suffices to know

$$\operatorname{Var}\left(\sum_{j} a_{j} X_{j}\right) = \sum_{j,k} a_{j} a_{k} \operatorname{Cov}\left(X_{j}, X_{k}\right)$$

for all choices of  $a_i$ .

The mean and variance determine the distribution of a single gaussian random variable. The analogous statement for several variables involves the *covariance matrix* Cov  $(X_j, X_k)$ . We will formulate it as follows.

**Lemma 1** Let  $X = (X_1, ..., X_m)$  be independent gaussian random variables with mean zero. Let  $A = (a_{ik})$  be an invertible (real-valued) matrix and define  $Y = (Y_1, ..., Y_m)$  by

$$Y_j = \sum_{k=1}^m a_{jk} X_k.$$

Then for every  $a = (a_1, \ldots, a_m) \in \mathbb{R}^m$ ,

$$a \cdot Y = \sum_{j=1}^{m} a_j Y_j$$

is a gaussian random variable with mean 0. Conversely, if  $Z = (Z_1, \ldots, Z_m)$  are random variables such that for every  $a = (a_1, \ldots, a_m)$ ,

$$a \cdot Z = \sum_{j=1}^{m} a_j Z_j$$

is a gaussian random variable with mean 0 and covariances coincide with those of Y,

$$\mathbb{E}(Z_i Z_k) = \mathbb{E}(Y_i Y_k)$$

then the joint distribution of  $Z = (Z_1, \ldots, Z_m)$  is the same as that of Y. In other words,

$$P(Z \in E) = P(Y \in E)$$
 for all Borel sets  $E \subset \mathbb{R}^m$ 

Moreover,  $A^{-1}Z$  has the same probability distribution as X.

*Proof.* Denote by V the covariance matrix of  $X = (X_1, \ldots, X_m)$ , that is  $v_{jk} = \mathbb{E}(X_j X_k)$ . Then V is diagonal with entries  $\sigma_1^2, \ldots, \sigma_m^2$  (the variance of  $X_1, \ldots, X_m$ , respectively) along the diagonal. Denote the covariance matrix of Y by  $C = (c_{jk})$ , that is,  $c_{jk} = \text{Cov}(Y_j, Y_k) = \mathbb{E}(Y_j Y_k)$ . Then

$$c_{jk} = \mathbb{E}(Y_j Y_k) = \sum_{\ell} a_{j\ell} a_{k\ell} \sigma_{\ell}^2 \implies C = (c_{jk}) = AVA^T$$

The random variable  $a \cdot Y$  is a linear combination of the independent gaussians  $X_j$ . Therefore by Proposition 1,  $a \cdot Y$  is a gaussian random variable with mean zero. The variance of  $a \cdot Y$  is

$$v(a) = \mathbb{E}((a \cdot Y)^2) = \sum_{j,k=1}^{m} a_j a_k c_{jk}$$

The mean and variance specify the distribution of  $a \cdot Y$  completely, and it follows from the formula for the Fourier transform of the gaussian that

$$\mathbb{E}\left(e^{-ita\cdot Y}\right) = e^{-v(a)t^2/2}$$

Specializing to t = 1 and  $a = \xi$  we find the Fourier transform of  $\mu_Y$ , the joint probability distribution of Y on  $\mathbb{R}^m$ , is

$$\int_{\mathbb{D}^m} e^{-i\xi \cdot x} d\mu_Y(x) = \mathbb{E}\left(e^{-i\xi \cdot Y}\right) = e^{-v(\xi)/2}$$

If Z has the property that  $a \cdot Z$  is gaussian with mean zero and the variances  $\mathbb{E}(Z_j Z_k) = \mathbb{E}(Y_j Y_k) = c_{jk}$ , then the same reasoning leads to the conclusion that the Fourier transform on  $\mathbb{R}^m$  of  $\mu_Z$  the joint probability distribution of Z is also equal to  $e^{-v(\xi)/2}$ . Therefore, by uniqueness of the Fourier transform for measures,  $\mu_Y = \mu_Z$ . This concludes the proof.

We make use of Lemma 1 in a special case, in order to characterize B(t).

**Proposition 2** Suppose that B(t) is such that B(0) = 0. Then B satisfies property (2) if and only if

- a)  $\sum_{j=1}^{m} \xi_j B(t_j)$  is a Gaussian random variable with mean 0.
- b)  $\mathbb{E}(B(s)B(t)) = s \wedge t$ ,  $(s \wedge t = \min(s, t))$ .

*Proof.* Assume that B satisfies (2). To prove (a), note that for any  $\xi_j$  one can find  $b_j$  such that

$$\sum_{j} \xi_{j} B(t_{j}) = \xi_{1}(B(t_{1}) - B(0)) + \sum_{\ell} b_{\ell}(B(t_{\ell+1}) - B(t_{\ell}))$$

The latter sum is a sum of independent gaussians, so the fact that the sum is gaussian follows from Proposition 1. To prove (b), note first that (2) implies B(s) is gaussian with mean 0 and variance s, i. e.,  $\mathbb{E}(B(s)^2) = s$ . More generally, for  $s \leq t$ ,

$$\mathbb{E}(B(s)B(t)) = \mathbb{E}(B(s)(B(t) - B(s))) + \mathbb{E}(B(s)^{2}) = 0 + \mathbb{E}(B(s)^{2}) = s,$$

because independence gives  $\mathbb{E}(B(s)(B(t) - B(s))) = \mathbb{E}(B(s))\mathbb{E}((B(t) - B(s))) = 0$ .

Conversely, suppose C(t) satisfies a) and b) and C(0) = 0. Define B by B(0) = 0 and (2), then we have just shown that  $X = (B(t_1) - B(t_0), \ldots, B(t_m) - B(t_{m-1}))$  is a sequence of independent gaussians of mean zero, and  $Y = (B(t_1), \ldots, B(t_m))$  has correlation matrix  $\mathbb{E}(B(t_j)B(t_k)) = t_j \wedge t_k$ . Therefore  $Z = (C(t_1), \ldots, C(t_m))$  satisfies the hypotheses of Lemma 1 with the same correlation matrix as Y, and by Lemma 1, Z satisfies (2).

We are now ready to prove part (a) of Theorem 2. Let  $0 \le t_0 < t_1 < \cdots < t_m \le \pi$ . The fact that

$$\sum_{j=1}^{m} \xi_j W(t_j)$$

is gaussian of mean zero follows from Proposition 1. The fact that W(0) = 0 is obvious. According to Proposition 2 it remains to show that for  $0 \le s \le t \le \pi$ ,

$$\mathbb{E}(W(s)W(t)) = s \wedge t$$

We could do this all at once, but we carry out a slightly simpler calculation  $\mathbb{E}(W(t)^2) = t$  first.

Proposition 1 implies W(t) is gaussian with mean zero and variance

$$\mathbb{E}(W(t)^2) = c_0^2 t^2 + c_1^2 \sum_{k=1}^{\infty} \frac{\sin^2(kt)}{k^2}$$

The case  $t = \pi$  identifies  $c_0$ :

$$\pi = c_0^2 \pi^2 \implies c_0 = 1/\sqrt{\pi}$$

Denote

$$u(t) = \sum_{k=1}^{\infty} \frac{\sin^2(kt)}{k^2}$$

Then

$$u'(t) = \sum_{k=1}^{\infty} \frac{2k\sin(kt)\cos(kt)}{k^2} = \sum_{k=1}^{\infty} \frac{\sin(2kt)}{k}$$

and

$$u''(t) \sim \sum_{k=1}^{\infty} \frac{2k\cos(2kt)}{k} = 2\sum_{k=1}^{\infty} \cos(2kt) = -1 + \sum_{k \in \mathbb{Z}} e^{2ikt}$$

The last series is periodic of period  $\pi$ . The standard delta function of period  $\pi$  has Fourier coefficients

$$\frac{1}{\pi} \int_{-\pi/2}^{\pi/2} \delta(t) e^{-2int} \, dt = 1/\pi$$

Thus

$$u''(t) = -1 + \pi \sum_{n \in \mathbb{Z}} \delta(t - n\pi)$$

The function u'(t) is odd and we can find its formula by integrating u''(t). We get

$$u'(t) = \begin{cases} \pi/2 - t & 0 < t < \pi \\ -\pi/2 - t & -\pi < t < 0 \end{cases}$$

One way to check your arithmetic is to evaluate u'(t) places where we know what to expect. For instance,

$$u'(\pm \pi/2) = \sum_{k=1}^{\infty} \frac{\sin(\pm 2k\pi/2)}{k} = 0$$

and the formula above gives  $u'(\pi/2) = \pi/2 - \pi/2 = 0$  and  $u'(-\pi/2) = -\pi/2 - (-\pi/2) = 0$ . (You can also confirm the periodicity of period  $\pi$ .)

Next integrate u'(t) to get u(t), which is even and satisfies u(0) = 0. Thus,

$$u(t) = \begin{cases} (\pi/2)t - t^2/2 & 0 \le t \le \pi \\ -(\pi/2)t - t^2/2 & -\pi \le t \le 0 \end{cases}$$

You can check your arithmetic in this case by confirming that u(t) is continuous and periodic of period  $2\pi$  so that the values at  $t = \pm \pi$  must agree. (The series is absolutely convergent, so u must be continuous everywhere.)

Now inserting the values of u(t) into the formula for the variance we have for  $0 \le t \le \pi$ ,

$$\mathbb{E}(W(t)^2) = (1/\pi)t^2 + c_1^2[(\pi/2)t - t^2/2] = t$$

provided that  $c_1 = \sqrt{2/\pi}$ .

Now let's do the full calculation, which is very similar.

$$\mathbb{E}(W(s)W(t)) = c_0^2 st + c_1^2 \sum_{k=1}^{\infty} \frac{\sin(ks)\sin(kt)}{k^2}$$

Since  $\sin A \sin B = \frac{1}{2} [\cos(A - B) - \cos(A + B)],$ 

$$\sum_{k=1}^{\infty} \frac{\sin(ks)\sin(kt)}{k^2} = \frac{1}{2} \sum_{k=1}^{\infty} \frac{\cos(k(s-t)) - \cos(k(s+t))}{k^2} = \frac{1}{4} [v(s-t) - v(s+t)]$$

with

$$v(t) = 2\sum_{k=1}^{\infty} \frac{\cos(kt)}{k^2}$$

We evaluate v(t) by a similar procedure to the one above.

$$v'(t) = -2\sum_{k=1}^{\infty} \frac{\sin(kt)}{k}$$

$$v''(t) \sim -2\sum_{k=1}^{\infty} \cos kt = 1 - \sum_{k \in \mathbb{Z}} e^{ikt}$$

This time v'' has period  $2\pi$  and

$$1 - \sum_{k \in \mathbb{Z}} e^{ikt} = 1 - 2\pi \sum_{n \in \mathbb{Z}} \delta(t - 2\pi n)$$

Integrating, the odd function v'(t) is given by

$$v'(t) = \begin{cases} -\pi + t & 0 < t < \pi \\ \pi + t & -\pi < t < 0 \end{cases}$$

Integrating a second time,

$$v(t) - v(0) = -\pi |t| + t^2/2, \quad |t| \le \pi$$

We could calculate v(0), but we only need difference v(s-t) - v(s+t), so the value is not relevant. If we extend v(t) - v(0) as a periodic function of period  $2\pi$ , then we get

$$v(t) - v(0) = -\pi t + t^2/2, \quad 0 \le t \le 2\pi$$

(We need this range in order to evaluate v(s+t).)

Substituting the formula for v(t) - v(0), we obtain for  $0 \le s \le t \le \pi$ ,

$$\mathbb{E}(W(s)W(t)) = c_0^2 st + \frac{1}{4}c_1^2[v(s-t) - v(s+t)]$$

$$= \frac{st}{\pi} + \frac{1}{2\pi}[-\pi(t-s) + (t-s)^2/2 - (-\pi(s+t) + (s+t)^2/2)]$$

$$= s$$

This finishes the proof of part (a) of Theorem 2.

To get started with part (b) we need some lemmas.

**Lemma 2** If  $a_k$  are mean zero variance 1 gaussians, then

$$\mathbb{E}(|a_{i_1}a_{i_2}a_{i_3}a_{i_4}|) \le \mathbb{E}(|a_1|^4) = 3 < \infty$$

*Proof.* All we really care about is that this is finite, which is easy because all the distributions involved are rapidly decreasing. But we can also give an explicit bound as follows. For equidistributed random variables, applying the Schwarz inequality twice,

$$\mathbb{E}(X_1X_2X_3X_4) \leq [\mathbb{E}(|X_1X_2|^2)]^{1/2} [\mathbb{E}(|X_3X_4|^2)]^{1/2} \leq \prod_{j=1}^4 [\mathbb{E}(|X_j|^4)^{1/4} = \mathbb{E}(|X_1|^4)$$

One can also get this by applying a version of Hölder's inequality with several factors.

$$\mathbb{E}(|a_j a_{j'} a_k a_{k'}|) \le \mathbb{E}(|a_1|^4) < \infty$$

 $\mathbb{E}(a_1^4) = 3$  is calculated as follows. (We only need finiteness, but this calculation is a nice trick to know.) Change of variables of the formula saying the the standard gaussian has integral 1 to get

$$\int_{-\infty}^{\infty} \frac{e^{-\lambda x^2/2}}{\sqrt{2\pi}} dx = \lambda^{-1/2}.$$

Differentiate with respect to  $\lambda$  to obtain

$$\int_{-\infty}^{\infty} (-x^2/2) \frac{e^{-\lambda x^2/2}}{\sqrt{2\pi}} dx = -(1/2)\lambda^{-3/2}$$

Differentiate a second time to get

$$\int_{-\infty}^{\infty} (-x^2/2)^2 \frac{e^{-\lambda x^2/2}}{\sqrt{2\pi}} dx = (1/2)(3/2)\lambda^{-5/2}$$

Thus,  $\mathbb{E}(a_1^2) = 1$ ,  $\mathbb{E}(a_1^4) = 3$  and, more generally,  $\mathbb{E}((a_1)^{2n}) = (2n-1)(2n-3)\cdots 3\cdot 1$ .

**Lemma 3** For  $m \ge 1$  and  $0 \le \beta \le 2$ ,

$$R_{\beta}(m) = \int_{0}^{1} r^{m} (1-r)^{\beta} dr \leq 100 m^{-1-\beta}$$

*Proof.* This integral can be evaluated in terms of what is known as Euler's beta integral. The answer is a product of gamma functions and the asymptotics are easy to read off from Stirling's formula. We won't rely on any of that, but rather prove the upper bound directly.

For 
$$1 - (k+1)/m \le r \le 1 - k/m$$
,  

$$r^m (1-r)^{\beta} < (1 - k/m)^m [(k+1)/m]^{\beta} < e^{-k} [(k+1)/m]^{\beta}$$

Therefore,

$$\int_0^1 r^m (1-r)^\beta dr \le \frac{1}{m} \sum_{k=0}^{m-1} e^{-k} [(k+1)/m]^\beta$$

$$= m^{-1-\beta} \sum_{k=0}^{m-1} (k+1)^\beta e^{-k}$$

$$\le m^{-1-\beta} \int_0^\infty (x+2)^2 e^{-x} dx \le 10m^{-1-\beta}$$

Let

$$F(z) = \sum_{k=1}^{\infty} a_k z^k / k$$

with  $a_k$  independent gaussians with mean zero and variance 1. Note that

$$B(t) = c_0 a_0 t + c_1 \sum_{k=1}^{\infty} a_k \frac{\sin(kt)}{k} = c_0 a_0 t + c_1 \operatorname{Im} F(e^{it})$$

In order to show that B(t) is almost surely continuous, it suffices to show the same for  $F(e^{it})$ . This is accomplished by estimating F(z) in |z| < 1. Note that

$$F_x(z) = \frac{\partial}{\partial x} F(z) = \sum_{j=0}^{\infty} a_{j+1} z^j$$

since for z=x+iy,  $(\partial/\partial x)z=1$ . Moreover, since  $(\partial/\partial y)z=i$ , we also have  $F_y=-iF_x$  and

$$\frac{1}{2}|\nabla F|^2 = |F_x|^2 = \left|\sum_{j=0}^{\infty} a_{j+1}z^j\right|^2 = \sum_{j,j'=0}^{\infty} a_{j+1}a_{j'+1}z^j\bar{z}^{j'}$$

**Lemma 4** For any  $\beta > 1$ ,

$$\mathbb{E} \int_{0}^{2\pi} \int_{0}^{1} |\nabla F(re^{it})|^{4} (1-r)^{\beta} r \, dr \, dt < \infty,$$

and, consequently

$$\int_0^{2\pi} \int_0^1 |\nabla F(re^{it})|^4 (1-r)^\beta r \, dr \, dt < \infty,$$

almost surely.

*Proof.* Think of the expectation as a triple integral (over  $\omega \in \Omega$ , the probability sample) and r and t. The monotone convergence theorem implies

$$\mathbb{E} \int_0^{2\pi} \int_0^1 |\nabla F(re^{it})|^4 (1-r)^{\beta} r \, dr \, dt = \lim_{r_0 \to 1^-} \mathbb{E} \int_0^{2\pi} \int_0^{r_0} |\nabla F(re^{it})|^4 (1-r)^{\beta} r \, dr \, dt$$

Therefore it suffices to bound the integral restricted to  $0 \le r \le r_0 < 1$ , uniformly as  $r_0 \to 1$ .

Next, apply Fubini's theorem (justified subsequently)

$$\mathbb{E} \int_{0}^{2\pi} \int_{0}^{r_{0}} |\nabla F(re^{it})|^{4} (1-r)^{\beta} r \, dr \, dt$$

$$= \mathbb{E} \int_{0}^{2\pi} \int_{0}^{r_{0}} \sum_{j,j',k,k'=0}^{\infty} a_{j} a_{j'} a_{k} a_{k'} r^{j+j'+k+k'} e^{i(j-j'+k-k')t} (1-r)^{\beta} r \, dr \, dt$$

$$= \int_{0}^{2\pi} \int_{0}^{r_{0}} \sum_{j,j',k,k'=0}^{\infty} \mathbb{E}(a_{j} a_{j'} a_{k} a_{k'}) r^{j+j'+k+k'} e^{i(j-j'+k-k')t} (1-r)^{\beta} r \, dr \, dt$$

$$= 4\pi \int_{0}^{2\pi} \int_{0}^{r_{0}} \sum_{j,k=0}^{\infty} \mathbb{E}(a_{j}^{2} a_{k}^{2}) r^{2j+2k+1} (1-r)^{\beta} \, dr$$

$$\leq 12\pi \int_{0}^{1} \sum_{j,k=0}^{\infty} r^{2j+2k+1} (1-r)^{\beta} \, dr$$

$$= 12\pi \sum_{j,k=0}^{\infty} R_{\beta} (2j+2k+1)$$

$$\leq C \sum_{j,k=0}^{\infty} \frac{1}{(2j+2k+1)^{1+\beta}} \approx \int_{x \in \mathbb{R}^{2}} \frac{dx}{(1+|x|)^{1+\beta}} < \infty$$

provided  $\beta > 1$ , so that the exponent  $1 + \beta > 2$ . We need to justify Fubini's theorem so as to bring the expectation inside the integrals and the sum. It is in order to justify this step that the integral was restricted to  $0 \le r \le r_0$ . In fact,

$$\int_0^{2\pi} \int_0^{r_0} \sum_{j,j',k,k'=0}^{\infty} \mathbb{E} |a_j a_{j'} a_k a_{k'} r^{j+j'+k+k'} e^{i(j-j'+k-k')t} | (1-r)^{\beta} r \, dr \, dt < \infty$$

By Lemma 2,  $\mathbb{E}(|a_j a_{j'} a_k a_{k'}|) \leq 3$ . Moreover,

$$\int_0^{2\pi} \int_0^{r_0} \sum_{j,j',k,k'=0}^{\infty} r^{j+j'+k+k'+1} 3(1-r)^{\beta} dr dt \le 6\pi \sum_{j,j',k,k'=0}^{\infty} r_0^{j+j'+k+k'}$$

$$= \frac{6\pi}{(1-r_0)^4} < \infty$$

For the next step we need the mean value property for harmonic functions. If u is harmonic in |z| < 1, and continuous on  $|z| \le 1$ , then for  $0 \le r < 1$ ,

$$u(re^{it}) = \sum_{n \in \mathbb{Z}} a_n r^{|n|} e^{int}$$

Integrating in t,

$$\frac{1}{2\pi} \int_{0}^{2\pi} u(re^{it}) dt = a_0 = u(0)$$

Now integrating with respect to r on  $0 \le r \le \rho \le 1$ ,

$$\frac{1}{2\pi} \int_0^{2\pi} \int_0^{\rho} u(re^{it}) \, rdr \, dt = \int_0^{\rho} u(0) \, rdr = u(0)\rho^2/2$$

Thus

$$u(0) = \frac{1}{\pi \rho^2} \int_0^{\rho} \int_0^{2\pi} u(re^{it}) \, r dr \, dt = \frac{1}{\pi \rho^2} \int_{|z| \le \rho} u(z) \, dx dy$$

where z = x + iy. A similar argument (or a change of variable) shows that if u is harmonic in  $|z - z_0| \le \rho$ , then

$$u(z_0) = \frac{1}{\pi \rho^2} \int_{|z-z_0| \le \rho} u(z) \, dx dy \qquad \text{(Mean value property)} \tag{4}$$

We now apply (4) to  $\nabla F$ . Almost surely,

$$C_* = \int_0^{2\pi} \int_0^1 |\nabla F(re^{it})|^4 (1-r)^\beta r \, dr \, dt < \infty$$

Let  $\alpha = 1 - (2 + \beta)/4$ . For F satisfying the bound above, we will show that there is a constant C depending on  $C_* = C_*(F)$  such that for all z in the unit disk,

$$|\nabla F(z)| \le C(1-|z|)^{-1+\alpha} \tag{5}$$

We will then deduce Hölder continuity with exponent  $\alpha$ . Since  $\beta$  is any real number greater than 1, we see that the Hölder exponent of W(t) at least  $\alpha$  for any  $\alpha < 1/4$ . (Estimates using higher powers than  $|\nabla F|^4$  and higher moments of the gaussian coefficients  $a_k(\omega)$  can be used to show that W is Hölder continuous for any exponent  $\alpha < 1/2$ .)

Let  $|z_0| = r_0$ , and let  $1 - r_0 = 2\rho$ . Then

$$|\nabla F(z_0)| \le \frac{1}{\pi \rho^2} \int_{|z-z_0| \le \rho} |\nabla F(z)| \, dx dy \le \left(\frac{1}{\pi \rho^2} \int_{|z-z_0| \le \rho} |\nabla F(z)|^4 \, dx dy\right)^{1/4}$$

On the disk  $|z - z_0| \le \rho$ ,  $|z| = r \le 1 - \rho$ . Therefore,

$$\int_{|z-z_0| < \rho} |\nabla F(z)|^4 \, dx dy \le 10 \rho^{-\beta} C_*$$

It follows that

$$|\nabla F(z_0)| \le (10C_* \rho^{-2-\beta})^{1/4}$$

which is the same as (5).

**Lemma 5** If F satisfies (5) on  $|z| \leq 1$ , for some  $\alpha$ ,  $0 < \alpha \leq 1$ , then  $F(e^{it})$  is Hölder continuous with exponent  $\alpha$ , that is,

$$|F(e^{t_1}) - F(e^{it_2})| \le C|t_1 - t_2|^{\alpha}$$

*Proof.* Given any two points  $t_1$  and  $t_2$  such that  $t_2 - t_2 = \rho$ . Consider  $1 - r_0 = \rho$  and the line segment  $L_1$  from  $e^{it_1}$  to  $r_0e^{it_1}$ ,  $L_2$  is the circular arc of length less than  $\rho$  along  $|z| = r_0$  from  $r_0e^{it_1}$  to  $r_0e^{it_2}$ , and  $L_3$  is the segment from  $r_0e^{it_2}$  to  $e^{it_2}$ . The integral of  $|\nabla F|$  on  $L_1$  is at most

$$C \int_0^{\rho} s^{-1+\alpha} ds = (C/\alpha)\rho^{\alpha}$$

and similarly on  $L_3$ . The integral on the circular arc  $L_2$  is at most its length of the arc times the bound on  $|\nabla F|$  along that arc, namely  $\rho O(\rho^{-1+\alpha}) = O(\rho^{\alpha})$ . Thus

$$|F(e^{it_2}) - F(e^{it_1})| \le C\rho^{\alpha}$$

MIT OpenCourseWare http://ocw.mit.edu

18.103 Fourier Analysis Fall 2013

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.
