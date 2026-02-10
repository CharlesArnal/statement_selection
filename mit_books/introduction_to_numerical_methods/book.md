## Square Roots via Newton's Method

S. G. Johnson, MIT Course 18.335

February 4, 2015

### 1 Overview

**Numerical methods** can be distinguished from other branches of analysis and computer science by three characteristics:

- They work with arbitrary **real** numbers (and vector spaces/extensions thereof): the desired results are not restricted to integers or exact rationals (although in practice we only ever compute *rational approximations* of irrational results).
- Like in computer science (= math + time = math + money), we are concerned not only with existence and correctness of the solutions (as in analysis), but with the **time** (and other computational resources, e.g. memory) required to compute the result.
- We are also concerned with **accuracy** of the results, because in practice we only ever have **approximate** answers:
  - Some algorithms may be intrinsically approximate—like the Newton's-method example shown below, they converge towards the desired result but never reach it in a finite number of steps. How fast they converge is a key question.
  - Arithmetic with real numbers is approximate on a computer, because we approximate the set  $\mathbb{R}$  of real numbers by the set  $\mathbb{F}$  of **floating-point numbers**, and the result of every elementary operation  $(+,-,\times,\div)$  is **rounded** to the nearest element of  $\mathbb{F}$ . We need to understand  $\mathbb{F}$  and how accumulation of these rounding errors affects different algorithms.

## 2 Square roots

A classic algorithm that illustrates many of these concerns is "Newton's" method to compute square roots  $x = \sqrt{a}$  for a > 0, i.e. to solve  $x^2 = a$ . The algorithm starts with some guess  $x_1 > 0$  and computes the sequence of improved guesses

$$x_{n+1} = \frac{1}{2} \left( x_n + \frac{a}{x_n} \right).$$

The intuition is very simple: if  $x_n$  is too big  $(> \sqrt{a})$ , then  $a/x_n$  will be too small  $(< \sqrt{a})$ , and so their arithmetic mean  $x_{n+1}$  will be closer to  $\sqrt{a}$ . It turns out that this algorithm is very old, dating at least to the ancient Babylonians circa 1000 BCE. In modern times, this was seen to

<sup>&</sup>lt;sup>1</sup>See e.g. Boyer, A History of Mathematics, ch. 3; the Babylonians used base 60 and a famous tablet (YBC 7289) shows  $\sqrt{2}$  to about six decimal digits.

be equivalent to Newton's method to find a root of  $f(x) = x^2 - a$ . Recall that Newton's method finds an approximate root of f(x) = 0 from a guess  $x_n$  by approximating f(x) as its tangent line  $f(x_n) + f'(x_n)(x - x_n)$ , leading to an improved guess  $x_{n+1}$  from the root of the tangent:

$$x_{n+1} = x_n - \frac{f(x_n)}{f'(x_n)},$$

and for  $f(x) = x^2 - a$  this yields the Babylonian formula above.

### 2.1 Convergence proof

A classic analysis text (Rudin, *Principles of Mathematical Analysis*) approaches the proof of convergence of this algorithm as follows: we prove that the sequence converges monotonically and is bounded, and hence it has a limit; we then easily see that the limit is  $\sqrt{a}$ . In particular:

- 1. Suppose  $x_n > \sqrt{a}$ , then it follows  $\sqrt{a} < x_{n+1} < x_n$ :
  - (a)  $x_{n+1} x_n = \frac{1}{2} \left( \frac{a}{x_n} x_n \right) = \frac{a x_n^2}{2x_n} < 0.$
  - (b)  $x_{n+1}^2 a = \frac{1}{4}(x_n^2 + 2a + \frac{a^2}{x_n^2}) a = \frac{1}{4}(x_n^2 2a + \frac{a^2}{x_n^2}) = \frac{1}{4}(x_n \frac{a}{x_n})^2 = \frac{(x_n^2 a)^2}{4x_n^2} > 0$  (regardless of whether  $x_n > \sqrt{a}$ ).
- 2. A monotonic-decreasing sequence that is bounded below converges (Rudin theorem 3.14). If  $x_1 < \sqrt{a}$ , the second property above means that  $x_2 > \sqrt{a}$ ; then for n > 2 it is monotonically decreasing and bounded below by  $\sqrt{a}$ .
- 3. The limit  $x = \lim_{n \to \infty} x_n$  satisfies  $x = \frac{1}{2}(x + \frac{a}{x})$ , which is easily solved to show that  $x^2 = a$ .

However, this proof by itself tells us nothing about how fast the sequence converges

#### 2.2 Convergence example

Using the accompanying Julia notebook, we will apply this method to compute the most famous root of all,  $\sqrt{2}$ . (Supposedly, the Greek who discovered that  $\sqrt{2}$  is irrational was thrown off a cliff by his Pythagorean colleagues.). As a starting guess, we will use  $x_1 = 1$ , producing the following sequence when computed with about 60 digits of accuracy, where the correct digits are shown in boldface:

- 1
- 1.5
- 1.41 666666666666666666666666666666666666
- $\textbf{1.41421} \\ 56862745098039215686274509803921568627450980392156862745$
- **1.41421356237**46899106262955788901349101165596221157440445849057
- **1.41421356237309504880168**96235025302436149819257761974284982890
- 1.4142135623730950488016887242096980785696718753772340015610125
- 1.4142135623730950488016887242096980785696718753769480731766796

Looking carefully, we see that the **number of accurate digits approximately doubles on each iteration**. This fantastic convergence rate means that we only need seven Newton iterations to obtain more than 60 accurate digits—the accuracy is quickly limited only by the precision of our floating-point numbers, a topic we will discuss in more detail later on.

#### 2.3 Convergence rate

Let us analyze the convergence rate quantitatively—given a small error  $\delta_n$  on the *n*-th iteration, we will determine how much smaller the error  $\delta_{n+1}$  is in the next iteration.

In particular, let us define  $x_n = x(1 + \delta_n)$ , where  $x = \sqrt{a}$  is the exact solution. This corresponds to defining  $|\delta_n|$  as the **relative error**:

$$|\delta_n| = \frac{|x_n - x|}{|x|},$$

also called the **fractional error** (the error as a fraction of the exact value). Relative error is typically the most useful way to quantify the error because it is a *dimensionless* quantity (independent of the units or overal scalling of x). The logarithm  $(-\log_{10} \delta_n)$  of the relative error is roughly the number of **accurate significant digits** in the answer  $x_n$ .

We can plug this definition of  $x_n$  (and  $x_{n+1}$ ) in terms of  $\delta_n$  (and  $\delta_{n+1}$ ) into our Newton iteration formula to solve for the iteration of  $\delta_n$ , using the fact that a/x = x to divide both sides by x:

$$1 + \delta_{n+1} = \frac{1}{2} \left( 1 + \delta_n + \frac{1}{1 + \delta_n} \right) = \frac{1}{2} \left[ 1 + \delta_n + 1 - \delta_n + \delta_n^2 + O(\delta_n^3) \right],$$

where we have Taylor-expanded  $(1-\delta_n)^{-1}$ . The  $O(\delta_n^3)$  means roughly "terms of order  $\delta_n^3$  or smaller;" we will define it more precisely later on. Because the sequence converges, we are entitled to assume that  $|\delta_n|^3 \ll 1$  for sufficiently large n, and so the  $\delta_n^3$  and higher-order terms are eventually negligible compared to  $\delta_n^2$ . We obtain:

$$\delta_{n+1} = \frac{\delta_n^2}{2} + O(\delta_n^3),$$

which means the **error roughly squares** (and halves) on each iteration once we are close to the solution. Squaring the relative error corresponds precisely to doubling the number of significant digits, and hence explains the phenomenon above. This is known as **quadratic convergence** (not to be confused with "second-order" convergence, which unfortunately refers to an entirely different concept).

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

# 18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# Lecture 2: Floating-Point Arithmetic, The IEEE Standard

MIT 18.335J / 6.337J

Introduction to Numerical Methods

Per-Olof Persson

### **Floating Point Formats**

Scientific notation:

Floating point representation

$$\pm (d_0 + d_1 \beta^{-1} + \dots + d_{p-1} \beta^{-(p-1)}) \beta^e, \quad 0 \le d_i < \beta$$

with base  $\beta$  and precision p

- $\bullet$  Exponent range  $[e_{\min}, e_{\max}]$
- Normalized if  $d_0 \neq 0$  (use  $e = e_{\min} 1$  to represent 0)

# **Floating Point Numbers**

- The gaps between adjacent numbers scale with the size of the numbers
- Relative resolution given by *machine epsilon*,  $\epsilon_{\text{machine}} = .5\beta^{1-p}$
- $\bullet$  For all x, there exists a floating point x' such that  $|x-x'| \leq \epsilon_{\mathrm{machine}}|x|$
- Example:  $\beta = 2, p = 3, e_{\min} = -1, e_{\max} = 2$

# **Special Quantities**

- $\bullet$   $\pm \infty$  is returned when an operation overflows
- $x/\pm\infty=0$  for any number x,  $x/0=\pm\infty$  for any nonzero number x
- Operations with infinity are defined as limits, e.g.

$$4 - \infty = \lim_{x \to \infty} 4 - x = -\infty$$

- NaN (Not a Number) is returned when the an operation has no well-defined finite or infinite result
- Examples:  $\infty \infty$ ,  $\infty/\infty$ , 0/0,  $\sqrt{-1}$ ,  $\mathrm{NaN} \odot x$

#### **Denormalized Numbers**

- $\bullet$  With normalized significand there is a "gap" between 0 and  $\beta^{e_{\min}}$
- This can result in x-y=0 even though x=y, and code fragments like if x=y then z=1/(x-y) might break
- $\bullet$  Solution: Allow non-normalized significand when the exponent is  $e_{\min}$
- This gradual underflow garantees that

$$x = y \iff x - y = 0$$

## **IEEE Single Precision**

• 1 sign bit, 8 exponent bits, 23 significand bits:

| 0 | 00000000 | 000000000000000000000000000000000000000 |
|---|----------|-----------------------------------------|
| S | E        | M                                       |

• Represented number:

$$(-1)^S \times 1.M \times 2^{E-127}$$

• Special cases:

|                  | E=0 | 0 < E < 255      | E = 255     |
|------------------|-----|------------------|-------------|
| M = 0            | ±0  | Powers of 2      | $\pm\infty$ |
| M=0 Denormalized |     | Ordinary numbers | NaN         |

# **IEEE Single Precision, Examples**

| S | Е        | M                                       | Quantity                                     |
|---|----------|-----------------------------------------|----------------------------------------------|
| 0 | 11111111 | 00000100000000000000000                 | NaN                                          |
| 1 | 11111111 | 001000100010010101010                   | NaN                                          |
| 0 | 11111111 | 000000000000000000000000000000000000000 | $\infty$                                     |
| 0 | 10000001 | 10100000000000000000000                 | $+1 \cdot 2^{129-127} \cdot 1.101 = 6.5$     |
| 0 | 10000000 | 000000000000000000000000000000000000000 | $+1 \cdot 2^{128-127} \cdot 1.0 = 2$         |
| 0 | 00000001 | 000000000000000000000000000000000000000 | $+1 \cdot 2^{1-127} \cdot 1.0 = 2^{-126}$    |
| 0 | 00000000 | 100000000000000000000000000000000000000 | $+1 \cdot 2^{-126} \cdot 0.1 = 2^{-127}$     |
| 0 | 00000000 | 0000000000000000000000000001            | $+1 \cdot 2^{-126} \cdot 2^{-23} = 2^{-149}$ |
| 0 | 00000000 | 000000000000000000000000000000000000000 | 0                                            |
| 1 | 00000000 | 000000000000000000000000000000000000000 | -0                                           |
| 1 | 10000001 | 10100000000000000000000                 | $-1 \cdot 2^{129 - 127} \cdot 1.101 = -6.5$  |
| 1 | 11111111 | 000000000000000000000000000000000000000 | $-\infty$                                    |

# **IEEE Floating Point Data Types**

|                          | Single precision                   | Double precision              |
|--------------------------|------------------------------------|-------------------------------|
| Significand size $(p)$   | 24 bits                            | 53 bits                       |
| Exponent size            | 8 bits                             | 11                            |
| Total size               | 32 bits                            | 64 bits                       |
| $e_{\max}$               | +127                               | +1023                         |
| $e_{\min}$               | -126                               | -1022                         |
| Smallest normalized      | $2^{-126} \approx 10^{-38}$        | $2^{-1022} \approx 10^{-308}$ |
| Largest normalized       | $2^{127} \approx 10^{38}$          | $2^{1023} \approx 10^{308}$   |
| $\epsilon_{\rm machine}$ | $2^{-24} \approx 6 \cdots 10^{-8}$ | $2^{-53} \approx 10^{-16}$    |

# **Floating Point Arithmetic**

- $\bullet$  Define  $\mathrm{fl}(x)$  as the closest floating point approximation to x
- $\bullet$  By the definition of  $\epsilon_{\mathrm{machine}}$ , we have for the relative error:

For all 
$$x \in \mathbb{R}$$
, there exists  $\epsilon$  with  $|\epsilon| \leq \epsilon_{\mathrm{machine}}$  such that  $\mathrm{fl}(x) = x(1+\epsilon)$ 

- The result of an operation  $\circledast$  using floating point numbers is  $\mathrm{fl}(a\circledast b)$
- If  $f(a \circledast b)$  is the nearest floating point number to  $a \circledast b$ , the arithmetic rounds correctly (IEEE does), which leads to the following property:

For all floating point x,y, there exists  $\epsilon$  with  $|\epsilon| \leq \epsilon_{\rm machine}$  such that  $x\circledast y=(x*y)(1+\epsilon)$ 

Round to nearest even in the case of ties

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## Notes on the equivalence of norms

Steven G. Johnson, MIT Course 18.335

September 19, 2012

If we are given two norms  $\|\cdot\|_a$  and  $\|\cdot\|_b$  on some finite-dimensional vector space V over  $\mathbb{C}$ , a very useful fact is that they are always within a constant factor of one another. Specifically, there exists a pair of real numbers  $0 < C_1 \le C_2$  such that, for all  $x \in V$ , the following inequality holds:

$$C_1 \|x\|_b < \|x\|_a < C_2 \|x\|_b$$

Note that any *finite*-dimensional vector space, by definition, is spanned by a *basis*  $e_1, e_2, \ldots, e_n$  where n is the *dimension* of the vector space. (The basis is often chosen to be orthonormal if we have an inner product, but non-orthonormal bases are fine too.) That is, any vector x can be written

$$x = \sum_{i=1}^{n} \alpha_i e_i$$

where the  $\alpha_i$  are some scalars depending on x.

Now, we can prove equivalence of norms in four steps, the last of which requires some knowledge of analysis. (I have seen other proofs as well, but they all require some theorem of analysis.)

## Step 1: It is sufficient to consider $\|\cdot\|_b = \|\cdot\|_1$ (transitivity).

First, us define an  $L_1$ -style norm by

$$||x||_1 = \sum_{i=1}^n |\alpha_i|.$$

(It is easy to see this is a norm. The linear independence of any basis  $\{e_i\}$  means that  $x \neq 0 \iff \alpha_j \neq 0$  for some  $j \iff ||x||_1 > 0$ . The triangle inequality and the scaling property are obvious and follow from the usual properties of  $L_1$  norms on  $\alpha \in \mathbb{C}^n$ .)

We will show that it is sufficient for to prove that  $\|\cdot\|_a$  is equivalent to  $\|\cdot\|_1$ , because norm equivalence is *transitive*: if two norms are equivalent to  $\|\cdot\|_1$ , then they are equivalent to each other. In particular, suppose both  $\|\cdot\|_a$  and  $\|\cdot\|_{a'}$  are equivalent to  $\|\cdot\|_1$  for constants  $0 < C_1 \le C_2$  and  $0 < C_1' \le C_2'$ , respectively:

$$C_1 ||x||_1 \le ||x||_a \le C_2 ||x||_1,$$
  
 $C'_1 ||x||_1 \le ||x||_{a'} \le C'_2 ||x||_1.$ 

It immediately follows that

$$\frac{C_1'}{C_2}\|x\|_a \leq \|x\|_{a'} \leq \frac{C_2'}{C_1}\|x\|_a,$$

and hence  $\|\cdot\|_a$  and  $\|\cdot\|_{a'}$  are equivalent. Q.E.D.

#### Step 2: It is sufficient to consider only x with $||x||_1 = 1$

We wish to show that

$$C_1||x||_1 \le ||x||_a \le C_2||x||_1$$

is true for all  $x \in V$  for some  $C_1, C_2$ . It is trivially true for x = 0, so we need only consider  $x \neq 0$ , in which case we can divide by  $||x||_1$  to obtain the condition

$$C_1 \leq ||u||_a \leq C_2$$

where  $u = x/||x||_1$  has norm  $||u||_1 = 1$ . Q.E.D.

#### Step 3: Any norm $\|\cdot\|_a$ is continuous under $\|\cdot\|_1$

We wish to show that any norm  $\|\cdot\|_a$  is a continuous function on V under the topology induced by the norm  $\|\cdot\|_1$ . That is, we wish to show that for any  $\epsilon > 0$ , there exists a  $\delta > 0$  such that

$$||x - x'||_1 < \delta \implies |||x||_a - ||x'||_a| < \epsilon.$$

We prove this in two steps. First, by the triangle inequality on  $\|\cdot\|_a$ , it follows that

$$||x||_a - ||x'||_a = ||x' + (x - x')||_a - ||x'||_a \le ||x - x'||_a$$
$$||x'||_a - ||x||_a = ||x - (x - x')||_a - ||x||_a \le ||x - x'||_a$$

and hence

$$|||x||_a - ||x'||_a| \le ||x - x'||_a$$

Second, applying the triangle inequality again, and writing  $x = \sum_{i=1}^{n} \alpha_i e_i$  and  $x' = \sum_{i=1}^{n} \alpha'_i e_i$  in our basis, we obtain

$$||x - x'||_a \le \sum_{i=1}^n |\alpha_i - \alpha'_i| \cdot ||e_i||_a \le ||x - x'||_1 \left(\max_i ||e_i||_a\right).$$

Therefore, if we choose

$$\delta = \frac{\epsilon}{\max_i \|e_i\|_a},$$

it immediately follows that

$$||x - x'||_1 < \delta \implies |||x||_a - ||x'||_a| \le ||x - x'||_a < \epsilon.$$

### Step 4: The maximum and minimum of $\|\cdot\|_a$ on the unit sphere

It is a standard theorem of analysis, the extreme value theorem, that a continuous function (e.g.  $\|\cdot\|_a$ , from step 3) on compact set (e.g. the unit "sphere" defined by  $\{u \text{ for } \|u\|_1 = 1\}$ , a closed and bounded set) must achieve a maximum and minimum value on the set (it cannot merely approach them). Let

$$C_1 = \min_{\|u\|_1 = 1} \|u\|_a,$$

$$C_2 = \max_{\|u\|_1 = 1} \|u\|_a.$$

Since  $u \neq 0$  for  $||u||_1 = 1$ , it follows that  $C_2 \geq C_1 > 0$  and

$$C_1 \leq ||u||_a \leq C_2$$

as required by step 2. We are done!

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

# 18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# Modern Differential Equations Solver Software: Where We Are and Where We're Headed

Chris Rackauckas

Massachusetts Institute of Technology

# A lot of people solve differential equations every single day

How has this gotten better, how has it stayed the same?

### Non-Stiff Equations

- Non-stiff equations are generally thought to have been "solved"
- Standard methods: Runge-Kutta and Adams-Bashforth-Moulton
  - ABM is implicit!!!!!!!
- Tradeoff: ABM minimizes function calls while RK maximizes steps.
- In the end, Runge-Kutta seems to have "won"
  - Optimization of the leading truncation coefficients
  - PI(D)-adaptivity
  - High order (8th, 9th, 14th!)

# Simulating ODEs: RK4

$$y' = f(t, y)$$
 You know  $y(t_n)$  and what to find  $y(t_{n+1})$ 

$$t_{n+1} = t_n + h$$

$$Euler: y_{n+1} = y_n + hf(t_n, y_n)$$

$$\begin{align} k_1 &= f(t_n,y_n), \ k_2 &= f\left(t_n+\frac{h}{2},y_n+h\frac{k_1}{2}\right), \ k_3 &= f\left(t_n+\frac{h}{2},y_n+h\frac{k_2}{2}\right), \ k_4 &= f\left(t_n+h,y_n+hk_3\right). \end{array} \ \begin{align*} \overline{y_{n+1} &= y_n+\frac{h}{6}\left(k_1+2k_2+2k_3+k_4\right), \ t_{n+1} &= t_n+h \end{array}$$

## The Structure of a Runge-Kutta Method

$$y_{n+1}=y_n+h\sum_{i=1}^sb_ik_i,$$
 where  $k_1=f(t_n,y_n),\ k_2=f(t_n+c_2h,y_n+h(a_{21}k_1)),\ k_3=f(t_n+c_3h,y_n+h(a_{31}k_1+a_{32}k_2)),$   $\vdots \ k_s=f(t_n+c_sh,y_n+h(a_{s1}k_1+a_{s2}k_2+\cdots+a_{s,s-1}k_{s-1})).$ 

# 4<sup>th</sup> Order Runge-Kuttas as Butcher Tableus

#### "The Runge-Kutta Method"

#### Runge's 3/8's method

| 0   |      |     |     |     |
|-----|------|-----|-----|-----|
| 1/3 | 1/3  |     |     |     |
| 2/3 | -1/3 | 1   |     |     |
| 1   | 1    | -1  | 1   |     |
|     | 1/8  | 3/8 | 3/8 | 1/8 |

# Ways to Judge an RK Method

#### Optimization of next order coefficients

$$\begin{aligned} b_2a_{21} + b_3[a_{31} + a_{32}] + b_4[a_{41} + a_{42} + a_{43}] &= 1/2 \\ b_2a_{21}^2 + b_3[a_{31} + a_{32}]^2 + b_4[a_{41} + a_{42} + a_{43}]^2 &= 1/3 \\ b_2a_{22} + b_3[a_{21}a_{32} + a_{33}] + b_4[a_{21}a_{42} + a_{43}(a_{31} + a_{32}) + a_{44}] &= 1/6 \\ b_2a_{21}^3 + b_3[a_{31} + a_{32}]^3 + b_4[a_{41} + a_{42} + a_{43}]^3 &= 1/4 \\ b_2a_{21}a_{22} + b_3[\frac{1}{2}a_{21}^2a_{32} + (a_{31} + a_{32})(a_{21}a_{32} + a_{33})] + \frac{1}{2}b_4[a_{21}^2a_{42} \\ + a_{43}(a_{31} + a_{32})^2 + 2(a_{41} + a_{42} + a_{43})(a_{21}a_{42} + (a_{31} + a_{32})a_{43} + a_{44})] &= 1/6 \\ b_3a_{22}a_{32} + b_4[a_{21}a_{32}a_{43} + a_{22}a_{42} + a_{33}a_{43}] &= 1/24 \\ b_2a_{21}^4 + b_3[a_{31} + a_{32}]^4 + b_4[a_{41} + a_{42} + a_{43}]^4 &= 1/5 \\ 3b_2a_{21}^2a_{22} + b_3[a_{21}^3a_{32} + 3(a_{31} + a_{32})^2(a_{21}a_{32} + a_{33})] + b_4[a_{21}^3a_{42} + (a_{31} + a_{32})^3a_{43} + 3(a_{41} + a_{42} + a_{43})^2(a_{21}a_{42} + (a_{31} + a_{32})a_{43} + a_{44})] &= 7/20 \\ b_3a_{21}^2a_{32}(a_{31} + a_{32}) + b_4[(a_{41} + a_{42} + a_{43})(a_{21}^2a_{42} + (a_{31} + a_{32})^2a_{43})] &= 1/15 \\ \frac{1}{2}b_2a_{22}^2 + b_3[a_{21}a_{32}(\frac{1}{2}a_{21}a_{32} + a_{22} + a_{33}) + a_{22}a_{32}(a_{31} + a_{32}) + \frac{1}{2}a_{33}^2] \\ + b_4[\frac{1}{2}a_{21}^2(a_{32}a_{43} + a_{42}^2) + (a_{31} + a_{32})(a_{21}(a_{32}a_{43} + a_{42}a_{43}) + a_{43}(a_{33} + a_{44}) \\ + \frac{1}{2}(a_{31} + a_{32})a_{43}^2) + a_{21}a_{42}(a_{22} + a_{44}) + (a_{21}a_{32}a_{43} + a_{22}a_{42} \\ + a_{33}a_{43})(a_{41} + a_{42} + a_{43}) + \frac{1}{2}a_{44}^2 \\ = 11/120 \\ b_4a_{22}a_{32}a_{43} = 1/120 \\ \end{cases}$$

#### Stability

# Dormand-Prince 5<sup>th</sup> Order (1980)

| 0    |            |             |            |          |               |          |      |
|------|------------|-------------|------------|----------|---------------|----------|------|
| 1/5  | 1/5        |             |            |          |               |          |      |
| 3/10 | 3/40       | 9/40        |            |          |               |          |      |
| 4/5  | 44/45      | -56/15      | 32/9       |          |               |          |      |
| 8/9  | 19372/6561 | -25360/2187 | 64448/6561 | -212/729 |               |          |      |
| 1    | 9017/3168  | -355/33     | 46732/5247 | 49/176   | -5103/18656   |          |      |
| 1    | 35/384     | 0           | 500/1113   | 125/192  | -2187/6784    | 11/84    |      |
|      | 35/384     | 0           | 500/1113   | 125/192  | -2187/6784    | 11/84    | 0    |
|      | 5179/57600 | 0           | 7571/16695 | 393/640  | -92097/339200 | 187/2100 | 1/40 |

## Adaptivity

- These Runge-Kutta methods have also been tuned for adaptive stepsizes
  - Embedded methods use the same stages  $k_i$  in order to get two solutions,  $u_n$  and  $\widetilde{u_n}$ .
  - The difference is an error estimate:  $E_n = \frac{\|u_n \widetilde{u_n}\|}{abstol + (reltol)|u_n|}$
  - If  $E_n < 1$ , accept the step, otherwise reject the step
  - Change the timestep. There are many methods!
    - Simplest is akin to proportional control:  $\Delta t_{new} = \frac{\Delta t}{E_n}$
    - PI-adaptivity brings in previous errors to smooth out the time steps
      - Changing  $\Delta t$  can decrease stability!

#### Dense Output

- Dense (continuous) output can also be embedded into the numerical method.
- Simplest method: Hermite interpolation
  - $u_{n+\theta} = (1-\theta)u_n + \theta u_{n+1} + \theta(\theta-1)((1-2\theta)(u_{n+1}-u_n) + (\theta-1)\Delta t u'_n + \theta \Delta t u'_{n+1}$
  - Only uses the values and derivatives at the endpoints!

```
\widetilde{b}_1 = -1.0530884977290216t(t-1.3299890189751412) \left(t^2-1.4364028541716351t+0.7139816917074209\right) \widetilde{b}_2 = 0.1017t^2 \left(t^2-2.1966568338249754t+1.2949852507374631\right) \widetilde{b}_3 = 2.490627285651252793t^2 \left(t^2-2.38535645472061657t+1.57803468208092486\right) \widetilde{b}_4 = -16.54810288924490272(t-1.21712927295533244)(t-0.61620406037800089)t^2 \widetilde{b}_5 = 47.37952196281928122(t-1.203071208372362603)(t-0.658047292653547382)t^2 \widetilde{b}_6 = -34.87065786149660974(t-1.2)(t-0.666666666666666666666666666666666666
```

## RK methods are still being improved!

- Optimizing coefficients can be done not just in general, but also to applications
  - Recent methods, Tsit5 and Vern#, reduce the number of assumptions made in coefficient optimization, leading to more optimal solutions (>2010)
  - Methods specialized for wave equations, low-dispersion results, extended monotonicity equation for PDEs (SSPRK), etc. are hot topics in new high order Runge-Kutta methods

#### 100x100 Linear ODEs

#### Pleiades Problem

# 3-Body Problem (CVODE\_Adams fails)

# Minor improvements in Differential Equations. jl

- FMA (fused multiply-add)
- SIMD
- fastmath on adaptivity parameters
- Full inlining of user function

#### But can we do more?

Parallelism is not well-exploited.

### 3 forms of parallelism in diffeqs

- Within-Method parallelism
  - Parallelize the operations within the method of a differential equation solver or within the derivative function f
  - Methods can be chosen to have more within-method parallelism
- Parallelism in time
  - Parallelize across time, then relax to a solution
    - May be hard to converge! May not be efficient!
- Parameter Parallelism
  - If people are solving the same system thousands of times with different initial conditions and parameters, this is a good level to parallelize at!

# Pervasive Allowance of Within-Method parallelism through Julia

- Julia's broadcast system allows an array type to define its actions
- If an array chooses to parallelize its elementwise (broadcasted) operations), they will be broadcasted
- If an entire solver is written to never index and always broadcast, then all internal operations will be the user-defined actions
- Result: full parallelism in the ODE solver
  - GPU-based arrays stay on the GPU
  - Distributed arrays stay distributed
  - Multithreaded arrays will auto-multithread the operations of the method

#### Example of a Broadcast-Based Internal

@muladd function perform step!(integrator, cache::Tsit5Cache, repeat step=false) Zero GPU/Distrib TO DOUGLE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO THE PARTY TO @unpack c1,c2,c3,c4,c5,c6,a21,a31,a32,a41,a42,a43,a51,a52,a53,a54,a61,a62,a63,a64,a65, @unpack k1,k2,k3,k4,k5,k6,k7,utilde,tmp,atmp = cache a = dt\*a21@. tmp = uprev+a\*k1 f(k2, tmp, p, t+c1\*dt) 0. tmp = uprev+dt\*(a31\*k1+a32\*k2) f(k3, tmp, p, t+c2\*dt)@. tmp = uprev+dt\*(a41\*k1+a42\*k2+a43\*k3) f(k4, tmp, p, t+c3\*dt)  $\emptyset$ . tmp = uprev+dt\*(a51\*k1+a52\*k2+a53\*k3+a54\*k4) f(k5, tmp, p, t+c4\*dt) $\emptyset$ . tmp = uprev+dt\*(a61\*k1+a62\*k2+a63\*k3+a64\*k4+a65\*k5) f(k6, tmp, p, t+dt)@. u = uprev+dt\*(a71\*k1+a72\*k2+a73\*k3+a74\*k4+a75\*k5+a76\*k6) f(k7, u, p, t+dt) if integrator.opts.adaptive @. utilde = dt\*(btilde1\*k1 + btilde2\*k2 + btilde3\*k3 + btilde4\*k4 + btilde5\*k5 + btil calculate\_residuals!(atmp, utilde, uprev, u, integrator.opts.abstol, integrator.opts integrator.EEst = integrator.opts.internalnorm(atmp,t)

# Pros/Cons of "Array-Based Parallelism"

#### • Pros:

- It's a style that's already used a lot
  - Big PDE simulations, climate simulations
- Dead simple to get nearly 100% efficient (in Julia!)

#### • Cons:

Only efficient for LARGE ODE systems

What about changing the method for more within-method parallelism?

### Parallel Runge-Kutta methods

$$\mathbf{A} = \begin{bmatrix} 0 & & & \\ \times & 0 & & \\ \times & 0 & 0 & \\ \times & \times & \times & 0 \\ \times & \times & \times & 0 & 0 \end{bmatrix}$$

5 stages
But only 3 steps in parallel

# Multithreading Extrapolation

# Parareal Algorithms – Parallel in Time

#### Parameter Parallelism

- Naïve: Take the ODE solver and run it in parallel many times
  - This is fairly efficient!
- Next level: compile the ODE solver to a GPU kernel, and then call that GPU kernel on an array of parameters
  - Thousands of ODE solves per computer!
  - Limiting factor: memory

# Intermediate Conclusion: That's just non-stiff ODEs (and not even all of it)

Even with non-stiff methods, we have already improved a lot over the older Fortran methods. And there's still a lot more that we can do.

# Stiff ODEs: Fall of the BDF

What's coming to get GEAR's method.

#### Backwards Differentiation Formulae

- BDF1:  $y_{n+1} y_n = hf(t_{n+1}, y_{n+1})$  (this is the backward Euler method)
- $\bullet$  BDF2:  $y_{n+2} \frac{4}{3} y_{n+1} + \frac{1}{3} y_n = \frac{2}{3} h f(t_{n+2}, y_{n+2})$
- $\bullet$  BDF3:  $y_{n+3}-\frac{18}{11}y_{n+2}+\frac{9}{11}y_{n+1}-\frac{2}{11}y_n=\frac{6}{11}hf(t_{n+3},y_{n+3})$
- $\bullet$  BDF4:  $y_{n+4}-\frac{48}{25}y_{n+3}+\frac{36}{25}y_{n+2}-\frac{16}{25}y_{n+1}+\frac{3}{25}y_n=\frac{12}{25}hf(t_{n+4},y_{n+4})$
- $\bullet$  BDF5:  $y_{n+5}-\frac{300}{137}y_{n+4}+\frac{300}{137}y_{n+3}-\frac{200}{137}y_{n+2}+\frac{75}{137}y_{n+1}-\frac{12}{137}y_n=\frac{60}{137}hf(t_{n+5},y_{n+5})$
- $\bullet$  BDF6:  $y_{n+6} \frac{360}{147}y_{n+5} + \frac{450}{147}y_{n+4} \frac{400}{147}y_{n+3} + \frac{225}{147}y_{n+2} \frac{72}{147}y_{n+1} + \frac{10}{147}y_n = \frac{60}{147}hf(t_{n+6},y_{n+6})$

Methods with s > 6 are not zero-stable so they cannot be used.<sup>[4]</sup>

#### Evolution of Gear's Method

- GEAR: Original code. Adaptive order adaptive time via interpolation
  - Lowers the stability!
- LSODE series: update of GEAR
  - Adds rootfinding, Krylov, etc
- VODE: Variable-coefficient form
  - No interpolation necessary.
- CVODE: VODE rewritten in C++
  - Adds sensitivity analysis

#### Problems with BDF

BDF is a multistep method

Needs "Startup Steps"

Inefficient with events

It is only L-stable up to 2<sup>nd</sup> order

Has high truncation error coefficients

#### **Implicit**

Requires good step predictors

# But in 2019, what can we exploit?

Sparse factorizations, Krylov exponential linear algebra, IMEX, Approximate Factorization, ETC.

# Orego Benchmarks

#### Rosenbrock Methods

Aren't new! (ode23s)

Can fix a lot of problems:

Exploit sparse factorization

No step predictions required

Can optimize coefficients to high

order

Con: Needs accurate Jacobians

$$Wk_{1} = F(y_{n})$$

$$Wk_{2} = F\left(y_{n} + \frac{2}{3}hk_{1}\right) - \frac{4}{3}hdJk_{1}$$

$$y_{n+1} = y_{n} + \frac{h}{4}(k_{1} + 3k_{2})$$

#### Automatic Differentiation in a nutshell

- Numerical differentiation is numerically bad because you're dividing by a small number. Can this be avoided?
- Early idea: instead of using a real-valued difference, when f is real-valued but complex analytic, use the following identity:

$$f'(x) \approx \Im\left\{\frac{f(x+ih)}{h}\right\}.$$

- Claim: the numerical stability of this algorithm matches that of f
- Automatic differentiation then scales this idea to multiple dimensions
- One implementation: use Dual numbers  $x = a + b\epsilon$  where  $\epsilon^2 = 0$  (smooth infinitesimal arithmetic). Define  $f(x) = f(a) + f'(a)b\epsilon$  (chain rule).

# Differentiable Programming

$$(x+x'\varepsilon)+(y+y'\varepsilon)=x+y+(x'+y')\varepsilon \ (x+x'\varepsilon)\cdot(y+y'\varepsilon)=xy+xy'\varepsilon+yx'\varepsilon+x'y'\varepsilon^2=xy+(xy'+yx')\varepsilon$$

- Claim: if you recompiled your entire program to do Dual arithmetic, then the output of your program is a Dual number which computes both the original value and derivative simultaneously (to machine accuracy).
- As described, this is known as operator overloading forward-mode automatic differentiation (AD). There are also computational graph and AST-based AD implementations. In addition, there are "adjoint" or reverse-mode automatic differentiation which specifically produce gradients of cost functions with better scaling properties
- "Backpropogation" of neural networks is simple reverse-mode AD on some neural network program.

## Differentiable Programming in Julia

- I have defined this implementation of automatic differentiation as "the way you would change every arithmetic operation of a program if you wanted to calculate the derivative.
- The differential equation solvers and PuMaS are all implemented as generic algorithms in Julia which are generic with respect to the Number and AbstractArray types that are used
- ForwardDiff.jl defines a Dual number type for forward-mode automatic differentiation, Flux.jl defines a Tracker number type for reverse-mode automatic differentiation.
- If you put these into these simulation tools, a new algorithm is automatically generated that propagates the solution and its derivatives through every step of the code.

# Side note: this same technology let's us fuse with neural networs

#### ODE Problems can fall into different classes

#### **Physical Modeling**

SecondOrderODEProblem(f,u0,tspan,p)

• 
$$u^{\prime\prime} = f(u, p, t)$$

PartitionedODEProblem(f1,f2,v0,u0,tsp an,p)

• 
$$v' = f_1(t, u)$$

• 
$$u' = f_2(v)$$

HamiltonianODEProblem(H,p0,q0,tspan,p)

#### **PDE Discretizations**

SplitODEProblem(f1,f2,u0,tspan,p) (IMEX)

• 
$$u' = f_1(u, p, t) + f_2(u, p, t)$$

SemilinearODEProblem(A,f2,u0,tspan,p)

• 
$$u' = Au + f(u, p, t)$$

LocalSemilinearODEProblem(A,f2,u0,tspan, p)

$$u' = Au + f.(u, p, t)$$

#### Exponential Runge-Kutta

Explicit methods for stiff equations

Small enough: Build matrix

exponential

Large enough: Krylov exp(t\*A)\*v

$$\begin{aligned} U_{ni} &= e^{c_i h_n L_n} u_n + h_n \sum_{j=1}^{i-1} a_{ij} (h_n L_n) N_n (U_{nj}), \ u_{n+1} &= e^{h_n L_n} u_n + h_n \sum_{i=1}^{s} b_i (h_n L_n) N_n (U_{ni}) \end{aligned}$$

# Non-stiff and Stiff ODEs are far from solved if you really need the performance.

Plenty of methods were not mentioned here that are showing promise in research and in the Differential Equations. jl software

## Putting it together for users: polyalgorithms

#### Conclusion

- Today you can solve ODEs
- Tomorrow you will likely be able to solve them much faster

Want a paid summer position? Want a paid part time position as a PuMaS/DiffEq developer?

Contact me for Google Summer of Code or PuMaS development. No Julia experience is required for GSoC. Julia experience is required for PuMaS.

https://julialang.org/soc/ideas-page

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# Lecture 10 Householder Reflectors and Givens Rotations

MIT 18.335J / 6.337J

Introduction to Numerical Methods

Per-Olof Persson

September 26, 2006

## **Gram-Schmidt as Triangular Orthogonalization**

Gram-Schmidt multiplies with triangular matrices to make columns orthogonal, for example at the first step:

$$\begin{bmatrix} v_1 & v_2 & \cdots & v_n \end{bmatrix} \begin{bmatrix} \frac{1}{r_{11}} & \frac{-r_{12}}{r_{11}} & \frac{-r_{13}}{r_{11}} & \cdots \\ & 1 & & \\ & & 1 & \\ & & & \ddots \end{bmatrix} = \begin{bmatrix} q_1 & v_2^{(2)} & \cdots & v_n^{(2)} \\ & & \ddots & \\ & & & \ddots \end{bmatrix}$$

After all the steps we get a product of triangular matrices

$$A\underbrace{R_1R_2\cdots R_n}_{\hat{R}^{-1}} = \hat{Q}$$

"Triangular orthogonalization"

## **Householder Triangularization**

The Householder method multiplies by unitary matrices to make columns triangular, for example at the first step:

$$Q_1 A = \begin{bmatrix} r_{11} & \mathbf{x} & \cdots & \mathbf{x} \\ \mathbf{0} & \mathbf{x} & \cdots & \mathbf{x} \\ \mathbf{0} & \mathbf{x} & \cdots & \mathbf{x} \\ \vdots & \vdots & \ddots & \vdots \\ \mathbf{0} & \mathbf{x} & \cdots & \mathbf{x} \end{bmatrix}$$

After all the steps we get a product of orthogonal matrices

$$\underbrace{Q_n \cdots Q_2 Q_1}_{Q^*} A = R$$

"Orthogonal triangularization"

## **Introducing Zeros**

- $\bullet$   $Q_k$  introduces zeros below the diagonal in column k
- Preserves all the zeros previously introduced

$$\begin{bmatrix} \times & \times & \times & \times \\ \times & \times & \times & \times \\ \times & \times &$$

#### **Householder Reflectors**

• Let  $Q_k$  be of the form

$$Q_k = \begin{bmatrix} I & 0 \\ 0 & F \end{bmatrix}$$

where I is  $(k-1)\times(k-1)$  and F is  $(m-k+1)\times(m-k+1)$ 

 $\bullet$  Create Householder reflector F that introduces zeros:

$$x = \begin{bmatrix} \times \\ \times \\ \times \\ \vdots \\ \times \end{bmatrix} \qquad Fx = \begin{bmatrix} \|x\| \\ 0 \\ \vdots \\ 0 \end{bmatrix} = \|x\|e_1$$

#### **Householder Reflectors**

• Idea: Reflect across hyperplane H orthogonal to  $v = \|x\|e_1 - x$ , by the unitary matrix

$$F = I - 2\frac{vv^*}{v^*v}$$

Compare with projector

$$P_{\perp v} = I - \frac{vv^*}{v^*v}$$

#### **Choice of Reflector**

- We can choose to reflect to any multiple z of  $||x||e_1$  with |z|=1
- Better numerical properties with large ||v||, for example

$$v = \operatorname{sign}(x_1) ||x|| e_1 + x$$

• Note: sign(0) = 1, but in MATLAB, sign(0) = 0

## The Householder Algorithm

- Compute the factor R of a QR factorization of  $m \times n$  matrix A ( $m \ge n$ )
- Leave result in place of A, store reflection vectors  $v_k$  for later use

#### **Algorithm: Householder QR Factorization**

for 
$$k = 1$$
 to  $n$ 

$$x = A_{k:m,k}$$

$$v_k = \text{sign}(x_1) ||x||_2 e_1 + x$$

$$v_k = v_k / ||v_k||_2$$

$$A_{k:m,k:n} = A_{k:m,k:n} - 2v_k (v_k^* A_{k:m,k:n})$$

## Applying or Forming Q

- Compute  $Q^*b=Q_n\cdots Q_2Q_1b$  and  $Qx=Q_1Q_2\cdots Q_nx$  implicitly
- $\bullet$  To create Q explicitly, apply to x=I

## Algorithm: Implicit Calculation of $Q^*b$

for 
$$k=1$$
 to  $n$  
$$b_{k:m}=b_{k:m}-2v_k(v_k^*b_{k:m})$$

## Algorithm: Implicit Calculation of Qx

for 
$$k=n$$
 downto  $1$  
$$x_{k:m}=x_{k:m}-2v_k(v_k^*x_{k:m})$$

## **Operation Count - Householder QR**

Most work done by

$$A_{k:m,k:n} = A_{k:m,k:n} - 2v_k(v_k^* A_{k:m,k:n})$$

- Operations per iteration:
  - 2(m-k)(n-k) for the dot products  $v_k^*A_{k:m,k:n}$
  - (m-k)(n-k) for the outer product  $2v_k(\cdots)$
  - (m-k)(n-k) for the subtraction  $A_{k:m,k:n}-\cdots$
  - -4(m-k)(n-k) total
- Including the outer loop, the total becomes

$$\sum_{k=1}^{n} 4(m-k)(n-k) = 4\sum_{k=1}^{n} (mn-k(m+n)+k^2)$$

$$\sim 4mn^2 - 4(m+n)n^2/2 + 4n^3/3 = 2mn^2 - 2n^3/3$$

#### **Givens Rotations**

Alternative to Householder reflectors

- A Givens rotation  $R=\begin{bmatrix}\cos\theta & -\sin\theta \\ \sin\theta & \cos\theta\end{bmatrix}$  rotates  $x\in\mathbb{R}^2$  by  $\theta$
- $\bullet$  To set an element to zero, choose  $\cos \theta$  and  $\sin \theta$  so that

$$\begin{bmatrix} \cos \theta & -\sin \theta \\ \sin \theta & \cos \theta \end{bmatrix} \begin{bmatrix} x_i \\ x_j \end{bmatrix} = \begin{bmatrix} \sqrt{x_i^2 + x_j^2} \\ 0 \end{bmatrix}$$

or

$$\cos \theta = \frac{x_i}{\sqrt{x_i^2 + x_j^2}}, \qquad \sin \theta = \frac{-x_j}{\sqrt{x_i^2 + x_j^2}}$$

#### **Givens QR**

Introduce zeros in column from bottom and up

$$\begin{bmatrix} \times & \times & \times & \times \\ \times & \times & \times & \times \\ \times & \times &$$

• Flop count  $3mn^2-n^3$  (or 50% more than Householder QR)

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.335 Fall 2008 Performance Experiments with Matrix Multiplication

Steven G. Johnson

Hardware: 2.66GHz Intel Core 2 Duo 64-bit mode, double precision, gcc 4.1.2

optimized BLAS dgemm: ATLAS 3.6.0

http://math-atlas.sourceforge.net

## A trivial problem?

$$C = A B$$
 $m \times p \quad m \times n \quad n \times p$ 

the "obvious" C code:

```
/* C = A B, where A is m x n, B is n x p,
```

```
for i = 1 to m

for j = 1 to p

C_{ij} = \sum_{k=1}^{n} A_{ik} B_{kj}
```

2mnp flops (adds+mults)

just three loops, how complicated can it get?

## flops/time is not constant!

(square matrices, m=n=p)

#### Not all "noise" is random

## All flops are not created equal

### Things to remember

- We cannot understand performance without understanding memory efficiency (caches).
  - $-\sim 10$  times more important than arithmetic count
- Computers are more complicated than you think.
- Even a trivial algorithm is nontrivial to implement well.
  - matrix multiplication: 10 lines of code  $\rightarrow$  130,000+ (ATLAS)

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# Experiments with Cache-Oblivious Matrix Multiplication for 18.335

Steven G. Johnson MIT Applied Math

platform: 2.66GHz Intel Core 2 Duo, GNU/Linux + gcc 4.1.2 (-O3) (64-bit), double precision

# (optimal) Cache-Oblivious Matrix Multiply

divide and conquer:

divide *C* into 4 blocks compute block multiply recursively

achieves optimal  $\Theta(n^3/\sqrt{Z})$  cache complexity

#### A little C implementation (~25 lines)

```
/* C = C + AB, where A is m x n, B is n x p, and C is m x p, in
  row-major order. Actually, the physical size of A, B, and C
  are m x fdA, n x fdB, and m x fdC, but only the first n/p/p
  columns are used, respectively. */
void add matmul rec(const double *A, const double *B, double *C,
                         int m, int n, int p, int fdA, int fdB, int fdC)
    if (m+n+p \le 48) \{ /* \le 16x16 \text{ matrices "on average" } */
                                                                     note: base case is \sim 16 \times 16
              int i, j, k;
              for (i = 0; i < m; ++i)
                                                                           recursing down to 1\times 1
                   for (k = 0; k < p; ++k) {
                             double sum = 0;
                             for (j = 0; j < n; ++j)
                                                                           would kill performance
                                       sum += A[i*fdA +j] * B[j*fdB + k];
                             C[i*fdC + k] += sum;
                                                                           (1 function call per element,
                                                                                 no register re-use)
    else { /* divide and conquer */
              int m2 = m/2, n2 = n/2, p2 = p/2;
                                                                                            dividing C into 4
              add matmul rec(A, B, C, m2, n2, p2, fdA, fdB, fdC);
              add matmul rec(A+n2, B+n2*fdB, C, m2, n-n2, p2, fdA, fdB, fdC);
                                                                                            — note that, instead, for
              add matmul rec(A, B+p2, C+p2, m2, n2, p-p2, fdA, fdB, fdC);
              add matmul rec(A+n2, B+p2+n2*fdB, C+p2, m2, n-n2, p-p2, fdA, fdB, fdC);
                                                                                            very non-square matrices,
              add matmul rec(A+m2*fdA, B, C+m2*fdC, m-m2, n2, p2, fdA, fdB, fdC);
                                                                                            we might want to divide
              add matmul rec(A+m2*fdA+n2, B+n2*fdB, C+m2*fdC, m-m2, n-n2, p2, fdA, fdB, fdC);
                                                                                            C in 2 along longest axis
              add matmul rec(A+m2*fdA, B+p2, C+m2*fdC+p2, m-m2, n2, p-p2, fdA, fdB, fdC);
              add matmul rec(A+m2*fdA+n2, B+p2+n2*fdB, C+m2*fdC+p2, m-m2, n-n2, p-p2, fdA, fdB, fdC);
void matmul rec(const double *A, const double *B, double *C,
                         int m, int n, int p)
{
    memset(C, 0, sizeof(double) * m*p);
    add matmul rec(A, B, C, m, n, p, n, p, p);
}
```

## No Cache-based Performance Drops!

#### ...but absolute performance still sucks

### Registers .EQ. Cache

- The registers (~100) form a very small, almost ideal cache
  - Three nested loops is not the right way to use this "cache" for the same reason as with other caches
- Need long blocks of unrolled code: load blocks of matrix into local variables (= registers), do matrix multiply, write results
  - Loop-free blocks = many optimized hard-coded base cases of recursion for different-sized blocks ... often automatically generated (ATLAS)
  - Unrolled  $n \times n$  multiply has  $(n^3)!$  possible code orderings compiler cannot find optimal schedule (NP hard) cacheoblivious scheduling can help (c.f. FFTW), but ultimately requires some experimentation (automated in ATLAS)

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# Lecture 14 Hessenberg/Tridiagonal Reduction

MIT 18.335J / 6.337J
Introduction to Numerical Methods

Per-Olof Persson October 26, 2006

## **Introducing Zeros by Similarity Transformations**

• Try computing the Schur factorization  $A=QTQ^*$  by applying Householder reflectors from left and right that introduce zeros:

$$\begin{bmatrix} \times \times \times \times \times \times \\ \times \times \times \times \times \times \\ \times \times \times \times \times$$

- The right multiplication destroys the zeros previously introduced
- We already knew this would not work, because of Abel's theorem
- However, the subdiagonal entries typically decrease in magnitude


## The Hessenberg Form

• Instead, try computing an upper Hessenberg matrix H similar to A:

$$\begin{bmatrix} \times \times \times \times \times \\ \times \times \times \times \times \\ \times \times \times \times \times \\ \times \times \times \times \times \\ A \end{bmatrix} \xrightarrow{Q_1^*} \begin{bmatrix} \times \times \times \times \times \\ \mathbf{x} \times \mathbf{x} \times \mathbf{x} \\ \mathbf{0} \times \mathbf{x} \times \mathbf{x} \\ \mathbf{0} \times \mathbf{x} \times \mathbf{x} \\ \mathbf{0} \times \mathbf{x} \times \mathbf{x} \\ \mathbf{0} \times \mathbf{x} \times \mathbf{x} \end{bmatrix} \xrightarrow{Q_1} \begin{bmatrix} \times \times \times \times \\ \times \times \times \times \\ \times \times \times \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\ \mathbf{x} \times \mathbf{x} \times \\$$

- This time the zeros we introduce are not destroyed
- Continue in a similar way with column 2:

$$\begin{bmatrix} \times \times \times \times \times \\ \times \times \times \times \times \\ \times \times \times \times \\ \times \times \times \times \\ \times \times \times \times \end{bmatrix} \xrightarrow{Q_1^*} \begin{bmatrix} \times \times \times \times \times \\ \times \times \times \times \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{0} \times \mathbf{X} \times \\ \mathbf{0} \times \mathbf{X} \end{bmatrix} \xrightarrow{Q_1} \begin{bmatrix} \times \times \mathbf{X} \times \\ \times \times \times \times \\ \times \times \mathbf{X} \times \\ \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X} \times \\ \mathbf{X} \times \mathbf{X}$$

## The Hessenberg Form

 $\bullet$  After m-2 steps, we obtain the Hessenberg form:

$$\underbrace{Q_{m-2}^* \cdots Q_2^* Q_1^*}_{Q^*} A \underbrace{Q_1 Q_2 \cdots Q_{m-2}}_{Q} = H = \begin{bmatrix} \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times$$

 $\bullet$  For hermitian A, zeros are also introduced above diagonals

$$\begin{bmatrix} \times \times \times \times \times \\ \times \times \times \times \times \\ \times \times \times \times \times \\ \times \times \times \times \times \\ X \times X \times$$

producing a tridiagonal matrix T after m-2 steps

#### **Householder Reduction to Hessenberg**

#### Algorithm: Householder Hessenberg

$$\begin{split} \text{for } k &= 1 \text{ to } m-2 \\ x &= A_{k+1:m,k} \\ v_k &= \mathrm{sign}(x_1) \|x\|_2 e_1 + x \\ v_k &= v_k / \|v_k\|_2 \\ A_{k+1:m,k:m} &= A_{k+1:m,k:m} - 2v_k (v_k^* A_{k+1:m,k:m}) \\ A_{1:m,k+1:m} &= A_{1:m,k+1:m} - 2(A_{1:m,k+1:m} v_k) v_k^* \end{split}$$

• Operation count (not twice Householder QR):

$$\sum_{k=1}^{m} 4(m-k)^2 + 4m(m-k) = \underbrace{4m^3/3}_{QR} + 4m^3 - 4m^3/2 = 10m^3/3$$

• For hermitian A, operation count is twice QR divided by two =  $4m^3/3$ 

## Stability of Householder Hessenberg

• The Householder Hessenberg reduction algorithm is backward stable:

$$\tilde{Q}\tilde{H}\tilde{Q}^* = A + \delta A, \qquad \frac{\|\delta A\|}{\|A\|} = O(\epsilon_{\text{machine}})$$

where  $\tilde{Q}$  is an exactly unitary matrix based on  $\tilde{v}_k$ 

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

## 18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## Why restarting Arnoldi/Lanczos is not trivial

Steven G. Johnson, MIT Applied Mathematics, course 18.335 March 21, 2019

#### Overview

The Arnoldi (and Lanczos) algorithms iteratively construct an  $m \times n$  orthonormal basis  $Q_n$  for the Krylov space  $\mathcal{K}_n = \operatorname{span} \left\{ b, Ab, \ldots, A^{n-1}b \right\}$  for a starting vector b and an  $m \times m$  matrix A. For very large m (e.g. huge sparse A), however, practical application of this algorithm eventually hits a maximum n where one runs out of memory for  $Q_n$  [and the computational cost also grows as  $\Theta(mn^2)$ ]. Even Lanczos runs into this problem, because roundoff errors lead to "ghost eigenvalues" if one does not explicitly store  $Q_n$  and periodically re-orthogonalize. The solution is periodic **restarting**: shrink down to a k-dimensional subspace containing your "best guesses" for the solution vectors, and continue Arnoldi from there. It turns out that the algorithms to perform restarting properly—called **implicitly restarted** Arnoldi or Lanczos—are surprisingly complicated and subtle. The purpose of these notes is not to explain how implicit restarting works. Rather, it is to briefly explain why naive restarting methods don't work. That is, why is restarting so hard?

## Restarting in general

In general, restarting means finding a smaller orthonormal basis

$$\underbrace{\hat{Q}_k}_{m \times k} = \underbrace{Q_n}_{m \times n} \underbrace{\hat{Q}}_{n \times k}$$

for a subspace  $\hat{\mathcal{K}}_k \subset \mathcal{K}_n$  (k < n), where  $\hat{Q}^*\hat{Q} = I \implies \hat{Q}_k^*\hat{Q}_k = I$ , and then treating this as the k-th step of an Arnoldi process and continuing from there normally (until you restart again). However, for this to work,  $\hat{Q}_k$  needs to preserve a **key property** of the Arnoldi process:

$$AQ_n = Q_n H_n + r_n e_n^*,$$

where  $H_n = Q_n^* A Q_n$  is upper-Hessenberg  $n \times n$ ,  $r_n = h_{n+1,n} q_{n+1} \perp \mathcal{K}_n$ , and  $e_n^* = \begin{bmatrix} 0 & 0 & \cdots & 0 & 1 \end{bmatrix}$ . This is the property that allows subsequent steps to continue the upper-Hessenberg property (which for Lanczos is tridiagonal and

crucial to its three-term recurrence structure). Hence, we would like to obtain the same structure for  $A\hat{Q}_k$ 

To compute  $A\hat{Q}_k$ , it is convenient to define the  $n\times n$  unitary matrix  $Q=\begin{bmatrix} \hat{Q} & \hat{Q}_\perp \end{bmatrix}$  where the  $n\times (n-k)$  matrix  $\hat{Q}_\perp$  is any orthonormal basis for the orthogonal complement of  $\hat{Q}$ 's column space. Then we can write

$$\begin{split} A\hat{Q}_k &= AQ_n\hat{Q} = Q_nH_n\hat{Q} + r_ne_n^*\hat{Q} \\ &= Q_nQQ^*H_n\hat{Q} + r_ne_n^*\hat{Q} \\ &= \left[ \begin{array}{cc} \hat{Q}_k & A\hat{Q}_\perp \end{array} \right] \left[ \begin{array}{cc} \hat{Q}^*H_n\hat{Q} \\ \hat{Q}_\perp^*H_n\hat{Q} \end{array} \right] + r_ne_n^*\hat{Q} \\ &= \left[ \begin{array}{cc} \hat{Q}_k & \left(\hat{Q}^*H_n\hat{Q}\right) \end{array} \right] + A\hat{Q}_\perp\hat{Q}_\perp^*H_n\hat{Q} + r_ne_n^*\hat{Q} \end{split}.$$

This looks messy, but we can simplfy it quite a bit if we make a good choice for  $\hat{Q}$ . With the *right* choice of  $\hat{Q}$ , in fact it *is* possible to have the  $\hat{Q}_k\hat{H}_k+\hat{r}_ke_k^*$  structure, allowing us to restart Arnoldi and Lanczos, but finding such a  $\hat{Q}$  is surprisingly subtle.

#### Naive restarting

The most obvious way to restart is to use Ritz vectors. Recall the Rayleigh-Ritz procedure: search for  $x \in \mathcal{K}_n$  and  $\nu \in \mathbb{C}$  such that  $Ax - \nu x \perp \mathcal{K}_n$ , or equivalently  $x = Q_n z$  where  $H_n z = \nu z$ . This is how we estimate the eigenvectors and eigenvalues at the n-th step of Arnoldi. It seems natural that we should want our "restarted" basis  $\hat{Q}_k$  to contain the Ritz vectors  $x = Q_n z$  that are our best estimates so far for the desired eigenvectors. For example, suppose we are looking for the k biggest- $|\lambda|$  eigenvalues, then a natural choice of restarting basis would be the Ritz vectors  $Q_n \hat{Z}$  corresponding to the biggest  $|\nu|$ . If we orthogonalize these via QR as  $\hat{Z} = \hat{Q}\hat{R}$ , we get

$$\hat{Q} = \hat{Z}\hat{R}^{-1}$$

and

$$H_n \hat{Q} = H_n \hat{Z} \hat{R}^{-1} = \hat{Z} \underbrace{\begin{bmatrix} \nu_1 & & & \\ & \nu_2 & & \\ & & \ddots & \\ & & & \ddots \\ & & & & \lambda \end{bmatrix}}_{\hat{\Lambda}} \hat{R}^{-1} = \hat{Z} \hat{\Lambda} \hat{R}^{-1} = \hat{Q} \hat{R} \hat{\Lambda} \hat{R}^{-1}.$$

Two nice things happen! In the boxed term  $\hat{Q}_k \hat{H}_k$  above, we get

$$\hat{H}_k = \hat{Q}^* H_n \hat{Q} = \hat{Q}^* \hat{Q} \hat{R} \hat{\Lambda} \hat{R}^{-1} = \hat{R} \hat{\Lambda} \hat{R}^{-1},$$

which is a product of upper-triangular matrices, and hence is upper-triangular—this certainly satisfies the requirement that  $\hat{H}_k$  should be upper-Hessenberg! Also, from the second boxed term:

$$\hat{Q}_{\perp}^* H_n \hat{Q} = \hat{Q}_{\perp}^* \hat{Q} \hat{R} \hat{\Lambda} \hat{R}^{-1} = 0,$$

since  $\hat{Q}_{\perp}^*\hat{Q}=0$  by construction. So, the second boxed term above disappears! Unfortunately, the third boxed term is

$$r_n e_n^* \hat{Q} = r_n \left( \text{last row of } \hat{Q} \right).$$

While  $r_n \perp \mathcal{K}_n \implies r_n \perp \hat{\mathcal{K}}_n$  (that is,  $\hat{Q}_k^* r_n = 0$ ) as desired, in general the last row of  $\hat{Q}$  will **not** be a multiple of  $e_k^*$ . So, this doesn't work.

The same problem arises for naive restarting of the Lanczos case  $A = A^*$ . In this case, the upper-Hessenberg matrix  $H_n$  is Hermitian. Hence the upper-triangular matrix  $\hat{H}_k = \hat{\Lambda}$  is diagonal ( $\hat{R} = I$  since the eigenvectors  $\hat{Z}$  are orthonormal). But there is still no reason why the last row of  $\hat{Q}$  should be a multiple of  $[0 \ 0 \ \cdots \ 0 \ 1]$ , so it doesn't work.

### Implicit restarting

In fact, it is possible to choose a  $\hat{Q}_k$  such that it *mostly* contains the Ritz vectors that we want and *does* preserve the Arnoldi/Lanczos property. One hint of this is that our naive choice above was actually *too good* in two ways:  $\hat{H}_k$  was upper-triangular instead of just upper-Hessenberg, and  $r_n$  was orthogonal to  $\mathcal{K}_n$  and not just  $\hat{\mathcal{K}}_k$ . This gives us "wiggle room:" if we do a little "worse" in making  $\hat{H}_k$  only upper-Hessenberg and  $\hat{r}_k$  only  $\perp \hat{\mathcal{K}}_k$ , we then have enough freedom to make the last row of  $\hat{Q}$  a multiple of  $e_k^*$ .

In particular, instead of taking eigenvectors  $\hat{Z}$  of  $H_n$ , a better solution is to do exactly n-k steps of shifted QR iteration on  $H_n$  and let  $\hat{Q}$  be the resulting eigenvector/Schur-vector estimate. This is a good estimate for the Ritz eigenvectors that we want, and it turns out to be just right to preserve the Arnoldi property. Proving that this is true requires care and tedious calculation, but is relatively straightforward. I won't go through it in detail, but if you google "implicitly restarted Arnoldi" or "implicitly restarted Lanczos" you can find a number of reviews that go through the algebra. In practice, you are unlikely to ever need to know the details: most people use "canned" implementations of Arnoldi and Lanczos such as ARPACK. But please resist the temptation to do naive restarting!

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

# 18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# Lecture 24 Sparse Matrix Algorithms

MIT 18.335J / 6.337J
Introduction to Numerical Methods

Per-Olof Persson November 28, 2006

#### **Sparse vs. Dense Matrices**

- A sparse matrix is a matrix with enough zeros that it is worth taking advantage of them [Wilkinson]
- A *structured matrix* has enough structure that it is worthwhile to use it (e.g. Toeplitz)

 a
 b
 c
 d
 e

 b
 a
 b
 c
 d

 c
 b
 a
 b
 c

 d
 c
 b
 a
 b

 e
 d
 c
 b
 a

• A dense matrix is neither sparse nor structured

## **MATLAB Sparse Matrices: Design Principles**

- Most operations should give the same results for sparse and full matrices
- Sparse matrices are never created automatically, but once created they propagate
- Performance is important but usability, simplicity, completeness, and robustness are more important
- Storage for a sparse matrix should be O(nonzeros)
- Time for a sparse operation should be close to  $O(\mathrm{flops})$

#### **Data Structures for Matrices**

#### Full:

- Storage: Array of real (or complex) numbers
- Memory: nrows\*ncols

| 31 | 0  | 53 |
|----|----|----|
| 0  | 59 | 0  |
| 41 | 26 | 0  |

double \*A

#### Sparse:

- Compressed column storage
- Memory: About
  - 1.5\*nnz+.5\*ncols


## **Compressed Column Format - Observations**

- $\bullet$  Element look-up:  $O(\log \# \text{elements in column})$  time
- Insertion of new nonzero very expensive
- Sparse vector = Column vector (not Row vector)

## **Graphs and Sparsity: Cholesky Factorization**


#### **Permutations of the 2-D Model Problem**

- $\bullet\,$  2-D Model Problem: Poisson's Equation on  $n\times n$  finite difference grid
- Total number of unknowns  $n^2 = N$
- Theoretical results for the fill-in:
  - With natural permutation:  $O(N^{3/2})$  fill
  - With any permutation:  $\Omega(N \log N)$  fill
  - With a *nested dissection* permutation:  $O(N \log N)$  fill

### **Nested Dissection Ordering**

- $\bullet$  A separator in a graph G is a set S of vertices whose removal leaves at least two connected components
- $\bullet$  A *nested dissection* ordering for an N-vertex graph G numbers its vertices from 1 to N as follows:
  - Find a separator S, whose removal leaves connected components  $T_1, T_2, \ldots, T_k$
  - Number the vertices of S from  $N-\left|S\right|+1$  to N
  - Recursively, number the vertices of each component:  $T_1$  from 1 to  $|T_1|$ ,  $T_2$  from  $|T_1|+1$  to  $|T_1|+|T_2|$ , etc
  - If a component is small enough, number it arbitrarily
- It all boils down to finding good separators!


### **Heuristic Fill-Reducing Matrix Permutations**

- Banded orderings (Reverse Cuthill-McKee, Sloan, etc):
  - Try to keep all nonzeros close to the diagonal
  - Theory, practice: Often wins for "long, thin" problems
- Minimum degree:
  - Eliminate row/col with fewest nonzeros, add fill, repeat
  - Hard to implement efficiently current champion is "Approximate Minimum Degree" [Amestoy, Davis, Duff]
  - Theory: Can be suboptimal even on 2-D model problem
  - Practice: Often wins for medium-sized problems

#### **Heuristic Fill-Reducing Matrix Permutations**

- Nested dissection:
  - Find a separator, number it last, proceed recursively
  - Theory: Approximately optimal separators
  - Practice: Often wins for very large problems
- The best modern general-purpose orderings are ND/MD hybrids


#### **Fill-Reducing Permutations in Matlab**

- Reverse Cuthill-McKee:
  - p=symrcm(A);
  - Symmetric permutation: A(p,p) often has smaller bandwidth than A
- Symmetric approximate minimum degree:
  - p=symamd(A);
  - Symmetric permutation: chol(A(p,p)) sparser than chol(A)
- Nonsymmetric approximate minimum degree:
  - p=colamd(A);
  - Column permutation: lu(A(:,p)) sparser than lu(A)
- Symmetric nested dissection:
  - Not built into MATLAB, several versions in the MESHPART toolbox

#### **Complexity of Direct Methods**

Time and space to solve any problem on any well-shaped finite element mesh with N nodes:


MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

## 18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# A Brief Overview of Optimization Problems

Steven G. Johnson MIT course 18.335, Spring 2019

#### Why optimization?

- In some sense, *all engineering design* is optimization: choosing design parameters to improve some objective
- Much of *data analysis* is also optimization: extracting some model parameters from data while minimizing some error measure (e.g. fitting)
- Most *business decisions* = optimization: varying some *decision parameters* to maximize profit (e.g. investment portfolios, supply chains, etc.)

#### A general optimization problem

$$\min_{x\in\mathbb{R}^n} f_0(x)$$

subject to *m* constraints

$$f_i(x) \le 0$$
  
$$i = 1, 2, ..., m$$

x is a *feasible point* if it satisfies all the constraints

minimize an objective function  $f_0$ with respect to n design parameters x(also called decision parameters, optimization variables, etc.)

— note that maximizing g(x)

corresponds to  $f_0(x) = -g(x)$ 

note that an *equality constraint* h(x) = 0

yields two inequality constraints

$$f_i(x) = h(x)$$
 and  $f_{i+1}(x) = -h(x)$ 

(although, in practical algorithms, equality constraints typically require special handling)

*feasible region* = set of all feasible  $x_3$ 

#### Important considerations

- Global versus local optimization
- Convex vs. non-convex optimization
- Unconstrained or box-constrained optimization, and other special-case constraints
- Special classes of functions (linear, etc.)
- Differentiable vs. non-differentiable functions
- Gradient-based vs. derivative-free algorithms
- •
- Zillions of different algorithms, usually restricted to various special cases, each with strengths/weaknesses

#### Global vs. Local Optimization

- For *general nonlinear* functions, *most* algorithms only guarantee a local optimum
  - that is, a feasible  $x_0$  such that  $f_0(x_0) \le f_0(x)$  for all feasible x within some neighborhood  $||x-x_0|| < R$  (for some small R)
- A much harder problem is to find a global optimum: the minimum of  $f_0$  for all feasible x
  - exponentially increasing difficulty with increasing n, practically impossible to *guarantee* that you have found global minimum without knowing some special property of  $f_0$
  - many available algorithms, problem-dependent efficiencies
    - *not* just genetic algorithms or simulated annealing (which are popular, easy to implement, and thought-provoking, but usually *very slow!*)
    - for example, non-random systematic search algorithms (e.g. DIRECT), partially randomized searches (e.g. CRS2), repeated local searches from different starting points ("multistart" algorithms, e.g. MLSL), ...

#### Convex Optimization

[ good reference: *Convex Optimization* by Boyd and Vandenberghe, free online at <a href="www.stanford.edu/~boyd/cvxbook">www.stanford.edu/~boyd/cvxbook</a> ]

All the functions  $f_i$  (i=0...m) are convex:

$$f_i(\alpha x + \beta y) \le \alpha f_i(x) + \beta f_i(y)$$
 where  $\alpha + \beta = 1$   
 $\alpha, \beta \in [0, 1]$ 

For a convex problem (convex objective & constraints) any local optimum *must* be a global optimum

⇒ efficient, robust solution methods available

#### Important Convex Problems

- LP (linear programming): the objective and constraints are *affine*:  $f_i(x) = a_i^T x + \alpha_i$
- QP (quadratic programming): affine constraints + convexquadratic objective  $x^{T}Ax+b^{T}x$
- SOCP (second-order cone program): LP + cone constraints  $||Ax+b||_2 \le a^Tx + \alpha$
- SDP (semidefinite programming): constraints are that  $\Sigma A_k x_k$  is positive-semidefinite

all of these have very efficient, specialized solution methods

#### Important special constraints

- Simplest case is the *unconstrained* optimization problem: *m*=0
  - e.g., line-search methods like steepest-descent,
     nonlinear conjugate gradients, Newton methods ...
- Next-simplest are *box constraints* (also called *bound constraints*):  $x_k^{\min} \le x_k \le x_k^{\max}$ 
  - easily incorporated into line-search methods and many other algorithms
  - many algorithms/software *only* handle box constraints
- •
- Linear equality constraints Ax=b
  - for example, can be explicitly eliminated from the problem by writing  $x=Ny+\xi$ , where  $\xi$  is a solution to  $A\xi=b$  and N is a basis for the nullspace of A

#### Derivatives of $f_i$

- Most-efficient algorithms typically require user to supply the gradients  $\nabla_x f_i$  of objective/constraints
  - you should *always* compute these analytically
    - rather than use finite-difference approximations, better to just use a derivative-free optimization algorithm
    - in principle, one can always compute  $\nabla_x f_i$  with about the same cost as  $f_i$ , using adjoint methods
  - gradient-based methods can find (local) optima of problems with millions of design parameters
- Derivative-free methods: only require  $f_i$  values
  - easier to use, can work with complicated "black-box" functions where computing gradients is inconvenient
  - may be only possibility for nondifferentiable problems
  - need > n function evaluations, bad for large n

#### Removable non-differentiability

consider the *non*-differentiable *unconstrained* problem:

$$\min_{x \in \mathbb{R}^n} |f_0(x)|$$

equivalent to *minimax* problem:

$$\min_{x \in \mathbb{R}^n} (\max\{f_0(x), -f_0(x)\})$$

...still nondifferentiable...

...equivalent to *constrained* problem with a "temporary" variable t:

therentiable. 
$$x \in \mathbb{R}^n, t \in \mathbb{R}$$

subject to: 
$$t \ge f_0(x)$$
  
 $t \ge -f_0(x)$ 

i.e. 
$$f_1(x,t) = f_0(x) - t$$
  
 $f_2(x,t) = -f_0(x) - t$ 

#### Example: Chebyshev linear fitting

find the fit that minimizes the *maximum error*:

$$\min_{x_1, x_2} \left( \max_i |x_1 a_i + x_2 - b_i| \right)$$
$$= \min_{x \in \mathbb{R}^2} ||Ax - b||_{\infty}$$

... nondifferentiable minimax problem

equivalent to a *linear programming* problem (LP):

 $\min_{x_1,x_2,t} t$ 

subject to 2N constraints:

$$t \ge x_1 a_i + x_2 - b_i$$
  
$$t \ge -x_1 a_i - x_2 + b_i$$

equivalently:  

$$t \ge |x_1 a_i + x_2 - b_i|$$

### Relaxations of Integer Programming

If x is integer-valued rather than real-valued (e.g.  $x \in \{0,1\}^n$ ), the resulting integer programming or combinatorial optimization problem becomes much harder in general.

However, useful results can often be obtained by a *continuous* relaxation of the problem — e.g., going from  $x \in \{0,1\}^n$  to  $x \in [0,1]^n$  ... at the very least, this gives an lower bound on the optimum  $f_0$ 

"Penalty terms" or "projection filters" (SIMP, RAMP, etc.) can be used to obtain x that  $\approx 0$  or  $\approx 1$  almost everywhere.

[ See e.g. Sigmund & Maute, "Topology optimization approaches," *Struct*. *Multidisc*. *Opt*. **48**, pp. 1031–1055 (2013). ]

#### Example: Topology Optimization

design a structure to do something, made of material A or B... let *every pixel* of discretized structure vary *continuously* from A to B

[ + tricks to impose minimum feature size and mostly "binary" A/B ]

density of each pixel varies continuously from 0 (air) to max

ex: design a cantilever to support maximum weight with a fixed amount of material

## optimized structure, deformed under load

© Springer Nature Switzerland AG. All rights reserved. This content is excluded from our Creative Commons license. For more information, see <a href="https://ocw.mit.edu/help/faq-fair-use">https://ocw.mit.edu/help/faq-fair-use</a>.

### Stochastic Optimization

$$\min_{x \in \mathbb{R}^n} E[f(x, \xi)]$$

where  $E[\cdots]$  is expected value averaging over random vars  $\xi$ 

#### Deep-learning example:

Fitting ("learning") to a huge "training set" by sampling a random subset  $\xi$ :

$$f(x,\xi) = \sum_{k \in \xi} f_k(x)$$

 $\nabla_{x} f$  often exists, but typically can't use standard gradient-descent because of randomness.

A popular algorithm: Adam [Kingma & Ba, 2014] "stochastic gradient descent"

#### Some Sources of Software

• NLopt: implements many nonlinear optimization algorithms callable from many languages (C, Python, R, Matlab, ...) (global/local, constrained/unconstrained, derivative/no-derivative)

http://github.com/stevengj/nlopt

- Python: scipy.optimize, pyOpt, ...; Julia: JuMP, Optim,...
- Decision tree for optimization software: http://plato.asu.edu/guide.html
  - lists many (somewhat older) packages for many problems
- CVX: general convex-optimization package <a href="http://cvxr.com">http://cvxr.com</a>
  ... also Python CVXOPT, R CVXR, Julia Convex

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# **Adjoint Methods**

Steven G. Johnson

Created Spring 2006, updated December 17, 2012.

## 1 Introduction

Given the solution x of a discretized PDE or some other set of M equations parameterized by P variables **p** (design parameters, a.k.a. control variables or decision parameters), we often wish to compute some function  $g(\mathbf{x}, \mathbf{p})$  based on the parameters and the solution. For example, if the PDE is a wave equation, we might want to know the scattered power in some direction. Or, for a mechanical simulation, we might want to know the load-bearing capacity of the structure. Or for a fluid, we might wish to know the flow rate somewhere. Often, however, we want to know more than just the *value* of *g*—we also want to know its gradient  $\frac{dg}{d\mathbf{p}}$ . Adjoint methods give an efficient way to evaluate  $\frac{dg}{d\mathbf{p}}$ , with a cost *independent* of P and usually comparable to the cost of solving for x once.

The gradient of g with respect to  $\mathbf{p}$  is extremely useful. It gives a measure of the sensitivity of our answer to the parameters **p** (which may, for example, come from some experimental measurements with some associated uncertainties). Or, we may want to perform an optimization of g, picking the p that produce some desired result; in this case the gradient indicates a useful search direction (e.g. for nonlinear conjugate-gradient optimization). For largescale optimization problems, the number P of design parameters can be hundreds, thousands, or morethis is common in shape or topology optimization, in which p controls the placement and shape of arbitrary blobs of different materials constituting a given structure/design. Sometimes, this process is called *inverse design*: finding the problem that yields a given solution instead of the other way around. When  $P \gg 1$ , the amazing efficiency of adjoint methods makes inverse design possible.

I hadn't found any textbook description of adjoint methods that I particularly like, which is part of my motivation for writing up these notes. One introduction can be found in [1], and a more general treatment can be found in [2]. Subsequently, Gil Strang wrote a nice introduction to adjoint methods in his book [3], including a discussion of the important topic of automatic differentiation (for which adjoint or "reverse" differentiation is a key idea).

### 2 Linear equations

Suppose that the column-vector  $\mathbf{x}$  solves the  $M \times M$  linear equation  $A\mathbf{x} = \mathbf{b}$  where we take  $\mathbf{b}$  and A to be real<sup>1</sup> and to depend in some way on  $\mathbf{p}$ . To evaluate the gradient directly, we would do

$$\frac{dg}{d\mathbf{p}} = g_{\mathbf{p}} + g_{\mathbf{x}}\mathbf{x}_{\mathbf{p}}$$

where the subscripts indicate partial derivatives ( $g_{\mathbf{x}}$  is a row vector,  $\mathbf{x}_{\mathbf{p}}$  is an  $M \times P$  matrix, etc.). Since g is a given function,  $g_{\mathbf{p}}$  and  $g_{\mathbf{x}}$  are presumably easy to compute. On the other hand, computing  $\mathbf{x}_{\mathbf{p}}$  is hard: evaluating it directly by differentiating  $A\mathbf{x} = \mathbf{b}$  by a parameter  $p_i$  gives  $\mathbf{x}_{p_i} = A^{-1}(\mathbf{b}_{p_i} - A_{p_i}\mathbf{x})$ . That is, we would have to solve an  $M \times M$  linear equation for P right-hand sides, once for every compont of  $\mathbf{p}$ ; this is impractical if P and M are large.

More explicitly, the problematic term is:

$$g_{\mathbf{x}}\mathbf{x}_{\mathbf{p}} = \underbrace{g_{\mathbf{x}}}_{1 \times M} \underbrace{[A^{-1}(\mathbf{b}_{\mathbf{p}} - A_{\mathbf{p}}\mathbf{x})]}_{M \times P} = \underbrace{[g_{\mathbf{x}}A^{-1}]}_{1 \times M} \underbrace{(\mathbf{b}_{\mathbf{p}} - A_{\mathbf{p}}\mathbf{x})}_{M \times P},$$

where  $A_{\mathbf{p}}\mathbf{x}$  denotes the  $M \times P$  matrix with columns  $A_{p_i}\mathbf{x}$  for  $i = 1, \dots P$ . One way of looking at the difficulty is that in the first equation we multiply a  $M \times M$  matrix by a  $M \times P$  matrix, which costs  $O(M^2P)$  work, or equivalently we have multiplications of  $A^{-1}$ 

<sup>&</sup>lt;sup>1</sup>This involves no loss of generality, since complex linear equations can always be written as real linear equations of twice the size by taking the real and imaginary parts as separate variables.

<sup>&</sup>lt;sup>2</sup>Technically,  $A_{\mathbf{p}}$  is a rank-3 tensor or "three-dimensional matrix," although it almost certainly isn't stored this way. For example,  $A_{p_i}\mathbf{x}$  could be computed for each i separately without saving  $A_{p_i}$ . Often,  $A_{p_i}$  will be very sparse.

by P vectors (i.e., solves of P right-hand sides, which in practice would likely use a factorization of A or an iterative solver rather than explicitly computing  $A^{-1}$ ).<sup>3</sup> However, this can be ameliorated simply by parenthesizing in a different way [3],<sup>4</sup> as shown in the last expression. If we multiply  $\lambda^T = g_x A^{-1}$  first, that corresponds to only a single solution of an adjoint equation<sup>5</sup>

$$A^T \lambda = g_{\mathbf{x}}^T. \tag{1}$$

and then we multiply a *single* vector  $\boldsymbol{\lambda}^T$  by our  $M \times P$  matrix for only  $\theta(MP)$  work. Putting it all together, we obtain:

$$\frac{dg}{d\mathbf{p}}_{\mathbf{f}=0} = g_{\mathbf{p}} - \boldsymbol{\lambda}^T \mathbf{f}_{\mathbf{p}} = g_{\mathbf{p}} - \boldsymbol{\lambda}^T (A_{\mathbf{p}} \mathbf{x} - \mathbf{b}_{\mathbf{p}}).$$

Again,  $A(\mathbf{p})$  and  $\mathbf{b}(\mathbf{p})$  are presumably specified analytically and thus  $A_{\mathbf{p}}$  and  $\mathbf{b}_{\mathbf{p}}$  can easily be computed (in some cases automatically, by automatic program differentiators such as ADIFOR). Note that the adjoint problem is of the same size as the original  $A\mathbf{x} = \mathbf{b}$  system, can use the same factorization (e.g. LU factorization A = LU immediately gives  $A^T = U^T L^T$ ), has the same condition number, and has the same spectrum of eigenvalues (the eigenvalues of A and  $A^T$  are identical) so iterative algorithms will have similar performance (and can use similar preconditioners)—in every sense, solving the adjoint problem should be no harder than solving the original problem.

# 3 Nonlinear equations

If **x** satisfies some general, possibly nonlinear, equations  $\mathbf{f}(\mathbf{x}, \mathbf{p}) = 0$ , the process is almost exactly the same. Differentiating the **f** equation, we find  $\mathbf{f}_{\mathbf{x}}\mathbf{x}_{\mathbf{p}}$  +

 $\mathbf{f_p} = 0$  and thus  $\mathbf{x}_p = -\mathbf{f_x}^{-1}\mathbf{f_p}$ . Hence, we write

$$\frac{dg}{d\mathbf{p}} = g_{\mathbf{p}} + g_{\mathbf{x}}\mathbf{x}_{\mathbf{p}} = g_{\mathbf{p}} - \underbrace{g_{\mathbf{x}}}_{1 \times M} \underbrace{\left[\mathbf{f}_{\mathbf{x}}^{-1}, \mathbf{f}_{\mathbf{p}}\right]}_{1 \times M} = g_{\mathbf{p}} - \underbrace{\left[g_{\mathbf{x}}\mathbf{f}_{\mathbf{x}}^{-1}\right]}_{1 \times M} \underbrace{\mathbf{f}_{\mathbf{p}}}_{M \times P}.$$

We solve for x by whatever method, then solve for  $\lambda$  from

$$\mathbf{f}_{\mathbf{v}}^{T} \boldsymbol{\lambda} = \mathbf{g}_{\mathbf{v}}^{T}, \tag{2}$$

and finally obtain

$$\frac{d\mathbf{g}}{d\mathbf{p}}_{\mathbf{f}=0} = \mathbf{g}_{\mathbf{p}} - \boldsymbol{\lambda}^T \mathbf{f}_{\mathbf{p}}.$$
 (3)

The only difference is that the adjoint equation (2) is not simply the adjoint of the equation for  $\mathbf{x}$ . Still, it is a single  $M \times M$  linear equation for  $\lambda$  that should be of comparable (or lesser) difficulty to solving for  $\mathbf{x}$ .

# 4 Eigenproblems

As a more complicated example illustrating the use of equations (2) and (3) from the previous sections, let us suppose that we are solving a linear eigenproblem  $A\mathbf{x} = \alpha \mathbf{x}$  and looking at some function  $g(\mathbf{x}, \alpha, \mathbf{p})$ . For simplicity, assume that A is real-symmetric and that  $\alpha$  is simple (non-degenerate; i.e.,  $\mathbf{x}$  is the only eigenvector for  $\alpha$ ). In this case, we now have M+1 unknowns described by the column vector:

$$\tilde{\mathbf{x}} = \begin{pmatrix} \mathbf{x} \\ \alpha \end{pmatrix}.$$

The eigenequation  $\mathbf{f} = A\mathbf{x} - \alpha\mathbf{x}$  only gives us M equations and doesn't completely determine  $\tilde{\mathbf{x}}$ , for two reasons. First, of course, there are many possible eigenvalues, but let's assume that we have picked one in some fashion (e.g. the smallest  $\alpha$ , or the  $\alpha$  closest to  $\pi$ , or the third largest  $|\alpha|$ , or ...). Second, the eigenequation does not determine the length  $|\mathbf{x}|$ ; let's arbitrarily pick  $|\mathbf{x}| = 1$  or  $\mathbf{x}^T\mathbf{x} = 1$ . This gives us M+1 equations  $\tilde{\mathbf{f}} = 0$  where:

$$\tilde{\mathbf{f}} = \begin{pmatrix} \mathbf{f} \\ \mathbf{x}^T \mathbf{x} - 1 \end{pmatrix}.$$

 $<sup>^{3}</sup>$ If M is sparse, then the cost might be significantly less than this  $O(M^{2}P)$  upper bound, but in any case solving P right-hand sides will be significantly more costly than solving a single right-hand side for the adjoint formulation.

<sup>&</sup>lt;sup>4</sup>Another way of looking at this, and the source of the  $\lambda$  notation, is to think of sort of a "Lagrange multiplier" process: replace g with  $\tilde{g} = g - \lambda^T \mathbf{f}$  by adding a multiple  $\lambda$  of  $\mathbf{f} = 0$ , and then choose  $\lambda$  is a clever way to cancel the annoying derivative term. This gives the same result, and may be easier to generalize to some more complicated circumstances, however, such as differential-algebraic equations [2].

<sup>&</sup>lt;sup>5</sup>For complex-valued **x** and *A* and real *g*, instead of the transpose  $A^T$  one typically obtains the adjoint  $A^{\dagger} = A^{T*}$  (the conjugate-transpose).

<sup>&</sup>lt;sup>6</sup>Problems involving degenerate eigenvalues occur surprisingly often in optimization of eigenvalues (e.g. when maximizing the minimum eigenvalue of some system), and must be treated with special care. In that case, a generalization of the gradient is required to determine sensitivities or the steepest-descent direction [4], a more elaborate version of what is called *degenerate* perturbation theory in quantum mechanics [?].

We'll need M + 1 adjoint variables  $\tilde{\lambda}$ :

$$\tilde{\boldsymbol{\lambda}} = \left( \begin{array}{c} \boldsymbol{\lambda} \\ \boldsymbol{\beta} \end{array} \right).$$

The adjoint equations (2) then give:

$$(A - \alpha)\lambda = g_{\mathbf{x}}^T - 2\beta \mathbf{x},\tag{4}$$

$$-\mathbf{x}^T \boldsymbol{\lambda} = g_{\alpha}. \tag{5}$$

The first equation, at first glance, seems to be problematic:  $A - \alpha$  is singular, with a null space of  $\mathbf{x}$ . It's, okay, though! First, we have to choose  $\beta$  so that solutions of equation (4) *exist*: the right-hand side must be orthogonal to  $\mathbf{x}$  so that it is not in the null space of  $A - \alpha$ . That is, we must have  $\mathbf{x}^T(g_{\mathbf{x}}^T - 2\beta \mathbf{x}) = 0$ , and thus  $\beta = \mathbf{x}^T g_{\mathbf{x}}^T/2$  (since  $\mathbf{x}^T \mathbf{x} = 1$ ), and therefore  $\lambda$  satisfies:

$$(A - \alpha)\lambda = (1 - \mathbf{x}\mathbf{x}^T)g_{\mathbf{x}}^T = Pg_{\mathbf{x}}^T$$
 (6)

where  $P = 1 - \mathbf{x}\mathbf{x}^T$  is the projection operator into the space orthogonal to  $\mathbf{x}$ . This equation then has a solution, and in fact it has infinitely many solutions: we can add any multiple of  $\mathbf{x}$  to  $\boldsymbol{\lambda}$  and still have a solution. Equivalently, we can write  $\boldsymbol{\lambda} = \boldsymbol{\lambda}_0 + \gamma \mathbf{x}$  for  $\mathbf{x}^T \boldsymbol{\lambda}_0 = 0$  and some  $\gamma$ . Fortunately,  $\gamma$  is determined by (5):  $\gamma = -g_{\alpha}$ . Finally, with  $\boldsymbol{\lambda}_0$  determined by (6), we can find the desired gradient via (3):

$$\frac{dg}{d\mathbf{p}}_{\mathbf{f}=0} = g_{\mathbf{p}} - \boldsymbol{\lambda}^T A_p \mathbf{x} = g_{\mathbf{p}} - \boldsymbol{\lambda}_0^T A_p \mathbf{x} + g_{\alpha} \mathbf{x}^T A_p \mathbf{x}.$$
(7)

If we compare with  $\frac{dg}{d\mathbf{p}} = g_{\mathbf{p}} + g_{\mathbf{x}}\mathbf{x}_{\mathbf{p}} + g_{\alpha}\alpha_{\mathbf{p}}$ , we immediately see that  $\alpha_{\mathbf{p}} = \mathbf{x}^T A_p \mathbf{x}$ . This is a well-known result from quantum physics and perturbation theory, where it is known as the Hellman-Feynman theorem.

# 5 Example inverse design

As a more concrete example of an inverse-design problem, let's consider the Schrodinger eigen-equation in one dimension,

$$\left[ -\frac{d^2}{dx^2} + V(x) \right] \psi(x) = E \psi(x),$$

with periodic boundaries  $\psi(x+2) = \psi(x)$ . Normally, we take a given V(x) and solve for  $\psi$  and E.

Figure 1: Optimized V(x) (scaled by 1/1000) and  $\psi(x)$  for  $\psi_0(x) = 1 + \sin[\pi x + \cos(3\pi x)]$  after 500 cg iterations.

Now, however, we will specify a particular  $\psi_0(x)$  and find the V(x) that gives  $\psi(x) \approx \psi_0(x)$  for the ground-state eigenfunction (i.e. for the smallest eigenvalue E). In particular, we will find the V(x) that minimizes

$$g = \int_{-1}^{1} |\psi(x) - \psi_0(x)|^2 dx.$$

To solve this numerically, we will discretize the interval  $x \in [-1,1)$  with M equally-spaced points  $x_n = n\Delta x$  ( $\Delta x = \frac{2}{M+1}$ ), and solve for the solution  $\psi(x_n)$  at these points, denoted by the vector  $\boldsymbol{\psi}$ . That is, to compare with the notation of the previous sections, we have the eigenvector  $\mathbf{x} = \boldsymbol{\psi}$ , the eigenvalue  $\alpha = E$ , and the parameters  $V(x_n)$  or  $\mathbf{p} = \mathbf{V}$ . If we discretize the eigenoperator with the usual center-difference scheme, we get  $A\boldsymbol{\psi} = E\boldsymbol{\psi}$  for:

$$A = \frac{1}{\Delta x^2} \begin{pmatrix} 2 & -1 & 0 & \cdots & 0 & -1 \\ -1 & 2 & -1 & 0 & \cdots & \\ 0 & -1 & 2 & -1 & 0 & \cdots \\ \vdots & & & \ddots & & \\ & & & -1 & 2 & -1 \\ -1 & 0 & \cdots & 0 & -1 & 2 \end{pmatrix} + \operatorname{diag}(\mathbf{V}).$$

As before, we normalize  $\psi$  (and  $\psi_0$ ) to  $\psi^T \psi = 1,^8$  giving a projection operator  $P = 1 - \psi \psi^T$  (or  $P = 1 - |\psi\rangle\langle\psi|$ , in Dirac notation). The discrete version of g is now

$$g(\boldsymbol{\psi}, \mathbf{V}) = (\boldsymbol{\psi} - \boldsymbol{\psi}_0)^T (\boldsymbol{\psi} - \boldsymbol{\psi}_0) \Delta x$$

<sup>&</sup>lt;sup>7</sup>Since *P* commutes with  $A - \alpha$ , we can solve for  $\lambda_0$  easily by an iterative method such as conjugate gradient: if we start with an initial guess orthogonal to  $\mathbf{x}$ , all subsequent iterates will also be orthogonal to  $\mathbf{x}$  and will thus converge to  $\lambda_0$  (except for roundoff, which can be corrected by multiplying the final result by *P*).

<sup>&</sup>lt;sup>8</sup>We also have an arbitrary choice of sign, which we fix by choosing  $\int \psi dx > 0$ .

where  $\psi_0$  is  $\psi_0(x_n)$ , our target eigenfunction. Therefore,  $g_{\psi} = 2(\psi - \psi_0)^T \Delta x$  and thus, by eq. (6), we find  $\lambda$  via:

$$(A-E)\lambda = 2P(\psi - \psi_0)\Delta x, \tag{8}$$

with  $P\lambda = 0$  ( $\lambda = \lambda_0$  since  $g_E = 0$ ).  $g_V$  and  $g_E$  are both 0. Moreover,  $A_{V_n}$  is simply the matrix with 1 at (n,n) and 0's elsewhere, and thus from (7):

$$\frac{dg}{dV_n} = -\lambda_n \psi_n$$

or equivalently  $\frac{dg}{d\mathbf{V}} = -\lambda \quad \psi$  where is the pointwise product (.\* in Matlab).

Whew! Now how do we solve these equations numerically? This is illustrated by the Matlab function  $schrodinger_fd_adj$  given below. We set up A as a sparse matrix, then find the smallest eigenvalue and eigenvector via the eigs function (which uses an iterative Arnoldi method). Then we solve (8) for  $\lambda$  via the Matlab pcg function (preconditioned conjugate-gradient, although we don't bother with a preconditioner).

Then, given g and  $\frac{dg}{dV}$ , we then just plug it into some optimization algorithm. In particular, nonlinear conjugate gradient seems to work well for this problem.<sup>9</sup>

#### 5.1 Optimization results

In this section, we give a few example results from running the above procedure (nonlinear cg optimization) for M = 100. As the starting guess for our optimization, we'll just use V(x) = 0. That is, we are doing a *local optimization* in a *100-dimensional space*, using the adjoint method to get the gradient. It is somewhat remarkable that this works—in a few seconds on a PC, it converges to a very good solution!

We'll try a couple of example  $\psi_0(x)$  functions. To start with, let's do  $\psi_0(x) = 1 + \sin[\pi x + \cos(3\pi x)]$ . (Note that the ground-state  $\psi$  will never have any nodes, so we require  $\psi_0 \ge 0$  everywhere.) This  $\psi_0(x)$ , along with the resulting  $\psi(x)$  and V(x) after 500 cg iterations, are shown in figure 1. The solution  $\psi(x)$  matches  $\psi_0(x)$  very well except for a couple of small ripples, and V(x) is quite complicated—not something you could easily guess!

http://www2.imm.dtu.dk/~hbn/Software/

Figure 2: Optimized V(x) (scaled by 1/10000) and  $\psi(x)$  for  $\psi_0(x) = 1 - |x|$  for |x| < 0.5, after 5000 cg iterations.

Figure 3: Optimized  $\psi(x)$  for  $\psi_0(x) = 1 - |x|$  for |x| < 0.5, after various numbers of nonlinear conjugate-gradient iterations (from 10 to 10000).

Oh, but that  $\psi_0$  was too easy! Let's try one with discontinuities:  $\psi_0(x) = 1 - |x|$  for |x| < 0.5 and 0 otherwise (which looks a bit like a "house"). This  $\psi_0(x)$ , along with the resulting  $\psi(x)$  and V(x) after 500 cg iterations, are shown in figure 2. Amazingly, it still captures  $\psi_0$  pretty well, although it has a bit more trouble with the discontinuities than with the slope discontinuity. This time, we let it converge for 5000 cg iterations to give it a bit more time. Was this really necessary? In figure 3, we plot  $\psi(x)$  for 10, 20, 40, 80, 160, 320, and 5000 cg iterations. It gets the rough shape pretty quickly, but the discontinuous features are converging fairly slowly. (Presumably this could be improved if we found a good preconditioner, or perhaps by a different optimization method or objective function.)

#### 5.2 Matlab code

The following code solves for g and  $\frac{dg}{d\mathbf{V}}$ , not to mention the eigenfunction  $\boldsymbol{\psi}$  and the corresponding eigenvalue E, for a given  $\mathbf{V}$  and  $\boldsymbol{\psi}_0$ .

```
% Usage: [g,gp,E,psi] = schrodinger_fd_adj(x, V, psi0)
%
% Given a column-vector x(:) of N equally spaced x points a
% V of the potential V(x) at those points, solves Schroding
                 [-d^2/dx^2 + V(x)] psi(x) = E psi(x)
% with periodic boundaries for the lowest "ground state" ei
% wavefunction psi.
% Furthermore, it computes the function g = integral |psi -
% the gradient gp = dg/dV (at each point x).
function [g,gp,E,psi] = schrodinger_fd_adj(x, V, psi0)
  dx = x(2) - x(1);
  N = length(x);
  A = \text{spdiags}([\text{ones}(N,1), -2 * \text{ones}(N,1), \text{ones}(N,1)], -1:1,
  A(1,N) = 1;
  A(N,1) = 1;
  A = - A / dx^2 + spdiags(V, 0, N,N);
  opts.disp = 0;
  [psi,E] = eigs(A, 1, 'sa', opts);
  E = E(1,1);
  if sum(psi) < 0
    psi = -psi; % pick sign; note that psi' * psi = 1 from
  end
  gpsi = psi - psi0;
  g = gpsi' * gpsi * dx;
  gpsi = gpsi * 2*dx;
  P = Q(x) x - psi * (psi' * x); % projection onto direction
  [lambda,flag] = pcg(A - spdiags(E*ones(N,1), 0, N,N), P(g)
  lambda = P(lambda);
  gp = -real(conj(lambda) .* psi);
  disp(g);
```

## 6 Initial-value problems

So far, we have looked at  $\mathbf{x}$  that are determined by "simple" algebraic equations (which may come from a PDE, etcetera). What if, instead, we are determining  $\mathbf{x}$  by integrating a set of equations in *time*? The simplest example of this is an initial-value problem for a linear, time-independent, homogeneous set of ODEs:

$$\dot{\mathbf{x}} = B\mathbf{x}$$

whose solution after a time *t* for  $\mathbf{x}(0) = \mathbf{b}$  is formally:

$$\mathbf{x} = \mathbf{x}(t) = e^{Bt}\mathbf{b}.$$

This, however, is exactly a linear equation  $A\mathbf{x} = \mathbf{b}$  with  $A = e^{-Bt}$ , so we can just quote our results from earlier! That is, suppose we are optimizing (or evaluating the sensitivity) of some function  $g(\mathbf{x}, \mathbf{p})$  based on the solution  $\mathbf{x}$  at time t. Then we find the adjoint vector  $\boldsymbol{\lambda}$  via (1):

$$e^{-B^T t} \lambda = g_{\mathbf{v}}^T$$
.

Equivalently,  $\lambda$  is the exactly the solution  $\lambda(t)$  after a time t of its own adjoint ODE:

$$\dot{\lambda} = R^T \lambda$$

with initial condition  $\lambda(0) = g_{\mathbf{x}}^T$ . We should have expected this by now: solving for  $\lambda$  always involves a task of similar complexity to finding  $\mathbf{x}$ , so if we found  $\mathbf{x}$  by integrating an ODE then we find  $\lambda$  by an ODE too! Of course, we need not solve these ODEs by matrix exponentials; we can use Runge-Kutta, forward Euler, or (if B comes from a PDE) whatever scheme we deem appropriate (e.g. Crank-Nicolson).

One important property to worry about is *stability*, and here we are in luck. The eigenvalues of B and  $B^T$  are complex-conjugates, and so if one is stable (eigenvalues with absolute values  $\leq 1$ ) then the other is!

Finally, we can write down the gradient  $\frac{dg}{d\mathbf{p}}$  via equation (3):

$$\frac{dg}{d\mathbf{p}} = g_{\mathbf{p}} - \boldsymbol{\lambda}^T (A_{\mathbf{p}} \mathbf{x} - \mathbf{b}_{\mathbf{p}}).$$

Now, since  $A = e^{-Bt}$ , one might be tempted to write  $A_{\mathbf{p}} = -B_{\mathbf{p}}t \cdot A$ , but this is not true except in the *very* special case where  $B_{\mathbf{p}}$  commutes with B! Unfortunately, the general expression for differentiating a

matrix exponential turns out to be more complicated:  $A_{\mathbf{p}} = -\int_0^t e^{-Bt'} B_{\mathbf{p}} e^{-B(t-t')} dt'$ , and so,

$$\frac{dg}{d\mathbf{p}} = g_{\mathbf{p}} + \int_0^t \boldsymbol{\lambda}^T (t - t') B_{\mathbf{p}} \mathbf{x}(t') dt' + \boldsymbol{\lambda}^T \mathbf{b}_{\mathbf{p}}.$$

This is especially unfortunate because it usually means that we have to *store*  $\mathbf{x}(t')$  at all times  $0 \le t' \le t$  in order to compute the integral. Adjoint methods are storage-intensive for time-dependent problems!

More generally, of course, one might wish to include time-varying A, nonlinearities, inhomogeneous (source) terms, etcetera, into the equations to integrate. A very general formulation of the problem, for differential-algebraic equations (DAEs), can be found in [2]. A similar general principle remains, however: the adjoint variable  $\lambda$  is determined by integrating a similar (adjoint) DAE, using the final value of  $\mathbf{x}(t)$  to compute the *initial* condition of  $\boldsymbol{\lambda}(0)$ . In fact, the  $\lambda(t)$  equation is actually often interpreted as being integrated backwards in time from t to 0. Alternatively, one can consider a "discrete-time" situation of recurrence equations, in which case the adjoint problem is a recurrence "backward in time" see my online notes on adjoint methods for recurrences.

## References

- [1] R. M. Errico, "What is an adjoint model?," *Bulletin Am. Meteorological Soc.*, vol. 78, pp. 2577–2591, 1997.
- [2] Y. Cao, S. Li, L. Petzold, and R. Serban, "Adjoint sensitivity analysis for differential-algebraic equations: The adjoint DAE system and its numerical solution," *SIAM J. Sci. Comput.*, vol. 24, no. 3, pp. 1076–1089, 2003.
- [3] G. Strang, Computational Science and Engineering. Wellesley, MA: Wellesley-Cambridge Press, 2007.
- [4] A. P. Seyranian, E. Lund, and N. Olhoff, "Multiple eigenvalues in structural optimization problems," *Structural Optimization*, vol. 8, pp. 207–227, 1994.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

# 18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# Adjoint methods and sensitivity analysis for recurrence relations

Steven G. Johnson

Created October 2007, updated November 9, 2011.

#### 1 Introduction

In this note, we derive an adjoint method for sensitivity analysis of the solution of recurrence relations. In particular, we suppose that we have a M-component vector  $\mathbf{x}$  that is determined by iterating a recurrence relation

$$\mathbf{x}^n = \mathbf{f}(\mathbf{x}^{n-1}, \mathbf{p}, n) \triangleq \mathbf{f}^n$$

for some function  $\mathbf{f}$  depending on the previous  $\mathbf{x}$ , a vector  $\mathbf{p}$  of P parameters, and the step index n. The initial condition is

$$\mathbf{x}^0 = \mathbf{b}(\mathbf{p})$$

for some given function  $\mathbf{b}$  of the parameters. Furthermore, we have some function g of  $\mathbf{x}$ .

$$g^n \triangleq g(\mathbf{x}^n, \mathbf{p}, n)$$

and we wish to compute the gradient  $\frac{dg^N}{d\mathbf{p}}$  of  $g^N$ , for some N, with respect to the parameters  $\mathbf{p}$ .

## 2 The explicit gradient

The gradient of  $g^N$  can be written explicitly as:

$$\frac{dg^{N}}{d\mathbf{p}} = g_{\mathbf{p}}^{N} + g_{\mathbf{x}}^{N} \left( \mathbf{f}_{\mathbf{p}}^{N} + \mathbf{f}_{\mathbf{x}}^{N} \left[ \mathbf{f}_{\mathbf{p}}^{N-1} + \mathbf{f}_{\mathbf{x}}^{N-1} \left\{ \mathbf{f}_{\mathbf{p}}^{N-2} + \cdots \right\} \right] \right), \tag{1}$$

where subscripts denote partial derivatives, and should be thought of as row vectors, vs. column vectors  $\mathbf{x}$  and  $\mathbf{p}$ . So, for example,  $g_{\mathbf{x}}^N$  is a  $1 \times M$  matrix, and  $\mathbf{f}_{\mathbf{p}}^N$  is a  $M \times P$  matrix. Equation (1) is derived simply by applying the chain rule to  $g^N = g(\mathbf{x}^n, \mathbf{p}) = g(f(\mathbf{x}^{n-1}, \mathbf{p}), \mathbf{p}) = g(f(f(\mathbf{x}^{n-2}, \mathbf{p}), \mathbf{p}), \mathbf{p}) = \cdots$ .

<sup>&</sup>lt;sup>1</sup>Note that if  $\mathbf{x}^n$  depends on  $\mathbf{x}^{n-\ell}$  for  $\ell=1,\ldots,L$ , the recurrence can still be cast in terms of  $\mathbf{x}^{n-1}$  alone by expanding  $\mathbf{x}$  into a vector of length ML, in much the same way that an Lth-order ODE can be converted into L 1st-order ODEs.

The natural way to evaluate eq. (1) might seem to be starting at the innermost parentheses and working outwards, but this is inefficient. Each parenthesized expression is a  $M \times P$  matrix that must be multiplied by  $\mathbf{f}_{\mathbf{x}}^n$ , a  $M \times M$  matrix, requiring  $O(M^2P)$  time for each multiplication assuming dense matrices. There are O(N) such multiplications, so evaluating the whole expression in this fashion requires  $O(NM^2P)$  time. However, for dense matrices, the evaluation of  $g^N$  itself requires  $O(NM^2)$  time, which means that the gradient (calculated this way) is as expensive as O(P) evaluations of  $g^N$ .

Similarly, evaluating gradients by finite-difference approximations or similar numerical tricks requires O(P) evaluations of the function being differentiated (e.g. center-difference approximations require two function evaluations per dimension). So, direct evaluation of the gradient by the above technique, while it may be more accurate than numerical approximations, is not substantially more efficient. This is a problem if P is large.

#### 3 The gradient by adjoints

Instead of computing the gradient explicitly (by "forward" differentiation), *adjoint methods* typically allow one to compute gradients with the same cost as evaluating the function roughly twice, regardless of the number P of parameters [1, 2, 3, 4]. A very general technique for constructing adjoint methods involves something similar to Lagrange multipliers, where one adds zero to  $g^N$  in a way cleverly chosen to make computing the gradient easier, and in a previous note I derived the adjoint gradient for recurrence relations by this technique, analogous to work by Cao and Petzold on adjoint methods for differential-algebraic equations [2]. However, Gil Strang has pointed out to me that in many cases adjoint methods can be derived much more simply just by parenthesizing the gradient equation in a different way [4], and this turns out to be the case for the recurrence problem above.

The key fact is that, in the gradient equation (1), we are evaluating lots of expressions like  $g_{\mathbf{x}}^N(\mathbf{f}_{\mathbf{x}}^N\mathbf{f}_{\mathbf{p}}^{N-1})$ ,  $g_{\mathbf{x}}^N(\mathbf{f}_{\mathbf{x}}^N\mathbf{f}_{\mathbf{p}}^{N-2}]$ ), and so on. Parenthesized this way, these expressions require  $O(M^2P)$  operations each, because they involve matrix-matrix multiplications. However, we can parenthesize them a different way, so that they involve only vector-matrix multiplications, in order to reduce the complexity to  $O(M^2+MP)$ , which is obviously a huge improvement for large M and P. In particular, parenthesize them as  $(g_{\mathbf{x}}^N\mathbf{f}_{\mathbf{x}}^N)\mathbf{f}_{\mathbf{p}}^{N-1}$ ,  $[(g_{\mathbf{x}}^N\mathbf{f}_{\mathbf{x}}^N)\mathbf{f}_{\mathbf{x}}^{N-1}]\mathbf{f}_{\mathbf{p}}^{N-2}$ , and so on, involving repeated multiplication of a row vector on the left (starting with  $g_{\mathbf{x}}^N$ ) by a matrix  $\mathbf{f}_{\mathbf{x}}^n$  on the right. This repeated multiplication defines an *adjoint recurrence* relation for a M-component column vector  $\lambda^n$ , recurring backwards from n=N to n=0:

$$\lambda^{n-1} = (\mathbf{f}_{\mathbf{x}}^n)^T \lambda^n,$$

where T is the transpose, with "initial" condition

$$\lambda^N = \left(g_{\mathbf{x}}^N\right)^T.$$

In terms of this adjoint vector (so-called because of the transposes in the expressions

above), the gradient becomes:

$$\frac{dg^N}{d\mathbf{p}} = g_{\mathbf{p}}^N + \sum_{n=1}^N (\lambda^n)^T \mathbf{f}_{\mathbf{p}}^n + (\lambda^0)^T \mathbf{b}_{\mathbf{p}}.$$
 (2)

Consider the computational cost to evaluate the gradient in this way. Evaluating  $g^N$  and the  $\mathbf{x}^n$  costs  $O(NM^2)$  time, assuming dense matrices, and evaluating  $\lambda^n$  also takes  $O(NM^2)$  time. Finally evaluating equation (2) takes O(NMP) time in the worst case, dominated by the time to evaluate the summation assuming  $\mathbf{f}_{\mathbf{p}}^n$  is a dense matrix. So, the total is  $O(NM^2 + NMP)$ , much better than  $O(NM^2P)$  for large M and P.

In practice, the situation is likely to be even better than this, because often  $\mathbf{f}_{\mathbf{p}}^n$  will be a sparse matrix: each component of  $\mathbf{p}$  will appear only for certain components of  $\mathbf{x}$  and or for certain steps n. In this case the O(NMP) cost will be greatly reduced, e.g. to O(NM) or O(MP) or similar. Then the cost of the gradient will be dominated by the two  $O(NM^2)$  recurrences—i.e., as is characteristic of adjoint methods, the cost of finding the gradient will be comparable to the cost of finding the function value twice.

Note that there is, however, at least one drawback of the adjoint method (2) in comparison to the direct method (1): the adjoint method may require more storage. For the direct method, O(M) storage is required for the current  $\mathbf{x}^n$  (which can be discarded once  $\mathbf{x}^{n+1}$  is computed) and O(PM) storage is required for the  $M \times P$  matrix being accumulated, to be multiplied by  $g_{\mathbf{x}}^N$  at the end, for O(PM) storage total. In the adjoint method, all of the  $\mathbf{x}^n$  must be stored, because they are used in the backwards recurrence for  $\lambda^n$  once  $\mathbf{x}^N$  is reached, requiring O(NM) storage. [The  $\lambda^n$  vectors, on the other hand, can be discarded once  $\lambda^{n-1}$  is computed, assuming the summation in eq. (2) is computed on the fly. Only O(M) storage is needed for this summation, assuming  $\mathbf{f}_{\mathbf{p}}^n$  can be computed on the fly (or is sparse).] Whether the O(PM) storage for the direct method is better or worse than the O(NM) storage for the adjoint method obviously depends on how P compares to N.

### 4 A simple example

Finally, let us consider a simple example of a M=2 linear recurrence:

$$\mathbf{x}^n = A\mathbf{x}^{n-1} + \begin{pmatrix} 0 \\ p_n \end{pmatrix}$$

with an initial condition

$$\mathbf{x}^0 = \mathbf{b} = \begin{pmatrix} 1 \\ 0 \end{pmatrix}$$

and some  $2 \times 2$  matrix A, e.g.

$$A = \begin{pmatrix} \cos \theta & \sin \theta \\ -\sin \theta & \cos \theta \end{pmatrix}$$

for  $\theta = 0.1$ . Here, P = N: there are N parameters  $p_n$ , one per step n, acting as "source" terms in the recurrence (which otherwise has oscillating solutions since A is unitary).

Let us also pick a simple function g to differentiate, e.g.

$$g(\mathbf{x}) = (x_2)^2$$
.

The adjoint recurrence for  $\lambda^n$  is then:

$$\lambda^{n-1} = (\mathbf{f}_{\mathbf{x}}^n)^T \lambda^n = A^T \lambda^n,$$

with "initial" condition:

$$\lambda^N = \left(g_{\mathbf{x}}^N\right)^T = \left(\begin{array}{c} 0\\ 2x_2^N \end{array}\right).$$

Notice that this case is rather simple: since our recurrence is linear, the adjoint recurrence does not depend on  $\mathbf{x}^n$  except in the initial condition.

The gradient is also greatly simplified because  $\mathbf{f}_{\mathbf{p}}^n$  is sparse: it is a  $2 \times N$  matrix of zeros, except for the *n*-th column which is  $(0,1)^T$ . That means that the gradient (2) becomes:

$$\frac{dg^N}{dp_k} = \lambda_2^k,$$

requiring O(N) work to find the whole gradient.

As a quick test, I implemented this example in GNU Octave (a Matlab clone) and checked it against the numerical center-difference gradient; it only takes a few minutes to implement and is worthwhile to try if you are not clear on how this works. For extra credit, try modifying the recurrence, e.g. to make  $\bf f$  nonlinear in  $\bf x$  and/or  $\bf p$ .

#### References

- [1] R. M. Errico, "What is an adjoint model?," *Bulletin Am. Meteorological Soc.*, vol. 78, pp. 2577–2591, 1997.
- [2] Y. Cao, S. Li, L. Petzold, and R. Serban, "Adjoint sensitivity analysis for differential-algebraic equations: The adjoint DAE system and its numerical solution," *SIAM J. Sci. Comput.*, vol. 24, no. 3, pp. 1076–1089, 2003.
- [3] S. G. Johnson, "Notes on adjoint methods for 18.336." Online at http://math.mit.edu/stevenj/18.336/adjoint.pdf, October 2007.
- [4] G. Strang, *Computational Science and Engineering*. Wellesley, MA: Wellesley-Cambridge Press, 2007.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

# 18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# Quasi-Newton optimization: Origin of the BFGS update

Steven G. Johnson, notes for 18.335 at MIT

April 25, 2019

#### Abstract

In a typical optimization setting we are provided with an objective function f(x) and its gradient  $\nabla f$  only. However, as these are evaluated for many different points x we can infer something about the second derivative ("Hessian") by watching how  $\nabla f$  changes, and by incorporating that information into our optimization algorithm we can accelerate convergence. This approach leads to "quasi-Newton" or "variable-metric" methods, so-called because they approximate an exact Newton step for  $\nabla f = 0$ . The most widely used method to approximate the Hessian is a BFGS update, and in these notes we survey the basic ideas underlying this important algorithm.

# 1 Newton steps and backtracking

Suppose that we are trying to solve

$$\min_{x \in \mathbb{R}^n} f(x)$$

and we are supplied a method to efficiently compute both f(x) and  $\nabla f$  (e.g. by an adjoint method).

On step k of optimization, let  $x^k$  be our current iterate, and let  $g^k = \nabla f|_{x^k}$ . If we had the **second derivative "Hessian" matrix**  $H^k$  as well  $(H^k_{ij} = \frac{\partial f}{\partial x_i \partial x_j}|_{x^k})$ , then we could try to make progress via second-order (quadratic) Taylor expansion

$$f(x^k + \delta) \approx f(x^k) + \delta^T g^k + \frac{1}{2} \delta^T H^k \delta = q(\delta).$$

Near a local minimum, H is positive-definite, and the minimum of  $q(\delta)$  is

$$\delta^k = -(H^k)^{-1}g^k.$$

In fact, this is exactly a **Newton step** in finding a root of  $\nabla f = 0$ , where we approximate the gradient near x by a first-order Taylor expansion

$$\nabla f|_{x+\delta} \approx g^k + H^k \delta.$$

However, we might run into a problem: the Newton step  $\delta$  might be so large that our Taylor expansion is not accurate, and  $f(x^k + \delta)$  might actually get worse. There are a couple of common approaches to fix this:

- 1. **Trust region**: minimize a  $q(\delta)$  only for  $\delta$  sufficiently small, i.e. in a "trust region." For example, a common choice is a spherical trust region  $\|\delta\|_2 < r^k$  for some radius  $r^k$ , in which case there is a nice result: strong duality holds, and we can optimize a convex dual problem. If the resulting step is not "acceptable" (see below), we can change the trust-region radius and try again.
- 2. Line search: We can minimize  $f(x^k + \alpha \delta^k)$  over  $\alpha \in \mathbb{R}$ , i.e. along the direction of the Newton step  $\delta^k$ . Usually minimizing this *exactly* is more trouble than it is worth just to take a single optimization step, so it is common to do an **inexact line search**: try different  $\alpha$  until the result is "acceptable" (see below).
- 3. **Backtracking**: Instead of exact line search, we try  $f(x^k + \alpha \delta^k)$  for  $\alpha = 1, \tau, \tau^2, \tau^3, \ldots$  where  $0 < \tau < 1$  is some parameter (e.g.  $\tau = 0.5$ ), until the result is "acceptable" (see below).

For both a trust region and backtracking line search we have to decide whether a given step  $\delta$  is acceptable. Naively, we can simply check whether  $f(x^k + \delta) < f(x^k)$ , but in practice it turns out that we want to impose stronger conditions — we only want to take steps  $\delta$  where our quadratic approximation  $q(\delta)$  is reasonably accurate. In practice, we typically impose one or both of the **Wolfe conditions** on the step  $\delta$ :

- 1.  $f(x^k + \delta) \leq f(x^k) + c_1 \delta^T g^k$  where  $0 < c_1 < 1$ , typically  $c_1 = 10^{-4}$ : f must decrease at least proportional to the prediction of the gradient  $g^k$ .
- 2.  $|\delta^T g^{k+1}| \leq c_2 |\delta^T g^k|$ , where  $g^{k+1} = \nabla f|_{x^k + \delta}$  and  $0 < c_2 < 1$ , e.g.  $c_2 = 0.9$ : the derivative  $\delta^T \nabla f$  along the search direction must decrease sufficiently. (Note that for an exact line search we will have  $g^{k+1} = 0$ .) This condition helps prevent trust-region or inexact line-search methods from taking steps  $\delta$  that are too small, and it also leads to a nice property of BFGS updates below.

# 2 Quasi-Newton/Variable-metric methods

The problem with Newton steps is that the exact Hessian is hard to come by when n is large. Even with adjoint methods, evaluating H exactly typically costs at least n times the cost of evaluating f once (it correspond to taking the gradient n times: one more gradient for each component of  $\nabla f$ ). When n is really large, just *storing* the H matrix ( $n^2$  numbers) might be impractical.

 $<sup>^1\</sup>mathrm{This}$  is called the "trust region problem," and is discussed in e.g. Boyd & Vandenberghe section 5.2.

Instead, "quasi" Newton methods (also called "variable-metric" methods) apply the same Newton steps above but use an **approximate Hessian**  $H^k$ , often a low-rank approximation (which can be stored and applied efficiently). In fact, since what is needed for the Newton step is  $(H^k)^{-1}$ , usually one stores a low-rank **approximate inverse Hessian**. To obtain this, we want to **iteratively** construct our approximate  $H^{k+1}$  (or  $(H^{k+1})^{-1}$ ) given only the gradient (first derivative) of f. Some desired properties of  $H^k$  are:

- 1. For a convex quadratic f(x),  $H^k$  should approach the exact Hessian as  $k \to \infty$  (i.e., as we apply our iterative update for many points and many gradient evaluations, approaching the minimum). In practice, what can typically be proved [6, 5, 3] is that for a convex quadratic f(x), the quasi-Newton method gives the exact minimum and the exact Hessian in n steps (in exact arithmetic).
- 2. Secant condition:

$$\underbrace{g^{k+1} - g^k}_{\gamma} = H^{k+1} \underbrace{(x^{k+1} - x^k)}_{\delta}.$$

This condition arises because it would be true of the exact Hessian for a quadratic f (see the  $\nabla f|_{x+\delta}$  Taylor expansion above). Equivalently,  $H^k$  must at least predict the change in the gradient on the k-th step.

- 3. Real-symmetric positive-definite. This makes our q(n) function convex and  $\delta^k = -(H^k)^{-1}g^k$  is in the "downhill" direction from  $x^k$ .
- 4.  $H^k$  should "remember" as much information from previous steps (i.e. the previous gradient evaluations) as possible. (We *don't* want to impose the secant conditions on all steps simultaneously, however, because this could quickly become impossible: f may not be exactly quadratic.)

The last criterion is rather vague and could lead to many possible quasi-Newton algorithms. However, it turns out that an extremely easy and powerful approach to "remembing" information is to simply **minimize the change in**  $H^k$ : we minimize  $||H^{k+1} - H^k||$  in some norm, or alternatively minimize  $||(H^{k+1})^{-1} - (H^k)^{-1}||$ . In the appropriate choice of norm, the latter leads to the famous "BFGS" update, which has lots of nice properties.

# 3 BFGS updates

This update, named for Broyden [1], Fletcher [2], Goldfarb [3], and Shanno [4], who wrote four *separate* papers that developed the approach in 1970, is obtained by solving

$$\min_{H\in\mathbb{R}^{n\times n}}\|H^{-1}-(H^k)^{-1}\|_W$$
 subject to  $H^{-1}\gamma=\delta$  and  $H^T=H$ 

That is, we minimize the change in  $H^{-1}$  subject to the second condition and require that it be real-symmetric (it will turn out that we get positive-definiteness "for free" below). Here,  $\| \cdots \|_W$  is a weighted Frobenius norm

$$\|A\|_W^2 = \frac{1}{2}\operatorname{tr}\left[WAWA^T\right] = \frac{1}{2}\|MAM^T\|_F^2 = \frac{1}{2}\operatorname{tr}\left[MAM^TMA^TM^T\right]$$

where  $W = M^T M$  is a positive-definite "weight" matrix to be chosen later (recall the identity  $\operatorname{tr} AB = \operatorname{tr} BA$ ). If we let  $E = H^{-1} - (H^k)^{-1}$ , require that the previous iterate  $H^k$  be symmetric, then this optimization problem equivalently becomes

$$\min_{E \in \mathbb{R}^{n \times n}} \|E\|_W^2$$

subject to 
$$Ey = r$$
 and  $E^T = E$ 

where  $y = \gamma$  and  $r = \delta - (H^k)^{-1} \gamma$ .<sup>2</sup> This optimization problem is, in fact, a **QP**: we are minimizing a convex quadratic objective subject to affine constraints. In consequence, strong duality holds and we can instead solve the Lagrange dual problem. Equivalently, we can solve the KKT conditions. It turns out that this leads to a very nice formula for the update E if we make the right choice of weight matrix W.

Let's apply duality, following Greenstadt [7] and Goldfarb [3]. We define Lagrange multipliers  $\lambda \in \mathbb{R}^n$  for the Ey-r=0 constraint and  $\Gamma^T \in \mathbb{R}^{n \times n}$  for the  $E-E^T=0$  constraint, and obtain the Lagrangian

$$L(E, \lambda, \Gamma) = \operatorname{tr} \left[ \frac{1}{2} W E W E^T + (E y - r) \lambda^T + \Gamma(E - E^T) \right].$$

Here, note that  $\operatorname{tr}\left[(Ey-r)\lambda^T\right]=\operatorname{tr}\left[\lambda^T(Ey-r)\right]=\lambda^T(Ey-r)$  is just the ordinary sum of n Lagrange multipliers  $\lambda_i$  times n constraints, but by re-ordering it into a rank-1 matrix we were able to combine it with the  $\|E\|_W^2$  trace. And  $\operatorname{tr}\left[\Gamma(E-E^T)\right]=\sum_{i,j}\Gamma_{ji}(E-E^T)_{ji}=\sum_{i,j}(\Gamma^T)_{ij}(E-E^T)_{ij}$  is a "Frobenius inner product" of the  $n^2$  Lagrange multipliers  $(\Gamma^T)_{ij}$  with the  $n^2$  constraints from  $E^T=E$ . Note that

$$\nabla_B \operatorname{tr}(BC) = \nabla_B \sum_{ij} B_{ij} C_{ji} = C^T,$$

where  $\nabla_B$  denotes the matrix of partial derivatives  $\frac{\partial \operatorname{tr}(BC)}{\partial B_{ij}} = C_{ji}$ , and similarly  $\nabla_B \operatorname{tr}(B^TC) = C$ . We can now solve the KKT conditions

$$\nabla_E L = 0 = WEW + \lambda y^T + \Gamma^T - \Gamma,$$
  

$$Ey - r = 0,$$
  

$$E^T - E = 0.$$

<sup>&</sup>lt;sup>2</sup>If alternatively we were minimizing  $||H - H^k||_W$ , we would get exactly the same form of minimization problem with  $E = H - H^k$ ,  $y = \delta$ , and  $r = \gamma - H^k \delta$ . This leads to an alternative quasi-Newton method, called the Davidon–Fletcher–Powell (DFP) method, that seems not to perform quite as well in practice. Intuitively, since  $H^{-1}$  is the quantity that appears in the Newton step, it is not too surprising that it is better to minimize the change in  $H^{-1}$  rather than the change in H.

subject to the constraints Ey = r and  $E^T = E$ . The first equation gives

$$E = -W^{-1} \left( \lambda y^T + \Gamma^T - \Gamma \right) W^{-1}.$$

The requirement that  $E = E^T$  then means that  $(\lambda y^T + \Gamma^T - \Gamma) = (\lambda y^T + \Gamma^T - \Gamma)^T$ , or equivalently

$$\Gamma^T - \Gamma = \frac{1}{2} \left( y \lambda^T - \lambda y^T \right)$$

and hence

$$E = -\frac{1}{2}W^{-1}(y\lambda^{T} + \lambda y^{T})W^{-1}.$$

Finally, the condition Ey = r now implies

$$y\lambda^T W^{-1}y + \lambda \left(y^T W^{-1}y\right) = -2Wr.$$

Since the  $(\cdots)$  term is a scalar, we can solve for

$$\lambda = -\frac{2Wr + y\lambda^T W^{-1}y}{y^T W^{-1}y}.$$

At first glance, this doesn't seem immediately helpful since there is a  $\lambda^T$  on the right hand side. But if we multiply both sides by  $y^TW^{-1}$  and transpose, we can solve for the unknown scalar  $\lambda^TW^{-1}y$ :

$$\lambda^T W^{-1} y = -\frac{2r^T y + y^T W^{-1} y \left(\lambda^T W^{-1} y\right)}{y^T W^{-1} y} \implies \lambda^T W^{-1} y = -\frac{r^T y}{y^T W^{-1} y}.$$

Plugging this back into  $\lambda = \cdots$ , we get

$$\lambda = -\frac{2Wr + -\frac{yr^Ty}{y^TW^{-1}y}}{y^TW^{-1}y} = \frac{yy^Tr}{\left(y^TW^{-1}y\right)^2} - \frac{2Wr}{y^TW^{-1}y}.$$

Finally, we can substitute this into our E equation to obtain

$$E = \frac{1}{y^T W^{-1} y} \left[ r y^T W^{-1} + W^{-1} y r^T - \frac{y^T r}{y^T W^{-1} y} W^{-1} y y^T W^{-1} \right].$$

This looks messy, but it is actually quite nice: a **sum of rank-1 updates** to the inverse Hessian! But we have one trick left up our sleeve: we haven't chosen our weight W yet! Different choices of W lead to different quasi-Newton methods, but it is useful to note that E only involves W via the combination  $W^{-1}y$ .

To get an E that turns out to have the especially nice property of preserving positive-definiteness (if  $H^k$  is definite then  $H^{k+1}$  is also, as we discuss below), is to choose some W so that  $W^{-1}y = \delta$ . For example, we can choose  $W^{-1} = (H^{k+1})^{-1} = E + (H^k)^{-1}$ . We then obtain, after a bit more algebra, the famous

<sup>&</sup>lt;sup>3</sup>This may seem a bit circular: we choose W based on the *result* of the optimization. One way to think of it is that if you choose W based on the  $E = \cdots$  formula, then hold W fix and minimize  $||E||_W$  in our QP, you recover the same W.

#### BFGS update:

$$(H^{k+1})^{-1} = (H^k)^{-1} - \frac{1}{\gamma^T \delta} \left[ (H^k)^{-1} \gamma \delta^T + \delta \gamma^T (H^k)^{-1} - \left( 1 + \frac{\gamma^T (H^k)^{-1} \gamma}{\gamma^T \delta} \right) \delta \delta^T \right]$$

This may look a little messy. Equivalently, via the Sherman–Morrison formula,<sup>4</sup> we can derive (after a bunch more algebra) the corresponding update of  $H^k$ :

$$H^{k+1} = H^k + \frac{\gamma \gamma^T}{\gamma^T \delta} - \frac{H^k \delta \delta^T H^k}{\delta^T H^k \delta},$$

which is easier to analyze, even though in practice it is  $H^{-1}$  that we compute and store.

#### 3.1 Positive-definiteness

A key property of the choice of weight W in the BFGS update is that it allows us to ensure positive-definiteness of  $H^{k+1}$  assuming  $H^k$  is definite. (Typically the algorithm starts with  $H^0 = I$  or a similar diagonal positive-definite matrix.) We simply need to check that  $x^T H^{k+1} x > 0$  for any  $x \neq 0$ :

$$\begin{split} x^T H^{k+1} x &= x^T H^k x - \frac{(\delta^T H^k x)^2}{\delta^T H^k \delta} + \frac{(x^T \gamma)^2}{\gamma^T \delta} \\ &= \underbrace{\frac{(x^T H^k x)(\delta^T H^k \delta) - (\delta^T H^k x)^2}{\delta^T H^k \delta}}_{\geq 0 \text{ by Cauchy-Schwarz}} + \underbrace{\frac{(x^T \gamma)^2}{\gamma^T \delta}}_{> 0 \text{ if } \gamma^T \delta > 0}. \end{split}$$

The first term is  $\geq 0$  by the Cauchy-Schwarz inequality: for any inner product  $\langle x, y \rangle$ , it is always true that  $\langle x, x \rangle \langle \delta, \delta \rangle \geq |\langle x, y \rangle|^2$ , and in this case because  $H^k$  is positive-definite we have an inner product  $\langle x, y \rangle = x^T H^k y$ .

is positive-definite we have an inner product  $\langle x,y\rangle=x^TH^ky$ . The second term is clearly >0 whenever  $\gamma^T\delta=\delta^T\gamma=\delta^Tg^{k+1}-\delta^Tg^k>0$ , but why should this be? If we did an exact line search, then  $\delta^Tg^{k+1}=0$ , and  $-\delta^Tg^k=(x^{k+1}-x^k)^T(-g^k)>0$  because  $-g^k$  is the "downhill" direction and  $x^{k+1}$  must be "downhill" from  $x^k$ . If we did an inexact line search, but we imposed the second Wolfe condition  $|\delta^Tg^{k+1}|<|\delta^Tg^k|$ , then we still have  $\delta^Tg^{k+1}-\delta^Tg^k>0$  (the second term is positive and the first term can't be a larger negative magnitude). If we didn't impose the second Wolfe condition and happened to do a step where  $\delta^T\gamma\lesssim 0$ , then we can just skip the update: let  $H^{k+1}=H^k$ : violating the second Wolfe condition generally means that we took too small a step, and we want to keep going in the same direction.

The Sherman–Morrison formula  $(A+uv^T)^{-1}=A^{-1}-\frac{A^{-1}uv^TA^{-1}}{1+v^TA^{-1}u}$  shows that a rank-1 update of A corresponds to a rank-1 update of  $A^{-1}$  and vice-versa.

### 4 Low-storage quasi-Newton (L-BFGS)

Applying the BFGS update directly requires  $\Theta(n^2)$  storage for  $(H^k)^{-1}$  and  $\Theta(n^2)$  work on each step to update  $H^{k+1}$ . This is fine for n up to a few thousand, but for truly large-scale optimization problems it is prohibitive. Fortunately, the fact that BFGS is made of rank-1 updates (adding rank-1 matrices  $uv^T$  to  $H^k$  or its inverse), there is a solution: store a set of rank-1 updates, not the matrix. That is, represent

$$(H^k)^{-1} \approx H^0 + \sum_{j=1}^m u^j (v^j)^T,$$

where we keep the m most recent rank-1 updates for some m (typically  $10 \lesssim m \leq 100$ ). This is known as an **L-BFGS** method, where "L" stands for "low-storage", and was introduced by Nocedal in 1980 [8].

With this representation of  $(H^k)^{-1}$ , assuming  $H^0$  is sparse (typically diagonal, e.g. I), the storage cost is  $\Theta(mn)$  for the  $\{u^j,v^j\}$  vectors, the cost to multiply  $(H^k)^{-1}g^k$  for the quasi-Newton step is also  $\Theta(mn)$ , where as usual we compute  $uv^Tg$  by  $u(v^Tg)$  in  $\Theta(n)$  operations, and the cost of updating to  $H^{k+1}$  is  $\Theta(mn)$  for the  $(H^k)^{-1}\gamma$  product plus  $\Theta(n)$  other operations.

Although for  $m \ll n$  this procedure can no longer converge to the exact Hessian, in practice L-BFGS can greatly accelerate optimization (compared to steepest-descent and other first-order methods with "no memory") in many cases, especially optimization to high accuracy, in much the same way as an approximate Krylov method like restarted GMRES or nonlinear conjugate-gradient.

# 5 BFGS and constrained optimization

For nonlinearly constrained optimization (min  $f_0(x)$  subject to  $f_i(x) \leq 0$ ), the most common utilization of BFGS has been for sequential quadratic programming (SQP): approximate the optimization problem by a sequence of convex QP (convex quadratic objective + affine constraints), typically solved in a trust region to give each optimization step. BFGS is then used to obtain the quadratic term in the QP, but there are a variety of ways to do this. The simplest is to apply BFGS to  $f_0$ , but in that case only linear approximations are used for the constraints  $f_i$ . Alternatively, BFGS can be applied to some form of Lagrangian or "augmented" Lagrangian (= Lagrangian + penalties for violated constraints) [9].

#### References

- [1] C. Broyden, "The convergence of a class of double-rank minimization algorithms," J. Inst. Math. Appl. 6, pp. 76–90 (1970).
- [2] R. Fletcher, "A new approach to variable-metric algorithms," *Computer J.* **13**, pp. 317–322 (1970).

- [3] D. Goldfarb, "A family of variable-metric methods derived by variational means," *Math. Comp.* **24**, pp. 23–26 (1970).
- [4] D. Shanno, "Conditioning of quasi-Newton methods for function minimization," *Math. Comp.* **24**, pp. 647–656 (1970).
- [5] R. Fletcher and M. J. D. Powell, "A rapidly convergent descent method for minimization," *Comput. J.* **6**, pp. 163–168 (1963).
- [6] C. G. Broyden, "Quasi-Newton methods and their application to function minimisation," *Math. Comp.* **21**, pp. 368–381 (1967).
- [7] J. Greenstadt, "Variations on variable metric methods," *Math. Comp.* **24**, pp. 1–22 (1970).
- [8] R. H. Byrd, J. Nocedal, R. B. Schnabel, "Representations of quasi-Newton matrices and their use in limited memory methods," *Math. Prog.* **63**, pp. 129–156 (1994).
- [9] R. H. Byrd, R. A. Tapia, Y. Zhang, "An SQP augmented Lagrangian BFGS algorithm for constrained optimization," SIAM J. Optim. 2, pp. 210–241 (1992).

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

# 18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## Fast Fourier Transform Algorithms (MIT IAP 2008)

Prof. Steven G. Johnson, MIT Dept. of Mathematics

January 11, 2008

Fast Fourier transforms (FFTs),  $O(N \log N)$  algorithms to compute a discrete Fourier transform (DFT) of size N, have been called one of the ten most important algorithms of the 20th century. They are what make Fourier transforms practical on a computer, and Fourier transforms (which express any function as a sum of pure sinusoids) are used in everything from solving partial differential equations to digital signal processing (e.g. MP3 compression) to multiplying large numbers (for computing  $\pi$  to  $10^{12}$  decimal places). Although the applications are important and numerous, the FFT algorithms themselves reveal a surprisingly rich variety of mathematics that has been the subject of active research for 40+ years, and into which this lecture will attempt to dip your toes. The DFT and its inverse are defined by the following relation between N inputs  $x_n$  and N outputs  $y_k$  (all complex numbers):

DFT
$$(x_n)$$
:  $y_k = \sum_{n=0}^{N-1} x_n e^{-\frac{2\pi i}{N}nk},$  (1)

inverse DFT
$$(y_k)$$
:  $x_n = \frac{1}{N} \sum_{k=0}^{N-1} y_k e^{+\frac{2\pi i}{N} nk}$  (2)

where  $i=\sqrt{-1}$ , recalling Euler's identity that  $e^{i\phi}=\cos\phi+i\sin\phi$ . Each of the N DFT outputs  $k=0,\cdots,N-1$  is the sum of N terms, so evaluating this formula directly requires  $O(N^2)$  operations. The trick is to rearrange this computation to expose redundant calculations that we can factor out.

The most important FFT algorithm is called the Cooley-Tukey (C-T) algorithm, after the two authors who popularized it in 1965 (unknowingly re-inventing an algorithm known to Gauss in 1805). It works for any *composite* size  $N=N_1N_2$  by re-expressing the DFT of size N in terms of smaller DFTs of size  $N_1$  and  $N_2$  (which are themselves broken down, recursively, into smaller DFTs until the prime factors are reached). Effectively, C-T expresses the array  $x_n$  of length N as a "two-dimensional" array of size  $N_1 \times N_2$  indexed by  $(n_1, n_2)$ , so that  $n=N_1n_2+n_1$  (where  $n_{1,2}=0,\cdots,N_{1,2}-1$ ). Similarly, the output is expressed as a *transposed* 2d array,  $N_2 \times N_1$ , indexed by

 $(k_2, k_1)$ , so that  $k = N_2k_1 + k_2$ . Substituted into the DFT above, this gives:

$$y_{N_2k_1+k_2} = \sum_{n_1=0}^{N_1-1} \left( \left\{ e^{-\frac{2\pi i}{N} n_1 k_2} \right\} \left[ \sum_{n_2=0}^{N_2-1} e^{-\frac{2\pi i}{N_2} n_2 k_2} x_{N_1 n_2 + n_1} \right] \right) e^{-\frac{2\pi i}{N_1} n_1 k_1}$$
(3)

where we have used the fact that  $e^{-2\pi i n_2 k_1} = 1$  (for any integers  $n_2$  and  $k_1$ ). Here, the outer sum is exactly a length- $N_1$  DFT of the  $(\cdots)$  terms, one for each value of  $k_2$ ; and the inner sum in  $[\cdots]$  is a length- $N_2$  DFT, one for each value of  $n_1$ . The phase in the  $\{\cdots\}$  is called the "twiddle factor" (honest). Assuming that N has small (bounded) prime factors, this algorithm requires  $O(N\log N)$  operations when carried out recursively — the key savings coming from the fact that we have exposed a repeated calculation: the  $[\cdots]$  DFTs need only be carried out *once* for *all*  $y_k$  outputs.

For a given N, there are many choices of factorizations (e.g.  $12=3\cdot 4$  and  $4\cdot 3$  give a different sequence of computations). Moreover, the transposition from input to output implies a data rearrangement process that can be accomplished in many ways. As a result, many different strategies for evaluating the C-T algorithm have been proposed (each with its own name), and the optimal approach is still a matter of active research. Commonly, either  $N_1$  or  $N_2$  is a small (bounded) constant factor, called the radix, and the approach is called decimation in time (DIT) for  $N_1$  = radix or frequency (DIF) for  $N_2$  = radix. Textbook examples are typically radix-2 DIT (dividing  $x_n$  into two interleaved halves with each step), but serious implementations employ more sophisticated strategies.

There are many other FFT algorithms and there are also many different ways to view the *same* algorithms. One fruitful way is to view the DFT in terms of operations on *polynomials*. In particular, define a polynomial x(z) by

$$x(z) = \sum_{n=0}^{N-1} x_n z^n.$$
 (4)

Then

$$y_k = x(e^{-\frac{2\pi i}{N}k}) = x(z) \mod (z - e^{-\frac{2\pi i}{N}k}),$$
 (5)

 $<sup>^1</sup>$ Read " $O(N^2)$ " as "roughly proportional, for large N." e.g.  $15N^2+24N$  is  $O(N^2)$ . (Technically, I should really say  $\Theta(N^2)$ , but I'm not going to get that formal.)

where  $x(z) \mod u(z)$  (x(z) "modulo" u(z)) means the *remainder* of dividing x(z) by u(z). Since u(z) mod u(z) = 0, taking  $x(z) \mod u(z)$  is equivalent to setting u(z) = 0, which in this case means setting  $z = e^{-\frac{2\pi i}{N}k}$ .

The DFT corresponds to computing  $x(z) \mod (z$  $e^{-\frac{2\pi i}{N}k}$ ) for all  $k=0\ldots N-1$ , which would take  $O(N^2)$ operations if done directly. The key observation, from a polynomial viewpoint, is that we can do this modulo operation recursively by combining the factors  $(z - e^{-\frac{2\pi i}{N}k})$ . In particular, it is easy to show that  $x(z) \mod u(z) = [x(z)]$  $\mod u(z)v(z) \mod u(z)$  for any u(z) and v(z). This means that we can first compute x(z) modulo the product of the factors, and then recursively evaluate the remainder by a recursive factorization of this product. But the product  $\prod_k (z - e^{-\frac{2\pi i}{N}k}) = z^N - 1$ , since the  $e^{-\frac{2\pi i}{N}k}$  are just the Nth roots of unity (solutions of  $z^N - 1 = 0$ ). It follows that any recursive factorization of  $z^N - 1$  into  $N \log N$ bounded-degree factors gives us an  $O(N \log N)$  FFT algorithm! In particular, the radix-2 Cooley-Tukey algorithm is equivalent to the recursive factorization (for N a power of 2):  $z^N-a=(z^{N/2}-\sqrt{a})(z^{N/2}+\sqrt{a})$ , where we start with a=1 and end up with  $a=e^{-i\frac{2\pi i}{N}k}$ .

Different recursive factorizations of  $z^N-1$  lead to different FFT algorithms, one of which you will examine for homework. Many other FFT algorithms exist as well, from the "prime-factor algorithm" (1958) that exploits the Chinese remainder theorem for  $gcd(N_1, N_2) = 1$ , to FFT algorithms that work for *prime* N, one of which we give below.

The core of the DFT is the constant  $\omega_N = e^{-\frac{2\pi i}{N}}$ ; because this is a primitive root of unity  $(\omega_N^N = 1)$ , any exponent of  $\omega_N$  is evaluated  $modulo\ N$ . That is,  $\omega_N^m = \omega_N^r$  where r is the remainder when we divide m by N ( $r = m \mod N$ ). A great body of number theory has been developed around such "modular arithmetic", and we can exploit it to develop FFT algorithms different from C-T. For example, Rader's algorithm (1968) allows us to compute  $O(N\log N)$  FFTs of prime sizes N, by turning the DFT into a cyclic convolution of length N-1, which in turn is evaluated by (non-prime) FFTs. Given  $a_n$  and  $b_n$  ( $n=0,\cdots,N-1$ ), their convolution  $c_n$  is defined by the sum

$$c_n = \sum_{m=0}^{N-1} a_m b_{n-m},\tag{6}$$

where the convolution is *cyclic* if the n-m subscript is "wrapped" periodically onto  $0, \dots, N-1$ . This operation is central to digital filtering, differential equations, and other applications, and is evaluated in  $O(N \log N)$  time by the *convolution theorem*:  $c_n = \text{inverse FFT}(\text{FFT}(a_n) \cdot \text{FFT}(b_n))$ . Now, back to the FFT...

For prime N, there exists a generator g of the multiplicative group modulo N: this means that  $g^p \mod N$  for  $p=0,\cdots,N-2$  produces all  $n=1,\cdots,N-1$  exactly once (but not in order!). Thus, we can write all non-zero n and k in the form  $n=g^p$  and  $k=g^{N-1-q}$  for some p and

q, and rewrite the DFT as

$$y_0 = \sum_{n=0}^{N-1} x_n,\tag{7}$$

$$y_{k\neq 0} = y_{g^{N-1-q}} = x_0 + \sum_{p=0}^{N-2} \omega_N^{g^{p+N-1-q}} x_{g^p},$$
 (8)

where (8) is exactly the cyclic convolution of  $a_p = x_{g^p}$  with  $b_p = \omega_N^{g^{N-1-p}}$ . This convolution has non-prime length N-1, and so we can evaluate it via the convolution theorem with FFTs in  $O(N\log N)$  time (except for some unusual cases).

## **Further Reading**

- D. N. Rockmore, "The FFT: An Algorithm the Whole Family Can Use," Comput. Sci. Eng. 2 (1), 60 (2000). Special issue on "top ten" algorithms of century. See: http://tinyurl.com/3wjvk and http://tinyurl.com/yvonp8
- "Fast Fourier transform," *Wikipedia: The Free Ency-clopedia* (http://tinyurl.com/5c6f3). Edited by SGJ for correctness as of 10 Jan 2006 (along with subsidiary articles on C-T and other specific algorithms).
- "The Fastest Fourier Transform in the West," a free FFT implementation obviously named by arrogant MIT graduate students. http://www.fftw.org/

## **Homework Problems**

**Problem 1:** Prove that equation (2) really is the inverse of equation (1). Hint: substitute (1) into (2), interchange the order of the two sums, and sum the geometric series.

**Problem 2:** (a) Prove that for N a power of 2, we can recursively factorize  $z^N-1$  into polynomials of the form  $z^M-1$ and  $z^{2M} + az^M + 1$  with a some real numbers and  $|a| \le 2$ , for a decreasing sequence of M all the way down to M=1. (The final quadratic factors for M=1 can then be factored into conjugate pairs of roots of unity  $e^{\frac{2\pi i}{N}k}$ .) This gives an FFT algorithm due to Bruun (1978), distinct from Cooley-Tukey in that all of its multiplicative constants (a's) are real numbers until the very last step. (b) Apply this algorithm to write down the steps for a "Bruun" FFT of size N=8, and count the number of required real additions and multiplications (not counting operations for x-independent constants like  $2 \cdot \sqrt{2}$  that can be precomputed, and not counting trivial multiplications by  $\pm 1$  or  $\pm i$ ). Compare this to the minimum known operation count of 56 total real additions and multiplications for N=8 (achieved by the "split-radix" algorithm).

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

## 18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

#### In the beginning (c. 1805):

#### Carl Friedrich Gauss

trigonometric interpolation:

$$y_{j} = \sum_{k=0}^{n-1} c_{k} e^{j\frac{2\pi}{n}kj}$$

$$generalizing \ work$$
of Clairaut (1754)
$$and \ Lagrange \ (1762)$$

discrete Fourier transform (DFT): (before Fourier)

$$C_{k} = \frac{1}{n} \sum_{k=0}^{n-1} y_{j} e^{-i\frac{2\pi}{n}kj}$$

#### Gauss' DFT notation:

From "Theoria interpolationis methodo nova tractata"

Quum haec formula indefinite pro valore quocunque ipsius t locum habeat, manifestum est, si producta sinuum in numeratoribus in cosinus sinusque arcuum multiplicium evolvantur, id quod provenit cum

$$\alpha + \alpha' \cos t + \alpha'' \cos 2t + \alpha''' \cos 3t + \text{etc.}$$
  
+  $\beta' \sin t + \beta'' \sin 2t + \beta''' \sin 3t + \text{etc.}$ 

identicum esse debere, unde coëfficientes  $\alpha$ ,  $\alpha'$ ,  $\delta'$ ,  $\alpha''$ ,  $\delta''$  etc. innotescent. Ceterum formula pro T, ut hic exhibita est, ita est comparata, ut sponte et sine calculo pateat, substitutis pro t resp. a, b, c, d etc. valoribus propositis A, B, C, D etc. probe satisfieri.

Kids: don't try this at home!

## Gauss' fast Fourier transform (FFT)

how do we compute: 
$$C_k = \frac{1}{n} \sum_{k=0}^{n-1} y_j e^{-\frac{2\pi}{n}kj}$$
?

— not directly:  $O(n^2)$  operations ... for Gauss, n=12

Gauss' insight: "Distribuamus hanc periodum primo in tres periodos quaternorum terminorum."

= We first distribute this period [n=12] into 3 periods of length 4 ...

Divide and conquer. (any composite *n*)

#### But how fast was it?

"illam vero methodum calculi mechanici taedium magis minuere"

= "truly, this method greatly reduces the tedium of mechanical calculation"

(For Gauss, being less boring was good enough.)

#### two (of many) re-inventors:

## Danielson and Lanczos (1942)

[ J. Franklin Inst. 233, 365–380 and 435–452]

Given Fourier transform of density (X-ray scattering) find density:

discrete sine transform (DST-1) = DFT of real, odd-symmetry

...double sampling until density (DFT) converges...

#### Gauss' FFT in reverse:

## Danielson and Lanczos (1942)

[ J. Franklin Inst. **233**, 365–380 and 435–452]

"By a certain transformation process, it is possible to double the number of ordinates with only slightly more than double the labor."

from  $O(n^2)$  to ???

64-point DST in only 140 minutes!

re-inventing Gauss (for the last time)

[ *Math. Comp.* **19**, 297–301 ]

## Cooley and Tukey (1965)

 $N = N_1 N_2$ 

1d DFT of size *N*:

= 
$$\sim$$
2d DFT of size  $N_1 \times N_2$ 

(+ phase rotation by twiddle factors)

= Recursive DFTs of sizes  $N_1$  and  $N_2$ 

$$O(N^2) \longrightarrow O(N \log N)$$

n=2048, IBM 7094, 36-bit float: 1.2 seconds (~ $10^6$  speedup vs. Dan./Lanc.)

## The "Cooley-Tukey" FFT Algorithm

(non-contiguous)

(non-contiguous)

## "Cooley-Tukey" FFT, in math

Recall the definition of the DFT:

$$y_k = \sum_{n=0}^{N-1} \omega_N^{nk} x_n$$
 where  $\omega_N = e^{-\frac{2\pi i}{N}}$ 

Trick: if  $N = N_1 N_2$ , re-index  $n = n_1 + N_1 n_2$  and  $k = N_2 k_1 + k_2$ :

$$y_{N_{2}k_{1}+k_{2}} = \sum_{n_{1}=0}^{N_{1}-1} \sum_{n_{2}=0}^{N_{2}-1} \omega_{N}^{n_{1}N_{2}k_{1}} \omega_{N}^{n_{1}k_{2}} \omega_{N}^{N_{1}n_{2}N_{2}k_{1}} \omega_{N}^{N_{1}n_{2}k_{2}} x_{n_{1}+N_{1}n_{2}}$$

$$= \sum_{n_{1}=0}^{N_{1}-1} \omega_{N_{1}}^{n_{1}k_{1}} \omega_{N}^{n_{1}k_{2}} \left( \sum_{n_{2}=0}^{N_{2}-1} \omega_{N_{2}}^{n_{2}k_{2}} x_{n_{1}+N_{1}n_{2}} \right)$$
size- $N_{1}$  DFTs twiddles size- $N_{2}$  DFTs

... repeat recursively.

## Cooley-Tukey terminology

- Usually  $N_1$  or  $N_2$  is small, called *radix r* 
  - $-N_1$  is radix: "decimation in time" (DIT)
  - $-N_2$  is radix: "decimation in frequency" (DIF)
- Size-r DFTs of radix: "butterflies"
  - Cooley & Tukey *erroneously* claimed r=3 "optimal": they thought butterflies were  $\Theta(r^2)$
  - In fact,  $r \approx \sqrt{N}$  is optimal cache-oblivious
- "Mixed-radix" uses different radices at different stages (different factors of *n*)

## Many other FFT algorithms

- Prime-factor algorithm:  $N = N_1 N_2$  where  $N_1$  and  $N_2$  are coprime: re-indexing based on Chinese Remainder Theorem with no twiddle factors.
- Rader's algorithm: for prime N, re-index using generator of multiplicative group to get a convolution of size N-1, do via FFTs.
- Bluestein's algorithm: re-index using  $nk = -\frac{1}{2}(k-n)^2 + \frac{n^2}{2} + \frac{k^2}{2}$  to get convolution of size N, do via zero-padded FFTs.
- Many others...
- Specialized versions for real  $x_n$ , real-symmetric/antisymmetric  $x_n$  (DCTs and DSTs), etc.

#### ...but how do we make it faster?

We (probably) cannot do better than  $\Theta(n \log n)$ . (the proof of this remains an open problem)

[ unless we give up exactness ]

We're left with the "constant" factor...

#### The Next 30 Years...

```
Assume "time"

= # multiplications

# multiplications + # additions (= flops)
```

```
Winograd (1979): # multiplications = \Theta(n) (...realizable bound! ... but costs too many additions)
```

```
Yavne (1968): split-radix FFT, saves 20% over radix-2 flops [unsurpassed until last 2007, another ~6% saved by Lundy/Van Buskirk and Johnson/Frigo]
```

## Are arithmetic counts so important?

#### The Next 30 Years...

```
Assume "time"

= # multiplications

# multiplications + # additions (= flops)
```

```
Winograd (1979): # multiplications = \Theta(n) (...realizable bound! ... but costs too many additions)
```

Yavne (1968): split-radix FFT, saves 20% over radix-2 flops [unsurpassed until last 2007, another ~6% saved]

```
last 15+ years: flop count (varies by ~20%) no longer determines speed (varies by factor of ~10+)
```

#### a basic question:

# If arithmetic no longer dominates, what does?

## The Memory Hierarchy (not to scale)

disk (out of core) / remote memory (parallel) (terabytes) RAM (gigabytes) L2 cache (megabytes) L1 cache (10s of kilobytes) registers (~100)

...what matters is not how much work you do, but *when* and *where* you do it.

the name of the game:

do as much work as possible before going out of cache

...difficult for FFTs

...many complications

...continually changing

# The "Fastest Fourier Transform in the West"

Steven G. Johnson, MIT Applied Mathematics

Matteo Frigo, Oracle; formerly MIT LCS (CSAIL)

## What's the fastest algorithm for

(computer science = math + fime = math + \$)

- Find best asymptotic complexity naïve DFT to FFT: O(n²) to O(n log n)
- 2 Find best exact operation count?
- Find variant/implementation that runs fastest hardware-dependent unstable answer!

Better to change the question...

A question with a more stable answer?

What's the smallest set of "simple" algorithmic steps whose compositions ~always span the ~fastest algorithm?

• C library for real & complex FFTs (arbitrary size/dimensionality) (+ parallel versions for threads & MPI)

• Computational kernels (80% of code) automatically generated

• Self-optimizes for your hardware (picks best composition of steps) = portability + performance

free software: <a href="http://www.fftw.org/">http://www.fftw.org/</a>

## FFTW performance

power-of-two sizes, double precision

## FFTW performance

non-power-of-two sizes, double precision

numutils valkenburg

unusual: non-power-of-two sizes receive as much optimization as powers of two

...because we

let the code do the optimizing

## FFTW performance

double precision, 2.8GHz Pentium IV: 2-way SIMD (SSE2)

## Why is FFTW fast?

FFTW implements many FFT algorithms:

A planner picks the best composition (*plan*) by measuring the speed of different combinations.

#### Three ideas:

- 1 A recursive framework enhances locality.
- 2 Computational kernels (codelets) should be automatically generated.
- 3 Determining the unit of composition is critical.

## FFTW is easy to use

```
complex x[n];
plan p;
p = plan dft 1d(n, x, x, FORWARD, MEASURE);
execute(p); /* repeat as needed */
destroy plan(p);
```

Key fact: usually, many transforms of same size are required.

## Why is FFTW fast?

#### FFTW implements many FFT algorithms:

A planner picks the best composition (*plan*) by measuring the speed of different combinations.

#### Three ideas:

- 1 A recursive framework enhances locality.
- 2 Computational kernels (codelets) should be automatically generated.
- 3 Determining the unit of composition is critical.

## Why is FFTW slow?

```
1965 Cooley & Tukey, IBM 7094, 36-bit single precision: size 2048 DFT in 1.2 seconds
```

```
2003 FFTW3+SIMD, 2GHz Pentium-IV 64-bit double precision: size 2048 DFT in 50 microseconds (24,000x speedup)
```

```
(= 30% improvement per year)
```

```
(Moore's prediction: 30 nanoseconds)
```

(= doubles every ~30 months)

FFTs are hard: don't get "peak" CPU speed especially for large n, unlike e.g. dense matrix multiply

## Discontiguous Memory Access

1d DFT of size n:

=  $\sim$ 2d DFT of size  $p \times q$ 

first DFT columns, size q (non-contiguous)

finally, DFT columns, size *p* (non-contiguous)

## Cooley-Tukey is Naturally Recursive

But traditional implementation is non-recursive, breadth-first traversal:

log<sub>2</sub> *n* passes over whole array

## Traditional cache solution: Blocking

breadth-first, but with *blocks* of size = cache optimal choice: radix = cache size radix >> 2

...requires program specialized for cache size ...multiple levels of cache = multilevel blocking

## Recursive Divide & Conquer is Good

(depth-first traversal)

[Singleton, 1967]

eventually small enough to fit in cache ...no matter what size the cache is

#### Cache Obliviousness

- A cache-oblivious algorithm does not know the cache size
  - for many algorithms [Frigo 1999],
     can be provably "big-O" optimal for any machine
     & for all levels of cache simultaneously

... but this ignores e.g. constant factors, associativity, ...

cache-obliviousness is a good beginning, but is not the end of optimization

we'll see: FFTW combines *both* styles (breadth- and depth-first) with self-optimization

## Why is FFTW fast?

#### FFTW implements many FFT algorithms:

A planner picks the best composition (*plan*) by measuring the speed of different combinations.

#### Three ideas:

- 1 A recursive framework enhances locality.
- 2 Computational kernels (codelets) should be automatically generated.
- 3 Determining the unit of composition is critical.

#### The Codelet Generator

a domain-specific FFT "compiler"

• Generates fast hard-coded C for FFT of a given size

Necessary to give the planner a large space of codelets to experiment with (any factorization).

Exploits modern CPU deep pipelines & large register sets.

Allows easy experimentation with different optimizations & algorithms.

...CPU-specific hacks (SIMD) feasible

(& negates recursion overhead)

#### The Codelet Generator

written in Objective Caml [Leroy, 1998], an ML dialect

## The Generator Finds Good/New FFTs

| n       | FFTW (adds+mults) | literature (adds+mults) |             |  |  |  |
|---------|-------------------|-------------------------|-------------|--|--|--|
| complex |                   |                         |             |  |  |  |
| 13      | 176 + 68 = 244    | 172 + 90 = 262          | [LCT93]     |  |  |  |
|         |                   | 188 + 40 = 228          | [SB96]      |  |  |  |
| 15      | 156 + 56 = 212    | 162 + 50 = 212          | [BP85]      |  |  |  |
|         |                   | 162 + 36 = 198          | [BP85]      |  |  |  |
| 64      | 912 + 248 = 1160  | 964 + 196 = 1160        | [Yavne68]   |  |  |  |
|         |                   | real                    |             |  |  |  |
| 15      | 64 + 25 = 89      | 67 + 25 = 92            | [HBJ84]     |  |  |  |
|         |                   | 67 + 17 = 84            | [SJHB87]    |  |  |  |
| 64      | 394 + 124 = 518   | 420 + 98 = 518          | [SJHB87]    |  |  |  |
|         | real syr          | mmetric (even)          |             |  |  |  |
| 16      | 26 + 9 = 35       | 30 + 5 = 35             | [Duhamel86] |  |  |  |
| 64      | 172 + 67 = 239    | 190 + 49 = 239          | [Duhamel86] |  |  |  |

## Symbolic Algorithms are Easy

#### Cooley-Tukey in OCaml

#### DSP book:

$$y_k = \sum_{j=0}^{n-1} x_j \omega_n^{jk} = \sum_{j_2=0}^{p-1} \left[ \left( \sum_{j_1=0}^{q-1} x_{pj_1+j_2} \omega_q^{j_1 k_1} \right) \omega_n^{j_2 k_1} \right] \omega_p^{j_2 k_2},$$

where n = pq and  $k = k_1 + qk_2$ .

#### **OCaml** code:

```
let cooley_tukey n p q x =
let inner j2 = fftgen q
   (fun j1 -> x (p * j1 + j2)) in
let twiddle k1 j2 =
   (omega n (j2 * k1)) @* (inner j2 k1) in
let outer k1 = fftgen p (twiddle k1) in
   (fun k -> outer (k mod q) (k / q))
```

## Simple Simplifications

#### Well-known optimizations:

Algebraic simplification, e.g. a + 0 = a

Constant folding

Common-subexpression elimination

## Symbolic Pattern Matching in OCaml

The following *actual code fragment* is solely responsible for simplifying multiplications:

```
stimesM = function
```

(Common-subexpression elimination is implicit via "memoization" and monadic programming style.)

## Simple Simplifications

#### Well-known optimizations:

Algebraic simplification, e.g. a + 0 = a

Constant folding

Common-subexpression elimination

#### FFT-specific optimizations:

Network transposition (transpose + simplify + transpose)

\_\_\_\_\_ negative constants...

## A Quiz: Is One Faster?

Both compute the same thing, and have the same number of arithmetic operations:

$$a = 0.5 * b;$$
 $c = -0.5 * d;$ 
 $e = 1.0 + a;$ 
 $f = 1.0 + c;$ 

Faster because no separate load for -0.5

10–15% speedup

# Non-obvious transformations require experimentation

## Quiz 2: Which is Faster?

accessing strided array inside codelet (amid dense numeric code), nonsequential

```
array[stride * i]
```

This is faster, of course! Except on brain-dead architectures...

```
array[strides[i]]
```

```
using precomputed stride array:
strides[i] = stride * i
```

...namely, Intel Pentia: integer multiplication conflicts with floating-point

up to ~10–20% speedup

(even better to bloat: pregenerate various constant strides)

# Machine-specific hacks are feasible\nif you just generate special code

stride precomputation

SIMD instructions (SSE, Altivec, 3dNow!)

fused multiply-add instructions...

## The Generator Finds Good/New FFTs

| n       | FFTW (adds+mults) | literature (adds+mults) |             |  |  |  |
|---------|-------------------|-------------------------|-------------|--|--|--|
| complex |                   |                         |             |  |  |  |
| 13      | 176 + 68 = 244    | 172 + 90 = 262          | [LCT93]     |  |  |  |
|         |                   | 188 + 40 = 228          | [SB96]      |  |  |  |
| 15      | 156 + 56 = 212    | 162 + 50 = 212          | [BP85]      |  |  |  |
|         |                   | 162 + 36 = 198          | [BP85]      |  |  |  |
| 64      | 912 + 248 = 1160  | 964 + 196 = 1160        | [Yavne68]   |  |  |  |
|         |                   | real                    |             |  |  |  |
| 15      | 64 + 25 = 89      | 67 + 25 = 92            | [HBJ84]     |  |  |  |
|         |                   | 67 + 17 = 84            | [SJHB87]    |  |  |  |
| 64      | 394 + 124 = 518   | 420 + 98 = 518          | [SJHB87]    |  |  |  |
|         | real syr          | mmetric (even)          |             |  |  |  |
| 16      | 26 + 9 = 35       | 30 + 5 = 35             | [Duhamel86] |  |  |  |
| 64      | 172 + 67 = 239    | 190 + 49 = 239          | [Duhamel86] |  |  |  |

## Why is FFTW fast?

#### FFTW implements many FFT algorithms:

A planner picks the best composition (*plan*) by measuring the speed of different combinations.

#### Three ideas:

- 1 A recursive framework enhances locality.
- 2 Computational kernels (codelets) should be automatically generated.
- 3 Determining the unit of composition is critical.

## What does the planner compose?

- The Cooley-Tukey algorithm presents many choices:
  - which factorization? what order? memory reshuffling?

Find simple steps that combine without restriction to form many different algorithms.

... steps to do WHAT?

FFTW 1 (1997): steps solve out-of-place DFT of size n

## "Composable" Steps in FFTW 1

SOLVE — Directly solve a small DFT by a codelet

CT-FACTOR[r] — Radix-r Cooley-Tukey step = execute loop of r sub-problems of size n/r

Many algorithms difficult to express via simple steps.

- e.g. expresses only depth-first recursion (loop is *outside* of sub-problem)
- e.g. in-place without bit-reversal
   requires combining
   two CT steps (DIT + DIF) + transpose

## What does the planner compose?

- The Cooley-Tukey algorithm presents many choices:
  - which factorization? what order? memory reshuffling?

Find simple steps that combine without restriction to form many different algorithms.

... steps to do WHAT?

FFTW 1 (1997): steps solve out-of-place DFT of size n

Steps cannot solve problems that cannot be expressed.

## What does the planner compose?

- The Cooley-Tukey algorithm presents many choices:
  - which factorization? what order? memory reshuffling?

Find simple steps that combine without restriction to form many different algorithms.

... steps to do WHAT?

#### FFTW 3 (2003):

steps solve a problem, specified as a DFT(input/output, v,n): multi-dimensional "vector loops" v of multi-dimensional transforms n

{sets of (size, input/output strides)}

## Some Composable Steps (out of ~16)

SOLVE — Directly solve a small DFT by a codelet

CT-FACTOR[r] — Radix-r Cooley-Tukey step = r (loop) sub-problems of size n/r (& recombine with size-r twiddle codelet)

VECLOOP — Perform one vector loop

(can choose any loop, i.e. loop reordering)

INDIRECT — DFT = copy + in-place DFT

TRANSPOSE — solve in-place  $m \times n$  transpose

## Many Resulting "Algorithms"

- INDIRECT + TRANSPOSE gives in-place DFTs,
  - bit-reversal = product of transpositionsno separate bit-reversal "pass"[ Johnson (unrelated) & Burrus (1984) ]
- VECLOOP can push topmost loop to "leaves"
  - "vector" FFT algorithm [ Swarztrauber (1987) ]
- CT-FACTOR then VECLOOP(s) gives "breadth-first" FFT,
  - erases iterative/recursive distinction

## Many Resulting "Algorithms"

- INDIRECT + TRANSPOSE gives in-place DFTs,
  - bit-reversal = product of transpositions

... no separate bit-reversal "pass"

[ Johnson (unrelated) & Burrus (1984) ]

- VECLOOP can push topmost loop to "leaves"
  - "vector" FFT algorithm [ Swarztrauber (1987) ]
- CT-FACTOR then VECLOOP(s) gives "breadth-first" FFT,
  - erases iterative/recursive distinction

# Depth- vs. Breadth- First for size $n = 30 = 3 \times 5 \times 2$

A "depth-first" plan:

CT-FACTOR[3]
VECLOOP x3
CT-FACTOR[2]
SOLVE[2, 5]

A "breadth-first" plan:

CT-FACTOR[3]
CT-FACTOR[2]
VECLOOP x3
SOLVE[2, 5]

(Note: *both* are executed by explicit recursion.)

## Many Resulting "Algorithms"

- INDIRECT + TRANSPOSE gives in-place DFTs,
  - bit-reversal = product of transpositions
    - ... no separate bit-reversal "pass"

[ Johnson (unrelated) & Burrus (1984) ]

- VECLOOP can push topmost loop to "leaves"
  - "vector" FFT algorithm [ Swarztrauber (1987) ]
- CT-FACTOR then VECLOOP(s) gives "breadth-first" FFT,
  - erases iterative/recursive distinction

## In-place plan for size 2<sup>14</sup> = 16384 (2 GHz PowerPC G5, double precision)

Radix-32 DIT + Radix-32 DIF = 2 loops = transpose ... where leaf SOLVE  $\sim$  "radix" 32 x 1

## Out-of-place plan for size 2<sup>19</sup>=524288

(2GHz Pentium IV, double precision)

CT-FACTOR[4] (buffered variant)
 CT-FACTOR[32] (buffered variant)

Unpredictable: (automated) experimentation is the only solution.

## Dynamic Programming

the assumption of "optimal substructure"

Try all applicable steps:

```
DFT(16) = fastest of: CT-FACTOR[2]: 2 DFT(8)

CT-FACTOR[4]: 4 DFT(4)
```

DFT(8) = fastest of: CT-FACTOR[2]: 2 DFT(4)

CT-FACTOR[4]: 4 DFT(2)

SOLVE[1,8]

If exactly the same problem appears twice, assume that we can re-use the plan.

— i.e. ordering of plan speeds is assumed independent of context

## Planner Unpredictability

double-precision, power-of-two sizes, 2GHz PowerPC G5

Classic strategy: minimize op's fails badly

#### another test:

Use plan from: another machine? e.g. Pentium-IV? ... lose 20–40%

## We've Come a Long Way?

- In the name of performance, computers have become complex & unpredictable.
- Optimization is hard: simple heuristics (e.g. fewest flops) no longer work.

• One solution is to avoid the details, not embrace them:

(Recursive) composition of simple modules + feedback (self-optimization)

High-level languages (not C) & code generation are a powerful tool for high performance.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.335J Introduction to Numerical Methods Spring 2019

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.
