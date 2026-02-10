MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 1: The algebra of Complex numbers

(Text 1-11 & 19-20)

## Remarks on Lecture 1

 $\blacktriangleright$  On p.19-20, it is stated that each circle in  $\mathbb C$ 

$$(x-a)^2 + (y-b)^2 = r^2 (1)$$

has the form

$$(\alpha_0 - \alpha_3)(x^2 + y^2) - 2\alpha_1 x - 2\alpha_2 y + \alpha_0 + \alpha_3 = 0,$$

so the mapping  $z\mapsto Z$  maps circles in the plane to circles on S. Solving the equations

$$a = \frac{\alpha_1}{\alpha_0 - \alpha_3}, \ b = \frac{\alpha_2}{\alpha_0 - \alpha_3}, \ r^2 - a^2 - b^2 = -\frac{\alpha_0 + \alpha_3}{\alpha_0 - \alpha_3}$$

for  $\alpha_0, \alpha_1, \alpha_2, \alpha_3$  is disagreeable so we instead determine the image of the curve (1) under the map  $z \mapsto Z$ . Using the formulas (24)-(26) and

$$1 - x_3 = \frac{2}{1 + |z|^2},$$

formula (1) becomes

$$ax_1 + bx_2 + \frac{1 + r^2 - a^2 - b^2}{2}x_3 = \frac{a^2 + b^2 - r^2 + 1}{2}.$$

This is a plane which must intersect the sphere so has distance < 1 from 0.

▶ The formula (28) can be proved geometrically as follows (Exercise 4):

Z'\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_

This proves (28).

Let  $Z \in S$  lie on the plane

$$x_2 = 0.$$

The angles at Z are right angles, so by similar triangles:

$$\frac{d(N,Z)}{2} = \frac{1}{d(N,z)} = \frac{1}{\sqrt{1+|z|^2}}.$$

Thus

$$\frac{d(N,Z)}{d(N,z')} = \frac{2}{\sqrt{1+|z|^2}\sqrt{1+|z'|^2}}$$

and by symmetry this is

$$\frac{d(N,Z')}{d(N,z)}.$$

Thus the triangles  $\triangle NZZ'$  and  $\triangle Nzz'$  are similar, so the above ratio is

$$\frac{d(Z,Z')}{|z-z'|}.$$

Finally we show that the spherical representation  $z \mapsto Z$  is <u>conformal</u>. This means that if l and m are two lines in the plane intersecting in z at an angle  $\alpha$ , then the corresponding circles C and D through N and Z intersect Z at the same angle  $\alpha$ . Consider the tangent plane  $\pi$  to S at the point N, the plane through Z and l intersects  $\pi$  in a line l'. Similarly the plane through Z and m intersect  $\pi$  in m'. Clearly l' and m' intersect at N at the same angle  $\alpha$ . Since they are tangents to C and D at N, C and D must intersect at the angle  $\alpha$  both at N and at Z.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 2: Exponential function & Logarithm for a complex argument

(Replacing Text p.10 - 20)

For b > 1,  $x \in \mathbb{R}$ , we defined in 18.100B,

$$b^x = \sup_{t \in \mathbb{Q}, \ t \le x} b^t$$

(where  $b^t$  was easy to define for  $t\in\mathbb{Q}$  ). Then the formula

$$b^{x+y} = b^x b^y$$

was hard to prove directly. We shall obtain another expression for  $b^x$  making proof easy.

Let

$$L(x) = \int_1^x \frac{dt}{t}, \quad x > 0.$$

Then

$$L(xy) = L(x) + L(y)$$

and

$$L'(x) = \frac{1}{x} > 0.$$

So L(x) has an inverse E(x) satisfying

$$E(L(x)) = x.$$

By 18.100B,

$$E'(L(x))L'(x) = 1,$$

SO

$$E'(L(x)) = x.$$

If y = L(x), so x = E(y), we thus have

$$E'(y) = E(y),$$

It is easy to see E(0) = 1, so by uniqueness,

$$E(x) = 1 + x + \frac{x^2}{2} + \dots + \frac{x^n}{n!} + \dots$$
 and  $E(1) = e$ .

Theorem 1  $b^x = E(xL(b)), \forall x \in \mathbb{R}.$ 

*Proof:* Let u = L(x), v = L(y), then

$$E(u + v) = E(L(x) + L(y)) = E(L(xy)) = xy = E(u)E(v),$$

$$E(n) = E(1)^n = e^n,$$

and if  $t = \frac{n}{m}$ ,

$$E(t)^m = E(mt) = E(n) = e^n.$$

SO

$$E(t) = e^t, \ t \in \mathbb{Q}, \ t > 0.$$

Since

$$E(t)E(-t) = 1,$$

So

$$E(t) = e^t, \ t \in \mathbb{Q}.$$

Now

$$b^n = E(nL(b))$$

and

$$b^{\frac{1}{m}} = E\left(\frac{1}{m}L(b)\right)$$

since both have same  $m^{th}$  power.

$$\left(b^{\frac{1}{m}}\right)^n = b^{\frac{n}{m}} = E\left(\frac{1}{m}L(b)\right)^n = E\left(\frac{n}{m}L(b)\right),$$

so

$$b^t = E(tL(b)), \ t \in \mathbb{Q}.$$

Now for  $x \in \mathbb{R}$ ,

$$b^x = \sup_{t \le x, \ t \in \mathbb{Q}} (b^t) = \sup_{t \le x, \ t \in \mathbb{Q}} E(tL(b)) = E(xL(b))$$

since E(x) is continuous.

Q.E.D.

Corollary 1 For any  $b > 0, x, y \in \mathbb{R}$ , we have  $b^{x+y} = b^x b^y$ .

In particular  $e^x = E(x)$ , so we have the amazing formula

$$\left(1+1+\frac{1}{2!}+\dots+\frac{1}{n!}+\dots\right)^x = 1+x+\frac{x^2}{2!}+\dots+\frac{x^n}{n!}+\dots$$

The formula for  $e^x$  suggests defining  $e^z$  for  $z \in \mathbb{C}$  by

$$e^z = 1 + z + \frac{z^2}{2!} + \dots + \frac{z^n}{n!} + \dots$$

the convergence being obvious.

Proposition 1  $e^{z+w} = e^z e^w$  for all  $z, w \in \mathbb{C}$ .

*Proof:* Look at the functions

$$f(t) = e^{tz+w}, \ q(t) = e^{tz}e^{w}$$

for  $t \in \mathbb{R}$ . Differentiating the series for  $e^{tz+w}$  and  $e^{tz}$  with respect to t, term-by-term, we see that

$$\frac{df}{dt} = zf(t), \ \frac{dg}{dt} = zg(t)$$

and

$$f(0) = e^w, \ g(0) = e^w.$$

By the uniqueness for these equations, we deduce  $f \equiv g$ . Thus f(1) = g(1). Q.E.D. Note that if  $t \in \mathbb{R}$ ,

$$e^{it}e^{-it} = 1$$
, and  $(e^{it})^{-1} = e^{-it}$ .

Thus

$$|e^{it}| = 1.$$

So  $e^{it}$  lies on the unit circle.

Put

$$\cos t = \frac{e^{it} + e^{-it}}{2} = 1 - \frac{t^2}{2} + \cdots,$$
$$\sin t = \frac{e^{it} - e^{-it}}{2} = t - \frac{t^3}{3!} + \cdots.$$

Thus we verify the old geometric meaning  $e^{it} = \cos t + i \sin t$ . Note that the  $e^{it}(t \in \mathbb{R})$  fill up the unit circle. In fact by the intermediate value theorem,  $\{\cos t \mid t \in \mathbb{R}\}$  fills up the interval [-1,1], so  $e^{it} = \cos t + i \sin t$  is for a suitable t an arbitrary point on the circle.

Note that  $z \mapsto e^z$  takes all values  $w \in \mathbb{C}$  except 0. For this note

$$e^z = e^x \cdot e^{iy}, \quad z = x + iy.$$

Choose x with

$$e^x = |w|$$

and then y so that

$$e^{iy} = \frac{w}{|w|},$$

then  $e^z = w$ .

$$z = |z|e^{i\varphi}, \quad w = |w|e^{i\psi},$$

then

$$zw = |z||w|e^{i(\varphi+\psi)}$$
  
= |z||w|(\cos(\varphi+\psi) + i\sin(\varphi+\psi)),

which gives a geometric interpretation of the multiplication.

From this we also have the following very useful formula

$$(\cos \varphi + i \sin \varphi)^n = e^{in\varphi} = \cos n\varphi + i \sin n\varphi.$$

Thus

**Theorem 2** The roots of  $z^n = 1$  are  $1, \omega, \omega^2, \cdots, \omega^{n-1}$ , where

$$\omega = \cos\frac{2\pi}{n} + i\sin\frac{2\pi}{n}.$$

Geometric meanings for some useful complex number sets:

$$\begin{aligned} |z-a| &= r &&\longleftrightarrow & \text{circle} \\ |z-a| + |z-b| &= r, \ (|a-b| < r) &&\longleftrightarrow & \text{ellipse} \\ |z-a| &= |z-b| &&\longleftrightarrow & \text{perpendicular bisector} \\ \{z \mid z = a + tb, t \in \mathbb{R}\} &&\longleftrightarrow & \text{line} \\ \{z \mid \text{Im}z < 0\} &&\longleftrightarrow & \text{lower half plane} \\ \{z \mid \text{Im}\left(\frac{z-a}{b}\right) < 0\} &&\longleftrightarrow & \text{general half plane} \end{aligned}$$

For x real,  $x \mapsto e^x$  has an inverse. This is **NOT** the case for  $z \mapsto e^z$ , because

$$e^{z+2\pi i} = e^z,$$

thus  $e^z$  does not have an inverse. Moreover, for  $w \neq 0$ ,

$$e^z = w$$

has infinitely many solutions:

$$e^x = |w|, \quad e^{iy} = \frac{w}{|w|} \Longrightarrow x = \log|w|, \quad y = \arg(w).$$

So

$$\log w = \log |w| + i\arg(w)$$

takes infinitely many values, thus not a function.

Define

 $Arg(w) \triangleq principal argument of w in interval - \pi < Arg(w) < \pi$ 

and define the principal value of logarithm to be

$$Log(w) \triangleq log |w| + iArg(w),$$

which is defined in slit plane (removing the negative real axis).

We still have

$$\log z_1 z_2 = \log z_1 + \log z_2$$

in the sense that both sides take the same infinitely many values. We can be more specific:

Theorem 3 In slit plane,

$$Log(z_1z_2) = Log(z_1) + Log(z_2) + n \cdot 2\pi i, \quad n = 0 \text{ or } \pm 1$$

and n = 0 if

$$-\pi < Arg(z_1) + Arg(z_2) < \pi.$$

In particular, n = 0 if  $z_1 > 0$ .

*Proof:* In fact,  $Arg(z_1)$ ,  $Arg(z_2)$  and  $Arg(z_1z_2)$  are all in  $(-\pi, \pi)$ , thus

$$-\pi - \pi - \pi < \text{Arg}(z_1) + \text{Arg}(z_2) - \text{Arg}(z_1 z_2) < \pi + \pi + \pi,$$

but

$$\operatorname{Arg}(z_1) + \operatorname{Arg}(z_2) - \operatorname{Arg}(z_1 z_2) = n \cdot 2\pi i,$$

thus

$$|n| \leq 1$$
.

If

$$|\operatorname{Arg}(z_1) + \operatorname{Arg}(z_2)| < \pi,$$

 ${\rm since}$ 

$$|\operatorname{Arg}(z_1 z_2)| < \pi,$$

they must agree since difference is a multiple of  $2\pi.$ 

Q.E.D.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 3: Analytic Functions; Rational Functions

(Text 21-32)

## Remarks on Lecture 3

- ► Formula (14) on p.32 was proved under the assumption that  $R(\infty) = \infty$ . On the other hand, if  $R(\infty)$  is finite, then (12) holds with  $G \equiv 0$ . Then we use the previous proof on  $R(\beta_j + \frac{1}{\zeta})$  and we still get the representation (14).
- ▶ For theorem 1 on page 29, we have the following stronger version:

**Theorem 1 (Stronger version)** The smallest convex set which contains all the zeros of P(z) also contains the zeros of P'(z).

*Proof:* Let  $\alpha_1, \dots, \alpha_n$  be the zeros of P, so

$$P(z) = a_n(z - \alpha_1) \cdots (z - \alpha_n).$$

Then

$$\frac{P'(z)}{P(z)} = \frac{1}{z - \alpha_1} + \dots + \frac{1}{\alpha_n}.$$

If  $z_0$  is a zero of P'(z) and  $z_0 \neq \text{each } \alpha_i$ , then this vanishes for  $z = z_0$ ; conjugating the equation gives

$$\frac{z_0 - \alpha_1}{|z_0 - \alpha_1|^2} + \dots + \frac{z_0 - \alpha_n}{|z_0 - \alpha_n|^2} = 0,$$

SO

$$z_0 = m_1 \alpha_1 + \dots + m_n \alpha_n,$$

where

$$m_i \ge 0$$
 and  $\sum_{i=1}^n m_i = 1$ .

We now only need to prove the following simple result:

**Proposition 1** Given  $a_1, \dots, a_n \in \mathbb{C}$ , the set

$$\{\sum_{i=1}^{n} m_i a_i \mid m_i \ge 0, \ \sum_{i=1}^{n} m_i = 1\}$$
 (1)

is the intersection C of all convex sets containing all  $a_i$  (which is called the convex hull of  $a_1, \dots, a_n$ ).

*Proof:* We must show that each point  $\sum_{i=1}^{n} a_i m_i$  in (1) is contained in each convex set containing the  $a_i$  and thus in C. We may assume it has the form

$$x = \sum_{i=1}^{p} m_i a_i$$

where

$$m_i > 0$$
 for  $1 \le i \le p$ 

and

$$m_j = 0 \text{ for } j > p.$$

We prove  $x \in C$  by induction on p. Statement is clear if p = 1. Put

$$\lambda = \sum_{i=1}^{p-1} m_i$$

and

$$a = \sum_{i=1}^{p-1} \frac{m_1}{\lambda} a_i.$$

By inductive assumption,  $a \in C$ . But

$$x = \sum_{i=1}^{p} m_i a_i = \lambda a + (1 - \lambda) a_i$$

where  $0 \le \lambda \le 1$ . So  $x \in C$  as stated. Q.E.D.

## Solution to 4 on p.33

Suppose R(z) is rational and

$$|R(z)| = 1$$

for |z| = 1. Then

$$|R(e^{i\theta})| \equiv 1 \quad \theta \in \mathbb{R}.$$

Let S(z) be the rational functions obtained by conjugating all the coefficients in R(z), then

$$R(e^{i\theta})S(e^{-i\theta}) = R(e^{i\theta})\overline{R(e^{i\theta})} = 1.$$

So

$$R(z)S(\frac{1}{z}) = 1$$
 on  $|z| = 1$ .

Clearing denominators we see this relation

$$R(z)S(\frac{1}{z}) = 1$$

holds for all  $z \in \mathbb{C}$ .

Since a polynomial has only finitely many zeroes, let

$$\alpha_1, \cdots, \alpha_p$$

be all the zeroes of R(z) which are not equal to 0 or  $\infty$ . Then

$$\frac{1}{\alpha_1}, \cdots, \frac{1}{\alpha_p}$$

are the poles of S(z) which are not equal to 0 or  $\infty$ . So

$$\frac{1}{\bar{\alpha}_1}, \cdots, \frac{1}{\bar{\alpha}_n}$$

are the poles of R(z) which are not equal to 0 or  $\infty$  because of the definition of S. Then

$$R(z) \left( \frac{z - \alpha_1}{1 - \bar{\alpha}_1 z} \cdots \frac{z - \alpha_p}{1 - \bar{\alpha}_p z} \right)^{-1}$$

has no poles or zeros except possibly 0 and  $\infty$ . Hence

$$R(z) = Cz^{l} \frac{z - \alpha_{1}}{1 - \bar{\alpha}_{1}z} \cdots \frac{z - \alpha_{p}}{1 - \bar{\alpha}_{p}z}$$

where C is constant with |C| = 1, l is integer.

Conversely, such R has |R(z)| = 1 on |z| = 1.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

# 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 4: Power Series

(Text 33-42)

#### Remarks on Lecture 4

### Problem 8 on p.41

We know  $\sum_{0}^{\infty} w^n$  converges only for |w| < 1. Otherwise the terms do not converge to 0. Now put

$$z' = z + \frac{1}{2},$$

SO

$$w = \frac{z}{1+z} = \frac{z' - \frac{1}{2}}{z' + \frac{1}{2}}.$$

So |w| < 1 is equivalent to

$$\text{Re}z' > 0$$
,

or equivalently

$$\operatorname{Re} z > -\frac{1}{2}.$$

## Problem 9 on p.41

Write

$$\frac{z^n}{1+z^{2n}} = \frac{1}{z^n + z^{-n}}.$$

Write  $a_n \sim b_n$  if

$$\left| \frac{a_n}{b_n} \right| \longrightarrow c \neq 0.$$

Then if 
$$|z|>1,$$
 
$$\frac{1}{z^n+z^{-n}}\sim z^{-n},$$
 and if  $|z|<1,$  
$$\frac{1}{z^n+z^{-n}}\sim z^n.$$

So in both cases we have convergence. If  $z = e^{it}$ , we have

$$\frac{1}{z^n + z^{-n}} = \frac{1}{2\cos nt},$$

so the terms do not tend to 0, so we have divergence.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 5: Exponentials and Trigonometric Functions

(Text 42-47)

## Remarks on Lecture 5

Since  $\cos z$  is even,  $\arccos z$  can just as well defined as

$$\arccos z = -i\log(z + \sqrt{z^2 - 1}).$$

This in fact more appropriate because then the derivative is

$$-\frac{1}{\sqrt{1-z^2}},$$

which is better because then the derivative is < 0 for z = 0. Note that in any case

$$\cos(\arccos z) = z,$$

since  $z + \sqrt{z^2 - 1}$  and  $z - \sqrt{z^2 - 1}$  are reciprocals.

---

MIT OpenCourseWare http://ocw.mit.edu

# 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# Lecture 6: Conformal Maps; Linear Transformations

(Text 69-80)

## Remarks on Lecture 6

### Problem 6 on p.83

Let C, D have center a, C', D' their images under mapping S. Then lines  $\bot C$  and D go to circles  $\bot C'$  and D' and these must be lines through the common center b of C' and D'.

In the extended plane, lines intersect always at  $\infty$ . Thus under S, a and  $\infty$  go to b and  $\infty$  or  $\infty$  and b. Let

$$w_1 = Sz_1, \quad w_2 = Sz_2,$$

then

$$(z_1, z_2, a, \infty) = \begin{cases} (w_1, w_2, b, \infty), \\ (w_1, w_2, \infty, b), \end{cases}$$

and

$$\left|\frac{z_1-a}{z_2-a}\ :\ \frac{z_1-\infty}{z_2-\infty}\right| = \left\{\begin{array}{c} \left|\frac{w_1-b}{w_2-b}\ :\ \frac{w_1-\infty}{w_2-\infty}\right|,\\\\ \left|\frac{w_1-\infty}{w_2-\infty}\ :\ \frac{w_1-b}{w_2-b}\right|. \end{array}\right.$$

So

$$\frac{r}{R} = \begin{cases} \frac{r_1}{R_1} ,\\ \frac{R_1}{r_1} . \end{cases}$$

Theorem 1 (Implying Problem 7, p. 83 and Problem 6, p. 88.)

If A and B are two nonintersecting circles there exists a linear transformation mapping A and B into concentric circles.

*Proof.* First transform A to a line  $A_1$ . This sends B to a circle  $B_1$ . Consider the line  $\ell$  from the center of B perpendicular to  $A_1$ . Let M be the point  $\ell \cap A_1$ . With M as center construct the circle C cutting  $B_1$  orthogonally. Then take a linear transformation sending one of the points in  $\ell \cap C$  to  $\infty$ . It sends C and  $\ell$  into orthogonal lines m and n. Then  $A_1$  and  $B_1$  are sent into circles  $A_2$  and  $B_2$  which cut m and n orthogonally and are therefore concentric.

#### Problem 5 on p.83

Suppose S maps a to 0. Since a and  $\frac{R^2}{\bar{a}}$  are symmetric with respect to |z| = R, S maps  $\frac{R^2}{\bar{a}}$  to  $\infty$ . The transformation

$$S_0(z) = R^2 \frac{z - a}{R^2 - \bar{a}z}$$

maps a to 0 and  $\frac{R^2}{\bar{a}}$  to  $\infty$ , and maps |z|=R into itself since

$$|Re^{i\theta} - a| = |R - \bar{a}e^{i\theta}|.$$

If T also has this property, then  $TS_0^{-1}$  maps 0 to 0 and maps  $\infty$  to  $\infty$ , so

$$TS_0^{-1} = cz$$

with |c| = 1. Thus

$$T = R^2 e^{i\theta} \frac{z - a}{R^2 - \bar{a}z}.$$

---

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 7: Linear Transformations

(Text 80-89)

## Remarks on Lecture 6

Concerning Definition 13 p. 81, formula (11) shows that the definition does not depend on the choice of  $z_1, z_2, z_3$ .

Exercise 2 on page 88 requires a minor correction. For example w = -z is hyperbolic according to definition on page 86, yet when written in the form

$$\frac{az+b}{cz+d}$$

with

$$ad - bc = 1$$
,

we must take

$$a = -d = i$$
,

SO

$$a + d = 0$$
.

The transformation w = z causes other ambiguities.

Thus we modify the definition a bit.

## Definition 1

- S is parabolic if either it is the identity or has exactly one fixed point.
- S is strictly hyperbolic if k > 0 in (12) but k ≠ 1.
  S is elliptic if |k| = 1 in (12) p. 86 but S is not identity.

Then the statement of Exercise 2 holds with hyperbolic replaced by strictly hyperbolic.

(i) the condition for exactly one fixed point for

$$Sz = \frac{\alpha z + \beta}{\gamma z + \delta}$$

is

$$(\alpha - \delta)^2 = -4\beta\gamma$$
 (wrong sign in text).

With the normalization

$$\alpha\delta - \beta\gamma = 1$$

this amounts to

$$(\alpha + \delta)^2 = 4$$

as desired.

(ii) Assume two fixed points are a and b, so

$$\frac{w-a}{w-b} = k\frac{z-a}{z-b},$$

which we write as

$$w = Tz = \frac{\alpha z + \beta}{\gamma z + \delta}.$$

Put

$$A = \left(\begin{array}{c} \alpha \ \beta \\ \gamma \ \delta \end{array}\right)$$

and define

$$\operatorname{Tr}^2(T) = \frac{(\operatorname{Trace} A)^2}{\det A}.$$

By linear algebra,

$$\operatorname{Trace}(BAB^{-1}) = \operatorname{Trace}(A)$$

and

$$\det\left(BAB^{-1}\right) = \det A.$$

Define

$$z_1 = Sz = \frac{z - a}{z - b},$$
$$w_1 = Sw = \frac{w - a}{w - b}.$$

Then

$$Tr^2(T) = Tr^2(STS^{-1}).$$

Now

$$w_1 = STz = STS^{-1}z_1,$$

SO

$$w_1 = kz_1$$
.

Then

$$\operatorname{Tr}^{2}(T) = \operatorname{Tr}^{2}(STS^{-1}) = k + \frac{1}{k} + 2.$$

If T is strictly hyperbolic, we have

$$k > 0, \quad k \neq 1,$$

SO

$$\operatorname{Tr}^2(T) > 4$$
,

which under the assumption

$$\alpha\delta - \beta\gamma = 1$$

amounts to

$$(\alpha + \delta)^2 > 4$$

as stated.

Conversely, if

$$(\alpha + \delta)^2 > 4,$$

then k > 0. So the transformation

$$w_1 = kz_1$$

maps each line through 0 and  $\infty$  into itself. So T maps each circle  $C_1$  into itself with k > 0. Thus T is strictly hyperbolic.

(iii) If 
$$|k| = 1$$
, then

$$w_1 = e^{i\theta} z_1$$

and we find

$$\operatorname{Tr}^2(T) = \left(2\cos\frac{\theta}{2}\right)^2 < 4$$

since the possibility  $\theta = 0$  is excluded.

Conversely, if

$$-2 < \alpha + \delta < 2, \quad \alpha \delta - \beta \gamma = 1$$

we have

$$\operatorname{Tr}^{2}(T) = (\alpha + \delta)^{2} = k + \frac{1}{k} + 2 < 4.$$

Writing

$$k = re^{i\theta} \ (r > 0)$$

this implies

$$\left(r + \frac{1}{r}\right)\cos\theta + i\left(r - \frac{1}{r}\right)\sin\theta < 2,$$

which implies

$$r=1$$
 or  $\theta=0$  or  $\theta=\pi$ .

If r = 1, then |k| = 1, so T is elliptic.

Since  $r + \frac{1}{r} \ge 2$ , the possibility  $\theta = 0$  is ruled out. Finally if  $\theta = \pi$ , then k = -r, so

$$(\alpha + \delta)^2 = -r - \frac{1}{r} + 2.$$

But  $r \geq 0$ , so since  $\alpha + \delta$  is real, this implies r = 1, so k = -1, and T is thus elliptic.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 8: Line Integrals

(Text 101-108)

## Remarks on Lecture 8

The following rule (integration by substitution) is often useful.

**Theorem 1** Let  $w = \varphi(z)$  be a holomorphic function on a region  $\Omega$ . Let  $\gamma$  be a curve in  $\Omega$ , then

$$\int_{\varphi(\gamma)} f(w) \ dw = \int_{\gamma} f(\varphi(z)) \varphi'(z) \ dz.$$

*Proof:* Let  $\gamma$  be given by

$$\gamma : z(t), \ \alpha \le t \le \beta.$$

Then  $\varphi(\gamma)$  is given by

$$\varphi$$
:  $w(t) = \varphi(z(t)), \ \alpha \le t \le \beta$ .

Then LHS equals

$$\int_0^\beta f(w(t))w'(t) \ dt,$$

and RHS equals

$$\int_{\alpha}^{\beta} f(\varphi(z(t)))\varphi'(z(t))z'(t) dt = \int_{\alpha}^{\beta} f(w(t))w'(t) dt.$$

Q.E.D.

## Exercise 3 on page 108.

We have

$$\frac{1}{z^2 - 1} = \frac{1}{2} \left( \frac{1}{z - 1} - \frac{1}{z + 1} \right),$$

so the problem is reduced to computing

$$\int_{\gamma} \frac{1}{z-1} dz$$
 and  $\int_{\gamma} \frac{1}{z+1} dz$ ,

where  $\gamma$ : |z| = 2 is the circle.

Since  $\log(z+1)$  is holomorphic in the region

 $\mathbb{C} \setminus I_{\epsilon}$ , where  $I_{\epsilon}$  is the shown wedge with vertex -1 and opening of angle  $\epsilon$ . In this region

$$\frac{d(\log(z+1))}{dz} = \frac{1}{z+1}.$$

Letting  $\epsilon \to 0$  we deduce from Theorem p.107 middle

$$\int_{\gamma+\Gamma} \frac{1}{z+1} \ dz = 0.$$

Hence

$$\int_{\gamma} \frac{1}{z+1} \ dz = 2\pi i.$$

Similarly,

$$\int_{\gamma} \frac{dz}{z-1} = 2\pi i$$

using the circle |z-1|=1. Consequently,

$$\int_{\gamma} \frac{dz}{z^2 - 1} = 0.$$

The result is obvious from our substitution theorem because if

$$\varphi(z) = -z,$$

then

$$\varphi(\gamma) = \gamma$$
 (including orientation).

So

$$\int_{\gamma} \frac{dz}{z^2 - 1} = - \int_{\gamma} \frac{dz}{z^2 - 1}.$$

More generally we have

**Theorem 2** Let R be a rational function on  $\mathbb{C}$ . Then

$$\int_{\gamma} R(z^2) \ dz = 0$$

for every circle  $\gamma$  around the origin provided  $R(z^2) \neq 0$  on  $\gamma$ .

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 9: Cauchy-Goursat Theorem

(Text 109-115)

## Remarks on Lecture 9

Property (ii) (page 116) of the winding number follows since

$$a \longrightarrow n(\gamma, a)$$

is a continuous function on  $\mathbb{C} \setminus \gamma$  and the image of each component is a connected set of integers, hence constant.

---

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# Lecture 10: The Special Cauchy's Formula and Applications

(Text 118-126)

### Remarks on Lecture 10

#### Exercise 6 on page 108

The values of f(z) lie in the disk |w-1| < 1 which is contained in the slit plane where Log w is defined. thus Log f(z) is well-defined and holomorphic in  $\Omega$  and has derivative

$$\frac{1}{f(z)}f'(z).$$

Thus

$$\int_{\gamma} \frac{f'(z)}{f(z)} dz = 0$$

by the Primitive theorem.

#### Exercise 2 on page 120

By using the substitution  $w = \varphi(z) = -z$  we have

$$\int_{\varphi(\gamma)} \frac{dw}{w^2+1} = \int_{\gamma} \frac{-dz}{z^2+1}.$$

Since  $\varphi(\gamma) = \gamma$  (including the orientation). Thus the integral is 0.

Also

$$\frac{1}{z^2 + 1} = \frac{1}{z - i} - \frac{1}{z + i}$$

and

$$n(\gamma, i) = n(\gamma, -i),$$

so again the total integral is 0.

#### Exercise 3 on page 120

On  $|z| = \rho$ , we can write  $z = \rho e^{i\theta}$ , thus

$$\frac{dz}{d\theta} = \rho e^{i\theta} i,$$

SO

$$\frac{dz}{z} = i \ d\theta,$$

and

$$|dz| = \rho d\theta = -i\rho \frac{dz}{z}.$$

Thus

$$\begin{split} \int_{|z|=\rho} \frac{|dz|}{|z-a|^2} &= -i\rho \int_{|z|=\rho} \frac{dz}{z(z-a)(\frac{\rho^2}{z}-\bar{a})} \\ &= -i\rho \left[ \frac{1}{\rho^2-|a|^2} \int_{|z|=\rho} \frac{dz}{z-a} + \frac{\bar{a}}{\rho^2-|a|^2} \int_{|z|=\rho} \frac{dz}{\rho^2-\bar{a}z} \right]. \end{split}$$

If  $|a| > \rho$ , the first term is 0, the other term is

$$\frac{1}{\bar{a}} \int_{|z|=\rho} \frac{dz}{\frac{\rho^2}{\bar{a}}-z} = -2\pi i \frac{1}{\bar{a}},$$

so the result is

$$\frac{2\pi\rho}{|a|^2-\rho^2}.$$

If  $|a| < \rho$ , then the second is 0 and the other is

$$-i\rho \ 2\pi i \frac{1}{\rho^2 - |a|^2} = \frac{2\pi\rho}{\rho^2 - |a|^2}.$$

Thus in both cases the result is

$$\left| \frac{2\pi\rho}{\rho^2 - |a|^2} \right|.$$

▶ The Taylor's Theorem (with remainder) proved in pp.125-126 should be stated as follows:

**Theorem 1 (Taylor's Theorem)** If f(z) is analytic in a region  $\Omega$  containing a, one has

$$f(z) = f(a) + \frac{f'(a)}{1!}(z-a) + \dots + \frac{f^{n-1}(a)}{(n-1)!}(z-a)^{n-1} + f_n(z)(z-a)^n,$$

where  $f_n(z)$  is analytic in  $\Omega$ . Moreover, if C is the boundary of a closed disk contained in  $\Omega$  with center a, then  $f_n(z)$  has the representation

$$f_n(z) = \frac{1}{2\pi i} \int_C \frac{f(\zeta) \, d\zeta}{(\zeta - a)^n (\zeta - z)} \qquad (z \text{ inside } C).$$

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 11: Isolated Singularities

(Text 126-130)

## Remarks on Lecture 11

Singularities: Let f(z) be holomorphic in a disk  $0 < |z - a| < \delta$  with the center a removed.

(i) If

$$\lim_{z \to a} f(z)$$

exist or if just

$$\lim_{z \to a} f(z)(z - a) = 0,$$

then a is a removable singularity and f extends to a holomorphic function on the whole disk  $|z-a|<\delta$ .

(ii) If

$$\lim_{z \to a} f(z) = \infty,$$

a is said to be a pole. In this case

$$f(z) = (z - a)^{-h} f_h(z),$$

where h is a positive integer and  $f_h(z)$  is holomorphic at a and  $f_h(a) \neq 0$ . We also have the polar development

$$f(z) = B_h(z-a)^{-h} + \dots + B_1(z-a)^{-1} + \varphi(z),$$

where  $\varphi(z)$  is holomorphic at a.

If neither (i) nor (ii) holds, a is said to be an essential singularity.

**Theorem 9** A holomorphic function comes arbitrarily close to any complex value in every neighborhood of an essential singularity.

<u>Simplified Proof:</u> Suppose statement false. Then  $\exists A \in \mathbb{C}$  and  $\delta > 0$  and  $\epsilon > 0$  such that

$$|f(z) - A| > \delta$$
 for  $|z - a| < \epsilon$ .

Then

$$\lim_{z \to a} (z - a)^{-1} (f(z) - A) = \infty.$$

So

$$(z-a)^{-1}(f(z)-A)$$

has a pole at z = a. Thus

$$f(z) - A = (z - a)(z - a)^{-h}g(z),$$

where  $h \in \mathbb{Z}^+$  and g(z) is holomorphic at z = a.

If h = 1, f(z) has a removable singularity at z = a. If h > 1, f(z) - A has a pole at z = a and so does f(z). Both possibilities are excluded by assumption, so the proof is complete. Q.E.D.

## Exercise 4 on p.130.

Suppose f is meromorphic in  $\mathbb{C} \cup \{\infty\}$ . We shall prove f is a rational function. If  $\infty$  is a pole, we work with g = 1/f, so we may assume  $\infty$  is not a pole. It is not an essential singularity, so  $\infty$  is a removable singularity. Thus for some R > 0, f(z) is bounded for  $|z| \geq R$ . Since the poles of f(z) are isolated, there are just finitely many poles in the disk  $|z| \leq R$ . (Poles of f(z) are zeroes of 1/f(z).) At a pole a, use the polar development near a

$$f(z) = B_h(z-a)^{-h} + \dots + B_1(z-a)^{-1} + \varphi(z).$$

The equation shows that  $\varphi$  extends to a meromorphic function on  $\mathbb{C} \cup \infty$  with one less pole than f(z). We can then do this argument with  $\varphi(z)$  and after iteration we obtain

$$f(z) = \sum_{i=1}^{n} P_i \left( \frac{1}{z - a_i} \right) + g(z),$$

where  $P_i$  are polynomials and g is holomorphic in  $\mathbb{C}$ . The formula shows that g is bounded for |z| > geR and being analytic on  $|z| \leq R$ , it thus must be bounded on  $\mathbb{C}$ . By Liouville's theorem, it is constant. So f is a rational function.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

# 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

# Lecture 12: The Local Mapping. Schwarz's Lemma and non-Euclidean interpretation

(Text 130-136)

## Remarks on Lecture 12

#### Proof of Theorem 11, p.131.

The last formula on p.131 reads

$$\sum_{j} n(\gamma, z_j(a)) = \sum_{j} n(\gamma, z_j(b)) \tag{1}$$

provided a and b belong to the same component of the set  $\mathbb{C} - \Gamma$ . In (1) we take for  $\gamma$  the circle

$$z(t) = z_0 + \epsilon e^{it} \qquad (0 \le t \le 2\pi),$$

where  $\epsilon > 0$  is so small that  $z_0$  is the only zero of

$$f(z) - w_0 = 0$$

inside  $\gamma$ . (The zeroes of  $f(z) - w_0 = 0$  are isolated.)

As before let  $\Gamma = f(\gamma)$  and let  $\Omega_0$  denote the component of  $\mathbb{C} - \Gamma$  containing  $w_0$ .

Since  $\gamma$  is a circle,

$$n(\gamma, z_j(a)) = 0$$
 or 1

depending on whether  $z_j(a)$  is outside  $\gamma$  or inside  $\gamma$  (Since  $a \notin \Gamma$ ,  $z_j(a) \notin \gamma$ ). Thus the left hand side of (1) equals the number of points inside  $\gamma$  where f takes the value a.

In (1) we now take a arbitrary in  $\Omega_0$  and take  $b = w_0$ . By the choice of  $\gamma$  he right hand side of (1) equals n. Equation (1) therefore shows that each value in  $\Omega_0$  is taken n times by f inside  $\gamma$  (multiple roots counted according to their multiplicity). In particular, this holds for any disk  $|w-w_0| < \delta$  inside  $\Omega_0$  with center  $w_0$ . Q.E.D.

**Remark**: In dealing with winding numbers  $n(\delta, z)$ , we have to pay attention to the parametrization. Thus if

$$\gamma(t) = e^{it} \ (0 \le t \le 2\pi), \qquad f(z) = z^n$$

and  $\Gamma = f(\gamma)$ , we have

$$n(\gamma, 0) = 1,$$
  $n(\Gamma, 0) = n$ 

although  $\gamma$  and  $\Gamma$  are represented geometrically by the same point set.

### Non-Euclidean Plane

This is the unit disk |z| < 1 with the following convention:

- a) Non-Euclidean point = Point in disk;
- b) Non-Euclidean line = Arc in disk perpendicular to the boundary.

This model satisfies all Euclid's axioms except the famous **Parallel Axiom**:

Given a point p outside a line l, there is exactly one line through the point which does not intersect l.

This axiom clearly fails in the above model; thereby solving the 2000 year old problem of proving the Parallel Axiom on the basis of the other axioms. It cannot be done!

We can now introduce distance in the non-Euclidean plane D.

Given  $z_1, z_2 \in D$ , mark the points u, v of intersection with |z| = 1, in the order indicated. We put

$$d(z_1, z_2) = \frac{1}{2} \log (z_1, z_2, v, u)$$
  
=  $\frac{1}{2} \log (\frac{z_1 - v}{z_1 - u} : \frac{z_2 - v}{z_2 - u}).$ 

The cross ratio is real (page 79) and the geometry shows easily that the cross ratio is  $\geq 1$ . So

$$d(z_1, z_2) \ge 0$$
,

$$d(z_1, z_2) = d(z_2, z_1).$$

It is also easy to show from the formula that

$$d(z_1, z_3) = d(z_1, z_2) + d(z_3, z_2).$$

Consider a fractional linear transformation

$$z \longrightarrow e^{i\varphi} \frac{z - z_2}{1 - \bar{z}_2 z}$$

mapping

$$z_2 \longrightarrow 0$$
 and  $z_1 \longrightarrow \left| \frac{z_1 - z_2}{1 - \bar{z}_2 z_1} \right|$ .

Then by the order of the points  $v, z_2, z_1, u$  we see that

$$v \longrightarrow -1$$
 and  $u \longrightarrow 1$ .

The invariance of the cross ratio gives

$$d(z_2, z_1) = \frac{1}{2} \log \left( 0, \left| \frac{z_2 - z_1}{1 - \bar{z}_2 z_1} \right|, -1, 1 \right)$$

$$= \frac{1}{2} \log \left( \frac{|1 - \bar{z}_2 z_1| + |z_1 - z_2|}{|1 - \bar{z}_2 z_1| - |z_1 - z_2|} \right)$$
 (Exercise 7).

Thus

$$d(z, z + \Delta z) = \frac{1}{2} \log \left( 1 + \frac{2|\Delta z|}{|1 - \overline{z}(z + \Delta z)| - |\Delta z|} \right).$$

So since

$$\lim_{x \to 0} \frac{\log(1+x)}{x} = 1$$

we deduce

$$\lim_{\Delta z \to 0} \frac{d(z,z+\Delta z)}{|\Delta z|} = \frac{1}{1-|z|^2}.$$

This suggests defining a non-Euclidean length of a curve

$$\gamma : z(t) \qquad (\alpha \le t \le \beta)$$

by

$$L(\gamma) = \int_{\gamma} \frac{|dz|}{1 - |z|^2}.$$

Exercises 1 and 6 now give the following geometric interpretation of Schwarz's Lemma:

<u>Ex 1.</u> Formula (30) implies by division, letting  $z \to z_0$ ,

$$\frac{|f'(z)|}{1 - |f(z)|^2} \le \frac{1}{1 - |z|^2}.$$

 $\underline{\underline{\operatorname{Ex}\ 6.}}$  Let  $f:D\to D$  be holomorphic and  $f(\gamma)$  the image curve

$$w(t) = f(z(t))$$
  $\alpha \le t \le \beta$ 

of the curve  $\gamma$  above. Then

$$L(f(\gamma)) = \int_{\alpha}^{\beta} \frac{|w'(t)|}{1 - |w(t)|^2} dt$$

$$= \int_{\alpha}^{\beta} \frac{|f'(z(t))z'(t)|}{1 - |f(z(t))|^2} dt$$

$$\leq \int_{\alpha}^{\beta} \frac{|z'(t)|}{1 - |z(t)|^2} \quad \text{(by Ex 1.)}$$

$$= L(\gamma).$$

Thus

$$L(f(\gamma)) \le L(\gamma)$$

as stated.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 13: The General Cauchy Theorem

(Replacing Text 137-148)

Here we shall give a brief proof of the general form of Cauchy's Theorem. (cf. John D. Dixon, A brief proof of Cauchy's integral theorem, *Proc. Amer. Math. Soc.* 29, (1971) 625-626.)

**Definition 1** A closed curve  $\gamma$  in an open set  $\Omega$  is homologous to 0 (written  $\gamma \sim 0$ ) with respect to  $\Omega$  if

$$n(\gamma, a) = 0$$
 for all  $a \notin \Omega$ .

**Definition 2** A region is **simply connected** if its complement with respect to the extended plane is connected.

**Remark:** If  $\Omega$  is simply connected and  $\gamma \subset \Omega$  a closed curve, then  $\gamma \sim 0$  with respect to  $\Omega$ . In fact,  $n(\gamma, z)$  is constant in each component of  $\mathbb{C} - \gamma$ , hence constant in  $\mathbb{C} - \Omega$  and is 0 for z sufficiently large.

**Theorem 1 (Cauchy's Theorem)** If f is analytic in an open set  $\Omega$ , then

$$\int_{\gamma} f(z) \ dz = 0$$

for every closed curve  $\gamma \subset \Omega$  such that  $\gamma \sim 0$ .

In particular, if  $\Omega$  is simply connected then  $\int_{\gamma} f(z) dz = 0$  for every closed  $\gamma \subset \Omega$ .

We shall first prove

**Theorem 2** (Cauchy's Integral Formula) Let f be holomorphic in an open set  $\Omega$ . Then

$$n(\gamma, z)f(z) = \frac{1}{2\pi i} \int_{\gamma} \frac{f(\zeta)}{\zeta - z} d\zeta \tag{1}$$

where  $\gamma \sim 0$  with respect to  $\Omega$ .

*Proof:* The prove is based on the following three claims.

Define  $g(z,\zeta)$  on  $\Omega \times \Omega$  by

$$g(z,\zeta) = \begin{cases} \frac{f(\zeta) - f(z)}{\zeta - z} & \text{for } z \neq \zeta, \\ f'(z) & \text{for } z = \zeta. \end{cases}$$

Claim 1: g is continuous on  $\Omega \times \Omega$  and holomorphic in each variable and  $g(z,\zeta) = g(\zeta,z)$ .

Clearly g is continuous outside the diagonal in  $\Omega \times \Omega$ . Let  $(z_0, z_0)$  be a point on the diagonal and  $D \subset \Omega$  a disk with center  $z_0$ . Let  $z \neq \zeta$  in D. Then by Theorem 8

$$g(z,\zeta) - g(z_0,z_0) = f'(\zeta) + \frac{1}{2}f_2(z)(z-\zeta) - f'(z_0).$$

So the continuous at  $(z_0, z_0)$  is obvious.

For the holomorphy statement, it is clear that for each  $\zeta_0 \in \Omega$  the function

$$z \mapsto g(z, \zeta_0)$$

is holomorphic on  $\Omega - \zeta_0$ . Since

$$\lim_{z \to \zeta_0} g(z, \zeta_0)(z - \zeta_0) = 0$$

the point  $\zeta_0$  is a removable singularity (Theorem 7, p.124), so

$$z \mapsto q(z,\zeta_0)$$

is indeed holomorphic on  $\Omega$ . This proves Claim 1.

Let

$$\Omega' = \{ z \in \mathbb{C} - (\gamma) : n(\gamma, z) = 0 \}.$$

Define function h on  $\mathbb{C}$  by

$$h(z) = \frac{1}{2\pi i} \int_{\gamma} g(z, \zeta) \ d\zeta, \qquad z \in \Omega;$$
 (2)

$$h(z) = \frac{1}{2\pi i} \int_{\gamma} \frac{f(\zeta)}{\zeta - z} \, d\zeta, \qquad z \in \Omega'.$$
 (3)

Since both expression agree on  $\Omega \cap \Omega'$  and since  $\Omega \cup \Omega' = \mathbb{C}$ , this is a valid definition.

## Claim 2: h is holomorphic.

This is obvious on the open sets  $\Omega'$  and  $\Omega - \gamma$ . To show holomorphy at  $z_0 \in \gamma$ , consider a disk  $D \subset \Omega$  with center  $z_0$ . Let  $\delta$  be any closed curve in D. Then

$$\int_{\delta} h(z) \ dz = \frac{1}{2\pi i} \int_{\delta} \left( \int_{\gamma} g(z, \zeta) \ d\zeta \right) dz$$
$$= \frac{1}{2\pi i} \int_{\gamma} \left( \int_{\delta} g(z, \zeta) \ dz \right) d\zeta.$$

For each  $\zeta$ ,

$$z \mapsto g(z,\zeta)$$

is holomorphic on D (even  $\Omega$ ). So by the Cauchy's theorem for disks,

$$\int_{\delta} g(z,\zeta) \ dz = 0.$$

Now the Morera's Theorem implies h is holomorphic.

Now we can prove:

Claim 3:  $h \equiv 0$ , so (1) holds.

We have  $z \in \Omega'$  for |z| sufficiently large. So by (3),

$$\lim_{z \to \infty} h(z) = 0.$$

By Liouville's Theorem,  $h \equiv 0$ .

Q.E.D.

Proof of Theorem 1: To derive Cauchy's theorem, let  $z_0 \in \Omega - \gamma$  and put

$$F(z) = (z - z_0)f(z).$$

By (1),

$$\frac{1}{2\pi i} \int_{\gamma} f(z) dz = \frac{1}{2\pi i} \int_{\gamma} \frac{F(z)}{z - z_0} dz$$
$$= n(\gamma, z_0) F(z_0)$$
$$= 0.$$

Q.E.D.

Note finally that <u>Corollary 2</u> on p.142 is an immediately consequence of Cauchy's Theorem.

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

# 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 14: The Residue Theorem and Application

(Replacing Text 148-154)

Let  $\Omega$  be a region and  $a \in \Omega$ . Let f(z) be holomorphic in  $\Omega' = \Omega - a$ 

**Definition 1** The **residue** is defined as

$$R = Res_{z=a} f(z) \triangleq \frac{1}{2\pi i} \int_C f(z) \ dz,$$

where C is any circle contained in  $\Omega$  with center a.

If C' is another circle with center a and

$$C' \subset \Omega$$
,

then Cauchy's Theorem for the annulus shows that

$$\operatorname{Res}_{z=a} f(z)$$

is independence of the choice of C.

While the definition can be shown to be equivalent to Definition 3 on p.149 in the text, we shall not need this.

In place of Theorem 17 (Text p.150) we shall prove the following version:

**Theorem 17** 'Let f be analytic except for isolated singularities  $a_j$  in a region  $\Omega$ . Let  $\gamma$  be a simple closed curve which has interior contained in  $\Omega$  and  $a_j \notin \gamma$  (all j). Then

$$\frac{1}{2\pi i} \int_{\gamma} f(z) \ dz = \sum_{i} Res_{z=a_{i}} f(z).$$

where the sum ranges over all  $a_i$  inside  $\gamma$ .

Proof:

By compactness of  $\gamma$  and its interior, the sum above is finite. For simplicity let  $a_1, a_2$  be the singularities inside  $\gamma$ .

The outside of  $\gamma$  is connected and if we take two disks  $D_1, D_2$  around  $a_1$  and  $a_2$  and connect their boundaries to  $\gamma$  with "bridges" as in Fig. 14-3, the piece remaining in the interior of  $\gamma$  is simply connected (the complement is connected). Thus the integral over the boundary of this region is 0.

Letting the widths of the bridges tend to 0, the theorem follows. Q.E.D.

#### Calculation of residues.

1. *If* 

$$\lim_{z \to a} f(z)(z-a)$$

exists and is finite, then it equals  $Res_{z=a}f(z)$ .

In fact a is then a pole of f(z), so

$$f(z) = B_h(z-a)^{-h} + \dots + B_1(z-a)^{-1} + \varphi(z), \qquad B_h \neq 0.$$

Then

$$\frac{1}{2\pi i} \int_C f(z) \ dz = B_1$$

and since the singular part above equals

$$(z-a)^{-h}(B_h+B_{h-1}(z-a)+\cdots+B_1(z-a)^{h-1})$$

the finiteness of the limit implies  $h \leq 1$ .

2. If  $f(z) = \frac{g(z)}{h(z)}$  where  $g(a) \neq 0$  and h(z) has a simple zero at z = a, then

$$Res_{z=a}f(z) = \frac{g(a)}{h'(a)}.$$

In fact

$$\lim_{z \to a} f(a)(z - a) = \lim_{z \to a} g(z) \frac{1}{\frac{h(z) - h(a)}{z - a}} = \frac{g(a)}{h'(a)}.$$

3. If f has a pole of order h, then

$$Res_{z=a}f(z) = \frac{1}{(h-1)!} \left\{ \frac{d^{h-1}}{dz^{h-1}} (z-a)^h f(z) \right\}_{z=a}.$$

In fact

$$f(z) = (z - a)^{-h}g(z),$$

where q is holomorphic at a. So

$$g^{(h-1)}(a) = (h-1)! \frac{1}{2\pi i} \int_C \frac{g(z)}{(z-a)^h} dz = (h-1)! \operatorname{Res}_{z=a} f(z).$$

Example: (from text p.151.)

$$f(z) = \frac{e^z}{(z-a)^2} \implies \operatorname{Res}_{z=a} f(z) = \left(\frac{d}{dz}e^z\right)_{z=a} = e^a.$$

### Application: The Argument Principle.

**Theorem 18** 'Let f(z) be meromorphic in  $\Omega$ ,  $\gamma \subset \Omega$  a simple closed curve with interior inside  $\Omega$ . Assume  $\gamma$  passes through no zeros nor poles of f. Then

$$\frac{1}{2\pi i} \int_{\gamma} \frac{f'(z)}{f(z)} dz = N - P,$$

where N is the number of zeros, P the number of poles inside  $\gamma$ , all counted with multiplicity.

*Proof:* By theorem 17', the integral is the sum of the residues of f'(z)/f(z).

At a zero a of order h, we have

$$f(z) = (z - a)^h f_h(z), f_h(a) \neq 0$$

and

$$\frac{f'(z)}{f(z)} = \frac{h}{z - a} + \frac{f'_h(z)}{f_h(z)} \Longrightarrow \text{Residue } h,$$

At a pole b of order k, we have similarly

$$\frac{f'(z)}{f(z)} = \frac{-k}{z - b} + \frac{f'_h(z)}{f_h(z)} \Longrightarrow \text{Residue } -k.$$

Now the result follows from Theorem 17'.

Q.E.D.

Corollary 1 (Rouche's Theorem) Let f and g be holomorphic in a region  $\Omega$ . Let  $\gamma$  be a simple closed curve in  $\Omega$  with interior  $\subset \Omega$ . Assume

$$|f(z) - g(z)| < f(z)$$
 on  $\gamma$ .

Then f and g have the same number of zeros inside  $\gamma$ , say  $N_f$  and  $N_g$ .

*Proof:* (The text does not take into account the case when f and g have common zeros). The inequality implies that f and g are zero-free on  $\gamma$ . Put

$$\psi(z) = \frac{g(z)}{f(z)},$$

then

$$|\psi(z) - 1| < 1$$

on  $\gamma$ , so the curve  $\Gamma = \psi(\gamma)$  lies in the disk  $|\zeta - 1| < 1$ . Hence

$$\frac{1}{2\pi i} \int_{\gamma} \frac{\psi'(z)}{\psi(z)} dz = \int_{\Gamma} \frac{d\zeta}{\zeta} = n(\Gamma, 0) = 0$$

(book p.116). Now

$$N_g = \frac{1}{2\pi i} \int_{\gamma} \frac{g'(z)}{g(z)} dz$$

$$= \frac{1}{2\pi i} \int_{\gamma} \frac{\psi' f + \psi f'}{\psi f} dz$$

$$= \frac{1}{2\pi i} \int_{\gamma} \frac{\psi'(z)}{\psi(z)} dz + \frac{1}{2\pi i} \int_{\gamma} \frac{f'(z)}{f(z)} dz$$

$$= N_f.$$

This proves the result.

Q.E.D.

#### Exercise 2 p.154

We use Rouche's theorem twice, first on  $\gamma:|z|=2$  and then on  $\gamma:|z|=1.$ 

For 
$$\gamma: |z| = 2$$
, take  $f(z) = z^4$ ,  $g(z) = z^4 - 6z + 3$ .

For 
$$\gamma : |z| = 1$$
, take  $f(z) = -6z$ ,  $g(z) = z^4 - 6z + 3$ .

---

# 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 15: Contour Integration and Applications

(Text 154-161)

### Remarks on Lecture 15

In parts 4 and 5 (p. 154-160) some clarification of the use of the logarithm are called for.

#### Example 4 p.159

The relation

$$(-z)^{2\alpha} = e^{2\pi i\alpha}z^{2\alpha}$$

which is crucial for proof deserves explanation.

Fig. 15-1

We consider the function

$$\log_{\theta} z = \log|z| + i\arg_{\theta} z$$

in the region  $\mathbb{C} - l_{\theta}$  (the plane with the ray  $l_{\theta}$  removed) where the angle is fixed by

$$\theta < \arg_{\theta} z < \theta + 2\pi.$$

In the problem of computing

$$\int_0^\infty x^\alpha R(x) \ dx$$

we consider

$$\log_{-\frac{\pi}{2}}(z)$$

in the plane  $\mathbb{C}$  with the negative imaginary axis removed and us the Residue theorem on the contour in Fig. 4.13. As in the text we arrive at the integral

$$\int_{-\infty}^{\infty} z^{2\alpha+1} R(z^2) \ dz = \int_{0}^{\infty} \left( z^{2\alpha+1} + (-z)^{2\alpha+1} \right) R(z^2) \ dz.$$

On the right z belongs to  $(0, \infty)$  and

$$\log_{-\frac{\pi}{2}}(z) = \log|z| + \left(-\frac{\pi}{2} + \frac{\pi}{2}\right)i, \qquad \frac{-\pi}{2} < \arg_{-\frac{\pi}{2}}z < \frac{3\pi}{2},$$

$$\log_{-\frac{\pi}{2}}(-z) = \log|z| + \left(-\frac{\pi}{2} + \frac{3\pi}{2}\right)i$$

$$= \log_{-\frac{\pi}{2}}(z) + i\pi, \qquad z > 0.$$

Thus for z > 0,

$$(-z)^{2\alpha+1} = e^{(2\alpha+1)\log_{-\frac{\pi}{2}}(-z)}$$

$$= e^{(2\alpha+1)(\log|z|+i\pi)}$$

$$= -e^{2\alpha i\pi}z^{2\alpha+1},$$

so the last integrals combine to

$$(1 - e^{2\alpha i\pi}) \int_0^\infty z^{2\alpha+1} R(z^2) dz.$$

For z > 0 we have from the above

$$\log_{-\frac{\pi}{2}}(z) = \log|z|,$$

SO

$$\frac{1}{2\pi i} \int_{-\infty}^{\infty} z^{2\alpha+1} R(z^2) dz = \frac{1}{2\pi i} (1 - e^{2\alpha i\pi}) \int_{0}^{\infty} x^{2\alpha+1} R(x^2) dx 
= -\frac{1}{\pi} e^{\alpha\pi i} \sin \pi \alpha \int_{0}^{\infty} x^{2\alpha+1} R(x^2) dx.$$
(1)

The left hand side of (1) is the sum of the residues of

$$z^{2\alpha+1}R(z^2) = f(z)$$

in the upper half plane. If

$$R(z^2) = \frac{g(z)}{h(z)},$$

where g and h are holomorphic,  $g(a) \neq 0$ , and h has a simple zero at a, then

$$\operatorname{Res}_{z=a} f(z) = z^{(2\alpha+1)}(a) \frac{g(a)}{h'(a)}, \tag{2}$$

where

$$z^{2\alpha+1} = e^{(2\alpha+1)\log_{-\frac{\pi}{2}}(z)}.$$

#### Example: Exercise 3(g) p.161

To calculate

$$\int_0^\infty x^{\frac{1}{3}} \frac{dx}{1+x^2},$$

we use  $x = t^2$  and arrive at

$$\int_{-\infty}^{\infty} z^{\frac{5}{3}} \frac{dz}{1+z^4}$$

in (1). The poles in the upper half plane are

$$z = e^{i\frac{\pi}{4}}$$
 and  $z = e^{i(\frac{\pi}{4} + \frac{\pi}{2})}$ .

We use (2) to calculate the residues:

$$\operatorname{Res}_{z=e^{i\frac{\pi}{4}}} \left( z^{\frac{5}{3}} \frac{1}{1+z^4} \right) = z^{\frac{5}{3}} \left( e^{i\frac{\pi}{4}} \right) \frac{1}{4(e^{i\frac{\pi}{4}})^3}$$

$$= e^{\frac{5}{3}\log_{-\frac{\pi}{2}}(e^{i\frac{\pi}{4}})} \frac{1}{4(e^{i\frac{\pi}{4}})^3}$$

$$= e^{\frac{5}{3}\left(i\frac{\pi}{4}\right)} \frac{1}{4(e^{i\frac{\pi}{4}})^3}$$

$$= \frac{1}{4}e^{-i\frac{\pi}{3}},$$

and

$$\operatorname{Res}_{z=e^{i\frac{3\pi}{4}}} \left( z^{\frac{5}{3}} \frac{1}{1+z^4} \right) = z^{\frac{5}{3}} \left( e^{i\frac{3\pi}{4}} \right) \frac{1}{4(e^{i\frac{3\pi}{4}})^3}$$

$$= e^{\frac{5}{3} \log_{-\frac{\pi}{2}} \left( i \left( -\frac{\pi}{2} + \frac{5\pi}{4} \right) \right)} \frac{1}{4(e^{i\frac{3\pi}{4}})^3}$$

$$= \frac{1}{4} e^{-i\pi}.$$

Thus (1) gives

$$\frac{1}{4}e^{-i\frac{\pi}{3}} + \frac{1}{4}e^{-i\pi} = -\frac{1}{\pi}e^{\frac{1}{3}\pi i}\sin\frac{\pi}{3}\int_0^\infty x^{\frac{5}{3}}\frac{dx}{1+x^4},$$

SO

$$\int_0^\infty x^{\frac{5}{3}} \frac{dx}{1+x^4} = \frac{\pi}{2\sqrt{3}}.$$

#### Example 5 p.160

The last four lines on the page are a bit misleading because the specific logarithm has already been chosen. So here is a completion of the proof after the equation

$$\int_0^\pi \text{Log}(-2ie^{ix}\sin x) \ dx = 0.$$

We know (Lecture 2) that

$$Log(z_1 z_2) = Log z_1 + Log z_2, \quad \text{if } -\pi < Arg z_1 + Arg z_2 < \pi.$$
 (3)

Using this for  $z = 2 \sin x$  we get

$$\int_0^{\pi} \log(2\sin x) \ dx + \int_0^{\pi} \log(-ie^{ix}) \ dx = 0.$$
 (4)

But

$$Log(-i) = -\frac{\pi i}{2}, \qquad Loge^{ix} = ix \ (0 < x < \pi),$$

so since  $-\frac{\pi}{2} + x$  is in  $(-\pi, \pi)$ , (3) implies

$$Log(-ie^{ix}) = -\frac{\pi i}{2} + ix.$$

Now (4) implies the result

$$\int_0^{\pi} \log \sin \theta \ d\theta = -\pi \log 2.$$

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

# 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 16: Harmonic Functions

(Replacing Text 162-170)

While integrals like  $\int_{\gamma} f(z) dz$  and  $\int_{\gamma} M dx + N dy$  have been defined in the text (p.101), differential forms like dx, dy and dz = dx + i dy have not been defined (and the definition is more subtle), we shall develop the theory of harmonic functions (p.162-170) without differential forms.

**Definition 1** A real-valued function u(z) = u(x,y) in a region  $\Omega$  is harmonic if it is  $C^2$  and satisfying the equation

$$\frac{\partial^2 u}{\partial x^2} + \frac{\partial^2 u}{\partial y^2} = 0.$$

The Cauchy-Riemann equations for a holomorphic function imply quickly that the real and imaginary parts of a holomorphic function are harmonic. The converse holds if  $\Omega$  is simply connected:

**Theorem 1** If  $\Omega$  is simply connected and u harmonic in  $\Omega$ , there exists a holomorphic function f(z) such that

$$u(z) = Ref(z).$$

**Remark:** Note the condition  $\underline{\Omega}$  is simply connected can not be removed, for example  $u(z) = \log |z|$  is harmonic in the punctured plane  $\mathbb{C} - \{0\}$ , but it cannot be written as real part of a holomorphic function.

*Proof:* Put

$$g(z) = \frac{\partial u}{\partial x} - i \frac{\partial u}{\partial y} = u_1 + i v_1.$$

Then

$$\frac{\partial u_1}{\partial x} = \frac{\partial^2 u}{\partial x^2} = -\frac{\partial^2 u}{\partial y^2} = \frac{\partial v_1}{\partial y},$$

$$\frac{\partial u_1}{\partial y} = \frac{\partial^2 u}{\partial x \partial y} = -\frac{\partial v_1}{\partial x}.$$

So by the Cauchy-Riemann equation, g is holomorphic. By p.142, since  $\Omega$  is simply connected,

$$g(z) = f'(z)$$

for some holomorphic function f. Writing

$$f(z) = U(x, y) + iV(x, y),$$

we have by the Cauchy-Riemann equation

$$g(z) = f'(z) = \frac{\partial U}{\partial x} - i \frac{\partial U}{\partial y},$$

SO

$$u(x,y) = U(x,y) + \text{constant.}$$

Thus

$$u(z) = \text{Re}f(z) + \text{constant}.$$

Q.E.D.

Corollary 1 (cf. (34) p.134) If u is harmonic in  $\Omega$ , then if the disk  $|z - z_0| \le r$  lies in  $\Omega$ ,

$$u(z_0) = \frac{1}{2\pi} \int_0^{2\pi} u(z_0 + re^{i\theta}) \ d\theta.$$

More generally, if the annulus  $r_1 \leq |z - z_0| \leq r_2$  belongs to a region  $\Omega$ , we have

**Theorem 20** If u is harmonic in  $\Omega$ , and  $\{z : r_1 \leq |z - z_0| \leq r_2\} \in \Omega$ , then

$$\frac{1}{2\pi} \int_0^{2\pi} u(z_0 + re^{i\theta}) \ d\theta = \alpha \log r + \beta, \qquad r_1 \le r \le r_2, \tag{1}$$

where  $\alpha$  and  $\beta$  are constants.

*Proof:* The function  $z \mapsto u(z_0 + z)$  is harmonic, so writing the Laplacian in polar coordinates,

$$\Delta = \frac{\partial^2}{\partial r^2} + \frac{1}{r} \frac{\partial}{\partial r} + \frac{1}{r^2} \frac{\partial^2}{\partial \theta^2}.$$

Denote the left hand side of (1) by V(r), then

$$\frac{\partial^2 V}{\partial r^2} + \frac{1}{r} \frac{\partial V}{\partial r} = 0.$$

Writing this as

$$\frac{\partial}{\partial r} \left( r \frac{\partial V}{\partial r} \right) = 0,$$

the theorem follows.

Q.E.D.

### The Poisson Formula

Let u be harmonic on  $|z| \leq 1$ . Then

$$u = \operatorname{Re}(f)$$

where f is holomorphic on  $|z| \leq 1$ . Consider

$$S(z) = \frac{z+a}{1+\bar{a}z},$$
 (|a| < 1)

which maps the unit disk onto itself. Then  $f \circ S$  is holomorphic and  $u \circ S$  is harmonic (the real part of  $f \circ S$ ). Use the corollary on it with  $z_0 = 0$ , then

$$u(a) = u(S(0)) = \frac{1}{2\pi} \int_0^{2\pi} u(S(e^{i\varphi})) d\varphi.$$

But

 $S(e^{i\varphi}) = \frac{e^{i\varphi} + a}{1 + \bar{a}e^{i\varphi}} = e^{i\theta},$ 

SO

$$e^{i\varphi} = \frac{e^{i\theta} - a}{1 - \bar{a}e^{i\theta}}.$$

Hence

$$ie^{i\varphi}\frac{d\varphi}{d\theta} = \frac{ie^{i\theta} - |a|^2 ie^{i\theta}}{(1 - \bar{a}e^{i\theta})^2},$$

or

$$\frac{d\varphi}{d\theta} = \frac{ie^{i\theta} - |a|^2 ie^{i\theta}}{(1 - \bar{a}e^{i\theta})^2} \cdot \frac{1}{i} \cdot \frac{1 - \bar{a}e^{i\theta}}{e^{i\theta} - a}$$

$$= \frac{1 - |a|^2}{|e^{i\theta} - a|^2}.$$
(2)

This gives

Poisson's Formula ((63) in text)

$$u(a) = \frac{1}{2\pi} \int_0^{2\pi} u(e^{i\theta}) \frac{d\varphi}{d\theta} d\theta = \frac{1}{2\pi} \int_{|z|=1} \frac{1 - |a|^2}{|z - a|^2} u(z) d\theta.$$

### Schwarz' Theorem

**Theorem 2 (Schwarz' Theorem)** Let U be a real piecewise continuous function on |z| = 1 and define the Poisson integral  $u(z) = P_U(z)$  by

$$u(a) = \frac{1}{2\pi} \int_0^{2\pi} \frac{1 - |a|^2}{|a - e^{i\varphi}|^2} U(e^{i\varphi}) \ d\varphi, \qquad |a| < 1.$$
 (3)

Then u is harmonic, and

$$\lim_{z \to e^{i\varphi_0}} u(z) = U(e^{i\varphi_0})$$

if U is continuous at  $e^{i\varphi_0}$ .

*Proof:* We may assume  $\varphi_0 = 0$ . Since

$$\frac{1-|z|^2}{|z-e^{i\varphi}|^2} = \operatorname{Re}\left(\frac{e^{i\varphi}+z}{e^{i\varphi}-z}\right),\,$$

u is the real part of a holomorphic function, hence harmonic.

Because of (2) formula (3) can be written

$$u(S(0)) = \frac{1}{2\pi} \int_0^{2\pi} U(S(e^{i\varphi})) \ d\varphi.$$

Taking  $a = \tanh t$  we obtain as  $t \to \infty$ 

$$u(\tanh t) = \frac{1}{2\pi} \int_0^{2\pi} U\left(\frac{e^{i\varphi} + \tanh t}{\tanh t e^{i\varphi} + 1}\right) d\varphi$$
$$\longrightarrow \frac{1}{2\pi} \int_0^{2\pi} U(1) d\varphi$$
$$= U(1).$$

Q.E.D.

#### Exercise 5, p.171

Since  $\log |1+z|$  is harmonic in |z| < 1 we have by the mean-value theorem

$$\frac{1}{2\pi} \int_{-\pi}^{\pi} \log|1 + re^{i\theta}| \ d\theta = \log 1 = 0 \tag{4}$$

for r < 1. We shall now show that

$$\left|\log\left|1 + re^{i\theta}\right|\right|$$

is bounded by an integrable function  $g(\theta)$ . So by the <u>dominated convergence theorem</u> we can let  $r \to 1$  under the integral sign, giving the <u>desired result</u>

$$\int_{-\pi}^{\pi} \log|1 + e^{i\theta}| \ d\theta = 0. \tag{5}$$

Since the integrand  $\log |1 + e^{i\theta}|$  changes sign on the circle, we split the circle into the two arcs  $(-\frac{2\pi}{3}, \frac{2\pi}{3})$  and  $(\frac{2\pi}{3}, \frac{4\pi}{3})$ , where we have

$$|1 + e^{i\theta}| \ge 1$$

and

$$|1 + e^{i\theta}| \le 1$$

respectively. In the first interval we have  $\cos \theta \ge -\frac{1}{2}$  so

$$\frac{\sqrt{3}}{2} \le |1 + re^{i\theta}| \le |1 + e^{i\theta}| = 2\cos\frac{\theta}{2}, \qquad |\theta| \le \frac{2\pi}{3}, \text{ and } r \ge \frac{1}{2}.$$
 (6)

In the second interval we put  $\theta = \pi + \varphi$  and we see from the geometry, since  $|\varphi| \leq \frac{\pi}{3}$ , that

$$1 \ge |1 + re^{i\theta}| = |1 - re^{i\varphi}| \ge 1 - \cos\varphi = 2\cos^2\frac{\theta}{2}, \qquad \frac{2\pi}{3} \le \theta \le \frac{4\pi}{3}.$$
 (7)

Since  $\log \left| \cos \frac{\theta}{2} \right|$  is integrable, the estimates (6) and (7) show that  $|\log |1 + re^{i\theta}||$  is bounded by an integrable function  $g(\theta)$ , so (5) is established.

---

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 17: Mittag-Leffer's Theorem

(Text 187-190)

**Theorem 1 (Mittag-Leffer's Theorem)** Let  $\{b_{\nu}\}$  be a sequence in  $\mathbb{C}$  such that

$$\lim_{\nu \to \infty} b_{\nu} = \infty,$$

and  $P_{\nu}(\zeta)$  polynomials without constant term. Then there exist functions f meromorphic in  $\mathbb{C}$  with poles at just the points  $b_{\nu}$  and corresponding singular parts

$$P_{\nu}\left(\frac{1}{z-b_{\nu}}\right).$$

The most general f(z) of this kind can be written

$$f(z) = g(z) + \sum_{\nu} \left[ P_{\nu} \left( \frac{1}{z - b_{\nu}} \right) - p_{\nu}(z) \right]$$
 (1)

where g is holomorphic in z and the  $p_{\nu}$  are polynomials.

Proof: We may assume all  $b_{\nu} \neq 0$ . Consider the Taylor series for  $P_{\nu}\left(\frac{1}{z-b_{\nu}}\right)$  around z=0. It is analytic for  $|z|<|b_{\nu}|$ . Let  $p_{\nu}(z)$  be the partial sum up to  $z^{n_{\nu}}$  ( $n_{\nu}$  to be determined later). Consider the finite Taylor series of

$$\varphi(z) = P_{\nu} \left( \frac{1}{z - b_{\nu}} \right)$$

in a disk D with center 0. By (29) on p.126,

$$\varphi_n(z) = \frac{1}{2\pi i} \int_C \frac{\varphi(\zeta)}{\zeta^n(\zeta - z)} d\zeta.$$

Taking C as the circle with center 0 and radius  $\frac{|b_{\nu}|}{2}$  and  $n = n_{\nu} + 1$  we deduce

$$|\varphi_{n_{\nu}+1}(z)| \le \frac{1}{2\pi} 2\pi \frac{|b_{\nu}|}{2} \frac{M_{\nu}}{(\frac{1}{2}|b_{\nu}|)^{n_{\nu}+1} \cdot \frac{|b_{\nu}|}{4}} \quad \text{for } |z| \le \frac{|b_{\nu}|}{4},$$

where

$$M_{\nu} = \max_{z \in C} \left| P_{\nu} \left( \frac{1}{z - b_{\nu}} \right) \right|.$$

Thus by Theorem 8 on p.125,

$$\left| P_{\nu} \left( \frac{1}{z - b_{\nu}} \right) - p_{\nu}(z) \right| \le 2M_{\nu} \left( \frac{2|z|}{|b_{\nu}|} \right)^{n_{\nu} + 1} \quad \text{for } |z| \le \frac{|b_{\nu}|}{4}.$$
 (2)

We now select  $n_{\nu}$  large enough so that

$$2^{n_{\nu}} > M_{\nu} 2^{\nu}$$
.

Then

$$2M_{\nu} \left(\frac{2|z|}{|b_{\nu}|}\right)^{n_{\nu}+1} \le 2^{-\nu} \quad \text{for } |z| \le \frac{|b_{\nu}|}{4}.$$

We claim now that the sum (1) converges uniformly in each disk  $|z| \leq R$  (except at the poles) and thus represents a meromorphic function h(z). To see this we split the sum in (1):

$$h(z) = \sum_{\frac{|b_{\nu}|}{4} \le R} \left( P_{\nu} \left( \frac{1}{z - b_{\nu}} \right) - p_{\nu}(z) \right) + \sum_{\frac{|b_{\nu}|}{4} > R} \left( P_{\nu} \left( \frac{1}{z - b_{\nu}} \right) - p_{\nu}(z) \right). \tag{3}$$

Because of (2), the second sum is holomorphic for  $|z| \leq R$  since  $R \leq \frac{|b_{\nu}|}{4}$ . The first sum is finite and has

$$P_{\nu}\left(\frac{1}{z-b_{\nu}}\right)$$

as the singular part at the pole  $b_{\nu}$ .

This proves the existence. If f is any other meromorphic function with these properties, then f(z) - h(z) is holomorphic. Q.E.D.

## Exercise 3 on p.178

Here we need some preparation on series of the form

$$\sum_{n=1}^{\infty} a_n v_n$$

and use on

$$a_n = (-1)^n$$
,  $v_n = (1+n)^{-s}$ ,  $s = \sigma + it$ .

We have if

$$A_n = a_0 + \dots + a_n,$$

then

$$A_0v_0 + \sum_{n=1}^{N} (A_n - A_{n-1})v_n - \sum_{n=0}^{N-1} A_n(v_n - v_{n+1}) = A_Nv_N.$$

**Lemma 1** If  $(A_n)$  is bounded,  $v_n \to 0$ , and

$$\sum_{n=1}^{\infty} |v_n - v_{n+1}| < \infty,$$

then  $\sum_{n=0}^{\infty} a_n v_n$  converges.

This is obvious from the identity above.

In our example,

$$v_n = |(1+n)^{-s}| = \frac{1}{(1+n)^{\sigma}},$$

so  $v_n \to 0$  even uniformly on compact subsets of Res > 0. For  $v_n - v_{n+1}$  we have

$$v_n - v_{n+1} = \frac{1}{(n+1)^s} - \frac{1}{(n+2)^s} = s \int_{n+1}^{n+2} x^{-s-1} dx,$$

SO

$$|v_n - v_{n+1}| \le |s| \frac{1}{(n+1)^{\sigma+1}}.$$

Thus

$$\sum_{n=1}^{\infty} (-1)^{n-1} \frac{1}{n^s}$$

converges, and actually uniformly on compact sets in the region  $\sigma > 0$  because this is the case with  $v_n \to 0$  and  $\sum |v_n - v_{n+1}|$ .

## Exercise 1 on p.186

For a given annulus

$$R_1 < |z - a| < R_2,$$

the expansion

$$\sum_{-\infty}^{\infty} A_n (z-a)^{-n}$$

is unique because the coefficients are determined by (3). For different annuli (even with the same center) the expansion for a given function may be different. Consider

$$\frac{1}{z-a} = \frac{1}{z-b-(a-b)}$$

$$= \frac{1}{1-\frac{z-b}{a-b}} \frac{1}{b-a}$$

$$= \frac{1}{1-\frac{a-b}{z-b}} \frac{1}{z-b}.$$

The first formula gives

$$\frac{1}{z-a} = \frac{1}{b-a} \sum_{n=0}^{\infty} \left(\frac{z-b}{a-b}\right)^n \quad \text{for } 0 < |z-b| < |a-b|,$$

the second

$$\frac{1}{z-a} = \frac{1}{z-b} \sum_{n=0}^{\infty} \left(\frac{a-b}{z-b}\right)^n \quad \text{for } |a-b| < |z-b| < \infty.$$

---

## Lecture 18: Infinite Products

(Text 191-200)

## Remarks on Lecture 18

Problem 1 on p.197: Suppose that  $a_n \to \infty$  (all different, a condition missing in text) and  $A_n$  arbitrary complex numbers. Show that there exists an entire function f(z) which satisfies  $f(a_n) = A_n$ .

*Proof:* (A simpler alternative to the hint in text). Let g(z) be an analytic function with simple zeros at the  $a_n$ . By the Mittag-Leffler theorem, there exists a meromorphic function h on  $\mathbb{C}$  with poles exactly at the points  $a_n$  with the corresponding singular part

$$\frac{A_n/b_n}{z-a_m}$$
.

Then

$$f(z) = g(z)h(z)$$

has the desired property.

Q.E.D.

## Remarks on the formula for $\pi \cot \pi z$ (line 8 p.197)

Since the product formula for  $\sin \pi z$  has infinitely many factors taking the logarithmic derivative requires justification. Generally, write

$$f(z) = \prod_{1}^{\infty} f_n(z) = \lim_{N \to \infty} \prod_{1}^{N} f_n(z) = \lim_{N \to \infty} g_N(z)$$

the convergence being uniform on compacts.

By Theorem 1,

$$f'(z) = \lim_{N \to \infty} g'_N(z)$$

SO

$$\frac{f'(z)}{f(z)} = \lim_{N \to \infty} \frac{g'_N(z)}{g_N(z)}.$$

Here  $g'_N(z)/g_N(z)$  is given by the rule for differentiating a product.

This remark justifies to proof of (27) as well.

In the text the Gamma function is defined by means of the product formula (29) in §2.4 and the integral formula (42) derived by an interesting residue calculus due to Lindelöf. Here we go a shorter way and derive the product formula from the definition in terms of the integral formula.

The Gamma function can be defined by

$$\Gamma(z) = \int_0^\infty t^{z-1} e^{-t} dt \quad \text{Re} z > 0.$$

Writing

$$f_n(z) = \int_0^n t^{-z-1} e^{-t} dt$$

 $f_n$  is holomorphic and

$$|\Gamma(z) - f_n(z)| \le \left| \int_n^\infty e^{z-1} e^{-t} dt \right| \le \int_n^\infty e^{\operatorname{Re} z - 1} e^{-t} dt$$

which  $\to 0$  uniformly in each half plane  $\text{Re}z > \delta$  ( $\delta > 0$ ). Thus  $\Gamma(z)$  is holomorphic in Rez > 0. Here are some of its properties

(i)  $\Gamma(z+1) = z\Gamma(z)$ .

This follows by integration by parts.

(ii)  $\Gamma(z)$  extends to a meromorphic function on  $\mathbb C$  with simple poles at  $z=0,-1,-2,\ldots$  The function

$$H(z) = \frac{\Gamma(z+1)}{z}$$

is meromorphic in Rez > -1 with a pole at z = 0. Since

$$\lim_{z \to 0} zH(z) \neq 0$$

the pole is simple. The residue is  $\Gamma(1) = 1$ . Also  $H(z) = \Gamma(z)$  for Rez > 0. Thus  $\Gamma(z)$  is meromorphic in Rez > -1 with simple pole at z = 0. Statement (ii) follows by repetition.

(iii) For x > 0, y > 0

$$\int_0^1 t^{x-1} (1-t)^{y-1} dt = \frac{\Gamma(x)\Gamma(y)}{\Gamma(x+y)}$$

Proof:

$$\Gamma(x)\Gamma(y) = \int_0^\infty t^{x-1}e^{-t}dt \int_0^\infty s^{y-1}e^{-s}ds$$

Put s = tv. Since integrands are positive, integrals can be interchanged. We get

$$\Gamma(x)\Gamma(y) = \int_0^\infty t^{x-1}e^{-t}dt \int_0^\infty t^y v^{y-1}e^{-tv}dv$$

$$= \int_0^\infty v^{y-1}dv \int_0^\infty t^{x+y-1}e^{(v+1)t}dt \qquad t = \frac{u}{1+v}$$

$$= \int_0^\infty v^{y-1}dv \int_0^\infty u^{x+y-1}e^{-ut}dt (1+v)^{-x-y}du$$

$$= \Gamma(x+y) \int_0^\infty \frac{v^{y-1}}{(1+v)^{x+y}}dv = \Gamma(x+y) \int_0^\infty s^{x-1}(1-s)^{y-1}ds \qquad (1)$$

the last expression coming from  $v = s^{-1}(1 - s)$ . This proves (iii).

(iv)  $\Gamma(z)\Gamma(1-z) = \frac{\pi}{\sin \pi z}$ 

From (1) we obtain

$$\Gamma(x)\Gamma(1-x) = \int_0^\infty \frac{v^{-x}}{1+v} dv$$

which evaluates to  $\pi/\sin(\pi x)$  by the method of Exercise 3(g) p.161, done in Lecture 15. This proves (iv) by meromorphic continuation.

Since the poles of  $\Gamma(z)$  are canceled by zeros of  $\sin \pi z$ ,  $\Gamma(1-z)$  is never 0. By (iii) we have for 0 < h < x z = x + iy

$$\frac{\Gamma(z-h)\Gamma(h)}{\Gamma(z)} = \int_0^1 t^{z-h-1} (1-t)^{h-1} dt$$

$$= \int_0^1 (1-t)^{z-h-1} t^{h-1} dt$$

$$= \frac{1}{h} + \int_0^1 [(1-t)^{z-h-1} - 1] t^{h-1} dt.$$

Since  $(1-t)^{z-h-1}t^{h-1} \to (1-t)^{z-1}t^{-1}$  as  $h \to 0$  uniformly in t we obtain

$$\frac{\Gamma(z-h)\Gamma(h)}{\Gamma(z)} = \frac{1}{h} + \int_0^1 [(1-t)^{z-1} - 1]t^{-1} dt + o(1) \text{ as } h \to 0.$$

The left hand side is

$$\frac{1}{\Gamma(z)}(\Gamma(z) - h\Gamma'(z) + \cdots) \left\{ \frac{1}{h+A+\cdots} \right\}$$

where  $\{\ \}$  is the Laurent series for  $\Gamma(h)$  with center h=0. Equating the constant terms on left hand side and right hand side we get

$$\frac{\Gamma'(z)}{\Gamma(z)} = \int_0^1 (1 - (1 - t))^{z - 1} t^{-1} dt - A \qquad x > 0.$$

Writing  $t^{-1} = \sum_{0}^{\infty} (1-t)^n$  the expression is

$$\int_{0}^{1} \sum_{n} [(1-t)^{n} - (1-t)^{n+z-1}] dt - A$$

$$= \sum_{n} \int_{0}^{1} [(1-t)^{n} - (1-t)^{n+z-1}] dt - A$$

$$= \sum_{n}^{\infty} \left(\frac{1}{n+1} - \frac{1}{n+z}\right) - A = 1 - \frac{1}{z} + \sum_{1}^{\infty} \left(\frac{1}{n+1} - \frac{1}{n+z}\right) - A$$

$$= \sum_{n}^{\infty} \left(\frac{1}{n} - \frac{1}{n+1}\right) - \frac{1}{z} + \sum_{1}^{\infty} \left(\frac{1}{n+1} - \frac{1}{n+z}\right) - A$$

$$= -\frac{1}{z} + \sum_{1}^{\infty} \left(\frac{1}{n} - \frac{1}{n+z}\right) - A$$

SO

$$= \frac{\Gamma'(z)}{\Gamma(z)} + \frac{1}{z} = \sum_{1}^{\infty} \left(\frac{1}{n} - \frac{1}{n+z}\right) - A.$$

Having justified taking logarithmic derivative of an infinite product this gives

$$\frac{1}{\Gamma(z)} = ze^{Cz} \prod_{1}^{\infty} \left(1 + \frac{z}{n}\right) e^{-\frac{z}{n}} \qquad C = \text{const.}$$

Putting z = 1 we have

$$1 = e^C \prod_{1}^{\infty} \left( 1 + \frac{1}{n} \right) e^{-\frac{1}{h}}$$

SO

$$1 = e^{C} \lim_{N \to \infty} \left( (N+1)e^{-\left(1 + \frac{1}{2} + \cdots + \frac{1}{N}\right)} \right)$$

SO

$$0 = C + \lim_{N \to \infty} \left( \log(N+1) - 1 - \frac{1}{2} - \dots - \frac{1}{N} \right) = C - \gamma$$

so

 $C = \text{the Euler constant } \gamma$ .

---

MIT OpenCourseWare <a href="http://ocw.mit.edu">http://ocw.mit.edu</a>

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: <a href="http://ocw.mit.edu/terms">http://ocw.mit.edu/terms</a>.

## Lecture 19: Normal Families

(Replacing Text 219-227)

**Theorem 1** Let  $\Omega \subset \mathbb{C}$  be a region,  $\mathcal{F}$  a family of holomorphic functions on  $\Omega$  such that for each compact  $E \subset \Omega$ ,  $\mathcal{F}$  is uniformly bounded on E. Then  $\mathcal{F}$  has a subsequence converging uniformly on each compact subset of  $\Omega$ .

First we prove that on each compact subset  $E \subset \Omega$ , the family  $\mathcal{F}$  is equicontinuous. This means, given  $\epsilon > 0$  there exists a  $\delta > 0$  such that for all  $f \in \mathcal{F}$ ,

$$|f(z') - f(z'')| < \epsilon$$
 if  $|z' - z''| < \delta, \ z', z'' \in E$ . (1)

The distance function  $x \to d(x, \mathbb{C} - \Omega)$  is continuous and has a minimum > 0 on the compact set E. Let d > 0 be such that (D denoting disk)  $F = \bigcup_{x \in E} D(x, 2d)$  has closure  $\bar{F} \subset \Omega$ .

Let  $z', z'' \in E$  satisfy

$$|z' - z''| < d$$

and let  $\gamma$  denote the circle

$$\gamma : |z - z'| = 2d.$$

Then  $\gamma \subset \bar{F}$  and z' and z'' are both inside  $\gamma$ . Also  $|\zeta - z'| = 2d$ ,  $|\zeta - z''| \ge d$  for  $\zeta \in \gamma$ .

By Cauchy's formula for  $f \in \mathcal{F}$ ,

$$f(z') - f(z'') = \frac{z' - z''}{2\pi i} \int_{\gamma} \frac{f(\zeta)}{(\zeta - z')(\zeta - z'')} d\zeta,$$

so if  $M(\bar{F})$  is the maximum of f on  $\bar{F}$ 

$$|f(z') - f(z'')| \le |z' - z''| \frac{M(\bar{F})}{d}.$$

Hence (1) follows.

To conclude the proof of Theorem 1 choose any sequence  $(z_j)$  which is dense in  $\Omega$ . Let  $f_m$  be any sequence in  $\mathcal{F}$ . The sequence  $f_m(z_1)$  is bounded so  $f_m$  has

a subsequence  $f_{m,1}$  converging at  $z_1$ . Form this take a subsequence  $f_{m,2}$  which converges at  $z_2$ . Continuing we see that the subsequence  $f_{m,m}$  converges at each  $z_j$ .

By the first part of the proof,  $\mathcal{F}$  is equicontinuous on the compact set  $\bar{F}$ . Given  $\epsilon > 0$  there exists a  $\delta < d$  such that (1) holds for all  $z', z'' \in \bar{F}$ ,  $f \in \mathcal{F}$ . If  $z \in E$  the disk  $D(z, \delta)$  contains some  $z_j$  so  $D(z_j, \delta)$  contains z.

By the compactness of E,

$$E \subset \bigcup_{i=1}^{p} D(z_i, \delta)$$

for some  $z_1, \dots, z_p$ . Thus given  $z \in E$  there exists a  $z_i = z_i(z)$  such that  $|z - z_i(z)| < \delta$ . Then  $z_i(z) \in \bar{F}$ . Thus by (1) for  $\bar{F}$ ,

$$|f(z) - f(z_i(z))| < \epsilon.$$
  $f \in \mathcal{F}.$  (2)

There exists N > 0 such that

$$|f_{r,r}(z_i) - f_{s,s}(z_i)| < \epsilon \qquad 1 \le i \le p, \ r, s > N.$$
 (3)

Given  $z \in E$  we have with  $z_i = z_i(z)$ 

$$|f_{r,r}(z) - f_{s,s}(z)| \le |f_{r,r}(z) - f_{r,r}(z_i)| + |f_{r,r}(z_i) - f_{s,s}(z_i)| + |f_{s,s}(z_i) - f_{s,s}(z)|$$
  
  $\le 3\epsilon$  by (2) and (3).

The proves the stated uniform convergence on E.

<u>Remark:</u> In the text, p. 223, it is erroneously assumed (and used) that  $\zeta_k \in E$ . This error occurs in many other texts.

---

## Lecture 20: The Riemann Mapping Theorem

(Text 229-231)

**Remark**: The first step is to show that there exists an analytic and univalent function f, mapping  $\Omega$  into the unit disk D satisfying  $f(z_0) = 0$  and  $f'(z_0) > 0$ . In order to expand  $f(\Omega)$  we take  $f'(z_0)$  as large as possible. This indeed accomplishes  $f(\Omega) = D$ .

The proof concludes with the contradiction

$$|G'(z_0)| > B = |f'(z_0)|.$$

After the proof it is indicated in the text that this contradiction  $|f'(z_0)| < |G'(z_0)|$  is a consequence of Schwarz's lemma by writing

$$f(z) = H(W), \ W = G(z).$$

However, H is then only defined on  $G(\Omega)$ , so until we know that  $G(\Omega) = D$  Schwarz's lemma (p.135) does not apply.

Thus the phrase "a consequence of Schwarz's lemma" should properly read "consistent with Schwarz's lemma", which probably was the author's intention.

Koebe's proof from 1915 is outlined in Pólya and Szegö, Vol. II, §2. This is based on considering the distance of the origin to the boundary of the image region  $f(\Omega)$ . The square root map is then used to increase this distance. By iteration this leads to an explicit sequence converging to the desired limit map.

---

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 21 and 22: The Prime Number Theorem

(New lecture, not in Text)

The location of prime numbers is a central question in number theory. Around 1808, Legendre offered experimental evidence that the number  $\pi(x)$  of primes < x behaves like  $x/\log x$  for large x. Tchebychev proved (1848) the partial result that the ratio of  $\pi(x)$  to  $x/\log x$  for large x lies between 7/8 and 9/8. In 1896 Hadamard and de la Valle Poussin independently proved the Prime Number Theorem that the limit of this ratio is exactly 1. Many distinguished mathematicians (particularly Norbert Wiener) have contributed to a simplification of the proof and now (by an important device by D.J. Newman and an exposition by D. Zagier) a very short and easy proof is available.

These lectures follows Zagier's account of Newman's short proof on the prime number theorem. cf:

- (1) D.J.Newman, Simple Analytic Proof of the Prime Number Theorem, Amer. Math. Monthly 87 (1980), 693-697.
- (2) D.Zagier, Newman's short proof of the Prime Number Theorem. Amer. Math. Monthly 104 (1997), 705-708.

The prime number theorem states that the number  $\pi(x)$  of primes which are less than x is asymptotically like  $\frac{x}{\log x}$ :

$$\frac{\pi(x)}{x/\log x} \longrightarrow 1$$
 as  $x \to \infty$ .

Through Euler's product formula (I) below (text p.213) and especially through Riemann's work,  $\pi(x)$  is intimately connected to the Riemann zeta function

$$\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s},$$

which by the convergence of the series in Res > 1 is holomorphic there.

The prime number theorem is approached by use of the functions

$$\Phi(s) = \sum_{p \ prime} \frac{\log p}{p^s}, \qquad \mathcal{V}(x) = \sum_{p \le x \ prime} \log p.$$

Simple properties of  $\Phi$  will be used to show  $\zeta(s) \neq 0$  and  $\Phi(s) - \frac{1}{s-1}$  holomorphic for Res  $\geq 1$ . Deeper properties result from writing  $\Phi(s)$  as an integral on which Cauchy's theorem for contour integration can be used. This will result in the relation  $\mathcal{V}(x) \sim x$  from which the prime number theorem follows easily.

I 
$$\frac{1}{\zeta(s)} = \prod_{1}^{\infty} (1 - p_n^{-s}) \quad \text{for Re} s > 1.$$

Proof: For each  $n(1-p_n^{-s})^{-1} = \sum_{m=0}^{\infty} p_n^{-ms}$ . Putting this into the finite product

$$\prod_{1}^{N} (1 - p_1^{-s})^{-1} \text{ we obtain } \prod_{1}^{N} (1 - p_n^{-s})^{-1} = \sum_{k=1}^{\infty} n_k^{-s}. \text{ Now let } N \to \infty.$$

II  $\zeta(s) - \frac{1}{s-1}$  extends to a holomorphic function in Res > 0.

Proof: In fact for Res > 1,

$$\zeta(s) - \frac{1}{s-1} = \sum_{n=1}^{\infty} \frac{1}{n^s} - \int_1^{\infty} \frac{dx}{x^s}$$
$$= \sum_{n=1}^{\infty} \int_n^{n+1} \left(\frac{1}{n^s} - \frac{1}{x^s}\right) dx$$

But

$$\left| \frac{1}{n^s} - \frac{1}{x^s} \right| = \left| \int_{n}^{x} s \frac{dy}{y^{s+1}} \right| \le \max_{n \le y \le x} \left| \frac{s}{y^{s+1}} \right| \le \frac{s}{n^{\text{Res}+1}},$$

so the sum above converges uniformly in each half-plane  $\operatorname{Re}s \geq \delta\left(\delta>0\right)$ .

III  $\mathcal{V}(x) = O(x)$  (Sharper form proved later).

Proof: Since the p in the interval n divides <math>(2n)! but not n! we have

$$2^{2n} = (1+1)^{2n} = \sum_{k=0}^{2n} {2n \choose k} \ge {2n \choose n} \ge \prod_{n$$

Thus

$$\mathcal{V}(2n) - \mathcal{V}(n) \le 2n \log 2. \tag{1}$$

If x is arbitrary, select n with  $n < \frac{x}{2} \le n + 1$ , then

$$\mathcal{V}(x) \leq \mathcal{V}(2n+2) \leq \mathcal{V}(n+1) + (2n+2)\log 2 \qquad \text{(by (1))}$$

$$= \mathcal{V}\left(\frac{x}{2}+1\right) + (x+2)\log 2$$

$$= \mathcal{V}\left(\frac{x}{2}\right) + \log\left(\frac{x}{2}+1\right) + (x+2)\log 2.$$

Thus if  $C > \log 2$ ,

$$\mathcal{V}(x) - \mathcal{V}\left(\frac{x}{2}\right) \le Cx \quad \text{for} \quad x \ge x_0 = x_0(C).$$
 (2)

Consider the points

Use (2) for the points right of  $x_0$ ,

$$\mathcal{V}\left(\frac{x}{2}\right) - \mathcal{V}\left(\frac{x}{2^{2}}\right) \leq C\frac{x}{2},$$

$$\vdots$$

$$\mathcal{V}\left(\frac{x}{2^{r}}\right) - \mathcal{V}\left(\frac{x}{2^{r+1}}\right) \leq C\frac{x}{2^{r}}$$

Summing, we get

$$\mathcal{V}(x) - \mathcal{V}(x_0) \leq \mathcal{V}(x) - \mathcal{V}\left(\frac{x}{2^{r+1}}\right)$$
  
  $\leq Cx + \dots + C\frac{x}{2^r},$ 

SO

$$\mathcal{V}(x) \le 2C(x) + O(1).$$

IV  $\zeta(s) \neq 0$  and  $\Phi(s) - \frac{1}{s-1}$  is holomorphic for  $\text{Re}s \geq 1$ .

Proof: If Res > 1, part I shows that  $\zeta(s) \neq 0$  and

$$-\frac{\zeta'(s)}{\zeta(s)} = \sum_{p} \frac{\log p}{p^s - 1} = \Phi(s) + \sum_{p} \frac{\log p}{p^s(p^s - 1)}.$$
 (3)

The last sum converges for Res  $> \frac{1}{2}$ , so by II,  $\Phi(s)$  extends meromorphically to Res  $> \frac{1}{2}$  with poles only at s = 1 and at the zeros of  $\zeta(s)$ . Note that

$$\zeta(s) = 0 \implies \zeta(\bar{s}) = 0.$$

Let  $\alpha \in \mathbb{R}$ . If  $s_0 = 1 + i\alpha$  is a zero of  $\zeta(s)$  of order  $\mu \geq 0$ , then

$$-\frac{\zeta'(s)}{\zeta(s)} = -\frac{\mu}{s - s_0} + \text{function holomorphic near } s_0.$$

So

$$\lim_{\epsilon \to 0} \epsilon \Phi(1 + \epsilon + i\alpha) = -\mu.$$

We exploit the positivity of each term in

$$\Phi(1+\epsilon) = \sum_{p} \frac{\log p}{p^{1+\epsilon}}$$

for  $\epsilon > 0$ . It implies

$$\sum_{p} \frac{\log p}{p^{1+\epsilon}} \left( p^{+\frac{i\alpha}{2}} + p^{-\frac{i\alpha}{2}} \right)^2 \ge 0,$$

SO

$$\Phi(1 + \epsilon + i\alpha) + \Phi(1 + \epsilon - i\alpha) + 2\Phi(1 + \epsilon) \ge 0. \tag{4}$$

By II, s = 1 is a simple pole of  $\zeta(s)$  with residue +1, so

$$\lim_{\epsilon \searrow 0} \epsilon \Phi(1 + \epsilon) = 1.$$

Thus (4) implies

$$-2\mu + 2 \ge 0,$$

SO

$$\mu \leq 1$$
.

This is not good enough, so we try

$$\sum_{p} \frac{\log p}{p^{1+\epsilon}} \left( p^{+\frac{i\alpha}{2}} + p^{-\frac{i\alpha}{2}} \right)^4 \ge 0.$$

Putting

$$\lim_{\epsilon \searrow 0} \epsilon \Phi(1 + \epsilon \pm 2i\alpha) = -\nu,$$

where  $\nu \geq 0$  is the order of  $1 \pm 2i\alpha$  as a zero of  $\zeta(s)$ , the same computation gives

$$6 - 8\mu - 2\nu \ge 0$$
,

which implies  $\mu = 0$  since  $\mu, \nu \ge 0$ . Now II and (3) imply  $\Phi(s) - \frac{1}{s-1}$  holomorphic for Res  $\ge 1$ .

V 
$$\int_{1}^{\infty} \frac{\mathcal{V}(x) - x}{x^2} dx$$
 is convergent.

Proof: The function  $\mathcal{V}(x)$  is increasing with jumps  $\log p$  at the points x=p. Thus

$$\Phi(s) = \sum_{p} \frac{\log p}{p^{s}}$$
$$= s \int_{1}^{\infty} \frac{\mathcal{V}(x)}{x^{s+1}} dx$$

In fact, writing  $\int_1^\infty$  as  $\sum_i \int_{p_i}^{p_{i+1}}$  this integral becomes  $\sum_{i=1}^\infty \mathcal{V}(p_i) \left(\frac{1}{p_i^s} - \frac{1}{p_{i+1}^s}\right) s^{-1}$  which by  $\mathcal{V}(p_{i+1}) - \mathcal{V}(p_i) = \log p_{i+1}$  reduces to  $\Phi(s)$ . Using the substitution  $x = e^t$  we obtain

$$\Phi(s) = s \int_0^\infty e^{-st} \mathcal{V}(e^t) dt$$
 Res > 1.

Consider now the functions

$$f(t) = \mathcal{V}(e^t)e^{-t} - 1,$$
  
 $g(z) = \frac{\Phi(z+1)}{z+1} - \frac{1}{z}.$ 

f(t) is bounded by III and we have

$$\int_{1}^{e^{T}} \frac{\mathcal{V}(x) - x}{x^{2}} dx = \int_{0}^{T} f(t) dt.$$
 (5)

Also, by IV,

$$\Phi(z+1) = \frac{1}{z} + h(z),$$

where h is holomorphic in  $\text{Re}z \geq 0$ , so

$$g(z) = \frac{\Phi(z+1)}{z+1} - \frac{1}{z} = \frac{h(z)-1}{z+1}$$

is holomorphic in  $\text{Re}z \geq 0$ .

For Rez > 0 we have

$$g(z) = \int_0^\infty e^{-zt} (f(t) + 1) - \int_0^\infty e^{-zt} dt$$
$$= \int_0^\infty e^{-zt} f(t) dt.$$

Now we need the following theorem:

**Theorem 1 (Analytic Theorem)** Let f(t)  $(t \ge 0)$  be bounded and locally integrable and assume the function

$$g(z) = \int_0^\infty e^{-zt} f(t) dt \qquad Re(z) > 0$$

extends to a holomorphic function on  $Re(z) \geq 0$ , then

$$\lim_{T \to \infty} \int_0^T f(t) \ dt$$

exists and equals g(0).

This will imply Part V by (5). Proof of Analytic Theorem will be given later.

VI 
$$\mathcal{V}(x) \sim x$$
.

Proof: Assume that for some  $\lambda > 1$  we have  $\mathcal{V}(x) \geq \lambda x$  for arbitrary large x. Since  $\mathcal{V}(x)$  is increasing we have for such x

$$\int_{r}^{\lambda x} \frac{\mathcal{V}(t) - t}{t^2} dt \ge \int_{r}^{\lambda x} \frac{\lambda x - t}{t^2} dt = \int_{1}^{\lambda} \frac{\lambda - s}{s^2} ds = \delta(\lambda) > 0.$$

On the other hand, V implies that to each  $\epsilon > 0$ ,  $\exists K$  such that

$$\left| \int_{K_1}^{K_2} \frac{\mathcal{V}(x) - x}{x^2} dx \right| < \epsilon \quad \text{for } K_1, K_2 > K.$$

Thus the  $\lambda$  cannot exist.

Similarly if for some  $\lambda < 1, \mathcal{V}(x) \leq \lambda x$  for arbitrary large x, then for  $t \leq x$ ,

$$\mathcal{V}(t) \leq \mathcal{V}(x) \leq \lambda x$$

SO

$$\int_{\lambda_T}^x \frac{\mathcal{V}(t) - t}{t^2} \le \int_{\lambda_T}^x \frac{\lambda x - t}{t^2} = \int_{\lambda}^1 \frac{\lambda - s}{s^2} ds = \delta(\lambda) < 0.$$

Again this is impossible for the same reason. Thus both

$$\beta = \limsup_{x \to \infty} \frac{\mathcal{V}(x)}{x} > 1$$

and

$$\alpha = \liminf_{x \to \infty} \frac{\mathcal{V}(x)}{x} < 1$$

are impossible. Thus they must agree, i.e.  $V(x) \sim x$ .

## **Proof of Prime Number Theorem:**

We have

$$\mathcal{V}(x) = \sum_{p \le x} \log p \le \sum_{p \le x} \log x = \pi(x) \log x,$$

SO

$$\liminf_{x \to \infty} \frac{\pi(x) \log x}{x} \ge \liminf_{x \to \infty} \frac{\mathcal{V}(x)}{x} = 1.$$

Secondly if  $0 < \epsilon < 1$ ,

$$\mathcal{V}(x) \geq \sum_{x^{1-\epsilon} \leq p \leq x} \log p$$

$$\geq (1-\epsilon) \sum_{x^{1-\epsilon} \leq p \leq x} \log x$$

$$= (1-\epsilon) \log x \left(\pi(x) + O(x^{1-\epsilon})\right)$$

thus

$$\limsup_{x \to \infty} \frac{\pi(x) \log x}{x} \le \frac{1}{1 - \epsilon} \limsup_{x \to \infty} \frac{\mathcal{V}(x)}{x}$$

for each  $\epsilon$ . Thus

$$\lim_{x \to \infty} \frac{\pi(x) \log x}{x} = 1.$$

Q.E.D.

## Proof of Analytic Theorem: (Newman).

Put

$$g_T(z) = \int_0^T e^{-zt} f(t) dt,$$

which is holomorphic in  $\mathbb{C}$ . We only need to show

$$\lim_{T\to\infty}g_T(0)=g(0).$$

Fix R and then take  $\delta > 0$  small enough so that g(z) is holomorphic on C and its interior.

By Cauchy's formula

$$g(0) - g_T(0) = \frac{1}{2\pi i} \int_C (g(z) - g_T(z)) e^{zT} \left(1 + \frac{z^2}{R^2}\right) \frac{dz}{z}. (6)$$

On semicircle

$$C_+: C \cap (\text{Re}z > 0)$$

integrand is bounded by  $\frac{2B}{R^2}$ , where

$$B = \sup_{t > 0} |f(t)|.$$

In fact for Rez > 0,

$$|g(z) - g_T(z)| = \left| \int_T^\infty f(t)e^{-zt} dt \right|$$

$$\leq B \int_T^\infty |e^{-zt}| dt$$

$$= \frac{Be^{-\operatorname{Re}zT}}{\operatorname{Re}z}$$

and

$$\left| e^{zT} \left( 1 + \frac{z^2}{R^2} \right) \frac{1}{z} \right| = e^{\operatorname{Re}zT} \cdot \frac{2\operatorname{Re}z}{R^2} \qquad (z = Re^{i\theta}).$$

So the contribution to the integral (6) over  $C_+$  is bounded by  $\frac{B}{R}$ , namely

$$\frac{Be^{-\mathrm{Re}zT}}{\mathrm{Re}z} \cdot e^{\mathrm{Re}zT} \cdot \frac{2\mathrm{Re}z}{R^2} \cdot \pi R \frac{1}{2\pi} = \frac{B}{R}.$$

Next consider the integral over

Look at g(z) and  $g_T(z)$  separately. For  $g_T(z)$  which is entire, this contour can be replaced by

Again the integral is bounded by  $\frac{B}{R}$  because

$$|g_{T}(z)| = \left| \int_{0}^{T} f(t)e^{-zt}dt \right|$$

$$\leq B \int_{0}^{T} |e^{-zt}| dt$$

$$\leq B \int_{-\infty}^{T} |e^{-zt}| dt$$

$$= \frac{Be^{-\operatorname{Re}zT}}{|\operatorname{Re}z|}$$

and

$$\left| \left( 1 + \frac{z^2}{R^2} \right) \frac{1}{z} \right|$$

on  $C'_{\underline{\ }}$  has the same estimate as before.

There remains

$$\int_{C_{\underline{}}} e^{zT} \underbrace{g(z) \left(1 + \frac{z^2}{R^2}\right) \frac{1}{z}}_{\text{indep. of } T} dz.$$

On the contour,  $|e^{zT}| \leq 1$  and

$$\lim_{T \to \infty} |e^{zT}| \to 0 \quad \text{for } \text{Re}z < 0.$$

By dominated convergence, the integral  $\to$  0 as  $T\to +\infty$ ,  $\delta$  is fixed. It follows that

$$\limsup_{T \to \infty} |g(0) - g_T(0)| \le \frac{2B}{R}.$$

Since R is arbitrary, this proves the theorem.

Q.E.D.

**Remarks:** Riemann proved an explicit formula relating the zeros  $\rho$  of  $\zeta(s)$  in 0 < Re s < 1 to the prime numbers. The improved version by von Mangoldt reads

$$\mathcal{V}(x) = \sum_{p \le x} \log p$$
$$= x - \sum_{\{\rho\}} \frac{x^{\rho}}{\rho} + \sum_{n \ge 1} \frac{x^{-2n}}{2n} - \log 2\pi.$$

He conjectured that  $\operatorname{Re}\rho = \frac{1}{2}$  for all  $\rho$ . This is the famous **Riemann Hypothesis**.

---

## 18.112 Functions of a Complex Variable Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 23: The Extension of $\zeta(s)$ to the whole plane and the Functional Equation

(Text 214-217)

See Riemann's Collected Works p. 146.

In Theorem 10 we consider the function  $z \to (-z)^{s-1}$  with z outside the positive real axis  $R^+$ . Angles are measured from the positive real axis from  $-\pi$  to  $+\pi$ . Consider contour C.

If z is on the upper part of the cut  $R^+$ , -z is below the negative real axis so

$$arg(-z) = -\pi$$
 so  $(-z)^{s-1} = x^{s-1}e^{-(s-1)\pi i}$ .

If z is on the lower par of the cut  $R^+$  then -z is above the negative real axis so  $\arg(-z)=+\pi$  so  $(-z)^{s-1}=x^{s-1}e^{(s-1)i\pi}$ .
