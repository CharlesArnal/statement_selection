# Chapter 1: Nonparametric Estimators

*From: A. B. Tsybakov, Introduction to Nonparametric Estimation*

---

<!-- Page 11 -->

Nonparametric estimators
1.1 Examples of nonparametric models and problems
1. Estimation of a probability density
Let X1, . . . , Xn be identically distributed real valued random variables whose
common distribution is absolutely continuous with respect to the Lebesgue
measure on R. The density of this distribution, denoted by p, is a function
from R to [0, +∞) supposed to be unknown. The problem is to estimate p.
An estimator of p is a function x →pn(x) = pn(x, X1, . . . , Xn) measurable
with respect to the observation X = (X1, . . . , Xn). If we know a priori that
p belongs to a parametric family {g(x, θ) : θ ∈Θ}, where g(·, ·) is a given
function, and Θ is a subset of Rk with a ﬁxed dimension k independent of
n, then estimation of p is equivalent to estimation of the ﬁnite-dimensional
parameter θ. This is a parametric problem of estimation. On the contrary, if
such a prior information about p is not available we deal with a nonparametric
problem. In nonparametric estimation it is usually assumed that p belongs to
some “massive” class P of densities. For example, P can be the set of all the
continuous probability densities on R or the set of all the Lipschitz continuous
probability densities on R. Classes of such type will be called nonparametric
classes of functions.
2. Nonparametric regression
Assume that we have n independent pairs of random variables (X1, Y1), . . . ,
(Xn, Yn) such that
Yi = f(Xi) + ξi,
Xi ∈[0, 1],
(1.1)
where the random variables ξi satisfy E(ξi) = 0 for all i and where the func-
tion f from [0, 1] to R (called the regression function) is unknown. The
problem of nonparametric regression is to estimate f given a priori that
this function belongs to a nonparametric class of functions F. For exam-
ple, F can be the set of all the continuous functions on [0, 1] or the set of
A. B. Tsybakov, Introduction to Nonparametric Estimation,


<!-- Page 12 -->

1 Nonparametric estimators
all the convex functions, etc. An estimator of f is a function x →fn(x) =
fn(x, X) deﬁned on [0, 1] and measurable with respect to the observation
X = (X1, . . . , Xn, Y1, . . . , Yn). In what follows, we will mainly focus on the
particular case Xi = i/n.
3. Gaussian white noise model
This is an idealized model that provides an approximation to the nonpara-
metric regression (1.1). Consider the following stochastic diﬀerential equation:
dY (t) = f(t)dt +
√n dW(t),
t ∈[0, 1],
where W is a standard Wiener process on [0, 1], the function f is an unknown
function on [0, 1], and n is an integer. We assume that a sample path X =
{Y (t), 0 ≤t ≤1} of the process Y is observed. The statistical problem is to
estimate the unknown function f. In the nonparametric case it is only known
a priori that f ∈F where F is a given nonparametric class of functions.
An estimator of f is a function x →fn(x) = fn(x, X) deﬁned on [0, 1] and
measurable with respect to the observation X.
In either of the three above cases, we are interested in the asymptotic
behavior of estimators as n →∞.
1.2 Kernel density estimators
We start with the ﬁrst of the three problems described in Section 1.1. Let
X1, . . . , Xn be independent identically distributed (i.i.d.) random variables
that have a probability density p with respect to the Lebesgue measure on R.
The corresponding distribution function is F(x) =
 x
−∞p(t)dt. Consider the
empirical distribution function
Fn(x) = 1
n
n

i=1
I(Xi ≤x),
where I(·) denotes the indicator function. By the strong law of large numbers,
we have
Fn(x) →F(x),
∀x ∈R,
almost surely as n →∞. Therefore, Fn(x) is a consistent estimator of F(x)
for every x ∈R. How can we estimate the density p? One of the ﬁrst intuitive
solutions is based on the following argument. For suﬃciently small h > 0 we
can write an approximation
p(x) ≈F(x + h) −F(x −h)
2h
.


<!-- Page 13 -->

1.2 Kernel density estimators
Replacing F by the estimate Fn we deﬁne
ˆpR
n (x) = Fn(x + h) −Fn(x −h)
2h
.
The function ˆpR
n is an estimator of p called the Rosenblatt estimator. We can
rewrite it in the form:
ˆpR
n (x) =
2nh
n

i=1
I(x −h < Xi ≤x + h) = 1
nh
n

i=1
K0
Xi −x
h

,
where K0(u) = 1
2 I(−1 < u ≤1). A simple generalization of the Rosenblatt
estimator is given by
ˆpn(x) = 1
nh
n

i=1
K
Xi −x
h

,
(1.2)
where K : R →R is an integrable function satisfying

K(u)du = 1. Such a
function K is called a kernel and the parameter h is called a bandwidth of the
estimator (1.2). The function x →ˆpn(x) is called the kernel density estimator
or the Parzen–Rosenblatt estimator.
In the asymptotic framework, as n →∞, we will consider a bandwidth h
that depends on n, denoting it by hn, and we will suppose that the sequence
(hn)n≥1 tends to 0 as n →∞. The notation h without index n will also be
used for brevity whenever this causes no ambiguity.
Some classical examples of kernels are the following:
K(u) = 1
2 I(|u| ≤1) (the rectangular kernel),
K(u) = (1 −|u|)I(|u| ≤1) (the triangular kernel),
K(u) = 3
4 (1 −u2)I(|u| ≤1) (the parabolic kernel,
or the Epanechnikov kernel),
K(u) = 15
16 (1 −u2)2I(|u| ≤1) (the biweight kernel),
K(u) =
√
2π exp(−u2/2) (the Gaussian kernel),
K(u) = 1
2 exp(−|u|/
√
2) sin(|u|/
√
2 + π/4) (the Silverman kernel).
Note that if the kernel K takes only nonnegative values and if X1, . . . , Xn are
ﬁxed, then the function x →ˆpn(x) is a probability density.
The Parzen–Rosenblatt estimator can be generalized to the multidimen-
sional case. For example, we can deﬁne a kernel density estimator in two di-
mensions as follows. Suppose that we observe n pairs of random variables
(X1, Y1), . . . , (Xn, Yn) such that (Xi, Yi) are i.i.d. with a density p(x, y) in R2.
A kernel estimator of p(x, y) is then given by the formula


<!-- Page 14 -->

1 Nonparametric estimators
ˆpn(x, y) =
nh2
n

i=1
K
Xi −x
h

K
Yi −y
h

(1.3)
where K : R →R is a kernel deﬁned as above and h > 0 is a bandwidth.
1.2.1 Mean squared error of kernel estimators
A basic measure of the accuracy of estimator ˆpn is its mean squared risk (or
mean squared error) at an arbitrary ﬁxed point x0 ∈R:
MSE = MSE(x0)
△= Ep

(ˆpn(x0) −p(x0))2
.
Here, MSE stands for “mean squared error” and Ep denotes the expectation
with respect to the distribution of (X1, . . . , Xn):
Ep

(ˆpn(x0) −p(x0))2 △=

. . .

(ˆpn(x0, x1, . . . , xn) −p(x0))2
n
	
i=1
[p(xi)dxi] .
We have
MSE = b2(x0) + σ2(x0)
(1.4)
where
b(x0) = Ep[ˆpn(x0)] −p(x0)
and
σ2(x0) = Ep

ˆpn(x0) −Ep[ˆpn(x0)]
2
.
Deﬁnition 1.1 The quantities b(x0) and σ2(x0) are called the bias and the
variance of the estimator ˆpn at a point x0, respectively.
To evaluate the mean squared risk of ˆpn we will analyze separately its variance
and bias.
Variance of the estimator ˆpn
Proposition 1.1 Suppose that the density p satisﬁes p(x) ≤pmax < ∞for
all x ∈R. Let K : R →R be a function such that

K2(u)du < ∞.
(1.5)
Then for any x0 ∈R, h > 0, and n ≥1 we have
σ2(x0) ≤C1
nh
where C1 = pmax

K2(u)du.


<!-- Page 15 -->

1.2 Kernel density estimators
Proof. Put
ηi(x0) = K
Xi −x0
h

−Ep

K
Xi −x0
h

.
The random variables ηi(x0), i = 1, . . . , n, are i.i.d. with zero mean and vari-
ance
Ep

η2
i (x0)

≤Ep

K2
Xi −x0
h

=

K2
z −x0
h

p(z)dz ≤pmaxh

K2(u)du.
Then
σ2(x0) = Ep
⎡
⎣

nh
n

i=1
ηi(x0)
2⎤
⎦=
nh2 Ep

η2
1(x0)

≤C1
nh .
(1.6)
We conclude that if the bandwidth h = hn is such that nh →∞as n →∞,
then the variance σ2(x0) goes to 0 as n →∞.
Bias of the estimator ˆpn
The bias of the kernel density estimator has the form
b(x0) = Ep[ˆpn(x0)] −p(x0) = 1
h

K
z −x0
h

p(z)dz −p(x0).
We now analyze the behavior of b(x0) as a function of h under some regularity
conditions on the density p and on the kernel K.
In what follows ⌊β⌋will denote the greatest integer strictly less than the
real number β.
Deﬁnition 1.2 Let T be an interval in R and let β and L be two positive
numbers. The H¨older class Σ(β, L) on T is deﬁned as the set of ℓ= ⌊β⌋
times diﬀerentiable functions f : T →R whose derivative f (ℓ) satisﬁes
|f (ℓ)(x) −f (ℓ)(x′)| ≤L|x −x′|β−ℓ,
∀x, x′ ∈T.
Deﬁnition 1.3 Let ℓ≥1 be an integer. We say that K : R →R is a kernel
of order ℓif the functions u →ujK(u), j = 0, 1, . . . , ℓ, are integrable and
satisfy

K(u)du = 1,

ujK(u)du = 0,
j = 1, . . . , ℓ.


<!-- Page 16 -->

1 Nonparametric estimators
Some examples of kernels of order ℓwill be given in Section 1.2.2. It is
important to note that another deﬁnition of an order ℓkernel is often used
in the literature: a kernel K is said to be of order ℓ+ 1 (with integer ℓ≥1)
if Deﬁnition 1.3 holds and

uℓ+1K(u)du ̸= 0. Deﬁnition 1.3 is less restric-
tive and seems to be more natural, since there is no need to assume that

uℓ+1K(u)du ̸= 0 for noninteger β. For example, Proposition 1.2 given be-
low still holds if

uℓ+1K(u)du = 0 and even if this integral does not exist.
Suppose now that p belongs to the class of densities P = P(β, L) deﬁned
as follows:
P(β, L) =

p
 p ≥0,

p(x)dx = 1, and p ∈Σ(β, L) on R

and assume that K is a kernel of order ℓ. Then the following result holds.
Proposition 1.2 Assume that p ∈P(β, L) and let K be a kernel of order ℓ=
⌊β⌋satisfying

|u|β|K(u)|du < ∞.
Then for all x0 ∈R, h > 0 and n ≥1 we have
|b(x0)| ≤C2hβ
where
C2 = L
ℓ!

|u|β|K(u)|du.
Proof. We have
b(x0) = 1
h

K
z −x0
h

p(z)dz −p(x0)
=

K(u)

p(x0 + uh) −p(x0)

du.
Next,
p(x0 + uh) = p(x0) + p′(x0)uh + · · · + (uh)ℓ
ℓ!
p(ℓ)(x0 + τuh),
(1.7)
where 0 ≤τ ≤1. Since K has order ℓ= ⌊β⌋, we obtain
b(x0) =

K(u)(uh)ℓ
ℓ!
p(ℓ)(x0 + τuh)du
=

K(u)(uh)ℓ
ℓ!
(p(ℓ)(x0 + τuh) −p(ℓ)(x0))du
and


<!-- Page 17 -->

1.2 Kernel density estimators
|b(x0)| ≤

|K(u)||uh|ℓ
ℓ!
p(ℓ)(x0 + τuh) −p(ℓ)(x0)
du
≤L

|K(u)||uh|ℓ
ℓ!
|τuh|β−ℓdu ≤C2hβ.
Upper bound on the mean squared risk
From Propositions 1.1 and 1.2, we see that the upper bounds on the bias and
variance behave in opposite ways as the bandwidth h varies. The variance de-
creases as h grows, whereas the bound on the bias increases (cf. Figure 1.1).
The choice of a small h corresponding to a large variance is called an un-
Bias/Variance tradeoff
h∗
n
Bias squared
Variance
Figure 1.1. Squared bias, variance, and mean squared error (solid line)
as functions of h.
dersmoothing. Alternatively, with a large h the bias cannot be reasonably
controlled, which leads to oversmoothing. An optimal value of h that balances
bias and variance is located between these two extremes. Figure 1.2 shows
typical plots of the corresponding density estimators. To get an insight into
the optimal choice of h, we can minimize in h the upper bound on the MSE
obtained from the above results.
If p and K satisfy the assumptions of Propositions 1.1 and 1.2, we obtain
MSE ≤C2
2h2β + C1
nh .
(1.8)


<!-- Page 18 -->

1 Nonparametric estimators
Undersmoothing
Oversmoothing
Correct smoothing
Figure 1.2. Undersmoothing, oversmoothing, and correct smoothing.
The circles indicate the sample points Xi.
The minimum with respect to h of the right hand side of (1.8) is attained
at
h∗
n =
 C1
2βC2

2β+1
n−
2β+1 .
Therefore, the choice h = h∗
n gives
MSE(x0) = O

n−
2β
2β+1

,
n →∞,
uniformly in x0. We have the following result.


<!-- Page 19 -->

1.2 Kernel density estimators
Theorem 1.1 Assume that condition (1.5) holds and the assumptions of Pro-
position 1.2 are satisﬁed. Fix α > 0 and take h = αn−
2β+1 . Then for n ≥1
the kernel estimator ˆpn satisﬁes
sup
x0∈R
sup
p∈P(β,L)
Ep[(ˆpn(x0) −p(x0))2] ≤Cn−
2β
2β+1 ,
where C > 0 is a constant depending only on β, L, α and on the kernel K.
Proof. We apply (1.8) as shown above. To justify the application of Proposi-
tion 1.1, it remains to prove that there exists a constant pmax < ∞satisfying
sup
x∈R
sup
p∈P(β,L)
p(x) ≤pmax.
(1.9)
To show (1.9), consider K∗which is a bounded kernel of order ℓ, not neces-
sarily equal to K. Applying Proposition 1.2 with h = 1 we get that, for any
x0 ∈R and any p ∈P(β, L),


K∗(z −x0)p(z)dz −p(x0)
 ≤C∗
△= L
ℓ!

|u|β|K∗(u)|du.
Therefore, for any x ∈R and any p ∈P(β, L),
p(x) ≤C∗
2 +

|K∗(z −x)|p(z)dz ≤C∗
2 + K∗
max,
where K∗
max = supu∈R |K∗(u)|. Thus, we get (1.9) with pmax = C∗
2 + K∗
max.
Under the assumptions of Theorem 1.1, the rate of convergence of the es-
timator ˆpn(x0) is ψn = n−
β
2β+1 , which means that for a ﬁnite constant C and
for all n ≥1 we have
sup
p∈P(β,L)
Ep

(ˆpn(x0) −p(x0))2
≤Cψ2
n.
Now the following two questions arise. Can we improve the rate ψn by using
other density estimators? What is the best possible rate of convergence? To
answer these questions it is useful to consider the minimax risk R∗
n associated
to the class P(β, L):
R∗
n(P(β, L))
△= inf
Tn
sup
p∈P(β,L)
Ep

(Tn(x0) −p(x0))2
,
where the inﬁmum is over all estimators. One can prove a lower bound on
the minimax risk of the form R∗
n(P(β, L)) ≥C′ψ2
n = C′n−
2β
2β+1 with some
constant C′ > 0 (cf. Chapter 2, Exercise 2.8). This implies that under the
assumptions of Theorem 1.1 the kernel estimator attains the optimal rate
of convergence n−
β
2β+1 associated with the class of densities P(β, L). Exact
deﬁnitions and discussions of the notion of optimal rate of convergence will
be given in Chapter 2.


<!-- Page 20 -->

1 Nonparametric estimators
Positivity constraint
It follows easily from Deﬁnition 1.3 that kernels of order ℓ≥2 must take
negative values on a set of positive Lebesgue measure. The estimators ˆpn
based on such kernels can also take negative values. This property is sometimes
emphasized as a drawback of estimators with higher order kernels, since the
density p itself is nonnegative. However, this remark is of minor importance
because we can always use the positive part estimator
ˆp+
n (x)
△= max{0, ˆpn(x)}
whose risk is smaller than or equal to the risk of ˆpn:
Ep

(ˆp+
n (x0) −p(x0))2
≤Ep

(ˆpn(x0) −p(x0))2
,
∀x0 ∈R.
(1.10)
In particular, Theorem 1.1 remains valid if we replace there ˆpn by ˆp+
n . Thus,
the estimator ˆp+
n is nonnegative and attains fast convergence rates associated
with higher order kernels.

---
*[End of extracted section containing Propositions 1.1 and 1.2]*
