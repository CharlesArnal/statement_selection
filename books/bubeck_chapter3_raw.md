# Chapter 3: Dimension-free Convex Optimization

*From: S. Bubeck, Convex Optimization: Algorithms and Complexity*

---

<!-- Page 35 -->

3
Dimension-free convex optimization
We investigate here variants of the gradient descent scheme. This it-
erative algorithm, which can be traced back to Cauchy [1847], is the
simplest strategy to minimize a diﬀerentiable function f on Rn. Start-
ing at some initial point x1 ∈Rn it iterates the following equation:
xt+1 = xt −η∇f(xt),
(3.1)
where η > 0 is a ﬁxed step-size parameter. The rationale behind (3.1)
is to make a small step in the direction that minimizes the local ﬁrst
order Taylor approximation of f (also known as the steepest descent
direction).
As we shall see, methods of the type (3.1) can obtain an oracle
complexity independent of the dimension1. This feature makes them
particularly attractive for optimization in very high dimension.
Apart from Section 3.3, in this chapter ∥· ∥denotes the Euclidean
norm. The set of constraints X ⊂Rn is assumed to be compact and
1Of course the computational complexity remains at least linear in the dimension
since one needs to manipulate gradients.
262


<!-- Page 36 -->

3.1. Projected subgradient descent for Lipschitz functions
263
x
y
∥y −x∥
ΠX (y)
∥y −ΠX (y)∥
∥ΠX (y) −x∥
X
Figure 3.1: Illustration of Lemma 3.1.
convex. We deﬁne the projection operator ΠX on X by
ΠX (x) = argmin
y∈X
∥x −y∥.
The following lemma will prove to be useful in our study. It is an easy
corollary of Proposition 1.3, see also Figure 3.1.
Lemma 3.1. Let x ∈X and y ∈Rn, then
(ΠX (y) −x)⊤(ΠX (y) −y) ≤0,
which also implies ∥ΠX (y) −x∥2 + ∥y −ΠX (y)∥2 ≤∥y −x∥2.
Unless speciﬁed otherwise all the proofs in this chapter are taken
from Nesterov [2004a] (with slight simpliﬁcation in some cases).
3.1
Projected subgradient descent for Lipschitz functions
In this section we assume that X is contained in an Euclidean ball
centered at x1 ∈X and of radius R. Furthermore we assume that f is
such that for any x ∈X and any g ∈∂f(x) (we assume ∂f(x) ̸= ∅),


<!-- Page 37 -->

264
Dimension-free convex optimization
xt
yt+1
gradient step
(3.2)
xt+1
projection (3.3)
X
Figure 3.2: Illustration of the projected subgradient descent method.
one has ∥g∥≤L. Note that by the subgradient inequality and Cauchy-
Schwarz this implies that f is L-Lipschitz on X, that is |f(x)−f(y)| ≤
L∥x −y∥.
In this context we make two modiﬁcations to the basic gradient
descent (3.1). First, obviously, we replace the gradient ∇f(x) (which
may not exist) by a subgradient g ∈∂f(x). Secondly, and more impor-
tantly, we make sure that the updated point lies in X by projecting
back (if necessary) onto it. This gives the projected subgradient descent
algorithm2 which iterates the following equations for t ≥1:
yt+1 = xt −ηgt, where gt ∈∂f(xt),
(3.2)
xt+1 = ΠX (yt+1).
(3.3)
This procedure is illustrated in Figure 3.2. We prove now a rate of
convergence for this method under the above assumptions.
Theorem 3.2. The projected subgradient descent method with η =
2In the optimization literature the term “descent" is reserved for methods such
that f(xt+1) ≤f(xt). In that sense the projected subgradient descent is not a
descent method.


<!-- Page 38 -->

3.1. Projected subgradient descent for Lipschitz functions
265
R
L
√
t satisﬁes
f
 
1
t
t
X
s=1
xs
!
−f(x∗) ≤RL
√
t .
Proof. Using the deﬁnition of subgradients, the deﬁnition of the
method, and the elementary identity 2a⊤b = ∥a∥2 + ∥b∥2 −∥a −b∥2,
one obtains
f(xs) −f(x∗)
≤
g⊤
s (xs −x∗)
=
1
η(xs −ys+1)⊤(xs −x∗)
=
1
2η

∥xs −x∗∥2 + ∥xs −ys+1∥2 −∥ys+1 −x∗∥2
=
1
2η

∥xs −x∗∥2 −∥ys+1 −x∗∥2
+ η
2∥gs∥2.
Now note that ∥gs∥≤L, and furthermore by Lemma 3.1
∥ys+1 −x∗∥≥∥xs+1 −x∗∥.
Summing the resulting inequality over s, and using that ∥x1 −x∗∥≤R
yield
t
X
s=1
(f(xs) −f(x∗)) ≤R2
2η + ηL2t
2
.
Plugging in the value of η directly gives the statement (recall that by
convexity f((1/t) Pt
s=1 xs) ≤1
t
Pt
s=1 f(xs)).
We will show in Section 3.5 that the rate given in Theorem 3.2
is unimprovable from a black-box perspective. Thus to reach an ε-
optimal point one needs Θ(1/ε2) calls to the oracle. In some sense
this is an astonishing result as this complexity is independent3 of the
ambient dimension n. On the other hand this is also quite disappointing
compared to the scaling in log(1/ε) of the center of gravity and ellipsoid
method of Chapter 2. To put it diﬀerently with gradient descent one
could hope to reach a reasonable accuracy in very high dimension,
while with the ellipsoid method one can reach very high accuracy in
3Observe however that the quantities R and L may dependent on the dimension,
see Chapter 4 for more on this.


<!-- Page 39 -->

266
Dimension-free convex optimization
reasonably small dimension. A major task in the following sections
will be to explore more restrictive assumptions on the function to be
optimized in order to have the best of both worlds, that is an oracle
complexity independent of the dimension and with a scaling in log(1/ε).
The computational bottleneck of the projected subgradient descent
is often the projection step (3.3) which is a convex optimization problem
by itself. In some cases this problem may admit an analytical solution
(think of X being an Euclidean ball), or an easy and fast combinatorial
algorithm to solve it (this is the case for X being an ℓ1-ball, see Mac-
ulan and de Paula [1989]). We will see in Section 3.3 a projection-free
algorithm which operates under an extra assumption of smoothness on
the function to be optimized.
Finally we observe that the step-size recommended by Theorem 3.2
depends on the number of iterations to be performed. In practice this
may be an undesirable feature. However using a time-varying step size
of the form ηs =
R
L√s one can prove the same rate up to a log t factor.
In any case these step sizes are very small, which is the reason for
the slow convergence. In the next section we will see that by assuming
smoothness in the function f one can aﬀord to be much more aggressive.
Indeed in this case, as one approaches the optimum the size of the
gradients themselves will go to 0, resulting in a sort of “auto-tuning" of
the step sizes which does not happen for an arbitrary convex function.
3.2
Gradient descent for smooth functions
We say that a continuously diﬀerentiable function f is β-smooth if the
gradient ∇f is β-Lipschitz, that is
∥∇f(x) −∇f(y)∥≤β∥x −y∥.
Note that if f is twice diﬀerentiable then this is equivalent to the eigen-
values of the Hessians being smaller than β. In this section we explore
potential improvements in the rate of convergence under such a smooth-
ness assumption. In order to avoid technicalities we consider ﬁrst the
unconstrained situation, where f is a convex and β-smooth function
on Rn. The next theorem shows that gradient descent, which iterates


<!-- Page 40 -->

3.2. Gradient descent for smooth functions
267
xt+1 = xt −η∇f(xt), attains a much faster rate in this situation than
in the non-smooth case of the previous section.
Theorem 3.3. Let f be convex and β-smooth on Rn. Then gradient
descent with η = 1
β satisﬁes
f(xt) −f(x∗) ≤2β∥x1 −x∗∥2
t −1
.
Before embarking on the proof we state a few properties of smooth
convex functions.
Lemma 3.4. Let f be a β-smooth function on Rn. Then for any x, y ∈
Rn, one has
|f(x) −f(y) −∇f(y)⊤(x −y)| ≤β
2 ∥x −y∥2.
Proof. We represent f(x) −f(y) as an integral, apply Cauchy-Schwarz
and then β-smoothness:
|f(x) −f(y) −∇f(y)⊤(x −y)|
=

Z 1
0
∇f(y + t(x −y))⊤(x −y)dt −∇f(y)⊤(x −y)

≤
Z 1
0
∥∇f(y + t(x −y)) −∇f(y)∥· ∥x −y∥dt
≤
Z 1
0
βt∥x −y∥2dt
= β
2 ∥x −y∥2.
In particular this lemma shows that if f is convex and β-smooth,
then for any x, y ∈Rn, one has
0 ≤f(x) −f(y) −∇f(y)⊤(x −y) ≤β
2 ∥x −y∥2.
(3.4)
This gives in particular the following important inequality to evaluate
the improvement in one step of gradient descent:
f

x −1
β ∇f(x)

−f(x) ≤−1
2β ∥∇f(x)∥2.
(3.5)


<!-- Page 41 -->

268
Dimension-free convex optimization
The next lemma, which improves the basic inequality for subgradients
under the smoothness assumption, shows that in fact f is convex and
β-smooth if and only if (3.4) holds true. In the literature (3.4) is often
used as a deﬁnition of smooth convex functions.
Lemma 3.5. Let f be such that (3.4) holds true. Then for any x, y ∈
Rn, one has
f(x) −f(y) ≤∇f(x)⊤(x −y) −1
2β ∥∇f(x) −∇f(y)∥2.
Proof. Let z = y −1
β(∇f(y) −∇f(x)). Then one has
f(x) −f(y)
= f(x) −f(z) + f(z) −f(y)
≤∇f(x)⊤(x −z) + ∇f(y)⊤(z −y) + β
2 ∥z −y∥2
= ∇f(x)⊤(x −y) + (∇f(x) −∇f(y))⊤(y −z) + 1
2β ∥∇f(x) −∇f(y)∥2
= ∇f(x)⊤(x −y) −1
2β ∥∇f(x) −∇f(y)∥2.
We can now prove Theorem 3.3
Proof. Using (3.5) and the deﬁnition of the method one has
f(xs+1) −f(xs) ≤−1
2β ∥∇f(xs)∥2.
In particular, denoting δs = f(xs) −f(x∗), this shows:
δs+1 ≤δs −1
2β ∥∇f(xs)∥2.
One also has by convexity
δs ≤∇f(xs)⊤(xs −x∗) ≤∥xs −x∗∥· ∥∇f(xs)∥.
We will prove that ∥xs −x∗∥is decreasing with s, which with the two
above displays will imply
δs+1 ≤δs −
1
2β∥x1 −x∗∥2 δ2
s.


<!-- Page 42 -->

3.2. Gradient descent for smooth functions
269
Let us see how to use this last inequality to conclude the proof. Let
ω =
1
2β∥x1−x∗∥2 , then4
ωδ2
s+δs+1 ≤δs ⇔ω δs
δs+1
+ 1
δs
≤
1
δs+1
⇒
1
δs+1
−1
δs
≥ω ⇒1
δt
≥ω(t−1).
Thus it only remains to show that ∥xs −x∗∥is decreasing with s. Using
Lemma 3.5 one immediately gets
(∇f(x) −∇f(y))⊤(x −y) ≥1
β ∥∇f(x) −∇f(y)∥2.
(3.6)
We use this as follows (together with ∇f(x∗) = 0)
∥xs+1 −x∗∥2
=
∥xs −1
β ∇f(xs) −x∗∥2
=
∥xs −x∗∥2 −2
β ∇f(xs)⊤(xs −x∗) + 1
β2 ∥∇f(xs)∥2
≤
∥xs −x∗∥2 −1
β2 ∥∇f(xs)∥2
≤
∥xs −x∗∥2,
which concludes the proof.
The constrained case
We now come back to the constrained problem
min. f(x)
s.t. x ∈X.
Similarly to what we did in Section 3.1 we consider the projected gra-
dient descent algorithm, which iterates xt+1 = ΠX (xt −η∇f(xt)).
The key point in the analysis of gradient descent for unconstrained
smooth optimization is that a step of gradient descent started at x will
decrease the function value by at least
1
2β∥∇f(x)∥2, see (3.5). In the
constrained case we cannot expect that this would still hold true as a
step may be cut short by the projection. The next lemma deﬁnes the
“right" quantity to measure progress in the constrained case.
4The last step in the sequence of implications can be improved by taking δ1 into
account. Indeed one can easily show with (3.4) that δ1 ≤
1
4ω . This improves the rate
of Theorem 3.3 from 2β∥x1−x∗∥2
t−1
to 2β∥x1−x∗∥2
t+3
.


<!-- Page 43 -->

270
Dimension-free convex optimization
Lemma 3.6. Let x, y ∈X, x+ = ΠX

x −1
β∇f(x)

, and gX (x) =
β(x −x+). Then the following holds true:
f(x+) −f(y) ≤gX (x)⊤(x −y) −1
2β ∥gX (x)∥2.
Proof. We ﬁrst observe that
∇f(x)⊤(x+ −y) ≤gX (x)⊤(x+ −y).
(3.7)
Indeed the above inequality is equivalent to

x+ −

x −1
β ∇f(x)
⊤
(x+ −y) ≤0,
which follows from Lemma 3.1. Now we use (3.7) as follows to prove
the lemma (we also use (3.4) which still holds true in the constrained
case)
f(x+) −f(y)
= f(x+) −f(x) + f(x) −f(y)
≤∇f(x)⊤(x+ −x) + β
2 ∥x+ −x∥2 + ∇f(x)⊤(x −y)
= ∇f(x)⊤(x+ −y) + 1
2β ∥gX (x)∥2
≤gX (x)⊤(x+ −y) + 1
2β ∥gX (x)∥2
= gX (x)⊤(x −y) −1
2β ∥gX (x)∥2.
We can now prove the following result.
Theorem 3.7. Let f be convex and β-smooth on X. Then projected
gradient descent with η = 1
β satisﬁes
f(xt) −f(x∗) ≤3β∥x1 −x∗∥2 + f(x1) −f(x∗)
t
.
Proof. Lemma 3.6 immediately gives
f(xs+1) −f(xs) ≤−1
2β ∥gX (xs)∥2,


<!-- Page 44 -->

3.3. Conditional gradient descent, aka Frank-Wolfe
271
and
f(xs+1) −f(x∗) ≤∥gX (xs)∥· ∥xs −x∗∥.
We will prove that ∥xs −x∗∥is decreasing with s, which with the two
above displays will imply
δs+1 ≤δs −
1
2β∥x1 −x∗∥2 δ2
s+1.
An easy induction shows that
δs ≤3β∥x1 −x∗∥2 + f(x1) −f(x∗)
s
.
Thus it only remains to show that ∥xs −x∗∥is decreasing with s. Using
Lemma 3.6 one can see that gX (xs)⊤(xs −x∗) ≥
1
2β∥gX (xs)∥2 which
implies
∥xs+1 −x∗∥2
=
∥xs −1
β gX (xs) −x∗∥2
=
∥xs −x∗∥2 −2
β gX (xs)⊤(xs −x∗) + 1
β2 ∥gX (xs)∥2
≤
∥xs −x∗∥2.
3.3
Conditional gradient descent, aka Frank-Wolfe
We describe now an alternative algorithm to minimize a smooth con-
vex function f over a compact convex set X. The conditional gradient
descent, introduced in Frank and Wolfe [1956], performs the following
update for t ≥1, where (γs)s≥1 is a ﬁxed sequence,
yt ∈argminy∈X ∇f(xt)⊤y
(3.8)
xt+1 = (1 −γt)xt + γtyt.
(3.9)
In words conditional gradient descent makes a step in the steepest
descent direction given the constraint set X, see Figure 3.3 for an il-
lustration. From a computational perspective, a key property of this


<!-- Page 45 -->

272
Dimension-free convex optimization
xt
yt
−∇f(xt)
xt+1
X
Figure 3.3: Illustration of conditional gradient descent.
scheme is that it replaces the projection step of projected gradient de-
scent by a linear optimization over X, which in some cases can be a
much simpler problem.
We now turn to the analysis of this method. A major advantage of
conditional gradient descent over projected gradient descent is that the
former can adapt to smoothness in an arbitrary norm. Precisely let f
be β-smooth in some norm ∥· ∥, that is ∥∇f(x) −∇f(y)∥∗≤β∥x −y∥
where the dual norm ∥· ∥∗is deﬁned as ∥g∥∗= supx∈Rn:∥x∥≤1 g⊤x.
The following result is extracted from Jaggi [2013] (see also Dunn and
Harshbarger [1978]).
Theorem 3.8. Let f be a convex and β-smooth function w.r.t. some
norm ∥· ∥, R = supx,y∈X ∥x −y∥, and γs =
2
s+1 for s ≥1. Then for any
t ≥2, one has
f(xt) −f(x∗) ≤2βR2
t + 1 .
Proof. The following inequalities hold true, using respectively β-
smoothness (it can easily be seen that (3.4) holds true for smoothness
in an arbitrary norm), the deﬁnition of xs+1, the deﬁnition of ys, and


<!-- Page 46 -->

3.3. Conditional gradient descent, aka Frank-Wolfe
273
the convexity of f:
f(xs+1) −f(xs)
≤
∇f(xs)⊤(xs+1 −xs) + β
2 ∥xs+1 −xs∥2
≤
γs∇f(xs)⊤(ys −xs) + β
2 γ2
sR2
≤
γs∇f(xs)⊤(x∗−xs) + β
2 γ2
sR2
≤
γs(f(x∗) −f(xs)) + β
2 γ2
sR2.
Rewriting this inequality in terms of δs = f(xs) −f(x∗) one obtains
δs+1 ≤(1 −γs)δs + β
2 γ2
sR2.
A simple induction using that γs =
2
s+1 ﬁnishes the proof (note that
the initialization is done at step 2 with the above inequality yielding
δ2 ≤β
2 R2).
In addition to being projection-free and “norm-free", the conditional
gradient descent satisﬁes a perhaps even more important property: it
produces sparse iterates. More precisely consider the situation where
X ⊂Rn is a polytope, that is the convex hull of a ﬁnite set of points
(these points are called the vertices of X). Then Carathéodory’s theo-
rem states that any point x ∈X can be written as a convex combination
of at most n + 1 vertices of X. On the other hand, by deﬁnition of the
conditional gradient descent, one knows that the tth iterate xt can be
written as a convex combination of t vertices (assuming that x1 is a
vertex). Thanks to the dimension-free rate of convergence one is usu-
ally interested in the regime where t ≪n, and thus we see that the
iterates of conditional gradient descent are very sparse in their vertex
representation.
We note an interesting corollary of the sparsity property together
with the rate of convergence we proved: smooth functions on the sim-
plex {x ∈Rn
+ : Pn
i=1 xi = 1} always admit sparse approximate mini-
mizers. More precisely there must exist a point x with only t non-zero
coordinates and such that f(x) −f(x∗) = O(1/t). Clearly this is the
best one can hope for in general, as it can be seen with the function


<!-- Page 47 -->

274
Dimension-free convex optimization
f(x) = ∥x∥2
2 since by Cauchy-Schwarz one has ∥x∥1 ≤
p
∥x∥0∥x∥2
which implies on the simplex ∥x∥2
2 ≥1/∥x∥0.
Next we describe an application where the three properties of condi-
tional gradient descent (projection-free, norm-free, and sparse iterates)
are critical to develop a computationally eﬃcient procedure.
An application of conditional gradient descent: Least-squares re-
gression with structured sparsity
This example is inspired by Lugosi [2010] (see also Jones [1992]). Con-
sider the problem of approximating a signal Y ∈Rn by a “small" com-
bination of dictionary elements d1, . . . , dN ∈Rn. One way to do this
is to consider a LASSO type problem in dimension N of the following
form (with λ ∈R ﬁxed)
min
x∈RN
Y −
N
X
i=1
x(i)di
2
2 + λ∥x∥1.
Let D ∈Rn×N be the dictionary matrix with ith column given by di.
Instead of considering the penalized version of the problem one could
look at the following constrained problem (with s ∈R ﬁxed) on which
we will now focus, see e.g. Friedlander and Tseng [2007],
min
x∈RN ∥Y −Dx∥2
2
⇔
min
x∈RN ∥Y/s −Dx∥2
2
(3.10)
subject to ∥x∥1 ≤s
subject to ∥x∥1 ≤1.
We make some assumptions on the dictionary. We are interested in
situations where the size of the dictionary N can be very large, poten-
tially exponential in the ambient dimension n. Nonetheless we want to
restrict our attention to algorithms that run in reasonable time with
respect to the ambient dimension n, that is we want polynomial time
algorithms in n. Of course in general this is impossible, and we need to
assume that the dictionary has some structure that can be exploited.
Here we make the assumption that one can do linear optimization over
the dictionary in polynomial time in n. More precisely we assume that
one can solve in time p(n) (where p is polynomial) the following prob-
lem for any y ∈Rn:
min
1≤i≤N y⊤di.


<!-- Page 48 -->

3.3. Conditional gradient descent, aka Frank-Wolfe
275
This assumption is met for many combinatorial dictionaries. For in-
stance the dicÂŋtioÂŋnary eleÂŋments could be vecÂŋtor of inciÂŋ-
dence of spanÂŋning trees in some ﬁxed graph, in which case the
linÂŋear optiÂŋmizaÂŋtion probÂŋlem can be solved with a greedy
algorithm.
Finally, for normalization issues, we assume that the ℓ2-norm of
the dictionary elements are controlled by some m > 0, that is ∥di∥2 ≤
m, ∀i ∈[N].
Our problem of interest (3.10) corresponds to minimizing the func-
tion f(x) = 1
2∥Y −Dx∥2
2 on the ℓ1-ball of RN in polynomial time in
n. At ﬁrst sight this task may seem completely impossible, indeed one
is not even allowed to write down entirely a vector x ∈RN (since this
would take time linear in N). The key property that will save us is that
this function admits sparse minimizers as we discussed in the previous
section, and this will be exploited by the conditional gradient descent
method.
First let us study the computational complexity of the tth step of
conditional gradient descent. Observe that
∇f(x) = D⊤(Dx −Y ).
Now assume that zt = Dxt −Y ∈Rn is already computed, then to
compute (3.8) one needs to ﬁnd the coordinate it ∈[N] that maximizes
|[∇f(xt)](i)| which can be done by maximizing d⊤
i zt and −d⊤
i zt. Thus
(3.8) takes time O(p(n)). Computing xt+1 from xt and it takes time
O(t) since ∥xt∥0 ≤t, and computing zt+1 from zt and it takes time
O(n). Thus the overall time complexity of running t steps is (we assume
p(n) = Ω(n))
O(tp(n) + t2).
(3.11)
To derive a rate of convergence it remains to study the smoothness
of f. This can be done as follows:
∥∇f(x) −∇f(y)∥∞
=
∥D⊤D(x −y)∥∞
=
max
1≤i≤N
d⊤
i


N
X
j=1
dj(x(j) −y(j))



≤
m2∥x −y∥1,


<!-- Page 49 -->

276
Dimension-free convex optimization
which means that f is m2-smooth with respect to the ℓ1-norm. Thus
we get the following rate of convergence:
f(xt) −f(x∗) ≤8m2
t + 1.
(3.12)
Putting together (3.11) and (3.12) we proved that one can get an ε-
optimal solution to (3.10) with a computational eﬀort of O(m2p(n)/ε+
m4/ε2) using the conditional gradient descent.
3.4
Strong convexity
We will now discuss another property of convex functions that can
signiﬁcantly speed-up the convergence of ﬁrst order methods: strong
convexity. We say that f : X →R is α-strongly convex if it satisﬁes the
following improved subgradient inequality:
f(x) −f(y) ≤∇f(x)⊤(x −y) −α
2 ∥x −y∥2.
(3.13)
Of course this deﬁnition does not require diﬀerentiability of the function
f, and one can replace ∇f(x) in the inequality above by g ∈∂f(x). It
is immediate to verify that a function f is α-strongly convex if and only
if x 7→f(x) −α
2 ∥x∥2 is convex (in particular if f is twice diﬀerentiable
then the eigenvalues of the Hessians of f have to be larger than α).
The strong convexity parameter α is a measure of the curvature of
f. For instance a linear function has no curvature and hence α = 0.
On the other hand one can clearly see why a large value of α would
lead to a faster rate: in this case a point far from the optimum will
have a large gradient, and thus gradient descent will make very big
steps when far from the optimum. Of course if the function is non-
smooth one still has to be careful and tune the step-sizes to be relatively
small, but nonetheless we will be able to improve the oracle complexity
from O(1/ε2) to O(1/(αε)). On the other hand with the additional
assumption of β-smoothness we will prove that gradient descent with
a constant step-size achieves a linear rate of convergence, precisely the
oracle complexity will be O( β
α log(1/ε)). This achieves the objective we
had set after Theorem 3.2: strongly-convex and smooth functions can
be optimized in very large dimension and up to very high accuracy.


<!-- Page 50 -->

3.4. Strong convexity
277
Before going into the proofs let us discuss another interpretation of
strong-convexity and its relation to smoothness. Equation (3.13) can
be read as follows: at any point x one can ﬁnd a (convex) quadratic
lower bound q−
x (y) = f(x)+∇f(x)⊤(y −x)+ α
2 ∥x−y∥2 to the function
f, i.e. q−
x (y) ≤f(y), ∀y ∈X (and q−
x (x) = f(x)). On the other hand for
β-smoothness (3.4) implies that at any point y one can ﬁnd a (convex)
quadratic upper bound q+
y (x) = f(y) + ∇f(y)⊤(x −y) + β
2 ∥x −y∥2 to
the function f, i.e. q+
y (x) ≥f(x), ∀x ∈X (and q+
y (y) = f(y)). Thus in
some sense strong convexity is a dual assumption to smoothness, and in
fact this can be made precise within the framework of Fenchel duality.
Also remark that clearly one always has β ≥α.
3.4.1
Strongly convex and Lipschitz functions
We consider here the projected subgradient descent algorithm with
time-varying step size (ηt)t≥1, that is
yt+1 = xt −ηtgt, where gt ∈∂f(xt)
xt+1 = ΠX (yt+1).
The following result is extracted from Lacoste-Julien et al. [2012].
Theorem 3.9. Let f be α-strongly convex and L-Lipschitz on X. Then
projected subgradient descent with ηs =
2
α(s+1) satisﬁes
f
 t
X
s=1
2s
t(t + 1)xs
!
−f(x∗) ≤
2L2
α(t + 1).
Proof. Coming back to our original analysis of projected subgradient
descent in Section 3.1 and using the strong convexity assumption one
immediately obtains
f(xs) −f(x∗) ≤ηs
2 L2 +
 1
2ηs
−α
2

∥xs −x∗∥2 −1
2ηs
∥xs+1 −x∗∥2.
Multiplying this inequality by s yields
s(f(xs)−f(x∗)) ≤L2
α + α
4

s(s−1)∥xs −x∗∥2 −s(s+1)∥xs+1 −x∗∥2

,
Now sum the resulting inequality over s = 1 to s = t, and apply
Jensen’s inequality to obtain the claimed statement.


<!-- Page 51 -->

278
Dimension-free convex optimization
3.4.2
Strongly convex and smooth functions
As we will see now, having both strong convexity and smoothness allows
for a drastic improvement in the convergence rate. We denote κ = β
α
for the condition number of f. The key observation is that Lemma 3.6
can be improved to (with the notation of the lemma):
f(x+) −f(y) ≤gX (x)⊤(x −y) −1
2β ∥gX (x)∥2 −α
2 ∥x −y∥2.
(3.14)
Theorem 3.10. Let f be α-strongly convex and β-smooth on X. Then
projected gradient descent with η = 1
β satisﬁes for t ≥0,
∥xt+1 −x∗∥2 ≤exp

−t
κ

∥x1 −x∗∥2.
Proof. Using (3.14) with y = x∗one directly obtains
∥xt+1 −x∗∥2
=
∥xt −1
β gX (xt) −x∗∥2
=
∥xt −x∗∥2 −2
β gX (xt)⊤(xt −x∗) + 1
β2 ∥gX (xt)∥2
≤

1 −α
β

∥xt −x∗∥2
≤

1 −α
β
t
∥x1 −x∗∥2
≤
exp

−t
κ

∥x1 −x∗∥2,
which concludes the proof.
We now show that in the unconstrained case one can improve the
rate by a constant factor, precisely one can replace κ by (κ + 1)/4 in
the oracle complexity bound by using a larger step size. This is not a
spectacular gain but the reasoning is based on an improvement of (3.6)
which can be of interest by itself. Note that (3.6) and the lemma to
follow are sometimes referred to as coercivity of the gradient.
Lemma 3.11. Let f be β-smooth and α-strongly convex on Rn. Then
for all x, y ∈Rn, one has
(∇f(x)−∇f(y))⊤(x−y) ≥
αβ
β + α∥x−y∥2 +
1
β + α∥∇f(x)−∇f(y)∥2.


<!-- Page 52 -->

3.5. Lower bounds
279
Proof. Let ϕ(x) = f(x) −α
2 ∥x∥2. By deﬁnition of α-strong convexity
one has that ϕ is convex. Furthermore one can show that ϕ is (β −α)-
smooth by proving (3.4) (and using that it implies smoothness). Thus
using (3.6) one gets
(∇ϕ(x) −∇ϕ(y))⊤(x −y) ≥
1
β −α∥∇ϕ(x) −∇ϕ(y)∥2,
which gives the claimed result with straightforward computations.
(Note that if α = β the smoothness of ϕ directly implies that
∇f(x) −∇f(y) = α(x −y) which proves the lemma in this case.)
Theorem 3.12. Let f be β-smooth and α-strongly convex on Rn. Then
gradient descent with η =
2
α+β satisﬁes
f(xt+1) −f(x∗) ≤β
2 exp

−
4t
κ + 1

∥x1 −x∗∥2.
Proof. First note that by β-smoothness (since ∇f(x∗) = 0) one has
f(xt) −f(x∗) ≤β
2 ∥xt −x∗∥2.
Now using Lemma 3.11 one obtains
∥xt+1 −x∗∥2
=
∥xt −η∇f(xt) −x∗∥2
=
∥xt −x∗∥2 −2η∇f(xt)⊤(xt −x∗) + η2∥∇f(xt)∥2
≤

1 −2 ηαβ
β + α

∥xt −x∗∥2 +

η2 −2
η
β + α

∥∇f(xt)∥2
=
κ −1
κ + 1
2
∥xt −x∗∥2
≤
exp

−
4t
κ + 1

∥x1 −x∗∥2,
which concludes the proof.
3.5
Lower bounds
We prove here various oracle complexity lower bounds. These results
ﬁrst appeared in Nemirovski and Yudin [1983] but we follow here the


<!-- Page 53 -->

280
Dimension-free convex optimization
simpliﬁed presentation of Nesterov [2004a]. In general a black-box pro-
cedure is a mapping from “history" to the next query point, that is it
maps (x1, g1, . . . , xt, gt) (with gs ∈∂f(xs)) to xt+1. In order to simplify
the notation and the argument, throughout the section we make the
following assumption on the black-box procedure: x1 = 0 and for any
t ≥0, xt+1 is in the linear span of g1, . . . , gt, that is
xt+1 ∈Span(g1, . . . , gt).
(3.15)
Let e1, . . . , en be the canonical basis of Rn, and B2(R) = {x ∈Rn :
∥x∥≤R}. We start with a theorem for the two non-smooth cases
(convex and strongly convex).
Theorem 3.13. Let t ≤n, L, R > 0. There exists a convex and L-
Lipschitz function f such that for any black-box procedure satisfying
(3.15),
min
1≤s≤t f(xs) −
min
x∈B2(R) f(x) ≥
RL
2(1 +
√
t).
There also exists an α-strongly convex and L-lipschitz function f such
that for any black-box procedure satisfying (3.15),
min
1≤s≤t f(xs) −
min
x∈B2( L
2α)
f(x) ≥L2
8αt.
Note that the above result is restricted to a number of iterations
smaller than the dimension, that is t ≤n. This restriction is of course
necessary to obtain lower bounds polynomial in 1/t: as we saw in Chap-
ter 2 one can always obtain an exponential rate of convergence when
the number of calls to the oracle is larger than the dimension.
Proof. We consider the following α-strongly convex function:
f(x) = γ max
1≤i≤t x(i) + α
2 ∥x∥2.
It is easy to see that
∂f(x) = αx + γconv

ei, i : x(i) = max
1≤j≤t x(j)

.
In particular if ∥x∥≤R then for any g ∈∂f(x) one has ∥g∥≤αR + γ.
In other words f is (αR + γ)-Lipschitz on B2(R).


<!-- Page 54 -->

3.5. Lower bounds
281
Next we describe the ﬁrst order oracle for this function: when asked
for a subgradient at x, it returns αx+γei where i is the ﬁrst coordinate
that satisﬁes x(i) = max1≤j≤t x(j). In particular when asked for a
subgradient at x1 = 0 it returns e1. Thus x2 must lie on the line
generated by e1. It is easy to see by induction that in fact xs must lie
in the linear span of e1, . . . , es−1. In particular for s ≤t we necessarily
have xs(t) = 0 and thus f(xs) ≥0.
It remains to compute the minimal value of f. Let y be such that
y(i) = −γ
αt for 1 ≤i ≤t and y(i) = 0 for t + 1 ≤i ≤n. It is clear that
0 ∈∂f(y) and thus the minimal value of f is
f(y) = −γ2
αt + α
2
γ2
α2t = −γ2
2αt.
Wrapping up, we proved that for any s ≤t one must have
f(xs) −f(x∗) ≥γ2
2αt.
Taking γ = L/2 and R = L
2α we proved the lower bound for α-strongly
convex functions (note in particular that ∥y∥2 = γ2
α2t =
L2
4α2t ≤R2 with
these parameters). On the other taking α = L
R
1
1+
√
t and γ = L
√
t
1+
√
t
concludes the proof for convex functions (note in particular that ∥y∥2 =
γ2
α2t = R2 with these parameters).
We proceed now to the smooth case. As we will see in the following
proofs we restrict our attention to quadratic functions, and it might
be useful to recall that in this case one can attain the exact optimum
in n calls to the oracle (see Section 2.4). We also recall that for a
twice diﬀerentiable function f, β-smoothness is equivalent to the largest
eigenvalue of the Hessians of f being smaller than β at any point, which
we write
∇2f(x) ⪯βIn, ∀x.
Furthermore α-strong convexity is equivalent to
∇2f(x) ⪰αIn, ∀x.


<!-- Page 55 -->

282
Dimension-free convex optimization
Theorem 3.14. Let t ≤(n −1)/2, β > 0. There exists a β-smooth
convex function f such that for any black-box procedure satisfying
(3.15),
min
1≤s≤t f(xs) −f(x∗) ≥3β
32
∥x1 −x∗∥2
(t + 1)2
.
Proof. In this proof for h : Rn →R we denote h∗= infx∈Rn h(x). For
k ≤n let Ak ∈Rn×n be the symmetric and tridiagonal matrix deﬁned
by
(Ak)i,j =





2,
i = j, i ≤k
−1,
j ∈{i −1, i + 1}, i ≤k, j ̸= k + 1
0,
otherwise.
It is easy to verify that 0 ⪯Ak ⪯4In since
x⊤Akx = 2
k
X
i=1
x(i)2−2
k−1
X
i=1
x(i)x(i+1) = x(1)2+x(k)2+
k−1
X
i=1
(x(i)−x(i+1))2.
We consider now the following β-smooth convex function:
f(x) = β
8 x⊤A2t+1x −β
4 x⊤e1.
Similarly to what happened in the proof Theorem 3.13, one can see
here too that xs must lie in the linear span of e1, . . . , es−1 (because of
our assumption on the black-box procedure). In particular for s ≤t we
necessarily have xs(i) = 0 for i = s, . . . , n, which implies x⊤
s A2t+1xs =
x⊤
s Asxs. In other words, if we denote
fk(x) = β
8 x⊤Akx −β
4 x⊤e1,
then we just proved that
f(xs) −f∗= fs(xs) −f∗
2t+1 ≥f∗
s −f∗
2t+1 ≥f∗
t −f∗
2t+1.
Thus it simply remains to compute the minimizer x∗
k of fk, its norm,
and the corresponding function value f∗
k.
The point x∗
k is the unique solution in the span of e1, . . . , ek of
Akx = e1. It is easy to verify that it is deﬁned by x∗
k(i) = 1 −
i
k+1 for
i = 1, . . . , k. Thus we immediately have:
f∗
k = β
8 (x∗
k)⊤Akx∗
k −β
4 (x∗
k)⊤e1 = −β
8 (x∗
k)⊤e1 = −β
8

1 −
1
k + 1

.


<!-- Page 56 -->

3.5. Lower bounds
283
Furthermore note that
∥x∗
k∥2 =
k
X
i=1

1 −
i
k + 1
2
=
k
X
i=1

i
k + 1
2
≤k + 1
3
.
Thus one obtains:
f∗
t −f∗
2t+1 = β
8

1
t + 1 −
1
2t + 2

≥3β
32
∥x∗
2t+1∥2
(t + 1)2 ,
which concludes the proof.
To simplify the proof of the next theorem we will consider the lim-
iting situation n →+∞. More precisely we assume now that we are
working in ℓ2 = {x = (x(n))n∈N : P+∞
i=1 x(i)2 < +∞} rather than in
Rn. Note that all the theorems we proved in this chapter are in fact
valid in an arbitrary Hilbert space H. We chose to work in Rn only for
clarity of the exposition.
Theorem 3.15. Let κ > 1. There exists a β-smooth and α-strongly
convex function f : ℓ2 →R with κ = β/α such that for any t ≥1 and
any black-box procedure satisfying (3.15) one has
f(xt) −f(x∗) ≥α
2
 √κ −1
√κ + 1
!2(t−1)
∥x1 −x∗∥2.
Note that for large values of the condition number κ one has
 √κ −1
√κ + 1
!2(t−1)
≈exp

−4(t −1)
√κ

.
Proof. The overall argument is similar to the proof of Theorem 3.14.
Let A : ℓ2 →ℓ2 be the linear operator that corresponds to the inﬁnite
tridiagonal matrix with 2 on the diagonal and −1 on the upper and
lower diagonals. We consider now the following function:
f(x) = α(κ −1)
8
(⟨Ax, x⟩−2⟨e1, x⟩) + α
2 ∥x∥2.
We already proved that 0 ⪯A ⪯4I which easily implies that f is α-
strongly convex and β-smooth. Now as always the key observation is


<!-- Page 57 -->

284
Dimension-free convex optimization
that for this function, thanks to our assumption on the black-box pro-
cedure, one necessarily has xt(i) = 0, ∀i ≥t. This implies in particular:
∥xt −x∗∥2 ≥
+∞
X
i=t
x∗(i)2.
Furthermore since f is α-strongly convex, one has
f(xt) −f(x∗) ≥α
2 ∥xt −x∗∥2.
Thus it only remains to compute x∗. This can be done by diﬀerentiating
f and setting the gradient to 0, which gives the following inﬁnite set
of equations
1 −2κ + 1
κ −1x∗(1) + x∗(2) = 0,
x∗(k −1) −2κ + 1
κ −1x∗(k) + x∗(k + 1) = 0, ∀k ≥2.
It is easy to verify that x∗deﬁned by x∗(i) =
 √κ−1
√κ+1
i satisfy this
inﬁnite set of equations, and the conclusion of the theorem then follows
by straightforward computations.
3.6
Geometric descent
So far our results leave a gap in the case of smooth optimization: gra-
dient descent achieves an oracle complexity of O(1/ε) (respectively
O(κ log(1/ε)) in the strongly convex case) while we proved a lower
bound of Ω(1/√ε) (respectively Ω(√κ log(1/ε))). In this section we
close these gaps with the geometric descent method which was re-
cently introduced in Bubeck et al. [2015b]. Historically the ﬁrst method
with optimal oracle complexity was proposed in Nemirovski and Yudin
[1983]. This method, inspired by the conjugate gradient (see Section
2.4), assumes an oracle to compute plane searches. In Nemirovski [1982]
this assumption was relaxed to a line search oracle (the geometric de-
scent method also requires a line search oracle). Finally in Nesterov
[1983] an optimal method requiring only a ﬁrst order oracle was in-
troduced. The latter algorithm, called Nesterov’s accelerated gradient


<!-- Page 58 -->

3.6. Geometric descent
285
descent, has been the most inﬂuential optimal method for smooth opti-
mization up to this day. We describe and analyze this method in Section
3.7. As we shall see the intuition behind Nesterov’s accelerated gradient
descent (both for the derivation of the algorithm and its analysis) is
not quite transparent, which motivates the present section as geometric
descent has a simple geometric interpretation loosely inspired from the
ellipsoid method (see Section 2.2).
We focus here on the unconstrained optimization of a smooth and
strongly convex function, and we prove that geometric descent achieves
the oracle complexity of O(√κ log(1/ε)), thus reducing the complex-
ity of the basic gradient descent by a factor √κ. We note that this
improvement is quite relevant for machine learning applications. Con-
sider for example the logistic regression problem described in Section
1.1: this is a smooth and strongly convex problem, with a smoothness
of order of a numerical constant, but with strong convexity equal to the
regularization parameter whose inverse can be as large as the sample
size. Thus in this case κ can be of order of the sample size, and a faster
rate by a factor of √κ is quite signiﬁcant. We also observe that this
improved rate for smooth and strongly convex objectives also implies
an almost optimal rate of O(log(1/ε)/√ε) for the smooth case, as one
can simply run geometric descent on the function x 7→f(x) + ε∥x∥2.
In Section 3.6.1 we describe the basic idea of geometric descent, and
we show how to obtain eﬀortlessly a geometric method with an oracle
complexity of O(κ log(1/ε)) (i.e., similar to gradient descent). Then we
explain why one should expect to be able to accelerate this method in
Section 3.6.2. The geometric descent method is described precisely and
analyzed in Section 3.6.3.
3.6.1
Warm-up: a geometric alternative to gradient descent
We start with some notation. Let B(x, r2) := {y ∈Rn : ∥y −x∥2 ≤r2}
(note that the second argument is the radius squared), and
x+ = x −1
β ∇f(x), and x++ = x −1
α∇f(x).


<!-- Page 59 -->

286
Dimension-free convex optimization
|g|
√1 −ε |g|
1
√1 −ε
Figure 3.4: One ball shrinks.
Rewriting the deﬁnition of strong convexity (3.13) as
f(y) ≥f(x) + ∇f(x)⊤(y −x) + α
2 ∥y −x∥2
⇔
α
2 ∥y −x + 1
α∇f(x)∥2 ≤∥∇f(x)∥2
2α
−(f(x) −f(y)),
one obtains an enclosing ball for the minimizer of f with the 0th and
1st order information at x:
x∗∈B
 
x++, ∥∇f(x)∥2
α2
−2
α(f(x) −f(x∗))
!
.
Furthermore recall that by smoothness (see (3.5)) one has f(x+) ≤
f(x) −
1
2β∥∇f(x)∥2 which allows to shrink the above ball by a factor
of 1 −1
κ and obtain the following:
x∗∈B
 
x++, ∥∇f(x)∥2
α2

1 −1
κ

−2
α(f(x+) −f(x∗))
!
(3.16)
This suggests a natural strategy: assuming that one has an enclosing
ball A := B(x, R2) for x∗(obtained from previous steps of the strat-
egy), one can then enclose x∗in a ball B containing the intersection
of B(x, R2) and the ball B

x++, ∥∇f(x)∥2
α2

1 −1
κ

obtained by (3.16).
Provided that the radius of B is a fraction of the radius of A, one can


<!-- Page 60 -->

3.6. Geometric descent
287
√1 −ε |g|
p
1 −ε|g|2
p
1 −√ε
Figure 3.5: Two balls shrink.
then iterate the procedure by replacing A by B, leading to a linear
convergence rate. Evaluating the rate at which the radius shrinks is an
elementary calculation: for any g ∈Rn, ε ∈(0, 1), there exists x ∈Rn
such that
B(0, 1) ∩B(g, ∥g∥2(1 −ε)) ⊂B(x, 1 −ε).
(Figure 3.4)
Thus we see that in the strategy described above, the radius squared
of the enclosing ball for x∗shrinks by a factor 1 −1
κ at each iteration,
thus matching the rate of convergence of gradient descent (see Theorem
3.10).
3.6.2
Acceleration
In the argument from the previous section we missed the following
opportunity: observe that the ball A = B(x, R2) was obtained by inter-
sections of previous balls of the form given by (3.16), and thus the
new value f(x) could be used to reduce the radius of those previ-
ous balls too (an important caveat is that the value f(x) should be
smaller than the values used to build those previous balls). Poten-
tially this could show that the optimum is in fact contained in the
ball B

x, R2 −1
κ∥∇f(x)∥2
. By taking the intersection with the ball


<!-- Page 61 -->

288
Dimension-free convex optimization
B

x++, ∥∇f(x)∥2
α2

1 −1
κ

this would allow to obtain a new ball with
radius shrunk by a factor 1 −
1
√κ (instead of 1 −1
κ): indeed for any
g ∈Rn, ε ∈(0, 1), there exists x ∈Rn such that
B(0, 1 −ε∥g∥2) ∩B(g, ∥g∥2(1 −ε)) ⊂B(x, 1 −√ε).
(Figure 3.5)
Thus it only remains to deal with the caveat noted above, which we
do via a line search. In turns this line search might shift the new ball
(3.16), and to deal with this we shall need the following strengthening
of the above set inclusion (we refer to Bubeck et al. [2015b] for a simple
proof of this result):
Lemma 3.16. Let a ∈Rn and ε ∈(0, 1), g ∈R+. Assume that ∥a∥≥g.
Then there exists c ∈Rn such that for any δ ≥0,
B(0, 1 −εg2 −δ) ∩B(a, g2(1 −ε) −δ) ⊂B
c, 1 −√ε −δ
 .
3.6.3
The geometric descent method
Let x0 ∈Rn, c0 = x++
0
, and R2
0 =

1 −1
κ
 ∥∇f(x0)∥2
α2
. For any t ≥0 let
xt+1 =
argmin
x∈{(1−λ)ct+λx+
t , λ∈R}
f(x),
and ct+1 (respectively R2
t+1) be the center (respectively the squared
radius) of the ball given by (the proof of) Lemma 3.16 which contains
B
 
ct, R2
t −∥∇f(xt+1)∥2
α2κ
!
∩B
 
x++
t+1, ∥∇f(xt+1)∥2
α2

1 −1
κ
!
.
Formulas for ct+1 and R2
t+1 are given at the end of this section.
Theorem 3.17. For any t ≥0, one has x∗∈B(ct, R2
t ), R2
t+1 ≤

1 −
1
√κ

R2
t , and thus
∥x∗−ct∥2 ≤

1 −1
√κ
t
R2
0.
Proof. We will prove a stronger claim by induction that for each t ≥0,
one has
x∗∈B

ct, R2
t −2
α

f(x+
t ) −f(x∗)

.


<!-- Page 62 -->

3.7. Nesterov’s accelerated gradient descent
289
The case t = 0 follows immediately by (3.16). Let us assume that the
above display is true for some t ≥0. Then using f(x+
t+1) ≤f(xt+1) −
1
2β∥∇f(xt+1)∥2 ≤f(x+
t ) −1
2β∥∇f(xt+1)∥2, one gets
x∗∈B
 
ct, R2
t −∥∇f(xt+1)∥2
α2κ
−2
α

f(x+
t+1) −f(x∗)
!
.
Furthermore by (3.16) one also has
B
 
x++
t+1, ∥∇f(xt+1)∥2
α2

1 −1
κ

−2
α

f(x+
t+1) −f(x∗)
!
.
Thus it only remains to observe that the squared radius of the ball given
by Lemma 3.16 which encloses the intersection of the two above balls is
smaller than

1 −
1
√κ

R2
t −2
α(f(x+
t+1)−f(x∗)). We apply Lemma 3.16
after moving ct to the origin and scaling distances by Rt. We set ε = 1
κ,
g = ∥∇f(xt+1)∥
α
, δ = 2
α

f(x+
t+1) −f(x∗)

and a = x++
t+1 −ct. The line
search step of the algorithm implies that ∇f(xt+1)⊤(xt+1 −ct) = 0 and
therefore, ∥a∥= ∥x++
t+1 −ct∥≥∥∇f(xt+1)∥/α = g and Lemma 3.16
applies to give the result.
One can use the following formulas for ct+1 and R2
t+1 (they are
derived from the proof of Lemma 3.16). If |∇f(xt+1)|2/α2 < R2
t /2
then one can tate ct+1 = x++
t+1 and R2
t+1 = |∇f(xt+1)|2
α2

1 −1
κ

. On the
other hand if |∇f(xt+1)|2/α2 ≥R2
t /2 then one can tate
ct+1
=
ct + R2
t + |xt+1 −ct|2
2|x++
t+1 −ct|2
(x++
t+1 −ct),
R2
t+1
=
R2
t −|∇f(xt+1)|2
α2κ
−
 
R2
t + ∥xt+1 −ct∥2
2∥x++
t+1 −ct∥
!2
.
3.7
Nesterov’s accelerated gradient descent
We describe here the original Nesterov’s method which attains the op-
timal oracle complexity for smooth convex optimization. We give the
details of the method both for the strongly convex and non-strongly
convex case. We refer to Su et al. [2014] for a recent interpretation of


<!-- Page 63 -->

290
Dimension-free convex optimization
xs
ys
ys+1
xs+1
−1
β∇f(xs)
ys+2
xs+2
Figure 3.6: Illustration of Nesterov’s accelerated gradient descent.
the method in terms of diﬀerential equations, and to Allen-Zhu and
Orecchia [2014] for its relation to mirror descent (see Chapter 4).
3.7.1
The smooth and strongly convex case
Nesterov’s accelerated gradient descent, illustrated in Figure 3.6, can
be described as follows: Start at an arbitrary initial point x1 = y1 and
then iterate the following equations for t ≥1,
yt+1
=
xt −1
β ∇f(xt),
xt+1
=
 
1 +
√κ −1
√κ + 1
!
yt+1 −
√κ −1
√κ + 1yt.
Theorem 3.18. Let f be α-strongly convex and β-smooth, then Nes-
terov’s accelerated gradient descent satisﬁes
f(yt) −f(x∗) ≤α + β
2
∥x1 −x∗∥2 exp

−t −1
√κ

.
Proof. We deﬁne α-strongly convex quadratic functions Φs, s ≥1 by


<!-- Page 64 -->

3.7. Nesterov’s accelerated gradient descent
291
induction as follows:
Φ1(x) = f(x1) + α
2 ∥x −x1∥2,
Φs+1(x) =

1 −1
√κ

Φs(x)
+ 1
√κ

f(xs) + ∇f(xs)⊤(x −xs) + α
2 ∥x −xs∥2

.
(3.17)
Intuitively Φs becomes a ﬁner and ﬁner approximation (from below) to
f in the following sense:
Φs+1(x) ≤f(x) +

1 −1
√κ
s
(Φ1(x) −f(x)).
(3.18)
The above inequality can be proved immediately by induction, using
the fact that by α-strong convexity one has
f(xs) + ∇f(xs)⊤(x −xs) + α
2 ∥x −xs∥2 ≤f(x).
Equation (3.18) by itself does not say much, for it to be useful one
needs to understand how “far" below f is Φs. The following inequality
answers this question:
f(ys) ≤min
x∈Rn Φs(x).
(3.19)
The rest of the proof is devoted to showing that (3.19) holds true, but
ﬁrst let us see how to combine (3.18) and (3.19) to obtain the rate given
by the theorem (we use that by β-smoothness one has f(x) −f(x∗) ≤
β
2 ∥x −x∗∥2):
f(yt) −f(x∗)
≤
Φt(x∗) −f(x∗)
≤

1 −1
√κ
t−1
(Φ1(x∗) −f(x∗))
≤
α + β
2
∥x1 −x∗∥2

1 −1
√κ
t−1
.
We now prove (3.19) by induction (note that it is true at s = 1 since
x1 = y1). Let Φ∗
s = minx∈Rn Φs(x). Using the deﬁnition of ys+1 (and


<!-- Page 65 -->

292
Dimension-free convex optimization
β-smoothness), convexity, and the induction hypothesis, one gets
f(ys+1)
≤
f(xs) −1
2β ∥∇f(xs)∥2
=

1 −1
√κ

f(ys) +

1 −1
√κ

(f(xs) −f(ys))
+ 1
√κf(xs) −1
2β ∥∇f(xs)∥2
≤

1 −1
√κ

Φ∗
s +

1 −1
√κ

∇f(xs)⊤(xs −ys)
+ 1
√κf(xs) −1
2β ∥∇f(xs)∥2.
Thus we now have to show that
Φ∗
s+1
≥

1 −1
√κ

Φ∗
s +

1 −1
√κ

∇f(xs)⊤(xs −ys)
+ 1
√κf(xs) −1
2β ∥∇f(xs)∥2.
(3.20)
To prove this inequality we have to understand better the functions
Φs. First note that ∇2Φs(x) = αIn (immediate by induction) and thus
Φs has to be of the following form:
Φs(x) = Φ∗
s + α
2 ∥x −vs∥2,
for some vs ∈Rn. Now observe that by diﬀerentiating (3.17) and using
the above form of Φs one obtains
∇Φs+1(x) = α

1 −1
√κ

(x −vs) + 1
√κ∇f(xs) + α
√κ(x −xs).
In particular Φs+1 is by deﬁnition minimized at vs+1 which can now be
deﬁned by induction using the above identity, precisely:
vs+1 =

1 −1
√κ

vs + 1
√κxs −
1
α√κ∇f(xs).
(3.21)
Using the form of Φs and Φs+1, as well as the original deﬁnition (3.17)
one gets the following identity by evaluating Φs+1 at xs:
Φ∗
s+1 + α
2 ∥xs −vs+1∥2
=

1 −1
√κ

Φ∗
s + α
2

1 −1
√κ

∥xs −vs∥2 + 1
√κf(xs).
(3.22)


<!-- Page 66 -->

3.7. Nesterov’s accelerated gradient descent
293
Note that thanks to (3.21) one has
∥xs −vs+1∥2
=

1 −1
√κ
2
∥xs −vs∥2 +
1
α2κ∥∇f(xs)∥2
−
2
α√κ

1 −1
√κ

∇f(xs)⊤(vs −xs),
which combined with (3.22) yields
Φ∗
s+1
=

1 −1
√κ

Φ∗
s + 1
√κf(xs) +
α
2√κ

1 −1
√κ

∥xs −vs∥2
−1
2β ∥∇f(xs)∥2 + 1
√κ

1 −1
√κ

∇f(xs)⊤(vs −xs).
Finally we show by induction that vs −xs = √κ(xs −ys), which con-
cludes the proof of (3.20) and thus also concludes the proof of the
theorem:
vs+1 −xs+1
=

1 −1
√κ

vs + 1
√κxs −
1
α√κ∇f(xs) −xs+1
=
√κxs −(√κ −1)ys −
√κ
β ∇f(xs) −xs+1
=
√κys+1 −(√κ −1)ys −xs+1
=
√κ(xs+1 −ys+1),
where the ﬁrst equality comes from (3.21), the second from the induc-
tion hypothesis, the third from the deﬁnition of ys+1 and the last one
from the deﬁnition of xs+1.

---
*[End of extracted section containing Theorem 3.18]*
