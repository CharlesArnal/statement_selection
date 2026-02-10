| MIT OpenCourseWare |
|--------------------|
| http://ocw.mit.edu |

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

# Hopf Bifurcations.

Department of Mathematics Massachusetts Institute of Technology Cambridge, Massachusetts MA 02139 September 25, 1999

In two dimensions a Hopf bifurcation occurs as a Spiral Point switches from stableto unstable (or vice versa) and a periodic solution appears. There are, however, more details to the story than this: The fact that a critical point switches from stable to unstable spiral (or vice versa) alone does not guarantee that a periodic solution will arise,<sup>1</sup> though one almost always does. Here we will explore these questions in some detail, using the method of multiple scales to nd precise conditions <sup>a</sup> limit cycle to occur and to calculate its size. We will use <sup>a</sup> second order scalar equation to illustrate the situation, but the results and methods are quite general andeasy to generalize to any number of dimensions and general dynamical systems.

<sup>1</sup>Extra conditions have to be satised. For example, in the damped pendulum equation: x+x\_ +sin <sup>x</sup> <sup>=</sup> 0, there areno periodic solutions for 6=<sup>0</sup> !

| 1 | Hopf<br>bifurcation<br>for<br>second<br>order<br>scalar<br>equations. |                                                                                  |                                                                               | 3  |  |
|---|-----------------------------------------------------------------------|----------------------------------------------------------------------------------|-------------------------------------------------------------------------------|----|--|
|   | 1.1                                                                   |                                                                                  | Reduction of general phase<br>plane case<br>to<br>second<br>order<br>scalar.  | 3  |  |
|   | 1.2                                                                   |                                                                                  | Equilibrium solution and<br>linearization.                                    | 3  |  |
|   | 1.3                                                                   |                                                                                  | Assumptions on<br>the<br>linear eigenvalues needed<br>for a Hopf bifurcation. | 4  |  |
|   | 1.4                                                                   | Weakly Nonlinear things and expansion<br>of the<br>equation near<br>equilibrium. |                                                                               | 5  |  |
|   | 1.5                                                                   |                                                                                  | Explanation of the<br>idea behind<br>the<br>calculation.<br>5                 |    |  |
|   | 1.6                                                                   | Calculation of the<br>limit cycle<br>size.                                       |                                                                               | 6  |  |
|   | 1.7                                                                   | 3).<br>The<br>Two<br>Timing expansion<br>up<br>to<br>O(                          |                                                                               | 7  |  |
|   |                                                                       |                                                                                  | Calculation<br>of<br>the<br>proper<br>scaling<br>for<br>the<br>slow<br>time.  | 7  |  |
|   |                                                                       |                                                                                  | Resonances<br>occur<br>rst<br>at<br>third<br>order.<br>Non-degeneracy.        | 8  |  |
|   |                                                                       |                                                                                  | Asymptotic<br>equations<br>at<br>third<br>order.                              | 8  |  |
|   |                                                                       |                                                                                  | Supercritical<br>and<br>subcritical<br>Hopf<br>bifurcations.                  | 9  |  |
|   |                                                                       | 1.7.1                                                                            | Remark on the<br>situation at<br>the<br>critical bifurcation value.           | 9  |  |
|   |                                                                       | 1.7.2                                                                            | Remark on higher<br>orders<br>and two<br>timing validity limits               | 10 |  |
|   |                                                                       | 1.7.3                                                                            | Remark on the<br>problem when<br>the<br>nonlinearity is degenerate.           | 10 |  |

# 1 Hopf bifurcation for second order scalar equations.

## 1.1 Reduction of general phase plane case to second order scalar.

We will consider here equations of the form

$$\ddot{x} + h(\dot{x}, x, \mu) = 0, \tag{1.1}$$

where h is a smooth and  $\mu$  is a parameter.

Note 1 There is not much loss of generality in studying an equation like (1.1), as opposed to a phase plane general system. For let:

$$\dot{x} = f(x, y, \mu) \quad and \quad \dot{y} = g(x, y, \mu). \tag{1.2}$$

Then we have

$$\ddot{x} = f_x \dot{x} + f_y \dot{y} = f_x f + f_y g = F(x, y, \mu). \tag{1.3}$$

Now, from  $\dot{x} = f(x, y, \mu)$  we can, at least in principle,<sup>2</sup> write

$$y = G(\dot{x}, x, \mu). \tag{1.4}$$

Substituting then (1.4) into (1.3) we get an equation of the form (1.1).

# 1.2 Equilibrium solution and linearization.

Consider now an equilibrium solution<sup>4</sup> for (1.1), that is:

$$x = X(\mu)$$
 such that  $h(0, X, \mu) = 0$ , (1.5)

<sup>&</sup>lt;sup>2</sup>We can do this in a neighborhood of any point  $(x_*, y_*)$  (say,a critical point) such that  $f_y(x_*, y_*, \mu) \neq 0$ , as follows from the Implicit Function theorem. If  $f_y = 0$ , but  $g_x \neq 0$ , then the same ideas yield an equation of the form  $\ddot{y} + \tilde{h}(\dot{y}, y, \mu) = 0$  for some  $\tilde{h}$ . The approach will fail only if both  $f_y = g_x = 0$ . But, for a critical point this last situation implies that the eigenvalues are  $f_x$  and  $g_y$ , that is: **both real**! Since we are interested in studying the behavior of phase plane systems near a **non-degenerate** critical point switching from stable to unstable spiral behavior, this **cannot happen**.

<sup>&</sup>lt;sup>3</sup>Vice versa, if we have an equation of the form (1.1), then defining y by  $y = G(\dot{x}, x, \mu)$ , for any G such that the equation can be solved to yield  $\dot{x} = f(x, y, \mu)$  (for example:  $G = \dot{x}$ ), then  $\dot{y} = G_{\dot{x}}\ddot{x} + G_{x}\dot{x} = g(x, y)$  upon replacing  $\dot{x} = f$  and  $\ddot{x} = -h$ .

<sup>&</sup>lt;sup>4</sup>i.e.: a critical point.

so that  $x \equiv X$  is a solution for any fixed  $\mu$ . There is **no loss of generality** in assuming

$$X(\mu) \equiv 0$$
 for all values of  $\mu$ , (1.6)

since we can always change variables as follows:  $x_{\text{old}} = X(\mu) + x_{\text{new}}$ 

The linearized equation near the equilibrium solution  $x \equiv 0$  (that is, the equation for x infinitesimal) is now:

$$\ddot{x} - 2\alpha \dot{x} + \beta x = 0, \tag{1.7}$$

where  $\alpha = \alpha(\mu) = -\frac{1}{2}h_x(0, 0, \mu)$  and  $\beta = \beta(\mu) = h_x(0, 0, \mu)$ .

The critical point is a **spiral point** if  $\beta > \alpha^2$ . The eigenvalues and linearized solution are then

$$\lambda = \alpha \pm i\widetilde{\omega} \tag{1.8}$$

(where  $\widetilde{\omega} = \sqrt{\beta - \alpha^2}$ ) and

$$x = ae^{\alpha t}\cos\left(\tilde{\omega}(t - t_0)\right), \tag{1.9}$$

where a and  $t_0$  are constants.

# 1.3 Assumptions on the linear eigenvalues needed for a Hopf bi-furcation.

<u>Assume now</u>: At  $\mu = 0$  the critical point changes from a stable to an unstable spiral point (if the change occurs for some other  $\mu = \mu_c$ , one can always redefine  $\mu_{\text{old}} = \mu_c + \mu_{\text{new}}$ ). Thus

$$\alpha < 0$$
 for  $\mu < 0$  and  $\alpha > 0$  for  $\mu > 0$ , with  $\beta > 0$  for  $\mu$  small.

In fact, <u>assume</u>:

• I. 
$$h$$
 is smooth.  
• II.  $\alpha(0) = 0$ ,  $\beta(0) > 0$  and  $\frac{d}{d\mu}\alpha(0) > 0$ .<sup>5</sup> 
$$(1.10)$$

We point out that, in addition, there are some restrictions on the behavior of the nonlinear terms near the critical point that are needed for a Hopf bifurcation to occur. See equation (1.22).

<sup>&</sup>lt;sup>5</sup>This last is known as the Transversality condition. It guarantees that the eigenvalues **cross** the imaginary axis as  $\mu$  varies.

# 1.4 Weakly Nonlinear things and expansion of the equation near equilibrium.

Our objective is to study what happens near the critical point, for  $\mu$  small. Since for  $\mu = 0$  the critical point is a **linear center**, the nonlinear terms will be important in this study. Since we will be considering the **region near** the critical point, the **nonlinearity will be weak**.

Thus we will use the methods introduced in the Weakly Nonlinear Things notes.

For  $x, \dot{x}$ , and  $\mu$  small we can expand h in (1.1). This yields

$$\ddot{x} + \omega_0^2 x + \left\{ \frac{1}{2} A \dot{x}^2 + B \dot{x} x + \frac{1}{2} C x^2 \right\} + 
+ \frac{1}{6} \left\{ D \dot{x}^3 + 3 E \dot{x}^2 x + 3 F \dot{x} x^2 + G x^3 \right\} 
- 2 p^2 \dot{x} \mu + \Omega x \mu + O(\epsilon^4, \epsilon^2 \mu, \epsilon \mu^2) = 0,$$
(1.11)

where we have used that  $h(0,0,\mu) \equiv 0$  and  $\alpha(0) = 0$ . In this equation we have:

**A**. 
$$\omega_0^2 = \frac{\partial}{\partial x} h(0, 0, 0) = \beta(0) > 0$$
, with  $\omega_0 > 0$ ,

**B**. 
$$A = \frac{\partial^2}{\partial \dot{x}^2} h(0, 0, 0), \quad B = \frac{\partial^2}{\partial \dot{x} \partial x} h(0, 0, 0), \dots,$$

C. 
$$p^2 = -\frac{1}{2} \frac{\partial^2}{\partial \dot{x} \partial \mu} h(0, 0, 0) = \frac{d}{d\mu} \alpha(0) > 0$$
, with  $p > 0$ ,

**D**. 
$$\Omega = \frac{\partial^2}{\partial x \partial \mu} h(0,0,0) = \frac{d}{d\mu} \beta(0),$$

E.  $\epsilon$  is a measure of the size of  $(x, \dot{x})$ . Further: both  $\epsilon$  and  $\mu$  are small.

# 1.5 Explanation of the idea behind the calculation.

We now want to study the solutions of (1.11). The idea is, again: for  $\epsilon$  and  $\mu$  small the solutions are going to be dominated by the center in the linearized equation  $\ddot{x} + \omega_0^2 x = 0$ , with a slow drift in the amplitude and small changes to the period<sup>6</sup> caused by the higher order terms. Thus we will use an approximation for the solution like the ones in section 2.1 of the Weakly Nonlinear Things notes.

 $<sup>^6</sup>$ We will not model these period changes here. See section 2.3 of the Weakly Nonlinear Things notes for how to do so.

## 1.6 Calculation of the limit cycle size.

This is a parameter that does not appear in (1.1) or, equivalently, (1.11). In fact, the only parameter in the equation is  $\mu$  (assumed small as we are close to the bifurcation point  $\mu = 0$ ). Thus:

$$\epsilon$$
 must be related to  $\mu$ . (1.13)

In fact,  $\epsilon$  will be a measure of the size of the limit cycle, which is a property of the equation (and thus a function of  $\mu$  and not arbitrary all).

<u>However</u>: We do not know  $\epsilon$  a priori! How do we go about determining it?

The idea is: If we choose  $\epsilon$  "too small" in our scaling of  $(x, \dot{x})$ , then we will be looking "too close" to the critical point and thus will find only spiral-like behavior, with no limit cycle at all. Thus, we **must choose**  $\epsilon$  **just large enough** so that the terms involving  $\mu$  in (1.11) (specifically  $2p^2\mu\dot{x}$ , which is the leading order term in producing the stable/unstable spiral behavior) are "balanced" by the nonlinearity in such a fashion that a limit cycle is allowed. In the context of Two-Timing this means we want  $\mu$  to "kick in" the damping/amplification term  $2p^2\mu\dot{x}$  at "just the right level" in the sequence of solvability conditions the method produces. Thus, going back to (1.11), we see that

- The linear leading order terms  $\ddot{x} + \omega_0^2 x$  appear at  $O(\epsilon)$ .
- The first nonlinear terms (quadratic) appear at  $O(\epsilon^2)$ .

  However: Quadratic terms produce no resonances, since  $\sin^2 \theta = \frac{1}{2}(1 \cos 2\theta)$  and there are no sine or cosine terms. The same applies to  $\cos^2 \theta$  and to  $\sin \theta \cos \theta$ .
- Thus, the first resonances will occur when the cubic terms in x play a role ⇒ we must have the balance

$$O(x^3) = O(\mu \dot{x}), \qquad (1.14)$$

$$\Rightarrow \mu = O(\epsilon^2).$$

<sup>&</sup>lt;sup>7</sup>This is a crucial argument that must be well understood. Else things look like a bunch of miracles!

# 1.7 The Two Timing expansion up to $O(\epsilon^3)$ .

We are now ready to start. The expansion to use in (1.11) is

$$x = \epsilon x_1(\tau, T) + \epsilon^2 x_2(\tau, T) + \epsilon^3 x_3(\tau, T) + \dots, \qquad (1.15)$$

where  $0 < \epsilon \ll 1$ ,  $2\pi$ -periodicity in T is required,  $T = \omega_0 t$ ,  $\omega_0$  is as in  $(1.11)^8$ ,  $\tau$  is a slow time variable and  $\epsilon$  is related to  $\mu$  by  $\mu = \nu \epsilon^2$ , where  $\nu = \pm 1$  (which  $\nu$  we take depends on which "side" of  $\mu = 0$  we want to investigate).

<u>What exactly is  $\tau$ ?</u> Well, we need  $\tau$  to resolve resonances, which will not occur until the cubic terms kick in into the expansion  $\Rightarrow \tau = \epsilon^2 t$ . (This is exactly the same argument used to get (1.14)).

Then, with  $I' = \frac{\partial}{\partial T}$ , (1.11) becomes:

$$\omega_0^2 x'' + \omega_0^2 x + \left\{ \frac{1}{2} A \omega_0^2 (x')^2 + B \omega_0 x x' + \frac{1}{2} C x^2 \right\} + \frac{1}{6} \left\{ D \omega_0^3 (x')^3 + 3E \omega_0^2 (x')^2 x + 3F \omega_0 x' x^2 + G x^3 \right\} + 2\epsilon^2 \omega_0 x'_{\tau} - 2\epsilon^2 \nu p^2 \omega_0 x' + \epsilon^2 \nu \Omega x + O(\epsilon^4) = 0.$$

$$(1.16)$$

The rest is now a computational nightmare, but it is fairly straightforward. Without getting into any of the messy algebra, this is what will happen:

**At** 
$$O(\epsilon)$$
  $\omega_0^2 \{x_1'' + x_1\} = 0$ . Thus 
$$x_1 = a_1(\tau)e^{iT} + c.c. \tag{1.17}$$

for some complex valued function  $a_1(\tau)$ . We use complex notation, as in the Weakly Non-linear Things notes.

$$\mathbf{At} \ O(\epsilon^2) \qquad \qquad \omega_0^2 \left\{ x_2'' + x_2 \right\} + \underbrace{\left\{ \text{quadratic terms in} \quad x_1 \text{ and } x_1' \right\}}_{} = 0. \tag{1.18}$$

From the first bracket in (1.16), the quadratic terms here have the form:

$$C_1 a_1^2 e^{i2T} + C_2 |a_1^2| + C_1^* (a_1^*)^2 e^{-2iT}$$
,

where  $C_1$  and  $C_2$  are constants that can be computed in terms of  $\omega_0$ , A, B and C. Since the solution and equation are real valued,  $C_2$  is real. Here, as usual, \* indicates the complex conjugate.

<sup>&</sup>lt;sup>8</sup>Same as the linear (at  $\mu = 0$ ) frequency. No attempt is made in this expansion to include higher order nonlinear corrections to the frequency.

No resonances occur and we have

$$x_2 = \left\{ \left( a_2(\tau)e^{iT} + \frac{1}{3}\omega_0^{-2}C_1 a_1^2 e^{i2T} \right) + c.c. \right\} - \omega_0^{-2}C_2 \left| a_1^2 \right|. \tag{1.19}$$

$$\Delta t \ O(\epsilon^3) \qquad \omega_0^2 (x_3'' + x_3) + 2\omega_0 x_{1\tau}' - 2\nu p^2 \omega_0 x_1' + \nu \Omega x_1 + \mathbf{CNLT} = 0, \qquad (1.20)$$

where **CNLT** stands for **Cubic Non Linear Terms**, involving products of the form  $x_2x_1$ ,  $x'_2x_1$ ,  $x_2x'_1$ ,  $x'_2x'_1$ ,  $(x'_1)^3$ ,  $(x'_1)^2x_1$ ,  $x'_1x_1^2$  and  $x_1^3$ . These will produce a term of the form  $da_1^2a_1^*e^{iT} + c.c.$  plus other terms whose T dependencies are: 1,  $e^{\pm 2iT}$  and  $e^{\pm 3iT}$ , none of which is resonant (forces a non periodic response in  $x_3$ ). Here

d is a constant that can be computed in terms of 
$$\omega_0, A, B, C, D, E, F$$
 and G. (1.21)

This is a big and messy calculation, but it involves only sweat. In general, of course,  $\text{Im}(d) \neq 0$ . The case Im(d) = 0 is very particular, as it requires h in equation (1.1)to be just right, so that the particular combination of its derivatives at x = 0,  $\dot{x} = 0$  and  $\mu = 0$  that yields Im(d) just happens to vanish. Thus

Assume a nondegenerate case: 
$$Im(d) \neq 0$$
. (1.22)

For equation (1.20) to have solutions  $x_3$  periodic in T, the forcing terms proportional to  $e^{\pm iT}$  must vanish. This leads to the equation:

$$2\omega_0 i \frac{d}{d\tau} a_1 - 2\nu p^2 \omega_0 i a_1 + \nu \Omega a_1 + d \left| a_1^2 \right| a_1 = 0.$$
 (1.23)

Then write

 $a_1 = \rho e^{i\theta}$ , with  $\rho$  and  $\theta$  real,  $\rho > 0$ .

This yields

$$\frac{d}{d\tau}\theta = \frac{1}{2}\nu\omega_0^{-1}\Omega + \frac{1}{2}\omega_0^{-1}\operatorname{Re}(d)\rho^3$$
(1.24)

and

$$\frac{d}{d\tau}\rho = \nu p^2 (1 - \nu q \rho^2)\rho, \qquad (1.25)$$

where  $q = \frac{1}{2}\omega_0^{-1}p^{-2}\text{Im}(d)$ .

Equation(1.24) provides a correction to the phase of  $x_1$ , since  $x_1 = 2\rho \cos(T + \theta)$ . The first term on the right of (1.24) corresponds to the changes in the linear part of the phase due to  $\mu \neq 0$ , away from the phase  $T = \omega_0 t$  at  $\mu = 0$ . The second term accounts for the nonlinear effects.

The second equation (1.25) above is more interesting. First of all, it reconfirms that for  $\mu < 0$  (that is,  $\nu = -1$ ) the critical point ( $\rho = 0$ ) is a stable spiral, and that for  $\mu > 0$  (that is,  $\nu = 1$ ) it is an unstable spiral. <u>Further</u>

If 
$$\mathrm{Im}(d)>0$$
. Then a stable limit cycle exists for 
$$\mu>0\ (\mathrm{i.e.}\ \nu=1)\ \mathrm{with}\ \rho=\sqrt{2\omega_0p^2(\mathrm{Im}(d))^{-1}}\ .$$
 Supercritical (Soft) Hopf Bifurcation. 
$$(1.26)$$
 If  $\mathrm{Im}(d)<0$ . Then an unstable limit cycle exists for 
$$\mu<0\ (\mathrm{i.e.}\ \nu=-1)\ \mathrm{with}\ \rho=\sqrt{-2\omega_0p^2(\mathrm{Im}(d))^{-1}}\ .$$
 Subcritical (Hard) Hopf Bifurcation.

Notice that  $\rho$  here is equal to  $\frac{1}{2\epsilon}$  the radius of the limit cycle.

### 1.7.1 Remark on the situation at the critical bifurcation value.

Notice that, for  $\mu=0$  (critical value of the bifurcation parameter)<sup>9</sup> we can do a two timing analysis as above to verify what the nonlinear terms do to the center.<sup>10</sup> The calculations are exactly as the ones leading to equations (1.23)–(1.25), except that  $\nu=0$  and  $\epsilon$  is now a small parameter (unrelated to  $\mu$ , as  $\mu=0$  now) simply measuring the strength of the nonlinearity near the critical point. Then we get for  $\rho=\frac{1}{2\epsilon}$  radius of orbit around the critical point

$$\frac{d}{d\tau}\rho = -\frac{1}{2}\omega_0^{-1} \text{Im}(d)\rho^3 \,. \tag{1.27}$$

From this the behavior near the critical point follows.

<sup>&</sup>lt;sup>9</sup>Then the critical point is a center in the linearized regime.

<sup>&</sup>lt;sup>10</sup>This is the way one would normally go about deciding if a linear center is actually a spiral point and what stability it has.

Clearly <sup>8</sup> >>>>>>< >>>>>>: Im(d) <sup>&</sup>gt; <sup>0</sup> () Soft bifurcation () Nonlinear terms stabilize. For = 0 critical point is a stable spiral. Im(d) <sup>&</sup>lt; <sup>0</sup> () Hard bifurcation () Nonlinear terms de-stabilize. For = 0 critical point is an unstable stable spiral.

### 1.7.2 Remark on higher orders and two timing validity limits.

As pointed out in the Weakly Nonlinear Things notes, Two Timing is generally valid for some \limited" range in time, here probably <sup>j</sup> j 1 for incorporating the higher order corrections to the period the nonlinearity produces. If we are only interested in calculating the limit cycle in a Hopf bifurcation (not it's stability characteristics), we can always do so using the Poincare{Lindsteadt Method. In particular, then we can get the period to as high an order as wanted.

### 1.7.3 Remark on the problem when the nonlinearity isdegenerate.

What about the degenerate case Im(d)=0 ?

In this case there may be a limit cycle, or there may not be one. To decide the question one must look at the eects of nonlinearities higher than cubic (going beyond O( 3) in the expansion) and see ifthey stabilize or destabilize. If a limit cycle exists, then its size will not be given by <sup>q</sup> jj, but something else entirely dierent (given by the appropriate balance between nonlinearity and the linear damping/amplication produced by 6= 0 when 6= 0 in equation (1.7)). The details of the calculation needed in a case like this can be quite hairy. One must use methods like the ones in Section 2.3 of the Weakly Nonlinear Things notes because: even though the nonlinearity may require a high order before it decides the issue of stability, modications to the frequency of oscillation will occur at lower orders.11 We will not get into this sort of stu here.

<sup>11</sup>Note that Re(d) 6= 0 in (1.24) produces such <sup>a</sup> change, even if Im(d) <sup>=</sup> 0 and there are no nonlinear eects in (1.25).