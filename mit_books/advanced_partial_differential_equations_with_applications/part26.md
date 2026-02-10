| MIT OpenCourseWare |
|--------------------|
| http://ocw.mit.edu |

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

#### WeaklyNonlinear Things: Oscil lators.

Department of Mathematics

Massachusetts Institute of Technology

Cambridge, Massachusetts MA 02139

October 24, 1995

When nonlinearities are \small" there are various ways one can exploit this fact | and the fact that the linearized problem can be solved exactly1 | to produce useful approximations to the solutions.

We illustrate two of these techniques here, with examples from phaseplane analysis: The Poincare{Lindstedt method and the (more exible) Two Timing method. This second method is a particular case of the Multiple Scales approximation technique, which is useful whenever the solution of a problem involves eects that occur on very dierent scales. In the particular examples we consider, the dierent scales arise from the basic vibration frequency induced by the linear terms (fast scale) and from the (slow) scale over which the small nonlinear eects accumulate.

The material in these notes is intended to amplify the topics covered in section 7.6 and problems 7.6.13{7.6.22 of the book \Nonlinear Dynamics and Chaos" by S. Strogatz.

<sup>1</sup>Actually, one can also use these ideas when one has a nonlinear problem with known solution, and wishes to solve a slightly dierent one. But we will not talk about this here.

| 1 |           | Poincare-Lindstedt<br>Method<br>(PLM).                                                                             | 3  |
|---|-----------|--------------------------------------------------------------------------------------------------------------------|----|
|   |           | General<br>ideas<br>behind<br>the<br>method.                                                                       |    |
|   | 1.1       | Dung Equation.<br>Periodic<br>solutions<br>and<br>amplitude<br>dependence<br>of their<br>periods.                  | 3  |
|   | 1.2       | van der<br>Pol equation.<br>Calculation<br>of<br>the<br>limit<br>cycle.                                            | 6  |
| 2 | Two       | Timing,<br>Multiple<br>Scales<br>method<br>(TTMS)                                                                  |    |
|   | for       | the<br>van<br>der<br>Pol<br>equation.                                                                              | 8  |
|   | 2.1       | Calculation of the<br>limit cycle<br>and<br>stability.                                                             | 8  |
|   | 2.2       | Higher orders<br>and<br>limitations of TTMS.<br>technical.y<br>This<br>topic<br>is<br>fairly                       | 11 |
|   | 2.3       | Generalization of TTMS<br>to extend<br>the<br>range<br>of validity<br>technical.y<br>This<br>topic<br>is<br>fairly | 14 |
| A | Appendix. |                                                                                                                    | 16 |
|   | A.1       | Some details regarding section<br>1.1.                                                                             | 16 |
|   | A.2       | More<br>details regarding section 1.1<br>technical.y<br>This<br>topic<br>is<br>fairly                              | 17 |
|   | A.3       | Some details regarding section<br>1.2.                                                                             | 17 |

yThe material here is for completeness, but not actually needed to get a "basic" understanding.

# 1 Poincare-Lindstedt Method (PLM).

PLM is a technique for calculating periodic solutions. The idea is that, if the linearized equations have periodic solutionsand 0 < 1 isa measure of the size of the nonlinear terms

- I. For any nite time period t0 <sup>t</sup> t0 <sup>+</sup> Tf (Tf <sup>&</sup>gt; 0), the tra jectories for the full system will remain pretty close to those of the linearized system (errors no worse than O(Tf ), typically).
- II. On the other hand, even a small error is enough to destroy periodicity. An orbit that \closes on itself" after some time period, will generally fail to do so if slightly perturbed. Thus, typically, nonlinearity will destroy most periodic orbits the linearized system might Some, however, may survive <sup>2</sup> ! PLM is designed to pick those up.

#### if a periodic orbit of the linearized system survives:

- III. The nonlinearity will change (slightly) the shape of the orbit.
- IV. The speed of \travel" along the orbit will be aected by the nonlinearity. In particular the period will change (slightly.)

#### PLM takes care ofthese eects as follows:

- A. The solution isapproximated at leading order by the linear solution, but small correcat higher orders are introduced to take care of the (small) shape changes.
- B. The linear solution is evaluated at a stretched time, to account for the change in period.

The two examples that follow illustrate the ideas.

## 1.1 Dung Equation.

The equation can be written in the form

$$\ddot{x} + x + \epsilon \nu x^3 = 0 \,, \tag{1.1}$$

a. But for only a few values of a will periodicity \survive" the eect of the nonlinearity.

<sup>2</sup>That is, if ~u = ~u(t) is a periodic solution of the linearized system, then so is a~u, for any scalar constant

where  $0 < \epsilon \ll 1$  and  $\nu = \pm 1$ . This equation is actually a conservative system, with (conserved) energy

$$E = \frac{1}{2}\dot{x}^2 + \frac{1}{2}x^2 + \frac{1}{4}\epsilon\nu x^4 \,. \tag{1.2}$$

Thus all orbits for x bounded will be periodic.<sup>3</sup> PLM will allow us to calculate corrections to the linear period of  $2\pi$  and sinusoidal orbit shape (for the bounded orbits).

The **PLM expansion** is given by:

$$x(t) = x_0(T) + \epsilon x_1(T) + \epsilon^2 x_2(T) + \cdots,$$
 (1.3)

where  $x_j = x_j(T)$  is periodic of period  $2\pi$  in T and does not depend on  $\epsilon$ .  $T = \omega t$  is the stretched time variable, where

$$\omega = 1 + \epsilon \omega_1 + \epsilon^2 \omega_2 + \cdots, \tag{1.4}$$

is a (real, positive) constant to be computed. The **nonlinear period is then**  $2\pi/\omega$ .

**Note 1**  $x_0(T)$  will be the solution to the linearized problem, so (1.3) will reduce to the right answer when  $\epsilon = 0$ .

We now proceed as follows:

• **First:** Rewrite (1.1) in terms of the new independent variable T, replacing  $\dot{} = \frac{d}{dt}$  by  $\dot{} = \frac{d}{dT}$  via  $\dot{} = \frac{d}{dt}$  via  $\dot{} = \frac{d}{dt}$ . Thus:

$$\omega^2 x'' + x + \epsilon \,\nu \,x^3 = 0 \,. \tag{1.5}$$

• Second: Substitute (1.3) and (1.4) into (1.5) and collect equal powers<sup>4</sup> of  $\epsilon$ . Then require that the equation be satisfied at each level in  $\epsilon$ . Thus we get an equation for each order  $\epsilon^p$ , which determine higher and higher orders of approximation in the expansion (1.3), as follows:

<sup>&</sup>lt;sup>3</sup>Notice that, for  $\nu = 1$  ALL orbits are periodic. However, for  $\nu = -1$ , orbits where  $|x| > \epsilon^{-\frac{1}{2}}$  are not periodic. This follows from looking at the level curves for E in the  $(x, \dot{x})$  phase plane. Of course, when  $|x| = O(\epsilon^{-\frac{1}{2}})$ , the nonlinear term in equation (1.1) has the same size as the linear terms: the problem is no longer "weakly nonlinear". Thus, we should not be surprised if the solution exhibits behavior not close to the linearized one.

<sup>&</sup>lt;sup>4</sup>This is the **messy part.** It means you have to plug (1.3) and (1.4) into (1.5), then do all the products, etc. ... so as to end with the equation written as:  $\{\cdots\} + \epsilon \{\cdots\} + \epsilon^2 \{\cdots\} + \cdots = 0$ .

O(1) equation:

$$x_0'' + x_0 = 0. (1.6)$$

Clearly then

$$x_0 = a\cos T\,, (1.7)$$

where a is, at this stage, an arbitrary constant.<sup>5</sup>

 $O(\epsilon)$  equation:

$$x_1'' + 2\omega_1 x_0'' + x_1 + \nu x_0^3 = 0,$$
 that is

$$x_1'' + x_1 = 2\omega_1 a \cos T - \nu a^3 \cos^3 T =$$

$$= \left\{ 2\omega_1 a - \frac{3}{4}\nu a^3 \right\} \cos T - \frac{1}{4}\nu a^3 \cos 3T.$$
(1.8)

The form of equation (1.8) is typical of all the higher order equations.

Namely, we get the linear equation for the new term in x at that order —  $x_1$  here — forced by terms involving the lower orders already solved for.

The solution  $x_1$  to (1.8) will be  $2\pi$ -periodic in T only if the coefficient of the  $\cos T$  term on the right hand side (terms between the brackets) vanishes. This is because this term will produce a response in  $x_1$  proportional to  $T\sin T$ , which is **clearly** not periodic. Since we are interested in a **nontrivial solution** (that is  $a \neq 0$ ) we conclude that:

$$\omega_1 = \frac{3}{8}\nu a^2, 
x_1 = \frac{1}{32}\nu a^3 \cos 3T + A\cos T + B\sin T,$$
(1.9)

where the term marked by the brace in the second equation is the arbitrary homogeneous solution, with A and B arbitrary constants. The first equation here determines the first frequency correction, in terms of the amplitude<sup>6</sup> of the oscillations a, which remains arbitrary at this level.<sup>7</sup> We note also that the homogeneous solution in the second equation above

 $<sup>^{5}</sup>$ In fact, in this case, a will remain arbitrary. There is also a *phase shift* we could include in (1.7). But this is just a matter of where we put the time origin (see appendix A.1).

<sup>&</sup>lt;sup>6</sup>This is **typical of nonlinear oscillators:** the frequency depends on the amplitude.

<sup>&</sup>lt;sup>7</sup>That is, no restrictions have been imposed by the expansion on it. In fact, it can be shown that no restrictions on a will appear at any level of the expansion. This is because there is in fact a whole one parameter set of periodic solutions, which can be parameterized by the amplitude a.

amounts to no more than a small change in the amplitude and phase of the leading order solution. That is:

$$a\cos T \longrightarrow (a + \epsilon A)\cos T + \epsilon B\sin T = \tilde{a}\cos(T - \tilde{T})$$

for some  $\tilde{a}$  and  $\tilde{T}$ . Thus (see appendix A.1)

Without Loss of Generality: we can set 
$$A = B = 0$$
 in (1.9).

$$O(\epsilon^2)$$
 equation:

$$O(\epsilon^2)$$
 equation:  $x_2'' + 2\omega_1 x_1'' + (2\omega_2 + \omega_1^2) x_0'' + x_2 + 3\nu x_0^2 x_1 = 0,$  that is:

$$x_2'' + x_2 = \left(2\omega_2 + \omega_1^2\right) a \cos T + \frac{9}{16}\omega_1 \nu a^3 \cos 3T - \frac{3}{32}a^5 \cos^2 T \cos 3T, \qquad (1.11)$$

where  $\cos^2 T \cos 3T = \frac{1}{4} \cos T + \frac{1}{2} \cos 3T + \frac{1}{4} \cos 5T$ . Again:  $x_2$  will be periodic only if the coefficient of the  $\cos T$  forcing term on the right hand side here vanishes. This yields

$$\omega_2 = -\frac{1}{2}\omega_1^2 + \frac{3}{256}a^4 = -\frac{15}{256}a^4 \tag{1.12}$$

and an explicit formula for  $x_2$ , which we do not display here. Clearly, this **process can be** carried to any desired order (see appendix A.2).

In summary, we have found for the solutions<sup>8</sup> of the Duffing equation:

$$x \sim a \cos T + \frac{1}{32} \epsilon \nu a^3 \cos 3T + O(\epsilon^2),$$

$$T = \omega t,$$

$$\omega \sim 1 + \frac{3}{8} \epsilon \nu a^2 - \frac{15}{256} \epsilon^2 a^4 + O(\epsilon^3).$$
(1.13)

#### van der Pol equation. 1.2

The equation has the form

$$\ddot{x} - \epsilon \nu (1 - x^2) \dot{x} + x = 0, \qquad (1.14)$$

where  $0 < \epsilon \ll 1$  and  $\nu = \pm 1$ . We use now the same ideas of section 1.1, so that (1.3) and (1.4) still apply. Instead of (1.5) we get now

$$\omega^2 x'' + x - \epsilon \nu \omega (1 - x^2) x' = 0.$$
 (1.15)

<sup>&</sup>lt;sup>8</sup>Notice that this is valid only as long as  $0 \le a^2 \ll \epsilon^{-1}$ . When  $|a| = O(\epsilon^{-\frac{1}{2}})$ , the "corrections" cease to be smaller than the leading order and the expansion fails. This agrees with our observations in footnote 3.

We proceed now to look at the expansion order by order.

At O(1) we get, as before (see appendix A.3):

$$x_0 = a\cos T. (1.16)$$

 $O(\epsilon)$  equation:

$$x_1'' + 2\omega_1 x_0'' + x_1 - \nu(1 - x_0^2)x_0' = 0,$$
 that is:

$$x'' + x_1 = 2\omega_1 a \cos T - \nu a \sin T + \nu a^3 \cos^2 T \sin T$$
  
=  $2\omega_1 a \cos T + \nu a \left(\frac{1}{4}a^2 - 1\right) \sin T + \frac{1}{4}\nu a^3 \sin 3T$ . (1.17)

To get a periodic solution  $x_1$ , both the coefficients of  $\cos T$  and  $\sin T$  must vanish on the right hand side  $\Longrightarrow$  For a nontrivial solution ( $a \neq 0$ ) we must have<sup>9</sup>:

$$a = 2$$
,  $\omega_1 = 0$  and  $x_1 = -\frac{1}{32}\nu a^3 \sin 3T + A \cos T + B \sin T$ . (1.18)

Note 2 There is an important difference here with the situation in the analog equations (1.8) and (1.9). Now both sines and cosines appear on the right hand side of equation (1.17). Thus we end up with TWO conditions that must be satisfied if equation (1.17) is to have a periodic solution for  $x_1$ . These conditions are generally called Solvability Conditions. Thus now BOTH a and  $\omega_1$  are determined. There is NO FREE PARAMETER left and there is just one periodic orbit: the LIMIT CYCLE.

Since now a is fixed to be a = 2, we can no longer argue that by a slight change in the amplitude and phase of  $x_0$ , we can set A = B = 0 (homogeneous part of the solution, marked by the brace above), as we did in (1.10). It is still true, however, that the phase of the leading order  $x_0$  can be changed slightly. We can then use this to conclude (see appendix A.3)

Without Loss of Generality: we can set 
$$B = 0$$
 in  $(1.18)$ .  $(1.19)$ 

On the other hand, we point out that A remains to be determined. That is, the circular part of the limit cycle orbit does not have a radius exactly equal to 2, but rather equal to  $2 + \epsilon A + \dots$ 

<sup>&</sup>lt;sup>9</sup>We could take a=-2 also. This, however, is just a phase change  $T\to T+\pi$ . Thus, we may as well assume a>0.

At the **next order** (that is,  $O(\epsilon^2)$ ) we will get an equation of the form:

$$x_2'' + x_2 = \text{Forcing}. \tag{1.20}$$

Again (see note 3) sine and cosine forcing terms on the right will have to be eliminated. This will produce two conditions, that will determine both A and  $\omega_2$  uniquely. In  $x_2$  and homogeneous term of the form  $\alpha \cos T$  will appear, with  $\alpha$  and  $\omega_3$  determined at  $O(\epsilon^3)$ . And so on to higher and higher orders.

**Note 3** In fact, after some calculation — using (1.16), (1.18) and (1.19) — we can see that (1.20) is:

$$x_2'' + x_2 = \left(2\omega_2 + \frac{1}{128}a^4\right)a\cos T + \left(\frac{3}{4}a^2 - 1\right)\nu A\sin T - \frac{3}{64}a^3\left(2 - a^2\right)\cos 3T + \frac{3}{4}\nu Aa^2\sin 3T + \frac{5}{128}a^5\cos 5T.$$
(1.22)

Thus we conclude

$$\omega_2 = -\frac{1}{256}a^4$$
,  $A = 0$  and  $x_2 = \alpha \cos T + \frac{3}{512}a^3(2 - a^2)\cos 3T - \frac{5}{3072}a^5\cos 5T$ , (1.23)

where we recall that a = 2.

# 2 Two Timing, Multiple Scales method (TTMS) for the van der Pol equation.

# 2.1 Calculation of the limit cycle and stability.

In section 1.1 we basically obtained **all the solutions** to the Duffing equation (1.1) — since we ended up with two free parameters: the amplitude a and an arbitrary phase shift  $T \to T - T_0$ . On the other hand, in section 1.2 we only obtained the limit cycle solution. Now, suppose we want all the solutions to the van der Pol equation (1.14) — this will

<sup>&</sup>lt;sup>10</sup>With a " $\beta sinT$ " homogeneous part of the solution eliminated just as above in (1.19)

allow us to determine, in particular, the stability of the limit cycle. The method we introduce in this section (TTMS) will allow us to do this.

The main idea is that, if the solution is not periodic, then we cannot represent it with a single solution of the linearized equation (as we did in section 1, with its time dependence stretched by  $\omega$  from t to  $T = \omega t$  — to allow for nonlinear corrections to the period.<sup>11</sup>) For any "short" time period this will be O.K., but over long periods large errors may result because they accumulate. To resolve this difficulty we will allow ALL the parameters of the linear solution to change SLOWLY in time, so as to track the true evolution of the solution. Thus, for equation (1.14), we expand <sup>12</sup>:

$$x \sim x_0(\tau, t) + \epsilon x_1(\tau, t) + \epsilon^2 x_2(\tau, t) + \cdots,$$
 (2.1)

where t takes care of the "normal"  $2\pi$ -periodic dependence induced by the linear solution and  $\tau = \epsilon t$  is the *slow time* (that will allow the linear solution being used to drift (slowly) as time evolves, from one linear orbit to the next.<sup>13</sup>)

Remark 1 Note that now the solution depends explicitly on two times, thus the name for the method. In this case the "slow" time is  $\tau = \epsilon t$ , but in other problems it may be  $\tau = \epsilon^2 t$  — or something else. Figuring out what the exact dependence should be need not be trivial and usually requires some thinking: it is related to the rate at which the nonlinearity causes drift in the orbits — as opposed to just shape changes. We will talk about this later.

We now rewrite equation (1.14) in terms of the increased set of "independent" variables  $\tau$  and t to obtain (here a dot indicates differentiation with respect to t):

$$\ddot{x} + 2\epsilon \dot{x}_{\tau} + \epsilon^2 x_{\tau\tau} + x - \epsilon \nu (1 - x^2) \dot{x} - \epsilon^2 \nu (1 - x^2) x_{\tau} = 0.$$
 (2.2)

Note that the equation is now a P. D. E. ! This method appears to complicate things! However, the extra terms are multiplied by  $\epsilon$  and  $\epsilon^2$  and so at leading order we only get the linear O. D. E. In fact: we will only have to solve linear O. D. E.'s at each order in the approximation!

<sup>&</sup>lt;sup>11</sup>Namely: the orbits in phase space are quite close to the linear ones, but the speed at which they are tracked is slightly different  $\Longrightarrow$  Over long times a big error will accumulate, unless we correct for it.

<sup>&</sup>lt;sup>12</sup>This is only a first, very simple, implementation. We will introduce a more refined one in section 2.3.

<sup>&</sup>lt;sup>13</sup>This description, strictly, only applies to  $x_0$  above. The higher order terms  $\epsilon x_1$  ... are there to account for the fact that the nonlinear orbits will have slightly different shapes than the linear ones.

As usual, we now substitute the expansion (2.1) into equation (2.2) and collect equal powers of  $\epsilon$  to obtain

## O(1) equation:

$$x_0'' + x_0 = 0. (2.3)$$

This is the same as in section 1.2, except that now the arbitrary "constants" in the solution of (2.3) will depend on  $\tau$ . We thus have

$$x_0 = A_0(\tau)e^{it} + c.c. \,, \tag{2.4}$$

where c.c. denotes complex conjugate and  $A_0$  is complex valued.

**Remark 2** Alternatively, we could write  $x_0 = a(\tau)\cos t + b(\tau)\sin t$ , where  $A = \frac{1}{2}(a-ib)$ . We cannot now argue, as we did before, that it is O.K. to set b = 0 using the fact that a change of time origin  $t \to t + t_0$  is allowed. This is because  $t_0$  has to be constant, while setting an arbitrary  $b(\tau)$  to zero would require  $t_0 = t_0(\tau)$ , at least in principle.<sup>14</sup>

**Remark 3** The use of complex notation in (2.4) makes life simpler. The kind of expansions we are doing require at each level of approximation that one expand things like  $x_0^3$  in Fourier modes. This is much easier to do with exponentials than with sine and cosines!

# At $O(\epsilon)$ we obtain:

$$\ddot{x}_1 + x_1 = -2\dot{x}_{0\tau} + \nu(1 - x_0^2)\dot{x}_0 
= \left\{ -2i\left(\frac{d}{d\tau}A_0 - \frac{1}{2}\nu A_0\left(1 - |A_0|^2\right)\right)e^{it} - i\nu A_0^3 e^{3it} \right\} + c.c..$$
(2.5)

This equation is very similar to (1.17), except that now: (i) We are using complex notation, (ii) There is no  $\omega_1$  term and (iii) A new term in  $\frac{d}{d\tau}A_0$  appears because of the allowed  $\tau$  dependence. The solution  $x_1$  will be periodic in t provided the coefficient of the  $e^{it}$  forcing on the right hand side of (2.5) vanishes. This yields the equation

$$\frac{d}{d\tau}A_0 = \frac{1}{2}\nu \left(1 - |A_0|^2\right)A_0,\tag{2.6}$$

<sup>&</sup>lt;sup>14</sup>Actually, an argument to set b = 0 can be made, namely: we expect the solutions of equation (1.14) to be basically oscillatory. Thus, they will have maximums and minimums. If we set t = 0 to occur at a local maximum, then  $\dot{x} = 0$  at t = 0, which yields b = 0. But this argument will not work at higher orders.

which governs the evolution<sup>15</sup> of the amplitude  $A_0$  for the linear (circular) orbits under the effect of the weak nonlinearity.

If we let  $A_0 = \frac{1}{2}ae^{i\varphi}$ , where a and  $\varphi$  are a real amplitude and phase, respectively, then<sup>16</sup>

$$\frac{d}{d\tau}\varphi = 0 \quad \text{and} \quad \frac{d}{d\tau}a = \frac{1}{8}\nu(4 - a^2)a. \tag{2.7}$$

These formulas show that the orbits in the phase plane are nearly circular, with a slowly changing radius a that evolves following the second equation in (2.7) and a limit cycle for a = 2. In particular:

For 
$$\nu = 1$$
 the limit cycle is stable and it is unstable for  $\nu = -1$ . (2.8)

If we let  $\mu = \epsilon \nu$  in (1.14) and write the equation as

$$\ddot{x} - \mu(1 - x^2)\dot{x} + x = 0, \tag{2.9}$$

then we see that our calculations here show that at  $\mu = 0$  we have a **bifurcation**, with an exchange of stability between the limit cycle and the critical point at the origin.

$$\mu < 0$$
. Unstable limit cycle and stable spiral point. 
$$\mu > 0$$
. Stable limit cycle and unstable spiral point. 
$$\mu = 0$$
. Center with continuoum of periodic orbits. (There is no limit cycle.)

# 2.2 Higher orders and limitations of TTMS.

We us now finish the  $O(\epsilon)$  calculation and solve equation (2.5) using (2.6). We have

$$x_1 = \left\{ \frac{1}{8} i \nu A_0^3 e^{3it} + A_1(\tau) e^{it} \right\} + c.c., \qquad (2.11)$$

where  $A_1$  is complex valued.

Let us now continue the expansion to one more order, as there is an **important detail to** be learned from doing this.

<sup>&</sup>lt;sup>15</sup>Drift in phase space

<sup>&</sup>lt;sup>16</sup>Since this shows that  $\varphi$  is a constant, we could have taken b=0 in remark 2!

# The $O(\epsilon^2)$ equation is:

$$\ddot{x}_{2} + x_{2} = -2\dot{x}_{1\tau} - x_{0\tau\tau} + \nu\dot{x}_{1} + \nu x_{0\tau} - \nu x_{0}^{2}\dot{x}_{1} - 2\nu x_{0}x_{1}\dot{x}_{0} - \nu x_{0}^{2}x_{0\tau} 
= \left\{ -2i\left(A'_{1} - \frac{1}{2}\nu A_{1} + \nu |A_{0}^{2}| A_{1} + \frac{1}{2}\nu A_{0}^{2}A_{1}^{*} + \frac{1}{2}i\nu A'_{0} - \frac{1}{2}iA''_{0} \right. 
\left. -\frac{1}{2}i\nu\left(|A_{0}^{2}| A_{0}\right)' + \frac{1}{16}i|A_{0}^{4}|A_{0}\right)e^{it} + (\ldots)e^{3it} + (\ldots)e^{5it}\right\} + c.c.,$$
(2.12)

where  $\frac{d}{d\tau}$  and  $A_1^*$  denotes the complex conjugate of  $A_1$ . Thus, to avoid secular terms in  $x_2$  (namely: terms proportional to  $te^{it}$ , that destroy the periodicity in t) the coefficient of  $e^{it}$  on the right hand side of this last equation must vanish. Thus

$$A_{1}^{\prime} - \frac{1}{2}\nu A_{1} + \nu \left| A_{0}^{2} \right| A_{1} + \frac{1}{2}\nu A_{0}^{2} A_{1}^{*} = -\frac{1}{2}i\nu A_{0}^{\prime} + \frac{1}{2}iA_{0}^{\prime\prime} + \frac{1}{2}i\nu \left( \left| A_{0}^{2} \right| A_{0} \right)^{\prime} - \frac{1}{16}i \left| A_{0}^{4} \right| A_{0}. \quad (2.13)$$

This is a rather messy equation. We do not aim to solve it here; but only to analyze its behavior for  $\tau$  large.

Assume  $\nu = 1$ : In this case the limit cycle is stable and, for  $\tau$  large — see equation (2.7) —  $A_0 \sim e^{i\varphi}$ , for some constant  $\varphi$ . Then equation (2.13) reduces to

$$A_1' + \frac{1}{2}A_1 + \frac{1}{2}e^{2i\varphi}A_1^* = -\frac{1}{16}ie^{i\varphi}. \tag{2.14}$$

This is much simpler and can be solved explicitly 17

$$A_1 = \left(C_1 e^{-\tau} + iC_2 - \frac{1}{16} i\tau\right) e^{i\varphi}, \qquad (2.15)$$

where  $C_1$  and  $C_2$  are real constants. This means that the solution of equation (2.13) will behave, for large  $\tau$ , like

$$A_1 \sim -\frac{1}{16} i \tau e^{i\varphi} \,. \tag{2.16}$$

**This is "bad".** Notice that the expansion (2.1) for the solution of (1.14) — use equations (2.4) and (2.11) — is

$$x \sim 2 \operatorname{Re} \left( A_0(\tau) e^{i\tau} \right) - \frac{1}{4} \epsilon \operatorname{Im} \left( A_0^3(\tau) e^{3it} \right) + 2 \epsilon \operatorname{Re} \left( A_1(\tau) e^{it} \right) + \cdots$$

But, when  $\epsilon \tau = O(1)$  the second term in the expansion will not be small at all (as  $\epsilon A_1 \sim -\frac{1}{16}i\epsilon \tau e^{i\varphi}$ )! Thus

The two timing expansion (2.1) is only valid as long as 
$$|\tau| \ll \epsilon^{-1}$$
. (2.17)

Then  $z' + \operatorname{Re}(z) = -\frac{1}{16}i$ 

This is **pretty typical for TTMS expansions:** Usually they are valid for a time range where the "slow" time can be taken large — but not arbitrary large. Beyond some  $e^{-p}$ , for some  $e^{-p}$ , they fail.

In the current situation (2.17) is not terribly upsetting. It still allows us to take  $\tau$  fairly large. Once  $\tau$  is large and the limit cycle is reached  $\Longrightarrow$  can switch to the expansion in section 1.2!!

**However**: suppose that (2.17) makes us terribly unhappy, for whatever reasons. Then

The answer to this question is YES, but first we must understand why (2.17) occurs! This is clarified next; for simplicity we CONSIDER ONLY the STABLE LIMIT CYCLE case, when  $\nu = 1$ .

**Note 4** Equations (2.1)-(2.7) lead to an approximation of the limit cycle (for large  $\tau$ , so that  $A_0 \sim e^{i\varphi}$ ) given by

$$x \sim 2 \operatorname{Re}(e^{i(t+\varphi)}) = 2 \cos(t+\varphi). \tag{2.19}$$

On the other hand, the PLM calculation of section 1.2 tells us that we should use

$$x \sim 2 \cos(\omega t + \varphi) = 2 \operatorname{Re}(e^{i(\omega t + \varphi)})$$

where  $\omega = 1 - \frac{1}{16}\epsilon^2 + \cdots$ . Now, since (expand in Taylor series)

$$e^{i(\omega t + \varphi)} = e^{i(t+\varphi)}e^{-i\frac{1}{16}\epsilon^2t + \dots} = e^{i(t+\varphi)} - \frac{1}{16}i\epsilon^2te^{i(t+\varphi)} + \dots, \qquad (2.20)$$

we see that the error in (2.19) is  $-\frac{1}{16}i\epsilon^2 t e^{i(t+\varphi)} + \cdots$ , which is precisely the "bad" behavior arising in  $A_1$  earlier in equation (2.16). Thus

The TTMS expansion goes bad because it does not properly take into account the fact that the nonlinearity affects the phase — i.e. the position along the linear orbit of the solution. (2.21)

• It follows that, to achieve (2.18) we must fix the problem pointed out by (2.21). THIS WE DO NEXT.

## 2.3 Generalization of TTMS to extend the range of validity.

Let  $\phi$  be the *phase* of the solution — namely: its position along the orbit — and  $\omega = \frac{d}{dt}\phi$  its angular velocity. The phase increases with time and, for the linearized equation, we have

$$\frac{d}{dt}\phi = \omega = 1. (2.22)$$

However, once **nonlinear effects** kick in, **there is no reason for**  $\omega$  to remain equal to 1, or in fact even constant!

Now, when considering a **periodic orbit**, as long as  $\omega$  is approximated by its correct average value things will be O.K. (as then errors will not accumulate over time). This is what **PLM does**, by taking  $\phi = T = \omega t$  with  $\omega = 1 + \epsilon \omega_1 + \cdots$ . We **cannot use this idea of PLM in TTMS**, because now the orbit (thus the average value of  $\omega$ ) varies slowly as time changes. We **must then allow**  $\omega$  **to be a function of**  $\tau$ . Thus

To fix the type of problem discussed in the previous section 2.2 we must replace the expansion (2.1) by a subtler type, where the phase (fast time) itself is to be determined. Generally we must deal then with expansions of the form

$$x \sim X_0(\tau, \phi) + \epsilon X_1(\tau, \phi) + \epsilon^2 X_2(\tau, \phi) + \cdots, \qquad (2.23)$$

where  $2\pi$ -periodic dependence on the phase  $\phi$  is required,  $\tau = \epsilon t$  and

$$\frac{d}{dt}\phi = \omega = 1 + \epsilon \,\omega_1(\tau) + \epsilon^2 \,\omega_2(\tau) + \cdots.$$

This amounts to writing:  $\phi = \frac{1}{\epsilon} (\tau + \epsilon \phi_1(\tau) + \epsilon^2 \phi_2(\tau) + \cdots)$ , where  $\frac{d}{d\tau} \phi_j = \omega_j$ 

When no  $\tau$  dependence is allowed, this reduces to PLM. We will not carry out the details of this expansion here — they are quite messy and some technicalities are involved in selecting the  $\omega_j$ 's so that the  $X_j$ 's behave "properly" as functions of  $\tau$  (that is, no secular growth in  $\tau$  occurs). On the other hand, in the particular case of the van der Pol equation (1.14), when the limit cycle is stable<sup>18</sup>: all solutions eventually approach the limit cycle, and they do so on time scales where  $\tau \ll \epsilon^{-1}$  (as follows from our results in section 1.2). Thus, as long as no cumulative errors occur in tracking the limit cycle, there should be no problems. We can conclude thus, without doing any calculations, that:

<sup>&</sup>lt;sup>18</sup>That is,  $\nu = 1$ .

For equation (1.14), in the case  $\nu = 1$ :

- The  $\omega_j$ 's in equation (2.23) are constant and equal to the values calculated for the expansion in section 1.2.
- The functional form of  $X_0(\tau, \phi)$  in equation (2.23) is the same as that we obtained for  $x_0(\tau, t)$  in equation (2.1), with t replaced by  $\phi$ . That is:  $X_0(\tau, \phi) = x_0(\tau, \phi)$ .

In particular, note that from this we learn that the TTMS approximation for the behavior of the van der Pol equation is quite good. The secular growth displayed by  $A_1$  in equation (2.16) for very long times is nothing to worry about. It is simply a manifestation of the fact that we have some small (very small,  $O(\epsilon^2)$ ) errors on the velocity at which the solution moves along the limit cycle, but of nothing else. No important qualitative or quantitative effect is missing.

Note 5 Other ways to fix the problem in (2.17) can be devised. For example, some people advocate introducing ever slower time scales, such as  $\epsilon^2 t$ ,  $\epsilon^3 t$  and so on — in addition to the  $\epsilon t$  of equation (2.1). This is not a good idea, unless the problem truly depends on that many scales! For example: if the difficulty arises because the true slow time dependence<sup>19</sup> is on something like (say)  $\frac{\epsilon}{1+\epsilon^2}t$  and not  $\epsilon t$ , then this "lots of scales" approach will just complicate things for no real gain at all. For an expansion to be useful, it has to zero into the real behavior of the solution. The aim of doing an asymptotic expansion should be to learn something useful about the solution, not to produce a massive amount of algebra (even if this is, sometimes, an unfortunate byproduct, it is not the aim). In particular, producing an "approximation" that fools us into believing that the solution depends on very many different time scales (when in fact it does not), is exactly opposite to this objective.

<sup>&</sup>lt;sup>19</sup>Notice that the van der Pol equation is exactly an example of this type.

# A Appendix.

## A.1 Some details regarding section 1.1.

Generally, asymptotic expansions | like the ones in these notes | require at each level the solution of a linear equation with some forcing made up from the prior terms. The solution of this linear equation is then required to satisfy some condition (periodicity in the examples here) and this imposes restrictions on the forcing terms. These restrictions are then used to determine free parameters, slow time evolutions, etc.

When solving the linear equations in the expansion, it is very important to include in the solution ALL thefree parameters consistent with the conditions imposed on the solution. This is because parameters that are \arbitrary" at some level, may later be needed to satisfy the restrictions at a higher order.20 Failure to include a particular parameter | which boils down to setting it to some arbitrary xed value | will typically cause trouble at higher order, when a restriction on a forcing term will be found impossible to satisfy.

On the other hand, practical considerations dictate that we carry as few free parameters in a calculation as feasible. Thus, one must always look at the equations involved and ask if there is some argument that would allow for the elimination of a parameter | but never must one eliminate a parameter without a good reason.21

Consider now equation (1.1) | or (1.5). This equation is invariant under time translation: if x = X(t) is a solution, then so it is x = X(t t0). Thus, we can always pick the origin of the time coordinate to simplify the solution and eliminate parameters.

For example: The general solution of (1.6) is: <sup>a</sup> cos(T T0), where <sup>a</sup> and T0 are constants. But the invariance under time translation shows that we can set T0 = 0.

Furthermore: At the level of (1.9) we know that in fact a is arbitrary. Then, since A and <sup>B</sup> in (1.9) amount to making small O() changes to <sup>a</sup> and T0 at the O(1) level | thus they are not true \new" free parameters | we can again set A = B = 0, as in (1.10), without any fear.

<sup>20</sup>For example, in section 1.2, the amplitude a in (1.16) is eventually set to a = 2 in (1.18).

<sup>21</sup>Conversely: if an expansion fails at some level, one should always check to see if somehow an important degree of freedom (some parameter) was ignored!

In fact, the same argument shows that we can conclude:

At any level 
$$O(\epsilon^n)$$
 in the expansion, for  $n > 1$ , we can take  $x_n$  in (1.3) with **NO**  $\cos T$  or  $\sin T$  components. (A.1)

## A.2 More details regarding section 1.1.

It is clear that, in the expansion of section 1.1, the  $O(\epsilon^n)$  equations — for n > 1 — have the form

$$x_n'' + x_n = P_n(x_0, \dots, x_{n-1}) - \sum_{\ell=1}^n \alpha_\ell x_{n-\ell}'',$$
 (A.2)

where  $P_n$  is a cubic polynomial and the  $\alpha_\ell$ 's are constants defined by  $\omega^2 = \sum_{\ell=0}^{\infty} \alpha_\ell \epsilon^\ell$ . Thus  $\alpha_0 = 1$ ,  $\alpha_1 = 2\omega_1$ ,  $\alpha_2 = 2\omega_2 + \omega_1^2$ ,  $\alpha_3 = 2\omega_3 + 2\omega_1\omega_2$ , .... In general we can see that  $\alpha_n = 2\omega_n + f_n(\omega_1, \ldots, \omega_{n-1})$ , where  $f_n$  is a quadratic polynomial.

Because  $x_0$  is even, the forcing on the right hand side of (1.8) is also even. Then (1.10) gives  $x_1$  even. The same type of argument shows then that  $x_2$  is also even. More generally, one can show using (A.1) that all the  $x_n$ 's are even.

Now, the condition on (A.2) to get  $x_n$  periodic in T is that the right hand side should not have any forcing proportional to either  $\sin T$  or  $\cos T$ . But the right hand side is even, thus there is  $\mathbf{NO}$  sin T forcing ever. On the other hand, the coefficient of the  $\cos T$  forcing has the form:  $2a\omega_n + G_n(a, \omega_1, \ldots, \omega_{n-1})$ , where  $G_n$  is some polynomial function. Thus, one can always choose  $\omega_n$  so as to make the coefficient of  $\cos T$  vanish. We have thus shown that

The expansion in equation 
$$(1.3)$$
 works up to any order.  $(A.3)$ 

# A.3 Some details regarding section 1.2.

Equation (1.14) is invariant under time translation. Thus, just as we did in appendix A.1, we have a phase to play with and can use to eliminate parameters.

We used this fact in (1.16) to eliminate the sine component in  $x_0(T)$ . But now a is no longer a free parameter in the solution, as equation (1.18) shows that a = 2. Thus, in order to eliminate spurious parameters in  $x_1(T)$  (from the two – A and B – that appear in (1.18)), we only have a phase to play with.

Since 2 cos(T <sup>1</sup> <sup>2</sup> B) = 2 cos <sup>T</sup> +B sinT +:::, it follows that a small phase change can be used to eliminate B in x1(T ) as given in (1.18). But A cannot and should not be eliminated from the formula. In fact, at O( 2) the solvability requirement on the equations (periodicity of x2(T )) will determine A in the same fashion that a = 2 followed from the O() equation. At this level it will be possible to argue that no term in sin T is needed in x2(T ), but a term cos T must be kept (with determined atO( 3)). Clearly the same pattern willbe repeated over and over. In this fashion the expansion can be continued to any desired