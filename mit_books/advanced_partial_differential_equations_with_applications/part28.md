18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

# Weakly Nonlinear Expansions for Breathers.

Rodolfo R. Rosales, Department of Mathematics,

Massachusetts Inst. of Technology, Cambridge, Massachusetts, MA 02139

October 10, 2003

#### Abstract

Solitary waves are localized traveling steady profile solutions for dispersive nonlinear dynamical systems — usually modeled by a pde, or a system of pde's. Thus, at least in 1+1 dimensions, they are relatively easy to characterize analytically — since they correspond to solutions of the ode's to which the pde's reduce in a coordinate moving with the wave.

Breathers are also localized traveling waves, but their profile is not steady, but changes periodically in time. A possible mathematical definition of what, exactly, a breather is could go as follows: It is a localized solution of the equations such that, in an appropriately selected moving coordinate frame, the solution is periodic in time. This definition does not capture all the features of the available known exact breather solutions. For these examples, in a coordinate system moving with the wave, the wave profile is itself a moving periodic steady traveling wave, contained within an amplitude envelope that keeps it localized in space. Thus, these breathers are wave-package solutions, with a localized envelope that is itself a traveling steady profile. Unfortunately, the notions of wave-package, and envelope, are not ones for which precise, and sufficiently general, definitions can be provided — at least not for fully non-linear systems.

Breathers are hard to characterize analytically, even in 1+1 dimensions, since they are solutions for which the governing pde's cannot be reduced to a lower order system. In these notes we show how to produce expansions for breather solutions, in the weakly nonlinear limit, where the breathers are of small amplitude. In this limit one can look for breathers with very "shallow" envelopes, in which case separation of scales allows a reduction of the governing equations to a lower order system.

### Contents

| 1 | The<br>Sine<br>Gordon<br>Equation.                    | 3 |
|---|-------------------------------------------------------|---|
|   | Lorentz<br>invariance.                                | 3 |
|   | Limit<br>on<br>the<br>signal<br>propagation<br>speed. | 3 |

| Rosales | Breathers.<br>Weakly<br>Nonlinear<br>Expansions<br>for                                                   | 2  |
|---------|----------------------------------------------------------------------------------------------------------|----|
| 1.1     | Kink<br>and<br>anti-kink<br>solutions.                                                                   | 3  |
|         | PROBLEM<br>1:<br>Write<br>pseudo-spectral<br>code.<br>Do<br>kinks<br>&<br>anti-kinks<br>interacting.     | 4  |
|         | Hint:<br>Description<br>of<br>pseudo-spectral<br>code.                                                   | 4  |
|         | How<br>to<br>compute<br>spectral<br>derivatives<br>for<br>a<br>mod-2ω<br>periodic<br>function.           | 4  |
|         | Kink<br>asymptotic<br>behavior<br>as<br>x<br>� ±∼.                                                       | 4  |
|         | Kinks<br>direct<br>relation<br>to<br>linearized<br>(real)<br>decaying<br>exponential<br>solutions.       | 5  |
|         | 1.2	 Breather<br>solutions.                                                                              | 5  |
|         | Breathers<br>parameterized<br>by<br>envelope<br>speed<br>and<br>amplitude.                               | 5  |
|         | Breather<br>envelope<br>and<br>phase<br>properties.                                                      | 6  |
|         | Breathers<br>parameterized<br>by<br>the<br>wave-number<br>of<br>the<br>linearization<br>at<br>∼.         | 6  |
|         | Parameter<br>expansions<br>when<br>the<br>envelope<br>decays<br>slowly.                                  | 7  |
|         | Breather<br>asymptotic<br>behavior<br>as<br>x<br>� ±∼.                                                   | 7  |
|         | Breather<br>direct<br>relation<br>to<br>linearized<br>(complex)<br>decaying<br>exponential<br>solutions. | 7  |
|         | PROBLEM<br>2:<br>Compute<br>breather,<br>kink<br>and<br>anti-kink<br>interactions.                       | 8  |
| 2       | Breather<br>Expansion.                                                                                   | 8  |
|         | Nonlinear<br>Klein-Gordon<br>equation<br>in<br>1+1<br>dimensions.                                        | 8  |
|         | Lorentz<br>invariance<br>and<br>maximum<br>signal<br>propagation<br>speed.                               | 8  |
|         | Relate<br>breather<br>to<br>linearized<br>exponential<br>solutions.                                      | 9  |
|         | Use<br>Lorentz<br>invariance<br>to<br>simplify<br>the<br>problem.                                        | 9  |
|         | Perturbation<br>equations<br>to<br>be<br>solved.                                                         | 9  |
|         | Fredholm<br>alternative.                                                                                 | 9  |
|         | Expansion<br>in<br>powers<br>of<br>the<br>small<br>parameter.                                            | 9  |
|         | Condition<br>for<br>the<br>existence<br>of<br>a<br>breather.                                             | 10 |
|         | Approximate<br>expression<br>for<br>the<br>breather<br>solution.                                         | 10 |
|         | Questions<br>regarding<br>the<br>validity<br>of<br>the<br>expansion.                                     | 10 |
|         | Computing<br>breathers<br>numerically.<br>Bifurcation<br>approach.                                       | 11 |
|         | PROBLEM<br>3:<br>Breathers<br>for<br>KdV-type<br>equations.                                              | 12 |
|         | Hint:<br>for<br>problem<br>3.                                                                            | 12 |

### 1 The Sine Gordon Equation.

Here we give examples of solitary waves and breathers. These for the **Sine-Gordon equation**, where exact analytical expressions are known. The Sine-Gordon equation is given by

$$u_{tt} - u_{xx} + \sin u = 0, (1.1)$$

where u is an angle. In another set of notes (actually, a series of problems) we show how this equation can be used to model a torsion-coupled chain of pendulums, where u is the angle of the pendulum at position x, as a function of t. But the equation shows up in very many other contexts — although the chain of pendulums is the one for which intuition helps the most in understanding and interpreting the behaviors that occur.

Remark 1 Equation (1.1) is Lorentz invariant. Namely: if u = U(x,t) is a solution of the equation, then  $u = U\left(\frac{x-ct}{\sqrt{1-c^2}}, \frac{t-cx}{\sqrt{1-c^2}}\right)$  is also a solution, for any 1 < c < 1. The equation also satisfies the relativistic principle: No information can travel faster than the speed of light t = 1 which follows because the equation is hyperbolic, with characteristic speeds t = 1.

#### 1.1 Kink and anti-kink solutions.

For equation (1.1), u and  $u + 2n\pi$  are equivalent — since u is an angle. The solitary waves (called kinks and anti-kinks in this case) connect  $u = 2n\pi$  at  $x = -\infty$  with  $u = 2 (n \pm 1) \pi$  at  $x = +\infty$  — where n is an integer. They correspond to the chain of pendulums going through a full  $2\pi$  twist as x goes from  $-\infty$  to  $+\infty$  — either clock-wise or counter-clock-wise — from rest position to rest position. This rotation wave propagates through the chain as a deformation of permanent shape, where the speed of propagation is a function of how "tight" the twist is.<sup>1</sup> These waves can be written explicitly (they are traveling waves, so the equation reduces to an ode, which can be solved). The **kinks**, which correspond to a counterclockwise twist, are given by:

$$u = 2n\pi - 4\arctan\left(e^{Az}\right),\tag{1.2}$$

<sup>&</sup>lt;sup>1</sup>In the actual mechanical model, you can generate one by taking one of the end pendulums, and rotating it by a full turn. How fast you do this will determine the velocity of the wave so produced.

where -1 < c < 1 is the (constant) speed of the kink,  $z = (x - ct - x_0)$  is a moving coordinate (the kink position is given by  $x = ct + x_0$ ) and  $A = 1/\sqrt{1 - c^2}$ . The **anti-kinks**, on the other hand, are given by:

$$u = 2n\pi + 4\arctan\left(e^{Az}\right),\tag{1.3}$$

Check that these are solutions, by observing that both satisfy  $u_t = cu_x$  and  $u_x = (-1)^n 2A \sin(u/2)$ .

**Problem 1** Kinks and anti-kinks are very non-linear solutions, and it is interesting to study how they interact with each other. Write a pseudo-spectral code to solve equation (1.1), and start it with initial conditions corresponding to two kinks, or two anti-kinks, or a kink and an anti-kink, set-up so they will eventually collide<sup>2</sup> — see the statement for problem 2. Then see what happens. Note that the resolution needed for this is not large: 128 points in space should be enough.

**Hint 1** FFT spectral schemes work with solutions **PERIODIC** in space — **NOT** "mod- $2\pi$ " periodic, as the Sine-Gordon equation requires (since u is an angle). To do the numerical experiments in problem 1, you need to get around this problem. To get an appropriate spectral method:

First write the equation as:

$$u_t = v \quad and \quad v_t = u_{xx} - \sin u. \tag{1.4}$$

Next discretize space with a uniform grid, and evaluate the right hand side using FFT's to calculate derivatives. This reduces the pde to an ode (in the array of values for u and v at each node in the space grid). Finally, solve this ode using a standard ode solver — e.g. ode45 in MatLab. But, for this to work, you need to evaluate the derivative  $u_{xx}$  in a way that uses functions periodic in x only — else you cannot use FFT's. Here is one way to do so: Let  $U = e^{iu}$ . Then

$$u_{xx} = -i\left(\frac{UU_{xx} - (U_x)^2}{U^2}\right) = \operatorname{imag}\left(\frac{UU_{xx} - (U_x)^2}{U^2}\right),$$
 (1.5)

gives an appropriate formula involving only the periodic function U. WARNING: use of the second formula in the code, to avoid small imaginary parts in the answer (caused by errors in the FFT).

Remark 2 You can check that the solution in equation (1.2) has the following behaviors:

$$u \sim 2n\pi - 4e^{Az} \text{ as } x \to -\infty$$
 and  $u \sim 2(n-1)\pi + 4e^{-Az} \text{ as } x \to \infty.$  (1.6)

<sup>&</sup>lt;sup>2</sup>Kinks and anti-kinks are non-trivial in a very small region, so when separated enough, they can be added.

Thus the solution becomes "linear" at each end, and takes the form of a simple exponential that solves the linearized equation

$$u_{tt} - u_{xx} + u = 0. (1.7)$$

Exponentials of the form <sup>u</sup> <sup>=</sup> <sup>e</sup>�x−�<sup>t</sup> are solutions of this equation, provided that �<sup>2</sup> <sup>−</sup> �<sup>2</sup> <sup>+</sup> <sup>1</sup> <sup>=</sup> <sup>0</sup> — in the case of (1.6) we have: � = ±A and � = ±cA, with A = 1/ → 1 − c<sup>2</sup>. For � real, these exponentials are not acceptable as solutions for the linear equation (1.7), because they become unbounded as either x � ∼ or x � −∼. For equation (1.1), however, the exponential solution decaying as x � −∼ is "switched" (by the non-linear terms, as x varies from x = −∼ to x = +∼) into the solution decaying as x � ∼ (the signs of � and � are changed). Thus, a solution that decays exponentially at both ends ensues. This phenomenon is "generic". Namely: solitary waves are typically related to decaying exponential solutions (of the linearized equations) at each end of the real (space) axis, connected via the nonlinearity, so that a localized solution is obtained.

The exponentials in remark 2 are real valued. One may very well ask: is the nonlinearity capable of connecting decaying exponentials that have an oscillatory part? The answer is yes, and the resulting solutions are the breathers, which we present in the next subsection.

#### 1.2 Breather solutions.

A breather is a wave-package kind of solution — a periodic traveling wave with an envelope that limits the wave to reside in a bounded region of space. These solutions decay (exponentially) to zero as x � ±∼. For equation (1.1) exact formulas for the breathers are know. Namely: let −1 < c < 1, κ, p0, and q<sup>0</sup> be arbitrary constants. Then the breather is given by

$$u = 2n\pi + 4\arctan(\delta\sin(p)\operatorname{sech}(q)),$$
where  $p = \frac{cx - t}{\sqrt{(1 + \delta^2)(1 - c^2)}} + p_0,$ 
and  $q = \delta\frac{x - ct}{\sqrt{(1 + \delta^2)(1 - c^2)}} + q_0,$ 

This is not the kind of solution that is easy to arrive at by "inspection" — however, once you have it, checking that it is a solution is, in principle, just a lot of algebra. The reason behind the fact that one can write such a clean, and explicit, expression for the breather is that the Sine-Gordon equation (1.1) is part of a very special class of evolution equations, known as **Completely Integrable** systems. Such systems are very special, and rare. Thus, here we will not delve into the methods used to obtain solutions such as the one above in (1.8) — and many others. This is a very interesting area of mathematics, but our objective here is to provide methods that do not require a very special structure for the equation — this at the price of a method that provides only approximate solutions, and this only in the weakly non-linear regime.

**Remark 3** The breathers given by equation (1.8) have the following properties:

Envelope, given by 
$$\operatorname{sech} q$$
, 
$$\begin{cases} \text{ with speed } & c. \\ \text{ with decay length } & \frac{2\pi}{\delta} \sqrt{(1+\delta^2)(1-c^2)}. \end{cases}$$
 
$$\begin{cases} \text{ with speed } & c^{-1}. \\ \text{ with wave-length } & \frac{2\pi}{c} \sqrt{(1+\delta^2)(1-c^2)}. \end{cases}$$
 with wave-frequency  $2\pi \sqrt{(1+\delta^2)(1-c^2)}.$ 

Notice that, while the phase moves at a speed that is larger than the light speed, the envelope moves at a speed |c| < 1.

We now re-write the expression for the breathers in equation (1.8) in terms of a different set of parameters. Let the new parameters be:

$$p_0, \quad q_0, \quad \epsilon = \frac{\delta}{\sqrt{(1+\delta^2)(1-c^2)}}, \quad \text{and} \quad k = \frac{c}{\sqrt{(1+\delta^2)(1-c^2)}}.$$
 (1.9)

Then, in equation (1.8) we can write:

$$p = k x - \omega t + p_0$$
, and  $q = \epsilon (x - c t)$ , where  $\omega = \frac{1}{\sqrt{(1 + \delta^2)(1 - c^2)}}$ . (1.10)

The question is now: how do the parameters in (1.9) yield  $\omega$ ,  $\delta$ , and c? To do this we note that:

$$\Omega^2 - \kappa^2 + 1 = 0, \tag{1.11}$$
 where  $\kappa = \epsilon + ik$  and  $\Omega = \epsilon \, c + i\omega$ . Let  $Z = \sqrt{1 + (k + i \, \epsilon)^2}$ , then: 
$$\omega = \mathrm{Real} \, Z, \quad c = \frac{1}{\epsilon} \, \mathrm{Imag} \, Z, \quad \mathrm{and} \quad \delta = \frac{1}{k} \, \mathrm{Imag} \, Z, \tag{1.12}$$

where we have used that  $\delta k = \epsilon c$  to obtain the last equation.

The only places where the equations in (1.12) may present problems are for  $\epsilon=0$  or for k=0. It is easy to see that: for  $\epsilon=0$  no problem arises, since  $\mathsf{Imag}(Z)$  vanishes for  $\epsilon=0$ . On the other hand, for k=0 the restriction  $-1<\epsilon<1$  must be imposed. Then:

$$\omega = \sqrt{1 - \epsilon^2}, \quad c = 0, \quad \text{and} \quad \delta = \frac{\epsilon}{\sqrt{1 - \epsilon^2}}.$$
 (1.13)

**Remark 4** Notice that (for  $\epsilon$  small)  $\omega$ , c, and  $\delta$  have expansions of the form:

$$\omega = \sqrt{1 + k^2} + \epsilon^2 \omega_2 + O(\epsilon^4), \quad c = \frac{k}{\sqrt{1 + k^2}} + \epsilon^2 c_2 + O(\epsilon^4), \quad and \quad \delta = \frac{\epsilon}{k} c. \tag{1.14}$$

The fact that only even (or odd) powers of  $\epsilon$  should appear is easy to deduce from the fact that  $\epsilon \to -\epsilon$  corresponds to  $Z \to Z^*$ , where the asterisk indicates complex conjugate. Thus the real and imaginary parts of Z are even and odd in  $\epsilon$ , respectively.

**Remark 5** The breather solution in equation (1.8), for  $\epsilon > 0$ , has the following asymptotic behaviors:

As 
$$x \to +\infty$$
,  $u \sim 2 n \pi + (2 i \delta e^{-\theta} + c.c) + O(e^{-2q})$ , (1.15)

As 
$$x \to -\infty$$
,  $u \sim 2 n \pi - (2 i \delta e^{+\theta} + c.c) + O(e^{+2q})$ , (1.16)

where c.c. denotes the complex conjugate,  $\theta = q + i p = \kappa x - \Omega t + \theta_0$  and  $\theta_0 = q_0 + i p_0$ . From equation (1.11) it should be clear that both  $e^{\pm \theta}$  satisfy the linearized equation (1.7). Thus, the same phenomena that occurs for solitary waves (see remark 2), occurs also for the breathers. However, instead of a single exponential solution of the linearized equations being involved, two complex conjugate ones occur. Their common real part is the root of the localization of the breather, while the imaginary parts provide the time periodic feature. Again, this phenomenon is generic.

From (1.9 - 1.12) we see that the breather is entirely determined by the linearized solution. In fact, once  $\kappa$  and the zero phase  $\theta_0$  are given, everything else follows. Of particular interests is to observe what happens when the real part of  $\kappa$  is small (see remark 4). Then the decay rate at infinity is slow, so that a very broad breather ensues. The breather is then also of small total amplitude. This behavior is generic, and we exploit in the next section to provide a method for the approximate calculation

of breather solutions (for generic equations) in the weakly nonlinear limit where the breather profiles are broad and shallow.

Problem 2 Use the same algorithm developed for problem 1, to study the interaction of two breathers, or of a breather with either a kink or an anti-kink. Notice that all of these solutions decay (exponentially) to constant states u = 2nω as x � ±∼ (n is an integer). Thus, they do not "feel" each other if sufficiently far apart. Therefore one can get a solution of the equation by simply "adding" two (or more) of them, widely separated. Of course, if their velocities are such that they are in a collision course, eventually they will "feel" each other and will start interacting via the nonlinearity in the equation. What happens then? What is left after the interaction? These are the questions that you are expected to address, numerically, in this problem.

## 2 Breather Expansion.

Here we will present an example of the calculation of breather solutions in the slow decay (broad envelope) regime, where weakly nonlinear approximate expansions are possible. We will work with the example of the Nonlinear Klein-Gordon equation in 1+1 dimensions. Namely:

$$u_{tt} - u_{xx} + F(u) = 0, (2.17)$$

where F = F(u) is an "arbitrary" smooth function. We will assume that, for u small, F has the expansion

$$F = u - 6 a u^{2} - 4 b u^{3} + O(u^{4}), \tag{2.18}$$

where a and b are constants. We have normalized the coefficient of the linear term in the expansion to be one, which can be done by appropriately selecting the time and space scales. Notice that: (2.17) is Lorentz invariant, with a maximum signal propagation speed of one.

We now investigate the small amplitude breather solutions for equation (2.17), if they exist. Since any such solutions will be determined by the linearized, slowly decaying, exponential solutions, we begin by studying them. Let

$$\kappa = \epsilon + i k, \quad \text{and} \quad \Omega = \epsilon c + i \omega,$$
(2.19)

where δ, k, c, and � are real constants. Then — provided that u = e� <sup>x</sup>−� <sup>t</sup> is a solution of the linearized equation utt − uxx + u = 0 — the breather solution will have the form:

$$u = u(\chi, \tau),$$
 where  $\tau = kx - \omega t + \tau_0,$   $\chi = \epsilon (x - ct) + \chi_0,$  (2.20)

<sup>π</sup><sup>0</sup> and �<sup>0</sup> are (real) constants, AND: (1) u decays exponentially as � � ±�.

(2) u is a 2-� periodic function of χ .

The equation that � and � in (2.20) must satisfy is �<sup>2</sup> <sup>−</sup> �<sup>2</sup> <sup>+</sup> <sup>1</sup> <sup>=</sup> <sup>0</sup>. This yields:

$$\epsilon^2 - k^2 = 1 - \omega^2 + \epsilon^2 c^2$$
, and  $k = c \omega$ . (2.21)

From the second equation here we see that the breather oscillations (given via the π dependence) must propagate at speed 1/c. Thus, we can use the Lorentz invariance of the equation to simplify these expressions, by taking k = c = 0. Then

$$\chi = \epsilon x \quad \text{and} \quad \tau = \pm \sqrt{1 - \epsilon^2} t,$$
(2.22)

where we will assume that 0 < δ <sup>2</sup> <sup>∗</sup> <sup>1</sup>. The equation can then be written in the form:

$$u_{\tau\tau} + u = \epsilon^2 \left( u_{\tau\tau} + u_{\chi\chi} \right) + 6 a u^2 + 4 b u^3 + O(u^4). \tag{2.23}$$

Because u is 2-ω periodic in π , we can now use the Fredholm alternative to conclude that: The right hand side in equation (2.23) must be orthogonal to both sin χ and cos χ . This is the key restriction that closes the loop, and allows the computation of the breather solution.

So far we have not used the fact that δ is small. We now use it to expand the solution in the form:

$$u = \epsilon u_1 + \epsilon^2 u_2 + \epsilon^3 u_3 + \dots \tag{2.24}$$

Substituting this into (2.23), and collecting equal powers of δ then yields:

At O(π):

$$(u_1)_{\tau\tau} + u_1 = 0. (2.25)$$

We conclude that u<sup>1</sup> = A(�) sin π — where A = A(�) is some function to be determined.<sup>3</sup>

<sup>3</sup>Note that we can absorb any component of u<sup>1</sup> proportional to cos � into the arbitrary phase �0.

At  $O(\epsilon^2)$ :

$$(u_2)_{\tau\tau} + u_2 = 6 a (u_1)^2 = 3 a A^2 (1 - \cos 2\tau).$$
 (2.26)

Thus, at this order the Fredholm alternative is automatic. Therefore:

$$u_2 = A_2(\chi) \sin \tau + B_2(\chi) \cos \tau + 3 a A^2(\chi) + a A^2(\chi) \cos 2\tau, \tag{2.27}$$

where  $A_2$  and  $B_2$  are functions to be determined at higher order by the Fredholm alternative conditions — in a fashion similar to the one in which A is determined below at  $O(\epsilon^3)$ .

At  $O(\epsilon^3)$ :

$$(u_3)_{\tau\tau} + u_3 = (u_1)_{\tau\tau} + (u_1)_{\chi\chi} + 12 a u_1 u_2 + 4 b (u_1)^3$$
$$= (A'' - A + (30 a^2 + 3 b) A^3) \sin \tau + \text{HOH}, \qquad (2.28)$$

where HOH means "Higher Order Harmonics" (which do not contribute to the Fredholm alternative), and the **primes denote derivatives with respect to**  $\chi$ . It follows then that it must be:

$$A'' - A + (30a^2 + 3b)A^3 = 0. (2.29)$$

This equation has a solution decaying exponentially as  $\chi \to \pm \infty$ , provided that  $(30 \, a^2 + 3 \, b) > 0$  which is the condition for the existence of a breather solution in this case. The solution for A is as follows:

$$A = \frac{1}{\sqrt{30 a^2 + 3 b}} \operatorname{sech} \chi. \tag{2.30}$$

This yields the following approximate expression for the breather solution for equation (2.17)

$$u = \frac{\epsilon \sin \tau}{\sqrt{30 a^2 + 3 b}} \operatorname{sech} \chi + O(\epsilon^2). \tag{2.31}$$

Remark 6 At this point three important questions, which we will not discuss here, arise:

First: Can the expansion above be continued to higher order, and will any more restrictions on F — such as  $(30 a^2 + 3 b) > 0$  above — arise? Formally, there is no problem with continuing the expansion. At each order the undetermined coefficients from the homogeneous solution to the equations for the  $u'_n s$  (such as  $A_2$  and  $B_2$  above in the formula for  $u_2$  in equation (2.27))

provide enough freedom to satisfy the Fredholm alternative to any order. This yields equations of the form

$$L * A_n =$$
Forcing and  $L * B_n =$ Forcing, (2.32)

where <sup>L</sup> � <sup>S</sup> <sup>=</sup> <sup>S</sup>�� <sup>−</sup> <sup>S</sup> <sup>+</sup> (90 <sup>a</sup><sup>2</sup> <sup>+</sup> <sup>9</sup> <sup>b</sup>) <sup>A</sup><sup>2</sup> <sup>S</sup> is the linearized operator for the equation in (2.29) near the solution A. The forcings in these equations are determined by the lower order terms (already determined) at each level. The issue, though, is: do solutions that vanish exponentially as � � ±� exists for all these equations? Answering this question, while hard and messy, is not beyond the realm of the possible — but I do not feel like doing it here.<sup>4</sup>

Second: Even if one can show that the expansion works properly to any order, it is not clear at all that what we obtain is a convergent expansion. One may argue, though, that: Even if the expansion does not converge, and a true breather does not exist, the expansion shows that (at least for δ small) solutions may exist that "resemble" a breather quite a lot. Maybe they are not truly periodic in π (and, if one waits long enough, one would see significant deviations from periodicity), but the departures from periodicity are small over time periods that are not too long. From a practical perspective, this may be plenty good enough.

Third: Can we compute the breathers numerically? Is there a way to implement the approach here numerically? In regards to the second part of the question here: I am not sure.<sup>5</sup> In regards to the first part of the question: assume that a numerical algorithm for solving equation (2.23) in time π is at hand. Let us introduce some notation for this: for some initial data u(� , 0) = U(�), we indicate the solution by u(� , π ) = S(π ,δ) � U. Then, for the breather, what we want is F(U ,δ) = S(2ω ,δ) � U − U = 0. Numerically: U will be represented by some array of numbers (say: the values of U at a numerical grid for �). Thus: U will be some (large dimensional) vector. Further, F(u ,δ) will be some vector function of U that we can compute — with the problem reduced to solving the equation F(U ,δ) = 0. This is the type of problem that bifurcation theory deals with. Further: for small values of δ, the formulas here provide an approximate solution, that can be used to start a bifurcation computation — which then will allow the computation of the

<sup>4</sup>Real special credit will be given to anyone that comes up with a nice way to do this!

<sup>5</sup>Again: real special credit will be given to anyone that comes up with a nice way to do this!

solutions for values of  $\epsilon$  that need not be small at all.

**Problem 3** Calculate approximate breather solutions, following the type of approach used in this section for equation (2.17), for the KdV-type equation

$$u_t + u_{xxx} = F(u)_x, (2.33)$$

where  $F = a u^2 + b u^2 + O(u^3)$  is some smooth function.

**Hint 2** The condition for exponentials of the form  $e^{-\kappa x + \Omega t}$  to be solutions of the linearized equation  $u_t + u_{xxx} = 0$  is  $\Omega = \kappa^3$ . Thus, take:

$$\kappa = \epsilon + i k$$
, and  $\Omega = \kappa^3 = \epsilon \left( -3 k^2 + \epsilon^2 \right) + i \left( -k^3 + 3 \epsilon^2 k \right)$ , (2.34)

where  $\epsilon$  is small, and k is some constant. Let then

$$\chi = \epsilon \left( x - (\epsilon^2 - 3k^2) t \right), \quad and \quad \tau = k \left( x - (3\epsilon^2 - k^2) t \right). \tag{2.35}$$

Thus, we expect the breathers (if any exist) to be solutions of the form

$$u = u(\chi, \tau) = \epsilon u_1(\chi, \tau) + \epsilon^2 u_2(\chi, \tau) + \epsilon^3 u_3(\chi, \tau) + \dots$$
 (2.36)

which are periodic in  $\tau$  (of period  $2\pi$ ), and decay exponentially as  $\chi \to \pm \infty$ .

THE END.