| MIT OpenCourseWare |
|--------------------|
| http://ocw.mit.edu |

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

## to Continuum Modeling.

#### Rodolfo R. Rosales

# MIT, March, 2001.

These notes give <sup>a</sup> few examples illustrating how continuum models can be derived from special limits of discrete models. Only the simplest cases are considered, illustrating some of the most basic ideas. These techniques are useful because continuum models are often much easier to deal with than discrete models with very many variables, both conceptually and computationally.

| 1 | Introduction.                                                              | 2  |
|---|----------------------------------------------------------------------------|----|
| 2 | Wave<br>Equations<br>from<br>Mass-Spring<br>Systems.                       | 2  |
|   | Longitudinal Motion<br>                                                    | 2  |
|   | Nonlinear Elastic Wave<br>Equation (for a<br>Rod)<br>                      | 4  |
|   | Example:<br>Uniform Case<br>                                               | 4  |
|   | <br>Sound<br>Speed                                                         | 4  |
|   | Example:<br>Small Disturbances<br>                                         | 5  |
|   | <br>Linear Wave<br>Equation,<br>and Solutions<br>                          | 5  |
|   | Fast<br>Vibrations<br>                                                     | 5  |
|   | <br>Dispersion<br>                                                         | 6  |
|   | <br>Long Wave<br>Limit<br>                                                 | 6  |
|   | Transversal<br>Motion<br>                                                  | 6  |
|   | Stability of the<br>Equilibrium Solutions<br>                              | 7  |
|   | Nonlinear Elastic Wave<br>Equation (for a<br>String) .                     | 7  |
|   | Example:<br>Uniform String with Small Disturbances<br>                     | 7  |
|   | <br>Uniform String Nonlinear Wave<br>Equation.                             | 7  |
|   | <br>Linear Wave<br>Equation.                                               | 7  |
|   | <br>Stability and<br>Laplace's Equation                                    | 8  |
|   | <br>Ill-posed Time Evolution.                                              | 8  |
|   | General<br>Motion:<br>Strings<br>and Rods<br>                              | 8  |
| 3 | Torsion<br>Coupled<br>Pendulums:<br>Sine-Gordon<br>Equation.               | 8  |
|   | Hooke's<br>Law<br>for Torsional Forces<br>                                 | 9  |
|   | Equations<br>for<br>N<br>torsion coupled<br>equal pendulums<br>            | 10 |
|   | Continuum<br>Limit<br>                                                     | 10 |
|   | <br>Sine-Gordon Equation                                                   | 11 |
|   | <br>Boundary<br>Conditions<br>                                             | 11 |
|   | Kinks<br>and Breathers<br>for the<br>Sine<br>Gordon Equation<br>           | 11 |
|   | Example:<br>Kink and Anti-Kink Solutions<br>                               | 12 |
|   | Example:<br>Breather<br>Solutions<br>                                      | 13 |
|   | Pseudo-spectral<br>Numerical<br>Method for the<br>Sine-Gordon Equation<br> | 14 |
| 4 | Suggested<br>problems.                                                     | 14 |

MIT, Department of Mathematics, room 2-337, Cambridge, MA 02139.

## 1 Introduction.

Continuum approximations are useful in describing discrete systems with a large number of degrees of freedom. In general, a continuum approximation will not describe all possible solutions of the discrete system, but some special class that will depend on the approximations and assumptions made in deriving the continuum model. Whether or not the approximation is useful in describing a particular situation, will depend on the appropriate approximations being made. The most successful models arise in situations where most solutions of the discrete model evolve rapidly in time towards configurations where the assumptions behind the continuum model apply.

The basic step in obtaining a continuum model from a discrete system, is to identify some basic configuration (solution of the discrete model) that can be described by a few parameters. Then one assumes that the full solution of the system can be described, near every point in space and at every time, by this configuration — for some value of the parameters. The parameters are then assumed to vary in space and time, but on scales (macro-scales) that are much larger than the ones associated with the basic configuration (micro-scales). Then one attempts to derive equations describing the evolution of these parameters in the macro-scales, thus averaging out of the problem the micro-scales. There is a close connection between this approach, and the quasi-equilibrium approximations that are often invoked to "close" continuum sets of equations derived using conservation laws.

For example, when deriving the equations for Gas Dynamics in Statistical Mechanics, it is assumed that the local particle interactions rapidly exchange energy and momentum between the molecules — so that the local probability distributions for velocities take a standard form (equivalent to local thermodynamic equilibrium). What exactly makes these assumptions work (in terms of properties of the governing, micro-scale, equations) is rather poorly understood. But that they work rather well cannot be denied. In these notes we will consider examples that are rather simpler than these ones, however, where the "local configurations" tend to be rather trivial.

## 2 Wave Equations from Mass-Spring Systems.

## Longitudinal Motion.

Consider an array of bodies/particles, connected by springs, and restricted<sup>1</sup> to move on a straight line. Let the **positions of the bodies** be given by  $x_n = x_n(t)$ , with  $n = 0, \pm 1, \pm 2, \ldots$ , and let  $M_n$  be the **mass of the**  $n^{th}$  **particle.** Furthermore, let the **force law for the spring** between particles n and n + 1 be given by: force  $= f_{n+\frac{1}{2}}(\Delta x)$ , where  $\Delta x$  is the distance between the particles, and  $f_{n+\frac{1}{n}}$  is positive when the spring is under tension.<sup>2</sup>

If there are no other forces involved (e.g. no friction), the governing equations for the system are:

$$M_n \frac{d^2}{dt^2} x_n = f_{n+\frac{1}{2}}(x_{n+1} - x_n) - f_{n-\frac{1}{2}}(x_n - x_{n-1}), \qquad (2.1)$$

for  $n = 0, \pm 1, \pm 2, \ldots$  The simplest solution for this system of equations is equilibrium. In this case all the accelerations vanish, so that the particle positions are given by the series of algebraic

<sup>&</sup>lt;sup>1</sup>By some device: say the bodies are sliding inside a hollow tube.

<sup>&</sup>lt;sup>2</sup>If the spring obeys Hooke's law, then  $f_{n+\frac{1}{2}}(\Delta x) = k_{n+\frac{1}{2}}\left(\Delta x - L_{n+\frac{1}{2}}\right)$ , where  $k_{n+\frac{1}{2}} > 0$  and  $L_{n+\frac{1}{2}} > 0$  are the spring constant and equilibrium length, respectively.

equations

$$0 = f_{n+\frac{1}{2}}(x_{n+1} - x_n) - f_{n-\frac{1}{2}}(x_n - x_{n-1}).$$
(2.2)

This is the basic configuration (solution) that we will use in obtaining a continuum approximation. Note that this is a one parameter family: if the forces are monotone functions of the displacements  $\Delta x$ , then once any one of them is given, the others follow from (2.2).

Before proceeding any further, it is a good idea to **non-dimensionalize the equations.** We will **assume** that:

A. All the springs are roughly similar, so that we can talk of a typical spring force f, and a typical spring length L. Thus we can write

$$f_{n+\frac{1}{2}}(\Delta x) = f F_{n+\frac{1}{2}}\left(\frac{\Delta x}{L}\right),$$
 (2.3)

where  $F_{n+\frac{1}{2}}$  is a non-dimensional mathematical function, of O(1) size, and with O(1) derivatives. A further assumption is that  $F_{n+\frac{1}{2}}$  changes slowly with n, so that two nearby springs are nearly equal. Mathematically, this is specified by stating that:

$$F_{n+\frac{1}{2}}(\eta) = F(\epsilon(n+1/2), \eta),$$
 (2.4)

where  $0 < \epsilon \ll 1$ , and F is a "nice" (mathematical) function of its two variables.

B. All the particles have roughly the same mass m, and their masses change slowly with n, so that we can write:

$$M_n = m M(\epsilon n), \tag{2.5}$$

where M is a nice mathematical function, with O(1) size, and with O(1) derivatives.

Remark 2.1 Why do we need these assumptions? This has to do with the questions of validity, discussed in the introduction. Suppose that these hypothesis are violated, with the masses and springs jumping wildly in characteristics. Then the basic configuration described by (2.2) will still be a solution. However, as soon as there is any significant motion, neighboring parts of the chain will respond very differently, and the solution will move away from the local equilibrium implied by (2.2). There is no known method to, generically, deal with these sort of problems — which turn out to be very important: see remark 2.2.

From the assumptions in **A** and **B** above, we see that:

Changes in the mass-spring system occur over length scales 
$$\ell = L/\epsilon$$
. (2.6)

Using this scale to non-dimensionalize space, namely:  $x_n = \ell X_n$ , and a yet to be specified time scale  $\tau$  to non-dimensionalize time, namely:  $t = \tau T$ , the equations become:

$$M(\epsilon n) \frac{d^2}{dT^2} X_n = \frac{\epsilon f \tau^2}{m L} \left( F_{n + \frac{1}{2}} \left( \frac{X_{n+1} - X_n}{\epsilon} \right) - F_{n - \frac{1}{2}} \left( \frac{X_n - X_{n-1}}{\epsilon} \right) \right). \tag{2.7}$$

**A** and **B** above also imply that, for the solution in (2.2), the inter-particle distance  $x_{n+1} - x_n$  varies slowly — an  $O(\epsilon)$  fractional amount per step in n. Thus we propose solutions for (2.7) of the form:

$$X_n(t) = X(s_n, t), \text{ where } s_n = n \epsilon,$$
 (2.8)

and X = X(s,t) is some smooth function of its arguments.

Substituting (2.8) into (2.7), and using (2.4) and (2.5), we obtain

$$M(s)\frac{\partial^2}{\partial T^2}X = \frac{\epsilon^2 f \tau^2}{m L} \left(\frac{\partial}{\partial s} F\left(s, \frac{\partial}{\partial s} X\right) + O(\epsilon^2)\right). \tag{2.9}$$

Here we have used that:

$$\frac{X_{n+1} - X_n}{\epsilon} = \frac{\partial}{\partial s} X(s + \frac{1}{2}\epsilon, t) + O(\epsilon^2) \quad \text{and} \quad \frac{X_n - X_{n-1}}{\epsilon} = \frac{\partial}{\partial s} X(s - \frac{1}{2}\epsilon, t) + O(\epsilon^2),$$

with a similar formula applying to the difference  $F_{n+\frac{1}{2}} - F_{n-\frac{1}{2}}$ .

Equation (2.9) suggests that we should take

$$\tau = \sqrt{\frac{m\,L}{\epsilon^2\,f}}\,,\tag{2.10}$$

for the un-specified time scale in (2.7). Then equation (2.9) leads to the **continuum limit approximations** (valid for  $0 < \epsilon \ll 1$ )

$$M(s)\frac{\partial^2}{\partial T^2}X = \frac{\partial}{\partial s}F\left(s, \frac{\partial}{\partial s}X\right). \tag{2.11}$$

The mass-spring system introduced in equation (2.1) can be thought of as a simple model for an elastic rod under (only) longitudinal forces. Then we see that (2.11) is a model (nonlinear wave) equation for the longitudinal vibrations of an elastic rod, with s a lagrangian coordinate for the points in the rod, M = M(s) the mass density along the rod, and X giving the position of the point s as a function of time, and F a function characterizing the elastic response of the rod. Of course, in practice F must be obtained from laboratory measurements.

Remark 2.2 The way in which the equations for nonlinear elasticity can be derived for a crystalline solid is not too different<sup>3</sup> from the derivation of the wave equation (2.11) for longitudinal vibrations. Then a very important question arises (see first paragraph in section 1): What important behaviors are missed due to the assumptions in the derivation? How can they be modeled? In particular, what happens if there are "defects" in the crystal structure (see remark 2.1)? These are all very important, and open, problems of current research interest.

#### Example 2.1 Uniform Rod.

If all the springs and all the particles are equal, then we can take  $M \equiv 1$  and F is independent of s. Furthermore, if we take L to be the (common) equilibrium length of the springs, we then have

$$\frac{\partial^2}{\partial T^2} X = \frac{\partial}{\partial s} F\left(\frac{\partial}{\partial s} X\right) = c^2 \left(\frac{\partial}{\partial s} X\right) \frac{\partial^2}{\partial s^2} X, \qquad (2.12)$$

where  $c^2 = c^2(\eta) = dF/d\eta(\eta) > 0$ , and F(1) = 0 (equilibrium length). The unperturbed "rod" corresponds to  $X \equiv s$ , while  $X \equiv \alpha$  s corresponds to the rod under uniform tension  $(\alpha > 1)$ , or compression  $(\alpha < 1)$ . Also, note that c is a (non-dimensional) speed — the speed at which elastic disturbances along the rod propagate: i.e. the sound speed.

<sup>&</sup>lt;sup>3</sup>At least qualitatively, though it is technically far more challenging.

#### Example 2.2 Small Disturbances.

Consider a uniform rod in a situation where the departures from uniform equilibrium are small. That is  $\partial X/\partial s \approx \alpha$ , where  $\alpha$  is a constant. Then equation (2.12) can be approximated by the linear wave equation

$$X_{TT} = c^2 X_{ss} \,, \tag{2.13}$$

where  $c = c(\alpha)$  is a constant. The general solution to this equation has the form

$$X = g(s - cT) + h(s + cT), (2.14)$$

where g and h are arbitrary functions. This solution clearly shows that c is the wave propagation velocity.

#### Remark 2.3 Fast vibrations.

The vibration frequency for a typical mass m, attached to a typical spring in the chain, is:

$$\omega = \sqrt{\frac{f}{mL}} = \frac{1}{\epsilon \tau} \,. \tag{2.15}$$

This corresponds to a time scale much shorter than the one involved in the solution in (2.8-2.11). What role do the motions in these scales play in the behavior of the solutions of (2.1), under the assumptions made earlier in A and B?

For real crystal lattices, which are definitely not one dimensional (as the one in (2.1)) these fast time scales correspond to thermal energy (energy stored in the local vibrations of the atoms, relative to their equilibrium positions). It is believed that the nonlinearities in the lattice act so as to randomize these vibrations, so that the energy they contain propagates as heat (diffuses). In one dimension, however, this does not generally happen, with the vibrations remaining coherent enough to propagate with a strong wave component. The actual processes involved are very poorly understood, and the statements just made result, mainly, from numerical experiments with nonlinear lattices.

Just to be a bit more precise: consider the situation where all the masses are equal —  $M_n = m$  for all n, and all the springs are equal and satisfy Hooke's law (linear elasticity):

$$f_{n+\frac{1}{2}}(\Delta x) = k(\Delta x - L) = f\left(\frac{\Delta x}{L} - 1\right), \qquad (2.16)$$

where k is the spring constant, L is the equilibrium length, and f = kL. Then equation (2.1) takes the form

$$\frac{d^2}{dt^2}x_n = \omega^2 \left(x_{n+1} - 2x_n + x_{n-1}\right),\tag{2.17}$$

where  $\omega$  is as in (2.15). Because this system is linear, we can write its general solution as a linear superposition of eigenmodes, which are solutions of the form<sup>4</sup>

$$x_n = \exp(i \kappa n - i \sigma t)$$
, where  $\sigma = \pm 2 \omega \sin\left(\frac{\kappa}{2}\right)$  and  $-\infty < \kappa < \infty$  is a constant. (2.18)

These must be added to an equilibrium solution  $x_n = \alpha L n = s_n$ , where  $\alpha > 0$  is a constant.

<sup>&</sup>lt;sup>4</sup>Check that these are solutions.

Relative to the mean position  $s_n$  along the lattice, each solution in (2.18) can be written as

$$x_n = \exp(i\frac{\kappa}{\alpha L} s_n - i\sigma t).$$

Thus we see that it represents a wave of wavelength  $\lambda = 2\pi\alpha L/\kappa$ , and speed

$$c_w = \frac{\alpha L\sigma}{\kappa} = \pm \frac{2\alpha L\omega}{\kappa} \sin\left(\frac{\kappa}{2}\right) = \frac{2c}{\kappa} \sin\left(\frac{\kappa}{2}\right) \tag{2.19}$$

propagating along the lattice — where  $c = \alpha L\omega$  is a speed. Note that the speed of propagation is a function of the wave-length — this phenomenon is know by the name of **dispersion**. We also note that the maximum frequency these eigenmodes can have is  $\sigma = 2\omega$ , and corresponds to wavelengths of the order of the lattice separation.<sup>5</sup>

In the case of equations (2.16 – 2.17) there is no intrinsic  $\epsilon$  in the equations: it must arise from the initial conditions. That is to say: assume that the wavelength  $\ell$  with which the lattice is excited is much larger than the lattice equilibrium separation L, i.e.  $\ell \gg L$ , with  $\epsilon = L/\ell$ . This corresponds to solutions (2.18) with  $\kappa$  small. In this long wave limit we see that (2.19) implies that the solutions have the same wave speed  $c_w = \pm c$ . This corresponds to the situation in (2.13 – 2.14).

It is clear that, in the linear lattice situation described above, we cannot dismiss the fast vibration excitations (with frequencies of the order of  $\omega$ ) as constituting some sort of energy "bath" to be interpreted as heat. The energy in these vibrations propagates as waves through the media, with speeds which are of the same order of magnitude as the sound waves equation (2.13) describes. Before the advent of computers it was believed that nonlinearity would destroy the coherence of these fast vibrations. Numerical experiments, however, have shown that this is not (generally) true for one dimensional lattices, though it seems to be true in higher dimensions. Exactly why, and how, this happens is a subject of some current interest.

#### Transversal Motion.

We consider now a slightly different situation, in which the masses are allowed to move only in the direction perpendicular to the x axis. To be precise: consider a sequence of masses  $M_n$  in the plane, whose x coordinates are given by  $x_n=n\,L$ . Each mass is restricted to move only in the orthogonal coordinate direction, with  $y_n=y_n(t)$  giving its y position. The masses are connected by springs, with  $f_{n+\frac{1}{2}}(\Delta r_{n+\frac{1}{2}})$  the force law, where  $\Delta r_{n+\frac{1}{2}}=\sqrt{L^2+(y_{n+1}-y_n)^2}$  is the distance between masses. Assuming that there are no other forces involved, the governing equations for the system are:

$$M_n \frac{d^2}{dt^2} y_n = \frac{y_{n+1} - y_n}{\Delta r_{n+\frac{1}{2}}} f_{n+\frac{1}{2}} (\Delta r_{n+\frac{1}{2}}) - \frac{y_n - y_{n-1}}{\Delta r_{n-\frac{1}{2}}} f_{n-\frac{1}{2}} (\Delta r_{n-\frac{1}{2}}) , \qquad (2.20)$$

for  $n = 0, \pm 1, \pm 2, \ldots$  (you should convince yourself that this is the case).

The simplest solution for this system of equations is equilibrium, with all the masses lined up horizontally  $y_{n+1} = y_n$ , so that all the accelerations vanish. Again, one can use this (one parameter) family of solutions to obtain a continuum approximation for the system in (2.20) — under the same assumptions earlier in **A** and **B**.

<sup>&</sup>lt;sup>5</sup>The reason for the 2 relative to (2.15) is that the masses are coupled, and not attached to a single spring.

<sup>&</sup>lt;sup>6</sup>The first observation of this general phenomena was reported by E. Fermi, J. Pasta and S. Ulam, in 1955: *Studies of Non Linear Problems*, Los Alamos Report LA-1940 (1955), pp. 978-988 in Collected Papers of Enrico Fermi. II, The University of Chicago Press, Chicago, (1965).

#### Remark 2.4 Stability of the Equilibrium Solutions.

It should be intuitively obvious that the equilibrium solutions described above will be stable only if the equilibrium lengths of the springs  $\mathcal{L}_{n+\frac{1}{2}}$  are smaller than the horizontal separation L between the masses, namely:  $\mathcal{L}_{n+\frac{1}{2}} < L$ . This so that none of the springs is under compression in the solution, since any mass in a situation where its springs are under compression will easily "pop" out of alignment with the others — see example 2.3.

Introduce now the non-dimensional variables  $Y = \epsilon y/L$ ,  $X = \epsilon x/L$  (note that, since  $x_n = nL$ , in fact X plays here the same role that s played in the prior derivation<sup>7</sup>), and  $T = t/\tau$ , where  $\tau$  is as in (2.10). Then the **continuum limit for the equations in (2.20)** is given by

$$M(X)\frac{\partial^2 Y}{\partial T^2} = \frac{\partial}{\partial X} \left( \frac{F(X, S)}{S} \frac{\partial Y}{\partial X} \right)$$
 (2.21)

where Y = Y(X, T) and

$$S = \sqrt{1 + \left(\frac{\partial Y}{\partial X}\right)^2}.$$

### The derivation of this equation is left as an exercise to the reader.

The mass-spring system introduced in (2.20) can be thought of as a simple model for an elastic string restricted to move in the transversal direction only. Then we see that (2.21) is a model (nonlinear wave) equation for the transversal vibrations of a string, where X is the longitudinal coordinate along the string position, Y is the transversal coordinate, M = M(X) is the mass density along the string, and F = F(X, S) describes the elastic properties of the string.<sup>8</sup> In the non-dimensional coordinates, the (local) equilibrium length for the string is given by  $e_{\ell} = \mathcal{L}/L$ . That is, the elastic forces vanish for this length:

$$F(X, e_{\ell}(X)) \equiv 0$$
, where  $e_{\ell} < 1$  (for stability, see remark 2.4). (2.22)

We also assume that  $\frac{\partial}{\partial S}F(X,S) > 0$ .

#### Example 2.3 Uniform String with Small Disturbances.

Consider now a uniform string (neither M, nor F, depend on X) in a situation where the departures from equilibrium are small ( $\partial Y/\partial X$  is small).

For a uniform string we can assume  $M \equiv 1$ , and F is independent of X. Thus equation (2.21) reduces to

$$\frac{\partial^2 Y}{\partial T^2} = \frac{\partial}{\partial X} \left( \frac{F(\mathcal{S})}{\mathcal{S}} \frac{\partial Y}{\partial X} \right). \tag{2.23}$$

Next, for small disturbances we have  $S \approx 1$ , and (2.23) can be approximated by the linear wave equation

$$Y_{TT} = c^2 Y_{XX} \,, \tag{2.24}$$

where  $c^2 = F(1)$  is a constant (see equations (2.13 – 2.14).

<sup>&</sup>lt;sup>7</sup>The coordinate s is simply a label for the masses. Since in this case the masses do not move horizontally, X can be used as the label.

<sup>&</sup>lt;sup>8</sup>Notice that S is the local stretching of the string, due to its inclination relative to the horizontal position (actual length divided by horizontal length).

Notice how the stability condition  $e_{\ell} < 1$  in (2.22) guarantees that  $c^2 > 0$  in (2.23). If this were not the case, instead of the linear wave equation, the linearized equation would have been of the form

$$Y_{TT} + d^2 Y_{XX} = 0, (2.25)$$

with d > 0. This is Laplace Equation, which is ill-posed as an evolution in time problem. To see this, it is enough to notice that (2.25) has the following solutions:

$$Y = e^{d|k|t} \sin(kX), \quad \text{for any } -\infty < k < \infty.$$
 (2.26)

These solutions grow arbitrarily fast in time, the fastest the shortest the wave-length (|k| larger). This is just the mathematical form of the obvious physical fact that a straight string (with no bending strength) is not a very stable object when under compression.

## General Motion: Strings and Rods.

If no restrictions to longitudinal (as in (2.1)) or transversal (as in (2.20)) motion are imposed on the mass-spring chain, then (in the continuum limit) general equations including both longitudinal and transversal modes of vibration for a string are obtained. Since strings have no bending strength, these equations will be well behaved only as long as the string is under tension everywhere.

Bending strength is easily incorporated into the mass-spring chain model. Basically, what we need to do is to incorporate, at the location of each mass point, a bending spring. These springs apply a torque when their ends are bent, and will exert a force when-ever the chain is not straight. The continuum limit of a model like this will be equations describing the vibrations of a rod.

We will not develop these model equations here.

## 3 Torsion Coupled Pendulums: Sine-Gordon Equation.

Consider an horizontal axle A, of total length  $\ell$ , suspended at its ends by "frictionless" bearings. Along this axle, at equally spaced intervals, there are N equal pendulums. Each pendulum consists of a rigid rod, attached perpendicularly to the axle, with a mass at the end. When at rest, all the pendulums point down the vertical. We now make the following assumptions and approximations:

- 1. Each pendulum has a mass  $\frac{M}{N}$ . The distance from its center of mass to the axle center is L.
- 2. The axle A is free to rotate, and we can ignore any frictional forces (i.e.: they are small). In fact, the only forces that we will consider are gravity, and the torsional forces induced on the axle when the pendulums are not all aligned.
- 3. Any deformations to the axle and rod shapes are small enough that we can ignore them. Thus the axle and rod are assumed straight at all times.
- 4. The mass of the axle is small compared to M, so we ignore it (this assumption is not strictly needed, but we make it to keep matters simple).

Our aim is to produce a continuum approximation for this system, as  $N \to \infty$ , with everything else fixed.

Each one of the pendulums can be characterized by the angle  $\theta_n = \theta_n(t)$  that its suspending rod makes with the vertical direction. Each pendulum is then subject to three forces:

- (a) Gravity, for which only the component perpendicular to the pendulum rod is considered.<sup>9</sup>
- (b) Axle torsional force due to the twist  $\theta_{n+1} \theta_n$ . This couples each pendulum to the next one.
- (c) Axle torsional force due to the twist  $\theta_n \theta_{n-1}$ . This couples each pendulum to the prior one.

We will assume that the amount of twist per unit length in the axle is small, so that Hooke's law applies.

#### Remark 3.1 Hooke's Law for Torsional Forces.

In the Hooke's law regime, for a given fixed bar, the torque generated is directly proportional to the angle of twist, and inversely proportional to the distance over which the twist occurs.

To be specific: in the problem here, imagine that a section of length  $\Delta \ell$  of the axle has been twisted by an amount (angle)  $\Psi$ . Then, if T is the torque generated by this twist, one can write

$$T = \frac{\kappa \Psi}{\Delta \ell} \,, \tag{3.1}$$

where  $\kappa$  is a constant that depends on the axle material and the area of its cross-section — assume that the axle is an homogeneous cylinder. The dimensions of  $\kappa$  are given by:

$$[\kappa] = \frac{mass \times length^3}{time^2 \times angle} = \frac{force \times area}{angle}.$$
 (3.2)

This torque then translates onto a tangential force of magnitude F = T/L, on a mass attached to the axle at a distance L. The sign of the force is such that it opposes the twist.

Let us now go back to our problem, and write the equations of motion for the N pendulums. We will assume that:

- $\bullet$  The horizontal separation between pendulums is  $\frac{\ell}{N+1}$ .
- $\bullet$  The first and last pendulum are at a distance  $\frac{\ell}{2(N+1)}$  from the respective ends of the axle.

The tangential force (perpendicular to the pendulum rod) due to gravity on each of the masses is

$$F_g = -\frac{1}{N} Mg \sin \theta_n , \quad \text{where} \quad n = 1, \dots, N .$$
 (3.3)

For any two successive masses, there is also a torque whenever  $\theta_n \neq \theta_{n+1}$ . This is generated by the twist in the axle, of magnitude  $\theta_{n+1} - \theta_n$ , over the segment of length  $\ell/(N+1)$  connecting the two rods. Thus each of the masses experiences a force (equal in magnitude and opposite in sign)

$$F_T = \pm (N+1) \frac{\kappa}{\ell L} \left( \theta_{n+1} - \theta_n \right), \tag{3.4}$$

where the signs are such that the forces tend to make  $\theta_n = \theta_{n+1}$ . Putting all this together, we obtain the following set of equations for the angles:

$$\frac{1}{N} ML \frac{d^2 \theta_1}{dt^2} = -\frac{1}{N} Mg \sin \theta_1 + \frac{(N+1)\kappa}{\ell L} (\theta_2 - \theta_1), \qquad (3.5)$$

<sup>&</sup>lt;sup>9</sup>The component along the rod is balanced by the rod itself, which we approximate as being rigid.

$$\frac{1}{N} ML \frac{d^2 \theta_n}{dt^2} = -\frac{1}{N} Mg \sin \theta_n 
+ \frac{(N+1)\kappa}{\ell L} (\theta_{n+1} - \theta_n) - \frac{(N+1)\kappa}{\ell L} (\theta_n - \theta_{n-1}),$$
(3.6)
$$\text{for } n = 2, \dots, N-1, \text{ and}$$

$$\frac{1}{N} ML \frac{d^2 \theta_N}{dt^2} = -\frac{1}{N} Mg \sin \theta_N - \frac{(N+1)\kappa}{\ell L} (\theta_N - \theta_{N-1}). \tag{3.7}$$

These are the equations for N torsion coupled equal pendulums.

**Remark 3.2** To check that the signs for the torsion forces selected in these equations are correct, take the difference between the  $n^{th}$  and  $(n+1)^{th}$  equation. Then you should see that the torsion force (due to the portion of the axle connecting the  $n^{th}$  and  $(n+1)^{th}$  pendulums) is acting so as to make the angles equal.

Remark 3.3 Note that the equations for the first and last angle are different, because the first and last pendulum experience a torsion force from only one side. How would you modify these equations to account for having one (or both) ends of the axle fixed?

#### Continuum Limit.

Now we consider the continuum limit, in which we let  $N \to \infty$  and assume that the  $n^{\text{th}}$  angle can be written in the form:

$$\theta_n(t) = \theta(x_n, t), \qquad (3.8)$$

where  $\theta = \theta(x, t)$  is a "nice" function (with derivatives) and  $x_n = \frac{n + \frac{1}{2}}{N + 1} \ell$  is the position of the pendulum along the axle. In particular, note that:

$$\Delta x = x_{n+1} - x_n = \frac{\ell}{N+1} \,. \tag{3.9}$$

Take equation (3.6), and multiply it by  $N/\ell$ . Then we obtain

$$\rho L \frac{d^2 \theta_n}{dt^2} = -\rho g \sin \theta_n + \frac{N(N+1)\kappa}{\ell^2 L} (\theta_{n+1} - 2\theta_n + \theta_{n-1}),$$

where  $\rho = M/\ell$  is the mass density per unit length in the  $N \to \infty$  limit. Using equation (3.9), this can be written in the form:

$$\rho L \frac{d^2 \theta_n}{dt^2} = -\rho g \sin \theta_n + \frac{N}{(N+1)} \frac{\kappa}{L} \frac{\theta_{n+1} - 2\theta_n + \theta_{n-1}}{(\Delta x)^2}.$$
 (3.10)

From equation (3.8) we see that — in the limit  $N \to \infty$  (where  $\Delta \to 0$ ) — we have:

$$\frac{\theta_{n+1} - 2\theta_n + \theta_{n-1}}{(\Delta x)^2} \to \frac{\partial^2 \theta}{\partial x^2}(x_n, t).$$

Thus, finally, we obtain (for the continuum limit) the nonlinear wave equation (the "Sine-Gordon" equation):

$$\theta_{tt} - c^2 \theta_{xx} = -\omega^2 \sin \theta \,, \tag{3.11}$$

where  $\omega = \sqrt{\frac{g}{L}}$  is the pendulum angular frequency, and  $c = \sqrt{\frac{\kappa}{\rho L^2}}$  is a wave propagation speed

(check that the dimensions are correct).

#### Remark 3.4 Boundary Conditions.

What happens with the first (3.5) and last (3.7) equations in the limit  $N \to \infty$ ?

As above, multiply (3.5) by  $1/\ell$ . Then the equation becomes:

$$\frac{\rho L}{N} \frac{d^2 \theta_1}{dt^2} = -\frac{\rho g}{N} \sin \theta_1 + \frac{(N+1)\kappa}{\ell^2 L} (\theta_2 - \theta_1) = -\frac{\rho g}{N} \sin \theta_1 + \frac{\kappa}{\ell L} \frac{\theta_2 - \theta_1}{\Delta x}.$$

Thus, as  $N \to \infty$  one obtains

$$\theta_x(0,t) = 0.$$

This is just the statement that there are no torsion forces at the x = 0 end (since the axle is free to rotate there). Similarly, one obtains:

$$\theta_x(\ell, t) = 0,$$

at the other end of the axle. How would these boundary conditions be modified if the axle where fixed at one (or both) ends?

## Kinks and Breathers for the Sine Gordon Equation.

Equation (3.11), whose non-dimensional form is

$$\theta_{tt} - \theta_{xx} = -\sin\theta\,, (3.12)$$

has a rather interesting history. Its first appearance is not in the context of a physical context at all, but in the study of the geometry of surfaces with constant negative Gaussian curvature. Physical problems for which it has been used include: Josephson junction transmission lines, dislocation in crystals, propagation in ferromagnetic materials of waves carrying rotations in the magnetization direction, etc.<sup>10</sup> Mathematically, it is a very interesting because **it is one of the few physically important nonlinear partial differential equations that can be solved explicitly** (by a technique known as **Inverse Scattering**, which we will not describe here).

An important consequence of equation (3.12) exact solvability, is that it possesses **particle-like** solutions, known as kinks, anti-kinks, and breathers. These are localized traveling disturbances, which preserve their identity when they interact. In fact, the only effect of an interaction is a phase shift in the particle positions after the interaction: effectively, the "particles" approach each other, stay together briefly while they interact (this causes the "phase shift") and then depart, preserving their identities and original velocities. This can all be shown analytically, but here we will only illustrate the process, using some computational examples.

<sup>&</sup>lt;sup>10</sup>For reviews see:

A. C. Scott, 1970, Active and Nonlinear Wave Propagation in Electronics, Wiley Interscience, New York (page 250). Barone, A. F. Esposito, C. J. Magee, and A. C. Scott, 1971, Theory and Applications of the Sine Gordon Equation, Rivista del Nuovo Cimento vol. 1, pp. 227–267.

The first step is to present analytical expressions for the various particle-like solutions of equation (3.12). These turn out to be relatively simple to write.

#### Example 3.1 Kinks and Anti-Kinks.

Equation (3.12) has some interesting solutions, that correspond to giving the pendulums a full  $2\pi$  twist (e.g.: take one end pendulum, and give it a full  $2\pi$  rotation). This generates a  $2\pi$  twist wave that propagates along the pendulum chain. These waves are known as kinks or anti-kinks (depending on the sign of the rotation), and can be written explicitly. In fact, they are steady wave solutions, for which the equation reduces to an O.D.E., which can be explicitly solved.

Let -1 < c < 1 be a constant (kink, or anti-kink speed), and let  $z = (x - ct - x_0)$  be a moving coordinate, where the solution is steady — the "twist" will be centered at  $x = ct + x_0$ , where  $x_0$  is the position at time t = 0. Then the kink solution is given by

$$\theta = 2 \arccos\left(\frac{e^{2z/\beta} - 1}{e^{2z/\beta} + 1}\right) = 4 \arctan\left(\exp\left(-\frac{z}{\beta}\right)\right),$$
 (3.13)

where  $\beta = \sqrt{1-c^2}$  is the kink width. This solution represents a propagating clock-wise  $2\pi$  rotation, from  $\theta = 2 m \pi$  as  $x \to -\infty$  (where m is an integer) to  $\theta = 2 (m-1) \pi$  as  $x \to \infty$ , with most of the rotation concentrated in a region of width  $O(\beta)$  near  $x = ct + x_0$ . The parameter c is determined (for example) by how fast the initial twist is introduced when the kink is generated.

We note now that:

- From (3.13) it follows that  $\theta_t = -c \,\theta_x = \frac{2c}{\beta} \sin\left(\frac{\theta}{2}\right)$ . Using this, it is easy to show that (3.13) is a solution of equation (3.12).
- The Sine-Gordon equation is the simplest of a "class" of models proposed for nuclear interactions. In this interpretation, the kinks are nuclear particles. Since (in the non-dimensional version (3.12)) the speed of light is 1, the restriction -1 < c < 1 is the relativistic restriction, and the factor  $\beta$  incorporates the usual relativistic contraction.

The anti-kink solution follows by replacing  $x \to -x$  and  $t \to -t$  in (3.13). It corresponds to a propagating counter-clock-wise  $2\pi$  rotation, and it is given by

$$\theta = 2 \arccos\left(\frac{1 - e^{2z/\beta}}{1 + e^{2z/\beta}}\right) = 4 \arctan\left(\exp\left(\frac{z}{\beta}\right)\right).$$
 (3.14)

The kinks and anti-kinks are very non-linear solutions. Thus, it is of some interest to study how they interact with each other. Because they are very localized solutions (non-trivial only in a small region), when their centers are far enough they can be added. Thus, numerically it is rather easy to study their interactions, by setting up initial conditions that correspond to kinks and anti-kinks far enough that they do not initially interact. Then they are followed until they collide. In the lectures the results of numerical experiments of this type will be shown (the numerical method used in the experiments is a "pseudo-spectral" method).

Solutions of the form  $\theta = \theta(x - ct)$ , where c is a constant: the speed of propagation.

#### Example 3.2 Breathers.

A different kind of interesting solution is provided by the "breathers" — which we handle next. A breather is a wave-package kind of solution (an oscillatory wave, with an envelope that limits the wave to reside in a bounded region of space. These solutions vanish (exponentially) as  $x \to \pm \infty$ . This last property allows for easy numerical simulations of interactions of breathers (and kinks). One can setup initial conditions corresponding to the interaction of as many kinks and/or breathers as one may wish (limited only be the numerical resolution of the computation), simply by separating them in space.

A breather solution is characterized by two arbitrary constants -1 < d, V < 1. Then define

$$A = d/\sqrt{1 - d^{2}}, 
B = 1/\sqrt{1 - V^{2}}, 
C = \sqrt{1 - d^{2}}, 
p = CB(Vx - t + t_{0}), 
q = dB(x - Vt - x_{0}), 
Q = A \sin(p)/\cosh(q),$$
(3.15)

where  $x_0$  and  $t_0$  are constants, centering the envelope and the phase, respectively. Notice that the partial derivatives of Q (with respect to p and q) are given by

$$Q_p = A \cos(p)/\cosh(q) \quad and \quad Q_q = -Q \tanh(q). \tag{3.16}$$

The breather solution (and its time derivative) is then given by:

$$\theta = 4 \arctan(Q), 
\theta_t = -4 (1 + Q^2) (C B Q_p + d B V Q_q).$$
(3.17)

The breather solution is a wave-package type of solution, with the phase controlled by p, and the envelope (causing the exponential vanishing of the solution) by q). The wave-package details are given by:

$$\begin{array}{llllllllllllllllllllllllllllllllllll$$

Notice that, while the phase moves faster than the speed of "light" (i.e.: 1), the envelope always moves with a speed -1 < V < 1, and has width proportional to  $\sqrt{1 - V^2}$ .

Finally, in case you are familiar with the notion of group speed, notice that (for the linearized Sine-Gordon equation:  $\theta_{tt} - \theta_{xx} + \theta = 0$ ) we have: (group speed) = 1/(phase speed) — which is exactly the relationship satisfied by  $c_e = V$  and  $c_p = 1/V$  for a breather. This is because, for |x| large, the breathers must satisfy the linearized equation. Thus the envelope must move at the group velocity corresponding to the oscillations wave-length.

### Remark 3.5 Pseudo-spectral Numerical Method for the Sine-Gordon Equation.

Here we will give a rough idea of a numerical method that can be used to solve the Sine-Gordon equation. This remark will only make sense to you if you have some familiarity with Fourier Series for periodic functions.

The basic idea in spectral methods is that the numerical differentiation of a (smooth) periodic functions can be done much more efficiently (and accurately) on the "Fourier Side" — since there it amounts to term by term multiplication of the n<sup>th</sup> Fourier coefficient by in. On the other hand, non-linear operations (such as calculating the square, point by point, of the solution) can be done efficiently on the "Physical Side".

Thus, in a numerical computation using a pseudo-spectral method, all the operations involving taking derivatives are done using the Fourier Side, while all the non-linear operations are done directly on the numerical solution. The back-and-forth calculation of Fourier Series and their inverses is carried by the FFT (Fast Fourier Transform) algorithm — which is a very efficient algorithm for doing Fourier calculations.

Unfortunately, a naive implementation of a spectral scheme to solve the Sine-Gordon equation would require **periodic** in space, solutions. But we need to be able to solve for solutions that are  $\mathbf{mod}$ - $2\pi$   $\mathbf{periodic}$  (such as the kinks and anti-kinks), since the solutions to the equation are angles. Thus, we need to get around this problem.

In a naive implementation of a spectral method, we would write the equation as

$$\left\{
 \begin{array}{rcl}
 u_t & = & v \,, \\
 v_t & = & u_{xx} - \sin u \,,
 \end{array}
 \right\} 
 \tag{3.20}$$

where  $u = \theta$  and  $v = \theta_t$ . Next we would discretize space using a periodic uniform mesh (with a large enough period), and would evaluate the right hand side using FFT's to calculate derivatives. This would reduce the P.D.E. to some large O.D.E., involving all the values of the solution (and its time derivative) at the nodes in the space grid. This O.D.E. could then be solved using a standard O.D.E. solver — say, ode45 in MatLab.

In order to use the idea above in a way that allows us to solve the equation with mod- $2\pi$  periodicity in space, we need to be able to evaluate the derivative  $u_{xx}$  in a way that ignores jumps by multiples of  $2\pi$  in u. The following trick works in doing this:

Introduce 
$$U = e^{iu}$$
. Then

$$u_{xx} = i \frac{(U_x)^2 - U U_{xx}}{U^2} \tag{3.21}$$

gives a formula for  $u_{xx}$  that ignores  $2\pi$  jumps in u. Warning: In the actual implementation one must use

$$u_{xx} = -\mathrm{imag}\left(\frac{(U_x)^2 - U\,U_{xx}}{U^2}\right)$$

to avoid small imaginary parts in the answer (caused by numerical errors).

## 4 Suggested problems.

A list of suggested problems that go along with these notes follow:

- 1. Check the derivation of the system of equations (2.20).
- 2. Derive the continuum equation in (2.21).
- 3. Look at the end of section 2, under the title "General Motion: String and Rods". Derive continuum equations describing the motion (in the plane) of a string without constraints.
- 4. Look at the end of section 2, under the title "General Motion: String and Rods". Add bending springs to the model, and derive continuum equations describing the motion (in the plane) of
- 6. Answer the question in remark 3.3.
- 7. Do the dimensions check stated below equation (3.11).
- 8. Answer the question in remark 3.4.
- 9. Show that (3.13) is a solution (there is a hint about how to do this a few linesbelow the equation).
- 10. Use a computer to plot the solution in (3.13), as a function of z, for a few choices of c.
- 11. Show that (3.17) is a solution.
- 12. Use a computer to plot the solution in (3.17), as a function of x, for various times and choices of parameters.
- 13. Implementanumerical code to calculate interactions of kinks, breathers, etc., using the ideas