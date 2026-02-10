18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 01 2009 09 09 WED

TOPICS: Mechanics of the course.

Example pde. Initial and boundary value problems.

Well and ill-posed problems.

Introduction: Syllabus issues; exams; lecturer; etc.

ODE's and PDE's

ODE solution: determined by a set of constants. Simple Examples. PDE solution: determined by functions. Simple Examples.

Example pde: heat, laplace, wave, ... more later.

Initial value and boundary value problems.

Quote existence-uniqueness theorem for ODE IV problem.

No analogous theorem for PDE's. Closest is C-K theorem, and need very strong restrictions (e.g.: analytic functions.)

Well and ill-posed problems. Why is this important.

Examples (show these are badly ill-posed: growth rate of perturbations goes to infinity as the frequency grows. No control over errors.

- --- Can you recover the temperature in the past from today's data?
- --- Can you recover the steady state temperature inside a body from knowledge of the temperature and heat flux along some part of the boundary? [Do example of square, with temperature and flux given on a side, zero temperature on the two adjoining sides, and nothing known about the opposite side].
- --- Real life: issues like this (open problems) appear in multi-phase flows modeling, phase transition modeling, detonation waves (square wave model), image reconstruction.
- Possible Fix: filtering. Works if filtering makes sense within context of problem (e.g. CAT scans or image reconstruction). It can also lead to nonsense if applied mechanically.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 02 2009 09 14 MON

TOPICS: Conservation laws and pde.

Integral and differential forms.

Closure strategies. Quasi-equillibrium.

Derivation of pde by conservation laws. Integral and differential forms.

--- The pde given by a conserved density and the corresponding flux in 1-D and in multi-D.

--- Systems of conservation laws.

The problem of closure.

Example: Euler equations of gas dynamics (1-D) and closure via equilibrium

thermodynamics.

Adding sources.

General closure strategy; quasi-equilibrium. Equations of state. Examples: traffic flow and river flow.

--- Examine the properties of the flow equations of state for these two cases.

Equations of type  $rho_t + c(rho)*rho_x = 0$ .

c has dimensions of velocity ... what is it? It is NOT the flow velocity,

which is defined by q = flow rate = u\*rho, where rho = conserved density.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 03 2009 09 16 WED

TOPICS: Classification of pde.

Examples.

Kinematic waves and characteristics.

Definition of PDE. Rank PDE from general to simplest.

Quasi-linear, semi-linear, linear, high order, first order, systems, scalar ...

Simplest pde: scalar, first order in 2-D, and linear  $a*u_x + b*u_y = c*u + d$ , with a and b functions of (x, y).

Show it can be reduced to ode's along characteristics (this property defines it as a hyperbolic equation).

Characteristic form of the equations.

Allowed type of data: solution given along a curve that intersects (transversally) every characteristic in the region of interests once and only once.

Examples: a) linearized traffic flow and b) linearized river waves.

- --- General solution of the initial value problem.
- --- in (a) density waves move backwards through traffic.
- --- in (b) flood waves move forward of particles.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

```
Lecture 04 2009 09 21 MON
```

TOPICS: First order scalar pde.

Examples of solutions by characteristics.

Domain of influence.

Review characteristics.

Examples in detail:

1)  $x*u_x + y*u_y = 0$ ,

for  $y \ge 1$ , with u(x, 1) = F(x)

2)  $x*u_x + y*u_y = 1+y^2$ ,

for  $y \ge 1$ , with u(x, 1) = F(x)

Domain of dependence and domain of influence. Where is the solution defined and where it is not.

Examples showing solution not unique outside domain of influence:

For case (1), with  $F(x) = \exp(-x^2)$ , consider (in the plane without the origin = P0)

 $u1 = \exp(-x^2/y^2)$  ..... for  $x^2+y^2 > 0$ .

 $u = \exp(-x^2/y^2)$  ..... for  $y \ge 0$  and  $x^2+y^2 > 0$ . =  $\exp(-3*x^2/y^2)$  ..... for  $y \le 0$  and  $x^2+y^2 > 0$ .

Both u1 and u2 are smooth and solve the equation and given data, but they are not equal outside y >= 0 and  $x^2+y^2 > 0$ . Can construct infinitely many such u's.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

```
TOPICS: Domains of influence and dependence.
        Causality and uniqueness. Allowed boundary conditions.
        Examples.
Domain of definition and domain of dependence: where is the solution
  defined.
Implications for where conditions must be given:
  u_t + c(x) * u_x = 0 in an interval a < x < b.
  Causality:
     If c(a) > 0, BC's needed at x = a, and only then.
     If c(b) < 0, BC's needed at x = b, and only then.
  Draw characteristics for various example c = c(x).
Generalize method of characteristics to other first order scalar eqn.:
--- Semilinear.
--- Quasilinear.
Domain of definition of solution does not depend on data for linear.
Semilinear
  Do example: x*u_x + y*u_y = u^2, with u(x, 1) = F(x)
               Domain of definition depends on F [solution blows up
               along characteristics when F not zero].
  Do example u_t + c*u_x = u^2, with u(x, 0) = F(x).
              Solution not defined for all t > 0 along characteristics
               where F > 0.
Quasilinear
   Characteristics may cross, leading to multiple values.
  Start with u_t + c(u) * u_x = 0 and u(x, 0) = F(x).
   Solutions by characteristics.
   Implicit form of the solutions.
   Crossing of characteristics.
```

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 06 2009 09 28 MON

TOPICS: Graphical interpretation of solution by characteristics. Conservation. Wave steepening and breaking.

Back to the physics.

Continue with  $u_t + c(u)*u_x = 0$  and u(x, 0) = F(x).

Graphical interpretation of the solution by characteristics.

Show how conservation is satisfied by the characteristic laws.

Wave steepening and breaking (infinite derivatives).

Back to the physics:

Examine Traffic Flow and River Flows. What does breaking mean there?

Does it happen? What does solution do beyond that? Can we fix the
math.

model so it describes the behavior even after wave breaking?

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

TOPICS: Region of multiple values. Envelope of characteristics.

Continue with  $u_t + c(u) * u_x = 0$  and u(x, 0) = F(x).

Study boundary of the region of multiple values. Show that this is equivalent (as long as dc/du never vanishes) to looking at:  $c_t + c*c_x = 0$ , and c(x, 0) = C(x) = c(F(x)).

Relate boundary to maximums and minimums of x = z + c(z)\*t for fixed t. Write (parametric) equation for the curve.

Show curve is the envelope of the family of characteristics.

Envelope of a (smooth) family of curves: locus of crossings of infinitesimally close members of the family. Find equations.

Behavior of the boundary produced by a local minimum (or maximum) of the initial data C(x).

- --- Local minimum: cusp pointing down-time in space time.
- --- Local maximum: cusp pointing up-time in space time.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

TOPICS: More on envelopes. Infinite slopes at envelope. Shocks. Conservation and entropy. Irreversibility. Examples from traffic flow.

Continue with  $c_t + c*c_x = 0$  and c(x, 0) = C(x).

Show alternative definition of envelope of a smooth family of curves: Curve such that each point belongs to a family member, and is tangent

to the member here.

Hence: characteristics are tangent to the boundary of multiple values. Generic drawing of multiple valued region now justified.

Back to conservation form:  $\rho_t + q_x = 0$ .

Introduce shocks to knock out multiple-valued regions.

Now pde + discontinuities satisfying some conditions: Rankine-Hugoniot jump conditions (conservation)

Lax entropy conditions (causality)

System is now IRREVERSIBLE (show how information is lost at shocks).

Simple examples in Traffic Flow:

Red light turns green (show how Lax Entropy crucial here).

Green light turns red.

Green-red

Red-green

Meaning and (qualitative) comparison with reality.

Generic prescription for shocks forming out of a smooth solution.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 09 2009 10 07 WED

TOPICS: Continues lecture 8. More examples.

Continue with material in lecture 08. More examples.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 10 2009 10 13 TUE

TOPICS: Shocks in the presence of source terms. Example. Riemann problems and Godunov's type methods.

Shocks for equations with source terms. Example:

 $u_t + (0,5*u^2)_x = 1.$ 

Study characteristics, crossings and shock formation.

Derivation of the RH conditions.

Entropy conditions.

Riemann problems and numerical solutions. Godunov's type methods. Whole problem is encoded into the Riemann Problem, including the R.K. jump conditions and Entropy cond. If you can do the R.P., then you have, in principle, everything.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 11 2009 10 14 WED

TOPICS: The Riemann problem for the kinematic wave equation

with convex/concave flux.

Example of a conservation law with a point source term.

Riemann problem for:  $u_t + Q(rho)_x = 0$ 

Case Traffic Flow Q concave Case River Flows Q convex

Example: Riemann problem for  $u_t + (0.5*u^2) = delta(x)$ .

Give meaning to equation as a conservation law.

Point source term at the origin implies there is a discontinuity there, and appropriate jump conditions must be given, restricted by the need for causality.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

TOPICS: Shock structure and detailed physics.
Examples: Viscosity solution.

Traffic flow. Flood waves. Shallow water.

Shock structure as produced by more detailed physics.

Example: Viscosity solution in Traffic Flow
 Modify flux to q = Q(rho) - nu\*rho\_x. Justify, explain why.
 Now traveling wave solutions exist and satisfy the shock conditions

Explain why traveling waves should describe what happens near a shock when nu is ``small'' --- Scales inside the shock layer are much shorter/faster than outside. From point of view of the shock layer, both the shock speed, as well as the ``outside'' boundary conditions on the left and the right are steady. Hence shock layer should look like a steady traveling profile.

Example: Flood waves in rivers.

Viscosity solution cannot be justified physically. There is no analog of the ``look ahead'' preventive driving of Traffic flow. Fluid particles keep on going till catastrophe strikes: shock layer structure involves turbulent dissipation etc. No simple 1-D model for this seems possible.

Example: Numerical viscosity.

Even if ``non-physical'', the addition of viscosity (in a conservative form) to the equations, when shocks are known to occur, prevents the wave breaking and gives structures that (macroscopically) behave correctly. Hence, one can use this to stabilize numerical schemes.

Example: Shallow Water Wave equations and higher order terms.

Argue that, if one looks at the ``full'' equations for water waves, and then assumes sufficiently long waves, then the dominant effects should balance involving only first order derivatives. In addition, only two dependent variables should remain: depth and horizontal flow velocity vertical velocity cannot be important in this limit]. The independent variables reduce to time and horizontal coordinates. The result of this limit is the shallow water wave equations [assuming a flat bottom], which (assuming dependence on only one space dimensions) must have the form

```
h_t + (u^*h)_x and (rho^*h^*u)_t + ((rho^*h^*u)^*u + p)_x = 0,
```

because volume and momentum have to be conserved [if we ignore bottom friction]. Here p is the integrated pressure over the depth, and rho is the (constant) density. Since the pressure must be hydrostatic in this limit, we get  $p = (1/2)*g*rho*h^2$ , where g is the acceleration of gravity.

The equations above are then the same as isentropic Gas Dynamics for an ideal gas with gamma = 2.

Example: Shallow Water Wave equations and higher order terms.

The equations above have one-way solutions (simple waves). In addition, one can consider (in order to see what happens beyond wave breaking) adding to them higher order terms.

One easy way to add higher order terms is to go back to the original ``full'' equations, and linearize near a constant solution. Then the linear solutions can be found by Fourier analysis, and will be superpositions of modes with dependence  $\exp(i*k*x + lambda(k)*t)$ . In the long wave limit (k small) we can then expand lambda. Then we add to the equations above appropriate terms to recover this behavior.

When it is all said and done, and for one-way waves, one ends up with the following equation (now in a-dimensional variables)

$$u_t + (0.5*u^2)_x = nu*u_x + mu*u_xx$$

where mu and nu are small, and nu > 0. Unfortunately, this can be justified only for solutions that are small depertures from a constant because we obtain the correction terms from a linear analysis]. It, of course, does NOT capture the physics of turbulent hydraulic jumps. But is describes the regime where weak jumps live.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 13 2009 10 21 WED

TOPICS: Shallow water and higher order terms.

Traveling waves, shocks, and the effects of dispersion.

Solitons. Small dispersion limit.

Continue and finish material in lecture 12. In particular: % Traveling wave solutions for KdV:  $u_t + (0.5*u^2)_x = epsilon^2*u_xxx$ .

Can write them exactly, but easier to do it with phase plane analysis. Periodic traveling waves and solitary waves.

No shocks.

What happens in the epsilon small limit? Smooth I.V. should start evolving as  $u_t + u^*u_x = 0$ , approximately. But this then produces short scales, and the term epsilon^2\*u\_xxx kicks

in (preventing multiple values). However, no shocks can form (there are

none in this equation). What one observes is that short wave oscillations

[wave-length O(epsilon)] are generated near the points where  $u_t + u^*u_x = 0$  would produce infinite derivatives. These oscillations propagate away from these points, and the region with fast variations in the solution grows with time. No easy fix for cases like this. The small scales cannot be ignored (and shoved into a discontinuity) as in the cases where shocks form.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 14 2009 10 26 MON

TOPICS: pde and propagation of information.

Equations that allow weak singularities.

Examples.

How to send "information" via an equation: Insert "singularity" in equation. If the singularity is propagated by the equation, can use this

to send information (Alphabet with singularity type encoding "letters").

Works only if the equation allows singularities to propagate. Basically: Hyperbolic equations are equations with this property.

## Implementation:

Singularities must be "weak", so the equation makes sense even with them (i.e.: they appear in some sufficiently high order derivative). The curve/surface/whatever in space-time where the singularity appears is a characteristic.

Examples: Linear 1st order equations.

Semilinear and quasi-linear equations.

Rederive characteristics from this approach.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 15 2009 10 28 WED

Topics: Hyperbolicity and weak singularities.

Examples: Hamilton-Jacobi equation and characteristic form.

Eikonal equation. Multiple values.

Continue with lecture 14, and examples.

Example: equation H(u, p, q, x, y) = 0, where p = u\_x and q = u\_y.
Can singularities propagate in this equation?
 Yes, on second derivatives.
 Derive equation for locus of singularities, this gives an ode for x and y in terms of the solution [rays].
 Complete rays to full set of characteristic equations, for [x, y, p, q and u].

Example: Derive Eikonal equation and write characteristics. Geometrical interpretation of the characteristic solution.

Issue: rays can cross, leading to multiple values. Will investigate this in what follows.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 16 2009 11 02 MON

TOPICS: Continue with Hamilton-Jacobi equation. Characteristics, strips, and Monge cones. Eikonal as characteristic equation for wave equation in 2-D and 3-D.

Continue with lecture 15 and the equation H(u, p, q, x, y) = 0. The characteristics are curves in 5-D space. Interpretation of the characteristics as characteristic "strips", in 3-D.

Example: Eikonal equation, and Monge cones.

Eikonal equation as the equation for the characteristic surfaces of the wave equation in 2 or 3  $\rm D.$

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 17 2009 11 04 WED

TOPICS: Eikonal. Focusing and caustics. Description of the caustic.

Breakdown of approximation. Derivation of amplitude equation.

Characteristics for H(u, p, q, x, y) = 0; crossings and multiple values.

Example: Eikonal.

Focusing of convex wave-fronts and caustics.

Caustics as edge of the multiple-values region.

Caustics as envelope of the rays.

Caustics as the locus of the centers of curvature of the wave front. Typical form for caustic. Cusp at location of the first ray to focus.

Multiple-values not a problem: can have multiple waves at any given place.

However: as wavefronts approach the caustic, the expansion breaks down. Wavelength no longer shorter than all other length scales: wave front develops large curvature as it approaches caustic.

Hence: need another approximation near caustic.

Derivation of equation for amplitude A.

Conservation of energy (A^2) and blow up at caustics.

Energy moves along rays at speed c.

Characteristic form of the equation for the evolution of the amplitude.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

TOPICS: Eikonal. Amplitude and curvature along rays. Behavior near caustic. Caustic expansion.

WKBJ review. Turning points. Conneccion formulas and Airy functions. Matching.

Equation for amplitude along rays (constant coefficients wave equation):

dA/dt + kappa\*A = 0, where kappa = laplacian Phi = curvature. Explain:

Why kappa is curvature.

How to compute kappa along rays.

kappa behaves like 1/(t0 - t), so the amplitude blows up at the caustic.

## Caustic expansion:

Use coordinate system where one of the coordinates is distance from the caustic, and the other's coordinate lines are the normals to the caustic.

Strech differently in the two directions to match wave front shape (epsilon and epsilon $^2/3$ ).

Can produce description of solution near caustic, analogous to turning points in WKBJ. The two waves on one side, none in the other, given by the Airy function.

WKBJ, Turning point expansion, Airy.

WKBJ for problem  $y'' + (V(x)/epsilon^2) y = 0$ .

Oscillating and exponential solutions.

Amplitude blow up at turning points [V(x) = 0].

Turning point expansion [epsilon^2/3 layer].

Airy functions.

Behavior of the Airy function at +/- infinity.

Matching with WKBJ.

Show amplitude is epsilon $\{-1/6\}$  at turning point.

Note expansions overlap:

WKBJ valid for  $|x| \gg epsilon^2$  if turning point x = 0

--- wave vector is size  $\sqrt{|x|}/epsilon$ .

Turning point valid for |x| small.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Lecture 19 2009 11 16 MON

TOPICS: First order 1-D systems of equations. Classification. Hyperbolic systems and characteristics. Domains of dependence and influence. Examples.

First order systems of equations  $u_t + A*u_x = F(x, t, u)$ . where A = A(u, x, t).

Characteristics as singularity lines.

Characteristic form of the equations.

Example: linear, constant coefficients, no sources, case.

Hyperbolic if A is real diagonalizable.

Example: general solution for a hyperbolic system where A is constant and  $\mbox{\bf F}$  = 0.

In general, characteristics couple.

Domains of dependence and influence.

## Examples:

Linear Gas Dynamics (acoustics). Sound waves, general solution. Wave equation. Reduce to form above.

Klein Gordon equation. Characteristic form. Domains of dependece and influence.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 20 2009 11 18 WED

TOPICS: Examples of first order 1-D hypebolic systems. Linear acoustics. Wave equation. D'Alembert solution. Simple waves. Wave breaking. Shocks and shock conditions. Examples.

Continue with Lecture 19

Example: Linear acoustics in 1-D.

Exact solution by characteristics. System equivalent to wave equation.

Example: Wave equation. Solution of the initial value problem.

D'Alembert solution.

Domains of dependence and influence. Note: full wedge for data u and u\_t

Simple waves.

As in the scalar case, characteristics cross. Solution breaks down.

Breakdown of solutions: need to input appropriate physics. An example is when shocks apply.

Shocks for systems of conservation laws.

Rankine Hugoniot conditions.

Derivation of the Lax entropy conditions as needed for causality.

Example: Gas Dynamics and Shallow Water.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

TOPICS. Gas dynamics in 1-D. Characteristics, simple waves, Riemann Invariants, rarefaction waves, shocks and shock conditions. Riemann problem. Generalizations to N by N systems.

Example: Gas Dynamics in 1-D. Isentropic % -----Formulation in terms of mass Lagrangian coordinates.
Riemann Invariants and simple waves. Wave breaking.
Shock conditions (Rankine-Hugoniot ) for systems.
Lax entropy: explain how it works for causality.

Shocks in the p-v plane. Right and left shocks.

Lax entropy equivalent to compressive shocks.

Shock curve: for a fixed ``right'' state on a ``right'' shock,
 states in phase space (u, v) that can be reached by a shock.

Similar curve exists for left shocks, starting from left state.

Rarefaction curve: Same idea s for the shock curve. Write rarefactions using characteristic form, in particular: Riemann Invariants.

## RIEMANN PROBLEM:

Show how to solve using the shock/rarefaction curves as a sort of coordinate system in phase space. Describe how solution looks in space-time.

General systems: there are N shock curves and N rarefaction curves. At least locally they can be used to solve the Riemann problem. In general not always clear as the states on the right and left in a Riemann problem get further appart.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 22 2009 11 25 WED

TOPICS: Continue with lecture 21.

Continue/finish Lecture 21.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

TOPICS: Linear equations. Superposition. Normal modes and impulse problems (Green's functions). Heat equation in 1-D examples: various initial and boundary value problems.

Method of images.

## Linear equations:

Use superposition of special solutions to get general Standard methods for evolution equations:

- --- eigenmode analysis: separate time dependence as e^(lambda\*t)
- --- Greens functions: solve problems where the data is concentrated at a single location. Then integrate over these special solutions. Decompose general problem into 3 special ones:
- (1) Pure initial value. Homogeneous B.C. and no sources.
- (2) Pure boundary value. Zero initial values and no sources.
- (3) Pure sources. Zero initial values and homogeneous b.c.

EXAMPLES for the heat equation in 1-D. T\_t = T\_xx % ------#1 Initial values on the infinite line, no sources.% ------

- -- Solution by normal modes. Fourier transform.
- -- Green's Function. Use symmetries. Reduce problem to solving ode.
- -- Connection between approaches. Fourier transform of a delta.
- #2 Periodic initial values on the infinite line, no sources. % -----
- -- Solution by normal modes. Fourier series.
- -- Green's Function. Use periodic extension of Example #1 solution.
- -- Note: Normal modes good for t large. Green's function expression we have good for short times.
- #3 Initial data on half space x > 0. No sources. T(0, t) = 0.
- -- Green's function by the method of images: B.C. T = 0 equivalent to solution odd.
- #4 Initial data on half space x > 0. No sources.  $T_x(0, t) = 0$ .
- -- Green's function by the method of images: B.C.  $T_x = 0$  equivalent to solution even.
- #5 Initial data on an interval with T=0 at ends. No sources.
- -- Green's function by the method of images, and periodic extension.

Other examples one can do: (a) T=0 on one boundary and  $T_x=0$  on the other. (b) Robin boundary conditions. (c) Approach extends to simple sets in more than 1-D (later).

SYMMETRY: in all examples above G(x, y, t) = G(y, x, t). Generic. Motivate (no proof) by analogy with o.d.e. theory:  $u_t = A^*u$ , where A is symmetric. Then the solution operator  $exp(t^*A)$ , is also symmetric.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 24 2009 12 02 WED

TOPICS: Green's functions for signaling and source terms. Heat equation examples. Generalized functions.

Continue with lecture #23. Heat equation T\_t = T\_xx in 1-D.

## Further examples

- #6 Signaling problem in half space x>0. T given at x=0. No I.C.
- -- Green's Function. Use symmetries. Reduce problem to solving ode.
- #7 Signaling problems in an interval, with T or T\_x given on one side, and T or T\_x vanishing on the other.
- -- Green's functions by method of images.

START WITH SOURCE TERMS:  $T_t = T_{xx} + S$ , homogeneous IC and BC. Formulate problem.

To solve: re-interpret equation in terms of test functions.

DISTRIBUTIONS: functions as weights under the integral. Generalized functions: linear maps from test function onto constants. Examples: Delta function, Principal Value, Derivative of Delta function, etc. Define derivatives of generalized functions.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 25 2009 12 07 MON

TOPICS: Generalized functions.

Green's functions for heat equation in multi-D.

Reformulate initial value problem  $T_t = T_xx$ , T(x, 0) = G(x) in terms of test functions. In particular, what does the Green function satisfy.

Formulate Green's function problem for source term in terms of test functions. Note that we already know the solution!

Heat equation in 2-D/3-D: Unbounded space Green's function. 1-D theory extend easily to sets that tile the plane under reflections. Method of images and reflection symmetries. Illustrate with Strips, 2\*pi/N wedges, squares.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 26 2009 12 09 WED

TOPICS: Green's function. Poisson equation. Stokes equation. Example: stokes drag on a sphere.

Poisson equation in 3-D. Green's function (infinite domain).

Example of Green's functions applications: Stokes Flow.

Stokes flow equations. Justification.

Stokes flow produced by a point force.

Flow around a sphere held fixed in a flow constant far away from the

Flow around a sphere held fixed in a flow constant far away from the sphere.

Stokes drag.

Discussion of the problems caused by the slow decay of these solutions.
