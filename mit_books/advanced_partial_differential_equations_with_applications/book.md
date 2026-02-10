18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

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

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

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

Equations of type rho\_t + c(rho)\*rho\_x = 0.

c has dimensions of velocity ... what is it? It is NOT the flow velocity,

which is defined by q = flow rate = u\*rho, where rho = conserved density.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

Lecture 03 2009 09 16 WED

TOPICS: Classification of pde.

Examples.

Kinematic waves and characteristics.

Definition of PDE. Rank PDE from general to simplest.

 Quasi-linear, semi-linear, linear, high order, first order, systems, scalar ...

Simplest pde: scalar, first order in 2-D, and linear a\*u\_x + b\*u\_y = c\*u + d, with a and b functions of (x, y).

Show it can be reduced to ode's along characteristics (this property defines it as a hyperbolic equation).

Characteristic form of the equations.

Allowed type of data: solution given along a curve that intersects (transversally) every characteristic in the region of interests once and only once.

Examples: a) linearized traffic flow and b) linearized river waves.

- --- General solution of the initial value problem.
- --- in (a) density waves move backwards through traffic.
- --- in (b) flood waves move forward of particles.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

```
Lecture 04 2009 09 21 MON
```

TOPICS: First order scalar pde. Examples of solutions by characteristics. Domain of influence.

Review characteristics.

Examples in detail:

1) x\*u\_x + y\*u\_y = 0,

for y >= 1, with u(x, 1) = F(x)

2) x\*u\_x + y\*u\_y = 1+y^2,

for y >= 1, with u(x, 1) = F(x)

Domain of dependence and domain of influence. Where is the solution defined and where it is not.

Examples showing solution not unique outside domain of influence:

For case (1), with F(x) = exp(-x^2), consider (in the plane without the origin = P0)

u1 = exp(-x^2/y^2) ................. for x^2+y^2 > 0.

u = exp(-x^2/y^2) .................. for y >= 0 and x^2+y^2 > 0. = exp(-3\*x^2/y^2) ................ for y <=0 and x^2+y^2 > 0.

Both u1 and u2 are smooth and solve the equation and given data, but they are not equal outside y >= 0 and x^2+y^2 > 0. Can construct infinitely many such u's.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

```
TOPICS: Domains of influence and dependence. 
 Causality and uniqueness. Allowed boundary conditions. 
 Examples. 
Domain of definition and domain of dependence: where is the solution 
 defined. 
Implications for where conditions must be given: 
 u_t + c(x)*u_x = 0 in an interval a < x < b. 
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
 Start with u_t + c(u)*u_x = 0 and u(x, 0) = F(x). 
 Solutions by characteristics. 
 Implicit form of the solutions. 
 Crossing of characteristics.
```

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

Lecture 06 2009 09 28 MON

TOPICS: Graphical interpretation of solution by characteristics. Conservation. Wave steepening and breaking. Back to the physics.

Continue with u\_t + c(u)\*u\_x = 0 and u(x, 0) = F(x). Graphical interpretation of the solution by characteristics. Show how conservation is satisfied by the characteristic laws. Wave steepening and breaking (infinite derivatives).

Back to the physics:

 Examine Traffic Flow and River Flows. What does breaking mean there? Does it happen? What does solution do beyond that? Can we fix the math.

model so it describes the behavior even after wave breaking?

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

TOPICS: Region of multiple values. Envelope of characteristics.

Continue with u\_t + c(u)\*u\_x = 0 and u(x, 0) = F(x).

 Study boundary of the region of multiple values. Show that this is equivalent (as long as dc/du never vanishes) to looking at: c\_t + c\*c\_x = 0, and c(x, 0) = C(x) = c(F(x)).

Relate boundary to maximums and minimums of x = z + c(z)\*t for fixed t. Write (parametric) equation for the curve.

Show curve is the envelope of the family of characteristics.

 Envelope of a (smooth) family of curves: locus of crossings of infinitesimally close members of the family. Find equations.

Behavior of the boundary produced by a local minimum (or maximum) of the initial data C(x).

- --- Local minimum: cusp pointing down-time in space time.
- --- Local maximum: cusp pointing up-time in space time.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

TOPICS: More on envelopes. Infinite slopes at envelope. Shocks. Conservation and entropy. Irreversibility. Examples from traffic flow.

Continue with c\_t + c\*c\_x = 0 and c(x, 0) = C(x).

Show alternative definition of envelope of a smooth family of curves: Curve such that each point belongs to a family member, and is tangent

to the member here.

Hence: characteristics are tangent to the boundary of multiple values. Generic drawing of multiple valued region now justified.

Back to conservation form: \rho\_t + q\_x = 0.

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

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

Lecture 09 2009 10 07 WED

TOPICS: Continues lecture 8. More examples.

Continue with material in lecture 08. More examples.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

Lecture 10 2009 10 13 TUE

TOPICS: Shocks in the presence of source terms. Example. Riemann problems and Godunov's type methods.

Shocks for equations with source terms. Example:

u\_t + (0,5\*u^2)\_x = 1.

Study characteristics, crossings and shock formation.

Derivation of the RH conditions.

Entropy conditions.

Riemann problems and numerical solutions. Godunov's type methods. Whole problem is encoded into the Riemann Problem, including the R.K. jump conditions and Entropy cond. If you can do the R.P., then you have, in principle, everything.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

## Lecture 11 2009 10 14 WED

TOPICS: The Riemann problem for the kinematic wave equation

with convex/concave flux.

Example of a conservation law with a point source term.

Riemann problem for: u\_t + Q(rho)\_x = 0

 Case Traffic Flow Q concave Case River Flows Q convex

Example: Riemann problem for u\_t + (0.5\*u^2) = delta(x).

Give meaning to equation as a conservation law.

Point source term at the origin implies there is a discontinuity there, and appropriate jump conditions must be given, restricted by the need for causality.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

TOPICS: Shock structure and detailed physics. Examples: Viscosity solution.

Traffic flow. Flood waves. Shallow water.

Shock structure as produced by more detailed physics.

Example: Viscosity solution in Traffic Flow Modify flux to q = Q(rho) - nu\*rho\_x. Justify, explain why. Now traveling wave solutions exist and satisfy the shock conditions (both Rankine Hugoniot and Entropy).

 Explain why traveling waves should describe what happens near a shock when nu is ``small'' --- Scales inside the shock layer are much shorter/faster than outside. From point of view of the shock layer, both the shock speed, as well as the``outside'' boundary conditions on the left and the right are steady. Hence shock layer should look like a steady traveling profile.

Example: Flood waves in rivers.

 Viscosity solution cannot be justified physically. There is no analog of the ``look ahead'' preventive driving of Traffic flow. Fluid particles keep on going till catastrophe strikes: shock layer structure involves turbulent dissipation etc. No simple 1-D model for this seems possible.

Example: Numerical viscosity.

 Even if ``non-physical'', the addition of viscosity (in a conservative form) to the equations, when shocks are known to occur, prevents the wave breaking and gives structures that (macroscopically) behave correctly. Hence, one can use this to stabilize numerical schemes.

Example: Shallow Water Wave equations and higher order terms.

 Argue that, if one looks at the ``full'' equations for water waves, and then assumes sufficiently long waves, then the dominant effects should balance involving only first order derivatives. In addition, only two dependent variables should remain: depth and horizontal flow velocity vertical velocity cannot be important in this limit]. The independent variables reduce to time and horizontal coordinates. The result of this limit is the shallow water wave equations [assuming a flat bottom], which (assuming dependence on only one space dimensions) must have the form

```
 h_t + (u*h)_x and 
(rho*h*u)_t + ((rho*h*u)*u + p)_x = 0,
```

because volume and momentum have to be conserved [if we ignore bottom friction]. Here p is the integrated pressure over the depth, and rho is the (constant) density. Since the pressure must be hydrostatic in this limit, we get p = (1/2)\*g\*rho\*h^2, where g is the acceleration of gravity.

 The equations above are then the same as isentropic Gas Dynamics for an ideal gas with gamma = 2.

Example: Shallow Water Wave equations and higher order terms.

The equations above have one-way solutions (simple waves). In addition, one can consider (in order to see what happens beyond wave breaking) adding to them higher order terms.

One easy way to add higher order terms is to go back to the original ``full'' equations, and linearize near a constant solution. Then the linear solutions can be found by Fourier analysis, and will be superpositions of modes with dependence exp(i\*k\*x + lambda(k)\*t). In the long wave limit (k small) we can then expand lambda. Then we add to the equations above appropriate terms to recover this behavior.

When it is all said and done, and for one-way waves, one ends up with the following equation (now in a-dimensional variables)

$$u_t + (0.5*u^2)_x = nu*u_x + mu*u_xx$$

where mu and nu are small, and nu > 0. Unfortunately, this can be justified only for solutions that are small depertures from a constant because we obtain the correction terms from a linear analysis]. It, of course, does NOT capture the physics of turbulent hydraulic jumps. But is describes the regime where weak jumps live.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

Lecture 13 2009 10 21 WED

TOPICS: Shallow water and higher order terms. Traveling waves, shocks, and the effects of dispersion. Solitons. Small dispersion limit.

Continue and finish material in lecture 12. In particular: % Traveling wave solutions for KdV: u\_t + (0.5\*u^2)\_x = epsilon^2\*u\_xxx.

Can write them exactly, but easier to do it with phase plane analysis. Periodic traveling waves and solitary waves. No shocks.

What happens in the epsilon small limit? Smooth I.V. should start evolving as u\_t + u\*u\_x = 0, approximately. But this then produces short scales, and the term epsilon^2\*u\_xxx kicks

 in (preventing multiple values). However, no shocks can form (there are

 none in this equation). What one observes is that short wave oscillations

 [wave-length O(epsilon)] are generated near the points where u\_t + u\*u\_x = 0 would produce infinite derivatives. These oscillations propagate away from these points, and the region with fast variations in the solution grows with time. No easy fix for cases like this. The small scales cannot be ignored (and shoved into a discontinuity) as in the cases where shocks form.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

Lecture 14 2009 10 26 MON

TOPICS: pde and propagation of information. Equations that allow weak singularities. Examples.

How to send "information" via an equation: Insert "singularity" in equation. If the singularity is propagated by the equation, can use this

to send information (Alphabet with singularity type encoding "letters").

Works only if the equation allows singularities to propagate. Basically: Hyperbolic equations are equations with this property.

## Implementation:

 Singularities must be "weak", so the equation makes sense even with them (i.e.: they appear in some sufficiently high order derivative). The curve/surface/whatever in space-time where the singularity appears is a characteristic.

Examples: Linear 1st order equations. Semilinear and quasi-linear equations. Rederive characteristics from this approach.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

Lecture 15 2009 10 28 WED

Topics: Hyperbolicity and weak singularities. Examples: Hamilton-Jacobi equation and characteristic form. Eikonal equation. Multiple values.

Continue with lecture 14, and examples.

Example: equation H(u, p, q, x, y) = 0, where p = u\_x and q = u\_y. Can singularities propagate in this equation? Yes, on second derivatives. Derive equation for locus of singularities, this gives an ode for x and y in terms of the solution [rays]. Complete rays to full set of characteristic equations, for [x, y, p, q and u].

Example: Derive Eikonal equation and write characteristics. Geometrical interpretation of the characteristic solution.

 Issue: rays can cross, leading to multiple values. Will investigate this in what follows.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

## Lecture 16 2009 11 02 MON

TOPICS: Continue with Hamilton-Jacobi equation. Characteristics, strips, and Monge cones. Eikonal as characteristic equation for wave equation in 2-D and 3-D.

Continue with lecture 15 and the equation H(u, p, q, x, y) = 0. The characteristics are curves in 5-D space. Interpretation of the characteristics as characteristic "strips", in 3- D.

Example: Eikonal equation, and Monge cones.

Eikonal equation as the equation for the characteristic surfaces of the wave equation in 2 or 3 D.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

Lecture 17 2009 11 04 WED

TOPICS: Eikonal. Focusing and caustics. Description of the caustic. Breakdown of approximation. Derivation of amplitude equation.

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

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

TOPICS: Eikonal. Amplitude and curvature along rays. Behavior near caustic. Caustic expansion. WKBJ review. Turning points. Conneccion formulas and Airy functions. Matching.

Equation for amplitude along rays (constant coefficients wave equation):

 dA/dt + kappa\*A = 0, where kappa = laplacian Phi = curvature. Explain:

Why kappa is curvature.

How to compute kappa along rays.

kappa behaves like 1/(t0 -t), so the amplitude blows up at the caustic.

## Caustic expansion:

 Use coordinate system where one of the coordinates is distance from the caustic, and the other's coordinate lines are the normals to the caustic.

 Strech differently in the two directions to match wave front shape (epsilon and epsilon^2/3).

 Can produce description of solution near caustic, analogous to turning points in WKBJ. The two waves on one side, none in the other, given by the Airy function.

WKBJ, Turning point expansion, Airy.

WKBJ for problem y'' + (V(x)/epsilon^2) y = 0.

Oscillating and exponential solutions.

Amplitude blow up at turning points [V(x) = 0].

Turning point expansion [epsilon^2/3 layer].

Airy functions.

Behavior of the Airy function at +/- infinity.

Matching with WKBJ.

Show amplitude is epsilon^{-1/6} at turning point.

Note expansions overlap:

WKBJ valid for |x| >> epsilon^2 if turning point x = 0

--- wave vector is size \sqrt{|x|}/epsilon.

Turning point valid for |x| small.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

## Lecture 19 2009 11 16 MON

TOPICS: First order 1-D systems of equations. Classification. Hyperbolic systems and characteristics. Domains of dependence and influence. Examples.

First order systems of equations u\_t + A\*u\_x = F(x, t, u). where A = A(u, x, t).

Characteristics as singularity lines.

Characteristic form of the equations.

Example: linear, constant coefficients, no sources, case.

Hyperbolic if A is real diagonalizable.

Example: general solution for a hyperbolic system where A is constant and F = 0.

In general, characteristics couple.

Domains of dependence and influence.

## Examples:

 Linear Gas Dynamics (acoustics). Sound waves, general solution. Wave equation. Reduce to form above.

 Klein Gordon equation. Characteristic form. Domains of dependece and influence.

---

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

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

| MIT OpenCourseWare |
|--------------------|
| http://ocw.mit.edu |

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

# Incompressible, inviscid, fluid flow in a narrow cylindrical pipe with elastic thin walls.

Rodolfo R. Rosales\* September 15, 2003

#### **Contents**

- 1 Physical setup, assumptions, and notation.
- 2 Derivation of the governing equations. 4


3 Linearized governing equations.

## 1 Physical setup, assumptions, and notation.

Consider a flexible pipe, filled with a **fluid under a pressure** p. For the tube not to collapse, and flow to be possible, it must be  $p > p_0 =$ **outside pressure** — we assume  $p_0 =$ **constant.** Further, let x =**length coordinate along the tube axis.** We now make the following:

#### Structural Assumptions.

- S1. The fluid is incompressible. Let  $\rho = \text{constant be its density}$ .
- S2. The fluid is inviscid (no dissipation by the fluid motion). We also ignore gravity and other (possible) body forces on the fluid. The only force acting on the fluid is the pressure.
- **S3.** The walls of the tube/pipe are:
  - S3-1. Homogeneous. They have the same properties (thickness, etc.) everywhere.

<sup>\*</sup>MIT, Department of Mathematics, room 2-337, Cambridge, MA 02139.

- S3-2. Thin and flexible. Thus we will assume that they offer no resistance to bending. Furthermore, this assumption allows us to ignore the wall thickness, treating it as a surface. "Thin" here means this: let L be the scale over which motion occurs see "dynamic assumptions" below, and let h be the tube wall thickness. Then  $L \gg h$ , so that the amount of bending in the longitudinal direction is small enough to have negligible effects on the force balances. This also has the consequence of keeping the tube cross-section circular see "dynamic assumptions" below, so that there is no bending in the transversal direction.
- S4. The tube perimeter is constant i.e.: it does not depend on the coordinate x along the tube. It then follows (from S3-1) that, under steady state conditions [so that the fluid pressure is the same everywhere] the pipe has cylindrical shape. Let  $2\pi a_0$  be the repose (no forces) perimeter of the tube; i.e. let the repose radius of the tube be  $a_0 = \text{constant}$ .

#### Dynamic Assumptions.

- **D1.** Long wave assumption. The scale *L* over which the motion occurs is much bigger than the tube diameter or, for that matter, the tube wall's thickness. This has several important consequences:
  - **D1-1.** Cylindrical geometry. The long wave assumption implies that, at any given point x along the tube, the pressure is (essentially) constant so the cross-section of the tube takes a circular shape. Thus, the geometry is locally cylindrical, and can be described by the radius = a = a(x, t) of the circular cross-section of the fluid region inside the tube.
  - **D1-2. One dimensional approximation.** The long wave approximation implies that we can neglect any fluid motions in directions transversal to the tube axis. Thus the **fluid dynamics can be described by the two scalar functions:** p = p(x,t) =**pressure,** and u = u(x,t) =**flow velocity along the tube.**
  - **D1-3.** Transversal wall forces only. The long wave approximation implies that the strain on the walls is mainly along the perimeter, with relatively little stretching (or bending) in the longitudinal direction. Thus, we can assume that the **only force by the walls**

is a "tension" along the perimeter, trying to pull the perimeter back to its repose length of  $2\pi a_0$ .

**D2. Elastic regime.** The amount of wall stretching produced by the motion is small enough (and happens slowly enough) that the walls respond elastically. That is to say: the tube walls oppose stretching with a force that depends only on the amount of stretching.

It is important to notice that this assumption involves not just space scales, but time scales as well. If the deformations are too large, the walls will not respond elastically — permanent deformations will occur, etc. Furthermore, when the deformations occur too fast (even if they are small) dissipation can become important. Of course: what "too large" or "too fast" means depends on the physical properties of the tube walls.

Thus, we can write, for the tension introduced in (D1-3) a formula of the form:

$$T = f\left(\frac{\Delta a}{a_0}\right),\tag{1.1}$$

where  $\Delta a = a - a_0$  measures the amount of stretching (the tube perimeter changes by  $2\pi\Delta a$ ), f is a function characterizing the elastic response of the walls, and Tdx is the tension force along the perimeter of a "slice" of the tube of length dx.

**D3.** Neglect wall inertia. We will assume that the mass of the walls is negligible compared to the fluid mass. This will happen if, for example,  $a \gg h$ , where h is the wall thickness—this is a stronger assumption than the one in (S3-2), for which only  $L \gg h$  was required.

Remark 1.1 Notice that, at least for now, we are not making the assumption of small deviations from a steady state<sup>1</sup>. In particular, this would imply that a is nearly constant:  $a \approx a_s$  — where  $a_s - a_0$  is the stretching needed to balance the equilibrium steady state pressure. In this case Hooke's law applies, and equation (1.1) can be linearized to

$$\delta T = E h \frac{\delta a}{a_s},\tag{1.2}$$

<sup>&</sup>lt;sup>1</sup>Flow at constant speed and constant pressure.

where  $\delta a = a - a_s$ , E is the Young's modulus for the wall material,  $\delta T = T - T_s$  is the deviation of the tension from its equilibrium value  $T_s$ , and h is the wall thickness — which can be assumed constant in this approximation.

Of course, if we do not make the small deviation from a steady state assumption, we cannot assume that the wall thickness h is a constant. The variations in h do, of course, affect the forces produced by the walls. We can, however, assume that the wall thickness is a function of the stretching, and thus we can incorporate the effect of these variations into the force law (1.1) — without being forced to track an extra variable h = h(x, t).

We will make the small deviation from a steady state assumption later. This assumption leads to a great simplification of the equations (linearization).

### 2 Derivation of the governing equations.

We are now ready to derive the governing equations, using conservation of mass and momentum. Conservation of Mass. The fluid mass must be conserved. Since  $S = \pi a^2$  is the cross-sectional area of the tube, it follows that the mass density (per unit length dx) is  $\rho S$ , and the mass flow is  $\rho uS$ . Since there are no mass sources, we must have:

$$(\rho S)_t + (\rho u S)_x = 0 \qquad \Longleftrightarrow \qquad (S)_t + (u S)_x = 0. \tag{2.1}$$

By the way: notice that the mass in the tube walls does not "flow". Thus we do not have to worry about it when considering the equation for the conservation of mass (or, for that matter, the equation for the conservation of momentum).

Conservation of Momentum. The fluid linear momentum must be conserved. The linear momentum density per unit length dx is  $\rho uS$ . The linear momentum flux has two components: the advective component  $\rho u^2S$  (momentum carried by the flow), and the momentum flux due to the pressure force pS across the tube section. In addition, there is a momentum source per unit length, caused by the forces (in the flow direction) on the fluid by

the tube walls. It should be clear that this momentum source is given by<sup>2</sup>

$$M_s = 2\pi a p \frac{a_x}{\sqrt{1 + a_x^2}} \approx 2\pi a p a_x = p S_x, \tag{2.2}$$

where, from the long wave assumption, we have used that:  $1 + a_x^2 \approx 1$ . Thus we have

$$(\rho uS)_t + \left(\rho u^2 S + pS\right)_x = pS_x \qquad \Longleftrightarrow \qquad (uS)_t + \left(u^2 S\right)_x + \frac{S}{\rho} p_x = 0. \tag{2.3}$$

Using (2.1), this last equation can also be written in the form:

$$u_t + uu_x + \frac{1}{\rho}p_x = 0. {(2.4)}$$

**Equation for the pressure.** The pressure in the fluid p = p(x, t) must be balanced by both the pressure outside the tube  $p_0$ , and the elastic forces exerted by the tube walls. At the tube wall, the pressure force can be decomposed into two components:

**P2.** Radial force (per unit area) ...... 
$$p \frac{1}{\sqrt{1+a_x^2}} \approx p$$

As a consequence of the long wave approximation, the longitudinal force is much smaller than the radial one — this is consistent with **(D1-3)**: the wall elastic forces are transversal only, corresponding to stretching mainly in the transversal direction.

Because the curvature of a circle of radius a is 1/a, the tension T per unit length on the tube walls (see equation (1.1)) results in a radial force — per unit area – by the tube walls (see remark 2.1) of magnitude

Force 
$$=\frac{1}{a}T = \frac{1}{a}f\left(\frac{\Delta a}{a_0}\right)$$
 (2.5)

per unit area. Because of the assumption (**D-3**), this force — added to the one caused by the external pressure — must balance the radial force (**P2**) by the fluid in the pipe. Thus, we end up with the following formula for the pressure p = p(x, t):

$$p - p_0 = \frac{1}{a}T = \frac{1}{a}f\left(\frac{\Delta a}{a_0}\right). \tag{2.6}$$

 $<sup>^2\</sup>mathrm{See}$  (P1): "wall longitudinal force per unit area"  $\times$  "tube perimeter" = "momentum source".

**Final Equations.** We have now a complete system of equations

$$0 = S_t + (u S)_x, 
0 = u_t + u u_x + \frac{1}{\rho} p_x,$$
(2.7)

where p is given by equation (2.6), and  $S = \pi a^2$ 

Remark 2.1 Consider a string under tension, restricted to lie flat in a plane. Let the string be described (parametrically) by x = x(s) and y = y(s), where s is the arclength. Let T = T(s) be the tension along the string. We now ask the question: What force must be applied to the string, to keep it from moving under the effects of the tension?

In order to answer this question, we first note that the tension produces a force tangent to the string at each point, of magnitude T. The tangent vector to the string is given by  $\mathbf{t} = \mathbf{t}(s) = (\cos \theta, \sin \theta)$  — where  $\cos(\theta) = dx/ds$ , and  $\sin(\theta) = dy/ds$ . Thus, the net force on the element of string between s and s + ds is given by:

Force = 
$$T(s + ds) \mathbf{t}(s + ds) - T(s) \mathbf{t}(s) = \frac{d}{ds} (T \mathbf{t}) ds$$

Now  $d\mathbf{t}/ds = \kappa \mathbf{n}$ , where  $\kappa = d\theta/ds$  is the curvature of the string, and  $\mathbf{n} = (-\sin \theta, \cos \theta)$  is the unit normal to the string. Thus the net force on the string produced by the tension can be decomposed as follows:

Force 
$$=\frac{dT}{ds}\mathbf{t} + T\kappa\mathbf{n}$$
,

where the first component is longitudinal, and the second is transversal. This is the force that must be balanced to keep the string from moving. In particular, note that if the tension is constant, only a force normal to the string is produced—this is the result used above to obtain equation (2.5).

#### 3 Linearized governing equations.

A simple solution to the governing equations is that corresponding to a steady state, where  $u = u_s$ ,  $a = a_s$ ,  $S = S_s$ , and  $p = p_s$  are all constants. Of course, we must have  $S_s = \pi a_s^2$  and

$$p_s - p_0 = \frac{1}{a_s} f\left(\frac{a_s - a_0}{a_0}\right) . {(3.1)}$$

Note that, because the equations are Galilean invariant, we can assume (without loss of generality) that  $u_s = 0$ .

Consider now solutions that are infinitesimal perturbations of a steady state solution, so that we can write:  $u = \tilde{u}$ ,  $a = a_s + \tilde{a}$ ,  $S = S_s + \tilde{S}$ , and  $p_s + \tilde{p}$  — where the variables with tildes are infinitesimal. Then<sup>3</sup> we have:

$$\tilde{S} = 2 \pi \, a_s \, \tilde{a}$$
 and  $\tilde{p} = \frac{1}{a_s^2} \, E \, h \, \tilde{a} = \frac{\sqrt{\pi} \, E \, h}{2 \, S_s^{3/2}} \, \tilde{S} = \frac{\rho}{S_s} \, c^2 \, \tilde{S} \, ,$ 

where  $c^2 = \frac{\sqrt{\pi} E h}{2 \rho \sqrt{S_s}}$ , and c > 0 is a velocity. Thus the governing equations become

$$0 = S_t + S_s u_x, 
0 = u_t + \frac{c^2}{S_s} S_x,$$
(3.2)

where we have dropped the tildes. This yields the wave equation  $0 = u_{tt} - c^2 u_{xx} = S_{tt} - c^2 S_{xx}$  for both u and S.

THE END.

<sup>&</sup>lt;sup>3</sup>For the second formula here, see equations (1.2) and (2.5).

---

| MIT OpenCourseWare |
|--------------------|
| http://ocw.mit.edu |

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

## Branch Points and Branch Cuts (18.04, MIT).

Rodolfo R. Rosales\*

October 11, 1999

# These notes are in the process of being written.

Updates will be made from time to time. Check the date to make sure you have the last version.

## **Contents**

| 1            | Intr | oduction.                                                               | 3  |
|--------------|------|-------------------------------------------------------------------------|----|
| 2            | A fe | ew simple examples.                                                     | 10 |
|              | 2.1  | Branch cuts and branch points for $\log(z-1)$                           | 10 |
|              | 2.2  | Branch cuts and branch points for $\log(z^2-1)$                         | 11 |
|              | 2.3  | Branch cuts and branch points for $\log \left( \frac{z-1}{z+1} \right)$ | 13 |
|              | 2.4  | Branch cuts and branch points for $z^a$                                 | 15 |
|              | 2.5  | Branch cuts and branch points for $z^a(z-a)^b$                          | 17 |
| $\mathbf{L}$ | ist  | of Figures                                                              |    |
|              | 1.1  | Closed path in Complex Plane                                            | 3  |
|              | 1.2  | Another closed path                                                     | 3  |
|              | 1.3  | Yet another closed path                                                 | 5  |
|              | 1.4  | Region in the Complex Plane.                                            | 5  |
|              | 1.5  | Big region in the Complex Plane                                         | 5  |
|              | 1.6  | Cut Complex Plane                                                       | 6  |

<sup>\*</sup>MIT, Department of Mathematics, room 2-337, Cambridge, MA 02139.

Some possible choices of branch cuts for  $z^a(z-1)^b$ . . . . . . . . . . . . . . . . . . .


2.7

Consider the complex valued function1

$$\log(z) = \ln(r) + i\theta, \tag{1.1}$$

where z = rei , with r > 0 and real. As one goes around the closed path in Figure 1.1, starting counter-clockwise from point A and returning to A, it is clear that 0 increases to 0 +2. Therefore, upon tracing the path, we have:

$$\log(A) \to \log(A) + 2\pi i \,. \tag{1.2}$$

This means that log(z) does not return to its original value when one tries to dene it continuously along the closed path. Thus we have an identity crisis: which value should we choose for log(z) at A? Of course, A is arbitrary, so this problem arises at every point in the complex plane!

Before answering this question let us rst note that returns to its original value as z traces the closed path in Figure 1.2. Thus one may ask the question:

> What is the dierence between the paths in these two gures which makes the behavior of log(z) so entirely dierent as the closed paths are traced?

<sup>1</sup>Here ln(r) denotes the real valued natural logarithm of r.

The answer is that the rst path encloses the origin z = 0, while the second path does not. This is why increases by 2 asone goes around the rst path, but does not as one goes around the second path. Thus the origin is a branch point of log(z).

Denition 1.1 The point z0 is cal led a branch point | for the complex (multiple) valued function f (z) | if the value off (z) does not return to its initial value as a closed curve around the point is traced (starting from some arbitrary point on the curve), in such a way that f varies continuously as the path is traced.

There are some important clarications that we should make about this denition:

- First: What matters here is the local behavior of the the function f near z0. What may happen on paths that are some distance away from z0 is not relevant. To be more precise, the behavior must occur for all the curves that enclose the point and are suciently close to it. For example, consider again the case of the function log(z), take z0 = 2 and <sup>a</sup> closed curve around z = 2 that also encloses z = 0. The value of log(z) wil l change as this curve is traced, but this does not make z = 2 a branch point of log(z). In fact, for curves close to z = 2 there is no change, hence z = 2 is not a branch point of log(z)!).
- Second: There is the presumption here that there is some neighborhood of z0 where <sup>f</sup> (z) is dened (albeit with multiple values) and that for any point close enough to z0 (but not for z0 itself !) we can nd a smal l region around the point where f can be dened in a single valued and (at least) continuous fashion. Without this the notion of \moving along a curve with f changing continuously along the path" does not make any sense | and with it, it becomes quite natural: when moving along the path, we use this local and continuous denitions for f (z) to have continuous variation in the values of f as a function of the motion on the path. In the case of the log(z) function, it is clear that for any z1 6= 0 in the Complex Plane, we can always restrict the angle to some smal l range and get a (local) denition (near z1) for log(z) which is single valued and continuous (see what fol lows, in particular Figure 1.4).

The concept of \local patches" around points (introduced in denition 1.1 above) where the function can be dened in a \nice and well behaved" way, will become central later on: when the notion of analytic continuation is introduced. This notion gives a \general way" to think about these issues (and many others). Thus, it is important to get \used" to this kind of thinking early on.

Note that log(z) changes by 2i on the path in Figure 1.1, because this path encloses the origin in the counterclockwise sense | and only once. If a path enclosing the origin (once) in the clockwise sense is followed, then log(z) changes by 2i. If a path encloses the origin twice in the counterclockwise sense, as in this gure, then log(z) changes by 4i. And so on,any integer multiple of 2 can be obtained, depending on how many times the path winds around the origin | and in

It is clear that if we restrict ourselves to the region R in Figure 1.4, we may dene log(z) uniquely. This is because there is no closed path lying inside R that encloses the origin. To dene log(z) in

R, we may simply choose the angle to be between zero and 0:5 for any point in R. This choice is consistent throughout R. Alternatively, we may dene in region R to be between 2 and 2:5.

This definition of  $\log(z)$  differs from the previous one, but it is also perfectly consistent and equally acceptable. There are, therefore, several satisfactory definitions of  $\log(z)$  in region R. It is also easy to check that, no matter which definition (or **branch**) of  $\log(z)$  is chosen, we have:

$$\frac{d}{dz}\log(z) = \frac{1}{z}.$$

Thus  $\log(z)$  is analytic in region R, as long as a **branch** of  $\log(z)$  is chosen.

Obviously, we may enlarge the region R, and  $\log(z)$  in this enlarged region can still be defined uniquely. What is the largest region possible? Let us recall that the function of  $\log(z)$  is defined uniquely in any region which does not contain a closed path around the origin. In particular, it can be the one in Figure 1.5. Expanding this region to the extreme limit, we may define  $\log(z)$  uniquely in the entire Complex Plane, with an infinitesimally small region around the positive real x-axis excluded. This is the z-plane cut along the positive x-axis illustrated in Figure 1.6. This cut plane contains no closed path enclosing the origin.

The value of  $\log(z)$  at A (a point infinitesimally close to and above the positive x-axis), differs from that at B, which is infinitesimally close to A but is below the positive x-axis. Thus,  $\log(z)$  (as defined by this figure) is discontinuous across the  $branch\ cut$  — taken here as the positive x-axis. There is no contradiction: the points A and B are separated by the branch cut, and are  $regarded\ as\ two\ different\ points$ . A branch cut is like the great wall of China, and there are two different worlds inside and outside of the wall.

A deeper way to describe  $\log(z)$  is to think of  $\log(z)$  as a function defined **not** on a plane but on a **parking garage** which has many levels (infinitely many, actually). As we start out from point A and follow the path in Figure 1.1, we end up **not** at the same point in the garage, but at a point one level above point A. The value of  $\log(z)$  depends on which level in the garage we are at. Therefore,

although the value of log(z) changes by 2i, there is no \identity" crisis. Mathematicians call these levels Riemann sheets. If we start out at a point on the rst level of the garage2 (the rst Riemann sheet) and move around the origin in the counterclockwise direction n times, we arrive at the (n + 1)th level of the garage (the (n + 1)th Riemann sheet) and the function changes by

$$\log(z) \to \log(z) + 2n\pi i$$
.

Since n may be any integer, positive or negative, log(z) has innitely many Riemann sheets (lots of space to park your car). The whole surface constructed this way|over which log(z) is dened as a single valued analytic function (i.e.: the whole parking garage) | is called the Riemann surface for log(z). Note that dierent functions will have dierent Riemann surfaces associated with them. In particular: if the function is single valued to begin with (thus, has no branch points) then its Riemann surface will be just the Complex plane. For example, this would be the case when f (z) is a polynomial.

Remark 1.1 If we consider the cut plane as in Figure 1.6 and dene at A to be zero, then we could use the cut plane in Figure 1.6 to represent the rst Riemann sheet. This, however, is just a convenient choice; as we said before: which sheet we cal l the \rst" is somewhat arbitrary. As a matter of fact, even the notion of \sheet" is somewhat arbitrary: al l the \sheets" are joined together in one continuous surface (the Riemann Surface) and the division of this surface into sheets is just a convenient way of splitting itup into easy to understand units.

Let us clarify the point made in the previous paragraph a bit more: the analogy with a \parking garage" made before is convenient, but a bit misleading. Garages tend to be \natural ly" divided into \
oors" (the \sheets"), but this is not so here. A closer analogy would be a garage which is al l ramp, continuously curving up and up (with the cars parked on the side of the ramp). Then where you decide to put the division between one oor and the next becomes rather arbitrary | but you might do it anyway, so that nding where a particular car is parked can be done without having to search the whole garage.

Let us point out that there is no reason for insisting that the branch cut be on the positive real axis. We may (for example) choose the branch cut to be on the negative real axis, as in Figure 1.7. If we

<sup>2</sup>Which one is the \rst" level is arbitrary, of course. We pick one by throwing a dice with innitely many faces.

choose at A in Figure 1.7 to be zero, then the cut plane in here has << and represents half a level up and half a level down in the garage | in terms of of our prior way of thinking (introduced by Figure 1.6). But we may also just change our \sheet boundaries" and take the cut plane given by Figure 1.7 as the \rst sheet" (see Remark 1.1). We may also choose the branch cut to be any straight line originating from the origin and going all the way to innity. In fact,

the branch cut does not even have to be a straight line! We may choose it to be the curve in Figure 1.8, for example<sup>3</sup> . The function log(z) is dened uniquely in the cut plane of Figure 1.8, albeit in a (perhaps) \strange" way.

The point z = 0 is the only branch point of log(z) in the nite z-plane. Now we ask the question: is z = <sup>1</sup> a branch point of log(z)? To answer this question, we must rst clarify what we mean by z = <sup>1</sup> being a branch point. Well, it is not that hard to generalize denition 1.1 to include the point at innity. It is just a matter of interpreting a \closed curve around z = 1" as simply meaning a \very large loop"; in fact we want the behavior to occur for all loops that are large enough (in the same spirit as the rst \clarication" to denition 1.1). Notice that, if we think of the point

<sup>3</sup>To continue with the analogy of the parking garage: imagine that the lines dividing parking sections were painted by a slightly drunk attendant.

z = <sup>1</sup> as just one more point in the Riemann Sphere, then this denition of \closed curve around z = 1" is the natural one and it makes innity just like any other point in the Riemann Sphere.

Another (equivalent) way of thinking of the question in the prior paragraph, is to rst \map" <sup>1</sup> into a point on the nite Complex Plane and then apply to it the prior denition. This we can do using the inversion map (just a fancy word for saying we will take inverses). Namely, introduce the new variable by:

$$z \equiv \frac{1}{\zeta} \,. \tag{1.3}$$

Then = 0 corresponds to z = <sup>1</sup> and we have

$$\log(z) = -\log(\zeta).$$

Thus, since = 0 is a branch point of log( ), we conclude that z = <sup>1</sup> is a branch point of log(z). We point out that these two ways of dealing with the point at innity are equivalent, so which one is used for any given problem is just a matter of convenience. For some functions f (z) one way may lead to simpler manipulations than the other, in which case it would be (generally) the approach to use.

Finally: it should now be clear that a branch cut of log(z), is really just any curve joining the only two branch points of this function, with the ob jective of excluding curves from going around any of the branch points. This is because log(z) can be dened uniquely only if one is allowed to go around neither z = 0 nor z = 1, both being branch points.

In the next section we will consider examples of branch points, branch cuts and Riemann surfaces for other multiple valued functions.

## 2 A few simple examples.

Example 2.1 In this example we discuss the branch points of log(z 1) and draw a set of possible

$$\log(z-1) = \ln(\rho) + i\phi, \qquad (2.1)$$

where z 1 = e<sup>i</sup> , with > 0 and real (see Figure 2.1).

**Example 2.2** In this example we discuss the branch points of  $\log(z^2 - 1)$  and draw a set of possible branch cuts for this function. We have:

$$\log(z^2 - 1) = \log(z - 1) + \log(z + 1). \tag{2.2}$$

As we travel around z=1 on a closed path<sup>4</sup>,  $\log(z-1)$  changes by a multiple of  $2\pi i$  but  $\log(z+1)$  returns to its original value, hence  $\log(z^2-1)$  changes by the same amount. Thus z=1 is a branch point of  $\log(z^2-1)$ . Similarly, z=-1 is also a branch point. To investigate the point at infinity (there are no other branch points with  $|z| < \infty$ ), we substitute  $z=\frac{1}{\zeta}$  and find

$$\log(z^2 - 1) = \log\left(\frac{1 - \zeta^2}{\zeta^2}\right) = \log(1 - 2\zeta^2) - 2\log(\zeta). \tag{2.3}$$

On a curve enclosing  $\zeta = 0$ , the first term on the right hand side of (2.3) will return to its original value — by a calculation similar to the one below (2.2) — but the second will not. We conclude that the point  $\zeta = 0$ , or equivalently  $z - \infty$ , is the third branch point of  $\log(z^2 - 1)$ .

An alternative way of showing that  $z = \infty$  is a branch point for  $\log(z^2 - 1)$ , is to consider a curve "enclosing infinity". As we traverse such a curve, both  $\log(z - 1)$  and  $\log(z + 1)$  will change, by the same multiple of  $2\pi$ . Hence, from (2.2),  $\log(z^2 - 1)$  will not return to its original value. Thus  $z = \infty$  is a branch point.

<sup>&</sup>lt;sup>4</sup>Close enough to z = 1 that it does not enclose z = -1.

Note that: at  $z = \pm 1$ , the argument of the logarithm in this example (i.e.:  $(z^2 - 1)$ ) vanishes. At  $z = \infty$ , this argument is equal to infinity. As a general rule, the function  $\log(f(z))$  has branch points at the zeroes of f(z) and at the points where f(z) is infinite, as well as (possibly) the points where f(z) itself has branch points. But, be careful with this: the zeros have to be zeros in the sense of analytic functions and by "infinities" we mean poles. Other types of (singular) behaviors in f(z) can lead to unexpected results, e.g.: think of what happens at z = 0 when  $f(z) = \exp\left(\frac{1}{z}\right)$ .

**Example 2.3** In this example we discuss the branch points of  $\log \left(\frac{z-1}{z+1}\right)$  and draw a set of possible branch cuts for this function. We have:

$$\log\left(\frac{z-1}{z+1}\right) = \log(z-1) - \log(z+1). \tag{2.4}$$

Thus, by an argument entirely similar to that used in example 2.2, we see that  $z=\pm 1$  are the branch points of  $\log\left(\frac{z-1}{z+1}\right)$  for  $|z|<\infty$ . Also, substituting  $z=\frac{1}{\zeta}$ , we find

$$\log\left(\frac{z-1}{z+1}\right) = \log\left(\frac{1-\zeta}{1+\zeta}\right). \tag{2.5}$$

Thus we see that the only branch points for  $|\zeta| < \infty$  are  $\zeta = \pm 1$ , while  $\zeta = 0$  is not a branch point. The branch points  $\zeta = \pm 1$  correspond to  $z = \pm 1$ , while the point  $\zeta = 0$  corresponds to  $z = \infty$ . Thus  $z = \infty$  is not a branch point in this example. (note that at at  $z = \infty$ ,  $\frac{z-1}{z+1}$  is neither zero nor infinity and has a perfectly well defined value of one).

An alternative way of showing that  $z=\infty$  is not a branch point for  $\log\left(\frac{z-1}{z+1}\right)$ , is to consider a curve "enclosing infinity". As we traverse such a curve, both  $\log(z-1)$  and  $\log(z+1)$  will change, by the same multiple of  $2\pi$ . Hence, from (2.4),  $\log\left(\frac{z-1}{z+1}\right)$  will return to its original value (as the changes will cancel each other). Note the difference with example 2.2, where the changes added in equation (2.2) — making  $z=\infty$  a branch point of  $\log(z^2-1)$ .

The branch cuts must be drawn to prevent curves from going around the two branch points  $z=\pm 1$ . Thus the same branch cuts that were used in example 2.2 (see Figure 2.3) may be used here. However, the cuts on the right-most picture in Figure 2.3 are "excessive", as we explain next. To prevent curves from enclosing either of the branch points, any arc going from z=-1 to z=1 will do. This curve may go through  $\infty$  (as in the left-most and center pictures in Figure 2.3) or not.<sup>5</sup> Thus an arc connecting z=-1 to z=1 in the finite Complex plane is perfectly adequate, no "extension" joining it to  $z=\infty$  (as in the right-most picture in Figure 2.3) is required! The "extension" is needed in example 2.2 because there  $z=\infty$  is a branch point.

<sup>&</sup>lt;sup>5</sup>Recall that  $z = \infty$  is just one more point in the **Riemann Sphere**. In this sphere, a curve joining  $z = \pm 1$  may or may not go through  $\infty$ . If it does, then on the finite Complex plane the curve looks like two separate curves going from each of the points  $z = \pm 1$  to  $\infty$ .

For example, we may take the branch cut to be the straight line segment joining the two branch points, as in Figure 2.4. We may also take the cuts as in Figure 2.5 (we may think of them as a straight line joining z = -1 to z = 1, which passes through infinity).

The curve from A to B in Figure 2.4 illustrates the fact that infinity is not a problem in this example. If we follow the closed path in the figure, then (since the path encloses z=1) the function  $\log(z-1)$  changes by  $2\pi i$ . But the path encloses z=-1 as well, so the function  $\log(z+1)$  changes by the same amount  $2\pi i$ . Because the function  $\log\left(\frac{z-1}{z+1}\right)$  is the difference between  $\log(z-1)$  and  $\log(z+1)$ , it does not change as the closed path is traversed and takes the same value at A and B in the figure. No extra branch cuts are needed.

### Example 2.4 Let us now discuss the function

$$z^a = r^a e^{ia\theta} .$$

where a is a complex number. Obviously, as a closed path enclosing the origin (once) is traversed in the counterclockwise direction,  $\theta \to \theta + 2\pi$ . Hence we have that

$$z^a \rightarrow z^a e^{2\pi i a}$$

If a is not an integer (positive or negative), the value  $z^a$  changes after one goes around this path. Therefore, z=0 is a branch point of  $z^a$ . Clearly, the situation is the same for  $z=\infty$ . We conclude that when a is not an integer, the branch points of  $z^a$  are exactly z=0 and  $z=\infty$ . Thus, the branch cut for  $z^a$  can be any curve joining z=0 and  $z=\infty$ .

Let us now consider what happens when we go around the origin n times in the counterclockwise direction. Then

$$z^a \rightarrow z^a e^{2\pi i n a}$$
.

If a is a rational number of the form of  $\frac{m}{n}$  (where m is an integer), then  $e^{2\pi i n a} = e^{2\pi i m} = 1$  and  $z^a$  returns to its original value as we go around the origin n times. What this means is that, as we start from the (say) first Riemann sheet and go around the origin, we successively enter the  $2^{nd}$ ,  $3^{rd}$ , ...,  $(n-1)^{th}$  and  $n^{th}$  Riemann sheets, but then the  $(n+1)^{th}$  sheet we enter is the same as the first sheet. Thus  $z^{m/n}$  has n Riemann sheets. For example,  $z^{\frac{1}{2}}$  has two sheets (which is just right, because the square root of complex number has two possible values: one being the negative of the other). Other examples are  $z^{\frac{1}{3}}$  and  $z^{-\frac{1}{4}}$ , with three and four sheets, respectively.

Warning: in calculating the number of sheets that the Riemann surface for  $z^a$  has (when  $a = \frac{m}{n}$  is a rational number) it is important to use the representation of a where m and n are co-primes. For example, we can write  $0.5 = \frac{2}{4}$ , but the square root has only two Riemann sheets.

As a final example, consider  $1/z^2$ . Here a=-2 (which is an integer) so that neither z=0 nor  $z=\infty$  are branch points for  $1/z^2$ . In fact, this function has no branch points. Notice, however, that  $1/z^2$  "blows up" at z=0. Thus z=0 is a singularity for  $z^{-2}$  (called a pole), but it is not a branch point. This is an example of the important point made next.

VERY IMPORTANT POINT: The fact that a function f(z) — or its derivatives — may or may not have a "value" at some point  $z = z_0$ , is <u>IRRELEVANT</u> as far as deciding the issue of whether or not  $z_0$  is a branch point for f(z).

As a few further examples of this, consider

- $\sqrt{z}$  has a limit value at z=0 but not one at  $z=\infty$ . Both these points are branch points.
- $\frac{d}{dz}z^{\frac{3}{2}} = \frac{3}{2}z^{\frac{1}{2}}$  vanishes at z = 0, while  $\frac{d}{dz}z^{\frac{1}{5}} = \frac{1}{5}z^{\frac{4}{5}}$  blows up at z = 0. In both cases, however, z = 0 is a branch point. The derivative of a function may or may not approach a finite value as the branch point is approached. The fact that the derivative approaches a finite value or not at a point cannot be used as a criteria of whether the point is a branch point of a function.
- $\sqrt{z^2-1}$  approaches finite values at its two branch points  $(z=\pm 1)$ , but its derivative does not.
- $(z^2-1)^{\frac{3}{2}}$  and its first derivative approach finite values at its two branch points  $(z=\pm 1)$ .
- $\frac{1}{\sqrt{(z^2-1)}}$  blows up at both of its two branch points  $(z=\pm 1)$ .
- $\frac{1}{z^n}$   $(n = 1, 2, 3, \ldots)$  blows up at z = 0, but it has no branch points.

**Example 2.5** Here we discuss the branch points and possible branch cuts for  $z^a(z-1)^b$ .

From the discussion in example 2.4 (using the representation for  $z^a(z-a)^b$  introduced in Figure 2.6), it should be clear that the branch points for this function are as follows:

- z=0 is a branch point if and only if a is not an integer.
- z=1 is a branch point if and only if b is not an integer.
- $z=\infty$  is a branch point if and only if (a+b) is not an integer. If a+b is an integer, the function  $z^a(z-1)^b$  returns to its original value after a path enclosing both z=0 and z=1 is traced. This situation is similar to the one depicted in Figure 2.4.
- There are no other branch points.

Using the double polar coordinate system intro-duced in the picture, it is clear that we have:

$$z^{a}(z-1)^{b} = r_{2}^{a} r_{1}^{b} e^{i(a\theta_{2}+b\theta_{1})}.$$

Thus, on any counterclockwise path enclosing (only) z=0 or z=1 or  $z=\infty$ , we have:

$$\begin{array}{ll} \text{for } z=0: & z^a(z-1)^b \to z^a(z-1)^b \, e^{2\pi i a} \, , \\ \\ \text{for } z=1: & z^a(z-1)^b \to z^a(z-1)^b \, e^{2\pi i b} \, , \\ \\ \text{for } z=\infty: & z^a(z-1)^b \to z^a(z-1)^b \, e^{2\pi i (a+b)} \, , \end{array}$$

respectively

Figure 2.6: Double polar coordinate system.

Possible branch cuts for  $z^a(z-1)^b$  can be chosen as in Figure 2.7. However, note that if either a or b is an integer (but not both) then only  $z=\infty$  and one of z=1 or z=0 (but not both) will be branch points. In this case the choices of branch cuts will be similar to those in example 2.1. Finally, if both a and b are integers, then there are no branch points (hence no branch cuts either).

THE END.

---

| MIT OpenCourseWare |
|--------------------|
| http://ocw.mit.edu |

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

# Laws in Continuum Modeling.

### Rodolfo R. Rosales

## MIT, March, 2001.

 notes give examples illustrating how conservation principles are used to obtain (phenomenological) continuum models for physical phenomena. The general principles are presented, with examples from trac 
ow, river 
ows, granular 
ows, gas dynamics and diusion.

| 1 | Introduction.                                                                 | 2  |
|---|-------------------------------------------------------------------------------|----|
| 2 | Continuum<br>Approximation;<br>Densities<br>and<br>Fluxes.                    | 2  |
|   | 2.1<br>Examples<br>                                                           | 3  |
| 3 | Conservation<br>Laws<br>in<br>Mathematical<br>Form.                           | 5  |
|   | Integral Form of<br>a Conservation Law<br>(1-D case)<br>                      | 5  |
|   | Dierential Form of<br>a Conservation Law<br>(1-D case)<br>                    | 5  |
|   | Shock<br>Waves<br>                                                            | 6  |
|   | Integral Form of<br>a Conservation Law<br>(multi-D case)<br>                  | 6  |
|   | Dierential Form of<br>a Conservation Law<br>(multi-D case)<br>                | 7  |
|   | Dierential Form of<br>the<br>Equations for Vector<br>Conservation<br>Laws<br> | 7  |
| 4 | Phenomenological<br>Equation<br>Closure.                                      | 7  |
|   | 4.1<br>Examples<br>                                                           | 8  |
|   | Example:<br>River Flow                                                        | 8  |
|   | Quasi-equilibrium<br>approximation<br> <br>                                   | 8  |
|   | Example:<br>Trac<br>Flow                                                      | 9  |
|   | Example:<br>Heat Conduction .                                                 | 10 |
|   | <br>Fick's<br>Law<br>                                                         | 10 |
|   | <br>Thermal conductivity,<br>diusivity, heat<br>equation                      | 10 |
|   | Example:<br>Granular Flow<br>                                                 | 11 |
|   | Example:<br>Inviscid Fluid Flow                                               | 12 |
|   | <br>Incompressible Euler<br>Equations .                                       | 12 |
|   | <br>Incompressible Navier-Stokes<br>Equations<br>                             | 12 |
|   | Gas Dynamics<br> <br>                                                         | 13 |
|   | <br>Equation of State<br>                                                     | 13 |
|   | <br>Isentropic<br>Euler Equations<br>of Gas<br>Dynamics<br>                   | 13 |
|   | <br>Navier-Stokes<br>Equations<br>for Gas Dynamics<br>                        | 13 |
| 5 | Concluding<br>Remarks.                                                        | 13 |

MIT, Department of Mathematics, room 2-337, Cambridge, MA 02139.

In formulating a mathematical model for a continuum physical system, there are three basic steps

- A. Identify appropriate conservation laws (e.g. mass, momentum, energy, etc) and their corresponding densities and 
  uxes.
- B. Write the corresponding equations using conservation.
- C. Close the system of equations by proposing appropriate relationships between the uxes and

Of these steps, the mathematical one is the second. While it involves some subtlety, once you understand it, its application is fairly mechanical. The rst and third steps involve physical issues, and (generally) the third one is the hardest one, where all the main diculties appear in developing a new model. In what follows we will go through these steps, using some practical examples to

Of course, once a model is formulated, a fourth step arises, which is that of analyzing and validating the model, comparing its predictions with observations ... and correcting it whenever needed. This involves simultaneous mathematical and physical thinking. You should never forget that <sup>a</sup> model is no better than the approximations (explicit and/or implicit) made when deriving it. It is never a question of just"solving" the equations, forgetting what is behind them.

## 2 Continuum Approximation; Densities and Fluxes.

The modeling of physical variables as if they were a continuum eld is almost always an approximation. For example, for a gas one often talks about the density , or the ow velocity u, and thinks of them as functions of space and time: = (x; t) or u = u(x; t). But the fact is that a gas is made up by very many discrete molecules, and the concepts of density, or 
ow velocity, only make sense as local averages. These averages must be made over scales large enough that the discreteness of the gas becomes irrelevant, but small enough that the notion of these local averages varying in space and time makes sense.

Thus, in any continuum modeling there are several scales. On the one hand one has the "visible" scales, which are the ones over which the mathematical variables in the model vary (densities, 
uxes). On the other hand, there are the "invisible" scales, that pertain to the microscales that have been averaged in obtaining the model. The second set of scales must be much smaller than the rst set for the model to be valid. Unfortunately, this is not always the case, and whenever this fails all sort of very interesting (and largely open) problems in modern science and engineering arise.

Note that the reason people insist on trying to use continuum type models, even in situations where one runs into the diculties mentioned at the end of the last paragraph, is that continuum models are often much simpler (both mathematically and computationally) than anything else, and supply general understanding that is often very valuable.

The rst step in the modeling process is to identify conserved quantities (e.g. mass) and dene the appropriate densities and uxes | as in the following examples.

## 2.1 Examples

## Example 2.1 River Flow (a one dimensional example).

Consider a nice river (or a channel) owing down a plain (e.g. the Mississippi, the Nile, etc.). Let x be the length coordinate along the river, and at every point (and time) along the river let A = A(x; t) be the l led (by water) cross-section of the river bed.

We note now that A is the volume density (volume per unit length) of water along the river. We also note that, since water is incompressible, volume is conserved.1 Final ly, let Q = Q(x; t) be the volume ux of water down the river (i.e.: volume per unit time). Notice that, if u = u(x; t) is the average ow velocity down the river, then Q = uA (by denition of u).

Thus, in this case, an appropriate conservation law is the conservation of volume, with corresponding density A and 
ux Q. We note that both A and Q are regularly measured at various points along important rivers.

## Example 2.2 Trac Flow (a one dimensional example).

Consider a one lane road, in a situation where there are no cross-roads (e.g.: a tunnel, such as the Lincoln tunnel in NYC, or the Summer tunnel in Boston). Let x be length along the road. Under "heavy" trac conditions,2 we can introduce the notions of trac density = (x; t) (cars per unit length) and trac ow q = q(x; t)(cars per unit time). Again, we have q = u; where u is the average car ow velocity down the road.

In this case, the appropriate conservation law is, obviously, the conservation of cars. Notice that this is one example where the continuum approximation is rather borderline (since, for example, the local averaging distances are almost never much larger than a few car separation lengths). Nevertheless, as we wil l see, one can gain some very interesting insights from the model we wil l develop (and some useful practical facts).

### Example 2.3 Heat Conductivity.

Consider the thermal energy in a chunk of solid material (such as, say, a piece of copper). Then the thermal energy density (thermal energy per unit volume) is given by e = cT (x; t), where T is the temperature, c is the specic heat per unit mass, and is the density of the material (for simplicity we wil l assume here that both c and are constants). The thermal energy ow, Q = Q(x; t) is now a vector, whose magnitude gives the energy ow across a unit area normal to the ow direction.

In this case, assuming that heat is not being lost or gained from other energy forms, the relevant conservation law is the conservation of heat energy.

## Example 2.4 Steady State (dry) Granular Flow.

Consider steady state (dry) granular ow down some container (e.g. a silo, containing some dry granular material, with a hole at the bottom). At every point we characterize the 
ow in terms of two velocities: an horizontal (vector) velocity u = u(x; y; z; t), and a vertical (scalar) velocity v = v(x; y; z; t), where x and y are the horizontal length coordinates, and z is the vertical one.

<sup>1</sup>We are neglecting here such things as evaporation, seepage into the ground, etc. This cannot always be done.

<sup>2</sup>Why must we assume "heavy" trac?

The mass ow rate is then given by Q = [u; v],where is the mass density | which we wil l assume is nearly constant. The relevant conservation isnow the conservation of mass.

This example is dierent from the others in that we are looking at a steady state situation. We also note that this is another example where the continuum approximation is quite often "borderline", since the scale separation between the grain scales and the ow scales is not that great.

### Example 2.5 Inviscid Fluid Flow.

For a uid owing in some region of space, we consider now two conservation laws: conservation of mass and conservation of linear momentum. Let now = (x; t), u = u(x; t) and p = p(x; t) be, respectively, the uid density, ow velocity, and pressure | where we use either [u; v; w] or [u1; u2; u3] to denote the components of u, and either [x; y; z] or [x1; x2; x3] to denote the components of x. Then:

- The mass conservation law density is .................................................. .
- The mass conservation law ow is .................................................... u.
- The linear momentum conservation law density is .................................. u.
- The linear momentum conservation law ow is ............................ <sup>u</sup> u + p I.

The rst two expressions above are fairly obvious, but the last two (in particular, the last one) require some explanation. First of al l, momentum is a vector quantity. Thus its conservation is equivalent to three conservation laws, with a vector density and a rank two tensor3 ow (we explain this below). Second, momentum can be transferred from one part of a liquid to another in two ways: Advection: as a parcel of uid moves, it carries with it some momentum. Let us consider this mechanism component by component: The momentum density component ui is advected with <sup>a</sup> ow rate ui <sup>u</sup> <sup>=</sup> [uiu1; uiu2; uiu3]. Putting al lthree components together, we get for the momentum ux (due to advection) the expression [ui uj ] = <sup>u</sup> u | i.e., a rank two tensor, where each row (freeze the rst index) corresponds to the ux for one ofthe momentum components.

Forces: momentum is transferred by the forces exerted by one parcel of uid on another. If we assume that the uid is inviscid, then these forces can only be normal, and are given by the pressure (this is, actual ly, the "denition" of inviscid). Thus, again, let us consider this mechanism component by component: the momentum transfer by the pressure in the direction given by the unit vector<sup>4</sup> ei = [i j ], corresponding to the density ui, is the force per unit area (normal to ei) by the uid. Thus the corresponding momentum 
ow vector is p ei. Putting al l three components together, we get for the momentum ux (due to pressure forces) the expression <sup>p</sup> [i j ] = <sup>p</sup> <sup>I</sup> <sup>|</sup> again <sup>a</sup> rank two tensor, now a scalar multiple ofthe identity rank two tensor I.

Regarding the zero viscosity (inviscid) assumption: Fluids can also exert tangential forces, which also aect the momentum transfer. Momentum canalso be transferred in the normal direction by diusion of "faster" molecules into a region with "slower" molecules, and viceversa. Both these eects are characterized by the viscosity coecient | which here we assume can be neglected.

Note that in some of the examples we have given only one conservation law, and in others two (further examples, with three or more conservation laws invoked, exist). The reason willbecome clear when we go to the third step (step C in section 1). In fact, steps A and C in section 1 are intimately linked, as we will soon see.

<sup>3</sup> If you do not know what a tensor is, just think of it as a vector with more than one index (the rank is the number of indexes). This is all you need to know to understand what follows.

<sup>4</sup>Here i j is the Kronecker delta, equal to 1 if <sup>i</sup> <sup>=</sup> j, and to 0 if <sup>i</sup> 6= j.

## 3 Conservation Laws in Mathematical Form.

In this section we assume that we have identified some conservation law, with conserved density  $\rho = \rho(\mathbf{x}, t)$ , and flux  $\mathbf{F} = \mathbf{F}(\mathbf{x}, t)$ , and derive mathematical formulations for the conservation hypothesis. In other words, we will just state in mathematical terms the fact that  $\rho$  is the density for a conserved quantity, with flux  $\mathbf{F}$ .

First consider the one dimensional case (where the flux F is a scalar, and there is only one space coordinate: x). In this case, consider some (fixed) arbitrary interval in the line  $\Omega = \{a \le x \le b\}$ , and let us look at the evolution in time of the conserved quantity inside this interval. At any given time, the total amount of conserved stuff in  $\Omega$  is given by (this by definition of density)

$$M(t) = \int_a^b \rho(x, t) dx. \tag{3.1}$$

Further, the net rate at which the conserved quantity enters  $\Omega$  is given by (definition of flux)

$$R(t) = F(a, t) - F(b, t). (3.2)$$

It is also possible to have **sources and sinks** for the conserved quantity.<sup>5</sup> In this case let s = s(x,t) be the total net amount of the conserved quantity, per unit time and unit length, provided by the sources and sinks. For the interval  $\Omega$  we have then a net rate of added conserved stuff, per unit time, given by

$$S(t) = \int_{a}^{b} s(x, t) dx.$$
 (3.3)

The conservation law can now be stated in the mathematical form

$$\frac{d}{dt}M = R + S\,, (3.4)$$

which must apply for any choice of interval  $\Omega$ . Since this equation involves only integrals of the relevant densities and fluxes, it is known as the Integral Form of the Conservation Law.

Assume now that the densities and fluxes are nice enough to have nice derivatives. Then we can write:

$$\frac{d}{dt}M = \int_a^b \frac{\partial}{\partial t} \rho(x, t) \, dx \quad \text{and} \quad R = -\int_a^b \frac{\partial}{\partial x} F(x, t) \, dx \,. \tag{3.5}$$

Equation (3.4) can then be re-written in the form

$$\int_{a}^{b} \left( \frac{\partial}{\partial t} \rho(x, t) + \frac{\partial}{\partial x} F(x, t) - s(x, t) \right) dx = 0, \qquad (3.6)$$

which must apply for any choice of the interval  $\Omega$ . It follows that the integrand above in (3.6) must vanish identically. This then yields the following partial differential equation involving the density, flux and source terms:

$$\frac{\partial}{\partial t}\rho(x,t) + \frac{\partial}{\partial x}F(x,t) = s(x,t). \tag{3.7}$$

This equation is known as the **Differential Form of the Conservation Law.** 

 $<sup>^5</sup>$ As an illustration, in the inviscid fluid flow case of example 2.5, the effects of gravity translate into a vertical source of momentum, of strength  $\rho g$  per unit volume — where g is the acceleration of gravity. Other body forces have similar effects.

Remark 3.1 You may wonder why we even bother to give a name to the form of the equations in (3.4), since the differential form in (3.7) appears so much more convenient to deal with (it is just one equation, not an equation for every possible choice of  $\Omega$ ). The reason is that it is not always possible to assume that the densities and fluxes have nice derivatives. Oftentimes the physical systems involved develop, as they evolve,  $^6$  short enough scales that force the introduction of discontinuities into the densities and fluxes — and then (3.7) no longer applies, but (3.4) still does. Shock waves are the best known example of this situation. Examples of shock waves you may be familiar with are: the sonic boom produced by a supersonic aircraft; the hydraulic jump occurring near the bottom of the discharge ramp in a large dam; the wave-front associated with a flood moving down a river; the backward facing front of a traffic jam; etc. Some shock waves can cause quite spectacular effects, such as those produced by supernova explosions.

Now let us consider the multi-dimensional case, when the flux  $\mathbf{F}$  is a vector. In this case, consider some (fixed but arbitrary) region in space  $\Omega$ , with boundary  $\partial\Omega$ , and inside unit normal along the boundary  $\hat{\mathbf{n}}$ . We will now look at the evolution in time of the conserved quantity inside this region. At any given time, the total amount of conserved stuff in  $\Omega$  is given by

$$M(t) = \int_{\Omega} \rho(\mathbf{x}, t) \, dV \,. \tag{3.8}$$

On the other hand, the net rate at which the conserved quantity enters  $\Omega$  is given by

$$R(t) = \int_{\partial \Omega} \mathbf{F}(\mathbf{x}, t) \cdot \hat{\mathbf{n}} \, dS \,. \tag{3.9}$$

Let also  $s = s(\mathbf{x}, t)$  be the total net amount of conserved quantity, per unit time and unit volume, provided by any sources and/or sinks. For the region  $\Omega$  we have then a net rate of added conserved stuff, per unit time, given by

$$S(t) = \int_{\Omega} s(\mathbf{x}, t) \, dV \,. \tag{3.10}$$

The conservation law can now be stated in the mathematical form (compare with equation (3.4))

# Integral Form of the Conservation Law:

$$\frac{d}{dt}M = R + S\,, (3.11)$$

which must apply for any choice of the region  $\Omega$ .

If the densities and fluxes are nice enough to have nice derivatives, we can write:

$$\frac{d}{dt}M = \int_{\Omega} \frac{\partial}{\partial t} \rho(\mathbf{x}, t) dV \quad \text{and} \quad R = -\int_{\Omega} \operatorname{div}(\mathbf{F}(\mathbf{x}, t)) dV, \qquad (3.12)$$

where we have used the Gauss divergence theorem for the second integral. Equation (3.11) can then be re-written in the form

$$\int_{\Omega} \left( \frac{\partial}{\partial t} \rho(\mathbf{x}, t) + \operatorname{div}(\mathbf{F}(\mathbf{x}, t)) - s(\mathbf{x}, t) \right) dV = 0, \qquad (3.13)$$

<sup>&</sup>lt;sup>6</sup>Even when starting with very nice initial conditions.

which must apply for any choice of the region  $\Omega$ . It follows that the integrand above in (3.13) must vanish identically. This then yields the following partial differential equation involving the density, flux and source terms (compare with equation (3.7))

$$\frac{\partial}{\partial t}\rho(\mathbf{x},t) + \operatorname{div}(\mathbf{F}(\mathbf{x},t)) = s(\mathbf{x},t). \tag{3.14}$$

This equation is known as the **Differential Form of the Conservation Law.** 

Remark 3.2 In the case of a vector conservation law, the density  $\rho$  and the source term s will both be vectors, while the flux  $\mathbf{F}$  will be a rank two tensor (each row being the flux for the corresponding element in the density vector  $\rho$ ). In this case equation (3.14) is valid component by component, but can be given a vector meaning if we define the divergence for a rank two tensor  $\mathbf{F} = [F_{ij}]$  as follows:

$$\operatorname{\mathsf{div}}(\mathbf{F}) = \left[\sum_{i} \frac{\partial}{\partial x_{j}} F_{ij}\right] \, ,$$

so that  $div(\mathbf{F})$  is a vector (each element corresponding to a row in  $\mathbf{F}$ ). You should check that this is correct.

# 4 Phenomenological Equation Closure.

From the results in section 3 it is clear that each conservation principle can be used to yield an evolution equation relating the corresponding density and flux. However, this is not enough to provide a complete system of equations, since each conservation law provides only one equation, but requires two (in principle) "independent" variables. Thus extra relations between the fluxes and the densities must be found to be able to formulate a complete mathematical model. This is the **Closure Problem**, and it often requires making further assumptions and approximations about the physical processes involved.

Closure is actually the hardest and the subtler part of any model formulation. How good a model is, typically depends on how well one can do this part. Oftentimes the physical processes considered are very complex, and no good understanding of them exist. In these cases one is often forced to make "brute force" phenomenological approximations (some formula — with a few free parameters — relating the fluxes to the densities is proposed, and then it is fitted to direct measurements). Sometimes this works reasonably well, but just as often it does not (producing situations with very many different empirical fits, each working under some situations and not at all in others, with no clear way of knowing "a priori" if a particular fit will work for any given case).

We will illustrate how one goes about resolving the closure problem using the examples introduced earlier in subsection 2.1. These examples are all "simple", in the sense that one can get away with algebraic formulas relating the fluxes with the densities. However, this is not the only possibility, and situations where extra differential equations must be introduced also arise. The more complex the process being modeled is, the worse the problem, and the harder it is to close the system (with very many challenging problems still not satisfactorily resolved).

<sup>7</sup>Recall that, for a vector field, 
$$\operatorname{div}(\mathbf{v}) = \sum_{j} \frac{\partial}{\partial x_{j}} v_{j}$$
.

An important point to be made is that the formulation of an adequate mathematical model is only the beginning. As the examples below will illustrate, it is often the case that the mathematical models obtained are quite complicated (re
ecting the fact that the phenomena being modeled are complex), and often poorly understood. Thus, even in cases where accurate mathematical models have been known for well over a century (as in classical uids), there are plenty of open problems still around ... and even now new, un-expected, behaviors are being discovered in experimental laboratories. The fact is that, for these complex phenomena, mathematics alone is not enough. There is just too much that can happen, and the equations are too complicated to have explicit solutions. The only possibility of advance is by a simultaneous approach incorporating experiments and observations, numerical calculations, and theory.

## 4.1 Examples

## Example 4.1 River Flow (see example 2.1).

In this case we can write the conservation equation

$$A_t + Q_x = 0, (4.1)$$

where A and Q were introduced in example 2.1, and we ignore any sources or sinks for the water in the river. In order to close the model, we now claim that it is reasonable to assume that Q is a function of A; that is to say Q = Q(A; x) | for a uniform, man-made channel, one has

Q = Q(A): We justify this hypothesis as fol lows:

First: For a given river bed shape, when the ow is steady (i.e.: no changes in time) the average ow velocity u fol lows from the balance between the force of gravity pul ling the water down the slope, and the friction force on the river bed. This balance depends only on the river bed shape, its slope, and how much water there is (i.e. A). Thus, under these conditions, we have u = u(A; x). Consequently Q = Q(A; x) = u(A; x) A.

Second: As long as the ow in the river does not deviate too much from steady state ("slow" changes), the we can assume that the relationship Q = Q(A; x) that applies for steady ow remains (approximately) valid. This is the quasi-equilibrium approximation, which is often invoked in problems like this. How wel l it works in any given situation depends on how fast the processes leading to the equilibrium situation (the one that leads to Q = Q(A; x)) work | relative to the time scales of the river ow variations one is interested in.For actual rivers and channels, it turns out that this approximation is good enough for many applications.

Of course, the actual functional relationship Q = Q(A; x) (to be used to model a specic river) cannot be calculated theoretical ly, and must be extracted from actual measurements of the river 
ow under various conditions. The data is then tted by (relatively simple) empirical formulas, with free parameters selected for the best possible match.

However, it is possible to get a qualitative idea of roughly how Q depends on A, by the fol lowing simple argument: The force pul ling the water downstream (gravity) is proportional to the slope of the bed, the acceleration of gravity, the density ofwater, and the volume of water. Thus, roughly speaking, this force has the form Fg cg <sup>A</sup> (where cg <sup>=</sup> cg(x) is some function). On the other hand, the force opposing this motion, in the simplest possible model, can be thought as being

proportional to the wetted perimeter of the river bed (roughly  $P \propto \sqrt{A}$ ) times the frictional force on the bed (roughly proportional to the velocity u). That is  $F_f \approx c_f u \sqrt{A}$ , for some friction coefficient  $c_f$ . These two forces must balance  $(F_q = F_f)$ , leading to  $u \approx c_u \sqrt{A}$  (where  $c_u = c_q/c_f$ ), thus:

$$Q \approx c_u A^{3/2} \,. \tag{4.2}$$

Of course, this is too simple for a real river. But the feature of the flux increasing faster than linear is generally true — so that Q as a function of A produces a concave graph, with dQ/dA > 0

and  $d^2Q/dA^2 > 0$ .

## Example 4.2 Traffic Flow (see example 2.2).

In this case we can write the conservation equation

$$\rho_t + q_x = 0 \,, \tag{4.3}$$

where  $\rho$  and q were introduced in example 2.2, and we ignore any sources or sinks for cars (from road exit and incoming ramps, say). Just as in the river model, we close now the equations by claiming that it is reasonable to assume that q is a function of  $\rho$ , that is to say  $q = q(\rho, x) - for$ 

a nice, uniform, road, one has  $q = q(\rho)$ . Again, we use a quasi-equilibrium approximation to justify this hypothesis:

Under steady traffic conditions, it is reasonable to assume that the drivers will adjust their car speed to the local density (drive faster if there are few cars, slower if there are many). This yields  $u=u(\rho,x)$ , thus  $q=u(\rho,x)\rho=q(\rho,x)$ . Then, if the traffic conditions do not vary too rapidly, we can assume that the equilibrium relationship  $q = q(\rho, x)$  will still be (approximately) valid quasi-equilibrium approximation.

As in the river flow case, the actual functional dependence to be used for a given road must follow from empirical data. Such a fit for the Lincoln tunnel in NYC is given by

$$q = a \rho \log(\rho_j/\rho), \tag{4.4}$$

where a = 17.2 mph, and  $\rho_i = 228$  vpm (vehicles per mile). The generic shape of this formula is always true: q is a convex function of  $\rho$ , reaching a maximum flow rate  $q_m$  for some value  $\rho=\rho_m$ , and then decreases back to zero flow at a jamming density  $\rho=\rho_j$ . In particular,  $dq/d\rho$  is a decreasing function of  $\rho$ , with  $d^2q/d\rho^2<0$ .

For the formula above in (4.4), we have:  $\rho_m = 83$  vpm and  $q_m = 1430$  vph (vehicles per hour), with a corresponding flow speed  $u_m = q_m/\rho_m = a$ . The very existence of  $\rho_m$  teaches us a rather useful fact, even before we solve any equation: in order to maximize the flow in a highway, we should try to keep the car density near the optimal value  $\rho_m$ . This is what the lights at the entrances to freeways attempt to do during rush hour. Unfortunately, they do not work very well for this purpose, as some analysis with the model above (or just plain observation of an actual freeway) will show. In this example the continuum approximation is rather borderline. Nevertheless, the equations have the right qualitative (and even rough quantitative) behavior, and are rather useful to understand many features of how heavy traffic behaves.

<sup>&</sup>lt;sup>8</sup>Greenberg, H., 1959. An analysis of traffic flow. *Oper. Res.* 7:79–85.

## Example 4.3 Heat Conductivity (see example 2.3).

In this case we can write the conservation equation

$$c \rho T_t + \operatorname{div}(\mathbf{Q}) = s, \tag{4.5}$$

where c,  $\rho$ , T and  $\mathbf{Q}$  were introduced in example 2.3, and  $s = s(\mathbf{x}, t)$  is the heat supplied (per unit volume and unit time) by any sources (or sinks) — e.g. electrical currents, chemical reactions, etc.

We now complete the model by observing that heat flows from hot to cold, and postulating that the heat flow across a temperature jump is proportional to the temperature difference (this can be checked experimentally, and happens to be an accurate approximation). This leads to **Fick's Law** for the heat flow:

$$\mathbf{Q} = -\kappa \, \nabla T \,, \tag{4.6}$$

where  $\kappa$  is the coefficient of thermal conductivity of the material. For simplicity we will assume here that all of c,  $\rho$ , and  $\kappa$  are constant — though this is not necessarily true in general.

Substituting (4.6) into (4.5), we then obtain the **heat or diffusion equation:** 

$$T_t = \nu \, \nabla^2 T + f \,, \tag{4.7}$$

where  $\nu = \frac{\kappa}{c \rho}$  is the **thermal diffusivity** of the material, and  $f = \frac{s}{c \rho}$ .

In deriving the equation above, we assumed that the heat was contained in a chunk of solid material. The reason for this is that, in a fluid, heat can also be transported by motion of the fluid (convection). In this case (4.6) above must be modified to:

$$\mathbf{Q} = -\kappa \, \nabla \mathbf{T} + c \, \rho \, T \, \mathbf{u} \,, \tag{4.8}$$

where  $\mathbf{u} = \mathbf{u}(\mathbf{x}, t)$  is the fluid velocity. Then, instead of (4.7), we obtain

$$T_t + \operatorname{div}(\mathbf{u}T) = \nu \,\nabla^2 T + f \,. \tag{4.9}$$

In fact, this is the simplest possible situation that can occur in a fluid. The reason is that, generally, the fluid density depends on temperature, so that the fluid motion ends up coupled to the temperature variations, due to buoyancy forces. Then equation (4.9) must be augmented with the fluid equations, to determine  $\mathbf{u}$  and the other relevant fluid variables — see example 4.5.

**Remark 4.1** Note that  $\nu$  has dimensions  $\frac{Length^2}{Time}$ . Thus, given a length L, a time scale is provided by  $\tau = L^2/\nu$ . Roughly speaking, this is the amount of time it would take to heat (or cool) a region of size L by diffusion alone. If you go and check the value of  $\nu$  for (say) water, you will find out that it would take a rather long time to heat even a cup of tea by diffusion alone (you should do this calculation). The other term in (4.9) is crucial in speeding things up.

**Remark 4.2** If the fluid is incompressible, then  $div(\mathbf{u}) = 0$  (see example 4.5), and equation (4.9) takes the form

$$T_t + (\mathbf{u} \cdot \nabla)T = \nu \,\nabla^2 T + f \,. \tag{4.10}$$

Note that the left hand side in this equation is just the time derivative of the temperature in a fixed parcel of fluid, as it is being carried around by the flow.

 $<sup>{}^{9}\</sup>kappa$  must be measured experimentally, and varies from material to material.

Remark 4.3 Equations such as (4.9) and (4.10) are satised not just by the temperature, but by many other quantities that propagate by diusion (i.e.: their uxes satisfy Fick's Law (4.6)). Examples are given by any chemicals in solution in a liquid (salt, sugar, colorants, pol lutants, etc.). Of course, if there are any reactions these chemicals participate in, these reactions wil l have to be incorporated into the equations (as sources and sinks).

## Example 4.4 Steady State (dry) Granular Flow (see example 2.4).

In this case we can write the conservation equation

$$\operatorname{div}(\mathbf{Q}) = 0, \tag{4.11}$$

where Q = [u; v] is as in example 2.4, and there are no time derivatives involved because we assumed that the density was nearly constant (we also assume that there are no sources or sinks for the media). These equation involves three unknowns (the three 
ow velocities), so we need some extra relations between them to close the equation.

The argument now is as fol lows: as the grain particles ow down (because of the force ofgravity), they wil l also | more or less randomly | move to the sides (due to particle col lisions). We claim now that, on the average, it is easier for a particle to move from a region of low vertical velocity to one of high vertical velocity than the reverse.10 The simplest way to model this idea is to propose that the horizontal ow velocity u is proportional to the horizontal gradient of the vertical ow velocity v. Thus we propose a law of the form:

$$\mathbf{u} = b \, \nabla_{\perp} v \tag{4.12}$$

where b is a coecient (having length dimensions) and r? denotes the gradient with respect to the horizontal coordinates x and y. Two important points:

- A. Set the coordinate system so that the z axis points down. Thus v is positive when the ow is downwards, and b above is positive.
- B. Equation (4.12) is a purely empirical proposal, based on some rough intuition and experimental observations. However, it works. The predictions of the resulting model in equation (4.13) below have been checked against laboratory experiments, and they match the observations, provided that the value of b is adjusted properly (typical ly, b must be taken around a few particle diameters).

Substituting (4.12) into (4.11), using the formula for the divergence, and eliminating the common constant factor , we obtain the fol lowing model equation for the vertical velocity v:

$$0 = v_z + b \nabla_{\perp}^2 v = v_z + b (v_{xx} + v_{yy}). \tag{4.13}$$

Note that this is a diusion equation, except that the role of time has been taken over by the vertical coordinate z.Mathematical analysis of this equation shows that it only makes sense to solve it for z decreasing; i.e.: from bottom to top in the container where the ow takes place. This, actual ly, makes perfect physical sense: if you have a container ful l of (say) dry sand, and you open a hole at the bottom, the motion wil l propagate upwards through the media. On the other hand, if you move the grains at the top, the ones at the bottom wil l remain undisturbed. In other words, information about motion in the media propagates upward, not downwards.

<sup>10</sup>Intuitively: where the 
ow speed is higher, there is more space between particles where a new particle can move

## Example 4.5 Inviscid Fluid Flow (see example 2.5).

In this case, using the densities and fluxes introduced in example 2.5, we can write the conservation equations:

$$\rho_t + \operatorname{div}(\rho \, \mathbf{u}) = 0 \tag{4.14}$$

for the conservation of mass, and

$$(\rho \mathbf{u})_t + \operatorname{div}(\rho \mathbf{u} \otimes \mathbf{u}) + \nabla p = \mathbf{F}$$
(4.15)

for the conservation of momentum. Here  $\mathbf{F} = \mathbf{F}(\mathbf{x},t)$  denotes the body forces<sup>11</sup> (which are momentum sources), and we have used the mathematical identity (you should check this)  $\operatorname{div}(\mathbf{p}\,\mathbf{I}) = \nabla p$ . Another easy to check mathematical identity is  $\operatorname{div}(\mathbf{u} \otimes \mathbf{m}) = (\operatorname{div}(\mathbf{m}))\,\mathbf{u} + (\mathbf{m} \cdot \nabla)\,\mathbf{u}$ . Using this second identity, with  $\mathbf{m} = \rho\,\mathbf{u}$ , in equation (4.15), and substituting from equation (4.14) to eliminate the term containing the divergence of  $\mathbf{m}$ , we obtain:

$$\rho\left(\mathbf{u}_{t} + (\nabla \cdot \mathbf{u})\,\mathbf{u}\right) + \nabla p = \mathbf{F}. \tag{4.16}$$

The problem now is that we have four equations and five unknowns (density, pressure and the three velocities). An extra equation is needed. Various possibilities exist, and we illustrate a few below.

## Incompressibility Assumption (liquids).

Liquids are generally very had to compress. This means that, as a parcel of fluid is carried around by the flow, its volume (equivalently, its density) will change very little. If we then make the assumption that the liquid density does not change at all (due to pressure changes ... it certainly may change due to temperature changes, or solutes<sup>12</sup> in the liquid), then we obtain the following additional equation:

$$\rho_t + (\nabla \cdot \mathbf{u}) \,\rho = 0 \,. \tag{4.17}$$

This equation simply states that the time derivative of the density, following a parcel of fluid as it moves, vanishes. In other words: the fluid is incompressible (though it need not have a constant density). In this case we can write a complete system of equations for the fluid motion. Namely:

$$0 = \rho_t + (\nabla \cdot \mathbf{u}) \rho, 
0 = \operatorname{div}(\mathbf{u}), 
\mathbf{F} = \rho (\mathbf{u}_t + (\nabla \cdot \mathbf{u}) \mathbf{u}) + \nabla p,$$
(4.18)

where the second equation follows from (4.14), upon use of (4.17). These are known as the **Incompressible Euler Equations** for a fluid. The "simplest" situation arises when  $\rho$  can be assumed constant, and then the first equation above is not needed. However, even in this case, the behavior of the solutions to these equations is not well understood — and extremely rich.

Remark 4.4 The equations above ignore viscous effects, important in modeling many physical situations. Viscosity is incorporated with the method used in example 4.3, by adding to the momentum flux components proportional to derivatives of the flow velocity **u**. What results from this are the Incompressible Navier-Stokes Equations.

Furthermore, heat conduction effects can also be considered (and are needed to correctly model many physical situations). This requires the introduction of a new independent variable into the equations (temperature), and the use of one more conservation law (energy).

<sup>&</sup>lt;sup>11</sup>Such as gravity.

<sup>&</sup>lt;sup>12</sup>For example, salt.

## Gas Dynamics.

For gases one cannot assume incompressibility. In this case, one must introduce another conservation law (conservation of energy), and yet another variable: the internal energy per unit mass e. This results in ve equations (conservation of mass (4.14), conservation of momentum (4.15), and conservation of energy) and six variables (density ,
ow velocity u, pressure p and internal energy e). At this stage thermodynamics comes to the rescue, providing an extra relationship: the equation of state. For example, for an ideal gas with constant specic heats (polytropic gas) one has:

$$e = c_v T$$
 and  $p = R \rho T$   $\Longrightarrow$  Equation of state:  $e = \frac{p}{(\gamma - 1) \rho}$ , (4.19)

where cv is the specic heat at constant volume, cp is the specic heat at constant pressure, <sup>R</sup> <sup>=</sup> cp cv is the gas constant and <sup>=</sup> cp=cv is the ratio of specic heats.

A simplifying assumption that can be made, applicable in some cases, is that the ow is isentropic.13 In this case the pressure is a function of the density only, and (4.14) and (4.15) then form a complete system: the Isentropic Euler Equations of Gas Dynamics. For a polytropic gas:

$$p = \kappa \,\rho^{\gamma} \,, \tag{4.20}$$

where is a constant. In one dimension the equations are

$$\rho_t + (\rho u)_x = 0$$
 and  $(\rho u)_t + (\rho u^2 + p)_x = 0$ , (4.21)

where p = p().

Remark 4.5 The closure problem in this last example involving gas dynamics seemed rather simple, and (apparently) we did not have to cal lupon any "quasi-equilibrium" approximation, or similar. However, this is so only because we invoked an already existing (mayor) theory: thermodynamics. In eect, in this case, one cannot get closure unless thermodynamics is developed rst (no smal l feat). Furthermore: in fact, <sup>a</sup> quasi-equilibrium approximation isinvolved. Formulas such as the ones above in (4.19, apply only for equilibrium thermodynamics! Thus, the closure problem for this example is resolved in a fashion that is exactly analogous to the one used in several of the previous examples.

Remark 4.6 In the fashion similar to the one explained in remark 4.4 for the incompressible case, viscous and heat conduction eects can be incorporated into the equations of Gas Dynamics. The result is the Navier-Stokes Equations for Gas Dynamics.

## 5 Concluding Remarks.

Here we have presented the derivation (using conservation principles) of a few systems of equations used in the modeling of physical phenomena. The study of these equations, and of the physical phenomena they model, on the other hand, would require several lifetimes (and is still proceeding). In particular, notice that here we have not even mentioned the very important sub ject of boundary conditions (what to do at the boundaries of, say, a 
uid). This introduces a whole set of new complications, and physical eects (such as surface tension).

<sup>13</sup>That is: the entropy is the same everywhere.

---

# Simplest Car Following Trac Flow Model.

### Rodolfo R. Rosales

### MIT, Friday March 26, 1999.

These notes describe in some detail the continuum limit behavior of a very simple car following one solved by a set of MatLab scripts in the Athena 18311-Toolkit at MIT, which illustrate the phenomena described here. These are the scripts whose names end with the acronym CFSM.

### Contents

| 1 | The<br>Model.<br>Nondimensionalization.                       | 2  |
|---|---------------------------------------------------------------|----|
| 2 | Continuum<br>Limit<br>of<br>Model.                            | 4  |
| 3 | Numerical<br>Issues.<br>Stiness<br>of<br>the<br>equations.    | 9  |
| 4 | Examples.                                                     | 13 |
| 5 | Notes<br>on<br>the<br>MatLab<br>script<br>quadCFSM.           | 15 |
|   | List<br>of<br>Figures                                         |    |
|   | 1.1<br>Typical  ow<br>and<br>velocity functions.              | 2  |
|   | 5.1<br>Typical initial conditions for script<br>quadCFSM.     | 15 |
|   | 5.2<br>Solution after<br>shocks<br>form.                      | 17 |
|   | 5.3<br>Approximation of the<br>initial wave<br>velocity data. | 19 |
|   | 5.4<br>Comparison of exact<br>and approximate solutions.      | 21 |

MIT, Department of Mathematics, room 2-337, Cambridge, MA 02139.

### 1 The Model. Nondimensionalization.

Consider a line of cars on a road, with car n located at  $\tilde{x}_n = \tilde{x}_n(t)$ , moving at speed  $\tilde{u}_n = \frac{d\tilde{x}_n}{dt}$ . Measure distance  $\tilde{x}$  along the road in the same direction the cars move (so the car velocities  $\tilde{u}_n$  are all non-negative). Number the cars so that  $\{\tilde{x}_n\}$  is an increasing sequence  $(\tilde{x}_{n+1} - \tilde{x}_n) > \text{car length} > 0$  (identify  $\tilde{x}_n$  with the location of (say) the front end of the car).

Remark 1.1 We use tildes over the variable symbols to indicate that we are dealing with dimensional variables. We will use the same symbols (without tildes) to denote the nondimensional versions of the same variables, when we nondimensionalize the equations later on.

Assume now that the drivers follow some rule (such as the ones proposed in problems 61.1 and 61.2 of Haberman's book) prescribing the car speed as a function of the distance to the next car<sup>1</sup>. That is, assume that there is some function (the *car velocity function*)  $\tilde{U} = \tilde{U}(\tilde{\rho})$  such that

$$\tilde{u}_n = \tilde{U}(\tilde{\rho}_n), \quad \text{where} \quad \tilde{\rho}_n = \frac{1}{\tilde{x}_{n+1} - \tilde{x}_n}.$$
 (1.1)

Here we identify  $\tilde{\rho}_n$  with the car density at the position of the  $n^{th}$  car. We also introduce the

<sup>&</sup>lt;sup>1</sup>As long as the situation is not changing too rapidly, this is not unreasonable. Note that in this model we will, implicitly, deal with all the cars as if they were equal copies of each other — all the cars obey exactly the same rules.

notation  $\tilde{h}_n = (1/\tilde{\rho}_n) = \tilde{x}_{n+1} - \tilde{x}_n$  for the car separation. Typical shapes for the car velocity  $\tilde{U}$  and the car flow  $\tilde{Q} = \tilde{\rho}\tilde{U}$  (both functions of  $\tilde{\rho}$ ) are shown in figure 1.1.

Then the model is given by the following set of coupled ODE's

$$\frac{d\tilde{x}_n}{d\tilde{t}} = \tilde{u}_n \,, \tag{1.2}$$

where the velocities and positions are related by equation (1.1). To complete the model we need to give a **boundary condition**. For example, if there are N cars, then the velocity  $\tilde{u}_N$  of the car at the head of the group would have to be prescribed (since (1.1) cannot be used for n = N).

Typical values<sup>2</sup> for the various constants involved are as follows: jamming density  $\rho_J = 160 \ cpm$ , road capacity  $q_m = 1600 \ cph$ , density at road capacity  $\rho_m = 80 \ cpm$  and car velocity at road capacity  $u_m = 20 \ mph$ . If we now assume a length scale L — characterizing a typical length over which the traffic density changes significantly — we can nondimensionalize as follows:

$$\tilde{x_n} = Lx_n$$
,  $\tilde{\rho_n} = \rho_J \rho_n$ ,  $\tilde{u}_n = \frac{q_m}{\rho_J} u_n$ ,  $\tilde{U}(\tilde{\rho}) = \frac{q_m}{\rho_J} U(\rho)$ ,  $\tilde{Q}(\tilde{\rho}) = q_m Q(\rho)$  and  $\tilde{t} = \frac{L\rho_J}{q_m} t$ . (1.3)

Then the equations take the form

$$\frac{dx_n}{dt} = u_n = U(\rho_n) \quad \text{and} \quad \rho_n = \frac{\epsilon}{x_{n+1} - x_n}, \tag{1.4}$$

where  $\epsilon = 1/(L\rho_J)$  is a small nondimensional number — with the values above and with L a large fraction of a mile, we get  $\epsilon = O(10^{-2})$ . Note also that the nondimensional versions of the car velocity and car flow functions have the same forms as the dimensional ones; but with the jamming density and road capacity set to one.

Remark 1.2 In the nondimensionalization above, the choice of L was left a bit ambiguous. While the other parameters follow from actual measurements and are pretty fixed (for a given road), the length scale is more flexible and depends on the particular solution of the equations one is looking at. On the other hand, while L can (at least in principle) be arbitrarily large<sup>3</sup>, there is an approximate minimum size  $L_{min}$  it can have. Consider the way we defined L, which requires (in particular) that we be able to distinguish a length scale. Thus, think of a typical perturbation to the density

<sup>&</sup>lt;sup>2</sup>See sections 62 and 63 in Haberman's book

<sup>&</sup>lt;sup>3</sup>Consider the example where all the cars are equally spaced, so that  $L=\infty$ .

 along the road | say, a hump or a sinusoidal up and down. This perturbation is\marked" by a discrete set of points (the car positions) and needs a minimum number of them before itcan be clearly identied | a reasonable number4 being about twenty or so. With the kinds of car densities implied by m, we see that Lmin cannot be much shorter than about <sup>a</sup> quarter of <sup>a</sup> mile (best we can have, at near jamming density, is about an eighth of a mile). Thus our assumption above (where we took L a large fraction of a mile) is quite reasonable. This, in addition to = O(102) , yields (in the nondimensionalization above in (1.3)) a time scale LJ qm order of a few minutes | 6 min for L a ful l mile and 3 min for half a mile.

Remark 1.3 Continuing with the issue of the length scale L: we also need (of course) that a length scale exist! The cars could be randomly distributed on the road, in which case there would not be much of a length scale to be identied. However, this a situation that cannot persist: think of the example of three cars, with the rst two close and the third far behind. Then the third car would end up moving faster than the second and the two distances would tend to even out. If, on the other hand, it is the second and third car that are closer, then the second car would move faster than the third and (again) the distances would tend to even out. In general, there is a tendency for the cars to settle down to situations where the car separations do not vary very rapid ly, except for a few isolated places where \jumps" occur. This process is il lustrated by the MatLab script randCFSM in the Athena 18311-Toolkit, which solves the equations in this model with random initial separations

In remark 1.2 we considered the question of what is the minimum size the length scale L | used in equation (1.3) to nondimensionalize lengths | can have. In this section we will consider a somewhat opposite situation, where L becomes larger and larger. Equivalently:

consider the limit: 
$$\epsilon \to 0$$
 in the model equations (1.4). (2.1)

Of course, this is only an \ideal" limit we are taking. In practice is xed. However, since is small, we expect the limit will give us useful information regarding the behavior of the model (1.4).

<sup>4</sup>Think of how many points per wavelength are needed to have a reasonable drawing of a sine wave.

Remark 2.1 Let  $N_L$  be the typical number of cars that make the features (bumps, whatever) in the traffic density that were used (earlier, in equation (1.3)) to determine the length scale L. These two quantities are related by an equation of the form  $N_L = \rho_* L$ , where  $\rho_*$  is some average density<sup>5</sup> (which cannot be too different from, say,  $\rho_m$ ). Thus, letting  $\epsilon \to 0$  amounts to both making L and  $N_L$  large, since  $\epsilon = \frac{1}{L\rho_J} = \frac{\rho_*}{\rho_J N_L}$ . In fact, note that  $\epsilon = O(N_L^{-1})$  — since  $\frac{\rho_*}{\rho_J} = O(1)$ .

Because of the way the equations were nondimensionalized, we see that:

• The separation between cars satisfies

$$h_n = x_{n+1} - x_n = O(\epsilon). (2.2)$$

This follows because in equation (1.4)  $\rho_n = O(1)$ .

• Significant variations in car separation (i.e., in  $\rho_n$ ) occur over O(1) distances. Thus, it is reasonable to assume that **there is a function**  $\rho = \rho(x,t)$  such that

$$\rho_n = \rho(x_n, t) \,. \tag{2.3}$$

We expect  $\rho$  to be reasonably nice and (generally) have O(1) partial derivatives  $\frac{\partial \rho}{\partial t}$  and  $\frac{\partial \rho}{\partial x}$ .

We now rewrite the equations for the model (1.4) in terms of the densities rather than the car positions. Thus we have

$$\frac{d}{dt}\rho_n = -\epsilon^{-1}\rho_n^2 \left(u_{n+1} - u_n\right) \quad \text{or, equivalently:} \quad \frac{d}{dt}\rho_n = -\rho_n \left(\frac{u_{n+1} - u_n}{x_{n+1} - x_n}\right), \tag{2.4}$$

where the densities, velocities and positions are related, in the usual way, by  $u_n = U(\rho_n)$  and  $\rho_n = \epsilon/(x_{n+1} - x_n)$ . Again, in addition to initial conditions a boundary condition is needed. For example, if there are N cars, then velocity (or the density)  $u_N$  of the leading car would be required.

From equations (2.2 – 2.3) it is clear that the expression  $\left(\frac{u_{n+1}-u_n}{x_{n+1}-x_n}\right)$  can be replaced by  $\frac{\partial u}{\partial x}(x_n,t)$ 

in the limit given by (2.1), where  $u = u(x,t) = U(\rho(x,t))$ . Furthermore, from (2.3) it follows that  $\frac{d}{dt}\rho_n = \left(\frac{\partial\rho}{\partial t} + u\frac{\partial\rho}{\partial x}\right)(x_n,t)$  — using the chain rule. Substituting all this into equation (2.4) we see

that  $\rho$  above in (2.3) must satisfy the PDE

$$0 = \frac{\partial \rho}{\partial t} + \frac{\partial q}{\partial x} = \frac{\partial \rho}{\partial t} + c \frac{\partial \rho}{\partial x} \tag{2.5}$$

<sup>&</sup>lt;sup>5</sup>For example: we used  $\rho_* = \rho_m$  in remark 1.2 (with  $N_L \approx 20$ ) to determine  $L_{min}$ .

in the limit  $\epsilon \to 0$ , where  $q = \rho u = \rho U(\rho) = Q(\rho)$  and  $c = c(\rho) = \frac{dq}{d\rho}$ . Thus we obtain the **same** continuous traffic flow model that was developed in the lectures (see the lecture notes or the book by Haberman) using a phenomenological approach and conservation of cars.

An interesting point arises now. The solution of the PDE (2.5) (by characteristics, say) generally breaks down after a finite time. That is, infinite derivatives and multiple values develop after some critical time — even if the initial data are smooth. On the other hand, it is quite clear that the model (1.4) — equivalently (2.4) — cannot develop anything even resembling multiple values. In fact, there is no breakdown either: provided the initial values for the car positions are such that the densities all satisfy  $0 < \rho_n(0) \le 1$ , then the solution will exist for all times and the bound  $0 < \rho_n(t) \le 1$  will be satisfied. The proof of this is rather easy: (i) The density can go to zero only if the distance between cars goes to infinity, but this cannot happen because the car velocities are bounded. (ii) Neither can the density go beyond one, for as soon as  $\rho_n$  reaches one, the  $n^{th}$  car will stop, while the  $(n+1)^{th}$  car will be moving at a non-negative velocity. (iii) Thus, the condition  $0 < \rho_n \le 1$  will be preserved. (iv) This is enough to guarantee a solution for all times, for a solution can cease to exist only if it either "blows up" or if it reaches a singularity in the equations. However, as long as  $0 < \rho_n \le 1$ , neither of these two things can happen.

Note 2.1 Notice that the argument in (ii) above shows that a density of one can be maintained only if the density is identically one from some car on forward. Else a decrease in density will propagate backward through the cars, as the cars where  $\rho_n = 1$  will not move. On the other hand, if the density is one from some point on, then a "wave" carrying a value of one will move backward through the road, as cars move into the ones that are stopped ahead in the line.

The question is now: what happens in the limit (2.1) beyond the time where the solution of the PDE (2.5) breaks down? This question is addressed by the MatLab script quadCFSM in the Athena 18311-Toolkit — see section 5 here. This script solves the model equations (1.4) — with initial conditions that correspond to a smooth positive hump for (2.5) — in the limit (2.1). Actually not "in the limit", but for  $\epsilon$  small enough that one can see what will happen when  $\epsilon \to 0$ . With the initial conditions used by quadCFSM the solution to (2.5) breaks down in a finite time.

(2.6)

On the other hand, what the numerical experiments show is:

- 1. As long as the solution of (2.5) behaves nicely, it does approximate quite well the behavior of the solution of (1.4).
- 2. The solution of (2.5) exhibits breakdown with formation of infinities in the derivatives in the regions where the density  $\rho$  is increasing with x. In these regions, the solution of (1.4) also shows progressive steepening of the density profile. However, rather than "topple over" and develop multiple values (as happens with the solution by characteristics of (2.5)), the solution of (1.4) develops a very sharp transition just a few cars wide from one value of  $\rho$  to a bigger one. In effect, the function  $\rho$  in (2.3) develops a discontinuity that stops multiple values from arising.
- 3. Other than the phenomena described in the prior item, the  $\epsilon \to 0$  limit of (1.4) is still described by (2.5) that is, away from the discontinuities in the density, (2.5) applies.

Thus the proper description of the limit in (2.1) is still (2.5), but we must add discontinuities (across which the density increases) in the solution to avoid the formation of multiple values. These discontinuities are called SHOCKS and cannot be placed arbitrarily, since:

• Shocks must move so that cars are conserved. If  $x = x_S(t)$  is the shock position, then

$$\frac{d}{dt}x_S = \frac{[q]}{[\rho]},\tag{2.7}$$

where we use the notation [] to denote the jump in a function across a discontinuity. This condition is called the **Rankine–Hugoniot jump condition**.

• The (so called) **entropy condition** must hold

In terms of the **characteristic curves** for equation (2.5), this means that the curves **converge** into the shock — and terminate there. Thus the shock path acts as a "cut" in space—time, where the characteristic curves end. This prevents their crossing and the formation of multiply valued regions in the solution.

It can be shown that these two conditions are enough to uniquely determine the solution of (2.5), now for all times and without any multiple values arising. Thus, this "augmented" model (i.e. equations (2.5), plus discontinuities governed by (2.7) and (2.8)) is the result of (2.1).

Remark 2.2 The condition (2.8) is very important. No discontinuous transitions are developed by (1.4) that are not associated with an increase in the density. This is very clear intuitively; when the density is decreasing the cars move faster the further ahead they are in the line and no steepening tendency arises (exactly the opposite occurs). It is only when the density increases that sharp transitions are generated and maintained.

We now examine the derivation leading to equation (2.5) and ask: what did we miss that would explain the behavior in (2.6)? The answer has to do with the assumption right below (2.3) that  $\rho$  has O(1) partial derivatives — which it obviously does not. Thus there will be extra contributions (that we neglected) near shocks to equation (2.5). Specifically, consider the step where we replaced  $\left(\frac{u_{n+1}-u_n}{x_{n+1}-x_n}\right)$  by  $\frac{\partial u}{\partial x}(x_n,t)$ . In a more precise calculation (to estimate the error made by the substitution) we expand  $u_{n+1}$  in a Taylor series centered at  $x_n$ . That is  $u_{n+1}=u_n+u_n^{(1)}h_n+\frac{1}{2}u_n^{(2)}h_n^2+\ldots$ , where  $h_n=x_{n+1}-x_n$  and we use the notation  $u_n^{(j)}=\frac{\partial^j u}{\partial x^j}(x_n,t)$ . Thus

$$\left(\frac{u_{n+1}-u_n}{x_{n+1}-x_n}\right) = \frac{\partial u}{\partial x}(x_n,t) + \frac{1}{2}u_n^{(2)}h_n + \frac{1}{6}u_n^{(3)}h_n^2 + \dots = \frac{\partial u}{\partial x}(x_n,t) + \frac{1}{2\rho_n}\epsilon u_n^{(2)} + \frac{1}{6\rho_n^2}\epsilon^2 u_n^{(3)} + \dots,$$

where we used (1.4) to replace  $h_n$  by  $\rho_n$ . In this expression we can neglect the higher order terms (as we did when obtaining (2.5)) only if we can argue that  $\epsilon^{j-1}u_n^{(j)}$  is small for j > 1. But, when the partial derivatives of  $\rho$  — thus those of u — are not bounded, we cannot do this. Then all these extra terms will become important (an cannot be neglected, as we did in (2.5)) near shocks.

To have an idea of what the effect of these extra terms is on the behavior of the solution, it is enough to just keep one extra term and see how this changes (2.5)). Using  $u = U(\rho)$  to replace derivatives of u by derivatives of  $\rho$ , this yields the equation

$$\frac{\partial \rho}{\partial t} + c \frac{\partial \rho}{\partial x} = \frac{1}{2} \epsilon \frac{\partial}{\partial x} \left( \nu(\rho) \frac{\partial}{\partial x} \rho \right) , \qquad (2.9)$$

where  $v = -\frac{dU}{d\rho}$  (notice that  $\nu$  is a POSITIVE function of  $\rho$ ). Thus a (small) amount of diffusion is added to equation (2.5). As long as the derivatives are bounded, the effects of this

diffusion can be neglected. But, when the density profile steepens, it becomes important and begins to "fight" the steepening — this is what diffusion does. Eventually a balance between the two effects (diffusion and the tendency to steepen) is achieved, within a narrow region of high derivatives.

It is easy to estimate the width the balanced region in the prior paragraph should have, as follows (this will be the **shock width**). Let this width be  $w_S$ . Then, while  $\rho$  will remain O(1) near the shock, each derivative will be larger than the prior one by a factor  $w_S^{-1}$ . Thus, in equation (2.9), the left hand side will have size  $w_S^{-1}$  while the right hand side has size  $\epsilon w_S^{-2}$ . Clearly, for balance we need  $w_S = \epsilon$ . Since  $\epsilon$  is also the order of magnitude of the car separation, this **predicts a shock width of a few cars**, which agrees well with the numerical results in (2.6).

## 3 Numerical Issues. Stiffness of the equations.

We now go back to the discrete equations and perform an analysis to see what sort of time scales are involved in their behavior. This is important for many reasons, some of which we will explain later on. In particular: in any numerical calculation we must make sure that all times scales are handled properly, even if they are not immediately apparent in the solution — the precise meaning of this last rather strange statement will be clarified below in remark 3.2 (second point).

Consider a situation where the car densities deviate slightly from some constant state  $\rho_*$ . Thus:

$$\rho_n = \rho_* + \delta_n \,, \tag{3.1}$$

where the perturbations  $\delta_n$  to the density are assumed small. Substituting this formula in the equations for the model (use the first form in equation (2.4), which involves only the densities  $\rho_n$  and the velocities  $u_n = U(\rho_n)$ ) and neglecting higher order terms in the perturbations, we obtain:

$$\frac{d\delta_n}{dt} = \epsilon^{-1} \nu_* \rho_*^2 \left( \delta_{n+1} - \delta_n \right) , \qquad (3.2)$$

where  $\nu_* = \nu(\rho_*)$  and  $\nu$  is as in (2.9). This last equation is linear and can be solved using eigenmodes. Specifically, the general solution is a linear combination<sup>6</sup> of the fundamental modes:

$$\delta_n = e^{(ikn + \sigma t)}, \text{ with } \sigma = \epsilon^{-1}\nu_*\rho_*^2(e^{ik} - 1) = \epsilon^{-1}\nu_*\rho_*^2\{(\cos(k) - 1) + i\sin(k)\},$$
 (3.3)

<sup>&</sup>lt;sup>6</sup>Notice that this is the same type of solution used in the von Neumann stability analysis of numerical schemes.

where  $-\pi \leq k \leq \pi$  (these solutions are periodic in the wavenumber k, since the exponential is sampled only at integer values). The values of  $\sigma$  determine the time scales involved in the solution. We note that all the  $\sigma$ 's have negative real parts, so that all these solutions decay (i.e. the constant state  $\rho_*$  is a stable solution of (2.4)). In fact, the shorter the wavelength  $\lambda = \frac{2\pi}{k}$ , the faster the decay rate. The maximum decay rate corresponds to solutions that oscillate with a wavelength of two car separations  $(k = \pm \pi)$ , with  $\sigma = -2\epsilon^{-1}\nu_*\rho_*^2$ . This corresponds to a time scale  $\tau_m = \frac{\epsilon}{2\nu_*\rho_*^2}$ .

Remark 3.1 We note that  $\tau_m$  is a very short time. As pointed out in remark 1.2, O(1) times in the nondimensional equations typically correspond to a few minutes in dimensional units. Since  $\epsilon = O(10^{-2})$ , we see that  $\tau_m$  corresponds to a dimensional time scale that must be measured in seconds! Now we ask and answer the questions: What exactly is the meaning of the time scale  $\tau_m$ ? What role does it play in the time evolution of the equations? For this we go back to the point made in remark 1.3. It is quite clear that  $\tau_m$  is precisely the time scale over which rapid variations in the car separations are "wiped out" by the time evolution of the model. This is the process illustrated by the MatLab script randCFSM. After these variations are eliminated, this time scale plays no role, except to the extent that it keeps eliminating any such small variations that might arise due to "external" perturbations.

Remark 3.2 The last statement in the prior remark appears innocuous, but it is actually not. What do we mean here by "external" perturbations?

• First: the equations (1.4) are a pretty crude model for traffic flow; it is pretty unrealistic to assume that the drivers respond only to the distance to the car right ahead (and then that they can adjust their car velocity instantaneously to the prescribed u). We are using this model only as a simple example to illustrate some of the phenomena involved. However, even if we were to set up an ideal situation, it would still be an approximation. Thus, all the neglected "little" things that the model ignores would constantly introduce changes (perturbations) into the solution. In addition one would still have to consider truly external perturbations, such as a new car added (or one gone) to the line. Note that it is important that a mathematical model be "stable" to such perturbations, else it is worthless (as the neglected effects would be able to completely change the nature of the solution). On this last account (at least), the model (1.4) behaves the right way.

 Second: another (very important) source of \external" perturbations arises when solving the equations numerically. This is because any numerical scheme wil l, necessarily, involve approximations | which wil l introduce errors into the solution. These errors better not grow, else disaster wil l strike. Now, the exact equation here would very quickly dissipate them, but this need not be so with a numerical scheme if one is not careful. Precisely because the equations being approximated are so forceful about dissipating errors, naive numerical approximations can easily over do the eect and end up amplifying the perturbations! A simple example of this is provided by the equation y\_ = y, with large and positive. The solutions of this simple equation decay very fast to zero. But, approximate the equation by the naive forward Euler scheme: yn+1 <sup>=</sup> yn ynt, where yn <sup>=</sup> y(n t).Then yn = (1 t)ny0 and, unless t 2=, the numerical solution blows up! Thus, to get this scheme to behave properly one needs to take a time step which is as short as the time scale ofdecay. For the equations given by (1.4) this would mean a time step as short as m, which is disastrous! That is, we would be forced to resolve time scales in the order of seconds (or fractions), while in fact the phenomena we are real ly interested in fol lowing take place over minutes or even hours. In fact, nothing happens over seconds, we have to keep such a smal l time step just so the numerical scheme does not go unstable.

Problems that present short time scales that are irrelevant to the solutions one is trying to compute (but arise because smal l deviations from these solutions are very quickly \squashed" by the governing equations) are cal led numerically STIFF and require special care. Naive approximations invariably lead to very inecient codes, requiring unrealistical ly smal l time steps. We wil l not go into these problems here, but you should be aware of their existence.

Remark 3.3 Actual ly, as pointed out earlier, al l the 's in (3.3) have negative real parts, so al l the scales decay. Thus, if we wait long enough, not just the short wavelength (a few car distances long) variations wil l vanish, but the long ones as wel l. Although this conclusion isbased on the linearized analysis in (3.1 { 3.3) and thus is valid only for smal l perturbations from a constant, it is actual ly true for the whole set of equations (as a bit of numerical experimentation wil l quickly show). This then makes it necessary that we revisit the statements made in remark 1.3, and state them in a more precise way. The \natural" state for the model is to go into a situation where the

length scale satises L = 1.Any length scale present in the initial data wil l eventual ly be wiped out (unless it keeps on being re-introduced by external perturbations). But the large scales have decay times much longer than m <sup>|</sup> since the real part of behaves like <sup>k</sup> <sup>2</sup> for k smal l. Thus, while short scale variations wil l be quickly dampened (and wil l become irrelevant), longer scales wil l remain for \reasonable" times. Thus, we are back to being rather vague about the meaning of the space scale L. Basical ly, we have to argue phenomenological ly: it is produced by processes that are very complicated and are not included in the model. At the level of simplicity ofthis model, there is not much more that we can do about it. We must take this scale L as an external input, on the same footing as other quantities such as J , etc. The value for Lmin computed earlier gives an idea of what is reasonable (i.e. anything larger than Lmin and smal ler than the length of the road), but this is about as much as we wil l be able to say here.

Remark 3.4 One can make an interesting observation regarding the size of m. It is clear that the model (1.4) does not al low accidents (car col lisions). These would require (at the very least) that n <sup>&</sup>gt; <sup>1</sup> somewhere, sometime. But we showed earlier (see the paragraph above the note 2.1) that the equations wil l not let this happen. The time m is closely associated with the mechanism that prevents this from happening. Now notice that real accidents happen7 (even when the drivers attempt to fol low the recommended rules of separation between cars versus speed) because of eects we have not considered in the model, such as: (a) human reaction time, (b) cars cannot accelerate or stop instantaneously, etc. Unlike the mechanism behind the time m, which is stabilizing, these other eects destabilize. The interesting fact is that the time scales associated with them are about the same as those given by m. But perhaps this is not too surprising, if one postulates a tendency to \push the envelope" in terms of safety. That is: drivers wil l drive as fast and as close to the next car as it is \reasonably" safe, where this means that the stabilizing eects wil l be kept at a \multiple" of the de-stabilizing ones | but not too large a multiple!

Finally, just for completeness, we end this section by showing how the linear perturbation analysis in (3.1 { 3.3) looks like in terms of the car positions. In this case we have

$$x = x_0 + n \frac{\epsilon}{\rho_*} + u_* t + y_n \,, \tag{3.4}$$

<sup>7</sup>Let us exclude here such things as the drivers falling asleep, etc.

where  $u_* = U(\rho_*)$  and  $y_n$  is small. Then

$$y_{n+1} - y_n + \frac{\epsilon}{\rho_*} = x_{n+1} - x_n = \frac{\epsilon}{\rho_n} = \frac{\epsilon}{\rho_*} - \frac{\epsilon}{\rho_*^2} \delta_n$$

where we used (3.1) and neglected quadratic terms in the perturbations. Thus

$$\delta_n = -\frac{\rho_*^2}{\epsilon} \left( y_{n+1} - y_n \right) .$$

Since  $u_n = U(\rho_* + \delta_n) = u_* - \nu_* \delta_n$ , we then have (using (3.4)

$$\frac{dy_n}{dt} = \frac{1}{2\,\tau_m} \left( y_{n+1} - y_n \right) \,, \tag{3.5}$$

which (of course) is the same equation the  $\delta_n$ 's satisfy!

## 4 Examples.

In this section we consider examples of choices for the velocity  $U(\rho)$  and flow  $Q(\rho)$  functions. We stress that these are just qualitative examples, not actual fits to measured data (which need not give simple formulas). Thus one must be careful about not drawing too many conclusions from them, specially of the too precise quantitative type.

**Example 4.1** The simplest example is that of a quadratic flow function,

$$\tilde{Q} = \frac{4 q_m}{\rho_J^2} \tilde{\rho} (\rho_J - \tilde{\rho}) \quad and \quad \tilde{U} = \frac{4 q_m}{\rho_J^2} (\rho_J - \tilde{\rho}).$$

This yields  $\rho_m = \frac{1}{2} \rho_J$ ,  $u_m = \frac{2 q_m}{\rho_J}$  and a maximum car velocity  $u_{max} = 2 u_m$ . These numbers are compatible with the typical values given earlier above equation (1.3), except that the maximum car velocity seems a bit low (though not out of range). Then again, the typical values given are from measurements in the NYC Lincoln tunnel in the 1950's (where, perhaps, a maximum car speed of 40 mph was reasonable). In general these numbers are meant only as ballpark figures. After nondimensionalization, we have the forms

$$Q = 4\rho(1-\rho), \quad U = 4(1-\rho) \quad and \quad c = 4(1-2\rho).$$
 (4.1)

In this case the shock speed in (2.7) is the average of the characteristic speed c across the shock and  $\nu = 4$  in (2.9). In particular  $\tau_m = \frac{\epsilon}{8\rho_z^2}$ .

**Example 4.2** Another simple example follows from the rule stating: for each unit  $v_r$  of some speed  $(v_r = 10 \ mph \ \text{is typical})$  the separation to the next car should increase by at least one car length  $\ell$ . If we apply this rule exactly, then  $\frac{\tilde{u}_n}{v_r}\ell + \ell = \tilde{x}_{n+1} - \tilde{x}_n = \frac{1}{\tilde{\rho}_n}$ . From this and the speed limit, we obtain

$$\tilde{u} = \tilde{U}(\tilde{\rho}) = \min\left(u_{max}, v_r \frac{\rho_J - \tilde{\rho}}{\tilde{\rho}}\right) \quad \text{and} \quad \tilde{Q} = \tilde{\rho} \,\tilde{U} = \min\left(\tilde{\rho} \, u_{max}, v_r \, (\rho_J - \tilde{\rho})\right),$$

where  $\rho_J = \ell^{-1}$ . This yields

$$u_m = u_{max}$$
,  $\rho_m = \frac{v_r \rho_J}{v_r + u_{max}}$  and  $q_m = \rho_m u_m = \frac{v_r \rho_J u_{max}}{v_r + u_{max}}$ .

With  $u_{max}=50$  mph,  $v_r=10$  mph and  $\rho_J=160$  cpm this yields  $\rho_m\approx 27$  cpm and  $q_m\approx 1330$  cph—not altogether unreasonable numbers. One point though is that  $\rho_J=160$  cpm corresponds to  $\ell=33$  ft, which is a tad too long. The reason for this is that the cars stop when the distance to the next car is bigger than zero (not zero, as this rule would have). Thus, if one uses  $\rho_J=\ell^{-1}$  with an actual car length, too high a jamming density results—so we use a car length that is about twice actual to compute  $\rho_J$ . In other words, this rule is rather unrealistic for low velocities. The implementation of the speed limit is also rather crude and gives the strange feature of a corner (at the maximum) in the flow profile  $\tilde{Q}=\tilde{Q}(\tilde{\rho})$ . After nondimensionalizing, we have

$$Q = min\left(\frac{\rho}{\alpha}, \frac{1-\rho}{1-\alpha}\right), \quad U = min\left(\frac{1}{\alpha}, \frac{1-\rho}{\rho(1-\alpha)}\right) \quad and \quad c = \frac{1-2\alpha + sign(\alpha-\rho)}{2\alpha(1-\alpha)}, \quad (4.2)$$

where  $0 < \alpha = \frac{\rho_m}{\rho_J} < 1$ . Note the strange feature of a piece-wise constant wave speed c. Thus, in the continuum limit, the parts of the density profile with  $\rho > \alpha$  move (backwards) at constant<sup>8</sup> speed  $(\alpha - 1)^{-1}$ . Similarly, the parts with  $\rho < \alpha$  move (forward) with speed  $\alpha^{-1}$ . Shocks will arise where these two kinds of behaviors "collide" and will move at the speed given by (2.7), with a jump in  $\rho$  (as x increases) from  $\rho < \alpha$  to  $\rho > \alpha$ . This is pretty strange behavior! This case is implemented by strangeCFSM in the Athena MatLab 18311-Toolkit.

Finally, note that an alternative formulation of the rule in this example is that the time it would take a car to cover the distance to the next car should be a given fixed  $\Delta t$ . It is easy to see that the correspondence is  $v_r = \frac{\ell}{\Delta t}$  — since this rule simply states that  $\tilde{u} \Delta t = \frac{1}{\tilde{\rho}} - \ell$ . In particular,  $v_r = 10$  mph and  $\ell = 16$  ft correspond to  $\Delta t = 1.1$  sec, since a mile is 5280 ft.

<sup>&</sup>lt;sup>8</sup>Therefore: no wave shape deformation.

## 5 Notes on the MatLab script quadCFSM.

The MatLab script quadCFSM in the Athena 18311-Toolkit solves the equations in (1.4) using the quadratic flow function (4.1) in example 4.1. A finite number of cars N is used, with  $x_1 < x_2 < \ldots < x_N$  and the density  $0 < \rho_N < 1$  at the leading car given and **constant**<sup>9</sup>. The **initial conditions** are such that (see figure 5.1)  $x_N(0) = 0$ ,  $x_1(0) < -\pi$  and

$$\rho_n(0) = \rho_N + (1 - \rho_N)r(x_n) \quad \text{for} \quad 1 \le n < N,$$
(5.1)

with r = r(x) a symmetric positive "hump" in  $-\pi < x < 0$ ,  $r(\frac{1}{2}\pi) = 1$  and  $r \equiv 0$  outside  $[-\pi, 0]$ .

Remark 5.1 The cars are placed so that  $x_p(0) = -\pi$  for some p > 1 (thus  $N_h = N + 1 - p$  is the number of cars in the hump, with  $1 < N_h < N$ ). Then, from (1.4), we must have

$$\pi = x_N(0) - x_p(0) = \sum_{n=p}^{N-1} \frac{\epsilon}{\rho_n}.$$

<sup>&</sup>lt;sup>9</sup>The leading car velocity is then also constant  $u_N = 4(1 - \rho_N)$ .

This equation determines the value of  $\epsilon$  in terms of the number of cars in the hump and the densities given by (5.1). Note also the relationship

$$\epsilon(N_h - 1) = \sum_{n=p}^{N-1} \rho_n(x_{n+1} - x_n).$$

As the number of cars increases (continuum limit) this leads to the formula

$$\lim_{N_h \to \infty} \epsilon(N_h - 1) = \int_{-\pi}^0 \rho(x) dx = \pi \rho_N + (1 - \rho_N) A_r,$$
 (5.2)

where  $\rho = \rho(x)$  is as in (5.1) above and  $A_r$  is the area under the function r = r(x).

We now describe the behavior in the **continuum limit** of the problem solved by this script, using the theory of shocks and characteristics developed in section 2 here and elsewhere. The results of this analysis are built into the scheme graphics, that compare the actual solution of the equations (1.4) with the predictions here. The good agreement found is a confirmation of the correctness of the theory in section 2. In the continuum limit we use equation (2.5) to deal with the well behaved parts of the solution — where we can use the characteristic method — and equations (2.7) and (2.8) to deal with the discontinuities (shocks).

Notice that in this case the wave speed satisfies  $c = 4 - 8\rho$  and is a linear function of the density  $\rho$ . It then follows that in this example c is also a conserved quantity. Thus we can consider the solution of the continuum limit problem fully in terms of c. It is easy to see that c satisfies the equation

$$0 = \frac{\partial c}{\partial t} + \frac{\partial}{\partial x} (\frac{1}{2}c^2), \quad \text{with} \quad c(x,0) = c_N - C(x),$$
 (5.3)

where  $-4 < c_N = 4 - 8\rho_N < 4$  and  $C = (4 + c_N)r(x)$ . Thus the initial profile for c has a "dip" instead of a "hump". In terms of c the shock condition (2.7) states: **the shock speed is the average of the characteristic speeds on the sides of the shock**.

# WARNING: this is true only for this case of a quadratic flow function $Q = Q(\rho)$ .

Similarly, (2.8) becomes: **across shocks** c **decreases** — which is true for **all** flow functions Q.

The characteristic curves are given by  $\frac{dx}{dt} = c$  — with c constant. Furthermore,  $\frac{dS}{dt} = -S^2$  on them, where  $S = c_x$  is the slope of the solution. This shows that S will eventually go to  $-\infty$  on any characteristic where S starts negative, at time  $t = -1/S(\zeta, 0)$ . Here  $\zeta$  is the value of x on the

characteristic at time <sup>t</sup> = 0 and S(x; 0) = dC dx (x). This follows from the general solution of the equation above for S along characteristics:

$$S = \frac{S(\zeta, 0)}{1 + S(\zeta, 0)t}.$$

An analysis of this problem shows that a shock will form | starting on the characteristic where <sup>S</sup> is negative and has the largest absolute value. Let this be given by Sm <sup>=</sup> S(m; 0) = dC dx ( ).

$$t_S = -\frac{1}{S_m}$$
 and  $x_S = \zeta_m + (c_N - C(\zeta_m))t_S$ .

Note that m must correspond to a location on the back end of the initial hump.

Figure 5.2: Solution after a shock forms. The gure shows how the multiple values in the solution by characteristics are eliminated by the shock. The shock is located so that the area under the density curve (number of cars) is preserved. In this case, because the ow function isquadratic, thearea under the wave velocity curve is also preserved.

Eventually (time "large") most of the characteristics that start with x somewhere in the the position of the initial hump "die" at the shock. More precisely, the density disturbance will be made up only from characteristics that start near the leading edge (x = 0) of the initial hump, i.e.

$$x = ct + \zeta$$
, with  $c = c_N - C(\zeta)$  and  $\zeta$  small and negative. (5.4)

The mechanism behind this is simple. An inspection of the solution by characteristics (see figure 5.2) shows that (as time advances) the initial hump in  $\rho$  (equivalently, in c) deforms. The back part steepens while the front part stretches. Eventually a shock forms on the back and all the details of the variations in the density are absorbed by it: the characteristics reach the shock and terminate there. The only part that remains is the very stretched out front. Because the stretching is linear in  $\rho$ , this part becomes a straight line, joining the front edge of the shock with the position of the leading characteristic starting at the front edge of the initial hump (i.e.  $x = c_N t$ ). Thus the wave takes a triangular form (backward saw-tooth) with the shock on the back and a **corner moving** at the characteristic speed  $c_N$  at the front. Furthermore, because of conservation, the total area in the saw-tooth must be equal to that in the original hump. We can be a bit more precise using (5.4), that yields the approximation  $c \approx \frac{x}{t}$  because  $\zeta$  is small. Then

1. There is a **shock** at 
$$x_S = c_N t - \sqrt{2tA}.$$
2. For  $x_S < x \le c_N t$  
$$c = \frac{x}{t}.$$
3. Elsewhere 
$$c = c_N.$$
4. The car density follows from 
$$\rho = \frac{4-c}{8}.$$

Here A is the area of the bump in c. That is

$$A = \int_{-\pi}^{0} C(x)dx = (4 + c_N)A_r \approx 8(\epsilon(N_h - 1) - \pi\rho_N),$$

where we have used (5.2) and the fact that  $4 + c_N = 8(1 - \rho_N)$  to write the last (approximate) equality. The formula for  $x_S$  follows because this area must be conserved. Specifically, note that the value of c immediately ahead of the shock is given by

$$c_S = \frac{x_S}{t} = c_N - \sqrt{\frac{2A}{t}} \,.$$

The value of  $x_S$  is selected so that the area of the triangular saw-tooth equals A. That is, so that the equation  $2A = (c_N - c_S)(c_N t - x_S)$  holds. Note that here we have used the fact that c itself is conserved, as stated earlier in (5.3).

A more detailed justification of the arguments above can be found in the book by G. B. Whitham: Linear and Nonlinear Waves. Hopefully, it will also be done in the lectures.

Of course, the triangular shape is achieved exactly only for t ! 1, so that these are not very good approximations as far as the script is concerned (which cannot run the solution for a very long time, particularly in the continuum limit when N has to be large). The main source of error occurs in terms of space and time translations. That is, the shape of the solution described by (5.5) is achieved fairly quickly, but it is not properly centered10 . The source of these errors is that in (5.4)

Thus, in order to do the graphical comparisons of the continuum limit with the actual solutions of the (1.4), the script quadCFSM uses an improved approximation, which we describe next (the idea is actually very simple). As stated earlier, after a while the details of the solution are

determined only by the part of the initial data close to the origin, with the rest meaningful only as far as determining the area parameter A. Thus, instead of reducing the information about this

<sup>10</sup>Given any solution <sup>c</sup> = c(x; t), <sup>c</sup> = c(x x;<sup>t</sup> t) is also a solution (for any constants x and t). The problem with the approximation (5.5) is mainly the existence of displacements xand t it does not account for.

zone to just the fact that it is "near" x = 0 where (at t = 0)  $c = c_N$ , we approximate the initial data for x negative near the origin as follows (see figure 5.3):

$$c(x,0) \approx c_N + Bx$$
 for some constant  $B > 0$ . (5.6)

In terms of (5.3) this just means that we write  $C \approx -Bx$ . With initial conditions of this form, equation (5.3) can be solved exactly. Thus, we replace the approximation  $c \approx \frac{x}{t}$  used earlier for the front part of the sawtooth, by the solution that follows from initial conditions as in (5.6). Other than this, we use the same ideas that lead to (5.5), to obtain the **improved approximation**:

1. There is a **shock** at 
$$x_S = c_N t - \sqrt{\frac{2A(1+Bt)}{B}}$$
.  
2. For  $x_S < x \le c_N t$   $c = c_N + \frac{B}{1+Bt}(x-c_N t) = \frac{x-x_*}{t-t_*}$ , where  $x_* = c_N t_*$  and  $t_* = -1/B$ .  
3. Elsewhere  $c = c_N t_*$  and  $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c = c_N t_*$   $c$ 

Just one issue remains now and it is how to best choose B. For a given target time around which one desires the approximation to be good, one can use (5.5) to get an estimate of what is the range of characteristics that are making up the front of the saw-tooth. That is, one can determine an interval  $x_{\ell} \leq x \leq 0$  such that the characteristics originating there at time t = 0 do not die at the shock up until after the target time. It is then over this range  $x_{\ell} \leq x \leq 0$  that we need the approximation (5.6) to hold. Of course, the target time cannot be too small, for the range  $x_{\ell} \leq x \leq 0$  has to be small enough that an approximation of the form (5.6) makes sense. Once  $x_{\ell}$  is determined, we can choose B by conservation of area (i.e. cars). That is, we require that the area under the straight line (5.6) be the same as the area under the curve it replaces. This yields the equation

$$\frac{1}{2}Bx_{\ell}^{2} = \int_{x_{\ell}}^{0} (c_{N} - c(x, 0))dx = 8 \int_{x_{\ell}}^{0} (\rho(x, 0) - \rho_{N})dx.$$

Now we can associate  $x_{\ell}$  with the initial position of one of the cars in (1.4), say car number  $\ell$ , and make the following approximation

$$\int_{x_{\ell}}^{0} (\rho(x,0) - \rho_{N}) dx \approx \sum_{\ell}^{N-1} \rho_{n}(x_{n+1} - x_{n}) + x_{\ell} \rho_{N} = \epsilon(N - \ell) + x_{\ell} \rho_{N}.$$

| MIT OpenCourseWare |
|--------------------|
| http://ocw.mit.edu |

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

$$B = 16 \frac{\epsilon(N-\ell) + x_{\ell}\rho_N}{x_{\ell}^2}. \tag{5.8}$$

Remark 5.2 As nal point: quadCFSM puts cars only a nite distance behind the initial hump; i.e. the initial conditions in (5.1) are dened only for x1(0) <sup>x</sup> xN (0) = 0, where x1(0) <sup>&</sup>lt; is actual ly not too large in size<sup>11</sup> . Thus, if the computation were to be run for long enough, all the cars would eventual ly go through the disturbance and emerge in front of it where is identical ly N . That is, the solution of the ODE settles down to n N after a suciently long time. This fol lows from the factthat the car speed u is always bigger than the wave speed c.

<sup>11</sup>The size of x1(0) is not xed and is calculated to have enough cars in the problem to allow the saw-tooth shape enough time to develop fully before all the cars go through it.

---

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

---

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

---

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

---

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

---

| MIT OpenCourseWare |
|--------------------|
| http://ocw.mit.edu |

18.306 Advanced Partial Differential Equations with Applications Fall 2009

For information about citing these materials or our Terms of Use, visit:<http://ocw.mit.edu/terms>.

# Stability of Numerical Schemes for PDE's.

Rodolfo R. Rosales

MIT, Friday February 12, 1999.

The purpose of these notes is to give some examples illustrating how naive numerical approximations to PDE's may not work at all as expected. In addition, the following two important notions are introduced: (I) von Neumann stability analysis | helps identify when (and if ) numerical schemes behave properly. (II) Articial viscosity | a tool in stabilizing numerical schemes. These notes should be read in conjunction with the use of the MatLab scripts (in the Athena 18311-Toolkit at MIT) whose names end with the acronym GBNS (for Good-Bad-Numerical-Schemes).

#### Contents

| 1 | Naive<br>Scheme<br>for<br>the<br>Wave<br>Equation.                                      | 2  |
|---|-----------------------------------------------------------------------------------------|----|
| 2 | von<br>Neumann<br>stability<br>analysis<br>for<br>PDE's.                                | 7  |
| 3 | Numerical<br>Viscosity<br>and<br>Stabilized<br>Scheme.                                  | 12 |
| 4 | Reference.                                                                              | 12 |
|   | List<br>of<br>Figures<br>1.1<br>Naive scheme,<br>cosine<br>initial data with 40 points. | 3  |
|   | 1.2<br>Naive scheme,<br>cosine<br>initial data with 57 points.                          | 4  |
|   | 1.3<br>Naive scheme,<br>cosine<br>initial data with 80 points.                          | 5  |
|   | 1.4<br>Naive scheme,<br>periodic Gaussian initial data.<br>Small corner.                | 6  |
|   | 1.5<br>Naive scheme,<br>periodic Gaussian initial data.<br>Sharper<br>corner            | 7  |
|   | 3.1<br>Corrected<br>scheme,<br>cosine<br>initial data with 55 points                    | 13 |
|   | 3.2<br>Corrected<br>scheme,<br>cosine<br>initial data with 190 points.                  | 14 |

MIT, Department of Mathematics, room 2-337, Cambridge, MA 02139.

# 1 Naive Scheme for the Wave Equation.

We will illustrate the points we want to make with the wave equation (in one space dimension)

$$\frac{\partial^2 u}{\partial t^2} - \frac{\partial^2 u}{\partial x^2} = 0. {1.1}$$

Since this equation is second order in time, it needs two initial conditions. For example:

$$u(x,0) = u_0(x)$$
 and  $\frac{\partial u}{\partial t}(x,0) = v_0(x)$ . (1.2)

We will assume here that both  $u_0$  and  $v_0$  are periodic, with some **period** T > 0. Then the solution of (1.1) is periodic in x with the same period: u(x + T, t) = u(x, t).

Remark 1.1 We note that, in fact, we can write the solution of this problem explicitly

$$u = \frac{1}{2} \left( u_0(x-t) + u_0(x+t) + \int_{x-t}^{x+t} v_0(s) ds \right).$$

However, this is not the point here (see below).

Operate now as if (1.1) were complicated enough that we needed to solve the equation numerically. For this purpose introduce a **numerical grid**  $\{x_n, t_j\}$  — where n and j are integers, as follows

$$x_n = x_0 + n\Delta x$$
 and  $t_i = j\Delta t$ . (1.3)

Here  $\Delta x$  and  $\Delta t$  are some "small" positive constants and  $x_0$  is arbitrary. Next replace the function u = u(x, t) of the continuum variables x and t by a **discrete double sequence**  $\{u_n^j\}$ , where

$$u_n^j = u(x_n, t_j). (1.4)$$

Finally, introduce the new variable  $v = \frac{\partial u}{\partial t}$  to re-write equation (1.1) as a first order in time system

$$\frac{\partial u}{\partial t} = v \quad \text{and} \quad \frac{\partial v}{\partial t} = \frac{\partial^2 u}{\partial x^2}.$$
 (1.5)

In view of (1.4) it is now clear that  $u_n^j$  (and the similarly defined  $v_n^j$ ) should satisfy

$$\frac{u_n^{j+1} - u_n^j}{\Delta t} = v_n^j + O(\Delta t) \quad \text{and} \quad \frac{v_n^{j+1} - v_n^j}{\Delta t} = \frac{u_{n+1}^j - 2u_n^j + u_{n-1}^j}{(\Delta x)^2} + O(\Delta t, (\Delta x)^2), \tag{1.6}$$

which can be checked by expanding  $u_n^{j+1}$ ,  $u_{n+1}^j$ , ... in Taylor series centered at  $(x_n, t_j)$  — using (1.4) — and substituting the expansions in (1.6). This suggests the following numerical scheme, allowing simple calculation of the solution at time  $t = t_{j+1}$  (once it is known at time  $t = t_j$ )

$$u_n^{j+1} = u_n^j + \Delta t \, v_n^j \quad \text{and} \quad v_n^{j+1} = v_n^j + \frac{\Delta t}{(\Delta x)^2} \left( u_{n+1}^j - 2u_n^j + u_{n-1}^j \right) ,$$
 (1.7)

where the errors should be of size  $O(\Delta t, (\Delta x)^2)$ , that is: small.

Upon implementation one quickly discovers that **this algorithm is disastrously bad**. The MatLab scripts: InitGBNS, lectureGBNS, demoGBNS, movieGBNS and the help file readmeGBNS in the Athena 18311-Toolkit all deal with this scheme and another one to be introduced later in these notes. In particular, lectureGBNS goes through and explains a series of calculations showing the details of how the scheme fails. We illustrate here the problem with a couple of examples.

**Example 1.1** Consider the following initial data (with period T=2) for equation (1.5):

$$u(x,0) = u_0(x) = \frac{1}{2} (1 + \cos(\pi x))$$
 and  $v(x,0) = v_0(x) \equiv 0$ . (1.8)

The exact solution: 
$$u = \frac{1}{4} (2 + \cos(\pi (x - t)) + \cos(\pi (x + t))) = \frac{1}{2} (1 + \cos(\pi x) \cos(\pi t))$$
 — see

remark 1.1 — is clearly also periodic in time of period 2 (a standing wave). For the numerical solution we take  $\Delta x = 2 \Delta t = 2/N$  (for some "large" N) and  $x_0 = -1$  in (1.3). Then we implement (1.7) for  $1 \le n \le N$  (the periodicity of the solution means that the indexes n + N and n are equivalent) and solve the equations over one time period:  $0 \le t \le 2$ .

Figure 1.1: Solution of (1.5) with initial data (1.8) using (1.7) with 40 points in the space grid. To avoid an over-dense graph not all the points in the numerical grid are plotted. However, enough points to show all the relevant details are kept.

Figure 1.1 shows the result of this calculation using N = 40. Note that the periodicity in time fails to hold. In fact, after one time period the numerical method appears to have **amplified** the initial

data by about 30%! However, maybe this is not so bad (or is it?); after all the value of N being used is not that large and the numerical solution looks otherwise guite reasonable.

Let us now check what happens as we increase the resolution (larger N). Any reasonable numerical scheme ought to give a better approximation when we do this. Figure 1.2 shows the result of increasing N to N=57 (a rather small increase). The new approximation is not only not better; it is a **disaster**. By time  $t\approx 2$ , O(1) grid scale (i.e. wavelength  $= 2\Delta x$ ) oscillations appear in the numerical solution, making it useless. As we will soon see, the scheme is amplifying the errors; the 30% amplification of the initial cosine wave seen when using N=40 was just a forewarning of what happens for larger N. As N is made even larger, the oscillations generated become huge (in fact,

Figure 1.2: Solution of (1.5) with initial data (1.8) using (1.7) with 57 points in the space grid. To avoid an over-dense graph not all the points in the numerical grid are plotted. However, enough points to show all the relevant details are kept.

their size increases exponentially with N, as we will soon show). This is illustrated by figure 1.3, which corresponds to N=80. Here (instead of a 3D graph) we plot the numerical solution at time t=2. Grid scale (wavelength =  $2\Delta x$ ) oscillations is all that can be seen in this graph — notice the (very large) vertical scale on this figure!

Final ly, we point out that if (instead of increasing N) we compute for longer times, the same eect of large amplitude grid scale oscil lations arising (which grow exponential ly in time) is observed.

Figure 1.3: Solution of (1.5) with initial data (1.8) using (1.7) with 80 points in the space grid. Notice the large amplitude grid scale oscillations generated by the scheme. There is nothing but numerical noise in this picture!

Example 1.2 In a second example we take the fol lowing Gaussian initial data for equation (1.5)

$$u(x,0) = u_0(x) = \exp(-a \ln(10) x^2)$$
 and  $v(x,0) = v_0(x) \equiv 0$ , (1.9)

for 1 x 1, where a > 0 is a constant. We extend this to periodic initial data (of period T = 2) by repeating the above proles over each interval (2n 1) x (2n + 1), with n integer. These initial values are not smooth | as were the ones in the prior example. There is a smal l corner in u0(x), whenever x is an odd integer (in particular for x = 1). This is because at these points there is a cut-o from a Gaussian centered at x 1 to one centered at x + 1. Notice that the size of the miss-match in the derivatives of u0 goes down very rapid ly as <sup>a</sup> increases.

For the numerical solution we take  $x_0 = -1$ ,  $\Delta x = 0.02$  and  $\Delta t = 0.01$  in (1.3) — this corresponds to N = 100 in the notation of example 1.1 — and use (1.7) to solve the equations for  $0 \le t \le 0.5$ . This is very similar to what we did in the prior example, except that here we vary the initial conditions (by changing the parameter a) instead of changing the resolution with variations in N.

In the first calculation, we take a relatively large a, namely a = 10. Figure 1.4 shows the result of this calculation, which appears quite reasonable.

Figure 1.4: Solution of (1.5) with initial data (1.9) using (1.7) with 100 points in the space grid and a=10. To avoid an over-dense graph not all the points in the numerical grid are plotted (enough points to show all the relevant details are kept).

In the second calculation, we take a smaller value a=6. This makes the corners more substantial (though still pretty weak). Figure 1.5 shows the result of this last calculation, which is now not reasonable at all. It is quite clear that, just as in the prior example, the small errors that are triggered by the corners are amplified by the scheme (so we observe grid scale oscillations near  $x=\pm 1$  towards the end of the run).

Finally, we point out that, if the calculations are run for times longer than  $0 \le t \le 0.5$ , even the one with a = 10 eventually shows grid scale oscillations. These grow exponentially in time and pretty soon dominate the whole solution (not just the neighborhood of  $x = \pm 1$ ) with huge amplitudes.

Figure 1.5: Solution of (1.5) with initial data (1.9) using (1.7) with 100 points in the space grid and a=6. To avoid an over-dense graph not all the points in the numerical grid are plotted (enough points to show all the relevant details are kept).

The next section gives a detailed explanation of why this is happening.

# 2 von Neumann stability analysis for PDE's.

In this section we introduce the von Neumann stability analysis technique, that can be used to analyze numerical schemes and predict when the behavior observed in the prior section will occur. There are two **basic** concepts useful in understanding numerical schemes. These are the notions of **consistency** and **stability**. For a numerical scheme to be useful it must be both consistent and stable. It is very important to realize that these two notions are **independent**.

Consistency simply means that, as  $\Delta x$  and  $\Delta t$  vanish, the solutions of the equation must satisfy the numerical scheme with errors that vanish. This is in fact what equation (1.6) tells us about the scheme in (1.7). Consistency guarantees that the scheme truly approximates the equation we intend to solve with it (and not something else).

**Stability** simply means that the scheme does not amplify errors. Obviously this is very important, since errors are impossible to avoid in any numerical calculation. In fact, even in the ideal case of infinite precision, we still have to deal with discretization errors — i.e. the O terms in (1.6). Clearly, if errors are amplified, pretty soon they will dominate any computation (making it useless).

As it turns out, for linear constant coefficient schemes such as (1.7), a complete stability analysis is possible, because the numerical algorithm equations can be solved exactly by separation of variables. This means then that any solution of the scheme can be written as a superposition of Fourier modes. These Fourier modes are solutions of the form

$$u_n^j = U G^j e^{ikn} \quad \text{and} \quad v_n^j = V G^j e^{ikn},$$
 (2.1)

where U, V, G and k are constants (with k real). Generally double sequences like this will be solutions provided G, U and V are restricted by some functional relations of the form  $G = G(k, \Delta x, \Delta t)$ ,  $U = U(k, \Delta x, \Delta t)$  and  $V = V(k, \Delta x, \Delta t)$  — below we carry through the calculations for the specific example of (1.7).

G is called the **Growth Factor**. It is clear that:

for stability 
$$||G|| \le 1$$
 is needed for all  $k$ . (2.2)

Else some modes will be amplified by a factor G in each time step, eventually dominating the solution. A scheme is called **stable** if the stability condition  $||G|| \le 1$  can be satisfied with (perhaps) a restriction on the time step of the form  $0 < \Delta t \le \tau(\Delta x)$ , where  $\tau$  is a **positive** function of its argument. Notice that restrictions of this latter form allow arbitrarily small time and space steps, which are needed to be able to compute the solution with any required degree of accuracy (how small is determined by how well consistency is satisfied, which determines the size of the errors for any given  $\Delta t$  and  $\Delta x$ ).

Remark 2.1 The parameter k is the wavenumber of the mode, related to the wavelength  $\lambda$  in  $space^1$  by  $\lambda = (2\pi\Delta x)/k$ . For the particular case of periodic problems (such as the ones considered in examples 1.1 and 1.2), the Fourier modes (2.1) must also satisfy the periodicity condition. That is, one must have  $\lambda = T/\ell$ , where  $\ell$  is an integer and T is the period in space. Since in this case one would normally take  $\Delta x = T/N$ , where N is a large natural number, the acceptable values for k end up restricted to the set

$$k = k_{\ell} = \frac{2\pi \Delta x}{T} \ell = \frac{2\pi}{N} \ell \quad and \quad \lambda = \lambda_{\ell} = \frac{T}{\ell}, \quad with \quad 0 \le \ell < N.$$
 (2.3)

Here the upper bound N on  $\ell$  follows from the fact that  $k_{\ell}$  and  $k_{\ell+N}$  give the same Fourier mode in (2.1); thus there is no reason to keep both.

We note that (due to the fact that the numerical scheme only samples the solution at a discrete set  $\{x_n\}$  of points in space) there is a certain trickiness in the interpretation of the wavelengths  $\lambda_{\ell}$  above. Clearly,  $\ell=0$  corresponds to a solution independent of x and  $\ell=1$  corresponds to the fundamental mode with wavelength T in x. As  $\ell$  continues to increase harmonics of this fundamental mode appear, with wavelengths T/2, T/3 ... However, this process cannot continue forever, since

<sup>&</sup>lt;sup>1</sup>Write the argument kn in the exponentials in (2.1) as  $kn = \frac{k}{\Delta x}(x_n - x_0)$ , using (1.3).

the numerical grid cannot resolve arbitrarily small wavelengths. In fact, the shortest wavelength that can be resolved corresponds to  $\ell=N/2$  with  $\lambda_\ell=2\,\Delta x$  (grid size oscillations, with period 2 in n: the solution alternates between two values on the grid). To see this recall that  $k_\ell$  and  $k_{\ell+N}$  give the same Fourier mode in (2.1). Thus the mode  $(N-\ell)$  has the same wavelength as the mode  $-\ell$ , i.e.  $T/\ell$ . This means that, after  $\ell=N/2$  the wavelengths start increasing, to reach back the fundamental mode at  $\ell=N-1$ . Each wavelength then actually appears twice in the range  $1<\ell< N$ .

We should not be too surprised by the fact that each wavelength appears twice in the range  $1 < \ell < N$ . Notice that the modes in (2.1) are complex valued (except when k is a multiple of  $2\pi$ ). Thus, to be real valued any solution should include both the modes and their complex conjugates. However, the mode conjugate to the one with  $k = k_{\ell}$  above in (2.3) is the mode with  $k = k_{-\ell}$ , which is precisely the same as the mode with  $k = k_{N-\ell}$ .

In any numerical calculation it is the modes with wavelengths of the order of the grid size  $\Delta x$  (i.e.  $\ell$  close to N/2) that are worrisome in terms of instabilities. These modes cannot be expected to represent accurately any true feature of the real solution one is trying to compute<sup>2</sup> and should not have any significant presence in the numerical solution. Thus, it is very important that they not be amplified by the scheme. In fact, generally it is desirable to have them damped, since they mostly represent numerical "noise" generated by all the approximations implicit in any numerical calculation.

On the other hand, the modes with wavelengths much bigger than  $\Delta x$  (that is,  $\ell \approx 0$  or  $\ell \approx N$  in (2.3)) should be treated "accurately" by the scheme. By this we mean that their time evolution (given by the factors  $G^j$  in (2.1)) should be as close as possible to the one provided by the PDE the scheme approximates. This is what consistency is all about.

Consider now the special case of the algorithm (1.7). To see under which conditions (2.1) is a solution, substitute this form into (1.7). Dividing by the common factor  $G^j e^{ikn}$  it follows that

$$GU = U + \Delta t V$$
 and  $GV = V + \frac{\Delta t}{(\Delta x)^2} (e^{ik} - 2 + e^{-ik}) U$ .

Clearly an eigenvalue equation  $\mathbf{A} \mathbf{Y} = G \mathbf{Y}$ , with eigenvalue G, eigenvector  $\mathbf{Y} = (U, V)^T$  and matrix of coefficients

$$\mathbf{A} = \begin{pmatrix} 1 & \Delta t \\ -4\frac{\Delta t}{(\Delta x)^2} \sin^2(\frac{k}{2}) & 1 \end{pmatrix}.$$

From the characteristic equation  $det(\mathbf{A} - G) = 0$ , then

$$G = 1 \pm 2 i \frac{\Delta t}{\Delta x} \sin(\frac{1}{2}k). \tag{2.4}$$

It is clear that, for (1.7) there is no stability, since (2.4) yields

$$||G||^2 = 1 + \left(2\frac{\Delta t}{\Delta x}\sin(\frac{1}{2}k)\right)^2,$$
 (2.5)

which is always bigger than one.

<sup>&</sup>lt;sup>2</sup>Recall (1.4), which makes sense in terms of approximating the solution only if  $\Delta x$  is much smaller than any distance over which the solution changes significantly.

Notice that the maximum amplification for the scheme (1.7) occurs — as follows from (2.5) — for  $k = \pi$ . This corresponds to  $\ell = N/2$  in (2.3), i.e.: grid size oscillations with  $\lambda = 2 \Delta x$ . In this case

$$||G|| = G_M = \sqrt{1 + 4\eta}, \qquad (2.6)$$

where  $\eta = (\Delta t/\Delta x)^2$ . For (1.7), the amplitude of the grid size oscillations grows like  $G_M^j$ . Thus we can write for the amplification factor  $A_2 = A_2(t)$  (for the period  $2\Delta x$  mode)

$$A_2 = \exp\left(t\frac{\ln(G_M)}{\Lambda t}\right),\tag{2.7}$$

where we have used  $j = t/\Delta t$ . In particular (in **examples 1.1 and 1.2** earlier) we took  $\Delta x = 2 \Delta t$  and  $\Delta t = 1/N$ , so that

$$A_2 = \exp(\frac{\ln 2}{2} N t) = 2^{\frac{Nt}{2}}.$$
 (2.8)

We will now use these results to explain the behavior observed earlier in figures 1.1 through 1.5.

Remark 2.2 Consider first example 1.1, with the initial data for scheme (1.7) given by

$$u_n^0 = \frac{1}{2} \left( 1 - \cos(\frac{2n\pi}{N}) \right)$$
 and  $v_n^0 = 0$ .

These data correspond to a superposition of just three modes in (2.1), with  $k = k_0$ ,  $k = k_1$  and  $k = k_{-1} \sim k_{N-1}$  in (2.3). Thus, the **exact solution for the scheme equations** is rather simple and has the form

$$u_n^j = \frac{1}{2} \left( 1 - \frac{g^j + \bar{g}^j}{2} \cos(\frac{2n\pi}{N}) \right) \quad and \quad v_n^j = \frac{g^j - \bar{g}^j}{2i} \, \hat{v} \cos(\frac{2n\pi}{N}) \,, \quad for \quad g = 1 + i \sin(\frac{\pi}{N}) \,, \quad (2.9)$$

where  $\hat{v}$  is a constant and  $\bar{g}$  denotes the complex conjugate of g. Of course, g and  $\bar{g}$  are the values G in (2.4) takes for  $k = k_1 = 2\pi/N$ .

Notice that the exact solution (2.9) does not exhibit any catastrophic growth of grid size oscillations, as was observed in example 1.1. However, the results displayed in figures 1.1 through 1.3 do not correspond to the exact solution above but to actual computations using the scheme in (1.7) — which were done using double precision floating point arithmetic (MatLab's default). The round off errors introduced by the finite precision of the calculations introduces (very small) perturbations into the exact solution above, which the scheme then evolves in time just as if they were part of the solution.

To understand what the scheme does with the perturbations introduced by the finite precision, decompose them into a sum over the modes in (2.1). This sum will generally include all the modes, in particular the highly amplified ones with grid size wavelengths. Consider then what would happen with the solution of the scheme if we add to the initial data above<sup>3</sup> a small amount of the component corresponding to the maximum amplification rate above in (2.6). Let the amplitude of this component be  $\epsilon$ , where  $\epsilon$  has (roughly) the size of the expected errors. Actually,  $\epsilon$  should be a little smaller than the round off errors that occur, since not all the errors get projected into the fastest growing modes. Thus take  $\epsilon = O(10^{-17})$  as a good ballpark figure for the calculations in section 1 and use (2.8) above to explain the behavior observed in figures 1.1 through 1.3, as follows:

<sup>&</sup>lt;sup>3</sup>Which has only components corresponding to  $\ell = 0$ ,  $\ell = 1$  and  $\ell = N - 1$  in (2.3).

1. First, for N=40, (2.8) gives  $A_2\approx 1.1\times 10^{12}$  for the final time t=2. This is not enough to compensate for the smallness of  $\epsilon$  and the numerical solution is well described by (2.9).

Notice that (2.9) is not periodic in time; since the wave amplitude in u behaves like  $Re(g^j)$ , which grows as j grows. In fact, 2N = 80 steps are needed to reach the final time t = 2 and it is easy to check that

$$Re(g^{80}) = Re\left\{ \left( 1 + i \sin(\frac{\pi}{40}) \right)^{80} \right\} \approx 1.28$$
.

This agrees quite well with the  $\approx 30\%$  growth in the wave amplitude observed in figure 1.1.

- 2. Second, for N = 57, (2.8) gives  $A_2 \approx 1.4 \times 10^{17}$  for the final time t = 2. This is about the same as  $\epsilon^{-1}$  and agrees with the fact that grid oscillations of O(1) amplitude are observed in figure 1.2.
- 3. Third, for N=80, (2.8) gives  $A_2 \approx 1.2 \times 10^{24}$  for the final time t=2. This is about  $10^7$  times bigger than  $\epsilon^{-1}$ , which (again) agrees pretty well with the observed amplitude of the grid size oscillations in figure 1.3.
- 4. Finally, it is not just the mode with  $\ell = N/2$  in (2.3) that gets a large amplification factor by the scheme. All the ones with  $\ell \approx N/2$  do and should thus be present in the solution. It is well known that when sinusoidals with close wavenumbers are added, "beats" with wavenumbers equal to the difference in wavenumbers occur. Thus, in this case we should observe "beats" with wavenumbers low multiples of  $k_1 = 2\pi/N$  which, indeed, are quite obvious in figure 1.3.

Remark 2.3 Now consider example 1.2, where N = 100 and  $0 \le t \le 0.5$ . Then, for the time t = 0.5, equation (2.8) gives  $A_2 \approx 3.4 \times 10^7$ .

In this case the initial data has components in all the modes  $0 \le \ell < N$  in (2.3). In fact, because of the corners at  $x = \pm 1$ , the amplitude present in the higher modes is relatively large. The strength of these corners can be measured by the jump in the derivative of the initial data there:  $J(a) = 4 a \ln(10) 10^{-a}$ . For moderate<sup>4</sup> size a, J(a) pretty much determines how much amplitude there is in the higher modes. Now  $J(10) \approx 9.2 \times 10^{-9}$  and  $J(6) \approx 5.5 \times 10^{-5}$ . Thus, from the value of  $A_2$  above, it should be clear why in figure 1.4 (corresponding to a = 10) the solution exhibits no detectable oscillations, while in figure 1.5 (corresponding to a = 6) they show up.

Notice that in this case it is also true that it is not just the mode with  $\ell = N/2$  in (2.3) that gets a large amplification factor by the scheme. All the neighboring ones are also present. However, now their amplitudes and phases are all correlated because they (mostly) are generated by the corner in the initial data. Thus they interfere with each other in ways subtler than the mere beating observed in the prior example; i.e.: the pattern of grid size oscillations has a clear maximum near the positions of the corners in figure 1.5.

In the next section we will discuss a simple strategy to stabilize numerical schemes, to get rid of numerical oscillations and other undesirable effects. The strategy is based on the introduction of artificial (numerical) dissipation to (selectively) damp the higher modes, without significantly affecting the lower modes (where a consistent scheme should behave properly — see remark 2.4).

<sup>&</sup>lt;sup>4</sup>When a is large, the corner is very weak and the dominant contribution to the mode amplitudes comes from the smooth part of the initial data (which yields very little amplitude in the high modes).

**Remark 2.4** Finally, going back now to the last paragraph in remark 2.1, consider the behavior of G in (2.4) for k small. Namely

$$G = 1 \pm i \frac{\Delta t}{\Delta x} k + O\left(\frac{\Delta t}{\Delta x} k^3\right) . \tag{2.10}$$

This should be compared with the behavior of the exact solution for the wave equation (1.1) — see remark 1.1 — which evolves Fourier modes according to the rule

$$u \propto \exp\left\{i\frac{k}{\Delta x}(x_n \pm t_j)\right\} \propto \exp\left\{i\left(kn \pm \frac{\Delta t}{\Delta x}kj\right)\right\}.$$

Thus the exact evolution corresponds to a factor G given by

$$G_{exact} = exp\left(\pm i\frac{\Delta t}{\Delta x}k\right) = 1 \pm i\frac{\Delta t}{\Delta x}k + O\left(\left(\frac{\Delta t}{\Delta x}k\right)^{2}\right). \tag{2.11}$$

This should be compared with (2.10) above. It is clear then that (for k small) G is correct up to small terms in k, which is an alternative way of verifying that the scheme (1.7) is consistent.

### 3 Numerical Viscosity and Stabilized Scheme.

Notation used for Good Scheme in MatLab:  $\eta = (\Delta t/\Delta x)^2$  and  $\nu = \Delta t/\Delta x^2$ .

Next the figures that go with the good scheme.

#### 4 Reference.

For more information regarding stability of numerical schemes (and many other useful numerical topics) a good all-around practical reference is *Numerical Recipes, The Art of Scientific Computing* by W. H. Press, S. A. Teukolsky, W. T. Vetterling and B. P. Flannery. Cambridge U. Press, New York, 1992.

Figure 3.1: Solution of (1.5) with initial data (1.8) using the corrected scheme (3.1) with 55 points in the space grid. To avoid an over-dense graph not all the points in the numerical grid are plotted. However, enough points to show all the relevant details are kept.

Figure 3.2: Solution of (1.5) with initial data (1.8) using the corrected scheme (3.1) with 190 points in the space grid. To avoid an over-dense graph not all the points in the numerical grid are plotted. However, enough points to show all the relevant details are kept.
