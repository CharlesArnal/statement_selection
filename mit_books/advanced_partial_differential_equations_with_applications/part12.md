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