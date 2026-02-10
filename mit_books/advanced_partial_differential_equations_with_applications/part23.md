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