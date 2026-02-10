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