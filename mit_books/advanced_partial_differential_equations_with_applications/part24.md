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