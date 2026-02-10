## Lecture 1

General overview of what a PDE is and why they are important. Discussed examples of some typical and important PDEs (see handout, page 1). With non-constant coefficients (the most common case in real-world physics and engineering), even the simplest PDEs are rarely solvable by hand; even with constant coefficients, only a relative handful of cases are solvable, usually high-symmetry cases (spheres, cylinders, etc.) solvable. Therefore, although we will solve a few simple cases by hand in 18.303, the emphasis will instead be on two things: learning to *think* about PDEs by recognizing how their *structure* relates to concepts from finite-dimensional linear algebra (matrices), and learning to *approximate* PDEs by actual matrices in order to solve them on computers.

Went through 2nd page of handout, comparing a number of concepts in finite-dimensional linear algebra (ala 18.06) with linear PDEs (18.303). The things in the "18.06" column of the handout should already be familiar to you (although you may need to review a bit if it's been a while since you took 18.06)—this is the kind of thing I care about from 18.06 for this course, not how good you are at Gaussian elimination or solving 2×2 eigenproblems by hand. The things in the "18.303" column are perhaps unfamiliar to you, and some of the relationships may not be clear at all: what is the dot product of two functions, or the transpose of a derivative, or the inverse of a derivative operator? Unraveling and elucidating these relationships will occupy a large part of this course.

Covered the concept of **nondimensionalization**: rescaling the units so that dimensionful constants and other odd numbers disappear, making as many things "1" as possible. Gave an example of a heat equation  $\kappa \nabla^2 T = \partial T/\partial t$  in an L×L box in SI units, where we have a thermal conductivity  $\kappa$  in m<sup>2</sup>/s. By rescaling the spatial coordinates to x/L and y/L, and rescaling the time coordinate to  $\kappa t/L^2$ , we obtained a simplified equation of the form  $\nabla^2 T = \partial T/\partial t$  in a 1×1 box. Not only does this simplify the equations, but it can also improve our understanding: by rescaling with *characteristic times and distances*, we are left with distance and time units where 1 is the characteristic time and distance, and so in these units it is immediately obvious what we should consider "big" and "small". For example, in the rescaled time units, 0.01 is a small time in which probably not much happens, while 100 is a big time in which the solution has probably changed a lot. In the original SI units we would have had to explicitly compare to the characteristic time  $L^2/\kappa$ .

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 2

Started with a very simple vector space V of functions: functions u(x) on [0,L] with u(0)=u(L)=0 (Dirichlet boundary conditions), and with one of the simplest operators: the 1d Laplacian  $\hat{A}=d^2/dx^2$ . Explained how this describes some simple problems like a stretched string, 1d electrostatic problems, and heat flow between two reservoirs.

Inspired by 18.06, we begin by asking what the null space of  $\hat{A}$  is, and we quickly see that it is  $\{0\}$ . Thus, any solution to  $\hat{A}u=f$  must be unique. We then ask what the eigenfunctions are, and quickly see that they are  $\sin(n\pi x/L)$  with eigenvalues  $-(n\pi/L)^2$ . If we can expand functions in this basis, then we can treat  $\hat{A}$  as a number, just like in 18.06, and solve lots of problems easily. Such an expansion is precisely a Fourier sine series (see handout).

In terms of sine series for f(x), solve  $\hat{A}u=f$  (Poisson's equation) and  $\hat{A}u=\partial u/\partial t$  with u(x,0)=f(x) (heat equation). In the latter case, we immediately see that the solutions are decaying, and that the high-frequency terms decay faster...eventually, no matter how complicated the initial condition, it will eventually be dominated by the smallest-n nonzero term in the series (usually n=1). Physically, diffusion processes like this smooth out oscillations, and nonuniformities eventually decay away. Sketched what the solution looks like in a typical case.

As a preview of things to come later, by a simple change to the time-dependence found a solution to the wave equation  $\hat{A}u=\partial^2 u/\partial t^2$  from the same sine series, which gives "wavelike" behavior. (This is an instance of what we will later call a "separation of variables" technique.)

**Further reading:** Section 4.1 of the Strang book (Fourier series and solutions to the heat equation).

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 3

Now, we will go back to the happy land of finite-ness for a while, by learning to approximate a PDE by a matrix. This will not only give us a way to compute things we cannot solve by hand, but it will also give us a different perspective on certain properties of the solutions that may make certain abstract concepts of the PDE clearer. We begin with one of the simplest numerical methods: we replace the continuous space by a grid, the function by the values on a grid, and derivatives by differences on the grid. This is called a **finite-difference method**.

Went over the basic concepts and accuracy of approximating derivatives by differences; see handout.

Armed with center differences (see handout), went about approximating the 1d Laplacian operator  $d^2/dx^2$  by a matrix, resulting in a famous tridiagonal matrix known as a *discrete Laplacian*. The properties of this matrix will mirror many properties of the underlying PDE, but in a more familiar context. We already see by inspection that it is real-symmetric, and hence we must have real eigenvalues, diagonalizability, and orthogonal eigenvectors—much as we observed for the  $d^2/dx^2$  operator—and in the next lecture we will show that the eigenvalues are negative, i.e. that the matrix is negative-definite.

The negative eigenvalues mean that the discrete Laplacian is negative definite, and also suggest that it can be written in the form -D<sup>T</sup>D for some D. Reviewed the proof that this means the matrix is negative definite, which also relies on D being full column rank.

**Further reading:** notes on finite-difference approximations from 18.330. See the matrix K section 1.1 ("Four special matrices") of the Strang book, and in general chapter 1 of that book.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 4

Showed that our A indeed has this  $-D^TD$  form and hence is negative-definite: we derived the discrete Laplacian by turning two derivatives into differences, one by one, and now by writing the first step as a matrix we get D, while writing the second step as a matrix shows that it is  $-D^T$ . To get a negative *definite* matrix (as opposed to just negative semidefinite), we additionally require that D be full column rank; showed that this is easy to see from  $D^T$  since it is uppertriangular.

To do a similar analysis of the actual Laplacian, we first have to have a dot product, or **inner product**. Defined an abstract  $\langle u, v \rangle$  notation (a map from *functions* u and v to *scalars*  $\langle u, v \rangle$ ) for inner products, as well as three key properties. First,  $\langle u, v \rangle = \text{complex conjugate of } \langle v, u \rangle$ . Second,  $|u|^2 = \langle u, u \rangle$  must be nonnegative, and zero only if u = 0. Third, it must be linear:  $\langle u, \alpha v + \beta w \rangle = \alpha \langle u, v \rangle + \beta \langle u, w \rangle$ . (Note: some textbooks, especially in functional analysis, put the conjugation on the second argument instead of the first.) For functions, the most common inner product (though *not the only choice* and not always the *best* choice, as we will see next time) is a simple integral  $\int uv$  (conjugating u for complex functions); we will look at this more next time.

Reviewed inner products of functions. A vector space with an inner product (plus a technical criterion called "completeness" that is almost always satisfied in practice) is called a **Hilbert space**. Note that we include only functions with finite norm  $\langle u,u \rangle$  in the Hilbert space (i.e. we consider only square-integrable functions), which throws out a lot of divergent functions and means that everything has a convergent Fourier series. (Another omitted technicality: we have to ignore finite discrepancies at isolated points, or otherwise you can have  $\langle u,u \rangle = 0$  for u(x) nonzero; there is a rigorous way to do this, which we will come back to later.)

Defined the **adjoint**  $\hat{A}^*$  of a linear operator: whatever we have to do to move it from one side of the inner product to the other, i.e. whatever  $\hat{A}^*$  satisfies  $\langle u, \hat{A}v \rangle = \langle \hat{A}^*u, v \rangle$  for all u,v. (Omitted techicality: we must further restrict ourselves to functions that are sufficiently differentiable that  $\langle u, \hat{A}u \rangle$  is finite, which is called a **Sobolev space** for this  $\hat{A}$ , a subset of the Hilbert space.) For matrices and ordinary vector dot products, this is equivalent to the "swap rows and columns" definition. For differential operators, it corresponds to integration by parts, and depends on the boundary conditions as well as on the operator and on the inner product.

Showed that with u(0)=u(L)=0 boundary conditions and this inner product,  $(d^2/dx^2)^T$  is real-symmetric (also called "Hermitian" or "self-adjoint"). [There is an omitted technicality here: technically, we have only showed that the operator is symmetric. To show that it is Hermitian, we must also show that the adjoint has the same domain in the Hilbert space. Mostly we can avoid this technical distinction in real applications; it doesn't arise explicitly in the proofs here.]

Not only that, but next time we will show that  $d^2/dx^2$  is negative-definite on this space, since  $\langle u, u'' \rangle = -\int |u'|^2$ , and u'=0 only if u=constant=0 with these boundary conditions.

Showed that the proof of real eigenvalues from 18.06 carries over without modification for Hermitian operators; similarly for the proof of orthogonal eigenvectors, hence the orthogonality of the Fourier sine series. Similarly for the proof of negative eigenvalues.

So, many of the key properties of  $d^2/dx^2$  follow "by inspection" once you learn how to transpose operators (integrate by parts). And this immediately tells us key properties of the solutions, if we assume the spectral theorem: Poisson's equation has a unique solution, the diffusion equation has decaying solutions, and the wave equation has oscillating solutions.

**Further reading:** Notes on function spaces, Hermitian operators, and Fourier series that I once wrote for 18.06 (slightly different notation). Textbook, section 3.1: transpose of a derivative. The general topic of linear algebra for functions leads to a subject called *functional analysis*; a rigorous introduction to functional analysis can be found in, for example, the book *Basic Classes of Linear Operators* by Gohberg et al. There are some technicalities that I omit: a differential operator is only called "self-adjoint" if it is equal to its adjoint and is "densely defined", and showing that an operator equals its adjoint furthermore requires an extra step of showing that  $\hat{A}$  and  $\hat{A}^*$  act on the same domains.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 5

Finished negative-definiteness proof from previous lecture.

Discussed diagonalizability of infinite-dimensional Hermitian operators. Unlike the proof of real eigenvalues, etcetera, we cannot simply repeat the proof from the matrix case (where one can proceed by induction on the dimension). In practice, however, real-symmetric operators arising from physical systems are almost always diagonalizable; the precise conditions for this lead to the "spectral theorem" of functional analysis.) (One hand-wavy argument: all physical PDEs can apparently be simulated by a sufficiently powerful computer to any desired accuracy, in principle. Since the discrete approximation is diagonalizable, and converges to the continuous solution, it would be surprising if the eigenfunctions of the continuous problem "missed" some solution. In fact, all the counter-examples of self-adjoint operators that lack a spectral theorem seem to involve unphysical solutions that oscillate infinitely fast as they approach some point, and hence cannot be captured by any discrete approximation no matter how fine.) In 18.303, we will typically just assume that that all functions of interest lie in the span of the eigenfunctions, and focus on the consequences of this assumption.

Showed how this immediately tells us key properties of the solutions, if we assume the spectral theorem: Poisson's equation has a unique solution, the diffusion equation has decaying solutions (with larger eigenvalues = faster oscillations = decaying faster, making the solution smoother over time), and the wave equation has oscillating solutions.

Not only do we now understand  $d^2/dx^2$  at a much deeper level, but you can obtain the same insights for many operators that *cannot* be solved analytically. For example, showed that the operator d/dx [c(x) d/dx], which is the 1d Laplacian operator for a non-uniform "medium", is also real-symmetric positive definite if c(x)>0, given the same u(0)=u(L)=0 boundary conditions.

As another example, considered the operator  $c(x)d^2/dx^2$  for real c(x)>0. This is *not* self-adjoint under the usual inner product, but *is* self-adjoint if we use the *modified* inner product  $\langle u,v\rangle=\int uv/c$  with a "weight" 1/c(x). (This modified inner product satisfies all of our required inner-product properties for positive c(x).) Therefore,  $c(x)d^2/dx^2$  indeed has real, negative eigenvalues, and has eigenfunctions that are orthogonal under this new inner product. Later on, we will see more examples of how sometimes you have to change the inner product in order to understand the self-adjointness of  $\hat{A}$ .

Fortunately, it's usually pretty obvious how to change the inner product, typically some simple weighting factor that falls out of the definition of  $\hat{A}$ . (In fact, for matrices, it turns out that *every* diagonalizable matrix with real eigenvalues is Hermitian under some modified inner product. I didn't prove this, however.)

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 6

Previously, we started with the continuous PDE equations and derived a discrete/matrix version as an approximation. Now we will do the reverse: we will *start* with a truly discrete (finite-dimensional) system, and then derive the continuum PDE model as a limit or approximation. This is one of the common ways by which PDE models are derived in the first place, will give yet another perspective on similar mathematics, and will also shed some light on the origin of the variable c(x) coefficients from the last lecture.

In particular, we look at the 8.01 (or 8.03) system of a set of N masses m sliding without friction and connected by springs of constant k, anchored to walls on both sides.

If the displacements of each mass are given by a vector  $\mathbf{u}$ , we show that  $d^2\mathbf{u}/dt^2 = A\mathbf{u}$  where  $A = (k/m) (-D^TD^T) \Delta x^2$ , with D being *exactly* our "first derivative" matrix from previous lectures. Thus, up to a scale factor, our discrete Laplacian A from previous lectures is not only an approximation for  $d^2/dx^2$ , but it is also *exactly* the matrix describing this coupled-spring system!

By inspection, A is real-symmetric negative-definite as before, and hence we have N real eigenvalues  $\lambda_n < 0$  and orthonormal eigenvectors  $\mathbf{u}_n$ . By expanding the solution  $\mathbf{u}(t)$  in terms of these eigenvectors, we see that we obtain oscillating solutions: a set of (orthogonal) *normal modes* with real "eigenfrequencies"  $\omega_n = \sqrt{-\lambda_n}$ . The negative-definiteness is critical to have oscillation, as otherwise we would get complex  $\omega_n$  and exponential growth! Showed a few examples for N=1,2,3 to get an intuition for these modes.

Took the N $\to\infty$  limit keeping the total length L fixed, which corresponds to  $\Delta x\to 0$  (breaking the system into smaller and smaller pieces). Correspondingly, we decrease the masses proportional to  $\Delta x$ , so that m= $\rho\Delta x$  where  $\rho$  is a density. On the other hand, reminded ourselves that cutting springs in half *increases* the spring constant, so we should let k= $c/\Delta x$  for some constant c. With these definitions, our matrix A is precisely ( $c/\rho$ ) (-D<sup>T</sup>D), where -D<sup>T</sup>D is our approximate (center-difference) d<sup>2</sup>/dx<sup>2</sup> from before, and hence this limit gives precisely the scalar wave equation  $\partial^2 u/\partial t^2 = (c/\rho) \partial^2 u/\partial x^2$ , with the boundary conditions u(0,t)=u(L,t)=0 (fixed ends). As before, this operator is self-adjoint negative definite and so we get real  $\lambda_n$ <0 etcetera. Exactly as in the finite-dimensional case above, we therefore get oscillating "normal mode" solutions, just with an infinite series of eigenfunctions instead of a finite sum.

Finally, considered the "inhomogeneous medium" case where we allow all the masses and spring constants to be different. Showed that this corresponds to inserting some diagonal matrices into the above expressions, and in the continuum limit gives  $\partial^2 u/\partial t^2 = (1/\rho) \partial/\partial x$  (c  $\partial u/\partial x$ )=Âu where  $\rho(x)$  and c(x) are positive functions. As in the previous lecture, we can see that this is indeed self-adjoint negative-definite, and hence we get *oscillating normal-mode solutions*, if we define the modified inner product  $\langle u,v \rangle = \int \rho uv$ . And we can see this even though we probably cannot solve this PDE by hand except for very special cases of  $\rho$  and c!

**Further reading:** Same as previous lecture. Sections 2.1 and 2.2 in the Strang book cover very similar material on discrete vibration problems.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 7

Now that we have seen several specific examples, we are equipped to consider more general problems, ones that are even harder to solve analytically.

Started in 1d with the "Sturm-Liouville operator"  $w(x)^{-1}$  [ - d/dx (c(x) d/dx) + p(x)], with Dirichlet (0) boundaryies on  $\Omega$ =[0,L]. Showed that it is self-adjoint under the weighted inner product  $\langle u,v\rangle$ = $\int wuv$ , assuming w is real and positive and c and p are real. If we further assume that c $\geq$ 0 and p $\geq$ 0, the operator is positive-definite, a so-called **elliptic operator** (although the technical definition of elliptic operators is slightly more restrictive in order to exclude pathological cases of the coefficient functions etc.).

Generalized Sturm-Liouville operators to multiple dimensions:  $\hat{A}=w(\mathbf{x})^{-1}$  [  $-\nabla \cdot (\mathbf{c}(\mathbf{x})\nabla) + \mathbf{p}(\mathbf{x})$  ], with Dirichlet (0) boundaryies on some finite domain  $\Omega$ , and again we will show that this is self-adjoint for real coefficients and w>0, and positive-definite (elliptic) for c≥0 and p>0. The key to the proof is the divergence theorem, which generalizes "integration by parts" to multiple dimensions.

We can now analyze three important cases, and give them their conventional historical names:

- Âu=f where is self-adjoint and positive (or negative) definite. This is sometimes called an *elliptic* problem.
- Âu=∂u/∂t where is self-adjoint and negative definite (hence exponentially decaying solutions), or possibly semidefinite. This is sometimes called a *parabolic* problem.
- $\hat{A}u = \partial u^2/\partial t^2$  where  $\hat{A}$  is self-adjoint and negative definite (hence oscillating solutions), or possibly semidefinite. This is sometimes called a *hyperbolic* problem.

(I won't spend any times on the analogies between these equations and those of parabolas, ellipses, and hyperbolas. That only works well in simple cases with scalar functions u, and I find it much clearer and more general just to talk about the definiteness and self-adjointness of Â.)

**Further reading:** Much of the theory of these kinds of 1d operators is traditionally called "Sturm-Liouville theory", and can be found under that name in many books (e.g. *Methods of Applied Mathematics* by Hildebrand, *Methods of Mathematical Physics* by Courant & Hilbert, and many similar titles). Even Wikipedia has a decent article on the topic under that name.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 8

**Music and wave equations:** Spent a little time relating the 18.303 theory of the vibrating string to what you hear when you listen to a stringed instrument; scales, harmonics, transposition, timbre and the Fourier series, etcetera. (See notes.) Performed a little demo on my Yamaha guitalele. To obtain a chromatic scale, each fret on the guitalele (or guitar) shortens the strings by a factor of  $2^{1/12}$  (and this is why the frets get closer together as you go up the neck: they are equally spaced on a log scale).

**New topic: Separation of variables:** (See notes.) This is a technique to *reduce the dimensionality* of a PDE by representing the solution as a product of lower-dimensional functions. It *only works in a handful of cases*, usually as a consequence of *symmetry*, but those cases are common enough that it is important to know them. It also gives us our only analytically solvable PDE examples in more than 1d; otherwise we will have to use the computer.

**Separation of Time**: The most important case is the one we've already done, under another name. We solved  $Au=\partial u/\partial t$  by looking for eigenfunctions  $Au=\lambda u$ , and then multiplying by  $exp(\lambda t)$  to get the time dependence. Similarly for  $Au=\partial u^2/\partial t^2$  except with sines and cosines. In both cases, we wrote the solution as a sum of products of purely spatial functions (the eigenfunctions) and purely temporal functions like  $exp(\lambda t)$ . The key point here is that we aren't assuming that the *solution* is separable, only that it can be decomposed into *linear combination* of separable functions.

**Separation of Space**: Here, we try to solve problems in more than one *spatial* dimension by factoring out 1d problems in one or more dimension. In particular, we will try to find *eigenfunctions* in separable form, and then write any solution as a linear combination of eigenfunctions as usual. In practice, this mainly works only in a few important cases, especially when one direction is *translationally invariant* or when the problem is *rotationally invariant*. In the former case, translational invariance in one direction (say z) allows us to write the eigenfunctions in separable form as X(x,y)Z(z), where it turns out that  $Z(z)=\exp(ikz)$  for some k (and X and  $\lambda$  will then depend on k). In the latter case, we get separable eigenfunctions  $R(r)\exp(im\theta)$  where m is an integer, in 2d, and  $R(r)Y_{l,m}(\theta,\phi)$  in 3d, where  $Y_{l,m}(\theta,\phi)$  is a spherical harmonic. Also, we can *sometimes* get separable solutions for finite "box-like" domains, i.e. translationally invariant problems that have been truncated to a finite length in z.

To start with, we looked at  $\nabla^2 u = \lambda u$  in a 2d  $L_x \times L_y$  box with Dirichlet boundary conditions, and looked for separable solutions of the form X(x)Y(y). Plugging this in and dividing by XY (the standard techniques), we get 1d eigenproblems for X and Y, and these eigenproblems ( $X'' = X \times \text{constant}$  and  $Y'' = Y \times \text{constant}$ ) just give us our familiar sine and cosine solutions. Adding in the boundary condition, we get  $\sin(n_x\pi x/L_x)\sin(n_y\pi x/L_y)$  eigenfunctions with eigenvalues  $\lambda = (n_x\pi/L_x)^2 - (n_y\pi/L_y)^2$ . As expected, these are real and negative, and the eigenfunctions are orthogonal...giving us a 2d Fourier sine series. For example, this gives us the "normal modes" of a square drum surface.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 9

Finished consideration of separability of  $\nabla^2 u = \lambda u$  in a 2d box, from notes: discussed orthogonality of these eigenfunctions. Also showed that separability breaks down, in general, for non-constant coefficients in the box.

More separation of variables: cylindrical case of a cylinder of radius R with Dirichlet boundary conditions. Show that the Laplace eigenequation here is indeed separable into a function of  $\theta$  multiplied by a function of r, satisfying separate 1d ODEs. Show that the  $\theta$  dependence is  $\sin(m\theta)$  or  $\cos(m\theta)$  (or any linear combination), where m is an integer (in order to be periodic in  $\theta$ ). The r dependence satisfies a more complicated 2nd-order ODE that we can't solve by hand (even if you have taken 18.03).

At this point, it's more a historical question than a mathematical one: has someone solved this equation before, and if so is there a standard name (and normalization, etc) for the solutions? In fact, that is the case here (not surprisingly, since the Laplacian is so important): our r equation is an instance of **Bessel's equation**, and the solutions are called **Bessel functions**. The canonical two Bessel functions are  $J_m$  and  $Y_m$ : there is a standard convention defining the normalization, etcetera, of these, but the important thing for our purposes is that J is finite at r=0 and Y blows up at the origin. In Julia, SciPy, Matlab, and similar packages, these are supplied as built-in functions (e.g. besselj and bessely), and we use Julia to plot a few of them to get a feel for what they look like: basically, sinusoidal functions that are slowly decaying in r.

To get eigenfunctions, we have to impose boundary conditions. Finite-ness of the solution at r=0 means that we can only have  $J_m(kr)$  solutions, and vanishing at r=R means that kR must be a root of  $J_m$ . We have to find these roots numerically, but this is easy to do, and we obtain a discrete set of eigenfunctions and eigenvalues.

From the general orthogonality of the Laplacian eigenfunctions, we can derive an orthogonality relation for Bessel functions, and by evaluating the integral numerically we can see that this orthogonality is indeed the case.

By looking at Bessel's equation asymptotically, we find that it reduces to sines and cosines for large r; more careful considerations show that it must actually reduce to sines and cosines multiplied by  $1/\sqrt{r}$ , and we can verify this from the plot. Conversely, for small r we show that it goes as either  $r^m$  ( $J_m$ ) or  $1/r^m$  ( $Y_m$ , except for m=1 where  $Y_0$  is proportional to log r); this is why we have one finite solution and one divergent one at r=0. (There are many, many more properties of Bessel functions that one can derive analytically, but that is not our major concern here.)

**Further reading:** The Wikipedia page on Bessel functions has many plots, definitions, and properties, as well as links to standard reference works.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 10

(Finished asymptotics of Bessel functions from previous lecture notes.)

Discussed **boundary conditions** more generally than we have done in the past. Up to now, we have mostly considered u=0 (Dirichlet) or  $\mathbf{n} \cdot \nabla u=0$  (Neumann) on the boundary, and mostly the former

More generally, we can consider "general Dirichlet" and "general Neumann" boundary conditions, where either the values u(x) or the normal derivatives  $\mathbf{n} \cdot \nabla u$  are some given function  $g(\mathbf{x},t)$  on the boundary. (For example, general Dirichlet boundary conditions arise for a drum head where the edges are not held flat, and you may even be warping the edges as a function of time.) If  $g\neq 0$ , these functions u do *not* form a vector space because they do not include u=0, so we must transform the problem somehow to get back to linear algebra.

For general Dirichlet, one simple approach is to write u=v+g, where our new unknown v has zero-Dirichlet boundaries (similar to pset 1). Showed how this transforms e.g. a wave equation  $\hat{A}u=\partial^2 u/\partial t^2$ -f(x,t) into wave equation in v but with an additional "force" term modifying f:  $\hat{A}v=\partial^2 v/\partial t^2$ -[f+ $\hat{A}g-\partial^2 g/\partial t^2$ ]. For example, considered the steady-state 1d version of this problem  $d^2u/dx^2=0$  (Laplace's equation) with u(0)=a, u(L)=b boundaries and showed that the solution is a straight line, which is physically obvious for a string stretched from (0,a) to (L,b).

Intuitively, this makes a certain amount of sense: warping the boundary corresponds to an external force. But intuitively, the "physical" boundary force is only applied at the boundary, not everywhere in  $\Omega$  as it is for a general g(x) above. It turns out that we can do this, too. It is easier to see this in the discrete case, for the same 1d problem as above. In this case, showed that we obtained the same Dirichlet A matrix as we do for 0 boundary conditions, while the (a,b) boundary conditions just turned into terms added to the right hand side, but only in the first and last rows: an "external force" applied at the boundaries. The PDE version of this technique involves delta functions, which we aren't prepared to handle yet. (In fact, this generalizes to cases where we want to specify jumps and other discontinuities of u in the *interior* of  $\Omega$  as well, in which case one can again use new surface-localized terms on the right-hand-side and it is sometimes called an "immersed boundary" or "imbedded boundary" method, especially in fluid mechanics.)

To better understand how Neumann boundary conditions arise, we have to better understand the meaning of  $\nabla u$ . Considered the case of a diffusion equation, where u=mass/volume of some solute, and  $\nabla \cdot c \nabla u = \partial u/\partial t$ . The total mass M within some volume V is just  $\int_{V} u$ , and showed by applying the divergence theorem we obtain dM/dt equal to a surface integral of  $c\nabla u$ . Since dM/dt>0 when mass is flowing *in* to the volume, this means that  $-c\nabla u$  is a mass "flux" vector (mass/time·area).

If we have diffusion in a closed container, so that no mass can flow in or out of  $\Omega$ , we then immediately see that we should apply (0) Neumann boundary conditions. Furthmore, total mass =  $\int_{\Omega} u$  is *conserved* (constant in time) for any solution u.

More generally, for any equation  $\hat{A}u=\partial u/\partial t$ , showed that we obtain a **conservation law**  $\partial/\partial t$   $\langle v,u\rangle=0$  for any  $v(\mathbf{x})$  in the *left null space*  $N(\hat{A}^*)$ .

For the case of diffusion with Neumann boundary conditions, reviewed the fact that  $\hat{A}=\hat{A}^*$  but  $\hat{A}$  is only negative *semidefinite*:  $N(\hat{A})=N(\hat{A}^*)$  contains any *constant function*, and is spanned by  $v(\mathbf{x})=1$ . Hence  $\langle 1,u \rangle$  is conserved. i.e. total mass, or total heat, or average temperature, is conserved in a closed/insulated  $\Omega$ .

Another example of a (0) Neumann boundary condition arises when we are considering  $u(\mathbf{x})$  that are mirror-symmetric (even) around some mirror plane, which is equivalent to imposing a Neumann boundary condition on the mirror plane. (Similar, antisymmetric/odd symmetry is equivalent to a zero Dirichlet boundary.) Another example is a stretched string where one end can slide freely up and down a rod with no friction: that end has a Neumann condition.

There are many other possible boundary conditions, of course. The most complicated ones can arise for PDEs with multiple unknowns (e.g. pressure, temperature, velocity, ...), in which case the boundary conditions may be equations relating several different unknowns or their derivatives.

One can also have *nonlocal* boundary conditions, in which u at one point on  $\partial\Omega$  is related to u at a *different* point. The most common example of this are *periodic* boundary conditions. e.g. considered  $\hat{A}=d^2/dx^2$  on [0,L] for u(0)=u(L). Showed that  $\hat{A}$  is still self-adjoint, but not because the boundary terms are *individually* zero, but rather because the x=0 and x=L boundary terms *cancel*. The eigenfunctions are now sines *and* cosines of  $2\pi nx/L$ , and give a general Fourier series (not just a sine or cosine series)! Also,  $\hat{A}$  is now negative *semidefinite* because constant u are allowed. Hence, for example, diffusion on a periodic domain still conserves total mass, because any mass that exits one side comes back in through the other side.

**Further reading:** The u=v+g trick is closely related to the standard proof of the uniqueness of solutions to Laplace's/Poisson's equation with general Dirichlet boundaries (google "Laplace uniqueness" or "Poisson uniqueness", e.g. this page). The trick of moving boundary conditions over to the right-hand side is so obvious for finite-difference methods that it hardly has a name, but it is often commented on explicitly for finite-element methods where things are less obvious (e.g. section 3.6 of the book). There is a review of immersed boundary methods by Mittal and Iaccarino that is fairly readable, but oriented mainly towards fluid mechanics. Periodic domains arise in many cases, the most obvious being equations on a torus (e.g. waves on a membrane that loops back to itself, diffusion in a circular tube, or masses and springs connected into a ring). They also arise for systems that repeat periodically, e.g. a periodic crystal in solid-state physics, in which case you can write the solutions as Bloch waves of the form  $u(x)=u_k(x)e^{ik \cdot x}$  where  $u_k$  is a periodic function that solves a PDE with periodic boundary conditions (and plotting the eigenvalues as a function of k gives a band structure).

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 11

(Finished discussion of Neumann from previous lecture: mass flux, conservation of mass in the diffusion equation, and other conservation laws.)

2d finite-difference discretizations: discretized the 2d Laplacian operator  $\nabla^2$  in an  $L_x \times L_y$  box with  $N_x \times N_y$  points, for Dirichlet (0) boundaries, so that  $u(m\Delta x, n\Delta y)$  is approximated by  $N_x N_y$  degrees of freedom  $u_{m,n}$ . Showed that simply applying the 1d center-difference rule along x and y results in a (famous) "5-point stencil" approximation for  $-\nabla^2$  in which the Laplacian at  $(n_x, n_y)$  depends on u at  $(n_x, n_y)$  and the 4 nearest-neighbor points.

In order to express this as a matrix A, however, we need to "flatten" the 2d grid of points  $u_{nx,ny}$  into a single column vector  $\mathbf{u}$  with  $N_xN_y$  components. There are multiple ways to do this, but a standard and easy scheme is the "column-major" approach in which  $\mathbf{u}$  is formed from the contiguous columns (x)  $u_{nx,:}$  concatenated in sequence. (This is the approach used internally within Matlab to store matrices.)

Given this, we then see how to form  $\partial^2/\partial x^2$  by operating one  $N_x$ -column at a time, using the the  $N_x \times N_x$  discrete 1d Laplacian  $A_x$  (=- $D_x^T D_x$ ). The  $\partial^2/\partial x^2$  matrix is simply a matrix with  $A_x$  along the diagonal  $N_y$  times, which differentiates each  $N_x$ -column block by block. The  $\partial^2/\partial y^2$  matrix is a little tricker, but if we think of operating on whole columns then we see that it is just the  $A_y$  matrix with the entries "multiplied" by  $N_x \times N_x$  identity matrices  $I_x$ .

In order to have a convenient way to express this, we use the Kronecker product notation  $A \otimes B$  [kron(A,B) in Matlab], which multiplies the *entries* of A by the *matrix* B to create a *matrix of matrices*. In this notation,  $A = I_v \otimes A_x + A_v \otimes I_x$ .

Using this machinery, constructed A for  $N_x=10$  and  $N_y=15$  for  $L_x=1$  and  $L_y=1.5$  in Julia. Visualized the pattern of nonzero entries with spy. Solved for the eigenfunctions, and plotted a few; to convert a column vector  $\mathbf{u}$  back into a 2d matrix, used reshape( $\mathbf{u}$ , $N_x$ , $N_y$ ), and plotted in 3d with the surf command. The first few eigenfunctions can be seen to roughly match the  $\sin(n_x\pi x/L_x)\sin(n_y\pi x/L_y)$  functions we expect from separation of variables. However,  $N_x=10$ ,  $N_y=15$  is rather coarse, too coarse a discretization to have a really nice (or accurate) picture of the solutions.

In order to increase  $N_x$  and  $N_y$ , however, we have a problem. If the problem has  $N=N_xN_y$  degrees of freedom, we need to store  $N^2$  numbers  $(8N^2$  bytes) just to store the matrix A, and even just solving Ax=b by Gaussian elimination takes about  $N^3$  arithmetic operations. Worked through a few numbers to see that even  $N_x=N_y=100$  would have us waiting for 20 minutes and needing a GB of storage, while 3d grids (e.g.  $100\times100\times100$ ) seem completely out of reach. The saving grace, however, is sparsity: the matrix is mostly zero (and in fact the 5-point stencil A has < 5N nonzero entries). This means that, first, you can store only the nonzero entries, greatly reducing storage. Second, it turns out there are ways to exploit the sparsity to solve Ax=b much more quickly, and there are also quick ways to find a *few* of the eigenvalues and eigenvectors.

In Julia, you exploit sparsity by using the sparse command and friends to create sparse matrice. Once you have a sparse matrix, Matlab automatically uses algorithms to exploit sparsity if you solve Ax=b by x=Ab and use the eigs function to find a few eigenvalues (instead of eig).

Starting with the  $\nabla^2$  operator on a square grid, showed how we can convert to any other  $\Omega$  shape with Dirichlet boundaries just by taking a subset of the rows/cols (as in problem 2 of pset 5). Recovered the Bessel solutions for a circular domain.

**Further reading:** Section 3.5 of the Strang book on 2d finite differences, section 7.1 on sparsity. See, for example min-max theorem in Wikipedia, although this presentation is rather formal. Unfortunately, most of the discussion you will find of this principle online and in textbooks is either (a) full of formal functional analysis or (b) specific to quantum mechanics [where the operator is  $A=-\nabla^2+V$  for some "potential-energy" function V(x)].

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 12

Using this Kronecker-product machinery, constructed A for  $N_x$ =10 and  $N_y$ =15 for  $L_x$ =1 and  $L_y$ =1.5 in Julia. Visualized the pattern of nonzero entries with spy. Solved for the eigenfunctions, and plotted a few; to convert a column vector  $\mathbf{u}$  back into a 2d matrix, used reshape( $\mathbf{u}$ , $N_x$ , $N_y$ ), and plotted in 3d with the surf command. The first few eigenfunctions can be seen to roughly match the  $\sin(n_x\pi x/L_x)\sin(n_y\pi x/L_y)$  functions we expect from separation of variables. However,  $N_x$ =10,  $N_y$ =15 is rather coarse, too coarse a discretization to have a really nice (or accurate) picture of the solutions.

In order to increase  $N_x$  and  $N_y$ , however, we have a problem. If the problem has  $N=N_xN_y$  degrees of freedom, we need to store  $N^2$  numbers ( $8N^2$  bytes) just to store the matrix A, and even just solving Ax=b by Gaussian elimination takes about  $N^3$  arithmetic operations. Worked through a few numbers to see that even  $N_x=N_y=100$  would have us waiting for 20 minutes and needing a GB of storage, while 3d grids (e.g.  $100\times100\times100$ ) seem completely out of reach. The saving grace, however, is sparsity: the matrix is mostly zero (and in fact the 5-point stencil A has < 5N nonzero entries). This means that, first, you can store only the nonzero entries, greatly reducing storage. Second, it turns out there are ways to exploit the sparsity to solve Ax=b much more quickly, and there are also quick ways to find a *few* of the eigenvalues and eigenvectors.

In Julia, you exploit sparsity by using the sparse command and friends to create sparse matrice. Once you have a sparse matrix, Matlab automatically uses algorithms to exploit sparsity if you solve Ax=b by  $x=A\b$  and use the eigs function to find a few eigenvalues (instead of eig).

Starting with the  $\nabla^2$  operator on a square grid (from last lecture), showed how we can convert to any other  $\Omega$  shape with Dirichlet boundaries just by taking a subset of the rows/cols. Looked at a couple of triangular domains, and recovered the Bessel solutions for a circular domain.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 13

In order to get an intuitive feel for what the eigenfunctions should look like, a powerful tool is the **min–max theorem**. See handout for notes.

As a final example corresponding to the  $-c\nabla^2$  operator in the notes, considered an "L"-shaped domain  $\Omega$  with c=1/w(x). In particular, suppose that w(x)=1 everywhere except for a small region where  $w(x)=w_0>1$ . In order to concentrate in this small region, u(x) will have to have bigger slope (sacrificing the numerator). As  $w_0$  increases, we expect the denominator of the Rayleigh quotient to "win" and the concentration to increase, while for  $w_0$  close to 1 the eigenfunctions should be similar to the case of  $-\nabla^2$ .

**Further reading:** See, for example min-max theorem in Wikipedia, although this presentation is rather formal. Unfortunately, most of the discussion you will find of this principle online and in textbooks is either (a) full of formal functional analysis or (b) specific to quantum mechanics [where the operator is  $A=-\nabla^2+V$  for some "potential-energy" function V(x)].

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 14

(See notes.) Introduced Green's functions by analogy with matrix inverses, and constructed Green's function of  $-d^2/dx^2$  with Dirichlet boundaries as an example.

We had to jump through some hoops to avoid a problematic-looking "delta function" that keeps appearing, a limit of a function whose area is "infinitely concentrated" at a "single point". This is possible, but becomes more and more painful as we go on, motivating us to find an alternate definition of "function" in the future, a **distribution**.

For the 1d example, we can explicitly check that  $u(x) = \int G(x,x')f(x')dx'$  solves -u''=f. (See 2nd handout.)

**Further reading:** Strang book, section 1.4. Many PDE books introduce Green's functions and delta functions in various ways; see, e.g. section 9.3.4 of *Elementary Applied Partial Differential Equations* by Haberman.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 15

Went through notes on reciprocity and positivity of Green's functions.

The previous approach is all extremely cumbersome though—we have to go through lots of contortions to avoid differentiating discontinuities and avoid delta functions. More generally, there are a number of difficulties that continually arise when we deal with classical functions (mapping numbers to numbers): went through section 1 of the distribution handout.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 16

Delta functions and distributions: finished notes from previous lecture.

**Further reading:** See the books *Generalized Functions* by Gel'fand and Shilov and *A Guide to Distribution Theory and Fourier Transforms* by Strichartz referenced at the end of the notes. Wikipedia has a decent article on distributions. The idea that there are functions  $\phi(x)$  which are infinitely differentiable but are zero outside of a finite region is a bit counterintuitive if you think about the interface between the zero and nonzero regions, but it is quite possible; see bump function on Wikipedia for an elaboration on the example I gave in class, and a proof that the derivatives are continuous here. In practice, however, we will almost never have to explicitly construct test functions to talk about distributions.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 17

Derived Green's function of  $\nabla^2$  in 3d for infinite space (requiring solutions to  $\rightarrow$  zero at infinity to get a unique solution), in three steps:

- 1. Because the  $\nabla^2$  operator is invariant under translations (changes of variables  $\mathbf{x} \rightarrow \mathbf{x} + \mathbf{y}$ ), showed that  $G(\mathbf{x}, \mathbf{x}')$  can be written as  $G(\mathbf{x}, \mathbf{x}') = G(\mathbf{x} \mathbf{x}', 0)$ . Similarly, rotational invariance implies that  $G(\mathbf{x} \mathbf{x}', 0) = g(|\mathbf{x} \mathbf{x}'|)$  for some function  $g(\mathbf{r})$  that only depends on the distance from  $\mathbf{x}'$ .
- 2. In spherical coordinates, solved  $-\nabla^2 g = 0$  for r > 0 (away from the delta function), obtaining g(r)=c/r for some constant c to be determined.
- 3. Took the distributional derivative  $(-\nabla^2 g)\{\phi\} = g\{-\nabla^2 \phi\}$  ("integrating by parts" using the fact from Lecture 7 that  $\nabla^2$  is self-adjoint) for an arbitrary test function  $\phi(\mathbf{x})$ , and showed by explicit integration that we get  $c\phi(0)$ . Therefore  $c=1/4\pi$  for us to solve  $-\nabla^2 g = \delta(\mathbf{x}-\mathbf{x}')$ .

Hence  $G(\mathbf{x}, \mathbf{x}') = 1/4\pi |\mathbf{x} - \mathbf{x}'|$  for this problem, and  $-\nabla^2 \mathbf{u} = \mathbf{f}$  is solved by  $\mathbf{u}(\mathbf{x}) = \int f(\mathbf{x}') d^3 \mathbf{x}' / 4\pi |\mathbf{x} - \mathbf{x}'|$ .

A physical example of this can be found in electrostatics, from 8.02: the potential V of a charge density  $\rho$ , satisfies  $-\nabla^2 V = \rho/\epsilon_0$ . A point charge q at  $\mathbf{x}'$  is a charge density that is zero everywhere except for  $\mathbf{x}'$ , and has integral q, hence is  $\rho(\mathbf{x}) = q\delta(\mathbf{x} - \mathbf{x}')$ . Solving for V is exactly our Green's function equation except that we multiply by  $q/\epsilon_0$ , and hence the solution is  $V(\mathbf{x}) = q/4\pi\epsilon_0|\mathbf{x} - \mathbf{x}'|$ , which should be familiar from 8.02. Hence  $-\nabla^2 V = \rho/\epsilon_0$  is solved by  $V(\mathbf{x}) = \int \rho(\mathbf{x}') d^3 \mathbf{x}' / 4\pi\epsilon_0|\mathbf{x} - \mathbf{x}'|$ , referred to in 8.02 as a "superposition" principle (writing any charge distribution as the sum of a bunch of point charges).

Perhaps the most important reason to solve for  $G(\mathbf{x},\mathbf{x}')$  in empty space is that solutions for more complicated systems, with boundaries, are "built out of" this one.

An illustrative example is  $\Omega$  given by the 3d half-space z>0, with Dirichlet boundaries (solutions=0 at z=0). For a point  $\mathbf{x}'$  in  $\Omega$ , showed that the Green's function  $G(\mathbf{x},\mathbf{x}')$  of  $-\nabla^2$  is  $G(\mathbf{x},\mathbf{x}')=(1/|\mathbf{x}-\mathbf{x}'|-1/|\mathbf{x}-\mathbf{x}''|)/4\pi$ , where  $\mathbf{x}''$  is the same as  $\mathbf{x}'$  but with the sign of the z component flipped. That is, the solution in the upper half-space z>0 looks like the solution from two point sources  $\delta(\mathbf{x}-\mathbf{x}')-\delta(\mathbf{x}-\mathbf{x}'')$ , where the second source is a "negative image" source in z<0. This is called the **method of images**.

Reviewed method-of-images solution for half-space. There are a couple of other special geometries where a method-of-images gives a simple analytical solution, but it is not a very general method (complicated generalizations for 2d problems notwithstanding). The reason we are covering it, instead, is that it gives an analytically solvable example of a principle that *is* general: Green's functions (and other solutions) in complicated domains *look like solutions in the unbounded domain plus extra sources on the boundaries*.

**Further reading:** See e.g. sections 9.5.6–9.5.8 of *Elementary Applied Partial Differential Equations* by Haberman for a traditional textbook treatment of Green's functions of  $\nabla^2$  in empty space and the half-space. If you Google "method of images" you will find lots of links, mostly from the electrostatics viewpoint see also e.g. *Introduction to Electrodynamics* by Griffiths for a standard textbook treatment; the only mathematical difference introduced by (vacuum) electrostatics is the multiplication by the physical constant  $\varepsilon_0$  (and the identification of  $-\nabla V$  as the electric field).

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 18

In the image method, the "extra source" is ostensibly not on the boundary, it is on the other side of the boundary. However, we can transform it to what we want by the following trick: consider the function  $\mathbf{u}(\mathbf{x})$  in  $\Omega = \mathbb{R}^3$  that equals  $(1/|\mathbf{x}-\mathbf{x}'| - 1/|\mathbf{x}-\mathbf{x}''|)/4\pi$  [the method-of-images solution] for z>0 and  $\mathbf{u}(\mathbf{x})=0$  for z<0. What right-hand-side does  $-\nabla^2\mathbf{u}$  give? In z>0  $-\nabla^2\mathbf{u}$  gives  $\delta(\mathbf{x}-\mathbf{x}')$  as before, and for z<0  $-\nabla^2\mathbf{u}$  gives zero. At z=0, however, there is a slope discontinuity in  $(1/|\mathbf{x}-\mathbf{x}'| - 1/|\mathbf{x}-\mathbf{x}''|)/4\pi$ , which means that  $-\nabla^2\mathbf{u}$  also gives a  $\delta(\mathbf{z})$  term:  $\delta(\mathbf{z})$   $\sigma(\mathbf{x},\mathbf{y})$  for a  $\sigma(\mathbf{x},\mathbf{y})$  given by the amplitude of the slope discontinuity.

What does this mean? Our solution  $u(\mathbf{x})$  is due to the sum of a point source at  $\mathbf{x}'$  and sources at the interface (z=0). Worked out what these sources  $\sigma(\mathbf{x},\mathbf{y})$  are. Physically, in the electrostatics example they correspond to a surface charge density on the surface of a conductor. Why are these sources there? They are there to cancel the effect of the source at  $\mathbf{x}'$  for z<0, enforcing the boundary condition u=0 at z=0.

More generally, we can do this for *any* interface  $d\Omega$ : we can write the solution from a point source  $\delta(\mathbf{x}-\mathbf{x}')$  in  $\Omega$  as the sum of the solution from that point source plus an integral of *unknown* point sources  $\sigma(\mathbf{x}')$  for points  $\mathbf{x}'$  the boundary  $d\Omega$ . Formally, we determine  $\sigma(\mathbf{x}')$  by requiring  $u(\mathbf{x})$  to satisfy the boundary condition at  $d\Omega$ , which gives a *surface integral equation* (SIE) (of the "first kind") for  $\sigma(\mathbf{x}')$ . Numerically, we discretize the surface in some way to get a finite number of unknowns approximating  $\sigma(\mathbf{x}')$ , leading to an SIE numerical method.

SIE methods (most commonly the "boundary element method", BEM) are very powerful in several ways. Because they only have unknowns on the *boundaries* (not everywhere in space like in a PDE method like finite differences), they can greatly reduce the number of unknowns: they handle the homogeneous regions analytically. They can handle infinite space (e.g. a cylinder surrounded by infinite space as in the pset) analytically, with no artificial truncation. Done properly, the matrices can have very nice properties. There are also some difficulties. SIE methods are not so efficient for problems that are not mostly homogeneous, especially continuously-varying media, and nonlinear or time-dependent problems are also difficult. Because the empty-space Green's function  $(1/4\pi |\mathbf{x}-\mathbf{x}'| \text{ in 3d})$  blows up for nearby points, there are lots of tricky singularities that must be dealt with carefully in setting up SIE methods. Furthermore, because you have long-range interactions (every surface point interacts with every other point via the Green's function), the matrices are dense, not sparse. That means that developing fast solvers for large problems is tricky; remarkably, there are ways to do this (most famously the pioneering fast multipole method invented in 1985), but implementing them is not for the timid. Worse, the singularity-handling and fast-solver techniques depend heavily on the specific Green's function of empty space; for example, changing from  $3d (1/|\mathbf{x}-\mathbf{x}'|)$  to  $2d (\ln|\mathbf{x}-\mathbf{x}'|)$ problems requires a completely different implementation, although the concepts are similar.

**Further reading:** There are many books on integral-equation methods, e.g. *Boundary Integral Equation Methods for Solids and Fluids* by Bonnet is a reasonably general introduction.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### Lecture 19

# 1 Homogeneous media

Suppose we have Poisson's equation with constant coefficients (= 1 for simplicity), i.e. in a homogeneous medium, i.e. in "empty space", i.e.

$$-\nabla^2 u = f$$

in some region  $\Omega$ , with boundary conditions so that this has a unique solution, e.g. Dirichlet boundaries  $u|_{d\Omega} = 0$ . Then we can write the solution in terms of the Green's function  $G_0(\mathbf{x}, \mathbf{x}')$ :

$$u(\mathbf{x}) = \int_{\Omega} G_0(\mathbf{x}, \mathbf{x}') f(\mathbf{x}') d^n \mathbf{x}', \tag{1}$$

in *n* dimensions, where  $-\nabla^2 G_0(\mathbf{x}, \mathbf{x}') = \delta(\mathbf{x} - \mathbf{x}')$ . For example, if  $\Omega = \mathbb{R}^3$ , then  $G_0(\mathbf{x}, \mathbf{x}') = \frac{1}{4\pi |\mathbf{x} - \mathbf{x}'|}$ .

# 2 Inhomogeneous media

Now, suppose we have non-constant coefficients  $c(\mathbf{x}) > 0$ , corresponding to an inhomogeneous medium (i.e. different "materials" at different points in space). This could enter Poisson's equation in several ways, for example:

- 1.  $-c\nabla^2 u = f$  for example, in a stretched string or drum, 1/c would be proportional to the density, so  $c(\mathbf{x})$  would represent a variable density.
- 2.  $-\nabla \cdot (c\nabla u) = f$  for example, in electrostatics  $\sqrt{c}$  would be proportional to the refractive index; in a stretched string or drum c would be proportional to a tension/elasticity; in a diffusion problem c would be a diffusion coefficient; in a heat-conduction problem c would be proportional to a thermal conductivity.
- 3.  $-\nabla^2 u + cu = f$  for example, in quantum mechanics this would represent Schrödinger's equation with a variable potential energy c.
- 4. Various other generalizations and combinations. e.g. a multidimensional Sturm–Liouville equation,  $-c_1\nabla \cdot (c_2\nabla u) + c_3u = f$ , for different functions  $c_{1,2,3}(\mathbf{x})$  (and  $c_2$  could even be a positive-definite matrix).

All of these are of the form  $\hat{A}u = f$  where  $\hat{A}$  is self-adjoint and positive-definite (assuming zero Dirichlet boundary conditions and an appropriate inner product  $\langle u, v \rangle$ ), as we've seen previously in class, so they should have unique solutions (excluding pathological c functions). However, the solutions may in general be quite different from those of  $-\nabla^2 u = f$ . Can we relate them to  $G_0$ , the Green's function for empty space?

$$2.1 \quad -c\nabla^2 u = f$$

This case is quite trivial to relate to empty space: just rewrite it as  $-\nabla^2 u = f/c$  (valid since c > 0), in which case we can use eq. (1) to obtain

$$u(\mathbf{x}) = \int_{\Omega} G_0(\mathbf{x}, \mathbf{x}') \frac{f(\mathbf{x}')}{c(\mathbf{x}')} d^n \mathbf{x}',$$

from which it follows that the Green's function of this problem is  $G(\mathbf{x}, \mathbf{x}') = G_0(\mathbf{x}, \mathbf{x}')/c(\mathbf{x}')$ .

**2.2** 
$$-\nabla \cdot (c\nabla u) = f$$

To make it look like empty space, we employ the product rule to write  $\nabla(c\nabla u) = (\nabla c) \cdot (\nabla u) + c\nabla^2 u$ , obtaining:

$$-\nabla^2 u = \frac{f}{c} + \frac{\nabla c}{c} \cdot \nabla u.$$

If we substitute the right-hand side as if it were "f" in the empty-space problem, from eq. (1), and note that  $(\nabla c)/c = \nabla \ln c$ , we obtain:

$$u(\mathbf{x}) = \int_{\Omega} G_0(\mathbf{x}, \mathbf{x}') \left[ \frac{f(\mathbf{x}')}{c(\mathbf{x}')} + \nabla' [\ln c(\mathbf{x}')] \cdot \nabla' u(\mathbf{x}') \right] d^n \mathbf{x}'.$$
 (2)

Notice, however, that the unknown u appears on both the left- and right-hand sides. This is a **volume integral equation**<sup>1</sup> for  $u(\mathbf{x})$ . There are various numerical methods to solve such "VIE" problems approximately by discretizing space, but we won't cover these in 18.303. However, there are still several lessons to be learned from this equation. First, one can think of the inhomogeneous solution as the sum of "homogeneous" solutions  $G_0(\mathbf{x}, \mathbf{x}')$  from the right-hand-sides  $f(\mathbf{x}')/c$  at  $\mathbf{x}'$  plus a "scattered" solution from the solution u creating new source terms at inhomogeneities  $\nabla c$ . Second, there are various general situations where this VIE simplifies considerably. In the following, denote

$$u_0(\mathbf{x}) = \int_{\Omega} G_0(\mathbf{x}, \mathbf{x}') \frac{f(\mathbf{x}')}{c(\mathbf{x}')} d^n \mathbf{x}',$$

the part of  $u(\mathbf{x})$  that doesn't come from the inhomogeneity  $\nabla c$ , the "incident" solution. We then can write  $u = u_0 + \hat{B}u$  where  $\hat{B}$  is the linear integral operator corresponding to  $\hat{B}u = \int G_0 \nabla' \ln c \cdot \nabla' u$ .

(This terminology of "incident" and "scattered" parts of the solution has its origins in wave-equation problems, where the solution represents a wave propagating outwards from a source f, and is actually bouncing off of objects/inhomogeneities. In the present problem, there is no time dependence so this terminology is only an analogy.)

#### 2.2.1 Piecewise-homogeneous media

The most common and important case of inhomogeneous media is where  $c(\mathbf{x})$  is **piecewise-constant**. e.g. in one region you have glass, in another region you have metal, and in another region you have water, each corresponding to a different constant value of c.

For example, suppose we have  $\Omega = \mathbb{R}^3$ , with  $-\nabla \cdot (c\nabla u) = f$  for the situation depicted in figure 1:  $c(\mathbf{x}) = c_1$  in some volume V and  $= c_2$  outside of V. In this case  $\nabla \ln c$  is actually a delta function at the interface, multiplied by the magnitude  $\ln c_2 - \ln c_1 = \ln(c_2/c_1)$  of

 $<sup>^{1}</sup>$ More specifically, it is a "second-kind" integral equation, since u appears both inside and outside the integral.

Figure 1: Schematic example of piecewise-constant coefficients  $c(\mathbf{x})$ :  $c(\mathbf{x}) = c_1$  in some region V (with boundary dV, and  $\hat{\mathbf{n}}$  denoting the outward unit-normal vector), and  $c(\mathbf{x}) = c_2$  otherwise.

the discontinuity, also multiplied by a unit-normal vector  $\hat{\mathbf{n}}$  at each point on the interface (giving the direction  $\nabla \ln c$ ). Then the VIE (2) simplifies to  $u_0$  plus a *surface integral*:

$$u(\mathbf{x}) = u_0(\mathbf{x}) + \ln(c_2/c_1) \oiint_{dV} G_0(\mathbf{x}, \mathbf{x}') \nabla' u(\mathbf{x}') \cdot d\mathbf{A}', \tag{3}$$

where  $d\mathbf{A}' = \hat{\mathbf{n}} dA'$  is the usual outward-normal differential area in a surface integral. This is now a **surface integral equation** (SIE) for  $u(\mathbf{x})$ : once we know  $\hat{\mathbf{n}} \cdot \nabla u$  on the surface, we can get  $\mathbf{u}(\mathbf{x})$  everywhere! Physically, this can be interpreted as "scattering" of the solution off the *interface* between  $c_1$  and  $c_2$ , as represented by "source" terms at every  $\mathbf{x}' \in dV$ .

However, this isn't quite right. The problem is that  $\nabla u \cdot \hat{\mathbf{n}}$  isn't actually continuous across the interface in general, and so evaluating it on the surface dV is not well-defined. We can see this by looking at the original equation  $\nabla \cdot (c\nabla n) = f$ : unless f happens to have delta functions right on the dV interface, the quantity  $c\nabla u$  must be continuous across the interface in the  $\hat{\mathbf{n}}$  direction. That is,  $c\nabla u \cdot \hat{\mathbf{n}}$  is continuous, not  $\nabla u \cdot \hat{\mathbf{n}}$ . So, before we can evaluate a surface integral, we need to rewrite things in terms of  $c\nabla u \cdot \hat{\mathbf{n}}$ . We can do this, since

$$\nabla[\ln c] \cdot \nabla u = \frac{\nabla c}{c} \cdot \nabla u = \frac{\nabla c}{c^2} \cdot c \nabla u = \nabla \left( -\frac{1}{c} \right) \cdot c \nabla u$$

in eq. (2). And  $\nabla(-1/c)$  is also a delta function multiplied by  $\hat{\mathbf{n}}$  and the magnitude  $\frac{1}{c_1} - \frac{1}{c_2}$  of the discontinuity, and hence we obtain a corrected SIE:

$$u(\mathbf{x}) = u_0(\mathbf{x}) + \left(\frac{1}{c_1} - \frac{1}{c_2}\right) \iint_{dV} G_0(\mathbf{x}, \mathbf{x}') \left[c(\mathbf{x}')\nabla' u(\mathbf{x}')\right] \cdot d\mathbf{A}', \tag{4}$$

which is well-defined since the integrand is now a continuous quantity across the interface. (And even this is not quite in the form that is used in numerics.)

Like our SIE equations for the case where  $\Omega$  itself has a boundary, these SIE equations are solved by parameterizing the surface unknowns via some discretization, and then choosing the unknowns so that u satisfies appropriate continuity conditions at the interface dV. The details of this get rather tricky very quickly, but these can yield very efficient computational methods because they only involve unknowns at interfaces and handle homogeneous regions (even infinite homogeneous regions) analytically via  $G_0$ .

#### 2.2.2 Born approximation

We have written the solution in the form  $u = u_0 + \hat{B}u$ , where  $u_0$  is the solution due to f ignoring the inhomogeneity, and  $\hat{B}$  is an integral operator giving the "scattered" portion of the solution  $\hat{B}u$  due to the inhomogeneity. We can then formally write:

$$u = u_0 + \hat{B}u = u_0 + \hat{B}(u_0 + \hat{B}u) = u_0 + \hat{B}u_0 + \hat{B}^2(u_0 + \hat{B}u_0 + \hat{B}^2u)$$
$$= \cdots = \left(\sum_{k=0}^{\infty} \hat{B}^k\right) u_0,$$

which is called a "Born–Dyson" series/expansion (sometimes omitting one name or the other). Equivalently,  $(1 - \hat{B})u = u_0$  implies  $u = (1 - \hat{B})^{-1}u_0$ , and the Taylor series for  $(1 - \hat{B})^{-1}$  is  $\sum_k \hat{B}^k$ .

What does this represent physically?  $u_0$  is the "incident" portion of the solution, before scattering off the inhomogeneity.  $\hat{B}u_0$  is the portion of the solution where this "incident" solution has scattered *once* off the inhomogeneity, producing a scattered solution

$$\hat{B}u_0 = \int_{\Omega} G_0(\mathbf{x}, \mathbf{x}') \nabla' \ln c(\mathbf{x}') \cdot \nabla' u_0(\mathbf{x}') d^n \mathbf{x}'.$$

But of course, *this* portion of the solution *also* scatters off of the inhomogeneity, producing a portion of the solution representing incident solutions that have scattered *twice*:

$$\hat{B}^2 u_0 = \int_{\Omega} G_0(\mathbf{x}, \mathbf{x}') \nabla' \ln c(\mathbf{x}') \cdot \nabla' \left[ \int_{\Omega} G_0(\mathbf{x}', \mathbf{x}'') \nabla'' \ln c(\mathbf{x}'') \cdot \nabla'' u_0(\mathbf{x}'') d^n \mathbf{x}'' \right] d^n \mathbf{x}',$$

i.e. a  $u_0$  at  $\mathbf{x}''$  produces a source term due to  $\nabla''c$ , which "travels" from  $\mathbf{x}''$  to  $\mathbf{x}'$  via  $G_0(\mathbf{x}',\mathbf{x}'')$ , then produces a source at  $\mathbf{x}'$  due to  $\nabla'c$ , then "travels" from  $\mathbf{x}'$  to  $\mathbf{x}$  via  $G_0(\mathbf{x},\mathbf{x}')$ , and of course this must be integrated over all possible scattering points  $\mathbf{x}'$  and  $\mathbf{x}''$ . Then  $\hat{B}^3u_0$  represents things scattering three times, and so on.<sup>2</sup>

Now, suppose we have a system that is nearly homogeneous. e.g.  $\nabla c$  is small. Then one might expect that the scattered portion  $\hat{B}u$  of the solution to be small. In this case, we may be able to approximate this series by keeping only the first two terms—if scattering once has small amplitude, then scattering twice should have even smaller amplitude. (e.g. if  $\nabla c$  is small, this could be thought of as expanding as a power series in  $\nabla c$ , since  $\hat{B}^k \sim |\nabla c|^k$ .) This is the **Born approximation**:

$$u(\mathbf{x}) \approx u_0(\mathbf{x}) + \hat{B}u_0$$

and is an extremely useful way to think about nearly homogeneous problems.

<sup>&</sup>lt;sup>2</sup>In quantum mechanics, this kind of series of events is sometimes represented graphically by the notation of "Feynman diagrams," and can be generalized to nonlinear problems and other effective inhomogeneities. In that context, this process of summing all possible scattering sequences is sometimes mysteriously described as a "particle exploring all possible paths between two points," but is really just a consequence of particles being described by PDEs (Schrödinger's equation, in single-particle quantum mechanics), rather than ODEs.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 20

## 3 Example: Inhomogeneity in a small volume

Suppose we are solving  $-\nabla \cdot (c\nabla u) = f$  in  $\Omega = \mathbb{R}^3$  with a point source  $f(\mathbf{x}) = \delta(\mathbf{x} - \mathbf{x}_0)$  at  $\mathbf{x}_0$ . Furthermore, suppose that  $c(\mathbf{x})$  is piecewise-constant as in figure 1, with  $c(\mathbf{x}) = c_2$  everywhere except in a volume V, centered at  $\mathbf{x}_1$ , where  $\mathbf{c}(\mathbf{x}) = c_1$ . Now, suppose that we want the solution  $u(\mathbf{x})$ , but are far from V: both the source point  $\mathbf{x}_0$  and the desired point  $\mathbf{x}$  are far from V, with  $|\mathbf{x}_1 - \mathbf{x}_0|$  and  $|\mathbf{x}_1 - \mathbf{x}|$  both much bigger than the diameter of V. This is shown schematically in figure 2. In this case, we should expect the effect of the "scattered"

Figure 2: Schematic of problem with an inhomogeneity in a small volume V (centered at  $\mathbf{x}_1$ ): we have a source at  $\mathbf{x}_0$  and want the solution at  $\mathbf{x}$ , with both  $\mathbf{x}_0$  and  $\mathbf{x}$  much farther from  $\mathbf{x}_1$  than the diameter of V.

solution from V to be small at  $\mathbf{x}$ , and a Born approximation should apply. Furthermore, we will assume  $c_1 \approx c_2$  (though not exactly equal!), so that we can neglect the effect of the discontinuity in  $\nabla u$  mentioned after equation (3) above (which greatly complicates the application of any Born-like approximation in this problem because it would prevent us from using  $u \approx u_0$  in V).<sup>3</sup>

In this case,

$$u_0(\mathbf{x}) = G_0(\mathbf{x}, \mathbf{x}_0) / c(\mathbf{x}_0) = \frac{1}{4\pi c_2 |\mathbf{x} - \mathbf{x}_0|},$$

so in the Born approximation we write:

$$u(\mathbf{x}) \approx u_0(\mathbf{x}) + \hat{B}u_0$$

where the scattered part of the solution, applying the SIE form (4) [valid when  $c_1 \approx c_2$ ], is

$$\hat{B}u_0 = \ln(c_2/c_1) \iint_{dV} G_0(\mathbf{x}, \mathbf{x}') \nabla' u_0(\mathbf{x}') \cdot d\mathbf{A}'$$

$$= \ln(c_2/c_1) \iiint_{V} \nabla' \cdot [G_0(\mathbf{x}, \mathbf{x}') \nabla' u_0(\mathbf{x}')] d^3\mathbf{x}'$$

$$= \ln(c_2/c_1) \iiint_{V} \left[ \nabla' G_0(\mathbf{x}, \mathbf{x}') \cdot \nabla' u_0(\mathbf{x}') + G_0 \nabla'^2 u_0 \right] d^3\mathbf{x}',$$

<sup>&</sup>lt;sup>3</sup>It turns out that many people get this wrong in electromagnetism for cases when  $c_1$  and  $c_2$  are very different, as discussed in my paper on a closely related subject, "Roughness losses and volume-current methods in photonic-crystal waveguides," *Appl. Phys. B* **81**, 238–293 (2005): http://math.mit.edu/~stevenj/papers/JohnsonPoO5.pdf

where in the second line we applied the divergence theorem, and in the third line the product rule led to a  $\nabla^2 u_0$  term, where  $\nabla^2 u_0 = -\delta(\mathbf{x} - \mathbf{x}_0)$  is zero in V (since  $\mathbf{x}_0$  is outside of V).

Now, since V is small compared to the distance from  $\mathbf{x}$  and  $\mathbf{x}_0$ , the distances  $|\mathbf{x}' - \mathbf{x}|$  and  $|\mathbf{x}' - \mathbf{x}_0|$  hardly change for any  $\mathbf{x}' \in V$ , and so the  $\nabla' G_0$  and  $\nabla' u_0$  terms are approximately constant in this integral and we can just pull them out, giving the approximation:

$$\hat{B}u_0 \approx \ln(c_2/c_1) \nabla' G_0(\mathbf{x}, \mathbf{x}') \cdot \nabla' u_0(\mathbf{x}')|_{\mathbf{x}'=\mathbf{x}_1} \text{ volume}(V).$$

We can compute these gradients explicitly:

$$\nabla' \frac{1}{|\mathbf{x}' - \mathbf{y}|} = -\frac{\mathbf{x}' - \mathbf{y}}{|\mathbf{x}' - \mathbf{y}|^3},$$

and hence:

$$u(\mathbf{x}) \approx \frac{1}{4\pi c_2 |\mathbf{x} - \mathbf{x}_0|} + \ln(c_2/c_1) \frac{(\mathbf{x}_1 - \mathbf{x})}{4\pi |\mathbf{x}_1 - \mathbf{x}|^3} \cdot \frac{(\mathbf{x}_1 - \mathbf{x}_0)}{4\pi c_2 |\mathbf{x}_1 - \mathbf{x}_0|^3} \text{ volume}(V).$$
 (5)

Notice that the amplitude of the scattered term vanishes as volume(V)  $\rightarrow$  0, as expected. Notice that it also depends on the sign of  $(\mathbf{x}_1 - \mathbf{x}) \cdot (\mathbf{x}_1 - \mathbf{x}_0)$ . Why is that? What does a  $\nabla' G_0$  source "mean," physically?

## 3.1 Dipole sources

Consider the following problem in  $\Omega = \mathbb{R}^3$ , requiring as usual that solutions vanish at  $\infty$ :

$$-\nabla^2 D_{\mathbf{p}}(\mathbf{x}, \mathbf{x}') = -\mathbf{p} \cdot \nabla \delta(\mathbf{x} - \mathbf{x}') = +\mathbf{p} \cdot \nabla' \delta(\mathbf{x} - \mathbf{x}').$$

This is like the Green's function equation, except now we have put the *derivative* of a delta function on the right-hand side, with some constant vector  $\mathbf{p}$  (the "dipole moment"). Recall what the derivative of a delta function is:

$$[-\mathbf{p} \cdot \nabla \delta(\mathbf{x} - \mathbf{x}')]\{\phi\} = [\delta(\mathbf{x} - \mathbf{x}')]\{\mathbf{p} \cdot \nabla \phi\} = \mathbf{p} \cdot \nabla \phi|_{\mathbf{x}'} = \lim_{\epsilon \to 0} \frac{\phi(\mathbf{x}' + \epsilon \mathbf{p}) - \phi(\mathbf{x}' - \epsilon \mathbf{p})}{2\epsilon},$$

and hence (similar to pset 5 of 2010 or pset 7 of 2011),

$$-\mathbf{p} \cdot \nabla \delta(\mathbf{x} - \mathbf{x}') = \lim_{\epsilon \to 0} \frac{\delta(\mathbf{x} - \mathbf{x}' - \epsilon \mathbf{p}) - \delta(\mathbf{x} - \mathbf{x}' + \epsilon \mathbf{p})}{2\epsilon}.$$

That is, the derivative of a delta function is a limit of limit of two delta functions of opposite sign, displaced proportional to **p**. In 8.02, where delta functions are "point charges," this is what you would have called an "electric dipole."

We can solve for  $\mathbf{D}_{\mathbf{p}}$  quite easily, because we know the solution  $G_0$  to  $-\nabla^2 G_0(\mathbf{x}, \mathbf{x}') = \delta(\mathbf{x} - \mathbf{x}')$ , and  $\nabla$  and  $\nabla'$  derivatives can be interchanged in their order:

$$-\mathbf{p} \cdot \nabla \delta(\mathbf{x} - \mathbf{x}') = \mathbf{p} \cdot \nabla' \left[ \delta(\mathbf{x} - \mathbf{x}') \right] = \mathbf{p} \cdot \nabla' \left[ -\nabla^2 G_0(\mathbf{x}, \mathbf{x}') \right] = -\nabla^2 \left[ \mathbf{p} \cdot \nabla' G_0(\mathbf{x}, \mathbf{x}') \right],$$

and hence

$$D_{\mathbf{p}}(\mathbf{x}, \mathbf{x}') = \mathbf{p} \cdot \nabla' G_0(\mathbf{x}, \mathbf{x}') = \mathbf{p} \cdot \frac{\mathbf{x} - \mathbf{x}'}{4\pi |\mathbf{x} - \mathbf{x}'|^3}.$$

In electrostatics, the would be the potential of a dipole. Note that this falls off as  $\sim 1/|\mathbf{x} - \mathbf{x}'|^2$ , whereas  $G_0$  falls off as  $\sim 1/|\mathbf{x} - \mathbf{x}'|$ .

Given this solution, we can now interpret the scattered part of the solution (5) above: a small inhomogeneity gives an effective dipole source p at  $x_1$ , where

$$\mathbf{p} = -\ln(c_2/c_1) \frac{(\mathbf{x}_1 - \mathbf{x}_0)}{4\pi |\mathbf{x}_1 - \mathbf{x}_0|^3} \text{ volume}(V).$$

In electrostatics, for a typical case where V is a small piece of matter in vacuum,  $c_2 < c_1$ , so  $\mathbf{p}$  is parallel to  $\mathbf{x}_1 - \mathbf{x}_0$ . Physically, a positive point charge induces a dipole moment  $\mathbf{p}$  pointed away from the charge, because a "+" charge at  $\mathbf{x}_0$  pushes "+" charges in V away from it, as shown below.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 21

New topic: Time-stepping and stability. Before, we turned operator equations Âu=f into matrix equations Au=f by discretizing in space. Now, we want to turn time-dependent operator equations  $\hat{A}u=f+\partial u/\partial t$  into discrete equations in both time and space. This will involve a new concern: stability.

Began with a trivial example of an operator Â=a, a single number a<0, which for f=0 gives the ODE du/dt=au, and has the exponentially decaying (for a<0) solution u(t)=u(0)e<sup>at</sup>. Now we will discretize u(t) in time by  $u(n\Delta t)\approx u^n$ —we will always use *superscripts* to denote the *timestep* n. Approximating the time derivative by a forward difference yields  $u^{n+1} \approx (1+a\Delta t)u^n = (1+a\Delta t)^{n+1}u^0$ . Even though the exact ODE has decaying solutions, this discretization may have *exponentially* growing solutions unless  $\Delta t < 2/|a|$ : the discretization is only **conditionally stable**. In contrast, a backward difference yields  $u^{n+1} \approx (1-a\Delta t)^{-1} u^n = (1+a\Delta t)^{-1-n} u^0$ , which is always exponentially decaying for a<0: the scheme is **unconditionally stable**.

For a more general operator Â, we proceed conceptually in two steps. First, we discretize in space only to yield a system of ODEs  $A\mathbf{u} = \partial \mathbf{u}/\partial t$  for a matrix A (e.g. by finite differences in space). Then we discretize in time and ask what happens to the eigenvectors of A. Focused on the case where A (and  $\hat{A}$ ) are self-adjoint and negative-definite (negative eigenvalues  $\lambda < 0$ ), as for the heat equation  $(\hat{A}=\nabla^2)$  with Dirichlet boundaries. In this case, showed that forward differences give an **explicit timestep**  $u^{n+1} \approx (1+A\Delta t)u^n$  and are conditionally stable: we must have  $\Delta t < 2/|\lambda|$ . In contrast, backward differences give an **implicit timestep**  $u^{n+1} \approx (1-A\Delta t)^{-1} u^n$  where we must solve a linear system at each step, but are unconditionally stable (decaying for any  $\Delta t$ ).

## Some definitions:

- $\hat{A}u = \partial u/\partial t$  is **well posed** if the solution  $u(\mathbf{x},t)$  is finite for any finite t and for any initial condition  $u(\mathbf{x},0)$ . (Note that PDEs with diverging solutions can still be well-posed, as long as they are finite at finite times, even if they are exponentially large.)
- A discretization is **consistent** if the discretization goes to  $\hat{A}u = \partial u/\partial t$  as  $\Delta x$  and  $\Delta t \rightarrow 0$ .
  - If the difference between the discrete equations and  $\hat{A}u = \partial u/\partial t$ , the **local truncation error**, goes to zero as  $\Delta x^a$  and as  $\Delta t^b$ , then we say the scheme is "a-th order in space and b-th order in time."
- A discretization is **stable** if  $\mathbf{u}^{t/\Delta t} \approx \mathbf{u}(\mathbf{x},t)$  does *not* blow up as  $\Delta t \to 0$  and  $\Delta x \to 0$ . (Informally, we often say it is "stable" if the solution does not blow up for any  $\Delta t$ , but a more precise definition has to take into account that the original PDE may have solutions that blow up as  $t\rightarrow\infty$ .)
  - it is **conditionally stable** if it is stable only when  $\Delta t$  has a certain relationship to the spatial discretization A, and in particular this usually means that  $\Delta t$  is constrained by some relationship with  $\Delta x$ .
  - it is **unconditionally stable** if it is stable for all  $\Delta t$  independent of  $\Delta x$  or A (or at least as long as A has some property like negative-definiteness). A discretization is **convergent** if  $\mathbf{u}^{t/\Delta t} \rightarrow \mathbf{u}(\mathbf{x},t)$  as  $\Delta \mathbf{x}$ ,  $\Delta t \rightarrow 0$ .

A very important result (stated here without proof) is the **Lax equivalence theorem**: for any consistent discretization of a well-posed linear initial-value problem, stability implies **convergence and vice versa**. If it is unstable, then it is obvious that it cannot converge: the

discretization blows up but the real solution doesn't. Less obvious is the fact that *if it does not blow up, it must converge*.

The Lax theorem is very reassuring, because it turns out that it is quite difficult to prove stability in general (we usually prove necessary but not sufficient conditions in conditionally stable schemes), but if you run it and it doesn't blow up, you know it must be converging to the correct result.

The tricky case to analyze is that of conditionally stable schemes. We need to relate the eigenvalues of A to  $\Delta x$  in some way to obtain a useful condition on  $\Delta t$ .

For explicit timestepping of the heat/diffusion equation with forward differences,  $\Delta t$  is proportional to  $\Delta x^2$ , so even though the discretization is second-order in space (errors  $\sim \Delta x^2$ ) and first-order in time (errors  $\sim \Delta t$ ), the time and space discretization errors are comparable (or at least proportional).

On the other hand, for implicit timestepping with backward differences,  $\Delta t$  is independent of  $\Delta x$ , so the first-order accuracy in time can really limit us. Instead, presented a second-order scheme in time by considering  $(\mathbf{u}^{n+1}-\mathbf{u}^n)/\Delta t$  to be a *center* difference around step n+0.5 [ $t=(n+0.5)\Delta t$ ]. In this case, we evaluate the right-hand side  $A\mathbf{u}$  at n+0.5 by averaging:  $A(\mathbf{u}^{n+1}+\mathbf{u}^n)/2$ . This gives a **Crank-Nicolson** scheme:  $\mathbf{u}^{n+1}=(1-A\Delta t/2)^{-1}(1+A\Delta t/2)\mathbf{u}^n$ . This is an implicit scheme, but is second-order accurate in both space and time (assuming a 2nd-order A in space). Showed that it is unconditionally stable if A is negative-definite.

For conditionally stable schemes, we need the eigenvalues of A. Gave a crude argument that the biggest  $|\lambda|$  for  $\nabla^2$  and similar operators is proportional to  $\Delta x^2$ , based on the fact that the solution cannot oscillate faster than the grid. To do better than this, we need to consider simplified cases that we can analyze analytically.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 22

**Von Neumann analysis**. The idea of Von Neumann analysis is to analyze the eigenvalues of the space discretization, A, in a simple case that can be solved analytically:  $\infty$  space and constant coefficients. In this case the eigensolutions will be sinusoids (Fourier modes), which are most conveniently written as complex exponentials.

In particular, considered  $\hat{A}=d^2/dx^2$  in one dimension, discretized by the usual center difference. We try a solution  $u_m=e^{ikm}$ , and show that it is indeed an eigenvector (with infinitely many components in  $\infty$  space!) of the discretized second derivative. (Briefly reviewed properties of complex exponentials and the equivalence to sines and cosines by Euler's identity.) Showed that the corresponding eigenvalues are  $\lambda(k)=-4\sin^2(k/2)/\Delta x^2$ . Hence, the maximum  $|\lambda|$  is for  $k=\pi$  (a solution that oscillates with every grid point).

Applying the conditional stability result from last lecture for forward-difference timestepping, we find  $\Delta t < \Delta x^2/2$ . This is necessary and sufficient for stability in the  $\infty$ -space case, because any (polynomially bounded) initial condition can be written as a sum of these  $e^{ikm}$  functions. In fact, this is a kind of reverse Fourier series, a discrete-"time" Fourier transform (DTFT, although here it is space not time). Reviewed how Fourier series can be written in terms of complex exponentials rather than sines and cosines. Noted that k and k+2 $\pi$  give equivalent solutions: this is called aliasing, and means that we only need to consider k in  $[-\pi,\pi]$ .

When we have boundaries, inhomogeneities, etcetera, then it is usually too hard to compute the eigenvalues exactly; in this case Von Neumann analysis usually gives us at best a necessary condition for stability, but not a sufficient condition. In practice, though, it works very well, although usually we err on the conservative side and make  $\Delta t$  a little bit smaller than the Von Neumann bound might strictly request.

Similarly, analyzed the 2d heat equation with center differences in space and forward differences in time, and showed that the maximum  $\Delta t$  is decreased by a factor of 2. In general, it is decreased proportional to the number of dimensions.

The important consequence of this is: when you refine the discretization in space (decreasing  $\Delta x$ ), you must *also refine the discretization in time* (decreasing  $\Delta t$ ) in an explicit scheme (like forward differences in time).

New subject: **Wave equations.** Although we originally wrote the wave equation as a second derivative in time, in order to think about time evolution (either numerically or analytically) it is nicer to write it as a first-order derivative into time. The most obvious way to do this is to introduce a new variable  $v=\partial u/\partial t$ , but this turns out to lead to a somewhat unsymmetrical system of equations that is hard to analyze.

Instead, we will look at the scalar wave equation  $\nabla^2 u = \partial^2 u/\partial t^2$  in a new way. We will introduct a new vector-valued unknown  $\mathbf{v}$ , defined by  $\partial \mathbf{v}/\partial t = \nabla \mathbf{u}$  and  $\partial \mathbf{u}/\partial t = \nabla \cdot \mathbf{v}$ ; showed that this is equivalent to  $\nabla^2 \mathbf{u} = \partial^2 \mathbf{u}/\partial t^2$ . This leads to a new equation of the form  $\partial \mathbf{w}/\partial t = \hat{\mathbf{A}}\mathbf{w}$ , where  $\mathbf{w} = (\mathbf{u}; \mathbf{v})$  and  $\hat{\mathbf{A}}$  is the 2×2operator  $\hat{\mathbf{A}} = (0, \nabla \cdot ; \nabla, 0) = (0, \text{div}; \text{grad}; 0)$ . Now the problem looks superficially like

the heat/diffusion equation: it is first-order in time, with some new operator  $\hat{A}$ . But this  $\hat{A}$  is very different from the old  $\hat{A}=\nabla^2!$  In fact, we will see that this  $\hat{A}$  gives  $\hat{A}^*=-\hat{A}$ : it is **anti-Hermitian**, and from this stems many of the important properties of wave equations.

**Further reading:** See for example chapter 6 of the Strang book for a typical textbook treatment of Von Neumann analysis. Something I dislike about this and many textbooks is that it does Von Neumann analysis right away. I prefer considering the dependence of  $\Delta t$  on the eigenvalues of A in general first (where things are both simpler and more general than diving into a specific discretization), and only then finding the eigenvalues of A in the Von Neumann case where we can solve for them exactly.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 23

Defined the inner product  $\langle \mathbf{w}, \mathbf{w}' \rangle$  in the obvious way as  $\int (uu'+\mathbf{v}\cdot\mathbf{v}')$  and showed that  $\hat{A}^*=-\hat{A}$ , i.e. that it is anti-Hermitian, for either Dirichlet or Neumann boundary conditions. From this, reprised the proof of real eigenvalues for the Hermitian case to show that now the eigenvalues are purely imaginary. Alternatively, showed that  $i\hat{A}$  is a Hermitian operator, so all of the properties of Hermitian operators carry over to  $\hat{A}$  except that the eigenvalues are multiplied by i.

Showed that an anti-Hermitian operator  $\hat{A}$  is simply i times a self-adjoint/Hermitian operator  $-i\hat{A}$ , and therefore it inherits the nice properties of self-adjoint operators with one difference: the eigenvalues are *imaginary* instead of real. If we call the eigenvalues  $-i\omega$  for a real  $\omega$ , then it is clear that we obtain oscillating solutions with time dependence  $e^{-i\omega t}$ . Furthermore, showed that  $\langle w,w \rangle$  is conserved in time, which in the next lecture we will interpret as conservation of "energy".

With the wave equation in a new form  $\partial \mathbf{w}/\partial t = \mathbf{D}\mathbf{w}$ , we had derived important properties of D: anti-Hermitian, imaginary eigenvalues, unitary time evolution, conservation of energy, similar to the handout (but at a somewhat simpler level, as the handout is from a graduate class).

As in the notes from the previous lecture, considered the general case of the scalar wave equation with non-constant coefficients a,b>0:  $b\nabla \cdot (a\nabla u) = \partial^2 u/\partial t^2$ , splitting this up as  $\partial \mathbf{v}/\partial t = a\nabla u$  and  $\partial u/\partial t = b\nabla \cdot \mathbf{v}$ . As in the notes, showed that the resulting D operator is still anti-Hermitian but under a modified inner product  $\langle \mathbf{w}, \mathbf{w}' \rangle = \int (uu'/b + \mathbf{v} \cdot \mathbf{v}'/a)$ .

Gave simple example of compression waves in a 1d system that is the limit of springs and masses, from lecture 5.5. If h is the displacement, it is convenient (to obtain conservation of energy in a familiar form) to write  $u=\partial h/\partial t$  and  $v=\partial h/\partial x$ . We then get  $b=1/\rho$ ,  $a=\kappa$  (a "spring constant"), and find that  $\int (\rho u^2 + \kappa v^2)$  is conserved. We interpreted this as kinetic+potential energy.

Example: pressure waves in a fluid or gas. In this case, u=P (pressure),  $\mathbf{v}$  is a velocity, a=1/ $\rho$  ( $\rho$  is density), and b=K (bulk modulus: dP=-KdV/V, relating change in pressure dP to fractional change in volume dV/V). Again this gives a wave equation, with a conserved kinetic+potential energy  $\int (\rho |\mathbf{v}|^2 + P^2/K)$ .

Considered the case of Maxwell's equation in vacuum (which you already proved is anti-Hermitian in homework) and gave the corresponding energy density in the EM fields. Mentioned the case of Schrodinger's equation in quantum mechanics, where we only have one time derivative, and the conserved norm is interpreted as conservation of probability. The other cases in the notes are more complicated. MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 24

Discretization of the (1d scalar) wave equation: staggered grids and leap-frog schemes. Von Neumann and CFL analysis. Dispersion relation.

Discretization of the (1d scalar) wave equation, simplifying for now to an infinite domain (no boundaries) and constant coefficients (c=1). This corresponds to the equations  $\partial u/\partial t = \partial v/\partial x$  and  $\partial v/\partial t = \partial u/\partial x$ .

The obvious strategy is to make everything a center difference. First concentrating on the spatial discretization, showed that this means that u and v should be discretized on different grids: for integers m, we should discretize  $u(m\Delta x)\approx u_m$  and  $v([m+0.5]\Delta x)\approx v_{m+0.5}$ . That is, the u and v spatial grids are offset, or **staggered**, by  $\Delta x/2$ .

For discretizing in time, one strategy is to discretize u and v at the same timesteps  $n\Delta t$ . Center-differencing then leads to a Crank-Nicolson scheme, which can easily show to be unconditionally stable (albeit implicit) for anti-Hermitian spatial discretizations.

Alternatively, we can use an explicit **leap-frog** scheme in which u is discretized at times  $n\Delta t$  and v is discretized at times  $[n-0.5]\Delta t$ . Sketched out the corresponding staggered grids, difference equations, and leap-frog process.

Went through Von Neumann stability analysis of this leap-frog scheme, and derived the **dispersion relation**  $\omega(k)$  for **planewave** solutions  $e^{ik\Delta x \, m \, - \, i\omega\Delta t \, n}$ . Compared to dispersion relation  $\omega(k) = \pm c|k|$  of the analytical equation: matches for small k, but a large mismatch as k approaches  $\pi/\Delta x$ .

**Further reading:** Strang book, section 6.4 on the leapfrog scheme for the wave equation.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 25

**Traveling waves: D'Alembert's solution**. Considered the 1d scalar wave equation  $c^2 \partial^2 u/\partial x^2 = \partial^2 u/\partial t^2$  on an infinite domain with a constant coefficient c. Showed that any f(x) gives possible solutions  $u(x,t)=f(x\pm ct)$ . This is called D'Alembert's solution, and describes the function f(x) "moving" to the left or right with speed c. That is, wave equations have travelling solutions, and the constant c can be interpreted as the speed of these solutions. Adding a hard wall (Dirichlet boundary) is equivalent to looking for an odd solution  $f(x\pm ct)-f(-x\pm ct)$ , which gives an *inverted reflection* off the wall. (Neumann boundary conditions correspond to even solutions and give non-inverted reflections.) If we have two Dirichlet boundaries, as in a finite stretched string, then we obtain an infinite sequence of inverted reflections which we can write as an infinite series.

Given these solutions, it is attractive to try to write any solution u(x,t) as a superposition of D'Alembert solutions. We can do this if we pick a convenient basis of f(x) functions, and the most convenient basis will turn out to be  $f(x)=e^{ikx}$  for real k: this leads to Fourier transforms, which we will return to later. In particlar, we then obtain **planewave** solutions  $e^{i(kx\pm\omega t)}$  where  $\omega=\pm ck$  (the *dispersion relation*).  $2\pi/k$  is a spatial wavelength  $\lambda$ , and  $\omega/2\pi$  is a frequency f, and from this we find that  $\lambda f=c$ , a relation you may have seen before.

There is something suspiciously unphysical about D'Alembert solutions: they travel *without changing shape*, even if f(x) is a very non-smooth shape like a triangle wave. Real waves on strings, etcetera, don't seem to do this. The problem is that real wave equations incorporate a complication that we have not yet considered: the speed c, in reality *depends on*  $\omega$ , an effect called dispersion, so that different frequency components travel at different speeds and the solution will distort as it travels. Physically, it turns out that this comes down to the fact that materials do not respond instaneously to stimuli, which is mathematically expressed by the fact that the Fourier transformation of the frequency-domain equation  $\partial^2 u/\partial x^2 = -\omega^2 c(\& omega)^{-2}u$  Fourier transform to  $\partial^2 u/\partial x^2 = \partial^2 u/\partial t^2 * (some function of time) where "*" is a convolution operation. We will come back to this later.$ 

Went over handout, first five pages.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 28

Began discussing general topic of waveguides. Defined waveguides: a wave-equation system that is *invariant* (or periodic) in at least one direction (say y), and has some structure to *confine* waves in one or more of the other "transverse" directions. A simple example of a waveguide (although not the only example) consists of waves confined in a hollow pipe (either sound waves or electromagnetic waves, where the latter are confined in metal pipe). Began with a simple 2d example: a waveguide for a scalar wave equation that is invariant in y and confines waves with "hard walls" (Dirichlet boundaries at x=0 and x=L) in the x direction. In such a wave equation, or *any wave equation that is invariant in y*, the solutions are separable in the invariant direction, and the eigenfunctions  $u(x,y)e^{-i\omega t}$  can be written in the form  $u_k(x)e^{i(ky-\omega t)}$  for some function  $u_k$  and some eigenvalues  $\omega(k)$ . In this case, plugged the separable form into the scalar wave equation and immediately obtained a 1d equation for  $u_k$ :  $u_k$ "- $k^2u_k$ =- $\omega^2u_k$ , which we solved to find  $u_k$ =sin( $n\pi x/L$ ) for  $\omega^2$ = $k^2$ +( $n\pi/L$ )<sup>2</sup>. Plotted the dispersion relation  $\omega(k)$  for a few *guided modes* (different integers n), and discussed what the corresponding modes look like.

Commented on the k goes to 0 and infinity limits where the group velocity goes to 0 and 1 (c), respectively. As k goes to zero, the group velocity goes to zero but the phase velocity diverges; discuss what this means.

Discussed superposition of modes: explain that if we superimpose say the n=1 and n=2 modes at the same  $\omega$  and nearby k, what we get is a "zig-zagging" asymmetrical solution that bounces back and forth between the walls at intervals  $\pi/\Delta k$ . This is what we might get if we add an off-center source term, for example.

Discussed the existence of a low- $\omega$  *cutoff* for each mode and its implications. As we increase the frequency of a source term, it excites more and more modes (a quantum analogue of this phenomenon is quantized conductance in nanowires!). Moreover, by Taylor-expanding the dispersion relation near the cutoff as a quadratic function, we can solve for the solutions slightly *below* cutoff, and see that they must have *imaginary* k and hence be *exponentially decaying/growing*. These are called **evanescent modes** (as opposed to propagating modes for real k), and can only be excited by a localized source or some break or boundary in the waveguide (e.g. an endfacet); they are what you get if you try to vibrate a membrane below cutoff!

**Waveguide movies:** for a 2d waveguide of width L, put an off-center source at one end that turns on around t=0 to a sinusoidal forcing of frequency  $f=\omega \cdot L/2\pi c$ , and showed some movies of computer simulations. First, considered a waveguide with hard ("metal") walls like the previous example; depending on how f relates to the mode cutoffs (at 0.5, 1.0, 1.5, ...), we get very different results. Then, considered a source in an infinite homogeneous (c=1) medium ("vacuum"), which just gives waves radiating outwards in every direction. Finally, considered a medium that is c=1 in a width L, and outside is c=2: this gives waveguiding by a very different mechanism, "total internal reflection".

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 29

Went through the 2d example from the previous lecture analytically; see handout for notes. In general, we need both propagating and evanescent waves in order to find the solution when we have something that breaks translational symmetry (such as a localized source).

**Waveguide modes, in general**: In a waveguide, or any system that is invariant along one dimension (say z), we can always find *separable eigenfunctions* of  $\hat{A}u=\partial^2 u/\partial t^2$ . That is, we look for solutions of the form  $u_k(x,y)$   $e^{i(kz-\omega t)}$ , which are eigenfunctions of  $\hat{A}$  with eigenvalue  $-\omega^2$ . These are solutions to the full problem, with *each value of k giving us different solutions*  $u_k$  and  $\omega(k)$ . We can then build any arbitrary solution  $u_k$  via a superposition of these (much like a Fourier transform, writing any z dependence as a sum of  $e^{ikz}$  sinusoids). For each k, the function  $u_k(x,y)$  (which does not depend on  $u_k$ 0) satisfies  $\hat{A}e^{ikz}u_k$ 1- $u_k$ 2- $u_k$ 3. From which we derive the **reduced eigenproblem**  $\hat{A}_k u_k$ 2- $u_k$ 3. Where  $\hat{A}_k$ 4- $u_k$ 5 is an operator with no z derivatives and no z dependence: we have reduced the problem to one fewer spatial dimension.

Showed that  $\hat{A}_k$  is self-adjoint and definite if  $\hat{A}$  is.

A **waveguide** is any system in at which at least *some* of these modes  $u_k$  are *localized* (or *guided*): in particular, we usually require them to be at least square-integrable (finite-norm) over the reduced (x,y) domain (this is always true if the reduced domain is finite as for our "tube" waveguide examples). (In practice, guided modes usually decay at least exponentially fast in |(x,y)| outside of some compact region.)

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 30

Guidance, reflection, and refraction at interfaces between regions with different wave speeds c:

Started with the solutions of the scalar wave equation in infinite space with a constant coefficient (speed) c: plane waves  $\mathbf{u}(\mathbf{x},t)=e^{\mathrm{i}(\mathbf{k},\mathbf{x}-\omega t)}$ , satisfying  $\omega=c|\mathbf{k}|$ , where  $\mathbf{k}$  is the *wavevector* and indicates the propagation direction and the spatial wavelength  $2\pi/|\mathbf{k}|$ .

Now, considere what happens when a plane wave in a region with speed  $c_1$  is incident upon an interface at x=0 to another region with speed  $c_2$ . In general, we expect a transmitted wave and a reflected wave. At x=0, we will have some continuity conditions depending on the specifics of the wave equation (e.g. u continuous), and these continuity conditions must be *satisfied at all y and at all t*. The only way to satisfy the same continuity conditions at all y is for all of the waves to be oscillating at the same speed in the y direction at x=0, i.e. that they must all have the same  $k_y$ , and the only way to satisfy the same continuity conditions at all t is for the waves to be oscillating at the same  $\omega$ . Writing  $k_y=|\mathbf{k}|\sin\theta=(\omega/c)\sin\theta$ , we immediately obtain two results. First, the reflected angle is the same as the incident angle. Second,  $(1/c_1)\sin\theta_1=(1/c_2)\sin\theta_2$ . In optics, these are known as the **Law of Equal Angles** and **Snell's Law** respectively, but they are generic to *all* wave equations.

If  $c_1 < c_2$ , then showed that there are no real  $\theta_2$  solutions for a sufficiently large angle  $\theta_1$ . In optics, you probably learned this as **total internal reflection**, but it is general to any wave equation. Then, if we have two interfaces, with  $c_1 < c_2$  sandwiched between two semi-infinite  $c_2$  regions, we can obtain *guided modes* that are trapped mostly in  $c_1$ , and can crudely be thought of as "rays" bouncing back and forth in  $c_1$ , "totally internally reflected". More carefully, showed that "totally internally reflected" solutions correspond to **exponentially decaying solutions** in  $c_2$ , which are called *evanescent waves*.

To obtain a more general picture, we imagine writing down the dispersion relation  $\omega(k)$  for such a waveguide, looking as usual for separable eigenfunctions  $u_k(x)e^{i(ky-\omega t)}$ . Far from the  $c_1$  region, the solutions must just be planewaves propagating in  $c_2$ , with  $\omega=c_2|\mathbf{k}|=c_2k$  sec $\theta$ , since k is just the y component of  $\mathbf{k}$ , where  $\theta$  is the angle with the y axis. Plotting all of these solutions forms a continuous **cone** covering  $\omega(k)\geq c_2k$  (called the "light cone" in optics): this cone is *all the wave solutions that propagate in*  $c_2$ . The light cone for the  $c_1$  region has a lower slope  $(c_1)$ , and hence the  $c_1$  region will introduce new *guided* solutions below the  $c_2$  cone which are evanescent in  $c_2$ . In the next lecture, I will argue that a finite-thickness  $c_1$  region leads to a finite number of guided modes below the  $c_2$  cone, and give numerical examples.

**Further reading:** You can find many explanations of Snell's law, total internal reflection, etcetera, online. For a treatment in the context of the scalar wave equation, see e.g. *Haberman*, *Elementary Applied Partial Differential Equations* section 4.6. For a treatment in Maxwell's equations, see any elementary electromagnetism book; our book (chapter 3) has an abstract approach with a light cone etcetera mirroring the one here.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 31

Went through numerical examples of total internal reflection, i.e. guiding in a "slow" region; see IJulia notebook above.

Went through analytical proof, based on the min–max theorem, that under very general conditions any regions with a smaller speed c will lead to guided-wave (localized) solutions. See notes above.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 32

Discussed how "absorbing boundaries" are implemented in the frequency domain via complex coordinate stretching, leading to the idea of **perfectly matched layers** (PML); see the notes. Showed some animations of wave propagation showing the effect of the boundaries and the impact of PML.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 33

Perturbation theory: perturbations for self-adjoint eigenproblems, with application to computing losses in dissipative (slightly non-Hermitian) wave problems. Connection to Hellman-Feynman theorm. Showed that group velocity  $d\omega/dk$  can be evaluated via Hellman-Feynman, and yields a ratio of energy flux to energy density: an "energy velocity".

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 34

Began to introduce a new topic, **finite element methods**.

Set up the two key components of finite element methods (FEM): the basis and the discretization of the equations. FEM generalizes finite difference methods to nonuniform meshes, meshes that can conform to boundaries/interfaces, and gives more freedom in having different equations/discretizations/bases in different regions. A typical 2d mesh is composed of triangles (possibly with curved edges), in 3d tetrahedra, and in 1d just line segments, although other polyhedra are also possible. The vertices of the triangles/tetrahedra/etc are called *nodes* of the mesh.

First, we write unknown functions u(x) (in some Sobolev space V) approximately as  $\tilde{u}(x)$  (in an N-dimensional space  $\tilde{V}$ ) in terms of N basis functions  $b_n(x)$  (spanning  $\tilde{V}$ ) multiplied by unknown coefficients  $u_n$ , defined with respect to the mesh. Typically, the  $b_n(x)$  are simple (low degree) polynomial functions defined piecewise in each element, with some continuity constraints.

For example, gave the example of "tent" functions (1st order elements) where  $b_n(x)$  is 1 at node n, 0 at other nodes, and linearly interpolated between node n and adjacent nodes. For this basis,  $u_n$  is just the value of  $\tilde{u}(x)$  at the nodes. In the 1d case this just corresponds to linearly interpolating  $\tilde{u}(x)$  between each pair of nodes.

Given a basis, we need to construct a discretization of  $\hat{A}u=f$ , and the typical way to do this is a **Galerkin** method. Recall that, in the distributional/weak sense, the exact solution satisfies  $\langle \phi, \hat{A}u \rangle = \langle \phi, f \rangle$  for test functions  $\phi$ . (Typically, we phrase the problem in terms of the **bilinear form**  $\langle \phi, u \rangle_A = \langle \phi, \hat{A}u \rangle$ , where we usually integrate by parts so that half of the derivatives fall on  $\phi$ . This avoids the need for explicit delta functions. e.g. for  $\hat{A}=-\nabla^2$  with Dirichlet boundaries we get  $\langle \phi, u \rangle_A = \langle \nabla \phi, \nabla u \rangle$ .) Here, we need to get just N equations, so we will do this for only N test functions  $\phi$ , and in particular the Galerkin approach is to choose  $\phi=b_m$  for m from 1 to N. Showed that this gives a matrix equation  $A\mathbf{u}=\mathbf{f}$ , where the entries of  $\mathbf{u}$  are the unknown coefficients  $\mathbf{u}_n$ , with:

- The entries of **f** are  $f_n = \langle b_n, f \rangle$
- The entries of A are  $A_{mn} = \langle b_m, b_n \rangle_A$ .

For the integrals of  $A_{mn}$  to exist, some continuity constraints must be imposed on the basis. For example, with  $\hat{A}=\nabla^2$  or similar 2nd-derivative operators, we only need  $b_n$  to be continuous and piecewise differentiable.

Another way of looking at the Galerkin approach is that we require the *residual*  $\tilde{A}\tilde{u}$ -f to be orthogonal to  $b_m$  (i.e. the residual is orthogonal to  $\tilde{V}$ ). As we increase N, and the basis approaches a complete basis, the intuition is that this forces the error to go to zero (in the distributional/weak sense). Later, we will outline a more careful convergence proof.

For  $\hat{A}$  self-adjoint and positive-definite, the bilinear form  $\langle u,v \rangle_A$  is a proper inner product and  $\|u\|_A = \langle u,u \rangle_A^{1/2}$  is a norm. From  $\langle b_m,\tilde{u} \rangle_A = \langle b_m,f \rangle = \langle b_m,u \rangle_A$  where u is the exact solution, we

obtain  $\langle b_m, \tilde{u}-u \rangle_A = 0$ . That is, the error  $\tilde{u}$ -u is orthogonal to  $\tilde{V}$  in the  $\langle \cdot, \cdot \rangle_A$  sense. It follows that  $\tilde{u}$  is the *orthogonal projection* of u onto  $\tilde{V}$ :  $\tilde{u}$  minimizes  $\|\tilde{u}-u\|_A$  over all  $\tilde{u}$  in  $\tilde{V}$ . This is a key ingredient of convergence proofs.

Showed that Galerkin discretizations preserve some nice properties of  $\hat{A}$ : if  $\hat{A}$  is self-adjoint, then A is Hermitian; if  $\hat{A}$  is positive-definite (or negative-definite, etcetera) then A is positive-definite (or negative-definite, etcetera).

**Further reading:** Textbook, section 3.6. There are lots of books on finite-element methods. These Finite Element Analysis Course Notes by Joseph E. Flaherty at RPI are pretty helpful.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 35

Evaluated the Galerkin discretization of  $\hat{A}=d^2/dx^2$  with tent basis functions. Showed that, for a uniform grid, we recover our center-difference finite-difference matrix. For a nonuniform grid, we get a generalization. Analyzed the accuracy to show that the generalization is still second-order accurate if the resolution is changing "continuously" (i.e. if it is approaching a continuously varying resolution as N increases), but is only first-order accurate if the resolution jumps. This means that grid-generation methods for finite elements try to produce meshes where the elements change in size smoothly.

On the other hand, if we define accuracy in an "average" sense (e.g. the L2 norm of the error), then it turns out that we always have second-order accuracy even if there are jumps in resolution (although these may have large localized contributions to the error). For positive-definite operators Â, we will use the fact (from last lecture) that Galerkin methods minimize an Â-weighted norm of the error in ũ in order to flesh out a more careful convergence analysis.

Discussed some of the general tradeoffs of complexity in finite-element vs. finite-difference methods: more sophistication is not always better, especially since computer time is usually much cheaper than programmer time.

**Further reading:** See the notes on finite-element methods from 16.920J/2.097J/6.339J. Some nice free/open-source software packages for finite-element calculations are FEniCS, deal.II, and libMesh.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 36

Sketch of convergence proof for the finite-element method based on bounding the error  $\|\tilde{\mathbf{u}} - \mathbf{u}\|_{A}$  via the min-max theorem for positive-definite  $\hat{\mathbf{A}}$  (coercive bilinear forms). Then showed that the latter is minimized since  $\tilde{\mathbf{u}}$  is an orthogonal projection, and finally bounded  $\|\tilde{\mathbf{u}} - \mathbf{u}\|_{A}$  above by  $\|\&\text{vtilde}; -\mathbf{u}\|_{A}$  where &vtilde; is a simple Lagrange interpolation of  $\mathbf{u}$ . (Unfortunately, the error estimate produced by this procedure is a bit too conservative: for first-order elements, this gives a first-order upper bound, when in fact the error is typically second-order.)

Boundary conditions and the finite-element method: essential vs. natural boundary conditions. Dirichlet is essential (imposed by the function space, or via explicit constraint equations), while Neumann is natural (imposed by the weak form in the absence of an essential boundary condition).

**Further reading:** Lectures 2 and 7 of these course notes by Joseph Flaherty at RPI were pretty readable regarding convergence (see, in particular, section 2.6 of lecture 2). The book Understanding and Implementing the Finite Element Method by Mark S. Gockenbach has a nice discussion of boundary conditions in chapter 2.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 37

Discussed what finite-element software looks like nowadays, via some nice free/open-source software packages for finite-element calculations are FEniCS, Firedrake, deal.II, and libMesh. In particular, went through the FEniCS, Firedrake, and libmesh Poisson-equation tutorials (from their web sites).

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 38

Discussed the impact of a different kind of algebraic structure on the solution of linear PDEs: symmetry. Looked at the specific examples of mirror symmetries, the symmetries of a square, and translational symmetry. Showed that a symmetry corresponds to a symmetry operator that commutes with  $\hat{A}$  and preserves the boundary conditions, and allows us to find simultaneous eigenfunctions of  $\hat{A}$  and the symmetry operator. For mirror symmetries, this leads to even/odd solutions, and for translational symmetry this leads to separable solutions with exp(ikz) exponentials in the invariant directions.

However, for more complicated symmetry groups with multiple "interacting" operations, looking for simultaneous eigenfunction tells us the truth but not the whole truth. To see how the symmetry operations relate to one another, we use group representation theory. Defined representations of a group and gave a few examples to suggest how they relate to eigenfunctions, although no proofs were given.

**Further reading:** The general subject of symmetry and linear PDEs leads to group theory (for the symmetry group) and group representation theory (to generalize the symmetry "eigenfunctions" to non-commutative groups). For a simple introduction similar to the one in class but applied to Maxwell's equations, see e.g. chapter 3 of our book. For a more complete treatment, see any book on the applications of group theory to physics; my favorite is this book by Inui but it is out of print; a classic with cheap reprints is this book by Tinkham. See this summary of the key definitions and theorems in representation theory for understanding the consequences of representations for eigenfunctions and linear PDEs in general.

MIT OpenCourseWare http://ocw.mit.edu

18.303 Linear Partial Differential Equations: Analysis and Numerics Fall 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.
