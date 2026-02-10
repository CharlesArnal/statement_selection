# MATH 18.152 COURSE NOTES - CLASS MEETING # 1

# 18.152 Introduction to PDEs, Fall 2011

# Class Meeting # 1: Introduction to PDEs

Professor: Jared Speck

### 1. What is a PDE?

We will be studying functions  $u = u(x^1, x^2, \dots, x^n)$  and their partial derivatives. Here  $x^1, x^2, \dots, x^n$  are standard Cartesian coordinates on  $\mathbb{R}^n$ . We sometimes use the alternate notation u(x,y), u(x,y,z), etc. We also write e.g.  $u(r, \theta, \phi)$  for spherical coordinates on  $\mathbb{R}^3$ , etc. We sometimes also have a "time" coordinate t, in which case  $t, x^1, \dots, x^n$  denotes standard Cartesian coordinates on  $\mathbb{R}^{1+n}$ . We also use the alternate notation  $x^0 \stackrel{\text{def}}{=} t$ .

We use lots of different notation for partial derivatives:

(1.0.1a) 
$$\frac{\partial}{\partial x^i} u = u_{x^i} = \partial_i u, \qquad 1 \le i \le n,$$

(1.0.1b) 
$$\frac{\partial^2 u}{\partial x^i \partial x^j} = \frac{\partial}{\partial x^i} \frac{\partial}{\partial x^j} u = u_{x^i x^j} = \partial_i \partial_j u, \qquad 1 \le i, j \le n.$$

If i = j, then we sometimes abbreviate  $\partial_i \partial_j u \stackrel{\text{def}}{=} \partial_i^2 u$ . If u is a function of (x, y), then we also write  $u_x = \frac{\partial}{\partial x} u$ , etc.

**Definition 1.0.1.** A PDE in a single unknown u is an equation involving u and its partial derivatives. All such equations can be written as

$$(1.0.2) F(u, u_{x^1}, \dots, u_{x^n}, u_{x^1x^1}, \dots, u_{x^{i_1} \dots x^{i_N}}, x^1, x^2, \dots, x^n) = 0, i_1, \dots, i_N \in \{1, 2, \dots, n\}$$
 for some function  $F$ .

Here N is called the *order* of the PDE. N is the maximum number of derivatives appearing in the equation.

**Example 1.0.1.** u = u(t, x)

$$(1.0.3) -\partial_t^2 u + (1 + \cos u)\partial_x^3 u = 0$$

is a third-order nonlinear PDE.

**Example 1.0.2.** u = u(t, x)

$$(1.0.4) -\partial_t^2 u + 2\partial_x^2 u + u = t$$

is a second-order linear PDE.

We say that (1.0.4) is a constant coefficient linear PDE because u and its derivatives appear linearly (i.e. first power only) and are multiplied only by constants.

**Example 1.0.3.** u = u(t, x)

$$\partial_t u + 2(1+x^2)\partial_x^3 u + u = t$$

is a third-order linear PDE.

We say that (1.0.5) is a variable coefficient linear PDE because u and its derivatives appear linearly (i.e. first power only) and are multiplied only by functions of the coordinates (t, x).

**Example 1.0.4.** u = u(t, x), v = v(t, x)

$$(1.0.6a) \partial_t u + 2x \partial_x v = \sin(x^2),$$

$$(1.0.6b) \partial_t v - x^2 \partial_x u - 0$$

is a system of PDEs in the unknowns u, v.

# 2. The Goals of PDE (and of this course)

Suppose that we are interested in some physical system. A very fundamental question is:

• Which PDEs are good models for the system?

A major goal of *modeling* is to answer this question. There is no general recipe for answering it! In practice, good models are often the end result of confrontations between experimental data and theory. In this course, we will discuss some important physical systems and the PDEs that are commonly used to model them.

Now let's assume that we have a PDE that we believe is a good model for our system of interest. Then most of the time, the primary goals of PDE are to answer questions such as the following:

- (1) Does the PDE have any solutions? (Some PDEs have NO SOLUTIONS whatsoever!!)
- (2) What kind of "data" do we need to specify in order to solve the PDE?
- (3) Are the solutions corresponding to the given data unique?
- (4) What are the basic qualitative properties of the solution?
- (5) Does the solution contain singularities? If so, what is their nature?
- (6) What happens if we slightly vary the data? Does the solution then also vary only slightly?
- (7) What kinds of quantitative estimates can be derived for the solutions?
- (8) How can we define the size (i.e., "the norm") of a solution in way that is useful for the problem at hand?

### 3. Physical Examples

It is difficult to exaggerate how prevalent PDEs are. We will discuss some important physically motivated examples throughout this course. Here is a first look.

- $-\partial_r^2 u + \partial_r^2 u = 0$  wave equation, second-order, linear, homogeneous

- $-\partial_t u + \partial_x^2 u = 0$  heat equation, second-order, linear, homogeneous  $\partial_x^2 u + \partial_y^2 u + \partial_z^2 u = 0$  Laplace's equation, second-order, linear, homogeneous  $\partial_x^2 u + \partial_y^2 u + \partial_z^2 u = f(x, y, z)$  Poisson's equation with source function f, second-order, linear, inhomogeneous (unless f = 0)
- $i\partial_t u + \partial_r^2 u = 0$  Schrödinger's equation, second-order, linear, homogeneous
- $u_t + u_x = 0$ , transport equation, first-order, linear, homogeneous
- $u_t + uu_x = 0$ , Burger's equation, first-order, nonlinear, homogeneous

 $\mathbf{E} = (E_1(x, y, z), E_2(x, y, z), E_3(x, y, z)), \mathbf{B} = (B_1(x, y, z), B_2(x, y, z), B_3(x, y, z))$  are vectors in

(3.0.7a) 
$$\partial_t \mathbf{E} - \nabla \times \mathbf{B} = 0,$$
  $\nabla \cdot \mathbf{E} = 0,$ 

(3.0.7b) 
$$\partial_t \mathbf{B} + \nabla \times \mathbf{E} = 0,$$
  $\nabla \cdot \mathbf{B} = 0$ 

"Maxwell's equations" in a vacuum (i.e., matter-free spacetime), first-order, linear, homogeneous.

#### 4. Linear PDEs

Before we dive into a specific model, let's discuss a distinguished class of PDEs that are relatively easy to study. The PDEs of interest are called *linear PDEs*. Most of this course will concern linear PDEs.

**Definition 4.0.2.** A linear differential operator  $\mathcal{L}$  is a differential operator such that

$$\mathcal{L}(au + bv) = a\mathcal{L}u + b\mathcal{L}v$$

for all constants  $a, b \in \mathbb{R}$  and all functions u, v.

**Remark 4.0.1.** The notation was introduced out of convenience and laziness. The definition is closely connected to the superposition principle.

**Example 4.0.5.**  $\mathcal{L} \stackrel{\text{def}}{=} -\partial_t^2 + (t^2 - x^2)\partial_x^2$  is a linear operator:  $\mathcal{L}u = -\partial_t^2 u + (t^2 - x^2)\partial_x^2 u$ 

**Example 4.0.6.** 
$$u = u(x, y)$$
,  $\mathcal{L}u = \partial_x^2 u + u^2 \partial_y^2 u$  does **NOT** define a linear operator:  $\mathcal{L}(u+v) = \partial_x^2 (u+v) + (u+v)^2 \partial_y^2 (u+v) \neq \partial_x^2 u + u^2 \partial_y^2 u + \partial_x^2 v + v^2 \partial_y^2 v = \mathcal{L}u + \mathcal{L}v$ 

**Definition 4.0.3.** A PDE is *linear* if it can be written as

$$\mathcal{L}u = f(x^1, \cdots, x^n)$$

for some linear operator  $\mathcal{L}$  and some function f of the coordinates.

**Definition 4.0.4.** If f = 0, then we say that the PDE is homogeneous. Otherwise, we say that it is inhomogeneous.

Example 4.0.7. u = u(t, x)

$$(4.0.10) \partial_t u - (1 + \cos t)\partial_x^2 u = tx$$

is a linear PDE.

Here is an incredibly useful property of linear PDEs.

**Proposition 4.0.1** (Superposition principle). If  $u_1, \dots, u_M$  are solutions to the linear PDE

$$\mathcal{L}u = 0,$$

and  $c_1, \dots, c_M \in \mathbb{R}$ , then  $\sum_{i=1}^M c_i u_i$  is also a solution.


Proof.

(4.0.12) 
$$\mathcal{L}\sum_{i=1}^{M} c_{i}u_{i} = \sum_{i=1}^{M} c_{i} \underbrace{\mathcal{L}u_{i}}^{=0} = 0.$$

**Remark 4.0.2.** This shows that the set of all solutions to  $\mathcal{L}u = 0$  is a *vector space* when  $\mathcal{L}$  is linear.

As we will see in the next proposition, inhomogeneous and homogeneous linear PDEs are closely related.

Proposition 4.0.2 (Relationship between the inhomogeneous and homogeneous linear PDE solutions). Let  $S_h$  be the set of all solutions to the homogeneous linear PDE

$$\mathcal{L}u = 0,$$

and let  $u_I$  be a "fixed" solution to the inhomogeneous linear PDE

$$\mathcal{L}u = f(x^1, \cdots, x^n).$$

Then the set  $S_I$  of all solutions to (4.0.14) is the translation of  $S_H$  by  $u_I : S_I = \{u_I + u_H \mid u_H \in S_H\}$ .

Proof. Assume that  $\mathcal{L}u_I = f$ , and let w be any other solution to (4.0.14), i.e.,  $\mathcal{L}w = f$ . Then  $\mathcal{L}(w - u_I) = f - f = 0$ , so that  $w - u_I \in S_H$ . Thus,  $w = u_I + \underbrace{(w - u_I)}_{\text{belongs to } S_H}$ , and so  $w \in S_I$ 

by definition. On the other hand, if  $w \in S_I$ , then  $w = u_I + u_H$  for some  $u_H \in S_H$ . Therefore,  $\mathcal{L}w = \mathcal{L}(u_I + u_H) = \mathcal{L}u_I + \mathcal{L}u_H = f + 0 = f$ . Thus, w is a solution to (4.0.14).

#### 5. How to solve PDEs

- There is no general recipe that works for all PDEs! We will develop some tools that will enable us to analyze some important classes of PDEs.
- Usually, we don't have explicit formulas for the solutions to the PDEs we are interested in! Instead, we are forced to understand and estimate the solutions without having explicit formulas.

The two things that you typically need to study a PDE:

- You need to know the PDE.
- You need some "data."

# 6. Some simple PDEs that we can easily solve

6.1. Constant coefficient transport equations. Consider the first-order linear transport equation

(6.1.1) 
$$a\partial_x u(x,y) + b\partial_y u(x,y) = 0,$$

where  $a, b \in \mathbb{R}$ . Let's try to solve this PDE by reasoning geometrically. Geometrically, this equation says that  $\nabla u \cdot v = 0$ , where  $\nabla u \stackrel{\text{def}}{=} (\partial_x u, \partial_y u)$  and v is the vector  $(a, b) \in \mathbb{R}^2$ . Thus, the derivative of

u in the direction (a,b) is 0, which implies that u is constant along lines pointing in the direction of (a,b). The slope of such a line is  $\frac{b}{a}$ . Therefore, every such line can be described as the set of solutions to bx - ay = c, where  $c \in \mathbb{R}$ . Since u is constant along these lines, we know that u is a "function that depends only on the line c." Therefore u(x,y) = f(c) = f(bx - ay) for some function f.

In order to provide more details about u, we would need to prescribe some "data." For example, if it is known that  $u(x,0) = x^2$ , then  $x^2 = f(bx)$ . Thus,  $f(c) = b^{-2}c^2$ , and  $u(x,y) = (x - b^{-1}ay)^2$ . In the future, we will discuss the kinds of data that can be specified in more detail. As we will see, the type of data will depend on the type of PDE.

6.2. Solving a variable coefficient transport equations. With only a bit of additional effort, the procedure from Section 6.1 can be extended to cover the case where the coefficients are prespecified functions of x, y. Let's consider the following example:

$$(6.2.1) y\partial_x u + x\partial_y u = 0.$$

Let P denote a point P = (x, y), and let V denote the vector V = (y, x). Using vector calculus notation, (6.2.1) can be written as  $\nabla u(P) \cdot V = 0$ , i.e., the derivative of u at P in the direction of V is 0. Thus, equation (6.2.1) implies that u is constant along the curve  $\mathcal{C}$  passing through P that points in the same direction as V. This vector can be viewed as a line segment with slope  $\frac{x}{y}$ . Therefore, if the curve  $\mathcal{C}$  is parameterized by  $x \to (x, y(x))$  (where we are viewing y as a function of x along  $\mathcal{C}$ ) then  $\mathcal{C}$  has slope  $\frac{dy}{dx}$ , and y is therefore a solution to the following ODE:

$$\frac{dy}{dx} = \frac{x}{y}.$$

We can use the following steps to integrate (6.2.2), which you might have learned in an ODE class:

(6.2.3) 
$$(6.2.2) \implies y \frac{dy}{dx} = x \implies \frac{1}{2} \frac{d}{dx} (y^2) = x$$

$$(6.2.4) \qquad \Longrightarrow \frac{y^2}{2} = \frac{x^2}{2} + c, \ c = \text{constant}.$$

Thus, the curve C is a hyperbola of the form  $\{y^2 - x^2 = c\}$ . These curves are called *characteristics*. We conclude that u is constant along the hyperbolas  $\{y^2 - x^2 = c\}$ , which implies that  $u(x,y) = f(x^2 - y^2)$  for some function f(c).

We can carry out the same procedure for a PDE of the form

$$(6.2.5) a(x,y)\partial_x u + b(x,y)\partial_y u = 0,$$

as long as we can figure out how to integrate the ODE

(6.2.6) 
$$\frac{dy}{dx} = \frac{b(x,y)}{a(x,y)}.$$

### 7. Some basic analytical notions and tools

We now discuss a few ideas from analysis that will appear repeatedly throughout the course.

7.1. **Norms.** In PDE, there are many different ways to measure the "size" of a function f. These measures are called *norms*. Here is a simple, but useful norm that will appear throughout this course.

**Definition 7.1.1** ( $C^k$  norms). Let f be a function defined on a domain  $\Omega \subset \mathbb{R}$ . Then for any integer  $k \geq 0$ , we define the  $C^k$  norm of f on  $\Omega$  by

(7.1.1) 
$$||f||_{C^k(\Omega)} \stackrel{\text{def}}{=} \sum_{a=0}^k \sup_{x \in \Omega} |f^{(a)}(x)|,$$

where  $f^{(a)}(x)$  is the  $a^{th}$  order derivative of f(x). We often omit the symbol  $\Omega$  when  $\Omega = \mathbb{R}$ .

### Example 7.1.1.

such as

$$(7.1.2)$$

The same notation is used in the case that  $\Omega \subset \mathbb{R}^n$ , but in this case, we now sum over all partial derivatives of order  $\leq k$ . For example, if  $\Omega \subset \mathbb{R}^2$ , then  $||f||_{C^2(\Omega)} \stackrel{\text{def}}{=} \sup_{(x,y)\in\Omega} |f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f(x,y)| + \sup_{(x,y)\in\Omega} |\partial_x f$ 

(7.1.3) 
$$||f||_{C^{1,2}} \stackrel{\text{def}}{=} \sum_{a=0}^{1} \sup_{(t,x)\in\mathbb{R}^2} |\partial_t^a f(t,x)| + \sum_{a=1}^{2} \sup_{(t,x)\in\mathbb{R}^2} |\partial_x^a f(t,x)|.$$

Above, the "1" in  $C^{1,2}$  refers to the t coordinate, while the "2" refers to the x coordinate.

The next definition provides a very important example of another class of norms that are prevalent in PDE theory.

**Definition 7.1.2** ( $L^p$  norms). Let  $1 \le p < \infty$  be a number, and let f be a function defined on a domain  $\Omega \subset \mathbb{R}^n$ . We define the  $L^p$  norm of f by

(7.1.4) 
$$||f||_{L^p(\Omega)} \stackrel{\text{def}}{=} \left( \int_{\Omega} |f(x)|^p d^n x \right)^{1/p}.$$

We often write just  $L^p$  instead of  $L^p(\mathbb{R}^n)$ .

 $\|\cdot\|_{L^p(\Omega)}$  has all the properties of a norm:

- Non-negativity:  $||f||_{L^p(\Omega)} \ge 0$ ,  $||f||_{L^p(\Omega)} = 0 \iff f(x) = 0$  almost everywhere
- Scaling:  $\|\lambda f\|_{L^p(\Omega)} = |\lambda| \|f\|_{L^p(\Omega)}$
- Triangle inequality:  $||f+g||_{L^p(\Omega)} \leq ||f||_{L^p(\Omega)} + ||g||_{L^p(\Omega)}$

Similarly,  $\|\cdot\|_{C^k(\Omega)}$  also has all the properties of a norm. All of these properties are very easy to show except for the last one in the case of  $\|\cdot\|_{L^p(\Omega)}$ . You will study the very important case p=2 in detail in your homework.

<sup>&</sup>lt;sup>1</sup> "Almost everywhere" is a term that would be precisely defined in a course on measure theory.

7.2. The divergence theorem. A lot of PDE results are derived using integration by parts (sometimes very fancy versions of it), which provides us with *integral identities*. This will become more apparent as the course progresses. Let's recall a very important version of integration by parts from vector calculus: the divergence theorem. We first need to recall the notion of a vectorfield on  $\mathbb{R}^n$ .

**Definition 7.2.1** (Vectorfield). Recall that a vectorfield  $\mathbf{F}$  on  $\Omega \subset \mathbb{R}^n$  is an  $\mathbb{R}^n$ -valued (i.e. vector-valued) function defined on  $\Omega$ . That is,

(7.2.1) 
$$\mathbf{F}: \Omega \to \mathbb{R}^n,$$
$$\mathbf{F}(x^1, \dots, x^n) = \left(F^1(x^1, \dots, x^n), \dots, F^n(x^1, \dots, x^n)\right),$$

where each of the  $F^i$  are scalar-valued functions on  $\mathbb{R}^n$ .

We also need to recall the definition of the divergence operator, which is a differential operator that acts on vectorfields.

**Definition 7.2.2** (Divergence). Recall that  $\nabla \cdot \mathbf{F}$ , the divergence of  $\mathbf{F}$ , is the scalar-valued function on  $\mathbb{R}^n$  defined by

(7.2.2) 
$$\nabla \cdot \mathbf{F} \stackrel{\text{def}}{=} \sum_{i=1}^{n} \partial_{i} F^{i}.$$

We are now ready to recall the divergence theorem.

**Theorem 7.1** (Divergence Theorem). Let  $\Omega \subset \mathbb{R}^3$  be a domain<sup>2</sup> with a boundary that we denote by  $\partial\Omega$ . Then the following formula holds:

(7.2.3) 
$$\int_{\Omega} \nabla \cdot \mathbf{F}(x, y, z) \, dx dy dz = \int_{\partial \Omega} \mathbf{F}(\sigma) \cdot \hat{\mathbf{N}}(\sigma) \, d\sigma.$$

Above,  $\hat{\mathbf{N}}(\sigma)$  is the **unit outward** normal vector to  $\partial\Omega$ , and  $d\sigma$  is the surface measure induced on  $\partial\Omega$ . Recall that if  $\partial\Omega \subset \mathbb{R}^3$  can locally be described as the graph of a function  $\phi(x,y)$  (e.g.,  $\partial\Omega = \{(x,y,z) \mid z = \phi(x,y)\}$ ), then

(7.2.4) 
$$d\sigma = \sqrt{1 + |\nabla \phi(x, y)|^2} dx dy,$$

where  $\nabla \phi = (\partial_x \phi, \partial_y \phi)$  is the gradient of  $\phi$ , and  $|\nabla \phi| \stackrel{\text{def}}{=} \sqrt{(\partial_x \phi)^2 + (\partial_y \phi)^2}$  is the Euclidean length of  $\nabla \phi$ .

**Remark 7.2.1.** The divergence theorem holds in all dimensions, not just 3. In dimension 1, the divergence theorem is

(7.2.5) 
$$\int_{[a,b]} \frac{d}{dx} F(x) \, dx = F(b) - F(a),$$

which is just the Fundamental Theorem of Calculus.

<sup>&</sup>lt;sup>2</sup>Throughout this course, a *domain* is defined to be an open, connected subset of  $\mathbb{R}^n$ .

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### MATH 18.152 COURSE NOTES - CLASS MEETING # 2

### 18.152 Introduction to PDEs, Fall 2011

# Class Meeting # 2: The Diffusion (aka Heat) Equation

Professor: Jared Speck

#### 1. Introduction to the Heat Equation

The heat equation for a function u(t,x),  $x \stackrel{\text{def}}{=} (x^1, \dots, x^n) \in \mathbb{R}^n$ , is

$$(1.0.1) u_t - D\Delta u = f(t, x).$$

Here, the constant D > 0 is the diffusion coefficient, f(t, x) is an inhomogeneous term, and  $\Delta$  is the Laplacian operator, which takes the following form in Cartesian coordinates:

(1.0.2) 
$$\Delta \stackrel{\text{def}}{=} \sum_{i=1}^{n} \partial_i^2.$$

Equation (1.0.1) is first-order and linear.

# 2. A SIMPLE MODEL OF HEAT FLOW THAT LEADS TO THE HEAT EQUATION

We now give an example of a simple model of heat flow that leads to the heat equation. Consider a homogeneous, isotropic solid body  $\mathcal{B} \subset \mathbb{R}^n$  (n = 3 is the physically relevant case) described by the following physical properties:

(2.0.3) 
$$\rho \stackrel{\text{def}}{=} \text{mass density} \sim [\text{mass}] \times [\text{Volume}]^{-1} = \text{constant},$$

(2.0.4) 
$$e(t,x) \stackrel{\text{def}}{=} \text{thermal energy per unit mass} \sim [\text{energy}] \times [\text{mass}]^{-1}$$
.

Let's also assume that heat is supplied to the body by an external source which pumps in heat at the following rate per unit mass:

(2.0.5) 
$$\mathscr{R} \sim [\text{energy}] \times [\text{time}]^{-1} \times [\text{mass}]^{-1}$$
.

The total thermal E(t; V) energy contained in a body sub-volume  $V \subset \mathcal{B}$  at time t is the integral of e(t, x) over V:

(2.0.6) 
$$E(t;V) \stackrel{\text{def}}{=} \int_{V} \rho e(t,x) d^{n}x.$$

The rate of change of the total energy contained in V is

(2.0.7) 
$$\frac{d}{dt}E(t;V) = \frac{d}{dt}\int_{V} \rho e(t,x) d^{n}x = \int_{V} \rho \partial_{t} e(t,x) d^{n}x.$$

In (2.0.7), we have assumed that you can differentiate under the integral; we can do this when e(t,x) is a "nice" function. We will be more precise about the meaning of "nice" later in the course.

Let's now address the factors that can cause  $\frac{d}{dt}E(t;V)$  to be non-zero. That is, let's account for the factors that cause the energy within the volume V to change. In our simple model, we will account for only two factors. First, by integrating (2.0.5) over V, we deduce the rate of energy pumped into the sub-volume V by the external source:

(2.0.8) 
$$\int_{V} \rho \mathcal{R}(t, x) d^{n}x \sim [\text{energy}] \times [\text{time}]^{-1}.$$

Second, we will also assume that heat energy is flowing throughout the body, and that flow can be modeled by a heat flux vector  $\mathbf{q}$ 

(2.0.9) 
$$\mathbf{q} \sim [\text{energy}] \times [\text{time}]^{-1} \times [\text{area}]^{-1}$$

which specifies the direction and magnitude of heat flow across a unit area. That is, if  $d\sigma \subset \partial V$  is a small surface area with *outward* unit-normal  $\hat{\mathbf{N}}$ , then  $\mathbf{q} \cdot \hat{\mathbf{N}}$  is the energy flowing *out* of the small surface. Thus, the rate of heat energy flowing *into* V is

(2.0.10) 
$$-\int_{\partial V} \mathbf{q} \cdot \hat{\mathbf{N}} d\sigma = -\int_{V} \nabla \cdot \mathbf{q} d^{n} x \sim [\text{energy}] \times [\text{time}]^{-1},$$

where the equality follows from the divergence theorem.

We will connect the various energies together by assuming the following energy conservation "law:" The rate of change of total energy in the sub-volume V is equal to the rate of heat energy flowing into V + rate of heat energy supplied by the external source. Using (2.0.7), (2.0.8), and (2.0.10), we see that this "law" takes the following form in terms of integrals:

(2.0.11) 
$$\int_{V} \rho \partial_{t} e(t, x) d^{n} x = -\int_{V} \nabla \cdot \mathbf{q} d^{n} x + \int_{V} \rho \mathscr{R} d^{n} x.$$

Since the above relations are assumed to hold for all body sub-volumes V, the integrands must be equal (again, as long as they are nice):

(2.0.12) 
$$\rho \partial_t e(t, x) = -\nabla \cdot \mathbf{q} + \rho \mathcal{R}.$$

2.1. Fourier's law. In order to turn (2.0.12) into a PDE that we can study, we need to make another assumption about e(t, x),  $\mathbf{q}$ , and their relation to the temperature u(t, x). Fourier hypothesized the following "Fourier's Law of heat conduction:"

(2.1.1) 
$$\mathbf{q}(t,x) = -\kappa \nabla u(t,x),$$

where  $\kappa > 0$  is the thermal conductivity, and  $\nabla u \stackrel{\text{def}}{=} (\partial_1 u, \dots, \partial_n u)$  is the spatial derivative gradient of the temperature u(t,x). We will assume that  $\kappa$  is a constant. Recall that at each fixed t,  $\nabla u(t,x)$  points in the direction of maximal increase and that  $\nabla u(t,x)$  is perpendicular to the level sets  $\{x \mid u(x) = \text{constant}\}$ . Thus, (2.1.1) states that heat flows "from hot to cold" (i.e. towards decreasing temperature) and that the flow is perpendicular to the surfaces of constant temperature.

**Remark 2.1.1.** (2.1.1) is NOT A FUNDAMENTAL LAW OF NATURE! It is a simple but reasonable (under certain circumstances) model!

We need one more assumption in order to derive our PDE - we need to relate e(t,x) to u(t,x). We will assume a very simple model, which is experimentally verified by many substances in moderate temperature ranges:

$$(2.1.2) e = c_v u$$

Here,  $c_v > 0$  is the *specific heat at constant volume*. We also assume that  $c_v$  is constant. Like many of our previous assumptions, (2.1.2) is also just a simple model, and not a fundamental law of nature.

Finally, we combine (2.0.12), (2.1.1), and (2.1.2), and use the identity  $\nabla \cdot \nabla u = \Delta u$ , thus arriving at

(2.1.3) 
$$\partial_t u(t,x) = \frac{\kappa}{c_v \rho} \Delta u + \frac{1}{c_v} \mathcal{R}.$$

This is the heat equation (1.0.1) with  $D = \frac{\kappa}{c_v \rho}$  and  $f = \frac{1}{c_v} \mathcal{R}$ .

#### 3. Well-posedness

Remember, one of the main goals of PDE theory is to figure out which kind of data lead to a unique solution. It is not always obvious which kind of data we are allowed to specify in order to solve the equation. When we have a PDE and a notion of data such that the data always lead to a unique solution, and the solution depends "continuously" on the data, we say that the problem is well-posed.

3.1. **Dirichlet boundary conditions.** Let's study Dirichlet boundary conditions for the heat equation in n = 1 dimensions. Think of a one-dimensional rod with endpoints at x = 0 and x = L. Let's set most of the constants equal to 1 for simplicity, and assume that there is no external source pumping energy into the rod, i.e., that there is no inhomogeneous term f.

Then we could, for example, prescribe the temperature of the rod at t = 0 (sometimes called Cauchy data) and also at the boundaries x = 0 and x = L for all times  $t \in [0, T]$ :

(3.1.1) 
$$\begin{cases} \partial_t u - D \partial_x^2 u = 0, & (t, x) \in (0, T) \times (0, L), \\ u(0, x) = g(x), & x \in [0, L], & (\text{Cauchy data}), \\ u(t, 0) = h_0(t), & u(t, L) = h_L(t), & t > 0, & (\text{Dirichlet data}). \end{cases}$$

As we will see, under suitable assumptions on the functions,  $g, h_0, h_L$ , these conditions lead to a well-posed problem.

3.2. Neumann (N for Normal!) boundary conditions. Instead of prescribing the temperature at the boundaries, let's instead prescribe the *inward rate of heat flow* (given by Fourier's law with  $\kappa = 1$ ) at the boundaries:

(3.2.1) 
$$\begin{cases} \partial_t u - D\partial_x^2 u = 0, & (t, x) \in (0, T) \times (0, L), \\ u(0, x) = g(x), & (\text{Cauchy data}), \\ -\partial_x u(t, 0) = h_0(t), & \partial_x u(t, L) = h_L(t), & (\text{Neumann data}). \end{cases}$$

Under suitable assumptions on the functions,  $g, h_0, h_L$ , these conditions also lead to a well-posed problem.

3.3. Robin boundary conditions. We can also take some linear combinations of the Dirichlet and Neumann conditions:

(3.3.1) 
$$\begin{cases} \partial_t u - D \partial_x^2 u = 0, & (t, x) \in (0, T) \times (0, L), \\ u(0, x) = g(x), & (\text{Cauchy data}), \\ -\partial_x u(t, 0) + \alpha u(t, 0) = h_0(t), & \partial_x u(t, L) + \alpha u(t, L) = h_L(t), \end{cases}$$
 (Robin data),

where  $\alpha > 0$  is a positive constant. Under suitable assumptions on the functions,  $g, h_0, h_L$ , these conditions also lead to a well-posed problem.

3.4. **Mixed boundary conditions.** The above three boundary conditions are called *homogeneous* because they are of the same type at each end. It is also possible to prescribe one condition at one endpoint, and a different condition at the other endpoint. These are called *mixed boundary conditions*. These conditions also lead to a well-posed problem.

# 4. Separation of variables

We now discuss a technique, known as *separation of variables*, that can be used to explicitly solve certain PDEs. It is especially useful in the study of linear PDEs. Although this technique is applicable to some important PDEs, it is unfortunately far from universally applicable.

In a nutshell, the separation of variables technique can be summarized as:

- Look for a solution of the form u(t,x) = v(t)w(x).
- Plug this guess into the PDE and hope that the PDE forces the functions v and w to be solutions to ODEs that can be solved without too much trouble.

As we will see, when one tries to apply this technique, one quickly runs into difficulties that are best addressed using techniques from Fourier analysis. We don't have time right now to give a detailed introduction to Fourier analysis, but we will return to it later in the course if time permits; at the moment, we will only show how to use some of these techniques, without fully justifying them

A great way to illustrate separation of variables is through an example. Let's try to solve the heat equation problem with homogeneous (i.e., vanishing) Dirichlet conditions

(4.0.1) 
$$\begin{cases} u_t - u_{xx} = 0, & (t, x) \in (0, T] \times [0, 1], \\ u(0, x) = x, & x \in [0, 1], \\ u(t, 0) = 0, & u(t, 1) = 0, \end{cases}$$

by separation of variables.

**Remark 4.0.1.** Note that such a solution cannot possibly be continuous at the point (0,1).

We plug in the form u(t,x) = v(t)w(x) into (4.0.1) and discover that

$$\frac{v'(t)}{v(t)} = \frac{w''(x)}{w(x)}.$$

This should hold for all t, x. It therefore must be the case that both sides are equal to a constant, which we will call  $\lambda$ . We then have

$$(4.0.3a) v'(t) = \lambda v(t),$$

$$(4.0.3b) w''(x) = \lambda w(x).$$

Furthermore, w(0) = w(1) = 0 by the boundary conditions.

Let's address v first, since it requires less work to deal with than w. If  $\lambda \in \mathbb{R}$ , then (4.0.3a) can be generally solved:

$$(4.0.4) v(t) = Ae^{\lambda t}$$

for some  $A \in \mathbb{R}$ .

In contrast, the study of w(x) splits into three cases:

- $\lambda = 0$ . Then w(x) = Bx + C for some  $B, C \in \mathbb{R}$ . The boundary conditions imply that C = 0 and B + C = 0, so that B = C = 0. Thus, this solution is not very interesting.
- $\lambda > 0$ . Then  $w(x) = Be^{\sqrt{\lambda}x} + Ce^{-\sqrt{\lambda}x}$  for some  $B, C \in \mathbb{R}$ . The boundary conditions imply that B + C = 0, and  $Be^{\sqrt{\lambda}} + Ce^{-\sqrt{\lambda}} = 0$ , which forces B = C = 0. This solution is also not very interesting.
- $\lambda < 0$ . Then  $w(x) = B \sin(\sqrt{|\lambda|}x) + C \cos(\sqrt{|\lambda|}x)$  for some  $B, C \in \mathbb{R}$ . The boundary condition w(0) = 0 forces C = 0, so  $w(x) = B \sin(\sqrt{\lambda}x)$ . The boundary condition w(1) = 0 then forces  $\lambda = -\pi^2 m^2$  for some  $m \in \mathbb{Z}^+$ , where  $\mathbb{Z}^+ \stackrel{\text{def}}{=}$  the set of non-negative integers. The  $\lambda$  are called eigenvalues, and the corresponding  $w_m$  are the corresponding eigenvectors. Equation (4.0.3a) is called an eigenvalue problem corresponding to the linear operator  $\mathcal{L} \stackrel{\text{def}}{=} \partial_x^2$ .

We have shown that the only solutions w are of the form  $w_m(x) = B\sin(2\pi mx)$ ,  $m \in \mathbb{Z}^+$ . Using also (4.0.4) and the fact that  $\lambda = -\pi^2 m^2$  for our solutions, we have produced a family of solutions to the heat equation  $\partial_t u - \partial_x^2 u = 0$  that satisfying the boundary conditions:

$$(4.0.5) u_m(t,x) = e^{-m^2\pi^2 t} \sin(m\pi x), A_m \in \mathbb{R}, m \in \mathbb{Z}^+.$$

But we haven't yet satisfied the initial condition u(0,x) = x. To do this, we could try using the superposition principle:

(4.0.6) 
$$u(t,x) = \sum_{m=1}^{\infty} A_m u_m(t,x).$$

We would have to solve for the  $A_m$  to achieve the desired initial condition u(0,x) = x.

Here is a list of things we would have to do to fully solve this problem using this technique:

- (1) Find plausible  $A_m$ .
- (2) Show that the infinite sum (4.0.6) converges.
- (3) Show that the infinite sum solves the heat equation.
- (4) Show that u(t,x) satisfies the boundary conditions.
- (5) Check that  $\lim_{t\to 0^+} u(t,x) = u(0,x) = x$ . We also have to investigate in which sense this limit may or may not hold. We already know that this equality cannot hold pointwise at the point (0,1).

(6) Show that there can be no other solution with these initial/boundary conditions (uniqueness).

Let's deal with (1) first. If (4.0.6) holds, then at t = 0:

(4.0.7) 
$$x = u(0,x) = \sum_{m=1}^{\infty} A_m u_m(0,x) = \sum_{m=1}^{\infty} A_m \sin(m\pi x).$$

This is a Fourier series expansion for the function f(x) = x on the interval [0,1].

It is helpful to think of a function f(x) as a vector in an infinite dimensional vector space and the  $\sin(m\pi x)$  as basis vectors (however, it is not trivial to show that they form a basis...). Furthermore, if we introduce the dot product

$$\langle f(x), g(x) \rangle \stackrel{\text{def}}{=} \int_{[0,1]} f(x)g(x) \, dx,$$

then the basis vectors are orthogonal (do the computation yourself!):

(4.0.9) 
$$\langle \sin(m\pi x), \sin(\pi nx) \rangle = \begin{cases} 1/2 \text{ if } m = n \\ 0 \text{ if } m \neq n. \end{cases}$$

This *suggests* that the following heuristic computations might be able to be made completely rigorous:

$$(4.0.10) \qquad \int_{[0,1]} f(x) \sin(\pi n x) dx = \langle f(x), \sin(\pi n x) \rangle = \langle \sum_{m=1}^{\infty} A_m \sin(m \pi x), \sin(\pi n x) \rangle$$
$$= \sum_{m=1}^{\infty} \langle A_m \sin(m \pi x), \sin(\pi n x) \rangle$$
$$= \frac{1}{2} A_n.$$

Applying this to our function f(x) = x, we integrate by parts to compute that

$$(4.0.11) \quad A_m = 2 \int_{[0,1]} x \sin(m\pi x) \, dx = -\frac{2}{m\pi} x \cos(m\pi x)|_{x=0}^{x=1} + \frac{2}{m\pi} \int_{[0,1]} \cos(\pi nx) \, dx = (-1)^{m+1} \frac{2}{m\pi}.$$

We now hope that our solution is:

(4.0.12) 
$$u(t,x) = \sum_{m=1}^{\infty} (-1)^{m+1} e^{-m^2 \pi^2 t} \frac{2}{m\pi} \sin(m\pi x).$$

Remark 4.0.2. The individual terms  $(-1)^{m+1}e^{-m^2\pi^2t}\frac{2}{m\pi}\sin(m\pi x)$  are sometimes called the *modes* of the solution. Note that each mode is rapidly decaying at an exponential rate as  $t \to \infty$ . Furthermore, the infinite sum  $\sum_{m=1}^{\infty}(-1)^{m+1}e^{-m^2\pi^2t}\frac{2}{m\pi}\sin(m\pi x)$  also decays exponentially in time. Later in the course we will study the heat equation on all of  $\mathbb{R}$ , and we will once again see that under suitable assumptions, solutions to the heat equation tend to exponentially decay in time. However, if we had non-zero Dirichlet conditions for the problem (4.0.1), then the solution might not decay to 0, but instead to some other state.

Let's now answer some of the remaining questions from above.

- (2) Thanks to the rapidly decaying in m factor  $e^{-m^2\pi^2t}$ , for any t > 0, the series (4.0.12) can be seen to uniformly converge for  $x \in [0,1]$  using one of the standard convergence arguments from analysis (carefully work through this argument yourself; pg. 9 of your book might be a helpful reference). The argument for t = 0 is much more subtle and is addressed in Theorem 4.1 below.
- (3) We already know that each mode in (4.0.12) solves the heat equation. So what about the infinite sum? Again, for any t > 0, the  $e^{-m^2\pi^2t}$  factor plus standard results from analysis allow us to repeatedly differentiate the series term-by-term in both t and x (work through this yourself). In particular, the series is *smooth* (i.e., infinitely differentiable in all variables) for any t > 0. In particular, for t > 0, we have that

(4.0.13a) 
$$\partial_t u = \sum_{m=1}^{\infty} \partial_t [(-1)^{m+1} e^{-m^2 \pi^2 t} \frac{2}{m\pi} \sin(m\pi x)] = \sum_{m=1}^{\infty} (-1)^m m\pi e^{-m^2 \pi^2 t} \sin(m\pi x),$$

(4.0.13b) 
$$\partial_x^2 u = \sum_{m=1}^{\infty} \partial_x^2 [(-1)^{m+1} e^{-m^2 \pi^2 t} \frac{2}{m\pi} \sin(m\pi x)] = \sum_{m=1}^{\infty} (-1)^m m\pi e^{-m^2 \pi^2 t} \frac{2}{m\pi} \sin(m\pi x),$$

which shows that  $-\partial_t u + \partial_x^2 u = 0$ .

(4) The fact that u verifies the correct Dirichlet conditions at x = 0 and x = 1 follows from the fact that each of the modes does.

The remaining two questions require more work. We first quote the following theorem from Fourier analysis to help us understand the Fourier expansion at t = 0. Using this theorem, you will address question (5) in your homework.

Theorem 4.1 (Some basic facts from Fourier analysis). If f(x) is a function such that  $||f||_{L^2([0,1])}^2 \stackrel{\text{def}}{=} \int_0^1 |f(x)|^2 dx < \infty$ , then f(x) can be Fourier-expanded as  $f(x) = \sum_{m=1}^{\infty} A_m \sin(m\pi x)$ , where  $A_m = 2 \int_{[0,1]} f(x) \sin(m\pi x) dx$ . The infinite sum converges in the sense that

(4.0.14) 
$$||f - \sum_{m=1}^{N} A_m \sin(m\pi x)||_{L^2([0,1])} \to 0 \text{ as } N \to \infty.$$

We also have the Parseval identity

$$(4.0.15) ||f||_{L^2([0,1])}^2 = \sum_{m=1}^{\infty} A_m^2 ||\sin(m\pi x)||_{L^2([0,1])}^2 = \sum_{m=1}^{\infty} \frac{1}{2} A_m^2.$$

Note that (4.0.15) is an "infinite dimensional Pythagorean theorem." Furthermore, if f is continuous on [0,1], then for any subinterval  $[a,b] \subset (0,1)$ ,

(4.0.16) 
$$||f - \sum_{m=1}^{N} A_m \sin(m\pi x)||_{C^0([a,b])} \to 0 \text{ as } N \to \infty,$$

i.e., the convergence is uniform on any closed subinterval [a,b] of the open interval (0,1).

**Exercise 4.0.1.** Many extensions of Theorem 4.1 are possible. Read Appendix A of your textbook in order to learn about them.

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## MATH 18.152 COURSE NOTES - CLASS MEETING # 3

## 18.152 Introduction to PDEs, Fall 2011

Class Meeting # 3: The Heat Equation: Uniqueness

Professor: Jared Speck

## 1. Uniqueness

The results from the previous lecture produced one solution to the Dirichlet problem

(1.0.1) 
$$\begin{cases} u_t - u_{xx} = 0, & (t, x) \in (0, T] \times [0, 1], \\ u(0, x) = x, & x \in [0, 1], \\ u(t, 0) = 0, & u(t, 1) = 0, \end{cases}$$

namely

(1.0.2) 
$$u(t,x) = \sum_{m=1}^{\infty} (-1)^{m+1} e^{-m^2 \pi^2 t} \frac{2}{m\pi} \sin(m\pi x).$$

But how do we know that this is the only one? In other words, we need to answer the uniqueness question (6) from the previous lecture. The next theorem addresses this question. We first need to introduce some important spacetime domains that will play a role in the analysis.

**Definition 1.0.1.** Let  $\Omega \subset \mathbb{R}^n$  be a bounded spatial domain (i.e., an open connected subset of  $\mathbb{R}^n$ ), and let T > 0 be a time. We define the corresponding spacetime cylinder  $Q_T \subset \mathbb{R}^{1+n}$  by

$$(1.0.3) Q_T \stackrel{\text{def}}{=} (0, T) \times \Omega.$$

We also define the parabolic boundary  $\partial_{\nu}Q_{T}$  of  $Q_{T}$  as follows:

(1.0.4) 
$$\partial_p Q_T \stackrel{\text{def}}{=} \{0\} \times \overline{\Omega} \cup (0, T] \times \partial \Omega$$

$$= \text{bottom of } \overline{Q}_T \cup \text{ sides of } \overline{Q}_T.$$

Here,  $\overline{Q}_T$  denotes the closure of  $Q_T$  in  $\mathbb{R}^{1+n}$ .

Theorem 1.1 (A uniqueness result for the heat equation on a finite interval). Solutions  $u \in C^{1,2}(\overline{Q}_T)$  to the inhomogeneous heat equation

(1.0.5) 
$$\partial_t u - D\partial_x^2 u = f(t, x)$$

are unique under Dirichlet, Neumann, Robin, or mixed conditions.

**Remark 1.0.1.** By  $u \in C^{1,2}(\overline{Q}_T)$ , we mean that the time derivatives of u(t,x) up to order 1 (the first index) are continuously differentiable on  $Q_T$  and extend continuously to the closure of  $Q_T$ , and also that all spatial derivatives of u(t,x) up to order 2 (the second index) are continuously differentiable on  $Q_T$  and extend continuously to the closure of  $Q_T$ . Unfortunately, these kind of ugly technical details often play a role in PDE theory.

**Remark 1.0.2.** In its current form Theorem, 1.1 is not quite strong enough to apply to the problem (1.0.1). More precisely, the solution to that problem has a discontinuity at (0,1), while Theorem 1.1 requires that the solutions are of class  $C^{1,2}(\overline{Q}_T)$ . Uniqueness does in fact hold in a certain sense for the problem (1.0.1), but the because of the discontinuity, this issue is best addressed in a more advanced course.

*Proof.* Let's do the Dirichlet proof in the case D = 1. Assume we have two solutions to (1.0.5) with specified Cauchy and Dirichlet data. Then by subtracting them and calling the difference w, we get another solution w satisfying

(1.0.6) 
$$\begin{cases} \partial_t w - \partial_x^2 w = 0, & (t, x) \in [0, T] \times [0, L], \\ w(0, x) = 0, & x \in [0, L], \\ w(t, 0) = 0, & w(t, L) = 0, & t \in [0, T]. \end{cases}$$

We want to show that w(t,x) = 0 for  $(t,x) \in [0,T] \times [0,L]$ . We perform the following superimportant and very commonly used strategy: we multiply both sides of (1.0.6) by w and integrate dx over the interval [0,L] to derive

(1.0.7) 
$$\int_{[0,L]} w \partial_t w \, dx = \int_{[0,L]} w \partial_x^2 w \, dx$$
 differentiate under the integral 
$$\frac{d}{dt} \frac{1}{2} \int_{[0,L]} w^2(t,x) \, dx = \int_{[0,L]} w \partial_t w \, dx = \underbrace{\int_{[0,L]} w \partial_x^2 w \, dx}_{\text{integrate by parts}}$$
 
$$= \underbrace{-\int_{[0,L]} (\partial_x w(t,x))^2 \, dx}_{\leq 0} + \underbrace{w(t,x)\partial_x w(t,x)|_{x=0}^{x=L}}_{= 0 \text{ by bndry. cond.}}$$
 
$$\leq 0.$$

So if we define the *energy* 

(1.0.8) 
$$E(t) \stackrel{\text{def}}{=} \underbrace{\int_{[0,L]} w^2(t,x) \, dx},$$

then we have shown that

$$(1.0.9) \frac{d}{dt}E(t) \le 0.$$

But E(0) = 0 by the initial conditions of w. Therefore, E(t) = 0 for  $t \in [0, T]$ . But since  $w^2(t, x)$  is continuous and non-negative, it must be that  $w^2(t, x) = 0$  for  $(t, x) \in [0, T] \times [0, L]$ .

**Remark 1.0.3.** Broadly speaking, the strategy we have used in this proof is called the *energy* method. It is a very flexible strategy that applies to many PDEs.

Note also that we did not need to know very much about the solution to conclude that it is unique! In particular, we didn't need to "find a formula" for the solution!

Note also that E(t) is the square of the spatial  $L^2([0,L])$  norm of w at time t.

18.152 Introduction to Partial Differential Equations Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## MATH 18.152 COURSE NOTES - CLASS MEETING # 4

## 18.152 Introduction to PDEs, Fall 2011

Class Meeting #4: The Heat Equation: The Weak Maximum Principle

Professor: Jared Speck

## 1. The Weak Maximum Principle

We will now study some important properties of solutions to the heat equation  $\partial_t u - D\Delta u = 0$ . For simplicity, we sometimes only study the case of 1+1 spacetime dimensions, even though analogous properties are verified in higher dimensions.

**Theorem 1.1** (Weak Maximum Principle). Let  $\Omega \subset \mathbb{R}^n$  be a domain. Recall that  $Q_T \stackrel{def}{=} (0,T) \times \Omega$  is a spacetime cylinder and that  $\partial_p Q_T \stackrel{def}{=} \{0\} \times \overline{\Omega} \cup (0,T] \times \partial \Omega$  is its corresponding parabolic boundary. Let  $w \in C^{1,2}(Q_T) \cap C(\overline{Q}_T)$  be a solution to the (possibly inhomogeneous) heat equation

$$(1.0.1) w_t - D\Delta w = f,$$

where  $f \leq 0$ . Then w(t,x) obtains its max in the region  $\overline{Q}_T$  on  $\partial_p Q_T$ . Thus, if w is strictly negative on  $\partial_p Q_T$ , then w is strictly negative on  $\overline{Q}_T$ .

*Proof.* For simplicity, we consider only case of 1+1 spacetime dimensions. Let  $\epsilon$  be a positive number, and let  $u=w-\epsilon t$ . Our goal is to first study u, and then take a limit as  $\epsilon \downarrow 0$  to extract information about w. Note that on  $\overline{Q}_T$  we have  $u \leq w$ , that  $w \leq u + \epsilon T$ , and that in  $Q_T$  we have

$$(1.0.2) u_t - Du_{xx} = f - \epsilon < 0.$$

We claim that the maximum of u on  $\overline{Q}_{T-\epsilon}$  occurs on  $\partial_p Q_{T-\epsilon}$ . To verify the claim, suppose that u(t,x) has its max at  $(t_0,x_0)\in \overline{Q}_{T-\epsilon}$ . We may assume that  $0< t_0\leq T-\epsilon$ , since if  $t_0=0$  the claim is obviously true. Under this assumption, we have that u< w and that  $w\leq u+\epsilon T$ . Similarly, we may also assume that  $x\in\Omega$ , since otherwise we would have  $(t,x)\in\partial_p Q_{T-\epsilon}$ , and the claim would be true.

Then from vector calculus,  $u_x(t_0, x_0)$  must be equal to 0. Furthermore,  $u_t(t_0, x_0)$  must also be equal to 0 if  $t_0 < T - \epsilon$ , and  $u_t(t_0, x_0) \ge 0$  if  $t_0 = T - \epsilon$ . Now since  $u(t_0, x_0)$  is a maximum value, we can apply Taylor's remainder theorem in x to deduce that for x near  $x_0$ , we have

$$(1.0.3) u(t_0, x) - u(t_0, x_0) = \underbrace{u_x|_{t_0, x_0}(x - x_0)}_{0} + u_{xx}|_{t_0, x^*}(x - x_0)^2 \le 0,$$

where  $x_*$  is some point in between  $x_0$  and x. Therefore,  $u_{xx}(t_0, x^*) \leq 0$ , and by taking the limit as  $x \to x_0$ , it follows that  $u_{xx}(t_0, x_0) \leq 0$ . Thus, in any possible case, we have that

$$(1.0.4) u_t(t_0, x_0) - Du_{xx}(t_0, x_0) \ge 0,$$

which contradicts (1.0.2).

Using  $u \leq w$  and that fact that  $\partial_p Q_{T-\epsilon} \subset \partial_p Q_T$ , we have thus shown that

(1.0.5) 
$$\max_{\overline{Q}_{T-\epsilon}} u = \max_{\partial_p Q_{T-\epsilon}} u \le \max_{\partial_p Q_{T-\epsilon}} w \le \max_{\partial_p Q_T} w.$$

Using (1.0.5) and  $w \leq u + \epsilon T$ , we also have that

(1.0.6) 
$$\max_{\overline{Q}_{T-\epsilon}} w \le \max_{\overline{Q}_{T-\epsilon}} u + \epsilon T \le \epsilon T + \max_{\partial_p Q_T} w.$$

Now since w is uniformly continuous on  $\overline{Q}_T$ , we have that

$$\begin{array}{cc}
\max w \uparrow \max w \\
\overline{Q}_{T-\epsilon}
\end{array}$$

as  $\epsilon \downarrow 0$ . Thus, allowing  $\epsilon \downarrow 0$  in inequality (1.0.6), we deduce that

$$\max_{\overline{Q}_T} w = \lim_{\epsilon \downarrow 0} \max_{\overline{Q}_{T-\epsilon}} w \leq \lim_{\epsilon \downarrow 0} (\epsilon T + \max_{\partial_p Q_T} w) = \max_{\partial_p Q_T} w \leq \max_{\overline{Q}_T} w.$$

Therefore, all of the inequalities in (1.0.8) can be replaced with equalities, and

$$\max_{\overline{Q}_T} w = \max_{\partial_p Q_T} w$$

as desired.

The following very important corollary shows how to *compare* two different solutions to the heat equation with possibly different inhomogeneous terms. The proof relies upon the weak maximum principle.

Corollary 1.0.1 (Comparison Principle and Stability). Suppose that v, w are solutions to the heat equations

$$(1.0.10) v_t - Dv_{xx} = f,$$

$$(1.0.11) w_t - Dw_{xx} = g.$$

Then

- (1) (Comparison): If  $v \geq w$  on  $\partial_p Q_T$  and  $f \geq g$ , then  $v \geq w$  on all of  $Q_T$ .
- (2) (Stability):  $\max_{\overline{Q}_T} |v w| \le \max_{\partial_p Q_T} |v w| + T \max_{\overline{Q}_T} |f g|$ .

*Proof.* One of the things that makes linear PDEs relatively easy to study is that you can add or subtract solutions: Setting  $u \stackrel{\text{def}}{=} w - v$ , we have

$$(1.0.12) u_t - Du_{xx} = g - f \le 0.$$

Then by Theorem 1.1, since  $u \leq 0$  on  $\partial_p Q_T$  we have that  $u \leq 0$  on  $Q_T$ . This proves (1).

To prove (2), we define  $M \stackrel{\text{def}}{=} \max_{\overline{Q}_T} |f - g|$ ,  $u \stackrel{\text{def}}{=} w - v - tM$  and note that

$$(1.0.13) u_t - Du_{xx} = g - f - M \le 0.$$

Thus, by Theorem 1.1, we have that

(1.0.14) 
$$\max_{\overline{Q}_T} u = \max_{\partial_p Q_T} u \le \max_{\partial_p Q_T} |w - v|.$$

Thus, subtracting and adding tM, we have

$$(1.0.15) \qquad \max_{\overline{Q}_T} w - v \le \max_{\overline{Q}_T} (w - v - tM) + \max_{\overline{Q}_T} tM \le \max_{\partial_p Q_T} |w - v| + TM.$$

Similarly, by setting  $u \stackrel{\text{def}}{=} v - w - tM$ , we can show that

(1.0.16) 
$$\max_{\overline{Q}_T} v - w \le \max_{\partial_p Q_T} |w - v| + TM.$$

Combining (1.0.15) and (1.0.16), and recalling the definition of M, we have shown (2).

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## MATH 18.152 COURSE NOTES - CLASS MEETING # 5

## 18.152 Introduction to PDEs, Fall 2011

Class Meeting # 5: The Fundamental Solution for the Heat Equation

Professor: Jared Speck

## 1. The Fundamental solution

As we will see, in the case  $\Omega = \mathbb{R}^n$ , we will be able to represent general solutions the inhomogeneous heat equation

(1.0.1) 
$$u_t - D\Delta u = f, \qquad \Delta \stackrel{\text{def}}{=} \sum_{i=1}^n \partial_i^2$$

in terms of f, the initial data, and a single solution that has very special properties. This special solution is called the fundamental solution.

**Remark 1.0.1.** Note that when  $\Omega = \mathbb{R}^n$ , there are no finite boundary conditions to worry about. However, we do have to worry about "boundary conditions at  $\infty$ ." Roughly speaking, this means that we have to assume something about the growth rate of the solution as  $|x| \to \infty$ .

**Definition 1.0.1.** The fundamental solution  $\Gamma_D(t,x)$  to (1.0.1) is defined to be

(1.0.2) 
$$\Gamma_D(t,x) \stackrel{\text{def}}{=} \frac{1}{(4\pi Dt)^{n/2}} e^{-\frac{|x|^2}{4Dt}}, \qquad t > 0, x \in \mathbb{R}^n,$$

where  $x \stackrel{\text{def}}{=} (x^1, \dots, x^n), |x|^2 \stackrel{\text{def}}{=} \sum_{i=1}^n (x^i)^2$ .

Let's check that  $\Gamma_D(t,x)$  solves (1.0.1) when f=0 in the next lemma.

**Lemma 1.0.1.**  $\Gamma_D(t,x)$  is a solution to the heat equation (1.0.1) when f=0 for  $x \in \mathbb{R}^n, t>0$ .

Proof. We compute that 
$$\partial_t \Gamma_D(t,x) = \left(-\frac{2\pi Dn}{(4\pi Dt)^{n/2+1}} + \frac{1}{(4\pi Dt)^{n/2}} \frac{|x|^2}{4Dt^2}\right) e^{-\frac{|x|^2}{4Dt}}$$
. Also, we compute  $\partial_i \Gamma_D(t,x) = -\frac{2\pi x^i}{(4\pi Dt)^{n/2+1}} e^{-\frac{|x|^2}{4Dt}}$  and  $\partial_i^2 \Gamma_D(t,x) = \left(-\frac{2\pi}{(4\pi Dt)^{n/2+1}} + \frac{1}{4Dt} \frac{2\pi (x^i)^2}{(4\pi Dt)^{n/2+1}}\right) e^{-\frac{|x|^2}{4Dt}}$ ,  $D\Delta\Gamma_D(t,x) = \left(-\frac{2\pi Dn}{(4\pi Dt)^{n/2+1}} + \frac{1}{4Dt} \frac{2\pi D|x|^2}{(4\pi Dt)^{n/2+1}}\right) e^{-\frac{|x|^2}{4Dt}}$ . Lemma 1.0.1 now easily follows.

$$D\Delta\Gamma_D(t,x) = \left(-\frac{2\pi Dn}{(4\pi Dt)^{n/2+1}} + \frac{1}{4Dt}\frac{2\pi D|x|^2}{(4\pi Dt)^{n/2+1}}\right)e^{-\frac{|x|^2}{4Dt}}$$
. Lemma 1.0.1 now easily follows.

Here are a few very important properties of  $\Gamma_D(t,x)$ .

**Lemma 1.0.2.**  $\Gamma_D(t,x)$  has the following properties:

- (1) If  $x \neq 0$ , then  $\lim_{t\to 0^+} \Gamma_D(t,x) = 0$
- $(2) \lim_{t\to 0^+} \Gamma_D(t,0) = \infty$
- (3)  $\int_{\mathbb{R}^n} \Gamma_D(t,x) d^n x = 1 \text{ for all } t > 0$

*Proof.* This is a good exercise for you to do on your own.

As we will see, (1) - (3) suggest that at t=0,  $\Gamma_D(0,x)$  behaves like the "delta distribution" centered at 0." We'll make sense of this in the next lemma.

**Remark 1.0.2.** The delta distribution is sometimes called the "delta function," but it is *not a function in the usual sense!* 

So what is the delta distribution?

**Definition 1.0.2.** The delta distribution  $\delta$  is an example of a mathematical object called a *distribution*. It acts on suitable functions  $\phi(x)$  as follows:

$$(1.0.3) \langle \delta, \phi \rangle \stackrel{\text{def}}{=} \phi(0).$$

**Remark 1.0.3.** The notation  $\langle \cdot, \cdot \rangle$  is meant to remind you of the  $L^2$  inner product

(1.0.4) 
$$\langle f, g \rangle = \int_{\mathbb{R}^n} f(x)g(x) d^n x.$$

The next lemma shows that  $\Gamma_D(t,x)$  behaves like the delta distribution as  $t\to 0^+$ .

**Lemma 1.0.3.** Suppose that  $\phi(x)$  is a continuous function on  $\mathbb{R}^n$  and that there exist constants  $a, b \geq 0$  such that

$$|\phi(x)| \le ae^{b|x|^2}.$$

Then

(1.0.6) 
$$\lim_{t \to 0^+} \int_{\mathbb{R}^n} \Gamma_D(t, x) \phi(x) \, d^n x = \phi(0).$$

*Proof.* Using Property (3) of Lemma 1.0.2, we start with the simple inequality

$$(1.0.7) \qquad \phi(0) = \int_{\mathbb{R}^n} \Gamma_D(t, x) \phi(0) \, d^n x = \int_{\mathbb{R}^n} \Gamma_D(t, x) \phi(x) \, d^n x + \int_{\mathbb{R}^n} \Gamma_D(t, x) (\phi(0) - \phi(x)) \, d^n x.$$

Let  $\epsilon > 0$  be any small positive number, and choose a ball B of radius R centered at 0 such that  $|\phi(0) - \phi(x)| \le \epsilon$  for  $x \in B$  (this is possible since  $\phi$  is continuous). Then the last term from above can be estimated as follows, where  $B^c$  denotes the complement of B in  $\mathbb{R}^n$ :

$$\left| \int_{\mathbb{R}^{n}} \Gamma_{D}(t,x) (\phi(0) - \phi(x)) d^{n}x \right| \leq \int_{B} \Gamma_{D}(t,x) |\phi(0) - \phi(x)| d^{n}x + \int_{B^{c}} \Gamma_{D}(t,x) |\phi(0) - \phi(x)| d^{n}x$$

$$(1.0.8) \qquad \leq \int_{B} \Gamma_{D}(t,x) \epsilon d^{n}x + |\phi(0)| \int_{B^{c}} \Gamma_{D}(t,x) d^{n}x + \int_{B^{c}} \Gamma_{D}(t,x) |\phi(x)| d^{n}x$$

$$\leq \epsilon + |\phi(0)| \int_{B^{c}} \Gamma_{D}(t,x) d^{n}x + \int_{B^{c}} \Gamma_{D}(t,x) |\phi(x)| d^{n}x.$$

We have thus shown that

$$(1.0.9) \qquad \left| \phi(0) - \int_{\mathbb{R}^n} \Gamma_D(t, x) \phi(x) \, d^n x \right| \le \epsilon + |\phi(0)| \int_{B^c} \Gamma_D(t, x) \, d^n x + \int_{B^c} \Gamma_D(t, x) |\phi(x)| \, d^n x.$$

To estimate the final term on the right-hand side of (1.0.8), we take advantage of the spherical symmetry of  $\Gamma(t,x)$  in x. More precisely, we introduce the radial variable  $r=|x|\stackrel{\text{def}}{=}\sqrt{\sum_{i=1}^n(x^i)^2}$ 

and recall from vector calculus that for spherically symmetric functions,  $d^n x = C_n r^{n-1} dr$  where  $C_n > 0$  is a constant. Therefore, using the assumed bound  $|\phi(x)| \le a e^{br^2}$ , we have that

$$\int_{B^c} \Gamma_D(t,x) |\phi(x)| \, d^n x \le C'_n t^{-n/2} \int_{r=R}^{\infty} r^{n-1} e^{-(\frac{1}{4Dt}-b)r^2} \, dr \le C''_n \left(\frac{1}{4D}-bt\right)^{-n/2} \int_{\rho=R\sqrt{\frac{1}{4Dt}-b}}^{\infty} \rho^{n-1} e^{-\rho^2} \, d\rho,$$

where  $C'_n > 0$  and  $C''_n > 0$  are constants. To deduce the second inequality in (1.0.10), we have made the change of variables  $r = \rho(\frac{1}{4Dt} - b)^{-1/2} = \rho t^{1/2}(\frac{1}{4D} - bt)^{-1/2}$ . Now since  $R\sqrt{\frac{1}{4Dt} - b} \to \infty$  as  $t \to 0^+$ , it easily follows from the last expression in (1.0.10) that  $\int_{B^c} \Gamma_D(t, x) d^n x$  goes to 0 as  $t \to 0^+$ .

The second term on the right-hand side of (1.0.8) can similarly be shown to go to 0 as  $t \to 0^+$ . Combining the above arguments, we have thus shown that for any  $\epsilon > 0$ ,

(1.0.11) 
$$\limsup_{t \to 0^+} \left| \phi(0) - \int_{\mathbb{R}^n} \Gamma_D(t, x) \phi(x) \, d^n x \right| \le \epsilon.$$

We therefore conclude that

(1.0.12) 
$$\lim_{t \to 0^+} \left| \phi(0) - \int_{\mathbb{D}^n} \Gamma_D(t, x) \phi(x) \, d^n x \right| = 0$$

as desired.

Remark 1.0.4. Lemma 1.0.3 can be restated as

(1.0.13) 
$$\lim_{t \to 0^+} \langle \Gamma_D(t, \cdot), \phi(\cdot) \rangle = \langle \delta(\cdot), \phi(\cdot) \rangle = \phi(0).$$

On the left,  $\langle , \rangle$  means the integral inner product, whereas in the middle it has the meaning of (1.0.3). We sometimes restate (1.0.13) as

(1.0.14) 
$$\lim_{t \to 0^+} \Gamma_D(t, x) = \delta(x).$$

Let's summarize the above results.

**Proposition 1.0.4** (Properties of  $\Gamma_D(t,x)$ ).  $\Gamma_D(t,x)$  is a solution to the heat equation (1.0.1) (with f=0) verifying the initial conditions

(1.0.15) 
$$\lim_{t \to 0^+} \Gamma_D(t, x) = \delta(x).$$

1.1. Solving the global Cauchy problem when n = 1. Let's see how we can use  $\Gamma_D$  to solve the following initial value (aka Cauchy) problem:

(1.1.1) 
$$u_t - Du_{xx} = 0, \qquad (t, x) \in (0, \infty) \times \mathbb{R},$$
$$u(0, x) = g(x).$$

We will make use of an important mathematical operation called *convolution*.

**Definition 1.1.1.** If f and g are two functions on  $\mathbb{R}^n$ , then we define their convolution f \* g to be the following function on  $\mathbb{R}^n$ :

$$(1.1.2) (f*g)(x) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} f(y)g(x-y) d^n y.$$

Convolution is an averaging process, in which the function f(x) is replaced by the "average value" of f(x) relative to the "profile" function g(x).

The convolution operator plays a very important role in many areas of mathematics. Here are two key properties. First, by making the change of variables z = x - y,  $d^n z = d^n y$  in (1.1.2), we see that

$$(1.1.3) (f * g)(x) = \int_{\mathbb{R}^n} f(y)g(x-y) d^n y = \int_{\mathbb{R}^n} f(x-z)g(z) d^n z = (g * f)(x),$$

which implies that convolution is a *commutative* operation. Next, Fubini's theorem can be used to show that

$$(1.1.4) f * (g * h) = (f * g) * h,$$

so that \* is also associative.

**Remark 1.1.1.** According to (1.0.3) and (1.1.3),

$$(1.1.5) (f * \delta)(x) = \langle \delta(y), f(x - y) \rangle_y = f(x),$$

so that in the context of convolutions, the  $\delta$  distribution plays the role of an "identity element."

The next proposition is a standard fact from analysis. It allows us to differentiate under integrals under certain assumptions. We will use it in the proof of the next theorem.

**Proposition 1.1.1** (Differentiating under the integral). Let I(a,b) be a function on  $\mathbb{R} \times \mathbb{R}$ . Assume that

$$(1.1.6) \qquad \int_{\mathbb{R}} |I(a,b)| \, da < \infty$$

for all b belonging to a neighborhood of  $b_0$  and define

(1.1.7) 
$$J(b) \stackrel{def}{=} \int_{\mathbb{R}} I(a,b) \, da.$$

Assume that there exists a neighborhood  $\mathcal{N}$  of  $b_0$  such that for almost every<sup>1</sup> a,  $\partial_b I(a,b)$  exists for  $b \in \mathcal{N}$ . In addition, assume that there exists as function U(a) (defined for almost all a) such that for  $b \in \mathcal{N}$ , we have that  $|\partial_b I(a,b)| < U(a)$  and such that

<sup>&</sup>lt;sup>1</sup>In a measure theory course, you would learn a precise technical definition of "almost every." For the purposes of this course, it suffices to know the following fact: if a statement holds for all a except for those values of a belonging to a countable set, then the statement holds for almost every a. The main point is that the function I(a, b) does not have to be "well-behaved" at every single value of a; it can have some "bad a spots," just not too many of them.

$$(1.1.8) \qquad \int_{\mathbb{R}} U(a) \, da < \infty.$$

Then near J(b) is differentiable near  $b_0$ , and

(1.1.9) 
$$\partial_b J(b) = \int_{\mathbb{R}} \partial_b I(a,b) \, da.$$

**Remark 1.1.2.** An analogous proposition is true for functions I(a,b) defined on  $\mathbb{R}^m \times \mathbb{R}^n$ .

Theorem 1.1 (Solving the global Cauchy problem via the fundamental solution). Assume that g(x) is a continuous function on  $\mathbb{R}^n$  that verifies the bounds  $|g(x)| \leq ae^{b|x|^2}$ , where a, b > 0 are constants. Then there exists a solution u(t, x) to the homogeneous heat equation

(1.1.10) 
$$u_t - D\Delta u = 0, \qquad (t > 0, x \in \mathbb{R}^n),$$
$$u(0, x) = g(x), \qquad x \in \mathbb{R}^n$$

existing for  $(t, x) \in [0, T) \times \mathbb{R}^n$ , where

$$(1.1.11) T \stackrel{def}{=} \frac{1}{4Db}.$$

Furthermore, u(t,x) can be represented as

(1.1.12) 
$$u(t,x) = [g(\cdot) * \Gamma_D(t,\cdot)](x) = \int_{\mathbb{R}^n} g(y) \Gamma_D(t,x-y) d^n y$$
$$= \frac{1}{(4\pi Dt)^{n/2}} \int_{\mathbb{R}^n} g(y) e^{-\frac{|x-y|^2}{4Dt}} d^n y.$$

The solution u(t,x) is of regularity  $C^{\infty}\left((0,\frac{1}{4Db})\times\mathbb{R}^n\right)$  (i.e., it is infinitely differentiable). Finally, for each compact subinterval  $[0,T']\subset[0,T)$ , there exist constants A,B>0 (depending on the compact subinterval) such that

$$(1.1.13) |u(t,x)| \le Ae^{B|x|^2}$$

for all  $(t,x) \in [0,T'] \times \mathbb{R}^n$ . The solution u(t,x) is the unique solution in the class of functions verifying a bound of the form (1.1.13).

**Remark 1.1.3.** Note the very important **smoothing property** of diffusion: the solution to the heat equation on all of  $\mathbb{R}^n$  is *smooth* even if the data are merely *continuous*.

**Remark 1.1.4.** The formula (1.1.12) shows that solutions to (1.1.10) propagate with **infinite speed**: even if the initial data g(x) have support that is contained within some compact region, (1.1.12) shows that at any time t > 0, the solution u(t, x) has "spread out over the entire space  $\mathbb{R}^n$ ." In contrast, as we will see later in the course, some important PDEs have finite speeds of propagation (for example, the wave equation).

*Proof.* For simplicity, we only give the proof in the case n = 1. The basic strategy of the proof is to analyze the behavior of  $\Gamma_D(t, y)$  in detail.

Let u(t,x) be the function defined by (1.1.12). The argument that follows will show that the right-hand side of (1.1.12) is finite (and more). In fact, let us first demonstrate the bound (1.1.13). To this end, let  $\epsilon > 0$  be any positive number. Then using the simple algebraic estimate  $|2xy| \le \epsilon^{-1}x^2 + \epsilon y^2$ , we deduce the inequality

$$|x - y|^2 = x^2 - 2xy + y^2 \le (1 + \epsilon^{-1})x^2 + (1 + \epsilon)y^2.$$

Using (1.1.14) and the assumed bound on  $|g(\cdot)|$ , we deduce that

$$|g(x-y)| \le ae^{b|x-y|^2} \le ae^{(1+\epsilon^{-1})b|x|^2}e^{(1+\epsilon)b|y|^2}$$

Using (1.1.15) and the fact that  $\int_{\mathbb{R}^n} g(y) \Gamma_D(t, x - y) dy = \int_{\mathbb{R}^n} g(x - y) \Gamma_D(t, y) dy$  (i.e., that convolution is commutative), we have the following estimates:

$$|u(t,x)| \leq \int_{\mathbb{R}} |g(x-y)| \Gamma_{D}(t,y) \, dy \leq a e^{(1+\epsilon^{-1})b|x|^{2}} \int_{\mathbb{R}} e^{(1+\epsilon)b|y|^{2}} \Gamma_{D}(t,y) \, dy$$

$$\leq a e^{(1+\epsilon^{-1})b|x|^{2}} \int_{\mathbb{R}} \frac{1}{\sqrt{4\pi D}} t^{-1/2} e^{-\left[\frac{1}{4\pi Dt} - (1+\epsilon)b\right]y^{2}} \, dy$$

$$= a e^{(1+\epsilon^{-1})b|x|^{2}} \frac{1}{\sqrt{4\pi D}} \left[\frac{1}{4\pi D} - (1+\epsilon)bt\right]^{-1/2} \underbrace{\int_{\mathbb{R}} e^{-z^{2}} \, dz}_{<\infty}$$

$$\leq A e^{(1+\epsilon^{-1})b|x|^{2}},$$

where A>0 is an  $\epsilon$ -dependent constant, and in the next-to-last step, we have made the change of variables  $z=\left[\frac{1}{4\pi Dt}-(1+\epsilon)b\right]^{1/2}y=t^{-1/2}\left[\frac{1}{4\pi D}-(1+\epsilon)bt\right]^{1/2}y$ . Note that this change of variables is valid as long as  $0< t<\frac{1}{4\pi D(1+\epsilon)b}$ . Since  $\epsilon$  is allowed to be arbitrarily small, we have thus demonstrated an estimate of the form (1.1.13).

Let's now check that the function u(t,x) defined by (1.1.12) is a solution to the heat equation and also that it takes on the initial conditions g(x). To this end, let  $\mathcal{L} \stackrel{\text{def}}{=} \partial_t - D\partial_x^2$ . We want to show that  $\mathcal{L}u(t,x) = 0$  for  $t > 0, x \in \mathbb{R}^n$  and that  $u(t,x) \to g(x)$  as  $t \downarrow 0$ . Recall that by Proposition 1.0.4,  $\mathcal{L}\Gamma_D(t,x) = 0$  for  $t > 0, x \in \mathbb{R}$ . For  $t > 0, x \in \mathbb{R}$ , we have that

(1.1.17) 
$$\mathcal{L}u(t,x) = \int_{\mathbb{R}} g(y) \underbrace{\mathcal{L}\Gamma_D(t,x-y)}_{0} dy = 0.$$

To derive (1.1.17), we have used Proposition 1.1.1 to differentiate under the integral; because of rapid exponential decay of  $\Gamma_D(\cdot, \cdot)$  in its second argument as the argument goes to  $\infty$ , one can use arguments similar to those given in the beginning of this proof to check that the hypotheses of the proposition are verified.

Similarly, the fact that  $u \in C^{\infty}((0, \frac{1}{4Db}) \times \mathbb{R})$  can be derived by repeatedly differentiating with respect to t and x under the integral in (1.1.12).

Furthermore by (1.0.15) and (1.1.5), we have that

(1.1.18) 
$$\lim_{t \to 0^+} u(t, x) = \lim_{t \to 0^+} (g(\cdot) * \Gamma_D(t, \cdot))(x) = (g * \delta)(x) = g(x).$$

The question of uniqueness in the class of solutions verifying a bound of the form (1.1.13) is challenging and will not be addressed here. Instead, with the help of the weak maximum principle, you will prove a weakened version of the uniqueness result in your homework.

In the next theorem, we extend the results of Theorem 1.1 to allow for an inhomogeneous term f(t,x).

**Theorem 1.2** (Duhamel's principle). Let g(x) and  $T \stackrel{def}{=} \frac{1}{4Db}$  be as in Theorem 1.1. Also assume that f(t,x),  $\partial_i f(t,x)$ , and  $\partial_i \partial_j f(t,x)$  are continuous, bounded functions on  $[0,T) \times \mathbb{R}^n$  for  $1 \le i,j \le n$ . Then there exists a unique solution u(t,x) to the inhomogeneous heat equation

(1.1.19) 
$$u_t - D\Delta u = f(t, x), \qquad (t, x) \in (0, \infty) \times \mathbb{R},$$
$$u(0, x) = g(x), \qquad x \in \mathbb{R}$$

existing for  $(t,x) \in [0,T) \times \mathbb{R}$ . Furthermore, u(t,x) can be represented as

(1.1.20) 
$$u(t,x) = (\Gamma_D(t,\cdot) * g)(x) + \int_0^t (\Gamma_D(t-s,\cdot) * f(s,\cdot))(x) ds.$$

The solution has the following regularity properties:  $u \in C^0([0,T) \times \mathbb{R}) \cap C^{1,2}((0,T) \times \mathbb{R})$ .

*Proof.* A slightly less technical version of this theorem is one of your homework exercises.  $\Box$ 

2. Deriving 
$$\Gamma_D(t,x)$$

Let's backtrack a bit and discuss how one could derive the fundamental solution to the heat equation

(2.0.21) 
$$\partial_t u(t,x) - D\Delta_x u(t,x) = 0, \qquad (t,x) \in [0,\infty) \times \mathbb{R}^n.$$

As we will see, the fundamental solution is connected to some important invariance properties associated to solutions of (2.0.21). These properties are addressed in the next lemma.

Lemma 2.0.2 (Invariance of solutions to the heat equation under translations and parabolic dilations). Suppose that u(t,x) is a solution to the heat equation (2.0.21). Let  $A, t_0 \in \mathbb{R}$  be constants, and  $x_0 \in \mathbb{R}^n$ . Then the amplified and translated function

(2.0.22) 
$$u^*(t,x) \stackrel{\text{def}}{=} Au(t-t_0, x-x_0)$$

is also a solution to (2.0.21).

Similarly, if  $\lambda > 0$  is a constant, then the amplified, parabolically scaled function

(2.0.23) 
$$u^*(t,x) \stackrel{\text{def}}{=} Au(\lambda^2 t, \lambda x)$$

is also a solution.

*Proof.* We address only the case (2.0.23), and leave (2.0.22) as a simple exercise. Using the chain rule, we calculate that if u is a solution to (2.0.21), then

(2.0.24) 
$$\partial_t u^*(t,x) - \Delta u^*(t,x) = \lambda^2 A \{ (\partial_t u)(\lambda^2 t, \lambda x) - (D\Delta u)(\lambda^2 t, \lambda x) \} = 0.$$

Thus,  $u^*$  is also a solution.

We would now like to choose the constant A in (2.0.23) so that the "total thermal energy" of  $u^*$  is equal to the "total thermal energy of" of u.

**Definition 2.0.2.** We define the total thermal energy  $\mathcal{T}(t)$  at time t associated to u(t,x) by

(2.0.25) 
$$\mathcal{T}(t) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} u(t, x) d^n x.$$

It is important to note that for rapidly-spatially decaying solutions to the heat equation,  $\mathcal{T}(t)$  is constant.

**Lemma 2.0.3.** Let  $u(t,x) \in C^{1,2}([0,\infty) \times \mathbb{R}^n)$  be a solution to the heat equation  $-\partial_t u(t,x) + \Delta u(t,x) = 0$ . Assume that at each fixed t,  $\lim_{|x| \to \infty} |x|^{n-1} |\nabla_x u(t,x)| = 0$ , uniformly in x. Furthermore, assume that there exists a function  $f(x) \geq 0$ , not depending on t, such that  $|\partial_t u| \leq f(x)$  and such that  $\int_{\mathbb{R}^n} f(x) d^n x < \infty$ . Then the total thermal energy of u(t,x) is constant in time:

$$(2.0.26) \mathcal{T}(t) = \mathcal{T}(0).$$

*Proof.* Let  $\mathcal{T}(t) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} u(t,x) d^n x$  denote the total thermal energy at time t. The hypotheses on ensure that we can differentiate under the integral and use the heat equation:

(2.0.27) 
$$\frac{d}{dt}\mathcal{T}(t) = \int_{\mathbb{R}^n} \partial_t u(t,x) \, d^n x = \int_{\mathbb{R}^n} \Delta u(t,x) \, d^n x = \lim_{R \to \infty} \int_{B_R(0)} \Delta u(t,x) \, d^n x,$$

where  $B_R(0) \subset \mathbb{R}^n$  denotes the ball of radius R centered at the origin. Then with the help of the divergence theorem, and recalling that  $d\sigma = R^{n-1}d\omega$  along  $\partial B_R(0)$ , where  $\omega$  denotes angular coordinates along the unit sphere  $\partial B_1(0)$ , we conclude that

(2.0.28) 
$$\lim_{R \to \infty} \int_{B_R(0)} \Delta u(t, x) \, d^n x = \lim_{R \to \infty} \int_{\partial B_R(0)} \nabla_{\hat{N}} u(t, \sigma) \, d\sigma$$
$$= \lim_{R \to \infty} \int_{\partial B_1(0)} R^{n-1} \nabla_{\hat{N}} u(t, R\omega) \, d\omega$$
$$= \int_{\partial B_1(0)} \lim_{R \to \infty} R^{n-1} \nabla_{\hat{N}} u(t, R\omega) \, d\omega = \int_{\partial B_1(0)} 0 \, d\omega = 0.$$

In the last steps, we have used the following basic fact from analysis: the condition  $\lim_{|x|\to\infty} |x|^{n-1} |\nabla_x u(t,x)| = 0$  uniformly in  $\omega$  allows us to interchange the order of the limit and the integral.

We now return to the issue of choosing constant A in (2.0.23) so that the total thermal energy of  $u^*$  is equal to the total thermal energy of u. Using the change of variables  $z = \lambda x$ , and recalling from multi-variable calculus that  $d^n z = \lambda^n d^n x$ , we compute that

$$(2.0.29) \qquad \int_{\mathbb{R}^n} u^*(t,x) d^n x = A \int_{\mathbb{R}^n} u(D^2 \lambda^2 t, \lambda x) d^n x = A \lambda^{-n} \int_{\mathbb{R}^n} u(\lambda^2 t, z) d^n z.$$

Observe that that  $\int_{\mathbb{R}^n} u(\lambda^2 t, z) d^n z$  is in fact the mass of u. Thus, we choose  $A = \lambda^n$ , which results in

(2.0.30) 
$$u^*(t,x) = \lambda^n u(D^2 \lambda^2 t, \lambda x).$$

Motivated by the parabolic scaling result (2.0.23), we now introduce the dimensionless variable

$$\zeta \stackrel{\text{def}}{=} \frac{x}{\sqrt{Dt}},$$

where we have used the fact that the constant D has the dimensions of [length<sup>2</sup>]/[time]. Note that  $\zeta$  is *invariant* under the parabolic scaling  $t \to \lambda^2 t$ ,  $x \to \lambda x$ .

We now proceed to derive the fundamental solution. For simplicity, we only consider the case of 1+1 spacetime dimensions. We will look for a fundamental solution of the form

(2.0.32) 
$$\Gamma_D(t,x) = \frac{1}{\sqrt{Dt}}V(\zeta),$$

where  $V(\zeta)$  is a function that we hope to determine. Admittedly, it is not easy to completely motivate the fact that  $\Gamma_D(t,x)$  should look like (2.0.32). We first note that since we would like to achieve  $\int_{\mathbb{R}} \Gamma_D(t,x) = 1$ , the change of variables (2.0.31) leads to the following identity:

(2.0.33) 
$$1 = \int_{\mathbb{R}} \Gamma_D(t, x) \int_{\mathbb{R}} \frac{1}{\sqrt{Dt}} V\left(\frac{x}{\sqrt{Dt}}\right) dx = \int_{\mathbb{R}} V(\zeta) d\zeta.$$

Next, since  $\Gamma_D(t,x)$  is assumed to solve the heat equation, we calculate that

$$(2.0.34) 0 = \partial_t \Gamma - \Delta \Gamma = -\frac{1}{2} D^{-1/2} t^{-3/2} \left\{ V''(\zeta) + \frac{1}{2} \zeta V'(\zeta) + \frac{1}{2} V(\zeta) \right\}.$$

Therefore, V must be a solution to the following ODE:

(2.0.35) 
$$V''(\zeta) + \frac{1}{2}\zeta V'(\zeta) + \frac{1}{2}V(\zeta) = 0.$$

Since we want  $\Gamma_D(t,x)$  to behave like the  $\delta$  distribution (at least for small t>0), we demand that

$$(2.0.36) V(\zeta) \ge 0.$$

Furthermore, since we want  $\Gamma_D(t,x)$  to rapidly decay as  $|x|\to\infty$ , we demand that

$$(2.0.37) V(\pm \infty) = 0.$$

We also expect that ideally,  $V(\zeta)$  should be an even function. Furthermore, it is easy to see that if  $V(\zeta)$  is a solution to (2.0.35), then so is  $W(\zeta) \stackrel{\text{def}}{=} V(-\zeta)$ . Thus, it is reasonable to look for an even solution. Now for any differentiable even function  $V(\zeta)$ , it necessarily follows that V'(0) = 0. Thus, we demand that

$$(2.0.38) V'(0) = 0.$$

We now note that (2.0.35) can be written in the form

(2.0.39) 
$$\frac{d}{d\zeta}(V'(\zeta) + \frac{1}{2}\zeta V(\zeta)) = 0,$$

which implies that  $V'(\zeta) + \frac{1}{2}\zeta V(\zeta)$  is constant. By setting  $\zeta = 0$  in and using (2.0.38), we see that this constant is 0:

(2.0.40) 
$$V'(\zeta) + \frac{1}{2}\zeta V(\zeta) = 0.$$

Now the first-order ODE (2.0.40) can be written in the form

(2.0.41) 
$$\frac{d}{d\zeta} \ln V(\zeta) = -\frac{1}{2}\zeta,$$

which can be easily integrated as follows:

(2.0.42) 
$$\ln\left(\frac{V(\zeta)}{V(0)}\right) = -\frac{1}{4}\zeta^2,$$

(2.0.43) 
$$\implies V(\zeta) = V(0)e^{-\frac{1}{4}\zeta^2}.$$

To find V(0), we use the relation (2.0.33), and the integral identity<sup>2</sup>

(2.0.44) 
$$1 = \int_{\mathbb{R}} V(0)e^{-\frac{1}{4}\zeta^2} d\zeta = 2V(0) \int_{\mathbb{R}} e^{-\alpha^2} d\alpha = 2V(0)\sqrt{\pi}.$$

Therefore,  $V(0) = \frac{1}{\sqrt{4\pi}}$ , and

(2.0.45) 
$$V(\zeta) = \frac{1}{\sqrt{4\pi}} e^{-\frac{1}{4}\zeta^2}.$$

Finally, from (2.0.32) and (2.0.45), we deduce that

(2.0.46) 
$$\Gamma_D(t,x) = \frac{1}{\sqrt{4\pi t}} e^{-\frac{x^2}{4t}}$$

as desired.

Let  $I \stackrel{\text{def}}{=} \int_{\mathbb{R}} e^{-x^2} dx$ . Then  $I^2 = \int_{\mathbb{R}} \int_{\mathbb{R}} e^{-(x^2+y^2)} dx dy$ , and by switching to polar coordinates, we have that  $I^2 = 2\pi \int_{r=0}^{\infty} r e^{-r^2} dr = \pi$ . Thus,  $I = \sqrt{\pi}$ .

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# MATH 18.152 COURSE NOTES - CLASS MEETING # 6

## 18.152 Introduction to PDEs, Fall 2011

# Class Meeting # 6: Laplace's and Poisson's Equations

Professor: Jared Speck

We will now study the Laplace and Poisson equations on a domain (i.e. open connected subset)  $\Omega \subset \mathbb{R}^n$ . Recall that

$$\Delta \stackrel{\text{def}}{=} \sum_{i=1}^{n} \partial_i^2.$$

The Laplace equation is

$$\Delta u(x) = 0, \qquad x \in \Omega,$$

while the Poisson equation is the inhomogeneous equation

$$(0.0.3) \Delta u(x) = f(x).$$

Functions  $u \in C^2(\Omega)$  verifying (0.0.2) are said to be *harmonic*. (0.0.2) and (0.0.3) are both second order, linear, constant coefficient PDEs. As in our study of the heat equation, we will need to supply some kind of boundary conditions to get a well-posed problem. But unlike the heat equation, there is no "timelike" variable, so there is no "initial condition" to specify!

#### 1. Where does it come from?

1.1. **Basic examples.** First example: set  $\partial_t u \equiv 0$  in the heat equation, and (0.0.2) results. These solutions are known as *steady state solutions*.

Second example: We start with Maxwell equations from electrodynamics. The quantities of interest are

- $\mathbf{E} = (E_1(t, x, y, z), E_2(t, x, y, z), E_3(t, x, y, z))$  is the electric field
- $\mathbf{B} = (B_1(t, x, y, z), B_2(t, x, y, z), B_3(t, x, y, z))$  is the magnetic induction
- $\mathbf{J} = (J_1(t, x, y, z), J_2(t, x, y, z), J_3(t, x, y, z))$  is the current density
- $\rho$  is the charge density

Maxwell's equations are

(1.1.1) 
$$\partial_t \mathbf{E} - \nabla \times \mathbf{B} = -\mathbf{J}, \qquad \nabla \cdot \mathbf{E} = \rho,$$

(1.1.2) 
$$\partial_t \mathbf{B} + \nabla \times \mathbf{E} = 0,$$
  $\nabla \cdot \mathbf{B} = 0.$ 

Recall that  $\nabla \times$  is the curl operator, so that e.g.  $\nabla \times \mathbf{B} = (\partial_y B_3 - \partial_z B_2, \partial_z B_1 - \partial_x B_3, \partial_x B_2 - \partial_y B_1)$ . Let's look for steady-state solutions with  $\partial_t \mathbf{E} = \partial_t \mathbf{B} \equiv 0$ . Then equation (1.1.2) implies that

$$(1.1.3) \qquad \nabla \times \mathbf{E} = 0,$$

so that by the Poincaré lemma, there exists a scalar-valued function  $\phi(x,y,z)$  such that

(1.1.4) 
$$\mathbf{E}(x, y, z) = -\nabla \phi(x, y, z).$$

The function  $\phi$  is called an *electric potential*. Plugging (1.1.4) into the second of (1.1.1), and using the identity  $\nabla \cdot \nabla \phi = \Delta \phi$ , we deduce that

$$(1.1.5) \qquad \Delta\phi(x,y,z) = -\rho(x,y,z).$$

This is exactly the Poisson equation (0.0.3) with inhomogeneous term  $f = -\rho$ . Thus, Poisson's equation is at the heart of electrostatics.

1.2. Connections to complex analysis. Let z = x + iy (where  $x, y \in \mathbb{R}$ ) be a complex number, and let f(z) = u(z) + iv(z) be a complex-valued function (where  $u, v \in \mathbb{R}$ ). We recall that f is said to be differentiable at  $z_0$  if

(1.2.1) 
$$\lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0}$$

exists. If the limit exists, we denote it by  $f'(z_0)$ .

A fundamental result of complex analysis is the following: f is differentiable at  $z_0 = x_0 + iy_0 \simeq (x_0, y_0)$  if and only if the real and imaginary parts of f verify the Cauchy-Riemann equations at  $z_0$ :

$$(1.2.2) u_x(x_0, y_0) = v_y(x_0, y_0),$$

$$(1.2.3) u_y(x_0, y_0) = -v_x(x_0, y_0).$$

Differentiating (1.2.2) and using the symmetry of mixed partial derivatives (we are assuming here that u(x,y) and v(x,y) are  $C^1$  near  $(x_0,y_0)$ ), we have

(1.2.4) 
$$\Delta u \stackrel{\text{def}}{=} u_{xx} + u_{yy} = v_{yx} - v_{xy} = 0,$$

(1.2.5) 
$$\Delta v \stackrel{\text{def}}{=} v_{xx} + v_{yy} = -u_{yx} + u_{xy} = 0.$$

Thus, the real and imaginary parts of a complex-differentiable function are harmonic!

#### 2. Well-posed Problems

Much like in the case of the heat equation, we are interested in well-posed problems for the Laplace and Poisson equations. Recall that well-posed problems are problems that i) have a solution; ii)the solutions are unique; and iii)the solution varies continuously with the data.

Let  $\Omega \subset \mathbb{R}^n$  be a domain with a Lipschitz boundary, and let  $\hat{N}$  denote the unit outward normal vector to  $\partial\Omega$ . We consider the PDE

$$(2.0.6) \Delta u(x) = f(x), x \in \Omega,$$

supplemented by some boundary conditions. The following boundary conditions are known to lead to well-posed problems:

- (1) Dirichlet data: specify a function g(x) defined on  $\partial\Omega$  such that  $u|_{\partial\Omega}(x)=g(x)$ .
- (2) Neumann data: specify a function h(x) defined on  $\partial\Omega$  such that  $\nabla_{\hat{N}}u(x)|_{\partial\Omega}(x) = h(x)$ .
- (3) Robin-type data: specify a function h(x) defined on  $\partial\Omega$  such that  $\nabla_{\hat{N}}u(x)|_{\partial\Omega}(x) + \alpha u|_{\partial\Omega}(x) = h(x)$ , where  $\alpha > 0$  is a constant.
- (4) Mixed conditions: for example, we can divide  $\partial\Omega$  into two disjoint pieces  $\partial\Omega = S_D \cup S_N$ , where  $S_N$  is relatively open in  $\partial\Omega$ , and specify a function g(x) defined on  $S_D$  and a function h(x) defined on  $S_N$  such that  $u|_{S_D}(x) = g(x)$ ,  $\nabla_{\hat{N}} u|_{S_N}(x) = h(x)$ .
- (5) Conditions at infinity: When  $\Omega = \mathbb{R}^n$ , we can specify asymptotic conditions on u(x) as  $|x| \to \infty$ . We will return to this kind of condition later in the course.

### 3. Uniqueness via the Energy Method

In this section, we address the question of uniqueness for solutions to the equation (0.0.3), supplemented by suitable boundary conditions. As in the case of the heat equation, we are able to provide a simple proof based on the energy method.

**Theorem 3.1.** Let  $\Omega \subset \mathbb{R}^n$  be a smooth, bounded domain. Then under Dirichlet, Robin, or mixed boundary conditions, there is at most one solution of regularity  $u \in C^2(\Omega) \cap C^1(\overline{\Omega})$  to the Poisson equation (0.0.3).

In the case of Neumann conditions, any two solutions can differ by at most a constant.

*Proof.* If u and v are two solutions to (0.0.3) with the same boundary data, then we can subtract them (aren't linear PDEs nice?!...) to get a solution  $w \stackrel{\text{def}}{=} u - v$  to the Poisson equation with 0 data:

$$\Delta w = 0.$$

Let's perform the usual trick of multiplying (3.0.7) by w, integrating over  $\Omega$ , and integrating by parts via the divergence theorem:

$$(3.0.8) 0 = \int_{\Omega} w \Delta w \, d^n x = \int_{\Omega} w \nabla \cdot \nabla w \, d^n x = -\int_{\Omega} |\nabla w|^2 \, d^n x + \int_{\partial \Omega} w \nabla_{\hat{N}} w \, d\sigma.$$

In the case of Dirichlet data,  $w|_{\partial\Omega} = 0$ , so the last term in (3.0.8) vanishes. Thus, in the Dirichlet case, we have that

$$(3.0.9) \qquad \int_{\Omega} |\nabla w|^2 = 0.$$

Thus,  $\nabla w = 0$  in  $\Omega$ , and so w is constant in  $\overline{\Omega}$ . Since w is 0 on  $\partial\Omega$ , we have that  $w \equiv 0$  in  $\overline{\Omega}$ , which shows that  $u \equiv v$  in  $\overline{\Omega}$ .

Similarly, in the Robin case

(3.0.10) 
$$\int_{\partial\Omega} w \nabla_{\hat{N}} w \, d\sigma = -\alpha \int_{\partial\Omega} w^2 \, d\sigma \le 0,$$

which implies that

$$(3.0.11) \qquad \int_{\Omega} |\nabla w|^2 = 0,$$

and we can argue as before conclude that  $w \equiv 0$  in  $\overline{\Omega}$ .

Now in the Neumann case, we have that  $\nabla_{\hat{N}} w|_{\partial\Omega} = 0$ , and we can argue as above to conclude that w is constant in  $\overline{\Omega}$ . But now we can't say anything about the constant, so the best we can conclude is that u = v + constant in  $\overline{\Omega}$ .

### 4. Mean value properties

Harmonic functions u have some amazing properties. Some of the most important ones are captured in the following theorem, which shows that the pointwise values of u can be determined by its average over solid balls or their boundaries.

**Theorem 4.1** (Mean value properties). Let u(x) be harmonic in the domain  $\Omega \subset \mathbb{R}^n$ , and let  $B_R(x) \subset \Omega$  be a ball of radius R centered at the point x. Then the following mean value formulas hold:

(4.0.12a) 
$$u(x) = \frac{n}{\omega_n R^n} \int_{B_R(x)} u(y) \, d^n y,$$

(4.0.12b) 
$$u(x) = \frac{1}{\omega_n R^{n-1}} \int_{\partial B_R(x)} u(\sigma) d\sigma,$$

where  $\omega_n$  is the area of  $\partial B_1(0) \subset \mathbb{R}^n$ , that is, the area of the boundary of the unit ball in  $\mathbb{R}^n$ .

*Proof.* Let's address the n=2 case only; the proof is similar for other values of n. Let's also assume that x is the origin; as we will see, we will be able to treat the case of general x by reducing it to the origin. We will work with polar coordinates  $(r,\theta)$  on  $\mathbb{R}^2$ . For a ball of radius r, we have that the measure  $d\sigma$  corresponding to  $\partial B_r(0)$  is  $d\sigma = r d\theta$ . Note also that along  $\partial B_r(0)$ , we have that  $\partial_r u = \nabla u \cdot \hat{N} = \nabla_{\hat{N}} u$ , where  $\hat{N}(\sigma)$  is the unit normal to  $\partial B_r(0)$ . For any  $0 \le r < R$ , we define

(4.0.13) 
$$g(r) \stackrel{\text{def}}{=} \frac{1}{2\pi r} \int_{\partial B_r(0)} u(\sigma) d\sigma = \frac{1}{2\pi r} \int_{\theta=0}^{2\pi} r u(r,\theta) d\theta = \frac{1}{2\pi} \int_{\theta=0}^{2\pi} u(r,\theta) d\theta.$$

We now note that since u is continuous at 0, we have that

$$(4.0.14) u(0) = \lim_{r \to 0^+} g(r).$$

Thus, we would obtain (4.0.12b) in the case x = 0 if we could show that g'(r) = 0. Let's now show this. To this end, we calculate that

$$(4.0.15) g'(r) = \frac{1}{2\pi} \int_{\theta=0}^{2\pi} \partial_r u(r,\theta) d\theta = \frac{1}{2\pi} \int_{\theta=0}^{2\pi} \nabla_{\hat{N}} u(r,\theta) d\theta = \frac{1}{2\pi} \int_{\partial B_1(0)} \nabla_{\hat{N}(\sigma)} u(\sigma) d\sigma.$$

By the divergence theorem, this last term is equal to

(4.0.16) 
$$\frac{1}{2\pi} \int_{B_1(0)} \Delta u(y) \, d^2 y.$$

But  $\Delta u = 0$  since u is harmonic, so we have shown that

$$(4.0.17) g'(r) = 0,$$

and we have shown (4.0.12b) for x = 0.

To prove (4.0.12a), we use polar coordinate integration and (4.0.12b) (in the case x = 0) to obtain

$$(4.0.18) u(0)R^2/2 = \int_0^R ru(0) dr = \frac{1}{2\pi} \int_0^R \int_{\theta=0}^{2\pi} ru(r,\theta) d\theta dr = \frac{1}{2\pi} \int_{B_R(0)} u(y) d^2y.$$

We have now shown (4.0.12a) and (4.0.12b) when x = 0.

To obtain the corresponding formulas for non-zero x, define  $v(y) \stackrel{\text{def}}{=} u(x+y)$ , and note that  $\Delta_y v(y) = (\Delta_y u)(x+y) = 0$ . Therefore, using what we have already shown,

$$(4.0.19) u(x) = v(0) = \frac{2}{\omega_n R^2} \int_{B_R(0)} v(y) d^2y = \frac{2}{\omega_2 R^2} \int_{B_R(0)} u(x+y) d^2y = \frac{2}{\omega_2 R^2} \int_{B_R(x)} u(y) d^2y,$$

which implies (4.0.12a) for general x. We can similarly obtain (4.0.12b) for general x.

#### 5. Maximum Principle

Let's now discuss another amazing property verified by harmonic functions. The property, known as the *strong maximum principle*, says that most harmonic functions achieve their maximums and minimums only on the interior of  $\Omega$ . The only exceptions are the constant functions.

**Theorem 5.1** (Strong Maximum Principle). Let  $\Omega \subset \mathbb{R}^n$  be a domain, and assume that  $u \in C(\Omega)$  verifies the mean value property (4.0.12a). Then if u achieves its max or min at a point  $p \in \Omega$ , then u is constant on  $\Omega$ . Therefore, if  $\Omega$  is bounded and  $u \in C(\overline{\Omega})$  is not constant, then for every  $x \in \Omega$ , we have

(5.0.20) 
$$u(x) < \max_{y \in \partial \Omega} u(y), \qquad u(x) > \min_{y \in \partial \Omega} u(y).$$

*Proof.* We give the argument for the "min" in the case n = 2. Suppose that u achieves its min at a point  $p \in \Omega$ , and that u(p) = m. Let  $B(p) \subset \Omega$  be any ball centered at p, and let z be any point in B(p). Choose a small ball  $B_r(z)$  of radius r centered z with  $B_r(z) \subset B(p)$ .

Note that by the definition of a min, we have that

$$(5.0.21) u(z) \ge m.$$

Using the assumption that the mean value property (4.0.12a) holds, we conclude that

$$(5.0.22)$$

$$m = \frac{1}{|B(p)|} \int_{B(p)} u(y) d^2y = \frac{1}{|B(p)|} \left\{ \int_{B_r(z)} u(y) d^2y + \int_{B \setminus B_r(z)} u(y) d^2y \right\}$$

$$= \frac{1}{|B(p)|} \left\{ |B_r(z)|u(z) + \int_{B \setminus B_r(z)} u(y) d^2y \right\} \ge \frac{1}{|B(p)|} \left\{ |B_r(z)|u(z) + m(|B(p)| - |B_r(z)|) \right\}.$$

Rearranging inequality (5.0.22), we conclude that

$$(5.0.23) u(z) \le m.$$

Combining (5.0.21) and (5.0.23), we conclude that

$$(5.0.24) u(x) = m$$

holds for all points  $x \in B(p)$ . Therefore, u is locally constant at any point where it achieves its min. Since  $\Omega$  is open and connected, we conclude that u(x) = m for all  $x \in \Omega$ .

The next corollary will allow us to compare the size of two solutions to Poisson's equation if we have information about the size of the source terms and about the values of the solutions on  $\partial\Omega$ . The proof is based on Theorem 5.1.

Corollary 5.0.1. Let  $\Omega \subset \mathbb{R}^n$  be a bounded domain and let  $f \in C(\Omega)$ . Then the PDE

(5.0.25) 
$$\begin{cases} \Delta u = 0, & x \in \Omega, \\ u(x) = f(x), & x \in \partial\Omega, \end{cases}$$

has at most one solution  $u_f \in C^2(\Omega) \cap C(\overline{\Omega})$ . Furthermore, if  $u_f$  and  $u_g$  are the solutions corresponding to the data  $f, g \in C(\Omega)$ , then

(1) (Comparison Principle) If  $f \ge g$  on  $\partial \Omega$  and  $f \ne g$ , then

$$u_f > u_q$$
 in  $\Omega$ .

(2) (**Stability Estimate**) For any  $x \in \Omega$ , we have that

$$|u_f(x) - u_g(x)| \le \max_{y \in \partial\Omega} |f(y) - g(y)|.$$

*Proof.* We first prove the Comparison Principle. Let  $w = u_f - u_q$ . Then by subtracting the PDEs, we see that w solves

(5.0.26) 
$$\begin{cases} \Delta w = 0, & x \in \Omega, \\ u(x) = f(x) - g(x) \ge 0, & x \in \partial\Omega, \end{cases}$$

Since w is harmonic, since  $f(x) - g(x) \ge 0$  on  $\partial \Omega$ , and since  $f \ne g$ , Theorem 5.1 implies that w is not constant and that for every  $x \in \Omega$ , we have

$$(5.0.27) w(x) > \max_{y \in \partial \Omega} f(y) - g(y) \ge 0.$$

This proves the Comparison Principle.

For the Stability Estimate, we perform a similar argument for both  $\pm w$ , which leads to the estimates

(5.0.28) 
$$w(x) > -\max_{y \in \partial\Omega} |f(y) - g(y)|$$

(5.0.28) 
$$w(x) > -\max_{y \in \partial \Omega} |f(y) - g(y)|,$$
(5.0.29) 
$$-w(x) > -\max_{y \in \partial \Omega} |f(y) - g(y)|.$$

Combining (5.0.28) and (5.0.29), we deduce the Stability Estimate.

The "at most one" statement of the corollary now follows directly from applying the Stability Estimate to w in the case f = g.  18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# MATH 18.152 COURSE NOTES - CLASS MEETING # 7

# 18.152 Introduction to PDEs, Fall 2011

Class Meeting # 7: The Fundamental Solution and Green Functions

Professor: Jared Speck

# 1. The Fundamental Solution for $\Delta$ in $\mathbb{R}^n$

Here is a situation that often arises in physics. We are given a function f(x) on  $\mathbb{R}^n$  representing the spatial density of some kind of quantity, and we want to solve the following equation:

$$\Delta u(x) = f(x), \qquad x = (x^1, \dots, x^n) \in \mathbb{R}^n.$$

Furthermore, we often want to impose the following decay condition as  $|x| \to \infty$ :

$$(1.0.2) |u(x)| \to 0.$$

For technical reasons, we will need a different condition in the case n = 2. A good physical example is the theory of electrostatics, in which u(x) is the electric potential<sup>1</sup>, and f(x) is the charge density. f(x) could be e.g a compactly supported function modeling the charge density of a charged star, and we might want to know how the potential behaves far away from the star (i.e. as  $|x| \to \infty$ ). Roughly speaking, the decay conditions (1.0.2) are physically motivated by the fact that the star should not have a large effect on far-away locations.

As we will soon see, the PDE (1.0.1) has a unique solution verifying (1.0.2) as long as f(x) is sufficiently differentiable and decays sufficiently rapidly as  $|x| \to \infty$ . Much like in the case of the heat equation, we will be able to construct the solution using an object called the *fundamental solution*.

**Definition 1.0.1.** The fundamental solution  $\Phi$  corresponding to the operator  $\Delta$  is

(1.0.3) 
$$\Phi(x) \stackrel{\text{def}}{=} \begin{cases} \frac{1}{2\pi} \ln|x| & n = 2, \\ -\frac{1}{\omega_n |x|^{n-2}} & n \ge 3, \end{cases}$$

where as usual  $|x| \stackrel{\text{def}}{=} \sqrt{\sum_{i=1}^{n} (x^{i})^{2}}$  and  $\omega_{n}$  is the surface area of a unit ball in  $\mathbb{R}^{n}$  (e.g.  $\omega_{3} = 4\pi$ ).

**Remark 1.0.1.** Some people prefer to define their  $\Phi$  to be the negative of our  $\Phi$ .

Essentially, our goal in this section is to show that  $\Delta\Phi(x) = \delta(x)$ , where  $\delta$  is the delta distribution. Let's assume that this holds for now. We then claim that the solution to (1.0.1) is  $u(x) = f * \Phi(x) = \int_{\mathbb{R}^n} f(y) \Phi(x-y) d^n y$ . This can be heuristically justified by the following heuristic computations:  $\Delta_x(f * \Phi) = f * \Delta_x \Phi = f * \delta = f(x)$ .

Let's now make rigorous sense of this. We first show that away from the origin, the fundamental solution verifies Laplace's equation.

**Lemma 1.0.1.** If  $x \neq 0$ , then  $\Delta \Phi(x) = 0$ .

<sup>&</sup>lt;sup>1</sup>Recall that the the force **F** associated to u is  $\mathbf{F} = -\nabla u$ .

*Proof.* Let's do the proof in the case n=3. Note that  $\Phi(x)=\Phi(r)$   $(r\stackrel{\text{def}}{=}|x|)$  is spherically symmetric. Thus, using the fact that  $\Delta=\partial_r^2+\frac{2}{r}\partial_r$  when r>0 for spherically symmetric functions, we have that  $\Delta\Phi=\partial_r^2\Phi+\frac{2}{r}\partial_r\Phi=\frac{-2}{\omega_3r^4}+\frac{2}{\omega_3r^4}=0$ .

We are now ready to state and prove a rigorous version of the aforementioned heuristic results.

**Theorem 1.1** (Solution to Poisson's equation in  $\mathbb{R}^n$ ). Let  $f(x) \in C_0^{\infty}(\mathbb{R}^n)$  (i.e., f(x) is a smooth, compactly supported function on  $\mathbb{R}^n$ ). Then for  $n \geq 3$ , the Laplace equation  $\Delta u(x) = f(x)$  has a unique smooth solution u(x) that tends to 0 as  $|x| \to \infty$ . For n = 2, the solution is unique under the assumptions  $\frac{u(x)}{|x|} \to 0$  as  $|x| \to \infty$  and  $|\nabla u(x)| \to 0$  as  $|x| \to \infty$ . Furthermore, these unique solutions can be represented as

(1.0.4) 
$$u(x) = (\Phi * f)(x) = \begin{cases} \frac{1}{2\pi} \int_{\mathbb{R}^2} \ln|y| f(x-y) d^2 y, & n = 2, \\ -\frac{1}{\omega_n} \int_{\mathbb{R}^n} |y|^{n-2} f(x-y) d^n y, & n \ge 3. \end{cases}$$

Furthermore, there exist constants  $C_n > 0$  such that the following decay estimate holds for the solution as  $|x| \to \infty$ :

(1.0.5) 
$$|u(x)| \le \begin{cases} C_2 \ln|x| & n = 2, \\ \frac{C_n}{|x|^{n-2}} & n \ge 3. \end{cases}$$

**Remark 1.0.2.** As we alluded to above, Theorem 1.1 shows that  $\Delta\Phi(x) = \delta(x)$ , where  $\delta$  is the "delta distribution." For on the one hand, as we have previously discussed, we have that  $f = \delta * f$ . On the other hand, our proof of Theorem 1.1 below will show that  $f = \Delta u = \Delta(\Phi * f) = (\Delta\Phi) * f$ . Thus, for any f, we have  $\delta * f = (\Delta\Phi) * f$ , and so  $\Delta\Phi = \delta$ .

*Proof.* We consider only the case n = 3. Let's first show existence by checking that the function u defined in (1.0.4) solves the equation and has the desired properties. We first differentiate under the integral (we use one of our prior propositions to justify this) and use the fact that  $\Delta_x f(x-y) = \Delta_y f(x-y)$  (you can easily verify this with the chain rule) to derive

(1.0.6) 
$$\Delta_x u(x) = -\frac{1}{4\pi} \int_{\mathbb{R}^3} \frac{1}{|y|} \Delta_x f(x-y) d^3 y = -\frac{1}{4\pi} \int_{\mathbb{R}^3} \frac{1}{|y|} \Delta_y f(x-y) d^3 y.$$

To show that the right-hand side of (1.0.6) is equal to f(x), we will split the integral into two pieces: a small ball centered at the origin, and it's complement. Thus, let  $B_{\epsilon}(0)$  denote the ball of radius  $\epsilon$  centered at 0. We then split

$$(1.0.7) \Delta_x u(x) = -\frac{1}{4\pi} \int_{B_{\epsilon}(0)} \frac{1}{|y|} \Delta_y f(x-y) d^3y - \frac{1}{4\pi} \int_{B_{\epsilon}(0)} \frac{1}{|y|} \Delta_y f(x-y) d^3y \stackrel{\text{def}}{=} I + II.$$

We first show that I goes to 0 as  $\epsilon \to 0^+$ . To this end, let

(1.0.8) 
$$M \stackrel{\text{def}}{=} \sup_{y \in \mathbb{R}^3} |f(y)| + |\nabla f(y)| + |\Delta_y f(y)|.$$

Then using spherical coordinates  $(r,\omega)$  for the y variable, and recalling that  $d^3y = r^2 d\omega$  (where  $\omega \in \partial B_1(0) \subset \mathbb{R}^3$  is a point on the unit sphere and  $d\omega = \sin\theta d\theta d\phi$ ) in spherical coordinates, we have that

$$(1.0.9) |I| \le \int_{B_{\epsilon}(0)} \left| \frac{1}{|y|} \Delta_y f(x - y) \right| d^3 y \le M \int_{r=0}^{\epsilon} \int_{\partial B_1(0)} r \, d\omega \, dr = 2\epsilon^2 \pi M.$$

Clearly, the right-hand side of (1.0.9) goes to 0 as  $\epsilon \to 0^+$ .

We would now like to understand the second term on the right-hand side of (1.0.7). We claim that

$$(1.0.10) |f(x) - II| \to 0$$

as  $\epsilon \to 0^+$ . After we show this, we can combine (1.0.7), (1.0.9), and (1.0.10) and let  $\epsilon \to 0^+$  to deduce that  $\Delta_x u(x) = f(x)$  as desired.

To show (1.0.10), we will use integration by parts via *Green's identity* and simple estimates to control the boundary terms. Recall that Green's identity for two functions u, v is

$$(1.0.11) \qquad \int_{\Omega} v(x)\Delta u(x) - u(x)\Delta v(x) d^{n}x = \int_{\partial\Omega} v\nabla_{\hat{N}}u(\sigma) - u\nabla_{\hat{N}}v(\sigma) d\sigma.$$

Using (1.0.11) and Lemma 1.0.1, we compute that

(1.0.12)

$$\int_{B_{\epsilon}^{c}(0)} -\frac{1}{|y|} \Delta_{y} f(x-y) + f(x-y) \underbrace{\Delta_{y} \frac{1}{|y|}}_{0} d^{3}y = \int_{\partial B_{\epsilon}^{c}(0)} \frac{1}{|\sigma|} \nabla_{\hat{N}(\sigma)} f(x-\sigma) - f(x-\sigma) \nabla_{\hat{N}(\sigma)} \frac{1}{|\sigma|} d\sigma.$$

Above,  $\nabla_{\hat{N}(\sigma)}$  is the outward unit radial derivative on the sphere  $\partial B_{\epsilon}(0)$ . This corresponds to the "opposite" choice of normal that appears in the standard formulation of Green's identity for  $B_{\epsilon}^{c}(0)$ , but we have compensated for this by carefully inserting minus signs on the right-hand side of (1.0.12). Recalling also that  $\nabla_{\hat{N}(\sigma)} \frac{1}{|\sigma|} = -\frac{1}{|\sigma|^2}$ , that  $|\sigma| = \epsilon$  on  $\partial B_{\epsilon}^{c}(0)$ , and that  $d\sigma = \epsilon^2 d\omega$  on  $\partial B_{\epsilon}^{c}(0)$ , it follows that

$$(1.0.13) - \int_{B_{\varepsilon}^{c}(0)} \frac{1}{|y|} \Delta_{y} f(x-y) d^{3}y = - \int_{\partial B_{1}(0)} \epsilon \omega \cdot (\nabla f)(x-\epsilon \omega) d\omega + \int_{\partial B_{1}(0)} f(x-\epsilon \omega) d\omega.$$

Using (1.0.8), it follows that the first integral on the right-hand side of (1.0.13) is bounded by  $4\pi M\epsilon$ , and thus goes to 0 as  $\epsilon \to 0^+$ . Furthermore, since f is continuous and since  $\int_{\partial B_1(0)} 1 d\omega = 4\pi$ , it follows that the second integral converges to  $4\pi f(x)$  as  $\epsilon \to 0^+$ . We have thus proved (1.0.10) for n=3.

To estimate |u(x)| as  $|x| \to \infty$ , we assume that f(x) vanishes outside of the ball  $B_R(0)$ . It suffices to estimate right-hand side of (1.0.4) when |x| > 2R. We first note the inequality  $\frac{1}{|x-y|} \le \frac{2}{|x|}$ , which holds for  $|y| \le R$  and |x| > 2R. Using this inequality and (1.0.8), we can estimate right-hand side of (1.0.4) by

$$(1.0.14) |u(x)| = \frac{1}{4\pi} \Big| \int_{B_R(0)} \frac{1}{|x-y|} f(y) d^3y \Big| \le \frac{M}{2\pi |x|} \int_{B_R(0)} 1 d^3y = \frac{2R^3 M}{3|x|},$$

and we have shown (1.0.5) in the case n = 3.

To prove uniqueness, we will make use of Corollary 4.0.4, which we will prove later. Now if u, v are two solutions with the assumed decay conditions at  $\infty$ , then using the usual strategy, we note that  $w \stackrel{\text{def}}{=} u - v$  is a solution to the Laplace equation

$$(1.0.15) \qquad \Delta w = 0$$

that verifies  $|w(x)| \to 0$  as  $|x| \to \infty$ . In particular, w is a bounded harmonic function on  $\mathbb{R}^3$ . We will show in Corollary 4.0.4 below that w(x) must be a constant function. Furthermore, the constant must be 0 since  $|w(x)| \to 0$  as  $|x| \to \infty$ .

#### 2. Green functions for domains $\Omega$

Our goal in this section is to derive an analog of Theorem 1.1 on the interior of domains  $\Omega \subset \mathbb{R}^n$ . Specifically, we will study the boundary value Poisson problem

(2.0.16) 
$$\Delta u(x) = f(x), \qquad x \in \Omega \subset \mathbb{R}^n,$$
$$u(x) = g(x), \qquad x \in \partial \Omega.$$

**Theorem 2.1** (Basic existence theorem). Let g be a bounded Lipschitz domain, and let  $g \in C(\partial\Omega)$ . Then the PDE (2.0.16) has a unique solution  $u \in C^2(\Omega) \cap C(\overline{\Omega})$ .

*Proof.* This proof is a bit beyond this course.

**Definition 2.0.2.** Let  $\Omega \subset \mathbb{R}^n$  be a domain. A *Green function* in  $\Omega$  is defined to be a function of  $(x,y) \in \Omega \times \Omega$  verifying the following conditions for each fixed  $x \in \Omega$ :

(2.0.17) 
$$\Delta_y G(x, y) = \delta(x), \qquad y \in \Omega$$

(2.0.18) 
$$G(x,\sigma) = 0,$$
  $\sigma \in \partial \Omega.$ 

**Proposition 2.0.2.** Let  $\Phi$  be the fundamental solution (1.0.3) for  $\Delta$  in  $\mathbb{R}^n$ , and let  $\Omega \in \mathbb{R}^n$  be a domain. Then the Green function G(x,y) for  $\Omega$  can be decomposed as

(2.0.19) 
$$G(x,y) = \Phi(x-y) - \phi(x,y),$$

where for each  $x \in \Omega$ ,  $\phi(x,y)$  solves the Dirichlet problem

$$(2.0.20) \Delta_y \phi(x, y) = 0, y \in \Omega,$$

(2.0.21) 
$$\phi(x,\sigma) = \Phi(x-\sigma), \qquad \sigma \in \partial\Omega.$$

*Proof.* As we have previously discussed,  $\Delta \Phi = \delta$ . Also using (2.0.20), we compute that

$$(2.0.22) \Delta_y \left( \Phi(x-y) - \phi(x,y) \right) = \Delta_y \Phi(x-y) - \Delta_y \phi(x,y) = \delta(x-y).$$

Therefore,  $\Phi(x-y) - \phi(x,y)$  verifies equation (2.0.17).

Furthermore, using (2.0.21), we have that  $\Phi(x-\sigma) - \phi(x,\sigma) = 0$  whenever  $\sigma \in \partial\Omega$ . Thus,  $\Phi(x-y) - \phi(x,y)$  also verifies the boundary condition (2.0.18).

The following technical proposition will play later in this section when we derive representation formulas for solutions to (2.0.16) in terms of Green functions.

**Proposition 2.0.3** (Representation formula for u). Let  $\Phi$  be the fundamental solution (1.0.3) for  $\Delta$  in  $\mathbb{R}^n$ , and let  $\Omega \subset \mathbb{R}^n$  be a domain. Assume that  $u \in C^2(\overline{\Omega})$ . Then for every  $x \in \Omega$ , we have the following representation formula for u(x):

$$(2.0.23) \quad u(x) = \int_{\Omega} \Phi(x - y) \Delta_y u(y) \, d^n y - \underbrace{\int_{\partial \Omega} \Phi(x - \sigma) \nabla_{\hat{N}(\sigma)} u(\sigma) \, d\sigma}_{single \ layer \ potential} + \underbrace{\int_{\partial \Omega} u(\sigma) \nabla_{\hat{N}(\sigma)} \Phi(x - \sigma) \, d\sigma}_{double \ layer \ potential}.$$

*Proof.* We'll do the proof for n=3, in which case  $\Phi(x)=-\frac{1}{4\pi|x|}$ . We will also make use of Green's identity (1.0.11). Let  $B_{\epsilon}(x)$  be a ball of radius  $\epsilon$  centered at x, and let  $\Omega_{\epsilon} \stackrel{\text{def}}{=} \Omega \backslash B_{\epsilon}(x)$ . Note that  $\partial \Omega_{\epsilon} = \partial \Omega \cup -\partial B_{\epsilon}(x)$ . Using (1.0.11), we compute that

$$(2.0.24) \qquad \int_{\Omega_{\epsilon}} \frac{1}{|x-y|} \Delta u(y) \, d^{3}y = \int_{\partial\Omega_{\epsilon}} \frac{1}{|x-\sigma|} \nabla_{\hat{N}} u(\sigma) - u(\sigma) \nabla_{\hat{N}} \Big( \frac{1}{|x-\sigma|} \Big) \, d\sigma$$

$$= \int_{\partial\Omega} \frac{1}{|x-\sigma|} \nabla_{\hat{N}} u(\sigma) \, d\sigma - \int_{\partial\Omega} u(\sigma) \nabla_{\hat{N}} \Big( \frac{1}{|x-\sigma|} \Big) \, d\sigma$$

$$- \int_{\partial B_{\epsilon}(x)} \frac{1}{|x-\sigma|} \nabla_{\hat{N}} u(\sigma) \, d\sigma + \int_{\partial B_{\epsilon}(x)} u(\sigma) \nabla_{\hat{N}} \Big( \frac{1}{|x-\sigma|} \Big) \, d\sigma.$$

In the last two integrals above,  $\hat{N}(\sigma)$  denotes the radially outward unit normal to the boundary of the ball  $B_{\epsilon}(x)$ . This corresponds to the "opposite" choice of normal that appears in the standard formulation of Green's identity, but we have compensated by adjusting the signs in front of the integrals.

Let's symbolically write (2.0.24) as

$$(2.0.25) L = R1 + R2 + R3 + R4.$$

Our goal is to show that as  $\epsilon \downarrow 0$ , the following limits are achieved:

- $L \to -4\pi \int_{\Omega} \Phi(x-y) \Delta_y u(y) d^3y$
- $R1 \rightarrow 4\pi \times \text{single layer potential}$
- $R2 \rightarrow -4\pi \times double layer potential$
- $R3 \rightarrow 0$
- $R4 \rightarrow -4\pi u(x)$ .

Once we have calculated the above limits, (2.0.23) then follows from simple algebraic rearranging. We first address L. Let  $M = \max_{u \in \Omega} \Delta u(y)$ . We then estimate

$$\left| \int_{\Omega} \frac{1}{|x-y|} \Delta u(y) d^3y - \int_{\Omega_{\epsilon}} \frac{1}{|x-y|} \Delta u(y) d^3y \right| \leq \int_{B_{\epsilon}(x)} \frac{1}{|x-y|} |\Delta u(y)| d^3y$$

$$\leq M \int_{B_{\epsilon}(x)} \frac{1}{|x-y|} d^3y \to 0 \text{ as } \epsilon \downarrow 0.$$

This shows that L converges to  $\int_{\Omega} \frac{1}{|x-y|} \Delta u(y) d^3y$  as  $\epsilon \downarrow 0$ .

The limits for R1 and R2 are obvious since these terms do not depend on  $\epsilon$ .

We now address R3. To this end, Let  $M' = \max_{y \in \overline{\Omega}} |\nabla u(y)|$ . We then estimate R3 by

$$|R3| \leq \int_{\partial B_{\epsilon}(x)} \left| \frac{1}{|x - \sigma|} \nabla_{\hat{N}} u(\sigma) \right| d\sigma \leq \int_{\partial B_{\epsilon}(x)} \frac{1}{\epsilon} M' d\sigma = \underbrace{4\pi \epsilon^{2}}_{\text{surface area of } \partial B_{\epsilon}(x)} \times \epsilon^{-1} M' \to 0 \text{ as } \epsilon \downarrow 0.$$

We now address R4. Using spherical coordinates  $(r, \theta, \phi) \in [0, \infty) \times [0, \pi) \times [0, 2\pi)$  centered at x, we have that  $d\sigma = r^2 \sin \theta \, d\theta \, d\phi$ . Therefore,  $\int_{\partial B_{\epsilon}(x)} \frac{1}{|x-\sigma|^2} \, d\sigma = \int_{\phi \in [0,2\pi]} \int_{\theta \in [0,\pi]} 1 \, d\theta \, d\phi = 4\pi$ . We now estimate

$$(2.0.28) \qquad \left| \frac{1}{4\pi} R4 - \left[ -u(x) \right] \right| = \left| u(x) + \frac{1}{4\pi} \int_{\partial B_{\epsilon}(x)} u(\sigma) \nabla_{\hat{N}(\sigma)} \left( \frac{1}{|x - \sigma|} \right) d\sigma \right|$$

$$= \frac{1}{4\pi} \left| \int_{\partial B_{\epsilon}(x)} \left( u(x) - u(\sigma) \right) \left( \frac{1}{|x - \sigma|^2} \right) d\sigma \right|$$

$$\leq \frac{1}{4\pi} \int_{\partial B_{\epsilon}(x)} |u(x) - u(\sigma)| \left( \frac{1}{|x - \sigma|^2} \right) d\sigma$$

$$\leq \frac{1}{4\pi} \max_{\sigma \in \partial B_{\epsilon}(x)} |u(x) - u(\sigma)| \int_{\partial B_{\epsilon}(x)} \left( \frac{1}{|x - \sigma|^2} \right) d\sigma$$

$$\leq \max_{\sigma \in \partial B_{\epsilon}(x)} |u(x) - u(\sigma)| \to 0 \text{ as } \epsilon \downarrow 0.$$

This shows that  $R4 \rightarrow -4\pi u(x)$  as  $\epsilon \downarrow 0$ .

Theorem 2.2 (Representation formula for solutions to the boundary value Poisson equation). The solution u to (2.0.16) can be represented as

(2.0.29) 
$$u(x) = -\int_{\Omega} f(y)G(x,y) d^{n}y - \int_{\partial\Omega} g(\sigma) \underbrace{\nabla_{\hat{N}}G(x,\sigma)}_{Poisson \ kernel} d\sigma.$$

*Proof.* Applying Proposition 2.0.3, we have that

$$(2.0.30) \quad u(x) = -\int_{\Omega} \Phi(x-y) f(y) \, d^n y + \int_{\partial \Omega} \Phi(x-\sigma) \nabla_{\hat{N}(\sigma)} u(\sigma) \, d\sigma - \int_{\partial \Omega} g(\sigma) \nabla_{\hat{N}(\sigma)} \Phi(x-\sigma) \, d\sigma.$$

Recall also that

(2.0.31) 
$$G(x,y) = \Phi(x-y) - \phi(x,y)$$

(2.0.32) 
$$G(x,\sigma) = 0 \text{ when } \sigma \in \partial \Omega.$$

Applying the Green identity (1.0.11) to the functions u(y) and  $\phi(x,y)$ , and recalling that  $\Delta_y \phi(x,y) = 0$  for each fixed  $x \in \Omega$ , we have that

$$(2.0.33) 0 = \int_{\Omega} \phi(x,y) \overbrace{f(y)}^{\Delta u(y)} d^{n}y - \int_{\partial \Omega} \overbrace{\phi(x,\sigma)}^{\Phi(x-\sigma)} \nabla_{\hat{N}} u(\sigma) d\sigma + \int_{\partial \Omega} \overbrace{g(\sigma)}^{u(\sigma)} \nabla_{\hat{N}} \phi(x,\sigma) d\sigma.$$

Adding (2.0.30) and (2.0.33), and using (2.0.31), we deduce the formula (2.0.29).

## 3. Poisson's Formula

Let's compute the Green function G(x,y) and Poisson kernel  $P(x,\sigma) \stackrel{\text{def}}{=} -\nabla_{\hat{N}} G(x,\sigma)$  from (2.0.29) in the case that  $\Omega \stackrel{\text{def}}{=} B_R(0) \subset \mathbb{R}^3$  is a ball of radius R centered at the origin. We'll use a technique called the *method of images* that works for special domains.

Warning 3.0.1. Brace yourself for a bunch of tedious computations that at the end of the day will lead to a very nice expression.

The basic idea is to hope that  $\phi(x,y)$  from (2.0.19), viewed as a potential that depends on y, is equal to the potential generated by some "imaginary charge" q placed at a point  $x^* \in \Omega^c$ . To ensure that property (2.0.18) holds, q and  $x^*$  have to be chosen so that along the boundary  $\{y \in \mathbb{R}^3 \mid |y| = R\}$ ,  $\phi(x,y) = \frac{1}{4\pi|x-y|}$ . In a nutshell, we guess that

(3.0.34) 
$$G(x,y) = \frac{1}{4\pi|x-y|} - \frac{q}{4\pi|x^*-y|},$$

and we try to solve for q and  $x^*$  so that G(x,y) vanishes when |y| = R. Thus, when |y| = R, we must have

(3.0.35) 
$$\frac{1}{4\pi|x-y|} = \frac{q}{4\pi|x^*-y|}.$$

$$(3.0.36) |x^* - y|^2 = q^2|x - y|^2.$$

$$(3.0.37) |x|^2 - 2x \cdot y + R^2 = |x - y|^2 = q^2 |x^* - y|^2 = q^2 (|x^*|^2 - 2x^* \cdot y + R^2).$$

Then performing simple algebra, we have

$$|x^*|^2 + R^2 - q^2(R^2 + |x|^2) = 2y \cdot (x^* - q^2x).$$

Now since the left-hand side of (3.0.38) does not depend on y, it must be the case that the second term on the right-hand side vanishes. This implies that  $x^* = q^2x$ , and also leads to the equation

$$(3.0.39) q4|x|2 - q2(R2 + |x|2) + R2 = 0.$$

Solving (3.0.39) for q, we finally have that

$$(3.0.40) q = \frac{R}{|x|},$$

$$(3.0.41) x^* = \frac{R^2}{|x|^2} x.$$

Therefore,

(3.0.42) 
$$\phi(x,y) = \frac{1}{4\pi} \frac{R}{|x| \left| \frac{R^2}{|x|^2} x - y \right|},$$

(3.0.43) 
$$\phi(0,y) = \frac{1}{R},$$

where we took a limit as  $x \to 0$  in (3.0.42) to derive (3.0.43).

Next, using (3.0.34), we have

(3.0.44) 
$$G(x,y) = \frac{1}{4\pi|x-y|} - \frac{1}{4\pi} \frac{R}{|x| \frac{R^2}{|x|^2} x - y|}, \qquad x \neq 0,$$

(3.0.45) 
$$G(0,y) = \frac{1}{4\pi|y|} - \frac{1}{R}.$$

(3.0.46) 
$$\nabla_y G(x,y) = \frac{x-y}{4\pi |x-y|^3} - \frac{1}{4\pi} \frac{R}{|x|} \frac{x^* - y}{|x^* - y|^3}$$

Now when  $\sigma \in \partial B_R(0)$ , (3.0.36) and (3.0.40) imply that

(3.0.47) 
$$|x^* - \sigma| = \frac{R}{|x|} |x - \sigma|.$$

Therefore, using (3.0.46) and (3.0.47), we compute that

(3.0.48) 
$$\nabla_{\sigma}G(x,\sigma) = \frac{x-\sigma}{4\pi|x-\sigma|^3} - \frac{1}{4\pi} \frac{|x|^2}{R^2} \frac{x^*-\sigma}{|x-\sigma|^3} = \frac{x-\sigma}{4\pi|x-\sigma|^3} - \frac{1}{4\pi} \frac{|x|^2}{R^2} \frac{\frac{R^2}{|x|^2} x - \sigma}{|x-\sigma|^3} = \frac{-\sigma}{4\pi|x-\sigma|^3} \left(1 - \frac{|x|^2}{R^2}\right).$$

Using (3.0.48) and the fact that  $\hat{N}(\sigma) = \frac{\sigma}{R}$ , we deduce

(3.0.49) 
$$\nabla_{\hat{N}(\sigma)} G(x,\sigma) \stackrel{\text{def}}{=} \nabla_{\sigma} G(x,\sigma) \cdot \hat{N}(\sigma) = \frac{R^2 - |x|^2}{4\pi R} \frac{1}{|x-\sigma|^3}.$$

**Remark 3.0.3.** If the ball were centered at the point  $p \in \mathbb{R}^3$  instead of the origin, then the formula (3.0.49) would be replaced with

(3.0.50) 
$$\nabla_{\hat{N}(\sigma)} G(x,\sigma) \stackrel{\text{def}}{=} \nabla_{\sigma} G(x,\sigma) \cdot \hat{N}(\sigma) = \frac{R^2 - |x-p|^2}{4\pi R} \frac{1}{|x-\sigma|^3}.$$

**Theorem 3.1** (Poisson's formula). Let  $B_R(p) \subset \mathbb{R}^3$  be a ball of radius R centered at  $p = (p^1, p^2, p^3)$ , and let  $x = (x^1, x^2, x^3)$  denote a point in  $\mathbb{R}^3$ . Then the unique solution  $u \in C^2(B_R(p)) \cap C(\overline{B}_R(p))$  of the PDE

(3.0.51) 
$$\begin{cases} \Delta u = 0, & x \in \Omega, \\ u(x) = f(x), & x \in \partial \Omega, \end{cases}$$

can be represented using the Poisson formula:

(3.0.52) 
$$u(x) = \frac{R^2 - |x - p|^2}{4\pi R} \int_{\partial B_R(p)} \frac{f(\sigma)}{|x - \sigma|^3} d\sigma.$$

**Remark 3.0.4.** In n dimensions, the formula (3.0.52) gets replaced with

(3.0.53) 
$$u(x) = \frac{R^2 - |x - p|^2}{\omega_n R} \int_{\partial B_R(p)} \frac{f(\sigma)}{|x - \sigma|^n} d\sigma,$$

where as usual,  $\omega_n$  is the surface area of the unit ball in  $\mathbb{R}^n$ .

*Proof.* The identity (3.0.52) follows immediately from Theorem 2.2 and (3.0.50).

## 4. Harnack's inequality

**Theorem 4.1** (Harnack's inequality). Let u be harmonic and **non-negative** in the ball  $B_R(0) \subset \mathbb{R}^n$ . Then for any  $x \in B_R(0)$ , we have that

$$\frac{R^{n-2}(R-|x|)}{(R+|x|)^{n-1}}u(0) \le u(x) \le \frac{R^{n-2}(R+|x|)}{(R-|x|)^{n-1}}u(0).$$

*Proof.* We'll do the proof for n = 3. The basic idea is to combine the Poisson representation formula with simple inequalities and the mean value property. By Theorem 3.1, we have that

(4.0.55) 
$$u(x) = \frac{R^2 - |x|^2}{4\pi R} \int_{\partial B_R(0)} \frac{f(\sigma)}{|x - \sigma|^3} d\sigma.$$

By the triangle inequality, for  $\sigma \in \partial B_R(0)$  (i.e.  $|\sigma| = R$ ), we have that  $|x| - R \le |x - \sigma| \le |x| + R$ . Applying the first inequality to (4.0.55), and using the non-negativity of f, we deduce that

(4.0.56) 
$$u(x) \le \frac{R + |x|}{R^2 - |x|^2} \frac{1}{4\pi R} \int_{\partial B_R(0)} f(\sigma) d\sigma.$$

Now recall that by the mean value property, we have that

$$(4.0.57) u(0) = \frac{1}{4\pi R^2} \int_{\partial B_R(0)} f(\sigma) d\sigma.$$

Thus, combining (4.0.56) and (4.0.57), we have that

$$(4.0.58) u(x) \le \frac{R^{n-2}(R+|x|)}{(R-|x|)^{n-1}},$$

which implies one of the inequalities in (4.0.54). The other one can be proven similarly using the remaining triangle inequality.

Corollary 4.0.4 (Liouville's theorem). Suppose that  $u \in C^2(\mathbb{R}^n)$  is harmonic on  $\mathbb{R}^n$ . Suppose their exists a constant M such that  $u(x) \ge M$  for all  $x \in \mathbb{R}^n$ , or such that  $u(x) \le M$  for all  $x \in \mathbb{R}^n$ . Then u is constant.

*Proof.* We first consider the case that  $u(x) \ge M$ . Let  $v \stackrel{\text{def}}{=} u + |M|$ . Observe that  $v \ge 0$  is harmonic and verifies the hypotheses of Theorem 4.1. Thus, by (4.0.54), if  $x \in \mathbb{R}^n$  and R is sufficiently large, we have that

$$\frac{R^{n-2}(R-|x|)}{(R+|x|)^{n-1}}u(0) \le u(x) \le \frac{R^{n-2}(R+|x|)}{(R-|x|)^{n-1}}u(0).$$

Allowing  $R \to \infty$  in (4.0.59), we conclude that v(x) = v(0). Thus, v is a constant-valued function (and therefore u is too).

To handle the case  $u(x) \leq M$ , we simply consider the function  $w(x) \stackrel{\text{def}}{=} -u(x) + |M|$  in place of v(x), and we argue as above.

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## MATH 18.152 COURSE NOTES - CLASS MEETING # 8

## 18.152 Introduction to PDEs, Fall 2011

## Class Meeting #8: Green Functions

Professor: Jared Speck

## 1. Green functions for domains $\Omega$

Our goal in this section is to derive an integral representation formula for the solution to Poisson's equation on domains  $\Omega \subset \mathbb{R}^n$ . Specifically, we will study the boundary value Poisson PDE

(1.0.1) 
$$\Delta u(x) = f(x), \qquad x \in \Omega \subset \mathbb{R}^n,$$
$$u(x) = g(x), \qquad x \in \partial\Omega.$$

We first state a basic existence theorem.

**Theorem 1.1** (Basic existence theorem). Let g be a bounded Lipschitz domain, and let  $g \in C(\partial\Omega)$ . Then the PDE (1.0.1) has a unique solution  $u \in C^2(\Omega) \cap C(\overline{\Omega})$ .

*Proof.* This proof is a bit beyond this course.

We now define the basic object that will play the role of a fundamental solution on a domain  $\Omega$ .

**Definition 1.0.1.** Let  $\Omega \subset \mathbb{R}^n$  be a domain. A *Green function* in  $\Omega$  is defined to be a function of  $(x,y) \in \Omega \times \Omega$  verifying the following conditions for each fixed  $x \in \Omega$ :

(1.0.2) 
$$\Delta_y G(x,y) = \delta_x(y) \stackrel{\text{def}}{=} \delta(y-x), \qquad y \in \Omega,$$

(1.0.3) 
$$G(x,\sigma) = 0,$$
  $\sigma \in \partial \Omega.$ 

Let's now connect G(x,y) to  $\Phi(x-y)$ .

**Proposition 1.0.1.** Let  $\Phi$  be the fundamental solution for  $\Delta$  in  $\mathbb{R}^n$ , and let  $\Omega \in \mathbb{R}^n$  be a domain. Then the Green function G(x,y) for  $\Omega$  can be decomposed as

(1.0.4) 
$$G(x,y) = \Phi(x-y) - \phi(x,y),$$

where for each  $x \in \Omega$ ,  $\phi(x,y)$  solves the Dirichlet problem

$$\Delta_{\nu}\phi(x,y) = 0, y \in \Omega,$$

(1.0.6) 
$$\phi(x,\sigma) = \Phi(x-\sigma), \qquad \sigma \in \partial\Omega.$$

*Proof.* As we have previously discussed,  $\Delta \Phi = \delta$ . Also using (1.0.5), we compute that

$$(1.0.7) \Delta_y (\Phi(x-y) - \phi(x,y)) = \Delta_y \Phi(x-y) - \Delta_y \phi(x,y) = \delta(y-x).$$

Therefore,  $\Phi(x-y) - \phi(x,y)$  verifies equation (1.0.2).

Furthermore, using (1.0.6), we have that  $\Phi(x-\sigma) - \phi(x,\sigma) = 0$  whenever  $\sigma \in \partial\Omega$ . Thus,  $\Phi(x-y) - \phi(x,y)$  also verifies the boundary condition (1.0.3).

The following technical proposition will play later in this section when we derive representation formulas for solutions to (1.0.1) in terms of Green functions.

**Proposition 1.0.2** (Representation formula for u). Let  $\Phi$  be the fundamental solution for  $\Delta$  in  $\mathbb{R}^n$ , and let  $\Omega \subset \mathbb{R}^n$  be a domain. Assume that  $u \in C^2(\overline{\Omega})$ . Then for every  $x \in \Omega$ , we have the following representation formula for u(x):

$$(1.0.8) \quad u(x) = \int_{\Omega} \Phi(x - y) \Delta_y u(y) d^n y - \underbrace{\int_{\partial \Omega} \Phi(x - \sigma) \nabla_{\hat{N}(\sigma)} u(\sigma) d\sigma}_{single\ layer\ potential} + \underbrace{\int_{\partial \Omega} u(\sigma) \nabla_{\hat{N}(\sigma)} \Phi(x - \sigma) d\sigma}_{double\ layer\ potential}.$$

*Proof.* We'll do the proof for n = 3, in which case  $\Phi(x) = -\frac{1}{4\pi|x|}$ . We will also make use of Green's identity. Let  $B_{\epsilon}(x)$  be a ball of radius  $\epsilon$  centered at x, and let  $\Omega_{\epsilon} \stackrel{\text{def}}{=} \Omega \backslash B_{\epsilon}(x)$ . Note that  $\partial \Omega_{\epsilon} = \partial \Omega \cup -\partial B_{\epsilon}(x)$ . Using Green's identity, we compute that

$$(1.0.9) \qquad \int_{\Omega_{\epsilon}} \frac{1}{|x-y|} \Delta u(y) \, d^{3}y = \int_{\partial\Omega_{\epsilon}} \frac{1}{|x-\sigma|} \nabla_{\hat{N}} u(\sigma) - u(\sigma) \nabla_{\hat{N}} \left(\frac{1}{|x-\sigma|}\right) d\sigma$$

$$= \int_{\partial\Omega} \frac{1}{|x-\sigma|} \nabla_{\hat{N}} u(\sigma) \, d\sigma - \int_{\partial\Omega} u(\sigma) \nabla_{\hat{N}} \left(\frac{1}{|x-\sigma|}\right) d\sigma$$

$$- \int_{\partial B_{\epsilon}(x)} \frac{1}{|x-\sigma|} \nabla_{\hat{N}} u(\sigma) \, d\sigma + \int_{\partial B_{\epsilon}(x)} u(\sigma) \nabla_{\hat{N}} \left(\frac{1}{|x-\sigma|}\right) d\sigma.$$

In the last two integrals above,  $\hat{N}(\sigma)$  denotes the radially outward unit normal to the boundary of the ball  $B_{\epsilon}(x)$ . This corresponds to the "opposite" choice of normal that appears in the standard formulation of Green's identity, but we have compensated by adjusting the signs in front of the integrals.

Let's symbolically write (1.0.9) as

$$(1.0.10) L = R1 + R2 + R3 + R4.$$

Our goal is to show that as  $\epsilon \downarrow 0$ , the following limits are achieved:

- $L \rightarrow -4\pi \int_{\Omega} \Phi(x-y) \Delta_y u(y) d^3y$
- $R1 \rightarrow 4\pi \times \text{single layer potential}$
- $R2 \rightarrow -4\pi \times \text{double layer potential}$
- $R3 \rightarrow 0$
- $R4 \rightarrow -4\pi u(x)$ .

Once we have calculated the above limits, (1.0.8) then follows from simple algebraic rearranging. We first address L. Let  $M = \max_{u \in \overline{\Omega}} \Delta u(y)$ . We then estimate

$$\left| \int_{\Omega} \frac{1}{|x-y|} \Delta u(y) d^3y - \int_{\Omega_{\epsilon}} \frac{1}{|x-y|} \Delta u(y) d^3y \right| \leq \int_{B_{\epsilon}(x)} \frac{1}{|x-y|} |\Delta u(y)| d^3y$$

$$\leq M \int_{B_{\epsilon}(x)} \frac{1}{|x-y|} d^3y \to 0 \text{ as } \epsilon \downarrow 0.$$

This shows that L converges to  $\int_{\Omega} \frac{1}{|x-y|} \Delta u(y) d^3y$  as  $\epsilon \downarrow 0$ .

The limits for R1 and R2 are obvious since these terms do not depend on  $\epsilon$ .

We now address R3. To this end, Let  $M' = \max_{y \in \overline{\Omega}} |\nabla u(y)|$ . We then estimate R3 by

(1.0.12)

$$|R3| \leq \int_{\partial B_{\epsilon}(x)} \left| \frac{1}{|x - \sigma|} \nabla_{\hat{N}} u(\sigma) \right| d\sigma \leq \int_{\partial B_{\epsilon}(x)} \frac{1}{\epsilon} M' d\sigma = \underbrace{4\pi \epsilon^2}_{\text{surface area of } \partial B_{\epsilon}(x)} \times \epsilon^{-1} M' \to 0 \text{ as } \epsilon \downarrow 0.$$

We now address R4. Using spherical coordinates  $(r, \theta, \phi) \in [0, \infty) \times [0, \pi) \times [0, 2\pi)$  centered at x, we have that  $d\sigma = r^2 \sin \theta \, d\theta \, d\phi$ . Therefore,  $\int_{\partial B_{\epsilon}(x)} \frac{1}{|x-\sigma|^2} \, d\sigma = \int_{\phi \in [0,2\pi]} \int_{\theta \in [0,\pi]} 1 \, d\theta \, d\phi = 4\pi$ . We now estimate

$$(1.0.13) \qquad \left| \frac{1}{4\pi} R4 - \left[ -u(x) \right] \right| = \left| u(x) + \frac{1}{4\pi} \int_{\partial B_{\epsilon}(x)} u(\sigma) \nabla_{\hat{N}(\sigma)} \left( \frac{1}{|x - \sigma|} \right) d\sigma \right|$$

$$= \frac{1}{4\pi} \left| \int_{\partial B_{\epsilon}(x)} \left( u(x) - u(\sigma) \right) \left( \frac{1}{|x - \sigma|^2} \right) d\sigma \right|$$

$$\leq \frac{1}{4\pi} \int_{\partial B_{\epsilon}(x)} |u(x) - u(\sigma)| \left( \frac{1}{|x - \sigma|^2} \right) d\sigma$$

$$\leq \frac{1}{4\pi} \max_{\sigma \in \partial B_{\epsilon}(x)} |u(x) - u(\sigma)| \int_{\partial B_{\epsilon}(x)} \left( \frac{1}{|x - \sigma|^2} \right) d\sigma$$

$$\leq \max_{\sigma \in \partial B_{\epsilon}(x)} |u(x) - u(\sigma)| \to 0 \text{ as } \epsilon \downarrow 0.$$

This shows that  $R4 \to -4\pi u(x)$  as  $\epsilon \downarrow 0$ .

MIT OpenCourseWare http://ocw.mit.edu

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## MATH 18.152 COURSE NOTES - CLASS MEETING # 9

# 18.152 Introduction to PDEs, Fall 2011

Class Meeting # 9: Poisson's Formula, Harnack's Inequality, and Liouville's Theorem

Professor: Jared Speck

### 1. Representation Formula for Solutions to Poisson's Equation

We now derive our main representation formula for solution's to Poisson's equation on a domain  $\Omega$ .

Theorem 1.1 (Representation formula for solutions to the boundary value Poisson equation). Let  $\Omega$  be a domain with a smooth boundary, and assume that  $f \in C^2(\overline{\Omega})$  and  $g \in C(\partial \Omega)$ . Then the unique solution  $u \in C^2(\Omega) \cap C(\overline{\Omega})$  to

(1.0.1) 
$$\Delta u(x) = f(x), \qquad x \in \Omega \subset \mathbb{R}^n,$$
$$u(x) = g(x), \qquad x \in \partial\Omega.$$

can be represented as

(1.0.2) 
$$u(x) = \int_{\Omega} f(y)G(x,y) d^{n}y + \int_{\partial\Omega} g(\sigma) \underbrace{\nabla_{\hat{N}(\sigma)}G(x,\sigma)}_{Poisson \ kernel} d\sigma,$$

where G(x,y) is the Green function for  $\Omega$ .

*Proof.* Applying the **Representation formula for** u Proposition, we have that

$$(1.0.3) u(x) = \int_{\Omega} \Phi(x-y) f(y) d^n y - \int_{\partial \Omega} \Phi(x-\sigma) \nabla_{\hat{N}(\sigma)} u(\sigma) d\sigma + \int_{\partial \Omega} g(\sigma) \nabla_{\hat{N}(\sigma)} \Phi(x-\sigma) d\sigma.$$

Recall also that

(1.0.4) 
$$G(x,y) = \Phi(x-y) - \phi(x,y),$$

where

(1.0.5) 
$$\Delta_y \phi(x, y) = 0, \qquad x \in \Omega,$$

and

(1.0.6) 
$$G(x,\sigma) = 0 \text{ when } x \in \Omega \text{ and } \sigma \in \partial \Omega.$$

The expression (1.0.3) is not very useful since don't know the value of  $\nabla_{\hat{N}(\sigma)} u(\sigma)$  along  $\partial\Omega$ . To fix this, we will use Green's identity. Applying Green's identity to the functions u(y) and  $\phi(x,y)$ , and recalling that  $\Delta_y \phi(x,y) = 0$  for each fixed  $x \in \Omega$ , we have that

$$(1.0.7) 0 = \int_{\Omega} \phi(x,y) \underbrace{f(y)}_{f(y)} d^{n}y - \int_{\partial\Omega} \underbrace{\phi(x,\sigma)}_{\phi(x,\sigma)} \nabla_{\hat{N}} u(\sigma) d\sigma + \int_{\partial\Omega} \underbrace{g(\sigma)}_{y} \nabla_{\hat{N}} \phi(x,\sigma) d\sigma.$$

Subtracting (1.0.7) from (1.0.3), and using (1.0.4), we deduce the formula (1.0.2).

### 2. Poisson's Formula

Let's compute the Green function G(x,y) and Poisson kernel  $P(x,\sigma) \stackrel{\text{def}}{=} \nabla_{\hat{N}} G(x,\sigma)$  from (1.0.2) in the case that  $\Omega \stackrel{\text{def}}{=} B_R(0) \subset \mathbb{R}^3$  is a ball of radius R centered at the origin. We'll use a technique called the *method of images* that works for special domains.

Warning 2.0.1. Brace yourself for a bunch of tedious computations that at the end of the day will lead to a very nice expression.

The basic idea is to hope that  $\phi(x,y)$  from the decomposition  $G(x,y) = \Phi(x-y) - \phi(x,y)$ , where  $\phi(x,y)$  is viewed as a function of x that depends on the parameter y, is equal to the Newtonian potential generated by some "imaginary charge" q placed at a point  $x^* \in B_R^c(0)$ . To ensure that  $G(x,\sigma) = 0$  when  $\sigma \in \partial B_R(0)$ , q and  $x^*$  have to be chosen so that along the boundary  $\{y \in \mathbb{R}^3 \mid |y| = R\}$ ,  $\phi(x,y) = \frac{1}{4\pi|x-y|}$ . In a nutshell, we guess that

(2.0.8) 
$$G(x,y) = -\frac{1}{4\pi|x-y|} + \underbrace{\frac{q}{4\pi|x^*-y|}}_{\phi(x,y)?},$$

and we try to solve for q and  $x^*$  so that G(x,y) vanishes when |y| = R.

**Remark 2.0.1.** Note that  $\Delta_y \frac{q}{4\pi|x^*-y|} = 0$ , which is one of the conditions necessary for constructing G(x,y).

By the definition of G(x,y), we must have G(x,y) = 0 when |y| = R, which implies that

(2.0.9) 
$$\frac{1}{4\pi|x-y|} = \frac{q}{4\pi|x^*-y|}.$$

Simple algebra then leads to

$$(2.0.10) |x^* - y|^2 = q^2|x - y|^2.$$

When |y| = R, we use (2.0.10) to compute that

$$(2.0.11) |x^*|^2 - 2x^* \cdot y + R^2 = |x^* - y|^2 = q^2|x - y|^2 = q^2(|x|^2 - 2x \cdot y + R^2),$$

where  $\cdot$  denotes the Euclidean dot product. Then performing simple algebra, it follows from (2.0.11) that

$$(2.0.12) |x^*|^2 + R^2 - q^2(R^2 + |x|^2) = 2y \cdot (x^* - q^2x).$$

Now since the left-hand side of (2.0.12) does not depend on y, it must be the case that the right-hand side is always 0. This implies that  $x^* = q^2x$ , and also leads to the equation

$$(2.0.13) q4|x|2 - q2(R2 + |x|2) + R2 = 0.$$

Solving (2.0.13) for q, we finally have that

$$(2.0.14) q = \frac{R}{|x|},$$

$$(2.0.15) x^* = \frac{R^2}{|x|^2} x.$$

Therefore,

(2.0.16) 
$$\phi(x,y) = \frac{1}{4\pi} \frac{R}{|x| \left| \frac{R^2}{|x|^2} x - y \right|},$$

(2.0.17) 
$$\phi(0,y) = \frac{1}{4\pi R},$$

where we took a limit as  $x \to 0$  in (2.0.16) to derive (2.0.17). Next, using (2.0.8), we have

(2.0.18) 
$$G(x,y) = -\frac{1}{4\pi|x-y|} + \frac{1}{4\pi} \frac{R}{|x| \left| \frac{R^2}{|x|^2} x - y \right|}, \qquad x \neq 0,$$

(2.0.19) 
$$G(0,y) = -\frac{1}{4\pi|y|} + \frac{1}{4\pi R}.$$

For future use, we also compute that

(2.0.20) 
$$\nabla_y G(x,y) = -\frac{x-y}{4\pi |x-y|^3} + \frac{1}{4\pi} \frac{R}{|x|} \frac{x^* - y}{|x^* - y|^3}.$$

Now when  $\sigma \in \partial B_R(0)$ , (2.0.10) and (2.0.14) imply that

(2.0.21) 
$$|x^* - \sigma| = \frac{R}{|x|} |x - \sigma|.$$

Therefore, using (2.0.20) and (2.0.21), we compute that

$$(2.0.22) \qquad \nabla_{\sigma}G(x,\sigma) = -\frac{x-\sigma}{4\pi|x-\sigma|^3} + \frac{1}{4\pi} \frac{|x|^2}{R^2} \frac{x^*-\sigma}{|x-\sigma|^3} = -\frac{x-\sigma}{4\pi|x-\sigma|^3} + \frac{1}{4\pi} \frac{|x|^2}{R^2} \frac{\frac{R^2}{|x|^2} x - \sigma}{|x-\sigma|^3} = \frac{\sigma}{4\pi|x-\sigma|^3} \left(1 - \frac{|x|^2}{R^2}\right).$$

Using (2.0.22) and the fact that  $\hat{N}(\sigma) = \frac{1}{R}\sigma$ , we deduce

(2.0.23) 
$$\nabla_{\hat{N}(\sigma)} G(x,\sigma) \stackrel{\text{def}}{=} \nabla_{\sigma} G(x,\sigma) \cdot \hat{N}(\sigma) = \frac{R^2 - |x|^2}{4\pi R} \frac{1}{|x-\sigma|^3}.$$

**Remark 2.0.2.** If the ball were centered at the point  $p \in \mathbb{R}^3$  instead of the origin, then the formula (2.0.23) would be replaced with

(2.0.24) 
$$\nabla_{\hat{N}(\sigma)} G(x,\sigma) \stackrel{\text{def}}{=} \nabla_{\sigma} G(x,\sigma) \cdot \hat{N}(\sigma) = -\frac{R^2 - |x-p|^2}{4\pi R} \frac{1}{|x-\sigma|^3}.$$

Let's summarize this by stating a lemma.

**Lemma 2.0.1.** The Green function for a ball  $B_R(p) \subset \mathbb{R}^3$  is

(2.0.25a) 
$$G(x,y) = -\frac{1}{4\pi|x-y|} + \frac{1}{4\pi} \frac{R}{|x-p||\frac{R^2}{|x-p|^2}(x-p) - (y-p)|}, \qquad x \neq p,$$

(2.0.25b) 
$$G(p,y) = -\frac{1}{4\pi|y-p|} + \frac{1}{4\pi R}.$$

Furthermore, if  $x \in B_R(p)$  and  $\sigma \in \partial B_R(p)$ , then

(2.0.25c) 
$$\nabla_{\hat{N}(\sigma)} G(x, \sigma) = \frac{R^2 - |x - p|^2}{4\pi R} \frac{1}{|x - \sigma|^3}.$$

We can now easily derive a representation formula for solutions to the Laplace equation on a ball.

**Theorem 2.1** (Poisson's formula). Let  $B_R(p) \subset \mathbb{R}^3$  be a ball of radius R centered at  $p = (p^1, p^2, p^3)$ , and let  $x = (x^1, x^2, x^3)$  denote a point in  $\mathbb{R}^3$ . Let  $g \in C(\partial B_R(p))$ . Then the unique solution  $u \in C^2(B_R(p)) \cap C(\overline{B}_R(p))$  of the PDE

(2.0.26) 
$$\begin{cases} \Delta u(x) = 0, & x \in B_R(p), \\ u(x) = g(x), & x \in \partial B_R(p), \end{cases}$$

can be represented using the Poisson formula:

(2.0.27) 
$$u(x) = \frac{R^2 - |x - p|^2}{4\pi R} \int_{\partial B_R(p)} \frac{g(\sigma)}{|x - \sigma|^3} d\sigma.$$

**Remark 2.0.3.** In n dimensions, the formula (2.0.27) gets replaced with

(2.0.28) 
$$u(x) = \frac{R^2 - |x - p|^2}{\omega_n R} \int_{\partial B_R(p)} \frac{g(\sigma)}{|x - \sigma|^n} d\sigma,$$

where as usual,  $\omega_n$  is the surface area of the unit ball in  $\mathbb{R}^n$ .

*Proof.* The identity (2.0.27) follows immediately from Theorem 1.1 and Lemma 2.0.1.

### 3. Harnack's inequality

We will now use some of our tools to prove a famous inequality for Harmonic functions. The theorem provides some estimates that place limitations on how slow/fast harmonic functions are allowed to grow.

**Theorem 3.1** (Harnack's inequality). Let  $B_R(0) \subset \mathbb{R}^n$  be the ball of radius R centered at the origin, and let  $u \in C^2(B_R(0)) \cap C(\overline{B}_R(0))$  be the unique solution to (2.0.26). Assume that u is **non-negative** on  $\overline{B}_R(0)$ . Then for any  $x \in B_R(0)$ , we have that

$$(3.0.29) \frac{R^{n-2}(R-|x|)}{(R+|x|)^{n-1}}u(0) \le u(x) \le \frac{R^{n-2}(R+|x|)}{(R-|x|)^{n-1}}u(0).$$

*Proof.* We'll do the proof for n = 3. The basic idea is to combine the Poisson representation formula with simple inequalities and the mean value property. By Theorem 2.1, we have that

(3.0.30) 
$$u(x) = \frac{R^2 - |x|^2}{4\pi R} \int_{\partial B_R(0)} \frac{g(\sigma)}{|x - \sigma|^3} d\sigma.$$

By the triangle inequality, for  $\sigma \in \partial B_R(0)$  (i.e.  $|\sigma| = R$ ), we have that  $|x| - R \le |x - \sigma| \le |x| + R$ . Applying the first inequality to (3.0.30), and using the non-negativity of g, we deduce that

(3.0.31) 
$$u(x) \le \frac{R + |x|}{R^2 - |x|^2} \frac{1}{4\pi R} \int_{\partial B_R(0)} g(\sigma) \, d\sigma.$$

Now recall that by the mean value property, we have that

$$(3.0.32) u(0) = \frac{1}{4\pi R^2} \int_{\partial B_R(0)} g(\sigma) d\sigma.$$

Thus, combining (3.0.31) and (3.0.32), we have that

(3.0.33) 
$$u(x) \le \frac{R(R+|x|)}{(R-|x|)^2} u(0),$$

which implies one of the inequalities in (3.0.29). The other one can be proved similarly using the remaining triangle inequality.

We now prove a famous consequence of Harnack's inequality. The statement is also often proved in introductory courses in complex analysis, and it plays a central role in some proofs of the fundamental theorem of algebra.

Corollary 3.0.2 (Liouville's theorem). Suppose that  $u \in C^2(\mathbb{R}^n)$  is harmonic on  $\mathbb{R}^n$ . Assume that there exists a constant M such that  $u(x) \geq M$  for all  $x \in \mathbb{R}^n$ , or such that  $u(x) \leq M$  for all  $x \in \mathbb{R}^n$ . Then u is a constant-valued function.

*Proof.* We first consider the case that  $u(x) \ge M$ . Let  $v \stackrel{\text{def}}{=} u + |M|$ . Observe that  $v \ge 0$  is harmonic and verifies the hypotheses of Theorem 3.1. Thus, by (3.0.29), if  $x \in \mathbb{R}^n$  and R is sufficiently large, we have that

$$(3.0.34) \frac{R^{n-2}(R-|x|)}{(R+|x|)^{n-1}}v(0) \le v(x) \le \frac{R^{n-2}(R+|x|)}{(R-|x|)^{n-1}}v(0).$$

Allowing  $R \to \infty$  in (3.0.34), we conclude that v(x) = v(0). Thus, v is a constant-valued function (and therefore u is too).

To handle the case  $u(x) \leq M$ , we simply consider the function  $w(x) \stackrel{\text{def}}{=} -u(x) + |M|$  in place of v(x), and we argue as above.

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# MATH 18.152 COURSE NOTES - CLASS MEETING # 10

## 18.152 Introduction to PDEs, Fall 2011

Class Meeting # 10: Introduction to the Wave Equation

Professor: Jared Speck

#### 1. What is the wave equation?

The standard wave equation for a function u(t,x) (where  $t \in \mathbb{R}, x \in \mathbb{R}^n$ ) is

(1.0.1) 
$$-\frac{1}{c^2} \partial_t^2 u + \Delta u = 0.$$

(1.0.1) is second order and linear. The constant c > 0 is called the *speed* (this terminology will be justified as our course progresses), and it has dimensions of  $\frac{\text{length}}{\text{time}}$ . Note that heuristically speaking, if we let  $c \to \infty$ , then (1.0.1) becomes Laplace's equation. However, as we will see, in order to have a well-posed problem for (1.0.1), we will need to specify Cauchy (i.e. initial data) for u and also  $\partial_t u$ . The fact that we need to specify Cauchy data is in stark contrast to Laplace's equation, but is analogous to the heat equation. The fact that we need to specify two pieces of Cauchy data is connected to the fact that the wave equation is second order in time.

### 2. Where does it come from?

Equation (1.0.1) arises in an incredible variety of physical contexts, especially those involving disturbances that propagate at a finite speed. Let's discuss how the wave equation arises as an approximation to the equations of fluid mechanics. For simplicity, let's only discuss the case of 1 spatial dimension. The equations of fluid mechanics, which are known as the *Euler equations*, take the following form in 1+1 dimensions:

(2.0.2a) 
$$\partial_t \rho + \partial_x (\rho v) = 0,$$

(2.0.2b) 
$$\partial_t(\rho v) + \partial_x(\rho v^2) = -\partial_x p,$$

where  $\rho(t,x)$  is the fluid mass density, v(t,x) is the fluid velocity, and p(t,x) is the pressure. Equation (2.0.2a) implies the conservation of mass, and equation (2.0.2b) is Newton's second law: the rate of change of fluid momentum is equal to the force, which is created by the pressure gradient (i.e., the  $-\partial_x p$  term). The Euler equations are highly nonlinear, and we are very far from obtaining a full understanding of how their solutions behave in general.

A fundamental aspect of fluid mechanics is that the system is not closed because there are not enough equations. A common method of achieving closure is by choosing an *equation of state*, which is a relationship between the fluid variables. This relationship is often empirically determined. A commonly studied equation of state is

$$(2.0.3a) p = K \rho^{\gamma}$$

where  $\gamma > 1$  and K > 0 are constants. For future use, we note that under (2.0.3a), we have

(2.0.3b) 
$$\partial_x p = K \gamma \rho^{\gamma - 1} \partial_x \rho,$$

(2.0.3c) 
$$\partial_x^2 p = K \gamma \rho^{\gamma - 1} \partial_x^2 \rho + K \gamma (\gamma - 1) \rho^{\gamma - 2} (\partial_x \rho)^2,$$

Also for future use, we differentiate (2.0.2a) with respect to t and (2.0.2b) with respect to x to deduce that

$$(2.0.4a) \qquad \partial_t^2 \rho + \rho \partial_t \partial_x v + v \partial_t \partial_x \rho + \partial_t \rho \partial_x v + \partial_t v \partial_x \rho = 0,$$

$$(2.0.4b) \rho \partial_t \partial_x v + v \partial_t \partial_x \rho + \partial_t \rho \partial_x v + \partial_t v \partial_x \rho + \partial_x^2 \rho + 4\rho v \partial_x^2 v + 2\partial_x \rho \partial_x v = -\partial_x^2 p.$$

The theory of acoustics is based on *linearizing* (i.e. throwing away the nonlinear terms) the equations (2.0.4a) - (2.0.4b) around the static solutions  $\rho = \bar{\rho} = const > 0$ , v = 0,  $p = \bar{p} = const > 0$ . These static solutions describe a fluid at rest. Let's assume that we make a small perturbation of this solution, i.e., that v is small, and that

$$(2.0.5) \rho = \bar{\rho} + \delta,$$

where  $\delta(t, x)$  is a small function.

Using the expansion (2.0.5), we now throw away (with the help of (2.0.3c)) all of the quadratic and higher-order small terms from (2.0.4a) - (2.0.4b) to obtain the following **approximating** system (the quantities that are assumed to be small are v,  $\delta$ , and all of their partial derivatives):

(2.0.6a) 
$$\partial_t^2 \delta + \bar{\rho} \partial_t \partial_x v = 0,$$

(2.0.6b) 
$$\bar{\rho}\partial_t \partial_x v = -K\gamma \bar{\rho}^{\gamma - 1} \partial_x^2 \delta.$$

Comparing (2.0.6a) and (2.0.6b), we see that  $\delta$  verifies the following approximating equation

$$(2.0.7) -\partial_t^2 \delta + K \gamma \bar{\rho}^{\gamma - 1} \partial_x^2 \delta = 0.$$

Equation (2.0.7) is a wave equation for the perturbation  $\delta(t, x)$ ! It models the propagation of *sound* waves. This is the linear theory of acoustics! Note that the speed associated to the equation (2.0.7) depends on the background density  $\bar{\rho}$ :

$$(2.0.8) c = \sqrt{K\gamma\bar{\rho}^{\gamma-1}}.$$

When  $\gamma > 1$ , higher background density  $\implies$  faster sound speed propagation.

**Remark 2.0.1.** For air under "normal" atmospheric conditions,  $\gamma = 1.4$  is a pretty good model.

#### 3. Some Well-Posed Problems

Recall that well-posed PDEs have three important properties:

- Given suitable data, a solution exists.
- The solution is unique.
- The solution depends continuously on the data.

Perhaps the most often studied well-posed problem for the wave equation is the *global Cauchy* problem in 1 + n spacetime dimensions:

(3.0.9a) 
$$-\partial_t^2 u(t,x) + \Delta_x u(t,x) = 0, \qquad (t,x) \in \mathbb{R} \times \mathbb{R}^n,$$

(3.0.9b) 
$$u(0,x) = f(x), \quad x \in \mathbb{R}^n,$$

(3.0.9c) 
$$\partial_t u(0,x) = g(x), \qquad x \in \mathbb{R}^n.$$

We now mention some additional well-posed problems in the case of 1+1 dimensions. We assume that u verifies the wave equation for  $(t, x) \in (-\infty, \infty) \times [0, L]$  and that Cauchy data is given:

$$(3.0.10a) -\partial_t^2 u(t,x) + \partial_x^2 u(t,x) = 0, (t,x) \in \mathbb{R} \times [0,L],$$

(3.0.10b) 
$$u(0,x) = f(x), \qquad x \in [0,L],$$

(3.0.10c) 
$$\partial_t u(0,x) = g(x), \qquad x \in [0,L].$$

Unlike in the case of (3.0.9a) - (3.0.9c), because of the finiteness of the interval [0, L], we need to supplement (3.0.10a) - (3.0.10c) with additional conditions in order to generated a well-posed problem. Here are some well-known ways of generating a well-posed problem; they are essentially the same as in the case of the heat equation.

- (1) Dirichlet data: also specifying u(t,0) = a(t), u(t,L) = b(t) for t > 0
- (2) Neumann data: also specifying  $\partial_x u(t,0) = a(t)$ ,  $\partial_x u(t,L) = b(t)$  for t > 0
- (3) Robin data: also specifying  $\partial_x u(t,0) = ku(t,0)$ ,  $\partial_x u(t,L) = -ku(t,L)$  for t > 0, where k > 0 is a constant
- (4) Mixed data: e.g. one kind of data at x = 0, and a different kind at x = L

#### 4. 1 + 1 Spacetime dimensions

Let's consider the wave equation with speed c in 1 + 1 dimensions:

$$(4.0.11) -c^{-2}\partial_{\tau}^{2}u(\tau,x) + \partial_{x}^{2}u(\tau,x) = 0.$$

Let's first note the following fact: if f, g are any differentiable functions, then  $u(x, \tau) \stackrel{\text{def}}{=} f(x - c\tau)$  and  $u(x, \tau) \stackrel{\text{def}}{=} g(x + c\tau)$  solve (4.0.11). The first is called a right-traveling wave, and the second is called a left-traveling wave. To visualized wave propagation in 1 + 1 dimensions, you can imagine that the graph of  $f(\cdot)$  and  $g(\cdot)$  are translated to the right/left at a speed c. This gives a good idea of what wave motion looks like in 1 + 1 dimensions. In particular, the amplitudes of the traveling wave solutions are preserved in time. As we will see, wave propagation in higher dimensions is quite different. In higher dimensions, the amplitudes decay in time due to the spreading out of the waves. You will study the case of 1 + 3 spatial dimension in one of your homework exercises; you will show that in this case, the amplitudes decay at a rate of order  $t^{-1}$  as  $t \to \infty$ .

**Remark 4.0.2.** Not all wave solutions in 1 + 1 dimensions are traveling waves; see Theorem 4.1.

By making the change of variables  $t \stackrel{\text{def}}{=} c\tau$ , we can transform equation (4.0.11) into a wave equation with speed equal to 1:

$$(4.0.12) -\partial_t^2 u(t,x) + \partial_x^2 u(t,x) = 0.$$

This makes our life a bit easier. Let's now consider the global Cauchy problem by supplementing (4.0.12) with the initial data

(4.0.13) 
$$u(0,x) = f(x), \partial_t u(0,x) = g(x).$$

As we will see, (4.0.12) + (4.0.13) has a unique solution that has a nice representation.

**Theorem 4.1** (d'Alembert's formula). Assume that  $f \in C^2(\mathbb{R})$  and  $g \in C^1(\mathbb{R})$ . Then the unique solution u(t,x) to (4.0.12) + (4.0.13) satisfies  $u \in C^2([0,\infty) \times \mathbb{R})$  and can be represented by d'Alembert's formula:

(4.0.14) 
$$u(t,x) = \frac{1}{2} \Big( f(x+t) + f(x-t) \Big) + \frac{1}{2} \int_{z=x-t}^{z=x+t} g(z) \, dz.$$

**Remark 4.0.3.** For the wave equation  $-c^{-2}\partial_t^2 u + \partial_x^2 u = 0$  formula (4.0.14) is replaced with

(4.0.15) 
$$u(t,x) = \frac{1}{2} \left( f(x+ct) + f(x-ct) \right) + \frac{1}{2c} \int_{z=x-ct}^{z=x+ct} g(z) \, dz.$$

**Remark 4.0.4.** Equation (4.0.14) illustrates the *finite speed of propagation* property associated to the wave equation. More precisely, the value of the solution at (t,x) is only influenced by the "initial data interval"  $\{(0,y) \mid x-t \leq y \leq x+t\}$ ; changes to the initial data (4.0.13) outside of this interval have no effect on the solution at (t,x). We will reexamine this property later in the course with the help of energy methods.

*Proof.* To derive (4.0.14), it is convenient to introduce a change of variables called *null coordinates*:

$$(4.0.16) q \stackrel{\text{def}}{=} t - x,$$

$$(4.0.17) s \stackrel{\text{def}}{=} t + x.$$

The chain rule implies the following relationships between partial derivatives:

(4.0.18) 
$$\partial_q = \frac{1}{2}(\partial_t - \partial_x), \qquad \partial_s = \frac{1}{2}(\partial_t + \partial_x),$$

(4.0.19) 
$$\partial_t = \partial_q + \partial_s, \qquad \partial_x = \partial_s - \partial_q.$$

The operators  $\partial_q$  and  $\partial_s$  can be viewed as directional derivatives in the (t,x) Cartesian spacetime direction .5(1,-1) and .5(1,1) respectively. These *null directions*, which are sometimes called *characteristic directions*, are extremely important. In the future, we will discuss the notion of a characteristic direction in a general setting.

It is now easy to see that (4.0.12) takes the following form in null coordinates:

$$\partial_s \partial_q u = 0.$$

Integrating (4.0.20) with respect to s, we have that

$$(4.0.21) \partial_q u = H(q),$$

where H is a function of q.

Note that the value of q is the same for the pair of Cartesian spacetime points  $(\tau, y)$  and  $(0, y - \tau)$ . Thus, using the initial conditions (4.0.13), we have that

$$(4.0.22) \partial_q u(\tau, y) = \partial_q u(0, y - \tau) = \left(\frac{1}{2}(\partial_t - \partial_x)u\right)(0, y - \tau) = \frac{1}{2}(g(y - \tau) - f'(y - \tau)).$$

Similarly, interchanging the partial derivatives in (4.0.20) to deduce  $\partial_s \partial_a u = 0$ , we conclude that

(4.0.23) 
$$\partial_s u(\tau, y) = \frac{1}{2} (g(y+\tau) + f'(y+\tau)).$$

Adding (4.0.22) and (4.0.23), and using (4.0.18), we have that

(4.0.24) 
$$\partial_t u(t,x) = \frac{1}{2} \Big( f'(x+t) - f'(x-t) + g(x+t) + g(x-t) \Big).$$

Integrating (4.0.24) in time with respect to t from 0 to t, and again using the initial conditions (4.0.13), we have that

$$(4.0.25) u(t,x) = \overbrace{u(0,x)}^{f(x)} + \frac{1}{2} \Big( f(x+t) - f(x) + f(x-t) - f(x) \Big) + \frac{1}{2} \int_{\tau=0}^{t} g(x+\tau) + g(x-\tau) d\tau$$
$$= \frac{1}{2} \Big( f(x+t) + f(x-t) \Big) + \frac{1}{2} \int_{z=x-t}^{z=x+t} g(z) dz,$$

where to derive the last equality, we made the integration change of variables  $z = x + \tau$  for the  $g(x+\tau)$  term, and the change of variables  $z=x-\tau$  for the  $g(x-\tau)$  term. We have thus derived (4.0.14).

Without a lot of additional effort, we can extend Theorem 4.1 to apply to the following initial + boundary value PDE in 1 + 1 dimensions; the result is stated and proved in the next corollary. This PDE would arise in the study of e.g. the following idealized problem: a description of the propagation of waves on an infinitely long vibrating string with one end fixed. Furthermore, the corollary will later play a role in our extension of Theorem 4.1 to the case of 1+3 dimensions.

**Corollary 4.0.1.** Let  $f \in C^2([0,\infty)), g \in C^1([0,\infty)), and assume that <math>f(0) = g(0) = 0$ . Then the unique solution to the following 1+1 dimensional initial + boundary value problem

(4.0.26a) 
$$-\partial_t^2 u(t,x) + \partial_x^2 u(t,x) = 0, \qquad (t,x) \in [0,\infty) \times (0,\infty),$$

(4.0.26b) 
$$u(t,0) = 0, t \in [0,\infty),$$

(4.0.26c) 
$$u(0,x) = f(x), x \in (0,\infty),$$
  
(4.0.26d)  $\partial_t u(0,x) = g(x), x \in (0,\infty)$ 

$$(4.0.26d) \partial_t u(0,x) = g(x), x \in (0,\infty)$$

satisfies  $u \in C^2([0,\infty) \times [0,\infty))$ . Furthermore, it can be represented as

$$(4.0.27) u(t,x) = \begin{cases} \frac{1}{2} \Big( f(x+t) + f(x-t) \Big) + \frac{1}{2} \int_{z=|x-t|}^{z=x+t} g(z) \, dz, & \text{if } 0 \le t \le x, \\ \frac{1}{2} \Big( f(x+t) - f(t-x) \Big) + \frac{1}{2} \int_{z=|x-t|}^{z=x+t} g(z) \, dz, & \text{if } 0 \le x \le t. \end{cases}$$

*Proof.* The idea is that if we extend u to be odd in x, then we can reduce the problem to the case of Theorem 4.1. Motivated by this, we define

(4.0.28) 
$$\widetilde{u}(t,x) \stackrel{\text{def}}{=} \left\{ \begin{array}{ll} u(t,x), & \text{if } t \ge 0, x \ge 0, \\ -u(t,-x), & \text{if } t \ge 0, x \le 0, \end{array} \right. ,$$

(4.0.29) 
$$\widetilde{f}(x) \stackrel{\text{def}}{=} \begin{cases} f(x), & \text{if } x \ge 0, \\ -f(-x), & \text{if } x \le 0, \end{cases}$$

$$\widetilde{g}(x) \stackrel{\text{def}}{=} \begin{cases} g(x), & \text{if } x \ge 0, \\ -g(-x), & \text{if } x \le 0. \end{cases}$$

(4.0.30) 
$$\widetilde{g}(x) \stackrel{\text{def}}{=} \begin{cases} g(x), & \text{if } x \ge 0, \\ -g(-x), & \text{if } x \le 0. \end{cases}$$

Since u(t,x) solves (4.0.26a), it follows that  $\widetilde{u}(t,x)$  is a solution to the wave equation (4.0.12) for  $(t,x) \in \mathbb{R} \times \mathbb{R}$  with initial data  $\widetilde{u}(0,x) = \widetilde{f}(x)$ ,  $\partial_t \widetilde{u}(t,x) = \widetilde{g}(x)$ . Thus, by (4.0.14), we have that

$$(4.0.31) \widetilde{u}(t,x) = \frac{1}{2} \left( \widetilde{f}(x+t) + \widetilde{f}(x-t) \right) + \frac{1}{2} \int_{z=x-t}^{z=x+t} \widetilde{g}(z) \, dz.$$

The expression (4.0.27) now easily follows from considering (4.0.31) separately in the spacetime regions  $\{(t,x) \mid 0 \le t \le x\}$  and  $\{(t,x) \mid 0 \le x \le t\}$ , and from the definitions (4.0.28) - (4.0.30); note that in the case  $\{(t,x) \mid 0 \le t \le x\}$ , since  $\widetilde{g}$  is odd, the part of the integral from x-t to t-x cancels and thus the only net contribution comes from the integration interval [|x-t|, x+t].

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## MATH 18.152 COURSE NOTES - CLASS MEETING # 11

18.152 Introduction to PDEs, Fall 2011

Professor: Jared Speck

Class Meeting # 11: The Method of Spherical Means

## 1. 1+3 spacetime dimensions and the method of spherical means

We would now like to derive an analog of d'Alembert's formula in the physically relevant case of 1+3 dimensions. As we will see, the analogous formula, known as Kirchhoff's formula, can be derived through the following steps.

- Given a solution u(t,x) to the 1 + 3 dimensional wave equation, we will define a spherical average of u centered at x. The average will depend on the averaging radius r.
- For fixed x, we will show that a slight modification of the average will solve the 1+1 dimensional wave equation in the unknowns (t,r). With the help of our corollary to d'Alembert's formula, we will be able to find an explicit formula for this modified function.
- We will take a limit as the averaging goes to 0 in order to recover an expression for u(t,x).

This procedure is known as the *method of spherical means*. The final result will be stated and proved as a theorem. Before proving the theorem, we will develop some preliminary estimates. We will use spherical coordinates  $(r, \theta, \phi) \in [0, \infty) \times [0, \pi) \times [0, 2\pi)$  on  $\mathbb{R}^3$ . Recall that if the spherical coordinates are centered at the Cartesian point  $(p^1, p^2, p^3)$ , then the standard Cartesian coordinates  $(x^1, x^2, x^3)$  are connected to spherical coordinates by

$$(1.0.1a) x^1 = p^1 + r\sin\theta\cos\phi,$$

$$(1.0.1b) x^2 = p^2 + r\sin\theta\sin\phi,$$

(1.0.1c) 
$$x^3 = p^3 + r\cos\theta.$$

Also recall that the integration measure associated to  $B_r(0)$  is  $d\sigma = r^2 d\omega$ , where  $d\omega \stackrel{\text{def}}{=} \sin\theta d\theta d\phi$ . Here,  $\omega$  represents the angular variables. We will abuse notation by using the symbol  $\omega$  to denote both the angular coordinates  $(\theta, \phi)$ , and alternatively as the corresponding point  $(\sin\theta\cos\phi, \sin\theta\sin\phi, \cos\theta) \in \partial B_1(0)$ .

**Proposition 1.0.1** (Spherical averages). Let  $u(t,x) \in C^2([0,\infty) \times \mathbb{R}^3)$  be a solution to the 1+3 dimensional global Cauchy problem

$$(1.0.2a) -\partial_t^2 u(t,x) + \Delta u(t,x) = 0, (t,x) \in [0,\infty) \times \mathbb{R}^3,$$

(1.0.2b) 
$$u(0,x) = f(x), x \in \mathbb{R}^3,$$

(1.0.2c) 
$$\partial_t u(0,x) = g(x), \qquad x \in \mathbb{R}^3.$$

For each r > 0, define the spherically averaged quantities

(1.0.3a) 
$$U(t,r;x) \stackrel{\text{def}}{=} \frac{1}{4\pi r^2} \int_{\partial B_r(x)} u(t,\sigma) d\sigma = \frac{1}{4\pi} \int_{\omega \in \partial B_1(0)} u(t,x+r\omega) d\omega,$$

(1.0.3b) 
$$F(r;x) \stackrel{\text{def}}{=} \frac{1}{4\pi r^2} \int_{\partial B_r(x)} f(\sigma) d\sigma,$$

(1.0.3c) 
$$G(r;x) \stackrel{\text{def}}{=} \frac{1}{4\pi r^2} \int_{\partial B_r(x)} g(\sigma) d\sigma,$$

and their related modifications

(1.0.4a) 
$$\widetilde{U}(t,r;x) \stackrel{def}{=} rU(t,r;x),$$

(1.0.4b) 
$$\widetilde{F}(r;x) \stackrel{def}{=} rF(r;x),$$

(1.0.4c) 
$$\widetilde{G}(r;x) \stackrel{def}{=} rG(r;x).$$

Then  $\widetilde{U}(t,r;x) \in C^2([0,\infty) \times [0,\infty))$  is a solution to the following initial + boundary-value problem for the **one-dimensional** wave equation:

$$(1.0.5a) -\partial_t^2 \widetilde{U}(t,r;x) + \partial_r^2 \widetilde{U}(t,r;x) = 0, (t,r) \in [0,\infty) \times [0,\infty),$$

(1.0.5b) 
$$\widetilde{U}(t,0;x) = 0, \quad t \in [0,\infty),$$

(1.0.5c) 
$$\widetilde{U}(0,r;x) = \widetilde{F}(r;x), \qquad r \in (0,\infty),$$

(1.0.5d) 
$$\partial_t \widetilde{U}(0, r; x) = \widetilde{G}(r; x), \qquad r \in (0, \infty).$$

Furthermore,

(1.0.6) 
$$\lim_{r \to 0} U(t, r; x) = u(t, x).$$

*Proof.* Differentiating under the integral on the right-hand side of (1.0.3a), using the chain rule relation  $\partial_r[u(t,x+r\omega)]d\omega = (\nabla u)(t,x+r\omega) \cdot \omega d\omega = \frac{1}{r^2}\nabla_{\hat{N}(\sigma)}u(t,\sigma)d\sigma$  (where  $\hat{N}(\sigma)$  is the outward unit normal to  $\partial B_r(x)$ ), and applying the divergence theorem, we compute that

(1.0.7) 
$$\partial_r U = \frac{1}{4\pi r^2} \int_{\partial B_r(x)} \nabla_{\hat{N}(\sigma)} u(t,\sigma) d\sigma = \frac{1}{4\pi r^2} \int_{B_r(x)} \Delta_y u(t,y) d^3y.$$

We now derive a version of the fundamental theorem of calculus that will be used in our analysis below. If h is a continuous function on  $\mathbb{R}^3$ , then using spherical coordinates  $(\rho, \omega)$  centered at the fixed point x, we have

$$(1.0.8)$$

$$\partial_r \int_{B_r(x)} h(y) d^3y = \partial_r \int_0^r \int_{\omega \in \partial B_1(0)} \rho^2 h(\rho, x + \rho \omega) d\omega d\rho = \int_{\omega \in \partial B_1(0)} r^2 h(r, x + r\omega) d\omega \stackrel{\text{def}}{=} \int_{\partial B_r(x)} h(\sigma) d\sigma.$$

Multiplying both sides of (1.0.7) by  $r^2$  and applying (1.0.8), we have that

(1.0.9) 
$$\partial_r(r^2\partial_r U) = \frac{1}{4\pi}\partial_r \int_{B_r(x)} \Delta_y u(t,y) \, d^3y = \frac{1}{4\pi} \int_{\partial B_r(x)} \Delta u(t,\sigma) \, d\sigma.$$

Differentiating under the integral in (1.0.3a) and using (1.0.2a), we have that

(1.0.10) 
$$\partial_t^2 U(t,r;x) = \frac{1}{4\pi r^2} \int_{\partial B_r(x)} \partial_t^2 u(t,\sigma) \, d\sigma = \frac{1}{4\pi r^2} \int_{\partial B_r(x)} \Delta u(t,\sigma) \, d\sigma.$$

Comparing (1.0.9) and (1.0.10), we see that

(1.0.11) 
$$\partial_t^2 U(t,r;x) = \frac{1}{r^2} \partial_r (r^2 \partial_r U) = \partial_r^2 U(t,r;x) + \frac{2}{r} \partial_r U(t,r;x).$$

Multiplying both sides of (1.0.11) by r and performing simple calculations, we see that

(1.0.12) 
$$\partial_t^2 [rU(t,r;x)] = \partial_r^2 [rU(t,r;x)].$$

We have thus shown that the PDE (1.0.5a) is verified by  $\widetilde{U} \stackrel{\text{def}}{=} rU$ .

Using (1.0.2b) - (1.0.2c) and definitions (1.0.3b) - (1.0.3c), it is easy to check that the initial conditions (1.0.5c) - (1.0.5d) hold. Note that you will have to differentiate under the integral in (1.0.3a) in order to show that (1.0.5d) holds.

The limit (1.0.6) follows easily from the right-hand side of (1.0.3a), since u is continuous.

Finally, the boundary condition (1.0.5b) then follows easily from multiplying (1.0.6) by r before taking the limit  $r \to 0^+$ .

Corollary 1.0.2 (Representation formula for  $\widetilde{U}(t,r;x)$ ). Under the assumptions of Proposition 1.0.1, for  $0 \le r \le t$ , we have that

$$(1.0.13) \qquad \widetilde{U}(t,r;x) \stackrel{def}{=} rU(t,r;x) = \frac{1}{2} \Big( \widetilde{F}(r+t;x) - \widetilde{F}(r-t;x) \Big) + \frac{1}{2} \int_{\rho=-r+t}^{\rho=r+t} \widetilde{G}(\rho;x) \, d\rho.$$

*Proof.* (1.0.13) follows from (1.0.5a) - (1.0.5d) and the Corollary to d'Alembert's formula.  $\Box$ 

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## MATH 18.152 COURSE NOTES - CLASS MEETING # 12

## 18.152 Introduction to PDEs, Fall 2011

Class Meeting # 12: Kirchhoff's Formula and Minkowskian Geometry

Professor: Jared Speck

### 1. Kirchhoff's Formula

We are now ready to derive Kirchhoff's famous formula.

**Theorem 1.1** (Kirchhoff's formula). Assume that  $f \in C^3(\mathbb{R}^3)$  and  $g \in C^2(\mathbb{R}^3)$ . Then the unique solution u(t,x) to the global Cauchy problem

$$(1.0.1a) -\partial_t^2 u(t,x) + \Delta u(t,x) = 0, (t,x) \in [0,\infty) \times \mathbb{R}^3,$$

(1.0.1b) 
$$u(0,x) = f(x), \qquad x \in \mathbb{R}^3,$$

(1.0.1c) 
$$\partial_t u(0,x) = g(x), \qquad x \in \mathbb{R}^3$$

in 1+3 dimensions satisfies  $u \in C^2([0,\infty) \times \mathbb{R}^3)$  and can be represented as follows:

$$(1.0.2) u(t,x) = \frac{1}{4\pi t^2} \int_{\partial B_t(x)} f(\sigma) d\sigma + \frac{1}{4\pi t} \int_{\partial B_t(x)} \nabla_{\hat{N}(\sigma)} f(\sigma) d\sigma + \frac{1}{4\pi t} \int_{\partial B_t(x)} g(\sigma) d\sigma.$$

**Remark 1.0.1.** Equation (1.0.2) again illustrates the finite speed of propagation property associated to the linear wave equation. More precisely, the behavior of the solution at the point (t, x) is only affected by the initial data in the region  $\{(0,y) \mid |x-y|=t\}$ . The fact that this region is the boundary of a ball rather than a solid ball is known as the sharp Huygens principle. It can be shown that the sharp version of this principle holds 1 + n dimensions when  $n \ge 3$  is odd, but not when n = 1 or when n is even. However, even when the sharp version fails, there still is a finite speed of propagation property; the solution in these cases depends on the data in the solid ball.

**Remark 1.0.2.** Note that in Theorem 1.1, we can only guarantee that the solution is one degree *less differentiable* than the data. This contrasts to d'Alembert's formula, in which the 1+1 dimensional solution was shown to have the same degree of differentiability as the data.

*Proof.* Using the **Representation formula for**  $\widetilde{U}(t,r;x)$  corollary, the differentiability of  $\widetilde{F}$ , and the continuity of  $\widetilde{G}$ , we have that

(1.0.3) 
$$u(t,x) = \lim_{r \to 0^+} U(t,r;x) = \lim_{r \to 0^+} \frac{\widetilde{U}(t,r;x)}{r}$$
$$= \lim_{r \to 0^+} \frac{\widetilde{F}(r+t;x) - \widetilde{F}(r-t;x)}{2r} + \frac{1}{2r} \int_{\rho=-r+t}^{\rho=r+t} \widetilde{G}(\rho;x) d\rho$$
$$= \partial_t \widetilde{F}(t;x) + \widetilde{G}(t;x).$$

The  $\partial_t \widetilde{F}(t;x)$  term on the right-hand side of (1.0.3) arises from the definition of a partial derivative, while to derive the  $\widetilde{G}(t;x)$  term, we applied the fundamental theorem of calculus (think about both

of these claims own your own!). By the definition of  $\widetilde{F}$  and  $\widetilde{G}$  (see the **Spherical averages** Proposition), it therefore follows from (1.0.3) that

(1.0.4) 
$$u(t,x) = \partial_t \left( t \frac{1}{4\pi t^2} \int_{\partial B_t(x)} f(\sigma) d\sigma \right) + t \frac{1}{4\pi t^2} \int_{\partial B_t(x)} g(\sigma) d\sigma.$$

Differentiating under the integral sign, using the chain rule relation  $\partial_t [f(x+t\omega)] = (\nabla f)(x+t\omega) \cdot \omega = \nabla_{\hat{N}(x+t\omega)} f(x+t\omega)$  (where  $\hat{N}$  is the unit outward normal to  $\partial B_t(x)$ ), and recalling that  $d\sigma = t^2 d\omega$  on  $\partial B_t(x)$ , we have that

$$(1.0.5) t\partial_{t} \left(\frac{1}{4\pi t^{2}} \int_{\partial B_{t}(x)} f(\sigma) d\sigma\right) = t\partial_{t} \left(\frac{1}{4\pi} \int_{\partial B_{1}(0)} \left[f(x+t\omega)\right] d\omega\right) = \frac{t}{4\pi} \int_{\partial B_{1}(0)} \partial_{t} \left[f(x+t\omega)\right] d\omega$$
$$= \frac{t}{4\pi} \int_{\partial B_{1}(0)} \nabla_{\hat{N}(x+t\omega)} f(x+t\omega) d\omega$$
$$\stackrel{\text{def}}{=} \frac{1}{4\pi t} \int_{\partial B_{t}(x)} \nabla_{\hat{N}(\sigma)} f(\sigma) d\sigma.$$

Combining (1.0.4) and (1.0.5), we have that

$$(1.0.6) u(t,x) = \frac{1}{4\pi t^2} \int_{\partial B_t(x)} f(\sigma) d\sigma + \frac{1}{4\pi t} \int_{\partial B_t(x)} \nabla_{\hat{N}(\sigma)} f(\sigma) d\sigma + \frac{1}{4\pi t} \int_{\partial B_t(x)} g(\sigma) d\sigma.$$

We have thus shown (1.0.2).

The fact that  $u \in C^2([0, \infty) \times \mathbb{R}^3)$  follows from differentiating the integrals in the formula (1.0.2) and using the hypotheses on f and g.

Exercise 1.0.1. Show that (1.0.3) holds.

**Exercise 1.0.2.** Verify that  $u \in C^2([0,\infty) \times \mathbb{R}^3)$ , as was claimed at the end of the proof above.

# The Linear Wave Equation: A Geometric Point of View

We will now derive some very important results for solutions to the linear wave equation. The results will exploit interplay between geometry and analysis. Many of the techniques that we will discuss play a central role in current PDE research.

#### 2. Geometric background

Throughout this lecture, standard rectangular coordinates on  $\mathbb{R}^{1+n}$  are denoted by  $(x^0, x^1, \dots, x^n)$ , and we often use the alternate notation  $x^0 = t$ . The Minkowski metric on  $\mathbb{R}^{1+n}$ , which we denote by m, embodies the *Lorentzian geometry* at the heart of Einstein's theory of special relativity. As we will see, this geometry is intimately connected to the linear wave equation. The components of m takes the following form relative to a standard rectangular coordinate system:

(2.0.7) 
$$m_{\mu\nu} = (m^{-1})^{\mu\nu} = \operatorname{diag}(-1, \underbrace{1, 1, \dots, 1}_{n \text{ copies}}).$$

We can view  $m_{\mu\nu}$  as an  $(1+n)\times(1+n)$  matrix of real numbers. It is conventional to label the first row and column of  $m_{\mu\nu}$  starting with "0" rather than "1," so that  $m_{00} = -1$ ,  $m_{22} = 1$ ,  $m_{02} = 0$ , etc. Note that m is symmetric:  $m_{\mu\nu} = m_{\nu\mu}$ .

If X is a vector in  $\mathbb{R}^{1+n}$  with components  $X^{\mu}$  ( $0 \le \mu \le n$ ), then we define its metric dual to be the covector with components  $X_{\mu}$  ( $0 \le \mu \le n$ ) defined by

$$(2.0.8) X_{\mu} \stackrel{\text{def}}{=} \sum_{\alpha=0}^{3} m_{\mu\alpha} X^{\alpha}.$$

This is called "lowering the indices of X with m."

Similarly, given a covector with components  $Y_{\mu}$ , we can use  $(m^{-1})$  to form a vector  $Y^{\mu}$  by raising the indices:

(2.0.9) 
$$Y^{\mu} \stackrel{\text{def}}{=} \sum_{\alpha=0}^{3} (m^{-1})^{\mu\alpha} Y_{\alpha}.$$

These notions of duality are called *metric duality*. They are related to, but distinct from (roughly speaking by a minus sign in the first component), the notion of *basis duality* commonly introduced in linear algebra.

We will make use of *Einstein's summation convention*, in which we avoid writing many of the summation signs  $\Sigma$  to reduce the notational clutter. In particular, repeated indices, with one up and one down, are summed over their ranges. Here is an example:

$$(2.0.10) X_{\alpha}Y^{\alpha} \stackrel{\text{def}}{=} \sum_{\alpha=0}^{3} X_{\alpha}Y^{\alpha} \stackrel{\text{def}}{=} \sum_{\alpha=0}^{3} X_{\alpha}Y^{\alpha} = m_{\alpha\beta}X^{\beta}Y^{\alpha} \stackrel{\text{def}}{=} m_{\alpha\beta}X^{\beta}Y^{\beta} = m_{\alpha\beta}X^{\alpha}Y^{\beta},$$

where the last equality is a consequence of the symmetry property of m.

We now make the following important observation: the linear wave equation  $-\partial_t^2 \phi + \Delta \phi = 0$  can be written as

$$(2.0.11) (m^{-1})^{\alpha\beta}\partial_{\alpha}\partial_{\beta}\phi = 0.$$

We will return to this observation in a bit.

We first provide a standard division of vectors into three classes timelike, spacelike, null.

## Definition 2.0.1.

- (1) Timelike vectors:  $m(X, X) \stackrel{\text{def}}{=} m_{\alpha\beta} X^{\alpha} X^{\beta} < 0$
- (2) Spacelike vectors: m(X,X) > 0
- (3) Null vectors: m(X,X) = 0
- (4) Causal vectors: {Timelike vectors}  $\cup$  {Null vectors}

We also will need to know when a vector is pointing "towards the future." This idea is captured by the next definition.

**Definition 2.0.2.** A vector  $X \in \mathbb{R}^n$  is said to be *future-directed* if  $X^0 > 0$ .

2.1. **Lorentz transformations.** Lorentz transformations play a very important role in the study of the linear wave equation.

**Definition 2.1.1.** A Lorentz transformation is a linear transformation  $\Lambda^{\mu}_{\nu}$  (i.e., a matrix) that preserves the form of the Minkowski metric  $m_{\mu\nu} \stackrel{\text{def}}{=} \text{diag}(-1, 1, 1, \dots, 1)$ :

(2.1.1) 
$$\Lambda^{\alpha}_{\ \mu}\Lambda^{\beta}_{\ \nu}m_{\alpha\beta} = m_{\mu\nu}.$$

In standard matrix notation, (2.1.1) reads

$$\Lambda^T m \Lambda = m,$$

where T denotes the transpose.

By taking the determinant of each side of (2.1.2) and using the basic properties of the determinant, we see that  $|\det(\Lambda)| = 1$ . If  $\det(\Lambda) = 1$ , then  $\Lambda$  is said to be *proper* or *orientation preserving*. It is easy to see that (2.1.1) is equivalent to

(2.1.3) 
$$m(\Lambda X, \Lambda Y) = m(X, Y), \quad \forall \text{ vectors } X, Y \in \mathbb{R}^{1+n},$$

i.e., that the linear transformation  $\Lambda$  preserves the Minkowskian inner product. In (2.1.3),  $m(X,Y) \stackrel{\text{def}}{=} m_{\alpha\beta}X^{\alpha}Y^{\beta}$  and  $\Lambda X$  is the vector with components  $(\Lambda X)^{\mu} = \Lambda^{\mu}_{\alpha}X^{\alpha}$ .

Also note that the left-hand side of (2.1.2) is connected to the linear-algebraic notion of change of basis on  $\mathbb{R}^{1+n}$ . More precisely, an important way of thinking about Lorentz transformations  $\Lambda$  is the following: if we have a standard rectangular coordinate system  $(x^0, \dots, x^n)$  on  $\mathbb{R}^{1+n}$ , and we change coordinates by defining  $y^{\mu} \stackrel{\text{def}}{=} \Lambda^{\mu}_{\alpha} x^{\alpha}$ , then relative to the new coordinate system  $(y^0, \dots, y^n)$ , the Minkowski metric still has the same form  $m_{\mu\nu} = \text{diag}(-1, 1, 1, \dots, 1)$ . This statement would be false if, for example, we changed to polar spatial coordinates, or we dilated spacetime coordinates by setting  $(y^0, \dots, y^n) = \alpha(x^0, \dots, x^n)$  for some constant  $\alpha > 0$ . Thus, the Lorentz transformations capture some invariance properties of m under certain special linear coordinate transformations.

Corollary 2.1.1. If X is timelike, and  $\Lambda$  is a Lorentz transformation, then  $\Lambda X$  is also timelike. Analogous results also hold if X is spacelike or null.

*Proof.* Corollary 2.1.1 easily follows from Definition 2.0.1 and 
$$(2.1.3)$$
.

It can be checked that the Lorentz transformations form a group. In particular:

- If  $\Lambda$  is a Lorentz transformation, then so is  $\Lambda^{-1}$ .
- If  $\Lambda$  and  $\Upsilon$  are Lorentz transformations, then so is their matrix product  $\Lambda \Upsilon$ , which has components  $(\Lambda \Upsilon)^{\mu}_{\nu} \stackrel{\text{def}}{=} \Lambda^{\mu}_{\alpha} \Upsilon^{\alpha}_{\nu}$ .

The condition (2.1.2) can be viewed as  $(n+1)^2$  scalar equations. However, by the symmetry of m, there are plenty of redundancies, so that only  $\frac{1}{2}(n+1)(n+2)$  of the equations are independent. This leaves  $(n+1)^2 - \frac{1}{2}(n+1)(n+2) = \frac{1}{2}n(n+1)$  "free parameters" that determine the matrix  $\Lambda$ . Thus, the Lorentz transformations form a " $\frac{1}{2}n(n+1)$  dimensional" group.

It can be shown that the proper Lorentz group is  $generated^1$  by the  $\frac{(n)(n-1)}{2}$  dimensional subgroup of spatial rotations, and the n dimensional subgroup of proper Lorentz boosts. For the sake of concreteness let's focus on the physical case of n = 3 spatial dimensions.

Then the rotations about the  $x^3$  axis are the set of linear transformations of the form

<sup>&</sup>lt;sup>1</sup>By "generated," we mean that all proper Lorentz transformations can be built out of a finite number of products of boosts and spatial rotations.

(2.1.4) 
$$\Lambda^{\alpha}_{\ \mu} = \begin{bmatrix} 1 & 0 & 0 & 0 \\ 0 & \cos\theta & -\sin\theta & 0 \\ 0 & \sin\theta & \cos\theta & 0 \\ 0 & 0 & 0 & 1 \end{bmatrix},$$

where  $\theta \in [0, 2\pi)$  is the counter-clockwise angle of rotation. Analogous matrices yield the rotations about the  $x^1$  and  $x^2$  axes. Note that the  $X^0$  (i.e. "time") coordinate of vectors X is not affected by such transformations.

The (proper) Lorentz boosts are the famous linear transformations that play a distinguished role in Einstein's theory of special relativity. They are sometimes called *spacetime rotations*, because they intermix the time component  $X^0$  of vectors X with their spatial components  $X^1, X^2, \dots, X^n$ . The Lorentz boosts in the  $x^1$  direction can be expressed as

(2.1.5) 
$$\Lambda^{\alpha}_{\ \mu} = \begin{bmatrix} \cosh \zeta & -\sinh \zeta & 0 & 0 \\ -\sinh \zeta & \cosh \zeta & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \end{bmatrix}$$

where  $\zeta \in (-\infty, \infty)$ . Equivalently, (2.1.5) may be parameterized by

(2.1.6) 
$$\Lambda^{\alpha}_{\ \mu} = \begin{bmatrix} \gamma & -\gamma v & 0 & 0 \\ -\gamma v & \gamma & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \end{bmatrix}$$

where  $v \in (-1,1)$  is a "velocity" and  $\gamma = \sqrt{\frac{1}{1-v^2}}$ . The requirement that |v| < 1 is directly connected to the idea that in special relativity, material particles should never "exceed the speed of light."

2.2. Null frames. It is often the case that the standard basis on  $\mathbb{R}^{1+n}$  is not the best basis for analyzing solutions to the linear wave equation. One of the most useful bases is called a *null frame*, which can vary from spacetime point to spacetime point.

**Definition 2.2.1.** A null frame is a basis for  $\mathbb{R}^{1+n}$  consisting of vectors  $\{L, \underline{L}, e_{(1)}, \dots, e_{(n-1)}\}$ . Here, L and  $\underline{L}$  are null vectors normalized by  $m(L,\underline{L}) = -2$ , and the  $e_{(i)}$  are orthonormal vectors that span the m-orthogonal complement of  $\mathrm{span}(L,\underline{L}): m(e_{(i)},e_{(j)}) = \delta_{ij}, m(L,e_{(i)}) = m(\underline{L},e_{(i)}) = 0$ , for  $1 \le i \le j \le n-1$ . Note that the  $e_{(i)}$  must form a basis for this complement; i.e., since they are m-orthonormal, they must be linearly independent.

In particular, we have the decomposition

(2.2.1) 
$$\mathbb{R}^{1+n} = \operatorname{span}(L, \underline{L}) \oplus \operatorname{span}(e_{(1)}, \dots, e_{(n-1)}),$$

where each of the two subspaces in the above direct sum are m-orthogonal.

**Example 2.2.1.** A common choice of a null frame is to take  $L^{\mu} = (1, \omega^1, \cdots, \omega^n)$ ,  $\underline{L}^{\mu} = (1, -\omega^1, \cdots, -\omega^n)$ , and to take the  $e_{(i)}$  to be any m-orthonormal basis for the m-orthogonal complement of span $(L, \underline{L})$ . Note that this n-1 dimensional complementary space is spanned by the n non-linearly independent vectors  $v_{(i)}^{\mu} \stackrel{\text{def}}{=} (0, -\omega^1, -\omega^2, \cdots, -\omega^{i-1}, 1 - \omega^i, -\omega^{i+1}, \cdots, -\omega^n)$ ,  $1 \leq i \leq n$ . Here,  $\omega^i \stackrel{\text{def}}{=} \frac{x^i}{r}$ ,

and  $r \stackrel{\text{def}}{=} \sqrt{\sum_{i=1}^{n} (x^{i})^{2}}$  is the standard radial coordinate. Observe that  $v_{(i)}$  is formed by subtracting of the "radial part"  $(0, \omega_{1}, \dots, \omega_{n})$  from the standard spatial unit basis vector  $b_{(i)}^{\mu} \stackrel{\text{def}}{=} (0, 0, \dots, 0, \dots, 0)$ . Note that  $\sum_{i=1}^{n} (\omega^{i})^{2} = 1$ .

ith spatial slot

For this null frame, in terms of differential operators,  $\nabla_L = \partial_t + \partial_r$ , while  $\nabla_{\underline{L}} = \partial_t - \partial_r$ . The  $\nabla_{e_{(i)}}$  are the angular derivatives, i.e., derivatives in directions tangential to the Euclidean spheres  $S_{r,t} \stackrel{\text{def}}{=} \{(\tau, x^1, \dots, x^n) \mid \tau = t, \sqrt{\sum_{i=1}^n (x^i)^2} = r.\}$ 

The following proposition shows that the Minkowski metric has a very nice form when expressed relative to a null frame.

Proposition 2.2.1 (Null frame decomposition of m). If  $\{L, \underline{L}, e_{(1)}, \dots, e_{(n-1)}\}$  is a null frame, then we can decompose

(2.2.2) 
$$m_{\mu\nu} = -\frac{1}{2}L_{\mu}\underline{L}_{\nu} - \frac{1}{2}\underline{L}_{\mu}L_{\nu} + \eta h_{\mu\nu},$$

where  $\psi_{\mu\nu}$  is positive-definite on the m-orthogonal complement of  $span(L,\underline{L})$ , and  $\psi_{\mu\nu}$  vanishes on span(L,L).

Similarly, by raising each index on both sides of (2.2.2) with  $m^{-1}$ , we have that

$$(2.2.3) (m^{-1})^{\mu\nu} = -\frac{1}{2}L^{\mu}\underline{L}^{\nu} - \frac{1}{2}\underline{L}^{\mu}L^{\nu} + \eta h^{\mu\nu}.$$

*Proof.* We define  $\eta_{\mu\nu} \stackrel{\text{def}}{=} m_{\mu\nu} + \frac{1}{2}L_{\mu}\underline{L}_{\nu} + \frac{1}{2}\underline{L}_{\mu}L_{\nu}$ . Since  $m(L, L) = m(\underline{L}, \underline{L}) = 0$ , and  $m(L, \underline{L}) = -2$ , it easily follows that  $\eta_{\mu}(L, L) = \eta_{\mu}(L, \underline{L}) = \eta_{\mu}(\underline{L}, \underline{L}) = 0$ . Thus,  $\eta_{\mu\nu}$  vanishes on span $(L, \underline{L})$ .

Since  $m(L, e_{(i)}) = m(\underline{L}, e_{(i)}) = 0$  for  $1 \le i \le n$ , it easily follows that  $\eta h(L, e_{(i)}) = \eta h(\underline{L}, e_{(i)}) = 0$ .

Finally, it also easily follows that  $\psi(e_{(i)}, e_{(j)}) = m(e_{(i)}, e_{(j)}) = \delta_{ij}$ , where  $\delta_{ij} = 1$  if i = j and  $\delta_{ij} = 0$  if  $i \neq j$ , so that  $\{e_{(i)}\}_{i=1}^{n-1}$  is an  $\psi$ -orthonormal basis for the m-orthogonal complement of span $(L, \underline{L})$ .

Remark 2.2.1. If the null frame is the one described in Example 2.2.1, then  $mu_{\mu\nu}$  is a metric that is positive definite in the "angular" directions, and 0 otherwise. In fact,  $mu_{\mu\nu}$  is the standard Euclidean metric on the family Euclidean spheres  $S_{r,t}$ .  $mu_{\mu\nu}$  is known as the first fundamental form of the spheres relative to  $mu_{\mu\nu}$ .

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## MATH 18.152 COURSE NOTES - CLASS MEETING # 13

## 18.152 Introduction to PDEs, Fall 2011

## Class Meeting # 13: Geometric Energy Estimates

Professor: Jared Speck

1.  $\square_m$ , the energy-momentum tensor, and compatible currents

The following shorthand notation is often used for the "linear wave operator associated to m:"

$$(1.0.1) \qquad \Box_m \stackrel{\text{def}}{=} (m^{-1})^{\alpha\beta} \partial_{\alpha} \partial_{\beta}.$$

Using this notation, the wave equation  $-\partial_t^2 + \Delta \phi = 0$  can be expressed as

$$\Box_m \phi = 0.$$

We now introduce a very important object called the *energy-momentum tensor*. As we will see, it encodes some very important conservation laws associated to solutions of (1.0.2).

**Definition 1.0.1.** The energy-momentum tensor associated to equation (1.0.2) is

(1.0.3) 
$$T_{\mu\nu} \stackrel{\text{def}}{=} \partial_{\mu}\phi \partial_{\nu}\phi - \frac{1}{2}m_{\mu\nu}(m^{-1})^{\alpha\beta}\partial_{\alpha}\phi \partial_{\beta}\phi.$$

Later in the course, we will hopefully have time to motivate its derivation in the larger context of *variational methods*. For now, we will simply study/use its useful properties.

Note that  $T_{\mu\nu}$  is symmetric:

$$(1.0.4) T_{\mu\nu} = T_{\nu\mu}.$$

In your homework, you will prove the following very important positivity property of T, which is called the *dominant energy condition*.

# Lemma 1.0.1 (Dominant Energy Condition for $T_{\mu\nu}$ ).

(1.0.5)

 $T(X,Y) \stackrel{def}{=} T_{\alpha\beta}X^{\alpha}Y^{\beta} \ge 0$  if X, Y are both timelike and future-directed or timelike and past-directed. Since causal vectors are the limit of timelike vectors, we have the following consequence of (1.0.5):

(1.0.6)

 $T(X,Y) \stackrel{\text{def}}{=} T_{\alpha\beta}X^{\alpha}Y^{\beta} \ge 0$  if X,Y are future-directed and causal or past-directed and causal. As before, we can raise the indices of T:

(1.0.7) 
$$T^{\mu\nu} = (m^{-1})^{\mu\alpha} (m^{-1})^{\nu\beta} T_{\alpha\beta}.$$

A very special case of Lemma 1.0.1 is the following, which corresponds to  $X^{\mu} = Y^{\mu} = \delta_0^{\mu} = (1, 0, 0, \dots, 0)$  in the lemma:

(1.0.8) 
$$T_{00} = T^{00} = \frac{1}{2} \sum_{\mu=0}^{3} (\partial_{\mu} \phi)^{2} = \frac{1}{2} |\nabla_{t,x} \phi|^{2}.$$

The derivation of (1.0.8) is a simple computation that you should do for yourself. Note that  $T_{00}$  is positive definite in all of the derivatives of  $\phi$ . This fact will play an important role in Theorem 2.1 below.

The next lemma shows that  $T^{\mu\nu}$  is divergence-free whenever  $\phi$  verifies the wave equation. This fact is intimately connected to the derivation of conservation laws, which are fundamental ingredients in the study of hyperbolic PDEs.

**Lemma 1.0.2** (The divergence of  $T^{\mu\nu}$ ). Let  $T_{\mu\nu}$  be the energy-momentum tensor defined in (1.0.3). Then

(1.0.9) 
$$\partial_{\mu} T^{\mu\nu} = (\Box_{m} \phi) (m^{-1})^{\nu\alpha} \partial_{\alpha} \phi.$$

In particular, if  $\phi$  is a solution to (1.0.2), then

$$\partial_{\mu}T^{\mu\nu} = 0.$$

*Proof.* The proof is a computation that uses the symmetry property  $(m^{-1})^{\mu\nu} = (m^{-1})^{\nu\mu}$  and the fact that we are allowed to interchange the order of partial derivatives (if  $\phi$  is sufficiently smooth):

$$(1.0.11) \qquad \partial_{\mu}T^{\mu\nu} = \partial_{\mu}\Big((m^{-1})^{\mu\alpha}(m^{-1})^{\nu\beta}\partial_{\alpha}\phi\partial_{\beta}\phi - \frac{1}{2}(m^{-1})^{\mu\nu}(m^{-1})^{\alpha\beta}\partial_{\alpha}\phi\partial_{\beta}\phi\Big)$$

$$= (\Box_{m}\phi)(m^{-1})^{\nu\beta}\partial_{\beta}\phi + (m^{-1})^{\mu\alpha}(m^{-1})^{\nu\beta}(\partial_{\alpha}\phi)\partial_{\mu}\partial_{\beta}\phi$$

$$- \frac{1}{2}(m^{-1})^{\mu\nu}(m^{-1})^{\alpha\beta}(\partial_{\mu}\partial_{\alpha}\phi)\partial_{\beta}\phi - \frac{1}{2}(m^{-1})^{\mu\nu}(m^{-1})^{\alpha\beta}(\partial_{\alpha}\phi)\partial_{\mu}\partial_{\beta}\phi$$

$$= (\Box_{m}\phi)(m^{-1})^{\nu\beta}\partial_{\beta}\phi,$$

where the last three terms have canceled each other.

As we will soon see, the energy-momentum tensor provides an amazingly convenient way of bookkeeping in the divergence theorem. However, in order to apply the divergence theorem, we need to find a **useful** vectorfield to take the divergence of. By useful, we mean a vectorfield that can be used to control a solution  $\phi$  to the wave equation. One way of constructing a useful vectorfield is to start with an auxiliary vectorfield X and then to contract it with the energy momentum tensor to form a new vectorfield X. The next definition shows how to do this.

**Definition 1.0.2.** Given any vectorfield X, we associate to it the following *compatible current*, which is itself a vectorfield:

$$(1.0.12) (X)J^{\mu} \stackrel{\text{def}}{=} T^{\mu\alpha}X_{\alpha}.$$

So which vectors X are the useful ones? It turns out that the answer is causal vectors. This fact is closely connected to the dominant energy condition (1.0.5). This will become more clear in our proof of theorem 2.1 below; Note that by Lemma 1.0.1,  $J^{\mu}Y_{\mu} \stackrel{\text{def}}{=} T^{\mu\alpha}X_{\alpha}Y_{\mu} = T_{\alpha\beta}X^{\alpha}Y^{\beta} \stackrel{\text{def}}{=} T(X,Y) \ge 0$  if X,Y are both timelike and future-directed (i.e.,  $X^0,Y^0>0$ ) or past-directed (i.e.,  $X^0,Y^0<0$ ).

In order to apply the divergence theorem to  ${}^{(X)}J^{\mu}$ , we of course need to know its divergence. We carry out this computation in the next corollary.

Corollary 1.0.3. Using (1.0.4) and (1.0.10), we have that

(1.0.13) 
$$\partial_{\mu} \binom{(X)}{J^{\mu}} = T^{\alpha\beta(X)} \pi_{\alpha\beta},$$

where

$$(1.0.14) (X)_{\pi_{\mu\nu}} \stackrel{def}{=} \frac{1}{2} \left( \partial_{\mu} X_{\nu} + \partial_{\nu} X_{\mu} \right)$$

is called the deformation tensor of X.

We now state a version of the divergence theorem that is tailored to our study of the linear wave equation.

**Theorem 1.1** (Divergence Theorem). Let  $\phi$  be a solution to the linear wave equation  $\Box_m \phi = 0$ . Let X be any vectorfield, and let (X)J be the compatible current define in Definition 1.0.2. Let  $\Omega \subset \mathbb{R}^{1+n}$  be a domain with boundary  $\partial \Omega$ . Then the following integral identity holds:

(1.0.15) 
$$\int_{\partial\Omega} \hat{N}_{\alpha}{}^{(X)} J^{\alpha}[\phi(\sigma)] d\sigma = \int_{\Omega} \partial_{\mu} {}^{(X)} J^{\mu}[\phi(t,x)] dt d^{n}x.$$

### 2. Energy Estimates and Uniqueness

We will now use the results of the previous section to derive some extremely important energy estimates for solutions to  $\square_m \phi = 0$ . The results we derive are a geometry version of integration by parts + the divergence theorem. They could alternatively be derived by multiplying both sides of the wave equation by a suitable quantity and then integrating by parts over a suitable hypersurfaces, but there is a substantial gain in geometric insight that accompanies our use of compatible currents.

Theorem 2.1 (Energy estimates in a cone). Let  $\phi(t,x)$  be a  $C^2$  solution to the 1+n dimensional global Cauchy problem for the linear wave equation

$$(2.0.16) \qquad \Box_m \phi = 0,$$

$$\phi(0,x) = f(x), \qquad x \in \mathbb{R}^n.$$

(2.0.17) 
$$\phi(0,x) = f(x), \qquad x \in \mathbb{R}^n,$$
(2.0.18) 
$$\partial_t \phi(0,x) = g(x), \qquad x \in \mathbb{R}^n.$$

Let  $R \in [0, \infty]$ , let X be the past-directed timelike vector defined by  $X^{\mu} = -\delta_0^{\mu}$ , and let  $(X)J^{\mu}[\phi(t,y)]$  be the compatible current (1.0.12) associated to X. Note that by (1.0.8),  $(X)J^{\mu}[\phi(t,y)] = |\nabla_{t,y}\phi(t,y)|^2 = |\nabla_{t,y}\phi(t,y)|^2$  $\sum_{\mu=0}^{n} (\partial_{\mu} \phi)^{2} = (\partial_{t} \phi)^{2} + \sum_{i=1}^{n} (\partial_{i} \phi)^{2}.$  Define the square of the energy  $E[\phi](t)$  by

(2.0.19) 
$$E^{2}[\phi](t) \stackrel{\text{def}}{=} \int_{B_{R-t}(p)} \hat{N}_{\mu}{}^{(X)} J^{\mu}[\phi(t,y)] d^{n}y = \frac{1}{2} \int_{B_{R-t}(p)} |\nabla_{t,y}\phi(t,y)|^{2} d^{n}y,$$

where  $\hat{N}_{\mu} = \delta^{0}_{\mu}$  (and therefore  $\hat{N}^{\mu} = -\delta^{\mu}_{0}$ ) is the past-pointing unit normal covector to  $\{t\} \times B_{R-t}(p) \subset \mathbb{R}^{4}$ , and  $B_{R}(p) \subset \mathbb{R}^{3}$  denotes the solid Euclidean ball of radius R centered at p. Then

(2.0.20) 
$$E[\phi](t) \le E[\phi](0).$$

Proof. The goal is to apply Theorem 1.1 to the solid truncated backwards light cone  $C_{t,p;R} \stackrel{\text{def}}{=} \{(\tau,y) \in [0,\infty) \times \mathbb{R}^n \mid |y-p| \le R-\tau\}$  and to make use of the dominant energy condition. It is easy to see that  $\partial C_{t,p;R} = \mathcal{B} \cup \mathcal{M}_{t,p;R} \cup \mathcal{T}$ , where  $\mathcal{B} \stackrel{\text{def}}{=} \{0\} \times B_R(p)$  is the flat base of the truncated cone,  $\mathcal{T} \stackrel{\text{def}}{=} \{t\} \times B_{R-t}(p)$  is the flat top of the truncated cone, and  $\mathcal{M}_{t,p;R} \stackrel{\text{def}}{=} \{(\tau,y) \in [0,\infty) \times \mathbb{R}^n \mid |y-p| = R-\tau\}$  is the mantle of the truncated cone.

By Theorem 1.1, we have that

(2.0.21) 
$$E[\phi](t) - E[\phi](0) + F[\phi] = \int_{C_{t,n}} \partial_{\mu} \binom{(X)}{J^{\mu}} [\phi(\tau, y)] d\tau d^{n}y,$$

where

(2.0.22) 
$$F[\phi] \stackrel{\text{def}}{=} \int_{\mathcal{M}_{t,v;R}} \hat{N}_{\alpha}{}^{(X)} J^{\alpha}[\phi(\sigma)] d\sigma$$

is the "flux" associated to  $\mathcal{M}_{t,p;R}$ . Since  $\phi$  solves the wave equation (2.0.16), and since  ${}^{(X)}\pi_{\mu\nu} = 0$ , the identity (1.0.13) implies that the right-hand side of (2.0.21) is 0. Therefore,

(2.0.23) 
$$E[\phi](t) - E[\phi](0) + F[\phi] = 0.$$

We claim that  $F[\phi] \ge 0$ . The energy inequality (2.0.20) would then follow from (2.0.23). They key observation for showing that  $F[\phi] \ge 0$  is the following. Along the mantle  $\mathcal{M}_{t,p;R}$ , it is easy to see (draw the picture!) that  $\hat{N}_{\mu} = \underline{L}_{\mu}$ , where  $\underline{L}$  is a past-directed null vector. Therefore, the integrand in (2.0.22) is equal to  $T_{\alpha\beta}X^{\alpha}\underline{L}^{\beta}$ , and since X is a past-directed timelike vector, the dominant energy condition (1.0.6) implies that  $T_{\alpha\beta}X^{\alpha}\underline{L}^{\beta} \ge 0$ . Therefore,  $F[\phi] \ge 0$  as desired.

Theorem 2.1 can easily be used to prove the following **local** uniqueness result for solutions to the linear wave equation.

Corollary 2.0.4 (Uniqueness). Suppose that two  $C^2$  solutions  $\phi_1$  and  $\phi_2$  to (2.0.16) have the same initial data on  $B_R(p) \subset \{(\tau, y) \mid \tau = 0\}$ . Then the two solutions agree on the "solid backwards light cone"  $C_{p;R} \stackrel{def}{=} \{(\tau, y) \mid 0 \le \tau \le R, 0 \le |y - p| \le R - \tau\}$ .

*Proof.* Define  $\psi \stackrel{\text{def}}{=} \phi_1 - \phi_2$ . Then  $\psi$  verifies (2.0.16) and furthermore,  $E[\psi](0) = 0$ . Thus, by Theorem 2.1,  $E[\psi](t) = 0$  for  $0 \le t \le R$ . Therefore, from the definition of  $E[\psi](t)$ , it follows that  $\nabla_{\tau,y}\psi(\tau,y) = 0$  for  $(\tau,y) \in \mathcal{C}_{p;R}$ . Thus, by elementary analysis,  $\psi$  is constant in  $\mathcal{C}_{p;R}$ . But  $\psi(0,x) = 0$  for  $(0,x) \in \mathcal{C}_{p;R}$ . Thus,  $\psi(\tau,y) = 0$  for all points  $(\tau,y) \in \mathcal{C}_{p;R}$ .

Corollary 2.0.4 is one illustration of the *finite speed of propagation* property associated to the linear wave equation. Another way to think about it is the following. Suppose you alter the initial conditions *outside* of  $B_R(p)$ , but not on  $B_R(p)$  itself. Then this alteration has no effect whatsoever on the behavior of the solution in the spacetime region  $C_{p;R}$  Think about this claim yourself; it follows easily from the Corollary!

#### 3. Developments, Domain of Dependence, and Range of Influence

We will now develop a language for discussing the finite speed of propagation properties of the linear wave equation in more detail. If we had more time in this course, we could adopt a more geometric point of view that would apply to many other hyperbolic PDEs. This would involve fleshing out our discussion of Lorentzian geometry, and also developing a generalized version of geometry that applies to a large class of PDEs.

Warning 3.0.1. Some people permute or even severely alter the following definitions, which can be very confusing. The definitions below therefore indicate some of my biases.

**Definition 3.0.3 (Development).** Let  $S \subset \{(t,x) \mid t=0\}$  be a set. Assume that that we know the initial data  $\phi(0,x) = f(x)$ ,  $\partial_t \phi(0,x) = g(x)$  for the wave equation (1.0.2), but only for  $x \in S$ . Then a future development  $\Omega$  of S is defined to be a "future" region of spacetime  $\Omega \subset \mathbb{R}^{1+n} \cap \{(t,x) \mid t \geq 0\}$  on which the solution  $\phi(t,x)$  to (1.0.2) is uniquely determined by the initial data on S. A past development  $\mathcal{D}^-(S)$  can be analogously defined (replace  $t \geq 0$  with  $t \leq 0$  in the previous definition).

**Example 3.0.1.** If  $B_R(p)$  and  $C_{p;R}$  are as in Corollary 2.0.4, then  $C_{p;R}$  is a development of  $B_R(p)$ . You can imagine that the solution knows how to "develop" in  $C_{p;R}$  from the initial conditions on its subset  $B_R(p)$ .

**Definition 3.0.4** (Maximal development). The maximal future development of S, which we denote by  $\mathcal{D}^+(S)$ , is defined to be the union of all future developments of S. The maximal past development  $\mathcal{D}^-(S)$  can be analogously defined. The maximal development of S is defined to be  $\mathcal{D}^+(S) \cup \mathcal{D}^-(S)$ .

**Example 3.0.2.** Consider the plane  $P \stackrel{\text{def}}{=} \{(t, x^1, x^2, x^3) \mid x^1 = 0\}$ . Then using techniques from a more advanced course, one could show that  $\mathcal{D}(P) = P$  for the wave equation (1.0.2). That is, knowing the conditions of a solution  $\phi$  along P is not enough information to determine the solution anywhere else. This is closely connected to the fact that all smooth curves in P have tangent vectors that are timelike relative to the Minkowski metric.

**Definition 3.0.5** (Domain of dependence). Let  $\Omega \subset \mathbb{R}^{1+n}$ . Assume that  $\phi$  is a solution to the wave equation (1.0.2) in  $\Omega$ . A domain of dependence for  $\Omega$  is a set S such that  $\phi$  is completely determined on  $\Omega$  from only the data  $\phi|_S$  and  $\nabla_{t,x}\phi|_S$ .

**Remark 3.0.1.** For general nonlinear hyperbolic PDEs, domains of dependence depend both on  $\Omega$  and the solution  $\phi$  itself. However, for the linear wave equation, domains of dependence do not depend on the solution. Roughly speaking, this is because the "geometry of the solution" is predetermined by the Minkowski metric m.

**Example 3.0.3.** In 1+1 dimensions, a domain of dependence for the spacetime point (t, x) (for the wave equation (1.0.2)) is the "initial data" interval  $\{0\} \times [x-t,x+t]$ . Another domain of dependence for this point is the interval  $\{t/2\} \times [x-t/2,x+t/2]$ . A trivial example is that (t,x) is a domain of dependence for itself.

**Example 3.0.4.** In 1+3 dimensions, a domain of dependence for the positive t axis  $\{(t, x^1, x^2, x^3) \mid x^1 = x^2 = x^3 = 0, t \ge 0\}$  (for the wave equation (1.0.2)) is all of "space:"  $\{(t, x^1, x^2, x^3) \mid t = 0\}$ . Any subset of space is *not* a domain of dependence for the positive t axis.

The next definition is complementary to the notion of domain of dependence.

**Definition 3.0.6** (Range of influence). Assume that  $\phi$  is a solution to the wave equation (1.0.2) in  $\mathbb{R}^{1+n}$ . The range of influence  $\mathcal{R}$  for a set  $S \subset \mathbb{R}^{1+n}$  is the set of all points  $(t,x) \in \mathbb{R}^{1+n}$  such that  $\phi(t,x)$  is affected by the initial data  $\phi|_S$  and  $\nabla_{t,x}\phi|_S$ .

**Example 3.0.5.** In 1 + 1 dimensions, the (future) range of influence (for  $t \ge 0$ ) of the interval  $S = \{0\} \times [-1, 1]$  is  $\mathcal{R} = \{(t, x) \mid -t - 1 \le x \le t + 1\}$ .

**Example 3.0.6.** In 1 + 1 dimensions, the (future) range of influence (for  $t \ge 0$ ) of the t axis  $S = \{(t,0) | t \ge 0\}$  is  $\mathcal{R} = \{(t,x) | t \ge 0\}$ .

**Example 3.0.7.** In 1+3 dimensions, the (future) range of influence (for  $t \ge 0$ ) of  $S = \{0\} \times \partial B_1(0)$  is  $\mathcal{R} = \{(t,x) \mid 0 \le t \le 1, |x| = 1 - t\} \cup \{(t,x) \mid 0 \le t < t, |x| = 1 + t\}$  where  $|x| \stackrel{\text{def}}{=} \sqrt{(x^1)^2 + (x^2)^2 + (x^3)^2}$ . This is a consequence of the Sharp Huygens' Principle.

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# MATH 18.152 COURSE NOTES - CLASS MEETING # 15

## 18.152 Introduction to PDEs, Fall 2011

Class Meeting # 15: Classification of second order equations

Professor: Jared Speck

### 1. REVIEW OF THREE IMPORTANT EXAMPLES OF PDES

Let's review some basic facts concerning the three PDEs we've examined in detail thus far.

| Equation                                        | Type                   | Well-posed problems               | Features                                     |
|-------------------------------------------------|------------------------|-----------------------------------|----------------------------------------------|
| $\Delta u(x) = f(x)$                            | Elliptic               | Boundary value prob-              | mean value properties;                       |
|                                                 |                        | lems: All of $\mathbb{R}^n$ (with | maximum principle; Har-                      |
|                                                 |                        | boundary conditions               | nack inequality                              |
|                                                 |                        | at $\infty$ ); finite bound-      |                                              |
|                                                 |                        | aries under Dirichlet,            |                                              |
|                                                 |                        | Neumann, Robin,                   |                                              |
|                                                 |                        | or Mixed boundary                 |                                              |
|                                                 |                        | conditions                        |                                              |
| $\partial_t u(t,x) - \Delta u(t,x) = f(t,x)$    | Diffusive (parabolic): | Initial value (Cauchy)            | Infinite speeds of propaga-                  |
|                                                 |                        | problems: all of $\mathbb{R}^n$   | tion; smoothing properties;                  |
|                                                 |                        | at $t = 0$ ; Initial +            | maximum principle, $t^{-n/2}$                |
|                                                 |                        | boundary value prob-              | decay as $t \to \infty$ for the              |
|                                                 |                        | lems: data at $t = 0 +$           | global Cauchy problem                        |
|                                                 |                        | Dirichlet, Neumann,               |                                              |
|                                                 |                        | Robin, or Mixed                   |                                              |
|                                                 |                        | boundary conditions               |                                              |
| $-\partial_t^2 u(t,x) + \Delta u(t,x) = f(t,x)$ | Hyperbolic             | Initial value (Cauchy)            | Finite speed of propagation;                 |
|                                                 |                        | problems: all of $\mathbb{R}^n$   | domain of dependence and                     |
|                                                 |                        | at $t = 0$ ; Initial +            | influence; energy identities;                |
|                                                 |                        | boundary value prob-              | order $t^{(1-n)/2}$ decay as $t \to -\infty$ |
|                                                 |                        | lems: data at $t = 0 +$           | $\infty$ for the global Cauchy               |
|                                                 |                        | Dirichlet, Neumann,               | problem                                      |
|                                                 |                        | Robin, or Mixed                   |                                              |
|                                                 |                        | boundary conditions               |                                              |

#### 2. Motivating example

Let's consider the following second-order linear PDE on  $\mathbb{R}^{1+n}$ :

(2.0.1) 
$$\mathcal{L}u \stackrel{\text{def}}{=} A^{\alpha\beta} \partial_{\alpha} \partial_{\beta} u + B^{\alpha} \partial_{\alpha} u + Cu = 0.$$

In (2.0.1), A, B, C are allowed to be functions of the coordinates  $(x^0, \dots, x^n)$ . We will also use the standard notation  $x^0 = t$ . By the symmetry of the mixed partial derivatives, we can also assume that A is symmetric:

$$(2.0.2) A^{\mu\nu} = A^{\nu\mu}.$$

The question we would like to address at the moment is the following: what are the basic properties of solutions to (2.0.1)? Is this equation most like a Laplace, heat, or wave equation? That is, is (2.0.1) elliptic, diffusive, or hyperbolic? As we will see, the most important part of equation (2.0.1) in this context is the principal part  $A^{\alpha\beta}\partial_{\alpha}\partial_{\beta}u$ , which involves the top-order derivatives.

To begin answering this question, let's start with a simple example on  $\mathbb{R}^2$ . Let's try to classify the following equation:

(2.0.3) 
$$\mathcal{L}u \stackrel{\text{def}}{=} \partial_t^2 u - 4\partial_t \partial_x u + 2\partial_x^2 u = 0.$$

Note that it would be easy to answer our question if we were able to make a linear change of variables that eliminates the cross term  $-4\partial_t\partial_x u$ ; the PDE would then look just like one of the other ones we have already studied. More precisely, let's try to eliminate the cross terms by making good choices for the constants a, b, c, d in the following linear change variables:

$$(2.0.4a) \widetilde{t} = at + bx,$$

$$(2.0.4b) \widetilde{x} = ct + dx.$$

In order to have a viable change of variables, we also need to achieve the following non-degeneracy condition from linear algebra:

$$(2.0.5) ad - bc \neq 0.$$

(2.0.5) states the determinant of the above linear transformation is non-zero, and that the transformation is non-degenerate.

Then using the chain rule, we have that

(2.0.6a) 
$$\partial_t = \frac{\partial \widetilde{t}}{\partial t} \partial_{\widetilde{t}} + \frac{\partial \widetilde{x}}{\partial t} \partial_{\widetilde{x}} = a \partial_{\widetilde{t}} + c \partial_{\widetilde{x}},$$

(2.0.6b) 
$$\partial_x = \frac{\partial \widetilde{t}}{\partial x} \partial_{\widetilde{t}} + \frac{\partial \widetilde{x}}{\partial x} \partial_{\widetilde{x}} = b \partial_{\widetilde{t}} + d \partial_{\widetilde{x}}.$$

Inserting (2.0.6a) - (2.0.6b) into (2.0.3), we compute that

$$(2.0.7) \mathcal{L}u = (a^2 - 4ab + 2b^2)\partial_{\tilde{t}}^2 u + (2ac + 4bd - 4ad - 4bc)\partial_{\tilde{t}}\partial_{\tilde{x}} u + (c^2 - 4cd + 2d^2)\partial_{\tilde{x}}^2 u.$$

To make the cross term in (2.0.7) vanish, we now choose

$$(2.0.8) a = 1, b = 0, c = 2, d = 1.$$

Note that (2.0.8) also verifies the non-degeneracy condition (2.0.5). We remark that other choices would also have worked. In the new coordinates, we have that

(2.0.9) 
$$\mathcal{L}u = \partial_{\tilde{t}}^2 u - 2\partial_{\tilde{x}}^2 u.$$

Dividing by -2, we see that the PDE (2.0.3) was actually a "standard" linear wave equation in disguise:

$$(2.0.10) -\frac{1}{2}\partial_{\tilde{t}}^2 u + \partial_{\tilde{x}}^2 = 0.$$

Relative to the coordinates  $(\tilde{t}, \tilde{x})$ , the "speed" associated to the wave equation (2.0.10) is  $\sqrt{2}$ . Let's do another example. Consider the PDE

(2.0.11) 
$$\mathcal{L}u \stackrel{\text{def}}{=} -2\partial_t^2 u - 2\partial_t \partial_x u - \partial_x^2 u + \partial_x u = 0.$$

Using (2.0.6a) - (2.0.6b) again, we compute that

$$(2.0.12) \qquad \mathcal{L}u = (-2a^2 - 2ab - b^2)\partial_{\tilde{t}}^2 u + (-2ac - bd - 2ad - 2bc)\partial_{\tilde{t}}\partial_{\tilde{x}} u + (-2c^2 - 4cd - d^2)\partial_{\tilde{x}}^2 u + b\partial_{\tilde{\tau}} u + d\partial_{\tilde{x}} u.$$

Choosing

(2.0.13) 
$$a = \frac{1}{\sqrt{2}}, \quad b = 0, \quad c = -1, \quad d = 1,$$

we see that

(2.0.14) 
$$\mathcal{L}u = -\partial_{\tilde{t}}^2 u - \partial_{\tilde{x}}^2 u + \partial_{\tilde{x}} u.$$

Thus, multiplying by -1, we see that (2.0.11) is really just a Laplace-like equation in disguise:

(2.0.15) 
$$\partial_{\tilde{t}}^2 u + \partial_{\tilde{x}}^2 u - \partial_{\tilde{x}} u = 0.$$

Equation (2.0.11) is therefore elliptic. We remark that the first-order term in (2.0.15) does not affect the elliptic nature of the system.

Let's do one final example. Consider the PDE

(2.0.16) 
$$\mathcal{L}u \stackrel{\text{def}}{=} \partial_t^2 u - 2\partial_t \partial_x u + \partial_x^2 u + \partial_x u = 0.$$

Using (2.0.6a) - (2.0.6b) again, we compute that

$$\mathcal{L}u = (a^2 - 2ab + b^2)\partial_{\tilde{t}}^2 u + (2ac + 2bd - 2ad - 2bc)\partial_{\tilde{t}}\partial_{\tilde{x}} u + (c^2 - 2cd + d^2)\partial_{\tilde{x}}^2 u + b\partial_{\tilde{t}} u + d\partial_{\tilde{x}} u.$$

Choosing

$$(2.0.18) a = 1, b = 0, c = -1, d = -1,$$

we see that

$$\mathcal{L}u = \partial_{\tilde{t}}^2 u - \partial_{\tilde{x}} u.$$

Thus, (2.0.16) is equivalent to

$$(2.0.20) -\partial_{\widetilde{x}}u + \partial_{\widetilde{\tau}}^2 u = 0.$$

Now observe that (2.0.20) is just the standard heat equation, with the variable  $\tilde{x}$  playing the role of "time" and  $\tilde{t}$  playing the role of "space." Equation (2.0.20) is therefore diffusive (parabolic).

#### 3. A General Framework

In this section, we will establish a general framework for classifying second order constant coefficient scalar PDEs. The framework will cover the three examples from the previous section as special cases. The proof will reveal that the classification is intimately connected to the theory of quadratic forms from linear algebra. Throughout this section, we will use the notation

$$(3.0.21) x = (x^0, x^1, \dots, x^n).$$

As above, we will investigate PDEs of the form

(3.0.22) 
$$\mathcal{L}u \stackrel{\text{def}}{=} A^{\alpha\beta} \partial_{\alpha} \partial_{\beta} u + B^{\alpha} \partial_{\alpha} u + Cu = 0,$$

where  $A^{\mu\nu} = A^{\nu\mu}$ .

We begin by providing a simple version of Hadamard's classic definitions.

**Definition 3.0.1** (Hadamard's classification of second order scalar PDEs). Equation (3.0.22) is respectively said to be *elliptic*, *hyperbolic*, or *parabolic* according to the following conditions on the  $(1+n) \times (1+n)$  symmetric matrix A:

- All of the eigenvalues of A have the same sign elliptic
- n of the eigenvalues of A have the same (non-zero) sign, and the remaining one has the opposite (non-zero) sign **hyperbolic**
- n of the eigenvalues of A have the same (non-zero) sign, and the remaining one is 0 **parabolic**

**Remark 3.0.1.** Many of the ideas in this section, including the definition above, can be generalized to include the case where A depends on (x), or even on the solution u itself; PDEs of the latter type are said to be *quasilinear*.

We now state and prove the main classification theorem.

Theorem 3.1 (Classification of second order constant-coefficient PDEs). Consider the following second order constant coefficient PDE

(3.0.23) 
$$\mathcal{L}u(x) \stackrel{def}{=} A^{\alpha\beta} \partial_{\alpha} \partial_{\beta} u(x) + B^{\alpha} \partial_{\alpha} u(x) + Cu(x) = 0,$$

where  $\partial_{\alpha} \stackrel{\text{def}}{=} \frac{\partial}{\partial x^{\alpha}}$ . Then there exists a linear change of variables  $y^{\mu} = M_{\alpha}^{\ \mu} x^{\alpha}$  such that

- If all of the eigenvalues of  $A^{\mu\nu}$  have the same (non-zero) sign, then (3.0.23) can be written as  $\pm \mathcal{L}u = \Delta_y u(y) + \widetilde{B}^{\alpha} \frac{\partial}{\partial y^{\alpha}} u(y) + Cu(y) = 0$ , where  $\Delta_y \stackrel{def}{=} \sum_{\mu=0}^n \frac{\partial^2}{(\partial y^{\alpha})^2}$ .
- If n of the eigenvalues of A have the same (non-zero) sign, and the remaining one has the opposite (non-zero) sign, then (3.0.23) can be written as  $\pm \mathcal{L}u = \Box_y u(y) + \widetilde{B}^\alpha \frac{\partial}{\partial y^\alpha} u(y) + Cu(y) = 0$ , where  $\Box_y \stackrel{\text{def}}{=} (m^{-1})^{\alpha\beta} \frac{\partial}{\partial y^\alpha} \frac{\partial}{\partial y^\beta}$  is the standard linear wave operator, and  $(m)^{-1} = diag(-1, 1, 1, \dots, 1)$  is the standard Minkowskian matrix.

• If n eigenvalues  $\lambda^{(1)}, \dots, \lambda^{(n)}$  of A have the same (non-zero) sign, and the remaining one is  $\lambda^{(0)} = 0$ , then (3.0.23) can be written as  $\pm \mathcal{L}u = \widetilde{B}^0 \frac{\partial}{\partial y^0} u(y^0, y^1, \dots, y^n) + \sum_{i=1}^n \frac{\partial^2}{(\partial y^i)^2} u(y^0, y^1, \dots, y^n) + \sum_{i=1}^n \widetilde{B}^i \frac{\partial}{\partial y^i} u(y^0, y^1, \dots, y^n) + Cy = 0$ . Furthermore, let  $v^{(0)}, v^{(1)}, \dots, v^{(n)}$  be a corresponding diagonalizing unit-length co-vector basis. More precisely, this means that  $\sum_{\alpha=0}^n |v_\alpha^{(\mu)}|^2 = 1$  for  $0 \le \mu \le n$ , that  $A^{\alpha\beta}v_\alpha^{(\mu)}v_\beta^{(\nu)} = \lambda^{(\mu)}$  if  $\mu = \nu$ , and that  $A^{\alpha\beta}v_\alpha^{(\mu)}v_\beta^{(\nu)} = 0$  if  $\mu \ne \nu$  (standard linear algebraic theory guarantees the existence of such a basis). Then if the non-zero vector B satisfies  $B^{\alpha}v_\alpha^{(0)} \ne 0$ , we also have that  $\widetilde{B}^0 \ne 0$ .

**Remark 3.0.2.** The " $\pm$ " sign above distinguishes whether or not most of the eigenvalue of  $A^{\mu\nu}$  are positive or negative. For example, if all of the eigenvalues of  $A^{\mu\nu}$  are positive, then  $\mathcal{L}u = \Delta_y u(y) + \cdots$ , while if they are all negative, then  $\mathcal{L}u = -\Delta_y u(y) + \cdots$  (and similarly for the other two cases).

*Proof.* Let's consider the first case, in which all of the eigenvalues have the same (non-zero) sign. Then by standard linear algebra, since  $A^{\mu\nu}$  is symmetric and positive definite (perhaps after multiplying it by -1), there exists an invertible "change-of-basis" matrix  $M_{\mu}^{\nu}$  such that

$$(3.0.24) M_{\alpha}{}^{\mu}A^{\alpha\beta}M_{\beta}{}^{\nu} = I^{\mu\nu},$$

where  $I^{\mu\nu} \stackrel{\text{def}}{=} \text{diag}(1,1,\cdots,1)$  is the  $(n+1)\times(n+1)$  identity matrix. In fact, we can choose

(3.0.25) 
$$M_{\alpha}^{\ \mu} = \frac{1}{\sqrt{|\lambda^{(\mu)}|}} v_{\alpha}^{(\mu)} \text{ (no summation in } \mu),$$

where  $\lambda^{(\mu)}$  is the "eigenvalue" of A corresponding to the unit-length covector  $v_{\alpha}^{(\mu)}$  (i.e.,  $\sum_{\alpha=0}^{n} |v_{\alpha}^{(\mu)}|^2 = 1$ ) appearing in the statement of the theorem.

We now make the linear change of variables  $y^{\mu} = M_{\alpha}^{\ \mu} x^{\alpha}$ . Then by the chain rule,  $\frac{\partial}{\partial x^{\alpha}} = \frac{\partial y^{\mu}}{\partial x^{\alpha}} \frac{\partial}{\partial y^{\mu}} = M_{\alpha}^{\ \mu} \frac{\partial}{\partial y^{\mu}}$ . Therefore,

$$(3.0.26) A^{\alpha\beta} \frac{\partial}{\partial x^{\alpha}} \frac{\partial}{\partial x^{\beta}} u = A^{\alpha\beta} M_{\alpha}{}^{\mu} M_{\beta}{}^{\nu} \frac{\partial}{\partial y^{\mu}} \frac{\partial}{\partial y^{\nu}} u = I^{\mu\nu} \frac{\partial}{\partial y^{\mu}} \frac{\partial}{\partial y^{\nu}} u = \Delta_{y} u.$$

This completes the proof in the first case.

In the second case, in which n of the eigenvalues of A have the same (non-zero) sign, and the remaining one has the opposite (non-zero) sign, the proof is similar. The key difference is that because of the eigenvalue of opposite sign, (3.0.24) is replaced with

$$(3.0.27) M_{\alpha}^{\ \mu} A^{\alpha\beta} M_{\beta}^{\ \nu} = (m^{-1})^{\mu\nu},$$

where  $(m^{-1})^{\mu\nu} \stackrel{\text{def}}{=} \text{diag}(-1, 1, 1, \dots, 1)$  is the standard  $(1+n) \times (1+n)$  Minkowski matrix. Therefore,

$$(3.0.28) A^{\alpha\beta} \frac{\partial}{\partial x^{\alpha}} \frac{\partial}{\partial x^{\beta}} u = A^{\alpha\beta} M_{\alpha}^{\ \mu} M_{\beta}^{\ \nu} \frac{\partial}{\partial y^{\mu}} \frac{\partial}{\partial y^{\nu}} u = (m^{-1})^{\mu\nu} \frac{\partial}{\partial y^{\mu}} \frac{\partial}{\partial y^{\nu}} u = \Box_{y} u.$$

This completes the proof in the second case.

In the third case, in which n of the eigenvalues of A have the same (non-zero) sign, and the remaining one is 0, the proof is similar. The key difference is that because of the zero eigenvalue, (3.0.24) is replaced with

$$(3.0.29) M_{\alpha}{}^{\mu}A^{\alpha\beta}M_{\beta}{}^{\nu} = D^{\mu\nu},$$

where  $D^{\mu\nu} \stackrel{\text{def}}{=} \text{diag}(0, 1, 1, \dots, 1)$ .

Therefore,

$$(3.0.30) A^{\alpha\beta} \frac{\partial}{\partial x^{\alpha}} \frac{\partial}{\partial x^{\beta}} u = A^{\alpha\beta} M_{\alpha}{}^{\mu} M_{\beta}{}^{\nu} \frac{\partial}{\partial y^{\mu}} \frac{\partial}{\partial y^{\nu}} u = D^{\mu\nu} \frac{\partial}{\partial y^{\mu}} \frac{\partial}{\partial y^{\nu}} u = \sum_{i=1}^{n} \frac{\partial^{2}}{(\partial y^{i})^{2}} u.$$

Furthermore, we have that

$$(3.0.31) B^{\alpha} \frac{\partial}{\partial x^{\alpha}} u = M_{\alpha}{}^{\mu} B^{\alpha} \frac{\partial}{\partial u^{\mu}} u.$$

Thus, using using (3.0.25), we have that

$$\widetilde{B}^0 \stackrel{\text{def}}{=} M_{\alpha}^{\ 0} B^{\alpha} = v_{\alpha}^{(0)} B^{\alpha} \neq 0.$$

**Example 3.0.1.** In the first example from above,

$$(3.0.33) A^{\mu\nu} = \begin{bmatrix} 1 & -2 \\ -2 & 2 \end{bmatrix}.$$

To calculate the eigenvalues of A, we first set

(3.0.34) 
$$\det(A - \lambda I) = \det \begin{bmatrix} 1 - \lambda & -2 \\ -2 & 2 - \lambda \end{bmatrix} = \lambda^2 - 3\lambda - 2 = 0.$$

The solutions are

$$\lambda = \frac{3 \pm \sqrt{17}}{2}.$$

Since the eigenvalues are of opposite sign, the corresponding PDE is hyperbolic.

**Example 3.0.2.** In the second example from above,

(3.0.36) 
$$A^{\mu\nu} = \begin{bmatrix} -2 & -1 \\ -1 & -1 \end{bmatrix}.$$

To calculate the eigenvalues of A, we first set

(3.0.37) 
$$\det(A - \lambda I) = \det \begin{bmatrix} -2 - \lambda & -1 \\ -1 & -1 - \lambda \end{bmatrix} = \lambda^2 + 3\lambda + 1 = 0.$$

The solutions are

$$\lambda = \frac{-3 \pm \sqrt{5}}{2}.$$

Both of these eigenvalues are negative, and thus the corresponding PDE is elliptic.

**Example 3.0.3.** In the final example from above,

$$(3.0.39) A^{\mu\nu} = \begin{bmatrix} 1 & -1 \\ -1 & 1 \end{bmatrix}.$$

To calculate the eigenvalues of A, we first set

$$(3.0.40) \qquad \det(A - \lambda I) = \det \begin{bmatrix} 1 - \lambda & -1 \\ -1 & 1 - \lambda \end{bmatrix} = \lambda^2 + 2\lambda = 0.$$

The solutions are

$$(3.0.41) \lambda = 0, -2,$$

and so the corresponding PDE is parabolic.

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# MATH 18.152 COURSE NOTES - CLASS MEETING # 16

## 18.152 Introduction to PDEs, Fall 2011

Class Meeting # 16: The Fourier Transform on  $\mathbb{R}^n$ 

Professor: Jared Speck

### 1. Introduction to the Fourier Transform

Earlier in the course, we learned that periodic functions  $f \in L^2([-1,1])$  (of period 2) can be represented using a Fourier series:

(1.0.1) 
$$f(x) = \frac{a_0}{2} + \sum_{m=1}^{\infty} a_m \cos(m\pi x) + \sum_{m=1}^{\infty} b_m \sin(m\pi x).$$

The "=" sign above is interpreted in the sense of the convergence of the sequence of partial sums associated to the right-hand side in the  $L^2([-1,1])$  norm. The coefficients  $a_m$  and  $b_m$  represent the "amount of the frequency m" that the function f contains. These coefficients were related to f itself by

(1.0.2a) 
$$a_0 = \int_{-1}^1 f(x) \, dx,$$

(1.0.2b) 
$$a_m = \int_{-1}^1 f(x) \cos(m\pi x) \, dx, \qquad (m \ge 1),$$

(1.0.2c) 
$$b_m = \int_{-1}^{1} f(x) \sin(m\pi x) dx, \qquad (m \ge 1).$$

The Fourier transform is a "continuous" version of the formula (1.0.1) for functions defined on the whole space  $\mathbb{R}^n$ . Our goal is to write functions f defined on  $\mathbb{R}^n$  as a superposition of different frequencies. However, instead of discrete frequencies m, we will need to use "continuous frequencies"  $\xi$ .

**Definition 1.0.1** (Fourier Transform). Let  $f \in L^1(\mathbb{R}^n)$ , i.e.,  $\int_{\mathbb{R}^n} |f(x)| d^n x < \infty$ . The Fourier transform of f is denoted by  $\hat{f}$ , and it is a new function of the frequency variable  $\xi \in \mathbb{R}^n$ . It is defined for each frequency  $\xi$  as follows:

(1.0.3) 
$$\hat{f}(\xi) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} f(x)e^{-2\pi i \xi \cdot x} d^n x,$$

where  $\cdot$  denotes the Euclidean dot product, i.e., if  $x = (x^1, \dots, x^n)$  and  $\xi = (\xi^1, \dots, \xi^n)$ , then  $\xi \cdot x \stackrel{\text{def}}{=} \sum_{j=1}^n \xi^j x^j$ . In the above formula, recall that if is r is a real number, then  $e^{ir} = \sin r + i \cos r$ .

The formula (1.0.3) is analogous to the formulas (1.0.2a) - (1.0.2c). It provides the "amount of the frequency component"  $\xi$  that f contains. Later in the course, we will derive an analog of the representation formula (1.0.1).

Remark 1.0.1. The Fourier transform can be defined on a much larger class of functions than those that belong to  $L^1$ . However, to make rigorous sense of this fact requires advanced techniques that go beyond this course.

We will also use the following notation.

**Definition 1.0.2** (Inverse Fourier transform). Given a function  $f(\xi) \in L^1(\mathbb{R}^n)$ , its inverse Fourier transform, which is denoted by  $f^{\vee}$ , is a new function of x defined as follows:

(1.0.4) 
$$f^{\vee}(x) \stackrel{\text{def}}{=} \hat{f}(-x) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} f(x)e^{2\pi i\xi \cdot x} d^n \xi.$$

The name is motivated as follows: later in the course, we will show that  $(\hat{f})^{\vee} = f$ . Thus,  $\vee$  is in fact the inverse of the operator  $\wedge$ .

The Fourier transform is very useful in the study of certain PDEs. To use it in the context of PDEs, we will have to understand how the Fourier transform operator interacts with partial derivatives. In order to do this, it is convenient to introduce the following notation, which will simultaneously help us bookkeep when taking repeated derivatives, and when classifying the structure monomials.

## Definition 1.0.3. If

(1.0.5) 
$$\vec{\alpha} \stackrel{\text{def}}{=} (\alpha^1, \cdots, \alpha^n)$$

is an array of non-negative integers, then we define  $\partial_{\vec{\alpha}}$  to be the differential operator

$$\partial_{\vec{\alpha}} \stackrel{\text{def}}{=} \partial_1^{\alpha^1} \cdots \partial_n^{\alpha^n}.$$

Note that  $\partial_{\vec{\alpha}}$  is an operator of order  $|\vec{\alpha}| \stackrel{\text{def}}{=} \alpha^1 + \dots + \alpha^n$ . If  $x = (x^1, \dots, x^n)$  is an element of  $\mathbb{C}^n$ , then we also define  $x^{\vec{\alpha}}$  to be the monomial

$$(1.0.7) x^{\vec{\alpha}} \stackrel{\text{def}}{=} (x^1)^{\alpha^1} \cdots (x^n)^{\alpha^n}.$$

The following function spaces will play an important role in our study of the Fourier transform. Throughout this discussion, the functions f are allowed to be complex-valued.

## Definition 1.0.4 (Some important function spaces).

(1.0.8) 
$$C^{k} \stackrel{\text{def}}{=} \{ f : \mathbb{R}^{n} \to \mathbb{C} \mid \partial_{\vec{\alpha}} f \text{ is continuous for } |\vec{\alpha}| \le k \},$$

(1.0.9) 
$$C_0 \stackrel{\text{def}}{=} \{ f : \mathbb{R}^n \to \mathbb{C} \mid f \text{ is continuous and } \lim_{|x| \to \infty} f(x) = 0 \}.$$

We also recall the following norm on the space of bounded, continuous functions  $f: \mathbb{R}^n \to \mathbb{C}$ :

(1.0.10) 
$$||f||_{C_0} \stackrel{\text{def}}{=} \max_{x \in \mathbb{R}^n} |f(x)|.$$

The  $L^2$  norm plays an important role in Fourier analysis. Since  $\hat{f}$  is in general complex-valued we also need to extend the notion of the  $L^2$  inner product to complex-valued functions. This is accomplished in the next definition.

**Definition 1.0.5** (Inner product for complex-valued functions). Let f and g be complex-valued functions defined on  $\mathbb{R}^n$ . We define their complex inner product by

(1.0.11) 
$$\langle f, g \rangle \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} f(x)\bar{g}(x) d^n x,$$

where  $\bar{g}$  denotes the complex conjugate of g. That is, if g(x) = u(x) + iv(x), where u and v are real-valued, then  $\bar{g}(x) \stackrel{\text{def}}{=} u(x) - iv(x)$ .

We also define norm of f by

(1.0.12) 
$$||f|| \stackrel{\text{def}}{=} \langle f, f \rangle^{1/2} \stackrel{\text{def}}{=} \left( \int_{\mathbb{R}^n} |f(x)|^2 d^n x \right)^{1/2}.$$

Note that this is just the standard  $L^2$  norm extended to complex-valued functions.

Note that  $\langle \cdot, \cdot \rangle$  and  $\| \cdot \|$  verify all of the standard properties associated to a complex inner product and its norm:

- $||f|| \ge 0$  and ||f|| = 0 if and only if f = 0 almost everywhere
- $\langle g, f \rangle = \overline{\langle f, g \rangle}$  (Hermitian symmetry)
- If a and b are complex numbers, then  $\langle af + bg, h \rangle = a \langle f, h \rangle + b \langle g, h \rangle$ , and  $\langle f, ag \rangle = \bar{a} \langle f, g \rangle$  (Hermitian linearity)
- $|\langle f, g \rangle| \le ||f|| ||g||$  (Cauchy-Schwarz inequality)
- $||f + g|| \le ||f|| + ||g||$  (Triangle Inequality)

### 2. Properties of the Fourier Transform

The next lemma illustrates some basic properties of  $\hat{f}$  that hold whenever  $f \in L^1$ .

**Lemma 2.0.1** (Properties of  $\hat{f}$  for  $f \in L^1$ ). Suppose that  $f \in L^1(\mathbb{R}^n)$ . Then  $\hat{f}$  is a bounded, continuous function and

$$(2.0.13)$$

*Proof.* Since  $|e^{ir}|=1$  for all real numbers r, it follows that for each fixed  $\xi$ , we have

$$|\hat{f}(\xi)| \le \int_{\mathbb{R}^n} |f(x)e^{-2\pi i\xi \cdot x}| \, d^n x \le \int_{\mathbb{R}^n} |f(x)| \, d^n x \stackrel{\text{def}}{=} ||f||_{L^1}.$$

Taking the max over all  $\xi \in \mathbb{R}^n$ , the estimate (2.0.13) thus follows.

We now prove that  $\hat{f}$  is continuous. Given  $\epsilon > 0$ , let  $B_R$  be a ball of radius R centered at the origin such that the integral of |f| over its complement  $B_R^c$  is no larger than  $\epsilon$ :

$$(2.0.15) \qquad \int_{B_B^c} |f(x)| \, d^n x \le \epsilon.$$

It is possible to choose such a ball since  $f \in L^1$ . We then estimate

$$(2.0.16) |\hat{f}(\xi) - \hat{f}(\eta)| \leq \int_{B_R} |f(x)| |e^{-2\pi i \xi \cdot x} - e^{-2\pi i \eta \cdot x}| d^n x + \int_{B_R^c} |f(x)| |e^{-2\pi i \xi \cdot x} - e^{-2\pi i \eta \cdot x}| d^n x$$

$$\leq \int_{B_R} |f(x)| |e^{-2\pi i \xi \cdot x} - e^{-2\pi i \eta \cdot x}| d^n x + 2\epsilon.$$

Now since  $e^{-2\pi i r}$  is a uniformly continuous function of the real number r on any compact set, if  $|\xi - \eta|$  is sufficiently small, then we can ensure that  $\max_{x \in B_R} |e^{-2\pi i \xi \cdot x} - e^{-2\pi i \eta \cdot x}| \leq \epsilon$ . We then conclude that the final integral over  $B_R$  on the right-hand side of (2.0.16) will be no larger than

(2.0.17) 
$$\max_{x \in B_R} |e^{-2\pi i \xi \cdot x} - e^{-2\pi i \eta \cdot x}| \int_{B_R} |f(x)| \, d^n x \le \epsilon \int_{\mathbb{R}^n} |f(x)| \, d^n x \stackrel{\text{def}}{=} \epsilon ||f||_{L^1}.$$

Thus, in total, we have shown that if  $|\xi - \eta|$  is sufficiently small, then  $|\hat{f}(\xi) - \hat{f}(\eta)| \le \epsilon ||f||_{L^1} + 2\epsilon$ . Since such an estimate holds for all  $\epsilon > 0$ ,  $\hat{f}$  is continuous by definition.

It is helpful to introduce notation to indicate that a function has been translated.

**Definition 2.0.6** (Translation of a function). If  $\mathbb{R}^n \to \mathbb{C}$  is a function and  $y \in \mathbb{R}^n$  is any point, then we define the translated function  $\tau_y f$  by

(2.0.18) 
$$\tau_y f(x) \stackrel{\text{def}}{=} f(x - y).$$

The next theorem collects together some very important properties of the Fourier transform. In particular, it illustrates how the Fourier transform interacts with translations, derivatives, multiplication by polynomials, products, convolutions, and complex conjugates.

Theorem 2.1 (Important properties of the Fourier transform). Assume that  $f, g \in L^1(\mathbb{R}^n)$ , and let  $t \in \mathbb{R}$ . Then

$$(2.0.19a)$$

$$(\tau_{y}f)^{\wedge}(\xi) = e^{-2\pi i \xi \cdot y} \hat{f}(\xi),$$

$$(2.0.19b)$$

$$\hat{h}(\xi) = \tau_{\eta} \hat{f}(\xi) \qquad if \ h(x) \stackrel{def}{=} e^{2\pi i \eta \cdot x} f(x),$$

$$(2.0.19c)$$

$$\hat{h}(\xi) = t^{n} \hat{f}(t\xi) \qquad if \ h(x) \stackrel{def}{=} f(t^{-1}x),$$

$$(2.0.19d)$$

$$(f * g)^{\wedge}(\xi) = \hat{f}(\xi) \hat{g}(\xi),$$

$$(2.0.19e)$$

$$If \ x^{\vec{\alpha}} f \in L^{1} for \ |\vec{\alpha}| \leq k, \ then \ \hat{f} \in C^{k} \ and \ \partial_{\vec{\alpha}} \hat{f}(\xi) = [(-2\pi i x)^{\vec{\alpha}} f(x)]^{\wedge}(\xi),$$

$$(2.0.19f)$$

$$If \ f \in C^{k}, \ \partial_{\vec{\alpha}} f \in L^{1} \ for \ |\vec{\alpha}| \leq k, \ and \ \partial_{\vec{\alpha}} f \in C_{0} \ for \ |\vec{\alpha}| \leq k - 1, \ then \ (\partial_{\vec{\alpha}} f)^{\wedge}(\xi) = (2\pi i \xi)^{\vec{\alpha}} \hat{f}(\xi),$$

$$(2.0.19g)$$

$$\hat{f}(\xi) = (\bar{f})^{\vee}(\xi) \ and \ (\bar{f}^{\vee})(\xi) = (\bar{f})^{\wedge}(\xi).$$

Above,  $\bar{f}$  denotes the complex conjugate of f; i.e., if f = u + iv, where u and v are real-valued, then f = u - iv.

*Proof.* To prove (2.0.19a), we make the change of variables z = x - y,  $d^n z = d^n x$  and calculate that

(2.0.20)

$$(\tau_y f)^{\wedge}(\xi) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} f(x-y) e^{-2\pi i x \cdot \xi} d^n x = \int_{\mathbb{R}^n} f(z) e^{-2\pi i (z+y) \cdot \xi} d^n z = e^{-2\pi i y \cdot \xi} \int_{\mathbb{R}^n} f(z) e^{-2\pi i z \cdot \xi} d^n z \stackrel{\text{def}}{=} e^{-2\pi i y \cdot \xi} \hat{f}(\xi).$$

To prove (2.0.19b), we calculate that

$$(2.0.21) \qquad \hat{h}(\xi) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} e^{2\pi i \eta \cdot x} f(x) e^{-2\pi i x \cdot \xi} d^n x = \int_{\mathbb{R}^n} f(x) e^{-2\pi i x \cdot (\xi - \eta)} d^n x \stackrel{\text{def}}{=} \hat{f}(\xi - \eta) \stackrel{\text{def}}{=} \tau_{\eta} \hat{f}(\xi).$$

To prove (2.0.19c), we make the change of variables  $y = t^{-1}x$ ,  $d^n y = t^{-n}d^n x$  to deduce that

(2.0.22) 
$$\hat{h}(\xi) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} f(t^{-1}x)e^{-2\pi i x \cdot \xi} d^n x$$

$$\int_{\mathbb{R}^n} f(y)e^{-2\pi i y \cdot t\xi} t^n d^n y$$

$$\stackrel{\text{def}}{=} t^n \hat{f}(t\xi).$$

To prove (2.0.19d), we use the definition of convolution, (2.0.19a), and Fubini's theorem to deduce that

$$(2.0.23)$$

$$(f * g)^{\wedge}(\xi) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} e^{-2\pi x \cdot \xi} \Big( \int_{\mathbb{R}^n} f(x - y) g(y) d^n y \Big) d^n x = \int_{\mathbb{R}^n} g(y) \underbrace{\left( \int_{\mathbb{R}^n} e^{-2\pi x \cdot \xi} f(x - y) d^n x \right)}_{e^{-2\pi i \xi \cdot y} \hat{f}(\xi)} d^n y$$

$$= \hat{f}(\xi) \int_{\mathbb{R}^n} e^{-2\pi i \xi \cdot y} g(y) d^n y \stackrel{\text{def}}{=} \hat{f}(\xi) \hat{g}(\xi).$$

To prove (2.0.19e), we differentiate under the integral in the definition of  $f(\xi)$  to deduce that

(2.0.24)

$$\partial_{\vec{\alpha}}^{(\xi)} \hat{f}(\xi) = \int_{\mathbb{R}^n} f(x) \partial_{\vec{\alpha}}^{(\xi)} e^{-2\pi i x \cdot \xi} d^n x = \int_{\mathbb{R}^n} f(x) (-2\pi i x)^{\vec{\alpha}} e^{-2\pi i x \cdot \xi} d^n x \stackrel{\text{def}}{=} [(-2\pi i x)^{\vec{\alpha}} f(x)]^{\hat{\alpha}} (\xi).$$

To prove (2.0.19f), we integrate by parts  $|\vec{\alpha}|$  times and use the hypotheses on f to discard the boundary terms at infinity, thus concluding that

$$(2.0.25) \qquad (\partial_{\vec{\alpha}} f)^{\hat{}}(\xi) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} \partial_{\vec{\alpha}} f(x) e^{-2\pi i x \cdot \xi} d^n x = \int_{\mathbb{R}^n} f(x) (-1)^{|\vec{\alpha}|} \partial_{\vec{\alpha}}^{(x)} e^{-2\pi i x \cdot \xi} d^n x$$
$$= \int_{\mathbb{R}^n} f(x) (2\pi i \xi)^{\vec{\alpha}} e^{-2\pi i x \cdot \xi} d^n x \stackrel{\text{def}}{=} (2\pi i \xi)^{\vec{\alpha}} \hat{f}(\xi).$$

To deduce the first relation in (2.0.19g), we compute that

$$(2.0.26)$$

$$\bar{\hat{f}}(\xi) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} f(x)e^{-2\pi ix\cdot\xi} d^n x = \int_{\mathbb{R}^n} \bar{f}(x)\overline{e^{-2\pi ix\cdot\xi}} d^n x = \int_{\mathbb{R}^n} \bar{f}(x)e^{2\pi ix\cdot\xi} d^n x \stackrel{\text{def}}{=} \hat{f}(-\xi) \stackrel{\text{def}}{=} (\bar{f})^{\vee}(\xi).$$

The second relation in (2.0.19g) can be shown using similar reasoning.

(2.0.19e) roughly shows that if f decays very rapidly at infinity, then  $\hat{f}$  is very differentiable. Similarly, (2.0.19f) roughly shows that if f is very differentiable with rapidly decaying derivatives, then  $\hat{f}$  also rapidly decays. The Fourier transform thus connects the decay properties of f to the differentiability properties of  $\hat{f}$ , and vice versa. In the next proposition, we provide a specific example of these phenomena. More precisely, the next proposition shows that the Fourier transform of a smooth, compactly supported function is itself smooth and rapidly decaying at infinity.

**Proposition 2.0.2.** Let  $f \in C_c^{\infty}(\mathbb{R}^n)$ , i.e., f is a smooth, compactly supported function. Then  $\hat{f}$  is smooth and "rapidly decaying at infinity" in the following sense: for each  $N \geq 0$ , there exists a constant  $C_N > 0$  such that

$$(2.0.27) |\hat{f}(\xi)| \le C_N (1 + |\xi|)^{-N}.$$

Furthermore, an estimate similar to (2.0.27) holds (with possibly different constants) for all of the derivatives  $|\partial_{\vec{\beta}}\hat{f}(\xi)|$ .

In particular,  $\hat{f} \in L^1$ :

(2.0.28) 
$$\|\hat{f}(\xi)\|_{L^{1}} \stackrel{def}{=} \int_{\mathbb{R}^{n}} |\hat{f}(\xi)| d^{n}\xi < \infty,$$

and similarly for  $\partial_{\vec{\beta}}\hat{f}$ , where  $\vec{\beta}$  is any derivative multi-index.

*Proof.* Using (2.0.19e) and the fact that f is compactly supported (and hence  $x^{\vec{\alpha}} f \in L^1$ ), we see that  $\hat{f}$  is smooth.

To prove (2.0.27), we use (2.0.19f), (2.0.13), and the fact that  $\|\partial_{\vec{\alpha}} f\|_{L^1} < \infty$  for any differential operator  $\partial_{\vec{\alpha}}$  to deduce that

$$|(2.0.29) |(2\pi i \xi)^{\vec{\alpha}} \hat{f}(\xi)| = |(\partial_{\vec{\alpha}} f)^{\hat{}}(\xi)| \le ||\partial_{\vec{\alpha}} f||_{L^{1}} = C_{\vec{\alpha}},$$

where  $C_{\vec{\alpha}}$  is a constant depending on  $\vec{\alpha}$ . In particular, if  $M \geq 0$  is an integer, then by applying (2.0.29) to the differential operator  $\Delta^M \stackrel{\text{def}}{=} (\sum_{i=1}^n \partial_i^2)^M \left(\text{i.e., } \left|(2\pi i)^{2M} \left(\sum_{i=1}^n (\xi^i)^2\right)^M \hat{f}(\xi)\right| = \sum_{|\xi| \geq M} |\xi|^{2M}$ 

$$|(\Delta^M f)^{\wedge}(\xi)| \leq C_M$$
), it follows that

$$(2.0.30) (2\pi|\xi|)^{2M}|\hat{f}(\xi)| \le C_M$$

for some constant  $C_M > 0$ . It is easy to see that an estimate of the form (2.0.27) follows from (2.0.30).

(2.0.28) follows from (2.0.27) and the fact that

(2.0.31) 
$$\int_{\mathbb{R}^n} \frac{1}{(1+|\xi|)^{n+1}} d^n \xi < \infty.$$

To see that (2.0.31) holds, perform the integration using spherical coordinates on  $\mathbb{R}^n$ :

(2.0.32) 
$$\int_{\mathbb{R}^n} \frac{1}{(1+|\xi|)^{n+1}} d^n \xi = \omega_n \int_{\rho=0}^{\infty} \frac{\rho^{n-1}}{(1+\rho)^{n+1}} d\rho,$$

where  $\rho \stackrel{\text{def}}{=} |\xi| \stackrel{\text{def}}{=} \sqrt{\sum_{j=1}^{n} (\xi^{j})^{2}}$  is the radial variable on  $\mathbb{R}^{n}$ , and  $\omega_{n}$  is the surface area of the unit ball in  $\mathbb{R}^{n}$ . By a simple comparison estimate, it is easy to see that the integral on the right-hand side of (2.0.32) converges (the integrand behaves like 0 near  $\rho = 0$ , and like  $\frac{1}{\rho^{2}}$  near  $\infty$ ).

To show that similar results hold for for  $\partial_{\vec{\beta}}\hat{f}$ , we first use (2.0.19e) to conclude that

(2.0.33) 
$$\partial_{\vec{\beta}} \hat{f}(\xi) = [(-2\pi i x)^{\vec{\beta}} f(x)]^{\hat{}}(\xi).$$

Furthermore, the function  $(-2\pi ix)^{\vec{\beta}}f(x)$  also satisfies the hypotheses of the proposition. We can therefore repeat the above arguments with  $\partial_{\vec{\beta}}\hat{f}$  in place of  $\hat{f}$  and  $(-2\pi ix)^{\vec{\beta}}f(x)$  in place of f.

#### 3. Gaussians

One of the most important classes of functions in Fourier theory is the class of Gaussians. The next proposition shows that this class interacts very nicely with the Fourier transform.

Proposition 3.0.3 (The Fourier transform of a Gaussian is another Gaussian). Let  $f(x) = exp(-\pi z|x|^2)$ , where z = a + ib is a complex number,  $a, b \in \mathbb{R}$ , a > 0,  $x = (x^1, \dots, x^n) \in \mathbb{R}^n$ , and  $|x|^2 = \sum_{j=1}^n (x^j)^2$ . Then

$$\hat{f}(\xi) = z^{-n/2} exp(-\pi |\xi|^2 / z).$$

*Proof.* We consider only the case b = 0, so that z = a. The cases  $b \neq 0$  would follow from an argument similar to the one we give below but requiring a few additional technical details. We first address the case n = 1. Then by properties (2.0.19e)-(2.0.19f) of Theorem 2.1, we have that

$$(3.0.35) \hat{f}'(\xi) = (-2\pi i x e^{-a\pi x^2})^{\wedge}(\xi) = \frac{i}{a} (\frac{d}{dx} e^{-a\pi x^2})^{\wedge}(\xi) = \frac{i}{a} 2\pi i \xi \hat{f}(\xi) = \frac{-2\pi}{a} \xi \hat{f}(\xi).$$

We can view (3.0.35) as

$$\frac{d}{d\xi}\ln\hat{f} = \frac{-2\pi}{a}\xi.$$

Integrating (3.0.36) with respect to  $\xi$  and then exponentiating both sides, we conclude that

(3.0.37) 
$$\hat{f}(\xi) = C\exp(-\pi \xi^2 / a.)$$

Furthermore, the constant C clearly must be equal to  $\hat{f}(0)$ .

We now compute  $\hat{f}(0)$ :

(3.0.38) 
$$\hat{f}(0) \stackrel{\text{def}}{=} \int_{\mathbb{R}} e^{-\pi ax^2} \underbrace{e^{-2\pi i\xi 0}}^{1} dx = a^{-1/2}.$$

Note that you have previously calculated this integral in your homework. Combining (3.0.36) and (3.0.38), we arrive at the desired expression (3.0.34) in the case n = 1.

To treat the case of general n, we note that the properties of the exponential function and the Fubini theorem together allow us to reduce it to the case of n = 1:

(3.0.39) 
$$\hat{f}(\xi) = \int_{\mathbb{R}^n} \exp(-\pi a|x|^2) \exp(-2\pi i \xi \cdot x) d^n x$$

$$= \int_{\mathbb{R}^n} \exp\left(-\pi a \sum_{k=1}^n (x^k)^2\right) \exp\left(-2\pi i \sum_{j=1}^n \xi^j x^j\right) d^n x$$

$$= \int_{\mathbb{R}^n} \prod_{j=1}^n \left\{ \exp\left(-\pi a (x^j)^2\right) \exp(-2\pi i \xi^j x^j) \right\} d^n x$$

$$= \prod_{j=1}^n \left\{ \int_{\mathbb{R}} \exp\left(-\pi a (x^j)^2\right) \exp(-2\pi i \xi^j x^j) dx^j \right\}$$

$$= \prod_{j=1}^n a^{-1/2} \exp\left(-\pi (\xi^j)^2 / a\right)$$

$$= a^{-n/2} \exp\left(-\pi a^{-1} \sum_{j=1}^n (\xi^j)^2\right)$$

$$= a^{-n/2} \exp(-\pi |\xi|^2 / a).$$

We have thus shown (3.0.34).

#### 4. Fourier Inversion and the Plancherel Theorem

The next lemma is very important. It shows that the Fourier transform interacts nicely with the  $L^2$  inner product.

Lemma 4.0.4 (Interaction of the Fourier transform with the  $L^2$  inner product). Assume that  $f, g \in L^1$ . Then

(4.0.40) 
$$\int_{\mathbb{P}^n} \hat{f}(x)g(x) \, d^n x = \int_{\mathbb{P}^n} f(x)\hat{g}(x) \, d^n x.$$

Alternatively, in terms of the complex  $L^2$  inner product, we have that

$$(4.0.41) \qquad \langle \hat{f}, q \rangle = \langle f, q^{\vee} \rangle.$$

*Proof.* Using the definition of the Fourier transform and Fubini's theorem, the left-hand side of (4.0.40) is equal to

$$(4.0.42) \qquad \int_{\mathbb{R}^n} \int_{\mathbb{R}^n} f(\xi)g(x)e^{-2\pi i\xi \cdot x} d^n \xi d^n x.$$

By the same reasoning, this is also equal to the right-hand side of (4.0.40).

To obtain (4.0.41), simply replace g with  $\bar{g}$  in the identity (4.0.40) and use property (2.0.19g).

The next theorem is central to Fourier analysis. It shows that the operators  $\wedge$  and  $\vee$  are inverses of each other whenever f and  $\hat{f}$  are nice functions.

**Theorem 4.1** (Fourier inversion theorem). Suppose that  $f : \mathbb{R}^n \to \mathbb{C}$  is a continuous function, that  $f \in L^1$ , and that  $\hat{f} \in L^1$ . Then

$$(4.0.43) (\hat{f})^{\vee} = (f^{\vee})^{\wedge} = f.$$

That is, the operators  $\land$  and  $\lor$  are inverses of each other.

*Proof.* We first note that

$$(4.0.44) \qquad (\hat{f})^{\vee}(x) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} \left\{ \int_{\mathbb{R}^n} f(y) e^{-2\pi i y \cdot \xi} d^n y \right\} e^{2\pi i x \cdot \xi} d^n \xi.$$

Note that the integral in (4.0.44) is not absolutely convergent when viewed as a function of  $(y, \xi) \in \mathbb{R}^n \times \mathbb{R}^n$ . Thus, our proof of (4.0.43) will involve a slightly delicate limiting procedure that makes use of the auxiliary function

(4.0.45) 
$$\phi(t,\xi) \stackrel{\text{def}}{=} \exp(-\pi t^2 |\xi|^2 + 2\pi i \xi \cdot x).$$

Note that (2.0.19b) and Proposition 3.0.3 together imply that

(4.0.46) 
$$\hat{\phi}(y) = t^{-n} \exp(-\pi |x - y|^2 / t^2) \stackrel{\text{def}}{=} \Gamma(t, x - y),$$

where

(4.0.47) 
$$\Gamma(t;y) \stackrel{\text{def}}{=} t^{-n} \exp(-\pi |y|^2 / t^2).$$

Also note that  $\Gamma(t,y)$  is just the fundamental solution of the heat equation with diffusion constant  $D = \frac{1}{4\pi}$ . In particular, we previously showed in our study of the heat equation that

$$(4.0.48) \qquad \qquad \int_{\mathbb{R}^n} \Gamma(t, y) \, d^n y = 1$$

for all t > 0. We now compute that

$$(4.0.49) \qquad (\Gamma(t,\cdot)*f)(x) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} \Gamma(t,x-y)f(y) d^n y$$

$$= \int_{\mathbb{R}^n} \hat{\phi}(t,y)f(y) d^n y$$

$$= \int_{\mathbb{R}^n} \phi(t,\xi)\hat{f}(\xi) d^n \xi$$

$$= \int_{\mathbb{R}^n} \exp(-\pi t^2 |\xi|^2) \hat{f}(\xi) \exp(2\pi i \xi \cdot x) d^n \xi$$

During our study of the heat equation, we showed that the left-hand side of (4.0.49) converges to f(x) as  $t \downarrow 0$ . To complete the proof of the theorem, it remains to show that the right-hand side converges to

(4.0.50) 
$$\int_{\mathbb{R}^n} \hat{f}(\xi) \exp(2\pi i \xi \cdot x) \, d^n \xi \stackrel{\text{def}}{=} (\hat{f})^{\vee}(x) \stackrel{\text{def}}{=} (\hat{f})^{\wedge}(-x)$$

as  $t \downarrow 0$ . To this end, given any number  $\epsilon > 0$ , choose a ball  $B_R$  of radius R centered at the origin such that

$$(4.0.51) \qquad \int_{B_R^c} |\hat{f}(\xi)| \, d^n \xi \le \epsilon.$$

Above,  $B_R^c$  denotes the complement of the ball. It is possible to choose such a ball since  $\hat{f} \in L^1$ . We then estimate

$$\begin{aligned} &\left| \int_{\mathbb{R}^{n}} \exp(-\pi t^{2} |\xi|^{2}) \hat{f}(\xi) \exp(2\pi i \xi \cdot x) \, d^{n} \xi - \hat{f}^{\vee}(x) \right| \\ &\stackrel{\text{def}}{=} \left| \int_{\mathbb{R}^{n}} \exp(-\pi t^{2} |\xi|^{2}) \hat{f}(\xi) \exp(2\pi i \xi \cdot x) \, d^{n} \xi - \int_{\mathbb{R}^{n}} \hat{f}(\xi) \exp(2\pi i \xi \cdot x) \, d^{n} \xi \right| \\ &\leq \int_{\mathbb{R}^{n}} \left| \exp(-\pi t^{2} |\xi|^{2}) - 1 \right| |\hat{f}(\xi)| \, d^{n} \xi \\ &\leq \max_{\xi \in B_{R}} \left| \exp(-\pi t^{2} |\xi|^{2}) - 1 \right| \int_{B_{R}} |\hat{f}(\xi)| \, d^{n} \xi + \int_{B_{R}^{c}} |\exp(-\pi t^{2} |\xi|^{2}) - 1 ||\hat{f}(\xi)| \, d^{n} \xi \\ &\leq \max_{\xi \in B_{R}} \left| \exp(-\pi t^{2} |\xi|^{2}) - 1 \right| ||\hat{f}||_{L^{1}} + \int_{B_{R}^{c}} |\hat{f}(\xi)| \, d^{n} \xi \\ &\leq \max_{\xi \in B_{R}} \left| \exp(-\pi t^{2} |\xi|^{2}) - 1 \right| ||\hat{f}||_{L^{1}} + \epsilon. \end{aligned}$$

As  $t \downarrow 0$ , the first term on the right-hand side of (4.0.52) converges to 0. In particular, if t is sufficiently small, then the right-hand side of (4.0.52) will be no larger than  $2\epsilon$ . Since this holds for any  $\epsilon > 0$ , we have thus shown that the right-hand side of (4.0.49) converges to the expression (4.0.50) as  $t \downarrow 0$ , i.e., that it converges to  $(\hat{f})^{\vee}(x)$ . Since, as we have previously noted, the left-hand side of (4.0.49) converges to f(x) as  $t \downarrow 0$ , we have thus shown that  $(\hat{f})^{\vee}(x) = f(x)$ .

It can similarly be shown that  $(f^{\vee})^{\wedge}(x) = f(x)$ . This completes the proof of (4.0.43).

The next theorem plays a central role in many areas of PDE and analysis. It shows that the Fourier transform preserves the  $L^2$  norm of functions.

**Theorem 4.2** (The Plancherel theorem). Suppose that  $f, g : \mathbb{R}^n \to \mathbb{C}$  are continuous functions, that  $f, g \in L^1 \cap L^2$ , and that  $\hat{f}, \hat{g} \in L^1$ . Then  $\hat{f}, \hat{g} \in L^2$ , and

$$(4.0.53) \qquad \langle f, g \rangle = \langle \hat{f}, \hat{g} \rangle,$$

i.e., the Fourier transform preserves the  $L^2$  inner product. In particular, by setting f=g, it follows from (4.0.53) that

$$(4.0.54) ||f||_{L^2} = ||\hat{f}||_{L^2}.$$

*Proof.* By applying (4.0.41) with g replaced by  $\hat{g}$ , we have that

$$\langle \hat{f}, \hat{g} \rangle = \langle f, (\hat{g})^{\vee} \rangle.$$

By the Fourier inversion theorem (i.e. Theorem 4.1), we have that  $(\hat{g})^{\vee} = g$ , and so the right-hand side of (4.0.55) is equal to

$$(4.0.56) \langle f, g \rangle.$$

We have thus shown (4.0.53).

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## MATH 18.152 COURSE NOTES - CLASS MEETING # 19

## 18.152 Introduction to PDEs, Fall 2011

Class Meeting # 19: Schrödinger's Equation

Professor: Jared Speck

## 1. Introduction

Schrödinger's equation is the fundamental PDE of quantum mechanics. In the case of a single quantum particle, the unknown function is the wave function  $\psi(t,x)$ , which is a map from  $\mathbb{R}^{1+n}$  into the complex numbers:

$$\psi: \mathbb{R}^{1+n} \to \mathbb{C}$$
.

Above and throughout these notes, t is the time coordinate, and  $x=(x^1,\cdots,x^n)$  are the spatial coordinates. Schrödinger's equation is

(1.0.1) 
$$i\partial_t \psi(t,x) + \frac{1}{2} \Delta \psi(t,x) = V(t,x)\psi(t,x),$$

where  $\Delta = \sum_{i=1}^{n} \partial_i^2$  is the usual Laplacian with respect to the spatial variables, and V(t,x) is the potential, which models the interaction of the particle with its environment. In this course, we will mainly consider the case of free particles, in which V=0 (i.e., the homogeneous Schrödinger equation). In the case of free particles, there is an important family of solutions to (1.0.1), namely the free waves. The free wave solutions provide some important intuition about how solutions to the homogeneous Schrödinger equation behave. To derive the free wave solutions, we first make the assumption that

(1.0.2) 
$$\psi(t,x) = e^{i(\omega t - \xi \cdot x)},$$

where  $\cdot$  is the Euclidean dot product. Above,  $\omega \in \mathbb{R}$  is the *frequency*, and  $\xi \in \mathbb{R}^n$  is the *wave vector*. Note that (1.0.2) can be written as  $e^{i|\xi|(\frac{\omega}{|\xi|}t-\frac{\xi}{|\xi|}\cdot x)}$ , where  $|\xi|$  is the Euclidean length of  $\xi$ . Since  $\frac{\xi}{|\xi|}$  is a unit vector in  $\mathbb{R}^n$ , it therefore follows that the *speed* of the plane wave is

$$\frac{\omega}{|\xi|}$$

Plugging (1.0.2) into (1.0.1), we derive the algebraic relation

(1.0.4) 
$$-(\omega + \frac{|\xi|^2}{2})e^{i(\omega t + \xi \cdot x)} = 0,$$

which implies

$$(1.0.5) \qquad \qquad \omega = -\frac{|\xi|^2}{2},$$

$$\frac{\omega}{|\xi|} = -\frac{|\xi|}{2}.$$

These conditions are necessary and sufficient in order for the function given in (1.0.2) to solve (1.0.1) when V = 0. Note in particular that (1.0.6) shows that the speed of the plane wave solution depends on  $|\xi|$ , and in particular that larger  $|\xi|'s$  lead to larger speeds. The dependence of the speed of the plane wave on  $\xi$  is known as dispersion, and (1.0.5) is known as the dispersion relation of Schrödinger's equation.

Dispersion plays a very important role in the analysis of certain PDEs, and in particular Schrödinger's equation. Heuristically, one sometimes imagines that a "typical" solution to a dispersive PDE is composed of many free waves, each moving at a different speed and/or spatial direction (at least when the dispersion relation is non-trivial). The dispersive nature of the PDE suggests that the different free wave components in the solution should separate from each other. As we will see (see e.g. Theorem 2.1), this heuristic argument is sometimes rigorously borne out, and separation can cause the overall amplitude of the solution to decay in time (frequently at a rate of t to some negative power).

## 2. The Fundamental Solution

We are now going to study the following global Cauchy problem for Schrödinger's equation:

(2.0.7a) 
$$i\partial_t \psi(t, x) + \frac{1}{2} \Delta \psi(t, x) = 0,$$
 (2.0.7b) 
$$\psi(0, x) = \phi(x).$$

Let's start by momentarily forgetting about the initial data and instead trying to find the fundamental solution K(t,x) to equation (2.0.7a). We will precisely define the fundamental solution below; it is analogous to the fundamental solution for the heat equation. As we will see, the techniques from Fourier analysis that we have previously developed will allow us to derive the fundamental solution with relative ease. To this end, we set  $\psi(t,x) = K(t,x)$ , take the spatial Fourier of equation (2.0.7a), and use the Fourier transform property  $(\partial_{\vec{\alpha}}K)^{\wedge}(t,\xi) = (2\pi i \xi)^{\vec{\alpha}}\hat{K}(t,\xi)$  (and in particular  $(\Delta K)^{\wedge}(t,\xi) = -4\pi^2|\xi|^2\hat{K}(t,\xi)$ ) to deduce the following ODE for  $\hat{K}(t,\xi)$ :

(2.0.8) 
$$i\partial_t \hat{K}(t,\xi) - 2\pi^2 |\xi|^2 \hat{K}(t,\xi) = 0.$$

We rewrite (2.0.8) as

(2.0.9) 
$$\partial_t \ln \hat{K}(t,\xi) = -2\pi^2 i|\xi|^2,$$

which can be easily integrated to give

$$\hat{K}(t,\xi) = Ce^{-2\pi^2 it|\xi|^2},$$

where  $C(\xi)$  is a constant that we have to calculate.

To calculate  $C(\xi)$ , we recall that we are ultimately trying to solve the following initial value problem for Schrödinger's equation:

(2.0.11a) 
$$i\partial_t \psi(t, x) + \frac{1}{2} \Delta \psi(t, x) = 0,$$
 (2.0.11b) 
$$\psi(0, x) = \phi(x).$$

Since K(t, x) is supposed to be the fundamental solution, we would like (in analogy with the results of our study of the heat equation) the solution to (2.0.11a) - (2.0.11b) to be of the form

(2.0.12) 
$$\psi(t, x) = (K(t, \cdot) * \phi(\cdot))(x).$$

Formally taking the Fourier transform of (2.0.12), using the fact that the Fourier transform turns convolutions into products, and using (2.0.10), we arrive at the formal relation

(2.0.13) 
$$\hat{\psi}(t,\xi) = \hat{K}(t,\xi)\hat{\phi}(\xi) = C(\xi)e^{-2\pi^2it|\xi|^2}\hat{\phi}(\xi).$$

Since (2.0.13) must in particular hold at t = 0, it is easy to see that

$$(2.0.14) C(\xi) = 1.$$

Thus, the spatial Fourier transform of K can be expressed as

$$\hat{K}(t,\xi) = e^{-2\pi^2 it|\xi|^2}.$$

In the next proposition, we make rigorous sense of the above formal calculations, and we calculate K(t,x) from  $\hat{K}(t,\xi)$ .

Proposition 2.0.1 (Calculation of the Fundamental Solution K(t,x) for Schrödinger's equation). Let  $\phi(x)$  be a smooth compactly supported function, and let  $\psi(t,x)$  be the function whose spatial Fourier transform is defined as in (2.0.13):

(2.0.16) 
$$\hat{\psi}(t,\xi) = \hat{K}(t,\xi)\hat{\phi}(\xi),$$

where  $\hat{K}(t,\xi)$  is defined in (2.0.15). Then if t>0, we have that

(2.0.17) 
$$\psi(t,x) = (K(t,\cdot) * \phi)(x) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} K(t,y)\phi(x-y) \, d^n y = \int_{\mathbb{R}^n} K(t,x-y)\phi(y) \, d^n y,$$

where

(2.0.18) 
$$K(t,x) = \frac{1}{(2\pi i t)^{n/2}} e^{i\frac{|x|^2}{2t}}.$$

Above, 
$$i^{1/2} = e^{i\pi/4} = \frac{1}{\sqrt{2}}(1+i)$$
.

**Remark 2.0.1.** We refer to  $\hat{K}(t,\xi)$  as the Fourier transform of K(t,x), and K(t,x) as the inverse Fourier transform of  $\hat{K}(t,\xi)$ .

**Remark 2.0.2.** Note that  $K(t,\cdot)$  is not an element of  $L^1$  because  $\int_{\mathbb{R}} |K(t,x)| d^n x = \infty$ . Since many of our previous results for the Fourier transform used the assumption that  $K(t,\cdot) \in L^1$ , our analysis of K(t,x) is more delicate than these results.

*Proof.* For simplicity, let's consider only the case n=1. Previously, we showed that since  $\phi$  is smooth and compactly supported,  $\hat{\phi}$  is smooth, is rapidly decaying at infinity, and is an element of  $L^1$ . Therefore, the same is true of the function  $\hat{\psi}(\xi) = e^{-2\pi^2 it|\xi|^2} \hat{\phi}(\xi)$ . Thus, by the Fourier inversion theorem,  $\psi(t,x)$  is the inverse Fourier transform of  $\hat{\psi}(t,\xi)$ :

(2.0.19) 
$$\psi(t,x) = (\hat{\psi})^{\vee}(t,x) \stackrel{\text{def}}{=} \int_{\mathbb{R}} e^{2\pi i \xi x} \hat{\psi}(t,\xi) \, d\xi = \int_{\mathbb{R}} e^{2\pi i \xi x} e^{-2\pi^2 i t |\xi|^2} \hat{\phi}(\xi) \, d\xi.$$

To complete the proof, we will use that fact that the aforementioned properties of  $\hat{\phi}$  together with the expression (2.0.19) allow us to express

(2.0.20) 
$$\psi(t,x) = \lim_{\delta \to 0^+} \int_{\mathbb{R}} e^{2\pi i \xi x} e^{-2\pi^2 (\delta + i)t|\xi|^2} \hat{\phi}(\xi) dx.$$

We will show (2.0.20) at the end of the proof; let us take it for granted at the moment. Defining

$$f_{\delta;t}(\xi) \stackrel{\text{def}}{=} e^{-2\pi^2(\delta+i)t|\xi|^2},$$

we see that (2.0.20) is by definition equivalent to

(2.0.22) 
$$\psi(t,x) = \lim_{\delta \to 0^+} (f_{\delta;t}\hat{\phi})^{\vee}(x).$$

Note that  $f_{\delta;t}$  is a Gaussian whose argument has *negative* real part. Thus, we have previously calculated its inverse Fourier transform:

(2.0.23) 
$$f_{\delta;t}^{\vee}(x) = \frac{1}{\sqrt{2\pi(\delta+i)t}} e^{-|x|^2/(2t(\delta+i))}.$$

Furthermore, it is easy to see that

(2.0.24) 
$$\lim_{\delta \to 0^+} f_{\delta;t}^{\vee}(x) = \frac{1}{\sqrt{2\pi i t}} e^{i|x|^2/(2t)}.$$

We note that in the formula (2.0.24),  $\sqrt{i} = e^{i\pi/4} = \frac{1}{\sqrt{2}}(1+i)$ .

Using (2.0.22), the Fourier transform + Fourier inversion identity  $(uv)^{\vee} = [u^{\vee} * v^{\vee}]$ , and the Fourier inversion theorem  $(\hat{\phi})^{\vee} = \phi$ , we have that

(2.0.25) 
$$\psi(t,x) = \lim_{\delta \to 0^+} [f_{\delta;t}^{\vee} * \phi](x) \stackrel{\text{def}}{=} \lim_{\delta \to 0^+} \int_{\mathbb{R}} f_{\delta;t}^{\vee}(x-y)\phi(y) \ dy$$
$$= \int_{\mathbb{R}} \lim_{\delta \to 0^+} f_{\delta;t}^{\vee}(x-y)\phi(y) \ dy$$
$$= \frac{1}{\sqrt{2\pi i t}} \int_{\mathbb{R}} e^{i|x-y|^2/(2t)}\phi(y) \ dy.$$

We are allowed to bring the limit inside the integral in (2.0.25) because  $\phi(y)$  is smooth and compactly supported and because (for each fixed t > 0) the limit (2.0.24) is achieved *uniformly* on compact spatial sets. We have thus shown (2.0.17).

It remains to prove (2.0.20). We need to show that

(2.0.26) 
$$\left| \int_{\mathbb{R}} e^{2\pi i \xi x} e^{-2\pi^2 i t |\xi|^2} \left( e^{-2\pi^2 \delta t |\xi|^2} - 1 \right) \hat{\phi}(\xi) \, d\xi \right|$$

goes to 0 as  $\delta \downarrow 0$ . As we have previously discussed several times, the key to such an estimate is to split the integral over  $\mathbb{R}$  into an integral over a ball [-R, R] and its complement. More precisely, for any R > 0, the expression (2.0.26) can be bounded as follows:

$$(2.0.27) \leq \int_{[-R,R]} |e^{-2\pi^2 \delta t |\xi|^2} - 1||\hat{\phi}(\xi)| \, d\xi + \int_{\{|\xi| \geq R\}} \underbrace{|e^{-2\pi^2 \delta t |\xi|^2} - 1|}_{\leq 1} |\hat{\phi}(\xi)| \, d\xi$$

$$\leq \max_{\xi \in [-R,R]} |e^{-2\pi^2 \delta t |\xi|^2} - 1| \int_{[-R,R]} |\hat{\phi}(\xi)| \, dx + \int_{\{|\xi| \geq R\}} |\hat{\phi}(\xi)| \, d\xi$$

$$\stackrel{\text{def}}{=} I + II.$$

Let  $\epsilon > 0$  be a positive number. In our previous studies of the Fourier transform, we showed that (see also the remarks above)  $\int_{\mathbb{R}} |\hat{\phi}| d\xi \stackrel{\text{def}}{=} ||\hat{\phi}||_{L^1} < \infty$ . Now by Taylor expanding, we see that the following inequality holds whenever R > 0,  $\xi \in [-R, R]$ , and  $\delta t R^2$  is sufficiently small:

$$(2.0.28) |e^{-2\pi^2 \delta t |\xi|^2} - 1| \le C\delta t R^2,$$

where C is a positive constant. Thus, we have the following estimate, valid whenever  $\delta t R^2$  is sufficiently small:

(2.0.29) 
$$|I| \le C\delta t R^2 \int_{[-R,R]} |\hat{\phi}(\xi)| \, dx \le C\epsilon t R^2 ||\hat{\phi}||_{L^1}.$$

Furthermore, since  $\|\hat{\phi}\|_{L^1} < \infty$ , if R is sufficiently large, then

$$(2.0.30) |II| \le \epsilon.$$

Thus, if t is fixed, R is first chosen to be sufficiently large, and then  $\delta$  is chosen to be sufficiently small, we have that

$$(2.0.31) |I| + |II| \le C\delta t R^2 + \epsilon \le 2\epsilon.$$

In total, we have shown that if  $\delta$  is sufficiently small, then (2.0.26) is  $\leq 2\epsilon$ . Since this holds for any  $\epsilon > 0$ , we have thus shown (2.0.20).

We now formally define the fundamental solution.

Definition 2.0.1 (The Fundamental Solution to Schrödinger's equation). The fundamental solution associated to (1.0.1) is the function  $K(t,x) = \frac{1}{(2\pi i t)^{n/2}} e^{i\frac{|x|^2}{2t}}$  given in (2.0.18).

As an exercise, let's check that K(t,x) verifies Schrödinger equation.

Lemma 2.0.2 (K(t,x) verifies the free Schrödinger equation). For t > 0, K(t,x) is a solution to the free Schrödinger equation.

*Proof.* We use the chain rule to calculate

(2.0.32) 
$$\partial_j e^{i\frac{|x|^2}{2t}} = x^j \frac{i}{t} e^{i\frac{|x|^2}{2t}},$$

(2.0.33) 
$$\partial_j^2 e^{i\frac{|x|^2}{2t}} = \left(1 + \frac{i(x^j)^2}{t}\right) \frac{i}{t} e^{i\frac{|x|^2}{2t}},$$

(2.0.34) 
$$\frac{1}{2}\Delta K(t,x) = \frac{1}{(2\pi i t)^{n/2}} e^{i\frac{|x|^2}{2t}} \left(i\frac{n}{2t} - \frac{|x|^2}{2t^2}\right) e^{i\frac{|x|^2}{2t}},$$

(2.0.35) 
$$i\partial_t K(t,x) = \frac{i}{(2\pi i t)^{n/2}} e^{i\frac{|x|^2}{2t}} \left( -\frac{n}{2t} - \frac{i|x|^2}{2t^2} \right).$$

From the last two calculations, it easily follows that

$$(2.0.36) i\partial_t K(t,x) + \frac{1}{2}\Delta K(t,x) = 0.$$

We would like our fundamental solution to have the property that  $\lim_{t\to 0^+} \psi(t,x) = \phi(x)$  for nice functions  $\phi$ , where  $\psi(t,x) \stackrel{\text{def}}{=} [K(t,\cdot)*\phi(\cdot)](x)$ . Now using (2.0.13), if the initial datum  $\phi$  is smooth and compactly supported (and therefore, as previously shown,  $\hat{\phi}$  is smooth and rapidly decaying), it is not difficult to show that

(2.0.37) 
$$\lim_{t \downarrow 0} \|\hat{\psi}(t, \cdot) - \hat{\phi}\|_{L^2} = 0.$$

(2.0.13) shows that the transformed function  $\hat{\psi}(t,\cdot)$  converges to the transformed datum  $\hat{\phi}(\cdot)$  in the  $L^2$  norm as  $t \downarrow 0$ . But how does the function  $\psi(t,\cdot) \stackrel{\text{def}}{=} [K(t,\cdot) * \phi(\cdot)](x)$  behave as  $t \downarrow 0$ ? By (2.0.17), this is equivalent to studying the behavior of  $\frac{1}{(2\pi i t)^{n/2}} \int_{\mathbb{R}^n} e^{i\frac{|x-y|^2}{2t}} \phi(y) d^n y$  as  $t \downarrow 0$ . The next proposition briefly addresses this surprisingly difficult question.

**Proposition 2.0.3** (The behavior of  $K(t,\cdot) * \phi(\cdot)$  as  $t \downarrow 0$ ). Let  $\phi \in C_c^{\infty}(\mathbb{R}^n)$ . Then

(2.0.38) 
$$\lim_{t \to 0^+} \frac{1}{(2\pi i t)^{n/2}} \int_{\mathbb{R}^n} e^{i\frac{|x-y|^2}{2t}} \phi(y) d^n y = \phi(x).$$

*Proof.* The proof of this proposition requires a technically involved technique from Fourier Analysis known as the method of stationary phase; it is therefore slightly beyond the scope of this course. The main difficulty is that the most of the important behavior in (2.0.38) is due to the rapid oscillation in y of the integrand (except when y is near x!) as  $t \downarrow 0$ .

We are now ready to state and prove the main theorem concerning the solution to the free Schrödinger equation.

Theorem 2.1 (The Solution to the Global Cauchy Problem Schrödinger's Equation and the Dispersive Estimate). Let  $\phi(x) \in C_c^{\infty}(\mathbb{R}^n)$ . Then there exists a unique solution  $\psi \in C^{\infty}((0,\infty) \times \mathbb{R}^n)$  to the free Schrödinger equation

(2.0.39a) 
$$i\partial_t \psi(t, x) + \frac{1}{2} \Delta \psi(t, x) = 0, \qquad t > 0, x \in \mathbb{R}^n,$$
(2.0.39b) 
$$\psi(0, x) = \phi(x), \qquad x \in \mathbb{R}^n.$$

The solution can be expressed as

(2.0.40) 
$$\psi(t, x) = [K(t, \cdot) * \phi(\cdot)](x),$$

where K(t,x) is the fundamental solution defined in (2.0.18).

Furthermore, for each t > 0, the solution  $\psi(t, x)$  verifies the **dispersive estimate** 

$$(2.0.41)$$

Above, C > 0 is a constant that does not depend on the initial data.

*Proof.* Let  $\mathcal{L} \stackrel{\text{def}}{=} i\partial_t + \frac{1}{2}\Delta_x$  denote the free Schrödinger operator. By definition, we have that

$$[K(t,\cdot)*\phi(\cdot)](x) = \int_{\mathbb{R}^n} \phi(y) \frac{1}{(2\pi i t)^{n/2}} e^{i\frac{|x-y|^2}{2t}} d^n y.$$

According to our previously discussed differentiation-under-the-integral theorem (and making use of our assumptions on  $\phi(x)$ ), for t > 0, we can differentiate under the integral in (2.0.42) and use Lemma 2.0.2 to deduce that

(2.0.43) 
$$\mathcal{L}[K(t,\cdot) * \phi(\cdot)](x) = \int_{\mathbb{R}^n} \phi(y) \mathcal{L}\left\{\frac{1}{(2\pi i t)^{n/2}} e^{i\frac{|x-y|^2}{2t}}\right\} d^n y = 0.$$

Thus,  $\phi * K_t$  verifies Schrödinger's equation (2.0.39a).

The fact that  $\psi \in C^{\infty}((0,\infty) \times \mathbb{R}^n)$  follows from expressing

$$(2.0.44) [K(t,\cdot)*\phi(\cdot)](x) = \int_{\mathbb{R}^n} \phi(x-y) \frac{1}{(2\pi i t)^{n/2}} e^{i\frac{|y|^2}{2t}} d^n y.$$

and repeatedly differentiating with respect to x under the integral.

To prove (2.0.41), we note that the following simple pointwise inequality follows easily from (2.0.42):

$$(2.0.45) |[K(t,\cdot)*\phi(\cdot)](x)| \leq \left| \int_{\mathbb{R}^n} \phi(y) \frac{1}{(2\pi i t)^{n/2}} e^{i\frac{|x-y|^2}{2t}} d^n y \right|$$

$$\leq \frac{1}{(2\pi)^{n/2} t^{n/2}} \int_{\mathbb{R}^n} |\phi(y)| d^n y \stackrel{\text{def}}{=} \frac{1}{(2\pi)^{n/2} t^{n/2}} ||\phi||_{L^1}.$$

Taking the max over all  $x \in \mathbb{R}^n$ , the estimate (2.0.41) thus follows.

Let's now prove a very important property of sufficiently regular solutions to the free Schrödinger equation: their  $L^2$  norm is constant in time.

**Proposition 2.0.4** (Preservation of  $L^2$  norm). Under the assumptions of Theorem 2.1, we have that

(2.0.46) 
$$\|\psi(t,\cdot)\|_{L^{2}} = \underbrace{\|\phi\|_{L^{2}}}_{\|\phi\|_{L^{2}}}$$

where the  $L^2$  norm on the left-hand of (2.0.46) is taken over the spatial variables only. In particular, if  $\int_{\mathbb{R}^n} |\phi(x)|^2 d^n x = 1$ , then  $\int_{\mathbb{R}^n} |\psi(t,x)|^2 d^n x = 1$  holds for all  $t \geq 0$ .

*Proof.* We give two proofs, the first using the original solution, and the second using its Fourier transform; both proofs are important. For the first proof, we begin by noting that if

$$(2.0.47) i\partial_t \psi(t,x) + \frac{1}{2} \Delta \psi(t,x) = 0,$$

then by taking the complex conjugate of both sides, we have that

$$(2.0.48) -i\partial_t \bar{\psi}(t,x) + \frac{1}{2}\Delta \bar{\psi}(t,x) = 0,$$

where  $\bar{\psi}$  denotes the complex conjugate of  $\psi$ .

Differentiating under the integral in the definition of the  $L^2$  norm, recalling that  $|\psi|^2 = \psi \bar{\psi}$ , and using (2.0.47) - (2.0.48), we thus deduce that

$$(2.0.49) \quad \frac{d}{dt} \|\psi(t,\cdot)\|_{L^{2}}^{2} = \frac{d}{dt} \int_{\mathbb{R}^{n}} \psi(t,x) \bar{\psi}(t,x) d^{n}x = \int_{\mathbb{R}^{n}} \partial_{t} \psi(t,x) \bar{\psi}(t,x) + \psi(t,x) \partial_{t} \bar{\psi}(t,x) d^{n}x = \frac{i}{2} \int_{\mathbb{R}^{n}} \Delta \psi(t,x) \bar{\psi}(t,x) - \psi(t,x) \Delta \bar{\psi}(t,x) d^{n}x.$$

Integrating by parts on the right-hand side of (2.0.49), we conclude that

(2.0.50) 
$$\frac{d}{dt} \|\psi(t,\cdot)\|_{L^{2}}^{2} = -\frac{i}{2} \int_{\mathbb{D}^{n}} \nabla \psi(t,x) \cdot \nabla \bar{\psi}(t,x) - \nabla \psi(t,x) \cdot \nabla \bar{\psi}(t,x) d^{n}x = 0,$$

where  $\cdot$  denotes the Euclidean dot product. We have thus shown (2.0.46).

For the second proof, we begin by recalling (2.0.13) and (2.0.14):

(2.0.51) 
$$\hat{\psi}(t,\xi) = e^{-2\pi^2 it|\xi|^2} \hat{\phi}(\xi).$$

In particular, (2.0.51) implies that

$$(2.0.52) |\hat{\psi}(t,\xi)|^2 = |\hat{\phi}(\xi)|^2.$$

Integrating (2.0.52) over  $\mathbb{R}^n$ , we deduce that

$$(2.0.53)$$

where the  $L^2$  norm on the left-hand side of (2.0.53) is taken over the  $\xi$  variables only. Finally, by Plancherel's theorem, we see that (2.0.53) implies

$$(2.0.54)$$

Again, we have shown (2.0.46).

18.152 Introduction to Partial Differential Equations. Fall 201s1

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### MATH 18.152 COURSE NOTES - CLASS MEETING # 21

### 18.152 Introduction to PDEs, Fall 2011

# Class Meeting # 21: Lagrangian Field Theories

Professor: Jared Speck

Many of the PDEs of interest to us can be realized as the Euler-Lagrange equations corresponding to a function known as a  $Lagrangian \mathcal{L}$ . Closely related are the notions of the action corresponding to the Lagrangian, and the notion of a stationary point of the action. These ideas fall under a branch of mathematics known as the calculus of variations. As we will see, these ideas will provide a framework for deriving conserved (and more generally almost-conserved) quantities for solutions to the Euler-Lagrange equations, the availability of which plays a central role in the analysis of these solutions. Some important examples of PDEs to which these methods apply include the familiar linear wave equation, Maxwell's equations of electromagnetism, the Euler equations of fluid mechanics, and the Einstein equations of general relativity.

## 1. VARIATIONAL FORMULATION (THE ACTION PRINCIPLE)

In this section, we will study (scalar-valued) functions  $\phi$  on  $\mathbb{R}^{1+n}$ . They are sometimes called (scalar-valued) fields on  $\mathbb{R}^{1+n}$ . We will use the notation

$$(1.0.1) x = (x^0, x^1, \dots, x^n)$$

to denote the standard coordinates on  $\mathbb{R}^{1+n}$ , and as usual, we will sometimes use the alternate notation  $x^0 = t$ . We will use the notation

(1.0.2) 
$$\nabla \phi \stackrel{\text{def}}{=} (\nabla_t \phi, \nabla_1 \phi, \cdots, \nabla_n \phi)$$

to denote the spacetime gradient of  $\phi$ . We will study PDEs that are (in a sense to be explained) generated by a Lagrangian.

**Definition 1.0.1** (Lagrangian). A Lagrangian  $\mathcal{L}$  is a function of  $\phi$  and  $\nabla \phi$  (and sometimes the spacetime coordinates x and perhaps other quantities too). We indicate the dependence of  $\mathcal{L}$  on e.g.  $\phi$  and  $\nabla \phi$  by writing

$$\mathcal{L}(\phi, \nabla \phi).$$

**Example 1.0.1.** As we will see,  $\mathcal{L} \stackrel{\text{def}}{=} \frac{1}{2} (m^{-1})^{\alpha\beta} \nabla_{\alpha} \phi \nabla_{\beta} \phi$ , is the Lagrangian corresponding to the linear wave equation, where  $m^{-1} = \text{diag}(-1, 1, 1, \dots, 1)$  is the standard Minkowski metric.

Given a Lagrangian  $\mathcal{L}$  and a compact subset of spacetime  $\mathfrak{K}$ , we can define an important functional known as the action. The action inputs functions  $\phi$  and outputs a real number.

**Definition 1.0.2** (Action). Let  $\mathfrak{K} \subset \mathbb{R}^{1+n}$  be a compact subset of spacetime. We define the action  $\mathcal{A}$  of  $\phi$  over the set  $\mathfrak{K}$  by

(1.0.4) 
$$\mathcal{A}[\phi; \mathfrak{K}] \stackrel{\text{def}}{=} \int_{\mathfrak{C}} \mathcal{L}(\phi(x), \nabla \phi(x)) d^{1+n}x.$$

Above,  $d^{1+n}x \stackrel{\text{def}}{=} dt dx^1 d^2 \cdots dx^n$  denotes spacetime integration. We often omit the argument x of  $\phi$  and  $\nabla \phi$ .

A main theme that runs throughout this section is that it is possible to generalize certain aspects of standard calculus, which takes place on  $\mathbb{R}^{1+n}$ , to apply to (infinite dimensional) spaces of functions. In this context, the action  $\mathcal{A}$  plays the same role that a function plays in standard calculus. Moreover, many important PDEs have solutions that are *stationary points*<sup>1</sup> for the action. The notion of a stationary point is a generalization of the notion of a critical point from calculus. In order to define a stationary point of  $\mathcal{A}$ , we will need to introduce the notion of a *variation*. The motivation behind the next two definitions is that we would like to understand how  $\mathcal{A}[\phi; \mathfrak{K}]$  changes when we slightly change  $\phi$ .

**Definition 1.0.3** (Variation). Given a compact set  $\mathfrak{K}$ , a function  $\psi \in C_c^{\infty}(\mathfrak{K})$  is called a variation.

**Definition 1.0.4.** Given a variation  $\psi$  and a small number  $\epsilon$ , we define

(1.0.5) 
$$\phi_{\epsilon} \stackrel{\text{def}}{=} \phi + \underbrace{\epsilon \psi}_{\text{tiny perturbation of } \phi}$$

We now give the definition of a stationary point of the action. Stationary points are the moral equivalent of critical points<sup>2</sup> from calculus.

**Definition 1.0.5** (**Definition of a stationary point**  $\phi$ ). We say that  $\phi$  is a **stationary point** of the action if the following relation holds for all compact subsets  $\mathfrak{K}$  and all variations  $\psi \in C_c^{\infty}(\mathfrak{K})$ :

(1.0.6) 
$$\frac{d}{d\epsilon}\Big|_{\epsilon=0} \mathcal{A}[\phi_{\epsilon}; \mathfrak{K}] = 0.$$

The next theorem is central to our discussion in this section. It shows that the stationary points of  $\mathcal{A}$  verify a PDE called the *Euler-Lagrange equation*.

**Theorem 1.1** (The Principle of Stationary Action). Let  $\mathcal{L}(\phi, \nabla \phi, x)$  be a  $C^2$  Lagrangian. Then a  $C^2$  field  $\phi$  is a stationary point of the action if and only if the following **Euler-Lagrange** PDE is verified by  $\phi$ :

(1.0.7) 
$$\nabla_{\alpha} \left( \frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial (\nabla_{\alpha} \phi)} \right) = \frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial \phi}.$$

Above,  $\frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial (\nabla_{\alpha} \phi)}$  denotes partial differentiation of  $\mathcal{L}$  with respect to its argument  $\nabla_{\alpha} \phi$  with its other arguments (e.g., the other  $\nabla_{\mu} \phi$  with  $\mu \neq \alpha$ ,  $\phi$ , x, etc.) held fixed.

*Proof.* Let  $\mathfrak{K} \subset \mathbb{R}^{1+n}$  be a compact subset of spacetime and let  $\psi$  be any variation with support contained in  $\mathfrak{K}$ . For any  $\epsilon > 0$ , we define as in (1.0.5):  $\phi_{\epsilon} \stackrel{\text{def}}{=} \phi + \epsilon \psi$ . We then differentiate under the integral and use the chain rule to conclude that

<sup>&</sup>lt;sup>1</sup>Even though they are called "stationary points," they are actually fields on  $\mathbb{R}^{1+n}$ .

<sup>&</sup>lt;sup>2</sup>Recall that x is a critical point of the function f if f'(x) = 0.

(1.0.8) 
$$\frac{d}{d\epsilon} \mathcal{A}[\phi_{\epsilon}; \mathfrak{K}] \stackrel{\text{def}}{=} \frac{d}{d\epsilon} \int_{\mathfrak{K}} \mathcal{L}(\phi_{\epsilon}, \nabla \phi_{\epsilon}, x) d^{1+n} x = \int_{\mathfrak{K}} \partial_{\epsilon} \mathcal{L}(\phi_{\epsilon}, \nabla \phi_{\epsilon}, x) d^{1+n} x$$
$$= \int_{\mathfrak{K}} \frac{\partial \mathcal{L}(\phi_{\epsilon}, \nabla \phi_{\epsilon}, x)}{\partial \phi} \underbrace{\partial_{\epsilon} \phi_{\epsilon}}_{\psi} + \frac{\partial \mathcal{L}(\phi_{\epsilon}, \nabla \phi_{\epsilon}, x)}{\partial (\nabla_{\alpha} \phi)} \underbrace{\partial_{\epsilon} \nabla_{\alpha} \phi_{\epsilon}}_{\nabla_{\alpha} \psi} d^{1+n} x.$$

Above,  $\partial_{\epsilon}$  denotes the derivative with respect to the parameter  $\epsilon$  with all other variables held fixed. We now set  $\epsilon = 0$ , integrate by parts in (1.0.8) (and observe that the conditions on  $\psi$  guarantee that there are no boundary terms) to deduce that

(1.0.9) 
$$\frac{d}{d\epsilon} \mathcal{A}[\phi_{\epsilon}; \mathfrak{K}] = \int_{\mathfrak{K}} \frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial \phi} \psi + \frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial (\nabla_{\alpha} \phi)} \nabla_{\alpha} \psi \, d^{1+n} x$$

$$= \int_{\mathfrak{K}} \frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial \phi} \psi - \nabla_{\alpha} \left( \frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial (\nabla_{\alpha} \phi)} \right) \psi \, d^{1+n} x$$

$$= \int_{\mathfrak{K}} \left\{ \frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial \phi} - \nabla_{\alpha} \left( \frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial (\nabla_{\alpha} \phi)} \right) \right\} \psi \, d^{1+n} x.$$

We now observe that (1.0.9) is equal to 0 for all variations  $\psi$  if and only if the term in large brackets on the right-hand side of (1.0.9) must be 0. Since this observation holds for any compact subset  $\mathfrak{K}$ , we have thus shown that (1.0.7) holds if and only if  $\phi$  is a stationary point of the action.

**Example 1.0.2.** Let  $\mathcal{L} \stackrel{\text{def}}{=} -\frac{1}{2}(m^{-1})^{\alpha\beta}\nabla_{\alpha}\phi\nabla_{\beta}\phi$  (note that this  $\mathcal{L}$  does not directly depend on x) where  $m^{-1} = \text{diag}(-1, 1, 1, \dots, 1)$  is the standard Minkowski metric. Then

(1.0.10) 
$$\frac{\partial \mathcal{L}(\phi, \nabla \phi)}{\partial \phi} = 0,$$

(1.0.11) 
$$\frac{\partial \mathcal{L}(\phi, \nabla \phi)}{\partial (\nabla_{\mu} \phi)} = -(m^{-1})^{\mu \alpha} \nabla_{\alpha} \phi.$$

Therefore, the Euler-Lagrange equation corresponding to  $\mathcal{L}$  is

(1.0.12) 
$$\nabla_{\mu} \Big( (m^{-1})^{\mu \alpha} \nabla_{\alpha} \phi \Big) = 0.$$

Note that equation (1.0.12) is just the familiar linear wave equation  $(m^{-1})^{\alpha\beta}\nabla_{\alpha}\nabla_{\beta}\phi = 0$ .

#### 2. Coordinate Invariant Lagrangians

Many important PDEs are the Euler-Lagrange equations corresponding to *coordinate invariant* Lagrangians; we will explain what this means momentarily. Motivated by this claim, we will now introduce a class of changes of coordinates on spacetime. The new coordinates will be formed by flowing the old coordinates in the direction of a vectorfield Y on spacetime. These new coordinates will therefore verify a system of ordinary differential equations generated by the flow of Y. In the next proposition, we review some facts concerning these new coordinates; these facts are basic results in ODE theory.

Proposition 2.0.1 (Basic facts from ODE theory for autonomous systems). Let  $Y(x) = (Y^0(\underbrace{x^0, \cdots, x^n}_{x}), Y^1(x^0, \cdots, x^n), \cdots, Y^n(x^0, \cdots, x^n))$  be a smooth vectorfield on  $\mathbb{R}^{1+n}$ . Assume that

there exists a uniform constant C > 0 such that

(2.0.13) 
$$|\nabla_{\mu}Y^{\nu}(x)| \le C, \quad x \in \mathbb{R}^{1+n}, \quad 0 \le \mu, \nu \le n.$$

Consider the initial value problem (where the independent variable is the "flow parameter"  $\epsilon$ ) for the following system of ordinary differential equations:

(2.0.14) 
$$\frac{d}{d\epsilon}\widetilde{x}^{\mu}(\epsilon) = Y^{\mu}(\widetilde{x}),$$

$$\widetilde{x}^{\mu}(0) = x^{\mu}$$

Then there exists a number  $\epsilon_0 > 0$  such that the initial value problem (2.0.14) - (2.0.15) has a unique smooth (in  $\epsilon$ ) solution existing on the interval  $\epsilon \in [-\epsilon_0, \epsilon_0]$ .

Let us denote the "flow map" from the data x to the solution  $\widetilde{x}$  at flow parameter  $\epsilon$  by  $\widetilde{x} = F_{\epsilon}(x)$ . Then on the interval  $[-\epsilon_0, \epsilon_0]$ , the flow map

$$(2.0.16) x \to F_{\epsilon}(x) \stackrel{def}{=} \widetilde{x}.$$

is a smooth (in x), bijective map from  $\mathbb{R}^{1+n}$  to  $\mathbb{R}^{1+n}$  with smooth inverse  $F_{-\epsilon}(\cdot)$ , i.e.,  $\widetilde{x} = F_{\epsilon}(x) \implies x = F_{-\epsilon}(\widetilde{x})$ ; such maps are called **diffeomorphisms** of  $\mathbb{R}^{1+n}$ . Furthermore, if  $|\epsilon_1| + |\epsilon_2| \le \epsilon_0$ , then the flow map verifies the following **one-parameter commutative group** properties:

$$(2.0.17) F_{\epsilon_1} \circ F_{\epsilon_2} = F_{\epsilon_2} \circ F_{\epsilon_1} = F_{\epsilon_1 + \epsilon_2}.$$

Let us also denote the derivative matrix corresponding to the flow map  $F_{\epsilon}$  by M:

$$(2.0.18) M_{\nu}^{\mu} \stackrel{def}{=} \frac{\partial \widetilde{x}^{\mu}}{\partial x^{\nu}}.$$

Then if  $|\epsilon|$  is sufficiently small, we have the following expansions in  $\epsilon$ :

(2.0.19) 
$$\widetilde{x}^{\mu} \stackrel{def}{=} F_{\epsilon}^{\mu}(x) = x^{\mu} + \epsilon Y^{\mu}(x) + \epsilon^{2} \mathcal{R}^{\mu}(\epsilon, x),$$

$$(2.0.20) M^{\mu}_{\nu} = \delta^{\mu}_{\nu} + \epsilon \nabla_{\nu} Y^{\mu}(x) + \epsilon^{2} \nabla_{\nu} \mathcal{R}^{\mu}(\epsilon, x),$$

$$(2.0.21) (M^{-1})^{\mu}_{\nu} = \frac{\partial x^{\mu}}{\partial \widetilde{x}^{\nu}} = \delta^{\mu}_{\nu} - \epsilon \nabla_{\nu} Y^{\mu}(x) + \epsilon^{2} \mathcal{S}^{\mu}_{\nu}(\epsilon, x),$$

(2.0.22) 
$$det M^{-1} = 1 - \epsilon \nabla_{\alpha} Y^{\alpha} + \epsilon^{2} \mathcal{S}(\epsilon, x).$$

Above,  $\mathcal{R}^{\mu}(\epsilon, x)$ ,  $\nabla_{\nu}\mathcal{R}^{\mu}(\epsilon, x)$ ,  $\mathcal{S}^{\mu}_{\nu}(\epsilon, x)$ ,  $\mathcal{S}(\epsilon, x)$  are smooth functions of  $(\epsilon, x)$  for  $\epsilon \in [-\epsilon_0, \epsilon_0]$ ,  $x \in \mathbb{R}^{1+n}$ .

Remark 2.0.1. The assumption (2.0.13) guarantees that the "time of existence"  $\epsilon_0$  can be chosen to be independent of the initial data x.

*Proof.* Most of the results of Proposition 2.0.1 are standard facts from ODE theory and will not be proved here. We will show how to derive the expansions (2.0.21) and (2.0.22) from the other results. To this end, we will need some basic facts from matrix theory. We will use the following norm for  $(1+n) \times (1+n)$  matrix-valued functions on  $\mathbb{R}^{1+n}$ :

(2.0.23) 
$$||M|| \stackrel{\text{def}}{=} \max_{x \in \mathbb{R}^{1+n}} \sqrt{\sum_{0 \le \mu, \nu \le n} |M_{\nu}^{\mu}(x)|^2}.$$

Now if I is the 1+n identity matrix<sup>3</sup>, and ||A|| is a sufficiently small  $(1+n) \times (1+n)$  matrix, then the matrix  $M \stackrel{\text{def}}{=} (I-A)^{-1}$  can be expanded in a convergent series:

$$(2.0.24) (I-A)^{-1} = I + A + A^2 + A^3 + \cdots$$

Note in particular that the tail (i.e., all but the first two terms) can be bounded by

$$(2.0.25)$$

if ||A|| is sufficiently small. We now apply (2.0.24) and (2.0.25) to the matrix M defined in (2.0.18) (where  $A_{\nu}^{\mu} \stackrel{\text{def}}{=} \epsilon \nabla_{\nu} Y^{\mu}$ ), thereby arriving at (2.0.21). To derive (2.0.22), we first Taylor expand the determinant (viewed as a real-valued function of

To derive (2.0.22), we first Taylor expand the determinant (viewed as a real-valued function of matrices) for sufficiently small ||A||:

(2.0.26) 
$$\det(I+A) = 1 + A_{\alpha}^{\alpha} + O(\|A\|^2)$$

Above, we write  $O(\|A\|^2)$  to denote a term that can be bounded by  $C\|A\|^2$ , where C > 0 is some positive constant independent of (all sufficiently small) A. The expansion (2.0.22) now follows from (2.0.21) and (2.0.26). We remark that you will derive the expansion (2.0.26) in your homework in more detail.

We will now "define" how various fields and their derivatives transform under a change of coordinates. A full justification of these definitions can be found in books on tensor analysis or differential geometry.

**Definition 2.0.6** (Transformation properties of fields). Let  $\phi(x)$  be a scalar-valued function, let m(x) be an (invertible) metric (depending on x) with components  $m_{\mu\nu}(x)$ , and let  $x \to \widetilde{x}$  be a spacetime diffeomorphism. Then upon changing coordinates  $x \to \widetilde{x}$ , these quantities transform as follows:

(2.0.27a) 
$$\widetilde{\phi}(\widetilde{x}) \stackrel{\text{def}}{=} \phi|_{(x \circ \widetilde{x})},$$

(2.0.27b) 
$$\widetilde{\nabla}_{\mu}\widetilde{\phi}(\widetilde{x}) \stackrel{\text{def}}{=} (M^{-1})_{\mu}^{\alpha}|_{(x\circ\widetilde{x})} \nabla_{\alpha}\phi|_{x\circ\widetilde{x}},$$

$$(2.0.27c) \qquad \widetilde{m}_{\mu\nu}(\widetilde{x}) \stackrel{\text{def}}{=} (M^{-1})^{\alpha}_{\mu|_{(x\circ\widetilde{x})}} (M^{-1})^{\beta}_{\nu|_{(x\circ\widetilde{x})}} m_{\alpha\beta}|_{(x\circ\widetilde{x})},$$

$$(2.0.27d) \qquad (\widetilde{m}^{-1})^{\mu\nu}(\widetilde{x}) \stackrel{\text{def}}{=} M^{\mu}_{\alpha}|_{(x\circ\widetilde{x})} M^{\nu}_{\beta}|_{(x\circ\widetilde{x})} (m^{-1})^{\alpha\beta}|_{(x\circ\widetilde{x})}.$$

 $<sup>\</sup>overline{^{3}}$ Note that  $I^{\mu}_{\nu} = \delta^{\mu}_{\nu}$ .

Above and throughout, we use the notation

(2.0.28a) 
$$\nabla_{\mu} \stackrel{\text{def}}{=} \frac{\partial}{\partial x^{\mu}},$$
(2.0.28b) 
$$\widetilde{\nabla}_{\mu} \stackrel{\text{def}}{=} \frac{\partial}{\partial \widetilde{x}^{\mu}},$$

 $M^{\mu}_{\nu} \stackrel{\text{def}}{=} \frac{\partial \widetilde{x}^{\mu}}{\partial x^{\nu}}$  is the derivative matrix defined in (2.0.18), and  $(M^{-1})^{\mu}_{\nu} = \frac{\partial x^{\mu}}{\partial \widetilde{x}^{\nu}}$  is its inverse. Furthermore, the notation  $x \circ \widetilde{x}$  indicates that we are viewing x as a function of  $\widetilde{x}$ ; this is possible since  $x \to \widetilde{x}$  is a diffeomorphism.

Remark 2.0.2. (2.0.27a) simply says that the transformed function  $\widetilde{\phi}$  takes the same value at the new coordinate  $\widetilde{x}$  that  $\phi$  takes at the old coordinate x. (2.0.27b) is really just the chain rule expressing  $\frac{\partial}{\partial \widetilde{x}^{\mu}}$  in terms of  $\frac{\partial}{\partial x^{\mu}}$ . (2.0.27c) is the standard transformation law for tensors with two upstairs indices. These transformation laws generalize to other tensors in a straightforward fashion; the generalization can be found in books on tensor analysis/ differential geometry. Roughly speaking, tensors with indices downstairs transform by multiplication by the matrix  $M^{-1}$  (one copy of  $M^{-1}$  for each index), and tensors with indices upstairs transform by multiplication by the matrix M (one copy of M for each index).

We will now define what it means for a Lagrangian to be coordinate invariant.

**Definition 2.0.7** (Coordinate invariant Lagrangian). Let  $\mathcal{L}(\phi, \nabla \phi, m)$  be a Lagrangian that depends only on  $\phi$ ,  $\nabla \phi$ , and the Minkowski metric m. We say that  $\mathcal{L}$  is coordinate invariant if for all spacetime diffeomorphisms  $x \to \widetilde{x}$ , we have that

(2.0.29) 
$$\mathcal{L}(\phi(x), \nabla \phi(x), m(x)) = \mathcal{L}(\widetilde{\phi}(\widetilde{x}), \widetilde{\nabla} \widetilde{\phi}(\widetilde{x}), \widetilde{m}(\widetilde{x})),$$

where the transformed fields are defined in Definition 2.0.6.

**Example 2.0.3.** Consider the Lagrangian for the linear wave equation:  $\mathcal{L}(\phi, \nabla \phi, m) = -\frac{1}{2}(m^{-1})^{\mu\nu}\nabla_{\mu}\phi\nabla_{\nu}\phi$ . Using (2.0.27a) - (2.0.27c) and the fact that  $M^{\mu}_{\alpha}(M^{-1})^{\kappa}_{\mu} = \delta^{\kappa 4}_{\alpha}$ , we compute that

(2.0.30) 
$$\mathcal{L}(\widetilde{\phi}, \widetilde{\nabla}\widetilde{\phi}, \widetilde{m}) \stackrel{\text{def}}{=} -\frac{1}{2} (\widetilde{m}^{-1})^{\mu\nu} \widetilde{\nabla}_{\mu} \widetilde{\phi} \widetilde{\nabla}_{\nu} \widetilde{\phi}$$

$$= -\frac{1}{2} M_{\alpha}^{\mu} M_{\beta}^{\nu} (m^{-1})^{\alpha\beta} (M^{-1})_{\mu}^{\kappa} \nabla_{\kappa} \phi (M^{-1})_{\mu}^{\lambda} \nabla_{\lambda} \phi$$

$$= -\frac{1}{2} (m^{-1})^{\mu\nu} \nabla_{\mu} \phi \nabla_{\nu} \phi.$$

This Lagrangian is therefore coordinate invariant.

As we will see, the availability of an energy-momentum tensor for certain Euler-Lagrange equations is closely connected to the coordinate invariance property of their Lagrangians. In order to derive this connection, we will need to understand more about how the coordinate transformations (2.0.16) vary with  $\epsilon$ .

<sup>&</sup>lt;sup>4</sup>Recall that  $\delta_{\alpha}^{\kappa} = 1$  if  $\alpha = \kappa$  and  $\delta_{\alpha}^{\kappa} = 1$  if  $\alpha \neq \kappa$ ;  $\delta_{\alpha}^{\kappa}$  can be viewed as the identity matrix.

Proposition 2.0.2 (Derivatives with respect to the flow parameter  $\epsilon$ ). Let  $\tilde{x}^{\mu} = F_{\epsilon}(x)$ be the change of spacetime coordinates defined in (2.0.16), and let  $\widetilde{\phi}$ ,  $\widetilde{\nabla}_{\mu}\widetilde{\phi}$ ,  $\widetilde{m}_{\mu\nu}$ ,  $(\widetilde{m}^{-1})^{\mu\nu}$  be the transformed fields defined in Definition 2.0.6. Then the following identities hold for all spacetime points  $\widetilde{x}$ :

(2.0.31a) 
$$\partial_{\epsilon} \Big|_{\widetilde{z}=0} \widetilde{\phi}|_{\widetilde{x}} = -Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} \phi|_{\widetilde{x}},$$

$$(2.0.31b) \qquad \partial_{\epsilon} \Big|_{\epsilon=0} \widetilde{\nabla}_{\mu} \widetilde{\phi}|_{\widetilde{x}} = -\nabla_{\mu} Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} \phi|_{\widetilde{x}} - Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} \nabla_{\mu} \phi|_{\widetilde{x}} = -\nabla_{\mu} (Y^{\alpha} \nabla_{\alpha} \phi)|_{\widetilde{x}},$$

$$(2.0.31c) \qquad \partial_{\epsilon} \Big|_{\epsilon=0}^{\epsilon=0} \widetilde{m}_{\mu\nu}|_{\widetilde{x}} = -m_{\nu\alpha}|_{\widetilde{x}} \nabla_{\mu} Y^{\alpha}|_{\widetilde{x}} - m_{\mu\alpha}|_{\widetilde{x}} \nabla_{\nu} Y^{\alpha}|_{\widetilde{x}} - \underbrace{Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} m_{\mu\nu}|_{\widetilde{x}}}_{0 \text{ for the Minkowski metric}},$$

$$(2.0.31d) \partial_{\epsilon}\Big|_{\epsilon=0} (\widetilde{m}^{-1})^{\mu\nu}|_{\widetilde{x}} = (m^{-1})^{\alpha\nu}|_{\widetilde{x}} \nabla_{\alpha} Y^{\mu}|_{\widetilde{x}} + (m^{-1})^{\mu\alpha}|_{\widetilde{x}} \nabla_{\alpha} Y^{\nu}|_{\widetilde{x}} - \underbrace{Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} (m^{-1})^{\mu\nu}|_{\widetilde{x}}}_{0 \text{ for the Minkowski metric}},$$

$$(2.0.31e) \quad \partial_{\epsilon}|_{\epsilon=0} det M^{-1}|_{\widetilde{x}} = -\nabla_{\alpha} Y^{\alpha}|_{\widetilde{x}}.$$

Above and for the remainder of these notes,  $\partial_{\epsilon}$  denotes the derivative of an  $\epsilon$ -dependent quantity with the new coordinates  $\widetilde{x}$  held fixed.

**Remark 2.0.3.** In the language of differential geometry, the tilded fields are the *Lie derivatives* of the un-tilded fields with respect to the vectorfield -Y.

*Proof.* Recall that  $\widetilde{x}^{\mu} = F^{\mu}_{\epsilon}(x)$ ,  $x^{\mu} = F^{\mu}_{-\epsilon}(\widetilde{x})$ ,  $F^{\mu}_{0}(x) = x^{\mu}$  (so that  $x = \widetilde{x}$  when  $\epsilon = 0$ ) and  $\partial_{\epsilon}F^{\mu}_{\epsilon}(\cdot)=Y^{\mu}(\cdot)$ . Therefore, using the chain rule, we compute that

(2.0.32) 
$$\partial_{\epsilon}|_{\epsilon=0}\widetilde{\phi}(\widetilde{x}) \stackrel{\text{def}}{=} \partial_{\epsilon}|_{\epsilon=0}\phi(F_{-\epsilon}(\widetilde{x})) = \nabla_{\alpha}\phi|_{\widetilde{x}}\partial_{\epsilon}|_{\epsilon=0}F_{-\epsilon}^{\alpha}(\widetilde{x})$$
$$= -Y^{\alpha}|_{\widetilde{x}}\nabla_{\alpha}\phi|_{\widetilde{x}},$$

We have thus shown (2.0.31a).

Similarly, with the help of (2.0.21), and noting that  $(M^{-1})^{\nu}_{\mu} = \delta^{\nu}_{\mu}$  when  $\epsilon = 0$  and  $\partial_{\epsilon}|_{\epsilon=0} [(M^{-1})^{\alpha}_{\mu} \circ (M^{-1})^{\alpha}_{\mu}]$  $F_{-\epsilon}|_{\widetilde{x}} = -\nabla_{\mu}Y^{\alpha}|_{\widetilde{x}}$ , we compute that

$$\begin{split} \partial_{\epsilon}|_{\epsilon=0} \widetilde{\nabla}_{\mu} \widetilde{\phi}(\widetilde{x}) &\stackrel{\text{def}}{=} \partial_{\epsilon}|_{\epsilon=0} \Big\{ (M^{-1})^{\alpha}_{\mu} \circ F_{-\epsilon}(\widetilde{x}) (\nabla_{\alpha} \phi) \circ F_{-\epsilon}(\widetilde{x}) \Big\} \\ &= \Big\{ \partial_{\epsilon}|_{\epsilon=0} \big[ (M^{-1})^{\alpha}_{\mu} \circ F_{-\epsilon}(\widetilde{x}) \big] \Big\} (\nabla_{\alpha} \phi) \circ F_{-\epsilon}(\widetilde{x}) + (M^{-1})^{\alpha}_{\mu} \circ F_{-\epsilon}(\widetilde{x}) \partial_{\epsilon}|_{\epsilon=0} (\nabla_{\alpha} \phi) \circ F_{-\epsilon}(\widetilde{x}) \\ &= -\nabla_{\mu} Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} \phi|_{\widetilde{x}} - \underbrace{(M^{-1})^{\alpha}_{\mu}|_{\widetilde{x}}}_{\delta^{\alpha}} Y^{\beta}|_{\widetilde{x}} \nabla_{\beta} \nabla_{\alpha} \phi|_{\widetilde{x}}. \end{split}$$

We have thus shown we have thus shown (2.0.31b). The proofs of (2.0.31c) and (2.0.31d) are similar, and we omit the details.

To prove (2.0.31e), we simply differentiate the expansion (2.0.22) with respect to  $\epsilon$  and set  $\epsilon = 0$ .

We now state the following simple corollary to Proposition 2.0.2.

Corollary 2.0.3 (The derivative of  $\mathcal{L}$  with respect to the flow parameter  $\epsilon$ ). Let  $\mathcal{L}(\phi, \nabla \phi, m)$  be a  $C^2$  Lagrangian. Then under the assumptions of Proposition 2.0.2, the following identity holds at all spacetime points:

$$(2.0.34) \qquad \partial_{\epsilon}|_{\epsilon=0} \mathcal{L}(\widetilde{\phi}, \widetilde{\nabla}\widetilde{\phi}, \widetilde{m}) = -\frac{\partial \mathcal{L}(\phi, \nabla\phi, m)}{\nabla\phi} Y^{\alpha} \nabla_{\alpha} \phi$$

$$-\frac{\partial \mathcal{L}(\phi, \nabla\phi, m)}{\partial(\nabla_{\mu}\phi)} \nabla_{\mu} (Y^{\alpha} \nabla_{\alpha}\phi)$$

$$-\frac{\partial \mathcal{L}(\phi, \nabla\phi, m)}{\partial m_{\mu\nu}} \Big\{ m_{\alpha\nu} \nabla_{\mu} Y^{\alpha} + m_{\mu\alpha} \nabla_{\nu} Y^{\alpha} + \underbrace{Y^{\alpha} \nabla_{\alpha} m_{\mu\nu}}_{0} \Big\}.$$

*Proof.* By the chain rule, we have that

(2.0.35) 
$$\partial_{\epsilon} \mathcal{L}(\widetilde{\phi}, \widetilde{\nabla} \widetilde{\phi}, \widetilde{m}) = \frac{\partial \mathcal{L}(\widetilde{\phi}, \widetilde{\nabla} \widetilde{\phi}, \widetilde{m})}{\partial \phi} \partial_{\epsilon} \widetilde{\phi} + \frac{\partial \mathcal{L}(\widetilde{\phi}, \widetilde{\nabla} \widetilde{\phi}, \widetilde{m})}{\partial (\nabla_{\mu} \phi)} \partial_{\epsilon} \widetilde{\nabla} \widetilde{\phi} + \frac{\partial \mathcal{L}(\widetilde{\phi}, \widetilde{\nabla} \widetilde{\phi}, \widetilde{m})}{\partial m_{\mu\nu}} \partial_{\epsilon} \widetilde{m}_{\mu\nu}.$$

The relation (2.0.34) now follows from Proposition 2.0.2 and (2.0.35).

#### 3. The energy-momentum tensor

The main goal of this section is to show that for a certain class of coordinate invariant Lagrangians  $\mathcal{L}$ , there exists an energy-momentum tensor  $T^{\mu\nu}$ . This  $T^{\mu\nu}$  plays the same role in the analysis of the corresponding Euler-Lagrange equation corresponding to  $\mathcal{L}$  as it did in our previous analysis of the linear wave equation. More precisely, for solutions to the Euler-Lagrange equation corresponding to  $\mathcal{L}$ , we will show that  $\nabla_{\mu}T^{\mu\nu}=0$ . As we saw earlier in the course, this identity forms the basis for the derivation of conserved quantities in solutions to the Euler-Lagrange equations.

Theorem 3.1 (Derivation and divergence-free property of the energy-momentum tensor). Let  $\mathcal{L}(\phi, \nabla \phi, m)$  be a coordinate invariant Lagrangian (in the sense of Definition 2.0.7) that depends only on  $\phi, \nabla \phi$ , and the Minkowski metric m. Let

(3.0.36) 
$$T^{\mu\nu} \stackrel{def}{=} 2 \frac{\partial \mathcal{L}}{\partial m_{\mu\nu}} + (m^{-1})^{\mu\nu} \mathcal{L}$$

be the energy-momentum tensor corresponding to  $\mathcal{L}$ . Then  $T^{\mu\nu}$  is symmetric:

(3.0.37) 
$$T^{\mu\nu} = T^{\nu\mu}, \qquad 0 \le \mu, \nu \le n.$$

Furthermore, if  $\phi$  verifies the Euler-Lagrange equation (1.0.7), the following divergence identity is verified by  $T^{\mu\nu}$ :

(3.0.38) 
$$\nabla_{\mu} T^{\mu\nu} = 0, \qquad (\nu = 0, 1, 2, \dots, n).$$

*Proof.* The relation (3.0.37) follows easily from (3.0.36) since  $m_{\mu\nu} = m_{\nu\mu}$ .

We will now prove (3.0.38). To this end, let  $\mathfrak{K} \subset \mathbb{R}^{1+n}$  be a compact spacetime subset, and let  $Y: \mathbb{R}^{1+n} \to \mathbb{R}^{1+n}$  be a smooth vectorfield with support contained in  $\mathfrak{K}$ . Let  $\widetilde{x}$  be the change of variables (2.0.16), and consider the transformed quantities  $\widetilde{\phi}, \widetilde{\nabla} \widetilde{\phi}, \widetilde{m}, \widetilde{m}^{-1}$  given in Definition 2.0.6. Now by assumption, we have that  $\mathcal{L}(\phi, \nabla \phi, m) = \mathcal{L}(\widetilde{\phi}, \widetilde{\nabla} \widetilde{\phi}, \widetilde{m})$ . Furthermore, by the standard change of variables theorem from advanced calculus, we have that  $d^{1+n}x = \det \frac{\partial x}{\partial \widetilde{x}} d^{1+n}\widetilde{x} = \det M^{-1} d^{1+n}\widetilde{x}$ , where the matrix M is defined in (2.0.18). Therefore, we have that

(3.0.39) 
$$\mathcal{A}[\phi; \mathfrak{K}] = \int_{\mathfrak{K}} \mathcal{L}(\phi, \nabla \phi, m) \, d^{1+n} x$$
$$= \int_{\mathfrak{K}} \mathcal{L}(\widetilde{\phi}, \widetilde{\nabla} \widetilde{\phi}, \widetilde{m}) \, \det M^{-1} d^{1+n} \widetilde{x}.$$

Now the left-hand side of (3.0.39) doesn't depend on  $\epsilon$ . We therefore have that

(3.0.40) 
$$\frac{d}{d\epsilon}|_{\epsilon=0}\mathcal{A}[\phi;\mathfrak{R}] = 0.$$

On the other hand, we can differentiate under the integral on the right-hand side of (3.0.39) with respect to  $\epsilon$  at  $\epsilon=0$  and use (2.0.31e) plus Corollary 2.0.3 (together with the fact that  $x=\widetilde{x}$  when  $\epsilon=0$ ) to deduce that

$$(3.0.41) \qquad \frac{d}{d\epsilon}|_{\epsilon=0}\mathcal{A}[\phi;\mathfrak{K}] = \int_{\mathfrak{K}} -\frac{\partial \mathcal{L}(\phi,\nabla\phi,m)}{\nabla\phi} Y^{\alpha} \nabla_{\alpha}\phi - \frac{\partial \mathcal{L}(\phi,\nabla\phi,m)}{\partial(\nabla_{\mu}\phi)} \nabla_{\mu} (Y^{\alpha}\nabla_{\alpha}\phi) d^{1+n}x$$

$$-\int_{\mathfrak{K}} \frac{\partial \mathcal{L}(\phi,\nabla\phi,m)}{\partial m_{\mu\nu}} \Big\{ m_{\alpha\nu} \nabla_{\mu} Y^{\alpha} + m_{\mu\alpha} \nabla_{\nu} Y^{\alpha} + \underbrace{Y^{\alpha}\nabla_{\alpha} m_{\mu\nu}}_{0} \Big\} d^{1+n}x$$

$$-\int_{\mathfrak{K}} \mathcal{L}(\phi,\nabla\phi,m) \nabla_{\alpha} Y^{\alpha} d^{1+n}x.$$

Integrating by parts in (3.0.41) and using (3.0.40), we have that

$$(3.0.42) 0 = -\int_{\mathfrak{K}} \left\{ \frac{\partial \mathcal{L}(\phi, \nabla \phi, m)}{\nabla \phi} - \nabla_{\mu} \left( \frac{\partial \mathcal{L}(\phi, \nabla \phi, m)}{\partial (\nabla_{\mu} \phi)} \right) \right\} Y^{\alpha} \nabla_{\alpha} \phi \, d^{1+n} x$$
$$- \int_{\mathfrak{K}} \frac{\partial \mathcal{L}(\phi, \nabla \phi, m)}{\partial m_{\mu\nu}} \left\{ m_{\alpha\nu} \nabla_{\mu} Y^{\alpha} + m_{\mu\alpha} \nabla_{\nu} Y^{\alpha} + \underbrace{Y^{\alpha} \nabla_{\alpha} m_{\mu\nu}}_{0} \right\} d^{1+n} x$$
$$- \int_{\mathfrak{K}} \mathcal{L}(\phi, \nabla \phi, m) \nabla_{\alpha} Y^{\alpha} \, d^{1+n} x.$$

We now note that the Euler-Lagrange equation (1.0.7) implies that the first line on the right-hand side of (3.0.42) is 0. Therefore, we collect the remaining terms together to derive that

$$(3.0.43) \qquad 0 = -\int_{\mathfrak{K}} \left\{ \frac{\partial \mathcal{L}(\phi, \nabla \phi, m)}{\partial m_{\mu\nu}} + \frac{1}{2} (m^{-1})^{\mu\nu} \mathcal{L}(\phi, \nabla \phi, m) \right\} \left\{ m_{\alpha\nu} \nabla_{\mu} Y^{\alpha} + m_{\mu\alpha} \nabla_{\nu} Y^{\alpha} \right\} d^{1+n} x$$
$$= -\int_{\mathfrak{K}} \left\{ 2 \frac{\partial \mathcal{L}(\phi, \nabla \phi, m)}{\partial m_{\mu\nu}} + (m^{-1})^{\mu\nu} \mathcal{L}(\phi, \nabla \phi, m) \right\} m_{\alpha\nu} \nabla_{\mu} Y^{\alpha} d^{1+n} x.$$

Integrating by parts in (3.0.43), we deduce that

$$(3.0.44) 0 = \int_{\Re} \nabla_{\mu} \left\{ 2 \frac{\partial \mathcal{L}(\phi, \nabla \phi, m)}{\partial m_{\mu\nu}} + (m^{-1})^{\mu\nu} \mathcal{L}(\phi, \nabla \phi, m) \right\} m_{\alpha\nu} Y^{\alpha} d^{1+n} x.$$

Since (3.0.43) must hold for all such smooth vectorfields Y with support contained in  $\mathfrak{K}$ , we conclude that the divergence of the term in braces is 0:

(3.0.45) 
$$\nabla_{\mu} \left\{ 2 \frac{\partial \mathcal{L}(\phi, \nabla \phi, m)}{\partial m_{\mu\nu}} + (m^{-1})^{\mu\nu} \mathcal{L}(\phi, \nabla \phi, m) \right\} = 0.$$

We have thus shown that (3.0.38) holds.

**Example 3.0.4.** The Lagrangian for the linear wave equation is  $\mathcal{L} = -\frac{1}{2}(m^{-1})^{\alpha\beta}\nabla_{\alpha}\phi\nabla_{\beta}\phi$ . We therefore appeal to (3.0.36) and calculate that

$$(3.0.46) T^{\mu\nu} \stackrel{\text{def}}{=} 2 \frac{\partial \mathcal{L}}{\partial m_{\mu\nu}} + (m^{-1})^{\mu\nu} \mathcal{L}$$
$$= (m^{-1})^{\mu\alpha} (m^{-1})^{\nu\beta} \nabla_{\alpha} \phi \nabla_{\beta} \phi - \frac{1}{2} (m^{-1})^{\mu\nu} (m^{-1})^{\alpha\beta} \nabla_{\alpha} \phi \nabla_{\beta} \phi.$$

**Remark 3.0.4.** To derive (3.0.46), we have used the fact that if q is any quantity, and m is a symmetric invertible  $(1+n) \times (1+n)$  matrix that depends on q, then

$$(3.0.47) \qquad \frac{d}{dq} (m^{-1})^{\mu\nu} = -(m^{-1})^{\mu\alpha} (m^{-1})^{\nu\beta} \frac{d}{dq} m_{\alpha\beta}, \qquad 0 \le \mu, \nu \le n.$$

You will derive the simple relation (3.0.47) in your homework. In particular, it follows from (3.0.47) that

(3.0.48) 
$$\frac{\partial (m^{-1})^{\mu\nu}}{\partial m_{\kappa\lambda}} = -(m^{-1})^{\mu\kappa} (m^{-1})^{\nu\lambda}.$$

On the left-hand side of (3.0.48), we are viewing the components  $(m^{-1})^{\mu\nu}$  as functions of the components  $m_{\kappa\lambda}$ ,  $0 \le \kappa, \lambda \le n$ .

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### MATH 18.152 COURSE NOTES - CLASS MEETING # 24

#### 18.152 Introduction to PDEs, Fall 2011

# Class Meeting # 24: Transport Equations and Burger's Equation

Professor: Jared Speck

In these notes, we introduce a class of evolution PDEs known as transport equations. Such equations arise in a physical context whenever a quantity is "transported" in a certain direction. Some important physical examples include the mass density flow for an incompressible fluid, and the Boltzmann equation of kinetic theory. We discuss both linear transport equations and a famous nonlinear transport equation known as Burger's equation. One of our major goals is to show that in contrast to the case of linear PDEs, solutions to Burger's equations can develop singularities in finite time.

#### 1. Transport Equations

Linear homogeneous transport equations are PDEs of the form

$$(1.0.1) X^{\mu} \partial_{\mu} u = 0,$$

where  $(x^0, x^1, \dots, x^n)$  are coordinates on  $\mathbb{R}^{1+n}$  and  $X(x^0, \dots, x^n)$  is a vectorfield on  $\mathbb{R}^{1+n}$ . As we will soon see, the transport equation is closely connected to the following system of ODEs for the unknowns  $\gamma^{\mu}$ :

(1.0.2) 
$$\frac{d}{ds}\gamma^{\mu}(s) = X^{\mu}(\gamma^{0}(s), \gamma^{1}(s), \cdots, \gamma^{n}(s)), \qquad (\mu = 0, 1, \cdots, n).$$

Given initial conditions  $\gamma^{\mu}(0)$ , the solutions to (1.0.2) are curves  $\gamma: I \to \mathbb{R}^{1+n}$ , where I is an interval. These curves are known as the *integral curves* of the vectorfield X. They are also known as the *characteristic curves* associated to the PDE (1.0.1). The next proposition clarifies the connection between the transport equation (1.0.1) and its characteristic curves.

Proposition 1.0.1 (Connection between transport equations and ODEs). If u solves the transport equation (1.0.1), then u is constant along the integral curves of X. More precisely, if  $\gamma(s)$  is any solution to (1.0.2), then

(1.0.3) 
$$\frac{d}{ds}u(\gamma^0(s),\cdots,\gamma^n(s)) = 0.$$

*Proof.* Using the chain rule, (1.0.2), and (1.0.1), we have that

$$(1.0.4) \qquad \frac{d}{ds}u(\gamma^{0}(s),\dots,\gamma^{n}(s)) = \sum_{\mu=0}^{n} \left(\frac{\partial}{\partial x^{\mu}}u\right)|_{\gamma(s)}\frac{d}{ds}\gamma^{\mu}(s)$$
$$= \sum_{\mu=0}^{n} \left(\frac{\partial}{\partial x^{\mu}}u\right)|_{\gamma(s)}X^{\mu}(\gamma(s)) = (X^{\mu}\partial_{\mu}u)|_{\gamma(s)} = 0.$$

1.1. Constant vectorfields. Let's consider a very special case of (1.0.1) in which the components of X are constant. That is, we assume that

$$(1.1.1) X = (\overline{X}^0, \overline{X}^1, \cdots, \overline{X}^n)$$

where the  $\overline{X}^{\mu}$  are constants independent of  $(x^0, \dots, x^n)$ .

In this case, the solutions to the system (1.0.2) of ODEs are the straight lines

$$\gamma(s) = \mathring{\gamma} + sX,$$

where  $\mathring{\gamma} = \gamma(0)$  is a constant vector.

For concreteness, let's also assume that

$$(1.1.3) \overline{X}^0 = 1$$

and as usual, let's use the alternate notation  $x^0 = t$ . Let's assume that we are given Cauchy data for u on the hypersurface  $\{t = 0\} \times \mathbb{R}^n$ :

$$(1.1.4) u(0, x^1, \dots, x^n) = f(x^1, \dots, x^n),$$

where f is a function on  $\mathbb{R}^n$ . We now note that

$$(1.1.5) (t, x^1, \dots, x^n) = (0, x^1 - t\overline{X}^1, \dots, x^n - t\overline{X}^n) + tX,$$

which implies that the spacetime point  $(t, x^1, \dots, x^n)$  lies on the characteristic curve  $\gamma(t)$  passing through the "initial" point  $(0, x^1 - t\overline{X}^1, \dots, x^n - t\overline{X}^n) \subset \{t = 0\} \times \mathbb{R}^n$ . Therefore, by Proposition 1.0.1, we have that

(1.1.6) 
$$u(0, x^1, \dots, x^n) = f(x^1 - t\overline{X}^1, \dots, x^n - t\overline{X}^n).$$

and we have *explicitly solved* the PDE (1.0.1).

## 2. A Nonlinear Scalar PDE: Burger's (Inviscid) Equation

Burger's equation is a simple nonlinear PDE in 1+1 dimensions. It is often used to illustrate some important features of (some) nonlinear PDEs. As we will see, it can be viewed as a nonlinear version of the transport equation. Our main goal in these next two sections is to illustrate a phenomenon not found in linear PDEs: the formation of a singularity in the solution.

Burger's equation is the following PDE for the function u(t,x):

(2.0.7) 
$$\partial_t u + u \partial_x u = 0, \qquad (t, x) \in [0, \infty) \times \mathbb{R}.$$

As we will see, the Cauchy problem (i.e., the initial value problem in which the datum u(0,x) is prescribed) for (2.0.7) is well-posed.

Equation (2.0.7) is a simple example of a nonlinear conservation law. More precisely, the next proposition shows that under suitable assumptions, the spatial  $L^2$  norm of solutions to (2.0.7) is preserved in time.

Proposition 2.0.1 (Burger's equation is a conservation law). Let  $T \geq 0$ , and let u(t,x) be a  $C^1$  solution to (2.0.7) on  $S_T \stackrel{def}{=} [0,T] \times \mathbb{R}$ . Assume that for each fixed  $t \in [0,T]$ , we have that  $\lim_{x \to \pm \infty} u(t,x) = 0$ . Then for  $(t,x) \in S_T$ , we have that

(2.0.8) 
$$\int_{\mathbb{R}} u^2(t,x) \, dx = \int_{\mathbb{R}} u^2(0,x) \, dx,$$

i.e., the spatial  $L^2$  norm of  $u(t,\cdot)$  is preserved in time.

*Proof.* Multiplying both sides of (2.0.7) by u, we deduce that

(2.0.9) 
$$\frac{1}{2}\partial_t(u^2) + \frac{1}{3}\partial_x(u^3) = 0.$$

Integrating (2.0.9) over  $\mathbb{R}$ , using the Fundamental Theorem of calculus and the assumption on the behavior of u(t,x) as  $x \to \pm \infty$ , and "un-differentiating" under the integral, we deduce that

(2.0.10) 
$$\frac{1}{2}\frac{d}{dt} \int_{\mathbb{D}} |u(t,x)|^2 dx = 0.$$

The proposition now follows from (2.0.10).

Notice that (2.0.7) can be viewed as as a transport equation whose speed and direction depend on the solution u itself. As in the case of transport equations, we can define the characteristic curves associated to a solution of (2.0.7).

**Definition 2.0.1.** Let u be a solution of (2.0.7). The characteristic curves associated to u are the solutions to the following system of ODEs:

$$\frac{d}{ds}\gamma^0 = 1,$$

(2.0.11b) 
$$\frac{d}{ds}\gamma^1 = u \circ \gamma = u(\gamma^0(s), \gamma^1(s)).$$

**Remark 2.0.1.** Equation (2.0.11a) shows that  $\gamma^0(s) = s + c$ , where c is a constant. There is no loss of generality in parameterizing the curve with the constant c set equal to 0.

The next two propositions are essential for our analysis of Burger's equation.

Proposition 2.0.2 (Burger solutions are constant along characteristics).  $C^1$  solutions to (2.0.7) are constant along the characteristic curves (2.0.11a) - (2.0.11b).

*Proof.* Using the chain rule and the equations (2.0.7), (2.0.11a) - (2.0.11b), we compute that

$$(2.0.12) \qquad \frac{d}{ds}[u \circ \gamma(s)] = (\partial_t u)|_{\gamma} \frac{d}{ds} \gamma^0 + (\partial_x u)|_{\gamma} \frac{d}{ds} \gamma^1 = (\partial_t u)|_{\gamma} + u|_{\gamma} (\partial_x u)|_{\gamma} = 0.$$

Proposition 2.0.3 (Burger characteristics are straight lines). The characteristic curves (2.0.11a) - (2.0.11b) are straight lines in  $\mathbb{R}^{1+1}$ .

*Proof.* It clearly follows from (2.0.11a) that

(2.0.13) 
$$\frac{d^2}{ds^2}\gamma^0(s) = 0.$$

Furthermore, using the ODE (2.0.11b) and the computation (2.0.12), we compute that

(2.0.14) 
$$\frac{d^2}{ds^2} \gamma^1(s) = \frac{d}{ds} [u \circ \gamma(s)] = 0.$$

We have thus shown that  $\frac{d^2}{ds^2}\gamma^{\mu}(s)=0$  for  $\mu=0,1$ . Thus, the curve  $\gamma$  has **0** acceleration, and is therefore a straight line.

#### 3. "Solving" Burger's equation

Using the propositions from the previous section, will now exhibit an implicit solution to the following initial value problem for Burger's equation:

(3.0.15) 
$$\partial_t u + u \partial_x u = 0, \qquad (t, x) \in [0, \infty) \times \mathbb{R},$$
$$u(0, x) = f(x), \qquad x \in \mathbb{R}.$$

**Theorem 3.1.** Let u be a  $C^1$  solution to (3.0.15), and let (t, x) be a spacetime point. With (t, x) fixed, assume that the implicit equation x = p + f(p)t in the unknown p has a unique solution. Then

$$(3.0.16) u(t,x) = f(p).$$

Proof. Let  $\gamma(s) = (\gamma^0(s), \gamma^1(s))$  denote the characteristic curve passing through the Cartesian (t, x) spacetime point (0, p) when s = 0, i.e.,  $(\gamma^0(0), \gamma^1(0)) = (0, p)$ . According to the ODEs (2.0.11a) - (2.0.11b) and Proposition 2.0.3,  $\gamma(s)$  is a straight line with constant "t/x" slope  $\frac{\dot{\gamma}^0(0)}{\dot{\gamma}^1(0)} = \frac{1}{f(p)}$ . It therefore follows that

$$(3.0.17) \gamma^0(s) = s,$$

(3.0.18) 
$$\gamma^{1}(s) = p + f(p)s.$$

Consequently, by Proposition 2.0.2, we have that

(3.0.19) 
$$u(s, p + f(p)s) = u(0, p) = f(p).$$

Equation (3.0.16) thus follows.

#### 4. Formation of Singularities

Proposition 2.0.1 shows that the spatial  $L^2$  norm of nice solutions to Burger's equation is preserved in time. This conserved quantity suggests that the solution can never grow large and therefore that the solution should exist for all time. However, this intuition is false! The next theorem shows that even though the  $L^2$  norm is preserved, the solution can develop a singularity in finite time, even if the initial datum f is very small and very nice.

Theorem 4.1 (Sharp Characterization of Singularity Formation in Burger's Equation). Let  $f \in C^1(\mathbb{R})$  be initial data for Burger's equation (3.0.15). Then the corresponding solution u(t,x) remains  $C^1$  for all  $(t,x) \in [0,\infty) \times \mathbb{R}$  if and only if  $f'(x) \geq 0$  holds for all  $x \in \mathbb{R}$ .

Proof. Suppose that there exists a point  $x_0$  such that  $f'(x_0) < 0$ . Then there exists a nearby point  $x_1 > x_0$  with  $f(x_1) < f(x_0)$ . Let  $\gamma_{(x_i)}(s)$  denote the characteristic curve passing through the spacetime point  $(0, x_i)$  at s = 0. Then by Proposition 2.0.2,  $u \circ \gamma_{(x_i)}(s) = f(x_i)$  for all  $s \ge 0$ . Furthermore, as in the proof of Theorem 3.1,  $\gamma_{(x_i)}(s)$  traces out a straight line with slope  $(x_i)$  horizontal, t vertical)  $m_i \stackrel{\text{def}}{=} \frac{1}{f(x_i)}$ . Since  $\frac{1}{m_1} < \frac{1}{m_0}$ , it is easy to check that  $\gamma_{(x_0)}$  intersects  $\gamma_{(x_1)}$  at the spacetime point  $(t,x) = \left(\frac{x_1-x_0}{\frac{1}{m_0}-\frac{1}{m_1}},\frac{m_0x_0-m_1x_1}{m_0-m_1}\right)$ . Thus, by Proposition 2.0.2  $u(t,x) = f(x_0)$  and  $u(t,x) = f(x_1)$ , which is a contradiction.

On the other hand, if  $f'(p) \ge 0$  for all p, then for all  $t_0 \ge 0$  and all  $x_0$ , the equation

$$(4.0.20) x_0 = p + f(p)t_0$$

has a unique solution  $p = p_0(t_0, x_0)$  that depends on  $(t_0, x_0)$  in a  $C^1$  fashion. This fact follows from e.g. the implicit function theorem since  $\partial_p(p + f(p)t_0) = 1 + f'(p)t_0 > 0$  (i.e., the right-hand side of (4.0.20) is strictly increasing in p). Therefore, by Theorem 3.1  $u(t_0, x_0) = f \circ p_0(t_0, x_0)$ , and  $u \in C^1([0, \infty) \times \mathbb{R})$ .

**Exercise 4.0.1.** Work through the details to to show that  $\gamma_{(x_0)}$  intersects  $\gamma_{(x_1)}$  at  $(t,x) = \left(\frac{x_1 - x_0}{\frac{1}{m_0} - \frac{1}{m_1}}, \frac{m_0 x_0 - m_1 x_1}{m_0 - m_1}\right)$ .

**Exercise 4.0.2.** Find a reference and review the implicit function theorem.

 $\neg$ 

18.152 Introduction to Partial Differential Equations. Fall 2011

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.
