## **Topic 0 Notes**

Jeremy Orloff

### 0 18.04 course introduction

This class is an adaptation of a class originally taught by Andre Nachbin. He deserves most of the credit for the course design. The topic notes were written by me with many corrections and improvements contributed by Jörn Dunkel. Of course, any responsibility for typos and errors lies entirely with me.

### **0.1** Brief course description

Complex analysis is a beautiful, tightly integrated subject. It revolves around complex analytic functions. These are functions that have a complex derivative. Unlike calculus using real variables, the mere existence of a complex derivative has strong implications for the properties of the function.

Complex analysis is a basic tool in many mathematical theories. By itself and through some of these theories it also has a great many practical applications.

There are a small number of far-reaching theorems that we'll explore in the first part of the class. Along the way, we'll touch on some mathematical and engineering applications of these theorems. The last third of the class will be devoted to a deeper look at applications.

The main theorems are Cauchy's Theorem, Cauchy's integral formula, and the existence of Taylor and Laurent series. Among the applications will be harmonic functions, two dimensional fluid flow, easy methods for computing (seemingly) hard integrals, Laplace transforms, and Fourier transforms with applications to engineering and physics.

### 0.2 Topics needed from prerequisite math classes

We will review these topics as we need them:

- Limits
- Power series
- Vector fields
- Line integrals
- Green's theorem

#### 0.3 Level of mathematical rigor

We will make careful arguments to justify our results. Though, in many places we will allow ourselves to skip some technical details if they get in the way of understanding the main point, but we will note what was left out.

# 0.4 Speed of the class

(Borrowed from R. Rosales 18.04 OCW 1999)

Do not be fooled by the fact things start slow. This is the kind of course where things keep on building up continuously, with new things appearing rather often. Nothing is really very hard, but the total integration can be staggering - and it will sneak up on you if you do not watch it. Or, to express it in mathematically sounding lingo, this course is "locally easy" but "globally hard". That means that if you keep up-to-date with the homework and lectures, and read the class notes regularly, you should not have any problems.

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 1 Notes**

Jeremy Orloff

# 1 Complex algebra and the complex plane

We will start with a review of the basic algebra and geometry of complex numbers. Most likely you have encountered this previously in 18.03 or elsewhere.

#### 1.1 Motivation

The equation  $x^2 = -1$  has no real solutions, yet we know that this equation arises naturally and we want to use its roots. So we make up a new symbol for the roots and call it a complex number.

**Definition.** The symbols  $\pm i$  will stand for the solutions to the equation  $x^2 = -1$ . We will call these new numbers complex numbers. We will also write

$$\sqrt{-1} = \pm i$$

Note: Engineers typically use *j* while mathematicians and physicists use *i*. We'll follow the mathematical custom in 18.04.

The number i is called an **imaginary number**. This is a historical term. These are perfectly valid numbers that don't happen to lie on the real number line. We're going to look at the algebra, geometry and, most important for us, the exponentiation of complex numbers.

Before starting a systematic exposition of complex numbers, we'll work a simple example.

**Example 1.1.** Solve the equation  $z^2 + z + 1 = 0$ .

Solution: We can apply the quadratic formula to get

$$z = \frac{-1 \pm \sqrt{1 - 4}}{2} = \frac{-1 \pm \sqrt{-3}}{2} = \frac{-1 \pm \sqrt{3}\sqrt{-1}}{2} = \frac{-1 \pm \sqrt{3}i}{2}.$$

**Think:** Do you know how to solve quadratic equations by completing the square? This is how the quadratic formula is derived and is well worth knowing!

# 1.2 Fundamental theorem of algebra

One of the reasons for using complex numbers is because allowing complex roots means every polynomial has exactly the expected number of roots. This is called the fundamental theorem of algebra.

**Theorem.** (Fundamental theorem of algebra) A polynomial of degree n has exactly n complex roots (repeated roots are counted with multiplicity).

<sup>&</sup>lt;sup>1</sup>Our motivation for using complex numbers is *not* the same as the historical motivation. Historically, mathematicians were willing to say  $x^2 = -1$  had no solutions. The issue that pushed them to accept complex numbers had to do with the formula for the roots of cubics. Cubics always have at least one real root, and when square roots of negative numbers appeared in this formula, even for the real roots, mathematicians were forced to take a closer look at these (seemingly) exotic objects.


In a few weeks, we will be able to prove this theorem as a remarkably simple consequence of one of our main theorems.

## 1.3 Terminology and basic arithmetic

#### **Definitions**

• Complex numbers are defined as the set of all numbers

$$z = x + yi$$

where x and y are real numbers.

- We denote the set of all complex numbers by **C**. (On the blackboard we will usually write ℂ –this font is called *blackboard bold*.)
- We call x the **real part** of z. This is denoted by x = Re(z).
- We call y the **imaginary part** of z. This is denoted by y = Im(z).

**Important:** The imaginary part of z is a **real number**. It **does not** include the i.

The basic arithmetic operations follow the standard rules. All you have to remember is that  $i^2 = -1$ . We will go through these quickly using some simple examples. It almost goes without saying that in 18.04 it is essential that you become fluent with these manipulations.

- **Addition:** (3+4i)+(7+11i)=10+15i
- **Subtraction:** (3+4i)-(7+11i)=-4-7i
- Multiplication:

$$(3+4i)(7+11i) = 21+28i+33i+44i^2 = -23+61i$$
.

Here we have used the fact that  $44i^2 = -44$ .

Before talking about division and absolute value we introduce a new operation called conjugation. It will prove useful to have a name and symbol for this, since we will use it frequently.

**Complex conjugation** is denoted with a bar and defined by

$$\overline{x+iy} = x - iy.$$

If z = x + iy then its conjugate is  $\overline{z} = x - iy$  and we read this as "z-bar = x - iy".

#### Example 1.2.

$$\overline{3+5i}=3-5i.$$

The following is a very **useful property of conjugation**: If z = x + iy then

$$z\overline{z} = (x + iy)(x - iy) = x^2 + y^2.$$

Note that  $z\overline{z}$  is real. We will use this property in the next example to help with division.

**Example 1.3. (Division.)** Write  $\frac{3+4i}{1+2i}$  in the standard form x+iy.

Solution: We use the useful property of conjugation to clear the denominator:

$$\frac{3+4i}{1+2i} = \frac{3+4i}{1+2i} \cdot \frac{1-2i}{1-2i} = \frac{11-2i}{5} = \frac{11}{5} - \frac{2}{5}i.$$

In the next section we will discuss the geometry of complex numbers, which gives some insight into the meaning of the magnitude of a complex number. For now we just give the definition.

**Definition.** The magnitude of the complex number x + iy is defined as

$$|z| = \sqrt{x^2 + y^2}.$$

The magnitude is also called the **absolute value**, **norm** or **modulus**.

**Example 1.4.** The norm of  $3 + 5i = \sqrt{9 + 25} = \sqrt{34}$ .

**Important.** The norm is the sum of  $x^2$  and  $y^2$ . It does not include the i and is therefore always positive.

# 1.4 The complex plane

### 1.4.1 The geometry of complex numbers

Because it takes two numbers x and y to describe the complex number z = x + iy we can visualize complex numbers as points in the xy-plane. When we do this we call it the complex plane. Since x is the real part of z we call the x-axis the real axis. Likewise, the y-axis is the imaginary axis.

### 1.4.2 The triangle inequality

The triangle inequality says that for a triangle the sum of the lengths of any two legs is greater than the length of the third leg.

Triangle inequality: |AB| + |BC| > |AC|

For complex numbers the triangle inequality translates to a statement about complex magnitudes. Precisely: for complex numbers  $z_1$ ,  $z_2$ 

$$|z_1| + |z_2| \ge |z_1 + z_2|$$

with equality only if one of them is 0 or if  $arg(z_1) = arg(z_2)$ . This is illustrated in the following figure.

Triangle inequality:  $|z_1| + |z_2| \ge |z_1 + z_2|$ 

We get equality only if  $z_1$  and  $z_2$  are on the same ray from the origin, i.e. they have the same argument.

#### 1.5 Polar coordinates

In the figures above we have marked the length r and polar angle  $\theta$  of the vector from the origin to the point z = x + iy. These are the same polar coordinates you saw in 18.02 and 18.03. There are a number of synonyms for both r and  $\theta$ 

$$r = |z| = \text{magnitude} = \text{length} = \text{norm} = \text{absolute value} = \text{modulus}$$
  
 $\theta = \arg(z) = \text{argument of } z = \text{polar angle of } z$ 

As in 18.02 you should be able to visualize polar coordinates by thinking about the distance r from the origin and the angle  $\theta$  with the x-axis.

**Example 1.5.** Let's make a table of z, r and  $\theta$  for some complex numbers. Notice that  $\theta$  is not uniquely defined since we can always add a multiple of  $2\pi$  to  $\theta$  and still be at the same point in the plane.

$$z = a + bi$$
  $r$   $\theta$   
1 0,  $2\pi$ ,  $4\pi$ , ... Argument = 0, means  $z$  is along the  $x$ -axis  
 $i$  1  $\pi/2$ ,  $\pi/2 + 2\pi$  ... Argument =  $\pi/2$ , means  $z$  is along the  $y$ -axis  
 $1 + i$   $\sqrt{2}$   $\pi/4$ ,  $\pi/4 + 2\pi$  ... Argument =  $\pi/4$ , means  $z$  is along the ray at 45° to the  $x$ -axis

When we want to be clear which value of  $\theta$  is meant, we will specify a **branch** of arg. For example,  $0 \le \theta < 2\pi$  or  $-\pi < \theta \le \pi$ . This will be discussed in much more detail in the coming weeks. Keeping careful track of the branches of arg will turn out to be one of the key requirements of complex analysis.

#### 1.6 Euler's Formula

Euler's (pronounced 'oilers') formula connects complex exponentials, polar coordinates, and sines and cosines. It turns messy trig identities into tidy rules for exponentials. We will use it a lot. The formula is the following:

$$e^{i\theta} = \cos(\theta) + i\sin(\theta). \tag{1}$$

There are many ways to approach Euler's formula. Our approach is to simply take Equation 1 as the definition of complex exponentials. This is legal, but does not show that it's a good definition. To do that we need to show the  $e^{i\theta}$  obeys all the rules we expect of an exponential. To do that we go systematically through the properties of exponentials and check that they hold for complex exponentials.

# 1.6.1 $e^{i\theta}$ behaves like a true exponential

**P1.**  $e^{it}$  differentiates as expected:

$$\frac{de^{it}}{dt} = ie^{it}.$$

*Proof.* This follows directly from the definition:

$$\frac{de^{it}}{dt} = \frac{d}{dt}(\cos(t) + i\sin(t)) = -\sin(t) + i\cos(t) = i(\cos(t) + i\sin(t)) = ie^{it}.$$

**P2.** 
$$e^{i \cdot 0} = 1$$
.

*Proof.* 
$$e^{i \cdot 0} = \cos(0) + i \sin(0) = 1$$
.

**P3.** The usual rules of exponents hold:

$$e^{ia}e^{ib} = e^{i(a+b)}$$
.

*Proof.* This relies on the cosine and sine addition formulas.

$$e^{ia} \cdot e^{ib} = (\cos(a) + i\sin(a)) \cdot (\cos(b) + i\sin(b))$$
  
= \cos(a) \cos(b) - \sin(a) \sin(b) + i (\cos(a) \sin(b) + \sin(a) \cos(b))  
= \cos(a + b) + i \sin(a + b) = e^{i(a+b)}.

**P4.** The definition of  $e^{i\theta}$  is consistent with the power series for  $e^x$ .

*Proof.* To see this we have to recall the power series for  $e^x$ ,  $\cos(x)$  and  $\sin(x)$ . They are

$$e^{x} = 1 + x + \frac{x^{2}}{2!} + \frac{x^{3}}{3!} + \frac{x^{4}}{4!} + \dots$$

$$\cos(x) = 1 - \frac{x^{2}}{2!} + \frac{x^{4}}{4!} - \frac{x^{6}}{6!} + \dots$$

$$\sin(x) = x - \frac{x^{3}}{3!} + \frac{x^{5}}{5!} + \dots$$

Now we can write the power series for  $e^{i\theta}$  and then split it into the power series for sine and cosine:

$$e^{i\theta} = \sum_{0}^{\infty} \frac{(i\theta)^n}{n!}$$

$$= \sum_{0}^{\infty} (-1)^k \frac{\theta^{2k}}{(2k)!} + i \sum_{0}^{\infty} (-1)^k \frac{\theta^{2k+1}}{(2k+1)!}$$

$$= \cos(\theta) + i \sin(\theta).$$

So the Euler formula definition is consistent with the usual power series for  $e^x$ .

Properties **P1-P4** should convince you that  $e^{i\theta}$  behaves like an exponential.

#### 1.6.2 Complex exponentials and polar form

Now let's turn to the relation between polar coordinates and complex exponentials.

Suppose z = x + iy has polar coordinates r and  $\theta$ . That is, we have  $x = r\cos(\theta)$  and  $y = r\sin(\theta)$ . Thus, we get the important relationship

$$z = x + iy = r\cos(\theta) + ir\sin(\theta) = r(\cos(\theta) + i\sin(\theta)) = re^{i\theta}$$
.

This is so important you shouldn't proceed without understanding. We also record it without the intermediate equation.

$$z = x + iy = re^{i\theta}. (2)$$

Because r and  $\theta$  are the polar coordinates of (x, y) we call  $z = re^{i\theta}$  the polar form of z.

Let's now verify that magnitude, argument, conjugate, multiplication and division are easy in polar form

Magnitude.  $|e^{i\theta}| = 1$ .

Proof.

$$|e^{i\theta}| = |\cos(\theta) + i\sin(\theta)| = \sqrt{\cos^2(\theta) + \sin^2(\theta)} = 1.$$

In words, this says that  $e^{i\theta}$  is always on the unit circle – this is useful to remember!

Likewise, if  $z = re^{i\theta}$  then |z| = r. You can calculate this, but it should be clear from the definitions: |z| is the distance from z to the origin, which is exactly the same definition as for r.

Argument. If  $z = re^{i\theta}$  then  $arg(z) = \theta$ .

*Proof.* This is again the definition: the argument is the polar angle  $\theta$ .

Conjugate.  $\overline{(re^{i\theta})} = re^{-i\theta}$ .

Proof.

$$\overline{(re^{i\theta})} = \overline{r(\cos(\theta) + i\sin(\theta))} = r(\cos(\theta) - i\sin(\theta)) = r(\cos(-\theta) + i\sin(-\theta)) = re^{-i\theta}.$$

In words: complex conjugation changes the sign of the argument.

Multiplication. If  $z_1 = r_1 e^{i\theta_1}$  and  $z_2 = r_2 e^{i\theta_2}$  then

$$z_1 z_2 = r_1 r_2 e^{i(\theta_1 + \theta_2)}$$
.

This is what mathematicians call trivial to see, just write the multiplication down. In words, the formula says the for  $z_1z_2$  the magnitudes multiply and the arguments add.

Division. Again it's trivial that

$$\frac{r_1 e^{i\theta_1}}{r_2 e^{i\theta_2}} = \frac{r_1}{r_2} e^{i(\theta_1 - \theta_2)}.$$

**Example 1.6.** (Multiplication by 2i) Here's a simple but important example. By looking at the graph we see that the number 2i has magnitude 2 and argument  $\pi/2$ . So in polar coordinates it equals  $2e^{i\pi/2}$ . This means that multiplication by 2i multiplies lengths by 2 and adds  $\pi/2$  to arguments, i.e. rotates by  $90^{\circ}$ . The effect is shown in the figures below

|2i| = 2,  $arg(2i) = \pi/2$ 

Multiplication by 2i rotates by  $\pi/2$  and scales by 2

**Example 1.7.** (Raising to a power) Let's compute 
$$(1+i)^6$$
 and  $\left(\frac{1+i\sqrt{3}}{2}\right)^3$ 

Solution: 1 + i has magnitude  $= \sqrt{2}$  and  $\arg = \pi/4$ , so  $1 + i = \sqrt{2}e^{i\pi/4}$ . Raising to a power is now easy:

$$(1+i)^6 = \left(\sqrt{2}e^{i\pi/4}\right)^6 = 8e^{6i\pi/4} = 8e^{3i\pi/2} = -8i.$$

Similarly, 
$$\frac{1+i\sqrt{3}}{2} = e^{i\pi/3}$$
, so  $\left(\frac{1+i\sqrt{3}}{2}\right)^3 = (1 \cdot e^{i\pi/3})^3 = e^{i\pi} = -1$ 

#### 1.6.3 Complexification or complex replacement

In the next example we will illustrate the technique of complexification or complex replacement. This can be used to simplify a trigonometric integral. It will come in handy when we need to compute certain integrals.

**Example 1.8.** Use complex replacement to compute

$$I = \int e^x \cos(2x) \, dx.$$

Solution: We have Euler's formula

$$e^{2ix} = \cos(2x) + i\sin(2x),$$

so  $cos(2x) = Re(e^{2ix})$ . The complex replacement trick is to replace cos(2x) by  $e^{2ix}$ . We get (justification below)

$$I_c = \int e^x \cos 2x + i e^x \sin 2x \, dx, \qquad I = \text{Re}(I_c).$$

Computing  $I_c$  is straightforward:

$$I_c = \int e^x e^{i2x} dx = \int e^{x(1+2i)} dx = \frac{e^{x(1+2i)}}{1+2i}.$$

Here we will do the computation first in rectangular coordinates. In applications, for example throughout 18.03, polar form is often preferred because it is easier and gives the answer in a more useable form.

$$I_c = \frac{e^{x(1+2i)}}{1+2i} \cdot \frac{1-2i}{1-2i}$$

$$= \frac{e^x(\cos(2x) + i \sin(2x))(1-2i)}{5}$$

$$= \frac{1}{5}e^x(\cos(2x) + 2\sin(2x) + i(-2\cos(2x) + \sin(2x)))$$

So,

$$I = \text{Re}(I_c) = \frac{1}{5}e^x(\cos(2x) + 2\sin(2x)).$$

**Justification of complex replacement.** The trick comes by cleverly adding a new integral to I as follows. Let  $J = \int e^x \sin(2x) dx$ . Then we let

$$I_c = I + iJ = \int e^x (\cos(2x) + i\sin(2x)) dx = \int e^x e^{2ix} dx.$$

Clearly, by construction,  $Re(I_c) = I$  as claimed above.

Alternative using polar coordinates to simplify the expression for  $I_c$ :

In polar form, we have  $1+2i=r\mathrm{e}^{i\phi}$ , where  $r=\sqrt{5}$  and  $\phi=\arg(1+2i)=\tan^{-1}(2)$  in the first quadrant. Then:

$$I_c = \frac{e^{x(1+2i)}}{\sqrt{5}e^{i\phi}} = \frac{e^x}{\sqrt{5}}e^{i(2x-\phi)} = \frac{e^x}{\sqrt{5}}(\cos(2x-\phi) + i\sin(2x-\phi)).$$

Thus,

$$I = \operatorname{Re}(I_c) = \frac{e^x}{\sqrt{5}}\cos(2x - \phi).$$

#### **1.6.4** *N*th roots

We are going to need to be able to find the *n*th roots of complex numbers, i.e., solve equations of the form

$$z^N = c$$
.

where c is a given complex number. This can be done most conveniently by expressing c and z in polar form,  $c = Re^{i\phi}$  and  $z = re^{i\theta}$ . Then, upon substituting, we have to solve

$$r^N e^{iN\theta} = Re^{i\phi}$$

For the complex numbers on the left and right to be equal, their magnitudes must be the same and their arguments can only differ by an integer multiple of  $2\pi$ . This gives

$$r = R^{1/N}$$
  $N\theta = \phi + 2\pi n$ , where  $n = 0, \pm 1, \pm 2, ...$ 

Solving for  $\theta$ , we have

$$\theta = \frac{\phi}{N} + \frac{2\pi n}{N}.$$

### **Example 1.9.** Find all 5 fifth roots of 2.

Solution: For c = 2, we have R = 2 and  $\phi = 0$ , so the fifth roots of 2 are

$$z_n = 2^{1/5} e^{2n\pi i/5}$$
, where  $n = 0, \pm 1, \pm 2, ...$ 

Looking at the right hand side we see that for n = 5 we have  $2^{1/5}e^{2\pi i}$  which is exactly the same as the root when n = 0, i.e.  $2^{1/5}e^{0i}$ . Likewise n = 6 gives exactly the same root as n = 1, and so on. This means, we have 5 different roots corresponding to n = 0, 1, 2, 3, 4.

$$z_n = 2^{1/5}, \ 2^{1/5}e^{2\pi i/5}, \ 2^{1/5}e^{4\pi i/5}, \ 2^{1/5}e^{6\pi i/5}, \ 2^{1/5}e^{8\pi i/5}$$

Similarly we can say that in general  $c = Re^{i\phi}$  has N distinct Nth roots:

$$z_n = r^{1/N} e^{i\phi/N + i2\pi(n/N)}$$
 for  $n = 0, 1, 2, ..., N - 1$ .

## **Example 1.10.** Find the 4 fourth roots of 1.

Solution: We need to solve  $z^4 = 1$ , so  $\phi = 0$ . So the 4 distinct fourth roots are in polar form

$$z_n = 1$$
,  $e^{i\pi/2}$ ,  $e^{i\pi}$ ,  $e^{i3\pi/2}$ 

and in Cartesian representation

$$z_n = 1, i, -1, -i.$$

### **Example 1.11.** Find the 3 cube roots of -1.

Solution:  $z^2 = -1 = e^{i\pi + i2\pi n}$ . So,  $z_n = e^{i\pi/3 + i2\pi(n/3)}$  and the 3 cube roots are  $e^{i\pi/3}$ ,  $e^{i\pi}$ ,  $e^{i5\pi/3}$ . Since  $\pi/3$  radians is 60° we can simpify:

$$e^{i\pi/3} = \cos(\pi/3) + i\sin(\pi/3) = \frac{1}{2} + i\frac{\sqrt{3}}{2}$$
  $\Rightarrow$   $z_n = -1, \frac{1}{2} \pm i\frac{\sqrt{3}}{2}$ 

#### **Example 1.12.** Find the 5 fifth roots of 1 + i.

Solution: 
$$z^5 = 1 + i = \sqrt{2}e^{i(\pi/4 + 2n\pi)}$$
, for  $n = 0, 1, 2, ...$  So, the 5 fifth roots are 
$$2^{1/10}e^{i\pi/20} \quad 2^{1/10}e^{i9\pi/20} \quad 2^{1/10}e^{i17\pi/20} \quad 2^{1/10}e^{i25\pi/20} \quad 2^{1/10}e^{i33\pi/20}$$

Using a calculator we could write these numerically as a + bi, but there is no easy simplification.

**Example 1.13.** We should check that our technique works as expected for a simple problem. Find the 2 square roots of 4.

Solution:  $z^2 = 4e^{i2\pi n}$ . So,  $z_n = 2e^{i\pi n}$ , with n = 0, 1. So the two roots are  $2e^0 = 2$  and  $2e^{i\pi} = -2$  as expected!

### 1.6.5 The geometry of Nth roots

Looking at the examples above we see that roots are always spaced evenly around a circle centered at the origin. For example, the fifth roots of 1 + i are spaced at increments of  $2\pi/5$  radians around the circle of radius  $2^{1/5}$ .

Note also that the roots of real numbers always come in conjugate pairs.

### 1.7 Inverse Euler formula

Euler's formula gives a complex exponential in terms of sines and cosines. We can turn this around to get the inverse Euler formulas.

Euler's formula says:

$$e^{it} = \cos(t) + i\sin(t)$$
 and  $e^{-it} = \cos(t) - i\sin(t)$ .

By adding and subtracting we get:

$$\cos(t) = \frac{e^{it} + e^{-it}}{2} \quad \text{and} \quad \sin(t) = \frac{e^{it} - e^{-it}}{2i}.$$

Please take note of these formulas we will use them frequently!

### 1.8 de Moivre's formula

For positive integers *n* we have de Moivre's formula:

$$(\cos(\theta) + i\sin(\theta))^n = \cos(n\theta) + i\sin(n\theta)$$

*Proof.* This is a simple consequence of Euler's formula:

$$(\cos(\theta) + i\sin(\theta))^n = (e^{i\theta})^n = e^{in\theta} = \cos(n\theta) + i\sin(n\theta).$$

The reason this simple fact has a name is that historically de Moivre stated it before Euler's formula was known. Without Euler's formula there is not such a simple proof.

# 1.9 Representing complex multiplication as matrix multiplication

Consider two complex numbers  $z_1 = a + bi$  and  $z_2 = c + di$  and their product

$$z_1 z_2 = (a+bi)(c+id) = (ac-bd) + i(bc+ad) =: w$$
 (3)

Now let's define two matrices

$$Z_1 = \begin{bmatrix} a & -b \\ b & a \end{bmatrix} \qquad Z_2 = \begin{bmatrix} c & -d \\ d & c \end{bmatrix}$$

Note that these matrices store the same information as  $z_1$  and  $z_2$ , respectively. Let's compute their matrix product

$$Z_1Z_2 = \begin{bmatrix} a & -b \\ b & a \end{bmatrix} \begin{bmatrix} c & -d \\ d & c \end{bmatrix} = \begin{bmatrix} ac-bd & -(bc+ad) \\ bc+ad & ac-bd \end{bmatrix} := W.$$

Comparing W just above with w in Equation 3, we see that W is indeed the matrix corresponding to the complex number  $w = z_1 z_2$ . Thus, we can represent any complex number z equivalently by the matrix

$$Z = \begin{bmatrix} \operatorname{Re} z & -\operatorname{Im} z \\ \operatorname{Im} z & \operatorname{Re} z \end{bmatrix}$$

and complex multiplication then simply becomes matrix multiplication. Further note that we can write

$$Z = \operatorname{Re} z \begin{bmatrix} 1 & 0 \\ 0 & 1 \end{bmatrix} + \operatorname{Im} z \begin{bmatrix} 0 & -1 \\ 1 & 0 \end{bmatrix},$$

i.e., the imaginary unit *i* corresponds to the matrix  $\begin{bmatrix} 0 & -1 \\ 1 & 0 \end{bmatrix}$  and  $i^2 = -1$  becomes

$$\begin{bmatrix} 0 & -1 \\ 1 & 0 \end{bmatrix} \begin{bmatrix} 0 & -1 \\ 1 & 0 \end{bmatrix} = - \begin{bmatrix} 1 & 0 \\ 0 & 1 \end{bmatrix}.$$

**Polar form (decomposition).** Writing  $z = re^{i\theta} = r(\cos\theta + i\sin\theta)$ , we find

$$Z = r \begin{bmatrix} \cos \theta & -\sin \theta \\ \sin \theta & \cos \theta \end{bmatrix} = \begin{bmatrix} r & 0 \\ 0 & r \end{bmatrix} \begin{bmatrix} \cos \theta & -\sin \theta \\ \sin \theta & \cos \theta \end{bmatrix}$$

corresponding to a stretch factor r multiplied by a 2D rotation matrix. In particular, multiplication by i corresponds to the rotation with angle  $\theta = \pi/2$  and r = 1.

We will not make a lot of use of the matrix representation of complex numbers, but later it will help us remember certain formulas and facts.

### 1.10 The exponential function

We have Euler's formula:  $e^{i\theta} = \cos(\theta) + i\sin(\theta)$ . We can extend this to the complex exponential function  $e^z$ .

**Definition.** For z = x + iy the complex exponential function is defined as

$$e^z = e^{x+iy} = e^x e^{iy} = e^x (\cos(y) + i\sin(y)).$$

In this definition  $e^x$  is the usual exponential function for a real variable x.

It is easy to see that all the usual rules of exponents hold:

- 1.  $e^0 = 1$
- 2.  $e^{z_1+z_2} = e^{z_1}e^{z_2}$
- 3.  $(e^z)^n = e^{nz}$  for positive integers n.
- 4.  $(e^z)^{-1} = e^{-z}$
- 5.  $e^z \neq 0$

It will turn out that the property  $\frac{de^z}{dz} = e^z$  also holds, but we can't prove this yet because we haven't defined what we mean by the complex derivative  $\frac{d}{dz}$ .

Here are some more simple, but extremely important properties of  $e^z$ . You should become fluent in their use and know how to prove them.

6.  $|e^{i\theta}| = 1$ 

Proof.

$$|e^{i\theta}| = |\cos(\theta) + i\sin(\theta)| = \sqrt{\cos^2(\theta) + \sin^2(\theta)} = 1.$$

7.  $|e^{x+iy}| = e^x$  (as usual z = x + iy and x, y are real).

*Proof.* You should be able to supply this. If not: ask a teacher or TA.

8. The path  $e^{it}$  for  $0 < t < \infty$  wraps counterclockwise around the unit circle. It does so infinitely many times. This is illustrated in the following picture.

The map  $t \to e^{it}$  wraps the real axis around the unit circle.

## 1.11 Complex functions as mappings

A complex function w = f(z) is hard to graph because it takes 4 dimensions: 2 for z and 2 for w. So, to visualize them we will think of complex functions as mappings. That is we will think of w = f(z) as taking a point in the complex z-plane and mapping (sending) it to a point in the complex w-plane.

We will use the following terms and symbols to discuss mappings.

- A function w = f(z) will also be called a mapping of z to w.
- Alternatively we will write  $z \mapsto w$  or  $z \mapsto f(z)$ . This is read as "z maps to w".
- We will say that "w is the image of z under the mapping" or more simply "w is the image of z".

• If we have a set of points in the z-plane we will talk of the image of that set under the mapping. For example, under the mapping  $z \mapsto iz$  the image of the imaginary z-axis is the real w-axis.

The image of the imaginary axis under  $z \mapsto iz$ .

Next, we'll illustrate visualizing mappings with some examples:

**Example 1.14.** The mapping  $w = z^2$ . We visualize this by putting the z-plane on the left and the w-plane on the right. We then draw various curves and regions in the z-plane and the corresponding image under  $z^2$  in the w-plane.

In the first figure we show that rays from the origin are mapped by  $z^2$  to rays from the origin. We see that

- 1. The ray  $L_2$  at  $\pi/4$  radians is mapped to the ray  $f(L_2)$  at  $\pi/2$  radians.
- 2. The rays  $L_2$  and  $L_6$  are both mapped to the same ray. This is true for each pair of diametrically opposed rays.
- 3. A ray at angle  $\theta$  is mapped to the ray at angle  $2\theta$ .

 $f(z) = z^2$  maps rays from the origin to rays from the origin.

The next figure gives another view of the mapping. Here we see vertical stripes in the first quadrant are mapped to parabolic stripes that live in the first and second quadrants.

 $z^2 = (x^2 - y^2) + i2xy$  maps vertical lines to left facing parabolas.

The next figure is similar to the previous one, except in this figure we look at vertical stripes in both the first and second quadrants. We see that they map to parabolic stripes that live in all four quadrants.

 $f(z) = z^2$  maps the first two quadrants to the entire plane.

The next figure shows the mapping of stripes in the first and fourth quadrants. The image map is identical to the previous figure. This is because the fourth quadrant is minus the second quadrant, but  $z^2 = (-z)^2$ .

Vertical stripes in quadrant 4 are mapped identically to vertical stripes in quadrant 2.

Simplified view of the first quadrant being mapped to the first two quadrants.

Simplified view of the first two quadrants being mapped to the entire plane.

**Example 1.15.** The mapping  $w = e^z$ . Here we present a series of plots showing how the exponential function maps z to w.

Notice that vertical lines are mapped to circles and horizontal lines to rays from the origin.

The next four figures all show essentially the same thing: the exponential function maps horizontal stripes to circular sectors. Any horizontal stripe of width  $2\pi$  gets mapped to the entire plane minus the origin,

Because the plane minus the origin comes up frequently we give it a name:

**Definition.** The punctured plane is the complex plane minus the origin. In symbols we can write it as  $C - \{0\}$  or  $C/\{0\}$ .

The horizontal strip  $0 \le y < 2\pi$  is mapped to the punctured plane

The horizontal strip  $-\pi < y \le \pi$  is mapped to the punctured plane

Simplified view showing  $e^z$  maps the horizontal stripe  $0 \le y < 2\pi$  to the punctured plane.

Simplified view showing  $e^z$  maps the horizontal stripe  $-\pi < y \le \pi$  to the punctured plane.

### **1.12** The function arg(z)

#### 1.12.1 Many-to-one functions

The function  $f(z) = z^2$  maps  $\pm z$  to the same value, e.g. f(2) = f(-2) = 4. We say that f(z) is a 2-to-1 function. That is, it maps 2 different points to each value. (Technically, it only maps one point to 0, but we will gloss over that for now.) Here are some other examples of many-to-one functions.

**Example 1.16.**  $w = z^3$  is a 3-to-1 function. For example, 3 different z values get mapped to w = 1:

$$1^{3} = \left(\frac{-1 + \sqrt{3}i}{2}\right)^{3} = \left(\frac{-1 - \sqrt{3}i}{2}\right)^{3} = 1$$

**Example 1.17.** The function  $w = e^z$  maps infinitely many points to each value. For example

$$e^{0} = e^{2\pi i} = e^{4\pi i} = \dots = e^{2n\pi i} = \dots = 1$$

$$e^{i\pi/2} = e^{i\pi/2 + 2\pi i} = e^{i\pi/2 + 4\pi i} = \dots = e^{i\pi/2 + 2n\pi i} = \dots = i$$

In general,  $e^{z+2n\pi i}$  has the same value for every integer n.

## **1.12.2** Branches of arg(z)

**Important note.** You should master this section. Branches of arg(z) are the key that really underlies all our other examples. Fortunately it is reasonably straightforward.

The key point is that the argument is only defined up to multiples of  $2\pi i$  so every z produces infinitely many values for  $\arg(z)$ . Because of this we will say that  $\arg(z)$  is a multiple-valued function.

Note. In general a function should take just one value. What that means in practice is that whenever we use such a function will have to be careful to specify which of the possible values we mean. This is known as specifying a branch of the function.

**Definition.** By a branch of the argument function we mean a choice of range so that it becomes single-valued. By specifying a branch we are saying that we will take the single value of arg(z) that lies in the branch.

Let's look at several different branches to understand how they work:

(i) If we specify the branch as  $0 \le \arg(z) < 2\pi$  then we have the following arguments.

$$arg(1) = 0$$
;  $arg(i) = \pi/2$ ;  $arg(-1) = \pi$ ;  $arg(-i) = 3\pi/2$ 

This branch and these points are shown graphically in Figure (i) below.

Figure (i): The branch  $0 \le \arg(z) < 2\pi$  of  $\arg(z)$ .

Notice that if we start at z = 1 on the positive real axis we have  $\arg(z) = 0$ . Then  $\arg(z)$  increases as we move counterclockwise around the circle. The argument is continuous until we get back to the positive real axis. There it jumps from almost  $2\pi$  back to 0.

There is no getting around (no pun intended) this discontinuity. If we need arg(z) to be continuous we will need to remove (cut) the points of discontinuity out of the domain. The branch cut for this branch of arg(z) is shown as a thick orange line in the figure. If we make the branch cut then the domain for arg(z) is the plane minus the cut, i.e. we will only consider arg(z) for z not on the cut.

For future reference you should note that, on this branch, arg(z) is continuous near the negative real axis, i.e. the arguments of nearby points are close to each other.

(ii) If we specify the branch as  $-\pi < \arg(z) \le \pi$  then we have the following arguments:

$$arg(1) = 0$$
;  $arg(i) = \pi/2$ ;  $arg(-1) = \pi$ ;  $arg(-i) = -\pi/2$ 

This branch and these points are shown graphically in Figure (ii) below.

Figure (ii): The branch  $-\pi < \arg(z) \le \pi$  of  $\arg(z)$ .

Compare Figure (ii) with Figure (i). The values of arg(z) are the same in the upper half plane, but in the lower half plane they differ by  $2\pi$ .

For this branch the branch cut is along the negative real axis. As we cross the branch cut the value of arg(z) jumps from  $\pi$  to something close to  $-\pi$ .

(iii) Figure (iii) shows the branch of  $\arg(z)$  with  $\pi/4 \le \arg(z) < 9\pi/4$ .

Figure (iii): The branch  $\pi/4 \le \arg(z) < 9\pi/4$  of  $\arg(z)$ .

Notice that on this branch arg(z) is continuous at both the positive and negative real axes. The jump of  $2\pi$  occurs along the ray at angle  $\pi/4$ .

(iv) Obviously, there are many many possible branches. For example,

$$42 < \arg(z) < 42 + 2\pi$$
.

(v) We won't make use of this in 18.04, but, in fact, the branch cut doesn't have to be a straight line. Any curve that goes from the origin to infinity will do. The argument will be continuous except for

a jump by  $2\pi$  when z crosses the branch cut.

### **1.12.3** The principal branch of arg(z)

Branch (ii) in the previous section is singled out and given a name:

**Definition.** The branch  $-\pi < \arg(z) \le \pi$  is called the principal branch of  $\arg(z)$ . We will use the notation  $\operatorname{Arg}(z)$  (capital A) to indicate that we are using the principal branch. (Of course, in cases where we don't want there to be any doubt we will say explicitly that we are using the principal branch.)

### **1.12.4** Continuity of arg(z)

The examples above show that there is no getting around the jump of  $2\pi$  as we cross the branch cut. This means that when we need  $\arg(z)$  to be continuous we will have to restrict its domain to the plane minus a branch cut.

# 1.13 Concise summary of branches and branch cuts

We discussed branches and branch cuts for arg(z). Before talking about log(z) and its branches and branch cuts we will give a short review of what these terms mean. You should probably scan this section now and then come back to it after reading about log(z).

Consider the function w = f(z). Suppose that z = x + iy and w = u + iv.

**Domain.** The domain of f is the set of z where we are allowed to compute f(z).

**Range.** The range (image) of f is the set of all f(z) for z in the domain, i.e. the set of all w reached by f.

**Branch.** For a multiple-valued function, a branch is a choice of range for the function. We choose the range to exclude all but one possible value for each element of the domain.

**Branch cut.** A branch cut removes (cuts) points out of the domain. This is done to remove points where the function is discontinuous.

# **1.14** The function log(z)

Our goal in this section is to define the log function. We want  $\log(z)$  to be the inverse of  $e^z$ . That is, we want  $e^{\log(z)} = z$ . We will see that  $\log(z)$  is multiple-valued, so when we use it we will have to specify a branch.

We start by looking at the simplest example which illustrates that log(z) is multiple-valued.

#### **Example 1.18.** Find log(1).

Solution: We know that  $e^0 = 1$ , so log(1) = 0 is one answer.

We also know that  $e^{2\pi i} = 1$ , so  $\log(1) = 2\pi i$  is another possible answer. In fact, we can choose any multiple of  $2\pi i$ :

 $log(1) = 2n\pi i$ , where *n* is any integer

This example leads us to consider the polar form for z as we try to define  $\log(z)$ . If  $z = re^{i\theta}$  then one possible value for  $\log(z)$  is

$$\log(z) = \log(re^{i\theta}) = \log(r) + i\theta,$$

here  $\log(r)$  is the usual logarithm of a real positive number. For completeness we show explicitly that with this definition  $e^{\log(z)} = z$ :

$$e^{\log(z)} = e^{\log(r) + i\theta} = e^{\log(r)}e^{i\theta} = re^{i\theta} = z$$

Since r = |z| and  $\theta = \arg(z)$  we have arrived at our definition.

**Definition.** The function log(z) is defined as

$$\log(z) = \log(|z|) + i \arg(z),$$

where log(|z|) is the usual natural logarithm of a positive real number.

#### Remarks.

- 1. Since arg(z) has infinitely many possible values, so does log(z).
- 2.  $\log(0)$  is not defined. (Both because  $\arg(0)$  is not defined and  $\log(|0|)$  is not defined.)
- 3. Choosing a branch for arg(z) makes log(z) single valued. The usual terminology is to say we have chosen a branch of the log function.
- 4. The principal branch of log comes from the principal branch of arg. That is,

$$\log(z) = \log(|z|) + i \arg(z)$$
, where  $-\pi < \arg(z) \le \pi$  (principal branch).

**Example 1.19.** Compute all the values of log(i). Specify which one comes from the principal branch.

Solution: We have that |i| = 1 and  $arg(i) = \frac{\pi}{2} + 2n\pi$ , so

$$\log(i) = \log(1) + i\frac{\pi}{2} + i2n\pi = i\frac{\pi}{2} + i2n\pi$$
, where *n* is any integer.

The principal branch of  $\arg(z)$  is between  $-\pi$  and  $\pi$ , so  $\operatorname{Arg}(i) = \pi/2$ . Therefore, the value of  $\log(i)$  from the principal branch is  $i\pi/2$ .

**Example 1.20.** Compute all the values of  $\log(-1 - \sqrt{3}i)$ . Specify which one comes from the principal branch.

Solution: Let  $z = -1 - \sqrt{3}i$ . Then |z| = 2 and in the principal branch  $\text{Arg}(z) = -2\pi/3$ . So all the values of  $\log(z)$  are

$$\log(z) = \log(2) - i\frac{2\pi}{3} + i2n\pi.$$

The value from the principal branch is  $\log(z) = \log(2) - i2\pi/3$ .

### 1.14.1 Figures showing $w = \log(z)$ as a mapping

The figures below show different aspects of the mapping given by log(z).

In the first figure we see that a point z is mapped to (infinitely) many values of w. In this case we show  $\log(1)$  (blue dots),  $\log(4)$  (red dots),  $\log(i)$  (blue cross), and  $\log(4i)$  (red cross). The values in the principal branch are inside the shaded region in the w-plane. Note that the values of  $\log(z)$  for a given z are placed at intervals of  $2\pi i$  in the w-plane.

Mapping  $\log(z)$ :  $\log(1)$ ,  $\log(4)$ ,  $\log(i)$ ,  $\log(4i)$ 

The next figure illustrates that the principal branch of log maps the punctured plane to the horizontal strip  $-\pi < \text{Im}(w) \le \pi$ . We again show the values of  $\log(1)$ ,  $\log(4)$ ,  $\log(i)$  and  $\log(4i)$ . Since we've chosen a branch, there is only one value shown for each log.

Mapping log(z): the principal branch and the punctured plane

The third figure shows how circles centered on 0 are mapped to vertical lines, and rays from the origin are mapped to horizontal lines. If we restrict ourselves to the principal branch the circles are

mapped to vertical line segments and rays to a single horizontal line in the principal (shaded) region of the w-plane.

Mapping log(z): mapping circles and rays

### 1.14.2 Complex powers

We can use the log function to define complex powers.

**Definition.** Let z and a be complex numbers then the power  $z^a$  is defined as

$$z^a = e^{a \log(z)}$$
.

This is generally multiple-valued, so to specify a single value requires choosing a branch of log(z).

**Example 1.21.** Compute all the values of  $\sqrt{2i}$ . Give the value associated to the principal branch of  $\log(z)$ .

Solution: We have

$$\log(2i) = \log(2e^{\frac{i\pi}{2}}) = \log(2) + i\frac{\pi}{2} + i2n\pi.$$

So.

$$\sqrt{2i} = (2i)^{1/2} = e^{\frac{\log(2i)}{2}} = e^{\frac{\log(2i)}{2} + \frac{i\pi}{4} + in\pi} = \sqrt{2}e^{\frac{i\pi}{4} + in\pi}.$$

(As usual *n* is an integer.) As we saw earlier, this only gives two distinct values. The principal branch has  $Arg(2i) = \pi/2$ , so

$$\sqrt{2i} = \sqrt{2}e^{\left(\frac{i\pi}{4}\right)} = \sqrt{2}\frac{(1+i)}{\sqrt{2}} = 1+i.$$

The other distinct value is when n = 1 and gives minus the value just above.

**Example 1.22.** Cube roots: Compute all the cube roots of i. Give the value which comes from the principal branch of  $\log(z)$ .

Solution: We have  $\log(i) = i\frac{\pi}{2} + i2n\pi$ , where *n* is any integer. So,

$$i^{1/3} = e^{\frac{\log(i)}{3}} = e^{i\frac{\pi}{6} + i\frac{2n\pi}{3}}$$

This gives only three distinct values

$$e^{i\pi/6}$$
,  $e^{i5\pi/6}$ ,  $e^{i9\pi/6}$ 

On the principal branch  $\log(i) = i\frac{\pi}{2}$ , so the value of  $i^{1/3}$  which comes from this is

$$e^{i\pi/6} = \frac{\sqrt{3}}{2} + \frac{i}{2}.$$

**Example 1.23.** Compute all the values of  $1^i$ . What is the value from the principal branch?

Solution: This is similar to the problems above.  $log(1) = 2n\pi i$ , so

$$1^{i} = e^{i \log(1)} = e^{i2n\pi i} = e^{-2n\pi}$$
, where *n* is an integer.

The principal branch has log(1) = 0 so  $1^i = 1$ .

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 2 Notes**

Jeremy Orloff

# 2 Analytic functions

### 2.1 Introduction

The main goal of this topic is to define and give some of the important properties of complex analytic functions. A function f(z) is analytic if it has a complex derivative f'(z). In general, the rules for computing derivatives will be familiar to you from single variable calculus. However, a much richer set of conclusions can be drawn about a complex analytic function than is generally true about real differentiable functions.

# 2.2 The derivative: preliminaries

In calculus we defined the derivative as a limit. In complex analysis we will do the same.

$$f'(z) = \lim_{\Delta z \to 0} \frac{\Delta f}{\Delta z} = \lim_{\Delta z \to 0} \frac{f(z + \Delta z) - f(z)}{\Delta z}.$$

Before giving the derivative our full attention we are going to have to spend some time exploring and understanding limits. To motivate this we'll first look at two simple examples – one positive and one negative.

**Example 2.1.** Find the derivative of  $f(z) = z^2$ .

Solution: We compute using the definition of the derivative as a limit.

$$\lim_{\Delta z \to 0} \frac{(z + \Delta z)^2 - z^2}{\Delta z} = \lim_{\Delta z \to 0} \frac{z^2 + 2z\Delta z + (\Delta z)^2 - z^2}{\Delta z} = \lim_{\Delta z \to 0} 2z + \Delta z = 2z.$$

That was a positive example. Here's a negative one which shows that we need a careful understanding of limits.

**Example 2.2.** Let  $f(z) = \overline{z}$ . Show that the limit for f'(0) does not converge.

Solution: Let's try to compute f'(0) using a limit:

$$f'(0) = \lim_{\Delta z \to 0} \frac{f(\Delta z) - f(0)}{\Delta z} = \lim_{\Delta z \to 0} \frac{\overline{\Delta z}}{\Delta z} = \frac{\Delta x - i\Delta y}{\Delta x + i\Delta y}.$$

Here we used  $\Delta z = \Delta x + i \Delta y$ .

Now,  $\Delta z \to 0$  means both  $\Delta x$  and  $\Delta y$  have to go to 0. There are lots of ways to do this. For example, if we let  $\Delta z$  go to 0 along the x-axis then,  $\Delta y = 0$  while  $\Delta x$  goes to 0. In this case, we would have

$$f'(0) = \lim_{\Delta x \to 0} \frac{\Delta x}{\Delta x} = 1.$$

On the other hand, if we let  $\Delta z$  go to 0 along the positive y-axis then

$$f'(0) = \lim_{\Delta y \to 0} \frac{-i\Delta y}{i\Delta y} = -1.$$

The limits **don't** agree! The problem is that the limit depends on how  $\Delta z$  approaches 0. If we came from other directions we'd get other values. There's nothing to do, but agree that the limit does not exist.

Well, there is something we can do: explore and understand limits. Let's do that now.

# 2.3 Open disks, open deleted disks, open regions

**Definition.** The open disk of radius r around  $z_0$  is the set of points z with  $|z - z_0| < r$ , i.e. all points within distance r of  $z_0$ .

The open deleted disk of radius r around  $z_0$  is the set of points z with  $0 < |z - z_0| < r$ . That is, we remove the center  $z_0$  from the open disk. A deleted disk is also called a punctured disk.

Left: an open disk around  $z_0$ ; right: a deleted open disk around  $z_0$ 

**Definition.** An open region in the complex plane is a set A with the property that every point in A can be be surrounded by an open disk that lies entirely in A. We will often drop the word open and simply call A a region.

In the figure below, the set A on the left is an open region because for every point in A we can draw a little circle around the point that is completely in A. (The dashed boundary line indicates that the boundary of A is not part of A.) In contrast, the set B is not an open region. Notice the point z shown is on the boundary, so every disk around z contains points outside B.

Left: an open region A; right: B is not an open region

#### 2.4 Limits and continuous functions

**Definition.** If f(z) is defined on a punctured disk around  $z_0$  then we say

$$\lim_{z\to z_0}f(z)=w_0$$

if f(z) goes to  $w_0$  no matter what direction z approaches  $z_0$ .

The figure below shows several sequences of points that approach  $z_0$ . If  $\lim_{z \to z_0} f(z) = w_0$  then f(z) must go to  $w_0$  along each of these sequences.

Sequences going to  $z_0$  are mapped to sequences going to  $w_0$ .

# **Example 2.3.** Many functions have obvious limits. For example:

$$\lim_{z \to 2} z^2 = 4$$

and

$$\lim_{z \to 2} (z^2 + 2)/(z^3 + 1) = 6/9.$$

Here is an example where the limit doesn't exist because different sequences give different limits.

#### **Example 2.4.** (No limit) Show that

$$\lim_{z \to 0} \frac{z}{\overline{z}} = \lim_{z \to 0} \frac{x + iy}{x - iy}$$

does not exist.

Solution: On the real axis we have

$$\frac{z}{\overline{z}} = \frac{x}{x} = 1,$$

so the limit as  $z \to 0$  along the real axis is 1.

By contrast, on the imaginary axis we have

$$\frac{z}{\overline{z}} = \frac{iy}{-iy} = -1,$$

so the limit as  $z \to 0$  along the imaginary axis is -1. Since the two limits do not agree the limit as  $z \to 0$  does not exist!

#### 2.4.1 Properties of limits

We have the usual properties of limits. Suppose

$$\lim_{z \to z_0} f(z) = w_1 \text{ and } \lim_{z \to z_0} g(z) = w_2$$

then

• 
$$\lim_{z \to z_0} f(z) + g(z) = w_1 + w_2$$
.

$$\bullet \lim_{z \to z_0} f(z)g(z) = w_1 \cdot w_2.$$

- If  $w_2 \neq 0$  then  $\lim_{z \to z_0} f(z)/g(z) = w_1/w_2$
- If h(z) is continuous and defined on a neighborhood of  $w_1$  then  $\lim_{z \to z_0} h(f(z)) = h(w_1)$  (Note: we will give the official definition of continuity in the next section.)

We won't give a proof of these properties. As a challenge, you can try to supply it using the formal definition of limits given in the appendix.

We can restate the definition of limit in terms of functions of (x, y). To this end, let's write

$$f(z) = f(x + iy) = u(x, y) + iv(x, y)$$

and abbreviate

$$P = (x, y), P_0 = (x_0, y_0), w_0 = u_0 + iv_0.$$

Then

$$\lim_{z\to z_0} f(z) = w_0 \quad \text{ iff } \begin{cases} \lim_{P\to P_0} u(x,y) = u_0 \\ \lim_{P\to P_0} v(x,y) = v_0. \end{cases}$$

Note. The term 'iff' stands for 'if and only if' which is another way of saying 'is equivalent to'.

#### 2.4.2 Continuous functions

A function is continuous if it doesn't have any sudden jumps. This is the gist of the following definition.

**Definition.** If the function f(z) is defined on an open disk around  $z_0$  and  $\lim_{z \to z_0} f(z) = f(z_0)$  then we say f is continuous at  $z_0$ . If f is defined on an open region A then the phrase 'f is continuous on A' means that f is continuous at every point in A.

As usual, we can rephrase this in terms of functions of (x, y):

**Fact.** f(z) = u(x, y) + iv(x, y) is continuous iff u(x, y) and v(x, y) are continuous as functions of two variables.

#### Example 2.5. (Some continuous functions)

(i) A polynomial

$$P(z) = a_0 + a_1 z + a_2 z^2 + \dots + a_n z^n$$

is continuous on the entire plane. Reason: it is clear that each power  $(x + iy)^k$  is continuous as a function of (x, y).

(ii) The exponential function is continuous on the entire plane. Reason:

$$e^z = e^{x+iy} = e^x \cos(y) + ie^x \sin(y).$$

So the both the real and imaginary parts are clearly continuous as a function of (x, y).

(iii) The principal branch Arg(z) is continuous on the plane minus the non-positive real axis. Reason: this is clear and is the reason we defined branch cuts for arg. We have to remove the negative real axis because Arg(z) jumps by  $2\pi$  when you cross it. We also have to remove z=0 because Arg(z) is not even defined at 0.

(iv) The principal branch of the function log(z) is continuous on the plane minus the non-positive real axis. Reason: the principal branch of log has

$$\log(z) = \log(r) + i \operatorname{Arg}(z).$$

So the continuity of log(z) follows from the continuity of Arg(z).

#### **2.4.3** Properties of continuous functions

Since continuity is defined in terms of limits, we have the following properties of continuous functions.

Suppose f(z) and g(z) are continuous on a region A. Then

- f(z) + g(z) is continuous on A.
- f(z)g(z) is continuous on A.
- f(z)/g(z) is continuous on A except (possibly) at points where g(z) = 0.
- If h is continuous on f(A) then h(f(z)) is continuous on A.

Using these properties we can claim continuity for each of the following functions:

- $\bullet$   $e^{z^2}$
- $\cos(z) = (e^{iz} + e^{-iz})/2$
- If P(z) and Q(z) are polynomials then P(z)/Q(z) is continuous except at roots of Q(z).

# 2.5 The point at infinity

By definition the extended complex plane =  $\mathbb{C} \cup \{\infty\}$ . That is, we have **one** point at infinity to be thought of in a limiting sense described as follows.

A sequence of points  $\{z_n\}$  goes to infinity if  $|z_n|$  goes to infinity. This "point at infinity" is approached in any direction we go. All of the sequences shown in the figure below are growing, so they all go to the (same) "point at infinity".

Various sequences all going to infinity.

If we draw a large circle around 0 in the plane, then we call the region **outside** this circle a neighborhood of infinity.

The shaded region outside the circle of radius *R* is a neighborhood of infinity.

### 2.5.1 Limits involving infinity

The key idea is  $1/\infty = 0$ . By this we mean

$$\lim_{z \to \infty} \frac{1}{z} = 0$$

We then have the following facts:

- $\lim_{z \to z_0} f(z) = \infty \Leftrightarrow \lim_{z \to z_0} 1/f(z) = 0$
- $\lim_{z \to \infty} f(z) = w_0 \Leftrightarrow \lim_{z \to 0} f(1/z) = w_0$
- $\lim_{z \to \infty} f(z) = \infty \Leftrightarrow \lim_{z \to 0} \frac{1}{f(1/z)} = 0$

**Example 2.6.**  $\lim_{z\to\infty} e^z$  is not defined because it has different values if we go to infinity in different directions, e.g. we have  $e^z = e^x e^{iy}$  and

$$\lim_{x \to -\infty} e^x e^{iy} = 0$$

$$\lim_{x \to +\infty} e^x e^{iy} = \infty$$

 $\lim_{y\to +\infty} e^x e^{iy}$  is not defined, since x is constant, so  $e^x e^{iy}$  loops in a circle indefinitely.

**Example 2.7.** Show  $\lim_{z\to\infty} z^n = \infty$  (for *n* a positive integer).

Solution: We need to show that  $|z^n|$  gets large as |z| gets large. Write  $z = Re^{i\theta}$ , then

$$|z^n| = |R^n e^{in\theta}| = R^n = |z|^n$$

#### 2.5.2 Stereographic projection from the Riemann sphere

This is a lovely section and we suggest you read it. However it will be a while before we use it in 18.04.

One way to visualize the point at  $\infty$  is by using a (unit) Riemann sphere and the associated stereographic projection. The figure below shows a sphere whose equator is the unit circle in the complex plane.

Stereographic projection from the sphere to the plane.

Stereographic projection from the sphere to the plane is accomplished by drawing the secant line from the north pole N through a point on the sphere and seeing where it intersects the plane. This gives a 1-1 correspondence between a point on the sphere P and a point in the complex plane z. It is easy to see show that the formula for stereographic projection is

$$P = (a, b, c) \mapsto z = \frac{a}{1 - c} + i \frac{b}{1 - c}.$$

The point N = (0,0,1) is special, the secant lines from N through P become tangent lines to the sphere at N which never intersect the plane. We consider N the point at infinity.

In the figure above, the region outside the large circle through the point z is a neighborhood of infinity. It corresponds to the small circular cap around N on the sphere. That is, the small cap around N is a neighborhood of the point at infinity on the sphere!

The figure below shows another common version of stereographic projection. In this figure the sphere sits with its south pole at the origin. We still project using secant lines from the north pole.

#### 2.6 Derivatives

The definition of the complex derivative of a complex function is similar to that of a real derivative of a real function: For a function f(z) the derivative f at  $z_0$  is defined as

$$f'(z_0) = \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0}$$

Provided, of course, that the limit exists. If the limit exists we say f is analytic at  $z_0$  or f is differentiable at  $z_0$ .

**Remember:** The limit has to exist and be the same no matter how you approach  $z_0$ !

If f is analytic at all the points in an open region A then we say f is analytic on A.

As usual with derivatives there are several alternative notations. For example, if w = f(z) we can write

$$f'(z_0) = \frac{dw}{dz}\Big|_{z_0} = \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0} = \lim_{\Delta z \to 0} \frac{\Delta w}{\Delta z}$$

**Example 2.8.** Find the derivative of  $f(z) = z^2$ .

Solution: We did this above in Example 2.1. Take a look at that now. Of course, f'(z) = 2z.

**Example 2.9.** Show  $f(z) = \overline{z}$  is not differentiable at any point z.

Solution: We did this above in Example 2.2. Take a look at that now.

Challenge. Use polar coordinates to show the limit in the previous example can be any value with modulus 1 depending on the angle at which z approaches  $z_0$ .

#### 2.6.1 Derivative rules

It wouldn't be much fun to compute every derivative using limits. Fortunately, we have the same differentiation formulas as for real-valued functions. That is, assuming f and g are differentiable we have:

• Sum rule: 
$$\frac{d}{dz}(f(z) + g(z)) = f' + g'$$

• Product rule: 
$$\frac{d}{dz}(f(z)g(z)) = f'g + fg'$$

• Quotient rule: 
$$\frac{d}{dz}(f(z)/g(z)) = \frac{f'g - fg'}{g^2}$$

• Chain rule: 
$$\frac{d}{dz}g(f(z)) = g'(f(z))f'(z)$$

• Inverse rule: 
$$\frac{df^{-1}(z)}{dz} = \frac{1}{f'(f^{-1}(z))}$$

To give you the flavor of these arguments we'll prove the product rule.

$$\frac{d}{dz}(f(z)g(z)) = \lim_{z \to z_0} \frac{f(z)g(z) - f(z_0)g(z_0)}{z - z_0}$$

$$= \lim_{z \to z_0} \frac{(f(z) - f(z_0))g(z) + f(z_0)(g(z) - g(z_0))}{z - z_0}$$

$$= \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0} g(z) + f(z_0) \frac{(g(z) - g(z_0))}{z - z_0}$$

$$= f'(z_0)g(z_0) + f(z_0)g'(z_0)$$

Here is an important fact that you would have guessed. We will prove it in the next section.

**Theorem.** If f(z) is defined and differentiable on an open disk and f'(z) = 0 on the disk then f(z) is constant.

# 2.7 Cauchy-Riemann equations

The Cauchy-Riemann equations are our first consequence of the fact that the limit defining f(z) must be the same no matter which direction you approach z from. The Cauchy-Riemann equations will be one of the most important tools in our toolbox.

#### 2.7.1 Partial derivatives as limits

Before getting to the Cauchy-Riemann equations we remind you about partial derivatives. If u(x, y) is a function of two variables then the partial derivatives of u are defined as

$$\frac{\partial u}{\partial x}(x,y) = \lim_{\Delta x \to 0} \frac{u(x + \Delta x, y) - u(x, y)}{\Delta x},$$

i.e. the derivative of u holding y constant.

$$\frac{\partial u}{\partial y}(x, y) = \lim_{\Delta y \to 0} \frac{u(x, y + \Delta y) - u(x, y)}{\Delta y},$$

i.e. the derivative of u holding x constant.

### 2.7.2 The Cauchy-Riemann equations

The Cauchy-Riemann equations use the partial derivatives of u and v to allow us to do two things: first, to check if f has a complex derivative and second, to compute that derivative. We start by stating the equations as a theorem.

**Theorem 2.10.** (Cauchy-Riemann equations) If f(z) = u(x, y) + iv(x, y) is analytic (complex differentiable) then

$$f'(z) = \frac{\partial u}{\partial x} + i \frac{\partial v}{\partial x} = \frac{\partial v}{\partial y} - i \frac{\partial u}{\partial y}$$

In particular,

$$\frac{\partial u}{\partial x} = \frac{\partial v}{\partial y}$$
 and  $\frac{\partial u}{\partial y} = -\frac{\partial v}{\partial x}$ .

This last set of partial differential equations is what is usually meant by the Cauchy-Riemann equations.

Here is the short form of the Cauchy-Riemann equations:

$$u_x = v_y$$
$$u_y = -v_x$$

*Proof.* Let's suppose that f(z) is differentiable in some region A and

$$f(z) = f(x + iy) = u(x, y) + iv(x, y).$$

We'll compute f'(z) by approaching z first from the horizontal direction and then from the vertical direction. We'll use the formula

$$f'(z) = \lim_{\Delta z \to 0} \frac{f(z + \Delta z) - f(z)}{\Delta z},$$

where  $\Delta z = \Delta x + i \Delta y$ .

Horizontal direction:  $\Delta y = 0$ ,  $\Delta z = \Delta x$ 

$$f'(z) = \lim_{\Delta z \to 0} \frac{f(z + \Delta z) - f(z)}{\Delta z}$$

$$= \lim_{\Delta x \to 0} \frac{f(x + \Delta x + iy) - f(x + iy)}{\Delta x}$$

$$= \lim_{\Delta x \to 0} \frac{(u(x + \Delta x, y) + iv(x + \Delta x, y)) - (u(x, y) + iv(x, y))}{\Delta x}$$

$$= \lim_{\Delta x \to 0} \frac{u(x + \Delta x, y) - u(x, y)}{\Delta x} + i \frac{v(x + \Delta x, y) - v(x, y)}{\Delta x}$$

$$= \frac{\partial u}{\partial x}(x, y) + i \frac{\partial v}{\partial x}(x, y)$$

Vertical direction:  $\Delta x = 0$ ,  $\Delta z = i\Delta y$  (We'll do this one a little faster.)

$$f'(z) = \lim_{\Delta z \to 0} \frac{f(z + \Delta z) - f(z)}{\Delta z}$$

$$= \lim_{\Delta y \to 0} \frac{(u(x, y + \Delta y) + iv(x, y + \Delta y)) - (u(x, y) + iv(x, y))}{i\Delta y}$$

$$= \lim_{\Delta y \to 0} \frac{u(x, y + \Delta y) - u(x, y)}{i\Delta y} + i \frac{v(x, y + \Delta y) - v(x, y)}{i\Delta y}$$

$$= \frac{1}{i} \frac{\partial u}{\partial y}(x, y) + \frac{\partial v}{\partial y}(x, y)$$

$$= \frac{\partial v}{\partial y}(x, y) - i \frac{\partial u}{\partial y}(x, y)$$

We have found two different representations of f'(z) in terms of the partials of u and v. If put them together we have the Cauchy-Riemann equations:

$$f'(z) = \frac{\partial u}{\partial x} + i \frac{\partial v}{\partial x} = \frac{\partial v}{\partial y} - i \frac{\partial u}{\partial y}$$
  $\Rightarrow$   $\frac{\partial u}{\partial x} = \frac{\partial v}{\partial y}$ , and  $-\frac{\partial u}{\partial y} = \frac{\partial v}{\partial x}$ .

It turns out that the converse is true and will be very useful to us.

**Theorem.** Consider the function f(z) = u(x, y) + iv(x, y) defined on a region A. If u and v satisfy the Cauchy-Riemann equations and have continuous partials then f(z) is differentiable on A.

The proof of this is a tricky exercise in analysis. It is somewhat beyond the scope of this class, so we will skip it. If you're interested, with a little effort you should be able to grasp it.

# 2.7.3 Using the Cauchy-Riemann equations

The Cauchy-Riemann equations provide us with a direct way of checking that a function is differentiable and computing its derivative.

**Example 2.11.** Use the Cauchy-Riemann equations to show that  $e^z$  is differentiable and its derivative is  $e^z$ .

Solution: We write 
$$e^z = e^{x+iy} = e^x \cos(y) + ie^x \sin(y)$$
. So

$$u(x, y) = e^x \cos(y)$$
 and  $v(x, y) = e^x \sin(y)$ .

Computing partial derivatives we have

$$u_x = e^x \cos(y),$$
  $u_y = -e^x \sin(y)$   
 $v_x = e^x \sin(y),$   $v_y = e^x \cos(y)$ 

We see that  $u_x = v_y$  and  $u_y = -v_x$ , so the Cauchy-Riemann equations are satisfied. Thus,  $e^z$  is differentiable and

$$\frac{d}{dz}e^z = u_x + iv_x = e^x \cos(y) + ie^x \sin(y) = e^z.$$

**Example 2.12.** Use the Cauchy-Riemann equations to show that  $f(z) = \overline{z}$  is not differentiable.

Solution: f(x + iy) = x - iy, so u(x, y) = x, v(x, y) = -y. Taking partial derivatives

$$u_x = 1$$
,  $u_y = 0$ ,  $v_x = 0$ ,  $v_y = -1$ 

Since  $u_x \neq v_y$  the Cauchy-Riemann equations are not satisfied and therefore f is not differentiable.

**Theorem.** If f(z) is differentiable on a disk and f'(z) = 0 on the disk then f(z) is constant.

*Proof.* Since f is differentiable and  $f'(z) \equiv 0$ , the Cauchy-Riemann equations show that

$$u_x(x, y) = u_y(x, y) = v_x(x, y) = v_y(x, y) = 0$$

We know from multivariable calculus that a function of (x, y) with both partials identically zero is constant. Thus u and v are constant, and therefore so is f.

### **2.7.4** f'(z) as a 2 × 2 matrix

Recall that we could represent a complex number a + ib as a  $2 \times 2$  matrix

$$a+ib \quad \leftrightarrow \quad \begin{bmatrix} a & -b \\ b & a \end{bmatrix}.$$
 (1)

Now if we write f(z) in terms of (x, y) we have

$$f(z) = f(x+iy) = u(x,y) + iv(x,y) \quad \leftrightarrow \quad f(x,y) = (u(x,y), v(x,y)).$$

We have

$$f'(z) = u_x + iv_x,$$

so we can represent f'(z) as

$$\begin{bmatrix} u_x & -v_x \\ v_x & u_x \end{bmatrix}.$$

Using the Cauchy-Riemann equations we can replace  $-v_x$  by  $u_y$  and  $u_x$  by  $v_y$  which gives us the representation

$$f'(z) \quad \leftrightarrow \quad \begin{bmatrix} u_x & u_y \\ v_x & v_y \end{bmatrix},$$

i.e, f'(z) is just the Jacobian of f(x, y).

For me, it is easier to remember the Jacobian than the Cauchy-Riemann equations. Since f'(z) is a complex number I can use the matrix representation in Equation 1 to remember the Cauchy-Riemann equations!

# 2.8 Cauchy-Riemann all the way down

We've defined an analytic function as one having a complex derivative. The following theorem shows that if f is analytic then so is f'. Thus, there are derivatives all the way down!

**Theorem 2.13.** Assume the second order partials of u and v exist and are continuous. If f(z) = u + iv is analytic, then so is f'(z).

*Proof.* To show this we have to prove that f'(z) satisfies the Cauchy-Riemann equations. If f = u + iv we know

$$u_x = v_y$$
,  $u_y = -v_x$ ,  $f' = u_x + iv_x$ .

Let's write

$$f' = U + iV,$$

so, by Cauchy-Riemann,

$$U = u_x = v_y, \quad V = v_x = -u_y.$$
 (2)

We want to show that  $U_x = V_y$  and  $U_y = -V_x$ . We do them one at a time.

To prove  $U_x = V_y$ , we use Equation 2 to see that

$$U_x = v_{yx}$$
 and  $V_y = v_{xy}$ .

Since  $v_{xy} = v_{yx}$ , we have  $U_x = V_y$ .

Similarly, to show  $U_v = -V_x$ , we compute

$$U_v = u_{xy}$$
 and  $V_x = -u_{yx}$ .

So, 
$$U_y = -V_x$$
. QED.

**Technical point.** We've assumed as many partials as we need. So far we can't guarantee that all the partials exist. Soon we will have a theorem which says that an analytic function has derivatives of all order. We'll just assume that for now. In any case, in most examples this will be obvious.

#### 2.9 Gallery of functions

In this section we'll look at many of the functions you know and love as functions of z. For each one we'll have to do three things.

- 1. Define how to compute it.
- 2. Specify a branch (if necessary) giving its range.
- 3. Specify a domain (with branch cut if necessary) where it is analytic.
- 4. Compute its derivative.

Most often, we can compute the derivatives of a function using the algebraic rules like the quotient rule. If necessary we can use the Cauchy-Riemann equations or, as a last resort, even the definition of the derivative as a limit.

Before we start on the gallery we define the term "entire function".

**Definition.** A function that is analytic at every point in the complex plane is called an entire function. We will see that  $e^z$ ,  $z^n$ ,  $\sin(z)$  are all entire functions.

# 2.9.1 Gallery of functions, derivatives and properties

The following is a concise list of a number of functions and their complex derivatives. None of the derivatives will surprise you. We also give important properties for some of the functions. The proofs for each follow below.

1.  $f(z) = e^z = e^x \cos(y) + ie^x \sin(y)$ .

Domain = all of  $\mathbb{C}$  ( f is entire).

$$f'(z) = e^z$$
.

2.  $f(z) \equiv c$  (constant)

Domain = all of  $\mathbb{C}$  (f is entire).

$$f'(z) = 0.$$

3.  $f(z) = z^n$  (*n* an integer  $\ge 0$ )

Domain = all of  $\mathbb{C}$  (f is entire).

$$f'(z) = nz^{n-1}.$$

4. P(z) (polynomial)

A polynomial has the form  $P(z) = a_n z^n + a_{n-1} z^{n-1} + ... + a_0$ .

Domain = all of  $\mathbb{C}$  (P(z) is entire).

$$P'(z) = na_n z^{n-1} + (n-1)a_{n-1} z^{n-1} + \dots + 2a_2 z + a_1.$$

5. f(z) = 1/z

Domain =  $\mathbb{C} - \{0\}$  (the punctured plane).

$$f'(z) = -1/z^2$$
.

6. f(z) = P(z)/Q(z) (rational function).

When P and Q are polynomials P(z)/Q(z) is called a rational function.

If we assume that P and Q have no common roots, then:

Domain =  $\mathbb{C}$  – {roots of Q}

$$f'(z) = \frac{P'Q - PQ'}{Q^2}.$$

7.  $\sin(z)$ ,  $\cos(z)$ 

**Definition.** 
$$\cos(z) = \frac{e^{iz} + e^{-iz}}{2}, \quad \sin(z) = \frac{e^{iz} - e^{-iz}}{2i}$$

(By Euler's formula we know this is consistent with cos(x) and sin(x) when z = x is real.)

Domain: these functions are entire.

$$\frac{d\cos(z)}{dz} = -\sin(z), \quad \frac{d\sin(z)}{dz} = \cos(z).$$

Other key properties of sin and cos:

- $-\cos^2(z) + \sin^2(z) = 1$
- $-e^z = \cos(z) + i\sin(z)$
- Periodic in x with period  $2\pi$ , e.g.  $\sin(x + 2\pi + iy) = \sin(x + iy)$ .
- They are not bounded!
- In the form f(z) = u(x, y) + iv(x, y) we have

$$\cos(z) = \cos(x)\cosh(y) - i\sin(x)\sinh(y)$$

$$\sin(z) = \sin(x)\cosh(y) + i\cos(x)\sinh(y)$$

(cosh and sinh are defined below.)

- The zeros of  $\sin(z)$  are  $z = n\pi$  for n any integer. The zeros of  $\cos(z)$  are  $z = \pi/2 + n\pi$  for n any integer. (That is, they have only real zeros that you learned about in your trig. class.)
- 8. Other trig functions cot(z), sec(z) etc.

**Definition.** The same as for the real versions of these function, e.g.  $\cot(z) = \cos(z)/\sin(z)$ ,  $\sec(z) = 1/\cos(z)$ .

Domain: The entire plane minus the zeros of the denominator.

Derivative: Compute using the quotient rule, e.g.

$$\frac{d\tan(z)}{dz} = \frac{d}{dz} \left(\frac{\sin(z)}{\cos(z)}\right) = \frac{\cos(z)\cos(z) - \sin(z)(-\sin(z))}{\cos^2(z)} = \frac{1}{\cos^2(z)} = \sec^2 z$$

(No surprises there!)

9. sinh(z), cosh(z) (hyperbolic sine and cosine)

Definition.

$$\cosh(z) = \frac{e^z + e^{-z}}{2}, \quad \sinh(z) = \frac{e^z - e^{-z}}{2}$$

Domain: these functions are entire.

$$\frac{d\cosh(z)}{dz} = \sinh(z), \quad \frac{d\sinh(z)}{dz} = \cosh(z)$$

Other key properties of cosh and sinh:

- $-\cosh^2(z) \sinh^2(z) = 1$
- For real x, cosh(x) is real and positive, sinh(x) is real.
- $-\cosh(iz) = \cos(z), \quad \sinh(z) = -i\sin(iz).$
- 10.  $\log(z)$  (See Topic 1.)

**Definition.**  $\log(z) = \log(|z|) + i \arg(z)$ .

Branch: Any branch of arg(z).

Domain: C minus a branch cut where the chosen branch of arg(z) is discontinuous.

$$\frac{d}{dz}\log(z) = \frac{1}{z}$$

11.  $z^a$  (any complex a) (See Topic 1.)

**Definition.**  $z^a = e^{a \log(z)}$ .

Branch: Any branch of log(z).

Domain: Generally the domain is  $\mathbb{C}$  minus a branch cut of log. If a is an integer  $\geq 0$  then  $z^a$  is entire. If a is a negative integer then  $z^a$  is defined and analytic on  $\mathbb{C} - \{0\}$ .

$$\frac{dz^a}{dz} = az^{a-1}.$$

12.  $\sin^{-1}(z)$ 

**Definition.**  $\sin^{-1}(z) = -i \log(iz + \sqrt{1 - z^2}).$ 

The definition is chosen so that  $\sin(\sin^{-1}(z)) = z$ . The derivation of the formula is as follows. Let  $w = \sin^{-1}(z)$ , so  $z = \sin(w)$ . Then,

$$z = \frac{e^{iw} - e^{-iw}}{2i} \Rightarrow e^{2iw} - 2ize^{iw} - 1 = 0$$

Solving the quadratic in  $e^{iw}$  gives

$$e^{iw} = \frac{2iz + \sqrt{-4z^2 + 4}}{2} = iz + \sqrt{1 - z^2}.$$

Taking the log gives

$$iw = \log(iz + \sqrt{1 - z^2}) \Leftrightarrow w = -i\log(iz + \sqrt{1 - z^2}).$$

From the definition we can compute the derivative:

$$\frac{d}{dz}\sin^{-1}(z) = \frac{1}{\sqrt{1 - z^2}}.$$

Choosing a branch is tricky because both the square root and the log require choices. We will look at this more carefully in the future.

For now, the following discussion and figure are for your amusement.

Sine (likewise cosine) is not a 1-1 function, so if we want  $\sin^{-1}(z)$  to be single-valued then we have to choose a region where  $\sin(z)$  is 1-1. (This will be a branch of  $\sin^{-1}(z)$ , i.e. a range for the image,) The figure below shows a domain where  $\sin(z)$  is 1-1. The domain consists of the vertical strip z = x + iy with  $-\pi/2 < x < \pi/2$  together with the two rays on boundary where  $y \ge 0$  (shown as red lines). The figure indicates how the regions making up the domain in the z-plane are mapped to the quadrants in the w-plane.

A domain where  $z \mapsto w = \sin(z)$  is one-to-one

#### 2.9.2 A few proofs

Here we prove at least some of the facts stated in the list just above.

- 1.  $f(z) = e^z$ . This was done in Example 2.11 using the Cauchy-Riemann equations.
- 2.  $f(z) \equiv c$  (constant). This case is trivial.
- 3.  $f(z) = z^n$  (n an integer  $\ge 0$ ): show  $f'(z) = nz^{n-1}$

It's probably easiest to use the definition of derivative directly. Before doing that we note the factorization

$$z^{n} - z_{0}^{n} = (z - z_{0})(z^{n-1} + z^{n-2}z_{0} + z^{n-3}z_{0}^{2} + \dots + z^{2}z_{0}^{n-3} + zz_{0}^{n-2} + z_{0}^{n-1})$$

Now

$$f'(z_0) = \lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0} = \lim_{z \to z_0} \frac{z^n - z_0^n}{z - z_0}$$

$$= \lim_{z \to z_0} (z^{n-1} + z^{n-2}z_0 + z^{n-3}z_0^2 + \dots + z^2z_0^{n-3} + zz_0^{n-2} + z_0^{n-1})$$

$$= nz_0^{n-1}.$$

Since we showed directly that the derivative exists for all z, the function must be entire.

- 4. P(z) (polynomial). Since a polynomial is a sum of monomials, the formula for the derivative follows from the derivative rule for sums and the case  $f(z) = z^n$ . Likewise the fact the P(z) is entire.
- 5. f(z) = 1/z. This follows from the quotient rule.
- 6. f(z) = P(z)/Q(z). This also follows from the quotient rule.
- 7.  $\sin(z)$ ,  $\cos(z)$ . All the facts about  $\sin(z)$  and  $\cos(z)$  follow from their definition in terms of exponentials.
- 8. Other trig functions  $\cot(z)$ ,  $\sec(z)$  etc. Since these are all defined in terms of cos and sin, all the facts about these functions follow from the derivative rules.
- 9.  $\sinh(z)$ ,  $\cosh(z)$ . All the facts about  $\sinh(z)$  and  $\cosh(z)$  follow from their definition in terms of exponentials.
- 10.  $\log(z)$ . The derivative of  $\log(z)$  can be found by differentiating the relation  $e^{\log(z)} = z$  using the chain rule. Let  $w = \log(z)$ , so  $e^w = z$  and

$$\frac{d}{dz}e^{w} = \frac{dz}{dz} = 1 \quad \Rightarrow \quad \frac{de^{w}}{dw}\frac{dw}{dz} = 1 \quad \Rightarrow \quad e^{w}\frac{dw}{dz} = 1 \quad \Rightarrow \quad \frac{dw}{dz} = \frac{1}{e^{w}}$$

Using  $w = \log(z)$  we get

$$\frac{d\log(z)}{dz} = \frac{1}{z}.$$

11.  $z^a$  (any complex a). The derivative for this follows from the formula

$$z^a = e^{a \log(z)}$$
  $\Rightarrow$   $\frac{dz^a}{dz} = e^{a \log(z)} \cdot \frac{a}{z} = \frac{az^a}{z} = az^{a-1}$ 

# 2.10 Branch cuts and function composition

We often compose functions, i.e. f(g(z)). In general in this case we have the chain rule to compute the derivative. However we need to specify the domain for z where the function is analytic. And when branches and branch cuts are involved we need to take care.

**Example 2.14.** Let  $f(z) = e^{z^2}$ . Since  $e^z$  and  $z^2$  are both entire functions, so is  $f(z) = e^{z^2}$ . The chain rule gives us

$$f'(z) = e^{z^2}(2z).$$

**Example 2.15.** Let  $f(z) = e^z$  and g(z) = 1/z. f(z) is entire and g(z) is analytic everywhere but 0. So f(g(z)) is analytic except at 0 and

$$\frac{df(g(z))}{dz} = f'(g(z))g'(z) = e^{1/z} \cdot \frac{-1}{z^2}.$$

**Example 2.16.** Let  $h(z) = 1/(e^z - 1)$ . Clearly h is entire except where the denominator is 0. The denominator is 0 when  $e^z - 1 = 0$ . That is, when  $z = 2\pi ni$  for any integer n. Thus, h(z) is analytic on the set

$$\mathbf{C} - \{2\pi ni, \text{ where } n \text{ is any integer}\}\$$

The quotient rule gives  $h'(z) = -e^z/(e^z - 1)^2$ . A little more formally: h(z) = f(g(z)). where f(w) = 1/w and  $w = g(z) = e^z - 1$ . We know that g(z) is entire and f(w) is analytic everywhere except w = 0. Therefore, f(g(z)) is analytic everywhere except where g(z) = 0.

**Example 2.17.** It can happen that the derivative has a larger domain where it is analytic than the original function. The main example is  $f(z) = \log(z)$ . This is analytic on C minus a branch cut. However

$$\frac{d}{dz}\log(z) = \frac{1}{z}$$

is analytic on  $\mathbb{C} - \{0\}$ . The converse can't happen.

**Example 2.18.** Define a region where  $\sqrt{1-z}$  is analytic.

Solution: Choosing the principal branch of argument, we have  $\sqrt{w}$  is analytic on

$$\mathbf{C} - \{x \le 0, y = 0\}$$
, (see figure below.).

So  $\sqrt{1-z}$  is analytic except where w=1-z is on the branch cut, i.e. where w=1-z is real and  $\leq 0$ . It's easy to see that

$$w = 1 - z$$
 is real and  $< 0 \Leftrightarrow z$  is real and  $> 1$ .

So  $\sqrt{1-z}$  is analytic on the region (see figure below)

$$\mathbf{C} - \{x > 1, y = 0\}$$

Note. A different branch choice for  $\sqrt{w}$  would lead to a different region where  $\sqrt{1-z}$  is analytic.

The figure below shows the domains with branch cuts for this example.

**Example 2.19.** Define a region where  $f(z) = \sqrt{1 + e^z}$  is analytic.

Solution: Again, let's take  $\sqrt{w}$  to be analytic on the region

$$\mathbf{C} - \{x \le 0, y = 0\}$$

So, f(z) is analytic except where  $1 + e^z$  is real and  $\le 0$ . That is, except where  $e^z$  is real and  $\le -1$ . Now,  $e^z = e^x e^{iy}$  is real only when y is a multiple of  $\pi$ . It is negative only when y is an odd multiple of  $\pi$ . It has magnitude greater than 1 only when x > 0. Therefore f(z) is analytic on the region

$$\mathbf{C} - \{x \ge 0, \ y = \text{odd multiple of } \pi\}$$

The figure below shows the domains with branch cuts for this example.

# 2.11 Appendix: Limits

The intuitive idea behind limits is relatively simple. Still, in the 19th century mathematicians were troubled by the lack of rigor, so they set about putting limits and analysis on a firm footing with careful definitions and proofs. In this appendix we give you the formal definition and connect it to the intuitive idea. In 18.04 we will not need this level of formality. Still, it's nice to know the foundations are solid, and some students may find this interesting.

### 2.11.1 Limits of sequences

Intuitively, we say a sequence of complex numbers  $z_1, z_2, \ldots$  converges to a if for large  $n, z_n$  is really close to a. To be a little more precise, if we put a small circle of radius  $\epsilon$  around a then eventually the sequence should stay inside the circle. Let's refer to this as the sequence being captured by the circle. This has to be true for any circle no matter how small, though it may take longer for the sequence to be 'captured' by a smaller circle.

This is illustrated in the figure below. The sequence is strung along the curve shown heading towards a. The bigger circle of radius  $\epsilon_2$  captures the sequence by the time n=47, the smaller circle doesn't capture it till n=59. Note that  $z_{25}$  is inside the larger circle, but since later points are outside the circle we don't say the sequence is captured at n=25

A sequence of points converging to a

**Definition.** The sequence  $z_1, z_2, z_3, \ldots$  converges to the value a if for every  $\epsilon > 0$  there is a number  $N_{\epsilon}$  such that  $|z_n - a| < \epsilon$  for all  $n > N_{\epsilon}$ . We write this as

$$\lim_{n\to\infty} z_n = a.$$

Again, the definition just says that eventually the sequence is within  $\epsilon$  of a, no matter how small you choose  $\epsilon$ .

**Example 2.20.** Show that the sequence  $z_n = (1/n + i)^2$  has limit -1.

Solution: This is clear because  $1/n \to 0$ . For practice, let's phrase it in terms of epsilons: given  $\epsilon > 0$  we have to choose  $N_{\epsilon}$  such that

$$|z_n - (-1)| < \epsilon$$
 for all  $n > N_{\epsilon}$ 

One strategy is to look at  $|z_n + 1|$  and see what  $N_{\epsilon}$  should be. We have

$$|z_n - (-1)| = \left| \left( \frac{1}{n} + i \right)^2 + 1 \right| = \left| \frac{1}{n^2} + \frac{2i}{n} \right| < \frac{1}{n^2} + \frac{2}{n}$$

So all we have to do is pick  $N_{\epsilon}$  large enough that

$$\frac{1}{N_{\epsilon}^2} + \frac{2}{N_{\epsilon}} < \epsilon$$

Since this can clearly be done we have proved that  $z_n \to i$ .

This was clearly more work than we want to do for every limit. Fortunately, most of the time we can apply general rules to determine a limit without resorting to epsilons!

#### Remarks.

- 1. In 18.04 we will be able to spot the limit of most concrete examples of sequences. The formal definition is needed when dealing abstractly with sequences.
- 2. To mathematicians  $\epsilon$  is one of the go-to symbols for a small number. The prominent and rather eccentric mathematician Paul Erdos used to refer to children as epsilons, as in 'How are the epsilons doing?'
- 3. The term 'captured by the circle' is not in common usage, but it does capture what is happening.

**2.11.2** 
$$\lim_{z \to z_0} f(z)$$

Sometimes we need limits of the form  $\lim_{z \to z_0} f(z) = a$ . Again, the intuitive meaning is clear: as z gets close to  $z_0$  we should see f(z) get close to a. Here is the technical definition

**Definition.** Suppose f(z) is defined on a punctured disk  $0 < |z - z_0| < r$  around  $z_0$ . We say  $\lim_{z \to z_0} f(z) = a$  if for every  $\epsilon > 0$  there is a  $\delta$  such that

$$|f(z) - a| < \epsilon$$
 whenever  $0 < |z - z_0| < \delta$ 

This says exactly that as z gets closer (within  $\delta$ ) to  $z_0$  we have f(z) is close (within  $\epsilon$ ) to a. Since  $\epsilon$  can be made as small as we want, f(z) must go to a.

#### Remarks.

- 1. Using the punctured disk (also called a deleted neighborhood) means that f(z) does not have to be defined at  $z_0$  and, if it is then  $f(z_0)$  does not necessarily equal a. If  $f(z_0) = a$  then we say the f is continuous at  $z_0$ .
- 2. Ask any mathematician to complete the phrase "For every  $\epsilon$ " and the odds are that they will respond "there is a  $\delta$ ..."

#### 2.11.3 Connection between limits of sequences and limits of functions

Here's an equivalent way to define limits of functions: the limit  $\lim_{z \to z_0} f(z) = a$  if, for every sequence of points  $\{z_n\}$  with limit  $z_0$  the sequence  $\{f(z_n)\}$  has limit a.

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 3 Notes**

Jeremy Orloff

# 3 Line integrals and Cauchy's theorem

#### 3.1 Introduction

The basic theme here is that complex line integrals will mirror much of what we've seen for multivariable calculus line integrals. But, just like working with  $e^{i\theta}$  is easier than working with sine and cosine, complex line integrals are easier to work with than their multivariable analogs. At the same time they will give deep insight into the workings of these integrals.

To define complex line integrals, we will need the following ingredients:

- The complex plane: z = x + iy
- The complex differential dz = dx + idy
- A curve in the complex plane:  $\gamma(t) = x(t) + iy(t)$ , defined for  $a \le t \le b$ .
- A complex function: f(z) = u(x, y) + iv(x, y)

### 3.2 Complex line integrals

Line integrals are also called path or contour integrals. Given the ingredients we define the complex line integral  $\int_{\mathbb{R}} f(z) dz$  by

$$\int_{\gamma} f(z) dz := \int_{a}^{b} f(\gamma(t))\gamma'(t) dt.$$
 (1a)

You should note that this notation looks just like integrals of a real variable. We don't need the vectors and dot products of line integrals in  $\mathbb{R}^2$ . Also, make sure you understand that the product  $f(\gamma(t))\gamma'(t)$  is just a product of complex numbers.

An alternative notation uses dz = dx + idy to write

$$\int_{\gamma} f(z) dz = \int_{\gamma} (u + iv)(dx + idy)$$
 (1b)

Let's check that Equations 1a and 1b are the same. Equation 1b is really a multivariable calculus expression, so thinking of  $\gamma(t)$  as (x(t), y(t)) it becomes

$$\int_{\gamma} f(z) \, dz = \int_{a}^{b} \left[ u(x(t), y(t)) + iv(x(t), y(t)) \right] \left( x'(t) + iy'(t) \right) dt$$

But,

$$u(x(t), y(t)) + iv(x(t), y(t)) = f(\gamma(t))$$

and

$$x'(t) + iy'(t) = \gamma'(t)$$

so the right hand side of this equation is

$$\int_a^b f(\gamma(t))\gamma'(t)\,dt.$$

That is, it is exactly the same as the expression in Equation 1a.

**Example 3.1.** Compute  $\int_{\gamma} z^2 dz$  along the straight line from 0 to 1 + *i*.

Solution: We parametrize the curve as  $\gamma(t) = t(1+i)$  with  $0 \le t \le 1$ . So  $\gamma'(t) = 1+i$ . The line integral is

$$\int z^2 dz = \int_0^1 t^2 (1+i)^2 (1+i) dt = \frac{2i(1+i)}{3}.$$

**Example 3.2.** Compute  $\int_{\gamma} \overline{z} dz$  along the straight line from 0 to 1 + i.

Solution: We can use the same parametrization as in the previous example. So,

$$\int_{\gamma} \overline{z} \, dz = \int_{0}^{1} t(1-i)(1+i) \, dt = 1.$$

**Example 3.3.** Compute  $\int_{\gamma} z^2 dz$  along the unit circle.

Solution: We parametrize the unit circle by  $\gamma(\theta) = e^{i\theta}$ , where  $0 \le \theta \le 2\pi$ . We have  $\gamma'(\theta) = ie^{i\theta}$ . So, the integral becomes

$$\int_{\gamma} z^2 dz = \int_{0}^{2\pi} e^{2i\theta} i e^{i\theta} d\theta = \int_{0}^{2\pi} i e^{3i\theta} d\theta = \left. \frac{e^{i3\theta}}{3} \right|_{0}^{2\pi} = 0.$$

**Example 3.4.** Compute  $\int \overline{z} dz$  along the unit circle.

Solution: Parametrize C:  $\gamma(t) = e^{it}$ , with  $0 \le t \le 2\pi$ . So,  $\gamma'(t) = ie^{it}$ . Putting this into the integral gives

$$\int_C \overline{z} \, dz = \int_0^{2\pi} \overline{e^{it}} \, i \, e^{it} \, dt = \int_0^{2\pi} i \, dt = \boxed{2\pi i.}$$

#### 3.3 Fundamental theorem for complex line integrals

This is exactly analogous to the fundamental theorem of calculus.

**Theorem 3.5.** (Fundamental theorem of complex line integrals) If f(z) is a complex analytic function on an open region A and  $\gamma$  is a curve in A from  $z_0$  to  $z_1$  then

$$\int_{\gamma} f'(z) \, dz = f(z_1) - f(z_0).$$

*Proof.* This is an application of the chain rule. We have

$$\frac{df(\gamma(t))}{dt} = f'(\gamma(t))\gamma'(t).$$

So

$$\int_{\gamma} f'(z) dz = \int_{a}^{b} f'(\gamma(t)) \gamma'(t) dt = \int_{a}^{b} \frac{df(\gamma(t))}{dt} dt = f(\gamma(t)) \Big|_{a}^{b} = f(z_{1}) - f(z_{0}).$$

Another equivalent way to state the fundamental theorem is: if f has an antiderivative F, i.e. F' = f then

$$\int_{\gamma} f(z) \, dz = F(z_1) - F(z_0).$$

**Example 3.6.** Redo  $\int_{\gamma} z^2 dz$ , with  $\gamma$  the straight line from 0 to 1 + i.

Solution: We can check by inspection that  $z^2$  has an antiderivative  $F(z) = z^3/3$ . Therefore the fundamental theorem implies

$$\int_{\gamma} z^2 dz = \frac{z^3}{3} \bigg|_{0}^{1+i} = \frac{(1+i)^3}{3} = \frac{2i(1+i)}{3}.$$

**Example 3.7.** Redo  $\int_{\gamma} z^2 dz$ , with  $\gamma$  the unit circle.

Solution: Again, since  $z^2$  had antiderivative  $z^3/3$  we can evaluate the integral by plugging the endpoints of  $\gamma$  into the  $z^3/3$ . Since the endpoints are the same the resulting difference will be 0!

# 3.4 Path independence

We say the integral  $\int_{\gamma} f(z) dz$  is path independent if it has the same value for any two paths with the same endpoints. More precisely, if f(z) is defined on a region A then  $\int_{\gamma} f(z) dz$  is path independent in A, if it has the same value for any two paths in A with the same endpoints.

The following theorem follows directly from the fundamental theorem. The proof uses the same argument as Example 3.7.

**Theorem 3.8.** If f(z) has an antiderivative in an open region A, then the path integral  $\int_{\gamma} f(z) dz$  is path independent for all paths in A.

*Proof.* Since f(z) has an antiderivative of f(z), the fundamental theorem tells us that the integral only depends on the endpoints of  $\gamma$ , i.e.

$$\int_{\gamma} f(z) dz = F(z_1) - F(z_0)$$

where  $z_0$  and  $z_1$  are the beginning and end point of  $\gamma$ .

An alternative way to express path independence uses closed paths.

**Theorem 3.9.** The following two things are equivalent.

- 1. The integral  $\int f(z) dz$  is path independent.
- 2. The integral  $\int_{\mathbb{R}^n} f(z) dz$  around any closed path is 0.

*Proof.* This is essentially identical to the equivalent multivariable proof. We have to show two things:

- (i) Path independence implies the line integral around any closed path is 0.
- (ii) If the line integral around all closed paths is 0 then we have path independence.

To see (i), assume path independence and consider the closed path C shown in figure (i) below. Since the starting point  $z_0$  is the same as the endpoint  $z_1$  the line integral  $\int_C f(z) dz$  must have the same value as the line integral over the curve consisting of the single point  $z_0$ . Since that is clearly 0 we must have the integral over C is 0.

To see (ii), assume  $\int_C f(z) dz = 0$  for any closed curve. Consider the two curves  $C_1$  and  $C_2$  shown in figure (ii). Both start at  $z_0$  and end at  $z_1$ . By the assumption that integrals over closed paths are 0 we have  $\int_{C_1 - C_2} f(z) dz = 0$ . So,

$$\int_{C_1} f(z) \, dz = \int_{C_2} f(z) \, dz.$$

That is, any two paths from  $z_0$  to  $z_1$  have the same line integral. This shows that the line integrals are path independent.

Figure (i)

Figure (ii)

### **Examples**

**Example 3.10.** Why can't we compute  $\int \overline{z} dz$  using the fundamental theorem.

Solution: Because  $\overline{z}$  doesn't have an antiderivative. We can also see this by noting that if  $\overline{z}$  had an antiderivative, then its integral around the unit circle would have to be 0. But, we saw in Example 3.4 that this is not the case.

**Example 3.11.** Compute  $\int_{\mathcal{X}} \frac{1}{z} dz$  over each of the following contours

(i) The line from 1 to 1 + i.

- (ii) The circle of radius 1 around z = 3.
- (iii) The unit circle.

Solution: For parts (i) and (ii) there is no problem using the antiderivative log(z) because these curves are contained in a simply connected region that doesn't contain the origin.

(i)

$$\int_{\gamma} \frac{1}{z} dz = \log(1+i) - \log(1) = \log(\sqrt{2}) + i\frac{\pi}{4}.$$

(ii) Since the beginning and end points are the same, we get

$$\int_{\gamma} \frac{1}{z} \, dz = 0$$

(iii) We parametrize the unit circle by  $\gamma(\theta) = e^{i\theta}$  with  $0 \le \theta \le 2\pi$ . We compute  $\gamma'(\theta) = ie^{i\theta}$ . So the integral becomes

$$\int_{\gamma} \frac{1}{z} dz = \int_{0}^{2\pi} \frac{1}{e^{i\theta}} i e^{i\theta} dt = \int_{0}^{2\pi} i dt = 2\pi i.$$

Notice that we could use  $\log(z)$  if we were careful to let the argument increase by  $2\pi$  as it went around the origin once.

**Example 3.12.** Compute  $\int_{\gamma} \frac{1}{z^2} dz$ , where  $\gamma$  is the unit circle in two ways.

- (i) Using the fundamental theorem.
- (ii) Directly from the definition.

Solution: (i) Let f(z) = -1/z. Since  $f'(z) = 1/z^2$ , the fundamental theorem says

$$\int_{\gamma} \frac{1}{z^2} dz = \int_{\gamma} f'(z) dz = f(\text{endpoint}) - f(\text{start point}) = 0.$$

It equals 0 because the start and endpoints are the same.

(ii) As usual, we parametrize the unit circle as  $\gamma(\theta) = e^{i\theta}$  with  $0 \le \theta \le 2\pi$ . So,  $\gamma'(\theta) = ie^{i\theta}$  and the integral becomes

$$\int_{\gamma} \frac{1}{z^2} dz = \int_{0}^{2\pi} \frac{1}{e^{2i\theta}} i e^{i\theta} d\theta = \int_{0}^{2\pi} i e^{-i\theta} d\theta = -e^{-i\theta} \Big|_{0}^{2\pi} = 0.$$

# 3.6 Cauchy's theorem

Cauchy's theorem is analogous to Green's theorem for curl free vector fields.

**Theorem 3.13.** (Cauchy's theorem) Suppose A is a simply connected region, f(z) is analytic on A and C is a simple closed curve in A. Then the following three things hold:

(i) 
$$\int_C f(z) dz = 0$$

- (i') We can drop the requirement that C is simple in part (i).
- (ii) Integrals of f on paths within A are path independent. That is, two paths with the same endpoints integrate to the same value.

(iii) f has an antiderivative in A.

*Proof.* We will prove (i) using Green's theorem – we could give a proof that didn't rely on Green's, but it would be quite similar in flavor to the proof of Green's theorem.

Let R be the region inside the curve. And write f = u + iv. Now we write out the integral as follows

$$\int_C f(z) \, dz = \int_C (u + iv) \, (dx + idy) = \int_C (u \, dx - v \, dy) + i(v \, dx + u \, dy).$$

Let's apply Green's theorem to the real and imaginary pieces separately. First the real piece:

$$\int_C u \, dx - v \, dy = \int_R (-v_x - u_y) \, dx \, dy = 0.$$

We get 0 because the Cauchy-Riemann equations say  $u_v = -v_x$ , so  $-v_x - u_v = 0$ .

Likewise for the imaginary piece:

$$\int_C v \, dx + u \, dy = \int_R (u_x - v_y) \, dx \, dy = 0.$$

We get 0 because the Cauchy-Riemann equations say  $u_x = v_y$ , so  $u_x - v_y = 0$ .

To see part (i') you should draw a few curves that intersect themselves and convince yourself that they can be broken into a sum of simple closed curves. Thus, (i') follows from (i).<sup>1</sup>

Part (ii) follows from (i) and Theorem 3.9.

To see (iii), pick a base point  $z_0 \in A$  and let

$$F(z) = \int_{z_0}^z f(w) \, dw.$$

Here the integral is over any path in A connecting  $z_0$  to z. By part (ii), F(z) is well defined. If we can show that F'(z) = f(z) then we'll be done. Doing this amounts to managing the notation to apply the fundamental theorem of calculus and the Cauchy-Riemann equations. So, let's write

$$f(z) = u(x, y) + iv(x, y), \quad F(z) = U(x, y) + iV(x, y).$$

Then we can write

$$\frac{\partial f}{\partial x} = u_x + iv_x$$
, etc.

We can formulate the Cauchy-Riemann equations for F(z) as

$$F'(z) = \frac{\partial F}{\partial x} = \frac{1}{i} \frac{\partial F}{\partial y}$$
 (2a)

i.e.

$$F'(z) = U_x + iV_x = \frac{1}{i}(U_y + iV_y) = V_y - iU_y.$$
 (2b)

<sup>&</sup>lt;sup>1</sup>In order to truly prove part (i') we would need a more technically precise definition of simply connected so we could say that all closed curves within A can be continuously deformed to each other.

For reference, we note that using the path  $\gamma(t) = x(t) + iy(t)$ , with  $\gamma(0) = z_0$  and  $\gamma(b) = z$  we have

$$F(z) = \int_{z_0}^{z} f(w) dw = \int_{z_0}^{z} (u(x, y) + iv(x, y))(dx + idy)$$
$$= \int_{0}^{b} (u(x(t), y(t)) + iv(x(t), y(t))(x'(t) + iy'(t)) dt.$$
(3)

Our goal now is to prove that the Cauchy-Riemann equations given in Equation 3 hold for F(z). The figure below shows an arbitrary path from  $z_0$  to z, which can be used to compute F(z). To compute the partials of F we'll need the straight lines that continue C to z + h or z + ih.

Paths for proof of Cauchy's theorem

To prepare the rest of the argument we remind you that the fundamental theorem of calculus implies

$$\lim_{h \to 0} \frac{\int_0^h g(t) \, dt}{h} = g(0). \tag{4}$$

(That is, the derivative of the integral is the original function.)

First we'll look at  $\frac{\partial F}{\partial x}$ . So, fix z = x + iy. Looking at the paths in the figure above we have

$$F(z+h) - F(z) = \int_{C+C_x} f(w) \, dw - \int_C f(w) \, dw = \int_{C_x} f(w) \, dw.$$

The curve  $C_x$  is parametrized by  $\gamma(t) = x + t + iy$ , with  $0 \le t \le h$ . So,

$$\frac{\partial F}{\partial x} = \lim_{h \to 0} \frac{F(z+h) - F(z)}{h} = \lim_{h \to 0} \frac{\int_{C_x} f(w) \, dw}{h}$$

$$= \lim_{h \to 0} \frac{\int_0^h u(x+t,y) + iv(x+t,y) \, dt}{h}$$

$$= u(x,y) + iv(x,y)$$

$$= f(z). \tag{5}$$

The second to last equality follows from Equation 4.

Similarly, we get (remember: w = z + it, so dw = i dt)

$$\frac{1}{i}\frac{\partial F}{\partial y} = \lim_{h \to 0} \frac{F(z+ih) - F(z)}{ih} = \lim_{h \to 0} \frac{\int_{C_y} f(w) \, dw}{ih}$$

$$= \lim_{h \to 0} \frac{\int_0^h u(x, y+t) + iv(x, y+t) \, i \, dt}{ih}$$

$$= u(x, y) + iv(x, y)$$

$$= f(z). \tag{6}$$

Together Equations 5 and 6 show

$$f(z) = \frac{\partial F}{\partial x} = \frac{1}{i} \frac{\partial F}{\partial y}$$

By Equation 2a we have shown that F is analytic and F' = f.  $\square$ 

## 3.7 Extensions of Cauchy's theorem

Cauchy's theorem requires that the function f(z) be analytic on a simply connected region. In cases where it is not, we can extend it in a useful way.

Suppose R is the region between the two simple closed curves  $C_1$  and  $C_2$ . Note, both  $C_1$  and  $C_2$  are oriented in a counterclockwise direction.

**Theorem 3.14.** (Extended Cauchy's theorem) If f(z) is analytic on R then

$$\int_{C_1 - C_2} f(z) \, dz = 0.$$

*Proof.* The proof is based on the following figure. We 'cut' both  $C_1$  and  $C_2$  and connect them by two copies of  $C_3$ , one in each direction. (In the figure we have drawn the two copies of  $C_3$  as separate curves, in reality they are the same curve traversed in opposite directions.)

With  $C_3$  acting as a cut, the region enclosed by  $C_1 + C_3 - C_2 - C_3$  is simply connected, so Cauchy's Theorem 3.13 applies. We get

$$\int_{C_1 + C_3 - C_2 - C_3} f(z) \, dz = 0$$

The contributions of  $C_3$  and  $-C_3$  cancel, which leaves  $\int_{C_1-C_2} f(z) dz = 0$ . QED

**Note.** This clearly implies  $\int_{C_1} f(z) dz = \int_{C_2} f(z) dz$ .

**Example 3.15.** Let f(z) = 1/z. f(z) is defined and analytic on the punctured plane.

Punctured plane:  $\mathbf{C} - \{0\}$ 

**Question:** What values can  $\int_C f(z) dz$  take for C a simple closed curve (positively oriented) in the plane?

Solution: We have two cases (i)  $C_1$  not around 0, and (ii)  $C_2$  around 0

Case (i): Cauchy's theorem applies directly because the interior does not contain the problem point at the origin. Thus,

$$\int_{C_1} f(z) \, dz = 0.$$

Case (ii): we will show that

$$\int_{C_2} f(z) dz = 2\pi i.$$

Let  $C_3$  be a small circle of radius a centered at 0 and entirely inside  $C_2$ .

Figure for part (ii)

By the extended Cauchy theorem we have

$$\int_{C_2} f(z) dz = \int_{C_3} f(z) dz = \int_0^{2\pi} i dt = 2\pi i.$$

Here, the line integral for  $C_3$  was computed directly using the usual parametrization of a circle.

**Answer to the question:** The only possible values are 0 and  $2\pi i$ .

We can extend this answer in the following way:

If C is not simple, then the possible values of

$$\int_C f(z) \, dz$$

are  $2\pi ni$ , where n is the number of times C goes (counterclockwise) around the origin 0.

**Definition.** n is called the *winding number* of C around 0. n also equals the number of times C crosses the positive x-axis, counting +1 for crossing from below and -1 for crossing from above.

A curve with winding number 2 around the origin.

**Example 3.16.** A further extension: using the same trick of cutting the region by curves to make it simply connected we can show that if f is analytic in the region R shown below then

$$\int_{C_1-C_2-C_3-C_4} f(z)\, dz = 0.$$

That is,  $C_1 - C_2 - C_3 - C_4$  is the boundary of the region R.

**Orientation.** It is important to get the orientation of the curves correct. One way to do this is to make sure that the region R is always to the left as you traverse the curve. In the above example. The region is to the right as you traverse  $C_2$ ,  $C_3$  or  $C_4$  in the direction indicated. This is why we put a minus sign on each when describing the boundary.

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 4 Notes**

Jeremy Orloff

# 4 Cauchy's integral formula

#### 4.1 Introduction

Cauchy's theorem is a big theorem which we will use almost daily from here on out. Right away it will reveal a number of interesting and useful properties of analytic functions. More will follow as the course progresses.

If you learn just one theorem this week it should be Cauchy's integral formula!

We start with a statement of the theorem for functions. After some examples, we'll give a generalization to all derivatives of a function. After some more examples we will prove the theorems. After that we will see some remarkable consequences that follow fairly directly from the Cauchy's formula.

# 4.2 Cauchy's integral for functions

**Theorem 4.1.** (Cauchy's integral formula) Suppose C is a simple closed curve and the function f(z) is analytic on a region containing C and its interior. We assume C is oriented counterclockwise. Then for any  $z_0$  inside C:

$$f(z_0) = \frac{1}{2\pi i} \int_C \frac{f(z)}{z - z_0} dz$$
 (1)

Cauchy's integral formula: simple closed curve C, f(z) analytic on and inside C.

This is remarkable: it says that knowing the values of f on the boundary curve C means we know everything about f inside C!! This is probably unlike anything you've encountered with functions of real variables.

**Aside 1.** With a slight change of notation (z becomes w and  $z_0$  becomes z) we often write the formula as

$$f(z) = \frac{1}{2\pi i} \int_C \frac{f(w)}{w - z} dw$$
 (2)

**Aside 2.** We're not being entirely fair to functions of real variables. We will see that for f = u + iv

the real and imaginary parts u and v have many similar remarkable properties. u and v are called conjugate harmonic functions.

### 4.2.1 Examples

**Example 4.2.** Compute  $\int_C \frac{e^{z^2}}{z-2} dz$ , where C is the curve shown.

Solution: Let  $f(z) = e^{z^2}$ . f(z) is entire. Since C is a simple closed curve (counterclockwise) and z = 2 is inside C, Cauchy's integral formula says that the integral is  $2\pi i f(2) = 2\pi i e^4$ .

**Example 4.3.** Do the same integral as the previous example with *C* the curve shown.

Solution: Since  $f(z) = e^{z^2}/(z-2)$  is analytic on and inside C, Cauchy's theorem says that the integral is 0.

**Example 4.4.** Do the same integral as the previous examples with C the curve shown.

Solution: This one is trickier. Let  $f(z) = e^{z^2}$ . The curve C goes around 2 twice in the clockwise direction, so we break C into  $C_1 + C_2$  as shown in the next figure.

These are both simple closed curves, so we can apply the Cauchy integral formula to each separately. (The negative signs are because they go clockwise around z = 2.)

$$\int_C \frac{f(z)}{z-2} \, dz = \int_{C_1} \frac{f(z)}{z-2} \, dz + \int_{C_2} \frac{f(z)}{z-2} \, dz = -2\pi i f(2) - 2\pi i f(2) = -4\pi i f(2).$$

# 4.3 Cauchy's integral formula for derivatives

Cauchy's integral formula is worth repeating several times. So, now we give it for all derivatives  $f^{(n)}(z)$  of f. This will include the formula for functions as a special case.

**Theorem 4.5.** Cauchy's integral formula for derivatives. If f(z) and C satisfy the same hypotheses as for Cauchy's integral formula then, for all z inside C we have

$$f^{(n)}(z) = \frac{n!}{2\pi i} \int_C \frac{f(w)}{(w-z)^{n+1}} dw, \quad n = 0, 1, 2, \dots$$
 (3)

where, C is a simple closed curve, oriented counterclockwise, z is inside C and f(w) is analytic on and inside C.

**Example 4.6.** Evaluate 
$$I = \int_C \frac{e^{2z}}{z^4} dz$$
 where  $C: |z| = 1$ .

Solution: With Cauchy's formula for derivatives this is easy. Let  $f(z) = e^{2z}$ . Then,

$$I = \int_C \frac{f(z)}{z^4} dz = \frac{2\pi i}{3!} f'''(0) = \frac{8}{3}\pi i.$$

**Example 4.7.** Now Let C be the contour shown below and evaluate the same integral as in the previous example.

Solution: Again this is easy: the integral is the same as the previous example, i.e.  $I = \frac{8}{3}\pi i$ .

## 4.3.1 Another approach to some basic examples

Suppose C is a simple closed curve around 0. We have seen that

$$\int_C \frac{1}{z} dz = 2\pi i.$$

The Cauchy integral formula gives the same result. That is, let f(z) = 1, then the formula says

$$\frac{1}{2\pi i} \int_C \frac{f(z)}{z - 0} \, dz = f(0) = 1.$$

Likewise Cauchy's formula for derivatives shows

$$\int_C \frac{1}{(z)^n} dz = \int_C \frac{f(z)}{z^{n+1}} dz = f^{(n)}(0) = 0, \quad \text{for integers } n > 1.$$

#### 4.3.2 More examples

Example 4.8. Compute

$$\int_C \frac{\cos(z)}{z(z^2+8)} dz$$
 over the contour shown.

Solution: Let  $f(z) = \cos(z)/(z^2 + 8)$ . f(z) is analytic on and inside the curve C. That is, the roots of  $z^2 + 8$  are outside the curve. So, we rewrite the integral as

$$\int_C \frac{\cos(z)/(z^2+8)}{z} dz = \int_C \frac{f(z)}{z} dz = 2\pi i f(0) = 2\pi i \frac{1}{8} = \frac{\pi i}{4}.$$

**Example 4.9.** Compute  $\int_C \frac{1}{(z^2+4)^2} dz$  over the contour shown.

Solution: We factor the denominator as

$$\frac{1}{(z^2+4)^2} = \frac{1}{(z-2i)^2(z+2i)^2}.$$

Let

$$f(z) = \frac{1}{(z+2i)^2}.$$

Clearly f(z) is analytic inside C. So, by Cauchy's formula for derivatives:

$$\int_C \frac{1}{(z^2+4)^2} dz = \int_C \frac{f(z)}{(z-2i)^2} = 2\pi i f'(2i) = 2\pi i \left[ \frac{-2}{(z+2i)^3} \right]_{z=2i} = \frac{4\pi i}{64i} = \frac{\pi}{16}$$

**Example 4.10.** Compute  $\int_C \frac{z}{z^2 + 4} dz$  over the curve C shown below.

Solution: The integrand has singularities at  $\pm 2i$  and the curve C encloses them both. The solution to the previous solution won't work because we can't find an appropriate f(z) that is analytic on the whole interior of C. Our solution is to split the curve into two pieces. Notice that  $C_3$  is traversed both forward and backward.

Split the original curve C into 2 pieces that each surround just one singularity.

We have

$$\frac{z}{z^2 + 4} = \frac{z}{(z - 2i)(z + 2i)}.$$

We let

$$f_1(z) = \frac{z}{z + 2i}$$
 and  $f_2(z) = \frac{z}{z - 2i}$ .

So,

$$\frac{z}{z^2 + 4} = \frac{f_1(z)}{z - 2i} = \frac{f_2(z)}{z + 2i}.$$

The integral, can be written out as

$$\int_C \frac{z}{z^2 + 4} \, dz = \int_{C_1 + C_3 - C_3 + C_2} \frac{z}{z^2 + 4} \, dz = \int_{C_1 + C_3} \frac{f_1(z)}{z - 2i} \, dz + \int_{C_2 - C_3} \frac{f_2(z)}{z + 2i} \, dz$$

Since  $f_1$  is analytic inside the simple closed curve  $C_1 + C_3$  and  $f_2$  is analytic inside the simple closed curve  $C_2 - C_3$ , Cauchy's formula applies to both integrals. The total integral equals

$$2\pi i (f_1(2i) + f_2(-2i)) = 2\pi i (1/2 + 1/2) = 2\pi i.$$

**Remarks.** 1. We could also have done this problem using partial fractions:

$$\frac{z}{(z-2i)(z+2i)} = \frac{A}{z-2i} + \frac{B}{z+2i}.$$

It will turn out that  $A = f_1(2i)$  and  $B = f_2(-2i)$ . It is easy to apply the Cauchy integral formula to both terms.

2. **Important note.** In an upcoming topic we will formulate the Cauchy residue theorem. This will allow us to compute the integrals in Examples 4.8-4.10 in an easier and less ad hoc manner.

## 4.3.3 The triangle inequality for integrals

We discussed the triangle inequality in the Topic 1 notes. It says that

$$|z_1 + z_2| \le |z_1| + |z_2|,\tag{4a}$$

with equality if and only if  $z_1$  and  $z_2$  lie on the same ray from the origin.

A useful variant of this statement is

$$|z_1| - |z_2| \le |z_1 - z_2|. \tag{4b}$$

This follows because Equation 4a implies

$$|z_1| = |(z_1 - z_2) + z_2| \le |z_1 - z_2| + |z_2|.$$

Now subtracting  $z_2$  from both sides give Equation 4b

Since an integral is basically a sum, this translates to the triangle inequality for integrals. We'll state it in two ways that will be useful to us.

**Theorem 4.11.** (Triangle inequality for integrals) Suppose g(t) is a complex valued function of a real variable, defined on  $a \le t \le b$ . Then

$$\left| \int_{a}^{b} g(t) dt \right| \leq \int_{a}^{b} |g(t)| dt,$$

with equality if and only if the values of g(t) all lie on the same ray from the origin.

*Proof.* This follows by approximating the integral as a Riemann sum.

$$\left| \int_a^b g(t) \, dt \right| \approx \left| \sum g(t_k) \Delta t \right| \le \sum |g(t_k)| \Delta t \approx \int_a^b |g(t)| \, dt.$$

The middle inequality is just the standard triangle inequality for sums of complex numbers.  $\square$ 

**Theorem 4.12.** (Triangle inequality for integrals II) For any function f(z) and any curve  $\gamma$ , we have

$$\left| \int_{\gamma} f(z) \, dz \right| \le \int_{\gamma} |f(z)| \, |dz|.$$

Here  $dz = \gamma'(t) dt$  and  $|dz| = |\gamma'(t)| dt$ .

*Proof.* This follows immediately from the previous theorem:

$$\left| \int_{\gamma} f(z) dz \right| = \left| \int_{a}^{b} f(\gamma(t)) \gamma'(t) dt \right| \le \int_{a}^{b} |f(\gamma(t))| |\gamma'(t)| dt = \int_{\gamma} |f(z)| |dz|.$$

Corollary. If |f(z)| < M on C then

$$\left| \int_C f(z) \, dz \right| \le M \cdot (\text{length of } C).$$

*Proof.* Let  $\gamma(t)$ , with  $a \le t \le b$ , be a parametrization of C. Using the triangle inequality

$$\left| \int_C f(z) dz \right| \le \int_C |f(z)| |dz| = \int_a^b |f(\gamma(t))| |\gamma'(t)| dt \le \int_a^b M|\gamma'(t)| dt = M \cdot (\text{length of } C).$$

Here we have used that

$$|\gamma'(t)| dt = \sqrt{(x')^2 + (\gamma')^2} dt = ds,$$

the arclength element.

## **Example 4.13.** Compute the real integral

$$I = \int_{-\infty}^{\infty} \frac{1}{(x^2 + 1)^2} dx$$

Solution: The trick is to integrate  $f(z) = 1/(z^2 + 1)^2$  over the closed contour  $C_1 + C_R$  shown, and then show that the contribution of  $C_R$  to this integral vanishes as R goes to  $\infty$ .

The only singularity of

$$f(z) = \frac{1}{(z+i)^2 (z-i)^2}$$

inside the contour is at z = i. Let

$$g(z) = \frac{1}{(z+i)^2}.$$

Since g is analytic on and inside the contour, Cauchy's formula gives

$$\int_{C_1+C_R} f(z) dz = \int_{C_1+C_R} \frac{g(z)}{(z-i)^2} dz = 2\pi i g'(i) = 2\pi i \frac{-2}{(2i)^3} = \frac{\pi}{2}.$$

We parametrize  $C_1$  by

$$\gamma(x) = x$$
, with  $-R \le x \le R$ .

So,

$$\int_{C_1} f(z) dz = \int_{-R}^{R} \frac{1}{(x^2 + 1)^2} dx.$$

This goes to I (the value we want to compute) as  $R \to \infty$ .

Next, we parametrize  $C_R$  by

$$\gamma(\theta) = Re^{i\theta}$$
, with  $0 \le \theta \le \pi$ .

So,

$$\int_{C_{P}} f(z) dz = \int_{0}^{\pi} \frac{1}{(R^{2}e^{2i\theta} + 1)^{2}} iRe^{i\theta} d\theta$$

By the triangle inequality for integrals, if R > 1

$$\left| \int_{C_R} f(z) \, dz \right| \le \int_0^{\pi} \left| \frac{1}{(R^2 e^{2i\theta} + 1)^2} i R e^{i\theta} \right| \, d\theta. \tag{5}$$

From the triangle equality in the form Equation 4b we know that

$$|R^2e^{2i\theta} + 1| > |R^2e^{2i\theta}| - |1| = R^2 - 1.$$

Thus,

$$\frac{1}{|R^2 \mathrm{e}^{2i\theta} + 1|} \le \frac{1}{R^2 - 1} \quad \Rightarrow \quad \frac{1}{|R^2 \mathrm{e}^{2i\theta} + 1|^2} \le \frac{1}{(R^2 - 1)^2}.$$

Using Equation 5, we then have

$$\left| \int_{C_R} f(z) \, dz \right| \le \int_0^{\pi} \left| \frac{1}{(R^2 e^{2i\theta} + 1)^2} \, i R e^{i\theta} \right| \, d\theta \le \int_0^{\pi} \frac{R}{(R^2 - 1)^2} \, d\theta = \frac{\pi R}{(R^2 - 1)^2}$$

Clearly this goes to 0 as R goes to infinity. Thus, the integral over the contour  $C_1 + C_R$  goes to I as R gets large. But

$$\int_{C_1+C_R} f(z) \, dz = \pi/2$$

for all R > 1. We can therefore conclude that  $I = \pi/2$ .

As a sanity check, we note that our answer is real and positive as it needs to be.

### 4.4 Proof of Cauchy's integral formula

#### 4.4.1 A useful theorem

Before proving the theorem we'll need a theorem that will be useful in its own right.

**Theorem 4.14.** (A second extension of Cauchy's theorem) Suppose that A is a simply connected region containing the point  $z_0$ . Suppose g is a function which is

- 1. Analytic on  $A \{z_0\}$
- 2. Continuous on A. (In particular, g does not blow up at  $z_0$ .)

Then,

$$\int_C g(z) \, dz = 0$$

for all closed curves C in A.

*Proof.* The extended version of Cauchy's theorem in the Topic 3 notes tells us that

$$\int_C g(z) dz = \int_{C_r} g(z) dz,$$

where  $C_r$  is a circle of radius r around  $z_0$ .

Since g(z) is continuous we know that |g(z)| is bounded inside  $C_r$ . Say, |g(z)| < M. The corollary to the triangle inequality says that

$$\left| \int_{C_r} g(z) dz \right| \le M \text{ (length of } C_r) = M 2\pi r.$$

Since r can be as small as we want, this implies that

$$\int_{C_r} g(z) \, dz = 0.$$

**Note.** Using this, we can show that g(z) is, in fact, analytic at  $z_0$ . The proof will be the same as in our proof of Cauchy's theorem that g(z) has an antiderivative.

### 4.4.2 Proof of Cauchy's integral formula

We reiterate Cauchy's integral formula from Equation 1:  $f(z_0) = \frac{1}{2\pi i} \int_C \frac{f(z)}{z - z_0} dz$ .

*Proof.* (of Cauchy's integral formula) We use a trick that is useful enough to be worth remembering. Let

$$g(z) = \frac{f(z) - f(z_0)}{z - z_0}.$$

Since f(z) is analytic on A, we know that g(z) is analytic on  $A - \{z_0\}$ . Since the derivative of f exists at  $z_0$ , we know that

$$\lim_{z \to z_0} g(z) = f'(z_0).$$

That is, if we define  $g(z_0) = f'(z_0)$  then g is continuous at  $z_0$ . From the extension of Cauchy's theorem just above, we have

$$\int_C g(z) \, dz = 0, \quad \text{i.e.} \quad \int_C \frac{f(z) - f(z_0)}{z - z_0} \, dz = 0.$$

Thus

$$\int_C \frac{f(z)}{z - z_0} \, dz = \int_C \frac{f(z_0)}{z - z_0} \, dz = f(z_0) \int_C \frac{1}{z - z_0} \, dz = 2\pi i f(z_0).$$

The last equality follows from our, by now, well known integral of  $1/(z-z_0)$  on a loop around  $z_0$ .

## 4.5 Proof of Cauchy's integral formula for derivatives

Recall that Cauchy's integral formula in Equation 3 says

$$f^{(n)}(z) = \frac{n!}{2\pi i} \int_C \frac{f(w)}{(w-z)^{n+1}} dw, \quad n = 0, 1, 2, \dots$$

First we'll offer a quick proof which captures the reason behind the formula, and then a formal proof.

Quick proof: We have an integral representation for f(z),  $z \in A$ , we use that to find an integral representation for f'(z),  $z \in A$ .

$$f'(z) = \frac{d}{dz} \left[ \frac{1}{2\pi i} \int_C \frac{f(w)}{w - z} dw \right] = \frac{1}{2\pi i} \int_C \frac{d}{dz} \left( \frac{f(w)}{w - z} \right) dw = \frac{1}{2\pi i} \int_C \frac{f(w)}{(w - z)^2} dw$$

(Note, since  $z \in A$  and  $w \in C$ , we know that  $w - z \neq 0$ ) Thus,

$$f'(z) = \frac{1}{2\pi i} \int_C \frac{f(w)}{(w-z)^2} dw$$

Now, by iterating this process, i.e. by mathematical induction, we can show the formula for higher order derivatives.

Formal proof: We do this by taking the limit of

$$\lim_{\Delta z \to 0} \frac{f(z + \Delta z) - f(z)}{\Delta z}$$

using the integral representation of both terms:

$$f(z + \Delta z) = \frac{1}{2\pi i} \int_C \frac{f(w)}{w - z - \Delta z} dw, \qquad f(z) = \frac{1}{2\pi i} \int_C \frac{f(w)}{w - z} dw$$

Now, using a little algebraic manipulation we get

$$\frac{f(z + \Delta z) - f(z)}{\Delta z} = \frac{1}{2\pi i \Delta z} \int_C \frac{f(w)}{w - z - \Delta z} - \frac{f(w)}{w - z} dw$$
$$= \frac{1}{2\pi i \Delta z} \int_C \frac{f(w)\Delta z}{(w - z - \Delta z)(w - z)} dw$$
$$= \frac{1}{2\pi i} \int_C \frac{f(w)}{(w - z)^2 - \Delta z(w - z)} dw$$

Letting  $\Delta z$  go to 0, we get Cauchy's formula for f'(z):

$$f'(z) = \frac{1}{2\pi i} \int_C \frac{f(w)}{(w-z)^2} dw$$

There is no problem taking the limit under the integral sign because everything is continuous and the denominator is never 0.  $\square$ 

# 4.6 Amazing consequence of Cauchy's integral formula

#### 4.6.1 Existence of derivatives

**Theorem.** Suppose f(z) is analytic on a region A. Then, f has derivatives of all order.

*Proof.* This follows from Cauchy's integral formula for derivatives. That is, we have a formula for all the derivatives, so in particular the derivatives all exist.

A little more precisely: for any point z in A we can put a small disk around  $z_0$  that is entirely contained in A. Let C be the boundary of the disk, then Cauchy's formula gives a formula for all the derivatives  $f^{(n)}(z_0)$  in terms of integrals over C. In particular, those derivatives exist.  $\square$ 

**Remark.** If you look at the proof of Cauchy's formula for derivatives you'll see that f having derivatives of all orders boils down to 1/(w-z) having derivatives of all orders for w on a curve not containing z.

**Important remark.** We have at times assumed that for f = u + iv analytic, u and v have continuous higher order partial derivatives. This theorem confirms that fact. In particular,  $u_{xy} = u_{yx}$ , etc.

#### 4.6.2 Cauchy's inequality

**Theorem 4.15.** (Cauchy's inequality) Let  $C_R$  be the circle  $|z-z_0|=R$ . Assume that f(z) is analytic on  $C_R$  and its interior, i.e. on the disk  $|z-z_0| \le R$ . Finally let  $M_R = \max |f(z)|$  over z on  $C_R$ . Then

$$|f^{(n)}(z_0)| \le \frac{n! M_R}{R^n}, \quad n = 1, 2, 3, \dots$$
 (6)

*Proof.* Using Cauchy's integral formula for derivatives (Equation 3) we have

$$|f^{(n)}(z_0)| \le \frac{n!}{2\pi} \int_{C_P} \frac{|f(w)|}{|w - z_0|^{n+1}} |dw| \le \frac{n!}{2\pi} \frac{M_R}{R^{n+1}} \int_{C_P} |dw| = \frac{n!}{2\pi} \frac{M_R}{R^{n+1}} \cdot 2\pi R$$

#### 4.6.3 Liouville's theorem

**Theorem 4.16.** (Liouville's theorem) Assume f(z) is entire and suppose it is bounded in the complex plane, namely |f(z)| < M for all  $z \in \mathbb{C}$  then f(z) is constant.

*Proof.* For any circle of radius R around  $z_0$  the Cauchy inequality says  $|f'(z_0)| \leq \frac{M}{R}$ . But, R can be as large as we like so we conclude that  $|f'(z_0)| = 0$  for every  $z_0 \in \mathbb{C}$ . Since the derivative is 0, the function itself is constant.

In short:

If 
$$f$$
 is entire and bounded then  $f$  is constant.

**Note.**  $P(z) = a_n z^n + ... + a_0$ ,  $\sin(z)$ ,  $e^z$  are all entire but **not bounded**.

Now, practically for free, we get the fundamental theorem of algebra.

**Corollary.** (Fundamental theorem of algebra) Any polynomial P of degree  $n \ge 1$ , i.e.

$$P(z) = a_0 + a_1 z + ... + a_n z^n, \ a_n \neq 0,$$

has exactly n roots.

*Proof.* There are two parts to the proof.

**Hard part**: Show that *P* has at least one root.

This is done by contradiction, together with Liouville's theorem. Suppose P(z) does not have a zero. Then

- 1. f(z) = 1/P(z) is entire. This is obvious because (by assumption) P(z) has no zeros.
- 2. f(z) is bounded. This follows because 1/P(z) goes to 0 as |z| goes to  $\infty$ .

(It is clear that |1/P(z)| goes to 0 as z goes to infinity, i.e. |1/P(z)| is small outside a large circle. So |1/P(z)| is bounded by M.)

So, by Liouville's theorem f(z) is constant, and therefore P(z) must be constant as well. But this is a contradiction, so the hypothesis of "No zeros" must be wrong, i.e. P must have a zero.

Easy part: P has exactly n zeros. Let  $z_0$  be one zero. We can factor  $P(z) = (z - z_0)Q(z)$ . Q(z) has degree n - 1. If n - 1 > 0, then we can apply the result to Q(z). We can continue this process until the degree of Q is 0.

#### 4.6.4 Maximum modulus principle

Briefly, the maximum modulus principle states that if f is analytic and not constant in a domain A then |f(z)| has no relative maximum in A and the absolute maximum of |f| occurs on the boundary of A.

In order to prove the maximum modulus principle we will first prove the mean value property. This will give you a good feel for the maximum modulus principle. It is also important and interesting in its own right.

**Theorem 4.17.** (Mean value property) Suppose f(z) is analytic on the closed disk of radius r centered at  $z_0$ , i.e. the set  $|z - z_0| \le r$ . Then,

$$f(z_0) = \frac{1}{2\pi} \int_0^{2\pi} f(z_0 + re^{i\theta}) d\theta$$
 (7)

*Proof.* This is an application of Cauchy's integral formula on the disk  $D_r = |z - z_0| \le r$ .

We can parametrize  $C_r$ , the boundary of  $D_r$ , as

$$\gamma(\theta) = z_0 + re^{i\theta}$$
, with  $0 \le \theta \le 2\pi$ , so  $\gamma'(\theta) = ire^{i\theta}$ .

By Cauchy's formula we have

$$f(z_0) = \frac{1}{2\pi i} \int_{C_{\tau}} \frac{f(z)}{z - z_0} dz = \frac{1}{2\pi i} \int_0^{2\pi} \frac{f(z_0 + re^{i\theta})}{re^{i\theta}} i re^{i\theta} d\theta = \frac{1}{2\pi} \int_0^{2\pi} f(z_0 + re^{i\theta}) d\theta$$

This proves the property.  $\square$ 

In words, the mean value property says  $f(z_0)$  is the arithmetic mean of the values on the circle.

Now we can state and prove the maximum modulus principle. We state the assumptions carefully. When applying this theorem, it is important to verify that the assumptions are satisfied.

**Theorem 4.18.** (Maximum modulus principle) Suppose f(z) is analytic in a connected region A and  $z_0$  is a point in A.

- 1. If |f| has a relative maximum at  $z_0$  then f(z) is constant in a neighborhood of  $z_0$ .
- 2. If A is bounded and connected, and f is continuous on A and its boundary, then either f is constant or the absolute maximum of |f| occurs only on the boundary of A.

*Proof.* **Part** (1): The argument for part (1) is a little fussy. We will use the mean value property and the triangle inequality from Theorem 4.11.

Since  $z_0$  is a relative maximum of |f|, for every small enough circle  $C: |z-z_0| = r$  around  $z_0$  we have  $|f(z)| \le |f(z_0)|$  for z on C. Therefore, by the mean value property and the triangle inequality

$$|f(z_0)| = \left| \frac{1}{2\pi} \int_0^{2\pi} f(z_0 + re^{i\theta}) d\theta \right|$$
 (mean value property)  

$$\leq \frac{1}{2\pi} \int_0^{2\pi} |f(z_0 + re^{i\theta})| d\theta$$
 (triangle inequality)  

$$\leq \frac{1}{2\pi} \int_0^{2\pi} |f(z_0)| d\theta$$
 ( $|f(z_0 + re^{i\theta})| \leq |f(z_0)|$ )  

$$= |f(z_0)|$$

Since the beginning and end of the above are both  $|f(z_0)|$  all the inequalities in the chain must be equalities.

The first inequality can only be an equality if for all  $\theta$ ,  $f(z_0 + re^{i\theta})$  lie on the same ray from the origin, i.e. have the same argument or are 0.

The second inequality can only be an equality if all  $|f(z_0 + re^{i\theta})| = |f(z_0)|$ . So we have all  $f(z_0 + re^{i\theta})$  have the same magnitude and the same argumeny. This implies they are all the same.

Finally, if f(z) is constant along the circle and  $f(z_0)$  is the average of f(z) over the circle then  $f(z) = f(z_0)$ , i.e. f is constant on a small disk around  $z_0$ .

**Part (2):** The assumptions that A is bounded and f is continuous on A and its boundary serve to guarantee that |f| has an absolute maximum (on A combined with its boundary). Part (1) guarantees that the absolute maximum can not lie in the interior of the region A unless f is constant. (This requires a bit more argument. Do you see why?) If the absolute maximum is not in the interior it must be on the boundary.  $\square$ 

**Example 4.19.** Find the maximum modulus of  $e^z$  on the unit square with  $0 \le x, y \le 1$ .

Solution:

$$|e^{x+iy}| = e^x$$
,

so the maximum is when x = 1,  $0 \le y \le 1$  is arbitrary. This is indeed on the boundary of the unit square

**Example 4.20.** Find the maximum modulus for  $\sin(z)$  on the square  $[0, 2\pi] \times [0, 2\pi]$ .

Solution: We use the formula

$$\sin(z) = \sin x \cosh y + i \cos x \sinh y$$
.

So,

$$|\sin(z)|^2 = \sin^2 x \cosh^2 y + \cos^2 x \sinh^2 y$$
  
=  $\sin^2 x \cosh^2 y + (1 - \sin^2 x) \sinh^2 y$   
=  $\sin^2 x + \sinh^2 y$ .

We know the maximum over x of  $\sin^2(x)$  is at  $x = \pi/2$  and  $x = 3\pi/2$ . The maximum of  $\sinh^2 y$  is at  $y = 2\pi$ . So maximum modulus is

$$\sqrt{1+\sinh^2(2\pi)} = \sqrt{\cosh^2(2\pi)} = \cosh(2\pi).$$

This occurs at the points

$$z = x + iy = \frac{\pi}{2} + 2\pi i$$
, and  $z = \frac{3\pi}{2} + 2\pi i$ .

Both these points are on the boundary of the region.

**Example 4.21.** Suppose f(z) is entire. Show that if  $\lim_{z\to\infty} f(z) = 0$  then  $f(z) \equiv 0$ .

Solution: This is a standard use of the maximum modulus principle. The strategy is to show that the maximum of |f(z)| is not on the boundary (of the appropriately chosen region), so f(z) must be constant.

Fix  $z_0$ . For  $R > |z_0|$  let  $M_R$  be the maximum of |f(z)| on the circle |z| = R. The maximum modulus theorem says that  $|f(z_0)| < M_R$ . Since f(z) goes to 0, as R goes to infinity, we must have  $M_R$  also goes to 0. This means  $|f(z_0)| = 0$ . Since this is true for any  $z_0$ , we have  $f(z) \equiv 0$ .

**Example 4.22.** Here is an example of why you need A to be bounded in the maximum modulus theorem. Let A be the upper half-plane

$$Im(z) > 0$$
.

So the boundary of *A* is the real axis.

Let 
$$f(z) = e^{-iz}$$
. We have

$$|f(x)| = |e^{-ix}| = 1$$

for x along the real axis. Since  $|f(2i)| = |e^2| > 1$ , we see |f| cannot take its maximum along the boundary of A.

Of course, it can't take its maximum in the interior of A either. What happens here is that f(z) doesn't have a maximum modulus. Indeed |f(z)| goes to infinity along the positive imaginary axis.

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 5 Notes**

Jeremy Orloff

## 5 Introduction to harmonic functions

#### 5.1 Introduction

Harmonic functions appear regularly and play a fundamental role in math, physics and engineering. In this topic we'll learn the definition, some key properties and their tight connection to complex analysis. The key connection to 18.04 is that both the real and imaginary parts of analytic functions are harmonic. We will see that this is a simple consequence of the Cauchy-Riemann equations. In the next topic we will look at some applications to hydrodynamics.

#### 5.2 Harmonic functions

We start by defining harmonic functions and looking at some of their properties.

**Definition 5.1.** A function u(x, y) is called harmonic if it is twice continuously differentiable and satisfies the following partial differential equation:

$$\nabla^2 u = u_{xx} + u_{yy} = 0. {1}$$

Equation 1 is called Laplace's equation. So a function is harmonic if it satisfies Laplace's equation. The operator  $\nabla^2$  is called the Laplacian and  $\nabla^2 u$  is called the Laplacian of u.

#### 5.3 Del notation

Here's a quick reminder on the use of the notation  $\nabla$ . For a function u(x, y) and a vector field  $\mathbf{F}(x, y) = (u, v)$ , we have

(i) 
$$\nabla = \left(\frac{\partial}{\partial x}, \frac{\partial}{\partial y}\right)$$

(ii) 
$$\operatorname{grad} u = \nabla u = (u_x, u_y)$$

(iii) 
$$\operatorname{curl} \mathbf{F} = \nabla \times \mathbf{F} = (v_x - u_y)$$

(iv) 
$$\operatorname{div} \mathbf{F} = \mathbf{\nabla} \cdot \mathbf{F} = u_x + v_y$$

(v) div grad 
$$u = \nabla \cdot \nabla u = \nabla^2 u = u_{xx} + u_{yy}$$

(vi) 
$$\operatorname{curl} \operatorname{grad} u = \nabla \times \nabla u = 0$$

(vii) 
$$\operatorname{div}\operatorname{curl}\mathbf{F} = \mathbf{\nabla}\cdot\mathbf{\nabla}\times\mathbf{F} = 0.$$

### **5.3.1** Analytic functions have harmonic pieces

The connection between analytic and harmonic functions is very strong. In many respects it mirrors the connection between  $e^z$  and sine and cosine.

Let z = x + iy and write f(z) = u(x, y) + iv(x, y).

**Theorem 5.2.** If f(z) = u(x, y) + iv(x, y) is analytic on a region A then both u and v are harmonic functions on A.

*Proof.* This is a simple consequence of the Cauchy-Riemann equations. Since  $u_x = v_y$  we have

$$u_{xx} = v_{yx}$$
.

Likewise,  $u_v = -v_x$  implies

$$u_{yy} = -v_{xy}.$$

Since  $v_{xy} = v_{yx}$  we have

$$u_{xx} + u_{yy} = v_{yx} - v_{xy} = 0.$$

Therefore u is harmonic. We can handle v similarly.  $\square$ 

**Note.** Since we know an analytic function is infinitely differentiable we know u and v have the required two continuous partial derivatives. This also ensures that the mixed partials agree, i.e.  $v_{xy} = v_{yx}$ .

To complete the tight connection between analytic and harmonic functions we show that any harmonic function is the real part of an analytic function.

**Theorem 5.3.** If u(x, y) is harmonic on a simply connected region A, then u is the real part of an analytic function f(z) = u(x, y) + iv(x, y).

*Proof.* This is similar to our proof that an analytic function has an antiderivative. First we come up with a candidate for f(z) and then show it has the properties we need. Here are the details broken down into steps 1-4.

1. Find a candidate, call it g(z), for f'(z):

If we had an analytic f with f = u + iv, then Cauchy-Riemann says that  $f' = u_x - iu_y$ . So, let's define

$$g = u_{x} - iu_{y}$$
.

This is our candidate for f'.

2. Show that g(z) is analytic:

Write  $g = \phi + i\psi$ , where  $\phi = u_x$  and  $\psi = -u_y$ . Checking the Cauchy-Riemann equations we have

$$\begin{bmatrix} \phi_x & \phi_y \\ \psi_x & \psi_y \end{bmatrix} = \begin{bmatrix} u_{xx} & u_{xy} \\ -u_{yx} & -u_{yy} \end{bmatrix}$$

Since u is harmonic we know  $u_{xx} = -u_{yy}$ , so  $\phi_x = \psi_y$ . It is clear that  $\phi_y = -\psi_x$ . Thus g satisfies the Cauchy-Riemann equations, so it is analytic.

3. Let f be an antiderivative of g:

Since A is simply connected our statement of Cauchy's theorem guarantees that g(z) has an antiderivative in A. We'll need to fuss a little to get the constant of integration exactly right. So, pick a base point  $z_0$  in A. Define the antiderivative of g(z) by

$$f(z) = \int_{z_0}^{z} g(z) dz + u(x_0, y_0).$$

(Again, by Cauchy's theorem this integral can be along any path in A from  $z_0$  to z.)

4. Show that the real part of f is u.

Let's write f = U + iV. So,  $f'(z) = U_x - iU_y$ . By construction

$$f'(z) = g(z) = u_x - iu_y.$$

This means the first partials of U and u are the same, so U and u differ by at most a constant. However, also by construction,

$$f(z_0) = u(x_0, y_0) = U(x_0, y_0) + iV(x_0, y_0),$$

So,  $U(x_0, y_0) = u(x_0, y_0)$  (and  $V(x_0, y_0) = 0$ ). Since they agree at one point we must have U = u, i.e. the real part of f is u as we wanted to prove.

**Important corollary.** *u* is infinitely differentiable.

*Proof.* By definition we only require a harmonic function u to have continuous second partials. Since the analytic f is infinitely differentiable, we have shown that so is u!

#### **5.3.2** Harmonic conjugates

**Definition.** If u and v are the real and imaginary parts of an analytic function, then we say u and v are harmonic conjugates.

**Note.** If f(z) = u + iv is analytic then so is if(z) = -v + iu. So, if u and v are harmonic conjugates and so are u and -v.

#### 5.4 A second proof that u and v are harmonic

This fact is important enough that we will give a second proof using Cauchy's integral formula. One benefit of this proof is that it reminds us that Cauchy's integral formula can transfer a general question on analytic functions to a question about the function 1/z. We start with an easy to derive fact.

**Fact.** The real and imaginary parts of f(z) = 1/z are harmonic away from the origin. Likewise for

$$g(z) = f(z - a) = \frac{1}{z - a}$$

away from the point z = a.

Proof. We have

$$\frac{1}{z} = \frac{x}{x^2 + y^2} - i \frac{y}{x^2 + y^2}.$$

It is a simple matter to apply the Laplacian and see that you get 0. We'll leave the algebra to you! The statement about g(z) follows in either exactly the same way, or by noting that the Laplacian is translation invariant.

**Second proof that** f **analytic implies** u **and** v **are harmonic.** We are proving that if f = u + iv is analytic then u and v are harmonic. So, suppose f is analytic at the point  $z_0$ . This means there is a disk of some radius, say r, around  $z_0$  where f is analytic. Cauchy's formula says

$$f(z) = \frac{1}{2\pi i} \int_{C_{-}} \frac{f(w)}{w - z} dw,$$

where  $C_r$  is the circle  $|w - z_0| = r$  and z is in the disk  $|z - z_0| < r$ .

Now, since the real and imaginary parts of 1/(w-z) are harmonic, the same must be true of the integral, which is limit of linear combinations of such functions. Since the circle is finite and f is continuous, interchanging the order of integration and differentiation is not a problem.

### 5.5 Maximum principle and mean value property

These are similar to the corresponding properties of analytic functions. Indeed, we deduce them from those corresponding properties.

**Theorem.** (Mean value property) If u is a harmonic function then u satisfies the mean value property. That is, suppose u is harmonic on and inside a circle of radius r centered at  $z_0 = x_0 + iy_0$  then

$$u(x_0, y_0) = \frac{1}{2\pi} \int_0^{2\pi} u(z_0 + re^{i\theta}) d\theta$$

*Proof.* Let f = u + iv be an analytic function with u as its real part. The mean value property for f says

$$\begin{split} u(x_0, y_0) + iv(x_0, y_0) &= f(z_0) = \frac{1}{2\pi} \int_0^{2\pi} f(z_0 + r\mathrm{e}^{i\theta}) \, d\theta \\ &= \frac{1}{2\pi} \int_0^{2\pi} u(z_0 + r\mathrm{e}^{i\theta}) + iv(z_0 + r\mathrm{e}^{i\theta}) \, d\theta \end{split}$$

Looking at the real parts of this equation proves the theorem.

**Theorem.** (Maximum principle) Suppose u(x, y) is harmonic on a open region A.

- (i) Suppose  $z_0$  is in A. If u has a relative maximum or minimum at  $z_0$  then u is constant on a disk centered at  $z_0$ .
- (ii) If A is bounded and connected and u is continuous on the boundary of A then the absolute maximum and absolute minimum of u occur on the boundary.

*Proof.* The proof for maxima is identical to the one for the maximum modulus principle. The proof for minima comes by looking at the maxima of -u.

**Note.** For analytic functions we only talked about maxima because we had to use the modulus in order to have real values. Since |-f| = |f| we couldn't use the trick of turning minima into maxima by using a minus sign.

### 5.6 Orthogonality of curves

An important property of harmonic conjugates u and v is that their level curves are orthogonal. We start by showing their gradients are orthogonal.

**Lemma 5.4.** Let z = x + iy and suppose that f(z) = u(x, y) + iv(x, y) is analytic. Then the dot product of their gradients is 0, i.e.

$$\nabla u \cdot \nabla v = 0$$

*Proof.* The proof is an easy application of the Cauchy-Riemann equations.

$$\nabla u \cdot \nabla v = (u_x, u_y) \cdot (v_x, v_y) = u_x v_x + u_y v_y = v_y v_x - v_x v_y = 0$$

In the last step we used the Cauchy-Riemann equations to substitute  $v_y$  for  $u_x$  and  $-v_x$  for  $u_y$ .  $\square$ 

The lemma holds whether or not the gradients are 0. To guarantee that the level curves are smooth the next theorem requires that  $f'(z) \neq 0$ .

**Theorem.** Let z = x + iy and suppose that

$$f(z) = u(x, y) + iv(x, y)$$

is analytic. If  $f'(z) \neq 0$  then the level curve of u through (x, y) is orthogonal to the level curve v through (x, y).

*Proof.* The technical requirement that  $f'(z) \neq 0$  is needed to be sure that the level curves are smooth. We need smoothness so that it even makes sense to ask if the curves are orthogonal. We'll discuss this below. Assuming the curves are smooth the proof of the theorem is trivial: We know from 18.02 that the gradient  $\nabla u$  is orthogonal to the level curves of u and the same is true for  $\nabla v$  and the level curves of v. Since, by Lemma 5.4, the gradients are orthogonal this implies the curves are orthogonal.

Finally, we show that  $f'(z) \neq 0$  means the curves are smooth. First note that

$$f'(z) = u_x(x, y) - iu_y(x, y) = v_y(x, y) + iv_x(x, y).$$

Now, since  $f'(z) \neq 0$  we know that

$$\nabla u = (u_x, u_y) \neq 0.$$

Likewise,  $\nabla v \neq 0$ . Thus, the gradients are not zero and the level curves must be smooth.

**Example 5.5.** The figures below show level curves of u and v for a number of functions. In all cases, the level curves of u are in orange and those of v are in blue. For each case we show the level curves separately and then overlayed on each other.

**Example 5.6.** Let's work out the gradients in a few simple examples.

(i) Let 
$$f(z)=z^2=(x^2-y^2)+i2xy,$$
 So 
$$\pmb{\nabla} u=(2x,-2y)\quad\text{and}\quad \pmb{\nabla} v=(2y,2x).$$

It's trivial to check that  $\nabla u \cdot \nabla v = 0$ , so they are orthogonal.

(ii) Let

$$f(z) = \frac{1}{z} = \frac{x}{r^2} - i\frac{y}{r^2}.$$

So, it's easy to compute

$$\nabla u = \left(\frac{y^2 - x^2}{r^4}, \frac{-2xy}{r^4}\right)$$
 and  $\nabla v = \left(\frac{2xy}{r^4}, \frac{y^2 - x^2}{r^4}\right)$ .

Again it's trivial to check that  $\nabla u \cdot \nabla v = 0$ , so they are orthogonal.

**Example 5.7.** (Degenerate points: f'(z) = 0.) Consider

$$f(z) = z^2.$$

From the previous example we have

$$u(x, y) = x^2 - y^2$$
,  $v(x, y) = 2xy$ ,  $\nabla u = (2x, -2y)$ ,  $\nabla v = (2y, 2x)$ .

At z = 0, the gradients are both 0 so the theorem on orthogonality doesn't apply.

Let's look at the level curves through the origin. The level curve (really the 'level set') for

$$u = x^2 - y^2 = 0$$

is the pair of lines  $y = \pm x$ . At the origin this is not a smooth curve.

Look at the figures for  $z^2$  above. It does appear that away from the origin the level curves of u intersect the lines where v = 0 at right angles. The same is true for the level curves of v and the lines where u = 0. You can see the degeneracy forming at the origin: as the level curves head towards 0 they get pointier and more right angled. So the level curve u = 0 is more properly thought of as four right angles. The level curve of u = 0, not knowing which leg of v = 0 to intersect orthogonally takes the average and comes into the origin at  $45^{\circ}$ .

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 6 Notes**

Jeremy Orloff

# 6 Two dimensional hydrodynamics and complex potentials

#### 6.1 Introduction

Laplace's equation and harmonic functions show up in many physical models. As we have just seen, harmonic functions in two dimensions are closely linked with complex analytic functions. In this section we will exploit this connection to look at two dimensional hydrodynamics, i.e. fluid flow.

Since static electric fields and steady state temperature distributions are also harmonic, the ideas and pictures we use can be repurposed to cover these topics as well.

## **6.2** Velocity fields

Suppose we have water flowing in a region A of the plane. Then at every point (x, y) in A the water has a velocity. In general, this velocity will change with time. We'll let F stand for the velocity vector field and we can write

$$\mathbf{F}(x, y, t) = (u(x, y, t), v(x, y, t)).$$

The arguments (x, y, t) indicate that the velocity depends on these three variables. In general, we will shorten the name to velocity field.

A beautiful and mesmerizing example of a velocity field is at <a href="http://hint.fm/wind/index.html">http://hint.fm/wind/index.html</a>. This shows the current velocity of the wind at all points in the continental U.S.

## **6.3** Stationary flows

If the velocity field is unchanging in time we call the flow a stationary flow. In this case, we can drop *t* as an argument and write:

$$\mathbf{F}(x, y) = (u(x, y), v(x, y))$$

Here are a few examples. These pictures show the streamlines from similar figures in topic 5. We've added arrows to indicate the direction of flow.

Example 6.1. Uniform flow.  $\mathbf{F} = (1, 0)$ .

**Example 6.2.** Eddy (vortex)  $F = (-y/r^2, x/r^2)$ 


**Example 6.3. Source F** =  $(x/r^2, y/r^2)$ 

## 6.4 Physical assumptions, mathematical consequences

This is a wordy section, so we'll start by listing the mathematical properties that will follow from our assumptions about the velocity field  $\mathbf{F} = u + iv$ .

- (A)  $\mathbf{F} = \mathbf{F}(x, y)$  is a function of x, y, but not time t (stationary).
- (B)  $\operatorname{div} \mathbf{F} = 0$  (divergence free).
- (C)  $\operatorname{curl} \mathbf{F} = 0$  (curl free).

## **6.4.1** Physical assumptions

We will make some standard physical assumptions. These don't apply to all flows, but they do apply to a good number of them and they are a good starting point for understanding fluid flow more generally. More important to 18.04, these are the flows that are readily susceptible to complex analysis.

Here are the assumptions about the flow, we'll discuss them further below:

- (A) The flow is stationary.
- (B) The flow is incompressible.
- (C) The flow is irrotational.

We have already discussed stationarity in Section 6.3, so let's now discuss the other two properties.

(B) **Incompressibility.** We will assume throughout that the fluid is incompressible. This means that the density of the fluid is constant across the domain. Mathematically this says that the velocity field **F** must be divergence free, i.e. for  $\mathbf{F} = (u, v)$ :

$$\operatorname{div}\mathbf{F} \equiv \mathbf{\nabla} \cdot \mathbf{F} = u_x + v_y = 0.$$

To understand this, recall that the divergence measures the infinitesimal flux of the field. If the flux is not zero at a point  $(x_0, y_0)$  then near that point the field looks like

Left: Divergent field:  $\operatorname{div} \mathbf{F} > 0$ , right: Convergent field:  $\operatorname{div} \mathbf{F} < 0$ 

If the field is diverging or converging then the density must be changing! That is, the flow is not incompressible.

As a fluid flow the left hand picture represents a source and the right represents a sink. In electrostatics where **F** expresses the electric field, the left hand picture is the field of a positive charge density and the right is that of a negative charge density.

If you prefer a non-infinitesimal explanation, we can recall Green's theorem in flux form. It says that for a simple closed curve C and a field  $\mathbf{F} = (u, v)$ , differentiable on and inside C, the flux of  $\mathbf{F}$  through C satisfies

Flux of **F** across 
$$C = \int_C \mathbf{F} \cdot \mathbf{n} \, ds = \int \int_R \operatorname{div} \mathbf{F} \, dx \, dy$$
,

where R is the region inside C. Now, suppose that  $\operatorname{div}\mathbf{F}(x_0,y_0)>0$ , then  $\operatorname{div}\mathbf{F}(x,y)>0$  for all (x,y) close to  $(x_0,y_0)$ . So, choose a small curve C around  $(x_0,y_0)$  such that  $\operatorname{div}\mathbf{F}>0$  on and inside C. By Green's theorem

Flux of **F** through 
$$C = \int \int_R \operatorname{div} \mathbf{F} \, dx \, dy > 0$$
.

Clearly, if there is a net flux out of the region the density is decreasing and the flow is not incompressible. The same argument would hold if  $\operatorname{div} \mathbf{F}(x_0, y_0) < 0$ . We conclude that incompressible is equivalent to divergence free.

(C) Irrotational flow. We will assume that the fluid is irrotational. This means that the there are no infinitesimal vortices in A. Mathematically this says that the velocity field  $\mathbf{F}$  must be curl free, i.e. for  $\mathbf{F} = (u, v)$ :

$$\operatorname{curl} \mathbf{F} \equiv \mathbf{\nabla} \times \mathbf{F} = v_x - u_y = 0.$$

To understand this, recall that the curl measures the infinitesimal rotation of the field. Physically this means that a small paddle placed in the flow will not spin as it moves with the flow.

### 6.4.2 Examples

**Example 6.4.** The eddy is irrotational! The eddy from Example 6.2 is irrotational. The vortex at the origin is not in  $A = \mathbb{C} - \{0\}$  and you can easily check that  $\text{curl} \mathbf{F} = 0$  everywhere in A. This is

not physically impossible: if you placed a small paddle wheel in the flow it would travel around the origin without spinning!

**Example 6.5.** Shearing flows are rotational. Here's an example of a vector field that has rotation, though not necessarily swirling.

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

Shearing flow: box turns because current is faster at the top.

The field  $\mathbf{F} = (ay, 0)$  is horizontal, but  $\operatorname{curl} \mathbf{F} = -a \neq 0$ . Because the top moves faster than the bottom it will rotate a square parcel of fluid. The minus sign tells you the parcel will rotate clockwise! This is called a shearing flow. The water at one level will be sheared away from the level above it.

### 6.4.3 Summary

(A) Stationary:  $\mathbf{F}$  depends on x, y, but not t, i.e.,

$$\mathbf{F}(x, y) = (u(x, y), v(x, y)).$$

(B) Incompressible: divergence free:

$$\operatorname{div} \mathbf{F} = u_x + v_y = 0$$
, i.e.  $u_x = -v_y$ .

(C) Irrotational: curl free:

$$\operatorname{curl} \mathbf{F} = v_x - u_y = 0,$$
 i.e.,  $u_y = v_x$ .

For future reference we put the last two equalities in a numbered equation:

$$u_x = -v_y$$
 and  $u_y = v_x$  (1)

These look almost like the Cauchy-Riemann equations (with sign differences)!

## 6.5 Complex potentials

There are different ways to do this. We'll start by seeing that every complex analytic function leads to an irrotational, incompressible flow. Then we'll go backwards and see that all such flows lead to an analytic function. We will learn to call the analytic function the complex potential of the flow.

Annoyingly, we are going to have to switch notation. Because u and v are already taken by the vector field  $\mathbf{F}$ , we will call our complex potential

$$\Phi = \phi + i\psi$$
.

### 6.5.1 Analytic functions give us incompressible, irrotational flows

Let  $\Phi(z)$  be an analytic function on a region A. For z = x + iy we write

$$\Phi(z) = \phi(x, y) + i\psi(x, y).$$

From this we can define a vector field

$$\mathbf{F} = \nabla \phi = (\phi_x, \phi_y) = : (u, v),$$

here we mean that u and v are defined by  $\phi_x$  and  $\phi_v$ .

From our work on analytic and harmonic functions we can make a list of properties of these functions.

- 1.  $\phi$  and  $\psi$  are both harmonic.
- 2. The level curves of  $\phi$  and  $\psi$  are orthogonal.
- 3.  $\Phi' = \phi_x i\phi_y$ .
- 4. **F** is divergence and curl free (proof just below). That is, the analytic function  $\Phi$  has given us an incompressible, irrotational vector field **F**.

It is standard terminology to call  $\phi$  a potential function for the vector field  $\mathbf{F}$ . We will also call  $\Phi$  a complex potential function for  $\mathbf{F}$ . The function  $\psi$  will be called the stream function of  $\mathbf{F}$  (the name will be explained soon). The function  $\Phi'$  will be called the complex velocity.

*Proof.* (**F** is curl and divergence free.) This is an easy consequence of the definition. We find

$$\operatorname{curl}\mathbf{F} = v_x - u_y = \phi_{yx} - \phi_{xy} = 0$$

$$\operatorname{div} \mathbf{F} = u_x + v_y = \phi_{xx} + \phi_{yy} = 0$$
 (since  $\phi$  is harmonic).

We'll postpone examples until after deriving the complex potential from the flow.

#### 6.5.2 Incompressible, irrotational flows always have complex potential functions

For technical reasons we need to add the assumption that A is simply connected. This is not usually a problem because we often work locally in a disk around a point  $(x_0, y_0)$ .

**Theorem.** Assume  $\mathbf{F} = (u, v)$  is an incompressible, irrotational field on a simply connected region A. Then there is an analytic function  $\Phi$  which is a complex potential function for  $\mathbf{F}$ .

*Proof.* We have done all the heavy lifting for this in previous topics. The key is to use the property  $\Phi' = u - iv$  to guess  $\Phi'$ . Working carefully we define

$$g(z) = u - iv$$

Step 1: Show that g is analytic. Keeping the signs straight, the Cauchy Riemann equations are

$$u_x = (-v)_v$$
 and  $u_v = -(-v)_x = v_x$ .

But, these are exactly the equations in Equation 1. Thus g(z) is analytic.

Step 2: Since A is simply connected, Cauchy's theorem says that g(z) has an antiderivative on A. We call the antiderivative  $\Phi(z)$ .

Step 3: Show that  $\Phi(z)$  is a complex potential function for **F**. This means we have to show that if we write  $\Phi = \phi + i\psi$ , then  $\mathbf{F} = \nabla \phi$ . To do this we just unwind the definitions.

$$\Phi' = \phi_x - i\phi_y$$
 (standard formula for  $\Phi'$ )  
 $\Phi' = g = u - iv$  (definition of  $\Phi$  and  $g$ )

Comparing these equations we get

$$\phi_x = u, \qquad \phi_v = v.$$

But this says precisely that  $\nabla \phi = \mathbf{F}$ . QED

Example 6.6. Source fields. The vector field

$$\mathbf{F} = a\left(\frac{x}{r^2}, \frac{y}{r^2}\right)$$

models a source pushing out water or the 2D electric field of a positive charge at the origin. (If you prefer a 3D model, it is the field of an infinite wire with uniform charge density along the z-axis.) Show that  $\mathbf{F}$  is curl-free and divergence-free and find its complex potential.

We could compute directly that this is curl-free and divergence-free away from 0. An alternative method is to look for a complex potential  $\Phi$ . If we can find one then this will show  $\mathbf{F}$  is curl and divergence free and find  $\phi$  and  $\psi$  all at once. If there is no such  $\Phi$  then we'll know that  $\mathbf{F}$  is not both curl and divergence free.

One standard method is to use the formula for  $\Phi'$ :

$$\Phi' = u - iv = a \frac{(x - iy)}{r^2} = a \frac{\overline{z}}{(\overline{z}z)} = \frac{a}{z}.$$

This is analytic and we have

$$\Phi(z) = a \log(z).$$

#### 6.6 Stream functions

In everything we did above poor old  $\psi$  just tagged along as the harmonic conjugate of the potential function  $\phi$ . Let's turn our attention to it and see why it's called the stream function.

**Theorem.** Suppose that

$$\Phi = \phi + i\psi$$

is the complex potential for a velocity field  $\mathbf{F}$ . Then the fluid flows along the level curves of  $\psi$ . That is, the  $\mathbf{F}$  is everywhere tangent to the level curves of  $\psi$ . The level curves of  $\psi$  are called streamlines and  $\psi$  is called the stream function.

*Proof.* Again we have already done most of the heavy lifting to prove this. Since **F** is the velocity of the flow at each point, the flow is always tangent to **F**. You also need to remember that  $\nabla \phi$  is perpendicular to the level curves of  $\phi$ . So we have:

- 1. The flow is parallel to  $\mathbf{F}$ .
- 2.  $\mathbf{F} = \nabla \phi$ , so the flow is orthogonal to the level curves of  $\phi$ .
- 3. Since  $\phi$  and  $\psi$  are harmonic conjugates, the level curves of  $\psi$  are orthogonal to the level curves of  $\phi$ .

Combining 2 and 3 we see that the flow must be along the level curves of  $\psi$ .

### 6.6.1 Examples

We'll illustrate the streamlines in a series of examples that start by defining the complex potential for a vector field.

Example 6.7. Uniform flow. Let

$$\Phi(z) = z$$
.

Find **F** and draw a plot of the streamlines. Indicate the direction of the flow.

Solution: Write

$$\Phi = x + iv$$
.

So

$$\phi = x$$
 and  $\mathbf{F} = \nabla \phi = (1, 0),$ 

which says the flow has uniform velocity and points to the right. We also have

$$\psi = y$$
,

so the streamlines are the horizontal lines y = constant.

Uniform flow to the right.

Note that another way to see that the flow is to the right is to check the direction that the potential  $\phi$  increases. The Topic 5 notes show pictures of this complex potential which show both the streamlines and the equipotential lines.

Example 6.8. Linear source. Let

$$\Phi(z) = \log(z).$$

Find **F** and draw a plot of the streamlines. Indicate the direction of the flow.

Solution: Write

$$\Phi = \log(r) + i\theta.$$

So

$$\phi = \log(r)$$
 and  $\mathbf{F} = \nabla \phi = (x/r^2, y/r^2)$ ,

which says the flow is radial and decreases in speed as it gets farther from the origin. The field is not defined at z = 0. We also have

$$\psi = \theta$$
,

so the streamlines are rays from the origin.

Linear source: radial flow from the origin.

### **6.6.2** Stagnation points

A stagnation point is one where the velocity field is 0.

**Stagnation points.** If  $\Phi$  is the complex potential for a field **F** then the stagnation points  $\mathbf{F} = 0$  are exactly the points z where  $\Phi'(z) = 0$ .

*Proof.* This is clear since  $\mathbf{F} = (\phi_x, \phi_y)$  and  $\Phi' = \phi_x - i\phi_y$ .

**Example 6.9.** Stagnation points. Draw the streamlines and identify the stagnation points for the potential  $\Phi(z) = z^2$ .

Solution: (We drew the level curves for this in Topic 5.) We have

$$\Phi = (x^2 - y^2) + i2xy.$$

So the streamlines are the hyperbolas: 2xy = constant. Since  $\phi = x^2 - y^2$  increases as |x| increases and decreases as |y| increases, the arrows, which point in the direction of increasing  $\phi$ , are as shown on the figure below.

Stagnation flow: stagnation point at z = 0.

The stagnation points are the zeros of

$$\Phi'(z) = 2z,$$

i.e. the only stagnation point is at the z = 0.

Note. The stagnation points are what we called the critical points of a vector field in 18.03.

## 6.7 More examples with pretty pictures

**Example 6.10.** Linear vortex. Analyze the flow with complex potential function

$$\Phi(z) = i \log(z).$$

*Solution:* Multiplying by i switches the real and imaginary parts of log(z) (with a sign change). We have

$$\Phi = -\theta + i \log(r).$$

The stream lines are the curves  $\log(r) = \text{constant}$ , i.e. circles with center at z = 0. The flow is clockwise because the potential  $\phi = -\theta$  increases in the clockwise direction.

Linear vortex.

This flow is called a linear vortex. We can find **F** using  $\Phi'$ .

$$\Phi' = \frac{i}{z} = \frac{y}{r^2} + i\frac{x}{r^2} = \phi_x - i\phi_y.$$

So

$$\mathbf{F} = (\phi_x, \phi_y) = (y/r^2, -x/r^2).$$

(By now this should be a familiar vector field.) There are no stagnation points, but there is a singularity at the origin.

**Example 6.11.** Double source. Analyze the flow with complex potential function

$$\Phi(z) = \log(z - 1) + \log(z + 1).$$

Solution: This is a flow with linear sources at  $\pm 1$ . We used Octave to plot the level curves of  $\psi = \text{Im}(\Phi)$ .

Two sources.

We can analyze this flow further as follows.

- Near each source the flow looks like a linear source.
- On the y-axis the flow is along the axis. That is, the y-axis is a streamline. It's worth seeing three different ways of arriving at this conclusion.

**Reason 1:** By symmetry of vector fields associated with each linear source, the *x* components cancel and the combined field points along the *y*-axis.

Reason 2: We can write

$$\Phi(z) = \log(z-1) + \log(z+1) = \log((z-1)(z+1)) = \log(z^2-1).$$

So

$$\Phi'(z) = \frac{2z}{z^2 - 1}.$$

On the imaginary axis

$$\Phi'(iy) = \frac{2iy}{-y^2 - 1}.$$

Thus,

$$\mathbf{F} = \left(0, \frac{2y}{y^2 + 1}\right)$$

which is along the axis.

**Reason 3:** On the imaginary axis  $\Phi(iy) = \log(-y^2 - 1)$ . Since this has constant imaginary part, the axis is a streamline.

Because of the branch cut for  $\log(z)$  we should probably be a little more careful here. First note that the vector field **F** comes from  $\Phi' = 2z/(z^2 - 1)$ , which doesn't have a branch cut. So we shouldn't

really have a problem. Now, as z approaches the y-axis from one side or the other, the argument of  $\log(z^2 - 1)$  approaches either  $\pi$  or  $-\pi$ . That is, as such limits, the imaginary part is constant. So the streamline on the y-axis is the limit case of streamlines near the axis.

Since  $\Phi'(z) = 0$  when z = 0, the origin is a stagnation point. This is where the fields from the two sources exactly cancel each other.

**Example 6.12.** A source in uniform flow. Consider the flow with complex potential

$$\Phi(z) = z + \frac{Q}{2\pi} \log(z).$$

This is a combination of uniform flow to the right and a source at the origin. The figure below was drawn using Octave. It shows that the flow looks like a source near the origin. Farther away from the origin the flow stops being radial and is pushed to the right by the uniform flow.

A source in uniform flow.

Since the components of  $\Phi'$  and F are the same except for signs, we can understand the flow by considering

$$\Phi'(z) = 1 + \frac{Q}{2\pi z}.$$

Near z = 0 the singularity of 1/z is most important and

$$\Phi' \approx \frac{Q}{2\pi z}$$
.

So, the vector field looks a linear source. Far away from the origin the 1/z term is small and  $\Phi'(z) \approx 1$ , so the field looks like uniform flow.

Setting  $\Phi'(z) = 0$  we find one stagnation point

$$z = -\frac{Q}{2\pi}$$
.

It is the point on the x-axis where the flow from the source exactly balances that from the uniform flow. For bigger values of Q the source pushes fluid farther out before being overwhelmed by the uniform flow. That is why Q is called the source strength.

**Example 6.13.** Source + sink. Consider the flow with complex potential

$$\Phi(z) = \log(z - 2) - \log(z + 2).$$

This is a combination of source ( $\log(z-2)$ ) at z=2 and a sink ( $-\log(z+2)$ ) at z=-2.

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

## **Topic 7 Notes**

Jeremy Orloff

# 7 Taylor and Laurent series

## 7.1 Introduction

We originally defined an analytic function as one where the derivative, defined as a limit of ratios, existed. We went on to prove Cauchy's theorem and Cauchy's integral formula. These revealed some deep properties of analytic functions, e.g. the existence of derivatives of all orders.

Our goal in this topic is to express analytic functions as infinite power series. This will lead us to Taylor series. When a complex function has an isolated singularity at a point we will replace Taylor series by Laurent series. Not surprisingly we will derive these series from Cauchy's integral formula.

Although we come to power series representations after exploring other properties of analytic functions, they will be one of our main tools in understanding and computing with analytic functions.

#### 7.2 Geometric series

Having a detailed understanding of geometric series will enable us to use Cauchy's integral formula to understand power series representations of analytic functions. We start with the definition:

**Definition.** A finite geometric series has one of the following (all equivalent) forms.

$$S_n = a(1 + r + r^2 + r^3 + \dots + r^n)$$

$$= a + ar + ar^2 + ar^3 + \dots + ar^n$$

$$= \sum_{j=0}^{n} ar^j$$

$$= a \sum_{j=0}^{n} r^j$$

The number r is called the ratio of the geometric series because it is the ratio of consecutive terms of the series.

**Theorem.** The sum of a finite geometric series is given by

$$S_n = a(1+r+r^2+r^3+\ldots+r^n) = \frac{a(1-r^{n+1})}{1-r}.$$
 (1)

*Proof.* This is a standard trick that you've probably seen before.

$$S_n = a+ ar + ar^2 + \dots + ar^n$$
  
 $rS_n = ar + ar^2 + \dots + ar^n + ar^{n+1}$ 

When we subtract these two equations most terms cancel and we get

$$S_n - rS_n = a - ar^{n+1}$$

Some simple algebra now gives us the formula in Equation 1.

**Definition.** An infinite geometric series has the same form as the finite geometric series except there is no last term:

$$S = a + ar + ar^2 + \dots = a \sum_{j=0}^{\infty} r^j$$
.

Note. We will usually simply say 'geometric series' instead of 'infinite geometric series'.

**Theorem.** If |r| < 1 then the infinite geometric series converges to

$$S = a \sum_{j=0}^{\infty} r^{j} = \frac{a}{1 - r}$$
 (2)

If  $|r| \ge 1$  then the series does not converge.

*Proof.* This is an easy consequence of the formula for the sum of a finite geometric series. Simply let  $n \to \infty$  in Equation 1.

**Note.** We have assumed a familiarity with convergence of infinite series. We will go over this in more detail in the appendix to this topic.

## 7.2.1 Connection to Cauchy's integral formula

Cauchy's integral formula says

$$f(z) = \frac{1}{2\pi i} \int_C \frac{f(w)}{w - z} dw.$$

Inside the integral we have the expression

$$\frac{1}{w-z}$$

which looks a lot like the sum of a geometric series. We will make frequent use of the following manipulations of this expression.

$$\frac{1}{w-z} = \frac{1}{w} \cdot \frac{1}{1-z/w} = \frac{1}{w} \left( 1 + (z/w) + (z/w)^2 + \dots \right)$$
 (3)

The geometric series in this equation has ratio z/w. Therefore, the series converges, i.e. the formula is valid, whenever |z/w| < 1, or equivalently when

$$|z| < |w|$$
.

Similarly,

$$\frac{1}{w-z} = -\frac{1}{z} \cdot \frac{1}{1-w/z} = -\frac{1}{z} \left( 1 + (w/z) + (w/z)^2 + \dots \right)$$
 (4)

The series converges, i.e. the formula is valid, whenever |w/z| < 1, or equivalently when

$$|z| > |w|$$
.


## 7.3 Convergence of power series

When we include powers of the variable z in the series we will call it a power series. In this section we'll state the main theorem we need about the convergence of power series. Technical details will be pushed to the appendix for the interested reader.

**Theorem 7.1.** Consider the power series

$$f(z) = \sum_{n=0}^{\infty} a_n (z - z_0)^n.$$

There is a number  $R \ge 0$  such that:

- 1. If R > 0 then the series converges absolutely to an analytic function for  $|z z_0| < R$ .
- 2. The series diverges for  $|z-z_0| > R$ . R is called the radius of convergence. The disk  $|z-z_0| < R$  is called the disk of convergence.
- 3. The derivative is given by term-by-term differentiation

$$f'(z) = \sum_{n=0}^{\infty} na_n (z - z_0)^{n-1}$$

The series for f' also has radius of convergence R.

4. If  $\gamma$  is a bounded curve inside the disk of convergence then the integral is given by term-by-term integration

$$\int_{\gamma} f(z) dz = \sum_{n=0}^{\infty} \int_{\gamma} a_n (z - z_0)^n$$

Notes.

- The theorem doesn't say what happens when  $|z z_0| = R$ .
- If  $R = \infty$  the function f(z) is entire.
- If R = 0 the series only converges at the point  $z = z_0$ . In this case, the series does not represent an analytic function on any disk around  $z_0$ .
- Often (not always) we can find R using the ratio test.

The proof of this theorem is in the appendix.

#### 7.3.1 Ratio test and root test

Here are two standard tests from calculus on the convergence of infinite series.

**Ratio test.** Consider the series  $\sum_{n=0}^{\infty} c_n$ . If  $L = \lim_{n \to \infty} |c_{n+1}/c_n|$  exists, then:

1. If L < 1 then the series converges absolutely.

- 2. If L > 1 then the series diverges.
- 3. If L = 1 then the test gives no information.

**Note.** In words, L is the limit of the absolute ratios of consecutive terms.

Again the proof will be in the appendix. (It boils down to comparison with a geometric series.)

**Example 7.2.** Consider the geometric series  $1 + z + z^2 + z^3 + \dots$  The limit of the absolute ratios of consecutive terms is

$$L = \lim_{n \to \infty} \frac{|z^{n+1}|}{|z^n|} = |z|$$

Thus, the ratio test agrees that the geometric series converges when |z| < 1. We know this converges to 1/(1-z). Note, the disk of convergence ends exactly at the singularity z = 1.

**Example 7.3.** Consider the series  $f(z) = \sum_{n=0}^{\infty} \frac{z^n}{n!}$ . The limit from the ratio test is

$$L = \lim_{n \to \infty} \frac{|z^{n+1}|/(n+1)!}{|z^n|/n!} = \lim \frac{|z|}{n+1} = 0.$$

Since L < 1 this series converges for every z. Thus, by Theorem 7.1, the radius of convergence for this series is  $\infty$ . That is, f(z) is entire. Of course we know that  $f(z) = e^z$ .

**Root test.** Consider the series  $\sum_{n=0}^{\infty} c_n$ . If  $L = \lim_{n \to \infty} |c_n|^{1/n}$  exists, then:

- 1. If L < 1 then the series converges absolutely.
- 2. If L > 1 then the series diverges.
- 3. If L = 1 then the test gives no information.

**Note.** In words, L is the limit of the nth roots of the (absolute value) of the terms.

The geometric series is so fundamental that we should check the root test on it.

**Example 7.4.** Consider the geometric series  $1 + z + z^2 + z^3 + \dots$  The limit of the *n*th roots of the terms is

$$L = \lim_{n \to \infty} |z^n|^{1/n} = \lim |z| = |z|$$

Happily, the root test agrees that the geometric series converges when |z| < 1.

## 7.4 Taylor series

The previous section showed that a power series converges to an analytic function inside its disk of convergence. Taylor's theorem completes the story by giving the converse: around each point of analyticity an analytic function equals a convergent power series.

**Theorem 7.5.** (Taylor's theorem) Suppose f(z) is an analytic function in a region A. Let  $z_0 \in A$ . Then,

$$f(z) = \sum_{n=0}^{\infty} a_n (z - z_0)^n,$$

where the series converges on any disk  $|z - z_0| < r$  contained in A. Furthermore, we have formulas for the coefficients

$$a_n = \frac{f^{(n)}(z_0)}{n!} = \frac{1}{2\pi i} \int_{\gamma} \frac{f(z)}{(z - z_0)^{n+1}} dz.$$
 (5)

(Where  $\gamma$  is any simple closed curve in A around  $z_0$ , with its interior entirely in A.)

We call the series the power series representing f around  $z_0$ .

The proof will be given below. First we look at some consequences of Taylor's theorem.

**Corollary.** The power series representing an analytic function around a point  $z_0$  is unique. That is, the coefficients are uniquely determined by the function f(z).

*Proof.* Taylor's theorem gives a formula for the coefficients.

#### 7.4.1 Order of a zero

**Theorem.** Suppose f(z) is analytic on the disk  $|z - z_0| < r$  and f is not identically 0. Then there is an integer  $k \ge 0$  such that  $a_k \ne 0$  and f has Taylor series around  $z_0$  given by

$$f(z) = (z - z_0)^k (a_k + a_{k+1}(z - z_0) + \dots) = (z - z_0)^k \sum_{n=k}^{\infty} a_n (z - z_0)^{n-k}.$$
 (6)

*Proof.* Since f(z) is not identically 0, not all the Taylor coefficients are zero. So, we take k to be the index of the first nonzero coefficient.

**Theorem 7.6.** Zeros are isolated. If f(z) is analytic and not identically zero then the zeros of f are isolated. (By isolated we mean that we can draw a small disk around any zeros that doesn't contain any other zeros.)

Isolated zero at  $z_0$ :  $f(z_0) = 0$ ,  $f(z) \neq 0$  elsewhere in the disk.

*Proof.* Suppose  $f(z_0) = 0$ . Write f as in Equation 6. There are two factors:

$$(z-z_0)^k$$

and

$$g(z) = a_k + a_{k+1}(z - z_0) + \dots$$

Clearly  $(z-z_0)^k \neq 0$  if  $z \neq z_0$ . We have  $g(z_0) = a_k \neq 0$ , so g(z) is not 0 on some small neighborhood of  $z_0$ . We conclude that on this neighborhood the product is only zero when  $z = z_0$ , i.e.  $z_0$  is an isolated 0.

**Definition.** The integer k in Theorem 7.6 is called the order of the zero of f at  $z_0$ .

Note, if  $f(z_0) \neq 0$  then  $z_0$  is a zero of order 0.

## 7.5 Taylor series examples

The uniqueness of Taylor series along with the fact that they converge on any disk around  $z_0$  where the function is analytic allows us to use lots of computational tricks to find the series and be sure that it converges.

**Example 7.7.** Use the formula for the coefficients in terms of derivatives to give the Taylor series of  $f(z) = e^z$  around z = 0.

Solution: Since  $f'(z) = e^z$ , we have  $f^{(n)}(0) = e^0 = 1$ . So,

$$e^z = 1 + z + \frac{z^2}{2!} + \frac{z^3}{3!} + \dots = \sum_{n=0}^{\infty} \frac{z^n}{n!}$$

**Example 7.8.** Expand  $f(z) = z^8 e^{3z}$  in a Taylor series around z = 0.

Solution: Let w = 3z. So,

$$e^{3z} = e^w = \sum_{n=0}^{\infty} \frac{w^n}{n!} = \sum_{k=0}^{\infty} \frac{3^n}{n!} z^n$$

Thus,

$$f(z) = \sum_{n=0}^{\infty} \frac{3^n}{n!} z^{n+8}.$$

**Example 7.9.** Find the Taylor series of sin(z) around z = 0 (Sometimes the Taylor series around 0 is called the Maclaurin series.)

Solution: We give two methods for doing this.

#### Method 1.

$$f^{(n)}(0) = \frac{d^n \sin(z)}{dz^n} = \begin{cases} (-1)^m & \text{for } n = 2m + 1 = \text{odd, } m = 0, 1, 2, \dots \\ 0 & \text{for } n \text{ even} \end{cases}$$

Method 2. Using

$$\sin(z) = \frac{e^{iz} - e^{-iz}}{2i},$$

we have

$$\sin(z) = \frac{1}{2i} \left[ \sum_{n=0}^{\infty} \frac{(iz)^n}{n!} - \sum_{n=0}^{\infty} \frac{(-iz)^n}{n!} \right] = \frac{1}{2i} \sum_{n=0}^{\infty} [(1 - (-1)^n)] \frac{i^n z^n}{n!}$$

(We need absolute convergence to add series like this.)

Conclusion:

$$\sin(z) = \sum_{n=0}^{\infty} (-1)^n \frac{z^{2n+1}}{(2n+1)!},$$

which converges for  $|z| < \infty$ .

**Example 7.10.** Expand the rational function

$$f(z) = \frac{1 + 2z^2}{z^3 + z^5}$$

around z = 0.

Solution: Note that f has a singularity at 0, so we can't expect a convergent Taylor series expansion. We'll aim for the next best thing using the following shortcut.

$$f(z) = \frac{1}{z^3} \frac{2(1+z^2)-1}{1+z^2} = \frac{1}{z^3} \left[ 2 - \frac{1}{1+z^2} \right].$$

Using the geometric series we have

$$\frac{1}{1+z^2} = \frac{1}{1-(-z^2)} = \sum_{n=0}^{\infty} (-z^2)^n = 1 - z^2 + z^4 - z^6 + \dots$$

Putting it all together

$$f(z) = \frac{1}{z^3} \left( 2 - 1 + z^2 - z^4 + \dots \right) = \left( \frac{1}{z^3} + \frac{1}{z} \right) - \sum_{n=0}^{\infty} (-1)^n z^{2n+1}$$

**Note.** The first terms are called the singular part, i.e. those with negative powers of z. The summation is called the regular or analytic part. Since the geometric series for  $1/(1+z^2)$  converges for |z| < 1, the entire series is valid in 0 < |z| < 1

Example 7.11. Find the Taylor series for

$$f(z) = \frac{e^z}{1 - z}$$

around z = 0. Give the radius of convergence.

Solution: We start by writing the Taylor series for each of the factors and then multiply them out.

$$f(z) = \left(1 + z + \frac{z^2}{2!} + \frac{z^3}{3!} + \dots\right) \left(1 + z + z^2 + z^3 + \dots\right)$$
$$= 1 + (1+1)z + \left(1 + 1 + \frac{1}{2!}\right)z^2 + \left(1 + 1 + \frac{1}{2!} + \frac{1}{3!}\right)z^3 + \dots$$

The biggest disk around z = 0 where f is analytic is |z| < 1. Therefore, by Taylor's theorem, the radius of convergence is R = 1.

f(z) is analytic on |z| < 1 and has a singularity at z = 1.

**Example 7.12.** Find the Taylor series for

$$f(z) = \frac{1}{1 - z}$$

around z = 5. Give the radius of convergence.

Solution: We have to manipulate this into standard geometric series form.

$$f(z) = \frac{1}{-4(1+(z-5)/4)} = -\frac{1}{4}\left(1-\left(\frac{z-5}{4}\right)+\left(\frac{z-5}{4}\right)^2-\left(\frac{z-5}{4}\right)^3+\ldots\right)$$

Since f(z) has a singularity at z = 1 the radius of convergence is R = 4. We can also see this by considering the geometric series. The geometric series ratio is (z - 5)/4. So the series converges when |z - 5|/4 < 1, i.e. when |z - 5| < 4, i.e. R = 4.

Disk of convergence stops at the singularity at z = 1.

#### **Example 7.13.** Find the Taylor series for

$$f(z) = \log(1+z)$$

around z = 0. Give the radius of convergence.

Solution: We know that f is analytic for |z| < 1 and not analytic at z = -1. So, the radius of convergence is R = 1. To find the series representation we take the derivative and use the geometric series.

$$f'(z) = \frac{1}{1+z} = 1 - z + z^2 - z^3 + z^4 - \dots$$

Integrating term by term (allowed by Theorem 7.1) we have

$$f(z) = a_0 + z - \frac{z^2}{2} + \frac{z^3}{3} - \frac{z^4}{4} + \dots = a_0 + \sum_{n=1}^{\infty} (-1)^{n-1} \frac{z^n}{n}$$

Here  $a_0$  is the constant of integration. We find it by evalating at z = 0.

$$f(0) = a_0 = \log(1) = 0.$$

Disk of convergence for  $\log(1+z)$  around z=0.

## Example 7.14. Can the series

$$\sum a_n(z-2)^n$$

converge at z = 0 and diverge at z = 3.

Solution: No! We have  $z_0 = 2$ . We know the series diverges everywhere outside its radius of convergence. So, if the series converges at z = 0, then the radius of convergence is at least 2. Since  $|3 - z_0| < 2$  we would also have that z = 3 is inside the disk of convergence.

## 7.5.1 Proof of Taylor's theorem

For convenience we restate Taylor's Theorem 7.5.

**Taylor's theorem.** (Taylor series) Suppose f(z) is an analytic function in a region A. Let  $z_0 \in A$ . Then,

$$f(z) = \sum_{n=0}^{\infty} a_n (z - z_0)^n,$$

where the series converges on any disk  $|z - z_0| < r$  contained in A. Furthermore, we have formulas for the coefficients

$$a_n = \frac{f^{(n)}(z_0)}{n!} = \frac{1}{2\pi i} \int_{\gamma} \frac{f(z)}{(z - z_0)^{n+1}} dz$$
 (7)

*Proof.* In order to handle convergence issues we fix  $0 < r_1 < r_2 < r$ . We let  $\gamma$  be the circle  $|w - z_0| = r_2$  (traversed counterclockise).

Disk of convergence extends to the boundary of A  $r_1 < r_2 < r$ , but  $r_1$  and  $r_2$  can be arbitrarily close to r.

Take z inside the disk  $|z - z_0| < r_1$ . We want to express f(z) as a power series around  $z_0$ . To do this we start with the Cauchy integral formula and then use the geometric series.

As preparation we note that for w on  $\gamma$  and  $|z - z_0| < r_1$  we have

$$|z - z_0| < r_1 < r_2 = |w - z_0|,$$

so

$$\frac{|z-z_0|}{|w-z_0|} < 1.$$

Therefore,

$$\frac{1}{w-z} = \frac{1}{w-z_0} \cdot \frac{1}{1 - \frac{z-z_0}{w-z_0}} = \frac{1}{w-z_0} \sum_{n=0}^{\infty} \left(\frac{z-z_0}{w-z_0}\right)^n = \sum_{n=0}^{\infty} \frac{(z-z_0)^n}{(w-z_0)^{n+1}}$$

Using this and the Cauchy formula gives

$$f(z) = \frac{1}{2\pi i} \int_{\gamma} \frac{f(w)}{w - z} dw$$

$$= \frac{1}{2\pi i} \int_{\gamma} \sum_{n=0}^{\infty} \frac{f(w)}{(w - z_0)^{n+1}} (z - z_0)^n dw$$

$$= \sum_{n=0}^{\infty} \left( \frac{1}{2\pi i} \int_{\gamma} \frac{f(w)}{(w - z_0)^{n+1}} dw \right) (z - z_0)^n$$

$$= \sum_{n=0}^{\infty} \frac{f^{(n)}(z_0)}{n!} (z - z_0)^n$$

The last equality follows from Cauchy's formula for derivatives. Taken together the last two equalities give Taylor's formula. QED

## 7.6 Singularities

**Definition.** A function f(z) is singular at a point  $z_0$  if it is not analytic at  $z_0$ 

**Definition.** For a function f(z), the singularity  $z_0$  is an isolated singularity if f is analytic on the deleted disk  $0 < |z - z_0| < r$  for some r > 0.

**Example 7.15.**  $f(z) = \frac{z+1}{z^3(z^2+1)}$  has isolated singularities at  $z=0,\pm i$ .

**Example 7.16.**  $f(z) = e^{1/z}$  has an isolated singularity at z = 0.

**Example 7.17.**  $f(z) = \log(z)$  has a singularity at z = 0, but it is not isolated because a branch cut, starting at z = 0, is needed to have a region where f is analytic.

**Example 7.18.**  $f(z) = \frac{1}{\sin(\pi/z)}$  has singularities at z = 0 and z = 1/n for  $n = \pm 1, \pm 2, ...$  The singularities at  $\pm 1/n$  are isolated, but the one at z = 0 is not isolated.

Every neighborhood of 0 contains zeros at 1/n for large n.

#### 7.7 Laurent series

**Theorem 7.19.** (Laurent series). Suppose that f(z) is analytic on the annulus

$$A: r_1 < |z - z_0| < r_2.$$

Then f(z) can be expressed as a series

$$f(z) = \sum_{n=1}^{\infty} \frac{b_n}{(z - z_0)^n} + \sum_{n=0}^{\infty} a_n (z - z_0)^n.$$

The coefficients have the formulus

$$a_n = \frac{1}{2\pi i} \int_{\gamma} \frac{f(w)}{(w - z_0)^{n+1}} dw$$

$$b_n = \frac{1}{2\pi i} \int_{\gamma} f(w)(w - z_0)^{n-1} dw,$$

where  $\gamma$  is any circle  $|w - z_0| = r$  inside the annulus, i.e.  $r_1 < r < r_2$ . Furthermore

- The series  $\sum_{n=0}^{\infty} a_n (z-z_0)^n$  converges to an analytic function for  $|z-z_0| < r_2$ .
- The series  $\sum_{n=1}^{\infty} \frac{b_n}{(z-z_0)^n}$  converges to an analytic function for  $|z-z_0| > r_1$ .
- Together, the series both converge on the annulus A where f is analytic.

The proof is given below. First we define a few terms.

**Definition.** The entire series is called the Laurent series for f around  $z_0$ . The series

$$\sum_{n=0}^{\infty} a_n (z - z_0)^n$$

is called the analytic or regular part of the Laurent series. The series

$$\sum_{n=1}^{\infty} \frac{b_n}{(z-z_0)^n}$$

is called the singular or principal part of the Laurent series.

**Note.** Since f(z) may not be analytic (or even defined) at  $z_0$  we don't have any formulas for the coefficients using derivatives.

*Proof.* (Laurent series). Choose a point z in A. Now set circles  $C_1$  and  $C_3$  close enough to the boundary that z is inside  $C_1 + C_2 - C_3 - C_2$  as shown. Since this curve and its interior are contained in A, Cauchy's integral formula says

$$f(z) = \frac{1}{2\pi i} \int_{C_1 + C_2 - C_3 - C_3} \frac{f(w)}{w - z} dw$$

The contour used for proving the formulas for Laurent series.

The integrals over  $C_2$  cancel, so we have

$$f(z) = \frac{1}{2\pi i} \int_{C_1 - C_3} \frac{f(w)}{w - z} \, dw.$$

Next, we divide this into two pieces and use our trick of converting to a geometric series. The calculations are just like the proof of Taylor's theorem. On  $C_1$  we have

$$\frac{|z - z_0|}{|w - z_0|} < 1,$$

so

$$\frac{1}{2\pi i} \int_{C_1} \frac{f(w)}{w - z} dw = \frac{1}{2\pi i} \int_{C_1} \frac{f(w)}{w - z_0} \cdot \frac{1}{\left(1 - \frac{z - z_0}{w - z_0}\right)} dw$$

$$= \frac{1}{2\pi i} \int_{C_1} \sum_{n=0}^{\infty} \frac{f(w)}{(w - z_0)^{n+1}} (z - z_0)^n dw$$

$$= \sum_{n=0}^{\infty} \left(\frac{1}{2\pi i} \int_{C_1} \frac{f(w)}{(w - z_0)^{n+1}} dw\right) (z - z_0)^n$$

$$= \sum_{n=0}^{\infty} a_n (z - z_0)^n.$$

Here  $a_n$  is defined by the integral formula given in the statement of the theorem. Examining the above argument we see that the only requirement on z is that  $|z - z_0| < r_2$ . So, this series converges for all such z.

Similarly on  $C_3$  we have

$$\frac{|w - z_0|}{|z - z_0|} < 1,$$

so

$$\begin{split} \frac{1}{2\pi i} \int_{C_3} \frac{f(w)}{w - z} \, dw &= \frac{1}{2\pi i} \int_{C_3} -\frac{f(w)}{z - z_0} \cdot \frac{1}{\left(1 - \frac{w - z_0}{z - z_0}\right)} \, dw \\ &= -\frac{1}{2\pi i} \int_{C_3} \sum_{n=0}^{\infty} f(w) \frac{(w - z_0)^n}{(z - z_0)^{n+1}} \, dw \\ &= -\frac{1}{2\pi i} \sum_{n=0}^{\infty} \left( \int_{C_1} f(w) (w - z_0)^n \, dw \right) (z - z_0)^{-n-1} \\ &= -\sum_{n=1}^{\infty} \frac{b_n}{(z - z_0)^n}. \end{split}$$

In the last equality we changed the indexing to match the indexing in the statement of the theorem. Here  $b_n$  is defined by the integral formula given in the statement of the theorem. Examining the above argument we see that the only requirement on z is that  $|z - z_0| > r_1$ . So, this series converges for all such z.

Combining these two formulas we have

$$f(z) = \frac{1}{2\pi i} \int_{C_1 - C_3} \frac{f(w)}{w - z} dw = \sum_{n=1}^{\infty} \frac{b_n}{(z - z_0)^n} + \sum_{n=0}^{\infty} a_n (z - z_0)^n$$

The last thing to note is that the integrals defining  $a_n$  and  $b_n$  do not depend on the exact radius of the circle of integration. Any circle inside A will produce the same values. We have proved all the statements in the theorem on Laurent series. QED

## 7.7.1 Examples of Laurent series

In general, the integral formulas are not a practical way of computing the Laurent coefficients. Instead we use various algebraic tricks. Even better, as we shall see, is the fact that often we don't really need all the coefficients and we will develop more techniques to compute those that we do need.

Example 7.20. Find the Laurent series for

$$f(z) = \frac{z+1}{z}$$

around  $z_0 = 0$ . Give the region where it is valid.

Solution: The answer is simply

$$f(z) = 1 + \frac{1}{z}.$$

This is a Laurent series, valid on the infinite region  $0 < |z| < \infty$ .

**Example 7.21.** Find the Laurent series for

$$f(z) = \frac{z}{z^2 + 1}$$

around  $z_0 = i$ . Give the region where your answer is valid. Identify the singular (principal) part.

Solution: Using partial fractions we have

$$f(z) = \frac{1}{2} \cdot \frac{1}{z-i} + \frac{1}{2} \cdot \frac{1}{z+i}$$

Since  $\frac{1}{z+i}$  is analytic at z=i it has a Taylor series expansion. We find it using geometric series.

$$\frac{1}{z+i} = \frac{1}{2i} \cdot \frac{1}{1+(z-i)/(2i)} = \frac{1}{2i} \sum_{n=0}^{\infty} \left(-\frac{z-i}{2i}\right)^n$$

So the Laurent series is

$$f(z) = \frac{1}{2} \cdot \frac{1}{z-i} + \frac{1}{4i} \sum_{n=0}^{\infty} \left( -\frac{z-i}{2i} \right)^n$$

The singular (principal) part is given by the first term. The region of convergence is 0 < |z - i| < 2.

**Note.** We could have looked at f(z) on the region  $2 < |z - i| < \infty$ . This would have produced a different Laurent series. We discuss this further in an upcoming example.

**Example 7.22.** Compute the Laurent series for

$$f(z) = \frac{z+1}{z^3(z^2+1)}$$

on the region A: 0 < |z| < 1 centered at z = 0.

Solution: This function has isolated singularities at  $z = 0, \pm i$ . Therefore it is analytic on the region A.

f(z) has singularities at  $z = 0, \pm i$ .

At z = 0 we have

$$f(z) = \frac{1}{z^3} (1+z)(1-z^2+z^4-z^6+\ldots).$$

Multiplying this out we get

$$f(z) = \frac{1}{z^3} + \frac{1}{z^2} - \frac{1}{z} - 1 + z + z^2 - z^3 - \dots$$

The following example shows that the Laurent series depends on the region under consideration.

**Example 7.23.** Find the Laurent series around z = 0 for  $f(z) = \frac{1}{z(z-1)}$  in each of the following regions:

- (i) the region  $A_1: 0 < |z| < 1$
- (ii) the region  $A_2$ :  $1 < |z| < \infty$ .

Solution: For (i)

$$f(z) = -\frac{1}{z} \cdot \frac{1}{1-z} = -\frac{1}{z}(1+z+z^2+...) = -\frac{1}{z}-1-z-z^2-...$$

For (ii): Since the usual geometric series for 1/(1-z) does not converge on  $A_2$  we need a different form,

$$f(z) = \frac{1}{z} \cdot \frac{1}{z(1 - 1/z)} = \frac{1}{z^2} \left( 1 + \frac{1}{z} + \frac{1}{z^2} + \dots \right)$$

Since |1/z| < 1 on  $A_2$  our use of the geometric series is justified.

One lesson from this example is that the Laurent series depends on the region as well as the formula for the function.

#### 7.8 Digression to differential equations

Here is a standard use of series for solving differential equations.

**Example 7.24.** Find a power series solution to the equation

$$f'(x) = f(x) + 2,$$
  $f(0) = 0.$ 

Solution: We look for a solution of the form

$$f(x) = \sum_{n=0}^{\infty} a_n x^n.$$

Using the initial condition we find  $f(0) = 0 = a_0$ . Substituting the series into the differential equation we get

$$f'(x) = a_1 + 2a_2x + 3a_3x^3 + \dots = f(x) + 2 = a_0 + 2 + a_1x + a_2x^2 + \dots$$

Equating coefficients and using  $a_0 = 0$  we have

$$a_1 = a_0 + 2$$
  $\Rightarrow a_1 = 2$   
 $2a_2 = a_1$   $\Rightarrow a_2 = a_1/2 = 1$   
 $3a_3 = a_2$   $\Rightarrow a_3 = 1/3$   
 $4a_4 = a_3$   $\Rightarrow a_4 = 1/(3 \cdot 4)$ 

In general

$$(n+1)a_{n+1} = a_n \quad \Rightarrow \quad a_{n+1} = \frac{a_n}{(n+1)} = \frac{1}{3 \cdot 4 \cdot 5 \cdots (n+1)}.$$

You can check using the ratio test that this function is entire.

#### **7.9 Poles**

Poles refer to isolated singularities. So, we suppose f(z) is analytic on  $0 < |z - z_0| < r$  and has Laurent series

$$f(z) = \sum_{n=1}^{\infty} \frac{b_n}{(z - z_0)^n} + \sum_{n=0}^{\infty} a_n (z - z_0)^n.$$

**Definition of poles.** If only a finite number of the coefficients  $b_n$  are nonzero we say  $z_0$  is a finite pole of f. In this case, if  $b_k \neq 0$  and  $b_n = 0$  for all n > k then we say  $z_0$  is a pole of order k.

- If  $z_0$  is a pole of order 1 we say it is a simple pole of f.
- If an infinite number of the  $b_n$  are nonzero we say that  $z_0$  is an essential singularity or a pole of infinite order of f.
- If all the  $b_n$  are 0, then  $z_0$  is called a removable singularity. That is, if we define  $f(z_0) = a_0$  then f is analytic on the disk  $|z z_0| < r$ .

The terminology can be a bit confusing. So, imagine that I tell you that f is defined and analytic on the punctured disk  $0 < |z - z_0| < r$ . Then, a priori we assume f has a singularity at  $z_0$ . But, if after computing the Laurent series we see there is no singular part we can extend the definition of f to the full disk, thereby 'removing the singularity'.

We can explain the term essential singularity as follows. If f(z) has a pole of order k at  $z_0$  then  $(z-z_0)^k f(z)$  is analytic (has a removable singularity) at  $z_0$ . So, f(z) itself is not much harder to work with than an analytic function. On the other hand, if  $z_0$  is an essential singularity then no algebraic trick will change f(z) into an analytic function at  $z_0$ .

## 7.9.1 Examples of poles

We'll go back through many of the examples from the previous sections.

**Example 7.25.** The rational function

$$f(z) = \frac{1 + 2z^2}{z^3 + z^5}$$

expanded to

$$f(z) = \left(\frac{1}{z^3} + \frac{1}{z}\right) - \sum_{n=0}^{\infty} (-1)^n z^{2n+1}.$$

Thus, z = 0 is a pole of order 3.

Example 7.26. Consider

$$f(z) = \frac{z+1}{z} = 1 + \frac{1}{z}.$$

Thus, z = 0 is a pole of order 1, i.e. a simple pole.

Example 7.27. Consider

$$f(z) = \frac{z}{z^2 + 1} = \frac{1}{2} \cdot \frac{1}{z - i} + g(z),$$

where g(z) is analytic at z = i. So, z = i is a simple pole.

Example 7.28. The function

$$f(z) = \frac{1}{z(z-1)}$$

has isolated singularities at z = 0 and z = 1. Show that both are simple poles.

Solution: In a neighborhood of z = 0 we can write

$$f(z) = \frac{g(z)}{z}$$
, where  $g(z) = \frac{1}{z-1}$ .

Since g(z) is analytic at 0, z = 0 is a finite pole. Since  $g(0) \neq 0$ , the pole has order 1, i.e. it is simple.

Likewise, in a neighborhood of z = 1,

$$f(z) = \frac{h(z)}{z-1}$$
, where  $h(z) = \frac{1}{z}$ .

Since h is analytic at z = 1, f has a finite pole there. Since  $h(1) \neq 0$  it is simple.

Example 7.29. Consider

$$e^{1/z} = 1 + \frac{1}{z} + \frac{1}{2!z^2} + \frac{1}{3!z^3} + \dots$$

So, z = 0 is an essential singularity.

**Example 7.30.** log(z) has a singularity at z = 0. Since the singularity is not isolated, it can't be classified as either a pole or an essential singularity.

#### 7.9.2 Residues

In preparation for discussing the residue theorem in the next topic we give the definition and an example here.

Note well, residues have to do with isolated singularites.

**Definition 7.31.** Consider the function f(z) with an isolated singularity at  $z_0$ , i.e. defined on  $0 < |z - z_0| < r$  and with Laurent series

$$f(z) = \sum_{n=1}^{\infty} \frac{b_n}{(z - z_0)^n} + \sum_{n=0}^{\infty} a_n (z - z_0)^n.$$

The residue of f at  $z_0$  is  $b_1$ . This is denoted

$$\operatorname{Res}(f, z_0)$$
 or  $\operatorname{Res}_{z=z_0} f = b_1$ .

What is the importance of the residue? If  $\gamma$  is a small, simple closed curve that goes counterclockwise around  $z_0$  then

$$\int_{\mathcal{X}} f(z) = 2\pi i b_1.$$

 $\gamma$  is small enough to be inside  $|z - z_0| < r$ , and surround  $z_0$ .

This is easy to see by integrating the Laurent series term by term. The only nonzero integral comes from the term  $b_1/z$ .

**Example 7.32.** The function

$$f(z) = e^{1/(2z)} = 1 + \frac{1}{2z} + \frac{1}{2(2z)^2} + \dots$$

has an isolated singularity at 0. From the Laurent series we see that

$$\operatorname{Res}(f,0) = \frac{1}{2}.$$

## 7.10 Appendix: convergence

This section needs to be completed. It will give some of the careful technical definitions and arguments regarding convergence and manipulation of series. In particular it will define the notion

of uniform convergence. The short description is that all of our manipulations of power series are justified on any closed bounded region. Almost, everything we did can be restricted to a closed disk or annulus, and so was valid.

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 8 Notes**

Jeremy Orloff

## 8 Residue Theorem

### 8.1 Poles and zeros

We remind you of the following terminology: Suppose f(z) is analytic at  $z_0$  and

$$f(z) = a_n(z - z_0)^n + a_{n+1}(z - z_0)^{n+1} + \dots,$$

with  $a_n \neq 0$ . Then we say f has a zero of order n at  $z_0$ . If n = 1 we say  $z_0$  is a simple zero.

Suppose f has an *isolated* singularity at  $z_0$  and Laurent series

$$f(z) = \frac{b_n}{(z - z_0)^n} + \frac{b_{n-1}}{(z - z_0)^{n-1}} + \dots + \frac{b_1}{z - z_0} + a_0 + a_1(z - z_0) + \dots$$

which converges on  $0 < |z - z_0| < R$  and with  $b_n \ne 0$ . Then we say f has a pole of order n at  $z_0$ . If n = 1 we say  $z_0$  is a simple pole.

There are several examples in the Topic 7 notes. Here is one more

### Example 8.1.

$$f(z) = \frac{z+1}{z^3(z^2+1)}$$

has isolated singularities at  $z = 0, \pm i$  and a zero at z = -1. We will show that z = 0 is a pole of order 3,  $z = \pm i$  are poles of order 1 and z = -1 is a zero of order 1. The style of argument is the same in each case.

At z = 0:

$$f(z) = \frac{1}{z^3} \cdot \frac{z+1}{z^2+1}.$$

Call the second factor g(z). Since g(z) is analytic at z=0 and g(0)=1, it has a Taylor series

$$g(z) = \frac{z+1}{z^2+1} = 1 + a_1 z + a_2 z^2 + \dots$$

Therefore

$$f(z) = \frac{1}{z^3} + \frac{a_1}{z^2} + \frac{a_2}{z} + \dots$$

This shows z = 0 is a pole of order 3.

At z = i:  $f(z) = \frac{1}{z-i} \cdot \frac{z+1}{z^3(z+i)}$ . Call the second factor g(z). Since g(z) is analytic at z = i, it has a Taylor series

$$g(z) = \frac{z+1}{z^3(z+i)} = a_0 + a_1(z-i) + a_2(z-i)^2 + \dots$$

where  $a_0 = g(i) \neq 0$ . Therefore

$$f(z) = \frac{a_0}{z - i} + a_1 + a_2(z - i) + \dots$$

This shows z = i is a pole of order 1.

The arguments for z = -i and z = -1 are similar.

## 8.2 Words: Holomorphic and meromorphic

**Definition.** A function that is analytic on a region A is called holomorphic on A.

A function that is analytic on A except for a set of poles of finite order is called meromorphic on A.

Example 8.2. Let

$$f(z) = \frac{z + z^2 + z^3}{(z - 2)(z - 3)(z - 4)(z - 5)}.$$

This is meromorphic on C with (simple) poles at z = 2, 3, 4, 5

### 8.3 Behavior of functions near zeros and poles

The basic idea is that near a zero of order n, a function behaves like  $(z-z_0)^n$  and near a pole of order n, a function behaves like  $1/(z-z_0)^n$ . The following make this a little more precise.

**Behavior near a zero.** If f has a zero of order n at  $z_0$  then near  $z_0$ ,

$$f(z) \approx a_n (z - z_0)^n,$$

for some constant  $a_n$ .

*Proof.* By definition f has a Taylor series around  $z_0$  of the form

$$f(z) = a_n (z - z_0)^n + a_{n+1} (z - z_0)^{n+1} + \dots$$
  
=  $a_n (z - z_0)^n \left( 1 + \frac{a_{n+1}}{a_n} (z - z_0) + \frac{a_{n+2}}{a_n} (z - z_0)^2 + \dots \right)$ 

Since the second factor equals 1 at  $z_0$ , the claim follows.

**Behavior near a finite pole.** If f has a pole of order n at  $z_0$  then near  $z_0$ ,

$$f(z) \approx \frac{b_n}{(z - z_0)^n},$$

for some constant  $b_n$ .

*Proof.* This is nearly identical to the previous argument. By definition f has a Laurent series around  $z_0$  of the form

$$f(z) = \frac{b_n}{(z - z_0)^n} + \frac{b_{n-1}}{(z - z_0)^{n-1}} + \dots + \frac{b_1}{z - z_0} + a_0 + \dots$$
$$= \frac{b_n}{(z - z_0)^n} \left( 1 + \frac{b_{n-1}}{b_n} (z - z_0) + \frac{b_{n-2}}{b_n} (z - z_0)^2 + \dots \right)$$

Since the second factor equals 1 at  $z_0$ , the claim follows.

#### 8.3.1 Picard's theorem and essential singularities

Near an essential singularity we have Picard's theorem. We won't prove or make use of this theorem in 18.04. Still, we feel it is pretty enough to warrant showing to you.

**Picard's theorem.** If f(z) has an essential singularity at  $z_0$  then in every neighborhood of  $z_0$ , f(z) takes on all possible values infinitely many times, with the possible exception of one value.

**Example 8.3.** It is easy to see that in any neighborhood of z = 0 the function  $w = e^{1/z}$  takes every value except w = 0.

### 8.3.2 Quotients of functions

We have the following statement about quotients of functions. We could make similar statements if one or both functions has a pole instead of a zero.

**Theorem.** Suppose f has a zero of order m at  $z_0$  and g has a zero of order n at  $z_0$ . Let

$$h(z) = \frac{f(z)}{g(z)}.$$

Then

- If n > m then h(z) has a pole of order n m at  $z_0$ .
- If n < m then h(z) has a zero of order m n at  $z_0$ .
- If n = m then h(z) is analytic and nonzero at  $z_0$ .

We can paraphrase this as h(z) has 'pole' of order n - m at  $z_0$ . If n - m is negative then the 'pole' is actually a zero.

*Proof.* You should be able to supply the proof. It is nearly identical to the proofs above: express f and g as Taylor series and take the quotient.

#### Example 8.4. Let

$$h(z) = \frac{\sin(z)}{z^2}.$$

We know  $\sin(z)$  has a zero of order 1 at z = 0 and  $z^2$  has a zero of order 2. So, h(z) has a pole of order 1 at z = 0. Of course, we can see this easily using Taylor series

$$h(z) = \frac{1}{z^2} \left( z - \frac{z^3}{3!} + \dots \right)$$

### 8.4 Residues

In this section we'll explore calculating residues. We've seen enough already to know that this will be useful. We will see that even more clearly when we look at the residue theorem in the next section.

We introduced residues in the previous topic. We repeat the definition here for completeness.

**Definition.** Consider the function f(z) with an isolated singularity at  $z_0$ , i.e. defined on the region  $0 < |z - z_0| < r$  and with Laurent series (on that region)

$$f(z) = \sum_{n=1}^{\infty} \frac{b_n}{(z - z_0)^n} + \sum_{n=0}^{\infty} a_n (z - z_0)^n.$$

The residue of f at  $z_0$  is  $b_1$ . This is denoted

$$Res(f, z_0) = b_1$$
 or  $Res_{z=z_0} f = b_1$ .

What is the importance of the residue? If  $\gamma$  is a small, simple closed curve that goes counterclockwise around  $b_1$  then

$$\int_{\gamma} f(z) = 2\pi i b_1.$$

 $\gamma$  small enough to be inside  $|z - z_0| < r$ , surround  $z_0$  and contain no other singularity of f.

This is easy to see by integrating the Laurent series term by term. The only nonzero integral comes from the term  $b_1/z$ .

### Example 8.5.

$$f(z) = e^{1/2z} = 1 + \frac{1}{2z} + \frac{1}{2(2z)^2} + \dots$$

has an isolated singularity at 0. From the Laurent series we see that Res(f, 0) = 1/2.

### Example 8.6.

(i) Let

$$f(z) = \frac{1}{z^3} + \frac{2}{z^2} + \frac{4}{z} + 5 + 6z.$$

f has a pole of order 3 at z = 0 and Res(f, 0) = 4.

(ii) Suppose

$$f(z) = \frac{2}{z} + g(z),$$

where g is analytic at z = 0. Then, f has a simple pole at 0 and Res(f, 0) = 2.

(iii) Let

$$f(z) = \cos(z) = 1 - z^2/2! + \dots$$

Then f is analytic at z = 0 and Res(f, 0) = 0.

(iv) Let

$$f(z) = \frac{\sin(z)}{z} = \frac{1}{z} \left( z - \frac{z^3}{3!} + \dots \right) = 1 - \frac{z^2}{3!} + \dots$$

So, f has a removable singularity at z = 0 and Res(f, 0) = 0.

#### **Example 8.7.** Using partial fractions. Let

$$f(z) = \frac{z}{z^2 + 1}.$$

Find the poles and residues of f.

Solution: Using partial fractions we write

$$f(z) = \frac{z}{(z-i)(z+i)} = \frac{1}{2} \cdot \frac{1}{z-i} + \frac{1}{2} \cdot \frac{1}{z+i}.$$

The poles are at  $z = \pm i$ . We compute the residues at each pole:

At z = i:

$$f(z) = \frac{1}{2} \cdot \frac{1}{z - i}$$
 + something analytic at *i*.

Therefore the pole is simple and Res(f, i) = 1/2.

At z = -i:

$$f(z) = \frac{1}{2} \cdot \frac{1}{z+i} + \text{ something analytic at } -i.$$

Therefore the pole is simple and Res(f, -i) = 1/2.

Example 8.8. Mild warning! Let

$$f(z) = -\frac{1}{z(1-z)}$$

then we have the following Laurent expansions for f around z = 0.

On 0 < |z| < 1:

$$f(z) = -\frac{1}{z} \cdot \frac{1}{1-z} = -\frac{1}{z}(1+z+z^2+...).$$

Therefore the pole at z = 0 is simple and Res(f, 0) = -1.

On  $1 < |z| < \infty$ :

$$f(z) = \frac{1}{z^2} \cdot \frac{1}{1 - 1/z} = \frac{1}{z^2} \left( 1 + \frac{1}{z} + \frac{1}{z^2} + \dots \right).$$

Even though this is a valid Laurent expansion you must not use it to compute the residue at 0. This is because the definition of residue requires that we use the Laurent series on the region  $0 < |z - z_0| < r$ .

#### Example 8.9. Let

$$f(z) = \log(1+z).$$

This has a singularity at z = -1, but it is not isolated, so not a pole and therefore there is no residue at z = -1.

### 8.4.1 Residues at simple poles

Simple poles occur frequently enough that we'll study computing their residues in some detail. Here are a number of ways to spot a simple pole and compute its residue. The justification for all of them goes back to Laurent series.

Suppose f(z) has an isolated singularity at  $z = z_0$ . Then we have the following properties.

**Property 1.** If the Laurent series for f(z) has the form

$$\frac{b_1}{z - z_0} + a_0 + a_1(z - z_0) + \dots$$

then f has a simple pole at  $z_0$  and  $Res(f, z_0) = b_1$ .

### Property 2 If

$$g(z) = (z - z_0)f(z)$$


is analytic at  $z_0$  then  $z_0$  is either a simple pole or a removable singularity. In either case  $Res(f, z_0) = g(z_0)$ . (In the removable singularity case the residue is 0.)

*Proof.* Directly from the Laurent series for f around  $z_0$ .

**Property 3.** If f has a simple pole at  $z_0$  then

$$\lim_{z \to z_0} (z - z_0) f(z) = \text{Res}(f, z_0)$$

This says that the limit exists and equals the residue. Conversely, if the limit exists then either the pole is simple, or f is analytic at  $z_0$ . In both cases the limit equals the residue.

*Proof.* Directly from the Laurent series for f around  $z_0$ .

**Property 4.** If f has a simple pole at  $z_0$  and g(z) is analytic at  $z_0$  then

$$\operatorname{Res}(fg, z_0) = g(z_0) \operatorname{Res}(f, z_0).$$

If  $g(z_0) \neq 0$  then

$$Res(f/g, z_0) = \frac{1}{g(z_0)} Res(f, z_0).$$

*Proof.* Since  $z_0$  is a simple pole,

$$f(z) = \frac{b_1}{z - z_0} + a_0 + a_1(z - z_0)$$

Since g is analytic,

$$g(z) = c_0 + c_1(z - z_0) + \dots,$$

where  $c_0 = g(z_0)$ . Multiplying these series together it is clear that

$$Res(fg, z_0) = c_0 b_1 = g(z_0) Res(f, z_0).$$
 QED

The statement about quotients f/g follows from the proof for products because 1/g is analytic at  $z_0$ .

**Property 5.** If g(z) has a simple zero at  $z_0$  then 1/g(z) has a simple pole at  $z_0$  and

Res
$$(1/g, z_0) = \frac{1}{g'(z_0)}$$
.

*Proof.* The algebra for this is similar to what we've done several times above. The Taylor expansion for *g* is

$$g(z) = a_1(z - z_0) + a_2(z - z_0)^2 + \dots,$$

where  $a_1 = g'(z_0)$ . So

$$\frac{1}{g(z)} = \frac{1}{a_1(z - z_0)} \left( \frac{1}{1 + \frac{a_2}{a_1}(z - z_0) + \dots} \right)$$

The second factor on the right is analytic at  $z_0$  and equals 1 at  $z_0$ . Therefore we know the Laurent expansion of 1/g is

$$\frac{1}{g(z)} = \frac{1}{a_1(z - z_0)} \left( 1 + c_1(z - z_0) + \dots \right)$$

Clearly the residue is  $1/a_1 = 1/g'(z_0)$ . QED.

### Example 8.10. Let

$$f(z) = \frac{2+z+z^2}{(z-2)(z-3)(z-4)(z-5)}.$$

Show all the poles are simple and compute their residues.

Solution: The poles are at z=2,3,4,5. They are all isolated. We'll look at z=2 the others are similar. Multiplying by z-2 we get

$$g(z) = (z-2)f(z) = \frac{2+z+z^2}{(z-3)(z-4)(z-5)}.$$

This is analytic at z = 2 and

$$g(2) = \frac{8}{-6} = -\frac{4}{3}.$$

So the pole is simple and Res(f, 2) = -4/3.

#### Example 8.11. Let

$$f(z) = \frac{1}{\sin(z)}.$$

Find all the poles and their residues.

Solution: The poles of f(z) are the zeros of  $\sin(z)$ , i.e.  $n\pi$  for n an integer. Since the derivative

$$\sin'(n\pi) = \cos(n\pi) \neq 0,$$

the zeros are simple and by Property 5 above

$$\operatorname{Res}(f, n\pi) = \frac{1}{\cos(n\pi)} = (-1)^n.$$

#### Example 8.12. Let

$$f(z) = \frac{1}{z(z^2 + 1)(z - 2)^2}.$$

Identify all the poles and say which ones are simple.

Solution: Clearly the poles are at  $z = 0, \pm i, 2$ .

At z = 0:

$$g(z) = z f(z)$$

is analytic at 0 and g(0) = 1/4. So the pole is simple and the residue is g(0) = 1/4.

At z = i:

$$g(z) = (z - i)f(z) = \frac{1}{z(z + i)(z - 2)^2}$$

is analytic at i, the pole is simple and the residue is g(i).

At z = -i: This is similar to the case z = i. The pole is simple.

At z = 2:

$$g(z) = (z-2)f(z) = \frac{1}{z(z^2+1)(z-2)}$$

is not analytic at 2, so the pole is not simple. (It should be obvious that it's a pole of order 2.)

**Example 8.13.** Let p(z), q(z) be analytic at  $z = z_0$ . Assume  $p(z_0) \neq 0$ ,  $q(z_0) = 0$ ,  $q'(z_0) \neq 0$ . Find

$$\operatorname{Res}_{z=z_0} \frac{p(z)}{q(z)}.$$

Solution: Since  $q'(z_0) \neq 0$ , q has a simple zero at  $z_0$ . So 1/q has a simple pole at  $z_0$  and

$$Res(1/q, z_0) = \frac{1}{q'(z_0)}$$

Since  $p(z_0) \neq 0$  we know

$$\operatorname{Res}(p/q, z_0) = p(z_0) \operatorname{Res}(1/q, z_0) = \frac{p(z_0)}{q'(z_0)}.$$

### 8.4.2 Residues at finite poles

For higher-order poles we can make statements similar to those for simple poles, but the formulas and computations are more involved. The general principle is the following

**Higher order poles.** If f(z) has a pole of order k at  $z_0$  then

$$g(z) = (z - z_0)^k f(z)$$

is analytic at  $z_0$  and if

$$g(z) = a_0 + a_1(z - z_0) + \dots$$

then

Res
$$(f, z_0) = a_{k-1} = \frac{g^{(k-1)}(z_0)}{(k-1)!}$$
.

*Proof.* This is clear using Taylor and Laurent series for g and f.

#### Example 8.14. Let

$$f(z) = \frac{\sinh(z)}{z^5}$$

and find the residue at z = 0.

Solution: We know the Taylor series for

$$\sinh(z) = z + z^3/3! + z^5/5! + \dots$$

(You can find this using  $\sinh(z) = (e^z - e^{-z})/2$  and the Taylor series for  $e^z$ .) Therefore,

$$f(z) = \frac{1}{z^4} + \frac{1}{3!z^2} + \frac{1}{5!} + \dots$$

We see Res(f, 0) = 0.

Note, we could have seen this by realizing that f(z) is an even function.

### Example 8.15. Let

$$f(z) = \frac{\sinh(z)e^z}{z^5}.$$

Find the residue at z = 0.

Solution: It is clear that Res(f, 0) equals the coefficient of  $z^4$  in the Taylor expansion of  $sinh(z)e^z$ . We compute this directly as

$$\sinh(z)e^{z} = \left(z + \frac{z^{3}}{3!} + \dots\right) \left(1 + z + \frac{z^{2}}{2} + \frac{z^{3}}{3!} + \dots\right) = \dots + \left(\frac{1}{4!} + \frac{1}{3!}\right)z^{4} + \dots$$

So

$$\operatorname{Res}(f,0) = \frac{1}{3!} + \frac{1}{4!} = \frac{5}{24}.$$

**Example 8.16.** Find the residue of

$$f(z) = \frac{1}{z(z^2 + 1)(z - 2)^2}$$

at z = 2.

Solution:  $g(z) = (z-2)^2 f(z) = \frac{1}{z(z^2+1)}$  is analytic at z=2. So, the residue we want is the  $a_1$  term in its Taylor series, i.e. g'(2). This is easy, if dull, to compute

$$\operatorname{Res}(f,2) = g'(2) = -\frac{13}{100}$$

### **8.4.3** $\cot(z)$

The function  $\cot(z)$  turns out to be very useful in applications. This stems largely from the fact that it has simple poles at all multiples of  $\pi$  and the residue is 1 at each pole. We show that first.

**Fact.**  $f(z) = \cot(z)$  has simple poles at  $n\pi$  for n an integer and  $\operatorname{Res}(f, n\pi) = 1$ .

Proof.

$$f(z) = \frac{\cos(z)}{\sin(z)}.$$

This has poles at the zeros of sin, i.e. at  $z = n\pi$ . At poles f is of the form p/q where q has a simple zero at  $z_0$  and  $p(z_0) \neq 0$ . Thus we can use the formula

Res
$$(f, z_0) = \frac{p(z_0)}{q'(z_0)}$$
.

In our case, we have

$$\operatorname{Res}(f, n\pi) = \frac{\cos(n\pi)}{\cos(n\pi)} = 1,$$

as claimed.

Sometimes we need more terms in the Laurent expansion of cot(z). There is no known easy formula for the terms, but we can easily compute as many as we need using the following technique.

**Example 8.17.** Compute the first several terms of the Laurent expansion of cot(z) around z=0.

Solution: Since cot(z) has a simple pole at 0 we know

$$\cot(z) = \frac{b_1}{z} + a_0 + a_1 z + a_2 z^2 + \dots$$

We also know

$$\cot(z) = \frac{\cos(z)}{\sin(z)} = \frac{1 - z^2/2 + z^4/4! - \dots}{z - z^3/3! + z^5/5! - \dots}$$

Cross multiplying the two expressions we get

$$\left(\frac{b_1}{z} + a_0 + a_1 z + a_2 z^2 + \dots\right) \left(z - \frac{z^3}{3!} + \frac{z^5}{5!} - \dots\right) = 1 - \frac{z^2}{2} + \frac{z^4}{4!} - \dots$$

We can do the multiplication and equate the coefficients of like powers of z

$$b_1 + a_0 z + \left(-\frac{b_1}{3!} + a_1\right) z^2 + \left(-\frac{a_0}{3!} + a_2\right) z^3 + \left(\frac{b_1}{5!} - \frac{a_1}{3!} + a_3\right) z^4 = 1 - \frac{z^2}{2!} + \frac{z^4}{4!}$$

So, starting from  $b_1 = 1$  and  $a_0 = 0$ , we get

$$-b_1/3! + a_1 = -1/2!$$
  $\Rightarrow a_1 = -1/3$   
 $-a_0/3! + a_2 = 0$   $\Rightarrow a_2 = 0$   
 $b_1/5! - a_1/3! + a_3 = 1/4!$   $\Rightarrow a_3 = -1/45$ 

As noted above, all the even terms are 0 as they should be. We have

$$\cot(z) = \frac{1}{z} - \frac{z}{3} - \frac{z^3}{45} + \dots$$

### 8.5 Cauchy Residue Theorem

This is one of the major theorems in 18.04. It will allow us to make systematic our previous somewhat ad hoc approach to computing integrals on contours that surround singularities.

**Theorem.** (Cauchy's residue theorem) Suppose f(z) is analytic in the region A except for a set of isolated singularities. Also suppose C is a simple closed curve in A that doesn't go through any of the singularities of f and is oriented counterclockwise. Then

$$\int_C f(z) dz = 2\pi i \sum \text{ residues of } f \text{ inside } C$$

*Proof.* The proof is based of the following figures. They only show a curve with two singularities inside it, but the generalization to any number of signularities is straightforward. In what follows we are going to abuse language and say pole when we mean isolated singularity, i.e. a finite order pole or an essential singularity ('infinite order pole').

The left figure shows the curve C surrounding two poles  $z_1$  and  $z_2$  of f. The right figure shows the same curve with some cuts and small circles added. It is chosen so that there are no poles of f inside it and so that the little circles around each of the poles are so small that there are no other poles inside them. The right hand curve is

$$\tilde{C} = C_1 + C_2 - C_3 - C_2 + C_4 + C_5 - C_6 - C_5$$

The left hand curve is  $C = C_1 + C_4$ . Since there are no poles inside  $\tilde{C}$  we have, by Cauchy's theorem,

$$\int_{\tilde{C}} f(z) dz = \int_{C_1 + C_2 - C_3 - C_2 + C_4 + C_5 - C_6 - C_5} f(z) dz = 0$$

Dropping  $C_2$  and  $C_5$ , which are both added and subtracted, this becomes

$$\int_{C_1 + C_4} f(z) \, dz = \int_{C_3 + C_6} f(z) \, dz \tag{1}$$


If

$$f(z) = \dots + \frac{b_2}{(z - z_1)^2} + \frac{b_1}{z - z_1} + a_0 + a_1(z - z_1) + \dots$$

is the Laurent expansion of f around  $z_1$  then

$$\int_{C_3} f(z) dz = \int_{C_3} \dots + \frac{b_2}{(z - z_1)^2} + \frac{b_1}{z - z_1} + a_0 + a_1(z - z_1) + \dots dz$$

$$= 2\pi i b_1$$

$$= 2\pi i \operatorname{Res}(f, z_1)$$

Likewise

$$\int_{C_6} f(z) dz = 2\pi i \operatorname{Res}(f, z_2).$$

Using these residues and the fact that  $C = C_1 + C_4$ , Equation 1 becomes

$$\int_C f(z) dz = 2\pi i \left[ \text{Res}(f, z_1) + \text{Res}(f, z_2) \right].$$

That proves the residue theorem for the case of two poles. As we said, generalizing to any number of poles is straightforward.

#### Example 8.18. Let

$$f(z) = \frac{1}{z(z^2+1)}.$$

Compute  $\int f(z) dz$  over each of the contours  $C_1$ ,  $C_2$ ,  $C_3$ ,  $C_4$  shown.

Solution: The poles of f(z) are at  $z = 0, \pm i$ . Using the residue theorem we just need to compute the residues of each of these poles.

At z = 0:

$$g(z) = zf(z) = \frac{1}{z^2 + 1}$$

is analytic at 0 so the pole is simple and

$$Res(f, 0) = g(0) = 1.$$

At z = i:

$$g(z) = (z - i)f(z) = \frac{1}{z(z + i)}$$

is analytic at i so the pole is simple and

$$Res(f, i) = g(i) = -1/2.$$

At z = -i:

$$g(z) = (z+i)f(z) = \frac{1}{z(z-i)}$$

is analytic at -i so the pole is simple and

$$Res(f, -i) = g(-i) = -1/2.$$

Using the residue theorem we have

$$\begin{split} &\int_{C_1} f(z)\,dz = 0 \text{ (since } f \text{ is analytic inside } C_1) \\ &\int_{C_2} f(z)\,dz = 2\pi i\operatorname{Res}(f,i) = -\pi i \\ &\int_{C_3} f(z)\,dz = 2\pi i\left[\operatorname{Res}(f,i) + \operatorname{Res}(f,0)\right] = \pi i \\ &\int_{C_4} f(z)\,dz = 2\pi i\left[\operatorname{Res}(f,i) + \operatorname{Res}(f,0) + \operatorname{Res}(f,-i)\right] = 0. \end{split}$$

Example 8.19. Compute

$$\int_{|z|=2} \frac{5z-2}{z(z-1)} \, dz.$$

Solution: Let

$$f(z) = \frac{5z - 2}{z(z - 1)}.$$

The poles of f are at z = 0, 1 and the contour encloses them both.

At z = 0:

$$g(z) = zf(z) = \frac{5z - 2}{(z - 1)}$$

is analytic at 0 so the pole is simple and

$$Res(f, 0) = g(0) = 2.$$

At z = 1:

$$g(z) = (z - 1)f(z) = \frac{5z - 2}{z}$$

is analytic at 1 so the pole is simple and

$$Res(f, 1) = g(1) = 3.$$

Finally

$$\int_C \frac{5z - 2}{z(z - 1)} dz = 2\pi i \left[ \text{Res}(f, 0) + \text{Res}(f, 1) \right] = 10\pi i.$$

Example 8.20. Compute

$$\int_{|z|=1} z^2 \sin(1/z) \, dz.$$

Solution: Let

$$f(z) = z^2 \sin(1/z).$$

f has an isolated singularity at z = 0. Using the Taylor series for  $\sin(w)$  we get

$$z^{2}\sin(1/z) = z^{2}\left(\frac{1}{z} - \frac{1}{3!z^{3}} + \frac{1}{5!z^{5}} - \dots\right) = z - \frac{1/6}{z} + \dots$$

So,  $Res(f, 0) = b_1 = -1/6$ . Thus the residue theorem gives

$$\int_{|z|=1} z^2 \sin(1/z) \, dz = 2\pi i \operatorname{Res}(f,0) = -\frac{i\pi}{3}.$$

Example 8.21. Compute

$$\int_C \frac{dz}{z(z-2)^4} \, dz,$$

where, C: |z-2| = 1.

Solution: Let

$$f(z) = \frac{1}{z(z-2)^4}.$$

The singularity at z = 0 is outside the contour of integration so it doesn't contribute to the integral.

To use the residue theorem we need to find the residue of f at z=2. There are a number of ways to do this. Here's one:

$$\frac{1}{z} = \frac{1}{2 + (z - 2)}$$

$$= \frac{1}{2} \cdot \frac{1}{1 + (z - 2)/2}$$

$$= \frac{1}{2} \left( 1 - \frac{z - 2}{2} + \frac{(z - 2)^2}{4} - \frac{(z - 2)^3}{8} + \dots \right)$$

This is valid on 0 < |z - 2| < 2. So,

$$f(z) = \frac{1}{(z-2)^4} \cdot \frac{1}{z} = \frac{1}{2(z-2)^4} - \frac{1}{4(z-2)^3} + \frac{1}{8(z-2)^2} - \frac{1}{16(z-2)} + \dots$$

Thus, Res(f, 2) = -1/16 and

$$\int_C f(z) dz = 2\pi i \operatorname{Res}(f, 2) = -\frac{\pi i}{8}.$$

#### Example 8.22. Compute

$$\int_C \frac{1}{\sin(z)} \, dz$$

over the contour C shown.

Solution: Let

$$f(z) = 1/\sin(z).$$

There are 3 poles of f inside C at 0,  $\pi$  and  $2\pi$ . We can find the residues by taking the limit of  $(z-z_0)f(z)$ . Each of the limits is computed using L'Hospital's rule. (This is valid, since the rule is

just a statement about power series. We could also have used Property 5 from the section on residues of simple poles above.)

At z = 0:

$$\lim_{z \to 0} \frac{z}{\sin(z)} = \lim_{z \to 0} \frac{1}{\cos(z)} = 1.$$

Since the limit exists, z = 0 is a simple pole and

$$Res(f, 0) = 1.$$

At  $z = \pi$ :

$$\lim_{z \to \pi} \frac{z - \pi}{\sin(z)} = \lim_{z \to \pi} \frac{1}{\cos(z)} = -1.$$

Since the limit exists,  $z = \pi$  is a simple pole and

$$\operatorname{Res}(f, \pi) = -1.$$

At  $z = 2\pi$ : The same argument shows

$$Res(f, 2\pi) = 1.$$

Now, by the residue theorem

$$\int_C f(z) \, dz = 2\pi i \left[ \text{Res}(f, 0) + \text{Res}(f, \pi) + \text{Res}(f, 2\pi) \right] = 2\pi i.$$

#### 8.6 Residue at $\infty$

The residue at  $\infty$  is a clever device that can sometimes allow us to replace the computation of many residues with the computation of a single residue.

Suppose that f is analytic in  $\mathbb{C}$  except for a finite number of singularities. Let C be a positively oriented curve that is large enough to contain all the singularities.

All the poles of f are inside C

**Definition.** We define the residue of f at infinity by

$$\operatorname{Res}(f, \infty) = -\frac{1}{2\pi i} \int_C f(z) \, dz.$$

We should first explain the idea here. The interior of a simple closed curve is everything to left as you traverse the curve. The curve C is oriented counterclockwise, so its interior contains all the poles of f. The residue theorem says the integral over C is determined by the residues of these poles.

On the other hand, the interior of the curve -C is everything outside of C. There are no poles of f in that region. If we want the residue theorem to hold (which we do -it's that important) then the only option is to have a residue at  $\infty$  and define it as we did.

The definition of the residue at infinity assumes all the poles of f are inside C. Therefore the residue theorem implies

$$\operatorname{Res}(f, \infty) = -\sum$$
 the residues of  $f$ .

To make this useful we need a way to compute the residue directly. This is given by the following theorem.

**Theorem.** If f is analytic in C except for a finite number of singularities then

$$\operatorname{Res}(f, \infty) = -\operatorname{Res}\left(\frac{1}{w^2}f(1/w), 0\right).$$

*Proof.* The proof is just a change of variables: w = 1/z.

Change of variable: w = 1/z

First note that z = 1/w and

$$dz = -(1/w^2) dw.$$

Next, note that the map w = 1/z carries the positively oriented z-circle of radius R to the negatively oriented w-circle of radius 1/R. (To see the orientiation, follow the circled points 1, 2, 3, 4 on C in the z-plane as they are mapped to points on  $\tilde{C}$  in the w-plane.) Thus,

$$\operatorname{Res}(f, \infty) = -\frac{1}{2\pi i} \int_{C} f(z) dz = \frac{1}{2\pi i} \int_{\tilde{C}} f(1/w) \frac{1}{w^{2}} dw$$

Finally, note that z=1/w maps all the poles inside the circle C to points outside the circle  $\tilde{C}$ . So the only possible pole of  $(1/w^2)f(1/w)$  that is inside  $\tilde{C}$  is at w=0. Now, since  $\tilde{C}$  is oriented clockwise, the residue theorem says

$$\frac{1}{2\pi i} \int_{\tilde{C}} f(1/w) \frac{1}{w^2} dw = -\text{Res}\left(\frac{1}{w^2} f(1/w), 0\right)$$

Comparing this with the equation just above finishes the proof.

### Example 8.23. Let

$$f(z) = \frac{5z - 2}{z(z - 1)}.$$

Earlier we computed

$$\int_{|z|=2} f(z) dz = 10\pi i$$

by computing residues at z = 0 and z = 1. Recompute this integral by computing a single residue at infinity.

Solution:

$$\frac{1}{w^2}f(1/w) = \frac{1}{w^2} \frac{5/w - 2}{(1/w)(1/w - 1)} = \frac{5 - 2w}{w(1 - w)}.$$

We easily compute that

$$\operatorname{Res}(f, \infty) = -\operatorname{Res}\left(\frac{1}{w^2}f(1/w), 0\right) = -5.$$

Since |z| = 2 contains all the singularities of f we have

$$\int_{|z|=2} f(z) dz = -2\pi i \operatorname{Res}(f, \infty) = 10\pi i.$$

This is the same answer we got before!

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 9 Notes**

Jeremy Orloff

# 9 Definite integrals using the residue theorem

## 9.1 Introduction

In this topic we'll use the residue theorem to compute some real definite integrals.

$$\int_a^b f(x) \, dx$$

The general approach is always the same

- 1. Find a complex analytic function g(z) which either equals f on the real axis or which is closely connected to f, e.g.  $f(x) = \cos(x)$ ,  $g(z) = e^{iz}$ .
- 2. Pick a closed contour C that includes the part of the real axis in the integral.
- 3. The contour will be made up of pieces. It should be such that we can compute  $\int g(z) dz$  over each of the pieces except the part on the real axis.
- 4. Use the residue theorem to compute  $\int_C g(z) dz$ .
- 5. Combine the previous steps to deduce the value of the integral we want.

# 9.2 Integrals of functions that decay

The theorems in this section will guide us in choosing the closed contour C described in the introduction.

The first theorem is for functions that decay faster than 1/z.

**Theorem 9.1.** (a) Suppose f(z) is defined in the upper half-plane. If there is an a > 1 and M > 0 such that

$$|f(z)| < \frac{M}{|z|^a}$$

for |z| large then

$$\lim_{R\to\infty}\int_{C_R}f(z)\,dz=0,$$


where  $C_R$  is the semicircle shown below on the left.

Semicircles: left:  $Re^{i\theta}$ ,  $0 < \theta < \pi$  right:  $Re^{i\theta}$ ,  $\pi < \theta < 2\pi$ .

**(b)** If f(z) is defined in the lower half-plane and

$$|f(z)| < \frac{M}{|z|^a},$$

where a > 1 then

$$\lim_{R\to\infty}\int_{C_R}f(z)\,dz=0,$$

where  $C_R$  is the semicircle shown above on the right.

*Proof.* We prove (a), (b) is essentially the same. We use the triangle inequality for integrals and the estimate given in the hypothesis. For R large

$$\left| \int_{C_R} f(z) \, dz \right| \le \int_{C_R} |f(z)| \, |dz| \le \int_{C_R} \frac{M}{|z|^a} \, |dz| = \int_0^{\pi} \frac{M}{R^a} R \, d\theta = \frac{M\pi}{R^{a-1}}.$$

Since a > 1 this clearly goes to 0 as  $R \to \infty$ . QED

The next theorem is for functions that decay like 1/z. It requires some more care to state and prove.

**Theorem 9.2.** (a) Suppose f(z) is defined in the upper half-plane. If there is an M > 0 such that

$$|f(z)| < \frac{M}{|z|}$$

for |z| large then for a > 0

$$\lim_{x_1 \to \infty, x_2 \to \infty} \int_{C_1 + C_2 + C_2} f(z) e^{iaz} dz = 0,$$

where  $C_1 + C_2 + C_3$  is the rectangular path shown below on the left.

Rectangular paths of height and width  $x_1 + x_2$ .

(b) Similarly, if a < 0 then

$$\lim_{x_1 \to \infty, x_2 \to \infty} \int_{C_1 + C_2 + C_3} f(z) e^{iaz} dz = 0,$$

where  $C_1 + C_2 + C_3$  is the rectangular path shown above on the right.

**Note.** In contrast to Theorem 9.1 this theorem needs to include the factor  $e^{iaz}$ .

*Proof.* (a) We start by parametrizing  $C_1$ ,  $C_2$ ,  $C_3$ .

$$C_1$$
:  $\gamma_1(t) = x_1 + it$ , t from 0 to  $x_1 + x_2$ 

 $C_2$ :  $\gamma_2(t) = t + i(x_1 + x_2)$ , t from  $x_1$  to  $-x_2$ 

 $C_3$ :  $\gamma_3(t) = -x_2 + it$ , t from  $x_1 + x_2$  to 0.

Next we look at each integral in turn. We assume  $x_1$  and  $x_2$  are large enough that

$$|f(z)| < \frac{M}{|z|}$$

on each of the curves  $C_i$ .

$$\left| \int_{C_1} f(z) e^{iaz} dz \right| \le \int_{C_1} |f(z) e^{iaz}| |dz| \le \int_{C_1} \frac{M}{|z|} |e^{iaz}| |dz|$$

$$= \int_0^{x_1 + x_2} \frac{M}{\sqrt{x_1^2 + t^2}} |e^{iax_1 - at}| dt$$

$$\le \frac{M}{x_1} \int_0^{x_1 + x_2} e^{-at} dt$$

$$= \frac{M}{x_1} (1 - e^{-a(x_1 + x_2)}) / a.$$

Since a > 0, it is clear that this last expression goes to 0 as  $x_1$  and  $x_2$  go to  $\infty$ .

$$\left| \int_{C_2} f(z) e^{iaz} dz \right| \le \int_{C_2} |f(z) e^{iaz}| |dz| \le \int_{C_2} \frac{M}{|z|} |e^{iaz}| |dz|$$

$$= \int_{-x_2}^{x_1} \frac{M}{\sqrt{t^2 + (x_1 + x_2)^2}} |e^{iat - a(x_1 + x_2)}| dt$$

$$\le \frac{M e^{-a(x_1 + x_2)}}{x_1 + x_2} \int_0^{x_1 + x_2} dt$$

$$< M e^{-a(x_1 + x_2)}$$

Again, clearly this last expression goes to 0 as  $x_1$  and  $x_2$  go to  $\infty$ .

The argument for  $C_3$  is essentially the same as for  $C_1$ , so we leave it to the reader.

The proof for part (b) is the same. You need to keep track of the sign in the exponentials and make sure it is negative.

**Example.** See Example 9.16 below for an example using Theorem 9.2.

9.3 Integrals 
$$\int_{-\infty}^{\infty}$$
 and  $\int_{0}^{\infty}$ 

Example 9.3. Compute

$$I = \int_{-\infty}^{\infty} \frac{1}{(1+x^2)^2} \, dx.$$

Solution: Let

$$f(z) = 1/(1+z^2)^2$$
.

It is clear that for z large

$$f(z) \approx 1/z^4$$
.

In particular, the hypothesis of Theorem 9.1 is satisfied. Using the contour shown below we have, by the residue theorem,

$$\int_{C_1 + C_R} f(z) dz = 2\pi i \sum \text{ residues of } f \text{ inside the contour.}$$
 (1)

We examine each of the pieces in the above equation.

$$\int_{C_R} f(z) dz$$
: By Theorem 9.1(a),

$$\lim_{R \to \infty} \int_{C_R} f(z) \, dz = 0.$$

$$\int_{C_1} f(z) dz$$
: Directly, we see that

$$\lim_{R \to \infty} \int_{C_1} f(z) dz = \lim_{R \to \infty} \int_{-R}^{R} f(x) dx = \int_{-\infty}^{\infty} f(x) dx = I.$$

So letting  $R \to \infty$ , Equation 1 becomes

$$I = \int_{-\infty}^{\infty} f(x) dx = 2\pi i \sum$$
 residues of f inside the contour.

Finally, we compute the needed residues: f(z) has poles of order 2 at  $\pm i$ . Only z = i is inside the contour, so we compute the residue there. Let

$$g(z) = (z - i)^2 f(z) = \frac{1}{(z + i)^2}.$$

Then

Res
$$(f, i) = g'(i) = -\frac{2}{(2i)^3} = \frac{1}{4i}$$

So,

$$I = 2\pi i \operatorname{Res}(f, i) = \boxed{\frac{\pi}{2}}.$$

## Example 9.4. Compute

$$I = \int_{-\infty}^{\infty} \frac{1}{x^4 + 1} \, dx.$$

Solution: Let  $f(z) = 1/(1+z^4)$ . We use the same contour as in the previous example

As in the previous example,

$$\lim_{R \to \infty} \int_{C_R} f(z) \, dz = 0$$

and

$$\lim_{R \to \infty} \int_{C_1} f(z) \, dz = \int_{-\infty}^{\infty} f(x) \, dx = I.$$

So, by the residue theorem

$$I = \lim_{R \to \infty} \int_{C_1 + C_R} f(z) dz = 2\pi i \sum \text{ residues of } f \text{ inside the contour.}$$

The poles of f are all simple and at

$$e^{i\pi/4}$$
,  $e^{i3\pi/4}$ ,  $e^{i5\pi/4}$ ,  $e^{i7\pi/4}$ 

Only  $e^{i\pi/4}$  and  $e^{i3\pi/4}$  are inside the contour. We compute their residues as limits using L'Hospital's rule. For  $z_1 = e^{i\pi/4}$ :

$$\operatorname{Res}(f, z_1) = \lim_{z \to z_1} (z - z_1) f(z) = \lim_{z \to z_1} \frac{z - z_1}{1 + z^4} = \lim_{z \to z_1} \frac{1}{4z^3} = \frac{1}{4e^{i3\pi/4}} = \frac{e^{-i3\pi/4}}{4}$$

and for  $z_2 = e^{i3\pi/4}$ :

$$\operatorname{Res}(f, z_2) = \lim_{z \to z_2} (z - z_2) f(z) = \lim_{z \to z_2} \frac{z - z_2}{1 + z^4} = \lim_{z \to z_2} \frac{1}{4z^3} = \frac{1}{4e^{i9\pi/4}} = \frac{e^{-i\pi/4}}{4}$$

So.

$$I = 2\pi i (\text{Res}(f, z_1) + \text{Res}(f, z_2)) = 2\pi i \left(\frac{-1 - i}{4\sqrt{2}} + \frac{1 - i}{4\sqrt{2}}\right) = 2\pi i \left(-\frac{2i}{4\sqrt{2}}\right) = \boxed{\pi \frac{\sqrt{2}}{2}}$$

**Example 9.5.** Suppose b > 0. Show

$$\int_0^\infty \frac{\cos(x)}{x^2 + b^2} dx = \frac{\pi e^{-b}}{2b}.$$

Solution: The first thing to note is that the integrand is even, so

$$I = \frac{1}{2} \int_{-\infty}^{\infty} \frac{\cos(x)}{x^2 + b^2}.$$

Also note that the square in the denominator tells us the integral is absolutely convergent.

We have to be careful because cos(z) goes to infinity in either half-plane, so the hypotheses of Theorem 9.1 are not satisfied. The trick is to replace cos(x) by  $e^{ix}$ , so

$$\tilde{I} = \int_{-\infty}^{\infty} \frac{e^{ix}}{x^2 + b^2} dx$$
, with  $I = \frac{1}{2} \operatorname{Re}(\tilde{I})$ .

Now let

$$f(z) = \frac{\mathrm{e}^{iz}}{z^2 + h^2}.$$

For z = x + iy with y > 0 we have

$$|f(z)| = \frac{|e^{i(x+iy)}|}{|z^2 + b^2|} = \frac{e^{-y}}{|z^2 + b^2|}.$$

Since  $e^{-y} < 1$ , f(z) satisfies the hypotheses of Theorem 9.1 in the upper half-plane. Now we can use the same contour as in the previous examples

We have

$$\lim_{R \to \infty} \int_{C_R} f(z) \, dz = 0$$

and

$$\lim_{R \to \infty} \int_{C_1} f(z) \, dz = \int_{-\infty}^{\infty} f(x) \, dx = \tilde{I}.$$

So, by the residue theorem

$$\tilde{I} = \lim_{R \to \infty} \int_{C_1 + C_R} f(z) dz = 2\pi i \sum$$
 residues of  $f$  inside the contour.

The poles of f are at  $\pm bi$  and both are simple. Only bi is inside the contour. We compute the residue as a limit using L'Hospital's rule

Res
$$(f, bi)$$
 =  $\lim_{z \to bi} (z - bi) \frac{e^{iz}}{z^2 + b^2} = \frac{e^{-b}}{2bi}$ .

So,

$$\tilde{I} = 2\pi i \operatorname{Res}(f, bi) = \frac{\pi e^{-b}}{b}.$$

Finally,

$$I = \frac{1}{2} \operatorname{Re}(\tilde{I}) = \frac{\pi e^{-b}}{2h},$$

as claimed.

Warning: Be careful when replacing  $\cos(z)$  by  $e^{iz}$  that it is appropriate. A key point in the above example was that  $I = \frac{1}{2} \operatorname{Re}(\tilde{I})$ . This is needed to make the replacement useful.

# 9.4 Trigonometric integrals

The trick here is to put together some elementary properties of  $z = e^{i\theta}$  on the unit circle.

1. 
$$e^{-i\theta} = 1/z$$
.

2. 
$$\cos(\theta) = \frac{e^{i\theta} + e^{-i\theta}}{2} = \frac{z + 1/z}{2}$$
.

3. 
$$\sin(\theta) = \frac{e^{i\theta} - e^{-i\theta}}{2i} = \frac{z - 1/z}{2i}$$
.

We start with an example. After that we'll state a more general theorem.

### Example 9.6. Compute

$$\int_0^{2\pi} \frac{d\theta}{1 + a^2 - 2a\cos(\theta)}.$$

Assume that  $|a| \neq 1$ .

Solution: Notice that  $[0, 2\pi]$  is the interval used to parametrize the unit circle as  $z = e^{i\theta}$ . We need to make two substitutions:

$$\cos(\theta) = \frac{z + 1/z}{2}$$

$$dz = ie^{i\theta} d\theta \quad \Leftrightarrow \quad d\theta = \frac{dz}{iz}$$

Making these substitutions we get

$$I = \int_0^{2\pi} \frac{d\theta}{1 + a^2 - 2a\cos(\theta)}$$

$$= \int_{|z|=1} \frac{1}{1 + a^2 - 2a(z + 1/z)/2} \cdot \frac{dz}{iz}$$

$$= \int_{|z|=1} \frac{1}{i((1 + a^2)z - a(z^2 + 1))} dz.$$

So, let

$$f(z) = \frac{1}{i((1+a^2)z - a(z^2+1))}.$$

The residue theorem implies

$$I = 2\pi i \sum$$
 residues of f inside the unit circle.

We can factor the denominator:

$$f(z) = \frac{-1}{ia(z-a)(z-1/a)}.$$

The poles are at a, 1/a. One is inside the unit circle and one is outside.

If |a| > 1 then 1/a is inside the unit circle and  $Res(f, 1/a) = \frac{1}{i(a^2 - 1)}$ 

If |a| < 1 then a is inside the unit circle and  $\operatorname{Res}(f, a) = \frac{1}{i(1 - a^2)}$ 

We have

$$I = \begin{cases} \frac{2\pi}{a^2 - 1} & \text{if } |a| > 1\\ \frac{2\pi}{1 - a^2} & \text{if } |a| < 1 \end{cases}$$

The example illustrates a general technique which we state now.

**Theorem 9.7.** Suppose R(x, y) is a rational function with no poles on the circle

$$x^2 + v^2 = 1$$

then for

$$f(z) = \frac{1}{iz}R\left(\frac{z+1/z}{2}, \frac{z-1/z}{2i}\right)$$

we have

$$\int_0^{2\pi} R(\cos(\theta), \sin(\theta)) d\theta = 2\pi i \sum \text{ residues of } f \text{ inside } |z| = 1.$$

*Proof.* We make the same substitutions as in Example 9.6. So,

$$\int_0^{2\pi} R(\cos(\theta), \sin(\theta)) d\theta = \int_{|z|=1} R\left(\frac{z+1/z}{2}, \frac{z-1/z}{2i}\right) \frac{dz}{iz}$$

The assumption about poles means that f has no poles on the contour |z| = 1. The residue theorem now implies the theorem.

#### 9.5 Integrands with branch cuts

Example 9.8. Compute

$$I = \int_0^\infty \frac{x^{1/3}}{1 + x^2} \, dx.$$

Solution: Let

$$f(x) = \frac{x^{1/3}}{1 + x^2}.$$

Since this is asymptotically comparable to  $x^{-5/3}$ , the integral is absolutely convergent. As a complex function

$$f(z) = \frac{z^{1/3}}{1 + z^2}$$

needs a branch cut to be analytic (or even continuous), so we will need to take that into account with our choice of contour.

First, choose the following branch cut along the positive real axis. That is, for  $z = re^{i\theta}$  not on the axis, we have  $0 < \theta < 2\pi$ .

Next, we use the contour  $C_1 + C_R - C_2 - C_r$  shown below.

Contour around branch cut: inner circle of radius r, outer of radius R.

We put convenient signs on the pieces so that the integrals are parametrized in a natural way. You should read this contour as having r so small that  $C_1$  and  $C_2$  are essentially on the x-axis. Note well, that, since  $C_1$  and  $C_2$  are on opposite sides of the branch cut, the integral

$$\int_{C_1-C_2} f(z) \, dz \neq 0.$$

First we analyze the integral over each piece of the curve.

On  $C_R$ : Theorem 9.1 says that

$$\lim_{R \to \infty} \int_{C_R} f(z) \, dz = 0.$$

On  $C_r$ : For concreteness, assume r < 1/2. We have |z| = r, so

$$|f(z)| = \frac{|z^{1/3}|}{|1+z^2|} \le \frac{r^{1/3}}{1-r^2} \le \frac{(1/2)^{1/3}}{3/4}.$$

Call the last number in the above equation M. We have shown that, for small r, |f(z)| < M. So,

$$\left| \int_{C_r} f(z) \, dz \right| \le \int_0^{2\pi} |f(r\mathrm{e}^{i\theta})| |ir\mathrm{e}^{i\theta}| \, d\theta \le \int_0^{2\pi} Mr \, d\theta = 2\pi Mr.$$

Clearly this goes to zero as  $r \to 0$ .

On  $C_1$ :

$$\lim_{r \to 0, \, R \to \infty} \int_{C_1} f(z) \, dz = \int_0^\infty f(x) \, dx = I.$$

On  $C_2$ : We have (essentially)  $\theta = 2\pi$ , so  $z^{1/3} = e^{i2\pi/3}|z|^{1/3}$ . Thus,

$$\lim_{r \to 0, R \to \infty} \int_{C_2} f(z) \, dz = e^{i2\pi/3} \int_0^\infty f(x) \, dx = e^{i2\pi/3} I.$$

The poles of f(z) are at  $\pm i$ . Since f is meromorphic inside our contour the residue theorem says

$$\int_{C_1 + C_R - C_2 - C_r} f(z) dz = 2\pi i (\text{Res}(f, i) + \text{Res}(f, -i)).$$

Letting  $r \to 0$  and  $R \to \infty$  the analysis above shows

$$(1 - e^{i2\pi/3})I = 2\pi i (\text{Res}(f, i) + \text{Res}(f, -i))$$

All that's left is to compute the residues using the chosen branch of  $z^{1/3}$ 

$$\operatorname{Res}(f, -i) = \frac{(-i)^{1/3}}{-2i} = \frac{(e^{i3\pi/2})^{1/3}}{2e^{i3\pi/2}} = \frac{e^{-i\pi}}{2} = -\frac{1}{2}$$
$$\operatorname{Res}(f, i) = \frac{i^{1/3}}{2i} = \frac{e^{i\pi/6}}{2e^{i\pi/2}} = \frac{e^{-i\pi/3}}{2}$$

A little more algebra gives

$$(1 - e^{i2\pi/3})I = 2\pi i \cdot \frac{-1 + e^{-i\pi/3}}{2} = \pi i(-1 + 1/2 - i\sqrt{3}/2) = -\pi i e^{i\pi/3}.$$

Continuing

$$I = \frac{-\pi i e^{i\pi/3}}{1 - e^{i2\pi/3}} = \frac{\pi i}{e^{i\pi/3} - e^{-\pi i/3}} = \frac{\pi/2}{(e^{i\pi/3} - e^{-i\pi/3})/2i} = \frac{\pi/2}{\sin(\pi/3)} = \frac{\pi}{\sqrt{3}}.$$

Whew! (Note: a sanity check is that the result is real, which it had to be.)

### Example 9.9. Compute

$$I = \int_{1}^{\infty} \frac{dx}{x\sqrt{x^2 - 1}}.$$

Solution: Let

$$f(z) = \frac{1}{z\sqrt{z^2 - 1}}$$
.

The first thing we'll show is that the integral

$$\int_{1}^{\infty} f(x) \, dx$$

is absolutely convergent. To do this we split it into two integrals

$$\int_{1}^{\infty} \frac{dx}{x\sqrt{x^{2}-1}} = \int_{1}^{2} \frac{dx}{x\sqrt{x^{2}-1}} + \int_{2}^{\infty} \frac{dx}{x\sqrt{x^{2}-1}}.$$

The first integral on the right can be rewritten as

$$\int_{1}^{2} \frac{1}{x\sqrt{x+1}} \cdot \frac{1}{\sqrt{x-1}} \, dx \le \int_{1}^{2} \frac{1}{\sqrt{2}} \cdot \frac{1}{\sqrt{x-1}} \, dx = \frac{2}{\sqrt{2}} \sqrt{x-1} \bigg|_{1}^{2}.$$

This shows the first integral is absolutely convergent.

The function f(x) is asymptotically comparable to  $1/x^2$ , so the integral from 2 to  $\infty$  is also absolutely convergent.

We can conclude that the original integral is absolutely convergent.

Next, we use the following contour. Here we assume the big circles have radius R and the small ones have radius r.

We use the branch cut for square root that removes the positive real axis. In this branch

$$0 < \arg(z) < 2\pi$$
 and  $0 < \arg(\sqrt{w}) < \pi$ .

For f(z), this necessitates the branch cut that removes the rays  $[1, \infty)$  and  $(-\infty, -1]$  from the complex plane.

The pole at z = 0 is the only singularity of f(z) inside the contour. It is easy to compute that

Res
$$(f, 0) = \frac{1}{\sqrt{-1}} = \frac{1}{i} = -i.$$

So, the residue theorem gives us

$$\int_{C_1 + C_2 - C_3 - C_4 + C_5 - C_6 - C_7 + C_8} f(z) \, dz = 2\pi i \operatorname{Res}(f, 0) = 2\pi. \tag{2}$$

In a moment we will show the following limits

$$\lim_{R \to \infty} \int_{C_1} f(z) \, dz = \lim_{R \to \infty} \int_{C_5} f(z) \, dz = 0$$

$$\lim_{r \to 0} \int_{C_3} f(z) \, dz = \lim_{r \to 0} \int_{C_7} f(z) \, dz = 0.$$

We will also show

$$\begin{split} \lim_{R \to \infty, \, r \to 0} \int_{C_2} f(z) \, dz &= \lim_{R \to \infty, \, r \to 0} \int_{-C_4} f(z) \, dz \\ &= \lim_{R \to \infty, \, r \to 0} \int_{-C_6} f(z) \, dz = \lim_{R \to \infty, \, r \to 0} \int_{C_8} f(z) \, dz = I. \end{split}$$

Using these limits, Equation 2 implies  $4I = 2\pi$ , i.e.

$$I=\pi/2.$$

All that's left is to prove the limits asserted above.

The limits for  $C_1$  and  $C_5$  follow from Theorem 9.1 because

$$|f(z)| \approx 1/|z|^{3/2}$$

for large z.

We get the limit for  $C_3$  as follows. Suppose r is small, say much less than 1. If

$$z = -1 + re^{i\theta}$$

is on  $C_3$  then,

$$|f(z)| = \frac{1}{|z\sqrt{z-1}\sqrt{z+1}|} = \frac{1}{|-1+r\mathrm{e}^{i\theta}|\sqrt{|-2+r\mathrm{e}^{i\theta}|}\sqrt{r}} \le \frac{M}{\sqrt{r}}.$$

where M is chosen to be bigger than

$$\frac{1}{|-1+re^{i\theta}|\sqrt{|-2+re^{i\theta}|}}$$

for all small r.

Thus,

$$\left| \int_{C_3} f(z) dz \right| \le \int_{C_3} \frac{M}{\sqrt{r}} |dz| \le \frac{M}{\sqrt{r}} \cdot 2\pi r = 2\pi M \sqrt{r}.$$

This last expression clearly goes to 0 as  $r \to 0$ .

The limit for the integral over  $C_7$  is similar.

We can parameterize the straight line  $C_8$  by

$$z = x + i\epsilon$$
.

where  $\epsilon$  is a small positive number and x goes from (approximately) 1 to  $\infty$ . Thus, on  $C_8$ , we have

$$arg(z^2 - 1) \approx 0$$
 and  $f(z) \approx f(x)$ .

All these approximations become exact as  $r \to 0$ . Thus,

$$\lim_{R \to \infty, \, r \to 0} \int_{C_8} f(z) \, dz = \int_1^\infty f(x) \, dx = I.$$

We can parameterize  $-C_6$  by

$$z = x - i\epsilon$$

where x goes from  $\infty$  to 1. Thus, on  $C_6$ , we have

$$arg(z^2-1)\approx 2\pi$$
,

so

$$\sqrt{z^2-1} \approx -\sqrt{x^2-1}$$
.

This implies

$$f(z) \approx -\frac{1}{x\sqrt{x^2 - 1}} = -f(x).$$

Thus,

$$\lim_{R \to \infty, r \to 0} \int_{-C_6} f(z) \, dz = \int_{\infty}^1 -f(x) \, dx = \int_1^{\infty} f(x) \, dx = I.$$

We can parameterize  $C_2$  by  $z = -x + i\epsilon$  where x goes from  $\infty$  to 1. Thus, on  $C_2$ , we have

$$arg(z^2 - 1) \approx 2\pi$$
,

so

$$\sqrt{z^2 - 1} \approx -\sqrt{x^2 - 1}.$$

This implies

$$f(z) \approx \frac{1}{(-x)(-\sqrt{x^2 - 1})} = f(x).$$

Thus,

$$\lim_{R\to\infty,\,r\to 0}\int_{C_2}f(z)\,dz=\int_{\infty}^1f(x)\,(-dx)=\int_1^\infty f(x)\,dx=I.$$

The last curve  $-C_4$  is handled similarly.

# 9.6 Cauchy principal value

First an example to motivate defining the principal value of an integral. We'll actually compute the integral in the next section.

#### Example 9.10. Let

$$I = \int_0^\infty \frac{\sin(x)}{x} \, dx.$$

This integral is not absolutely convergent, but it is conditionally convergent. Formally, of course, we mean

$$I = \lim_{R \to \infty} \int_0^R \frac{\sin(x)}{x} \, dx.$$

We can proceed as in Example 9.5. First note that  $\sin(x)/x$  is even, so

$$I = \frac{1}{2} \int_{-\infty}^{\infty} \frac{\sin(x)}{x} \, dx.$$

Next, to avoid the problem that  $\sin(z)$  goes to infinity in both the upper and lower half-planes we replace the integrand by  $\frac{e^{ix}}{x}$ .

We've changed the problem to computing

$$\tilde{I} = \int_{-\infty}^{\infty} \frac{\mathrm{e}^{ix}}{x} \, dx.$$

The problems with this integral are caused by the pole at 0. The biggest problem is that the integral doesn't converge! The other problem is that when we try to use our usual strategy of choosing a closed contour we can't use one that includes z = 0 on the real axis. This is our motivation for defining principal value. We will come back to this example below.

**Definition.** Suppose we have a function f(x) that is continuous on the real line except at the point  $x_1$ , then we define the Cauchy principal value as

$$\text{p.v.} \int_{-\infty}^{\infty} f(x) \, dx = \lim_{R \to \infty, \, r_1 \to 0} \int_{-R}^{x_1 - r_1} f(x) \, dx + \int_{x_1 + r_1}^{R} f(x) \, dx.$$

Provided the limit converges. You should notice that the intervals around  $x_1$  and around  $\infty$  are symmetric. Of course, if the integral

$$\int_{-\infty}^{\infty} f(x) \, dx$$

converges, then so does the principal value and they give the same value. We can make the definition more flexible by including the following cases.

1. If f(x) is continuous on the entire real line then we define the principal value as

p.v. 
$$\int_{-\infty}^{\infty} f(x) dx = \lim_{R \to \infty} \int_{-R}^{R} f(x) dx$$

2. If we have multiple points of discontinuity,  $x_1 < x_2 < x_3 < ... < x_n$ , then

p.v. 
$$\int_{-\infty}^{\infty} f(x) dx = \lim_{n \to \infty} \int_{-R}^{x_1 - r_1} f(x) dx + \int_{x_1 + r_1}^{x_2 - r_2} + \int_{x_2 + r_2}^{x_3 - r_3} + \dots \int_{x_n + r_n}^{R} f(x) dx.$$

Here the limit is taken as  $R \to \infty$  and each of the  $r_k \to 0$ .

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

Intervals of integration for principal value are symmetric around  $x_k$  and  $\infty$ 

The next example shows that sometimes the principal value converges when the integral itself does not. The opposite is never true. That is, we have the following theorem.

**Theorem 9.11.** If 
$$f(x)$$
 has discontinuities at  $x_1 < x_2 < ... < x_n$  and  $\int_{-\infty}^{\infty} f(x) dx$  converges then so does p.v.  $\int_{-\infty}^{\infty} f(x) dx$ .

*Proof.* The proof amounts to understanding the definition of convergence of integrals as limits. The integral converges means that each of the limits

$$\lim_{R_{1} \to \infty, a_{1} \to 0} \int_{-R_{1}}^{x_{1} - a_{1}} f(x) dx$$

$$\lim_{b_{1} \to 0, a_{2} \to 0} \int_{x_{1} + b_{1}}^{x_{2} - a_{2}} f(x) dx$$

$$\dots$$

$$\lim_{R_{2} \to \infty, b_{n} \to 0} \int_{x_{n} + b_{n}}^{R_{2}} f(x) dx.$$
(3)

converges. There is no symmetry requirement, i.e.  $R_1$  and  $R_2$  are completely independent, as are  $a_1$  and  $b_1$  etc.

The principal value converges means

$$\lim \int_{-R}^{x_1 - r_1} + \int_{x_1 + r_1}^{x_2 - r_2} + \int_{x_2 + r_2}^{x_3 - r_3} + \dots \int_{x_n + r_n}^{R} f(x) \, dx \tag{4}$$

converges. Here the limit is taken over all the parameter  $R \to \infty$ ,  $r_k \to 0$ . This limit has symmetry, e.g. we replaced both  $a_1$  and  $b_1$  in Equation 3 by  $r_1$  etc. Certainly if the limits in Equation 3 converge then so do the limits in Equation 4. QED

#### Example 9.12. Consider both

$$\int_{-\infty}^{\infty} \frac{1}{x} dx$$
 and p.v.  $\int_{-\infty}^{\infty} \frac{1}{x} dx$ .

The first integral diverges since

$$\int_{-R_1}^{-r_1} \frac{1}{x} dx + \int_{r_2}^{R_2} \frac{1}{x} dx = \ln(r_1) - \ln(R_1) + \ln(R_2) - \ln(r_2).$$

This clearly diverges as  $R_1$ ,  $R_2 \to \infty$  and  $r_1$ ,  $r_2 \to 0$ .

On the other hand the symmetric integral

$$\int_{-R}^{-r} \frac{1}{x} dx + \int_{r}^{R} \frac{1}{x} dx = \ln(r) - \ln(R) + \ln(R) - \ln(r) = 0.$$

This clearly converges to 0.

We will see that the principal value occurs naturally when we integrate on semicircles around points. We prepare for this in the next section.

# 9.7 Integrals over portions of circles

We will need the following theorem in order to combine principal value and the residue theorem.

**Theorem 9.13.** Suppose f(z) has a **simple** pole at  $z_0$ . Let  $C_r$  be the semicircle  $\gamma(\theta) = z_0 + re^{i\theta}$ , with  $0 \le \theta \le \pi$ . Then

$$\lim_{r \to 0} \int_{C_r} f(z) dz = \pi i \operatorname{Res}(f, z_0)$$
 (5)

Small semicircle of radius r around  $z_0$ 

*Proof.* Since we take the limit as r goes to 0, we can assume r is small enough that f(z) has a Laurent expansion of the punctured disk of radius r centered at  $z_0$ . That is, since the pole is simple,

$$f(z) = \frac{b_1}{z - z_0} + a_0 + a_1(z - z_0) + \dots$$
 for  $0 < |z - z_0| \le r$ .

Thus,

$$\int_{C_{-}} f(z) dz = \int_{0}^{\pi} f(z_{0} + re^{i\theta}) rie^{i\theta} d\theta = \int_{0}^{\pi} \left( b_{1}i + a_{0}ire^{i\theta} + a_{1}ir^{2}e^{i2\theta} + \dots \right) d\theta$$

The  $b_1$  term gives  $\pi i b_1$ . Clearly all the other terms go to 0 as  $r \to 0$ . QED.

If the pole is not simple the theorem doesn't hold and, in fact, the limit does not exist.

The same proof gives a slightly more general theorem.

**Theorem 9.14.** Suppose f(z) has a **simple** pole at  $z_0$ . Let  $C_r$  be the circular arc  $\gamma(\theta) = z_0 + re^{i\theta}$ , with  $\theta_0 \le \theta \le \theta_0 + \alpha$ . Then

$$\lim_{r \to 0} \int_{C_{-}} f(z) dz = \alpha i \operatorname{Res}(f, z_{0})$$

Small circular arc of radius r around  $z_0$ 

**Example 9.15.** (Return to Example 9.10.) A long time ago we left off Example 9.10 to define principal value. Let's now use the principal value to compute

$$\tilde{I} = \text{p.v.} \int_{-\infty}^{\infty} \frac{e^{ix}}{x} dx.$$

Solution: We use the indented contour shown below. The indentation is the little semicircle the goes around z = 0. There are no poles inside the contour so the residue theorem implies

$$\int_{C_1 - C_r + C_2 + C_R} \frac{e^{iz}}{z} \, dz = 0.$$

Next we break the contour into pieces.

$$\lim_{R\to\infty,\,r\to 0}\int_{C_1+C_2}\frac{\mathrm{e}^{iz}}{z}\,dz=\tilde{I}.$$

Theorem 9.2(a) implies

$$\lim_{R \to \infty} \int_{C_R} \frac{e^{iz}}{z} dz = 0.$$

Equation 5 in Theorem 9.13 tells us that

$$\lim_{r \to 0} \int_{C_{z}} \frac{e^{iz}}{z} dz = \pi i \operatorname{Res}\left(\frac{e^{iz}}{z}, 0\right) = \pi i$$

Combining all this together we have

$$\lim_{R \to \infty, r \to 0} \int_{C_1 - C_r + C_2 + C_p} \frac{e^{iz}}{z} dz = \tilde{I} - \pi i = 0,$$

so  $\tilde{I} = \pi i$ . Thus, looking back at Example 5, where  $I = \int_0^\infty \frac{\sin(x)}{x} dx$ , we have

$$I = \frac{1}{2}\operatorname{Im}(\tilde{I}) = \frac{\pi}{2}.$$

There is a subtlety about convergence we alluded to above. That is, I is a genuine (conditionally) convergent integral, but  $\tilde{I}$  only exists as a principal value. However since I is a convergent integral we know that computing the principle value as we just did is sufficient to give the value of the convergent integral.

#### 9.8 Fourier transform

**Definition.** The Fourier transform of a function f(x) is defined by

$$\hat{f}(\omega) = \int_{-\infty}^{\infty} f(x) e^{-ix\omega} dx$$

This is often read as 'f-hat'.

**Theorem.** (Fourier inversion formula.) We can recover the original function f(x) with the Fourier inversion formula

$$f(x) = \frac{1}{2\pi} \int_{-\infty}^{\infty} \hat{f}(\omega) e^{ix\omega} d\omega.$$

So, the Fourier transform converts a function of x to a function of  $\omega$  and the Fourier inversion converts it back. Of course, everything above is dependent on the convergence of the various integrals.

*Proof.* We will not give the proof here. (We may get to it later in the course.)

Example 9.16. Let

$$f(t) = \begin{cases} e^{-at} & \text{for } t > 0\\ 0 & \text{for } t < 0 \end{cases},$$

where a > 0. Compute  $\hat{f}(\omega)$  and verify the Fourier inversion formula in this case.

Solution: Computing  $\hat{f}$  is easy: For a > 0

$$\widehat{f}(\omega) = \int_{-\infty}^{\infty} f(t) e^{-i\omega t} dt = \int_{0}^{\infty} e^{-at} e^{-i\omega t} dt = \frac{1}{a + i\omega} \text{ (recall } a > 0\text{)}.$$

We should first note that the inversion integral converges. To avoid distraction we show this at the end of this example.

Now, let

$$g(z) = \frac{1}{a + iz}$$

Note that  $\hat{f}(\omega) = g(\omega)$  and  $|g(z)| < \frac{M}{|z|}$  for large |z|.

To verify the inversion formula we consider the cases t > 0 and t < 0 separately. For t > 0 we use the standard contour.

Theorem 9.2(a) implies that

$$\lim_{x_1 \to \infty, x_2 \to \infty} \int_{C_1 + C_2 + C_3} g(z) e^{izt} dz = 0$$
 (6)

Clearly

$$\lim_{x_1 \to \infty, x_2 \to \infty} \int_{C_t} g(z) e^{izt} dz = \int_{-\infty}^{\infty} \widehat{f}(\omega) d\omega$$
 (7)

The only pole of  $g(z)e^{izt}$  is at z = ia, which is in the upper half-plane. So, applying the residue theorem to the entire closed contour, we get for large  $x_1, x_2$ :

$$\int_{C_1 + C_2 + C_3 + C_4} g(z) e^{izt} dz = 2\pi i \operatorname{Res} \left( \frac{e^{izt}}{a + iz}, ia \right) = \frac{e^{-at}}{i}.$$
 (8)

Combining the three equations 6, 7 and 8, we have

$$\int_{-\infty}^{\infty} \widehat{f}(\omega) d\omega = 2\pi e^{-at} \quad \text{for } t > 0$$

This shows the inversion formula holds for t > 0.

For t < 0 we use the contour

Theorem 9.2(b) implies that

$$\lim_{x_1 \to \infty, x_2 \to \infty} \int_{C_1 + C_2 + C_3} g(z) e^{izt} dz = 0$$

Clearly

$$\lim_{x_1 \to \infty, x_2 \to \infty} \frac{1}{2\pi} \int_{C_A} g(z) e^{izt} dz = \frac{1}{2\pi} \int_{-\infty}^{\infty} \widehat{f}(\omega) d\omega$$

Since, there are no poles of  $g(z)e^{izt}$  in the lower half-plane, applying the residue theorem to the entire closed contour, we get for large  $x_1, x_2$ :

$$\int_{C_1 + C_2 + C_3 + C_4} g(z) e^{izt} dz = -2\pi i \operatorname{Res} \left( \frac{e^{izt}}{a + iz}, ia \right) = 0.$$

Thus,

$$\frac{1}{2\pi} \int_{-\infty}^{\infty} \widehat{f}(\omega) \, d\omega = 0 \quad \text{for } t < 0$$

This shows the inversion formula holds for t < 0.

Finally, we give the promised argument that the inversion integral converges. By definition

$$\int_{-\infty}^{\infty} \widehat{f}(\omega) e^{i\omega t} d\omega = \int_{-\infty}^{\infty} \frac{e^{i\omega t}}{a + i\omega} d\omega$$
$$= \int_{-\infty}^{\infty} \frac{a\cos(\omega t) + \omega\sin(\omega t) - i\omega\cos(\omega t) + ia\sin(\omega t)}{a^2 + \omega^2} d\omega$$

The terms without a factor of  $\omega$  in the numerator converge absolutely because of the  $\omega^2$  in the denominator. The terms with a factor of  $\omega$  in the numerator do not converge absolutely. For example, since

$$\frac{\omega \sin(\omega t)}{a^2 + \omega^2}$$

decays like  $1/\omega$ , its integral is not absolutely convergent. However, we claim that the integral does converge conditionally. That is, both limits

$$\lim_{R_2 \to \infty} \int_0^{R_2} \frac{\omega \sin(\omega t)}{a^2 + \omega^2} d\omega \text{ and } \lim_{R_1 \to \infty} \int_{-R_1}^0 \frac{\omega \sin(\omega t)}{a^2 + \omega^2} d\omega$$

exist and are finite. The key is that, as  $\sin(\omega t)$  alternates between positive and negative arches, the function  $\frac{\omega}{a^2 + \omega^2}$  is decaying monotonically. So, in the integral, the area under each arch adds or subtracts less than the arch before. This means that as  $R_1$  (or  $R_2$ ) grows the total area under the curve oscillates with a decaying amplitude around some limiting value.

Total area oscillates with a decaying amplitude.

# 9.9 Solving DEs using the Fourier transform

Let

$$D = \frac{d}{dt}.$$

Our goal is to see how to use the Fourier transform to solve differential equations like

$$P(D)y = f(t)$$
.

Here P(D) is a polynomial operator, e.g.

$$D^2 + 8D + 7I$$
.

We first note the following formula:

$$\widehat{Df}(\omega) = i\omega \widehat{f}. \tag{9}$$

*Proof.* This is just integration by parts:

$$\widehat{Df}(\omega) = \int_{-\infty}^{\infty} f'(t) e^{-i\omega t} dt$$

$$= f(t) e^{-i\omega t} \Big|_{-\infty}^{\infty} - \int_{-\infty}^{\infty} f(t) (-i\omega e^{-i\omega t} dt)$$

$$= i\omega \int_{-\infty}^{\infty} f(t) e^{-i\omega t} dt$$

$$= i\omega \widehat{f}(\omega) \quad \text{OED}$$

In the third line we assumed that f decays so that  $f(\infty) = f(-\infty) = 0$ .

It is a simple extension of Equation 9 to see

$$(\widehat{P(D)f})(\omega) = P(i\omega)\widehat{f}.$$

We can now use this to solve some differential equations.

**Example 9.17.** Solve the equation

$$y''(t) + 8y'(t) + 7y(t) = f(t) = \begin{cases} e^{-at} & \text{if } t > 0\\ 0 & \text{if } t < 0 \end{cases}$$

Solution: In this case, we have

$$P(D) = D^2 + 8D + 7I,$$

SO

$$P(s) = s^2 + 8s + 7 = (s+7)(s+1).$$

The DE

$$P(D)v = f(t)$$

transforms to

$$P(iw)\hat{y} = \hat{f}.$$

Using the Fourier transform of f found in Example 9.16 we have

$$\hat{y}(\omega) = \frac{\hat{f}}{P(i\omega)} = \frac{1}{(a+i\omega)(7+i\omega)(1+i\omega)}.$$

Fourier inversion says that

$$y(t) = \frac{1}{2\pi} \int_{-\infty}^{\infty} \widehat{y}(\omega) e^{i\omega t} d\omega$$

As always, we want to extend  $\hat{y}$  to be function of a complex variable z. Let's call it g(z):

$$g(z) = \frac{1}{(a+iz)(7+iz)(1+iz)}.$$

Now we can proceed exactly as in Example 9.16. We know  $|g(z)| < M/|z|^3$  for some constant M. Thus, the conditions of Theorem 9.2 are easily met. So, just as in Example 9.16, we have:

For t > 0,  $e^{izt}$  is bounded in the upper half-plane, so we use the contour below on the left.

$$y(t) = \frac{1}{2\pi} \int_{-\infty}^{\infty} \widehat{y}(\omega) e^{i\omega t} d\omega = \frac{1}{2\pi} \lim_{x_1 \to \infty, x_2 \to \infty} \int_{C_4} g(z) e^{izt} dz$$

$$= \frac{1}{2\pi} \lim_{x_1 \to \infty, x_2 \to \infty} \int_{C_1 + C_2 + C_3 + C_4} g(z) e^{izt} dz$$

$$= i \sum_{z \in S} \text{residues of } e^{izt} g(z) \text{ in the upper half-plane}$$

The poles of  $e^{izt}g(z)$  are at

These are all in the upper half-plane. The residues are respectively,

$$\frac{e^{-at}}{i(7-a)(1-a)}$$
,  $\frac{e^{-7t}}{i(a-7)(-6)}$ ,  $\frac{e^{-t}}{i(a-1)(6)}$ 

Thus, for t > 0 we have

$$y(t) = \frac{e^{-at}}{(7-a)(1-a)} - \frac{e^{-7t}}{(a-7)(6)} + \frac{e^{-t}}{(a-1)(6)}.$$

$$C_3 \qquad i(x_1+x_2) \qquad C_1 \qquad C_3 \qquad i(x_1+x_2) \qquad C_1$$

$$C_4 \qquad x_1 \rightarrow \operatorname{Re}(z)$$

$$C_3 \qquad i(x_1+x_2) \qquad C_1 \qquad C_2$$

$$C_4 \qquad x_1 \rightarrow \operatorname{Re}(z)$$

$$C_3 \qquad Im(z) \qquad C_2$$

$$C_4 \qquad x_1 \rightarrow \operatorname{Re}(z)$$

$$C_3 \qquad C_4 \qquad x_1 \rightarrow \operatorname{Re}(z)$$

$$C_4 \qquad C_1 \qquad C_2 \qquad C_1 \qquad C_2 \qquad C_1$$

$$C_4 \qquad C_1 \qquad C_2 \qquad C_1 \qquad C_2 \qquad C_2 \qquad C_1 \qquad C_2 \qquad C_2$$

$$C_4 \qquad C_1 \qquad C_2 \qquad C_2 \qquad C_1 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_2 \qquad C_3 \qquad C_2 \qquad C_2 \qquad C_3 \qquad C_2 \qquad C_3 \qquad C_4 \qquad C_4 \qquad C_4 \qquad C_4 \qquad C_4 \qquad C_4 \qquad C_4 \qquad C_5 \qquad C_5 \qquad C_5 \qquad C_6 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7 \qquad C_7$$

More briefly, when t < 0 we use the contour above on the right. We get the exact same string of equalities except the sum is over the residues of  $e^{izt}g(z)$  in the lower half-plane. Since there are no poles in the lower half-plane, we find that

$$\widehat{\mathbf{v}}(t) = 0$$

when t < 0.

Conclusion (reorganizing the signs and order of the terms):

$$y(t) = \begin{cases} 0 & \text{for } t < 0\\ \frac{e^{-at}}{(7-a)(1-a)} + \frac{e^{-7t}}{(7-a)(6)} - \frac{e^{-t}}{(1-a)(6)} & \text{for } t > 0. \end{cases}$$

**Note.** Because  $|g(z)| < M/|z|^3$ , we could replace the rectangular contours by semicircles to compute the Fourier inversion integral.

#### Example 9.18. Consider

$$y'' + y = f(t) = \begin{cases} e^{-at} & \text{if } t > 0\\ 0 & \text{if } t < 0. \end{cases}$$

Find a solution for t > 0.

Solution: We work a little more quickly than in the previous example.

Taking the Fourier transform we get

$$\widehat{y}(\omega) = \frac{\widehat{f}(\omega)}{P(i\omega)} = \frac{\widehat{f}(\omega)}{1 - \omega^2} = \frac{1}{(a + i\omega)(1 - \omega^2)}.$$

(In the last expression, we used the known Fourier transform of f.)

As usual, we extend  $\hat{y}(\omega)$  to a function of z:

$$g(z) = \frac{1}{(a+iz)(1-z^2)}.$$

This has simple poles at

$$-1$$
, 1,  $ai$ .

Since some of the poles are on the real axis, we will need to use an indented contour along the real axis and use principal value to compute the integral.

The contour is shown below. We assume each of the small indents is a semicircle with radius r. The big rectangular path from (R, 0) to (-R, 0) is called  $C_R$ .

For t > 0 the function  $e^{izt}g(z) < M/|z|^3$  in the upper half-plane. Thus, we get the following limits:

$$\lim_{R \to \infty} \int_{C_R} e^{izt} g(z) dz = 0$$
 (Theorem 9.2(b))
$$\lim_{R \to \infty, r \to 0} \int_{C_2} e^{izt} g(z) dz = \pi i \operatorname{Res}(e^{izt} g(z), -1)$$
 (Theorem 9.14)
$$\lim_{R \to \infty, r \to 0} \int_{C_4} e^{izt} g(z) dz = \pi i \operatorname{Res}(e^{izt} g(z), 1)$$
 (Theorem 9.14)
$$\lim_{R \to \infty, r \to 0} \int_{C_1 + C_3 + C_5} e^{izt} g(z) dz = \text{p.v.} \int_{-\infty}^{\infty} \hat{y}(t) e^{i\omega t} dt$$

Putting this together with the residue theorem we have

$$\lim_{R \to \infty, r \to 0} \int_{C_1 - C_2 + C_3 - C_4 + C_5 + C_R} e^{izt} g(z) dz = \text{p.v.} \int_{-\infty}^{\infty} \hat{y}(t) e^{i\omega t} dt - \pi i \operatorname{Res}(e^{izt} g(z), -1) - \pi i \operatorname{Res}(e^{izt} g(z), 1)$$

$$= 2\pi i \operatorname{Res}(e^{izt}, ai).$$

All that's left is to compute the residues and do some arithmetic. We don't show the calculations, but give the results

Res(e<sup>izt</sup> g(z), -1) = 
$$\frac{e^{-it}}{2(a-i)}$$
  
Res(e<sup>izt</sup> g(z), 1) =  $-\frac{e^{it}}{2(a+i)}$   
Res(e<sup>izt</sup> g(z), ai) =  $-\frac{e^{-at}}{i(1+a^2)}$ 

We get, for t > 0,

$$y(t) = \frac{1}{2\pi} \text{p.v.} \int_{-\infty}^{\infty} \hat{y}(t) e^{i\omega t} dt$$

$$= \frac{i}{2} \operatorname{Res}(e^{izt} g(z), -1) + \frac{i}{2} \operatorname{Res}(e^{izt} g(z), 1) + i \operatorname{Res}(e^{izt} g(z), ai)$$

$$= \frac{e^{-at}}{1 + a^2} + \frac{a}{1 + a^2} \sin(t) - \frac{1}{1 + a^2} \cos(t).$$

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 10 Notes**

Jeremy Orloff

# 10 Conformal transformations

#### 10.1 Introduction

In this topic we will look at the geometric notion of conformal maps. It will turn out that analytic functions are automatically conformal. Once we have understood the general notion, we will look at a specific family of conformal maps called fractional linear transformations and, in particular at their geometric properties. As an application we will use fractional linear transformations to solve the Dirichlet problem for harmonic functions on the unit disk with specified values on the unit circle. At the end we will return to some questions of fluid flow.

## 10.2 Geometric definition of conformal mappings

We start with a somewhat hand-wavy definition:

**Informal definition.** Conformal maps are functions on **C** that preserve the angles between curves.

More precisely: Suppose f(z) is differentiable at  $z_0$  and  $\gamma(t)$  is a smooth curve through  $z_0$ . To be concrete, let's suppose  $\gamma(t_0) = z_0$ . The function maps the point  $z_0$  to  $w_0 = f(z_0)$  and the curve  $\gamma$  to

$$\tilde{\gamma}(t) = f(\gamma(t)).$$

Under this map, the tangent vector  $\gamma'(t_0)$  at  $z_0$  is mapped to the tangent vector

$$\tilde{\gamma}'(t_0) = (f \circ \gamma)'(t_0)$$

at  $w_0$ . With these notations we have the following definition.

**Definition.** The function f(z) is conformal at  $z_0$  if there is an angle  $\phi$  and a scale a > 0 such that for any smooth curve  $\gamma(t)$  through  $z_0$  the map f rotates the tangent vector at  $z_0$  by  $\phi$  and scales it by a. That is, for any  $\gamma$ , the tangent vector  $(f \circ \gamma)'(t_0)$  is found by rotating  $\gamma'(t_0)$  by  $\phi$  and scaling it by a.

If f(z) is defined on a region A, we say it is a conformal map on A if it is conformal at each point z in A.

**Note.** The scale factor a and rotation angle  $\phi$  depends on the point z, but not on any of the curves through z.

**Example 10.1.** The figure below shows a conformal map f(z) mapping two curves through  $z_0$  to two curves through  $w_0 = f(z_0)$ . The tangent vectors to each of the original curves are both rotated and scaled by the same amount.

A conformal map rotates and scales all tangent vectors at  $z_0$  by the same ammount.

**Remark 1.** Conformality is a local phenomenon. At a different point  $z_1$  the rotation angle and scale factor might be different.

**Remark 2.** Since rotations preserve the angles between vectors, a key property of conformal maps is that they preserve the angles between curves.

**Example 10.2.** Recall that way back in Topic 1 we saw that  $f(z) = z^2$  maps horizontal and vertical grid lines to mutually orthogonal parabolas. We will see that f(z) is conformal. So, the orthogonality of the parabolas is no accident. The conformal map preserves the right angles between the grid lines.

## 10.3 Tangent vectors as complex numbers

In 18.02, you used parametrized curves  $\gamma(t) = (x(t), y(t))$  in the xy-plane. Considered this way, the tangent vector is just the derivative:

$$\gamma'(t) = (x'(t), y'(t)).$$

Note, as a vector, (x', y') represents a *displacement*. If the vector starts at the origin, then the endpoint is at (x', y'). More typically we draw the vector starting at the point  $\gamma(t)$ .

In 18.04, we use parametrized curves  $\gamma(t) = x(t) + iy(t)$  in the complex plane. Considered this way, the tangent vector is just the derivative:

$$\gamma'(t) = \chi'(t) + i\gamma'(t).$$

It should be clear that these representations are equivalent. The vector (x', y') and the complex number x' + iy' both represent the same displacement. Also, the length of a vector and the angle between two vectors is the same in both representations.

Thinking of tangent vectors to curves as complex numbers allows us to recast conformality in terms of complex numbers.

**Theorem 10.3.** If f(z) is conformal at  $z_0$  then there is a complex number  $c = ae^{i\phi}$  such that the map f multiplies tangent vectors at  $z_0$  by c. Conversely, if the map f multiplies all tangent vectors at  $z_0$  by  $c = ae^{i\phi}$  then f is conformal at  $z_0$ .

*Proof.* By definition f is conformal at  $z_0$  means that there is an angle  $\phi$  and a scalar a > 0 such that the map f rotates tangent vectors at  $z_0$  by  $\phi$  and scales them by a. This is exactly the effect of multiplication by  $c = ae^{i\phi}$ .

## 10.4 Analytic functions are conformal

**Theorem 10.4.** (Operational definition of conformal) If f is analytic on the region A and  $f'(z_0) \neq 0$ , then f is conformal at  $z_0$ . Furthermore, the map f multiplies tangent vectors at  $z_0$  by  $f'(z_0)$ .

*Proof.* The proof is a quick computation. Suppose  $z = \gamma(t)$  is curve through  $z_0$  with  $\gamma(t_0) = z_0$ . The curve  $\gamma(t)$  is transformed by f to the curve  $w = f(\gamma(t))$ . By the chain rule we have

$$\frac{df(\gamma(t))}{dt}\bigg|_{t_0} = f'(\gamma(t_0))\gamma'(t_0) = f'(z_0)\gamma'(t_0).$$

The theorem now follows from Theorem 10.3.

**Example 10.5.** (Basic example) Suppose  $c = ae^{i\phi}$  and consider the map f(z) = cz. Geometrically, this map rotates every point by  $\phi$  and scales it by a. Therefore, it must have the same effect on all tangent vectors to curves. Indeed, f is analytic and f'(z) = c is constant.

**Example 10.6.** Let  $f(z) = z^2$ . So f'(z) = 2z. Thus the map f has a different affect on tangent vectors at different points  $z_1$  and  $z_2$ .

**Example 10.7.** (Linear approximation) Suppose f(z) is analytic at z = 0. The linear approximation (first two terms of the Taylor series) is

$$f(z) \approx f(0) + f'(0)z.$$

If  $\gamma(t)$  is a curve with  $\gamma(t_0) = 0$  then, near  $t_0$ ,

$$f(\gamma(t)) \approx f(0) + f'(0)\gamma(t)$$

That is, near 0, f looks like our basic example plus a shift by f(0).

**Example 10.8.** The map  $f(z) = \overline{z}$  has lots of nice geometric properties, but it is not conformal. It preserves the length of tangent vectors and the angle between tangent vectors. The reason it isn't conformal is that is does not rotate tangent vectors. Instead, it reflects them across the x-axis.

In other words, it reverses the orientation of a pair of vectors. Our definition of conformal maps requires that it preserves orientation.

## **10.5** Digression to harmonic functions

**Theorem 10.9.** If u and v are harmonic conjugates and g = u + iv has  $g'(z_0) \neq 0$ , then the level curves of u and v through  $z_0$  are orthogonal.

**Note.** We proved this in an earlier topic using the Cauchy-Riemann equations. Here will make an argument involving conformal maps.

*Proof.* First we'll examine how g maps the level curve u(x, y) = a. Since g = u + iv, the image of the level curve is w = a + iv, i.e it's (contained in) a vertical line in the w-plane. Likewise, the level curve v(x, y) = b is mapped to the horizontal line w = u + ib.

Thus, the images of the two level curves are orthogonal. Since *g* is conformal it preserves the angle between the level curves, so they must be orthogonal.

g = u + iv maps level curves of u and v to grid lines.

### 10.6 Riemann mapping theorem

The Riemann mapping theorem is a major theorem on conformal maps. The proof is fairly technical and we will skip it. In practice, we will write down explicit conformal maps between regions.

**Theorem 10.10.** (Riemann mapping theorem) If A is simply connected and not the whole plane, then there is a bijective conformal map from A to the unit disk.

**Corollary.** For any two such regions there is a bijective conformal map from one to the other. We say they are conformally equivalent.

#### 10.7 Fractional linear transformations

**Definition.** A fractional linear transformation is a function of the form

$$T(z) = \frac{az+b}{cz+d}$$
, where a, b, c, d are complex constants and  $ad-bc \neq 0$ 

These are also called Mobius transforms or bilinear transforms. We will abbreviate fractional linear transformation as FLT.

**Simple point.** If ad - bc = 0 then T(z) is a constant function.

*Proof.* The full proof requires that we deal with all the cases where some of the coefficients are 0. We'll give the proof assuming  $c \neq 0$  and leave the case c = 0 to you. Assuming  $c \neq 0$ , the condition ad - bc = 0 implies

$$\frac{a}{c}(c,d) = (a,b).$$

So,

$$T(z) = \frac{(a/c)(cz+d)}{cz+d} = \frac{a}{c}.$$

That is, T(z) is constant.

Extension to  $\infty$ . It will be convenient to consider linear transformations to be defined on the extended complex plane  $\mathbb{C} \cup \{\infty\}$  by defining

$$T(\infty) = \begin{cases} a/c & \text{if } c \neq 0\\ \infty & \text{if } c = 0 \end{cases}$$
$$T(-d/c) = \infty & \text{if } c \neq 0.$$

#### **10.7.1 Examples**

**Example 10.11.** (Scale and rotate) Let T(z) = az. If a = r is real this scales the plane. If  $a = e^{i\theta}$  it rotates the plane. If  $a = re^{i\theta}$  it does both at once.

Multiplication by  $a = re^{i\theta}$  scales by r and rotates by  $\theta$ 

Note that T is the fractional linear transformation with coefficients

$$\begin{bmatrix} a & b \\ c & d \end{bmatrix} = \begin{bmatrix} a & 0 \\ 0 & 1 \end{bmatrix}.$$

(We'll see below the benefit of presenting the coefficients in matrix form!)

**Example 10.12.** (Scale and rotate and translate) Let T(z) = az + b. Adding the b term introduces a translation to the previous example.

The map w = az + b scales, rotates and shifts the square.

Note that T is the fractional linear transformation with coefficients

$$\begin{bmatrix} a & b \\ c & d \end{bmatrix} = \begin{bmatrix} a & b \\ 0 & 1 \end{bmatrix}.$$

**Example 10.13.** (Inversion) Let T(z) = 1/z. This is called an inversion. It turns the unit circle inside out. Note that  $T(0) = \infty$  and  $T(\infty) = 0$ . In the figure below the circle that is outside the unit circle in the z plane is inside the unit circle in the w plane and vice-versa. Note that the arrows on the curves are reversed.

The map w = 1/z inverts the plane.

Note that T is the fractional linear transformation with coefficients

$$\begin{bmatrix} a & b \\ c & d \end{bmatrix} = \begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}.$$

### Example 10.14. Let

$$T(z) = \frac{z - i}{z + i}.$$

We claim that this maps the x-axis to the unit circle and the upper half-plane to the unit disk.

*Proof.* First take x real, then

$$|T(x)| = \frac{|x-i|}{|x+i|} = \frac{\sqrt{x^2+1}}{\sqrt{x^2+1}} = 1.$$

So, T maps the x-axis to the unit circle.

Next take z = x + iy with y > 0, i.e. z in the upper half-plane. Clearly

$$|y+1| > |y-1|$$
,

so

$$|z+i| = |x+i(y+1)| > |x+i(y-1)| = |z-i|,$$

implying that

$$|T(z)| = \frac{|z-i|}{|z+i|} < 1.$$

So, T maps the upper half-plane to the unit disk.

We will use this map frequently, so for the record we note that

$$T(i) = 0$$
,  $T(\infty) = 1$ ,  $T(-1) = i$ ,  $T(0) = -1$ ,  $T(1) = -i$ .

These computations show that the real axis is mapped counterclockwise around the unit circle starting at 1 and coming back to 1.

The map  $w = \frac{z-i}{z+i}$  maps the upper-half plane to the unit disk.

#### 10.7.2 Lines and circles

**Theorem.** A linear fractional transformation maps lines and circles to lines and circles.

Before proving this, note that it does not say lines are mapped to lines and circles to circles. For example, in Example 10.14 the real axis is mapped the unit circle. You can also check that inversion w = 1/z maps the line z = 1 + iy to the circle |z - 1/2| = 1/2.

*Proof.* We start by showing that inversion maps lines and circles to lines and circles. Given z and w = 1/z we define x, y, u and v by

$$z = x + iy$$
 and  $w = \frac{1}{z} = \frac{x - iy}{x^2 + y^2} = u + iv$ 

So,

$$u = \frac{x}{x^2 + y^2} \quad \text{and} \quad v = -\frac{y}{x^2 + y^2}.$$

Now, every circle or line can be described by the equation

$$Ax + By + C(x^2 + y^2) = D$$

(If C = 0 it describes a line, otherwise a circle.) We convert this to an equation in u, v as follows.

$$Ax + By + C(x^{2} + y^{2}) = D$$

$$\Leftrightarrow \frac{Ax}{x^{2} + y^{2}} + \frac{By}{x^{2} + y^{2}} + C = \frac{D}{x^{2} + y^{2}}$$

$$\Leftrightarrow Au - Bv + C = D(u^{2} + v^{2}).$$

In the last step we used the fact that

$$u^{2} + v^{2} = |w|^{2} = 1/|z|^{2} = 1/(x^{2} + y^{2}).$$

We have shown that a line or circle in x, y is transformed to a line or circle in u, v. This shows that inversion maps lines and circles to lines and circles.

We note that for the inversion w = 1/z.

- 1. Any line not through the origin is mapped to a circle through the origin.
- 2. Any line through the origin is mapped to a line through the origin.
- 3. Any circle not through the origin is mapped to a circle not through the origin.
- 4. Any circle through the origin is mapped to a line not through the origin.

Now, to prove that an arbitrary fractional linear transformation maps lines and circles to lines and circles, we factor it into a sequence of simpler transformations.

First suppose that c = 0. So,

$$T(z) = (az + b)/d.$$

Since this is just translation, scaling and rotating, it is clear it maps circles to circles and lines to lines.

Now suppose that  $c \neq 0$ . Then,

$$T(z) = \frac{az+b}{cz+d} = \frac{\frac{a}{c}(cz+d)+b-\frac{ad}{c}}{cz+d} = \frac{a}{c} + \frac{b-ad/c}{cz+d}$$

So, w = T(z) can be computed as a composition of transforms

$$z \mapsto w_1 = cz + d \mapsto w_2 = 1/w_1 \mapsto w = \frac{a}{c} + (b - ad/c)w_2$$

We know that each of the transforms in this sequence maps lines and circles to lines and circles. Therefore the entire sequence does also.

# 10.7.3 Mapping $z_i$ to $w_i$

It turns out that for two sets of three points  $z_1, z_2, z_3$  and  $w_1, w_2, w_3$  there is a fractional linear transformation that takes  $z_i$  to  $w_i$ . We can construct this map as follows.

Let

$$T_1(z) = \frac{(z - z_1)(z_2 - z_3)}{(z - z_3)(z_2 - z_1)}.$$

Notice that

$$T_1(z_1) = 0,$$
  $T_1(z_2) = 1,$   $T_1(z_3) = \infty.$ 

Likewise let

$$T_2(w) = \frac{(w - w_1)(w_2 - w_3)}{(w - w_3)(w_2 - w_1)}.$$

Notice that

$$T_2(w_1) = 0,$$
  $T_2(w_2) = 1,$   $T_2(w_3) = \infty.$ 

Now  $T(z) = T_2^{-1} \circ T_1(z)$  is the required map.

### 10.7.4 Correspondence with matrices

We can identify the transformation

$$T(z) = \frac{az+b}{cz+d}$$

with the matrix

$$\begin{bmatrix} a & b \\ c & d \end{bmatrix}.$$

This identification is useful because of the following algebraic facts.

**1.** If  $r \neq 0$  then  $\begin{bmatrix} a & b \\ c & d \end{bmatrix}$  and  $r \begin{bmatrix} a & b \\ c & d \end{bmatrix}$  correspond to the same FLT.

*Proof.* This follows from the obvious equality

$$\frac{az+b}{cz+d} = \frac{raz+rb}{rcz+rd}.$$

**2.** If T(z) corresponds to  $A = \begin{bmatrix} a & b \\ c & d \end{bmatrix}$  and S(z) corresponds to  $B = \begin{bmatrix} e & f \\ g & h \end{bmatrix}$  then composition  $T \circ S(z)$  corresponds to matrix multiplication AB.

*Proof.* The proof is just a bit of algebra.

$$T \circ S(z) = T\left(\frac{ez+f}{gz+h}\right) = \frac{a\left((ez+f)/(gz+h)\right) + b}{c\left((ez+f)/(gz+h)\right) + d} = \frac{(ae+bg)z + af+bh}{(ce+dg)z + cf+dh}$$

$$AB = \begin{bmatrix} a & b \\ c & d \end{bmatrix} \begin{bmatrix} e & f \\ g & h \end{bmatrix} = \begin{bmatrix} ae+bg & af+bh \\ ce+dg & cf+dh \end{bmatrix}$$

The claimed correspondence is clear from the last entries in the two lines above.

**3.** If T(z) corresponds to  $A = \begin{bmatrix} a & b \\ c & d \end{bmatrix}$  then T has an inverse and  $T^{-1}(w)$  corresponds to  $A^{-1}$  and also to  $\begin{bmatrix} d & -b \\ -c & a \end{bmatrix}$ , i.e. to  $A^{-1}$  without the factor of  $1/\det(A)$ .

*Proof.* Since  $AA^{-1} = I$  it is clear from the previous fact that  $T^{-1}$  corresponds to  $A^{-1}$ . Since

$$A^{-1} = \frac{1}{ad - bc} \begin{bmatrix} d & -b \\ -c & a \end{bmatrix}$$

Fact 1 implies  $A^{-1}$  and  $\begin{bmatrix} d & -b \\ -c & a \end{bmatrix}$  both correspond to the same FLT, i.e. to  $T^{-1}$ .

#### **Example 10.15.**

- 1. The matrix  $\begin{bmatrix} a & b \\ 0 & 1 \end{bmatrix}$  corresponds to T(z) = az + b.
- 2. The matrix  $\begin{bmatrix} e^{i\alpha} & 0 \\ 0 & e^{-i\alpha} \end{bmatrix}$  corresponds to rotation by  $2\alpha$ .
- 3. The matrix  $\begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}$  corresponds to the inversion w = 1/z.

## 10.8 Reflection and symmetry

### 10.8.1 Reflection and symmetry in a line

**Example 10.16.** Suppose we have a line S and a point  $z_1$  not on S. The reflection of  $z_1$  in S is the point  $z_2$  so that S is the perpendicular bisector to the line segment  $\overline{z_1}\overline{z_2}$ . Since there is exactly one such point  $z_2$ , the reflection of a point in a line is unique.

**Definition.** If  $z_2$  is the reflection of  $z_1$  in S, we say that  $z_1$  and  $z_2$  are symmetric with respect to the line S.

In the figure below the points  $z_1$  and  $z_2$  are symmetric in the x-axis. The points  $z_3$  and  $z_4$  are symmetric in the line S.

In order to define the reflection of a point in a circle we need to work a little harder. Looking back at the previous example we can show the following.

**Fact.** If  $z_1$  and  $z_2$  are symmetric in the line S, then any circle through  $z_1$  and  $z_2$  intersects S orthogonally.

*Proof.* Call the circle C. Since S is the perpendicular bisector of a chord of C, the center of C lies on S. Therefore S is a radial line, i.e. it intersects C orthogonally.

Circles through symmetric points intersect the line at right angles.

### 10.8.2 Reflection and symmetry in a circle

We will adapt this for our definition of reflection in a circle. So that the logic flows correctly we need to start with the definition of symmetric pairs of points.

**Definition.** Suppose S is a line or circle. A pair of points  $z_1$ ,  $z_2$  is called symmetric with respect to S if every line or circle through the two points intersects S orthogonally.

First we state an almost trivial fact.

**Fact.** Fractional linear transformations preserve symmetry. That is, if  $z_1$  and  $z_2$  are symmetric in a line or circle S, then, for an FLT T,  $T(z_1)$  and  $T(z_2)$  are symmetric in T(S).

*Proof.* The definition of symmetry is in terms of lines and circles, and angles. Fractional linear transformations map lines and circles to lines and circles and, being conformal, preserve angles.

**Theorem.** Suppose S is a line or circle and  $z_1$  a point not on S. There is a unique point  $z_2$  such that the pair  $z_1$ ,  $z_2$  is symmetric in S.

*Proof.* Let T be a fractional linear transformation that maps S to a line. We know that  $w_1 = T(z_1)$  has a unique reflection  $w_2$  in this line. Since  $T^{-1}$  preserves symmetry,  $z_1$  and  $z_2 = T^{-1}(w_2)$  are symmetric in S. Since  $w_2$  is the unique point symmetric to  $w_1$  the same is true for  $z_2$  vis-a-vis  $z_1$ . This is all shown in the figure below.

We can now define reflection in a circle.

**Definition.** The point  $z_2$  in the theorem is called the reflection of  $z_1$  in S.

### 10.8.3 Reflection in the unit circle

Using the symmetry preserving feature of fractional linear transformations, we start with a line and transform to the circle. Let *R* be the real axis and *C* the unit circle. We know the FLT

$$T(z) = \frac{z - i}{z + i}$$

maps R to C. We also know that the points z and  $\overline{z}$  are symmetric in R. Therefore

$$w_1 = T(z) = \frac{z-i}{z+i}$$
 and  $w_2 = T(\overline{z}) = \frac{\overline{z}-i}{\overline{z}+i}$ 

are symmetric in D. Looking at the formulas, it is clear that  $w_2 = 1/\overline{w_1}$ . This is important enough that we highlight it as a theorem.

**Theorem.** (Reflection in the unit circle) The reflection of  $z = x + iy = re^{i\theta}$  in the unit circle is

$$\frac{1}{z} = \frac{z}{|z|^2} = \frac{x + iy}{x^2 + y^2} = \frac{e^{i\theta}}{r}.$$

The calculations from  $1/\overline{z}$  are all trivial.

### Notes.

- 1. It is possible, but more tedious and less insightful, to arrive at this theorem by direct calculation.
- 2. If z is on the unit circle then  $1/\overline{z} = z$ . That is, z is its own reflection in the unit circle –as it should be.
- 3. The center of the circle 0 is symmetric to the point at  $\infty$ .

The figure below shows three pairs of points symmetric in the unit circle:

$$z_1 = 2; \ w_1 = \frac{1}{2}, \quad z_2 = 1 + i; \ w_2 = \frac{1 + i}{2}, \quad z_3 = -2 + i; \ w_3 = \frac{-2 + i}{5}.$$

Pairs of points  $z_i$ ;  $w_i$  symmetric in the unit circle.

**Example 10.17.** Reflection in the circle of radius R. Suppose S is the circle |z| = R and  $z_1$  is a point not on S. Find the reflection of  $z_1$  in S.

Solution: Our strategy is to map S to the unit circle, find the reflection and then map the unit circle back to S.

Start with the map T(z) = w = z/R. Clearly T maps S to the unit circle and

$$w_1 = T(z_1) = z_1/R$$
.

The reflection of  $w_1$  is

$$w_2 = 1/\overline{w_1} = R/\overline{z}_1.$$

Mapping back from the unit circle by  $T^{-1}$  we have

$$z_2 = T^{-1}(w_2) = Rw_2 = R^2/\overline{z}_1.$$

Therefore the reflection of  $z_1$  is  $R^2/\overline{z}_1$ .

Here are three pairs of points symmetric in the circle of radius 2. Note, that this is the same figure as the one above with everything doubled.

$$z_1 = 4$$
;  $w_1 = 1$ ,  $z_2 = 2 + 2i$ ;  $w_2 = 1 + i$ ,  $z_3 = -4 + 2i$ ;  $w_3 = \frac{-4 + 2i}{5}$ .

Pairs of points  $z_i$ ;  $w_i$  symmetric in the circle of radius 2.

**Example 10.18.** Find the reflection of  $z_1$  in the circle of radius R centered at c.

Solution: Let T(z) = (z - c)/R. T maps the circle centered at c to the unit circle. The inverse map is

$$T^{-1}(w) = Rw + c.$$

So, the reflection of  $z_1$  is given by mapping z to T(z), reflecting this in the unit circle, and mapping back to the original geometry with  $T^{-1}$ . That is, the reflection  $z_2$  is

$$z_1 \to \frac{z_1 - c}{R} \to \frac{R}{\overline{z_1 - c}} \to \boxed{z_2 = \frac{R^2}{\overline{z_1 - c}} + c.}$$

We can now record the following important fact.

**Fact.** (Reflection of the center) For a circle S with center c the pair c,  $\infty$  is symmetric with respect to the circle.

*Proof.* This is an immediate consequence of the formula for the reflection of a point in a circle. For example, the reflection of z in the unit circle is  $1/\overline{z}$ . So, the reflection of 0 is infinity.

**Example 10.19.** Show that if a circle and a line don't intersect then there is a pair of points  $z_1$ ,  $z_2$  that is symmetric with respect to both the line and circle.

Solution: By shifting, scaling and rotating we can find a fractional linear transformation T that maps the circle and line to the following configuration: The circle is mapped to the unit circle and the line to the vertical line x = a > 1.

For any real r,  $w_1 = r$  and  $w_2 = 1/r$  are symmetric in the unit circle. We can choose a specific r so that r and 1/r are equidistant from a, i.e. also symmetric in the line x = a. It is clear geometrically that this can be done. Algebraically we solve the equation

$$\frac{r+1/r}{2} = a \quad \Rightarrow \quad r^2 - 2ar + 1 = 0 \quad \Rightarrow \quad r = a + \sqrt{a^2 - 1} \quad \Rightarrow \quad \frac{1}{r} = a - \sqrt{a^2 - 1}.$$

Thus  $z_1 = T^{-1}(a + \sqrt{a^2 - 1})$  and  $z_2 = T^{-1}(a - \sqrt{a^2 - 1})$  are the required points.

**Example 10.20.** Show that if two circles don't intersect then there is a pair of points  $z_1$ ,  $z_2$  that is symmetric with respect to both circles.

*Solution:* Using a fractional linear transformation that maps one of the circles to a line (and the other to a circle) we can reduce the problem to that in the previous example.

**Example 10.21.** Show that any two circles that don't intersect can be mapped conformally to concentric circles.

Solution: Call the circles  $S_1$  and  $S_2$ . Using the previous example start with a pair of points  $z_1$ ,  $z_2$  which are symmetric in both circles. Next, pick a fractional linear transformation T that maps  $z_1$  to 0 and  $z_2$  to infinity. For example,

$$T(z) = \frac{z - z_1}{z - z_2}.$$

Since T preserves symmetry 0 and  $\infty$  are symmetric in the circle  $T(S_1)$ . This implies that 0 is the center of  $T(S_1)$ . Likewise 0 is the center of  $T(S_2)$ . Thus,  $T(S_1)$  and  $T(S_2)$  are concentric.

### 10.9 Solving the Dirichlet problem for harmonic functions

In general, a Dirichlet problem in a region A asks you to solve a partial differential equation in A where the values of the solution on the boundary of A are specificed.

**Example 10.22.** Find a function *u* harmonic on the unit disk such that

$$u(e^{i\theta}) = \begin{cases} 1 & \text{for } 0 < \theta < \pi \\ 0 & \text{for } -\pi < \theta < 0 \end{cases}$$

This is a Dirichlet problem because the values of u on the boundary are specified. The partial differential equation is implied by requiring that u be harmonic, i.e. we require  $\nabla^2 u = 0$ . We will solve this problem in due course.

#### 10.9.1 Harmonic functions on the upper half-plane

Our strategy will be to solve the Dirichlet problem for harmonic functions on the upper half-plane and then transfer these solutions to other domains.

**Example 10.23.** Find a harmonic function u(x, y) on the upper half-plane that satisfies the boundary condition

$$u(x,0) = \begin{cases} 1 & \text{for } x < 0 \\ 0 & \text{for } x > 0 \end{cases}$$

Solution: We can write down a solution explicitly as

$$u(x, y) = \frac{1}{\pi}\theta,$$

where  $\theta$  is the argument of z = x + iy. Since we are only working on the upper half-plane we can take any convenient branch with branch cut in the lower half-plane, say  $-\pi/2 < \theta < 3\pi/2$ .

To show u is truly a solution, we have to verify two things:

- 1. *u* satisfies the boundary conditions
- 2. u is harmonic

Both of these are straightforward. First, look at the point  $r_2$  on the positive x-axis. This has argument  $\theta = 0$ , so  $u(r_2, 0) = 0$ . Likewise  $\arg(r_1) = \pi$ , so  $u(r_1, 0) = 1$ . Thus, we have shown point (1).

To see point (2) remember that

$$\log(z) = \log(r) + i\theta.$$

So,

$$u = \operatorname{Re}\left(\frac{1}{\pi i}\log(z)\right).$$

Since it is the real part of an analytic function, *u* is harmonic.

**Example 10.24.** Suppose  $x_1 < x_2 < x_3$ . Find a harmonic function u on the upper half-plane that satisfies the boundary condition

$$u(x,0) = \begin{cases} c_0 & \text{for } x < x_1 \\ c_1 & \text{for } x_1 < x < x_2 \\ c_2 & \text{for } x_2 < x < x_3 \\ c_3 & \text{for } x_3 < x \end{cases}$$

Solution: We mimic the previous example and write down the solution

$$u(x, y) = c_3 + (c_2 - c_3)\frac{\theta_3}{\pi} + (c_1 - c_2)\frac{\theta_2}{\pi} + (c_0 - c_1)\frac{\theta_1}{\pi}.$$

Here, the  $\theta_j$  are the angles shown in the figure. One again, we chose a branch of  $\theta$  that has  $0 < \theta < \pi$  for points in the upper half-plane. (For example the branch  $-\pi/2 < \theta < 3\pi/2$ .)

To convince yourself that u satisfies the boundary condition test a few points:

- At  $r_3$ : all the  $\theta_i = 0$ . So,  $u(r_3, 0) = c_3$  as required.
- At  $r_2$ :  $\theta_1 = \theta_2 = 0$ ,  $\theta_3 = \pi$ . So,  $u(r_2, 0) = c_3 + c_2 c_3 = c_2$  as required.
- Likewise, at  $r_1$  and  $r_0$ , u have the correct values.

As before, u is harmonic because it is the real part of the analytic function

$$\Phi(z) = c_3 + \frac{(c_2 - c_3)}{\pi i} \log(z - x_3) + \frac{(c_1 - c_2)}{\pi i} \log(z - x_2) + \frac{(c_1 - c_0)}{\pi i} \log(z - x_1).$$

#### 10.9.2 Harmonic functions on the unit disk

Let's try to solve a problem similar to the one in Example 10.22.

**Example 10.25.** Find a function *u* harmonic on the unit disk such that

$$u(e^{i\theta}) = \begin{cases} 1 & \text{for } -\pi/2 < \theta < \pi/2 \\ 0 & \text{for } \pi/2 < \theta < 3\pi/2 \end{cases}$$

Solution: Our strategy is to start with a conformal map T from the upper half-plane to the unit disk. We can use this map to pull the problem back to the upper half-plane. We solve it there and then push the solution back to the disk.

Let's call the disk D, the upper half-plane H. Let z be the variable on D and w the variable on H. Back in Example 10.14 we found a map from H to D. The map and its inverse are

$$z = T(w) = \frac{w - i}{w + i},$$
  $w = T^{-1}(z) = \frac{iz + i}{-z + 1}.$ 

The function u on D is transformed by T to a function  $\phi$  on H. The relationships are

$$u(z) = \phi \circ T^{-1}(z)$$
 or  $\phi(w) = u \circ T(w)$ 

These relationships determine the boundary values of  $\phi$  from those we were given for u. We compute:

$$T^{-1}(i) = -1,$$
  $T^{-1}(-i) = 1,$   $T^{-1}(1) = \infty,$   $T^{-1}(-1) = 0.$ 

This shows the left hand semicircle bounding D is mapped to the segment [-1, 1] on the real axis. Likewise, the right hand semicircle maps to the two half-lines shown. (Literally, to the 'segment' 1 to  $\infty$  to -1.)

We know how to solve the problem for a harmonic function  $\phi$  on H:

$$\phi(w) = 1 - \frac{1}{\pi}\theta_2 + \frac{1}{\pi}\theta_1 = \text{Re}\left(1 - \frac{1}{\pi i}\log(w - 1) + \frac{1}{\pi i}\log(w + 1)\right).$$

Transforming this back to the disk we have

$$u(z) = \phi \circ T^{-1}(z) = \text{Re}\left(1 - \frac{1}{\pi i}\log(T^{-1}(z) - 1) + \frac{1}{\pi i}\log(T^{-1}(z) + 1)\right).$$

If we wanted to, we could simplify this somewhat using the formula for  $T^{-1}$ .

## 10.10 Flows around cylinders

#### 10.10.1 Milne-Thomson circle theorem

The Milne-Thomson theorem allows us to insert a circle into a two-dimensional flow and see how the flow adjusts. First we'll state and prove the theorem.

**Theorem.** (Milne-Thomson circle theorem) If f(z) is a complex potential with all its singularities outside |z| = R then

$$\Phi(z) = f(z) + \overline{f\left(\frac{R^2}{\overline{z}}\right)}$$

is a complex potential with streamline on |z| = R and the same singularities as f in the region |z| > R.

*Proof.* First note that  $R^2/\overline{z}$  is the reflection of z in the circle |z| = R.

Next we need to see that  $\overline{f(R^2/\overline{z})}$  is analytic for |z| > R. By assumption f(z) is analytic for  $|z| \le R$ , so it can be expressed as a Taylor series

$$f(z) = a_0 + a_1 z + a_2 z^2 + \dots \tag{1}$$

Therefore.

$$\overline{f\left(\frac{R^2}{\overline{z}}\right)} = \overline{a_0} + \overline{a_1}\frac{R^2}{z} + \overline{a_2}\left(\frac{R^2}{z}\right)^2 + \dots$$
(2)

All the singularities of f are outside |z| = R, so the Taylor series in Equation 1 converges for  $|z| \le R$ . This means the Laurent series in Equation 2 converges for  $|z| \ge R$ . That is,  $\overline{f(R^2/\overline{z})}$  is analytic for  $|z| \ge R$ , i.e. it introduces no singularies to  $\Phi(z)$  outside |z| = R.

The last thing to show is that |z| = R is a streamline for  $\Phi(z)$ . This follows because for  $z = Re^{i\theta}$ 

$$\Phi(Re^{i\theta}) = f(Re^{i\theta}) + \overline{f(Re^{i\theta})}$$

is real. Therefore

$$\psi(Re^{i\theta}) = Im(\Phi(Re^{i\theta}) = 0.$$

#### **10.10.2** Examples

Think of f(z) as representing flow, possibly with sources or vortices outside |z| = R. Then  $\Phi(z)$  represents the new flow when a circular obstacle is placed in the flow. Here are a few examples.

**Example 10.26.** (Uniform flow around a circle) We know from Topic 6 that f(z) = z is the complex potential for uniform flow to the right. So,

$$\Phi(z) = z + R^2/z$$

is the potential for uniform flow around a circle of radius R centered at the origin.

Uniform flow around a circle

Just because they look nice, the figure includes streamlines inside the circle. These don't interact with the flow outside the circle.

Note, that as z gets large flow looks uniform. We can see this analytically because

$$\Phi'(z) = 1 - R^2/z^2$$

goes to 1 as z gets large. (Recall that the velocity field is  $(\phi_x, \phi_y)$ , where  $\Phi = \phi + i\psi \dots$ )

**Example 10.27.** (Source flow around a circle) Here the source is at z = -2 (outside the unit circle) with complex potential

$$f(z) = \log(z + 2).$$

With the appropriate branch cut the singularities of f are also outside |z|=1. So we can apply Milne-Thomson and obtain

$$\Phi(z) = \log(z+2) + \overline{\log\left(\frac{1}{z} + 2\right)}$$

Source flow around a circle

We know that far from the origin the flow should look the same as a flow with just a source at z = -2. Let's see this analytically. First we state a useful fact:

**Useful fact.** If g(z) is analytic then so is  $h(z) = \overline{g(\overline{z})}$  and  $h'(z) = \overline{g'(\overline{z})}$ .

*Proof.* Use the Taylor series for g to get the Taylor series for h and then compare h'(z) and  $g'(\overline{z})$ .  $\square$  Using this we have

$$\Phi'(z) = \frac{1}{z+2} - \frac{1}{z(1+2z)}$$

For large z the second term decays much faster than the first, so

$$\Phi'(z) \approx \frac{1}{z+2}.$$

That is, far from z = 0, the velocity field looks just like the velocity field for f(z), i.e. the velocity field of a source at z = -2.

Example 10.28. (Transforming flows) If we use

$$g(z) = z^2$$

we can transform a flow from the upper half-plane to the first quadrant

# 10.11 Examples of conformal maps and excercises

As we've seen, once we have flows or harmonic functions on one region, we can use conformal maps to map them to other regions. In this section we will offer a number of conformal maps between various regions. By chaining these together along with scaling, rotating and shifting we can build a large library of conformal maps. Of course there are many many others that we will not touch on.

For convenience, in this section we will let

$$T_0(z) = \frac{z - i}{z + i}.$$

This is our standard map of taking the upper half-plane to the unit disk.

**Example 10.29.** Let  $H_{\alpha}$  be the half-plane above the line

$$y = \tan(\alpha)x$$
,

i.e.,  $\{(x, y) : y > \tan(\alpha)x\}$ . Find an FLT from  $H_{\alpha}$  to the unit disk.

Solution: We do this in two steps. First use the rotation

$$T_{-\alpha}(z) = e^{-i\alpha}z$$

to map  $H_{\alpha}$  to the upper half-plane. Follow this with the map  $T_0$ . So our map is  $T_0 \circ T_{-\alpha}(z)$ .

You supply the picture

**Example 10.30.** Let A be the channel  $0 \le y \le \pi$  in the xy-plane. Find a conformal map from A to the upper half-plane.

Solution: The map  $f(z) = e^z$  does the trick. (See the Topic 1 notes!)

You supply the picture: horizontal lines get mapped to rays from the origin and vertical segments in the channel get mapped to semicircles.

**Example 10.31.** Let B be the upper half of the unit disk. Show that  $T_0^{-1}$  maps B to the second quadrant.

Solution: You supply the argument and figure.

**Example 10.32.** Let *B* be the upper half of the unit disk. Find a conformal map from *B* to the upper half-plane.

Solution: The map  $T_0^{-1}(z)$  maps B to the second quadrant. Then multiplying by -i maps this to the first quadrant. Then squaring maps this to the upper half-plane. In the end we have

$$f(z) = \left(-i\left(\frac{iz+i}{-z+1}\right)\right)^2.$$

You supply the sequence of pictures.

**Example 10.33.** Let A be the infinite well  $\{(x, y) : x \le 0, 0 \le y \le \pi\}$ . Find a conformal map from A to the upper half-plane.

Solution: The map  $f(z) = e^z$  maps A to the upper half of the unit disk. Then we can use the map from Example 10.32 to map the half-disk to the upper half-plane.

You supply the sequence of pictures.

**Example 10.34.** Show that the function

$$f(z) = z + 1/z$$

maps the region shown below to the upper half-plane.

Solution: You supply the argument and figures

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 11 Notes**

Jeremy Orloff

# 11 Argument Principle

# 11.1 Introduction

The argument principle (or principle of the argument) is a consequence of the residue theorem. It connects the winding number of a curve with the number of zeros and poles inside the curve. This is useful for applications (mathematical and otherwise) where we want to know the location of zeros and poles.

# 11.2 Principle of the argument

#### Setup.

 $\gamma$  a simple closed curve, oriented in a counterclockwise direction.

f(z) analytic on and inside  $\gamma$ , except for (possibly) some finite poles inside (not on)  $\gamma$  and some zeros inside (not on)  $\gamma$ .

Let  $p_1, \ldots, p_m$  be the poles of f inside  $\gamma$ .

Let  $z_1, \ldots, z_n$  be the zeros of f inside  $\gamma$ .

Write  $\operatorname{mult}(z_k)$  = the multiplicity of the zero at  $z_k$ . Likewise write  $\operatorname{mult}(p_k)$  = the order of the pole at  $p_k$ .

We start with a theorem that will lead to the argument principle.

**Theorem 11.1.** With the above setup

$$\int_{\gamma} \frac{f'(z)}{f(z)} dz = 2\pi i \left( \sum \text{mult}(z_k) - \sum \text{mult}(p_k) \right).$$

*Proof.* To prove this theorem we need to understand the poles and residues of f'(z)/f(z). With this in mind, suppose f(z) has a zero of order m at  $z_0$ . The Taylor series for f(z) near  $z_0$  is

$$f(z) = (z - z_0)^m g(z)$$

where g(z) is analytic and never 0 on a small neighborhood of  $z_0$ . This implies

$$\frac{f'(z)}{f(z)} = \frac{m(z - z_0)^{m-1}g(z) + (z - z_0)^m g'(z)}{(z - z_0)^m g(z)}$$
$$= \frac{m}{z - z_0} + \frac{g'(z)}{g(z)}$$

Since g(z) is never 0, g'(z)/g(z) is analytic near  $z_0$ . This implies that  $z_0$  is a simple pole of f'(z)/f(z) and

Res 
$$\left(\frac{f'(z)}{f(z)}, z_0\right) = m = \text{mult}(z_0).$$

Likewise, if  $z_0$  is a pole of order m then the Laurent series for f(z) near  $z_0$  is

$$f(z) = (z - z_0)^{-m} g(z)$$

where g(z) is analytic and never 0 on a small neighborhood of  $z_0$ . Thus,

$$\frac{f'(z)}{f(z)} = -\frac{m(z - z_0)^{-m-1}g(z) + (z - z_0)^{-m}g'(z)}{(z - z_0)^{-m}g(z)}$$
$$= -\frac{m}{z - z_0} + \frac{g'(z)}{g(z)}$$

Again we have that  $z_0$  is a simple pole of f'(z)/f(z) and

Res 
$$\left(\frac{f'(z)}{f(z)}, z_0\right) = -m = -\text{mult}(z_0).$$

The theorem now follows immediately from the Residue Theorem:

$$\int_{\gamma} \frac{f'(z)}{f(z)} dz = 2\pi i \text{sum of the residues}$$
$$= 2\pi i \left( \sum \text{mult}(z_k) - \sum \text{mult}(p_k) \right).$$

**Definition.** We write  $Z_{f,\gamma}$  for the sum of multiplicities of the zeros of f inside  $\gamma$ . Likewise for  $P_{f,\gamma}$ . So the Theorem 11.1 says,

$$\int_{\gamma} \frac{f'}{f} dz = 2\pi i \left( Z_{f,\gamma} - P_{f,\gamma} \right). \tag{1}$$

**Definition.** Winding number. We have an intuition for what this means. We define it formally via Cauchy's formula. If  $\gamma$  is a closed curve then its winding number (or index) about  $z_0$  is defined as

$$\operatorname{Ind}(\gamma, z_0) = \frac{1}{2\pi i} \int_{\gamma} \frac{1}{z - z_0} dz.$$

(In class I'll draw some pictures. You should draw a few now.)

# 11.2.1 Mapping curves: $f \circ \gamma$

One of the key notions in this topic is mapping one curve to another. That is, if  $z = \gamma(t)$  is a curve and w = f(z) is a function, then  $w = f \circ \gamma(t) = f(\gamma(t))$  is another curve. We say f maps  $\gamma$  to  $f \circ \gamma$ . We have done this frequently in the past, but it is important enough to us now, so that we will stop here and give a few examples. This is a key concept in the argument principle and you should make sure you are very comfortable with it.

**Example 11.2.** Let  $\gamma(t) = e^{it}$  with  $0 \le t \le 2\pi$  (the unit circle). Let  $f(z) = z^2$ . Describe the curve  $f \circ \gamma$ .

Solution: Clearly  $f \circ \gamma(t) = e^{2it}$  traverses the unit circle twice as t goes from 0 to  $2\pi$ .

**Example 11.3.** Let  $\gamma(t) = it$  with  $-\infty < t < \infty$  (the y-axis). Let f(z) = 1/(z+1). Describe the curve  $f \circ \gamma(t)$ .

Solution: f(z) is a fractional linear transformation and maps the line given by  $\gamma$  to the circle through the origin centered at 1/2. By checking at a few points:

$$f(-i) = \frac{1}{-i+1} = \frac{1+i}{2}$$
,  $f(0) = 1$ ,  $f(i) = \frac{1}{i+1} = \frac{1-i}{2}$ ,  $f(\infty) = 0$ .

We see that the circle is traversed in a clockwise manner as t goes from  $-\infty$  to  $\infty$ .

The curve  $z = \gamma(t) = it$  is mapped to  $w = f \circ \gamma(t) = 1/(it + 1)$ .

#### 11.2.2 Argument principle

You will also see this called the principle of the argument.

**Theorem 11.4.** Argument principle. For f and  $\gamma$  with the same setup as above

$$\int_{\gamma} \frac{f'(z)}{f(z)} dz = 2\pi i \operatorname{Ind}(f \circ \gamma, 0) = 2\pi i (Z_{f,\gamma} - P_{f,\gamma})$$
 (2)

*Proof.* Theorem 11.1 showed that

$$\int_{\gamma} \frac{f'(z)}{f(z)} dz = 2\pi i (Z_{f,\gamma} - P_{f,\gamma})$$

So we need to show is that the integral also equals the winding number given. This is simply the change of variables w = f(z). With this change of variables the countour  $z = \gamma(t)$  becomes  $w = f \circ \gamma(t)$  and dw = f'(z) dz so

$$\int_{\gamma} \frac{f'(z)}{f(z)} dz = \int_{f \circ \gamma} \frac{dw}{w} = 2\pi i \operatorname{Ind}(f \circ \gamma, 0)$$

The last equality in the above equation comes from the definition of winding number.

Note that by assumption  $\gamma$  does not go through any zeros of f, so  $w = f(\gamma(t))$  is never zero and 1/w in the integral is not a problem.

Here is an easy corollary to the argument principle that will be useful to us later.

Corollary. Assuming that  $f \circ \gamma$  does not go through -1, i.e. there are no zeros of 1 + f(z) on  $\gamma$  then

$$\int_{\gamma} \frac{f'}{f+1} = 2\pi i \operatorname{Ind}(f \circ \gamma, -1) = 2\pi i (Z_{1+f,\gamma} - P_{f,\gamma}). \tag{3}$$

*Proof.* Applying the argument principle in Equation 2 to the function 1 + f(z), we get

$$\int_{\gamma} \frac{(1+f)'(z)}{1+f(z)} dz = 2\pi i \operatorname{Ind}(1+f \circ \gamma, 0) = 2\pi i (Z_{1+f,\gamma} - P_{1+f,\gamma})$$

Now, we can compare each of the terms in this equation to those in Equation 3:

$$\int_{\gamma} \frac{(1+f)'(z)}{1+f(z)} dz = \int_{\gamma} \frac{f'(z)}{1+f(z)} dz \qquad \text{(because } (1+f)' = f')$$

$$\text{Ind}(1+f\circ\gamma,0) = \text{Ind}(f\circ\gamma,-1) \qquad (1+f \text{ winds around } 0 \Leftrightarrow f \text{ winds around } -1)$$

$$Z_{1+f,\gamma} = Z_{1+f,\gamma} \qquad \text{(same in both equations)}$$

$$P_{1+f,\gamma} = P_{f,\gamma} \qquad \text{(poles of } f = \text{poles of } 1+f)$$

**Example 11.5.** Let  $f(z) = z^2 + z$  Find the winding number of  $f \circ \gamma$  around 0 for each of the following curves.

- 1.  $\gamma_1$  = circle of radius 2.
- 2.  $\gamma_2$  = circle of radius 1/2.
- 3.  $\gamma_3$  = circle of radius 1.

**answers.** f(z) has zeros at 0, -1. It has no poles.

So, f has no poles and two zeros inside  $\gamma_1$ . The argument principle says  $\operatorname{Ind}(f \circ \gamma_1, 0) = Z_{f, \gamma_1} - P_{f, \gamma} = 2$ 

Likewise f has no poles and one zero inside  $\gamma_2$ , so  $\operatorname{Ind}(f \circ \gamma_2, 0) = 1 - 0 = 1$ 

For  $\gamma_3$  a zero of f is on the curve, i.e. f(-1) = 0, so the argument principle doesn't apply. The image of  $\gamma_3$  is shown in the figure below – it goes through 0.

The image of 3 different circles under  $f(z) = z^2 + z$ .

#### 11.2.3 Rouché's theorem.

**Theorem 11.6.** Rouchés theorem. Make the following assumptions:  $\gamma$  is a simple closed curve

f, h are analytic functions on and inside  $\gamma$ , except for some finite poles.

There are no poles of f and h on  $\gamma$ .

|h| < |f| everywhere on  $\gamma$ .

Then

$$\operatorname{Ind}(f \circ \gamma, 0) = \operatorname{Ind}((f + h) \circ \gamma, 0).$$

That is,

$$Z_{f,\gamma} - P_{f,\gamma} = Z_{f+h,\gamma} - P_{f+h,\gamma} \tag{4}$$

*Proof.* In class we gave a heuristic proof involving a person walking a dog around  $f \circ \gamma$  on a leash of length  $h \circ \gamma$ . Here is the analytic proof.

The argument principle requires the function to have no zeros or poles on  $\gamma$ . So we first show that this is true of f, f + h, (f + h)/f. The argument is goes as follows.

Zeros: The fact that  $0 \le |h| < |f|$  on  $\gamma$  implies f has no zeros on  $\gamma$ . It also implies f + h has no zeros on  $\gamma$ , since the value of h is never big enough to cancel that of f. Since f and f + h have no zeros, neither does (f + h)/f.

Poles: By assumption f and h have no poles on  $\gamma$ , so f + h has no poles there. Since f has no zeros on  $\gamma$ , (f + h)/f has no poles there.

Now we can apply the argument principle to f and f + h

$$\frac{1}{2\pi i} \int_{\gamma} \frac{f'}{f} dz = \operatorname{Ind}(f \circ \gamma, 0) = Z_{f, \gamma} - P_{f, \gamma}. \tag{5}$$

$$\frac{1}{2\pi i} \int_{\gamma} \frac{(f+h)'}{f+h} dz = \text{Ind}((f+h)\circ\gamma, 0) = Z_{f+h,\gamma} - P_{f+h,\gamma}.$$
 (6)

Next, by assumption  $\left|\frac{h}{f}\right| < 1$ , so  $\left(\frac{h}{f}\right) \circ \gamma$  is inside the unit circle. This means that  $1 + \frac{h}{f} = \frac{f+h}{f}$  maps  $\gamma$  to the inside of the unit disk centered at 1. (You should draw a figure for this.) This implies that

Ind 
$$\left(\left(\frac{f+h}{f}\right)\circ\gamma,0\right)=0.$$

Let  $g = \frac{f+h}{f}$ . The above says  $\operatorname{Ind}(g \circ \gamma, 0) = 0$ . So,  $\int_{\gamma} \frac{g'}{g} dz = 0$ . (We showed above that g has no zeros or poles on  $\gamma$ .)

Now, it's easy to compute that  $\frac{g'}{g} = \frac{(f+h)'}{f+h} - \frac{f'}{f}$ . So, using

$$\operatorname{Ind}(g \circ \gamma, 0) = \int_{\gamma} \frac{g'}{g} dz = \int_{\gamma} \frac{(f+h)'}{f+h} dz - \int_{\gamma} \frac{f'}{f} dz = 0 \Rightarrow \operatorname{Ind}((f+h) \circ \gamma, 0) = \operatorname{Ind}(f \circ \gamma, 0).$$

Now equations 5 and 6 tell us  $Z_{f,\gamma} - P_{f,\gamma} = Z_{f+h,\gamma} - P_{f+h,\gamma}$ , i.e. we have proved Rouchés theorem. **Corollary.** Under the same hypotheses, If h and f are analytic (no poles) then

$$Z_{f,\gamma} = Z_{f+h,\gamma}.$$

*Proof.* Since the functions are analytic  $P_{f,\gamma}$  and  $P_{f+h,\gamma}$  are both 0. So Equation 4 shows  $Z_f = Z_{f+h}$ . QED.

We think of h as a small perturbation of f.

**Example 11.7.** Show all 5 zeros of  $z^5 + 3z + 1$  are inside the curve  $C_2$ : |z| = 2.

Solution: Let  $f(z) = z^5$  and h(z) = 3z + 1. Clearly all 5 roots of f (really one root with multiplicity 5) are inside  $C_2$ . Also clearly, |h| < 7 < 32 = |f| on  $C_2$ . The corollary to Rouchés theorem says all 5 roots of  $f + h = z^5 + 3z + 1$  must also be inside the curve.

**Example 11.8.** Show  $z + 3 + 2e^z$  has one root in the left half-plane.

Solution: Let f(z) = z + 3,  $h(z) = 2e^z$ . Consider the contour from -iR to iR along the y-axis and then the left semicircle of radius R back to -iR. That is, the contour  $C_1 + C_R$  shown below.

To apply the corollary to Rouchés theorem we need to check that (for R large) |h| < |f| on  $C_1 + C_R$ . On  $C_1$ , z = iy, so

$$|f(z)| = |3 + iy| \ge 3$$
,  $|h(z)| = 2|e^{iy}| = 2$ .

So |h| < |f| on  $C_1$ .

On  $C_R$ , z = x + iy with x < 0 and |z| = R. So,

$$|f(z)| > R - 3$$
 for R large,  $|h(z)| = 2|e^{x+iy}| = 2e^x < 2$  (since  $x < 0$ ).

So |h| < |f| on  $C_R$ .

The only zero of f is at z = -3, which lies inside the contour.

Therefore, by the Corollary to Rouchés theorem, f + h has the same number of roots as f inside the contour, that is 1. Now let R go to infinity and we see that f + h has only one root in the entire half-plane.

**Theorem.** Fundamental theorem of algebra.

Rouchés theorem can be used to prove the fundamental theorem of algebra as follows.

Proof. Let

$$P(z) = z^{n} + a_{n-1}z^{n-1} + \dots + a_0$$

be an *n*th order polynomial. Let  $f(z) = z^n$  and h = P - f. Choose an R such that  $R > \max(1, n|a_{n-1}|, \dots, n|a_0|)$ . Then on |z| = R we have

$$|h| \le |a_{n-1}|R^{n-1} + |a_{n-2}|R^{n-2} + \dots + |a_0| \le \frac{R}{n}R^{n-1} + \frac{R}{n}R^{n-2} + \dots + \frac{R}{n} < R^n.$$

On |z| = R we have  $|f(z)| = R^n$ , so we have shown |h| < |f| on the curve. Thus, the corollary to Rouchés theorem says f + h and f have the same number of zeros inside |z| = R. Since we know f has exactly n zeros inside the curve the same is true for the polynomial f + h. Now let R go to infinity, we've shown that f + h has exactly n zeros in the entire plane.

**Note.** The proof gives a simple bound on the size of the zeros: they are all have magnitude less than or equal to  $\max(1, n|a_{n-1}|, \dots, n|a_0|)$ .

# 11.3 Nyquist criterion for stability

The Nyquist criterion is a graphical technique for telling whether an unstable linear time invariant system can be stabilized using a negative feedback loop. We will look a little more closely at such systems when we study the Laplace transform in the next topic. For this topic we will content ourselves with a statement of the problem with only the tiniest bit of physical context.

**Note.** You have already encountered linear time invariant systems in 18.03 (or its equivalent) when you solved constant coefficient linear differential equations.

### 11.3.1 System functions

A linear time invariant system has a system function which is a function of a complex variable. Typically, the complex variable is denoted by *s* and a capital letter is used for the system function.

Let G(s) be such a system function. We will make a standard assumption that G(s) is meromorphic with a finite number of (finite) poles. This assumption holds in many interesting cases. For example, quite often G(s) is a rational function Q(s)/P(s) (Q and P are polynomials).

We will be concerned with the stability of the system.

**Definition.** The system with system function G(s) is called stable if all the poles of G are in the left half-plane. That is, if all the poles of G have negative real part.

The system is called unstable if any poles are in the right half-plane, i.e. have positive real part.

For the edge case where no poles have positive real part, but some are pure imaginary we will call the system marginally stable. This case can be analyzed using our techniques. For our purposes it would require and an indented contour along the imaginary axis. If we have time we will do the analysis.

**Example 11.9.** Is the system with system function 
$$G(s) = \frac{s}{(s+2)(s^2+4s+5)}$$
 stable?

Solution: The poles are -2,  $-2 \pm i$ . Since they are all in the left half-plane, the system is stable.

**Example 11.10.** Is the system with system function 
$$G(s) = \frac{s}{(s^2 - 4)(s^2 + 4s + 5)}$$
 stable?

Solution: The poles are  $\pm 2$ ,  $-2 \pm i$ . Since one pole is in the right half-plane, the system is unstable.

**Example 11.11.** Is the system with system function 
$$G(s) = \frac{s}{(s+2)(s^2+4)}$$
 stable?

Solution: The poles are -2,  $\pm 2i$ . There are no poles in the right half-plane. Since there are poles on the imaginary axis, the system is marginally stable.

**Terminology.** So far, we have been careful to say 'the system with system function G(s)'. From now on we will allow ourselves to be a little more casual and say 'the system G(s)'. It is perfectly

clear and rolls off the tongue a little easier!

#### 11.3.2 Pole-zero diagrams

We can visualize G(s) using a pole-zero diagram. This is a diagram in the s-plane where we put a small cross at each pole and a small circle at each zero.

**Example 11.12.** Give zero-pole diagrams for each of the systems

$$G_1(s) = \frac{s}{(s+2)(s^2+4s+5)}, \quad G_2(s) = \frac{s}{(s^2-4)(s^2+4s+5)}, \quad G_3(s) = \frac{s}{(s+2)(s^2+4s+5)}$$

*Solution:* These are the same systems as in the examples just above. We first note that they all have a single zero at the origin. So we put a circle at the origin and a cross at each pole.

Pole-zero diagrams for the three systems.

#### 11.3.3 A bit about stability

This is just to give you a little physical orientation. Given our definition of stability above, we could, in principle, discuss stability without the slightest idea what it means for physical systems.

The poles of G(s) correspond to what are called modes of the system. A simple pole at  $s_1$  corresponds to a mode  $y_1(t) = e^{s_1 t}$ . The system is stable if the modes all decay to 0, i.e. if the poles are all in the left half-plane.

Physically the modes tell us the behavior of the system when the input signal is 0, but there are initial conditions. A pole with positive real part would correspond to a mode that goes to infinity as *t* grows. It is certainly reasonable to call a system that does this in response to a zero signal (often called 'no input') unstable.

To connect this to 18.03: if the system is modeled by a differential equation, the modes correspond to the homogeneous solutions  $y(t) = e^{st}$ , where s is a root of the characteristic equation. In 18.03 we called the system stable if every homogeneous solution decayed to 0. That is, if the unforced system always settled down to equilibrium.

# 11.3.4 Closed loop systems

If the system with system function G(s) is unstable it can sometimes be stabilized by what is called a negative feedback loop. The new system is called a closed loop system. Its system function is given

by Black's formula

$$G_{CL}(s) = \frac{G(s)}{1 + kG(s)},\tag{7}$$

where k is called the feedback factor. We will just accept this formula. Any class or book on control theory will derive it for you.

In this context G(s) is called the open loop system function.

Since  $G_{CL}$  is a system function, we can ask if the system is stable.

**Theorem.** The poles of the closed loop system function  $G_{CL}(s)$  given in Equation 7 are the zeros of 1 + kG(s).

*Proof.* Looking at Equation 7, there are two possible sources of poles for  $G_{CL}$ .

- 1. The zeros of the denominator 1 + kG. The theorem recognizes these.
- 2. The poles of G. Since G is in both the numerator and denominator of  $G_{CL}$  it should be clear that the poles cancel. We can show this formally using Laurent series. If G has a pole of order n at  $s_0$  then

$$G(s) = \frac{1}{(s - s_0)^n} \left( b_n + b_{n-1}(s - s_0) + \dots + a_0(s - s_0)^n + a_1(s - s_0)^{n+1} + \dots \right),$$

where  $b_n \neq 0$ . So,

$$G_{CL}(s) = \frac{\frac{1}{(s-s_0)^n} \left( b_n + b_{n-1}(s-s_0) + \dots a_0(s-s_0)^n + \dots \right)}{1 + \frac{k}{(s-s_0)^n} \left( b_n + b_{n-1}(s-s_0) + \dots a_0(s-s_0)^n + \dots \right)}$$

$$= \frac{\left( b_n + b_{n-1}(s-s_0) + \dots a_0(s-s_0)^n + \dots \right)}{(s-s_0)^n + k \left( b_n + b_{n-1}(s-s_0) + \dots a_0(s-s_0)^n + \dots \right)},$$

which is clearly analytic at  $s_0$ . (At  $s_0$  it equals  $b_n/(kb_n) = 1/k$ .)

**Example 11.13.** Set the feedback factor k = 1. Assume a is real, for what values of a is the open loop system  $G(s) = \frac{1}{s+a}$  stable? For what values of a is the corresponding closed loop system  $G_{CL}(s)$  stable?

(There is no particular reason that a needs to be real in this example. But in physical systems, complex poles will tend to come in conjugate pairs.)

Solution: G(s) has one pole at s = -a. Thus, it is stable when the pole is in the left half-plane, i.e. for a > 0.

The closed loop system function is

$$G_{CL}(s) = \frac{1/(s+a)}{1+1/(s+a)} = \frac{1}{s+a+1}.$$

This has a pole at s = -a - 1, so it's stable if a > -1. The feedback loop has stabilized the unstable open loop systems with  $-1 < a \le 0$ . (Actually, for a = 0 the open loop is marginally stable, but it is fully stabilized by the closed loop.)

**Note.** The algebra involved in canceling the s+a term in the denominators is exactly the cancellation that makes the poles of G removable singularities in  $G_{CL}$ .

**Example 11.14.** Suppose  $G(s) = \frac{s+1}{s-1}$ . Is the open loop system stable? Is the closed loop system stable when k=2.

Solution: G(s) has a pole in the right half-plane, so the open loop system is not stable. The closed loop system function is

$$G_{CL}(s) = \frac{G}{1+kG} = \frac{(s+1)/(s-1)}{1+2(s+1)/(s-1)} = \frac{s+1}{3s+1}.$$

The only pole is at s = -1/3, so the closed loop system is stable. This is a case where feedback stabilized an unstable system.

**Example 11.15.**  $G(s) = \frac{s-1}{s+1}$ . Is the open loop system stable? Is the closed loop system stable when k=2.

Solution: The only pole of G(s) is in the left half-plane, so the open loop system is stable. The closed loop system function is

$$G_{CL}(s) = \frac{G}{1+kG} = \frac{(s-1)/(s+1)}{1+2(s-1)/(s+1)} = \frac{s-1}{3s-1}.$$

This has one pole at s = 1/3, so the closed loop system is unstable. This is a case where feedback destabilized a stable system. It can happen!

# 11.3.5 Nyquist plot

For the Nyquist plot and criterion the curve  $\gamma$  will always be the imaginary s-axis. That is

$$s = \gamma(\omega) = i\omega$$
, where  $-\infty < \omega < \infty$ .

For a system G(s) and a feedback factor k, the Nyquist plot is the plot of the curve

$$w = kG \circ \gamma(\omega) = kG(i\omega).$$

That is, the Nyquist plot is the image of the imaginary axis under the map w = kG(s).

**Note.** In  $\gamma(\omega)$  the variable is a greek omega and in  $w = G \circ \gamma$  we have a double-u.

**Example 11.16.** Let 
$$G(s) = \frac{1}{s+1}$$
. Draw the Nyquist plot with  $k=1$ .

Solution: In this case G(s) is a fractional linear transformation, so we know it maps the imaginary axis to a circle. It is easy to check it is the circle through the origin with center w = 1/2. You can also check that it is traversed clockwise.

Nyquist plot of 
$$G(s) = 1/(s+1)$$
, with  $k = 1$ .

**Example 11.17.** Take G(s) from the previous example. Describe the Nyquist plot with gain factor k = 2.

Solution: The Nyquist plot is the graph of  $kG(i\omega)$ . The factor k=2 will scale the circle in the previous example by 2. That is, the Nyquist plot is the circle through the origin with center w=1. In general, the feedback factor will just scale the Nyquist plot.

# 11.3.6 Nyquist criterion

The Nyquist criterion gives a graphical method for checking the stability of the closed loop system.

**Theorem 11.18.** Nyquist criterion. Suppose that G(s) has a finite number of zeros and poles in the right half-plane. Also suppose that G(s) decays to 0 as s goes to infinity. Then the closed loop system with feedback factor k is stable if and only if the winding number of the Nyquist plot around w = -1 equals the number of poles of G(s) in the right half-plane.

More briefly,

$$G_{CL}(s)$$
 is stable  $\Leftrightarrow$  Ind $(kG \circ \gamma, -1) = P_{GRHP}$ 

Here,  $\gamma$  is the imaginary s-axis and  $P_{G,RHP}$  is the number of poles of **the original open loop system function** G(s) in the right half-plane.

*Proof.*  $G_{CL}$  is stable exactly when all its poles are in the left half-plane. Now, recall that the poles of  $G_{CL}$  are exactly the zeros of 1 + kG. So, stability of  $G_{CL}$  is exactly the condition that the number of zeros of 1 + kG in the right half-plane is 0.

Let's work with a familiar contour.

Let  $\gamma_R = C_1 + C_R$ . Note that  $\gamma_R$  is traversed in the *clockwise* direction. Choose R large enough that the (finite number) of poles and zeros of G in the right half-plane are all inside  $\gamma_R$ . Now we can apply Equation 3 in the corollary to the argument principle to kG(s) and  $\gamma$  to get

$$-\operatorname{Ind}(kG \circ \gamma_R, -1) = Z_{1+kG, \gamma_R} - P_{G, \gamma_R}$$

(The minus sign is because of the clockwise direction of the curve.) Thus, for all large R

the system is stable 
$$\Leftrightarrow Z_{1+kG,\gamma_R} = 0 \Leftrightarrow \operatorname{Ind}(kG \circ \gamma_R, -1) = P_{G,\gamma_R}$$
.

Finally, we can let R go to infinity. The assumption that G(s) decays 0 to as s goes to  $\infty$  implies

that in the limit, the entire curve  $kG \circ C_R$  becomes a single point at the origin. So in the limit  $kG \circ \gamma_R$  becomes  $kG \circ \gamma$ . QED

### 11.3.7 Examples using the Nyquist Plot mathlet

The Nyquist criterion is a visual method which requires some way of producing the Nyquist plot. For this we will use one of the MIT Mathlets (slightly modified for our purposes).

Open the Nyquist Plot applet at

http://web.mit.edu/jorloff/www/jmoapplets/nyquist/nyquistCrit.html

Play with the applet, read the help.

Now refresh the browser to restore the applet to its original state. Check the *Formula* box. The formula is an easy way to read off the values of the poles and zeros of G(s). In its original state, applet should have a zero at s = 1 and poles at  $s = 0.33 \pm 1.75 i$ .

The left hand graph is the pole-zero diagram. The right hand graph is the Nyquist plot.

**Example 11.19.** To get a feel for the Nyquist plot. Look at the pole diagram and use the mouse to drag the yellow point up and down the imaginary axis. Its image under kG(s) will trace out the Nyquis plot.

Notice that when the yellow dot is at either end of the axis its image on the Nyquist plot is close to 0.

**Example 11.20.** Refresh the page, to put the zero and poles back to their original state. There are two poles in the right half-plane, so the open loop system G(s) is unstable. With k = 1, what is the winding number of the Nyquist plot around -1? Is the closed loop system stable?

Solution: The curve winds twice around -1 in the counterclockwise direction, so the winding number  $\operatorname{Ind}(kG \circ \gamma, -1) = 2$ . Since the number of poles of G in the right half-plane is the same as this winding number, the closed loop system is stable.

**Example 11.21.** With the same poles and zeros, move the k slider and determine what range of k makes the closed loop system stable.

Solution: When k is small the Nyquist plot has winding number 0 around -1. For these values of k,  $G_{CL}$  is unstable. As k increases, somewhere between k=0.65 and k=0.7 the winding number jumps from 0 to 2 and the closed loop system becomes stable. This continues until k is between 3.10 and 3.20, at which point the winding number becomes 1 and  $G_{CL}$  becomes unstable.

Answer: The closed loop system is stable for k (roughly) between 0.7 and 3.10.

**Example 11.22.** In the previous problem could you determine analytically the range of k where  $G_{CL}(s)$  is stable?

*Solution:* Yes! This is possible for small systems. It is more challenging for higher order systems, but there are methods that don't require computing the poles.

In this case, we have

$$G_{CL}(s) = \frac{G(s)}{1 + kG(s)} = \frac{\frac{s-1}{(s-0.33)^2 + 1.75^2}}{1 + \frac{k(s-1)}{(s-0.33)^2 + 1.75^2}} = \frac{s-1}{(s-0.33)^2 + 1.75^2 + k(s-1)}$$

So the poles are the roots of

$$(s-0.33)^2 + 1.75^2 + k(s-1) = s^2 + (k-0.66)s + 0.33^2 + 1.75^2 - k$$

For a quadratic with positive coefficients the roots both have negative real part. This happens when

$$0.66 < k < 0.33^2 + 1.75^2 \approx 3.17$$
.

# **Example 11.23.** What happens when k goes to 0.

Solution: As k goes to 0, the Nyquist plot shrinks to a single point at the origin. In this case the winding number around -1 is 0 and the Nyquist criterion says the closed loop system is stable if and only if the open loop system is stable.

This should make sense, since with k = 0,

$$G_{CL} = \frac{G}{1 + kG} = G.$$

#### **Example 11.24.** Make a system with the following zeros and poles:

A pair of zeros at  $0.6 \pm 0.75i$ 

A pair of poles at  $-0.5 \pm 2.5i$ .

A single pole at 0.25.

Is the corresponding closed loop system stable when k = 6?

Solution: The answer is no,  $G_{CL}$  is not stable. G has one pole in the right half plane. The mathlet shows the Nyquist plot winds once around w=-1 in the *clockwise* direction. So the winding number is -1, which does not equal the number of poles of G in the right half-plane.

If we set k = 3, the closed loop system is stable.

# 11.4 A bit on negative feedback

Given Equation 7, in 18.04 we can ask if there are any poles in the right half-plane without needing any underlying physical model. Still, it's nice to have some sense of where this fits into science and engineering.

In a negative feedback loop the output of the system is looped back and subtracted from the input.

**Example 11.25.** The heating system in my house is an example of a system stabilized by feedback. The thermostat is the feedback mechanism. When the temperature outside (input signal) goes down the heat turns on. Without the thermostat it would stay on and overheat my house. The thermostat turns the heat up or down depending on whether the inside temperature (the output signal) is too low or too high (negative feedback).

**Example 11.26.** Walking or balancing on one foot are examples negative feedback systems. If you feel yourself falling you compensate by shifting your weight or tensing your muscles to counteract the unwanted acceleration.

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

## **Topic 12 Notes**

Jeremy Orloff

# 12 Laplace transform

#### 12.1 Introduction

The Laplace transform takes a function of time and transforms it to a function of a complex variable s. Because the transform is invertible, no information is lost and it is reasonable to think of a function f(t) and its Laplace transform F(s) as two views of the same phenomenon. Each view has its uses and some features of the phenomenon are easier to understand in one view or the other.

We can use the Laplace transform to transform a linear time invariant system from the time domain to the s-domain. This leads to the system function G(s) for the system –this is the same system function used in the Nyquist criterion for stability.

One important feature of the Laplace transform is that it can transform analytic problems to algebraic problems. We will see examples of this for differential equations.

## 12.2 A brief introduction to linear time invariant systems

Let's start by defining our terms.

**Signal.** A signal is any function of time.

**System.** A system is some machine or procedure that takes one signal as input does something with it and produces another signal as output.

**Linear system.** A linear system is one that acts linearly on inputs. That is,  $f_1(t)$  and  $f_2(t)$  are inputs to the system with outputs  $y_1(t)$  and  $y_2(t)$  respectively, then the input  $f_1 + f_2$  produces the output  $y_1 + y_2$  and, for any constant c, the input  $cf_1$  produces output  $cy_1$ .

This is often phrased in one sentence as input  $c_1f_1 + c_2f_2$  produces output  $c_1y_1 + c_2y_2$ , i.e. linear combinations of inputs produces a linear combination of the corresponding outputs.

**Time invariance.** Suppose a system takes input signal f(t) and produces output signal y(t). The system is called time invariant if the input signal g(t) = f(t - a) produces output signal y(t - a).

**LTI.** We will call a linear time invariant system an LTI system.

**Example 12.1.** Consider the constant coefficient differential equation

$$3y'' + 8y' + 7y = f(t)$$

This equation models a damped harmonic oscillator, say a mass on a spring with a damper, where f(t) is the force on the mass and y(t) is its displacement from equilibrium. If we consider f to be the input and y the output, then this is a linear time invariant (LTI) system.

**Example 12.2.** There are many variations on this theme. For example, we might have the LTI system

$$3y'' + 8y' + 7y = f'(t),$$

where we call f(t) the input signal and y(t) the output signal.


## 12.3 Laplace transform

**Definition.** The Laplace transform of a function f(t) is defined by the integral

$$\mathcal{L}(f;s) = \int_0^\infty e^{-st} f(t) dt,$$

for those s where the integral converges. Here s is allowed to take complex values.

**Important note.** The Laplace transform is only concerned with f(t) for  $t \ge 0$ . Generally, speaking we can require f(t) = 0 for t < 0.

**Standard notation.** Where the notation is clear, we will use an upper case letter to indicate the Laplace transform, e.g,  $\mathcal{L}(f;s) = F(s)$ .

The Laplace transform we defined is sometimes called the one-sided Laplace transform. There is a two-sided version where the integral goes from  $-\infty$  to  $\infty$ .

#### 12.3.1 First examples

Let's compute a few examples. We will also put these results in the Laplace transform table at the end of these notes.

**Example 12.3.** Let  $f(t) = e^{at}$ . Compute  $F(s) = \mathcal{L}(f; s)$  directly. Give the region in the complex *s*-plane where the integral converges.

$$\mathcal{L}(e^{at}; s) = \int_0^\infty e^{at} e^{-st} dt = \int_0^\infty e^{(a-s)t} dt = \frac{e^{(a-s)t}}{a-s} \Big|_0^\infty$$

$$= \begin{cases} \frac{1}{s-a} & \text{if } Re(s) > Re(a) \\ \text{divergent} & \text{otherwise} \end{cases}$$

The last formula comes from plugging  $\infty$  into the exponential. This is 0 if Re(a - s) < 0 and undefined otherwise.

**Example 12.4.** Let f(t) = b. Compute  $F(s) = \mathcal{L}(f; s)$  directly. Give the region in the complex s-plane where the integral converges.

$$\mathcal{L}(b; s) = \int_0^\infty b e^{-st} dt = \frac{b e^{-st}}{-s} \Big|_0^\infty$$
$$= \begin{cases} \frac{b}{s} & \text{if Re}(s) > 0\\ \text{divergent} & \text{otherwise} \end{cases}$$

The last formula comes from plugging  $\infty$  into the exponential. This is 0 if Re(-s) < 0 and undefined otherwise.

**Example 12.5.** Let f(t) = t. Compute  $F(s) = \mathcal{L}(f; s)$  directly. Give the region in the complex s-plane where the integral converges.

$$\mathcal{L}(t;s) = \int_0^\infty t e^{-st} dt = \frac{t e^{-st}}{-s} - \frac{e^{-st}}{s^2} \Big|_0^\infty$$
$$= \begin{cases} \frac{1}{s^2} & \text{if } \text{Re}(s) > 0\\ \text{divergent} & \text{otherwise} \end{cases}$$

#### Example 12.6. Compute

$$\mathcal{L}(\cos(\omega t))$$
.

Solution: We use the formula

$$\cos(\omega t) = \frac{e^{i\omega t} + e^{-i\omega t}}{2}.$$

So,

$$\mathcal{L}(\cos(\omega t); s) = \frac{1/(s - i\omega) + 1/(s + i\omega)}{2} = \frac{s}{s^2 + \omega^2}.$$

#### 12.3.2 Connection to Fourier transform

The Laplace and Fourier transforms are intimately connected. In fact, the Laplace transform is often called the Fourier-Laplace transform. To see the connection we'll start with the Fourier transform of a function f(t).

$$\hat{f}(\omega) = \int_{-\infty}^{\infty} f(t) e^{-i\omega t} dt.$$

If we assume f(t) = 0 for t < 0, this becomes

$$\hat{f}(\omega) = \int_0^\infty f(t) e^{-i\omega t} dt.$$
 (1)

Now if  $s = i\omega$  then the Laplace transform is

$$\mathcal{L}(f;s) = \mathcal{L}(f;i\omega) = \int_0^\infty f(t)e^{-i\omega t} dt$$
 (2)

Comparing these two equations we see that  $\hat{f}(\omega) = \mathcal{L}(f; i\omega)$ . We see the transforms are basically the same things using different notation –at least for functions that are 0 for t < 0.

#### 12.4 Exponential type

The Laplace transform is defined when the integral for it converges. Functions of exponential type are a class of functions for which the integral converges for all s with Re(s) large enough.

**Definition.** We say that f(t) has exponential type a if there exists an M such that  $|f(t)| < Me^{at}$  for all  $t \ge 0$ .

**Note.** As we've defined it, the exponential type of a function is not unique. For example, a function of exponential type 2 is clearly also of exponential type 3. It's nice, but not always necessary, to find the smallest exponential type for a function.

**Theorem.** If f has exponential type a then  $\mathcal{L}(f)$  converges absolutely for Re(s) > a.

*Proof.* We prove absolute convergence by bounding

$$|f(t)e^{-st}|$$
.

The key here is that Re(s) > a implies Re(a - s) < 0. So, we can write

$$\int_{0}^{\infty} |f(t)e^{-st}| dt \le \int_{0}^{\infty} |Me^{(a-s)t}| dt = \int_{0}^{\infty} Me^{Re(a-s)t} dt$$

The last integral clearly converges when Re(a - s) < 0. QED

**Example 12.7.** Here is a list of some functions of exponential type.

$$f(t) = e^{at}$$
:  $|f(t)| < 2e^{Re(a)t}$  (exponential type Re(a))  
 $f(t) = 1$ :  $|f(t)| < 2 = 2e^{0 \cdot t}$  (exponential type 0)  
 $f(t) = \cos(\omega t)$ :  $|f(t)| \le 1$  (exponential type 0)

In the above, all of the inequalities are for  $t \ge 0$ .

For f(t) = t, it is clear that for any a > 0 there is an M depending on a such that  $|f(t)| \le Me^{at}$  for  $t \ge 0$ . In fact, it is a simple calculus exercise to show M = 1/(ae) works. So, f(t) = t has exponential type a for any a > 0.

The same is true of  $t^n$ . It's worth pointing out that this follows because, if f has exponential type a and g has exponential type b then fg has exponential type a + b. So, if t has exponential type a then  $t^n$  has exponential type a.

#### 12.5 Properties of Laplace transform

We have already used the linearity of Laplace transform when we computed  $\mathcal{L}(\cos(\omega t))$ . Let's officially record it as a property.

**Property 1.** The Laplace transform is linear. That is, if a and b are constants and f and g are functions then

$$\mathcal{L}(af + bg) = a\mathcal{L}(f) + b\mathcal{L}(g). \tag{3}$$

(The proof is trivial –integration is linear.)

**Property 2.** A key property of the Laplace transform is that, with some technical details,

Laplace transform transforms derivatives in t to multiplication by s (plus some details).

This is proved in the following theorem.

**Theorem.** If f(t) has exponential type a and Laplace transform F(s) then

$$\mathcal{L}(f'(t);s) = sF(s) - f(0), \text{ valid for Re}(s) > a. \tag{4}$$

*Proof.* We prove this using integration by parts.

$$\mathcal{L}(f';s) = \int_0^\infty f'(t)e^{-st} dt = f(t)e^{-st}\Big|_0^\infty + \int_0^\infty sf(t)e^{-st} dt = -f(0) + sF(s).$$

In the last step we used the fact that at  $t = \infty$ ,  $f(t)e^{-st} = 0$ , which follows from the assumption about exponential type.

Equation 4 gives us formulas for all derivatives of f.

$$\mathcal{L}(f'';s) = s^2 F(s) - sf(0) - f'(0) \tag{5}$$

$$\mathcal{L}(f''';s) = s^3 F(s) - s^2 f(0) - s f'(0) - f''(0)$$
(6)

**Proof.** For Equation 5:

$$\mathcal{L}(f'';s) = \mathcal{L}((f')';s) = s\mathcal{L}(f';s) - f'(0) = s(sF(s) - f(0)) - f'(0) = s^2F(s) - sf(0) - f'(0)$$
. QED

The proof Equation 6 is similar. Also, similar statements hold for higher order derivatives.

**Note.** There is a further complication if we want to consider functions that are discontinuous at the origin or if we want to allow f(t) to be a generalized function like  $\delta(t)$ . In these cases f(0) is not defined, so our formulas are undefined. The technical fix is to replace 0 by  $0^-$  in the definition and all of the formulas for Laplace transform. You can learn more about this by taking 18.031.

**Property 3. Theorem.** If f(t) has exponential type a, then F(s) is an analytic function for Re(s) > a and

$$F'(s) = -\mathcal{L}(tf(t); s). \tag{7}$$

*Proof.* We take the derivative of F(s). The absolute convergence for Re(s) large guarantees that we can interchange the order of integration and taking the derivative.

$$F'(s) = \frac{d}{ds} \int_0^\infty f(t) e^{-st} dt = \int_0^\infty -t f(t) e^{-st} dt = \mathcal{L}(-tf(t); s).$$

This proves Equation 7.

Equation 7 is called the *s*-derivative rule. We can extend it to more derivatives in *s*: Suppose  $\mathcal{L}(f;s) = F(s)$ . Then,

$$\mathcal{L}(tf(t);s) = -F'(s) \tag{8}$$

$$\mathcal{L}(t^n f(t); s) = (-1)^n F^{(n)}(s) \tag{9}$$

Equation 8 is the same as Equation 7 above. Equation 9 follows from this.

**Example 12.8.** Use the s-derivative rule and the formula  $\mathcal{L}(1; s) = 1/s$  to compute the Laplace transform of  $t^n$  for n a positive integer.

Solution: Let f(t) = 1 and  $F(s) = \mathcal{L}(f; s)$ . Using the s-derivative rule we get

$$\mathcal{L}(t;s) = \mathcal{L}(tf;s) = -F'(s) = \frac{1}{s^2}$$

$$\mathcal{L}(t^2;s) = \mathcal{L}(t^2f;s) = (-1)^2 F''(s) = \frac{2}{s^3}$$

$$\mathcal{L}(t^n;s) = \mathcal{L}(t^nf;s) = (-1)^n F^n(s) = \frac{n!}{s^{n+1}}$$

**Property 4.** *t*-shift rule. As usual, assume f(t) = 0 for t < 0. Suppose a > 0. Then,

$$\mathcal{L}(f(t-a);s) = e^{-as}F(s) \tag{10}$$

*Proof.* We go back to the definition of the Laplace transform and make the change of variables  $\tau = t - a$ .

$$\mathcal{L}(f(t-a);s) = \int_0^\infty f(t-a)e^{-st} \, dt = \int_a^\infty f(t-a)e^{-st} \, dt$$
$$= \int_0^\infty f(\tau)e^{-s(\tau+a)} \, d\tau = e^{-sa} \int_0^\infty f(\tau)e^{-s\tau} \, d\tau = e^{-sa} F(s).$$

The properties in Equations 3-10 will be used in examples below. They are also in the table at the end of these notes.

#### 12.6 Differential equations

**Coverup method.** We are going to use partial fractions and the coverup method. We will assume you have seen partial fractions. If you don't remember them well or have never seen the coverup method, you should read the note *Partial fractions and the coverup method* posted with the class notes

**Example 12.9.** Solve  $y'' - y = e^{2t}$ , y(0) = 1, y'(0) = 1 using Laplace transform.

Solution: Call  $\mathcal{L}(y) = Y$ . Apply the Laplace transform to the equation gives

$$(s^2Y - sy(0) - y'(0)) - Y = \frac{1}{s - 2}$$

A little bit of algebra now gives

$$(s^2 - 1)Y = \frac{1}{s - 2} + s + 1.$$

So

$$Y = \frac{1}{(s-2)(s^2-1)} + \frac{s+1}{s^2-1} = \frac{1}{(s-2)(s^2-1)} + \frac{1}{s-1}$$

Use partial fractions to write

$$Y = \frac{A}{s-2} + \frac{B}{s-1} + \frac{C}{s+1} + \frac{1}{s-1}.$$

The coverup method gives A = 1/3, B = -1/2, C = 1/6.

We recognize

$$\frac{1}{s-a}$$

as the Laplace transform of  $e^{at}$ , so

$$y(t) = Ae^{2t} + Be^{t} + Ce^{-t} + e^{t} = \frac{1}{3}e^{2t} - \frac{1}{2}e^{t} + \frac{1}{6}e^{-t} + e^{t}.$$

**Example 12.10.** Solve y'' - y = 1, y(0) = 0, y'(0) = 0.

*Solution:* The rest (zero) initial conditions are nice because they will not add any terms to the algebra. As in the previous example we apply the Laplace transform to the entire equation.

$$s^2Y - Y = \frac{1}{s}$$
, so  $Y = \frac{1}{s(s^2 - 1)} = \frac{1}{s(s - 1)(s + 1)} = \frac{A}{s} + \frac{B}{s - 1} + \frac{C}{s + 1}$ 

The coverup method gives A = -1, B = 1/2, C = 1/2. So,

$$y = A + Be^{t} + Ce^{-t} = -1 + \frac{1}{2}e^{t} + \frac{1}{2}e^{-t}.$$

## 12.7 System functions and the Laplace transform

When we introduced the Nyquist criterion for stability we stated without any justification that the system was stable if all the poles of the system function G(s) were in the left half-plane. We also asserted that the poles corresponded to exponential modes of the system. In this section we'll use the Laplace transform to more fully develop these ideas for differential equations.

## 12.7.1 Lightning review of 18.03

Definitions.

**1.**  $D = \frac{d}{dt}$  is called a differential operator. Applied to a function f(t) we have

$$Df = \frac{df}{dt}.$$

We read Df as 'D applied to f.'

**Example 12.11.** If  $f(t) = t^3 + 2$  then  $Df = 3t^2$ ,  $D^2f = 6t$ .

**2.** If P(s) is a polynomial then P(D) is called a polynomial differential operator.

**Example 12.12.** Suppose  $P(s) = s^2 + 8s + 7$ . What is P(D)? Compute P(D) applied to  $f(t) = t^3 + 2t + 5$ . Compute P(D) applied to  $g(t) = e^{2t}$ .

Solution:  $P(D) = D^2 + 8D + 7I$ . (The *I* in 7*I* is the identity operator.) To compute P(D)f we compute all the terms and sum them up:

$$f(t) = t^3 + 2t + 5$$
$$Df(t) = 3t^2 + 2$$
$$D^2f(t) = 6t$$

Therefore:  $(D^2 + 8D + 7I)f = 6t + 8(3t^2 + 2) + 7(t^3 + 2t + 5) = 7t^3 + 24t^2 + 20t + 51$ .

$$g(t) = e^{2t}$$

$$Dg(t) = 2e^{2t}$$

$$D^{2}g(t) = 4e^{2t}$$

Therefore:  $(D^2 + 8D + 7I)g = 4e^{2t} + 8(2)e^{2t} + 7e^{2t} = (4 + 16 + 7)e^{2t} = P(2)e^{2t}$ .

The substitution rule is a straightforward statement about the derivatives of exponentials.

**Theorem 12.13.** (Substitution rule) For a polynomial differential operator P(D) we have

$$P(D)e^{st} = P(s)e^{st}. (11)$$

*Proof.* This is obvious. We 'prove it' by example. Let  $P(D) = D^2 + 8D + 7I$ . Then

$$P(D)e^{at} = a^2e^{at} + 8ae^{at} + 7e^{at} = (a^2 + 8a + 7)e^{at} = P(a)e^{at}.$$

Let's continue to work from this specific example. From it we'll be able to remind you of the general approach to solving constant coefficient differential equations.

**Example 12.14.** Suppose  $P(s) = s^2 + 8s + 7$ . Find the exponential modes of the equation P(D)y = 0.

Solution: The exponential modes are solutions of the form  $y(t) = e^{s_0 t}$ . Using the substitution rule

$$P(D)e^{s_0t} = 0 \iff P(s_0) = 0.$$

That is,  $y(t) = e^{s_0 t}$  is a mode exactly when  $s_0$  is a root of P(s). The roots of P(s) are -1, -7. So the modal solutions are

$$y_1(t) = e^{-t}$$
 and  $y_2(t) = e^{-7t}$ .

**Example 12.15.** Redo the previous example using the Laplace transform.

Solution: For this we solve the differential equation with arbitrary initial conditions:

$$P(D)y = y'' + 8y' + 7y = 0;$$
  $y(0) = c_1, y'(0) = c_2.$ 

Let  $Y(s) = \mathcal{L}(y; s)$ . Applying the Laplace transform to the equation we get

$$(s^{2}Y(s) - sy(0) - y'(0)) + 8(sY(s) - y(0)) + 7Y(s) = 0$$

Algebra:

$$(s^2 + 8s + 7)Y(s) - sc_1 - c_2 - 8c_1 = 0 \iff Y = \frac{sc_1 + 8c_1 + c_2}{s^2 + 8s + 7}$$

Factoring the denominator and using partial fractions, we get

$$Y(s) = \frac{sc_1 + 8c_1 + c_2}{s^2 + 8s + 7} = \frac{sc_1 + 8c_1 + c_2}{(s+1)(s+7)} = \frac{A}{s+1} + \frac{B}{s+7}.$$

We are unconcerned with the exact values of A and B. Taking the Laplace inverse we get

$$v(t) = Ae^{-t} + Be^{-7t}$$
.

That is, y(t) is a linear combination of the exponential modes.

You should notice that the denominator in the expression for Y(s) is none other than the characteristic polynomial P(s).

#### 12.7.2 The system function

**Example 12.16.** With the same P(s) as in Example 12.12 solve the inhomogeneous DE with rest initial conditions: P(D)y = f(t), y(0) = 0, y'(0) = 0.

Solution: Taking the Laplace transform of the equation we get

$$P(s)Y(s) = F(s)$$
.

Therefore

$$Y(s) = \frac{1}{P(s)} F(s)$$

We can't find y(t) explicitly because f(t) isn't specified.

But, we can make the following definitions and observations. Let G(s) = 1/P(s). If we declare f to be the input and g the output of this linear time invariant system, then G(s) is called the system function. So, we have

$$Y(s) = G(s) \cdot F(s). \tag{12}$$

The formula  $Y = G \cdot F$  can be phrased as

output = system function  $\times$  input.

Note well, the roots of P(s) correspond to the exponential modes of the system, i.e. the poles of G(s) correspond to the exponential modes.

The system is called stable if the modes all decay to 0 as t goes to infinity. That is, if all the poles have negative real part.

**Example 12.17.** This example is to emphasize that not all system functions are of the form 1/P(s). Consider the system modeled by the differential equation

$$P(D)x = Q(D)f$$

where P and Q are polynomials. Suppose we consider f to be the input and x to be the ouput. Find the system function.

Solution: If we start with rest initial conditions for x and f then the Laplace transform gives P(s)X(s) = Q(s)F(s) or

$$X(s) = \frac{Q(s)}{P(s)} \cdot F(s)$$

Using the formulation

output = system function  $\times$  input,

we see that the system function is

$$G(s) = \frac{Q(s)}{P(s)}.$$

Note that when f(t) = 0 the differential equation becomes P(D)x = 0. If we make the assumption that the Q(s)/P(s) is in reduced form, i.e. P and Q have no common zeros, then the modes of the system (which correspond to the roots of P(s)) are still the poles of the system function.

**Comments.** All LTI systems have system functions. They are not even all of the form Q(s)/P(s). But, in the *s*-domain, the output is always the system function times the input. If the system function is not rational then it may have an infinite number of poles. Stability is harder to characterize, but under some reasonable assumptions the system will be stable if all the poles are in the left half-plane.

The system function is also called the transfer function. You can think of it as describing how the system transfers the input to the output.

#### 12.8 Laplace inverse

Up to now we have computed the inverse Laplace transform by table lookup. For example,  $\mathcal{L}^{-1}(1/(s-a)) = e^{at}$ . To do this properly we should first check that the Laplace transform has an inverse.

We start with the bad news: Unfortunately this is not strictly true. There are many functions with the same Laplace transform. We list some of the ways this can happen.

1. If f(t) = g(t) for  $t \ge 0$ , then clearly F(s) = G(s). Since the Laplace transform only concerns  $t \ge 0$ , the functions can differ completely for t < 0.

2. Suppose  $f(t) = e^{at}$  and

$$g(t) = \begin{cases} f(t) & \text{for } t \neq 1 \\ 0 & \text{for } t = 1. \end{cases}$$

That is, f and g are the same except we arbitrarily assigned them different values at t = 1. Then, since the integrals won't notice the difference at one point, F(s) = G(s) = 1/(s-a). In this sense it is impossible to define  $\mathcal{L}^{-1}(F)$  uniquely.

The good news is that the inverse exists as long as we consider two functions that only differ on a negligible set of points the same. In particular, we can make the following claim.

**Theorem.** Suppose f and g are continuous and F(s) = G(s) for all s with Re(s) > a for some a. Then f(t) = g(t) for  $t \ge 0$ .

This theorem can be stated in a way that includes piecewise continuous functions. Such a statement takes more care, which would obscure the basic point that the Laplace transform has a unique inverse up to some, for us, trivial differences.

We start with a few examples that we can compute directly.

#### Example 12.18. Let

$$f(t) = e^{at}$$
.

So,

$$F(s) = \frac{1}{s - a}.$$

Show

$$f(t) = \sum \operatorname{Res}(F(s)e^{st})$$
(13)

$$f(t) = \frac{1}{2\pi i} \int_{c-i\infty}^{c+i\infty} F(s) e^{st} ds$$
 (14)

The sum is over all poles of  $e^{st}/(s-a)$ . As usual, we only consider t > 0.

Here, c > Re(a) and the integral means the path integral along the vertical line x = c.

Solution: Proving Equation 13 is straightforward: It is clear that

$$\frac{e^{st}}{s-a}$$

has only one pole which is at s = a. Since,

$$\sum \operatorname{Res}\left(\frac{\mathrm{e}^{st}}{s-a}, a\right) = \mathrm{e}^{at}$$

we have proved Equation 13.

Proving Equation 14 is more involved. We should first check the convergence of the integral. In this case, s = c + iy, so the integral is

$$\frac{1}{2\pi i} \int_{c-i\infty}^{c+i\infty} F(s) e^{st} ds = \frac{1}{2\pi i} \int_{-\infty}^{\infty} \frac{e^{(c+iy)t}}{c+iy-a} i dy = \frac{e^{ct}}{2\pi} \int_{-\infty}^{\infty} \frac{e^{iyt}}{c+iy-a} dy.$$

The (conditional) convergence of this integral follows using exactly the same argument as in the example near the end of Topic 9 on the Fourier inversion formula for  $f(t) = e^{at}$ . That is, the integrand is a decaying oscillation, around 0, so its integral is also a decaying oscillation around some limiting value.

Now we use the contour shown below.

We will let R go to infinity and use the following steps to prove Equation 14.

1. The residue theorem guarantees that if the curve is large enough to contain a then

$$\frac{1}{2\pi i} \int_{C_1 - C_2 - C_3 + C_4} \frac{e^{st}}{s - a} ds = \sum \operatorname{Res} \left( \frac{e^{st}}{s - a}, a \right) = e^{at}.$$

- 2. In a moment we will show that the integrals over  $C_2$ ,  $C_3$ ,  $C_4$  all go to 0 as  $R \to \infty$ .
- 3. Clearly as R goes to infinity, the integral over  $C_1$  goes to the integral in Equation 14 Putting these steps together we have

$$e^{at} = \lim_{R \to \infty} \int_{C_1 - C_2 - C_3 + C_4} \frac{e^{st}}{s - a} ds = \int_{c - i\infty}^{c + i\infty} \frac{e^{st}}{s - a} ds.$$

Except for proving the claims in step 2, this proves Equation 14.

To verify step 2 we look at one side at a time.

 $C_2$ :  $C_2$  is parametrized by  $s = \gamma(u) = u + iR$ , with  $-R \le u \le c$ . So,

$$\left| \int_{C_2} \frac{e^{st}}{s - a} \, ds \right| = \int_{-R}^{c} \left| \frac{e^{(u + iR)t}}{u + iR - a} \right| \le \int_{-R}^{c} \frac{e^{ut}}{R} \, du = \frac{e^{ct} - e^{-Rt}}{tR}.$$

Since c and t are fixed, it's clear this goes to 0 as R goes to infinity.

The bottom  $C_4$  is handled in exactly the same manner as the top  $C_2$ .

 $C_3$ :  $C_3$  is parametrized by  $s = \gamma(u) = -R + iu$ , with  $-R \le u \le R$ . So,

$$\left| \int_{C_{n}} \frac{e^{st}}{s-a} \, ds \right| = \int_{-R}^{R} \left| \frac{e^{(-R+iu)t}}{-R+iu-a} \right| \le \int_{-R}^{R} \frac{e^{-Rt}}{R+a} \, du = \frac{e^{-Rt}}{R+a} \int_{-R}^{R} du = \frac{2Re^{-Rt}}{R+a}.$$

Since a and t > 0 are fixed, it's clear this goes to 0 as R goes to infinity.

**Example 12.19.** Repeat the previous example with f(t) = t for t > 0,  $F(s) = 1/s^2$ .

This is similar to the previous example. Since F decays like  $1/s^2$  we can actually allow  $t \ge 0$ 

**Theorem 12.20.** Laplace inversion 1. Assume f is continuous and of exponential type a. Then for c > a we have

$$f(t) = \frac{1}{2\pi i} \int_{c-i\infty}^{c+i\infty} F(s) e^{st} ds.$$
 (15)

As usual, this formula holds for t > 0.

*Proof.* The proof uses the Fourier inversion formula. We will just accept this theorem for now. Example 12.18 above illustrates the theorem.

**Theorem 12.21.** Laplace inversion 2. Suppose F(s) has a finite number of poles and decays like 1/s (or faster). Define

$$f(t) = \sum \text{Res}(F(s)e^{st}, p_k)$$
, where the sum is over all the poles  $p_k$ . (16)

Then  $\mathcal{L}(f;s) = F(s)$ 

*Proof.* Proof given in class. To be added here. The basic ideas are present in the examples above, though it requires a fairly clever choice of contours.

The integral inversion formula in Equation 15 can be viewed as writing f(t) as a 'sum' of exponentials. This is extremely useful. For example, for a linear system if we know how the system responds to input  $f(t) = e^{at}$  for all a, then we know how it responds to any input by writing it as a 'sum' of exponentials.

#### 12.9 Delay and feedback.

Let f(t) = 0 for t < 0. Fix a > 0 and let h(t) = f(t - a). So, h(t) is a delayed version of the signal f(t). The Laplace property Equation 10 says

$$H(s) = e^{-as}F(s)$$

where H and F are the Laplace transforms of h and f respectively.

Now, suppose we have a system with system function G(s). (Again, called the open loop system.) As before, can feed the output back through the system. But, instead of just multiplying the output by a scalar we can delay it also. This is captured by the feedback factor  $ke^{-as}$ .

The system function for the closed loop system is

$$G_{CL}(s) = \frac{G}{1 + k e^{-as} G}$$

Note even if you start with a rational function the system function of the closed loop with delay is not rational. Usually it has an infinite number of poles.

**Example 12.22.** Suppose G(s) = 1, a = 1 and k = 1 find the poles of  $G_{CL}(s)$ .

Solution:

$$G_{CL}(s) = \frac{1}{1 + e^{-s}}.$$

So the poles occur where  $e^{-s} = -1$ , i.e. at  $in\pi$ , where n is an odd integer. There are an infinite number of poles on the imaginary axis.

**Example 12.23.** Suppose G(s) = 1, a = 1 and k = 1/2 find the poles of  $G_{CL}(s)$ . Is the closed loop system stable?

Solution:

$$G_{CL}(s) = \frac{1}{1 + e^{-s}/2}.$$

So the poles occur where  $e^{-s} = -2$ , i.e. at  $-\log(2) + in\pi$ , where *n* is an odd integer. Since  $-\log(2) < 0$ , there are an infinite number of poles in the left half-plane. With all poles in the left half-plane, the system is stable.

**Example 12.24.** Suppose G(s) = 1, a = 1 and k = 2 find the poles of  $G_{CL}(s)$ . Is the closed loop system stable?

Solution:

$$G_{CL}(s) = \frac{1}{1 + 2e^{-s}}.$$

So the poles occur where  $e^{-s} = -1/2$ , i.e. at  $\log(2) + in\pi$ , where *n* is an odd integer. Since  $\log(2) > 0$ , there are an infinite number of poles in the right half-plane. With poles in the right half-plane, the system is not stable.

**Remark.** If Re(s) is large enough we can express the system function

$$G(s) = \frac{1}{1 + ke^{-as}}$$

as a geometric series

$$\frac{1}{1+ke^{-as}} = 1 - ke^{-as} + k^2e^{-2as} - k^3e^{-3as} + \dots$$

So, for input F(s), we have output

$$X(s) = G(s)F(s) = F(s) - ke^{-as}F(s) + k^2e^{-2as}F(s) - k^3e^{-3as}F(s) + \dots$$

Using the shift formula Equation 10, we have

$$x(t) = f(t) - kf(t-a) + k^2 f(t-2a) - k^3 f(t-3a) + \dots$$

(This is not really an infinite series because f(t) = 0 for t < 0.) If the input is bounded and k < 1 then even for large t the series is bounded. So bounded input produces bounded output –this is also what is meant by stability. On the other hand if k > 1, then bounded input can lead to unbounded output –this is instability.

#### **12.10** Table of Laplace transforms

#### **Properties and Rules**

We assume that f(t) = 0 for t < 0.

| Function        | <u>Transform</u>                       |              |
|-----------------|----------------------------------------|--------------|
| f(t)            | $F(s) = \int_0^\infty f(t) e^{-st} dt$ | (Definition) |
| a f(t) + b g(t) | a F(s) + b G(s)                        | (Linearity)  |
| $e^{at}f(t)$    | F(s-a)                                 | (s-shift)    |
| f'(t)           | sF(s) - f(0)                           |              |

| f''(t)                  | $s^2 F(s) - s f(0) - f'(0)$                       |                                             |
|-------------------------|---------------------------------------------------|---------------------------------------------|
| $f^{(n)}(t)$            | $s^n F(s) - s^{n-1} f(0) - \cdots - f^{(n-1)}(0)$ | 0)                                          |
| tf(t)                   | -F'(s)                                            |                                             |
| $t^n f(t)$              | $(-1)^n F^{(n)}(s)$                               |                                             |
| f(t-a)                  | $e^{-as}F(s)$                                     | ( <i>t</i> -translation or <i>t</i> -shift) |
| $\int_0^t f(\tau)d\tau$ | $\frac{F(s)}{s}$                                  | (integration rule)                          |
| $\frac{f(t)}{t}$        | $\int_{s}^{\infty} F(\sigma)  d\sigma$            |                                             |

# **Function Table**

| <b>Function</b>                                                 | <b>Transform</b>               | Region of convergence |
|-----------------------------------------------------------------|--------------------------------|-----------------------|
| 1                                                               | 1/s                            | Re(s) > 0             |
| e <sup>at</sup>                                                 | 1/(s-a)                        | Re(s) > Re(a)         |
| t                                                               | $1/s^2$                        | Re(s) > 0             |
| $t^n$                                                           | $n!/s^{n+1}$                   | Re(s) > 0             |
| $\cos(\omega t)$                                                | $s/(s^2+\omega^2)$             | Re(s) > 0             |
| $\sin(\omega t)$                                                | $\omega/(s^2+\omega^2)$        | Re(s) > 0             |
| $e^{at}\cos(\omega t)$                                          | $(s-a)/((s-a)^2+\omega^2)$     | Re(s) > Re(a)         |
| $e^{at}\sin(\omega t)$                                          | $\omega/((s-a)^2+\omega^2)$    | Re(s) > Re(a)         |
| $\delta(t)$                                                     | 1                              | all s                 |
| $\delta(t-a)$                                                   | $e^{-as}$                      | all s                 |
| $\cosh(kt) = \frac{e^{kt} + e^{-kt}}{2}$                        | $s/(s^2-k^2)$                  | Re(s) > k             |
| $\sinh(kt) = \frac{e^{kt} - e^{-kt}}{2}$                        | $k/(s^2-k^2)$                  | Re(s) > k             |
| $\frac{1}{2\omega^3}(\sin(\omega t) - \omega t \cos(\omega t))$ | $\frac{1}{(s^2 + \omega^2)^2}$ | Re(s) > 0             |
| $\frac{t}{2\omega}\sin(\omega t)$                               | $\frac{s}{(s^2 + \omega^2)^2}$ | Re(s) > 0             |
| $\frac{1}{2\omega}(\sin(\omega t) + \omega t \cos(\omega t))$   | $\frac{s^2}{(s^2+\omega^2)^2}$ | Re(s) > 0             |
| $t^n e^{at}$                                                    | $n!/(s-a)^{n+1}$               | Re(s) > Re(a)         |
| $\frac{1}{\sqrt{\pi t}}$                                        | $\frac{1}{\sqrt{s}}$           | Re(s) > 0             |
| $t^a$                                                           | $\frac{\Gamma(a+1)}{s^{a+1}}$  | Re(s) > 0             |

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.

---

# **Topic 13 Notes**

Jeremy Orloff

# 13 Analytic continuation and the Gamma function

#### 13.1 Introduction

In this topic we will look at the Gamma function. This is an important and fascinating function that generalizes factorials from integers to all complex numbers. We look at a few of its many interesting properties. In particular, we will look at its connection to the Laplace transform.

We will start by discussing the notion of analytic continuation. We will see that we have, in fact, been using this already without any comment. This was a little sloppy mathematically speaking and we will make it more precise here.

# 13.2 Analytic continuation

If we have an function which is analytic on a region A, we can sometimes extend the function to be analytic on a bigger region. This is called analytic continuation.

Example 13.1. Consider the function

$$F(z) = \int_0^\infty e^{3t} e^{-zt} dt.$$
 (1)

We recognize this as the Laplace transform of  $f(t) = e^{3t}$  (though we switched the variable from s to z). The integral converges absolutely and F is analytic in the region  $A = {\text{Re}(z) > 3}$ .

Can we extend F(z) to be analytic on a bigger region B? That is, can we find a region B a function  $\tilde{F}(z)$  such that

- 1. B contains A
- 2.  $\tilde{F}(z)$  is analytic on B
- 3.  $\tilde{F}(z)$  agrees with F on A, i.e.  $\tilde{F}(z) = F(z)$  for  $z \in A$ .

Solution: Yes! We know that  $F(z) = \frac{1}{z-3}$  -valid for any z in A. So we can define  $\tilde{F}(z) = \frac{1}{z-3}$  for any z in  $B = \mathbb{C} - \{3\}$ .

We say that we have analytically continued F on A to  $\tilde{F}$  on B.

**Note.** Usually we don't rename the function. We would just say F(z) defined by Equation 1 can be continued to  $F(z) = \frac{1}{z-3}$  on B.

**Definition.** Suppose f(z) is analytic on a region A. Suppose also that A is contained in a region B. We say that f can be analytically continued from A to B if there is a function  $\tilde{f}(z)$  such that

- 1.  $\tilde{f}(z)$  is analytic on **B**.
- 2.  $\tilde{f}(z) = f(z)$  for all z in A.

As noted above, we usually just use the same symbol f for the function on A and its continuation to B.


The region A = Re(z) > 0 is contained in B = Re(z) > -1.

**Note.** We used analytic continuation implicitly in, for example, the Laplace inversion formula involving residues of  $F(s) = \mathcal{L}(f; s)$ . Recall that we wrote that for  $f(t) = e^{3t}$ ,  $F(s) = \frac{1}{s-3}$  and

$$f(t) = \sum$$
 residues of  $F$ .

As an integral, F(s) was defined for Re(s) > 3, but the residue formula relies on its analytic continuation to  $\mathbb{C} - \{3\}$ .

#### 13.2.1 Analytic continuation is unique

**Theorem 13.2.** Suppose f, g are analytic on a connected region A. If f = g on an open subset of A then f = g on all of A.

*Proof.* Let h = f - g. By hypothesis h(z) = 0 on an open set in A. Clearly this means that the zeros of h are not isolated. Back in Topic 7 we showed that for analytic h on a connected region A either the zeros are isolated or else h is identically zero on A. Thus, h is identically 0, which implies f = g on A.

**Corollary.** There is at most one way to analytically continue a function from a region A to a connected region B.

*Proof.* Two analytic continuations would agree on A and therefore must be the same.

**Extension.** Since the proof of the theorem uses the fact that zeros are isolated, we actually have the stronger statement: if f and g agree on a nondiscrete subset of A then they are equal. In particular, if f and g are two analytic functions on A and they agree on a line or ray in A then they are equal.

Here is an example that shows why we need A to be connected in Theorem 13.2.

**Example 13.3.** Suppose A is the plane minus the real axis. Define two functions on A as follows.

$$f(z) = \begin{cases} 1 \text{ for } z \text{ in the upper half-plane} \\ 0 \text{ for } z \text{ in the lower half-plane} \end{cases}$$
$$g(z) = \begin{cases} 1 \text{ for } z \text{ in the upper half-plane} \\ 1 \text{ for } z \text{ in the lower half-plane} \end{cases}$$

Both f and g are analytic on A and agree on an open set (the upper half-plane), but they are not the same function.

Here is an example that shows a little care must be taken in applying the corollary.

**Example 13.4.** Suppose we define f and g as follows

$$f(z) = \log(z)$$
 with  $0 < \theta < 2\pi$   
 $g(z) = \log(z)$  with  $-\pi < \theta < \pi$ 

Clearly f and g agree on the first quadrant. But we can't use the theorem to conclude that f = g everywhere. The problem is that the regions where they are defined are different. f is defined on  $\mathbf{C}$  minus the positive real axis, and g is defined on  $\mathbf{C}$  minus the negative real axis. The region where they are both defined is  $\mathbf{C}$  minus the real axis, which is not connected.

Because they are both defined on the upper half-plane, we can conclude that they are the same there. (It's easy to see this is true.) But (in this case) being equal in the first quadrant doesn't imply they are the same in the lower half-plane.

## 13.3 Definition and properties of the Gamma function

**Definition.** The Gamma function is defined by the integral formula

$$\Gamma(z) = \int_0^\infty t^{z-1} e^{-t} dt$$
 (2)

The integral converges absolutely for Re(z) > 0.

### **Properties**

- 1.  $\Gamma(z)$  is defined and analytic in the region Re(z) > 0.
- 2.  $\Gamma(n+1) = n!$ , for integers  $n \ge 0$ .
- 3.  $\Gamma(z+1) = z\Gamma(z)$  (functional equation) This property and Property 2 characterize the factorial function. Thus,  $\Gamma(z)$  generalizes n! to complex numbers z. Some authors will write  $\Gamma(z+1) = z!$ .
- 4.  $\Gamma(z)$  can be analytically continued to be meromorphic on the entire plane with simple poles at  $0, -1, -2 \ldots$  The residues are

$$\operatorname{Res}(\Gamma, -m) = \frac{(-1)^m}{m!}$$

5. 
$$\Gamma(z) = \left[ z e^{\gamma z} \prod_{1}^{\infty} \left( 1 + \frac{z}{n} \right) e^{-z/n} \right]^{-1}$$
, where  $\gamma$  is Euler's constant

$$\gamma = \lim_{n \to \infty} 1 + \frac{1}{2} + \frac{1}{3} + \dots + \frac{1}{n} - \log(n) \approx 0.577$$

This property uses an infinite product. Unfortunately we won't have time, but infinite products represent an entire topic on their own. Note that the infinite product makes the positions of the poles of  $\Gamma$  clear.

6. 
$$\Gamma(z)\Gamma(1-z) = \frac{\pi}{\sin(\pi z)}$$

With Property 5 this gives a product formula for  $\sin(\pi z)$ .

7.  $\Gamma(z+1) \approx \sqrt{2\pi} z^{z+1/2} e^{-z}$  for |z| large,  $\operatorname{Re}(z) > 0$ . In particular,  $n! \approx \sqrt{2\pi} n^{n+1/2} e^{-n}$ . (Stirling's formula)

8. 
$$2^{2z-1}\Gamma(z)\Gamma(z+1/2) = \sqrt{\pi}\Gamma(2z)$$
 (Legendre duplication formula)

**Notes.** These are just some of the many properties of  $\Gamma(z)$ . As is often the case, we could have chosen to define  $\Gamma(z)$  in terms of some of its properties and derived Equation 2 as a theorem.

We will prove (some of) these properties below.

**Example 13.5.** Use the properties of  $\Gamma$  to show that  $\Gamma(1/2) = \sqrt{\pi}$  and  $\Gamma(3/2) = \sqrt{\pi}/2$ .

Solution: From Property 2 we have  $\Gamma(1) = 0! = 1$ . The Legendre duplication formula with z = 1/2 then shows

$$2^0\Gamma\left(\frac{1}{2}\right)\Gamma(1) = \sqrt{\pi}\Gamma(1) \Rightarrow \Gamma\left(\frac{1}{2}\right) = \sqrt{\pi}.$$

Now, using the functional equation Property 3 we get

$$\Gamma\left(\frac{3}{2}\right) = \Gamma\left(\frac{1}{2} + 1\right) = \frac{1}{2}\Gamma\left(\frac{1}{2}\right) = \frac{\sqrt{\pi}}{2}.$$

## 13.4 Connection to Laplace

**Claim.** For Re(z) > 1 and Re(s) > 0,  $\mathcal{L}(t^{z-1}; s) = \frac{\Gamma(z)}{s^z}$ .

*Proof.* By definition  $\mathcal{L}(t^{z-1};s) = \int_0^\infty t^{z-1} \mathrm{e}^{-st} \, dt$ . It is clear that if  $\mathrm{Re}(z) > 1$ , then the integral converges absolutely for  $\mathrm{Re}(s) > 0$ .

Let's start by assuming that s > 0 is real. Use the change of variable  $\tau = st$ . The Laplace integral becomes

$$\int_0^\infty t^{z-1} e^{-st} dt = \int_0^\infty \left(\frac{\tau}{s}\right)^{z-1} e^{-\tau} \frac{d\tau}{s} = \frac{1}{s^z} \int_0^\infty \tau^{z-1} e^{-\tau} = \frac{\Gamma(z)}{s^z} d\tau.$$

This shows that  $\mathcal{L}(t^{z-1};s) = \frac{\Gamma(z)}{s^z}$  for s real and positive. Since both sides of this equation are analytic on Re(s) > 0, the extension to Theorem 13.2 guarantees they are the same.

**Corollary.**  $\Gamma(z) = \mathcal{L}(t^{z-1}; 1)$ . (Of course, this is also clear directly from the definition of  $\Gamma(z)$  in Equation 2.

### 13.5 Proofs of (some) properties of $\Gamma$

Property 1. This is clear since the integral converges absolutely for Re(z) > 0.

Property 2. We know (see the Laplace table)  $\mathcal{L}(t^n; s) = \frac{n!}{s^{n+1}}$ . Setting s = 1 and using the corollary to the claim above we get

$$\Gamma(n+1) = \mathcal{L}(t^n; 1) = n!.$$

(We could also prove this formula directly from the integral definition of of  $\Gamma(z)$ .)

Property 3. We could do this relatively easily using integration by parts, but let's continue using the Laplace transform. Let  $f(t) = t^z$ . We know

$$\mathcal{L}(f,s) = \frac{\Gamma(z+1)}{s^{z+1}}$$

Now assume Re(z) > 0, so f(0) = 0. Then  $f' = zt^{z-1}$  and we can compute  $\mathcal{L}(f'; s)$  two ways.

$$\mathcal{L}(f';s) = \mathcal{L}(zt^{z-1};s) = \frac{z\Gamma(z)}{s^z}$$
$$\mathcal{L}(f';s) = s\mathcal{L}(t^z;s) = \frac{\Gamma(z+1)}{s^z}$$

Comparing these two equations we get property 3 for Re(z) > 0.

Property 4. We'll need the following notation for regions in the plane.

$$\begin{split} B_0 &= \{ \text{Re}(z) > 0 \} \\ B_1 &= \{ \text{Re}(z) > -1 \} - \{ 0 \} \\ B_2 &= \{ \text{Re}(z) > -2 \} - \{ 0, -1 \} \\ B_n &= \{ \text{Re}(z) > -n \} - \{ 0, -1, \dots, -n+1 \} \end{split}$$

So far we know that  $\Gamma(z)$  is defined and analytic on  $B_0$ . Our strategy is to use Property 3 to analytically continue  $\Gamma$  from  $B_0$  to  $B_n$ . Along the way we will compute the residues at 0 and the negative integers.

Rewrite Property 3 as

$$\Gamma(z) = \frac{\Gamma(z+1)}{z} \tag{3}$$

The right side of this equation is analytic on  $B_1$ . Since it agrees with  $\Gamma(z)$  on  $B_0$  it represents an analytic continuation from  $B_0$  to  $B_1$ . We easily compute

$$\operatorname{Res}(\Gamma, 0) = \lim_{z \to 0} z\Gamma(z) = \Gamma(1) = 1.$$

Similarly, Equation 3 can be expressed as  $\Gamma(z+1) = \frac{\Gamma(z+2)}{z+1}$ . So,

$$\Gamma(z) = \frac{\Gamma(z+1)}{z} = \frac{\Gamma(z+2)}{(z+1)z} \tag{4}$$

The right side of this equation is analytic on  $B_2$ . Since it agrees with  $\Gamma$  on  $B_0$  it is an analytic continuation to  $B_2$ . The residue at -1 is

Res
$$(\Gamma, -1)$$
 =  $\lim_{z \to -1} (z + 1)\Gamma(z) = \frac{\Gamma(1)}{-1} = -1$ .

We can iterate this procedure as far as we want

$$\Gamma(z) = \frac{\Gamma(z+m+1)}{(z+m)(z+m-1) + \dots + (z+1)z}$$
 (5)

The right side of this equation is analytic on  $B_{m+1}$ . Since it agrees with  $\Gamma$  on  $B_0$  it is an analytic continuation to  $B_{m+1}$ . The residue at -m is

$$\operatorname{Res}(\Gamma, -m) = \lim_{z \to -m} (z + m) \Gamma(z) = \frac{\Gamma(1)}{(-1)(-2)\dots(-m)} = \frac{(-1)^m}{m!}.$$

We'll leave the proofs of Properties 5-8 to another class!

MIT OpenCourseWare https://ocw.mit.edu

18.04 Complex Variables with Applications Spring 2018

For information about citing these materials or our Terms of Use, visit: https://ocw.mit.edu/terms.
