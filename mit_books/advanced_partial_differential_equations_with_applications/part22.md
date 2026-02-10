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