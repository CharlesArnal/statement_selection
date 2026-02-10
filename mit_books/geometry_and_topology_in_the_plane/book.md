6 I. POLYGONS

## 1. Cutting and pasting polygons

Suppose that we have two polygonal shapes, but equal area. How can we prove that they have the same area? The simplest way would be to cut one into finitely many polygonal pieces, then reassemble those into the second shape.

- We look at several examples such cut-and-paste arguments.
- Inspired by that, we ask whether every equality of areas can be proved in this way.

This is a way of approaching the notion of area (for polygons), without integrals or any kind of limit process.

(1a) Exploring the problem. Let's look at how cutting and pasting polygons can be fun.

Example 1.1. Take a Greek cross:

I would like to cut-and-paste transform it into a square. Let's say that each edge (edges is another word for sides) of the cross has length 1. Then, its area is 5. Hence, a square of equal area must have side-lengths  $\sqrt{5}$ , which suggests the hypothenuse of a right-angled triangle with other sidelengths 1 and 2. Motivated by that, we find a solution:

$$(1.2) \qquad \qquad \begin{array}{c} \begin{array}{c} \\ \\ \end{array} \\ \end{array}$$

Example 1.2. Take a regular 12-gon inscribed in a circle of radius R. Its area is exactly  $3R^2$ . One can prove that using trigonometric functions, but that's too complicated. Instead, we cut the 12-gon into 9 suitable pieces, and then reassemble those pieces into 3 squares of side-length R:

One has to figure out what cuts to make exactly, and why the pieces fit together: don't take my word for it, do it yourself!

Let's look for cut-and-paste strategies which could be useful in general.

Strategy 1.3. Cut-and-paste transforming a triangle into a rectangle is always possible:

STRATEGY 1.4. Cut-and-paste transforming a rectangle into another (of the same area, of course):

For this to work as drawn, we need  $a \le b$ . Therefore, one such step can at most halve the height; we may have to repeat the process several times.

(1b) The general result. To turn this into a systematic discussion, we need to agree on what we are talking about. We only ever look at polygons in the plane. These *are* polygons:

These are *not* polygons:

The first example in (1.6) is a convex polygon. Convexity is not necessary for a polygon (the other two examples in (1.6) are not convex), but it's an important enough notion for us to take a short detour and define it properly.

DEFINITION 1.5. A polygon is convex if, when you take any two points on its boundary, the line segment connecting them never leaves the polygon.

Intuitively, if you build a room in a convex shape, you can see from any point on the wall to any other point (it then also follows that any two people in the room can see each other). Let's get back to our main discussion:

DEFINITION 1.6. Two polygons are called scissors congruent if one of them can be cut into finitely many polygonal pieces, which can be moved around and reassembled to form the other polygon. "Moving around" consists of arbitrary Euclidean transformation (congruence transformations).

8 I. POLYGONS

Clearly, if two polygons are scissors congruent, then they must have the same area. We're interested in the converse, which is not a priori clear, but true:

THEOREM 1.7. If two polygons have the same area, they are scissors congruent.

The proof works as follows. Take the first polygon.

Step 1: Cut it into triangles. This is always possible.

Step 2: Apply Strategy 1.3 to each triangle, to transform it into a rectangle.

Step 3: Apply Strategy 1.4 to each rectangle, to make it size  $1 \times (something)$ .

Step 4: Take all those rectangles and paste them together into a single one of size  $1 \times (something)$ .

We can apply the same process to the second polygon, and arrive at the same rectangle in the end (because that depends only on the area). The concluding idea is to run that process in reverse, so as to transform the rectangle into the second polygon.

(1c) Using less transformations. Each Euclidean transformation is a combination of translations, rotations, and reflections. At no point in the argument above have we actually used reflections: so, Theorem 1.7 is true even if we only allow translations and rotations. Let's see if we can pare down the repertoire of transformations even more.

Fact 1.4 used only translations (no rotations), while Fact 1.3 additionally used 180° rotations. In the proof of Theorem 1.7, we can get up (3) by using only those two kinds of transformations. At that stage, we'll end up with a bunch of rectangles whose sides point in all sorts of directions. In the original Step 4, we (implicitly) rotated the rectangles to align their sides. We can avoid that by inserting another Step  $2\frac{1}{2}$ , which makes all rectangles into axis-parallel ones (with horizontal and vertical sides), without rotating the pieces:

STRATEGY 1.8. Take a rectangle. One can apply a cut-and-paste process to it, which involves only translations, and whose outcome is another rectangle, rotated by any desired angle from the original one. For that, it is maybe simplest to first transform the rectangle into a square, using Strategy 1.4 (which satisfies our condition of using only translations). After that, one does the following:

or, if you prefer to draw it in a single go,

COROLLARY 1.9. Theorem 1.7 is still true if we restrict the notion of scissors congruence to using only translations and 180 degree rotations (instead of all Euclidean transformations).

(1d) Using only translations. Getting bolder, we ask: how about getting away with no rotations at all, meaning using only translations? This is impossible in general. The obstacle is called Hadwiger invariants. Take a polygon P and a nonzero vector w in  $\mathbb{R}^2$  (actually, we only need the direction of that vector, meaning that it doesn't matter if we multiply w by a positive number). The Hadwiger invariant  $had_w(P)$  is defined by

(1.10) 
$$had_w(P) = \sum_e \pm length(e).$$

Here, e are edges (sides) of our polygon which are perpendicular (orthogonal) to w. We set the sign equal to + if w points outwards along e, and - if it points inwards. This definition means that we always have

$$(1.11) had_{-w}(P) = -had_w(P).$$

If the polygon has n edges, there can only be at most 2n directions with nonzero Hadwiger invariants (namely, the pair of opposite directions perpendicular to each edge). However, there can be less than that, due to cancellations.

Example 1.10. The hexagon below has 6 nonzero Hadwiger invariants. Here's one direction out of each pair, plus another direction where the Hadwidger invariant is zero due to cancellations:

(1.12) 
$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

The nifty choice of signs in (1.10) ensures that, if I cut P into  $P_1$ ,  $P_2$  by a straight-line cut, then

(1.13) 
$$\operatorname{had}_{w}(P) = \operatorname{had}_{w}(P_{1}) + \operatorname{had}_{w}(P_{2}) \text{ for all } w.$$

The cut produces a new edge. That new edge occurs for  $P_1$  and for  $P_2$ , but if a perpendicular direction to that edge points inwards for  $P_1$ , then it points outwards for  $P_2$ , hence the associated signs are opposite; which explains (1.13). Moreover, the Hadwiger invariants stay the same under translation. Therefore:

THEOREM 1.11. If two polygons  $P_1$  and  $P_2$  are scissors congruent in a way which uses only translations (and no other Euclidean transformations), then their Hadwiger invariants must agree:

(1.14) 
$$had_w(P_1) = had_w(P_2) \text{ for all } w.$$

This means that besides equality of area, there are other conditions (possibly, one for every edge of  $P_1$  or  $P_2$ ) that need to be satisfied, if we are determined to use only translations.

REMARK 1.12. The analogue of Theorem 1.7 for three-dimensional polytopes is false. Again, this is because there are additional geometric quantities (not Hadwiger invariants, but the so-called Dehn invariant, whose definition is a little more tricky) which are additive under cut-and-paste, and unchanged under Euclidean transformations.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

14 I. POLYGONS

## 2. Integer polygons

An integer polygon is one whose vertices (corners) have integer coordinates.

- We discuss Pick's theorem on the area of integer polygons;
- We consider what coordinate transformations one can apply to integer polygons, and look specifically at integer triangles.

(2a) Computing areas. Let's say we want to estimate the area of a polygon. Here's one way:

(2.1) 
$$\operatorname{area}(P) \approx \text{(number of integer points in } P\text{)}.$$

The idea is that around each integer point (point with integer coordinates) we draw a  $1 \times 1$  square. The collection of those squares approximates the polygon:

Our formulation "in P" left it ambiguous what to do with integer points that lie on the boundary of P. We can improve the formula by treating them differently from the integer points in the interior. If an integer point lies on one of the edges (sides) of P, but is not a vertex (corner), let's count it as  $\frac{1}{2}$  (instead of 1 for points in the interior). If an integer point is a vertex of P, with interior angle  $\alpha$ , we count it as  $\alpha/2\pi$ . Here are two examples of how points contribute to our new formula:

The formula is:

 $area(P) \approx (number of integer points in the interior of P)$ 

(2.4) 
$$+\frac{1}{2}$$
 (number of integer points on the boundary of  $P$ , which are not vertices)  $+\frac{1}{2\pi}$  (sum of interior angles at all integer vertices).

Of course, this idea is still only an approximation. As just one of its many faults, the vertex contribution doesn't quite match the intuition: even in (2.3), based on the idea of which portion of the square lies in our polygon, it should be 1/16 = 0.625 and not  $\arctan(1/2)/2\pi = 0.073...$ 

From now on, we focus on the special case where P is an *integer polygon*, which means that all its vertices are integer points. This means that in (2.4) we are summing over all vertices. For any

polygon, the sum of the interior angles at all the vertices is  $\pi$  (number of vertices -2). Therefore, we can rewrite the formula as follows:

 $area(P) \approx (number of integer points in the interior of P)$ 

(2.5) 
$$+\frac{1}{2}$$
 (number of integer points on the boundary of  $P$ , including vertices)  $-1$ .

Now, a miracle happens:

Theorem 2.1. (Pick's theorem) The formula (2.5) for integer polygons is an exact equality.

Example 2.2. The following polygon has 2 interior integer points, and 8 boundary integer points, hence area 5.

(2b) Integer affine transformations. In classical geometry, congruences (Euclidean transformations) are key. When we talk about integer polygons, it's important to preserve integrality of coordinates. Among Euclidean transformations, this rules out almost all rotations and reflections, which is pretty poor. We propose a wider class of transformations:

DEFINITION 2.3. An integer affine transformation of the plane is a transformation of the form

$$(2.7) v = \begin{pmatrix} x \\ y \end{pmatrix} \longmapsto Av + w = \begin{pmatrix} a & b \\ c & d \end{pmatrix} v + \begin{pmatrix} e \\ f \end{pmatrix} = \begin{pmatrix} ax + by + e \\ cx + dy + f \end{pmatrix}$$

where A is a  $2 \times 2$  matrix with integer entries and  $det(A) = ad - bc = \pm 1$ , and w is an integer vector.

Such transformations do not preserve lengths and angles, but they do preserve area, because the Jacobian has determinant 1. Most importantly for us, if v has integer coordinates, then so does Av + w, and vice versa. One can compose integer affine transformations:

$$(2.8) v \longmapsto A_1 v + w_1 \longmapsto A_2 (A_1 v + w_1) + w_2 = (A_2 A_1) v + (A_2 w_1 + w_2).$$

One can also reverse an integer affine transformation: the inverse of  $v \mapsto Av + w$  is

(2.9) 
$$v \longmapsto A^{-1}(v - w) = A^{-1}v + (-A^{-1}w),$$

and  $A^{-1}$  again has integer entries (by Cramer's rule).

Example 2.4. The matrix  $A = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ , with w = 0, gives the "shear"  $(x, y) \mapsto (x + y, y)$ :

16 I. POLYGONS

DEFINITION 2.5. Two integer polygons are called integer affine equivalent if there is an integer affine transformation carrying one to the other.

Let's look at integer triangles T. After an integer translation, we can assume that the vertices are (0,0), (a,c), and (b,d). The standard formula for area says that

(2.11) 
$$\operatorname{area}(T) = \frac{1}{2} \left| \det \begin{pmatrix} a & b \\ c & d \end{pmatrix} \right|.$$

So the area is always a half-integer (this also follows from Pick's theorem, but I don't want to bother with that theorem here, since the triangle case is so explicit). Integer triangles with area  $\frac{1}{2}$  are called minimal triangles.

Fact 2.6. Any two minimal integer triangles are integer affine equivalent.

The reason is kind of staring us in the face. Take the "standard minimal triangle", which has vertices (0,0), (1,0), (0,1). Then, any triangle with vertices (0,0), (a,c) and (b,d) is the image of our "standard triangle" under the transformation

$$(2.12) v \mapsto Av, \ A = \begin{pmatrix} a & b \\ c & d \end{pmatrix}.$$

If the triangle is minimal, A has determinant  $\pm 1$  by the area formula, so this is an integer affine transformation. Here's an example:

$$(2.13) \qquad \qquad \frac{\begin{pmatrix} -1 & 2 \\ -1 & 1 \end{pmatrix}}{}$$

One can combine two such transformations to relate any two minimal triangles to each other. For integer triangles that are not minimal, there is no statement of that kind.

Example 2.7. These two integer triangles

both have area 4, but are not integer affine equivalent. This is easy to see: one has three points in its interior, the other only one; but integer affine transformations map integer points to integer points, and obviously interior points to interior points.

(2c) Pick's theorem by decomposition. How would one prove Pick's theorem? One way would be to gradually reduce it to simpler shapes.

FACT 2.8. Take an integer polygon P and cut it into two integer polygonal pieces  $P_1$ ,  $P_2$  (for simplicity, let's say by a straight cut going from one integer boundary point of P to another). If Pick's theorem holds for  $P_1$  and  $P_2$ , then it also holds for P.

The cut creates a new edge. Any integer point on that edge, which is not an endpoint is counted as 1/2 each in the count for  $P_1$  and  $P_2$ , which matches the fact that it used to be an interior integer point for P, counted as 1. The two endpoints of the edge are boundary points of P, hence contribute 1/2 + 1/2 = 1 to its count. After cutting, they contribute 1/2 + 1/2 = 1 for each of  $P_1$  and  $P_2$ , but that's compensated by subtracting 1 in (2.5).

Fact 2.9. Pick's theorem holds for minimal triangles.

Indeed, we know that any two minimal triangles are integer affine equivalent, so if it holds for any one of them (like our standard triangle), then it holds for all. This is not circular reasoning, we did not use Pick's theorem when talking about minimal triangles.

Then, to complete the proof of Pick's theorem, one would have to show that any integer polygon can, by repeated cutting, be divided into minimal triangles (which is true). Pick's theorem holds for each such triangle, and then by gradually putting the pieces back together, one gets it for the original polygon. But frankly, that method doesn't give a lot of intuition.

(2d) The oil spill argument. We want to outline a different proof of Pick's theorem, based on a thought experiment. At each integer point in the plane, we deposit a quantity (called 1) of oil. After that, the oil starts spreading out at speed 1, into a larger and larger circular drop of uniform density; and the drops merge, each continuing to spread as if the others didn't exist (you can think of each drop as lying on its own glass plate, and that we are looking at the whole parallel stack of plates from the top). Now introduce an integer polygon P, and ask: at a given time, how much oil is in P?

FACT 2.10. A very small time after the oil is placed, the amount of oil in P is exactly the right hand side of Pick's formula (2.5).

The idea is exactly as in (2.3), except that this time, we are exactly computing the amount of oil. Integer points make contributions like this:

FACT 2.11. As time passes, the amount of oil in P gets closer and closer to the area of P.

Indeed, as the oil spreads, we get closer and closer to a uniform distribution of oil across the plane (with density 1, because we started with a unit of oil at each integer point).

FACT 2.12. At any time, the net flow rate of oil across the boundary of P is zero.

18 I. POLYGONS

Let's forget about the whole of P, and just take one of its edges e (which is a line segment with integer endpoints). The claim is that the flow rate across e is zero. That is true for simple symmetry reasons. A 180 degree rotation around the midpoint of e preserves integer points, and therefore our oil picture at any time is unchanged under that rotation. But if the net flow across the edge was positive in one direction, after rotation, the rotated picture would show it to be positive in the other direction, which is a contradiction.

Because the net flow is zero, the quantity of oil contained in P doesn't change, which means that its value for small t (given by Fact 2.10) equals its limit as  $t \to \infty$  (given by Fact 2.11). Bingo, Pick's theorem follows!

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 3. The shoelace formula and the winding number

This is the last of our three lectures on areas of polygons. We introduce a formula for the area of a polygon, in terms of the coordinates of its vertices. Then, we subject this formula to destructive testing:

- we look at increasingly complicated examples, and finally try cases that are outside the domain of applicability of the formula, because they aren't polygons (they have self-intersections);
- that will lead to the notion of winding number: our first topological invariant.
- (3a) Some coordinate geometry. The length of a vector  $v = (x, y) \in \mathbb{R}^2$  is

$$||v|| = \sqrt{x^2 + y^2}.$$

Given  $v_1 = (x_1, y_1)$  and  $v_2 = (x_2, y_2)$ , their scalar product and cross product are the numbers

$$(3.2) v_1 \cdot v_2 = x_1 x_2 + y_1 y_2,$$

(3.3) 
$$v_1 \times v_2 = x_1 y_2 - y_1 x_2 = \det \begin{pmatrix} x_1 & x_2 \\ y_1 & y_2 \end{pmatrix}.$$

You may be familiar with the cross product in three-dimensional space (where the outcome is again a vector). The two-dimensional version (which produces a number) is not common notation, but we find it convenient here. Both products are linear in each entry (satisfy the distributive law):

$$(3.4) (v_1 + v_2) \cdot v_3 = v_1 \cdot v_3 + v_2 \cdot v_3, v_1 \cdot (v_2 + v_3) = v_1 \cdot v_2 + v_1 \cdot v_3,$$

$$(3.5) (v_1 + v_2) \times v_3 = v_1 \times v_3 + v_2 \times v_3, v_1 \times (v_2 + v_3) = v_1 \times v_2 + v_1 \times v_3.$$

They are also (anti)symmetric:

$$(3.6) v_1 \cdot v_2 = v_2 \cdot v_1,$$

$$(3.7) v_1 \times v_2 = -(v_2 \times v_1).$$

Geometrically, if  $\langle (v_1, v_2) \rangle$  is the angle formed by the vectors,

$$(3.8) v_1 \cdot v_2 = ||v_1|| \, ||v_2|| \, \cos(\langle (v_1, v_2)),$$

$$(3.9) v_1 \times v_2 = ||v_1|| \, ||v_2|| \sin(\sphericalangle(v_1, v_2)).$$

If one of the vectors is zero, both products are zero, so we don't have to think about what we mean by angle. For two nonzero vectors, the sign of  $\langle (v_1, v_2) \rangle$  is important for the second formula: turning from  $v_1$  to  $v_2$  in anticlockwise direction is measured by a positive angle, while turning clockwise is measured by a negative angle. Two vectors are linearly dependent exactly when  $v_1 \times v_2$  is zero. A basis  $(v_1, v_2)$ , consisting of two linearly independent vectors, is called *positively oriented* if  $v_1 \times v_2 > 0$  (meaning that one goes from  $v_1$  to  $v_2$  by an anticlockwise turn with angle

24 I. POLYGONS

between 0 and  $\pi$ ), and negatively oriented if  $v_1 \times v_2 < 0$ .

$$(3.10) \qquad v_2 \qquad v_1 \qquad v_2 \qquad v_2 \qquad v_2 \qquad v_2 \qquad v_2 \qquad v_2 \qquad v_2 \qquad v_3 \qquad v_4 \qquad v_4 \qquad v_5 \qquad v_6 \qquad v_6 \qquad v_7 \qquad v_8 \qquad v_8 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v_9 \qquad v$$

(3b) The shoelace formula. Take a polygon P with n vertices, having coordinates

$$(3.11) v_0 = (x_0, y_0), v_1 = (x_1, y_1), \dots, v_{n-1} = (x_{n-1}, y_{n-1}), v_n = (x_n, y_n) = (x_0, y_0) = v_0.$$

We repeat one vertex (index 0 and index n are the same), since that is convenient for writing down formulae. The *shoelace formula* is

(3.12) 
$$\operatorname{area}(P) = \frac{1}{2} |v_0 \times v_1 + v_1 \times v_2 + \dots + v_{n-1} \times v_n|.$$

This formula is easiest to understand if P is convex and the origin o = (0,0) lies in its interior. If we assume that the ordering of the vertices is anticlockwise, then each  $\frac{1}{2}(v_{k-1} \times v_k)$  is positive, and equals the area of the triangle with vertices  $(o, v_{k-1}, v_k)$ . Adding up those numbers yields the area of P. If the ordering of the vertices is clockwise, the same holds with the opposite signs (in the end, taking the absolute value will cancel out that overall sign change).

EXAMPLE 3.1. The following polygon has area 14 (three triangles of area 3, and two of area 5/2):

(3.13) 
$$(-2,-1) \xrightarrow{(2,2)} (3,0) \operatorname{area}\left( \bigwedge \right) = \frac{1}{2}(-1,2) \times (-2,-1) = 5/2$$

We'll now start analyzing what the formula does in more general situations. First of all, it's not necessary that the origin should lie in the interior of P, because the entire expression is unchanged under translation by any vector w:

$$(v_{0} + w) \times (v_{1} + w) + (v_{1} + w) \times (v_{2} + w) + \dots + (v_{n-1} + w) \times (v_{n} + w)$$

$$= (v_{0} \times v_{1} + v_{0} \times w + w \times v_{1}) + (v_{1} \times v_{2} + v_{1} \times w + w \times v_{2}) + \dots$$

$$= (v_{0} \times v_{1} + v_{1} \times v_{2} + \dots + v_{n-1} \times v_{n}) + (v_{0} + \dots + v_{n-1}) \times w + w \times (v_{1} + \dots + v_{n})$$

$$= v_{0} \times v_{1} + v_{1} \times v_{2} + \dots + v_{n-1} \times v_{n}.$$

It is also not necessary that P should be convex: the shoelace formula still applies, because the terms partially cancel.

Example 3.2. In the following case, one can see how two of the triangles have pieces lying outside P, but those contribute with opposite signs, which provides the required partial cancellation. There is a part of P (shaded more darkly) that lies in 3 triangles, but again, cancellation means that it

is effectively only counted once.

Next, let's look at situations which are not polygons, just polygonal loops. By that, we mean that we are given points (3.11) where the coordinates are arbitrary: points can repeat, the edges may intersect or overlap, and so on. To make that clear, we change the notation, and write p for polygonal loops (as opposed to P for polygons). A polygonal loop doesn't really have an "inside", so while we can plug the coordinates into the shoelace formula, it's not obvious what the output means!

Example 3.3. Working through the example below triangle-by-triangle, we see that the shoelace formula (omitting the absolute value, for simplicity) yields: the area of the light gray shaded region, plus twice the area of the dark gray shaded region, minus the area of the black region. This is easiest to see for the black region, which is part of only one of the triangles, yielding a negative contribution.

The outcome we've been looking for is this (without the absolute value, which is more of a hindrance than a help):

Theorem 3.4. Take a polygonal loop p, with vertices  $(v_0, v_1, \ldots, v_n = v_0)$ . Then

$$(3.17) \qquad \frac{1}{2} \left( v_0 \times v_1 + v_1 \times v_2 + \dots + v_{n-1} \times v_n \right) = \sum_R \operatorname{area}(R) \operatorname{wind}(p, some \ point \ in \ R).$$

Here, the sum is over all regions R into which p divides the plane, and wind $(p, \cdot)$  are the winding numbers of p. (Formally, we include the outermost "unbounded region" R, but that won't matter since its winding number is zero.)

26 I. POLYGONS

(3c) Winding numbers. The formula (3.17) involves a new notion, that of winding number

(3.18) wind
$$(p,q) \in \mathbb{Z}$$
, for  $p$  a polygonal loop, and  $q$  a point not lying on  $p$ .

The name describes the intuition correctly: we stand at the point q, and turn our heads to watch a train moving once around p. The winding number is how many full turns we have done at the end, with counterclockwise turns counting as +1 and clockwise ones as -1. Example 3.3 had winding numbers 1 (light gray shaded part), 2 (dark gray), and -1 (black).

Example 3.5. The star

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

has winding number 2 on the innermost pentagon region, winding number 1 on the triangle regions, and of course 0 for the unbounded region.

Example 3.6. The winding numbers of the following loop take values from -2 to 2. Note the existence of a bounded region with winding number 0:

$$(3.20)$$

Let's return to the initial situation of a polygon P. There, the absolute value of (3.17) computes the area of (the inside of) the polygon. That happens because

(3.21) 
$$\operatorname{wind}(P,q) = \begin{cases} \pm 1 & \text{if } q \text{ lies inside } P, \\ 0 & \text{if } q \text{ lies outside } P. \end{cases}$$

Let's take a step back. Since the beginning of this course, we have used the fact that a polygon divides the plane into two regions, the inside and outside. The formula (3.21) gives us a way to check which of those two regions a point belongs to. Turning this on its head, we can use that idea to give a rigorous proof of the fact that the inside and outside are distinct regions. A similar observation concerns the sign in (3.21). When we think of a polygon as given by a list of numbered vertices, we choose one way of going around it (clockwise or anticlockwise). Clockwise yields a sign of -1, and anticlockwise yields +1. Again, one can use this as a mathematical definition of "clockwise" and "anticlockwise".

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

30 I. POLYGONS

## 4. The winding number (continued)

In the last lecture, we talked about winding numbers in informal terms. Now,

- we give a trigonometric formula for the winding number. It's not a good tool for computing things by hand, but it puts our discussion on a basis which is independent of intuition.
- We look at some properties and applications of winding numbers.

(4a) A formula for the winding number. Remember the intuition behind the winding number: take a polygonal loop p with vertices  $(v_0, v_1, \ldots, v_n = v_0)$ , and a point q not lying on p. Standing at q, we turn around to follow a point which goes once around p, and count the total number of rotations we have performed. One can do this by measuring the total angle by which we have turned (making sure to count clockwise turning negatively), divided by  $2\pi$ .

To make this precise, suppose that we have vectors  $w_1, w_2 \in \mathbb{R}^2$  which are both nonzero, and which do not point in opposite directions ( $w_1$  is not a negative multiple of  $w_2$ ). We measure the angle  $\alpha$  between those two vectors, and write it as

$$\langle (w_1, w_2) = \alpha \in (-\pi, \pi);$$

it is positive if  $(w_1, w_2)$  is a positively oriented basis; negative for negatively oriented bases; and zero if  $w_1, w_2$  are positive multiples of each other. In the application to winding numbers, we are standing and q and watching the segment from  $v_{k-1}$  to  $v_k$ ; the relevant angle is then  $\langle (v_{k-1} - q, v_k - q)$ . It will never happen that  $v_{k-1} - q = 0$ , or that  $v_k = 0$ , or that  $v_{k-1} - q$  and  $v_k - q$  point in opposite directions; because any of those would mean that q lies on p. So  $\langle (v_{k-1} - q, v_k - q)$  is always defined. This gives the following formula, which we use as definition of the winding number:

(4.2) 
$$\operatorname{wind}(p,q) = \frac{1}{2\pi} \sum_{k=1}^{n} \langle (v_{k-1} - q, v_k - q).$$

(4b) **Properties.** In the area formula from the last lecture, we saw wind(p, some point  $q \in R$ ), where R was one of the regions into which p divides the plane. This makes sense because of:

PROPOSITION 4.1. If we move q around without crossing p, wind(p,q) remains constant.

The proof is a classical argument in topology: looking at (4.2) shows that the winding number depends continuously on q (as long as we do not cross p, where the expression becomes ill-defined). But a continuous function can't jump from one integer value to a different one, so wind(p,q) doesn't change if we move q around (again, unless we cross p).

COROLLARY 4.2. Suppose that q can be moved to infinity without crossing p. Then wind(p,q) = 0.

Because of the previous Proposition, we can assume that q is very very far from p. In this case, the vectors  $v_k - q$  are all equal to -q plus an error which is relatively much smaller than q. As a

consequence, the angles in (4.2) are very small, and add up to a number which is much smaller in absolute value than  $2\pi$ , so  $|\text{wind}(p,q)| \ll 1$ . Since the winding number is an integer, it must be zero!

PROPOSITION 4.3. Let  $q_0, q_1$  be two points which lie on either side of one of the edges of p, as follows:

$$\begin{array}{cccc}
p & \bullet^{q_1} \\
q_0 & & \\
\end{array}$$

We assume that all other edges lie outside the picture (this is important!). Then wind $(p, q_1) = \text{wind}(p, q_0) + 1$ .

Let's think of  $q_0$ ,  $q_1$  as lying very close to each other, and that the edge which is being crossed is  $\overline{v_{k-1}v_k}$ . Its contribution to the winding numbers is

$$(4.4)$$

as the following picture shows:

$$v_{k-1} = q_1$$

$$q_0 = q_1$$

$$v_k$$

The other edges contribute approximately the same to wind $(p, q_0)$  and wind $(p, q_1)$ . Therefore, wind $(p, q_1) \approx \text{wind}(p, q_0) + 1$ . But since we are talking about integers, an approximate equality with small error is necessarily a strict equality.

Example 4.4. We compute the winding numbers region by region, starting with the outside (the fat arrows show one possible direction of reasoning):

Proposition 4.3 leads to another algorithm for computing winding numbers. Choose a ray (half-line) starting at q and going to infinity, subject to:

(4.7) the ray must avoid the vertices of p, and intersect each edge in at most one point.

32 I. POLYGONS

Count the intersection points between our ray and the edges of p, with signs:

Explicitly, our ray is determined by a nonzero vector w, and the sign depends on whether  $(w, v_k - v_{k-1})$  is an oriented basis or not. One can write the outcome as:

(4.9) 
$$\operatorname{wind}(p,q) = \sum_{\substack{\text{those } 1 \leq k \leq n \text{ for which} \\ \text{the ray intersects } \overline{v_{k-1}v_k}}} \operatorname{sign}(w \times (v_k - v_{k-1})).$$

This is the first of several formulae of the same kind that we will encounter: each computes a topological quantity by counting points with  $\pm 1$  signs, and in order to work, they require some linear independence condition, in this case (4.7).

REMARK 4.5. The sign conventions in (4.3) and (4.8) may look like opposites, but are consistent: in one situation, we're computing how the winding number around  $q_1$  differs from that around  $q_0$ ; in the other, we're computing the winding number at the starting point q of the ray.

Suppose that P is a polygon. Choose a ray (4.7). Each intersection point of that ray with the edges of P contributes  $\pm 1$  to the winding number. The winding number is even (0) if q lies outside P, and odd  $(\pm 1$ , depending on how our numbering of the vertices goes around P) if q lies inside P. This leads to the "point-in-polygon test":

(4.10) 
$$q$$
 lies  $\begin{cases} \text{outside} \\ \text{inside} \end{cases}$   $P$  if the ray intersects the edges of  $P$  an  $\begin{cases} \text{even} \\ \text{odd} \end{cases}$  number of times.

(4c) A topological application. A simple self-intersection of a polygonal loop is a point where two edges cross: that point is not allowed to be a vertex, and should not lie on any other edge. Here's a loop with a simple self-intersection, and three examples that have more complicated self-intersections (which we don't want here):

Proposition 4.6. Take a polygonal loop which has N simple self-intersections, and no self-intersections of any other kind. divides the plane into N + 2 regions.

There is a process that removes a simple self-intersection point:

$$(4.12)$$

It's important to do it as indicated, so that the outcome is a single loop, and not two of them! Winding numbers show that in the picture above, the parts to the left and right of the intersection point belong to different regions:

(4.13) winding number 
$$x + 1$$
  $x - 1$ 

After we remove the selfintersection point, those two regions get merged. Therefore, (4.12) decreases the number of regions by 1. Repeated application reduces the statement of Proposition 4.6 to the familiar case N=0 of polygons.

Example 4.7. Here's a repeated application of that process, together with the winding numbers:

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

38 I. POLYGONS

## 5. Loops avoiding two points

Fix two points in the plane, and look at polygonal loops that avoid both points. The possible behaviours of such loops are unexpectedly complicated. How can one encode that complexity?

- We introduce a "language" written with four letters, and additional rules for words in that language. This may look strange, but it's actually easy to work with.
- Each loop gives rise to a "word" in our language. One can read off the winding numbers from the word, but it contains much more information than they do.
- (5a) Loops that avoid two points. One can think of the winding number wind(p,q) as describing the topology of polygonal loops p which avoid q. Different winding numbers correspond to qualitatively different behaviours. What if we fix two points a and b, and look at loops that avoid both? There are now two winding numbers wind(p,a) and wind(p,b), but one gets the feeling that this does not describe the situation completely. Here are two loops with wind(p,a) = 2, wind(p,b) = 0, but which in an intuitive sense behave differently:

$$(5.1) \qquad \qquad \bullet a \qquad b \bullet$$

and here is a loops with both winding numbers zero, but which is still somehow nontrivial:

$$(5.2)$$

There is a more sophisticated topological invariant which encodes such complexity. However, it is not a number!

(5b) Letters and words. Take a language which is written using only four letters: A,  $A^{-1}$  ("A-inverse"), B,  $B^{-1}$  ("B-inverse"). A word is an arbitrary sequence of such letters, put inside square brackets to remind us that it's part of our language game:

(5.3) 
$$[A]$$
,  $[AABA]$ ,  $[BAB^{-1}A^{-1}]$ ,... as well as the empty (trivial) word  $[]$ .

There are two rules concerning words. First, when a pair of letters  $AA^{-1}$ ,  $A^{-1}A$ ,  $BB^{-1}$ ,  $B^{-1}B$  occurs, we can cancel it. So

$$[BB^{-1}ABA^{-1}A] = [AB]. \quad [A^{-1}BAA^{-1}B^{-1}A] = [].$$

In reverse, one can also insert a cancelling pair anywhere into a word, if one wants to. We regard this as still being the same word. Second, you can move a letter from the start to the end of the word, or from the end to the start. You can also do this several times:

$$[BABA^{-1}B] = [ABA^{-1}BB] = [BA^{-1}BBA].$$

Again, all these are thought of as being the same word. Even though you can move a letter from the start to the end and back, you can't move letters around arbitrarily: [ABAB] and [AABB] are different words.

(5c) From loops to words. Let p be a polygonal loop which avoids both a and b. Send out a ray from each of our two points a and b to infinity, so that the rays don't intersect each other:

$$(5.6)$$

Those rays should be chosen so that they don't meet the vertices of p, and intersect each edge of p in at most one point, just as in (4.7) from the last lecture. We go once around p and write down a word left-to-right. Each letter corresponds to an intersection point with a ray, and they are assigned following this rule:

For instance, the words associated to the loops from (5.1) are

By comparing the instructions above with those for computing winding numbers, one sees:

FACT 5.1. The winding numbers of a loop can be read off from the associated word: wind(p, a) is the number of A letters minus the number of  $A^{-1}$  letters; and wind(p, b), the number of B letters minus the number of  $B^{-1}$  letters.

However, our language cares not just about counting intersection points with the rays, but also about the order in which those points appear along the loop. For instance, the loop from (5.2) yields the word  $[BA^{-1}B^{-1}A]$ , which is not the empty word [].

Fact 5.2. Every word in our language comes from some loop.

Here's the proof: given a word, we can construct a corresponding loop by taking basic pieces for the letters, which are all loop with the same starting point, and going around one, then a second

40 I. POLYGONS

one, and so on, as required:

Theorem 5.3. The word associated to p is independent of the choice of rays. It also remains the same if we move a and b (as long as we don't cross p).

The reason is this: moving the ray, or the points, can lead to the appearance or disappearance of an  $AA^{-1}$ , and similarly for other cancelling pairs.

It can also lead to moving the last letter to the first position (and vice versa),

With some effort, one can show that this takes into account anything that can happens when moving points and rays.

(5d) Topological implications. Let's see how words interact with geometric properties of polygonal loops.

PROPOSITION 5.4. Suppose that we can move a to infinity without crossing p. Then the word of p is one of the following: [],  $[B \cdots B]$  (a bunch of repeated B) or  $[B^{-1} \cdots B^{-1}]$  (a bunch of repeated  $B^{-1}$ ).

This is a consequence of Theorem 5.3, by contradiction: if one could move a far away, the ray emanating from it could be chosen not to intersect p at all. This means that we get a word involving only the letters B and  $B^{-1}$ . But since those two cancel, we can reduce our word until only B or only  $B^{-1}$ , or the empty word, remain.

PROPOSITION 5.5. Suppose that we can move from a to b without crossing p. Then the word of p is one of the following: [], [BA ... BA] (an even number of letters, with A and B alternating),  $[A^{-1}B^{-1}...A^{-1}B^{-1}]$  (an even number of letters, with  $A^{-1}$  and  $B^{-1}$  alternating).

The argument is similar: one moves a close to b and chooses the rays parallel and to each other, so that each intersection point with ray is followed by an intersection point with the other. The resulting word is made up out of pieces BA or  $A^{-1}B^{-1}$ .

BA and  $A^{-1}B^{-1}$  cancel each other out, so in the end, only one of the two kinds, or the empty word, is left.

PROPOSITION 5.6. For an actual polygon, the word is one of these:  $[], [A], [A^{-1}], [B], [B^{-1}], [AB] = [BA], [A^{-1}B^{-1}] = [B^{-1}A^{-1}].$ 

The idea is that a polygon can go either clockwise or counterclockwise, and we can place the points a, b either both outside, both inside, or one of each. To turn this into a rigorous argument, one again needs Theorem 5.3: if one of our points is outside the polygon, one can move it far away, and then choose a ray which doesn't intersect the polygon at all; if it's inside, one can move it (for instance) close to the topmost vertex, and then choose a ray which intersects the polygon exactly once.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

48 II. BILLIARDS

## 6. Introduction to billiards

Polygonal billiards (or snooker, or pool, or the classic videogame Pong) is the study of Newtonian motion of a point inside a polygon. The interesting aspect is the long-term behaviour of the trajectories of motion. To study that,

- we introduce the simple idea of drawing mirror copies of our polygon. This is generally helpful; and in very special cases, it explains the billiards behaviour completely.
- Using that idea, we investigate the existence of periodic billiards trajectories.

The contents of this lecture belong to elementary geometry, and don't give a good picture of the intricacy of billiards. We will make up for that in the next lecture, where some theoretical muscle will be brought to bear.

(6a) Playing billiards. Suppose that we have a polygon. Inside it, a pointlike ball is moving in a straight line, bouncing off the edges according to the reflection (equal angle) law. We call the path of its motion a billiards trajectory.

$$(6.1)$$

If the ball hits a vertex of the polygon, we declare the behaviour after that to be undefined (for a corner with a general angle, there's no good way to decide how the trajectory should be continued).

If our polygon is a rectangle, any one trajectory only goes in four directions: the direction in which it was originally pointed; the directions obtained from the original one by horizontal or vertical reflection (assuming our rectangle is drawn parallel to the coordinate axes); and the original direction reversed.

While this is a particularly simple situation, there's a class of polygons to which a similar idea applies. Namely, let's say that P is a rational-angle polygon if all interior angles are rational multiples of  $360^{\circ}$  (so, a  $44^{\circ}$  angle would be allowed, but a  $(360/\sqrt{2})^{\circ}$  one would not).

PROPOSITION 6.1. Suppose that we have a rational-angle polygon, in which all interior angles are integer multiples of 180°/M for some natural number M. Then, any single billiards trajectory moves in at most 2M different directions (here, directions refers to the vector which gives the velocity).

For instance, this applies to a rectangle with M=2; and to an equilateral triangle and a regular hexagon, with M=3. To see why the Proposition is true, let's draw a line through the origin parallel to one of the walls, and then all the other lines obtained from it by rotating by multiples of  $180^{\circ}/M$ . When bouncing off a wall, the direction of a billiards trajectory is changed by reflection along one of those M lines. Now, if we have two lines which form an angle  $\alpha$ , then the composition of the two reflections is a rotation with angle  $2\alpha$  (either clockwise or anticlockwise). For our lines,  $\alpha$  is a multiple of  $180^{\circ}/M$ , so the rotation is by some multiple of  $360^{\circ}/M$ . So, if we follow a trajectory and it bounces off walls 6 times, then the new direction is obtained from the original one by 6 reflections, but we can also think of those as three rotations, where the total angle is still an integer multiple of  $360^{\circ}/M$ . If we follow the trajectory through to the 7th bounce, the new direction is given by 7 reflections, or equivalently 1 reflection followed by 3 rotations. Eventually, one sees that all possible directions are obtained from the original one by using either rotations with angle a multiple of  $360^{\circ}/M$ , or a reflection corresponding to the first bounce followed by the same kind of rotations. (In contrast, for polygons that do not have the rational-angle property, a single billiards trajectory can go in infinitely many directions, since the different reflections can combine to yield all sorts of angles of rotation.)

A special kind of billiards trajectories are periodic ones, which repeat the same motion after bouncing off edges a certain number of time. Here are two simple examples, with 2 and 3 bounces:

One could go around those trajectories some number N times, and that would be considered a periodic trajectory with 2N or 3N bounces (but not a particularly interesting one). Here is a 6-bounce periodic trajectory in a square:

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

50 II. BILLIARDS

Given any acute (all angles  $< 90^{\circ}$ ) triangle, the base points of the altitudes form a smaller triangle, called the orthic (or Fagnano) triangle, which is a 3-bounce trajectory:

(6.5)

Checking that a specific periodic trajectory works is elementary, since one only needs to verify the incoming-angle-equals-outgoing angle property; at worst, as in the case of the orthic triangle, that turns into an extended exercise in Euclidean geometry. Finding periodic trajectories is an entirely different story. One might think that Proposition 6.1 would help to solve it, but it falls short, since it only regards the direction, and not the position, of a trajectory. Indeed, most trajectories in a square (those with irrational slope) are not periodic. This remains a lively topics in mathematics, for instance the answer to the following is not known:

QUESTION 6.2. Is there a periodic billiards trajectory in every triangle?

(6b) Mirror polygons. Switching metaphors, let's think of the edges as mirrors, and of our ball as a ray of light. It is a natural idea to add a copy of the polygon that's reflected along one of the edges, as if we were ourselves standing inside the polygon and looking at the mirrors, or as in the image produced by a kaleidoscope. One could then think of a billiards trajectory as continuing straight into the reflected polygon, instead of bouncing off the edge. We call this an unfolded billiards trajectory. One can repeat the process, adding more reflected copies:

In general, that runs into problems as the reflected polygons start to overlap.

However, there are a few special shapes for which we can continue reflecting infinitely many times, with the resulting copies tiling the plane.

Square or rectangle. The tiling (with a symbol 1 placed on each tile, so that you can see in which way it is a reflected copy) is:

Triangle with angles  $45^{\circ}/45^{\circ}/90^{\circ}$ :

Equilateral triangle:

$$(6.10) \qquad \underbrace{1 \checkmark \checkmark \checkmark }_{1 \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark \checkmark$$

Triangle with angles  $30^{\circ}/60^{\circ}/90^{\circ}$ . This has no symmetries, so you can figure out how it's a reflected copy just by looking at the shape, I don't have to mark it with extra stuff:

For those very special shapes, one can draw any billiards trajectory in an "unfolded" way, as a straight line passing through the plane tiled with reflected polygons. This makes it easy to find periodic trajectories! Take two tiles which are oriented in the same way (one is the original polygon, and the other a translated copy of it). Pick points on those which correspond to each other, and join them by a straight line. That line, assuming it avoids vertices, is the unfolded version of a periodic billiards trajectory.

EXAMPLE 6.3. Here is the 6-bounce periodic trajectory in the square, from (6.4), in unfolded and folded form:

One can translate the line, and that gives an infinite family of periodic trajectories.

52 II. BILLIARDS

Example 6.4. Here is a 6-bounce periodic trajectory in an equilateral triangle:

Again, there is an infinite family of such trajectories. One of them, where one starts and ends in the middle of one edge, is a 2-fold repeat of the 3-bounce trajectory from (6.3).

- (6c) Other polygonal shapes. In principle, one can try to use the reflection trick in other situations as well, but then one has to figure out in each case to what extent it works. As a strategy for finding periodic orbits, it goes as follows:
  - (Unfolding) Add reflected copies to the original polygon, until we get to one which is a translated version of the original. These copies may not overlap.
  - (Finding a trajectory) Draw a straight line segment from a point in the original polygon to its counterpart in the translated copy. This segment must be contained in the union of the non-overlapping polygons we drew, and may not pass through any vertex.
  - (Folding back up) By copying the pieces of the straight line segment back into the original polygon, one gets a periodic trajectory, with one bounce for each edge we crossed.

Example 6.5. For the equilateral triangle, we found a 6-bounce trajectory in (6.13). Let's look at a triangle which is close to equilateral, and see if we can do the same thing. Write the sides as (a,b,c), and angles as  $(\alpha,\beta,\gamma)$ . Suppose that we reflect along side a, which yields a mirror triangle with sides (a'=a,c',b'). Reflect the new triangle along b', which yields another triangle with sides (a'',b''=b',c''). Continue in that way, doing 6 reflections in total, using sides in order abcabc. Thinking of how this affects the way in which the triangles are oriented, one gets this simplified picture:

$$(6.14) \qquad \stackrel{a \text{ reflection}}{\Longrightarrow} \qquad \stackrel{b' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{a''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{b'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c'''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''' \text{ reflection}}{\Longrightarrow} \qquad \stackrel{c''' \text{ reflection}}{\Longrightarrow} \qquad$$

The total angle of rotation is  $2\gamma + 2\beta + 2\alpha = 360^{\circ}$ , which means that the final triangle is a translated (not rotated) copy of the original one. One can then get a 6-bounce trajectory as follows:

Of course, to fully justify this, we would have to explain why the 7 triangles in the picture don't overlap, and why we can find a straight line segment that only goes through those particular

reflected copies. All that has to do with how close the picture is to the original one for the equilateral triangle: for obtuse triangles the process fails, but for acute ones it can always be made to work, and as a special case one can get the Fagnano trajectory (twice repeated).

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

58 II. BILLIARDS

## 7. Phase space

This will be a concept-heavy lecture. It involves changing how we picture billiards, in a way that's not immediately intuitive.

- We introduce phase space.
- We measure areas in phase space, and how the billiards dynamics affects those areas.
- As a consequence, we get an abstract but very general existence result about "almost periodic" trajectories.
- (7a) Recurrence. Let's begin with the payoff, the Poincaré recurrence theorem:

THEOREM 7.1. Inside any polygon, choose a point and a direction, in any way you want. Then, there is a billiards trajectory whose starting position and direction are arbitrarily close to the ones we picked, and which after some amount of bounces, returns to a position and direction arbitrarily close to the ones we picked.

"Arbitrarily close" means: you get to specify a desired precision, and the theorem guarantees the existence of a trajectory that fits those specifications. Suppose that you declare the specification to be "positions at distance less than 0.001 from the one we fixed, and directions whose angle differs by less than 0.001° from the one we fixed". By the recurrence theorem, there is a trajectory that starts off like that, and after some unknown time, again satisfies that. If you now get more picky and refine your bounds to 0.000001, there is also a trajectory with those properties, but it will probably be much longer and complicated than the previous one. These trajectories won't usually be periodic: they are only "almost periodic", in the sense that they return to a state very close to their starting state.

(7b) Phase space. Think about coding billiards on a computer. Clearly, it would be a waste of time to simulate the straight-line motion. We should just start at one bounce point, see what direction we take from there, and directly compute the next bounce point and direction. Mathematically, the idea is encoded into phase space. The formal definition of phase space (for billiards in a polygon P) is

(7.1) 
$$\Omega = \bigsqcup_{e} (0, \operatorname{length}(e)) \times (0, \pi).$$

This is a disjoint (meaning non-overlapping) union of rectangles, one for each edge e of the polygon. A point in phase space is written as  $(e, s, \theta)$ , with the following meaning: e is the edge, let's say  $e = \overline{v_{k-1}v_k}$  for some k, where the vertices have been ordered anticlockwise. Then, s specifies a point on the edge, through its distance from  $v_{k-1}$ ; in other words, how far do we have to walk anticlockwise along the edge before reaching our desired point. Finally,  $\theta$  specifies an inwards pointing direction at our point, obtained by rotating the vector  $w = v_k - v_{k-1}$  anticlockwise by the angle  $\theta$ .

Example 7.2. Let's take our polygon to be a  $3 \times 1$  rectangle, with sides labeled abcd. Here are some examples of phase space coordinates:

(7c) The billiards map. Take a point p in phase space, meaning a boundary point and inwards direction. Place the ball at the boundary point, and move it in the prescribed direction until we again hit the boundary of the polygon. Then, record the new position and the reflected direction (the direction in which the ball will continue after bouncing off). This defines another point in phase space, T(p). We can think of this as a map from phase space to phase space, the billiards map

$$(7.3) T: \Omega - - > \Omega.$$

If we are interested in what happens to our trajectory as it keeps bouncing, we form T(T(p)), T(T(T(p))), ... in that way, we have transformed continuous billiards motion into a problem of repeated application of the billiards map. There is also an inverse billiards map  $T^{-1}: \Omega \dashrightarrow \Omega$ , which is obtained by running the billiards motion in reverse. It satisfies

$$(7.4) T(T^{-1}(p)) = T^{-1}(T(p)).$$

Why is the arrow in (7.3) dashed? Because we could run into a corner, in which case T(p) is not defined. The same holds for  $T^{-1}$ , so the equalities in (7.4) hold only if no such catastrophe happens.

Example 7.3. We take a simple 4-bounce periodic billiards trajectory in a  $1 \times 1$  square, where each bounce happens a third of the way off from a corner:

$$(7.5) d a$$

Each segment of the trajectory (or rather, the starting point and direction of that segment) corresponds to a point in phase space. The map T takes the point corresponding to a segment to that

60 II. BILLIARDS

for the subsequent segment. The outcome is that we get four phase space points permuted by T:

(7.6) 
$$(a, s = 1/3, \theta = \pi/4)$$

$$a$$

$$b$$

$$(d, s = 2/3, \theta = \pi/4)$$

$$c$$

$$T$$

$$d$$

$$d$$

What can one say about the billiards map in general? Let's write  $T(e, s, \theta) = (e', s', \theta')$ . If we vary s a little, and keep  $\theta$  fixed, the trajectory gets displaced to a parallel one:

As the diagram shows, we have

(7.8) 
$$T(e, s + \Delta s, \theta) = (e', s' + \Delta s', \theta') = \left(e', s' - \frac{\sin(\theta)}{\sin(\theta')} \Delta s, \theta'\right).$$

If we keep s fixed and vary  $\theta$ , then  $\theta'$  decreases by the same amount; and s' also changes, but in a more complicated way, which we won't try to write down.

(7.9) 
$$T(e, s, \theta + \Delta \theta) = (e', s' + something, \theta' - \Delta \theta).$$

In calculus language,

(7.10) 
$$\frac{\partial s'}{\partial s} = -\frac{\sin(\theta)}{\sin(\theta')}, \qquad \frac{\partial s'}{\partial \theta} = (something),$$

$$\frac{\partial \theta'}{\partial s} = 0, \qquad \frac{\partial \theta'}{\partial \theta} = -1.$$

(7d) Conservation of areas and the recurrence theorem. At this point, we change coordinates on the phase space a little, keeping s, but replacing  $\theta \in (0, \pi)$  by  $t = -\cos(\theta) \in (-1, 1)$ . In these coordinates, phase space looks like this:

$$(7.11) (e, s, t) \in \Omega = \bigsqcup_{e} (0, \operatorname{length}(e)) \times (-1, 1).$$

While apparently arbitrary, this change leads to a crucial insight into the nature of the billiards map. Writing T(s,t) = (s',t') in our new coordinates, the chain rule says that

(7.12) 
$$\frac{\partial t'}{\partial t} = \frac{\partial t'}{\partial \theta} \frac{\partial \theta'}{\partial \theta} \left( \frac{\partial t}{\partial \theta} \right)^{-1} = \sin(\theta')(-1)\sin(\theta)^{-1} = -\frac{\sin(\theta')}{\sin(\theta)}.$$

Let's summarize the situation in a matrix of derivatives

(7.13) 
$$\begin{pmatrix} \frac{\partial s'}{\partial s} & \frac{\partial s'}{\partial t} \\ \frac{\partial t'}{\partial s} & \frac{\partial t'}{\partial t} \end{pmatrix} = \begin{pmatrix} -\frac{\sin(\theta)}{\sin(\theta')} & (something) \\ 0 & -\frac{\sin(\theta')}{\sin(\theta)} \end{pmatrix}.$$

Even though we haven't computed one of the entries, we can see that the matrix has determinant 1. By general change-of-coordinate formulas, this implies what's known as Liouville's theorem:

Theorem 7.4. In (s,t) coordinates on the phase space, the billiards map is area-preserving.

We now return to the Poincaré recurrence theorem, in a formulation that uses phase space, and which is more mathematically precise than before. This is the same statement, even though it may take some time to recognize that!

Theorem 7.5. Let  $U \subset \Omega$  be any subset with positive area. Then, there is some  $p \in U$  and an M > 0 such that

(7.14) 
$$T^{M}(p) = \overbrace{T(T(\cdots(p))\cdots)}^{M \text{ times}} \in U.$$

The proof is easy: take a natural number N and look at the sets

$$(7.15) U, T(U), T^{2}(U), \dots, T^{N-1}(U).$$

Working in (s,t) coordinates, all those have the same area by Liouville's theorem. If they didn't overlap, the area of their union would be N times the area of U. On the other hand, the area of the entire phase space is finite: it's twice the perimeter of the polygon. If N is really large, that's a contradiction, so our sets must overlap after all. To say it more precisely, there must be  $1 \leq N_1 < N_2 \leq N$  such that  $T^{N_1}(U) \cap T^{N_2}(U)$  has positive area. Now we apply the inverse billiards map, which also preserves areas:

$$(7.16) \quad \operatorname{area}(T^{N_1}(U) \cap T^{N_2}(U)) = \operatorname{area}(T^{N_1-1}(U) \cap T^{N_2-1}(U)) = \dots = \operatorname{area}(U \cap T^{N_2-N_1}(U)).$$

Since the last intersection has positive area, there must be a point in it. This was our desired goal, and we got  $M = N_2 - N_1$ . There's a possible objection: we've argued as if T was a one-to-one (invertible) map from  $\Omega$  to itself, whereas really it's not everywhere defined, and the same for  $T^{-1}$ . However, the badly-behaved points form one-dimensional subsets of phase space, which have zero area, so they don't affect our argument after all.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

66 II. BILLIARDS

## 8. Billiards in curved domains

Billiards makes sense in regions with curved boundaries. Some of the things we've talked about (like phase space) also work in this context. However, we like to focus on what's new.

- We discuss the law of reflection for curved boundaries, and playing billiards in an ellipse.
- We use the extremal-length interpretation of the law of reflection to give an abstract existence criterion for periodic orbits.
- We return to phase space, and talk about how that can be used to understand optical devices consisting of curved mirrors.

(8a) The law of reflection. When light bounces off a curved mirror, the law of reflection says that the incoming and outgoing angles between the ray of light and the tangent line to the mirror must be equal. This is what we will choose as the behaviour for billiards in curved billiards tables.

One can derive the equal-angle reflection law from an extremal (shortest path) principle. Namely, suppose that we consider a curved mirror parametrized as  $c(t) \in \mathbb{R}^2$ . Fix two points p and q that do not lie on our mirror. Let's suppose that we go from p to a point c(t) on the curve, and then from there to q, each time along a straight line.

vector 
$$c(t) - p$$

vector  $q - c(t)$ 

vector  $q - c(t)$ 

vector  $q - c(t)$ 

The total length of this path is

$$(8.2) S(t) = ||c(t) - p|| + ||c(t) - q|| = \sqrt{(c(t) - p) \cdot (c(t) - p)} + \sqrt{(c(t) - q) \cdot (c(t) - q)}.$$

We differentiate this, and use the product rule for the scalar product:

(8.3) 
$$S'(t) = \frac{(c(t) - p) \cdot c'(t)}{\|c(t) - p\|} + \frac{(c(t) - q) \cdot c'(t)}{\|c(t) - q\|}.$$

Let's divide this by ||c'(t)|| and rewrite it as

(8.4) 
$$\frac{S'(t)}{\|c'(t)\|} = \frac{c(t) - p}{\|c(t) - p\|} \cdot \frac{c'(t)}{\|c'(t)\|} - \frac{q - c(t)}{\|q - c(t)\|} \cdot \frac{c'(t)}{\|c'(t)\|}.$$

Now, all the vectors in the scalar products have length one, so the scalar product is the cosine of the angles  $\alpha$  and  $\beta$ . In particular, S'(t) = 0 if and only if the angles are equal. Let's remember this:

PROPOSITION 8.1. S'(t) = 0 if and only if the trajectory from p to c(t) to q satisfies the equal-angle law.

Let's look at the special case of an ellipse. Take two points p and q, which will be the foci of the ellipse, and some number s which is bigger than the distance between them. The ellipse is then defined as the set of points  $v \in \mathbb{R}^2$  such that

$$(8.5) ||v - p|| + ||v - q|| = s.$$

Consider paths from p to a point on the ellipse and then back to q. By definition, the length of such path is then independent of which point on the ellipse we pick. In other words, if we parametrized the ellipse in some way, then R(t) = r would be a constant function. This means that the assumption from Proposition 8.1 is always satisfied:

FACT 8.2. If a billiards trajectory in the ellipse starts at one focus, then after bouncing off once it will reach the other focus.

The trajectories that keep hitting foci have a characteristic behaviour. Namely, as we extend them far into the future, they keep getting closer and closer to the major axis, which is the line between the two foci. (An extreme special case is the periodic trajectory that just keeps bouncing back and forth along that axis.)

Of course, these are not all the trajectories in the ellipse: there are lots of others, which never hit a focus.

Now we leave the ellipse behind, and return to the general question of periodic orbits, for a large class of billiards tables.

Theorem 8.3. Suppose that our billiards region has no corners, and is strictly convex. Then, for every  $n \geq 2$ , there is (at least) one periodic billiards trajectory with n bounces.

No corners means that the boundary of the region is smooth everywhere. The other condition is:

DEFINITION 8.4. Strict convexity means that if you have two points on the boundary of our region, the line segment connecting them stays inside our region, and doesn't touch the boundary anywhere except at its endpoints (so, a polygon can never be strictly convex, but a curved region can be).

The proof of the theorem is remarkably easy: consider all possible polygonal loops with n vertices, with the vertices lying on the boundary of our region. Clearly, there's an upper bound on the length of such loops. Analysis tells us that the maximum is achieved by some loop. When we derived the equal-angle law, we used only vanishing of the derivative of the length. Hence, that reasoning applies not just to the shortest path, but also the longest one. This shows that the

68 II. BILLIARDS

longest path must satisfy the equal-angle law, hence is a billiards trajectory. You can see where the argument would go wrong for polygonal billiards: the longest loop can be one that goes through corners, so it's not well-defined as a billiards trajectory.

(8b) The limitations of optical devices. The phase space picture also applies to billiards in curved domains. Suppose we have a billiards table whose boundary consists of curved segments (corners are allowed). One defines phase space in  $(s, t = -cos(\theta))$  coordinates again as

(8.7) 
$$\Omega = \bigsqcup_{e} (0, \operatorname{length}(e)) \times (-1, 1).$$

where e are the segments of the boundary, and length(e) is the arclength. The second coordinate is  $t = -\cos(\theta)$ , where  $\theta \in (0, \pi)$  measures the angle between with respect to the tangent line at the appropriate boundary point. Everything we have said, including the billiards transformation T and its area-preserving property (Liouville's theorem), still applies.

There are implications of this in optics (in our discussion, the world is two-dimensional, but the three-dimensional world also satisfies a version of that). Take a box with two holes ("input" and "output") of length l and m, respectively. Inside the box, we arrange N curved mirrors. What we want is that all the light coming through the input hole, at an angle of at most  $\alpha$  from the perpendicular direction, bounces off our mirrors in fixed order  $1, 2, \ldots, N$ , and then leaves through the output hole, at an angle of at most  $\beta$  from the perpendicular direction:

You can take any n, and make the mirrors of arbitrarily curved shapes. When is this possible? The first insight is this:

PROPOSITION 8.5. If the input and output lengths are equal, l = m, then the angles must satisfy  $\beta > \alpha$ ; you can't squeeze the light into a smaller angle!

PROPOSITION 8.6. If the input and output angles are equal,  $\alpha = \beta$ , then the lengths must satisfy  $l \leq m$ : you can't make the output hole smaller than the input!

The idea is to think of the whole thing as a curved billards table, by joining the mirrors with arbitrary other pieces, and where the input and output holes are straight-line parts of the boundary.

The incoming light can be thought of as a billiards trajectory starting at an input line, and whose angular coordinate in phase space is constrained to

(8.10) 
$$\theta \in (\pi/2 - \alpha, \pi/2 + \alpha), \text{ or equivalently,}$$
$$t \in (-\cos(\pi/2 - \alpha), -\cos(\pi/2 + \alpha)) = (-\sin(\alpha), \sin(\alpha)).$$

In other words, those starting points form a region in phase space,

$$(8.11) U = (0, l) \times (-\sin(\alpha), \sin(\alpha)).$$

After N+1 applications of the billiards map, we end up in a similar rectangle describing how one would be our off the straight line corresponding to the output end,

(8.12) 
$$V = (0, m) \times (-\sin(\beta), -\sin(\beta)).$$

Our requirement that this should work for all light rays then means that the billiards transformation T should satisfy

$$(8.13) T^{N+1}(U) \subset V.$$

Since areas are preserved under T, this can only happen if

(8.14) 
$$\operatorname{area}(U) = 2l\sin(\alpha) \le \operatorname{area}(V) = 2m\sin(\beta).$$

Special cases of this  $(l = m, \text{ or } \alpha = \beta)$  explain the two Propositions above. We have actually proved more:

Proposition 8.7. In general, for the optical contraption to be theoretically possible, we need

$$(8.15) \frac{l}{m} \le \frac{\sin(\beta)}{\sin(\alpha)}.$$

In words, you can squeeze the angles  $(\beta < \alpha)$  but only by making the output opening larger than the input one (l < m); or you can make the output smaller than the input, but have to tolerate a larger output angle; and there are precise quantitative bounds on that. One could check by computation see that a specific system (say, a single circular-piece mirror) satisfies those constraints. The remarkable thing is that they apply to systems of mirrors of any shape.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 9. First computations

The vibrational properties of a piece of string (tied to a fixed position at each end) are familiar: the frequencies are inverse proportional to the length of the string, and they consists of a lowest principal frequency together with its integer multiples (overtones). The two-dimensional situation, where we are looking at a vibrating drum or membrane, is much more interesting, because the geometry of the vibrating region becomes relevant.

- We introduce the resonance frequencies of a region in the plane, with emphasis on the lowest one (the principal frequency).
- We compute the principal frequency for rectangles and equilateral triangles.

(9a) **Definition.** Take a region U of the plane. It should be of bounded size, meaning not go out to infinity. It should also consist of a single piece, not several disconnected ones. We include the boundary as part of U. This boundary can be straight-lined (polygonal) or curved. Take the Laplace operator, which applied to a function f of (x, y) is

$$(9.1) \Delta f = \partial_x^2 f + \partial_y^2 f.$$

A number  $\lambda > 0$  is called a resonance frequency of U if there is a function

(9.2) 
$$\begin{cases} f: U \longrightarrow \mathbb{R}, \text{ twice differentiable,} \\ f(x,y) = 0 \text{ for all boundary points of } U; \text{ but } f \text{ is not the constant (zero) function,} \\ \Delta f = -\lambda^2 f. \end{cases}$$

These f are called resonance modes. The *principal frequency* is the lowest resonance frequency (the full set of frequencies can be quite complicated, unlike the one-dimensional case).

LEMMA 9.1. The resonance frequencies of a region are unchanged under translations, rotations, and reflections (it is a congruence invariant).

That is pretty straightforward (it's a change of variables that does not affect  $\Delta$ ). Next,

LEMMA 9.2. Scaling up a region (in both directions at once!) by some factor c results in a new region whose resonance frequencies are 1/c times those of the original one.

The definition of the principal frequency as lowest resonance frequency is intuitively nice, but complicated to work with directly. To avoid that, we'll use (but not prove) the following characterization:

THEOREM 9.3. (i) For the principal frequency, there is only one function f satisfying (9.2), up to multiplication by a constant (we call this function the principal mode).

(ii) Among all resonance frequencies, the principal frequency is the only one for which the function f is either  $\geq 0$  on all of U, or  $\leq 0$  on all of U (one can switch signs by multiplying it with a negative constant); any other resonance mode has both positive and negative values.

Part (i) has an interesting consequence: whatever symmetries U might have, are inherited by the principal mode f. Part (ii) is useful because, if we find a function  $f \geq 0$  (or  $f \leq 0$ ) which satisfies (9.2) for some  $\lambda$ , then  $\lambda$  must be the principal frequency.

Example 9.4. Let  $U = \{0 \le x \le a, 0 \le y \le b\}$  be a rectangle of size  $a \times b$ . Because it's an interval in both x and y directions, it makes sense to try to combine the trig functions that one sees in the theory of the one-dimensional vibrating string. With this and the general requirements as motivation, it is not impossible to come up with the function

$$(9.3) f(x,y) = \sin(\pi x/a)\sin(\pi y/b),$$

which satisfies:

- f(x,y) = 0 on the boundary of the rectangle;
- $f(x,y) \ge 0$  everywhere in the rectangle;
- $\Delta f = -(\pi^2/a^2 + \pi^2/b^2)f$ .

The first and third property show that it's a resonance mode. The second property, thanks to (ii) in the previous theorem, shows that's the principal mode. Therefore, the principal frequency of our rectangle is

$$\lambda = \pi \sqrt{\frac{1}{a^2} + \frac{1}{b^2}}.$$

EXAMPLE 9.5. Take the equilateral triangle U with side length 1. In coordinates, let's say this is the triangle with vertices (0,0), (1,0),  $(\frac{1}{2},\frac{1}{2}\sqrt{3})$ . I pull the following function out of my ass,

$$(9.5) f(x,y) = \sin\left(\frac{4\pi}{\sqrt{3}}y\right) + \sin\left(2\pi x - \frac{2\pi}{\sqrt{3}}y\right) + \sin\left(-2\pi x - \frac{2\pi}{\sqrt{3}}y\right).$$

This satisfies:

- f(x,y) = 0 zero on the boundary of the triangle;
- $f(x,y) \ge 0$  everywhere in the triangle;

The first two properties can be seen just by having the computer plot it:

The third one is a differentiation exercise. As before, it follows that we have found the principal mode and hence principal frequency. It is maybe best to scale up the conclusion to any size: the

principal frequency of an equilateral triangle of side-length l is

$$\lambda = \frac{4}{\sqrt{3}}\pi l^{-1}.$$

(9b) The reflection principle. There should be a better way to motivate the function f we've found for the triangle, and in fact there is. This method applies exactly to the shapes whose reflections tile the plane, which we've seen before. Moreover, those are the only shapes where an exact formula for the principal frequency is known!

Let's start with the principal mode f for the equilateral triangle. We enlarge the triangle by reflecting along the x-axis. On the diamond-shape formed by the triangle and its reflection, we consider the function

(9.8) 
$$F(x,y) = \begin{cases} f(x,y) & y \ge 0, \\ -f(x,-y) & y \le 0. \end{cases}$$

f(x,-y) is what one gets from f(x,y) by applying reflection to the domain of the function. We are doing that and simultaneously changing sign. The change ensures that the function F is nice: continuous, differentiable, and in fact twice differentiable. Think about it like this: on the axis y=0, the derivatives  $\partial_x F=0$  and  $\partial_x^2 F=0$  because the function is zero for all x; the derivatives  $\partial_y F$  and  $\partial_x \partial_y F$  also exist, as one can see by differentiating f(x,y) and -f(x,-y) (here's where the sign change comes in); and finally,  $\partial_y^2 F$  exists because, by the property of f being a principal mode, we have  $\partial_y f = -\partial_x^2 f - \lambda^2 f$ , and that carries over to -f(x,-y).

One can keep on reflecting until the copies tile the entire plane, you've seen this before! Each time we do that, we carry over the function to the reflected copy and simultaneously change signs, which in the end yields

$$(9.9) F: \mathbb{R}^2 \longrightarrow \mathbb{R}.$$

We call this the function obtained by unfolding the original f. The definition of F graphically looks like this, where the orientation of the  $\pm f$  reflects how the triangles are reflected copies of the original one, as in (6.10):

Let's clean up our story a little bit. Remember that the principal mode inherits all the symmetries of the original shape. In our case, this means that the function f is invariant under 120° rotations

and under reflection that exchange two sides of the triangle. Because of that, we can also just draw the picture like this:

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

You'll now see many translated copies of the same f. This shows that the function F on the plane has the following periodicity properties:

(9.12) 
$$F(x+1,y) = F(x,y),$$
$$F(x+\frac{1}{2},y+\frac{1}{2}\sqrt{3}) = F(x,y).$$

Of course, alongside those, it also has the property inherited from f,

$$(9.13) \Delta F = -\lambda^2 F.$$

At this point, we turn the argument around: we think generally of functions F with the properties we have just written down, and try to see if we can use that to produce the fundamental mode as the restriction of such a function to the triangle. There is an easy class of trigonometric functions that satisfy (9.13). Namely, given some  $v = (c, d) \in \mathbb{R}^2$ , define

(9.14) 
$$S_v = \sin(2\pi v \cdot (x, y)) = \sin(2\pi (cx + dy)),$$
$$C_v = \cos(2\pi v \cdot (x, y)) = \cos(2\pi (cx + dy)).$$

These satisfy

(9.15) 
$$\Delta S_v = -4\pi^2 ||v||^2 S_v = -4\pi^2 (c^2 + d^2) S_v,$$
$$\Delta C_v = -4\pi^2 ||v||^2 C_v = -4\pi^2 (c^2 + d^2) C_v.$$

In order for  $C_v$  and  $S_v$  to have the same periodicity as in (9.12), we need v to satisfy

$$(9.16) v \cdot (1,0) \in \mathbb{Z}, \quad v \cdot (\frac{1}{2}, \frac{\sqrt{3}}{2}) \in \mathbb{Z}.$$

The allowed v form a hex grid (not to be confused with the previous pictures!)

We have marked out the 6 black dots which are at distance  $\frac{2}{\sqrt{3}}$  from the origin. To these points correspond 6 functions  $C_v$  or  $S_v$ . All of them satisfy (9.15) with the same  $||v||^2 = \frac{2}{3}$ . Each of those  $S_v(x,y)$  separately is zero on one of the sides of the triangle, so to get something that's

zero on all three sides, we need to combine them in some way that causes useful cancellations. Here's how to do it:

$$(9.18) F = S_{(0,\frac{2}{\sqrt{3}})} + S_{(1,-\frac{1}{\sqrt{3}})} + S_{(-1,-\frac{1}{\sqrt{3}})},$$

and that is indeed the function (9.5) we came up with before.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 10. An extremal characterization

Resonance frequencies and resonance modes are visibly akin to eigenvalues and eigenvectors. It's time to make use of this relation.

- Based on an idea from linear algebra, we explain an easy way to get an upper bound on the principal frequency from any choice of "test function". One can refine this by using several test functions, and the bounds become pretty good!
- Besides the practical computational aspect, this approach also establishes a number of interesting properties of the principal frequency.

(10a) The Rayleigh quotient. An  $n \times n$  matrix A is called symmetric if  $A_{ij} = A_{ji}$ . In other words, A is equal to its transpose  $A^t$ . Given such a matrix, we look at the Rayleigh quotient

$$\frac{w \cdot Aw}{w \cdot w}, \ \ w \neq 0.$$

If we restrict to vectors of length one, then this is just  $w \cdot Aw$ . The quotient extends it to all nonzero vectors, so that it has the same value on any multiple of w. One can think of it as a function on the sphere (two-dimensional sphere if n=3), and as such, it has to achieve a minimum and maximum somewhere. What's important is that these values have meaning, in terms of the eigenvectors w of A, which are vectors that satisfy

(10.2) 
$$Aw = \mu w$$
 for some  $\mu \in \mathbb{R}$ , called the eigenvalue.

THEOREM 10.1. The minimal value of (10.1) is the lowest eigenvalue of A, and the vectors w that achieve that value are the corresponding eigenvectors. (There's a corresponding result for the maximum, but we won't be using it.)

By turning the logic of the argument around, we can get upper bounds on the lowest eigenvalue:

Corollary 10.2. Let  $\mu$  be the smallest eigenvalue of A. Then

(10.3) 
$$\mu \le \frac{w \cdot Aw}{w \cdot w} \quad \text{for all nonzero vectors } w.$$

Moreover, if equality holds, then w is an eigenvector for  $\mu$ .

Back to principal frequencies!

THEOREM 10.3. Let  $\lambda$  be the principal frequency of a region U. Then

(10.4) 
$$\lambda^2 \le \frac{\int_U \|\nabla f\|^2}{\int_U f^2}$$

for any function  $f: U \to \mathbb{R}$  which is zero on the boundary of U, but not altogether zero. Equality holds exactly when f is the resonance mode corresponding to  $\lambda$ .

(10b) Applications. The theorem above is quite easy to use: you can stick in any f as a "test function", and get an upper bound for the principal frequency.

Example 10.4. Look at the disc of radius 1 (centered at the origin). We can use any function f in (10.4) to get an upper bound for its principal frequency. Let's make a guess and take

$$(10.5) f(x,y) = 1 - x^2 - y^2,$$

which has  $\|\nabla f\|^2 = 4(x^2 + y^2)$ . We can compute the necessary integrals in radial coordinates,

(10.6) 
$$\int_{U} \|\nabla f\|^{2} = \int_{0}^{1} (2\pi r) 4r^{2} dr = 2\pi, \quad \int_{U} f^{2} = \int_{0}^{1} (2\pi r) (1 - r^{2})^{2} dr = \pi/3.$$

We therefore get a bound  $\lambda \leq \sqrt{6} = 2.449...$  for the principal frequency.

The test function idea also has theoretical payoff:

COROLLARY 10.5. Suppose that we have two regions with  $U \subset V$ . Then the principal frequency of U is greater than or equal to the principal frequency of V; meaning,  $\lambda_U \geq \lambda_V$ .

To explain the argument, we need to clarify what test functions f can appear in Theorem 10.3: any function that's continuous on U, piecewise differentiable, and whose derivatives are continuous on each piece, is allowed. This allows us to integrate both  $f^2$  and  $\|\nabla f\|^2$ , so the formula (10.4) makes sense. Now let's get back to  $U \subset V$ . We write  $\lambda_U$  and  $\lambda_V$  for their principal frequencies, and  $f_U$  for the principal mode of U. Let's extend  $f_U$  by zero over the rest of V, and call the result  $f_V$ . Of course,  $f_V$  is not the principal mode of V, but it does satisfy the conditions we've mention. Therefore,

(10.7) 
$$\lambda_V^2 \le \frac{\int_V \|\nabla f_V\|^2}{\int_V f_V^2} = \frac{\int_U \|\nabla f_U\|^2}{\int_U f_U^2} = \lambda_U,$$

and that's all there is to it.

Example 10.6. Take again the disc of radius 1. It contains a square of side-length  $\sqrt{2}$ , and is contained in a square of side-length 2. We know that the principal frequency of an l by l square is  $\pi\sqrt{2}l^{-1}$ . For the principal frequency  $\lambda$  of the disc, we get

$$(10.8)$$

The upper bound is much cruder than what we got from our previous test function, but the lower bound  $\pi\sqrt{1/2} = 2.221...$  is new.

(10c) Explaining the theorem. Take functions f and g on U. Green's theorem, applied to the vector field  $(f\partial_y g, -f\partial_x g)$ , says that

(10.9) 
$$\int_{U} \partial_{x}(-f\partial_{x}g) - \partial_{y}(f\partial_{y}g) = \int_{U} -f\Delta g - \nabla f \cdot \nabla g = \text{some integral over the boundary of } U.$$

If f is zero on the boundary of U, then the boundary term becomes zero, which means

(10.10) 
$$\int_{U} -f\Delta g = \int_{U} \nabla f \cdot \nabla g.$$

Using that, one can rewrite the quotient in the theorem above as

$$\frac{\int_{U} -f \cdot \Delta f}{\int_{U} f^{2}}.$$

If f is any resonance mode, then  $\Delta f = -\lambda^2 f$  for the corresponding frequency  $\lambda$ , and so the quotient is just  $\lambda^2$ . This explains why, if we take f to be the principal resonance mode, we get the principal frequency. This, together with the linear algebra analogy (where  $-\Delta$  plays the role of A), is as far as we'll get in explaining why Theorem 10.3 holds.

(10d) Using more than one test function. We can use any test function to get an upper bound on the principal frequency, but depending on how good we are at picking the function, the bound might be more or less useful. Here's a more systematic way of applying the idea. Choose functions  $f_1, \ldots, f_n$  on U, each of which is zero on the boundary. We are looking for a test function which is a linear combination of them,

(10.12) 
$$f = w_1 f_1 + \dots + w_n f_n$$
, where  $w = (w_1, \dots, w_n) \in \mathbb{R}^n$  can be any nonzero vector.

For the fundamental frequency, we get

(10.13) 
$$\lambda^{2} \leq \frac{\int_{U} \|\nabla f\|^{2}}{\int_{U} f^{2}} = \frac{\sum_{i,j=1}^{n} A_{ij} w_{i} w_{j}}{\sum_{i,j=1}^{n} B_{ij} w_{i} w_{j}} = \frac{w \cdot Aw}{w \cdot Bw},$$

where

(10.14) 
$$A_{ij} = \int_{U} \nabla f_i \cdot \nabla f_j, \quad B_{ij} = \int_{U} f_i f_j.$$

Our job is then to pick w so that the quotient (10.13) becomes as small as possible, so that we get the best bound for  $\lambda^2$ . Luckily, there's a linear algebra theorem for that, which generalizes the one from the start of the lecture:

THEOREM 10.7. Let A and B be symmetric matrices of size n. We also require that B is positive, in the sense that  $w \cdot Bw > 0$  for all nonzero  $w \in \mathbb{R}^n$ . Then, the minimum of the quantity

$$\frac{w \cdot Aw}{w \cdot Bw}, \ w \in \mathbb{R}^n \ nonzero,$$

is the lowest eigenvalue of  $B^{-1}A$ .

In case you don't like eigenvectors, the eigenvalues of  $B^{-1}A$  are also the roots of the polynomial  $p(t) = \det(tB - A)$ . Let's summarize the outcome:

COROLLARY 10.8. Pick functions  $f_1, \ldots, f_n$  on U, each of which is zero on the boundary, and compute the associated matrices A and B. Then the principal frequency  $\lambda$  satisfies

(10.16) 
$$\lambda^2 < any \ root \ of \ p(t) = \det(tB - A).$$

EXAMPLE 10.9. Let's return to the disc, with the repertoire of functions  $f_1 = 1 - x^2 - y^2$ ,  $f_2 = f_1^2$ ,  $f_3 = f_1^3$ . After computing all the required integrals and the determinant (all of which we skip here), one gets

(10.17) 
$$\det(tB - A) = \pi^3 (t^3 / 378000 - t^2 / 2520 + 2t / 175 - 4 / 75),$$

which has its smallest root at t = 5.783... This gives us a bound  $\lambda \leq \sqrt{t} = 2.404...$ , a big improvement over Example 10.4 (the four digits we've written down actually agree with the value of  $\lambda$ , computed numerically by other means).

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 11. Symmetrization

Symmetrization is a process that takes a region and some straight line (the axis), and produces a new region that's symmetric with respect to that axis.

- We define symmetrization, and explore its effect on area and perimeter. This is elementary geometry!
- We discuss some examples, including an in-depth look at symmetrization of triangles.
- Finally, returning to the principal frequency, symmetrization provides inequalities between the principal frequencies of different regions.

(11a) Definition and first properties. Fix a line l in the plane. Given a region U, symmetrization with respect to the axis l works as follows. Take any line  $l^{\perp}$  perpendicular to l, look at the total length of  $U \cap l^{\perp}$ , and draw the open interval of the same length inside  $l^{\perp}$  centered on the point  $l \cap l^{\perp}$ . The union of those intervals, for all  $l^{\perp}$ , is the symmetrization of U, written as  $S_l(U)$ . It is a new region, symmetric with respect to l. The easiest situation is when U is convex, in which case  $U \cap l^{\perp}$  consists of a single interval. Then, we just slide the interval along  $l^{\perp}$  until it becomes symmetric with respect to l, and apply the same to all  $l^{\perp}$  to form  $S_l(U)$ . In the non-convex case, one may have to merge several intervals into one, but the idea is the same.

Example 11.1. Take a triangle. Mostly, if we symmetrize it, we get a kite (a quadrilateral which is symmetric with respect to reflection along one diagonal):

The exception to "mostly" is symmetrization with respect to an altitude, which gives another triangle (necessarily an isosceles one, because of the symmetry):

Example 11.2. Take a circular strip, lying between two concentric circles. In this case, when we symmetrize, we have to merge pairs of intervals. This looks as follows:

In formulae, we would have

(11.4) 
$$U = \{c \le \sqrt{x^2 + y^2} \le d\},$$
$$S_l(U) = \{c \le |x| \le d, |y| \le \sqrt{d^2 - x^2}\} \cup \{|x| \le c, |y| \le \sqrt{d^2 - x^2} - \sqrt{c^2 - x^2}\}.$$

LEMMA 11.3. The area of  $S_l(U)$  is the same as that of U.

This is due to the definition of area as integral of the function that gives the lengths of  $l \cap l^{\perp}$  (Cavalieri's principle of indivisibles if you're historically minded, or Fubini's theorem for the analytically informed).

Theorem 11.4. The perimeter of  $S_l(U)$  is less or equal than the perimeter of U.

Let's look at the situation (not the most general one, but close enough) familiar from calculus, where U is the region between two graphs f(x) and g(x),

(11.5) 
$$U = \{ a \le x \le b, \ f(x) \le y \le g(x) \}.$$

Here, we're assuming  $f(x) \leq g(x)$ , and that f(a) = g(a), f(b) = g(b). The perimeter of U is then just the sum of the lengths of the two graphs,

(11.6) 
$$\int_{a}^{b} \sqrt{1 + f'(x)^2} + \sqrt{1 + g'(x)^2} \ dx.$$

Let's symmetrize with respect to the x-axis,

(11.7) 
$$S_l(U) = \{ a \le x \le b, \ |y| \le \frac{1}{2} (g(x) - f(x)) \}.$$

This is the region between the graph of  $\frac{1}{2}(f(x) - g(x))$  and  $\frac{1}{2}(g(x) - f(x))$ , so we have a similar formula for the perimeter,

(11.8) 
$$\int_{a}^{b} 2\sqrt{1 + \frac{1}{4}(g'(x) - f'(x))^2} \ dx.$$

The claim is that the integrand here is less or equal than that in the previous formula. If we write F = f'(x), G = g'(x), then what we need is

(11.9) 
$$2\sqrt{1+(G-F)^2/4} \le \sqrt{1+F^2} + \sqrt{1+G^2}.$$

This inequality holds for all numbers F and G. One can prove it by squaring repeatedly and cleaning up terms, which we'll leave to you.

(11b) Isosceles triangles. As discussed before, if we take a triangle and symmetrize it with respect to an altitude, we get another triangle, which is always isosceles. What if we already start with an isosceles triangle, let's call it T? One of its altitudes is the axis of symmetry, so symmetrizing with respect to that changes nothing. Let's symmetrize with respect to one of the two other altitudes, and call this process altitude symmetrization S(T). (Up to congruence, it doesn't matter which of the two altitudes you pick.)

LEMMA 11.5. Take an isosceles triangle which is not equilateral. If we apply altitude symmetrization to it, then the new triangle has smaller perimeter than the old one.

This is an elementary geometry exercise, which we'll skip. Let's look generally at the perimeters of isosceles triangles. For simplicity, we use triangles with area  $\sqrt{3}/4$ , so that the equilateral one has side-length 1. An isosceles triangle with are  $\sqrt{3}/4$  and base b has height h (measured with respect to the base) and perimeter

$$(11.11) p = b + 2\sqrt{(b/2)^2 + h^2} = b + \sqrt{b^2 + 4h^2} = b\left(1 + \sqrt{1 + \frac{3}{h^4}}\right).$$

Let's look at the function p = p(b):

It has an absolute minimum p(1) = 3 corresponding to the equilateral triangle. For every p > 3, there are exactly two values b with p(b) = p. This has the following consequence:

THEOREM 11.6. Start with any isosceles triangle, and apply altitude symmetrization over and over. The result is a sequence of isosceles triangles, which either turns equilateral after finitely many steps, or else becomes closer and closer to equilateral in the limit.

PROOF. As before, we just discuss triangles with area  $\sqrt{3}/4$ . One can scale the discussion up and down to any area. As the theorem says, it's an option to get an equilateral triangle after finitely many steps. If that's not the case, then by our previous Lemma, we get a sequence of triangles with bases  $b_1, b_2, b_3, \dots > 0$  and perimeters  $p_1, p_2, p_3, \dots > 3$ , with

$$(11.13) p_1 > p_2 > p_3 > \cdots$$

If the limit of those  $p_n$  is 3, then by looking at the graph of the function, we see that the limit of the  $b_n$  must be 1, so we are converging to an equilateral triangle. What if the limit of the  $p_n$  is some number p > 3? To that number correspond two values of b, meaning two isosceles triangles. Because of the limiting process, at least one of those two must have the property that its perimeter doesn't decrease under isosceles symmetrization, which contradicts our Lemma. So p > 3 is after all impossible!

(11c) Back to the principal frequency. With respect to symmetrization, the principal frequency behaves like the perimeter:

THEOREM 11.7. The principal frequency of  $S_l(U)$  is less or equal than that of U.

The theorem is proved using the minimizing idea from the previous lecture: one takes a test function f on U, and produces another function  $S_l(f)$  on  $S_l(U)$ , such that

(11.14) 
$$\int_{S_l(U)} S_l(f)^2 = \int_U f^2, \quad \int_{S_l(U)} \|\nabla S_l(f)\|^2 \le \int_U \|\nabla f\|^2.$$

Obviously, the gap in this explanation is the definition of  $S_l(f)$ , and why it has those properties. There are geometric ways to understand this, which are quite similar to our discussion of the behaviour of the perimeter, but we prefer not to get into that discussion here. It's the consequences which make this fact interesting.

Example 11.8. Take an  $a \times b$  rectangle, rotated by some angle  $\alpha$ . We assume that the angle of rotation is small enough so that the x-axis still passes through the b-side, and symmetrize with respect to that axis.

$$(11.15) \qquad \qquad b \qquad \qquad a$$

The outcome is a hexagon symmetric with respect to the x-axis, and also with respect to rotation by  $180^{\circ}$ . It has the following measurements:

$$(11.16) \qquad \qquad \frac{b}{\cos(\alpha)}$$

$$b\sin(\alpha)$$

Therefore, if we take a, b and  $\alpha$  so that  $b\sin(\alpha) = \frac{1}{2}$ ,  $b/\cos(\alpha) = \sqrt{3}$ ,  $a\cos(\alpha) = \frac{3}{2}$ , the symmetrized shape is a regular hexagon with side-length 1. The quotient of the first two equations says that  $\sin(2\alpha) = 2\sin(\alpha)\cos(\alpha) = 1/\sqrt{3}$ , and with that at hand, one can calculate everything. For the fundamental frequency of the hexagon, this yields a reasonably good bound (much better than what one gets from putting a rectangle inside the hexagon)

(11.17) 
$$\lambda \le \pi \sqrt{\frac{1}{a^2} + \frac{1}{b^2}} = \frac{2\pi}{3} \sqrt{5 - \frac{4}{3}\sqrt{6}} = 2.75794\dots$$

As a more serious application, suppose that we start with a triangle. By repeated symmetrization as in our previous discussion, we can turn it into a triangle which is either equilateral or very very close to it. In the latter case it contains a slightly smaller equilateral triangle, and is contained in a slightly larger equilateral one, so the fundamental frequency is very close to that of the equilateral one, and we can actually make the error as small as we want. So we've proved this:

COROLLARY 11.9. Among all triangles with a given area, the equilateral one achieves the minimum of the principal frequency.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

96 IV. LOOPS

## 12. Smooth loops

We look at smoothly curved loops in the plane. This is the curvy analogue of our previous study of polygonal loops. The basic ideas are similar, but the techniques involved in realizing them are different.

- We define the winding number of a smooth loop around a point, by an integral formula.
- We discuss properties of winding numbers, with emphasis on deformation invariance.

(12a) **Definition.** Take functions x(t) and y(t), defined for  $t \in \mathbb{R}$  and which have derivatives of all orders (these are usually called smooth functions), together with a T > 0 such that both functions are T-periodic:

(12.1) 
$$x(t+T) = x(t), y(t+T) = y(t)$$
 for all t.

We then call the parametrized curve  $c(t) = (x(t), y(t)) \in \mathbb{R}^2$  a smooth loop. Note that the choice of T is part of the definition of a smooth loop: for instance,  $c(t) = (\cos(t), \sin(t))$ , we could take  $T = 2\pi$  (loop goes once around the circle) or  $T = 4\pi$  (loop goes twice around the circle).

EXAMPLE 12.1. Even though the loop is smooth as a parametrized curve, the shape in the plane it traces out can appear non-smooth, at those points where the speed of c(t) becomes zero. For instance, take  $x(t) = \cos(t) - \cos(2t)/2$ ,  $y(t) = \sin(t) - \sin(2t)/2$ . With  $T = 2\pi$ , this is a smooth loop, and looks like this:

At the point t = 0, we have  $x'(t) = -\sin(t) + \sin(2t) = 0$  and  $y'(t) = -\cos(t) + \cos(2t) = 0$ , and that's where the kink happens.

Take two smooth loops  $c_0(t)$  and  $c_1(t)$ , and let's say that they both have period T. A deformation of  $c_0$  into  $c_1$  is given by  $c_s(t) = (x(s,t), y(s,t))$ , for  $s \in [0,1]$  and  $t \in \mathbb{R}$ , such that x(s,t) and y(s,t) are arbitrarily often differentiable, and the periodicity condition is preserved throughout:

$$(12.3) x(s,t+T) = x(s,t), y(s,t+T) = y(s,t).$$

Here,  $s \in [0, 1]$  is an auxiliary parameter; for s = 0, 1 we get our original two loops, and  $c_s$  for general s yields a family of smooth loops which gradually interpolate between them.

EXAMPLE 12.2. Even though the deformation is smooth, the loops can appear to change shape. For example, take  $x(s,t) = \cos(t) - s\cos(2t)$ ,  $y(s,t) = \sin(t) - s\sin(2t)$ , which is certainly a

smooth deformation. For s = 1/2 that gives the previous example. When we cross that parameter value, a small curl appears in the loop:

FACT 12.3. Any two smooth loops (with the same T) can be deformed into each other.

One simply moves from  $c_0(t)$  to  $c_1(t)$  by a straight line segment, which means setting

$$(12.5) c_s(t) = c_0(t) + s(c_1(t) - c_0(t)) = (1 - s)c_0(t) + sc_1(t).$$

This seems to say that deformation isn't very interesting. Which is true: that notion only becomes worth while talking about if we put additional restrictions on what deformations are allowed.

Nrom now, we'll gradually dinish our use of "smooth"; all loops that occur are intended to be smooth ones, so this word isn't really necessary.

(12b) Winding numbers. Let c be a smooth loop, and  $q \in \mathbb{R}^2$  a point not lying on that loop. The winding number of c around q is defined as

(12.6) 
$$\operatorname{wind}(c,q) = \frac{1}{2\pi} \int_0^T \frac{(c(t) - q) \times c'(t)}{\|c(t) - q\|^2} dt.$$

One can write the formula more symmetrically as

(12.7) 
$$\operatorname{wind}(c,q) = \frac{1}{2\pi} \int_0^T \frac{c(t) - q}{\|c(t) - q\|} \times \frac{d}{dt} \left( \frac{c(t) - q}{\|c(t) - q\|} \right) dt.$$

It may look as if this can't possibly equivalent to the previous expression, because

(12.8) 
$$\frac{d}{dt}\frac{c(t)-q}{\|c(t)-q\|} = \frac{c'(t)}{\|c(t)-q\|} + (c(t)-q)\frac{d}{dt}\left(\frac{1}{\|c(t)-q\|}\right),$$

and the second term has no counterpart in (12.6). The answer to that quandary is that the term in question is a scalar multiple of c(t) - q, hence contributes zero if we take the cross product with that vector.

To see what the integral formula means geometrically, let's write a smooth loop in polar coordinates centered at q,

$$c(t) = q + r(t)(\cos\theta(t), \sin\theta(t)).$$

Then  $(c(t) - q)/\|c(t) - q\| = (\cos \theta(t), \sin \theta(t))$ , and the winding number integral is

$$(12.10) \qquad \frac{1}{2\pi} \int_0^T \begin{pmatrix} \cos\theta(t) \\ \sin\theta(t) \end{pmatrix} \times \begin{pmatrix} -\sin\theta(t) \\ \cos\theta(t) \end{pmatrix} \theta'(t) dt = \frac{1}{2\pi} \int_0^T \theta'(t) dt = \frac{1}{2\pi} (\theta(T) - \theta(0)).$$

98 IV. LOOPS

When we write (12.9), we want r(t) and  $\theta(t)$  to vary continuously with t. That requirement may force us to choose  $\theta(t)$  not to be periodic: from the ambiguity of polar coordinates, we know that the values  $\theta(t)$  and  $\theta(t+T)$  can differ by an integer multiple of  $2\pi$ . Our computation shows that this multiple is the winding number, as defined by the integral formula:

(12.11) 
$$\theta(t+T) = \theta(t) + 2\pi \operatorname{wind}(c, q).$$

This shows that the integral is always an integer. More importantly, it exactly reproduces the original intuition of counting the number of turns we have to do, while standing at q and looking towards the point c(t) as it moves around the loop.

- (12c) Properties of the winding number. The computational techniques that we have learned in the polygonal case carry over to smooth loops. For instance, the ray-cutting formula works as follows. Take a ray going from q to infinity, in direction w, such that:
- (12.12) Wherever that ray meets c(t), the vectors w and c'(t) are linearly independent.

(This means that the ray crosses our loop transversally.) Then,

(12.13) 
$$\operatorname{wind}(c,q) = \sum_{\substack{\text{those } t \in [0,T) \text{ such} \\ \text{that } c(t) \text{ lies on the ray}}} \operatorname{sign}(w \times c'(t)).$$

Example 12.4. Look at  $c(t) = (\cos(5t), \sin(3t))$ , with  $T = 2\pi$ . We are interested in the winding number around the origin o (which our loop avoids). Take a horizontal ray going to the right, which means w = (1,0). This hits our loop at those times t such that

$$\sin(3t) = 0, \ \cos(5t) > 0.$$

In the interval  $[0, 2\pi)$ , those times are t = 0,  $t = \pi/3$ ,  $t = 5\pi/3$  (because  $\cos(0) = 1$  and  $\cos(5\pi/3) = \cos(25\pi/3) = \frac{1}{2}$ ). We have

(12.15) 
$$w \times c'(t) = (1,0) \times (-6\sin(5t), 3\cos(3t)) = 3\cos(3t) \begin{cases} 3 & t = 0, \\ -3 & t = \pi/3, \\ -3 & t = 5\pi/3. \end{cases}$$

Therefore wind(c, o) = 1 - 1 - 1 = -1. Of course, if we took a different ray, the number of intersection points could be different, but the total contribution would remain the same. Here's a picture of the loop so that you can check the computation visually:

PROPOSITION 12.5. Take two smooth loops  $c_0, c_1$  (with the same T) which avoid q. If they can be deformed into each other without ever passing through q, which means that all  $c_s$  avoid q, then wind  $(c_0, q) = \text{wind}(c_1, q)$ .

We've seen the relevant kind of argument before: from the integral formula, one sees that  $\operatorname{wind}(c_s,q)$  varies continuously with s. But we also know it's an integer, so it must be constant in s. Deformation invariance is frequently applied like this: the winding number doesn't change if we "wiggle the loop a little", since the original loop and the wiggled one can be joined by a deformation without crossing q. How much we're allowed to wiggle depends on how far the original loop was from the point q that we're computing the winding number for. Here is an explicit criterion:

COROLLARY 12.6. (Man-dog-lamppost theorem) Suppose that  $c_0, c_1$  are smooth loops (with the same period T), and q a point, such that

(12.17) 
$$||c_1(t) - c_0(t)|| < ||c_0(t) - q||$$
 for all  $t$ .

Then wind $(c_0, q) = \text{wind}(c_1, q)$ .

Here,  $c_0$  is the original loop, and  $c_1$  is the wiggled one. To prove the equality of winding numbers, we use the straight-line deformation  $c_s$ ,  $0 \le s \le 1$ , from (12.5). The important thing is that  $c_s(t)$  never becomes equal to q. This is geometrically intuitive, or one can argue by contradiction:

(12.18) 
$$c_s(t) = q \implies c_0(t) - q = s(c_1(t) - c_0(t)) \implies ||c_0(t) - q|| = s||c_1(t) - c_0(t)||$$
$$\implies ||c_0(t) - q|| \le ||c_1(t) - c_0(t)||, \text{ which is impossible.}$$

Example 12.7. We'll compute the winding number of

(12.19) 
$$c_1(t) = (\cos(3t) + \cos(5t)/10, \sin(3t) + \sin(5t)/10), \quad (T = 2\pi),$$

around the origin o. Our loop can be seen as a slight wiggle on  $c_0(t) = (\cos(3t), \sin(3t))$ , which goes three times around a circle. Quantitatively,  $||c_0(t) - o|| = ||(\cos(3t), \sin(3t))|| = 1$ , while  $||c_1(t) - c_0(t)|| = ||(\cos(5t)/10, \sin(5t)/10)|| = 1/10$ . By man-dog-lamppost, wind $(c_1, 0) = \sin(c_0, 0) = 3$ .

The name can help you remember what's going on. The idea is that  $c_0(t)$  is the position of a man walking in a smooth loop, around a lamppost q. The man is holding a dog on a leash: the position of the dog is  $c_1(t)$ , and the length of the leash is  $||c_1(t) - c_0(t)||$ . If the leash remains shorter than the distance from the man to the lamppost, which is  $||c_0(t) - q||$ , the leash can't get tangled around the lamppost. Therefore, after getting back to their starting positions, the man and the dog have circled the lamppost the same amount of times.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

104 IV. LOOPS

## 13. Equations in two variables

Maybe surprisingly, winding numbers can be used to prove existence results for solutions of systems of equations (two equations in two variables).

- Given such a system, and a prospective region where a solution could be located, one constructs an appropriate smooth loop. If that loop has nonzero winding number, the system must have at least one solution in our region. (This is similar to how one can use the intermediate value theorem to prove, for instance, that there is an  $x \in (0, \pi/2)$  with  $\cos(x) = x$ .)
- Deformation methods for the winding number, such as man-dog-lamppost, are particularly useful in this context.

(13a) Existence of solutions. Let's start with functions g(a,b) and h(a,b), defined and smooth (have derivatives of any order) for all  $(a,b) \in \mathbb{R}^2$ . We are given (x,y), and are looking for solutions (a,b) of

(13.1) 
$$g(a,b) = x,$$
$$h(a,b) = y,$$

This is pretty general, g and h can be almost anything! For a more geometric picture, we combine our functions into a map

(13.2) 
$$F(x,y) = (g(x,y), h(x,y)) : \mathbb{R}^2 \longrightarrow \mathbb{R}^2.$$

In your mind, imagine two copies of the plane: that where F is defined, with coordinates (a, b), and that where it takes values, with coordinates (x, y). Then, if q = (x, y) is given, what we are looking for in (13.1) are p = (a, b) such that F(p) = q. Fix some r > 0, take the circle  $c(t) = (r\cos(t), r\sin(t))$  of radius r around the origin (a loop with  $T = 2\pi$ ), and look at its image under F:

$$d(t) = F(c(t)) = F(r\cos(t), r\sin(t)) = (g(r\cos(t), r\sin(t)), h(r\cos(t), r\sin(t))).$$

We'll be interested in the winding number of d around our chosen point q. Of course, for that to be defined, we have to assume that d(t) never becomes equal to q: in other words, there shouldn't be any solutions of F(p) = q on the circle ||p|| = r.

THEOREM 13.1. Suppose that wind $(d,q) \neq 0$ . Then there must be a

(13.4) 
$$p \in \mathbb{R}^2 \text{ with } ||p|| < r, \text{ which solves } F(p) = q.$$

PROOF. Look at the deformation obtained by shrinking the circle in the (a, b) plane, depending on a parameter  $s \in [0, 1]$ :

(13.5) 
$$c_s(t) = (sr\cos(t), sr\sin(t)),$$
$$d_s(t) = F(c_s(t)) = F(sr\cos(t), sr\sin(t)).$$

At one end,  $d_0(t) = F(0,0)$  is the constant path. At the other end,  $d_1(t) = d(t)$  is the path from our statement. The proof is by contradiction. Suppose that there is no solution (13.4). This implies that all loops  $d_s$  avoid q. By deformation invariance of the winding number, one would have wind $(d_0, q) = \text{wind}(d_1, q)$ . But  $d_0$  is a constant path, and therefore its winding numbers are 0, which is a contradiction.

Example 13.2. We want to show that there's a solution  $(a,b) \in \mathbb{R}^2$  of

(13.6) 
$$a - \cos(a + b^4) = 0,$$
$$b - \cos(ab) = 0,$$

so 
$$F(a,b)=(a-\cos(a+b^4),b-\cos(ab))=(a,b)-(\cos(a+b^4),\cos(ab))$$
. The relevant loop is

(13.7) 
$$d(t) = (r\cos(t), r\sin(t)) - (\cos(r\cos(t) + r^4\sin(t)^4), \cos(r^2\cos(t)\sin(t))).$$

To see whether our method applies, we need to know wind (d, o), where o = (0, 0) is the origin, and r has been chosen appropriately (we don't yet know how). Looking at (13.7), the two terms have somewhat different sizes:

(13.8) 
$$||(r\cos(t), r\sin(t))|| = r,$$

(13.9) 
$$\|(\cos(r\cos(t) + r^4\sin(t)^4), \cos(r^2\cos(t)\sin(t)))\| < 2;$$

in the second case, this is because both the x and y coordinate lie in [-1,1]. If we choose  $r \ge 2$ , the man-dog-lamppost theorem applies, with  $(r\cos(t), r\sin(t))$  being the man, d(t) the dog, and the lamppost at the origin o = (0,0). The consequence is that

(13.10) 
$$\operatorname{wind}(d, o) = \operatorname{wind}(t \mapsto (r \cos(t), r \sin(t)), o) = 1.$$

It follows that (13.6) has a solution with  $a^2 + b^2 \le 2^2 = 4$ . Note that it's pretty clearly impossible to find the solution explicitly!

Our argument didn't use anything about (13.6) except that one side was just (a, b), and the other side was bounded (13.9). In fact, the same reasoning gives a general statement:

COROLLARY 13.3. Suppose that k(a,b) and l(a,b) are functions (defined on  $\mathbb{R}^2$  and smooth) which are bounded (above and below, with bounds that hold for all a,b). Then, the system of equations

(13.11) 
$$a = k(a, b), b = l(a, b)$$

always has a solution.

(13b) More examples. So far, we have only dealt with cases where the winding number is 1. Let's enlarge our repertoire:

106 IV. LOOPS

Example 13.4. Take  $F(a,b) = (a^2 - 1,b)$ , q = (0,0), and r > 1. The relevant loop is

(13.12) 
$$d(t) = F(r\cos(t), r\sin(t)) = (r^2\cos(t)^2 - 1, r\sin(t)).$$

Let's compute the winding number using the intersect-a-ray approach. Specifically, we look at points where d(t) is a positive multiple of w = (1,0). This happens at t = 0 and  $t = \pi$ , where

(13.13) 
$$d(0) = d(\pi) = (r^2 - 1, 0), \ d'(0) = (0, r), \ d'(\pi) = (0, -r).$$

Therefore,  $d'(t) \times w$  is negative at t = 0 and positive at  $t = \pi$ , which means that the winding number is zero! This may be surprising because we clearly have solutions (a,b) = (-1,0) and (a,b) = (1,0) of F(a,b) = (0,0). This is not a contradiction to our theorem, it just means that the converse implication doesn't hold in general.

(13c) A counting formula. You may have realized that in our context, two numbers appear: first, the winding number; and second, the number of solutions to our system of equations. The existence theorem says that if the first is nonzero, so is the second. That doesn't mean that the two numbers are equal: indeed, we've seen in examples that that's not the case generally; and moreover, such an equality is a priori impossible, as the winding number can be negative, and on the other hand the number of solutions can be infinite. Nevertheless, there is a relation, under certain additional assumptions:

THEOREM 13.5. Look at a loop (13.3). Assume that for every p as in (13.4), the partial derivatives  $\partial F/\partial a$  and  $\partial F/\partial b$ , taken at the point (a,b) = p, are linearly independent vectors. Then

(13.14) 
$$\operatorname{wind}(d,q) = \sum_{p} \operatorname{sign}\left(\frac{\partial F}{\partial a} \times \frac{\partial F}{\partial b}\right).$$

Here, the sum is over all (13.4), and the partial derivatives are taken at those points.

Let's revisit Example 13.4. We have

(13.15) 
$$\frac{\partial F}{\partial a} \times \frac{\partial F}{\partial b} = (2a, 0) \times (0, 1) = 2a,$$

which has opposite signs at (a, b) = (1, 0) and (a, b) = (-1, 0). Hence, the two contributions on the right hand side of (13.14) cancel each other out, which confirms our previous computation wind(d, o) = 0.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 14. Complex polynomials

Given how long we've been talking about the plane, it's surprising that complex numbers haven't appeared so far. We now fix this:

- One can use winding numbers to detect zeros of complex polynomials.
- Unlike the case of real equations, this is an "if and only if" process, and provides a count of how many zeros lie in a disc of radius r, assuming that the zeros are counted with their proper positive multiplicities.

(14a) Complex numbers. A complex number is given by its real and imaginary parts, z = x + iy, hence is the same as a point (x, y) in the plane. One writes |z| instead of ||z|| for its length, meaning

(14.1) 
$$|z| = \sqrt{x^2 + y^2}$$
 for  $z = x + iy$ .

There's a famous formula for trigonometric functions in terms of the complex exponential,

(14.2) 
$$e^{i\theta} = \cos(\theta) + i\sin(\theta).$$

This means that complex numbers are written in radial coordinates as  $z = re^{i\theta}$ . As one sees from that, the product of complex numbers multiplies the radii and adds the angles:

$$(14.3) (r_1e^{i\theta_1})(r_2e^{i\theta_2}) = (r_1r_2)e^{i(\theta_1+\theta_2)}.$$

One can think of smooth loops as taking values in complex numbers, meaning  $c(t) \in \mathbb{C}$ . The simplest example may be the loop

$$(14.4) c(t) = e^{int},$$

with  $T = 2\pi$ , for some integer n. This goes n times around the radius 1 circle (if n is negative, that means clockwise). One can see this directly,  $e^{int} = \cos(nt) + i\sin(nt)$ ; or one can say that  $e^{it}$  goes once around the circle, and then taking the n-th power has the effect of multiplying the angles by n.

(14b) Roots and multiplicities. Take a complex polynomial of degree n:

(14.5) 
$$f(z) = a_n z^n + a_{n-1} z^{n-1} + \dots + a_1 z + a_0, \text{ with } a_n \neq 0.$$

The fundamental theorem of algebra says that we can always write this as

(14.6) 
$$f(z) = a(z - w_1)^{m_1} \cdots (z - w_k)^{m_k},$$

where  $a = a_n$  is the leading coefficient; the roots  $w_i$  are all different from each other; and the multiplicities  $m_i$  are positive integers, whose sum is n. This is a theoretical existence statement, which basically says that f has n zeros once those are counted with the proper multiplicities. If we know w is a root, we can actually compute its multiplicity without writing the polynomial in the form described above:

LEMMA 14.1. The multiplicity of a root w is the smallest m such that the m-th derivative of f at w is nonzero.

112 IV. LOOPS

Example 14.2. Take  $f(z) = z + 3z^2 - 3z^3 + z^4$ , which satisfies f(1) = 0. We compute

$$f'(z) = -1 + 6z - 9z^{2} + 4z^{3}, \quad f'(1) = 0,$$

$$f''(z) = 6 - 18z + 12z^{2}, \qquad f''(1) = 0,$$

$$f'''(z) = -18 + 24z, \qquad f'''(1) = 6 \neq 0,$$

so the multiplicity at 1 is 3.

From now on, we write  $\operatorname{mult}(f, w)$  for the multiplicity of f at w (if w is not a root, one can set that multiplicity to 0).

(14c) The winding number formula. Applying the same idea as in the previous lecture, we look at the image of a circle of radius r > 0 under f, which is the loop (with  $T = 2\pi$ )

(14.8) 
$$d(t) = f(re^{it}) = f(r\cos(t) + ri\sin(t)).$$

Suppose that f has is no root on the circle of radius r around the origin, so that the winding number wind(d,0) is defined. Then:

Theorem 14.3. For a loop (14.8),

(14.9) 
$$\operatorname{wind}(d,0) = \sum_{\substack{|w| < r \\ f(w) = 0}} \operatorname{mult}(f, w),$$

where the sum is over all roots of f lying inside the circle of radius r.

In particular, the winding number is always nonnegative; and it is > 0 if and only if there is a solution of f(w) = 0 inside the circle. This two-way implication is part of the special magic of the class of holomorphic functions, of which polynomials are the simplest examples.

Example 14.4. Take 
$$f(z) = z^5 - z^3 - \frac{1}{2}$$
. The loop  $d(t) = f(e^{it}) = e^{5it} - e^{3it} - \frac{1}{2}$  looks like this:

From that, one reads off the winding number around the origin, wind(d,0) = 3 (the picture doesn't tell you which way the loop goes; but the other direction gives a winding number of -3, which is impossible). This means that we have three possibilities: either there are three solutions of f(p) = 0 with |p| < 1, each having multiplicity 1; or two solutions, with multiplicities 1,2; or a single solution, with multiplicity 3 (in fact, the first is the case, but you can't tell that just from our computation).

EXAMPLE 14.5. Take f(z) = (z+i)(z-i)(z+1)(z-1)(z-1/4). There is one root with |p| = 1/4, and four roots with |p| = 1. All roots have multiplicity 1. Consequently, the winding

number wind(d,0) remains zero for r < 1/4, and then jumps to 1. The jump happens in a relatively simple way, by d moving across the origin:

The winding number remains at that value for 1/4 < r < 1, and then jumps to 5 when crossing r = 1. At that value, four parts of the loop d all pass through the origin simultaneously:

Example 14.6. Take  $f(z)=(z-\frac{1}{2})^3(z-i)$ . This has a root of multiplicity 3 at 1/2, and a root of multiplicity 1 at i. Correspondingly, we expect the winding number to be 0 for r<1/2, then 3 for  $r\in(1/2,1)$ , and finally 4 for r>1. The jump from 0 to 3 comes with a sudden curling behaviour:

(14d) Other values. We have focused on the equation p(z) = 0, but simply by subtracting a constant from p, one can apply the result to equations p(z) = u for an arbitrary complex number u.

COROLLARY 14.7. Take  $d(t) = p(re^{it})$  as before. For every u where it is defined, the winding number wind(p, u) is nonnegative; and it is > 0 if and only if there is a solution of p(z) = u with z inside the circle of radius r.

114 IV. LOOPS

Example 14.8. Take the leftmost picture from Example 14.5, with r = 0.98. We have not drawn that, but the motion of the loop is anticlockwise (meaning, to the left at its topmost point). As a consequence, one can check that the winding numbers are positive for all regions except the outermost infinite region. It follows that for any u lying in those regions, the equation p(z) = u has a solution with |z| < 0.98.

COROLLARY 14.9. Take  $d_1 = p(r_1e^{it})$ ,  $d_2 = p(r_2e^{it})$ , for some  $r_2 > r_1 > 0$ . Then, for every complex number u where both winding numbers are defined, we have

$$(14.14) wind(d_2, u) \ge wind(d_1, u).$$

In other words, as the radius increases, the winding number of our loops around any point can only go up or stay the same; it can never go down.

(14e) Proof. The proof of the theorem is, as usual for loops, by a deformation argument. We write our polynomial as a product, but separating the roots that lie inside and outside the circle of radius r:

(14.15) 
$$f(z) = \left(\prod_{|w_i| < r} (z - w_i)^{m_i}\right) \left(\prod_{|w_i| > r} (z - w_i)^{m_i}\right).$$

Now we introduce a parameter  $s \in [0, 1]$  which changes it like this:

(14.16) 
$$f_s(z) = \left( \prod_{|w_i| < r} (z - sw_i)^{m_i} \right) \left( \prod_{|w_i| > r} (sz - w_i) \right).$$

If  $|w_i| < r$  is a root of f, then  $s|w_i|$  is a root of  $f_s$ . In the second instance, if  $|w_i| > r$  is a root of f, then  $|w_i|/s$  is a root of  $f_s$  (or for s=0, there is no corresponding root). In words, the roots lying inside the circle of radius r move inwards as s becomes smaller, and those lying outside the circle move to infinity. At no time s does  $f_s$  actually have a root on the circle. Therefore, if we define

$$(14.17) d_s(t) = f_s(re^{it}),$$

then wind $(d_s, 0)$  remains the same for all s. For s = 1 we have  $f_1 = f$ , so  $d_1 = d$  is the loop associated to the original polynomial. Now let's see what we get for s = 0:

(14.18) 
$$f_0(z) = \left(\prod_{|w_i| < r} z^{m_i}\right) \left(\prod_{|w_i| > r} (-w_i)^{m_i}\right) = z^m a,$$

where  $m = \sum_{|w_i| < r} m_i$ , and  $a = \prod_{|w_i| > r} (-w_i)^{m_i}$  is a nonzero constant. The associated loop is  $d_0(t) = e^{imt}a$ , which goes m times around the circle of radius |c|. Therefore, wind $(d_0, 0) = m$ . The same is therefore true of wind $(d, 0) = \text{wind}(d_1, 0)$ . Looking at the definition of m, that's exactly what the theorem says!

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 15. The linking number

Mostly, we resist the urge to go off into higher dimensions; this lecture is one of the exceptions.

- Linking numbers are three-dimensional analogues of winding numbers, but the standard way of computing linking numbers involves projecting down to two dimensions.
- One way of defining the linking number is by an explicit integral. We use that definition to prove deformation invariance, and also to explain (partially) the projection formula.

## (15a) Undercrossings and overcrossings. Take two loops in space,

(15.1) 
$$c(t) \in \mathbb{R}^3, \quad c(t+T) = c(t),$$
$$d(u) \in \mathbb{R}^3, \quad d(u+U) = d(u),$$

which never intersect each other:

(15.2) 
$$c(t) \neq d(u)$$
 for all  $t, u$ .

The linking number is an integer  $link(c,d) \in \mathbb{Z}$ , which arises from trying pull the loops apart (without letting them intersect). Here are its basic properties:

- (Symmetry) link(c, d) = link(d, c).
- (Direction) If we change the direction of one of the loops, meaning either replacing c(t) with c(-t), or d(t) with d(-t), the linking number switches sign (if we make both changes at the same time, the linking number remains the same).
- (Deformation invariance) The linking number remains constant under deformations of c and d, as long as the loops don't cross each other.
- (Separation) If c and d are separated by a plane (one loop on each side), the linking number is zero.

To compute the linking number, we project our loops to the (x, y) plane. This is as if we were looking at them from above (and from a great height). We'll need to impose two important requirements.

- Whenever the projected loops in the plane intersect each other, only one piece of c and one piece of d cross there. This means that if c(t) and d(u) have the same (x,y)-coordinates, then no other point of c or d has those (x,y)-coordinates.
- At any such a crossing point, the projected loops must cross each other transversally; meaning that their derivatives at the crossing point must be linearly independent.

One can deform (slightly) any given loops to achieve this. At each crossing point, we remember which loop was originally above the other in the z-coordinate. Then,

(15.3) 
$$\operatorname{link}(c,d) = \sum_{\substack{\text{crossing points}\\ \text{of the projections}}} \pm \frac{1}{2},$$

120 IV. LOOPS

where the sign is determined by what the crossing looks like (including the directions of parametrization of the two loops):

$$(15.4) \qquad \qquad \begin{array}{c} \uparrow \\ \hline \\ \downarrow \\ +\frac{1}{2} \end{array} \qquad \begin{array}{c} -\frac{1}{3} \end{array}$$

It doesn't matter which of the two pieces is c and which is d (remember the symmetry property), but it does matter that they belong to different loops: otherwise, we would have a selfintersection of one of our two projected loops, and selfintersections do not count for the linking number. One can show that there is always an even number of crossings (the polygonal analogue was Problem 4.7). This explains why, in spite of the  $\frac{1}{2}$  in (15.3), the linking number is an integer.

Example 15.1. Here are some linking number computations:

One can motivate the signs associated to the crossings by deformation invariance:

The undercrossing-overcrossing formula works well for computing the linking number, but is not a satisfactory theoretical basis, because it depends on a choice of projection to the plane.

(15b) The Gauss integral. Because we are working in three dimensions, the notational conventions are different from our usual ones. The length and dot (scalar) product are the obvious ones in  $\mathbb{R}^3$ , but  $\times$  is now the spatial cross product

$$(15.7) v \times w \in \mathbb{R}^3 for v, w \in \mathbb{R}^3.$$

It is helpful to remember the following formula, which demystifies the cross product:

(15.8)  $(v \times w) \cdot q = (\text{the determinant of the } 3 \times 3 \text{ matrix with column vectors } v, w, q).$ 

One defines the linking number

(15.9) 
$$\operatorname{link}(c,d) = \frac{1}{4\pi} \int_0^T \int_0^U \frac{(c'(t) \times d'(u)) \cdot (c(t) - d(u))}{\|c(t) - d(u)\|^3} du dt.$$

A priori this formula is mysterious, and it's not clear at all what it has to do with our previous description of the linking number. The first step in understand it to show that it has the required deformation invariance property:

THEOREM 15.2. The integral (15.9) is unchanged if we deform c and d, as long as they don't cross each other.

This can be proved by a lengthy multivariable computation, which we omit here. What's easier is the following consequence, which is a form of the separation property:

COROLLARY 15.3. Suppose that c lies in  $\{z > 0\} \subset \mathbb{R}^3$ , and d in the region  $\{z < 0\} \subset \mathbb{R}^3$ . Then their linking number, as defined by (15.9), is zero.

PROOF. Let's use the deformation  $c_s(t) = c(t) + (0,0,s)$  and  $d_s(u) = d(u) - (0,0,s)$ , which pulls the first loop up and pushes the second one down. This does not change the derivatives:  $c'_s(t) = c'(t)$  and  $d'_s(u) = d'(u)$ . However,  $||c_s(t) - d_s(u)||$  goes to infinity as s goes to infinity, because the two loops are separated by at least 2s distance. As a consequence, we have

(15.10) 
$$\frac{c_s(t) - d_s(u)}{\|c_s(t) - d_s(u)\|^3} \longrightarrow 0 \quad \text{as } s \text{ goes to infinity.}$$

But that means that the entire integral goes to zero. On the other hand, by deformation invariance it doesn't change at all, which means it must have been equal to zero in the first place!  $\Box$ 

(15c) Contributions from crossings. How does the definition via the integral formula relate to the original description of the linking number in terms of crossings? We will only look at this in a highly simplified toy model. Namely, let's suppose that instead of loops we consider the straight lines

$$(15.11) c(t) = (t, 0, 0), \quad d(u) = (0, u, z),$$

where z is a nonzero constant. Then

(15.12) 
$$(c'(t) \times d'(u)) \cdot (c(t) - d(u)) = \det \begin{pmatrix} 1 & 0 & t \\ 0 & 1 & -u \\ 0 & 0 & -z \end{pmatrix} = -z,$$
$$||c(t) - d(u)|| = \sqrt{t^2 + u^2 + z^2}.$$

Of course, the linking number is not really defined in this situation; but we can still look at the integral, which is now an improper one, integrating over  $(t, u) \in \mathbb{R}^2$ . It can be explicitly solved by passing to polar coordinates:

(15.13) 
$$-\frac{1}{4\pi} \int_{-\infty}^{\infty} \int_{-\infty}^{\infty} \frac{z}{(z^2 + t^2 + u^2)^{3/2}} dt du = -\frac{1}{2} \int_{0}^{\infty} \frac{zr}{(z^2 + r^2)^{3/2}} dr$$

$$= \frac{1}{2} \frac{z}{(z^2 + r^2)^{1/2}} \Big|_{r=0}^{r=\infty} = -\frac{1}{2} \frac{z}{|z|} = \begin{cases} -\frac{1}{2} & z > 0, \\ \frac{1}{2} & z < 0. \end{cases}$$

These are exactly the contributions from (15.4), for the unique crossing of our paths-which-are-not-loops.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 16. Immersed loops and the rotation number

Possibly, our notion of loop will have struck you as intuitively wrong, since it allows for example a constant map to be a loop. That may be because what you have in mind is a different notion, that of an immersed loop. Briefly, an immersed loop is one that can't stop moving at any time.

- Immersed loops have another topological invariant associated to them, the rotation number, which involves the direction of motion rather than the position.
- The rotation number can be easily explained in terms of the winding number of derivatives, and then we can use our previous techniques to compute it.
- There is another and more exciting way of computing the rotation number, in terms of selfintersection points.
- (16a) Immersed loops. Take a loop c with period T,  $c(t+T) = c(t) \in \mathbb{R}^2$ . We say that the loop is *immersed* if  $c'(t) \in \mathbb{R}^2$  never becomes zero. An immersed loop can have selfintersection or self-tangency points. It can even repeat the same trajectory several times. What it can't do is form a kind of corner: it always moves forward in the direction of its tangent line, which itself varies differentiably in time. Here are some examples and non-examples of immersed loops:

It's important to remember that the two non-examples on the right could in principle be smooth loops, parametrized in such a way that the derivative is zero at the kinks in the image.

We define the rotation number of an immersed loop by the integral formula

(16.2) 
$$\operatorname{rot}(c) = \frac{1}{2\pi} \int_0^T \frac{c'(t) \times c''(t)}{\|c'(t)\|^2} dt.$$

Example 16.1. Take

(16.3) 
$$c(t) = (R\cos(mt), R\sin(mt)) \quad (T = 2\pi),$$

the loop that goes m times round a circle of radius R. Then ||c'(t)|| = Rm, and

(16.4) 
$$c'(t) \times c''(t) = \begin{pmatrix} -Rm\sin(mt) \\ Rm\cos(mt) \end{pmatrix} \times \begin{pmatrix} -Rm^2\cos(mt) \\ -Rm^2\sin(mt) \end{pmatrix} = R^2m^3,$$

so

(16.5) 
$$\frac{1}{2\pi} \int_0^T \frac{c'(t) \times c''(t)}{\|c'(t)\|^2} dt = \frac{1}{2\pi} \int_0^{2\pi} \frac{R^2 m^3}{(Rm)^2} dt = m.$$

(16b) Counting tangencies. Saying that a loop is immersed means exactly that  $c'(t) \in \mathbb{R}^2$  avoids the origin o. It is therefore natural to suspect a relation with the winding number of c'. Indeed, a direct comparison of the integral formulae shows that

(16.6) 
$$\operatorname{rot}(c) = \operatorname{wind}(c', o).$$

Example 16.2. Here's a trefoil-shaped immersed loop c(t), and an approximate picture of c'(t):

From the right-hand picture, we read off that rot(c) = wind(c', o) = 2.

Recall that, to compute the winding number of a loop d(t) around a point, we send out a ray from that point to infinity and, roughly speaking, count the intersections of the ray with the loop. If our point is the origin, and the ray goes in direction w, this amounts to looking at all d(t) which are positive multiples of w. Applying the previous recipe to d(t) = c'(t), we get a way of computing the rotation number of c by counting points where c'(t) points in some chosen direction. Let's explain the outcome in a self-contained way. Let c be an immersed loop. Choose a nonzero vector w, and look at those t where c'(t) points in the same direction as (in other words, is a positive multiple of) w. We count those with signs:

Example 16.3. Here's another way of computing that the trefoil loop has rotation number 2, by counting upwards-pointing tangencies:

$$(16.9)$$

There is an implicit assumption here, which is that w is chosen so that our curve bends either to the left or to the right at the relevant points. Let's make this a little more rigorous. The assumption is:

(16.10) for each t such that c'(t) is a positive multiple of w, the vectors (c'(t), c''(t)) must be linearly independent.

Then, we can write our formula as

(16.11) 
$$\operatorname{rot}(c) = \sum_{t} \operatorname{sign}(c'(t) \times c''(t)),$$

summing over all  $t \in [0, T)$  which appear in (16.10).

(16c) Counting selfintersections. Take an immersed loop c, with period T. We say that the loop is *embedded* if it has no selfintersections. This means that for each  $q \in \mathbb{R}^2$ , there is at most

one  $t \in [0,T)$  such that c(t) = q. One can think of embedded loops as the smooth analogues of polygons.

Proposition 16.4. (Umlaufsatz) For an embedded loop c, one always has  $rot(c) = \pm 1$ .

We get +1 if we go around the loop anticlockwise, -1 if we go around the loop clockwise. Even though that may not be clear at first sight, this is the curved analogue of the familiar fact that the angles of a polygon with n vertices add up to  $(n-2)\pi$  (if you want to explore the connection, you'd have to approximate our loops by a polygonal one, and then see how the polygonal approximation to the rotation number is related to the angles).

There is a generalization of the Umlaufsatz, which yields a remarkable relation between the rotation number and selfintersection points. Let c(t) be an immersed loop (with period T). We say that c has  $simple\ selfintersections$  if the following two conditions hold:

- (No triple intersections) For every  $q \in \mathbb{R}^2$ , there are at most two  $t \in [0,T)$  with c(t)=q.
- (Transverse crossing) If  $q = c(t_1) = c(t_2)$  for some  $t_1 < t_2$  in [0, T), then  $(c'(t_1), c'(t_2))$  must be linearly independent.

Suppose that we have a selfintersection point, with notation as in the second condition above. We can give it a sign,

(16.12) 
$$\sigma(q) = \operatorname{sign}(c'(t_2) \times c'(t_1)) = -\operatorname{sign}(c'(t_1) \times c'(t_2)) \in \{\pm 1\}.$$

Geometrically, the convention looks like this, remembering always that  $t_1 < t_2$ :

The sign is sensitive to where we put the starting point t = 0 on the loop. We want to choose that in a particular way:

(16.14) An immersed loop is said to have an outside starting point if the entire loop lies in the half-plane to one side of its tangent line at t = 0.

THEOREM 16.5. (Whitney's formula) Let c be an immersed loop with simple selfintersections, and which has an outside starting point. Then,

(16.15) 
$$\operatorname{rot}(c) = \pm 1 + \sum_{q} \sigma(q).$$

The sign of the first term is fixed as follows. Start at c(0), and look in direction c'(0). If the loop lies in the half-plane to the left of you, we get +1; if it lies in the half-plane to the right of you, we get -1. The other terms are the signs associated to selfintersection points.

Example 16.6. Yet again, we compute the rotation number of the trefoil loop, this time using Whitney's formula:

(16d) **Deformations.** The simple selfintersection requirement may strike one as a problem: what if it fails? Here, deforming immersed loops comes in handy.

FACT 16.7. The rotation number is deformation invariant within the class of immersed loops. This means that if  $c_s(t)$  is a deformation of loops  $(0 \le s \le 1)$ , such that for every value of the parameter s the loop  $t \mapsto c_s(t)$  is immersed, then  $rot(c_0) = rot(c_1)$ .

This follows immediately from the corresponding property of the winding number. Saying that the loops  $c_s$  must remain immersed is the same as saying that  $c_s'(t) = \partial c_s(t)/\partial t$  must avoid the origin, which is what we need in order for wind $(c_s', o)$  to be constant as a function of s.

Example 16.8. The loop drawn below can be deformed to a circle without breaking immersion (to see that, imagine pushing each of the four pieces which stick out along the coordinate axes all the way through to the opposite side). Therefore, it has rotation number 1.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 17. Arnold invariants

We mentioned in the last lecture that deforming an immersed loop preserves its rotation number. Actually, the converse is also true: two loops with the same rotation number can be deformed into each other through immersed loops. One could think that this finishes off the topic of the topology of immersed loops, but actually, it's only the beginning!

- Any deformation can be broken down into steps, each of which changes the picture of the loop in the plane in a specific way. There are three kinds of such transitions.
- There is a way of keeping track of how many moves of each kind occur. This is provided by Arnold invariants, one for each kind of transition.

(17a) Deformations of immersed loops. We begin by stating (without proof) the result mentioned above:

THEOREM 17.1. (Whitney-Graustein) Take two immersed loops  $c_0(t)$  and  $c_1(t)$  with (the same period T, and) the same rotation number. Then, one can deform one into the other through immersed loops.

To get a more explicit picture, let's start with the notion of immersed loop with simple selfintersections, from the last lecture. What are the simplest ways in which an immersed loop can fail to have simple selfintersections? The loop could have a self-tangency, meaning two points  $0 \le t_1 < t_2 < T$  such that  $c(t_1) = c(t_2)$  and the derivatives  $c'(t_1)$ ,  $c'(t_2)$  are linearly dependent. More precisely, this comes in two versions, the direct self-tangency, where  $c'(t_1)$ ,  $c'(t_2)$  differ by multiplication by a positive number; and the inverse self-tangency, where the number is negative. In both cases, we can perturb the loop a little to remove the self-tangency. Depending on how we perturb, we may or may not create a pair of selfintersection points:

$$(17.1)$$

and

$$(17.2) \qquad \qquad \bigcirc \langle --- \rangle \rangle$$

The other simple way in which our loop could fail to have simple selfintersections is by having a triple intersection point. Again, there are two ways of perturbing this situation to get rid of the triple point. Each of them trades it for a triple of simple selfintersection points:

One can use this to give the following more combinatorial version of Whitney-Graustein:

THEOREM 17.2. Take two immersed loops with only simple selfintersections, and which have the same rotation number. Then, they can be transformed into each other by a composition of the following kinds of deformations:

- Deformations during which the loop retains its property of having simple selfintersections at all times. Such deformations do not change the overall topological picture of the loop in the plane. In particular, they can't create or destroy selfintersections. In the game we're about to play, this is considered a "free action" which you can do at any time.
- Direct self-tangency moves, which means passing from one side of (17.1) to the other. This creates or destroys a pair of selfintersection points.
- Inverse self-tangency moves, which are the same for (17.2)
- Triple point moves, which means passing from one side of (17.3) to the other. This preserves the number of selfintersection points.

Example 17.3. These two loops have rotation number 3, and 2 simple selfintersection points:

$$(17.4)$$

They are related by a sequence of three moves, one of each type:

Of course, this is only one way of constructing a deformation, there are many others. One can ask, for instance: can we transform those two loops into each other using only triple point moves?

(17b) The  $J^{\pm}$  invariants. We now introduce the first two Arnold invariants, which count self-tangency moves (with suitable signs).

PROPOSITION 17.4. To each immersed loop c with simple selfintersections one can associate two integers  $J^-(c)$  and  $J^+(c)$ , such that the following are satisfied:

- Reversing the direction of a loop doesn't change  $J^-$  or  $J^+$ .
- The loops below have prescribed values of the invariants:

(17.6) 
$$J^{-} = -1 \quad J^{-} = 0 \qquad J^{-} = -3k$$

$$J^{+} = 0 \quad J^{+} = 0 \qquad J^{+} = -2k$$

$$k \text{ curls (as drawn, } k = 2)$$

• Under an inverse self-tangency move which creates two new selfintersection points,  $J^-$  decreases by 2 (conversely, under such a move which destroys two selfintersection points, it increases by 2); and  $J^+$  remains the same.

- Under a direct self-tangency move which creates two new selfintersection points,  $J^+$  increases by 2 (conversely, under such a move which destroys two selfintersection points, it decreases by 2); and  $J^-$  remains the same.
- $J^-$  and  $J^+$  do not change under triple point moves.

The first property gives one example for each winding number. Together with the rules for what happens under the different types of moves, this describes  $J^-$  and  $J^+$  completely, and allows us to compure it in any given case, by finding a deformation that transforms the loop into the relevant example where the values are given. In practice, you only have to know one of the two invariants, because (as one sees by looking at the moves):

FACT 17.5.  $J^{+}(c) - J^{-}(c)$  is the number of selfintersection points of c.

Example 17.6. Let's revisit our previous example. The  $J^{\pm}$  values for one loop are prescribed by (17.6), and we derive those for the other loop by following the moves:

(17.7) 
$$J^{+} = -4, J^{-} = -6$$

$$J^{+} = -6, J^{-} = -8$$

$$direct tangency$$

$$triple point$$

$$J^{+} = -4, J^{-} = -8$$

$$J^{+} = -4, J^{-} = -8$$

Hence, it's impossible to relate the two loops without using self-tangency moves of both kinds!

Example 17.7. Take this loop:

(17.8) 
$$2k \text{ selfintersections (here, } k = 3)$$

Obviously, one can deform this to a circle (an embedded loop) by using k inverse self-tangency moves, and no moves of any other kind. Hence,  $J^+=0$ , just by looking up the value for the circle. Moreover,  $J^-=-2k$ , which one can either see by following the moves, or from Fact 17.5.

(17c) An explicit formula. If we have a simple selfintersection point q, the winding numbers for the regions surrounding q form a pattern like this:

(17.9) winding number 
$$w + 1$$
  $w - 1$ 

(we saw this first in the corresponding polygonal case). Let's call w the mean winding number of c at q, written as meanwind(c, q).

Proposition 17.8. (Viro-Gutkin) One can compute the  $J^-$ -invariant by the formula

(17.10) 
$$J^{-}(c) = 1 - \sum_{R} \text{wind}(c, R)^{2} + \sum_{q} \text{meanwind}(c, q)^{2}.$$

Here, R are the regions into which c divides the plane; we take a point in each region, and wind(c, R) is the winding number around that point. The second sum is over selfintersections q.

Example 17.9. Let's see that this is compatible with the values originally stated. The loop

$$(17.11) \qquad \qquad \begin{array}{c|c} & & & & & & & & & & & & & & & & & & &$$

with k curls divides the plane into k+2 regions with winding numbers 0,1 and 2 (the latter appears k times). The k selfintersection points all have mean winding number 1. Therefore

$$(17.12) J^{-} = 1 - (1+4k) + k = -3k.$$

Example 17.10. Take the following (with rotation number 5):

$$(17.13)$$

The regions of its complement have winding numbers 0, 1, 2, 3, 4, 5, as drawn in the picture; and the selfintersection points have mean winding numbers 1, 2, 3, 4. As a consequence

$$(17.14) J^{-} = 1 - (1^{2} + 2^{2} + 3^{2} + 4^{2} + 5^{2}) + (1^{2} + 2^{2} + 3^{2} + 4^{2}) = -24,$$

and therefore  $J^+ = -20$ . It follows that, in order to deform it to the "standard loop" which is the k = 4 case of (17.6) with  $J^- = -12$  and  $J^+ = -8$ , we need at least 6 direct and 6 inverse self-tangency moves.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 18. Arnold invariants (continued)

Among the moves introduced in the previous lecture, the triple point move is the most mysterious one: self-tangency moves create, or in reverse direction destroy, self-intersection points, but at first sight, the triple point move doesn't have such a directionality.

- Nevertheless, a closer look at the situation allows us to assign a sign to such a move. This underlies the third Arnold invariant, called *strange invariant*, which was missing from our collection so far.
- There is an explicit expression for this invariant, which combines the signs from Whitney's formula for the rotation number with the (mean) winding number.

(18a) Triangles. Let c be an immersed loop with simple self-intersections. Suppose that among the regions into which it divides the plane, there is a triangular one T, where the vertices of the triangle correspond to three different selfintersection points.

As we go around the loop, we will pass through the three sides of the triangle in some order: let's number the sides correspondingly as  $a_1$ ,  $a_2$ ,  $a_3$  (if we move the starting point of c elsewhere, we might get to the sides in order  $(a_2, a_3, a_1)$  or  $(a_3, a_1, a_2)$  instead, but that turns out not to matter in the end). Let's just focus on the triangle, and go around it in the same order  $(a_1, a_2, a_3)$ . We set  $\delta_1 = 1$  if that way of going around the triangle agrees with the direction of  $a_1$  (increasing t), and  $\delta_1 = -1$  otherwise. Similarly, we have  $\delta_2$  and  $\delta_3$ . We define the sign of the triangle to be

(18.2) 
$$\delta(T) = -\delta_1 \delta_2 \delta_3 \in \{\pm 1\}.$$

FACT 18.1. The sign of the triangle does not change if we reverse the direction of the loop, meaning that we replace c(t) with c(-t).

Passing to c(-t) means that we reach the sides of T in the opposite order; but at the same time, the increasing t-direction on each side reverses; so the  $\delta_k$  remain the same.

FACT 18.2. Suppose that we carry out a triple point move with our triangle. After that move, we get a new triangle whose sign is the opposite of the old one.

This is not hard to see. All of the  $\delta_k$  change signs after the move, with the compound effect being a sign change in  $\delta(T)$ :

(18b) The strange invariant. The observation above provides triple point moves with a kind of directionality: if one such move replaces a negative triangle with a positive one, then the reverse move does the opposite.

THEOREM 18.3. To every immersed loop c with simple selfintersections, one can associate an integer St(c), such that the following are satisfied:

- Reversing the direction of a loop doesn't change St.
- The loops below have prescribed St invariants:

(18.4) 
$$St = 0 St = k$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow \qquad \downarrow \qquad \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad \downarrow \qquad$$

- Under a triple point move which replaces a negative triangle with a positive one, St increases by 1 (and the reverse direction decreases it by 1).
- St does not change under the other kinds of moves.

Example 18.4. We look at the same series of moves as last lecture, starting with one of the standard examples. The triple point move changes a triangle with  $\delta(T) = 1$  into one with  $\delta(T) = -1$ , hence decreases the strange invariant by 1.

To see that St indeed goes up (and now down) by 1, we need to look at the signs of the triangles that are involved:

(18.6) 
$$\delta(T) = -1 \qquad \delta(T) = 1$$

(18c) An explicit formula. Suppose that c has an outside starting point. Then, every self-intersection point has a sign  $\sigma(q) \in \{\pm 1\}$ , which is what appears in Whitney's formula for the rotation number. As a reminder, the conventions are:

We also have the mean winding number for selfintersection points, introduced in the previous lecture. The two combine in this formula:

PROPOSITION 18.5. (Shumakovich) Assuming an exterior starting point, one can compute the strange invariant by

(18.8) 
$$St(c) = \sum_{q} \sigma(q) \operatorname{meanwind}(c, q).$$

Example 18.6. We reconsider the previous computation:

There are two double points, whose contributions yield St(c) = 1 + 2 = 3.

Example 18.7. Take these two loops:

They both have 4 selfintersection points, and rotation number 5, so the Whitney signs are clearly all  $\sigma(q) = 1$ . On the left, the mean indices are all 1, yielding St = 4. On the right, the mean indices are 1, 2, 3, 4, so St = 10. This means that when transforming one loop into the other, at least 6 triple point moves are necessary. We proved in the last lecture that at least 6 direct and 6 inverse self-tangencies are necessary, so in total, one needs at least 18 moves (this is a lower bound; I haven't checked whether you can really get away with just that many moves).

To see why Proposition 18.5 is correct, one needs to look at the behaviour of the proposed formula under the various moves. A direct or inverse tangency creates two new selfintersection points, which have opposite signs  $\sigma(q)$  (after all, the rotation number doesn't change, so their contributions to Whitney's formula must cancel out) and the same meanwind(q). Therefore, the right hand side of (18.8) is invariant under self-tangency moves, as it should be. Here's a sample picture of the situation (the w are winding numbers of the regions, and the  $\sigma$  the Whitney signs of the selfintersection points):

Here's an example which shows how to analyze the effect of a triple point move:

The Whitney signs carry over, but the winding numbers change. In this particular case, the mean winding numbers of all three intersection points go down by 1, but since the Whitney signs are (+1,+1,-1), the cumulative effect is that the right hand side of (18.8) decreases by 1; which, as one can check, matches the sign convention for St.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 19. Introduction to algebraic curves

In this chapter we will discuss algebraic curves in the plane, which are described by a polynomial equation in two variables. To familiarize you with this kind of object, this lecture is dedicated to fairly basic example constructions:

- We look at algebraic curves which are of the very special form f(x) = g(y), and how one can draw roughly what such a curve looks like.
- We show one can construct algebraic curves passing through a given finite collection of points in the plane (interpolation).
- We look at other ways in which algebraic curves can arise, through rational or trigonometric parametrizations.

(19a) Definition and first examples. An algebraic curve is the subset of the plane formed by the solutions (x, y) of a non-constant polynomial equation in two variables,

(19.1) 
$$C = \{(x, y) \in \mathbb{R}^2 : f(x, y) = 0\}.$$

To make our language more precise, let's say that  $x^i y^j$  is a monomial of degree i + j. Then, a polynomial of degree  $\leq d$  is a sum of monomials

(19.2) 
$$f(x,y) = \sum_{\substack{i \ge 0, j \ge 0\\ i+1 \le d}} a_{ij} x^i y^j,$$

with real coefficients  $a_{ij} \in \mathbb{R}$ . If at least one of the top degree terms  $a_{ij}x^iy^j$ , i+j=d, is nonzero, we say that the polynomial has degree d. This notion of degree behaves in the way familiar from a single variable: if you multiply polynomials, the degrees add. An algebraic curve of degree d > 0 is the zero-set of a polynomial of that degree. For instance, a degree 1 polynomial is just a linear function  $f(x,y) = a_{00} + a_{10}x + a_{01}y$ , with  $(a_{10},a_{01}) \neq (0,0)$ ; and hence, a degree 1 algebraic curve is just a straight line. We call a degree 2 algebraic curve a conic.

Fact 19.1. The conics are of the following kinds:

- ellipses, including circles;
- parabolae;
- hyperbolae; these three cases together are the classical conics.
- Unions of two lines. This happens when f(x,y) is the product of two degree 1 polynomials. The two lines can intersect (for instance, xy = 0), or they can be parallel (x(x-1) = 0), or they can even be the same  $(x^2 = 0)$ ; in situations like this, the terminology "curve of degree d" becomes a little awkward).
- Sets consisting of one point in the plane  $(x^2 + y^2 = 0)$ .
- The empty set  $(x^2 + y^2 = -1)$ .

As we saw above, the union of two lines is an algebraic curve. More generally,

FACT 19.2. If  $C_1$  and  $C_2$  are algebraic curves, then so is  $C = C_1 \cup C_2$ . To see that, write  $C_i = \{f_i(x,y) = 0\}$ , and then  $C = \{f(x,y) = 0\}$ , where  $f(x,y) = f_1(x,y)f_2(x,y)$ .

We also saw that a single point is an algebraic curve. This is also an instance of a wider observation:

FACT 19.3. If  $C_1$  and  $C_2$  are algebraic curves, then so is  $C = C_1 \cap C_2$ . To see that, write  $C_i = \{f_i(x,y) = 0\}$ , and then  $C = \{f(x,y) = 0\}$ , where  $f(x,y) = f_1(x,y)^2 + f_2(x,y)^2$ .

We've defined an algebraic curve just as a subset  $C \subset \mathbb{R}^2$  which can be described by an algebraic equation, but different equations can give the same curve. The unfortunate outcome of this is that the degree of C is in general ambiguous. The line  $\{x=0\}$  is also the conic  $\{x^2=0\}$ , and indeed the degree n curve  $\{x^n=0\}$  for any n.

The following is maybe the simplest way to construct examples of higher degree curves whose structure you can understand. Look at

$$(19.3) C = \{p(x) = y^2\}.$$

This means that  $y = \pm \sqrt{p(x)}$ , so for every x, we have 0, 1 or 2 solutions of y, depending on the sign of p(x).

Example 19.4. Take  $C = \{x^3 - x = y^2\}$ . This satisfies

(19.4) 
$$p(x) = x^{3} - x = (x - 1)(x + 1)x \begin{cases} negative & x < -1, \\ positive & -1 < x < 0, \\ negative & 0 < x < 1, \\ positive & x > 1, \\ zero & x = -1, 0, 1. \end{cases}$$

So, we get two solutions of  $y^2 = p(x)$  for every  $x \in (-1,0)$ , and also for every x > 1. Here's what C actually looks like:

(19b) Interpolation. Everyone knows that there's a line through any two given points. The result one degree higher is this:

LEMMA 19.5. For any 5 points in the plane, there is a conic which goes through all those points. (There may be more than one, depending on the positions of the points, but there is at least one. It may not be a classical conic, though.)

To prove the result, write  $q_i = (x_i, y_i), i = 1, ..., 5$ . Let's look at a general conic f(x, y) = 0,

$$f(x,y) = a_{20}x^2 + a_{11}xy + a_{02}y^2 + a_{10}x + a_{01}y + a_{00}.$$

The condition for that conic to go through our five points are

$$a_{20}x_1^2 + a_{11}x_1y_1 + a_{02}y_1^2 + a_{10}x_1 + a_{01}y_1 + a_{00} = 0,$$

$$a_{20}x_2^2 + a_{11}x_2y_2 + a_{02}y_2^2 + a_{10}x_2 + a_{01}y_2 + a_{00} = 0,$$

$$a_{20}x_3^2 + a_{11}x_3y_3 + a_{02}y_3^2 + a_{10}x_3 + a_{01}y_3 + a_{00} = 0,$$

$$a_{20}x_4^2 + a_{11}x_4y_4 + a_{02}y_4^2 + a_{10}x_4 + a_{01}y_4 + a_{00} = 0,$$

$$a_{20}x_5^2 + a_{11}x_5y_5 + a_{02}y_5^2 + a_{10}x_5 + a_{01}y_5 + a_{00} = 0.$$

These are 5 linear equations for the 6 unknown coefficients of the conic. Hence, there must be a solution where not all of the  $a_{ij}$  are zero. (In principle, the resulting f(x, y) could have degree 1, but then one could take the product with an arbitrary linear term to get the degree back up to 2). The same idea actually works in any degree:

THEOREM 19.6. Take some  $d \ge 1$ , and choose d(d+3)/2 points in the plane. Then there is an algebraic curve of degree d which passes through all of them.

(19c) Parametrizations. We are used to two ways of describing curves, one by equations and the other by parametrizations. Algebraic curves are by definition given by polynomial equations, but we also have the following:

Theorem 19.7. Any two rational functions x(t) and y(t) parametrize part of an algebraic curve.

EXAMPLE 19.8. One can find a rational parametrization of the circle  $x^2 + y^2 = 1$  (minus a point) as follows. Draw a line from a point (t, -1) to (0, 1). This line intersects the circle at one point other than (0, 1), and one can solve for the coordinates of that point:

To understand why the theorem holds, let's suppose that x(t) and y(t) are polynomials of degree  $\leq 3$ . We claim that then, they parametrize part of an algebraic curve of degree  $\leq 4$ . Look at the monomials that can occur,

(19.9) 
$$1, x(t), y(t), x(t)^{2}, x(t)y(t), y(t)^{2}, x(t)^{3}, x(t)^{2}y(t), x(t)y(t)^{2}, y(t)^{3}, x(t)^{4}, x(t)^{3}y(t), x(t)^{2}y(t)^{2}, x(t)y(t)^{3}, y(t)^{4}.$$

Each of these is a polynomial of degree  $\leq 3 \cdot 4 = 12$  in t. Such a polynomial has 13 coefficients, so we can think of it as a vector in  $\mathbb{R}^{13}$ . There are 15 such polynomials/vectors, so there must be a linear relation between them (15 > 13); and that translates into a polynomial relation between x(t) and y(t) of degree  $\leq 4$ . The same argument shows that if x(t) and y(t) are polynomials of degree  $\leq d$ , for some  $d \geq 2$ , then they trace out part of an algebraic curve of degree  $\leq 2d - 2$ . The general case of rational functions is similar but more complicated, since one has to take the degrees of numerator and denominator into account.

A trigonometric polynomial of degree  $\leq d$  is an expression

(19.10) 
$$p(\theta) = a + \sum_{k=1}^{d} b_k \cos(k\theta) + \sum_{k=1}^{d} c_k \sin(k\theta),$$

with constants  $a, b_1, \ldots, b_d, c_1, \ldots, c_d$ . A trigonometric rational function is then defined as a function that's a quotient of two trigonometric polynomials.

Theorem 19.9. Any two trigonometric rational functions  $x(\theta)$  and  $y(\theta)$  parametrize part of an algebraic curve.

One can prove this as before, by finding linear relations between the  $x(\theta)^i y(\theta)^j$  (by the angle addition formulae, these are all polynomials in  $\cos(\theta)$  and  $\sin(\theta)$ ). There is also a more sneaky approach, using the rational parametrization (x(t),y(t)) of the circle from (19.8): substituting  $(\cos(\theta),\sin(\theta))=(x(t),y(t))$  turns a parametrization by trigonometric rational functions into one (much more complicated) by ordinary rational functions. So, the theorem can actually be reduced to the previous one.

Any kind of converse to the theorems above is false: "most" algebraic curves of degree > 2 can't be parametrized by rational (or trigonometric rational) functions. In other words, any parametrization of such a curve must be by functions which are more complicated.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 20. Mechanical linkages and polynomial equations

In this lecture, we explore other contexts which give rise to algebraic curves, even though one might not necessarily expect that.

- Mechanisms assembled from rods and joints often move along algebraic curves.
- To help us understand why that is the case, we introduce the resultant, a beautiful piece of classical algebra.

(20a) Linkages. Let's imagine a machine (the precise terminology is mechanical linkage) that consists of rods and rotary joints, all moving in a common plane; any intersections that may occur between the parts will be ignored. More precisely, we specify the lengths of the rods connecting various joints; certain joints will have a fixed positions, while the others can move freely, subject to the length constraints; and finally, somewhere on our machine, we place a pen. What are the possible positions of the pen? In other words, if we put a sheet of paper on our plane and let the machine move in all possible ways, what shape does the pen color?

Example 20.1. Take the two-piece robot arm drawn below:

(20.1) this point fixed at 
$$(0,0)$$
  $\bullet$  position of the pen length 2 length 1

Clearly, the pen can reach any point in the region  $\{1 \le x^2 + y^2 \le 9\}$ .

Example 20.2. This is the Chebyshev mechanism, consisting of three rods with two fixed points:

It draws a curve like this,

This was historically of interest in engineering because it has a piece which is almost (but not exactly) a straight line segment. It turns out that (20.3) is part of the following algebraic curve:

$$(20.4) (x^2 + y^2)^3 - 8(7x^4 - 12x^2y^2 + 5y^4) + 16(49x^2 + 24y^2) = 0.$$

To be precise, the solution set of (20.4) consists of the curve we've drawn, its mirror image under  $y \mapsto -y$  (the same machine but in a position where the long rods hang downwards), and the (more mysterious) point (0,0).

The naive idea is that if a linkage has "one degree of freedom", it draws part of an algebraic curve. Unfortunately, in this case the notion of "degree of freedom" has huge pitfalls, which every single engineering class discussing linkages steps into. The actual statement is this:

THEOREM 20.3. The set S of all possible positions of the pen can be described by polynomial equalities and inequalities (one or several expressions p(x, y)? 0 with p polynomial, and ? being  $=, \neq, >, \geq, <, \leq$ ). If, in that description, there is at least one equality, then S is a subset of an algebraic curve.

Example 20.4. As we've already seen, the possible positions of the pen in (20.1) are described by the inequalities  $x^2 + y^2 > 1$  and  $x^2 + y^2 < 9$ .

Example 20.5. The possible positions of the pen in Chebyshev's mechanism is described by the equation (20.4) together with some inequality which excludes the point (0,0), let's say  $x^2 + y^2 > 0$ .

(20b) Systems of polynomial equations. Let's see what the mathematics of a mechanical linkage looks like. Write  $(x_k, y_k)$  for the position of all the joints, and (x, y) for the position of the pen. Some joints are fixed, which means that the corresponding variables  $(x_k, y_k)$  are set to specific values. For the other  $(x_k, y_k)$ , we have equalities of the form

(20.5) 
$$(x_j - x_k)^2 + (y_j - y_k)^2 = squared length of the rod connecting the j-th and k-th joint.$$

If the pen happens to be at the m-th joint, we have  $x = x_m$  and  $y = y_m$ ; in general, there will be a linear equation giving (x, y) in terms of the  $(x_k, y_k)$ .

EXAMPLE 20.6. For the Chebyshev mechanism (20.2), let  $(x_1, y_1)$ ,  $(x_2, y_2)$  be the positions of the moveable joints, and (x, y) that of the pen. The constraints are

$$(x_1 - 2)^2 + y_1^2 = 5^2,$$

$$(x_2 + 2)^2 + y_2^2 = 5^2,$$

$$(x_1 - x_2)^2 + (y_1 - y_2)^2 = 2^2,$$

$$x = \frac{1}{2}(x_1 + x_2),$$

$$y = \frac{1}{2}(y_1 + y_2).$$

We want to describe those (x,y) such that there exist  $(x_1,y_1,x_2,y_2)$  satisfying these equations.

Changing notation a bit, the general situation is that we have variables  $(x, y, z_1, \dots, z_n)$  (the z's are our previous  $x_k$  and  $y_k$ ) and polynomial equations

(20.7) 
$$f_1(x, y, z_1, \dots, z_n) = 0,$$

$$f_2(x, y, z_1, \dots, z_n) = 0,$$

$$\dots$$

$$f_m(x, y, z_1, \dots, z_n) = 0$$

Then, we look at

(20.8) 
$$S = \{(x, y) \in \mathbb{R}^2 : \text{ there exist } (z_1, \dots, z_n) \text{ such that } (x, y, z_1, \dots, z_n) \text{ satisfies } (20.7) \}.$$

The question is, how does one get from such a description to polynomial equalities (or inequalities) that involve only (x, y)? In general, this is answered by the Tarski-Seidenberg theorem, which is beyond our scope; but we can get some idea of the mathematics involved.

(20c) The resultant. Take two polynomials is one variable z, of degree m and n:

(20.9) 
$$f(z) = a_m z^m + a_{m-1} z^{m-1} + \dots + a_1 z + a_0,$$
$$g(z) = b_n z^n + b_{n-1} z^{n-1} + \dots + b_1 z + b_0.$$

The resultant  $res_z(f, g)$  is a number which depends on the coefficients of f and g, and which has the following very nifty property:

LEMMA 20.7. If f and g share a root, then  $res_z(f,g) = 0$ . (More precisely, the resultant is zero exactly when f and g have a common factor. The common root case is when that factor is (z-c) for some  $c \in \mathbb{R}$ .)

The definition of the resultant is elementary but gruesome, as the determinant of a matrix of size m+n. The first n rows contain the coefficients of f padded with n-1 zeros, and the last m rows do the same for q padded with m-1 zeros:

$$(20.10) \quad \operatorname{res}_{z}(f,g) = \det \begin{pmatrix} a_{m} & a_{m-1} & \dots & a_{2} & a_{1} & a_{0} & 0 & 0 & \dots & 0 \\ 0 & a_{m} & a_{m-1} & \dots & a_{2} & a_{1} & a_{0} & 0 & \dots & 0 \\ & & & & & & & \\ \vdots & & & & & & \\ 0 & -\frac{1}{b_{n}} - \frac{1}{b_{n-1}} - \frac{1}{b_{n}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac{1}{b_{0}} - \frac$$

What does this have to do with our discussion? Take a simple of case of (20.8), which is that we have two polynomial equations in three variables,

(20.11) 
$$f(x,y,z) = 0, g(x,y,z) = 0$$

and look at

(20.12) 
$$S = \{(x, y) \in \mathbb{R}^2 : \text{ there exists a } z \in \mathbb{R} \text{ such that (20.11) holds} \}.$$

Pick some  $(x,y) \in \mathbb{R}^2$ , and insert those in f and g, so that they just become polynomials in z. If there exists a z such that f(x,y,z)=0 and g(x,y,z)=0, then those polynomials have a common root. Therefore,

(20.13) 
$$S \subset \{(x,y) : \operatorname{res}_z(f,g) = 0\}.$$

It is important to clarify the situation here: when forming the resultant with respect to z, we write

(20.14) 
$$f(x,y,z) = a_m(x,y)z^m + a_{m-1}(x,y)z^{m-1} + \dots + a_1(x,y)z + a_0(x,y),$$
$$g(x,y,z) = b_n(x,y)z^n + b_{n-1}(x,y)z^{n-1} + \dots + b_1(x,y)z + b_0(x,y).$$

and then stick the  $a_k(x, y)$  and  $b_k(x, y)$  (themselves polynomials in x and y) into (20.10), so that  $\operatorname{res}_z(f, g)$  is a function of (x, y). In fact, the formula (Cramer's formula for the determinant) shows that it is a polynomial!

COROLLARY 20.8. If the polynomial  $h(x,y) = res_z(f,g)$  is nonzero, then the set S from (20.12) is a subset of the algebraic curve  $C = \{h(x,y) = 0\}$ .

If this applies, it reduces us from two polynomial equations in three variables (20.11) to one equation in two variables (h(x, y) = 0).

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 21. Intersections of algebraic curves

The structure of an algebraic curve is constrained by its degree. In this lecture we'll look at one aspect of this, namely how algebraic curves can intersect each other.

- We look at some simple (but still useful) cases, like the intersection of an algebraic curve and a line.
- Then we will state the general result, Bézout's theorem. Later, this will turn out to be a useful tool for studying the topology of algebraic curves.

(21a) Intersections with lines. The curve in the picture below could be algebraic, but if it is, its degree must be at least 6. To see that, one looks at the dashed line, and applies the following general observation:

PROPOSITION 21.1. Let C be a degree d curve, and L a line. Then C intersects L in at most d points, except in the case where L is actually a subset of C.

Namely, take  $C = \{f(x,y) = 0\}$ , and parametrize the line L by (x(t) = at + b, y(t) = ct + d). Points of C that lie on the line correspond to solutions of

$$(21.2) f(x(t), y(t)) = f(at + b, ct + d) = 0,$$

which is a polynomial in one variable t of degree  $\leq d$ . That polynomial could be zero, in which case all t are solutions, and the line is contained in C. Otherwise, it is a basic fact that such a polynomial can only have at most d roots.

PROPOSITION 21.2. An algebraic curve of odd degree d can't be a bounded subset of the plane (it always goes out to infinity).

We have  $C = \{f(x, y) = 0\}$ , where f has degree d. Suppose first that the  $x^d$ -coefficient of f(x, y) is nonzero. Then, if we set y to be a constant, f(x, y) is a polynomial in x of degree d. By another elementary fact, a polynomial of odd degree always has a root. This means that our curve intersects any horizontal line, and must therefore be unbounded.

Well then, what if the  $x^d$ -coefficient is zero? We can work around that by changing coordinates. Let's look at f(x, cx + y), where c is some constant. If  $f(x, y) = \sum_{i+j \le d} a_{ij} x^i y^j$ , then

(21.3) 
$$(x^{d}\text{-coefficient of } f(x, cx + y)) = a_{d,0} + a_{d-1,1}(x^{d}\text{-coefficient of } x^{d-1}(cx + y))$$

$$+ a_{d-2,2}(x^{d}\text{-coefficient of } x^{d-2}(cx + y)^{2}) + \cdots$$

$$= a_{d,0} + a_{d-1,1}c + a_{d-2,2}c^{2} + \cdots + c^{d}.$$

Since f has degree d, one of the  $a_{d-i,i}$  must be nonzero. Therefore, the expression (21.3) is a nonzero polynomial in c, and we can choose c so that the expression is not zero. Then, the previous argument applies after the coordinate change from (x, y) to (x, cx + y).

(21b) Intersection with conics. Going back to the intersection problem, we look at the next case, that of conics.

PROPOSITION 21.3. Let  $C = \{f(x,y) = 0\}$  be a degree d curve, and D a conic. Then C intersects D in at most 2d points, with two exceptions. One exception is if D is contained in C. The second exception is if D is the union of two different lines, and one of those lines is a subset of C.

One can prove this case-by-case by looking at the different kinds of conics. We'll do one example of each case:

- (Parabola) Suppose that  $D = \{x^2 = y\}$ , which we can parametrize by  $(x(t), y(t)) = (t, t^2)$ . Intersection points are solutions of  $f(t, t^2) = 0$ , which is a polynomial in t of degree  $\leq 2d$ , therefore has at most 2d roots.
- (Hyperbola) Suppose that  $D = \{xy = 1\}$ . If we set  $(x(t), y(t)) = (t, t^{-1})$ , then  $f(t, t^{-1})$  is no longer a polynomial in t. Instead, it contains powers of t from  $t^{-d}$  to  $t^d$ . But if we multiply by  $t^d$ , we get a polynomial of degree  $\leq 2d$ , to which the previous argument applies.
- (Ellipse) As an example take the circle  $D = \{x^2 + y^2 = 1\}$ , for which we have the parametrization

(21.4) 
$$x(t) = \frac{4t}{t^2 + 4}, \ y(t) = \frac{t^2 - 4}{t^2 + 4}.$$

If we insert that into the equation for  $C = \{f(x,y) = 0\}$ , we get a sum of terms

(21.5) 
$$x(t)^{i}y(t)^{j} = \frac{(4t)^{i}(t^{2}-4)^{j}}{(t^{2}+4)^{i+j}} = \frac{(4t)^{i}(t^{2}-4)^{j}(t^{2}+4)^{d-i-j}}{(t^{2}+4)^{d}}.$$

Therefore,  $(t^2 + 4)^d f(x(t), y(t))$  is a polynomial of degree  $\leq 2d$  in t. (This argument doesn't quite work if (0, 1) lies on C, because our parametrization leaves out that point; but we can avoid that by rotating the coordinate plane before parametrizing.)

- (Other cases) D could consist of two lines, or one line, or a point, or is empty. All those are easy.
- (21c) The general result. There is a theorem about intersections of algebraic curves of any degree, which includes all the cases discussed above. This is a much more difficult result, because curves of degree > 2 don't generally have rational parametrizations. As an introductory step, let's remind ourselves that if a polynomial can be written as a product of others,

(21.6) 
$$f(x,y) = g(x,y)h(x,y),$$

then the curve  $C = \{f(x, y) = 0\}$  is the union of  $D = \{g(x, y) = 0\}$  and  $E = \{h(x, y) = 0\}$ :

$$(21.7) C = D \cup E.$$

EXAMPLE 21.4. Suppose that f has degree 3. Excluding the silly cases where g or h are constants, the way that (21.6) happens is that one of the factors (g,h) has degree 1 (and the other has degree 2). Then C contains a line. For all other degree 3 curves, f can't be factored into lower degree polynomials. For instance,  $f(x,y) = x^3 + x - y^2$  can't be factored, since a quick look at the graph shows us that  $\{f(x,y)=0\}$  certainly doesn't contain a line.

The general intersection problem is that we have two curves

(21.8) 
$$C_1 = \{f_1(x,y) = 0\}, C_2 = \{f_2(x,y) = 0\}$$

of degrees  $d_1$  and  $d_2$ , respectively. The problem, as we already saw in the situations above, is that that there are exceptions: it is possible for  $C_1 \cap C_2$  to be infinite, when the two curves have a part in common. Let's see how that could come about algebraically: suppose that  $f_1$  and  $f_2$  have a common factor g, which means they can be written as products of polynomials

(21.9) 
$$f_1(x,y) = g(x,y)h_1(x,y), f_2(x,y) = g(x,y)h_2(x,y),$$

Then, every point where g(x,y) = 0 belongs to both  $C_1$  and  $C_2$ . In terms of sets, take  $D = \{g(x,y) = 0\}$ , and  $E_1 = \{h_1(x,y) = 0\}$ ,  $E_2 = \{h_2(x,y) = 0\}$ . We have

$$(21.10) C_1 = D \cup E_1, \quad C_2 = D \cup E_2,$$

and therefore

$$(21.11) C_1 \cap C_2 = D \cup (E_1 \cap E_2).$$

If D consists of infinitely many points, then the intersection  $C_1 \cap C_2$  is clearly infinite. Bézout's theorem says that this is the only exception:

THEOREM 21.5. (Bézout's theorem) Let  $C_1 = \{f_1(x,y) = 0\}$  and  $C_2 = \{f_2(x,y) = 0\}$  be algebraic curves of degrees  $d_1$  and  $d_2$ . Then,  $C_1$  intersects  $C_2$  in at most  $d_1d_2$  points, except in the following situation: (21.9) holds, where g(x,y) is such that  $D = \{g(x,y) = 0\}$  has infinitely many points, and  $h_1, h_2$  have no common factor (the last one is clear because we can move any common factor to g).

In the "except" situation, one can apply Bézout's theorem another time, to  $(h_1, h_2)$  (which have no common factor) to fully describe  $C_1 \cap C_2$ .

Example 21.6. Any curve of degree d intersects the curve  $\{x^3 + x - y^2 = 0\}$  in at most 3d points. In that case, the exceptional situation is impossible, because the degree 3 polynomial can't be factored.

Example 21.7. Suppose that  $C_1$  and  $C_2$  both have degree 3. Then, the cases break down as follows.

• (21.9) applies with g of degree 3. This means that  $h_1$  and  $h_2$  are constants, so  $f_1$  and  $f_2$  are multiples of each other:  $C_1 = C_2$ .

- (21.9) applies with g of degree 2. Then  $h_1, h_2$  are of degree 1, and have no common factor, so they are different lines. This means that  $E_1 = \{h_1 = 0\}$  and  $E_2 = \{h_2 = 0\}$ : the intersection  $E_1 \cap E_2$  is empty or a single point. In the end,  $C_1 \cap C_2 = D \cup (E_1 \cap E_2)$  consists of a conic D (which has infinitely many points) and at most one additional point.
- (21.9) applies with g of degree 1, so D = {g(x,y) = 0} is a line. Then h<sub>1</sub>, h<sub>2</sub> are of degree 2, and have no common factor. We can apply Bézout to (h<sub>1</sub>, h<sub>2</sub>), and find that E<sub>1</sub> ∩ E<sub>2</sub> is at most four points. So, C<sub>1</sub> ∩ C<sub>2</sub> consists of a line D and at most four additional points.
- Finally, there's the case where the "main branch" of Bézout applies, meaning  $C_1 \cap C_2$  consists of  $\leq 9$  points (this is what happens most of the time).

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 22. Nonsingular curves

Many, but not all, algebraic curves look like they are smoothly embedded (no kinks or selfinter-sections). Formally, these are the *nonsingular curves*.

- Topologically, a nonsingular curve consists of bounded components (which look like loops, called ovals) and unbounded ones (curves going to infinity at both ends).
- We discuss a number of basic results concerning the number and position of ovals, depending of course on the degree of the curve.

(22a) Nonsingular points. The circle  $x^2 + y^2 = 1$  is smooth, in a way in which the curves xy = 0 or  $x^3 + y^2 = 0$  are not. The mathematics behind that is:

DEFINITION 22.1. A solution (x,y) of f(x,y)=0 is called a singular point if the partial derivatives  $\partial_x f = \frac{\partial f}{\partial x}$  and  $\partial_y f = \frac{\partial f}{\partial y}$  are both zero at that point. Otherwise, it is called nonsingular. We say that the equation f(x,y)=0 is nonsingular if all of its solutions are nonsingular.

Often, we will say "C is a nonsingular curve of degree d". By this we mean that there is a degree d polynomial f(x,y) such that the equation f(x,y) = 0 is nonsingular and defines the curve C.

EXAMPLE 22.2. Take  $f(x,y) = p(x) - y^2$ . Then

(22.1) 
$$\begin{aligned} \partial_x f &= p'(x), \\ \partial_u f &= -2y. \end{aligned}$$

Therefore, a singular point is of the form (x,0), where p(x) = 0 and p'(x) = 0. The equation f(x,y) = 0 is nonsingular if and only if there are no such points.

Example 22.3. Take  $f(x,y) = f_1(x,y)f_2(x,y)$ . Then: any singular point of  $f_1(x,y) = 0$  is a singular point of f(x,y) = 0, and the same is true for  $f_2(x,y) = 0$ . Moreover: any point (x,y) where both  $f_1(x,y) = 0$  and  $f_2(x,y) = 0$  becomes a singular point of f(x,y) = 0. This is easy to see: the product rule says that

(22.2) 
$$\partial_x(f_1 f_2) = (\partial_x f_1) f_2 + f_1(\partial_x f_2), \\ \partial_y(f_1 f_2) = (\partial_y f_1) f_2 + f_1(\partial_y f_2).$$

If (x,y) is a singular point of  $f_1(x,y) = 0$ , then f inherits the vanishing of derivatives, so it becomes a singular point of f(x,y) = 0. The same holds for  $f_2(x,y) = 0$ . Moreover, if both  $f_1$  and  $f_2$  are zero at (x,y), then that also causes the partial derivatives (22.2) to vanish.

THEOREM 22.4. If f(x,y) = 0 is nonsingular, the curve  $C = \{f(x,y) = 0\}$  is a disjoint union of components of two kinds: bounded components, also called ovals, each of which can be traced out by an embedded loop; and unbounded components, which are embedded curves going off to infinity at both ends. On the two sides of any component, f(x,y) has opposite signs.

The main topological question is, how many components can there be, and arranged how?

Example 22.5. An equation f(x,y) = 0 of degree 2 is nonsingular exactly if the resulting curve is one of the following:

- an ellipse (one oval);
- a parabola (one unbounded component);
- a hyperbola (two unbounded components);
- two parallel lines (two unbounded components);
- the empty set (which satisfies "all points are nonsingular points of f(x,y) = 0" in the same sense as "all my Ferraris are green").

(22b) Degree 3 curves. A nonsingular curve of degree 3 must have at least one unbounded component; otherwise, it would be contained in a bounded subset of the plane, and we saw in the previous lecture that this is impossible.

Example 22.6. The curves below have one, two, or three unbounded components, and zero ovals:

(22.3) 
$$y = x^3$$
  $y(x^2 - 1) = 1$ 

These have one oval, and one, two or three unbounded components:

$$y^{2} = x^{3} - x$$

$$y(y - x^{2} + 1) = -1/6$$

$$y^{2}x = (x - 1)(x - 2)(x - 3)$$

It will turn out that these are the only possibilities!

Like any embedded loop, an oval divides the plane into a bounded (inside) and unbounded (outside) region. Therefore, any line through a point inside the oval must intersect that oval at least twice (since it goes towards infinity at both ends). One can use that and Bézout's theorem to show the following:

Proposition 22.7. A nonsingular algebraic curve of degree 3 has at most one oval.

Let's separate out one case, which is where the defining equation of our curve is a product of two polynomials, of degrees 1 and 2. Because of nonsingularity, the zero-sets of those two polynomials can't intersect (see Example 22.3), and the desired property is easy to see from the structure of lines and conics.

The main work goes into the other case, where the defining equation does not factor. We argue by contradiction: suppose that there are two ovals. They could be nested one inside the other, or not. In the nested case, we take a point lying inside the innermost oval. A line through that point must intersect each oval twice, yielding a total of four intersection points with the algebraic

curve. But that's impossible, by Bézout's theorem. Similarly, if the two ovals are not nested, we take one point inside each, and connect those two points by a line, with the same outcome.

Proposition 22.8. A nonsingular algebraic curve of degree 3 has at most three unbounded components.

Let's just consider the case where the defining equation is not a product. Each unbounded component goes out to infinity at both its ends. So, if we take a sufficiently large circle, the unbounded component will intersect that circle at least twice. If there are four unbounded components, this would give at least eight intersection points with a large circle, again contradicting Bézout's theorem.

(22c) Higher degrees. For the general discussion, we'll focus on the ovals. We'll need to know this:

Lemma 22.9. Suppose that C is a nonsingular algebraic curve. Take an oval  $O \subset C$ , a point p inside that oval, and another point q outside. If a conic goes through both p and q, it must intersect O at least twice.

If our conic is unbounded (a line, a union of two lines, a parabola, or a hyperbola), it's enough to have one point inside the oval; the previously used argument applies. This leaves the case of ellipses, where we use the fact that we have to travel from inside the oval to outside and then back.

PROPOSITION 22.10. A nonsingular algebraic curve of degree 4 can have at most 4 ovals. Moreover, if it has 2 ovals nested inside each other, then it can't have any other ovals.

Let's just consider the case where the defining polynomial is not a product. Suppose that we have two ovals nested inside each other, plus another oval. There are three possibilities for how the three ovals could be arranged:

All of those possibilities can be ruled out by a judicious choice of line, which produces more than 4 intersection points, hence violates the Bézout bound:

Similarly, suppose that we have at least 5 ovals, none of them nested inside each other. Pick a point inside each oval. We now appeal to interpolation (Lemma 19.5): there is a conic which goes through all 5 points. This conic will intersect each oval at least twice, by Lemma 22.9, so one gets at least 10 intersection points of the conic and the curve, which contradicts Bézout's theorem.

Theorem 22.11. (Harnack's theorem for the Euclidean plane) A nonsingular algebraic curve of degree d can have at most M ovals, where

(22.9) 
$$M = \begin{cases} \frac{d(d-3)}{2} + 2 & \text{if } d \text{ is even,} \\ \frac{d(d-3)}{2} + 1 & \text{if } d \text{ is odd.} \end{cases}$$

The proof follows the same idea as the d=3,4 cases, of constructing an auxiliary curve and applying Bézout's theorem.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 177

## 23. Singular points

Even though a randomly chosen algebraic curve will be nonsingular, the singular curves play a particular role in the theory.

- We will introduce the simplest class of singular points, called nodes (they are essentially the local minima, local maxima, and saddle points for functions of two variables, which are familiar from multivariable calculus).
- By slightly tweaking the defining polynomial, one can remove a node. This turns out to be a good way of constructing algebraic curves with interesting topological structure.
- (23a) Nodes. Take  $4x^3 3x y^2 = b$ , where b > 0 is a parameter:

The b = -1 case has a singular point. At that value, the structure of our curves changes: the b > -1 curves have an oval, but the b < -1 curves don't. This shows the importance of singular points for understanding the topology even of nonsingular curves.

The general setup is this. Given  $C = \{f(x, y) = 0\}$ , recall that a point  $(x_0, y_0)$  of C is a singular point if both f and its derivatives are zero at that point:

(23.2) 
$$f(x_0, y_0) = 0, \ (\nabla f)_{(x_0, y_0)} = 0.$$

The next step is to look at the symmetric matrix of second derivatives, the Hessian

(23.3) 
$$\operatorname{Hess}(f) = \begin{pmatrix} \partial_x^2 f & \partial_x \partial_y f \\ \partial_y \partial_x f & \partial_y^2 f \end{pmatrix}.$$

DEFINITION 23.1. A singular point is called a node if the Hessian  $H = \text{Hess}(f)(x_0, y_0)$  at that point has nonzero determinant. As you may remember from multivariable calculus, there are three sub-cases:

- If det(H) > 0 and the trace is tr(H) > 0, the point  $(x_0, y_0)$  is a local minimum of f. In that case,  $(x_0, y_0)$  sits by itself on C (there are no other points nearby, since f becomes positive).
- If det(H) > 0 and tr(H) < 0, the point  $(x_0, y_0)$  is a local maximum of f(x, y). Again,  $(x_0, y_0)$  sits by itself on C (the only difference being that f becomes negative nearby).
- If det(H) < 0,  $(x_0, y_0)$  is a saddle point. In this case, the local picture of C is that two branches cross transversally. The four nearby regions of the plane have different signs

of f, like this:

EXAMPLE 23.2. The b = -1 case of (23.1) has a node, which is a saddle point, at  $(x_0, y_0) = (1/2, 0)$ . To check that this is the case, we take  $f(x, y) = 4x^3 - 3x - y^2 + 1$ , and compute

(23.5) 
$$\nabla f = \begin{pmatrix} 12x^2 - 3 \\ -2y \end{pmatrix}, \quad \det(\operatorname{Hess}(f)) = -48x.$$

We have  $f(x_0, y_0) = 0$  (the point lies on the curve),  $(\nabla f)_{(x_0, y_0)} = 0$  (it's a singular point), and  $\det(\operatorname{Hess}(f)_{(x_0, y_0)}) = -24 < 0$  (it's a saddle point).

LEMMA 23.3. Take polynomials  $f_1(x, y)$  and  $f_2(x, y)$ . Let  $(x_0, y_0)$  be a solution both of  $f_1(x_0, y_0) = 0$  and  $f_2(x_0, y_0) = 0$  (geometrically, it's an intersection point of the resulting algebraic curves). Suppose that the gradient vectors  $\nabla f_1$ ,  $\nabla f_2$  at  $(x_0, y_0)$  are linearly independent. Then:

- for  $f(x,y) = f_1(x,y)f_2(x,y)$ , the equation f(x,y) = 0 has a node at  $(x_0,y_0)$ , which is a saddle point.
- for  $g(x,y) = f_1(x,y)^2 + f_2(x,y)^2$ , the equation g(x,y) = 0 has a node at  $(x_0,y_0)$ , which is a local minimum

That's geometrically intuitive, but one can also check it by explicit computation: the Hessian of f at  $(x_0, y_0)$  satisfies  $\det(\operatorname{Hess}(f)) = -(\nabla f_1 \times \nabla f_2)^2 < 0$ . For the Hessian of g, one gets  $\det(\operatorname{Hess}(g)) = 2(\nabla f_1 \times \nabla f_2)^2 > 0$ .

(23b) Perturbing nodes. What happens if, starting with an algebraic curve with a node, one slightly modifies the defining polynomial? Suppose that  $C = \{f(x, y) = 0\}$  has a node at  $(x_0, y_0)$ . Let g(x, y) be another polynomial such that  $g(x_0, y_0) \neq 0$ , and look at

(23.6) 
$$\tilde{C} = \{ f(x,y) = \epsilon g(x,y) \},$$

where  $\epsilon$  is a (sufficiently) small nonzero parameter.

• If f has a local minimum at  $(x_0, y_0)$ , depending on the signs, the singular point will either disappear or be replaced by a small oval:

(23.7) 
$$f(x,y) = \epsilon g(x,y) \qquad f(x,y) = 0 \qquad f(x,y) = \epsilon g(x,y)$$

$$\epsilon g(x_0,y_0) < 0 \qquad \epsilon g(x_0,y_0) > 0$$

• If f has a local maximum at  $(x_0, y_0)$ , the same happens, with switched signs:

(23.8) 
$$f(x,y) = \epsilon g(x,y) \qquad f(x,y) = 0 \qquad f(x,y) = \epsilon g(x,y)$$
 
$$\epsilon g(x_0,y_0) < 0 \qquad \qquad \epsilon g(x_0,y_0) > 0$$

• If f has a saddle point at  $(x_0, y_0)$ , two of the neighbouring regions will merge:

(23.9) 
$$f(x,y) = \epsilon g(x,y) \qquad f(x,y) = 0 \qquad f(x,y) = \epsilon g(x,y) \\ \epsilon g(x_0, y_0) < 0 \qquad \epsilon g(x_0, y_0) > 0$$

To understand this, one studies quadratic models, say f(x,y) = xy or  $x^2 + y^2$  or  $-x^2 - y^2$ , and takes g(x,y) to be a nonzero constant. This means that all we are doing is looking at the level sets of these quadratic functions. It's a good model for our problem because the Hessian gives the quadratic approximation near the singular point.

(23c) Applications. We can use this idea to construct algebraic curves with different shapes.

Example 23.4. Start with the union of two intersecting ellipses,

(23.10) 
$$f(x,y) = f_1(x,y)f_2(x,y),$$
$$f_1(x,y) = x^2 + 4y^2 - 1, \ f_2(x,y) = 4x^2 + y^2 - 1.$$

By perturbing this, we get a nonsingular degree 4 curve with 4 ovals (which is the maximal number allowed by Harnack's theorem):

(23.11) 
$$C = \{f(x,y) = 0\} \qquad \tilde{C} = \{f(x,y) = \epsilon\}$$

There are a number of other possible perturbations:

(23.12) 
$$\tilde{C} = \{f(x,y) = \epsilon\} \qquad \tilde{C} = \{f(x,y) = \epsilon x\}$$

Example 23.5. Take  $f_1, f_2$  as in the previous example, but now

(23.13) 
$$f(x,y) = f_1(x,y)^2 + f_2(x,y)^2.$$

This consists of just 4 points, but if we look at  $f(x,y) = \epsilon$  for some small  $\epsilon > 0$ , each point expands into a small oval. This gives another construction of a degree 4 curve with 4 ovals.

Finally, a warning is appropriate, which we have glossed over in the examples above. When perturbing to  $f(x,y) = \epsilon g(x,y)$ , we have explained what happens to nodes. Around a nonsingular point, the curve will move only a little (for sufficiently small  $\epsilon$ ), without changing its shape. However, but close to infinity (far out in the plane), it is possible that more drastic changes

might happen. In practice this means that you can control what happens in any given bounded subset of the plane (for instance, to produce a certain desired arrangement of ovals). However, if you want full information about the curve you've produced, you should at least look at a computer plot, to check that no undesirable effects have occurred near infinity (there are more rigorous arguments, but they're beyond our scope here). This is not a dramatic failure, since I think of this more as a discovery method; after all, we haven't specified what "small  $\epsilon$ " means quantitatively either.

Example 23.6. Take f(x,y) = y(y-1)x, which consists of two vertical lines and a horizontal line. This has two saddle point singularities. Take  $g(x,y) = x^2 + 1$ , and look at  $C = \{f(x,y) = \epsilon g(x,y)\}$  for small  $\epsilon > 0$ . From just thinking of the nodes, one might expect C to look like this:

and that's what happens near the nodes. However, if you zoom out far enough, you'll see that the overall shape of the curve looks like this instead:

By accident, while removing the nodes, we have also perturbed our two parallel lines to a (very thin) parabola!

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 185

## 24. Patchworking

Patchworking (invented by Viro) is another way of constructing nonsingular algebraic curves with prescribed topology. It involves polynomials whose coefficients are of vastly different sizes.

- The process is combinatorial and, in its basic version, very easy to carry out.
- It is another question altogether why it works; we'll only be able to give you some hints.

(24a) Patchworking. We look at polynomials in a very specific form, which depend on a parameter t > 0, thought of as small:

(24.1) 
$$f_t(x,y) = \sum_{i+j \le d} \sigma_{ij} t^{w_{ij}} x^i y^j.$$

Here,  $\sigma_{ij} \in \{\pm 1\}$  are signs that we can choose freely, and the powers of t are prescribed:

(24.2) 
$$w_{ij} = \frac{i(i-1)}{2} + \frac{j(j-1)}{2} + \frac{(i+j)(i+j-1)}{2}.$$

Take the triangle  $T_d$  with vertices (0,0), (d,0), (0,d); and decompose it into  $d^2$  smaller triangles, in the following specific way:

Each integer point (i, j) in  $T_d$  represents a monomial in  $f_t$ , and we mark it with the corresponding sign  $\sigma_{ij}$ . The markings below

correspond to

(24.5) 
$$f_t(x,y) = 1 - x - y + t^2x^2 - txy + t^2y^2 - t^6x^3 - t^4x^2y - t^4xy^2 - t^6y^3 + t^{12}x^4 - t^9x^3y + t^8x^2y^2 - t^9xy^3 + t^{12}y^4.$$

In the next step, if an edge of one of the small triangles connects two vertices with opposite signs, we mark a point on that edge:

Each of the small triangles has an even number (either 0 or 2) of edges with marked points. If there are 2 such marked points, we connect them by a line inside the small triangle:

The outcome is a "topologically correct" picture of  $\{f_t(x,y) = 0, x,y > 0\}$ , assuming t > 0 is chosen sufficiently small (I can't tell you how small, but as degrees get higher, this will need to be really tiny).

To capture the entire zero-set of  $f_t(x, y)$ , one applies the previous process to  $f_t(\pm x, \pm y)$ . Pictorially, it is convenient to reflect the original triangle and its decomposition along the coordinate axes, forming a diamond shape. To each integer point in that shape, one associates a sign, by starting with the original signs in the triangle, and applying the following rules.

- when reflecting along the vertical axis, reverse the signs of points (i,j) with odd i; and
- when reflecting along the horizontal axis, reverse the signs of points (i, j) with odd j.

This just expresses which monomials  $x^i y^j$  change signs under  $(x, y) \mapsto (-x, y)$  or  $(x, y) \mapsto (x, -y)$ . Finally, one draws lines as before:

We can now be a bit more explicit about what "topologically correct" means: the algebraic curve we are looking at is nonsingular, and the picture correctly describes the topology of each of its components (oval or unbounded), as well as how they are arranged with respect to each other. Of course, it represents those components as stick figure caricatures, but that's irrelevant. In our running example, the outcome is that  $f_t(x,y) = 0$ , for small t > 0, is a (nonsingular degree 4) curve with three ovals (not nested inside each other) and 4 unbounded components.

(24b) A one-variable analogue. Let's look at polynomials in one variable, again with a parameter t > 0, of a special form. Namely, we take  $\sigma_i \in \{\pm 1\}$ ,  $w_i = i(i-1)/2$ , and consider

$$(24.9) p_t(x) = \sigma_0 t^{w_0} + \sigma_1 t^{w_1} + \dots + \sigma_d t^{w_d} = \sigma_0 + \sigma_1 x + \sigma_2 t x + \sigma_3 t^3 x^3 + \dots$$

PROPOSITION 24.1. For small t,  $p_t$  has as many positive roots (solutions of  $p_t(x) = 0$  with x > 0) as there are sign changes in the sequence  $(\sigma_0, \ldots, \sigma_d)$ . More precisely, to each sign change  $\sigma_i \neq \sigma_{i+1}$  corresponds a root  $x \approx t^{-i}$ .

The similarity with patchworking becomes evident when we represent this graphically. Draw [0,d] subdivided into unit intervals, with the sign  $\sigma_i$  associated to the point i, and then insert a dot between  $\sigma_i$  and  $\sigma_{i+1}$  whenever their signs are opposite. Those dots represent the positive zeros of our polynomial. For instance, take

(24.10) 
$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

In this example, Proposition 24.1 says that there should be three positive roots, at  $x_1 \approx t^{-1}$ ,  $x_2 \approx t^{-3}$ ,  $x_3 \approx t^{-4}$ . Let's check this against the actual location of the positive roots (determined numerically, hence approximate):

|           |                                                                | $x_2$                | $x_3$                 |
|-----------|----------------------------------------------------------------|----------------------|-----------------------|
| $10^{-1}$ | $1.001 \cdot 10^{1}$                                           | $1.232 \cdot 10^3$   | $0.886 \cdot 10^4$    |
| $10^{-2}$ | $1.000 \cdot 10^2$                                             | $1.020 \cdot 10^{6}$ | $0.990 \cdot 10^{8}$  |
| $10^{-3}$ | $1.001 \cdot 10^{1}$ $1.000 \cdot 10^{2}$ $1.000 \cdot 10^{3}$ | $1.002 \cdot 10^9$   | $0.999 \cdot 10^{12}$ |

The advantage of the one-variable situation is that we can explain this phenomenon with a minimum of fuss. Let's look at our polynomial with the x-variable rescaled in a t-dependent way:

(24.11) 
$$p_t(x) \approx \sigma_0 + \sigma_1 x,$$

$$(x^{-1}t) p_t(t^{-1}x) \approx \sigma_1 + \sigma_2 x,$$

$$\dots$$

$$(x^{-i}t^{i(i+1)/2}) p_t(t^{-i}x) \approx \sigma_i + \sigma_{i+1} x.$$

Here,  $\approx$  means that we neglect terms with positive powers of t (thinking about the limit  $t \to 0$ , in which those become zero). If  $\sigma_0 \neq \sigma_1$ , then  $\sigma_0 + \sigma_1 x = 0$  has the obvious solution x = 1. In view of (24.11), one can then find a root of  $p_t(x)$ , for small t, with  $x \approx 1$ . Similarly, if  $\sigma_i \neq \sigma_{i+1}$ , then  $\sigma_i + \sigma_{i+1} x = 0$  has the solution x = 1, and therefore  $p_t(t^{-i}x) = 0$  has a solution  $x \approx 1$ , which means that  $p_t(x) = 0$  has a solution  $x \approx t^{-i}$ . This explains most of Proposition 24.1: that there are at least as many positive roots as there are sign-changes, and the approximate position of those roots. The rest, that there are no other positive roots, can be derived from a classical theorem (Descartes' rule of signs); we won't discuss that here.

The idea behind patchworking is the same: after a suitable t-dependent rescaling of (x, y)coordinates, one can approximate the polynomial by one with only three terms, whose zero-set is
a straight line. The union of those lines then gives a picture of  $\{f_t(x, y) = 0\}$ . While the details

are not as easy as in the one-variable case, what you should take away from this is that the pieces of the patchworked curve actually live at quite different scales in the (x, y)-coordinates (making ordinary graphing software totally ineffective).

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 25. Tropical geometry

On the face of it, tropical geometry is a new kind of algebraic geometry, where we replace the arithmetic operations by different and simpler ones. It is closely related to patchworking, for which it provides a more quantitatively accurate viewpoint.

- We introduce tropical arithmetic, tropical polynomials, and tropical algebraic curves.
- We relate them to ordinary arithmetic and ordinary algebraic curves, by taking logarithms with respect to large bases.

## (25a) The tropical numbers. The tropical numbers are

$$(25.1) \mathbb{R}_{\text{trop}} = \{-\infty\} \cup \mathbb{R},$$

but with different addition and multiplication operations:

(25.2) 
$$a \oplus b = \max(a, b),$$
$$a \odot b = a + b.$$

Since tropical multiplication is ordinary addition, the tropical multiplicative neutral element is the ordinary additive neutral element, meaning 0. The tropical additive neutral element is  $-\infty$ . Not all of the usual rules hold: there can't be tropical subtraction, since it's impossible to recover a from knowing b and  $\max(a, b)$ .

One can relate tropical numbers to ordinary nonnegative real numbers as follows. Fix some s > 0, thought of as being large. The correspondence is

(25.3) 
$$a \in \mathbb{R}_{\text{trop}} \longrightarrow x = s^a \in \mathbb{R}^{\geq 0},$$
$$a = \log_s(x) \in \mathbb{R}_{\text{trop}} \longleftarrow x \in \mathbb{R}^{\geq 0},$$

with the convention that  $s^{-\infty} = 0$  and  $\log_s(0) = -\infty$ . This is compatible with multiplications,

(25.4) 
$$\log_{\mathfrak{c}}(s^a \cdot s^b) = a + b = a \odot b.$$

It is also approximately compatible with additions, with an error that goes to 0 as  $s \to \infty$ :

LEMMA 25.1. For  $a, b \in \mathbb{R}^{\text{trop}}$ ,

(25.5) 
$$a \oplus b \le \log_s(s^a + s^b) \le a \oplus b + \frac{1}{s^{|a-b|} \ln(s)}.$$

The first inequality in (25.5) follows from the fact that  $\log_s$  is an increasing function. For the other one, it's enough to look at the case  $a \ge b$ . Using the fact that  $\ln(1+c) \le c$ , we then write

(25.6) 
$$\log_s(s^a + s^b) = \log_s(s^a(1 + s^{b-a})) = \log_s(s^a) + \log_s(1 + s^{b-a})$$
$$= a + \frac{\ln(1 + s^{b-a})}{\ln(s)} \le a + \frac{1}{s^{a-b}\ln(s)}.$$

Visually, it's eyecatching how the graph of  $\ln(e^a + e^b)$  bends to approximate  $\max(a, b)$ :

(25b) Tropicalization of polynomials. Take a polynomial in two variables, depending on an additional parameter s, of the form

(25.8) 
$$f_s(x,y) = \sum_{i+j \le d} s^{-w_{ij}} x^i y^j, \ w_{ij} \in \mathbb{Z}.$$

To find the tropical analogue of  $f_s$ , we replace: x with  $a = \log_s(x)$ ; y with  $b = \log_s(y)$ ; the powers  $s^{-w_{ij}}$  with the constants  $\log_s(s^{-w_{ij}}) = -w_{ij}$ ; and all arithmetic operations with their tropical counterparts:

(25.9) 
$$f_{\text{trop}}(a,b) = \bigoplus_{i+j \le d} \left( (-w_{ij}) \odot \underbrace{a \odot \cdots \odot a}_{i \text{ terms}} \odot \underbrace{b \odot \cdots \odot b}_{j \text{ terms}} \right).$$

In more concrete terms, this is a piecewise linear function:

(25.10) 
$$f_{\text{trop}}(a,b) = \max_{i+j \le d} \{ ia + jb - w_{ij} \}.$$

EXAMPLE 25.2. If 
$$f_s(x,y) = 1 + x + s^{-3}x^2y^2$$
, then  $f_{\text{trop}}(a,b) = \max\{0, a, 2a + 2b - 3\}$ .

The tropical version of  $f_s(x,y) = 0$  is  $f_{\text{trop}}(a,b) = -\infty$  (since  $-\infty$  is the additive unit in the tropical numbers). However, that's not particularly interesting in either context:  $f_s(x,y) = 0$  has no solutions with x,y > 0, and correspondingly  $f_{\text{trop}}(a,b) = -\infty$  has no solutions with  $a,b > -\infty$ . We therefore look at polynomials which have terms of either sign:

(25.11) 
$$f_s(x,y) = \sum_{i+j \le d} \sigma_{ij} s^{-w_{ij}} x^i y^j, \quad w_{ij} \in \mathbb{Z}, \ \sigma_{ij} \in \{\pm 1\}.$$

To tropicalize the equation  $f_s(x,y) = 0$ , we separate the polynomial into positive and negative terms,  $f_s(x,y) = f_s^+(x,y) - f_s^-(x,y)$ . Then, the algebraic curve associated to  $f_s$  can be written without subtraction as  $C_s = \{f_s^+(x,y) = f_s^-(x,y)\}$ . Its tropicalization is accordingly

(25.12) 
$$C_{\text{trop}} = \{(a,b) : f_{\text{trop}}^+(a,b) = f_{\text{trop}}^-(a,b)\}.$$

EXAMPLE 25.3. Take  $C_s = \{1 + x - y = 0\} = \{y = x + 1\}$ , which in this particular case is independent of s. In s-dependent coordinates  $x = s^a$ ,  $y = s^b$ , we get  $C_s = \{b = \log_s(s^a + 1)\}$ ,

which looks like this:

Compare this with  $C_{\text{trop}} = \{b = \max(a, 0)\}$ :

(25c) Tropical patchworking. Generally speaking, drawing  $C_{\text{trop}}$  can be quite complicated, as one has to figure out which of the many terms is the maximal one in  $f_{\text{trop}}^{\pm}(a,b)$  for any point (a,b). The situation becomes simpler if we take the exponents of s to be those from our previous discussion of patchworking,

(25.15) 
$$w_{ij} = \frac{i(i-1)}{2} + \frac{j(j-1)}{2} + \frac{(i+j)(i+j-1)}{2}.$$

In this case, the computation of maxima simplifies, leaving the following contributions to  $C_{\text{trop}}$ :

- for each (i, j) such that  $\sigma_{i+1,j} \neq \sigma_{i,j}$ , we get a piece of the vertical line a = 2i + j, which is the solution set of  $ai + bj + w_{ij} = a(i+1) + bj + w_{i+1,j}$ ;
- for each (i,j) such that  $\sigma_{i,j+1} \neq \sigma_{i,j}$ , we get a piece of the horizontal line b=i+2j, which is the solution set of  $ai+bj+w_{ij}=ai+b(j+1)+w_{i,j+1}$ ;
- for each (i, j) such that  $\sigma_{i+1, j-1} \neq \sigma_{i, j}$ , we get a piece of the diagonal line b-a = j-i-1, which is the solution set of  $ai + bj + w_{ij} = (a+1)i + (b-1)j + w_{i+1, j-1}$ .

It's useful to look at an example. Let's take a fairly simple one,

(25.16) 
$$f_s(x,y) = 1 - x - y + s^{-2}x^2 + s^{-1}xy + s^{-2}y^2.$$

Here is the picture of all the lines listed above, with the actual  $C_{\text{trop}}$  marked in bold:

We can compare it with the actual algebraic curve in log coordinates. Let's introduce the notation

(25.18) 
$$\operatorname{Log}_s : (\mathbb{R}^{\geq 0})^2 \longrightarrow (\{-\infty\} \cup \mathbb{R})^2, \\ \operatorname{Log}_s(x, y) = (\operatorname{log}_s(x), \operatorname{log}_s(y)).$$

Then,  $\operatorname{Log}_s(C_s \cap (\mathbb{R}^{\geq 0})^2)$  looks like this (for s large, in this case s=100):

Moreover, if we set  $s = t^{-1}$ , then  $C_t$  is an example of patchworking according to this diagram:

What this example reveals is actually part of a general pattern.  $C_{\rm trop}$  is a modified version of the patchworking diagram; both are essentially combinatorial (stick-figure) objects, and one can go back and forth between them, without affecting the qualitative (topological) structure. Secondly, as one would guess from our discussion of the relation between ordinary and tropical numbers:

THEOREM 25.4. In the situation of (25.15), we have that as  $s \to \infty$ ,

(25.21) 
$$\operatorname{Log}_{s}(C_{s} \cap (\mathbb{R}^{\geq 0})^{2}) \longrightarrow C_{\operatorname{trop}}.$$

In words, take the part of  $C_s$  where (x,y) are nonnegative, and look at it in logarithmic coordinates with base s. Then, as s goes to infinity, this converges to the corresponding tropical curve. We will leave the statement imprecise, by not explaining what notion of convergence appears here. The important point is that tropicalization can serve as an intermediate notion between the patchworking diagram and the actual algebraic curve, and thereby provides us with a better understanding of patchworking itself.

Example 25.5. Take (24.5), but replacing (x,y) by (-x,-y), and setting  $s=t^{-1}$  as before, which means

$$C_{s} = \left\{1 + x + y + s^{-2}x^{2} - s^{-1}xy + s^{-2}y^{2} + s^{-6}x^{3} + s^{-4}x^{2}y + s^{-4}xy^{2} + s^{-6}y^{3} + s^{-12}x^{4} - s^{-9}x^{3}y + s^{-8}x^{2}y^{2} - s^{-9}xy^{3} + s^{-12}y^{4} = 0\right\},$$

$$C_{\text{trop}} = \left\{\max\{0, a, b, 2a - 2, 2b - 2, 3a - 6, 2a + b - 4, a + 2b - 4, 3b - 6, 4a - 12, 2a + 2b - 8, 4b - 12\right\} = \max\{a + b - 1, 3a + b - 9, a + 3b - 9\}\right\}.$$

We draw the patchworking diagram, which is a rotated version of the bottom left quadrant in (24.8), alongside  $C_{\text{trop}}$  and  $\text{Log}_s(C_s)$  (for s = 1000):

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 26. Projective geometry

A century ago, there might have been an entire course in projective geometry! Here, two lectures is all we have time for.

- We define points and lines in the projective plane, and explain how they are related to standard planar geometry.
- We look at some properties of projective geometry, including a surprising duality between points and lines.

(26a) The projective plane. The projective plane, written here as  $\mathbb{P}^2$ , is made up of the following:

DEFINITION 26.1. A projective point  $p \in \mathbb{P}^2$  is a triple [x:y:z], where  $(x,y,z) \in \mathbb{R}^3$  cannot all be zero, and with the convention that [x:y:z] and [tx:ty:tz] are the same point, for all  $t \neq 0$ . The [x:y:z] are called homogeneous coordinates, and we use the [::] notation to remind ourselves that this denotes a projective point.

One can think of projective points as lines through the origin in  $\mathbb{R}^3$ . The point [x:y:z] corresponds to the line in  $\mathbb{R}^3$  consisting of all multiples of the vector (x,y,z). That explains why we can't have [0:0:0] (not a line in space), and also why [x:y:z] and [tx:ty:tz] are the same point (they give the same line in space). The relation with ordinary plane geometry is done as follows:

- Each point (x, y) in  $\mathbb{R}^2$  becomes a projective point  $[x : y : 1] \in \mathbb{P}^2$ . This gets you all those projective points whose homogeneous z-coordinate is nonzero, because [x : y : z] = [x/z : y/z : 1] for  $z \neq 0$ .
- The remaining projective points p = [x : y : 0], which do not belong to the Euclidean plane, are called *points at infinity*. A point at infinity corresponds to a line through the origin in  $\mathbb{R}^2$ . More intuitively, one can think of points at infinity as corresponding to directions in  $\mathbb{R}^2$ , but where a direction and its opposite give the same point at infinity.

With that in mind, one can draw the projective plane qualitatively as follows:

Even though the idea of "points at infinity" is helpful for visualizing things, within projective geometry itself, this is not a natural distinction: any projective point is as good as any other one.

DEFINITION 26.2. Take  $(a,b,c) \neq (0,0,0)$ . A projective line  $L \subset \mathbb{P}^2$  consists of all p = [x:y:z] which solve the equation ax + by + cz = 0.

We can think of projective points as lines in  $\mathbb{R}^3$ , and correspondingly of projective lines as planes through the origin in  $\mathbb{R}^3$ , whic consist of all solutions (x, y, z) of ax + by + cz = 0. Then, a projective point p lies on a projective line L iff the line in  $\mathbb{R}^3$  corresponding to p is contained in the plane corresponding to p. Again, there's a relation with the standard geometry of  $\mathbb{R}^2$ , with one exception:

- Suppose that  $(a, b) \neq (0, 0)$ . In that case, the associated projective line consists of points [x:y:1] which satisfy ax + by + c = 0, which is an ordinary line in  $\mathbb{R}^2$ ; together with one point at infinity, which is the unique solution [x:y:0] of ax + by = 0. We say that this projective line is the completion of ax + by + c = 0.
- if (a,b) = (0,0), we have the line at infinity z = 0, which consists of all points at infinity.

FACT 26.3. Through any two (different) projective points, there is a exactly one projective line.

In terms of  $\mathbb{R}^3$ , this means that if we take two different lines through the origin, then they lie on a uniquely determined common plane. While the same property holds in the Euclidean plane, the following statement wouldn't:

FACT 26.4. Any two (different) projective lines intersect in exactly one projective point.

In terms of  $\mathbb{R}^3$ , this means that if we take two different planes through the origin, their intersection is a line through the origin. From a viewpoint of standard plane geometry, this result looks like this:

- if you have two lines in  $\mathbb{R}^2$  which are not parallel, their projective completions have different points at infinity. So the intersection of the completions still consists of one point in  $\mathbb{R}^2$ .
- If you have two parallel lines in  $\mathbb{R}^2$ , their projective completions have the same point at infinity, where they intersect.
- Finally, if we take the projective completion of a line in  $\mathbb{R}^2$ , that always intersects the line at infinity in one point.

(26b) **Duality.** There is a general principle, called *projective duality*, which allows us to switch the role of lines and points. The idea is very simple: we switch the line  $L = \{ax + by + cz = 0\}$  with the point p = [a:b:c], and vice versa. If one thinks of projective points and lines as linear subspaces of  $\mathbb{R}^3$ , then duality consists of passing to the orthogonal complement. With that in mind, we write  $p^{\perp}$  for the dual (projective line) to the point p, and p for the dual (point) of the projective line p. Duality has the following property:

(26.2) 
$$p \text{ lies on } L \Leftrightarrow L^{\perp} \text{ lies on } p^{\perp}.$$

Example 26.5. If I take a point

$$(26.3) (a,b) \in \mathbb{R}^2, (a,b) \neq (0,0),$$

that becomes p = [a:b:1] in the projective plane, which is the line in  $\mathbb{R}^3$  consisting of multiples of (a,b,1). Its dual is  $\{ax+by+z=0\}$ , which is the projective completion of

$$(26.4) ax + by + 1 = 0.$$

In contrast, if I take the origin (0,0) in  $\mathbb{R}^2$ , then the dual is the line at infinity  $\{z=0\}$ .

A classical application of duality is to configurations of points and lines.

DEFINITION 26.6. Let  $c, \gamma, l, \lambda$  be integers, such that  $c\lambda = l\gamma$ . A  $(c_{\lambda}l_{\gamma})$  configuration consists of c (different) points and l (different) lines in the projective plane, such that: each of the c points lies on exactly  $\lambda$  of the l lines; and each of the l lines contains exactly  $\gamma$  of the c points. (A configuration doesn't need to contain all the lines connecting its points, nor all the intersection points of its lines.)

Example 26.7. A complete quadrilateral consists of four lines, no three of which meet in a common point, and the 6 points in which two of those lines intersect. This is a  $(6_24_3)$  configuration.

EXAMPLE 26.8. Here's a  $(9_39_3)$  configuration constructed starting from the points  $(p_1, p_2, p_3)$  which are collinear (lie on the same line), and three more points  $(q_4, q_5, q_6)$  which are also collinear (for a different line). We connect  $p_i$  with  $q_j$  for all  $i \neq j$ , adding 6 more lines. Pappus' theorem from geometry tells us that the intersection points  $r_1, r_2, r_3$  are collinear, which yields the required ninth line in the configuration.

The theory of configurations asks for what  $(p, \lambda, l, \beta)$  a configuration exists; and if there are ones with the same  $(p, \lambda, l, \beta)$  that are combinatorially or geometrically different from each other. This is best done in the projective plane, to avoid having to deal separately with the case of parallel lines.

Proposition 26.9. If we take a  $(c_{\lambda}l_{\gamma})$  configuration, and apply projective duality to all its points and lines, we get an  $(l_{\gamma}c_{\lambda})$  configuration.

Example 26.10. The dual of a complete quadrilateral is a  $(4_36_2)$  configuration: it consists of 4 points, no three of which are collinear, and all possible lines through two of those points.

(26.7)

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 27. Algebraic curves in the projective plane

So far, all we've seen from projective geometry are points and lines.

- One can talk about projective algebraic curves, and this helps us understand the behaviour of ordinary algebraic curves (as they go out to infinity).
- There is a notion of nonsingularity for projective algebraic curves, and a corresponding version of Harnack's theorem. This situation is actually simpler than the case of  $\mathbb{R}^2$ , since we no longer have to distinguish between ovals and unbounded components.

(27a) Projective completion. A homogeneous polynomial of degree d, in variables (x, y, z), is an expression of the form

(27.1) 
$$g(x, y, z) = \sum_{i+j+k=d} b_{ijk} x^i y^j z^k = 0,$$

where the coefficients  $(b_{ijk})$  are not all zero. Note the i+j+k=d condition here, every monomial has degree d. As a consequence,

(27.2) 
$$q(tx, ty, tz) = t^d q(x, y, z),$$

In particular, whether g(x, y, z) is zero or not depends only on the projective point p = [x : y : z].

DEFINITION 27.1. Let g(x, y, z) be a homogeneous polynomial of degree d. Then, the set  $D \subset \mathbb{P}^2$  of those points  $p = [x : y : z] \in \mathbb{P}^2$  where g(x, y, z) = 0 is called a projective algebraic curve of degree d.

Suppose that f(x,y) is a polynomial of degree d (not homogeneous), hence defines an algebraic curve  $C \subset \mathbb{R}^2$ . We can insert powers of z to make the polynomial homogeneous:

(27.3) 
$$f(x,y) = \sum_{i+j \le d} a_{ij} x^i y^j \implies g(x,y,z) = \sum_{i+j \le d} a_{ij} x^i y^j z^{d-i-j}.$$

This defines a projective curve  $D \subset \mathbb{P}^2$ . As in the case of lines, we call this process *projective* completion. If we think of  $\mathbb{P}^2$  as the union of  $\mathbb{R}^2$  and the line at infinity, then D consists of C together with certain points at infinity. Those points at infinity are

(27.4) 
$$D \setminus C = \{ [x:y:0] : h(x,y) = 0 \}, \text{ where } h(x,y) = \sum_{i+j=d} a_{ij} x^i y^j.$$

In words, the points at infinity are defined using only those monomials in f(x, y) which are of degree exactly d.

EXAMPLE 27.2. Let's look at what happens to certain kinds of conics in  $\mathbb{R}^2$  under projective completion. We'll do this by example, but the behaviour only depends on the type of conic we're considering.

| type                  | example          | $  \ projective$   | equation for       | $  points \ at \infty$ |
|-----------------------|------------------|--------------------|--------------------|------------------------|
|                       |                  | completion         | points at $\infty$ |                        |
| ellipse               | $x^2 + 2y^2 = 1$ | $x^2 + 2y^2 = z^2$ | $x^2 + 2y^2 = 0$   | none                   |
| parabola              | $y = x^2$        | $yz = x^2$         | $0 = x^2$          | [0:1:0]                |
| hyperbola             | xy = 1           | $xy = z^2$         | xy = 0             | [1:0:0], [0:1:0]       |
| $parallel\ lines$     | x(x-1) = 0       | x(x-z) = 0         | $x^2 = 0$          | [0:1:0]                |
| $intersecting\ lines$ | xy = 0           | xy = 0             | xy = 0             | [1:0:0], [0:1:0]       |

The parabola has only one point at  $\infty$ , because its two ends go to  $\infty$  in approximately the same direction. So do the two parallel lines, because if we go to  $\infty$  in opposite directions, so end up at the same point of  $\mathbb{P}^2$ , by definition. One sees intuitively how this differs from the behaviour of the hyperbola and the intersecting lines.

Example 27.3. The projective completion of xy(x+y)=1 is  $xy(x+y)=z^3$ . The points at infinity are solutions of xy(x+y)=0. There are three of them, [1:0:0], [0:1:0], [1:-1:0]. This is clearly visible in the picture of the curve in  $\mathbb{R}^2$ , where there are three pairs of opposite directions in which the curve goes off to  $\infty$ :

Example 27.4.  $x^4 + y^2 + 1 = 0$  has no solutions in  $\mathbb{R}^2$ , but the projective completion is  $x^4 + y^2z^2 + z^4 = 0$ , which has the single solution [x:y:z] = [0:1:0]. The appearance of this point at infinity has no geometric motivation, but algebra rules here and we follow that.

(27b) Nonsingular curves. Take a homogeneous equation g(x, y, z) = 0. We say that a solution [x : y : z] is singular if the gradient  $(\nabla g)_{(x,y,z)}$  is zero; otherwise, it's nonsingular. The equation is called nonsingular if all its solutions are nonsingular points. If we take an ordinary plane curve f(x,y) = 0 and projectively complete to g(x,y,z) = 0, then the notion of nonsingularity for points [x : y : 1] agrees with the one we had defined before (by a computation which we omit). However, one still has to look at the points at infinity!

Example 27.5. Let's return to our collection of conics.

| type                  | projective     | gradient    | points at $\infty$ | are the points         |
|-----------------------|----------------|-------------|--------------------|------------------------|
|                       | completion     |             |                    | $at \propto singular?$ |
| parabola              | $yz - x^2 = 0$ | (-2x,z,y)   | [0:1:0]            | nonsingular            |
| hyperbola             | $xy - z^2 = 0$ | (y,x,-2z)   | [1:0:0], [0:1:0]   | non singular           |
| $parallel\ lines$     | x(x-z) = 0     | (2x-z,0,-x) | [0:1:0]            | singular               |
| $intersecting\ lines$ | xy = 0         | (y, x, 0)   | [1:0:0], [0:1:0]   | non singular           |

The projective completions of the ellipse, parabola and hyperbola are nonsingular projective algebraic curves. In the second-to-last case, the point at infinity where the completions of the two

parallel lines cross becomes a singular point. One could say that our original curve is "singular at infinity".

LEMMA 27.6. Let f(x,y) be a polynomial of degree d. If the projective completion of the associated curve has exactly d points at infinity, then those points must be nonsingular.

To see that, let's suppose for simplicity that [1:0:0] is not a point at infinity. With notation as in (27.3), look at this:

(27.6) 
$$p(x) = g(x, 1, 0) = \sum_{i+j=d} a_{ij} x^{i}.$$

p(x) is a polynomial of degree  $\leq d$ , and not identically equal to zero. By assumption, it has d roots x, which correspond to the points at infinity [x:1:0] of our completion. In that case, we necessarily have  $p'(x) \neq 0$  at each root. Because

$$(27.7) p'(x) = (\nabla g)_{(x,1,0)} \cdot (1,0,0),$$

this means that the gradient is nonzero at each such point.

THEOREM 27.7. A nonsingular projective curve consists of a finite number of projective ovals (which one can think of as parametrized by embedded loops in  $\mathbb{P}^2$ ).

While making the notion of embedded loop in  $\mathbb{P}^2$  rigorous would require quite a bit of work, the geometric intuition isn't that hard: it's a loop in the plane that can go off to infinity in some direction, and then either come back or re-emerge in the opposite direction. Here's such a loop, which with four points at infinity (three where it crosses the line at infinity, and one where it just touches).

Example 27.8. Take the projective completion of an ellipse, a parabola, or a hyperbola. Each has exactly one projective oval! In fact, from the point of view of projective geometry, they all look the same.

EXAMPLE 27.9. The completion of the curve from Example 27.3 is nonsingular (by Lemma 27.6), and has only one projective oval. One sees that just by following along as it goes through the points at infinity.

Many of the results we have discussed for algebraic curves in  $\mathbb{R}^2$  have better-behaved projective analogues. Here's Harnack's theorem:

THEOREM 27.10. A nonsingular projective curve of degree d consists of at most d(d-3)/2 + 2 ovals.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 28. Delaunay triangulations

We consider decompositions of a convex polygonal region into triangles, using a prescribed set of points as vertices of the triangles.

- We motivate the issue through numerical integration (kept to its simplest form).
- In any given example, many different such "triangulations" exist, related to each other by sequences of local transformations.
- The Delaunay condition describes triangulations that avoid thin triangles.
- Going back to applications, we explain how one can use this to think of finite point sets in the plane as tracing out a geometric shape.

(28a) Numerical integration. Take a function of one variable, f(x). We want an approximate formula for  $\int_a^b f(x) dx$ , based only on knowing finitely many values  $f(x_1), \ldots, f(x_n)$ , where  $a = x_1 < x_2 < \cdots < x_n = b$ . The simplest solution is the trapezoid rule

(28.1) 
$$\int_{a}^{b} f(x) dx \approx \frac{1}{2} (f(x_2) + f(x_1))(x_2 - x_1) + \frac{1}{2} (f(x_3) + f(x_2))(x_3 - x_2) + \cdots .$$

You have probably seen this before, at least in the case where  $x_1, \ldots, x_n$  are equally spaced. Now, let's look at the corresponding problem for functions of two variables.

(28.2) We are given points  $v_1 = (x_1, y_1), \dots, v_n = (x_n, y_n)$ ; no two are equal, and they do not all lie on the same straight line.

DEFINITION 28.1. The convex hull of  $(v_1, \ldots, v_n)$  is the smallest convex polygon P which contains all those points. (The vertices of P will be a subset of the  $v_i$ .)

For functions f(x, y) defined on the convex hull P, we want an approximate formula for  $\int_P f$  in terms of the values  $f(v_i)$ . It's easy to find such a formula if, say, P is a rectangle and the  $v_i$  form a grid; but that may not be true in applications. One way to approach this is to decompose P into triangles. More precisely:

DEFINITION 28.2. A triangulation of P, with vertices  $(v_1, \ldots, v_n)$ , is a decomposition into non-overlapping triangles, such that all the  $v_i$ , and no other points, appear as vertices of those triangles.

Given such a triangulation, the analog of the trapezoid rule is:

(28.3) 
$$\int_P f(x,y) \, dx \, dy \approx \sum_T \operatorname{area}(T) (\text{average value of } f \text{ at the three vertices of } T).$$

Here, the sum is over the triangles in the triangulation. The vertices of each triangle belong to our  $(v_1, \ldots, v_n)$ , so the overall formula is a weighted sum of  $f(v_i)$ . Different choices of triangulations give different approximate answers, some better than others.

EXAMPLE 28.3. Take the points (x,y) = (0,0), (2,0), (4,1), (0,4), (1,3), (4,4). In the picture below, the triangulation on the left has triangles that are very long and thin, and we suspect that it's not a good choice. The triangulation on the right looks better in that respect:

(28b) Different triangulations. We can change a triangulation by a *flip*, applied to a pair of neighbouring triangles which form a convex quadrilateral:

$$(28.5)$$

Some topological facts:

- Any finite set of points admits a triangulation (boring).
- Any two triangulations of the same set of points have the same number of triangles (interesting).
- Any two triangulations of the same point set can be related by a sequence of flips (even more interesting).

Example 28.4. One can get from one triangulation in (28.4) to the other by two flips:

DEFINITION 28.5. A triangulation is Delaunay if, when we take the circumcircle of any triangle in it (the unique circle going through its vertices), no point of our set lies inside that circle. To clarify: "inside" means in the interior. It is ok for a Delaunay triangulation if more points of our set lie on the circumcircle itself.

The key property is:

Theorem 28.6. For every finite set of points as in (28.2), there is a Delaunay triangulation.

For instance, the triangulation on the right in (28.4) is Delaunay, but that on the left isn't. Moreover, there is an algorithm which, starting from any triangulation, produces a Delaunay triangulation in finitely many flip steps. Namely, suppose that we have two adjacent triangles which together form a convex quadrilateral, and which by themselves (as a triangulation of that quadrilateral, forgetting all the other points) fail to obey the Delaunay condition. Then, we flip; and repeat that until that's no longer possible. Why does this work, and not, for instance, cycle endlessly?

LEMMA 28.7. Suppose we have two adjacent triangles which form a convex quadrilateral and, by themselves, are not Delaunay. Apply a flip. Then, the new triangulation gives an approximate formula for  $\int_{\mathbb{R}} x^2 + y^2$  which is less than that for the original triangulation.

This is a small nifty piece of geometry, which we won't explain here. Given that, the flip algorithm can never cycle back to a previous choice of triangulation; and because there are only finitely many possible triangulation of our given point set, it must eventually end in a situation where no further such moves are available. This means that for any two adjacent triangles which form a convex quadrilateral, Delaunay holds. By a further geometric argument, it then follows that the entire triangulation is Delaunay. Next, what can we say abou how many Delaunay triangulations a fixed set of points can have?

Theorem 28.8. Suppose that T is a triangle whose vertices belong to our point set, and with the following property (which is stronger than what's in the definition of Delaunary triangulation): all the other points in our finite set lie outside (in the exterior of) the circumcircle of the triangle. Then, T occurs in every possible Delaunay triangulation.

In particular, if no four points in our set lie on the same circle, the Delaunay triangulation is unique (because then, the Theorem applies to any triangle in it).

(28c) The topology of data. Suppose that we have a finite set of points in the plane, which are the result of some measurement or sampling process. I would like assign an overall shape to this "point cloud", as if looking at it with my glasses off:

$$(28.7) \qquad \qquad \stackrel{?}{\longrightarrow} \bigcirc$$

There are many ways of doing this, all depending on a choice of scale  $\sigma > 0$  to do the blurring. Let's say that we want a computational (polygonal) flavour. Here's a particularly simple approach. First, form the Delaunay triangulation (let's assume for simplicity that there's a unique one). Draw the original point set, together with all the edges in the triangulation which are of length  $< \sigma$ , and finally those triangles from our triangulations all of whose edges have length  $< \sigma$ . Let's call the union of all that the *shape complex* of the point set, at scale  $\sigma$ . If we take  $\sigma$  small (smaller than the distance between any two points), the shape complex just consists of the original points. If we take  $\sigma$  large (larger than any of the distances), we are being told to add all edges and all triangles, so the outcome is just the convex hull P. Obviously, the right choice of scale (somewhere between those two extremes) is important, in order for the outcome to be meaningful.

 $\begin{tabular}{lllllllllllllllllllllllllllllllllll$ 

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 29. Betti numbers

We have mentioned shape complexes, but we didn't explain the meaning of the word "complex". What's going on is that any triangulation is an example of the much more general notion of planar complex. A planar complex is a collection points, edges (line segments), and triangles in the plane. In this lecture,

- We introduce planar complexes, and their Euler characteristic;
- we encode the combinatorial structure of such a complex in its boundary operators (which are matrices, so, get ready for some linear algebra);
- from those matrices, we extract some more interesting topological invariants, the Betti numbers.

(29a) Combinatorial data. A planar complex is: a finite collection of points; plus, a finite collection of edges (line segments); plus, a finite collection of triangles, all of it in the plane, and subject to a bunch of rules:

- If an edge is part of our complex, then both of its endpoints are part of the complex.
- If a triangle is part of our complex, then all three sides are edges that are also part of the complex.
- Otherwise, no overlaps, no intersections!

It may be easiest first to think of the case where there are only points and edges. Then, a planar complex is just a graph drawn in the plane (with straight edges that don't intersect). To make a general complex, we fill in some (could be none, all, or any subset of them) triangle-shaped regions created by that graph. Here's an example and some non-examples:

DEFINITION 29.1. Suppose that a planar complex K consists of  $n_0$  points,  $n_1$  edges, and  $n_2$  triangles. Its Euler characteristic  $\chi = \chi(K)$  is

$$(29.2) \chi = n_0 - n_1 + n_2.$$

Given that the Euler characteristic contains so little information about our complex (it only knows how many pieces of each dimension there are, not how they are arranged), it's surprising that it is of any importance at all!

(29b) Boundary operators. What if we were programmers, and wanted to encode the combinatorial structure of a complex? We could do it like this.

- Number the points by  $\{1, \ldots, n_0\}$ .
- Every edge can be described by its pair (i, j) of endpoints, for  $1 \le i < j \le n_0$ . Record all the edges in our complex by pairs  $(i_1, j_1), \ldots, (i_{n_1}, j_{n_1})$ .
- Every triangle can be described by its triple (p, q, r) of vertices, for  $1 \le p < q < r \le n_0$ . Record all the triangles in our complex by triples  $(p_1, q_1, r_1), \ldots, (p_{n_2}, q_{n_2}, r_{n_2})$ .

Next, we turn the combinatorial data into a pair of matrices, the so-called boundary operators  $D_1$  and  $D_2$  of the complex.

 $D_1$  is a matrix with  $n_0$  rows and  $n_1$  columns, which means that rows are labeled by points and columns are labeled by edges (the triangles are irrelevant for  $D_1$ ). Each column vector contains one entry with -1 and one entry with 1, all other entries being zero. Namely, if the column corresponds to an edge (i, j), the i-th entry is -1 and the j-th entry is 1.

Example 29.2. This is the complex obtained from a triangulation of a pentagon:

$$(29.3)$$

It has  $n_0 = 5$ ,  $n_1 = 7$ ,  $n_2 = 3$  (hence  $\chi = 1$ ). The edges are

$$(29.4) (1,2), (1,3), (1,4), (1,5), (2,3), (3,4), (4,5).$$

Therefore,

(29.5) 
$$D_{1} = \begin{pmatrix} -1 & -1 & -1 & 0 & 0 & 0 \\ 1 & 0 & 0 & 0 & -1 & 0 & 0 \\ 0 & 1 & 0 & 0 & 1 & -1 & 0 \\ 0 & 0 & 1 & 0 & 0 & 1 & -1 \\ 0 & 0 & 0 & 1 & 0 & 0 & 1 \end{pmatrix}.$$

 $D_2$  is a matrix with  $n_1$  rows and  $n_2$  columns, which means that rows are labeled by edges and columns are labeled by triangles. Each column vector contains two 1 entries and one -1 entry. Namely, if the column corresponds to a triangle (p, q, r), then the entries corresponding to the edges (p, q) and (q, r) are marked 1, and the entry corresponding to (p, r) is marked -1.

Example 29.3. For (29.3), the triangles are

$$(29.6) (1,2,3), (1,3,4), (1,2,5).$$

The first triangle has edges (1,2), (2,3) and (1,3), which are numbers 1, 5 and 2 in the ordering from (29.4). This determines where to put the nonzero entries in the first column of  $D_2$ . Taking this and the other two triangles into account, we get:

(29.7) 
$$D_2 = \begin{pmatrix} 1 & 0 & 0 \\ -1 & 1 & 0 \\ 0 & -1 & 1 \\ 0 & 0 & -1 \\ 1 & 0 & 0 \\ 0 & 1 & 0 \\ 0 & 0 & 1 \end{pmatrix}.$$

When writing down the matrices, we have implicitly chosen to order the edges and triangles in some way. We'll use lexicographic ordering, but that doesn't really matter. What matters is that when choosing the order in which the edges appear, you need to use the same one for  $D_1$  and  $D_2$  (as we've done in the examples above).

Fact 29.4. The boundary operators always satisfy  $D_1D_2 = 0$  (the zero matrix).

(29c) Betti numbers. Remember that the rank of a matrix A is the maximal number of linearly independent columns that you can find. It is also the maximal number of linearly independent rows, which means that a matrix and its transpose have the same rank:

(29.8) 
$$\operatorname{rank}(A^t) = \operatorname{rank}(A).$$

The nullity of a matrix is the maximal number of linearly independent vectors w which solve Aw = 0, the linear system of equations determined by A. The rank-nullity theorem relates the two notions:

(29.9) if A is a matrix with n columns, 
$$rank(A) + nullity(A) = n$$
.

DEFINITION 29.5. The Betti numbers  $b_0 = b_0(K)$ ,  $b_1 = b_1(K)$ ,  $b_2 = b_2(K)$ , are defined by

(29.10) 
$$b_0 = n_0 - \operatorname{rank}(D_1),$$

$$b_1 = n_1 - \operatorname{rank}(D_1) - \operatorname{rank}(D_2),$$

$$b_2 = n_2 - \operatorname{rank}(D_2).$$

Note that the alternating sum of the Betti numbers is the Euler characteristic:

$$(29.11) b_0 - b_1 + b_2 = n_0 - n_1 + n_2 = \chi.$$

The Betti numbers are nonnegative integers. To see that, we use the linear algebra facts above:

(29.12) 
$$b_0 = n_0 - \operatorname{rank}(D_1^t) = \operatorname{nullity}(D_1^t),$$
$$b_1 = \operatorname{nullity}(D_1) - \operatorname{rank}(D_2),$$
$$b_2 = \operatorname{nullity}(D_2).$$

From that, it's clear that  $b_0 \ge 0$  and  $b_2 \ge 0$ . What about  $b_1$ ? Because  $D_1D_2 = 0$ , every column of  $D_2$  is a solution of  $D_1w = 0$ , so there are at least as many linearly independent solutions as column vectors, which means that  $\text{nullity}(D_1) \ge \text{rank}(D_2)$ .

Example 29.6. In (29.5), the last four rows are clearly linearly independent. On the other hand, if we add up all the rows we get zero (something that's always true for  $D_1$ ), so the first row is minus the sum of the others. It follows that  $rank(D_1) = 4$ . In (29.7), the three columns are clearly linearly independent, so  $rank(D_2) = 3$ . Therefore, the Betti numbers are

$$(29.13) b_0 = 5 - 4 = 1, b_1 = 7 - 4 - 3 = 0, b_2 = 3 - 3 = 0.$$

It will take us a while to understand what Betti numbers mean, but here's a start:

Theorem 29.7.  $b_0$  is the number of components (parts not connected to each other) of the complex.

To understand that, think of what  $D_1^t w = 0$  means. The vector w assigns to each vertex in our complex a real number. For each edge, the corresponding coefficient of  $D_1^t w$  is the difference of the coefficients of w assigned to the endpoints of that edge. Therefore,  $D_1^t w = 0$  says that whenever two vertices are connected by an edge, they carry the same number. So, a solution  $D_1^t w = 0$  must assign the same value to all vertices in a given component, and there are no other constraints. In other words, such a solution is given by choosing a real number for each component.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 30. Betti numbers (continued)

Picking up where we left off,

- we complete our discussion of Betti numbers of planar complexes.
- The definition of Betti numbers works for complexes in a more abstract sense, not drawn in the plane. This gives us examples with more interesting (and harder to understand) behaviour.

(30a) Betti numbers of planar complexes, revisited. Recall the definition of Betti numbers of a planar complex K, in terms of the ranks of boundary operators, and how we analyzed that using linear algebra:

$$b_0(K) = n_0 - \operatorname{rank}(D_1) = \operatorname{nullity}(D_1^t),$$

$$(30.1) \qquad b_1(K) = n_1 - \operatorname{rank}(D_1) - \operatorname{rank}(D_2) = \operatorname{nullity}(D_1) - \operatorname{rank}(D_2),$$

$$b_2(K) = n_2 - \operatorname{rank}(D_2) = \operatorname{nullity}(D_2).$$

Example 30.1. Take the example from the last lecture, but remove one triangle, so  $n_0 = 5$ ,  $n_1 = 7$ ,  $n_2 = 2$ :

$$(30.2) 1 4$$

We have

(30.3) 
$$D_2 = \begin{pmatrix} 1 & 0 \\ -1 & 0 \\ 0 & 1 \\ 0 & -1 \\ 1 & 0 \\ 0 & 0 \\ 0 & 1 \end{pmatrix}$$

with  $rank(D_2) = 2$ , which means  $b_2 = 0$ . As we saw last time,  $b_0$  is the number of components not connected to each other, so  $b_0 = 1$ . Finally, the Euler characteristic is

$$(30.4) \chi = b_0 - b_1 + b_2 = n_0 - n_1 - n_2 = 5 - 7 + 2 = 0$$

from which we conclude that  $b_1 = 1$  (one could of course also compute  $b_1$  directly, using rank $(D_1) = 4$ ).

Theorem 30.2. For a planar complex K, we always have  $b_2(K) = 0$ .

What we want to show is that  $D_2w = 0$  has only the trivial solution w = 0. When we spell it out, this is a linear system, with one variable  $w_T$  for each triangle, and one equation for each

edge e. By definition of  $D_2$ , the equations have the form

(30.5) 
$$\sum_{\substack{\text{triangles } T\\ \text{adjacent to } e}} \pm w_T = 0.$$

Hence, if T has an edge not shared by any other triangle, then  $w_T = 0$ ; and if the edge e is shared by exactly two triangles  $T_1$  and  $T_2$ , then  $w_{T_1} = \pm w_{T_2}$ . Starting with any triangle T, one can always pass through adjacent triangles (ones sharing an edge) until one reaches a triangle that has an "outside" edge, not shared with any other triangle. By going through all the equations, it follows that the coefficient of  $w_T$  the original triangle had to be zero.

DEFINITION 30.3. A hole of a planar complex K is a bounded component of the complement  $\mathbb{R}^2 \setminus K$ . Here, components means pieces not connected to each other; and bounded means that we exclude the infinite outside component.

Theorem 30.4. For a planar complex K, the Euler characteristic is

(30.6) 
$$\chi = (number\ of\ components\ of\ K) - (number\ of\ holes\ of\ K).$$

The main job here would be to prove the theorem about planar graphs (complexes without triangles). Once one has that, then filling in a triangle clearly raises  $\chi$  by one and also destroys a hole, hence increases both sides of the equation by the same amount. We don't want to get too far into planar graphs, hence won't explain this further.

Corollary 30.5. For every planar complex,  $b_1$  is the number of holes.

This follows from the previous results: by Theorem 30.2,  $b_1 = \chi - b_0 - b_2 = \chi - b_0$ . We also know (Theorem 29.7) that  $b_0$  is the number of components; so by Theorem 30.4,  $b_1$  must be the number of holes.

(30b) Abstract complexes. The definition of Betti numbers uses only data encoded into  $D_1$  and  $D_2$ . Those data describe the adjacencies (how points, edges, and triangles fit together), but not how the complex lies in the plane. For instance, here are two complexes with the same adjacencies:

$$(30.7) \qquad \qquad \begin{array}{c} 1 \\ 2 \\ 6 \\ 3 \\ 4 \\ 5 \end{array}$$

Maybe it would be better to say these are two pictures of the same "abstract" complex, but realized differently in the plane. In fact, Betti number can be defined in such an abstract situation, which is where they reach their full power.

Definition 30.6. An abstract complex is given by combinatorial data, as follows:

- integers  $n_0, n_1, n_2 \geq 0$ .
- Pairs  $(i_1, j_1), \ldots, (i_{n_1}, j_{n_1})$ , where  $1 \le i_k < j_k \le n_0$ , and where no two pairs may be the same.

• Triples  $(p_1, q_1, r_1), \ldots, (p_{n_2}, q_{n_2}, r_{n_2})$ , where  $1 \leq p_k < q_k < r_k \leq n_0$ , and where no two triples are the same. Moreover, whenever if a triple (p, q, r) appears, the pairs (p, q), (p, r), (q, r) must be on the previous list.

We imagine these abstract points, edges and triangles glued together, all floating in your imagination (not in ordinary three-dimensional space: many abstract complexes can't be represented in three dimensions). The definition of Euler characteristic, boundary operator, and Betti numbers, go through as before. Also, the description of  $b_0$  in terms of components still works for abstract complexes. In contrast, our description of  $b_1$  makes no sense, since we don't have a complement of the complex. And finally,  $b_2$  can be nonzero, as shown by the following example:

Example 30.7. Take a tetrahedron. It has 4 vertices and all possible edges and triangles,

$$(30.8)$$
  $(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)$  and  $(1,2,3), (1,2,4), (1,3,4), (2,3,4)$ .

The Euler characteristic is  $\chi = n_0 - n_1 + n_2 = 4 - 6 + 4 = 2$ . The boundary operators are

$$(30.9) D_1 = \begin{pmatrix} -1 & -1 & -1 & 0 & 0 & 0 \\ 1 & 0 & 0 & -1 & -1 & 0 \\ 0 & 1 & 0 & 1 & 0 & -1 \\ 0 & 0 & 1 & 0 & 1 & 1 \end{pmatrix}, D_2 = \begin{pmatrix} 1 & 1 & 0 & 0 \\ -1 & 0 & 1 & 0 \\ 0 & -1 & -1 & 0 \\ 1 & 0 & 0 & 1 \\ 0 & 1 & 0 & -1 \\ 0 & 0 & 1 & 1 \end{pmatrix}.$$

As usual, the rows of  $D_1$  add up to zero, giving one linear relation; and the first three are linearly independent, so rank $(D_1) = 3$ . The alternating sum of the columns of  $D_2$  (first minus second plus third minus fourth) is zero; and the first three columns are linearly independent, so rank $(D_2) = 3$ . We get

$$(30.10) b_0 = 4 - 3 = 1, b_1 = 6 - 3 - 3 = 0, b_2 = 4 - 3 = 1.$$

(30c) The topology of data, revisited. Suppose we have points numbered  $1, \ldots, n_0$ , and some notion of distance  $\operatorname{dist}(i,j)$  between two points. They don't need to lie in the plane: they could be in a higher-dimensional space, or even in some more abstract context, and you can define distance in whichever way you want, subject to some commonsense constraints.

Fix some scale  $\sigma > 0$ . To our points, add edges (i, j) for each i < j such that  $\operatorname{dist}(i, j) < \delta$ . In the same way, add a triangle (p, q, r) for each p < q < r such that all three points are at distance  $< \sigma$  from each other. The outcome is an abstract complex called the *Vietoris-Rips complex* of our point set, at scale  $\sigma$ . The Betti number  $b_0$  can be thought of as a simple measure of clustering: we group our points so that any two with distance  $< \sigma$  lie in the same group, and then  $b_0$  is the number of groups.  $b_1$  is a more interesting notion: it expresses insights about the structure of our point set which are not immediately obvious. (Finally,  $b_2$  does not contain any meaningful information, due to the limitations of our setup).

Example 30.8. Take these sixteen  $3 \times 3$  pixel images:

These will be the points of our abstract complex! We define the distance between two images to be the number of pixels whose differ. For instance, the distance between the 1st and 13th image is the maximal possible value, 9. Take  $\sigma = 3.5$ , and draw the edges of the Vietoris-Rips complex:

When drawing this in the plane, you'll see spurious intersections between the edges, which you are supposed to ignore. Moreover, to make the picture less messy, we have drawn two copies of the 1 and 9 points, but those should be thought of as being the same. To form the Vietoris-Rips complex, we should fill triangles wherever we can (we have indicated one triangle in the picture; when drawn in the plane, the triangles will overlap, hence we won't try drawing all of them). Altogether, we have  $n_0 = 16$ ,  $n_1 = 40$ ,  $n_2 = 32$ . Clearly, the whole complex is connected, so  $b_0 = 1$ . Rather than writing down  $D_2$ , I will give you a free piece of information, namely that  $b_2 = 8$ . Because of the Euler characteristic, this means that

$$(30.13) b_1 = 1.$$

Intuitively, this is in agreement with imagining (30.11) as (two slightly different versions, one in each row, of) an image being rotated once, creating a "loop".

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 31. Surfaces

We focus on a very special class of abstract complexes, namely combinatorial surfaces.

- Orientability is a key distinction between such surfaces. We will look at examples of orientable and non-orientable surfaces.
- We study the implications of orientability for Betti numbers.

## (31a) Combinatorial surfaces. A combinatorial surface is an abstract complex, such that:

- Every edge appears on the boundary of exactly two triangles.
- Take any vertex, and look at the edges and triangles that have our chosen vertex lying on them. Then, the outcome looks like one of these (with the chosen vertex marked in white):

This means that the adjacent triangles together look like a convex polygon, triangulated by connecting an interior point to all its vertices.

DEFINITION 31.1. Suppose that for each triangle, we choose one of the two possible ways of going around its boundary, subject to this constraint: for any given edge, the choices for the two adjacent triangles yield opposite ways of going along that edge. This is called an orientation of the surface. It's not always possible: a surface which allows it is called orientable.

(31b) Examples. We already saw one abstract complex, namely the tetrahedron, which is actually a combinatorial surface. The same holds for the octahedron, icosahedron, and other (less symmetric) convex polyhedra with triangular faces: they are all surfaces, and can be thought of as combinatorial versions of the two-dimensional sphere.

Example 31.2. The tetrahedron is orientable (and the same holds for the other combinatorial spheres). This is easiest to see by drawing the triangles one-by-one, and then picking a way to go around the boundary of each, so that the edge conditions are satisfied:

For instance, in the first triangle, we go around the boundary by moving from 1 to 2; whereas in the second triangle, we move from 2 to 1.

31. SURFACES 233

Example 31.3. The following picture,

properly understood, is a combinatorial surface (a torus). To represent it in the plane, we have drawn several copies of the vertices, and that also holds for the edges: the (1,4) edges on the left and right side are the same. If we cut out the picture and glue those two sides together, we get a ring (annulus), but note that the top and bottom sides should also be thought of as being glued together. We have  $n_0 = 7$ ,  $n_1 = 21$ ,  $n_2 = 14$ , hence  $\chi = 0$ . The torus is orientable (remember, you have to check that the orientation condition also holds at the edges that have been drawn twice):

Example 31.4. Here is another picture of the same kind as the previous one. Note that on the boundary of our picture, every point and every edge is identified with its counterpart on the opposite side. One can think of it as the top half of an icosahedron, where the boundary is glued to itself with a 180 degree twist. In fact, it is a combinatorial version of the projective plane.

We have  $n_0 = 6$ ,  $n_1 = 15$ ,  $n_2 = 10$ , which means that  $\chi = 1$ . The projective plane is non-orientable. To see this, it's enough to start with one triangle and gradually try to extend orientations to the neighbouring ones. The outcome is a contradiction:

(31c) Orientability and its consequences. One reason why orientability is important is that it has significant implications for the Betti numbers.

PROPOSITION 31.5. Take a combinatorial surface which is connected (meaning that it's not divided into several mutually disconnected parts; equivalently,  $b_0 = 1$ ). Then  $b_2 = 1$  if the surface is orientable, and  $b_2 = 0$  otherwise.

EXAMPLE 31.6. For the torus from Example 31.3, we now know that  $b_2 = 1$ , and of course  $b_0 = 1$ . By the Euler characteristic computation, we must have  $b_1 = 2$ .

EXAMPLE 31.7. For the projective plane from Example 31.4, we now know that  $b_2 = 0$ , and also  $b_0 = 1$ , hence  $b_1 = 0$ .

The proof of the Proposition is based on  $b_2 = \text{nullity}(D_2)$ , and an argument similar to that which showed  $b_2 = 0$  for planar complexes. Suppose that we have oriented our surface, and take one of the triangles (p, q, r), for  $1 \le p < q < r \le n_0$ . Assign to our triangle a number  $\pm 1$ , like this. If the orientation tells us to go around the triangle from the p-th point to the q-th point to the r-th point, we take +1; and if the opposite is true, take -1. The condition on the orientation means that this collection of numbers is a solution to  $D_2w = 0$ , so its existence proves that  $b_2 > 0$ . The rest of the argument (showing that any other solution is a multiple of this one; and the converse direction, namely that existence of a solution implies orientability) is similar, and we won't go through it here.

Proposition 31.8. The Euler characteristic of an orientable surface is always even.

Taking those two Propositions together, we also see this:

Corollary 31.9. For an orientable surface,  $b_1$  is even.

There is an elementary combinatorial proof of Proposition 31.8. Like many elegant arguments, it is also mystifying in a what-did-we-just-do way. Moreover, it relies on the notion of *sign of a permutation*, which we've not used before; so, you have my permission to skip it if you want!

Take a surface which has been oriented. Define a *side* to be an edge together with the choice of one of the two adjacent triangles. Let's call the set of sides  $\Sigma$  (it is of size  $2n_1$ ). We look at three ways of permuting the sides:

- The opposite map  $o: \Sigma \to \Sigma$ , which keeps the edge but passes from one adjacent triangle to the other. In other words, for each edge, it swaps out the two possible sides. As a consequence,  $sign(o) = (-1)^{n_1}$ .
- The successor map  $s: \Sigma \to \Sigma$  uses the orientation, to go from the given side to the next one for the same triangle. Clearly, if we do it three times, we get back to the original side, meaning that  $s^3$  is the trivial (identity) permutation. This shows that  $\operatorname{sign}(s)^3 = \operatorname{sign}(s^3) = 1$ , and therefore  $\operatorname{sign}(s) = 1$ .
- The rotator map  $r: \Sigma \to \Sigma$  is a little more complicated. Given a side, move forward (using the orientation of the triangle) along the edge until one hits a vertex. We then

31. SURFACES 235

pass to the next triangle adjacent to that vertex, again using the orientation:

Here, we've indicated a side just by drawing a dot in the triangle, lying near the desired edge. sign(r) is the number of vertices of our surface which have even valence (have an even number of edges adjacent to them); to see that, one needs to look at how each side cycles if we repeat r.

One observes (proof-by-picture) that these three permutations are related, one being the composition of the other two:

$$o = s \circ r$$

As a consequence, sign(o) = sign(s)sign(r) = sign(r). In words, the number of edges is congruent mod 2 to the number of even-valence vertices. At this point, we need two more easy combinatorial facts (the first is true for any graph, and the second for any surface):

- the number of vertices of odd valence is even;
- the number of triangles is even.

The previous argument, and the first fact, combine to show that the number of edges is congruent mod 2 to the number of all vertices. Together with the second fact, we see that the number of edges is congruent mod 2 to the number of vertices plus the number of triangles. Which is exactly what Proposition 31.8 said!

(31d) Summary. Since we have talked about Betti numbers in various degrees of generality, it makes sense to summarize we know about their behaviour and geometric meaning (for surfaces we have assumed connectedness, to make the statements simpler; of course, in general a surface doesn't have to be connected).

|       | planar complex | abstract complex | connected  | connected      |
|-------|----------------|------------------|------------|----------------|
|       |                |                  | orientable | non-orientable |
|       |                |                  | surface    | surface        |
| $b_0$ | components     | components       | 1          | 1              |
| $b_1$ | holes          | ?                | even       | ?              |
| $b_2$ | 0              | ?                | 1          | 0              |

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 32. Combinatorial loops

In an abstract complex, a combinatorial loop is a path that moves along edges and ends where it started.

- We introduce the notion of homotopy (a combinatorial version of deformation) between two such loops.
- The main question is: how can we decide if two loops are homotopic to each other?

We will look at a number of examples, and answer our question by methods that look a bit improvised, even though they will remind you of our previous topics of polygonal/smooth loops and their winding numbers.

(32a) The definitions. Take an abstract complex K with  $n_0$  points (vertices). A combinatorial loop of length  $m \geq 0$  is a collection  $l = (a_0, a_1, \ldots, a_m)$  of points in K, meaning that  $1 \leq a_k \leq n_0$ , such that:

- for all k, we have  $a_{k-1} \neq a_k$ , and there is an edge connecting  $a_{k-1}$  to  $a_k$  (in other words, if  $a_{k-1} < a_k$ , then  $(a_{k-1}, a_k)$  is in the list of edges for K; and if  $a_{k-1} > a_k$ , then  $(a_k, a_{k-1})$  is in that list).
- $a_m = a_0$ .

In words, the loop moves from vertex to vertex along edges, and eventually returns to its starting point. The simplest loops are the constant ones, m = 0, which just consist of one vertex l = (a). The next simplest ones are zigzags  $(a_0, a_1, a_2 = a_0)$ , which have m = 2.

What makes combinatorial loops interesting is the notion of homotopy. Two loops are homotopic if they are related by a sequence of the following moves:

- Changing the starting point: this means passing from  $(a_0, \ldots, a_m)$  to  $(a_1, a_2, \ldots, a_m, a_1)$ , or vice versa to  $(a_{m-1}, a_0, a_1, \ldots, a_{m-1})$ . This makes sense because  $a_m = a_0$ .
- Removing or inserting a zigzag: if (...a, b, a...) occurs in our loop, then we can replace that by (...a...), which shortens it by 2. The reverse move, which makes a loop longer by 2, is also allowed.
- Moving across a triangle: if our loop has (...a, b, c...) and  $\{a, b, c\}$  are the three vertices of a triangle (in any order), then we can delete b, shortening the loop by 1. The reverse move, which makes a loop longer by 1, is also allowed.

Lemma 32.1. For a constant loop, the homotopy class depends only on the component of K in which it lies.

Suppose there's an edge connecting the a-th and b-th vertex. Then the constant loops (a) and (b) are homotopic:

(32.1) (a) 
$$\xrightarrow{\text{insert zigzag}}$$
  $(a, b, a)$   $\xrightarrow{\text{change starting point}}$   $(b, a, b)$   $\xrightarrow{\text{remove zigzag}}$   $(b)$ .

By saying that K has only one component, we mean that you can move from any vertex to any other along edges. By repeating the argument above, we then see that any two vertices give rise to homotopic constant paths.

(32b) Examples. The simpler half of the problem is the constructive one: to show that a given loop is homotopic to a constant, or that two loops are homotopic to each other, all one needs to do is find a suitable sequence of moves.

Example 32.2. Take this star-shaped graph (a complex without triangles):

(32.2)

Any non-constant loop must pass through the 1 vertex. After rotating the starting point, we can assume that it starts and ends at 1. Then, it necessarily consists of zigzag pieces  $(\ldots 1, a, 1, \ldots)$  with  $1 < a \le n_0$ . Each such piece can be cancelled. It follows that every loop is homotopic to a constant loop.

EXAMPLE 32.3. Take this complex (with  $n_0 \ge 4$  points, forming an  $(n_0 - 1)$ -gon with one point at the center):

(32.3)

Suppose we have a loop (...a, b...), where  $a, b \ge 2$ . By moving across a triangle, one can always replace that by (...a, 1, b...). Having done that in all places, we have a loop that bounces back-and-forth between 1 and other vertices, which then can be shortened to a constant. Hence, all loops are homotopic to constant ones.

We now turn to the harder theoretical part of the problem, where one is trying to prove that a given loop is not homotopic to a constant, or that two loops are not homotopic. For that, one has to find some sort of obstacle that will prevent one loop from turning into the other. Here's a toy model:

Example 32.4. Take this graph ( $n_0 \ge 3$  points connected to each other in a circular way, with no triangles):

(32.4)

We have a strong intuitive feeling that the loop  $(1, 2, 3, ..., n_0, 1)$  is not homotopic to a constant loop, since it "goes once around". To make it rigorous, we introduce a combinatorial analogue

of the notion of winding number. Namely, we associate to every loop l an integer I(l), like this: whenever (...1,2...) occurs in our loop, count that as +1; whenever (...2,1...) occurs, count it as -1; and add up those numbers. This integer is unchanged under homotopies (there are no triangles, so we don't have to look at that move). Now, the loop we started with had value w(l) = 1, whereas the constant loop has w(l) = 0, so they can't be homotopic.

(32c) The torus. Take this surface, which is a combinatorial version of a torus:

We can associate to a loop a winding number w(l), by counting how often it crosses the dashed cut drawn above, with signs: +1 for a left-to-right crossing, and -1 for a right-to-left one. This means that we count occurrences of the following patterns:

(32.6) 
$$(...2, 3...), (...8, 9...), (...5, 6...), (...8, 3...), (...5, 9...), (...2, 6...) count as +1, \\ (...3, 2...), (...9, 8...), (...6, 5...), (...3, 8...), (...9, 5...), (...6, 2...) count as -1.$$

The sum of all those signs is unchanged under homotopies! One can show that by checking it for every possible occurrence of move-over-a-triangle.

Example 32.5. The loop l = (1, 2, 3, 1) has  $w_{\rightarrow}(l) = 1$ . Hence, it's not homotopic to a constant, but it's also not homotopic to l = (1, 2, 3, 1, 2, 3, 1), which has  $w_{\rightarrow}(l) = 2$ .

Example 32.6. The loop 
$$l = (1, 4, 6, 9, 8, 2, 1)$$
 has  $w_{\rightarrow}(l) = -1$  and  $w_{\uparrow}(l) = 1$ .

There is also an entirely different vertical winding number, which would be obtained by counting the crossings with a left-to-right cut.

- (32d) General cuts. A cut c in an abstract complex is defined by picking a set of edges (which we picture by drawing a dot in the center of each edge) and a sign -1 or +1 on each of those edges, obeying the following rules:
  - For every triangle in the complex, either none or two of its boundary edges belong to the cut (we then visualize that by drawing a dotted line connecting the two).

• The signs (where the triangle has vertices p, q, r with p < q < r) must satisfy:

Each cut gives us a winding number  $w_c(l)$  for loops l. Roughly speaking, whenever an edge in the cut appears as part of our loop ("the loop crosses the cut"), we get a  $\pm 1$  contribution, and the sum of those contributions is  $w_c(l)$ . The rule for the signs is: if an edge (i,j), obviously with i < j, is part of the cut, and our loop goes from i to j, use sign for that edge; and if the loop goes from j to i, use the opposite sign (as you can see, sign issues are rather tricky). The outcome is an integer which is unchanged under homotopies.

Example 32.7. Here's our previous torus example, with the signs added:

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 33. Combinatorial winding numbers and the boundary operators

In the previous lecture, we introduced cuts and the resulting winding numbers. We now generalize that notion a bit, and relate it to boundary operators.

- To each loop one can associate a vector, which counts how many times each edge in the complex appears in it (with signs).
- By taking suitable scalar products, one can define general combinatorial winding numbers, which are homotopy invariants. This construction will also explain the geometric meaning of the first Betti number of a complex.

(33a) From loops to vectors. Let K be an abstract complex. Let's introduce some notation. If (i,j) is an edge, which by definition means  $1 \le i < j \le n_0$ , we write  $e_{(i,j)}$  for the corresponding unit (standard basis) vector in  $\mathbb{R}^{n_1}$  (recall  $n_1$  is the number of edges, and we usually order those edges lexicographically). We also find it convenient to write  $e_{(j,i)} = -e_{(i,j)}$ . To any combinatorial loop  $l = (a_0, \ldots, a_m)$  one can associate a vector

(33.1) 
$$v_l = \sum_{i=1}^m e_{(a_{i-1}, a_i)} \in \mathbb{R}^{n_1}.$$

In words: if  $a_{i-1} < a_i$ , we take the unit vector for the edge  $(a_{i-1}, a_i)$ ; if  $a_{i-1} > a_i$ , take minus the unit vector for the edge  $(a_i, a_{i-1})$ ; and add up all those vectors to get  $v_l$ . A constant loop l gives rise to the vector  $v_l = 0$ , since there are no contributions at all. The same is true for loops l = (a, b, a), since one gets two terms which exactly cancel each other. It is important to remember that  $v_l$  only sees which edges are part of l, not the order in which they occur. Therefore, it doesn't have all the information about the loop,

Example 33.1. Take the graph

$$(33.2)$$

with edges (1,2), (1,3), (2,3). The loop l = (1,2,3,1) consists of the edges (1,2), (2,3), and the reverse of (1,3). Therefore,  $v_l = (1,-1,1)$ .

EXAMPLE 33.2. Take two tetrahedra, stick them together along one triangle, and then forget that triangle. The outcome is this surface ( $n_0 = 5$ ,  $n_1 = 9$ , and  $n_2 = 6$  including two triangles that are "hidden" at the back the picture):

In the loop l = (2, 3, 4, 2, 3, 4, 2), each of the three edges (2, 3), (2, 4), (3, 4) appears twice, but the edge (2, 4) appears in reverse order. Therefore,

$$(33.4) \ v_l = 2e_{(2.3)} + 2e_{(3.4)} + 2e_{(4.2)} = 2e_{(2.3)} + 2e_{(3.4)} - 2e_{(2.4)} = (0, 0, 0, 2, -2, 0, 2, 0, 0) \in \mathbb{R}^{n_1}.$$

In the rightmost expression, we have followed our usual convention of listing the edges in lexicographic order: (1,2), (1,3), (1,4), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5).

LEMMA 33.3. The vector  $v_l$  always satisfies  $D_1v_l = 0$ .

For that, it's enough to remember that by definition of boundary operators,  $De_{(i,j)} \in \mathbb{R}^{n_0}$  is the j-th unit vector minus the i-th unit vector. Basically, this the difference between the endpoints of the edge (i,j). The terms in  $D_1v_l$  coming from subsequent edges will partly cancel, since each edge ends where the following one starts; and because we have a loop that comes back to its starting point, they will finally cancel altogether.

THEOREM 33.4. Suppose that  $l_0$  and  $l_1$  are homotopic. Then  $v_{l_0} - v_{l_1} = D_2 x$  for some  $x \in \mathbb{R}^{n_2}$ .

To prove that, we have to investigate what happens to  $v_l$  under the moves that define the notion of homotopy. If we change the starting point,  $v_l$  doesn't change at all, since we still have the same edges, just in different order. And if insert or delete a zigzag  $(\ldots, a, b, a, \ldots)$ , we add or remove two contributions to  $v_l$ , but those contributions are the same basis vector with opposite signs, so again  $v_l$  remains the same.

The interesting part is passing over a triangle: a single move passes from  $l_0 = (\ldots, a, b, c, \ldots)$  to  $l_1 = (\ldots, a, c, \ldots)$ . This means that

$$(33.5) v_{l_0} - v_{l_1} = e_{(a,c)} - e_{(a,b)} - e_{(b,c)}.$$

The notation here hides some sign issues, but irrespectively, the right hand is, up to an overall sign,  $D_2$  of the unit vector in  $\mathbb{R}^{n_2}$  associated to the triangle with vertices  $\{a, b, c\}$ . A general homotopy involves several such moves, but one can add the resulting vectors in  $\mathbb{R}^{n_2}$  to get the desired x.

(33b) Winding numbers. We want to turn the vectors  $v_l$  into a practical tool for distinguishing non-homotopic loops. For that purpose, it's important to remember the fact that  $D_2D_1 = 0$ .

COROLLARY 33.5. Fix some  $c \in \mathbb{R}^{n_1}$  such that  $D_2^t c = 0$ . Then, the number  $c \cdot v_l \in \mathbb{R}$  is a homotopy invariant, which means it remains the same if (keeping c the same, of course) we change l to a homotopic loop.

We call this the combinatorial winding number of l with respect to c, and write it as

$$(33.6) wind_c(l) = c \cdot v_l.$$

The proof is really easy. Suppose that  $l_0$  and  $l_1$  are homotopic. Then

$$(33.7) v_{l_1} - v_{l_0} = D_2 x \implies I_c(l_1) - I_c(l_0) = c \cdot (v_{l_1} - v_{l_0}) = c \cdot D_2 x = D_2^t c \cdot x = 0.$$

Concretely, a vector c has one coefficient for every edge, and  $D_2^t c = 0$  consists of one equation for every triangle. If (p, q, r) is a triangle, which always means p < q < r, then the equation is:

(33.8) the (p,q)-coefficient of c plus the (q,r)-coefficient of c equals the (p,r)-coefficient of c.

The cuts used in the previous lecture were actually specific choices of vectors c: whenever an edge (i,j), i < j, occurs in the cut with sign  $\pm 1$ , we take  $\pm e_{(i,j)}$ , and add up those vectors. The outcome satisfies (33.8), as one can check by looking at this picture:

(33.9) 
$$p + q + q + q + q + q + q + q + q + q +$$

as standing for vectors (up to overall  $\pm 1$  signs)

(33.10) 
$$c = \pm (e_{(p,q)} - e_{(q,r)}), \quad c = \pm (e_{(p,q)} + e_{(p,r)}), \quad c = \pm (e_{(q,r)} - e_{(p,r)}).$$

Of course, a general solution of  $D_2^t c = 0$  doesn't correspond to a cut, and one could skip the geometric intuition and just look for such solutions directly, by solving that system of equations like any linear algebra problem.

Example 33.6. The cut in the torus we drew last time,

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

corresponds to the vector

$$(33.12) c = e_{(2,3)} + e_{(5,6)} + e_{(8,9)} - e_{(3,8)} + e_{(5,9)} + e_{(2,6)}.$$

(33c) Theory aspects. Remember that  $D_1D_2=0$ . For the transposed matrices, we have

$$(33.13) D_2^t D_1^t = (D_1 D_2)^t = 0.$$

In principle, this seems to provide an easy way to find solutions of  $D_2^t c = 0$ : any vector  $c = D_1^t b$  will do. However, these are useless for our purpose:

LEMMA 33.7. If  $c = D_1^t b$ , then wind<sub>c</sub>(l) = 0 for all loops l.

The proof is a simple matrix computation: since  $D_1v_l=0$ ,

(33.14) 
$$\operatorname{wind}_{D_{1}^{t}b}(l) = (D_{1}^{t}b) \cdot v_{l} = b \cdot (D_{1}b) = 0.$$

What is the overall implication? We have seen that any  $c \in \mathbb{R}^{n_1}$  with  $D_2^t c = 0$  gives rise to a combinatorial winding number wind<sub>c</sub>. The number of linearly independent such c is

(33.15) 
$$\operatorname{nullity}(D_2^t) = n_1 - \operatorname{rank}(D_2^t) = n_1 - \operatorname{rank}(D_2).$$

However, we now that some of those combinatorial winding numbers are just zero. The number of linearly independent c which are useless in this way is

$$\operatorname{rank}(D_1^t) = \operatorname{rank}(D_1).$$

Hence, the actually useful number is

(33.17) 
$$\operatorname{nullity}(D_2^t) - \operatorname{rank}(D_1^t) = n_1 - \operatorname{rank}(D_2) - \operatorname{rank}(D_1) = b_1(K).$$

In words, this means that there are  $b_1(K)$  essentially different ways of measuring "how a loop winds around K". Finally, this provides us with a geometric intuition for the first Betti numbers, even though it's one that requires quite a bit of background knowledge. The extreme case is  $b_1(K) = 0$ . In that case, the combinatorial winding numbers are all zero, which means they provide no information whatsoever about homotopy classes of loops. To understand homotopy better, one would then need to refine our tools (see the case of the projective plane from the end of the previous lecture; the mod 2 calculation used there hints at a whole new concept, that of mod 2 Betti numbers).

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 34. The hyperbolic plane

Hyperbolic geometry is one of the two non-Euclidean geometries. This means that it has the notions familiar to you from Euclidean geometry (points, lines, circles, distances, angles, areas), but most of them are interpreted in quite different ways.

- We define hyperbolic geodesics, which are the analogues of straight lines, and look at the beginnings of triangle geometry;
- We introduce the hyperbolic distance, and the associated notion of hyperbolic circle.

(34a) Points and lines. The hyperbolic plane is the upper half of the ordinary plane, minus the x-axis:

(34.1) 
$$\mathbb{H} = \{(x, y) \in \mathbb{R}^2 : y > 0\} = \{z = x + iy \in \mathbb{C} : \operatorname{im}(z) > 0\}.$$

Complex coordinates turn out to be particularly useful in this context. The hyperbolic geometry notion of straight line has a special name:

DEFINITION 34.1. A hyperbolic geodesic in  $\mathbb{H}$  is either a straight vertical half-line, or a half-circle centered on the horizontal axis.

If we were living in the hyperbolic plane, Newtonian motion, light rays, and sound propagation, would happen along geodesics. To a person born with hyperbolic senses, all geodesics appear equivalent: the apparent distinction between circles and vertical lines is an artifact of the way we have represented the hyperbolic plane inside the ordinary plane. From elementary geometry, we can see that geodesics have some of the properties we expect from the notion of a straight line, but hold one surprise:

- Through any two points in  $\mathbb{H}$  there is exactly one geodesic. (This implies that two different geodesics can intersect in at most one point.)
- If we fix a point in  $\mathbb{H}$ , there is exactly one geodesic through that point with any prescribed tangent line. (This implies that two different geodesics can never be tangent to each other.)
- Fix a geodesic c, and a point p not lying on c. Then there are infinitely many geodesics passing through p and which do not intersect c (this is unlike the case of Euclidean geometry, where the corresponding property characterizes the unique parallel line):

The last-mentioned fact shows that hyperbolic geometry is not Euclidean geometry written in some weird nonlinear coordinate system! Other notions are defined using geodesics. For instance,

a triangle in hyperbolic geometry consists of three points joined by geodesic segments. Here are two examples:

$$(34.3)$$

(34b) Angles. Hyperbolic geometry uses the same notion of angle as ordinary geometry. More precisely, if two geodesics intersect at a point, we take the tangent lines (in the standard sense) at that point, and measure their angle. As before, some familiar geometric properties hold, and some don't. What we are interested in is this:

Theorem 34.2. In a hyperbolic triangle, the sum of the angles is always less than  $\pi$ .

Let's first look at how a half-circle and a vertical line intersect:

$$\begin{array}{c|c}
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & \\
 & & & &$$

We are interested in the angle  $\alpha$  of intersection, which is also one of the angles of the (Euclidean, not hyperbolic) right-angled triangle in the picture. Let x, p, r be the side-lengths (again in the standard Euclidean sense) of the triangle, so that  $x = r\cos(\alpha)$  and  $p = r\sin(\alpha)$ . If we move the vertical line slightly, the angle changes like this:

(34.5) 
$$\frac{d\alpha}{dx} = \left(\frac{dx}{d\alpha}\right)^{-1} = (-r\sin(\alpha))^{-1} = -1/p.$$

Look at a hyperbolic triangle where one of the three sides is a vertical line.

$$(34.6) p$$

If I move the vertical line slightly to the right, the argument above says that  $d\alpha/dx = -1/p$ . A similar argument, using the complementary angle, shows that  $d\beta/dx = 1/q$ . Of course,  $\gamma$  is independent of x. The outcome is that

(34.7) 
$$\frac{d}{dx}(\alpha + \beta + \gamma) = \frac{1}{q} - \frac{1}{p} > 0.$$

Qualitatively, as we move the vertical line to the right, the sum of angles increases. On the other hand, as we move the vertical line closer and closer to the intersection of the two circles, the hyperbolic triangle becomes tiny, and its behaviour is closer and closer to that of an ordinary

straight-line triangle, so the sum of angles approaches  $\pi$ . We have just shown that in the original triangle (34.6), the sum of angles is always less than  $\pi$ !

This proves our desired theorem, in the special case where the left side of the hyperbolic triangle is a vertical line. Of course, by reflection, the same is true if the right side is a vertical line. Finally, for triangles bounded by three half-circles, we can obtain our result by decomposing them into two pieces which are triangles bounded by a vertical line, and then adding up the angles:

(34c) Distances. Remember that in the complex plane, |z-w| is the ordinary distance between two points. In terms of the complex conjugate, one can write this as  $|z-w|^2 = (z-w)(\bar{z}-\bar{w})$ . The hyperbolic analogue is gruesome:

Definition 34.3. The hyperbolic distance between two points  $z, w \in \mathbb{H}$  is

(34.9) 
$$\operatorname{dist}(z, w) = \ln \left( \frac{|z - \bar{w}| + |z - w|}{|z - \bar{w}| - |z - w|} \right).$$

A priori, it's not clear where this comes from, or that it makes any sense as a notion of distance. At least, since  $|z - \bar{w}| = |w - \bar{z}|$ , it is symmetric, meaning  $\operatorname{dist}(z, w) = \operatorname{dist}(w, z)$ .

Example 34.4. Take two points on the same vertical line, w = x + iu and z = x + iy, with u > y. Then

(34.10) 
$$\operatorname{dist}(x+iu, x+iy) = \ln\left(\frac{(u+y) + (u-y)}{(u+y) - (u-y)}\right) = \ln(u/y) = \ln(u) - \ln(y).$$

We can make it more symmetric: for all  $u \neq y$  (but still on the same vertical line),

(34.11) 
$$\operatorname{dist}(x + iu, x + iy) = |\ln(u/y)| = |\ln(u) - \ln(y)|.$$

Unsurprisingly, hyperbolic geometry also uses hyperbolic trig functions (sinh, cosh, tanh; you may want to look up the definition and the shape of their graphs, to refresh your memory; in particular, the formula  $\cosh(x)^2 - \sinh(x)^2 = 1$  is often useful). For us, their first appearance is in the following equivalent, and more convenient, formula for the distance:

(34.12) 
$$\cosh(\operatorname{dist}(z, w)) - 1 = \frac{|z - w|^2}{2\operatorname{im}(z)\operatorname{im}(w)}.$$

Since cosh is defined in terms of exponentials, its inverse function can be written in terms of logarithms, more precisely it is  $\pm \ln(x+\sqrt{x^2-1})$ . Applying this to (34.12), plus a lot of computation, shows the equivalence to our original distance formula.

Maybe a better way to understand distance is to look at circles. The hyperbolic circle with center z and radius r is naturally defined as the set of all points w such that dist(z, w) = r. Let's wrestle

with this equation. It means that

$$\frac{|z-w|^2}{2\operatorname{im}(z)\operatorname{im}(w)} = \cosh(r) - 1$$

$$(34.13) \qquad \Leftrightarrow (\operatorname{re}(z) - \operatorname{re}(w))^2 + (\operatorname{im}(z) - \operatorname{im}(w))^2 = 2(\cosh(r) - 1)\operatorname{im}(z)\operatorname{im}(w)$$

$$\Leftrightarrow (\operatorname{re}(z) - \operatorname{re}(w))^2 + (\cosh(r)\operatorname{im}(z) - \operatorname{im}(w))^2 = \cosh(r)^2 - 1 = \sinh(r)^2\operatorname{im}(z)^2.$$

Writing x = re(z), y = im(z), the outcome is:

FACT 34.5. The hyperbolic circle with center (x, y) and radius r is exactly the ordinary Euclidean circle with center  $(x, \cosh(r)y)$  and radius  $\sinh(r)y$ .

An easy check, as well as a way to remember this, is: the top and bottom points of the circle are (34.14)  $(x, \cosh(r)y + \sinh(r)y) = (x, e^r y)$  and  $(x, \cosh(r)y - \sinh(r)y) = (x, e^{-r}y)$ .

Indeed, as we see from Example 34.4, both points have hyperbolic distance r from (x, y). Here is a picture of hyperbolic circles centered at i = (0, 1):

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 35. Arclengths and areas

So far, concepts of hyperbolic geometry, such as geodesics and distances, have appeared in somewhat haphazard and unrelated ways. The modern viewpoint is that these, and another notions, arise from a single concept, that of the infinitesimal length element.

- The infinitesimal length element appears most naturally in the notion of hyperbolic arclength of a path. We introduce that, and explain how it gives rise to hyperbolic geodesics and to the distance formula.
- We also consider the associated notion of hyperbolic area, and explain how that can be used to improve our understanding of hyperbolic triangles.

(35a) Lengths and distances. At a point (x, y) in the hyperbolic plane, the *infinitesimal* length element is

$$\frac{\sqrt{dx^2 + dy^2}}{y}.$$

In terms of complex numbers z = x + iy, one would write that formula as

$$\frac{|dz|}{\mathrm{im}(z)}.$$

where  $\operatorname{im}(z) = y$  is the imaginary part. The infinitesimal length element describes how the geometry is distorted, compared to the Euclidean one, around this particular point. Our first use of this is to define the arclength of a path  $c(t) = (x(t), y(t)) \in \mathbb{H}$ :

(35.3) 
$$\operatorname{length}(c) = \int \frac{\sqrt{x'(t)^2 + y'(t)^2}}{y(t)} dt.$$

If we think of our path as complex-valued,  $c(t) \in \mathbb{C}$ , the same formula is

(35.4) 
$$\operatorname{length}(c) = \int \frac{|c'(t)|}{\operatorname{im}(c(t))} dt.$$

Here is how arclength leads one naturally to the concepts of distance and of geodesic:

Theorem 35.1. For any two points z and w,

(35.5) 
$$\operatorname{dist}(z, w) = \min\{\operatorname{length}(c) \text{ for all paths } c \text{ from } z \text{ to } w\}.$$

THEOREM 35.2. Given two points z and w, the paths of minimal length from z to w are precisely those that go along a geodesic (without ever turning back, of course).

Let's prove these theorems in a special case, namely z = (0, 1) and  $w = (0, e^r)$ , where r > 0. We know from the distance formula that dist(z, w) = r. Take any path c from z to w. Then

(35.6) 
$$|\operatorname{length}(c)| = \int \frac{\sqrt{(dx/dt)^2 + (dy/dt)^2}}{y(t)} dt$$

$$\geq \int \frac{\sqrt{(dy/dt)^2}}{y(t)} dt \geq \int \frac{dy/dt}{y(t)} dt = \ln(y(t)) \Big|_{\text{starting } t}^{\text{endpoint } t} = \ln(e^r) - \ln(1) = r.$$

So, the length is indeed always  $\geq$  the distance. Moreover, in order for (35.6) to be an equality, we must have dx/dy=0 and  $dy/dt\geq 0$  everywhere. So, minimal length paths are those that move upwards along the vertical line.

We haven't been too precise about the class of paths that is allowed. Basically, anything for which you can carry out the arclength integral works, let's say a piecewise smooth path.

Corollary 35.3. For any three points z, u, w, we have

(35.7) 
$$\operatorname{dist}(z, w) < \operatorname{dist}(z, u) + \operatorname{dist}(u, w).$$

We could of course prove this directly from the definition of distance (ouch), but it follows much more easily from Theorem 35.1: take a length-minimal path from z to u, and another such path from u to w. Together, they give a path from u to u of length dist(z, u) + dist(u, w). That sum must therefore be  $\geq dist(z, w)$ .

(35b) Area. If infinitesimal lengths are stretched by 1/y, areas should be stretched by  $1/y^2$ . Indeed, we define the hyperbolic area of a region  $U \subset \mathbb{H}$  by

(35.8) 
$$\operatorname{area}(U) = \int_{U} \frac{1}{y^2} \, dx \, dy.$$

Example 35.4. Suppose that our region is the area between two graphs y = q(x) and y = p(x):

(35.9) 
$$U = \{ a \le x \le b, \ q(x) \le y \le p(x) \}$$

Then, we can carry out the area computation by integrating y first, just like you learned in calculus:

(35.10) 
$$\operatorname{area}(U) = \int_{a}^{b} \left( \int_{f(x)}^{g(x)} \frac{1}{y^{2}} \, dy \right) dx = \int_{a}^{b} \frac{1}{p(x)} - \frac{1}{q(x)} \, dx.$$

Example 35.5. Take the region bounded by the geodesics x = -1, x = +1 and  $x^2 + y^2 = 1$  (this looks like a triangle, but it's not, since the sides don't actually meet in  $\mathbb{H}$ ). We get an improper integral

(35.11) 
$$\int_{-1}^{1} \left( \int_{\sqrt{1-x^2}}^{\infty} \frac{1}{y^2} dy \right) dx = \int_{1}^{r} \frac{1}{\sqrt{1-x^2}} dx = \arcsin(x) \Big|_{x=-1}^{x=1} = \pi.$$

One can consider any region of the same shape, bounded by a half-circle and two vertical half-lines which are asymptotic to the same points on the horizontal axis. The same argument (with a small change of variables) shows that the area is always  $\pi$ .

THEOREM 35.6. The area of any hyperbolic triangle is  $< \pi$ .

Let's look at a special case, which is when one side of the triangle is a vertical line. This is actually straightforward, since the triangle is clearly contained in a larger region of area  $\pi$ :

(35c) Triangle geometry. We know two things about hyperbolic triangles: first, the sum of the angles is  $< \pi$ ; and second, the area is  $< \pi$ . The two are actually related:

THEOREM 35.7. (Gauss-Bonnet) For a hyperbolic triangle T, with angles  $(\alpha, \beta, \gamma)$ ,

(35.13) 
$$\operatorname{area}(T) = \pi - \alpha - \beta - \gamma.$$

As usual, we will just look at the case where one of the sides is vertical,

$$(35.14) p$$

What happens if we move that side? The fundamental theorem of calculus, applied to the area integral, tells us that

$$\frac{d}{dx}\operatorname{area}(T) = \frac{1}{p} - \frac{1}{q},$$

where x is the coordinate giving the position of the vertical line; and last time we saw that

(35.16) 
$$\frac{d}{dx}(\alpha + \beta + \gamma) = \frac{1}{q} - \frac{1}{p}.$$

As a consequence,

(35.17) 
$$\frac{d}{dx}(\operatorname{area}(T) - \pi + \alpha + \beta + \gamma) = 0,$$

which means that expression in brackets is constant in x. If we move the vertical line to the right until the triangle shrinks to a point, then in the limit  $\alpha + \beta + \gamma \to \pi$  and  $\operatorname{area}(T) \to 0$ , so  $(\operatorname{area}(T) - \pi + \alpha + \beta + \gamma) \to 0$ . A constant function which has limit 0 is of course 0 everywhere, and that's what we wanted!

We close this chapter by stating two formulae without proof. Take a hyperbolic triangle with side-lengths (a, b, c) and angles  $(\alpha, \beta, \gamma)$ , labeled in the way you're used to from ordinary geometry.

The hyperbolic cosine laws are

(35.18) 
$$\cos(\alpha) = \frac{\cosh(b)\cosh(c) - \cosh(a)}{\sinh(b)\sinh(c)}$$

(35.18) 
$$\cos(\alpha) = \frac{\cosh(b)\cosh(c) - \cosh(a)}{\sinh(b)\sinh(c)},$$

$$\cosh(a) = \frac{\cos(\alpha) + \cos(\beta)\cos(\gamma)}{\sin(\beta)\sin(\gamma)}.$$

The first cosine law recovers the angles in a triangle from the three side-lengths, which is something one can also do in Euclidean geometry. The second law, on the other hand, would be inconceivable in Euclidean geometry, where one certainly can't determine side-lengths starting only with angles, because of the freedom to scale up any triangle! As one already sees from our discussion of the maximal area of triangles, there's no "scaling up" in hyperbolic geometry.

At this point, we need to own up to the sins we've committed:

- we have established the key relation between arclength and distance (Theorems 35.1 and 35.2) only when z = (0, 1) and  $w = (0, e^r), r > 0$ .
- we have proved Gauss-Bonnet (both its proper form, Theorem 35.7, and the preliminary Theorem 35.6) only for triangles where one side is a vertical line.

In both situations, the general statement actually follows from those special cases, but that will have to wait until the next lecture.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 36. Hyperbolic isometries

One way to think of Euclidean geometry is that the basic notion is congruence transformations: all geometric notions must be invariant under them. There is a similar class of transformations in hyperbolic geometry.

- We introduce those transformations, called hyperbolic isometries, both through special classes, and a general formalism.
- Often, isometries can be applied to simplify a coordinate argument or computation. We want to at least lay the groundwork for that.

(36a) The simplest isometries. A hyperbolic isometry is a map  $\Phi : \mathbb{H} \to \mathbb{H}$  which is reversible, and compatible with all notions of hyperbolic geometry we have introduced. Namely, it:

- (1) preserves angles (in the sense of the angle between the tangent lines, at the intersection of two curves);
- (2) preserves hyperbolic distances;
- (3) preserves hyperbolic arclengths of curves;
- (4) preserves hyperbolic areas of regions;
- (5) takes hyperbolic geodesics to hyperbolic geodesics;
- (6) takes hyperbolic circles to hyperbolic circles.

These are not all logically independent. For instance, there's an implication  $(2) \Rightarrow (6)$  (because circles are defined in terms of distances). All the transformations which we'll discuss have those properties, even though we won't verify them.

Let's introduce some special examples of hyperbolic isometries. The simplest one are (horizontal) translations:

(36.1) 
$$\Phi(x,y) = (x+b,y), \text{ where } b \text{ is some real number.}$$

Vertical translations can't be allowed. For starters, a vertical translation is not an invertible map from the upper half-plane to itself; and even if we somehow ignored that, it fails to have the required properties. Instead, we have (radial) rescalings:

(36.2) 
$$\Phi(x,y) = (ax,ay)$$
, where a is some positive real number.

(36b) Hyperbolic rotations. Clearly, there should be some analogue of rotations. Ordinary Euclidean rotations won't do, because they don't take  $\mathbb{H}$  to  $\mathbb{H}$ . Our first intuition is that a rotation should have a center that's fixed. Let's just look at rotations with center i = (0, 1). These should be hyperbolic isometries that satisfy  $\Phi(i) = i$ . What other properties should such a transformation have?

- Since it fixes i and preserves distances, each hyperbolic circle with center i must be preserved under  $\Phi$ .
- It must send any geodesic passing through i to another such geodesic.
- Presumably, to deserve the name,  $\Phi$  should rotate tangent directions at the point i by some (anticlockwise) angle, let's call it  $\theta$ .

What we are saying is that a hyperbolic rotation should preserve the "hyperbolic polar coordinate system" given by geodesics through i and hyperbolic circles centered at i:

This idea, together with the fact that the derivative of  $\Phi$  at the point i is a rotation by  $\theta$ , completely describes the transformation. There's also a formula: the hyperbolic rotation with center i and angle  $\theta$  is, in complex coordinates,

(36.4) 
$$\Phi(z) = \frac{\cos(\theta/2)z + \sin(\theta/2)}{\cos(\theta/2) - \sin(\theta/2)z}.$$

While this formula is not easy to parse, it certainly satisfies

(36.5) 
$$\Phi(i) = \frac{\cos(\theta/2)i + \sin(\theta/2)}{\cos(\theta/2) - i\sin(\theta/2)} = \frac{i(\cos(\theta/2) - i\sin(\theta/2))}{\cos(\theta/2) - i\sin(\theta/2)} = i.$$

A computation of the derivative (Jacobian) of  $\Phi$  at the point z = i shows that it really rotates tangent lines by  $\theta$ ; but we'll have to omit that.

Example 36.1. The simplest example of a hyperbolic rotation occurs for  $\theta = \pi$ . This is called an inversion:

(36.6) 
$$\Phi(z) = -\frac{1}{z} = -\frac{\bar{z}}{|z|^2},$$

or in real coordinates,

(36.7) 
$$\Phi(x,y) = \frac{(-x,y)}{x^2 + y^2}.$$

It takes  $\{x^2 + y^2 = r\}$  to  $\{x^2 + y^2 = 1/r\}$  for any r, hence the name; and it also flips the sign of the x-coordinate.

(36c) What we can do with them. Isometries can often be used to bring geometric objects into a position where they are more convenient for coordinate computations. This may involve one of the transformations listed above, or more typically the composition of several of them.

FACT 36.2. Given two points z and w, there is an isometry  $\Phi$  such that  $\Phi(z) = w$ .

Let's first assume w = i = (0, 1). One can rescale z so that its y-coordinate becomes 1, and then use horizontal translation to move it to (0, 1), so that works. How about the general case? Well, first we move z to (0, 1), and then we use the reverse of that argument to move (0, 1) to w.

FACT 36.3. Given two geodesics c and d, there is an isometry  $\Phi$  such that  $\Phi(c) = d$ .

Let's pick some point w on our geodesic c. We can find a first isometry that moves that point to (0,1). After applying that, our geodesic will be one that goes through (0,1). By applying a hyperbolic rotation, we can rotate the tangent line at (0,1) of our geodesic so it points vertically. Since a geodesic is determined by one point and the tangent line at that point, the entire geodesic ends up being the y-axis. This argument proves that we can transform c to the y-axis, and using the reverse of that, we can then map the y-axis to d.

FACT 36.4. Given any hyperbolic triangle, there is an isometry  $\Phi$  such that after applying that isotopy, one of the vertices of the triangle is i, and the other vertex is  $e^ri$  for some r > 0.

That almost follows from what we've said. We can pick a side of the triangle, and use an isometry to take that to the y-axis. Then, a suitable rescaling takes the bottom vertex to (0,1) and the top vertex to  $(0,e^r)$ , as desired.

As an example of how these arguments can be useful, remember our theorem from last time, that the hyperbolic distance between two points is the minimal arclength of a path connecting them, and that length-minimizing paths follow geodesics. We only proved this for points of the form (0,1) and  $(0,e^r)$ . But by applying an isometry (which preserves both distance and arclength), the general case follows. The same idea applies to Gauss-Bonnet, which was the other issue listed at the end of the previous lecture.

(36d) The general formula. Here's the general form of hyperbolic isometries. Take a real  $2 \times 2$  matrix A, with  $\det(A) > 0$ . Each such matrix gives rise to a hyperbolic isometry A, like this:

(36.8) 
$$A = \begin{pmatrix} a & b \\ c & d \end{pmatrix}, \text{ we have } \Phi_A(z) = \frac{az+b}{cz+d}.$$

Note that A and  $\lambda A$ , for any  $\lambda \neq 0$ , give the same transformation. So there are really three (not four) degrees of freedom in choosing  $\Phi_A$ . The previously discussed classes of transformations are all special cases. For (horizontal) translations, take

(36.9) 
$$A = \begin{pmatrix} 1 & b \\ 0 & 1 \end{pmatrix} \implies \Phi_A(z) = z + b$$

For (radial) expansions,

(36.10) 
$$A = \begin{pmatrix} a & 0 \\ 0 & d \end{pmatrix} \implies \Phi_A(z) = (a/d)z$$

with ad > 0 (as far as  $\Phi_A$  is concerned, only the quotient a/d > 0 matters). The case of hyperbolic rotations (with center i) is:

$$(36.11) A = \begin{pmatrix} \cos(\theta/2) & \sin(\theta/2) \\ -\sin(\theta/2) & \cos(\theta/2) \end{pmatrix} \implies \Phi_A(z) = \frac{\cos(\theta/2)z + \sin(\theta/2)}{\cos(\theta/2) - \sin(\theta/2)z}.$$

It may be a little weird that the hyperbolic rotation that rotates tangent lines at i by  $\theta$  is given by the Euclidean rotation matrix A with angle  $-\theta/2$ ; but that's just a clash of conventions, nothing to get excited about.

The reason for writing the parameters as matrix entries is that composition of isometries is governed by matrix multiplication,

(36.12) 
$$\Phi_A(\Phi_B(z)) = \Phi_{AB}(z).$$

The identity matrix gives the identity (trivial) isometry, and therefore, the inverse matrix gives the inverse isometry; so the class of  $\Phi_A$  is closed under composition as well as passing to inverses. This ease in writing down compositions is precisely the advantage of the matrix framework.

Example 36.5. Suppose that we want to have hyperbolic rotations centered not at i, but at some arbitrary point z = (x, y). We can achieve that by composing three elements:

• First, we use an initial isometry to move z to i. One can construct this out of translations and expansions (Fact 36.2). As a formula:

$$(36.13) B = \begin{pmatrix} 1 & -x/y \\ 0 & 1 \end{pmatrix} \begin{pmatrix} 1 & 0 \\ 0 & y \end{pmatrix} = \begin{pmatrix} 1 & -x \\ 0 & y \end{pmatrix}.$$

- Then, we take the matrix A from (36.11) to do the rotation centered at i;
- Finally, we use  $B^{-1}$  to move i back to z.

The outcome is that our desired rotation-with-center-z is given by the matrix (we multiply by y to simplify the formula, that doesn't affect the isometry)

(36.14) 
$$yB^{-1}AB = \begin{pmatrix} y\cos(\theta/2) - x\sin(\theta/2) & (x^2 + y^2)\sin(\theta/2) \\ -\sin(\theta/2) & y\cos(\theta/2) + x\sin(\theta/2) \end{pmatrix}.$$

Strictly speaking, we have only covered half of the symmetries of the hyperbolic plane: reflection along the y-axis, R(x,y) = (-x,y), should also be allowed. A general symmetry is then either  $\Phi_A$  or  $R\Phi_A$ . However, for most purposes the  $\Phi_A$  are enough, and their formalism is particularly satisfying.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 37. The geodesic equation

In hyperbolic geometry, lengths and distances are changed from their Euclidean counterparts. This then affects the notion of straight line (geodesic). At the root of those changes lies the length element  $y^{-1}\sqrt{dx^2 + dy^2}$ . What happens if instead of  $y^{-1}$ , one takes a general (positive) function of (x, y)? This gives a lot of different "curved geometries". What are geodesics in each of those? We will get to the answer by:

- introducing a differential equation for parametrized curves (the geodesic equation);
- examining the geometric meaning of that equation; and
- for hyperbolic geometry, checking that the solutions agree with our previous definition of geodesic.
- (37a) Curved geometries. A curved geometry is specified by its infinitesimal length element

(37.1) 
$$e^{\psi(x,y)} \sqrt{dx^2 + dy^2},$$

where  $\psi(x,y) \in \mathbb{R}$  can be any function. Hyperbolic geometry is one example, with  $\psi(x,y) = -\ln(y)$ . The factor  $e^{\psi(x,y)}$  tells us how much the geometry is "bunched up" around (x,y). As before, the notion of arclength gets modified accordingly:

(37.2) 
$$\operatorname{length}(c) = \int e^{\psi(c(t))} ||c'(t)|| dt.$$

If you think of c(t) as a point moving in time, then  $e^{\psi(c(t))}||c'(t)||$  is its speed with respect to our curved geometry.

DEFINITION 37.1. The geodesic equation for a curve  $c(t) \in \mathbb{R}^2$  is

(37.3) 
$$c''(t) - \|c'(t)\|^2 \nabla \psi_{c(t)} + 2(\nabla \psi_{c(t)} \cdot c'(t)) c'(t) = 0.$$

There are always the boring stationary solutions c(t) = constant. The other solutions define curves that we call the geodesics for our geometry.

In the Euclidean plane  $(\psi(x,y)=0)$  the equation reduces to c''(t)=0, which is Newtonian motion with no force applied; the solutions are c(t)=vt+w for  $v,w\in\mathbb{R}^2$ , meaning straight-line motion at constant speed. For a general curved geometry, the geodesic equation yields precisely the analogue of straight-line motion.

(37b) The geodesic equation in (x, y)-components. The geodesic equation may not look particularly appealing, but we'll get used to it and its properties. It is an equality of vectors, which we can separate into components c(t) = (x(t), y(t)). One has  $||c'(t)||^2 = x'(t)^2 + y'(t)^2$ , and  $\nabla \psi = (\partial_x \psi, \partial_y \psi)$ . After some cancellations, the component equations are:

(37.4) 
$$x''(t) + (x'(t)^2 - y'(t)^2)\partial_x \psi + 2x'(t)y'(t)\partial_y \psi = 0, y''(t) + (y'(t)^2 - x'(t)^2)\partial_y \psi + 2x'(t)y'(t)\partial_x \psi = 0.$$

Here, the partial derivatives of  $\psi$  are taken at the point (x(t), y(t)).

Example 37.2. Let's look at hyperbolic geometry. There, the equations become

(37.5) 
$$x''(t) - 2\frac{x'(t)y'(t)}{y(t)} = 0,$$
$$y''(t) + \frac{x'(t)^2 - y'(t)^2}{y(t)} = 0.$$

A useful trick is to rewrite them as

(37.6) 
$$\frac{d}{dt} \frac{x'(t)}{y(t)^2} = 0,$$

$$\frac{d}{dt} \frac{x'(t)x(t) + y'(t)y(t)}{y(t)^2} = 0.$$

We can integrate,

(37.7) 
$$x'(t) = Ay(t)^{2},$$
$$x'(t)x(t) + y'(t)y(t) = By(t)^{2}.$$

for some constants A, B. For A = 0, we have x'(t) = 0, so (x(t), y(t)) moves along a vertical line. What if  $A \neq 0$ ? We combine the two equations,

$$(37.8) x'(t)x(t) + y'(t)y(t) = (B/A)x'(t) \Leftrightarrow (x(t) - B/A)x'(t) + y(t)y'(t) = 0,$$

and then integrate again:

(37.9) 
$$(x(t) - B/A)^2 + y(t)^2 = C.$$

This describes the circle of radius  $\sqrt{C}$  centered at the point (B/A, 0) on the horizontal axis. In this way, we have recovered all the hyperbolic geodesics.

(37c) The geodesic equation in components parallel and orthogonal to the motion. Of course, (x, y)-coordinates are somewhat arbitrary. A better approach is to separate the geodesic equation into a component that is a multiple of c'(t), and a component which is orthogonal to it. This is done by taking the dot product and the cross product of the equation with c'(t) (for our notion of cross product of vectors in  $\mathbb{R}^2$ , which produces a number). The outcome, again after some cancellation, is:

(37.10) 
$$(c''(t) + ||c'(t)||^2 \nabla \psi_{c(t)}) \cdot c'(t) = 0,$$

(37.11) 
$$(c''(t) - ||c'(t)||^2 \nabla \psi_{c(t)}) \times c'(t) = 0.$$

FACT 37.3. Along a solution c(t) of the geodesic equation, the speed (with respect to our curved geometry)  $e^{\psi(c(t))} \|c'(t)\|$  is constant.

This is equivalent to saying that  $e^{2\psi(c(t))}\|c'(t)\|^2$  is constant. If we differentiate that, we get

(37.12) 
$$\frac{d}{dt} \left( e^{2\psi(c(t))} \|c'(t)\|^2 \right) = 2e^{2\psi(c(t))} \left( c''(t) + \|c'(t)\|^2 \nabla \psi_{c(t)} \right) \cdot c'(t) \right),$$

which is zero by (37.10). Physically, think of this (after dividing by 2) as conservation of kinetic energy,  $\frac{1}{2}$ speed<sup>2</sup>, which is a feature of Newtonian motion.

The other equation (37.11) is more crucial geometrically, since it determines how a geodesic bends, but harder to explain. If we have a curve c(t) with  $c'(t) \neq 0$ , we can look at ones that have been displaced sideways with respect to the tangent direction, by which we mean

(37.13) 
$$d(t) = c(t) + \delta J c'(t).$$

where we have used the 90° rotation matrix  $J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ , and  $\delta$  is a small constant, which governs the amount and direction (left or right) of displacement.

LEMMA 37.4. Suppose that c'(t) is never zero. Then the arclength integrand for d(t) is approximately (to first order in  $\delta$ , which means ignoring terms that are quadratic or higher order in  $\delta$  and  $\delta'$ ) given by

$$(37.15) e^{\psi(d)} \|d'(t)\| \approx e^{\psi(c)} \Big( \|c'(t)\| + \frac{\delta}{\|c'(t)\|} (c''(t) - \|c'(t)\|^2 \nabla \psi) \times c'(t) \Big).$$

I will spare you the gory details. The important point is that what appears in (37.15) is  $\delta/\|c'(t)\|$  times the second part of the geodesic equation. In Euclidean geometry, whenever c(t) curves to the left, displacing it in that direction makes it shorter, and similar for curving to the right. Straight lines are characterized by the fact that the displaced version proceed at the same speed as the original curve. In our context, the same characterization of geodesics is at least approximately true (to first order in  $\delta$ ).

THEOREM 37.5. Suppose that c(t),  $t \in [a,b]$ , is a curve that proceeds with constant speed in our geometry. Suppose also that among all curves connecting the endpoints c(a) and c(b), ours achieves the minimal possible arclength. Then c(t) is a solution of the geodesic equation.

As before, we consider displaced curves, but where the amount of displacement  $\delta(t)$  is now a function, satisfying  $\delta(a) = \delta(b) = 0$ . This condition ensures that the displaced curve d(t) has the same endpoints as c(t). By assumption, length $(c) \ge \text{length}(d)$ , which for small displacements (at first order) implies that

(37.16) 
$$\int_{a}^{b} \delta(t) ((c'' - ||c'||^{2} \nabla \psi) \times c') dt \ge 0.$$

This must hold for all possible  $\delta(t)$ . In particular, we can take

(37.17) 
$$\delta(t) = -f(t)((c'' - ||c'||^2 \nabla \psi) \times c'),$$

where f(t) is a function defined for  $t \in [a, b]$ , such that f(a) = f(b) = 0, and all other values f(t) are positive. In that case, what (37.16) says is that

(37.18) 
$$\int_{a}^{b} -f(t) ((c'' - ||c'||^{2} \nabla \psi) \times c')^{2} dt \ge 0.$$

There's an almost-contradiction here: the integrand is  $\leq 0$ , and the integral is supposed to be  $\geq 0$ . The only way out is that the integrand is actually zero. But since f(t) > 0 for  $t \in (a,b)$ , this means that  $(c'' - \|c'\|^2 \nabla \psi) \times c'$  must be zero, which is (37.11) (the other equation (37.10) is already true, because of the assumption that c advances with constant speed).

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 38. Behaviour(s) of geodesics

In the last lecture, we encountered the geodesic equation for general curved geometries, but the only concrete example we considered was hyperbolic geometry, where we already knew what the outcome would be. This time, we'll proceed along two lines of enquiry:

- we get more experience with the general properties of solutions of the geodesic equation;
- and we look at special classes of geometries where solutions become easier to find.

The guiding question is to what extent solutions, in a general geometry, share (or do not share) the qualitative behaviour of straight lines in Euclidean geometry.

(38a) The geodesic equation, revisited. We decided that in a curved geometry

(38.1) 
$$e^{\psi(x,y)} \sqrt{dx^2 + dy^2},$$

the analogue of straight-line motion should be a curve  $c(t) \in \mathbb{R}^2$  which solves

(38.2) 
$$c'' - \|c'\|^2 \nabla \psi + 2(\nabla \psi \cdot c')c' = 0.$$

We can look at this from a pure differential equations viewpoint, and check some basic properties:

- If c(t) is a geodesic, then so is c(t+T) for any constant T. In other words, there's no geometrically preferred "starting point" on a geodesic.
- If c(t) is a geodesic, then so is c(Rt) for any constant R (including a negative one). To see that, note that the first derivatives of c(Rt) scale linearly with R, and the second derivatives quadratically. But since the equation has quadratic terms in c'(t), everything works out.
- Given a starting point and a starting velocity vector, there is one and only one geodesic c such that c(0) is our starting point and c'(0) is our starting velocity vector. (This is a general property of second order differential equations, and the only time that we'll use the theory of such equations.)

Combining all three properties, one sees the following:

FACT 38.1. If two geodesics become tangent at some point, then they trace out the same curve (in fact, up to reparametrizations c(Rt + T), the two geodesics are the same).

(38b) Translationally invariant geometries. Suppose that our geometry depends only on one of the variables,  $\psi = \psi(y)$ . The geodesic equations simplify to

(38.3) 
$$x'' + 2x'y'(d\psi/dy) = 0,$$
$$y'' + ((y')^2 - (x')^2)(d\psi/dy) = 0,$$

There are a few special solutions which are easy to describe.

FACT 38.2. Any vertical line can be parametrized so that it becomes a geodesic:

(38.4) 
$$x(t) = C$$
,  $y(t)$  a solution of  $y'' + (y')^2 (d\psi/dy) = 0$ .

FACT 38.3. If the derivative  $d\psi/dy$  is zero ( $\psi$  has a critical point) for some value of y, then that particular horizontal line (with x(t) = A + Bt) is also a geodesic.

We can gain some understanding of more general solutions, but that requires digging deeper into the equations. The first line of (38.3) can be written as

$$\frac{d}{dt}(e^{2\psi}x') = 0.$$

This generalizes something we've seen for hyperbolic geometry, namely the first equation in (37.6). There is an underlying principle from classical mechanics, where any symmetry gives rise to a quantity that's constant under the motion. In our case, the symmetry of the geometry under horizontal translations gives rise to the invariant quantity  $e^{2\psi}x'$ , which is the horizontal component of momentum. Speaking of conserved quantities, we also have conservation of speed (which, in mechanics, arises from the time-translation invariance of the geodesic equation). The two conserved quantities give us the equations

(38.6) 
$$x' = e^{-2\psi}A,$$
$$(x')^{2} + (y')^{2} = e^{-2\psi}B,$$

with constants A and B. Inserting them into the second line of (38.3) gives us

(38.7) 
$$y'' + (e^{-2\psi}B - 2e^{-4\psi}A^2)(d\psi/dy) = 0.$$

This kind of equation, which we can write as y'' = -dU/dy with

(38.8) 
$$U(y) = \int (e^{-2\psi}B - 2e^{-4\psi}A^2)(d\psi/dy) dy = -\frac{B}{2}e^{-2\psi(y)} + \frac{A^2}{2}e^{-4\psi(y)},$$

has a well-known meaning. It describes the motion of a Newtonian particle y(t) (with one degree of freedom) in the potential U(y), like someone skiing over a hill of shape U(y). Note however that U(y) depends on A and B – and those depend on which specific geodesics we are considering: they can be read off from the starting position and velocity at any specific time.

When doing this analysis, we had one particular kind of behaviour in mind. Suppose that we are at a local maximum of the function which defines the curved geometry. For simplicity, let's say that the maximum happens at y = 0, and has the form

$$\psi(0) = 0, \ \psi'(0) = 0, \ \psi''(0) < 0.$$

We know then that the x-axis with its standard parametrization (x(t) = t, y(t) = 0) is a geodesic. What happens if we start at a point on the x-axis, but with a starting direction that's not quite horizontal? So

$$x'(0) = 1,$$

$$y(0) = 0;$$

$$y'(0)^{2} = \epsilon \text{ for some } \epsilon.$$

By plugging that into (38.6), we see that A=1,  $B=1+\epsilon$ . The potential is therefore

(38.11) 
$$U(y) = -\frac{1+\epsilon}{2}e^{-2\psi(y)} + \frac{1}{2}e^{-4\psi(y)}.$$

It is easy to see that U'(0) = 0. A more laborious computation shows that

$$(38.12) U''(0) = -(1+\epsilon)\psi''(0) < 0$$

So the potential has a minimum at y=0. If  $\epsilon$  is small, our picture is therefore that of a particle oscillating in the bottom of a trough. This means that y(t) will perform small oscillations around 0, while  $x'(t) = e^{-2\psi(y)}$  means that x(t) keeps moving to the right at a speed approximately equal to 1. Our geodesic will behave like this:

(It's not a simple sin-wave, even though qualitatively it looks the same.) From that, we take away the following general insight:

FACT 38.4. In general, it is possible for two geodesics to intersect each other more than once; in fact, they can intersect infinitely many times.

(38c) Rotationally invariant geometries. Suppose that our geometry is invariant under rotations around the origin, which means that  $\psi = \psi(r)$  can be written as a function of  $r = \sqrt{x^2 + y^2}$ . We could analyze this as before, but there's a change of coordinate trick that we can do instead, and which saves us a lot of time. Namely, use the following version of polar coordinates:

(38.14) 
$$x = e^{\rho} \cos(\theta),$$
$$y = e^{\rho} \sin(\theta).$$

A computation, which we omit, shows the following:

PROPOSITION 38.5. (x(t), y(t)) is a geodesic for our rotationally invariant geometry if and only if  $(\theta(t), \rho(t))$  is a geodesic for the geometry  $\psi(e^{\rho}) + \rho$ .

If we think of  $(\theta, \rho)$  as Cartesian coordinates in a plane, then  $\psi(e^{\rho}) + \rho$  is a translation-invariant geometry. For such geometries, we know (Fact 38.2) that all lines  $\theta = constant$  are geodesics, and that implies the following:

FACT 38.6. In a rotationally invariant geometry, all radial lines (straight lines through the origin), parametrized in an appropriate way, are geodesics.

In  $(\theta, \rho)$  coordinates, we also know (Fact 38.3) that a line  $\rho = constant$  is a geodesic if, at that value of  $\rho$ , the function defining the geometry has a critical point. In our case, that condition says that

(38.15) 
$$\frac{d}{d\rho}(\psi(e^{\rho}) + \rho) = 0 \iff \psi'(e^{\rho}) = -1/e^{\rho}.$$

Bearing in mind that  $e^{\rho} = r$  is the radius, we find that:

FACT 38.7. In a rotationally invariant geometry, the circle of radius r > 0 around the origin is a geodesic if and only if  $\psi'(r) = -1/r$  (at that value of r).

It is easy to construct geometries for which this equation has solutions (indeed, you may have already seen one in Problem 37.2, even though there, we did not use radial coordinates). This illustrates:

FACT 38.8. In general, it is possible for a geodesic to come back to its starting point, and even to be periodic.

By dividing such a circle into a small and a large piece, we see:

FACT 38.9. In general, it is possible for a segment of a geodesic to not be the shortest path between its endpoints.

In our previous discussion of translationally-invariant geometries we found that under certain assumptions, if a horizontal line is a geodesic, there are other geodesics that oscillate around it. In the rotationally-invariant case, that translates into geodesics that oscillate around circles:

(38.16)

In general, the oscillation is by no means guaranteed to return to the initial position after going once, or even several times, round the circle. Instead, the geodesic could, as it goes, gradually weave a denser and denser web of oscillations around the circle, without ever repeating. We learn:

FACT 38.10. It is possible for a geodesic to cross itself, even infinitely many times.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 39. Curvature

In this lecture, we look at the quantity that gives a precise meaning to the expression "curved geometries", namely the (Gauss) curvature.

- We define curvature, and compute a few simple examples.
- It's a good idea to average (integrate) the curvature over regions of our geometry. This leads to a general version of the Gauss-Bonnet theorem.

(39a) From geodesics to curvature. We saw that the geodesic equation can be thought of as consisting of two parts:

- (39.1) along a geodesic c(t), the speed  $e^{\psi(c(t))} ||c'(t)||$  is constant;
- (39.2) the geodesic tries to "not turn left or right",  $(c''(t) ||c'(t)||^2 \nabla \psi_{c(t)}) \times c'(t) = 0$ .

While these equations are hard to solve, we can suppose that we know one (nonconstant) solution c(t), and study the behaviour of other solutions which are close by. Specifically, let's take sideways displacement by a varying amount  $\delta(t)$ ,

$$(39.3) d(t) = c(t) + \delta(t)Jc'(t),$$

where J is the matrix that rotates vectors by 90°. Look at (39.2) for d(t), and think of  $\delta(t)$  as small, so that all terms which are quadratic or higher order in  $\delta(t)$  can be omitted. The outcome, after a lot of computation which we skip, is the approximate geodesic equation

(39.4) 
$$\delta''(t) - \|c'(t)\|^2 (\Delta \psi)_{c(t)} \delta(t) = 0,$$

where  $\Delta \psi = \partial_x^2 \psi + \partial_y^2 \psi$  is the Laplace operator (which we've also seen in Chapter III). It contains an important geometric quantity:

Definition 39.1. The curvature of a curved geometry is the function

$$(39.5) K = -e^{-2\psi} \Delta \psi.$$

If the geodesic proceeds with unit speed in our geometry, meaning that  $e^{\psi(c(t))}||c'(t)|| = 1$ , we can write (39.4)

(39.6) 
$$\delta''(t) + K(c(t))\delta(t) = 0.$$

This equation describes the approximate behaviour of geodesics that are close to our original c(t). For instance, suppose that we have constant positive curvature K = C > 0. Then (39.6) becomes  $\delta'' + C\delta = 0$ , which has the solutions  $\delta(t) = A\sin(\sqrt{C}t) + B\cos(\sqrt{C}t)$ . Hence, in this case we see nearby geodesics that oscillate around the original one (as a qualitative conclusion, this is correct, in spite of the fact that we're looking at an approximation to the geodesic equation).

Example 39.2. Hyperbolic geometry,  $\psi = -\ln(y)$ , has constant negative curvature:

(39.7) 
$$K = -y^2 \Delta(-\ln(y)) = -1.$$

Example 39.3. Take

$$(39.8) \qquad \qquad \psi(y) = -\ln(\cosh(y)).$$

This is the length element for a round sphere parametrized by the Mercator map-making projection. The curvature is constant, but with the opposite sign.

(39.9) 
$$K = \cosh(y)^2 (d^2/dy^2) (\ln(\cosh(y))) = \cosh(y)^2 (d/dy) \tanh(y) = 1.$$

(39b) The integrated curvature. In any curved geometry, areas are computed by

(39.10) 
$$\operatorname{area}(U) = \int_{U} e^{2\psi(x,y)} dx \, dy.$$

Similarly, the geometrically correct way to integrate a function f(x,y) over a region U is

(39.11) 
$$\int_{U} e^{2\psi(x,y)} f(x,y) dx dy.$$

This encodes the sense of integral as an average, where regions with larger  $\psi$  should count more. Applying that idea to curvature, we define the integrated curvature over a region U to be

(39.12) 
$$\int_{U} e^{2\psi} K \, dx \, dy = \int_{U} (-\Delta \psi) \, dx \, dy.$$

Example 39.4. Suppose that we have a doubly-periodic geometry,

(39.13) 
$$\psi(x,y) = \psi(x+1,y) = \psi(x,y+1).$$

Then, the integrated curvature over  $U = [0,1]^2$  is zero. This is easy:

(39.14) 
$$\int_{0}^{1} \int_{0}^{1} (\partial_{x}^{2} \psi) dx dy = \int_{0}^{1} (\partial_{x} \psi) \Big|_{x=0}^{x=1} dy = 0$$

by periodicity, and the same for  $\partial_{\nu}^{2}\psi$ .

One can think of the example above as a statement about curved geometries on the torus (the torus in question is obtained by identifying opposite sides of U). Since the integrated curvature is zero, it's impossible for such a geometry to have curvature which is everywhere positive (or everywhere negative). This is an instance of a general relationship between curvature and topology.

Let's take a bounded region U, with no holes and with smooth boundary. We parametrize the boundary by a curve c(t) with period T > 0, meaning c(t) = c(t+T), going anticlockwise around it. Green's theorem says that

(39.15) 
$$\int_{U} (-\Delta \psi) \, dx \, dy = \int_{0}^{T} -(\nabla \psi)_{c(t)} \times c'(t) \, dt.$$

You're maybe used to one side of Green's formula being a contour integral. Here, we have spelled out that integral using the parametrization. Suppose that c is a geodesic: from the geodesic equation  $\times c'(t)$ , which is

(39.16) 
$$(c''(t) - ||c'(t)||^2 \nabla \psi_{c(t)}) \times c'(t) = 0,$$

we get

(39.17) 
$$\int_0^T -(\nabla \psi)_{c(t)} \times c'(t) dt = \int_0^T \frac{c'(t) \times c''(t)}{\|c'(t)\|^2} dt.$$

We have seen this integral before, it's just  $2\pi$  times the rotation number of c. Remember we had Whitney's formula, which relates the rotation number to selfintersections: here we have no selfintersections, and we go anticlockwise, so the formula says that the winding number is +1. We put everything together:

Theorem 39.5. If the boundary of U is a periodic geodesic, the integrated curvature on U is

(39.18) 
$$\int_{U} (-\Delta \psi) \, dx \, dy = 2\pi.$$

What if instead having a region with smooth boundary, we have one with n corners? The rotation number integral still computes by how much the tangent direction rotates on each side of the boundary, but obviously misses out on the sudden change of tangent direction at the corners. Hence, it computes  $2\pi - \theta_1 - \cdots - \theta_n$ , where the  $\theta_i \in (-\pi, \pi)$  are the angles (positive if counterclockwise, negative if clockwise) by which the tangent direction changes:

In terms of the more familiar interior angles at the corners,  $\alpha_k = \pi - \theta_k$ , the rotation number integral is  $(2 - n)\pi + \theta_1 + \cdots + \alpha_n$ . The outcome is:

THEOREM 39.6. (General Gauss-Bonnet) In any curved geometry, let U be a geodesic n-gon. By this we mean a region without holes, whose boundary is a union of n segments of geodesics, coming together at the corners with interior angles  $\alpha_k \in (0, 2\pi)$ . Then

(39.20) 
$$\int_{U} (-\Delta \psi) \, dx \, dy = \alpha_1 + \dots + \alpha_n + (2 - n)\pi.$$

For hyperbolic geometry, where K = -1, the integrated curvature is -area(T), and this is the theorem we've seen before, in the case of triangles (n = 3).

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 40. Geometry of combinatorial surfaces

A priori, combinatorial surfaces seem hardly the kind of object that can have curvature, but one can in fact make sense of that. The triangles makinf up the surface are thought of as flat, and the curvature is concentrated at the vertices (like a Dirac  $\delta$ -function), where it appears in the form of an angle defect. In this lecture,

- we introduce combinatorial surfaces with added geometric data;
- we explain a version of Gauss-Bonnet for such surfaces;
- finally, we return to our discussion of polygonal billiards, and explain how this gives rise to a particular construction of surfaces.

(40a) Geometric combinatorial surfaces. Recall that a combinatorial surface S is a special case of an abstract complex. As such, it is constructed from vertices, edges and triangles, according to given incidence rules. A geometry on a combinatorial surface is specified like this: each edge (i, j) should be given a positive length  $l_{ij} > 0$ ; such that for each triangle (p, q, r), we have the triangle inequalities

$$l_{pr} < l_{pq} + l_{qr},$$

$$l_{pq} < l_{pr} + l_{qr},$$

$$l_{qr} < l_{pq} + l_{pr}.$$

Visually, one thinks of each triangle as drawn in the Euclidean plane (up to Euclidean transformations, which means that only its congruence class matters), in a way which is compatible with the prescribed edge-lengths. This realizability is equivalent to (40.1), and the lengths determine the congruence class.

Look at a vertex of our surface. By definition, it is surrounded by a collection of triangles, which can be drawn in the plane as in (31.1). However, this picture isn't necessarily compatible with realizing the triangles geometrically; in the relevant congruence classes, the angles surrounding the vertex may not add up to  $2\pi$ . We give this defect a name: the discrete curvature at our vertex is

(40.2) 
$$\kappa_{vertex} = 2\pi - \sum (adjacent \ angles \ of \ the \ triangles \ at \ the \ vertex).$$

For bookkeeping purposes, since the vertices are numbered as  $1, \ldots, n_0$ , we have discrete curvatures  $\kappa_1, \ldots, \kappa_{n_0}$ .

PROPOSITION 40.1. The sum  $\sum_{i=1}^{n_0} \kappa_i$  of the discrete curvatures at all vertices of the surface S equals  $2\pi\chi(S)$ , where  $\chi$  is the Euler characteristic.

This is completely elementary:  $\sum_{i} \kappa_{i}$  is  $2\pi n_{0}$  (the number of vertices) minus the sum of all angles that occur on our surface, which is  $\pi n_{2}$  (the number of triangles). Because of the surface condition, the number of edges is  $n_{1} = \frac{3}{2}n_{2}$ . Therefore,

(40.3) 
$$2\pi\chi(S) = 2\pi(n_0 - n_1 + n_2) = 2\pi(n_0 - n_2/2) = 2\pi n_0 - \pi n_2 = \sum_{i=1}^{n} \kappa_i.$$

Example 40.2. Let's think of an icosahedron, in its original incarnation as a Platonic solid (all edges have the same length). Since there are five equilateral triangles adjacent to each vertex,  $\kappa_i = 2\pi - 5(\pi/3) = \pi/3$ . There are twelve vertices, so  $\sum_i \kappa_i = 4\pi$ . Indeed, we know that the Euler characteristic is 2.

Example 40.3. For a torus, realized in any way as a combinatorial surface, the Euler characteristic is zero. Hence, the discrete curvatures must sum to zero (either they are all zero, or else curvatures of either sign must occur).

Example 40.3 should remind you of the statement about the integral of the Gaussian curvature for a doubly periodic geometry, Example 39.4. Indeed, there is a Gauss-Bonnet theorem for curved surfaces, which we can't state, not having the definition of such a surface; and then, Proposition 40.1 can be viewed as the discrete combinatorial analogue of that theorem.

(40b) Geodesics on combinatorial surfaces. A geodesic on the ordinary plane is just a straight line. Similarly, in a combinatorial surface that's been equipped with a geometry, we can move inside each triangle in a straight-line constant-speed motion; and whenever we cross an edge, we continue onto the adjacent triangle with the same speed and at the same angle from their common edge. The outcome is called a combinatorial geodesic. If we happen to run into a vertex, the behaviour becomes undefined, and the geodesic will end there.

EXAMPLE 40.4. The following picture shows a tetrahedron as one would make it out of paper, folding the outer triangles up and gluing their sides together; and a periodic geodesic on it:

(40c) Translation surfaces. The description of combinatorial geodesics may have reminded you of something, namely our original discussion of polygonal billiards. There is indeed a connection between the two, for polygons with rational angles. Let's more specifically take a triangle whose angles are integer multiples of  $180^{\circ}/N$  for some N. We can associate to such a triangle a combinatorial surface, called its translation surface. To do that, simply take the triangle, and start repeatedly reflecting it along its sides. The reflected triangles will usually start to overlap, but whenever that happens, we avoid it by translating one of the triangles to somewhere else in the plane. Also, we don't want to keep copies which are just translations of each other, so after finitely many reflections, we will have a complete collection. Moreover, whenever we separate a triangle and its reflected copy by translating them apart, let's remember their original common edge (the edge of the reflection). Those edges are glued back together (in an abstract

sense, meaning they are the same edge in the abstract complex) to form the *translation surface* associated to our triangle.

Example 40.5. Take a triangle with angles  $(\pi/4, \pi/4, \pi/2)$ . The associated translation surface is a torus, which consists of the following pattern of triangles with the sides identified.

Since this triangle has symmetries, we have drawn a symbol inside the triangles so that you can see how they are reflected copies of each other. This is the infinite periodic tiling (6.9) "rolled up" into a torus. Note that this translation surface has 4 vertices: both the center and the corner of the square in (40.5) come from the right angle in the original triangle.

Example 40.6. Take a triangle with angles  $(\pi/8, 3\pi/8, \pi/2)$ . Composing two reflections on axes that intersect at a  $\pi/8$  angle gives a  $\pi/4$  rotation, which we can also do repeatedly; from the other angles we don't get any additional rotations. So, we have 8 rotations that we will apply to our triangle, plus reflected versions, making 16 triangles. If we first do the reflections around the  $\pi/8$  vertex, we can draw the 16 without overlap:

However, other reflections will cause opposite sides of this octagon to become identified with each other (the arrow in our picture indicates how that happens). This identification is not the same as when constructing the projective plane: opposite sides are identified by a translation, not by a 180° rotation!

Attentive readers will have noticed a problem, clearly visible in (40.5). Namely, a translation surface may violate one of our original conditions in the definition of abstract complex: there can be two different edges that connect the same endpoints. This is just a bookkeeping problem: originally, we had labeled the edges by their pairs of endpoints; now, we'll just have to index them in some other way, and then remember what the endpoints of each edge are. It's like changing the data structures in our computer code; the actual mathematics remains the same,

including notions of Euler characteristics, Betti numbers, and orientability. Speaking of the latter, translation surfaces are always orientable (this comes from their construction by reflections).

As one can see from the construction, translation surfaces are naturally geometric. Each vertex of a translation surface comes from one of the original vertices of the triangle. Basically, we keep reflecting along lines passing through that vertex until we get back in original position. This means:

FACT 40.7. If a vertex of the translation surface comes from a vertex of the triangle with an angle  $\pi \frac{a}{b}$  (with a and b coprime), the discrete curvature at our vertex will be  $2\pi(1-a)$ .

Example 40.8. For the  $(\pi/8, 3\pi/8, \pi/2)$  triangle, two kinds of vertices (those for the smallest and largest angle) will have discrete curvature zero, but the remaining kind has curvature  $-4\pi$ . There is only one such vertex (it corresponds to the vertices of the octagon in (40.6); the identification of opposite sides causes any two of those to become the same). The discrete Gauss-Bonnet theorem says that the Euler characteristic must be -2. This is not one of the surfaces we've seen before, it's an "orientable genus two surface". Such surfaces are usually shown in space like this:

(40.7)

Our original analysis of billiards trajectories, by drawing them as straight lines continuing into reflected triangles, now turns into the following:

FACT 40.9. The billiards motion in the triangle can be viewed as the motion along geodesics on the associated translation surface.

18.900 Geometry and Topology in the Plane Spring 2023

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.
