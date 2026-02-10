## 18.433 Combinatorial Optimization

## Polyhedral Combinatorics

September 16 Lecturer: Santosh Vempala

So far we have treated graphs as sets of vertices and edges, G=(V,E). One can also think of each edge as an axis. Any point in space corresponds to a graph. The coordinates determine the edge weight.

The point (1,0,1) in this space would correspond to a graph with only 2 edges present (i.e. of weight > 0): (1,2) and (3,1). How would we define a matching? It will also be a point with all coordinates being either 0 or 1. If  $M = e_1, ..., e_k$ , then  $X_m = (1,0,1,...,0,1)$ , where the first coordinate indicates that  $e_1 \in M$ , the second coordinate indicates that  $e_2 \notin M$ , and so forth.

We think of matchings as solutions to equations (if it is a point). Consider  $\mathbf{x} = (x_{e_1}, x_{e_2}, ..., x_{e_m})$  as a vector of all edges in the graph.

- 1.  $x_e \in \{0, 1\} \ \forall e \in E$
- 2.  $\sum_{e \in \delta(v)} x_e \le 1 \ \forall v \in V$

Claim 1. Any solution to these two equations is a matching.

**Proof.** If a vertex had more than one incident edge then it wouldn't be a matching.  $\Box$ 

Constraint (1) appears to be very strong. Suppose we replace it with the restriction that  $0 \le x_e \le 1$ . Now there are solutions that aren't matchings.

Consider the two edge graph shown above. The matchings here are (0,1), (1,0), and (0,0). Note that the matchings bound the set of solutions (i.e. their convex hull equals the solution set). Is this always true? Are the "corners" always the matchings?

Consider the complete graph with 3 vertices, with all edge weights equal to one-half. This satisfies both equations. The corners of this shape will be at (1,0,0), (0,0,1), (0,1,0), and  $(\frac{1}{2},\frac{1}{2},\frac{1}{2})$ . The last corner is not a matching, so it is not always true that the corners are the matchings.

## Review of linear algebra and convexity

- $x_1, \ldots, x_m \in \mathbb{R}^n$  (Each  $x_i$  is a vector with n coordinates)
- $\lambda_1, \ldots, \lambda_m \in \mathbb{R}$ .
- A linear combination is  $\lambda_1 x_1 + \lambda_2 x_2 + ... + \lambda_m x_m = \sum \lambda_i x_i$ .
- An affine combination is a linear combination where  $\sum \lambda_i = 1$ .
- A convex combination is an affine combination where  $\lambda_i \geq 0 \ \forall i$ .

For example, given 2 points  $x_1$  and  $x_2$ , what points are convex combinations of them? The answer is the line segment between them. What points are affine combinations? The infinite line through the two points. What about linear combinations? The whole plane (in 3D, this would be the plane defined by  $x_1$ ,  $x_2$ , and the origin).

The linear hull (span) of  $x_1, \ldots, x_n$  is the set of vectors  $\{\Sigma \lambda_i x_i : \lambda_1, \ldots, \lambda_n \in \mathbb{R}\}$ . Similarly, the affine hull is the set of all vectors that are affine combinations of the  $x_i$ 's and the convex hull is the set of all vectors that are convex combinations of the  $x_i$ 's.

Consider three linearly independent points in  $\mathbb{R}^3$ . Their linear hull is the entire space. Their affine hull is the plane defined by the points. Their convex hull is the triangle having the

three points as vertices, within the plane defined by the three points. A linear hull always contains the origin  $(\lambda_i = 0)$ .

A set S is convex if  $\forall x, y \in S$ , the line segment from x to y is also contained in S, i.e. any convex combination of x and y is in the set:  $\lambda x + (1 - \lambda)y \in S \ \forall \lambda, 1 \ge \lambda \ge 0$ .

One can prove that the convex hull of  $x_1, \ldots, x_m$  is the smallest convex set containing them.

A convex polytope is the convex hull of a finite set of points. It has a sharp, cornered structure. A hyperplane is a set of the form  $\{x \in \mathbb{R}^n : a \cdot x = t\}$  for some  $a \in \mathbb{R}^n$  and  $t \in \mathbb{R}$ ; hence the hyperplane is defined by (a,t). A halfspace is the set of vector that are on one side of a hyperplane: the halfspace determined by (a,t) for  $a \in \mathbb{R}^n$  and  $t \in \mathbb{R}$  is the set  $\{x : a \cdot x \leq t\}$ . Are halfspaces convex? Yes, observe that if  $a \cdot x \leq t$  and  $a \cdot y \leq t$  then  $a \cdot (\lambda x + (1 - \lambda)y) \leq t$  for any  $0 \leq \lambda \leq 1$ . It is also easy to verify that the intersection of two convex sets is convex. A polyhedron is the intersection of a finite number of half-spaces.

The following theorem plays a key role in polyhedral theory.

Theorem 2 (Minkowski-Weyl). Every convex polytope is a polyhedron.

## **Definitions**

- A full-dimensional polyhedron is one that has an interior point (a point that satisfies all the half-spaces inequalities as strict inequalities rather than as equalities).
- The minimal set of half-spaces needed to describe a full-dimensional polytope are its essential inequalities. A facet is the subset of points of the polyhedron that satisfies an essential inequality as an equality.
- A vertex or extreme point of a polyhedron is any point that is not a convex combination of 2 other points in the set. It is the unique solution of n linearly independent half spaces, i.e., a point that satisfies n linearly independent essential inequalities as equalities.
- A face is a subset (of a polyhedron) of the form  $\{x : x \text{ satisfies some subset of the essential inequalities as equalities}\}$ . The dimension of a face is the dimension of the affine hull of the face. It equals n—(the number of equations satisfied). Thus the dimension of a vertex is 0, of a facet, n-1.

A regular polytope is one in which all vertices have the same degree and every facet has

the same number of edges. We will now prove that there are five regular polytopes (up to symmetry) in three dimensions. The ancient Greeks called them regular solids.

Let  $f_i$  be the number of faces of dimension i of a polytope. Then the following identity was proved by Euler:

$$\sum_{i=0}^{n-1} (-1)^i f_i = 1 - (-1)^n$$

So, for n = 3,  $f_0 - f_1 + f_2 = 2$ . Let us check this for a tetrahedron :

 $f_0 = 4$  (vertices)

 $f_1 = 6 \text{ (edges)}$ 

'  $f_2 = 4$  (facets)

So the relation holds.

Let v be the number of edges at each vertex and e be the number of edges per facet.

- 1. Now  $f_1 = \frac{ef_2}{2}$ , as every edge occurs on 2 facets.
- 2. The number of vertices is  $f_0 = \frac{2e}{v}$ .
- 3. From Euler's formula,  $f_0 f_1 + f_2 = 2$ .

Together these imply that

$$\frac{e}{v}f_2 - \frac{e}{2}f_2 + f_2 = 2$$

It follows that

$$f_2 = \frac{4v}{2e - (e - 2)v}$$

where e > 3 since the polytope is in 3 dimensions.

Consider e = 3. Then

$$f_2 = \frac{4v}{6-v} \Rightarrow 1 \le v \le 5$$

Now  $v \ge 3$  and so v = 3, 4, 5 are the possibilities. In addition,  $f_2$  must be an integer. So we get  $f_2 = 4, 8, 20$  which gives (4, 6, 4), (6, 12, 8) and (12, 30, 20) as the  $(f_0, f_1, f_2)$  descriptions of regular polytopes.

Now consider e = 4. Then  $f_2 = \frac{4v}{8-2v}$  gives (8, 12, 6). No more solutions exist. For e = 5,  $f_2 = \frac{4v}{10-3v}$  has only (20, 30, 12) as a solution. And there are no solutions for  $e \ge 6$ . The unique polytopes corresponding to these descriptions are the only 5 regular polytopes in three dimensions.

---

## 18.433 Combinatorial Optimization

The Matching Polytope: Bipartite Graphs

September 18 Lecturer: Santosh Vempala

A matching M corresponds to a vector  $\chi^M = (0, 0, 1, 1, 0...0)$  of size |E| where  $\chi_e^M$  is 1 if  $e \in M$  and 0 if  $e \notin M$ . Let  $\mathcal{M}$  be the convex hull of all vectors corresponding to matchings.

$$\mathcal{M} = conv\{x = \chi^M \mid M \text{ is a matching}\}\$$

and the resulting relaxation of the integral constraints:

$$P = \{x \mid x_e \ge 0 \quad \forall e \in E, \sum_{e \in \delta(v)} x_e \le 1 \ \forall v \in V\}$$

We now claim that  $\mathcal{M} \subseteq P$ . Note that  $\mathcal{M}$  is convex. Clearly P is also convex (since the constraints are linear). Now  $\mathcal{M} = conv(x_1 \dots x_N)$  where  $x_1 \dots x_N \in P$ . Since P is convex,  $conv(x_1 \dots x_N) \subseteq P$ .

When is  $\mathcal{M} = P$ ? It's not true in general.

All vertices of  $\mathcal{M}$  are 0-1 points. If the vertices of P were integral, then they must be either 0 or 1. But then they must be a matching. So when are the vertices of P integral? They're the solutions to n independent equations and also the points that can't be expressed as a convex combination of two other points.

**Theorem 1.** If G is bipartite, then  $P = \mathcal{M}$ .

**Proof I.** Suppose this isn't the case. Then P has a vertex that is not integral (implied by  $P \neq \mathcal{M}$ ). So take a non-integral vertex x with the fewest non-integral elements. Let  $G_x = (V, E_x)$ , the graph with only fractional valued edges. Suppose there is a cycle. It must be an even length cycle because the graph is bipartite. Let  $\epsilon$  to be min(a, 1 - b) where a (b) is the minimum (maximum) value of edges in the cycle. Add  $\epsilon$  to alternating edges in the cycle and subtract  $\epsilon$  from the other (also alternating) edges to get  $x' = x + \epsilon z$  where  $z = (1, -1, 1, -1 \dots 1, -1)$  along edges in the cycle (zero on other edges). So x' still satisfies the constraints in P and hence  $x' \in P$ . Now let  $x'' = x - \epsilon z$ . Note that  $x'' \in P$  and  $x = \frac{1}{2}(x' + x'')$ . Why is x not a vertex? x is a convex combination of two other points in P, so it can't be a vertex. If there are no cycles, then we can apply the same idea along some path. Hence the vertices of P are integral and the theorem follows.

We note that the fact that G is bipartite prevents odd cycles; the trick in Theorem 1 cannot be done on an odd cycle since the vertex constraint for one of the vertices on the cycle may become violated for x' or x''.

Next we give an alternative proof of Theorem 1 based on a different concept of what a vertex of a polytope is.

**Proof II.** We will prove that if G is bipartite, then the vertices of P are integral. For the purpose of this proof, we will consider a vertex of a polytope as a solution to n (where n is the dimension of the space) linearly independent hyperplanes (i.e. facets). This implies that it must satisfy n linearly independent inequalities (constraints) as equalities.

We can describe P by using a matrix inequality to represent the given constraint conditions.

$$P = \{x \mid Ax \le b\}$$

If y is a vertex of the polytope defined by the constraint matrix A then there exists a subset of rows  $A_1$  of A, and a corresponding subset  $b_1 \subseteq b$  such that

$$A_1 y = b_1$$

and

$$det(A_1) \neq 0$$

Given such a system, we can easily solve for y using Cramer's rule.

$$y_i = \frac{\det(A_1^{(i)})}{\det(A_1)}$$

where  $A_1^{(i)}$  is the matrix  $A_1$  with the *ith* column replaced by  $b_1$ .

Our question is: when is the vertex integral? One sufficient condition is the following:

**Observation 2.** The vertex solution y is integral if the numerator of the value above is integral and  $det(A_i) = \pm 1$ .

Note that we need this for all  $n \times n$  submatrices  $A_1$  (with  $det(A_1) \neq 0$ ). The first condition holds since A is an integral matrix and b is integral. To show the second condition holds we will make use of the following definition.

**Definition 3.** A matrix is said to be totally unimodular if every square submatrix has a determinant of 0, 1 or -1.

We will show that the constraint matrix (defined below) for the given polytope is indeed totally unimodular, which will give us our desired result.

The first part of the matrix comes from the second constraint set of P:

$$\sum_{e \in \delta(v)} x_e \le 1$$

This simply gives us the vertex-edge adjacency matrix of the graph G,  $A_{adj}$ .  $A_{adj}$  has |V| rows and |E| columns, with each element being defined as follows:

$$a_{ve} = \begin{cases} 0 & \text{if } e \notin \delta(v) \\ 1 & \text{if } e \in \delta(v) \end{cases}$$

 $(\delta(v))$  is the set of neighbors of v)

We also wish to put the first set of constraints,  $x_e \geq 0 \quad \forall e \in E$ , into the form  $A\mathbf{x} \leq b$ . This we achieve by the use of the negative of the identity matrix.

Therefore, our constraint matrix, A, consists of two parts:

- 1. The  $|V| \times |E|$  adjacency matrix on top.
- 2. The negative of the  $|E| \times |E|$  identity matrix on the bottom.

**Lemma 4.** If G is bipartite, then the constraint matrix is totally unimodular.

**Proof.** Take any  $k \times k$  submatrix Q of A. We will prove the result by induction on k.

For k = 1, this is true because each element of A is 0 or  $\pm 1$  by construction.

Now assume the lemma true for all  $(k-1) \times (k-1)$  size submatrices.

Consider a matrix Q of size  $k \times k$ .

- 1. If any row in Q is all zero, then |Q| = 0 and we are done.
- 2. If any row in Q has only a single non-zero element that is  $\pm 1$ , then we can expand around that 1 or -1 and use our induction hypothesis on the  $(k-1) \times (k-1)$  size submatrix to deduce that |Q| = 0 or  $\pm 1$ , and we are done.
- 3. If we then assume that every row in Q has more than one non-zero element, then Q must come entirely from the upper half of the constraint matrix,  $A_{adj}$ , since the lower half is the identity matrix. But if this is the case, then the bipartiteness of G

implies that we can partition the rows of Q into two sections corresponding to the partitioning of the vertices of G. However, if we sum the rows of each section, we will get the same vectors, because each edge from E touches exactly one vertex from each section and hence each column has a 1 in each section. This implies that Q is a dependent system and hence |Q| = 0.

We have shown that A is totally unimodular, which proves our lemma, and thus shows that the vertices of P are indeed integral, which proves that  $P = \mathcal{M}$ .

A similar theorem holds for the perfect matching polytope  $\mathcal{PM}(G)$ , the convex hull of perfect matching of G. The only change we need to make to P is to replace the inequality at each vertex by an equality, i.e. the sum of the edges at each vertex is 1.

What about for non-bipartite graphs? Clearly the same constraints do not apply, because we can have a triangle with edge weights of  $\frac{1}{2}$  on each side. In such a situation,  $P(G) \neq \mathcal{M}(G)$  because there exist no perfect matchings of G, while the point  $(\frac{1}{2}, \frac{1}{2}, \frac{1}{2}) \in P(G)$ .

---

## 18.433 Combinatorial Optimization

The Matching Polytope: General graphs

September 23 Lecturer: Santosh Vempala

A matching M corresponds to a vector  $x^M = (0, 0, 1, 1, 0...0)$  where  $x_e^M$  is 1 iff  $e \in M$  and 0 if  $e \notin M$ . Let  $\mathcal{M}$  be the convex hull of all vectors corresponding to matchings.

$$\mathcal{M} = conv\{x = \chi^M \mid M \text{ is a matching}\}\$$

and the resulting relaxation of the integral constraints:

$$P = \{x \mid x_e \ge 0 \quad \forall e \in E, \sum_{e \in \delta(v)} x_e \le 1 \ \forall v \in V\}$$

In the last lecture we saw that  $\mathcal{M}(G) = P$  for any bipartite graph G. Also to describe the perfect matching polytope,  $\mathcal{PM}(G)$ , we just modified P by replacing the inequalities at each vertex by equalities.

What about for non-bipartite graphs? Clearly the same constraints do not apply, because we can have a triangle with edge weights of  $\frac{1}{2}$  on each side. In such a situation,  $P(G) \neq M(G)$  because there exist no perfect matchings of G, while the point  $(\frac{1}{2}, \frac{1}{2}, \frac{1}{2}) \in P(G)$ .

In addition to the already mentioned constraints,

Constraint 1: 
$$x_e \ge 0 \quad \forall e \in E$$
  
Constraint 2:  $\sum_{e \in \delta(v)} x_e = 1 \quad \forall v \in V$ 

we require an additional constraint in the case of general graphs. This constraint is described below.

Constraint 3': Given a subgraph,  $S \subseteq V$ , of G such that |S| is odd, then the number of edges within S that we can add to the matching is limited to:

$$\sum_{e \in S} x_e \le \frac{|S| - 1}{2}$$

Now, there is a simpler way to state this third constraint set, which takes into account the fact that, for a perfect matching to exist, then G must have an even number of vertices. If

we assume that |V| is even, then by dividing G into S and  $\overline{S}$ , we obtain:

$$\sum_{e \in S} x_e \le \frac{|S| - 1}{2}$$

$$\sum_{e \in \overline{S}} x_e \le \frac{|\overline{S}| - 1}{2}$$

Here we note that both S and  $\overline{S}$  have an odd number of vertices.

$$\Rightarrow \sum_{e \in S, e \in \overline{S}} x_e \le \frac{|S| + |\overline{S}|}{2} - 1$$

Since we are considering only perfect matchings, it follows that

$$\sum_{e \in E} x_e = \frac{|V|}{2}$$

hence we obtain the following inequality, which for perfect matchings is equivalent to constraint 3'.

Constraint 3: 
$$\sum_{e \in (S,\overline{S})} x_e \ge 1$$
 for any  $S$  of size odd.

This next theorem of Edmonds states that these three conditions determine the perfect matching polytope of any graph.

**Theorem 1.** (Edmonds)

$$P = \{x \mid x \text{ satisfies Constraints 1, 2, and 3}\} = PM(G)$$

**Proof.** It is fairly easy to show that  $PM(G) \subseteq P$  because the constraints of P are satisfied by any perfect matching.

We will show that  $P \subseteq PM(G)$  through contradiction.

Suppose that  $P \not\subseteq PM(G)$ . Let G be the smallest counterexample (by smallest, we mean the fewest number of edges). The fact that this is a counterexample implies that P has an x such that  $x \not\in PM(G)$ . We will make a series of deductions from the assumptions that i) G is the smallest counterexample, and ii)  $x \not\in PM(G)$ .

1. 
$$0 < x_e < 1 \quad \forall e \in E$$

Suppose that for some e,  $x_e = 0$ , then we can delete the edge and obtain a smaller counterexample, G - e. But this is impossible, because we assumed G was the smallest

counterexample. Also, if for some e,  $x_e = 1$ , then it must be disconnected from the graph (each vertex incident to the edge has no other neighbors by our second constraint condition). But if that is the case, then we can delete the endpoints of e and still have a counterexample, which again is a contradiction.

- 2. G has no isolated vertices (see Constraint 3).
- 3. G has no vertices of degree 1.

If there was a vertex of degree 1, then the edge attached to that vertex would have weight 1, and we already showed in the first observation that it was impossible for  $x_e = 1$ . Hence each vertex has degree at least two.

4. There exists at least one vertex of degree strictly greater than 2.

Suppose otherwise. If every vertex has degree 2, then we have some disjoint collection of cycles. For such a graph, it is easy to show that P = PM(G).

5. |E| > |V|.

This follows because:

$$2|E| = \sum_{v} \deg(v) > 2|V| \Rightarrow |E| > |V|$$

Note that P and PM(G) are in m = |E|-dimensional space. So a vertex of P has to be the unique solution of for m independent constraints. So the vertex x must be the solution of m equalities. These m equalities must come from our base set of constraints:

$$\begin{array}{rcl} x_e & \geq & 0 & \forall \, e \in E \\ \displaystyle \sum_{e \in \delta(v)} x_e & = & 1 & \forall \, v \in V \\ \displaystyle \sum_{e \in \delta(S)} x_e & \geq & 1 & \forall \, S \subseteq V, \, |S| \text{ is odd} \end{array}$$

Looking at the three constraints, we see that we get 0 equalities from the first constraint, and n = |V| from the second constraint. Since m > n, we must therefore get at least one constraint of the third type.

$$\Rightarrow \exists W, \sum_{e \in \delta(W)} x_e = 1, \quad |W| \text{ odd and } \geq 3$$

Look at the cut  $(W, \overline{W})$ . The sum of the edges weights of the cut is 1. Form a new graph by contracting  $\overline{W}$  to a single vertex, u. Call the resulting graph G'. The edge variables are then redefined as follows

$$x'_e = \begin{cases} x_e & \text{if } e \in E(W) \\ x_{wu} = \sum_{v \in \overline{W}} x_{wv} & \text{if } wv \in (W, \overline{W}) \end{cases}$$

That is,  $x_e$  stays the same for edges not crossing the cut, and all  $x_e$ 's are summed together for edges crossing the cut and coming from the same point in W.

We can easily check that the vector x' satisfies the three constraint conditions for G'. So if M' refer to matchings in G', with incidence vectors  $\chi^{M'}$  then

$$x' \in PM(G')$$

$$\Rightarrow x' = \sum_{M'} \lambda_{M'} \chi^{M'}$$

This is a convex combination, so  $\lambda_{M'} \geq 0$  and  $\sum_{M'} \lambda_{M'} = 1$ .

If we follow the same procedure as above, except contracting W rather than  $\overline{W}$  to get G'', then we will get an  $x'' \in PM(G'')$ . It follows that

$$x'' = \sum_{M''} \alpha_{M''} \chi^{M''}$$

Using these decompositions of x' and x'', we can give an intuitive description of how to construct a decomposition of x into a convex composition of perfect matchings of the original graph (thus contradicting our initial assumption concerning G).

The basic idea is to use the fact Kx' and Kx'', for some large interger K, can be viewed as the sum of K incidence vectors from their respective matchings, M' and M''. Then, by finding the corresponding matchings in G, we can combine them to give perfect matchings in G. We can then use this to show that x is a convex combination of perfect matching vectors in G.

First we have that

$$\Rightarrow x' = \sum_{M'} \lambda_{M'} \chi^{M'} \tag{1}$$

$$\Rightarrow x'' = \sum_{M''} \alpha_{M''} \chi^{M''} \tag{2}$$

We will show that (1) and (2) together imply that x is a convex combination of perfect matchings.

For every perfect matching of M, we can associate perfect matchings M' and M'' in G' and G'' induced by M. We will use their coefficients in x' and x'' to define the coefficient of M.

We will show that x is a convex combination by simply finding one and showing that it is indeed a convex combination. Let

$$M = M' \cup M''$$
 have weight  $= \left(\frac{\lambda_{M'} \alpha_{M''}}{x_e}\right)$ 

With this set of convex multipliers, x will be a convex combination. Take  $e \in M' \cap M''$  then

$$x_e = \sum_{M': e \in M'} \lambda_{M'} = \sum_{M'': e \in M''} \alpha_{M''}$$

The following claim will give the result.

## Claim 2.

$$x = \sum_{e \in (W,\overline{W})} \sum_{M: e \in M} \left( \frac{\lambda_{M'} \alpha_{M''}}{x_e} \right) \chi^M$$

**Proof of Claim.** Consider an edge f. Assume first that  $f \in E(W)$ . Then

$$x_{f} = \sum_{e \in (W,\overline{W})} \frac{1}{x_{e}} \sum_{M: e \in M} \lambda_{M'} \alpha_{M''} \chi_{f}^{M}$$

$$= \sum_{e \in \delta(W)} \frac{1}{x_{e}} \sum_{M: e, f \in M} \lambda_{M'} \left( \sum_{M'': e \in M''} \alpha_{M''} \right)$$

$$= \sum_{e \in \delta(W)} \sum_{M': e, f \in M'} \lambda_{M'}$$

$$= \sum_{M': f \in M'} \lambda_{M'}$$

$$= x_{f}$$

Similarly arguments may be applied if  $f \in E(\overline{W})$  or if  $f \in (W, \overline{W})$ .

We have now shown x is a convex combination of perfect matchings, which means that it itself must be a perfect matching. But this contradicts our earlier assumption that  $x \notin PM(G)$ . Hence, we arrive at a contradiction from our original assumption that  $P \nsubseteq PM(G)$ , which means that  $P \subseteq PM(G)$  proving the theorem.

---

## 18.433 Combinatorial Optimization

## Minimum Cuts

October 2 Lecturer: Santosh Vempala

Finding minimum cuts in graphs is an interesting problem and has many applications in some areas such as network design. This problem has two variants: (1) finding a minimum set of edges whose removal disconnects a particular vertex s from a particular vertex t (we call this version the minimum s-t cut problem), (2) finding a minimum set of edges whose removal disconnects the graph (we call this version the minimum cut problem). Both versions apply to directed or undirected graphs.

The minimum s-t cut problem for directed graphs can be solved by using the Max flow-Min cut theorem which says the maximum flow in the graph is equal to the minimum cut in the graph. In fact, a minimum cut  $(S, \overline{S})$  can be obtained by choosing those vertices of G to which there exist directed paths from s in the residual graph as S and the rest of the vertices as  $\overline{S}$ . We can also solve the minimum s-t cut problem in undirected graphs using the algorithm for directed ones (the solution is left as an exercise).

One naive way to solve the minimum cut problem is to choose every pair of vertices as s and t and then use the algorithm for the minimum s-t cut problem. The running time of this algorithm is  $\binom{n}{2}$  times of that of the maximum flow algorithm. We can reduce the factor  $\binom{n}{2}$  to n-1 by considering the fact that each minimum cut separates a fixed vertex s from at least one other vertex t (we have n-1 ways to choose t).

Below, we give a randomized approach for finding a minimum cut in undirected graphs. We also analyze the running time of the algorithm carefully.

## Randomized minimum cut algorithm

- 1. While there exist more than two vertices in the graph
  - (a) Pick an edge e at random.
  - (b) Contract e to a single vertex to get a multigraph (we keep multiple edges).
- 2. Report the edges between the two remaining super-vertices as a minimum cut.

One can observe that the running time of contracting an edge is in O(n) and the number of iterations of the main loop is n-2. Thus the overall running time is in  $O(n^2)$ . Later in

this lecture, we use some tricks to reduce the running time from  $O(n^2)$  time to O(m) time (m is the number of edges).

We now compute the chance of reporting a minimum cut. One can see that the number of cuts in a graph is exponential  $(2^n)$  and thus the chance of getting a minimum cut from a random process might be very low, i.e.  $\frac{1}{2^n}$ . However, we show in Lemma 1 that this chance in not small in our case.

**Lemma 1.** Any particular minimum cut will be the output of the algorithm with probability at least  $\frac{1}{\binom{n}{2}} \approx \frac{2}{n^2}$ .

*Proof.* Suppose a minimum cut  $C = (S, \overline{S})$  has c edges. Thus the degree of each vertex in the graph is at least c and the number of edges is at least  $\frac{nc}{2}$ . If the algorithm does not pick any edge from C, then our final cut will be C.

$$Prob(picking \ an \ edge \ from \ C) \le \frac{c}{\frac{nc}{2}} = \frac{2}{n}$$

and thus

$$Prob(not\ picking\ any\ edge\ from\ C) \ge 1 - \frac{2}{n}$$

Using the same reasoning, we can observe that the chance of not picking any edge from C after contracting the first edge is  $1 - \frac{2}{n-1}$  and so on. Therefore

$$Prob(finding\ cut\ C) \ge (1 - \frac{2}{n}) \cdot (1 - \frac{2}{n-1}) \cdots (1 - \frac{2}{3}) = \frac{1}{\binom{n}{2}}.$$

Thus the chance of succeed in our randomized algorithm is at least  $\frac{1}{\binom{n}{2}}$ . We can improve our chance by iterating this algorithm more than one time and choosing the best cut as our final result. We have

$$\begin{aligned} Prob(succeed\ in\ k\ attempts) &= 1 - Prob(fail\ in\ all\ attempts) \\ &= 1 - Prob(F_1)Prob(F_2) \cdots Prob(F_k) \\ &= 1 - Prob(F_1)^k \\ &= 1 - (1 - \frac{1}{\binom{n}{2}})^k \end{aligned}$$

For example, after  $k = \binom{n}{2}$  iterations of the algorithm, we have at least  $1 - \frac{1}{e}$  chance and by  $k = 2\binom{n}{2} \ln n$  iterations, we have at least  $1 - \frac{1}{n^2}$  chance of success.

It is worth mentioning that using Lemma 1, we can obtain the upper bound  $\binom{n}{2}$  for the maximum number of minimum cuts in a graph. In fact, each minimum cut can be obtained uniquely by the above algorithm with probability at least  $\frac{1}{\binom{n}{2}}$  and thus the number of minimum cuts can not be more that the aforementioned upper bound.

As stated earlier, the running time of the algorithm is  $O(n^2)$ . We now improve the running time to O(m). Suppose we pick a random permutation  $e_1, e_2, \dots, e_m$  of all edges and contract each edge in this order that we can until we have two vertices left in the graph. We can observe that this algorithm has the same output as our first algorithm. Now, consider this binary search approach: first contract edges  $e_1, e_2, \dots, e_{\lceil \frac{m}{2} \rceil}$  in O(m). If the number of vertices after contracting is two, then we report the edges between these vertices as a minimum cut, if the number is one we recurse on the first half of edges, otherwise we continue the algorithm for the second half of edges. The running time of this algorithm is in  $O(m \log m)$ . However still there is some room for improvement. If the number of remaining vertices is more than two, the new obtained graph G' has at most  $\lfloor \frac{m}{2} \rfloor$  edges (we contracted the first half of edges before) and if the number of remaining vertices is 1 then we can discard the second half of edges. In both cases, we have at most  $\frac{m}{2}$  edges left. Thus, the second iteration takes time proportional to m/2. Similarly, the third iteration takes time proportional to m/2. Similarly, the third iteration takes time proportional to m/2.

---

## 18.433 Combinatorial Optimization

## Linear Programs

Oct 14 Lecturer: Santosh Vempala

A linear program consists of linear constraints with the goal of maximizing or minimizing a linear objective function subject to the constraints.

Lets look at the max-flow problem:

$$G = (V, E)$$

In this problem the capacities are  $u_{ij}$  and the flows are  $x_{ij}$ . The conditions a flow must satisfy are:

$$0 \le x_{ij} \le u_{ij} \qquad \forall i, j \in E$$
$$\sum_{i} x_{ij} = \sum_{i} x_{ji} \qquad \forall v \in V \setminus \{s, t\}$$

Note that all of our constraints are linear as they are of the form:

$$a_1x_1 + a_2x_2 + \ldots + a_nx_n \stackrel{\geq}{\leq} b$$

We would like to find the maximum of  $\sum_{j} x_{sj} - \sum_{j} x_{js}$ .

Let's look at a minimum cost flow problem. The constraints are:

$$0 \le x_{ij} \le u_{ij},$$

$$\sum_{i} x_{ij} - \sum_{i} x_{ji} = b(i) \quad \forall i \in V.$$

The objective function is:

$$\sum_{i,j\in E} c_{ij} x_{ij}.$$

The goal is to minimize the objective function.

A maximum matching problem would have the following constraints:

$$0 \le x_e \le 1 \qquad \forall e \in E$$

$$\sum_{e:e \text{ meets } v} x_e \le 1 \qquad \forall v \in V$$

$$\sum_{e \in S} x_e \le \frac{|s| - 1}{2} \qquad \forall s \subseteq V, |s| \text{ odd}$$

The general form of a linear program is:

$$x = \begin{pmatrix} x_1 \\ x_2 \\ \vdots \\ x_n \end{pmatrix}, \qquad c = \begin{pmatrix} c_1 \\ c_2 \\ \vdots \\ c_n \end{pmatrix}, \qquad x, c \in \Re$$

$$\operatorname{Max} c^{T} x = \sum_{i=1}^{n} c_{i} x_{i} \quad \text{or} \quad \operatorname{Min} c^{T} x = \operatorname{Max} - c^{T} x$$
$$Ax \leq b, \ x \geq 0 \quad a^{T} x \geq b \iff -a^{T} x \leq -b$$

To solve:

$$\max cxAx < b$$

we can set x = y - z, where  $y, z \ge 0$ .

(Note: 
$$a^T x \ge b \iff -a^T \le b$$
)

We are trying to find an x such that the objective function is maximized. We must ask ourselves if there is a good characterization for the solution. Suppose we are given  $x^*$ . Is  $x^*$  the optimal solution?

If NO: Either  $x^*$  does not satisfy some constraint or give  $x^{**}$  such that

$$c^T x^{**} > c^T x^*.$$

If YES: ?? (We'll come back to this later)

Here is another example: Find the maximum value of  $(4x_1 + x_2 + 5x_3 + 3x_4)$ , call it  $z^*$ , subject to the following constraints:

$$x_1 - x_2 - x_3 + 3x_4 \le 1 \tag{1}$$

$$5x_1 + x_2 + 3x_3 + 8x_4 \leq 55 \tag{2}$$

$$-x_1 + 2x_2 + 3x_3 - 5x_4 \leq 3 \tag{3}$$

$$x_1, x_2, x_3, x_4 > 0$$
 (4)

Let's try to estimate  $z^*$  with a hit and miss method:

$$x = (0, 0, 1, 0)$$
  $z^* \ge 5$   
 $x = (2, 1, 1, \frac{1}{3})$   $z^* \ge 15$ 

The problem with this method is that we don't know when  $z^*$  is a maximum. We need to find an upper bound on the optimum.

Let's try another approach: Equation 2 multiplied by  $\frac{5}{3}$  is

$$\frac{25}{3}x_1 + \frac{5}{3}x_2 + 5x_3 + \frac{40}{3}x_4 \le \frac{275}{3}.$$

Notice that the left side of this equation is term-by-term greater than or equal to the objective function. Therefore,

$$4x_1 + x_2 + 5x_3 + 3x_4 \le \frac{275}{3}.$$

And therefore,

$$z^* \le \frac{275}{3}.$$

An even stricter bound can be obtained by adding Equations 2 and 3. This gives,

$$4x_1 + 3x_2 + 6x_3 + 3x_4 < 58$$
.

Again, this is term-by-term greater than or equal to the objective function, so,

$$z^* < 58$$
.

Let us generalize this approach. Choose  $y_1, y_2, y_3 \ge 0$  to be three multipliers on Equations 1, 2, and 3. Taking the sum we get:

$$(y_1 + 5y_2 - y_3)x_1 + (-y_1 + y_2 + 2y_3)x_2 + (-y_1 + 3y_2 + 3y_3)x_3 + + (3y_1 + 8y_2 - 5y_3)x_4 \ge y_1 + 55y_2 + 3y_3.$$
 (5)

In order for the left hand side of Equation 5 to be an upper bound on the objective function we require:

$$\begin{vmatrix} y_1 + 5y_2 - y_3 \ge 4 \\ -y_1 + y_2 + 2y_3 \ge 1 \\ -y_1 + 3y_2 + 3y_3 \ge 5 \\ 3y_1 + 8y_2 - 5y_3 \ge 3 \\ y_1, y_2, y_3 \ge 0 \end{vmatrix} \Longrightarrow z^* \le y_1 + 55y_2 + 3y_3$$

Therefore, in order to get the best upper bound we should minimize  $(y_1 + 55y_2 + 3y_3)$  according to the above constraints. This constitutes a new linear program.

In general:

$$\max_{Ax \le b} c^{T}x 
Ax \le b 
x_{i} \ge 0 \quad \forall i$$

$$\implies \begin{cases}
\max_{a_{11}x_{1} + a_{12}x_{2} + \dots + a_{1n}x_{n} \le b_{1} \\
a_{21}x_{1} + a_{22}x_{2} + \dots + a_{2n}x_{n} \le b_{2} \\
\vdots \\
a_{m1}x_{1} + a_{m2}x_{2} + \dots + a_{mn}x_{n} \le b_{n}
\end{cases}$$

Again, we would choose multipliers  $y_1, y_2, \ldots, y_m \geq 0$  on the m constraint equations above.

The dual is:

$$\min b_1 x_1 + b_2 x_2 + \dots + b_m y_m$$

$$a_{11} y_1 + a_{21} y_2 + \dots + a_{m1} y_m \ge c_1$$

$$a_{12} y_1 + a_{22} y_2 + \dots + a_{m2} y_m \ge c_2$$

$$\vdots$$

$$a_{1n} y_1 + a_{2n} y_2 + \dots + a_{mn} y_m \ge c_n$$

$$y_i \ge 0 \quad \forall i$$

Summarizing,

$$\begin{array}{ccc}
\max c^T x & \min b^T y \\
Ax \le b & A^T y \ge c \\
\underline{x \ge 0} & \underline{y \ge 0}
\end{array}$$
Primal

(Note: Dual(Dual) = Primal)

Also,

$$\max c^T x \le \min b^T y$$

therefore,

$$c^T x \le (A^T y)^T x = y^T A x \le y^T b = b^T y$$
$$\Rightarrow c^T x \le b^T y.$$

This gives us the Weak Duality Theorem:

$$\max \{c^T x / Ax \le b\} \le \min \{y^T b / A^T y = c, \ y \ge 0\}$$
 (6)

Next week we will prove the *Strong Duality Theorem* which replaces the inequality in Equation 6 with an equality. Using this we will be able to give a short proof of the case when  $x^*$  is optimal (i.e. the YES case mentioned earlier), which means that we have good characterization.

---

### 18.433 Combinatorial Optimization

# The Primal-dual Algorithm

October 28 Lecturer: Santosh Vempala

In this lecture, we introduce the *complementary slackness* conditions and use them to obtain a primal-dual method for solving linear programming.

# 1 Complementary Slackness

As we have seen before, using strong duality, we know that the optimum value for the following two linear programming are equal, i.e. u = w, if they are both feasible.

$$u = \max\{c^T x : Ax \le b, x \ge 0\} \quad (P)$$

$$w = min\{b^T y : A^T y \ge c, y \ge 0\} \quad (D)$$

Using the above result, we can check the optimality of a primal and/or a dual solution.

**Theorem 1.** Suppose x and y are feasible solutions to (P) and (D). Then x and y are optimal if and only if the following conditions are satisfied:

$$\forall i \ (b_i - \sum_j a_{ij} x_j) y_i = 0;$$

$$\forall j \ (\sum_{i} a_{ij} y_i - c_j) x_j = 0.$$

*Proof.* First, we note that since x and y are feasible  $(b_i - \sum_j a_{ij}x_j)y_i \ge 0$  and  $(\sum_i a_{ij}y_i - c_j)x_j \ge 0$ . By summing over i and j, we have:

$$\sum_{i} (b_i - \sum_{j} a_{ij} x_j) y_i \ge 0 \tag{1}$$

$$\sum_{j} \left( \sum_{i} a_{ij} y_i - c_j \right) x_j \ge 0 \tag{2}$$

By adding 1 and 2 and using the strong duality theorem

$$\sum_{i} b_{i} y_{i} - \sum_{i,j} a_{ij} x_{j} y_{i} + \sum_{j,i} a_{ij} y_{i} x_{j} - \sum_{j} c_{j} x_{j} = \sum_{i} b_{i} y_{i} - \sum_{j} c_{j} x_{j} = 0.$$

Therefore, all our inequalities must be equalities and we obtain the desired result.  $\Box$ 

# 2 Primal-dual algorithm

The main implication of Theorem 1 is that if x and y are feasible and satisfy the complementary slackness conditions, then they are optimal. This result leads us to the primal-dual algorithm in which we start with a feasible solution x and y and try to satisfy the conditions more and more.

For the sake of convenience, we consider the primal and dual programs as follows:

$$min\{c^T x : Ax = b, x \ge 0\} \quad (P)$$
$$max\{b^T y : A^T y \le c\} \quad (D)$$

In this form, the complementary slackness conditions that we need to satisfy are reduced to:

$$\forall j \ (c_j - \sum_i a_{ij} y_i) x_j = 0. \tag{3}$$

The steps of the primal-dual algorithm are as follows:

1. Start with a feasible solution y for (D). Obtaining such feasible solution y is easier than solving the linear program in many cases.

Let 
$$J = \{j : \sum_i a_{ij} y_i = c_j\}.$$

Now using 3, we need to obtain a solution x for (P) such that  $\forall j \notin J, x_j = 0$ . So the question is whether there is a feasible solution x with this property.

2. Formulate the restricted primal (RP) as follows:

$$\min \sum_{i=1}^{m} X_{i}$$

$$\forall i \quad \sum_{j \in J} a_{ij} x_{j} + X_{i} = b_{i}$$

$$X_{i}, x_{j} \geq 0$$

$$\forall j \notin J, x_{j} = 0$$

In fact, (RP) formulates the problem of finding feasible solution x with the aforementioned property. Here variables  $X_i$ 's are artificial variables and if  $\min \sum_{i=1}^m X_i$  is equal to zero, then  $x_j$ 's are optimal solutions to (P).

3. If Opt(RP) = 0 then x and y are optimal. Otherwise Opt(RP) > 0 and we write the dual of (RP), namely (DRP), for which we get solution  $\overline{y}$ .

$$\max \sum_{i=1}^{m} b_i y_i$$

$$\forall j \in J \quad \sum_{i} a_{ij} y_i \le 0$$

$$y_i \le 1$$

4. Improve the solution to (D) by setting  $y' = y + \epsilon \overline{y}$ . Here we determine  $\epsilon$  such that y' is feasible and  $\sum_i b_i y_i' > \sum_i b_i y_i$ . For feasibility, we must satisfy the condition  $\forall j \ \sum_i a_{ij} y_i' \leq c_j$ . For  $j \in J$ , we must have  $\sum_i a_{ij} y_i + \epsilon \sum_i a_{ij} \overline{y}_i \leq c_j$ . Since  $\forall j \in J$   $\sum_i a_{ij} \overline{y}_i \leq 0$ ,  $\epsilon$  can be arbitrary positive for  $j \in J$ .

Thus by taking

$$\epsilon = \min_{\{j \notin J \ s.t. \sum_{i} a_{ij} \overline{y}_{i} > 0\}} \frac{c_{j} - \sum_{i} a_{ij} y_{i}}{\sum_{i} a_{ij} \overline{y}_{i}}$$

we obtain our  $\epsilon > 0$  such that y' is feasible.

Also since Opt(DRP) = Opt(RP) > 0 and  $\epsilon > 0$ ,

$$\sum_{i} b_i y_i' = \sum_{i} b_i y_i + \epsilon \sum_{i} b_i \overline{y}_i > \sum_{i} b_i y_i.$$

We note that in the above primal-dual algorithm, solving (DRP) is usually easier than solving (P) or (D). In fact, in this approach, programs (P) and (RP) are temporary programs and we want to solve (D). To this end, we first solve (DRP) and then use the solution to improve y iteratively.

### 2.1 Example

Consider the following formulation of the max-flow problem:

$$\max f$$

$$\sum_{j} x_{sj} - \sum_{j} x_{js} - f \le 0$$

$$f - \sum_{j} x_{jt} + \sum_{j} x_{tj} \le 0$$

$$\forall i \ne s, t \quad \sum_{j} x_{ij} - \sum_{j} x_{ji} \le 0$$

$$x_{ij} \le u_{ij}$$

$$-x_{ij} \le 0$$

It is worth mentioning that in the original max-flow formulation, the first three sets of constraints are equalities. However in our new formulation by summing these three sets of inequalities, we get  $0 \le 0$  and thus these weaker sets of inequalities imply the equalities.

Now, we consider the above formulation as (D). One feasible solution to (D) can be obtained by taking x as a zero vector. Now if we go directly to (DRP) we have:

$$\max f$$

$$\sum_{j} x_{sj} - \sum_{j} x_{js} - f \leq 0$$

$$f - \sum_{j} x_{jt} + \sum_{j} x_{tj} \leq 0$$

$$\forall i \neq s, t \quad \sum_{j} x_{ij} - \sum_{j} x_{ji} \leq 0$$

$$x_{ij} \leq 0 \quad \forall i, j \text{ where } x_{ij} = u_{ij} \text{ in } (D)$$

$$-x_{ij} \leq 0 \quad \forall i, j \text{ where } x_{ij} = 0 \text{ in } (D)$$

$$x_{ij} \leq 1$$

$$f \leq 1$$

We can observe that (DRP) has the following interpretation. Find a path from s to t (with a flow of value 1) that uses only the following arcs in the following ways: saturated arcs in the backward direction; arcs with zero flow in the forward direction; and other arcs in either direction. In other words, we need to find a path in the residual graph. This observation shows that the max-flow algorithm is in fact a primal-dual algorithm.

Finally, we note that primal-dual algorithms do not have polynomial running time guarantees.

---

## 18.433 Combinatorial Optimization

## Separation Oracles

November 6,13 Lecturer: Santosh Vempala

In the last lecture, we presented a polynomial-time algorithm, namely the Ellipsoid algorithm, for solving a linear program. We also saw using binary search how optimization problems and feasibility problems are equivalent.

In the ellipsoid algorithm, we first consider an initial ellipsoid that contains our entire polyhedron P. If z, the center of the ellipsid, belongs to P then we can solve the feasibility problem and we are done. Otherwise we need to find a half-space  $a_k x \leq b_k$  such that P lies inside of the half-space and z lies in the outside. Then we obtain another ellipsoid containing the intersection of our previous ellipsoid and the half-space. We iterate until we find a point inside the polyhedron or claim that there is no such point. Here the volume drops by a factor of  $e^{\frac{-1}{2n+2}}$  in each iteration.

In today's lecture, we will see that the ellipsoid algorithm can be used in a much more general setting. The main thing we need is to be able to answer the question of whether z is in P or not and finding a separating hyperplane in the latter case. A procedure which does this is called a *separation oracle*.

Consider the minimum-cost arborescence problem: given a directed graph G = (V, E), an special vertex  $r \in V$  and a positive cost  $c_{ij}$  for each edge  $(i, j) \in E$ , find a subgraph of minimum cost that contains directed paths from r to all other vertices. The cost of the subgraph is the sum of the costs of its edges. This problem seems very similar to minimum spanning tree.

We solve this problem using linear programming. Let  $K = \text{Convex Hull of } \{x^T \in R^{|E|} : T \text{ is an arborescence}\}$  where  $x_e^T = 1$  if  $e \in T$  and  $x_e^T = 0$  otherwise. Now our problem is  $\min\{c_{ij}x_{ij} : x \in K$ . We can observe that this problem has the same optimal solution as the following problem:

$$\forall S \subseteq V \text{ where } r \in S \sum_{i \in S, j \notin S, (i,j) \in E} x_{ij} \ge 1$$
$$x_{ij} \in \{0,1\}$$

In fact, we can check that the above condition is equivalent to existence of paths from r to each other vertex  $v \in V$ . Furthermore, Edmonds proved that if we relax the last constraint to  $0 \le x_{ij} \le 1$ , then the set of feasible solutions to the linear program above is exactly K.

Now we have a linear program with an exponential number of constraints. However, we can design a separation oracle that runs in polynomial time. Checking  $0 \le x_{ij} \le 1$  can be done easily in polynomial time. We can also test the first set of constraints by calling at most (n-1) times of min-cut procedure. We consider vertex r as the source, each vertex  $s \in V, s \ne r$  as the sink and each  $x_{ij}$  as the capacity of edge (i, j) in the min-cut problem and check whether the minimum cut has capacity less than 1 or not. We can also find a violated constraint, namely a directed cut of value less than 1, if there exists such a cut.

Having the above facts, we can solve the minimum cost arborescence problem using ellipsoid algorithm in polynomial time.

In general, we have the following problem called *convex programming*: given a convex set K, find a point x in K. To solve this problem using ellipsoid algorithm, first we need a bounding ball for K. Then we need a separation oracle and finally find a lower bound on volume K (or the radius of a ball contained in K). It often turns out among these tasks, finding a separation oracle is the most difficult, since the other parts usually can be done very easily. For our previous example, the ball containing all points whose coordinates are between 0 and 1 is our initial ball. We observe that if the radius of our initial ball is R and the radius of our final ball is r, then the volume of the initial ellipsoid is  $f(n)R^n$  and the volume of the final ellipsoid is greater than or equal to  $f(n)r^n$  (f(n) is a function of the dimension). Let i be the number of iterations. We must have

$$f(n)R^n e^{\frac{-i}{2n+2}} \ge f(n)r^n$$

and thus i is in  $O(n^2 \log(R/r))$ . In each iteration, we call the separation oracle once. Let its running time be g(n). Then the overall running time is in  $O(n^2 \log(R/r) \cdot g(n))$ .

We now consider another problem for which the above approach can be applied. The maximum independent set problem is defined as follows: given a graph G = (V, E), find a subset  $S \subseteq V$  of maximum size such that there is no edge between vertices of S. The integer program (IP) for this problem is:

$$\max \sum_{i} x_{i}$$

$$\forall (i, j) \in E \quad x_{i} + x_{j} \leq 1$$

$$x_{ij} \in \{0, 1\}$$

and its relaxed linear program (LP) is:

$$\max \sum_{i} x_{i}$$

$$\forall (i, j) \in E \quad x_{i} + x_{j} \leq 1$$

$$0 \leq x_{ij} \leq 1$$

However Opt(LP)/Opt(IP) can be large, e.g. for a complete graph Opt(LP) = n/2 by setting all  $x_i$ 's equal to 1/2 but Opt(IP) = 1, and thus solving the linear program does not even give a good approximation of the optimum integer solution.

Let us add another set of constraints to the linear program. We can observe that for each odd cycle C, we can choose at most  $\frac{|C|-1}{2}$  vertices in an independent set. Thus our new LP is as follows:

$$\max \sum_{i} x_{i}$$

$$\forall (i, j) \in E \ x_{i} + x_{j} \leq 1$$

$$\forall \text{ odd cycles } C \sum_{i \in C} x_{i} \leq \frac{|C| - 1}{2}$$

$$0 \leq x_{ij} \leq 1$$

We note that after adding this set of constraints, the linear program and the integer program are still different (the counter-example is left for an exercise).

Let us find a separation oracle for these constraints. The first and the third sets can be checked in polynomial time. To test the second set, we define  $y_{ij} = 1 - x_i - x_j$  for each edge  $(i, j) \in E$ . Now we can observe that the second set of constraints is equivalent to saying that for any odd cycle C,  $\sum_{(i,j)\in E(C)} y_{ij} \geq 1$ . So by finding the length of the minimum odd cycle in the graph C, we can give a separation oracle.

We show that a minimum length odd-cycle can be found in polynomial time. To this end, we construct an undirected bipartite graph  $G' = (V' = V_1 \cup V_2, E')$  such that there exist a vertex  $i_1 \in V_1$  and a vertex  $i_2 \in V_2$  corresponding to each vertex  $i \in V$ . For an edge  $(i, j) \in E$ , we add two edges  $(i_1, j_2)$  and  $(j_1, i_2)$  in E'. We see that odd cycles in G correspond to paths from  $i_1$  to  $i_2$  in G' and finding a shortest path from  $i_1$  to  $i_2$  is easy to perform in polynomial time. Thus we have a polynomial-time separation oracle.

---

### 18.433 Combinatorial Optimization

# NP-completeness

November 18 Lecturer: Santosh Vempala

Up to now, we have found many efficient algorithms for problems in Matchings, Flows, Linear Programs, and Convex Programming. All of these are polynomial-time algorithms.

But there are also problems for which we have found no polynomial-time algorithms. The theory of NP-completeness unifies these failures. Roughly speaking, an NP-complete problem is one that is as hard as any problem in a large class of problems. For example, the Traveling Salesman Problem (TSP), Integer Programming (IP), the Longest Cycle, and Satisfiability (SAT) are all hard problems. NP-completeness tells us that they are all, in a precise sense, equally hard. Let's look at each problem in a little more detail.

#### 1. The Traveling Salesman Problem

Let's say that there exist a salesman that has to visit n cities and there exists a distance  $w_{i,j}$  between cities i and j. He wants to make sure to minimize his traveling time by visiting every city exactly once. In other words, there is a complete graph G = (V, E) with lengths  $w_{i,j}$  between nodes i and j. The question we must ask is: What is the shortest cycle that visits every node exactly once?

#### 2. Integer Linear Programming

Suppose that you have a linear program such as the following:

$$\min c^T x$$

$$Ax < b \text{ for } x_i > 0$$

This is your typical linear program. Now, if you decide to add an integrality constraint on  $x_i$  such that it is forced to be a positive integer, then you have an Integer Linear Program (ILP).

### 3. Boolean Satisfiability

The satisfiability problem (SAT) uses boolean expressions such as the following

$$f = (x_1 \lor x_2 \lor x_4) \land (x_3 \lor \bar{x}_4)...$$

with  $x_i = \{\text{True}, \text{False}\}\$ and using well known boolean identities. Does F have a satisfying assignment? Can we find values of  $x_i$  such that every clause in F is equal 1?

4. Longest Cycles

Given a graph G = (V, E), find the longest cycle.

5. Cliques

A clique is a complete subgraph. Given a graph G = (V, E), find a clique of maximum cardinality (vertices).

As different as these examples might seem, they have two main properties in common:

- A) None of them is known to have a polytime algorithm.
- B) If any one of them has a polytime algorithm, then they all do.

# 1 Optimization vs Decision

While property A seems trivial to us all by the inspection of each problem, property B is not as easy to see. To understand this property, we first formulate the *decision* versions of these optimization problems.

Find the optimum among a set of feasible solutions F with cost function c

vs

Is there a feasible solution of  $cost \leq L$ ?

If the Optimal (OPT) is solved, then the Decision (DEC) is also solved. Namely, DEC reduces to OPT. Now, is OPT reducible to DEC? Well, using the TSP as an example, we ask: Is there a  $tour \leq L$ ? Then, we proceed to do a binary search in order to find the length of the shortest tour, say S. But, we still don't know what the tour is. One way to figure this out is to use the following algorithm:

Take out an edge e.

Ask if the same graph still has a  $tour \leq S$ .

If it does, then we don't need that edge and can delete it.

If it doesn't, then we keep that edge because it will be part of our tour.

Repeat this algorithm for all the edges.

In the ILP example, we can ask: Is there an x of cost  $\leq L$ ? Well, one way to do this would be to set  $x_i = 0$  and if optimum stays the same, then we can fix that particular  $x_i$  to 0.

For the maximum cliques problem, the OPT problem would be: Find the largest clique, while the DEC problem would be: Is there a clique of size  $\leq k$ ? To find the optimal size  $k^*$ , again we do a binary search. We then consider the graph with  $v_i$  and all its neighbors. If the optimum in this graph remains the same, then save that vertex, then we can delete all other vertices. Else, delete  $v_i$  because it is not in the max clique.

## 2 P and NP

## 2.1 Definitions

P: Class of decision problems that can be solved in polytime.

NP: Decision problems that have a short proof (certificate) for YES answers. The proof has length bounded by a polynomial in the size of the input, and its correctness can be verified in polytime.

Note that problems in P have short proofs for both YES and NO answers. This means that  $P \subseteq NP$ . Let's look at a problem in P:

Linear Programming: Is the minimum less than some c?

YES: Give a feasible solution  $\leq c$ 

NO: Use the Dual of the problem to give a lower bound.

Now, let's look at the following examples of NP problems:

1. TSP, Is there a  $tour \leq L$ ?

YES: Give a tour

NO: ?

2. SAT, Does there exist a satisfying assignment?

YES: Give a satisfying assignment

NO: ?

3. Min ILP, Is the minimum  $\leq c$ ?

YES: Give a feasible solution that is  $\leq c$ 

NO: ?

This leads to the question: Is P = NP?

### 2.2 Reductions

A reduction from a problem A to a problem B is a function  $f:A\to B$  such that for all instances x

$$x \in A \Leftrightarrow f(x) \in B$$
.

If the function f can be computed in polynomial time, then it is called a polynomial-time reduction. An implication of this is the following:

If there exists a polytime algorithm for B, then there exists one for A.

A problem B is NP-hard if every problem in NP has a polytime reduction to B. If, in addition, B is in NP, then it is NP-complete.

Thus if A is NP-complete, and it has a reduction to another problem B in NP, then B is also NP-complete.

### 2.3 Examples of Reduction

SAT is NP-complete (we will not prove this in class).

1. ILP is NP-complete Let's take the following SAT problem and see if it can be solved by an ILP.

$$F = (x_1 \lor x_2 \lor \dots \lor \bar{x}_i) \land (x_4 \lor \bar{x}_5) \land \dots \land (x_a \lor x_b \lor \dots \lor x_c)$$

This SAT problem can also be written in the following way

$$x_1 + x_2 + \dots + \bar{x}_i \ge 1$$
$$x_4 + \bar{x}_5 \ge 1$$

$$x_a + x_b + \dots + \bar{x}_c \ge 1$$

Figure 1: clique is NP-complete

 $x_i = \begin{cases} 1, & \text{then true} \\ 0, & \text{then false} \end{cases}$ 

Since SAT can be reduced to an ILP, ILP is NP-complete.

### 2. Clique is NP-complete

SAT can be reduced to clique by the following construction. Suppose we have a formula F with m clauses.

- 1) Vertices are going to be of the form  $\langle x_a, i \rangle$  where  $x_a$  is a literal that occurs in clause  $C_i$
- 2) Edges are going to be of the form  $\{\langle x_a, i \rangle, \langle x_b, j \rangle\}$  for all  $x_a \neq \bar{x}_b$  and  $i \neq j$ .

By defining the vertices and edges this way, we ensure that all the connected vertices are compatible, since their truth values won't overlap. If we find a clique of size m in this graph, F is satisfiable. Refer to Fig. 1.

---

### 18.433 Combinatorial Optimization

## Flow Duality and algorithms

Sept 25, 30 Lecturer: Santosh Vempala

## 1 Introduction

A directed graph is a graph in which every edge has a direction. A capacity is the maximum flow allowed on an edge, and is represented by  $c_{i,j}$ , where the edge connects the vertices i and j in the direction from i to j.

Given a directed graph G = (V, E), a flow is a collection of paths from a source  $s \in V$  to a sink  $t \in V$ . The set of edge disjoint paths is the collection of all paths from s to t such that no edge appears in more than one path.

Suppose S is a set of vertices containing s but not containing t. Then  $\bar{S} = V - S$  is the compliment of set S. The size of a cut  $(S, \bar{S})$  is the number of edges from S to  $\bar{S}$ .

**Theorem 1.** (Menger) A graph G=(V,E) has k edge disjoint paths from s to  $t \iff k$  is the size of the minimum directed s-t cut.

### Proof.

- $(\Rightarrow)$  This direction is trivial.
- ( $\Leftarrow$ ) Assume this is false. Take the smallest counter example G. So G has minimum cut size k but does not contain k edge disjoint paths from s to t. Since G is minimal the removal of any edge will induce a graph with a smaller minimum cut. In particular, G contains no edges into the source s or out of the sink t as these arcs are not present in any s-t cut. We can divide our problem into two cases:
- (i)  $\exists e \in E$  that is not incident to s or t. Now, by the minimality of G, e is contained in some minimum cut  $(S, \bar{S})$ . The contraction of the set  $\bar{S}$  gives a graph G' with a minimum cut of at least k. Similarly the contraction of the set S gives a graph G'' with a minimum cut of at least k. Since G was the smallest counterexample, G' has k disjoint paths from s to the contracted vertex  $\bar{S}$  whilst G'' has k disjoint paths from the contracted vertex S to t. These two sets of k edge disjoint paths only coincide on edges within the cut  $(S, \bar{S})$ . Hence they may be merged to form k edge disjoint paths from s to t in G. A contradiction.

- (ii) Every edge is incident to s or t. Arrange the middle vertices (all vertices except s and t) into the following two groups:
  - 1. All vertices who have more edges going in than out, and s.
  - 2. All vertices who have more edges going out than in, and t.

Observe that, by definition, the set of edges that go from the first group to the second group must contain k edges. It then follows easily that we may find a collection of k edge disjoint paths from s to t.  $\square$ 

### 2 The Maximum Flow-Minimum Cut Theorem

The capacity of a cut  $(S, \bar{S})$ , denoted  $c(S, \bar{S})$ , is equal to the sum of the capacities of each edge in the cut whose direction is from S. Let f be a flow from s to t. We will abuse our notation and also denote by f the value of the flow.

**Lemma 2.** Let  $(S, \bar{S})$  be any s-t cut in the graph G. Then  $f \leq c(S, \bar{S})$ .

**Proof.** We know that f(s,V) - f(V,s) = f. We also know that f(x,V) - f(V,x) = 0 for all  $x \in V - \{s,t\}$ . Using this, we can see that f(S,V) - f(V,S) = f. We also know that V is equal to the union of S and  $\bar{S}$ . Thus we have  $f(S,\bar{S}) - f(\bar{S},S) = f$ . In conclusion

$$f = f(S, \bar{S}) - f(\bar{S}, S) \le f(S, \bar{S}) \le c(S, \bar{S}) \quad \Box$$

In a finite graph there is always a maximum possible flow. Finding this maximum value and the flow that attains it can be a very important part of many graph and network problems. Suppose we have a graph G = (V, E), where  $s, t \in V$  are the source and sink, respectively. Take a flow f from s to t. Is it the maximum flow? If we look again at Lemma 2, we can see that the value of the maximum flow is at most the value of the minimum capacity cut. So one way to see if f is maximum is to look for the minimum cut, find it's capacity, and compare the values. A better way is to attempt to find an augmenting path for f. Given our graph, with source s and sink t, an augmenting path for f is a path  $\{u_0, u_1, \ldots, u_r\}$  where:

- 1.  $u_0 = s$ .
- 2. If  $(u_i, u_{i+1})$  is an edge then  $f_{i,i+1} < c_{i,i+1}$ .

3. If  $(u_{i+1}, u_i)$  is an edge then  $f_{i+1,i} > 0$ .

We can see that for each vertex in the path, with the exception of s and t, the net flow must equal 0. If  $u_r = t$ , then our augmenting path is a flow augmenting path or f-augmenting path, and can be used to increase flow value.

This leads us to an algorithm for finding max flow that is very similar to the one we used to find maximum matching in a graph.

```
Algorithm I
{
1) Find an f-augmenting path.
2) Augment the original flow.
3) Repeat.
```

This algorithm leaves us with a few questions. What is the best way to find an augmenting path? Is this process bounded? Is f maximum when an augmenting path does not exist? We will answer these questions is reverse order.

**Theorem 3.** A flow f is maximum  $\iff$  there are no flow augmenting paths.

#### Proof.

}

- $(\Rightarrow)$  Clearly if there is a flow augmenting path then f can not be a maximum flow.
- ( $\Leftarrow$ ) Take the set of vertices  $A_f = \{u \in V : \exists \text{ an augmenting path from } s \text{ to } u.\}$ . Note that  $t \notin A_f$  as we have no flow augmenting path. Consider the cut  $(A_f, \bar{A}_f)$ . Take an edge (i, j), where  $i \in A_f$  and  $j \in \bar{A}_f$ . Note that for this edge  $f_{i,j} = c_{i,j}$  otherwise we could grow  $A_f$ . Similarly  $f_{j,i} = 0$ . This gives us the flow across the cut is  $\sum c_{i,j} 0$ . We can't send anymore than the capacity of the cut, so therefore the flow is maximum if  $t \notin A_f$ .  $\Box$

**Theorem 4.** (Max Flow-Min Cut) The maximum flow is equal to the minimum capacity cut.

**Proof.** Suppose f is the maximum flow value. Therefore the flow f has no augmenting paths. Since it has no augmenting paths, the graph contains a cut, given by  $A_f$ , of capacity f. Since no cut can have a capacity less than f the result follows.  $\square$ .

Figure 1: The initial flow.

## 3 Algorithmic Efficiency

The second question to be answered is whether or not the algorithm for finding an augmenting path is bounded. The answer is, not necessarily. If we look at the Figure 1, finding the wrong set of augmenting paths will lead to an infinite number of augmentation whose augmentation leads to a flow with value less than the maximum flow. The edges have extremely large capacities and the initial flow, of value  $1 + \alpha + \alpha^2$  where  $\alpha$  is the root of  $1 - \alpha - \alpha^3 = 0$ , is shown in Figure 1.

To find an augmenting path in this graph, pick a path that starts at s and proceeds to t. Find the lowest current flow value on this path, counting only the edges whose direction goes against the direction of your path. We do not worry about the edges going in the direction of our path, since the capacities of all edges are extremely large. Augment by this value.

For an example, see Figure 2. We may augment this flow by a value  $\alpha$ . In the subsequent step the situation is similar except that we may find an augmenting path with capacity  $\alpha^2$ . In the next step we may augment along a path of capacity  $\alpha^3$ . Observe that we have an infinite process. In addition, the limit of the value of the flow obtained is bounded  $(1 + \alpha + \alpha^2 + \sum_{r \geq 1} \alpha^r)$  whereas the maximum flow can be any value.

Figure 2: Augmentation by alpha

Figure 3: Residual Graph

# 4 A Weakly Polynomial Algorithm

There are better ways to find an augmenting path than by picking a random flow and trying to augment it. We can try making a residual graph. A residual graph takes each edge and makes it two different edges. Take the edge (i, j), with capacity  $c_{i,j}$  and flow  $f_{i,j}$ . The residual graph  $\operatorname{Res}(G)$  would have two edges between i and j, each with opposite directions. Edge (i, j) has a capacity on it equal to  $c_{i,j} - f_{i,j}$ , while the capacity on edge (j, i) is  $f_{i,j}$ . If either of the capacities is zero the we will omit the edge from  $\operatorname{Res}(G)$ . If there are already two edges of opposite direction connecting the two vertices, then forming the residual graph becomes a little more complicated (see figure 3).

Claim 1. An augmenting path in G corresponds to a directed s - t path in Res(G), and therefore and augmenting path in G corresponds to a directed path from s to t in Res(G).

This leads us to a new algorithm, similar to the one we were using before.

Algorithm II

```
{
1) Find an s - t path in Res(G)
2) Augment the flow.
3) Repeat.
}
```

The problem with this, as with before, is that it depends on picking a good original path to augment. How do we make a good choice of path? A good place to start would be to pick the path with the maximum capacity. This is a bounded search, a proof of this is asked for in the homework.

Claim 2. A flow f can be decomposed into at most m paths from s to t, excluding cycles.

**Proof of Claim.** Every time you create a path, remove the restraining edge in that path from the graph. The restraining edge is that whose flow capacity is filled, and thereby holds you back from sending any more flow down this path. We can easily induce that there can be no more than m paths.  $\square$ 

**Theorem 5.** There is a path P with  $c(P) \ge \frac{f^* - f}{m}$ , where f is the current flow value and  $f^*$  is the optimal flow value.

**Proof.** Take a graph G, and let  $f^*$  be the max flow, and f be the current flow. In Res(G) you should be able to send  $f^* - f$  as your max flow. Therefore there exists a path P in Res(G) where  $c(P) \geq \frac{f^* - f}{m}$ .  $\square$ .

Now let us examine the running time of the algorithm. We can find a maximum capacity path in O(m) time. Consider the set of augmentations, each with a capacity of at least  $\frac{f^*-f}{2m}$ . There are at most 2m such augmentations. After these augmentations, the remaining flow is at most  $\frac{f^*-f}{2}$ , since after the augmentations the current maximum capacity path has capacity below  $\frac{f^*-f}{2m}$ . We can see that the flow remaining halves at most every 2m steps, and from this get that the total number of augmentations is at most  $2m \log(nU)$ . We then have a weakly polynomial running time of  $O(m^2 \log(nU))$ .

# 5 A Strongly Polynomial Algorithm

Another way to pick which path to start with when looking for an augmenting path is to look for the shortest augmenting path. Start at the source, and look at everything you can get to in one step. That is to say, every vertex that is only one edge away. We will call

these depth 1. Now find depths  $2, 3, \ldots$  in similar fashion. Find the lowest depth to touch the sink, and send on it as much as you can send. Now take d(i) to be the level of depth of node i. Note that on an edge (i, j) in shortest path from s to t we have d(j) = d(i) + 1. The following observation is left as an exercise.

**Observation.** The shortest path lengths are non-decreasing in the course of this algorithm.

**Lemma 6.** The total number of times an edge can be the minimum capacity edge is O(n).

**Proof.** Suppose the edge (i, j) with capacity  $\beta$  is the minimum capacity edge along the augmenting path. Augment by  $\beta$ . Now Res(G) no longer contains the edge (i, j). Before the augmentation, at time  $\tau$  say, we had d(j) = d(i) + 1 since we used a shortest path. Now, the next time this edge is used the edge (i, j) must again be in Res(G). For this to be the case we must, in the meantime have augmented along some path containing the edge (j, i). At this point, say at time  $\tau'$ , we have d'(i) = d'(j) + 1. Hence  $d'(i) \geq d(i) + 2$ . The maximum value of d(i) is n and the theorem follows. Observe also that the total increase of d(i)'s over all vertices is less than  $n^2$ , and therefore the total number of augmentations is  $O(n^2)$ .  $\square$ 

Since it takes O(m) time to find a shortest path the running time of this algorithm is  $O(mn^2)$ , a strongly polynomial bound.

---

## 18.433 Combinatorial Optimization

## Matching Algorithms

September 4,9,11 Lecturer: Santosh Vempala

Given a graph G = (V, E), a matching M is a set of edges with the property that no two of the edges have an endpoint in common. We say that a vertex  $v \in V$  is matched if v is incident to an edge in the matching. Otherwise the vertex is unmatched. A matching is maximum if there is no matching of greater cardinality. In particular, a maximum matching is called perfect if every vertex of G is matched.

A bipartite graph G is a graph in which the vertices of G can be partitioned in two sets A and B with the property that every edge in G has one endpoint in A and one in B. In the case of bipartite graphs, the following theorem characterizes graphs that have a perfect matching. For  $U \subseteq A$  denote N(U) the set of vertices that are adjacent to vertices in U.

**Theorem 1 (Hall).** A bipartite graph with sets of vertices A, B has a perfect matching iff |A| = |B| and  $(\forall U \subseteq A)|N(U)| \ge |U|$ .

*Proof.* If a bipartite graph has a perfect matching, then it is easy to see that the right hand side is a necessary condition.

If the right hand side is true for a bipartite graph, then we will prove by induction on |A| that the graph has a perfect matching. If |A| is 0 or 1, the claim is true. Now consider 2 cases:

1. Suppose that  $(\forall U \subseteq A, U \neq \emptyset, U \neq A)|N(U)| > |U|$ . Consider e = (u, v) and  $G' = G - \{u\} - \{v\}$ . In G',  $\forall U \subseteq A - \{u\}$ 

$$|N_{G'}(U)| > |N(U)| - 1 > |U|.$$

So G' has a matching M of  $A - \{u\}$  into  $B - \{v\}$ .  $M \cup \{e\}$  gives us a matching of A into B in G.

2. Now suppose the opposite to the previous case: there exists  $A' \subset A$  nonempty such that |N(A')| = |A'|. Let  $G_1$  be the graph induced by  $A' \cup N(A')$ . Let  $G_2$  be the graph induced by G - A' - N(A').

In  $G_1$ ,  $(\forall U \subseteq A')N_G(U) = N_{G_1}(X)$ , and  $|N_{G_1}(U)| \ge |U|$ . Thus,  $G_1$  has a matching  $M_1$  of A' into N(A').

In  $G_2$ ,  $\forall U \subseteq A - A'$  we have

$$N_G(U \uplus A') = N_{G_2}(U) \uplus N_G(A').$$

That is,

$$|N_{G_2}(U)| = |N_G(U \uplus A'| - |N_G(A')|$$

$$\geq |U \uplus A'| - |A'|$$

$$= |U|.$$

Thus,  $G_2$  has matching  $M_2$  of A - A' into B - N(A'). Moreover,  $M_1 \cup M_2$  is a perfect matching of G.

Our goal in these lectures is to develop a fast algorithm for finding a matching of maximum cardinality in a given graph. Throughout this course, by "fast" we mean polynomial-time, i.e. the running time of the algorithm should be bounded by a fixed polynomial in the size of the input graph. The size of a graph is determined by number of vertices in the graph, denoted by n, and by the number of edges, denoted by m.

Now take a matching M with respect to the graph G. If every vertex of G is matched by M then M is a perfect matching and hence is a maximum matching of cardinality  $\frac{n}{2}$ . Should M not be perfect, then we would like to either find another matching of greater cardinality than M, i.e.  $augment\ M$ , or conclude that M is already maximum. One way to augment M is the following: find a path P in the graph that starts at an unmatched vertex and consists alternately of edges not in M and edges in M (i.e. unmatched edges and matched edges) and ends at an unmatched vertex. Then consider the set of edges M' obtained by deleting the edges M has in common with the path and adding the rest of the edges on the path, i.e. the symmetric difference of M and P, denoted by  $M \oplus P$ . It is easy to verify that M' is also a matching, and moreover it has one more edge than M. Such an alternating path P is called an augmenting path. This observation motivates the following "algorithm".

```
THE MATCHING ALGORITHM

{
    1. Start with any matching.
    2. Find an augmenting path with respect to the current matching.
    3. Augment the current matching.
    4. Repeat the above two steps as long as possible.
}
```

When the algorithm terminates, we have a matching M with no augmenting paths. What do we do now? Our first lemma tells us that at this point M must be maximum.

**Lemma 2.** A matching M is maximum iff it has no augmenting paths.

**Proof.** We have seen that if M contains an augmenting path then it is not a maximum matching.

So consider the converse. Assume that M does not contain an augmenting path. We will show that M is a maximum matching. In order to prove this we take some maximum matching  $M^*$  and show that  $|M| = |M^*|$ . Consider  $M \oplus M^*$ , the symmetric difference of M and  $M^*$ . Recall that this is the collection of edges that are in M but not  $M^*$  and vice versa, i.e.  $M \oplus M^* = (M - M^*) \cup (M^* - M)$ . Since M and  $M^*$  both induce subgraphs of maximum degree one, it follows that  $M \oplus M^*$  induces a subgraph of maximum degree two. Note that such a subgraph may consist only of disjoint paths and/or cycles. In addition, observe that since M and  $M^*$  are matchings these paths and cycles contain edges that are alternately in M and  $M^*$ .

Consider first the cycles in our induced graph. All such cycles must contain an even number of edges, otherwise there must be some vertex that is adjacent to two edges in either M or  $M^*$ , contradicting the definition of a matching. Thus, these cycles contain an equal number of edges from M and  $M^*$ .

Consider now the induced paths. Suppose we have a path P that contains an odd number of edges. Hence, either P contains one more edge from M than  $M^*$  or one more edge from  $M^*$  than M. In the former case note that P is then an augmenting path in G with respect to  $M^*$ , contradicting the maximality of  $M^*$ . In the latter case P is then an augmenting path in G with respect to M, contradicting our initial assumption. Hence all our induced paths contain an even number of edges and thus contain an equal number of edges from M and  $M^*$ .

So the paths and cycles induced by  $M \oplus M^*$  contain an equal number of edges from M and  $M^*$ . Finally consider the edges that are not induced by  $M \oplus M^*$ . These edges are either in both M and  $M^*$  or in neither of them. It follows that M and  $M^*$  are of equal cardinality and hence M is a maximum matching.

How long does our algorithm take? In each iteration of steps 2 and 3 we increase the size of the matching by one. Thus we can repeat steps 2 and 3 at most  $\frac{n}{2}$  times. So we are left with the question of how long it takes to find an augmenting path. Actually, first we must figure out *how* to find an augmenting path. It turns out that this will be much easier to do for *bipartite* graphs, which we will consider first.

## 1 Bipartite graphs

Take a bipartite graph, with a matching M, and let  $A^U \subseteq A$  and  $B^U \subseteq B$  be the vertices unmatched by M. We wish to find an augmenting path with respect to M. To do this, we will find the set of vertices S accessible from  $A^U$  by alternating paths. If S includes a vertex of  $B^U$  then the alternating path to that vertex will be an augmenting path.

The set S is determined by building an alternating forest F as follows:

- 1. Start with all the vertices of  $A^U$  as separate components of F.
- 2. Add edges from vertices of  $A \cap V(F)$  to vertices of B without merging any two connected components of F. That is, if a vertex of B is adjacent to more than one component, add it to only one of the components.
- 3. Then add the edges of M incident to vertices of  $B \cap V(F)$ .
- 4. Repeat the above two steps till no more edges can added to F.

If we find a vertex of  $B^U$  in the forest, then this gives us an augmenting path. If not, by the next lemma, the matching M is a maximum matching.

**Lemma 3.** M is maximum iff no vertex of  $B^U$  is in F.

**Proof.** If F includes a vertex v of  $B^U$  then the path from v to the vertex of  $A^U$  in the component containing v is an alternating path with unmatched vertices at its ends, i.e. an augmenting path. Hence M is not maximum.

Conversely, suppose that no vertex of  $B^U$  is included in F. In order to prove our result we introduce the notion of a a vertex cover. This is a set of vertices such that every edge is incident to at least one vertex in the set We will show that G has a vertex cover of size equal to the current matching. Since the size of any vertex cover, is at least the size of the maximum matching (one endpoint from each edge in the matching must be chosen in any vertex cover) this would prove that the matching M is maximum.

Let X = A - V(F) and  $Y = B \cap V(F)$ . Then we claim that  $X \cup Y$  is a vertex cover. Clearly, M meets every vertex of  $X \cup Y$ . Since M is a matching, no edge of M is incident to two vertices of  $X \cup Y$ . Now, given a matched vertex  $a \in V(F)$ , let (a, b) be the matching edge. From the description of F it follows that b must also be in V(F). As a result, every edge of M meets at least one vertex of  $X \cup Y$  and so  $|M| = |X \cup Y|$ .

All that is left to show is that  $X \cup Y$  is a cover of the graph. Suppose not. Then there is an edge (a,b) with  $a \in A$  and  $b \in B$  that is not covered. Hence we have  $a \in V(F)$  and  $b \notin V(F)$ . It follows that (a,b) is not a matching edge. In addition,  $b \notin B^U$  otherwise it would have been added to V(F). So b is matched, say by the edge (a',b), where  $a' \neq a$ . But this implies that F can be extended by adding the path aba' contradicting the assumption that F is maximal.

From the proof of the lemma we may derive the following theorem.

**Theorem 4.** (König) The size of a maximum matching in a bipartite graph is equal to the size of a minimum vertex cover of the graph.

We say that A has a matching into B if the maximum matching is of size |A|. In addition, denote by  $\Gamma(X)$  is the set of neighbors of  $X \subseteq V$ . The classical theorem of Frobenius and Hall then follows from König's theorem (and is actually equivalent to it).

**Theorem 5.** (Frobenius-Hall) A has a matching into B iff for every subset X of A,  $X \leq |\Gamma(X)|$ .

**Proof.** Clearly if there is a subset X of A such that  $X > |\Gamma(X)|$ , then there can be no matching of cardinality |A|. Conversely, assume that  $X \leq |\Gamma(X)|$  for all  $X \subseteq A$ . We will show that the minimum vertex cover is of cardinality |A|, from which the theorem will follow. We may assume that each vertex is incident to at least one edge and that  $|A| \leq |B|$ . Note that the vertices of A form a vertex cover of cardinality |A|. Suppose we have a vertex cover  $X \cup Y$ , where  $X \subseteq A$  and  $Y \subseteq B$ . Observe that  $\Gamma(A - X) \subseteq Y$ . Thus  $|A - X| \leq |\Gamma(A - X)| \leq |Y|$  and hence  $|X \cup Y| \geq |A|$  as desired.

**Theorem 6.** A maximum matching can be found in a bipartite graph in  $O(m\sqrt{n})$  time.

**Proof.** It is easy to see that the time spent in finding an augmenting path is O(m) and the total number of augmentations is at most  $\frac{n}{2}$ . So the total time is O(mn). To improve upon this analysis observe that the algorithm for finding augmenting paths might find more than one path. In this case let us augment on a maximal set of disjoint augmenting paths. With this modification we can show that the number of phases (where a phase is the construction of the alternating forest) is  $O(\sqrt{n})$ . The key observation, which is left as an exercise, is the following:

**Observation 7.** The length of the shortest augmenting path increases in each phase.

Given this observation, then after  $\sqrt{n}$  phases, the augmenting paths all have length at least  $2\sqrt{n}+1$ . Now consider an optimal matching  $M^*$  and the symmetric difference of M and  $M^*$ . If M is not maximum then there must be some alternating paths in the symmetric difference that are augmenting paths with respect to M. Since each of these has length at least  $2\sqrt{n}+1$  there can only be  $O(\sqrt{n})$  such paths in all (the total number of vertices is n). Thus  $|M^*|-|M|<\sqrt{n}$  and hence the algorithm will terminate in at most  $\sqrt{n}$  more phases.

## 2 General graphs

It is not hard to see that the algorithm from the previous section does not apply to general graphs. The main problem is caused by odd cycles with a maximal number of matching edges, i.e. cycles of length 2k + 1 which contain k matching edges. Such cycles are called blossoms, an example of which is shown in Figure 1, where the matching edges are shown in bold.

Figure 1: A Blossom.

The next lemma that shows us a way to deal with blossoms is the central idea in Edmonds' algorithm for finding a maximum matching in general graphs.

**Lemma 8.** (Cycle Shrinking) Let M be a matching of G and B be a blossom. Further, assume that B is vertex-disjoint from (i.e. has no vertices in common with) the rest of M. Consider the graph G' obtained by contracting B to a single vertex. Then the matching M' of G' induced by M is maximum in G' iff M is maximum in G.

**Proof.** First suppose that M' is not maximum in G'. From Lemma 2 it follows that G' contains an augmenting path P' with respect to M'. Suppose that P' does not intersect the blossom B in G, then P' is also an augmenting path in G and hence M is not maximum. So P' intersects B in G. In particular, the contracted blossom B must be an end vertex of the path P' in G' since B is vertex-disjoint from M'. Let P' meet B at the vertex v, and let v be the unmatched vertex in the blossom. Let v be the path from v to v in the blossom that begins with the matching edge incident to v. It is easy to see that v is then an augmenting path in v and so, again, v is not a maximum matching.

Now assume that M is not a maximum matching in G. We will show that M' is not a maximum matching in G'. So take an augmenting path P in G. We may assume that P intersects the blossom B, otherwise P is an augmenting path in G'. Note that since B contains only one unmatched vertex, it follows that at least one of the endpoints of P, say w, lies outside B. Let P' be the path created by starting at w and following P until it intersects the blossom. Observe that P' is an augmenting path in G' and the result follows.

To find an augmenting path in a general graph, we will modify the procedure for bipartite graphs, so that it also detects blossoms. If it does, we shrink the blossom and restart on the new graph. Any augmenting path found on the new graph can be easily translated to an augmenting path in the original graph. Further, by the previous lemma, if the matching is maximum in the new graph, then it is also maximum in the original graph.

Here is a formal description of the algorithm. Let M be a matching of G and let U be the subset of unmatched vertices (if every vertex is matched then the matching is maximum). We construct a forest F so that it has one connected component for each vertex of U. As before extend F by alternately adding unmatched and matched edges. Then the edges of M that are added to F will be at an odd distance from U. Also, vertices that are at an odd distance from U will have degree two (with one unmatched edge and one matched edge). Let us call such vertices inner vertices and the rest outer vertices. The vertices of U are all outer vertices.

Now consider the neighborhood of outer vertices. One of the following four possibilities must arise.

- 1. If we find an outer vertex x incident to a vertex y not in F, then we can add the edges (x, y) and (y, z) to F where (y, z) is an edge of M.
- 2. If two outer vertices belonging to different components are adjacent, then the roots of these components have an augmenting path between them.
- 3. If two outer vertices x, y in the same component are adjacent, then let C be the cycle formed by the edge (x, y) along with the path from x to y in F. Let P be the path connecting C to the root of the component. First, we can switch the edges of P to obtain a matching M<sub>1</sub> of the same size as P. Then C satisfies the condition of the cycle shrinking lemma. So we shrink C to a single vertex and get a new graph G'. Now the goal is to find an augmenting path in G'.
- 4. If every outer vertex only has inner vertices as neighbors, then M is already maximum. Too see this suppose F has p inner vertices and q outer vertices. Then q p = |U| since each matched outer vertex is matched with an inner vertex and vice versa. Now if we delete all the inner vertices of F from G, then the outer vertices will all be isolated components. But this means that any matching of G has to miss at least q p of them, and hence q p vertices of G. Since M misses exactly q p vertices, it must be maximum.

Thus, from the description of the algorithm, we obtain the lemma below.

**Lemma 9.** At each step of the algorithm, we either increase the size of F, or decrease the size of G or find an augmenting path or stop with a maximum matching.

**Theorem 10.** A maximum matching can be found in  $O(n^4)$  time.

**Proof.** Clearly our algorithm makes less than n augmentations. In addition, we can shrink at most n blossoms before finding an augmenting path. Finding an augmenting path or a blossom takes O(m) time since in growing a forest we examine each edge at most once. Hence our overall running time is  $O(mn^2) = O(n^4)$ .

The following theorem can be derived from Edmonds' algorithm.

**Theorem 11 (Tutte).** A graph G has a perfect matching iff for any subset of vertices X, the number of odd-sized components of the graph  $G \setminus X$  obtained by deleting X from G is at most |X|.

*Proof.* The necessity of the right hand condition is clear: if there exists a set of vertices X such that G - X has more that |X| odd-sized components, then there aren't enough vertices in X to match all the odd-sized components, because odd-sized components need an external vertex to be matched and can only be matched with vertices in X.

For the sufficiency, consider the forest in Edmonds' algorithm at the last step. Denote by X the set of inner vertices, p = |X|. Note that the vertices of X haven't been shrunk, because shrunk vertices have to be unmatched. If we consider G - X, then we get the outer vertices as isolated components (that is how the algorithm terminates: outer vertices only have inner vertices as neighbors). Some of these may correspond to shrunk odd components in the original graph. As in the description of the algorithm, call q the number of outer vertices, so that q - p is the number of unmatched vertices. Because of our hypothesis (applied to the set X), we have at most |X| odd components in the original graph, that is, we have at most p outer vertices. In other words, q = p and all vertices are matched.  $\square$ 

In his paper (called "Paths, Trees and Flowers") describing this algorithm, Edmonds also defined the notion of polynomial-time algorithms. In the decades since, this notion has come to play a fundamental role in complexity theory.

---

#### 18.433 Combinatorial Optimization

# The Simplex Algorithm

October 16, 23 Lecturer: Luis Rademacher

We proved the following:

**Lemma 1 (Farkas).** Let  $A \in \mathbb{R}^{m \times n}$ ,  $b \in \mathbb{R}^m$ . Exactly one of the following conditions is true:

1.  $\exists x \in \mathbb{R}^n : Ax = b \text{ and } x \ge 0$ 

2.  $\exists y \in \mathbb{R}^m : b^T y < 0 \text{ and } A^T b > 0.$ 

Consider a linear problem in standard form and its dual:

(P) 
$$\operatorname{opt}(P) = \max c^T x$$
  $\operatorname{opt}(D) = \min b^T y$  (D)  
s.t.  $Ax = b$  s.t.  $A^T y \ge c$   
 $x > 0$ 

We say that a problem is bounded if its optimum value is finite. We proved the weak duality theorem:

**Theorem 2.** If (P) and (D) are feasible, then  $opt(P) \leq opt(D)$  and finite. In particular, (P) is bounded.

The following corollary is an immediate consequence:

**Corollary 3.** If (D) is feasible, then (P) is bounded or infeasible. If (P) is feasible, then (D) is bounded or infeasible.

# 1 Strong duality

The previous corollary says that some combinations of being feasible (F), bounded (B), unbounded (U) and infeasible (I) for the primal and dual are not possible. For example, primal feasible, dual feasible and unbounded is impossible by the corollary. The strong duality theorem will tell us exactly which combinations are possible and, additionally, it will prove that in the case where the primal is bounded and feasible we have that opt(P) = opt(D), which is the most important conclusion.

**Theorem 4 (Strong duality).** For a linear program (P) and its dual (D) there are only the following possibilities:

- 1. (P) B F and (D) B F. In this case opt(P) = opt(D).
- 2. (P) I, (D) U F.
- 3. (P) U F, (D) I.
- 4. (P) I, (D) I.

*Proof.* A priori, there are 9 possible combinations. Weak duality already ruled out

- (P) B F, (D) U F,
- (P) U F, (D) B F, and
- (P) U F, (D) U F.

We will eliminate the case (P) B F, (D) I, then duality eliminates (P) I, (D) B F. Only the 4 claimed cases survive.

Assume that (P) B F. Let  $z > \operatorname{opt}(P)$ . Apply Farkas' lemma to  $A_0 = \binom{A}{c^T}$ ,  $b_0 = \binom{b}{z}$ . We know that  $c^T x < z$  for all feasible x, that is, x satisfying Ax = b and  $x \ge 0$ . In other words, for all x,  $x \ge 0$  implies that  $A_0 x = \binom{Ax}{c^T x} \ne \binom{b}{z} = b_0$ , i.e. condition (1) in Farkas' lemma is not satisfied; thus, (2) in the lemma is true: there exists  $y \in \mathbb{R}^m$  and there exists  $\alpha \in \mathbb{R}$  such that  $b^T y + z\alpha < 0$  and  $A^T y + \alpha c \ge 0$ .

We will now see that  $\alpha < 0$ . Else, let  $x^* \in \mathbb{R}^n$  be primal optimal, that is a primal feasible point such that  $c^T x^* = \operatorname{opt}(P)$ . Then the conditions that y and  $\alpha$  satisfy imply:

$$x^{*T}A^Ty + \alpha c^Tx^* \ge 0$$

If  $\alpha \geq 0$  we can get

$$b^T y + \alpha z > 0$$

which is a contradiction.

Thus,  $\alpha < 0$  and  $y_0 = -y/\alpha$  satisfies  $b^T y_0 < z$  and  $A^T y_0 \ge c$ . That is, the dual is feasible (and bounded). Moreover,  $z \ge \text{opt}(P)$  was arbitrary, i.e. for any

$$z > \max_{x>0, Ax=b} c^T x$$

there exists  $y_0$  dual feasible such that

$$\max_{x \ge 0, Ax = b} c^T x \le \min_{y : A^T y \ge c} b^T y \le b^T y_0 < z$$

The fact that z is arbitrary implies that

$$\max_{x \ge 0, Ax = b} c^T x = \min_{y : A^T y > c} b^T y.$$

## 2 Linear programs

Recall our standard form for a linear program:

maximize 
$$z = \mathbf{c}^t \mathbf{x}$$
, subject to  $\mathbf{a} \mathbf{x} \leq \mathbf{b}$ ,  $\mathbf{x} \geq 0$ . (1)

Let us concentrate on a concrete example, the program

# 3 The simplex algorithm

### 3.1 Insert slack variables

To solve the linear program above using the simplex algorithm, we first convert the constraints involving  $\leq$ 's to equality constraints by introducing **slack variables**. Each  $\leq$  inequality,  $\sum_{j=1}^{n} a_{ij}x_j \leq b_i$ , is replaced by the equality,  $\sum_{j=1}^{n} a_{ij}x_j + x_{n+i} = b_i$ , and an additional constraint that the slack variables are non-negative,  $x_{n+i} \geq 0$ .

In terms of our specific example, adding slack variables gives the linear program:

$$2x_1 + 3x_2 + x_3 + x_4 = 5,$$
maximize  $z = 5x_1 + 4x_2 + 3x_3$ , subject to
$$4x_1 + x_2 + 2x_3 + x_5 = 11,$$

$$3x_1 + 4x_2 + 2x_3 + x_6 = 8,$$

$$x_1, x_2, x_3, x_4, x_5, x_6 \ge 0.$$
(3)

### 3.2 Increase the objective function value through a pivot

Let us focus on our specific example. By isolating the slack variables in the equalities, we see that

$$x_4 = 5 - 2x_1 - 3x_2 - x_3$$

$$x_5 = 11 - 4x_1 - x_2 - 2x_3$$

$$x_6 = 8 - 3x_1 - 4x_2 - 2x_3$$
(4)

This suggests one feasible solution,

$$x_1, x_2, x_3 = 0,$$
  
 $x_4 = 5,$   
 $x_5 = 11,$   
 $x_6 = 8.$  (5)

For this solution our objective function is

$$z = 5x_1 + 4x_2 + 3x_3 = 0, (6)$$

which seems low. How can we do better? Perhaps we should attempt to increase  $x_1$ .

If we increase  $x_1$  and hold  $x_2$  and  $x_3$  at zero, we can calculate the required values of  $x_4, x_5$ , and  $x_6$  from (4). For example,

$$x_1 = 1,$$
  $x_2, x_3 = 0,$   $\Rightarrow$   $z = 5,$   $x_4 = 3,$   $x_5 = 7,$   $x_6 = 5,$   
 $x_1 = 2,$   $x_2, x_3 = 0,$   $\Rightarrow$   $z = 10,$   $x_4 = 1,$   $x_5 = 3,$   $x_6 = 2,$  (7)  
 $x_1 = 3,$   $x_2, x_3 = 0,$   $\Rightarrow$   $z = 15,$   $x_4 = -1,$   $x_5 = -1,$   $x_6 = -1.$ 

Increasing  $x_1$  improves the objective function value, but we cannot push  $x_1$  too far or the slack variables become negative, as is the case when  $x_1 = 3$ .

We can calculate the values of  $x_1$  that preserve nonnegativity for the slack variables from (4).

$$x_4 \ge 0 \Rightarrow x_1 \le \frac{5}{2},$$

$$x_5 \ge 0 \Rightarrow x_1 \le \frac{11}{4},$$

$$x_6 \ge 0 \Rightarrow x_1 \le \frac{8}{3},$$

$$(8)$$

so the most we can increase  $x_1$  is to  $x_1 = \frac{5}{2}$ .

Let's rewrite the equality constraints (4) to reflect our decision that  $x_1 = \frac{5}{2}$  and  $x_4 = 0$ .

$$x_{1} = \frac{5}{2} - \frac{3}{2}x_{2} - \frac{1}{2}x_{3} - \frac{1}{2}x_{4} ,$$

$$x_{5} = 11 - 4(\frac{5}{2} - \frac{3}{2}x_{2} - \frac{1}{2}x_{3} - \frac{1}{2}x_{4}) - x_{2} - 2x_{3},$$

$$x_{6} = 8 - 3(\frac{5}{2} - \frac{3}{2}x_{2} - \frac{1}{2}x_{3} - \frac{1}{2}x_{4}) - 4x_{2} - 2x_{3}.$$

$$(9)$$

and our objective function from (3) may be written  $z = \frac{25}{2} - \frac{1}{2}x_2 + \frac{1}{2}x_3 - \frac{5}{2}x_4$ .

This sequence of operations is called a **pivot**, for reasons which will make more sense when we write everything in tableau form.

### 3.3 Repeat

We have improved our objective function value from 0 to  $\frac{25}{2}$  by pivoting around  $x_1$ . Let's try to do it again. Increasing  $x_2$  will hurt our objective value, as will increasing  $x_4$ . The only thing we can increase is  $x_3$ .

$$x_1 \ge 0 \Rightarrow x_3 \le 5,$$
  
 $x_5 \ge 0$  puts no constraint on  $x_3$ , (10)  
 $x_6 \ge 0 \Rightarrow x_3 \le 1$ ,

so we'll increase  $x_3$  as far as we can, to 1.

Rewriting the equality constraints to reflect our choice of  $x_3 = 1$  and  $x_6 = 0$  yields

$$x_{3} = 1 + x_{2} + 3x_{4} - 2x_{6},$$

$$x_{5} = 1 + 5x_{2} + 2x_{4},$$

$$x_{1} = 1 - 2x_{2} - 2x_{4} + x_{6},$$
(11)

and objective function  $z = 13 - 3x_2 - x_4 - x_6$ .

When the objective function is written in this form, it is clear that increasing any of the variables  $x_2, x_4$ , or  $x_6$  will decrease the objective function value. Therefore the value is at its maximum, 13, when  $x_2, x_4, x_6 = 0$ .

# 4 High level description of the simplex algorithm

In a linear program of the form

$$\max c' x$$
s.t.  $Ax = b$ 

$$x \ge 0,$$

with m equality constraints and n variables, if one sets n-m variables to 0 and lets the equality constraints determine the value of the rest and this values are non-negative, then

that point is feasible and is a vertex (the proof is left as an exercise); it is called a basic feasible solution. The variables that were set to 0 are called the non-basic variables, the rest are the basic variables. The set of basic variables is also called the basis. Note that if the value of a variable is non-zero then it is basic, but the converse is not true. When, in a basic feasible solution, a basic variable is zero, that solution (or basis) is said to be degenerate. The geometrical meaning of this is that each basis has an associated vertex, but a vertex can be associated to several bases (in the degenerate case).

If we denote by B the indices of the basic variables and N the indices of the non-basic variables, the program is in canonical form if  $b \ge 0$  and the program is in the form:

$$\max c'_N x_N + c'_B x_B$$
s.t.  $A_N x_N + I x_B = b$ , 
$$x_N, x_B > 0$$
.

¿From a basic feasible solution (a vertex) and the problem in canonical form, the simplex algorithm chooses a non-basic variable that has a positive reduced cost, that is, a variable that, if increased, would increase the objective function. Then it increases the value of that variable as much as possible, without violating the non-negativity of the basic variables. That variable is made basic; (at least) one of the old basic variable becomes 0, and one becomes non-basic. The sequence of operations called a pivot (in the previous section) goes from the canonical form with respect to the old basis to the canonical form with respect to the new basis.

# 5 The simplex algorithm again (with better notation)

#### 5.1 Simplex tableau notation

If we were going to program a computer to perform the manipulations we outlined in the previous sections, it would be convenient to represent the coefficients in matrix form. When expressed as a matrix, or **simplex tableau**, the linear program in (3) looks like

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

## 5.2 Tableau algorithm

In terms of simplex tableau, the algorithm for solving the problem above is:

1. Look at the last row of the tableau. Find a column in this row with a positive entry. This is the pivot column.

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

2. Among the rows whose entry r in the pivot column is positive, find the row that has the smallest ratio  $\frac{s}{r}$ , where s is this row's entry in the last column. This is the pivot row.

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

3. Divide every entry of the pivot row by the entry in the pivot column.

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

4. For every other row, subtract a multiple of the pivot row to make the entry in the pivot column zero.

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

5. Repeat steps one to four. If step one finds no pivot column, we've reached the optimum. If step two finds no positive ratio then z is unbounded.

#### 5.3 Caveats

#### 5.3.1 Cycling

If you have bad luck in step one, the algorithm could be in a cycle. This is pretty unlikely. If you use a consistent rule for deciding which of the positive entries to make the pivot column, like choose the positive entry with the smallest index (Bland, Robert G., "A combinatorial abstraction of linear programming", *J. Combinatorial Theory*, Ser. B, 23 (1977), no. 1, 33–57.), it is impossible to cycle.

#### 5.3.2 Initial feasible solution

According to the description of the simplex algorithm that we saw, the algorithm can be applied directly only to systems in canonical form. As in our examples, if the system starts (or can be transformed to) the form

$$\max c' x$$
s.t.  $Ax \le b$ 

$$x > 0.$$
(17)

with  $b \ge 0$ , then the introduction of slack variables will leave the system in canonical form. The only non-trivial situation occurs when the system is in the form (17), but b has some negative components. In this case, one adds an auxiliary variable  $x_0$  and consider the problem:

min 
$$x_0$$
  
s.t.  $Ax - x_0 \le b$  (18)  
 $x, x_0 \ge 0$ ,

After adding slack variables, one pivots at variable  $x_0$  and the row associated to the minimum entry of b. This will leave the system in canonical form. Then one solves the problem (18) with the simplex algorithm. Consider now the situation when the algorithm finishes. If  $x_0 > 0$ , then the original problem (17) is infeasible. Else,  $x_0 = 0$ . In this case, if  $x_0$  is basic, then we perform one more pivot operation to make it non-basic. Now that  $x_0 = 0$  and non-basic, we stop considering that column in the tableau and replace the reduced costs by the cost function of (17). This is precisely a canonical form of the problem (17), so that we can apply simplex to it.

Example:

$$\max -2x_1 - 3x_2$$
s.t.  $-x_1 - x_2 \le -3$ 

$$2x_1 - x_2 \le -2$$

$$x_1, x_2 > 0$$

The initial tableau after adding the auxiliary variable  $x_0$  and the slack variables  $x_3$ ,  $x_4$  is

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

After pivoting with respect to the first row and first column we get

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

This tableau is in canonical form.

# 6 A proof of strong duality, based on the simplex algorithm

The strong duality theorem states:

$$\max \sum_{j=1}^{n} c_{j} x_{j}, \text{ subject to} \qquad \min \sum_{i=1}^{m} b_{i} y_{i}, \text{ subject to}$$

$$\sum_{j=1}^{n} a_{ij} x_{j} \leq b_{i} \qquad \sum_{i=1}^{m} a_{ij} y_{i} \geq c_{j}$$

$$x_{j} \geq 0 \qquad y_{i} \geq 0$$

$$(19)$$

We proved it already using Farkas' Lemma. Now we will prove it again using ideas borrowed from the simplex algorithm.

Weak duality proved

$$\sum_{j=1}^{n} c_j x_j \le \sum_{i=1}^{m} b_i y_i \tag{20}$$

for any feasible values of  $x_j$ 's and  $y_i$ 's, so to prove strong duality it is sufficient to exhibit feasible  $x_j$ 's and  $y_i$ 's where the sums are equal.

Given a linear program,

maximize 
$$\sum_{j=1}^{n} c_j x_j$$
, subject to  $\sum_{j=1}^{n} a_{ij} x_j \le b_i$ ,  $x_i \ge 0$ , (21)

let  $x_1^*, ..., x_n^*$  be a feasible solution that maximizes the objective function, and let  $z^* = \sum_{j=1}^n c_j x_j^*$  be the value of the maximum.

We introduce slack variables,

$$x_{n+i} = b_i - \sum_{j=1}^{n} a_{ij} x_j, \tag{22}$$

to convert the standard form linear program to the equality form we use in the simplex algorithm.

Because  $z^*$  is the maximum feasible value of the objective function we can write the value of the objective function for any feasible solution as

$$z = z^* + \sum_{k=1}^{n+m} \bar{c}_k x_k \tag{23}$$

for some  $\bar{c}_k \leq 0$ .

Let

$$y_i^* = -\bar{c}_{n+i}. (24)$$

We will show that  $z^* = \sum_{i=1}^m b_i y_i^*$  and  $\sum_{i=1}^m a_{ij} y_i^* \ge c_j$ . Since  $y_i^* \ge 0$  by construction, this will prove that a feasible dual solution is equal to a feasible primal solution.

Begin with z:

$$z = \sum_{j=1}^{n} c_j x_j = z^* + \sum_{k=1}^{m+n} \bar{c}_k x_k.$$
 (25)

We break up the sum

$$z = z^* + \sum_{j=1}^n \bar{c}_j x_j + \sum_{k=n+1}^{n+m} \bar{c}_k x_k.$$
 (26)

Substituting (24) to remove the  $\bar{c}$ 's in the second sum gives

$$z = z^* + \sum_{j=1}^n \bar{c}_j x_j + \sum_{i=1}^m -y_k^* x_{n+i}.$$
 (27)

Substituting (22) to remove the slack variables gives

$$z = z^* + \sum_{j=1}^n \bar{c}_j x_j + \sum_{i=1}^m -y_k^* (b_i - \sum_{j=1}^n a_{ij} x_j).$$
 (28)

Regrouping, reversing the order of the double sum, and regrouping some more, we have

$$z = (z^* - \sum_{i=1}^m b_i y_i^*) + \sum_{j=1}^n (\bar{c}_j + \sum_{i=1}^m a_{ij} y_i^*) x_j.$$
 (29)

Note that all the previous manipulations are just a rewriting of the objective function, and are valid for any  $x \in \mathbb{R}^n$ . So, it is true for  $x_j = 0$ . Therefore,

$$z^* = \sum_{i=1}^{m} b_i y_i^*, \tag{30}$$

which finishes half of the proof.

To see that the  $y_i$ 's are a feasible solution, we plug the value of  $z^*$  from (30) into (29) and set this equal to the original formula (25).

$$z = \sum_{j=1}^{n} (\bar{c}_j + \sum_{i=1}^{m} a_{ij} y_i^*) x_j = \sum_{j=1}^{n} c_j x_j.$$
 (31)

These sums can be equal only if the coefficients of the  $x_j$ 's are all equal (again, because this equality is true for any  $x \in \mathbb{R}^n$ ):

$$c_j = \bar{c}_j + \sum_{i=1}^m a_{ij} y_i^*. (32)$$

But each  $\bar{c}_j \leq 0$ , so

$$\sum_{i=1}^{m} a_{ij} y_i^* \ge c_{ij}. \tag{33}$$

This completes the proof of strong duality.

---

## Lecture The Ellipsoid Algorithm

Oct 30, Nov 4 Lecturer: Santosh Vempala

## 1 The Algorithm for Linear Programs

**Problem 1.** Given a polyhedron P, written as  $Ax \leq b$ , find a point in P.

Before tackling this problem, we begin with some definitions. A real symmetric matrix A with the property that  $x^TAx > 0$  for all  $x \neq 0$  is called *positive definite*. If A is positive definite, then there exists an invertible matrix P, such that  $A = P^TP$ . Let D be a positive definite matrix and consider the ellipsoid  $\text{Ell}(D,z) = \{x : (x-z)^TD^{-1}(x-z) \leq 1\}$ . Let  $\nu$  be the maximum number of bits required to describe a vertex of P and set  $R = 2^{\nu}$ . To solve Problem 1 we apply the following algorithm:

THE ELLIPSOID ALGORITHM

Start with the ellipsoid  $E_0 = \text{Ell}(R^2I, 0)$ .

At the  $i^{th}$  iteration, check whether  $z_i$  is in P.

- YES. Output  $z_i$  as the feasible point.
- NO. Find a constraint for P,  $a_k \cdot x \leq b_k$ , violated by  $z_i$ . Recurse on  $E_{i+1}$ , the minimum volume ellipsoid containing  $E_i \cap \{x \mid a_k \cdot x \leq a_k \cdot z_i\}$ .

Figure 1: One cycle of the algorithm

Observe that the algorithm halts when a point  $z_i$  is found to be within P. It must halt,

since at any step i, P is a subset of  $E_i$ , and we will see that after each step, the volume of  $E_{i+1}$  has decreased by an appreciable amount. For some value of i, the volume of  $E_i$  will be smaller than the volume of P, so the algorithm must halt before reaching this point. In the next section we show that the algorithm can actually be implemented in polynomial time.

## 2 The Time Bound

**Lemma 1.** The minimum volume ellipsoid containing  $\text{Ell}(D, z) \cap \{x \mid a \cdot x \leq a \cdot z\}$  is exactly E' = Ell(D', z'), where

$$z' = z - \frac{1}{n+1} \frac{Da}{\sqrt{a^T Da}} \tag{1}$$

and

$$D' = \frac{n^2}{n^2 - 1} \left( D - \frac{2}{n+1} \frac{Daa^T D}{a^T Da} \right)$$
 (2)

and

$$\frac{\operatorname{vol}(E')}{\operatorname{vol}(E)} \le e^{\frac{-1}{2n+2}} \tag{3}$$

**Sketch of proof:** First, note that Ell(A, 0) can be obtained from Ell(I, 0) (the unit ball) using the transformation y = Bx, where  $A = B^TB$ . To see this, consider the following:

$$x^{T}x \leq 1$$

$$y^{T}(B^{-1})^{T}(B^{-1})y = x^{T}x$$

$$y^{T}(B^{-1})^{T}(B^{-1})y \leq 1$$

$$y^{T}A^{-1}y \leq 1$$

where the first and last equations define the unit ball and Ell(A,0), respectively.

Now, first we will prove the results (1) and (2) for the special case of the unit ball, E = Ell(I, 0). In this case, (1) reduces to

$$z' = z - \frac{1}{n+1} \frac{a}{\sqrt{a^T a}}$$

and (2) reduces to

$$D' = \frac{n^2}{n^2 - 1} \left( I - \frac{2}{n+1} \frac{aa^T}{a^T a} \right)$$

Since E is a ball, we can rotate a without affecting anything. So, assume  $a = [1, 0, \dots, 0]^T$ . Then,  $z' = [-1/(n+1), 0, \dots, 0]^T$ .

Figure 2: Transform space to take E to a ball

$$D' = \frac{n^2}{n^2 - 1} \left( I - \frac{2}{n+1} \begin{bmatrix} 1 & & & \\ & 0 & & \\ & & \ddots & \\ & & & 0 \end{bmatrix} \right)$$
$$= \frac{n^2}{n^2 - 1} \begin{bmatrix} 1 - \frac{2}{n+1} & 0 & 0 & \cdots & 0 \\ 0 & 1 & & & \\ 0 & & 1 & & \\ \vdots & & & \ddots & \\ 0 & & & & 1 \end{bmatrix}$$

The simplified statements for z' and D' can be proved by calculus. The general case is then proved by applying a transformation of A to the unit ball  $(B^{-1}$  above; the transformation scales the volume of a convex set by the factor  $\det(B)$ .

Assuming (1) and (2), we can now prove (3). observe that:

$$\frac{\operatorname{vol}(\operatorname{Ell}(D',z'))}{\operatorname{vol}(\operatorname{Ell}(D,z))} = \frac{\operatorname{vol}(\operatorname{Ell}(I,0))}{\operatorname{vol}(\operatorname{Ell}(I,0))} \, \frac{\sqrt{\det(D')}}{\sqrt{\det(D)}}$$

We transform space to take E to the unit ball. The transformed E' is still the minimum ellipsoid containing half of E.

Then, assuming D = I, we have  $\sqrt{\det(D')} = \operatorname{vol}(E')/\operatorname{vol}(E)$ . Now we can use (2).

$$D' = \frac{n^2}{n^2 - 1} \left( I - \frac{2}{n+1} \begin{bmatrix} 1 & & & \\ & 0 & & \\ & & \ddots & \\ & & & 0 \end{bmatrix} \right)$$

The determinant of this matrix is

$$\det(D') = \left(\frac{n^2}{n^2 - 1}\right)^n \left(1 - \frac{2}{n+1}\right)$$

Hence,

$$\frac{\operatorname{vol}(E')}{\operatorname{vol}(E)} = \left(\frac{n^2}{n^2 - 1}\right)^{n/2} \left(\frac{n - 1}{n + 1}\right)^{1/2} \\
= \left(\frac{n^2}{n^2 - 1}\right)^{\frac{n - 1}{2}} \frac{n}{(n - 1)^{1/2}(n + 1)^{1/2}} \frac{(n - 1)^{1/2}}{(n + 1)^{1/2}} \\
= \left(1 + \frac{1}{n^2 - 1}\right)^{\frac{n - 1}{2}} \left(1 - \frac{1}{n + 1}\right) \\
\le e^{\frac{1}{(n - 1)(n + 1)} \frac{(n - 1)}{2}} e^{\frac{-1}{n + 1}} = e^{\frac{-1}{2(n + 1)}}$$

(using 
$$e^x \ge 1 + x$$
).

We need to calculate how small P can be in order to obtain a bound on the number of times we shrink E'. We will see that  $\operatorname{vol}(P) \geq 2^{-2n\nu}$  by finding a simplex inside P. Clearly the volume of the simplex will be less than or equal to the volume of P.

Now there exist n+1 affinely independent verticies of P, say  $x_0, x_1, \ldots, x_n$ .

$$\operatorname{vol}(\operatorname{conv}(x_0, \dots, x_n)) = \frac{1}{n!} \left| \det \begin{bmatrix} 1 & 1 & & 1 \\ & & \dots & \\ x_0 & x_1 & & x_n \end{bmatrix} \right|$$

A vertex  $x_i$  is a solution to a subset  $C_i$  of rows of  $Ax \leq b$ . We can solve for it using Cramer's Rule,  $x_{ij} = \frac{\det(C_{ij})}{\det(C_j)}$ , where  $C_{ij}$  is the matrix  $C_i$  with the  $i^{th}$  column replaced by b restricted to the relevant rows for  $C_i$ . So,

$$vol(conv(x_0, ..., x_n)) = \frac{1}{n!} det \begin{bmatrix} 1 & 1 \\ \frac{\det C_{11}}{\det C_1} & \frac{\det C_{12}}{\det C_2} \\ \frac{\det C_{21}}{\det C_1} & \frac{\det C_{22}}{\det C_2} \\ \vdots & & \ddots \end{bmatrix}$$

Pulling out the denominators, we see that

$$\frac{1}{n!} \det \left( \begin{bmatrix} \det C_1 & \det C_2 \\ \det C_{11} & \det C_{12} \\ & \ddots \\ & \det C_{nn} \end{bmatrix} \begin{bmatrix} \frac{1}{\det C_1} \\ & \frac{1}{\det C_2} \\ & \ddots \\ & \frac{1}{\det C_n} \end{bmatrix} \right) \right| \\
\geq \frac{1}{n!} \frac{1}{\det(C_1) \det(C_2) \cdots \det(C_n)}$$

As  $\det C_i \leq 2^{\nu}$ , we have  $\operatorname{vol}(\operatorname{conv}(x_0,\ldots,x_n)) \geq n^{-n}(2^{-\nu})^n \geq 2^{-2n\nu}$ . After i steps,  $\operatorname{vol}(E_i) \leq (2R)^n e^{\frac{-i}{2n+2}}$ . We stop before  $\operatorname{vol}(E_i) < \operatorname{vol}(P)$ . Thus,

$$2^{(\nu+1)n}e^{\frac{-i}{2n+2}} < 2^{-2n\nu}$$

which means we stop when  $i = O(n^2\nu)$ . Recall that  $\nu$  was less than the number of bits required to write down any  $n \times n$  subset of  $\{A,b\}$ , plus  $\log n$  bits. So, the the number of iterations is  $O(n^2\langle C,d\rangle)$ . If we use L-bit numbers, then  $\langle C,d\rangle = O(n^2L)$ . To check the validity of a point, we must check each constraint of P, taking O(mn) time. This dominates the time required to calculate the minimum ellipsoid. So the total time required to complete the algorithm is at most  $O(mn^5L)$ .

---

### 18.433 Combinatorial Optimization

# Approximation Algorithms

November 20,25 Lecturer: Santosh Vempala

# 1 Approximation Algorithms

Any known algorithm that finds the solution to an NP-hard optimization problem has exponential running time. However, sometimes polynomial time algorithms exist which find a "good" solution instead of an optimum solution.

Given a minimization problem and an approximation algorithm, we can evaluate the algorithm as follows. First, we find a lower bound on the optimum solution. Then we compare the algorithm's performance against the lower bound. For a maximization problem, we would find an upper bound and compare the solutions found by our approximation algorithm with that.

#### 1.1 Minimum Vertex Cover

Remember a vertex cover is a set of vertices that touch all the edges in the graph. The Minimum Vertex Cover Problem is to find the least-cardinality vertex cover.

A lower bound on the minimum vertex cover is given by a maximal matching. Since no two edges in a matching share the same vertex, there must be at least one vertex in the vertex cover for each edge in the matching.

Also, notice that the set of all matched vertices in a maximum matching is a vertex cover. This follows as any edge whose end-vertices are both unmatched may be added to the matching, contradicting the maximality of the matching. Clearly this algorithm contains twice as many vertices as our lower bound, which is the number of edges in a maximal matching. So the algorithm is within twice optimal.

Two issues are of interest here: how good is our lower bound with respect to the optimal solution, and how good is our final solution with respect to the optimal solution.

First we show that the lower bound can be a factor 2 away from optimal. Consider the complete graph with n edges. The maximal matching has  $\frac{n}{2}$  edges, so our lower bound is  $\frac{n}{2}$ .

However, n-1 vertices are required to cover the graph. To see this, consider any set of n-2 vertices. Because the graph is complete, there is an edge between the two omitted vertices that is not touched by the n-2 chosen vertices. For large n, we have  $\frac{\text{OPT}}{\text{LB}} = \frac{n-1}{\frac{1}{2}n} \to 2$ . So by comparing any algorithm to this bound, we will never have a tighter result than within twice optimal.

Now we compare our final solution to the optimal one. Our algorithm outputs all the vertices matched by a maximal matching. So consider a complete bipartite graph, with n vertices on each side of the partition. The graph contains a perfect matching so the algorithm outputs every vertex i.e. 2n vertices. The optimal vertex cover needs only n vertices, though, those vertices from one side of the partition. Thus we see that the bound on the algorithm's performance is tight.

## 1.2 The Travelling Salesman Problem

The travelling salesman problem is the following. Given a complete graph G = (V, E), and a metric function d(i, j) that gives edge lengths, find a Hamiltonian cycle of minimum total length. Notice that a minimum spanning tree (MST) is a lower bound on the optimum. For suppose there was a tour shorter than the MST. Remove an edge from the tour, and then it is a smaller spanning tree.

The Tree Algorithm: We can also construct an approximate solution from the MST. Find the MST, and double the edges. Note that each vertex now has even degree. Thus we can find an Eulerian tour in our new graph. From this tour we can derive an Hamiltionian cycle by short-cutting past vertices that we have already visited. By the triangle inequality, which holds because d(i, j) is a metric, the cost of the Hamiltonian cycle is at most the cost of the Eulerian tour. The cost of the Eulerian tour, though, is twice the cost of the MST. Therefore our algorithm provides a solution that is within twice optimal.

Thus our algorithm gives at worst a factor 2 approximation. Is this the true performance of the algorithm? Again, let us first compare the value of the lower bound to the optimal solution. There are cases where the factor 2 may be obtained. Consider the graph consisting of a path on n vertices. Let the edge costs on the path be 1. The cost of edges not on the path are given by their shortest path distances along the path. Thus the minimum spanning tree is of length n-1. The minimum tour, though, has length 2(n-1). Thus even an algorithm that finds the true solution seems only half optimal compared to this bound.

Now let us observe how the algorithm actually performs against the optimal solution. Again,

however, the algorithm may provide a solution that is twice optimal. Consider a ladder-shaped graph, with edge weights of 1. All other edges also assigned weights according to the shortest path distances. Note that the diagonal edges from one rung to the next have weight weight 2. One minimum spanning tree is all the rungs and one side of the ladder. These edges form a comb-shape. Then one way the algorithm could run is to follow the comb-shaped MST, but short-cut between rungs in a saw-tooth fashion. At the end of the ladder, jump back to the start. If there are n rungs, the length of this tour is 4n-2. However, the shortest tour is to run around the perimeter of the ladder, avoiding all rungs. This has length 2n.

Christofides' Algorithm: Another feasible bound on the optimum is given by a minimum-weight perfect matching. Since this is the collection of shortest distances between two points, and contains  $\frac{1}{2}n$  edges since our graph is complete, the minimum-weight perfect matching is less than half the optimum tour. In fact the minimum-weight perfect matching on any even subset of edges is also less than half the optimum tour, by the triangle inequality. This suggests a new algorithm.

First, find an MST. Then find a minimum-weight perfect matching on the odd-degree vertices. Since we added one edge per odd-degree vertex, all vertices are now even degree and we can find an Eulerian tour. Short-circuit the tour to produce an Hamiltonian cycle. The length of this cycle is less than the sum of the length of the MST plus the length of the min weight perfect matching. This is less than three-halves times the optimum. Thus we obtain a  $\frac{3}{2}$ -approximation algorithm. This simple algorithm provides the best guarantee known for the metric Travelling Salesman Problem.

### 1.3 Set Cover

Consider a set S of elements  $\{e_1, e_2, e_3, ..., e_n\}$ , and subsets  $S_1, S_2, S_3, ..., S_m \subseteq S$ . The Set Cover Problem is to find a minimum collection of subsets whose union equals S.

This problem can be written in matrix form. Let the rows represent subsets  $S_i$  and the columns represent elements  $e_j$ , and let  $M_{i,j}$  equal 1 if  $e_j \in S_i$  and 0 otherwise. Then the problem is to find the smallest-cardinality set of rows that covers all the columns.

One approximation algorithm is the greedy algorithm. At each step, pick the subset  $S_i$  that covers the most uncovered elements. We give an example to show that this algorithm can not give a performance guarantee better than  $O(\log n)$ . Let  $S = \{e_1, e_2, ... e_{2n}\}$ , with  $S_1 = \{e_1, e_2, ... e_n\}$  and  $S_2 = \{e_{n+1}, e_{n+2}, ... e_{2n}\}$ . Then, of course,  $S_1$  and  $S_2$  are a set cover.

Now let  $S_3$  contain the first half of both  $S_1$  and  $S_2$  and one more element, so that it covers more than  $S_1$  and  $S_2$ . Let  $S_4$  contain the next quarter of both  $S_1$  and  $S_2$  so that, after picking  $S_3$ , it covers slightly more of the rest of the  $S_3$  than  $S_4$  and  $S_5$ . Continue defining subsets  $S_4$  in this fashion. The greedy algorithm will pick  $S_3, S_4, \ldots$ , and end up with up to  $\log_2(\frac{n}{2})$  sets, whereas the optimum is only two sets.

In order to facilitate analysis of this algorithm, assign a cost to each element based on the set that the greedy algorithm picks. Let  $S_k$  be the  $k^{th}$  set chosen by the greedy algorithm, and let  $S'_k$  be the set of elements in  $S_k$  that were not previously covered by the sets  $\{S_1, S_2, \ldots, S_{k-1}\}$ . Now let the cost of an element  $e_i$  to be  $\frac{1}{|S'_k|}$ , where  $S_k$  is the first set to cover  $e_i$ . It follows that the sum of the costs of the elements is the cardinality of the set cover.

Note that the best-possible average cost of an element is  $\frac{\text{OPT}}{n}$ . In addition, since the greedy algorithm takes the least-cost elements first, we know that  $\cot(e_1) \leq \frac{\text{OPT}}{n}$ . Now, OPT is also an upper bound on the cost of the remaining elements, so  $\cot(e_k) \leq \frac{\text{OPT}}{n-k+1}$ . So the greedy cost is

$$\sum_{k=1}^{n} \cot(e_k) \le \sum_{k=1}^{n} \frac{\text{OPT}}{n-k+1} = \text{OPT} \sum_{k=1}^{n} \frac{1}{n-k+1}$$

We can bound the summation on the right by integrals, and thus observe that the sum is between  $\ln(n+1)$  and  $\ln n + 1$ . So the greedy algorithm is within  $\ln n + 1$  of the optimum. This bound is tight by the previous example.

It has been shown that approximating Set Cover to better than  $O(\log n)$  is itself NP-hard.

## 2 Relax and Round

A general approximation technique is the following. First model the problem as an integer program. Then relax the constraints to obtain a linear program. Solve the linear program (perhaps by using a separation oracle). Then round the fractional solution to an integral solution.

#### 2.1 Minimum Congestion

Given a graph G = (V, E), and a set of pairs of vertices  $(s_1, t_1), (s_2, t_2), \ldots, (s_k, t_k)$ , find a path between each pair  $s_i$  and  $t_i$ . The *congestion* on an edge is the number of paths that use the edge. The problem is to find a set of paths that minimizes the maximum congestion.

This problem is NP-complete.

To reduce this problem to an integer program, use variables  $x_{j,k}^i \in \{0,1\}$ . Assign 1 when the edge (j,k) is included in the path from  $s_i$  to  $t_i$ , and 0 otherwise.

In order to ensure that we generate paths, we set up a flow problem. We require a flow of value 1 from each  $s_i$  to  $t_i$ . Then the divergence of a vertex is 0, i.e.  $\sum_k x_{k,j}^i = \sum_l x_{j,l}^i$  for each vertex j, except when  $j = s_i$  or  $j = t_i$ , in which case the divergence is 1.

Treat the objective function  $\max_{e \in E} \sum_i x_e^i$  as another constraint, such that all the congestions are less than some integer c. Then we can find the optimum by using this feasibility problem in a binary search. The constraint is then  $\sum_i x_e^i \leq c$  for all edges e.

There is an integrality gap, that is, the optimal value of the integer program is not the same as the optimal value of its relaxation. Consider the graph of a box, with  $s_1$  in the upper left corner,  $s_2$  in the upper right,  $t_1$  in the lower right and  $t_2$  in the lower left. Then the optimum solution of the integer program has congestion 2, whereas we can assign flow of 1/2 to all the edges for each i and obtain maximum congestion of 1.

Our first approach to convert the linear program result to a set of paths might be to set  $x_e^i$  to 1 with probability  $x_e^i$  and to 0 with probability  $1 - x_e^i$ . Then the expected value is  $E(x_e^i) = 1 \cdot x_e^i + 0 \cdot (1 - x_e^i) = x_e^i$ , and the expected congestion is the sum of the expected edge weights, which is  $\sum_i x_e^i$ . However, this may not be a solution to the problem: this algorithm could lead us to take a set of edges that do not form paths from  $s_i$  to  $t_i$ .

Notice that the solution to the linear program gives a set of flows, rather than paths. We can decompose the flows into a sum of paths by the following: find a path from  $s_i$  to  $t_i$ , and set its weight to the minimum capacity  $\lambda_1^i$  of its edges. Then delete  $\lambda_1^i p_1$  from the flow and repeat, to get  $\lambda_i^i$ 's.

Also, notice that  $\sum_{j} \lambda_{j}^{i} = 1$  for all i. Therefore, our process for converting the linear program result to an integer solution will be to pick a path for each i with probability  $\lambda_{j}^{i}$ . Then, since the sum of the  $\lambda_{j}^{i}$  for a given edge is  $x_{e}^{i}$ , the expected value of paths from  $s_{i}$  to  $t_{i}$  using edge e is  $x_{e}^{i}$ . Therefore the expected congestion per edge is still  $\sum x_{e}^{i}$ . Notice that this is the expected congestion for a given edge, and we do not yet know what the maximum congestion will be.

Suppose that for any particular edge, given its integer (relaxed) congestion X, and its expected congestion  $\mu$ , we could show that the probability of X being greater than some constant factor  $c\mu$  is less than  $\frac{1}{n^2}$ , where n is the number of vertices. Then (union bound), with probability at least 1/2, every edge has a congestion less than  $c\mu$ . Since the expected

congestion of the linear program is less than the congestion of the integer program,  $c\mu \leq c \text{ OPT}$ .

Markov's inequality says that if X is a non-negative random variable, then  $P(X > c\mu) < 1/c$  for c > 0, so we could use  $c = n^2$ . However, this is no better than what we could have done picking random paths. So, for a particular edge, let  $X^j$  be the indicator of the event "path j through the edge is chosen in the rounding", let  $X = \sum_j X^j$  be the integer congestion of the edge, and let  $\mu = E(X)$ . Then

$$P(X > (1+\delta)\mu) = P\left(e^{tX} > e^{t(1+\delta)\mu} \cdot \frac{E(e^{tX})}{E(e^{tX})}\right)$$

We know

$$E(e^{tX}) = E(e^{t\sum X^i}) = \prod_i E(e^{tX^i}) = \prod_i (p_i e^t + 1 - p_i) = \prod_i (1 + p_i (e^t - 1))$$

Since  $1 + x \le e^x$  for any real x, and  $\sum p_i = \mu$ , we have

$$E(e^{tX}) \le \prod_{i} e^{p_i(e^t - 1)} = e^{e^t - 1} \prod_{i} e^{p_i} = e^{\mu(e^t - 1)}$$

¿From Markov's inequality, we obtain

$$P\left(e^{tX} > e^{t(1+\delta)\mu} \cdot \frac{E(e^{tX})}{E(e^{tX})}\right) \le \frac{E(e^{tX})}{e^{t(1+\delta)\mu}}$$

By substitution

$$\frac{E(e^{tX})}{e^{t(1+\delta)\mu}} \le \frac{e^{\mu(e^t-1)}}{e^{t(1+\delta)\mu}}$$

Set  $t = \ln(1 + \delta)$ . For  $1 + \delta \ge 2e$ , we get

$$P(X > (1+\delta)\mu) \le \left(\frac{e^{\delta}}{(1+\delta)^{1+\delta}}\right)^{\mu} \le \left(\frac{e^{1+\delta}}{(2e)^{1+\delta}}\right)^{\mu} = \frac{1}{2^{(1+\delta)\mu}}$$

Suppose we take  $\delta$  such that  $(1+\delta)\mu = \max(2e\mu, 2\log n)$ . Then

$$P(X < \max(2e\mu, 2\log n)) \le \frac{1}{2^{2\log n}} = \frac{1}{n^2}$$

Therefore with probability  $\frac{1}{2}$  none of the the edges have congestion greater than  $\max(2e\mu, 2\log n)$ . It follows that, by repeating the rounding procedure, we obtain an  $2e\text{OPT}+2\log n$ -approximation guarantee factor. Thus in the worst case we have an  $O(\log n)$  guarantee.
