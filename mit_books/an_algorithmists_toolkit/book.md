#### 18.409 An Algorithmist's Toolkit

September 10, 2009

#### Lecture 1

Lecturer: Jonathan Kelner Scribe: Jesse Geneson (2009)

#### 1 Overview

The class's goals, requirements, and policies were introduced, and topics in the class were described. Everything in the overview should be in the course syllabus, so please consult that for a complete description.

## 2 Linear Algebra Review

This course requires linear algebra, so here is a quick review of the facts we will use frequently.

**Definition 1** Let M by an  $n \times n$  matrix. Suppose that

$$Mx = \lambda x$$

for  $x \in \mathbb{R}^n$ ,  $x \neq 0$ , and  $\lambda \in \mathbb{R}$ . Then we call x an eigenvector and  $\lambda$  an eigenvalue of M.

**Proposition 2** If M is a symmetric  $n \times n$  matrix, then

- If v and w are eigenvectors of M with different eigenvalues, then v and w are orthogonal  $(v \cdot w = 0)$ .
- If v and w are eigenvectors of M with the same eigenvalue, then so is q = av + bw, so eigenvectors with the same eigenvalue need not be orthogonal.
- M has a full orthonormal basis of eigenvectors  $v_1, \ldots, v_n$ . All eigenvalues and eigenvectors are real.
- M is diagonalizable:

$$M = V\Lambda V^T$$

where V is orthogonal (VV<sup>T</sup> =  $I_n$ ), with columns equal to  $v_1, \ldots, v_n$ , and  $\Lambda$  is diagonal, with the corresponding eigenvalues of M as its diagonal entries. So  $M = \sum_{i=1}^n \lambda_i v_i v_i^T$ .

In Proposition 2, it was important that M was symmetric. No results stated there are necessarily true in the case that M is not symmetric.

**Definition 3** We call the span of the eigenvectors with the same eigenvalue an eigenspace.

# 3 Matrices for Graphs

During this course we will study the following matrices that are naturally associated with a graph:

- The Adjacency Matrix
- The Random Walk Matrix
- The Laplacian Matrix
- The Normalized Laplacian Matrix

Let G = (V, E) be a graph, where |V| = n and |E| = m. We will for this lecture assume that G is unweighted, undirected, and has no multiple edges or self loops.

**Definition 4** For a graph G, the adjacency matrix  $A = A_G$  is the  $n \times n$  matrix given by

$$A_{i,j} = \begin{cases} 1 & if (i,j) \in E \\ 0 & otherwise \end{cases}$$

For an unweighted graph G,  $A_G$  is clearly symmetric.

**Definition 5** Given an unweighted graph G, the Laplacian matrix  $L = L_G$  is the  $n \times n$  matrix given by

$$L_{i,j} = \begin{cases} -1 & if (i,j) \in E \\ d_i & if i = j \\ 0 & otherwise \end{cases}$$

where  $d_i$  is the degree of the  $i^{th}$  vertex.

For unweighted G, the Laplacian matrix is clearly symmetric. An equivalent definition for the Laplacian matrix is

$$L_G = D_G - A_G,$$

where  $D_G$  is the diagonal matrix with  $i^{th}$  diagonal entry equal to the degree of  $v_i$ , and  $A_G$  is the adjacency matrix.

## 4 Example Laplacians

Consider the graph H with adjacency matrix

$$\mathbf{A_H} = \left(\begin{array}{ccccc} 0 & 1 & 0 & 1 & 0 \\ 1 & 0 & 1 & 0 & 0 \\ 0 & 1 & 0 & 1 & 1 \\ 1 & 0 & 1 & 0 & 0 \\ 0 & 0 & 1 & 0 & 0 \end{array}\right)$$

This graph has Laplacian

$$\mathbf{L_H} = \begin{pmatrix} 2 & -1 & 0 & -1 & 0 \\ -1 & 2 & -1 & 0 & 0 \\ 0 & -1 & 3 & -1 & -1 \\ -1 & 0 & -1 & 2 & 0 \\ 0 & 0 & -1 & 0 & 1 \end{pmatrix}$$

Now consider the graph G with adjacency matrix

$$\mathbf{A_G} = \left( \begin{array}{ccc} 0 & 1 & 0 \\ 1 & 0 & 1 \\ 0 & 1 & 0 \end{array} \right)$$

This graph has Laplacian

$$\mathbf{L_G} = \left( \begin{array}{rrr} 1 & -1 & 0 \\ -1 & 2 & -1 \\ 0 & -1 & 1 \end{array} \right)$$

 $L_G$  is a matrix, and thus a linear transformation. We would like to understand how  $L_G$  acts on a vector v. To do this, it will help to think of a vector  $v \in \mathbb{R}^3$  as a map  $X : V \to \mathbb{R}$ . We can thus write v as

$$\mathbf{v} = \left(\begin{array}{c} X(1) \\ X(2) \\ X(3) \end{array}\right)$$

The action of  $L_G$  on v is then

$$\mathbf{L}_{\mathbf{G}}v = \begin{pmatrix} 1 & -1 & 0 \\ -1 & 2 & -1 \\ 0 & -1 & 1 \end{pmatrix} \begin{pmatrix} X(1) \\ X(2) \\ X(3) \end{pmatrix} = \begin{pmatrix} X(1) - X(2) \\ 2X(2) - X(1) - X(3) \\ X(3) - X(2) \end{pmatrix} = \begin{pmatrix} X(1) - X(2) \\ 2\left(X(2) - \left[\frac{X(1) + X(3)}{2}\right]\right) \\ X(3) - X(2) \end{pmatrix}$$

For a general Laplacian, we will have

$$[L_G v]_i = [d_i * (X(i) - \text{ average of X on neighbors of i})]$$

**Remark** For any G,  $\mathbf{1} = (1, ..., 1)$  is an eigenvector of  $L_G$  with eigenvalue 0, since for this vector X(i) always equals the average of its neighbors' values.

**Proposition 6** We will see later the following results about the eigenvalues  $\lambda_i$  and corresponding eigenvectors  $v_i$  of  $L_G$ :

- Order the eigenvalues so  $\lambda_1 \leq \ldots \leq \lambda_n$ , with corresponding eigenvectors  $v_1, \ldots, v_n$ . Then  $v_1 = 1$  and  $\lambda_1 = 0$ . So for all  $i \ \lambda_i \geq 0$ .
- One can get much information about the graph G from just the first few nontrivial eigenvectors.

### 5 Matlab Demonstration

As remarked before, vectors  $v \in \mathbb{R}^n$  may be construed as maps  $X_v : V \to \mathbb{R}$ . Thus each eigenvector assigns a real number to each vertex in G. A point in the plane is a pair of real numbers, so we can embed a connected graph into the plane using  $(X_{v_2}, X_{v_3}) : V \to \mathbb{R}^2$ . The following examples generated in Matlab show that this embedding provides representations of some planar graphs.

Figure 1: Plots of the first two nontrivial eigenvectors for a ring graph and a grid graph

Image courtesy of Dan Spielman. Used with Permission.

Figure 2: Handmade graph embedding (left) and plot of the first two nontrivial eigenvectors (right) for an interesting graph due to Spielman

Image courtesy of Dan Spielman. Used with Permission.

Figure 3: Handmade graph embedding (left) and plot of first two nontrivial eigenvectors (right) for a graph used to model an airfoil

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

#### 18.409 An Algorithmist's Toolkit

September 15, 2007

### Lecture 2

Lecturer: Jonathan Kelner

Scribe: Mergen Nachin 2009

## 1 Administrative Details

• Signup online for scribing.

## 2 Review of Lecture 1

All of the following are covered in detail in the notes for Lecture 1:

- The definition of  $L_G$ , specifically that  $L_G = D_G A_G$ , where  $D_G$  is a diagonal matrix of degrees and  $A_G$  is the adjacency matrix of graph G.
- The action of  $L_G$  on a vector x, namely that

$$[L_G x]_i = deg(i) (x_i - \text{average of } x \text{ on neighbors of } i)$$

• The eigenvalues of  $L_G$  are  $\lambda_1 \leq \cdots \leq \lambda_n$  with corresponding eigenvectors  $v_1, \ldots, v_n$ . The first and the most trivial eigenvector is  $v_1 = \mathbf{1}$  with an eigenvalue  $\lambda_1 = 0$ . We are mostly interested in  $v_2$  and  $\lambda_2$ .

# 3 Properties of the Laplacian

#### 3.1 Some simple properties

**Lemma 1 (Edge Union)** If G and H are two graphs on the same vertex set with **disjoint** edge sets,

$$L_{G \cup H} = L_G + L_H \text{ (additivity)}$$
 (1)

**Lemma 2 (Isolated Vertices)** If a vertex  $i \in G$  is isolated, then the corresponding row and column of the Laplacian are zero, i.e.  $[L_G]_{i,j} = [L_G]_{j,i} = 0$  for all j.

**Lemma 3 (Disjoint Union)** These together imply that the Laplacian of the disjoint union of G and H is direct sum of  $L_G$  and  $L_H$ , i.e.:

$$L_{G\coprod H} = L_G \oplus L_H = \begin{pmatrix} L_G & 0 \\ 0 & L_H \end{pmatrix}$$
 (2)

**Proof** Consider the graph  $G \coprod v(H) = (V_G \cup V_H, E_G)$ , namely the graph consisting of G along with the vertex set of H as disjoint vertices. Define  $v(G) \coprod H$  similarly. By the second remark,

$$L_{G\coprod v(H)} = \left( \begin{array}{cc} L_G & 0 \\ 0 & 0 \end{array} \right) \quad \text{and} \quad L_{v(G)\coprod H} = \left( \begin{array}{cc} 0 & 0 \\ 0 & L_H \end{array} \right).$$

By definition,  $G \coprod H = (G \coprod v(H)) \cup (v(G) \coprod H)$ , and so by the first remark:

$$L_{G\coprod H} = L_G \oplus L_H = \begin{pmatrix} L_G & 0 \\ 0 & L_H \end{pmatrix}.$$

This implies the Laplacian is the direct sum of the Laplacians of the connected components. Thus,

**Theorem 4 (Disjoint Union Spectrum)** If  $L_G$  has eigenvectors  $v_1, \ldots, v_n$  with eigenvalues  $\lambda_1, \ldots, \lambda_n$ , and  $L_H$  has eigenvectors  $w_1, \ldots, w_n$  with eigenvalues  $\mu_1, \ldots, \mu_n$ , then  $L_{G \coprod H}$  has eigenvectors:

$$v_1 \oplus \mathbf{0}, \dots, v_n \oplus \mathbf{0}, \mathbf{0} \oplus w_1, \dots, \mathbf{0} \oplus w_n$$

with corresponding eigenvalues:

$$\lambda_1,\ldots,\lambda_n,\mu_1,\ldots,\mu_n.$$

**Proof** By the previous lemma,

$$L_{G\coprod H}*(v_1\oplus \mathbf{0}) = \left(\begin{array}{cc} L_G & 0 \\ 0 & L_H \end{array}\right) \left(\begin{array}{c} v_1 \\ 0 \end{array}\right) = \left(\begin{array}{c} \lambda_1 v_1 \\ 0 \end{array}\right)$$

Thus  $v_1 \oplus \mathbf{0}$  is an eigenvector of  $L_{GIIH}$  with eigenvalue  $\lambda_1$ . The rest follow by symmetry.

### 3.2 The Laplacian of an edge

**Definition 5** Let  $L_e$  be the Laplacian of the graph on n vertices consisting of just the edge e.

**Example 1** If e is the edge  $(v_1, v_2)$ , then

$$L_e = \begin{pmatrix} 1 & -1 & 0 & & 0 \\ -1 & 1 & 0 & \cdots & 0 \\ 0 & 0 & 0 & & 0 \\ & \vdots & & \ddots & \vdots \\ 0 & 0 & 0 & \cdots & 0 \end{pmatrix}.$$

By additivity, this lets us write:

$$L_G = \sum_{e \in E} L_e \tag{3}$$

This will allow us to prove a number of facts about the Laplacian by proving them for one edge and adding them up. The more general technique, which we'll use more later, is to bound Laplacians by adding matrices of substructures.

So for an edge e,

$$L_e = \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix} \oplus [\text{zeros}].$$

Note that:

$$\begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix} = \begin{pmatrix} 1 \\ -1 \end{pmatrix} \begin{pmatrix} 1 & -1 \end{pmatrix} = 2 \begin{pmatrix} \frac{1}{\sqrt{2}} \\ -\frac{1}{\sqrt{2}} \end{pmatrix} \begin{pmatrix} \frac{1}{\sqrt{2}} & -\frac{1}{\sqrt{2}} \end{pmatrix},$$

and so  $\begin{pmatrix} \frac{1}{\sqrt{2}} & -\frac{1}{\sqrt{2}} \end{pmatrix}^T$  is an eigenvector with eigenvalue 2. This decomposition implies:

$$x^{T}L_{e}x = \begin{pmatrix} x_{1} & x_{2} \end{pmatrix} \begin{pmatrix} 1 \\ -1 \end{pmatrix} \begin{pmatrix} 1 & -1 \end{pmatrix} \begin{pmatrix} x_{1} \\ x_{2} \end{pmatrix} = (x_{1} - x_{2})^{2}.$$
 (4)

**Remark** The Laplacian is a quadratic form, specifically:

$$x^{T}L_{G}x = x^{T}(\sum_{e \in E} L_{e})x = \sum_{e \in E} x^{T}L_{e}x = \sum_{(i,j)\in E} (x_{i} - x_{j})^{2}$$
(5)

This implies that L is positive semidefinite.

#### 3.3 Review of Positive Semidefiniteness

**Definition 6** A symmetric matrix M is positive semidefinite (PSD) if  $\forall x \in \mathbb{R}^n$ ,

$$x^T M x > 0$$
.

M is positive definite (PD) if the inequality is strict  $\forall x \neq 0$ .

**Lemma 7** M is PSD iff all eigenvalues  $\lambda_i \geq 0$ . Similarly M is PD iff all eigenvalues  $\lambda_i > 0$ .

**Proof** Let's consider the matrix M in its eigenbasis, that is  $M = Q^T \Lambda Q$ . Clearly,  $y^T \Lambda y = \sum_i \lambda_i y_i^2 \ge 0$  for all  $y \in \mathbb{R}^n$  iff  $\lambda_i \ge 0$  for all i. Similar for PD matrix.

Lemma 8 (PSD Matrix Decomposition) M is PSD iff there exists a matrix A such that

$$M = A^T A. (6)$$

Note that A can be  $(n \times k)$  for any k, and that it need not be square. Importantly, note that A is not unique.

#### Proof

 $(\Rightarrow)$  If M is positive semidefinite, recall that M can be diagonalized as

$$M = Q^T \Lambda Q$$
.

thus

$$M = Q^T \Lambda^{1/2} \Lambda^{1/2} Q = \left(\Lambda^{1/2} Q\right)^T \left(\Lambda^{1/2} Q\right),$$

where  $\Lambda^{1/2}$  has  $\sqrt{\lambda_i}$  on the diagonal.

 $(\Leftarrow)$  If  $M = A^T A$ , then

$$x^T M x = x^T A^T A x = (Ax)^T (Ax)$$

Letting  $y = (Ax) \in \mathbb{R}^k$ , we see that:

$$x^T M x = y^T y = ||y||^2 \ge 0.$$

#### 3.4 Factoring the Laplacian

We know from the previous section that we can factor L as  $A^TA$  using eigenvectors, but there also exists a much nicer factorization which we will show here.

**Definition 9** Let m be the number of edges and n be the number of vertices. Then the incidence matrix  $\nabla = \nabla_G$  is the  $m \times n$  matrix given by:

$$\nabla_{e,v} = \begin{cases} 1 & \text{if } e = (v, w) \text{ and } v < w \\ -1 & \text{if } e = (v, w) \text{ and } v > w \\ 0 & \text{otherwise.} \end{cases}$$
 (7)

Example 2 The Laplacian and the Incidence matrix of the graph G=

is 
$$L_G = \begin{pmatrix} 3 & -1 & -1 & -1 \\ -1 & 1 & 0 & 0 \\ -1 & 0 & 1 & 0 \\ -1 & 0 & 0 & 1 \end{pmatrix}$$
  $\nabla_G = \begin{pmatrix} 1 & -1 & 0 & 0 \\ 1 & 0 & -1 & 0 \\ 1 & 0 & 0 & -1 \end{pmatrix}$ 

Lemma 10  $L_G = \nabla^T \nabla$ .

**Proof** Observe that  $\left[\nabla^T\nabla\right]_{ij}=(i\text{th column of }\nabla)\cdot(j\text{th column of }\nabla)=\sum_e\left(\left[\nabla\right]_{e,v_i}\right)\left(\left[\nabla\right]_{e,v_j}\right)$  This gives three cases:

• When i = j,

$$\left[\nabla^T\nabla\right]_{ij} = \sum_e \left(\left[\nabla\right]_{e,v_i}\right)^2 = \sum_{\substack{e \text{ incident to } v_i}} 1 = deg(i).$$

• When  $i \neq j$  and no edge exists between  $v_i$  and  $v_j$ ,

$$\left[\nabla^T\nabla\right]_{ij} = \sum_e \left(\left[\nabla\right]_{e,v_i}\right) \left(\left[\nabla\right]_{e,v_j}\right) = 0$$

as every edge is non-incident to at least one of  $v_i, v_j$ .

• When  $i \neq j$  and exists an edge e' between  $v_i$  and  $v_j$ ,

$$\left[\nabla^T\nabla\right]_{ij} = \sum_{e} \left(\left[\nabla\right]_{e,v_i}\right) \left(\left[\nabla\right]_{e,v_j}\right) = \left(\left[\nabla\right]_{e',v_i}\right) \left(\left[\nabla\right]_{e',v_j}\right) = -1. \quad \blacksquare$$

Corollary 11 Note that

$$x^{T}L_{G}x = ||\nabla x||^{2} = \sum_{(i,j)\in E} (x_{i} - x_{j})^{2},$$

This gives another proof that L is PSD.

#### 3.5 Dimension of the Null Space

**Theorem 12** If G is connected, the null space is 1-dimensional and spanned by the vector 1.

**Proof** Let  $x \in \text{null}(L)$ , i.e.  $L_G x = 0$ . This implies

$$x^{T}L_{G}x = \sum_{(i,j)\in E} (x_{i} - x_{j})^{2} = 0.$$

Thus,  $x_i = x_j$  for every  $(i, j) \in E$ . As G is connected, this means that all  $x_i$  are equal. Thus every member of the null space is a multiple of 1.

Corollary 13 If G is connected,  $\lambda_2 > 0$ .

Corollary 14 The dimension of the null space of  $L_G$  is exactly the number of connected components of G.

## 4 Spectra of Some Common Graphs

We compute the spectra of some graphs:

**Lemma 15 (Complete graph)** The Laplacian for the complete graph  $K_n$  on n vertices has eigenvalue 0 with multiplicity 1 and eigenvalue n with multiplicity n-1 and associated eigenspace  $\{x|x\cdot 1=0\}$ .

**Proof** By corollary 13, we conclude that eigenvalue 0 has multiplicity 1. Now, take any vector v which is orthogonal to 1 and consider  $[L_{K_n}v]_i$ . Note that this value is equal to

$$(n-1)v_i - \sum_{j \neq i} v_j = nv_i - \sum_j v_j = nv_i$$

Hence any vector v which is orthogonal to 1 is an eigenvector with an eigenvalue n.

**Lemma 16 (Ring graph)** The Laplacian for the ring graph  $R_n$  on n vertices has eigenvectors

$$x_k(u) = \sin(2\pi ku/n)$$
, and

$$y_k(u) = \cos(2\pi ku/n)$$

for  $0 \le k \le n/2$ . Both  $x_k$  and  $y_k$  have eigenvalue  $2 - 2\cos(2\pi k/n)$ . Note that,  $x_0 = \mathbf{0}$  should be ignored and  $y_0$  is  $\mathbf{1}$ , and when n is even  $x_{n/2} = \mathbf{0}$  should be ignored and we only have  $y_{n/2}$ .

**Proof** . The best way to see is to plot the graph on the circle using these vectors as coordinates. Below is the plot for a k = 3.

Just consider vertex 1. Keep in mind that  $\sin(2x) = 2\sin(x)\cos(x)$ . Then,

$$[Lx_k]_1 = 2x_k(1) - x_k(0) - x_k(2)$$

$$= 2\sin(2\pi k/n) - 0 - \sin(2\pi k/n)$$

$$= 2\sin(2\pi k/n) - 2\sin(2\pi k/n)\cos(2\pi k/n)$$

$$= (2 - 2\cos(2\pi k/n))\sin(2\pi k/n)$$

$$= (2 - 2\cos(2\pi k/n))x_k(1)$$

Note that this shows that  $x(u) = \Re(e^{2\pi i(ku+c)/n})$  is an eigenvector for any  $k \in \mathbb{Z}, c \in \mathbb{C}$ .

**Lemma 17 (Path graph)** The Laplacian for the path graph  $P_n$  on n vertices has the same eigenvalues as  $R_{2n}$  and eigenvectors

$$v_k(u) = \sin(\pi k u/n + \pi/2n)$$

for  $0 \le k < n$ 

**Proof** 

We will realize  $P_n$  as quotient of  $R_{2n}$ . Suppose z was an eigenvector of  $L_{R_{2n}}$  in which  $z_i = z_{2n-1-i}$  for  $0 \le i < n$ . Take the first n components of z and call this vector v. Note that for 0 < i < n:

$$\begin{split} [L_{P_n}v]_i &= 2(v_i - \sum \text{neighbors of i in } P_n) \\ &= 2(z_i - \sum \text{neighbors of i in } R_{2n}) \\ &= (z_i - \sum \text{neighbors of i in } R_{2n}) + (z_{2n-i-1} - \sum \text{neighbors of } (2n-i-1) \text{ in } R_{2n}) \\ &= \frac{1}{2}([L_{R_{2n}}z]_i + [L_{R_{2n}}z]_{2n-i-1}) \\ &= \frac{1}{2}(\lambda z_i + \lambda z_{2n-i-1}) \\ &= \lambda z_i \\ &= \lambda v_i \end{split}$$

Now consider the case when i = 0.

$$\begin{aligned} [L_{P_n}v]_0 &= v_0 - v_1 \\ &= 2v_0 - v_1 + v_0 \\ &= 2z_0 - z_1 + z_0 \\ &= 2z_0 - z_1 + z_{2n-1} \\ &= \lambda z_0 \\ &= \lambda v_0 \end{aligned}$$

Hence, v is an eigenvector of  $L_{P_n}$ . Now we show that such v exists, that is, there exists eigenvector z of  $L_{R_{2n}}$  in which  $z_i = z_{2n-1-i}$  for  $0 \le i < n$ . Take z,

$$z_k(u) = \sin(\pi k u/n + \pi/2n)$$
  
= 
$$\sin(\pi k u/n)\cos(\pi/2n) + \cos(\pi k u/n)\sin(\pi/2n)$$
  
= 
$$x_k(u)\cos(\pi/2n) + y_k\sin(\pi/2n)$$

We see that  $z_k$  is in the span of  $x_k$  and  $y_k$ . Hence,  $z_k$  is an eigenvector of  $L_{R_{2n}}$  with an eigenvalue  $2 - 2\cos(2\pi k/n)$  by lemma 16. Check that  $z_k$  satisfies  $z_k(i) = z_k(2n-1-i)$ 

#### 4.1 Graph Products

The next natural example is the grid graph, which will follow from general theory about product graphs.

**Definition 18** Let G = (V, E), and H = (W, F). The product graph  $G \times H$  has vertex set  $V \times W$  and edge set:

$$((v_1, w), (v_2, w)), \quad \forall (v_1, v_2) \in E, w \in W \quad \text{and}$$
  
 $((v, w_1), (v, w_2)), \quad \forall (w_1, w_2) \in F, v \in V.$ 

**Example 3**  $P_n \times P_m = G_{n,m}$ . We see that the vertices of  $P_n \times P_m$  are:

$$v(G_{n,m}) = \left\{ \begin{array}{cccc} (v_1, w_1) & (v_1, w_2) & \cdots & (v_1, w_m) \\ (v_2, w_1) & (v_2, w_2) & \cdots & (v_2, w_m) \\ \vdots & \vdots & \ddots & \vdots \\ (v_n, w_1) & (v_n, w_2) & \cdots & (v_n, w_m) \end{array} \right\}$$

The vertices are written in the above layout because it makes the edges intuitive. The edges are:

- For a fixed w, i.e. a column in the above layout, a copy of  $P_n$ .
- For a fixed v, i.e. a row in the above layout, a copy of  $P_m$ .

Thus  $P_n \times P_m = G_{n,m}$ , which is to say the product of two path graphs is the grid graph.

**Theorem 19 (Graph Products)** If  $L_G$  has eigenvectors  $v_1, \ldots, v_n$  with eigenvalues  $\lambda_1, \ldots, \lambda_n$ , and  $L_H$  has eigenvectors  $w_1, \ldots, w_k$  with eigenvalues  $\mu_1, \ldots, \mu_k$ , then  $L_{G \times H}$  has, for all  $1 \le i \le n$ ,  $1 \le j \le k$ , an eigenvector:

$$z_{ij}(v,w) = x_i(v)y_j(w)$$

of eigenvalue  $\lambda_i + \mu_i$ .

Note importantly that eigenvalues add here, they do not multiply.

**Proof** Let  $A_m$  be the graph with m isolated vertices. We can then decompose the product as:

$$G \times H = (G \times A_k) \cup (A_n \times H),$$

i.e. the edge union of k disjoint copies of G and n disjoint copies of H, exactly as in the definition. By Lemmas 1 and 3 we have

$$L_{G\times H} = L_{G\times A_k} + L_{A_n\times H} = L_G\otimes I_k + I_n\otimes L_H$$

Consider  $z_{ij} = x_i \otimes y_j$  as above for a fixed i and j, we see that:

$$L_{G \times H} z_{ij} = (L_G \otimes I_k) (x_i \otimes y_j) + (I_n \otimes L_H) (x_i \otimes y_j)$$
  
=  $(\lambda_i x_i \otimes y_j) + (x_i \otimes \mu_j y_j)$   
=  $(\lambda_i + \mu_j) (x_i \otimes y_j) = (\lambda_i + \mu_j) z_{ij}$ .

Corollary 20  $G_{n,m}$  has eigenvectors and eigenvalues completely determined by those of  $P_n$  and  $P_m$  as above.

# 5 Why is this called the Laplacian?

It turns out that the graph Laplacian is very naturally related to the continuous Laplacian.

- In 1 dimension, the continuous Laplacian is  $\frac{d}{dx}$ .
- In 2 dimensions, the continuous Laplacian is  $\nabla f = \frac{d^2 f}{dx^2} + \frac{d^2 f}{dy^2}$ .

#### 5.1 Discretizing Derivatives, 1d case

Consider a 1d function  $f: \mathbb{R} \to \mathbb{R}$ , which we wish to discretize at the points  $(\ldots, k-2, k-1, k, k+1, k+2, \ldots)$ :

$$f(k-2)$$
  $f(k-1)$   $f(k)$   $f(k+1)$   $f(k+1)$ 

We approximate the first derivative at the line midpoints,  $\frac{df}{dx}$ , up to scaling, by taking the differences between the values at the adjacent points:

The discrete first derivative of f is a function on edges, and is, up to scaling  $\nabla_{P_n} f$ , the incidence matrix of  $P_n$  defined earlier. In order to compute the second derivative at the original points,  $\frac{d^2 f}{dx^2}$ , again up to scaling, we take the differences of the adjacent midpoints at the vertices:

The discrete second derivative of f is thus, up to scaling,  $-L_{P_n}f$ .

#### 5.2 Discretizing Derivatives, 2d case

Here we discretize  $f: \mathbb{R}^2 \to \mathbb{R}$  on a grid:

To compute the discrete derivative in the x and y directions, we'll just look at a little piece. On the horizontal edges, we approximate  $\frac{df}{dx}$  up to scaling, and do likewise on the vertical edges with  $\frac{df}{dy}$ :

Again, the discrete derivative of f is a function on edges. When we consider the concatenation of the two discretization of the directional derivatives, we see that the discretization of the gradient, up to scaling, is  $\nabla_{G_{n,m}} f$ . Finally we use this to compute the discretized Laplacian, up to scaling, and get:

Thus the discretized Laplacian in two dimensions of f is  $-L_{G_{n,m}}f$ .

#### 5.3 A Note on Fourier Coefficients

We observed that paths and rings had eigenvectors that looked like Fourier coefficients. In the continuous case:

$$\frac{d^2 \sin(kx+c)}{dx^2} = k^2 \sin(kx+c)$$

$$\frac{d^2 \cos(kx+c)}{dx^2} = k^2 \cos(kx+c)$$

Thus  $\sin(kx+c)$  and  $\cos(kx+c)$  are eigenfunctions of the  $\frac{d^2}{dx^2}$  operator, i.e. the 1d Laplacian, both with eigenvalue  $k^2$ .

# 6 Bounding Laplacian Eigenvalues

Lemma 21 (Sum of the eigenvalues) Given an n-vertex graph G with degrees  $d_i$ , where  $d_{\max} = \max_i d_i$ , and Laplacian  $L_G$  with eigenvalues  $\lambda_i$ ,

$$\sum_{i} \lambda_{i} = \sum_{i} d_{i} \le d_{\max} n \tag{8}$$

**Proof** The first two expressions are both the trace, the upper bound is trivial.

**Lemma 22** (Bounds on  $\lambda_2$  and  $\lambda_n$ ) Given  $\lambda_i$  and  $d_i$  as above,

$$\lambda_2 \leq \frac{\sum_i d_i}{n-1} \tag{9}$$

$$\lambda_n \geq \frac{\sum_i d_i}{n-1} \tag{10}$$

**Proof** By the previous slide and the fact that  $\lambda_1 = 0$ , we get  $\sum_{i=2}^n \lambda_i = \sum_i d_i$ . As  $\lambda_2 \leq \cdots \leq \lambda_n$ , the bounds follow immediately.

## 7 Bounding $\lambda_2$ and $\lambda_{\max}$

**Theorem 23 (Courant-Fischer Formula)** For any  $n \times n$  symmetric matrix A,

$$\lambda_{1} = \min_{\|x\|=1} x^{T} A x = \min_{x \neq 0} \frac{x^{T} A x}{x^{T} x}$$

$$\lambda_{2} = \min_{\substack{\|x\|=1 \ x \perp v_{1}}} x^{T} A x = \min_{\substack{x \neq 0 \ x \perp v_{1}}} \frac{x^{T} A x}{x^{T} x}$$

$$\lambda_{\max} = \max_{\|x\|=1} x^{T} A x = \max_{x \neq 0} \frac{x^{T} A x}{x^{T} x}$$
(11)

**Proof** We consider the diagonalization  $A = Q^T \Lambda Q$ . As seen earlier,  $x^T A x = (Qx)^T \Lambda(Qx)$ . As Q is orthogonal, we also have ||Qx|| = x. Thus it suffices to consider diagonal matrices. Moreover, all of the equalities on the right follow immediately from linearity. Thus we need to consider, for ||x|| = 1:

$$x^T \Lambda x = (x_1 \cdots x_n) \begin{pmatrix} \lambda_1 \\ & \ddots \\ & & \lambda_n \end{pmatrix} \begin{pmatrix} x_1 \\ \vdots \\ x_n \end{pmatrix} = \sum \lambda_i x_i^2 = \frac{\sum \lambda_i x_i^2}{\sum x_i^2}.$$

We compute the gradient and find:

$$\left[\nabla_x \left(x^T \Lambda x\right)\right]_i = \frac{2\lambda_i x_i}{\sum x_i^2} - \frac{2\lambda_i x_i^3}{\left(\sum x_i^2\right)^2} = 2\lambda_i (x_i - x_i^3)$$

thus all extremal values occur when one  $x_i = 1$  and the rest are 0. The identities follow immediately.

Corollary 24 (Rayleigh Quotient) Letting G = (V, E) be a graph with Laplacian  $L_G$ ,

$$\lambda_{1} = 0 v_{1} = \mathbf{1}$$

$$\lambda_{2} = \min_{\substack{x \perp v_{1} \\ x \neq 0}} \frac{x^{T} L_{G} x}{x^{T} x} = \min_{\substack{\sum x = 0 \\ x \neq 0}} \frac{\sum_{(i,j) \in E} (x_{i} - x_{j})^{2}}{\sum_{i \in V} x_{i}^{2}}$$

$$\lambda_{\max} = \max_{x \neq 0} \frac{x^{T} L_{G} x}{x^{T} x} = \max_{x \neq 0} \frac{\sum_{(i,j) \in E} (x_{i} - x_{j})^{2}}{\sum_{i \in V} x_{i}^{2}}$$
(12)

The Rayleigh Quotient is a useful tool for bounding graph spectra. Whereas before we had to consider all possible vectors x, now in order to get an upper bound on  $\lambda_2$  we need only produce a vector with small Rayleigh quotient. Likewise to get a lower bound on  $\lambda_{\text{max}}$  we need only to find a vector with large Rayleigh quotient.

Examples next lecture!

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

September 17, 2009

Lecture 3

Lecturer: Jonathan Kelner

 $Scribe: Andre \ Wibisono$ 

# 1 Outline

Today's lecture covers three main parts:

- Courant-Fischer formula and Rayleigh quotients
- The connection of  $\lambda_2$  to graph cutting
- Cheeger's Inequality

# 2 Courant-Fischer and Rayleigh Quotients

The Courant-Fischer theorem gives a variational formulation of the eigenvalues of a symmetric matrix, which can be useful for obtaining bounds on the eigevalues.

Theorem 1 (Courant-Fischer Formula) Let A be an  $n \times n$  symmetric matrix with eigenvalues  $\lambda_1 \leq \lambda_2 \leq \ldots \leq \lambda_n$  and corresponding eigenvectors  $v_1, \ldots, v_n$ . Then

$$\lambda_{1} = \min_{\|x\|=1} x^{T} A x = \min_{x \neq 0} \frac{x^{T} A x}{x^{T} x},$$

$$\lambda_{2} = \min_{\substack{\|x\|=1 \\ x \perp v_{1}}} x^{T} A x = \min_{\substack{x \neq 0 \\ x \perp v_{1}}} \frac{x^{T} A x}{x^{T} x},$$

$$\lambda_n = \lambda_{\max} = \max_{\|x\|=1} x^T A x = \max_{x \neq 0} \frac{x^T A x}{x^T x}.$$

In general, for  $1 \le k \le n$ , let  $S_k$  denote the span of  $v_1, \ldots, v_k$  (with  $S_0 = \{0\}$ ), and let  $S_k^{\perp}$  denote the orthogonal complement of  $S_k$ . Then

$$\lambda_k = \min_{\substack{\|x\|=1\\x \in S_{k-1}^{\perp}}} x^T A x = \min_{\substack{x \neq 0\\x \in S_{k-1}^{\perp}}} \frac{x^T A x}{x^T x}.$$

**Proof** Let  $A = Q^T \Lambda Q$  be the eigendecomposition of A. We observe that  $x^T A x = x^T Q^T \Lambda Q x = (Qx)^T \Lambda (Qx)$ , and since Q is orthogonal, ||Qx|| = ||x||. Thus it suffices to consider the case when  $A = \Lambda$  is a diagonal matrix with the eigenvalues  $\lambda_1, \ldots, \lambda_n$  in the diagonal. Then we can write

$$x^T A x = \begin{pmatrix} x_1 & \cdots & x_n \end{pmatrix} \begin{pmatrix} \lambda_1 & & \\ & \ddots & \\ & & \lambda_n \end{pmatrix} \begin{pmatrix} x_1 \\ \vdots \\ x_n \end{pmatrix} = \sum_{i=1}^n \lambda_i x_i^2.$$

We note that when A is diagonal, the eigenvectors of A are  $v_k = e_k$ , the standard basis vector in  $\mathbb{R}^n$ , i.e.  $(e_k)_i = 1$  if i = k, and  $(e_k)_i = 0$  otherwise. Then the condition  $x \in S_{k-1}^{\perp}$  implies  $x \perp e_i$  for  $i = 1, \ldots, k-1$ , so  $x_i = \langle x, e_i \rangle = 0$ . Therefore, for  $x \in S_{k-1}^{\perp}$  with ||x|| = 1, we have

$$x^{T} A x = \sum_{i=1}^{n} \lambda_{i} x_{i}^{2} = \sum_{i=k}^{n} \lambda_{i} x_{i}^{2} \ge \lambda_{k} \sum_{i=k}^{n} x_{i}^{2} = \lambda_{k} ||x||^{2} = \lambda_{k}.$$

On the other hand, plugging in  $x = e_k \in S_{k-1}^{\perp}$  yields  $x^T A x = (e_k)^T A e_k = \lambda_k$ . This shows that

$$\lambda_k = \min_{\substack{\|x\|=1\\x \in S_{k-1}^{\perp}}} x^T A x.$$

Similarly, for ||x|| = 1,

$$x^{T}Ax = \sum_{i=1}^{n} \lambda_{i} x_{i}^{2} \le \lambda_{\max} \sum_{i=1}^{n} x_{i}^{2} = \lambda_{\max} ||x||^{2} = \lambda_{\max}.$$

On the other hand, taking  $x = e_n$  yields  $x^T A x = (e_n)^T A e_n = \lambda_{\text{max}}$ . Hence we conclude that

$$\lambda_{\max} = \max_{\|x\|=1} x^T A x.$$

The Rayleigh quotient is the application of the Courant-Fischer Formula to the Laplacian of a graph.

Corollary 2 (Rayleigh Quotient) Let G = (V, E) be a graph and L be the Laplacian of G. We already know that the smallest eigenvalue is  $\lambda_1 = 0$  with eigenvector  $v_1 = 1$ . By the Courant-Fischer Formula,

$$\lambda_2 = \min_{\substack{x \neq 0 \\ x \mid y_1}} \frac{x^T A x}{x^T x} = \min_{\substack{x \neq 0 \\ x \mid 1}} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i \in V} x_i^2},$$

$$\lambda_{\max} = \max_{x \neq 0} \frac{x^T A x}{x^T x} = \max_{x \neq 0} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i \in V} x_i^2}.$$

We can interpret the formula for  $\lambda_2$  as putting springs on each edge (with slightly weird boundary conditions corresponding to normalization) and minimizing the potential energy of the configuration.

Some big matrices are hard or annoying to diagonalize, so in some cases, we may not want to calculate the exact value of  $\lambda_2$ . However, we can still get an approximation by just constructing a vector x that has a small Rayleigh quotient. Similarly, we can find a lower bound on  $\lambda_{max}$  by constructing a vector that has a large Rayleigh quotient. We will look at two examples in which we bound  $\lambda_2$ .

### 2.1 Example 1: The Path Graph

Let  $P_{n+1}$  be the path graph of n+1 vertices. Label the vertices as  $0, 1, \ldots, n$  from one end of the path to the other. Consider the vector  $x \in \mathbb{R}^{n+1}$  given by  $x_i = 2i - n$  for vertices  $i = 0, 1, \ldots, n$ . Note that  $\sum_{i=0}^{n} x_i = 0$ , so  $x \perp 1$ . Calculating the Rayleigh quotient for x gives us

$$\frac{\sum_{(i,j)\in E} (x_i - x_j)^2}{\sum_{i\in V} x_i^2} = \frac{4n}{\sum_{i=0}^n (2i - n)^2} = \frac{4n}{\Omega(n^3)} = O\left(\frac{1}{n^2}\right).$$

Thus we can bound  $\lambda_2 \leq O(1/n^2)$ . We knew this was true from the explicit formula of  $\lambda_2$  in terms of sines and cosines from Lecture 2, but this is much cleaner and more general of a result.

### 2.2 Example 2: A Complete Binary Tree

Let G be a complete binary tree on  $n = 2^h - 1$  nodes. Define the vector  $x \in \mathbb{R}^n$  to have the value 0 on the root node, -1 on all nodes in the left subtree of the root, and 1 on all nodes in the right subtree of the root.

It is easy to see that  $\sum_{i \in V} x_i = 0$ , since there are equal numbers of nodes on the left and right subtrees of the root, so  $x \perp 1$ . Calculating the Rayleigh quotient of x gives us

$$\frac{\sum_{(i,j)\in E} (x_i - x_j)^2}{\sum_{i\in V} x_i^2} = \frac{2}{n-1} = O\left(\frac{1}{n}\right).$$

Thus we get  $\lambda_2 \leq O(1/n)$ , again with little effort. It turns out in this case that our approximation is correct within a constant factor, and we did not even need to diagonalize a big matrix.

# 3 Graph Cutting

The basic problem of graph cutting is to cut a given graph G into two pieces such that both are "pretty big". Graph cutting has many applications in computer science and computing, e.g. for parallel processing, divide-and-conquer algorithms, or clustering. In each application, we want to divide the problem into smaller pieces so as to optimize some measure of efficiency, depending on the specific problems.

# 3.1 How Do We Cut Graphs?

The first question to ask about graph cutting is what we want to optimize when we are cutting a graph. Before attempting to answer this question, we introduce several notations. Let G = (V, E) be a graph. Given a set  $S \subseteq V$  of vertices of G, let  $\bar{S} = V \setminus S$  be the complement of S in V. Let |S| and  $|\bar{S}|$  denote the number of vertices in S and  $\bar{S}$ , respectively. Finally, let e(S) denote the number of edges between S and  $\bar{S}$ . Note that  $e(S) = e(\bar{S})$ .

Now we consider some possible answers to our earlier question.

Attempt 1: Min-cut. Divide the vertex set V into two parts S and  $\bar{S}$  to minimize e(S). This approach is motivated by the intuition that to get a good cut, we do not want to break too many edges. However, this approach alone is not sufficient, as Figure 1(a) demonstrates. In this example, we ideally want to cut the graph across the two edges in the middle, but the min-cut criterion would result in a cut across the one edge on the right.

Attempt 2: Approximate bisection. Divide the vertex set V into two parts S and  $\bar{S}$ , such that |S| and  $|\bar{S}|$  are approximately n/2 (or at least n/3). This criterion would take care of the problem mentioned in Figure 1(a), but it is also not free of problems, as Figure 1(b) shows. In this example, we ideally want to cut the graph across the one edge in the middle that separates the two clusters. However, the approximate bisection criterion would force us to make a cut across the dense graph on the left.

**Figure 1**: Illustration for problems with the proposed graph cutting criteria.

Now we propose a criterion for graph cutting that balances the two approaches above.

**Definition 3 (Cut Ratio)** The cut ratio  $\phi$  of a cut  $S - \bar{S}$  is given by

$$\phi(S) = \frac{e(S)}{\min(|S|, |\bar{S}|)}.$$

The cut of minimum ratio is the cut that minimizes  $\phi(S)$ . The isoperimetric number of a graph G is the value of the minimum cut,

$$\phi(G) = \min_{S \subset V} \phi(S).$$

As we can see from the definition above, the cut ratio is trying to minimize the number of edges across the cut, while penalizing cuts with small number of vertices. This criterion turns out to be a good one, and is widely used for graph cutting in practice.

## 3.2 An Integer Program for the Cut Ratio

Now that we have a good definition of graph cutting, the question is how to find the optimal cut in a reasonable time. It turns out that we can cast the problem of finding cut of minimum ratio as an integer program as follows.

Associate every cut  $S - \bar{S}$  with a vector  $x \in \{-1, 1\}^n$ , where

$$x_i = \begin{cases} 1, & \text{if } i \in S, \text{ and} \\ -1, & \text{if } i \in \bar{S}. \end{cases}$$

Then it is easy to see that we can write

$$e(S) = \frac{1}{4} \sum_{(i,j) \in E} (x_i - x_j)^2.$$

For a boolean statement A, let [A] denote the characteristic function on A, so [A] = 1 if A is true, and [A] = 0 if A is false. Then we also have

$$|S| \cdot |\bar{S}| = \left(\sum_{i \in V} [i \in S]\right) \left(\sum_{j \in V} [j \in \bar{S}]\right) = \sum_{i,j \in V} [i \in S, j \in \bar{S}] = \frac{1}{2} \sum_{i,j \in V} [x_i \neq x_j] = \frac{1}{4} \sum_{i < j} (x_i - x_j)^2.$$

Combining the two computations above,

$$\min_{x \in \{-1,1\}^n} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i < j} (x_i - x_j)^2} = \min_{S \subseteq V} \frac{e(S)}{|S| \cdot |\bar{S}|}.$$

Now note that if  $|V| = |S| + |\bar{S}| = n$ , then

$$\frac{n}{2}\min(|S|,|\bar{S}|) \leq |S| \cdot |\bar{S}| \leq n\min(|S|,|\bar{S}|),$$

so we get

$$\frac{1}{n}\phi(G) = \min_{S \subseteq V} \frac{e(S)}{n \min(|S|, |\bar{S}|)} \le \min_{x \in \{-1, 1\}^n} \frac{\sum_{(i, j) \in E} (x_i - x_j)^2}{\sum_{i < j} (x_i - x_j)^2} \le \min_{S \subseteq V} \frac{2e(S)}{n \min(|S|, |\bar{S}|)} = \frac{2}{n}\phi(G).$$

Therefore, solving the integer program

$$\min_{x \in \{-1,1\}^n} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i < j} (x_i - x_j)^2}$$

allows us to approximate  $\phi(G)$  within a factor of 2. The bad news is that it is NP-hard to solve this program. However, if we remove the  $x \in \{-1,1\}^n$  constraint, we can actually solve the program. Note that removing the constraint  $x \in \{-1,1\}^n$  is actually the same as saying that  $x \in [-1,1]^n$ , since we can scale x without changing the value of the objective function.

#### 3.3 Interlude on Relaxations

The idea to drop the constraint  $x \in \{-1,1\}^n$  mentioned in the previous section is actually a recurring technique in algorithms, so it is worthwhile to give a more general explanation of this relaxation technique. A common setup in approximation algorithms is as follows: we want to solve an NP-hard question which takes the form of minimizing f(x) subject to the constraint  $x \in C$ . Instead, we minimize f(x) subject to a weaker constraint  $x \in C' \supseteq C$  (see Figure 2 for an illustration). Let p and q be the points that minimize f in C and C', respectively. Since  $C \subseteq C'$ , we know that  $f(q) \leq f(p)$ .

**Figure 2**: Illustration of the relaxation technique for approximation algorithms.

For this relaxation to be useful, we have to show how to "round" q to a feasible point  $q' \in C$ , and prove  $f(q') \leq \gamma f(q)$  for some constant  $\gamma \geq 1$ . This implies  $f(q') \leq \gamma f(q) \leq \gamma f(p)$ , so this process gives us a  $\gamma$ -approximation.

# Solving the Relaxed Program

Going back to our integer program to find the cut of minimum ratio, now consider the following relaxed program,

$$\min_{x \in \mathbb{R}^n} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i < j} (x_i - x_j)^2}.$$

Since the value of the objective function only depends on the differences  $x_i - x_j$ , we can translate  $x \in \mathbb{R}^n$ such that  $x \perp \mathbf{1}$ , i.e.  $\sum_{i=1}^{n} x_i = 0$ . Then observe that

$$\sum_{i < j} (x_i - x_j)^2 = n \sum_{i=1}^n x_i^2,$$

which can be obtained either by expanding the summation directly, or by noting that x is an eigenvector of the Laplacian of the complete graph  $K_n$  with eigenvalue n (as we saw in Lecture 2). Therefore, using the Rayleigh quotient,

$$\min_{x \in \mathbb{R}^n} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{\sum_{i < j} (x_i - x_j)^2} = \min_{\substack{x \in \mathbb{R}^n \\ x = 1}} \frac{\sum_{(i,j) \in E} (x_i - x_j)^2}{n \sum_{i=1}^n x_i^2} = \frac{\lambda_2}{n}.$$

Putting all the pieces together, we get

$$\phi(G) = \min_{S \subseteq V} \frac{e(S)}{\min(|S|, |\bar{S}|)}$$

$$\geq \frac{n}{2} \min_{S \subseteq V} \frac{e(S)}{|S| \cdot |\bar{S}|}$$

$$= \frac{n}{2} \min_{x \in \{-1, 1\}^n} \frac{\sum_{(i, j) \in E} (x_i - x_j)^2}{\sum_{i < j} (x_i - x_j)^2}$$

$$\geq \frac{n}{2} \min_{x \in \mathbb{R}^n} \frac{\sum_{(i, j) \in E} (x_i - x_j)^2}{\sum_{i < j} (x_i - x_j)^2}$$

$$= \frac{n}{2} \min_{x \in \mathbb{R}^n} \frac{\sum_{(i, j) \in E} (x_i - x_j)^2}{n \sum_{i=1}^n x_i^2}$$

$$= \frac{\lambda_2}{2}.$$

# 4 Cheeger's Inequality

In the previous section, we obtained the bound  $\phi(G) \geq \lambda_2/2$ , but what about the other direction? For that, we would need a rounding method, which is a way of getting a cut from  $\lambda_2$  and  $v_2$ , and an upper bound on how much ithe rounding increases the cut ratio that we are trying to minimize. In the next section, we will see how to construct a cut from  $\lambda_2$  and  $v_2$  that gives us the following bound, which is Cheeger's Inequality.

Theorem 4 (Cheeger's Inequality) Given a graph G,

$$\frac{\phi(G)^2}{2d_{\max}} \le \lambda_2 \le 2\phi(G),$$

where  $d_{\max}$  is the maximum degree in G.

As a side note, the  $d_{max}$  disappears from the formula if we use the normalized Laplacian in our calculations, but the proof is messier and is not fundamentally any different from the proof using the regular Laplacian.

The lower bound of  $\phi(G)^2/2d_{max}$  in Cheeger's Inequality is the best we can do to bound  $\lambda_2$ . The square factor  $\phi(G)^2$  is unfortunate, but if it were within a constant factor of  $\phi(G)$ , we would be able to find a constant approximation of an NP-hard problem. Also, if we look at the examples of the path graph and the complete binary tree, their isoperimetric numbers are the same since we can cut exactly one edge in the middle of the graph and divide the graphs into two asymptotically equal-sized pieces for a value of O(1/n). However, the two graphs have different upper bounds for  $\lambda_2$ ,  $O(1/n^2)$  and O(1/n) respectively, which demonstrate that both the lower and upper bounds of  $\lambda_2$  in Cheeger's inequality are tight (to a constant factor).

### 4.1 How to Get a Cut from $v_2$ and $\lambda_2$

Let  $x \in \mathbb{R}^n$  such that  $x \perp 1$ . We will use x as a map from the vertices V to  $\mathbb{R}$ . Cutting  $\mathbb{R}$  would thus give a partition of V as follows: order the vertices such that  $x_1 \leq x_2 \leq \ldots \leq x_n$ , and the cut will be defined by the set  $S = \{1, \ldots, k\}$  for some value of k. The value of k cannot be known a priori since the best cut depends on the graph. In practice, an algorithm would have to try all values of k to actually find the optimal cut after embedding the graph to the real line.

We will actually prove something slightly stronger than Cheeger's Inequality:

**Theorem 5** For any  $x \perp 1$ ,  $x_1 \leq x_2 \leq \ldots \leq x_n$ , there is some i for which

$$\frac{x^T L x}{x^T x} \ge \frac{\phi(\{1,\dots,i\})^2}{2d_{max}}.$$

This is great because it not only implies Cheeger's inequality by taking  $x = v_2$ , but it also gives an actual cut. It also works even if we have not calculated the exact values for  $\lambda_2$  and  $v_2$ ; we just have to get a good approximation of  $v_2$  and we can still get a cut.

# 4.2 Proof of Cheeger's Inequality

### 4.2.1 Step 1: Preprocessing

First, we are going to do some preprocessing. This step does not reduce the generality of the proof much, but it will make the actual proof cleaner.

- For simplicity, suppose n is odd.
- Let m = (n+1)/2.
- Define the vector y by  $y_i = x_i x_m$ .

We can observe that  $y_m = 0$ , half of the vertices are to the left of  $y_m$ , and the other half are to the right of  $y_m$ .

Claim 6

$$\frac{x^T L x}{x^T x} \ge \frac{y^T L y}{y^T y}$$

**Proof** First, the numerators are equal by the operation of the Laplacian,

$$x^{T}Lx = \sum_{(i,j)\in E} (x_{i} - x_{j})^{2} = \sum_{(i,j)\in E} ((y_{i} + x_{m}) - (y_{j} + x_{m}))^{2} = \sum_{(i,j)\in E} (y_{i} - y_{j})^{2} = y^{T}Ly.$$

Next, since  $x \perp 1$ ,

$$y^T y = (x + x_m \mathbf{1})^T (x + x_m \mathbf{1}) = x^T x + 2x_m (x^T \mathbf{1}) + x_m^2 (\mathbf{1}^T \mathbf{1}) = x^T x + nx_m^2 \ge x^T x.$$

Putting together the two computations above yields the desired inequality.

### 4.2.2 Step 2: A Little More Preprocessing

We do not want edges crossing  $y_m = 0$  (because we will later consider the positive and negative vertices separately), so we replace any edge (i, j) with two edges (i, m) and (m, j). Call this new edge set E'.

Claim 7

$$\frac{\sum_{(i,j) \in E} (y_i - y_j)^2}{\sum_{i \in V} y_i^2} \ge \frac{\sum_{(i,j) \in E'} (y_i - y_j)^2}{\sum_{i \in V} y_i^2}.$$

**Proof** The only difference in the numerator comes from the edges (i, j) that we split into (i, m) and (m, j). In that case, it is easy to see that (also noting that  $y_m = 0$ )

$$(y_j - y_i)^2 \ge (y_j - y_m)^2 + (y_m - y_i)^2.$$

### 4.2.3 Step 3: Breaking the Sum in Half

We would like to break the summations in half so that we do not have to deal with separate cases with positive and negative numbers. Let  $E'_{-}$  be the edges (i,j) with  $i,j \leq m$ , and let  $E'_{+}$  be the edges (i,j) with  $i,j \geq m$ . We then have

$$\frac{\sum_{(i,j)\in E'}(y_i-y_j)^2}{\sum_i y_i^2} = \frac{\sum_{(i,j)\in E'_-}(y_i-y_j)^2 + \sum_{(i,j)\in E'_+}(y_i-y_j)^2}{\sum_{i=1}^m y_i^2 + \sum_{i=m}^n y_i^2}.$$

Note that  $y_m$  appears twice in the summation on the denominator, which is fine since  $y_m = 0$ . We also know that for any a, b, c, d > 0,

$$\frac{a+b}{c+d} \ge \min\left(\frac{a}{c}, \frac{b}{d}\right),\,$$

so it is enough to bound

$$\frac{\sum_{(i,j)\in E'_{-}}(y_i - y_j)^2}{\sum_{i=1}^{m}y_i^2} \quad \text{and} \quad \frac{\sum_{(i,j)\in E'_{+}}(y_i - y_j)^2}{\sum_{i=m}^{n}y_i^2}.$$

Since the two values are essentially the same, we will focus only on the first one.

### 4.2.4 The Main Lemma

Let  $C_i$  be the number of edges crossing the point  $x_i$ , i.e. the number of edges in the cut if we were to take  $S = \{1, \ldots, i\}$ . Recall that

$$\phi = \phi(G) = \min_{S \subseteq V} \frac{e(S)}{\min(|S|, |\bar{S}|)},$$

so by taking  $S = \{1, ..., i\}$ , we get  $C_i \ge \phi i$  for  $i \le n/2$  and  $C_i \ge \phi (n-i)$  for  $i \ge n/2$ .

The main lemma we use to prove Cheeger's Inequality is as follows.

Lemma 8 (Summation by Parts) For any  $z_1 \leq \ldots \leq z_m = 0$ ,

$$\sum_{(i,j)\in E'_{-}} |z_i - z_j| \ge \phi \sum_{i=1}^{m} |z_i|.$$

**Proof** For each  $(i, j) \in E'_{-}$  with i < j, write

$$|z_i - z_j| = z_j - z_i = (z_{i+1} - z_i) + (z_{i+2} - z_{i+1}) + \dots + (z_j - z_{j-1}) = \sum_{k=j}^{j-1} (z_{k+1} - z_k).$$

Summing over  $(i,j) \in E'_{-}$ , we observe that each term  $z_{k+1} - z_k$  appears exactly  $C_k$  times. Therefore,

$$\sum_{(i,j)\in E'_{-}} |z_i - z_j| = \sum_{k=1}^{m-1} C_k (z_{k+1} - z_k) \ge \phi \sum_{k=1}^{m-1} k (z_{k+1} - z_k).$$

Note that  $z_i \leq z_m = 0$ , so  $|z_i| = -z_i$  for  $1 \leq i \leq m$ . Then we can evaluate the last summation above as

$$\sum_{(i,j)\in E'_{-}} |z_{i}-z_{j}| \ge \phi \sum_{k=1}^{m-1} k(z_{k+1}-z_{k})$$

$$= \phi ((z_{2}-z_{1}) + 2(z_{3}-z_{2}) + 3(z_{4}-z_{3}) + \dots + (m-1)(z_{m}-z_{m-1}))$$

$$= \phi (-z_{1}-z_{2}-\dots-z_{m-1}+(m-1)z_{m})$$

$$= \phi \sum_{i=1}^{m} |z_{i}|.$$

### 4.2.5 Using the Main Lemma to Prove Cheeger's Inequality

Now we can finally prove Cheeger's inequality.

**Proof of Cheeger's Inequality:** This proof has five main steps.

- 1. First, we normalize y such that  $\sum_{i=1}^{m} y_i^2 = 1$ .
- 2. Next, this is perhaps a somewhat nonintuitive step, but we want to get squares into our expression, so we apply the main lemma (Lemma 8) to a new vector z with  $z_i = -y_i^2$ . We now have

$$\sum_{(i,j)\in E'_{-}} |y_i^2 - y_j^2| \ge \phi \sum_{i=1}^m |y_i^2| = \phi.$$

3. Next, we want something that looks like  $(y_i - y_j)^2$  instead of  $y_i^2 - y_j^2$ , so we are going to use the Cauchy-Schwarz inequality.

$$\sum_{(i,j)\in E'_{-}} |y_i^2 - y_j^2| = \sum_{(i,j)\in E'_{-}} |y_i - y_j| \cdot |y_i + y_j| \le \left(\sum_{(i,j)\in E'_{-}} (y_i - y_j)^2\right)^{1/2} \left(\sum_{(i,j)\in E'_{-}} (y_i + y_j)^2\right)^{1/2}.$$

4. We want to get rid of the  $(y_i + y_j)^2$  part, so we bound it and observe that the maximum number of times any  $y_i^2$  can show up in the summation over the edges is the the maximum degree of any vertex.

$$\sum_{(i,j)\in E'} (y_i + y_j)^2 \le 2 \sum_{(i,j)\in E'} (y_i^2 + y_j^2) \le 2 \sum_{i=1}^m d_{max} \cdot y_i^2 \le 2d_{max}.$$

5. Putting it all together, we get

$$\frac{\sum_{(i,j) \in E'_{-}} (y_i - y_j)^2}{\sum_{i=1}^m y_i^2} \ge \frac{\left(\sum_{(i,j) \in E'_{-}} |y_i^2 - y_j^2|\right)^2}{\sum_{(i,j) \in E'} (y_i + y_j)^2} \ge \frac{\phi^2}{2d_{max}}.$$

Similarly, we can also show that

$$\frac{\sum_{(i,j)\in E'_{+}}(y_{i}-y_{j})^{2}}{\sum_{i=m}^{n}y_{i}^{2}} \ge \frac{\phi^{2}}{2d_{max}}.$$

Therefore,

$$\frac{x^T L x}{x^T x} \ge \frac{y^T L y}{y^T y} \ge \min \left\{ \frac{\sum_{(i,j) \in E'_-} (y_i - y_j)^2}{\sum_{i=1}^m y_i^2}, \frac{\sum_{(i,j) \in E'_+} (y_i - y_j)^2}{\sum_{i=m}^n y_i^2} \right\} \ge \frac{\phi^2}{2d_{max}}.$$

### 4.2.6 So who is Cheeger anyway?

Jeff Cheeger is a differential geometer. His inequality makes a lot more sense in the continuous world, and his motivation was in differential geometry. This was part of his PhD thesis, and he was actually investigating heat kernels on smooth manifolds. A heat kernel can also be thought of as a point of heat in space, and the question is the speed at which the heat spreads. It can also be thought of as the mixing time of a random walk, which will be discussed in future lectures.

| MIT C   | penCourseWare |
|---------|---------------|
| http:// | ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

#### 18.409 An Algorithmist's Toolkit

September 22, 2009

### Lecture 4

Lecturer: Jonathan Kelner

Scribe: Dan Iancu (2009)

## 1 Random walks

Let G = (V, E) be an undirected graph. Consider the random process that starts from some vertex  $v \in V(G)$ , and repeatedly moves to a neighbor of the current vertex chosen uniformly at random.

For  $t \geq 0$ , and for  $u \in V(G)$ , let  $p_t(u)$  denote the probability that you are at vertex u at time t. We can think of  $p_t$  as a vector in  $\mathbb{R}^n$ . Clearly,

$$\sum_{u \in V(G)} p_t(u) = 1$$

Observe that you are at a vertex u at time t, then at time t+1 you are at each neighbor v of u with probability 1/d(u), where d(u) denotes the degree of u. So,

$$\begin{array}{ll} p_{t+1}(v) & = & \displaystyle\sum_{(u,v)\in E(G)} \mathbf{Pr}[\mathrm{at}\ u\ \mathrm{at\ time}\ t] \cdot \mathbf{Pr}[\mathrm{`go\ to}\ v\ \mathrm{at\ time}\ t+1'\ \mathrm{given\ `at}\ u\ \mathrm{at\ time}\ t'] \\ & = & \displaystyle\sum_{(u,v)\in E(G)} p_t(u) \cdot \frac{1}{d(u)} \end{array}$$

We can write this using matrix notation as follows. Define the matrix  $W = W_G$ :

$$[W_G]_{i,j} = \begin{cases} \frac{1}{d(j)} & \text{if } (i,j) \in E(G) \\ 0 & \text{otherwise} \end{cases}$$

Note that  $[W_G]_{i,j}$  is the probability of going from j to i. We have

$$W_G = A \cdot D^{-1}$$
,

where A is the adjacency matrix of G, and D is the diagonal matrix with  $[D]_{i,i}$  the degree of the i-th vertex of G.

# 2 Stationary distribution

We define a probability vector  $\pi$  which corresponds to the stationary distribution of the random walk. Let

$$\pi(u) = \frac{d(u)}{\sum_{v \in V(G)} d(v)}.$$

Claim 1  $\pi$  is a probability distribution.

**Proof** We have

$$\sum_{u \in V(G)} \pi(i) = \sum_{u \in V(G)} \frac{d(u)}{\sum_{v \in V(G)} d(v)} = \frac{\sum_{u \in V(G)} d(u)}{\sum_{v \in V(G)} d(v)} = 1.$$

We next show that, if the random walk follows the distribution  $\pi$  at time t, then it has the same distribution at time t+1. This is expressed using matrix notation in the following claim.

Claim 2  $W \cdot \pi = \pi$ .

**Proof** Let  $k \in V(G)$ . We have

$$[W \cdot \pi]_k = \sum_{i=1}^n W_{k,i} \pi_i = \frac{1}{\sum_{v \in V(G)} d(v)} \sum_{(i,k) \in E(G)} \frac{1}{d(k)} \cdot d(k) = \frac{1}{\sum_{v \in V(G)} d(v)} \cdot d(k) = \pi(k).$$

This statement is equivalent to the matrix W having eigenvalue 1, with corresponding eigenvector  $\pi$  (note that, since  $\pi$  is a multiple of the vector of node degrees,  $D \cdot \mathbf{1}$ , we could also take the latter as the eigenvector).

The natural next step at this point would be to claim that the random walk of a graph G always converges to the stationary distribution  $\pi$ . This however turns out to be false. It is easy to see that for a bipartite graph G. Consider for example the case  $G = C_6$ , the cycle on 6 vertices, and let the vertex set of G be  $V(G) = \{1, 2, \ldots, 6\}$ . Assume without loss of generality that the random walk starts at time  $t_0 = 1$  at vertex 6. Then, at time t, the current vertex is odd if and only if t is odd. Therefore, the walk does not converge to any distribution.

# 3 Lazy Random Walks

There is an easy way to fix the above periodicity problem. We introduce a modified version of the original walk, which we call  $lazy \ random \ walk$ . In a lazy random walk at time t:

- we take a step of the original random walk with probability 1/2,
- we stay at the current vertex with probability 1/2.

We can show that the above modification breaks the periodicity of the random walk. The transition probabilities are encoded in the following matrix:

$$W' = (W + I)/2 = (I + A \cdot D^{-1})/2,$$

where I denotes the identity matrix.

The fact that W and W' are not symmetric matrices makes their analysis complicated. We will thus define new matrices. The *normalized walk matrix* is defined as

$$N = D^{-1/2} \cdot W \cdot D^{1/2} = D^{-1/2} \cdot A \cdot D^{-1/2}$$

The normalized lazy walk matrix is defined as

$$N' = D^{-1/2} \cdot W' \cdot D^{1/2} = (I + D^{-1/2} \cdot A \cdot D^{-1/2})/2.$$

**Claim 3** The matrices N and W have the same eigenvalues and related eigenvectors.

**Proof** Suppose that v is an eigenvector of N, with eigenvalue  $\lambda$ . Let  $q = D^{1/2} \cdot v$ . Then,

$$N \cdot v = \lambda \cdot v = D^{-1/2} \cdot W \cdot D^{1/2} \cdot v = D^{-1/2} \cdot W \cdot q.$$

Multiplying by  $D^{1/2}$  on the left we obtain

$$W \cdot q = \lambda \cdot D^{1/2} \cdot v = \lambda \cdot q.$$

Therefore, q is an eigenvector of W with eigenvalue  $\lambda$ .

Observe that, by Claim 2, W has eigenvector  $D \cdot \mathbf{1}$ , with eigenvalue 1. Therefore, by Claim 3, the normalized walk matrix N has eigenvector  $D^{1/2} \cdot \mathbf{1}$ , with eigenvalue 1.

# 4 Connections to Laplacians

We've used the Laplacian L. The normalized Laplacian  $\mathcal{L}$  is defined as

$$\mathcal{L} = D^{-1/2} \cdot L \cdot D^{-1/2}.$$

Claim 4  $N = I - \mathcal{L}$ .

Therefore, the eigenvalues of N are given by 1 – (eigenvalues of  $\mathcal{L}$ ). So, it makes sense to order them in the opposite way

$$1 = \mu_1 \ge \mu_2 \ge \ldots \ge \mu_n$$

We can now translate our theorems about the eigenvalues of Laplacians to theorems about  $\mu_i$ s. We have

- For each  $i, \mu_i \in [-1, 1]$ .
- If G is connected, then  $\mu_2 < 1$ .
- The -1 eigenvalues occur only for bipartite graphs.

Let  $\mu'_i$  be the eigenvalues of N'. Then

- For each  $i, \mu'_i \in [0, 1]$ .
- If G is connected, then  $\mu'_2 < 1$ .

# 5 $\ell_2$ Convergence

Define the spectral gap to be

$$\lambda := 1 - \mu_2'$$
.

For probability distributions p, q, we define their  $\ell_2$  distance to be

$$||p - q||_2 = \sqrt{\sum_i (p(i) - q(i))^2}.$$

The following theorem gives a bound on the rate of convergence of the lazy random walk to the stationary distribution  $\pi$ .

**Theorem 5** Let  $p_0$  be an arbitrary initial distribution, and  $p_t$  be the distribution after t steps of the lazy random walk. Then,

$$||p_t - \pi||_2 \le (1 - \lambda)^t \cdot \sqrt{\frac{\max_x d(x)}{\min_y d(y)}}.$$

**Proof** [Proof for regular graphs] Observe that for a matrix  $M = Q^{-1} \cdot \Lambda \cdot Q$ , we have  $M^k = Q^{-1} \cdot \Lambda^k \cdot Q$ . Thus, for an eigenvector v of M,  $M^k \cdot v = \lambda^k \cdot v$ .

Recall that  $N' = (I + D^{-1/2} \cdot A \cdot D^{-1/2})/2$ . Since G is regular,  $D = d \cdot I$ , for some integer d > 0. Thus,

$$N' = I + \frac{1}{d}A$$

and the stationary distribution is simply the uniform distribution on V(G)

$$\pi = \frac{1}{n} \cdot \mathbf{1}.$$

Let  $c_i = v_i^T p_0$ , where  $v_i$  denotes the eigenvector corresponding to the *i*-th eigenvalue. We have

$$N'^{k} \cdot p_{0} = \sum_{i=1}^{n} c_{i} \cdot \mu_{i}^{k} \cdot v_{i} = c_{1} \cdot v_{1} + \sum_{i=2}^{n} c_{i} \cdot \mu_{i}^{k} \cdot v_{i}$$

Since  $c_1 = v_1^T p_0 = 1/n$ , it follows that

$$||p_k - \pi||_2 = ||\sum_{i=2}^n c_i \cdot \mu_i^k \cdot v_i||_2 = \sqrt{\sum_{i=2}^n c_i^2 \cdot \mu_i^{2k}} \le \mu_2^k \sqrt{\sum_{i=2}^n c_i^2}$$

$$\le \mu_2^k \sum_{i=1}^n (v_i^T p_0)^2 \le \mu_2^k = (1 - \lambda)^k.$$

Using a similar argument, we can also show an analogous bound for  $\ell_{\infty}$  convergence.

**Theorem 6** For any vertex  $v \in V(G)$ ,

$$|p_t(v) - \pi(v)| \le (1 - \lambda)^t \cdot \sqrt{\frac{d(v)}{\min_y d(y)}}$$

## 6 Conductance

Cheeger's inequality carries over too, by replacing the isoperimetric number by a new parameter, which we call  $conductance \Phi$ .

Definition 7 (Conductance) For  $S \subseteq V(G)$ , let

$$\Phi(S) = \frac{e(S)}{\min\left(\sum_{v \in S} d(v), \sum_{v \in \bar{S}} d(v)\right)}.$$

We define the conductance to be

$$\Phi(G) = \min_{S \subset V} \Phi(S).$$

Using the above definition, Cheeger's inequality now becomes:

$$\Theta(1) \cdot \Phi^2(G) \le 1 - \mu_2' \le \Theta(1) \cdot \Phi(G).$$

The parameter  $\Phi(G)$  is related to the rate of convergence to the stationary distribution. In particular, bounds on  $\Phi(G)$  let us prove that a walk mixes quickly.

The intuitive interpretation of the connection between conductance and the rate of convergence is as follows. If a graph has high conductance, it is well-connected. Therefore, a large amount of probability mass can very quickly move from one part of the graph to another.

#### 7 Introduction to Monte Carlo methods

Assume that we want to estimate  $\pi = 3.1415...$  by throwing darts in the following dartboard:

Assume that the square corresponds to  $[-1,1] \times [-1,1]$ . If you pick a point in the square uniformly at random, the probability that you pick one inside the circle is equal to  $\pi/4$ . Suppose that you pick n points in  $[-1,1] \times [-1,1]$ , uniformly at random. Then,

 $\mathbf{E}[\text{number of points inside circle}] = n \cdot \pi/4$ 

So, you can return the estimate

 $\hat{\pi} = \text{(number of points inside circle)} \cdot 4/n.$ 

A natural question is how close this estimate would be to the right answer.

In order to answer the above question, we will introduce the Chernoff bound. Suppose we have a random variable  $r \in \{0,1\}$ , such that  $\mathbf{Pr}[r=1] = p$ , and  $\mathbf{Pr}[r=0] = 1 - p$ . Assume that we draw n independent samples  $r_1, \ldots, r_n$ , and let  $R = \sum_i r_i$ . By the linearity of expectation, we have

$$\mathbf{E}[R] = \mathbf{E}[\sum_{i} r_i] = \sum_{i} \mathbf{E}[r_i] = n \cdot p$$

We will say that R  $\epsilon$ -approximates  $\mathbf{E}[R]$  if

$$(1 - \epsilon)\mathbf{E}[R] \le R \le (1 + \epsilon)\mathbf{E}[R]$$

This is a multiplicative error measure.

Theorem 8 (One version of the Chernoff bound) The probability that R fails to  $\epsilon$ -approximate  $\mathbf{E}[R]$  is

$$\mathbf{Pr}\left[|R - \mathbf{E}[R]| \ge \epsilon \mathbf{E}[R]\right] \le 2e^{-np\epsilon^2/12} = 2e^{-\mathbf{E}[R]\epsilon^2/12}.$$

Some notes on the above bound:

- The bound is near tight.
- It is necessary for the trials to be independent, in order for the bound to hold.
- It provides a multiplicative, but not an additive error guarantee.
- For fixed  $\epsilon$ , it falls off exponentially in n. So, if we have failure probability 1/2, we can improve it to  $1/2^k$  by performing  $m = n \cdot k$  trails.
- $\bullet$  Therefore, smaller n requires more trials.
- If we want  $\epsilon$ -approximation with probability  $1 \delta$ , then we need

$$N \geq \Theta\left(\frac{\log(1/\delta)}{p\epsilon^2}\right).$$

That is, we need enough trials to get  $\Theta(\log(1/\delta)/\epsilon^2)$  successes.

Back to the dartboard example, if we want to estimate  $\pi$  within, say, 5%, with probability at least 0.99, then we have  $\epsilon = 0.05$ ,  $\delta = 1/100$ . Therefore, we need

$$N \ge \Theta\left(\frac{\log(100)}{(\pi/4)(0.05)^2}\right)$$

Observe that it is easy to make  $\delta$  smaller, but it is harder to make  $\epsilon$  smaller.

If we are bad darts, then we run into trouble. This happens if we have a big dartboard, and a small circle.

In particular, if p is exponentially small, then we need exponentially many trials to expect a constant number of successes.

We can also run into trouble if it is hard to throw darts at all. That is, if it is hard to draw samples uniformly at random from the ambient space. We will develop some techniques for fixing the above problems in certain scenarios.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 18.409 An Algorithmist's Toolkit | September 24, 2009      |
|----------------------------------|-------------------------|
| Lecture 5                        |                         |
| Lastymen: Longthan Kolmon        | Samiha: Chaumak Kichara |

## 1 Administrivia

Two additional resources on approximating the permanent

- Jerrum and Sinclair's original paper on the algorithm
- An excerpt from Motwani and Raghavan's Randomized Algorithms

## 2 Review of Monte Carlo Methods

We have some (usually exponentially large) set V of size Z, and we wish to know how many elements are contained in some subset S (which represents elements with some property we are interested in counting). A Monte Carlo method for approximating the size of S is to pick k elements uniformly at random from V and see how many are also contained in S. If q elements are contained in S, then return as our approximate solution Zq/k. In expectation, this is the correct answer, but how tightly the estimate is concentrated around the correct value depends on the size of  $p = \frac{|S|}{|V|}$ .

**Definition 1** An  $(\epsilon, \delta)$  approximation scheme is an algorithm for finding an approximation within a multiplicative factor of  $1 \pm \epsilon$  with probability  $1 - \delta$ .

Using the Chernoff bound, if we sample independently from a 0-1 random variable, we need to conduct

$$N \ge \Theta\left(\frac{\log \delta}{p\varepsilon^2}\right)$$

trials to achieve an  $(\epsilon, \delta)$  approximation, where  $p = \frac{|S|}{|V|}$  as before. This bound motivates the definition of a polynomial-time approximation scheme.

**Definition 2** A fully-polynomial randomized approximation scheme, or FPRAS, is an  $(\epsilon, \delta)$  approximation scheme with a runtime that is polynomial in n,  $1/\epsilon$ , and  $\log 1/\delta$ .

There are two main problems we might encounter when trying to design an FPRAS for a difficult problem. First, the S may be an exponentially small subset of V. In this case, it would take exponentially many samples from V to get  $O(\frac{\log 1/\delta}{\epsilon^2})$  successes. Second, it could be difficult to sample uniformly from a large and complicated set V. We will see ways to solve both these problems in two examples today.

# 3 DNF Counting and an Exponentially Small Target

Suppose we have n boolean variables  $x_1, x_2, \ldots x_n$ . A literal is an  $x_i$  or its negation.

**Definition 3** A formula F is in **disjunctive normal form** if it is a disjunction (OR) of conjunctive (AND) clauses:

$$F = C_1 \vee C_2 \vee \ldots \vee C_m$$

where each  $C_i$  is a clause containing the ANDs of some of the literals. For example, the formula  $F = (x_1 \wedge \overline{x_3}) \vee (x_2) \vee (x_2 \wedge \overline{x_1} \wedge x_3 \wedge x_4)$  is in disjunctive normal form.

If there are n boolean literals, then there are  $2^n$  possible assignments. Of these  $2^n$  assignments, we want to know how many of them satisfy a given DNF formula F. Unfortunately, computing the exact number of solutions to a given DNF formula is #P-Hard<sup>1</sup>. Therefore we simply wish to give an  $\varepsilon$ -approximation for the number of solutions a given DNF formula that succeeds with probability  $1 - \delta$  and runs in time polynomial in n, m,  $\log \delta$ , and  $1/\varepsilon$ .

Naïvely, one could simply try to use the Monte Carlo method outlined above to approximate the number of solutions. However the number of satisfying assignments might be exponentially small, requiring exponentially many samples to get a tight bound. For example the DNF formula  $F = (x_1 \wedge x_2 \wedge \cdots \wedge x_n)$  has only 1 solution out of  $2^n$  assignments.

## 3.1 Reducing the Sample Space

Instead of picking assignments uniformly at random and testing each clause, we will instead sample from the set of assignments that satisfy at least one clause (but not uniformly). This algorithm illustrates the general strategy of sampling only the important space.

Consider a table with assignments on one side and the clauses  $C_1, C_2, \ldots, C_m$  on the other, where each entry is 0 or 1 depending on whether the assignment satisfies the clause. Then, for each assignment, we color the entry for first clause which it satisfies yellow (if such a clause exists). We color the remaining entries satisfied clauses blue, and we set these entries to 0. See Figure 1.

Figure 1: A table of assignments versus clauses and how to color it.

We will sample uniformly from the space of blue and yellow colored entries, and then test whether we've sampled a yellow entry. We then multiply the ratio we get by the total number of blue and yellow entries, which we can easily compute.

Let clause  $C_i$  have  $k_i$  literals. Then clearly the column corresponding to  $C_i$  has  $2^{n-k_i}$  satisfying assignments (which we can easily compute). We choose which clause to sample from with probability proportional to  $2^{n-k_i}$ . Then we pick a random satisfying assignment for this clause and test whether it is the first satisfied clause in its row (a yellow entry), or if there is a satisfied clause that precedes it (a blue entry). The total size of the space we're sampling from is just  $\sum_i 2^{n-k_i}$ .

 $<sup>^{1}</sup>$ To see this, understand that the negation of a DNF formula is just a CNF formula by application of De Morgan's laws. Therefore counting solutions to a DNF formula is equivalent to counting (non-)solutions of a CNF formula, which is the canonical example of a #P-Hard problem.

Our probability of picking a yellow entry is at least 1/m, where m is the number of clauses, so we can take enough samples in polynomial time. Therefore, this algorithm is an FPRAS for counting the solutions to the DNF formula.

## 4 Approximating the Permanent of a 0-1 Matrix

**Definition 4 (Determinant)** For a given  $n \times n$  matrix M, the determinant is given by

$$det(M) = \sum_{\pi \in S_n} sgn(\pi) \prod_{i=1}^n M_{i,\pi(i)}.$$

The formula for the permanent of a matrix is largely the same, with the  $sgn(\pi)$  omitted.

**Definition 5 (Permanent)** For a given  $n \times n$  matrix M, the permanent is given by

$$per(M) = \sum_{\pi \in S_n} \prod_{i=1}^n M_{i,\pi(i)}.$$

However, while the determinant of a matrix is easily computable —  $O(n^3)$  by LU decomposition — calculating the permanent of a matrix is #P-Complete. As we will show, computing the permanent of a 0-1 matrix reduces to the problem of finding the number of perfect matchings in a bipartite graph.

## 4.1 The Permanent of a 0-1 Matrix and Perfect Matchings

Given an  $n \times n$  0-1 matrix M, we construct a subgraph G of  $K_{n,n}$ , as follows. Let the vertices on the left be  $v_1, v_2, \ldots v_n$  and let the vertices on the right be  $w_1, w_2, \ldots w_n$ . There is an edge between  $v_i$  and  $w_j$  if and only if  $M_{ij}$  is 1.

Suppose  $\sigma$  is a permutation of  $\{1, 2, \dots n\}$ . Then the product  $\prod_i M_{i\sigma(i)}$  is 1 if the pairing  $(v_i, w_{\sigma(i)})$  is a perfect matching, and 0 otherwise. Therefore, the permanent of M equals the number of perfect matchings in G. As an example, we look at a particular  $3 \times 3$  matrix and the corresponding subgraph of  $K_{3,3}$ .

$$\begin{pmatrix} 1 & 1 & 0 \\ 1 & 1 & 0 \\ 0 & 1 & 1 \end{pmatrix}$$

$$\begin{pmatrix} \boxed{1} & 1 & 0 \\ 1 & \boxed{1} & 0 \\ 0 & 1 & \boxed{1} \end{pmatrix}$$

$$\begin{pmatrix} \boxed{1} & \boxed{1} & 0 \\ 0 & 1 & \boxed{1} \end{pmatrix}$$

$$\begin{pmatrix} \boxed{1} & \boxed{1} & 0 \\ 0 & 1 & \boxed{1} \end{pmatrix}$$

Calculating the permanent of a 0-1 matrix is still #P-Complete. As we will see, there is an FPRAS for approximating it.

## 4.2 An FPRAS for Approximating the Permanent of a Dense Graph

#### 4.2.1 Some History

- 1989: Jerrum and Sinclair showed how to approximate the permanent of a dense graph (all vertices have degree at least n/2). At the time, it was not known if this result could be extended to the general case.
- 2001: Jerrum, Sinclair and Vigoda showed how to approximate the permanent of an arbitrary graph (and therefore for any matrix with nonnegative entries).

We will show today the result of 1989 for approximating the permanent of a dense graph.

#### 4.2.2 General Strategy

We can't do the naïve Monte Carlo here, since the probability of picking a perfect matching from the set of all permutations can be exponentially small. Therefore we will instead consider the set of all (possibly partial) matchings, not just perfect ones. Let  $M_k$  be the set of all partial matchings of size k. Now suppose that we had a black box that samples uniformly at random from  $M_k \cup M_{k-1}$  for any k. Then by the Monte Carlo method, by testing membership in  $M_k$ , we can determine the ratio  $r_k = \frac{|M_k|}{|M_{k-1}|}$ .

If we assume that for all k,  $1/\alpha \le r_k \le \alpha$  for some polynomially-sized  $\alpha$ , then we can estimate each  $r_k$  to within relative error  $\varepsilon = 1/n^2$  using polynomially many samples. Therefore our estimate of the number of perfect matchings is just

$$|M_n| = |M_1| \prod_{i=2}^n r_i.$$

If all of our approximations were within a  $(1\pm\frac{1}{n^2})$  factor, then our total error is at most  $(1\pm\frac{1}{n^2})^n \approx (1\pm\frac{1}{n})$ .

#### 4.2.3 Bounding the $r_k$

We first begin with a crucial lemma.

**Lemma 6** Let G be a bipartite graph of minimum degree  $\geq n/2$ . Then every partial matching in  $M_{k-1}$  has an augmenting path of length  $\leq 3$ .

**Proof** Let  $m \in M_{k-1}$  be a partial matching. Let u be an unmatched node of m. Now suppose that there are no augmenting paths of length 1 starting from u in this matching m (i.e. there is no unmatched node v such that there is an edge connecting u and v). Then by our degree conditions, u must be connected to at least n/2 of the matched nodes  $v'_i$ . Likewise if we pick an unmatched node v, if it has no augmenting paths of length 1, then it must be connected to at least n/2 of the matched nodes  $u'_j$ . But by the pigeonhole principle, there must exist i and j such that  $(u'_j, v'_i) \in m$ . The path  $(u, v'_i, u'_j, v)$  is an augmenting path of length 3.

**Theorem 7** Let G be a bipartite graph of minimum degree  $\geq n/2$ . Then  $1/n^2 \leq r_k \leq n^2$  for all k.

**Proof** We first prove that  $r_k \leq n^2$ . Consider the function  $f: M_k \to M_{k-1}$ , which maps  $m \in M_k$  to its (arbitrarily-chosen) canonical representative in  $M_{k-1}$  (i.e. uniquely choose a submatching of m). For any  $m' \in M_{k-1}$ , it must be the case that  $|f^{-1}(m')| \leq (n-k+1)^2 \leq n^2$ . Thus  $|M_k| \leq n^2 |M_{k-1}|$ .

Now we show that  $1/n^2 \le r_k$ . Fix some  $m \in M_k$ . By Lemma 6, every partial matching in  $M_{k-1}$  has an augmenting path of length  $\le 3$ . There are at most k partial matchings in  $M_{k-1}$  that can by augmented by a path of length 1 to equal m. In addition, there are at most k(k-1) matchings in  $M_{k-1}$  that can be augmented by a path of length 3 to equal m. Thus  $|M_{k-1}| \le (k + k(k-1))|M_k| = k^2|M_k| \le n^2|M_k|$ .

## 4.2.4 How to Sample (Approximately) Uniformly

We still have to show how to sample uniformly from  $C_k = M_k \cup M_{k-1}$ . We will only show how to sample approximately uniformly from this set. As it turns out, this result is good enough for our purposes.

The main idea here is to construct a graph whose vertex set is  $C_k$ , and then do a random walk on this graph which converges to the uniform distribution. We have to show two things: that the random walk converges in polynomial time, and that the stationary distribution on the graph  $C_k$  is uniform. To show that the random walk mixes quickly, we bound the conductance  $\Phi(C_k)$  by the method of canonical paths.

**Lemma 8** Let G = (V, E) be a graph for which we wish to bound  $\Phi(G)$ . For every  $v, w \in V$ , we specify a canonical path  $p_{v,w}$  from v to w. Suppose that for some constant b and for all  $e \in E$ , we have

$$\sum_{v,w\in V} \mathbf{I}[e\in p_{v,w}] \le b|V|$$

that is, at most b|V| of the canonical paths run through any given edge e. Then  $\Phi(G) \ge \frac{1}{4bd_{max}}$ , where  $d_{max}$  is the maximum degree of any vertex.

**Proof** As before, the conductance of G is defined as

$$\Phi(G) = \min_{S \subset V} \frac{e(S)}{\min\left\{\sum_{v \in S} d(v), \sum_{v \in \overline{S}} d(v)\right\}}.$$

Let  $S \subset V$ . We will show that  $\Phi(S) \geq \frac{1}{4bd_{max}}$ . Without loss of generality, assume that  $|S| \leq |V|/2$ . Then the number of canonical paths across the cut is at least  $|S||\overline{S}| \geq |S||V|/2$ . For each edge along the cut there can be no more than b|V| paths through each edge, the number of edges e(S) is at least  $\frac{|S|}{2h}$ .

In addition we can bound min  $\left\{\sum_{v\in S} d(v), \sum_{v\in \overline{S}} d(v)\right\}$  by  $|S|d_{max}$ . These bounds give us

$$\Phi(S) \geq \frac{|S|/2b}{|S|d_{max}} \geq \frac{1}{2bd_{max}}.$$

as claimed.

Since the spectral gap is at least  $\Phi(G)^2$ , as long as b and  $d_{max}$  are bounded by polynomials, a random walk on G will converge in polynomial time.

### 4.2.5 The Graph $C_k$

We will only do  $C_n$ . It should be clear later how to extend this construction for all k. Recall that our vertices correspond to matchings in  $M_n \cup M_{n-1}$ . We show how to connect our vertices with 4 different types of directed edges:

- Reduce  $(M_n \longrightarrow M_{n-1})$ : If  $m \in M_n$ , then for all  $e \in m$  define a transition to  $m' = m e \in M_{n-1}$
- Augment  $(M_{n-1} \longrightarrow M_n)$ : If  $m \in M_{n-1}$ , then for all u and v unmatched with  $(u, v) \in E$ , define a transition to  $m' = m + (u, v) \in M_n$ .
- Rotate  $(M_{n-1} \longrightarrow M_{n-1})$ : If  $m \in M_{n-1}$ , then for all  $(u, w) \in m$ ,  $(u, v) \in E$  with v unmatched, define a transition to  $m' = m + (u, v) (u, w) \in M_{n-1}$ .
- **Self-Loop**: Add enough self-loops so that you remain where you are with probability 1/2 (this gives us a uniform stationary distribution).

Note that this actually provides an undirected graph since each of these steps is reversible.

**Example 9** In Figure 2 we show  $C_2$  for the graph  $G = K_{2,2}$ . The two leftmost and two rightmost edges are **Augment/Reduce** pairs, while the others are **Rotate** transitions. The self-loops are omitted.

Figure by MIT OpenCourseWare.

**Figure 2**:  $C_2$  for the graph  $G = K_{2,2}$ .

#### 4.2.6 Canonical Paths

We still need to define the canonical paths  $p_{v,w}$  for our graph  $C_n$ . For each node  $s \in M_n \cup M_{n-1}$ , we associate with it a "partner"  $s' \in M_n$ , as follows:

- If  $s \in M_n$ , s' = s.
- If  $s \in M_{n-1}$  and has an augmenting path of length 1, augment to get s'.
- If  $s \in M_{n-1}$  and has a shortest augmenting path of length 3, augment to get s'.

Now for nodes  $s, t \in M_n \cup M_{n-1}$ , we show how to provide a canonical path  $p_{s,t}$  which consists of three segments (and each segment can be one of two different types).

- $s \longrightarrow s'$  (Type A)
- $s' \longrightarrow t'$  (Type B)
- $t' \longrightarrow t$  (Type A)

Type A paths are paths that connect a vertex  $s \in M_n \cup M_{n-1}$  to its partner  $s' \in M_n$ . Clearly, if  $s \in M_n$  then the type A path is empty. Now if  $s \in M_{n-1}$  and has an augmenting path of length 1, then our canonical path is simply the edge that performs the **Augment** operation. If  $s \in M_{n-1}$  and has a shortest augmenting path of length 3, then our canonical path is of length 2: first a **Rotate**, then an **Augment** (see Figure 3 for an example).

For a Type B path, both s' and t' are in  $M_n$ . We let  $d = s' \oplus t'$ , the symmetric difference of the two matchings (those edges which are not common to both matchings). It is clear that since s' and t' are perfect matchings, d consists of a collection of disjoint, even-length, alternating (from s' or from t') cycles of length at least 4.

Our canonical path from s' to t' will in a sense "unwind" each cycle of d individually. Now, in order for the path to be canonical, we need to provide some ordering on the cycles so that we process them in the same order each time. However, this can be done easily enough. In addition, we need to provide some ordering on the vertices in each cycle so that we unwind each cycle in the same order each time. Again, this can be done easily enough. All that remains is to describe how the cycles are unwound, which can be done much more effectively with a picture than by text. See Figures 4 and 5.

We must now bound the number of canonical paths that pass through each edge. First we consider the type A paths.

Figure by MIT OpenCourseWare.

Figure 3: Type A path of length 2.

**Lemma 10** Let  $s \in M_n$ . Then at most  $O(n^2)$  other nodes  $s' \in M_n \cup M_{n-1}$  have s as their partner.

**Proof** There are three possible types of nodes s' that have s as their partner. The first is if s' = s (hence the type A path is empty). The second can be obtained by a **Reduce** transition (the nodes s' with augmenting path of length 1). The third can be obtained by a **Reduce** and **Rotate** pair of transitions. There is only partner for the first, O(n) for the second, and  $O(n^2)$  for the third. Therefore there are at most  $O(n^2)$  nodes s' that can count s' as their partner.

Now we wish to count the number of canonical paths for type B.

**Lemma 11** Let T be a transition (i.e. an edge of  $C_n$ ). Then the number of pairs  $s, t \in M_n$  that contain T on their type B canonical path is bounded by  $|C_n|$ .

**Proof** We will provide an injection  $\sigma_T(s,t)$  that maps to matchings in  $C_n = M_n \cup M_{n-1}$ . As before, let  $d = s \oplus t$  be the symmetric difference of the two matchings s and t (recall that these can be broken down into disjoint alternating cycles  $C_1, \ldots, C_r$ ). Now we proceed along the unwinding of these cycles until we reach the transition T. At this point we stop and say that the particular matching we are at, where all cycles up to this point agree with s and all cycles after this point agree with s, is the matching that  $\sigma_T(s,t)$  maps to.

It is clear that this is fine when T is a **Reduce** or **Augment** transition, since these only occur at the beginning or end of an unwinding. The only problem is when T is a **Rotate** transition, because then there exists a vertex u (the pivot of the rotation) that is matched to a vertex v with  $(u, v) \in s$  and is also matched to a vertex w with  $(u, w) \in t$ . This is because up to T we agree with s, and after t we agree with t. But what we can do at this point is notice that one of these two edges (which we denote by  $e_{s,t}$ ) always has the start vertex of the current cycle as one of its end-points. Therefore by removing it we end up with a matching again. This is further illustrated in Figure 6.

**Theorem 12** The conductance of our graph has the following bound

$$\Phi(C_n) = \Theta\left(\frac{1}{n^6}\right)$$

Figure by MIT OpenCourseWare.

Figure 4: Unwinding a single cycle (type B path).

**Proof** By Lemma 8, we have  $\Phi(G) \geq \frac{1}{2bd_{max}}$ . As shown in Lemma 10, there are at most  $O(n^2)$  canonical paths to  $s \in M_n$  from  $M_{n-1}$ , and at most  $O(n^2)$  canonical paths from  $t \in M_n$  to  $M_{n-1}$ . In addition we showed in Lemma 11 that the number of type B paths through a particular transition T is bounded by  $|M_n \cup M_{n-1}| = |V|$  (where V is the vertex set of  $C_n$ ). Therefore as a whole, the number of canonical paths through a particular transition T is bounded by  $n^2 \times |V| \times n^2$ , which implies  $b = n^4$ .

Since  $d_{max} = O(n^2)$ , the conductance is bounded from below by  $\Theta\left(\frac{1}{n^6}\right)$  and our random walk mixes in polynomial time.

Figure by MIT OpenCourseWare.

Figure 5: Unwinding a collection of cycles (type B path).

Figure by MIT OpenCourseWare.

**Figure 6**: The encoding  $\sigma_T(s,t)$ .

| MIT C   | penCourseWare |
|---------|---------------|
| http:// | ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.409 An Algorithmist's Toolkit Lecture 6 Lecture: Jonathan Kelner Scribe: Anthony Kim(2009)

# **Topics**

- Diameters and their relationship to  $\lambda_2$
- Expanders
- Butterfly networks

# 1 Diameters and Eigenvalues

So far, every time we've dealt with eigenvalues, it's had something to do with connectivity. For example, the spectral gap can be used to approximate the quality of cuts; it also describes how well a graph can mix under a random walk. They both are saying similar things: the eigenvalue is saying how connected a graph is. A walk will mix quickly if there's a lot connected to everything else. The min-cut will likewise be large if there's a lot of connectivity.

For almost every reasonable property about a graph, there's something you can write down regarding its relation to the second eigenvalue of the Laplacian. Today, we're going to show the relation between  $\lambda_2$  and the diameter of a graph.

**Definition 1** The diameter,  $\delta$ , is the longest, shortest path between any two vertices of a graph. In other words, we can define the distance between two vertices u and v in G as the shortest path connecting the two. The diameter of G is the largest distance between any two vertices in G.

It's not immediately clear why the diameter should be related to  $\lambda_2$ ; the following provides intuition<sup>1</sup>:

- 1. Well-connected graphs have big  $\lambda_2$
- 2. Well-connected graphs have a small  $\delta$
- 3. So, graphs with big  $\lambda_2$  should have small  $\delta$

Before proceeding, we'll be making the following assumption:

**Assumption 2** G is a d-regular graph (this is for simplicity and not really a limiting assumption).

We'll also be utilizing lazy random walks in our investigation. As a reminder,

**Definition 3** A lazy random walk is simply a random walk along a graph with self loops added in:

$$M = \underbrace{\frac{A}{2d}}_{Random \ Walk} + \underbrace{\frac{I}{2}}_{Self-loops} \tag{1}$$

where A is the graph's adjacency matrix and I is the identity matrix.

Since we're using adjacency matrices, the interesting eigenvalues will be close to 1. So, let  $\mu_2$  be the second largest eigenvalue of M and  $\lambda$  be the gap (i.e.,  $\lambda = 1 - \mu_2$ ).

<sup>&</sup>lt;sup>1</sup>Note, however, that this is not a proper syllogism

#### 1.1 A First Bound

Claim 4 For any G,

$$\delta \le \frac{\ln(n)}{\lambda} \tag{2}$$

where  $\delta$  is the diameter of G, n is the number of vertices in the graph, and  $\lambda = 1 - \mu_2$ , where  $\mu_2$  is the second largest eigenvalue of the M associated with G.

Claim 4 means that  $\lambda$ , up to a logarithmic factor, really does provide a direct bound on the diameter of the graph. For most graphs, this isn't very tight, but it's a good place to start. So, why is it true?

**Proof** We will use random walks to prove claim 4. Let u and v be vertices that are as far as possible from one another. Start a random walk at u and let  $p_t(v)$  be the probability of a walk being at vertex v at time t. If  $p_t(v) > 0$ , then  $\delta \le t$ . Intuitively, this means that if we start at u and, after t time steps, there is some probability of ending up at v (the farthest vertex from u), then there must be a path of length t between the two. If there wasn't,  $p_t(v)$  would be 0.

Recalling that the stationary distribution is  $\pi(v) = 1/n$  for regular graphs, we can equivalently state that if  $|p_t(v) - \pi(v)| < \frac{1}{n}$ , then  $\delta \le t$ . Why? Because if  $|p_t(v) - \pi(v)| < \frac{1}{n}$ , then  $p_t(v) > 0$ , implying  $\delta \le t$ .

Recall from our earlier lecture on random walks that

$$|p_t(v) - \pi(v)| < (1 - \lambda)^t \sqrt{\frac{d(v)}{\min_y d(y)}} = (1 - \lambda)^t$$

Since G is regular, d(v) = d for all vertices (allowing the last equality above). We'll now look at what happens when we set  $t = \frac{\ln n}{\lambda}$ :

$$(1-\lambda)^t = (1-\lambda)^{\frac{\ln n}{\lambda}} < \left(\frac{1}{e}\right)^{\ln n} = \frac{1}{n}$$

With the inequality coming from the fact that  $(1-\lambda)^{1/\lambda} < \frac{1}{e}$  for all  $\lambda > 0$ . Thus, for  $t = \frac{\ln n}{\lambda}$ , we have that  $|p_t(v) - \pi(v)| < \frac{1}{n}$ , and therefore,  $\delta \le t = \frac{\ln n}{\lambda}$ .

## 1.2 A better bound

As stated earlier, bounding  $\delta$  by  $\frac{1}{n}$  is not that great. So, can we do better? Yes. And we do so by using an important trick that frequently comes up. First, note that if the  $(u,v)^{\text{th}}$  entry of  $A^k$  is non-zero, then there's a path of at most length k from u to v. Replacing A with M doesn't change this (it just makes the non-zero entries smaller). If  $e_u$  and  $e_v$  are basis vectors, then

$$|p_k(v) - \pi(v)| = |e_v^T M^k e_u - \frac{1}{n}| < \frac{1}{n}$$

which would imply  $\delta \leq k$ . Let's then let p(x) be a polynomial of degree k:

$$p(x) = \sum_{j=1}^{k} c_j x^j$$

Note that we can also interpret M as a variable and apply p to it as follows:

$$p(M) = \sum_{j=1}^{k} c_j M^j$$

If p(M) has no zero entries, then  $\delta \leq k$ . Why? Because all non-zero elements of M indicate all vertices that can be reached in one step,  $M^2$  is all vertices that can be reached in two steps, and so on. Thus,

for any non-zero entry (u, v) in p(M), there must have been a non-zero element in  $M^j$  for  $0 < j \le k$ , implying the existence of a path from u to v of at most length k. If this is true for all entries in p(M), then a path of at most length k exists from any vertex to any other vertex, which means the diameter is at most k.

**Claim 5** Suppose p has degree k, p(1) = 1, and  $|p(\mu_i)| < \frac{1}{n}$  for all  $i \ge 2$ , then

$$\delta \le k \tag{3}$$

**Proof** For this proof, it is sufficient to show that every entry in p(M) is non-zero. First, recall that we can write down any matrix, M, as the following:

$$M = \sum_{i} \mu_i v_i v_i^T$$

where  $\mu_i$  and  $v_i$  are the *i*-th eigenvalue and eigenvector, respectively. Since

$$M^k = \sum_i \mu_i^k v_i v_i^T$$

we can write

$$p(M) = \sum_{j=0}^{k} c_j M^j = \sum_{j=0}^{k} c_j \sum_i \mu_i^j v_i v_i^T = \sum_i \left( \sum_{j=0}^{k} c_j \mu_i^j \right) v_i v_i^T = \sum_i p(\mu_i) v_i v_i^T$$

Therefore, we can write the  $(a,b)^{th}$  entry of p(M) as follows

$$e_{a}^{T}p(M)e_{b} = e_{a}^{T} \left(\sum_{i} p(\mu_{i})v_{i}v_{i}^{T}\right)e_{b}$$

$$= \sum_{i} p(\mu_{i})(e_{a}^{T}v_{i})(v_{i}^{T}e_{b})$$

$$= \sum_{i} p(\mu_{i})v_{i}(a)v_{i}(b)$$

$$= \frac{1}{n} + \sum_{i=2}^{n} p(\mu_{i})v_{i}(a)v_{i}(b)$$

$$\geq \frac{1}{n} - \left|\sum_{i=2}^{n} p(\mu_{i})v_{i}(a)v_{i}(b)\right|$$

$$\geq \frac{1}{n} - \sum_{i=2}^{n} |p(\mu_{i})| |v_{i}(a)| |v_{i}(b)|$$

$$\geq \frac{1}{n} - \max_{i\geq 2} |p(\mu_{i})|$$

$$\geq \frac{1}{n} - \max_{i\geq 2} |p(\mu_{i})|$$

$$\geq 0$$

Where the penultimate step follows from  $\sum_i |v_i(a)| |v_i(b)| \le 1$ . Let V be the matrix where rows are the eigenvectors  $v_i$ 's. Then  $V \cdot V^T = I$  by the orthonormal condition. It follows that  $V^T \cdot V = I$  and the columns

<sup>&</sup>lt;sup>2</sup>Note that we're not saying anything about  $\delta$  if p(M) has zero entries. Since there are no restrictions on  $c_j$ , it's possible that the summation produces a zero entry for p(M) where for all positive  $c_j$  a non-zero entry would have existed.

of V form an orthonormal basis. Hence  $\left(\sum_{i=2}^{n}|v_i(a)||v_i(b)|\right)^2 \leq \left(\sum_{i=2}^{n}|v_i(a)|^2\right)\left(\sum_{i=2}^{n}|v_i(b)|^2\right) \leq 1$ . The ultimate step follows from our assumption that  $|p(\mu_i)| < \frac{1}{n}$  for all  $i \geq 2$ . Thus, if p(1) = 1 and  $|p(\mu_i)| < \frac{1}{n}$  for all  $i \geq 2$ , we have that every entry in p(M) is non-zero, implying that  $\delta \leq k$ .

**Claim 6** For any  $t \in (0,1)$ , I assert the existence of a magic polynomial,  $p_k^{(t)}$ , with the following properties:

- 1.  $p_k^{(t)}$  is of degree k
- 2.  $p_k^{(t)}(1) = 1$

3. 
$$\left| p_k^{(t)}(x) \right| \le 2 \left( 1 + \sqrt{2t} \right)^{-k} \text{ for any } x \in [0, 1 - t]$$

We will provide no proof for this claim here, but the polynomials are derived from Chebyshev polynomials, and we'll use them again later. To provide some intuition, figure 1 shows graphs of these polynomials for k = 10 with varying t. Notice that to keep the same bound for smaller values of t, a larger k is required due to the "oscillations" that the polynomial must take on in order to achieve p(1) = 1 while keeping p(x) small for  $x \in [0, 1-t]$ .

**Figure 1**: (a) t = 0.1 (b) t = 0.001 (c) t = 0.001 zoomed in for x from 0.99 to 1

If we set  $t = \lambda$ , we get a degree k polynomial, p, such that

- 1. p(1) = 1
- $2. \ |p(x)| \leq 2 \left(1 + \sqrt{2\lambda}\right)^{-k} \text{ for any } x \in [0, \mu_2].$

Additionally, if we set  $k = \left(1 + \frac{1}{\sqrt{2\lambda}}\right) \ln{(2n)}$ , then it is possible to show that  $p(x) < \frac{1}{n}$  for all  $x \in [0, \mu_2]$ , which gives the following bound:

$$\delta \le \left(1 + \frac{1}{\sqrt{2\lambda}}\right) \ln\left(2n\right) \tag{4}$$

This is much better than our previous bound of  $\delta \leq \frac{\ln(n)}{\lambda}$ . So, strangely, by putting in a particular polynomial, we get a bound that grows with  $1/\sqrt{\lambda}$  as opposed to just  $1/\lambda$ . This foreshadows our next unit on iterative linear algebra.

#### 1.3 Example Application

Suppose that you have a symmetric matrix M and want the eigenvector associated with the largest eigenvalue. For purposes of this example, let them be normalized such that the largest eigenvalue is 1. Then an easy way to get an approximate answer for the eigenvector is to compute  $M^k x$  for a large k and a random x.

Why does this give the eigenvector associated with  $\mu_1 = 1$ ? If all other eigenvalues are less than 1, then for a large enough k, they will diminish in importance, until all that is left is  $v_1$ . This is a very intuitive and natural algorithm that takes about  $1/\lambda$  steps to get close.

But we just found a much faster algorithm! Assuming that we know some good bound on  $\lambda$  (if we don't, we could easily search for it), we can compute  $p_k^{(\lambda)}(M)x$  instead of  $M^kx$  to get the dominant eigenvector. This method converges much faster, and we'll get into this more in a few lectures.

# 2 Expanders

If you had to know one set of graphs in your life, these are the ones to know. They often are a counterexample to many long-standing conjectures. Also, they turn up literally everywhere. If you didn't know any better, you would think that they don't exist from the described properties. But they're almost every single graph. Specifically, we'll be looking at families of d-regular graphs  $(G_n)_n$  as n goes to infinity:

**Definition 7**  $(G_n)_n$  is an expander family if  $\lambda_2(G_n) \geq c$  for some constant c and for all n.

Most of the graphs we've looked at are not expanders. For example, path graphs have  $\lambda_2 \leq O(1/n^2)$  and binary trees have  $\lambda_2 \leq O(1/n)$ . This means that  $\lambda_2$  very quickly goes to zero as  $n \to \infty$  for both cases. Expanders don't have this property. Even as  $n \to \infty$ ,  $\lambda_2$  stays above a constant. Given this, it's not clear that they should exist.

**Note:** We should think of d as a constant. In other words, we'll pick a d and study expanders in that family.

## 2.1 Relating Expanders to Cuts

The first thing we'll look at is Cheeger's inequality for expanders. Recall that

$$\frac{\lambda_2}{2} \le \phi(G)$$

For expanders, this implies

$$\frac{c}{2} \le \phi(G)$$

What does this mean? It means that any set, S, of vertices with  $|S| \le n/2$  has at least (c/2)|S| edges leaving it. This is a strong property: for expanders, there are no small cuts that can be made in the graph. Every cut that balances the sizes of the sets of vertices cuts a constant fraction of the edges in the graph.

The other side of Cheeger's inequality says

$$\Theta(1) \frac{\phi(G)^2}{d} \le \lambda_2$$

Again, for expanders, this can be rewritten.

$$\phi(G) \leq \sqrt{\frac{cd}{2\Theta(1)}}$$

Since d is a constant, this says that the isoperimetry,  $\phi$ , is also bounded above by a constant. Normally, there's a large gap between the upper-bound and lower-bounds in Cheeger's inequality. Here we've sandwiched  $\phi$  between two constants. Therefore, an equivalent definition of expanders is as follows:

**Definition 8**  $(G_n)_n$  is expander family if  $\phi(G) \geq c'$  for some constant c' and all n.

## 2.2 Do Expanders Exist?

A natural question is if expanders exist, what are the required parameters of the graphs? It turns out that random graphs are expanders, and so, almost all graphs are expanders. But, there's a limit as to how "good" of an expander you can have:

Claim 9 For any 
$$G$$
,

$$\lambda_2 \le d - 2\sqrt{d-1} + o(1) \tag{5}$$

In other words, even though  $\lambda_2$  is always larger than a constant, there's a limit as to how well-connected it can be. We won't prove this. But this is not that strong a bound. We already know that  $\lambda_2 \leq d$ . This is just  $O(\sqrt{d})$  smaller. Furthermore, this bound is tight since Ramanujan graphs meet it. So that's the limit of what an expander can be.

## 2.3 Expanders and Randomness

Expanders are all over the study of randomness, but we'll just study one interesting property. We'll use  $\mu_2 = d - \lambda_2$  to simplify formulas, where now,  $\mu_2$  is the second largest eigenvalue of the adjacency matrix. Suppose you make a graph by randomly including each edge with probability d/n. In other words, construct a graph such that each vertex has an expected number of d edges leaving it. Since the total number of possible edges is |S||T| and there's a d/n probability of having each edge, the expected number of edges between any two sets S and T will be  $\frac{d|S||T|}{n}$ .

Claim 10 Expander Mixing Lemma: If you choose any two vertex sets, S and T, the difference in the total number of edges between the two and the expected number for a random graph is bounded. Formally,

$$\left| e(S,T) - \frac{d|S||T|}{n} \right| \leq \frac{\mu_2}{n} \sqrt{|S||\bar{S}||T||\bar{T}|}$$

$$\leq \mu_2 \sqrt{\min(|S|, |\bar{S}|) \cdot \min(|T|, |\bar{T}|)}$$

This is surprising because there is no randomness here. This is just a property associated with expanders, but it behaves similarly to random graphs.

**Proof** Let  $\alpha$  and  $\beta$  be the fraction of total vertices that are in the sets S and T:

$$|S| = \alpha n$$
  $|T| = \beta n$ .

Let x and y be the characteristic vectors of S and T, respectively.

**Definition 11** A characteristic vector, x, of a set S is a vector of length n that has  $x_i = 1$  if  $v_i \in S$ , and  $x_i = 0$  otherwise.

We can now write the number of edges between sets S and T as  $e(S,T) = x^T Ay$ . Now, as you've probably noticed, it's beneficial to use vectors that are perpendicular to the all-ones vector,  $\mathbf{1}$ . So, we'll rewrite x and y as

$$v = x - \alpha \mathbf{1}$$
  $w = y - \beta \mathbf{1}$ .

Clearly,  $v \cdot \mathbf{1} = w \cdot \mathbf{1} = 0$ , implying orthogonality. Rewriting the number of edges between sets S and T, we get

$$e(S,T) = x^T A y$$
  
=  $(v + \alpha \mathbf{1})^T A (w + \beta \mathbf{1})$   
=  $v^T A w + v^T A \beta \mathbf{1} + \alpha \mathbf{1}^T A w + \alpha \mathbf{1}^T A \beta \mathbf{1}.$ 

Using the following identities,

$$A\mathbf{1} = d\mathbf{1} \qquad \mathbf{1}^T A = d\mathbf{1}^T,$$

we get

$$e(S,T) = v^T A w + \beta v^T A \mathbf{1} + \alpha \mathbf{1}^T A w + \alpha \beta \mathbf{1}^T A \mathbf{1}$$
$$= v^T A w + \beta v^T d \mathbf{1} + \alpha d \mathbf{1}^T w + \alpha \beta d \mathbf{1}^T \mathbf{1}$$
$$= v^T A w + \alpha \beta d n.$$

where we have used the orthogonality of v and w with  $\mathbf{1}$  (i.e.,  $v^T\mathbf{1}=0$ ) to cancel out the middle two terms. We now have the following bound:

$$\begin{aligned} |e(S,T) - \alpha \beta dn| &= |v^T A w| \\ &\leq |v| |A w| \\ &\leq |v| \mu_2 |w| \\ &= \frac{\mu_2}{n} \sqrt{(\alpha n) \left( (1-\alpha) n \right) (\beta n) \left( (1-\beta) n \right)} \\ &= \frac{\mu_2}{n} \sqrt{|S| |\bar{S}| |T| |\bar{T}|}, \end{aligned}$$

where the third line follows from the fact that w is orthogonal to 1, and thus,  $\mu_2$  is the largest eigenvalue that can affect w, and the fourth line follows from the fact that  $|v| = \sqrt{n\alpha(1-\alpha)}$ . To see this, note that

$$|v| = |x - \alpha \mathbf{1}|$$

$$= \sqrt{|S|(1 - \alpha)^2 + |\bar{S}|(-\alpha)^2}$$

$$= \sqrt{\alpha n(1 - \alpha)^2 + (1 - \alpha)n\alpha^2}$$

$$= \sqrt{\alpha n(1 - \alpha)(1 - \alpha + \alpha)}$$

$$= \sqrt{\alpha n(1 - \alpha)},$$

and the same steps show that  $|w| = \sqrt{n\beta(1-\beta)}$ . Thus, we have shown that  $|e(S,T) - \alpha\beta dn| \le \frac{\mu_2}{n} \sqrt{|S||\bar{S}||T||\bar{T}|}$ .

#### 2.4 Some Properties We Now Know

- Random walks on expanders mix in a logarithmic number of steps
- Expanders have logarithmic diameter
- Expanders have a constant isoperimetric number

#### 2.5 Vertex Expansion

We've discussed cutting a graph and looking at the number of edges cut. An equivalent way of thinking about a cut is to select a set of vertices and then count the number of edges with one vertex in the set and one out. Another useful metric can be obtained by counting the number of vertices that are neighbors of a set. In other words, for a set of vertices, X, let N(X), be the set of vertices, Y, such that  $(x,y) \in E$  such that  $x \in X$  and  $y \in \bar{X}$ .

#### Claim 12

$$N(X) \ge \frac{d^2|X|}{\mu^2 + (d^2 - \mu^2)|X|/n}$$

We don't prove this, but the high level idea is the following:

- Select a set of vertices from G. Call this set X.
- Let Y be the set of vertices that are neither in X nor in N(X). In other words,  $Y = V \setminus (N(X) \cup X)$ .
- Now, by construction, we have that e(X,Y)=0.

Algebra gets a little messy, but you can just plug the above into the expander mixing lemma to show this bound. It turns out also that for X/n small and  $\mu = 2\sqrt{d-1}$ , we can achieve

$$N(X) \ge \frac{d}{4}|X|.$$

Why is this interesting? What this is saying is that for any set X, there are at least d/4 neighbors not in X. Since each vertex has d neighbors total, this bound is quite strong. It turns out that this is about as good as you can get with spectral graph theory. To see this, we will generalize the vertex expansion as follows.

We want to show bounds of the form  $|N(S)| \ge \gamma |S|$ . In other words, we want to say that the vertex expansion of G is greater than or equal to  $\gamma$  for any S. Sometimes we'll only care about expansions of smaller sets (e.g., for  $|S| \le 0.01n$ ).

**Definition 13** G is an  $(\alpha, \beta)$ -expander if for  $\alpha\beta < 1$  and all sets S with  $|S| \le \alpha n$  have  $|N(S)| \ge \beta |S|$ .

We showed that Ramanujan graphs are  $(\alpha, d/4)$  expanders for some constant  $\alpha$ . Some applications need expansion greater than d/2 but with small (constant)  $\alpha$ . These exist, but we can't prove better than d/2 with spectral techniques.<sup>3</sup>

## 2.6 Bipartite Expanders

Many of the applications of expanders use bipartite expanders. These are just expanders that are bipartite graphs. It is easier to show that these exists (it will be a homework problem!).

**Definition 14** A d-regular bipartite graph is an  $(\alpha, \beta)$ -expander if every set S on the left with  $|S| \leq \alpha n$  has  $N(S) \geq \beta |S|$ .

Whenever  $\alpha\beta < 1$ , there exists some d such that almost all d-regular graphs on n nodes (for n sufficiently large), are  $(\alpha, \beta)$ -expanders.

<sup>&</sup>lt;sup>3</sup>It turns out that random graphs work here. In 2002, Capalbo, Reingold, Vadhan, and Wigderson gave an explicit construction technique with expansion d - o(1).

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 1 Administrivia

There were two administrative announcements made at the beginning of class today.

- The first problem set will be posted online tonight. It will be due two weeks from today, on October 15.
- Some people have asked Professor Kelner if he could post typo-free versions of the powerpoint slides online. Therefore, it is requested that the scribe email Professor Kelner a list of the known typos in the slides.

# 2 Outline

In today's lecture we are going to:

- Discuss nonblocking routing networks
- Start the description of a method for local and almost linear-time clustering and partitioning based on the Lovasz-Simonovits Theorem.

Nonblocking routing networks are an example application of expander graphs. Furthermore, many of the techniques that we discuss today for analyzing routing networks can also be applied to error-correcting codes. In the second half of class, we discuss local clustering and partitioning, and we will finish the analysis in Tuesday's class.

# 3 Nonblocking routing networks

Suppose you have a network with 2N terminals, consisting of N "input" terminals (drawn on the left side) and N "output" terminals (drawn on the right side). We want to design a network that connects them, in such a way that every permutation can be routed. That is, for any one-to-one function f from the input terminals to the output terminals, we would like there to be a path in the network from each input node i to the output node f(i). Furthermore, we ask that for any such f, the paths can be chosen to be vertex disjoint. The motivation is that we would like for each input terminal to be able to talk to a different output terminal so that none of the intermediate routers are overloaded. This kind of networks is called a nonblocking routing network and it is generally useful for communication.

We also want the network to have some nice features. First, we want that each node has bounded degree (If we don't ask this, then a simple solution is to put a wire from every input to every output. Of course, this is not very plausible for large N, for example the phone network in the U.S.). Second, we want that the number of nodes in the graph is  $O(n \log n)$  (so, that the network is not too big). And finally we want a fast, decentralized algorithm for finding routes.

## 3.1 Butterfly networks

A first attempt to find a small network in which routing is easy is to consider a Butterfly network. A Butterfly network for N inputs and outputs consists on  $\log(N)$  layers of N nodes each. The first layer (or zeroth layer) correspond to the N inputs and the last layer corresponds to the N outputs. The i-th layer is divided into blocks of  $N/2^i$  elements. Each block 'splits' into two blocks: 'up' and 'down' in the next layer. Each node has two neighbors in the next layer, one in the corresponding 'up' block and one in the corresponding 'down' block in such a way that every node in the (i+1)-th layer has only 2 neighbors in the i-th layer.

This can be easily done by labeling each node in the network with a pair (i,r) where i corresponds to the number of the layer and r is the position of the node in the layer written in binary. Then each node (i,r) is connected to (i+1,r) and  $(i+1,r^{(i+1)})$ , where  $r^{(i+1)}$  denotes r with the (i+1)-th element complemented.

Figure by MIT OpenCourseWare.

Figure 1: Butterfly network for 8 inputs.

Although in a Butterfly network, routing is easy (just follow the binary expansion of the label of the desired output), it's not possible to avoid congestion (e.g. in Figure 1, if you try to route 000 to 000 and 110 to 001, the route will collide on the third layer). Actually, for some permutations you can get up to  $\sqrt{N}$  collisions. While butterfly networks do not successfully avoid congestion, they are the base for a type of nonblocking routing network called a multibutterfly.

### 3.2 Multibutterfly networks

The construction of multibutterfly networks uses bipartite expanders, which we discussed last class. We recall the definition here:

**Definition 1** A d-regular bipartite graph is an  $(\alpha, \beta)$ -expander if every set S on the left with  $|S| \leq \alpha n$  has  $N(S) \geq \beta |S|$ .

Thus, intuitively, a regular bipartite graph is an  $(\alpha, \beta)$ -expander if any small collection of vertices on the left has a proportionately large number of neighbors.

A d-multibutterfly is a layered graph constructed similarly to the butterfly networks, but such that each node now has d edges out to the 'up' block of the next layer and d edges out to the 'down' block. These networks are carefully constructed such that the graph induced by the vertices of a block and its 'up' neighbor block and the graph induced by the block and its 'down' neighbor block are both  $(\alpha, \beta)$ -expanders for  $\beta > d/2$ ,  $\beta \approx 1/2\alpha$ .

A 2-multibutterfly for N=8 allowing 4 pairs of inputs/outputs is shown in Figure 2.

Note that d-multibutterflies have  $O(N \log N)$  vertices and that the vertices have bounded degree (at most 4d), then the only condition needed for this to be a good nonblocking routing network is that we can route any permutation of inputs and outputs easily.

Figure by MIT OpenCourseWare.

Figure 2: 2-Multibutterfly network for 4 inputs.

Each layer of the network has N elements, but the multibutterfly network we described will only route  $2N\alpha$  inputs to  $2N\alpha$  outputs. In a final implementation, we would connect the actual inputs and outputs to  $\alpha/2$  successive multibutterfly inputs/outputs.

Claim 2 A d-Multibutterfly with N nodes in each layer can route any permutation of  $2\alpha N$  inputs to  $2\alpha N$  outputs.

To prove this claim, we will need Hall's Theorem.

**Theorem 3 (Hall)** A bipartite graph G has a perfect matching if and only if every set S on the left has at least |S| neighbors on the right.

Using Hall's Theorem, we now prove the above claim.

**Proof** We only need to prove that in each pair of consecutive layers, any block can successfully route its signals to both the 'up' neighbor block and the 'down' neighbor block. It suffices to prove this for the first layer, since the proof for any other layer is identical. Note that in the first layer, at most  $\alpha N$  calls will need to go to the top half, and at most  $\alpha N$  calls need to go to the bottom half. Let S be the set of nodes in the first layer which need to go up, and let T be the set of nodes in the top half of the second layer. We will show that it is possible to choose edges to match each vertex of S with a vertex of T.

Since  $|S| \leq \alpha N$ , and the graph induced by  $S \cup T$  is an  $(\alpha, \beta)$ -expander by construction, it follows that  $|N(S) \cap T| \geq \beta |S| > |S|$ , and so, by Hall's theorem, there is a perfect matching between S and T. We use that matching to route the calls that need to go up. The calls that need to go down are routed in an analogous way.

The previous claim guarantees that a nonblocking routing exists, and it can be found by solving a matching problem. However, in real life we don't want to use a complicated global computation for routing: We need a simple distributed algorithm. Such an algorithm exists and is simple to describe. Consider a pair of blocks S and T that we want to match (as in the proof of the claim). The algorithm is as follows:

### Algorithm:

 $S_1 \leftarrow S$ .

while  $S_i \neq \emptyset$ 

Every node of  $S_i$  sends a proposal to all neighbors in T.

Every node of T receiving exactly one proposal accepts it.

Every node in  $S_i$  that got at least one accepted proposal picks one arbitrarily and matches to it.

 $S_{i+1}$  is the set of unmatched remaining nodes in  $S_i$ .

**Claim 4** The previous algorithm finds a matching of S and T in  $O(\log n)$  steps.

To prove this claim, first we will need to prove the following two lemmas:

**Lemma 5** For any set S of size  $|S| \le \alpha N$ , the number of vertices in T with exactly one neighbor in S is at least  $(2\beta - d)|S|$ 

**Proof** Let A be the vertices in T with exactly one neighbor in S, and let B be the remaining vertices in T which are neighbors of S. Since the graph induced by  $S \cup T$  is a  $(\alpha, \beta)$ -expander,  $|A \cup B| \ge \beta |S|$ . Also, we know that the number of edges from S to T is at most |A| + 2|B|. Thus, using the fact that the number of edges from S to T is exactly d|S|, we know:

$$|A| + |B| = |A \cup B| \ge \beta |S|$$

$$d|S| = e(S,T) \ge |A| + 2|B|$$

and hence

$$|A| \geq \beta |S| - |B| \geq \beta |S| - \frac{d|S| - |A|}{2}$$

and thus  $|A| \geq 2\beta |S| - d|S|$ .

Given the above lemma nd the fact that any node in the left side can receive at most d acceptances in any round of the protocol, we conclude:

Lemma 6 For all i,

$$\frac{|S_{i+1}|}{|S_i|} \le 2(1 - \beta/d).$$

This last lemma guarantees that the algorithm converges in  $O(\log n)$  steps, as desired.

# 4 Local and almost linear-time clustering and partitioning

### 4.1 Motivation

In these days, graphs are getting really big. For example, circuits layouts have 50 million transistors; scientific computing has hundreds of millions of variables; the Internet has billions of nodes, etc. So any algorithm that performs a task in these graph in time such as  $n^2$  will be very bad in practice. Even a running time such as  $n^{1.5}$  tends to not be good enough. In some cases, like in Internet, even visiting every node of the graph once is an impossible task. For that reason, we are interested in developing algorithms for certain applications that runs in almost linear time (i.e. O(npolylog(n))), or algorithms that are local, i.e., that do not need to visit the entire graph. (Note that log factors tend to be fairly small, even in the cases mentioned above, and oftentimes logarithmic factors depend on the specific model of computation being analyzed.)

### 4.2 Local Clustering

Given a vertex v in a graph we would like to know if v is contained in a cluster, where a cluster is a set that defines a cut of low conductance. We also want the running time for this algorithm to depend on cluster size and not in the size of the graph. A good example for this is finding a cluster of web pages around the mit.edu domain, where we don't want this task to depend on the number of sites recently created on the other side of the world.

The goal for this part of the lecture will be to describe an algorithm that runs in time almost linear in K that outputs a cluster of size at least K/2 around starting vertex, if that cluster exist.

The approach we will use will rely on what we know about cuts, eigenvalues and random walks. First observe that if v is contained in a cluster and you start running a random walk from v, then the low

conductance cut will be an obstacle for the mixing time. This means that the random walk has trouble leaving the cluster. So, a good guess for the cluster is the set of vertices for which a random walk starting at v will have the highest probabilities after a given number of steps. Using this idea, a good primitive to construct an almost linear algorithm will be the following.

"Approximate, for every vertex in the graph, the probability that a random walk starting from v is in that vertex after certain time, select the k highest valued vertices and check if they define a good cut. Repeat this until you get a good cut or you reach a predetermined limit."

Note that this method is similar to the proof of Cheeger's inequality, where we ordered the entries of  $v_2$  to obtain a cut. Here, however, use use a probability vector instead of the eigenvector  $v_2$ .

We need a bound that says that this idea works. Unfortunately, all the bounds we have proven thus far are global, involving  $\lambda_2$  of the whole graph. We desire bounds on a local feature of the graph. Furthermore, we can't really compute all of the necessary probabilities, because it will take too long. We therefore need to approximate the probabilities, without knowing the size of the cluster in advance.

### 4.3 Lovasz-Simonovits

The Lovasz-Simonovits Theorem will give us the bound we need for the algorithm. It relies on an interesting idea: measure the progress of the walk not by one number but by a whole curve. The better the random walk is to reaching the stable distribution, the closer the curve will be to a straight line. Different points on the curve will correspond to different size partitions. Before stating the theorem, we will need some definitions.

Let G be the digraph obtained from the original graph where we first replace each undirected edge uv by two directed arcs (u, v) and (v, u), and then we add self-loops loops to each node until every node v of G has  $d_v/2$  self-loops (i.e. half of the edges leaving v are self-loops).

Instead of focusing on the vertices, we will mainly study the edges of G. Suppose that we have a certain probability distribution p on vertices. Define

$$\rho(u) = \frac{p(u)}{d_u}, \text{ for every node } u,$$

$$\rho(u, v) = \rho(u), \text{ for every arc } (u, v).$$

Note that  $\rho(u, v)$  represents the mass about to be sent over arc (u, v) and that for every node u,  $\rho(u)$  approaches 1/2m as the walk converges (here, 2m is the number of arcs in the digraph). Therefore, as the walk converges,  $\rho(e)$  goes to 1/2m for every arc e.

We will define a curve that measures how close we are to convergence and also contains additional information.

**Definition 7 (Lovasz-Simonovits curve)** For a given  $\rho$ , order the arcs such that  $\rho(e_1) \geq \rho(e_2) \geq \ldots \geq \rho(e_{2m})$ . We define  $I : [0, 2m] \rightarrow [0, 1]$  as follows: For each  $k \in \{0, \ldots, 2m\}$ ,

$$I(k) = \sum_{i=1}^{k} \rho(e_i).$$

We extend I to the complete interval by interpolating it piecewise linearly.

Intuitively I(k) measures how much probability is transported over the k most utilized edges. Here we describe some of the properties of the L-S curve.

- As the walk converges I should eventually converge to a straight line.
- I(0) = 0, I(2m) = 1.
- The slope of I between k and k+1 is given by  $I(k+1)-I(k)=\rho(e_{k+1})$ .
- Since  $\rho$  depends only on the start vertex, it does not matter how we order edges out of any particular node u, and therefore the slope of I is constant for all the intervals corresponding to arcs leaving u.

• The slope is nondecreasing, so *I* is concave.

We will prove some claims and Theorems about I, and then we will state and prove the Lovasz-Simonovits Theorem.

Claim 8 For any  $c_1, \ldots, c_{2m} \leq 1$ ,

$$\sum_{i=1}^{2m} c_i \rho(e_i) \le I\left(\sum_{i=1}^{2m} c_i\right).$$

**Proof** Think of the  $c_i$ 's as weights for the  $\rho(e_i)$ . Since the  $\rho(e_i)$  are non-increasing, moving some weight from some j to some i < j only makes the sum bigger. So the sum is biggest when the first bunch of  $c_i$ 's are 1, the next one is the remaining, and the rest of them are 0, which is exactly the value of the right hand side.

In what follows, let  $\rho^t$  and  $I^t$  be  $\rho$  and I at time t in the random walk.

Claim 9 For all x and t,  $I^t(x) \leq I^{t-1}(x)$ .

**Proof** This claim states that the value of the curve at any point never increases as t increases. Let  $e_i = (u_i, v_i)$ , so that  $\rho(u_1, v_1) \geq \rho(u_2, v_2) \ldots \geq \rho(u_{2m}, v_{2m})$  It suffice to prove the claim in the case where x = k and W is the vertex set  $\{u_1, \ldots, u_k\}$  such that  $(u_1, v_1), \ldots, (u_k, v_k)$  are precisely the set of edges leaving W. We then have:

$$I^{t}(k) = \sum_{i=1}^{k} \rho^{t}(u_{i}, v_{i}) = \sum_{i=1}^{k} \rho^{t}(u_{i})$$

$$= \sum_{i=1}^{k} \rho^{t-1}(v_{i}, u_{i}), \text{ as the mass leaving } W \text{ at } t \text{ is the amount entering } W \text{ at } t-1$$

$$\leq I^{t-1}(\sum_{i=1}^{k} 1) = I^{t-1}(k),$$

where the last inequality follows from the previous claim.

Now we will prove something a little stronger: We will prove that the curve  $I^t$  has to lie below  $I^{t-1}$  by an amount depending on  $\phi_G$ .

**Theorem 10** For every initial distribution  $p^0$ , all t, and every  $x \in [0, m]$ ,

$$I^{t}(x) \le \frac{1}{2} \left( I^{t-1}(x - 2\phi_{G}x) + I^{t-1}(x + 2\phi_{G}x) \right),$$

and for every  $x \in [m, 2m]$ ,

$$I^{t}(x) \le \frac{1}{2} \left( I^{t-1}(x - 2\phi_{G}(2m - x)) + I^{t-1}(x + 2\phi_{G}(2m - x)) \right)$$

Before beginning the proof, we note that the above result has a geometric interpretation. The first equation above states that the value of  $I^t(x)$  lies below the midpoint of the line connecting  $I^{t-1}(x-2\phi_G x)$  and  $I^{t-1}(x+2\phi_G x)$ . Recalling that the graph of I is always concave, this implies the above result that the value of I(x) at time t is no greater than the value of I(x) at time t-1. Furthermore, if  $I^t$  differs significantly from the straight line (which I converges to in the limit) and if  $\phi_G(x)$  is large, then  $I^t(x)$  will decrease by a significant amount in the next step (once again, by concavity). Thus, the theorem matches our intuition that low-conductance cuts around x cause the walk to mix more slowly.

### Proof

This proof was not covered in its entirety in today's lecture, but it was covered in Lecture 7 of the 2007 version of the course:

We will only prove the case  $x \in [0, m]$ , the second case should be analogous. As in the previous claim we can assume without loss of generality that x = k, and that  $(u_1, v_1), \ldots, (u_k, v_k)$  are exactly the set of edges starting from  $W = \{u_1, \ldots, u_k\}$ . We then have:

$$\sum_{i=1}^{k} \rho^{t}(u_{i}, v_{i}) = \sum_{i=1}^{k} \rho^{t-1}(v_{i}, u_{i}).$$

Break the edges of the right into two sets:

$$W_1 = \{(v_i, u_i) : u_i, v_i \in W, v_i \neq u_i\}.$$
  $W_2 = \{(v_i, u_i) : u_i \in W, v_i \notin W\} \cup \{\text{self loops}\}.$ 

We claim that:

1. 
$$\sum_{(v,u)\in W_t} \rho^{t-1}(v,u) \leq \frac{1}{2}I^{t-1}(x-2\phi_G x)$$
.

2. 
$$\sum_{(v,u)\in W_2} \rho^{t-1}(v,u) \leq \frac{1}{2}I^{t-1}(x+2\phi_G x)$$
.

Note that out of the x=k edges starting at W, x/2 are self loops, and at least  $\phi_G x$  edges leave W, therefore, the number of edges in  $W_1$  is at most  $x/2 - \phi_G x$ . Note that if we let  $c_i$  be 1 if  $e_i \in W_i$  and 0 otherwise, we have that  $\sum_{i=1}^k c_i \leq x/2 - \phi_G x$ . And then, using Claim 8, we can obtain the following weaker bound:

$$\sum_{(v,u)\in W_1} \rho^{t-1}(v,u) \le I^{t-1}(x - 2\phi_G x).$$

We need to 'move' the 1/2 factor outside of  $I^{t-1}$  somehow. Instead of doing that, we will carefully choose other values for  $c_i$  to obtain the wanted bound. For that simply let  $c_i$  be 1/2 if  $e_i \in W_i$  or if  $e_i$  is a self loop in W and 0 otherwise. Then, since every vertex has the same number of self loops as edges leaving it (and they all have the same  $\rho$  value), we also obtain under this new set of weights, that  $\sum_{i=1}^k c_i \leq x/2 - \phi_G x$ . Using Claim 8 and that  $2c_i \leq 1$ , for every i, we have:

$$\sum_{(v,u)\in W_1} \rho^{t-1}(v,u) = \sum_{i=1}^k c_i \rho^{t-1}(v_i,u_i) = \frac{1}{2} \sum_{i=1}^k c_i \rho^{t-1}(v_i,u_i) \le \frac{1}{2} I^{t-1}(x-2\phi_G x).$$

The second claim follows in a similar way, and combining both of them we obtain the result.

Using the previous theorem, we are ready to state and prove Lovasz-Simonovits Theorem.

Theorem 11 (Lovasz-Simonovits) For all initial distribution  $p^0$  and every t,

$$I^{t}(x) \le \min(\sqrt{x}, \sqrt{2m-x}) \left(1 - \frac{1}{2}\phi_{G}^{2}\right)^{t} + \frac{x}{2m}.$$

Sketch of Proof Consider the curve

$$R^0 = \min(\sqrt{x}, \sqrt{2m - x}) + \frac{x}{2m}.$$

It is easy to show that  $I^0(x) \leq R^0(x)$ , for all  $x \in [0, 2m]$ . If we set

$$R^{t}(x) = \frac{1}{2} \left( R^{t-1}(x - 2\phi_{G}x) + R^{t-1}(x + 2\phi_{G}x) \right),$$

for  $x \in [0, m]$  and

$$R^{t}(x) = \frac{1}{2} \left( R^{t-1}(x - 2\phi_{G}(2m - x)) + R^{t-1}(x + 2\phi_{G}(2m - x)) \right),$$

for  $x \in [m, 2m]$ , then it is easy to show that

$$R^t(x) \leq \min(\sqrt{x}, \sqrt{2m-x}) \left(1 - \frac{1}{2}\phi_G^2\right)^t + \frac{x}{2m}.$$

Using that all the curves defined so far are concave and the previous theorem, we have:

$$I^t(x) \leq R^t(x),$$

for all t, which proves the theorem.

From here, we can derive the following Corollary:

Corollary 12 For W a set of vertices, and  $x = \sum_{w \in W} d_w$ ,

$$\left| \sum_{w \in W} p^t(w) - \pi(w) \right| \le \min(\sqrt{x}, \sqrt{2m - x}) \left( 1 - \frac{1}{2} \phi_G^2 \right)^t.$$

We can use this Corollary for local clustering in the following way. If after  $O((\log m/\phi_G)^2)$  steps a set of vertices contains a constant factor more than what it would have under stationary distribution, then we can get a cut C such that  $\Phi(C) \leq \phi_G$ . (The cut can be obtained by mapping the probabilities to real line and cut like we did with  $v_2$  some lectures ago).

The problem with this approach is that computing all the probabilities will be too slow. In particular, after a constant number of steps we have too many nonzero values. One solution proposed by Lovasz and Simonovits is to simply zero out the smallest probabilities and prove that it doesn't hurt much. However, the analysis can get messy. Instead, in next lecture we will speak about a different approach that uses a slightly different vector, called PageRank.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

#### 18.409 An Algorithmist's Toolkit

October 6, 2009

### Lecture 8

Lecturer: Jonathan Kelner Scribe: Alessandro Chiesa (2009)

# 1 Administrivia

You should probably know that

- the first problem set (due October 15) is posted on the class website, and
- its hints are also posted there.

Also, today in class there was a majority vote for posting problem sets earlier. Professor Kelner will post the problem sets from two years ago, but he reserves the right to add new problems once a problem set has already been posted.

#### Questions from last time.

- What is a level set? The level set of a function corresponding to a (fixed) constant c is the set of points in the function's domain whose image equals c.
- What is a good reference on applications of expander graphs? A course taught by Nathan Linial and Avi Wigderson [3].

**Plan for today.** We use what we proved last time to obtain a local clustering algorithm from a random walk scheme. Then, noting that similar results to the ones proved last time also hold for PageRank, we obtain a second scheme that yields a second, better local clustering algorithm. Finally, we briefly motivate the technique of sparsification, which we will discuss next time.

# 2 Local and Almost Linear-Time Clustering and Partitioning

#### 2.1 Review of Local Clustering

Let us briefly review local clustering, which we introduced last time. Given a vertex v in some graph G, we would like know if v is contained in a cluster, i.e. a subset of vertices that defines a cut with low conductance. However, we want the running time of our algorithm to depend on the *cluster size*, and not on the size of the graph. Last time we mentioned that a good example of a problem of this sort is trying to find a cluster of web pages around  $\mathtt{mit.edu}$ ; we surely do not want the running time of this task to depend on the number of sites created on the other side of the world. Let us make our goal a little bit more precise: in this lecture we will describe an algorithm that, after running for time almost linear in K, outputs a cluster of size at least K/2 around the starting vertex, if such a cluster exists.

#### 2.2 General Strategy

We observe that if we run a random walk starting from some vertex v contained in a cluster, then low-conductance cuts will be an obstacle to mixing; i.e., the random walk has trouble leaving the cluster. Hence, a good guess for the cluster is the set of vertices with the highest probability masses after a given number of steps (of a random walk that started at v). Last time we showed that this makes sense by proving the Lovász-Simonovits theorem [4].

Therefore, a good primitive to construct an almost linear-time global algorithm is the following. Run a random walk starting from v, and, at each step, for every vertex w, approximate the probability that the random walk is at w; then take the vertices with the k largest probability masses as a possible cut. Repeat this until you get a good cut or you reach a predetermined limit.

### 2.3 Obstacles

We need a bound that says that our general strategy works, and that is why we proved the Lovász-Simonovits theorem. However, the bound we have is global, i.e., it involves the conductance  $\phi(G)$  and we do not have the time to compute  $\lambda_2$  for the whole graph to bound the conductance. Moreover, if we exactly compute all the probabilities of the random walk, it will take too long. Finally, even if we approximate the probabilities, we would need a stronger bound, and the goodness of the approximation depends on the cluster size, which we do not know in advance.

#### 2.4 One Solution

A reasonable solution goes as follows. We recall that the proof of the Lovász-Simonovits theorem that we discussed last time used cuts on level sets of  $\rho^t$ . This implies that if a walk does not mix too quickly, we know that one of the cuts had bad conductance. Therefore, obtain the following corollary from the Lovász-Simonovits theorem.

Corollary 1 Let G = (V, E) be a connected, undirected graph with m edges and let  $\pi(x)$  be its stationary distribution  $\frac{d_x}{\sum_{v \in V} d_v}$ . For every subset of vertices  $W \subset V$  and and every time t, if  $x \equiv \sum_{w \in W} d_w$  and  $\varphi(W)$  is the conductance of the cut  $(W, \overline{W})$ , then the following inequality holds:

$$\left| \sum_{w \in W} p^t(w) - \pi(w) \right| \le \min\left(\sqrt{x}, \sqrt{2m - x}\right) \left(1 - \frac{1}{2}\phi(W)^2\right)^t.$$

Note that in the last lecture we stated a slightly weaker form of the theorem, where the conductance  $\varphi(W)$  of the cut  $(W, \overline{W})$  was replaced by the conductance  $\phi(G)$  of the whole graph. Nevertheless, we did actually prove the stronger version stated above.

The bound above has nothing to do with global properties of the graph. Therefore, we can use Corollary 1 for local clustering in the following way. If after  $O\left(\left(\frac{\log m}{\phi}\right)^2\right)$  steps a set of vertices contains a constant factor more than what it would have under the stationary distribution, then we can get a cut C such that  $\varphi(C) \leq \phi$ . (The cut can be obtained by mapping the probabilities to the real line and cut like we did with  $v_2$  a few lectures ago).

A problem with this approach is that computing all the probabilities will be too slow. In particular, after only a few steps we will have too many nonzero values to keep track of. Lovász and Simonovits proposed to simply zero out the smaller probabilities and then prove that it does not hurt much to do so. However, the analysis is really messy. Instead, Andersen, Chung, and Lang [1] propose an approach that, instead of using the probability vector of a lazy random walk, uses a slightly different vector called PageRank; we discuss this approach in the following section.

(Note that for all of this to work we still need to prove a partial converse. Indeed, one can show that if there exists a cut C of conductance  $\phi^2$ , then at least |C|/2 of its vertices will give a cut of conductance  $\phi$ , otherwise the random walk would mix too quickly.)

# 3 PageRank

#### 3.1 Definition

Consider an undirected connected graph G = (V, E). Recall that a *simple random walk* on G is a walk that, starting at some initial vertex, at each step moves from the current vertex to a randomly chosen neighbor of the vertex; a *lazy random walk* on G is a walk that, starting at some initial vertex, at each step with 0.5 probability stays on the current vertex and with 0.5 probability moves from the current vertex to a randomly chosen neighbor of the vertex.

We now consider a new Markov process that is a modification of a lazy random walk on a graph. Fix some distribution s over the vertices V of G and fix a parameter  $\alpha \in (0,1)$  (called the *teleport probability*). Starting from some initial vertex, at each step of the process we do the following: with probability  $1-\alpha$  we take a step of a lazy random walk on G, and with probability  $\alpha$  we "teleport" to a vertex drawn from s. For simplicity, we will take s to be a single vertex, i.e., all the probability mass is concentrated on one vertex.

The process converges to a stationary distribution (because it corresponds to an aperiodic, irreducible Markov chain). For consistency with [1], we denote this stationary distribution (which depends on the parameters s and  $\alpha$ ) by  $\operatorname{pr}_{\alpha}(s)$  and call it the  $\operatorname{PageRank\ vector}$ ; note that  $\operatorname{pr}_{\alpha}(s)$  is a vector in  $\mathbb{R}^n$ , where n = |V|. Moreover, it is easy to see that the stationary distribution  $\operatorname{pr}_{\alpha}(s)$  is the unique solution to the following equation:

$$\operatorname{pr}_{\alpha}(s) = \alpha s + (1 - \alpha)W\operatorname{pr}_{\alpha}(s) , \qquad (1)$$

where W is the transition matrix corresponding to a lazy random walk on G.

The point is that one can show that the Lovász-Simonovits theorem and its corollary hold for the PageRank vector  $\operatorname{pr}_{\alpha}(s)$ , where s corresponds to the starting vertex and  $\alpha$  corresponds to the number of time steps. Hence, rephrasing the discussion in Section 2.4, we know that if a subset of vertices S contains more than a constant factor more probability under  $\operatorname{pr}_{\alpha}(s)$  than under the stationary distribution, then we can find a cut with conductance  $O(\sqrt{\alpha \log \sum_{v \in Sd_v}})$ . Moreover, approximating the PageRank vector  $\operatorname{pr}_{\alpha}(s)$  is robust under small errors, because it is the solution of an equation rather than being the result of many successive computations each with approximations.

Next, we prove some properties about the PageRank vector and then show how to approximate it.

(Note that, just like before, we still need to prove a partial converse. Indeed, one can show that if there exists a cut C of conductance  $\alpha$ , then at least |C|/2 of its vertices will give a cut of conductance  $O(\sqrt{\alpha})$ ).

#### 3.2 Properties

We now prove three properties about the stationary distribution  $pr_{\alpha}$ .

**Proposition 2 (Uniqueness)**  $pr_{\alpha}(s)$  is unique.

**Proof** We must show that Equation (1) has a unique solution. Rewrite the equation as  $(I - (1 - \alpha)W)\operatorname{pr}_{\alpha}(s) = \alpha s$ . The matrix  $I - (1 - \alpha)W$  is strictly diagonally dominant<sup>2</sup> because the off-diagonal elements in each column add up to 1/2, while each diagonal element is  $1 - (1 - \alpha)(1/2)$ . By the Gershgorin circle theorem [2], it must be nonsingular, so that the equation has a unique solution.

Proposition 2 allows us to extend the definition of PageRank: given any vector  $s \in \mathbb{R}^n$ , not necessarily a probability distribution over the vertices of the graph, we define  $\operatorname{pr}_{\alpha}(s)$  as the unique solution of Equation (1).

$$\textbf{Proposition 3 (Linearity)} \ \operatorname{pr}_{\alpha}(cv+dw) = c \cdot \operatorname{pr}_{\alpha}(v) + d \cdot \operatorname{pr}_{\alpha}(w).$$

 $<sup>^{1}</sup>$ Google uses the directed version, because hyperlinks "go only one way".

<sup>&</sup>lt;sup>2</sup>A matrix is strictly diagonally dominant if  $a_{ii} > \sum_{j \neq i} |a_{ji}|$  for all i.

**Proof** By definition, the vector  $x \equiv \operatorname{pr}_{\alpha}(cv + dw)$  satisfies the following equation

$$x = \alpha(cv + dw) + (1 - \alpha)Wx .$$

Let us verify that  $x' \equiv c \operatorname{pr}_{\alpha}(v) + d \operatorname{pr}_{\alpha}(w)$  satisfies the same equation:

$$\begin{split} \alpha(cv+dw) + (1-\alpha)Wx' &= \alpha(cv+dw) + (1-\alpha)W(c\mathsf{pr}_\alpha(v) + d\mathsf{pr}_\alpha(w)) \\ &= \alpha cv + (1-\alpha)Wc\mathsf{pr}_\alpha(v) + \alpha dw + (1-\alpha)Wd\mathsf{pr}_\alpha(w) \\ &= c\mathsf{pr}_\alpha(v) + d\mathsf{pr}_\alpha(w) \\ &= x' \ . \end{split}$$

By Proposition 2, the equation has a unique solution, so that x = x' and the result follows.

Proposition 4 (Commutativity with W)  $\operatorname{pr}_{\alpha}(Ws) = W \operatorname{pr}_{\alpha}(s)$ .

**Proof** By definition, the vector  $x \equiv \operatorname{pr}_{\alpha}(Ws)$  satisfies the following equation

$$x = \alpha(cv + dw) + (1 - \alpha)Wx .$$

Let us verify that  $x' \equiv W \operatorname{pr}_{\alpha}(s)$  satisfies the same equation:

$$\begin{split} \alpha(cv+dw) + (1-\alpha)Wx' &= \alpha Ws + (1-\alpha)W^2 \mathrm{pr}_{\alpha}(s) \\ &= W(\alpha s + (1-\alpha)W \mathrm{pr}_{\alpha}(s)) \\ &= W \mathrm{pr}_{\alpha}(s) \\ &= x' \enspace . \end{split}$$

By Proposition 2, the equation has a unique solution, so that x = x' and the result follows.

As a corollary of Propositions 2 and 4, we deduce that  $pr_{\alpha}(s)$  is the unique solution to

$$\operatorname{pr}_{\alpha}(s) = \alpha s + (1 - \alpha)\operatorname{pr}_{\alpha}(Ws) . \tag{2}$$

#### 3.3 Approximating PageRank

We would like to come up with a fast way to find an approximation to the unique solution  $\operatorname{pr}_{\alpha}(s)$  of Equation (1). We now describe an iterative procedure that does that.

We maintain two vectors p, the approximation vector, and r, the error vector, that satisfy the following invariant

$$p = \operatorname{pr}_{\alpha}(s - r) \ .$$

Starting with initial values p = 0 and r = s, in each iteration, we pick a vertex u, and update the two vectors p and r to the new vectors p' and r' defined as follows:

$$p' = p + \alpha r(u)\chi_u ,$$
  

$$r' = r - r(u)\chi_u + (1 - \alpha)r(u)W\chi_u .$$

The vector  $\chi_u$  is the *characteristic vector* of u, i.e., the vector with a 1 in the coordinate corresponding to vertex u and 0 elsewhere. Given a fixed  $\epsilon > 0$ , we keep iterating as long as there exists some vertex u such that  $r(u) \geq \epsilon d(u)$ .

First, we prove that each iteration of the algorithm preserves the invariant  $p = \operatorname{pr}_{\alpha}(s-r)$ .

**Proposition 5**  $p' = \operatorname{pr}_{\alpha}(s - r')$ .

**Proof** By Proposition 3, it suffices to show that  $p' + \operatorname{pr}_{\alpha}(r') = p + \operatorname{pr}_{\alpha}(r)$ . So let us verify that:

$$\begin{split} p + \mathrm{pr}_{\alpha}(r) &= p + \mathrm{pr}_{\alpha}(r - r(u)\chi_u) + \mathrm{pr}_{\alpha}(r(u)\chi_u) \\ &= p + \mathrm{pr}_{\alpha}(r - r(u)\chi_u) + \alpha r(u)\chi_u + (1 - \alpha)\mathrm{pr}_{\alpha}(Wr(u)\chi_u) \\ &= (p + \alpha r(u)\chi_u) + \mathrm{pr}_{\alpha}(r - r(u)\chi_u + (1 - \alpha)r(u)W\chi_u) \\ &= p' + \mathrm{pr}_{\alpha}(r') \enspace . \end{split}$$

where the third equation resulted from an application of Equation (2).

Next, we prove a bound on the error vector.

**Proposition 6**  $||r'||_1 \le ||r||_1 - \alpha r(u)$ .

**Proof** Using the triangle inequality.

$$||r'||_1 = ||r - r(u)\chi_u + (1 - \alpha)r(u)W\chi_u||_1 \le ||r - r(u)\chi_u||_1 + (1 - \alpha)r(u)||W\chi_u||_1$$
.

However,  $||W\chi_u||_1 \le 1$ . Indeed, the *i*th element of  $W\chi_u$  is  $\frac{1}{2d(u)}$  when  $i \ne u$  and  $\frac{1}{2}$  when i = u. Therefore,

$$||r'||_1 \le ||r||_1 - r(u) + (1 - \alpha)r(u) = ||r||_1 - \alpha r(u)$$
,

as desired.

Finally, we prove that the iterative procedure works.

**Theorem 7** Fix  $\epsilon > 0$ . Suppose that in each iteration we pick a vertex u with the property that  $r(u) \ge \epsilon d(u)$ . Then the process terminates in  $O(\frac{1}{\epsilon \alpha})$  iterations with vectors p and r that satisfy the following properties:

- 1.  $\max_{v} \frac{r(v)}{d(v)} \le \epsilon$ .
- 2.  $\operatorname{vol}(\operatorname{supp}(p)) \leq \frac{1}{\epsilon \alpha}$ , where  $\operatorname{supp}(p)$  is the set of vertices for which p is nonzero and  $\operatorname{vol}(S) \equiv \sum_{x \in S} d_x$ .

**Proof** Initially,  $||r||_1 = 1$ . By Proposition 6,  $||r||_1$  decreases at each iteration by  $\alpha r(u)$ , which by assumption is at least  $\alpha \epsilon d(u)$ . Therefore, since the degree of each vertex is at least 1,  $||r||_1$  decreases at each iteration by at least  $\alpha \epsilon$ . We deduce that the algorithm must terminate in at most  $O(\frac{1}{\epsilon \alpha})$  iterations.

Next, by definition, the process terminates when there are no more vertices u such that  $r(u) \geq \epsilon d(u)$ . Therefore, condition (1) is automatically satisfied.

Moreover, if we let T denote the number of iterations that the algorithm takes to terminate and let  $d_i$  denote the degree of the vertex picked in the ith step of the algorithm, then  $\alpha \epsilon \sum_{i=1}^{T} d_i \leq 1$ , so that  $\sum_{i=1}^{T} d_i \leq \frac{1}{\epsilon \alpha}$ . Now note that every vertex in  $\operatorname{supp}(p)$  must have been picked at least once during the execution of the algorithm, so that

$$\operatorname{vol}(\operatorname{supp}(p)) \leq \sum_{i=1}^T d_i \leq \frac{1}{\epsilon \alpha} \ ,$$

thus showing (2), and completing the proof of the theorem.

The theorem we just proved gives the approximation to the PageRank vector that we need, and we finally get a local clustering algorithm. Note that to find a cut C we need  $\epsilon = O(1/\text{vol}(C))$ , so that the running time of the process is proportional to  $\frac{\text{vol}(C)}{\alpha}$ .

In order to obtain from this an almost-linear global partitioning algorithm, we do as follows. Let us suppose that  $\phi(G)$  is  $\mathsf{polylog}(n)$ . If we pick a random vertex v in a cluster of vertices C with conductance  $\phi^2$ , we will find with probability at least 0.5 a set with volume at least  $\mathsf{vol}(C)/2$ . However, this holds only if we use "appropriate" parameters  $\alpha$  and  $\epsilon$ , which we do not know! The fix is to binary search over the

possibilities, incurring an additional cost that is only a logarithmic multiplicative factor. In conclusion, we can find a globally optimal  $\phi$  (up to the usual squaring error times some log factors) by cutting off chunks of the graph and repeating. The total running time is almost linear because the running time on each chunk is almost linear in its volume.

Caveat. In a random walk scheme, we need to take  $1/\phi$  steps in order to get a cut of conductance  $1/\sqrt{\phi}$ ; hence, that takes time that is about (size of chunk)  $\cdot$  poly( $1/\phi$ ). Similarly, in a PageRank scheme, we need to take  $1/\alpha$  steps in order to get a cut of conductance  $1/\sqrt{\alpha}$ ; again, that takes time that is about (size of chunk)  $\cdot$  poly( $1/\phi$ ). As a consequence, the algorithm will run in time that is almost linear times some poly( $1/\phi$ ), which is almost linear only if  $\phi$  is at least polylog(n). Improving this for smaller conductances is still an open problem.

# 4 Intro to Sparsification

Sparsification is a technique used in dynamic graph algorithms to reduce the dependence of an algorithm's time on the number of edges in a graph. We briefly motivate this technique now, and will discuss it next time

Suppose that we have a graph G = (V, E) with  $m = \Theta(n^2)$  edges. We would like to solve some cut problem (e.g., sparsest cut, min cut, s-t min cut). Most algorithms that solve these kinds of problems have running times that typically grow with m, the number of edges in the graph. As a consequence, such algorithms are much slower for dense graphs than for sparse graphs.

It would be really nice if we could somehow throw out a lot of edges from G and still get an approximate answer, because the running time of the algorithm for the resulting graph will be close to that for a sparse graph. More precisely, is there any way to "approximate" our graph G with a *sparse* graph G' that has the property that all of its cuts have more or less the same size as the original graph G?

To answer this question, next time we will introduce the idea of *randomized sampling*. It is not a spectral technique, but we will discuss spectral techniques that improve it.

# References

- [1] Reid Andersen, Fan Chung, and Kevin Lang. Local Graph Partitioning using PageRank Vectors. In FOCS '06: Proceedings of the 47th Annual IEEE Symposium on Foundations of Computer Science, pages 475–486, Washington, DC, USA, 2006. IEEE Computer Society. Full version available at http://www.math.ucsd.edu/~fan/wp/localpartfull.pdf. 8-2, 8-3
- [2] Gershgorin circle theorem. http://en.wikipedia.org/wiki/Gershgorin\_circle\_theorem 8-3
- [3] Nathan Linial and Avi Wigderson. Expander Graphs And Their Applications. http://www.math.ias.edu/~boaz/ ExpanderCourse/ 8-1
- [4] László Lovász and Miklós Simonovits. The mixing rate of Markov chains, an isoperimetric inequality, and computing the volume. In FOCS '90: Proceedings of the 31st Annual IEEE Symposium on Foundations of Computer Science, pages 346–354, Washington, DC, USA, 1990. IEEE Computer Society. 8-1

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### 18.409 An Algorithmist's Toolkit

10/8/2009

## Lecture 9

Lecturer: Jonathan Kelner

At the end of the previous lecture, we began to motivate a technique called Sparsification. In this lecture, we describe sparsifiers and their use, and give an overview of Combinatorial and Spectral Sparsifiers. We also define Spectral Sparsifiers, and create tools and language with which to construct and analyze them.

# 1 Sparsification

Suppose we are given a graph G = (V, E). We would like to solve some cut problem (i.e. min-cut, s-t min cut, sparsest cut) and so on. The running time of algorithms for these problems typically depends on the number of edges in the graph, which might be as high as  $O(n^2)$ . Is there any way to approximate our graph with a sparse graph G' in which all cuts are approximately of the same size?

We will describe two ways of "sparsifying" our graph. The first is the method of Benczur-Karger, and relies on random sampling of edges. The second technique is Spectral Sparsification, and uses spectral techniques to improve upon Benczur-Karger's algorithm.

## 1.1 First Try

Our first attempt at sparsifying will use random sampling. Let's start by sampling each edge with probability p. Then, if a cut has c edges crossing it in G, the expected value of edges crossing it in the new graph G' is pc. Our algorithm will solve the cut problem in G'. Say the answer is a cut with value S'; then our algorithm will output the estimate S = S'/p for the original graph G.

Denoting the number of edges between S and  $\bar{S}$  by e(S) = pc, we have the following concentration result due to Chernoff's inequality:

$$P(|e_{G'}(S) - pc| \ge \epsilon pc) \ge e^{-\epsilon^2 pc/2}.$$
 (1)

So our result will be close to the correct answer provided pc is large. In particular, picking

$$p = \Omega(\frac{d\log n}{\epsilon^2 c}),$$

will make the right side of Eq. (1) at most  $n^{-d}$ . Summarizing, we can choose p to get an  $\epsilon$  multiplicative approximation with probability at least  $1 - n^{-d}$ .

Is it possible to choose p to get this multiplicative approximation for all cuts, rather than just one as above? The answer is yes; the main ingredient is a result of Karger that the number of small cuts in a graph is not too large:

**Theorem 1 (Karger)** If G has a min-cut of size c, then the number of cuts of value  $\alpha c$  or less is at most  $n^{2\alpha}$ .

### 1.2 Second try

The problem with this proposal is that it breaks for small cuts. Say c is small, but an edge e is only involved in cuts of size  $\geq k$ . What we want to do is to sample these edges with a small probability of failure.

The idea that we use is to sample edges, but with a "weight" of 1/p. This method is called importance sampling. To do this, we need a slightly modified version of the Chernoff bound:

**Theorem 2 (Chernoff Bound)** Let  $X_1, \ldots, X_n$  be random variables so that  $X_i \in [0, 1]$ , and let  $X = \sum X_i$ . Then,

$$Pr[|X - E[X]| \ge \epsilon X] \le 2e^{-\Theta(1)\epsilon^2 E[X]}$$

**Proof** The only difference here is that the random variables  $X_i$  are no longer discrete variables, but lie in the interval [0,1]. The proof is carried out the same as with the regular Chernoff bound.

What this allows us to do is to scale our random variables without changing the error bounds. Returning to our case, we assign to every edge e a random variable  $Y_e$  and a weight  $w_e$ . If e is in a cut of size c, we require that  $w_e \leq c$ . We will set  $Y_e = 1$  with probability  $p/w_e$ ; and  $Y_e = 0$  with probability  $1-p/w_e$ . Instead of counting how many edges cross a cut  $(S, \bar{S})$ , we will compute a weighted sum:

$$Y_S = \sum_{e \in \partial(S,\bar{S})} w_e Y_e$$

The expectation is still correct; if there are c edges across the cut  $(S, \bar{S})$  in G, then

$$E[Y_S] = \sum_{e \in \partial(S,\bar{S})} w_e \frac{p}{w_e} = pc.$$

This scheme gives us an advantage: if an edge is present in only cuts of large size, we can keep it with low probability, which corresponds to setting  $w_e$  to be large. On the other hand, if an edge is present in cuts of small size, we will keep it with high probability, which corresponds to setting  $w_e$  to be small. In this way, we can approximate cut problems while throwing away more edges which are present in only cuts of high size.

Thus, a natural choice for  $w_e$  would be the size of the smallest cut containing e. Unfortunately, we do not know  $w_e$ ; however, it is possible to approximate it quickly. The final result is an  $\epsilon$  multiplicative approximation based on this scheme. We refer the reader to [1] for details.

# 2 Spectral Sparsifiers

The construction shown above is known as a *Combinatorial Sparsifier*. In the upcoming section and following lecture, we will see how to improve upon it with the spectral methods that we have been learning.

Let G = (V, E) be our original graph. Recall that the laplacian has the property that

$$x^{T}L_{G}x = \sum_{(i,j)\in E} (x_{i} - x_{j})^{2},$$

for some  $x \in \mathbb{R}^n$ , and the sum is being taken over all edges in G. If x takes value 1 on the set S and -1 on the  $\bar{S}$ , this equation becomes

$$x^T L_G x = 4e(S).$$

Let G' be a combinatorial sparsifier of the graph G. The condition that all cuts in G are approximated with a multiplicative error of at most  $\epsilon$  by cuts in G' can be restated as

$$(1 - \epsilon)x^T L_{G'} x \le x^T L_G x \le (1 + \epsilon)x^T L_{G'} x, \tag{2}$$

for all x that take on only the values 1 and -1. This is true for all such discrete values of x.

On the other hand, consider if Eq. (2) is true for all  $x \in \mathbb{R}^n$ . Note that in this case we can limit ourselves to the instances  $x \in [-1,1]^n$  by normalization. We now have a good definition for a spectral version of sparsification:

**Definition 3** A Spectral Sparsifier G' of a graph G is one for which the relation

$$(1 - \epsilon)x^T L_{G'} \le x^T L_G x \le (1 + \epsilon)x^T L_{G'} x$$

for all  $x \in [0,1]^n$ 

It is clear from this definition that spectral sparsifiers are combinatorial sparsifiers. A natural question is then to ask if all combinatorial sparsifiers also spectral sparsifiers.

The answer is no, and we provide a proof by counterexample. Consider the graph G' with vertex set  $\{1, 2, ..., n\}$  and an edge between i, j when  $i - j \mod n \le k$ . G is G' with the edge (1, n/2) added. The graph looks something like the figure below.

Then, for an appropriate  $\epsilon$ , G' is a combinatorial sparsifier of G. Indeed, the min cut in G cuts  $\Theta(k)$  edges; the min cut in G' cuts one less. With  $\epsilon = \Theta(1/k)$ , we have that G' is a combinatorial sparsifier of G. On the other hand, G' is not a spectral sparsifier of G. Let

$$x = (0 \ 1 \ \dots \ n/2 - 1 \ n/2 - 1 \ \dots \ 1 \ 0).$$

Then, we have that

$$x^T L_{G'} x = \Theta(nk^3)$$

since each vertex contributes  $\Theta(\sum_{i=1}^k k^2)$  to the sum. On the other hand,

$$x^{T}L_{G}x = \Theta(nk^{3}) + (\frac{n}{2} - 1)^{2}$$

If k is constant, we get that we need  $\epsilon = \Theta(1/n)$  for G' to be a spectral sparsifier of G.

### 2.1 Order Relations on Laplacians

In order to define spectral approximations, we first need to define the appropriate vocabulary. Earlier, we made error approximations based on cut size. In the spectral case, we will be using the laplacian of the graph instead - so a nice way to compare laplacians would be idea. That is to say, we want a good relation  $\succeq$  on symmetric matrices that is an ordering on them, and also is somewhat consistent with the notions of cuts.

How will we define this ordering? An immediate idea is the following:

$$M \succeq N \Leftrightarrow m_{i,j} \geq n_{i,j} \forall i, j$$

Upon second thought, we realize that this is no good for our purposes. For one, spectral graph theory is all about eigenvalues, and this relation tells us nothing about the eigenvalues of the matrix! Furthemore, the values of individual entries are highly dependent on choice of basis, which would be bad. If such a definition were used, a process like diagonalizing the Laplacians could possibly affect the graph orders.

We try again with another definition:

$$M \succeq N$$
 if the  $i^{th}$  eigenvalue of  $M$  is  $\geq$  the  $i^{th}$  eigenvalue of  $N$  for all indices  $i$ 

This is better in that it is basis independent - but it is too basis independent. Under this definition, we have both

$$\left(\begin{array}{cc} 1 & 0 \\ 0 & -1 \end{array}\right) \succeq \frac{1}{\sqrt{2}} \left(\begin{array}{cc} 1 & 1 \\ 1 & -1 \end{array}\right)$$

as well as

$$\frac{1}{\sqrt{2}} \left( \begin{array}{cc} 1 & 1 \\ 1 & -1 \end{array} \right) \succeq \left( \begin{array}{cc} 1 & 0 \\ 0 & -1 \end{array} \right)$$

After this experimentation, we claim that the following is the "right" definition of order.

**Definition 4** We write that  $M \succeq N$  if

$$x^T M x > X^T N x \ \forall x \in \mathbb{R}^n$$

Note that this definition of order has the following properties:

- 1. If  $M \succeq N$  and  $N \succeq M$ , then M = n
- 2.  $M \succeq 0$  if M is a positive semidefinite matrix.
- 3.  $M \succ N$  if M N is positive semidefinite
- 4. If  $M_1 \succeq N_1$  and  $M_2 \succeq N_2$ , then

$$M_1 + M_2 \succeq N_1 + N_2$$

These properties suffice for our purposes, and with this, we can define an associated order on graphs as well.

**Definition 5** Given graphs G and H, say that  $G \succeq H$  if  $L_G \succeq L_H$ .

**Claim 6** Let  $G = (V, E_G, w_G)$  and  $H = (V, E_H, w_H)$  be weighted graphs on the same vertex set such that  $w_G(i,j) \ge w_H(i,j)$  for all edges  $(i,j) \in E$ . Then,  $G \succeq H$ 

#### 2.2 Towards Spectral Sparsification

With this order relation on graphs, we can now restate the goal of spectral sparsification: Given a dense graph G, we want to create a sparse graph H where

$$L_h \leq L_G \leq (1+\epsilon)L_H$$

By "sparse," we mean that H has polylog(n) edges, where n is the number of nodes. We will show in this and the next lecture how to construct spectral sparsifiers with O(nlogn) edges in Polynomial time. This can actually be improved to a linear time construction, but will use geometric techniques that we will learn. Moreover, it is possible to construct O(n) edge sparsifiers in polynomial time. The benefits of this are that the problem is more geometrically flavored. It is also a nice example of how generalizing can make things easier sometimes.

The algorithm that we propose is very simple. It is similar in structure to the B-K algorithm, but we use different probabilities for sampling the edges.

- Compute probability  $p_e$  for each edge e.
- Sample each edge uniformly with probability  $p_e$ , and if an edge is selected, include it with weight  $1/p_e$ .

These probabilities are based on a linear algebra sense of importance, and have a nice interpretation in terms of effective resistance of circuits. To proceed with our analysis, however, we need to develop the ideas of pseudoinverses, calculating effective resistances, and a matrix version of the Chernoff Bound.

#### 2.3 Pseudoinverses

In our analysis, we will come across the need to "invert" a singular matrix. Since this is obviously not possible, we redefine our question to one that makes more sense. Let M be a  $n \times n$  symmetric matrix. We can diagonalize M:

$$M = \sum_{i=1}^{n} \lambda_i v_i v_i^T$$

If all the eigenvalues are nonzero, then it obviously invertible, and  $M^{-1} = \sum_{i=1}^{n} \frac{1}{\lambda_i} v_i v_i^t$ 

The case we worry about is when there is a zero eigenvalue. But this is okay too: when M is degenerate, we define the *pseudoinverse* by throwing away the zero eigenvalues and eigenvectors. In that case, we have

$$M^{+} = \sum_{i \mid \lambda_i \neq 0} \frac{1}{\lambda_i} v_i v_i^T$$

The pseudoinverse has many nice properties. Of these, we use:

- $ker(L) = ker(L^+)$
- $MM^+ = \sum_{i|\lambda_i \neq 0} v_i v_i^T$  = the projection onto the nonzero eigenvectors.

It is easy to see that  $MM^+ = I$  when restricted to the image of M.

#### 2.4 Effective Resistance

We mentioned earlier that Spectral Sparsification also samples edges with different probability. It turns out that the correct way to do this is to sample each edge with probability proportional to its "effective resistance."

The basic idea is to treat each edge as a resistor with resistance 1. If the edge had a capacity of c, we give it a resistance of 1/c. After calculating these values, we sample the edge (u, v) with probability proportional to the effective resistance between nodes u and v.

Students may recall learning methods to solve circuits from their previous classes. For example, students may use a combination of Ohm's law and Kirchoff's law, as well as the rules for calculating effective resistances of resistors in series and parallel. To those who are comfortable with solving circuits, this may be a good way to think about the problem. However, the students who don't like solving circuits are in luck too: now that we have the tools of Spectral Graph Theory, we can solve circuits with only linear algebra! In fact, we will combine our frequent use of the graph Laplacian with the pseudoinverse defined above.

Let U be the edge-vertex adjacency matrix, C be the diagonal matrix with the various capacitances, and  $r_e = 1/c_e$ .

That is, we define U as in:

$$U(e,v) = \begin{cases} 1 & \text{if } v \text{ is the head of } e \\ -1 & \text{if } v \text{ is the tail of } e \\ 0 & \text{otherwise} \end{cases}$$

Then, we have that  $L=U^TCU$ . From ohm's law, we have i=CUv for  $i\in\mathbb{R}^E$ , and  $v\in\mathbb{R}^v$ . From the conservation of current, we have  $i_{ext}=U^Ti$ , for  $i_{ext}\in\mathbb{R}^V$ . Finally, we have  $i_{ext}=Lv$ , and  $v=L^+i_{ext}$ 

We define U(e, v) to be the adjacency matrix with  $\pm 1$  values. Let  $u_e$  be the  $e^{th}$  row, and  $v = L^+ i_e xt$ . We have

$$R_{eff}(e) = u_e L^+ u_e^T$$

and as a result.

$$R_{eff}(e) = (UL^+U^T)_{e,e}$$

Thus, calculating the effective resistance of an edge is as simple as calculating the pseudoinverse of the Laplacian. Simple!

#### 2.5 Error Bounds

The last tool that we need to build is a way to define error bounds for matrices. In particular, we will use the following theorem.

**Theorem 7** For distributions on vectors y where  $||y|| \le t$  and  $||Eyy^t||_2 \le 1$  (where we are using the  $l_2$  norm) then:

$$E \parallel Eyy^T - \frac{1}{q} \sum_{i=1}^q y_i y_i^T \parallel_2 \le kt \sqrt{\frac{\log q}{q}}$$

This is a "concentration of measure theorem, and we claim that it is similar to the Chernoff bound.

Now, onto approximation. For our sparisifier H to approximate the original dense graph G, we want that

$$1 - \epsilon \le \frac{x^T L_H x}{x^T L_C x} \le 1 + \epsilon$$

for all vectors x. Rather, it is sufficient to show that

$$1 - \epsilon \le \frac{z^T M^T L_H M z}{z^T M^T L_C M z} \le 1 + \epsilon$$

for all vectors z, provided that  $x \perp (L_G) \Rightarrow x \in range(M)$ . Choose M so that  $M^T L_G M$  is a projection. Then, it suffices to show that

$$\parallel M^T L_H M - M^T L_G M \parallel_2 \le \epsilon$$

From before, we have that  $L_G = U^T C U$ . Choose  $M = L_C^+ U^T C^{1/2}$ . Then, we have

$$\Pi = M^T L_G M = C^{1/2} U L_C^+ U^T C^{1/2} = \Pi \Pi$$

Now, recall that  $L_G = U^T C U$ . If we let  $d_e$  be the weight of e in the sparsifier H, set  $S_{e,e} = \frac{d_e}{c_e}$ . Then, we can write

$$L_H = U^T C S U = U^T C^{1/2} S C^{1/2} U$$

yielding

$$M^T L_H M = \Pi S \Pi$$

We need to choose a diagonal S such that the number of nonzero elements of S is  $O(nlog n/\epsilon^2)$  With this choice, we have

$$\|\Pi S\Pi - \Pi\|_2 \le \epsilon$$

Define  $\pi_e$  as the  $e^{th}$  column of  $\Pi$ : that is,  $\pi_e = \Pi(\cdot, e)$ . Then,  $\Pi S \Pi = \sum S_{e,e} \pi_e \pi_e^T$ , so

$$\| \pi_e \|^2 = \Pi_{e,e} = c_e R_{eff}(e)$$

(this is because  $\Pi=\Pi^2=C^{1/2}(UL_G^+U^T)C^{1/2})$ 

We then set  $\tau_e = \sqrt{\frac{n-1}{c_e R_{eff}(e)}} \pi_e$  with  $\| \tau_e \| = \sqrt{n-1}$ . Choose edges with probability  $p_e = \frac{c_2 R_{eff}(e)}{n-1}$ . Recall that

$$\sum_{e} c_e R_{eff}(e) = \sum_{e} \Pi_{e,e} = n - 1$$

Then, we find that

$$E[\tau_e \tau_e^T] = \sum_e p_e \tau_e \tau_e^T = \sum_e \pi_e \pi_e^T = \Pi$$

Sample q times with replacement, and set  $S(e,e) = \frac{1}{qc_eR_{eff}(e)} \times$  the number of times that e is chosen. Then, from the theorem above, we have

$$E[\parallel \Pi - \Pi S \Pi \parallel_2] \leq k \sqrt{n-1} \sqrt{\frac{logq}{q}} \leq \epsilon/2$$

for  $q = O(n \log n/\epsilon^2)$ . Thus, we see that our construction yields a spectral sparsifier as desired.

From the algorithmics of the construction, it is easy to see that this is a poly-time procedure. The whole procedure is constructive, and uses the standard linear algebra operations. The bottleneck in this procedure comes from computing effective resistances, and in particular, the matrix inversions and multiplications. We claim that the procedure can be improved to nearly linear time. Doing so would involve two components:

- Close to linear algorithms for solving linear equations of the form Lx = b for a laplacian L.
- A way to compute all the effective resistances by solving logarithmically many linear systems. This uses the Johnson-Lindenstrauss Lemma.

# References

[1] "Randomized Approximation Schemes for Cuts and Flows in Capacitated Graphs," A. Benczur, D. Karger, manuscript.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 18.409 | $\mathbf{A}\mathbf{n}$ | Algo | rithr | $\mathbf{nist's}$ | Toolk | $\operatorname{cit}$ |
|--------|------------------------|------|-------|-------------------|-------|----------------------|
|--------|------------------------|------|-------|-------------------|-------|----------------------|

10/15/2009

Lecture 10

Lecturer: Jonathan Kelner

In this lecture, we shall revisit the Spectral Sparsifiers and see a slightly different proof from last time. We will then begin a new topic: Convex Geometry.

## 1 Spectral Sparsification

Given a dense graph G, we would like want to create a sparse graph H where

$$L_h \preceq L_G \preceq (1+\epsilon)L_H$$

By "sparse," we mean that H has n.polylog(n) edges, where n is the number of nodes. More precisely, we show how to construct a spectral sparsifiers with O(nlogn) edges in Polynomial time. This can actually be improved to a linear time construction, but will use geometric techniques that we will learn. It is possible to construct O(n) edge sparsifiers in polynomial time. It is also a nice example of how generalizing can make things easier sometimes. The algorithm that we propose is very simple. It is similar in structure to the B-K algorithm, but we use different probabilities for sampling the edges.

- Compute probability  $p_e$  for each edge e.
- Sample each edge uniformly with probability  $p_e$ , and if an edge is selected, include it with weight  $1/p_e$ .

These probabilities are based on a linear algebra sense of importance, and have a nice interpretation in terms of effective resistance of circuits. To proceed with our analysis, however, we need to develop the ideas of pseudoinverses, calculating effective resistances, and a matrix version of the Chernoff Bound.

#### 1.1 Laplacians and Electrical Flow

We mentioned earlier that Spectral Sparsification can be viewed as sampling edges with different probability. It turns out that the correct way to do this is to sample each edge with probability proportional to its "effective resistance." The basic idea is to treat each edge as a resistor with resistance 1. If the edge had a capacity of c, we give it a resistance of 1/c. After calculating these values, we sample the edge (u, v) with probability proportional to the effective resistance between nodes u and v. For example, students may use a combination of Ohm's law and Kirchoff's law, as well as the rules for calculating effective resistances of resistors in series and parallel. To those who are comfortable with solving circuits, this may be a good way to think about the problem. However, the students who don't like solving circuits are in luck too: now that we have the tools of Spectral Graph Theory, we can solve circuits with only linear algebra! In fact, we will combine our frequent use of the graph Laplacian with the pseudoinverse defined above. We orient the edges arbitrarily and define U to be the edge-vertex adjacency matrix. That is, we define U as in:

$$U(e, v) = \begin{cases} 1 & \text{if } v \text{ is the head of } e \\ -1 & \text{if } v \text{ is the tail of } e \\ 0 & \text{otherwise} \end{cases}$$

We then let  $L = U^T U$ . From ohm's law, we have  $iR_{eff} = Uv$  for  $i \in \mathbb{R}^E$  and  $v \in \mathbb{R}^v$ . From the conservation of current, we have  $i_{ext} = U^T i$ , for  $i_{ext} \in \mathbb{R}^V$ . Finally, we have  $i_{ext} = Lv$ , and  $v = L^+ i_{ext}$  Let  $u_e$  be the  $e^{th}$  row of U (as defined in the prequel), and  $v = L^+ i_e xt$ . We have

$$R_{eff}(e) = u_e L^+ u_e^T$$

and as a result,

$$R_{eff}(e) = (UL^+U^T)_{e,e}$$

Thus, calculating the effective resistance of an edge is as simple as calculating the pseudoinverse of the Laplacian. Simple!

### 1.2 Towards Approximation

To show that H is a spectral sparsifier of G if suffices to show that

$$(1 - \epsilon)x^T L_G x \le x^T L_H x \le (1 + \epsilon)x^T L_G x, \quad \forall x$$

For this, it suffices to show that,  $\forall y$ ,

$$(1 - \epsilon) \le \frac{y^T (L_G^+)^{\frac{1}{2}} L_H(L_G^+)^{\frac{1}{2}} y}{y^T (L_G^+)^{\frac{1}{2}} L_G(L_G^+)^{\frac{1}{2}}} \le (1 + \epsilon), \quad \text{(Just take } y = L_G^{\frac{1}{2}} x\text{)}$$

Equivalently, need to show that

$$\| (L_G^+)^{\frac{1}{2}} L_H(L_G^+)^{\frac{1}{2}}) - I_{im(L_G} \|_2 \le \epsilon$$

We will use the following theorem (in which k is a universal constant):

**Theorem 1 (RV Theorem)** For distributions on vectors y where  $||y|| \le t$  and  $||Eyy^t||_2 \le 1$  (where we are using the  $l_2$  norm) then:

$$E \parallel Eyy^T - \frac{1}{q} \sum_{i=1}^q y_i y_i^T \parallel_2 \le kt \sqrt{\frac{\log q}{q}}$$

This is a "concentration of measure theorem" (similar to Chernoff bounds).

$$L_{G} = \sum_{e \in E} L_{e} = \sum_{e \in E} u_{e} u_{e}^{T}$$

$$I_{im(L_{G})} = L_{G}^{+})^{\frac{1}{2}} L_{G} (L_{G}^{+})^{\frac{1}{2}}$$

$$= \sum_{e \in E} L_{G}^{+})^{\frac{1}{2}} L_{e} (L_{G}^{+})^{\frac{1}{2}}$$

$$= \sum_{e \in E} L_{G}^{+})^{\frac{1}{2}} U_{e} U_{e}^{T} (L_{G}^{+})^{\frac{1}{2}}$$

$$= \sum_{e \in E} q_{e} q_{e}^{T}, \text{ where } q_{e} = (L_{G}^{+})^{\frac{1}{2}} u_{e}$$

$$\parallel q_{e} \parallel^{2} = u_{e}^{T} L_{G}^{+})^{\frac{1}{2}} L_{G}^{+})^{\frac{1}{2}} u_{e}$$

$$= u_{e} L^{+}) u_{e} = R_{eff}(e)$$

$$I_{im(L_G)} = \sum_{e \in E} q_e q_e^T$$
 and  $\parallel q_e \parallel^2 = R_{eff}(e)$ 

We would like all the vectors of same length, so set  $\tau_e = \sqrt{\frac{n-1}{c_e R_{eff}(e)} \pi_e}$  with  $\parallel \tau_e \parallel = \sqrt{n-1}$ . Now make a distribution which picks  $\tau_e$  with probability  $p_e = \frac{c_2 R_{eff}(e)}{n-1}$ . Recall that

$$\sum_{e} c_{e} R_{eff}(e) = \sum_{e} \Pi_{e,e} = n - 1$$

Then, we find that

$$E[\tau_e \tau_e^T] = \sum_e p_e \tau_e \tau_e^T = \sum_e q_e q_e^T = I_{im(L_G)XS}$$

Sample q times with replacement, and set  $S(e,e) = \frac{1}{qc_eR_{eff}(e)} \times$  the number of times that e is chosen. Then, from the theorem above, we have

$$E[\| (L_G^+)^{\frac{1}{2}} L_H(L_G^+)^{\frac{1}{2}}) - I_{im(L_G} \|_2] \le k\sqrt{n-1} \sqrt{\frac{\log N}{N}} \le \epsilon, \forall N = \theta(n \log n / \epsilon^2)$$

•

### 1.3 Algorithmics of the Construction

Thus, we see that our construction yields a spectral sparsifier as desired. From the algorithmics of the construction, it is easy to see that this is a poly-time procedure. The whole procedure is constructive, and uses the standard linear algebra operations. The bottleneck in this procedure comes from computing effective resistances, and in particular, the matrix inversions and multiplications. We claim that the procedure can be improved to nearly linear time. Doing so would involve two components:

- Close to linear algorithms for solving linear equations of the form Lx = b for a laplacian L.
- A way to compute all the effective resistances by solving logarithmically many linear systems. This uses the Johnson-Lindenstrauss Lemma.

### 1.4 Spectral Sparsification is Easy

- Pick  $N \tau_e$  vectors with replacement from this distribution.
- Take an edge e with weight:

$$\frac{1}{N.R_{eff}(e) \times (\text{ number of times chosen })}$$

- Note: Bigger q vectors get picked with higher probability, but are scaled down more!
- By R-V Theorem,

$$E[\| (L_G^+)^{\frac{1}{2}} L_H(L_G^+)^{\frac{1}{2}}) - I_{im(L_G} \|_2] \le k\sqrt{n-1}\sqrt{\frac{\log N}{N}} \le \epsilon, \forall N = \theta(n\log n/\epsilon^2)$$

.

# 2 Convex Geometry

This lecture we will just have many examples to build intuition. Next lecture we will start proving theorems.

**Definition 2** We say a set  $C \subseteq \mathbb{R}^n$  is convex when for all  $x, y \in C$  and  $t \in [0, 1]$ ,  $tx + (1 - t)y \in C$ . A function  $f : \mathbb{R}^n \to \mathbb{R}$  is convex iff the region above its graph (in  $\mathbb{R}^{n+1}$ ) is convex. A function  $f : \mathbb{R}^n \to \mathbb{R}$  is concave iff -f is convex. A convex body is a convex set which is both compact and has non-empty interior.

Keith Ball can be quoted as saying "All convex bodies behave a lot like Euclidean balls". This claim is "almost true" if one adds a few extra shapes: the ball, ellipsoid, cube, regular simplex, cross-polytope, and spherical cone (and all linear transformations of these shapes). Of course, this is not a formal statements: one can easily construct theorems which are satisfied for these shapes but not some other convex bodies. The point here is that for "most" theorems one would want to prove about convex bodies, if there were a counter-example there is a good chance that one of these shapes would be it.

We now give formal definitions of the shapes mentioned.

- 1. The Euclidean ball  $B_2^n$  is the set  $\{x \in \mathbb{R}^n \mid ||x||_2^2 \le 1\}$ .
- 2. The *ellipsoid* E is the set  $\{x \in \mathbb{R}^n \mid x^T A x \leq 1\}$  where A is a positive semidefinite  $n \times n$  matrix. Note we get the sphere when A is the identity matrix.
- 3. The cube  $B_{\infty}^n$  is the set  $\{x \in \mathbb{R}^n \mid ||x||_{\infty} \leq 1\}$ .
- 4. The simplex C is the set  $\{x \in \mathbb{R}^n \mid x_i \geq 0, \sum_i x_i \leq 1\}$ .
- 5. The cross-polytope  $B_1^n$  is the set  $\{x \in \mathbb{R}^n \mid ||x||_1 \leq 1\}$ , which is the convex hull of all points of the form  $(0,0,\ldots,0,\pm 1,0,\ldots,0)$ . In  $\mathbb{R}^2$  the cross-polytope and square are equivalent up to rotation of  $\pi/4$ . In  $\mathbb{R}^3$  the cross-polytope is the octahedron. In general the cross-polytope in  $\mathbb{R}^n$  has  $2^n$  faces and 2n vertices (compare with the cube which has exactly the reverse), and acts as the "opposite" of the cube.

### 2.1 Geometric Intuition in High Dimension

The first thing to notice in high dimensions is that the vast majority of volume lies near the boundary of a convex body. For example, in  $\mathbb{R}^2$  to get 1% of the volume of the square  $[-1,1]^2$  we can take the square  $[-1,1]^2$ . In 100 dimensions to get 1% of the volume of  $[-1,1]^{100}$  we would need to take the cube  $[-.955,.955]^{100}$ !

Big differences between balls and cubes also appear in high dimensions. For any n, to get a cube with volume 1 in  $\mathbb{R}^n$  we can take a cube with sidelength 1. The story for cubes is different. The volume of a radius-r sphere in  $\mathbb{R}^n$  is

$$\frac{r^n \pi^{n/2}}{\Gamma(\frac{n}{2} + 1)} \approx \left(r \sqrt{\frac{2\pi e}{n}}\right)^n$$

implying that in  $\mathbb{R}^n$  we need to take a sphere of radius roughly  $\sqrt{n/2\pi e}$  to get a volume of 1. In other words, balls in high dimensions are much smaller than cubes! Intuitively this makes sense. As we said previously, much of the volume in high dimensions lies near the boundary. If one imagines a sphere inscribed in a cube with sidelength equal to the sphere's diameter, very little of the sphere is near the cube's boundary.

Another thing to notice about high-dimensional balls is that much of the volume is concentrated around the equator. More concretely, define v(t) as the (n-1)-dimensional volume of  $B_2^n \cap \{x_0 = t\}$ . It turns out that v(t) drops off dramatically as t deviates from 0. Quantitatively, one can show that that

$$v(t) \approx \sqrt{e} \left(\frac{\sqrt{r^2 - t^2}}{r}\right)^{n-1}$$

Thus, if one wishes to know what distance from the equator one has to slice to get, say, 96% of the sphere's volume, one can solve for t in the equation  $\int_{-t}^{t} v(t)dt = .96\text{vol}(B_2^n)$  to find that the required value of t is quite small as a function of t (we leave the computation to the interested reader).

#### 2.2 Maximizing Volume with a Given Surface Area

One important question in convex geometry is the following: "What is the most volume that can be enclosed in a convex body with a given surface area?". In  $\mathbb{R}^2$  we can view the problem as us being given a string of some finite length and must arrange the string in the plane so as to maximize the area it encloses. The shape achieving this maximum area is of course the circle, but the proof is not trivial. We show a false proof that stood for quite some time before its major flaw was uncovered:

1. Let C be the shape achieving the maximum area. We can assume C is convex since if the line segment between x and y for some  $x, y \in C$  is not in C, we can reflect about the segment  $\overline{xy}$  to increase area.

- 2. We can assume C is symmetric about both the x and y axes. If not, first reflect the smaller-perimeter half of C about a line parallel to the x axis that bisects C's area. Then, do the same for y. If the resulting shape has smaller perimeter than C we arrive at a contradiction, since that extra "piece of string" could be used to increase the area of C. Otherwise, shift C so that its center is the origin (implying  $(x,y) \in C \Leftrightarrow (-x,-y) \in C$ ).
- 3. If C is not a circle, let p be the point on C's boundary that is farthest away such that there exists a p' equidistant from the origin with p such that p' is not on the boundary of C. Reflect about the line that bisects the angle between p and p' so that C contains both p and p'. The area of the new shape is the same as that of C.

The main problem with this proof is in Step 1. One cannot simply assume that there exists a shape C which maximizes the area. In particular, to perform this type of argument one would first have to show that some metric defined on the space of convex bodies is complete.

## References

[1] "Randomized Approximation Schemes for Cuts and Flows in Capacitated Graphs," A. Benczur, D. Karger, manuscript.

| MIT C   | penCourseWare |
|---------|---------------|
| http:// | ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

#### 18.409 An Algorithmist's Toolkit

October 20, 2009

### Lecture 11

Lecturer: Jonathan Kelner Scribe: Chaithanya Bandi

## 1 Outline

Today we'll introduce and discuss

- Polar of a convex body.
- Correspondence between norm functions and origin-symmetric bodies (and see how convex geometry can be a powerful tool for functional analysis).
- Fritz-John's Theorem

## 2 The Polar of a Polytope

Given a bounded polytope  $C \subset \mathbb{R}^n$  that contains the origin in its interior, we can represent C as

$$C = \{x | a_i \cdot x \le b_i, i = 1, \dots, k\},\$$

where  $b_i > 0$ .

Without loss of generality, by appropriately scaling each constraint, we can assume  $b_i = 1, \forall i = 1, \dots, k$ . Now the polar of C is given by

$$C^* = conv(a_1, \dots, a_k).$$

#### 2.1 Examples

Let C be the square with corners at (1,1), (1,-1), (-1,1), (-1,-1). Then  $\{a_i\} = \{(1,0), (0,1), (-1,0), (0,-1)\}$ . The polar has corners at (1,0), (0,1), (-1,0), (0,-1). Note that the polar is a square rotated and shrunk into a diamond. This polytope is also referred to as the "cross polytope". Note that the facets of C become the vertices of  $C^*$  and vice versa. For example, the three dimensional cube's polar is the octahedron. Six facets and eight vertices correspond to eight facets and six vertices.

The size and shape of a polar tends to be the reverse of that of the original set. For example, a short bulging rectangle with corners at (100, 3), (100, -3), (-100, 3), (-100, -3) would have a tall compressed polar with corners at  $(\pm 1/100, 0), (0, \pm 1/3)$ . Also note that polars of simplices are simplices.

#### 2.2 Properties of a polar

Some of the useful properties of a polar is summarised here. The properties will be illustrated using pictures.

- $(C^*)^* = C$  (proof later).
- If C is origin-symmetric, then so is  $C^*$ .
- If  $A \subseteq B$  then  $B^* \subseteq A^*$ .
- If A is scaled up, then  $A^*$  is scaled down.
- If the polar is low-dimensional, that would mean the original polytope had to be unbounded in some directions.

• Translation has a very drastic effect on the polar. It can become unbounded just by translating the polytope.

All these properties can be illustrated using the pictures below.

## 3 Polars of General Convex Bodies

Any convex body can be thought of as the intersection of a (possibly infinite) set of half spaces. These are called "'suporting hyperplanes". Therefore, the polar of a convex body can be seen as the convex hull of a (possibly infinite) set of points, coming from all of the supporting hyperplanes. With this intuition one can guess about the following:

- Polar of a sphere is a sphere.
- Polar of a sphere of radius r is a sphere of radius 1/r.
- Polar of an ellipse is an ellipse with axes reversed.

**Definition 1** The polar of a convex body C is given by

$$C^* = \{ x \in \mathbb{R}^n | x \cdot c < 1 \forall c \in C \}$$

We observe that this definition is equivalent to the previous definition.

**Proposition 2** For a polytope C given by  $C = \{x | a_i \cdot x \leq b_i, i = 1, ..., k\}$ , the sets  $C_1 = C_2$  where  $C_1 = \{x \in \mathbb{R}^n | x \cdot c \leq 1 \forall c \in C\}$  and  $C_2 == conv(a_1, ..., a_k)$ .

We skip the proof as it is easy to verify that if  $x \in C_1$  then  $x \in C_2$  and vice versa.

We will now prove that  $(C^*)^* = C$ . We would be needing the concept of a separating hyperplane for the proof which we introduce now.

#### 3.1 Separating Hyperplanes

Given a convex body  $K \subseteq \mathbb{R}^n$  and a point p, a separating hyperplane for K and p is a hyperplane that has K on one side of it and p on the other. More formally, for a vector  $\nu$ , the hyperplane  $H = \{x | \nu \cdot x = 1\}$  is a separating hyperplane for K and p if

- 1.  $\nu \cdot x < 1$  for all  $x \in K$ , and
- 2.  $\nu \cdot p > 1$ .

Note that if we replace the right hand side of both the above conditions by 0 or any other constant, we get an equivalent formulation.

We call a separating hyperplane H a strongly separating hyperplane if the second inequality is strict.

**Theorem 3 Separating Hyperplane Theorem**: If K is a convex body and p is a point not contained in K, then there exists a hyperplane that strongly separates them.

**Proof** We'll sketch an outline of the proof. It can be made rigorous. Consider a point  $x \in K$  that is the closest to p in  $\ell_2$  distance. Consider the plane H that is perpendicular to the line joining x to p and is passing through the midpoint of x and p. H must separate K from p because if there is some point of K, say p, that is on the same side of H as p, then we can use the convexity of K to conclude that the point p which is the intersection of the hyperplane with the line joining p and p is also in p. This contradicts the assumption that p is the point closest to p.

#### 3.2 Polar of a Polar

We'll use the above result to show why the polar of the polar of a convex body is the body itself. Recall that for a convex body K, we had defined its polar  $K^*$  to be  $\{p|k \cdot p \leq 1 \forall k \in K\}$ .

**Theorem 4** Let K be a convex body. Then  $K^{**} = K$ .

**Proof** We know that  $K^* = \{p | k \cdot p \leq 1 \forall k \in K\}$ . Similarly  $K^{**} = \{y | p \cdot y \leq 1 \forall p \in k^*\}$ . Let y be any point in K. Then, by the definition of the polar, for all  $p \in K^*$  we have that  $p \cdot y \leq 1$ . The definition of the polar of  $K^*$  implies that  $y \in K^{**}$ . Since this is true for every  $y \in K$ , we conclude that  $K \subseteq K^{**}$ .

The other direction of the proof is the nontrivial one and we'll have to use the convexity of the body and the separating hyperplane theorem. If possible, let y be such that  $y \in K^{**}$  and  $y \notin K$ . Since  $y \in K^{**}$ , we have that  $P \cdot y \leq 1 \forall p \in K^*$ . Since  $y \notin K$ , there exists a strongly separating hyperplane for y and K. Let it be  $H = \{x | v \cdot x = 1\}$ . By the definition of separating hyperplane, we have  $v \cdot k \leq 1 \forall k \in K$ . Hence,  $v \in K^*$ . Also,  $v \cdot y > 1$  (since H is a separating hyperplane), and we just showed that  $v \in K^*$ . This contradicts our assumption that  $y \in K^{**}$ . Hence  $K^{**} \subseteq K$ .

# 4 Norms and Symmetric Convex Bodies

We will show how norms and symmetric convex bodies co-exist. This provides us a way to use the results of Convex Geometry in Functional Analysis and vice versa. Recall that a norm on  $\mathbb{R}^n$  is a map  $q:\mathbb{R}^n\to\mathbb{R}$  such that:

- 1. q(ax) = aq(x) for  $a \in \mathbb{R}$  (homogeneity)
- 2.  $q(x+y) \le q(x) + q(y)$  (triangle inequality)
- 3.  $q(x) \ge 0$  for all x (nonnegativity) (actually implied by 1 and 2)
- 4. q(x) = 0 if and only if x = 0 (positivity) (without this conditions, q is a "seminorm")

Note that given a norm, one can construct a convex body. The simplest being the unit ball  $B_q = \{x \in \mathbb{R}^n | q(x) \leq 1\}$ . It is an easy exercise to verify the convexity of  $B_q$ .

Also as we will show now, given a convex body C, we can come up with a norm under which C is the unit ball. Note that C has to be origin symmetric.

**Definition 5** The Minkowski functional of an origin symmetric convex body C is the map  $p_C : \mathbb{R}^n \to \mathbb{R}$  defined by

$$p_C(x) = \inf_{\lambda > 0} \{ x \in \lambda C \}$$

(We will sometimes denote this by  $||x||_C$ , because it is a norm.)

To prove that this is a norm, one needs to verify the properties of homogeneity, triangle inequality etc. These follow from the convexity of the body.

#### 4.1 Norms, Duals, and the Polar

For any norm q, we can define its dual by  $q^*(x) = \sup_{v \neq 0} \left| \frac{v \cdot x}{q(v)} \right|$ . It is an exercise to see that the unit ball with respect to the dual norm of q is the polar of the unit ball with respect to q. This provides us a direct relation between convex geometry and functional analysis.

The following pictures allow us to have a geometric intuition of the norms and their duals.

$$p = 2$$

 $p = \frac{1}{2}$ : not a norm, and not convex

## 5 Banach-Mazur Distance

Recall from last time the definition of the Banach–Mazur distance between two convex bodies:

**Definition 6** Let K and L be two convex bodies. The Banach–Mazur distance d(K, L) is the least positive  $d \in \mathbb{R}$  for which theres a linear image L' of L such that  $L' \subseteq K \subseteq dL'$ , where dL' is the convex body obtained by multiplying every vector in L' by the scalar d.

Observe that the above definition takes into consideration only the intrinsic shape of the body, and it is independent of any particular choice of coordinate system. Also observe that the Banach–Mazur distance is symmetric in it's input arguments. If  $L \subseteq K \subseteq dL$ , then by scaling everything by d, we get that  $dL' \subseteq dK$ . Hence  $K \subseteq dL' \subseteq dK$ , which implies the symmetry property.

## 6 Fritz John's Theorem

Let  $B_2^n$  denote the *n*-dimensional unit ball. For any two convex bodies K and K', let d(K, K') denote the Banach–Mazur distance between them. In the rest of this lecture, we'll state and prove the Fritz John's theorem.

**Theorem 7** For any n-dimensional, origin-symmetric convex body K,  $d(K, B_2^n) \leq \sqrt{n}$ .

In other words, the theorem states that for every origin-symmetric convex body K, there exists some ellipsoid E such that  $E \subseteq K \subseteq \sqrt{n}E$ . We'll prove that the ellipsoid of maximal volume that is contained in K will satisfy the above containment.

Informally, the theorem says that up to a factor of  $\sqrt{n}$ , every convex body looks like a ball. The above bound of  $\sqrt{n}$  is tight for the cube. If we didn't require the condition that K is origin symmetric, then the bound would be n, which would be tight for a simplex.

The theorem can also be rephrased as the following: There exists a change of the coordinate basis for which  $B_2^n \subseteq K \subseteq \sqrt{n}B_2^n$ .

**Theorem 8** Let K be an origin-symmetric convex body. Then K contains a unique ellipsoid of maximal volume. Moreover, this largest ellipsoid is  $B_2^n$  if and only if the following conditions hold:

- $\bullet$   $B_2^n \subseteq K$
- There are unit vectors  $u_1, u_2, \ldots, u_m$  on the boundary of K and positive real numbers  $c_1, c_2, \ldots, c_m$  such that
  - 1.  $\sum_{i=1}^{m} c_i u_i = 0$ , and
  - 2. for all vectors x,  $\sum_{i=1}^{m} c_i \langle x, u_i \rangle^2 = |x|^2$ .

Since the  $u_i$  are unit vectors, they are points on the convex body K that also belong to the sphere  $B_2^n$ . Also, the first identity, i.e.  $\sum_{i=1}^m c_i u_i = 0$ , is actually redundant, since for origin symmetric bodies it can be derived from the second identity. This is because for every  $u_i$ , it's reflection in the origin is also contained in  $K \cap B_2^n$ .

The second identity says that the contact points (of the sphere with K) act somewhat like an orthonormal basis. They can be weighted so that they are completely isotropic. In other words, the points are not concentrated near some proper subspace, but are pretty evenly spread out in all directions. Together they mean that the  $u_i$  can be weighted so that their center of mass is the origin and their inertia tensor is the identity. Also, a simple rank argument shows that there need to be at least n such contact points, since the second identity can only hold for x in the span of the  $u_i$ .

#### 6.1 Proof of John's Theorem

**Proof** As part of the proof of John's Theorem, we'll prove the following things:

- 1. If there exist contact points  $\{u_i\}$  as required in the statement of Theorem 8, then  $B_2^n$  is the unique ellipsoid of maximal volume that is contained in K.
- 2. If  $B_2^n$  is the unique ellipsoid of maximal volume that is contained in K, then there exist points  $\{u_i\}$  such that they satisfy the two identities in Theorem 8.

**Proof of 1:** We are given unit vectors  $u_1, u_2, \ldots, u_m$  on the boundary of K and positive real numbers  $c_1, c_2, \ldots, c_m$  such that  $\sum_{i=1}^m c_i u_i = 0$ , and for all vectors x,  $\sum_{i=1}^m c_i \langle x, u_i \rangle^2 = |x|^2$ . We wish to show that  $B_2^n$  is the unique ellipsoid of maximal volume that is contained in K. Observe that it suffices to show that among all axis-aligned ellipsoids contained in K,  $B_2^n$  is the unique ellipsoid of maximal volume. This is because what we are trying to prove doesn't mention any basis and is only in terms of dot-products. Hence, since the statement will remain true under rotations, proving it for axis-aligned ellipsoids is enough.

For each  $u_i$  we have that for all  $k \in K$ ,  $u_i \cdot k \le 1$ . Hence  $u_i \in K^*$ . Let E be any axis-aligned ellipsoid such that  $E \in K$ . Then  $K^* \subseteq E^*$ . Hence  $\{u_1, u_2, \ldots, u_m\} \subseteq E^*$ . Since E is axis-aligned, it is of the form  $\{x \mid \sum_{i=1}^n \frac{x_i^2}{\sigma_i^2} \le 1\}$ .

 $Vol(E)/Vol(B_2^n) = \prod_{i=1}^n \alpha_i$ . Therefore, to show that  $Vol(E) < Vol(B_2^n)$ , we must show that  $\prod_{i=1}^n \alpha_i < 1$  for any such E which is not  $B_2^n$ .

Observe that  $E^* = \{Y | \sum_{i=1}^n \alpha_i^2 y_i^2 \le 1\}$ . Also, condition 2 of Theorem 8 is equivalent to the follow-

ing:  $\sum_{i=1}^{m} c_i u_i u_i^T = Id_n$ , where  $Id_n$  is the identity matrix of size n. Now, since  $u_i \cdot u_i = 1$ , we have  $\operatorname{Trace}(\sum_{i=1}^{m} c_i u_i u_i^T) = \sum_{i=1}^{n} c_i$ . Since  $\operatorname{Trace}(Id_n) = n$ , this implies that  $\sum_{i=1}^{n} c_i = n$ . Let  $e_j$  denote the vector which has a 1 in the  $i^{th}$  coordinate and 0 in the other coordinates. Clearly  $\langle u_i, e_j \rangle$  is the  $j^{th}$  coordinate of  $u_i$ . For  $i \leq i \leq m$ , since  $u_i \in E^*$ , we get that  $\sum_{j=1}^{n} \alpha_i^2 \langle u_i, e_j \rangle^2 \leq 1$ . Summing it over all i, we get

$$\sum_{i=1}^{m} \sum_{j=1}^{n} \alpha_i^2 \langle u_i, e_j \rangle^2 \le \sum_{i=1}^{n} c_i = n.$$

However, since by condition 2 of Theorem 8,  $\sum_{i=1}^{m} \langle u_i, e_j \rangle^2 = |e_j|^2$ , we get  $\sum_{i=1}^{n} \alpha_i^2 \leq n$ . By the AM-GM inequality, we get that  $(\prod_{i=1}^n \alpha_i^2)^{1/n} \leq \frac{\sum_{i=1}^n \alpha_i^2}{n} \leq 1$ , which implies that  $\prod_{i=1}^n \alpha_i \leq 1$ . Equality only holds if all the  $\alpha_i$  are equal. This shows that  $\prod_{i=1}^n \alpha_i < 1$  for any such E which is not  $B_2^n$ , completing the first part of the proof.

**Proof of 2:** Assume that we are give that  $B_2^n$  is the unique ellipsoid of maximal volume that is contained in K. We want to show that for some m, there exist  $c_i$  and  $u_i$  for  $1 \le i \le m$  (as in the statement of Theorem 8), such that for all vectors x,  $\sum_{i=1}^{m} c_i \langle x, u_i \rangle^2 = |x|^2$ . This is equivalent to showing that

$$\sum_{i=1}^{m} c_i u_i u_i^T = Id_n.$$

Also, taking trace of both sides, we get that  $\sum_{i=1}^{m} c_i = n$ . We already observed that for origin-symmetric bodies, the condition that  $\sum_{i=1}^{m} c_i u_i = 0$ , is implied by the previous condition.

Let  $U_i = u_i u_i^T$ . Also, observe that we can view the space of  $n \times n$  matrices as a vector of  $n^2$  real numbers. Hence we can parametrize the space of  $n \times n$  matrices by  $\mathbb{R}^{n^2}$ . Hence  $\sum_{i=1}^m c_i u_i u_i^T = Id_n$  means that  $Id_n/n$  is in the convex hull of the  $U_i$  (recall that the  $c_i$  are positive and sum to 1).

If possible, let there be no  $c_i$ ,  $u_i$  such that  $\sum_{i=1}^m c_i u_i u_i^T = Id_n$ . This means that  $Id_n/n$  is not in the convex

hull of the  $U_i$ . Hence, there must be a separating hyperplane H in the space of matrices that separates  $Id_n/n$ from the convex hull of the  $U_i$ .

For two  $n \times n$  matrices A and B, let  $A \bullet B$  denote their dot product in  $\mathbb{R}^{n^2}$ , i.e.  $A \bullet B = \sum_{i,j} A_{ij} \cdot B_{ij}$ . Thus, the separating hyperplane is a matrix H such that  $\forall A \in \text{conv}(U_i), A \bullet H \geq 1$ , and  $Id_n/n \bullet H < 1$ .

Let  $t = \operatorname{Trace}(H) = H \bullet Id_n$ . Let  $H' = H - t/n(Id_n)$ . Then  $Id_n/n \bullet H' = Id_n/n \bullet (H - t/nId_n) =$  $t/n - (Id_n/n \bullet t/nId_n) = 0$ . Similarly, since  $\forall A \in \text{conv}(U_i)$ , Trace(A) = 1, we get that  $A \bullet H' > 0$ . Hence, H' is such that:

- 1. Trace(H') = 0, and
- 2.  $H' \bullet (u_i u_i^T) > 0$  for all i.

Now, let  $E_{\delta} = \{x \in \mathbb{R}^n | x^T (Id_n + \delta H') x \leq 1. \text{ For all } i, \text{ we have } u_i^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ since } i \leq 1, \text{ for all } i, \text{ we have } u_i^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ since } i \leq 1, \text{ for all } i, \text{ for all } i, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ since } i \leq 1, \text{ for all } i, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i > 1, \text{ for all } i \in \mathbb{R}^n | x^T (Id_n + \delta H') u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1 + \delta u_i^T H' u_i = 1$  $H' \bullet (u_i u_i^T) > 0 \Rightarrow u_i^T H' u_i > 0$ . Hence  $u_i \notin E_\delta$ . Also, since  $H' \bullet (u_i u_i^T) > 0$  for all i, by compactness, there exists  $\epsilon > 0$  such that for all matrices w in the  $\epsilon$ -neighborhood of the set of all  $u_i$  satisfy  $H' \bullet (ww^T) > 0$ . Hence, by the previous argument, any such w is not contained in  $E_{\delta}$ .

Note that when  $\delta = 0$ , we get the unit ball  $B_2^n$ . For every  $\delta > 0$  we have that for all w in the  $\epsilon$ neighborhood of the contact points of  $B_2^n$ ,  $w \notin E_\delta$ . Hence, as we increase  $\delta$  continuously starting from 0, the continuity of the transformation of  $E_{\delta}$  implies that for sufficiently small  $\delta$ , boundary $(K) \cap E_{\delta} = \phi$ .

Hence  $\exists \epsilon' > 0$  such that  $(1 + \epsilon')E_{\delta} \subseteq K$ . Therefore, to conclude the proof, it suffices to show that  $Vol(E_{\delta} \geq Vol(B_2^n).$ 

Let  $\lambda_1, \lambda_2, \ldots, \lambda_n$  be the eigenvalues of  $Id_n + \delta H'$ . Since  $Vol(E_{\delta} = (\prod_{i=1}^n \lambda_i)^{-1}$ , to show that  $Vol(E_{\delta} \geq \prod_{i=1}^n \lambda_i)^{-1}$  $Vol(B_2^n)$ , we need to show that  $\prod_{i=1}^n \lambda_i \leq 1$ . However we know that  $\sum_{i=1}^n \lambda_i = \operatorname{Trace}(Id_n + \delta H') = \operatorname{Trace}(Id_n) = n$ . By the AM-GM inequality,  $(\prod_{i=1}^n \lambda_i)^{1/n} \leq (\sum_{i=1}^n \lambda_i)/n = 1$ . Hence  $\prod_{i=1}^n \lambda_i \leq 1$ . This concludes the proof of part 2.

To wrap up the proof of John's Theorem, assume without loss of generality that  $B_2^n$  is the ellipsoid of maximal volume contained in K. We can make this assumption since the particular choice of basis is not important for the proof. We need to show that  $B_2^n \subseteq K \subseteq \sqrt{n}B_2^n$ . Now, for all  $x \in K$ , we have  $x \cdot u_i \le 1$  for all i. Hence,  $|x|^2 = \sum c_i (x \cdot u_i)^2 \le \sum c_i = n$ . This shows that  $|x| \le \sqrt{n}$ , and hence  $K \subseteq \sqrt{B}_2^n$ . Thus, we have proven the existence of an ellipse E such that

$$E \subseteq K \subseteq \sqrt{n}E$$
.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

#### 18.409 An Algorithmist's Toolkit

October 22, 2009

#### Lecture 12

Lecturer: Jonathan Kelner Scribes: Alex Levin (2009)

## 1 Outline

Today we'll go over some of the details from last class and make precise many details that were skipped. We'll then go on to prove Fritz John's theorem. Finally, we will start discussing the Brunn-Minkowski inequality.

## 2 Separating Hyperplanes

Given a convex body  $K \subseteq \mathbb{R}^n$  and a point p, a separating hyperplane for K and p is a hyperplane that has K on one side of it and p on the other. More formally, for a vector  $\nu$ , the hyperplane  $H = \{x | \nu \cdot x = 1\}$  is a separating hyperplane for K and p if

- 1.  $\nu \cdot x \leq 1$  for all  $x \in K$ , and
- 2.  $\nu \cdot p > 1$ .

Note that if we replace the right hand side of both the above conditions by 0 or any other constant, we get an equivalent formulation.

We call a separating hyperplane H a strongly separating hyperplane if the second inequality is strict. Last time, we sketched a proof of the following theorem:

**Theorem 1 (Separating Hyperplane Theorem)** If K is a convex body and p is a point not contained in K, then there exists a hyperplane that strongly separates them.

We'll use the above result to show why the polar of the polar of a convex body is the body itself. Recall that for a convex body K, we had defined its polar  $K^*$  to be  $\{p|k \cdot p \leq 1 \forall k \in K\}$ .

**Theorem 2** Let K be a convex body. Then  $K^{**} = K$ .

**Proof** We know that  $K^* = \{p | k \cdot p \leq 1 \forall k \in K\}$ . Similarly  $K^{**} = \{y | p \cdot y \leq 1 \forall p \in k^*\}$ . Let y be any point in K. Then, by the definition of the polar, for all  $p \in K^*$  we have that  $p \cdot y \leq 1$ . The definition of the polar of  $K^*$  implies that  $y \in K^{**}$ . Since this is true for every  $y \in K$ , we conclude that  $K \subseteq K^{**}$ .

The other direction of the proof is the nontrivial one and we'll have to use the convexity of the body and the separating hyperplane theorem. Suppose that we can find a  $y \in K^{**}$  such that  $y \notin K$ . Since  $y \in K^{**}$ , we have that  $p \cdot y \leq 1$  for all  $p \in K^*$ . Since  $y \notin K$ , there exists a strongly separating hyperplane for y and K. Let it be  $H = \{x | v \cdot x = 1\}$ . By the definition of separating hyperplane, we have  $v \cdot k \leq 1$  for all  $k \in K$ . Hence,  $v \in K^*$ . Also,  $v \cdot y > 1$  (since H is a separating hyperplane), and we just showed that  $v \in K^*$ . This contradicts our assumption that  $y \in K^{**}$ . Hence  $K^{**} \subseteq K$ .

### 3 Banach–Mazur Distance

Recall from last time the definition of the Banach–Mazur distance between two convex bodies:

**Definition 3** Let K and L be two convex bodies. The Banach-Mazur distance d(K, L) is the least positive  $d \in \mathbb{R}$  for which there is a linear image L' of L such that  $L' \subseteq K \subseteq dL'$ , where dL' is the convex body obtained by multiplying every vector in L' by the scalar d.

Image by MIT OpenCourseWare.

Figure 1: Defining the distance between K and L.

Observe that the above definition takes into consideration only the intrinsic shape of the body, and it is independent of any particular choice of coordinate system. Also observe that the Banach–Mazur distance is symmetric in its input arguments. If  $L' \subseteq K \subseteq dL'$ , then by scaling everything by d, we get that  $dL' \subseteq dK$ . Hence  $K \subseteq dL' \subseteq dK$ , which implies the symmetry property.

### 4 Fritz John's Theorem

Let  $B_2^n$  denote the *n*-dimensional unit ball. For any two convex bodies K and K', let d(K, K') denote the Banach–Mazur distance between them. In the rest of this lecture, we will state and prove Fritz John's theorem.

**Theorem 4** For any n-dimensional, origin-symmetric convex body K, we have  $d(K, B_2^n) \leq \sqrt{n}$ .

In other words, the theorem states that for every origin-symmetric convex body K, there exists some ellipsoid E such that  $E \subseteq K \subseteq \sqrt{n}E$ . We will prove that the ellipsoid of maximal volume that is contained in K will satisfy the above containment.

Informally, the theorem says that up to a factor of  $\sqrt{n}$ , every convex body looks like a ball. The above bound of  $\sqrt{n}$  is tight for the cube. If we didn't require the condition that K is origin symmetric, then the bound would be n, which would be tight for a simplex.

The theorem can also be rephrased as the following: there exists a change of the coordinate basis for which  $B_2^n \subseteq K \subseteq \sqrt{n}B_2^n$ .

### 4.1 A slightly stronger version of the Fritz John Theorem

We will actually state and prove a more technical and slightly stronger version of the Fritz John theorem that implies our previous formulation. From now on, we assume that all the convex bodies we consider are origin-symmetric.

**Theorem 5** Let K be an origin-symmetric convex body. Then K contains a unique ellipsoid of maximal volume. Moreover, this largest ellipsoid is  $B_2^n$  if and only if the following conditions hold:

- $B_2^n \subseteq K$
- There are unit vectors  $u_1, u_2, \ldots, u_m$  on the boundary of K and positive real numbers  $c_1, c_2, \ldots, c_m$  such that

- 1.  $\sum_{i=1}^{m} c_i u_i = 0$ , and
- 2. For all vectors x, we have  $\sum_{i=1}^{m} c_i \langle x, u_i \rangle^2 = |x|^2$ . It is not hard to show that this condition is equivalent to the requirement that  $\sum_{i=1}^{m} c_i u_i u_i^T = \operatorname{Id}_n$ , where  $\operatorname{Id}_n$  is the  $n \times n$  identity matrix.

Since the  $u_i$  are unit vectors, they are points on the convex body K that also belong to the sphere  $B_2^n$ . Also, the first identity, i.e.  $\sum_{i=1}^m c_i u_i = 0$ , is actually redundant, since for origin-symmetric bodies it can be derived from the second identity. This is because for every  $u_i$ , its reflection in the origin (namely  $-u_i$ ) is also contained in  $K \cap B_2^n$ ; further we can take the constants in the second identity corresponding to  $u_i$  and  $-u_i$  to be the same, and this establishes the first equation.

The second identity says that the contact points of the sphere with K act somewhat like an orthonormal basis. They can be weighted so that they are completely isotropic. In other words, the points are not concentrated near some proper subspace, but are pretty evenly spread out in all directions. Together they mean that the  $u_i$  can be weighted so that their center of mass is the origin and their inertia tensor is the identity. Also, a simple rank argument shows that there need to be at least n such contact points, since the second identity can only hold for x in the span of the  $u_i$ .

Note that Theorem 4 easily follows from Theorem 5. Indeed, assume without loss of generality that  $B_2^n$  is the ellipsoid of maximal volume contained in K. We can make this assumption since the particular choice of basis is not important for the proof. We need to show that  $B_2^n \subseteq K \subseteq \sqrt{n}B_2^n$ . Now, for all  $x \in K$ , we have  $x \cdot u_i \leq 1$  for all i. Hence,  $|x|^2 = \sum c_i(x \cdot u_i)^2 \leq \sum c_i$ . In the course of the proof below, we will see that  $\sum c_i = n$ . This shows that  $|x| \leq \sqrt{n}$ , and hence  $K \subseteq \sqrt{n}B_2^n$ .

Thus, once we prove Theorem 5, we will have shown the existence of an ellipsoid E such that

$$E \subseteq K \subseteq \sqrt{n}E$$
.

### 4.2 Proof of John's Theorem

As part of the proof Theorem 5, we will prove the following things:

- 1. If there exist contact points  $\{u_i\}$  as required in the statement of Theorem 5, then  $B_2^n$  is the unique ellipsoid of maximal volume that is contained in K.
- 2. If  $B_2^n$  is the unique ellipsoid of maximal volume that is contained in K, then there exist points  $\{u_i\}$  such that they satisfy the two identities in Theorem 5.

To prove the first statement, suppose that we are given unit vectors  $u_1, u_2, \ldots, u_m$  on the boundary of K and positive real numbers  $c_1, c_2, \ldots, c_m$  such that  $\sum_{i=1}^m c_i u_i = 0$ , and for all vectors x, it is the case that  $\sum_{i=1}^m c_i \langle x, u_i \rangle^2 = |x|^2$ . We wish to show that  $B_2^n$  is the unique ellipsoid of maximal volume that is contained in K. Observe that it suffices to show that among all axis-aligned ellipsoids contained in K,  $B_2^n$  is the unique ellipsoid of maximal volume. This is because what we are trying to prove doesn't mention any basis and is only in terms of dot products. Hence, since the statement will remain true under rotations, proving it for axis-aligned ellipsoids is enough.

For each  $u_i$  it is the case that  $u_i \cdot k \leq 1$  for all  $k \in K$ , Hence  $u_i \in K^*$ . Let E be any axis-aligned ellipsoid such that  $E \subseteq K$ . Then  $K^* \subseteq E^*$ . Hence  $\{u_1, u_2, \dots, u_m\} \subseteq E^*$ . Since E is axis-aligned, it is of the form  $\{x \mid \sum_{i=1}^n \frac{x_i^2}{\alpha_i^2} \leq 1\}$ .

We also have that  $\operatorname{Vol}(E)/\operatorname{Vol}(B_2^n) = \prod_{i=1}^n \alpha_i$ . Therefore, to show that  $\operatorname{Vol}(E) < \operatorname{Vol}(B_2^n)$ , we must show that  $\prod_{i=1}^n \alpha_i < 1$  for any such E that is not  $B_2^n$ .

Observe that  $E^* = \{y | \sum_{i=1}^n \alpha_i^2 y_i^2 \le 1\}$ . Now, since  $u_i \cdot u_i = 1$ , we have  $\operatorname{Tr}\left(\sum_{i=1}^m c_i u_i u_i^T\right) = \sum_{i=1}^n c_i$ . Since  $\operatorname{Tr}(\operatorname{Id}_n) = n$ , this implies that  $\sum_{i=1}^n c_i = n$ .

Let  $e_j$  denote the vector which has a 1 in the  $j^{th}$  coordinate and 0 in the other coordinates. Clearly  $\langle u_i, e_j \rangle$  is the  $j^{th}$  coordinate of  $u_i$ . For  $1 \leq i \leq m$ , since  $u_i \in E^*$ , we get that  $\sum_{j=1}^n \alpha_j^2 \langle u_i, e_j \rangle^2 \leq 1$ . Summing it over all i, we get

$$\sum_{i=1}^{m} c_i \sum_{j=1}^{n} \alpha_j^2 \langle u_i, e_j \rangle^2 \le \sum_{i=1}^{n} c_i = n.$$
 (1)

Now, switching the order of summation on the left-hand side of (1) gives us

$$\sum_{j=1}^{n} \alpha_j^2 \sum_{i=1}^{m} c_i \langle u_i, e_j \rangle^2,$$

and by the above we know that this is at most n. Further, by condition 2 of Theorem 5, we know that  $\sum_{i=1}^{m} c_i \langle u_i, e_j \rangle^2 = |e_j|^2 = 1$ . Therefore, we get  $\sum_{j=1}^{n} \alpha_j^2 \leq n$ . By the AM-GM inequality, we get that  $\left(\prod_{i=1}^{n} \alpha_i^2\right)^{1/n} \leq \frac{\sum_{i=1}^{n} \alpha_i^2}{n} \leq 1$ , which implies that  $\prod_{i=1}^{n} \alpha_i \leq 1$ . Equality only holds if all the  $\alpha_i$  are equal. This shows that  $\prod_{i=1}^{n} \alpha_i < 1$  for any such E that is not E, completing the first part of the proof.

For the second part, assume that we are given that  $B_2^n$  is the unique ellipsoid of maximal volume that is contained in K. We want to show that for some m, there exist  $c_i$  and  $u_i$  for  $1 \le i \le m$  (as in the statement of Theorem 5), such that for all vectors x,  $\sum_{i=1}^m c_i \langle x, u_i \rangle^2 = |x|^2$ . Again, this is equivalent to showing that

$$\sum_{i=1}^{m} c_i u_i u_i^T = \mathrm{Id}_n .$$

We already observed that for origin-symmetric bodies, the condition that  $\sum_{i=1}^{m} c_i u_i = 0$  is implied by the previous requirement.

Let  $U_i = u_i u_i^T$ . Also, observe that we can view the space of  $n \times n$  matrices as a vector space of dimension  $n^2$ . Hence we can parametrize the space of  $n \times n$  matrices by  $\mathbb{R}^{n^2}$ . Thus,  $\sum_{i=1}^m c_i u_i u_i^T = \operatorname{Id}_n$  for  $c_i > 0$  means that  $\operatorname{Id}_n/n$  is in the convex hull of the  $U_i$  (if the identity holds, we know that the  $c_i$  are positive and sum to n).

If we cannot find  $c_i$ ,  $u_i$  such that  $\sum_{i=1}^m c_i u_i u_i^T = \mathrm{Id}_n$ , it means that  $\mathrm{Id}_n / n$  is not in the convex hull of the  $U_i$ . Hence, there must be a hyperplane in the space of matrices that separates  $\mathrm{Id}_n / n$  from the convex hull of the  $U_i$ .

For two  $n \times n$  matrices A and B, let  $A \bullet B$  denote their dot product in  $\mathbb{R}^{n^2}$ , i.e.  $A \bullet B = \sum_{i,j} A_{ij} \cdot B_{ij}$ . Thus, the separating hyperplane gives a matrix H such that  $A \bullet H \geq 1$  for all  $A \in \operatorname{conv}(U_i)$  and  $(\operatorname{Id}_n/n) \bullet H < 1$ . Let  $t = \operatorname{Tr}(H) = H \bullet \operatorname{Id}_n$ . Let  $H' = H - (t/n)(\operatorname{Id}_n)$ . Then  $(\operatorname{Id}_n/n) \bullet H' = (\operatorname{Id}_n/n) \bullet (H - (t/n)\operatorname{Id}_n) = t/n - ((\operatorname{Id}_n/n) \bullet (t/n)\operatorname{Id}_n) = 0$ . Similarly, since  $\operatorname{Tr}(A) = 1$  for all A in  $\operatorname{conv}(U_i)$ , we get that  $A \bullet H' > 0$ . Hence, H' is such that:

- 1. Tr(H') = 0, and
- 2.  $H' \bullet (u_i u_i^T) > 0$  for all i.

Now, let  $E_{\delta} = \left\{x \in \mathbb{R}^n | x^T (\operatorname{Id}_n + \delta H') x \leq 1\right\}$ . For all i, we have  $u_i^T (\operatorname{Id}_n + \delta H') u_i = 1 + \delta u_i^T H' u_i$ , which is greater than 1 since  $u_i^T H' u_i > 0 = H' \bullet (u_i u_i^T) > 0$ . Hence  $u_i \notin E_{\delta}$ . Also, since  $H' \bullet (u_i u_i^T) > 0$  for all i, by continuity, there exists  $\epsilon > 0$  such that for all vectors w in the  $\epsilon$ -neighborhood of the set of all  $u_i$  satisfy  $H' \bullet (ww^T) > 0$ . Hence, by the previous argument, any such w is not contained in  $E_{\delta}$ .

Note that when  $\delta = 0$ , we get the unit ball  $B_2^n$ . For every  $\delta > 0$  we have that all w in the  $\epsilon$ -neighborhood of the contact points of  $B_2^n$  are not contained in  $E_{\delta}$ . Hence, as we increase  $\delta$  continuously starting from 0, the continuity of the transformation of  $E_{\delta}$  implies that for sufficiently small  $\delta$ , boundary  $(K) \cap E_{\delta} = \emptyset$ .

Hence  $\exists \epsilon' > 0$  such that  $(1 + \epsilon')E_{\delta} \subseteq K$ . Therefore, to conclude the proof, it suffices to show that  $\operatorname{Vol}(E_{\delta}) \geq \operatorname{Vol}(B_2^n)$ , which gives give us a contradiction (as  $(1 + \epsilon')E_{\delta}$  is an ellipse of volume larger than  $B_2^n$  contained in K).

Let  $\lambda_1, \lambda_2, \ldots, \lambda_n$  be the eigenvalues of  $\operatorname{Id}_n + \delta H'$ . Since  $\operatorname{Vol}(E_\delta) = (\prod_{i=1}^n \lambda_i)^{-1}$ , to show that  $\operatorname{Vol}(E_\delta) \geq \operatorname{Vol}(B_2^n)$ , we need to show that  $\prod_{i=1}^n \lambda_i \leq 1$ . However we know that  $\sum_{i=1}^n \lambda_i = \operatorname{Tr}(\operatorname{Id}_n + \delta H') = \operatorname{Tr}(\operatorname{Id}_n) = n$ . By the AM-GM inequality,  $(\prod_{i=1}^n \lambda_i)^{1/n} \leq (\sum_{i=1}^n \lambda_i)/n = 1$ . Hence  $\prod_{i=1}^n \lambda_i \leq 1$ . This concludes the proof of part 2.

## 5 Sketch of a Simpler Proof

If we just wish to prove the existence of an ellipse E that satisfies the conditions of Fritz John's Theorem without actually characterizing it, then the picture below suggests an alternative and possibly simpler proof of the result.

If any point of K is more than  $\sqrt{n}$  distance away from the origin, then we can find an ellipse of larger volume than  $B_2^n$  that is contained in K.

Image by MIT OpenCourseWare.

Figure 2: A simpler proof of the "Rounding" result.

# 6 The Brunn-Minkowski Inequality

**Definition 6** For  $A, B \in \mathbb{R}^n$ , the Minkowski sum  $A \oplus B$  is given by

$$A \oplus B = \{a + b | a \in A, b \in B\}.$$

The Minkowski sum can be defined for any subsets of  $\mathbb{R}^n$ , but it is nicely behaved if A and B are convex. Intuitively, the Minkowski sum is obtained by moving one of the sets around the boundary of the other one.

The Brunn-Minkowski inequality, which relates the volume of  $A \oplus B$  to the volumes of A and B, implies many important theorems in convex geometry. The goal is to bound  $Vol(A \oplus B)$  in terms of Vol(A) and Vol(B). The following are some loose bounds that can be simply verified.

Fact 7  $Vol(A \oplus B) \ge \max\{Vol(A), Vol(B)\}$ 

**Proof** Let  $a \in A$ . We have  $\{a\} \oplus B \subseteq A \oplus B$ , by definition. Hence,

$$Vol(A \oplus B) \ge Vol(\{a\} \oplus B) = Vol(B).$$

Similarly,  $Vol(A \oplus B) \ge Vol(B)$ .

Fact 8  $Vol(A \oplus B) \ge Vol(A) + Vol(B)$ 

**Proof** By moving one of the sets around the other one (summing the extreme points), we can get disjoint copies of A and B in  $A \oplus B$ .

The bound given by Fact 8 is loose. To see that, consider the case that A = B. In this case,  $A \oplus A = 2A$  and hence,  $Vol(A \oplus A) = 2^n Vol(A)$ . So the volume of  $A \oplus A$  grows exponentially with n, while the lower bound given in the above fact do not. This suggests taking the n-th roots and still get a valid bound. Let us first prove it for boxes.

**Lemma 9** Let A and B be boxes in  $\mathbb{R}^n$ . Then

$$\operatorname{Vol}(A \oplus B)^{1/n} \ge \operatorname{Vol}(A)^{1/n} + \operatorname{Vol}(B)^{1/n}$$

**Proof** Let A have sides of length  $a_1, \ldots, a_n$  and B have sides of length  $b_1, \ldots, b_n$ . It directly follows from the definition of Minkowski sums that  $A \oplus B$  has sides of length  $a_1 + b_1, \ldots, a_n + b_n$ .

We just need to show the following:

$$\frac{\text{Vol}(A)^{1/n} + \text{Vol}(B)^{1/n}}{\text{Vol}(A \oplus B)^{1/n}} \le 1.$$
 (2)

We can rewrite the left-hand side of (2) as

$$\frac{(\prod_{i=1}^{n} a_i)^{1/n} + (\prod_{i=1}^{n} b_i)^{1/n}}{(\prod_{i=1}^{n} (a_i + b_i))^{1/n}} = \frac{(\prod_{i=1}^{n} a_i)^{1/n}}{(\prod_{i=1}^{n} (a_i + b_i))^{1/n}} + \frac{(\prod_{i=1}^{n} b_i)^{1/n}}{(\prod_{i=1}^{n} (a_i + b_i))^{1/n}}$$

$$= \prod_{i=1}^{n} \left(\frac{a_i}{a_i + b_i}\right)^{1/n} + \prod_{i=1}^{n} \left(\frac{b_i}{a_i + b_i}\right)^{1/n}$$

$$\leq \frac{1}{n} \sum_{i=1}^{n} \frac{a_i}{a_i + b_i} + \frac{1}{n} \sum_{i=1}^{n} \frac{b_i}{a_i + b_i} = 1$$

where the inequality is just an application of AM-GM.

Next time, we will prove the Brunn-Minkowski inequality for more general bodies, and study some of its applications.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### 18.409 An Algorithmist's Toolkit

October 27, 2009

### Lecture 13

Lecturer: Jonathan Kelner Scribe: Jonathan Pines (2009)

## 1 Outline

Last time, we proved the Brunn-Minkowski inequality for boxes. Today we'll go over the general version of the Brunn-Minkowski inequality and then move on to applications, including the Isoperimetric inequality and Grunbaum's theorem.

## 2 The Brunn-Minkowski inequality

**Theorem 1** Let  $A, B \subseteq \mathbb{R}^n$  be compact measurable sets. Then

$$(\text{Vol}(A \oplus B))^{1/n} \ge (\text{Vol}(A))^{1/n} + (\text{Vol}(B))^{1/n}.$$
 (1)

The equality holds when A is a translation of a dilation of B (up to zero-measure sets).

**Proof** An equivalent version of Brunn-Minkowski inquality is given by

$$\left(\operatorname{Vol}(\lambda A \oplus (1-\lambda)B)\right)^{1/n} \ge \lambda(\operatorname{Vol}(A))^{1/n} + (1-\lambda)(\operatorname{Vol}(B))^{1/n}, \quad \forall \lambda \in [0,1].$$
 (2)

The equivalence of (1) and (2) follows from the fact that  $Vol(\lambda A) = \lambda^n Vol(A)$ :

$$\left(\operatorname{Vol}(\lambda A \oplus (1-\lambda)B)\right)^{1/n} \geq \left(\operatorname{Vol}(\lambda A)\right)^{1/n} + \left(\operatorname{Vol}((1-\lambda)B)\right)^{1/n} 
= \left(\lambda^n \operatorname{Vol}(A)\right)^{1/n} + \left((1-\lambda)^n \operatorname{Vol}(B)\right)^{1/n} 
= \lambda \left(\operatorname{Vol}(A)\right)^{1/n} + (1-\lambda)\left(\operatorname{Vol}(B)\right)^{1/n}.$$
(3)

The inequality (2) implies that the  $n^{th}$  root of the volume function is concave with respect to the Minkowski sum.

Here, we sketch the proof for Theorem 1 by proving (1) for any set constructed from a finite collection of boxes. The proof can be generalized to any measurable set by approximating the set with a sequence of finite collections of boxes and taking the limit. We omit the analysis details here.

Let A and B be finite collections of boxes in  $\mathbb{R}^n$ . We prove (1) by induction on the number of boxes in  $A \cup B$ . Define the following subsets of  $\mathbb{R}^n$ :

$$A^{+} = A \cap \{x \in \mathbb{R}^{n} | x_{n} \ge 0\} , A^{-} = A \cap \{x \in \mathbb{R}^{n} | x_{n} \le 0\},$$
  

$$B^{+} = B \cap \{x \in \mathbb{R}^{n} | x_{n} \ge 0\} , B^{-} = B \cap \{x \in \mathbb{R}^{n} | x_{n} \le 0\}.$$
(4)

Translate A and B such that the following conditions hold:

- 1. A has some pair of boxes separated by the hyperplane  $\{x \in \mathbb{R}^n | x_1 = 0\}$ . i.e. there exists a box that lies completely in the halfspace  $\{x \in \mathbb{R}^n | x_1 \geq 0\}$  and there is some other box that lies in its complement half-space (see figure 1). (If there's no such box in that direction we can change coordinates.)
- 2. It holds that

$$\frac{\operatorname{Vol}(A^+)}{\operatorname{Vol}(A)} = \frac{\operatorname{Vol}(B^+)}{\operatorname{Vol}(B)}.$$
 (5)

Note that translation of A or B just translates  $A \oplus B$ , so any statement about the translated sets holds for the original ones.

Since  $A^+$  and  $A^-$  are strict subsets of A, we know that  $A^+ \cup B^+$  and  $A^- \cup B^-$  have fewer boxes than  $A \cup B$ . Therefore, (1) is true for them by the induction hypothesis. Moreover,  $A^+ \oplus B^+$  and  $A^- \oplus B^-$  are disjoint because they differ in sign of the  $x_1$  coordinate. Hence, we have

$$Vol(A \oplus B) \geq Vol(A^{+} \oplus B^{+}) + Vol(A^{-} \oplus B^{-})$$

$$\geq (Vol(A^{+})^{1/n} + Vol(B^{+})^{1/n})^{n} + (Vol(A^{-})^{1/n} + Vol(B^{-})^{1/n})^{n}$$

$$= Vol(A^{+}) \left(1 + \left(\frac{Vol(B^{+})}{Vol(A^{+})}\right)^{1/n}\right)^{n} + Vol(A^{-}) \left(1 + \left(\frac{Vol(B^{-})}{Vol(A^{-})}\right)^{1/n}\right)^{n}$$

$$= (Vol(A^{+}) + Vol(A^{-})) \left(1 + \left(\frac{Vol(B)}{Vol(A)}\right)^{1/n}\right)^{n}$$

$$= (Vol(A)^{1/n} + Vol(B)^{1/n})^{n}, \tag{6}$$

where the second inequality follows from the induction hypothesis, and the second equality is implied by (5).

**Figure 1**:  $A^+$  and  $B^+$  as defined in the proof of Theorem 1.

# 3 Applications of Brunn-Minkowski Inequality

In this section, we demonstrate the power of Brunn-Minkowski inequality by using it to prove some important theorems in convex geometry.

### 3.1 Volumes of Parallel Slices

Let  $K \in \mathbb{R}^n$  be a convex body. A parallel slice, denoted by  $K_t$ , is defined as an intersection of the body with a hyperplane, i.e.

$$K_t = K \cap \{x \in \mathbb{R}^n | x_1 = t\}. \tag{7}$$

Define the volume of the parallel slice  $K_t$ , denoted by  $v_K(t)$ , to be its (n-1)-dimensional volume.

$$v_K(t) = \operatorname{Vol}_{n-1}(K_t). \tag{8}$$

We are interested in the behavior of the function  $v_K(t)$ , and in particular, in whether it is concave.

Consider the Euclidean ball in  $\mathbb{R}^n$ . The following plots of  $v_K(t)$  for different n suggest that except for n=2, the function  $v_K(t)$  is not concave in t.

As another example, consider a circular cone in  $\mathbb{R}^3$ . The volume of a parallel slice is proportional to  $t^2$ , so  $v_K(t)$  is not concave. More generally,  $v_K(t)$  is proportional to  $t^{n-1}$  for a circular cone in  $\mathbb{R}^n$ . This suggests that the  $(n-1)^{th}$  root of  $v_K$  is a concave function. This guess is verified by Brunn's theorem.

**Theorem 2** (Brunn's Theorem) Let K be a convex body, and let  $v_K(t)$  be defined as in (8). Then the function  $v_K(t)^{\frac{1}{n-1}}$  is concave.

**Proof** Let  $s, r, t \in \mathbb{R}$  with  $s = (1 - \lambda)r + \lambda t$  for some  $\lambda \in [0, 1]$ . Define the (n - 1)-dimensional slices  $K_r, K_s, K_t$  as in (7). First, we claim that

$$(1 - \lambda)A_r \oplus \lambda A_t \subseteq A_s. \tag{9}$$

We show this by proving that for any  $x \in A_r$ ,  $y \in A_t$ , we have  $z = (1 - \lambda)x \oplus \lambda y \in A_s$ , as follows. Connect the points (r, x) and (t, y) with a straight line (see figure 2). By convexity of K, the line lies completely in the body. In particular, the point (s, z), which is a convex combination of (r, x) and (t, y), lies in  $A_s$ . Therefore,  $z \in A_s$  and the claim in (9) is true. Now, by applying the version of Brunn-Minkowski inequality in (2), we have

$$Vol(A_s)^{\frac{1}{n-1}} \geq (1-\lambda)Vol(A_r)^{\frac{1}{n-1}} + \lambda Vol(A_t)^{\frac{1}{n-1}}$$
  

$$\Rightarrow v_K(s)^{\frac{1}{n-1}} \geq (1-\lambda)v_K(r)^{\frac{1}{n-1}} + \lambda v_K(t)^{\frac{1}{n-1}}$$
(10)

Figure by MIT OpenCourseWare.

Figure 2: n-dimensional convex body K in Theorem 2.

#### 3.2 Isoperimetric Inequality

A few lectures ago, we asked the question of finding the body of a given volume with the smallest surface area. The answer, namely the Euclidean ball, is a direct consequence of the Isoperimetric inequality. Before stating the theorem, let us define the surface area of a body using the Minkowski sum.

**Definition 3** Let K be a body. The surface area of K is defined as the differential rate of volume increase as we add a small Euclidean ball to the body, i.e.,

$$S(K) = \operatorname{Vol}(\partial K) = \lim_{\epsilon \to 0} \frac{\operatorname{Vol}(K \oplus \epsilon B_2^n) - \operatorname{Vol}(K)}{\epsilon}.$$
 (11)

Now we state the theorem:

**Theorem 4** (Isoperimetric inequality) For any convex body K, with n-dimensional volume V(K) and surface area S(K),

$$\left(\frac{V(K)}{V(B_2^n)}\right)^{1/n} \le \left(\frac{S(K)}{S(B_2^n)}\right)^{\frac{1}{n-1}}$$
(12)

**Proof** By applying the Brunn-Minkowski inequality, we have the following:

$$V(K \oplus \epsilon B_2^n) \geq \left[ V(K)^{1/n} + \epsilon V(B_2^n)^{1/n} \right]^n$$

$$= V(K) \left[ 1 + \epsilon \left( \frac{V(B_2^n)}{V(K)} \right)^{1/n} \right]$$

$$\geq V(K) \left[ 1 + n\epsilon \left( \frac{V(B_2^n)}{V(K)} \right) \right]$$
(13)

where the second inequality is obtained by keeping the first two terms of the Taylor expansion of  $(1+x)^n$ . Now, the definition of surface area in (11) implies:

$$S(K) = V(\partial K) \geq \frac{V(K) + n\epsilon V(K) \left(\frac{V(B_2^n)}{V(K)}\right)^{1/n} - V(K)}{\epsilon}$$

$$= nV(K) \left(\frac{V(B_2^n)}{V(K)}\right)^{1/n}$$

$$= nV(K)^{\frac{n-1}{n}} V(B_2^n)^{1/n}. \tag{14}$$

For an *n*-dimensional unit ball, we have  $S(B_2^n) = nV(B_2^n)$ . Therefore,

$$\frac{S(K)}{S(B_2^n)} \geq \frac{nV(K)^{\frac{n-1}{n}}V(B_2^n)^{1/n}}{s(B_2^n)^{1/n}}$$

$$\Rightarrow \left(\frac{S(K)}{S(B_2^n)}\right)^{\frac{1}{n-1}} \geq \left(\frac{nV(K)^{\frac{n-1}{n}}V(B_2^n)^{1/n}}{nV(B_2^n)}\right)^{\frac{1}{n-1}}$$

$$= \left(\frac{V(K)}{V(B_2^n)}\right)^{1/n} \tag{15}$$

### 3.3 Grunbaum's Theorem

Given a high-dimensional convex body, we would like to pick a point x such that for any cut of the body by a hyperplane, the piece containing x is big. A reasonable choice for x is the centroid, i.e.

$$x = \frac{1}{\operatorname{Vol}(K)} \int_{y \in K} y dy.$$

This choice guarantees to get at least half of the volume for any origin symmetric body, such as a cube or a ball. The question is how much we are guaranteed to get for a general convex body, and in particular, what body gives the worst case. Do we get a constant fraction of the body, or does the guarantee depend on dimension?

Let us first consider the simple example of a circular *n*-dimensional cone (figure 3). Suppose we cut the cone C by the hyperplane  $\{x_1 = \bar{x}_1\}$  at its centroid, where

$$\bar{x}_1 = \frac{1}{\operatorname{Vol}(C)} \int_{t=0}^h t \cdot \operatorname{Vol}_{n-1} \left( \frac{tR}{h} \right)^{n-1} dt = \frac{n}{n+1} h.$$
 (16)

Grunbaum's theorem states that the circular cone is indeed the worst case if we choose the centroid.

**Figure 3**: *n*-dimensional circular cone.

First we'll need the following lemma:

**Lemma 5** Let  $L = C \cap \{x_1 \leq \bar{x}_1\}$  by the left side of the cone (which is  $x_1$ -aligned with vertex at the origin). Then  $\frac{1}{2} \geq \frac{V(L)}{V(C)} \geq \frac{1}{e}$ .

Proof

$$\frac{V(L)}{V(C)} = \frac{V(\frac{n}{n+1}C)}{V(C)} = \left(\frac{n}{n+1}\right)^n$$
$$\frac{1}{2} \le \left(\frac{n}{n+1}\right)^n \le \frac{1}{e}$$

**Theorem 6** (Grunbaum's Theorem) Let K be a convex body, and divide it into  $K_1$  and  $K_2$  using a hyperplane. If  $K_1$  contains the centroid of K, then

$$\frac{\operatorname{Vol}(K_1)}{\operatorname{Vol}(K)} \ge \frac{1}{e}.\tag{17}$$

In particular, the hyperplane through the centroid divides the volume into almost equal pieces, and the worst case ratio is approximately 0.37: 0.63.

**Proof** WLOG, change coordinates with an affine transformation so that the centroid is the origin and the hyperplane H used to cut is  $x_1 = 0$ . Then perform the following operations:

- 1. Replace every (n-1)-dimensional slice  $K_t$  with an (n-1)-dimensional ball with the same volume to get K', which is convex per Lemma 7 below.
- 2. Turn K' into a cone, such that the ratio gets smaller per Lemma 8 below.

Lemma 7 K' is convex.

**Proof** Let  $K'_t = K' \cap \{x_1 = t\}$  be a parallel slice in the modified body. The radius of  $K'_t$  is proportional to  $V(K_t)^{\frac{1}{n-1}}$ . By applying Brunn-Minkowski inequality, we get that  $V(K_t)^{\frac{1}{n-1}}$  is a concave function in t. Thus K' is convex.  $\blacksquare$ 

**Lemma 8** We can turn K' into a cone while decreasing the ratio.

**Proof** Let  $K'_+ = K' \cap \{x_1 \geq 0\}$ ,  $K'_- = K' \cap \{x_1 \leq 0\}$ . Make a cone  $y\bar{Q}_0$  by picking y having  $x_1$  coordinate positive on the  $x_1$ -axis, and  $V(y\bar{Q}_0) = V(K'_+)$ . Extend the code in the  $\{x_1 \leq 0\}$  region, so that the volume of the extended part equals  $V(K'_-)$ ; name this code C'. Now by Lemma 5, the centroid of C' must lie in  $y\bar{Q}_0$ . Let H' be the translation of H along the  $x_1$ -axis so that it contains the centroid of C'. Then

$$r(K, H) = r(C', H) \ge r(C', H') \ge 1/e.$$

This completes the proof of Grunbaum's theorem.  $\blacksquare$ 

## 4 Next Time

Next time, we will discuss approximating the volume of a convex body.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.409 An Algorithmist's Toolkit

10/29/09

## Lecture 14

Lecturer: Jonathan Kelner

# 1 Approximating the volume of a convex body

Exactly computing the volume a convex body is known to be #P-hard, so the fact that we can approximate its volume in P is surprising—the kind of result you would bet against until you saw it was true.

Before discussing any algorithms, though, we need to say what it means to be given a convex body K. To keep our implementation as general as possible, we'll assume that K is given by some oracle:

## 1. Membership oracle

Given a point p, returns 'yes' if  $p \in K$  and 'no' if  $p \notin K$ .

#### 2. Separation oracle

Given a point p, returns 'yes' if  $p \in K$  and a separating hyperplane H if  $p \notin K$ .

Given a reasonable description of a convex body, it is easy to build a separation oracle. For example,

#### 1. A ball of radius r

Given p, compute its norm |p|. If less than r, return 'yes'; if greater than r, return the hyperplane tangent to the boundary sphere at rp/|p|.

## 2. A cube of side length s

Given p, compute its  $l_{\infty}$  norm. If less than s/2, return 'yes'; if greater, return the face of the cube in the violated direction.

#### 3. A polytope

Given p, check each inequality. If it satisfies them all, return 'yes'; if not, return the failed inequality.

In what follows, we'll assume that our convex body contains a ball of radius 1 centered at the origin, and is contained within a ball of radius  $2^{\text{poly(n)}}$ . These conditions are reasonable—after suitable translation and dilation, they hold for any K specified by inequalities of polynomial bit length.

Given a membership oracle, how could we approximate volume? The naive Monte Carlo algorithm—pick points from some designated region (say a ball) and check if they're in K-in general fails. If K is an ellipse with major axis of exponential length l and minor axis  $l^{-1}$ , then the probability of a successful trial is exponentially small. No chance of a polynomial time algorithm. But if the body is well-rounded, say  $B_2^n \subseteq K \subseteq nB_2^n$ , then the following algorithm has a chance:

- 1. Pick points  $p_1, \dots, p_m$
- 2. Check if  $p_i \in K$
- 3. Set  $K' := \operatorname{conv}\{p_i | p_i \in K\}$
- 4. Return the volume of K'

If n = 2, this algorithm works:

**Theorem 1** For any  $\epsilon > 0$ , there exists a set  $P = \{p_1, \dots, p_m\}$  s.t. m is polynomial in  $1/\epsilon$  and for any well-rounded 2-dimensional convex body K,  $Vol(conv(P \cap K)) \ge Vol(K)/(1 + \epsilon)$ .

For example, a grid with spacing  $\epsilon/8$  works. In higher dimensions, though, a grid has exponentially many points. It's also difficult to compute the convex hull of a bunch of points in high dimensions. We could try to construct our set of points more carefully, perhaps tailoring them based on our knowledge of the body so far. It turns out that such an algorithm cannot succeed.

**Theorem 2** There is no deterministic poly time algorithm that, given a membership oracle for K, computes Vol(K) within a polynomial factor.

**Proof** Since the algorithm is deterministic, an adversary can construct a worst-case K depending on the queries. Her evil plan is to answer 'yes' to each query p if  $p \in B_2^n$ , so at the end of the algorithm, the only data known about the convex body is that it contains a polynomial number of points  $P = \{p_1, \ldots, p_m\} \subset B_2^n$ , and not certain points outside of the ball. Hence the algorithm cannot distinguish between  $K_1 = B_2^n$  and  $K_2 = \text{conv}(p_1, \ldots, p_m)$ . We will show that for any such polynomial collection of points, the ratio  $\text{Vol}(K_1)/\text{Vol}(K_2)$  is exponentially large, dooming our algorithm to defeat.

For each  $p_i$ , denote  $B_i$  by the ball centered at  $p_i/2$  of radius  $|p_i|/2$ . Now we claim that  $\operatorname{conv}(P) \subseteq \bigcup B_i$ . We can rewrite  $B_i$  as  $\{x | \angle p_i x O \ge \pi/2\}$ . Let  $v \in \overline{p_i p_j}$ . We'll show that  $B_v \subset B_i \cup B_j$ , where  $B_v$  is the ball centered at v/2 of radius |v|/2. For any point  $x \in B_v$ , we have  $\angle v x O \ge \pi/2$ . We consider three cases:

- 1.  $x \in \triangle Op_i p_j$ . Then  $\angle Oxp_i + \angle Oxp_j + \angle p_j xp_i = 2\pi$  gives  $\angle Oxp_i + \angle Oxp_j \ge \pi$ , and one angle must be at least  $\pi/2$ .
- 2. x is outside the triangle in the  $p_i$  direction, so  $\angle Oxp_i \ge \angle Oxv \ge \pi/2$
- 3. x is outside the triangle in the  $p_i$  direction, so  $\angle Oxp_i \ge \angle Oxv \ge \pi/2$

Hence  $B_v \subset \bigcup B_i$  for any v in the boundary of the convex hull of the  $p_i$ . Since any  $x \in \text{conv}(P)$  is a linear combination of two points v, w on the boundary,  $x \in B_x \subset B_v \cup B_w \subset \bigcup B_i$ . Hence the volume of the convex hull is at most

$$\operatorname{conv}(\operatorname{Vol}(P)) \le \sum_{i=1}^{m} \operatorname{Vol}(B_i) \le \frac{m}{2^n} \operatorname{Vol}(B_2^n).$$

One can show that separation oracles are also insufficient for creating a deterministic polynomial time algorithm. It is worth noting that, together with our randomized algorithm for approximating the volume of a convex body, we have proved that the separation oracle A separates P from BPP, i.e.,  $P^A \neq BPP^A$ . But it is widely believed that P = BPP. What's going on? There exist bodies without polynomial time separation oracles.

# 2 The Algorithm

We will give a randomized, polynomial time algorithm for approximating the volume of a convex body, given a separation oracle. The presentation roughly follows the original Dyer, Frieze, Kannan paper, and gives a very bad polynomial (degree  $\approx 30$ ). There are now algorithms running in  $O(n^4)$ . The strategy is similar to the one we used to approximate the permanent, finding a nested sequence of sets where random sampling hits with polynomial probability, and then multiplying the ratios.

Given a method for sampling from a convex body, we can implement the following (sketched) algorithm:

- 1. Change coordinates so that K is well-rounded ,  $B \subseteq K \subseteq nB$
- 2. Let  $\rho = 1 + 1/n$ , and let  $K_i = K \cap \rho^i B$ . Compute

$$\gamma_i = \frac{\operatorname{Vol}(K_{i-1})}{\operatorname{Vol}(K_i)}$$

## 3. Return $Vol(B) \prod \gamma_i$

The first step can be done with the separating oracle and the ellipsoid algorithm, or the method on the problem set. The last step works since  $K_0 = K \cap B = B$  and  $K_N = K \cap nB = K$ . For the second step, we need to sample. It's easy to sample from highly symmetric objects: the cube is given by n uniforms, U[0,1], the sphere by n gaussians, appropriately rescaled, the ball by picking the direction, then the radius. For nonsymmetric bodies, the best bet is a random walk. There are a few ways walk:

#### 1. Grid Walk

Intersect a grid with the body; walk on the resulting graph.

#### 2. Ball Walk

At a point p, pick a random neighbor in a small ball centered at p, and walk there.

### 3. Hit and Run

At a point p, draw a random line l through p and walk to a random point  $l \cap K$ .

We'll use the grid walk. Drop a width  $\delta$  grid on  $\mathbb{R}$ , the graph H with vertices  $\delta\mathbb{Z}^n$  with edges  $p \to p \pm \delta e_i$ , and set  $G = H \cap K$ . We can walk on G using a membership oracle; walk on H, and if you would go to a neighbor not in G, choose again. Note that H has degree 2n, but exponentially many vertices, so we need to show that the walk mixes very quickly. This is plausible though, and is easily seen when G is just a cube with side length  $\leq n/\delta$ . Since the path  $P_{n/\delta}$  mixes in time polynomial in  $n/\delta$ , and the cube is just the product  $P^n$ , its mixing time is n times that of the path, so still polynomial. There are still many problems with using a the walk on G to approximate K.

- 1. We're only sampling lattice points. After walk mixes, we could take a random vector v from the cube of width  $\delta$  centered at  $p \in G$ . But if  $p + v \notin K$ , we're in trouble. We could throw it out and re-sample, but this would overweight points near the boundary. Alternatively, we could start the whole walk over, which is acceptable as long as the probability of landing outside is small.
- 2. The graph might be (close to) bipartite. Just use the lazy walk.
- 3. The graph has nonconstant degree. Throw in self-loops for vertices near boundary. Equivalently, our walk is: pick a random vector  $v \in \pm e_i$ ; if  $p + v \in K$ , go there, otherwise, stay put.
- 4. The graph G might not be connected! If K has a sharp angle, then the vertex of G closest to the corner will not be adjacent to any other vertices of G. Finer grids don't help, as this is a problem with the angle itself.

We'll fix the last problem next lecture, by walking on the graph G associated to  $K' = (1 + \epsilon)K$ .

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 18.409 An Algorithmist's Toolkit | November $3^{rd}$ , 2009 |
|----------------------------------|--------------------------|
| Lecture 15                       |                          |
| Lecturer: Jonathan Kelner        | Scribe: Justin Thaler    |

### 1 Outline

In this lecture we will design a method to randomly sample from a convex body, and this method will be a subroutine in approximately computing volume

### 2 Reminder from Last Time

In the last lecture, we showed that no deterministic algorithm that queries a membership oracle only a polynomial number of times, can approximate the volume of a convex body to within a factor of  $\frac{m}{2^n}$  where m is the number of membership queries. However, a randomized algorithm can approximately compute the volume of a convex body and the procedure will be similar to the Jerrum and Sinclair method for approximating the permanent. The algorithm will construct a series of convex bodies, and the ratio of successive convex bodies in the series can be well-approximated. These approximations will be used to approximate the volume of the original convex body K, even if K has exponentially small volume compared to the bounding sphere that is guaranteed to contain K.

Last time, we presented the following sketch of how our randomized algorithm will work.

- 1. Change coordinates s.t. K is well-rounded, i.e.  $B \subseteq K \subseteq nB$
- 2. Let  $\rho = 1 + 1/n$ , and let  $K_i = K \cap \rho^i B$ . Compute  $\gamma_i = \frac{V(K_{i-1})}{V(K_i)}$
- 3. Return  $V(B) \prod \frac{1}{\gamma_i}$

Note that Step 3 works because  $K_0 = K \cap B = B$ . Also note that the first part isn't too hard using the ellipsoid algorithm, which we mention briefly near the end of these notes.

#### 3 Grid Walk

To approximately compute volume in Step 2 of our sketch above, we need a method to sample randomly from a convex body K. To do this, we will use a random walk and we will need to bound the mixing time of the random walk. There are a number of random walks that can be used to sample randomly from a convex body, and the most basic is the Grid Walk.

Define a grid graph H, such that nodes are points in  $\delta Z^n$ . The define the graph  $G = H \cap K$  as the subgraph of nodes in H that are also contained in the convex body K. For sufficiently small  $\delta$ , a random vertex in G is roughly a random point in K

The graph G can contain an exponential number of vertices. Consider the convex body K, the hyper-cube  $[-1,1]^n$ . We must show that even if the number of vertices is exponential, that the random walk mixes in polynomial time. Returning to the example of the hyper-cube, the hyper-cube is the graph product of n line graphs. Each line graph has a mixing time  $c^2$  if there are c nodes. Then a random walk on the grid graph is a choice of the direction to walk in, and a random step on the corresponding line graph. The walk mixes in  $O(nc^2logn)$  steps, because in expectation O(nlogn) steps are needed to ensure that a step is taken in all directions (this is an instance of the coupon-collector problem), and when  $O(c^2)$  steps have been taken in each direction, a random walk on the hyper-cube is mixed.

## 4 Problems with our Approach

We only sample grid points. A first-cut fix is to generate a random vertex p in G, and then add a random vector k in the cube  $[-\frac{\delta}{2}, \frac{\delta}{2}]$  to the point p. However p+k is not necessarily in K. We could generate another k in the cube, and try again - but if the nodes in G are generated uniformly at random, then a cube containing points in K and points not in K will generate the points in K disproportionately often compared to points in K that are in a cube that only contains points in K. This problem can be avoided by restarting the random sample procedure when a point p+k is generated that is not in K. A more serious problem is that not all points in K can be generated.

Also, the graph G is bipartite because the full grid H is bipartite, and G is a subgraph of H. Then a random walk will be periodic. Also, not all nodes in G have the same degree and the limiting distribution is not necessarily uniform on the nodes in G. These problems can be fixed by adding self-loops at each node, and adding extra self-loops at any node that is not connected to 2n nodes in G. The degrees in the graph can be made equal, and the limiting distribution will be uniform on the nodes.

The graph G need not even be connected.

Intuitively, this problem arises when K contains sharp boundaries and these problems can be removed by rounding out K. A possible approach is to set  $K(\alpha) = K \oplus \alpha B_2^n$ , or to set  $K' = (1 + \alpha)K$ . The approaches can both be made to work, but consider K'. By assumption  $B_2^n \subset K$  and  $\alpha B_2^n + K \subset K'$ . Choose  $\alpha = \delta \sqrt{n}$  equal to the diameter of a cube. Then all cubes contained in K have a neighbor in all 2n directions that is contained in K', and for all points p in K there is a cube in K' that contains p.

Run a random walk on K', and at any cube generate a random point p + k. If this point is not in K, then start the random walk over. Provided that there are not too many cubes near the boundary or entirely in K', in expectation we will not need to run the random walk many times before obtaining a random point in K. Then this defines a random walk on the graph  $G' = H \cap K'$ , and again self-loops can be added to each vertex to ensure that G' is regular and that the random walk is aperiodic.

Consider an arbitrary cube C that contains points in K, and points not in K. A point in  $K \cap C$  is generated with probability equal to the fraction of volume in C also in K, once the node corresponding to the cube C is reached. Because all points in K can be generated, then this random walk generates points in K uniformly at random.

# 5 Mixing

The above random walk will generate a random sample from any body K. Convexity is not needed to ensure that this random walk produces a random sample, but is needed to ensure that the random walk mixes quickly. Consider the body K given in the figure below. Intuitively, this walk mixes slowly for the same reasons that a random walk on a graph containing two cliques connected by a long path does.

To bound the mixing time for a random walk on a convex body K, we need to bound the isoperimetric number or conductance of G. Then for any set S of nodes in G such that  $|S| \leq \frac{|V(G)|}{2}$ , the isoperimetric number for S is  $\frac{|E(S)|}{|S|}$ . Each cube contains the same volume, and the size of S is proportional to the volume of Q(S) -  $Vol_n(Q(S))$ , the space enclosed by the cubes corresponding to nodes in S. Similarly, each edge leaving S corresponds to a face on the surface of Q(S), and each face has the same surface area. Then the number of edges leaving S is proportional to  $Vol_{n-1}(dQ(S))$ . If the space Q(S) does not intersect the boundary of K, then this is exactly the isoperimeteric number of the graph. To incorporate the boundary, we need a Relative Isoperimetric Inequality.

**Theorem** Let  $K \subset \mathbb{R}^n$  be a convex body with diameter d. Let S be an n-1 dimensional surface that cuts K into two pieces A and B. Then

$$min\{Vol_n(A), Vol_n(B)\} \le dVol_{n-1}(S)$$

Again, if A does not intersect the boundary (and is round enough) then this is approximately the standard isoperimeteric inequality. Also, we can define the isoperimeteric constant (or Cheeger constant) for any body X (not necessarily convex) as the minimum  $\phi$  such that

$$min\{Vol_n(A), Vol_n(B)\} \le \phi Vol_{n-1}(S)$$

Isoperimetric inequalities arise naturally in bounding the mixing time of any "diffusion" process.

# 6 Approximate Proof

The n-1-dimensional volume is more subtle to work with, and this theorem can be proven by proving a related theorem.

**Theorem** Let  $K \subset \mathbb{R}^n$  be a convex body with diameter d. Decompose K into  $A \cup B \cup S$ , where  $dist(A, B) \geq t$ . Then

$$min\{Vol_n(A), Vol_n(B)\} \le \frac{d}{t}Vol_n(S)$$

The original theorem is proven by decreasing t to zero. Let E be the smallest volume ellipse containing K. Then there are two cases to consider.

Case 1: The ellipse E is needle-like, which we define to mean all but at most 1 axis of E is of radius  $\leq \epsilon t$  for a small enough  $\epsilon$ . In this case, the theorem is true by inspection.

Case 2: The ellipse E is not needle-like. Then we can apply a symmetrization procedure until the ellipse is needle-like. Suppose that there exists a counter-example to our theorem, then by the Ham Sandwhich Theorem there exists a hyperplane that simultaneously cuts A into  $A_1$ ,  $A_2$  and B into  $B_1$ ,  $B_2$  such that  $A_1$  and  $A_2$  have equal volume, and so do  $B_1$  and  $B_2$ . Then the hyperplane cuts S into  $S_1$ ,  $S_2$  and one of the convex bodies  $A_1 \cup B_1 \cup S_1$  OR  $A_2 \cup B_2 \cup S_2$  is a counter-example that is closer to needle-like.

Iterating this procedure, we can eventually reduce all but at most one dimension to  $\leq \epsilon t$ , and this produces a contradiction because the theorem is true when the bounding ellipse is needle-like.

### 7 The Rest of the Details

- 1. We need to make sure we can arrange for our convex body K to be polynomially well-rounded to make sure the diameter isn't too big. The rough idea is that if K is far from isotopic (i.e. not well-rounded) we can find a point far from the origin using the ellipsoid algorithm and use this to construct a better John Ellipse; see the problem set for details.
- 2. We need to show that isoperimetry of our graph is properly related to isoperimetry of the body near the boundary. This is where we use rounding of the corners of K.
- 3. Finally, we need to show that we don't reject too many samples.
- 4. Once we've done all of the above, we get an algorithm for sampling from any convex body K, and can use this to estimate the volume as per our sketch at the beginning of these notes.

### 8 Concentration of Measure and Geometric Probability Theory

#### 8.1 The Chernoff (Hoeffding-Azuma-Bernstein-...) Bound

The question here is how to think of a convex body relating in some way to probability theory. We've been doing a lot of things with convex bodies and probabilities and there should be a lot of overlap. We sort of did this last time with isoperimetry but now we will be much more concrete. We'll think of points in the convex body as being points of a probability distribution. We'll have interesting, very strong theorems that go both ways in implications, that will appear unlikely. The main point is that we keep coming up with the phenomenon that volume in convex bodies is counterintuitively distributed, more or less pervasively for high-dimensional spaces. We've seen this over and over but we'll make it more concrete now. We already have the first concentration of measure theorem from earlier in the semester: the Chernoff bound.

**Theorem 1** Let  $x \in \{\pm 1\}^n$  be independent random variables with  $p[x_i = 1] = .5$ , and  $a_1, \ldots, a_n$  satisfying  $\sum a_i^2 = 1$  (some can be negative). Then

$$Pr\left[\left|\sum_{i=1}^{n} a_i x_i\right| > i\right] \le 2e^{-t^2/2}$$

I assert this is the same bound we already did. Now, let's change it so that the  $x_i$  are anywhere in [-1/2, 1/2]. The bound is still true up to some constants. Let's see what this means geometrically.

Claim 2 
$$\sum a_i x_i = a \cdot x = distance \ of \ x \ from \ hyperplane \ H_a = \{x | a \cdot x = 0\}.$$

Pictorially, that means I can take the unit cube in  $\mathbb{R}^n$ , pick any hyperplane at all, and we cut the cube with it, and that gives us some intersection with the interior of the cube. What it says is that no matter how we choose this hyperplane, almost all of the cube is pretty close to this hyperplane. I claim this is our first concentration of measure theorem.

Another way we can phrase this, so you get a hint of where I'm going with this, is to say that

$$\frac{\operatorname{Vol}(S)}{\operatorname{Vol}([-1/2, 1/2]^n)} \ge 1 - 2e^{-6t^2}$$

Here, we define S to be the set of all points within distance t of  $H_a$ .

So what is a little neighborhood of S? I've shown that it's "pretty big" as a function of the volumes involved. This is not exactly the isoperimetric inequality because we're looking at big sets, not small sets, and the set, not its complement. It's a different parameter regime but the same kind of question. Somehow we have three phenomena in this course that all come out to be the same thing: isoperimetric inequalities, Chernoff bounds, and this phenomenon of volume in convex bodies.

| MIT C   | penCourseWare |
|---------|---------------|
| http:// | ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

#### Lecture 16

Lecturer: Jonathan Kelner Scribe: Paul Christiano

# The Chernoff Bound as Concentration of Measure

We have already seen some ways in which convex bodies are related to probability. For example, we can think of the Chernoff bound as the statement that for any unit vector a and real t, if x is chosen uniformly at random from the cube then

$$\Pr\left[|a \cdot x| > t\right] \le 2e^{-6t^2}.$$

Since  $|a \cdot x|$  is the distance of x from the hyperplane orthagonal to a, this says that all but  $2e^{-6t^2}$  of the volume of the cube lies at distance at most t from this hyperplane. Since a was arbitrary, we can conclude that  $1 - 2e^{-6t^2}$  of the volume of the cube lies within t of any hyperplane through the origin.

On the sphere we also observed that almost all of the volume lies very close to any hyperplane through the origin. In light of the probabilistic implications of this assertion for the cube we are motivated to consider them for the sphere. First we will need to derive a stronger statement for the sphere.

### The Isoperimetric Inequality on the Sphere

We will consider the analogue of the isoperimetric question for subsets of the surface of the sphere. This requires analogues of the notions of distance, volume, and surface area.

We define the distance d(x,y) between points  $x,y \in S^{n-1}$  to be their distance in the usual Euclidean metric in  $\mathbb{R}^n$ .

For volumes, we use the unique rotationally invariant measure on the surface of the sphere. The volume Vol(A) of a region A on the surface of the sphere is the volume of the union in  $\mathbb{R}^n$  of all segments connecting the origin to a point of A, normalized so that the volume of the whole sphere is 1. Alternatively, this is Haar measure when the sphere is given the natural Lie group structure. (You can do anything reasonable and get the same measure.)

For surface areas, we use the same definition as in  $\mathbb{R}^n$ . Namely, for a set  $A \subset S^{n-1}$ , define  $A_{\epsilon}$  to be the set of points in  $S^{n-1}$  at a distance of less than  $\epsilon$  from some point of A. The surface area of A may be defined as  $\partial_{\epsilon} A_{\epsilon}$ . We won't work with this quantity-instead we will derive bounds on  $Vol(A_{\epsilon})$  itself for  $\epsilon > 0$ .

Now the isoperimetric question is: among sets with a fixed Vol(A), what is the minimal possible value of  $Vol(A_{\epsilon})$ ?

The answer is the analogue of a ball: a spherical cap. More precisely, define

$$C(r, v) = \{ x \in S^{n-1} : d(x, v) \le r \}.$$

This is the ball of radius r centered at v in the metric we have defined on the sphere. This result is precisely analogous to the isoperimetric inequality in  $\mathbb{R}^n$ . (The statement itself will be slightly more complicated because the optimal ratio  $A_{\epsilon}/A$  depends on the volume of A: a small cap is basically a ball in  $\mathbb{R}^{n-1}$ , while a very large cap has a very small surface area)

For convenience, we will also define the "cap at height t":

$$c_t = c(t, v) = \{x \in S^{n-1} : x \cdot v \ge t\}.$$

We have seen previously that the volume of a section of the sphere at height t is exponentiall small. From this it follows that the volume of c(t, v) is exponentially small in t. In fact,  $\operatorname{Vol}(c(t, v)) \approx e^{-nt^2/2}$ .

We will prove an approximation to this result soon, but first we consider some consequences.

**Theorem 1** For any A with Vol(A) = 1/2,  $Vol(A_{\epsilon}) > 1 - e^{-n\epsilon^2/2}$ .

**Proof** If A were a spherical cap, then  $A_{\epsilon}$  would be the complement of the spherical cap at height  $\epsilon$ , which has volume  $1 - e^{-n\epsilon^2/2}$ . But by the isoperimetric inequality this is the minimum possible value of Vol $(A_{\epsilon})$ .

This theorem shows that for spheres in high enough dimension almost all of the volume of the sphere lies within  $\epsilon$  of any set containing at least half the volume of the sphere. In fact almost all of the volume of the sphere lies within  $\epsilon$  of any set containing any constant fraction of the volume of the sphere (although the constants in the theorem would change).

We will now go on to use this result to conclude that Lipschitz functions are almost always close to their median.

# Lipschitz Functions and Concentration of Measure

**Definition 2 (1-Lipschitz)** A function  $f: S^{n-1}\mathbb{R}$  is 1-Lipschitz if  $|f(a)-f(b)| \leq |a-b|$  for all  $a,b \in S^{n-1}$ .

It turns out that many reasonable functions are Lipschitz. For example, distance from a fixed set is Lipschitz.

Define a median M of a Lipschitz function to be a value M such that  $Vol(\{x: f(x) \leq M\}) \geq Vol(\{x: f(x) \geq M\}) = 1/2$ .

If we take f were one of the coordinate functions (which are Lipschitz), then the statement that most of the volume of a sphere lies near any hyperplane through the origin becomes the statement that the value of f is almost always near its median. We will see that in fact all Lipschitz functions are almost always near their median.

**Theorem 3** If f is Lipschitz, M is its median, and  $\epsilon > 0$ , then

$$Vol({x : |f(x) - M| > \epsilon}) \le 2e^{-n\epsilon^2/2}.$$

**Proof** The set  $A = f(x) \leq M$  has volume at least 1/2. The set  $f(x) \leq M + \epsilon$  contains  $A_{\epsilon}$ . Therefore by the isoperimetric inequality,  $f(x) \leq M + \epsilon$  holds for at least  $1 - e^{-n\epsilon^2/2}$  of the volume of the sphere. Similarly,  $f(x) \geq M - \epsilon$  holds for  $1 - e^{-n\epsilon^2/2}$  of the volume of the sphere. Therefore in total  $|f(x) - M| > \epsilon$  for at most  $2e^{-n\epsilon^2/2}$  of the volume of the sphere (since at every point where this inequality holds at least one of the previous two must fail).

Although the range of a 1-Lipschitz function may have diameter 2, this result shows that 1-Lipschitz functions are almost constant over most of their domain. We call this result "concentration of measure."

Note that this result doesn't rely on the exact form of the isoperimetric inequality; it would be fine if the bound on the ratio  $Vol(A_{\epsilon})/Vol(A)$  was somewhat weaker.

# The Isoperimetric Inequality

We will prove a weaker statement than the full isoperimetric inequality because it is somewhat easier. Normally we would have to use a symmetrization argument, but after weakening the constantants we will be able to apply Brunn-Minkowski.

**Theorem 4** For any  $A \subset S^{n-1}$  and any  $\epsilon > 0$ 

$$\operatorname{Vol}(A_{\epsilon}) > 1 - \frac{2e^{-n\epsilon^2/16}}{\operatorname{Vol}(A)}.$$

#### Proof

We will need the following definition.

**Definition 5 (Modulus of Convexity)** The modulus of convexity  $\delta$  for a sphere is

$$\delta(\epsilon) = \inf \left\{ 1 - \left| \frac{x+y}{2} \right| : x, y \in S^{n-1}, |x-y| \ge \epsilon \right\}.$$

It is a matter of two dimensional geometry to compute

$$\delta(\epsilon) = 1 - \sqrt{1 - \frac{\epsilon^2}{4}} \ge \epsilon^2 / 8.$$

(where the inequality comes from the Taylor series).

This quantity measures how much more curved the sphere is than required by convexity. Namely, by convexity we are guaranteed that  $\delta(\epsilon) \leq 1$  (which we would obtain in the  $L_1$  or  $L_{\infty}$  norm). If  $\delta(\epsilon)$  is smaller, it means that longer segments lie well inside the convex body.

We would like to apply Brunn-Minkowski, but we don't have any result of that sort for the surface of the sphere. We will pass to a spherical shell, for which we can apply Brunn-Minkowski. Namely, if  $A \subset S^{n-1}$  consider  $B = [\frac{1}{2}, 1]A$ — the union of the sets xA for  $\frac{1}{2} \le x \le 1$ . Note that  $\operatorname{Vol}(B) \ge \operatorname{Vol}(A)/2$ , where the volume of B is taken in  $\mathbb{R}^{n-1}$  normalized so that  $B^n$  has volume 1 and the volume of A is taken in  $S^{n-1}$  normalized so that  $S^{n-1}$  has volume 1. The choice of 1/2 in particular is not important. All that matters is that neighborhoods of  $[\frac{1}{2}, 1]A$  centrally project to reasonable neighborhoods of  $S^{n-1}$ ; if we took (0, 1]A, neighborhoods near the origin could project to almost all of  $S^{n-1}$ .

To go from a set  $B \subset B^n$  to an  $A \subset S^{n-1}$  we take  $\left\{\frac{x}{|x|} : x \in B\right\}$ . Note that if we define  $B = \left[\frac{1}{2}, 1\right]A$ , take  $B_{\epsilon}$ , and then convert this back to a subset of  $S^{n-1}$ , we do not necessarily obtain  $A_{\epsilon}$ . A point within  $\epsilon$  of  $\frac{1}{2}A$  may project back to a point on  $S^{n-1}$  as far as  $2\epsilon$  from A. In fact this is the worst that can happen, so that  $B_{\epsilon}$  is carried back into  $A_{2\epsilon}$ . We would like to say that the volume of  $B_{\epsilon} \cap B^n$  is at least the volume of  $A_{2\epsilon}$ , so that we can convert a bound on the size of  $B_{\epsilon}$  from Brunn-Minkowski into a bound on the size of  $A_{2\epsilon} \supset A_{\epsilon}$ . This isn't quite true- $B_{\epsilon}$  may contain points of norm < 1/2. However, all points in  $B_{\epsilon}$  have norm at least  $1/2 - \epsilon$ , so it turns out this does not have a significant effect (Vol  $\left(\left[\frac{1}{2} - \epsilon, \frac{1}{2}\right]A\right)$  is very small).

We will show that  $Vol(B_{\epsilon} \cap B^n) \ge 1 - e^{-2n\delta}/Vol(B)$ . This will give us the desired result, since then

$$\operatorname{Vol}(A_{2\epsilon}) > (1+\epsilon)\operatorname{Vol}(B_{\epsilon} \cap B^n) \ge 1 - \frac{e^{-2n\delta(2\epsilon)}}{\operatorname{Vol}(B)} \ge 1 - 2\frac{e^{n\epsilon^2/2}}{\operatorname{Vol}(A)}$$

which is what we wanted.

To bound the volume of  $B_{\epsilon} \cap B^n$ , let C be the set of points of  $B^n$  at least  $\epsilon$  away from every point of B. For any  $x \in B$  and any  $y \in C$ , by the definition of modulus of convexity  $\frac{|x+y|}{2} \le 1 - \delta(\epsilon)$  (the worst case is that both lie in  $S^{n-1}$ ). This implies that  $B \oplus C \subset (1-\delta)B^n$ , so that  $Vol(B \oplus C)^{1/n} \le (1-\delta)$ . Now by Brunn-Minkowski,

$$(1 - \delta) \ge \operatorname{Vol}(B \oplus C)^{1/n} \ge \operatorname{Vol}(B)^{1/n} + \operatorname{Vol}(C)^{1/n}.$$

By easy calculus or the power-mean inequality, and the inequality  $e^{-x} \ge 1 - x$ , we conclude

$$Vol(B)^{1/2}Vol(C)^{1/2} \le (1 - \delta)^n$$

$$Vol(C) \le (1 - \delta)^2 n / Vol(B) \le e^{-2n\delta} / Vol(B)$$

Taking complements in  $B^n$ ,

$$Vol(B_{\epsilon} \cap B^n) = 1 - Vol(C) \ge 1 - \frac{e^{-2n\delta}}{Vol(B)}$$

as desired.

#### Johnson-Lindenstrauss

Johnson-Lindenstrauss can be proved by manipulating Gaussians, but it is quite easy with concentration of measure. For now we will just give the setup and outline some applications.

This is the first example we have seen of the notion of metric embeddings, which turn out to be generally algorithmically useful. Given a metric d on a finite set of points X, we would like to find a map  $f: X \to \mathbb{R}^n$  such that  $d(x,y) \approx d(f(x),f(y))$  for the normal Euclidean metric d on  $\mathbb{R}^n$ . More precisely, for any map  $f: X \to \mathbb{R}^n$  we define the distortion D to be the ratio between the largest and smallest values of  $\frac{d(x,y)}{d(f(x),f(y))}$  as x and y vary. We would like to find an embedding with  $1 + \epsilon$  distortion.

The Johnson-Lindenstrauss Theorem states that if the metric on X arises from an embedding of X into any Euclidean space, then X can be embedded with distortion at most  $1 + \epsilon$  in  $R^k$  for  $k = O(\epsilon^2 \log |X|)$ . More concretely, this embedding is given by projection onto a random k-dimensional subspace, and the ratio d(x,y)/d(f(x),f(y)) is very nearly  $O(\sqrt{k/n})$ .

This result is extremely useful in a number of situations. If I wish to answer some question about a fixed set of points which depends only on their pairwise distances, then Johnson-Lindenstrauss allows us to reduce the problem to one in logarithmic dimension (for fixed  $\epsilon$ ) by randomly projecting. If our algorithm has bad dependence on the dimension, this may reduce the runtime considerably (for example, exponential dependence becomes polynomial). Similarly, if I am dealing with a stream of very high-dimensional data and I do not have storage space to record it all, Johnson-Lindenstrauss allows us to retain a very small fraction of this data while preserving the answer to any question which depends only on distances.

We will prove this result in the next lecture.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

18.409 An Algorithmist's Toolkit

Nov. 10, 2009

### Lecture 17

Lecturer: Jonathan Kelner

## 1 Johnson-Lindenstrauss Theorem

## 1.1 Recap

We first recap a theorem (isoperimetric inequality) and a lemma (concentration) from last time:

**Theorem 1 (Measure concentration on the sphere)** Let  $\mathbb{S}^{n-1}$  be the unit sphere in  $\mathbb{R}^n$  and  $A \in \mathbb{S}^{n-1}$  be a measurable set with  $vol(A) \geq 1/2$ , and let  $A_{\varepsilon}$  denote the set of points of  $\mathbb{S}^{n-1}$  with distance at most  $\varepsilon$  from A. Then  $vol(A_{\varepsilon}) \geq 1 - e^{-n\varepsilon^2/2}$ .

This theorem basically says that: When we get a set A which is greater or equal to half of the sphere, if we further incorporate points at most  $\varepsilon$  away from A, we almost have the whole sphere.

**Definition 2 (c-Lipschitz)** A function  $f: A \to B$  is c-Lipschitz if, for any  $u, v \in A$ , we have  $||f(u) - f(v)|| \le c \cdot ||u - v||$ 

For a unit vector  $x \in \mathbb{S}^{n-1}$ , the projection of the first k dimension is a 1-Lipschitz function,:

$$f(x) = \sqrt{x_1^2 + x_2^2 + \dots + x_k^2}$$

**Lemma 3** For a unit vector  $x \in \mathbb{S}^{n-1}$ , and  $f(x) = \sqrt{x_1^2 + x_2^2 + \dots + x_k^2}$ . Let x be a vector randomly chosen with uniform distribution from  $\mathbb{S}^{n-1}$  and M be the median of f(x). Then f(x) is sharply concentrated with:

$$Pr[|f(x) - M| \ge t] \le 2e^{-t^2n/2}$$

#### 1.2 Metric Embedding

**Definition 4 (D-embedding)** Suppose that  $X = \{x_1, x_2, \dots x_n\}$  is a finite set, d is a metric on X, and  $f: X \to \mathbb{R}^k$  is 1-Lipschitz, with  $||f(x_i) - f(x_j)|| \le d(x_i, x_j)$ . The "distortion" of f is the minimum D for which

$$||f(x_i) - f(x_j)|| \le d(x_i, x_j) \le D||f(x_i) - f(x_j)||$$

for some positive constant  $\alpha$ . We refer to f as a D-embedding of X.

Claim of Johnson-Lindenstrauss Theorem: The Euclidean metric on any finite set X (a bunch of high dimensional points) can be embedded with distortion  $D = 1 + \varepsilon$  in  $\mathbb{R}^k$  for  $k = O(\varepsilon^{-2} \log n)$ .

If we lose  $\varepsilon$  ( $\varepsilon=0$ ), it becomes almost impossible to do better than that in  $\mathbb{R}^n$ . Nevertheless, it is not hard to construct a counter example to this: a simplex of n+1 points. The Johnson-Lindenstrauss theorem gives us an interesting result: if we project x to a random subspace, the projection y give us an approximate length of x for some fixed multiplication factor c, i.e.  $||x|| \sim c \cdot ||y||$ . And  $c \cdot y$  is embedded with distortion  $D=1+\varepsilon$ .

#### 1.3 Proof of the Theorem

Next, we provide a more precise statement about Johnson-Lindenstrauss Theorem:

**Theorem 5 (Johnson-Lindenstrauss)** Let  $X = \{x_1, x_2, \dots x_n\} \in \mathbb{R}^m$  (for any m) and let  $k = O(\varepsilon^{-2} \log n)$ .

- $\mathfrak{L} \subseteq \mathbb{R}^m$  be a uniform random k dimensional subspace.
- $\{y_1, y_2, \cdots y_n\}$  be projections of  $x_i$  on  $\mathfrak{L}$ .
- $y_i' = cy_i$  for some fixed constant c, and  $c = \Theta(\frac{k}{m})$

Then, with high probability  $\mathfrak{L}$  is a  $(1+\varepsilon)$ -embedding of X into  $\mathbb{R}^k$ , i.e. for  $x_i, x_j \in X$ 

$$||x_i - x_j|| \le ||y_i' - y_j'|| \le (1 + \varepsilon)||x_i - x_j||$$

Let  $\Pi_{\mathfrak{L}}: \mathbb{R}^m \to \mathfrak{L}$  be the orthogonal projection of  $\mathbb{R}^m$  vector into subspace  $\mathfrak{L}$ . For  $x_i, x_j \in X$ , we let x be the normalized unit vector of  $x_i - x_j$ , and we need to prove that

$$(1 - \phi) \cdot M \|x\| \le \|\Pi_{\mathfrak{L}}(x)\| \le (1 + \phi) \cdot M \|x\|$$

holds with high probability, where M is the median of the of the function  $f = \sqrt{x_1^2 + \dots + x_m^2}$ . Following definition 4, this shows that the mapping  $\Pi_{\mathfrak{L}}$  is a D-embedding of X into  $\mathbb{R}^k$  with  $D = \frac{1+\phi}{1-\phi}$ . We let  $\phi = \frac{\varepsilon}{3}$  so that  $D = \frac{1+\varepsilon/3}{1-\varepsilon/3} \le 1+\varepsilon$ . Since ||x|| = 1, it is equivalent to showing that the following inequality holds with high probability

$$|\|\Pi_{\mathfrak{L}}(x)\| - M| < \frac{\varepsilon}{3}M\tag{1}$$

Lemma 3 describes the case when we have a random unit vector and project it onto a fixed subspace. It is actually identical to fixing a vector and projecting it onto a random subspace (we will describe how this random subspace is generated in the next subsection). We use Lemma 3 and plug in  $t = \frac{\varepsilon}{2}M$ ; the probability inequality (1) does not hold is bounded by

$$Pr\left[|\|\Pi_{\mathfrak{L}}(x)\| - M| \ge \frac{\varepsilon}{3}M\right] \le 4e^{-t^2m/2}$$

$$= 4e^{-\varepsilon^2M^2m/18}$$

$$\le 4e^{-\varepsilon^2k/72}$$

$$\le 1/m^2$$

Line 4 holds since  $k = O(\varepsilon^{-2} \log n)$  (for further details, please see [1]). Line 3 holds since  $M = \Omega(\sqrt{\frac{k}{m}})$ based on the following reasoning: We have that

$$1 = \mathbb{E}[\|X\|^2] = \sum \mathbb{E}[x_i^2],$$

which implies that  $\mathbb{E}[x_i^2] = \frac{1}{m}$ . Consequently,

$$\frac{k}{m} = \mathbb{E}[f^2] \le \Pr[f \le M + t](M + t)^2 + \Pr[f > M + t] \max(f^2) \le (M + t)^2 + 2e^{-t^2m/2}$$

where we used the fact that  $f^2 = \sum_{i=1}^k x_i^2$ . Taking  $t = \Theta(\sqrt{\frac{k}{m}})$ , we have that  $M = \Omega(\sqrt{\frac{k}{m}})$ .

#### 1.4 Random Subspace

Here we describe how a random subspace is generated. We first provide a quick review about Gaussians, a multivariate Gaussian has PDF:

$$p_x(x_1, x_2, \dots, x_N) = \frac{1}{(2\pi)^{N/2} |\Sigma|^{1/2}} \exp(-\frac{1}{2} (x - \mu)^T \Sigma^{-1} (x - \mu))$$

where  $\Sigma$  is a nonsingular covariance matrix and vector  $\mu$  is the mean of x.

Gaussians have several nice properties. The following operations on Gaussian variables also yield Gaussian variables:

- Project onto a lower dimensional subspace.
- Restrict to a lower dimensional subspace, i.e. conditional probability.
- Any linear operations.

In addition, we can generate a vector with multi-dimensional Gaussian distribution by picking *each* coordinate according to a 1-dimensional Gaussian distribution.

How do we generate a random vector from a sphere? The idea here is to pick a point from a multidimensional Gaussian distribution (generate each coordinate with mean = 0 and variance = 1, N(0,1)) so most n-dimensional vectors have norm  $\sqrt{n}$ . As the shape of an independent Gaussian distribution's PDF is *symmetric*, this procedure does indeed generate a point randomly and uniformly from a sphere (after normalizing it). Generating a random vector from a uniform distribution does not work, since it is *not* sampling uniformly from a sphere after normalization.

How do we get a random projection? This is no more than sampling  $n \times k$  times from a N(0,1) gaussian distributions. Each k samples are grouped to form a k-dimensional vector, so we have n total vectors:  $v_1, v_2, \dots v_n$ . We can simply orthonormalize these vectors, denoted as  $\hat{v}_i$ , and form the random subspace  $\mathfrak{L}$ :

$$\left(\begin{array}{cccc}
\vdots & \vdots & & \vdots \\
\hat{v}_1 & \hat{v}_2 & \cdots & \hat{v}_n \\
\vdots & \vdots & & \vdots
\end{array}\right)$$

#### 1.5 Applications of Johnson-Lindenstrauss Theorem

The Johnson-Lindenstrauss Theorem is very useful in several application areas, since it can approximately solve many problems. Here we illustrate some of them:

- Proximity Problems: This is an immediate application of the J-L Theorem. This is the case when we get a set of points in a high dimensional space  $\mathbb{R}^d$  and we want to compute any property defined in terms of distance between points. Using the J-L theorem, we can actually solve the problem in a lower dimensional space (up to a distortion factor). Example problems here include closest pair, furthest pair, minimum spanning tree, minimum cost matching, and various clustering problems.
- On-line Problems: The problems of this type involve answering queries in a high dimensional space. This is usually done through partitioning a high dimensional space according to some error (distance) measure. However, this operation tends to be exponentially dependent on the dimension of the space, e.g.,  $\left(\frac{1}{\varepsilon}\right)^d$  (referred to as the "curse of dimensionality"). Projecting points of higher dimensional space into lower dimensional space significantly helps with these types of problems.
- Data Stream/Storage Problem: We obtain data in a stream but we cannot store it all due to some storage space restriction. One way of dealing with it is to maintain a count for each data entry and then see how the counts are distributed. The idea is to provide "sketches" of such data based on the J-L Theorem. For further details, please refer to Piotr Indyk's course and his survey paper.

In summary, applications that are related to dimensionality reduction are very likely to be a good platform for the J-L Theorem.

# 2 Dvoretsky's Theorem

Dvoretsky's Theorem, proved by Aryeh Dvoretsky in his article "A Theorem on Convex Bodies and Applications to Banach Spaces" in 1959, tries to answer the following question:

- Let C be an origin-symmetric convex body in  $\mathbb{R}^n$ .
- $S \subseteq \mathbb{R}^n$  be a vector subspace.
- We would like to know: does  $Y = C \cap S$  look like a sphere? Furthermore, for how high a dimension (we denote it as k) does there exist an S for which this occurs?

A formal statement of Y's similarity to a sphere can be characterized by whether Y has a small Banach-Mazur distance to the sphere, i.e. if there exists a linear transformation such that

$$\mathbb{S}^{k-1}(1) \le Y \le \mathbb{S}^{k-1}(1+\varepsilon)$$

where  $\mathbb{S}^{k-1}(r)$  is denoted as a sphere with radius r.

It turns out that k varies with different types of convex bodies: for a ellipsoid k = n, for a cross-polytope  $k = \Theta(n)$ , and for a cube is  $k = \log(n)$ . It turns out that the cube case is the worst case scenario. Here is a formal statement of Dvoretsky's Theorem:

**Theorem 6 (Dvoretsky)** There is a positive constant c > 0 such that, for all  $\varepsilon$  and n, every n-dimensional origin-symmetric convex body has a section within distance  $1 + \varepsilon$  of the unit ball of dimension

$$k \geq \frac{c\varepsilon^2}{\log(1+\varepsilon^{-1})}\log n$$

Instead of providing the whole proof, we give a sketch of the proof here:

- 1. When we are given an origin-symmetric convex body, denoted as C, it defines some norm with respect to the convex body:  $C \to \|\cdot\|_C$ .
- 2. We need a subspace S to be spherical. It is basically saying that when we take any vector  $\theta$  on S, then  $\|\theta\|_C$  is approximately *constant*.
- 3. This is similar to concentration of measures which we have shown before. It basically says that when we have a function defined as a norm  $f: \theta \to \|\theta\|_C$ , it is precisely concentrated for every  $\theta$  on the sphere (i.e. every  $\|\theta\|_C$  is close to median).
- 4. This is similar to Johnson-Lindenstrauss except that we need *every* vector in k-dimensional subspace satisfying point 2 (In the J-L theorem, we prove that *most* of the vectors (points) are close to a fixed constant, i.e. median).
- 5. What we do is to put a fine "mesh" on the k-dimensional subspace and show that every point on the grid is right. The number of points we need to check is approximately  $O((\frac{4}{\delta})^k)$  where  $\delta$  is the error. We can see that it is exponentially dependent on k and it looks similar to the dependency of k in the J-L theorem. For further details of the proof, please see [2].

#### References

- 1. Sariel Har-Peled, "Geometric Approximation Algorithms", http://valis.cs.uiuc.edu/~sariel/teach/notes/aprx
- 2. Arych Dvoretzky, "Some results on convex bodies and Banach spaces", Proceedings of the National Academy of Sciences, 1959.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 18.409 An Algorithmist's Toolkit | 2009-11-12              |
|----------------------------------|-------------------------|
| Lecture 18                       |                         |
| Lecturer: Ionathan Kelner        | Scribe: Colin Jia Zhena |

## 1 Lattice

**Definition.** (Lattice) Given n linearly independent vectors  $b_1, \dots, b_n \in \mathbb{R}^m$ , the *lattice* generated by them is defined as  $L(b_1, b_2, \dots b_n) = \{\sum x_i b_i | x_i \in \mathbb{Z}\}$ . We refer to  $b_1, \dots, b_n$  as a *basis* of the lattice. Equivalently, if we define B as the  $m \times n$  matrix whose columns are  $b_1, \dots, b_n$ , then the lattice generated by B is  $L(B) = L(b_1, b_2, \dots, b_n) = \{Bx | x \in \mathbb{Z}^n\}$ . We say that the *rank* of the lattice is n and its *dimension* is m. If n = m, the lattice is called a *full-rank* lattice.

It is easy to see that, L is a lattice if and only if L is a discrete subgroup of  $(\mathbb{R}^n, +)$ .

Remark. We will mostly consider full-rank lattices, as the more general case is not substantially different.

**Example.** The lattice generated by  $(1,0)^T$  and  $(0,1)^T$  is  $\mathbb{Z}^2$ , the lattice of all integers points (see Figure 1(a)). This basis is not unique: for example,  $(1,1)^T$  and  $(2,1)^T$  also generate  $\mathbb{Z}^2$  (see Figure 1 (b)). Yet another basis of  $\mathbb{Z}^2$  is given by  $(2005,1)^T$ ;  $(2006,1)^T$ . On the other hand,  $(1,1)^T$ ,  $(2,0)^T$  is not a basis of  $\mathbb{Z}^2$ : instead, it generates the lattice of all integer points whose coordinates sum to an even number (see Figure 1 (c)). All the examples so far were of full-rank lattices. An example of a lattice that is not full is  $L((2,1)^T)$  (see Figure 1(d)). It is of dimension 2 and of rank 1. Finally, the lattice  $\mathbb{Z} = L((1))$  is a one-dimensional full-rank lattice.

**Figure 1**: Lattices of  $\mathbb{R}^2$ 

Image courtesy of Oded Regev. Used with permission.

**Definition.** For matrix B,  $P(B) = \{Bx | x \in [0,1)^n\}$  is the fundamental parallelepiped of B.

Examples of fundamental parallelepipeds are the gray areas in Figure 1. For a full rank lattice L(B), P(B) tiles  $\mathbb{R}^n$  in the pattern L(B), in the sense that  $\mathbb{R}^n = \{P(B) + x : x \in L(B)\}$ ; see Figure 2.

Figure 2: P(B) tiles  $\mathbb{R}^n$ 

Image courtesy of Oded Regev. Used with permission.

In Figure 1, we saw that not every set of n linearly independent vectors B in a rank n full-rank lattice  $\Lambda$  is a basis of  $\Lambda$ . The fundamental parallelepiped characterizes exactly when B is a basis:

**Lemma.** Let  $\Lambda$  be a rank n full-rank lattice and B an invertible  $n \times n$  matrix. Then B is a basis (of  $\Lambda$ ) if and only if  $P(B) \cap \Lambda = \{0\}$ .

*Proof.* " $\Rightarrow$ " is obvious:  $\Lambda$  only contains elements with integer coordinates under B, and 0 is the only element of P(B) with integer coordinates.

For " $\Leftarrow$ ", need to show that any lattice point x = By satisfies  $y_i \in \mathbb{Z}$ . Note that By' with  $y_i' = y_i - \lfloor y_i \rfloor$  is a lattice point in P(B). By our assumption By' = 0, ie  $y_i \in \mathbb{Z}$ .

It is natural to ask when are two invertible matices A, B equivalent bases, ie bases of the same lattice. It turns out that this happens if and only if A, B are related by a unimodular matrix.

**Definition.** A square matrix U is unimodular if all entries are integer and  $det(U) = \pm 1$ .

**Lemma.** U is unimodular iff  $U^{-1}$  is unimodular.

*Proof.* Suppose U is unimodular. Clearly  $U^{-1}$  has  $\pm 1$  determinant. To see that  $U^{-1}$  has integer entries, note that they are simply signed minors of U divided by det(U).

**Lemma.** Nonsingular matrices  $B_1, B_2$  are equivalent bases if and only if  $B_2 = B_1U$  for some unimodular matrix U.

*Proof.* " $\Rightarrow$ ": Since each column of  $B_1$  has integer coordinates under  $B_2$ ,  $B_1 = B_2U$  for some integer matrix U. Similarly  $B_2 = B_1V$  for some integer matrix V. Hence  $B_1 = B_1VU$ , ie VU = I. Since V, U are both integer matrices, this means that  $det(U) = \pm 1$ , as required.

" $\Leftarrow$ ": Note that each column of  $B_2$  is contained in  $L(B_1)$  and vice versa.

**Corollary.** Nonsingular matrices  $B_1$ ,  $B_2$  are equivalent if and only if one can be obtained from the other by the following operations on columns:

- 1.  $b_i \leftrightarrow b_i + kb_i$  for some  $k \in \mathbb{Z}$
- 2.  $b_i \leftrightarrow b_i$
- 3.  $b_i \leftarrow -b_i$

Now that it is clear that bases of a lattice have the same absolute determinant, we can proceed to define the determinant of lattice:

**Definition.** (Determinant of lattice) Let L = L(B) be a lattice of rank n. We define the determinant of L, denoted det(L), as the n-dimensional volume of P(B), ie  $det(L) = \sqrt{det(B^TB)}$ . In particular if L is a full rank lattice, det(L) = |det(B)|.

## 1.1 Dual lattices

**Definition.** The dual  $\Lambda^*$  of lattice  $\Lambda$  is  $\{x \in \mathbb{R}^n : \forall v \in \Lambda, x \cdot v \in \mathbb{Z}\}.$ 

Equivalently, the dual can be viewed as the set of linear functionals from  $\Lambda$  to  $\mathbb{Z}$ .

Figure 3: Dual lattice

Image courtesy of Oded Regev. Used with permission.

**Definition.** For matrix B, its the dual basis  $B^*$  is the unique basis that satisfies

1. 
$$span(B) = span(B^*)$$

2. 
$$B^T B^* = I$$

Fact.  $(L(B))^* = L(B^*)$ .

Fact.  $(\Lambda^*)^* = \Lambda$ .

Fact.  $det(\Lambda^*) = \frac{1}{det(\Lambda)}$ .

## 2 Shortest vectors and successive minima

One basic parameter of a lattice is the length of the shortest nonzero vector in the lattice, denoted  $\lambda_1$ . How about the second shortest? We are not interested in the second/third/etc shortest vectors which happen to be simply scaler multiples of the shortest vector. Instead, one requires that the next "minimum" increases the dimension of the space spanned:

**Definition.** The *i*th successive minimum of lattice  $\Lambda$ ,  $\lambda_i(\Lambda)$ , is defined to be  $\inf\{r | \dim(span(\Lambda \cap \bar{B}(0,r)) \geq i\}$ .

Figure 4:  $\lambda_1(\Lambda)=1,\ \lambda_2\Lambda=2.3$  Image courtesy of Oded Regev. Used with permission.

The following theorem, due to Blichfield, has various important consequences, and in particular can be used to bound  $\lambda_1$ .

**Theorem.** (Blichfield) For any full-rank lattice  $\Lambda$  and (measurable) set  $S \subseteq \mathbb{R}^n$  with  $vol(S) > det(\Lambda)$ , there exist distinct  $z_1, z_2 \in S$  such that  $z_1 - z_2 \in \Lambda$ .

Proof. Let B be a basis of  $\Lambda$ . Define x+P(B) to be  $\{x+y:y\in P(B)\}$  and  $S_x$  to be  $=S\cap(x+P(B))$  (see Figure 5). Since  $S=\bigcup_{x\in\Lambda}S_x$  we conclude that  $vol(S)=\sum_{x\in\Lambda}vol(S_x)$ . Let  $\hat{S}_x$  denote  $\{z-x:z\in S_x\}$ . Then  $vol(\hat{S}_x)=vol(S_x)$ , ie  $\sum_{x\in\Lambda}vol(\hat{S}_x)=vol(S)>vol(P(B))$ . Therefore, there must exist nondisjoint  $\hat{S}_x$  and  $\hat{S}_y$  for  $x\neq y$ . Consider any nonzero  $z\in \hat{S}_x\cap \hat{S}_y$ , then  $z+x,z+y\in S$  and  $x-y=(z+x)-(z+y)\in\Lambda$ , as required.

**Figure 5**: Blichfield's theorem Image courtesy of Oded Regev. Used with permission.

As a corollary of Blichfield's theorem, we obtain the following theorem due to Minkowski, which says that any large enough centrally-symmetric convex set contains a nonzero lattice point. A set S is centrally-symmetric if it is closed under negation. It is easy to see that the theorem is false if we drop either of the central-symmetry or the convexity requirement.

**Theorem.** (Minkowski) Let  $\Lambda$  be a full-rank lattice of rank n. Any centrally-symmetric convex set S with  $vol(S) > 2^n det(\Lambda)$  contains a nonzero lattice point.

| MIT C   | penCourseWare |
|---------|---------------|
| http:// | ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 18.409 | $\mathbf{A}\mathbf{n}$ | Algo | orith | mist's | Toolkit |
|--------|------------------------|------|-------|--------|---------|
|--------|------------------------|------|-------|--------|---------|

11/17/2009

# Lecture 19

Lecturer: Jonathan Kelner Scribe: Steven Sam

# 1 Review of last lecture

Recall that  $L \subset \mathbf{R}^n$  is a *lattice* if L is a discrete set and is closed under addition and negation. In this lecture, we assume that all lattices are *full-rank*, i.e., the vectors in the lattice span  $\mathbf{R}^n$ .

Given linearly independent  $b_1, \ldots, b_n \in \mathbf{R}^n$ , one can form a lattice

$$L(B) = L(b_1, \dots, b_n) = \{Bx \mid x \in \mathbf{Z}^n\},\$$

where B is the set of the  $b_i$ 's. We call the  $b_i$ 's (and also the set B) a basis for L(B). Recall that a lattice can have many different bases. As opposed to linear algebra over a field, change of bases for lattices is more rigid, since the integrality constraints must be preserved. Because of this, one cannot usually find an orthonormal basis, and instead one of the most fundamental problems becomes finding a nice basis, which consists of short and almost orthogonal vectors.

Recall that for a basis B of L, the fundamental parallelepiped is

$$P(B) = \{Bx \mid x \in [0,1)^n\}.$$

Furthermore, if L is full rank, then the determinant of L is defined as  $Vol(P(B)) = |\det(B)|$ , and this is independent of the choice of a basis. The determinant is inversely proportional to the density of a lattice.

We say that an  $n \times n$  matrix M is unimodular if all entries of M are integers, and  $|\det(M)| = 1$ . Last time we saw that a matrix U is unimodular if and only if  $U^{-1}$  is unimodular. This implies that an inverse of a unimodular matrix has integer entries. Unimodular matrices are interesting for us, because two lattice bases  $B_1$  and  $B_2$  are equivalent if and only if  $B_1 = UB_2$ , for some unimodular matrix U. Moreover two bases are equivalent if and only if one can be obtained from the other by the following operations:

- $b_i \leftarrow b_i + k \cdot b_j$ , for  $i \neq j$  and  $k \in \mathbf{Z}$ ,
- swapping vectors:  $b_i \leftrightarrow b_j$ ,
- $b_i \leftarrow -b_i$ .

Last time, we proved the following theorem, which we will need for the proof of Minkowski's theorem.

**Theorem 1 (Blichfield)** For any full rank lattice L and measurable set  $S \subseteq \mathbf{R}^n$  with  $\operatorname{Vol}(S) > \det(L)$ , there exist distinct  $z_1, z_2 \in S$  such that  $z_1 - z_2 \in L$ .

## 2 Minkowski's theorem

**Theorem 2 (Minkowski's Theorem)** If L is a full rank lattice, and S any centrally-symmetric convex set of volume greater than  $2^n \cdot \det(L)$ , then K contains a nonzero point of L.

**Proof** Consider the set  $\hat{S} = \frac{1}{2}S$ . Then  $\operatorname{Vol}(\hat{S}) = 2^{-n}\operatorname{Vol}(S) > \det(L)$  by assumption. So we can apply Blichfield's theorem to conclude that there exist distinct points  $z_1, z_2 \in \hat{S}$  such that  $z_1 - z_2 \in L$ . In particular,  $2z_1, 2z_2 \in K$ . Since K is centrally-symmetric, we also have  $-2z_2 \in K$ . Hence the point  $z_1 - z_2 = \frac{1}{2}(2z_1 + (-2z_2))$  is in K since it is convex.

This theorem is very useful in many settings. For one, many nice number theory theorems follow from it. It also guarantees that the length  $\lambda_1(L)$  of the shortest vector in the lattice is not too big.

Corollary 3 For any full-rank lattice L,

$$\lambda_1(L) \leq \sqrt{n} \cdot (\det L)^{1/n}$$
.

**Proof** We first bound the volume of the ball B(0,r), for some radius r. This ball contains the hypercube  $\left[-\frac{r}{\sqrt{n}},\frac{r}{\sqrt{n}}\right]^n$ . Hence, its volume is greater than  $\left(\frac{2r}{\sqrt{n}}\right)^n$ . For  $r=\sqrt{n}\cdot\det(L)^{1/n}$ , the volume of B(0,r) is greater than  $2^n\cdot\det(L)$ , so the ball contains a nonzero

lattice vector, and therefore, the length of the shortest vector is at most  $\sqrt{n} \cdot \det(L)^{1/n}$ .

The above corollary easily generalizes to other minima. For instance, we will see in a problem set that

$$\left(\prod_{i=1}^n \lambda_i(L)\right)^{1/n} \le \sqrt{n} \cdot (\det L)^{1/n},$$

where  $\lambda_i(L)$  is the length of the *i*th shortest vector.

#### 3 Algorithmic questions

One could ask, for instance, if the bound given above for  $\lambda_1(L)$  is tight, and when it holds. Here we will focus on the algorithmic aspect of lattices. There are several interesting questions that one can ask for lattices. We assume that all lattices have integer coordinates. This is the same as giving them rational coordinates, since we can always multiply all coordinates of all vectors by the least common multiple of their denominators.

- Shortest Vector Problem (SVP): Find the shortest vector in L. Finding just the length of the shortest vector is equivalent.
- Closest Vector Problem (CVP): Find the vector in L closest to some given point p.

Both of the above problems are NP-hard, so one usually focuses on the approximate version of them: "Find a vector within  $\gamma$  of the optimum". Some similar questions, like "Does a vector of a given length exist?" turn out to be non-equivalent.

For the approximation versions of SVP and CVP, the gaps between the best known upper and lower bounds are very large. For instance, the best polynomial time algorithms for these problems get approximation factors which are essentially exponential in n. The best known factor is roughly  $2^{O(n \log \log n/\log n)}$ . The best exact algorithm runs in  $2^{O(n)}$  time. It turns out that one cannot find the vector guaranteed by Minkowski's Theorem. SVP is hard to approximate within any constant factor unless NP = RP. CVP is hard to approximate within  $n^{O(1/\log\log n)}$ . Approximation within the factor  $\sqrt{n}$  is in NP  $\cap$  co-NP.

#### Lattice basis reduction $\mathbf{4}$

We will show a polynomial time algorithm to approximately solve the SVP within a factor of  $2^{O(n)}$ . Because of an exponential error this might seem to be a very weak and useless result. Nevertheless, this algorithm is good enough to give extremely striking results both in theory and practice. For instance, it can be used to show that an integer program with a constant number of variables can be solved in polynomial time.

## Review of the Gram-Schmidt algorithm 4.1

Since our approach resembles the Gram-Schmidt algorithm, we first review this method for orthogonalizing a basis for inner product spaces.

We are given a basis  $b_1, \ldots, b_n$  for a vector space, and we want to construct an orthogonal basis  $b_1^{\star}, \ldots, b_n^{\star}$ such that  $\operatorname{span}(b_1,\ldots,b_k)=\operatorname{span}(b_1^*,\ldots,b_k^*)$ , for all  $k\in\{1,\ldots,k\}$ . In the Gram-Schmidt algorithm, the vectors  $b_i^{\star}$  are usually normalized, but we will not do it here.

The process works as follows:

- Let  $b_1^* := b_1$ .
- For k=2 to n:  $b_k^* := b_k [\text{projection of } b_k \text{ onto } \text{span}(b_1, \dots, b_{k-1})].$

The projection is computed in the following way:

projection of  $b_k$  onto span $(b_1, \ldots, b_{k-1})$  = projection of  $b_k$  onto span $(b_1^{\star}, \ldots, b_{k-1}^{\star})$ 

$$= \sum_{i=1}^{k-1} \text{projection of } b_k \text{ onto } b_i^{\star} = \sum_{i=1}^{k-1} \frac{b_k \cdot b_i^{\star}}{\|b_i^{\star}\|^2} b_i^{\star}$$

We set coefficients  $\mu_{ki}$  so that  $\mu_{kk} = 1$ , and

$$b_k = \sum_{i=1}^k \mu_{ki} b_i^{\star}.$$

Therefore, we can write the above as  $B = MB^*$ , where the basis vectors are rows of B and  $B^*$ , and

$$M = \begin{bmatrix} \mu_{11} & 0 & 0 & \cdots & 0 \\ \mu_{21} & \mu_{22} & 0 & \cdots & 0 \\ \vdots & \vdots & \vdots & \ddots & \vdots \\ \mu_{n1} & \mu_{n2} & \mu_{n3} & \cdots & \mu_{nn} \end{bmatrix} = \begin{bmatrix} 1 & 0 & 0 & \cdots & 0 \\ \mu_{21} & 1 & 0 & \cdots & 0 \\ \vdots & \vdots & \vdots & \ddots & \vdots \\ \mu_{n1} & \mu_{n2} & \mu_{n3} & \cdots & 1 \end{bmatrix}.$$

Note that det(M) = 1, so for lattices, we have  $Vol(B) = Vol(B^*)$ , but since entries of M are not necessarily integers,  $L(B) = L(B^*)$  does not have to hold. However,  $B^*$  can be used to bound the length  $\lambda_1(L(B))$  of the shortest vector in L(B).

**Lemma 4** For any nonzero  $b \in L(B)$ ,  $||b|| \ge \min_i ||b_i^{\star}||$ .

**Proof** Every nonzero  $b \in L(B)$  can be expressed as  $b = \sum_{i=1}^{k} \lambda_i b_i$ , where  $\lambda_k \neq 0$  and for each  $\lambda_i$  is an integer. We have

$$b = \sum_{i=1}^{k} \lambda_i b_i = \sum_{i=1}^{k} \lambda_i \sum_{j=1}^{i} \mu_{ij} b_j^* = \lambda_k b_k^* + \sum_{j=1}^{k-1} \sum_{i=1}^{k} \lambda_i \mu_{ij} b_j^*,$$

and therefore,

$$||b||^2 \ge ||\lambda_k b_k^{\star}|| \ge ||b_k^{\star}||^2$$
,

which finishes the proof.  $\blacksquare$ 

## 4.2 Gauss's Algorithm

We start by presenting an algorithm for solving the 2-dimensional SVP exactly.

We call a basis u, v for a 2-dimensional lattice reduced if  $||u|| \le ||v||$ , and  $2|u \cdot v| \le ||u||^2$ . One can show that the following claim holds.

**Proposition 5** A reduced basis for a 2-dimensional lattice contains the first two successive minima of L.

Sketch of Proof Rotate the plane, so that  $u=(u_1,0)$ , and  $v=(v_1,v_2)$ . We claim that the vector v is a vector with the smallest possible nonnegative second coordinate. The property  $2|u \cdot v| \leq ||u||^2$  implies that  $v_1 \in \left[-\frac{u_1}{2}, \frac{u_1}{2}\right]$ , which in turn implies that v is the shortest vector whose second coordinate is  $v_2$ . Because  $|v_2| \geq \sqrt{3}/2|u|$ , every vector whose second coordinate is greater than  $|v_2|$  (that is, at least  $2|v_2|$ ) has length at least  $\sqrt{3}|u|$  and cannot be shorter than v. Therefore, v is the shortest vector. Also, since  $|v_2| \geq \sqrt{3}/2|v|$ ,

one can show that every vector with second coordinate greater than  $|v_2|$  has length at least  $\sqrt{3}|v|$ . This implies that v is the shortest vector not generated by u.

A formal description of Gauss's algorithm follows.

While  $\{u, v\}$ , where  $||u|| \le ||v||$ , is not reduced:

- Set v := v mu, where  $m \in \mathbf{Z}$  is chosen to minimize the length of v mu.
- If  $||u|| \le ||v||$ , break.
- If  $||v|| \le ||u||$ , then swap u and v, and repeat.

In the second step, if  $||u|| \le ||v||$  even after the reduction, the basis cannot be further reduced and one can prove that  $2|u \cdot v| \le ||u||^2$ .

The algorithm is like a 2-dimensional discrete version of Gram–Schmidt, and is similar to the Euclidean GCD algorithm. Can we make it run in polynomial time? It turns out that it actually does run in polynomial time, but the proof of this fact is not obvious, and therefore, we do not present it here. Instead of this, we replace the termination criterion with

If 
$$(1 - \varepsilon)||u|| \le ||v||$$
, break.

It is easy to prove that the modified algorithm gives an  $(1-\varepsilon)$  approximate answer. Now in each reduction, we decrease the length of one of the vectors by at least a constant factor. Therefore the modified algorithm runs in weakly polynomial  $O(\log(\|u\| + \|v\|)/\varepsilon)$  time.

The proof that Gauss's algorithm runs in polynomial time uses the fact that for a sufficiently small  $\varepsilon$ , after the modified algorithm stops, only one more reduction suffices to get a reduced basis.

### 4.3 Reduced bases

We want to extend the notion of reduced bases to higher dimensions. In order to find a short vector in the lattice, we would like to perform a discrete version of the Gram–Schmidt. So we need to formalize the notion of being orthogonal in lattice problems. One way to do this is to say that the result of our procedure is "almost orthogonalized" so that doing Gram–Schmidt does not change much. In this section, we use the notation from Section 4.1.

**Definition 6 (Reduced bases)** Let  $\{b_1, \ldots, b_n\}$  be a basis for a lattice L and let M be its Gram-Schmidt matrix defined above. Then  $\{b_1, \ldots, b_n\}$  is a reduced basis if it meets the following two conditions:

- 1. All the non-diagonal entries of M satisfy  $|\mu_{ik}| \leq 1/2$ .
- 2. For each i,  $\|\pi_{S_i}b_i\|^2 \leq \frac{4}{3}\|\pi_{S_i}b_{i+1}\|^2$ , where  $S_i$  is the subspace orthogonal to  $\operatorname{span}(b_1,\ldots,b_{i-1})$ .

**Remark** The constant 4/3 here is somewhat arbitrary. In fact, any number strictly between 1 and 4 will do.

**Remark** Condition 2 is equivalent to  $||b_{i+1}^{\star} + \mu_{i+1,i}b_i^{\star}||^2 \ge \frac{3}{4}||b_i^{\star}||^2$  and one may think it as requiring that the projections of any two successive basis vectors  $b_i$  and  $b_{i+1}$  onto  $S_i$  satisfy a gapped norm ordering condition, analogous to what we did in Gauss's algorithm for 2-dimensional case.

| MIT C   | penCourseWare |
|---------|---------------|
| http:// | ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 20

Lecturer: Jonathan Kelner

## 1 Brief Review of Gram-Schmidt and Gauss's Algorithm

Our main task of this lecture is to show a polynomial time algorithm which approximately solves the Shortest Vector Problem (SVP) within a factor of  $2^{O(n)}$  for lattices of dimension n. It may seem that such an algorithm with exponential error bound is either obvious or useless. However, the algorithm of Lenstra, Lenstra and Lovász (LLL) is widely regarded as one of the most beautiful algorithms and is strong enough to give some extremely striking results in both theory and practice.

Recall that given a basis  $b_1, \ldots, b_n$  for a vector space (no lattices here yet), we can use the Gram-Schmidt process to construct an orthogonal basis  $b_1^*, \ldots, b_n^*$  such that  $b_1^* = b_1$  and  $b_k^* = b_k - [\text{projection of } b_k \text{ onto span}(b_1, \ldots, b_{k-1})]$  for all  $2 \le k \le n$  (note that we do not normalize  $b_k^*$ ). In particular, we have that for all k:

- $\operatorname{span}(b_1, \dots, b_k) = \operatorname{span}(b_1^*, \dots, b_k^*),$
- $b_k = \sum_{i=1}^k \mu_{ki} b_i^*$ , and
- $\mu_{kk} = 1$ .

The above conditions can be rewritten as  $B = MB^*$ , where basis vectors are rows of B and  $B^*$ , and

$$M = \begin{bmatrix} \mu_{11} & 0 & 0 & \dots & 0 \\ \mu_{21} & \mu_{22} & 0 & \dots & 0 \\ \vdots & & \ddots & & \\ \mu_{n1} & \mu_{n2} & \mu_{n3} & \dots & \mu_{nn} \end{bmatrix} = \begin{bmatrix} 1 & 0 & 0 & \dots & 0 \\ \mu_{21} & 1 & 0 & \dots & 0 \\ \vdots & & \ddots & & \\ \mu_{n1} & \mu_{n2} & \mu_{n3} & \dots & 1 \end{bmatrix}.$$

Obviously det(M) = 1, and thus  $vol(B) = vol(B^*)$ . However, the entries of M are not integers, and thus  $L(B) \neq L(B^*)$ . We have proved last time that

for any 
$$b \in L$$
,  $||b|| \ge \min_i \{ ||b_i^*|| \}$ .

We'll use this to prove useful bound for the shortest vector on lattice.

Recall also that last time we saw the Gauss's algorithm which solves SVP for d = 2. There are two key ingredients of the algorithm. The first is a definition of "reduced basis" which characterizes the discrete version of bases being orthogonal: namely,

a basis 
$$\{u,v\}$$
 for a 2-d lattices is said to be *reduced*, if  $|u| \leq |v|$  and  $|u \cdot v| \leq \frac{|u|^2}{2}$ .

The second is an efficient procedure that produces a reduced basis. The procedure consists of two stages: First is a Euclid-like process which subtracts a multiple of the shorter vector from the longer one to get a vector as short as possible. The second stage is, if the length ordering is broken, we swap the two vectors and repeat, otherwise (i.e.,  $|u| \leq |v|$ ) the procedure ends. To make the above procedure obviously terminate in polynomial time, we change the termination criterion to be  $(1 - \epsilon)|u| \leq |v|$ . This only gives us a  $(1 - \epsilon)$ -approximation, but is good enough. The basic idea of LLL algorithm is to generalize Gauss's algorithm to higher dimensions.

## 2 LLL Algorithm

#### 2.1 Reduced Basis

In order to find a short vector in the lattice, we would like to perform a discrete version of GS procedure. To this end, we need to formalize the notion of being orthogonal in lattice problems. One way to do this is to say that the result of our procedure is "almost orthogonalized" so that doing Gram-Schmidt does not change much.

**Definition 1 (Reduced Basis)** Let  $\{b_1, \ldots, b_n\}$  be a basis for a lattice L and let M be its GS matrix defined in Section 1.  $\{b_1, \ldots, b_n\}$  is a reduced basis if it meets the following two conditions:

- Condition 1: all the non-diagonal entries of M satisfy  $|\mu_{ik}| \leq 1/2$ .
- Condition 2: for each i,  $||\pi_{S_i}b_i||^2 \leq \frac{4}{3}||\pi_{S_i}b_{i+1}||^2$ , where  $S_i$  is the orthogonal complement of (i.e., the subspace orthogonal to)  $span(b_1,\ldots,b_{i-1})$ , and  $\pi_{S_i}$  is the projection operator to  $S_i$ .

**Remark** The constant 4/3 here is to guarantee polynomial-time termination of the algorithm, but the choice of the exact value is somewhat arbitrary. In fact, any number in (1, 4) will do.

**Remark** Condition 2 is equivalent to  $||b_{i+1}^* + \mu_{i+1,i}b_i^*||^2 \ge \frac{3}{4}||b_i^*||^2$  and one may think it as requiring that the projections of any two successive basis vectors  $b_i$  and  $b_{i+1}$  onto  $S_i$  satisfy a gapped norm ordering condition, analogous to what we did in Gauss's algorithm for 2D case.

#### 2.2 The algorithm

Given  $\{b_1, \ldots, b_n\}$ , the LLL algorithm works as below.

```
Repeat the following two steps until we have a reduced basis
```

## 3 Analysis of LLL Algorithm

The LLL algorithm looks pretty intuitive, but it is not obvious at all that it converges in polynomial number of steps or gives a good answer to SVP. We'll see that it indeed works.

#### 3.1 LLL produces a short vector

We first show that reduced basis gives a short vector.

Claim 2 If  $b_1, \ldots, b_n$  is a reduced basis, then  $||b_1|| \leq 2^{\frac{n-1}{2}} \lambda_1(L)$ .

**Proof** Note that

$$\begin{aligned} ||b_{i}^{*}||^{2} &= ||\pi_{S_{i}}b_{i}||^{2} \leq \frac{4}{3}||\pi_{S_{i}}b_{i+1}||^{2} \\ &= \frac{4}{3}||b_{i+1}^{*} + \mu_{i+1,i}b_{i}^{*}||^{2} = \frac{4}{3}||b_{i+1}^{*}||^{2} + \frac{4}{3}\mu_{i+1,i}^{2}||b_{i}^{*}||^{2} \\ &\leq \frac{4}{3}||b_{i+1}^{*}||^{2} + \frac{1}{3}||b_{i}^{*}||^{2}, \end{aligned}$$

which gives  $||b_{i+1}^*||^2 \ge \frac{1}{2}||b_i^*||^2$ . By induction on i, we have

$$||b_i^*||^2 \ge \frac{1}{2^{i-1}}||b_1^*||^2 = \frac{1}{2^{i-1}}||b_1||^2.$$

Recall that  $\forall b \in L$ ,  $||b|| \ge \min_i ||b_i^*||$ . Therefore  $\lambda_1(L) \ge \min_i ||b_i^*||$ , which combined with the inequality above yields

$$||b_1||^2 \le \min_i \{2^{i-1}||b_i^*||^2\} \le 2^{n-1} \min_i \{||b_i^*||^2\} \le 2^{n-1} \lambda_1(L)^2$$

as desired.

## 3.2 Convergence of LLL

Now we show that the LLL algorithm terminates in polynomial time. Note that in each iteration of LLL, Step 1 takes polynomial time and Step 2 takes O(1) times. What we need to show is that we only need to repeat Step 1 and Step 2 a polynomial number of times. To this end, we define a potential function as follows:

$$D(b_1, \dots, b_n) = \prod_{i=1}^n ||b_i^*||^{n-i}.$$

It is clear that Step 1 does not change D since we do not change the Gram-Schmidt basis.

We are going to show that each iteration of Step 2 decreases D by a constant factor. In Step 2, we swap i and i+1 only when  $||b_i^*||^2 > 4/3||\pi_{S_i}b_{i+1}||^2 \ge 4/3||b_{i+1}^*||^2$ . Therefore each swapping decreases D by a factor of at least  $2/\sqrt{3}$ , as desired.

It is left to show that D can be upper- and lower-bounded. Since  $||b_i^*|| \le ||b_i||$ , the initial value of D can be upper bounded by  $(\max_i ||b_i||)^{n(n-1)/2}$ . On the other hand, we may rewrite D as  $\prod_{i=1}^n |\det(\Lambda_i)|$ , where  $\Lambda_i$  is the lattice spanned by  $b_1, \ldots, b_i$ . Since we assume that the lattice basis vectors are integer-valued, so D is at least 1.

In sum, the algorithm must terminate in  $\log_{2/\sqrt{3}}(\max_i ||b_i||)^{n(n-1)/2} = \text{poly}(n)$  iterations.

# 4 Application of LLL-Lenstra's Algorithm for Integer Program-ming

## 4.1 Applications of LLL

LLL algorithm has many important applications in various fields of computer science. Here are a few (many taken from Regev's notes):

1. Solve integer programming in bounded dimension as we are going to see next.

- 2. Factor polynomials over the integers or rationals. Note that this problem is harder than the same task but over reals, e.g. it needs to distinguish  $x^2 1$  from  $x^2 2$ .
- 3. Given an approximation of an algebraic number, find its minimal polynomial. For example, given 0.645751 outputs  $x^2 + 4x 3$ .
- 4. Find integer relations among a set of numbers. A set of real numbers  $\{x_1, \ldots, x_n\}$  is said to have an integer relation if there exists a set of integers  $\{a_1, \ldots, a_n\}$  not identically zero such that  $a_1x_1 + \cdots + a_nx_n = 0$ . As an example, if we are given  $\arctan(1)$ ,  $\arctan(1/5)$  and  $\arctan(1/239)$ , we should output  $\arctan(1) 4\arctan(1/5) + \arctan(1/239) = 0$ . How would you find this just given these numbers as decimals?
- 5. Approximate to SVP, CVP and some other lattice problems.
- Break a whole bunch of cryptosystems. For example, RSA with low public exponent and many knapsack based cryptographic systems.
- 7. Build real life algorithms for some NP-hard problems, e.g. subset sum problem.

### 4.2 Integer Programming in Bounded Dimension

#### 4.2.1 Linear, Convex and Integer Programming

Consider the following feasibility version of the linear programming problem:

• Linear Programming (feasibility)

Given: An  $m \times n$  matrix A and a vector  $b \in \mathbb{R}^n$ 

**Goal:** Find a point  $x \in \mathbb{R}^n$  s.t.  $Ax \leq b$ , or determine (with a certificate) that none exists

One can show that other versions, such as the optimization version, are equivalent to feasibility version. If we relax the searching regions from polytopes to convex bodies, we get convex programming.

• Convex Programming (feasibility)

**Given:** A separation oracle for a convex body K and a promise that

- K is contained in a ball of singly exponential radius R
- if K is non-empty, it contains a ball of radius r which is at least 1/(singly exponential)

**Goal:** Find a point  $x \in \mathbb{R}^n$  that belongs to K, or determine (with a certificate) that none exists

Integer programming is the same thing as above, except that we require the program to produce a point in  $\mathbb{Z}^n$ , not just  $\mathbb{R}^n$ . Although linear programming and convex programming are known to be in  $\mathbf{P}$ , integer programming is a well-known NP-complete problem.

#### 4.2.2 Lenstra's algorithm

**Theorem 3 (Lenstra)** If our polytope/convex body is in  $\mathbb{R}^n$  for any constant n, then there exists a polynomial time algorithm for integer programming.

#### Remark.

- For linear programming (LP), the running time of the algorithm will grow exponentially in n, but polynomially in m (the number of constrains) and the number of bits in the inputs.
- For convex programming, the running time is polynomial in  $\log(R/r)$ .
- As before, we could also ask for maximum of  $c \cdot x$  over all  $x \in K \cap Z^n$ , which is equivalent to the feasibility problem, as we can do a binary search on the whole range of  $c \cdot x$ .

The main idea of Lenstra's algorithm is the following. The main difficulty of integer programming comes from the fact that K may not be well-rounded, therefore it could be exponentially large but still contain no integral point, as illustrated in the following figure:

Figure by MIT OpenCourseWare.

Figure 1: A not-well-rounded convex body

Our first step is thus to change the basis so that K is well-rounded, i.e., K contains a ball of radius 1 and is contained in a ball of radius c(n) for some function that depends only on n. Such a transformation will sends  $\mathbb{Z}^n$  to some lattice L. Now our convex body is well-rounded but the basis of lattice L may be ill-conditioned, as shown in the following figure:

Figure by MIT OpenCourseWare.

Figure 2: A well-rounded convex body and an ill-conditioned lattice basis

It turns out that the lattice points are still well-separated and we can remedy the lattice basis by a basis reduction procedure of LLL (i.e., discrete Gram-Schmidt). Finally we chop the lattice space up in some intelligent way and search for lattice points in K.

Note that in the first step of Lenstra's algorithm, what we need is an algorithmic version of Fritz John's theorem. As we saw in the problem set, there is an efficient algorithm which, for any convex body K specified by a separation oracle, constructs an ellipsoid E such that

$$E(P') \subseteq K \subseteq O(n^{3/2})E(P')$$
.

Next let  $T: \mathbb{R}^n \to \mathbb{R}^n$  be the linear transformation such that E(P') is transformed to  $\mathbf{B}(P,1)$ . Now K is sandwiched between two reasonably-sized balls:

$$\mathbf{B}(P,1) \subseteq TK \subseteq \mathbf{B}(P,R),$$

where  $R = O(n^{3/2})$  is the radius of the outer ball.

Let  $L = T\mathbb{Z}^n$  with basis  $Te_1, \ldots, Te_n$ . Our goal is to find a point (if it exists) in  $TK \cap T\mathbb{Z}^n = TK \cap L$ . Our next step is to apply the basis reduction in LLL algorithm. We will need the following two lemmas in analyzing Lenstra's algorithm. The proofs of the lemmas are left as exercises.

**Lemma 4** Let  $b_1, \ldots, b_n$  be any basis for L with  $||b_1||^2 \le \cdots \le ||b_n||^2$ . Then for every  $x \in \mathbb{R}^n$ , there exists a lattice point y such that

$$||x - y||^2 \le \frac{1}{4}(||b_1||^2 + \dots + ||b_n||^2)$$
  
  $\le \frac{1}{4}n||b_n||^2.$ 

**Lemma 5** For a reduced basis  $b_1, \ldots, b_n$  ordered as above,

$$\prod_{i=1}^{n} ||b_i|| \le 2^{n(n-1)/4} \det(L).$$

Consequently, if we let  $H = span(b_1, \ldots, b_{n-1})$ , then

$$2^{-n(n-1)/4}||b_n|| \le dist(H, b_n) \le ||b_n||.$$

Let  $b_1, \ldots, b_n$  be a reduced basis for L. Applying Lemma 4 gives us a point  $y \in L$  such that  $||y - P|| \le \frac{1}{2} \sqrt{n} ||b_n||$ .

- case 1:  $y \in TK$ . We find a point in  $TK \cap L$ .
- case 2:  $y \notin TK$ , hence  $y \notin \mathbf{B}(P,1)$ . Consequently,  $||y-P|| \ge 1$  and  $||b_n|| \ge \frac{2}{\sqrt{n}}$ .

This means that the length of  $b_n$  is not much smaller than R. In the following we partition L along the sublattice "orthogonal" to  $b_n$  and then apply this process recursively.

Let L' be the lattice spanned by  $b_1, \ldots, b_{n-1}$  and let  $\mathcal{L}_i = L' + ib_n$  for each  $i \in \mathbb{Z}$ . Clearly  $L = \bigcup_{i \in \mathbb{Z}} \mathcal{L}_i$ . From Lemma 5 the distance between two adjacent hyperplanes is at least

$$\operatorname{dist}(b_n, \operatorname{span}(b_1, \dots, b_{n-1})) \ge 2^{-n(n-1)/4} ||b_n||$$

$$\ge \frac{2}{\sqrt{n}} 2^{-n(n-1)/4} ||b_n|| = c_1(n),$$

where  $c_1(n)$  is some function that depends only on n. This implies that the convex body TK can not intersect with too many hyperplanes. That is

$$|\{i \in \mathbb{Z} : \mathcal{L}_i \cap \mathbf{B}(P,R) \neq \emptyset\}| \leq 2R/c_1(n) = c_2(n)$$

for some function  $c_2(n)$  that depends only on n. Now we have reduced our original searching problem in n-dimensional space to  $c_2(n)$  instances of searching problems in (n-1)-dimensional space. Therefore we can apply this process recursively and the total running time will be a polynomial in the input size times a function that depends only on n.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 18.409 An Algorithmist's Toolkit | November 21, 2009 |
|----------------------------------|-------------------|
| Lecture 21                       |                   |
| Lecturer: Jonathan Kelner        | Scribe: Van Zhana |

# 1 Solving Linear Systems: A Brief Overview

Given an invertible  $n \times n$  matrix A and an n-vector b, we would like to solve the matrix equation Ax = b. One way to do so is to invert A and multiply both sides by  $A^{-1}$ . While this approach is theoretically valid, there are several problems with it in practice. Computing the inverse of a large matrix is expensive and susceptible to numerical error due to the finite precision of floating-point numbers. Moreover, matrices which occur in real problems tend to be sparse and one would hope to take advantage of such structure to reduce work, but matrix inversion destroys sparsity.

So what would a numerical analyst do? A better method is Gaussian elimination, or equivalently, LU factorization followed by back-substitution. This technique is competitive when the matrix A is dense and unstructured, and it also has the advantage of allowing solution of Ax = b for multiple values of b with little additional work. However, it still fails to make use of the fact that systems encountered in practice are rarely dense and unstructured. As we will see in the next few lectures, iterative methods are the technique of choice for solving such systems.

# 2 A First Iterative Method

# 2.1 An Example

Consider the system

$$\left(\begin{array}{ccc} 100 & 3 & -2 \\ 1 & 200 & 5 \\ -4 & 3 & 100 \end{array}\right) x = \left(\begin{array}{c} 800 \\ 1000 \\ 500 \end{array}\right).$$

While computing the exact solution by hand would be a tedious task, it is a simple matter to find an approximate solution. Roughly speaking, we expect the behavior of our system to be governed by the "large" diagonal entries of the matrix A, so if we just pretend that all off-diagonal entries are zero, the solution we obtain should still be reasonably close to the correct answer. Of course, once we ignore the off-diagonal entries, solving the system is easy, and we get as a first approximation  $x_1 = (8, 5, 5)^T$ .

How close does our approximation come to solving the system? Multiply A by  $x_1$  to get  $(805, 1033, 483)^T$ . Subtracting from the desired result b, we find that we are off by  $e_1 = (-5, -33, 17)^T$ . Now this suggests a way to improve our estimate: since our system is linear, we can adjust our approximation  $x_1$  by applying the same technique as before with  $e_1$  on the right rather than b. Adding this adjustment gives an improved approximation  $x_2 = (7.95, 4.835, 5.17)^T$ , and clearly we can iterate the procedure as many times as we wish in hopes of obtaining better and better estimates converging to the true solution. It turns out that in this example one more iteration already achieves accuracy of about four significant figures: our next approximation is  $(7.9584, 4.8310, 5.1730)^T$ , while the actual answer is  $(7.9585, 4.8309, 5.1734)^T$  to four decimals. In fact, convergence is exponential: the number of correct digits increases linearly with the number of iterations.

## 2.2 A Bit Harder

One might argue that the above example was contrived, since our approximation scheme depended on the fact that the diagonal entries of A were much larger than the off-diagonal entries. However, consider the

system

$$\left(\begin{array}{ccc} 100 & -1 & -4 \\ 100 & 100 & 3 \\ 100 & 100 & 100 \end{array}\right) x = \left(\begin{array}{c} 100 \\ 200 \\ 300 \end{array}\right).$$

Again, while computing the exact answer would take some work, we can tell at a glance that the solution should be close to  $(1,1,1)^T$ . In this case, the above-diagonal entries are all small, and once we ignore these, we can easily solve the remaining lower-triangular system. As before, we may now iteratively improve our solution by finding the error and repeating the procedure, converging geometrically to the correct answer.

## 2.3 General Idea

Why do both of these matrices work? One was "almost diagonal" while the other was "almost lower-triangular." This suggests that the important common attribute of the matrices A is the existence of a decomposition

$$A = L + S$$
,

where L is "large"—accounting for "most of A"—and easy to invert, while S is "small." We reason that  $L^{-1}$  would thereby be a good approximation of  $A^{-1}$ . Therefore, we define

$$x_1 = L^{-1}b,$$

$$r_1 = b - Ax_1.$$

We can perform iterative updates according to

$$x_{k+1} = x_k + L^{-1}r_k, (1)$$

$$r_{k+1} = b - Ax_{k+1}. (2)$$

In the k-th stage,  $x_k$  is our current approximate solution to Ax = b and  $r_k$  is called the residual.

Note that this iterative approach never requires us to invert A: instead, we need only know how to multiply vectors by  $L^{-1}$ . Aside from this, only the (inexpensive) operations of matrix-vector multiplication and vector arithmetic are required. Thus, if we know an efficient way of computing  $L^{-1}y$  given a vector y—or alternatively, are given a "black box" that performs this operation—then we may infer a method for approximately solving Ax = b which may be much faster than the standard techniques for computing the exact solution.

#### 2.4 Analysis

Of course, for this method to be useful, we need to know that our iterations do actually improve our estimate. We would also like a bound on the improvement at each stage so that we know when to stop. To obtain these results, we need to make precise the notions of L and S being "large" and "small."

Consider the product

$$L^{-1}A = L^{-1}(L+S) = I + L^{-1}S.$$

This gives us some intuition that  $L^{-1}$  should be a good approximation of  $A^{-1}$  when  $L^{-1}S$  is "small" compared to the identity matrix I. Proceeding with the analysis, let x denote the actual solution to Ax = b. Substituting A = L + S, we get Lx = -Sx + b, or equivalently,

$$x = -L^{-1}Sx + L^{-1}b.$$

Define  $M = -L^{-1}S$  and  $z = L^{-1}b$  and observe that we can rewrite our iterative step as the recurrence

$$x_{k+1} = x_k + L^{-1}r_k$$

$$= x_k + L^{-1}(b - Ax_k)$$

$$= x_k + L^{-1}b - L^{-1}Lx_k - L^{-1}Sx_k$$

$$= Mx_k + z.$$

Note that x is a fixed point of this recurrence because it leaves zero residual: r = b - Ax = 0 by definition of x. In other words, x = Mx + z.

Now define the *error* at step k to be  $e_k = x_k - x$  and observe

$$\begin{array}{rcl} e_{k+1} & = & x_{k+1} - x \\ & = & Mx_k + z - x \\ & = & M(x + e_k) + z - x \\ & = & (Mx + z - x) + Me_k \\ & = & Me_k. \end{array}$$

It follows immediately that  $e_k = M^{k-1}e_1$ , and in fact

$$e_k = -M^k x$$
.

since we could have started our iteration at  $x_0 = 0$  in which case  $e_0 = -x$ . Thus, we can think of the error growing roughly as a matrix power<sup>1</sup>. We pause here to make a definition.

**Definition 1** The spectral radius  $\rho$  of a symmetric matrix M is the absolute value of its largest eigenvalue:

$$\rho = |\lambda_{\text{max}}|.$$

Observe that it follows from the definition that (in the symmetric case)

$$||M^n x|| \le \rho^n ||x||,$$

so if  $\rho < 1$ , then powers of M converge exponentially to zero at a rate given by  $\rho$ . The same holds for general M if we replace "eigenvalue" by "singular value." Summarizing, we have the following result.

**Theorem 2** Suppose A is a square matrix admitting a decomposition A = L + S where L is invertible and the largest singular value of  $L^{-1}S$  has absolute value  $\rho < 1$ . Then the iteration given by (1), (2) for solving Ax = b converges to the correct answer as  $\rho^k$ .

#### 2.5 Further Remarks

As a side note, the two specific examples we began with are cases of *Jacobi iteration*, in which the matrix A is decomposed as D+S with D diagonal and S small; and *Gauss-Seidel iteration*, where A=L+S with L lower triangular and S small.

Also, one may wonder why we want to work specifically with matrices that look like these. One good explanation is that in physics, many "natural" matrices tend to have larger diagonal values, since we are considering the transition matrix of a physical state near equilibrium.

# 3 Setup for More Iterative Methods

## 3.1 Assumptions

For the remainder of this lecture, we will restrict our attention to solving Ax = b for  $n \times n$  square matrices A that are symmetric and positive definite. Note that positive definiteness implies nonsingularity. These conditions may at first glance appear to be very restrictive, but in fact we claim we can reduce any nondegenerate square linear system to such a problem. Indeed, we need only observe that for an invertible matrix A,

$$Ax = b$$
 iff  $A^T Ax = A^T b$ .

<sup>&</sup>lt;sup>1</sup>This is similar to our analysis of stablization in random walks!

and the matrix  $A^TA$  is positive definite.

It is worth noting that while it is clear that the above reduction is theoretically valid, it is less clear whether or not such a reduction is practical. While the matrix product  $A^TA$  has the advantage of positive definiteness, it raises several other concerns. For one, matrix multiplication could be as expensive as solving the system in the first place and could destroy sparsity properties. Additionally, one might worry about the effects of replacing A with  $A^TA$  on convergence speed and condition number. As we shall see, however, the trick to getting around these issues is to never actually compute  $A^TA$ . Instead, since our algorithms will only use this matrix in the context of multiplying by a vector, we can perform such multiplications from right to left via two matrix-vector multiplications, thus avoiding the much more expensive matrix-matrix multiplication.

# 3.2 Converting a Linear Problem to a Quadratic One

Having assumed now that we are dealing with a symmetric positive definite matrix A, we can recast our linear system Ax = b as the condition that the vector x minimizes the quadratic form

$$f(x) = \frac{1}{2}x^T Ax - bx + c.$$

Indeed, the gradient of f is given by

$$\nabla f(x) = \frac{1}{2}(A + A^T)x - b = Ax - b$$

because A is symmetric, and since A is positive definite, the quadratic form f is strictly convex, hence has a unique minimizer x given by  $\nabla f(x) = 0$ . In this case, level (contour) sets of f(x) are ellipsoids with axes along the eigenvectors of A and axis lengths inversely proportional to the eigenvalues of A.

What happens if our assumptions on A are violated? If A is nonsymmetric, vanishing of the gradient is no longer equivalent to the condition Ax = b: instead, we get  $\frac{1}{2}(A + A^T)x = b$ . If A is negative definite,  $\nabla f(x) = 0$  gives a maximum rather than a minimum, and if A is symmetric but neither positive nor negative definite, then vanishing of the gradient generally gives a saddle point. For more geometric intuition and figures (some of which are reproduced in the lecture slides), we refer to [1].

# 4 Steepest Descent

## 4.1 Motivation

We now discuss the technique of steepest descent, also known as gradient descent, which is a general iterative method for finding local minima of a function f. The idea is that given a current estimate  $x_i$ , the gradient  $\nabla f(x_i)$ —or more precisely, its negative—gives the direction in which f is decreasing most rapidly. Hence, one would expect that taking a step in this direction should bring us closer to the minimum we seek. Keeping with our previous notation, we will let x denote the actual minimizer,  $x_i$  denote our i-th estimate, and

$$e_i = x_i - x, (3)$$

$$r_i = b - Ax_i = -Ae_i \tag{4}$$

denote the *i*-th error term and residual, respectively.

The question now is how to decide what step size to use at each iteration. A logical approach is to choose the step  $\alpha_i$  such that the updated estimate  $x_{i+1} = x_i - \alpha_i \nabla f(x_i)$  minimizes  $f(x_{i+1})$  among all such  $x_{i+1}$ . In general, the solution to this *line search* may or may not have a closed form, but in our case of f a quadratic form, we can determine the minimizing  $\alpha_i$  explicitly. Indeed, we need only notice that at the minimum along a line, the gradient is orthogonal to the line. Now the negative gradient at the i+1-st step

$$-\nabla f(x_{i+1}) = b - Ax_{i+1} = r_{i+1}$$

turns out just to equal the i + 1-st residual, so our orthogonality relation reduces to the condition that successive residuals be orthogonal:

$$r_{i+1}^T r_i = 0.$$

Expanding out

$$r_{i+1} = b - Ax_{i+1}$$

$$= b - A(x_i + \alpha_i r_i)$$

$$= r_i - \alpha_i Ar_i$$

and substituting into the previous equation gives (using  $A = A^T$ )

$$\alpha r_i^T A r_i = \alpha (A r_i)^T r_i = r_i^T r_i,$$

and thus we have a formula for computing the step size along  $r_i$  in terms of just  $r_i$  itself.

**Remark** It is important to remember that the residuals  $r_i = b - Ax_i$  measure the difference between our objective b and the result  $Ax_i$  of our approximation in "range space," whereas the errors  $e_i = x_i - x$  measure the difference between our approximation and the true solution in "domain space." Thus, the previous orthogonality relation that holds for residual vectors does not mean that successive error vectors in the domain are orthogonal. It does, however, imply that successive differences between consecutive approximations are orthogonal because these differences  $x_{i+1} - x_i = \alpha_i r_i$  are proportional to the residuals.

# 4.2 Algorithm

To summarize the development thus far, we have obtained an iterative algorithm for steepest descent with the following update step:

$$r_i = b - Ax_i \tag{5}$$

$$\alpha_i = \frac{r_i^T r_i}{r_i^T A r_i} \tag{6}$$

$$x_{i+1} = x_i + \alpha_i r_i. (7)$$

As an implementation note, we point out that the runtime of this algorithm is dominated by the two matrix-vector multiplications:  $Ax_i$  (used to compute  $r_i$ ) and  $Ar_i$  (used in finding the step size  $\alpha_i$ ). In fact, it is enough to do just the latter multiplication because as we saw before, we can alternatively write

$$r_{i+1} = r_i - \alpha_i A r_i,$$

so that after the first step we can find residuals by reusing the computation  $Ar_i$ , which was already done in the previous step. In practice, one needs to be careful about accumulation of roundoff errors, but this problem may be resolved by using (5) every once in a while to recalibrate.

#### 4.3 Analysis

Before dealing with general bounds on the rate of convergence of steepest descent, we make the preliminary observation that in certain special cases, steepest descent converges to the exact solution in just one step. More precisely, we make the following claim.

**Claim 3** If the current error vector  $e_i$  is an eigenvector of A, then the subsequent descent step moves directly to the correct answer. That is,  $e_{i+1} = 0$ .

**Proof** Apply (5)–(7) and the definition of the error (3) to find

$$e_{i+1} = e_i + \frac{r_i^T r_i}{r_i^T A r_i} r_i, (8)$$

giving the change in the error from step i to step i+1. In the case that  $e_i$  is an eigenvector of A, say with eigenvalue  $\lambda$ , we have from (4) that  $r_i = -Ae_i = -\lambda e_i$ , and hence (8) reduces to

$$e_{i+1} = e_i + \frac{1}{\lambda}(-\lambda e_i) = 0.$$

**Remark** The above result tells us that steepest descent works instantly for error vectors in the eigenspaces of A. These spaces have dimensions equal to the multiplicities of the corresponding eigenvalues, and in particular, if A is a multiple of the identity, then steepest descent converges immediately from any starting point. In general, we are not nearly so lucky and the eigenspaces each have dimension 1, but it is worth noting that even in this case convergence is qualitatively different from that of our first iterative approach: there are particular directions along which steepest descent works perfectly, whereas our first approach only gave the correct answer in the trivial case in which the error was already zero.

In light of the preceding remark, we can expect that convergence should be faster along some directions than others, and we will see that this is indeed the case. Before jumping headlong into the convergence analysis, however, it is worthwhile to define a more convenient measure of error.

**Definition 4** The energy norm of a vector e is given by

$$||e||_A = e^T A e. (9)$$

Motivation for this definition will be provided in the next lecture; for now, we simply take for granted that it obeys the usual properties of a norm—and hence produces the same qualitative notion of convergence—but lends itself to a cleaner convergence bounds. We will satisfy ourselves with simply stating the result and focus on discussing its consequences, since the proof is just a computation using (8) and (9). A more intuitive line of reasoning will also come in the next lecture.

**Theorem 5** Let  $e_i$  denote the error vector at step i of steepest descent. Let  $\{v_j\}_{j=1}^n$  be a normalized eigenbasis of A with corresponding eigenvalues  $\lambda_j$ , and let  $e_i = \sum_j \xi_j v_j$  denote the expansion of  $e_i$  with respect to this eigenbasis. Then

$$||e_{i+1}||_A^2 = ||e_i||_A^2 \left( 1 - \frac{(\sum_j \xi_j^2 \lambda_j^2)^2}{(\sum_j \xi_j^2 \lambda_j^3)(\sum_j \xi_j^2 \lambda_j)} \right). \tag{10}$$

The general result (10) is quite a mouthful, but fortunately we can understand its flavor just by looking at the two-dimensional case. In this case we have only two eigenvectors  $v_1$  and  $v_2$ . Assume  $\lambda_1 > \lambda_2$ , so the condition number of A is  $\kappa = \lambda_1/\lambda_2$ . Define  $\mu = \xi_1/\xi_2$  to be the ratio of the components of  $e_i$  along the basis vectors. Then (10) simplifies to

$$\frac{||e_{i+1}||_A^2}{||e_i||_A^2} = 1 - \frac{(\kappa^2 + \mu^2)^2}{(\kappa + \mu^2)(\kappa^3 + \mu^2)}.$$

Note that the form of the expression on the right corroborates our preliminary observations. If the condition number  $\kappa = 1$ , convergence occurs instantly, and if  $\kappa$  is close to 1, convergence occurs quickly for all values of  $\mu$ . If  $\kappa$  is large, convergence still occurs instantly if  $\mu = 0$  or  $\infty$ , but now the rate of convergence varies substantially with  $\mu$ , with the worst case being when  $e_i$  is closer to the smaller eigenvector than the larger one by a factor of  $\kappa$ , i.e.,  $\mu = \pm \kappa$  (see the lecture slides or [1] for helpful pictures).

#### 4.4 Some Motivation

To summarize, we have seen that the performance of steepest descent varies depending on the error direction and can sometimes be excellent; however, in the worst case (obtained by maximizing the factor on the right side of (10) over all  $\xi_j$ ) convergence is still only geometric.

The problem, as can be seen in the lecture figures, is that steepest descent has the potential to "zig-zag too much." We will see in the next lecture how the method of *conjugate gradients* overcomes this issue. The big idea here is that the so-called "zig-zagging" comes from situations when the ellipsoidal curves are very skew; the disparity between the magnitudes of the axes of the ellipses causes us to take very tiny steps. Note we can then think of the energy norm is really a normalization of the ellipses into spheres, which removes this issue.

# References

[1] Shewchuk, Jonathan. "An Introduction to the Conjugate Gradient Method Without the Agonizing Pain." August 1994. http://www.cs.cmu.edu/~jrs/jrspapers.html.

| MIT C   | penCourseWare |
|---------|---------------|
| http:// | ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Lecture 22

Lecturer: Jonathan Kelner

### 1 Last time

Last time, we reduced solving sparse systems of linear equations Ax = b where A is symmetric and positive definite to minimizing the quadratic form  $f(x) = \frac{1}{2}x^T Ax - bx + c$ .

The idea of steepest descent is to pick a point, find the direction of steepest decrease, step along that direction, and iterate until we get close to a zero. The appropriate directions turn out to be the residuals. We pick the step length to take us to the minimal f value along the line.

Each iteration requires only two matrix-vector multiplications. We can push this down to one by calculating the residuals as

$$r_{i+1} = b - Ax_{i+1}$$

$$= b - A(x_i + \alpha_i r_i)$$

$$= (b - Ax_i) - \alpha_i Ar_i$$

$$= r_i - \alpha_i Ar_i$$

This can allow floating point error to accumulate, though that can be fixed by occasionally calculating the residual using the original formula.

Today we'll talk about how to bound the error, and later how to get better performance.

# 2 Convergence Analysis of Steepest Descent

We study a very similar method that doesn't do the line search – it uses the same step length  $\alpha$  at every iteration. Asymptotically, the best possible  $\alpha$  and usual steepest descent have the same behavior.

Steepest descent doesn't depend on the basis at all, so we might as well pick the eigenbasis for analysis. The size of the error at each step certainly won't change if we switch bases, and it will be easier to see what's going on. For further cleanliness everything will be stated for 2x2 matrices – everything generalizes.

If we were trying to solve

$$\left(\begin{array}{cc} \lambda_1 & 0 \\ 0 & \lambda_2 \end{array}\right) \left(\begin{array}{c} x_1 \\ x_2 \end{array}\right) = \left(\begin{array}{c} b_1 \\ b_2 \end{array}\right)$$

the exact solution would be  $x_i = \frac{1}{\lambda_i}b$ . Keep in mind that we're working in the eigenbasis to do the analysis, but the actual algorithm does not get to work in the basis, since finding the eigenbasis is as hard as inverting the matrx.

First, let's see what happens if we use  $\alpha = 1$ . Obviously this is not general, for example if the  $\lambda$ s are greater than 2, but the algebra is enlightening.

Let's start with  $x_0 = 0$ , so the first residual  $r_0 = b$ , and for i > 0 the residual will be

$$r_i = r_{i-1} - Ar_{i-1}$$
$$= (1 - A)r_{i-1}$$
$$= (1 - A)^i b$$

where the last step follows from induction. Since  $x_i = x_{i-1} + r_i = \sum_{k=0}^{i} r_k$ , we can now write

$$x_k = \left[ \sum_{i=0}^{k-1} (1-A)^i \right] b$$

But the sum  $\sum_{i=0}^{k-1} (1-A)^i$  is just the first k terms of the taylor series 1/y around 1 – that is,  $x_k$  estimates  $\frac{1}{\lambda_i}b$  using Taylor series! For  $\alpha \neq 1$  the computation is similar,

$$x_k = \left[\sum_{i=0}^{k-1} \alpha (1 - \alpha A)^i\right] b$$

and we get another Taylor series approximation: 1/y around  $1/\alpha$ .

So how well can we choose  $\alpha$ ? We want the residuals to go to zero quickly. If we had  $1 \times 1$  matrices, we could just set  $\alpha = \frac{1}{\lambda}$  and get residual 0 in one step, but in general we need to choose  $\alpha$  which works for different eigenvalues simultaneously.

Taylor series only converge well very near where you expand it; this gives some intuition for why the condition number should be related to the distance between  $\lambda_{\text{max}}$  and  $\lambda_{\text{min}}$ . If these eigenvalues are far apart, then there is no  $\alpha$  that works for all the eigenvalues.

We can bound the  $L_2$  norm of the residual by bounding  $b_i$  by  $||b||_2$  and taking the max of the multipliers

$$||r_k||_2 \le \max_i |1 - \alpha \lambda_i|^k ||b||_2$$

So, we want to minimize

$$\max_{i} |1 - \alpha \lambda_{i}|$$

Since the maximum will occur at either the largest or the smallest eigenvalue, the best we can do is to balance them and have  $(1 - \alpha \lambda_{\min}) = -(1 - \alpha \lambda_{\min})$ . This gives that the best  $\alpha$  is the reciprocal of the midrange of the eigenvalues:

$$\alpha = \left(\frac{\lambda_{\min} + \lambda_{\max}}{2}\right)^{-1}$$

The resulting  $\max_i |1 - \alpha \lambda_i|$  is  $1 - \frac{2}{\kappa + 1}$  where  $\kappa = \lambda_{\max}/\lambda_{\min}$ , which we call the *condition number* of A. Note that  $\kappa$  is a ratio of eigenvalues, so it's unchanged by scaling the matrix.

From the bound for the  $L_2$  norm, we can derive that the number of iterations grows linearly in  $\kappa$ . Now can we do better?

#### 3 Conjugate Directions

Currently we are going to the minimal of f value along our search direction. As we saw in previous example, this can us to take a long zigzag path. What we would really like to do is go the length of the projection of x onto our search direction. If we could do that, then after i steps the error would be orthogonal to all previous search directions, and we'd be done with an  $n \times n$  matrix after n iterations.

Suppose we have orthogonal directions  $d_0, \ldots, d_{n-1}$  – the standard basis will do.

We have  $x_{i+1} = x + i\alpha_i d_i$ . We want  $e_{i+1} \perp d_i$ .

$$d_i^T e_{i+1} = d_i^T (e_i + \alpha_i d_i) = 0$$

which implies

$$\alpha_i = -\frac{d_i^T e_i}{d_i^T d_i}$$

The good news is we can compute everything except the  $e_i$ . The bad news is computing  $e_i$  is equivalent to finding x. Fortunately, a mild modification will make the calculation possible.

So far we've been talking about orthogonality relative to the standard inner product. There's no real reason to do this, and in fact it will be more convenient to work with the inner product  $||x||_A^2 = x^T A x$ , instead of  $x^T I x$  as we have been. Geometrically, this unwarps the isolines of the quadratic form into perfect circles

We can think of this as a change of basis:  $x' = A^{1/2}x$ , though not for computation – pretty much the only way to get the square root of A would be to retrieve the eigenvalues, which would defeat the purpose.

Suppose we have A-orthogonal search directions  $(d_i)$  – now the unit basis won't do, but suppose for the moment we have magically acquired search directions.

Again,  $x_{i+1} = x_i + \alpha_i d_i$ . We want  $e_{i+1} \perp_A d_i$ .

$$d_i^T A e_{i+1} = d_i^T A (e_i + \alpha d_i) = 0$$

which implies

$$\alpha_i = -\frac{d_i^T A e_i}{d_i^T A d_i}$$

But  $Ae_i$  is just  $r_i$ , which we do know how to compute. Yay.

# 4 Conjugate Gram-Schmidt

Conjugate directions is insufficient for our purposes because we might not have time to do n iterations. We'll settle for a crude answer, but we need it very fast.

Also, as mentioned before, we don't have search directions. You may recall the Gram-Schmidt process for orthogonalizing a set of vectors from a previous class. Does it work for A-orthogonality? Certainly; see page 5 of slides on Conjugate Gram-Schmidt.

The problem is that Conjugate Gram-Schmidt is still too slow. The crucial change we made to the algorithm is requiring each direction to be orthogonal to *all* previous search directions. While this gave us good convergence, it means we have to subtract off the projection into each of the previous directions, which means that we have to remember what the previous directions were. This incurs both time and space cost. We need a more sophisticated way to find the directions.

# 5 Conjugate Gradients

The trick is to choose the linearly independent vectors we feed to Gram-Schmidt very carefully. We will generate these vectors on the go. Define  $D_i = \text{span}(d_0, \ldots, d_{i-1})$ .

The property that we leverage is that after i steps, Conjugate Directions finds a point in  $x_0 + D_i$  – in fact, the one that minimizes the size of the error  $||e_i||_A = (e_i^T A e_i)^{1/2}$ .

Let the input to Gram-Schmidt be  $(u_i)$ , and define  $U_i$  analogously to  $D_i$ . By construction,  $x_i \in x_0 + D_i = x_0 + U_i$ , and  $e_i$  will be A-orthogonal to  $D_i = U_i$ .

We choose the magic inputs  $u_i = r_i$ . Since  $r_{i+1} = -Ae_{i+1}$ , by definition  $r_{i+1}$  is plain old orthogonal to  $D_{i+1}$  (and  $D_i, D_{i-1}, \ldots$ ). Also,  $r_{i+1} = r_i - \alpha_i Ad_i$ , so  $D_{i+1} = D_i \cup AD_i$ . Putting the two together,  $r_{i+1}$  is A-orthogonal to  $D_i$ .

Thus,  $r_{i+1}$  only A-projects onto the  $d_i$  component of  $D_{i+1}$ . There's only one thing to subtract off, so only one or two A-dot products are needed per iteration again, as in steepest descent. We no longer need to remember all the previous search directions, just the very last one, so we've fixed the space complexity as well.

The algorithm is given on a slide on page 6.

# 6 Convergence Analysis of Conjugate Gradients

After i iterations, the error is

$$e_i = \left(I + \sum_{j=1}^i \psi_j A^j\right) e_0$$

where the  $\psi$ 's are some mess of  $\alpha$ 's and  $\beta$ 's. Thus we can think of conjugate gradients at the *i*th step as finding these best possible coefficients for an *i*th degree polynomial  $P_i(\lambda)$  to make the A-norm of the error small.

$$||e_i||_A^2 \le \min_{P_i} \max_{\lambda \in \Lambda(A)} [P_i(\lambda)]^2 ||e_0||_A^2$$

Any sequence of *i*-degree polynomials which are 1 at 0 will give bounds on the error; we want ones which are small for every eigenvalue  $\lambda \in \Lambda(A)$ . This should remind you of the analysis of steepest descent, but Taylor Series are not the right choice here – they're designed to work around a point, while we want polynomials which will work at every eigenvalue. We can modify the magic polynomials from lecture 6 to work here. Recall that Chebyshev polynomials have the property of being 1 at 1, and small for some [0, l] where l < 1 is a parameter. We want polynomials which are 1 at 0 and small in  $[\lambda_{\min}, \lambda_{\max}]$ . This allows us to bound the error (measured in the *A*-inner product) at the *i*th iteration as

$$||e_i||_A \le 2\left(1 - \frac{2}{\sqrt{k} + 1}\right)^i ||e_0||_A$$

so the number iterations grows with the square root of  $\kappa$ , which is way better than the linear performance of steepest descent.

Note that the algorithm isn't actually computing any Chebyshev polynomials – it uses the best polynomial, which is at least as good. Also, notice that if we knew the range of the eigenvalues to begin with, we could skip to designing a polynomial to estimate  $A^{-1}$ . Conjugate gradients magically finds the best polynomial without explicitly knowing these values.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### 18.409 An Algorithmist's Toolkit

December 3, 2009

Lecture 23

Lecturer: Jonathan Kelner

### 1 Outline

Last lecture discussed the conjugate gradient algorithm for solving linear systems Ax = b. This lecture will discuss *preconditioning*, a method for speeding up the conjugate gradient algorithm for specific matrices.

# 2 Last Lecture

Last lecture we described the conjugate gradient algorithm for solving linear systems Ax = b for positive definite matrices A. The time bound for conjugate gradient depends on fitting low-degree polynomials to be small on the eigenvalues of A and large at 0. Using Chebyshev polynomials, this gives a running time of  $\tilde{O}(\kappa^{1/2})$ , where  $\kappa = \frac{\lambda_{\text{max}}}{\lambda}$  is the *condition number* of A.

 $\tilde{O}(\kappa^{1/2})$ , where  $\kappa = \frac{\lambda_{\max}}{\lambda_{\min}}$  is the condition number of A.

For certain matrices A, tighter bounds can be achieved. For example, if the eigenvalues of A tend to be clustered together, then polynomials can more easily be small at all the eigenvalues. But in the worst case and the general case, conjugate gradient takes  $\tilde{\Theta}(\kappa^{1/2})$  time. For ill-conditioned (or badly-conditioned, poorly-conditioned, etc.) matrices, this can be quite slow. What do we do then?

# 3 Preconditioning

### 3.1 Motivating example

Some matrices A with terrible condition number can still be solved fairly easily. For example, consider the matrix

$$A = \left(\begin{array}{ccc} 10000 & 777 & 123\\ 0.1 & 1 & 0.2\\ 0.002 & 0.001 & 0.01 \end{array}\right).$$

This has condition number  $\kappa \approx 1000000$ , and condition number  $10^{12}$  once you compute  $A^TA$  to get a positive definite matrix to perform conjugate gradient on. But if you normalize the diagonal to get

$$D^{-1}A = \left(\begin{array}{ccc} 1 & 0.0777 & 0.0123\\ 0.1 & 1 & 0.2\\ 0.2 & 0.1 & 1 \end{array}\right),$$

you find a well-conditioned matrix. So you can use conjugate gradient to quickly solve  $D^{-1}Ax = D^{-1}b$  instead. When we do this, we call D a "preconditioner" for A.

There's no reason that preconditioners have to be diagonal; they just have to be easily invertible. The next section discusses the general problem of finding preconditioners.

### 3.2 In general

The problem is that we want to solve Ax = b but A is ill-conditioned, so conjugate gradient doesn't work directly. However, we also know some other positive definite matrix M that approximates A and is easy to invert. Then we instead use conjugate gradient on  $M^{-1}Ax = M^{-1}b$ . If M approximates A, then  $M^{-1}A$  should have low condition number and conjugate gradient will be fast. This idea has few complications:

- How do we find M? There's no general answer to this question, since it's impossible for most A. However, most problems you want to solve have structure, which often allows you to find a good M. The second part of this lecture discusses how to find a good M when A is a Laplacian.
- It could hard to compute  $M^{-1}A$ . If M and A are sparse, you don't want to compute the dense matrix  $M^{-1}A$ . Fortunately, you don't need to. Conjugate gradient only computes vector products, which you can compute in succession.
- $M^{-1}A$  may not by symmetric or positive definite. You need it to be positive definite for conjugate gradient to be proven correct. Fortunately, this can be worked around, as shown below:

### 3.3 Dealing with $M^{-1}A$ being asymmetric

While  $M^{-1}A$  may not be symmetric, both M and A are. So we can factor  $M = EE^T$ . Then  $E^{-1}AE^{-T}$  has the same eigenvalues as  $M^{-1}A$ , since if  $M^{-1}Av = \lambda v$ , then

$$E^{-1}AE^{-T}(E^Tv) = E^TM^{-1}Av = \lambda E^Tv.$$

So rather than solving  $M^{-1}Ax = M^{-1}b$ , we can solve  $E^{-1}AE^{-T}\hat{x} = E^{-1}b$  and return  $x = E^{-T}\hat{x}$ . This can be done with conjugate gradient, since it uses a positive definite matrix.

Now, we might not know how to factor  $M = EE^T$ . Fortunately, if we look at how conjugate gradient works, it never actually requires this factorization. Every time E is used, it will come in the pair  $(aE^{-T})(E^{-1}b) = aM^{-1}b$ .

This completes our sketch of how preconditioning algorithms work, once you find a preconditioner. We will spend the rest of lecture on finding preconditioners for Laplacians.

# 4 Preconditioners on Laplacians

Recall from previous lectures that any graph G can be *sparsified*. This means that we can find a graph H with  $\tilde{O}(n)$  edges such that

$$(1 - \epsilon)L_h \leq L_G \leq (1 + \epsilon)L_h$$
.

Then  $L_h$  is a good preconditioner for  $L_G$ . This is because all the eigenvalues of  $L_H^{-1}L_G$  lie in  $[1 - \epsilon, 1 + \epsilon]$ , so  $L_H^{-1}L_G$  has constant condition number.

We can use this to solve Laplacian linear systems for all graphs as if they are sparse and only multiply the number of iterations by log factors. Each step of conjugate gradient requires solving a sparse linear system on H, and it only takes logarithmically many iterations to converge.

But to do this, we need to find H. Our previous method required a linear system solver to get H, so we can't use it. There is a way to get a slightly weaker spectral sparsifier in nearly linear time, though. We give a sketch of the algorithm, but don't go into much detail:

We know that random sampling does a good job of sparsifying expanders. The problem with random sampling is when cuts have very few edges crossing them. So we first break the graph into well-connected clusters with our fast local partitioning algorithm. Inside each cluster, we randomly sample. We then condense the clusters and recurse on the edges between clusters.

So in nearly linear time, we can get a graph with O(n) edges and a  $1 + \epsilon$  spectral approximation to G. But for use as a preconditioner, we don't need a  $1 + \epsilon$  approximation. We can relax the approximation ratio in order to dramatically cut the number of edges in the sparsifier. This will cause us to take more iterations of conjugate gradient, but be able to perform each iteration quickly. We dub these incredibly sparse matrices ultra-sparsifiers.

### 4.1 Ultra-Sparsification

What we cover now is a method to speed up conjugate gradient by using an even sparser H. All the methods discussed henceforth are easily applicable to solving Mx = b for any M that is weakly diagonally dominant (not just graph Laplacians), i.e. for all i it holds that  $|M_{i,i}| \geq \sum_{j \neq i} |M_{i,j}|$ . The H we will precondition with now we call ultra-sparsifiers as they will only have (1+o(1))n edges! You can think of H as essentially being a spanning tree of G with only a few extra edges.

**Theorem 1** Given a graph G with n vertices and m edges, it is possible to obtain a graph H with  $n + t \log^{O(1)} n$  edges such that  $L_H \leq L_G \leq (n/t)L_H$ , independent of m.

We will not prove Theorem 1 here. In the problem set you will show a weaker version where the (n/t) is replaced with  $(n/t^2)$ . Getting to (n/t) requires similar ideas but gets slightly more complicated.

The main benefit to ultra-sparsification is that for many algorithms, the ultra-sparse graph acts like a graph with many fewer vertices. The ultra-sparse graph is a tree with relatively few additional edges linking nodes of the tree. For intuition on this, note that paths without branching can usually be condensed into a single edge. Furthermore, linear systems on trees can be solved in linear time.

The result will be that we can solve diagonally dominant linear systems in nearly linear time. This lecture will focus on Laplacians, but the problem set has a question on how to extend it to general diagonally dominant systems.

#### 4.1.1 Embedding of graphs

Recall from problem set 1 that:

**Lemma 2** Let  $P_{u,v}$  be a path from u to v of length k, and let  $E_{u,v}$  be the graph that just has one edge from u to v. Then

$$E_{u,v} \prec kP_{u,v}$$

Now, suppose that we have two graphs G and H and an embedding of G onto H such that each edge in G maps to a path in H. For  $(i,j) \in G$ , define  $\operatorname{stretch}(i,j)$  to be the length of (i,j)'s embedded path in H. Then

$$G = \sum_{(i,j) \in E(G)} E_{i,j} \leq \sum_{(i,j) \in E(G)} \operatorname{stretch}(i,j) \operatorname{image}(i,j) \leq \sum_{(i,j) \in E(G)} \operatorname{stretch}(i,j) H.$$

If H is a subgraph of G, this means

$$H \leq G \leq \sum_{(i,j)\in E(G)} \operatorname{stretch}(i,j)H.$$

#### 4.1.2 Spanning tree preconditioners

For trees T, we can solve  $L_T x = b$  in linear time. So it would be really nice if H were a "low average-stretch spanning tree." We could then precondition on H and take O(m) time per iteration.

Turns out that that low average-stretch spanning trees exist and can be found efficiently:

**Theorem 3** Any graph G has a spanning tree T into which it can be embedded such that

$$\sum_{(i,j)\in E(G)} stretch(i,j) \le m \log^c n.$$

This already is strong enough to give a non-trivial result. If we use such a spanning tree as a preconditioner, we take O(m) per iteration and take  $\tilde{O}(m^{1/2}$  iterations (because the condition number is  $\tilde{O}(m)$ ), for  $\tilde{O}(m^{3/2})$  time.

Although we won't go into detail, it turns out that this exact algorithm actually runs in  $O(m^{4/3})$  time. The eigenvalues of the tree have a structure such that error is halved in  $\tilde{O}(m^{1/3})$  iterations, not just  $\tilde{O}(m^{1/2})$  iterations as Chebyshev polynomials show.

Instead, we'll add a few more edges to make "Vaidya's augmented spanning trees", which will improve the condition number substantially. In the problem set, you'll go into more detail into this, and into how to apply this recursively to get nearly linear recovery time.

#### 4.1.3 Constructing ultra-sparsifiers

We will take a spanner T of G, and add a small number s more edges to get H. We partition T into t subtrees of balances path lengths. We then add one well-chosen "bridge" edge between every pair of subtrees. This can be done so that

$$\kappa(L_H^{-1/2}L_GL_H^{-1/2}) \le O(n/t).$$

The ultra-sparsifier H will have n-1+s edges, for  $s \leq {t \choose 2}$  in general or  $s \leq O(t)$  for planar graphs. With more cleverness, Spielman and Teng showed that s can be improved to  $\tilde{O}(t)$  for general graphs.

## 5 Conclusion

It's interesting that previously we used linear algebra to speed up graph theory, but now we're using graph theory to speed up linear algebra.

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.409 An Algorithmist's Toolkit

December 8, 2009

## Lecture 24

Lecturer: Jonathan Kelner Scribe: Dimiter Ostrev

## Multiplicative Weights

In this lecture we will introduce Multiplicative Weights, a simple technique with many applications. We start with an example.

**Example** Suppose Mr. X wants to bet on football games but does not know much about football himself. Before each game, X can check the predictions of n experts. Is there an algorithm that allows Mr. X to perform well in the long run?

Two potential ideas are:

- (1) For each game, bet according to what the majority of experts predict
- (2) Wait a few games to see which of the experts get it right most of the time and then follow their advice

These strategies work well in some cases but not in others: (1) fails when only a few experts make good predictions, and (2) fails when there is an expert that performs well for the first few games and then never makes a correct prediction again. Instead, we will consider a combination of the two approaches: for each game, we will consider the opinion of all experts, but each expert's opinion will be weighted according to his past performance. More precisely, let  $w_i^t$  denote the weight of expert i after t games, and consider the following algorithm:

- 1. Set  $w_i^0 = 1$  for i = 1, ..., n
- 2. Make a prediction for game t based on a weighted majority of experts where expert i gets weight  $w_i^{t-1}/\sum_j w_j^{t-1}$
- 3. After game t update the weights as follows: if expert i's prediction for game t was wrong then set  $w_i^t = (1 \epsilon)w_i^{t-1}$ ; otherwise set  $w_i^t = w_i^{t-1}$

For this algorithm, we have the following:

**Theorem** Let  $m_i^t$  denote the number of mistakes that expert i makes in the first t games and  $m^t$  denote the number of mistakes that Mr. X makes in the first t games. Then for all i and t,

$$m^t \le \frac{2log(n)}{\epsilon} + 2(1+\epsilon)m_i^t$$

and in particular, this holds for the i that minimizes  $m_i^t$ .

**Proof** Define  $\Phi^k = \sum_i w_i^k$ . If Mr. X makes a mistake at game k, then a weighted majority of the experts must have made a wrong prediction for game k. The weights of all these experts drop by a factor of  $(1 - \epsilon)$  and so we have  $\Phi^k \leq (1 - \epsilon/2)\Phi^{k-1}$ . Then over the first t games we have

$$\Phi^t \le (1 - \frac{\epsilon}{2})^{m^t} \Phi^0 = n(1 - \frac{\epsilon}{2})^{m^t}$$

On the other hand we have  $w_i^t = (1 - \epsilon)^{m_i^t}$  and so

$$\Phi^t > w_i^t = (1 - \epsilon)^{m_i^t}$$

Therefore,

$$n(1 - \frac{\epsilon}{2})^{m^t} \ge (1 - \epsilon)^{m_i^t}$$

Rearranging this inequality gives

$$m^t \le \frac{\log(n)}{-\log(1 - \epsilon/2)} + m_i^t \frac{\log(1 - \epsilon)}{\log(1 - \epsilon/2)}$$

This bound is slightly stronger than the one in the statement of the theorem. Using the inequalities  $\epsilon/2 \le -log(1-\epsilon/2)$  and  $\epsilon+\epsilon^2 \ge -log(1-\epsilon)$  converts it to the required form and completes the proof.

Next, we will modify our algorithm to get rid of the factor of 2 on the right hand side of the bound above. Consider the following:

- 1. Set  $w_i^0 = 1$  for i = 1, ..., n
- 2. To make a prediction for game t, do the following: for i=1,...n, follow expert i's prediction with probability  $p_i^t = w_i^{t-1} / \sum_i w_i^{t-1}$
- 3. After game t update the weights as follows: if expert i's prediction for game t was wrong then set  $w_i^t = (1 \epsilon)w_i^{t-1}$  else set  $w_i^t = w_i^{t-1}$

For this algorithm, we have the following:

**Theorem** Let  $m_i^t$  denote the number of mistakes that expert i makes in the first t games and let  $m^t$  denote the random variable equal to the number of mistakes that Mr. X makes in the first t games. Then for  $\epsilon < 1/2$  and for all i and t.

$$E(m^t) \le \frac{log(n)}{\epsilon} + (1+\epsilon)m_i^t$$

and in particular, this holds for the i that minimizes  $m_i^t$ .

The proof of this Theorem is similar to before and we will omit it. Instead, we will introduce our most general version of the multiplicative weights algorithm. In the example above, we had only two possibilities for the relation between event outcomes and expert predictions: the outcome of game t either matched expert i's prediction or it did not. Our measure of performance for individual experts and for the algorithm as a whole was simply counting wrong predictions. We want to generalize the algorithm to allow for an arbitrary set P of possible outcomes to events. In this setting, we will measure the performance of the algorithm as follows: we will say that at each step, following expert i's prediction when the true outcome is j incurs a penalty of M(i, j). More precisely, we have the following:

- 0. The input of the algorithm consists of: a set P of possible outcomes to events. For i=1,...n and for  $j \in P$  a number M(i,j) from the interval  $[-l,\rho]$ . We will refer to  $\rho$  as the width; we will also have the restriction  $l < \rho$ .
- 1. Set  $w_i^0 = 1$  for i = 1, ..., n
- 2. To make a prediction for event t, do the following: for i=1,...n, follow expert i's prediction with probability  $p_i^t = w_i^{t-1}/\sum_j w_j^{t-1}$

3. Let  $j^t$  denote the outcome of event t. Update the weights as follows:

$$w_i^t = \left\{ \begin{array}{ll} w_i^{t-1} (1 - \epsilon)^{M(i, j^t)/\rho} & \text{if } M(i, j^t) \ge 0 \\ w_i^{t-1} (1 + \epsilon)^{-M(i, j^t)/\rho} & \text{if } M(i, j^t) < 0 \end{array} \right.$$

A similar analysis to before gives:

**Theorem** Let  $D^t$  denote the probability distribution  $\{p_1^t, \ldots, p_n^t\}$  with which we pick experts to make a prediction for event t. Let  $M(D^t, j^t)$  denote the expected value of our penalty when following the distribution  $D^t$  for event t and when the actual outcome is  $j^t$ . Then for  $\epsilon \leq 1/2$  and for all T and i,

$$\sum_{t=1}^{T} M(D^{t}, j^{t}) \leq \frac{\rho log(n)}{\epsilon} + (1+\epsilon) \sum_{t: M(i, j^{t}) \geq 0} M(i, j^{t}) + (1-\epsilon) \sum_{t: M(i, j^{t}) < 0} M(i, j^{t})$$

**Corollary** For any  $\delta$ , for  $\epsilon \leq min(1/2, \delta/4\rho)$ , for  $T = 16\rho^2 log(n)/\delta^2$  rounds and for all i, the average penalty we get per round obeys:

$$\frac{\sum_{t=1}^T M(D^t, j^t)}{T} \leq \delta + \frac{\sum_{t=1}^T M(i, j^t)}{T}$$

and in particular our average penalty per round is at most  $\delta$  bigger than the average penalty of the best expert.

## Applications of Multiplicative Weights

Our first application of the Multiplicative Weights algorithm will be to zero-sum games. In a zero-sum game, we have a row player, R, and a column player, C. If R plays strategy i and C plays strategy j, then R pays C the amount M(i,j). Players can also play mixed strategies, i.e. probability distributions over the sets of pure strategies. We will extend our payoff notation so that M(D,P) denotes the expected amount that R pays C when R plays the mixed strategy D and C plays the mixed strategy R. Recall that von Neumann's Minimax Theorem states that

$$min_D max_i M(D, j) = max_P min_i M(i, P)$$

We will denote the above quantity by  $\lambda$ ; it is known as the value of the game.

We are now ready to state the zero-sum game problem: given the sets of strategies for R and C and the payoffs M(i,j), estimate the value of the game  $\lambda$ . Our approach will be to associate elements of the current problem to appropriately chosen elements of the Multiplicative Weights algorithm, then directly apply what we already know about Multiplicative Weights to conclude that we do indeed get a good approximation to  $\lambda$  in a reasonable amount of time. The details of the argument will be presented next lecture.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### 18.409 An Algorithmist's Toolkit

December 10, 2009

# Lecture 25

Lecturer: Jonathan Kelner Scribe: Nikolaos Trichakis

## Multiplicative Weights

In this lecture, we will study various applications of the theory of Multiplicative Weights (MW). In this section, we briefly review the general version of the MW algorithm that we studied in the previous lecture. The following sections then show how the theory can be applied to approximately solve zero-sum games and linear programs, and how it connects with the theory of boosting and approximation algorithms.

We have n experts who predict the outcome of an event in consecutive rounds. Suppose that in each round there are P different outcomes for the event. If outcome j realizes, expert i pays a penalty of M(i,j). An important paremeter will prove to be the maximum allowable magnitude for the penalty. For that, let  $M(i,j) \in [-\ell,\rho]$ , with  $0 \le \ell \le \rho$ , where  $\rho$  is the width. Our goal is to devise a strategy that dictates which expert's recommendation to follow, in order to achieve an expected avegare penalty that is not much worse than that of the best expert (in hindsight).

The strategy that we analyzed in the previous lecture is as follows. We maintain for each expert a scalar weight, which can be thought of as a quality score. Then, at each round we choose to follow the recommendation of a specific expert with probability that is proportional to her weight. After the outcome is realized, we update the weights of each expert accordingly. In mathematical terms, let  $w_i^t$  be the weight of the *i*th epxert at the beginning of round t. Then, the MW algorithm is

- 0. Initialize  $w_i^1 = 1$ , for all i.
- 1. At step t,
  - a. Follow the recommedation of the ith epxert with probability  $p_i^t$ , where

$$p_i^t = \frac{w_i^t}{\sum_j w_j^t}.$$

- b. Let  $j^t \in P$  denote the outcome of the event at round t, and  $D^t = \{p_1^t, \dots, p_n^t\}$  the distribution we used above to select an expert. Our penalty is denoted by  $M(D^t, j^t)$ , and is equal to  $M(i, j^t)$ , where i is the selected expert.
- c. Update the weights as follows:

$$w_i^{t+1} = \begin{cases} w_i^t (1-\epsilon)^{M(i,j^t)/\rho} & \text{if } M(i,j^t) \ge 0\\ w_i^t (1+\epsilon)^{-M(i,j^t)/\rho} & \text{if } M(i,j^t) < 0. \end{cases}$$

In the previous lecture we argued that for any  $\delta > 0$ , for  $\epsilon \leq \min\left\{\frac{1}{2}, \frac{\delta}{4\rho}\right\}$  and after  $T = \frac{16\rho^2 \log(n)}{\delta^2}$  rounds and for all i, the average penalty we get per round obeys:

$$\frac{\sum_{t=1}^{T} M(D^{t}, j^{t})}{T} \le \delta + \frac{\sum_{t=1}^{T} M(i, j^{t})}{T}.$$

In particular our average penalty per round is at most  $\delta$  bigger than the average penalty of the best expert.

## **Zero-Sum Games**

There are two players, labeled as the "row" player R and the "column" player C. Each player has a finite set of actions that he can follow. At each round, player R pays player C an amount that depends on the actions of the two players. In particular, if R plays action i and C plays j, the payoff from R to C is M(i, j). We assume that the payoffs are normalized, such that  $M(i, j) \in [0, 1]$ . Naturally, player R tries to minimize the payoff, whereas player C tries to maximize it.

Each player can follow a pure strategy, which dictates a single action to be played repeatedly, or a mixed strategy, under which the player has a fixed probability distribution over actions, and chooses actions randomly according to it. One might expect that the order in which players choose their actions might play a role, since knowledge of your opponent's strategy helps you to adopt your strategy appropriately. If we let D and P to be the row and column mixed strategies respectively, the von Neumann's minimax Theorem says that in this game, the order of choosing actions is actually indifferent for the players. Mathematically,

$$\lambda^{\star} := \min_{D} \max_{i} M(D, j) = \max_{P} \min_{i} M(i, P),$$

where  $\lambda^{\star}$  is the so called *value* of the game. Our goal is to approximate this value, up to some additive error  $\delta$ .

We deploy the MW algorithm as follows. Let pure strategies for R correspond to experts, and pure strategies for C correspond to events. Then, the penalty paid by expert i in case of event j is exactly the payoff from R to C, if they follow strategies i and j accordingly, that is M(i,j). Assume also that for a mixed strategy D, we can efficiently compute the column strategy j that maximizes M(D,j) (a quantity eventually  $\geq \lambda^*$ ). At step t of the MW algorithm, we choose a distribution  $D^t$  over experts, which then corresponds to a mixed strategy for R. Given  $D^t$ , we compute the worst possible event, which is the column strategy  $j^t$  that maximizes  $M(D^t, j^t)$ .

To see why this approach yields an approximation to  $\lambda^*$ , first note that for any distribution D,

$$\sum_{t} M(D, j^t) \ge \min_{i} \sum_{t} M(i, j^t), \tag{1}$$

since a distribution is just a weighted average of pure strategies. Furthermore, as we argued above we have

$$M(D^t, j^t) \ge \lambda^*, \tag{2}$$

since we pick the payoff-maximizing column strategy. According to the MW theory, after  $T = \frac{16 \log(n)}{\delta^2}$  rounds and for any distribution D we have

$$\lambda^{\star} \leq \frac{\sum_{t=1}^T M(D^t, j^t)}{T} \leq \delta + \min_i \left\{ \frac{\sum_{t=1}^T M(i, j^t)}{T} \right\} \leq \delta + \frac{\sum_{t=1}^T M(D, j^t)}{T}.$$

The first inequality follows from (2) and the second from (1). Since the above is true for any distribution D, it is also true for the optimal distribution, and hence

$$\lambda^* \le \frac{\sum_{t=1}^T M(D^t, j^t)}{T} \le \delta + \lambda^*.$$

This demonstrates that the average penalty of the algorithm is an approximation of the value of the game, within and additive positive term of  $\delta$ . Note that also the average mixed strategy, or the best strategy  $D^t$ , constitutes an approximately optimal strategy as well, since its payoff is approximately the value of the game, against an optimally acting player.

### Linear Programming and the Plotkin-Shmoys-Tardos framework

There are various ways in which MW theory can used to solve linear programs. Given what we developed in the previous section, one immediate way is to cast the LP as a zero-sum game and solve it via MW.

Note that there are some interesting trade offs between this idea and the traditional ways of solving linear programming problems. In particular, ellipsoid and interior point algorithms (IP) achieve an error of  $\delta$  in  $O(\text{poly}(n)\log(\frac{1}{\delta}))$  steps. Their dependence on the corresponding notion of the MW penalty width is logarithmic. On the other hand, the MW algorithm achieves an error after  $O(\frac{\log(n)}{\delta^2})$  steps, in case the width is 1. Otherwise, the dependence on the width is quadratic, as we have shown. To summarize, IP algorithms are much better with respect to error and size of numbers (i.e., width), whereas MW are much better with respect to the dimension n.

We now switch focus to the Plotkin-Shmoys-Tardos framework, which is a more direct way of applying MW to linear programming. Our goal is to check to feasibility of a set of linear inequalities,

$$Ax \ge b, \quad x \ge 0,$$

where  $A = [a_1 \dots a_m]^T$  is an  $m \times n$  matrix and x an n dimensional vector, or more precisely to find an approximately feasible solution  $x^* \geq 0$ , such that for some  $\delta > 0$ ,

$$a_i^T x^* > b_i - \delta, \quad \forall i.$$

The analysis will be based on an oracle that answers the following question: Given a vector c and a scalar d, does there exist an  $x \ge 0$ , such that  $c^T x \ge d$ ? With this oracle, we will be able to repeatedly check whether a convex combination of the initial linear inequalities,  $a_i^T x \ge b_i$ , is infeasible; a condition that is sufficient for the infeasibility of our original problem. Note that the oracle is straightforward to construct, as it involves a single inequality. In particular, it returns a negative answer if d > 0 and c < 0.

The algorithm is as follows. Experts correspond to each of the m constraints, and events correspond to points  $x \geq 0$ . The penalty for the ith expert for the event x will be  $a_i^T x - b_i$ , and is assumed to take values in  $[-\rho, \rho]$ . Although one might expect the penalty to be the violation of the constraint, it is exactly the opposite; the reason is that the algorithm is trying to actually prove infeasibility of the problem. In the tth round, we use our distribution over experts to generate an inequality that would be valid, if the problem were feasible: if our distribution is  $p_1^t, \ldots, p_m^t$ , the inequality is  $\sum_i p_i^t a_i^T x \geq \sum_i p_i^t b_i$ . The oracle then either detects infeasibility of this constraint, in which case the original problem is  $\sum_i p_i^t (a_i^T x^t - b_i)$ , and the weights are updated accordingly. Note that in case infeasibility is not detected, the penalty we pay is always nonnegative, since  $x^t$  satisfies the checked inequality.

If after  $T = \frac{16\rho^2 \log(n)}{\delta^2}$  infeasibility is not detected, we have the following guarantee by the MW theory:

$$0 \le \frac{\sum_{t=1}^{T} \sum_{i} p_{i}^{t} (a_{i}^{T} x^{t} - b_{i})}{T} \le \delta + \frac{\sum_{t=1}^{T} (a_{i}^{T} x^{t} - b_{i})}{T},$$

for every i. The first inequality follows by the nonnegativity of all penalties. If we take  $\bar{x}$  to be the average of all visited points  $x^t$ ,

$$\bar{x} = \frac{\sum_{t} x^{t}}{T},$$

then this is our approximate solution, since from the above inequality we get for all i

$$0 \le \delta + a_i^T \bar{x} - b_i \Rightarrow a_i^T \bar{x} \ge b_i - \delta.$$

### Boosting

We now visit a problem from the area of Machine Learning. Suppose that we are given a sequence of training points,  $x_1, \ldots, x_N$ , which are drawn from a fixed but unknown to us distribution  $\mathcal{D}$ . Alongide, we are given corresponding 0-1 labels,  $c(x_1), \ldots, c(x_N)$ , assigned to each point, where c is a function from some concept class  $\mathcal{C}$  that maps points onto 0-1 labels. Our goal is to generate a hypothesis function h that assigns labels to points, replicating the function c in the best way possible. This is captured by the average absolute error,  $\mathbf{E}_{\mathcal{D}}[|h(x)-c(x)|]$ . We call a learning algorithm to be strong, if for every distribution  $\mathcal{D}$  and any

fixed  $\epsilon, \delta > 0$ , it outputs with probability at least  $1 - \delta$  a hypothesis h that achieves error no more than  $\epsilon$ . Similarly, it is called  $\gamma$ -weak, if the error is at most  $0.5 - \gamma$ .

Boosting is a very useful, both in theory and in practice, tool of combining weak rules of thumb into strong predictors. In particular, the theory of Boosting shows that if there exists a  $\gamma$ -weak learning algorithm for  $\mathcal{C}$ , then there also exists a strong one. We will show this in case we have a fixed training set with N points, and where the strong algorithm has a small error with respect to the uniform distribution on the training set.

We use the MW algorithm. In the tth round, we assign a different distribution  $\mathcal{D}^t$  on the training set, and use the weak learning algorithm to retrieve a hypothesis  $h_t$ , which by assumption has error at most  $0.5 - \gamma$ , with respect to  $\mathcal{D}^t$ . Our final hypothesis after T rounds,  $h_{\text{final}}$ , is obtained by taking majority vote among  $h_1, \ldots, h_T$ . The experts in this case are the samples in the training set, and the events are the hypotheses produced by the weak learning algorithm. The associated penalty for expert x on hypothesis  $h_t$  is 1 if  $h_t(x) = c(x)$ , and 0 otherwise. As in the previous exemple, we penalize the experts that "are doing well", as we want to eventually increase the weight of a point (expert) if our hypothesis got it wrong. We can start with  $\mathcal{D}^1$  being the uniform distribution, and we update according to the MW algorithm. Finally, after

 $T = \frac{2}{\gamma^2} \log \frac{1}{\epsilon}$ 

rounds we get an error rate for  $h_{\text{final}}$  on the training set, under the uniform distribution, that is at most  $\epsilon$ , as required.

## **Approximation Algorithms**

We conclude with an application that demonstrates how to use the MW algorithm to get  $O(\log n)$  approximation algorithms for many NP-hard problems. The problem that will focus on is the SET COVER problem: Given a universe of elements,  $U = \{1, ..., n\}$ , and a collection  $\mathcal{C} = \{C_1, ..., C_m\}$  of subsets of U, whose union equals U, we want to pick a minimum number of sets from  $\mathcal{C}$  to cover all of U. An immediate algorithm to tackle this problem is the greedy heuristic: at each step, choose the set from  $\mathcal{C}$  that has not been chosen yet and that covers the most out of the yet uncovered elements of U. The MW algorithm will end up taking exactly the form of that greedy algorithm, and will further prove the approximation bound.

We associate the elements of the universe with experts, and the sets of C with events. The penalty for expert i under event  $C_j$ ,  $M(i, C_j)$ , will be equal to 1 if  $i \in C_j$ , and 0 otherwise. In this case, we use the following simplified rule for updating the weights,

$$w_i^{t+1} = w_i^t (1 - M(i, C_j)).$$

The update rule then gives elements that are covered by the newly chosen set a weight of 0, leaving the remaining unaltered. Consequently, the weight of element i in round t is either 0 or 1, depending on if it has being covered already, or not. The distribution we will be using then in round t,

$$p_i^t = \frac{w_i^t}{\sum_k w_k^t},$$

is just a uniform distribution over the uncovered elements by round t. We then choose the maximally adversarial event (that is, the one that maximizes the penalty), which coincides with the set  $C_j$  that covers a maximum number of uncovered elements, and update our weights. The described MW algorithm coincides with the greedy algorithm, in repeatedly picking the set that covers the most uncovered elements.

For any distribution  $p_1^t, \ldots, p_n^t$  on the elements, we have that OPT sets cover everything. That means that the total weights of sets involved (according to the distribution p) is at least 1, and hence at least one of the remaining sets must cover at least 1/OPT fraction. Mathematically,

$$\max_{j} \sum_{i \in C_j} p_i^t \ge 1/\text{OPT}.$$

That shows that after every round, the total penalty drops significantly:

$$\Phi^{t+1} < \Phi^t e^{-1/\text{OPT}}.$$

The inequality is strict, since the penalty is always positive. Using  $\Phi^1=n$ , after OPT  $\log n$  iterations we get  $\Phi<1\Rightarrow\Phi=0$ , which shows that we can cover everything with OPT  $\log n$  sets — an  $\log n$  approximation.

| MIT (  | OpenCourseWare |
|--------|----------------|
| http:/ | /ocw.mit.edu   |

18.409 Topics in Theoretical Computer Science: An Algorithmist's Toolkit Fall 2009

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.
